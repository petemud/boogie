﻿using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using VC;
using BoogiePL = Microsoft.Boogie;
using System.Runtime.Caching;
using System.Diagnostics;

namespace Microsoft.Boogie
{
  #region Output printing

  public interface OutputPrinter
  {
    void ErrorWriteLine(TextWriter tw, string s);
    void ErrorWriteLine(TextWriter tw, string format, params object[] args);
    void AdvisoryWriteLine(string format, params object[] args);
    void Inform(string s, TextWriter tw);
    void WriteTrailer(PipelineStatistics stats);
    void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true);
    void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null);
  }

  #endregion

  public enum PipelineOutcome
  {
    Done,
    ResolutionError,
    TypeCheckingError,
    ResolvedAndTypeChecked,
    FatalError,
    Cancelled,
    VerificationCompleted
  }


  public class PipelineStatistics
  {
    public int ErrorCount;
    public int VerifiedCount;
    public int InconclusiveCount;
    public int TimeoutCount;
    public int OutOfResourceCount;
    public int OutOfMemoryCount;
    public int SolverExceptionCount;
    public long[] CachingActionCounts;
    public int CachedErrorCount;
    public int CachedVerifiedCount;
    public int CachedInconclusiveCount;
    public int CachedTimeoutCount;
    public int CachedOutOfResourceCount;
    public int CachedOutOfMemoryCount;
    public int CachedSolverExceptionCount;
  }


  #region Error reporting

  public delegate void ErrorReporterDelegate(ErrorInformation errInfo);


  public enum ErrorKind
  {
    Assertion,
    Precondition,
    Postcondition,
    InvariantEntry,
    InvariantMaintainance
  }


  public class ErrorInformationFactory
  {
    public virtual ErrorInformation CreateErrorInformation(IToken tok, string msg, string requestId = null,
      string originalRequestId = null, string category = null)
    {
      Contract.Requires(1 <= tok.line && 1 <= tok.col);
      Contract.Requires(msg != null);

      return ErrorInformation.CreateErrorInformation(tok, msg, requestId, originalRequestId, category);
    }
  }


  public class ErrorInformation
  {
    public readonly IToken Tok;
    public string Msg;
    public string Category { get; set; }
    public readonly List<AuxErrorInfo> Aux = new List<AuxErrorInfo>();
    public string OriginalRequestId { get; set; }
    public string RequestId { get; set; }
    public ErrorKind Kind { get; set; }
    public string ImplementationName { get; set; }
    public TextWriter Out = new StringWriter();
    public TextWriter Model = new StringWriter();

    public string FullMsg
    {
      get
      {
        return Category != null ? string.Format("{0}: {1}", Category, Msg) : Msg;
      }
    }

    public struct AuxErrorInfo
    {
      public readonly IToken Tok;
      public readonly string Msg;
      public readonly string Category;

      public string FullMsg
      {
        get { return Category != null ? string.Format("{0}: {1}", Category, Msg) : Msg; }
      }

      public AuxErrorInfo(IToken tok, string msg, string category = null)
      {
        Tok = tok;
        Msg = CleanUp(msg);
        Category = category;
      }
    }

    protected ErrorInformation(IToken tok, string msg)
    {
      Contract.Requires(tok != null);
      Contract.Requires(1 <= tok.line && 1 <= tok.col);
      Contract.Requires(msg != null);

      Tok = tok;
      Msg = CleanUp(msg);
    }

    internal static ErrorInformation CreateErrorInformation(IToken tok, string msg, string requestId = null,
      string originalRequestId = null, string category = null)
    {
      var result = new ErrorInformation(tok, msg);
      result.RequestId = requestId;
      result.OriginalRequestId = originalRequestId;
      result.Category = category;
      return result;
    }

    public virtual void AddAuxInfo(IToken tok, string msg, string category = null)
    {
      Contract.Requires(tok != null);
      Contract.Requires(1 <= tok.line && 1 <= tok.col);
      Contract.Requires(msg != null);
      Aux.Add(new AuxErrorInfo(tok, msg, category));
    }

    protected static string CleanUp(string msg)
    {
      if (msg.ToLower().StartsWith("error: "))
      {
        return msg.Substring(7);
      }
      else
      {
        return msg;
      }
    }
  }

  #endregion


  public class ExecutionEngine : IDisposable
  {
    public static OutputPrinter printer;

    public static ErrorInformationFactory errorInformationFactory = new ErrorInformationFactory();

    static int autoRequestIdCount;

    static readonly string AutoRequestIdPrefix = "auto_request_id_";

    public static string FreshRequestId()
    {
      var id = Interlocked.Increment(ref autoRequestIdCount);
      return AutoRequestIdPrefix + id;
    }

    public static int AutoRequestId(string id)
    {
      if (id.StartsWith(AutoRequestIdPrefix))
      {
        if (int.TryParse(id.Substring(AutoRequestIdPrefix.Length), out var result))
        {
          return result;
        }
      }

      return -1;
    }

    public readonly VerificationResultCache Cache;

    static readonly MemoryCache programCache = new MemoryCache("ProgramCache");

    static readonly CacheItemPolicy policy = new CacheItemPolicy
      {SlidingExpiration = new TimeSpan(0, 10, 0), Priority = CacheItemPriority.Default};

    public static Program CachedProgram(string programId)
    {
      var result = programCache.Get(programId) as Program;
      return result;
    }

    public ExecutionEngine(ExecutionEngineOptions options, VerificationResultCache cache)
    {
      Options = options;
      Cache = cache;
      checkerPool = new CheckerPool(options);
    }

    public static ExecutionEngine CreateWithoutSharedCache(ExecutionEngineOptions options) {
      return new ExecutionEngine(options, new VerificationResultCache());
    }

    public ExecutionEngineOptions Options { get; }
    private readonly CheckerPool checkerPool;

    static DateTime FirstRequestStart;

    static readonly ConcurrentDictionary<string, TimeSpan>
      TimePerRequest = new ConcurrentDictionary<string, TimeSpan>();

    static readonly ConcurrentDictionary<string, PipelineStatistics> StatisticsPerRequest =
      new ConcurrentDictionary<string, PipelineStatistics>();

    static readonly ConcurrentDictionary<string, CancellationTokenSource> ImplIdToCancellationTokenSource =
      new ConcurrentDictionary<string, CancellationTokenSource>();

    static readonly ConcurrentDictionary<string, CancellationTokenSource> RequestIdToCancellationTokenSource =
      new ConcurrentDictionary<string, CancellationTokenSource>();

    static ThreadTaskScheduler Scheduler = new ThreadTaskScheduler(16 * 1024 * 1024);

    static TextWriter ModelWriter = null;

    public bool ProcessFiles(IList<string> fileNames, bool lookForSnapshots = true, string programId = null)
    {
      Contract.Requires(cce.NonNullElements(fileNames));

      if (Options.VerifySeparately && 1 < fileNames.Count)
      {
        return fileNames.All(f => ProcessFiles( new List<string> {f}, lookForSnapshots, f));
      }

      if (0 <= Options.VerifySnapshots && lookForSnapshots)
      {
        var snapshotsByVersion = LookForSnapshots(fileNames);
        return snapshotsByVersion.All(s =>
        {
          // BUG: Reusing checkers during snapshots doesn't work, even though it should. We create a new engine (and thus checker pool) to workaround this.
          using var engine = new ExecutionEngine(Options, Cache);
          return engine.ProcessFiles(new List<string>(s), false, programId);
        });
      }

      using XmlFileScope xf = new XmlFileScope(Options.XmlSink, fileNames[^1]);
      Program program = ParseBoogieProgram(fileNames, false);
      var bplFileName = fileNames[^1];
      if (program == null)
      {
        return true;
      }
      return ProcessProgram(program, bplFileName, programId);
    }

    public bool ProcessProgram(Program program, string bplFileName, string programId = null)
    {
      if (programId == null)
      {
        programId = "main_program_id";
      }
      
      if (Options.PrintFile != null) {
        PrintBplFile(Options.PrintFile, program, false, true, Options.PrettyPrint);
      }

      PipelineOutcome oc = ResolveAndTypecheck(program, bplFileName, out var civlTypeChecker);
      if (oc != PipelineOutcome.ResolvedAndTypeChecked) {
        return true;
      }

      if (Options.PrintCFGPrefix != null) {
        foreach (var impl in program.Implementations) {
          using StreamWriter sw = new StreamWriter(Options.PrintCFGPrefix + "." + impl.Name + ".dot");
          sw.Write(program.ProcessLoops(Options, impl).ToDot());
        }
      }

      CivlVCGeneration.Transform(Options, civlTypeChecker);
      if (Options.CivlDesugaredFile != null) {
        int oldPrintUnstructured = Options.PrintUnstructured;
        Options.PrintUnstructured = 1;
        PrintBplFile(Options.CivlDesugaredFile, program, false, false,
          Options.PrettyPrint);
        Options.PrintUnstructured = oldPrintUnstructured;
      }

      EliminateDeadVariables(program);

      CoalesceBlocks(program);

      Inline(program);

      var stats = new PipelineStatistics();
      oc = InferAndVerify(program, stats, 1 < Options.VerifySnapshots ? programId : null);
      switch (oc) {
        case PipelineOutcome.Done:
        case PipelineOutcome.VerificationCompleted:
          printer.WriteTrailer(stats);
          return true;
        case PipelineOutcome.FatalError:
          return false;
        default:
          Debug.Assert(false, "Unreachable code");
          return false;
      }
    }

    public static IList<IList<string>> LookForSnapshots(IList<string> fileNames)
    {
      Contract.Requires(fileNames != null);

      var result = new List<IList<string>>();
      for (int version = 0; true; version++)
      {
        var nextSnapshot = new List<string>();
        foreach (var name in fileNames)
        {
          var versionedName = name.Replace(Path.GetExtension(name), ".v" + version + Path.GetExtension(name));
          if (File.Exists(versionedName))
          {
            nextSnapshot.Add(versionedName);
          }
        }

        if (nextSnapshot.Any())
        {
          result.Add(nextSnapshot);
        }
        else
        {
          break;
        }
      }

      return result;
    }

    public void CoalesceBlocks(Program program)
    {
      if (Options.CoalesceBlocks)
      {
        if (Options.Trace)
        {
          Console.WriteLine("Coalescing blocks...");
        }

        Microsoft.Boogie.BlockCoalescer.CoalesceBlocks(program);
      }
    }


    public void CollectModSets(Program program)
    {
      if (Options.DoModSetAnalysis)
      {
        new ModSetCollector(Options).DoModSetAnalysis(program);
      }
    }


    public void EliminateDeadVariables(Program program)
    {
      Microsoft.Boogie.UnusedVarEliminator.Eliminate(program);
    }


    public void PrintBplFile(string filename, Program program, bool allowPrintDesugaring, bool setTokens = true,
      bool pretty = false)
    {
      PrintBplFile(Options, filename, program, allowPrintDesugaring, setTokens, pretty);
    }

    public static void PrintBplFile(ExecutionEngineOptions options, string filename, Program program, bool allowPrintDesugaring, bool setTokens = true,
      bool pretty = false)

    {
      Contract.Requires(program != null);
      Contract.Requires(filename != null);
      bool oldPrintDesugaring = options.PrintDesugarings;
      if (!allowPrintDesugaring)
      {
        options.PrintDesugarings = false;
      }

      using (TokenTextWriter writer = filename == "-"
        ? new TokenTextWriter("<console>", Console.Out, setTokens, pretty, options)
        : new TokenTextWriter(filename, setTokens, pretty, options))
      {
        if (options.ShowEnv != ExecutionEngineOptions.ShowEnvironment.Never)
        {
          writer.WriteLine("// " + options.Version);
          writer.WriteLine("// " + options.Environment);
        }

        writer.WriteLine();
        program.Emit(writer);
      }

      options.PrintDesugarings = oldPrintDesugaring;
    }


    /// <summary>
    /// Parse the given files into one Boogie program.  If an I/O or parse error occurs, an error will be printed
    /// and null will be returned.  On success, a non-null program is returned.
    /// </summary>
    public Program ParseBoogieProgram(IList<string> fileNames, bool suppressTraceOutput)
    {
      Contract.Requires(cce.NonNullElements(fileNames));

      Program program = new Program();
      bool okay = true;
      
      for (int fileId = 0; fileId < fileNames.Count; fileId++)
      {
        string bplFileName = fileNames[fileId];
        if (!suppressTraceOutput)
        {
          if (Options.XmlSink != null)
          {
            Options.XmlSink.WriteFileFragment(bplFileName);
          }

          if (Options.Trace)
          {
            Console.WriteLine("Parsing " + GetFileNameForConsole(Options, bplFileName));
          }
        }

        try
        {
          var defines = new List<string>() {"FILE_" + fileId};
          int errorCount = Parser.Parse(bplFileName, defines, out Program programSnippet,
            Options.UseBaseNameForFileName);
          if (programSnippet == null || errorCount != 0)
          {
            Console.WriteLine("{0} parse errors detected in {1}", errorCount, GetFileNameForConsole(Options, bplFileName));
            okay = false;
          }
          else
          {
            program.AddTopLevelDeclarations(programSnippet.TopLevelDeclarations);
          }
        }
        catch (IOException e)
        {
          printer.ErrorWriteLine(Console.Out, "Error opening file \"{0}\": {1}",
            GetFileNameForConsole(Options, bplFileName), e.Message);
          okay = false;
        }
      }

      if (!okay)
      {
        return null;
      }
      else
      {
        if (program.TopLevelDeclarations.Any(d => d.HasCivlAttribute()))
        {
          Options.UseLibrary = true;
        }

        if (Options.UseLibrary)
        {
          Options.UseArrayTheory = true;
          Options.Monomorphize = true;
          var library = Parser.ParseLibraryDefinitions();
          program.AddTopLevelDeclarations(library.TopLevelDeclarations);
        }

        return program;
      }
    }

    internal static string GetFileNameForConsole(ExecutionEngineOptions options, string filename)
    {
      return options.UseBaseNameForFileName && !string.IsNullOrEmpty(filename) &&
             filename != "<console>"
        ? Path.GetFileName(filename)
        : filename;
    }


    /// <summary>
    /// Resolves and type checks the given Boogie program.  Any errors are reported to the
    /// console.  Returns:
    ///  - Done if no errors occurred, and command line specified no resolution or no type checking.
    ///  - ResolutionError if a resolution error occurred
    ///  - TypeCheckingError if a type checking error occurred
    ///  - ResolvedAndTypeChecked if both resolution and type checking succeeded
    /// </summary>
    public PipelineOutcome ResolveAndTypecheck(Program program, string bplFileName,
      out CivlTypeChecker civlTypeChecker)
    {
      Contract.Requires(program != null);
      Contract.Requires(bplFileName != null);

      civlTypeChecker = null;

      // ---------- Resolve ------------------------------------------------------------

      if (Options.NoResolve)
      {
        return PipelineOutcome.Done;
      }

      int errorCount = program.Resolve(Options);
      if (errorCount != 0)
      {
        Console.WriteLine("{0} name resolution errors detected in {1}", errorCount, GetFileNameForConsole(Options, bplFileName));
        return PipelineOutcome.ResolutionError;
      }

      // ---------- Type check ------------------------------------------------------------

      if (Options.NoTypecheck)
      {
        return PipelineOutcome.Done;
      }

      if (!FunctionDependencyChecker.Check(program))
      {
        return PipelineOutcome.TypeCheckingError;
      }
      
      errorCount = program.Typecheck(Options);
      if (errorCount != 0)
      {
        Console.WriteLine("{0} type checking errors detected in {1}", errorCount, GetFileNameForConsole(Options, bplFileName));
        return PipelineOutcome.TypeCheckingError;
      }

      if (MonomorphismChecker.IsMonomorphic(program))
      {
        Options.TypeEncodingMethod = CoreOptions.TypeEncoding.Monomorphic;
      }
      else if (Options.Monomorphize)
      {
        var monomorphizableStatus = Monomorphizer.Monomorphize(Options, program);
        if (monomorphizableStatus == MonomorphizableStatus.Monomorphizable)
        {
          Options.TypeEncodingMethod = CoreOptions.TypeEncoding.Monomorphic;
        }
        else if (monomorphizableStatus == MonomorphizableStatus.UnhandledPolymorphism)
        {
          Console.WriteLine("Unable to monomorphize input program: unhandled polymorphic features detected");
          return PipelineOutcome.FatalError;
        }
        else
        {
          Console.WriteLine("Unable to monomorphize input program: expanding type cycle detected");
          return PipelineOutcome.FatalError;
        }
      }
      else if (Options.UseArrayTheory)
      {
        Console.WriteLine(
          "Option /useArrayTheory only supported for monomorphic programs, polymorphism is detected in input program, try using -monomorphize");
        return PipelineOutcome.FatalError;
      } 
      else if (program.TopLevelDeclarations.OfType<DatatypeTypeCtorDecl>().Any())
      {
        Console.WriteLine(
          "Datatypes only supported for monomorphic programs, polymorphism is detected in input program, try using -monomorphize");
        return PipelineOutcome.FatalError;
      }

      CollectModSets(program);

      civlTypeChecker = new CivlTypeChecker(Options, program);
      civlTypeChecker.TypeCheck();
      if (civlTypeChecker.checkingContext.ErrorCount != 0)
      {
        Console.WriteLine("{0} type checking errors detected in {1}", civlTypeChecker.checkingContext.ErrorCount,
          GetFileNameForConsole(Options, bplFileName));
        return PipelineOutcome.TypeCheckingError;
      }

      if (Options.PrintFile != null && Options.PrintDesugarings)
      {
        // if PrintDesugaring option is engaged, print the file here, after resolution and type checking
        PrintBplFile(Options.PrintFile, program, true, true, Options.PrettyPrint);
      }

      return PipelineOutcome.ResolvedAndTypeChecked;
    }


    public void Inline(Program program)
    {
      Contract.Requires(program != null);

      if (Options.Trace)
      {
        Console.WriteLine("Inlining...");
      }

      // Inline
      var TopLevelDeclarations = cce.NonNull(program.TopLevelDeclarations);

      if (Options.ProcedureInlining != CoreOptions.Inlining.None)
      {
        bool inline = false;
        foreach (var d in TopLevelDeclarations)
        {
          if ((d is Procedure || d is Implementation) && d.FindExprAttribute("inline") != null)
          {
            inline = true;
          }
        }

        if (inline)
        {
          foreach (var impl in TopLevelDeclarations.OfType<Implementation>())
          {
            impl.OriginalBlocks = impl.Blocks;
            impl.OriginalLocVars = impl.LocVars;
          }

          foreach (var impl in TopLevelDeclarations.OfType<Implementation>())
          {
            if (Options.UserWantsToCheckRoutine(impl.Name) && !impl.IsSkipVerification(Options))
            {
              Inliner.ProcessImplementation(Options, program, impl);
            }
          }

          foreach (var impl in TopLevelDeclarations.OfType<Implementation>())
          {
            impl.OriginalBlocks = null;
            impl.OriginalLocVars = null;
          }
        }
      }
    }


    /// <summary>
    /// Given a resolved and type checked Boogie program, infers invariants for the program
    /// and then attempts to verify it.  Returns:
    ///  - Done if command line specified no verification
    ///  - FatalError if a fatal error occurred, in which case an error has been printed to console
    ///  - VerificationCompleted if inference and verification completed, in which the out
    ///    parameters contain meaningful values
    /// </summary>
    public PipelineOutcome InferAndVerify(
      Program program,
      PipelineStatistics stats,
      string programId = null,
      ErrorReporterDelegate er = null, string requestId = null)
    {
      Contract.Requires(program != null);
      Contract.Requires(stats != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out stats.InconclusiveCount) &&
                       0 <= Contract.ValueAtReturn(out stats.TimeoutCount));

      if (requestId == null)
      {
        requestId = FreshRequestId();
      }

      if (Options.PrintErrorModelFile != null)
      {
        ExecutionEngine.ModelWriter = new StreamWriter(Options.PrintErrorModelFile, false);
      }

      var start = DateTime.UtcNow;

      #region Do some pre-abstract-interpretation preprocessing on the program

      // Doing lambda expansion before abstract interpretation means that the abstract interpreter
      // never needs to see any lambda expressions.  (On the other hand, if it were useful for it
      // to see lambdas, then it would be better to more lambda expansion until after inference.)
      if (Options.ExpandLambdas)
      {
        LambdaHelper.ExpandLambdas(Options, program);
        if (Options.PrintFile != null && Options.PrintLambdaLifting)
        {
          PrintBplFile(Options.PrintFile, program, false, true, Options.PrettyPrint);
        }
      }

      #endregion

      #region Infer invariants using Abstract Interpretation

      if (Options.UseAbstractInterpretation)
      {
        new AbstractInterpretation.NativeAbstractInterpretation(Options).RunAbstractInterpretation(program);
      }

      #endregion

      #region Do some post-abstract-interpretation preprocessing on the program (e.g., loop unrolling)

      if (Options.LoopUnrollCount != -1)
      {
        program.UnrollLoops(Options.LoopUnrollCount, Options.SoundLoopUnrolling);
      }

      Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo = null;
      if (Options.ExtractLoops)
      {
        extractLoopMappingInfo = program.ExtractLoops(Options);
      }

      if (Options.PrintInstrumented)
      {
        program.Emit(new TokenTextWriter(Console.Out, Options.PrettyPrint, Options));
      }

      #endregion

      if (!Options.Verify)
      {
        return PipelineOutcome.Done;
      }

      #region Run Houdini and verify

      if (Options.ContractInfer)
      {
        return RunHoudini(program, stats, er);
      }

      #endregion

      var stablePrioritizedImpls = GetPrioritizedImplementations(program);

      if (1 < Options.VerifySnapshots)
      {
        CachedVerificationResultInjector.Inject(this, program, stablePrioritizedImpls, requestId, programId,
          out stats.CachingActionCounts);
      }

      var outcome = VerifyEachImplementation(program, stats, programId, er, requestId, stablePrioritizedImpls, extractLoopMappingInfo);

      if (1 < Options.VerifySnapshots && programId != null)
      {
        program.FreezeTopLevelDeclarations();
        programCache.Set(programId, program, policy);
      }

      TraceCachingForBenchmarking(stats, requestId, start);

      return outcome;
    }

    private Implementation[] GetPrioritizedImplementations(Program program)
    {
      var impls = program.Implementations.Where(
        impl => impl != null && Options.UserWantsToCheckRoutine(cce.NonNull(impl.Name)) &&
                !impl.IsSkipVerification(Options));

      // operate on a stable copy, in case it gets updated while we're running
      Implementation[] stablePrioritizedImpls = null;
      if (0 < Options.VerifySnapshots) {
        OtherDefinitionAxiomsCollector.Collect(Options, program.Axioms);
        DependencyCollector.Collect(Options, program);
        stablePrioritizedImpls = impls.OrderByDescending(
            impl => impl.Priority != 1 ? impl.Priority : Cache.VerificationPriority(impl, Options.RunDiagnosticsOnTimeout))
          .ToArray();
      } else {
        stablePrioritizedImpls = impls.OrderByDescending(impl => impl.Priority).ToArray();
      }

      return stablePrioritizedImpls;
    }

    private PipelineOutcome VerifyEachImplementation(Program program, PipelineStatistics stats, string programId,
      ErrorReporterDelegate er, string requestId, Implementation[] stablePrioritizedImpls,
      Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo)
    {
      program.DeclarationDependencies = Prune.ComputeDeclarationDependencies(Options, program);
      var outputCollector = new OutputCollector(stablePrioritizedImpls);
      var outcome = PipelineOutcome.VerificationCompleted;

      try {
        var cts = new CancellationTokenSource();
        RequestIdToCancellationTokenSource.AddOrUpdate(requestId, cts, (k, ov) => cts);

        var tasks = new Task[stablePrioritizedImpls.Length];
        // We use this semaphore to limit the number of tasks that are currently executing.
        var semaphore = new SemaphoreSlim(Options.VcsCores);

        // Create a task per implementation.
        for (int i = 0; i < stablePrioritizedImpls.Length; i++) {
          var taskIndex = i;
          var id = stablePrioritizedImpls[taskIndex].Id;

          if (ImplIdToCancellationTokenSource.TryGetValue(id, out var old)) {
            old.Cancel();
          }

          ImplIdToCancellationTokenSource.AddOrUpdate(id, cts, (k, ov) => cts);

          var t = new Task((dummy) =>
          {
            try {
              if (outcome == PipelineOutcome.FatalError) {
                return;
              }

              if (cts.Token.IsCancellationRequested) {
                cts.Token.ThrowIfCancellationRequested();
              }

              VerifyImplementation(program, stats, er, requestId, extractLoopMappingInfo, stablePrioritizedImpls,
                taskIndex, outputCollector, programId);
              ImplIdToCancellationTokenSource.TryRemove(id, out old);
            }
            finally {
              semaphore.Release();
            }
          }, cts.Token, TaskCreationOptions.None);
          tasks[taskIndex] = t;
        }

        // Execute the tasks.
        int j = 0;
        for (; j < stablePrioritizedImpls.Length && outcome != PipelineOutcome.FatalError; j++) {
          try {
            semaphore.Wait(cts.Token);
          }
          catch (OperationCanceledException) {
            break;
          }

          tasks[j].Start(Scheduler);
        }

        // Don't wait for tasks that haven't been started yet.
        tasks = tasks.Take(j).ToArray();
        Task.WaitAll(tasks);
      }
      catch (AggregateException ae) {
        ae.Flatten().Handle(e =>
        {
          if (e is ProverException) {
            printer.ErrorWriteLine(Console.Out, "Fatal Error: ProverException: {0}", e.Message);
            outcome = PipelineOutcome.FatalError;
            return true;
          }

          if (e is OperationCanceledException) {
            outcome = PipelineOutcome.Cancelled;
            return true;
          }

          return false;
        });
      }
      finally {
        CleanupRequest(requestId);
      }

      if (Options.PrintNecessaryAssumes && program.NecessaryAssumes.Any()) {
        Console.WriteLine("Necessary assume command(s): {0}", string.Join(", ", program.NecessaryAssumes));
      }

      cce.NonNull(Options.TheProverFactory).Close();

      outputCollector.WriteMoreOutput();
      return outcome;
    }

    private void TraceCachingForBenchmarking(PipelineStatistics stats, string requestId, DateTime start)
    {
      if (0 <= Options.VerifySnapshots && Options.TraceCachingForBenchmarking) {
        var end = DateTime.UtcNow;
        if (TimePerRequest.Count == 0) {
          FirstRequestStart = start;
        }

        TimePerRequest[requestId] = end.Subtract(start);
        StatisticsPerRequest[requestId] = stats;

        var printTimes = true;

        Console.Out.WriteLine(CachedVerificationResultInjector.Statistics.Output(printTimes));

        Console.Out.WriteLine("Statistics per request as CSV:");
        var actions = string.Join(", ", Enum.GetNames(typeof(VC.ConditionGeneration.CachingAction)));
        Console.Out.WriteLine(
          "Request ID{0}, Error, E (C), Inconclusive, I (C), Out of Memory, OoM (C), Timeout, T (C), Verified, V (C), {1}",
          printTimes ? ", Time (ms)" : "", actions);
        foreach (var kv in TimePerRequest.OrderBy(kv => ExecutionEngine.AutoRequestId(kv.Key))) {
          var s = StatisticsPerRequest[kv.Key];
          var cacs = s.CachingActionCounts;
          var c = cacs != null ? ", " + cacs.Select(ac => string.Format("{0,3}", ac)).Concat(", ") : "";
          var t = printTimes ? string.Format(", {0,8:F0}", kv.Value.TotalMilliseconds) : "";
          Console.Out.WriteLine(
            "{0,-19}{1}, {2,2}, {3,2}, {4,2}, {5,2}, {6,2}, {7,2}, {8,2}, {9,2}, {10,2}, {11,2}{12}", kv.Key, t,
            s.ErrorCount, s.CachedErrorCount, s.InconclusiveCount, s.CachedInconclusiveCount, s.OutOfMemoryCount,
            s.CachedOutOfMemoryCount, s.TimeoutCount, s.CachedTimeoutCount, s.VerifiedCount, s.CachedVerifiedCount, c);
        }

        if (printTimes) {
          Console.Out.WriteLine();
          Console.Out.WriteLine("Total time (ms) since first request: {0:F0}",
            end.Subtract(FirstRequestStart).TotalMilliseconds);
        }
      }
    }

    public static void CancelRequest(string requestId)
    {
      Contract.Requires(requestId != null);

      if (RequestIdToCancellationTokenSource.TryGetValue(requestId, out var cts))
      {
        cts.Cancel();

        CleanupRequest(requestId);
      }
    }

    private static void CleanupRequest(string requestId)
    {
      if (requestId != null)
      {
        RequestIdToCancellationTokenSource.TryRemove(requestId, out var old);
      }
    }


    private void VerifyImplementation(Program program, PipelineStatistics stats, ErrorReporterDelegate er,
      string requestId, Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo,
      Implementation[] stablePrioritizedImpls, int index, OutputCollector outputCollector, string programId)
    {
      var output = new StringWriter();
      Implementation impl = stablePrioritizedImpls[index];

      printer.Inform("", output); // newline
      printer.Inform($"Verifying {impl.Name} ...", output);
      var verificationResult = GetCachedVerificationResult(impl, output);

      var wasCached = true;
      if (verificationResult == null) {
        wasCached = false;

        verificationResult = VerifyImplementationWithoutCaching(program, stats, er, requestId, extractLoopMappingInfo, programId, impl, output);

        if (0 < Options.VerifySnapshots && !string.IsNullOrEmpty(impl.Checksum))
        {
          Cache.Insert(impl, verificationResult);
        }
      }
      verificationResult.Emit(this, stats, er, index, outputCollector, output, impl, wasCached);
    }

    private VerificationResult GetCachedVerificationResult(Implementation impl, TextWriter output)
    {
      VerificationResult verificationResult = null;
      int priority = 0;
      if (0 < Options.VerifySnapshots) {
        var cachedResults = Cache.Lookup(impl, Options.RunDiagnosticsOnTimeout, out priority);
        if (cachedResults != null && priority == Priority.SKIP) {
          printer.Inform(string.Format("Retrieving cached verification result for implementation {0}...", impl.Name),
            output);
          if (Options.VerifySnapshots < 3 ||
              cachedResults.Outcome == ConditionGeneration.Outcome.Correct) {
            verificationResult = cachedResults;
          }
        }
      }

      return verificationResult;
    }

    private VerificationResult VerifyImplementationWithoutCaching(Program program, PipelineStatistics stats,
      ErrorReporterDelegate er, string requestId, Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo,
      string programId, Implementation impl, TextWriter output)
    {
      VerificationResult verificationResult = new VerificationResult(requestId, impl, programId);

      using (var vcgen = CreateVCGen(program, checkerPool)) {
        vcgen.CachingActionCounts = stats.CachingActionCounts;
        verificationResult.ProofObligationCountBefore = vcgen.CumulativeAssertionCount;
        verificationResult.Start = DateTime.UtcNow;

        try {
          var cancellationToken = RequestIdToCancellationTokenSource[requestId].Token;
          verificationResult.Outcome =
            vcgen.VerifyImplementation(impl, out verificationResult.Errors,
              out verificationResult.VCResults, requestId, cancellationToken);
          if (Options.ExtractLoops && verificationResult.Errors != null) {
            var vcg = vcgen as VCGen;
            if (vcg != null) {
              for (int i = 0; i < verificationResult.Errors.Count; i++) {
                verificationResult.Errors[i] = vcg.extractLoopTrace(verificationResult.Errors[i], impl.Name,
                  program, extractLoopMappingInfo);
              }
            }
          }
        }
        catch (VCGenException e) {
          var errorInfo = errorInformationFactory.CreateErrorInformation(impl.tok,
            String.Format("{0} (encountered in implementation {1}).", e.Message, impl.Name), requestId, "Error");
          errorInfo.ImplementationName = impl.Name;
          printer.WriteErrorInformation(errorInfo, output);
          if (er != null) {
            lock (er) {
              er(errorInfo);
            }
          }

          verificationResult.Errors = null;
          verificationResult.Outcome = VCGen.Outcome.Inconclusive;
        }
        catch (ProverDiedException) {
          throw;
        }
        catch (UnexpectedProverOutputException upo) {
          printer.AdvisoryWriteLine("Advisory: {0} SKIPPED because of internal error: unexpected prover output: {1}",
            impl.Name, upo.Message);
          verificationResult.Errors = null;
          verificationResult.Outcome = VCGen.Outcome.Inconclusive;
        }
        catch (AggregateException ae) {
          ae.Flatten().Handle(e =>
          {
            if (e is IOException) {
              printer.AdvisoryWriteLine("Advisory: {0} SKIPPED due to I/O exception: {1}",
                impl.Name, e.Message);
              verificationResult.Errors = null;
              verificationResult.Outcome = VCGen.Outcome.SolverException;
              return true;
            }

            return false;
          });
        }

        verificationResult.ProofObligationCountAfter = vcgen.CumulativeAssertionCount;
        verificationResult.End = DateTime.UtcNow;
        verificationResult.ResourceCount = vcgen.ResourceCount;
      }

      return verificationResult;
    }

    private static ConditionGeneration CreateVCGen(Program program, CheckerPool checkerPool)
    {
      return new VCGen(program, checkerPool);
    }

    #region Houdini

    private PipelineOutcome RunHoudini(Program program, PipelineStatistics stats, ErrorReporterDelegate er)
    {
      Contract.Requires(stats != null);
      
      if (Options.StagedHoudini != null)
      {
        return RunStagedHoudini(program, stats, er);
      }

      Houdini.HoudiniSession.HoudiniStatistics houdiniStats = new Houdini.HoudiniSession.HoudiniStatistics();
      Houdini.Houdini houdini = new Houdini.Houdini(Options, program, houdiniStats);
      Houdini.HoudiniOutcome outcome = houdini.PerformHoudiniInference();
      houdini.Close();

      if (Options.PrintAssignment)
      {
        Console.WriteLine("Assignment computed by Houdini:");
        foreach (var x in outcome.assignment)
        {
          Console.WriteLine(x.Key + " = " + x.Value);
        }
      }

      if (Options.Trace)
      {
        int numTrueAssigns = 0;
        foreach (var x in outcome.assignment)
        {
          if (x.Value)
          {
            numTrueAssigns++;
          }
        }

        Console.WriteLine("Number of true assignments = " + numTrueAssigns);
        Console.WriteLine("Number of false assignments = " + (outcome.assignment.Count - numTrueAssigns));
        Console.WriteLine("Prover time = " + houdiniStats.proverTime.ToString("F2"));
        Console.WriteLine("Unsat core prover time = " + houdiniStats.unsatCoreProverTime.ToString("F2"));
        Console.WriteLine("Number of prover queries = " + houdiniStats.numProverQueries);
        Console.WriteLine("Number of unsat core prover queries = " + houdiniStats.numUnsatCoreProverQueries);
        Console.WriteLine("Number of unsat core prunings = " + houdiniStats.numUnsatCorePrunings);
      }

      foreach (Houdini.VCGenOutcome x in outcome.implementationOutcomes.Values)
      {
        ProcessOutcome(x.outcome, x.errors, "", stats, Console.Out, Options.TimeLimit, er);
        ProcessErrors(x.errors, x.outcome, Console.Out, er);
      }

      return PipelineOutcome.Done;
    }

    public Program ProgramFromFile(string filename)
    {
      Program p = ParseBoogieProgram( new List<string> {filename}, false);
      Debug.Assert(p != null);
      PipelineOutcome oc = ResolveAndTypecheck(p, filename, out var civlTypeChecker);
      Debug.Assert(oc == PipelineOutcome.ResolvedAndTypeChecked);
      return p;
    }

    private PipelineOutcome RunStagedHoudini(Program program, PipelineStatistics stats, ErrorReporterDelegate er)
    {
      Houdini.HoudiniSession.HoudiniStatistics houdiniStats = new Houdini.HoudiniSession.HoudiniStatistics();
      var stagedHoudini = new Houdini.StagedHoudini(Options, program, houdiniStats, ProgramFromFile);
      Houdini.HoudiniOutcome outcome = stagedHoudini.PerformStagedHoudiniInference();

      if (Options.PrintAssignment)
      {
        Console.WriteLine("Assignment computed by Houdini:");
        foreach (var x in outcome.assignment)
        {
          Console.WriteLine(x.Key + " = " + x.Value);
        }
      }

      if (Options.Trace)
      {
        int numTrueAssigns = 0;
        foreach (var x in outcome.assignment)
        {
          if (x.Value)
          {
            numTrueAssigns++;
          }
        }

        Console.WriteLine("Number of true assignments = " + numTrueAssigns);
        Console.WriteLine("Number of false assignments = " + (outcome.assignment.Count - numTrueAssigns));
        Console.WriteLine("Prover time = " + houdiniStats.proverTime.ToString("F2"));
        Console.WriteLine("Unsat core prover time = " + houdiniStats.unsatCoreProverTime.ToString("F2"));
        Console.WriteLine("Number of prover queries = " + houdiniStats.numProverQueries);
        Console.WriteLine("Number of unsat core prover queries = " + houdiniStats.numUnsatCoreProverQueries);
        Console.WriteLine("Number of unsat core prunings = " + houdiniStats.numUnsatCorePrunings);
      }

      foreach (Houdini.VCGenOutcome x in outcome.implementationOutcomes.Values)
      {
        ProcessOutcome(x.outcome, x.errors, "", stats, Console.Out, Options.TimeLimit, er);
        ProcessErrors(x.errors, x.outcome, Console.Out, er);
      }

      return PipelineOutcome.Done;
    }

    #endregion


    public string TimeIndication(VerificationResult verificationResult)
    {
      var result = "";
      if (Options.Trace)
      {
        result = string.Format("  [{0:F3} s, solver resource count: {1}, {2} proof obligation{3}]  ",
          (verificationResult.End - verificationResult.Start).TotalSeconds,
          verificationResult.ResourceCount,
          verificationResult.ProofObligationCount,
          verificationResult.ProofObligationCount == 1 ? "" : "s");
      }
      else if (Options.TraceProofObligations)
      {
        result = string.Format("  [{0} proof obligation{1}]  ", verificationResult.ProofObligationCount,
          verificationResult.ProofObligationCount == 1 ? "" : "s");
      }

      return result;
    }


    public void ProcessOutcome(VC.VCGen.Outcome outcome, List<Counterexample> errors, string timeIndication,
      PipelineStatistics stats, TextWriter tw, uint timeLimit, ErrorReporterDelegate er = null, string implName = null,
      IToken implTok = null, string requestId = null, string msgIfVerifies = null, bool wasCached = false)
    {
      Contract.Requires(stats != null);

      UpdateStatistics(stats, outcome, errors, wasCached);

      printer.Inform(timeIndication + OutcomeIndication(outcome, errors), tw);

      ReportOutcome(outcome, er, implName, implTok, requestId, msgIfVerifies, tw, timeLimit, errors);
    }


    private void ReportOutcome(VC.VCGen.Outcome outcome, ErrorReporterDelegate er, string implName,
      IToken implTok, string requestId, string msgIfVerifies, TextWriter tw, uint timeLimit, List<Counterexample> errors)
    {
      ErrorInformation errorInfo = null;

      switch (outcome)
      {
        case VCGen.Outcome.Correct:
          if (msgIfVerifies != null)
          {
            tw.WriteLine(msgIfVerifies); 
          }
          break;
        case VCGen.Outcome.ReachedBound:
          tw.WriteLine(string.Format("Stratified Inlining: Reached recursion bound of {0}",
            Options.RecursionBound));
          break;
        case VCGen.Outcome.Errors:
        case VCGen.Outcome.TimedOut:
          if (implName != null && implTok != null)
          {
            if (outcome == ConditionGeneration.Outcome.TimedOut ||
                (errors != null && errors.Any(e => e.IsAuxiliaryCexForDiagnosingTimeouts)))
            {
              errorInfo = errorInformationFactory.CreateErrorInformation(implTok,
                string.Format("Verification of '{1}' timed out after {0} seconds", timeLimit, implName), requestId);
            }

            //  Report timed out assertions as auxiliary info.
            if (errors != null)
            {
              var cmpr = new CounterexampleComparer();
              var timedOutAssertions = errors.Where(e => e.IsAuxiliaryCexForDiagnosingTimeouts).Distinct(cmpr).ToList();
              timedOutAssertions.Sort(cmpr);
              if (0 < timedOutAssertions.Count)
              {
                errorInfo.Msg += string.Format(" with {0} check(s) that timed out individually",
                  timedOutAssertions.Count);
              }

              foreach (Counterexample error in timedOutAssertions)
              {
                var callError = error as CallCounterexample;
                var returnError = error as ReturnCounterexample;
                var assertError = error as AssertCounterexample;
                IToken tok = null;
                string msg = null;
                if (callError != null)
                {
                  tok = callError.FailingCall.tok;
                  msg = callError.FailingCall.ErrorData as string ??
                        callError.FailingCall.Description.FailureDescription;
                }
                else if (returnError != null)
                {
                  tok = returnError.FailingReturn.tok;
                  msg = returnError.FailingReturn.Description.FailureDescription;
                }
                else
                {
                  tok = assertError.FailingAssert.tok;
                  if (assertError.FailingAssert.ErrorMessage == null || Options.ForceBplErrors) {
                      msg = assertError.FailingAssert.ErrorData as string;
                  }
                  else {
                    msg = assertError.FailingAssert.ErrorMessage;
                  }
                  msg ??= assertError.FailingAssert.Description.FailureDescription;
                }

                errorInfo.AddAuxInfo(tok, msg, "Unverified check due to timeout");
              }
            }
          }

          break;
        case VCGen.Outcome.OutOfResource:
          if (implName != null && implTok != null)
          {
            errorInfo = errorInformationFactory.CreateErrorInformation(implTok,
              "Verification out of resource (" + implName + ")", requestId);
          }

          break;
        case VCGen.Outcome.OutOfMemory:
          if (implName != null && implTok != null)
          {
            errorInfo = errorInformationFactory.CreateErrorInformation(implTok,
              "Verification out of memory (" + implName + ")", requestId);
          }

          break;
        case VCGen.Outcome.SolverException:
          if (implName != null && implTok != null)
          {
            errorInfo = errorInformationFactory.CreateErrorInformation(implTok,
              "Verification encountered solver exception (" + implName + ")", requestId);
          }

          break;

        case VCGen.Outcome.Inconclusive:
          if (implName != null && implTok != null)
          {
            errorInfo = errorInformationFactory.CreateErrorInformation(implTok,
              "Verification inconclusive (" + implName + ")", requestId);
          }

          break;
      }

      if (errorInfo != null)
      {
        errorInfo.ImplementationName = implName;
        if (er != null)
        {
          lock (er)
          {
            er(errorInfo);
          }
        }
        else
        {
          printer.WriteErrorInformation(errorInfo, tw);
        }
      }
    }


    private static string OutcomeIndication(VC.VCGen.Outcome outcome, List<Counterexample> errors)
    {
      string traceOutput = "";
      switch (outcome)
      {
        default:
          Contract.Assert(false); // unexpected outcome
          throw new cce.UnreachableException();
        case VCGen.Outcome.ReachedBound:
          traceOutput = "verified";
          break;
        case VCGen.Outcome.Correct:
          traceOutput = "verified";
          break;
        case VCGen.Outcome.TimedOut:
          traceOutput = "timed out";
          break;
        case VCGen.Outcome.OutOfResource:
          traceOutput = "out of resource";
          break;
        case VCGen.Outcome.OutOfMemory:
          traceOutput = "out of memory";
          break;
        case VCGen.Outcome.SolverException:
          traceOutput = "solver exception";
          break;
        case VCGen.Outcome.Inconclusive:
          traceOutput = "inconclusive";
          break;
        case VCGen.Outcome.Errors:
          Contract.Assert(errors != null);
          traceOutput = string.Format("error{0}", errors.Count == 1 ? "" : "s");
          break;
      }

      return traceOutput;
    }


    private static void UpdateStatistics(PipelineStatistics stats, VC.VCGen.Outcome outcome,
      List<Counterexample> errors, bool wasCached)
    {
      Contract.Requires(stats != null);

      switch (outcome)
      {
        default:
          Contract.Assert(false); // unexpected outcome
          throw new cce.UnreachableException();
        case VCGen.Outcome.ReachedBound:
          Interlocked.Increment(ref stats.VerifiedCount);
          if (wasCached)
          {
            Interlocked.Increment(ref stats.CachedVerifiedCount);
          }

          break;
        case VCGen.Outcome.Correct:
          Interlocked.Increment(ref stats.VerifiedCount);
          if (wasCached)
          {
            Interlocked.Increment(ref stats.CachedVerifiedCount);
          }

          break;
        case VCGen.Outcome.TimedOut:
          Interlocked.Increment(ref stats.TimeoutCount);
          if (wasCached)
          {
            Interlocked.Increment(ref stats.CachedTimeoutCount);
          }

          break;
        case VCGen.Outcome.OutOfResource:
          Interlocked.Increment(ref stats.OutOfResourceCount);
          if (wasCached)
          {
            Interlocked.Increment(ref stats.CachedOutOfResourceCount);
          }

          break;
        case VCGen.Outcome.OutOfMemory:
          Interlocked.Increment(ref stats.OutOfMemoryCount);
          if (wasCached)
          {
            Interlocked.Increment(ref stats.CachedOutOfMemoryCount);
          }

          break;
        case VCGen.Outcome.SolverException:
          Interlocked.Increment(ref stats.SolverExceptionCount);
          if (wasCached)
          {
            Interlocked.Increment(ref stats.CachedSolverExceptionCount);
          }

          break;
        case VCGen.Outcome.Inconclusive:
          Interlocked.Increment(ref stats.InconclusiveCount);
          if (wasCached)
          {
            Interlocked.Increment(ref stats.CachedInconclusiveCount);
          }

          break;
        case VCGen.Outcome.Errors:
          int cnt = errors.Where(e => !e.IsAuxiliaryCexForDiagnosingTimeouts).Count();
          Interlocked.Add(ref stats.ErrorCount, cnt);
          if (wasCached)
          {
            Interlocked.Add(ref stats.CachedErrorCount, cnt);
          }

          break;
      }
    }


    public void ProcessErrors(List<Counterexample> errors, VC.VCGen.Outcome outcome, TextWriter tw,
      ErrorReporterDelegate er, Implementation impl = null)
    {
      var implName = impl != null ? impl.Name : null;

      if (errors != null)
      {
        errors.Sort(new CounterexampleComparer());
        foreach (Counterexample error in errors)
        {
          if (error.IsAuxiliaryCexForDiagnosingTimeouts)
          {
            continue;
          }

          var errorInfo = CreateErrorInformation(error, outcome);
          errorInfo.ImplementationName = implName;

          if (Options.XmlSink != null)
          {
            WriteErrorInformationToXmlSink(Options.XmlSink, errorInfo, error.Trace);
          }

          if (Options.ErrorTrace > 0)
          {
            errorInfo.Out.WriteLine("Execution trace:");
            error.Print(4, errorInfo.Out, b => { errorInfo.AddAuxInfo(b.tok, b.Label, "Execution trace"); });
            if (Options.EnhancedErrorMessages == 1 && error.AugmentedTrace != null && error.AugmentedTrace.Count > 0)
            {
              errorInfo.Out.WriteLine("Augmented execution trace:");
              error.AugmentedTrace.Iter(elem => errorInfo.Out.Write(elem));
            }
            if (Options.PrintErrorModel >= 1 && error.Model != null)
            {
              error.Model.Write(ExecutionEngine.ModelWriter == null ? errorInfo.Out : ExecutionEngine.ModelWriter);
            }
          }

          if (Options.ModelViewFile != null) {
            error.PrintModel(errorInfo.Model, error);
          }

          printer.WriteErrorInformation(errorInfo, tw);

          if (er != null)
          {
            lock (er)
            {
              er(errorInfo);
            }
          }
        }
      }
    }


    private ErrorInformation CreateErrorInformation(Counterexample error, VC.VCGen.Outcome outcome)
    {
      ErrorInformation errorInfo;
      var cause = "Error";
      if (outcome == VCGen.Outcome.TimedOut)
      {
        cause = "Timed out on";
      }
      else if (outcome == VCGen.Outcome.OutOfMemory)
      {
        cause = "Out of memory on";
      }
      else if (outcome == VCGen.Outcome.SolverException)
      {
        cause = "Solver exception on";
      }
      else if (outcome == VCGen.Outcome.OutOfResource)
      {
        cause = "Out of resource on";
      }

      if (error is CallCounterexample callError)
      {
        if (callError.FailingRequires.ErrorMessage == null || Options.ForceBplErrors)
        {
          errorInfo = errorInformationFactory.CreateErrorInformation(callError.FailingCall.tok,
            callError.FailingCall.ErrorData as string ?? callError.FailingCall.Description.FailureDescription,
            callError.RequestId, callError.OriginalRequestId, cause);
          errorInfo.Kind = ErrorKind.Precondition;
          errorInfo.AddAuxInfo(callError.FailingRequires.tok,
            callError.FailingRequires.ErrorData as string ?? callError.FailingRequires.Description.FailureDescription,
            "Related location");
        }
        else
        {
          errorInfo = errorInformationFactory.CreateErrorInformation(null,
            callError.FailingRequires.ErrorMessage,
            callError.RequestId, callError.OriginalRequestId);
        }
      }
      else if (error is ReturnCounterexample returnError)
      {
        if (returnError.FailingEnsures.ErrorMessage == null || Options.ForceBplErrors)
        {
          errorInfo = errorInformationFactory.CreateErrorInformation(returnError.FailingReturn.tok,
            returnError.FailingReturn.Description.FailureDescription,
            returnError.RequestId, returnError.OriginalRequestId, cause);
          errorInfo.Kind = ErrorKind.Postcondition;
          errorInfo.AddAuxInfo(returnError.FailingEnsures.tok,
            returnError.FailingEnsures.ErrorData as string ?? returnError.FailingEnsures.Description.FailureDescription,
            "Related location");
        }
        else
        {
          errorInfo = errorInformationFactory.CreateErrorInformation(null,
            returnError.FailingEnsures.ErrorMessage,
            returnError.RequestId, returnError.OriginalRequestId);
        }
      }
      else // error is AssertCounterexample
      {
        Debug.Assert(error is AssertCounterexample);
        var assertError = (AssertCounterexample)error;
        if (assertError.FailingAssert is LoopInitAssertCmd or LoopInvMaintainedAssertCmd)
        {
          errorInfo = errorInformationFactory.CreateErrorInformation(assertError.FailingAssert.tok,
            assertError.FailingAssert.Description.FailureDescription,
            assertError.RequestId, assertError.OriginalRequestId, cause);
          errorInfo.Kind = assertError.FailingAssert is LoopInitAssertCmd ?
            ErrorKind.InvariantEntry : ErrorKind.InvariantMaintainance;
          if ((assertError.FailingAssert.ErrorData as string) != null)
          {
            errorInfo.AddAuxInfo(assertError.FailingAssert.tok, assertError.FailingAssert.ErrorData as string,
              "Related message");
          }
        }
        else
        {
          if (assertError.FailingAssert.ErrorMessage == null || Options.ForceBplErrors)
          {
            string msg = assertError.FailingAssert.ErrorData as string ??
                         assertError.FailingAssert.Description.FailureDescription;
            errorInfo = errorInformationFactory.CreateErrorInformation(assertError.FailingAssert.tok, msg,
              assertError.RequestId, assertError.OriginalRequestId, cause);
            errorInfo.Kind = ErrorKind.Assertion;
          }
          else
          {
            errorInfo = errorInformationFactory.CreateErrorInformation(null, 
              assertError.FailingAssert.ErrorMessage,
              assertError.RequestId, assertError.OriginalRequestId);
          }
        }
      }

      return errorInfo;
    }

    private static void WriteErrorInformationToXmlSink(XmlSink sink, ErrorInformation errorInfo, List<Block> trace)
    {
      var msg = "assertion violation";
      switch (errorInfo.Kind)
      {
        case ErrorKind.Precondition:
          msg = "precondition violation";
          break;

        case ErrorKind.Postcondition:
          msg = "postcondition violation";
          break;

        case ErrorKind.InvariantEntry:
          msg = "loop invariant entry violation";
          break;

        case ErrorKind.InvariantMaintainance:
          msg = "loop invariant maintenance violation";
          break;
      }

      var relatedError = errorInfo.Aux.FirstOrDefault();
      sink.WriteError(msg, errorInfo.Tok, relatedError.Tok, trace);
    }

    public void Dispose()
    {
      checkerPool.Dispose();
    }
  }
}
