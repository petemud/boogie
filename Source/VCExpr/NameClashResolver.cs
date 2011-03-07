//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;

// Visitor that establishes unique variable (or constant) names in a VCExpr.
// This is done by adding a counter as suffix if name clashes occur

// TODO: also handle type variables here

namespace Microsoft.Boogie.VCExprAST {
  using TEHelperFuns = Microsoft.Boogie.TypeErasure.HelperFuns;

  public class UniqueNamer : ICloneable {
    public string Spacer = "@@";

    public UniqueNamer() {
      GlobalNames = new Dictionary<Object, string>();
      LocalNames = TEHelperFuns.ToList(new Dictionary<Object/*!*/, string/*!*/>()
                                         as IDictionary<Object/*!*/, string/*!*/>);
      UsedNames = new Dictionary<string, bool>();
      CurrentCounters = new Dictionary<string, int>();
      GlobalPlusLocalNames = new Dictionary<Object, string>();
    }

    private UniqueNamer(UniqueNamer namer) {
      Contract.Requires(namer != null);
      Spacer = namer.Spacer;
      GlobalNames = new Dictionary<Object, string>(namer.GlobalNames);

      List<IDictionary<Object/*!*/, string/*!*/>/*!*/>/*!*/ localNames =
        new List<IDictionary<Object, string>>();
      LocalNames = localNames;

      foreach (IDictionary<Object/*!*/, string/*!*/>/*!*/ d in namer.LocalNames)
        localNames.Add(new Dictionary<Object/*!*/, string/*!*/>(d));

      UsedNames = new Dictionary<string, bool>(namer.UsedNames);
      CurrentCounters = new Dictionary<string, int>(namer.CurrentCounters);
      GlobalPlusLocalNames = new Dictionary<Object, string>(namer.GlobalPlusLocalNames);
    }

    public Object Clone() {
      Contract.Ensures(Contract.Result<Object>() != null);
      return new UniqueNamer(this);
    }

    ////////////////////////////////////////////////////////////////////////////

    private readonly IDictionary<Object/*!*/, string/*!*/>/*!*/ GlobalNames;
    [ContractInvariantMethod]
    void GlobalNamesInvariantMethod() {
      Contract.Invariant(cce.NonNullElements(GlobalNames));
    }
    private readonly List<IDictionary<Object/*!*/, string/*!*/>/*!*/>/*!*/ LocalNames;
    [ContractInvariantMethod]
    void LocalNamesInvariantMethod() {
      Contract.Invariant(Contract.ForAll(LocalNames, i => i != null && cce.NonNullElements(i)));
    }

    // dictionary of all names that have already been used
    // (locally or globally)
    private readonly IDictionary<string/*!*/, bool/*!*/>/*!*/ UsedNames;
    [ContractInvariantMethod]
    void UsedNamesInvariantMethod() {
      Contract.Invariant(cce.NonNullElements(UsedNames));
    }
    private readonly IDictionary<string/*!*/, int/*!*/>/*!*/ CurrentCounters;
    [ContractInvariantMethod]
    void CurrentCountersInvariantMethod() {
      Contract.Invariant(cce.NonNullElements(CurrentCounters));
    }
    private readonly IDictionary<Object/*!*/, string/*!*/>/*!*/ GlobalPlusLocalNames;
    [ContractInvariantMethod]
    void GlobalPlusLocalNamesInvariantMethod() {
      Contract.Invariant(cce.NonNullElements(GlobalPlusLocalNames));
    }

    ////////////////////////////////////////////////////////////////////////////

    public void PushScope() {
      LocalNames.Add(new Dictionary<Object/*!*/, string/*!*/>());
    }

    public void PopScope() {
      LocalNames.RemoveAt(LocalNames.Count - 1);
    }

    ////////////////////////////////////////////////////////////////////////////

    private string NextFreeName(Object thingie, string baseName) {
      Contract.Requires(baseName != null);
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string/*!*/ candidate;
      int counter;

      if (CurrentCounters.TryGetValue(baseName, out counter)) {
        candidate = baseName + Spacer + counter;
        counter = counter + 1;
      } else {
        candidate = baseName;
        counter = 0;
      }

      bool dummy;
      while (UsedNames.TryGetValue(candidate, out dummy)) {
        candidate = baseName + Spacer + counter;
        counter = counter + 1;
      }

      UsedNames.Add(candidate, true);
      CurrentCounters[baseName] = counter;
      GlobalPlusLocalNames[thingie] = candidate;
      return candidate;
    }

    // retrieve the name of a thingie; if it does not have a name yet,
    // generate a unique name for it (as close as possible to its inherent
    // name) and register it globally
    public string GetName(Object thingie, string inherentName) {
      Contract.Requires(inherentName != null);
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string res = this[thingie];

      if (res != null)
        return res;

      // if the object is not yet registered, create a name for it
      res = NextFreeName(thingie, inherentName);
      GlobalNames.Add(thingie, res);

      return res;
    }

    [Pure]
    public string this[Object/*!*/ thingie] {
      get {
        Contract.Requires(thingie != null);

        string res;
        for (int i = LocalNames.Count - 1; i >= 0; --i) {
          if (LocalNames[i].TryGetValue(thingie, out res))
            return res;
        }

        GlobalNames.TryGetValue(thingie, out res);
        return res;
      }
    }

    public string GetLocalName(Object thingie, string inherentName) {
      Contract.Requires(inherentName != null);
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string res = NextFreeName(thingie, inherentName);
      LocalNames[LocalNames.Count - 1][thingie] = res;
      return res;
    }

    public virtual string GetQuotedName(Object thingie, string inherentName)
    {
      return GetName(thingie, inherentName);
    }

    public virtual string GetQuotedLocalName(Object thingie, string inherentName)
    {
      return GetLocalName(thingie, inherentName);
    }

    public string Lookup(Object thingie) {
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string name;
      if (GlobalPlusLocalNames.TryGetValue(thingie, out name))
        return name;
      return Spacer + "undefined" + Spacer + thingie.GetHashCode() + Spacer;
    }
  }
}
