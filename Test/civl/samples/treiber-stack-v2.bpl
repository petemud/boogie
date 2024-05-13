// RUN: %parallel-boogie -lib:base -lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype LocPiece { Left(), Right() }
const AllLocPieces: [LocPiece]bool;
axiom AllLocPieces == MapConst(false)[Left() := true][Right() := true];

type TreiberNode _;
type LocTreiberNode T = Fraction (Loc (TreiberNode T)) LocPiece;
type StackElem T = Node (LocTreiberNode T) T;
type StackMap T = Map (LocTreiberNode T) (StackElem T);
datatype Treiber<T> { Treiber(top: Option (LocTreiberNode T), {:linear} stack: StackMap T) }

type X; // module type parameter

var {:layer 4, 5} Stack: Map (Loc (Treiber X)) (Vec X);
var {:layer 0, 4} {:linear} ts: Map (Loc (Treiber X)) (Treiber X);

function {:inline} Domain(ts: Map (Loc (Treiber X)) (Treiber X), loc_t: Loc (Treiber X)): Set (LocTreiberNode X) {
  ts->val[loc_t]->stack->dom
}

yield invariant {:layer 1} Yield1();

yield invariant {:layer 2} TopInStack(loc_t: Loc (Treiber X));
invariant (var loc_n := Map_At(ts, loc_t)->top; loc_n is None || Set_Contains(Domain(ts, loc_t), loc_n->t));
invariant (forall loc_n: LocTreiberNode X :: Set_Contains(Domain(ts, loc_t), loc_n) ==> 
              (var loc_n' := Map_At(Map_At(ts, loc_t)->stack, loc_n)->next; loc_n' is None || Set_Contains(Domain(ts, loc_t), loc_n'->t)));

yield invariant {:layer 2} LocInStack(loc_t: Loc (Treiber X), loc_n: Option (LocTreiberNode X));
invariant loc_n is None || Set_Contains(Domain(ts, loc_t), loc_n->t);

yield invariant {:layer 4} ReachInStack(loc_t: Loc (Treiber X));
invariant Map_Contains(ts, loc_t);
invariant (var t := ts->val[loc_t]; Between(t->stack->val, t->top, t->top, None()));
invariant (var t := ts->val[loc_t]; IsSubset(BetweenSet(t->stack->val, t->top, None()), Domain(ts, loc_t)->val));
invariant (var loc_n := Map_At(ts, loc_t)->top; loc_n is None || Set_Contains(Domain(ts, loc_t), loc_n->t));
invariant (forall {:pool "A"} loc_n: LocTreiberNode X :: {:add_to_pool "A", loc_n} Set_Contains(Domain(ts, loc_t), loc_n) ==>
              loc_n == Fraction(loc_n->val, Left(), AllLocPieces) &&
              (var loc_n' := Map_At(Map_At(ts, loc_t)->stack, loc_n)->next; loc_n' is None || Set_Contains(Domain(ts, loc_t), loc_n'->t)));

yield invariant {:layer 4} PushLocInStack(
  loc_t: Loc (Treiber X), loc_n: Option (LocTreiberNode X), new_loc_n: LocTreiberNode X, {:linear} right_loc_piece: One (LocTreiberNode X));
invariant Set_Contains(Domain(ts, loc_t), new_loc_n);
invariant right_loc_piece->val == Fraction(new_loc_n->val, Right(), AllLocPieces);
invariant new_loc_n == Fraction(new_loc_n->val, Left(), AllLocPieces);
invariant (var t := ts->val[loc_t]; Map_At(t->stack, new_loc_n)->next == loc_n && !BetweenSet(t->stack->val, t->top, None())[new_loc_n]);

yield procedure {:layer 4} Push(loc_t: Loc (Treiber X), x: X) returns (success: bool)
preserves call TopInStack(loc_t);
preserves call ReachInStack(loc_t);
{
  var loc_n: Option (LocTreiberNode X);
  var new_loc_n: LocTreiberNode X;
  var {:linear} right_loc_piece: One (LocTreiberNode X);

  call loc_n, new_loc_n, right_loc_piece := AllocNode#3(loc_t, x);
  par ReachInStack(loc_t) | PushLocInStack(loc_t, loc_n, new_loc_n, right_loc_piece);
  call success := WriteTopOfStack#0(loc_t, loc_n, Some(new_loc_n));  
}

yield procedure {:layer 4} Pop(loc_t: Loc (Treiber X)) returns (success: bool, x: X)
preserves call TopInStack(loc_t);
preserves call ReachInStack(loc_t);
{
  call success, x := PopIntermediate(loc_t);
}

atomic action {:layer 4} AtomicAllocNode#3(loc_t: Loc (Treiber X), x: X)
  returns (loc_n: Option (LocTreiberNode X), new_loc_n: LocTreiberNode X, {:linear} right_loc_piece: One (LocTreiberNode X))
modifies ts;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} treiber: Treiber X;
  var top: Option (LocTreiberNode X);
  var {:linear} stack: StackMap X;
  var {:linear} one_loc_n: One (Loc (TreiberNode X));
  var {:linear} cell_n: Cell (LocTreiberNode X) (StackElem X);
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);
  var {:linear} loc_pieces: Set (Fraction (Loc (TreiberNode X)) LocPiece);
  var {:linear} left_loc_piece: One (Fraction (Loc (TreiberNode X)) LocPiece);
  
  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  Treiber(top, stack) := treiber;
  assume loc_n is None || Map_Contains(stack, loc_n->t);
  call one_loc_n := One_New();
  call loc_pieces := One_To_Fractions(one_loc_n, AllLocPieces);
  call left_loc_piece := One_Get(loc_pieces, Fraction(one_loc_n->val, Left(), AllLocPieces));
  new_loc_n := left_loc_piece->val;
  call right_loc_piece := One_Get(loc_pieces, Fraction(one_loc_n->val, Right(), AllLocPieces));
  call cell_n := Cell_Pack(left_loc_piece, Node(loc_n, x));
  call Map_Put(stack, cell_n);
  treiber := Treiber(top, stack);
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 3} AllocNode#3(loc_t: Loc (Treiber X), x: X)
  returns (loc_n: Option (LocTreiberNode X), new_loc_n: LocTreiberNode X, {:linear} right_loc_piece: One (LocTreiberNode X))
preserves call TopInStack(loc_t);
ensures call LocInStack(loc_t, Some(new_loc_n));
refines AtomicAllocNode#3;
{
  var {:linear} one_loc_n: One (Loc (TreiberNode X));
  var {:linear} cell_n: Cell (LocTreiberNode X) (StackElem X);
  var {:linear} loc_pieces: Set (Fraction (Loc (TreiberNode X)) LocPiece);
  var {:linear} left_loc_piece: One (Fraction (Loc (TreiberNode X)) LocPiece);

  call loc_n := ReadTopOfStack#2(loc_t);
  call one_loc_n := One_New();
  call loc_pieces := One_To_Fractions(one_loc_n, AllLocPieces);
  call left_loc_piece := One_Get(loc_pieces, Fraction(one_loc_n->val, Left(), AllLocPieces));
  new_loc_n := left_loc_piece->val;
  call right_loc_piece := One_Get(loc_pieces, Fraction(one_loc_n->val, Right(), AllLocPieces));
  call cell_n := Cell_Pack(left_loc_piece, Node(loc_n, x));
  call AllocNode#0(loc_t, cell_n);
}

atomic action {:layer 4} AtomicPopIntermediate(loc_t: Loc (Treiber X)) returns (success: bool, x: X)
modifies ts;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var loc_n: Option (LocTreiberNode X);
  var {:linear} treiber: Treiber X;
  var top: Option (LocTreiberNode X);
  var {:linear} stack: StackMap X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);

  assert Map_Contains(ts, loc_t);
  if (success) {
    call cell_t := Map_Get(ts, loc_t);
    call one_loc_t, treiber := Cell_Unpack(cell_t);
    Treiber(top, stack) := treiber;
    assume top != None();
    assume Map_Contains(stack, top->t);
    Node(loc_n, x) := Map_At(stack, top->t);
    treiber := Treiber(loc_n, stack);
    call cell_t := Cell_Pack(one_loc_t, treiber);
    call Map_Put(ts, cell_t);
  }
}
yield procedure {:layer 3} PopIntermediate(loc_t: Loc (Treiber X)) returns (success: bool, x: X)
refines AtomicPopIntermediate;
preserves call TopInStack(loc_t);
{
  var loc_n, new_loc_n: Option (LocTreiberNode X);
  var node: StackElem X;

  success := false;
  call loc_n := ReadTopOfStack#2(loc_t);
  if (loc_n == None()) {
    return;
  }
  par LocInStack(loc_t, loc_n) | TopInStack(loc_t);
  call node := LoadNode#0(loc_t, loc_n->t);
  call Yield1();
  Node(new_loc_n, x) := node;
  call success := WriteTopOfStack#0(loc_t, loc_n, new_loc_n);
}

right action {:layer 3} AtomicReadTopOfStack#2(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X))
{
  assert Map_Contains(ts, loc_t);
  assume loc_n is None || Set_Contains(Domain(ts, loc_t), loc_n->t);
}
yield procedure {:layer 2} ReadTopOfStack#2(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X))
preserves call TopInStack(loc_t);
ensures call LocInStack(loc_t, loc_n);
refines AtomicReadTopOfStack#2;
{
  call loc_n := ReadTopOfStack#0(loc_t);
}

right action {:layer 2,3} AtomicLoadNode#1(loc_t: Loc (Treiber X), loc_n: LocTreiberNode X) returns (node: StackElem X)
{
  assert Map_Contains(ts, loc_t);
  assert Map_Contains(Map_At(ts, loc_t)->stack, loc_n);
  node := Map_At(Map_At(ts, loc_t)->stack, loc_n);
}

// primitives

atomic action {:layer 1} AtomicLoadNode#0(loc_t: Loc (Treiber X), loc_n: LocTreiberNode X) returns (node: StackElem X)
modifies ts;
refines AtomicLoadNode#1;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} treiber: Treiber X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);
  var top: Option (LocTreiberNode X);
  var {:linear} stack: StackMap X;
  var {:linear} one_loc_n: One (LocTreiberNode X);
  var {:linear} cell_n: Cell (LocTreiberNode X) (StackElem X);

  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  Treiber(top, stack) := treiber;
  call cell_n := Map_Get(stack, loc_n);
  call one_loc_n, node := Cell_Unpack(cell_n);
  call cell_n := Cell_Pack(one_loc_n, node);
  call Map_Put(stack, cell_n);
  treiber := Treiber(top, stack);
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} LoadNode#0(loc_t: Loc (Treiber X), loc_n: LocTreiberNode X) returns (node: StackElem X);
refines AtomicLoadNode#0;

atomic action {:layer 1,2} AtomicReadTopOfStack#0(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X))
modifies ts;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} treiber: Treiber X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);

  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  loc_n := treiber->top;
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} ReadTopOfStack#0(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X));
refines AtomicReadTopOfStack#0;

atomic action {:layer 1,4} AtomicWriteTopOfStack#0(
  loc_t: Loc (Treiber X), old_loc_n: Option (LocTreiberNode X), new_loc_n: Option (LocTreiberNode X)) returns (r: bool)
modifies ts;
{
  var {:linear} treiber: Treiber X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);
  var {:linear} one_loc_t: One (Loc (Treiber X));

  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  if (old_loc_n == treiber->top) {
    treiber->top := new_loc_n;
    r := true;
  } else {
    r := false;
  }
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} WriteTopOfStack#0(loc_t: Loc (Treiber X), old_loc_n: Option (LocTreiberNode X), new_loc_n: Option (LocTreiberNode X)) returns (r: bool);
refines AtomicWriteTopOfStack#0;

atomic action {:layer 1,3} AtomicAllocNode#0(loc_t: Loc (Treiber X), {:linear_in} cell_n: Cell (LocTreiberNode X) (StackElem X))
modifies ts;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} treiber: Treiber X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);

  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  call Map_Put(treiber->stack, cell_n);
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} AllocNode#0(loc_t: Loc (Treiber X), {:linear_in} cell_n: Cell (LocTreiberNode X) (StackElem X));
refines AtomicAllocNode#0;

atomic action {:layer 1,4} AtomicAllocTreiber#0({:linear_in} cell_t: Cell (Loc (Treiber X)) (Treiber X))
modifies ts;
{
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} AllocTreiber#0({:linear_in} cell_t: Cell (Loc (Treiber X)) (Treiber X));
refines AtomicAllocTreiber#0;

