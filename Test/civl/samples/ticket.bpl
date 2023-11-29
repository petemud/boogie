// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function RightOpen (n: int) : [int]bool;
function RightClosed (n: int) : [int]bool;
axiom (forall x: int, y: int :: RightOpen(x)[y] <==> y < x);
axiom (forall x: int, y: int :: RightClosed(x)[y] <==> y <= x);

type {:linear "tid"} X;
const nil: X;
var {:layer 0,1} t: int;       // next ticket to issue
var {:layer 0,2} s: int;       // current ticket permitted to critical section
var {:layer 1,2} cs: X;        // current thread in critical section
var {:layer 1,2} T: [int]bool; // set of issued tickets

// ###########################################################################
// Invariants

function {:inline} Inv1 (tickets: [int]bool, ticket: int): (bool)
{
  tickets == RightOpen(ticket)
}

function {:inline} Inv2 (tickets: [int]bool, ticket: int, lock: X): (bool)
{
  if (lock == nil) then tickets == RightOpen(ticket)
                   else tickets == RightClosed(ticket)
}

// ###########################################################################
// Yield invariants

yield invariant {:layer 2} YieldSpec ({:linear "tid"} tid: X);
invariant tid != nil && cs == tid;

yield invariant {:layer 1} Yield1 ();
invariant Inv1(T, t);

yield invariant {:layer 2} Yield2 ();
invariant Inv2(T, s, cs);

// ###########################################################################
// Procedures and actions

yield procedure {:layer 2} Customer ({:layer 1,2} {:linear_in "tid"} tid: X)
requires call Yield1();
requires call Yield2();
requires {:layer 2} tid != nil;
{
  while (*)
  invariant {:yields} true;
  invariant call Yield1();
  invariant call Yield2();
  {
    call Enter(tid);
    par Yield1() | Yield2() | YieldSpec(tid);
    call Leave(tid);
  }
}

yield procedure {:layer 2} Enter ({:layer 1,2} {:linear "tid"} tid: X)
preserves call Yield1();
preserves call Yield2();
ensures   call YieldSpec(tid);
requires {:layer 2} tid != nil;
{
  var m: int;

  call m := GetTicket(tid);
  call WaitAndEnter(tid, m);
}

right action {:layer 2} AtomicGetTicket ({:linear "tid"} tid: X) returns (m: int)
modifies T;
{ assume !T[m]; T[m] := true; }
yield procedure {:layer 1} GetTicket ({:layer 1} {:linear "tid"} tid: X) returns (m: int)
refines AtomicGetTicket;
preserves call Yield1();
{
  call m := GetTicket#0();
  call {:layer 1} T := Copy(T[m := true]);
}

atomic action {:layer 1} AtomicGetTicket#0 () returns (m: int)
modifies t;
{ m := t; t := t + 1; }
yield procedure {:layer 0} GetTicket#0 () returns (m: int);
refines AtomicGetTicket#0;

atomic action {:layer 2} AtomicWaitAndEnter ({:linear "tid"} tid: X, m:int)
modifies cs;
{ assume m == s; cs := tid; }
yield procedure {:layer 1} WaitAndEnter ({:layer 1} {:linear "tid"} tid: X, m:int)
refines AtomicWaitAndEnter;
preserves call Yield1();
{
  call WaitAndEnter#0(m);
  call {:layer 1} cs := Copy(tid);
}

atomic action {:layer 1} AtomicWaitAndEnter#0 (m:int)
{ assume m == s; }
yield procedure {:layer 0} WaitAndEnter#0 (m:int);
refines AtomicWaitAndEnter#0;

atomic action {:layer 2} AtomicLeave ({:linear "tid"} tid: X)
modifies cs, s;
{ assert cs == tid; s := s + 1; cs := nil; }
yield procedure {:layer 1} Leave ({:layer 1} {:linear "tid"} tid: X)
refines AtomicLeave;
preserves call Yield1();
{
  call Leave#0();
  call {:layer 1} cs := Copy(nil);
}

atomic action {:layer 1} AtomicLeave#0 ()
modifies s;
{ s := s + 1; }
yield procedure {:layer 0} Leave#0 ();
refines AtomicLeave#0;
