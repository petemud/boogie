// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} X;
const nil: X;

var {:layer 0,3} g: Lmap int int;
var {:layer 0,3} lock: X;
var {:layer 0,1} b: bool;

const p: int;

yield invariant {:layer 1} InvLock();
invariant lock != nil <==> b;

yield invariant {:layer 3} InvMem();
invariant Map_Contains(g->val, p) && Map_Contains(g->val, p+4) && Map_At(g->val, p) == Map_At(g->val, p+4);

yield procedure {:layer 3} P({:linear "tid"} tid: X)
requires {:layer 1,3} tid != nil;
preserves call InvLock();
preserves call InvMem();
{
    var t: int;
    var l: Lmap int int;

    call AcquireProtected(tid);
    call l := TransferFromGlobalProtected(tid);
    call t := Load(l, p);
    call l := Store(l, p, t+1);
    call t := Load(l, p+4);
    call l := Store(l, p+4, t+1);
    call TransferToGlobalProtected(tid, l);
    call ReleaseProtected(tid);
}

both action {:layer 3} AtomicTransferToGlobalProtected({:linear "tid"} tid: X, {:linear_in} l: Lmap int int)
modifies g;
{ assert tid != nil && lock == tid; g := l; }

yield procedure {:layer 2}
TransferToGlobalProtected({:linear "tid"} tid: X, {:linear_in} l: Lmap int int)
refines AtomicTransferToGlobalProtected;
preserves call InvLock();
{
  call TransferToGlobal(tid, l);
}

both action {:layer 3} AtomicTransferFromGlobalProtected({:linear "tid"} tid: X) returns (l: Lmap int int)
modifies g;
{ assert tid != nil && lock == tid; l := g; call g := Lmap_Empty(); }

yield procedure {:layer 2}
TransferFromGlobalProtected({:linear "tid"} tid: X) returns (l: Lmap int int)
refines AtomicTransferFromGlobalProtected;
preserves call InvLock();
{
  call l := TransferFromGlobal(tid);
}

right action {:layer 3} AtomicAcquireProtected({:linear "tid"} tid: X)
modifies lock;
{ assert tid != nil; assume lock == nil; lock := tid; }

yield procedure {:layer 2} AcquireProtected({:linear "tid"} tid: X)
refines AtomicAcquireProtected;
requires {:layer 1} tid != nil;
preserves call InvLock();
{
  call Acquire(tid);
}

left action {:layer 3} AtomicReleaseProtected({:linear "tid"} tid: X)
modifies lock;
{ assert tid != nil && lock == tid; lock := nil; }

yield procedure {:layer 2} ReleaseProtected({:linear "tid"} tid: X)
refines AtomicReleaseProtected;
preserves call InvLock();
{
  call Release(tid);
}

atomic action {:layer 2} AtomicAcquire({:linear "tid"} tid: X)
modifies lock;
{ assume lock == nil; lock := tid; }

yield procedure {:layer 1} Acquire({:linear "tid"} tid: X)
refines AtomicAcquire;
requires {:layer 1} tid != nil;
preserves call InvLock();
{
    var status: bool;
    var tmp: X;

    while (true)
    invariant {:yields} true;
    invariant call InvLock();
    {
        call status := CAS(tid, false, true);
        if (status) {
            return;
        }
    }
}

atomic action {:layer 2} AtomicRelease({:linear "tid"} tid: X)
modifies lock;
{ lock := nil; }

yield procedure {:layer 1} Release({:linear "tid"} tid: X)
refines AtomicRelease;
preserves call InvLock();
{
  call CLEAR(tid, false);
}

atomic action {:layer 1,2} AtomicTransferToGlobal({:linear "tid"} tid: X, {:linear_in} l: Lmap int int)
modifies g;
{ g := l; }

yield procedure {:layer 0} TransferToGlobal({:linear "tid"} tid: X, {:linear_in} l: Lmap int int);
refines AtomicTransferToGlobal;

atomic action {:layer 1,2} AtomicTransferFromGlobal({:linear "tid"} tid: X) returns (l: Lmap int int)
modifies g;
{ l := g; call g := Lmap_Empty(); }

yield procedure {:layer 0} TransferFromGlobal({:linear "tid"} tid: X) returns (l: Lmap int int);
refines AtomicTransferFromGlobal;

both action {:layer 1,3} AtomicLoad(l: Lmap int int, a: int) returns (v: int)
{ v := l->val->val[a]; }

yield procedure {:layer 0} Load(l: Lmap int int, a: int) returns (v: int);
refines AtomicLoad;

both action {:layer 1,3} AtomicStore({:linear_in} l_in: Lmap int int, a: int, v: int) returns (l_out: Lmap int int)
{ l_out := l_in; l_out->val->val[a] := v; }

yield procedure {:layer 0} Store({:linear_in} l_in: Lmap int int, a: int, v: int) returns (l_out: Lmap int int);
refines AtomicStore;

atomic action {:layer 1} AtomicCAS(tid: X, prev: bool, next: bool) returns (status: bool)
modifies b, lock;
{
  if (*) {
    assume b == prev; b := next; status := true; lock := tid;
  } else {
    status := false;
  }
}

yield procedure {:layer 0} CAS(tid: X, prev: bool, next: bool) returns (status: bool);
refines AtomicCAS;

atomic action {:layer 1} AtomicCLEAR(tid: X, next: bool)
modifies b, lock;
{ b := next; lock := nil; }

yield procedure {:layer 0} CLEAR(tid: X, next: bool);
refines AtomicCLEAR;
