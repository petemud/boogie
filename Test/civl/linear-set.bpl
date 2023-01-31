// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "x", "tid"} X;

function {:inline} NoElems() : [X]bool
{
    MapConst(false)
}

function {:inline} AllElems() : [X]bool
{
    MapConst(true)
}

var {:layer 0,1} x: int;
var {:layer 0,1} l: [X]bool;


procedure {:yields} {:layer 1} Split({:linear_in "x"} xls: [X]bool) returns ({:linear "x"} xls1: [X]bool, {:linear "x"} xls2: [X]bool)
ensures {:layer 1} xls == MapOr(xls1, xls2) && xls1 != NoElems() && xls2 != NoElems();
{
  call xls1, xls2 := SplitLow(xls);
}

procedure {:yields} {:layer 1} Allocate() returns ({:linear "tid"} xls: [X]bool);

procedure {:atomic} {:layer 1} AtomicSet(v: int)
modifies x;
{ x := v; }

procedure {:yields} {:layer 0} {:refines "AtomicSet"} Set(v: int);

procedure {:atomic} {:layer 1} AtomicLock(tidls: [X]bool)
modifies l;
{ assume l == NoElems(); l := tidls; }

procedure {:yields} {:layer 0} {:refines "AtomicLock"} Lock(tidls: [X]bool);

procedure {:atomic} {:layer 1} AtomicUnlock()
modifies l;
{ l := NoElems(); }

procedure {:yields} {:layer 0} {:refines "AtomicUnlock"} Unlock();

procedure {:atomic} {:layer 1} AtomicSplitLow({:linear_in "x"} xls: [X]bool) returns ({:linear "x"} xls1: [X]bool, {:linear "x"} xls2: [X]bool)
{
  // xls == xls1 ⊎ xls2
  assume xls == MapOr(xls1, xls2);
  assume MapAnd(xls1, xls2) == NoElems();
  assume xls1 != NoElems();
  assume xls2 != NoElems();
}

procedure {:yields} {:layer 0} {:refines "AtomicSplitLow"} SplitLow({:linear_in "x"} xls: [X]bool) returns ({:linear "x"} xls1: [X]bool, {:linear "x"} xls2: [X]bool);

procedure {:yields} {:layer 1} main({:linear_in "tid"} tidls': [X]bool, {:linear_in "x"} xls': [X]bool)
requires {:layer 1} tidls' != NoElems() && xls' == AllElems();
{
    var {:linear "tid"} tidls: [X]bool;
    var {:linear "x"} xls: [X]bool;
    var {:linear "tid"} lsChild: [X]bool;
    var {:linear "x"} xls1: [X]bool;
    var {:linear "x"} xls2: [X]bool;

    tidls := tidls';
    xls := xls';

    call Set(42);
    yield;
    assert {:layer 1} xls == AllElems();
    assert {:layer 1} x == 42;
    call xls1, xls2 := Split(xls);
    call lsChild := Allocate();
    assume (lsChild != NoElems());
    yield;
    async call thread(lsChild, xls1);
    call lsChild := Allocate();
    assume (lsChild != NoElems());
    yield;
    async call thread(lsChild, xls2);
}

procedure {:yields} {:layer 1} thread({:linear_in "tid"} tidls': [X]bool, {:linear_in "x"} xls': [X]bool)
requires {:layer 1} tidls' != NoElems() && xls' != NoElems();
{
    var {:linear "x"} xls: [X]bool;
    var {:linear "tid"} tidls: [X]bool;

    tidls := tidls';
    xls := xls';

    call Lock(tidls);
    yield;
    assert {:layer 1} tidls != NoElems() && xls != NoElems();
    call Set(0);
    yield;
    assert {:layer 1} tidls != NoElems() && xls != NoElems();
    assert {:layer 1} x == 0;
    call Unlock();
}
