// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "tid"} X = int;

var {:layer 0,1} a:[int]int;

procedure {:yields} {:layer 1} Allocate() returns ({:linear "tid"} tid: int);

procedure {:atomic} {:layer 1} AtomicWrite(idx: int, val: int)
modifies a;
{ a[idx] := val; }

procedure {:yields} {:layer 0} {:refines "AtomicWrite"} Write(idx: int, val: int);

procedure {:yields} {:layer 1} main()
{
    var {:linear "tid"} i: int;
    var {:linear "tid"} j: int;
    call i := Allocate();
    call j := Allocate();
    par i := t(i) | Yield(j, a);
    par i := u(i) | j := u(j);
}

procedure {:yields} {:layer 1} t({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int)
{
    i := i';

    call Write(i, 42);
    call Yield(i, a);
    assert {:layer 1} a[i] == 42;
}

procedure {:yields} {:layer 1} {:yield_ensures "Yield_42", i, 42}
u({:linear_in "tid"} i': int) returns ({:linear "tid"} i: int)
{
    i := i';

    call Write(i, 42);
}

procedure {:yield_invariant} {:layer 1} Yield({:linear "tid"} i: int, old_a: [int]int);
requires old_a[i] == a[i];

procedure {:yield_invariant} {:layer 1} Yield_42({:linear "tid"} i: int, v: int);
requires v == a[i];
