// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type X;
type {:linear "D"} Lin = int;

procedure A()
{
    var {:linear "D"} a: X;
    var {:linear "D"} b: int;
}

procedure B()
{
    var {:linear "D"} a: X;
    var {:linear "D"} b: [X]bool;
}

procedure C()
{
    var {:linear "D"} a: X;
    var {:linear "D"} c: [X]int;
}

function f(X): X;

yield procedure {:layer 1} D()
{
    var {:linear "D"} a: X;
    var {:linear "D"} x: X;
    var {:linear "D"} b: [X]bool;
    var c: X;
    var {:linear "D"} d: X;

    b[a] := true;

    a := c;

    c := a;

    a := d;

    a := a;

    a, x := x, a;

    a, x := x, x;

    call a, x := E(a, x);

    call a, x := E(a, a);

    call a, x := E(a, f(a));

    call a, x := E(a, d);

    call d, x := E(a, x);

    call a, x := E(c, x);

    call c, x := E(a, x);
}

yield procedure {:layer 1} E({:linear_in "D"} a: X, {:linear_in "D"} b: X) returns ({:linear "D"} c: X, {:linear "D"} d: X)
{
    c := a;
}

yield procedure {:layer 1} F({:linear_in "D"} a: X) returns ({:linear "D"} c: X);

var {:linear "D"} g:int;

procedure G(i:int) returns({:linear "D"} r:int)
{
  r := g;
}

procedure H(i:int) returns({:linear "D"} r:int)
modifies g;
{
  g := r;
}

yield procedure {:layer 1} I({:linear_in "D"} x:int) returns({:linear "D"} x':int)
{
  x' := x;
}

yield procedure {:layer 1} J()
{
}

yield procedure {:layer 1} P1({:linear_in "D"} x:int) returns({:linear "D"} x':int)
{
  par x' := I(x) | J();
  call x' := I(x');
}

yield procedure {:layer 1} P2({:linear_in "D"} x:int) returns({:linear "D"} x':int)
{
  call x' := I(x);
  par x' := I(x') | J();
}
