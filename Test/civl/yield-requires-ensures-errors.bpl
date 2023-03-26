// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:linear "lin"} X = int;
var {:layer 0,1} x:int;
yield invariant {:layer 1} yield_x(n: int);
invariant x >= n;

yield invariant {:layer 1} linear_yield_x({:linear "lin"} n: int);
invariant x >= n;

yield procedure {:layer 1} p0()
requires call yield_x(x == 4);
ensures call yield_x(x == 8);
{
}

yield procedure {:layer 1} p1(a: int) returns (c: int)
//requires call yield_x(c);
requires call linear_yield_x(a);
ensures call yield_x(a + c);
{
}

yield procedure {:layer 1} p2({:layer 0,0} a: int) returns (c: int)
requires call yield_x(a);
ensures call yield_x(a + c);
{
}

yield procedure {:layer 1}
p3({:linear "lin"} a: int, {:linear_in "lin"} b: int, {:linear_out "lin"} c: int);
requires call linear_yield_x(a);
ensures call linear_yield_x(a);
requires call linear_yield_x(c);
ensures call linear_yield_x(b);
