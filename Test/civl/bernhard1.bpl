// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "x"} X = int;
var {:linear "x"} {:layer 0,1} A : [int]bool;

procedure {:yields} {:layer 1} Proc ({:linear "x"} i: int)
{
  call {:layer 1} Lemma(A, i);
}

procedure {:lemma} Lemma (set: [int]bool, i: int);
requires !set[i];
