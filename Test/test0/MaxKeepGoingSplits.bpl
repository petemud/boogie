// First line checks for a deadlock
// RUN: %boogie /vcsMaxKeepGoingSplits:2 /proverOpt:O:smt.qi.eager_threshold=100 "%s"
// RUN: %boogie /vcsCores:3 /vcsMaxKeepGoingSplits:2 /trace /proverOpt:O:smt.qi.eager_threshold=100 "%s" > %t.log
// RUN: %OutputCheck --file-to-check "%t.log" "%s"
// CHECK-L: checking split 1/1
// CHECK-L: checking split 2/3
// CHECK-L: checking split 3/3
// CHECK-L: checking split 4/5
// CHECK-L: checking split 5/5
// CHECK-L: checking split 1/1, 0.00%, (cost:4/1 last) ...
// CHECK-L: Boogie program verifier finished with 1 verified, 1 error

function f(i:int, j:int) returns (int)
{
    if i == 0 then 0 else f(i - 1, i * j + 1) + f(i - 1, 2 * i * j)
}

// Without the max keep going splits this runs out of resources.
procedure {:rlimit 150000} test1(x:int)
{
    assert(f(8,3) == 0);
    assert(f(8,4) == 0);
    assert(f(8,5) == 0);
    assert(f(9,2) == 0);
}

// Runs out of resources
procedure {:rlimit 150000} test2(x:int)
{
    assert(f(8,3) == 0 && f(8,4) == 0 && f(8,5) == 0 && f(9,2) == 0);
}
