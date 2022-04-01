// RUN: %parallel-boogie -contractInfer -printAssignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Houdini is very interactive and doesn't work with batch mode
// UNSUPPORTED: batch_mode
const {:existential true} b1:bool;
const {:existential true} b2:bool;


var myVar: int;

procedure bar(i:int) 
modifies myVar;
ensures b2==>myVar>0;
{
  call foo(5);
}

procedure foo (i:int)
modifies myVar;
ensures b1 ==> myVar>0;
ensures myVar!=-1;
{
  if (i>0) {
    myVar := 5;
  } else {
    myVar := 0;
  }
}

// expected output: Correct
// expected end assigment: b1->False b2->False
