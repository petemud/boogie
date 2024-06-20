// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Value;

type Tid;

datatype StampedValue {
  StampedValue(ts: int, value: Value)
} 

datatype Permission {
    Permission(t_id: Tid, mem_index: int)
}

const n: int;
axiom n >= 1;

var {:layer 0,2} mem: [int]StampedValue;
var {:layer 0,2} r1: [Tid][int]StampedValue;  
var {:layer 0,2} r2: [Tid][int]StampedValue; 
var {:linear} {:layer 0,2} pSet: Set Permission;

function {:inline} WholeTidPermission(tid: Tid): Set Permission {
  Set((lambda {:pool "D"} x: Permission :: x->t_id == tid && (1 <= x->mem_index) && (x->mem_index <= n)))
}

action {:layer 1} start (tid: Tid)
modifies pSet;
creates main_f;
{
    var {:linear} sps: Set Permission;
    call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n)));
    call create_async(main_f(tid, sps));
}

// M =  main_f , \elim = read_f, I = Inv_f, M' = main_f'
async action {:layer 1} main_f(tid: Tid, {:linear_in} sps: Set Permission)
refines {:IS_right} main_f' using Inv_f;
modifies pSet;
creates read_f;
{
    // var {:linear} sps: Set Permission;
    assume {:add_to_pool "A", 0, n} true;
    assert (sps == Set((lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n))));
    call create_asyncs((lambda pa:read_f :: (1 <= pa->perm->val->mem_index) && (pa->perm->val->mem_index <= n) && pa->perm->val->t_id == tid));
}



action {:layer 2} main_f'(tid: Tid, {:linear_in} sps: Set Permission)
creates main_s;
modifies r1, pSet;
{
    var {:linear} sps2: Set Permission;
    var {:linear} done_set: Set Permission;
    sps2 := sps;
    assume {:add_to_pool "A", 0, n} true;
    assert (sps == Set((lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n))));
    havoc r1;
    assume (forall i:int :: ((1 <= i && i <= n) ==> (r1[tid][i]->ts < mem[i]->ts  || r1[tid][i]== mem[i]))); 
    call done_set := Set_Get(sps2, (lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n))); 
    call Set_Put(pSet, done_set);
    call create_async(main_s(tid));

}

async action {:layer 1} read_f({:linear_in} perm: One Permission)
creates read_f, main_s;
modifies r1, pSet;
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;
    assert 1 <= perm->val->mem_index && perm->val->mem_index <=n;
    assume {:add_to_pool "A", 0, n} true;
    assume {:exit_condition Set_IsSubset(WholeTidPermission(perm->val->t_id), pSet)} true;

    if (*) {
        assume {:add_to_pool "K", mem[perm->val->mem_index]->ts, k} {:add_to_pool "V", mem[perm->val->mem_index]->value, v} true;
        assume k < mem[perm->val->mem_index]->ts; 
        r1[perm->val->t_id][perm->val->mem_index]:= StampedValue(k, v);
    } else {
        r1[perm->val->t_id][perm->val->mem_index]:= mem[perm->val->mem_index];
    }
    call One_Put(pSet, perm);

    if (Set_IsSubset(WholeTidPermission(perm->val->t_id), pSet)){
        call create_async(main_s(perm->val->t_id));
    }
}


atomic action {: layer 1,2} write(i: int,v: Value)
modifies mem;
{
    var x: StampedValue;

    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
}

action {:layer 1} Inv_f(tid: Tid, {:linear_in} sps: Set Permission)
modifies r1, pSet;
creates read_f, main_s;
{
    var {:pool "A"} j: int;
    var {:linear} sps2: Set Permission;
    var {:linear} done_set: Set Permission;
    var choice: read_f;
    sps2 := sps;
    assert sps == WholeTidPermission(tid);
    assume {:add_to_pool "A", 0, j+1, n} 0 <= j && j <= n;
    havoc r1;
    assume (forall i:int :: ((1 <= i && i <= j) ==> (r1[tid][i]->ts < mem[i]->ts || r1[tid][i]== mem[i]))); 

    assume {:add_to_pool "D", Permission(tid, n)} true;
    call done_set := Set_Get(sps2, (lambda {:pool "D" } x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= j)));
  
    call Set_Put(pSet, done_set);
    if (j < n){
        choice := read_f(One(Permission(tid, j+1)));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C" } pa:read_f :: ((j+1) <=  pa->perm->val->mem_index) && ( pa->perm->val->mem_index <= n) && pa->perm->val->t_id == tid));
        call set_choice(choice);
    }
    else{
        call create_async(main_s(tid));
    }
}

// // ISL part
// M =  main_s , \elim = read_s, I = Inv_s, M' = main_s'
async action {:layer 1,2} main_s(tid: Tid)
// refines {:IS_left} main_s' using Inv_s;
// modifies pSet;
// creates read_s;
{
    // var {:linear} sps: Set Permission;

    // assume {:add_to_pool "A", 0} true;
    // call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n)));
    // call create_asyncs((lambda pa:read_s :: (1 <= pa->i) && (pa->i <= n) && pa->perm == One(Permission(tid, pa->i))));
}

// action {:layer 2} main_s'({:linear_in} tid: One Tid)
// modifies r2, pSet;
// {
//     var {:linear} sps: Set Permission;

//     call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n)));
//     havoc r2;
//     assume (forall i:int :: ((1 <= i && i <= n) ==> (r2[tid][i]->ts > mem[i]->ts  || r2[tid][i] == mem[i]))); 
// }

// async action {:layer 1} read_s({:linear_in} perm: One Permission, i: int)
// creates read_s;
// modifies r2;
// {
//     var {:pool "K"} k:int;
//     var {:pool "V"} v:Value;

//     if (*) {
//         assume {:add_to_pool "K", mem[i]->ts, k} {:add_to_pool "V", mem[i]->value, v} true;
//         assume k > mem[i]->ts; 
//         r2[perm->val->t_id][i] := StampedValue(k, v);
//     } else {
//         r2[perm->val->t_id][i] := mem[i];
//     }
// }

// action {:layer 1} Inv_s({:linear_in} tid: One Tid)
// modifies r2, pSet;
// creates read_s;
// {
//     var {:pool "A"} j: int;
//     var {:linear} sps: Set Permission;
//     var choice: read_s;

//     call sps := Set_Get(pSet, (lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n)));
//     assume {:add_to_pool "A", j+1} 0 <= j && j <= n;
//     havoc r2;
//     assume (forall i:int :: ((1 <= i && i <= j) ==> (r2[tid][i]->ts > mem[i]->ts || r2[tid][i] == mem[i]))); 
//     if (j < n){
//         choice := read_s(One(Permission(tid, j+1)), j+1);
//         assume {:add_to_pool "C", choice} true;
//         call create_asyncs((lambda {:pool "C" } pa:read_s :: ((j+1) <= pa->i) && (pa->i <= n) && pa->perm == One(Permission(tid, pa->i))));
//         call set_choice(choice);
//     }
// }

// permissions need to put back in globals to retry later
// how to know scan ended
// if r1 == r2, return snapshot 


// implement one iteration
// first scan, second scan 
// if it succeeds then good, otherwise nothing.



// prove that snapshot is correct if it succeeds.
// make it retryable anyway



// We check for exit that: 
// 1. assume exit, call A, any pa created is not in \elim  or no pa is created
// 2. assume not exit, call A, any pa created is in \elim or no pa is created
// Inconsistency check: forall E1, E2: (E1 and E2 are descendants of M) => gate(E1) and (gate(E2)+exit) can't be true together




// check 1: assume beta, any pa is in \elim or creates no pas
// check 2: assume not beta, any pa is not in \elim or create no pas
// beta = true as default (whole action is a right mover)

// chi = not beta (maybe)

// inconsistency: normal action execution , not beta action execution should be inconsistent together.


//specify negation : specify the exit (chi)

// async action {:layer 1, 2} gather_f()
// // modifies pSet;
// {
//     // call One_Put(pSet, perm);
//     // // call Set_Get(pSet(lambda x: Permission :: (x->t_id == tid) && (1 <= x->mem_index) && (x->mem_index <= n)));
//     // // if (*){
//     // assume Set_IsSubset(WholeTidPermission(tid), pSet);
//     // // }
// }