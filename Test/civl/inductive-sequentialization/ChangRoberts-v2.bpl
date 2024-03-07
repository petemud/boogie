// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const N: int; // size of the ring
axiom N > 0;

var {:layer 0,4} leader: [int]bool;       // leader[pid] iff pid is a leader

function {:inline} Pid(pid: int) : bool { 0 <= pid && pid < N }
function {:inline} Next(pid: int, i: int) : int { (pid + i) mod N }
function {:inline} Next_P(pa: P, i: int) : P
{
  P(Next(pa->self, i), Next(pa->pid, i))
}
function {:inline} Prev(pid: int, i: int) : int { (pid - i) mod N }
function {:inline} Prev_P(pa: P, i: int) : P
{
  P(Prev(pa->self, i), Prev(pa->pid, i))
}

// priority for becoming leader where ties are broken by pid
function Priority(int): int;      // pid -> priority
const ExpectedLeader: int;        // pid
axiom Pid(ExpectedLeader);
axiom (forall i: int:: Pid(i) ==> Priority(i) <= Priority(ExpectedLeader));
axiom (forall i: int:: Pid(i) && Priority(i) == Priority(ExpectedLeader) ==> i <= ExpectedLeader);

function {:inline} Below(self: int, pid: int): bool
{
  Priority(self) < Priority(pid) || 
  (Priority(self) == Priority(pid) && self < pid)
}

////////////////////////////////////////////////////////////////////////////////

function {:inline} Init(pids: [int]bool, leader: [int]bool) : bool
{
  pids == MapConst(true) &&
  leader == MapConst(false)
}

////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 4} MAIN3(pids: Set int)
modifies leader;
{
  assert Init(pids->val, leader);
  leader := MapConst(false)[ExpectedLeader := true];
}

action {:layer 3} INV2 (pids: Set int)
creates P;
modifies leader;
{
  var {:pool "INV2"} choice: P;
  var self, pid: int;

  assert Init(pids->val, leader);
  assume {:add_to_pool "P_MAIN2", choice} {:add_to_pool "INV2", P(Next(choice->self, 1), choice->pid), P(choice->pid, Prev(choice->pid, 1))} true;
  if (*) {
    call create_async(choice);
    call set_choice(choice);
    P(self, pid) := choice;
    assume Pid(self) && Pid(pid);
    if (pid != ExpectedLeader) {
      call create_asyncs(
        (lambda {:pool "P_INV2"} pa: P :: 
          {:add_to_pool "P_MAIN2", pa} 
          Pid(pa->pid) && pa->self == Next(pa->pid, 1) && Prev(pa->pid, ExpectedLeader) < Prev(pid, ExpectedLeader)));
    }
    if (self == pid) {
      assume (forall {:pool "ORDER"} x: int :: {:add_to_pool "ORDER", x} 0 < x && x < N ==> Below(Next(ExpectedLeader, x), ExpectedLeader));
    } else {
      assume (forall {:pool "ORDER"} x: int :: {:add_to_pool "ORDER", x} 0 < x && x < (self - pid) mod N ==> Below(Next(pid, x), pid));
    }
  } else {
    leader[ExpectedLeader] := true;
  }
}
////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 3} MAIN2(pids: Set int)
refines MAIN3 using INV2;
creates P;
{
  assert Init(pids->val, leader);
  assume {:add_to_pool "INV2", P(ExpectedLeader, Prev(ExpectedLeader, 1))} true;
  call create_asyncs(
    (lambda {:pool "P_MAIN2"} pa: P :: 
      {:add_to_pool "P_INV2", pa} 
      Pid(pa->pid) && pa->self == Next(pa->pid, 1)));
}

action {:layer 2} INV1({:linear_in} pids: Set int)
creates PInit, P;
{
  var {:pool "INV1"} k: int;
  assert Init(pids->val, leader);

  assume
    {:add_to_pool "INV1", k+1}
    {:add_to_pool "PInit", PInit(k), PInit(N)}
    0 <= k && k <= N;
  call create_asyncs((lambda {:pool "PInit"} pa: PInit :: k <= pa->self && pa->self < N));
  call create_asyncs((lambda pa: P :: 0 <= pa->pid && pa->pid < k && pa->self == Next(pa->pid, 1)));
  call set_choice(PInit(k));
}

////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 2} MAIN1(pids: Set int)
refines MAIN2 using INV1;
creates PInit;
{
  assert Init(pids->val, leader);
  assume {:add_to_pool "INV1", 0} true;
  call create_asyncs((lambda pa: PInit :: Pid(pa->self)));
}

async left action {:layer 2} PInit(self: int)
creates P;
{
  assert Pid(self);
  call create_async(P(Next(self, 1), self));
}

async atomic action {:layer 2, 3} P(self: int, pid: int)
creates P;
modifies leader;
{
  assert Pid(self) && Pid(pid);
  if (self == pid)
  {
    leader[pid] := true;
  }
  else if (Below(self, pid))
  {
    call create_async(P(Next(self, 1), pid));
    assume {:add_to_pool "P_INV2", P(Next(self, 1), pid)} true;
  }
}

////////////////////////////////////////////////////////////////////////////////

yield procedure {:layer 1} main(pids: Set int)
refines MAIN1;
{
  var {:pending_async}{:layer 1} PAs: [PInit]int;
  var pids': Set int;
  var i: int;

  pids' := pids;
  i := 0;
  while (i < N)
  invariant {:layer 1} 0 <= i && i <= N;
  invariant {:layer 1} (forall ii:int :: Pid(ii) && ii >= i ==> Set_Contains(pids', ii));
  invariant {:layer 1} PAs == (lambda pa: PInit :: if Pid(pa->self) && pa->self < i then 1 else 0);
  {
    pids' := Set_Remove(pids', i);
    async call pinit(i);
    i := i + 1;
  }
}

yield procedure {:layer 1} pinit(self: int)
refines PInit;
requires {:layer 1} Pid(self);
{
  async call p(Next(self, 1), self);
}

yield procedure {:layer 1} p(self: int, pid: int)
refines P;
requires {:layer 1} Pid(self) && Pid(pid);
{
  if (self == pid)
  {
    call set_leader(pid);
  }
  else if (Below(self, pid))
  {
    async call p(Next(self, 1), pid);
  }
}

////////////////////////////////////////////////////////////////////////////////

both action {:layer 1} SET_LEADER(pid: int)
modifies leader;
{
  leader[pid] := true;
}
yield procedure {:layer 0} set_leader(pid: int);
refines SET_LEADER;
