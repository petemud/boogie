// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Value;

type Tid;

datatype StampedValue {
    StampedValue(ts: int, value: Value)
} 

// datatype Permission {
//     Permission(tid: , mem_index: int)
// }

type Channel; // Send + Receive
type ChannelPiece = Fraction (Loc Channel) ChannelOp; // Send or Receive piece
type MemIndexPiece = Fraction ChannelPiece int; // Each mem index piece of Channel Piece

type Snapshot = [int]StampedValue;

datatype ChannelOp {
    Send(),
    Receive()
}

function {:inline} ChannelOps(): Set ChannelOp {
  Set_Add(Set_Add(Set_Empty(), Send()), Receive())
}



function {:inline} IsSend(piece: ChannelPiece): bool {
    piece == Fraction(piece->val, Send(), ChannelOps())
}

function {:inline} IsReceive(piece: ChannelPiece): bool {
    piece == Fraction(piece->val, Receive(), ChannelOps())
}

function {:inline} ToSend(piece: ChannelPiece): ChannelPiece {
    Fraction(piece->val, Send(), piece->ids)
}

const n: int;
axiom n >= 1;

var {:layer 0,3} mem: Snapshot;
var {:linear} {:layer 0,3} pSet: Set MemIndexPiece;
// var {:layer 0,3} channels: [Tid](Option Snapshot);
var {:layer 0,2} snapshots: [Loc Channel]Snapshot;  
var {:linear} {:layer 0,3} contents: Map ChannelPiece Snapshot;// contains only Send pieces

function {:inline} AllMemIndexPieces(s: ChannelPiece): Set MemIndexPiece {
    Set((lambda {:pool "D"} x: MemIndexPiece :: x->val == s && x->ids == MemIndices() && Set_Contains(x->ids,x->id)))
}


function {:inline} MemIndices(): Set int {
    Set((lambda {:pool "E" } x: int :: 1 <= x && x <= n))
}


atomic action {:layer 1,3} Send({:linear_in} one_s: One ChannelPiece, snapshot: Snapshot)
modifies contents;
{
    var {:linear} cell: Cell ChannelPiece Snapshot;
    assert IsSend(one_s->val);
    call cell := Cell_Pack(one_s, snapshot);
    call Map_Put(contents, cell);
}

right action {:layer 1,3} action_Receive({:linear} one_r: One ChannelPiece) returns ({:linear} one_s: One ChannelPiece, snapshot: Snapshot)
modifies contents;
{
    var {:linear} cell: Cell ChannelPiece Snapshot;
    var s: ChannelPiece;
    assert IsReceive(one_r->val);
    s := ToSend(one_r->val);
    assume Map_Contains(contents, s);
    call cell := Map_Get(contents, s);
    call one_s, snapshot := Cell_Unpack(cell);
}
yield procedure {:layer 0} Receive({:linear} one_r: One ChannelPiece) returns ({:linear} one_s: One ChannelPiece, snapshot: Snapshot);
refines action_Receive;

yield procedure  {:layer 2} coordinator() returns (snapshot: [int]StampedValue)
{
    var {:linear} one_loc_channel: One (Loc Channel);
    var {:linear} one_loc_channel_pieces: Set ChannelPiece;
    var {:linear} s: ChannelPiece;
    var {:linear} r: ChannelPiece;
    var {:linear} one_s: One ChannelPiece;
    var {:linear} one_r: One ChannelPiece;
    var {:linear} sps: Set MemIndexPiece;
    var snapshot': Snapshot;

    call one_loc_channel := One_New();
    call one_loc_channel_pieces := One_To_Fractions(one_loc_channel, ChannelOps());
    s := Fraction(one_loc_channel->val, Send(), ChannelOps());
    call one_s := One_Get(one_loc_channel_pieces, s);
    r := Fraction(one_loc_channel->val, Receive(), ChannelOps());
    call one_r := One_Get(one_loc_channel_pieces, r);

    while (true)
    invariant {:yields} true;
    {
        call sps:= One_To_Fractions(one_s, MemIndices());
        async call main_f(one_s->val, sps);
        
        call Yield1(); call Yield2();

        call one_s, snapshot := Receive(one_r); // right
        call sps:= One_To_Fractions(one_s,  MemIndices()); //local
        call main_s(one_s->val, sps);// 

        call Yield1(); call Yield2();

        call one_s, snapshot' := Receive(one_r); // right
        if (snapshot == snapshot') {
            return;
        }
    }
}

yield invariant {:layer 1} Yield1();
invariant true;
yield invariant {:layer 2} Yield2();
invariant true;

atomic action {:layer 1,2} write(i: int,v: Value)
modifies mem;
{
    var x: StampedValue;
    x := mem[i];
    mem[i] := StampedValue(x->ts + 1, v);
}
/////////////////////////////////////////////////////////////////////////////////////////////

async action {:layer 1} action_main_f(send: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
refines {:IS_right} main_f' using Inv_f;
modifies pSet;
creates read_f;
{
    assume {:add_to_pool "A", 0, n} true;
    assert sps == AllMemIndexPieces(send);
    // assert channels[tid] == None();
    call create_asyncs((lambda pa:read_f :: pa->s == send && Set_Contains(sps, pa->perm->val)));
}
yield procedure {:layer 0} main_f(send: ChannelPiece, {:linear_in} sps: Set MemIndexPiece);
refines action_main_f;

async action {:layer 2,3} main_f'(send: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies pSet, contents;
{
    var snapshot: Snapshot;  
    var {:linear} one_s: One ChannelPiece;
    var {:linear} pieces: Set MemIndexPiece;

    assume {:add_to_pool "A", 0, n} true;
    assert sps == AllMemIndexPieces(send);
    // assert channels[tid] == None();
    assume (forall i:int :: 1 <= i && i <= n ==> (snapshot[i]->ts < mem[i]->ts || snapshot[i]== mem[i]));
    // call Set_Put(pSet, sps);
    // call Send(send, snapshot);
    call pieces := Set_Get(pSet, AllMemIndexPieces(send)->val);
    one_s := One(send);
    call Fractions_To_One(one_s, MemIndices(), pieces);
    call Send(one_s, snapshot);

}

async action {:layer 1} {:exit_condition Set_IsSubset(AllMemIndexPieces(s), Set_Add(pSet, perm->val))} read_f(s: ChannelPiece, {:linear_in} perm: One MemIndexPiece)
modifies snapshots, pSet, contents;
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;
    var {:linear} one_s: One ChannelPiece;
    var {:linear} pieces: Set MemIndexPiece;
    assert 1 <= perm->val->id && perm->val->id <= n;
    assume {:add_to_pool "A", 0, n} true;

    if (*) {
        assume {:add_to_pool "K", mem[perm->val->id]->ts, k} {:add_to_pool "V", mem[perm->val->id]->value, v} true;
        assume k < mem[perm->val->id]->ts; 
        snapshots[s->val][perm->val->id]:= StampedValue(k, v);
    } else {
        snapshots[s->val][perm->val->id]:= mem[perm->val->id];
    }
    call One_Put(pSet, perm);

    if (Set_IsSubset(AllMemIndexPieces(s), pSet)) {
        call pieces := Set_Get(pSet, AllMemIndexPieces(s)->val);
        one_s := One(s);
        call Fractions_To_One(one_s, MemIndices(), pieces);
        call Send(one_s, snapshots[s->val]);
    }
}

action {:layer 1} Inv_f(send: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies snapshots, pSet, contents;
creates read_f;
{
    var {:pool "A"} j: int;
    var {:linear} sps': Set MemIndexPiece;
    var {:linear} done_set: Set MemIndexPiece;
    var {:linear} one_s: One ChannelPiece;
    var {:linear} pieces: Set MemIndexPiece;
    var choice: read_f;
    
    assert sps == AllMemIndexPieces(send);
    // assert channels[tid] == None();
    assume {:add_to_pool "A", 0, j+1, n} 0 <= j && j <= n;
    havoc snapshots;
    assume (forall i:int :: 1 <= i && i <= j ==> (snapshots[send->val][i]->ts < mem[i]->ts || snapshots[send->val][i]== mem[i]));

    assume {:add_to_pool "D", Fraction(send, n, MemIndices())} true;

    sps' := sps;
    call done_set := Set_Get(sps', (lambda {:pool "D"} x: MemIndexPiece :: x->val == send && 1 <= x->id && x->id <= j && x->ids ==  MemIndices()));
    call Set_Put(pSet, done_set);

    if (j < n) {
        choice := read_f(send, One(Fraction(send, j+1, MemIndices())));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C" } pa:read_f :: pa->s == send && j+1 <= pa->perm->val->id && pa->perm->val->id <= n && pa->perm->val->val == send && pa->perm->val->ids == MemIndices()));
        call set_choice(choice);
    } else {
        call pieces := Set_Get(pSet, AllMemIndexPieces(send)->val);
        one_s := One(send);
        call Fractions_To_One(one_s, MemIndices(), pieces);
        call Send(one_s, snapshots[send->val]);
    }
}

/////////////////////////////////////////////////////////////////////////////////////////////

async action {:layer 1} action_main_s(send: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
refines {:IS_right} main_s' using Inv_s;
modifies pSet;
creates read_s;
{
    assume {:add_to_pool "A", 0, n} true;
    assert sps == AllMemIndexPieces(send);
    // assert channels[tid] == None();
    call create_asyncs((lambda pa:read_s :: pa->s == send && Set_Contains(sps, pa->perm->val)));
}
yield procedure {:layer 0} main_s(send: ChannelPiece, {:linear_in} sps: Set MemIndexPiece);
refines action_main_s;

async action {:layer 2,3} main_s'(send: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies pSet, contents;
{
    var snapshot: Snapshot;  
    var {:linear} one_s: One ChannelPiece;
    var {:linear} pieces: Set MemIndexPiece;

    assume {:add_to_pool "A", 0, n} true;
    assert sps == AllMemIndexPieces(send);
    // assert channels[tid] == None();
    assume (forall i:int :: 1 <= i && i <= n ==> (snapshot[i]->ts > mem[i]->ts || snapshot[i]== mem[i]));
    // call Set_Put(pSet, sps);
    // call Send(send, snapshot);
    call pieces := Set_Get(pSet, AllMemIndexPieces(send)->val);
    one_s := One(send);
    call Fractions_To_One(one_s, MemIndices(), pieces);
    call Send(one_s, snapshot);

}

async left action {:layer 1} read_s(s: ChannelPiece, {:linear_in} perm: One MemIndexPiece)
modifies snapshots, pSet, contents;
{
    var {:pool "K"} k:int;
    var {:pool "V"} v:Value;
    var {:linear} one_s: One ChannelPiece;
    var {:linear} pieces: Set MemIndexPiece;
    assert 1 <= perm->val->id && perm->val->id <= n;
    assume {:add_to_pool "A", 0, n} true;

    if (*) {
        assume {:add_to_pool "K", mem[perm->val->id]->ts, k} {:add_to_pool "V", mem[perm->val->id]->value, v} true;
        assume k > mem[perm->val->id]->ts; 
        snapshots[s->val][perm->val->id]:= StampedValue(k, v);
    } else {
        snapshots[s->val][perm->val->id]:= mem[perm->val->id];
    }
    call One_Put(pSet, perm);

    if (Set_IsSubset(AllMemIndexPieces(s), pSet)) {
        call pieces := Set_Get(pSet, AllMemIndexPieces(s)->val);
        one_s := One(s);
        call Fractions_To_One(one_s, MemIndices(), pieces);
        call Send(one_s, snapshots[s->val]);
    }
}

action {:layer 1} Inv_s(send: ChannelPiece, {:linear_in} sps: Set MemIndexPiece)
modifies snapshots, pSet, contents;
creates read_s;
{
    var {:pool "A"} j: int;
    var {:linear} sps': Set MemIndexPiece;
    var {:linear} done_set: Set MemIndexPiece;
    var {:linear} one_s: One ChannelPiece;
    var {:linear} pieces: Set MemIndexPiece;
    var choice: read_s;
    
    assert sps == AllMemIndexPieces(send);
    assume {:add_to_pool "A", 0, j+1, n} 0 <= j && j <= n;
    havoc snapshots;
    assume (forall i:int :: 1 <= i && i <= j ==> (snapshots[send->val][i]->ts > mem[i]->ts || snapshots[send->val][i]== mem[i]));

    assume {:add_to_pool "D", Fraction(send, n, MemIndices())} true;
    sps' := sps;
    call done_set := Set_Get(sps', (lambda {:pool "D"} x: MemIndexPiece :: x->val == send && 1 <= x->id && x->id <= j && x->ids ==  MemIndices()));
    call Set_Put(pSet, done_set);

    if (j < n) {
        choice := read_s(send, One(Fraction(send, j+1, MemIndices())));
        assume {:add_to_pool "C", choice} true;
        call create_asyncs((lambda {:pool "C" } pa:read_s :: pa->s == send && j+1 <= pa->perm->val->id && pa->perm->val->id <= n && pa->perm->val->val == send && pa->perm->val->ids == MemIndices()));
        call set_choice(choice);
    } else {
        call pieces := Set_Get(pSet, AllMemIndexPieces(send)->val);
        one_s := One(send);
        call Fractions_To_One(one_s, MemIndices(), pieces);
        call Send(one_s, snapshots[send->val]);
    }
}