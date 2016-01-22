(*------------------------- Sponge Construction ------------------------*)

require import Pair Int IntDiv Real List Option FSet NewFMap DBool.
require import Fun Common.
require (*--*) IRO Block.

(*------------------------- Indifferentiability ------------------------*)

clone include Indifferentiability with
  type p     <- block * capacity,
  type f_in  <- bool list * int,
  type f_out <- bool list

  rename
    [module] "Indif" as "Experiment"
    [module] "GReal"  as "RealIndif"
    [module] "GIdeal"  as "IdealIndif".

(*------------------------- Ideal Functionality ------------------------*)

clone import IRO as BIRO with
  type from <- bool list,
  type to   <- bool,
  op valid  <- valid_toplevel,
  op dto    <- dbool.

(*------------------------- Sponge Construction ------------------------*)

module Sponge (P : DPRIMITIVE) : FUNCTIONALITY, CONSTRUCTION(P) = {
  proc init() : unit = {}

  proc f(bs : bool list, n : int) : bool list = {
    var z        <- [];
    var (sa, sc) <- (b0, Capacity.c0);
    var i        <- 0;
    var xs       <- pad2blocks bs;

    (* absorption *)
    while (xs <> []) {
      (sa, sc) <@ P.f(sa +^ head b0 xs, sc);
      xs        <- behead xs;
    }
    (* squeezing *)
    while (i < (n + r - 1) %/ r) {
      z        <- z ++ w2bits sa;
      (sa, sc) <@ P.f(sa, sc);
      i        <- i + 1;
    }

    return take n z;
  }
}.

(*------------- Simulator and Distinguisher Constructions --------------*)

module LowerFun (F : DFUNCTIONALITY) : Block.DFUNCTIONALITY = {
  proc f(xs : block list, n : int) = {
    var cs, ds : bool list;
    var obs : bool list option;
    var ys : block list <- [];

    obs <- unpad_blocks xs;
    if (obs <> None) {
      cs <@ F.f(oget obs, n * r); (* size cs = n * r *)
      ys <- bits2blocks cs; (* size ys = n *)
    }
    return ys;
  }
}.

module RaiseFun (F : Block.DFUNCTIONALITY) : DFUNCTIONALITY = {
  proc f(bs : bool list, n : int) = {
    var xs;

    xs <@ F.f(pad2blocks bs, (n + r - 1) %/ r);
    return take n (blocks2bits xs);
  }
}.

module LowerDist (D : DISTINGUISHER, F : Block.DFUNCTIONALITY) = D(RaiseFun(F)).

module RaiseSim (S : Block.SIMULATOR, F : DFUNCTIONALITY) = S(LowerFun(F)).

(*------------------------------- Proof --------------------------------*)

section.

declare module BlockSim  : Block.SIMULATOR{IRO, Block.BIRO.IRO}.
declare module Dist : DISTINGUISHER{Perm, BlockSim, IRO, Block.BIRO.IRO}.

module type BLOCK_IRO_BITS = {
  proc init() : unit
  proc g(x : block list, n : int) : bool list
  proc f(x : block list, n : int) : block list
}.

module type BLOCK_IRO_BITS_DIST(BIROB : BLOCK_IRO_BITS) = {
  proc distinguish(): bool 
}.

local module BlockIROBitsEager : BLOCK_IRO_BITS, Block.BIRO.IRO = {
  var mp : (block list * int, bool) fmap

  proc init() : unit = {
    mp <- map0;
  }

  proc fill_in(xs, i) = {
    if (! mem (dom mp) (xs, i)) {
      mp.[(xs, i)] <$ dbool;
    }
    return oget mp.[(xs, i)];
  }

  proc g(xs, n) = {
    var b, bs;
    var m <- ((n + r - 1) %/ r) * r;
    var i <- 0;

    bs <- [];
    if (valid_block xs) {
      while (i < n) {
        b <@ fill_in(xs, i);
        bs <- rcons bs b;
        i <- i + 1;
      }
      while (i < m) {  (* eager part *)
        fill_in(xs, i);
        i <- i + 1;
      }
    }
    return bs;
  }

  proc f(xs, n) = {
    var bs, ys;
    bs <@ g(xs, n * r);
    ys <- bits2blocks bs;
    return ys;
  }
}.

local module BlockIROBitsLazy : BLOCK_IRO_BITS, Block.BIRO.IRO = {
  var mp : (block list * int, bool) fmap

  proc init() : unit = {
    mp <- map0;
  }

  proc fill_in(xs, i) = {
    if (! mem (dom mp) (xs, i)) {
      mp.[(xs, i)] <$ dbool;
    }
    return oget mp.[(xs, i)];
  }

  proc g(xs, n) = {
    var b, bs;
    var i <- 0;

    bs <- [];
    if (valid_block xs) {
      while (i < n) {
        b <@ fill_in(xs, i);
        bs <- rcons bs b;
        i <- i + 1;
      }
    }
    return bs;
  }

  proc f(xs, n) = {
    var bs, ys;
    bs <@ g(xs, n * r);
    ys <- bits2blocks bs;
    return ys;
  }
}.

local module RaiseBIROBLazy (F : BLOCK_IRO_BITS) : FUNCTIONALITY = {
  proc init() = {
    F.init();
  }

  proc f(bs : bool list, n : int) = {
    var cs;

    cs <@ F.g(pad2blocks bs, n);
    return take n cs;
  }
}.

pred LazyInvar
     (mp1 : (bool list * int, bool) fmap,
      mp2 : (block list * int, bool) fmap) =
  (forall (bs : bool list, n : int),
   mem (dom mp1) (bs, n) <=> mem (dom mp2) (pad2blocks bs, n)) /\
  (forall (xs : block list, n),
   mem (dom mp2) (xs, n) => valid_block xs) /\
  (forall (bs : bool list, n : int),
   mem (dom mp1) (bs, n) =>
   oget mp1.[(bs, n)] = oget mp2.[(pad2blocks bs, n)]).

local lemma LowerFun_IRO_BlockIROBitsLazy_f :
  equiv[LowerFun(IRO).f ~ BlockIROBitsLazy.f :
        ={xs, n} /\ LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2} ==>
        ={res} /\ LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2}].
proof.
proc=> /=; inline BlockIROBitsLazy.g.
seq 0 1 :
  (={n} /\ xs{1} = xs0{2} /\
   LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2}); first auto.
case (valid_block xs{1}).
rcondt{1} 3; first auto. rcondt{2} 4; first auto.
inline *. rcondt{1} 7; first auto.
seq 6 3 : 
  (={n, n0} /\ xs{1} = xs0{2} /\ n0{1} = n{1} * r /\
   LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2} /\
   valid_block xs{1} /\ pad2blocks x{1} = xs0{2}).
auto; progress; have {2}<- /# := unpadBlocksK xs0{2}.
admit.
rcondf{1} 3; first auto. rcondf{2} 4; first auto.
auto; progress; by rewrite bits2blocks_nil.
qed.

(* TODO:
 
 IRO.f ~ RaiseBIROBLazy(BlockIROBitsLazy).f *)

(* TODO:
BlockIROBitsEager.f ~ Block.BIRO.IRO.f

BlockIROBitsEager.fi ~ Block.BIRO.IRO.fi

RaiseFun(BlockIROBitsEager).f ~ RaiseFun(Block.BIRO.IRO).f
*)

local lemma BlockIROBitsEager (D <: BLOCK_IRO_BITS_DIST) :
  equiv[D(BlockIROBitsEager).distinguish ~ D(BlockIROBitsLazy).distinguish : 
        ={glob D} /\ BlockIROBitsEager.mp{1} = BlockIROBitsLazy.mp{2} ==>
        ={glob D}].
proof.
admit.
qed.

pred BlockIROBits_Eager_Invar
     (mp1 : (block list * int, block) fmap,
      mp2 : (block list * int, bool) fmap) =
  (forall (xs : block list, i : int),
   mem (dom mp1) (xs, i) =>
   0 <= i /\
   (forall (j : int), 0 <= j < i => mem (dom mp1) (xs, j)) /\
   (forall (j : int), i * r <= j < (i + 1) * r =>
    mp2.[(xs, j)] = Some(nth false (w2bits(oget mp1.[(xs, i)])) j))) /\
  (forall (xs : block list, j : int),
   mem (dom mp2) (xs, j) =>
   0 <= j /\ mem (dom mp1) (xs, j %/ r)).

local lemma Sponge_Raise_Block_Sponge_f :
  equiv[Sponge(Perm).f ~ RaiseFun(Block.Sponge(Perm)).f :
        ={bs, n, glob Perm} ==> ={res, glob Perm}].
proof.
proc; inline Block.Sponge(Perm).f.
conseq (_ : ={bs, n, glob Perm} ==> _)=> //.
swap{2} [3..5] -2.
seq 4 4 :
  (={n, glob Perm, sa, sc, i} /\ xs{1} = xs0{2} /\ z{1} = [] /\ z{2} = [] /\
   valid_block xs0{2}).
auto; progress; apply valid_pad2blocks.
rcondt{2} 2; auto.
swap{2} 1 1.
seq 1 1 : 
  (={n, glob Perm, sa, sc, i} /\ xs{1} = xs0{2} /\ z{1} = [] /\ z{2} = []).
while (={glob Perm, sa, sc, i} /\ xs{1} = xs0{2} /\ z{1} = [] /\ z{2} = []).
wp. call (_ : ={glob Perm}). sim. auto. auto.
seq 0 1 : 
  (={n, glob Perm, sa, sc, i} /\ blocks2bits z{2} = z{1} /\
   n0{2} = (n{1} + r - 1) %/ r); first auto.
while (={n, glob Perm, i, sa, sc} /\ blocks2bits z{2} = z{1} /\
       n0{2} = (n{1} + r - 1) %/ r).
wp. call (_ : ={glob Perm}); first sim. auto.
auto; progress; by rewrite -cats1 blocks2bits_cat blocks2bits_sing.
auto.
qed.

local lemma RealIndif &m :
  Pr[RealIndif(Sponge, Perm, Dist).main() @ &m: res] =
  Pr[Block.RealIndif
     (Block.Sponge, Perm, LowerDist(Dist)).main() @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 : (={glob Dist, glob Perm}); first sim.
call (_ : ={glob Perm}); first 2 sim.
conseq Sponge_Raise_Block_Sponge_f=> //.
auto.
qed.

local lemma IdealIndifIROLazy &m :
  Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res] =
  Pr[Experiment
     (RaiseBIROBLazy(BlockIROBitsLazy), BlockSim(BlockIROBitsLazy),
      Dist).main() @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 :
  (={glob Dist, glob BlockSim} /\ IRO.mp{1} = NewFMap.map0 /\
   BlockIROBitsLazy.mp{2} = NewFMap.map0).
inline *; wp; call (_ : true); auto.
call
  (_ :
  ={glob Dist, glob BlockSim} /\
  IRO.mp{1} = map0 /\ BlockIROBitsLazy.mp{2} = map0 ==>
  ={res}).
proc (={glob BlockSim}).
smt.
smt.
admit.
admit.
admit.
auto.
qed.

local lemma IdealIndifLazy &m :
  Pr[Experiment
     (RaiseBIROBLazy(BlockIROBitsLazy), BlockSim(BlockIROBitsLazy),
      Dist).main() @ &m : res] =
  Pr[Block.IdealIndif
     (BlockIROBitsEager, BlockSim, LowerDist(Dist)).main() @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 :
  (={glob Dist, glob BlockSim} /\ BlockIROBitsLazy.mp{1} = NewFMap.map0 /\
   BlockIROBitsEager.mp{2} = NewFMap.map0).
inline *; wp; call (_ : true); auto.
(* reduction to BlockIROBitsEager *)
admit.
qed.

local lemma IdealIndifEager &m :
  Pr[Block.IdealIndif
     (BlockIROBitsEager, BlockSim, LowerDist(Dist)).main() @ &m : res] =
  Pr[Block.IdealIndif
     (Block.BIRO.IRO, BlockSim, LowerDist(Dist)).main () @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 :
  (={glob Dist, glob BlockSim} /\ BlockIROBitsEager.mp{1} = NewFMap.map0 /\
   Block.BIRO.IRO.mp{2} = NewFMap.map0).
inline *; wp; call (_ : true); auto.
call
  (_ :
  ={glob Dist, glob BlockSim} /\
  BlockIROBitsEager.mp{1} = map0 /\ Block.BIRO.IRO.mp{2} = map0 ==>
  ={res}).
proc (={glob BlockSim}).
smt.
smt.
proc (true); first 2 smt.
admit.
admit.
admit.
auto.
qed.

local lemma IdealIndif &m :
  Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res] =
  Pr[Block.IdealIndif
     (Block.BIRO.IRO, BlockSim, LowerDist(Dist)).main () @ &m : res].
proof.
by rewrite (IdealIndifIROLazy &m) (IdealIndifLazy &m) (IdealIndifEager &m).
qed.

lemma Conclusion' &m :
  `|Pr[RealIndif(Sponge, Perm, Dist).main() @ &m: res] -
    Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res]| =
  `|Pr[Block.RealIndif
       (Block.Sponge, Perm, LowerDist(Dist)).main() @ &m : res] -
    Pr[Block.IdealIndif
       (Block.BIRO.IRO, BlockSim, LowerDist(Dist)).main() @ &m : res]|.
proof.
by rewrite (RealIndif &m) (IdealIndif &m).
qed.

end section.

(*----------------------------- Conclusion -----------------------------*)

lemma Conclusion (BlockSim <: Block.SIMULATOR{IRO, Block.BIRO.IRO})
                 (Dist <: DISTINGUISHER{Perm, BlockSim, IRO, Block.BIRO.IRO})
                 &m :
  `|Pr[RealIndif(Sponge, Perm, Dist).main() @ &m: res] -
    Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res]| =
  `|Pr[Block.RealIndif
       (Block.Sponge, Perm, LowerDist(Dist)).main() @ &m : res] -
    Pr[Block.IdealIndif
       (Block.BIRO.IRO, BlockSim, LowerDist(Dist)).main() @ &m : res]|.
proof. by apply/(Conclusion' BlockSim Dist &m). qed.
