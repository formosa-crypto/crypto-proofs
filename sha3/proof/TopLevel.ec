(*------------------------- Sponge Construction ------------------------*)

require import Pair Int IntDiv Real List Option NewFMap.
require import Common.
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
  op valid  <- valid_toplevel.

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
  proc init() = {}

  proc f(xs : block list, n : int) = {
    var cs, ds : bool list;
    var obs : bool list option;
    var ys : block list <- [];

    obs <- unpad_blocks xs;
    if (obs <> None) {
      cs <@ F.f(oget obs, n * r); (* size cs = n * r *)
      ys <- bits2blocks cs;
    }
    return ys;
  }
}.

module RaiseFun (F : Block.DFUNCTIONALITY) : DFUNCTIONALITY = {
  proc init() = {}

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

lemma Sponge_Raise_Block_Sponge_f :
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

lemma RealIndif &m :
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

lemma IdealDist &1 &2 (a : bool) :
  (glob Dist){1} = (glob Dist){2} => (glob BlockSim){1} = (glob BlockSim){2} =>
  IRO.mp{1} = NewFMap.map0 => Block.BIRO.IRO.mp{2} = NewFMap.map0 =>
  Pr[Dist(IRO, BlockSim(LowerFun(IRO))).distinguish() @ &1 : a = res] =
  Pr[Dist(RaiseFun(Block.BIRO.IRO),
          BlockSim(Block.BIRO.IRO)).distinguish() @ &2 : a = res].
proof.
admit.
qed.

lemma IdealIndif &m :
  Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res] =
  Pr[Block.IdealIndif
     (Block.BIRO.IRO, BlockSim, LowerDist(Dist)).main () @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 :
  (={glob Dist, glob BlockSim} /\ IRO.mp{1} = NewFMap.map0 /\
   Block.BIRO.IRO.mp{2} = NewFMap.map0).
inline *; wp; call (_ : true); auto.
call
  (_ :
  ={glob Dist, glob BlockSim} /\
  IRO.mp{1} = map0 /\ Block.BIRO.IRO.mp{2} = map0 ==>
  ={res}).
bypr res{1} res{2}=> //; progress.
apply (IdealDist &1 &2 a)=> //.
auto.
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
