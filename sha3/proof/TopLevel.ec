(*------------------------- Sponge Construction ------------------------*)

require import Pair Int IntDiv Real List Option.
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

declare module BlockSim  : Block.SIMULATOR.
declare module Dist : DISTINGUISHER.

lemma Conclusion' &m :
  `|Pr[RealIndif(Sponge, Perm, Dist).main() @ &m: res] -
    Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res]| =
  `|Pr[Block.RealIndif
       (Block.Sponge, Perm, LowerDist(Dist)).main() @ &m : res] -
    Pr[Block.IdealIndif
       (Block.BIRO.IRO, BlockSim, LowerDist(Dist)).main() @ &m : res]|.
proof. admit. qed.

end section.

(*----------------------------- Conclusion -----------------------------*)

lemma Conclusion (BlockSim <: Block.SIMULATOR)
                 (Dist <: DISTINGUISHER)
                 &m :
  `|Pr[RealIndif(Sponge, Perm, Dist).main() @ &m: res] -
    Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res]| =
  `|Pr[Block.RealIndif
       (Block.Sponge, Perm, LowerDist(Dist)).main() @ &m : res] -
    Pr[Block.IdealIndif
       (Block.BIRO.IRO, BlockSim, LowerDist(Dist)).main() @ &m : res]|.
proof. by apply (Conclusion' BlockSim Dist &m). qed.
