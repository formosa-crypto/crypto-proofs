(* Top Level *)

require import AllCore List IntDiv StdOrder Common Sponge. import BIRO.
require SLCommon BlockSponge.

(* FIX: would be nicer to define limit at top-level and then clone
   BlockSponge with it - so BlockSponge would then clone lower-level
   theories with it

op limit : {int | 0 < limit} as gt0_max_limit.
*)

op limit : int = SLCommon.max_size.

(* FIX: don't want this in bound *)

op dstate : (block * capacity) distr = SLCommon.dstate.

(*---------------------------- Restrictions ----------------------------*)

(** The counter for the functionality counts the number of times the
    underlying primitive is called inside the functionality. This
    number is equal to the sum of the number of blocks in the padding
    of the input, plus the number of additional blocks the squeezing
    phase has to output.
  *)

module Cntr = {
  var c : int

  proc init() = {
    c <- 0;
  }
}.

module FC (F : DFUNCTIONALITY) = {
  proc init () : unit = {}

  (* ((size bs + 1) %/ r + 1) = size (pad2blocks bs): *)

  proc f (bs : bool list, n : int) : bool list = {
    var z : bool list <- [];
    if (Cntr.c +
        ((size bs + 1) %/ r + 1) +
        (max ((n + r - 1) %/ r - 1) 0) <= limit) {
      Cntr.c <-
        Cntr.c +
        ((size bs + 1) %/ r + 1) +
        (max ((n + r - 1) %/ r - 1) 0);
      z <@ F.f(bs, n);
    }
    return z;
  }
}.

module PC (P : DPRIMITIVE) = {
  proc init() = {}

  proc f (a : block * capacity) = {
    var z : block * capacity <- (b0, c0);
    if (Cntr.c + 1 <= limit) {
      z <@ P.f(a);
      Cntr.c <- Cntr.c + 1;
    }
    return z;
  }
  proc fi (a : block * capacity) = {
    var z : block * capacity <- (b0, c0);
    if (Cntr.c + 1 <= limit) {
      z <@ P.fi(a);
      Cntr.c <- Cntr.c + 1;
    }
    return z;
  }
}.

module DRestr (D : DISTINGUISHER) (F : DFUNCTIONALITY) (P : DPRIMITIVE) = {
  proc distinguish () : bool = {
    var b : bool;
    Cntr.init();
    b <@ D(FC(F),PC(P)).distinguish();
    return b;
  }
}.

section.

declare module Dist :
  DISTINGUISHER{Perm, BlockSponge.Sim, IRO, Cntr, BlockSponge.BIRO.IRO,
                BlockSponge.C}.

lemma drestr_commute1 &m :
  Pr[BlockSponge.RealIndif
     (BlockSponge.Sponge, Perm,
      LowerDist(DRestr(Dist))).main() @ &m : res] =
  Pr[BlockSponge.RealIndif
     (BlockSponge.Sponge, Perm,
      BlockSponge.DRestr(LowerDist(Dist))).main() @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 : (={glob Dist} /\ ={Perm.m, Perm.mi} ); first sim.
inline*; wp; sp.
call (_ : ={c}(Cntr, BlockSponge.C) /\ ={Perm.m, Perm.mi}).
proc; sp; if=> //; sp; sim.
proc; sp; if=> //; sp; sim.
proc=> /=.
inline BlockSponge.FC(BlockSponge.Sponge(Perm)).f.
wp; sp.
if=> //.
progress; smt(size_pad2blocks).
seq 1 1 :
  (={n} /\ nb{2} = (n{2} + r - 1) %/ r /\ bl{2} = pad2blocks bs{1} /\
   Cntr.c{1} = BlockSponge.C.c{2} /\ ={Perm.m, Perm.mi}).
auto; progress; by rewrite size_pad2blocks.
inline RaiseFun(BlockSponge.Sponge(Perm)).f.
wp; sp.
call (_ : ={Perm.m, Perm.mi}); first sim.
auto.
auto; progress; by rewrite blocks2bits_nil.
auto.
qed.

lemma drestr_commute2 &m :
  Pr[BlockSponge.IdealIndif
     (BlockSponge.BIRO.IRO, BlockSponge.Sim,
      LowerDist(DRestr(Dist))).main() @ &m : res] =
  Pr[BlockSponge.IdealIndif
     (BlockSponge.BIRO.IRO, BlockSponge.Sim,
      BlockSponge.DRestr(LowerDist(Dist))).main() @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 :
  (={glob Dist, BlockSponge.BIRO.IRO.mp,
     glob BlockSponge.Sim}); first sim.
inline*; wp; sp.
call
  (_ :
   ={c}(Cntr, BlockSponge.C) /\ ={BlockSponge.BIRO.IRO.mp} /\
   ={glob BlockSponge.Sim}).
proc; sp; if=> //; sim.
proc; sp; if=> //; sim.
proc=> /=.
inline BlockSponge.FC(BlockSponge.BIRO.IRO).f.
sp; wp.
if=> //.
progress; smt(size_pad2blocks).
seq 1 1 :
  (={n} /\ nb{2} = (n{2} + r - 1) %/ r /\ bl{2} = pad2blocks bs{1} /\
   Cntr.c{1} = BlockSponge.C.c{2} /\
   ={BlockSponge.BIRO.IRO.mp, Gconcl.S.paths, Gconcl.S.mi, Gconcl.S.m}).
auto; progress.
rewrite size_pad2blocks //.
inline RaiseFun(BlockSponge.BIRO.IRO).f.
wp; sp.
call (_ : ={BlockSponge.BIRO.IRO.mp}); first sim.
auto.
auto; progress; by rewrite blocks2bits_nil.
auto.
qed.

lemma security &m :
  `|Pr[RealIndif(Sponge, Perm, DRestr(Dist)).main() @ &m : res] -
    Pr[IdealIndif
       (IRO, RaiseSim(BlockSponge.Sim),
        DRestr(Dist)).main() @ &m : res]| <=
  (limit ^ 2)%r / 2%r * Distr.mu1 dstate witness +
  limit%r * ((2 * limit)%r / (2 ^ c)%r) +
  limit%r * ((2 * limit)%r / (2 ^ c)%r).
proof.
rewrite
  (RealOrder.ler_trans
   (`|Pr[BlockSponge.RealIndif
         (BlockSponge.Sponge, Perm, LowerDist(DRestr(Dist))).main() @ &m : res] -
      Pr[BlockSponge.IdealIndif
         (BlockSponge.BIRO.IRO, BlockSponge.Sim,
          LowerDist(DRestr(Dist))).main() @ &m : res]|))
  1:RealOrder.lerr_eq
  1:(conclusion BlockSponge.Sim (DRestr(Dist)) &m) //
  (drestr_commute1 &m) (drestr_commute2 &m)
  (BlockSponge.conclusion (LowerDist(Dist)) &m).
qed.

end section.

lemma SHA3Security
      (Dist <:
       DISTINGUISHER{Perm, IRO, BlockSponge.BIRO.IRO, Cntr,
                     BlockSponge.Sim, BlockSponge.C}) &m :
  `|Pr[RealIndif(Sponge, Perm, DRestr(Dist)).main() @ &m : res] -
    Pr[IdealIndif
       (IRO, RaiseSim(BlockSponge.Sim), DRestr(Dist)).main() @ &m : res]| <=
    (limit ^ 2)%r / 2%r * (Distr.mu1 dstate witness)%Distr +
    limit%r * ((2 * limit)%r / (2 ^ c)%r) +
    limit%r * ((2 * limit)%r / (2 ^ c)%r).
proof. apply (security Dist &m). qed.
