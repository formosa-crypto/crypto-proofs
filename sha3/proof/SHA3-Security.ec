(* Top-level Proof of SHA-3 Security *)

require import AllCore List IntDiv StdOrder Distr.

require import Common Sponge. import BIRO.

require SLCommon Gconcl_list.

(* FIX: would be nicer to define limit at top-level and then clone
   BlockSponge with it - so BlockSponge would then clone lower-level
   theories with it

op limit : {int | 0 < limit} as gt0_max_limit.
*)

op limit : int = SLCommon.max_size.

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
  DISTINGUISHER{Perm, Gconcl_list.SimLast, IRO, Cntr, BlockSponge.BIRO.IRO,
                BlockSponge.C, Gconcl.S,
                SLCommon.F.RO, SLCommon.F.RRO, SLCommon.Redo, SLCommon.C,
                Gconcl_list.BIRO2.IRO, Gconcl_list.F2.RO, Gconcl_list.F2.RRO}.

axiom Dist_lossless (F <: DFUNCTIONALITY) (P <: DPRIMITIVE) :
  islossless P.f => islossless P.fi => islossless F.f =>
  islossless Dist(F,P).distinguish.

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
     (BlockSponge.BIRO.IRO, Gconcl_list.SimLast(Gconcl.S),
      LowerDist(DRestr(Dist))).main() @ &m : res] =
  Pr[BlockSponge.IdealIndif
     (BlockSponge.BIRO.IRO, Gconcl_list.SimLast(Gconcl.S),
      BlockSponge.DRestr(LowerDist(Dist))).main() @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 :
  (={glob Dist, BlockSponge.BIRO.IRO.mp,
     glob Gconcl_list.SimLast(Gconcl.S)}); first sim.
inline*; wp; sp.
call
  (_ :  ={BlockSponge.BIRO.IRO.mp,Gconcl_list.BIRO2.IRO.mp} /\
   ={c}(Cntr, BlockSponge.C) /\
   ={glob Gconcl_list.SimLast(Gconcl.S)}).
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
   ={BlockSponge.BIRO.IRO.mp, Gconcl_list.BIRO2.IRO.mp,
     Gconcl.S.paths, Gconcl.S.mi, Gconcl.S.m}).
auto; progress.
rewrite size_pad2blocks //.
inline RaiseFun(BlockSponge.BIRO.IRO).f.
wp; sp.
call (_ : ={BlockSponge.BIRO.IRO.mp}); first sim.
auto.
auto; progress. by rewrite blocks2bits_nil.
auto.
qed.

op wit_pair : block * capacity = witness.

lemma security &m :
  `|Pr[RealIndif(Sponge, Perm, DRestr(Dist)).main() @ &m : res] -
    Pr[IdealIndif
       (IRO, RaiseSim(Gconcl_list.SimLast(Gconcl.S)),
        DRestr(Dist)).main() @ &m : res]| <=
  (limit ^ 2)%r / (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r.
proof.
rewrite powS 1:addz_ge0 1:ge0_r 1:ge0_c -pow_add 1:ge0_r 1:ge0_c.
have -> :
  (limit ^ 2)%r / (2 * (2 ^ r * 2 ^ c))%r =
  ((limit ^ 2)%r / 2%r) * (1%r / (2 ^ r)%r) * (1%r / (2 ^ c)%r).
  rewrite (fromintM 2) StdRing.RField.invfM StdRing.RField.mulrA
           -!StdRing.RField.mulrA.
  congr.
  rewrite (fromintM (2 ^ r)) StdRing.RField.invfM StdRing.RField.mulrA
          -!StdRing.RField.mulrA.
  congr; by rewrite StdRing.RField.mul1r.
rewrite/=.
have -> :
  (4 * limit ^ 2)%r / (2 ^ c)%r =
  limit%r * ((2 * limit)%r / (2 ^ c)%r) + limit%r * ((2 * limit)%r / (2 ^ c)%r).
  have -> : 4 = 2 * 2 by trivial.
  have {3}-> : 2 = 1 + 1 by trivial.
  rewrite powS // pow1 /#.
rewrite -/SLCommon.dstate /limit.
cut->:=conclusion (Gconcl_list.SimLast(Gconcl.S)) (DRestr(Dist)) &m.
cut//=:=(Gconcl_list.Real_Ideal (LowerDist(Dist))  _ &m).
+ move=>F P hp hpi hf'//=.
  cut hf:islossless RaiseFun(F).f.
  - proc;call hf';auto.
  exact(Dist_lossless (RaiseFun(F)) P hp hpi hf).
by rewrite(drestr_commute1 &m) (drestr_commute2 &m);smt().
qed.

end section.

lemma SHA3Security
      (Dist <: DISTINGUISHER{
                 Perm, IRO, BlockSponge.BIRO.IRO, Cntr, 
                 Gconcl_list.SimLast(Gconcl.S), BlockSponge.C, Gconcl.S,
                 SLCommon.F.RO, SLCommon.F.RRO, SLCommon.Redo, SLCommon.C,
                 Gconcl_list.BIRO2.IRO, Gconcl_list.F2.RO, Gconcl_list.F2.RRO})
        &m :
      (forall (F <: DFUNCTIONALITY) (P <: DPRIMITIVE),
        islossless P.f => 
        islossless P.fi => 
        islossless F.f =>
        islossless Dist(F,P).distinguish) =>
  `|Pr[RealIndif(Sponge, Perm, DRestr(Dist)).main() @ &m : res] -
    Pr[IdealIndif
       (IRO, RaiseSim(Gconcl_list.SimLast(Gconcl.S)), DRestr(Dist)).main() @ &m : res]| <=
  (limit ^ 2)%r / (2 ^ (r + c + 1))%r + (4 * limit ^ 2)%r / (2 ^ c)%r.
proof. move=>h;apply (security Dist h &m). qed.
