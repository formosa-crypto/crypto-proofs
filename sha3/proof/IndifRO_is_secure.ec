require import AllCore Distr SmtMap.
require (****) SecureRO Indifferentiability.


type block.
type f_in.
type f_out.

op    sampleto      : f_out distr.
axiom sampleto_ll   : is_lossless sampleto.
axiom sampleto_fu   : is_funiform sampleto.
axiom sampleto_full : is_full sampleto.

op    limit     : int.
axiom limit_gt0 : 0 < limit.

op bound : real.


op    bound_counter     : int.
axiom bound_counter_ge0 : 0 <= bound_counter.

op    increase_counter          : int -> f_in -> int.
axiom increase_counter_spec c m : c <= increase_counter c m.


clone import SecureRO as SRO with
  type from <- f_in,
  type to   <- f_out,

  op bound <- limit,
  op sampleto <- sampleto,
  op increase_counter <- increase_counter,
  op bound_counter <- bound_counter

  proof * by smt(sampleto_fu sampleto_ll sampleto_full limit_gt0 
    increase_counter_spec bound_counter_ge0).


clone import Indifferentiability as Indiff0 with
  type p    <- block,
  type f_in <- f_in,
  type f_out <- f_out.

module RO : FUNCTIONALITY = {
  proc init = SRO.RO.RO.init
  proc f = SRO.RO.RO.get
}.

module FInit (F : DFUNCTIONALITY) = {
  proc init () = {}
  proc get     = F.f
  proc f       = F.f
  proc set (a : f_in, b: f_out) = {}
  proc sample (a: f_in) = {}
  proc rem (a : f_in) = {}
}.

module GetF (F : SRO.RO.RO) = {
  proc init = F.init
  proc f = F.get
}.

module SInit (F : SRO.RO.RO) (S : SIMULATOR) = {
  proc init() = {
    S(GetF(F)).init();
    F.init();
  }
  proc get = F.get
  proc set = F.set
  proc rem = F.rem
  proc sample = F.sample
}.

module FM (C : CONSTRUCTION) (P : PRIMITIVE) = {
  proc init () = {
    P.init();
    C(P).init();
  }
  proc get     = C(P).f
  proc f       = C(P).f
  proc set (a : f_in, b: f_out) = {}
  proc sample (a: f_in) = {}
  proc rem (a : f_in) = {}
}.

module D (A : AdvCollision) (F : DFUNCTIONALITY) (P : DPRIMITIVE) = {
  proc distinguish = Collision(A,FInit(F)).main
}.

section Proof.

  declare module A : AdvCollision{Bounder, SRO.RO.RO, SRO.RO.FRO}.
  
  axiom D_ll (F <: Oracle) :
    islossless F.get => islossless A(F).guess.

  lemma coll_resistant_if_indifferentiable
      (C <: CONSTRUCTION{A, Bounder})
      (P <: PRIMITIVE{C, A, Bounder}) &m :
      (exists (S <: SIMULATOR{Bounder, A}),
        (forall (F <: FUNCTIONALITY), islossless F.f => islossless S(F).init) /\
        `|Pr[GReal(C,P,D(A)).main() @ &m : res] - 
          Pr[GIdeal(RO,S,D(A)).main() @ &m : res]| <= bound) =>
      Pr[Collision(A,FM(C,P)).main() @ &m : res] <= 
        bound + ((limit * (limit - 1) + 2)%r / 2%r * mu1 sampleto witness).
  proof.
  move=>[] S [] S_ll Hbound.
  cut->: Pr[Collision(A, FM(C,P)).main() @ &m : res] = 
         Pr[GReal(C, P, D(A)).main() @ &m : res].
  + byequiv=>//=; proc; inline*; wp; sim.
    by swap{1} [1..2] 2; sim.
  cut/#:Pr[GIdeal(RO, S, D(A)).main() @ &m : res] <= 
         (limit * (limit - 1) + 2)%r / 2%r * mu1 sampleto witness.
  cut->:Pr[GIdeal(RO, S, D(A)).main() @ &m : res] =
        Pr[Collision(A, SRO.RO.RO).main() @ &m : res].
  + byequiv=>//=; proc; inline D(A, RO, S(RO)).distinguish; wp; sim.
    inline*; swap{2} 1 1; wp. 
    call{1} (S_ll RO); auto.
    by proc; auto; smt(sampleto_ll).
  exact(RO_is_collision_resistant A &m).
  qed.

end section Proof.