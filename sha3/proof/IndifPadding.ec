require import Real NewFMap Fun.
require (*..*) Indifferentiability LazyRO.

clone import Indifferentiability as Ind1.

clone import Indifferentiability as Ind2
  with type p_in  <- Ind1.p_in,
       type p_out <- Ind1.p_out,
       type f_out <- Ind1.f_out.

op pad : Ind2.f_in -> Ind1.f_in.
op padinv : Ind1.f_in -> Ind2.f_in.
axiom cancel_pad    : cancel pad padinv.
axiom cancel_padinv : cancel padinv pad.

clone import LazyRO as RO1 
  with type from <- Ind1.f_in,
       type to   <- Ind1.f_out.

clone import LazyRO as RO2 
  with type from <- Ind2.f_in,
       type to   <- Ind1.f_out,
       op d      <- RO1.d.

module HF1 = {
  proc init = RO1.H.init
  proc oracle = RO1.H.f
}.

module HF2 = {
  proc init = RO2.H.init
  proc oracle = RO2.H.f
}.

module ConstrPad (FC:Ind1.Construction, P:Ind1.Primitive) = {
  module C = FC(P)

  proc init = C.init

  proc oracle (x:Ind2.f_in) : f_out = {
    var r;
    r = C.oracle(pad x);
    return r;
  }
}.

module DistPad(FD: Ind2.Distinguisher, F:Ind1.Functionality, P:Ind1.Primitive) = {
  module Fpad = {
    proc init = F.init

    proc oracle(x:Ind2.f_in) : f_out = {
      var r;
      r = F.oracle(pad x);
      return r;
    }
  }
    
  module Dpad = FD(Fpad, P)

  proc distinguish = Dpad.distinguish
}.

module SimPadinv(S:Ind1.Simulator, F2:Ind2.Functionality) = {
  module F1 = {
    proc init = F2.init
    proc oracle(x:Ind1.f_in):Ind1.f_out = {
      var r;
      r = F2.oracle(padinv x);
      return r;
    }
  }

  module S2 = S(F1)

  proc init = S2.init

  proc oracle = S2.oracle
  }.

section Reduction.

  declare module P  : Ind1.Primitive. (* It is compatible with Ind2.Primitive *)  
  declare module C  : Ind1.Construction {P}.
  declare module S  : Ind1.Simulator{ RO1.H, RO2.H}.

  declare module D' : Ind2.Distinguisher{P,C, RO1.H, RO2.H, S}.

  equiv ConstrDistPad: 
      Ind2.Indif(ConstrPad(C,P), P, D').main ~ 
      Ind1.Indif(C(P), P, DistPad(D')).main : ={glob P, glob C, glob D'} ==> 
                                              ={glob P, glob C, glob D', res}.
  proof. by proc;sim. qed.

  lemma PrConstrDistPad &m: 
      Pr[ Ind2.Indif(ConstrPad(C,P), P, D').main() @ &m : res] =
      Pr[ Ind1.Indif(C(P), P, DistPad(D')).main() @ &m : res].
  proof. by byequiv ConstrDistPad. qed.
  
  equiv DistH2H1:
      Ind2.Indif(HF2,SimPadinv(S,HF2),D').main ~
      Ind1.Indif(HF1,S(HF1), DistPad(D')).main : 
        ={glob D', glob S} ==> 
        ={glob D',glob S, res} /\ forall x, RO2.H.m{1}.[padinv x] = RO1.H.m{2}.[x].
  proof.
    proc.  
    call (_: ={glob S} /\ forall x, RO2.H.m{1}.[padinv x] = RO1.H.m{2}.[x]).
    + proc *;inline *.
      call (_: forall x, RO2.H.m{1}.[padinv x] = RO1.H.m{2}.[x]);auto.
      proc;inline *;wp;sp;if;first by progress [-split];rewrite !in_dom H.
      + auto;progress;first by rewrite !getP_eq.
        by rewrite !getP (can_eq _ _ cancel_padinv) H.
      by auto;progress;rewrite H.      
    + proc;inline *;wp;sp;if;first by progress[-split];rewrite -{1}(cancel_pad x{2}) !in_dom H.
      + auto;progress;first by rewrite !getP_eq.  
        by rewrite !getP (eq_sym x1) (can2_eq _ _ cancel_pad cancel_padinv) (eq_sym x{2}) H.
      by auto;progress;rewrite -H cancel_pad.
    inline *;wp. call (_: ={glob D'});first by sim.
    auto;progress;by rewrite !map0P.
  qed.

  lemma PrDistH2H1 &m:  
      Pr[Ind2.Indif(HF2,SimPadinv(S,HF2),D').main() @ &m : res] =
      Pr[Ind1.Indif(HF1,S(HF1), DistPad(D')).main() @ &m : res].
  proof. by byequiv DistH2H1. qed.

  lemma Conclusion &m:
      `| Pr[ Ind2.Indif(ConstrPad(C,P), P, D').main() @ &m : res] -
         Pr[Ind2.Indif(HF2,SimPadinv(S,HF2),D').main() @ &m : res] | =
      `| Pr[ Ind1.Indif(C(P), P, DistPad(D')).main() @ &m : res] - 
         Pr[Ind1.Indif(HF1,S(HF1), DistPad(D')).main() @ &m : res] |.
  proof. by rewrite (PrConstrDistPad &m) (PrDistH2H1 &m). qed.

end section Reduction.

