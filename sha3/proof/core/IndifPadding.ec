require import Fun Pair Real NewFMap.
require (*..*) Indifferentiability LazyRO.

clone import Indifferentiability as Ind1.

clone import Indifferentiability as Ind2
  with type p  <- Ind1.p,
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

module ConstrPad (FC:Ind1.CONSTRUCTION, P:Ind1.PRIMITIVE) = {
  module C = FC(P)

  proc init = C.init

  proc f (x:Ind2.f_in) : f_out = {
    var r;
    r = C.f(pad x);
    return r;
  }
}.

module DistPad(FD: Ind2.DISTINGUISHER, F:Ind1.FUNCTIONALITY, P:Ind1.PRIMITIVE) = {
  module Fpad = {
    proc init = F.init

    proc f(x:Ind2.f_in) : f_out = {
      var r;
      r = F.f(pad x);
      return r;
    }
  }

  proc distinguish = FD(Fpad,P).distinguish
}.

module SimPadinv(S:Ind1.SIMULATOR, F2:Ind2.FUNCTIONALITY) = {
  module F1 = {
    proc init = F2.init
    proc f(x:Ind1.f_in):Ind1.f_out = {
      var r;
      r = F2.f(padinv x);
      return r;
    }
  }

  module S2 = S(F1)

  proc init = S2.init

  proc f = S2.f
  proc fi = S2.fi
}.

section Reduction.
  declare module P  : Ind1.PRIMITIVE. (* It is compatible with Ind2.Primitive *)  
  declare module C  : Ind1.CONSTRUCTION {P}.
  declare module S  : Ind1.SIMULATOR{ RO1.H, RO2.H}.

  declare module D' : Ind2.DISTINGUISHER{P,C, RO1.H, RO2.H, S}.

  local equiv ConstrDistPad: 
      Ind2.GReal(ConstrPad(C), P, D').main ~ 
      Ind1.GReal(C, P, DistPad(D')).main : ={glob P, glob C, glob D'} ==> 
                                              ={glob P, glob C, glob D', res}.
  proof. by sim. qed.

  local lemma PrConstrDistPad &m: 
      Pr[ Ind2.GReal(ConstrPad(C), P, D').main() @ &m : res] =
      Pr[ Ind1.GReal(C, P, DistPad(D')).main() @ &m : res].
  proof. by byequiv ConstrDistPad. qed.

  local equiv DistH2H1:
      Ind2.GIdeal(RO2.H, SimPadinv(S), D').main ~
      Ind1.GIdeal(RO1.H, S, DistPad(D')).main :
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
    inline *;wp. call (_: ={glob D'}). 
    auto;progress;by rewrite !map0P.
  qed.

  local lemma PrDistH2H1 &m:  
      Pr[Ind2.GIdeal(RO2.H,SimPadinv(S),D').main() @ &m : res] =
      Pr[Ind1.GIdeal(RO1.H,S, DistPad(D')).main() @ &m : res].
  proof. by byequiv DistH2H1. qed.

  lemma Conclusion &m:
      `| Pr[Ind2.GReal (ConstrPad(C), P           , D'         ).main() @ &m : res] -
         Pr[Ind2.GIdeal(RO2.H       , SimPadinv(S), D'         ).main() @ &m : res] | =
      `| Pr[Ind1.GReal (C           , P           , DistPad(D')).main() @ &m : res] - 
         Pr[Ind1.GIdeal(RO1.H       , S           , DistPad(D')).main() @ &m : res] |.
  proof. by rewrite (PrConstrDistPad &m) (PrDistH2H1 &m). qed.

end section Reduction.
