(* -------------------------------------------------------------------- *)
require import Option Pair Int Real List FSet NewFMap.
require (*--*) Absorb Blocks.

(* -------------------------------------------------------------------- *)
require import Common.

op ( * ): 'a NewDistr.distr -> 'b NewDistr.distr -> ('a * 'b) distr.
op cast: 'a NewDistr.distr -> 'a distr.

op extend (bs : block list) (n : int): block list =
  bs ++ (mkseq (fun k => b0) n).

op strip_aux (bs : block list) (n : int) : block list * int =
  with bs = [] => ([],n)
  with bs = b :: bs =>
    if   b = b0
    then strip_aux bs (n + 1)
    else (rev (b :: bs),n).

op strip (bs : block list) = strip_aux (rev bs) 0.

op valid_upper (bs : block list) =
  bs <> [] /\
  forallb (fun n=> strip (extend bs n) = (bs,n)).

op valid_lower (bs : block list) =
  valid_upper (strip bs).`1.

(* PY: FIXME *)
clone Absorb as Lower with
  op ( * ) <- ( * )<:'a,'b>,
  op cast  <- cast<:'a>,
  op valid <- valid_lower.

clone Blocks as Upper with
  op ( * ) <- ( * )<:'a,'b>,
  op valid <- valid_upper.

(* -------------------------------------------------------------------- *)
module LowerFun( F : Upper.FUNCTIONALITY ) : Lower.FUNCTIONALITY = {
  proc init = F.init

  proc f(p : block list): block = {
    var b <- [];
    var n;

    if (valid_lower p) {
      (p,n) <- strip p;
      b <@ F.f(p,n + 1);
    }
    return last b0 b;
  }
}.

module Sim ( S : Lower.SIMULATOR, F : Upper.FUNCTIONALITY ) = S(LowerFun(F)).

module UpperFun ( F : Lower.FUNCTIONALITY ) = {
  proc init = F.init

  proc f(p : block list, n : int) : block list = {
    var b <- b0;
    var bs <- [];
    var i <- 0;

    if (valid_upper p) {
      while (i < n) {
        b <@ F.f(extend p i);
        bs <- rcons bs b;
        i <- i + 1;
      }
    }

    return bs;
  }
}.

module Dist ( D : Upper.DISTINGUISHER, F : Lower.FUNCTIONALITY, P : Lower.PRIMITIVE ) = D(UpperFun(F),P).

section.
  declare module LowerSim  : Lower.SIMULATOR.
  declare module UpperDist : Upper.DISTINGUISHER { LowerSim }.

  local equiv ModularUpper:
    UpperFun(Lower.BlockSponge(Lower.Perm.Perm)).f ~ Upper.BlockSponge(Upper.Perm.Perm).f:
         ={arg}
      /\ ={m,mi}(Lower.Perm.Perm,Upper.Perm.Perm)
      /\ (forall x, mem (dom Lower.Perm.Perm.m){1} x)
      ==>    ={res}
          /\ ={m,mi}(Lower.Perm.Perm,Upper.Perm.Perm)
          /\ (forall x, mem (dom Lower.Perm.Perm.m){1} x).
  proof.
  proc. sp; if=> //=.
  inline Lower.BlockSponge(Lower.Perm.Perm).f.
  admit. (* Fun with loops *)
  qed.

  pred relation (ro : (block list,block) fmap) (iro : (block list,block list) fmap) =
    (forall x y, iro.[x] = Some y =>
      forall i, 0 <= i < size y => ro.[extend x i] = onth y i)
 /\ (forall x y, ro.[x] = Some y =>
      let (x',n) = strip x in
         mem (dom iro) x
      /\ size (oget iro.[x]) >= n
      /\ nth witness (oget iro.[x]) n = y).

  local equiv ModularLower:
    UpperFun(Lower.Ideal.RO).f ~ Upper.BIRO.IRO.f:
          ={arg}
          /\ relation Lower.Ideal.RO.m{1} Upper.BIRO.IRO.mp{2}
      ==> ={res}
          /\ relation Lower.Ideal.RO.m{1} Upper.BIRO.IRO.mp{2}.
  proof.
  proc. sp; if=> //=.
  inline Lower.BlockSponge(Lower.Perm.Perm).f.
  admit. (* Fun with loops *)
  qed.

  lemma Conclusion &m:
    `|Pr[Upper.RealIndif(Upper.Perm.Perm,Upper.BlockSponge,UpperDist).main() @ &m: res]
      - Pr[Upper.IdealIndif(Upper.BIRO.IRO,Sim(LowerSim),UpperDist).main() @ &m: res]|
    = `|Pr[Lower.RealIndif(Lower.Perm.Perm,Lower.BlockSponge,Dist(UpperDist)).main() @ &m: res]
      - Pr[Lower.IdealIndif(Lower.Ideal.RO,LowerSim,Dist(UpperDist)).main() @ &m: res]|.
  proof. admit. qed.
end section.
