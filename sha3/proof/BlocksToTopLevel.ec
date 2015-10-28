(* -------------------------------------------------------------------- *)
require import Fun Pred Option Pair Int Real List FSet NewFMap.
require (*--*) Blocks TopLevel.

(* -------------------------------------------------------------------- *)
require import Common.
print Common.

op chunk: bool list -> bool list list.

op padlength (n : int) =
  let n' = (n + 2) %% r in
  if n' = 0 then 0 else r - n'.

op pad (bs : bool list): block list =
  let p = rcons (true :: mkseq (fun k => false) (padlength (size bs))) true in
  map bits2w (chunk (bs ++ p)).

op unpad (bs : block list): bool list option. (* Alley to fill in the definition *)

axiom unpadK (bs : bool list): pcancel pad unpad.
axiom padK (*?*) (bs : block list): ocancel unpad pad.

op valid_lower (bs : block list) = unpad bs <> None.

clone Blocks as Lower with
  op valid <- valid_lower.

clone TopLevel as Upper.

(* -------------------------------------------------------------------- *)
module UpperFun ( F : Lower.FUNCTIONALITY ) = {
  proc init = F.init

  proc f(p : bool list, n : int) = {
    var bs;

    bs  <@ F.f(pad p,(n + r - 1) /% r);
    return take n (flatten (map w2bits bs));
  }
}.

module LowerFun ( F: Upper.FUNCTIONALITY) = {
  proc init = F.init

  proc f(p : block list, n : int) = {
    var bs, m;
    var bs' <- [];

    m <- unpad p;
    if (m <> None) {
      bs  <@ F.f(oget m,n * r);
      bs' <- map bits2w (chunk bs);
    }
    return bs';
  }
}.

(* -------------------------------------------------------------------- *)
equiv ModularConstruction:
  UpperFun(Lower.BlockSponge(Perm)).f ~ Upper.Sponge(Perm).f:
    ={glob Perm, arg} ==> ={glob Perm, res}.
proof.
  proc. inline Lower.BlockSponge(Perm).f.
  admit. (* done *)
qed.

module ModularSimulator (S : Lower.SIMULATOR, F : Upper.FUNCTIONALITY) = S(LowerFun(F)).

module LowerDist ( D : Upper.DISTINGUISHER, F : Lower.FUNCTIONALITY, P : PRIMITIVE) =
  D(UpperFun(F),P).

section.
  declare module LowerSim : Lower.SIMULATOR.
  declare module UpperDist : Upper.DISTINGUISHER.

  lemma Conclusion &m:
    `|Pr[Upper.RealIndif(Upper.Sponge,Perm,UpperDist).main() @ &m: res]
      - Pr[Upper.IdealIndif(Upper.BIRO.IRO',ModularSimulator(LowerSim),UpperDist).main() @ &m: res]|
    = `|Pr[Lower.RealIndif(Lower.BlockSponge,Perm,LowerDist(UpperDist)).main() @ &m: res]
      - Pr[Lower.IdealIndif(Lower.BIRO.IRO',LowerSim,LowerDist(UpperDist)).main() @ &m: res]|.
  proof. admit. qed.
