(* -------------------------------------------------------------------- *)
require import Fun Pred Option Pair Int IntDiv Real List FSet NewFMap.
require (*--*) Blocks TopLevel.

(* -------------------------------------------------------------------- *)
require import Common.

(* -------------------------------------------------------------------- *)
module UpperFun (F : Blocks.FUNCTIONALITY) = {
  proc init = F.init

  proc f(p : bool list, n : int) = {
    var xs;

    xs <@ F.f(pad2blocks p, (n + r - 1) %/ r);
    return take n (blocks2bits xs);
  }
}.

module LowerFun (F : TopLevel.FUNCTIONALITY) = {
  proc init = F.init

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

(* -------------------------------------------------------------------- *)
equiv ModularConstruction:
  UpperFun(Blocks.BlockSponge(Perm)).f ~ TopLevel.Sponge(Perm).f:
    ={glob Perm, arg} ==> ={glob Perm, res}.
proof.
  proc. inline Blocks.BlockSponge(Perm).f.
  admit. (* done *)
qed.

module ModularSimulator (S : Blocks.SIMULATOR, F : TopLevel.FUNCTIONALITY) = S(LowerFun(F)).

module BlocksDist ( D : TopLevel.DISTINGUISHER, F : Blocks.FUNCTIONALITY, P : PRIMITIVE) =
  D(UpperFun(F),P).

section.
  declare module BlocksSim : Blocks.SIMULATOR.
  declare module TopLevelDist : TopLevel.DISTINGUISHER.

  lemma Conclusion &m:
    `|Pr[TopLevel.RealIndif(TopLevel.Sponge,Perm,TopLevelDist).main() @ &m: res]
      - Pr[TopLevel.IdealIndif(TopLevel.BIRO.IRO',ModularSimulator(BlocksSim),TopLevelDist).main() @ &m: res]|
    = `|Pr[Blocks.RealIndif(Blocks.BlockSponge,Perm,BlocksDist(TopLevelDist)).main() @ &m: res]
      - Pr[Blocks.IdealIndif(Blocks.BIRO.IRO',BlocksSim,BlocksDist(TopLevelDist)).main() @ &m: res]|.
  proof. admit. qed.
