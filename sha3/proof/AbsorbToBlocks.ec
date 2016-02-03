(* -------------------------------------------------------------------- *)
require import Option Pair Int Real List FSet NewFMap.
require (*--*) AbsorbSponge BlockSponge.

(* -------------------------------------------------------------------- *)
require import Common.

op cast: 'a NewDistr.distr -> 'a distr.

(* -------------------------------------------------------------------- *)
module LowerFun(F : Self.BlockSponge.DFUNCTIONALITY) : AbsorbSponge.DFUNCTIONALITY = {
  proc init() = {}

  proc f(xs : block list) : block = {
    var (ys, n) <- strip xs;
    var zs <- [];

    if (valid_block ys) {
      zs <@ F.f(ys, n + 1);
    }
    return last b0 zs;
  }
}.

module Sim (S : AbsorbSponge.SIMULATOR, F : Self.BlockSponge.DFUNCTIONALITY) = S(LowerFun(F)).

module UpperFun (F : AbsorbSponge.DFUNCTIONALITY) = {
  proc init() = {}

  proc f(xs : block list, n : int) : block list = {
    var y <- b0;
    var ys <- [];
    var i <- 0;

    if (valid_block xs) {
      while (i < n) {
        y <@ F.f(extend xs i);
        ys <- rcons ys y;
        i <- i + 1;
      }
    }
    return ys;
  }
}.

module BlocksOfAbsorbBlockSponge (P : Self.BlockSponge.DPRIMITIVE) =
  UpperFun(AbsorbSponge.BlockSponge(P)).

module Dist (D : Self.BlockSponge.DISTINGUISHER, F : AbsorbSponge.DFUNCTIONALITY) = D(UpperFun(F)).

section.
  declare module AbsorbSim  : AbsorbSponge.SIMULATOR { Perm, Self.BlockSponge.BIRO.IRO', AbsorbSponge.Ideal.RO }.
  declare module BlocksDist : Self.BlockSponge.DISTINGUISHER { Perm, Self.BlockSponge.BIRO.IRO', AbsorbSponge.Ideal.RO, AbsorbSim }.

  local equiv ModularBlocks_Real:
    UpperFun(AbsorbSponge.BlockSponge(Perm)).f ~ Self.BlockSponge.Sponge(Perm).f:
         ={arg}
      /\ ={m,mi}(Perm,Perm)
      /\ (forall x, mem (dom Perm.m){1} x)
      ==>    ={res}
          /\ ={m,mi}(Perm,Perm)
          /\ (forall x, mem (dom Perm.m){1} x).
  proof.
  proc. sp; if=> //=.
  inline AbsorbSponge.BlockSponge(Perm).f.
  admit. (* Fun with loops *)
  qed.

  pred lower (ro : (block list,block) fmap) (iro : (block list * int,block) fmap) =
    Self.BlockSponge.BIRO.prefix_closed iro /\
    forall x n, valid_block x => iro.[(x,n)] = ro.[extend x n].

  local equiv ModularAbsorb:
    UpperFun(AbsorbSponge.Ideal.RO).f ~ Self.BlockSponge.BIRO.IRO'.f:
          ={arg}
          /\ lower AbsorbSponge.Ideal.RO.m{1} Self.BlockSponge.BIRO.IRO'.mp{2}
      ==> ={res}
          /\ lower AbsorbSponge.Ideal.RO.m{1} Self.BlockSponge.BIRO.IRO'.mp{2}.
  proof.
  proc. sp; if=> //=.
  inline AbsorbSponge.BlockSponge(Perm).f.
  admit. (* Fun with loops *)
  qed.

  pred upper (ro : (block list,block) fmap) (iro : (block list * int,block) fmap) =
    (forall x y, valid_absorb x => ro.[x] = y => iro.[strip x] = y)
    /\ (forall x n y,
          valid_block x =>
          iro.[(x,n)] = Some y =>
          exists n',
               n <= n'
            /\ mem (dom ro) (extend x n')).

  module LowIRO' : AbsorbSponge.FUNCTIONALITY = {
    proc init = Self.BlockSponge.BIRO.IRO'.init
    proc f(xs : block list) = {
      var b <- b0;
      var (ys, n) = strip xs;

      if (valid_block ys) {
        b <@ Self.BlockSponge.BIRO.IRO'.f_lazy(ys, n);
      }

      return b;
    }
  }.

  pred holey_map (iro iro_lazy : (block list * int,block) fmap) =
        Self.BlockSponge.BIRO.prefix_closed iro
     /\ (forall xn,
          mem (dom iro_lazy) xn =>
          iro_lazy.[xn] = iro.[xn])
     /\ (forall x n,
          mem (dom iro) (x,n) =>
          exists n',
               n <= n'
            /\ mem (dom iro_lazy) (x,n')).

  (** Essentially, we can delay sampling every entry in the left map
      whose index is not in the index of the right map, as they have
      not ben given to the adversary. **)
  local lemma LazifyIRO:
    eager [Self.BlockSponge.BIRO.IRO'.resample_invisible(); , LowerFun(Self.BlockSponge.BIRO.IRO').f ~ LowIRO'.f, Self.BlockSponge.BIRO.IRO'.resample_invisible();:
              ={arg, Self.BlockSponge.BIRO.IRO'.visible}
           /\ holey_map Self.BlockSponge.BIRO.IRO'.mp{1} Self.BlockSponge.BIRO.IRO'.mp{2}
           /\ Self.BlockSponge.BIRO.IRO'.visible{2} = dom (Self.BlockSponge.BIRO.IRO'.mp){2}
           ==>     ={res, Self.BlockSponge.BIRO.IRO'.visible}
               /\ holey_map Self.BlockSponge.BIRO.IRO'.mp{1} Self.BlockSponge.BIRO.IRO'.mp{2}
               /\ Self.BlockSponge.BIRO.IRO'.visible{2} = dom (Self.BlockSponge.BIRO.IRO'.mp){2}].
  proof.
(*
    eager proc.
    case (!valid_lower p{1})=> /=.
      rcondf{1} 3; 1: by auto; inline *; auto; while (true); auto.
      rcondf{2} 2; 1: by auto.
      inline *; auto.
      rcondf{2} 4; 1: by auto; smt.
      while{1} (   work{1} <= dom (Blocks.BIRO.IRO'.mp){1}
                /\ holey_map Blocks.BIRO.IRO'.mp{1} Blocks.BIRO.IRO'.mp{2}
                /\ forall x, mem work{1} x => mem (dom Blocks.BIRO.IRO'.mp){1} x /\ !mem (dom Blocks.BIRO.IRO'.mp){2} x)
               (card work{1}).
        auto; progress.
        + admit. (* TODO: dto lossless *)
        + move=> x; rewrite domP in_fsetD in_fsetU !in_fset1.
          by case (x = pick work{hr})=> //= _ /H1 [->].
        + smt.
        + smt.
        + have [_] [_] /(_ x1 n0 _) //= := H0.
          move: H5; rewrite domP in_fsetU in_fset1=> -[//=|h].
          by have [->]:= H1 (x1,n0) _; first by rewrite h mem_pick // H2.
        + move: H5; rewrite domP in_fsetD in_fsetU !in_fset1.
          by case (x1 = pick work{hr})=> //= _ /H1 [->].
        + move: H5; rewrite in_fsetD in_fset1.
          by case (x1 = pick work{hr})=> //= _ /H1 [_ ->].
        + smt.
      by auto; smt.
    rcondt{1} 3; 1: by auto; inline *; auto; while (true); auto.
    rcondt{2} 2; 1: by auto.
    inline Blocks.BIRO.IRO'.f Blocks.BIRO.IRO'.f_lazy.
    rcondt{1} 8; 1: by auto; inline *; auto; while (true); auto; smt.
    rcondt{2} 4; 1: by auto; smt.
    case ((mem (dom Blocks.BIRO.IRO'.mp) (strip p)){1} /\ !(mem (dom Blocks.BIRO.IRO'.mp) (strip x)){2}).
      admit. (* this is the bad case where we need to bring down the sampling from resample_invisible *)
    inline{2} Blocks.BIRO.IRO'.resample_invisible.
    rcondf{2} 9; 1: by auto; inline *; sp; if; auto; smt.
    seq  1  0: ((((p{1} = x{2} /\ ={Blocks.BIRO.IRO'.visible}) /\
    holey_map Blocks.BIRO.IRO'.mp{1} Blocks.BIRO.IRO'.mp{2} /\
    Blocks.BIRO.IRO'.visible{2} = dom Blocks.BIRO.IRO'.mp{2}) /\
   valid_lower p{1}) /\
  ! (mem (dom Blocks.BIRO.IRO'.mp{1}) (strip p{1}) /\
     ! mem (dom Blocks.BIRO.IRO'.mp{2}) (strip x{2}))). (* disgusting copy-paste. we need seq* *)
      admit.
    splitwhile{1} 8: (i < n0 - 1).
    rcondt{1} 9.
      move=> &m; while (0 <= i < n0).
        by inline*; sp; if; auto; smt.
      by auto; smt.
    rcondf{1} 12.
      move=> &m; seq 8: (i = n0 - 1).
       * wp; while (0 <= i < n0).
           by inline*; sp; if; auto; smt.
         by auto; smt.
       * inline*; sp; if; auto; smt.
    admit. (* just pushing the proof through *)
*)
  admit.
  qed.


  (** This is an eager statement:
        - on actual queries, the two maps agree;
        - blocks in the IRO that are just generated on the way
          to answering actual queries can be resampled. **)
  (* AbsorbSponge.Ideal.RO.f ~ LowerFun(Blocks.BIRO.IRO).f:
             ={arg}
          /\ true
      ==> ={res}.
  *)

  lemma Intermediate &m:
    `|Pr[Self.BlockSponge.RealIndif(Self.BlockSponge.Sponge,Perm,BlocksDist).main() @ &m :res]
      - Pr[Self.BlockSponge.IdealIndif(Self.BlockSponge.BIRO.IRO',Sim(AbsorbSim),BlocksDist).main() @ &m: res]|
    = `|Pr[Self.BlockSponge.RealIndif(BlocksOfAbsorbBlockSponge,Perm,BlocksDist).main() @ &m: res]
        - Pr[Self.BlockSponge.IdealIndif(UpperFun(AbsorbSponge.Ideal.RO),Sim(AbsorbSim),BlocksDist).main() @ &m: res]|.
  proof.
  have ->: Pr[Self.BlockSponge.RealIndif(BlocksOfAbsorbBlockSponge,Perm,BlocksDist).main() @ &m: res]
           = Pr[Self.BlockSponge.RealIndif(Self.BlockSponge.Sponge,Perm,BlocksDist).main() @ &m :res].
    byequiv=> //=; proc.
    call (_:   ={m,mi}(Perm,Perm)
            /\ (forall x, mem (dom Perm.m){1} x)).
      by proc; if; auto; smt.
      by proc; if; auto; smt.
      (* BUG: arg should be handled much earlier and automatically *)
      by conseq ModularBlocks_Real=> //= &1 &2; case (arg{1}); case (arg{2})=> //=.
    call (_:     true
             ==>    ={glob Perm}
                 /\ (forall x, mem (dom Perm.m){1} x)).
      admit. (* Do this with an eagerly sampled RP *)
    (* Now the other initialization is dead code. *)
    call (_: true ==> true)=> //.
      by proc; auto.
  have ->: Pr[Self.BlockSponge.IdealIndif(UpperFun(AbsorbSponge.Ideal.RO),Sim(AbsorbSim),BlocksDist).main() @ &m: res]
           = Pr[Self.BlockSponge.IdealIndif(Self.BlockSponge.BIRO.IRO',Sim(AbsorbSim),BlocksDist).main() @ &m: res].
    byequiv=> //=; proc.
    call (_: ={glob AbsorbSim} /\ lower AbsorbSponge.Ideal.RO.m{1} Self.BlockSponge.BIRO.IRO'.mp{2}).
      proc (lower AbsorbSponge.Ideal.RO.m{1} Self.BlockSponge.BIRO.IRO'.mp{2})=> //=.
        proc; sp; if=> //=. smt.
        call ModularAbsorb; auto; smt.
      proc (lower AbsorbSponge.Ideal.RO.m{1} Self.BlockSponge.BIRO.IRO'.mp{2})=> //=.
        proc; sp; if=> //=. smt.
        call ModularAbsorb; auto; smt.
      (* Re-Bug *)
      by conseq ModularAbsorb=> &1 &2; case (arg{1}); case (arg{2}).
    inline *; wp;call (_: true)=> //=.
    auto; progress [-split]; split=> //=.
    admit.
  done.
  qed.

  lemma Remainder &m:
    `|Pr[Self.BlockSponge.RealIndif(BlocksOfAbsorbBlockSponge,Perm,BlocksDist).main() @ &m: res]
      - Pr[Self.BlockSponge.IdealIndif(UpperFun(AbsorbSponge.Ideal.RO),Sim(AbsorbSim),BlocksDist).main() @ &m: res]|
    = `|Pr[AbsorbSponge.RealIndif(AbsorbSponge.BlockSponge,Perm,Dist(BlocksDist)).main() @ &m: res]
        - Pr[AbsorbSponge.IdealIndif(AbsorbSponge.Ideal.RO,AbsorbSim,Dist(BlocksDist)).main() @ &m: res]|.
  proof. admit. qed.

  lemma Conclusion &m:
    `|Pr[Self.BlockSponge.RealIndif(Self.BlockSponge.Sponge,Perm,BlocksDist).main() @ &m: res]
      - Pr[Self.BlockSponge.IdealIndif(Self.BlockSponge.BIRO.IRO',Sim(AbsorbSim),BlocksDist).main() @ &m: res]|
    = `|Pr[AbsorbSponge.RealIndif(AbsorbSponge.BlockSponge,Perm,Dist(BlocksDist)).main() @ &m: res]
      - Pr[AbsorbSponge.IdealIndif(AbsorbSponge.Ideal.RO,AbsorbSim,Dist(BlocksDist)).main() @ &m: res]|.
  proof. by rewrite (Intermediate &m) (Remainder &m). qed.
end section.
