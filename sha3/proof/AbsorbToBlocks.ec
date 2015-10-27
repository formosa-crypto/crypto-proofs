(* -------------------------------------------------------------------- *)
require import Option Pair Int Real List FSet NewFMap.
require (*--*) Absorb Blocks.

(* -------------------------------------------------------------------- *)
require import Common.

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

lemma ge0_strip_aux n bs:
  0 <= n =>
  0 <= (strip_aux bs n).`2.
proof.
  elim bs n=> //= b bs ih n le0_n.
  case (b = b0)=> //=.
  by rewrite (ih (n + 1) _) 1:smt.
qed.

lemma ge0_strip2 bs:
  0 <= (strip bs).`2.
proof. by rewrite /strip; exact/(ge0_strip_aux 0 (rev bs)). qed.

op valid_upper (bs : block list) =
  bs <> [] /\
  forallb (fun n=> strip (extend bs n) = (bs,n)).

op valid_lower (bs : block list) =
  valid_upper (strip bs).`1.

(* PY: FIXME *)
clone Absorb as Lower with
  op cast  <- cast<:'a>,
  op valid <- valid_lower.

clone Blocks as Upper with
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

module UpperOfLowerBlockSponge (P : Upper.PRIMITIVE) = UpperFun(Lower.BlockSponge(P)).

module Dist ( D : Upper.DISTINGUISHER, F : Lower.FUNCTIONALITY, P : Lower.PRIMITIVE ) = D(UpperFun(F),P).

section.
  declare module LowerSim  : Lower.SIMULATOR { Perm, Upper.BIRO.IRO', Lower.Ideal.RO }.
  declare module UpperDist : Upper.DISTINGUISHER { Perm, Upper.BIRO.IRO', Lower.Ideal.RO, LowerSim }.

  local equiv ModularUpper_Real:
    UpperFun(Lower.BlockSponge(Perm)).f ~ Upper.BlockSponge(Perm).f:
         ={arg}
      /\ ={m,mi}(Perm,Perm)
      /\ (forall x, mem (dom Perm.m){1} x)
      ==>    ={res}
          /\ ={m,mi}(Perm,Perm)
          /\ (forall x, mem (dom Perm.m){1} x).
  proof.
  proc. sp; if=> //=.
  inline Lower.BlockSponge(Perm).f.
  admit. (* Fun with loops *)
  qed.

  pred lower (ro : (block list,block) fmap) (iro : (block list * int,block) fmap) =
    Upper.BIRO.prefix_closed iro /\
    forall x n, valid_upper x => iro.[(x,n)] = ro.[extend x n].

  local equiv ModularLower:
    UpperFun(Lower.Ideal.RO).f ~ Upper.BIRO.IRO'.f:
          ={arg}
          /\ lower Lower.Ideal.RO.m{1} Upper.BIRO.IRO'.mp{2}
      ==> ={res}
          /\ lower Lower.Ideal.RO.m{1} Upper.BIRO.IRO'.mp{2}.
  proof.
  proc. sp; if=> //=.
  inline Lower.BlockSponge(Perm).f.
  admit. (* Fun with loops *)
  qed.

  pred upper (ro : (block list,block) fmap) (iro : (block list * int,block) fmap) =
    (forall x y, valid_lower x => ro.[x] = Some y => iro.[strip x] = Some y)
    /\ (forall x n y,
          valid_upper x =>
          iro.[(x,n)] = Some y =>
          exists n',
               n <= n'
            /\ mem (dom ro) (extend x n')).

  module LowIRO' : Lower.FUNCTIONALITY = {
    proc init = Upper.BIRO.IRO'.init
    proc f(x : block list) = {
      var b <- b0;

      if (valid_lower x) {
        b <@ Upper.BIRO.IRO'.f_lazy(strip x);
      }

      return b;
    }
  }.

  pred holey_map (iro iro_lazy : (block list * int,block) fmap) =
        Upper.BIRO.prefix_closed iro
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
    eager [Upper.BIRO.IRO'.resample_invisible(); , LowerFun(Upper.BIRO.IRO').f ~ LowIRO'.f, Upper.BIRO.IRO'.resample_invisible();:
              ={arg, Upper.BIRO.IRO'.visible}
           /\ holey_map Upper.BIRO.IRO'.mp{1} Upper.BIRO.IRO'.mp{2}
           /\ Upper.BIRO.IRO'.visible{2} = dom (Upper.BIRO.IRO'.mp){2}
           ==>     ={res, Upper.BIRO.IRO'.visible}
               /\ holey_map Upper.BIRO.IRO'.mp{1} Upper.BIRO.IRO'.mp{2}
               /\ Upper.BIRO.IRO'.visible{2} = dom (Upper.BIRO.IRO'.mp){2}].
  proof.
    eager proc.
    case (!valid_lower p{1})=> /=.
      rcondf{1} 3; 1: by auto; inline *; auto; while (true); auto.
      rcondf{2} 2; 1: by auto.
      inline *; auto.
      rcondf{2} 4; 1: by auto; smt.
      while{1} (   work{1} <= dom (Upper.BIRO.IRO'.mp){1}
                /\ holey_map Upper.BIRO.IRO'.mp{1} Upper.BIRO.IRO'.mp{2}
                /\ forall x, mem work{1} x => mem (dom Upper.BIRO.IRO'.mp){1} x /\ !mem (dom Upper.BIRO.IRO'.mp){2} x)
               (card work{1}).
        auto; progress.
        + admit. (* TODO: dto lossless *)
        + move=> x; rewrite domP in_fsetD in_fsetU !in_fset1.
          by case (x = pick work{hr})=> //= _ /H1 [->].
        + smt.
        + smt.
        + have [_] [_] /(_ x1 n0 _) //= := H0.
          move: H5; rewrite domP in_fsetU in_fset1=> [//=|h].
          by have [->]:= H1 (x1,n0) _; first by rewrite h mem_pick // H2.
        + move: H5; rewrite domP in_fsetD in_fsetU !in_fset1.
          by case (x1 = pick work{hr})=> //= _ /H1 [->].
        + move: H5; rewrite in_fsetD in_fset1.
          by case (x1 = pick work{hr})=> //= _ /H1 [_ ->].
        + smt.
      by auto; smt.
    rcondt{1} 3; 1: by auto; inline *; auto; while (true); auto.
    rcondt{2} 2; 1: by auto.
    inline Upper.BIRO.IRO'.f Upper.BIRO.IRO'.f_lazy.
    rcondt{1} 8; 1: by auto; inline *; auto; while (true); auto; smt.
    rcondt{2} 4; 1: by auto; smt.
    case ((mem (dom Upper.BIRO.IRO'.mp) (strip p)){1} /\ !(mem (dom Upper.BIRO.IRO'.mp) (strip x)){2}).
      admit. (* this is the bad case where we need to bring down the sampling from resample_invisible *)
    inline{2} Upper.BIRO.IRO'.resample_invisible.
    rcondf{2} 9; 1: by auto; inline *; sp; if; auto; smt.
    seq  1  0: ((((p{1} = x{2} /\ ={Upper.BIRO.IRO'.visible}) /\
    holey_map Upper.BIRO.IRO'.mp{1} Upper.BIRO.IRO'.mp{2} /\
    Upper.BIRO.IRO'.visible{2} = dom Upper.BIRO.IRO'.mp{2}) /\
   valid_lower p{1}) /\
  ! (mem (dom Upper.BIRO.IRO'.mp{1}) (strip p{1}) /\
     ! mem (dom Upper.BIRO.IRO'.mp{2}) (strip x{2}))). (* disgusting copy-paste. we need seq* *)
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
  qed.


  (** This is an eager statement:
        - on actual queries, the two maps agree;
        - blocks in the IRO that are just generated on the way
          to answering actual queries can be resampled. **)
  (* Lower.Ideal.RO.f ~ LowerFun(Upper.BIRO.IRO).f:
             ={arg}
          /\ true
      ==> ={res}.
  *)

  lemma Intermediate &m:
    `|Pr[Upper.RealIndif(Perm,Upper.BlockSponge,UpperDist).main() @ &m :res]
      - Pr[Upper.IdealIndif(Upper.BIRO.IRO,Sim(LowerSim),UpperDist).main() @ &m: res]|
    = `|Pr[Upper.RealIndif(Perm,UpperOfLowerBlockSponge,UpperDist).main() @ &m: res]
        - Pr[Upper.IdealIndif(UpperFun(Lower.Ideal.RO),Sim(LowerSim),UpperDist).main() @ &m: res]|.
  proof.
  have ->: Pr[Upper.RealIndif(Perm,UpperOfLowerBlockSponge,UpperDist).main() @ &m: res]
           = Pr[Upper.RealIndif(Perm,Upper.BlockSponge,UpperDist).main() @ &m :res].
    byequiv=> //=; proc.
    call (_:   ={m,mi}(Perm,Perm)
            /\ (forall x, mem (dom Perm.m){1} x)).
      by proc; if; auto; smt.
      by proc; if; auto; smt.
      (* BUG: arg should be handled much earlier and automatically *)
      by conseq ModularUpper=> //= &1 &2; case (arg{1}); case (arg{2})=> //=.
    call (_:     true
             ==>    ={glob Perm}
                 /\ (forall x, mem (dom Perm.m){1} x)).
      admit. (* Do this with an eagerly sampled RP *)
    (* Now the other initialization is dead code. *)
    call (_: true ==> true)=> //.
      by proc; auto.
  have ->: Pr[Upper.IdealIndif(UpperFun(Lower.Ideal.RO),Sim(LowerSim),UpperDist).main() @ &m: res]
           = Pr[Upper.IdealIndif(Upper.BIRO.IRO,Sim(LowerSim),UpperDist).main() @ &m: res].
    byequiv=> //=; proc.
    call (_: ={glob LowerSim} /\ relation Lower.Ideal.RO.m{1} Upper.BIRO.IRO.mp{2}).
      proc (relation Lower.Ideal.RO.m{1} Upper.BIRO.IRO.mp{2})=> //=.
        by proc; sp; if=> //=; call ModularLower; auto.
      proc (relation Lower.Ideal.RO.m{1} Upper.BIRO.IRO.mp{2})=> //=.
        by proc; sp; if=> //=; call ModularLower; auto.
      (* Re-Bug *)
      by conseq ModularLower=> &1 &2; case (arg{1}); case (arg{2}).
    inline *; wp; call (_: true)=> //=.
      by sim.
    auto; progress [-split]; split=> //=.
    by split=> x y; rewrite map0P.
  done.
  qed.

  lemma Remainder &m:
    `|Pr[Upper.RealIndif(Perm,UpperOfLowerBlockSponge,UpperDist).main() @ &m: res]
      - Pr[Upper.IdealIndif(UpperFun(Lower.Ideal.RO),Sim(LowerSim),UpperDist).main() @ &m: res]|
    = `|Pr[Lower.RealIndif(Perm,Lower.BlockSponge,Dist(UpperDist)).main() @ &m: res]
        - Pr[Lower.IdealIndif(Lower.Ideal.RO,LowerSim,Dist(UpperDist)).main() @ &m: res]|.
  proof. admit. qed.

  lemma Conclusion &m:
    `|Pr[Upper.RealIndif(Perm,Upper.BlockSponge,UpperDist).main() @ &m: res]
      - Pr[Upper.IdealIndif(Upper.BIRO.IRO,Sim(LowerSim),UpperDist).main() @ &m: res]|
    = `|Pr[Lower.RealIndif(Perm,Lower.BlockSponge,Dist(UpperDist)).main() @ &m: res]
      - Pr[Lower.IdealIndif(Lower.Ideal.RO,LowerSim,Dist(UpperDist)).main() @ &m: res]|.
  proof. by rewrite (Intermediate &m) (Remainder &m). qed.
end section.
