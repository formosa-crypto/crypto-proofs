(*------------------------- Sponge Construction ------------------------*)

require import Fun Pair Int IntDiv Real List Option FSet NewFMap DBool.
require import Common StdOrder. import IntOrder.
require (*--*) IRO BlockSponge RndO.

(*------------------------- Indifferentiability ------------------------*)

clone include Indifferentiability with
  type p     <- block * capacity,
  type f_in  <- bool list * int,
  type f_out <- bool list

  rename
    [module] "Indif" as "Experiment"
    [module] "GReal"  as "RealIndif"
    [module] "GIdeal"  as "IdealIndif".

(*------------------------- Ideal Functionality ------------------------*)

clone import IRO as BIRO with
  type from <- bool list,
  type to   <- bool,
  op valid  <- valid_toplevel,
  op dto    <- dbool.

(*------------------------- Sponge Construction ------------------------*)

module Sponge (P : DPRIMITIVE) : FUNCTIONALITY, CONSTRUCTION(P) = {
  proc init() : unit = {}

  proc f(bs : bool list, n : int) : bool list = {
    var z        <- [];
    var (sa, sc) <- (b0, Capacity.c0);
    var i        <- 0;
    var xs       <- pad2blocks bs;

    (* absorption *)
    while (xs <> []) {
      (sa, sc) <@ P.f(sa +^ head b0 xs, sc);
      xs        <- behead xs;
    }
    (* squeezing *)
    while (i < (n + r - 1) %/ r) {
      z        <- z ++ w2bits sa;
      (sa, sc) <@ P.f(sa, sc);
      i        <- i + 1;
    }

    return take n z;
  }
}.

(*------------- Simulator and Distinguisher Constructions --------------*)

module LowerFun (F : DFUNCTIONALITY) : BlockSponge.DFUNCTIONALITY = {
  proc f(xs : block list, n : int) = {
    var cs, ds : bool list;
    var obs : bool list option;
    var ys : block list <- [];

    obs <- unpad_blocks xs;
    if (obs <> None) {
      cs <@ F.f(oget obs, n * r); (* size cs = n * r *)
      ys <- bits2blocks cs; (* size ys = n *)
    }
    return ys;
  }
}.

module RaiseFun (F : BlockSponge.DFUNCTIONALITY) : DFUNCTIONALITY = {
  proc f(bs : bool list, n : int) = {
    var xs;

    xs <@ F.f(pad2blocks bs, (n + r - 1) %/ r);
    return take n (blocks2bits xs);
  }
}.

module LowerDist (D : DISTINGUISHER, F : BlockSponge.DFUNCTIONALITY) =
  D(RaiseFun(F)).

module RaiseSim (S : BlockSponge.SIMULATOR, F : DFUNCTIONALITY) =
  S(LowerFun(F)).

(*------------------------------- Proof --------------------------------*)

abstract theory HybridIRO.

module type HYBRID_IRO = {
  proc init() : unit
  proc g(x : block list, n : int) : bool list
  proc f(x : block list, n : int) : block list
}.

module type HYBRID_IRO_DIST(HI : HYBRID_IRO) = {
  proc distinguish(): bool
}.

module HybridIROEager : HYBRID_IRO, BlockSponge.BIRO.IRO = {
  var mp : (block list * int, bool) fmap

  proc init() : unit = {
    mp <- map0;
  }

  proc fill_in(xs, i) = {
    if (! mem (dom mp) (xs, i)) {
      mp.[(xs, i)] <$ dbool;
    }
    return oget mp.[(xs, i)];
  }

  proc g(xs, n) = {
    var b, bs;
    var m <- ((n + r - 1) %/ r) * r;
    var i <- 0;

    bs <- [];
    if (valid_block xs) {
      while (i < n) {
        b <@ fill_in(xs, i);
        bs <- rcons bs b;
        i <- i + 1;
      }
      while (i < m) {  (* eager part *)
        fill_in(xs, i);
        i <- i + 1;
      }
    }
    return bs;
  }

  proc f(xs, n) = {
    var bs, ys;
    bs <@ g(xs, n * r);
    ys <- bits2blocks bs;
    return ys;
  }
}.

module HybridIROLazy : HYBRID_IRO, BlockSponge.BIRO.IRO = {
  var mp : (block list * int, bool) fmap

  proc init() : unit = {
    mp <- map0;
  }

  proc fill_in(xs, i) = {
    if (! mem (dom mp) (xs, i)) {
      mp.[(xs, i)] <$ dbool;
    }
    return oget mp.[(xs, i)];
  }

  proc g(xs, n) = {
    var b, bs;
    var i <- 0;

    bs <- [];
    if (valid_block xs) {
      while (i < n) {
        b <@ fill_in(xs, i);
        bs <- rcons bs b;
        i <- i + 1;
      }
    }
    return bs;
  }

  proc f(xs, n) = {
    var bs, ys;
    bs <@ g(xs, n * r);
    ys <- bits2blocks bs;
    return ys;
  }
}.

section.

declare module D : HYBRID_IRO_DIST.

local clone RndO.GenEager as RO.

lemma HybridIROLazyEager (D <: HYBRID_IRO_DIST) &m :
  Pr[D(HybridIROLazy).distinguish() @ &m : res] =
  Pr[D(HybridIROEager).distinguish() @ &m : res].
proof.
byequiv=> //.
admit. (* use RndO.ec result *)
qed.

end section.

module RaiseHybridIRO (HI : HYBRID_IRO) : FUNCTIONALITY = {
  proc init() = {
    HI.init();
  }

  proc f(bs : bool list, n : int) = {
    var cs;

    cs <@ HI.g(pad2blocks bs, n);
    return cs;
  }
}.

pred LazyInvar
     (mp1 : (bool list * int, bool) fmap,
      mp2 : (block list * int, bool) fmap) =
  (forall (bs : bool list, n : int),
   mem (dom mp1) (bs, n) <=> mem (dom mp2) (pad2blocks bs, n)) /\
  (forall (xs : block list, n),
   mem (dom mp2) (xs, n) => valid_block xs) /\
  (forall (bs : bool list, n : int),
   mem (dom mp1) (bs, n) =>
   oget mp1.[(bs, n)] = oget mp2.[(pad2blocks bs, n)]).

lemma lazy_invar_upd_mem_dom_iff
      (mp1 : (bool list * int, bool) fmap,
       mp2 : (block list * int, bool) fmap,
       bs cs : bool list, n m : int, b : bool) :
  LazyInvar mp1 mp2 =>
  mem (dom mp1.[(bs, n) <- b]) (cs, m) <=>
  mem (dom mp2.[(pad2blocks bs, n) <- b]) (pad2blocks cs, m).
proof.
move=> LI; split=> [mem_upd_mp1 | mem_upd_mp2].
rewrite domP in_fsetU1; rewrite domP in_fsetU1 in mem_upd_mp1.
case: ((cs, m) = (bs, n))=> [cs_m_eq_bs_n | cs_m_neq_bs_n].
right; by elim cs_m_eq_bs_n=> ->->.
left; smt ml=0.
rewrite domP in_fsetU1; rewrite domP in_fsetU1 in mem_upd_mp2.
case: ((cs, m) = (bs, n))=> [// | cs_m_neq_bs_n].
elim mem_upd_mp2=> [/# | [p2b_cs_p2b_bs eq_mn]].
have /# : cs = bs by apply pad2blocks_inj.
qed.

lemma lazy_invar_upd2_vb
      (mp1 : (bool list * int, bool) fmap,
       mp2 : (block list * int, bool) fmap,
       bs : bool list, xs : block list, n m : int, b : bool) :
  LazyInvar mp1 mp2 =>
  mem (dom mp2.[(pad2blocks bs, n) <- b]) (xs, m) =>
  valid_block xs.
proof.
move=> LI mem_upd_mp2.
rewrite domP in_fsetU1 in mem_upd_mp2.
elim mem_upd_mp2=> [/# | [-> _]].
apply/valid_pad2blocks.
qed.

lemma lazy_invar_upd_lu_eq
      (mp1 : (bool list * int, bool) fmap,
       mp2 : (block list * int, bool) fmap,
       bs cs : bool list, n m : int, b : bool) :
  LazyInvar mp1 mp2 =>
  mem (dom mp1.[(bs, n) <- b]) (cs, m) =>
  oget mp1.[(bs, n) <- b].[(cs, m)] =
  oget mp2.[(pad2blocks bs, n) <- b].[(pad2blocks cs, m)].
proof.
move=> LI mem_upd_mp1.
case: ((cs, m) = (bs, n))=> [[->->] | cs_m_neq_bs_n].
smt ml=0 w=(getP_eq).
rewrite domP in_fsetU1 in mem_upd_mp1.
elim mem_upd_mp1=> [mem_mp1 | [->->]].
case: ((pad2blocks bs, n) = (pad2blocks cs, m))=>
  [[p2b_bs_p2b_cs eq_mn] | p2b_bs_n_neq_p2b_cs_m].
smt ml=0 w=(pad2blocks_inj).
smt ml=0 w=(getP).
smt ml=0 w=(getP).
qed.

lemma LowerFun_IRO_HybridIROLazy_f :
  equiv[LowerFun(IRO).f ~ HybridIROLazy.f :
        ={xs, n} /\ LazyInvar IRO.mp{1} HybridIROLazy.mp{2} ==>
        ={res} /\ LazyInvar IRO.mp{1} HybridIROLazy.mp{2}].
proof.
proc=> /=; inline HybridIROLazy.g.
seq 0 1 :
  (={n} /\ xs{1} = xs0{2} /\
   LazyInvar IRO.mp{1} HybridIROLazy.mp{2}); first auto.
case (valid_block xs{1}).
rcondt{1} 3; first auto. rcondt{2} 4; first auto.
inline *. rcondt{1} 7; first auto.
seq 6 3 : 
  (={i, n0} /\ bs{1} = bs0{2} /\
   LazyInvar IRO.mp{1} HybridIROLazy.mp{2} /\
   pad2blocks x{1} = xs0{2}).
auto; progress; have {2}<- /# := unpadBlocksK xs0{2}.
wp.
while
  (={i, n0} /\ bs{1} = bs0{2} /\
   LazyInvar IRO.mp{1} HybridIROLazy.mp{2} /\
   pad2blocks x{1} = xs0{2}).
sp; auto.
if.
progress; smt ml=0.
rnd; auto; progress;
  [smt ml=0 w=(getP_eq) |
   smt ml=0 w=(lazy_invar_upd_mem_dom_iff) |
   smt ml=0 w=(lazy_invar_upd_mem_dom_iff) |
   smt ml=0 w=(lazy_invar_upd2_vb) |
   smt ml=0 w=(lazy_invar_upd_lu_eq)].
auto; progress; smt ml=0.
auto.
rcondf{1} 3; first auto. rcondf{2} 4; first auto.
auto; progress; by rewrite bits2blocks_nil.
qed.

lemma IRO_RaiseHybridIRO_HybridIROLazy_f :
  equiv[IRO.f ~ RaiseHybridIRO(HybridIROLazy).f :
        ={n} /\ x{1} = bs{2} /\
        LazyInvar IRO.mp{1} HybridIROLazy.mp{2} ==>
        ={res} /\ LazyInvar IRO.mp{1} HybridIROLazy.mp{2}].
proof.
proc=> /=; inline *.
rcondt{1} 3; first auto.
rcondt{2} 5; first auto; progress; apply valid_pad2blocks.
seq 2 4 :
  (={i, n} /\ n{1} = n0{2} /\ xs{2} = pad2blocks x{1} /\ bs{1} = bs0{2} /\
   LazyInvar IRO.mp{1} HybridIROLazy.mp{2}); first auto.
wp.
while
  (={i, n} /\ n{1} = n0{2} /\ xs{2} = pad2blocks x{1} /\ bs{1} = bs0{2} /\
   LazyInvar IRO.mp{1} HybridIROLazy.mp{2}).
wp; sp.
if.
progress; smt ml=0.
rnd; skip; progress;
  [smt ml=0 w=(getP_eq) |
   smt ml=0 w=(lazy_invar_upd_mem_dom_iff) |
   smt ml=0 w=(lazy_invar_upd_mem_dom_iff) |
   smt ml=0 w=(lazy_invar_upd2_vb) |
   smt ml=0 w=(lazy_invar_upd_lu_eq)].
auto; progress; smt ml=0.
auto.
qed.

pred EagerInvar
     (mp1 : (block list * int, block) fmap,
      mp2 : (block list * int, bool) fmap) =
  (forall (xs : block list, i : int),
   mem (dom mp1) (xs, i) =>
   0 <= i /\
   (forall (j : int), 0 <= j < i => mem (dom mp1) (xs, j)) /\
   (forall (j : int), i * r <= j < (i + 1) * r =>
    mp2.[(xs, j)] = Some(nth false (w2bits(oget mp1.[(xs, i)])) j))) /\
  (forall (xs : block list, j : int),
   mem (dom mp2) (xs, j) =>
   0 <= j /\ mem (dom mp1) (xs, j %/ r)).

lemma HybridIROEager_f_g :
  equiv[HybridIROEager.f ~ HybridIROEager.g :
        ={xs, HybridIROEager.mp} /\ n{1} * r = n{2} ==>
        res{1} = bits2blocks res{2} /\ ={HybridIROEager.mp}].
proof.
proc=> /=; inline *.
seq 5 3 :
  (={i, HybridIROEager.mp} /\ xs0{1} = xs{2} /\
   bs0{1} = bs{2} /\ n0{1} = n{2} /\ m{1} = n0{1} /\ m{2} = n{2}).
auto; progress;
  first 2 rewrite -addzA divzMDl 1:gtr_eqF 1:gt0_r // divz_small //;
          smt ml=0 w=(gt0_n).
if=> //; wp.
while
  (={i, HybridIROEager.mp} /\ xs0{1} = xs{2} /\
   bs0{1} = bs{2} /\ n0{1} = n{2} /\ m{1} = n0{1} /\
   m{2} = n{2}).
sp; wp; if=> //; rnd; auto.
while
  (={i, HybridIROEager.mp} /\ xs0{1} = xs{2} /\
   bs0{1} = bs{2} /\ n0{1} = n{2} /\ m{1} = n0{1} /\
   m{2} = n{2})=> //.
sp; wp; if=> //; rnd; auto.
auto.
qed.

lemma HybridIROEager_g_BlockIRO_f (n' : int) (x' : block list) :
  equiv[HybridIROEager.g ~ BlockSponge.BIRO.IRO.f :
        n' = n{1} /\ xs{1} = x{2} /\ x' = x{2} /\
        n{2} = (n{1} + r - 1) %/ r /\
        EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
        EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} /\
        (valid_block x' =>
         res{1} = take n' (blocks2bits res{2}) /\
         size res{2} = (n' + r - 1) %/ r) /\
        (! valid_block x' => res{1} = [] /\ res{2} = [])].
proof.
proc=> /=.
seq 3 2 :
  (n' = n{1} /\ xs{1} = x{2} /\ x' = x{2} /\
   n{2} = (n{1} + r - 1) %/ r /\ n{2} * r = m{1} /\
   i{1} = 0 /\ i{2} = 0 /\ bs{1} = [] /\ bs{2} = [] /\
  EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
auto; progress.
if=> //.
conseq
  (_ :
   xs{1} = x{2} /\ n' = n{1} /\ n{2} = (n{1} + r - 1) %/ r /\
   n{2} * r = m{1} /\ n{1} <= m{1} /\
   i{1} = 0 /\ i{2} = 0 /\ bs{1} = [] /\ bs{2} = [] /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
   bs{1} = take n' (blocks2bits bs{2}) /\
   size bs{2} = (n' + r - 1) %/ r /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})=> //.
progress; apply/needed_blocks_suff.
admit.   
qed.

lemma HybridIROEager_BlockIRO_f :
  equiv[HybridIROEager.f ~ BlockSponge.BIRO.IRO.f :
        xs{1} = x{2} /\ ={n} /\
        EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
        ={res} /\ EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}].
proof.
transitivity
  HybridIROEager.g
  (={xs, HybridIROEager.mp} /\ n{2} = n{1} * r /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
   res{1} = bits2blocks res{2} /\ ={HybridIROEager.mp})
  (xs{1} = x{2} /\ n{1} = n{2} * r /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
   res{1} = (blocks2bits res{2}) /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
progress.
exists BlockSponge.BIRO.IRO.mp{2}, HybridIROEager.mp{1}, (xs{1}, n{1} * r).
  progress; by rewrite H0.
progress; apply blocks2bitsK.
conseq HybridIROEager_f_g.
progress; by rewrite H0.
exists* n{1}; elim*=> n1. exists* xs{1}; elim*=> xs'.
conseq (HybridIROEager_g_BlockIRO_f n1 xs')=> //.
progress; rewrite H0; by rewrite needed_blocks_prod_r.
progress.
case (valid_block xs{1})=> [vb_xs1 | not_vb_xs1].
have [-> size_result_R] := H3 vb_xs1.
have -> : n{1} = size(blocks2bits result_R)
  by rewrite size_blocks2bits size_result_R H0
             needed_blocks_prod_r mulzC.
by rewrite take_size.
by have [->->] := H4 not_vb_xs1.
qed.

end HybridIRO.

section.

declare module BlockSim : BlockSponge.SIMULATOR{IRO, BlockSponge.BIRO.IRO}.
declare module Dist : DISTINGUISHER{Perm, BlockSim, IRO, BlockSponge.BIRO.IRO}.

local clone import HybridIRO as HIRO.

local lemma RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f :
  equiv[RaiseHybridIRO(HybridIROEager).f ~ RaiseFun(BlockSponge.BIRO.IRO).f :
  ={bs, n} /\ ={glob BlockSim} /\
  EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
  ={res} /\ ={glob BlockSim} /\
  EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}].
proof.
proc=> /=.
exists* n{1}; elim*=> n'.
exists* (pad2blocks bs{2}); elim*=> xs2.
call (HybridIROEager_g_BlockIRO_f n' xs2).
auto; progress.
by have [-> _] := H2 _; first apply/valid_pad2blocks.
qed.

local lemma Sponge_Raise_BlockSponge_f :
  equiv[Sponge(Perm).f ~ RaiseFun(BlockSponge.Sponge(Perm)).f :
        ={bs, n, glob Perm} ==> ={res, glob Perm}].
proof.
proc; inline BlockSponge.Sponge(Perm).f.
conseq (_ : ={bs, n, glob Perm} ==> _)=> //.
swap{2} [3..5] -2.
seq 4 4 :
  (={n, glob Perm, sa, sc, i} /\ xs{1} = xs0{2} /\ z{1} = [] /\ z{2} = [] /\
   valid_block xs0{2}).
auto; progress; apply valid_pad2blocks.
rcondt{2} 2; auto.
swap{2} 1 1.
seq 1 1 : 
  (={n, glob Perm, sa, sc, i} /\ xs{1} = xs0{2} /\ z{1} = [] /\ z{2} = []).
while (={glob Perm, sa, sc, i} /\ xs{1} = xs0{2} /\ z{1} = [] /\ z{2} = []).
wp. call (_ : ={glob Perm}). sim. auto. auto.
seq 0 1 : 
  (={n, glob Perm, sa, sc, i} /\ blocks2bits z{2} = z{1} /\
   n0{2} = (n{1} + r - 1) %/ r); first auto.
while (={n, glob Perm, i, sa, sc} /\ blocks2bits z{2} = z{1} /\
       n0{2} = (n{1} + r - 1) %/ r).
wp. call (_ : ={glob Perm}); first sim. auto.
auto; progress; by rewrite -cats1 blocks2bits_cat blocks2bits_sing.
auto.
qed.

local lemma RealIndif_Sponge_BlockSponge &m :
  Pr[RealIndif(Sponge, Perm, Dist).main() @ &m: res] =
  Pr[BlockSponge.RealIndif
     (BlockSponge.Sponge, Perm, LowerDist(Dist)).main() @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 : (={glob Dist, glob Perm}); first sim.
call (_ : ={glob Perm}); first 2 sim.
conseq Sponge_Raise_BlockSponge_f=> //.
auto.
qed.

local lemma Ideal_IRO_Experiment_HybridLazy &m :
  Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res] =
  Pr[Experiment
     (RaiseHybridIRO(HybridIROLazy), BlockSim(HybridIROLazy),
      Dist).main() @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 :
  (={glob Dist, glob BlockSim} /\ IRO.mp{1} = NewFMap.map0 /\
   HybridIROLazy.mp{2} = NewFMap.map0).
inline *; wp; call (_ : true); auto.
call
  (_ :
  ={glob Dist, glob BlockSim} /\
  IRO.mp{1} = map0 /\ HybridIROLazy.mp{2} = map0 ==>
  ={res}).
proc (={glob BlockSim} /\ LazyInvar IRO.mp{1} HybridIROLazy.mp{2}).
progress; rewrite dom0 in_fset0 in H; elim H.
trivial.
proc (LazyInvar IRO.mp{1} HybridIROLazy.mp{2})=> //.
apply LowerFun_IRO_HybridIROLazy_f.
proc (LazyInvar IRO.mp{1} HybridIROLazy.mp{2})=> //.
apply LowerFun_IRO_HybridIROLazy_f.
by conseq IRO_RaiseHybridIRO_HybridIROLazy_f.
auto.
qed.

local module HybridIRODist(HI : HYBRID_IRO) : HYBRID_IRO_DIST (HI) = {

  proc distinguish() : bool = {
    var b : bool;
    b <@ Experiment(RaiseHybridIRO(HI), BlockSim(HI), Dist).main();
    return b;
  }
}.

local lemma Experiment_Hybrid_Lazy_Eager &m :
  Pr[Experiment
     (RaiseHybridIRO(HybridIROLazy), BlockSim(HybridIROLazy),
      Dist).main() @ &m : res] =
  Pr[Experiment
     (RaiseHybridIRO(HybridIROEager), BlockSim(HybridIROEager),
      Dist).main() @ &m : res].
proof.
have -> :
  Pr[Experiment
     (RaiseHybridIRO(HybridIROLazy), BlockSim(HybridIROLazy),
      Dist).main() @ &m : res] =
  Pr[HybridIRODist(HybridIROLazy).distinguish() @ &m : res].
  byequiv=> //; proc; inline *; sim.
rewrite (HybridIROLazyEager(HybridIRODist) &m).
have -> :
  Pr[HybridIRODist(HybridIROEager).distinguish() @ &m : res] =
  Pr[Experiment
     (RaiseHybridIRO(HybridIROEager), BlockSim(HybridIROEager),
      Dist).main() @ &m : res].
  byequiv=> //; proc; inline *; sim.
done.
qed.

local lemma Experiment_HybridEager_Ideal_BlockIRO &m :
  Pr[Experiment
     (RaiseHybridIRO(HybridIROEager), BlockSim(HybridIROEager),
      Dist).main() @ &m : res] =
  Pr[BlockSponge.IdealIndif
     (BlockSponge.BIRO.IRO, BlockSim, LowerDist(Dist)).main () @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 :
  (={glob Dist, glob BlockSim} /\ HybridIROEager.mp{1} = NewFMap.map0 /\
   BlockSponge.BIRO.IRO.mp{2} = NewFMap.map0).
inline *; wp; call (_ : true); auto.
call
  (_ :
  ={glob Dist, glob BlockSim} /\
  HybridIROEager.mp{1} = map0 /\ BlockSponge.BIRO.IRO.mp{2} = map0 ==>
  ={res}).
proc
  (={glob BlockSim} /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}) => //.
progress; rewrite dom0 in_fset0 in H; elim H.
proc (EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})=> //;
  conseq HybridIROEager_BlockIRO_f=> //.
proc (EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})=> //;
  conseq HybridIROEager_BlockIRO_f=> //.
exists* n{1}; elim *=> n'.
conseq RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f=> //.
auto.
qed.

local lemma IdealIndif_IRO_BlockIRO &m :
  Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res] =
  Pr[BlockSponge.IdealIndif
     (BlockSponge.BIRO.IRO, BlockSim, LowerDist(Dist)).main () @ &m : res].
proof.
by rewrite (Ideal_IRO_Experiment_HybridLazy &m)
           (Experiment_Hybrid_Lazy_Eager &m)
           (Experiment_HybridEager_Ideal_BlockIRO &m).
qed.

lemma Conclusion' &m :
  `|Pr[RealIndif(Sponge, Perm, Dist).main() @ &m: res] -
    Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res]| =
  `|Pr[BlockSponge.RealIndif
       (BlockSponge.Sponge, Perm, LowerDist(Dist)).main() @ &m : res] -
    Pr[BlockSponge.IdealIndif
       (BlockSponge.BIRO.IRO, BlockSim, LowerDist(Dist)).main() @ &m : res]|.
proof.
by rewrite (RealIndif_Sponge_BlockSponge &m) (IdealIndif_IRO_BlockIRO &m).
qed.

end section.

(*----------------------------- Conclusion -----------------------------*)

lemma Conclusion (BlockSim <: BlockSponge.SIMULATOR{IRO, BlockSponge.BIRO.IRO})
                 (Dist <: DISTINGUISHER{Perm, BlockSim, IRO, BlockSponge.BIRO.IRO})
                 &m :
  `|Pr[RealIndif(Sponge, Perm, Dist).main() @ &m: res] -
    Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res]| =
  `|Pr[BlockSponge.RealIndif
       (BlockSponge.Sponge, Perm, LowerDist(Dist)).main() @ &m : res] -
    Pr[BlockSponge.IdealIndif
       (BlockSponge.BIRO.IRO, BlockSim, LowerDist(Dist)).main() @ &m : res]|.
proof. by apply/(Conclusion' BlockSim Dist &m). qed.
