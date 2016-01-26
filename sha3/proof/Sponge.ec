(*------------------------- Sponge Construction ------------------------*)

require import Fun Pair Int IntDiv Real List Option FSet NewFMap DBool.
require import Common StdOrder. import IntOrder.
require (*--*) IRO BlockSponge.

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

section.

declare module BlockSim  : BlockSponge.SIMULATOR{IRO, BlockSponge.BIRO.IRO}.
declare module Dist : DISTINGUISHER{Perm, BlockSim, IRO, BlockSponge.BIRO.IRO}.

module type BLOCK_IRO_BITS = {
  proc init() : unit
  proc g(x : block list, n : int) : bool list
  proc f(x : block list, n : int) : block list
}.

module type BLOCK_IRO_BITS_DIST(BIROB : BLOCK_IRO_BITS) = {
  proc distinguish(): bool {BIROB.g BIROB.f}
}.

local module BlockIROBitsEager : BLOCK_IRO_BITS, BlockSponge.BIRO.IRO = {
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

local module BlockIROBitsLazy : BLOCK_IRO_BITS, BlockSponge.BIRO.IRO = {
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

local lemma BlockIROBitsEager (D <: BLOCK_IRO_BITS_DIST) :
  equiv[D(BlockIROBitsEager).distinguish ~ D(BlockIROBitsLazy).distinguish : 
        ={glob D} /\ BlockIROBitsEager.mp{1} = BlockIROBitsLazy.mp{2} ==>
        ={glob D}].
proof.
admit. (* use RndO.ec result *)
qed.

local module RaiseBIROBLazy (F : BLOCK_IRO_BITS) : FUNCTIONALITY = {
  proc init() = {
    F.init();
  }

  proc f(bs : bool list, n : int) = {
    var cs;

    cs <@ F.g(pad2blocks bs, n);
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

local lemma lazy_invar_upd_mem_dom_iff
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

local lemma lazy_invar_upd2_vb
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

local lemma lazy_invar_upd_lu_eq
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

local lemma LowerFun_IRO_BlockIROBitsLazy_f :
  equiv[LowerFun(IRO).f ~ BlockIROBitsLazy.f :
        ={xs, n} /\ LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2} ==>
        ={res} /\ LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2}].
proof.
proc=> /=; inline BlockIROBitsLazy.g.
seq 0 1 :
  (={n} /\ xs{1} = xs0{2} /\
   LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2}); first auto.
case (valid_block xs{1}).
rcondt{1} 3; first auto. rcondt{2} 4; first auto.
inline *. rcondt{1} 7; first auto.
seq 6 3 : 
  (={i, n0} /\ bs{1} = bs0{2} /\
   LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2} /\
   pad2blocks x{1} = xs0{2}).
auto; progress; have {2}<- /# := unpadBlocksK xs0{2}.
wp.
while
  (={i, n0} /\ bs{1} = bs0{2} /\
   LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2} /\
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

local lemma IRO_RaiseBIROBLazy_BlockIROBitsLazy_f :
  equiv[IRO.f ~ RaiseBIROBLazy(BlockIROBitsLazy).f :
        ={n} /\ x{1} = bs{2} /\
        LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2} ==>
        ={res} /\ LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2}].
proof.
proc=> /=; inline *.
rcondt{1} 3; first auto.
rcondt{2} 5; first auto; progress; apply valid_pad2blocks.
seq 2 4 :
  (={i, n} /\ n{1} = n0{2} /\ xs{2} = pad2blocks x{1} /\ bs{1} = bs0{2} /\
   LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2}); first auto.
wp.
while
  (={i, n} /\ n{1} = n0{2} /\ xs{2} = pad2blocks x{1} /\ bs{1} = bs0{2} /\
   LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2}).
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

local lemma BlockIROBitsEager_f_BlockIRO_g :
  equiv[BlockIROBitsEager.f ~ BlockIROBitsEager.g :
        ={xs, BlockIROBitsEager.mp} /\ n{1} * r = n{2} ==>
        res{1} = bits2blocks res{2} /\ ={BlockIROBitsEager.mp}].
proof.
proc=> /=; inline *.
seq 5 3 :
  (={i, BlockIROBitsEager.mp} /\ xs0{1} = xs{2} /\
   bs0{1} = bs{2} /\ n0{1} = n{2} /\ m{1} = n0{1} /\ m{2} = n{2}).
auto; progress;
  first 2 rewrite -addzA divzMDl 1:gtr_eqF 1:gt0_r // divz_small //;
          smt ml=0 w=(gt0_n).
if=> //; wp.
while
  (={i, BlockIROBitsEager.mp} /\ xs0{1} = xs{2} /\
   bs0{1} = bs{2} /\ n0{1} = n{2} /\ m{1} = n0{1} /\
   m{2} = n{2}).
sp; wp; if=> //; rnd; auto.
while
  (={i, BlockIROBitsEager.mp} /\ xs0{1} = xs{2} /\
   bs0{1} = bs{2} /\ n0{1} = n{2} /\ m{1} = n0{1} /\
   m{2} = n{2})=> //.
sp; wp; if=> //; rnd; auto.
auto.
qed.

local lemma BlockIROBitsEager_g_Block_IRO_f
            (n' : int) (x' : block list) :
  equiv[BlockIROBitsEager.g ~ BlockSponge.BIRO.IRO.f :
        n' = n{1} /\ xs{1} = x{2} /\ x' = x{2} /\
        n{2} = (n{1} + r - 1) %/ r /\
        EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1} ==>
        EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1} /\
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
  EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1}).
auto; progress.
if=> //.
conseq
  (_ :
   xs{1} = x{2} /\ n' = n{1} /\ n{2} = (n{1} + r - 1) %/ r /\
   n{2} * r = m{1} /\ n{1} <= m{1} /\
   i{1} = 0 /\ i{2} = 0 /\ bs{1} = [] /\ bs{2} = [] /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1} ==>
   bs{1} = take n' (blocks2bits bs{2}) /\
   size bs{2} = (n' + r - 1) %/ r /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1})=> //.
progress; apply/needed_blocks_suff.
admit.   
qed.

local lemma BlockIROBitsEager_BlockIRO_f :
  equiv[BlockIROBitsEager.f ~ BlockSponge.BIRO.IRO.f :
        xs{1} = x{2} /\ ={n} /\
        EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1} ==>
        ={res} /\ EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1}].
proof.
transitivity
  BlockIROBitsEager.g
  (={xs, BlockIROBitsEager.mp} /\ n{2} = n{1} * r /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1} ==>
   res{1} = bits2blocks res{2} /\ ={BlockIROBitsEager.mp})
  (xs{1} = x{2} /\ n{1} = n{2} * r /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1} ==>
   res{1} = (blocks2bits res{2}) /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1}).
progress.
exists BlockSponge.BIRO.IRO.mp{2}, BlockIROBitsEager.mp{1}, (xs{1}, n{1} * r).
  progress; by rewrite H0.
progress; apply blocks2bitsK.
conseq BlockIROBitsEager_f_BlockIRO_g.
progress; by rewrite H0.
exists* n{1}; elim*=> n1. exists* xs{1}; elim*=> xs'.
conseq (BlockIROBitsEager_g_Block_IRO_f n1 xs')=> //.
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

local lemma RaiseBIROBLazy_BlockIROBitsEager_RaiseFun_Block_IRO_f :
  equiv[RaiseBIROBLazy(BlockIROBitsEager).f ~ RaiseFun(BlockSponge.BIRO.IRO).f :
  ={bs, n} /\ ={glob BlockSim} /\
  EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1} ==>
  ={res} /\ ={glob BlockSim} /\
  EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1}].
proof.
proc=> /=.
exists* n{1}; elim*=> n'.
exists* (pad2blocks bs{2}); elim*=> xs2.
call (BlockIROBitsEager_g_Block_IRO_f n' xs2).
auto; progress.
by have [-> _] := H2 _; first apply/valid_pad2blocks.
qed.

local lemma Sponge_Raise_Block_Sponge_f :
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

local lemma RealIndif &m :
  Pr[RealIndif(Sponge, Perm, Dist).main() @ &m: res] =
  Pr[BlockSponge.RealIndif
     (BlockSponge.Sponge, Perm, LowerDist(Dist)).main() @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 : (={glob Dist, glob Perm}); first sim.
call (_ : ={glob Perm}); first 2 sim.
conseq Sponge_Raise_Block_Sponge_f=> //.
auto.
qed.

local lemma IdealIndifIROLazy &m :
  Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res] =
  Pr[Experiment
     (RaiseBIROBLazy(BlockIROBitsLazy), BlockSim(BlockIROBitsLazy),
      Dist).main() @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 :
  (={glob Dist, glob BlockSim} /\ IRO.mp{1} = NewFMap.map0 /\
   BlockIROBitsLazy.mp{2} = NewFMap.map0).
inline *; wp; call (_ : true); auto.
call
  (_ :
  ={glob Dist, glob BlockSim} /\
  IRO.mp{1} = map0 /\ BlockIROBitsLazy.mp{2} = map0 ==>
  ={res}).
proc (={glob BlockSim} /\ LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2}).
progress; rewrite dom0 in_fset0 in H; elim H.
trivial.
proc (LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2})=> //.
apply LowerFun_IRO_BlockIROBitsLazy_f.
proc (LazyInvar IRO.mp{1} BlockIROBitsLazy.mp{2})=> //.
apply LowerFun_IRO_BlockIROBitsLazy_f.
by conseq IRO_RaiseBIROBLazy_BlockIROBitsLazy_f.
auto.
qed.

local lemma IdealIndifLazy &m :
  Pr[Experiment
     (RaiseBIROBLazy(BlockIROBitsLazy), BlockSim(BlockIROBitsLazy),
      Dist).main() @ &m : res] =
  Pr[Experiment
     (RaiseBIROBLazy(BlockIROBitsEager), BlockSim(BlockIROBitsEager),
      Dist).main() @ &m : res].
proof.
(* reduction to eager *)
admit.
qed.

local lemma IdealIndifEager &m :
  Pr[Experiment
     (RaiseBIROBLazy(BlockIROBitsEager), BlockSim(BlockIROBitsEager),
      Dist).main() @ &m : res] =
  Pr[BlockSponge.IdealIndif
     (BlockSponge.BIRO.IRO, BlockSim, LowerDist(Dist)).main () @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 :
  (={glob Dist, glob BlockSim} /\ BlockIROBitsEager.mp{1} = NewFMap.map0 /\
   BlockSponge.BIRO.IRO.mp{2} = NewFMap.map0).
inline *; wp; call (_ : true); auto.
call
  (_ :
  ={glob Dist, glob BlockSim} /\
  BlockIROBitsEager.mp{1} = map0 /\ BlockSponge.BIRO.IRO.mp{2} = map0 ==>
  ={res}).
proc
  (={glob BlockSim} /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1}) => //.
progress; rewrite dom0 in_fset0 in H; elim H.

proc (EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1})=> //;
  conseq BlockIROBitsEager_BlockIRO_f=> //.
proc (EagerInvar BlockSponge.BIRO.IRO.mp{2} BlockIROBitsEager.mp{1})=> //;
  conseq BlockIROBitsEager_BlockIRO_f=> //.
exists* n{1}; elim *=> n'.
conseq RaiseBIROBLazy_BlockIROBitsEager_RaiseFun_Block_IRO_f=> //.
auto.
qed.

local lemma IdealIndif &m :
  Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res] =
  Pr[BlockSponge.IdealIndif
     (BlockSponge.BIRO.IRO, BlockSim, LowerDist(Dist)).main () @ &m : res].
proof.
by rewrite (IdealIndifIROLazy &m) (IdealIndifLazy &m) (IdealIndifEager &m).
qed.

lemma Conclusion' &m :
  `|Pr[RealIndif(Sponge, Perm, Dist).main() @ &m: res] -
    Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res]| =
  `|Pr[BlockSponge.RealIndif
       (BlockSponge.Sponge, Perm, LowerDist(Dist)).main() @ &m : res] -
    Pr[BlockSponge.IdealIndif
       (BlockSponge.BIRO.IRO, BlockSim, LowerDist(Dist)).main() @ &m : res]|.
proof.
by rewrite (RealIndif &m) (IdealIndif &m).
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
