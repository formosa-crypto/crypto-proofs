(*------------------------- Sponge Construction ------------------------*)
(* checks with both Alt-Ergo and Z3 *)

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

module (Sponge : CONSTRUCTION) (P : DPRIMITIVE) : FUNCTIONALITY = {
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
      z        <- z ++ ofblock sa;
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

(*------------------- abstract theory of hybrid IROs -------------------*)

abstract theory HybridIRO.

module type HYBRID_IRO = {
  proc init() : unit
  proc g(x : block list, n : int) : bool list
  proc f(x : block list, n : int) : block list
}.

module type HYBRID_IRO_DIST(HI : HYBRID_IRO) = {
  proc distinguish() : bool
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

module HybridIROExper(HI : HYBRID_IRO, D : HYBRID_IRO_DIST) = {
  proc main() : bool = {
    var b : bool;
    HI.init();
    b <@ D(HI).distinguish();
    return b;
  }
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

section.

declare module D : HYBRID_IRO_DIST{HybridIROEager, HybridIROLazy}.

local clone RndO.GenEager as ERO with
  type from   <- block list * int,
  type to     <- bool,
  op sampleto <- fun _ => dbool.

local module EROExper(O : ERO.RO, D : ERO.RO_Distinguisher) = {
  proc main() : bool = {
    var b : bool;
    O.init();
    b <@ D(O).distinguish();
    return b;
  }
}.

local lemma LRO_RO (D <: ERO.RO_Distinguisher{ERO.RO, ERO.FRO}) &m :
  Pr[EROExper(ERO.LRO, D).main() @ &m : res] =
  Pr[EROExper(ERO.RO, D).main() @ &m : res].
proof.
byequiv=> //; proc.
seq 1 1 : (={glob D, ERO.RO.m}); first sim.
symmetry; call (ERO.RO_LRO_D D); auto.
qed.

local module HIRO(RO : ERO.RO) = {
  proc init() : unit = {
      RO.init();
  }

  proc g(xs, n) = {
    var b, bs;
    var m <- ((n + r - 1) %/ r) * r;
    var i <- 0;

    bs <- [];
    if (valid_block xs) {
      while (i < n) {
        b <@ RO.get(xs, i);
        bs <- rcons bs b;
        i <- i + 1;
      }
      while (i < m) {
        RO.sample(xs, i);
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

local lemma HybridIROLazy_fill_in_LRO_get :
  equiv[HybridIROLazy.fill_in ~ ERO.LRO.get :
        (xs, i){1} = x{2} /\ HybridIROLazy.mp{1} = ERO.RO.m{2} ==>
        ={res} /\ HybridIROLazy.mp{1} = ERO.RO.m{2}].
proof.
proc=> /=.
case: (mem (dom HybridIROLazy.mp{1}) (xs{1}, i{1})).
rcondf{1} 1; first auto. rcondf{2} 2; first auto.
rnd{2}; auto; progress; apply/dbool_ll.
rcondt{1} 1; first auto. rcondt{2} 2; first auto.
wp; rnd; auto.
qed.

local lemma HybridIROLazy_HIRO_LRO_init :
  equiv[HybridIROLazy.init ~ HIRO(ERO.LRO).init :
        true ==> HybridIROLazy.mp{1} = ERO.RO.m{2}].
proof. proc; inline*; auto. qed.

local lemma HybridIROLazy_HIRO_LRO_g :
  equiv[HybridIROLazy.g ~ HIRO(ERO.LRO).g :
        ={xs, n} /\ HybridIROLazy.mp{1} = ERO.RO.m{2} ==>
        ={res} /\ HybridIROLazy.mp{1} = ERO.RO.m{2}].
proof.
proc; inline ERO.LRO.sample; sp=> /=.
if=> //.
while{2} (true) (m{2} - i{2}).
progress; auto; progress; smt().
while (={xs, n, i, bs} /\ HybridIROLazy.mp{1} = ERO.RO.m{2}).
wp; call HybridIROLazy_fill_in_LRO_get; auto.
auto; progress; smt().
qed.

local lemma HybridIROLazy_HIRO_LRO_f :
  equiv[HybridIROLazy.f ~ HIRO(ERO.LRO).f :
        ={xs, n} /\ HybridIROLazy.mp{1} = ERO.RO.m{2} ==>
        ={res} /\ HybridIROLazy.mp{1} = ERO.RO.m{2}].
proof.
proc; wp; call HybridIROLazy_HIRO_LRO_g; auto.
qed.

local lemma RO_get_HybridIROEager_fill_in :
  equiv[ERO.RO.get ~ HybridIROEager.fill_in :
        x{1} = (xs, i){2} /\ ERO.RO.m{1} = HybridIROEager.mp{2} ==>
        ={res} /\ ERO.RO.m{1} = HybridIROEager.mp{2}].
proof.
proc=> /=.
case: (mem (dom HybridIROEager.mp{2}) (xs{2}, i{2})).
rcondf{1} 2; first auto. rcondf{2} 1; first auto.
rnd{1}; auto; progress; apply/dbool_ll.
rcondt{1} 2; first auto. rcondt{2} 1; first auto.
wp; rnd; auto.
qed.

local lemma RO_sample_HybridIROEager_fill_in :
  equiv[ERO.RO.sample ~ HybridIROEager.fill_in :
        x{1} = (xs, i){2} /\ ERO.RO.m{1} = HybridIROEager.mp{2} ==>
         ERO.RO.m{1} = HybridIROEager.mp{2}].
proof.
proc=> /=; inline ERO.RO.get; sp.
case: (mem (dom HybridIROEager.mp{2}) (xs{2}, i{2})).
rcondf{1} 2; first auto. rcondf{2} 1; first auto.
rnd{1}; auto; progress; apply/dbool_ll.
rcondt{1} 2; first auto. rcondt{2} 1; first auto.
wp; rnd; auto.
qed.

local lemma HIRO_RO_HybridIROEager_init :
  equiv[HIRO(ERO.RO).init ~ HybridIROEager.init :
        true ==> ={res} /\ ERO.RO.m{1} = HybridIROEager.mp{2}].
proof. proc; inline*; auto. qed.

local lemma HIRO_RO_HybridIROEager_g :
  equiv[HIRO(ERO.RO).g ~ HybridIROEager.g :
        ={xs, n} /\ ERO.RO.m{1} = HybridIROEager.mp{2} ==>
        ={res} /\ ERO.RO.m{1} = HybridIROEager.mp{2}].
proof.
proc; first sp=> /=.
if=> //.
while (={i, m, xs} /\ ERO.RO.m{1} = HybridIROEager.mp{2}).
wp; call RO_sample_HybridIROEager_fill_in; auto.
while (={i, n, xs, bs} /\ ERO.RO.m{1} = HybridIROEager.mp{2}).
wp; call RO_get_HybridIROEager_fill_in; auto.
auto.
qed.

local lemma HIRO_RO_HybridIROEager_f :
  equiv[HIRO(ERO.RO).f ~ HybridIROEager.f :
        ={xs, n} /\ ERO.RO.m{1} = HybridIROEager.mp{2} ==>
        ={res} /\ ERO.RO.m{1} = HybridIROEager.mp{2}].
proof.
proc; wp; call HIRO_RO_HybridIROEager_g; auto.
qed.

local module RODist(RO : ERO.RO) = {
  proc distinguish() : bool = {
    var b : bool;
    b <@ D(HIRO(RO)).distinguish();
    return b;
  }
}.

local lemma Exper_HybridLazy_ERO_LRO &m :
  Pr[HybridIROExper(HybridIROLazy, D).main() @ &m : res] =
  Pr[EROExper(ERO.LRO, RODist).main() @ &m : res].
proof.
byequiv=> //; proc; inline*; wp.
seq 1 1 : (={glob D} /\ HybridIROLazy.mp{1} = ERO.RO.m{2}); first auto.
call (_ : HybridIROLazy.mp{1} = ERO.RO.m{2}).
conseq HybridIROLazy_HIRO_LRO_init.
conseq HybridIROLazy_HIRO_LRO_g.
conseq HybridIROLazy_HIRO_LRO_f.
auto.
qed.

local lemma ERO_RO_Exper_HybridEager &m :
  Pr[EROExper(ERO.RO, RODist).main() @ &m : res] =
  Pr[HybridIROExper(HybridIROEager, D).main() @ &m : res].
proof.
byequiv=> //; proc; inline*; wp.
seq 1 1 : (={glob D} /\ ERO.RO.m{1} = HybridIROEager.mp{2}); first auto.
call (_ : ERO.RO.m{1} = HybridIROEager.mp{2}).
conseq HIRO_RO_HybridIROEager_init.
conseq HIRO_RO_HybridIROEager_g.
conseq HIRO_RO_HybridIROEager_f.
auto.
qed.

lemma HybridIROExper_Lazy_Eager &m :
  Pr[HybridIROExper(HybridIROLazy, D).main() @ &m : res] =
  Pr[HybridIROExper(HybridIROEager, D).main() @ &m : res].
proof.
by rewrite (Exper_HybridLazy_ERO_LRO &m)
           (LRO_RO RODist &m)
           (ERO_RO_Exper_HybridEager &m).
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

lemma lazy_invar0 : LazyInvar map0 map0.
proof.
split; first smt(in_fset0 dom0).
split; smt(in_fset0 dom0).
qed.

lemma lazy_invar_mem_pad2blocks_l2r
      (mp1 : (bool list * int, bool) fmap,
       mp2 : (block list * int, bool) fmap,
       bs : bool list, i : int) :
  LazyInvar mp1 mp2 => mem (dom mp1) (bs, i) =>
  mem (dom mp2) (pad2blocks bs, i).
proof. smt(). qed.

lemma lazy_invar_mem_pad2blocks_r2l
      (mp1 : (bool list * int, bool) fmap,
       mp2 : (block list * int, bool) fmap,
       bs : bool list, i : int) :
  LazyInvar mp1 mp2 => mem (dom mp2) (pad2blocks bs, i) =>
  mem (dom mp1) (bs, i).
proof. smt(). qed.

lemma lazy_invar_vb
      (mp1 : (bool list * int, bool) fmap,
       mp2 : (block list * int, bool) fmap,
       xs : block list, n : int) :
  LazyInvar mp1 mp2 => mem (dom mp2) (xs, n) =>
  valid_block xs.
proof. smt(). qed.

lemma lazy_invar_lookup_eq
      (mp1 : (bool list * int, bool) fmap,
       mp2 : (block list * int, bool) fmap,
       bs : bool list, n : int) :
  LazyInvar mp1 mp2 => mem (dom mp1) (bs, n) =>
  oget mp1.[(bs, n)] = oget mp2.[(pad2blocks bs, n)].
proof. smt(). qed.

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
left; smt().
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
smt(getP_eq).
rewrite domP in_fsetU1 in mem_upd_mp1.
elim mem_upd_mp1=> [mem_mp1 | [->->]].
case: ((pad2blocks bs, n) = (pad2blocks cs, m))=>
  [[p2b_bs_p2b_cs eq_mn] | p2b_bs_n_neq_p2b_cs_m].
smt(pad2blocks_inj).
smt(getP).
smt(getP).
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
inline*. rcondt{1} 7; first auto.
seq 6 3 : 
  (={i, n0} /\ bs{1} = bs0{2} /\
   LazyInvar IRO.mp{1} HybridIROLazy.mp{2} /\
   pad2blocks x{1} = xs0{2}).
auto; progress;
  have {2}<- := unpadBlocksK xs0{2}; first
  by rewrite (@some_oget (unpad_blocks xs0{2})).
wp.
while
  (={i, n0} /\ bs{1} = bs0{2} /\
   LazyInvar IRO.mp{1} HybridIROLazy.mp{2} /\
   pad2blocks x{1} = xs0{2}).
sp; auto.
if.
progress;
  [by apply (lazy_invar_mem_pad2blocks_l2r IRO.mp{1}
             HybridIROLazy.mp{2} x{1} i{2}) |
   by apply (lazy_invar_mem_pad2blocks_r2l IRO.mp{1}
             HybridIROLazy.mp{2} x{1} i{2})].
rnd; auto; progress;
  [by rewrite !getP_eq |
   by rewrite -(@lazy_invar_upd_mem_dom_iff IRO.mp{1}) |
   by rewrite (@lazy_invar_upd_mem_dom_iff IRO.mp{1} HybridIROLazy.mp{2}) |
   by rewrite (@lazy_invar_upd2_vb IRO.mp{1} HybridIROLazy.mp{2}
               x{1} xs2 i{2} n2 mpL) |
   by rewrite (@lazy_invar_upd_lu_eq IRO.mp{1} HybridIROLazy.mp{2})].
auto; progress [-delta].
by rewrite (lazy_invar_lookup_eq IRO.mp{1} HybridIROLazy.mp{2} x{1} i{2}).
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
proc=> /=; inline*.
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
progress;
  [by apply (lazy_invar_mem_pad2blocks_l2r IRO.mp{1}
             HybridIROLazy.mp{2} x{1} i{2}) |
   by apply (lazy_invar_mem_pad2blocks_r2l IRO.mp{1}
             HybridIROLazy.mp{2} x{1} i{2})].
rnd; auto; progress;
  [by rewrite !getP_eq |
   by rewrite -(@lazy_invar_upd_mem_dom_iff IRO.mp{1}) |
   by rewrite (@lazy_invar_upd_mem_dom_iff IRO.mp{1} HybridIROLazy.mp{2}) |
   by rewrite (@lazy_invar_upd2_vb IRO.mp{1} HybridIROLazy.mp{2}
               x{1} xs1 i{2} n1 mpL) |
   by rewrite (@lazy_invar_upd_lu_eq IRO.mp{1} HybridIROLazy.mp{2})].
auto; progress [-delta];
  by rewrite (lazy_invar_lookup_eq IRO.mp{1} HybridIROLazy.mp{2} x{1} i{2}).
auto.
qed.

pred EagerInvar
     (mp1 : (block list * int, block) fmap,
      mp2 : (block list * int, bool) fmap) =
  (forall (xs : block list, i : int),
   mem (dom mp1) (xs, i) =>
   0 <= i /\
   (forall (j : int), i * r <= j < (i + 1) * r =>
    mp2.[(xs, j)] = Some(nth false (ofblock (oget mp1.[(xs, i)])) j))) /\
  (forall (xs : block list, j : int),
   mem (dom mp2) (xs, j) => mem (dom mp1) (xs, j %/ r)).

pred BlockBitsAllInDom
     (xs : block list, i : int, mp : (block list * int, bool) fmap) =
  forall (j : int), i <= j < i + r => mem (dom mp) (xs, j).

pred BlockBitsAllOutDom
     (xs : block list, i : int, mp : (block list * int, bool) fmap) =
  forall (j : int), i <= j < i + r => ! mem (dom mp) (xs, j).

pred BlockBitsDomAllInOrOut
     (xs : block list, i : int, mp : (block list * int, bool) fmap) =
  BlockBitsAllInDom xs i mp \/ BlockBitsAllOutDom xs i mp.

lemma eager_inv_mem_mp1_ge0
      (mp1 : (block list * int, block) fmap,
       mp2 : (block list * int, bool) fmap,
       xs : block list, i : int) :
  EagerInvar mp1 mp2 => mem (dom mp1) (xs, i) => 0 <= i.
proof. move=> [ei1 ei2] mem_mp1_i; smt(). qed.

lemma eager_inv_mem_mp2_ge0
      (mp1 : (block list * int, block) fmap,
       mp2 : (block list * int, bool) fmap,
       xs : block list, j : int) :
  EagerInvar mp1 mp2 => mem (dom mp2) (xs, j) => 0 <= j.
proof.
move=> [ei1 ei2] mem_mp2_j.
have mem_mp1_j_div_r : mem (dom mp1) (xs, j %/ r) by smt().
have ge0_j_div_r : 0 <= j %/ r by smt().
smt(divz_ge0 gt0_r).
qed.

lemma eager_invar0 : EagerInvar map0 map0.
proof. split; smt(dom0 in_fset0). qed.

lemma eager_inv_imp_block_bits_dom
      (mp1 : (block list * int, block) fmap,
       mp2 : (block list * int, bool) fmap,
       xs : block list, i : int) :
  0 <= i => r %| i => EagerInvar mp1 mp2 =>
  BlockBitsDomAllInOrOut xs i mp2.
proof.
move=> ge0_i r_dvd_i [ei1 ei2].
case (mem (dom mp1) (xs, i %/ r))=> [mem_mp1 | not_mem_mp1].
have ei1_xs_i_div_r := ei1 xs (i %/ r).
have [_ mp2_eq_block_bits] := ei1_xs_i_div_r mem_mp1.
left=> j j_rng.
have mp2_eq_block_bits_j := mp2_eq_block_bits j _.
  by rewrite divzK // mulzDl /= divzK.
rewrite in_dom /#.
right=> j j_rng.
case (mem (dom mp2) (xs, j))=> // mem_mp2 /=.
have mem_mp1 := ei2 xs j mem_mp2.
have [k] [k_ran j_eq_i_plus_k] : exists k, 0 <= k < r /\ j = i + k
  by exists (j - i); smt().
have /# : (i + k) %/r = i %/ r
  by rewrite divzDl // (divz_small k r) 1:ger0_norm 1:ge0_r.
qed.

lemma eager_inv_mem_dom2
      (mp1 : (block list * int, block) fmap,
       mp2 : (block list * int, bool) fmap,
       xs : block list, i : int) :
   EagerInvar mp1 mp2 => mem (dom mp1) (xs, i) =>
   BlockBitsAllInDom xs (i * r) mp2.
proof.
move=> [ei1 _] mem j j_ran.
have [ge0_i eq_mp2_block_i] := ei1 xs i mem.
rewrite in_dom.
have /# := eq_mp2_block_i j _; smt().
qed.

lemma eager_inv_not_mem_dom2
      (mp1 : (block list * int, bool) fmap,
       mp2 : (block list * int, block) fmap,
       xs : block list, i : int) :
   EagerInvar mp2 mp1 => 0 <= i => ! mem (dom mp2) (xs, i) =>
   BlockBitsAllOutDom xs (i * r) mp1.
proof.
move=> [_ ei2] ge0_i not_mem_mp2_i j j_ran.
case (mem (dom mp1) (xs, j))=> // mem_mp1_j.
have mem_mp2_j_div_r := ei2 xs j mem_mp1_j.
have /# : j %/ r = i.
have [k] [k_ran ->] : exists k, 0 <= k < r /\ j = i * r + k
  by exists (j - i * r); smt().
by rewrite divzDl 1:dvdz_mull 1:dvdzz (divz_small k r)
           1:ger0_norm 1:ge0_r //= mulzK 1:gtr_eqF 1:gt0_r.
qed.

lemma block_bits_dom_first_in_imp_all_in
      (xs : block list, i : int, mp : (block list * int, bool) fmap) :
  BlockBitsDomAllInOrOut xs i mp => mem (dom mp) (xs, i) =>
  BlockBitsAllInDom xs i mp.
proof. smt(). qed.

lemma block_bits_dom_first_out_imp_all_out
      (xs : block list, i : int, mp : (block list * int, bool) fmap) :
  BlockBitsDomAllInOrOut xs i mp => ! mem (dom mp) (xs, i) =>
  BlockBitsAllOutDom xs i mp.
proof. smt(). qed.

lemma HybridIROEager_f_g :
  equiv[HybridIROEager.f ~ HybridIROEager.g :
        ={xs, HybridIROEager.mp} /\ n{1} * r = n{2} ==>
        res{1} = bits2blocks res{2} /\ ={HybridIROEager.mp}].
proof.
proc=> /=; inline*.
seq 5 3 :
  (={i, HybridIROEager.mp} /\ xs0{1} = xs{2} /\
   bs0{1} = bs{2} /\ n0{1} = n{2} /\ m{1} = n0{1} /\ m{2} = n{2}).
auto; progress; first 2 by rewrite needed_blocks_prod_r.
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

(* modules needed for applying transitivity tactic *)

module HybridIROEagerTrans = {
  (* from HybridIROEager; need copy for transitivity
     to work *)

  proc g(xs, n) = {
    var b, bs;
    var m <- ((n + r - 1) %/ r) * r;
    var i <- 0;

    bs <- [];
    if (valid_block xs) {
      while (i < n) {
        b <@ HybridIROEager.fill_in(xs, i);
        bs <- rcons bs b;
        i <- i + 1;
      }
      while (i < m) {
        HybridIROEager.fill_in(xs, i);
        i <- i + 1;
      }
    }
    return bs;
  }

  proc next_block(i, m : int, xs, bs) = {
    var b;

    while (i < m) {
      b <@ HybridIROEager.fill_in(xs, i);
      bs <- rcons bs b;
      i <- i + 1;
    }
    return (bs, i);
  }

  proc next_block_split(i, m : int, xs, bs) = {
    var b, i';

    (* assuming BlockBitsDomAllInOrOut xs i HybridIROEager.mp
       and m = i + r and size bs = i *)

    if (mem (dom HybridIROEager.mp) (xs, i)) {
      while (i < m) {
        b <- oget HybridIROEager.mp.[(xs, i)];
        bs <- rcons bs b;
        i <- i + 1;
      }
    } else {
      i' <- i;
      while (i < m) {
        b <$ dbool;
        bs <- rcons bs b;
        i <- i + 1;
      }
      i <- i';
      while (i < m) {
        HybridIROEager.mp.[(xs, i)] <- nth true bs i;
        i <- i + 1;
      }
    }
    return (bs, i);
  }
}.

pred eager_eq_except
     (xs : block list, i j : int,
      mp1 mp2 : (block list * int, bool) fmap) =
  forall (ys : block list, k : int),
  ys <> xs \/ k < i \/ j <= k => mp1.[(ys, k)] = mp2.[(ys, k)].

lemma eager_eq_except_upd1_eq_in
      (xs : block list, i j k : int, y : bool,
       mp1 mp2 : (block list * int, bool) fmap) :
  eager_eq_except xs i j mp1 mp2 => i <= k => k < j =>
  eager_eq_except xs i j mp1.[(xs, k) <- y] mp2.
proof.
move=> eee le_ik lt_kj ys l disj.
have ne : (xs, k) <> (ys, l) by smt().
smt(getP).
qed.

lemma eager_eq_except_upd2_eq_in
      (xs : block list, i j k : int, y : bool,
       mp1 mp2 : (block list * int, bool) fmap) :
  eager_eq_except xs i j mp1 mp2 => i <= k => k < j =>
  eager_eq_except xs i j mp1 mp2.[(xs, k) <- y].
proof.
move=> eee le_ik lt_kj ys l disj.
have ne : (xs, k) <> (ys, l) by smt().
smt(getP).
qed.

lemma eager_eq_except_maps_eq
      (xs : block list, i j : int, y : bool,
       mp1 mp2 : (block list * int, bool) fmap) :
  i <= j => eager_eq_except xs i j mp1 mp2 =>
  (forall (k : int),
   i <= k < j => mp1.[(xs, k)] = mp2.[(xs, k)]) =>
  mp1 = mp2.
proof.
move=> lt_ij eee ran_k.
apply fmapP=> p.
have [ys k] -> /# : exists ys k, p = (ys, k)
  by exists p.`1, p.`2; smt().
qed.

lemma HybridIROEagerTrans_next_block_split :
  equiv
  [HybridIROEagerTrans.next_block ~ HybridIROEagerTrans.next_block_split :
   ={i, m, xs, bs, HybridIROEager.mp} /\ m{1} = i{1} + r /\
   size bs{1} = i{1} /\
   BlockBitsDomAllInOrOut xs{1} i{1} HybridIROEager.mp{1} ==>
   ={res, HybridIROEager.mp}].
proof.
proc=> /=.
case (mem (dom HybridIROEager.mp{2}) (xs{2}, i{2})).
rcondt{2} 1; first auto.
conseq
  (_ :
   ={i, m, xs, bs, HybridIROEager.mp} /\ i{1} <= m{1} /\
   (forall (j : int),
    i{1} <= j < m{1} =>
    mem (dom HybridIROEager.mp{1}) (xs{1}, j)) ==>
   _).
progress; smt(gt0_r).
while 
  (={i, m, xs, bs, HybridIROEager.mp} /\ i{1} <= m{1} /\
   (forall (j : int),
    i{1} <= j < m{1} =>
    mem (dom HybridIROEager.mp{1}) (xs{1}, j))).
wp; inline*.
rcondf{1} 3; first auto; smt().
auto; smt().
auto.
rcondf{2} 1; first auto.
sp; exists* i{1}; elim*=> i''.
conseq
  (_ :
   ={i, m, xs, bs, HybridIROEager.mp} /\ i'' = i{1} /\
   i'' = i'{2} /\ i'' + r = m{1} /\ size bs{1} = i'' /\
   (forall (j : int),
    i{1} <= j < m{1} =>
    ! mem (dom HybridIROEager.mp{1}) (xs{1}, j)) ==>
   _).
progress; smt(gt0_r).
seq 1 1 :
  (={i, m, xs, bs} /\ i'{2} = i'' /\ i{1} = i'' + r /\
   size bs{1} = i'' + r /\ m{1} = i'' + r /\
   (forall (j : int),
    i'' <= j < i'' + r =>
    HybridIROEager.mp{1}.[(xs{1}, j)] = Some(nth true bs{1} j)) /\
   (forall (j : int),
    i'' <= j < i'' + 1 =>
    ! mem (dom HybridIROEager.mp{2}) (xs{1}, j)) /\
   eager_eq_except xs{1} i'' i{1} HybridIROEager.mp{1} HybridIROEager.mp{2}).
while
  (={i, m, xs, bs} /\ i'{2} = i'' /\ m{1} = i'' + r /\
   i'' <= i{1} <= i'' + r /\ size bs{1} = i{1} /\
   (forall (j : int),
    i'' <= j < i{1} =>
    HybridIROEager.mp{1}.[(xs{1}, j)] = Some(nth true bs{1} j)) /\
   (forall (j : int),
    i{1} <= j < i'' + r =>
    ! mem (dom HybridIROEager.mp{1}) (xs{1}, j)) /\
   (forall (j : int),
    i'' <= j < i'' + r =>
    ! mem (dom HybridIROEager.mp{2}) (xs{1}, j)) /\
   eager_eq_except xs{1} i'' (i'' + r) HybridIROEager.mp{1} HybridIROEager.mp{2}).
inline*; rcondt{1} 3; first auto; smt().
sp; wp; rnd; skip; progress.
by rewrite getP_eq oget_some.
smt(). smt(). smt(getP_eq size_rcons).
rewrite nth_rcons /=.
case (j = size bs{2})=> [-> /= | ne_j_size_bs].
by rewrite getP_eq oget_some.
have -> /= : j < size bs{2} by smt().
rewrite getP ne_j_size_bs /= /#.
rewrite domP in_fsetU1 /#.
by apply eager_eq_except_upd1_eq_in.
skip; progress; smt(gt0_r).
sp; elim*=> i_R.
conseq
  (_ :
   ={xs, bs, m} /\ i{2} = i'' /\ i{1} = i'' + r /\ m{1} = i'' + r /\
   size bs{1} = i'' + r /\
   (forall (j : int),
    i'' <= j < i'' + r =>
    HybridIROEager.mp{1}.[(xs{1}, j)] = Some (nth true bs{1} j)) /\
   eager_eq_except xs{1} i'' (i'' + r)
                   HybridIROEager.mp{1} HybridIROEager.mp{2} ==>
   _)=> //.
while{2}
  (={xs, bs, m} /\ i'' <= i{2} <= i'' + r /\ i{1} = i'' + r /\
   m{1} = i'' + r /\ size bs{1} = i'' + r /\
   (forall (j : int),
    i'' <= j < i{2} =>
    HybridIROEager.mp{1}.[(xs{1}, j)] = HybridIROEager.mp{2}.[(xs{1}, j)]) /\
   (forall (j : int),
    i{2} <= j < i'' + r =>
    HybridIROEager.mp{1}.[(xs{1}, j)] = Some (nth true bs{1} j)) /\
   eager_eq_except xs{1} i'' (i'' + r)
                   HybridIROEager.mp{1} HybridIROEager.mp{2})
  (m{2} - i{2}).
progress; auto; progress;
  [smt() | smt(gt0_r) | smt(getP) | smt() |
   by apply eager_eq_except_upd2_eq_in | smt()].
skip; progress;
  [smt(gt0_r) | smt() | smt() | smt() | smt(eager_eq_except_maps_eq)].
qed.

module BlockSpongeTrans = {
  (* from BlockSponge.BIRO.IRO; need copy for transitivity
     to work *)

  proc f(x, n) = {
    var b, bs;
    var i <- 0;

    bs <- [];
    if (valid_block x) {
      while (i < n) {
        b <@ BlockSponge.BIRO.IRO.fill_in(x, i);
        bs <- rcons bs b;
        i <- i + 1;
      }
    }

    return bs;
  }

  proc next_block(x, i, bs) = {
    var b;

    b <@ BlockSponge.BIRO.IRO.fill_in(x, i);
    bs <- rcons bs b;
    i <- i + 1;
    return (bs, i);
  }
}.

lemma HybridIROEager_next (i2 : int) :
  equiv
  [HybridIROEagerTrans.next_block ~ BlockSpongeTrans.next_block :
   i2 = i{2} /\ 0 <= i{2} /\ xs{1} = x{2} /\ i{1} = i{2} * r /\
   m{1} - i{1} = r /\ bs{1} = blocks2bits bs{2} /\ size bs{2} = i{2} /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
   res{1}.`1 = blocks2bits res{2}.`1 /\
   res{1}.`2 = res{2}.`2 * r /\ res{2}.`2 = i2 + 1 /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}].
proof.
transitivity
  HybridIROEagerTrans.next_block_split
  (={i, m, xs, bs, HybridIROEager.mp} /\ m{1} = i{1} + r /\
   size bs{1} = i{1} /\
   BlockBitsDomAllInOrOut xs{1} i{1} HybridIROEager.mp{1} ==>
   ={res, HybridIROEager.mp})
  (i2 = i{2} /\ 0 <= i{2} /\ xs{1} = x{2} /\ i{1} = i{2} * r /\
   m{1} - i{1} = r /\ size bs{1} = i{1} /\ bs{1} = blocks2bits bs{2} /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
   res{1}.`1 = blocks2bits res{2}.`1 /\
   res{1}.`2 = res{2}.`2 * r /\ res{2}.`2 = i2 + 1 /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
progress; exists HybridIROEager.mp{1}, (i{1}, m{1}, xs{1}, bs{1}).
progress. smt().
smt(size_blocks2bits).
apply
  (eager_inv_imp_block_bits_dom BlockSponge.BIRO.IRO.mp{2}
   HybridIROEager.mp{1} xs{1} i{1}).
smt(ge0_r).
rewrite H1; smt(dvdz_mulr dvdzz).
trivial.
smt(size_blocks2bits).
trivial.
apply HybridIROEagerTrans_next_block_split.
proc=> /=; inline*.
admit.
qed.

lemma HybridIROEager_g_BlockIRO_f (n1 : int) (x2 : block list) :
  equiv[HybridIROEager.g ~ BlockSponge.BIRO.IRO.f :
        n1 = n{1} /\ x2 = x{2} /\ xs{1} = x{2} /\ 
        n{2} = (n{1} + r - 1) %/ r /\
        EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
        EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} /\
        (valid_block x2 =>
           (n1 <= 0 => res{1} = [] /\ res{2} = []) /\
           (0 < n1 =>
              res{1} = take n1 (blocks2bits res{2}) /\
              size res{2} = (n1 + r - 1) %/ r)) /\
        (! valid_block x2 => res{1} = [] /\ res{2} = [])].
proof.
transitivity
  HybridIROEagerTrans.g
  (={n, xs, HybridIROEager.mp} ==> ={res, HybridIROEager.mp})
  (n1 = n{1} /\ x2 = x{2} /\ xs{1} = x{2} /\ 
   n{2} = (n{1} + r - 1) %/ r /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} /\
   (valid_block x2 =>
      (n1 <= 0 => res{1} = [] /\ res{2} = []) /\
      (0 < n1 =>
         res{1} = take n1 (blocks2bits res{2}) /\
         size res{2} = (n1 + r - 1) %/ r)) /\
   (! valid_block x2 => res{1} = [] /\ res{2} = []));
   [smt() | trivial | sim | idtac].
transitivity
  BlockSpongeTrans.f
  (n1 = n{1} /\ x2 = x{2} /\ xs{1} = x{2} /\ 
   n{2} = (n{1} + r - 1) %/ r /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} /\
   (valid_block x2 =>
      (n1 <= 0 => res{1} = [] /\ res{2} = []) /\
      (0 < n1 =>
         res{1} = take n1 (blocks2bits res{2}) /\
         size res{2} = (n1 + r - 1) %/ r)) /\
   (! valid_block x2 => res{1} = [] /\ res{2} = []))
  (={x, n, BlockSponge.BIRO.IRO.mp} ==> ={res, BlockSponge.BIRO.IRO.mp});
  last first; [sim | smt() | smt() | idtac].
proc=> /=.
seq 3 2 :
  (n1 = n{1} /\ xs{1} = x{2} /\ x2 = x{2} /\
   n{2} = (n{1} + r - 1) %/ r /\ n{2} * r = m{1} /\
   i{1} = 0 /\ i{2} = 0 /\ bs{1} = [] /\ bs{2} = [] /\
  EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
auto; progress.
if=> //.
case: (n1 < 0).
rcondf{1} 1; first auto; progress; smt().
rcondf{2} 1; first auto; progress;
  by rewrite -lezNgt needed_blocks_non_pos ltzW.
rcondf{1} 1; first auto; progress;
  by rewrite -lezNgt pmulr_lle0 1:gt0_r needed_blocks_non_pos ltzW.
auto; progress;
  [by rewrite blocks2bits_nil | by smt(needed_blocks0)].
(* 0 <= n1 *)
conseq
  (_ :
   xs{1} = x{2} /\ n1 = n{1} /\ 0 <= n1 /\ n{2} = (n{1} + r - 1) %/ r /\
   n{2} * r = m{1} /\ n{1} <= m{1} /\
   i{1} = 0 /\ i{2} = 0 /\ bs{1} = [] /\ bs{2} = [] /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
   bs{1} = take n1 (blocks2bits bs{2}) /\
   size bs{2} = (n1 + r - 1) %/ r /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
progress; [smt() | apply/needed_blocks_suff].
move=> |> &1 &2 ? ? ? mp1 mp2 bs ? ? ?;
  smt(size_eq0 needed_blocks0 take0).
splitwhile{1} 1 : i < (n1 %/ r) * r.
splitwhile{2} 1 : i < n1 %/ r.
seq 1 1 :
  (xs{1} = x{2} /\ n1 = n{1} /\ 0 <= n1 /\ n{2} = (n1 + r - 1) %/ r /\
   n{2} * r = m{1} /\ n{1} <= m{1} /\ i{1} = n1 %/ r * r /\
   i{2} = n1 %/ r /\ size bs{2} = i{2} /\ bs{1} = blocks2bits bs{2} /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
admit.
conseq
  (_ :
   n1 = n{1} /\ 0 <= n1 /\ xs{1} = x{2} /\ n{2} = (n1 + r - 1) %/ r /\
   n{2} * r = m{1} /\ n{1} <= m{1} /\ i{1} = n1 %/ r * r /\
   i{2} = n1 %/ r /\ size bs{2} = i{2} /\ bs{1} = blocks2bits bs{2} /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} /\
   (i{2} = n{2} \/ i{2} + 1 = n{2}) ==>
   bs{1} = take n1 (blocks2bits bs{2}) /\ size bs{2} = n{2} /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}) => //.
progress; by apply/needed_blocks_rel_div_r.
case: (i{2} = n{2}).
rcondf{2} 1; first auto; progress; smt().
rcondf{1} 1; first auto; progress; smt().
rcondf{1} 1; first auto; progress; smt().
auto=> |> &1 &2 ? ? sz_eq ? ? need_blks_eq.
split.
have -> : n{1} = size (blocks2bits bs{2})
  by rewrite size_blocks2bits sz_eq -mulzC divzK 1:needed_blocks_eq_div_r.
by rewrite take_size.
by rewrite sz_eq need_blks_eq.
(* i{2} <> n{2}, so i{2} + 1 = n{2} *)
rcondt{2} 1; first auto; progress; smt().
rcondf{2} 4; first auto; call (_ : true).
if=> //. auto; progress; smt().
conseq
  (_ :
   n1 = n{1} /\ 0 <= n1 /\ xs{1} = x{2} /\ 0 <= i{2} /\ i{1} = i{2} * r /\
   n{1} <= m{1} /\ m{1} - i{1} = r /\ i{1} <= n{1} /\
   bs{1} = blocks2bits bs{2} /\ size bs{1} = i{1} /\ size bs{2} = i{2} /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
   bs{1} = take n1 (blocks2bits bs{2}) /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})
  _
  (_ : size bs = n - 1 ==> size bs = n).
progress; smt(divz_ge0 gt0_r lez_floor size_blocks2bits).
smt().
wp. call (_ : true). auto. skip; smt(size_rcons).
transitivity{1}
  { while (i < m) {
      b <@ HybridIROEager.fill_in(xs, i);
      bs <- rcons bs b;
      i <- i + 1;
    }
  }
  (={bs, m, i, xs, HybridIROEager.mp} /\ n1 = n{1} /\ i{1} <= n1 /\
   n1 <= m{1} /\ size bs{1} = i{1} ==>
   ={HybridIROEager.mp} /\ bs{1} = take n1 bs{2})
  (xs{1} = x{2} /\ 0 <= i{2} /\ i{1} = i{2} * r /\ m{1} - i{1} = r /\
   size bs{2} = i{2} /\ bs{1} = blocks2bits bs{2} /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
   bs{1} = blocks2bits bs{2} /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
progress;
  exists HybridIROEager.mp{1}, (blocks2bits bs{2}), m{1},
         (size bs{2} * r), x{2};
  smt().
progress; smt(take_cat).
splitwhile{2} 1 : i < n1.
seq 1 1 :
  (={HybridIROEager.mp, xs, bs, i, m} /\ i{1} = n1 /\ n1 <= m{1} /\
   size bs{1} = n1).
while
  (={HybridIROEager.mp, xs, bs, i, m} /\ n{1} = n1 /\ n1 <= m{1} /\
   i{1} <= n1 /\ size bs{1} = i{1}).
wp.
call (_ : ={HybridIROEager.mp}).
if => //; rnd; auto.
skip; smt(size_rcons).
skip; smt().
while
  (={HybridIROEager.mp, xs, i, m} /\ n1 <= m{1} /\
   n1 <= i{1} <= m{1} /\ n1 <= size bs{2} /\
   bs{1} = take n1 bs{2}).
wp.
call (_ : ={HybridIROEager.mp}).
if => //; rnd; auto.
skip; progress;
  [smt() | smt() | smt(size_rcons) |
   rewrite -cats1 take_cat;
   smt(size_rcons take_oversize cats1 cats0)].
skip; smt(take_size).
transitivity{1}
  { (bs, i) <@ HybridIROEagerTrans.next_block(i, m, xs, bs);
  }
  (={i, m, xs, bs, HybridIROEager.mp} ==>
   ={i, m, xs, bs, HybridIROEager.mp})
  (xs{1} = x{2} /\ 0 <= i{2} /\ i{1} = i{2} * r /\ m{1} - i{1} = r /\
  size bs{2} = i{2} /\ bs{1} = blocks2bits bs{2} /\
  EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
  bs{1} = blocks2bits bs{2} /\
  EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
progress [-delta];
exists HybridIROEager.mp{1}, (blocks2bits bs{2}), m{1},
       (size bs{2} * r), x{2}=> //.
trivial.
inline HybridIROEagerTrans.next_block; sim.
transitivity{2}
  { (bs, i) <@ BlockSpongeTrans.next_block(x, i, bs);
  }
  (xs{1} = x{2} /\ 0 <= i{2} /\ i{1} = i{2} * r /\ m{1} - i{1} = r /\
   size bs{2} = i{2} /\ bs{1} = blocks2bits bs{2} /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
   bs{1} = blocks2bits bs{2} /\
   EagerInvar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})
  (={bs, i, x, BlockSponge.BIRO.IRO.mp} ==>
   ={bs, i, x, BlockSponge.BIRO.IRO.mp}).
progress [-delta];
exists BlockSponge.BIRO.IRO.mp{2}, bs{2}, (size bs{2}), x{2}=> //.
trivial.
exists* i{2}; elim*=> i2.
call (HybridIROEager_next i2).
auto.
inline BlockSpongeTrans.next_block; sim.
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
move=> |> &1 &2 ? n_eq inv.
exists BlockSponge.BIRO.IRO.mp{2}, HybridIROEager.mp{1}, (xs{1}, n{1} * r).
move=> |>; by rewrite n_eq.
progress; apply blocks2bitsK.
conseq HybridIROEager_f_g.
move=> |> &1 &2 ? -> ? //.
exists* n{1}; elim*=> n1. exists* xs{1}; elim*=> xs'.
conseq (HybridIROEager_g_BlockIRO_f n1 xs')=> //.
move=> |> &1 &2 ? -> inv; by rewrite needed_blocks_prod_r.
move=> |> &1 &2 ? n1_eq ? res1 res2 ? ? ? vb_imp not_vb_imp.
case (valid_block xs{1})=> [vb_xs1 | not_vb_xs1].
have [le0_n1_imp gt0_n1_imp] := vb_imp vb_xs1.
case: (n{1} <= 0)=> [le0_n1 | not_le0_n1].
smt().
have gt0_n1 : 0 < n{1} by smt().
have [-> sz_res2] := gt0_n1_imp gt0_n1.
have -> : n{1} = size(blocks2bits res2)
   by rewrite size_blocks2bits sz_res2 n1_eq
              needed_blocks_prod_r mulzC.
by rewrite take_size.
by have [->->] := not_vb_imp not_vb_xs1.
qed.

end HybridIRO.

section.

declare module BlockSim : BlockSponge.SIMULATOR{IRO, BlockSponge.BIRO.IRO}.
declare module Dist : DISTINGUISHER{Perm, BlockSim, IRO, BlockSponge.BIRO.IRO}.

local clone HybridIRO as HIRO.

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

local lemma RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f :
  equiv[HIRO.RaiseHybridIRO(HIRO.HybridIROEager).f ~
        RaiseFun(BlockSponge.BIRO.IRO).f :
  ={bs, n} /\ ={glob BlockSim} /\
  HIRO.EagerInvar BlockSponge.BIRO.IRO.mp{2} HIRO.HybridIROEager.mp{1} ==>
  ={res} /\ ={glob BlockSim} /\
  HIRO.EagerInvar BlockSponge.BIRO.IRO.mp{2} HIRO.HybridIROEager.mp{1}].
proof.
proc=> /=.
exists* n{1}; elim*=> n'.
exists* (pad2blocks bs{2}); elim*=> xs2.
call (HIRO.HybridIROEager_g_BlockIRO_f n' xs2).
auto=> |> &1 &2 ? res1 res2 mp1 mp2 ? vb_imp not_vb_imp.
case: (valid_block (pad2blocks bs{2}))=> [vb | not_vb].
have [le0_n2_imp gt0_n2_imp] := vb_imp vb.
case: (n{2} <= 0)=> [le0_n2 | not_le0_n2].
smt().
have gt0_n2 : 0 < n{2} by smt().
by have [-> _] := gt0_n2_imp gt0_n2.
have [-> ->] := not_vb_imp not_vb; by rewrite blocks2bits_nil.
qed.

local lemma Ideal_IRO_Experiment_HybridLazy &m :
  Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res] =
  Pr[Experiment
     (HIRO.RaiseHybridIRO(HIRO.HybridIROLazy), BlockSim(HIRO.HybridIROLazy),
      Dist).main() @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 :
  (={glob Dist, glob BlockSim} /\ IRO.mp{1} = NewFMap.map0 /\
   HIRO.HybridIROLazy.mp{2} = NewFMap.map0).
inline*; wp; call (_ : true); auto.
call
  (_ :
  ={glob Dist, glob BlockSim} /\
  IRO.mp{1} = map0 /\ HIRO.HybridIROLazy.mp{2} = map0 ==>
  ={res}).
proc (={glob BlockSim} /\ HIRO.LazyInvar IRO.mp{1} HIRO.HybridIROLazy.mp{2}).
progress [-delta]; apply HIRO.lazy_invar0.
trivial.
proc (HIRO.LazyInvar IRO.mp{1} HIRO.HybridIROLazy.mp{2})=> //.
apply HIRO.LowerFun_IRO_HybridIROLazy_f.
proc (HIRO.LazyInvar IRO.mp{1} HIRO.HybridIROLazy.mp{2})=> //.
apply HIRO.LowerFun_IRO_HybridIROLazy_f.
by conseq HIRO.IRO_RaiseHybridIRO_HybridIROLazy_f.
auto.
qed.

local module (HybridIRODist : HIRO.HYBRID_IRO_DIST) (HI : HIRO.HYBRID_IRO) = {
  proc distinguish() : bool = {
    var b : bool;
    BlockSim(HI).init();
    b <@ Dist(HIRO.RaiseHybridIRO(HI), BlockSim(HI)).distinguish();
    return b;
  }
}.

local lemma Experiment_HybridIROExper_Lazy &m :
  Pr[Experiment
     (HIRO.RaiseHybridIRO(HIRO.HybridIROLazy), BlockSim(HIRO.HybridIROLazy),
      Dist).main() @ &m : res] =
  Pr[HIRO.HybridIROExper(HIRO.HybridIROLazy, HybridIRODist).main() @ &m : res].
proof.
byequiv=> //; proc; inline*.
seq 2 2 : (={glob Dist, glob BlockSim, HIRO.HybridIROLazy.mp}).
swap{2} 1 1; wp; call (_ : true); auto.
sim.
qed.

local lemma HybridIROExper_Experiment_Eager &m :
  Pr[HIRO.HybridIROExper(HIRO.HybridIROEager, HybridIRODist).main() @ &m : res] =
  Pr[Experiment
     (HIRO.RaiseHybridIRO(HIRO.HybridIROEager), BlockSim(HIRO.HybridIROEager),
      Dist).main() @ &m : res].
proof.
byequiv=> //; proc; inline*.
seq 2 2 : (={glob Dist, glob BlockSim, HIRO.HybridIROEager.mp}).
swap{2} 1 1; wp; call (_ : true); auto.
sim.
qed.

local lemma Experiment_Hybrid_Lazy_Eager &m :
  Pr[Experiment
     (HIRO.RaiseHybridIRO(HIRO.HybridIROLazy), BlockSim(HIRO.HybridIROLazy),
      Dist).main() @ &m : res] =
  Pr[Experiment
     (HIRO.RaiseHybridIRO(HIRO.HybridIROEager), BlockSim(HIRO.HybridIROEager),
      Dist).main() @ &m : res].
proof.
by rewrite (Experiment_HybridIROExper_Lazy &m)
           (HIRO.HybridIROExper_Lazy_Eager HybridIRODist &m)
           (HybridIROExper_Experiment_Eager &m).
qed.

local lemma Experiment_HybridEager_Ideal_BlockIRO &m :
  Pr[Experiment
     (HIRO.RaiseHybridIRO(HIRO.HybridIROEager), BlockSim(HIRO.HybridIROEager),
      Dist).main() @ &m : res] =
  Pr[BlockSponge.IdealIndif
     (BlockSponge.BIRO.IRO, BlockSim, LowerDist(Dist)).main () @ &m : res].
proof.
byequiv=> //; proc.
seq 2 2 :
  (={glob Dist, glob BlockSim} /\ HIRO.HybridIROEager.mp{1} = NewFMap.map0 /\
   BlockSponge.BIRO.IRO.mp{2} = NewFMap.map0).
inline*; wp; call (_ : true); auto.
call
  (_ :
  ={glob Dist, glob BlockSim} /\
  HIRO.HybridIROEager.mp{1} = map0 /\ BlockSponge.BIRO.IRO.mp{2} = map0 ==>
  ={res}).
proc
  (={glob BlockSim} /\
   HIRO.EagerInvar BlockSponge.BIRO.IRO.mp{2} HIRO.HybridIROEager.mp{1}) => //.
progress [-delta]; apply HIRO.eager_invar0.
proc (HIRO.EagerInvar BlockSponge.BIRO.IRO.mp{2} HIRO.HybridIROEager.mp{1})=> //;
  conseq HIRO.HybridIROEager_BlockIRO_f=> //.
proc (HIRO.EagerInvar BlockSponge.BIRO.IRO.mp{2} HIRO.HybridIROEager.mp{1})=> //;
  conseq HIRO.HybridIROEager_BlockIRO_f=> //.
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
