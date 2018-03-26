(** This is a theory for the Squeezeless sponge: where the ideal
    functionality is a fixed-output-length random oracle whose output
    length is the input block size. We prove its security even when
    padding is not prefix-free. **)
require import Core Int Real StdOrder Ring IntExtra.
require import List FSet NewFMap Utils Common RndO DProd Dexcepted.

require (*..*) Indifferentiability.
(*...*) import Capacity IntOrder.

type state  = block  * capacity.
op   dstate = bdistr `*` cdistr.

clone include Indifferentiability with
  type p     <- state, 
  type f_in  <- block list,
  type f_out <- block
  rename [module] "GReal" as "RealIndif"
         [module] "GIdeal"  as "IdealIndif".

(** max number of call to the permutation and its inverse, 
    including those performed by the construction. *)
op max_size : { int | 0 <= max_size } as max_ge0.

(** Ideal Functionality **)
clone export Tuple as TupleBl with
  type t <- block,
  op Support.enum <- Block.blocks
  proof Support.enum_spec by exact Block.enum_spec. 

op bl_enum = flatten (mkseq (fun i => wordn i) (max_size + 1)). 
op bl_univ = FSet.oflist bl_enum.

(* -------------------------------------------------------------------------- *)
(* Random oracle from block list to block                                     *)
clone import RndO.GenEager as F with
  type from <- block list,
  type to   <- block,
  op sampleto <- fun (_:block list)=> bdistr
  proof * by exact Block.DBlock.dunifin_ll.


module Redo = {
  var prefixes : (block list, state) fmap

  proc init() : unit = {
    prefixes <- map0.[[] <- (b0,c0)];
  }
}.

(** We can now define the squeezeless sponge construction **)
module SqueezelessSponge (P:DPRIMITIVE): FUNCTIONALITY = {
  proc init () = {
    Redo.init();
  } 

  proc f(p : block list): block = {
    var (sa,sc) <- (b0,c0);
    var i : int <- 0;

    while (i < size p) { (* Absorption *)
      if (take (i+1) p \in dom Redo.prefixes) {
        (sa,sc) <- oget Redo.prefixes.[take (i+1) p];
      } else {
        (sa,sc) <- (sa +^ nth witness p i, sc);
        (sa,sc) <@ P.f((sa,sc));
        Redo.prefixes.[take (i+1) p] <- (sa,sc);
      }
      i <- i + 1;
    }

    return sa;          (* Squeezing phase (non-iterated) *)
  }
}.

clone export DProd.ProdSampling as Sample2 with 
  type t1 <- block,
  type t2 <- capacity,
  op d1   <- bdistr,
  op d2   <- cdistr.

(* -------------------------------------------------------------------------- *)
(** TODO move this **)

op incl (m m':('a,'b)fmap) = 
  forall x,  m .[x] <> None => m'.[x] = m.[x].

(* -------------------------------------------------------------------------- *)
(** usefull type and operators for the proof **)

type handle  = int.

type hstate = block * handle.
 
type ccapacity = capacity * flag.

type smap    = (state , state    ) fmap.
type hsmap   = (hstate, hstate   ) fmap.
type handles = (handle, ccapacity) fmap.

pred is_pre_permutation (m mi : ('a,'a) fmap) =
     (forall x, mem (rng m) x => mem (dom mi) x)
  /\ (forall x, mem (rng mi) x => mem (dom m) x).

lemma half_permutation_set (m' mi' : ('a,'a) fmap) x' y':
     (forall x, mem (rng m') x => mem (dom mi') x)
  => (forall x, mem (rng m'.[x' <- y']) x => mem (dom mi'.[y' <- x']) x).
proof.
  move=> h x0.
  rewrite rng_set domP !in_fsetU in_fset1 => -[/rng_rem_le in_rng|//=].
  by rewrite h.
qed.

lemma pre_permutation_set (m mi : ('a,'a) fmap) x y:
  is_pre_permutation m mi =>
  is_pre_permutation m.[x <- y] mi.[y <- x].
proof.
  move=> [dom_mi dom_m].
  by split; apply/half_permutation_set.
qed.    

(* Functionnal version of the construction using handle *)

op step_hpath (mh:hsmap) (sah:hstate option) (b:block) = 
    if sah = None then None 
    else 
      let sah = oget sah in 
      mh.[(sah.`1 +^ b, sah.`2)].

op build_hpath (mh:hsmap) (bs:block list) = 
   foldl (step_hpath mh) (Some (b0,0)) bs.

inductive build_hpath_spec mh p v h =
  | Empty of (p = [])
           & (v = b0)
           & (h = 0)
  | Extend p' b v' h' of (p = rcons p' b)
                       & (build_hpath mh p' = Some (v',h'))
                       & (mh.[(v' +^ b,h')] = Some (v,h)).

lemma build_hpathP mh p v h:
  build_hpath mh p = Some (v,h) <=> build_hpath_spec mh p v h.
proof.
elim/last_ind: p v h=> @/build_hpath //= [v h|p b ih v h]. 
+ by rewrite andaE; split=> [!~#] <*>; [exact/Empty|move=> [] /#].
rewrite -{1}cats1 foldl_cat {1}/step_hpath /=.
case: {-1}(foldl _ _ _) (eq_refl (foldl (step_hpath mh) (Some (b0,0)) p))=> //=.
+ apply/implybN; case=> [/#|p' b0 v' h'].
  move=> ^/rconssI <<- {p'} /rconsIs ->> {b}.
  by rewrite /build_hpath=> ->.
move=> [v' h']; rewrite oget_some /= -/(build_hpath _ _)=> build. 
split.
+ by move=> mh__; apply/(Extend mh (rcons p b) v h p b v' h' _ build mh__).
case=> [/#|] p' b' v'' h'' ^/rconssI <<- {p'} /rconsIs <<- {b'}.
by rewrite build /= => [#] <*>.
qed.

lemma build_hpath_map0 p:
   build_hpath map0 p
   = if   p = [] then Some (b0,0) else None.
proof.
elim/last_ind: p=> //= p b _.
by rewrite -{1}cats1 foldl_cat {1}/step_hpath /= map0P /= /#.
qed.

(* -------------------------------------------------------------------------- *)
theory Prefixe.

op prefixe ['a] (s t : 'a list) =
  with s = x :: s', t = y :: t' => if x = y then 1 + prefixe s' t' else 0
  with s = _ :: _ , t = []      => 0
  with s = []     , t = _ :: _  => 0
  with s = []     , t = []      => 0.

lemma prefixe_eq (l : 'a list) : prefixe l l = size l.
proof. elim:l=>//=/#. qed.


lemma prefixeC (l1 l2 : 'a list) : 
    prefixe l1 l2 = prefixe l2 l1.
proof.
move:l1;elim l2=>//=;first by move=>l1;elim l1=>//=.
move=>e2 l2 Hind l1;move:e2 l2 Hind;elim l1=>//=.
move=>e1 l1 Hind e2 l2 Hind1;rewrite Hind1/#.
qed.


lemma prefixe_ge0 (l1 l2 : 'a list) : 
    0 <= prefixe l1 l2.
proof.
move:l2;elim:l1=>//=;first move=>l2;elim:l2=>//=.
move=>e1 l1 Hind l2;move:e1 l1 Hind;elim l2=>//=.
move=>e2 l2 Hind2 e1 l1 Hind1/#.
qed.

lemma prefixe_sizel (l1 l2 : 'a list) :
    prefixe l1 l2 <= size l1.
proof.
move:l2;elim :l1=>//=;first by move=>l2;elim l2=>//=.
move=>e1 l1 Hind l2;move:e1 l1 Hind;elim l2=>//=;1:smt(size_ge0).
move=>e2 l2 Hind2 e1 l1 Hind1/#.
qed.

lemma prefixe_sizer (l1 l2 : 'a list) :
    prefixe l1 l2 <= size l2.
proof.
by rewrite prefixeC prefixe_sizel.
qed.


lemma prefixe_take (l1 l2 : 'a list) :
    take (prefixe l1 l2) l1 = take (prefixe l1 l2) l2.
proof.
move:l2;elim l1=>//=; first by move=>l2;elim l2=>//=.
move=>e1 l1 Hind l2/=;move:e1 l1 Hind;elim l2=>//=.
move=>e2 l2 Hind1 e1 l1 Hind2=>//=. 
by case(e1=e2)=>[->//=/#|//=].
qed.

lemma take_take (l : 'a list) (i j : int) :
    take i (take j l) = take (min i j) l.
proof.
case(i <= j)=>Hij.
+ case(j < size l)=>Hjsize;last smt(take_oversize).
  case(0 <= i)=>Hi0;last smt(take_le0).
  apply (eq_from_nth witness);1:smt(size_take).
  move=>k;rewrite !size_take//=1:/# Hjsize/=.
  cut->: (if i < j then i else j) = i by rewrite/#.
  move=>[Hk0 Hki].
  by rewrite !nth_take//=/#.
case(0<j)=>//=Hj0;last smt(take_le0).
rewrite min_ler 1:/#. 
pose l':=take j l. 
rewrite take_oversize//=.
rewrite/l' size_take /#.
qed.

lemma prefixe_take_leq (l1 l2 : 'a list) (i : int) :
    i <= prefixe l1 l2 => take i l1 = take i l2.
proof.
move=>Hi.
cut->:i = min i (prefixe l1 l2) by smt(min_lel).
by rewrite-(take_take l1 i _)-(take_take l2 i _) prefixe_take.
qed.

lemma prefixe_nth (l1 l2 : 'a list) :
    let i = prefixe l1 l2 in
    forall j, 0 <= j < i => 
    nth witness l1 j = nth witness l2 j.
proof.
rewrite/=. 
cut Htake:=prefixe_take l1 l2. search nth take.
move=>j[Hj0 Hjp];rewrite-(nth_take witness (prefixe l1 l2))1:prefixe_ge0//.
by rewrite-(nth_take witness (prefixe l1 l2) l2)1:prefixe_ge0//Htake.
qed.


op max_prefixe (l1 l2 : 'a list) (ll : 'a list list) =
  with ll = "[]" => l2
  with ll = (::) l' ll' => 
    if prefixe l1 l2 < prefixe l1 l' then max_prefixe l1 l' ll'
    else max_prefixe l1 l2 ll'.


op get_max_prefixe (l : 'a list) (ll : 'a list list) =
  with ll = "[]" => []
  with ll = (::) l' ll' => max_prefixe l l' ll'.


pred prefixe_inv (queries : (block list, block) fmap)
               (prefixes : (block list, state) fmap) =
  (forall (bs : block list),
    bs \in dom queries => oget queries.[bs] = (oget prefixes.[bs]).`1) &&
  (forall (bs : block list),
    bs \in dom queries => forall i, take i bs \in dom prefixes) &&
  (forall (bs : block list),
    forall i, take i bs <> [] =>
    take i bs \in dom prefixes =>
    exists l2, (take i bs) ++ l2 \in dom queries).

pred all_prefixes (prefixes : (block list, state) fmap) =
    forall (bs : block list), bs \in dom prefixes => forall i, take i bs \in dom prefixes.

lemma aux_mem_get_max_prefixe (l1 l2 : 'a list) ll :
    max_prefixe l1 l2 ll = l2 \/ max_prefixe l1 l2 ll \in ll.
proof.
move:l1 l2;elim:ll=>//=l3 ll Hind l1 l2. 
case(prefixe l1 l2 < prefixe l1 l3)=>//=hmax.
+ cut/#:=Hind l1 l3.
cut/#:=Hind l1 l2.
qed.


lemma mem_get_max_prefixe (l : 'a list) ll :
    ll <> [] => get_max_prefixe l ll  \in ll.
proof.
move:l;elim:ll=>//=l2 ll Hind l1. 
exact aux_mem_get_max_prefixe.
qed.


lemma take_get_max_prefixe l prefixes :
    (exists b, b  \in dom prefixes) =>
    all_prefixes prefixes =>
    take (prefixe l (get_max_prefixe l (elems (dom prefixes)))) l \in dom prefixes.
proof.
move=>nil_in_dom all_pref.
rewrite prefixe_take all_pref memE mem_get_max_prefixe;smt(memE).
qed.
    
lemma take_get_max_prefixe2 l prefixes i :
    (exists b, b \in dom prefixes) =>
    all_prefixes prefixes =>
    i <= prefixe l (get_max_prefixe l (elems (dom prefixes))) =>
    take i l \in dom prefixes.
proof.
move=>nil_in_dom all_pref hi. 
rewrite (prefixe_take_leq _ _ i hi) all_pref memE mem_get_max_prefixe;smt(memE).
qed.


lemma prefixe_cat (l l1 l2 : 'a list) :
    prefixe (l ++ l1) (l ++ l2) = size l + prefixe l1 l2.
proof.
move:l1 l2;elim l=>//=/#.
qed.


lemma prefixe_leq_take (l1 l2 : 'a list) i :
    0 <= i <= min (size l1) (size l2) => 
    take i l1 = take i l2 =>
    i <= prefixe l1 l2.
proof.
move=> [hi0 himax] htake.
rewrite-(cat_take_drop i l1)-(cat_take_drop i l2)htake. 
rewrite prefixe_cat size_take//=;smt(prefixe_ge0).
qed.

lemma prefixe0 (l1 l2 : 'a list) :
    prefixe l1 l2 = 0 <=> l1 = [] \/ l2 = [] \/ head witness l1 <> head witness l2 .
proof.
move:l2;elim:l1=>//=;1:rewrite/#;move=>e1 l1 Hind l2;move:e1 l1 Hind;elim:l2=>//=e2 l2 Hind2 e1 l1 Hind1.
smt(prefixe_ge0).
qed.

lemma head_nth0 (l : 'a list) : head witness l = nth witness l 0.
proof. by elim:l. qed.


lemma get_prefixe (l1 l2 : 'a list) i :
    0 <= i <= min (size l1) (size l2)=>
    (drop i l1 = [] \/ drop i l2 = [] \/
    (i < min (size l1) (size l2) /\
    nth witness l1 i <> nth witness l2 i)) =>
    take i l1 = take i l2 =>
    i = prefixe l1 l2.
proof.
move=>[hi0 hisize] [|[]]. 
+ move=>hi. 
  cut:=size_eq0 (drop i l1);rewrite {2}hi/=size_drop// =>h.
  cut hsize: size l1 = i by rewrite/#. 
  rewrite -hsize take_size.
  rewrite-{2}(cat_take_drop (size l1) l2)=><-.
  by rewrite-{2}(cats0 l1)prefixe_cat/#. 
+ move=>hi. 
  cut:=size_eq0 (drop i l2);rewrite {2}hi/=size_drop// =>h.
  cut hsize: size l2 = i by rewrite/#. 
  rewrite -hsize take_size.
  rewrite-{2}(cat_take_drop (size l2) l1)=>->.
  by rewrite-{4}(cats0 l2)prefixe_cat/#. 
move=>[himax  hnth] htake.
rewrite-(cat_take_drop i l1)-(cat_take_drop i l2)htake. 
rewrite prefixe_cat size_take//=.
+ cut[_ ->]:=prefixe0 (drop i l1) (drop i l2).
  case(i = size l1)=>hi1//=.
  + by rewrite hi1 drop_size//=.
  case(i = size l2)=>hi2//=.
  + by rewrite hi2 drop_size//=.
  by rewrite 2!head_nth0 nth_drop//=nth_drop//= hnth.
rewrite/#.
qed.

lemma get_max_prefixe_leq (l1 l2 : 'a list) (ll : 'a list list) :
    prefixe l1 l2 <= prefixe l1 (max_prefixe l1 l2 ll).
proof.
move:l1 l2;elim:ll=>//=/#.
qed.

lemma get_max_prefixe_is_max (l1 l2 : 'a list) (ll : 'a list list) :
    forall l3, l3 \in ll => prefixe l1 l3 <= prefixe l1 (max_prefixe l1 l2 ll).
proof.
move:l1 l2;elim:ll=>//=. 
move=>l4 ll Hind l1 l2 l3.
case(prefixe l1 l2 < prefixe l1 l4)=>//=h [];smt( get_max_prefixe_leq ).
qed.

lemma get_max_prefixe_max (l : 'a list) (ll : 'a list list) :
    forall l2, l2 \in ll => prefixe l l2 <= prefixe l (get_max_prefixe l ll).
proof. smt(get_max_prefixe_is_max get_max_prefixe_leq). qed.

lemma all_take_in (l : block list) i prefixes :
    0 <= i <= size l =>
    all_prefixes prefixes =>
    take i l \in dom prefixes =>
    i <= prefixe l (get_max_prefixe l (elems (dom prefixes))).
proof.
move=>[hi0 hisize] all_prefixe take_in_dom.
cut->:i = prefixe l (take i l);2:smt(get_max_prefixe_max memE).
apply get_prefixe. 
+ smt(size_take). 
+ by right;left;apply size_eq0;rewrite size_drop//size_take//=/#.
smt(take_take).
qed.

lemma prefixe_inv_leq (l : block list) i prefixes queries :
    0 <= i <= size l =>
    elems (dom queries) <> [] =>
    all_prefixes prefixes =>
    take i l \in dom prefixes =>
    prefixe_inv queries prefixes =>
    i <= prefixe l (get_max_prefixe l (elems (dom queries))).
proof.
move=>h_i h_nil h_all_prefixes take_in_dom [?[h_prefixe_inv h_exist]].
case(take i l = [])=>//=h_take_neq_nil.
+ smt(prefixe_ge0 size_eq0).
cut[l2 h_l2_mem]:=h_exist l i h_take_neq_nil take_in_dom.
rewrite memE in h_l2_mem.
rewrite(StdOrder.IntOrder.ler_trans _ _ _ _ (get_max_prefixe_max _ _ _ h_l2_mem)).
rewrite-{1}(cat_take_drop i l)prefixe_cat size_take 1:/#;smt(prefixe_ge0).
qed.


lemma max_prefixe_eq (l : 'a list) (ll : 'a list list) :
    max_prefixe l l ll = l.
proof. 
move:l;elim:ll=>//=l2 ll Hind l1;smt( prefixe_eq prefixe_sizel).
qed.

lemma prefixe_max_prefixe_eq_size (l1 l2 : 'a list) (ll : 'a list list) :
    l1 = l2 \/ l1 \in ll =>
    prefixe l1 (max_prefixe l1 l2 ll) = size l1.
proof.
move:l1 l2;elim:ll=>//=;1:smt(prefixe_eq). 
move=>l3 ll Hind l1 l2[->|[->|h1]].
+ rewrite prefixe_eq max_prefixe_eq;smt(max_prefixe_eq prefixe_eq prefixe_sizer).
+ rewrite prefixe_eq max_prefixe_eq. 
  case(prefixe l3 l2 < size l3)=>//=h;1:by rewrite prefixe_eq.
  cut h1:prefixe l3 l2 = size l3 by smt(prefixe_sizel).
  cut: size l3 <= prefixe l3 (max_prefixe l3 l2 ll);2:smt(prefixe_sizel).
  rewrite-h1.
  by clear Hind l1 h h1;move:l2 l3;elim:ll=>//=l3 ll Hind l1 l2/#.
by case(prefixe l1 l2 < prefixe l1 l3)=>//=/#.
qed.

lemma prefixe_get_max_prefixe_eq_size (l : 'a list) (ll : 'a list list) :
    l \in ll =>
    prefixe l (get_max_prefixe l ll) = size l.
proof.
move:l;elim:ll=>//;smt(prefixe_max_prefixe_eq_size).
qed.

lemma get_max_prefixe_exists (l : 'a list) (ll : 'a list list) :
    ll <> [] =>
    exists l2, take (prefixe l (get_max_prefixe l ll)) l ++ l2 \in ll.
proof.
move:l;elim:ll=>//=l2 ll Hind l1;clear Hind;move:l1 l2;elim:ll=>//=.
+ smt(cat_take_drop prefixe_take).
move=>l3 ll Hind l1 l2.
case( prefixe l1 l2 < prefixe l1 l3 )=>//=h/#.
qed.

lemma prefixe_geq (l1 l2 : 'a list) :
    prefixe l1 l2 = prefixe (take (prefixe l1 l2) l1) (take (prefixe l1 l2) l2).
proof.
move:l2;elim:l1=>//=[/#|]e1 l1 Hind l2;elim:l2=>//=e2 l2 Hind2.
case(e1=e2)=>//=h12.
cut->/=:! 1 + prefixe l1 l2 <= 0 by smt(prefixe_ge0).
rewrite h12/=/#.
qed.

lemma prefixe_take_prefixe (l1 l2 : 'a list) :
    prefixe (take (prefixe l1 l2) l1) l2 = prefixe l1 l2.
proof.
move:l2;elim:l1=>//=e1 l1 Hind l2;elim:l2=>//=e2 l2 Hind2.
case(e1=e2)=>//=h12.
cut->/=:! 1 + prefixe l1 l2 <= 0 by smt(prefixe_ge0).
rewrite h12/=/#.
qed.

lemma prefixe_leq_prefixe_cat (l1 l2 l3 : 'a list) :
    prefixe l1 l2 <= prefixe (l1 ++ l3) l2.
proof.
move:l2 l3;elim l1=>//=;1:smt(take_le0 prefixe_ge0).
move=>e1 l1 hind1 l2;elim:l2=>//=e2 l2 hind2 l3/#.
qed.

lemma prefixe_take_leq_prefixe (l1 l2 : 'a list) i :
    prefixe (take i l1) l2 <= prefixe l1 l2.
proof.
rewrite-{2}(cat_take_drop i l1).
move:(take i l1)(drop i l1);clear i l1=>l1 l3. 
exact prefixe_leq_prefixe_cat.
qed.

lemma prefixe_take_geq_prefixe (l1 l2 : 'a list) i :
    prefixe l1 l2 <= i =>
    prefixe l1 l2 = prefixe (take i l1) l2.
proof.
move=>hi.
cut:prefixe (take i l1) l2 <= prefixe l1 l2.
+ rewrite-{2}(cat_take_drop i l1) prefixe_leq_prefixe_cat.
cut/#:prefixe l1 l2 <= prefixe (take i l1) l2.
rewrite -prefixe_take_prefixe.
rewrite-(cat_take_drop (prefixe l1 l2) (take i l1))take_take min_lel// prefixe_leq_prefixe_cat. 
qed.

lemma get_max_prefixe_take (l : 'a list) (ll : 'a list list) i :
    prefixe l (get_max_prefixe l ll) <= i =>
    get_max_prefixe l ll = get_max_prefixe (take i l) ll.
proof.
move:l;elim:ll=>//=l2 ll Hind l1;clear Hind;move:l1 l2;elim:ll=>//=l3 ll Hind l1 l2.
case( prefixe l1 l2 < prefixe l1 l3 )=>//=h hi.
+ rewrite -prefixe_take_geq_prefixe//=;1:smt(get_max_prefixe_leq).
  rewrite -prefixe_take_geq_prefixe//=;1:smt(get_max_prefixe_leq). 
  rewrite h/=/#.
rewrite -prefixe_take_geq_prefixe//=;1:smt(get_max_prefixe_leq).
rewrite -prefixe_take_geq_prefixe//=;1:smt(get_max_prefixe_leq). 
rewrite h/=/#.
qed.


lemma drop_prefixe_neq (l1 l2 : 'a list) :
    drop (prefixe l1 l2) l1 = [] \/ drop (prefixe l1 l2) l1 <> drop (prefixe l1 l2) l2.
proof.
move:l2;elim:l1=>//=e1 l1 hind1 l2;elim:l2=>//=e2 l2 hind2/#.
qed.


lemma prefixe_prefixe_prefixe (l1 l2 l3 : 'a list) (ll : 'a list list) :
    prefixe l1 l2 <= prefixe l1 l3 =>
    prefixe l1 (max_prefixe l1 l2 ll) <= prefixe l1 (max_prefixe l1 l3 ll).
proof.
move:l1 l2 l3;elim:ll=>//=l4 ll hind l1 l2 l3 h123/#.
qed.

lemma prefixe_lt_size (l : 'a list) (ll : 'a list list) :
    prefixe l (get_max_prefixe l ll) < size l =>
    forall i, prefixe l (get_max_prefixe l ll) < i =>
    ! take i l \in ll.
proof.
move:l;elim:ll=>//=l2 ll Hind l1;clear Hind;move:l1 l2;elim:ll=>//=.
+ progress.
  rewrite-(cat_take_drop (prefixe l1 l2) (take i l1))
    -{3}(cat_take_drop (prefixe l1 l2) l2)take_take/min H0/=.
  rewrite prefixe_take. 
  cut:drop (prefixe l1 l2) (take i l1) <> drop (prefixe l1 l2) l2;2:smt(catsI). 
  rewrite (prefixe_take_geq_prefixe l1 l2 i) 1:/#.  
  cut:=drop_prefixe_neq (take i l1) l2.
  cut/#:drop (prefixe (take i l1) l2) (take i l1) <> [].
  cut:0 < size (drop (prefixe (take i l1) l2) (take i l1));2:smt(size_eq0).
  rewrite size_drop 1:prefixe_ge0 size_take;1:smt(prefixe_ge0).
  by rewrite-prefixe_take_geq_prefixe /#.

move=>l3 ll hind l1 l2.
case(prefixe l1 l2 < prefixe l1 l3)=>//=h;progress.
+ rewrite!negb_or/=. 
  cut:=hind l1 l3 H i H0;rewrite negb_or=>[][->->]/=.
  cut:=hind l1 l2 _ i _;smt(prefixe_prefixe_prefixe).
smt(prefixe_prefixe_prefixe).
qed.

lemma asfadst queries prefixes (bs : block list) :
    prefixe_inv queries prefixes =>
    elems (dom queries ) <> [] =>
    all_prefixes prefixes =>
    (forall j, 0 <= j <= size bs => take j bs \in dom prefixes) => 
    take (prefixe bs (get_max_prefixe bs (elems (dom queries))) + 1) bs = bs.
proof.
progress. 
cut h:=prefixe_inv_leq bs (size bs) prefixes queries _ _ _ _ _;rewrite//=.
+ exact size_ge0.
+ rewrite H2//=;exact size_ge0.
cut->/=:prefixe bs (get_max_prefixe bs (elems (dom queries))) = size bs by smt(prefixe_sizel).
rewrite take_oversize/#.
qed.


lemma prefixe_exchange_prefixe_inv (ll1 ll2 : 'a list list) (l : 'a list) :
    (forall l2, l2 \in ll1 => l2 \in ll2) =>
    (forall (l2 : 'a list), l2 \in ll1 => forall i, take i l2 \in ll2) =>
    (forall l2, l2 \in ll2 => exists l3, l2 ++ l3 \in ll1) =>
    prefixe l (get_max_prefixe l ll1) = prefixe l (get_max_prefixe l ll2).
proof.
case(ll1 = [])=>//=[->/#|]//=ll1_nil.
move=>incl all_prefix incl2 ;cut ll2_nil:ll2 <> [] by rewrite/#.
cut:=get_max_prefixe_max l ll2 (get_max_prefixe l ll1) _.
+ by rewrite incl mem_get_max_prefixe ll1_nil.
cut mem_ll2:=mem_get_max_prefixe l ll2 ll2_nil.
cut[]l3 mem_ll1:=incl2 _ mem_ll2.
cut:=get_max_prefixe_max l ll1 _ mem_ll1.
smt(prefixeC prefixe_leq_prefixe_cat).
qed.

lemma prefixe_inv_nil queries prefixes :
    prefixe_inv queries prefixes =>
    elems (dom queries) = [] => dom prefixes \subset fset1 [].
proof.
move=>[h1 [h2 h3]] h4 x h5;rewrite in_fset1.
cut:=h3 x (size x).
rewrite take_size h5/=;apply absurd=>//=h6.
rewrite h6/=negb_exists/=;smt(memE).
qed.


lemma aux_prefixe_exchange queries prefixes (l : block list) :
    prefixe_inv queries prefixes => all_prefixes prefixes =>
    elems (dom queries) <>  [] =>
    prefixe l (get_max_prefixe l (elems (dom queries))) = 
    prefixe l (get_max_prefixe l (elems (dom prefixes))).
proof.
move=>[h1[h2 h3]] h5 h4;apply prefixe_exchange_prefixe_inv.
+ smt(memE take_size).
+ smt(memE).
move=>l2;rewrite-memE=> mem_l2.
case(l2=[])=>//=hl2;1:rewrite hl2/=. 
+ move:h4;apply absurd=>//=;rewrite negb_exists/=/#.
smt(memE take_size).
qed.

lemma prefixe_exchange queries prefixes (l : block list) :
    prefixe_inv queries prefixes => all_prefixes prefixes =>
    prefixe l (get_max_prefixe l (elems (dom queries))) = 
    prefixe l (get_max_prefixe l (elems (dom prefixes))).
proof.
move=>[h1[h2 h3]] h5.
case(elems (dom queries) = [])=>//=h4;2:smt(aux_prefixe_exchange).
cut h6:=prefixe_inv_nil queries prefixes _ h4;1:rewrite/#.
rewrite h4/=. 
case(elems (dom prefixes) = [])=>//=[->//=|]h7.
cut h8:elems (dom prefixes) = [[]].
+ cut [hh1 hh2]:[] \in dom prefixes /\ forall x, x \in elems (dom prefixes) => x = [] by smt(memE).
  cut h9:=subset_leq_fcard _ _ h6.
  apply (eq_from_nth witness)=>//=.
  + rewrite-cardE-(fcard1 [<:block>]);move:h9;rewrite!fcard1!cardE=>h9. 
    cut/#:0 < size (elems (dom prefixes));smt(size_eq0 size_ge0 fcard1).
  move:h9;rewrite!fcard1!cardE=>h9 i [hi0 hi1]. 
  cut->/=:i = 0 by rewrite/#.
  by apply hh2;rewrite mem_nth/#.
by rewrite h8=>//=.  
qed.


pred all_prefixes_fset (prefixes : block list fset) =
  forall bs, bs \in prefixes => forall i, take i bs \in prefixes.

pred inv_prefixe_block  (queries : (block list, block) fmap)
               (prefixes : (block list, block) fmap) =
  (forall (bs : block list),
    bs \in dom queries => queries.[bs] = prefixes.[bs]) &&
  (forall (bs : block list),
    bs \in dom queries => forall i, 0 < i <= size bs => take i bs \in dom prefixes).

lemma prefixe_gt0_mem l (ll : 'a list list) : 
    0 < prefixe l (get_max_prefixe l ll) =>
    get_max_prefixe l ll \in ll.
proof.
move:l;elim:ll=>//=;first by move=>l;elim:l.
move=>l2 ll hind l1;clear hind;move:l1 l2;elim:ll=>//=l3 ll hind l1 l2.
by case(prefixe l1 l2 < prefixe l1 l3)=>//=/#.
qed.

lemma inv_prefixe_block_mem_take queries prefixes l i :
    inv_prefixe_block queries prefixes =>
    0 < i < prefixe l (get_max_prefixe l (elems (dom queries))) =>
    take i l \in dom prefixes.
proof.
move=>[]H_incl H_all_prefixes Hi.
rewrite (prefixe_take_leq _ (get_max_prefixe l (elems (dom queries))))1:/#.
rewrite H_all_prefixes.
cut:get_max_prefixe l (elems (dom queries)) \in dom queries;2:smt(in_dom).
by rewrite memE;apply prefixe_gt0_mem=>/#.
smt(prefixe_sizer).
qed.

(* lemma prefixe_inv_prefixe queries prefixes l : *)
(*     prefixe_inv queries prefixes => *)
(*     all_prefixes prefixes => *)
(*     (elems (dom queries) = [] => elems (dom prefixes) = [[]]) => *)
(*     prefixe l (get_max_prefixe l (elems (dom queries))) =  *)
(*     prefixe l (get_max_prefixe l (elems (dom prefixes))). *)
(* proof. *)
(* move=>[? h_prefixe_inv] h_all_prefixes. *)
(* case(elems (dom queries) = [])=>//=h_nil. *)
(* + by rewrite h_nil//==>->/=. *)
(* cut h_mem_queries:=mem_get_max_prefixe l (elems (dom queries)) h_nil. *)
(* cut h_leq :=all_take_in l (prefixe l (get_max_prefixe l (elems (dom queries)))) _ _ h_all_prefixes _. *)
(* + smt(prefixe_ge0 prefixe_sizel). *)
(* + by rewrite prefixe_take h_prefixe_inv memE h_mem_queries. *)
(* cut:=all_take_in l (prefixe l (get_max_prefixe l (elems (dom prefixes)))) _ _ h_all_prefixes _. *)
(* + smt(prefixe_ge0 prefixe_sizel). *)
(* +  *)
(* rewrite prefixe_take. *)
  
(*   rewrite -take_size. *)

(* print mem_get_max_prefixe. *)

(* qed. *)

pred invm (m mi : ('a * 'b, 'a * 'b) fmap) =
  forall x y, m.[x] = Some y <=> mi.[y] = Some x.

lemma invm_set (m mi : ('a * 'b, 'a * 'b) fmap) x y :
    ! x \in dom m => ! y \in rng m => invm m mi => invm m.[x <- y] mi.[y <- x].
proof.
move=>Hxdom Hyrng Hinv a b;rewrite!getP;split.
+ case(a=x)=>//=hax hab;cut->/#:b<>y.
  by cut/#:b\in rng m;rewrite in_rng/#.
case(a=x)=>//=hax.
+ case(b=y)=>//=hby.
  by rewrite (eq_sym y b)hby/=-Hinv hax;rewrite in_dom/=/# in Hxdom.
by rewrite Hinv/#.
qed.

op blocksponge (l : block list) (m : (state, state) fmap) (bc : state) =
  with l = "[]" => (l,bc)
  with l = (::) b' l' =>
    let (b,c) = (bc.`1,bc.`2) in
    if ((b +^ b', c) \in dom m) then blocksponge l' m (oget m.[(b +^ b', c)])
    else (l,(b,c)).
  
op s0 : state = (b0,c0).

lemma blocksponge_size_leq l m bc : 
    size (blocksponge l m bc).`1 <= size l.
proof.
move:m bc;elim l=>//=.
move=>e l Hind m bc/#.
qed.


lemma blocksponge_set l m bc x y :
    (x \in dom m => y = oget m.[x]) =>
    let bs1 = blocksponge l m bc in
    let bs2 = blocksponge l m.[x <- y] bc in
    let l1 = bs1.`1 in let l2 = bs2.`1 in let bc1 = bs1.`2 in let bc2 = bs2.`2 in
    size l2 <= size l1 /\ (size l1 = size l2 => (l1 = l2 /\ bc1 = bc2)).
proof.
move=>Hxy/=;split.
+ move:m bc x y Hxy;elim l=>//=.
  move=>/=e l Hind m bc x y Hxy/=;rewrite dom_set in_fsetU1.
  case((bc.`1 +^ e, bc.`2) = x)=>//=[->//=|hx]. 
  + rewrite getP/=oget_some;case(x\in dom m)=>//=[/#|].
    smt(blocksponge_size_leq getP).
  rewrite getP hx/=.
  case((bc.`1 +^ e, bc.`2) \in dom m)=>//=Hdom.
  by cut//:=Hind m (oget m.[(bc.`1 +^ e, bc.`2)]) x y Hxy.
move:m bc x y Hxy;elim l=>//=.
move=>e l Hind m bx x y Hxy.
rewrite!dom_set !in_fsetU1 !getP.
case((bx.`1 +^ e, bx.`2) \in dom m)=>//=Hdom.
+ case(((bx.`1 +^ e, bx.`2) = x))=>//=Hx.
  + move:Hdom;rewrite Hx=>Hdom. 
    cut:=Hxy;rewrite Hdom/==>Hxy2.
    rewrite oget_some -Hxy2/=.
    by cut:=Hind m y x y Hxy.
  by cut:=Hind m (oget m.[(bx.`1 +^ e, bx.`2)]) x y Hxy.
case(((bx.`1 +^ e, bx.`2) = x))=>//=;smt(blocksponge_size_leq).
qed.


lemma blocksponge_cat m l1 l2 bc :
    blocksponge (l1 ++ l2) m bc =
    let lbc = blocksponge l1 m bc in
    blocksponge (lbc.`1 ++ l2) m (lbc.`2).
proof.
rewrite/=. 
move:m bc l2;elim l1=>//= e1 l1 Hind m bc b.
case((bc.`1 +^ e1, bc.`2) \in dom m)=>//=[|->//=]Hdom.
by cut//:=Hind m (oget m.[(bc.`1 +^ e1, bc.`2)]) b.
qed.


lemma blocksponge_rcons m l bc b :
    blocksponge (rcons l b) m bc = 
    let lbc = blocksponge l m bc in
    blocksponge (rcons lbc.`1 b) m (lbc.`2).
proof.
by rewrite/=-2!cats1 blocksponge_cat/=. 
qed.


(* lemma prefixe_inv_bs_fst_nil queries prefixes m : *)
(*     prefixe_inv queries prefixes m => *)
(*     forall l, l \in dom queries => *)
(*     forall i, 0 <= i <= size l => *)
(*     (blocksponge (take i l) m s0).`1 = []. *)
(* proof. *)
(* move=>[h2 [h3 Hinv]] l Hdom i [Hi0 Hisize];move:i Hi0 l Hisize Hdom;apply intind=>//=. *)
(* + by move=>l;rewrite take0/=. *)
(* move=>i Hi0 Hind l Hil Hldom. *)
(* rewrite(take_nth b0)1:/#. *)
(* rewrite blocksponge_rcons/=. *)
(* cut->/=:=Hind l _ Hldom;1:rewrite/#. *)
(* by cut/=->/=/#:=Hinv _ Hldom i. *)
(* qed. *)


(* lemma blocksponge_drop l m bc : *)
(*     exists i, 0 <= i <= List.size l /\ (blocksponge l m bc).`1 = drop i l. *)
(* proof. *)
(* move:l bc=>l;elim:l=>//=;1:exists 0=>//=;progress. *)
(* case((bc.`1 +^ x, bc.`2) \in dom m)=>//=h. *)
(* + cut[i [[hi0 His] Hi]]:=H (oget m.[(bc.`1 +^ x, bc.`2)]). *)
(*   exists(i+1)=>/#. *)
(* cut[i [[hi0 His] Hi]]:=H (oget m.[(bc.`1 +^ x, bc.`2)]). *)
(* exists 0=>/#. *)
(* qed. *)


(* lemma prefixe_inv_set queries prefixes m x y : *)
(*     !x \in dom m => *)
(*     prefixe_inv queries prefixes m => *)
(*     prefixe_inv queries prefixes m.[x <- y]. *)
(* proof. *)
(* move=>Hxdom Hpref;progress=>//=.  *)
(* + rewrite/#. *)
(* + rewrite/#. *)
(* cut->:blocksponge (take i bs) m.[x <- y] s0 = blocksponge (take i bs) m s0. *)
(* + move:i H2  bs H3 H1;apply intind=>//=i;first smt(take0). *)
(*   move=>Hi0 Hind bs Hisize Hbsdom. *)
(*   rewrite (take_nth b0)1:/#. *)
(*   rewrite 2!blocksponge_rcons/=. *)
(*   cut[?[? Hpre]]:=Hpref. *)
(*   cut->/=:=prefixe_inv_bs_fst_nil _ _ _ Hpref _ Hbsdom i _;1:rewrite/#. *)
(*   cut/=->/=:=Hpre _ Hbsdom i _;1:rewrite/#. *)
(*   cut->/=:=Hind bs _ Hbsdom;1:rewrite/#. *)
(*   cut->/=:=prefixe_inv_bs_fst_nil _ _ _ Hpref _ Hbsdom i _;1:rewrite/#. *)
(*   rewrite dom_set in_fsetU1. *)
(*   cut/=->/=:=Hpre _ Hbsdom i _;1:rewrite/#. *)
(*   rewrite getP. *)
(*   cut/#:=Hpre _ Hbsdom i _;1:rewrite/#. *)
(* rewrite dom_set in_fsetU1. *)
(* cut[?[? Hpre]]:=Hpref. *)
(* cut/#:=Hpre _ H1 i _;1:rewrite/#. *)
(* qed. *)


(* lemma blocksponge_set_nil l m bc x y : *)
(*     !x \in dom m => *)
(*     let bs1 = blocksponge l m bc in *)
(*     let bs2 = blocksponge l m.[x <- y] bc in *)
(*     bs1.`1 = [] => *)
(*     bs2 = ([], bs1.`2). *)
(* proof. *)
(* rewrite/==>hdom bs1. *)
(* cut/=:=blocksponge_set l m bc x y. *)
(* smt(size_ge0 size_eq0). *)
(* qed. *)

(* lemma size_blocksponge queries m l : *)
(*     prefixe_inv queries m => *)
(*     size (blocksponge l m s0).`1 <= size l - prefixe l (get_max_prefixe l (elems (dom queries))). *)
(* proof. *)
(* move=>Hinv. *)
(* pose l2:=get_max_prefixe _ _;pose p:=prefixe _ _. search take drop. *)
(* rewrite-{1}(cat_take_drop p l)blocksponge_cat/=. *)
(* rewrite(prefixe_take). *)
(* qed. *)




end Prefixe.
export Prefixe.

(* -------------------------------------------------------------------------- *)

module C = {
  var c  : int
  var queries : (block list, block) fmap
  proc init () = {
    c       <- 0;
    queries <- map0.[[] <- b0];
  }
}.

module PC (P:PRIMITIVE) = {

  proc init () = {
    C.init();
    P.init();
  }

  proc f (x:state) = {  
    var y <- (b0,c0);
    y        <@ P.f(x);
    C.c      <- C.c + 1;
    return y;
  }

  proc fi(x:state) = {
    var y <- (b0,c0);
    y        <@ P.fi(x);
    C.c      <- C.c + 1;
    return y;
  } 

}.

module DPRestr (P:DPRIMITIVE) = {

  proc f (x:state) = {  
    var y <- (b0,c0);
    if (C.c + 1 <= max_size) {
      y        <@ P.f(x);
      C.c      <- C.c + 1;
    }
    return y;
  }

  proc fi(x:state) = {
    var y <- (b0,c0);
    if (C.c + 1 <= max_size) {
      y        <@ P.fi(x);
      C.c      <- C.c + 1;
    }
    return y;
  } 

}.

module PRestr (P:PRIMITIVE) = {

  proc init () = {
    C.init();
    P.init();
  }

  proc f = DPRestr(P).f

  proc fi = DPRestr(P).fi

}.

module FC(F:FUNCTIONALITY) = {

  proc init() = {
    F.init();
  }

  proc f (bs:block list) = {
    var b <- b0;
    if (!bs \in dom C.queries) {
      C.c <- C.c + size bs - prefixe bs (get_max_prefixe bs (elems (dom C.queries)));
      b <@ F.f(bs);
      C.queries.[bs] <- b;
    } else {
      b <- oget C.queries.[bs];
    }
    return b;
  }
}.

module DFRestr(F:DFUNCTIONALITY) = {

  proc f (bs:block list) = {
    var b= b0;
    if (!bs \in dom C.queries) {
      if (C.c + size bs - prefixe bs (get_max_prefixe bs (elems (dom C.queries))) <= max_size) {
        C.c <- C.c + size bs - prefixe bs (get_max_prefixe bs (elems (dom C.queries)));
        b <@ F.f(bs);
        C.queries.[bs] <- b;
      }
    } else {
      b <- oget C.queries.[bs];
    }
    return b;
  }
}.

module FRestr(F:FUNCTIONALITY) = {

  proc init() = {
    Redo.init();
    F.init();
  }

  proc f = DFRestr(F).f 

}.

(* -------------------------------------------------------------------------- *)
(* This allow swap the counting from oracle to adversary *)
module DRestr(D:DISTINGUISHER, F:DFUNCTIONALITY, P:DPRIMITIVE) = {
  proc distinguish() = {
    var b;
    C.init();
    b <@ D(DFRestr(F), DPRestr(P)).distinguish();
    return b;
  }
}.

lemma rp_ll (P<:DPRIMITIVE{C}): islossless P.f => islossless DPRestr(P).f.
proof. move=>Hll;proc;sp;if;auto;call Hll;auto. qed.

lemma rpi_ll (P<:DPRIMITIVE{C}): islossless P.fi => islossless DPRestr(P).fi.
proof. move=>Hll;proc;sp;if;auto;call Hll;auto. qed.

lemma rf_ll (F<:DFUNCTIONALITY{C}): islossless F.f => islossless DFRestr(F).f.
proof. move=>Hll;proc;sp;if;auto;if=>//;auto;call Hll;auto. qed.

lemma DRestr_ll (D<:DISTINGUISHER{C}): 
  (forall (F<:DFUNCTIONALITY{D})(P<:DPRIMITIVE{D}),
     islossless P.f => islossless P.fi => islossless F.f =>
     islossless D(F,P).distinguish) =>
  forall (F <: DFUNCTIONALITY{DRestr(D)}) (P <: DPRIMITIVE{DRestr(D)}),
    islossless P.f =>
    islossless P.fi => islossless F.f => islossless DRestr(D, F, P).distinguish.
proof.
  move=> D_ll F P p_ll pi_ll f_ll;proc.
  call (D_ll (DFRestr(F)) (DPRestr(P)) _ _ _).
  + by apply (rp_ll P). + by apply (rpi_ll P). + by apply (rf_ll F). 
  by inline *;auto.
qed.

section RESTR. 

  declare module F:FUNCTIONALITY{C}.
  declare module P:PRIMITIVE{C,F}.
  declare module D:DISTINGUISHER{F,P,C}.

  lemma swap_restr &m: 
    Pr[Indif(FRestr(F), PRestr(P), D).main()@ &m: res] =
    Pr[Indif(F,P,DRestr(D)).main()@ &m: res].
  proof.
    byequiv=>//;auto.
    proc;inline *;wp. 
    swap{1}[1..2] 3;sim;auto;call(:true);auto. 
  qed.

end section RESTR.

section COUNT.

  declare module P:PRIMITIVE{C}.
  declare module CO:CONSTRUCTION{C,P}.
  declare module D:DISTINGUISHER{C,P,CO}.

  axiom f_ll  : islossless P.f.
  axiom fi_ll : islossless P.fi.

  axiom CO_ll : islossless CO(P).f.

  axiom D_ll (F <: DFUNCTIONALITY{D}) (P <: DPRIMITIVE{D}):
    islossless P.f => islossless P.fi => islossless F.f => 
    islossless D(F, P).distinguish.

  lemma Pr_restr &m : 
    Pr[Indif(FC(CO(P)), PC(P), D).main()@ &m:res /\ C.c <= max_size] <= 
    Pr[Indif(CO(P), P, DRestr(D)).main()@ &m:res].
  proof.
    byequiv (_: ={glob D, glob P, glob CO} ==> C.c{1} <= max_size => ={res})=>//;
      2:by move=> ??H[]?/H<-.
    symmetry;proc;inline *;wp.
    call (_: max_size < C.c, ={glob P, glob CO, glob C}).
    + apply D_ll.
    + proc; sp;if{1};1:by auto;call(_:true);auto. 
      by auto;call{2} f_ll;auto=>/#. 
    + by move=> ?_;proc;sp;auto;if;auto;call f_ll;auto.
    + by move=> _;proc;sp;auto;call f_ll;auto=>/#.
    + proc;sp;auto;if{1};1:by auto;call(_:true);auto.
      by call{2} fi_ll;auto=>/#. 
    + by move=> ?_;proc;sp;auto;if;auto;call fi_ll;auto.
    + by move=> _;proc;sp;auto;call fi_ll;auto=>/#.
    + proc;inline*;sp 1 1;if;auto;if{1};auto;1:by call(_: ={glob P});auto;sim.
      by call{2} CO_ll;auto=>/#.
    + by move=> ?_;proc;sp;if;auto;if;auto;call CO_ll;auto.
    + by move=> _;proc;sp;if;auto;call CO_ll;auto;smt(prefixe_sizel).
    auto;call (_:true);auto;call(:true);auto=>/#.
  qed.

end section COUNT.

(* -------------------------------------------------------------------------- *)
(** Operators and properties of handles *)
op hinv (handles:handles) (c:capacity) = 
   find (fun _ => pred1 c \o fst) handles.

op hinvK (handles:handles) (c:capacity) = 
   find (fun _ => pred1 c) (restr Known handles).

op huniq (handles:handles) = 
  forall h1 h2 cf1 cf2, 
     handles.[h1] = Some cf1 => 
     handles.[h2] = Some cf2 => 
     cf1.`1 = cf2.`1 => h1 = h2.

lemma hinvP handles c:
  if hinv handles c = None then forall h f, handles.[h] <> Some(c,f)
  else exists f, handles.[oget (hinv handles c)] = Some(c,f).
proof.
  cut @/pred1@/(\o)/=[[h []->[]Hmem <<-]|[]->H h f]/= := 
    findP (fun (_ : handle) => pred1 c \o fst) handles.
  + by exists (oget handles.[h]).`2;rewrite oget_some get_oget;2:case (oget handles.[h]).
  cut := H h;rewrite in_dom/#.
qed.

lemma huniq_hinv (handles:handles) (h:handle): 
  huniq handles => mem (dom handles) h => hinv handles (oget handles.[h]).`1 = Some h.
proof.
  move=> Huniq;pose c := (oget handles.[h]).`1.
  cut:=Huniq h;cut:=hinvP handles c.
  case (hinv _ _)=> /=[Hdiff _| h' +/(_ h')];1:by rewrite in_dom /#.
  by move=> [f ->] /(_ (oget handles.[h]) (c,f)) H1 H2;rewrite H1 // get_oget.
qed.

lemma hinvKP handles c:
  if hinvK handles c = None then forall h, handles.[h] <> Some(c,Known)
  else handles.[oget (hinvK handles c)] = Some(c,Known).
proof.
  rewrite /hinvK.
  cut @/pred1/= [[h]|][->/=]:= findP (+ pred1 c) (restr Known handles).
  + by rewrite oget_some in_dom restrP;case (handles.[h])=>//= /#.
  by move=>+h-/(_ h);rewrite in_dom restrP => H1/#. 
qed.

lemma huniq_hinvK (handles:handles) c: 
  huniq handles => mem (rng handles) (c,Known) => handles.[oget (hinvK handles c)] = Some(c,Known).
proof.
  move=> Huniq;rewrite in_rng=> -[h]H;case: (hinvK _ _) (Huniq h) (hinvKP handles c)=>//=.
  by move=>_/(_ h);rewrite H.
qed.

lemma huniq_hinvK_h h (handles:handles) c: 
  huniq handles => handles.[h] = Some (c,Known) => hinvK handles c = Some h.
proof.
  move=> Huniq;case: (hinvK _ _) (hinvKP handles c)=>/= [H|h'];1: by apply H. 
  by rewrite oget_some=> /Huniq H/H. 
qed.

(* -------------------------------------------------------------------------- *)
(** The initial Game *)
module GReal(D:DISTINGUISHER) = RealIndif(SqueezelessSponge, PC(Perm), D).
