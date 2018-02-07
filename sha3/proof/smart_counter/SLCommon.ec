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

(** We can now define the squeezeless sponge construction **)
module SqueezelessSponge (P:DPRIMITIVE): FUNCTIONALITY = {
  proc init () = {} 

  proc f(p : block list): block = {
    var (sa,sc) <- (b0,c0);

    while (p <> []) { (* Absorption *)
      (sa,sc) <@ P.f((sa +^ head witness p,sc));
      p <- behead p;
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


pred prefixe_inv (queries : (block list, block) fmap)
               (m : (state, state) fmap) =
  forall (bs : block list),
    bs \in dom queries =>
    forall i, 0 <= i < size bs =>
      let bc  = (blocksponge (take i bs) m s0).`2 in
      (bc.`1 +^ nth b0 bs i, bc.`2) \in dom m.



lemma prefixe_inv_bs_fst_nil queries m :
    prefixe_inv queries m =>
    forall l, l \in dom queries =>
    forall i, 0 <= i <= size l =>
    (blocksponge (take i l) m s0).`1 = [].
proof.
move=>Hinv l Hdom i [Hi0 Hisize];move:i Hi0 l Hisize Hdom;apply intind=>//=.
+ by move=>l;rewrite take0/=.
move=>i Hi0 Hind l Hil Hldom.
rewrite(take_nth b0)1:/#.
rewrite blocksponge_rcons/=.
cut->/=:=Hind l _ Hldom;1:rewrite/#.
by cut/=->/=:=Hinv _ Hldom i _;1:rewrite/#.
qed.


lemma prefixe_inv_set queries m x y :
    !x \in dom m =>
    prefixe_inv queries m =>
    prefixe_inv queries m.[x <- y].
proof.
move=>Hxdom Hpref bs/=Hbsdom i [Hi0 Hisize].
cut->:blocksponge (take i bs) m.[x <- y] s0 = blocksponge (take i bs) m s0.
+ move:i Hi0 bs Hisize Hbsdom;apply intind=>//=i;first by rewrite take0//=.
  move=>Hi0 Hind bs Hsize Hbsdom.
  rewrite (take_nth b0)1:/#.
  rewrite 2!blocksponge_rcons/=.
  cut->/=:=prefixe_inv_bs_fst_nil _ _ Hpref _ Hbsdom i _;1:rewrite/#.
  cut/=->/=:=Hpref _ Hbsdom i _;1:rewrite/#.
  cut->/=:=Hind bs _ Hbsdom;1:rewrite/#.
  cut->/=:=prefixe_inv_bs_fst_nil _ _ Hpref _ Hbsdom i _;1:rewrite/#.
  rewrite dom_set in_fsetU1.
  cut/=->/=:=Hpref _ Hbsdom i _;1:rewrite/#.
  rewrite getP.
  cut/#:=Hpref _ Hbsdom i _;1:rewrite/#.
rewrite dom_set in_fsetU1.
cut/#:=Hpref _ Hbsdom i _;1:rewrite/#.
qed.


lemma blocksponge_set_nil l m bc x y :
    !x \in dom m =>
    let bs1 = blocksponge l m bc in
    let bs2 = blocksponge l m.[x <- y] bc in
    bs1.`1 = [] =>
    bs2 = ([], bs1.`2).
proof.
rewrite/==>hdom bs1.
cut/=:=blocksponge_set l m bc x y.
smt(size_ge0 size_eq0).
qed.

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
  var m  : (state, state) fmap
  var mi : (state, state) fmap
  var queries : (block list, block) fmap
  proc init () = { 
    c       <- 0;
    m       <- map0;
    mi      <- map0;
    queries <- map0;
  }
}.

module PC (P:PRIMITIVE) = {

  proc init () = {
    C.init();
    P.init();
  }

  proc f (x:state) = {  
    var y <- (b0,c0);
    if (!x \in dom C.m) {
      y        <@ P.f(x);
      C.c      <- C.c + 1;
      C.m.[x]  <- y;
      if (! y \in dom C.mi) {
        C.mi.[y] <- x;
      }
    } else {
      y        <- oget C.m.[x];
    }
    return y;
  }

  proc fi(x:state) = {
    var y <- (b0,c0);
    if (!x \in dom C.mi) {
      y        <@ P.fi(x);
      C.c      <- C.c + 1;
      C.mi.[x] <- y;
      if (! y \in dom C.m) {
        C.m.[y]  <- x;
      }
    } else {
      y        <- oget C.mi.[x];
    }
    return y;
  } 

}.

module DPRestr (P:DPRIMITIVE) = {

  proc f (x:state) = {  
    var y <- (b0,c0);
    if (!x \in dom C.m) {
      if (C.c + 1 <= max_size) {
        y        <@ P.f(x);
        C.c      <- C.c + 1;
        C.m.[x]  <- y;
        if (! y \in dom C.mi) {
          C.mi.[y] <- x;
        }
      }
    } else {
      y          <- oget C.m.[x];
    }
    return y;
  }

  proc fi(x:state) = {
    var y <- (b0,c0);
    if (!x \in dom C.mi) {
      if (C.c + 1 <= max_size) {
        y        <@ P.fi(x);
        C.c      <- C.c + 1;
        C.mi.[x] <- y;
        if (! y \in dom C.m) {
          C.m.[y]  <- x;
        }
      }
    } else {
      y          <- oget C.mi.[x];
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

  proc init = F.init

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

  proc init = F.init

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
proof. move=>Hll;proc;sp;if;auto;if;auto;call Hll;auto. qed.

lemma rpi_ll (P<:DPRIMITIVE{C}): islossless P.fi => islossless DPRestr(P).fi.
proof. move=>Hll;proc;sp;if;auto;if;auto;call Hll;auto. qed.

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
    byequiv=>//.
    proc;inline *;wp;swap{1}1 2;sim;auto;call(:true);auto;call(:true);auto. 
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
    symmetry;proc;inline *;wp;swap{2}1 2.
    call (_: max_size < C.c, ={glob P, glob CO, glob C}).
    + apply D_ll.
    + proc; sp;if;auto;if{1};1:by auto;call(_:true);auto. 
      by call{2} f_ll;auto=>/#. 
    + by move=> ?_;proc;sp;if;auto;if;auto;call f_ll;auto.
    + by move=> _;proc;sp;if;auto;call f_ll;auto=>/#.
    + proc;sp;if;auto;if{1};1:by auto;call(_:true);auto.
      by call{2} fi_ll;auto=>/#. 
    + by move=> ?_;proc;sp;if;auto;if;auto;call fi_ll;auto.
    + by move=> _;proc;sp;if;auto;call fi_ll;auto=>/#.
    + proc;inline*;sp 1 1;if;auto;if{1};auto;1:by call(_: ={glob P});auto;sim.
      by call{2} CO_ll;auto=>/#.
    + by move=> ?_;proc;sp;if;auto;if;auto;call CO_ll;auto.
    + by move=> _;proc;sp;if;auto;call CO_ll;auto;smt(prefixe_sizel).
    wp;call (_:true);call(_:true);auto=>/#.
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
