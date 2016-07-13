
(** This is a theory for the Squeezeless sponge: where the ideal
    functionality is a fixed-output-length random oracle whose output
    length is the input block size. We prove its security even when
    padding is not prefix-free. **)
require import Pred Fun Option Pair Int Real StdOrder Ring.
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
  proof * by exact Block.DWord.bdistr_ll.

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

(*
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
+ by rewrite anda_and; split=> [!~#] <*>; [exact/Empty|move=> [] /#].
rewrite -{1}cats1 foldl_cat {1}/step_hpath /=.
case: {-1}(foldl _ _ _) (eq_refl (foldl (step_hpath mh) (Some (b0,0)) p))=> //=.
+ apply/NewLogic.implybN; case=> [/#|p' b0 v' h'].
  move=> ^/rconssI <<- {p'} /rconsIs ->> {b}.
  by rewrite /build_hpath=> ->.
move=> [v' h']; rewrite oget_some /= -/(build_hpath _ _)=> build. 
split.
+ by move=> mh__; apply/(Extend mh (rcons p b) v h p b v' h' _ build mh__).
case=> [/#|] p' b' v'' h'' ^/rconssI <<- {p'} /rconsIs <<- {b'}.
by rewrite build /= => [#] <*>.
qed.
*)

lemma build_hpathP mh p v h: 
  build_hpath mh p = Some (v, h) <=>
  (p = [] /\ v=b0 /\ h=0) \/ 
  exists p' b v' h',  
    p = rcons p' b /\ build_hpath mh p' = Some(v',h') /\ mh.[(v'+^b, h')] = Some(v,h).
proof. (* this is not an induction, but only a case analysis *)
elim/last_ind: p v h => //= [v h|p b _ v h].
+ by rewrite /build_hpath /= anda_and; split=> [!~#] <*>; [left|move=> [] /#].
rewrite -{1}cats1 foldl_cat /= -/(build_hpath _ _) /=.
have -> /=: rcons p b <> [] by smt (). (* inelegant -- need lemma in List.ec *)
case: {-1}(build_hpath _ _) (eq_refl (build_hpath mh p))=> //=.
+ by rewrite /step_hpath //= NewLogic.implybN=> -[] p' b0 b' h' [#] /rconssI <*> ->.
move=> [v' h'] build_path; split=> [step_path|[] p' b' v'' h''].
+ by exists p, b, v', h'.
by move=> [#] ^/rconssI <<- /rconsIs <<-; rewrite build_path=> ->.
qed.

(* -------------------------------------------------------------------------- *)

module C = {
  var c:int
  proc init () = { c <- 0; }
}.

module PC (P:PRIMITIVE) = {

  proc init () = {
    C.init();
    P.init();
  }

  proc f (x:state) = {  
    var y;
    C.c <- C.c + 1;
    y     <@ P.f(x);
    return y;
  }

  proc fi(x:state) = {
    var y;
    C.c <- C.c + 1;
    y     <@ P.fi(x);
    return y;
  } 

}.

module DPRestr (P:DPRIMITIVE) = {

  proc f (x:state) = {  
    var y=(b0,c0);
    if (C.c + 1 <= max_size) {
      C.c <- C.c + 1;
      y     <@ P.f(x);
    }
    return y;
  }

  proc fi(x:state) = {
    var y=(b0,c0);
    if (C.c + 1 <= max_size) {
      C.c <- C.c + 1;
      y     <@ P.fi(x);
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
    var b= b0;
    C.c <- C.c + size bs;
    b <@ F.f(bs);
    return b;
  }
}.

module DFRestr(F:DFUNCTIONALITY) = {

  proc f (bs:block list) = {
    var b= b0;
    if (C.c + size bs <= max_size) {
      C.c <- C.c + size bs;
      b <@ F.f(bs);
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

lemma rp_ll (P<:DPRIMITIVE): islossless P.f => islossless DPRestr(P).f.
proof. move=>Hll;proc;sp;if=>//;call Hll;auto. qed.

lemma rpi_ll (P<:DPRIMITIVE): islossless P.fi => islossless DPRestr(P).fi.
proof. move=>Hll;proc;sp;if=>//;call Hll;auto. qed.

lemma rf_ll (F<:DFUNCTIONALITY): islossless F.f => islossless DFRestr(F).f.
proof. move=>Hll;proc;sp;if=>//;call Hll;auto. qed.

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
    proc;inline *;wp;swap{1}1 2;sim. 
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
    + proc; sp 1 0;if{1};1:by call(_:true);auto. 
      by call{2} f_ll;auto=>/#. 
    + by move=> ?_;proc;sp;if;auto;call f_ll;auto.
    + by move=> _;proc;call f_ll;auto=>/#.
    + proc;sp 1 0;if{1};1:by call(_:true);auto.
      by call{2} fi_ll;auto=>/#. 
    + by move=> ?_;proc;sp;if;auto;call fi_ll;auto.
    + by move=> _;proc;call fi_ll;auto=>/#.
    + proc;sp 1 0;if{1};1:by call(_: ={glob P});auto;sim.
      by call{2} CO_ll;auto=>/#.
    + by move=> ?_;proc;sp;if;auto;call CO_ll;auto.
    + move=> _;proc;call CO_ll;auto;smt ml=0 w=size_ge0. 
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
  by rewrite -not_def=> Heq; cut := H h;rewrite in_dom Heq.
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
  by move=>+h-/(_ h);rewrite in_dom restrP -!not_def=> H1 H2;apply H1;rewrite H2. 
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


