
(** This is a theory for the Squeezeless sponge: where the ideal
    functionality is a fixed-output-length random oracle whose output
    length is the input block size. We prove its security even when
    padding is not prefix-free. **)
require import Pred Fun Option Pair Int Real StdOrder Ring.
require import List FSet NewFMap Utils Common.

require (*..*) RndOrcl Indifferentiability.
(*...*) import Dprod Dexcepted Capacity IntOrder.

type state  = block  * capacity.
op   dstate = bdistr * cdistr.


clone include Indifferentiability with
  type p     <- state, 
  type f_in  <- block list,
  type f_out <- block
  rename [module] "GReal" as "RealIndif"
         [module] "GIdeal"  as "IdealIndif".


(** max number of call to the permutation and its inverse, 
    including those performed by the construction. *)
op max_size : int.

(** Ideal Functionality **)
clone export Tuple as TupleBl with
  type t <- block,
  op Support.enum <- Block.words
  proof Support.enum_spec by exact Block.enum_spec. 

op bl_enum = flatten (mkseq (fun i => wordn i) (max_size + 1)). 
op bl_univ = FSet.oflist bl_enum.

clone RndOrcl as RndOrclB with 
  type from <- block list,
  type to   <- block.
 
clone export RndOrclB.RestrIdeal as Functionality with
  op sample _ <- bdistr,
  op test l   <- List.size l <= max_size,
  op univ     <- bl_univ,
  op dfl      <- b0
  proof *.
realize sample_ll by exact Block.DWord.bdistr_ll.
realize testP.
proof.
  move=> x; rewrite mem_oflist-flattenP; split=>[_|[s[/mkseqP[i[/=_->>]]/wordnP->/#]]].
  exists (wordn (size x));cut Hsx := size_ge0 x.
  rewrite wordnP max_ler //= mkseqP /=;exists (size x);smt ml=0.
qed.

(** We can now define the squeezeless sponge construction **)
module SqueezelessSponge (P:DPRIMITIVE): FUNCTIONALITY = {
  proc init () = {} 

  proc f(p : block list): block = {
    var (sa,sc) <- (b0,c0);

    if (1 <= size p /\ p <> [b0]) {
      while (p <> []) { (* Absorption *)
        (sa,sc) <@ P.f((sa +^ head witness p,sc));
        p <- behead p;
      }
    }
    return sa;          (* Squeezing phase (non-iterated) *)
  }
}.

clone export Pair.Dprod.Sample as Sample2 with 
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

type caller = [ I | D ].

type handle  = int.

type hstate = block * handle.
 
type ccapacity = capacity * caller.

type smap    = (state , state    ) fmap.
type hsmap   = (hstate, hstate   ) fmap.
type handles = (handle, ccapacity) fmap.

(* Did we use it? *)
op (<=) (o1 o2 : caller) = o1 = I \/ o2 = D.

(* Did we use it? *)
op max (o1 o2 : caller) =
  with o1 = I => o2
  with o1 = D => D.

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

(** Operators and properties of handles *)

op hinv (handles:handles) (c:capacity) = 
   find (fun _ => pred1 c \o fst) handles.

op hinvD (handles:handles) (c:capacity) = 
   find (fun _ => pred1 (c,D)) handles.

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

lemma hinvDP handles c:
  if hinvD handles c = None then forall h, handles.[h] <> Some(c,D)
  else handles.[oget (hinvD handles c)] = Some(c,D).
proof.
  cut @/pred1/=[[h []->[]Hmem ]|[]->H h ]/= := 
    findP (fun (_ : handle) => pred1 (c,D)) handles.
  + by rewrite oget_some get_oget.
  by rewrite -not_def=> Heq; cut := H h;rewrite in_dom Heq. 
qed.

lemma huniq_hinvD (handles:handles) c: 
  huniq handles => mem (rng handles) (c,D) => handles.[oget (hinvD handles c)] = Some(c,D).
proof.
  move=> Huniq;rewrite in_rng=> -[h]H;case: (hinvD _ _) (Huniq h) (hinvDP handles c)=>//=.
  by move=>_/(_ h);rewrite H.
qed.

lemma huniq_hinvD_h h (handles:handles) c: 
  huniq handles => handles.[h] = Some (c,D) => hinvD handles c = Some h.
proof.
  move=> Huniq;case: (hinvD _ _) (hinvDP handles c)=>/= [H|h'];1: by apply H. 
  by rewrite oget_some=> /Huniq H/H. 
qed.

(* Functionnal version of the construction using handle *)

op step_hpath (mh:hsmap) (sah:hstate option) (b:block) = 
    if sah = None then None 
    else 
      let sah = oget sah in 
      mh.[(sah.`1 +^ b, sah.`2)].

op build_hpath (mh:hsmap) (bs:block list) = 
   foldl (step_hpath mh) (Some (b0,0)) bs.

lemma build_hpathP mh p v h: 
  build_hpath mh p = Some (v, h) =>
  (p = [] /\ v=b0 /\ h=0) \/ 
  exists p' b v' h',  
    p = rcons p' b /\ build_hpath mh p' = Some(v',h') /\ mh.[(v'+^b, h')] = Some(v,h).
proof.
  elim/last_ind:p=>@/build_hpath //= p' b _. 
  rewrite -cats1 foldl_cat /= => H;right;exists p',b. 
  move:H;rewrite {1}/step_hpath;case (foldl _ _ _)=> //= -[v' h'].
  by rewrite oget_some /==>Heq; exists v',h';rewrite -cats1.
qed.


