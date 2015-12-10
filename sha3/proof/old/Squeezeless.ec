
(** This is a theory for the Squeezeless sponge: where the ideal
    functionality is a fixed-output-length random oracle whose output
    length is the input block size. We prove its security even when
    padding is not prefix-free. **)
require import Pred Fun Option Pair Int Real List FSet NewFMap Utils Common.

require (*..*) RndOrcl Indifferentiability.
(*...*) import Dprod Dexcepted Capacity.

type state  = block  * capacity.
op   dstate = bdistr * cdistr.


clone include Indifferentiability with
  type p     <- state, 
  type f_in  <- block list,
  type f_out <- block
  rename [module] "GReal" as "RealIndif"
         [module] "GIdeal"  as "IdealIndif".


(* max number of call to the permutation and its inverse *)
op max_size : int.

(** Ideal Functionality **)
clone import Tuple as TupleBl with
  type t <- block,
  op Support.enum <- Block.words
  proof Support.enum_spec by exact Block.enum_spec. 

op bl_enum = flatten (mkseq (fun i => wordn i) (max_size + 1)). 
op bl_univ = FSet.oflist bl_enum.

clone RndOrcl as RndOrclB with 
  type from <- block list,
  type to   <- block.
 
clone import RndOrclB.RestrIdeal as Functionality with
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
module SqueezelessSponge (P:PRIMITIVE): CONSTRUCTION(P), FUNCTIONALITY = {
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

module Count = { var c:int }.

module DCount (D:DISTINGUISHER, F:DFUNCTIONALITY, P:DPRIMITIVE) = {

  module Fc = { 
    proc f (bs:block list) = {
      var b;
      Count.c <- Count.c + size bs;
      b     <@ F.f(bs);
      return b;
    }
  }

  module Pc = {
    proc f (x:state) = {
      var y;
      Count.c <- Count.c + 1;
      y     <@ P.f(x);
      return y;
    }

    proc fi(x:state) = {
      var y;
      Count.c <- Count.c + 1;
      y     <@ P.fi(x);
      return y;
    } 
  }

  proc distinguish = D(Fc,Pc).distinguish

}.

module DRestr (D:DISTINGUISHER, F:DFUNCTIONALITY, P:DPRIMITIVE) = {
  var count:int

  module Fc = { 
    proc f (bs:block list) = {
      var b = b0;
      if (Count.c + size bs <= max_size) {
        Count.c <- Count.c + size bs;
        b     <@ F.f(bs);
      }
      return b;
    }
  }

  module Pc = {
    proc f (x:state) = {
      var y;
      if (
      count <- count + 1;
      y     <@ P.f(x);
      return y;
    }

    proc fi(x:state) = {
      var y;
      count <- count + 1;
      y     <@ P.fi(x);
      return y;
    } 
  }

  proc distinguish = D(Fc,Pc).distinguish

}.




module type DPRIMITIVE = {
  proc f(x : p): p
  proc fi(x : p): p
}.

module type FUNCTIONALITY = {
  proc init(): unit
  proc f(x : f_in): f_out
}.

module type DFUNCTIONALITY = {
  proc f(x : f_in): f_out
}.


  (** Result (expected): The distance between Concrete and Concrete_F
      is bounded by N^2/|state|, where N is the total cost (in terms
      of queries to P and P^-1) of the adversary's queries **)

                 (** TODO: express and prove **)

  (** And now for the interesting bits **)
  (** Inform the primitive interface of queries made by the
      distinguisher on its functionality interface, keep track of
      primitive call paths in a coloured graph. **)
  (** The following invariants should always hold at adversary
      boundaries (they may be violated locally, but should always be
      fixed (say, by setting bad) before returning control, and the
      adversary should not be able to violate them himself):
        - if paths[x] = (_,(p,v)), then following path p through m
          from (0^r,0^c) leads to state (v,x); (in particular, this
          implies (v,x) \in rng m;
        - unless bad occurs (identify which ones), for every sc, there
          is at most one sa such that (sa,sc) \in rng m;
        - unless bad occurs (identify which ones), if paths[x] =
          (o,(p,_)) and paths[x'] = (o',(p++p',_)), then o' <= o;
          (todo: maybe change the direction of that order relation so
          it corresponds to "order of appearance along paths"?)

      The next step in the proof will probably be to eagerly sample
      all values of the rate and introduce some indirection on
      capacities so that they are only sampled (and propagated) just
      before being given to the adversary. This is easier to do if all
      samplings are independent, hence the move away from a random
      permutation. Some side-effects remain worrying.
   **)
  type caller = [ I | D ].

  op (<=) (o1 o2 : caller) = o1 = I \/ o2 = D.

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

  type handle  = int.

  type hstate = block * handle.
 
  type ccapacity = capacity * caller.

  type smap    = (state , state    ) fmap.
  type hsmap   = (hstate, hstate   ) fmap.
  type handles = (handle, ccapacity) fmap.

lemma get_oget (m:('a,'b)fmap) (x:'a) : mem (dom m) x => m.[x] = Some (oget m.[x]).
proof. by rewrite in_dom;case (m.[x]). qed.

lemma find_set (m:('a,'b) fmap) y x (p:'a -> 'b -> bool):
  (forall x, mem (dom m) x => !p x (oget m.[x])) =>
  find p m.[x <- y] = if p x y then Some x else None.
proof.
  cut [[a []->[]] | []-> Hp Hnp]:= findP p (m.[x<-y]);1: rewrite getP dom_set !inE /#. 
  by case (p x y)=> //; cut := Hp x;rewrite getP dom_set !inE /= oget_some.
qed.

require import StdOrder IntOrder.
require import Ring.

  (* Operators and properties of handles *)
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

 


















op check_hpath (mh:(hstate, hstate) fmap) (handles:(handle, ccapacity) fmap) (xs:block list) (c:capacity) = 
  obind (fun (sah:hstate) => if c = sah.`2 then Some sah.`1 else None)
        (build_hpath mh xs).

  if sah <> None then
   
  else None 

hpath 
  let step = fun (sah:hstate option ) (x:block) => 
    if sah = None then None 
    else 
      let sah = oget sah in 
       mh.[(sah.`1 +^ x, sah.`2)] in
  foldl step (Some (b0,0)) xs.







fun sah => mh.fun (sah:hstate) (cont=>
             if mem


op INV2 (m mi:(state , state ) fmap) (mh mhi:(hstate, hstate) fmap) (handles:(handle, ccapacity) fmap) chandle = 
  dom mh = rng mhi /\ dom mhi = rng mh /\ 
  (forall xh, mem (dom mh `|` rng mh) xh => mem (dom handles) xh.`2) /\ 
  (forall h, mem (dom handles) h => h < chandle) /\
  (forall xh,  mem (dom mh) xh => mem (dom m) (xh.`1, (oget handles.[xh.`2]).`1) \/ (oget handles.[xh.`2]).`2 = I) /\
  (forall xh,  mem (dom mhi) xh => mem (dom mi) (xh.`1, (oget handles.[xh.`2]).`1) \/ (oget handles.[xh.`2]).`2 = I).


lemma hinvD_rng x (handles:(handle, ccapacity) fmap):
   mem (rng handles) (x, D) =>
                  handles.[oget (hinvD handles x)]= Some(x, D).
proof.
  cut[ [a []->[]] | []->/=Hp ]/=:= findP (fun _ z => z = (x, D)) handles.
  + by rewrite oget_some=> ? <- _;apply get_oget.
  by rewrite in_rng=> -[a Ha];cut := Hp a; rewrite in_dom Ha oget_some. 
qed.

(* TODO: change the name *)
lemma map_perm (m mi: ('a, 'a) fmap) x y: !mem (dom mi) y => dom m = rng mi => dom m.[x<-y] = rng mi.[y<- x].
proof.
  move=> Hdom Heq;rewrite fsetP=> w;rewrite dom_set in_rng !inE;split.
  + rewrite Heq in_rng. case (w=x)=> -[->|Hneq/=[a Ha]];1:by exists y;rewrite getP. 
    exists a;rewrite getP;case (a=y)=>[->>|//].
    by move:Hdom;rewrite in_dom Ha.
  rewrite Heq in_rng;by move=>[a];rewrite getP;case(a=y)=>[->>/# |_ <-];left;exists a.
qed.

local hoare test_f : G2.S.f : INV2 G2.m G2.mi G2.mh G2.mhi G2.handles G2.chandle (*/\  INV2 G2.mi G2.mhi G2.handles*) ==>
                              INV2 G2.m G2.mi G2.mh G2.mhi G2.handles G2.chandle.
proof.
  proc;if;last by auto.
  auto;conseq (_ :_ ==> true)=> //.
  move=> &hr [][]Hmhmhi[]Hmhimh[]Hdomh[]Hhbound[]Hmhor Hmhior Hnmem y _;split;beta iota.
  + move=> Hnrng handles chandle hx2 @/handles.
    cut ->>{hx2} : hx2 = G2.chandle{hr}.  
    + rewrite /hx2 /handles /hinvD find_set /pred1 //=.
      move=> x2 Hx2;cut := Hnrng;rewrite in_rng NewLogic.negb_exists /= => /(_ x2).
      by rewrite get_oget.
    split=> /= [[Hmem _] | Hmem]. 
    + by cut /Hhbound // := Hdomh (x{hr}.`1, G2.chandle{hr}) _; rewrite inE;left.
    do !apply andI. 
    + apply map_perm=> //;rewrite -not_def=> H.
      by cut /#:= Hhbound chandle _;apply (Hdomh (y.`1,chandle));rewrite !inE -Hmhimh H.
    + apply map_perm=> //;rewrite -not_def=> H.
      by cut /#:= Hhbound G2.chandle{hr} _;apply (Hdomh (x{hr}.`1,G2.chandle{hr}));rewrite !inE H. 
    + move=>[x1 h];cut := Hdomh (x1,h).
      rewrite !(dom_set, rng_set, inE) /==>H1 [[H2|[_->]]|[/rng_rem_le H2|[_->]]]//;
      by rewrite H1 ?H2.
    + by move=> h;cut := Hhbound h;rewrite !dom_set !inE /= => H [[/H|]|->>]/#.
    + move=>[x1 h];rewrite !getP !dom_set !inE /==> -[|[]->> ->>];rewrite /chandles /=.
      + move=>Hh. cut /Hhbound/=:= Hdomh (x1,h) _;1:by rewrite !inE Hh.
        move=> ^Hlt /IntOrder.gtr_eqF; rewrite eq_sym=>->.
        by cut ->/#: h <> G2.chandle{hr} + 1 by smt ml=0.
      cut ->/=: G2.chandle{hr} <> G2.chandle{hr} + 1 by smt ml=0.
      by rewrite oget_some /#. 
     move=>[x1 h];rewrite !getP !dom_set !inE /==> -[|[]->> ->>];rewrite /chandles /=.
     + move=>Hh; cut /Hhbound/=:= Hdomh (x1,h) _;1:by rewrite !inE -Hmhimh Hh.
       move=> ^Hlt /IntOrder.gtr_eqF; rewrite eq_sym=>->.
       by cut ->/#: h <> G2.chandle{hr} + 1 by smt ml=0.
     by rewrite oget_some /#.
  move=> /= Hrng;cut Hget:= hinvD_rng _ _ Hrng;split=> /=.
  + move=> []/Hmhor /= [] ; rewrite Hget oget_some /#.
  move=> Hnot;do !apply andI. 
  + apply map_perm=> //;rewrite -not_def=> H.
    by cut /#:= Hhbound G2.chandle{hr} _;apply (Hdomh (y.`1,G2.chandle{hr}));
       rewrite !inE -Hmhimh H.
  + apply map_perm=> //;rewrite -not_def=> H.
    by cut := Hmhor _ H;move: Hnmem;rewrite Hget oget_some /=;case (x{hr}).
  + move=> [x1 h];rewrite !(dom_set,rng_set, inE) => -[[H|[_ ->]]| [/rng_rem_le H|[_->]]]//=.
    + by left;apply (Hdomh (x1,h));rewrite inE H.
    + by left;rewrite in_dom Hget.
    by left;apply (Hdomh (x1,h));rewrite inE H.
  + by move=>h;rewrite dom_set !inE=> -[/Hhbound|->]/#. 
  + move=> [x1 h];rewrite !(dom_set, getP, inE) /==> -[H|[->> ->>]].
    + by cut /IntOrder.ltr_eqF->/#:= Hhbound h _;1:by apply (Hdomh (x1,h));rewrite inE H.
    cut ->/=:oget (hinvD G2.handles{hr} x{hr}.`2) <> G2.chandle{hr}.
    + by cut /#:= Hhbound (oget (hinvD G2.handles{hr} x{hr}.`2)) _;1:by rewrite in_dom Hget.
    by rewrite Hget oget_some /=;right;case (x{hr}).
  move=> [x1 h];rewrite !(dom_set, getP, inE) /==> -[H|[->> ->> /=]].
  + by cut /IntOrder.ltr_eqF->/#:= Hhbound h _;1: apply (Hdomh (x1,h));rewrite inE -Hmhimh H.
  by rewrite oget_some /=;right;case y.
qed.

local hoare test_fi : G2.S.fi : INV2 G2.m G2.mi G2.mh G2.mhi G2.handles G2.chandle  ==>
                                INV2 G2.m G2.mi G2.mh G2.mhi G2.handles G2.chandle.
proof.
  proc;if;last by auto.
  auto.  move=> &hr [][]Hmhmhi[]Hmhimh[]Hdomh[]Hhbound[]Hmhor Hmhior Hnmem;split;beta iota.
  + move=> Hnrng handles chandle hx2 @/handles y Hy.
    cut ->>{hx2} : hx2 = G2.chandle{hr}.  
    + rewrite /hx2 /handles /hinvD find_set /pred1 //=.
      move=> x2 Hx2;cut := Hnrng;rewrite in_rng NewLogic.negb_exists /= => /(_ x2).
      by rewrite get_oget.
    split=> /= [[Hmem _] | Hmem]. 
    + by cut /Hhbound // := Hdomh (x{hr}.`1, G2.chandle{hr}) _;rewrite inE -Hmhimh;right.
    do !apply andI. 
    + apply map_perm=> //;rewrite -not_def=> H.
      by cut /#:= Hhbound G2.chandle{hr} _;apply (Hdomh (x{hr}.`1,G2.chandle{hr}));
         rewrite !inE -Hmhimh H.
    + apply map_perm=> //;rewrite -not_def=> H.
      by cut /#:= Hhbound chandle _;apply (Hdomh (y.`1,chandle));rewrite !inE -Hmhimh H.
    + move=>[x1 h];cut := Hdomh (x1,h).
      rewrite !(dom_set, rng_set, inE) /==>H1 [[H2|[_->]]|[/rng_rem_le H2|[_->]]]//;
      by rewrite H1 ?H2.
    + by move=> h;cut := Hhbound h;rewrite !dom_set !inE /= => H [[/H|]|->>]/#.
    + move=>[x1 h];rewrite !getP !dom_set !inE /==> -[|[]->> ->>];rewrite /chandles /=.
      + move=>Hh; cut /Hhbound/=:= Hdomh (x1,h) _;1:by rewrite !inE -Hmhimh Hh.
        move=> ^Hlt /IntOrder.gtr_eqF; rewrite eq_sym=>->.
        by cut ->/#: h <> G2.chandle{hr} + 1 by smt ml=0.
      by rewrite oget_some /#.
    move=>[x1 h];rewrite !getP !dom_set !inE /==> -[|[]->> ->>];rewrite /chandles /=.
    + move=>Hh;cut /Hhbound/=:= Hdomh (x1,h) _;1:by rewrite !inE -Hmhimh Hh.
      move=> ^Hlt /IntOrder.gtr_eqF; rewrite eq_sym=>->.
      by cut ->/#: h <> G2.chandle{hr} + 1 by smt ml=0.
    cut ->/=: G2.chandle{hr} <> G2.chandle{hr} + 1 by smt ml=0.
    by rewrite oget_some /#. 
  move=> /= Hrng y Hy;cut Hget:= hinvD_rng _ _ Hrng;split=> /=.
  + move=> []/Hmhior /= [] ; rewrite Hget oget_some /#.
  move=> Hnot;do !apply andI. 
  + apply map_perm=> //;rewrite -not_def=> H.
    by cut := Hmhior _ H;move: Hnmem;rewrite Hget oget_some /=;case (x{hr}).
  + apply map_perm=> //;rewrite -not_def=> H.
    by cut /#:= Hhbound G2.chandle{hr} _;apply (Hdomh (y.`1,G2.chandle{hr}));
       rewrite !inE -Hmhimh H.
  + move=> [x1 h];rewrite !(dom_set,rng_set, inE) => -[[H|[_ ->]]| [/rng_rem_le H|[_->]]]//=.
    + by left;apply (Hdomh (x1,h));rewrite inE H.
    + by left;apply (Hdomh (x1,h));rewrite inE H.
    by left;rewrite in_dom Hget.
  + by move=>h;rewrite dom_set !inE=> -[/Hhbound|->]/#. 
  + move=> [x1 h];rewrite !(dom_set, getP, inE) /==> -[H|[->> ->> /=]].
    + by cut /IntOrder.ltr_eqF->/#:= Hhbound h _;1: apply (Hdomh (x1,h));rewrite inE -Hmhimh H.
    by rewrite oget_some /==>{Hy};right;case y.
  move=> [x1 h];rewrite !(dom_set, getP, inE) /==> -[H|[->> ->>]].
  + by cut /IntOrder.ltr_eqF->/#:= Hhbound h _;1:apply (Hdomh (x1,h));rewrite inE -Hmhimh H.
  cut ->/=:oget (hinvD G2.handles{hr} x{hr}.`2) <> G2.chandle{hr}.
  + by cut /#:= Hhbound (oget (hinvD G2.handles{hr} x{hr}.`2)) _;1:by rewrite in_dom Hget.
  by rewrite Hget oget_some /=;right;case (x{hr}).
qed.

local hoare test_C : G2.C.f : INV2 G2.m G2.mi G2.mh G2.mhi G2.handles G2.chandle  ==>
                              INV2 G2.m G2.mi G2.mh G2.mhi G2.handles G2.chandle.
 

local module Game3 = {
    var m, mi               : (state , state ) fmap
    var mh, mhi             : (hstate, hstate) fmap
    var handles             : (handle, ccapacity) fmap
    var chandle             : int
    var paths               : (capacity, block list * block) fmap
    var bext                : bool


    module C = {
      proc init(): unit = { }

      proc f(p : block list): block = {
        var h, i <- 0; 
        var (sa,sc) <- (b0,c0);
        var sa';

        if (1 <= size p /\ p <> [b0]) {
          while (i < size p - 1 /\ mem (dom m) (sa +^ nth witness p i, sc)) {
            (sa, sc) <- oget m.[(sa +^ nth witness p i, sc)];
            (sa', h) <- oget mh.[(sa +^ nth witness p i, h)];
            i        <- i + 1;
          }
          while (i < size p) {
            sc                  <$ cdistr;
            sa'                 <- RO.f(take i p);
            mh.[(sa,h)]         <- (sa', chandle);
            mhi.[(sa',chandle)] <- (sa,h);
            (sa,h)              <- (sa',chandle);
            handles.[chandle]   <- (sc,I);
            chandle             <- chandle + 1;
            i                   <- i + 1;
          }
          sa <- RO.f(p);
        }
        return sa;
      }
    }

    module S = {
      (** Inner interface **)
      proc f(x : state): state = {
        var p, v, y, y1, y2, hy2, hx2;
  
        if (!mem (dom m) x) {
          if (mem (dom paths) x.`2) {
            (p,v) <- oget paths.[x.`2]; 
            y1    <- RO.f (rcons p (v +^ x.`1));
            y2    <$ cdistr;
            y     <- (y1, y2);
            paths.[y2] <- (rcons p (v +^ x.`1), y.`1);
          } else {
            y <$ dstate;
          }
          bext <- bext \/ mem (rng handles) (x.`2, I);   
            (*  exists x2 h, handles.[h] = Some (X2,I) *)
          if (!(mem (rng handles) (x.`2, D))) {
            handles.[chandle] <- (x.`2, D);
            chandle <- chandle + 1;
          }
          hx2 <- oget (hinvD handles x.`2);
          if (mem (dom mh) (x.`1, hx2)) {
            hy2               <- (oget mh.[(x.`1, hx2)]).`2;
            handles.[hy2]     <- (y.`2, D);
            (* bad               <- bad \/ mem X2 y.`2; *)
            m.[x]             <- y;
            mh.[(x.`1, hx2)]  <- (y.`1, hy2);
            mi.[y]            <- x;
            mhi.[(y.`1, hy2)] <- (x.`1, hx2);
          } else {
            hy2               <- chandle;
            chandle           <- chandle + 1;
            handles.[hy2]     <- (y.`2, D);
            m.[x]             <- y;
            mh.[(x.`1, hx2)]  <- (y.`1, hy2);
            mi.[y]            <- x;
            mhi.[(y.`1, hy2)] <- (x.`1, hx2);
          }
        } else {   
          y <- oget m.[x];
        }
        return y;
      }

      proc fi(x : state): state = {
        var y, y1, y2, hx2, hy2;

        if (!mem (dom mi) x) {
          bext <- bext \/ mem (rng handles) (x.`2, I);   
            (*  exists x2 h, handles.[h] = Some (X2,I) *)
          if (!(mem (rng handles) (x.`2, D))) {
            handles.[chandle] <- (x.`2, D);
            chandle <- chandle + 1;
          }
          hx2 <- oget (hinvD handles x.`2);
          if (mem (dom mhi) (x.`1, hx2)) {
            (y1,hy2)          <- oget mhi.[(x.`1, hx2)];
            y2                <$ cdistr;
            y                 <- (y1,y2);
            handles.[hy2]     <- (y.`2, D);
            (* bad               <- bad \/ mem X2 y.`2; *)
            mi.[x]            <- y;
            mhi.[(x.`1, hx2)] <- (y.`1, hy2);
            m.[y]             <- x;
            mh.[(y.`1, hy2)]  <- (x.`1, hx2);
          } else {
            y                 <$ dstate;
            hy2               <- chandle;
            chandle           <- chandle + 1;
            handles.[hy2]     <- (y.`2, D);
            mi.[x]            <- y;
            mhi.[(x.`1, hx2)] <- (y.`1, hy2);
            m.[y]             <- x;
            mh.[(y.`1, hy2)]  <- (x.`1, hx2);
          }
        } else {
          y <- oget mi.[x];
        }
        return y;
      }

      (** Distinguisher interface **)
      proc init() = { }

    }

  

    proc main(): bool = {
      var b;

      m        <- map0;
      mi       <- map0;
      bext     <- false;

      (* the empty path is initially known by the adversary to lead to capacity 0^c *)
      handles  <- map0.[0 <- (c0, D)];
      paths    <- map0.[c0 <- ([<:block>],b0)];
      chandle  <- 1;
      b        <@ D(C,S).distinguish();
      return b;
    }    
  }.




  local module Game1 = {
    var m, mi               : (hstate,hstate) fmap
    var paths               : (handle,(block list * block) list) fmap
    var handles             : (handle, ccapacity) fmap
    var bext, bred, bcoll   : bool
    var chandle             : int

    module S = {
      (** Inner interface **)
      proc fg(o : caller, x : state): state = {
        var o', p, v, y, y1, y2, ox2, hx2, y1h;
  
        ox2  <- hinv handles x.`2;
        hx2  <- oget ox2;
        bext <- bext \/ 
                (o = D /\ ox2 <> None  /\ paths.[hx2] <> None /\ 
                find_path m D paths hx2 = None);


        if (ox2 = None) {
           handles.[chandle] <- (x.`2,o);
           hx2               <- chandle;
           chandle           <- chandle + 1;
        }
        
        if (!mem (dom m) (x.`1, hx2) || (oget handles.[hx2]).`2 = I /\ o = D) { 
          if (mem (dom paths) hx2 /\ find_path m o paths hx2 <> None) {
            (p,v) <- oget (find_path m o paths hx2);
            y1    <- RO.f (rcons p (v +^ x.`1));
            y2    <$ cdistr;
            y     <- (y1, y2);
            if (hinv handles y.`2 = None) 
              paths.[chandle (*y2*)] <- extend_paths x.`1 y.`1 (oget paths.[hx2]);
          } else {
            y <$ dstate;
          }
          if (hinv handles y.`2 = None) {
            y1h               <- (y.`1, chandle);
            handles.[chandle] <- (y.`2, o);
            m.[(x.`1, hx2)]   <- y1h;
            mi.[y1h]          <- (x.`1, hx2);
            handles.[hx2]     <- (x.`2, max o (oget handles.[hx2]).`2);   (* Warning: not sure we want it *)
            chandle           <- chandle + 1;
          } else {
            bcoll <- true;
          }
        } else {   (* mem (dom m) (x.`1, hx2) /\ (!dom m with I \/ o <> D) *)  
          y1h              <- oget m.[(x.`1,hx2)];
          (y2,o')          <- oget handles.[y1h.`2];   
          handles.[y1h.`2] <- (y2, max o o');  
          handles.[hx2]    <- (x.`2, max o (oget handles.[hx2]).`2);
          y                <- (y1h.`1, y2);
        }
        return y;
      }

      proc f(x:state):state = {
        var r; 
        r <@ fg(D,x);
        return r;
      }

      proc fi(x : state): state = {
        var o', y, y2, ox2, hx2, y1h;

        ox2  <- hinv handles x.`2;
        hx2  <- oget ox2;

        if (ox2 = None) {
           handles.[chandle] <- (x.`2,D);
           hx2               <- chandle;
           chandle           <- chandle + 1;
        }
        
        if (!mem (dom mi) (x.`1,hx2) || (oget handles.[hx2]).`2 = I) {
          y                 <$ dstate;
          if ( hinv handles y.`2 = None) {
            y1h               <- (y.`1, chandle);
            handles.[chandle] <- (y.`2, D);
            mi.[(x.`1, hx2)]  <- y1h; 
            m.[y1h]           <- (x.`1, hx2);
            handles.[hx2]     <- ((oget handles.[hx2]).`1, D);
            chandle           <- chandle + 1;     
          } else {
            bcoll <- true;
          }

        } else {
          y1h              <- oget mi.[(x.`1,hx2)];
          (y2,o')          <- oget handles.[y1h.`2];   
          bred             <- bred \/ o' = I; 
          handles.[y1h.`2] <- (y2, D);  
          handles.[hx2]    <- (x.`2, D);
          y                <- (y1h.`1, y2);

        }
        return y;
      }

      (** Distinguisher interface **)
      proc init() = { }

    }

    module C = {
      proc init(): unit = { }

      proc f(p : block list): block = {
        var (sa,sc) <- (b0,c0);

        if (1 <= size p /\ p <> [b0]) {
          while (p <> []) {
            (sa,sc) <@ S.fg(I,(sa ^ head witness p,sc));
            p <- behead p;
          }
        }
        return sa;
      }
    }

    proc main(): bool = {
      var b;

      m        <- map0;
      mi       <- map0;
      bext     <- false;
      bred     <- false;
      bcoll    <- false;
      bsuff    <- false;
      bmitm    <- false;
      (* the empty path is initially known by the adversary to lead to capacity 0^c *)
      handles  <- map0.[0 <- (c0, D)];
      paths    <- map0.[0 <- ([<:block>],b0,D)];
      chandle  <- 1;
      b        <@ D(C,S).distinguish();
      return b;
    }    
  }.





module M = {
   proc f () : unit = {
      var x;
      var l:int list;
      l = [];
  }
}.































































  (** Result: the instrumented system and the concrete system are
      perfectly equivalent **)
  local equiv Game0_P_S_eq:
    Concrete_F.P.f ~ Game0.S.fg:
         arg{1} = arg{2}.`2
      /\ ={m,mi}(Concrete_F,Game0)
      /\ is_pre_permutation (Concrete_F.m){1} (Concrete_F.mi){1}
      ==> ={res}
          /\ ={m,mi}(Concrete_F,Game0)
          /\ is_pre_permutation (Concrete_F.m){1} (Concrete_F.mi){1}.
  proof.
    proc. inline *.
    sp; if=> //=; 2:by auto.
    auto; progress [-split].
    by rewrite pre_permutation_set.
  qed.

  local equiv Game0_Pi_Si_eq:
    Concrete_F.P.fi ~ Game0.S.fi:
         ={arg}
      /\ ={m,mi}(Concrete_F,Game0)
      /\ is_pre_permutation (Concrete_F.m){1} (Concrete_F.mi){1}
      ==> ={res}
          /\ ={m,mi}(Concrete_F,Game0)
          /\ is_pre_permutation (Concrete_F.m){1} (Concrete_F.mi){1}.
  proof.
    proc. inline *.
    sp; if=> //=; 2:by auto.
    auto; progress [-split].
    by rewrite pre_permutation_set.
  qed.

  local lemma Game0_pr &m:
    `|Pr[Concrete_F.main() @ &m: res]
      - Pr[Ideal.main() @ &m: res]|
    = `|Pr[Game0.main() @ &m: res]
        - Pr[Ideal.main() @ &m: res]|.
  proof.
    do !congr.
    byequiv=> //=.
    proc.
    call (_:    ={m,mi}(Concrete_F,Game0)
             /\ is_pre_permutation Concrete_F.m{1} Concrete_F.mi{1}).
      + by proc *;inline Game0.S.f;wp;call Game0_P_S_eq;auto.
      + by proc *;call Game0_Pi_Si_eq.
      + proc. sp; if=> //=.
        while (   ={sa,sc,p}
               /\ ={m,mi}(Concrete_F,Game0)
               /\ is_pre_permutation Concrete_F.m{1} Concrete_F.mi{1}).
          wp; call Game0_P_S_eq.
          by auto.
        by auto.
    by auto; smt.
  qed.

  (** Split the simulator map into distinct rate and capacity maps **)
  pred map_split (m0 : (state,state) fmap) (a1 : (state,block) fmap) (c1 : (state,capacity) fmap) =
       (forall x, mem (dom m0) x = mem (dom a1) x)
    /\ (forall x, mem (dom m0) x = mem (dom c1) x)
    /\ (forall x, mem (dom m0) x => m0.[x] = Some (oget a1.[x],oget c1.[x])).

  lemma map_split_set m0 a1 c1 s a c:
    map_split m0 a1 c1 =>
    map_split m0.[s <- (a,c)] a1.[s <- a] c1.[s <- c]
  by [].

  local module Game1 = {
    var mcol,micol          : (state,caller) fmap
    var rate, ratei         : (state,block) fmap
    var cap, capi           : (state,capacity) fmap
    var pathscol            : (capacity,caller) fmap
    var paths               : (capacity,block list * block) fmap
    var bext, bred          : bool
    var bcoll, bsuff, bmitm : bool

    module S = {
      (** Inner interface **)
      proc fg(o : caller, x : state): state = {
        var o', ya, yc, pv, p, v;

        o' <- odflt D pathscol.[x.`2];
        bext <- bext \/ (o' <= o);

        if (!mem (dom rate) x) {
          (ya,yc) <$ dstate;
          if (mem (dom paths) x.`2) {
            o'            <- oget pathscol.[x.`2];
            pv            <- oget paths.[x.`2];
            (p,v)         <- pv;
            bcoll         <- bcoll \/ (mem (dom paths) yc);
            bsuff         <- bsuff \/ (mem (rng cap) yc);
            pathscol.[yc] <- max o o';
            paths.[yc]    <- (rcons p (v ^ x.`1),ya);
          }
          rate.[x]        <- ya;
          ratei.[(ya,yc)] <- x.`1;
          cap.[x]         <- yc;
          capi.[(ya,yc)]  <- x.`2;
          mcol.[x]        <- o;
          micol.[(ya,yc)] <- o;
        } else {
          o'              <- oget mcol.[x];
          mcol.[x]        <- max o o';
          ya              <- oget rate.[x];
          yc              <- oget cap.[x];
          o'              <- oget micol.[(ya,yc)];
          micol.[(ya,yc)] <- max o o';
        }
        return (oget rate.[x],oget cap.[x]);
      }

      proc f(x:state):state = {
        var r; 
        r <@ fg(D,x);
        return r;
      }

      proc fi(x : state): state = {
        var ya, yc;

        if (!mem (dom ratei) x) {
          (ya,yc)        <$ dstate;
          micol.[x]      <- D;
          ratei.[x]      <- ya;
          capi.[x]       <- yc;
          mcol.[(ya,yc)] <- D;
          rate.[(ya,yc)] <- x.`1;
          cap.[(ya,yc)]  <- x.`2;
          bmitm  <- bmitm \/ (mem (dom paths) yc);
        } else {
          bred           <- bred \/ oget micol.[x] = I;
          micol.[x]      <- D;
          ya             <- oget ratei.[x];
          yc             <- oget capi.[x];
          mcol.[(ya,yc)] <- D;
        }
        return (oget ratei.[x],oget capi.[x]);
      }

      (** Distinguisher interface **)
      proc init() = { }

    }

    module C = {
      proc init(): unit = { }

      proc f(p : block list): block = {
        var (sa,sc) <- (b0,c0);

        if (1<= size p /\ p <> [b0]) {
          while (p <> []) {
            (sa,sc) <@ S.fg(I,(sa ^ head witness p,sc));
            p <- behead p;
          }
        }
        return sa;
      }
    }

    proc main(): bool = {
      var b;

      mcol     <- map0;
      micol    <- map0;
      rate     <- map0;
      ratei    <- map0;
      cap      <- map0;
      capi     <- map0;
      bext     <- false;
      bred     <- false;
      bcoll    <- false;
      bsuff    <- false;
      bmitm    <- false;
      (* the empty path is initially known by the adversary to lead to capacity 0^c *)
      pathscol <- map0.[c0 <- D];
      paths    <- map0.[c0 <- ([<:block>],b0)];
      b        <@ D(C,S).distinguish();
      return b;
    }    
  }.

  local equiv Game1_S_S_eq:
    Game0.S.fg ~ Game1.S.fg:
         ={arg}
      /\ ={pathscol,paths}(Game0,Game1)
      /\ map_split Game0.m{1}  Game1.rate{2}  Game1.cap{2}
      /\ map_split Game0.mi{1} Game1.ratei{2} Game1.capi{2}
      /\ is_pre_permutation (Game0.m){1} (Game0.mi){1}
      ==>    ={res}
          /\ ={pathscol,paths}(Game0,Game1)
          /\ map_split Game0.m{1}  Game1.rate{2}  Game1.cap{2}
          /\ map_split Game0.mi{1} Game1.ratei{2} Game1.capi{2}
          /\ is_pre_permutation (Game0.m){1} (Game0.mi){1}.
  proof. 
    proc. inline *.
    sp; if; 1:by progress [-split]; move: H=> [->].
    + auto; progress [-split].
      move: H3; case yL=> ya yc H3; case (x{2})=> xa xc.
      by rewrite !getP_eq !map_split_set ?pre_permutation_set.
    + auto; progress [-split].
      rewrite H H0 H1 /=.
      by move: H=> [_ [_ ->]].
  qed.

  local equiv Game1_Si_Si_eq:
    Game0.S.fi ~ Game1.S.fi:
         ={arg}
      /\ ={pathscol,paths}(Game0,Game1)
      /\ map_split Game0.m{1}  Game1.rate{2}  Game1.cap{2}
      /\ map_split Game0.mi{1} Game1.ratei{2} Game1.capi{2}
      /\ is_pre_permutation (Game0.m){1} (Game0.mi){1}
      ==>    ={res}
          /\ ={pathscol,paths}(Game0,Game1)
          /\ map_split Game0.m{1}  Game1.rate{2}  Game1.cap{2}
          /\ map_split Game0.mi{1} Game1.ratei{2} Game1.capi{2}
          /\ is_pre_permutation (Game0.m){1} (Game0.mi){1}.
  proof.
    proc. inline *.
    sp; if; 1:by progress [-split]; move: H0=> [->].
    + auto; progress [-split].
      move: H3; case yL=> ya yc H3; case (x{2})=> xa xc.
      by rewrite !getP_eq !map_split_set ?pre_permutation_set.
    + auto; progress [-split].
      rewrite H H0 H1 /=.
      by move: H0=> [_ [_ ->]].
  qed.

  local lemma Game1_pr &m:
    `|Pr[Game0.main() @ &m: res]
      - Pr[Ideal.main() @ &m: res]|
    = `|Pr[Game1.main() @ &m: res]
        - Pr[Ideal.main() @ &m: res]|.
  proof.
    do !congr. byequiv=> //=; proc.
    call (_:    ={pathscol,paths}(Game0,Game1)
             /\ map_split Game0.m{1}  Game1.rate{2}  Game1.cap{2}
             /\ map_split Game0.mi{1} Game1.ratei{2} Game1.capi{2}
             /\ is_pre_permutation Game0.m{1} Game0.mi{1}).
    + by proc;call Game1_S_S_eq.
    + by apply Game1_Si_Si_eq.
    + proc; sp; if=> //=.
      while (   ={sa,sc,p}
             /\ ={pathscol,paths}(Game0,Game1)
             /\ map_split Game0.m{1}  Game1.rate{2}  Game1.cap{2}
             /\ map_split Game0.mi{1} Game1.ratei{2} Game1.capi{2}
             /\ is_pre_permutation Game0.m{1} Game0.mi{1})=> //.
      by wp; call Game1_S_S_eq.
    by auto; smt.
  qed.

(*un jeu avec indirection.
jeu avec indirection -> simulateur. *)
  type handle = int.
  type hstate = block * handle.


  local module Game2 = {
    
    var mcol,micol          : (hstate,caller) fmap
    var rate, ratei         : (hstate,block) fmap
    var cap, capi           : (hstate,handle) fmap
    var handles             : (handle,capacity) fmap                
    var pathscol            : (handle,caller) fmap
    var paths               : (handle,block list * block) fmap
    var bext, bred          : bool
    var bcoll, bsuff, bmitm : bool

    module S = {
      (** Inner interface **)
      proc fg(o : caller, x : state): state = {
        var o', ya, yc, pv, p, v, x2;
   
        (* Fait chier ici *)
(*        o' <- odflt D pathscol.[x.`2];
          bext <- bext \/ (o' <= o); *)

        if (!mem (dom rate) x) {
          x2 <- hinv handles x.`2;        
          (ya,yc) <$ dstate;
          if (mem (dom paths) x.`2) {
            o'            <- oget pathscol.[x.`2];
            pv            <- oget paths.[x.`2];
            (p,v)         <- pv;
            bcoll         <- bcoll \/ (mem (dom paths) yc);
            bsuff         <- bsuff \/ (mem (rng cap) yc);
            pathscol.[yc] <- max o o';
            paths.[yc]    <- (rcons p (v ^ x.`1),ya);
          }
          rate.[x]        <- ya;
          ratei.[(ya,yc)] <- x.`1;
          cap.[x]         <- yc;
          capi.[(ya,yc)]  <- x.`2;
          mcol.[x]        <- o;
          micol.[(ya,yc)] <- o;
        } else {
          o'              <- oget mcol.[x];
          mcol.[x]        <- max o o';
          ya              <- oget rate.[x];
          yc              <- oget cap.[x];
          o'              <- oget micol.[(ya,yc)];
          micol.[(ya,yc)] <- max o o';
        }
        return (oget rate.[x],oget cap.[x]);
      }

      proc f(x:state):state = {
        var r; 
        r <@ fg(D,x);
        return r;
      }

      proc fi(x : state): state = {
        var ya, yc;

        if (!mem (dom ratei) x) {
          (ya,yc)        <$ dstate;
          micol.[x]      <- D;
          ratei.[x]      <- ya;
          capi.[x]       <- yc;
          mcol.[(ya,yc)] <- D;
          rate.[(ya,yc)] <- x.`1;
          cap.[(ya,yc)]  <- x.`2;
          bmitm  <- bmitm \/ (mem (dom paths) yc);
        } else {
          bred           <- bred \/ oget micol.[x] = I;
          micol.[x]      <- D;
          ya             <- oget ratei.[x];
          yc             <- oget capi.[x];
          mcol.[(ya,yc)] <- D;
        }
        return (oget ratei.[x],oget capi.[x]);
      }

      (** Distinguisher interface **)
      proc init() = { }

    }

    module C = {
      proc init(): unit = { }

      proc f(p : block list): block = {
        var (sa,sc) <- (b0,c0);

        if (1<= size p /\ p <> [b0]) {
          while (p <> []) {
            (sa,sc) <@ S.fg(I,(sa ^ head witness p,sc));
            p <- behead p;
          }
        }
        return sa;
      }
    }

    proc main(): bool = {
      var b;

      mcol     <- map0;
      micol    <- map0;
      rate     <- map0;
      ratei    <- map0;
      cap      <- map0;
      capi     <- map0;
      bext     <- false;
      bred     <- false;
      bcoll    <- false;
      bsuff    <- false;
      bmitm    <- false;
      (* the empty path is initially known by the adversary to lead to capacity 0^c *)
      pathscol <- map0.[c0 <- D];
      paths    <- map0.[c0 <- ([<:block>],b0)];
      b        <@ D(C,S).distinguish();
      return b;
    }    
  }.

end section.

(* That Self is unfortunate *)
lemma PermutationLemma:
  exists epsilon,
    forall (D <: Self.DISTINGUISHER) &m,
    `|Pr[RealIndif(SqueezelessSponge,P,D).main() @ &m: res]
      - Pr[IdealIndif(H,S,D).main() @ &m: res]|
  < epsilon.
proof. admit. qed.
