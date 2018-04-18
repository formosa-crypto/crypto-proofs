pragma -oldip.
require import Core Int Real RealExtra StdOrder Ring StdBigop IntExtra.
require import List FSet NewFMap Utils Common SLCommon RndO FelTactic Mu_mem.
require import DProd Dexcepted.
(*...*) import Capacity IntOrder Bigreal RealOrder BRA.

require (*--*) Handle.


clone export Handle as Handle0.

(*** THEORY PARAMETERS ***)
(** Validity of Functionality Queries **)
op valid: block list -> bool.
axiom valid_spec p: valid p => p <> [].

(** Validity and Parsing/Formatting of Functionality Queries **)
op format (p : block list) (n : int) = p ++ nseq (n - 1) b0.
op parse: block list -> (block list * int).

axiom formatK bs: format (parse bs).`1 (parse bs).`2 = bs.
axiom parseK p n: 0 < n => valid p => parse (format p n) = (p,n).
axiom parse_nil: parse [] = ([],0).

lemma parse_injective: injective parse.
proof. by move=> bs1 bs2 eq_format; rewrite -formatK eq_format (@formatK bs2). qed.

lemma parse_valid p: valid p => parse p = (p,1).
proof.
move=>h;cut{1}->:p=format p 1;2:smt(parseK).
by rewrite/format/=nseq0 cats0.
qed.


module type NFUNCTIONALITY = {
  proc init () : unit
  proc f (p : block list, n : int) : block list
}.

module type NDFUNCTIONALITY = {
  proc f (p : block list, n : int) : block list
}.


module NC = {
  var c : int
  var queries : (block list * int, block list) fmap
  proc init() = {
    c <- 0;
    queries <- map0;
  }
}.


module BlockSponge (P : PRIMITIVE) : NFUNCTIONALITY = {
  proc init() = {
    P.init();
  }
  proc f (p : block list, n : int) : block list = {
    var r : block list <- [];
    var i : int <- 0;
    var (b,c) <- (b0,c0);
    while (i < size p) {
      (b,c) <@ P.f(b +^ nth witness p i, c);
      i <- i + 1;
    }
    i <- 1;
    r <- rcons r b;
    NC.queries.[(p,1)] <- r;
    while (i < n) {
      (b,c) <@ P.f(b, c);
      r <- rcons r b;
      i <- i + 1;
      NC.queries.[(p,i)] <- r;
    }
    return r;
  }
}.

module type NDISTINGUISHER (F : NDFUNCTIONALITY, P : DPRIMITIVE) = {
  proc distinguish () : bool
}.

module NFC (F : NDFUNCTIONALITY) : NDFUNCTIONALITY = {  
  proc f (bl : block list, nb : int) = {
    var r : block list <- [];
    if (valid bl /\ 0 < nb) {
      if (! (bl,nb) \in dom NC.queries) {
        NC.c <- NC.c + size bl + nb - 1;
        r <@ F.f(bl,nb);
        NC.queries.[(bl,nb)] <- r;
      } else {
        r <- oget NC.queries.[(bl,nb)];
      }
    }
    return r;
  }
}.
    


module NPC (P : DPRIMITIVE) : DPRIMITIVE = {
  proc f (a : state) = {
    var z : state;
    z <@ P.f(a);
    NC.c <- NC.c + 1;
    return z;
  }
  proc fi (a : state) = {
    var z : state;
    z <@ P.fi(a);
    NC.c <- NC.c + 1;
    return z;
  }
}.

module (DSqueeze (F : DFUNCTIONALITY) : NDFUNCTIONALITY) = {
  proc f (p : block list, n : int) : block list = {
    var lres : block list <- [];
    var b : block <- b0;
    var i : int <- 0;
    while (i < n) {
      i <- i + 1;
      if (! (p,i) \in dom NC.queries) {
        b <@ F.f(format p i);
        lres <- rcons lres b;
        NC.queries.[(p,i)] <- lres;
      } else {
        lres <- oget NC.queries.[(p,i)];
      }
    }
    return lres;
  }
}.


module (Squeeze (F : FUNCTIONALITY) : NFUNCTIONALITY) = {
  proc init () : unit = {
    NC.queries <- map0;
    NC.c       <- 0;
    F.init();
  }
  proc f = DSqueeze(F).f
}.


module NDFRestr (F : NDFUNCTIONALITY) = {
  proc f (bl : block list, nb : int) = {
    var b : block <- b0;
    var lres : block list <- [];
    var i : int <- 0;

    if (valid bl /\ 0 < nb) {
      if (! (bl,nb) \in dom NC.queries) {
        if (NC.c + size bl + nb - 1 <= max_size) {
          NC.c <- NC.c + size bl + nb - 1;
          lres <@ F.f(bl,nb);
        }
      } else {
        lres <- oget NC.queries.[(bl,nb)];
      }
    }
    return lres;
  }
}.


module NDPRestr (P : DPRIMITIVE) : DPRIMITIVE = {
  proc f (a : state) = {
    var z : state;
    if (NC.c + 1 <= max_size) {
      z <@ P.f(a);
      NC.c <- NC.c + 1;
    }
    return z;
  }
  proc fi (a : state) = {
    var z : state;
    if (NC.c + 1 <= max_size) {
      z <@ P.fi(a);
      NC.c <- NC.c + 1;
    }
    return z;
  }
}.



module (NDRestr (D : NDISTINGUISHER) : NDISTINGUISHER)
  (F : NDFUNCTIONALITY) (P : DPRIMITIVE) = D(NDFRestr(F),NDPRestr(P)).



module (A (D : NDISTINGUISHER) : DISTINGUISHER)
  (F : DFUNCTIONALITY) (P : DPRIMITIVE) = {
  proc distinguish() : bool = {
    var b : bool;
    NC.init();
    b <@ D(NFC(DSqueeze(F)),NPC(P)).distinguish();
    return b;
  }
}.



module NIndif (F : NFUNCTIONALITY, P : PRIMITIVE, D : NDISTINGUISHER) = {
  proc main () : bool = {
    var b : bool;
    C.init();
    P.init();
    F.init();
    b <@ D(F,P).distinguish();
    return b;
  }
}.


module DC (D : NDISTINGUISHER) (F : NDFUNCTIONALITY) (P : DPRIMITIVE) = {
  proc distinguish () : bool = {
    var b : bool;
    NC.init();
    b <@ D(NFC(F),NPC(P)).distinguish();
    return b;
  }
}.


module P = Perm.


section.

  pred inv_ideal (squeeze : (block list * int, block list) fmap)
                 (c : (block list, block) fmap) =
    (forall p n, (p,n) \in dom squeeze => 
      forall i, 1 <= i <= n => (p,i) = parse (format p i)) /\
    (forall p n, (p,n) \in dom squeeze => 
      forall i, 1 <= i <= n => format p i \in dom c) /\
    (forall l, l \in dom c => 
      forall i, 1 <= i <= (parse l).`2 => ((parse l).`1,i) \in dom squeeze).


  inductive m_p (m : (state, state) fmap) (p : (block list, state) fmap)
      (q : (block list * int, block list) fmap) =
  | IND_M_P of (p.[[]] = Some (b0, c0))
        & (forall l, l \in dom p => forall i, 0 <= i < size l =>
            exists b c, p.[take i l] = Some (b,c) /\
            m.[(b +^ nth witness l i, c)] = p.[take (i+1) l])
        & (forall l n, (l,n) \in dom q => 
            valid l /\ 0 < n /\ size (oget q.[(l,n)]) = n /\
            (forall i, 0 < i <= n => q.[(l,i)] = Some (take i (oget q.[(l,n)]))))
        & (forall l n, (l,n) \in dom q => exists c, p.[format l n] = Some (last b0 (oget q.[(l,n)]),c))
        & (forall l, l \in dom p => l <> [] => exists l2, parse (l ++ l2) \in dom q).


  inductive INV_Real
    (c1 c2 : int)
    (m mi : (state, state) fmap)
    (p : (block list, state) fmap)
    (q : (block list * int, block list) fmap) =
    | INV_real of (c1 <= c2)
                & (m_p m p q)
                & (invm m mi).

  local lemma INV_Real_incr c1 c2 m mi p q :
      INV_Real c1 c2 m mi p q =>
      INV_Real (c1 + 1) (c2 + 1) m mi p q.
  proof. by  case;progress;split=>//=/#. qed.

  local lemma INV_Real_addm_mi c1 c2 m mi p q x y :
      INV_Real c1 c2 m mi p q =>
      ! x \in dom m =>
      ! y \in rng m =>
      INV_Real c1 c2 m.[x <- y] mi.[y <- x] p q.
  proof.
  case=> H_c1c2 H_m_p H_invm H_x_dom H_y_rng;split=>//=.
  + split;case:H_m_p=>//=;
    smt(getP in_dom oget_some take_oversize size_take take_take).
  exact invm_set.
  qed.

  local lemma invmC' (m mi : (state, state) fmap) :
      invm m mi => invm mi m.
  proof. by rewrite /#. qed.

  local lemma invmC (m mi : (state, state) fmap) :
      invm m mi <=> invm mi m.
  proof. by split;exact invmC'. qed.

  local lemma invm_dom_rng (m mi : (state, state) fmap) :
      invm m mi => dom m = rng mi.
  proof. by move=>h;rewrite fsetP=>x;split;rewrite in_dom in_rng/#. qed.

  local lemma lemma1 c1 c2 m mi p q bs i (l : block list):
      INV_Real c1 c2 m mi p q =>
      ! (bs,i) \in dom q =>
      valid bs =>
      0 < i =>
      size l = i =>
      (exists c, p.[format bs i] = Some (last b0 l, c)) =>
      (forall j, 0 < j < i => q.[(bs,j)] = Some (take j l)) =>
      INV_Real c1 c2 m mi p q.[(bs,i) <- l].
  proof.
  move=>INV0 H_bs_n_dom H_bs_valid H0in H_size H_format_dom H_pref_quer.
  split;cut[]//=H_c1c2 H_m_p H_invm:=INV0.
  split;cut[]//H_mp0 H_mp1 H_mp2 H_mp3 H_mp4:=H_m_p.
  + move=>l1 n1;rewrite dom_set in_fsetU1.
    case((l1, n1) = (bs, i))=>[[]->>->>|H_neq]//=. 
    - rewrite H_bs_valid getP/= oget_some/=H_size//=;split;1:rewrite/#;move=>j []Hj0 Hj1.
      rewrite getP/=;case(j=i)=>[->>|/#]//=;1:rewrite -H_size take_size//=.
    rewrite getP/=;move=>H_dom;cut[]->[]->[]H_size_get/=help:=H_mp2 _ _ H_dom;split.
    - by rewrite H_neq/=H_size_get.
    move=> j[]hj0 hji.
    rewrite !getP/=.
    cut:=H_neq;case(l1=bs)=>[->>H_n1i|]//=;smt(in_dom).
  + move=>m1 j;rewrite dom_set in_fsetU1 getP. 
    case((m1, j) = (bs, i))=>//=h H_dom.
    by cut[]c ->/#:=H_mp3 _ _ H_dom.
  + smt(dom_set in_fsetU1).
  qed.

  local lemma all_prefixes_of_INV_real c1 c2 m mi p q:
      INV_Real c1 c2 m mi p q =>
      all_prefixes p.
  proof.
  move=>[]_[]Hp0 Hmp1 _ _ _ _ l H_dom i.
  smt(take_le0 take_oversize size_take take_take take_size nth_take in_dom).
  qed.

  local lemma lemma2 c1 c2 m mi p q bl i sa sc lres:
      INV_Real c1 c2 m mi p q =>
      1 < i =>
      valid bl =>
      (sa,sc) \in dom m =>
      ! (format bl i) \in dom p =>
      ! (bl, i) \in dom q =>
      p.[format bl (i-1)] = Some (sa,sc) =>
      q.[(bl,i-1)] = Some lres =>
      INV_Real c1 c2 m mi p.[format bl i <- oget m.[(sa,sc)]] 
               q.[(bl,i) <- rcons lres (oget m.[(sa,sc)]).`1].
  proof.
  move=>inv0 h1i h_valid H_dom_m H_dom_p H_dom_q H_p_val H_q_val.
  split;cut[]//=_[] hmp0 hmp1 hmp2 hmp3 hmp4 hinvm:=inv0;split=>//=.
  + by rewrite getP;smt(size_cat size_nseq size_ge0).
  + move=>l;rewrite dom_set in_fsetU1;case;1:smt(all_prefixes_of_INV_real getP).
    move=>->>j[]hj0 hjsize;rewrite getP/=.
    cut:=hmp1 (format bl (i - 1));rewrite in_dom H_p_val/==>help.
    cut:=hjsize;rewrite !size_cat !size_nseq/=!max_ler 1:/#=>hjsizei.
    cut->/=:!take j (format bl i) = format bl i by smt(size_take).
    cut h:forall k, 0 <= k <= size bl + i - 2 => 
      take k (format bl (i - 1)) = take k (format bl i).
    * move=>k[]hk0 hkjS;rewrite !take_cat;case(k<size bl)=>//=hksize;congr. 
      apply (eq_from_nth witness);1:rewrite!size_take//=1,2:/#!size_nseq!max_ler/#.
      rewrite!size_take//=1:/#!size_nseq!max_ler 1:/#.
      pose o:=if _ then _ else _;cut->/={o}:o = k - size bl by smt().
      by progress;rewrite!nth_take//= 1,2:/# !nth_nseq//=/#.
    case(j < size bl + i - 2)=>hj. 
    - cut:=help j _;1:smt(size_cat size_nseq).
      move=>[]b c[].
      cut->:nth witness (format bl (i - 1)) j = nth witness (format bl i) j. 
      + by rewrite-(nth_take witness (j+1)) 1,2:/# eq_sym -(nth_take witness (j+1)) 1,2:/# !h//=/#.
      rewrite h 1:/# h 1:/# => -> h';exists b c=>//=;rewrite h'/=getP/=. 
      smt(size_take size_cat size_nseq).
    cut->>/=:j = size (format bl (i-1)) by smt(size_cat size_nseq).
    rewrite getP/=.
    cut h':size (format bl (i-1)) = size bl + i - 2 by smt(size_cat size_nseq).
    rewrite h'/=-(addzA _ _ 1)/=.
    cut h'':(size bl + i - 1) = size (format bl i) by smt(size_cat size_nseq).
    rewrite h'' take_size/=-h 1:/# -h' take_size.
    rewrite nth_cat h';cut->/=:! size bl + i - 2 < size bl by smt().
    by rewrite nth_nseq 1:/#;smt(Block.WRing.AddMonoid.addm0 in_dom get_oget). 
  + move=>bs n;rewrite dom_set in_fsetU1;case=>//=[Hdom|[]->>->>]//=;do!split=>//=.
    - by cut//:=hmp2 _ _ Hdom.
    - by cut//:=hmp2 _ _ Hdom.
    - by cut[]H_valid[]Hn0[]H_size H_prefixe:=hmp2 _ _ Hdom;rewrite getP/=;smt().
    - cut[]H_valid[]Hn0[]H_size H_prefixe k[]hk0 hksize:=hmp2 _ _ Hdom.
      rewrite!getP/=;cut->/=:!(bs = bl && n = i) by smt().
      by rewrite-H_prefixe//=;smt(in_dom).
    - smt().
    - by rewrite getP/=oget_some/=size_rcons;smt(in_dom get_oget).
    move=>j[]hj0 hji;rewrite!getP/=oget_some-{2}cats1 take_cat. 
    case(i=j)=>[->>|]//=.
    - by cut<-/=:j - 1 = size lres;smt(in_dom get_oget cats1).
    move=>hij;cut->/=:j<>i by smt().
    cut->:size lres = i - 1 by smt(in_dom get_oget cats1).
    case(j < i - 1)=>//=hh;1:smt(in_dom get_oget cats1).
    by cut->>/=: j = i - 1;smt(cats0).
  + move=>bs n;rewrite dom_set in_fsetU1;case=>[Hdom|[]->>->>].
    - rewrite !getP/=;smt(in_dom).
    by rewrite!getP/=oget_some last_rcons/=;smt(get_oget in_dom).
  move=>l;rewrite dom_set in_fsetU1;case=>[H_dom|->>]l_n_nil.
  + smt(dom_set in_fsetU1).
  by exists [];rewrite cats0 parseK//= 1:/# dom_set in_fsetU1.
  qed.

  local lemma take_nseq (a : 'a) i j :
      take j (nseq i a) = if j <= i then nseq j a else nseq i a.
  proof.
  case(0 <= j)=>hj0;last first.
  + rewrite take_le0 1:/#;smt(nseq0_le).
  case(j <= i)=>hij//=;last smt(take_oversize size_nseq). 
  apply(eq_from_nth witness).
  + smt(size_take size_nseq).
  smt(size_nseq size_take nth_take nth_nseq).
  qed.

  local lemma take_format (bl : block list) n i :
      0 < n =>
      0 <= i < size bl + n =>
      take i (format bl n) = 
      if i <= size bl then take i bl else format bl (i - size bl + 1).
  proof.
  move=>Hn0[]Hi0 Hisize;rewrite take_cat take_nseq.
  case(i < size bl)=>//=[/#|H_isize'].
  cut->/=:i - size bl <= n - 1 by smt().
  case(i = size bl)=>[->>|H_isize'']//=;1:by rewrite nseq0 take_size cats0.
  smt().
  qed.


  local lemma equiv_sponge (D <: NDISTINGUISHER {P, NC, Redo, C}) :
    equiv [ GReal(A(D)).main
      ~ NIndif(Squeeze(SqueezelessSponge(P)),P,DC(D)).main
      : ={glob D} ==> ={res, glob D, glob P, glob NC} /\ C.c{1} <= NC.c{2}].
  proof.
  proc;inline*;sp;wp.
  call(: ={Redo.prefixes, glob P, glob NC} /\ 
    INV_Real C.c{1} NC.c{2} Perm.m{1} Perm.mi{1} Redo.prefixes{1} NC.queries{1});auto;last first.
  + by progress;1:(split=>//=;1:split;smt(dom0 in_fset0 dom_set in_fsetU1 getP map0P));case:H0=>//=. 
  + by proc;inline*;auto;sp;if;auto;smt(INV_Real_addm_mi INV_Real_incr supp_dexcepted).
  + proc;inline*;auto;sp;if;auto;progress.
    + apply INV_Real_incr=>//=.
      apply INV_Real_addm_mi=>//=.
      + case:H=>H_c H_m_p H_invm;rewrite (invm_dom_rng _ _ H_invm)//=. 
        by move:H1;rewrite supp_dexcepted.
      case:H=>H_c H_m_p H_invm;cut<-//:=(invm_dom_rng Perm.mi{2} Perm.m{2}). 
      by rewrite invmC.
    + exact INV_Real_incr.
  + proc;inline*;sp;if;auto;sp;if;auto.
    swap 6;wp;sp=>/=;rcondt{1}1;1:auto;rcondt{2}1;1:auto.
    conseq(:_==> ={i,nb,bl,n,p,glob NC,glob Redo,glob P,lres} /\ (n,p){1} = (nb,bl){1} /\
      i{1} = nb{1} /\
      format p{1} i{1} \in dom Redo.prefixes{1} /\
      INV_Real C.c{1} (NC.c{1} + size bl{2} + i{1} - 1) Perm.m{1} Perm.mi{1} 
        Redo.prefixes{1} NC.queries{1}.[(bl{1}, i{1}) <- lres{1}]);progress.
    while(={i,nb,bl,n,p,glob NC,glob Redo,glob P,lres} /\ (n,p){1} = (nb,bl){1} /\
      0 < i{1} <= nb{1} /\ (0 < i{1} => Some lres{1} = NC.queries{1}.[(bl{1}, i{1})]) /\
      format p{1} i{1} \in dom Redo.prefixes{1} /\ valid p{1} /\ size lres{1} = i{1} /\
      INV_Real C.c{1} (NC.c{1} + size bl{2} + i{1} - 1) Perm.m{1} Perm.mi{1} 
        Redo.prefixes{1} NC.queries{1}.[(bl{1}, i{1}) <- lres{1}]);last first.
    + sp;conseq(:_ ==> ={i,nb,bl,n,p,glob NC,glob Redo,glob P,lres} /\ (n,p){1} = (nb,bl){1} /\
        0 < i{1} <= nb{1} /\ (0 < i{1} => Some lres{1} = NC.queries{1}.[(bl{1}, i{1})]) /\
        format p{1} i{1} \in dom Redo.prefixes{1} /\ size lres{1} = i{1} /\
        INV_Real C.c{1} (NC.c{1} + size bl{2} + i{1} - 1) Perm.m{1} Perm.mi{1} 
          Redo.prefixes{1} NC.queries{1}.[(bl{1}, i{1}) <- lres{1}]);1:progress=>/#. 
      sp;if;auto;last first.
      * progress. 
        - by rewrite/#.
        - by cut INV0:=H;cut[]//=H_c1c2 H_m_p H_invm:=INV0;cut[]/#:=H_m_p.
        - by cut[]_[]_ _ _ help _ _:=H;cut:=help _ _ H3;smt(in_dom).
        - cut[]_[]Hmp0 Hmp1 Hmp2 Hmp3 Hmp4 Hinvm:=H.
          cut//=:=Hmp2 bl{2} 1 H3;rewrite H0/==>help;cut/=->/=:=help 1;rewrite oget_some size_take//=.
        by rewrite set_eq 1:get_oget//=;split;case:H=>//=;smt(size_ge0).
      sp=>/=.
      exists* Redo.prefixes{1}, C.c{1};elim*=>pref count;progress.
      conseq(:_==> ={i0,p0,i,p,n,nb,bl,sa,lres,glob NC,glob Redo,glob Perm}
            /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p0{1} = p{1} /\ i0{1} = size p{1}
            /\ Redo.prefixes{1}.[take i0{1} p{1}] = Some (sa{1},sc{1})
            /\ INV_Real count NC.c{1} Perm.m{1} Perm.mi{1} pref NC.queries{1}
            /\ (forall l, l \in dom Redo.prefixes{1} => 
                 l \in dom pref \/ (exists j, 0 < j <= i0{2} /\ l = take j p{1}))
            /\ (forall l, l \in dom pref => pref.[l] = Redo.prefixes{1}.[l])
            /\ C.c{1} <= count + i0{1} <= NC.c{1} + i0{1}
            /\ (forall j, 0 <= j < i0{1} =>
                 exists b c, Redo.prefixes{1}.[take j p{1}] = Some (b,c) /\
                 Perm.m{1}.[(b +^ nth witness p{1} j, c)] = Redo.prefixes{1}.[take (j+1) p{1}]));
        progress.
      + by rewrite/#. 
      + by rewrite getP/=. 
      + by rewrite/format/=nseq0 cats0//-take_size in_dom H5.
      + rewrite set_set/=.
        cut inv0:=H6;cut[]h_c1c2[]Hmp0 Hmp1 Hmp2 Hmp3 Hmp4 Hinvm:=inv0;split=>//=.
        - rewrite/#.
        split=>//=.
        - smt(in_dom).
        - move=>l H_dom_R i []Hi0 Hisize;cut:=H7 l H_dom_R.
          case(l \in dom Redo.prefixes{2})=>H_in_pref//=.
          * cut:=Hmp1 l H_in_pref i _;rewrite//=.
            rewrite ?H8//=;1:smt(in_dom).
            case(i+1 < size l)=>h;1:smt(in_dom).
            by rewrite take_oversize 1:/#.
          move=>[]j[][]hj0 hjsize ->>.
          cut:=Hisize;rewrite size_take 1:/#.
          pose k:=if _ then _ else _;cut->>Hij{k}:k=j by rewrite/#.
          by rewrite!take_take!min_lel 1,2:/# nth_take 1,2:/#;smt(in_dom).
        - by move=>l n;rewrite!dom_set in_fsetU1=>[][];smt(getP oget_some in_dom take_oversize).
        - move=>l n;rewrite dom_set in_fsetU1 getP;case((l, n) = (bl{2}, 1))=>//=[[->>->>]|].
          * by rewrite oget_some/=/format/=nseq0 cats0-take_size H5/#.
          move=>h H_dom;cut[]c:=Hmp3 _ _ H_dom;smt(in_dom).
        - move=>l H_dom_R H_not_nil;rewrite dom_set.
          cut:=H7 l H_dom_R;case;1:smt(in_fsetU1).
          move=>[]j[][]hj0 hjsize ->>;exists(drop j bl{2}).
          by rewrite cat_take_drop parse_valid//=in_fsetU1.
    while( ={i0,p0,i,p,n,nb,bl,sa,sc,lres,glob NC,glob Redo,glob Perm}
        /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p0{1} = p{1} /\ 0 <= i0{1} <= size p{1}
        /\ Redo.prefixes{1}.[take i0{1} p{1}] = Some (sa{1},sc{1})
        /\ INV_Real count NC.c{1} Perm.m{1} Perm.mi{1} pref NC.queries{1}
        /\ (forall l, l \in dom Redo.prefixes{1} => 
             l \in dom pref \/ (exists j, 0 < j <= i0{2} /\ l = take j p{1}))
        /\ (forall l, l \in dom pref => pref.[l] = Redo.prefixes{1}.[l])
        /\ C.c{1} <= count + i0{1} <= NC.c{1} + i0{1}
        /\ (i0{1} < size p0{1} => 
             take (i0{1}+1) p{1} \in dom Redo.prefixes{1} =>
             Redo.prefixes{1} = pref)
        /\ all_prefixes Redo.prefixes{1}
        /\ (forall j, 0 <= j < i0{1} =>
             exists b c, Redo.prefixes{1}.[take j p{1}] = Some (b,c) /\
             Perm.m{1}.[(b +^ nth witness p{1} j, c)] = 
             Redo.prefixes{1}.[take (j+1) p{1}]));last first.
    + auto;progress.
      - by rewrite /format/=nseq0 cats0.
      - exact size_ge0.
      - by rewrite take0;cut[]_[]->//=:=H.
      - by rewrite/#.
      - by cut[]->//=:=H.
      - smt(all_prefixes_of_INV_real).
      - by rewrite/#.
      by rewrite/#.
    if;auto;progress.
    + by rewrite/#.
    + by rewrite/#.
    + smt(get_oget in_dom).
    + smt(in_dom take_take take_oversize size_take).
    + by rewrite/#.
    + by rewrite/#.
    + by rewrite/#.
    + case(j<i0{2})=>h;1:rewrite/#;cut<<-:j=i0{2} by rewrite/#.
      cut->>:=H7 H10 H12.
      by cut[]_[]_ help _ _ _ _:=H2;cut:=help _ H12 j _;smt(take_take nth_take size_take).
    sp;if;auto;progress.
    + by rewrite/#.
    + by rewrite/#.
    + by rewrite!getP/=.
    + by apply INV_Real_addm_mi=>//=;smt(supp_dexcepted). 
    + by move:H16;rewrite dom_set in_fsetU1/#.
    + by rewrite!getP/=;smt(in_dom). 
    + by rewrite/#.
    + by rewrite/#.
    + move:H12;apply absurd=>//=_.
      move:H17;rewrite dom_set in_fsetU1.
      cut->/=:!take (i0{2} + 1 + 1) bl{2} = take (i0{2} + 1) bl{2} by smt(size_take).
      smt(take_take size_take).
    + move=>l;rewrite!dom_set in_fsetU1;case.
      - move=>H_dom;cut[]:=H3 l H_dom.
        * by move=>Hdom i;rewrite in_fsetU1/=;
            smt(in_dom all_prefixes_of_INV_real). 
        move=>[]j[][]hj0 hji0->>k.
        rewrite in_fsetU1 take_take;left.
        cut[]:=H3 _ H_dom;smt(in_dom take_take take_le0 take0 take_oversize).
      move=>->>k.
      rewrite in_fsetU1 take_take;case(0 <= k)=>hk0;
        last smt(in_fsetU1 in_dom take_take take_le0 take0 take_oversize).
      case(k < i0{2})=>hki01;
        first smt(in_fsetU1 in_dom take_take take_le0 take0 take_oversize).
      by case(k <= i0{2} + 1)=>hki02;smt(in_dom).
    + rewrite!getP/=oget_some.
      cut->/=:!take j bl{2} = take (i0{2} + 1) bl{2} by smt(size_take).
      case(j < i0{2})=>hj0;2:smt(getP oget_some size_take).
      cut->/=:!take (j + 1) bl{2} = take (i0{2} + 1) bl{2} by smt(size_take). 
      by cut:=H9 j _;1:rewrite hj0 H16//=;smt(in_rng getP in_dom). 
    + by rewrite/#.
    + by rewrite/#.
    + by rewrite!getP/=.
    + by move:H14;rewrite dom_set in_fsetU1/#.
    + by rewrite!getP/=;smt(in_dom). 
    + by rewrite/#.
    + by rewrite/#.
    + move:H12;apply absurd=>//=_.
      move:H15;rewrite dom_set in_fsetU1.
      cut->/=:!take (i0{2} + 1 + 1) bl{2} = take (i0{2} + 1) bl{2} by smt(size_take).
      by move=>h;cut:=H8 _ h (i0{2}+1);rewrite take_take/#.
    + move=>l;rewrite!dom_set in_fsetU1;case.
      - move=>H_dom;cut[]:=H3 l H_dom.
        * by move=>Hdom i;rewrite in_fsetU1/=;
            smt(in_dom all_prefixes_of_INV_real). 
        move=>[]j[][]hj0 hji0->>k.
        rewrite in_fsetU1 take_take;left.
        cut[]:=H3 _ H_dom;smt(in_dom take_take take_le0 take0 take_oversize).
      move=>->>k.
      rewrite in_fsetU1 take_take;case(0 <= k)=>hk0;
        last smt(in_fsetU1 in_dom take_take take_le0 take0 take_oversize).
      case(k < i0{2})=>hki01;
        first smt(in_fsetU1 in_dom take_take take_le0 take0 take_oversize).
      by case(k <= i0{2} + 1)=>hki02;smt(in_dom).
    rewrite!getP/=.
    cut->/=:!take j bl{2} = take (i0{2} + 1) bl{2} by smt(size_take).
    by case(j < i0{2})=>hj0;smt(get_oget in_dom oget_some size_take).
  sp;if;auto;last first;progress.
  + rewrite/#.
  + rewrite/#.
  + by rewrite get_oget//=.
  + rewrite in_dom;cut[]_[]_ _ _ help _ _:=H4. 
    by cut//=:=help bl{2} (size lres{2}+1);rewrite dom_set in_fsetU1 H7/==>[][]c->.
  + cut[]_[]_ _ help _ _ _:=H4.
    cut:=help bl{2} (size lres{2}+1);rewrite dom_set in_fsetU1//=H7/=H3/=!getP/=.
    by cut->/=[]_[]->//:!size lres{2} + 1 = size lres{2} by smt().
  + by rewrite set_eq//=1:get_oget//=;split;cut:=H4;rewrite set_eq 1:H1//==>[][]//=/#.
  sp.
  splitwhile{1} 1 : i0 < size p0 - 1;splitwhile{2} 1 : i0 < size p0 - 1.
  rcondt{1}2;2:rcondt{2}2;1,2:by auto;
    while(i0 < size p0);auto;1:if;2:(sp;if);auto;smt(size_cat size_nseq size_ge0).
  rcondf{1}4;2:rcondf{2}4;1,2:by auto;
    seq 1 : (i0 = size p0 - 1);1:(auto;
      while(i0 < size p0);auto;1:if;2:(sp;if);auto;smt(size_cat size_nseq size_ge0));
    if;sp;2:if;auto;smt(size_cat size_nseq size_ge0).
  wp;conseq(:_==> ={sa,sc,glob Redo,glob Perm}
          /\ INV_Real C.c{1} (NC.c{1} + size bl{2} + i{1} - 1) Perm.m{1} Perm.mi{1}
               Redo.prefixes{1} NC.queries{1}.[(p{1}, i{1}) <- rcons lres{1} sa{1}]
          /\ (format p{1} i{1} \in dom Redo.prefixes{1}));progress.
  + smt(size_ge0).
  + smt(size_ge0).
  + by rewrite getP/=.
  + exact size_rcons.
  + by rewrite set_set//=.
  seq 1 1 : (={nb,bl,n,p,p0,i,i0,lres,sa,sc,glob NC,glob Redo,glob Perm}
          /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p0{1} = format p{1} i{1}
          /\ 1 < i{1} <= n{1} /\ valid p{1} /\ i0{1} = size p0{1} - 1
          /\ Some lres{1} = NC.queries{1}.[(bl{1}, i{1}-1)]
          /\ ! ((p{1}, i{1}) \in dom NC.queries{1})
          /\ Redo.prefixes{1}.[format p{1} (i{1}-1)] = Some (sa{1},sc{1})
          /\ INV_Real C.c{1} (NC.c{1} + size bl{2} + i{1} - 2) Perm.m{1} Perm.mi{1}
               Redo.prefixes{1} NC.queries{1}.[(bl{1}, i{1} - 1) <- lres{1}]);last first.
  + if;auto;progress. 
    - move:H6;rewrite -addzA/=take_size=>H_dom.
      move:H5;rewrite set_eq 1:H2//= =>inv0.
      apply lemma1=>//=.
      * split;case:inv0=>//=/#.
      * smt().
      * rewrite size_rcons;cut[]//=Hc[]Hmp0 Hmp1 Hmp2 Hmp3 Hmp4 Hinvm:=inv0.
        by cut:=Hmp2 bl{2} (i{2}-1);rewrite in_dom -H2/=H1/=oget_some/#.
      * rewrite last_rcons;smt(get_oget in_dom).
      move=>j[]hj0 hji.
      cut[]//=Hc[]Hmp0 Hmp1 Hmp2 Hmp3 Hmp4 Hinvm:=inv0;cut:=Hmp2 bl{2} (i{2}-1).
      rewrite in_dom -H2/=H1/=oget_some=>[][]hi10[]hsize->;1:smt().
      congr;rewrite-cats1 take_cat;case(j < size lres{2})=>//=hsize2.
      cut->//=:j = size lres{2} by smt().
      by rewrite cats0 take_size.
    - by move:H6;rewrite -(addzA _ _ 1)/=take_size.  
    sp;if;auto;progress.
    - move:H6 H7;rewrite!getP/=!oget_some nth_last -(addzA _ _ 1)/=take_size.
      rewrite last_cat last_nseq 1:/# Block.WRing.addr0;progress. 
      cut//=:=lemma2(C.c{1} + 1)(NC.c{2} + size bl{2} + i{2} - 1)
        Perm.m{2}.[(sa_R, sc{2}) <- y0L] Perm.mi{2}.[y0L <- (sa_R, sc{2})]
        Redo.prefixes{2} NC.queries{2} bl{2} i{2} sa_R sc{2} lres{2}.
      rewrite H/=H1/=H2/=H4/=H6/=H3/=dom_set in_fsetU1/=getP/=oget_some.
      cut->->//=:y0L = (y0L.`1, y0L.`2) by smt().
      rewrite INV_Real_addm_mi//=;2:smt(supp_dexcepted). 
      by cut:=H5;rewrite set_eq 1:H2//==>hinv0;split;case:hinv0=>//=/#.
    - by rewrite dom_set in_fsetU1//=-(addzA _ _ 1)/=take_size.
    - move:H6 H7;rewrite nth_last -(addzA _ _ 1)/=take_size.
      rewrite last_cat last_nseq 1:/# Block.WRing.addr0;progress. 
      pose a:=(_, _);cut->/={a}:a = oget Perm.m{2}.[(sa_R, sc{2})] by smt().
      apply lemma2=>//=;first cut:=H5;rewrite set_eq 1:H2//==>hinv0;split;case:hinv0=>//=/#.
      rewrite H2//=.
    - by rewrite dom_set in_fsetU1//=-(addzA _ _ 1)/=take_size.
  alias{1} 1 pref = Redo.prefixes;sp;alias{1} 1 count = C.c.
  alias{1} 1 pm = Perm.m;sp;alias{1} 1 pmi = Perm.mi;sp.
  conseq(:_==> ={nb,bl,n,p,p0,i,i0,lres,sa,sc,glob NC,glob Redo,glob Perm}
        /\ pmi{1} = Perm.mi{1} /\ pm{1} = Perm.m{1}
        /\ pref{1} = Redo.prefixes{1} /\ C.c{1} = count{1}
        /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p0{1} = format p{1} i{1}
        /\ i0{1} = size p0{1} - 1
        /\ Redo.prefixes{1}.[format p{1} (i0{1} - size p{1} + 1)] = Some (sa{1}, sc{1}));
    1:smt(size_cat size_nseq).
  splitwhile{1}1:i0 < size p;splitwhile{2}1:i0 < size p.
  while(={nb,bl,n,p,p0,i,i0,lres,sa,sc,glob NC,glob Redo,glob Perm}
        /\ pmi{1} = Perm.mi{1} /\ pm{1} = Perm.m{1} /\ 0 < i{1}
        /\ pref{1} = Redo.prefixes{1} /\ C.c{1} = count{1}
        /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p0{1} = format p{1} i{1}
        /\ size p{1} <= i0{1} <= size p0{1} - 1 /\ valid p{1}
        /\ (format p{1} (i{1}-1) \in dom Redo.prefixes{1})
        /\ INV_Real C.c{1} (NC.c{1} + size bl{2} + i{1} - 2) Perm.m{1} Perm.mi{1}
             Redo.prefixes{1} NC.queries{1}
        /\ Redo.prefixes{1}.[format p{1} (i0{1} - size p{1} + 1)] = Some (sa{1}, sc{1}) ).
  + rcondt{1}1;2:rcondt{2}1;auto;progress.
    - rewrite take_format;1,2:smt(size_cat size_ge0 size_nseq). 
      cut->/=:! i0{m} + 1 <= size bl{m} by smt().
      cut:=take_format bl{m} (i{m}-1) (i0{m} + 1) _ _;1,2:smt(size_cat size_ge0 size_nseq).
      cut->/=<-:! i0{m} + 1 <= size bl{m} by smt().
      by cut/#:=all_prefixes_of_INV_real.
    - rewrite take_format;1,2:smt(size_cat size_ge0 size_nseq). 
      cut->/=:! i0{hr} + 1 <= size bl{hr} by smt().
      cut:=take_format bl{hr} (i{hr}-1) (i0{hr} + 1) _ _;1,2:smt(size_cat size_ge0 size_nseq).
      cut->/=<-:! i0{hr} + 1 <= size bl{hr} by smt().
      by cut/#:=all_prefixes_of_INV_real.
    - smt().
    - smt().
    - rewrite take_format//=;1:smt(size_cat size_ge0 size_nseq). 
      cut->/=:!i0{2} + 1 <= size bl{2} by smt().
      rewrite get_oget 2:/#. 
      cut:=take_format bl{2} (i{2}-1) (i0{2} + 1) _ _;1,2:smt(size_cat size_ge0 size_nseq).
      cut->/=:!i0{2} + 1 <= size bl{2} by smt().
      by cut/#:=all_prefixes_of_INV_real.
  conseq(:_==> ={nb,bl,n,p,p0,i,i0,lres,sa,sc,glob NC,glob Redo,glob Perm}
        /\ pmi{1} = Perm.mi{1} /\ pm{1} = Perm.m{1} /\ 0 < i{1}
        /\ pref{1} = Redo.prefixes{1} /\ C.c{1} = count{1}
        /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p0{1} = format p{1} i{1}
        /\ size p{1} = i0{1} /\ valid p{1}
        /\ (format p{1} (i{1}-1) \in dom Redo.prefixes{1})
        /\ INV_Real C.c{1} (NC.c{1} + size bl{2} + i{1} - 2) Perm.m{1} Perm.mi{1}
             Redo.prefixes{1} NC.queries{1}
        /\ Redo.prefixes{1}.[take i0{1} p{1}] = Some (sa{1}, sc{1}));
    progress.
  + smt(size_cat size_ge0 size_nseq).
  + by rewrite /format/=nseq0 cats0 -take_size;exact H12.
  + smt().
  while( ={nb,bl,n,p,p0,i,i0,lres,sa,sc,glob NC,glob Redo,glob Perm}
        /\ pmi{1} = Perm.mi{1} /\ pm{1} = Perm.m{1} /\ 1 < i{1}
        /\ pref{1} = Redo.prefixes{1} /\ C.c{1} = count{1}
        /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p0{1} = format p{1} i{1}
        /\ 0 <= i0{1} <= size p{1} /\ valid p{1}
        /\ (format p{1} (i{1}-1) \in dom Redo.prefixes{1})
        /\ INV_Real C.c{1} (NC.c{1} + size bl{2} + i{1} - 2) Perm.m{1} Perm.mi{1}
             Redo.prefixes{1} NC.queries{1}
        /\ Redo.prefixes{1}.[take i0{1} p{1}] = Some (sa{1}, sc{1}) );last first.
  + auto;progress.
    - smt(size_ge0).
    - smt(size_ge0).
    - smt().
    - smt(set_eq in_dom).
    - by rewrite take0;case:H4=>[]_[]//=.
    - smt(size_cat size_nseq size_ge0).
    - smt(size_cat size_nseq size_ge0).
  rcondt{1}1;2:rcondt{2}1;auto;progress.
  + cut->:take (i0{m} + 1) (format bl{m} i{m}) = 
          take (i0{m} + 1) (format bl{m} (i{m} - 1))
      by rewrite!take_format//=;smt(size_cat size_ge0 size_nseq).
    by cut/#:=all_prefixes_of_INV_real.
  + cut->:take (i0{hr} + 1) (format bl{hr} i{hr}) = 
          take (i0{hr} + 1) (format bl{hr} (i{hr} - 1))
      by rewrite!take_format//=;smt(size_cat size_ge0 size_nseq).
    by cut/#:=all_prefixes_of_INV_real.
  + smt().
  + smt().
  cut->:take (i0{2} + 1) (format bl{2} i{2}) = 
        take (i0{2} + 1) (format bl{2} (i{2} - 1))
    by rewrite!take_format//=;smt(size_cat size_ge0 size_nseq).
  cut->:take (i0{2} + 1) bl{2} = take (i0{2} + 1) (format bl{2} (i{2} - 1))
    by rewrite take_format;smt(size_cat size_ge0 size_nseq).
  by cut:=all_prefixes_of_INV_real _ _ _ _ _ _ H4 _ H3;smt(in_dom).
  qed.



  local lemma lemma3 c c' m mi p q bl i sa sc lres:
      INV_Real c c' m mi p q =>
      0 < i =>
      q.[(bl,i)] = Some lres =>
      p.[format bl i] = Some (sa,sc) =>
      (bl,i+1) \in dom q =>
      q.[(bl,i+1)] = Some (rcons lres (oget m.[(sa,sc)]).`1).
  proof.
  move=>inv0 H_i0 H_q_i H_p_i H_dom_iS.
  cut[]_[]_ hmp1 hmp2 hmp3 _ _:=inv0.
  cut[]c2 h2:=hmp3 _ _ H_dom_iS.
  cut:=hmp1 (format bl (i+1));rewrite in_dom h2/==>help.
  cut:=help (size (format bl i)) _;1:smt(size_ge0 size_cat size_nseq).
  move=>[]b3 c3;rewrite!take_format;..4:smt(size_ge0 size_cat size_nseq).
  cut->/=:!size (format bl i) + 1 <= size bl by smt(size_cat size_nseq size_ge0).
  rewrite nth_cat.
  cut->/=:!size (format bl i) < size bl by smt(size_cat size_ge0).
  rewrite nth_nseq 1:size_cat 1:size_nseq 1:/#.
  pose x:=if _ then _ else _;cut->/={x}:x = format bl i.
  + rewrite/x;case(i = 1)=>//=[->>|hi1].
    - by rewrite/format/=nseq0 cats0//=take_size.
    by rewrite size_cat size_nseq/#.
  pose x:=List.size _ + 1 - List.size _ + 1;cut->/={x}:x=i+1
    by rewrite/x size_cat size_nseq;smt().
  rewrite H_p_i h2=>[]/=[][]->>->>. 
  rewrite Block.WRing.addr0=>H_pm;rewrite H_pm/=oget_some. 
  cut[]_[]_[]H_size H:=hmp2 _ _ H_dom_iS.
  cut H_q_i':=H i _;1:smt().
  cut:=H (i+1) _;1:smt().
  rewrite (take_nth witness)1:/# =>H_q_iS.
  rewrite H_q_iS/=oget_some last_rcons;congr.
  by cut:=H_q_i';rewrite H_q_i/=.
  qed.


  local lemma lemma3' c c' m mi p q bl i sa sc lres:
      INV_Real c c' m mi p q =>
      0 < i =>
      q.[(bl,i)] = Some lres =>
      p.[format bl i] = Some (sa,sc) =>
      (bl,i+1) \in dom q =>
      q.[(bl,i+1)] = Some (rcons lres (oget p.[format bl (i+1)]).`1).
  proof.
  move=>inv0 H_i0 H_q_i H_p_i H_dom_iS.
  cut[]_[]_ hmp1 hmp2 hmp3 _ _:=inv0.
  cut->:=lemma3 _ _ _ _ _ _ _ _ _ _ _ inv0 H_i0 H_q_i H_p_i H_dom_iS;congr;congr.
  cut[]b3 c3[]:=hmp1 (format bl (i+1)) _ (size (format bl i)) _.
  + rewrite in_dom;smt().
  + rewrite!size_cat!size_nseq;smt(size_ge0).
  rewrite nth_cat nth_nseq;1:smt(size_cat size_nseq size_ge0).
  cut->/=:!size (format bl i) < size bl by smt(size_cat size_nseq size_ge0).
  rewrite Block.WRing.addr0 !take_format 1,3:/#;1,2:smt(size_cat size_nseq size_ge0).
  cut->/=:!size (format bl i) + 1 <= size bl by smt(size_cat size_nseq size_ge0).
  cut->:size (format bl i) + 1 - size bl = i by smt(size_cat size_nseq).
  case(size (format bl i) <= size bl)=>//=Hi;last first.
  + cut->:size (format bl i) - size bl + 1 = i by smt(size_cat size_nseq).
    by rewrite H_p_i/==>[][]->>->>->//.
  cut->>/=:i = 1 by smt(size_cat size_nseq).
  by cut:=H_p_i;rewrite /(format bl 1)/=nseq0 cats0 take_size=>->/=[]->>->>->//.
  qed.
  

  local lemma lemma4 c c' m mi p q bl i sa sc lres:
      INV_Real c c' m mi p q =>
      0 < i =>
      q.[(bl,i)] = Some lres =>
      p.[format bl i] = Some (sa,sc) =>
      (bl,i+1) \in dom q =>
      p.[format bl (i+1)] = m.[(sa,sc)].
  proof.
  move=>inv0 H_i0 H_q_i H_p_i H_dom_iS.
  cut[]_[]_ hmp1 hmp2 hmp3 _ _:=inv0.
  cut[]c2 h2:=hmp3 _ _ H_dom_iS.
  cut:=hmp1 (format bl (i+1));rewrite in_dom h2/==>help.
  cut:=help (size (format bl i)) _;1:smt(size_ge0 size_cat size_nseq).
  move=>[]b3 c3;rewrite!take_format;..4:smt(size_ge0 size_cat size_nseq).
  cut->/=:!size (format bl i) + 1 <= size bl by smt(size_cat size_nseq size_ge0).
  rewrite nth_cat.
  cut->/=:!size (format bl i) < size bl by smt(size_cat size_ge0).
  rewrite nth_nseq 1:size_cat 1:size_nseq 1:/#.
  pose x:=if _ then _ else _;cut->/={x}:x = format bl i.
  + rewrite/x;case(i = 1)=>//=[->>|hi1].
    - by rewrite/format/=nseq0 cats0//=take_size.
    by rewrite size_cat size_nseq/#.
  pose x:=List.size _ + 1 - List.size _ + 1;cut->/={x}:x=i+1
    by rewrite/x size_cat size_nseq;smt().
  rewrite H_p_i h2=>[]/=[][]->>->>. 
  rewrite Block.WRing.addr0=>H_pm;rewrite H_pm/=. 
  cut[]_[]_[]H_size H:=hmp2 _ _ H_dom_iS.
  cut H_q_i':=H i _;1:smt().
  cut:=H (i+1) _;1:smt().
  by rewrite (take_nth witness)1:/# =>H_q_iS.
  qed.


  local lemma squeeze_squeezeless (D <: NDISTINGUISHER {P, NC, Redo, C}) :
    equiv [ NIndif(Squeeze(SqueezelessSponge(P)),P,DC(D)).main
        ~ NIndif(BlockSponge(P),P,DC(D)).main
        : ={glob D} ==> ={res, glob P, glob D, NC.c}].
  proof.
  proc;inline*;sp;wp. 
  call(: ={glob Perm,glob NC}
      /\ INV_Real 0 NC.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1} 
           NC.queries{1});auto;last first.
  + progress.
    split=>//=;1:split=>//=;smt(getP dom0 map0P in_fset0 dom_set in_fsetU1). 
  + proc;inline*;auto;sp;if;auto;progress.
    - by rewrite INV_Real_addm_mi;2..:smt(supp_dexcepted);split;case:H=>//=;smt().
    - by split;case:H=>//=;smt().
  + proc;inline*;auto;sp;if;auto;progress.
    - rewrite INV_Real_addm_mi;1: by split;case:H=>//=;smt().
      * case:H;smt(invm_dom_rng invmC supp_dexcepted).
      case:H;smt(invm_dom_rng invmC supp_dexcepted).
    - by split;case:H=>//=;smt(). 
  proc;inline*;sp;auto;if;auto;if;auto;sp.
  rcondt{1}1;auto;sp. 
  seq 1 4 : (={glob Perm, glob NC, i, p, n, bl, nb} /\ nb{1} = n{1}
      /\ (lres,sa,sc){1} = (r0,b,c){2} /\ bl{1} = p{2}
      /\ NC.queries{1}.[(p{1},i{1})] = Some lres{1}
      /\ valid p{1} /\ i{1} <= n{1} /\ i{1} = 1
      /\ ! ((p,n) \in dom NC.queries){1}
      /\ INV_Real 0 NC.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1} 
           NC.queries{1}.[(p{1}, i{1}) <- lres{1}]
      /\ Redo.prefixes{1}.[p{1}] = Some (sa{1},sc{1}));last first.
  + auto=>/=.
    while(={glob Perm, glob NC, i, p, n, bl, nb} /\ nb{1} = n{1}
      /\ (lres){1} = (r0){2} /\ bl{1} = p{2} /\ 0 < i{2} <= n{1}
      /\ valid p{1}
      /\ NC.queries{1}.[(p{1},i{1})] = Some lres{1}
      /\ ! ((p,n) \in dom NC.queries){1}
      /\ INV_Real 0 NC.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1} 
           NC.queries{1}.[(p{1}, i{1}) <- lres{1}]
      /\ Redo.prefixes{1}.[format p{1} i{1}] = Some (b{2},c{2}));last first.
    - auto;progress.
      * by rewrite/format/=nseq0 cats0 H4//=.
      * smt().
    sp;if{1};last first.
    - rcondf{2}1;auto;progress.
      * cut:=H4;rewrite set_eq//=in_dom=>inv0.
        cut[]_[]_ hmp1 hmp2 hmp3 _ _:=inv0.
        cut:=hmp1 (format p{hr} (i{hr}+1));rewrite in_dom//=.
        cut[]c3 h3:=hmp3 _ _ H8;rewrite h3/= => help.
        cut[]b4 c4:=help (size p{hr} + i{hr} - 1) _;1:smt(size_cat size_nseq size_ge0).
        rewrite !take_format 1,3:/#;1,2:smt(size_cat size_nseq size_ge0).
        rewrite nth_cat/=nth_nseq/=1:/# -(addzA _ (-1) 1)/=.
        cut->/=:!size p{hr} + i{hr} <= size p{hr} by smt().
        cut->/=:!size p{hr} + i{hr} - 1 < size p{hr} by smt().
        pose x:=if _ then _ else _;cut->/={x}:x = format p{hr} i{hr}.
        + rewrite/x;case(i{hr}=1)=>[->>|/#]//=.
          by rewrite -(addzA _ 1 (-1))/= take_size/format/=nseq0 cats0.
        by rewrite Block.WRing.addr0 (addzAC _ i{hr})/=H5/==>[][][]->>->>->;rewrite h3.
      * rewrite set_eq//=. 
        cut:=H4;rewrite set_eq//==>inv0.
        by cut->:=lemma3 _ _ _ _ _ _ _ _ _ _ _ inv0 H H2 H5 H8.
      * cut:=H4;rewrite set_eq//==>inv0. 
        by cut->:=lemma3 _ _ _ _ _ _ _ _ _ _ _ inv0 H H2 H5 H8.
      * smt().
      * smt().
      * smt(get_oget in_dom).
      * smt(set_eq get_oget in_dom).
      * cut:=H4;rewrite set_eq//==>inv0. 
        cut->:=lemma4 _ _ _ _ _ _ _ _ _ _ _ inv0 H H2 H5 H8;rewrite get_oget 2:/#. 
        cut[]_[]_ hmp1 hmp2 hmp3 _ _:=inv0.
        cut:=hmp1 (format p{2} (i{2}+1));rewrite in_dom//=.
        cut[]c3 h3:=hmp3 _ _ H8;rewrite h3/= => help.
        cut[]b4 c4:=help (size p{2} + i{2} - 1) _;1:smt(size_cat size_nseq size_ge0).
        rewrite !take_format 1,3:/#;1,2:smt(size_cat size_nseq size_ge0).
        rewrite nth_cat/=nth_nseq/=1:/# -(addzA _ (-1) 1)/=.
        cut->/=:!size p{2} + i{2} <= size p{2} by smt().
        cut->/=:!size p{2} + i{2} - 1 < size p{2} by smt().
        pose x:=if _ then _ else _;cut->/={x}:x = format p{2} i{2}.
        + rewrite/x;case(i{2}=1)=>[->>|/#]//=.
          by rewrite -(addzA _ 1 (-1))/= take_size/format/=nseq0 cats0.
        by rewrite in_dom Block.WRing.addr0 (addzAC _ i{2})/=H5/==>[][][]->>->>->;rewrite h3.
    swap{2}4-3;wp;sp=>/=.
    splitwhile{1}1:i0 < size p0 - 1.
    rcondt{1}2;2:rcondf{1}4;auto.
    + while(0 <= i0 <= size p0 -1);last by auto;smt(size_cat size_nseq size_ge0).
      if;auto;1:smt(size_cat size_nseq size_ge0).
      by sp;if;auto;smt(size_cat size_nseq size_ge0).
    + seq 1 : (i0 = size p0 - 1).
      - while(0 <= i0 <= size p0 -1);last by auto;smt(size_cat size_nseq size_ge0).
        if;auto;1:smt(size_cat size_nseq size_ge0).
        by sp;if;auto;smt(size_cat size_nseq size_ge0).
      by if;auto;1:smt();sp;if;auto;smt().
    seq 1 1 : 


  qed.
  
  local lemma equiv_ideal
      (IF <: FUNCTIONALITY{DSqueeze,C})
      (S <: SIMULATOR{DSqueeze,C,IF})
      (D <: NDISTINGUISHER{C,DSqueeze,IF,S}) :
      equiv [ S(IF).init ~ S(IF).init : true ==> ={glob S} ] =>
      equiv [ IF.init ~ IF.init : true ==> ={glob IF} ] =>
      equiv [ Indif(IF,S(IF),DRestr(A(D))).main
            ~ NIndif(Squeeze(IF),S(IF),NDRestr(D)).main
            : ={glob D}
            ==>
              ={res, glob D, glob IF, glob S, glob NC, C.c} ].
  proof.
  move=>S_init IF_init.
  proc;inline*;sp;wp;swap{2}2-1;swap{1}[3..5]-2;sp.
  call(: ={glob IF, glob S, C.c, glob DSqueeze}
      /\ C.c{1} <= NC.c{1} <= max_size
      /\ inv_ideal NC.queries{1} C.queries{1});auto;last first.
  + call IF_init;auto;call S_init;auto;smt(dom_set in_fsetU1 dom0 in_fset0 parse_nil max_ge0). 
  + proc;inline*;sp;if;auto;1:call(: ={glob IF});auto;1:proc(true);progress=>//=. 
  + by proc;inline*;sp;if;auto;1:call(: ={glob IF});auto;proc(true)=>//=. 
  proc;inline*;sp=>/=;if;auto;if{2};last first.
  + wp;conseq(:_==> lres{1} = oget NC.queries.[(p,i)]{1}
      /\ i{1} = n{1}
      /\ inv_ideal NC.queries{1} C.queries{1}
      /\ ={glob IF, glob S, C.c, NC.queries});progress.
    while{1}((0 < i{1} => lres{1} = oget NC.queries.[(p,i)]{1})
      /\ 0 <= i{1} <= n{1}
      /\ ((p{1}, n{1}) \in dom NC.queries{1})
      /\ valid p{1} /\ 0 < n{1}
      /\ inv_ideal NC.queries{1} C.queries{1}
      /\ ={glob IF, glob S, C.c, NC.queries})(n{1}-i{1});progress.
    - sp;rcondf 1;auto;progress;2..:rewrite/#.
      cut[]h1[]h2 h3 :=H5.
      cut h5:=h2 _ _ H2 n{hr} _;1:rewrite/#.
      cut :=h3 _ h5 (i2+1) _;1:rewrite/#.
      by cut<-/= :=h1 _ _ H2 n{hr} _;1:rewrite/#.
    by auto=>/#.

  sp;if{2}.
  + rcondt{2}7;1:auto;wp;sp. print inv_ideal.
    while(={glob IF, glob S, C.c, NC.queries} /\
      (i,n,p,lres){1} = (i0,n0,p0,lres0){2} /\
      inv_ideal NC.queries{1} C.queries{1} /\
      
    alias 


  + sp;auto=>/=.
    rcondf{2}1;1:auto;progress.
    + move:H4;pose s:= List.map _ _;pose c:=C.c{hr};pose p:=p{hr};pose n:=n{hr}.
      apply absurd=>//=.
      print diff_size_prefixe_leq_cat. prefixe_leq_prefixe_cat_size.
      search prefixe (++). 

      cut h:size (format p n) = size p + n - 1 by rewrite size_cat size_nseq max_ler /#.
sear
      cut h':max_size < c + size (format p n) 
      smt(prefixe_sizel).
    while{1}(={n, p, glob IF, glob S, NC.queries}
        /\ i{1} = nb_iter{2} /\ lres{1} = r{2}
        /\ inv_ideal NC.queries{1} C.queries{1}
        /\ max_size <= C.c{1}


    conseq(:_ ==> lres{1} = mkseq (+Block.b0) i{1} /\ i{1} = n{1}
           /\ ={glob IF, glob S} /\ C.c{1} = max_size
           /\ inv_ideal NC.queries{1} C.queries{1}
           /\ NC.queries{1} = NC.queries{2}.[(p{1}, n{1}) <- lres{1}]);
    1:smt(min_ler min_lel max_ler max_ler).
    while{1}(lres{1} = mkseq (+Block.b0) i{1} /\ i{1} = n{1}
           /\ ={glob IF, glob S} /\ C.c{1} = max_size
           /\ inv_ideal NC.queries{1} C.queries{1}
           /\ NC.queries{1} = NC.queries{2}.[(p{1}, n{1}) <- lres{1}])
      (n{1}-i{1});

  rcondt{2}1;1:auto;progress. search min.
  + pose m:=C.c{hr}+_.
    cut/#:1 <=min n{hr} (max 0 (n{hr} + max_size - m)).
    apply min_is_glb=>[/#|].

    rewrite /min/max.
  qed.

print RealIndif.


module IF = {
  proc init = F.RO.init
  proc f = F.RO.get
}.

module S(F : DFUNCTIONALITY) = {
  var m, mi               : smap
  var paths               : (capacity, block list * block) fmap

  proc init() = {
    m     <- map0;
    mi    <- map0;
    (* the empty path is initially known by the adversary to lead to capacity 0^c *)
    paths    <- map0.[c0 <- ([<:block>],b0)];
  }

  proc f(x : state): state = {
    var p, v, y, y1, y2;
    if (!mem (dom m) x) {
      if (mem (dom paths) x.`2) {
        (p,v) <- oget paths.[x.`2]; 
        y1    <- F.f (rcons p (v +^ x.`1));
      } else {
        y1 <$ bdistr;
      }
      y2 <$ cdistr;
      y <- (y1,y2);
      m.[x]             <- y;
      mi.[y]            <- x;
      if (mem (dom paths) x.`2) {
        (p,v) <- oget paths.[x.`2]; 
        paths.[y.`2] <- (rcons p (v +^ x.`1), y.`1);
      }
    } else {   
      y <- oget m.[x];
    }
    return y;
  }

  proc fi(x : state): state = {
    var y, y1, y2;
    if (!mem (dom mi) x) {
      y1       <$ bdistr;
      y2       <$ cdistr;
      y        <- (y1,y2);
      mi.[x]            <- y;
      m.[y]             <- x;
    } else {
      y <- oget mi.[x];
    }
    return y;
  }  
}.

lemma Real_Ideal &m (D <: NDISTINGUISHER): 
  Pr[NIndif(BlockSponge(PC(Perm)), PC(Perm), D).main() @ &m: res /\ C.c <= max_size] <=
  Pr[NIndif(IF,S(IF),DRestr(D)).main() @ &m : res] +
   (max_size ^ 2)%r / 2%r * mu dstate (pred1 witness) + 
   max_size%r * ((2*max_size)%r / (2^c)%r) + 
   max_size%r * ((2*max_size)%r / (2^c)%r).
proof.
search max_size.
  apply (ler_trans _ _ _ (Pr_restr  _ _ _ _ _ _ &m)).
  rewrite !(ler_add2l, ler_add2r);apply lerr_eq.
  apply (eq_trans _ Pr[G3(F.LRO).distinguish() @ &m : res]);1:by byequiv G2_G3.
  apply (eq_trans _ Pr[G3(F.RO ).distinguish() @ &m : res]).
  + by byequiv (_: ={glob G3, F.RO.m} ==> _)=>//;symmetry;conseq (F.RO_LRO_D G3).
  apply (eq_trans _ Pr[G4(F.RO ).distinguish() @ &m : res]);1:by byequiv G3_G4.
  apply (eq_trans _ Pr[G4(F.LRO).distinguish() @ &m : res]);1:by byequiv (F.RO_LRO_D G4).
  by byequiv G4_Ideal.
qed.
  
