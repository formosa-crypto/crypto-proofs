pragma -oldip.
require import Core Int Real RealExtra StdOrder Ring StdBigop IntExtra.
require import List FSet NewFMap Utils Common SLCommon RndO FelTactic Mu_mem.
require import DProd Dexcepted BlockSponge Gconcl.
(*...*) import Capacity IntOrder Bigreal RealOrder BRA.

require (*--*) Handle.

(*** THEORY PARAMETERS ***)
(** Validity of Functionality Queries **)
op valid: block list -> bool = valid_block.
axiom valid_spec p: valid p => p <> [].
axiom valid_ge0 x: 0 <= (parse x).`2.
axiom valid_gt0 x: valid (parse x).`1 => 0 < (parse x).`2.



clone export Handle as Handle0.

module DSqueeze (F : SLCommon.DFUNCTIONALITY) = {
  proc init () : unit = {} 
  proc f (p : block list, n : int) : block list = {
    var lres : block list <- [];
    var b : block <- b0;
    var i : int <- 0;
    if (valid p) {
      b <@ F.f(p);
      while (i < n) {
        i <- i + 1;
        lres <- rcons lres b;
        if (i < n) {
          b <@ F.f(format p (i+1));
        }
      }
    }
    return lres;
  }
}.


module (Squeeze (F : SLCommon.FUNCTIONALITY) : FUNCTIONALITY) = {
  proc init () : unit = {
    C.init();
    F.init();
  }
  proc f = DSqueeze(F).f
}.


module (A (D : DISTINGUISHER) : SLCommon.DISTINGUISHER)
  (F : SLCommon.DFUNCTIONALITY) (P : DPRIMITIVE) = {
  proc distinguish() : bool = {
    var b : bool;
    C.init();
    b <@ DRestr(D,DSqueeze(F),P).distinguish();
    return b;
  }
}.



module NIndif (F : FUNCTIONALITY, P : PRIMITIVE, D : DISTINGUISHER) = {
  proc main () : bool = {
    var b : bool;
    C.init();
    P.init();
    F.init();
    b <@ D(F,P).distinguish();
    return b;
  }
}.



module P = Perm.


section Real_Ideal.

  module Valid (F : DFUNCTIONALITY) = {
    proc init () = {}
    proc f (q : block list, k : int) = {
      var re : block list <- [];
      if (valid q) {
        re <@ F.f(q,k);
      }
      return re;
    }
  }.

  module SimLast (S : SLCommon.SIMULATOR) (F : DFUNCTIONALITY) = S(Last(Valid(F))).

  op (<=) (m1 m2 : (block list, 'b) fmap) = 
    forall x, x <> [] => x \in dom m1 => m1.[x] = m2.[x].

  local lemma leq_add_nin (m1 m2 : (block list, 'b) fmap) (x : block list) (y : 'b):
      m1 <= m2 => 
      ! x \in dom m2 =>
      m1 <= m2.[x <- y].
  proof.
  move=>h_leq H_n_dom a H_a_dom;rewrite getP/=;smt(in_dom).
  qed.


  local lemma leq_add_in (m1 m2 : (block list, 'b) fmap) (x : block list) :
      m1 <= m2 => 
      x \in dom m2 =>
      m1.[x <- oget m2.[x]] <= m2.
  proof.
  move=>h_leq H_n_dom a H_a_dom;rewrite getP/=;smt(in_dom getP).
  qed.

  local lemma leq_nin_dom (m1 m2 : (block list, 'b) fmap) (x : block list) :
      m1 <= m2 =>
      x <> [] =>
      ! x \in dom m2 => ! x \in dom m1 by smt(in_dom).

  local lemma prefixe_leq1 (l : block list) (m : (block list,block) fmap) i :
      0 <= i =>
      format l (i+1) \in dom m =>
      size (format l (i+1)) <= prefixe (format l (i+1+1)) 
        (get_max_prefixe (format l (i+1+1)) (elems (dom m))) <= size (format l (i+1+1)).
  proof. 
  rewrite memE;move=>hi0 H_dom. 
  cut->:(format l (i + 1 + 1)) = format l (i + 1) ++ [b0].
  + by rewrite/format/=-2!(addzA _ 1 (-1))//=nseqSr//-cats1 catA. 
  cut:=prefixe_leq_prefixe_cat_size (format l (i + 1))[b0](elems (dom m)).
  rewrite (prefixe_get_max_prefixe_eq_size _ _ H_dom)//=.
  rewrite (size_cat _ [b0])/=;pose x:= format _ _.
  cut:=get_max_prefixe_max (x ++ [b0]) _ _ H_dom.
  cut->:prefixe (x ++ [b0]) (format l (i + 1)) = size x
    by rewrite prefixeC-{1}(cats0 (format l (i+1)))/x prefixe_cat//=. 
  smt(prefixe_sizel size_cat prefixe_ge0 ).
  qed.

  local lemma prefixe_le1 (l : block list) (m : (block list,block) fmap) i :
      0 <= i =>
      format l (i+1) \in dom m =>
      size (format l (i+1+1)) - prefixe (format l (i+1+1)) 
        (get_max_prefixe (format l (i+1+1)) (elems (dom m))) <= 1.
  proof. 
  smt(prefixe_leq1 size_ge0 size_cat size_nseq).
  qed.

  local lemma leq_add2  (m1 m2 : (block list, 'b) fmap) (x : block list) (y : 'b) :
      m1 <= m2 => 
      ! x \in dom m2 =>
      m1.[x <- y] <= m2.[x <- y] by smt(in_dom getP dom_set in_fsetU1).


  local equiv ideal_equiv (D <: DISTINGUISHER{SLCommon.C, C, IF, BIRO.IRO, S}) :
      SLCommon.IdealIndif(IF, S, SLCommon.DRestr(A(D))).main
      ~
      SLCommon.IdealIndif(IF, S, A(D)).main
      :
      ={glob D} ==> ={glob D, res}.
  proof.
  proc;inline*;auto;sp.
  call(: ={glob IF, glob S, glob A} /\ SLCommon.C.c{1} <= C.c{1}
      /\ SLCommon.C.queries{1} <= F.RO.m{2});auto;last first.
  + progress.
    by move=>x;rewrite getP/=dom_set in_fsetU1 dom0 in_fset0//==>->.
  + proc;inline*;sp;if;auto;sp;rcondt{1}1;1:auto=>/#;sp;if=>//=;2:auto=>/#.
    wp 7 6;conseq(:_==> ={y} /\ ={F.RO.m} /\ ={S.paths, S.mi, S.m}
        /\ SLCommon.C.queries{1} <= F.RO.m{2});1:smt().
    if;auto;smt(leq_add_nin).
  + by proc;inline*;sp;if;auto;sp;rcondt{1}1;1:auto=>/#;sp;if;auto;smt().
  proc;inline*;sp;if;auto;swap 6;auto;sp;if;auto;2:smt(size_ge0).
  case(0 < n{1});last first.
  + sp;rcondf{1}3;2:rcondf{2}4;1,2:auto.
     - by if;auto;if;auto.
    by if{1};2:auto;1:if{1};auto;
     smt(prefixe_ge0 leq_add_in DBlock.dunifin_ll in_dom size_ge0 getP leq_add2).
  splitwhile{1}5: i + 1 < n;splitwhile{2}5: i + 1 < n.
  rcondt{1}6;2:rcondt{2}6;auto.
  * by while(i < n);auto;sp;if;auto;sp;if;auto;if;auto.
  * by while(i < n);auto;sp;if;auto;sp;if;auto;if;auto.
  rcondf{1}8;2:rcondf{2}8;auto.
  * while(i < n);auto.
      by sp;if;auto;sp;if;auto;if;auto.
    sp;if;auto;2:smt();if;auto;smt().
  * while(i < n);auto;2:smt();sp;if;auto;sp;if;auto;if;auto.
  rcondf{1}8;2:rcondf{2}8;auto.
  * while(i < n);auto.
      by sp;if;auto;sp;if;auto;if;auto.
    sp;if;auto;2:smt();if;auto;smt().
  * by while(i < n);auto;2:smt();sp;if;auto;sp;if;auto;if;auto.
  conseq(:_==> ={b,lres,F.RO.m,S.paths,S.mi,S.m}
        /\ i{1} = n{1} - 1
        /\ SLCommon.C.c{1} <= C.c{1} + size bl{1} + i{1}
        /\ SLCommon.C.queries{1} <= F.RO.m{2});1:smt().
  while(={lres,F.RO.m,S.paths,S.mi,S.m,i,n,p,nb,b,bl}
        /\ 0 <= i{1} <= n{1} - 1
        /\ SLCommon.C.queries.[format p (i+1)]{1} = Some b{1}
        /\ p{1} = bs{1} /\ valid p{1} /\ p{1} = bl{1}
        /\ C.c{1} + size p{1} + n{1} - 1 <= max_size
        /\ SLCommon.C.c{1} <= C.c{1} + size bl{1} + i{1}
        /\ SLCommon.C.queries{1} <= F.RO.m{2});progress.
  sp;rcondt{1}1;2:rcondt{2}1;1,2:auto;sp.
  case((x0 \in dom F.RO.m){2});last first.
  * rcondt{2}2;1:auto;rcondt{1}1;1:(auto;smt(leq_nin_dom size_cat size_eq0 size_nseq valid_spec)).
    rcondt{1}1;1:auto;1:smt(prefixe_le1 in_dom size_cat size_nseq). 
    sp;rcondt{1}2;auto;progress.
    - smt().
    - smt().
    - by rewrite!getP/=.
    - smt(prefixe_le1 in_dom).
    - by rewrite!getP/=oget_some leq_add2//=.
  if{1}.
  * rcondt{1}1;1:auto;1:smt(prefixe_le1 in_dom size_cat size_nseq). 
    sp;rcondf{1}2;2:rcondf{2}2;auto;progress.
    - smt().
    - smt().
    - by rewrite!getP/=.
    - smt(prefixe_ge0 prefixe_le1 in_dom).
    - smt(leq_add_in in_dom).
  rcondf{2}2;auto;progress.
  - smt(DBlock.dunifin_ll).
  - smt().
  - smt().
  - smt().
  - smt(set_eq in_dom).
  - smt().
  sp;conseq(:_==> ={F.RO.m,b}
        /\ SLCommon.C.queries.[p]{1} = Some b{1}
        /\ SLCommon.C.c{1} <= C.c{1} + size bl{1}
        /\ SLCommon.C.queries{1} <= F.RO.m{2});progress.
  - smt().
  - smt(nseq0 cats0).
  - smt(size_ge0).
  - smt().
  case(p{2} \in dom F.RO.m{2}).
  + rcondf{2}2;1:auto.
    sp;if{1}.
    - rcondt{1}1;1:auto;1:smt(prefixe_ge0).
      sp;rcondf{1}2;auto;progress.
      * by rewrite!getP/=. 
      * smt(prefixe_ge0).
      * smt(leq_add_in in_dom).
    auto;progress.
    - exact DBlock.dunifin_ll.
    - smt(in_dom).
    - smt(in_dom get_oget).
    - smt(size_ge0).
  rcondt{1}1;1:auto;1:smt(leq_nin_dom in_dom).
  rcondt{1}1;1:auto;1:smt(prefixe_ge0).
  sp;auto;progress.
  + by rewrite!getP/=.
  + smt(prefixe_ge0).
  + rewrite getP/=oget_some leq_add2//=.
  + by rewrite!getP/=.
  + smt(prefixe_ge0).
  + exact leq_add_in.
  qed.


  local module IF'(F : F.RO) = {
    proc init = F.init
    proc f (x : block list) : block = {
      var b : block <- b0;
      var i : int <- 0;
      var p,n;
      (p,n) <- parse x;
      if (valid p) {
        while (i < n) {
          i <- i + 1;
          F.sample(format p i);
        }
        b <@ F.get(x);
      }
      return b;
    }
  }.


  local module SampleFirst (I : BIRO.IRO) = {
    proc init = I.init
    proc f (m : block list, k : int) = {
      var r : block list <- [];
      if (k <= 0) {
        I.f(m,1);
      } else {
        r <- I.f(m,k);
      }
      return r;
    }
  }.


  axiom valid_uniq p1 p2 n1 n2 :
      valid p1 => valid p2 => format p1 n1 = format p2 n2 => p1 = p2 /\ n1 = n2.

  op inv_map (m1 : (block list, block) fmap) (m2 : (block list * int, block) fmap) =
      (forall p n, valid p => (p,n) \in dom m2 <=> format p (n+1) \in dom m1)
      /\ (forall x, x \in dom m1 <=> ((parse x).`1,(parse x).`2-1) \in dom m2)
      /\ (forall p n, valid p => m2.[(p,n-1)] = m1.[format p n])
      /\ (forall x, m1.[x] = m2.[((parse x).`1,(parse x).`2-1)]).


  local module (L (D : DISTINGUISHER) : F.RO_Distinguisher) (F : F.RO) = {
    proc distinguish = SLCommon.IdealIndif(IF'(F), S, A(D)).main
  }.


  local module Valid2 (F : F.RO) = {
    proc init = F.init
    proc f (q : block list) = {
      var r : block  <- b0;
      var s,t;
      (s,t) <- parse q;
      if (valid s) {
        r <@ F.get(q);
      }
      return r;
    }
  }.

  local module (L2 (D : DISTINGUISHER) : F.RO_Distinguisher) (F : F.RO) = {
    proc distinguish = SLCommon.IdealIndif(Valid2(F), S, A(D)).main
  }.

  local equiv Ideal_equiv_valid (D <: DISTINGUISHER{SLCommon.C, C, IF, BIRO.IRO, S}) :
      L(D,F.LRO).distinguish
      ~
      L2(D,F.LRO).distinguish
      :
      ={glob D} ==> ={glob D, res}.
  proof.
  proc;inline*;sp;wp.
  call(: ={glob F.RO, glob S, glob C});auto.
  + proc;sp;if;auto.
    call(: ={glob IF,glob S});auto.
    sp;if;auto;if;auto;sp.
    call(: ={glob IF});2:auto;2:smt();sp;if;auto;1:smt().
    inline F.LRO.sample;call(: ={glob IF});auto;progress.
    by while{1}(true)(n{1}-i{1});auto;smt().
  + by proc;sim.
  proc;sp;if;auto;sp;call(: ={glob IF,glob S});auto.
  sp;if;auto.
  while(={glob S,glob IF,lres,i,n,p,b}).
  + sp;if;auto.
    call(: ={glob IF});auto.
    sp;if;auto;progress;1,2:smt().
    call(: ={glob IF});auto.
    conseq(:_==> true);auto. 
    by inline*;while{1}(true)(n{1}-i{1});auto;smt().
  call(: ={glob IF});auto;sp;if;auto;1:smt().
  call(: ={glob IF});auto. 
  conseq(:_==> true);auto. 
  by inline*;while{1}(true)(n{1}-i{1});auto;smt().
  qed.  


  local equiv ideal_equiv2 (D <: DISTINGUISHER{SLCommon.C, C, IF, BIRO.IRO, S}) :
    L2(D,F.RO).distinguish ~ SLCommon.IdealIndif(IF,S,A(D)).main
    : ={glob D} ==> ={glob D, res}.
  proof.
  proc;inline*;sp;wp.
  call(: ={glob F.RO, glob S, glob C});auto.
  + proc;auto;sp;if;auto.
    call(: ={glob F.RO, glob S});auto.
    if;1,3:auto;sim;if;auto.
    call(: ={glob F.RO});2:auto. 
    (* This is false *)
    admit.
  + by proc;sim.
  proc;sp;if;auto;sp.
  call(: ={glob F.RO});auto;sp;if;auto;inline*;auto;sp.
  rcondt{1}1;1:auto;1:smt(parse_valid parseK formatK);sp.
  case(0 < n{1});last first.
  + by rcondf{2}4;1:auto;rcondf{1}5;auto.
  while(={lres,F.RO.m,i,n,p,b} /\ valid p{1} /\ 0 <= i{1} <= n{1}).
  + sp;if;1:auto.
    - by sp;rcondt{1}1;auto;smt(parse_valid parseK formatK).
    auto;smt(parse_valid parseK formatK).
  auto;smt(parse_valid parseK formatK).
  qed.


  local module IF2(F : F.RO) = {
    proc init = F.init
    proc f (x : block list) : block = {
      var b : block <- b0;
      var i : int <- 0;
      var p,n;
      (p,n) <- parse x;
      if (valid p) {
        if (0 < n) {
          while (i < n) {
            i <- i + 1;
            F.sample(format p i);
          }
          b <@ F.get(x);
        } else {
          F.sample(x);
        }
      }
      return b;
    }
  }.
  

  local module (L3 (D : DISTINGUISHER) : F.RO_Distinguisher) (F : F.RO) = {
    proc distinguish = SLCommon.IdealIndif(IF2(F), S, A(D)).main
  }.

  

  local equiv Ideal_equiv3 (D <: DISTINGUISHER{SLCommon.C, C, IF, BIRO.IRO, S}) :
      L(D,F.RO).distinguish ~ L3(D,F.RO).distinguish
      : ={glob D} ==> ={glob D, res}.
  proof.
  proc;inline*;auto;sp.
  call(: ={glob S, glob F.RO, glob C});auto;first last.
  + by proc;sim. 
  + proc;sp;if;auto;call(: ={glob F.RO});auto;sp.
    inline*;if;auto;sp.
    rcondt{1}1;1:auto;1:smt(parse_valid parseK formatK).
    rcondt{2}1;1:auto;1:smt(parse_valid parseK formatK).
    rcondt{2}1;1:auto;1:smt(parse_valid parseK formatK).
    rcondt{1}1;1:auto;1:smt(parse_valid parseK formatK);sp.
    rcondf{1}3;1:auto;1:smt(parse_valid parseK formatK);sp.
    rcondt{2}1;1:auto;1:smt(parse_valid parseK formatK);sp.
    rcondf{2}3;1:auto;1:smt(parse_valid parseK formatK);sp.
    case(0 < n{1});auto;last first.
    - by rcondf{1}8;1:auto;rcondf{2}8;1:auto;sim=>/#.
    while(={i,n,p,lres,b,F.RO.m} /\ valid p{1} /\ 0 <= i{1} <= n{1}).
    - sp;if;1,3:auto=>/#.
      sp;rcondt{2}1;1:auto;1:smt(parse_valid parseK formatK).
      rcondt{1}1;2:rcondt{2}1;1,2:(auto;smt(parseK formatK parse_valid)).
      conseq(:_==> ={b,F.RO.m});2:sim;progress=>/#.
    by wp 5 5;conseq(:_==> ={F.RO.m,r,x2});2:sim;smt(). 
  proc;sp;if;auto;call(: ={F.RO.m, glob S});auto.
  if;1,3:auto;sim;if;auto.
  call(: ={glob F.RO});auto;sp;inline*. 
  if;1,3:auto;1:smt().
  rcondt{2}1;1:auto;1:smt(parse_valid parseK formatK valid_gt0);sim;smt().
  qed.

  local module D2 (D : DISTINGUISHER) (F : F.RO) = {
    proc distinguish = D(FC(DSqueeze(Valid2(F))), PC(S(Valid2(F)))).distinguish
  }.

  local module D3 (D : DISTINGUISHER) (F : F.RO) = {
    proc distinguish = D(FC(DSqueeze(IF'(F))), PC(S(IF'(F)))).distinguish
  }.


  local lemma equiv_ideal (D <: DISTINGUISHER{SLCommon.C, C, IF, BIRO.IRO, S,F.FRO}) &m:
    Pr[SLCommon.IdealIndif(IF,S,SLCommon.DRestr(A(D))).main() @ &m : res] =
    Pr[L3(D,F.RO).distinguish() @ &m : res].
  proof.
  cut->:Pr[SLCommon.IdealIndif(IF, S, SLCommon.DRestr(A(D))).main() @ &m : res]
      = Pr[SLCommon.IdealIndif(IF, S, A(D)).main() @ &m : res].
  + by byequiv(ideal_equiv D)=>//=.
  cut<-:Pr[L(D, F.RO).distinguish() @ &m : res] = 
        Pr[L3(D, F.RO).distinguish() @ &m : res].
  + by byequiv(Ideal_equiv3 D).
  cut<-:Pr[L2(D,F.RO).distinguish() @ &m : res] =
        Pr[SLCommon.IdealIndif(IF,S,A(D)).main() @ &m : res].
  + by byequiv(ideal_equiv2 D). 
  cut->:Pr[L2(D, F.RO).distinguish() @ &m : res] = 
        Pr[L2(D,F.LRO).distinguish() @ &m : res].
  + byequiv=>//=;proc;sp;inline*;sp;wp.
    transitivity{1} {
          b1 <@ D2(D,F.RO).distinguish();
        }
        (={glob D, glob F.RO, glob C, glob S} ==> ={b1})
        (={glob D, glob F.RO, glob C, glob S} ==> ={b1});progress;1:smt();1:sim.
    transitivity{1} {
          b1 <@ D2(D,F.LRO).distinguish();
        }
        (={glob D, glob F.RO, glob C, glob S} ==> ={b1})
        (={glob D, glob F.RO, glob C, glob S} ==> ={b1});progress;1:smt();2:sim.
    by call(F.RO_LRO_D (D2(D)));auto.
  cut->:Pr[L(D, F.RO).distinguish() @ &m : res] = 
        Pr[L(D,F.LRO).distinguish() @ &m : res].
  + byequiv=>//=;proc;sp;inline*;sp;wp.
    transitivity{1} {
          b1 <@ D3(D,F.RO).distinguish();
        }
        (={glob D, glob F.RO, glob C, glob S} ==> ={b1})
        (={glob D, glob F.RO, glob C, glob S} ==> ={b1});progress;1:smt();1:sim.
    transitivity{1} {
          b1 <@ D3(D,F.LRO).distinguish();
        }
        (={glob D, glob F.RO, glob C, glob S} ==> ={b1})
        (={glob D, glob F.RO, glob C, glob S} ==> ={b1});progress;1:smt();2:sim.
    by call(F.RO_LRO_D (D3(D)));auto.
  rewrite eq_sym.
  by byequiv(Ideal_equiv_valid D).
  qed.


  local equiv double_squeeze :
    DSqueeze(IF2(F.RO)).f ~ Squeeze(IF).f :
    ={arg, F.RO.m} ==> ={res, F.RO.m}.
  proof.
  proc;inline*;auto;sp;if;auto;sp.
  rcondt{1}1;1:(auto;smt(parse_valid valid_gt0)).
  rcondt{1}1;1:(auto;smt(parse_valid valid_gt0)).
  rcondt{1}1;1:(auto;smt(parse_valid valid_gt0));sp.
  rcondf{1}3;1:(auto;smt(parse_valid valid_gt0));sp.
  case(0 < n{1});last first.
  + rcondf{2}4;1:auto=>/#.
    rcondf{1}8;1:auto=>/#.
    rcondf{1}5.
    + auto;smt(nseq0 cats0 dom_set in_fsetU1 parse_valid).
    by wp;rnd{1};auto;smt(DBlock.dunifin_ll nseq0 cats0 parse_valid set_eq in_dom).
  while(={F.RO.m,n,b,i,lres,p} /\ valid p{1} /\ 0 < n{1} /\ 0 <= i{1} <= n{1}
      /\ (i{1}+1 < n{1} => (forall j, 0 <= j <= i{1} => format p{1} (j+1) \in dom F.RO.m{1}))).
  + sp;if;1,3:auto=>/#. 
    sp;rcondt{1}1;1:(auto;smt(parseK formatK)).
    rcondt{1}1;1:(auto;smt(parseK formatK valid_gt0)).
    conseq(:_==> ={b,F.RO.m} /\ (forall (j : int), 0 <= j <= i{1} =>
        format p{1} (j+1) \in dom F.RO.m{2}));1:smt().
    splitwhile{1} 1 : i1 + 1 < n1.
    rcondt{1}2;1:auto.
    + by while(i1 < n1);auto;smt(valid_gt0 parseK formatK).
    rcondf{1}7;1:auto.
    + by while(i1 < n1);auto;smt(valid_gt0 parseK formatK).
    seq 3 0 : (={F.RO.m,x0} /\ x0{1} = format p{1} (i{1}+1) /\ x4{1} = x0{1} /\
      (forall (j : int), 0 <= j < i{1} => format p{1} (j+1) \in dom F.RO.m{2}));last first.
    + sp;rcondf{1}5;1:auto;1:smt(dom_set in_fsetU1).
      by wp;rnd{1};auto;smt(DBlock.dunifin_ll dom_set in_fsetU1).
    wp.
    conseq(:_==> ={F.RO.m} /\ i1{1} + 1 = n1{1});1:smt(parseK formatK).
    while{1}(={F.RO.m} /\ 0 < i1{1} + 1 <= n1{1} <= n{1} /\
      (forall j, 0 <= j < n1{1}-1 => format p1{1} (j+1) \in dom F.RO.m{1}))(n1{1}-i1{1}).
    + by progress;sp;rcondf 2;auto;smt(DBlock.dunifin_ll).
    by auto;smt(formatK parseK).
  by rcondf{1}5;2:(wp;rnd{1});auto;smt(DBlock.dunifin_ll dom_set in_fsetU1 nseq0 cats0 parse_valid).
  qed.


  local equiv Ideal_equiv (D <: DISTINGUISHER{SLCommon.C, C, IF, BIRO.IRO, S}) :
      L3(D,F.RO).distinguish
      ~
      IdealIndif(Squeeze(IF), SimLast(S), DRestr(D)).main
      :
      ={glob D} ==> ={glob D, res}.
  proof.
  proc;inline*;auto;sp.
  call(: ={glob S, glob C, F.RO.m});auto;first last.
  + by proc;inline*;sp;if;auto;sp;if;auto.
  + proc;sp;if;auto;sp. 
    by call(double_squeeze);auto;progress.
  proc;sp;if;auto;inline{1}1;inline{2}1;sp;if;1:auto;sim;if;auto.
  sp;inline*;sp;if;1,3:(auto;smt(parse_valid));sp.
  rcondt{1}1;1:(auto;smt(parse_valid valid_gt0)).
  rcondt{2}1;1:(auto;smt(parse_valid valid_gt0));sp.
  rcondt{1}1;1:(auto;smt(parse_valid valid_gt0));sp.
  splitwhile{2}4: i + 1 < n.
  rcondt{2}5;1:auto.
  + while(i < n);1:(sp;if);auto;smt(valid_gt0).
  rcondf{2}7;1:auto.
  + while(i < n);1:(sp;if);auto;smt(valid_gt0).
  rcondf{2}7;1:auto.
  + while(i < n);1:(sp;if);auto;smt(valid_gt0).
  seq 3 4 : (F.RO.m.[x0]{1} = Some b{2} /\ ={x, C.c, S.paths, F.RO.m});last first.
  + sp;rcondf{1}2;auto;smt(in_dom DBlock.dunifin_ll last_rcons).
  conseq(: _==> F.RO.m{1}.[format p0{1} i{1}] = Some b{2} /\ i{1} = n{1} /\ ={F.RO.m});progress.
  + rewrite-H7;congr;smt(parseK formatK).
  while(={F.RO.m,n} /\ i{1} = i{2} + 1 /\ p0{1} = p1{2} /\ i{1} <= n{1}
      /\ F.RO.m{1}.[format p0{1} i{1}] = Some b{2}).
  + sp;rcondt{2}1;auto;smt(get_oget in_dom getP).
  auto;smt(in_dom get_oget getP formatK parseK nseq0 cats0 valid_gt0).
  qed.



  local lemma equiv_ideal' (D <: DISTINGUISHER{SLCommon.C, C, IF, BIRO.IRO, S,F.FRO}) &m:
    Pr[SLCommon.IdealIndif(IF,S,SLCommon.DRestr(A(D))).main() @ &m : res] =
    Pr[IdealIndif(Squeeze(IF), SimLast(S), DRestr(D)).main() @ &m : res].
  proof.
  rewrite (equiv_ideal D &m).
  byequiv(Ideal_equiv D)=>//.
  qed.


  (* Real part *)


  
  pred inv_ideal (squeeze : (block list * int, block list) fmap)
                 (c : (block list, block) fmap) =
    (forall p n, (p,n) \in dom squeeze => 
      forall i, 1 <= i <= n => (p,i) = parse (format p i)) /\
    (forall p n, (p,n) \in dom squeeze => 
      forall i, 1 <= i <= n => format p i \in dom c) /\
    (forall l, l \in dom c => 
      forall i, 1 <= i <= (parse l).`2 => ((parse l).`1,i) \in dom squeeze).


  inductive m_p (m : (state, state) fmap) (p : (block list, state) fmap) =
  | IND_M_P of (p.[[]] = Some (b0, c0))
        & (forall l, l \in dom p => forall i, 0 <= i < size l =>
            exists b c, p.[take i l] = Some (b,c) /\
            m.[(b +^ nth witness l i, c)] = p.[take (i+1) l]).


  inductive INV_Real
    (c1 c2 : int)
    (m mi : (state, state) fmap)
    (p : (block list, state) fmap) =
    | INV_real of (c1 <= c2)
                & (m_p m p)
                & (invm m mi).

  local lemma INV_Real_incr c1 c2 m mi p :
      INV_Real c1 c2 m mi p =>
      INV_Real (c1 + 1) (c2 + 1) m mi p.
  proof. by  case;progress;split=>//=/#. qed.

  local lemma INV_Real_addm_mi c1 c2 m mi p x y :
      INV_Real c1 c2 m mi p =>
      ! x \in dom m =>
      ! y \in rng m =>
      INV_Real c1 c2 m.[x <- y] mi.[y <- x] p.
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

  local lemma all_prefixes_of_INV_real c1 c2 m mi p:
      INV_Real c1 c2 m mi p =>
      all_prefixes p.
  proof.
  move=>[]_[]Hp0 Hmp1 _ l H_dom i.
  smt(take_le0 take_oversize size_take take_take take_size nth_take in_dom).
  qed.

  local lemma lemma2 c1 c2 m mi p bl i sa sc:
      INV_Real c1 c2 m mi p =>
      1 < i =>
      valid bl =>
      (sa,sc) \in dom m =>
      ! (format bl i) \in dom p =>
      p.[format bl (i-1)] = Some (sa,sc) =>
      INV_Real c1 c2 m mi p.[format bl i <- oget m.[(sa,sc)]].
  proof.
  move=>inv0 h1i h_valid H_dom_m H_dom_p H_p_val.
  split;cut[]//=_[] hmp0 hmp1 hinvm:=inv0;split=>//=.
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


  local lemma equiv_sponge (D <: DISTINGUISHER {P, Redo, C, SLCommon.C}) :
    equiv [ GReal(A(D)).main
      ~ NIndif(Squeeze(SqueezelessSponge(P)),P,DRestr(D)).main
      : ={glob D} ==> ={res, glob D, glob P, C.c} /\ SLCommon.C.c{1} <= C.c{2} <= max_size].
  proof.
  proc;inline*;sp;wp.
  call(: ={Redo.prefixes, glob P, C.c} /\ C.c{1} <= max_size /\
    INV_Real SLCommon.C.c{1} C.c{2} Perm.m{1} Perm.mi{1} Redo.prefixes{1});auto;last first.
  + progress. 
    + exact max_ge0.
    + by split=>//=;1:split;smt(dom0 in_fset0 dom_set in_fsetU1 getP map0P).
    by case:H2=>//=. 
  + by proc;inline*;auto;sp;if;auto;sp;if;auto;
      smt(INV_Real_addm_mi INV_Real_incr supp_dexcepted).
  + proc;inline*;auto;sp;if;auto;sp;if;auto;progress.
    + apply INV_Real_incr=>//=.
      apply INV_Real_addm_mi=>//=.
      + case:H0=>H_c H_m_p H_invm;rewrite (invm_dom_rng _ _ H_invm)//=. 
        by move:H3;rewrite supp_dexcepted.
      case:H0=>H_c H_m_p H_invm;cut<-//:=(invm_dom_rng Perm.mi{2} Perm.m{2}). 
      by rewrite invmC.
    + exact INV_Real_incr.
  + proc;inline*;sp;if;auto.
    swap 6;wp;sp=>/=;if;auto;last by progress;split;case:H0=>//=;smt(size_ge0).
    conseq(: p{2} = bl{2} /\ n{2} = nb{2} /\ lres{2} = [] /\ b{2} = b0 /\
    i{2} = 0 /\ p{1} = bl{1} /\ n{1} = nb{1} /\ lres{1} = [] /\ b{1} = b0 /\
    i{1} = 0 /\ z{2} = [] /\ z{1} = [] /\ ={bl, nb} /\ ={Redo.prefixes} /\
    ={Perm.mi, Perm.m} /\ ={C.c} /\
    INV_Real SLCommon.C.c{1} C.c{2} Perm.m{1} Perm.mi{1} Redo.prefixes{1} /\
    C.c{1} + size bl{1} + max (nb{1} - 1) 0 <= max_size /\ valid p{1}
  ==> ={lres} /\ ={Redo.prefixes} /\ ={Perm.mi, Perm.m} /\
    C.c{1} + size bl{1} + max (nb{1} - 1) 0 =
    C.c{2} + size bl{2} + max (nb{2} - 1) 0 /\
    INV_Real SLCommon.C.c{1} (C.c{2} + size bl{2} + max (nb{2} - 1) 0)
    Perm.m{1} Perm.mi{1} Redo.prefixes{1});progress.
    sp.
    seq 2 2:(={i,n,p,lres,nb,bl,b,glob P,glob C,glob Redo}
           /\  INV_Real SLCommon.C.c{1} (C.c{2} + size bl{2})
                 Perm.m{1} Perm.mi{1} Redo.prefixes{1}
           /\  (n,p){1} = (nb,bl){1} /\ lres{1} = [] /\ i{1} = 0
           /\  valid p{1}
           /\ Redo.prefixes.[p]{1} = Some (b,sc){1}).
    + exists* Redo.prefixes{1},SLCommon.C.c{1};elim* => pref count/=.
      wp;conseq(:_==> ={i0,p0,i,p,n,nb,bl,sa,lres,C.c,glob Redo,glob Perm}
            /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p0{1} = p{1} /\ i0{1} = size p{1}
            /\ Redo.prefixes{1}.[take i0{1} p{1}] = Some (sa{1},sc{1})
            /\ INV_Real count C.c{1} Perm.m{1} Perm.mi{1} pref
            /\ (forall l, l \in dom Redo.prefixes{1} => 
                 l \in dom pref \/ (exists j, 0 < j <= i0{2} /\ l = take j p{1}))
            /\ (forall l, l \in dom pref => pref.[l] = Redo.prefixes{1}.[l])
            /\ SLCommon.C.c{1} <= count + i0{1} <= C.c{1} + i0{1}
            /\ (forall j, 0 <= j < i0{1} =>
                 exists b c, Redo.prefixes{1}.[take j p{1}] = Some (b,c) /\
                 Perm.m{1}.[(b +^ nth witness p{1} j, c)] = 
                 Redo.prefixes{1}.[take (j+1) p{1}]));
        progress. 
      - cut inv0:=H3;cut[]h_c1c2[]Hmp0 Hmp1 Hinvm:=inv0;split=>//=.
        - case:inv0;smt(size_ge0).
        split=>//=.
        - smt(in_dom).
        - move=>l H_dom_R i []Hi0 Hisize;cut:=H4 l H_dom_R.
          case(l \in dom Redo.prefixes{2})=>H_in_pref//=.
          * cut:=Hmp1 l H_in_pref i _;rewrite//=.
            rewrite ?H5//=;1:smt(in_dom).
            case(i+1 < size l)=>h;1:smt(in_dom).
            by rewrite take_oversize 1:/#.
          move=>[]j[][]hj0 hjsize ->>.
          cut:=Hisize;rewrite size_take 1:/#.
          pose k:=if _ then _ else _;cut->>Hij{k}:k=j by rewrite/#.
          by rewrite!take_take!min_lel 1,2:/# nth_take 1,2:/#;smt(in_dom).
        - smt(getP oget_some in_dom take_oversize).
      while( ={i0,p0,i,p,n,nb,bl,sa,sc,lres,C.c,glob Redo,glob Perm}
        /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p0{1} = p{1} /\ 0 <= i0{1} <= size p{1}
        /\ Redo.prefixes{1}.[take i0{1} p{1}] = Some (sa{1},sc{1})
        /\ INV_Real count C.c{1} Perm.m{1} Perm.mi{1} pref
        /\ (forall l, l \in dom Redo.prefixes{1} => 
             l \in dom pref \/ (exists j, 0 < j <= i0{2} /\ l = take j p{1}))
        /\ (forall l, l \in dom pref => pref.[l] = Redo.prefixes{1}.[l])
        /\ SLCommon.C.c{1} <= count + i0{1} <= C.c{1} + i0{1}
        /\ (i0{1} < size p0{1} => 
             take (i0{1}+1) p{1} \in dom Redo.prefixes{1} =>
             Redo.prefixes{1} = pref)
        /\ all_prefixes Redo.prefixes{1}
        /\ (forall j, 0 <= j < i0{1} =>
             exists b c, Redo.prefixes{1}.[take j p{1}] = Some (b,c) /\
             Perm.m{1}.[(b +^ nth witness p{1} j, c)] = 
             Redo.prefixes{1}.[take (j+1) p{1}]));last first.
      + auto;progress.
        - exact size_ge0.
        - by rewrite take0;cut[]_[]->//=:=H.
        - smt().
        - by cut[]->//=:=H.
        - smt(all_prefixes_of_INV_real).
        - smt().
        - smt().
      if;auto;progress.
      - smt().
      - smt().
      - smt(get_oget in_dom).
      - smt(in_dom).
      - smt().
      - smt().
      - smt(all_prefixes_of_INV_real in_dom take_take size_take).
      - case(j < i0{2})=>hj;1:smt().
        cut<<-/=:j = i0{2} by smt().
        cut->>:=H7 H10 H12.
        cut[]_[]hmp0 hmp1 _:=H2.
        cut[]b3 c3:=hmp1 _ H12 j _;1:smt(size_take).
        smt(take_take nth_take size_take).
      sp;if;auto;progress. 
      - smt().
      - smt().
      - smt(getP get_oget in_dom).
      - rewrite INV_Real_addm_mi//=;smt(supp_dexcepted). 
      - smt(dom_set in_fsetU1).
      - smt(getP in_dom).
      - smt().
      - smt().
      - move:H17;apply absurd=>//=_;rewrite dom_set in_fsetU1.
        pose x:=_ = _;cut->/={x}:x=false by smt(size_take).
        move:H12;apply absurd=>//=.
        smt(all_prefixes_of_INV_real dom_set in_fsetU1 take_take size_take).
      - move=>l;rewrite!dom_set!in_fsetU1;case=>[H_dom|->>]/=;1:smt(in_fsetU1).
        move=>j;rewrite in_fsetU1.
        case(0 <= j)=>hj0;2:smt(in_dom take_le0).
        case(j < i0{2} + 1)=>hjiS;2:smt(in_dom take_take).
        rewrite take_take/min hjiS//=;left.
        cut:=(take_take bl{2} j i0{2});rewrite min_lel 1:/#=><-.
        smt(all_prefixes_of_INV_real in_dom).
      - smt(getP get_oget in_dom dom_set in_fsetU1).
      - smt(getP get_oget in_dom).
      - smt().
      - smt(getP get_oget in_dom).
      - smt(dom_set in_fsetU1).
      - smt(getP in_dom).
      - smt().
      - smt().
      - move:H15;apply absurd=>//=_;rewrite dom_set in_fsetU1.
        pose x:=_ = _;cut->/={x}:x=false by smt(size_take).
        move:H12;apply absurd=>//=.
        cut:=take_take bl{2}(i0{2} + 1)(i0{2} + 1 + 1);rewrite min_lel 1:/# =><-h. 
        by rewrite (H8 _ h).
      - move=>l;rewrite!dom_set!in_fsetU1;case=>[H_dom|->>]/=;1:smt(in_fsetU1).
        move=>j;rewrite in_fsetU1.
        case(0 <= j)=>hj0;2:smt(in_dom take_le0).
        case(j < i0{2} + 1)=>hjiS;2:smt(in_dom take_take).
        rewrite take_take/min hjiS//=;left.
        cut:=(take_take bl{2} j i0{2});rewrite min_lel 1:/#=><-.
        smt(all_prefixes_of_INV_real in_dom).
      - smt(getP get_oget in_dom dom_set in_fsetU1).
  sp;case(0 < n{1});last first.
  - rcondf{1}1;2:rcondf{2}1;auto;1:smt().
    splitwhile{1} 1 : i + 1 < n;splitwhile{2} 1 : i + 1 < n.
    rcondt{1}2;2:rcondt{2}2;auto;progress.
    + while(i < n);auto.
      by sp;if;auto;sp;while(i < n);auto;if;auto;sp;if;auto.
    + while(i < n);auto.
      by sp;if;auto;sp;while(i < n);auto;if;auto;sp;if;auto.
    rcondf{1}4;2:rcondf{2}4;auto.
    + while(i < n);auto;2:smt().
      by sp;if;auto;sp;while(i < n);auto;if;auto;sp;if;auto.
    + while(i < n);auto;2:smt().
      by sp;if;auto;sp;while(i < n);auto;if;auto;sp;if;auto.
    rcondf{1}4;2:rcondf{2}4;1,2:auto.
    + while(i < n);auto;2:smt().
      by sp;if;auto;sp;while(i < n);auto;if;auto;sp;if;auto.
    + while(i < n);auto;2:smt().
      by sp;if;auto;sp;while(i < n);auto;if;auto;sp;if;auto.
    conseq(:_==> ={i,n,p,lres,nb,bl,b,glob P,glob C,glob Redo}
           /\  INV_Real SLCommon.C.c{1} (C.c{2} + size bl{2} + i{1} - 1)
                 Perm.m{1} Perm.mi{1} Redo.prefixes{1}
           /\  i{1} = n{1});1:smt();wp. 
    conseq(:_==> ={i,n,p,lres,nb,bl,b,glob P,glob C,glob Redo}
           /\  INV_Real SLCommon.C.c{1} (C.c{2} + size bl{2} + i{1})
                 Perm.m{1} Perm.mi{1} Redo.prefixes{1}
           /\  i{1}+1 = n{1});1:smt(). 
    while(={i,n,p,lres,nb,bl,b,glob P,glob C,glob Redo}
           /\  INV_Real SLCommon.C.c{1} (C.c{2} + size bl{2} + i{1})
                 Perm.m{1} Perm.mi{1} Redo.prefixes{1}
           /\  (n,p){1} = (nb,bl){1} /\ 0 < i{1}+1 <= n{1}
           /\  valid p{1}
           /\  (exists c2, Redo.prefixes.[format p (i+1)]{1} = Some (b,c2){1}));
    last by auto;smt(nseq0 cats0). 
  sp;rcondt{1}1;2:rcondt{2}1;auto.
  sp.
  splitwhile{1} 1 : i1 < size p1 - 1;splitwhile{2} 1 : i1 < size p1 - 1.
  rcondt{1}2;2:rcondt{2}2;1,2:by auto;
    while(i1 < size p1);auto;1:if;2:(sp;if);auto;smt(size_cat size_nseq size_ge0).
  rcondf{1}4;2:rcondf{2}4;1,2:by auto;
    seq 1 : (i1 = size p1 - 1);1:(auto;
      while(i1 < size p1);auto;1:if;2:(sp;if);auto;smt(size_cat size_nseq size_ge0));
    if;sp;2:if;auto;smt(size_cat size_nseq size_ge0).
  wp=>//=.
  wp;conseq(:_==> ={sa0,sc0,glob Redo,glob Perm}
          /\ INV_Real SLCommon.C.c{1} (C.c{1} + size bl{2} + i{1}) 
               Perm.m{1} Perm.mi{1} Redo.prefixes{1}
          /\ (format p{1} i{1} \in dom Redo.prefixes{1})
          /\ exists (c2 : capacity), Redo.prefixes{1}.[format p{1} (i{1}+1)] = Some (sa0{1}, c2));progress.
  + smt(size_ge0).
  + smt(size_ge0).
  + smt().
  seq 1 1 : (={nb,bl,n,p,p1,i,i1,lres,sa0,sc0,C.c,glob Redo,glob Perm}
          /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p1{1} = format p{1} (i{1}+1)
          /\ 1 <= i{1} < n{1} /\ valid p{1} /\ i1{1} = size p1{1} - 1
          /\ Redo.prefixes{1}.[format p{1} i{1}] = Some (sa0{1},sc0{1})
          /\ INV_Real SLCommon.C.c{1} (C.c{1} + size bl{2} + i{1} - 1) Perm.m{1} Perm.mi{1}
               Redo.prefixes{1});last first.
  + if;auto;progress. 
    - by split;case:H3=>//=;smt().
    - by rewrite in_dom H2//=.
    - by move:H4;rewrite -(addzA _ _ 1)/=take_size;smt(get_oget in_dom).
    sp;if;auto;progress.
    - move:H4 H5;rewrite!getP/=!oget_some nth_last -(addzA _ _ 1)/=take_size.
      rewrite last_cat last_nseq 1:/# Block.WRing.addr0;progress. 
      cut//=:=lemma2(SLCommon.C.c{1} + 1)(C.c{2} + size bl{2} + i{2})
        Perm.m{2}.[(sa0_R, sc0{2}) <- y2L] Perm.mi{2}.[y2L <- (sa0_R, sc0{2})]
        Redo.prefixes{2} bl{2} (i{2}+1) sa0_R sc0{2}.
      rewrite -(addzA _ 1)/=H1/=!dom_set!in_fsetU1/=H4/=H2/=getP/=oget_some/=.
      cut->->//=:y2L = (y2L.`1, y2L.`2);1,-1:smt().
      rewrite INV_Real_addm_mi//=;2:smt(supp_dexcepted). 
      by cut:=H3=>hinv0;split;case:hinv0=>//=/#.
    - by rewrite dom_set in_fsetU1//=-(addzA _ _ 1)/=take_size in_dom H2.
    - by rewrite!getP-(addzA _ _ 1)/=take_size/=;smt().
    - move:H4 H5;rewrite nth_last -(addzA _ _ 1)/=take_size.
      rewrite last_cat last_nseq 1:/# Block.WRing.addr0;progress. 
      pose a:=(_, _);cut->/={a}:a = oget Perm.m{2}.[(sa0_R, sc0{2})] by smt().
      apply lemma2=>//=;first cut:=H3=>hinv0;split;case:hinv0=>//=/#.
      smt().
      smt().
    - by rewrite dom_set in_fsetU1//=-(addzA _ _ 1)/=take_size;smt(in_dom).
    - by rewrite!getP-(addzA _ _ 1)/=take_size/=;smt().
  alias{1} 1 pref = Redo.prefixes;sp;alias{1} 1 count = SLCommon.C.c.
  alias{1} 1 pm = Perm.m;sp;alias{1} 1 pmi = Perm.mi;sp.
  conseq(:_==> ={nb,bl,n,p,p1,i,i1,lres,sa0,sc0,C.c,glob Redo,glob Perm}
        /\ pmi{1} = Perm.mi{1} /\ pm{1} = Perm.m{1}
        /\ pref{1} = Redo.prefixes{1} /\ SLCommon.C.c{1} = count{1}
        /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p1{1} = format p{1} (i{1}+1)
        /\ i1{1} = size p1{1} - 1
        /\ Redo.prefixes{1}.[format p{1} (i1{1} - size p{1} + 1)] = 
             Some (sa0{1}, sc0{1}));progress. 
  + smt(size_cat size_nseq set_eq in_dom).
  + move:H8;rewrite size_cat size_nseq-(addzA _ 1 (-1))/=/max H0/=.
    by pose x:= Int.(+) _ _;cut->/={x}: x = i_R + 1 by smt().
  + move:H8;rewrite size_cat size_nseq-(addzA _ 1 (-1))/=/max H0/=;smt().
  splitwhile{1}1:i1 < size p;splitwhile{2}1:i1 < size p.
  while(={nb,bl,n,p,p1,i,i1,lres,sa0,sc0,C.c,glob Redo,glob Perm}
        /\ INV_Real SLCommon.C.c{1} (C.c{1} + size bl{2} + i{1} - 1)
             Perm.m{1} Perm.mi{1} Redo.prefixes{1}
        /\ pmi{1} = Perm.mi{1} /\ pm{1} = Perm.m{1}
        /\ pref{1} = Redo.prefixes{1} /\ SLCommon.C.c{1} = count{1}
        /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p1{1} = format p{1} (i{1}+1)
        /\ (format p{1} i{1} \in dom Redo.prefixes{1})
        /\ size p{1} <= i1{1} <= size p1{1} - 1 /\ valid p{1}
        /\ Redo.prefixes{1}.[format p{1} (i1{1} - size p{1} + 1)] = 
             Some (sa0{1}, sc0{1})).
  + rcondt{1}1;2:rcondt{2}1;auto;progress.
    + cut->:take (i1{m} + 1) (format bl{m} (i{m} + 1)) = 
            take (i1{m} + 1) (format bl{m} i{m});2:smt(all_prefixes_of_INV_real).
      smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
    + cut->:take (i1{hr} + 1) (format bl{hr} (i{hr} + 1)) = 
            take (i1{hr} + 1) (format bl{hr} i{hr});2:smt(all_prefixes_of_INV_real).
      smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
    + smt().    
    + smt(size_cat size_nseq).
    + rewrite get_oget;2:smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
      cut->:format bl{2} (i1{2} + 1 - size bl{2} + 1) = 
            take (i1{2} + 1) (format bl{2} i{2})
        by smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
      smt(all_prefixes_of_INV_real).
  conseq(:_==> ={nb,bl,n,p,p1,i,i1,lres,sa0,sc0,C.c,glob Redo,glob Perm}
        /\ INV_Real SLCommon.C.c{1} (C.c{1} + size bl{2} + i{1} - 1)
             Perm.m{1} Perm.mi{1} Redo.prefixes{1}
        /\ pmi{1} = Perm.mi{1} /\ pm{1} = Perm.m{1}
        /\ pref{1} = Redo.prefixes{1} /\ SLCommon.C.c{1} = count{1}
        /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p1{1} = format p{1} (i{1}+1)
        /\ (format p{1} i{1} \in dom Redo.prefixes{1})
        /\ i1{1} = size p{1} /\ valid p{1}
        /\ Redo.prefixes{1}.[take i1{1} p{1}] = Some (sa0{1}, sc0{1}));
    1:smt(size_cat size_nseq nseq0 cats0 take_size).
  while(={nb,bl,n,p,p1,i,i1,lres,sa0,sc0,C.c,glob Redo,glob Perm}
        /\ INV_Real SLCommon.C.c{1} (C.c{1} + size bl{2} + i{1} - 1)
             Perm.m{1} Perm.mi{1} Redo.prefixes{1}
        /\ pmi{1} = Perm.mi{1} /\ pm{1} = Perm.m{1}
        /\ pref{1} = Redo.prefixes{1} /\ SLCommon.C.c{1} = count{1}
        /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p1{1} = format p{1} (i{1}+1)
        /\ (format p{1} i{1} \in dom Redo.prefixes{1})
        /\ 0 <= i1{1} <= size p{1} /\ valid p{1}
        /\ Redo.prefixes{1}.[take i1{1} p{1}] = Some (sa0{1}, sc0{1}));last first.
  + auto;progress.
    - smt().
    - cut[]_[]:=H;smt(in_dom).
    - exact size_ge0.
    - cut[]_[]:=H;smt(in_dom take0).
    - smt(size_cat size_nseq).
  rcondt{1}1;2:rcondt{2}1;auto;progress.
  - cut->:take (i1{m} + 1) (format bl{m} (i{m} + 1)) = 
          take (i1{m} + 1) (format bl{m} i{m});2:smt(all_prefixes_of_INV_real).
    smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
  - cut->:take (i1{hr} + 1) (format bl{hr} (i{hr} + 1)) = 
          take (i1{hr} + 1) (format bl{hr} i{hr});2:smt(all_prefixes_of_INV_real).
    smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
  - smt().
  - smt().
  - cut->:take (i1{2} + 1) (format bl{2} (i{2} + 1)) = 
          take (i1{2} + 1) (format bl{2} i{2}) 
      by smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
    cut->:take (i1{2} + 1) bl{2} = 
          take (i1{2} + 1) (format bl{2} i{2})
      by smt(take_cat take_le0 cats0).
    rewrite get_oget//=;smt(all_prefixes_of_INV_real).
  qed.


  local lemma lemma4 c c' m mi p bl i sa sc:
      INV_Real c c' m mi p =>
      0 < i =>
      p.[format bl i] = Some (sa,sc) =>
      format bl (i+1) \in dom p =>
      p.[format bl (i+1)] = m.[(sa,sc)].
  proof.
  move=>inv0 H_i0 H_p_i H_dom_iS.
  cut[]_[]_ hmp1 _ :=inv0.
  cut:=hmp1 (format bl (i+1)) H_dom_iS=>help. 
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
  rewrite H_p_i=>[]/=[][]->>->>. 
  by rewrite Block.WRing.addr0=>H_pm;rewrite H_pm/=. 
  qed.

  local lemma lemma3 c1 c2 m mi p bl b (sa:block) sc:
      INV_Real c1 c2 m mi p =>
      (sa +^ b,sc) \in dom m =>
      ! rcons bl b \in dom p =>
      p.[bl] = Some (sa,sc) =>
      INV_Real c1 c2 m mi p.[rcons bl b <- oget m.[(sa +^ b,sc)]].
  proof.
  move=>inv0 H_dom_m H_dom_p H_p_val.
  split;cut[]//=_[] hmp0 hmp1 hinvm:=inv0;split=>//=.
  + by rewrite getP;smt(size_cat size_nseq size_ge0).
  + move=>l;rewrite dom_set in_fsetU1;case;1:smt(all_prefixes_of_INV_real getP).
    move=>->>j[]hj0 hjsize;rewrite getP/=.
    cut:=hmp1 bl;rewrite in_dom H_p_val/==>help.
    cut->/=:!take j (rcons bl b) = rcons bl b by smt(size_take).
    move:hjsize;rewrite size_rcons=>hjsize.
    rewrite-cats1 !take_cat.
    pose x := if _ then _ else _;cut->/={x}: x = take j bl by smt(take_le0 cats0 take_size).
    rewrite nth_cat.
    case(j < size bl)=>//=hj;last first.
    + cut->>/=:j = size bl by smt().
      by rewrite take_size H_p_val/=;exists sa sc=>//=;smt(getP get_oget).
    cut->/=:j + 1 - size bl <= 0 by smt().
    rewrite cats0.
    pose x := if _ then _ else _;cut->/={x}: x = take (j+1) bl by smt(take_le0 cats0 take_size).
    cut:=hmp1 bl;rewrite in_dom H_p_val/==>hep.
    cut:=hep j _;rewrite//=;smt(getP size_cat size_take).
  qed.



  local lemma squeeze_squeezeless (D <: DISTINGUISHER {P, Redo, C, SLCommon.C}) :
    equiv [ NIndif(Squeeze(SqueezelessSponge(P)),P,DRestr(D)).main
        ~ RealIndif(Sponge,P,DRestr(D)).main
        : ={glob D} ==> ={res, glob P, glob D, C.c} /\ C.c{1} <= max_size].
  proof.
  proc;inline*;sp;wp. 
  call(: ={glob Perm,C.c} /\ C.c{1} <= max_size
      /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1});auto;last first.
  + progress.
    + exact max_ge0.
    split=>//=;1:split=>//=;smt(getP dom0 map0P in_fset0 dom_set in_fsetU1). 
  + proc;inline*;auto;sp;if;auto;sp;if;auto;progress.
    - by rewrite INV_Real_addm_mi;2..:smt(supp_dexcepted);split;case:H0=>//=;smt().
    - by split;case:H0=>//=;smt().
  + proc;inline*;auto;sp;if;auto;sp;if;auto;progress.
    - rewrite INV_Real_addm_mi;1: by split;case:H0=>//=;smt().
      * case:H0;smt(invm_dom_rng invmC supp_dexcepted).
      case:H0;smt(invm_dom_rng invmC supp_dexcepted).
    - by split;case:H0=>//=;smt(). 
  proc;inline*;sp;auto;if;auto;sp;if;auto;
    last by progress;split;case:H0=>//=;smt(size_ge0).
  conseq(: (exists (c_R : int),
      C.c{2} = c_R + size bl{2} + max (nb{2} - 1) 0 /\ xs{2} = bl{2} /\
      n{2} = nb{2} /\ z0{2} = [] /\ sc{2} = c0 /\ sa{2} = b0 /\ i{2} = 0 /\
      exists (c_L : int), C.c{1} = c_L + size bl{1} + max (nb{1} - 1) 0 /\
      p{1} = bl{1} /\ n{1} = nb{1} /\ lres{1} = [] /\ b{1} = b0 /\
      i{1} = 0 /\ z{2} = [] /\ z{1} = [] /\ ={bl, nb} /\
      ={Perm.mi, Perm.m} /\ c_L = c_R /\
      INV_Real 0 c_L Perm.m{1} Perm.mi{1} Redo.prefixes{1} /\ valid p{1})
    ==> lres{1} = z0{2} /\ ={Perm.mi, Perm.m} /\ ={C.c} /\
      INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1});1,2:smt().
  sp.
  seq 2 1 : (={glob P, i, n, C.c,sa,sc}
    /\ b{1} = sa{2} /\ Redo.prefixes.[p]{1} = Some (sa,sc){2}
    /\ lres{1} = z0{2} /\ i{1} = 0 /\ valid p{1}
    /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1}).
  + conseq(:_==> ={glob P, n, C.c,sa,sc} /\ b{1} = sa{2} /\ i0{1} = size p0{1}
        /\ Redo.prefixes{1}.[take i0{1} p0{1}] = Some (sa{1}, sc{1})
        /\ lres{1} = z0{2} /\ xs{2} = drop i0{1} p0{1}
        /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1});1:smt(take_size drop_size).
    wp;while(={glob P, n, C.c,sa,sc} /\ sa{1} = sa{2} /\ sc{1} = sc{2}
        /\ 0 <= i0{1} <= size p0{1} 
        /\ Redo.prefixes{1}.[take i0{1} p0{1}] = Some (sa{1}, sc{1})
        /\ lres{1} = z0{2} /\ xs{2} = drop i0{1} p0{1}
        /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1}).
    + if{1};auto.
      + sp;rcondf{2}1;auto;progress.
        + rewrite head_nth nth_drop//=.
          cut[]_[]_ hmp1 _ :=H2;cut:=hmp1 _ H5 i0{m} _;1:smt(size_take).
          move=>[]b3 c3;rewrite!take_take!nth_take 1,2:/# !min_lel//= 1:/#.
          rewrite H1=>//=[][][]->>->>.
          by rewrite nth_onth (onth_nth b0)//=;smt(in_dom).
        + rewrite head_nth nth_drop//=.
          cut[]_[]_ hmp1 _ :=H2;cut:=hmp1 _ H5 i0{1} _;1:smt(size_take).
          move=>[]b3 c3;rewrite!take_take!nth_take 1,2:/# !min_lel//= 1:/#.
          rewrite H1=>//=[][][]->>->>.
          by rewrite nth_onth (onth_nth b0)//=;smt(in_dom).
        + rewrite head_nth nth_drop//=.
          cut[]_[]_ hmp1 _ :=H2;cut:=hmp1 _ H5 i0{1} _;1:smt(size_take).
          move=>[]b3 c3;rewrite!take_take!nth_take 1,2:/# !min_lel//= 1:/#.
          rewrite H1=>//=[][][]->>->>.
          by rewrite nth_onth (onth_nth b0)//=;smt(in_dom).
        + rewrite head_nth nth_drop//=.
          cut[]_[]_ hmp1 _ :=H2;cut:=hmp1 _ H5 i0{1} _;1:smt(size_take).
          move=>[]b3 c3;rewrite!take_take!nth_take 1,2:/# !min_lel//= 1:/#.
          rewrite H1=>//=[][][]->>->>.
          by rewrite nth_onth (onth_nth b0)//=;smt(in_dom).
        + rewrite head_nth nth_drop//=.
          cut[]_[]_ hmp1 _ :=H2;cut:=hmp1 _ H5 i0{1} _;1:smt(size_take).
          move=>[]b3 c3;rewrite!take_take!nth_take 1,2:/# !min_lel//= 1:/#.
          rewrite H1=>//=[][][]->>->>.
          by rewrite nth_onth (onth_nth b0)//=;smt(in_dom).
        + smt().
        + smt().
        + smt(get_oget).
        + smt(behead_drop drop_add).
        + smt(size_drop size_eq0).
        + smt(size_drop size_eq0).
      sp=>//=. 
      if;auto;progress.
      + by rewrite head_nth nth_drop //=nth_onth (onth_nth witness)//=.
      + by move:H6;rewrite head_nth nth_drop //=nth_onth (onth_nth witness)//=.
      + by rewrite head_nth nth_drop //=nth_onth (onth_nth b0)//=. 
      + by rewrite head_nth nth_drop //=nth_onth (onth_nth b0)//=. 
      + by rewrite head_nth nth_drop //=nth_onth (onth_nth b0)//=. 
      + by rewrite head_nth nth_drop //=nth_onth (onth_nth b0)//=. 
      + by rewrite head_nth nth_drop //=nth_onth (onth_nth b0)//=. 
      + by rewrite head_nth nth_drop //=nth_onth (onth_nth b0)//=. 
      + smt().
      + smt().
      + by rewrite getP/=.
      + by rewrite behead_drop drop_add. 
      + rewrite!getP/=oget_some.
        cut:=lemma3 0 C.c{2}Perm.m{2}.[(sa{2} +^ nth witness p0{1} i0{1}, sc{2}) <- yL]
          Perm.mi{2}.[yL <- (sa{2} +^ nth witness p0{1} i0{1}, sc{2})] Redo.prefixes{1}
          (take i0{1} p0{1}) (nth witness p0{1} i0{1}) sa{2} sc{2}.
        rewrite!dom_set!in_fsetU1/=-take_nth//=H5/=H1/=getP/=oget_some.
        cut->->//=:(yL.`1, yL.`2) = yL by smt().
        rewrite INV_Real_addm_mi=>//=;smt(supp_dexcepted).
      + smt(size_drop size_eq0).
      + smt(size_drop size_eq0).
      + by rewrite head_nth nth_drop //=nth_onth (onth_nth b0)//=. 
      + by rewrite head_nth nth_drop //=nth_onth (onth_nth b0)//=. 
      + by rewrite head_nth nth_drop //=nth_onth (onth_nth b0)//=. 
      + by rewrite head_nth nth_drop //=nth_onth (onth_nth b0)//=. 
      + smt().
      + smt().
      + by rewrite getP.
      + by rewrite behead_drop drop_add.
      + rewrite(take_nth witness)//=. 
        cut:=lemma3 0 C.c{2} Perm.m{2} Perm.mi{2} Redo.prefixes{1}
          (take i0{1} p0{1}) (nth witness p0{1} i0{1}) sa{2} sc{2}.
        by rewrite-take_nth//= H5/=H1/=H2/=H6/=;smt().
      + smt(size_drop size_eq0).
      + smt(size_drop size_eq0).
    auto;progress.
    + exact size_ge0.
    + by rewrite take0;cut[]_[]->:=H.
    + by rewrite drop0.
    + split;case:H=>//=;smt(size_ge0).
    + smt(size_ge0 size_eq0).
    + smt(size_ge0 size_eq0).
    + smt().
  case(0 < n{1});last by rcondf{1}1;2:rcondf{2}1;auto;progress.
  splitwhile{1} 1 : i + 1 < n;splitwhile{2} 1 : i + 1 < n.
  rcondt{1}2;2:rcondt{2}2;auto;progress.
  + by while(i<n);auto;sp;if;auto;sp;while(i<n);auto;if;auto;sp;if;auto.
  + by while(i<n);auto;sp;if;auto;sp;if;auto.
  rcondf{1}4;2:rcondf{2}4;auto;progress.
  + by while(i<n);auto;2:smt();sp;if;auto;sp;while(i<n);auto;if;auto;sp;if;auto.
  + by while(i<n);auto;2:smt();sp;if;auto;sp;if;auto.
  rcondf{1}4;2:rcondf{2}4;auto;progress.
  + by while(i<n);auto;2:smt();sp;if;auto;sp;while(i<n);auto;if;auto;sp;if;auto.
  + by while(i<n);auto;2:smt();sp;if;auto;sp;if;auto.
  conseq(:_==> ={i,n,glob P,C.c} /\ lres{1} = z0{2} /\ b{1} = sa{2}
      /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1}
      /\ Redo.prefixes{1}.[format p{1} (i{1}+1)] = Some (sa,sc){2});progress.
  while(={i,n,glob P,C.c} /\ lres{1} = z0{2} /\ b{1} = sa{2} /\ 0 <= i{1} < n{1}
      /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1} /\ valid p{1}
      /\ Redo.prefixes{1}.[format p{1} (i{1}+1)] = Some (sa,sc){2});last first.
  + auto;1:smt(nseq0 cats0).
  sp;if;auto;sp.
  splitwhile{1}1: i1 < size p1 - 1.
  rcondt{1}2;2:rcondf{1}4;1,2:auto.
  + while(i1 < size p1);auto;2:smt(size_cat size_nseq size_ge0 size_eq0 valid_spec).
    by if;auto;1:smt();sp;if;auto;progress;smt().
  + seq 1 : (i1 = size p1 - 1).
    - while(i1 < size p1);auto;2:smt(size_cat size_nseq size_ge0 size_eq0 valid_spec).
      by if;auto;1:smt();sp;if;auto;progress;smt().
    by if;auto;1:smt();sp;if;auto;smt().
  seq 1 0 : (={i,n,glob P,C.c} /\ x0{2} = (sa{2}, sc{2}) /\ 0 < i{1} < n{1}
          /\ p1{1} = format p{1} (i{1} + 1) /\ (sa0,sc0){1} = x0{2}
          /\ i1{1} = size p{1} + i{1} - 1 /\ lres{1} = z0{2} /\ valid p{1}
          /\ Redo.prefixes{1}.[format p{1} i{1}] = Some (sa{2}, sc{2})
          /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1}
          /\ valid p{1});last first.
  + if{1};auto.
    + rcondf{2}1;auto;progress.
      + move:H5;rewrite take_oversize;1:rewrite size_cat size_nseq max_ler/#.
        move=>H_dom;rewrite in_dom. 
        by cut<-:=lemma4 _ _ _ _ _ _ _ _ _ H3 H H2 H_dom;rewrite-in_dom.
      + move:H5;rewrite take_oversize;1:rewrite size_cat size_nseq max_ler/#;move=>H_dom.
        by cut:=lemma4 _ _ _ _ _ _ _ _ _ H3 H H2 H_dom;smt(in_dom).
      + smt().
      + move:H5;rewrite take_oversize;1:rewrite size_cat size_nseq max_ler/#;move=>H_dom.
        by cut:=lemma4 _ _ _ _ _ _ _ _ _ H3 H H2 H_dom;smt(in_dom).
    sp;if;auto;progress.
    + move:H6;rewrite nth_cat nth_nseq;1:smt(size_ge0).
      cut->/=:!size p{1} + i{2} - 1 < size p{1} by smt().
      by rewrite Block.WRing.addr0.
    + move:H6;rewrite nth_cat nth_nseq;1:smt(size_ge0).
      cut->/=:!size p{1} + i{2} - 1 < size p{1} by smt().
      by rewrite Block.WRing.addr0.
    + move:H6;rewrite nth_cat nth_nseq;1:smt(size_ge0).
      cut->/=:!size p{1} + i{2} - 1 < size p{1} by smt().
      by rewrite Block.WRing.addr0.
    + move:H6;rewrite nth_cat nth_nseq;1:smt(size_ge0).
      cut->/=:!size p{1} + i{2} - 1 < size p{1} by smt().
      by rewrite Block.WRing.addr0.
    + move:H6;rewrite nth_cat nth_nseq;1:smt(size_ge0).
      cut->/=:!size p{1} + i{2} - 1 < size p{1} by smt().
      by rewrite Block.WRing.addr0.
    + smt().
    + move:H5 H6;rewrite nth_cat nth_nseq;1:smt(size_ge0).
      cut->/=:!size p{1} + i{2} - 1 < size p{1} by smt().
      rewrite Block.WRing.addr0 !getP/=oget_some take_oversize;1:rewrite size_cat size_nseq/#.
      move=>H_dom_iS H_dom_p.
      cut:=lemma2 0 C.c{2} Perm.m{2}.[(sa{2}, sc{2}) <- y0L]
          Perm.mi{2}.[y0L <- (sa{2}, sc{2})] Redo.prefixes{1}
          p{1} (i{2}+1) sa{2} sc{2} _ _ H4 _ H_dom_iS.
      + by rewrite INV_Real_addm_mi//=;smt(supp_dexcepted).
      + smt().
      + by rewrite dom_set in_fsetU1.
      by rewrite!getP/=oget_some-(addzA)/=H2/=;smt().
    + by rewrite!getP/=take_oversize//=size_cat size_nseq/#.
    + rewrite nth_cat;cut->/=:! size p{1} + i{2} - 1 < size p{1} by smt().
      by rewrite nth_nseq//=1:/# Block.WRing.addr0.
    + smt().
    + move:H5 H6;rewrite take_oversize 1:size_cat 1:size_nseq 1:/#.
      rewrite nth_cat;cut->/=:! size p{1} + i{2} - 1 < size p{1} by smt().
      rewrite nth_nseq//=1:/# Block.WRing.addr0 =>h1 h2.
      by cut:=lemma2 0 C.c{2} Perm.m{2} Perm.mi{2} Redo.prefixes{1}
          p{1} (i{2}+1) sa{2} sc{2} H3 _ H1 h2 h1;smt().
    + move:H5 H6;rewrite take_oversize 1:size_cat 1:size_nseq 1:/#.
      rewrite nth_cat;cut->/=:! size p{1} + i{2} - 1 < size p{1} by smt().
      by rewrite nth_nseq//=1:/# Block.WRing.addr0 !getP//=. 
  alias{1} 1 pref = Redo.prefixes;sp.
  conseq(:_==> ={glob P}
        /\ p1{1} = format p{1} (i{1} + 1) /\ pref{1} = Redo.prefixes{1}
        /\ i1{1} = size p1{1} - 1 
        /\ Redo.prefixes{1}.[take i1{1} p1{1}] = Some (sa0{1}, sc0{1})
        /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1});progress.
  + smt().
  + move:H9;rewrite take_format/=1:/#;1:smt(size_ge0 size_cat size_nseq).
    pose x := if _ then _ else _ ;cut->/={x}: x = format p{1} (i_R+1).
    + rewrite/x size_cat size_nseq-(addzA _ 1 (-1))/=!max_ler 1:/#-(addzA _ _ (-1))-(addzA _ _ (-1))/=.
      case(size p{1} + i_R <= size p{1})=>//=h;2:smt(size_ge0 size_cat size_nseq).
      cut->>/=:i_R = 0 by smt().
      by rewrite take_size/format nseq0 cats0.
    by rewrite H3/==>[][]->>->>.
  + move:H9;rewrite take_format/=1:/#;1:smt(size_ge0 size_cat size_nseq).
    pose x := if _ then _ else _ ;cut->/={x}: x = format p{1} (i_R+1).
    + rewrite/x size_cat size_nseq-(addzA _ 1 (-1))/=!max_ler 1:/#-(addzA _ _ (-1))-(addzA _ _ (-1))/=.
      case(size p{1} + i_R <= size p{1})=>//=h;2:smt(size_ge0 size_cat size_nseq).
      cut->>/=:i_R = 0 by smt().
      by rewrite take_size/format nseq0 cats0.
    by rewrite H3/=.
  + by rewrite size_cat size_nseq;smt().
  while{1}(={glob P} /\ 0 <= i1{1} <= size p1{1} - 1 /\ 0 < i{1} < n{1}
        /\ p1{1} = format p{1} (i{1} + 1) /\ pref{1} = Redo.prefixes{1}
        /\ format p{1} i{1} \in dom pref{1}
        /\ Redo.prefixes{1}.[take i1{1} p1{1}] = Some (sa0{1}, sc0{1})
        /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1})
    (size p1{1}-i1{1}-1);auto;last first.
  + progress.
    + smt(size_cat size_nseq size_ge0 size_eq0 valid_spec).
    + smt().
    + by rewrite in_dom H3.
    + by rewrite take0;cut[]_[]:=H1.
    + smt().
    + smt().
  rcondt 1;auto;progress.
  + cut->:take (i1{hr} + 1) (format p{hr} (i{hr} + 1)) =
          take (i1{hr} + 1) (format p{hr} i{hr});2:smt(all_prefixes_of_INV_real in_dom).
    rewrite!take_format;smt(valid_spec size_ge0 size_eq0 size_cat size_nseq).
  + smt().
  + smt(valid_spec size_ge0 size_eq0 size_cat size_nseq).
  + cut->:take (i1{hr} + 1) (format p{hr} (i{hr} + 1)) =
          take (i1{hr} + 1) (format p{hr} i{hr});2:smt(all_prefixes_of_INV_real in_dom).
    rewrite!take_format;smt(valid_spec size_ge0 size_eq0 size_cat size_nseq).
  smt().
  qed. 



  local lemma pr_real (D <: DISTINGUISHER{SLCommon.C, C, Perm, Redo}) &m :
      Pr [ GReal(A(D)).main() @ &m : res /\ SLCommon.C.c <= max_size] =
      Pr [ RealIndif(Sponge,P,DRestr(D)).main() @ &m : res].
  proof.
  cut->:Pr [ RealIndif(Sponge, P, DRestr(D)).main() @ &m : res ] =
        Pr [ NIndif(Squeeze(SqueezelessSponge(P)),P,DRestr(D)).main() @ &m : res /\ C.c <= max_size ].
  + by rewrite eq_sym;byequiv (squeeze_squeezeless D)=>//=.
  byequiv (equiv_sponge D)=>//=;progress;smt().
  qed.


  declare module D : DISTINGUISHER{SLCommon.C, C, Perm, Redo, F.RO, F.RRO, S, BIRO.IRO}.

  axiom D_lossless (F0 <: DFUNCTIONALITY{D}) (P0 <: DPRIMITIVE{D}) :
    islossless P0.f => islossless P0.fi => islossless F0.f => 
    islossless D(F0, P0).distinguish.


  lemma A_lossless (F <: SLCommon.DFUNCTIONALITY{A(D)})
                   (P0 <: SLCommon.DPRIMITIVE{A(D)}) :
      islossless P0.f =>
      islossless P0.fi => islossless F.f => islossless A(D, F, P0).distinguish.
  proof.
  progress;proc;inline*;sp;wp.
  call(:true);auto.
  + exact D_lossless.
  + proc;inline*;sp;if;auto;call H;auto.
  + proc;inline*;sp;if;auto;call H0;auto.
  proc;inline*;sp;if;auto;sp;if;auto.
  while(true)(n-i);auto.
  + by sp;if;auto;1:call H1;auto;smt().
  call H1;auto;smt().
  qed.

  (* REAL & IDEAL *)

  lemma concl &m :
      Pr [ RealIndif(Sponge,P,DRestr(D)).main() @ &m : res ] <=
      Pr [ IdealIndif(Squeeze(IF), SimLast(S), DRestr(D)).main() @ &m : res ] +
      (max_size ^ 2)%r / 2%r * mu dstate (pred1 witness) + 
      max_size%r * ((2*max_size)%r / (2^c)%r) + 
      max_size%r * ((2*max_size)%r / (2^c)%r).
  proof.
  rewrite-(pr_real D &m).
  rewrite-(equiv_ideal' D &m). 
  apply(Real_Ideal (A(D)) A_lossless &m).
  qed.

end section Real_Ideal.