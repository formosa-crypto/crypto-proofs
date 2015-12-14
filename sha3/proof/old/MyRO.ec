require import Option List FSet NewFMap.
        import NewLogic.

abstract theory Titer.

type t.  

module type Orcl = {
  proc f (x:t) : unit
}.

module Iter (O:Orcl) = {
  proc iter(l:t list) = {
    while (l <> []) { 
      O.f(head witness l);
      l <- drop 1 l;
    }
  }
}.

section.

declare module O:Orcl.

axiom iter_swap1 i1 i2:  
  equiv [Iter(O).iter ~ Iter(O).iter :
         l{1} = [i1;i2] /\ l{2} = [i2;i1] /\ ={glob O} ==> ={glob O}].

lemma iter_swap s1 i s2:
  equiv [Iter(O).iter ~ Iter(O).iter :
         l{1} = i::s1++s2 /\ l{2} = s1++i::s2 /\ ={glob O} ==> ={glob O}].
proof.
  elim:s1=> /=[|i' s1 Hrec];1:by sim.
  transitivity Iter(O).iter 
    (l{1}= i :: i' :: (s1 ++ s2) /\ l{2} = i' :: i :: (s1 ++ s2) /\ ={glob O} ==>
     ={glob O})
    (l{1}= i' :: i :: (s1 ++ s2) /\ l{2} = i' :: (s1 ++ i::s2) /\ ={glob O} ==>
     ={glob O})=>//.
  + by move=> ?&ml[*]<*>;exists (glob O){ml}, (i' :: i :: (s1 ++ s2)).
  + proc;rcondt{1}1=>//;rcondt{2}1=>//.
    rcondt{1}3;1:by auto;conseq(_: true).
    rcondt{2}3;1:by auto;conseq(_: true).
    seq 4 4 : (={l,glob O});last by sim.
    transitivity{1} {Iter(O).iter([i;i']); l <- drop 2 l;} 
      (l{1} = i :: i' :: (s1 ++ s2) /\ ={l, glob O} ==> ={l,glob O})
      (l{1} = i :: i' :: (s1 ++ s2) /\ 
       l{2} = i' :: i :: (s1 ++ s2) /\  ={glob O} ==> ={l,glob O})=>//.
    + by move=>?&ml[*]<*>;exists (glob O){ml}, (i :: i' :: (s1 ++ s2)).
    + inline *;rcondt{2} 2;1:by auto. 
      rcondt{2} 4;1:by auto;sp;conseq(_:true).
      rcondf{2} 6; auto;call(_:true);wp;call(_:true);auto.
    transitivity{1} {Iter(O).iter([i';i]); l <- drop 2 l;} 
      (l{1} = i :: i' :: (s1 ++ s2) /\ 
       l{2} = i' :: i :: (s1 ++ s2) /\  ={glob O} ==> ={l,glob O})
      (l{2} = i' :: i :: (s1 ++ s2) /\ ={l, glob O} ==> ={l,glob O})=>//.
    + by move=>?&ml[*]<*>;exists (glob O){ml}, (i' :: i :: (s1 ++ s2)).
    + wp; by call (iter_swap1 i i').
      (* call iter_swap1: FIXME catch exception *)
    inline *;rcondt{1} 2;1:by auto. 
    rcondt{1} 4;1:by auto;sp;conseq(_:true).
    rcondf{1} 6; auto;call(_:true);wp;call(_:true);auto.
  proc;rcondt{1}1=>//;rcondt{2}1=>//.
  seq 2 2 : (l{1} = i :: (s1 ++ s2) /\ l{2} = s1 ++ i :: s2 /\ ={glob O}).
  + by wp;call(_:true);auto;progress;rewrite drop0.
  transitivity{1} {Iter(O).iter(l); }
   (={l,glob O} /\ l{1}= i::(s1++s2) ==> ={glob O})
   (={glob O} /\ l{1}=i::(s1++s2) /\ l{2}= (s1++i::s2) ==> ={glob O})=>//.
  + by move=>?&ml[*]<*>;exists (glob O){ml}, (i :: (s1 ++ s2)).
  + by inline *;sim.    
  transitivity{1} {Iter(O).iter(l); }
   (={glob O} /\ l{1}=i::(s1++s2) /\ l{2}= (s1++i::s2) ==> ={glob O})
   (={l,glob O} /\ l{2}= (s1++i::s2) ==> ={glob O})=>//.
  + by move=>?&ml[*]<*>;exists (glob O){ml}, (s1 ++ i::s2).
  + by call Hrec;auto.
  by inline*;sim.         
qed.

lemma iter_perm : 
   equiv [Iter(O).iter ~ Iter(O).iter : perm_eq l{1} l{2} /\ ={glob O} ==> ={glob O}].
proof.
  exists*l{1},l{2};elim*=>l1 l2;case (perm_eq l1 l2)=> Hp;last first.
  + conseq (_:false==>_)=>// ??[*]//. 
  elim: l1 l2 Hp=> [|i s1 ih] s2 eq_s12 /=.
  + have ->: s2 = [] by apply/perm_eq_small/perm_eq_sym.
    proc;rcondf{1} 1=>//;rcondf{2} 1=>//.
  have/perm_eq_mem/(_ i) := eq_s12; rewrite mem_head /=.
  move/splitPr => [s3 s4] ->>.
  transitivity Iter(O).iter 
    (l{1}=i::s1 /\ l{2}=i::(s3++s4) /\ ={glob O} ==> ={glob O})
    (l{1}=i::(s3++s4) /\ l{2}=s3++i::s4 /\ ={glob O} ==> ={glob O})=>//.
  + by move=>?&ml[*]-> -> _ ->; exists (glob O){ml}, (i :: (s3 ++ s4)).
  + proc;rcondt{1}1=>//;rcondt{2}1=>//.
    seq 2 2: (s1 = l{1} /\ l{2}=s3++s4 /\ ={glob O}).
    + by wp;call(_:true);auto;progress;rewrite drop0.
    transitivity{1} {Iter(O).iter(l); }
      (={l,glob O} ==> ={glob O}) 
      (s1 = l{1} /\ l{2} = s3 ++ s4 /\ ={glob O} ==> ={glob O})=>//.
    + by move=>?&ml[*]-> -> ->;exists (glob O){ml}, l{1}.
    + by inline Iter(O).iter;sim.
    transitivity{1} {Iter(O).iter(l); }
      (s1 = l{1} /\ l{2} = s3 ++ s4 /\ ={glob O} ==> ={glob O})
      (={l,glob O} ==> ={glob O}) =>//.
    + by move=>?&ml[*]-> -> ->;exists (glob O){ml}, (s3++s4).
    + move: eq_s12; rewrite -(cat1s i s4) catA perm_eq_sym.
      rewrite perm_catCA /= perm_cons perm_eq_sym=> Hp.
    + call (ih (s3++s4) Hp)=>//.
    by inline Iter(O).iter;sim.
  by apply (iter_swap s3 i s4). (* FIXME: apply iter_swap fail! *)
qed.

end section.

end Titer.

type flag = [ Unknown | Known ].

abstract theory Ideal.

type from, to.

op sampleto : from -> to distr.

module type RO = {
  proc init  ()                  : unit
  proc get   (x : from)          : to
  proc set   (x : from, y : to)  : unit
  proc sample(x : from)          : unit
  proc in_dom(x : from,f : flag) : bool
  proc restrK()                  : (from,to)fmap
}.

module type Distinguisher(G : RO) = {
  proc distinguish(): bool 
}.

op in_dom_with (m:(from, to * flag)fmap) (x:from) (f:flag) = 
   mem (dom m) x /\ (oget (m.[x])).`2 = f.

op restr f (m:(from, to * flag)fmap) = 
  let m = filter (fun _ (p:to*flag) => p.`2=f) m in
  map (fun _ (p:to*flag) => p.`1) m.

lemma restrP m f x: 
  (restr f m).[x] = 
  obind (fun (p:to*flag)=>if p.`2=f then Some p.`1 else None) m.[x].
proof.
  rewrite /restr /= mapP filterP in_dom /=.
  by case (m.[x])=>//= -[x0 f'];rewrite oget_some /=;case (f' = f).
qed.

lemma restr_dom m f x: 
  mem (dom(restr f m)) x <=> (mem (dom m) x /\ (oget m.[x]).`2 = f).
proof. 
  rewrite !in_dom;case: (m.[x]) (restrP m f x)=>//= -[t f'] /=.
  by rewrite oget_some /=;case (f' = f)=> [_ ->|].
qed.

lemma restr_set_diff f2 f1 m x y: 
  !mem (dom m) x =>
  f2 <> f1 => restr f1 m.[x<-(y,f2)] = restr f1 m.
proof.
  rewrite fmapP in_dom=>/= Hdom Hf x';rewrite !restrP getP.
  by case (x' = x)=>//=->;rewrite Hf Hdom.
qed.

module RO : RO = {
  var m : (from, to * flag)fmap

  proc init () = { m <- map0; }

  proc get(x:from) = {
    var r;
    r <$ sampleto x;
    if (mem (dom m) x) r <- (oget m.[x]).`1;
    m.[x] <- (r,Known);
    return r;
  }

  proc set (x:from, y:to) = {
    m.[x] <- (y,Known);
  }

  proc sample(x:from) = {
    var c;
    c     <$ sampleto x;
    m.[x] <- (c,Unknown);
  }

  proc in_dom(x:from, f:flag) = {
    return in_dom_with m x f;
  }

  proc restrK() = {
    return restr Known m;
  }
}.

section LL. 

lemma init_ll : islossless RO.init.
proof. by proc;auto. qed.

lemma in_dom_ll : islossless RO.in_dom.
proof. by proc. qed.

lemma restrK_ll : islossless RO.restrK.
proof. by proc. qed.

lemma set_ll : islossless RO.set.
proof. by proc;auto. qed.

axiom sampleto_ll : forall x, Distr.weight (sampleto x) = 1%r.

lemma get_ll : islossless RO.get.
proof. by proc;auto;progress;apply sampleto_ll. qed.

lemma sample_ll : islossless RO.sample.
proof. by proc;auto;progress;apply sampleto_ll. qed.

end section LL.
 
end Ideal.

abstract theory GenEager.

clone include Ideal. 

axiom sampleto_ll : forall x, Distr.weight (sampleto x) = 1%r.

clone include Titer with type t <- from.

module ERO : RO = {

  proc init = RO.init

  proc get(x:from) = {
    var r;
    r <$ sampleto x;
    if (!mem (dom RO.m) x || (oget RO.m.[x]).`2 = Unknown) {
      RO.m.[x] <- (r,Known);
    }
    return (oget RO.m.[x]).`1;
  }

  proc set = RO.set 

  proc sample = RO.sample

  proc in_dom = RO.in_dom

  proc restrK = RO.restrK

  module I = {
    proc f = sample
  }

  proc resample () = {
    Iter(I).iter (elems (dom (restr Unknown RO.m)));
  }

}.

lemma set_eq (m:('a,'b)fmap) x y: m.[x] = Some y => m.[x<-y] = m.
proof.
  by rewrite fmapP=> Hx x';rewrite getP;case (x'=x)=>//->;rewrite Hx.
qed.

lemma eager_get :
  eager [ERO.resample(); , RO.get ~ ERO.get, ERO.resample(); :
         ={x,RO.m} ==> ={res,RO.m} ].
proof.
  eager proc.
  wp;case ((mem (dom RO.m) x /\ (oget RO.m.[x]).`2=Known){1}).
  + rnd{1};rcondf{2} 2;1:by auto=> /#.
    alias{1} 1 mx = oget RO.m.[x];inline *.
    while (={l,RO.m} /\ (!mem l x /\ RO.m.[x] = Some (mx.`1,Known)){1}).
    + auto=>?&ml[*]-> ->;case (l{ml})=>//=x2 l2 Hmx Hgx?->.
      by rewrite getP drop0 /#.
    auto=>??[*]-> ->/= Hmem HK;rewrite sampleto_ll/==> r _. 
    rewrite -memE restr_dom Hmem/= HK.
    rewrite {1}get_oget //= -HK;case:(oget _)HK=> x1?/=->.
    by move=>????-> _[*]_-> _ Heq?;rewrite in_dom set_eq Heq. 
  rcondt{2} 2. + auto=> ?[*]-> ->;rewrite negb_and /#.
  case ((mem (dom RO.m) x){1}).
  + inline{1} ERO.resample=>/=.
    transitivity{1} { Iter(ERO.I).iter(x::elems ((dom (restr Unknown RO.m)) `\` fset1 x));
                      r <$ sampleto x; }
      (={x,RO.m} /\ mem (dom RO.m{1}) x{1} /\ (oget RO.m{1}.[x{1}]).`2 = Unknown ==>
       ={x,RO.m})
      (={x,RO.m} /\ mem (dom RO.m{1}) x{1} /\ (oget RO.m{1}.[x{1}]).`2 = Unknown==>
       ={x} /\ eq_except RO.m{1} RO.m{2} (fset1 x{1}) /\
       RO.m{1}.[x{2}] = Some (result{2},Unknown) /\
       RO.m{2}.[x{2}] = Some (result{2},Known)).
    + by move=>?&ml[*]-> -> ??;exists RO.m{ml}, x{ml}=>/#.
    + move=>???;rewrite in_dom=>[*]<*>[*]->/eq_except_sym H Hxm Hx2.
      rewrite Hxm oget_some /=;apply /eq_sym.
      have /(congr1 oget):= Hx2 => <-;apply eq_except_set_eq=>//.
      by rewrite in_dom Hx2.
    + rnd;call (iter_perm ERO.I _).

  



      cut ->: (result{2}, Known) = oget RO.m{2}.[x{2}]. 
        

      search eq_except.
 set_eq.
 1:Hx.
;rewrite H=>{H}.    

 <- ((oget RO.m{1}.[x{1}]).`1, Known)] = RO.m{2}
     mem (dom RO.m{1} x{1}

    transitivity{1} { work <- dom RO.m;
                      r <$ sampleto x;
                      while (work <> fset0) {
                        x0  <- pick work;
                        if (in_dom_with RO.m x0 Unknown) {
                          c   <$ sampleto x0;
                          RO.m.[x0] <- (if x0 = x then r else c, Unknown);
                        }
                        work <- work `\` fset1 (pick work);
                      } }
      (={x,RO.m} ==> ={x,RO.m})
      (={x,RO.m} /\ (mem (dom RO.m) x /\ (oget RO.m.[x]).`2 = Unknown){1} ==>
       ={x} /\ RO.m{1} = RO.m{2}.[x{2}<-(result{2}, Unknown)] /\ 
       RO.m{2}.[x{2}] = Some(result{2}, Known)).
    + move=>?&mr[*]-> ->??;exists RO.m{mr},x{mr}=>/#.
    + move=>?&m?[2*]-> -> <- ->_. 
      by rewrite in_dom getP_eq oget_some set_set set_eq.
    + seq 1 1:(={work,x,RO.m});[by sim|symmetry]. 
      eager while (H:r<$sampleto x; ~ r<$sampleto x; : ={x} ==> ={r})=>//;1,3:by sim.
      swap{1}2-1;sp 1 1.
      if{2};[rcondt{1}2|rcondf{1}2];1,3,4:by auto.
      by rnd{2};wp;case ((x0 = x){1});[rnd{1}|];auto=>??[*]-> -> -> -> ->_ _ _->;
         rewrite sampleto_ll.
    alias{1} 1 cx = (oget RO.m.[x]).`1.
    while (={work,x,r} /\ mem (dom RO.m{1}) x{1} /\ (RO.m.[x]=Some(r,Known)){2}/\
               RO.m{1} = (RO.m.[x<-(if mem work x then cx{1} else r, Unknown)]){2}).
    + sp 1 1;case ((x0 = x){1}).
      + rcondt{1} 1. by auto;progress;rewrite getP_eq oget_some;case (mem _ _).
        rcondf{2} 1. by auto=> @/in_dom_with;progress;rewrite H0. 
        auto=> ??[*]_-> -> -> ->?-> ->?_<-/=;rewrite sampleto_ll=>c _.
        by rewrite dom_set !inE /= set_set.
      if=>//. auto;progress[-split]. by rewrite /in_dom_with dom_set getP !inE H3.
      + auto;progress [-split];split=>// _.
        by rewrite dom_set !inE H/= getP set_set (eq_sym x{2}) H3 H0.
      by auto;progress;rewrite !inE (eq_sym x{2}) H3.
    auto;progress [-split];rewrite H1 /=.
    rewrite dom_set fsetUC subset_fsetU_id /=.
    + by move=> x;rewrite inE.
    rewrite H getP_eq /= set_set /= set_eq. 
    + by rewrite {1}get_oget // -H0;case (oget _).
    by move=> ????-> ->/=[*];rewrite !inE oget_some. 
  inline *;swap{1} 3 -2.
  admit.
(*
  (* Admit *)
  while (={work,x,r} /\ (RO.m.[x]=None){1} /\ 
         RO.m{2} = RO.m{1}.[x{2}<-(r{2},Known)] /\
         !mem work{2} x{2}).
  + wp;sp 1 1;if. auto=> ??[*]-> -> -> Hex Hmem Heq Hx _ /= ?->/=.
    rewrite !inE Hmem !getP Heq /=.
    cut ^Hd->/=: x{2} <> pick work{2} by smt ml=0 w=mem_pick.
    by rewrite Hex set_set Hd.
  auto=>??/=[*]-> -> _ ^Hdom;rewrite in_dom=>/=Hnone?->;rewrite restr_set_diff//=.
  by rewrite Hnone /= restr_dom Hdom=>????-> ->[*];rewrite in_dom getP_eq. *)
qed.
 
search "_.[_<-_]".
    search 
  auto=> ??/=[*]-> -> _ Hmem/=?->/=;rewrite restr_set_diff //=.
  rewrite eq_except_sym set_eq_except restr_dom Hmem getP_eq=>????->_ [*].

  rewrite Hmem.

 get_eq.

  transitivity{2} {
  
=>-[->//|/#].


 {1}(get_oget m_R x{2}).
print get_oget.
search "_.[_]" "_.[_<-_]".
print restrK.


smt.
 H /=;smt. 
  case ((!mem work x){1}).
  + swap{1} 2 -1;while (={work,x} /\ eq_except RO.m{1} RO.m{2} (fset1 x{1}) /\ 
                         (!mem work x){1} /\ (RO.m.[x] = Some rd){2} /\ (!mem (dom RO.m) x){1}). 
    + inline *;auto;progress [-split].
      cut -> : mem (dom RO.m{2}) (pick work{2}) = mem (dom RO.m{1}) (pick work{2}) by rewrite !in_dom;smt.
      smt. 
    auto;progress [-split];rewrite !getP_eq;smt. 
  inline RO.f.
  transitivity{1} { rd <$ sample x;
                    while (work <> fset0) {
                      x0  <- pick work;
                      rd0 <$ sample x0;
                      if (!mem (dom RO.m) x0)
                        RO.m.[x0] <- if x0 = x then rd else rd0;
                      work <- work `\` fset1 (pick work);
                    } }
     (={x,work,RO.m} ==> ={x,RO.m})
     ((={x,work,RO.m} /\ mem work{1} x{1}) /\ ! mem (dom RO.m{2}) x{2} ==>
           ={x,RO.m} /\ (result = oget RO.m.[x]){2} /\ mem (dom RO.m{1}) x{1}) => //.
  + by move=> &1 &2 H; exists RO.m{2}, x{2}, work{2}; move: H.
  + transitivity{1} { while (work <> fset0) {
                        x0  <- pick work;
                        rd0 <$ sample x0;
                        if (!mem (dom RO.m) x0) RO.m.[x0] <- rd0;
                        work <- work `\` fset1 (pick work);
                      }
                      rd <$ sample x; }
        (={x,work,RO.m} ==> ={x,RO.m})
        (={x,work,RO.m} ==> ={x,RO.m})=> //.
    + by move=> &1 &2 H; exists RO.m{2}, x{2}, work{2}; move: H.
    + by sim; rnd{2}; sim : (={x,IND_Eager.H.m}); smt.
    symmetry; eager while (H: rd <$ sample x; ~ rd <$ sample x; : ={x} ==> ={rd})=> //; sim. 
    swap{2} 5 -4; swap [2..3] -1; case ((x = pick work){1}).
    + by wp; rnd{2}; rnd; rnd{1}; wp; skip; smt.
    by auto; smt.
  + while (={x, work} /\
           (!mem work x => mem (dom RO.m) x){1} /\
            RO.m.[x]{2} = Some rd{1} /\
            if (mem (dom RO.m) x){1} then ={RO.m}
            else eq_except RO.m{1} RO.m{2} (fset1 x{1})).
    + auto;progress; 1..9,12:smt.
      + case ((pick work = x){2})=> pick_x; last smt.
        subst x{2}; move: H7 H1; rewrite -neqF /eq_except=> -> /= eq_exc.
        by apply fmapP=> x0; case (pick work{2} = x0); smt.
    by auto; smt.
  by auto;progress [-split];rewrite H0 /= getP_eq;smt. 













  module IND_S(D:Distinguisher) = {
    proc main(): bool = {
      var b;
      RO.init();
      b <@ D(RO).distinguish();
      ERO.sample();
      return b;
    }  
  }.

  section EAGER.

    local lemma eager_query:
       eager [ERO.sample(); , RO.f ~ ERO.f, ERO.sample(); :
                 ={x,RO.m} ==> ={res,RO.m} ].
    proof.
      eager proc.
      inline ERO.sample;swap{2} 4 -3.
      seq 1 1: (={x,work,RO.m});first by sim.
      wp;case ((mem (dom RO.m) x){1}).
      + rnd{1}.
        alias{1} 1 mx = oget RO.m.[x].
        while (={work,RO.m} /\ (RO.m.[x] = Some mx){1}). 
        + by inline *;auto;progress;smt.
        auto;progress [- split]; rewrite sample_ll H /=;smt. 
      case ((!mem work x){1}).
      + swap{1} 2 -1;while (={work,x} /\ eq_except RO.m{1} RO.m{2} (fset1 x{1}) /\ 
                             (!mem work x){1} /\ (RO.m.[x] = Some rd){2} /\ (!mem (dom RO.m) x){1}). 
        + inline *;auto;progress [-split].
          cut -> : mem (dom RO.m{2}) (pick work{2}) = mem (dom RO.m{1}) (pick work{2}) by rewrite !in_dom;smt.
          smt. 
        auto;progress [-split];rewrite !getP_eq;smt. 
      inline RO.f.
      transitivity{1} { rd <$ sample x;
                        while (work <> fset0) {
                          x0  <- pick work;
                          rd0 <$ sample x0;
                          if (!mem (dom RO.m) x0)
                            RO.m.[x0] <- if x0 = x then rd else rd0;
                          work <- work `\` fset1 (pick work);
                        } }
         (={x,work,RO.m} ==> ={x,RO.m})
         ((={x,work,RO.m} /\ mem work{1} x{1}) /\ ! mem (dom RO.m{2}) x{2} ==>
               ={x,RO.m} /\ (result = oget RO.m.[x]){2} /\ mem (dom RO.m{1}) x{1}) => //.
      + by move=> &1 &2 H; exists RO.m{2}, x{2}, work{2}; move: H.
      + transitivity{1} { while (work <> fset0) {
                            x0  <- pick work;
                            rd0 <$ sample x0;
                            if (!mem (dom RO.m) x0) RO.m.[x0] <- rd0;
                            work <- work `\` fset1 (pick work);
                          }
                          rd <$ sample x; }
            (={x,work,RO.m} ==> ={x,RO.m})
            (={x,work,RO.m} ==> ={x,RO.m})=> //.
        + by move=> &1 &2 H; exists RO.m{2}, x{2}, work{2}; move: H.
        + by sim; rnd{2}; sim : (={x,IND_Eager.H.m}); smt.
        symmetry; eager while (H: rd <$ sample x; ~ rd <$ sample x; : ={x} ==> ={rd})=> //; sim. 
        swap{2} 5 -4; swap [2..3] -1; case ((x = pick work){1}).
        + by wp; rnd{2}; rnd; rnd{1}; wp; skip; smt.
        by auto; smt.
      + while (={x, work} /\
               (!mem work x => mem (dom RO.m) x){1} /\
                RO.m.[x]{2} = Some rd{1} /\
                if (mem (dom RO.m) x){1} then ={RO.m}
                else eq_except RO.m{1} RO.m{2} (fset1 x{1})).
        + auto;progress; 1..9,12:smt.
          + case ((pick work = x){2})=> pick_x; last smt.
            subst x{2}; move: H7 H1; rewrite -neqF /eq_except=> -> /= eq_exc.
            by apply fmapP=> x0; case (pick work{2} = x0); smt.
        by auto; smt.
      by auto;progress [-split];rewrite H0 /= getP_eq;smt. 
    qed.

    equiv Eager_S (D <: Distinguisher{RO}): IND_S(D).main ~ IND(ERO,D).main: ={glob D} ==> ={res,RO.m,glob D}.
    proof.
      proc; inline ERO.init RO.init.
      seq 1 1: (={glob D, RO.m});first by wp. 
      symmetry; eager (H: ERO.sample(); ~ ERO.sample();: ={RO.m} ==> ={RO.m}): 
            (={glob D, RO.m}) => //; first by sim.
      eager proc H (={RO.m}) => //; [by apply eager_query | by sim].
    qed.

    equiv Eager (D <: Distinguisher{RO}): IND(RO,D).main ~ IND(ERO,D).main: ={glob D} ==> ={res,glob D}.
    proof.
      transitivity IND_S(D).main
          (={glob D} ==> ={res,glob D})
          (={glob D} ==> ={res,RO.m,glob D}) => //.
      + by progress;exists (glob D){2}.
      + proc;inline{2} ERO.sample.
        while{2} true (card work{2}). 
        + move=> &m1 z;wp;call (f_ll sample_ll);auto;smt.
        conseq (_: _ ==> ={b,glob D}) => //;[smt | by sim].
      apply (Eager_S D).
    qed.

  end section EAGER.

end GenIdeal.















abstract theory 


module type SAMPLE = {
  proc sampleI(h:handle) : unit
  proc setD(h:handle, c:capacity) : unit
  proc get(h:handle) : capacity
  proc in_dom(h:handle,c:caller) : bool
  proc restrD() : (handle,capacity)fmap
}.

module type ADV_SAMPLEH(O:SAMPLE) = {
  proc main() : bool
}.



module Esample = {
  var handles : (handle, ccapacity)fmap

  proc sampleI(h:handle) = {
    var c;
    c           <$ cdistr;
    handles.[h] <- (c,I);
  }

  proc setD (h:handle, c:capacity) = {
    handles.[h] <- (c,D);
  }

  proc in_dom(h:handle, c:caller) = {
    return in_dom_with handles h c;
  }

  proc restrD() = {
    return (
      let m = NewFMap.filter (fun _ (p:ccapacity) => p.`2=D) handles in
      NewFMap.map (fun _ (p:ccapacity) => p.`1) m);
  }

  proc get(h:handle) = {
    var c;
    c <$ cdistr;
    if (!mem (dom handles) h || (oget handles.[h]).`2 = I) {
      handles.[h] <- (c,D);
    }
    return (oget (handles.[h])).`1;
  }

}.








type from, to.

module type RO = {
  proc init()     : unit
  proc f(x : from): to
}.

module type Distinguisher(G : RO) = {
  proc distinguish(): bool {G.f}
}.

module IND(G:RO, D:Distinguisher) = {
  proc main(): bool = {
    var b;

         G.init();
    b <@ D(G).distinguish();
    return b;
  }  
}.

abstract theory Ideal.

  op sample : from -> to distr.

  module RO = {
    var m : (from, to) fmap
  
    proc init() : unit = {
      m <- map0;
    }
  
    proc f(x : from) : to = {
      var rd;
      rd <$ sample x;
      if (! mem (dom m) x) m.[x] <- rd;
      return oget m.[x];
    }
  }.

  section LL. 

    axiom sample_ll : forall x, Distr.weight (sample x) = 1%r.

    lemma f_ll : phoare[RO.f : true ==> true] = 1%r. 
    proof. proc;auto;progress;apply sample_ll. qed.
  
  end section LL.
 
end Ideal.


abstract theory GenIdeal.

  clone include Ideal. 
  axiom sample_ll : forall x, Distr.weight (sample x) = 1%r.

  op RO_dom : from fset.

  module ERO = {
    proc sample() = {
      var work;
      work <- RO_dom;
      while (work <> fset0) {
        RO.f(pick work);
        work = work `\` fset1 (pick work);
      }
    }

    proc init() = {
      RO.m <- map0;
      sample();
    }

    proc f = RO.f
  }.

  module IND_S(D:Distinguisher) = {
    proc main(): bool = {
      var b;
      RO.init();
      b <@ D(RO).distinguish();
      ERO.sample();
      return b;
    }  
  }.

  section EAGER.

    local lemma eager_query:
       eager [ERO.sample(); , RO.f ~ ERO.f, ERO.sample(); :
                 ={x,RO.m} ==> ={res,RO.m} ].
    proof.
      eager proc.
      inline ERO.sample;swap{2} 4 -3.
      seq 1 1: (={x,work,RO.m});first by sim.
      wp;case ((mem (dom RO.m) x){1}).
      + rnd{1}.
        alias{1} 1 mx = oget RO.m.[x].
        while (={work,RO.m} /\ (RO.m.[x] = Some mx){1}). 
        + by inline *;auto;progress;smt.
        auto;progress [- split]; rewrite sample_ll H /=;smt. 
      case ((!mem work x){1}).
      + swap{1} 2 -1;while (={work,x} /\ eq_except RO.m{1} RO.m{2} (fset1 x{1}) /\ 
                             (!mem work x){1} /\ (RO.m.[x] = Some rd){2} /\ (!mem (dom RO.m) x){1}). 
        + inline *;auto;progress [-split].
          cut -> : mem (dom RO.m{2}) (pick work{2}) = mem (dom RO.m{1}) (pick work{2}) by rewrite !in_dom;smt.
          smt. 
        auto;progress [-split];rewrite !getP_eq;smt. 
      inline RO.f.
      transitivity{1} { rd <$ sample x;
                        while (work <> fset0) {
                          x0  <- pick work;
                          rd0 <$ sample x0;
                          if (!mem (dom RO.m) x0)
                            RO.m.[x0] <- if x0 = x then rd else rd0;
                          work <- work `\` fset1 (pick work);
                        } }
         (={x,work,RO.m} ==> ={x,RO.m})
         ((={x,work,RO.m} /\ mem work{1} x{1}) /\ ! mem (dom RO.m{2}) x{2} ==>
               ={x,RO.m} /\ (result = oget RO.m.[x]){2} /\ mem (dom RO.m{1}) x{1}) => //.
      + by move=> &1 &2 H; exists RO.m{2}, x{2}, work{2}; move: H.
      + transitivity{1} { while (work <> fset0) {
                            x0  <- pick work;
                            rd0 <$ sample x0;
                            if (!mem (dom RO.m) x0) RO.m.[x0] <- rd0;
                            work <- work `\` fset1 (pick work);
                          }
                          rd <$ sample x; }
            (={x,work,RO.m} ==> ={x,RO.m})
            (={x,work,RO.m} ==> ={x,RO.m})=> //.
        + by move=> &1 &2 H; exists RO.m{2}, x{2}, work{2}; move: H.
        + by sim; rnd{2}; sim : (={x,IND_Eager.H.m}); smt.
        symmetry; eager while (H: rd <$ sample x; ~ rd <$ sample x; : ={x} ==> ={rd})=> //; sim. 
        swap{2} 5 -4; swap [2..3] -1; case ((x = pick work){1}).
        + by wp; rnd{2}; rnd; rnd{1}; wp; skip; smt.
        by auto; smt.
      + while (={x, work} /\
               (!mem work x => mem (dom RO.m) x){1} /\
                RO.m.[x]{2} = Some rd{1} /\
                if (mem (dom RO.m) x){1} then ={RO.m}
                else eq_except RO.m{1} RO.m{2} (fset1 x{1})).
        + auto;progress; 1..9,12:smt.
          + case ((pick work = x){2})=> pick_x; last smt.
            subst x{2}; move: H7 H1; rewrite -neqF /eq_except=> -> /= eq_exc.
            by apply fmapP=> x0; case (pick work{2} = x0); smt.
        by auto; smt.
      by auto;progress [-split];rewrite H0 /= getP_eq;smt. 
    qed.

    equiv Eager_S (D <: Distinguisher{RO}): IND_S(D).main ~ IND(ERO,D).main: ={glob D} ==> ={res,RO.m,glob D}.
    proof.
      proc; inline ERO.init RO.init.
      seq 1 1: (={glob D, RO.m});first by wp. 
      symmetry; eager (H: ERO.sample(); ~ ERO.sample();: ={RO.m} ==> ={RO.m}): 
            (={glob D, RO.m}) => //; first by sim.
      eager proc H (={RO.m}) => //; [by apply eager_query | by sim].
    qed.

    equiv Eager (D <: Distinguisher{RO}): IND(RO,D).main ~ IND(ERO,D).main: ={glob D} ==> ={res,glob D}.
    proof.
      transitivity IND_S(D).main
          (={glob D} ==> ={res,glob D})
          (={glob D} ==> ={res,RO.m,glob D}) => //.
      + by progress;exists (glob D){2}.
      + proc;inline{2} ERO.sample.
        while{2} true (card work{2}). 
        + move=> &m1 z;wp;call (f_ll sample_ll);auto;smt.
        conseq (_: _ ==> ={b,glob D}) => //;[smt | by sim].
      apply (Eager_S D).
    qed.

  end section EAGER.

end GenIdeal.

abstract theory FiniteIdeal.

   clone include Ideal.
   axiom sample_ll (x : from): Distr.weight (sample x) = 1%r.

   op univ : from fset. 
   axiom univP (x:from) : mem univ x.

   module ERO = {
     proc sample() = {
       var work;
       work <- univ;
       while (work <> fset0) {
         RO.f(pick work);
         work = work `\` fset1 (pick work);
       }
     }

     proc init() = {
       RO.m <- map0;
       sample();
     }

     proc f(x:from):to = { return oget RO.m.[x]; }
  }.

  module IND_S(D:Distinguisher) = {
    proc main(): bool = {
      var b;
      RO.init();
      b <@ D(RO).distinguish();
      ERO.sample();
      return b;
    }  
  }.

  section EAGER.

    declare module D: Distinguisher { RO }.

    local clone GenIdeal as GI with 
      op sample <- sample, 
      op RO_dom <- univ
      proof sample_ll by apply sample_ll.

    local equiv ERO_main: 
      IND(GI.ERO, D).main ~ IND(ERO, D).main : ={glob D} ==> ={res, glob D} /\ GI.RO.m{1} = RO.m{2}.
    proof.
      proc.
      call (_:GI.RO.m{1} = RO.m{2} /\ dom RO.m{2} = univ).
      + proc; rcondf{1} 2;auto;progress;[ by rewrite H univP | by apply sample_ll].    
      inline *.
      while (={work} /\ GI.RO.m{1} = RO.m{2} /\ dom RO.m{2} = univ `\` work{2});auto;smt. 
    qed.

    equiv Eager_S : IND_S(D).main ~ IND(ERO,D).main: ={glob D} ==> ={res,RO.m,glob D}.
    proof.
      transitivity GI.IND_S(D).main 
          (={glob D} ==> ={res,glob D} /\ RO.m{1} = GI.RO.m{2})
          (={glob D} ==> ={res,glob D} /\ GI.RO.m{1} = RO.m{2}) => //.
      + by progress;exists (glob D){2}.
      + by sim. 
      transitivity IND(GI.ERO,D).main 
        (={glob D} ==> ={res,glob D, GI.RO.m}) 
        (={glob D} ==> ={res,glob D} /\ GI.RO.m{1} = RO.m{2}) => //.
      + by progress;exists (glob D){2}.
      + by conseq (GI.Eager_S D).
      by apply ERO_main.     
    qed.

    equiv Eager : IND(RO, D).main ~ IND(ERO,D).main: ={glob D} ==> ={res,glob D}.
    proof.
      transitivity IND(GI.RO,D).main 
          (={glob D} ==> ={res,glob D} /\ RO.m{1} = GI.RO.m{2})
          (={glob D} ==> ={res,glob D}) => //.
      + by progress;exists (glob D){2}.
      + by sim. 
      transitivity IND(GI.ERO,D).main 
        (={glob D} ==> ={res,glob D}) 
        (={glob D} ==> ={res,glob D}) => //.
      + by progress;exists (glob D){2}.
      + by conseq (GI.Eager D).
      by conseq ERO_main.
    qed.

  end section EAGER.

end FiniteIdeal.


abstract theory RestrIdeal.

  clone include Ideal.
  axiom sample_ll (x : from): Distr.weight (sample x) = 1%r.

  op test : from -> bool.
  op univ : from fset. 
  op dfl  : to.

  axiom testP x : test x <=> mem univ x. 

  module Restr (O:RO) = {
    proc init = RO.init
    proc f (x:from) : to = {
      var r <- dfl;
      if (test x) r <@ RO.f(x);
      return r;
    }
  }.

  module ERO = {
     proc sample() = {
       var work;
       work <- univ;
       while (work <> fset0) {
         RO.f(pick work);
         work = work `\` fset1 (pick work);
       }
     }

     proc init() = {
       RO.m <- map0;
       sample();
     }

     proc f(x:from):to = { 
       return (if test x then oget RO.m.[x] else dfl);
     }
  }.

  module IND_S(D:Distinguisher) = {
    proc main(): bool = {
      var b;
      RO.init();
      b <@ D(Restr(RO)).distinguish();
      ERO.sample();
      return b;
    }  
  }.

  section EAGER.

    declare module D: Distinguisher { RO }.

    local clone GenIdeal as GI with 
      op sample <- sample, 
      op RO_dom <- univ.

    local module Restr' (O:RO) = {
      proc init() = { }
      proc f(x:from) = {  
        var r <- dfl;
        if (test x) r <@ O.f(x);
        return r;
      }
    }.  
        
    local module RD (O:RO) = D(Restr'(O)).  

    local equiv ERO_main: 
      IND(GI.ERO, RD).main ~ IND(ERO, D).main : ={glob D} ==> ={res, glob D} /\ GI.RO.m{1} = RO.m{2}.
    proof.
      proc.
      call (_:GI.RO.m{1} = RO.m{2} /\ dom RO.m{2} = univ).
      + proc. 
        case (test x{1});[ rcondt{1} 2 | rcondf{1} 2];auto;last smt ml=0.
        by inline *;rcondf{1} 4;auto;progress;2:(by apply sample_ll);rewrite ?H0 ?H -?testP. 
      inline *.
      while (={work} /\ GI.RO.m{1} = RO.m{2} /\ dom RO.m{2} `|` work{2} = univ);auto;1:progress; smt.
    qed.

    equiv Eager_S : IND_S(D).main ~ IND(ERO,D).main: ={glob D} ==> ={res,RO.m,glob D}.
    proof.
      transitivity GI.IND_S(RD).main 
          (={glob D} ==> ={res,glob D} /\ RO.m{1} = GI.RO.m{2})
          (={glob D} ==> ={res,glob D} /\ GI.RO.m{1} = RO.m{2}) => //.
      + by progress;exists (glob D){2}.
      + by sim. 
      transitivity IND(GI.ERO,RD).main 
        (={glob D} ==> ={res,glob D, GI.RO.m}) 
        (={glob D} ==> ={res,glob D} /\ GI.RO.m{1} = RO.m{2}) => //.
      + by progress;exists (glob D){2}.
      + by conseq (GI.Eager_S RD).
      by apply ERO_main.     
    qed.

    equiv Eager : IND(Restr(RO), D).main ~ IND(ERO,D).main: ={glob D} ==> ={res,glob D}.
    proof.
      transitivity IND(GI.RO,RD).main 
          (={glob D} ==> ={res,glob D} /\ RO.m{1} = GI.RO.m{2})
          (={glob D} ==> ={res,glob D}) => //.
      + by progress;exists (glob D){2}.
      + by sim. 
      transitivity IND(GI.ERO,RD).main 
        (={glob D} ==> ={res,glob D}) 
        (={glob D} ==> ={res,glob D}) => //.
      + by progress;exists (glob D){2}.
      + by conseq (GI.Eager RD).
      by conseq ERO_main.
    qed.

  end section EAGER.

end RestrIdeal.