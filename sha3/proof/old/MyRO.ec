require import Option List FSet NewFMap.
        import NewLogic Fun.

(* TODO: move this *)
lemma set_eq (m:('a,'b)fmap) x y: m.[x] = Some y => m.[x<-y] = m.
proof.
  by rewrite fmapP=> Hx x';rewrite getP;case (x'=x)=>//->;rewrite Hx.
qed.

lemma oflistK_uniq (s : 'a list) : uniq s =>
  perm_eq s (elems (oflist s)).
proof. by move/undup_id => {1}<-; apply/FSet.oflistK. qed.

lemma setD1E (s : 'a fset) x :
  perm_eq (elems (s `\` fset1 x)) (rem x (elems s)).
proof.
rewrite setDE; pose s' := List.filter _ _; apply/(perm_eq_trans s').
  rewrite perm_eq_sym oflistK_uniq ?filter_uniq ?uniq_elems.
rewrite /s' rem_filter ?uniq_elems; apply/uniq_perm_eq;
  rewrite ?filter_uniq ?uniq_elems // => y.
by rewrite !mem_filter /predC in_fset1.
qed.

lemma perm_to_rem (s:'a fset) x : 
  mem s x => perm_eq (elems s) (x :: elems (s `\` fset1 x)).
proof.
rewrite memE => /perm_to_rem /perm_eqlP->; apply/perm_cons.
have /perm_eqlP <- := (setD1E s x); rewrite perm_eq_refl.
qed.

lemma mem_drop (s:'a list) n x: mem (drop n s) x => mem s x.
proof. by rewrite -{2}(cat_take_drop n) mem_cat=>->. qed.

lemma mem_take (s:'a list) n x: mem (take n s) x => mem s x.
proof. by rewrite -{2}(cat_take_drop n) mem_cat=>->. qed.
(* end TODO *)

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

lemma iter_ll(O<:Orcl): islossless O.f => islossless Iter(O).iter.
proof.
  move=> O_ll;proc;inline Iter(O).iter.
  while true (size l);auto=>/=.
  + call O_ll;skip=> /=?[*]Hl<-;smt ml=0 w=(size_eq0 size_ge0 size_drop).
  smt ml=0 w=(size_eq0 size_ge0).  
qed.

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
  + by move=> ?&mr[*]<*>;exists (glob O){mr}, (i' :: i :: (s1 ++ s2)).
  + proc;rcondt{1}1=>//;rcondt{2}1=>//.
    rcondt{1}3;1:by auto;conseq(_: true).
    rcondt{2}3;1:by auto;conseq(_: true).
    seq 4 4 : (={l,glob O});last by sim.
    transitivity{1} {Iter(O).iter([i;i']); l <- drop 2 l;} 
      (l{1} = i :: i' :: (s1 ++ s2) /\ ={l, glob O} ==> ={l,glob O})
      (l{1} = i :: i' :: (s1 ++ s2) /\ 
       l{2} = i' :: i :: (s1 ++ s2) /\  ={glob O} ==> ={l,glob O})=>//.
    + by move=>?&mr[*]<*>;exists (glob O){mr}, (i :: i' :: (s1 ++ s2)).
    + inline *;rcondt{2} 2;1:by auto. 
      rcondt{2} 4;1:by auto;sp;conseq(_:true).
      rcondf{2} 6; auto;call(_:true);wp;call(_:true);auto.
    transitivity{1} {Iter(O).iter([i';i]); l <- drop 2 l;} 
      (l{1} = i :: i' :: (s1 ++ s2) /\ 
       l{2} = i' :: i :: (s1 ++ s2) /\  ={glob O} ==> ={l,glob O})
      (l{2} = i' :: i :: (s1 ++ s2) /\ ={l, glob O} ==> ={l,glob O})=>//.
    + by move=>?&mr[*]<*>;exists (glob O){mr}, (i' :: i :: (s1 ++ s2)).
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
  + by move=>?&mr[*]<*>;exists (glob O){mr}, (i :: (s1 ++ s2)).
  + by inline *;sim.    
  transitivity{1} {Iter(O).iter(l); }
   (={glob O} /\ l{1}=i::(s1++s2) /\ l{2}= (s1++i::s2) ==> ={glob O})
   (={l,glob O} /\ l{2}= (s1++i::s2) ==> ={glob O})=>//.
  + by move=>?&mr[*]<*>;exists (glob O){mr}, (s1 ++ i::s2).
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
  + by move=>?&mr[*]-> -> _ ->; exists (glob O){mr}, (i :: (s3 ++ s4)).
  + proc;rcondt{1}1=>//;rcondt{2}1=>//.
    seq 2 2: (s1 = l{1} /\ l{2}=s3++s4 /\ ={glob O}).
    + by wp;call(_:true);auto;progress;rewrite drop0.
    transitivity{1} {Iter(O).iter(l); }
      (={l,glob O} ==> ={glob O}) 
      (s1 = l{1} /\ l{2} = s3 ++ s4 /\ ={glob O} ==> ={glob O})=>//.
    + by move=>?&mr[*]-> -> ->;exists (glob O){mr}, l{1}.
    + by inline Iter(O).iter;sim.
    transitivity{1} {Iter(O).iter(l); }
      (s1 = l{1} /\ l{2} = s3 ++ s4 /\ ={glob O} ==> ={glob O})
      (={l,glob O} ==> ={glob O}) =>//.
    + by move=>?&mr[*]-> -> ->;exists (glob O){mr}, (s3++s4).
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

lemma restr_set m f1 f2 x y: 
  restr f1 m.[x<-(y,f2)] = if f1 = f2 then (restr f1 m).[x<-y] else rem x (restr f1 m).
proof.
  rewrite fmapP;case (f1=f2)=>[->|Hneq]x0;rewrite !(restrP,getP);1: by case (x0=x).
  case (x0=x)=>[->|Hnx];1:by rewrite (eq_sym f2) Hneq remP_eq.
  by rewrite remP Hnx restrP.
qed.

lemma restr_set_eq m f x y: 
  restr f m.[x<-(y,f)] = (restr f m).[x<-y].
proof. by rewrite restr_set. qed.

lemma restr0 f : restr f map0 = map0.
proof. by apply fmapP=>x;rewrite restrP !map0P. qed.

lemma restr_set_neq f2 f1 m x y: 
  !mem (dom m) x =>
  f2 <> f1 => restr f1 m.[x<-(y,f2)] = restr f1 m.
proof.
  by move=>Hm Hneq;rewrite restr_set (eq_sym f1) Hneq rem_id//restr_dom Hm.
qed.

(* -------------------------------------------------------------------------- *)
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


(* -------------------------------------------------------------------------- *)
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

lemma resample_ll : islossless ERO.resample.
proof. 
  proc;call (iter_ll ERO.I _)=>//;apply (sample_ll sampleto_ll).
qed.

lemma eager_init :
  eager [ERO.resample(); , RO.init ~ ERO.init, ERO.resample(); :
         ={RO.m} ==> ={RO.m} ].
proof.
  eager proc. inline{2} *;rcondf{2}3;auto=>/=.
  + by move=>?_;rewrite restr0 dom0 elems_fset0.
  by conseq (_:) (_:true==>true: =1%r) _=>//;call resample_ll.
qed.

lemma iter_perm2 (i1 i2 : from):
  equiv[ Iter(ERO.I).iter ~ Iter(ERO.I).iter :
          l{1} = [i1; i2] /\ l{2} = [i2; i1] /\ ={glob ERO.I} ==>
          ={glob ERO.I}].
proof.
  proc;rcondt{1}1=>//;rcondt{2}1=>//.
  rcondt{1}3;1:by auto;conseq(_:true).
  rcondt{2}3;1:by auto;conseq(_:true).
  seq 4 4 : (={l,RO.m});2:by sim.
  case (i1=i2);1:by sim.
  inline *;swap[4..5]-2;swap{2} 6-2;auto=>?&mr[*]3!<*>Hneq/=?->?->/=.
  by rewrite set_set Hneq. 
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
    + auto=>?&mr[*]-> ->;case (l{mr})=>//=x2 l2 Hmx Hgx?->.
      by rewrite getP drop0 /#.
    auto=>??[*]-> ->/= Hmem HK;rewrite sampleto_ll/==> r _. 
    rewrite -memE restr_dom Hmem/= HK.
    rewrite {1}get_oget //= -HK;case:(oget _)HK=> x1?/=->.
    by move=>????-> _[*]_-> _ Heq?;rewrite in_dom set_eq Heq. 
  rcondt{2} 2. + auto=> ?[*]-> ->;rewrite negb_and /#.
  case ((mem (dom RO.m) x){1}).
  + inline{1} ERO.resample=>/=;rnd{1}.
    transitivity{1} { Iter(ERO.I).iter(x::elems ((dom (restr Unknown RO.m)) `\` fset1 x));
                      }
      (={x,RO.m} /\ mem (dom RO.m{1}) x{1} /\ (oget RO.m{1}.[x{1}]).`2 = Unknown ==>
       ={x,RO.m})
      (={x,RO.m} /\ mem (dom RO.m{1}) x{1} /\ (oget RO.m{1}.[x{1}]).`2 = Unknown==>
       ={x} /\ eq_except RO.m{1} RO.m{2} (fset1 x{1}) /\
       RO.m{1}.[x{2}] = Some (result{2},Unknown) /\
       RO.m{2}.[x{2}] = Some (result{2},Known)).
    + by move=>?&mr[*]-> -> ??;exists RO.m{mr}, x{mr}=>/#.
    + move=>???;rewrite in_dom=>[*]<*>[*]->/eq_except_sym H Hxm Hx2.
      rewrite sampleto_ll=> r _;rewrite /= Hxm oget_some /=;apply /eq_sym.
      have /(congr1 oget):= Hx2 => <-;apply eq_except_set_eq=>//.
      by rewrite in_dom Hx2.
    + call (iter_perm ERO.I iter_perm2).
      skip=> &1 &2 [[->> ->>]] [Hdom Hm];progress.
      by apply /perm_to_rem/restr_dom;rewrite Hdom Hm.
    inline *;rcondt{1} 2;1:by auto.
    while (={x,l} /\ !mem l{1} x{1}/\
           eq_except RO.m{1} RO.m{2} (fset1 x{1}) /\
           RO.m{1}.[x{2}] = Some (result{2}, Unknown) /\
           RO.m{2}.[x{2}] = Some (result{2}, Known)).
    + auto=> ?&mr[*]2!->Hm Hex Hm1 Hmr Hneq _/=?->.
      rewrite (contra _ _ (mem_drop _ 1 _) Hm) /=.
      rewrite!getP;move:Hm;rewrite-(mem_head_behead witness l{mr})//negb_or=>-[]->_.
      by rewrite Hm1 Hmr/=;apply eq_except_set. 
    auto=>?&mr[[->>->>]][]Hdom Hm /=/=?->/=.
    rewrite !drop0 restr_set /= dom_rem /= -memE !inE /=.
    by rewrite !getP_eq /= oget_some/= set2_eq_except.
  inline *. swap{1}3-2.
  while (={l,x} /\ !mem l{1} x{1} /\ RO.m{1}.[x{1}] = None /\
         RO.m{2} = RO.m{1}.[x{2}<-(r{2},Known)]).
  + auto=> ?&mr[*]2!->Hm Hn Heq Hl _/=?->.
    rewrite (contra _ _ (mem_drop _ 1 _) Hm) /=.
    rewrite set_set -Heq !getP -(eq_sym (x{mr})).
    by move:Hm;rewrite -(mem_head_behead witness l{mr} Hl) -Hn negb_or=>-[]->.
  auto=> ?&mr[*]2!->_ Hnm/=?->.
  rewrite -memE restr_set_neq //= restr_dom Hnm /=.
  by have:=Hnm;rewrite in_dom/==>->/=????->->;rewrite in_dom getP_eq oget_some. 
qed.

lemma eager_set :
  eager [ERO.resample(); , RO.set ~ ERO.set, ERO.resample(); :
         ={x,y} /\ ={RO.m} ==> ={res,RO.m} ].
proof.
  eager proc.
  case ((mem (dom RO.m) x /\ (oget RO.m.[x]).`2 = Unknown){1}).
  inline{1} ERO.resample=>/=;wp 1 2.
    transitivity{1} { Iter(ERO.I).iter(x::elems ((dom (restr Unknown RO.m)) `\` fset1 x));
                      }
      (={x,y,RO.m} /\ mem (dom RO.m{1}) x{1} /\ (oget RO.m{1}.[x{1}]).`2 = Unknown ==>
       ={x,y,RO.m})
      (={x,y,RO.m} /\ mem (dom RO.m{1}) x{1} /\ (oget RO.m{1}.[x{1}]).`2 = Unknown==>
       ={x,y} /\ eq_except RO.m{1} RO.m{2} (fset1 x{1}) /\
       RO.m{2}.[x{2}] = Some (y{2},Known)).
    + by move=>?&mr[*]-> -> ???;exists RO.m{mr}, y{mr}, x{mr}=>/#.
    + move=>??? [*]<*>[*]-> -> Hex Hm2.
      by rewrite (eq_except_set_eq RO.m{2} RO.m{m} x{2}) ?in_dom ?Hm2// eq_except_sym.
    + call (iter_perm ERO.I iter_perm2).
      skip=>?&mr[][]->>[]->>->>[]Hdom Hm/=.
      by apply /perm_to_rem/restr_dom;rewrite Hdom Hm.
    inline *;rcondt{1} 2;1:by auto.
    while (={x,l} /\ !mem l{1} x{1}/\
           eq_except RO.m{1} RO.m{2} (fset1 x{1}) /\
           RO.m{2}.[x{2}] = Some (y{2}, Known)).
    + auto=> ?&mr[*]2!->Hm Hex Hm1 Hmr _/=?->.
      rewrite (contra _ _ (mem_drop _ 1 _) Hm) /=.
      rewrite!getP;move:Hm;rewrite-(mem_head_behead witness l{mr})//negb_or=>-[]->_.
      by rewrite Hm1 /=;apply eq_except_set. 
    auto=>?&mr[*]3!<*>Hdom Hm /=/=;rewrite !drop0 sampleto_ll=>/=?_.
    by rewrite -memE restr_set /= dom_rem !inE !getP_eq set2_eq_except.
  inline *;wp.
  while (={x,l} /\ !mem l{1} x{1}/\
         eq_except RO.m{1} RO.m{2} (fset1 x{1}) /\
         RO.m{2}.[x{2}] = Some (y{2}, Known)).
  + auto=> ?&mr[*]2!->Hm Hex Hm1 Hmr _/=?->.
    rewrite (contra _ _ (mem_drop _ 1 _) Hm) /=.
    rewrite!getP;move:Hm;rewrite-(mem_head_behead witness l{mr})//negb_or=>-[]->_.
    by rewrite Hm1 /=;apply eq_except_set. 
  auto=> ?&mr[*]3!-> Hnm /=. 
  rewrite-memE restr_set/=rem_id?restr_dom//=Hnm.
  rewrite getP_eq eq_except_sym set_eq_except/=.
  move=>/=????2!->/=[]/eq_except_sym? Hx2;apply/eq_sym.
  have/(congr1 oget):=Hx2=><-;apply eq_except_set_eq=>//;by rewrite in_dom Hx2.
qed.

lemma eager_in_dom:
  eager [ERO.resample(); , RO.in_dom ~ ERO.in_dom, ERO.resample(); :
         ={x,f} /\ ={RO.m} ==> ={res,RO.m} ].
proof.
  eager proc;inline *;wp.
  while (={l,RO.m} /\ (forall z, mem l z => in_dom_with RO.m z Unknown){1} /\
         in_dom_with RO.m{1} x{1} f{1} = result{2}).
  + auto=>?&mr[*]2!->Hz <-?_/=?->/=. 
    by split=>[z Hm|];rewrite /in_dom_with dom_set getP !inE/#.
  by auto=>?&mr/=[*]3!->/=;split=>// z;rewrite -memE restr_dom. 
qed.

lemma eager_restrK:
  eager [ERO.resample(); , RO.restrK ~ ERO.restrK, ERO.resample(); :
         ={RO.m} ==> ={res,RO.m} ].
proof.
  eager proc;inline *;wp.
  while (={l,RO.m} /\ (forall z, mem l z => in_dom_with RO.m z Unknown){1} /\
         restr Known RO.m{1} = result{2}).
  + auto=>?&mr[*]2!->Hz<-?_/=?->/=. 
    split=>[z Hm|];1:by rewrite /in_dom_with dom_set getP !inE/#.
    rewrite restr_set rem_id?restr_dom//.
    by move:H=>/(mem_head_behead witness) /(_ (head witness l{mr})) /= /Hz /#.
  by auto=>?&mr/=->/=;split=>// z;rewrite -memE restr_dom. 
qed.

lemma eager_sample:
  eager [ERO.resample(); , RO.sample ~ ERO.sample, ERO.resample(); :
         ={x,RO.m} ==> ={res,RO.m} ].
proof.
  eager proc.
  transitivity{2} {
      c <$ sampleto x; RO.m.[x] <- (c, Unknown);
      Iter(ERO.I).iter(x::elems ((dom (restr Unknown RO.m)) `\` fset1 x));}
      (={x,RO.m} ==> ={x,RO.m}) 
      (={x,RO.m} ==> ={x,RO.m})=>//;last first.
  + inline{2} ERO.resample;call (iter_perm ERO.I iter_perm2);auto=>?&mr[]->->/=?->.
    by rewrite !restr_set/= !dom_set perm_eq_sym perm_to_rem !inE.
  + by move=>?&mr[*]2!->;exists RO.m{mr}, x{mr}.
  inline ERO.resample;inline{2}*;rcondt{2}4;1:by auto.
  wp;case ((!mem (dom RO.m) x \/ (oget RO.m.[x]).`2=Known){1}).
  + inline *;swap{1}3-1.
    while (={x,l} /\ RO.m{1}.[x{1} <- (c{1}, Unknown)] = RO.m{2} /\ !(mem l x){1}).
    + auto=>?&mr[*]2!-><- Hnm Hl _/=?->.
      rewrite (contra _ _ (mem_drop _ 1 _) Hnm) /= set_set.
      by move:Hnm;rewrite-(mem_head_behead witness l{mr})//negb_or eq_sym=>-[]->.
    auto=>?&mr[*]2!->?/=;rewrite sampleto_ll=>?_?->;rewrite drop0.
    rewrite restr_set/= dom_set fsetDK.
    cut<-/=:dom (restr Unknown RO.m{mr}) =
            dom (restr Unknown RO.m{mr}) `\` fset1 x{mr}.
    + apply fsetP=>z;rewrite !(restr_dom,inE)/#.
    by rewrite set_set/= -memE restr_dom;split=>/#.
  transitivity{1} {
    Iter(ERO.I).iter(x::elems ((dom (restr Unknown RO.m)) `\` fset1 x));
    c<$ sampleto x;}
    (={x,RO.m} /\ (mem (dom RO.m) x /\ (oget RO.m.[x]).`2=Unknown){1} ==> ={x,c,RO.m}) 
    (={x,RO.m} /\ (mem (dom RO.m) x /\ (oget RO.m.[x]).`2=Unknown){1} ==> 
     ={x} /\ RO.m{1}.[x{1} <- (c{1}, Unknown)] = RO.m{2})=>//.
  + by move=>?&mr[*]2!->?;exists RO.m{mr}, x{mr}=>/#.
  + rnd;call (iter_perm ERO.I iter_perm2);auto=>?&mr[*]->->/=??;split=>//.
    by rewrite perm_to_rem restr_dom.
  inline *;rcondt{1}2;1:by auto.
  swap{1} 7-2.
  while (={x,l} /\ RO.m{1}.[x{1} <- (c{1}, Unknown)] = RO.m{2} /\ !(mem l x){1}).
  + auto=>?&mr[*]2!-><- Hnm Hl _/=?->.
    rewrite (contra _ _ (mem_drop _ 1 _) Hnm) /= set_set.
    by move:Hnm;rewrite-(mem_head_behead witness l{mr})//negb_or eq_sym=>-[]->.
  by auto=>?&mr[*]2!->??/=?->?->;rewrite!drop0 restr_set/=dom_set fsetDK-memE!inE.
qed.

section.

declare module D:Distinguisher {RO}.

lemma eager_D : eager [ERO.resample(); , D(RO).distinguish ~ 
                       D(ERO).distinguish, ERO.resample(); :
                       ={glob D,RO.m} ==> ={RO.m, glob D} /\ ={res} ].
proof.
  eager proc (H_: ERO.resample(); ~ ERO.resample();: ={RO.m} ==> ={RO.m})
             (={RO.m})=>//; try by sim.
  + by apply eager_init. + by apply eager_get. + by apply eager_set. 
  + by apply eager_sample. + by apply eager_in_dom. + by apply eager_restrK. 
qed.


module Eager (D:Distinguisher) = {

  proc main1() = {
    var b;
    RO.init();
    b <@ D(RO).distinguish();
    return b;
  }

  proc main2() = {
    var b;
    RO.init();
    b <@ D(ERO).distinguish();
    ERO.resample();
    return b;
  }

}.

equiv Eager_1_2: Eager(D).main1 ~ Eager(D).main2 : 
  ={glob D} ==> ={res,glob RO, glob D}.
proof.
  proc.
  transitivity{1} 
    { RO.init(); ERO.resample(); b <@ D(RO).distinguish(); }
    (={glob D} ==> ={b,RO.m,glob D})
    (={glob D} ==> ={b,RO.m,glob D})=> //.
  + by move=> ?&mr->;exists (glob D){mr}.
  + inline *;rcondf{2}3;2:by sim.
    by auto=>?;rewrite restr0 dom0 elems_fset0.
  seq 1 1: (={glob D, RO.m});1:by inline *;auto.
  by eager call eager_D. 
qed.

end GenEager.
