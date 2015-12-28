require import Pair Option List FSet NewFMap.
        import NewLogic Fun.
require IterProc.

(* FIXME notation *)
abbrev ([+]) ['a 'b](x : 'b) = fun (_ : 'a) => x.

type flag = [ Unknown | Known ].

lemma neqK_eqU f : f <> Known <=> f = Unknown.
proof. by case: f. qed.

op in_dom_with (m:('from, 'to * 'flag)fmap) (x:'from) (f:'flag) = 
   mem (dom m) x /\ (oget (m.[x])).`2 = f.

op restr f (m:('from, 'to * 'flag)fmap) = 
  let m = filter (fun _ (p:'to*'flag) => p.`2=f) m in
  map (fun _ (p:'to*'flag) => p.`1) m.

lemma restrP (m:('from, 'to * 'flag)fmap) f x: 
  (restr f m).[x] = 
  obind (fun (p:'to*'flag)=>if p.`2=f then Some p.`1 else None) m.[x].
proof.
  rewrite /restr /= mapP filterP in_dom /=.
  by case (m.[x])=>//= -[x0 f'];rewrite oget_some /=;case (f' = f).
qed.

lemma dom_restr (m:('from, 'to * 'flag)fmap) f x: 
  mem (dom(restr f m)) x <=> in_dom_with m x f. 
proof. 
  rewrite /in_dom_with !in_dom;case: (m.[x]) (restrP m f x)=>//= -[t f'] /=.
  by rewrite oget_some /=;case (f' = f)=> [_ ->|].
qed.

lemma restr_set (m:('from, 'to * 'flag)fmap) f1 f2 x y: 
  restr f1 m.[x<-(y,f2)] = if f1 = f2 then (restr f1 m).[x<-y] else rem x (restr f1 m).
proof.
  rewrite fmapP;case (f1=f2)=>[->|Hneq]x0;rewrite !(restrP,getP);1: by case (x0=x).
  case (x0=x)=>[->|Hnx];1:by rewrite (eq_sym f2) Hneq remP_eq.
  by rewrite remP Hnx restrP.
qed.

lemma restr_set_eq (m:('from, 'to * 'flag)fmap) f x y: 
  restr f m.[x<-(y,f)] = (restr f m).[x<-y].
proof. by rewrite restr_set. qed.

lemma restr0 f : restr f map0<:'from, 'to * 'flag> = map0.
proof. by apply fmapP=>x;rewrite restrP !map0P. qed.

lemma restr_set_neq f2 f1 (m:('from, 'to * 'flag)fmap) x y: 
  !mem (dom m) x =>
  f2 <> f1 => restr f1 m.[x<-(y,f2)] = restr f1 m.
proof.
  by move=>Hm Hneq;rewrite restr_set(eq_sym f1)Hneq rem_id//dom_restr/in_dom_with Hm.
qed.

lemma restr_rem (m:('from,'to*'flag)fmap) x f: 
  restr f (rem x m) = 
   if in_dom_with m x f then rem x (restr f m) else restr f m.
proof.
  rewrite fmapP=>z;rewrite restrP;case (in_dom_with m x f);
   rewrite !(restrP,remP) /in_dom_with in_dom /#.
qed.

abstract theory Ideal.

type from, to.

op sampleto : from -> to distr.

module type RO = {
  proc init  ()                  : unit
  proc get   (x : from)          : to
  proc set   (x : from, y : to)  : unit
  proc rem   (x : from)          : unit
  proc sample(x : from)          : unit
}.

module type RO_Distinguisher(G : RO) = {
  proc distinguish(): bool 
}.

module type FRO = {
  proc init  ()                  : unit
  proc get   (x : from)          : to
  proc set   (x : from, y : to)  : unit
  proc rem   (x : from)          : unit 
  proc sample(x : from)          : unit
  proc in_dom(x : from,f : flag) : bool
  proc restrK()                  : (from,to)fmap
}.

module type FRO_Distinguisher(G : FRO) = {
  proc distinguish(): bool 
}.

(* -------------------------------------------------------------------------- *)
module RO : RO = {
  var m : (from, to)fmap

  proc init () = { m <- map0; }

  proc get(x:from) = {
    var r;
    r <$ sampleto x;
    if (!mem (dom m) x) m.[x] <- r;
    return (oget m.[x]);
  }

  proc set (x:from, y:to) = {
    m.[x] <- y;
  }

  proc rem (x:from) = {
    m <- rem x m;
  }

  proc sample(x:from) = {
    get(x);
  }

  proc restrK() = {
    return m;
  }

}.

module FRO : FRO = {
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

   proc rem (x:from) = {
    m <- rem x m;
  }

  proc sample(x:from) = {
    var c;
    c <$ sampleto x;
    if (!mem (dom m) x) m.[x] <- (c,Unknown);
  }

  proc in_dom(x:from, f:flag) = {
    return in_dom_with m x f;
  }

  proc restrK() = {
    return restr Known m;
  }

}.

equiv RO_FRO_init : RO.init ~ FRO.init : true ==> RO.m{1} = map (+fst) FRO.m{2}.
proof. by proc;auto=>/=;rewrite map_map0. qed.

equiv RO_FRO_get : RO.get ~ FRO.get :
   ={x} /\ RO.m{1} = map (+fst) FRO.m{2} ==> ={res} /\ RO.m{1} = map (+fst) FRO.m{2}.
proof. 
  proc;auto=>?&ml[]->->/=?->/=.
  rewrite !dom_map !map_set/fst/= getP_eq oget_some;progress.
  + by rewrite mapP oget_omap_some // -in_dom. 
  by apply /eq_sym/set_eq;rewrite get_oget?dom_map// mapP oget_omap_some// -in_dom. 
qed.

equiv RO_FRO_set : RO.set ~ FRO.set :
   ={x,y} /\ RO.m{1} = map (+fst) FRO.m{2} ==> RO.m{1} = map (+fst) FRO.m{2}.
proof. by proc;auto=>?&ml[*]3!->;rewrite map_set. qed.

equiv RO_FRO_rem : RO.rem ~ FRO.rem :
   ={x} /\ RO.m{1} = map (+fst) FRO.m{2} ==> RO.m{1} = map (+fst) FRO.m{2}.
proof. by proc;auto=>??;rewrite map_rem. qed.

equiv RO_FRO_sample : RO.sample ~ FRO.sample :
   ={x} /\ RO.m{1} = map (+fst) FRO.m{2} ==> RO.m{1} = map (+fst) FRO.m{2}.
proof. 
  by proc;inline *;auto=>?&ml[]2!->/=?->;rewrite dom_map/= map_set. 
qed.

lemma RO_FRO_D (D<:RO_Distinguisher{RO,FRO}) : 
  equiv [D(RO).distinguish ~ D(FRO).distinguish : 
     ={glob D} /\ RO.m{1} = map (+fst) FRO.m{2} ==>
     ={glob D} /\ RO.m{1} = map (+fst) FRO.m{2} ].
proof.
  proc (RO.m{1} = map (+fst) FRO.m{2})=>//.
  + by conseq RO_FRO_init. + by conseq RO_FRO_get. + by conseq RO_FRO_set. 
  + by conseq RO_FRO_rem. + by conseq RO_FRO_sample.
qed.

section LL. 

lemma RO_init_ll : islossless RO.init.
proof. by proc;auto. qed.

lemma FRO_init_ll : islossless FRO.init.
proof. by proc;auto. qed.

lemma FRO_in_dom_ll : islossless FRO.in_dom.
proof. by proc. qed.

lemma FRO_restrK_ll : islossless FRO.restrK.
proof. by proc. qed.

lemma RO_set_ll : islossless RO.set.
proof. by proc;auto. qed.

lemma FRO_set_ll : islossless FRO.set.
proof. by proc;auto. qed.

axiom sampleto_ll : forall x, Distr.weight (sampleto x) = 1%r.

lemma RO_get_ll : islossless RO.get.
proof. by proc;auto;progress;apply sampleto_ll. qed.

lemma FRO_get_ll : islossless FRO.get.
proof. by proc;auto;progress;apply sampleto_ll. qed.

lemma RO_sample_ll : islossless RO.sample.
proof. by proc;call RO_get_ll. qed.

lemma FRO_sample_ll : islossless FRO.sample.
proof. by proc;auto;progress;apply sampleto_ll. qed.

end section LL.
 
end Ideal.

(* -------------------------------------------------------------------------- *)

abstract theory GenEager.

clone include Ideal. 

axiom sampleto_ll : forall x, Distr.weight (sampleto x) = 1%r.

clone include IterProc with type t <- from.

(** A module that resample query if the associate value is unknown *)
module RRO : FRO = {

  proc init = FRO.init

  proc get(x:from) = {
    var r;
    r <$ sampleto x;
    if (!mem (dom FRO.m) x || (oget FRO.m.[x]).`2 = Unknown) {
      FRO.m.[x] <- (r,Known);
    }
    return (oget FRO.m.[x]).`1;
  }

  proc set = FRO.set 

  proc rem = FRO.rem

  proc sample = FRO.sample

  proc in_dom = FRO.in_dom

  proc restrK = FRO.restrK

  module I = {
    proc f (x:from) = {
      var c;
      c <$ sampleto x;
      FRO.m.[x] <- (c,Unknown);
    }
  }

  proc resample () = {
    Iter(I).iter (elems (dom (restr Unknown FRO.m)));
  }

}.

(* A module which is lazy on sample *)
module LRO : RO = {

  proc init = RO.init

  proc get = RO.get

  proc set = RO.set 

  proc rem = RO.rem

  proc sample(x:from) = {}

}.

lemma RRO_resample_ll : islossless RRO.resample.
proof. 
  proc;call (iter_ll RRO.I _)=>//;proc;auto=>/=?;apply sampleto_ll. 
qed.

lemma eager_init :
  eager [RRO.resample(); , FRO.init ~ RRO.init, RRO.resample(); :
         ={FRO.m} ==> ={FRO.m} ].
proof.
  eager proc. inline{2} *;rcondf{2}3;auto=>/=.
  + by move=>?_;rewrite restr0 dom0 elems_fset0.
  by conseq (_:) (_:true==>true: =1%r) _=>//;call RRO_resample_ll.
qed.

lemma iter_perm2 (i1 i2 : from):
  equiv[ Iter(RRO.I).iter_12 ~ Iter(RRO.I).iter_21 :
            ={glob RRO.I, t1, t2} ==> ={glob RRO.I}].
proof.
  proc;inline *;case ((t1=t2){1});1:by auto.
  by swap{2}[4..5]-3;auto=> &ml&mr[*]3!->neq/=?->?->;rewrite set_set neq.
qed.

lemma eager_get :
  eager [RRO.resample(); , FRO.get ~ RRO.get, RRO.resample(); :
         ={x,FRO.m} ==> ={res,FRO.m} ].
proof.
  eager proc.
  wp;case ((mem (dom FRO.m) x /\ (oget FRO.m.[x]).`2=Known){1}).
  + rnd{1};rcondf{2} 2;1:by auto=> /#.
    exists * ((oget FRO.m.[x{2}]){1}).
;inline RRO.resample.
    cut := iter_inv RRO.I (fun z=>x{1}<>z) (fun m1 m2 => m1 = m2 /\ .
    print iter_inv.
    while (={l,FRO.m} /\ (!mem l x /\ FRO.m.[x] = Some (mx.`1,Known)){1}).
    + auto=>?&mr[*]-> ->;case (l{mr})=>//=x2 l2 Hmx Hgx?->.
      by rewrite getP drop0 /#.
    auto=>??[*]-> ->/= Hmem HK;rewrite sampleto_ll/==> r _. 
    rewrite -memE dom_restr Hmem/= HK.
    rewrite {1}get_oget //= -HK;case:(oget _)HK=> x1?/=->.
    by move=>????-> _[*]_-> _ Heq?;rewrite in_dom set_eq Heq. 
  rcondt{2} 2. + auto=> ?[*]-> ->;rewrite negb_and /#.
  case ((mem (dom FRO.m) x){1}).
  + inline{1} RRO.resample=>/=;rnd{1}.
    transitivity{1} 
      { Iter(RRO.I).iter(x::elems ((dom (restr Unknown FRO.m)) `\` fset1 x)); }
      (={x,FRO.m} /\ mem (dom FRO.m{1}) x{1} /\ (oget FRO.m{1}.[x{1}]).`2 = Unknown ==>
       ={x,FRO.m})
      (={x,FRO.m} /\ mem (dom FRO.m{1}) x{1} /\ (oget FRO.m{1}.[x{1}]).`2 = Unknown==>
       ={x} /\ eq_except FRO.m{1} FRO.m{2} (fset1 x{1}) /\
       FRO.m{1}.[x{2}] = Some (result{2},Unknown) /\
       FRO.m{2}.[x{2}] = Some (result{2},Known)).
    + by move=>?&mr[*]-> -> ??;exists FRO.m{mr}, x{mr}=>/#.
    + move=>???;rewrite in_dom=>[*]<*>[*]->/eq_except_sym H Hxm Hx2.
      rewrite sampleto_ll=> r _;rewrite /= Hxm oget_some /=;apply /eq_sym.
      have /(congr1 oget):= Hx2 => <-;apply eq_except_set_eq=>//.
      by rewrite in_dom Hx2.
    + call (iter_perm RRO.I iter_perm2).
      skip=> &1 &2 [[->> ->>]] [Hdom Hm];progress.
      by apply /perm_to_rem/dom_restr;rewrite Hdom Hm.
    inline *;rcondt{1} 2;1:by auto.
    while (={x,l} /\ !mem l{1} x{1}/\
           eq_except FRO.m{1} FRO.m{2} (fset1 x{1}) /\
           FRO.m{1}.[x{2}] = Some (result{2}, Unknown) /\
           FRO.m{2}.[x{2}] = Some (result{2}, Known)).
    + auto=> ?&mr[*]2!->Hm Hex Hm1 Hmr Hneq _/=?->.
      rewrite (contra _ _ (mem_drop 1 _ _) Hm) /= !getP.
      move:Hm;rewrite-(mem_head_behead witness l{mr})//negb_or=>-[]-> _/=.
      rewrite Hm1 Hmr/=;apply eq_except_set=>//.
    auto=>?&mr[[->>->>]][]Hdom Hm /=/=?->/=.
    rewrite !drop0 restr_set /= dom_rem /= -memE !inE /=.
    by rewrite !getP_eq /= oget_some/= set2_eq_except.
  inline *. swap{1}3-2.
  while (={l,x} /\ !mem l{1} x{1} /\ FRO.m{1}.[x{1}] = None /\
         FRO.m{2} = FRO.m{1}.[x{2}<-(r{2},Known)]).
  + auto=> ?&mr[*]2!->Hm Hn Heq Hl _/=?->.
    rewrite (contra _ _ (mem_drop 1 _ _) Hm) /=.
    rewrite set_set -Heq !getP -(eq_sym (x{mr})).
    by move:Hm;rewrite -(mem_head_behead witness l{mr} Hl) -Hn negb_or=>-[]->.
  auto=> ?&mr[*]2!->_ Hnm/=?->.
  rewrite -memE restr_set_neq //= dom_restr Hnm /=.
  by have:=Hnm;rewrite in_dom/==>->/=????->->;rewrite in_dom getP_eq oget_some. 
qed.

lemma eager_set :
  eager [RRO.resample(); , FRO.set ~ RRO.set, RRO.resample(); :
         ={x,y} /\ ={FRO.m} ==> ={res,FRO.m} ].
proof.
  eager proc.
  case ((mem (dom FRO.m) x /\ (oget FRO.m.[x]).`2 = Unknown){1}).
  inline{1} RRO.resample=>/=;wp 1 2.
    transitivity{1} { Iter(RRO.I).iter(x::elems ((dom (restr Unknown FRO.m)) `\` fset1 x));
                      }
      (={x,y,FRO.m} /\ mem (dom FRO.m{1}) x{1} /\ (oget FRO.m{1}.[x{1}]).`2 = Unknown ==>
       ={x,y,FRO.m})
      (={x,y,FRO.m} /\ mem (dom FRO.m{1}) x{1} /\ (oget FRO.m{1}.[x{1}]).`2 = Unknown==>
       ={x,y} /\ eq_except FRO.m{1} FRO.m{2} (fset1 x{1}) /\
       FRO.m{2}.[x{2}] = Some (y{2},Known)).
    + by move=>?&mr[*]-> -> ???;exists FRO.m{mr}, y{mr}, x{mr}=>/#.
    + move=>??? [*]<*>[*]-> -> Hex Hm2.
      by rewrite (eq_except_set_eq FRO.m{2} FRO.m{m} x{2}) ?in_dom ?Hm2// eq_except_sym.
    + call (iter_perm RRO.I iter_perm2).
      skip=>?&mr[][]->>[]->>->>[]Hdom Hm/=.
      by apply /perm_to_rem/dom_restr;rewrite Hdom Hm.
    inline *;rcondt{1} 2;1:by auto.
    while (={x,l} /\ !mem l{1} x{1}/\
           eq_except FRO.m{1} FRO.m{2} (fset1 x{1}) /\
           FRO.m{2}.[x{2}] = Some (y{2}, Known)).
    + auto=> ?&mr[*]2!->Hm Hex Hm1 Hmr _/=?->.
      rewrite (contra _ _ (mem_drop 1 _ _) Hm) /=.
      rewrite!getP;move:Hm;rewrite-(mem_head_behead witness l{mr})//negb_or=>-[]->_.
      by rewrite Hm1 /=;apply eq_except_set. 
    auto=>?&mr[*]3!<*>Hdom Hm /=/=;rewrite !drop0 sampleto_ll=>/=?_.
    by rewrite -memE restr_set /= dom_rem !inE !getP_eq set2_eq_except.
  inline *;wp.
  while (={x,l} /\ !mem l{1} x{1}/\
         eq_except FRO.m{1} FRO.m{2} (fset1 x{1}) /\
         FRO.m{2}.[x{2}] = Some (y{2}, Known)).
  + auto=> ?&mr[*]2!->Hm Hex Hm1 Hmr _/=?->.
    rewrite (contra _ _ (mem_drop 1 _ _) Hm) /=.
    rewrite!getP;move:Hm;rewrite-(mem_head_behead witness l{mr})//negb_or=>-[]->_.
    by rewrite Hm1 /=;apply eq_except_set. 
  auto=> ?&mr[*]3!-> Hnm /=. 
  rewrite-memE restr_set/=rem_id?dom_restr//=Hnm.
  rewrite getP_eq eq_except_sym set_eq_except/=.
  move=>/=????2!->/=[]/eq_except_sym? Hx2;apply/eq_sym.
  have/(congr1 oget):=Hx2=><-;apply eq_except_set_eq=>//;by rewrite in_dom Hx2.
qed.

lemma eager_rem: 
  eager [RRO.resample(); , FRO.rem ~ RRO.rem, RRO.resample(); :
         ={x} /\ ={FRO.m} ==> ={res,FRO.m} ].
proof.
  eager proc;case ((in_dom_with FRO.m x Unknown){1}).
  + inline RRO.resample;wp.
    transitivity{1} 
      { Iter(RRO.I).iter(x::elems (dom (restr Unknown FRO.m) `\` fset1 x)); }
      (={x,FRO.m}/\(in_dom_with FRO.m x Unknown){1}==> ={x,FRO.m}) 
      (={x,FRO.m}/\ (in_dom_with FRO.m x Unknown){1} ==> (rem x FRO.m){1} = FRO.m{2})=>//.
    + by move=>?&mr[*]2!->_;exists FRO.m{mr}, x{mr}.   
    + call (iter_perm RRO.I iter_perm2);skip=>?&mr[*]2!->?/=.
      by apply /perm_to_rem/dom_restr. 
    inline *;rcondt{1}2;1:by auto.
    while (={l} /\ FRO.m{2} = rem x{1} FRO.m{1} /\ !(mem l x){1}).  
    + auto=>?&mr[*]->-> ^ + Hm Hl _/=?->.
      rewrite rem_set-(mem_head_behead witness l{mr})//negb_or=>-[]->_/=.
      by rewrite (contra _ _ (mem_drop 1 _ _) Hm).
    auto=>?&mr[*]2!->Hidm/=;rewrite sampleto_ll/==>?.
    by rewrite drop0 restr_rem Hidm/= dom_rem rem_set -memE !inE.
  inline *;wp. 
  while (={l} /\ FRO.m{2} = rem x{1} FRO.m{1} /\ !(mem l x){1}).
  + auto=>?&mr[*]->-> ^ + Hm Hl _/=?->.
    rewrite rem_set-(mem_head_behead witness l{mr})//negb_or=>-[]->_/=.
    by rewrite (contra _ _ (mem_drop 1 _ _) Hm).
  by auto=>?&mr[*]2!->Hndw/=;rewrite restr_rem Hndw//= -memE dom_restr. 
qed.

lemma eager_in_dom:
  eager [RRO.resample(); , FRO.in_dom ~ RRO.in_dom, RRO.resample(); :
         ={x,f} /\ ={FRO.m} ==> ={res,FRO.m} ].
proof.
  eager proc;inline *;wp.
  while (={l,FRO.m} /\ (forall z, mem l z => in_dom_with FRO.m z Unknown){1} /\
         in_dom_with FRO.m{1} x{1} f{1} = result{2}).
  + auto=>?&mr[*]2!->Hz <-?_/=?->/=. 
    split=>[z /mem_drop Hm|];rewrite /in_dom_with dom_set getP !inE /#.
  by auto=>?&mr/=[*]3!->/=;split=>// z;rewrite -memE dom_restr. 
qed.

lemma eager_restrK:
  eager [RRO.resample(); , FRO.restrK ~ RRO.restrK, RRO.resample(); :
         ={FRO.m} ==> ={res,FRO.m} ].
proof.
  eager proc;inline *;wp.
  while (={l,FRO.m} /\ (forall z, mem l z => in_dom_with FRO.m z Unknown){1} /\
         restr Known FRO.m{1} = result{2}).
  + auto=>?&mr[*]2!->Hz<-?_/=?->/=. 
    split=>[z /mem_drop Hm|];1:by rewrite /in_dom_with dom_set getP !inE /#.
    rewrite restr_set rem_id?dom_restr//.
    by move:H=>/(mem_head_behead witness) /(_ (head witness l{mr})) /= /Hz /#.
  by auto=>?&mr/=->/=;split=>// z;rewrite -memE dom_restr. 
qed.

lemma eager_sample:
  eager [RRO.resample(); , FRO.sample ~ RRO.sample, RRO.resample(); :
         ={x,FRO.m} ==> ={res,FRO.m} ].
proof.
  eager proc.
  case (!mem (dom (FRO.m{2})) x{2}).
  + rcondt{2}2;1:by auto.
    transitivity{2} {
      c <$ sampleto x; FRO.m.[x] <- (c, Unknown);
      Iter(RRO.I).iter(x::elems ((dom (restr Unknown FRO.m)) `\` fset1 x));}
      (={x,FRO.m} /\ ! mem (dom FRO.m{2}) x{2} ==> ={x,FRO.m}) 
      (={x,FRO.m} /\ ! mem (dom FRO.m{2}) x{2} ==> ={x,FRO.m})=>//;last first.
    + inline{2} RRO.resample;call (iter_perm RRO.I iter_perm2);auto=>?&mr[*]2!->?/=?->.
      by rewrite !restr_set/= !dom_set perm_eq_sym perm_to_rem !inE.
    + by move=>?&mr[*]2!->?;exists FRO.m{mr}, x{mr}.
    inline RRO.resample;inline{2}*;rcondt{2}4;1:by auto.
    inline *;wp;swap{1}-2.
    while (={l} /\ FRO.m{2} = (FRO.m.[x <- (c,Unknown)]){1} /\
           (!mem (dom FRO.m) x /\ !mem l x){1}).
    + auto=>?&mr[*]2!->Hd Hl Hnl _/=?->.
      rewrite dom_set !inE set_set (contra _ _ (mem_drop 1 _ _) Hl).
      by move:Hl;rewrite-(mem_head_behead witness l{mr})//negb_or eq_sym=>-[]->.
    auto=>?&mr[*]2!->Hd;rewrite sampleto_ll=>?_/=?->.
    rewrite drop0 set_set_eq restr_set/= -memE dom_set fsetDK;split=>//.
    have^Hx->: !mem (dom (restr Unknown FRO.m{mr})) x{mr} by rewrite dom_restr Hd.
    cut->//: dom (restr Unknown FRO.m{mr}) `\` fset1 x{mr} =
             dom (restr Unknown FRO.m{mr}).
    by rewrite fsetP=>x;rewrite in_fsetD1 /#.
  rcondf{2}2;1:by auto. 
  swap{1}2-1;inline*;auto.
  while (={l,FRO.m} /\ (mem (dom FRO.m) x){1});auto.
  by move=>?&mr[*]2!->Hm Hl _/=?->;rewrite dom_set !inE Hm.
qed.

section.

declare module D:FRO_Distinguisher {FRO}.

lemma eager_D : eager [RRO.resample(); , D(FRO).distinguish ~ 
                       D(RRO).distinguish, RRO.resample(); :
                       ={glob D,FRO.m} ==> ={FRO.m, glob D} /\ ={res} ].
proof.
  eager proc (H_: RRO.resample(); ~ RRO.resample();: ={FRO.m} ==> ={FRO.m})
             (={FRO.m})=>//; try by sim.
  + by apply eager_init. + by apply eager_get. + by apply eager_set. 
  + by apply eager_rem. + by apply eager_sample. 
  + by apply eager_in_dom. + by apply eager_restrK. 
qed.

module Eager (D:FRO_Distinguisher) = {

  proc main1() = {
    var b;
    FRO.init();
    b <@ D(FRO).distinguish();
    return b;
  }

  proc main2() = {
    var b;
    FRO.init();
    b <@ D(RRO).distinguish();
    RRO.resample();
    return b;
  }

}.

equiv Eager_1_2: Eager(D).main1 ~ Eager(D).main2 : 
  ={glob D} ==> ={res,glob FRO, glob D}.
proof.
  proc.
  transitivity{1} 
    { FRO.init(); RRO.resample(); b <@ D(FRO).distinguish(); }
    (={glob D} ==> ={b,FRO.m,glob D})
    (={glob D} ==> ={b,FRO.m,glob D})=> //.
  + by move=> ?&mr->;exists (glob D){mr}.
  + inline *;rcondf{2}3;2:by sim.
    by auto=>?;rewrite restr0 dom0 elems_fset0.
  seq 1 1: (={glob D, FRO.m});1:by inline *;auto.
  by eager call eager_D. 
qed.

end section.

equiv LRO_RRO_init : LRO.init ~ RRO.init : true ==> RO.m{1} = restr Known FRO.m{2}.
proof. by proc;auto=>/=;rewrite restr0. qed.

equiv LRO_RRO_get : LRO.get ~ RRO.get :
   ={x} /\ RO.m{1} = restr Known FRO.m{2} ==> ={res} /\ RO.m{1} = restr Known FRO.m{2}.
proof. 
  proc;auto=>?&ml[]->->/=?->/=.
  rewrite dom_restr negb_and ora_or neqK_eqU.
  rewrite !restr_set/= !getP_eq oget_some;progress.
  by move:H;rewrite negb_or/= restrP in_dom /#. 
qed.

equiv LRO_RRO_set : LRO.set ~ RRO.set :
   ={x,y} /\ RO.m{1} = restr Known FRO.m{2} ==> RO.m{1} = restr Known FRO.m{2}.
proof. by proc;auto=>?&ml[*]3!->;rewrite restr_set. qed.

equiv LRO_RRO_rem : LRO.rem ~ RRO.rem :
   ={x} /\ RO.m{1} = restr Known FRO.m{2} ==> RO.m{1} = restr Known FRO.m{2}.
proof. 
  proc;inline *;auto=>?&mr[*]->->. rewrite restr_rem.
  case (in_dom_with FRO.m{mr} x{mr} Known)=>// Hidw.
  by rewrite rem_id // dom_restr.
qed.

equiv LRO_RRO_sample : LRO.sample ~ RRO.sample:
   ={x} /\ RO.m{1} = restr Known FRO.m{2} ==> RO.m{1} = restr Known FRO.m{2}.
proof. 
  proc;auto=>?&ml[]_->;rewrite sampleto_ll=> ??;rewrite restr_set /==>Hnd. 
  by rewrite rem_id // dom_restr Hnd.
qed.

lemma LRO_RRO_D (D<:RO_Distinguisher{RO,FRO}) : 
  equiv [D(LRO).distinguish ~ D(RRO).distinguish : 
     ={glob D} /\ RO.m{1} = restr Known FRO.m{2} ==>
     ={glob D} /\ RO.m{1} = restr Known FRO.m{2} ].
proof.
  proc (RO.m{1} = restr Known FRO.m{2})=>//.
  + by conseq LRO_RRO_init. + by conseq LRO_RRO_get. + by conseq LRO_RRO_set.
  + by conseq LRO_RRO_rem. + by conseq LRO_RRO_sample. 
qed.

section.

declare module D : RO_Distinguisher{RO,FRO}.

local module M = {
  proc main1() = {
    var b;
    RRO.resample();
    b <@ D(FRO).distinguish();
    return b;
  }
  
  proc main2() = {
    var b;
    b <@ D(RRO).distinguish();
    RRO.resample();
    return b;
  }
}.

lemma RO_LRO_D : 
  equiv [D(RO).distinguish ~ D(LRO).distinguish : 
     ={glob D,RO.m} ==> ={glob D}].
proof.
  transitivity M.main1 
     (={glob D} /\ FRO.m{2} = map (fun _ c => (c,Known)) RO.m{1} ==>
        ={glob D})
     (={glob D} /\ FRO.m{1} = map (fun _ c => (c,Known)) RO.m{2} ==>
        ={glob D})=>//.
  + by move=>?&mr[]2!->;exists (glob D){mr},(map(fun _ c =>(c,Known))RO.m{mr}).
  + proc*;inline M.main1;wp;call (RO_FRO_D D);inline *.
    rcondf{2}2;auto.
    + move=> &mr[]_->;apply mem_eq0=>z;rewrite -memE dom_restr mapP dom_map in_dom.
      by case(RO.m{m}.[_]).
    by move=>?&mr[]2!->/=;rewrite map_comp map_id.
  transitivity M.main2
     (={glob D, FRO.m} ==> ={glob D})
     (={glob D} /\ FRO.m{1} = map (fun _ c => (c,Known)) RO.m{2} ==>
        ={glob D})=>//.
  + by move=>?&mr[]2!->;exists (glob D){mr},(map(fun _ c =>(c,Known))RO.m{mr}).
  + by proc; eager call (eager_D D);auto.
  proc*;inline M.main2;wp;call{1} RRO_resample_ll. 
  symmetry;call (LRO_RRO_D D);auto=> &ml&mr[*]2!->;split=>//=.
  by rewrite fmapP=>x;rewrite restrP mapP;case (RO.m{ml}.[x]).
qed.
