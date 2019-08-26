(* Top-level Proof of SHA-3 Security *)

require import AllCore Distr DList DBool List IntExtra IntDiv Dexcepted DProd SmtMap FSet.
require import Common SLCommon Sponge SHA3_OIndiff.
require (****) SecureORO SecureHash.
(*****) import OIndif.


(* module SHA3 (P : DPRIMITIVE) = { *)
(*   proc init() : unit = {} *)
(*   proc f (bl : bool list, n : int) : bool list = { *)
(*     var r : bool list; *)
(*     r <@ Sponge(P).f(bl ++ [false; true], n); *)
(*     return r; *)
(*   } *)
(* }. *)

op    size_out     : int.
axiom size_out_gt0 : 0 < size_out.

op    sigma     : int = SHA3Indiff.limit.
axiom sigma_ge0 : 0 <= sigma.

op limit : int = sigma.

type  f_out.

op    dout      : f_out distr.
axiom dout_ll   : is_lossless dout.
axiom dout_fu   : is_funiform dout.
axiom dout_full : is_full dout.


op    to_list : f_out -> bool list.
op    of_list : bool list -> f_out option.
axiom spec_dout (l : f_out) : size (to_list l) = size_out.
axiom spec2_dout (l : bool list) : size l = size_out => of_list l <> None.
axiom to_list_inj : injective to_list.
axiom to_listK e l : to_list e = l <=> of_list l = Some e.

axiom dout_equal_dlist : dmap dout to_list = dlist dbool size_out.

lemma doutE1 x : mu1 dout x = inv (2%r ^ size_out).
proof.
cut->:inv (2%r ^ size_out) = mu1 (dlist dbool size_out) (to_list x). 
+ rewrite dlist1E.
  - smt(size_out_gt0).
  rewrite spec_dout/=.
  pose p:= StdBigop.Bigreal.BRM.big _ _ _.
  cut->: p = StdBigop.Bigreal.BRM.big predT (fun _ => inv 2%r) (to_list x).
  - rewrite /p =>{p}. print StdBigop.Bigreal.BRM.
    apply StdBigop.Bigreal.BRM.eq_bigr.
    by move=> i; rewrite//= dbool1E.
  rewrite StdBigop.Bigreal.BRM.big_const count_predT spec_dout=> {p}. search 0 Int.(+) 1 (<=).
  have:=size_out_gt0; move/ltzW.
  move:size_out;apply intind=> //=. 
  - by rewrite powr0 iter0 //= fromint1.
  move=> i hi0 rec.
  by rewrite powrS//iterS// -rec; smt().
rewrite -dout_equal_dlist dmap1E.
apply mu_eq.
by move=> l; rewrite /pred1/(\o); smt(to_listK).
qed.


(* module CSetSize (F : OCONSTRUCTION) (P : ODPRIMITIVE) = { *)
(*   proc init = F(P).init *)
(*   proc f (x : bool list) = { *)
(*     var r, l; *)
(*     r <@ F(P).f(x,size_out); *)
(*     l <- (r <> None) ? of_list (oget r) : None; *)
(*     return l; *)
(*   } *)
(* }. *)

(* module FSetSize (F : OFUNCTIONALITY) = { *)
(*   proc init = F.init *)
(*   proc f (x : bool list) = { *)
(*     var r, l; *)
(*     r <@ F.f(x,size_out); *)
(*     l <- (r <> None) ? of_list (oget r) : None; *)
(*     return l; *)
(*   } *)
(* }. *)

clone import SecureORO as SORO with
  type from   <- bool list,
  type to     <- f_out,

  op sampleto <- dout,
  op bound    <- sigma,
  op increase_counter <- fun c m => c + ((size m + 1) %/ r + 1) +
        max ((size_out + r - 1) %/ r - 1) 0

  proof *. 
realize bound_ge0             by exact(sigma_ge0).
realize sampleto_ll           by exact(dout_ll).
realize sampleto_fu           by exact(dout_fu).
realize sampleto_full         by exact(dout_full).
realize increase_counter_spec by smt(List.size_ge0 divz_ge0 gt0_r).


clone import SecureHash as SH with
  type from   <- bool list,
  type to     <- f_out,
  type block  <- state,
  op sampleto <- dout,
  op bound    <- sigma,
  op increase_counter <- fun c m => c + ((size m + 1) %/ r + 1) +
        max ((size_out + r - 1) %/ r - 1) 0
proof *. 
realize sampleto_ll           by exact(dout_ll).
realize sampleto_fu           by exact(dout_fu).
realize sampleto_full         by exact(dout_full).
realize bound_ge0             by exact(sigma_ge0).
realize increase_counter_spec by smt(List.size_ge0 divz_ge0 gt0_r).


(* module FGetSize (F : ODFUNCTIONALITY) = { *)
(*   proc f (x : bool list, i : int) = { *)
(*     var r; *)
(*     r <@ F.f(x); *)
(*     return to_list r; *)
(*   } *)
(* }. *)

(* module SimSetSize (S : SIMULATOR) (F : Indiff0.DFUNCTIONALITY) = S(FGetSize(F)). *)

(* module DFSetSize (F : DFUNCTIONALITY) = { *)
(*   proc f (x : bool list) = { *)
(*     var r; *)
(*     r <@ F.f(x,size_out); *)
(*     return oget (of_list r); *)
(*   } *)
(* }. *)

(* module (DSetSize (D : Indiff0.DISTINGUISHER) : DISTINGUISHER) *)
(*   (F : DFUNCTIONALITY) (P : DPRIMITIVE) = D(DFSetSize(F),P). *)


module FSetSize (F : OFUNCTIONALITY) : OIndif.OFUNCTIONALITY = {
  proc init = F.init
  proc f (x : bool list) = {
    var y, r;
    y <@ F.f(x,size_out);
    r <- (y <> None) ? of_list (oget y) : None;
    return r;
  }
  proc get = f
}.

module DFSetSize (F : ODFUNCTIONALITY) : OIndif.OFUNCTIONALITY = {
  proc init () = {}
  proc f (x : bool list) = {
    var y, r;
    y <@ F.f(x,size_out);
    r <- (y <> None) ? of_list (oget y) : None;
    return r;
  }
}.

module FIgnoreSize (F : OIndif.ODFUNCTIONALITY) : OFUNCTIONALITY = {
  proc init () = {}
  proc f (x : bool list, i : int) = {
    var y, r;
    y <@ F.f(x);
    return omap to_list r;
  }
}.

module (OSponge : OIndif.OCONSTRUCTION) (P : OIndif.ODPRIMITIVE) = 
  FSetSize(CSome(Sponge,P)).

section Preimage.
(* TODO : stopped here *)

  declare module A : SH.AdvPreimage { Perm, Counter, Bounder, F.RO, F.FRO, 
    Redo, C, Gconcl.S, BlockSponge.BIRO.IRO, BlockSponge.C, BIRO.IRO, 
    Gconcl_list.BIRO2.IRO, Gconcl_list.F2.RO, Gconcl_list.F2.FRO, 
    Gconcl_list.Simulator, SHA3Indiff.Simulator, SHA3Indiff.Cntr, 
    SORO.Bounder, RO.RO }.

  local module FInit (F : OIndif.ODFUNCTIONALITY) : OIndif.OFUNCTIONALITY = {
    proc init () = {}
    proc f = F.f
  }.

  local module PInit (P : ODPRIMITIVE) : OPRIMITIVE = {
    proc init () = {}
    proc f  = P.f
    proc fi = P.fi
  }.


local module OF (F : Oracle) : OIndif.ODFUNCTIONALITY = {
  proc f = F.get
}.


local module Log = {
  var m : (bool list * int, bool) fmap
}.

local module ExtendOutputSize (F : Oracle) : ODFUNCTIONALITY = {
  proc f (x : bool list, k : int) = {
    var o, l, prefix, suffix, i;
    l <- None;
    i <- 0;
    prefix <- [];
    suffix <- [];
    o <@ F.get(x);
    if (o <> None) {
      prefix <- take k (to_list (oget o));
      i <- size_out;
    }
    while (i < k) {
      if ((x,i) \notin Log.m) {
        Log.m.[(x,i)] <$ {0,1};
      }
      suffix <- rcons suffix (oget Log.m.[(x,i)]);
      i <- i + 1;
    }
    l <- Some (prefix ++ suffix);
    return l;
  }
}.

local module OFC2 (F : Oracle) = OFC(ExtendOutputSize(F)).

local module ExtendOutput (F : RF) = {
  proc init () = {
    Log.m <- empty;
    F.init();
  }
  proc f = ExtendOutputSize(F).f
  proc get = f
}.

  local module (Dist_of_P1Adv (A : SH.AdvPreimage) : ODISTINGUISHER) (F : ODFUNCTIONALITY) (P : ODPRIMITIVE) = {
    proc distinguish () = {
      var hash, hash', m;
      Log.m <- empty;
      hash <$ dout;
      m <@ A(DFSetSize(F),P).guess(hash);
      hash' <@ DFSetSize(F).f(m);
      return hash' = Some hash;
    }
  }.
  

local module (SORO_P1 (A : SH.AdvPreimage) : SORO.AdvPreimage) (F : Oracle) = {
  proc guess (h : f_out) : bool list = {
    var mi;
    Log.m <- empty;
    Counter.c <- 0;
    OSimulator(ExtendOutputSize(F)).init();
    mi <@ A(DFSetSize(OFC2(F)),OPC(OSimulator(ExtendOutputSize(F)))).guess(h);
    return mi;
  }
}.

local module RFList = {
  var m : (bool list, f_out) fmap
  proc init () = {
    m <- empty;
  }
  proc get (x : bool list) : f_out option = {
    var z;
    if (x \notin m) {
      z <$ dlist dbool size_out;
      m.[x] <- oget (of_list z);
    }
    return m.[x];
  }
  proc sample (x: bool list) = {}
}.

local module RFWhile = {
  proc init () = {
    RFList.m <- empty;
  }
  proc get (x : bool list) : f_out option = {
    var l, i, b;
    if (x \notin RFList.m) {
      i <- 0;
      l <- [];
      while (i < size_out) {
        b <$ dbool;
        l <- rcons l b;
        i <- i + 1;
      }
      RFList.m.[x] <- oget (of_list l);
    }
    return RFList.m.[x];
  }
  proc sample (x: bool list) = {}
}.

module type TOTO (F : Oracle) = {
  proc main () : bool
}.

clone import Program as PBool with
  type t <- bool,
  op d <- dbool
proof *.


local equiv rw_RF_List_While :
    RFList.get ~ RFWhile.get : 
    ={arg, glob RFList} ==> ={res, glob RFWhile}.
proof.
proc; if; 1, 3: auto; wp.
conseq(:_==> z{1} = l{2})=> />.
transitivity{1} {
    z <@ Sample.sample(size_out);
  }
  (true ==> ={z})
  (true ==> z{1} = l{2})=>/>.
+ by inline*; auto.
transitivity{1} {
    z <@ LoopSnoc.sample(size_out);
  }
  (true ==> ={z})
  (true ==> z{1} = l{2})=>/>; last first.
+ inline*; auto; sim.
  by while(={l, i} /\ n{1} = size_out); auto; smt(cats1).
by call(Sample_LoopSnoc_eq); auto.
qed.


op inv (m1 : (bool list * int, bool) fmap) (m2 : (bool list, f_out) fmap) =
  (forall l i, (l,i) \in m1 => 0 <= i < size_out) /\
  (forall l i, (l,i) \in m1 => l \in m2) /\ 
  (forall l, l \in m2 => forall i, 0 <= i < size_out => (l,i) \in m1) /\ 
  (forall l i, (l,i) \in m1 => m1.[(l,i)] = Some (nth witness (to_list (oget m2.[l])) i)).

local equiv eq_IRO_RFWhile :
  BIRO.IRO.f ~ RFWhile.get :
  arg{1} = (x{2}, size_out) /\ inv BIRO.IRO.mp{1} RFList.m{2}
  ==>
  res{2} = of_list res{1} /\ inv BIRO.IRO.mp{1} RFList.m{2}.
proof.
proc; inline*; sp.
rcondt{1} 1; 1: by auto.
if{2}; sp; last first.
+ alias{1} 1 mp = BIRO.IRO.mp.
  conseq(:_==> BIRO.IRO.mp{1} = mp{1} /\ size bs{1} = i{1} /\ i{1} = size_out /\
        inv mp{1} RFList.m{2} /\
        bs{1} = take i{1} (to_list (oget RFList.m{2}.[x{1}])))=> />.
  - move=> &l &r 11?.
    rewrite take_oversize 1:spec_dout 1:H4 //.
    rewrite eq_sym to_listK => ->.
    by have:=H3; rewrite domE; smt().
  - smt(take_oversize spec_dout).
  while{1}(BIRO.IRO.mp{1} = mp{1} /\ size bs{1} = i{1} /\ 
        0 <= i{1} <= size_out /\ n{1} = size_out /\
        inv mp{1} RFList.m{2} /\ x{1} \in RFList.m{2} /\
        bs{1} = take i{1} (to_list (oget RFList.m{2}.[x{1}])))(size_out - i{1});
      auto=> />.
  + sp; rcondf 1; auto=> />; 1: smt().
    move=> &h 8?.
    rewrite size_rcons //=; do!split; 1, 2, 4: smt(size_ge0).
    rewrite (take_nth witness) 1:spec_dout 1:size_ge0//=. 
    rewrite - H6; congr; rewrite H4=> //=.
    by apply H3=> //=.
  smt(size_out_gt0 size_ge0 take0).
auto=> //=.
conseq(:_==> l{2} = bs{1} /\ size bs{1} = i{1} /\ i{1} = n{1} /\ n{1} = size_out /\
  inv BIRO.IRO.mp{1} RFList.m{2}.[x{2} <- oget (of_list l{2})])=> />. 
+ smt(get_setE spec2_dout).
+ smt(get_setE spec2_dout).
alias{1} 1 m = BIRO.IRO.mp; sp.
conseq(:_==> l{2} = bs{1} /\ size bs{1} = i{1} /\ i{1} = n{1} /\ 
  n{1} = size_out /\ inv m{1} RFList.m{2} /\
  (forall j, (x{1}, j) \in BIRO.IRO.mp{1} => 0 <= j < i{1}) /\
  (forall l j, l <> x{1} => m{1}.[(l,j)] = BIRO.IRO.mp{1}.[(l,j)]) /\
  (forall j, 0 <= j < i{1} => (x{1}, j) \in BIRO.IRO.mp{1}) /\
  (forall j, 0 <= j < i{1} => BIRO.IRO.mp{1}.[(x{1},j)] = Some (nth witness bs{1} j))).
+ move=> /> &l &r 11?; do!split; ..-2 : smt(domE mem_set).
  move=> l j Hin.
  rewrite get_setE/=.
  case: (l = x{r}) => [<<-|].
  - rewrite oget_some H8; 1:smt(); congr; congr.
    by rewrite eq_sym to_listK; smt(spec2_dout).
  move=> Hneq.
  by rewrite -(H6 _ _ Hneq) H2; smt(domE).
while(l{2} = bs{1} /\ size bs{1} = i{1} /\ 0 <= i{1} <= n{1} /\ ={i} /\
  n{1} = size_out /\ inv m{1} RFList.m{2} /\
  (forall j, (x{1}, j) \in BIRO.IRO.mp{1} => 0 <= j < i{1}) /\
  (forall l j, l <> x{1} => m{1}.[(l,j)] = BIRO.IRO.mp{1}.[(l,j)]) /\
  (forall j, 0 <= j < i{1} => (x{1}, j) \in BIRO.IRO.mp{1}) /\
  (forall j, 0 <= j < i{1} => BIRO.IRO.mp{1}.[(x{1},j)] = Some (nth witness bs{1} j))).
+ sp; rcondt{1} 1; auto=> />.
  - smt().
  move=> &l &r 13?.
  rewrite get_setE/=oget_some/=size_rcons/=; do!split; 1,2: smt(size_ge0).
  - smt(mem_set).
  - smt(get_setE).
  - smt(mem_set).
  - move=>j Hj0 Hjsize; rewrite get_setE/=nth_rcons.
    case: (j = size bs{l})=>[->>//=|h].
    have/=Hjs:j < size bs{l} by smt().
    by rewrite Hjs/=H8//=.
by auto; smt(size_out_gt0).
qed.

op eq_extend_size (m1 : (bool list * int, bool) fmap) (m2 : (bool list * int, bool) fmap)
  (m3 : (bool list * int, bool) fmap) =
  (forall x j, 0 <= j < size_out => m1.[(x,j)] = m2.[(x,j)]) /\
  (forall x j, size_out <= j => m1.[(x,j)] = m3.[(x,j)]) /\
  (forall x j, (x,j) \in m1 => 0 <= j).


local equiv eq_extend :
  FSome(BIRO.IRO).f ~ ExtendOutputSize(FSetSize(FSome(BIRO.IRO))).f :
  ={arg} /\ eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2} ==>
  ={res} /\ eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2}.
proof.
proc; inline*; auto; sp.
rcondt{1} 1; auto; rcondt{2} 1; auto.
qed.


local lemma rw_ideal_2 &m:
    Pr[SHA3_OIndiff.OIndif.OIndif(FSome(BIRO.IRO), OSimulator(FSome(BIRO.IRO)), 
      ODRestr(Dist_of_P1Adv(A))).main() @ &m : res] <=
    Pr[SORO.Preimage(SORO_P1(A), RFList).main() @ &m : res].
proof.
have->:Pr[SORO.Preimage(SORO_P1(A), RFList).main() @ &m : res] =
       Pr[SORO.Preimage(SORO_P1(A), RFWhile).main() @ &m : res].
+ byequiv(: ={glob A} ==> _)=>//=; proc.
  swap 1.
  inline{1} 1; inline{2} 1; sp.
  inline{1} 1; inline{2} 1; sp.
  inline{1} 2; inline{2} 2; sp.
  swap[1..2] 3; sp.
  inline{1} 1; inline{2} 1; sp.
  inline{1} 1; inline{2} 1; sp.
  inline{1} 5; inline{2} 5; wp.
  seq 3 3 : (={mi, h, hash, glob A, glob SORO.Bounder, glob RFList}); last first.
  - sp; if; auto; call(rw_RF_List_While); auto.
  call(: ={glob SORO.Bounder, glob RFList, glob OSimulator, glob OPC, glob Log}); auto.
  - proc; sp; if; auto.
    inline{1} 1; inline{2} 1; sp; if; 1, 3: auto; sim.
    if; 1: auto; sim; sp; sim; if; auto=> />; 1: smt(); sim.
    + inline{1} 1; inline{2} 1; sp; sim.
      inline{1} 1; inline{2} 1; sp; if; auto=> />.
      - by call(rw_RF_List_While); auto; smt(). 
      smt().
    smt().
  - by sim. 
  proc; sim; inline{1} 1; inline{2} 1; sp; if; auto.
  inline{1} 1; inline{2} 1; sp; sim.
  inline{1} 1; inline{2} 1; sp; if; auto; sim.
  by call(rw_RF_List_While); auto.
have->:Pr[SHA3_OIndiff.OIndif.OIndif(FSome(BIRO.IRO),
         OSimulator(FSome(BIRO.IRO)),
          ODRestr(Dist_of_P1Adv(A))).main() @ &m : res] =
       Pr[SHA3_OIndiff.OIndif.OIndif(FSome(BIRO.IRO),
         OSimulator(ExtendOutputSize(FSetSize(FSome(BIRO.IRO)))),
         ODRestr(Dist_of_P1Adv(A))).main() @ &m : res].
+ byequiv=> //=; proc; inline*; sp.
  seq 2 2 : (={m, hash, glob OSimulator, glob OFC} /\
         eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2}); last first.
  - sp; if; auto; sp; if; auto.
    while(={i, n, x1, bs} /\ eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2} /\
         n{1} = size_out /\ 0 <= i{1} <= n{1}); auto.
    * by sp; if; auto; smt(domE get_setE). 
    by move=> /> &l &r Heq1 Heq2 Heq3 Hc Hvalid; smt(size_out_gt0).
  call(: ={glob OSimulator, glob OFC} /\
         eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2}); last first; auto.
  + smt(mem_empty).
  + proc; sp; if; auto. 
    inline{1} 1; inline{2} 1; sp; if; 1, 3: auto.
    if; 1, 3: auto; sp.
    if; 1: auto; 1: smt(); last first.
    - by conseq=> />; sim; smt().
    wp=> />; 1: smt().
    rnd; auto=> />; 1: smt().
    call(: eq_extend_size BIRO.IRO.mp{1} BIRO.IRO.mp{2} Log.m{2}); last by auto; smt().

byequiv=> //=; proc.
inline{1} 1; inline{2} 2; sp.
inline{1} 1; inline{2} 3; swap{2}[1..2]1; sp.
inline{1} 1; inline{2} 3; sp.
inline{1} 1; sp.
inline{1} 1; sp.
swap{2} 1 1; sp; swap{2}[1..2]3; sp.
inline{1} 1; sp; auto. print ExtendOutputSize.
seq 2 5 : (={glob A, glob OSimulator, glob Counter, hash, m} /\
         inv BIRO.IRO.mp{1} RFList.m{2} /\
         SORO.Bounder.bounder{2} <= Counter.c{1}); last first.
+ inline{1} 1; inline{2} 1; sp; inline{1} 1; sp; auto.
  if{1}; sp; last first.
  - conseq(:_==> true)=> />.
    inline*; if{2}; auto; sp; if{2}; auto.
    by while{2}(true)(size_out - i{2}); auto=>/>; smt(dbool_ll).
  rcondt{2} 1; 1: by auto=> />; smt(divz_ge0 gt0_r size_ge0).
  inline{1} 1; sp; auto.
  auto; call(eq_IRO_RFWhile); auto.
auto; call(: ={glob OSimulator, glob Counter} /\ inv BIRO.IRO.mp{1} RFList.m{2} /\
        SORO.Bounder.bounder{2} <= Counter.c{1}); auto=> />.
+ smt().
+ proc; sp; if; auto=> />; 2: smt(); inline{1} 1; inline{2} 1; sp; auto.
  if; 1, 3: auto; -1: smt().
  
  (* TODO : reprendre ici, avec le spit des domaines *)


qed.

local lemma rw_ideal &m:
    Pr[SHA3_OIndiff.OIndif.OIndif(FSome(BIRO.IRO), OSimulator(FSome(BIRO.IRO)), 
      ODRestr(Dist_of_P1Adv(A))).main() @ &m : res] <=
    Pr[SORO.Preimage(SORO_P1(A),RF(RO.RO)).main() @ &m : res].
proof.
rewrite (StdOrder.RealOrder.ler_trans _ _ _ (rw_ideal_2 &m)).
byequiv(: ={glob A} ==> _) => //=; proc; inline*; sp; wp.
swap{2} 2; sp; swap{2}[1..2] 6; sp.
swap{1} 2; sp; swap{1}[1..2] 6; sp.
seq 2 2 : (
  Log.m{1} = empty /\
  SHA3Indiff.Simulator.m{1} = empty /\
  SHA3Indiff.Simulator.mi{1} = empty /\
  SHA3Indiff.Simulator.paths{1} = empty.[c0 <- ([], b0)] /\
  Gconcl_list.BIRO2.IRO.mp{1} = empty /\
  SORO.Bounder.bounder{1} = 0 /\
  RFList.m{1} = empty /\
  Counter.c{2} = 0 /\
  ={Log.m, glob SHA3Indiff.Simulator, glob SORO.Bounder, glob Counter} /\
  RO.RO.m{2} = empty /\ ={glob A, h, hash}); 1: auto=> />. 
seq 1 1 : (={glob A, glob SHA3Indiff.Simulator, glob SORO.Bounder, glob Counter, 
    mi, h, hash} /\ RFList.m{1} = RO.RO.m{2}).
+ call(: ={glob SHA3Indiff.Simulator, glob SORO.Bounder, glob Counter} /\ 
    RFList.m{1} = RO.RO.m{2}); auto.
  - admit.
  - admit.    
  - admit.
sp; if; 1, 3: auto; sp; wp 1 2.
if{1}.
+ wp=> />.
  rnd (fun x => oget (of_list x)) to_list; auto=> />.
  move=> &l c Hc Hnin; split.
  - move=> ret Hret. search to_list. 
    by have/= ->:= (to_listK ret (to_list ret)).
  move=> h{h}; split.
  - move=> ret Hret; rewrite -dout_equal_dlist.
    rewrite dmapE /=; apply mu_eq=> //= x /=.
    by rewrite /(\o) /pred1/=; smt(to_list_inj).
  move=> h{h} l Hl. 
  rewrite dout_full /=.
  have:= spec2_dout l.
  have:=supp_dlist dbool size_out l _; 1: smt(size_out_gt0).
  rewrite Hl/==> [#] -> h{h} /= H.
  have H1:=some_oget _ H.
  have:=to_listK (oget (of_list l)) l; rewrite {2}H1/= => -> /= {H H1}.
  by rewrite get_setE/=.
by auto=> />; smt(dout_ll).
qed.


local lemma leq_ideal &m :
    Pr[SHA3_OIndiff.OIndif.OIndif(FSome(BIRO.IRO), OSimulator(FSome(BIRO.IRO)), 
      ODRestr(Dist_of_P1Adv(A))).main() @ &m : res] <= (sigma + 1)%r / 2%r ^ size_out.
proof.
print SORO.RO_is_preimage_resistant. 
have:=rw_ideal &m.
admit.
qed.

  local lemma rw_real &m (A <: SH.AdvPreimage { Perm, Counter, Bounder }): 
      Pr[Preimage(A, OSponge, PSome(Perm)).main() @ &m : res] =
      Pr[SHA3_OIndiff.OIndif.OIndif(FSome(Sponge(Poget(PSome(Perm)))), PSome(Perm), 
        ODRestr(Dist_of_P1Adv(A))).main() @ &m : res].
  proof.
  byequiv=>//=; proc; inline*; sp; wp=> />.
  swap{1} 4; sp. 
  seq 2 2 : (={glob A, glob Perm, hash, m} /\ Bounder.bounder{1} = Counter.c{2}).
  + call(: ={glob Perm} /\ Bounder.bounder{1} = Counter.c{2})=> //=.
    - by proc; inline*; sp; if; auto; 2:sim=> />; 1: smt().
    - by proc; inline*; sp; if; auto; 2:sim=> />; 1: smt().
    - proc; inline*; sp; if; auto; sp=> />.
      by conseq(:_==> ={z0, glob Perm})=> />; sim.
    by auto. 
  by sp; if; auto=>/=; sim; auto.
  qed.

lemma Sponge_preimage_resistant &m:
    (forall (F <: OIndif.ODFUNCTIONALITY) (P <: OIndif.ODPRIMITIVE),
      islossless F.f => islossless P.f => islossless P.fi => islossless A(F,P).guess) =>
    Pr[Preimage(A, OSponge, PSome(Perm)).main() @ &m : res] <=
    (limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r +
    (4 * limit ^ 2)%r / (2 ^ c)%r +
    (sigma + 1)%r / (2%r ^ size_out).
proof.
move=> A_ll.
rewrite (rw_real &m A).
have := SHA3OIndiff (Dist_of_P1Adv(A)) &m _.
+ move=> F P Hp Hpi Hf; proc; inline*; sp; auto; call Hf; auto. 
  call(A_ll (DFSetSize(F)) P _ Hp Hpi); auto.
  - proc; inline*; auto; call Hf; auto.
  smt(dout_ll).
by have/#:=leq_ideal &m.
qed.


(* old proof *)

  declare module A : SH.AdvPreimage{SRO.RO.RO, SRO.RO.FRO, SRO.Bounder, Perm, 
    Gconcl_list.BIRO2.IRO, Simulator, Cntr, BIRO.IRO, F.RO, F.FRO, Redo, C, 
    Gconcl.S, BlockSponge.BIRO.IRO, BlockSponge.C, Gconcl_list.F2.RO,
    Gconcl_list.F2.FRO, Gconcl_list.Simulator, DPre}.

  axiom A_ll (F <: SRO.Oracle) : islossless F.get => islossless A(F).guess.

  local lemma invm_dom_rng (m mi : (state, state) fmap) :
      invm m mi => dom m = rng mi.
  proof. 
  move=>h; rewrite fun_ext=> x; rewrite domE rngE /= eq_iff; have h2 := h x; split.
  + move=> m_x_not_None; exists (oget m.[x]); rewrite -h2; move: m_x_not_None.
    by case: (m.[x]).
  by move=> [] a; rewrite -h2 => ->.
  qed.

  local lemma invmC' (m mi : (state, state) fmap) :
      invm m mi => invm mi m.
  proof. by rewrite /#. qed.

  local lemma invmC (m mi : (state, state) fmap) :
      invm m mi <=> invm mi m.
  proof. by split;exact invmC'. qed.

  local lemma useful m mi a :
      invm m mi => ! a \in m => Distr.is_lossless ((bdistr `*` cdistr) \ rng m).
  proof.
  move=>hinvm nin_dom.
  cut prod_ll:Distr.is_lossless (bdistr `*` cdistr).
  + by rewrite dprod_ll DBlock.dunifin_ll DCapacity.dunifin_ll. 
  apply dexcepted_ll=>//=;rewrite-prod_ll.
  cut->:predT = predU (predC (rng m)) (rng m);1:rewrite predCU//=.
  rewrite Distr.mu_disjoint 1:predCI//=StdRing.RField.addrC. 
  cut/=->:=StdOrder.RealOrder.ltr_add2l (mu (bdistr `*` cdistr) (rng m)) 0%r.
  rewrite Distr.witness_support/predC.
  move:nin_dom;apply absurd=>//=;rewrite negb_exists/==>hyp. 
  cut{hyp}hyp:forall x, rng m x by smt(supp_dprod DBlock.supp_dunifin DCapacity.supp_dunifin). 
  move:a. 
  cut:=eqEcard (fdom m) (frng m);rewrite leq_card_rng_dom/=. 
  cut->//=:fdom m \subset frng m. 
  + by move=> x; rewrite mem_fdom mem_frng hyp.
  smt(mem_fdom mem_frng).
  qed.


  local equiv equiv_sponge_perm c m :
      FInit(CSetSize(Sponge, Perm)).get ~ FInit(DFSetSize(FC(Sponge(Perm)))).get :
    ={arg, glob Perm} /\ invm Perm.m{1} Perm.mi{1} /\ 
      Cntr.c{2} = c /\ arg{2} = m /\
      (Cntr.c + ((size arg + 1) %/ Common.r + 1) + 
      max ((size_out + Common.r - 1) %/ Common.r - 1) 0 <= limit){2} ==>
    ={res, glob Perm} /\ invm Perm.m{1} Perm.mi{1} /\ 
      Cntr.c{2} = c + ((size m + 1) %/ Common.r + 1) + 
      max ((size_out + Common.r - 1) %/ Common.r - 1) 0.
  proof.
  proc; inline FC(Sponge(Perm)).f; sp.
  rcondt{2} 1; auto; sp.
  call(: ={glob Perm} /\ invm Perm.m{1} Perm.mi{1})=>/=; auto; inline*.
  while(={i, n, sa, sc, z, glob Perm} /\ invm Perm.m{1} Perm.mi{1}); auto.
  + sp; if; auto; sp; if; auto; progress.
    rewrite invm_set //=.
    by move:H4; rewrite supp_dexcepted.
  sp; conseq(:_==> ={i, n, sa, sc, glob Perm} /\ invm Perm.m{1} Perm.mi{1}); auto.
  while(={xs, sa, sc, glob Perm} /\ invm Perm.m{1} Perm.mi{1}); auto.
  sp; if; auto; progress. 
  rewrite invm_set=>//=.
  by move:H4; rewrite supp_dexcepted.
  qed.


  op same_ro (m1 : (bool list, f_out) fmap) (m2 : (bool list * int, bool) fmap) =
      (forall m, m \in m1 => forall i, 0 <= i < size_out => (m,i) \in m2)
    && (forall m, (exists i, 0 <= i < size_out /\ (m,i) \in m2) => m \in m1)
    && (forall m, m \in m1 => to_list (oget m1.[m]) = map (fun i => oget m2.[(m,i)]) (range 0 size_out)).

  op same_ro2 (m1 : (bool list, bool list) fmap) (m2 : (bool list * int, bool) fmap) =
      (forall m, m \in m1 => forall i, 0 <= i < size_out => (m,i) \in m2)
    && (forall m, (exists i, 0 <= i < size_out /\ (m,i) \in m2) => m \in m1)
    && (forall m, m \in m1 => oget m1.[m] = map (fun i => oget m2.[(m,i)]) (range 0 size_out)).

  clone import Program as Prog with
    type t <- bool,
    op d <- dbool
    proof *.

  local equiv equiv_ro_iro c m :
    FInit(RO).get ~ FInit(DFSetSize(FC(BIRO.IRO))).get :
    ={arg} /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\
    arg{2} = m /\ Cntr.c{2} = c /\
    (Cntr.c + ((size arg + 1) %/ Common.r + 1) + 
      max ((size_out + Common.r - 1) %/ Common.r - 1) 0 <= limit){2}
    ==> ={res} /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ 
      Cntr.c{2} = c + ((size m + 1) %/ Common.r + 1) + 
      max ((size_out + Common.r - 1) %/ Common.r - 1) 0.
  proof.
  proc; inline *; sp; rcondt{2} 1; 1: auto.
  swap{2} 1 5; sp; wp 2 1.
  conseq(:_==> oget SRO.RO.RO.m{1}.[x{1}] = oget (of_list bs0{2}) /\
    same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); 1:by auto.
  rcondt{2} 1; 1: auto.
  case: (x{1} \in SRO.RO.RO.m{1}).
  + rcondf{1} 2; auto.
    exists* BIRO.IRO.mp{2}; elim* => mp.
    while{2}(bs0{2} = map (fun j => oget BIRO.IRO.mp{2}.[(x0{2},j)]) (range 0 i{2})
        /\ n0{2} = size_out /\ x0{2} \in SRO.RO.RO.m{1} /\ 0 <= i{2} <= size_out
        /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ BIRO.IRO.mp{2} = mp)
      (size_out - i{2}); auto.
    - sp; rcondf 1; auto; 1: smt().
      progress. 
      * have/=<-:= map_rcons (fun (j : int) => oget BIRO.IRO.mp{hr}.[(x0{hr}, j)]) (range 0 i{hr}) i{hr}.
        by rewrite !rangeSr //=.
      * smt().
      * smt().
      * smt().
    progress. 
    - by rewrite range_geq.
    - smt(size_out_gt0).
    - smt().
    - exact(dout_ll).
    - have[] h[#] h1 h2 := H.
      cut->:i_R = size_out by smt().
      cut<-:=h2 _ H3.
      smt(to_listK).
  rcondt{1} 2; 1: auto; wp =>/=.
  exists* BIRO.IRO.mp{2}; elim* => mp.
  conseq(:_==> 
        same_ro SRO.RO.RO.m{1} mp /\ i{2} = size_out /\
        (forall (l,j),  (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
        (forall (l,j),  (l,j) \in mp => BIRO.IRO.mp{2}.[(l,j)] = mp.[(l,j)]) /\
        (forall (l,j), (l,j) \in BIRO.IRO.mp{2} => (l,j) \in mp \/ (l = x0{2} /\ 0 <= j < i{2})) /\
        (forall j, 0 <= j < i{2} => (x0{2},j) \in BIRO.IRO.mp{2}) /\
        take i{2} (to_list r{1}) = bs0{2} /\
        take i{2} (to_list r{1}) = map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})); progress=>//=.
  + by rewrite get_set_sameE /= oget_some; smt(to_listK take_oversize spec_dout).
  + move:H8; rewrite mem_set=>[][]//=h; 1:rewrite H3=>//=.
    - by have []h1 []h2 h3:= H2; have->//:=h1 _ h.
    by move:h => <<-; rewrite H6 //=.
  + rewrite mem_set//=; have[]//=h:= H5 _ _ H11; left.
    have []h1 []->//=:= H2.
    by exists i0=>//=.
  + move:H7; rewrite take_oversize 1:spec_dout//= => H7.
    move:H10; rewrite mem_set. 
    case(m \in SRO.RO.RO.m{1})=>//=h.
    - rewrite get_set_neqE; 1:smt().
      have []h1 []h2 ->//=:= H2. 
      by apply eq_in_map=> j;rewrite mem_range=>[][]hj1 hj2/=; rewrite H4//=h1//=.
    by move=><<-; rewrite get_set_eqE//=.
  alias{1} 1 l = [<:bool>].
  transitivity{1} {
      l <@ Sample.sample(size_out);
      r <- oget (of_list l);
    }
    (={glob SRO.RO.RO, x} ==> ={glob SRO.RO.RO, r})
    (x{1} = x0{2} /\ i{2} = 0 /\ n0{2} = size_out /\ mp = BIRO.IRO.mp{2} /\
      same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ x{1} \notin SRO.RO.RO.m{1} /\
      bs0{2} = []
      ==>
      same_ro SRO.RO.RO.m{1} mp /\ i{2} = size_out /\
      (forall (l,j),  (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
      (forall (l,j),  (l,j) \in mp => BIRO.IRO.mp{2}.[(l,j)] = mp.[(l,j)]) /\
      (forall (l,j), (l,j) \in BIRO.IRO.mp{2} => (l,j) \in mp \/ (l = x0{2} /\ 0 <= j < i{2})) /\
      (forall j, 0 <= j < i{2} => (x0{2},j) \in BIRO.IRO.mp{2}) /\
      take i{2} (to_list r{1}) = bs0{2} /\
      take i{2} (to_list r{1}) = 
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})); 
    progress.
  + smt().
  + inline*; sp; wp. 
    rnd to_list (fun x => oget (of_list x)); auto; progress. 
    - smt(spec_dout supp_dlist to_listK spec2_dout size_out_gt0). 
    - rewrite -dout_equal_dlist dmap1E; apply mu_eq=> x/=. 
      smt(to_listK).
    - rewrite-dout_equal_dlist supp_dmap; smt(dout_full).
    smt(to_listK).
  wp=>/=.
  conseq(:_==> i{2} = size_out /\ size l{1} = size_out /\
      (forall (l0 : bool list) (j : int),
        (l0, j) \in mp => (l0, j) \in BIRO.IRO.mp{2}) /\
      (forall (l0 : bool list) (j : int),
        (l0, j) \in mp => BIRO.IRO.mp{2}.[(l0, j)] = mp.[(l0, j)]) /\
      (forall (l0 : bool list) (j : int),
        (l0, j) \in BIRO.IRO.mp{2} => ((l0, j) \in mp) \/ (l0 = x0{2} /\ 0 <= j < i{2})) /\
      (forall (j : int), 0 <= j < i{2} => (x0{2}, j) \in BIRO.IRO.mp{2}) /\
      take i{2} l{1} = bs0{2} /\
      take i{2} l{1} =
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2}));
    progress.
  + have[]//=h h1:=to_listK (oget (of_list l_L)) l_L; rewrite h1//==> {h1 h}.
    smt(spec2_dout).
  + have[]//=h h1:=to_listK (oget (of_list l_L)) l_L; rewrite h1//==> {h1 h}.
    smt(spec2_dout). 
  transitivity{1} {
      l <@ LoopSnoc.sample(size_out);
    }
    (={glob SRO.RO.RO} ==> ={glob SRO.RO.RO, l})
    (x{1} = x0{2} /\ i{2} = 0 /\ n0{2} = size_out /\ mp = BIRO.IRO.mp{2} /\
      same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ x0{2} \notin SRO.RO.RO.m{1} /\
      bs0{2} = []
      ==>
      i{2} = size_out /\ size l{1} = size_out /\
      (forall (l,j),  (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
      (forall (l,j),  (l,j) \in mp => BIRO.IRO.mp{2}.[(l,j)] = mp.[(l,j)]) /\
      (forall (l,j), (l,j) \in BIRO.IRO.mp{2} => (l,j) \in mp \/ (l = x0{2} /\ 0 <= j < i{2})) /\
      (forall j, 0 <= j < i{2} => (x0{2},j) \in BIRO.IRO.mp{2}) /\
      take i{2} l{1} = bs0{2} /\
      take i{2} l{1} = 
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})); 
    progress.
  + smt(). 
  + by call Sample_LoopSnoc_eq; auto.
  inline*; sp; wp.
  conseq(:_==> i{2} = size_out /\ size l0{1} = i{2} /\ 
      same_ro SRO.RO.RO.m{1} mp /\ x0{2} \notin SRO.RO.RO.m{1} /\
      (forall l j, (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
      (forall l j, (l,j) \in mp => BIRO.IRO.mp{2}.[(l, j)] = mp.[(l, j)]) /\
      (forall l j, (l, j) \in BIRO.IRO.mp{2} => ((l, j) \in mp) \/ (l = x0{2} /\ 0 <= j < i{2})) /\
      (forall j, 0 <= j < i{2} => (x0{2}, j) \in BIRO.IRO.mp{2}) /\
      l0{1} = bs0{2} /\ bs0{2} = 
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})); progress.
  + smt(take_oversize).
  + smt(take_oversize).
  while(0 <= i{2} <= size_out /\ size l0{1} = i{2} /\ n0{2} = size_out /\
      ={i} /\ n{1} = n0{2} /\
      same_ro SRO.RO.RO.m{1} mp /\ x0{2} \notin SRO.RO.RO.m{1} /\
      (forall l j, (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
      (forall l j, (l,j) \in mp => BIRO.IRO.mp{2}.[(l, j)] = mp.[(l, j)]) /\
      (forall l j, (l, j) \in BIRO.IRO.mp{2} => ((l, j) \in mp) \/ (l = x0{2} /\ 0 <= j < i{2})) /\
      (forall j, 0 <= j < i{2} => (x0{2}, j) \in BIRO.IRO.mp{2}) /\
      l0{1} = bs0{2} /\ bs0{2} = 
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})).
  + sp; wp=> //=.
    rcondt{2} 1; 1:auto; progress.
    - have[]h1 [] h2 h3 := H1.
      have:=h2 x0{hr}; rewrite H2/= negb_exists/= =>/(_ (size bs0{hr})).
      rewrite size_ge0 H9/=; apply absurd =>/= h.
      by have //=:= H5 _ _ h.
    rnd; auto; progress.
    - smt(size_ge0).
    - smt().
    - by rewrite size_cat/=.
    - by rewrite mem_set; left; rewrite H3. 
    - rewrite get_setE (H4 _ _ H12).
      cut/#: !(l1, j) = (x0{2}, size bs0{2}).
      move:H2; apply absurd=> //=[#] <<- ->>.
      have[] h1 [] h2 h3 := H1.
      by apply h2; smt().
    - move:H12; rewrite mem_set.
      case((l1, j) \in BIRO.IRO.mp{2})=>//= h; 1: smt().
      by move=> [#] <<- ->> //=; rewrite size_ge0; smt().
    - rewrite mem_set.
      case(j = size bs0{2})=>//=.
      move=> h; rewrite h /=; have {H13} H13 {h} : j < size bs0{2} by smt().
      by apply H6. 
    - by rewrite cats1 get_set_sameE oget_some. 
    - rewrite get_set_sameE oget_some H7 rangeSr.
      rewrite !size_map 1:size_ge0. 
      rewrite (size_map _ (range 0 (size bs0{2}))) size_range /=.
      rewrite max_ler 1:size_ge0 map_rcons /=get_set_sameE oget_some; congr.
      apply eq_in_map=> j.
      rewrite mem_range /==> [] [] hj1 hj2.
      by rewrite get_set_neqE //=; smt().
  auto; progress.
  + smt(size_out_gt0).
  + smt().
  + smt(). 
  + by rewrite range_geq.
  smt().
  qed.

  lemma Sponge_preimage_resistant &m ha :
      (DPre.h{m} = ha) =>
      Pr[SRO.Preimage(A, FM(CSetSize(Sponge), Perm)).main(ha) @ &m : res] <=
      (limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r +
      (4 * limit ^ 2)%r / (2 ^ c)%r +
      (sigma + 1)%r / (2%r ^ size_out).
  proof.
  move=>init_ha.
  rewrite -(doutE1 ha).
  rewrite(preimage_resistant_if_indifferentiable A A_ll (CSetSize(Sponge)) Perm &m ha init_ha).
  exists (SimSetSize(Simulator))=>//=; split.
  + by move=> F _; proc; inline*; auto.
  cut->//:Pr[Indiff0.Indif(CSetSize(Sponge, Perm), Perm, DPre(A)).main() @ &m : res] =
        Pr[RealIndif(Sponge, Perm, DRestr(DSetSize(DPre(A)))).main() @ &m : res].
  + byequiv=>//=; proc. 
    inline DPre(A, CSetSize(Sponge, Perm), Perm).distinguish.
    inline SRO.Preimage(A, FInit(CSetSize(Sponge, Perm))).main.
    inline DRestr(DSetSize(DPre(A)), Sponge(Perm), Perm).distinguish 
          DSetSize(DPre(A), FC(Sponge(Perm)), PC(Perm)).distinguish 
          SRO.Preimage(A, FInit(DFSetSize(FC(Sponge(Perm))))).main.
    inline Perm.init CSetSize(Sponge, Perm).init Sponge(Perm).init 
          FC(Sponge(Perm)).init SRO.Counter.init Cntr.init 
          SRO.Bounder(FInit(CSetSize(Sponge, Perm))).init 
          SRO.Bounder(FInit(DFSetSize(FC(Sponge(Perm))))).init
          FInit(CSetSize(Sponge, Perm)).init 
          FInit(DFSetSize(FC(Sponge(Perm)))).init; sp. 
    wp; sp; sim.
    seq 1 1 : (={m, hash, glob DPre, glob SRO.Counter, glob Perm}
          /\ invm Perm.m{1} Perm.mi{1} /\ DPre.h{1} = ha
          /\ ={c}(SRO.Counter,Cntr)); last first.
    - if; auto; sp.
      exists* m{1}, SRO.Counter.c{1}; elim* => mess c.
      by call(equiv_sponge_perm c mess); auto; smt().
    call(: ={glob SRO.Counter, glob Perm, glob DPre, glob SRO.Bounder}
          /\ DPre.h{1} = ha
          /\ invm Perm.m{1} Perm.mi{1} /\ ={c}(SRO.Counter,Cntr)).
    + proc; sp; if; auto; sp; if; auto; sp.
      exists * x{1}; elim* => m c1 c2 b1 b2.
      by call(equiv_sponge_perm c1 m); auto; smt().
    auto; progress.
    by rewrite /invm=> x y; rewrite 2!emptyE.
  cut->//:Pr[Indiff0.Indif(RO, SimSetSize(Simulator, RO), DPre(A)).main() @ &m : res] =
        Pr[IdealIndif(BIRO.IRO, Simulator, DRestr(DSetSize(DPre(A)))).main() @ &m : res].
  + byequiv=>//=; proc.
    inline Simulator(FGetSize(RO)).init RO.init Simulator(BIRO.IRO).init 
          BIRO.IRO.init Gconcl_list.BIRO2.IRO.init; sp.
    inline DPre(A, RO, Simulator(FGetSize(RO))).distinguish.
    inline DRestr(DSetSize(DPre(A)), BIRO.IRO, Simulator(BIRO.IRO)).distinguish 
          DSetSize(DPre(A), FC(BIRO.IRO), PC(Simulator(BIRO.IRO))).distinguish; wp; sim.
    inline SRO.Bounder(FInit(DFSetSize(FC(BIRO.IRO)))).init 
          SRO.Bounder(FInit(RO)).init SRO.Counter.init FInit(RO).init
          FInit(DFSetSize(FC(BIRO.IRO))).init Cntr.init; sp.
    inline SRO.Preimage(A, FInit(RO)).main 
          SRO.Preimage(A, FInit(DFSetSize(FC(BIRO.IRO)))).main.
    inline SRO.Counter.init SRO.Bounder(FInit(RO)).init 
          SRO.Bounder(FInit(DFSetSize(FC(BIRO.IRO)))).init
          FInit(RO).init FInit(DFSetSize(FC(BIRO.IRO))).init ; sp; sim.
    seq 1 1 : (={m, glob SRO.Counter, glob DPre, hash}
          /\ ={c}(SRO.Counter,Cntr) /\ DPre.h{1} = hash{1}
          /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); last first.
    - if; auto; sp.
      exists * m{1}, SRO.Counter.c{1}; elim* => mess c.
      by call(equiv_ro_iro c mess); auto; smt().
    conseq(:_==> ={m, glob SRO.Counter, glob SRO.Bounder, glob DPre}
          /\ ={c}(SRO.Counter,Cntr)
          /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); progress.
    call(: ={glob SRO.Counter, glob SRO.Bounder, glob DPre}
          /\ ={c}(SRO.Counter,Cntr)
          /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); auto.
    + proc; sp; if; auto; sp; if; auto; sp.
      exists* x{1}; elim* => a c1 c2 b1 b2.
      call(equiv_ro_iro c1 a); auto; smt().
    smt(mem_empty).
  have->//=:= SHA3Indiff (DSetSize(DPre(A))) &m _.
  move=> F P P_f_ll P_fi_ll F_ll; proc; inline*; auto; sp; auto.
  seq 1 : true; auto. 
  + call (A_ll (SRO.Bounder(FInit(DFSetSize(F))))); auto.
    by proc; inline*; sp; if; auto; sp; if; auto; sp; call F_ll; auto.
  if; auto; sp.
  by call F_ll; auto.
  qed.

end section Preimage.



section SecondPreimage.

  declare module A : SRO.AdvSecondPreimage{SRO.RO.RO, SRO.RO.FRO, SRO.Bounder, Perm, 
    Gconcl_list.BIRO2.IRO, Simulator, Cntr, BIRO.IRO, F.RO, F.FRO, Redo, C, 
    Gconcl.S, BlockSponge.BIRO.IRO, BlockSponge.C, Gconcl_list.F2.RO,
    Gconcl_list.F2.FRO, Gconcl_list.Simulator, D2Pre}.

  axiom A_ll (F <: SRO.Oracle) : islossless F.get => islossless A(F).guess.

  local lemma invm_dom_rng (m mi : (state, state) fmap) :
      invm m mi => dom m = rng mi.
  proof. 
  move=>h; rewrite fun_ext=> x; rewrite domE rngE /= eq_iff; have h2 := h x; split.
  + move=> m_x_not_None; exists (oget m.[x]); rewrite -h2; move: m_x_not_None.
    by case: (m.[x]).
  by move=> [] a; rewrite -h2 => ->.
  qed.

  local lemma invmC' (m mi : (state, state) fmap) :
      invm m mi => invm mi m.
  proof. by rewrite /#. qed.

  local lemma invmC (m mi : (state, state) fmap) :
      invm m mi <=> invm mi m.
  proof. by split;exact invmC'. qed.

  local lemma useful m mi a :
      invm m mi => ! a \in m => Distr.is_lossless ((bdistr `*` cdistr) \ rng m).
  proof.
  move=>hinvm nin_dom.
  cut prod_ll:Distr.is_lossless (bdistr `*` cdistr).
  + by rewrite dprod_ll DBlock.dunifin_ll DCapacity.dunifin_ll. 
  apply dexcepted_ll=>//=;rewrite-prod_ll.
  cut->:predT = predU (predC (rng m)) (rng m);1:rewrite predCU//=.
  rewrite Distr.mu_disjoint 1:predCI//=StdRing.RField.addrC. 
  cut/=->:=StdOrder.RealOrder.ltr_add2l (mu (bdistr `*` cdistr) (rng m)) 0%r.
  rewrite Distr.witness_support/predC.
  move:nin_dom;apply absurd=>//=;rewrite negb_exists/==>hyp. 
  cut{hyp}hyp:forall x, rng m x by smt(supp_dprod DBlock.supp_dunifin DCapacity.supp_dunifin). 
  move:a. 
  cut:=eqEcard (fdom m) (frng m);rewrite leq_card_rng_dom/=. 
  cut->//=:fdom m \subset frng m. 
  + by move=> x; rewrite mem_fdom mem_frng hyp.
  smt(mem_fdom mem_frng).
  qed.


  local equiv equiv_sponge_perm c m :
      FInit(CSetSize(Sponge, Perm)).get ~ FInit(DFSetSize(FC(Sponge(Perm)))).get :
    ={arg, glob Perm} /\ invm Perm.m{1} Perm.mi{1} /\ 
      Cntr.c{2} = c /\ arg{2} = m /\
      (Cntr.c + ((size arg + 1) %/ Common.r + 1) + 
      max ((size_out + Common.r - 1) %/ Common.r - 1) 0 <= limit){2} ==>
    ={res, glob Perm} /\ invm Perm.m{1} Perm.mi{1} /\ 
      Cntr.c{2} = c + ((size m + 1) %/ Common.r + 1) + 
      max ((size_out + Common.r - 1) %/ Common.r - 1) 0.
  proof.
  proc; inline FC(Sponge(Perm)).f; sp.
  rcondt{2} 1; auto; sp.
  call(: ={glob Perm} /\ invm Perm.m{1} Perm.mi{1})=>/=; auto; inline*.
  while(={i, n, sa, sc, z, glob Perm} /\ invm Perm.m{1} Perm.mi{1}); auto.
  + sp; if; auto; sp; if; auto; progress.
    rewrite invm_set //=.
    by move:H4; rewrite supp_dexcepted.
  sp; conseq(:_==> ={i, n, sa, sc, glob Perm} /\ invm Perm.m{1} Perm.mi{1}); auto.
  while(={xs, sa, sc, glob Perm} /\ invm Perm.m{1} Perm.mi{1}); auto.
  sp; if; auto; progress. 
  rewrite invm_set=>//=.
  by move:H4; rewrite supp_dexcepted.
  qed.


  clone import Program as Prog2 with
    type t <- bool,
    op d <- dbool
    proof *.

  local equiv equiv_ro_iro c m :
    FInit(RO).get ~ FInit(DFSetSize(FC(BIRO.IRO))).get :
    ={arg} /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\
    arg{2} = m /\ Cntr.c{2} = c /\
    (Cntr.c + ((size arg + 1) %/ Common.r + 1) + 
      max ((size_out + Common.r - 1) %/ Common.r - 1) 0 <= limit){2}
    ==> ={res} /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ 
      Cntr.c{2} = c + ((size m + 1) %/ Common.r + 1) + 
      max ((size_out + Common.r - 1) %/ Common.r - 1) 0.
  proof.
  proc; inline *; sp; rcondt{2} 1; 1: auto.
  swap{2} 1 5; sp; wp 2 1.
  conseq(:_==> oget SRO.RO.RO.m{1}.[x{1}] = oget (of_list bs0{2}) /\
    same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); 1:by auto.
  rcondt{2} 1; 1: auto.
  case: (x{1} \in SRO.RO.RO.m{1}).
  + rcondf{1} 2; auto.
    exists* BIRO.IRO.mp{2}; elim* => mp.
    while{2}(bs0{2} = map (fun j => oget BIRO.IRO.mp{2}.[(x0{2},j)]) (range 0 i{2})
        /\ n0{2} = size_out /\ x0{2} \in SRO.RO.RO.m{1} /\ 0 <= i{2} <= size_out
        /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ BIRO.IRO.mp{2} = mp)
      (size_out - i{2}); auto.
    - sp; rcondf 1; auto; 1: smt().
      progress. 
      * have/=<-:= map_rcons (fun (j : int) => oget BIRO.IRO.mp{hr}.[(x0{hr}, j)]) (range 0 i{hr}) i{hr}.
        by rewrite !rangeSr //=.
      * smt().
      * smt().
      * smt().
    progress. 
    - by rewrite range_geq.
    - smt(size_out_gt0).
    - smt().
    - exact(dout_ll).
    - have[] h[#] h1 h2 := H.
      cut->:i_R = size_out by smt().
      cut<-:=h2 _ H3.
      smt(to_listK).
  rcondt{1} 2; 1: auto; wp =>/=.
  exists* BIRO.IRO.mp{2}; elim* => mp.
  conseq(:_==> 
        same_ro SRO.RO.RO.m{1} mp /\ i{2} = size_out /\
        (forall (l,j),  (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
        (forall (l,j),  (l,j) \in mp => BIRO.IRO.mp{2}.[(l,j)] = mp.[(l,j)]) /\
        (forall (l,j), (l,j) \in BIRO.IRO.mp{2} => (l,j) \in mp \/ (l = x0{2} /\ 0 <= j < i{2})) /\
        (forall j, 0 <= j < i{2} => (x0{2},j) \in BIRO.IRO.mp{2}) /\
        take i{2} (to_list r{1}) = bs0{2} /\
        take i{2} (to_list r{1}) = map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})); progress=>//=.
  + by rewrite get_set_sameE /= oget_some; smt(to_listK take_oversize spec_dout).
  + move:H8; rewrite mem_set=>[][]//=h; 1:rewrite H3=>//=.
    - by have []h1 []h2 h3:= H2; have->//:=h1 _ h.
    by move:h => <<-; rewrite H6 //=.
  + rewrite mem_set//=; have[]//=h:= H5 _ _ H11; left.
    have []h1 []->//=:= H2.
    by exists i0=>//=.
  + move:H7; rewrite take_oversize 1:spec_dout//= => H7.
    move:H10; rewrite mem_set. 
    case(m \in SRO.RO.RO.m{1})=>//=h.
    - rewrite get_set_neqE; 1:smt().
      have []h1 []h2 ->//=:= H2. 
      by apply eq_in_map=> j;rewrite mem_range=>[][]hj1 hj2/=; rewrite H4//=h1//=.
    by move=><<-; rewrite get_set_eqE//=.
  alias{1} 1 l = [<:bool>].
  transitivity{1} {
      l <@ Sample.sample(size_out);
      r <- oget (of_list l);
    }
    (={glob SRO.RO.RO, x} ==> ={glob SRO.RO.RO, r})
    (x{1} = x0{2} /\ i{2} = 0 /\ n0{2} = size_out /\ mp = BIRO.IRO.mp{2} /\
      same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ x{1} \notin SRO.RO.RO.m{1} /\
      bs0{2} = []
      ==>
      same_ro SRO.RO.RO.m{1} mp /\ i{2} = size_out /\
      (forall (l,j),  (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
      (forall (l,j),  (l,j) \in mp => BIRO.IRO.mp{2}.[(l,j)] = mp.[(l,j)]) /\
      (forall (l,j), (l,j) \in BIRO.IRO.mp{2} => (l,j) \in mp \/ (l = x0{2} /\ 0 <= j < i{2})) /\
      (forall j, 0 <= j < i{2} => (x0{2},j) \in BIRO.IRO.mp{2}) /\
      take i{2} (to_list r{1}) = bs0{2} /\
      take i{2} (to_list r{1}) = 
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})); 
    progress.
  + smt().
  + inline*; sp; wp. 
    rnd to_list (fun x => oget (of_list x)); auto; progress. 
    - smt(spec_dout supp_dlist to_listK spec2_dout size_out_gt0).
    - rewrite -dout_equal_dlist dmap1E; apply mu_eq=> x/=. 
      smt(to_listK).
    - rewrite-dout_equal_dlist supp_dmap; smt(dout_full).
    smt(to_listK).
  wp=>/=.
  conseq(:_==> i{2} = size_out /\ size l{1} = size_out /\
      (forall (l0 : bool list) (j : int),
        (l0, j) \in mp => (l0, j) \in BIRO.IRO.mp{2}) /\
      (forall (l0 : bool list) (j : int),
        (l0, j) \in mp => BIRO.IRO.mp{2}.[(l0, j)] = mp.[(l0, j)]) /\
      (forall (l0 : bool list) (j : int),
        (l0, j) \in BIRO.IRO.mp{2} => ((l0, j) \in mp) \/ (l0 = x0{2} /\ 0 <= j < i{2})) /\
      (forall (j : int), 0 <= j < i{2} => (x0{2}, j) \in BIRO.IRO.mp{2}) /\
      take i{2} l{1} = bs0{2} /\
      take i{2} l{1} =
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2}));
    progress.
  + have[]//=h h1:=to_listK (oget (of_list l_L)) l_L; rewrite h1//==> {h1 h}.
    smt(spec2_dout).
  + have[]//=h h1:=to_listK (oget (of_list l_L)) l_L; rewrite h1//==> {h1 h}.
    smt(spec2_dout).
  transitivity{1} {
      l <@ LoopSnoc.sample(size_out);
    }
    (={glob SRO.RO.RO} ==> ={glob SRO.RO.RO, l})
    (x{1} = x0{2} /\ i{2} = 0 /\ n0{2} = size_out /\ mp = BIRO.IRO.mp{2} /\
      same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ x0{2} \notin SRO.RO.RO.m{1} /\
      bs0{2} = []
      ==>
      i{2} = size_out /\ size l{1} = size_out /\
      (forall (l,j),  (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
      (forall (l,j),  (l,j) \in mp => BIRO.IRO.mp{2}.[(l,j)] = mp.[(l,j)]) /\
      (forall (l,j), (l,j) \in BIRO.IRO.mp{2} => (l,j) \in mp \/ (l = x0{2} /\ 0 <= j < i{2})) /\
      (forall j, 0 <= j < i{2} => (x0{2},j) \in BIRO.IRO.mp{2}) /\
      take i{2} l{1} = bs0{2} /\
      take i{2} l{1} = 
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})); 
    progress.
  + smt(). 
  + by call Sample_LoopSnoc_eq; auto.
  inline*; sp; wp.
  conseq(:_==> i{2} = size_out /\ size l0{1} = i{2} /\ 
      same_ro SRO.RO.RO.m{1} mp /\ x0{2} \notin SRO.RO.RO.m{1} /\
      (forall l j, (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
      (forall l j, (l,j) \in mp => BIRO.IRO.mp{2}.[(l, j)] = mp.[(l, j)]) /\
      (forall l j, (l, j) \in BIRO.IRO.mp{2} => ((l, j) \in mp) \/ (l = x0{2} /\ 0 <= j < i{2})) /\
      (forall j, 0 <= j < i{2} => (x0{2}, j) \in BIRO.IRO.mp{2}) /\
      l0{1} = bs0{2} /\ bs0{2} = 
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})); progress.
  + smt(take_oversize).
  + smt(take_oversize).
  while(0 <= i{2} <= size_out /\ size l0{1} = i{2} /\ n0{2} = size_out /\
      ={i} /\ n{1} = n0{2} /\
      same_ro SRO.RO.RO.m{1} mp /\ x0{2} \notin SRO.RO.RO.m{1} /\
      (forall l j, (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
      (forall l j, (l,j) \in mp => BIRO.IRO.mp{2}.[(l, j)] = mp.[(l, j)]) /\
      (forall l j, (l, j) \in BIRO.IRO.mp{2} => ((l, j) \in mp) \/ (l = x0{2} /\ 0 <= j < i{2})) /\
      (forall j, 0 <= j < i{2} => (x0{2}, j) \in BIRO.IRO.mp{2}) /\
      l0{1} = bs0{2} /\ bs0{2} = 
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})).
  + sp; wp=> //=.
    rcondt{2} 1; 1:auto; progress.
    - have[]h1 [] h2 h3 := H1.
      have:=h2 x0{hr}; rewrite H2/= negb_exists/= =>/(_ (size bs0{hr})).
      rewrite size_ge0 H9/=; apply absurd =>/= h.
      by have //=:= H5 _ _ h.
    rnd; auto; progress.
    - smt(size_ge0).
    - smt().
    - by rewrite size_cat/=.
    - by rewrite mem_set; left; rewrite H3. 
    - rewrite get_setE (H4 _ _ H12).
      cut/#: !(l1, j) = (x0{2}, size bs0{2}).
      move:H2; apply absurd=> //=[#] <<- ->>.
      have[] h1 [] h2 h3 := H1.
      by apply h2; smt().
    - move:H12; rewrite mem_set.
      case((l1, j) \in BIRO.IRO.mp{2})=>//= h; 1: smt().
      by move=> [#] <<- ->> //=; rewrite size_ge0; smt().
    - rewrite mem_set.
      case(j = size bs0{2})=>//=.
      move=> h; rewrite h /=; have {H13} H13 {h} : j < size bs0{2} by smt().
      by apply H6. 
    - by rewrite cats1 get_set_sameE oget_some. 
    - rewrite get_set_sameE oget_some H7 rangeSr.
      rewrite !size_map 1:size_ge0. 
      rewrite (size_map _ (range 0 (size bs0{2}))) size_range /=.
      rewrite max_ler 1:size_ge0 map_rcons /=get_set_sameE oget_some; congr.
      apply eq_in_map=> j.
      rewrite mem_range /==> [] [] hj1 hj2.
      by rewrite get_set_neqE //=; smt().
  auto; progress.
  + smt(size_out_gt0).
  + smt().
  + smt(). 
  + by rewrite range_geq.
  smt().
  qed.

  lemma Sponge_second_preimage_resistant &m mess :
      (D2Pre.m2{m} = mess) =>
      Pr[SRO.SecondPreimage(A, FM(CSetSize(Sponge), Perm)).main(mess) @ &m : res] <=
      (limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r +
      (4 * limit ^ 2)%r / (2 ^ c)%r +
      (sigma + 1)%r / (2%r ^ size_out).
  proof.  
  move=> init_mess.
  rewrite -(doutE1 witness).
  rewrite(second_preimage_resistant_if_indifferentiable A A_ll (CSetSize(Sponge)) Perm &m mess init_mess).
  exists (SimSetSize(Simulator)); split.
  + by move=> F _; proc; inline*; auto.
  cut->:Pr[Indiff0.Indif(CSetSize(Sponge, Perm), Perm, D2Pre(A)).main() @ &m : res] =
        Pr[RealIndif(Sponge, Perm, DRestr(DSetSize(D2Pre(A)))).main() @ &m : res].
  + byequiv=>//=; proc. 
    inline Perm.init CSetSize(Sponge, Perm).init Sponge(Perm).init 
          FC(Sponge(Perm)).init; sp.
    inline D2Pre(A, CSetSize(Sponge, Perm), Perm).distinguish.
    inline DRestr(DSetSize(D2Pre(A)), Sponge(Perm), Perm).distinguish 
          DSetSize(D2Pre(A), FC(Sponge(Perm)), PC(Perm)).distinguish Cntr.init.
    inline SRO.SecondPreimage(A, FInit(CSetSize(Sponge, Perm))).main
        SRO.SecondPreimage(A, FInit(DFSetSize(FC(Sponge(Perm))))).main.
    inline SRO.Bounder(FInit(CSetSize(Sponge, Perm))).init
          SRO.Bounder(FInit(DFSetSize(FC(Sponge(Perm))))).init 
          SRO.Counter.init FInit(DFSetSize(FC(Sponge(Perm)))).init
          FInit(CSetSize(Sponge, Perm)).init.
    wp; sp; sim. 
    seq 1 1 : (={m1, m2, glob SRO.Counter, glob Perm}
          /\ invm Perm.m{1} Perm.mi{1}
          /\ ={c}(SRO.Counter,Cntr)); last first.
    - if; auto; sp.
      case(SRO.Counter.c{1} + ((size m2{1} + 1) %/ r + 1) + 
          max ((size_out + r - 1) %/ r - 1) 0 < limit); last first.
      * rcondf{1} 2; 1: by auto; inline*; auto; conseq(: _ ==> true); auto.
        rcondf{2} 2; 1: by auto; inline*; auto; conseq(: _ ==> true); auto.
        auto; inline*; auto; sp; conseq(: _ ==> true); auto.
        if{2}; sp; auto; sim.
        while{1}(invm Perm.m{1} Perm.mi{1}) (((size_out + r - 1) %/ r)-i{1}).
        + auto; sp; if; auto. 
          - sp; if ;auto; progress.
            * exact (useful _ _ _ H H2).
            * rewrite invm_set=>//=. 
              by move:H4; rewrite  supp_dexcepted.
            * smt().
            smt().
          smt().
        conseq(:_==> invm Perm.m{1} Perm.mi{1}); 1:smt().
        while{1}(invm Perm.m{1} Perm.mi{1})(size xs{1}).
        + move=> _ z; auto; sp; if; auto; progress.
          * exact (useful _ _ _ H H1).
          * rewrite invm_set=>//=.
            by move:H3; rewrite supp_dexcepted.
          * smt().
          smt().
        auto; smt(size_ge0 size_eq0).
      rcondt{1} 2; first by auto; inline*; auto; conseq(:_==> true); auto.
      rcondt{2} 2; first by auto; inline*; auto; conseq(:_==> true); auto.
      sim.
      exists* m1{1}, m2{1}; elim* => a1 a2 c1 c2.
      call (equiv_sponge_perm (c2 + ((size a1 + 1) %/ r + 1) + max ((size_out + r - 1) %/ r - 1) 0) a2).
      auto; call (equiv_sponge_perm c2 a1); auto; progress. 
      smt(List.size_ge0 divz_ge0 gt0_r).
      smt(List.size_ge0 divz_ge0 gt0_r).
    call(: ={glob SRO.Counter, glob Perm, glob SRO.Bounder}
          /\ invm Perm.m{1} Perm.mi{1} /\ ={c}(SRO.Counter,Cntr)).
    + proc; sp; if; auto; sp; if; auto; sp.
      exists * x{1}; elim* => m c1 c2 b1 b2.
      by call(equiv_sponge_perm c1 m); auto; smt().
    inline*; auto; progress.
    by rewrite /invm=> x y; rewrite 2!emptyE.
  cut->:Pr[Indiff0.Indif(RO, SimSetSize(Simulator, RO), D2Pre(A)).main() @ &m : res] =
        Pr[IdealIndif(BIRO.IRO, Simulator, DRestr(DSetSize(D2Pre(A)))).main() @ &m : res].
  + byequiv=>//=; proc.
    inline Simulator(FGetSize(RO)).init RO.init Simulator(BIRO.IRO).init 
          BIRO.IRO.init Gconcl_list.BIRO2.IRO.init; sp.
    inline D2Pre(A, RO, Simulator(FGetSize(RO))).distinguish.
    inline DRestr(DSetSize(D2Pre(A)), BIRO.IRO, Simulator(BIRO.IRO)).distinguish 
          DSetSize(D2Pre(A), FC(BIRO.IRO), PC(Simulator(BIRO.IRO))).distinguish; wp; sim.
    inline SRO.Bounder(FInit(DFSetSize(FC(BIRO.IRO)))).init 
          SRO.Bounder(FInit(RO)).init SRO.Counter.init FInit(RO).init
          FInit(DFSetSize(FC(BIRO.IRO))).init Cntr.init; sp.
    inline SRO.SecondPreimage(A, FInit(RO)).main 
          SRO.SecondPreimage(A, FInit(DFSetSize(FC(BIRO.IRO)))).main.
    inline SRO.Bounder(FInit(RO)).init 
          SRO.Bounder(FInit(DFSetSize(FC(BIRO.IRO)))).init SRO.Counter.init
          FInit(RO).init FInit(DFSetSize(FC(BIRO.IRO))).init.
    sp; sim.
    seq 1 1 : (={m1, m2, glob SRO.Counter}
          /\ ={c}(SRO.Counter,Cntr)
          /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); last first.
    - if; auto; sp.
      case: (SRO.Counter.c{1} + ((size m2{1} + 1) %/ r + 1) + 
          max ((size_out + r - 1) %/ r - 1) 0 < limit); last first. 
      * rcondf{1} 2; first by auto; inline*; auto.
        rcondf{2} 2; first auto; inline*; auto; sp.
        + rcondt 1; first by auto; smt().
          by sp; rcondt 1; auto; conseq(:_==> true); auto.
        inline*;sp; auto.
        rcondt{2} 1; first by auto; smt().
        conseq(:_==> true); first smt(dout_ll).
        sp; rcondt{2} 1; auto; conseq(:_==> true); auto.
        by while{2}(true)(n0{2}-i{2}); auto; 1:(sp; if; auto); smt(dbool_ll).
      rcondt{1} 2; first by auto; inline*; auto.
      rcondt{2} 2; first auto; inline*; auto; sp.
      + rcondt 1; first by auto; smt().
        by sp; rcondt 1; auto; conseq(:_==> true); auto.
      sim.
      exists* m1{1}, m2{1}; elim*=> a1 a2 c1 c2.
      call(equiv_ro_iro (c2 + ((size a1 + 1) %/ r + 1) + 
          max ((size_out + r - 1) %/ r - 1) 0) a2).
      auto; call(equiv_ro_iro c2 a1); auto; smt().
    call(: ={glob SRO.Counter, glob SRO.Bounder} /\ ={c}(SRO.Counter,Cntr)
          /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); auto.
    + proc; sp; if; auto; sp; if; auto; sp.
      exists* x{1}; elim* => a c1 c2 b1 b2.
      call(equiv_ro_iro c1 a); auto; smt().
    smt(mem_empty). 
  have->//=:= SHA3Indiff (DSetSize(D2Pre(A))) &m _.
  move=> F P P_f_ll P_fi_ll F_ll; proc; inline*; auto; sp.
  seq 1 : true; auto.
  + call (A_ll (SRO.Bounder(FInit(DFSetSize(F))))); auto.
    by proc; inline*; sp; if; auto; sp; if; auto; sp; call F_ll; auto.
  if; auto; sp.
  seq 1 : true; auto.
  + by call F_ll; auto.
  sp; if; auto; sp; call F_ll; auto.
  qed.

end section SecondPreimage.



section Collision.

  declare module A : SRO.AdvCollision{SRO.RO.RO, SRO.RO.FRO, SRO.Bounder, Perm, 
    Gconcl_list.BIRO2.IRO, Simulator, Cntr, BIRO.IRO, F.RO, F.FRO, Redo, C, 
    Gconcl.S, BlockSponge.BIRO.IRO, BlockSponge.C, Gconcl_list.F2.RO,
    Gconcl_list.F2.FRO, Gconcl_list.Simulator}.

  axiom A_ll (F <: SRO.Oracle) : islossless F.get => islossless A(F).guess.

  local lemma invm_dom_rng (m mi : (state, state) fmap) :
      invm m mi => dom m = rng mi.
  proof. 
  move=>h; rewrite fun_ext=> x; rewrite domE rngE /= eq_iff; have h2 := h x; split.
  + move=> m_x_not_None; exists (oget m.[x]); rewrite -h2; move: m_x_not_None.
    by case: (m.[x]).
  by move=> [] a; rewrite -h2 => ->.
  qed.

  local lemma invmC' (m mi : (state, state) fmap) :
      invm m mi => invm mi m.
  proof. by rewrite /#. qed.

  local lemma invmC (m mi : (state, state) fmap) :
      invm m mi <=> invm mi m.
  proof. by split;exact invmC'. qed.

  local lemma useful m mi a :
      invm m mi => ! a \in m => Distr.is_lossless ((bdistr `*` cdistr) \ rng m).
  proof.
  move=>hinvm nin_dom.
  cut prod_ll:Distr.is_lossless (bdistr `*` cdistr).
  + by rewrite dprod_ll DBlock.dunifin_ll DCapacity.dunifin_ll. 
  apply dexcepted_ll=>//=;rewrite-prod_ll.
  cut->:predT = predU (predC (rng m)) (rng m);1:rewrite predCU//=.
  rewrite Distr.mu_disjoint 1:predCI//=StdRing.RField.addrC. 
  cut/=->:=StdOrder.RealOrder.ltr_add2l (mu (bdistr `*` cdistr) (rng m)) 0%r.
  rewrite Distr.witness_support/predC.
  move:nin_dom;apply absurd=>//=;rewrite negb_exists/==>hyp. 
  cut{hyp}hyp:forall x, rng m x by smt(supp_dprod DBlock.supp_dunifin DCapacity.supp_dunifin). 
  move:a. 
  cut:=eqEcard (fdom m) (frng m);rewrite leq_card_rng_dom/=. 
  cut->//=:fdom m \subset frng m. 
  + by move=> x; rewrite mem_fdom mem_frng hyp.
  smt(mem_fdom mem_frng).
  qed.


  local equiv equiv_sponge_perm c m :
      FInit(CSetSize(Sponge, Perm)).get ~ FInit(DFSetSize(FC(Sponge(Perm)))).get :
    ={arg, glob Perm} /\ invm Perm.m{1} Perm.mi{1} /\ 
      Cntr.c{2} = c /\ arg{2} = m /\
      (Cntr.c + ((size arg + 1) %/ Common.r + 1) + 
      max ((size_out + Common.r - 1) %/ Common.r - 1) 0 <= limit){2} ==>
    ={res, glob Perm} /\ invm Perm.m{1} Perm.mi{1} /\ 
      Cntr.c{2} = c + ((size m + 1) %/ Common.r + 1) + 
      max ((size_out + Common.r - 1) %/ Common.r - 1) 0.
  proof.
  proc; inline FC(Sponge(Perm)).f; sp.
  rcondt{2} 1; auto; sp.
  call(: ={glob Perm} /\ invm Perm.m{1} Perm.mi{1})=>/=; auto; inline*.
  while(={i, n, sa, sc, z, glob Perm} /\ invm Perm.m{1} Perm.mi{1}); auto.
  + sp; if; auto; sp; if; auto; progress.
    rewrite invm_set //=.
    by move:H4; rewrite supp_dexcepted.
  sp; conseq(:_==> ={i, n, sa, sc, glob Perm} /\ invm Perm.m{1} Perm.mi{1}); auto.
  while(={xs, sa, sc, glob Perm} /\ invm Perm.m{1} Perm.mi{1}); auto.
  sp; if; auto; progress. 
  rewrite invm_set=>//=.
  by move:H4; rewrite supp_dexcepted.
  qed.

  clone import Program as Prog3 with
    type t <- bool,
    op d <- dbool
    proof *.

  local equiv equiv_ro_iro c m :
    FInit(RO).get ~ FInit(DFSetSize(FC(BIRO.IRO))).get :
    ={arg} /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\
    arg{2} = m /\ Cntr.c{2} = c /\
    (Cntr.c + ((size arg + 1) %/ Common.r + 1) + 
      max ((size_out + Common.r - 1) %/ Common.r - 1) 0 <= limit){2}
    ==> ={res} /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ 
      Cntr.c{2} = c + ((size m + 1) %/ Common.r + 1) + 
      max ((size_out + Common.r - 1) %/ Common.r - 1) 0.
  proof.
  proc; inline *; sp; rcondt{2} 1; 1: auto.
  swap{2} 1 5; sp; wp 2 1.
  conseq(:_==> oget SRO.RO.RO.m{1}.[x{1}] = oget (of_list bs0{2}) /\
    same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); 1:by auto.
  rcondt{2} 1; 1: auto.
  case: (x{1} \in SRO.RO.RO.m{1}).
  + rcondf{1} 2; auto.
    exists* BIRO.IRO.mp{2}; elim* => mp.
    while{2}(bs0{2} = map (fun j => oget BIRO.IRO.mp{2}.[(x0{2},j)]) (range 0 i{2})
        /\ n0{2} = size_out /\ x0{2} \in SRO.RO.RO.m{1} /\ 0 <= i{2} <= size_out
        /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ BIRO.IRO.mp{2} = mp)
      (size_out - i{2}); auto.
    - sp; rcondf 1; auto; 1: smt().
      progress. 
      * have/=<-:= map_rcons (fun (j : int) => oget BIRO.IRO.mp{hr}.[(x0{hr}, j)]) (range 0 i{hr}) i{hr}.
        by rewrite !rangeSr //=.
      * smt().
      * smt().
      * smt().
    progress. 
    - by rewrite range_geq.
    - smt(size_out_gt0).
    - smt().
    - exact(dout_ll).
    - have[] h[#] h1 h2 := H.
      cut->:i_R = size_out by smt().
      cut<-:=h2 _ H3.
      smt(to_listK).
  rcondt{1} 2; 1: auto; wp =>/=.
  exists* BIRO.IRO.mp{2}; elim* => mp.
  conseq(:_==> 
        same_ro SRO.RO.RO.m{1} mp /\ i{2} = size_out /\
        (forall (l,j),  (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
        (forall (l,j),  (l,j) \in mp => BIRO.IRO.mp{2}.[(l,j)] = mp.[(l,j)]) /\
        (forall (l,j), (l,j) \in BIRO.IRO.mp{2} => (l,j) \in mp \/ (l = x0{2} /\ 0 <= j < i{2})) /\
        (forall j, 0 <= j < i{2} => (x0{2},j) \in BIRO.IRO.mp{2}) /\
        take i{2} (to_list r{1}) = bs0{2} /\
        take i{2} (to_list r{1}) = map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})); progress=>//=.
  + by rewrite get_set_sameE /= oget_some; smt(to_listK take_oversize spec_dout).
  + move:H8; rewrite mem_set=>[][]//=h; 1:rewrite H3=>//=.
    - by have []h1 []h2 h3:= H2; have->//:=h1 _ h.
    by move:h => <<-; rewrite H6 //=.
  + rewrite mem_set //=; have [] //= h:= H5 _ _ H11; left.
    have []h1 []->//=:= H2.
    by exists i0=>//=.
  + move:H7; rewrite take_oversize 1:spec_dout//= => H7.
    move:H10; rewrite mem_set. 
    case(m \in SRO.RO.RO.m{1})=>//=h.
    - rewrite get_set_neqE; 1:smt().
      have []h1 []h2 ->//=:= H2. 
      by apply eq_in_map=> j;rewrite mem_range=>[][]hj1 hj2/=; rewrite H4//=h1//=.
    by move=><<-; rewrite get_set_eqE//=.
  alias{1} 1 l = [<:bool>].
  transitivity{1} {
      l <@ Sample.sample(size_out);
      r <- oget (of_list l);
    }
    (={glob SRO.RO.RO, x} ==> ={glob SRO.RO.RO, r})
    (x{1} = x0{2} /\ i{2} = 0 /\ n0{2} = size_out /\ mp = BIRO.IRO.mp{2} /\
      same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ x{1} \notin SRO.RO.RO.m{1} /\
      bs0{2} = []
      ==>
      same_ro SRO.RO.RO.m{1} mp /\ i{2} = size_out /\
      (forall (l,j),  (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
      (forall (l,j),  (l,j) \in mp => BIRO.IRO.mp{2}.[(l,j)] = mp.[(l,j)]) /\
      (forall (l,j), (l,j) \in BIRO.IRO.mp{2} => (l,j) \in mp \/ (l = x0{2} /\ 0 <= j < i{2})) /\
      (forall j, 0 <= j < i{2} => (x0{2},j) \in BIRO.IRO.mp{2}) /\
      take i{2} (to_list r{1}) = bs0{2} /\
      take i{2} (to_list r{1}) = 
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})); 
    progress.
  + smt().
  + inline*; sp; wp. 
    rnd to_list (fun x => oget (of_list x)); auto; progress. 
    - smt(spec_dout supp_dlist to_listK spec2_dout size_out_gt0). 
    - rewrite -dout_equal_dlist dmap1E; apply mu_eq=> x/=. 
      smt(to_listK).
    - rewrite-dout_equal_dlist supp_dmap; smt(dout_full).
    smt(to_listK).
  wp=>/=.
  conseq(:_==> i{2} = size_out /\ size l{1} = size_out /\
      (forall (l0 : bool list) (j : int),
        (l0, j) \in mp => (l0, j) \in BIRO.IRO.mp{2}) /\
      (forall (l0 : bool list) (j : int),
        (l0, j) \in mp => BIRO.IRO.mp{2}.[(l0, j)] = mp.[(l0, j)]) /\
      (forall (l0 : bool list) (j : int),
        (l0, j) \in BIRO.IRO.mp{2} => ((l0, j) \in mp) \/ (l0 = x0{2} /\ 0 <= j < i{2})) /\
      (forall (j : int), 0 <= j < i{2} => (x0{2}, j) \in BIRO.IRO.mp{2}) /\
      take i{2} l{1} = bs0{2} /\
      take i{2} l{1} =
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2}));
    progress.
  + have[]//=h h1:=to_listK (oget (of_list l_L)) l_L; rewrite h1//==> {h1 h}.
    smt(spec2_dout).
  + have[]//=h h1:=to_listK (oget (of_list l_L)) l_L; rewrite h1//==> {h1 h}.
    smt(spec2_dout). 
  transitivity{1} {
      l <@ LoopSnoc.sample(size_out);
    }
    (={glob SRO.RO.RO} ==> ={glob SRO.RO.RO, l})
    (x{1} = x0{2} /\ i{2} = 0 /\ n0{2} = size_out /\ mp = BIRO.IRO.mp{2} /\
      same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2} /\ x0{2} \notin SRO.RO.RO.m{1} /\
      bs0{2} = []
      ==>
      i{2} = size_out /\ size l{1} = size_out /\
      (forall (l,j),  (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
      (forall (l,j),  (l,j) \in mp => BIRO.IRO.mp{2}.[(l,j)] = mp.[(l,j)]) /\
      (forall (l,j), (l,j) \in BIRO.IRO.mp{2} => (l,j) \in mp \/ (l = x0{2} /\ 0 <= j < i{2})) /\
      (forall j, 0 <= j < i{2} => (x0{2},j) \in BIRO.IRO.mp{2}) /\
      take i{2} l{1} = bs0{2} /\
      take i{2} l{1} = 
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})); 
    progress.
  + smt(). 
  + by call Sample_LoopSnoc_eq; auto.
  inline*; sp; wp.
  conseq(:_==> i{2} = size_out /\ size l0{1} = i{2} /\ 
      same_ro SRO.RO.RO.m{1} mp /\ x0{2} \notin SRO.RO.RO.m{1} /\
      (forall l j, (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
      (forall l j, (l,j) \in mp => BIRO.IRO.mp{2}.[(l, j)] = mp.[(l, j)]) /\
      (forall l j, (l, j) \in BIRO.IRO.mp{2} => ((l, j) \in mp) \/ (l = x0{2} /\ 0 <= j < i{2})) /\
      (forall j, 0 <= j < i{2} => (x0{2}, j) \in BIRO.IRO.mp{2}) /\
      l0{1} = bs0{2} /\ bs0{2} = 
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})); progress.
  + smt(take_oversize).
  + smt(take_oversize).
  while(0 <= i{2} <= size_out /\ size l0{1} = i{2} /\ n0{2} = size_out /\
      ={i} /\ n{1} = n0{2} /\
      same_ro SRO.RO.RO.m{1} mp /\ x0{2} \notin SRO.RO.RO.m{1} /\
      (forall l j, (l,j) \in mp => (l,j) \in BIRO.IRO.mp{2}) /\
      (forall l j, (l,j) \in mp => BIRO.IRO.mp{2}.[(l, j)] = mp.[(l, j)]) /\
      (forall l j, (l, j) \in BIRO.IRO.mp{2} => ((l, j) \in mp) \/ (l = x0{2} /\ 0 <= j < i{2})) /\
      (forall j, 0 <= j < i{2} => (x0{2}, j) \in BIRO.IRO.mp{2}) /\
      l0{1} = bs0{2} /\ bs0{2} = 
        map (fun (j : int) => oget BIRO.IRO.mp{2}.[(x0{2}, j)]) (range 0 i{2})).
  + sp; wp=> //=.
    rcondt{2} 1; 1:auto; progress.
    - have[]h1 [] h2 h3 := H1.
      have:=h2 x0{hr}; rewrite H2/= negb_exists/= =>/(_ (size bs0{hr})).
      rewrite size_ge0 H9/=; apply absurd =>/= h.
      by have //=:= H5 _ _ h.
    rnd; auto; progress.
    - smt(size_ge0).
    - smt().
    - by rewrite size_cat/=.
    - by rewrite mem_set; left; rewrite H3. 
    - rewrite get_setE (H4 _ _ H12).
      cut/#: !(l1, j) = (x0{2}, size bs0{2}).
      move:H2; apply absurd=> //=[#] <<- ->>.
      have[] h1 [] h2 h3 := H1.
      by apply h2; smt().
    - move:H12; rewrite mem_set.
      case((l1, j) \in BIRO.IRO.mp{2})=>//= h; 1: smt().
      by move=> [#] <<- ->> //=; rewrite size_ge0; smt().
    - rewrite mem_set.
      case(j = size bs0{2})=>//=.
      move=> h; rewrite h /=; have {H13} H13 {h} : j < size bs0{2} by smt().
      by apply H6. 
    - by rewrite cats1 get_set_sameE oget_some. 
    - rewrite get_set_sameE oget_some H7 rangeSr.
      rewrite !size_map 1:size_ge0. 
      rewrite (size_map _ (range 0 (size bs0{2}))) size_range /=.
      rewrite max_ler 1:size_ge0 map_rcons /=get_set_sameE oget_some; congr.
      apply eq_in_map=> j.
      rewrite mem_range /==> [] [] hj1 hj2.
      by rewrite get_set_neqE //=; smt().
  auto; progress.
  + smt(size_out_gt0).
  + smt().
  + smt(). 
  + by rewrite range_geq.
  smt().
  qed.

  lemma Sponge_coll_resistant &m :
      Pr[SRO.Collision(A, FM(CSetSize(Sponge), Perm)).main() @ &m : res] <=
      (limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r +
      (4 * limit ^ 2)%r / (2 ^ c)%r +
      (sigma * (sigma - 1) + 2)%r / 2%r / (2%r ^ size_out).
  proof. 
  rewrite -(doutE1 witness).
  rewrite (coll_resistant_if_indifferentiable A A_ll (CSetSize(Sponge)) Perm &m).
  exists (SimSetSize(Simulator)); split.
  + by move=> F _; proc; inline*; auto.
  cut->:Pr[Indiff0.Indif(CSetSize(Sponge, Perm), Perm, DColl(A)).main() @ &m : res] =
        Pr[RealIndif(Sponge, Perm, DRestr(DSetSize(DColl(A)))).main() @ &m : res].
  + byequiv=>//=; proc. 
    inline Perm.init CSetSize(Sponge, Perm).init Sponge(Perm).init 
          FC(Sponge(Perm)).init; sp.
    inline DColl(A, CSetSize(Sponge, Perm), Perm).distinguish.
    inline DRestr(DSetSize(DColl(A)), Sponge(Perm), Perm).distinguish 
          DSetSize(DColl(A), FC(Sponge(Perm)), PC(Perm)).distinguish Cntr.init; wp; sp; sim. 
    seq 2 2 : (={m1, m2, glob SRO.Counter, glob Perm}
          /\ invm Perm.m{1} Perm.mi{1}
          /\ ={c}(SRO.Counter,Cntr)); last first.
    - if; auto; sp.
      case(SRO.Counter.c{1} + ((size m2{1} + 1) %/ r + 1) + 
          max ((size_out + r - 1) %/ r - 1) 0 < limit); last first.
      * rcondf{1} 2; 1: by auto; inline*; auto; conseq(: _ ==> true); auto.
        rcondf{2} 2; 1: by auto; inline*; auto; conseq(: _ ==> true); auto.
        auto; inline*; auto; sp; conseq(: _ ==> true); auto.
        if{2}; sp; auto; sim.
        while{1}(invm Perm.m{1} Perm.mi{1}) (((size_out + r - 1) %/ r)-i{1}).
        + auto; sp; if; auto. 
          - sp; if ;auto; progress.
            * exact (useful _ _ _ H H2).
            * rewrite invm_set=>//=. 
              by move:H4; rewrite  supp_dexcepted.
            * smt().
            smt().
          smt().
        conseq(:_==> invm Perm.m{1} Perm.mi{1}); 1:smt().
        while{1}(invm Perm.m{1} Perm.mi{1})(size xs{1}).
        + move=> _ z; auto; sp; if; auto; progress.
          * exact (useful _ _ _ H H1).
          * rewrite invm_set=>//=.
            by move:H3; rewrite supp_dexcepted.
          * smt().
          smt().
        auto; smt(size_ge0 size_eq0).
      rcondt{1} 2; first by auto; inline*; auto; conseq(:_==> true); auto.
      rcondt{2} 2; first by auto; inline*; auto; conseq(:_==> true); auto.
      sim.
      exists* m1{1}, m2{1}; elim* => a1 a2 c1 c2.
      call (equiv_sponge_perm (c2 + ((size a1 + 1) %/ r + 1) + max ((size_out + r - 1) %/ r - 1) 0) a2).
      auto; call (equiv_sponge_perm c2 a1); auto; progress. 
      smt(List.size_ge0 divz_ge0 gt0_r).
      smt(List.size_ge0 divz_ge0 gt0_r).
    call(: ={glob SRO.Counter, glob Perm, glob SRO.Bounder}
          /\ invm Perm.m{1} Perm.mi{1} /\ ={c}(SRO.Counter,Cntr)).
    + proc; sp; if; auto; sp; if; auto; sp.
      exists * x{1}; elim* => m c1 c2 b1 b2.
      by call(equiv_sponge_perm c1 m); auto; smt().
    inline*; auto; progress.
    by rewrite /invm=> x y; rewrite 2!emptyE.
  cut->:Pr[Indiff0.Indif(RO, SimSetSize(Simulator, RO), DColl(A)).main() @ &m : res] =
        Pr[IdealIndif(BIRO.IRO, Simulator, DRestr(DSetSize(DColl(A)))).main() @ &m : res].
  + byequiv=>//=; proc.
    inline Simulator(FGetSize(RO)).init RO.init Simulator(BIRO.IRO).init 
          BIRO.IRO.init Gconcl_list.BIRO2.IRO.init; sp.
    inline DColl(A, RO, Simulator(FGetSize(RO))).distinguish.
    inline DRestr(DSetSize(DColl(A)), BIRO.IRO, Simulator(BIRO.IRO)).distinguish 
          DSetSize(DColl(A), FC(BIRO.IRO), PC(Simulator(BIRO.IRO))).distinguish; wp; sim.
    inline SRO.Bounder(FInit(DFSetSize(FC(BIRO.IRO)))).init 
          SRO.Bounder(FInit(RO)).init SRO.Counter.init FInit(RO).init
          FInit(DFSetSize(FC(BIRO.IRO))).init Cntr.init; sp.
    seq 1 1 : (={m1, m2, glob SRO.Counter}
          /\ ={c}(SRO.Counter,Cntr)
          /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); last first.
    - if; auto; sp.
      case: (SRO.Counter.c{1} + ((size m2{1} + 1) %/ r + 1) + 
          max ((size_out + r - 1) %/ r - 1) 0 < limit); last first. 
      * rcondf{1} 2; first by auto; inline*; auto.
        rcondf{2} 2; first auto; inline*; auto; sp.
        + rcondt 1; first by auto; smt().
          by sp; rcondt 1; auto; conseq(:_==> true); auto.
        inline*;sp; auto.
        rcondt{2} 1; first by auto; smt().
        conseq(:_==> true); first smt(dout_ll).
        sp; rcondt{2} 1; auto; conseq(:_==> true); auto.
        by while{2}(true)(n0{2}-i{2}); auto; 1:(sp; if; auto); smt(dbool_ll).
      rcondt{1} 2; first by auto; inline*; auto.
      rcondt{2} 2; first auto; inline*; auto; sp.
      + rcondt 1; first by auto; smt().
        by sp; rcondt 1; auto; conseq(:_==> true); auto.
      sim.
      exists* m1{1}, m2{1}; elim*=> a1 a2 c1 c2.
      call(equiv_ro_iro (c2 + ((size a1 + 1) %/ r + 1) + 
          max ((size_out + r - 1) %/ r - 1) 0) a2).
      auto; call(equiv_ro_iro c2 a1); auto; smt().
    call(: ={glob SRO.Counter, glob SRO.Bounder} /\ ={c}(SRO.Counter,Cntr)
          /\ same_ro SRO.RO.RO.m{1} BIRO.IRO.mp{2}); auto.
    + proc; sp; if; auto; sp; if; auto; sp.
      exists* x{1}; elim* => a c1 c2 b1 b2.
      call(equiv_ro_iro c1 a); auto; smt().
    smt(mem_empty). 
  have->//=:= SHA3Indiff (DSetSize(DColl(A))) &m _.
  move=> F P P_f_ll P_fi_ll F_ll; proc; inline*; auto; sp.
  seq 1 : true; auto.
  + call (A_ll (SRO.Bounder(FInit(DFSetSize(F))))); auto.
    by proc; inline*; sp; if; auto; sp; if; auto; sp; call F_ll; auto.
  if; auto; sp.
  seq 1 : true; auto.
  + by call F_ll; auto.
  sp; if; auto; sp; call F_ll; auto.
  qed.

end section Collision.

module X (F : SRO.Oracle) = {
  proc get (bl : bool list) = {
  var r;
  r <@ F.get(bl ++ [ false ; true ]);
  return r;
  }
}.

module AdvCollisionSHA3 (A : SRO.AdvCollision) (F : SRO.Oracle) = {
  proc guess () = {
    var m1, m2;
    (m1, m2) <@ A(X(F)).guess();
    return (m1 ++ [ false ; true ], m2 ++ [ false ; true ]);
  }
}.

section SHA3_Collision.

  declare module A : SRO.AdvCollision{SRO.RO.RO, SRO.RO.FRO, SRO.Bounder, Perm, 
    Gconcl_list.BIRO2.IRO, Simulator, Cntr, BIRO.IRO, F.RO, F.FRO, Redo, C, 
    Gconcl.S, BlockSponge.BIRO.IRO, BlockSponge.C, Gconcl_list.F2.RO,
    Gconcl_list.F2.FRO, Gconcl_list.Simulator}.

  axiom A_ll (F <: SRO.Oracle) : islossless F.get => islossless A(F).guess.

  lemma SHA3_coll_resistant &m :
      Pr[SRO.Collision(AdvCollisionSHA3(A), FM(CSetSize(Sponge), Perm)).main() @ &m : res] <=
      (limit ^ 2 - limit)%r / (2 ^ (r + c + 1))%r +
      (4 * limit ^ 2)%r / (2 ^ c)%r +
      (sigma * (sigma - 1) + 2)%r / 2%r / (2%r ^ size_out).
  proof.
  apply (Sponge_coll_resistant (AdvCollisionSHA3(A)) _ &m).
  by move=> F F_ll; proc; inline*; call(A_ll (X(F))); auto; proc; call F_ll; auto.
  qed.


end section Collision.