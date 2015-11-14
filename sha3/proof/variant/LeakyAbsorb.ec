(* -------------------------------------------------------------------- *)
require import Option Pair Int Real Distr List FSet NewFMap.
require (*--*) LazyRP RndOrcl. 
(*---*) import Dprod.

(* -------------------------------------------------------------------- *)

type block.    (* = {0,1}^r *)
type capacity. (* = {0,1}^c *)

op cdist : capacity distr.
op bdist : block distr.
axiom bdist_ll : weight bdist = 1%r.

(* isomorphic to the {0,1}^? uniform distributions *)

op b0 : block.
op c0 : capacity.

op (^) : block -> block -> block.

(* -------------------------------------------------------------------- *)
clone import LazyRP as Perm with
  type D <- block * capacity,
  op   d <- bdist * cdist

  rename [module] "P" as "Perm".


(* -------------------------------------------------------------------- *)
module type WeirdIRO = {
  proc init(): unit

  proc f(_: block list * int): block list
}.

module type WeirdIRO_ = {
  proc f(_: block list * int): block list
}.

op valid_query : block list -> int -> bool.
op valid_queries : (block list) fset.
axiom valid_queryP     : forall m n, valid_query m n => forall k, 0 <= k <= n => mem valid_queries (m ++ mkseq (fun x => b0) k).
axiom valid_query_take : forall m n, valid_query m n => forall i, 0 <= i <= size m => mem valid_queries (take i m).
axiom valid_query_take1 : 
  forall m n, valid_query m n => forall i, 0 <= i <= size m => valid_query (take i m) 1.
axiom valid_query_size : forall m n, valid_query m n => 1 <= size m.

module type RO = {
  proc init () : unit
  proc f(_:block list) : block 
}.

module Ro = {
  var h : (block list,block) fmap

  proc init() = { h = map0; }

  proc f(m : block list) = {
    var r;
    r <$ bdist;
    if (!mem (dom h) m) h.[m] <- r ;
    return oget h.[m];
  }
}.

module GenIdealFunctionalityThatDoesNotAbsorb(Ro:RO) = {
  proc init = Ro.init

  proc f(m : block list, n : int) = {
    var i <- 1;
    var j <- 1;
    var z <- [];
    var b <- b0;

    if (valid_query m n) {
      while (j <= size m) {
        z <- rcons z b;
        b <@ Ro.f(take j m);
        j <- j + 1;
      }
      while (i < n) {
        z <- rcons z b;
        m <- rcons m b0;
        b <@ Ro.f(m);
        i <- i + 1;
      }
    }
    return z;
  }
}.

module IdealFunctionalityThatDoesNotAbsorb = GenIdealFunctionalityThatDoesNotAbsorb(Ro).

module GenIdealFunctionalityThatAbsorbs(Ro:RO) = {
  proc init = Ro.init 

  proc f(m : block list, n : int) = {
    var i <- 1;
    var z <- [];
    var b;

    if (valid_query m n) {
      b <@ Ro.f(m);
      while (i < n) {
        z <- rcons z b;
        m <- rcons m b0;
        b <@ Ro.f(m);
        i<- i + 1;
      }
    }
    return z;
  }
}.

module IdealFunctionalityThatAbsorbs = GenIdealFunctionalityThatAbsorbs(Ro).

(* -------------------------------------------------------------------- *)
module type CONSTRUCTION(P : RP) = {
  proc init() : unit

  proc f(bp : block list, n : int) : block list
}.

module type SIMULATOR(F : WeirdIRO_) = {
  proc init() : unit

  proc f(_ : block * capacity) : block * capacity

  proc fi(_ : block * capacity) : block * capacity
}.

module type DISTINGUISHER(F : WeirdIRO_, P : RP_) = {
  proc distinguish() : bool 
}.

(* -------------------------------------------------------------------- *)
module Experiment(F : WeirdIRO, P : RP, D : DISTINGUISHER) = {
  proc main() : bool = {
    var b;
    
    F.init();
    P.init();
    b <@ D(F, P).distinguish();

    return b;
  }
}.

(* -------------------------------------------------------------------- *)
module SpongeThatDoesNotAbsorb (P : RP) : WeirdIRO, CONSTRUCTION(P) = {
  proc init () = { }

  proc f(p : block list, n : int): block list = {
    var z       <- [];
    var (sa,sc) <- (b0, c0);
    var i       <- 0;
    var l       <- size p;

    if (valid_query p n) {
      (* Absorption *)
      while (p <> []) {
        z       <- rcons z sa;
        (sa,sc) <@ P.f(sa ^ head b0 p, sc);
        p       <- behead p;
      }
      (* Squeezing *)
      while (i < n) {
        z       <- rcons z sa;
        (sa,sc) <@ P.f(sa,sc);
      }
    }

    return z;
  }
}.

module SpongeThatAbsorbs (P : RP) : WeirdIRO, CONSTRUCTION(P) = {
  proc init () = {} 

  proc f(p : block list, n : int): block list = {
    var z       <- [];
    var (sa,sc) <- (b0, c0);
    var i       <- 0;

    if (valid_query p n) {
      (* Absorption *)
      while (p <> []) {
        (sa,sc) <@ P.f(sa ^ head b0 p, sc);
        p       <- behead p;
      }
      (* Squeezing *)
      while (i < n) {
        z       <- rcons z sa;
        (sa,sc) <@ P.f(sa,sc);
      }
    }

    return z;
  }
}.

(* -------------------------------------------------------------------- *)
section PROOF.
  declare module S:SIMULATOR     { IdealFunctionalityThatDoesNotAbsorb }.
  declare module D:DISTINGUISHER { Perm, IdealFunctionalityThatDoesNotAbsorb, S }.

  (* From DoNot to Absorb *)

  module MkF(F:WeirdIRO_) = {
    proc f(m:block list, n:int) = {
      var r = [];
      if (valid_query m n) {
        r <@ F.f(m,n);
        r <- drop (size m) r;
      }
      return r;
    }
  }.

  (* From Absord to do Not *)
  module MkD (D:DISTINGUISHER, F:WeirdIRO_, P:RP_) = D(MkF(F),P).

  module MkFdoNot1 (F:WeirdIRO_) = {
    proc f(m:block list, n:int) : block list = {
      var i, r, tl, b;
      r <- [];
      if (valid_query m n) {
        i <- 1;
        b <- [b0]; 
        while (i <= size m) {
          r <- r ++ b;
          b <- F.f(take i m, 1);
          i <- i + 1;

        }
        tl <- F.f(m,n);
        r  <- r ++ tl;
      }
      return r;
    }
  }.

  module MkFdoNot (F:WeirdIRO) = {
    proc init = F.init
    proc f = MkFdoNot1(F).f
  }.

  module MkS(S:SIMULATOR, F:WeirdIRO) = S(MkFdoNot(F)).

  local clone RndOrcl as RndOrcl0 with 
    type from <- block list, 
    type to   <- block.
  
  local clone RndOrcl0.RestrIdeal as RI with
    op sample <- fun (bl:block list) => bdist,
    op test   <- (mem valid_queries),
    op univ   <- valid_queries,
    op dfl    <- b0
    proof *.
  realize sample_ll. by move=> _;apply bdist_ll. qed.
  realize testP. by []. qed.
  import RI.

  local module E1 (Ro:RO) = {
    module F = { 
      proc f = GenIdealFunctionalityThatDoesNotAbsorb(Ro).f
    }
    module P = S(F)
    proc distinguish () : bool = {
      var b;
      P.init();
      b <@  MkD(D, F, P).distinguish();
      return b;
    }
  }.

  local module E2 (Ro:RO) = {
    module F = { 
      proc f = GenIdealFunctionalityThatAbsorbs(Ro).f
    }
    module P = S(MkFdoNot1(F)) 
    proc distinguish () : bool = {
      var b;
      P.init();
      b <@  D(F, P).distinguish();
      return b;
    }
  }.

  local equiv f_f : 
    GenIdealFunctionalityThatDoesNotAbsorb(Ro).f ~ E1(Restr(RO)).F.f : 
    ={m, n} /\ Ro.h{1} = RO.m{2} ==> ={res} /\ Ro.h{1} = RO.m{2}.
  proof.
    proc;sp;if => //.
    inline{2} Restr(RO).f.
    while (={z,i,n,b,m} /\ Ro.h{1} = RO.m{2} /\ 
              (forall k, 0 <= k <= n - i => mem valid_queries (m ++ map (fun x => b0) (iota_ 0 k))){2}).
    + rcondt{2} 5=> //. 
      + auto;progress; rewrite - cats1;cut := H 1 _; [by smt| by rewrite iota1].  
      auto; call (_:Ro.h{1} = RO.m{2});[by sim | auto;progress].
      cut := H (k+1) _;1:by smt.
      rewrite iotaS //= -cats1 -catA /= (_:  map (fun (x : int) => b0) (iota_ 1 k) = map (fun (x : int) => b0) (iota_ 0 k)) //.
      by rewrite (iota_addl 1 0 k) -map_comp;apply eq_map.
    while (={z,j,n,b,m} /\ Ro.h{1} = RO.m{2} /\ valid_query m{1} n{1} /\ 0 <= j{1}).
    + rcondt{2} 4=> //. 
      + auto;progress;apply (valid_query_take _ _ H)=> //.
      auto; call (_:Ro.h{1} = RO.m{2});[by sim | auto;progress;smt].
    skip;progress;apply (valid_queryP _ _ H2);smt.
  qed.

  local equiv f_f_a :  GenIdealFunctionalityThatAbsorbs(Ro).f ~ E2(Restr(RO)).F.f : ={m,n} /\ Ro.h{1} = RO.m{2} ==> ={res} /\ Ro.h{1} = RO.m{2}. 
  proof.
    proc; sp;if=> //;inline{2} Restr(RO).f;sp.
    rcondt{2} 1=> //.
    + auto;progress;cut := valid_query_take _ _ H (size m{hr}).
      rewrite take_size=> HH;apply HH;smt.
    while (={z,i,n,b,m} /\ Ro.h{1} = RO.m{2} /\ 
                (forall k, 0 <= k <= n - i => mem valid_queries (m ++ map (fun x => b0) (iota_ 0 k))){2}).
    + rcondt{2} 5=> //. 
      + auto;progress; rewrite -cats1;cut := H 1 _; [by smt| by rewrite iota1].  
      auto; call (_:Ro.h{1} = RO.m{2});[by sim | auto;progress].
      cut := H (k+1) _;1:by smt.
      rewrite iotaS //= -cats1 -catA /= (_:  map (fun (x : int) => b0) (iota_ 1 k) = map (fun (x : int) => b0) (iota_ 0 k)) //.
      by rewrite (iota_addl 1 0 k) -map_comp;apply eq_map.
    wp;call (_:Ro.h{1} = RO.m{2});[by sim | auto;progress]. 
    apply (valid_queryP _ _ H);smt.
  qed.

  local equiv f_f' : 
    MkFdoNot(GenIdealFunctionalityThatAbsorbs(Ro)).f ~ MkFdoNot1(E2(Restr(RO)).F).f :
    ={m, n} /\ Ro.h{1} = RO.m{2} ==>
    ={res} /\ Ro.h{1} = RO.m{2}.
  proof.
    proc;sp;if => //;wp.
    call f_f_a. 
    while (={i,m,r,b} /\ Ro.h{1} = RO.m{2} /\ valid_query m{1} n{1} /\ 0 <= i{1});last by auto.
    wp; call f_f_a;auto;progress;smt.
  qed.
 
  local equiv f_dN : E1(ERO).F.f ~ MkFdoNot1(E2(ERO).F).f : ={m, n} /\ ={RO.m} ==> ={res, RO.m}.
  proof.
    proc;sp;if=> //;sp.
    inline {2} E2(ERO).F.f.
    rcondt{2} 6;auto; 1: by conseq (_: _ ==> true).
    while (={RO.m} /\ z{1} = r{2} ++ z0{2} /\ i{1} = i1{2} /\ n{1} = n1{2} /\ b{1} = b1{2} /\
           m{1} = m1{2}).
    + inline *;auto;progress;smt. 
    inline ERO.f;auto.
    while (={RO.m,m,n} /\ z{1} = r{2} /\ b{2} = [b{1}] /\ valid_query m{1} n{1} /\ 
           j{1} = i{2} /\ 0 <= i{2} /\
           (1 < j => b =  mem valid_queries (take j m) ? oget RO.m.[x]  : Self.b0){1}).
    + rcondt{2} 6;1:by auto;progress;smt. 
      rcondf{2} 8;1:by auto.
      auto;progress;smt.
    auto;progress;smt. 
  qed.

  lemma conclusion &m:
    `| Pr[Experiment(SpongeThatDoesNotAbsorb(Perm), Perm, MkD(D)).main() @ &m : res]
        - Pr[Experiment(IdealFunctionalityThatDoesNotAbsorb, 
             S(IdealFunctionalityThatDoesNotAbsorb), MkD(D)).main() @ &m : res] | = 
    `|Pr[Experiment(SpongeThatAbsorbs(Perm),Perm,D).main() @ &m : res] 
      - Pr[Experiment(IdealFunctionalityThatAbsorbs, MkS(S,IdealFunctionalityThatAbsorbs), D).main() @ &m : res]|.
  proof.
    congr;congr.
    + byequiv (_: ={glob D} ==> _) => //;proc;inline *.
      call (_: ={glob Perm});1,2:(by sim); last by auto.
      proc;inline{1}SpongeThatDoesNotAbsorb(Perm).f;sp 1 3;if=> //.
      sp;rcondt{1} 1=> //;wp.
      while (={glob Perm, i, sa, sc} /\ n0{1} = n{2} /\ z{1} = take (size m{1}) z{1} ++ z{2} /\ size m{1} <= size z{1}).
      + call (_ : ={glob Perm});[by sim|auto;progress [-split];smt].
      while (={glob Perm, p, sa,sc} /\ (size z = size m - size p){1}).
      + wp;call (_ : ={glob Perm});[by sim|auto;progress [-split];smt].
      by auto;progress [-split];smt. 
    cut -> : Pr[Experiment(IdealFunctionalityThatDoesNotAbsorb, S(IdealFunctionalityThatDoesNotAbsorb), MkD(D)).main () @ &m : res] =
               Pr[RndOrcl0.IND(Restr(RO), E1).main() @ &m : res].
    + byequiv=> //. (* PY: BUG printer res *)
      proc;inline{2} E1(Restr(RO)).distinguish;auto.
      call (_: ={glob S} /\ Ro.h{1} = RO.m{2}). 
      + by proc (Ro.h{1} = RO.m{2}) => //;apply f_f.
      + by proc (Ro.h{1} = RO.m{2}) => //;apply f_f.
      + by proc;sp;if=> //;wp;call f_f.
      by inline *; call (_: Ro.h{1} = RO.m{2});auto;apply f_f.
    cut -> : Pr[Experiment(IdealFunctionalityThatAbsorbs, MkS(S, IdealFunctionalityThatAbsorbs), D).main() @ &m : res] = 
               Pr[RndOrcl0.IND(Restr(RO), E2).main() @ &m : res].
    + byequiv=> //. 
      proc;inline{2} E2(Restr(RO)).distinguish;auto.
      call (_: ={glob S} /\ Ro.h{1} = RO.m{2}). 
      + proc (Ro.h{1} = RO.m{2}) => //; apply f_f'.
      + by proc (Ro.h{1} = RO.m{2}) => //;apply f_f'.
      + conseq f_f_a => //. 
      by inline *;call (_:Ro.h{1} = RO.m{2});[apply f_f'|auto].
    cut -> : Pr[RndOrcl0.IND(Restr(RO), E1).main() @ &m : res] = 
             Pr[RndOrcl0.IND(ERO, E1).main() @ &m : res].
    + byequiv (Eager E1)=> //.
    cut -> : Pr[RndOrcl0.IND(Restr(RO), E2).main() @ &m : res] = 
             Pr[RndOrcl0.IND(ERO, E2).main() @ &m : res].
    + byequiv (Eager E2)=> //.
    byequiv=> //.
    proc; inline *;wp.
    call (_: ={RO.m, glob S}).
    + by proc (={RO.m})=> //;apply f_dN.
    + by proc (={RO.m})=> //;apply f_dN.
    + proc;sp;if => //.
      inline{1} E1(ERO).F.f;sp;rcondt{1} 1; 1:by auto.
      wp;while (={RO.m,i,b} /\ n0{1} = n{2} /\ m0{1} = m{2} /\ z{1} = take (size m{1}) z{1} ++ z{2} /\ (size m <= size z){1}).
      + inline *;auto;progress [-split]; smt. 
      inline *;splitwhile{1} 1 : (j < size m0).
      wp;seq 1 0 : (={i,RO.m, m, glob S} /\ n0{1} = n{2} /\ m0{1} = m{2} /\ size m0{1} - 1 = size z{1} /\ size m0{1} = j{1} /\ z{2} = []).
      while{1} (size z{1} = j{1} - 1 /\ j{1} <= size m0{1}) ((size m0 - j){1});auto;progress [-split]; smt. 
      rcondt{1} 1;1:by auto. 
      rcondf{1} 5;auto;progress[-split];smt. 
    call (_: ={RO.m})=> //;1:by apply f_dN.
    sim : (={glob S, glob D, RO.m})=> //. 
  qed.
