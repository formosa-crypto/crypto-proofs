(* -------------------------------------------------------------------- *)
require import Option Pair Int Real List FSet NewFMap.
require (*--*) LazyRP RndOrcl.
(*---*) import Dprod.

(* -------------------------------------------------------------------- *)
op r : { int | 0 < r } as gt0_r.
op c : { int | 0 < c } as gt0_c.

type block.    (* = {0,1}^r *)
type capacity. (* = {0,1}^c *)

op cdist : capacity distr.
op bdist : block distr.

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
axiom valid_queryP : forall m n, valid_query m n => mem valid_queries (m ++ map (fun x => b0) (iota_ 0 n)).

module IdealFunctionalityThatDoesNotAbsorb = {
  var h : (block list,block) fmap

  proc init() = { h = map0; }

  proc core(m : block list) = {
    if (!mem (dom h) m) {
      h.[m] <$ bdist;
    }
    return oget h.[m];
  }

  proc f(m : block list, n : int) = {
    var i <- 1;
    var j <- 1;
    var z <- [];
    var b <- b0;

    if (valid_query m n) {
      while (j <= size m) {
        z <- rcons z b;
        b <@ core(take j m);
        j <- j + 1;
      }
      while (i < n) {
        z <- rcons z b;
        m <- rcons m b0;
        b <@ core(m);
        j <- j + 1;
      }
    }
    return z;
  }
}.

module IdealFunctionalityThatAbsorbs = {
  proc init = IdealFunctionalityThatDoesNotAbsorb.init

  proc f(m : block list, n : int) = {
    var j <- 1;
    var z <- [];
    var b;

    if (valid_query m n) {
      b <@ IdealFunctionalityThatDoesNotAbsorb.core(m);
      while (j < n) {
        z <- rcons z b;
        m <- rcons m b0;
        b <@ IdealFunctionalityThatDoesNotAbsorb.core(m);
        j <- j + 1;
      }
    }
    return z;
  }
}.

(* -------------------------------------------------------------------- *)
module type CONSTRUCTION(P : RP) = {
  proc init() : unit

  proc f(bp : block list, n : int) : block list
}.

module type SIMULATOR(F : WeirdIRO) = {
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

  module MkFdoNot (F:WeirdIRO) = {
    proc init = F.init
    proc f(m:block list, n:int) : block list = {
      var i, r, tl, b;
      r <- [];
      if (valid_query m n) {
        i <- 0;
        while (i < size m - 1) {
          b <- F.f(take i m, 1);
          i <- i + 1;
          r <- r ++ b;
        }
        tl <- F.f(m,n);
        r  <- r ++ tl;
      }
      return r;
    }
  }.

  module MkS(S:SIMULATOR, F:WeirdIRO) = S(MkFdoNot(F)).

  local clone 

  lemma conclusion &m:
    `| Pr[Experiment(SpongeThatDoesNotAbsorb(Perm), Perm, MkD(D)).main() @ &m : res]
        - Pr[Experiment(IdealFunctionalityThatDoesNotAbsorb, 
             S(IdealFunctionalityThatDoesNotAbsorb), MkD(D)).main() @ &m : res] | = 
    `|Pr[Experiment(SpongeThatAbsorbs(Perm),Perm,D).main() @ &m : res] -
      -Pr[Experiment(IdealFunctionalityThatAbsorbs, MkS(S,IdealFunctionalityThatAbsorbs), D).main() @ &m : res]|.
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
    +      
      auto. 

smt. smt.
search drop.          
        
sim.




op eps : real.

axiom core:
  exists (S <: SIMULATOR),
    forall (D <: DISTINGUISHER) &m,
      `|  Pr[Experiment(SpongeThatDoesNotAbsorb(Perm), Perm, D).main() @ &m : res]
        - Pr[Experiment(IdealFunctionalityThatDoesNotAbsorb, S(IdealFunctionalityThatDoesNotAbsorb), D).main() @ &m : res]|
       < eps.

lemma top:
  exists eps',
    exists (S <: SIMULATOR),
      forall (D <: DISTINGUISHER) &m,
        `|  Pr[Experiment(SpongeThatAbsorbs(Perm), Perm, D).main() @ &m : res]
          - Pr[Experiment(IdealFunctionalityThatAbsorbs, S(IdealFunctionalityThatAbsorbs), D).main() @ &m : res]|
         < eps'.
proof. admit. (** FILL ME IN **) qed.