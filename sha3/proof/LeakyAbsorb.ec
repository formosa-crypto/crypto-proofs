(* -------------------------------------------------------------------- *)
require import Option Pair Int Real List FSet NewFMap.
require (*--*) IRO LazyRP.
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

module IdealFunctionalityThatDoesNotAbsorb = {
  var h : (block list * int,block) fmap

  proc init() = { h = map0; }

  proc core(m : block list * int) = {
    if (!mem (dom h) m) {
      h.[m] <$ bdist;
    }
    return oget h.[m];
  }

  proc f(m : block list, n : int) = {
    var i <- 0;
    var j <- 1;
    var z <- [];
    var b <- b0;

    if (m <> []) {
      while (i < size m) {
        z <- rcons z b;
        b <@ core(take i m,0);
        i <- i + 1;
      }
      while (j < n) {
        z <- rcons z b;
        b <@ core(m,j);
        j <- j + 1;
      }
    }
    return z;
  }
}.

module IdealFunctionalityThatAbsorbs = {
  var h : (block list * int,block) fmap

  proc init() = { h = map0; }

  proc core (m : block list * int) = {
    if (!mem (dom h) m) {
      h.[m] <$ bdist;
    }
    return oget h.[m];
  }

  proc f(m : block list, n : int) = {
    var j <- 1;
    var z <- [];
    var b;

    if (m <> []) {
      b <@ core(m,0);
      while (j < n) {
        z <- rcons z b;
        b <@ core(m,j);
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

module type DISTINGUISHER(F : WeirdIRO, P : RP) = {
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
  proc init = P.init

  proc f(p : block list, n : int): block list = {
    var z       <- [];
    var (sa,sc) <- (b0, c0);
    var i       <- 0;
    var l       <- size p;

    if (p <> [] /\ nth witness p (size p - 1) <> b0) {
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
  proc init = P.init

  proc f(p : block list, n : int): block list = {
    var z       <- [];
    var (sa,sc) <- (b0, c0);
    var i       <- 0;

    if (p <> [] /\ nth witness p (size p - 1) <> b0) {
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