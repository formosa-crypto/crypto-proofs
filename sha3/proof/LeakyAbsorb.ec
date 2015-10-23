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

op b2bits : block -> bool list.

op (^) : block -> block -> block.
op pad : bool list -> block list.

(* -------------------------------------------------------------------- *)
clone import LazyRP as Perm with
  type D <- block * capacity,
  op   d <- bdist * cdist

  rename [module] "P" as "Perm".

clone import IRO as BIRO with
  type from                   <- block list,
  type to                     <- block,
  op   valid (x : block list) <- true,
  op   dto                    <- bdist.

(* -------------------------------------------------------------------- *)
module type WeirdIRO = {
  proc init(): unit

  proc f(_: block list * int): block list
}.

module IdealFunctionality = {
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
    var z <- [b0];
    var b;

    m <- m ++ mkseq (fun k => b0) n;
    while (i < size m) {
      b <@ core(take i m);
      z <- rcons z b;
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

    (* Absorption *)
    while (p <> []) {
      z       <- rcons z sa;
      (sa,sc) <@ P.f(sa ^ head b0 p, sc);
      p       <- behead p;
    }
    (* Squeezing *)
    while (i < n/%r) {
      z       <- rcons z sa;
      (sa,sc) <@ P.f(sa,sc);
    }

    return drop l z;
  }
}.

(* -------------------------------------------------------------------- *)
module SpongeThatAbsorbs (P : RP) : WeirdIRO, CONSTRUCTION(P) = {
  proc init = P.init

  proc f(p : block list, n : int): block list = {
    var z       <- [];
    var (sa,sc) <- (b0, c0);
    var i       <- 0;

    (* Absorption *)
    while (p <> []) {
      (sa,sc) <@ P.f(sa ^ head b0 p, sc);
      p       <- behead p;
    }
    (* Squeezing *)
    while (i < n/%r) {
      z       <- rcons z sa;
      (sa,sc) <@ P.f(sa,sc);
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
        - Pr[Experiment(IdealFunctionality, S(IdealFunctionality), D).main() @ &m : res]|
       < eps.


lemma top:
  exists eps',
    exists (S <: SIMULATOR),
      forall (D <: DISTINGUISHER) &m,
        `|  Pr[Experiment(SpongeThatAbsorbs(Perm), Perm, D).main() @ &m : res]
          - Pr[Experiment(IRO, S(IRO), D).main() @ &m : res]|
         < eps'.
proof. admit. (** FILL ME IN **) qed.