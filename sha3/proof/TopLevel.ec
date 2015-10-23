(* -------------------------------------------------------------------- *)
require import Pair Int Real List.
require (*--*) IRO LazyRP.
(*---*) import Dprod.

(* -------------------------------------------------------------------- *)
(* Replay Common.ec *)
op r : { int | 0 < r } as gt0_r.
op c : { int | 0 < c } as gt0_c.

type block.
type capacity.

op cdist : capacity distr.
op bdist : block distr.

op b0 : block.
op c0 : capacity.

op b2bits : block -> bool list.

op (^) : block -> block -> block.

(* -------------------------------------------------------------------- *)
op pad : bool list -> block list.

(* -------------------------------------------------------------------- *)
clone import IRO as BIRO with
  type from <- bool list,
  type to <- bool,
  op valid (x : bool list) <- true.

clone import LazyRP as Perm with
  type D <- block * capacity,
  op   d <- bdist * cdist

  rename [module] "P" as "Perm".
  
(* -------------------------------------------------------------------- *)
module type CONSTRUCTION(P : RP) = {
  proc init() : unit

  proc f(bp : bool list, n : int) : bool list
}.

module type SIMULATOR(F : BIRO.IRO) = {
  proc init() : unit

  proc f(_ : block * capacity) : block * capacity

  proc fi(_ : block * capacity) : block * capacity
}.

module type DISTINGUISHER(F : BIRO.IRO, P : RP) = {
  proc distinguish() : bool
}.

(* -------------------------------------------------------------------- *)
module Experiment(F : BIRO.IRO, P : RP, D : DISTINGUISHER) = {
  proc main() : bool = {
    var b;
    
    F.init();
    P.init();
    b <@ D(F, P).distinguish();

    return b;
  }
}.

(* -------------------------------------------------------------------- *)
module Sponge (P : RP) : BIRO.IRO, CONSTRUCTION(P) = {
  proc init = P.init

  proc f(bp : bool list, n : int): bool list = {
    var z <- [];
    var s <- (b0, c0);
    var i <- 0;
    var p <- pad bp;

    (* Absorption *)
    while (p <> []) {
      s <@ P.f(s.`1 ^ head b0 p, s.`2);
      p <- behead p;
    }
    (* Squeezing *)
    while (i < n/%r) {
      z <- z ++ (b2bits s.`1);
      s <@ P.f(s);
    }

    return take n z;
  }
}.

(* -------------------------------------------------------------------- *)
op eps : real.

lemma top:
  exists (S <: SIMULATOR),
    forall (D <: DISTINGUISHER) &m,
      `|  Pr[Experiment(Sponge(Perm), Perm, D).main() @ &m : res]
        - Pr[Experiment(IRO, S(IRO), D).main() @ &m : res]|
       < eps.
proof. admit. qed.
