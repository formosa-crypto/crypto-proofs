(* -------------------------------------------------------------------- *)
require import Pair Int IntDiv Real List.
require (*--*) IRO LazyRP Indifferentiability.

(* -------------------------------------------------------------------- *)
require import Common.

(* -------------------------------------------------------------------- *)
clone import IRO as BIRO with
  type from <- bool list,
  type to <- bool,
  op valid (x : bool list) <- true.
  
(* -------------------------------------------------------------------- *)
clone include Indifferentiability with
  type p     <- block * capacity,
  type f_in  <- bool list * int,
  type f_out <- bool list

  rename
    [module] "Indif" as "Experiment"
    [module] "GReal"  as "RealIndif"
    [module] "GIdeal"  as "IdealIndif".

(* -------------------------------------------------------------------- *)

module Sponge (P : PRIMITIVE) : BIRO.IRO, CONSTRUCTION(P) = {
  proc init = P.init

  proc f(bp : bool list, n : int) : bool list = {
    var z       <- [];
    var (sa,sc) <- (b0, Capacity.c0);
    var i       <- 0;
    var p       <- map bits2w (chunk (pad bp));

    (* Absorption *)
    while (p <> []) {
      (sa,sc) <@ P.f(sa +^ head b0 p, sc);
      p       <- behead p;
    }
    (* Squeezing *)
    while (i < (n + r - 1) %/ r) {
      z       <- z ++ (Block.w2bits sa);
      (sa,sc) <@ P.f(sa,sc);
      i       <- i + 1;
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
