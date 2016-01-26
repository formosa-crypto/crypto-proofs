(*-------------------- Padded Block Sponge Construction ----------------*)

require import Option Pair Int Real List.
require (*--*) IRO Indifferentiability.
require import Common.

(*------------------------- Indifferentiability ------------------------*)

clone include Indifferentiability with
  type p     <- block * capacity,
  type f_in  <- block list * int,
  type f_out <- block list

  rename
    [module] "Indif" as "Experiment"
    [module] "GReal"  as "RealIndif"
    [module] "GIdeal"  as "IdealIndif".

(*------------------------- Ideal Functionality ------------------------*)

clone import IRO as BIRO with
  type from <- block list,
  type to   <- block,
  op valid  <- valid_block,
  op dto    <- bdistr.

(*------------------------- Sponge Construction ------------------------*)

module Sponge (P : DPRIMITIVE) : FUNCTIONALITY, CONSTRUCTION(P) = {
  proc init() = {}

  proc f(xs : block list, n : int) : block list = {
    var z        <- [];
    var (sa, sc) <- (b0, Capacity.c0);
    var i        <- 0;

    if (valid_block xs) {
      (* absorption *)
      while (xs <> []) {
        (sa, sc) <@ P.f(sa +^ head b0 xs, sc);
        xs       <- behead xs;
      }
      (* Squeezing *)
      while (i < n) {
        z        <- rcons z sa;
        (sa, sc) <@ P.f(sa, sc);
        i        <- i + 1;
      }
    }
    return z;
  }
}.

(*----------------------------- Conclusion -----------------------------*)

(* this is just for typechecking, right now: *)

op eps : real.

lemma conclusion :
  exists (S <: SIMULATOR),
    forall (D <: DISTINGUISHER) &m,
      `|  Pr[RealIndif(Sponge, Perm, D).main() @ &m : res]
        - Pr[IdealIndif(IRO, S, D).main() @ &m : res]|
       < eps.
proof. admit. qed.
