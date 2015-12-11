(* -------------------------------------------------------------------- *)
require import Option Pair Int Real List.
require (*--*) Common IRO LazyRP Indifferentiability.

(* -------------------------------------------------------------------- *)
require import Common.

(* -------------------------------------------------------------------- *)

clone import IRO as BIRO with
  type from <- block list,
  type to   <- block,
  op valid  <- valid_block.
  
(* -------------------------------------------------------------------- *)
clone include Indifferentiability with
  type p     <- block * capacity,
  type f_in  <- block list * int,
  type f_out <- block list

  rename
    [module] "Indif" as "Experiment"
    [module] "GReal"  as "RealIndif"
    [module] "GIdeal"  as "IdealIndif".

(* -------------------------------------------------------------------- *)
module BlockSponge (P : DPRIMITIVE) : FUNCTIONALITY, CONSTRUCTION(P) = {
  proc init() = {}

  proc f(p : block list, n : int) : block list = {
    var z       <- [];
    var (sa,sc) <- (b0, Capacity.c0);
    var i       <- 0;

    if (valid_block p) {
      (* Absorption *)
      while (p <> []) {
        (sa,sc) <@ P.f(sa +^ head b0 p, sc);
        p       <- behead p;
      }
      (* Squeezing *)
      while (i < n) {
        z       <- rcons z sa;
        (sa,sc) <@ P.f(sa,sc);
        i       <- i + 1;
      }
    }
    return z;
  }
}.

(* -------------------------------------------------------------------- *)
op eps : real.

lemma top:
  exists (S <: SIMULATOR),
    forall (D <: DISTINGUISHER) &m,
      `|  Pr[RealIndif(BlockSponge, Perm, D).main() @ &m : res]
        - Pr[IdealIndif(IRO, S, D).main() @ &m : res]|
       < eps.
proof. admit. qed.
