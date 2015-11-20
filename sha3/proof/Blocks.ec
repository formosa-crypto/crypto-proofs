(* -------------------------------------------------------------------- *)
require import Option Pair Int Real List.
require (*--*) Common IRO LazyRP Indifferentiability.

(* -------------------------------------------------------------------- *)
require import Common.

(* -------------------------------------------------------------------- *)

op valid : block list -> bool =
  fun xs => unpad xs <> None.

clone import IRO as BIRO with
  type from  <- block list,
  type to    <- block,
    op valid <- valid.
  
(* -------------------------------------------------------------------- *)
clone include Indifferentiability.Core with
  type Types.p     <- block * capacity,
  type Types.f_in  <- block list * int,
  type Types.f_out <- block list

  rename
    [module] "Indif" as "Experiment"
    [module] "al"  as "alIndif".

(* -------------------------------------------------------------------- *)
module BlockSponge (P : PRIMITIVE) : BIRO.IRO, CONSTRUCTION(P) = {
  proc init = P.init

  proc f(p : block list, n : int) : block list = {
    var z       <- [];
    var (sa,sc) <- (b0, Capacity.c0);
    var i       <- 0;

    if (valid p) {
      (* Absorption *)
      while (p <> []) {
        (sa,sc) <@ P.f(sa ^ head b0 p, sc);
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
        - Pr[IdealIndif(IRO', S, D).main() @ &m : res]|
       < eps.
proof. admit. qed.
