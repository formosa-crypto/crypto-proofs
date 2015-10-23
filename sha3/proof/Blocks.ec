(* -------------------------------------------------------------------- *)
require import Option Pair Int Real List.
require (*--*) Common IRO LazyRP Indifferentiability.

op ( * ): 'a NewDistr.distr -> 'b NewDistr.distr -> ('a * 'b) distr.

(* -------------------------------------------------------------------- *)
clone include Common.

(* -------------------------------------------------------------------- *)
op valid: block list -> bool. (* is in the image of the padding function *)
axiom valid_lb m:
  valid m =>
  m <> [] /\ nth witness m (size m - 1) <> b0.

clone import IRO as BIRO with
  type from <- block list,
  type to <- block,
  op valid <- valid.

clone import LazyRP as Perm with
  type D <- block * capacity,
  op   d <- bdistr * Capacity.cdistr

  rename [module] "P" as "Perm".
  
(* -------------------------------------------------------------------- *)
clone include Indifferentiability.Core with
  type Types.p     <- block * capacity,
  type Types.f_in  <- block list * int,
  type Types.f_out <- block list

  rename
    [module] "Indif" as "Experiment"
    [module] "al"  as "alIndif".
import Types.

(* -------------------------------------------------------------------- *)
(** Spurious uninitialized variable warning on p *)
module BlockSponge (P : RP) : BIRO.IRO, CONSTRUCTION(P) = {
  proc init = P.init

  proc f(p : block list, n : int): block list = {
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
      `|  Pr[Experiment(BlockSponge(Perm), Perm, D).main() @ &m : res]
        - Pr[Experiment(IRO, S(IRO), D).main() @ &m : res]|
       < eps.
proof. admit. qed.
