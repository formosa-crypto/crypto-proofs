(* -------------------------------------------------------------------- *)
require import Option Pair Int Real List.
require (*--*) Common LazyRP RndOrcl Indifferentiability.

op cast: 'a NewDistr.distr -> 'a distr.

(* -------------------------------------------------------------------- *)
require import Common.

(* -------------------------------------------------------------------- *)

op valid : block list -> bool =
  fun xs => strip xs <> None.

clone import RndOrcl as RO with
  type from                          <- block list,
  type to                            <- block,
    op Ideal.sample (x : block list) <- cast bdistr.
clone import Ideal. (* ?? Nested abstract theories... we don't like them *)
  
(* -------------------------------------------------------------------- *)
clone include Indifferentiability with
  type p     <- block * capacity,
  type f_in  <- block list,
  type f_out <- block

  rename
    [module] "Indif" as "Experiment"
    [module] "GReal"  as "RealIndif"
    [module] "GIdeal"  as "IdealIndif".
 

(* -------------------------------------------------------------------- *)
module BlockSponge (P : PRIMITIVE) : RO, CONSTRUCTION(P) = {
  proc init = P.init

  proc f(p : block list): block = {
    var (sa,sc) <- (b0, Capacity.c0);

    if (valid p) {
      (* Absorption *)
      while (p <> []) {
        (sa,sc) <@ P.f(sa ^ head b0 p, sc);
        p       <- behead p;
      }
    }
    return sa;
  }
}.

(* -------------------------------------------------------------------- *)
op eps : real.

lemma top:
  exists (S <: SIMULATOR),
    forall (D <: DISTINGUISHER) &m,
      `|  Pr[Experiment(BlockSponge(Perm), Perm, D).main() @ &m : res]
        - Pr[Experiment(RO, S(RO), D).main() @ &m : res]|
       < eps.
proof. admit. qed.
