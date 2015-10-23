(* -------------------------------------------------------------------- *)
require import Pair Int Real List.
require (*--*) IRO LazyRP Indifferentiability.
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
clone include Indifferentiability.Core with
  type Types.p     <- block * capacity,
  type Types.f_in  <- bool list * int,
  type Types.f_out <- bool list

  rename
    [module] "Indif" as "Experiment"
    [module] "al"  as "alIndif".
import Types.

(* -------------------------------------------------------------------- *)
(** Spurious uninitialized variable warning on p *)
module Sponge (P : RP) : BIRO.IRO, CONSTRUCTION(P) = {
  proc init = P.init

  proc f(bp : bool list, n : int): bool list = {
    var z       <- [];
    var (sa,sc) <- (b0, c0);
    var i       <- 0;
    var p       <- pad bp;

    (* Absorption *)
    while (p <> []) {
      (sa,sc) <@ P.f(sa ^ head b0 p, sc);
      p       <- behead p;
    }
    (* Squeezing *)
    while (i < (n + r - 1) /% r) {
      z       <- z ++ (b2bits sa);
      (sa,sc) <@ P.f(sa,sc);
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
