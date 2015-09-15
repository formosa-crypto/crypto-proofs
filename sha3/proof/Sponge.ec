require import Option Pair Int Real NewList NewFSet NewFMap.
require (*..*) AWord LazyRP IRO Indifferentiability Squeezeless.
(* TODO: Clean up the Bitstring and Word theories
      -- Make use of those new versions. *)
(*...*) import Dprod.
(* TODO: Datatype definitions and distributions should
     be properly separated and reorganized. *)

op r : { int | 0 < r } as lt0_r.
op c : { int | 0 < c } as lt0_c.

(** Clarify assumptions on the distributions as we go. As this is currently
    written, we are hiding some pretty heavy axioms behind cloning. **)
type block.
op dblock: block distr.

clone import AWord as Block with
  op   length      <- r,
  type word        <- block,
  op   Dword.dword <- dblock
proof leq0_length by smt.

type capacity.
op dcapacity: capacity distr.

clone AWord as Capacity with
  op   length      <- c,
  type word        <- capacity,
  op   Dword.dword <- dcapacity
proof leq0_length by smt.

type state = block * capacity.

(** The following is just lining up type definitions and defines the
    Indifferentiability experiment. Importantly, it defines neither
    ideal primitive nor ideal functionality: only their type. **)
type p_query = [
  | F  of state
  | Fi of state
].

op is_F (q : p_query) =
  with q = F  s => true
  with q = Fi s => false.

op is_Fi (q : p_query) =
  with q = F  s => false
  with q = Fi s => true.

op get_query (q : p_query) =
  with q = F  s => s
  with q = Fi s => s.

clone include Indifferentiability with
  type p_in  <- p_query,
  type p_out <- state,
  type f_in  <- block list * int,
  type f_out <- bool list.

(** Ideal Functionality **)
clone import IRO as Functionality with
  type from <- block list.

(** Ideal Primitive for the Random Transformation case **)
clone import LazyRP as Primitive with
  type D <- state,
  op   d    <- dblock * dcapacity.

(*** TODO: deal with these.
       - bitstrings should have conversions to and from bool list
       - the generic RO should be defined somewhere else
       - lining up names and types should be easier than it is... ***)
op to_bits: block -> bool list.

module RP_to_P (O : RP) = {
  proc init = O.init
  proc oracle(q : p_query) = {
    var r;

    if (is_F q) {
      r <@ O.f(get_query q);
    } else {
      r <@ O.fi(get_query q);
    }
    return r;
  }
}.

module IRO_to_F (O : IRO): Functionality = {
  proc init = O.init

  (* proc oracle = O.hash
       does not work because of input types not lining up...
     I though this had been taken care of. *)
  proc oracle(x : block list * int): bool list = {
    var bs;
    bs = O.f(x.`1,x.`2);
    return bs;
  }
}.

(** We can now define the sponge construction **)
module Sponge (P : Primitive): Construction(P), Functionality = {
  proc init = P.init

  proc oracle(p : block list, n : int): bool list = {
    var z <- [];
    var s <- (Block.zeros,Capacity.zeros);
    var i <- 0;

    if (size p >= 1 /\ nth witness p (size p - 1) <> Block.zeros) {
      (* Absorption *)
      while (p <> []) {
        s <@ P.oracle(F (s.`1 ^ head witness p,s.`2));
        p <- behead p;
      }
      (* Squeezing *)
      while (i < n/%r) {
        z <- z ++ (Self.to_bits s.`1); (* Typing by constraint would be nice *)
        s <@ P.oracle(F s);
      }
    }

    return take n z;
  }
}.

(** TODO: ftn is in fact a function of N
      (number of queries to the primitive interface) **)
op ftn: real.

module P = RP_to_P(Primitive.P).
module F = IRO_to_F(IRO).

clone import Squeezeless as Core with
  op   r                  <- r,
  type block              <- block,
  op   dblock             <- dblock,
  op   c                  <- c,
  type capacity           <- capacity,
  op   dcapacity          <- dcapacity,
  (** The following should be dealt with by sub-theory instantiation,
      but the sub-theories we instantiate are partially concrete **)
  op   Block.zeros        <- Self.Block.zeros,
  op   Block.ones         <- Self.Block.ones,
  op   Block.(^)          <- Self.Block.(^),
  op   Block.land         <- Self.Block.land,
  op   Block.to_bits      <- Self.Block.to_bits,
  op   Block.from_bits    <- Self.Block.from_bits,
  op   Block.to_int       <- Self.Block.to_int,
  op   Block.from_int     <- Self.Block.from_int,
  op   Capacity.zeros     <- Self.Capacity.zeros,
  op   Capacity.ones      <- Self.Capacity.ones,
  op   Capacity.(^)       <- Self.Capacity.(^),
  op   Capacity.land      <- Self.Capacity.land,
  op   Capacity.to_bits   <- Self.Capacity.to_bits,
  op   Capacity.from_bits <- Self.Capacity.from_bits,
  op   Capacity.to_int    <- Self.Capacity.to_int,
  op   Capacity.from_int  <- Self.Capacity.from_int
proof *.
  realize lt0_r                   by exact/lt0_r.
  realize lt0_c                   by exact/lt0_c.
  realize Block.ones_neq0         by exact/Self.Block.ones_neq0.
  realize Block.xorwA             by exact/Self.Block.xorwA.
  realize Block.xorwC             by exact/Self.Block.xorwC.
  realize Block.xor0w             by exact/Self.Block.xor0w.
  realize Block.xorwK             by exact/Self.Block.xorwK.
  realize Block.landwA            by exact/Self.Block.landwA.
  realize Block.landwC            by exact/Self.Block.landwC.
  realize Block.land1w            by exact/Self.Block.land1w.
  realize Block.landwDl           by exact/Self.Block.landwDl.
  realize Block.landI             by exact/Self.Block.landI.
  realize Block.length_to_bits    by exact/Self.Block.length_to_bits.
  realize Block.can_from_to       by exact/Self.Block.can_from_to.
  realize Block.pcan_to_from      by exact/Self.Block.pcan_to_from.
  realize Block.to_from           by exact/Self.Block.to_from.
  realize Block.from_to           by exact/Self.Block.from_to.
  realize Block.Dword.mu_x_def    by exact/Self.Block.Dword.mu_x_def.
  realize Block.Dword.lossless    by exact/Self.Block.Dword.lossless.
  realize Capacity.ones_neq0      by exact/Self.Capacity.ones_neq0.
  realize Capacity.xorwA          by exact/Self.Capacity.xorwA.
  realize Capacity.xorwC          by exact/Self.Capacity.xorwC.
  realize Capacity.xor0w          by exact/Self.Capacity.xor0w.
  realize Capacity.xorwK          by exact/Self.Capacity.xorwK.
  realize Capacity.landwA         by exact/Self.Capacity.landwA.
  realize Capacity.landwC         by exact/Self.Capacity.landwC.
  realize Capacity.land1w         by exact/Self.Capacity.land1w.
  realize Capacity.landwDl        by exact/Self.Capacity.landwDl.
  realize Capacity.landI          by exact/Self.Capacity.landI.
  realize Capacity.length_to_bits by exact/Self.Capacity.length_to_bits.
  realize Capacity.can_from_to    by exact/Self.Capacity.can_from_to.
  realize Capacity.pcan_to_from   by exact/Self.Capacity.pcan_to_from.
  realize Capacity.to_from        by exact/Self.Capacity.to_from.
  realize Capacity.from_to        by exact/Self.Capacity.from_to.
  realize Capacity.Dword.mu_x_def by exact/Self.Capacity.Dword.mu_x_def.
  realize Capacity.Dword.lossless by exact/Self.Capacity.Dword.lossless.
(* end of clone *)

module type BlockSponge = {
  proc init(): unit
  proc oracle(p : block list, n : int): block list
}.

module Squeezer(F : Core.Functionality): BlockSponge = {
  proc init = F.init

  proc oracle(p : block list, n : int): block list = {
    var z <- [];
    var b;
    var i <- 0;

    if (size p >= 1 /\ nth witness p (size p - 1) <> Self.Block.zeros) {
      while (i < n) {
        b <@ F.oracle(p ++ mkseq (fun i => Self.Block.zeros) i);
        z <- rcons z b;
        i <- i + 1;
      }
    }

    return z;
  }
}.

(* Result: if there exists a good simulator for the Core functionality
   F, then we can construct a simulator for Squeezer(F) that has the
   same differentiability advantage.
   Note: We need to be careful and may need to make this whitebox so
   we can avoid having to make too many queries. *)

module Truncator(F : BlockSponge): Self.Functionality = {
  proc init = F.init

  proc oracle(p : block list, n : int): bool list = {
    var z <- [];
    var bs;

    if (size p >= 1 /\ nth witness p ( size p - 1) <> Self.Block.zeros) {
      bs <@ F.oracle(p,n /% r);
      z <- z ++ flatten (map to_bits bs);
    }

    return take n z;
  }
}.

(* Result: if there exists a good simulator for the BlockSponge F,
   then we can construct a simulator for Truncator(F) that has the
   same differentiability advantage.
   Note: We need to be careful and may need to make this whitebox so
   we can avoid having to make too many queries. *)

(* That Self is unfortunate *)
lemma PermutationLemma: exists (S <: Simulator),
  forall (D <: Self.Distinguisher) &m,
    `|Pr[Indif(Sponge(P),P,D).main() @ &m: res]
      - Pr[Indif(F,S(F),D).main() @ &m: res]|
  < ftn.
proof. admit. qed.