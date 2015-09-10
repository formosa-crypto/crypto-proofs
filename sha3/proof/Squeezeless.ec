(** This is a theory for the Squeezeless sponge: where the ideal
    functionality is a fixed-output-length random oracle whose output
    length is the input block size. We prove its security even when
    padding is not prefix-free. **)
require import Option Pair Int Real NewList NewFSet NewFMap.
require (*..*) AWord LazyRP LazyRO Indifferentiability.
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

type state  = block  *  capacity.
op   dstate = dblock * dcapacity.

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
  type f_in  <- block list,
  type f_out <- block.

(** Ideal Functionality **)
clone import LazyRO as Functionality with
  type from <- block list,
  type to   <- block,
  op   d    <- dblock.

(** Ideal Primitive for the Random Transformation case **)
clone import LazyRP as Primitive with
  type D <- state,
  op   d <- dstate.

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

module RO_to_F (O : RO): Functionality = {
  proc init   = O.init
  proc oracle = O.f
}.

(** We can now define the squeezeless sponge construction **)
module SqueezelessSponge (P : Primitive): Construction(P), Functionality = {
  proc init = P.init

  proc oracle(p : block list): block = {
    var (sa,sc) <- (Block.zeros,Capacity.zeros);

    if (size p >= 1 /\ p <> [Block.zeros]) {
      (* Absorption *)
      while (p <> []) {
        (sa,sc) <@ P.oracle(F (sa ^ head witness p,sc));
        p <- behead p;
      }
    }
    return sa;
  }
}.

(** And the corresponding simulator **)
op find_chain: (state,state) fmap -> state -> (block list * block) option.

module PreSimulator (F : Functionality) = {
  var m, mi: (state,state) fmap

  proc init() = {
    F.init();
    m  <- map0;
    mi <- map0;
  }

  proc f(x:state) = {
    var pvo, p, v, h, y;

    if (!mem (dom m) x) {
      pvo <- find_chain m x;
      if (pvo <> None) {
        (p,v) <- oget pvo;
        h <@ F.oracle(rcons p v);
        y <$ dcapacity;
      } else {
        (h,y) <$ dstate;
      }
      m.[x] <- (h,y);
      mi.[(h,y)] <- x;
    }
    return oget m.[x];
  }

  proc fi(x:state) = {
    var y;

    if (!mem (dom mi) x) {
      y <$ dstate;
      mi.[x] <- y;
      m.[y] <- x;
    }
    return oget mi.[x];
  }
}.

module P = RP_to_P(Primitive.P).
module F = RO_to_F(H).
module S(F : Functionality) = RP_to_P(PreSimulator(F)).

(* That Self is unfortunate *)
lemma PermutationLemma:
  exists epsilon,
    forall (D <: Self.Distinguisher) &m,
    `|Pr[Indif(SqueezelessSponge(P),P,D).main() @ &m: res]
      - Pr[Indif(F,S(F),D).main() @ &m: res]|
  < epsilon.
proof. admit. qed.
