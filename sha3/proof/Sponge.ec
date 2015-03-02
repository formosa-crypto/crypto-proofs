require import Option Pair Int Real NewList NewFSet NewFMap.
require (*..*) AWord LazyRO IRO Indifferentiability.
(* TODO: Clean up the Bitstring and Word theories
      -- Make use of those new versions. *)
(*...*) import Dprod.
(* TODO: Datatype definitions and distributions should
     be properly separated and reorganized. *)

op r : int.
axiom le0_r: 0 < r.

op c : int.
axiom le0_c: 0 < c.

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

(** Ideal Functionality **)
clone import IRO as Functionality with
  type from <- block list.

(** The following is just lining up type definitions and defines the
    Indifferentiability experiment. Importantly, it defines neither
    ideal primitive nor ideal functionality: only their type. **)
clone import Indifferentiability as Main with
  type p_in  <- state,
  type p_out <- state,
  type f_in  <- block list * int,
  type f_out <- bool list.

(** Ideal Primitive for the Random Transformation case **)
clone import LazyRO as Primitive with
  type from <- state,
  type to   <- state,
  op   d    <- dblock * dcapacity.

(*** TODO: deal with these.
       - bitstrings should have conversions to and from bool list
       - the generic RO should be defined somewhere else
       - lining up names and types should be easier than it is... ***)
op to_bits: block -> bool list.

module RO_to_P (O : Types.RO) = {
  proc init = O.init
  proc oracle = O.hash
}.

module IRO_to_F (O : IRO): Functionality = {
  proc init = O.init

  (* proc oracle = O.hash
       does not work because of input types not lining up...
     I though this had been taken care of. *)
  proc oracle(x : block list * int): bool list = {
    var bs;
    bs = O.hash(x.`1,x.`2);
    return bs;
  }
}.

(** We can now define the sponge construction **)
module Sponge (P : Primitive): Construction(P) = {
  proc init = P.init

  proc oracle(p : block list, n : int): bool list = {
    var z;
    var s = (Block.zeros,Capacity.zeros);
    var i = 0;

    if (size p >= 1 /\ nth witness p (size p - 1) <> Block.zeros) {
      z = [];
      while (p <> []) {
        s = P.oracle(s.`1 ^ head witness p,s.`2);
        p = behead p;
      }
      while (i < n/%r) {
        z = z ++ (Self.to_bits s.`1); (* Typing by constraint would be nice *)
        s = P.oracle(s);
      }
    }

    return take n z;
  }
}.

(** TODO: ftn is in fact a function of N
      (number of queries to the primitive interface) **)
op ftn: real.

module P = RO_to_P(Primitive.H).
module F = IRO_to_F(IRO).

lemma TransformationLemma (D <: Distinguisher) &m:
  exists (S <: Simulator),
    `|Pr[Indif(Sponge(P),P,D).main() @ &m: res]
      - Pr[Indif(F,S(F),D).main() @ &m: res]|
  < ftn.
proof. admit. qed.
