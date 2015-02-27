require import Option Pair Int ABitstring NewList.
require (*..*) AWord Indifferentiability.
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

clone import Indifferentiability as Main with
  type from0 <- state,
  type to0   <- state,
  op   d0    <- fun (x:state) => dblock * dcapacity,
  type from1 <- block list * int,
  type to1   <- bitstring,
  op   d1    <- fun (x:block list * int) => DBitstring.dbitstring x.`2.

module Sponge (H : H.RO): Construction(H) = {
  proc init = H.init

  proc hash(p : block list, n : int): bitstring = {
    var z = ABitstring.zeros n;
    var s = (Block.zeros,Capacity.zeros);
    var i = 0;

    if (size p >= 1 /\ nth witness p (size p - 1) <> Block.zeros) {
      z = ABitstring.zeros 0;
      while (p <> []) {
        s = H.hash(s.`1 ^ head witness p,s.`2);
        p = behead p;
      }
      while (i < n/%r) {
        z = z || (to_bits s.`1);
        s = H.hash(s);
      }
    }

    return sub z 0 n;
  }
}.
