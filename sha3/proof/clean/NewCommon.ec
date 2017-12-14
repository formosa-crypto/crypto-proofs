require import Core Logic Distr.
require import Int IntExtra Real List NewFMap FSet.
require import StdOrder.
(*---*) import IntOrder.

(*** THEORY PARAMETERS ***)
(** Block/Rate **)
theory Block.
  op r : int.
  axiom r_ge0: 0 <= r.

  type block.

  op b0: block.
  op (+^): block -> block -> block.

  axiom addbA b1 b2 b3: b1 +^ (b2 +^ b3) = b1 +^ b2 +^ b3.
  axiom addbC b1 b2: b1 +^ b2 = b2 +^ b1.
  axiom add0b b: b0 +^ b = b.
  axiom addbK b: b +^ b = b0.

  op blocks: block list.
  axiom blocks_spec b: count (pred1 b) blocks = 1.
  axiom card_block: size blocks = 2^r.

  clone import Ring.ZModule as BlockMonoid with 
    type t               <- block,
    op zeror             <- b0,
    op ( + )             <- (+^),
    op [ - ] (b : block) <- b
  remove abbrev (-)
  proof *.
  realize addrA by exact/addbA.
  realize addrC by exact/addbC.
  realize add0r by exact/add0b.
  realize addNr by exact/addbK.

  clone import MFinite as DBlock with
    type t            <- block,
    op   Support.enum <- blocks
  rename "dunifin"  as "bdistr"
         "duniform" as "bdistr"
  proof *.
  realize Support.enum_spec by exact/blocks_spec.
end Block.
import Block DBlock.

(**  Capacity  **)
theory Capacity.
  op c : int.
  axiom c_ge0: 0 <= c.

  type capacity.

  op c0: capacity.

  op caps: capacity list.
  axiom caps_spec b: count (pred1 b) caps = 1.
  axiom card_capacity: size caps = 2^c.

  clone import MFinite as DCapacity with
    type t            <- capacity,
    op   Support.enum <- caps
  rename "dunifin"  as "cdistr"
         "duniform" as "cdistr"
  proof *.
  realize Support.enum_spec by exact/caps_spec.
end Capacity.
import Capacity DCapacity.

(** Query Bound **)
op max_query: int.
axiom max_query_ge0: 0 <= max_query.