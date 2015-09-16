(** These should make it into the standard libs **)
require import NewList NewFSet.

op image (f : 'a -> 'b) (X : 'a fset) = oflist (map f (elems X))
  axiomatized by imageE.

lemma imageP (f : 'a -> 'b) (X : 'a fset) (b : 'b):
  mem (image f X) b <=> exists a, mem X a /\ f a = b.
proof.
  rewrite imageE mem_oflist mapP.
  (* FIXME *)
  by split=> [[a] [a_in_X b_def]| [a] [a_in_X b_def]];
    [rewrite -memE in a_in_X | rewrite memE in a_in_X];
    exists a; rewrite b_def.
qed.