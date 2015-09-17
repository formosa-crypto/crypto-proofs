(** These should make it into the standard libs **)
require import NewList NewFSet NewFMap.

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

lemma rem_id (x : 'a) (m : ('a,'b) fmap):
  !mem (dom m) x => rem x m = m.
proof.
  rewrite in_dom /= => x_notin_m; apply/fmapP=> x'; rewrite remP.
  case (x' = x)=> //= ->>.
  by rewrite x_notin_m.
qed.

lemma dom_rem_le (x : 'a) (m : ('a,'b) fmap) (x' : 'a):
  mem (dom (rem x m)) x' => mem (dom m) x'.
proof. by rewrite dom_rem in_fsetD. qed.

lemma rng_rem_le (x : 'a) (m : ('a,'b) fmap) (x' : 'b):
  mem (rng (rem x m)) x' => mem (rng m) x'.
proof. by rewrite rng_rm in_rng=> [x0] [_ h]; exists x0. qed.
