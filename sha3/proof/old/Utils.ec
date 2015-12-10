(** These should make it into the standard libs **)
require import Option Pair List FSet NewFMap.

(* -------------------------------------------------------------------- *)

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
proof. by rewrite rng_rm in_rng=> -[x0] [_ h]; exists x0. qed.


(* -------------------------------------------------------------------- *)
  (* In NewFMap *)

op reindex (f : 'a -> 'c) (m : ('a, 'b) fmap) =
  NewFMap.oflist (map (fun (x : 'a * 'b) => (f x.`1,x.`2)) (elems m))
  axiomatized by reindexE.


  
lemma dom_reindex (f : 'a -> 'c) (m : ('a, 'b) fmap) x:
  mem (dom (reindex f m)) x <=> mem (image f (dom m)) x.
proof.
  rewrite reindexE dom_oflist imageP mapP /fst; split.
    move=> [[x' y] [+ ->>]].
    rewrite mapP=> -[[x0 y0]] /= [h [->> ->>]] {x' y}.
    by exists x0; rewrite domE mem_oflist mapP /fst; exists (x0,y0).
  move=> [a] [a_in_m <<-].
  exists (f a,oget m.[a])=> /=; rewrite mapP /=.
  exists (a,oget m.[a])=> //=.
  have:= a_in_m; rewrite in_dom; case {-1}(m.[a]) (eq_refl m.[a])=> //=.
  by move=> y; rewrite getE mem_assoc_uniq 1:uniq_keys.
qed.

require import Fun.

lemma reindex_injective_on (f : 'a -> 'c) (m : ('a, 'b) fmap):
  (forall x y, mem (dom m) x => f x = f y => x = y) =>
  (forall x, m.[x] = (reindex f m).[f x]).
proof.
  move=> f_pinj x.
  pose s:= elems (reindex f m).
  case (assocP s (f x)).
    rewrite -dom_oflist {1}/s elemsK dom_reindex imageP.
    move=> [[a]] [] /f_pinj h /(h x) ->> {a}.
    rewrite !getE.
    move=> [y] [+ ->].
    rewrite /s reindexE.
    pose s':= map (fun (x : 'a * 'b) => (f x.`1,x.`2)) (elems m).
    have <- := (perm_eq_mem _ _ (oflistK s')).
    (** FIXME: make this a lemma **)
    have h' /h': forall (s : ('c * 'b) list) x, mem (reduce s) x => mem s x.
      rewrite /reduce=> s0 x0; rewrite -{2}(cat0s s0); pose acc:= [].
      elim s0 acc x0=> {s'} [acc x0 /=|x' s' ih acc x0 /=].
        by rewrite cats0.
      move=> /ih; rewrite -cat1s catA cats1 !mem_cat=> -[|-> //=].
      rewrite /augment; case (mem (map fst acc) x'.`1)=> _ h'; left=> //.
      by rewrite mem_rcons /=; right.
    rewrite /s' mapP=> -[[a' b']] /= [xy_in_m []].
    rewrite eq_sym. have h0 /h0 ->> <<- {a' b'}:= f_pinj a' x _; 1:by smt.
    by apply/mem_assoc_uniq; 1:exact uniq_keys.
  rewrite -mem_oflist {1}/s -domE=> -[] h; have := h; rewrite dom_reindex.
  rewrite imageP=> h'. have {h'} h': forall (a : 'a), !mem (dom m) a \/ f a <> f x by smt.
  have /= := h' x.
  rewrite in_dom !getE /=.
  by move=> -> ->.
qed.

lemma reindex_injective (f : 'a -> 'c) (m : ('a, 'b) fmap):
  injective f =>
  (forall x, m.[x] = (reindex f m).[f x]).
proof. by move=> f_inj; apply/reindex_injective_on=> + + _. qed.
