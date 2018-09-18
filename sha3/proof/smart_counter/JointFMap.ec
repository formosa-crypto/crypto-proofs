require import SmtMap.

(*****) import Finite FSet List.

op (+) (m1 m2 : ('a,'b) fmap) : ('a,'b) fmap =
  ofmap (Map.offun (fun x=> if x \in m2 then m2.[x] else m1.[x])).

lemma joinE ['a 'b] (m1 m2 : ('a,'b) fmap) (x : 'a):
  (m1 + m2).[x] = if x \in m2 then m2.[x] else m1.[x].
proof.
rewrite /(+) getE ofmapK /= 2:Map.getE 2:Map.offunK //.
apply/finiteP=> /=; exists (elems (fdom m1) ++ elems (fdom m2))=> x0 /=.
rewrite Map.getE Map.offunK /= mem_cat -!memE !mem_fdom !domE.
by case: (m2.[x0]).
qed.

lemma mem_join ['a 'b] (m1 m2 : ('a,'b) fmap) (x : 'a):
  x \in (m1 + m2) <=> x \in m1 \/ x \in m2.
proof. by rewrite domE joinE !domE; case: (m2.[x]). qed.