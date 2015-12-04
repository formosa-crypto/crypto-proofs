(* ------------------------- Auxiliary Lemmas ------------------------- *)

require import Bool Int List.

(* go in Int.ec? *)
lemma leltz (y x z : int) : x <= y < z => x < z.
proof.
move=> [/lez_eqVlt [-> // | lt_xy lt_yz]]; exact (ltz_trans y).
qed.

(* go in Int.ec? *)
lemma ltlez (y x z : int) : x < y <= z => x < z.
proof.
move=> [lt_xy /lez_eqVlt [<- // | lt_yz]]; exact (ltz_trans y).
qed.

(* go in List.ec? *)
lemma last_rev ['a] (x0 : 'a) (xs : 'a list) :
  last x0 (rev xs) = head x0 xs.
proof.
elim xs=> [| x xs ih]; [rewrite rev_nil // | rewrite rev_cons lastrcons //].
qed.

(* go in List.ec? *)
lemma head_nonnil ['a] (x0 : 'a) (xs : 'a list) :
  head x0 xs <> x0 => xs <> [].
proof. case (xs)=> //. qed.
