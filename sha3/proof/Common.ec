(* -------------------------------------------------------------------- *)
require import Option Fun Pair Int IntExtra Real List NewDistr.
require (*--*) FinType LazyRP Monoid.

(* -------------------------------------------------------------------- *)
theory BitWord.
type bword.

op zero : bword.
op (^)  : bword -> bword -> bword.

clone include Monoid
  with
    type t   <- bword,
      op idm <- zero,
      op (+) <- (^)
  proof Axioms.* by admit.

clone FinType with type t <- bword
  proof * by admit.

op w2bits : bword -> bool list.
op bits2w : bool list -> bword.
op size   : { int | 0 < size } as gt0_size.

lemma w2bitsK : cancel w2bits bits2w.
proof. admit. qed.

lemma bits2wK (s : bool list) :
  size s = size => w2bits (bits2w s) = s.
proof. admit. qed.

lemma w2bits_size (x : bword) : size(w2bits x) = size.
proof. admit. qed.

op uniform : bword distr =
  MUniform.duniform FinType.enum.
end BitWord.

(* -------------------------------------------------------------------- *)
op r : { int | 0 < r } as gt0_r.
op c : { int | 0 < c } as gt0_c.

type block.    (* ~ bitstrings of size r *)
type capacity. (* ~ bitstrings of size c *)

(* -------------------------------------------------------------------- *)
clone BitWord as Capacity with
  type bword <- capacity,
    op size  <- c
  proof * by apply/gt0_c

  rename
    [op] "zero" as "c0"
    [op] "uniform" as "cdistr".

clone export BitWord as Block with
  type bword <- block,
    op size  <- r
  proof * by apply/gt0_r

  rename
    [op] "zero" as "b0"
    [op] "uniform" as "bdistr".

op ( * ): 'a NewDistr.distr -> 'b NewDistr.distr -> ('a * 'b) Pervasive.distr.

clone export LazyRP as Perm with
  type D <- block * capacity,
  op d <- bdistr * Capacity.cdistr
rename
  [module type] "RP" as "PRIMITIVE"
  [module] "P" as "Perm".

(* ------------------------- Padding/Unpadding ------------------------ *)

(* if size cs < r, then size (chunk_aux (xs, cs) b).`2 < r *)
op chunk_aux : block list * bool list -> bool -> block list * bool list =
  fun p b =>
    let (xs, cs) = p in
    let ds = rcons cs b in
    if size ds = r
    then (rcons xs (bits2w ds), [])
    else (xs, ds).

(* size (chunk bs).`2 < r *)
op chunk : bool list -> block list * bool list =
  foldl chunk_aux ([], []).

op flatten (p : block list * bool list) : bool list =
  flatten(map w2bits p.`1) ++ p.`2.

lemma chunk_aux_flatten (xs : block list, cs : bool list, bs : bool list) :
  size cs < r =>
  flatten (foldl chunk_aux (xs, cs) bs) =
  flatten(map w2bits xs) ++ cs ++ bs.
proof.
move: bs xs cs.
elim.
(* basis step *)
move=> xs cs siz_cs_lt_r.
have -> : foldl chunk_aux (xs, cs) [] = (xs, cs) by trivial.
rewrite /flatten /=.
rewrite - catA.
rewrite cats0 //.
(* inductive step *)
move=> x l IH xs cs siz_cs_lt_r /=.
rewrite {2} /chunk_aux /=.
case (size cs = r - 1) => siz_cs_eq_r_min1.
have -> : size(rcons cs x) = r by smt.
simplify.
have -> :
  flatten (map w2bits xs) ++ cs ++ x :: l =
  flatten (map w2bits xs) ++ (rcons cs x) ++ l by smt.
rewrite (IH (rcons xs (bits2w (rcons cs x))) []).
  smt.  
have -> :
  map w2bits (rcons xs (bits2w (rcons cs x))) =
  rcons (map w2bits xs) (rcons cs x) by smt.
rewrite - cats1.
smt.
have : size cs < r - 1 by smt.
move=> siz_cs_lt_r_min1.
clear siz_cs_lt_r siz_cs_eq_r_min1.
have : !(size(rcons cs x) = r) by smt.
move=> H.
rewrite H /=.
rewrite (IH xs (rcons cs x)).
  smt.
smt.
qed.

lemma chunk_flatten : cancel chunk flatten.
proof.
rewrite /cancel => p.
rewrite /chunk.
rewrite chunk_aux_flatten.
smt.
smt.
qed.

lemma foldl_chunk_aux_add_bits (ys : block list, cs, ds : bool list) :
  size ds + size cs < r =>
  foldl chunk_aux (ys, ds) cs = (ys, ds ++ cs).
proof.
move: ys ds.
elim cs.
smt.
move=> c cs IH ys ds siz_ys_plus_c_cs_lt_r.
have -> :
  foldl chunk_aux (ys, ds) (c :: cs) =
  foldl chunk_aux (ys, rcons ds c) cs.
  simplify.
  have -> : chunk_aux (ys, ds) c = (ys, rcons ds c).
    rewrite /chunk_aux.
    simplify.
    smt.
  reflexivity.
rewrite (IH ys (rcons ds c)).
smt.
smt.
qed.

lemma foldl_chunk_aux_new_block (ys : block list, cs, ds : bool list) :
  cs <> [] => size ds + size cs = r =>
  foldl chunk_aux (ys, ds) cs = (rcons ys (bits2w(ds ++ cs)), []).
proof.
move=> cs_nonnil siz.
cut cs_form : exists (es, fs : bool list),
  size es = size cs - 1 /\
  size fs = 1 /\
  cs = es ++ fs.
  exists (take (size cs - 1) cs), (drop (size cs - 1) cs).
  smt.
elim cs_form => es fs [H1 [H2 H3]].
cut fs_form : exists (f : bool), fs = [f].
  exists (nth false fs 0).
  smt.
elim fs_form => f H4.
rewrite H3 H4.
rewrite foldl_cat.
rewrite foldl_chunk_aux_add_bits.
smt.
cut -> : 
  foldl chunk_aux (ys, ds ++ es) [f] =
  chunk_aux (ys, ds ++ es) f.
  trivial.
rewrite /chunk_aux.
smt.
qed.

lemma flatten_chunk_aux (xs, ys : block list, cs : bool list) :
  size cs < r =>
  foldl chunk_aux (ys, []) (flatten(xs, cs)) = (ys ++ xs, cs).
proof.  
move: cs ys.
elim xs.
(* basis step *)
move=> cs ys siz_cs_lt_r.
have -> : flatten([], cs) = cs by smt.
rewrite foldl_chunk_aux_add_bits.
smt.
smt.
(* inductive step *)
move=> x xs IH cs ys siz_cs_lt_r.
have -> : flatten(x :: xs, cs) = w2bits x ++ flatten (xs, cs) by smt.
rewrite foldl_cat.
rewrite foldl_chunk_aux_new_block.
smt.
smt.
have -> : bits2w([] ++ w2bits x) = x by smt.
rewrite (IH cs (rcons ys x)).
assumption.
smt.
qed.

lemma flatten_chunk (xs, ys : block list, cs : bool list) :
  size cs < r =>
  chunk(flatten(xs, cs)) = (xs, cs).
proof.
move=> siz_cs_lt_r.
rewrite /chunk.
rewrite (flatten_chunk_aux xs [] cs).
assumption.
smt.
qed.

pred valid_block (xs : block list) =
  exists (ys : bool list, n : int),
  0 <= n < r /\
  flatten(map w2bits xs) = ys ++ [true] ++ nseq n false ++ [true].

op pad : bool list -> block list =
  fun bs =>
  let (xs, cs) = chunk bs in
  let siz_cs = size cs in (* siz_cs < r *)
  if 2 <= r - siz_cs
  then rcons xs
             (bits2w(cs ++
                     [true] ++
                     nseq (r - siz_cs - 2) false ++
                     [true]))
  else (* r - siz_cs = 1 *)
       xs ++ [bits2w(rcons cs true)] ++
       [bits2w(rcons (nseq (r - 1) false) true)].

(* unpad_aux returns None if its argument xs doesn't end with true and
   have at least one other occurrence of true; otherwise, it returns
   Some of the result of removing the shortest suffix of xs containing
   two occurrences of true *)
op unpad_aux : bool list -> bool list option =
  fun xs =>
    let ys = rev xs in
    if !(head false ys)
    then None
    else let zs = behead ys in
         let i = find ((=) true) zs in
         if i = size zs
         then None
         else Some(rev(drop (i + 1) zs)).

op unpad : block list -> bool list option =
  fun xs => unpad_aux(flatten(map w2bits xs)).

lemma pad_valid (bs : bool list) : valid_block(pad bs).
proof.

lemma valid_block (xs : block list) :
  unpad xs <> None <=> valid_block xs.
proof.
admit.
qed.

lemma pad_unpad : pcancel pad unpad.
proof.
rewrite /pcancel.
admit.
qed.

lemma unpad_pad : ocancel unpad pad.
proof.
rewrite /ocancel.
admit.
qed.

(* ------------------------ Extending/Stripping ----------------------- *)

(* extend xs n returns None if xs doesn't unpad successfully;
   otherwise, it returns the result of adding n copies of b0 to the
   end of xs (n < 0 is treated as n = 0) *)
op extend : block list -> int -> block list option =
  fun xs n =>
  if unpad xs = None
  then None
  else Some(xs ++ nseq n b0).

op extend_uncur : block list * int -> block list option =
  fun (p : block list * int) => extend p.`1 p.`2.

(* strip returns None if removing the longest suffix of b0's from its
   argument yields a block list that cannot be unpadded; otherwise, it
   removes the longest suffix of b0's from its argument and returns
   the pair of the resulting block list with the number of b0's
   removed *)
op strip : block list -> (block list * int)option =
  fun xs =>
    let ys = rev xs in
    let i = find (fun x => x <> b0) ys in
    if i = size xs
    then None
    else let zs = rev(drop i ys) in
         if unpad zs = None
         then None
         else Some(zs, i).

pred valid_absorb (xs : block list) =
  exists (ys : block list, n : int),
  0 <= n /\ valid_block ys /\ xs = ys ++ nseq n b0.

lemma valid_absorb (xs : block list) :
  strip xs <> None <=> valid_absorb xs.
proof.
admit.
qed.

lemma extend_strip (xs : block list, n : int) :
  oapp strip (Some(xs, max n 0)) (extend xs n) = Some(xs, max n 0).
proof.
admit.
qed.

lemma strip_extend (xs : block list) :
  oapp extend_uncur (Some xs) (strip xs) = Some xs.
proof.
admit.
qed.
