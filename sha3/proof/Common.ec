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
  fun bs => foldl chunk_aux ([], []) bs.

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
  fun xs =>
    if xs = []
    then None
    else let bs = w2bits(last b0 xs) in
         let ys = take (size xs - 1) xs in
         let ocs = unpad_aux bs in
         if ocs = None
         then if bs = nseq (r - 1) false ++ [true] && ys <> []
              then let ds = w2bits(last b0 ys) in
                   let ws = take (size ys - 1) ys in
                   if !(last false ds)
                   then None
                   else Some(flatten(map w2bits ws) ++
                             take (size ds - 1) ds)
              else None
         else Some(flatten(map w2bits ys) ++ oget ocs).

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
