(* -------------------------------------------------------------------- *)
require import Option Fun Pair Int IntExtra IntDiv Real List NewDistr.
require import Ring StdRing StdOrder StdBigop BitEncoding.
require (*--*) FinType BitWord LazyRP Monoid.
(*---*) import IntID IntOrder Bigint Bigint.BIA IntDiv.

(* -------------------------------------------------------------------- *)
op r : { int | 2 <= r } as ge2_r.
op c : { int | 0 <  c } as gt0_c.

type block.    (* ~ bitstrings of size r *)
type capacity. (* ~ bitstrings of size c *)

(* -------------------------------------------------------------------- *)
lemma gt0_r: 0 < r.
proof. by apply/(ltr_le_trans 2)/ge2_r. qed.

lemma ge0_r: 0 <= r.
proof. by apply/ltrW/gt0_r. qed.

(* -------------------------------------------------------------------- *)
clone BitWord as Capacity with
  type word <- capacity,
    op n    <- c
  proof gt0_n by apply/gt0_c

  rename "dword" as "cdistr"
         "zerow" as "c0".

clone export BitWord as Block with
  type word <- block,
    op n    <- r
  proof gt0_n by apply/gt0_r

  rename "dword" as "bdistr"
         "zerow" as "b0".

(* -------------------------------------------------------------------- *)
op ( * ): 'a distr -> 'b distr -> ('a * 'b) distr.

clone export LazyRP as Perm with
  type D <- block * capacity,
  op   d <- bdistr * Capacity.cdistr
rename
  [module type] "RP" as "PRIMITIVE"
  [module] "P" as "Perm".

(* ------------------------- Padding/Unpadding ------------------------ *)

(* What about this (and the comment applies to other functions): *)

op chunk (bs : bool list) = BitChunking.chunk r bs.

op mkpad (n : int) =
  true :: rcons (nseq ((-(n+2)) %% r) false) true.

op pad (s : bool list) =
  s ++ mkpad (size s).

op unpad (s : bool list) =
  if !last false s then None else
  let i = index true (behead (rev s)) in
  if i+1 = size s then None else Some (take (size s - (i+2)) s).

lemma rev_mkpad n : rev (mkpad n) = mkpad n.
proof. by rewrite /mkpad rev_cons rev_rcons rev_nseq. qed.

lemma last_mkpad b n : last b (mkpad n) = true.
proof. by rewrite !(lastcons, lastrcons). qed.

lemma head_mkpad b n : head b (mkpad n) = true.
proof. by []. qed.

lemma last_pad b s : last b (pad s) = true.
proof. by rewrite lastcat last_mkpad. qed.

lemma size_mkpad n : size (mkpad n) = (-(n+2)) %% r + 2.
proof.
rewrite /mkpad /= size_rcons size_nseq max_ler.
by rewrite modz_ge0 gtr_eqF ?gt0_r. by ring.
qed.

lemma size_pad s: size (pad s) = (size s + 1) %/ r * r + r.
proof.
rewrite /pad /mkpad size_cat /= size_rcons size_nseq.
rewrite max_ler 1:modz_ge0 1:gtr_eqF ?gt0_r // (addrCA 1).
rewrite modNz ?gt0_r ?ltr_spaddr ?size_ge0 //.
by rewrite (@subrE (size s + 2)) -(addrA _ 2) /= modzE; ring.
qed.

lemma size_pad_dvd_r s: r %| size (pad s).
proof. by rewrite size_pad dvdzD 1:dvdz_mull dvdzz. qed.

lemma index_true_behead_mkpad n :
  index true (behead (mkpad n)) = (-(n + 2)) %% r.
proof.
rewrite /mkpad -cats1 index_cat mem_nseq size_nseq.
by rewrite max_ler // modz_ge0 gtr_eqF ?gt0_r.
qed.

lemma size_chunk bs : size (chunk bs) = size bs %/ r.
proof. by apply/BitChunking.size_chunk/gt0_r. qed.

lemma in_chunk_size bs b: mem (chunk bs) b => size b = r.
proof. by apply/BitChunking.in_chunk_size/gt0_r. qed.

lemma chunkK bs : r %| size bs => flatten (chunk bs) = bs.
proof. by apply/BitChunking.chunkK/gt0_r. qed.

lemma padK : pcancel pad unpad.
proof.
move=> s @/unpad; rewrite last_pad /= rev_cat rev_mkpad.
pose i := index _ _; have ^iE {1}->: i = (-(size s + 2)) %% r.
  rewrite /i behead_cat //= index_cat {1}/mkpad /= mem_rcons /=.
  by rewrite index_true_behead_mkpad.
pose b := _ = size _; case: b => @/b - {b}.
  rewrite modNz ?gt0_r ?ltr_spaddr ?size_ge0 //.
  rewrite (subrE (size s + 2)) -(addrA _ 2) size_pad.
  rewrite (addrC _ r) 2!subrE -!addrA => /addrI; rewrite addrCA /=.
  rewrite -subr_eq0 -opprB subrE opprK -divz_eq oppr_eq0.
  by rewrite addz_neq0 ?size_ge0.
move=> _ /=; rewrite iE -size_mkpad /pad size_cat addrK_sub.
by rewrite take_cat /= take0 cats0.
qed.

lemma unpadK : ocancel unpad pad.
proof.
move=> s @/unpad; case: (last false s) => //=.
elim/last_ind: s=> //= s b ih {ih}; rewrite lastrcons => hb.
rewrite rev_rcons /= size_rcons -(inj_eq _ (addIr (-1))) /= ?addrK.
pose i := index _ _; case: (i = size s) => //=.
move=> ne_is @/pad; pose j := _ - (i+2); apply/eq_sym.
rewrite -{1}(cat_take_drop j (rcons s b)) eqseq_cat //=.
rewrite size_take; first rewrite /j subr_ge0.
  (have ->: 2=1+1 by done); rewrite addrA -ltzE ltr_add2r.
  by rewrite ltr_neqAle ne_is /= /i -size_rev index_size.
rewrite {2}/j size_rcons ltr_subl_addr ?ltr_spaddr //=.
  by rewrite /i index_ge0.
rewrite -cats1 drop_cat {1}/j ltr_subl_addr ler_lt_add //=.
  by rewrite ltzE /= ler_addr // /i index_ge0.
rewrite /mkpad -cats1 -cat_cons hb; congr.
admit.                          (* missing results on drop/take *)
qed.

lemma chunk_padK : pcancel (chunk \o pad) (unpad \o flatten).
proof. by move=> s @/(\o); rewrite chunkK 1:size_pad_dvd_r padK. qed.


lemma mkseq_add (f:int -> 'a) (n m:int): 
   0 <= n => 0 <= m =>
   mkseq f (n+m) = mkseq f n ++ mkseq (fun i => f (n+i)) m.
admit.
qed.


lemma flattenK bs : (forall b, mem bs b => size b = r) => chunk (flatten bs) = bs.
proof.
  elim:bs=> [_|x xs Hrec Hs]. by rewrite flatten_nil /chunk /= div0z mkseq0.
  rewrite flatten_cons /chunk size_cat Hs 1://.
  cut /= -> :=(divzMDl 1 (size (flatten xs)) r);1:by apply /gtr_eqF/gt0_r.
  rewrite mkseq_add // 1:divz_ge0 1:gt0_r 1:size_ge0 (mkseqS _ 0) 1:// mkseq0 /=.
  rewrite drop0 take_cat Hs //= take0 cats0 /= -{3}Hrec;1:by move=> b Hb;apply Hs;right.
  apply eq_in_mkseq => /= i Hi; rewrite IntID.mulrDr /= drop_cat (Hs x) //=.
  cut ->/=:!(r + r * i < r);smt ml=0 w=gt0_r.
qed.

op blocks2bits (xs:block list) : bool list = 
  flatten (map w2bits xs).

op bits2blocks (xs:bool list) : block list =
  map bits2w (chunk xs).

lemma block2bitsK : cancel blocks2bits bits2blocks.
proof.
  move=> xs;rewrite /blocks2bits /bits2blocks flattenK.
  + by move=> b /mapP [x [_ ->]];rewrite /w2bits -Array.sizeE size_word.
  rewrite -map_comp -{2}(map_id xs) /(\o) /=;apply eq_map=> @/idfun x /=;apply oflistK.
qed.


(*
(* -------------------------------------------------------------------- *)
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
have -> : flatten(x :: xs, cs) = w2bits x ++ flatten (xs, cs) by (* smt *) admit.
rewrite foldl_cat.
rewrite foldl_chunk_aux_new_block.
smt ml=0.
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
admit.
qed.

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
*)
(* ------------------------ Extending/Stripping ----------------------- *)


op valid_block (xs : block list) =
  unpad (flatten (map w2bits xs)) <> None.
(* extend xs n returns None if xs doesn't unpad successfully;
   otherwise, it returns the result of adding n copies of b0 to the
   end of xs (n < 0 is treated as n = 0) *)

op extend (xs:block list) (n:int): block list option =
  if unpad (flatten (map w2bits xs)) = None then None
  else Some(xs ++ nseq n b0).

op extend_uncur (p:block list * int): block list option =
  extend p.`1 p.`2.

(* strip returns None if removing the longest suffix of zerow's from its
   argument yields a block list that cannot be unpadded; otherwise, it
   removes the longest suffix of zerow's from its argument and returns
   the pair of the resulting block list with the number of zerow's
   removed *)
op strip (xs:block list): (block list * int)option =
    let ys = rev xs in
    let i = find (fun x => x <> b0) ys in
    if i = size xs then None
    else 
      let zs = rev(drop i ys) in
      if valid_block zs then Some(zs, i) 
      else None.


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
