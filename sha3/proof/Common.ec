(* -------------------------------------------------------------------- *)
require import Option Fun Pair Int IntExtra IntDiv Real List NewDistr.
require import Ring StdRing StdOrder StdBigop BitEncoding.
require (*--*) FinType BitWord LazyRP Monoid.
(*---*) import IntID IntOrder Bigint Bigint.BIA IntDiv.
require import Auxiliary.

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

lemma flattenK bs :
  (forall b, mem bs b => size b = r) => chunk (flatten bs) = bs.
proof. by apply/BitChunking.flattenK/gt0_r. qed.

op blocks2bits (xs:block list) : bool list = 
  flatten (map w2bits xs).

op bits2blocks (xs:bool list) : block list =
  map bits2w (chunk xs).

lemma blocks2bitsK : cancel blocks2bits bits2blocks.
proof.
  move=> xs;rewrite /blocks2bits /bits2blocks flattenK.
  + by move=> b /mapP [x [_ ->]];rewrite size_tolist.
  rewrite -map_comp -{2}(map_id xs) /(\o) /=;apply eq_map=> @/idfun x /=;
  apply oflistK.
qed.

lemma bits2blocksK (bs : bool list) :
  r %| size bs => blocks2bits(bits2blocks bs) = bs.
proof.
move=> siz_bs_div_r.
rewrite /blocks2bits /bits2blocks -map_comp.
have map_tolistK :
  forall (xss : bool list list),
  (forall (xs : bool list), mem xss xs => size xs = r) =>
  map (w2bits \o bits2w) xss = xss.
  + elim => [// | xs yss ih mem_xs_cons_yss_siz_r /=].
  + split.
  + apply tolistK; rewrite mem_xs_cons_yss_siz_r //.
  + apply ih => zs mem_zss_zs.
  + by rewrite mem_xs_cons_yss_siz_r /=; first right; assumption.
rewrite map_tolistK; [apply in_chunk_size | exact chunkK].
qed.

op pad2blocks : bool list -> block list  = bits2blocks \o pad.
op unpad_blocks : block list -> bool list option = unpad \o blocks2bits.

lemma pad2blocksK : pcancel pad2blocks unpad_blocks.
proof.
move=> xs.
rewrite /pad2blocks /unpad_blocks /(\o) bits2blocksK
        1:size_pad_dvd_r padK //.
qed.

lemma unpadBlocksK : ocancel unpad_blocks pad2blocks.
proof.
move=> xs; rewrite /pad2blocks /unpad_blocks /(\o).
pose bs := blocks2bits xs.
case (unpad bs = None) => [-> // | unpad_bs_neq_None].
have unpad_bs : unpad bs = Some(oget(unpad bs))
  by move: unpad_bs_neq_None; case (unpad bs)=> //.
rewrite unpad_bs /=.
have -> : pad(oget(unpad bs)) = bs by rewrite - {2} (unpadK bs) unpad_bs //.
rewrite /bs blocks2bitsK //.
qed.

(* ------------------------ Extending/Stripping ----------------------- *)

op extend (xs : block list) (n : int) =
  xs ++ nseq n b0.

op strip (xs : block list) =
  let i = find (fun x => x <> b0) (rev xs) in
  (take (size xs - i) xs, i).

lemma extendK (xs : block list) (n : int) :
  last b0 xs <> b0 => 0 <= n => strip(extend xs n) = (xs, n).
proof.
move=> xs_ends_not_b0 ge0_n.
rewrite /strip /extend /= rev_cat rev_nseq size_cat size_nseq max_ler //
        subzE - addzA.
have head_rev_xs_neq_b0 : head b0 (rev xs) <> b0 by rewrite - last_rev revK //.
have -> : rev xs = head b0 (rev xs) :: behead (rev xs)
  by rewrite head_behead //; exact (head_nonnil b0 (rev xs)).
pose p := fun (x : block) => x <> b0.
have has_p_full : has p (nseq n b0 ++ head b0 (rev xs) :: behead (rev xs))
  by apply has_cat; right; simplify; left.
have not_has_p_nseq : ! has p (nseq n b0) by rewrite has_nseq.
have -> : find p (nseq n b0 ++ head b0 (rev xs) :: behead (rev xs)) = n.
  rewrite find_cat not_has_p_nseq /= size_nseq max_ler //.
  have -> // : p (head b0 (rev xs)) by trivial.
by rewrite (addzC n) addNz /= take_size_cat.
qed.

lemma stripK (xs : block list) :
  let (ys, n) = strip xs in
  extend ys n = xs.
proof.
rewrite /strip /extend /=.
pose p := fun x => x <> b0.
pose i := find p (rev xs).
have [i_low i_upp] : 0 <= i <= size xs
  by split; [apply find_ge0 | move=> _; rewrite - size_rev find_size].
have i_upp' : 0 <= size xs - i by rewrite subz_ge0 //.
have {3} <- :
  take (size xs - i) xs ++ drop (size xs - i) xs = xs by apply cat_take_drop.
have siz_drop : size(drop (size xs - i) xs) = i.
  rewrite size_drop 1 : i_upp'.
  have -> : size xs - (size xs - i) = i by algebra.
  apply max_ler; first apply i_low.
have drop_eq_b0 :
  forall (j : int),
  0 <= j < i => nth b0 (drop (size xs - i) xs) j = b0.
    move=> j [j_low j_upp].
    have [i_min_j_min_1_low i_min_j_min_1_upp] : 0 <= i - j - 1 < i.
      split => [|_].
      rewrite - subz_gt0 - lez_add1r in j_upp; rewrite subz_ge0 //.
      rewrite - subz_gt0.
      have -> : i - (i - j - 1) = j + 1 by algebra.
      by rewrite - lez_add1r addzC addzA lez_add2r.
    rewrite nth_drop //.
    have -> : size xs - i + j = size xs - ((i - j - 1) + 1) by algebra.
    rewrite - (nth_rev b0 (i - j - 1) xs).
    split=> [//| _]; exact (ltlez i).
    have -> :
      (nth b0 (rev xs) (i - j - 1) = b0) = !p(nth b0 (rev xs) (i - j - 1))
      by trivial.
    exact before_find.
have <- // : drop (size xs - i) xs = nseq i b0.
  apply (eq_from_nth b0)=> [| j rng_j].
  rewrite siz_drop size_nseq max_ler //.
  rewrite siz_drop in rng_j; rewrite nth_nseq //; exact drop_eq_b0.
qed.

(*------------------------------ Validity ----------------------------- *)

(* in TopLevel *)
op valid_toplevel (_ : bool list) = true.

(* in Block *)
op valid_block (xs : block list) = unpad_blocks xs <> None.

(* in Absorb *)
op valid_absorb (xs : block list) =
  let (ys, _) = strip xs in valid_block ys.
