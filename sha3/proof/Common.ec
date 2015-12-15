(* -------------------------------------------------------------------- *)
require import Option Fun Pair Int IntExtra IntDiv Real List NewDistr.
require import Ring StdRing StdOrder StdBigop BitEncoding.
require (*--*) FinType BitWord LazyRP Monoid.
(*---*) import IntID IntOrder Bigint Bigint.BIA IntDiv Dprod.

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

clone export LazyRP as Perm with
  type D <- block * capacity,
  op   d <- bdistr * Capacity.cdistr
rename
  [module type] "RP" as "PRIMITIVE"
  [module] "P" as "Perm".

(* ------------------------- Padding/Unpadding ------------------------ *)

op chunk (bs : bool list) = BitChunking.chunk r bs.

op mkpad (n : int) =
  true :: rcons (nseq ((-(n+2)) %% r) false) true.

op pad (s : bool list) =
  s ++ mkpad (size s).

op unpad (s : bool list) =
  if !last false s then None else
  let i = index true (behead (rev s)) in
  if i + 1 = size s then None
  else let n = size s - (i + 2) in
       if i = (-(n+2)) %% r then Some (take n s) else None.

lemma rev_mkpad n : rev (mkpad n) = mkpad n.
proof. by rewrite /mkpad rev_cons rev_rcons rev_nseq. qed.

lemma last_mkpad b n : last b (mkpad n) = true.
proof. by rewrite !(last_cons, last_rcons). qed.

lemma head_mkpad b n : head b (mkpad n) = true.
proof. by []. qed.

lemma last_pad b s : last b (pad s) = true.
proof. by rewrite last_cat last_mkpad. qed.

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
by rewrite -(addrA _ 2) /= modzE; ring.
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

lemma chunk_cat (xs ys : bool list) :
  r %| size xs => chunk (xs ++ ys) = chunk xs ++ chunk ys.
proof. by apply/BitChunking.chunk_cat/gt0_r. qed.

lemma padK : pcancel pad unpad.
proof.
move=> s @/unpad; rewrite last_pad /= rev_cat rev_mkpad.
pose i := index _ _.
have ^iE {1 2}->: i = (-(size s + 2)) %% r.
  rewrite /i behead_cat //= index_cat {1}/mkpad /= mem_rcons /=.
  by rewrite index_true_behead_mkpad.
pose b := _ = size _; case b => @/b - {b}.
  rewrite modNz ?gt0_r ?ltr_spaddr ?size_ge0 //.
  rewrite -(addrA _ 2) size_pad (addrC _ r) -!addrA => /addrI.
  rewrite addrCA /= -subr_eq0 -opprD oppr_eq0 addrC -divz_eq.
  by rewrite addz_neq0 ?size_ge0.
move=> sz {sz}.
have -> : size (pad s) - (i + 2) + 2 = size (pad s) - i by ring.
pose b := _ = _ %% r; case b=> @/b - {b}; last first.
have -> // : size s + 2 = size (pad s) - i
  by rewrite /pad size_cat size_mkpad iE #ring.
move=> sz {sz} /=; rewrite iE -size_mkpad /pad size_cat addrK.
by rewrite take_cat /= take0 cats0.
qed.

lemma unpadK : ocancel unpad pad.
proof.
move=> s @/unpad; case: (last false s)=> //=.
elim/last_ind: s=> //= s b ih {ih}; rewrite last_rcons => hb.
rewrite rev_rcons /= size_rcons -(inj_eq _ (addIr (-1))) /= ?addrK.
pose i := index _ _; case: (i = size s)=> // ne_is @/pad.
have [ge0_i lt_siz_s_i] : 0 <= i < size s.
  have le_siz_s_i : i <= size s by rewrite /i - size_rev index_size.
  split=> [| _]; [rewrite index_ge0 | rewrite ltr_neqAle //].
have -> : size s + 1 - (i + 2) + 2 = size s - i + 1 by ring.
have -> : size s + 1 - (i + 2) = size s - i - 1 by ring.
case: (i = (-(size s - i + 1)) %% r) => [iE | //].
pose j := size s - i - 1; apply/eq_sym.
rewrite -{1}(cat_take_drop j (rcons s b)) eqseq_cat //=.
rewrite size_take; first rewrite /j subr_ge0.
  rewrite - (ler_add2r i) - addrA addNr /= lez_add1r //.
rewrite {2}/j size_rcons ltr_subl_addr ?ltr_spaddr //=.
  rewrite ler_add2l - ler_oppl (ler_trans 0) // lerN10.
rewrite -cats1 drop_cat {1}/j ltr_subl_addr ler_lt_add //=.
  rewrite ltr_oppl (ltr_le_trans 0) 1:ltrN10 //.
rewrite /mkpad -cats1 -cat_cons hb; congr.
have [ge0_j le_siz_j] : 0 <= j < size s.
  rewrite /j; split=> [| _].
  rewrite - (ler_add2r 1) /= - addrA addNr /= - (ler_add2r i)
          - addrA addNr /= lez_add1r //.
  rewrite - addrA - opprD - (ltr_add2r (i + 1)) - addrA addrN /=
          ltz_addl (ler_lt_trans i) // ltz_addl ltr01.
rewrite (drop_nth false) //.
have -> : nth false s j = true
  by rewrite /j - addrA - opprD - nth_rev // nth_index //
             - index_mem size_rev //.
congr.
have size_drop : size (drop (j + 1) s) = (-(j + 2)) %% r.
  rewrite size_drop; 1:rewrite (ler_trans j) //ler_addl ler01.
  rewrite max_ler /j.
  have -> // : size s - (size s - i - 1 + 1) = i by ring.
  have -> : size s - (size s - i - 1 + 1) = i by ring.
  have -> : -(size s - i - 1 + 2) = -(size s - i + 1).
  ring. rewrite - iE //.
apply (eq_from_nth false).
rewrite size_drop size_nseq.
rewrite max_ler // 1:modz_ge0 gtr_eqF ?gt0_r //.
move=> k [ge0k lt_size_drop_k]; rewrite size_drop in lt_size_drop_k.
rewrite nth_nseq; first split=> // _; rewrite - size_drop //.
rewrite nth_drop // 1:(ler_trans j) // 1:lez_addl 1:ler01.
rewrite /j.
have -> : size s - i - 1 + 1 + k = size s - ((i - k - 1) + 1) by ring.
have i_min_k_min1_rng {size_drop} : 0 <= i - k - 1 < i.
  rewrite iE; pose sz := (-(size s - i + 1)) %% r.
  split=> [| _].
  rewrite - (ler_add2r (k + 1)) /=.
  have -> @/sz : sz - k - 1 + (k + 1) = sz by ring.
  have -> : -(size s - i + 1) = -(size s - i - 1 + 2) by ring.
  rewrite - /j addrC lez_add1r //.
  rewrite -(ltr_add2r (k + 1)).
  have -> : sz - k - 1 + (k + 1) = sz by algebra.
  rewrite  ltr_addl ltzS //.
rewrite - nth_rev //.
  split=> [| _ //].
  elim i_min_k_min1_rng=> //.
  rewrite (ltr_trans i) //; elim i_min_k_min1_rng=> //.
have -> :
  (nth false (rev s) (i - k - 1) = false) =
  (nth false (rev s) (i - k - 1) <> true) by smt ml=0.
rewrite (before_index false) //.
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
move=> xs_ends_not_b0 ge0_n; rewrite /strip /extend /=.
rewrite rev_cat rev_nseq size_cat size_nseq max_ler // -addzA.
have head_rev_xs_neq_b0 : head b0 (rev xs) <> b0 by rewrite - last_rev revK //.
have -> : rev xs = head b0 (rev xs) :: behead (rev xs).
  by rewrite head_behead //; case: (rev xs) head_rev_xs_neq_b0.
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
  extend (strip xs).`1 (strip xs).`2 = xs.
proof.
rewrite /extend /strip eq_sym /=; pose i := find _ _.
rewrite -{1}(cat_take_drop (size xs - i) xs); congr.
have [ge0_i le_ixs]: 0 <= i <= size xs.
  by rewrite find_ge0 -size_rev find_size.
have sz_drop: size (drop (size xs - i) xs) = i.
  rewrite size_drop ?subr_ge0 // opprD opprK.
  by rewrite addrA /= max_ler.
apply/(eq_from_nth b0) => [|j]; rewrite ?size_nseq ?max_ler //.
rewrite sz_drop=> -[ge0_j lt_ji]; rewrite nth_nseq //.
rewrite nth_drop ?subr_ge0 // -{1}revK nth_rev ?size_rev.
  rewrite addr_ge0 ?subr_ge0 //= -ltr_subr_addr.
  by rewrite ltr_add2l ltr_opp2.
have @/predC1 /= ->// := (before_find b0 (predC1 b0)).
pose s := (_ - _)%Int; rewrite -/i (_ : s = i - (j+1)) /s 1:#ring.
by rewrite subr_ge0 -ltzE lt_ji /= ltr_snaddr // oppr_lt0 ltzS.
qed.

(*------------------------------ Validity ----------------------------- *)

(* in TopLevel *)
op valid_toplevel (_ : bool list) = true.

(* in Block *)
op valid_block (xs : block list) = unpad_blocks xs <> None.

(* in Absorb *)
op valid_absorb (xs : block list) =
  let (ys, _) = strip xs in valid_block ys.
