(* -------------------------------------------------------------------- *)

require import Option Fun Pair Int IntExtra IntDiv Real List NewDistr.
require import Ring StdRing StdOrder StdBigop BitEncoding.
require (*--*) FinType BitWord LazyRP Monoid.
(*---*) import IntID IntOrder Bigint Bigint.BIA IntDiv Dprod.
require import NewLogic.

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

lemma b0 : b0 = bits2w(nseq r false).
proof.
admit. (* FIXME *)
qed.

lemma bits2w_inj_eq (cs ds : bool list) :
  size cs = r => size ds = r => bits2w cs = bits2w ds <=> cs = ds.
proof.
admit. (* FIXME *)
qed.

lemma last_eq_rcons (x : 'a) (xs : 'a list) :
  last x xs = x => xs = [] \/ exists ys, xs = rcons ys x.
proof.
elim xs; smt ml=0.
qed.

lemma last_neq_rcons (y x : 'a) (xs : 'a list) :
  x <> y => last y xs = x => exists ys, xs = rcons ys x.
proof.
elim xs; smt ml=0.
qed.

(* -------------------------------------------------------------------- *)

clone export LazyRP as Perm with
  type D <- block * capacity,
  op   d <- bdistr * Capacity.cdistr
rename
  [module type] "RP" as "PRIMITIVE"
  [module] "P" as "Perm".

(* ------------------------- Padding/Unpadding ------------------------ *)

op chunk (bs : bool list) = BitChunking.chunk r bs.

op num0 (n : int) = (-(n + 2)) %% r.

op mkpad (n : int) = true :: rcons (nseq (num0 n) false) true.

op pad (s : bool list) = s ++ mkpad (size s).

op unpad (s : bool list) =
  if !last false s then None else
  let i = index true (behead (rev s)) in
  if i + 1 = size s then None
  else let n = size s - (i + 2) in
       if i = num0 n then Some (take n s) else None.

lemma rev_mkpad n : rev (mkpad n) = mkpad n.
proof. by rewrite /mkpad rev_cons rev_rcons rev_nseq. qed.

lemma last_mkpad b n : last b (mkpad n) = true.
proof. by rewrite !(last_cons, last_rcons). qed.

lemma head_mkpad b n : head b (mkpad n) = true.
proof. by []. qed.

lemma last_pad b s : last b (pad s) = true.
proof. by rewrite last_cat last_mkpad. qed.

lemma size_mkpad n : size (mkpad n) = num0 n + 2.
proof.
rewrite /mkpad /= size_rcons size_nseq max_ler.
by rewrite modz_ge0 gtr_eqF ?gt0_r. by ring.
qed.

lemma size_pad_equiv (m : int) :
  0 <= m => m + num0 m + 2 = (m + 1) %/ r * r + r.
proof.
move=> ge0_m.
by rewrite modNz 1:/# 1:gt0_r -(addrA _ 2) /= modzE #ring.
qed.

lemma num0_prop (m : int) :
  0 <= m => 0 <= num0 m < r /\ r %| (m + num0 m + 2).
proof.
move=> ge0_m. split. split=> [| _].
by rewrite modz_ge0 1:gtr_eqF 1:gt0_r. rewrite ltz_pmod gt0_r.
rewrite (size_pad_equiv m) // dvdzD 1:dvdz_mull dvdzz.
qed.

lemma num0_alt (n m : int) :
  0 <= m => 0 <= n < r => r %| (m + n + 2) => n = num0 m.
proof.
move=> ge0_m [ge0_n lt_rn] r_dvd_m_add_n_add2.
rewrite modNz 1:ltr_spaddr // 1:gt0_r.
have -> : m + 2 - 1 = ((m + n + 2) - (n + 1)) by algebra.
rewrite -modzDm; have -> /= : (m + n + 2) %% r = 0 by apply dvdzE.
rewrite modz_mod modNz 1:/# 1:gt0_r.
have -> : r - 1 - (r - 1 - (n + 1 - 1) %% r) = n %% r by algebra.
rewrite modz_small 1:gtr0_norm 1:gt0_r /#.
qed.

lemma size_pad_raw (s : bool list) :
  size (pad s) = size s + num0 (size s) + 2.
proof.
rewrite /pad /mkpad /= -cats1 -cat1s 2!catA 3!size_cat /=
        size_nseq 1:max_ler 1:modz_ge0 1:gtr_eqF 1:gt0_r // #ring.
qed.

lemma size_pad (s : bool list) :
  size (pad s) = (size s + 1) %/ r * r + r.
proof. by rewrite size_pad_raw size_pad_equiv 1:size_ge0. qed.

lemma size_pad_dvd_r s : r %| size (pad s).
proof. by rewrite size_pad dvdzD 1:dvdz_mull dvdzz. qed.

lemma pad_alt (s : bool list, n : int) :
  0 <= n < r => r %| (size s + n + 2) =>
  pad s = s ++ [true] ++ nseq n false ++ [true].
proof.
move=> [ge0_n lt_nr] mod.
rewrite /pad /mkpad /= -cats1 -cat1s 2!catA
        (num0_alt n (size s)) // size_ge0.
qed.

lemma index_true_behead_mkpad n :
  index true (behead (mkpad n)) = num0 n.
proof.
rewrite /mkpad -cats1 index_cat mem_nseq size_nseq.
by rewrite max_ler // modz_ge0 gtr_eqF ?gt0_r.
qed.

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
move=> sz {sz}; rewrite /num0.
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
elim/last_ind: s=> //= s b ih {ih}; rewrite last_rcons => ->.
rewrite rev_rcons /= size_rcons -(inj_eq _ (addIr (-1))) /= ?addrK.
pose i := index _ _; case: (i = size s)=> // ne_is @/pad @/num0.
have lt_is: i < size s by rewrite ltr_neqAle ne_is -size_rev index_size.
have [ge0_i lt_siz_s_i] : 0 <= i < size s.
  have le_siz_s_i : i <= size s by rewrite /i - size_rev index_size.
  split=> [| _]; [rewrite index_ge0 | rewrite ltr_neqAle //].
pose j := (size s + _ - _); case: (i = (-(j + 2)) %% r) => // iE.
apply/eq_sym; rewrite -{1}(cat_take_drop j (rcons _ _)); congr.
have jE: j = size s - (i + 1) by rewrite /j #ring.
have [ge0_j lt_js]: 0 <= j < size s by move=> /#.
rewrite -cats1 drop_cat lt_js /= /mkpad -cats1 -cat_cons; congr=> //=.
rewrite size_take // size_cat /= ltr_spsaddr //= -iE.
have sz_js: size (drop j s) = i+1; last apply/(eq_from_nth false).
+ by rewrite size_drop //= max_ler ?subr_ge0 ?ltrW // /j #ring.
+ by rewrite sz_js /= addrC size_nseq max_ler.
rewrite sz_js => k [ge0_k lt_kSi]; rewrite nth_drop //.
move/ler_eqVlt: ge0_k => [<-|] /=.
  by rewrite jE -nth_rev ?nth_index // -index_mem size_rev.
move=> lt0_k; rewrite gtr_eqF //= nth_nseq 1:/#.
have ->: j + k = (size s) - ((i-k) + 1) by rewrite /j #ring.
by rewrite -nth_rev 1:/# &(negbRL _ true) &(before_index) /#.
qed.

lemma nosmt unpad_prop (t : bool list) :
  unpad t <> None <=>
  exists (s : bool list, n : int),
  (0 <= n < r /\ r %| (size s + n + 2)) &&
  t = s ++ [true] ++ nseq n false ++ [true].
proof.
split=> [unpd_neq_None | [s n [[range_n dvd] ->]]].
have [u unpd_Some] : exists s, unpad t = Some s
  by move: unpd_neq_None; case (unpad t)=> // x _; exists x.
have <- : pad u = t by rewrite -(unpadK t) unpd_Some.
exists u, (num0 (size u)); split=> [| [num0_rng dvd_num0]].
by rewrite num0_prop size_ge0. by apply pad_alt.
by rewrite -pad_alt // padK.
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

lemma chunk_padK : pcancel (chunk \o pad) (unpad \o flatten).
proof. by move=> s @/(\o); rewrite chunkK 1:size_pad_dvd_r padK. qed.

lemma flattenK bs :
  (forall b, mem bs b => size b = r) => chunk (flatten bs) = bs.
proof. by apply/BitChunking.flattenK/gt0_r. qed.

op blocks2bits (xs:block list) : bool list = flatten (map w2bits xs).

lemma blocks2bits_nil : blocks2bits [] = [].
proof. by rewrite /blocks2bits /= flatten_nil. qed.

lemma blocks2bits_sing (x : block) : blocks2bits [x] = w2bits x.
proof. by rewrite /blocks2bits /flatten /= cats0. qed.

lemma blocks2bits_cat (xs ys : block list) :
  blocks2bits (xs ++ ys) = blocks2bits xs ++ blocks2bits ys.
proof. by rewrite /blocks2bits map_cat flatten_cat. qed.

lemma size_blocks2bits (xs : block list) :
  size (blocks2bits xs) = r * size xs.
proof.
elim xs=> [| x xs ih].
by rewrite blocks2bits_nil.
rewrite -cat1s blocks2bits_cat blocks2bits_sing size_cat //
         size_cat size_tolist ih /= #ring.
qed.

op bits2blocks (xs:bool list) : block list = map bits2w (chunk xs).

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
  + by rewrite mem_xs_cons_yss_siz_r /=; first right.
rewrite map_tolistK; [apply in_chunk_size | exact chunkK].
qed.

op pad2blocks : bool list -> block list  = bits2blocks \o pad.
op unpad_blocks : block list -> bool list option = unpad \o blocks2bits.

lemma pad2blocksK : pcancel pad2blocks unpad_blocks.
proof.
move=> xs.
by rewrite /pad2blocks /unpad_blocks /(\o) bits2blocksK
           1:size_pad_dvd_r padK.
qed.

lemma unpadBlocksK : ocancel unpad_blocks pad2blocks.
proof.
move=> xs; rewrite /pad2blocks /unpad_blocks /(\o).
pose bs := blocks2bits xs.
case (unpad bs = None) => [-> // | unpad_bs_neq_None].
have unpad_bs : unpad bs = Some(oget(unpad bs))
  by move: unpad_bs_neq_None; case (unpad bs).
rewrite unpad_bs /=.
have -> : pad(oget(unpad bs)) = bs
  by rewrite - {2} (unpadK bs) unpad_bs.
by rewrite /bs blocks2bitsK.
qed.

(* ------------------------ Extending/Stripping ----------------------- *)
op extend (xs : block list) (n : int) =
  xs ++ nseq n b0.

op strip (xs : block list) =
  let i = find (fun x => x <> b0) (rev xs) in
  (take (size xs - i) xs, i).

lemma strip_ge0 (xs : block list) :
  0 <= (strip xs).`2.
proof. rewrite /strip /= find_ge0. qed.

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

lemma nosmt valid_block_prop (xs : block list) :
  valid_block xs <=>
  exists (s : bool list, n : int),
  0 <= n < r /\ blocks2bits xs = s ++ [true] ++ nseq n false ++ [true].
proof.
rewrite /unpad_blocks /(\o).
split=> [vb | [s n] [rng_n btb]].
have /# :
  exists (s : bool list) (n : int),
  (0 <= n < r /\ r %| (size s + n + 2)) &&
  blocks2bits xs = s ++ [true] ++ nseq n false ++ [true]
  by apply unpad_prop.
have dvd : r %| (size s + n + 2).
  have <- : size (blocks2bits xs) = size s + n + 2
    by rewrite btb 3!size_cat /= size_nseq max_ler /#.
  rewrite size_blocks2bits dvdz_mulr dvdzz.
rewrite unpad_prop /#.
qed.

lemma valid_block_ends_not_b0 (xs : block list) :
  valid_block xs => last b0 xs <> b0.
proof.
move=> vb_xs.
have [s n [_ btb_eq]] :
  exists (s : bool list) (n : int),
  0 <= n < r /\ 
  blocks2bits xs = s ++ [true] ++ nseq n false ++ [true].
  by rewrite -valid_block_prop.
case (last b0 xs <> b0)=> [// | last_xs_eq_b0].
rewrite nnot in last_xs_eq_b0.
move: last_xs_eq_b0=> /last_eq_rcons [->> | [ys ->>]].
rewrite /blocks2bits /# in btb_eq.
rewrite -cats1 blocks2bits_cat blocks2bits_sing in btb_eq.
have left : last true (blocks2bits ys ++ w2bits b0) = false
  by rewrite last_cat b0 tolistK 1:size_nseq 1:max_ler // 1:ge0_r //
             last_nseq 1:gt0_r.
have right : last true (s ++ [true] ++ nseq n false ++ [true]) = true
  by rewrite cats1 last_rcons.
have last_eq :
  last true (blocks2bits ys ++ w2bits b0) =
  last true (s ++ [true] ++ nseq n false ++ [true])
  by rewrite btb_eq.
by rewrite left right in last_eq.
qed.

(* in Absorb *)
op valid_absorb (xs : block list) = valid_block((strip xs).`1).

lemma nosmt valid_absorb_prop (xs : block list) :
  valid_absorb xs <=>
  exists (ys : block list, n : int),
  0 <= n /\ xs = ys ++ nseq n b0 /\ valid_block ys.
proof.
rewrite /valid_absorb.
split=> [| [ys n] [ge0_n [-> vb_ys]]].
move=> strp_xs_valid.
exists (strip xs).`1, (strip xs).`2.
split; first apply (strip_ge0 xs).
split=> //.
by rewrite -/(extend (strip xs).`1 (strip xs).`2) eq_sym (stripK xs).
by rewrite -/(extend ys n) extendK 1:valid_block_ends_not_b0.
qed.
