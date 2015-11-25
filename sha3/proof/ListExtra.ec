(* -------------------------------------------------------------------- *)
require import Option Fun Pair Int IntExtra IntDiv Real List NewDistr.
require import Ring StdRing StdOrder.
(*---*) import IntID IntOrder.

(* -------------------------------------------------------------------- *)
lemma nth_flatten x0 n (bs : 'a list list) i :
     all (fun s => size s = n) bs
  => nth x0 (flatten bs) i = nth x0 (nth [] bs (i %/ n)) (i %% n).
proof.
case: (n <= 0) => [ge0_n|/ltrNge gt0_n] /allP /= eqz.
  have bsE: bs = nseq (size bs) [].
    elim: bs eqz => /= [|b bs ih eqz]; 1: by rewrite nseq0.
    rewrite addrC nseqS ?size_ge0 -ih /=.
      by move=> x bsx; apply/eqz; rewrite bsx.
    by rewrite -size_eq0 -leqn0 ?size_ge0 eqz.
  rewrite {2}bsE nth_nseq_if if_same /=.
  rewrite bsE; elim/natind: (size bs)=> [m le0_m|m ge0_m ih];
    by rewrite ?nseqS // nseq0_le // flatten_nil.
case: (i < 0)=> [lt0_i|/lerNgt ge0_i].
  rewrite nth_neg // (@nth_neg []) // ltrNge.
  by rewrite divz_ge0 // -ltrNge.
elim: bs i ge0_i eqz => [|b bs ih] i ge0_i eqz /=.
  by rewrite flatten_nil.
have /(_ b) /= := eqz; rewrite flatten_cons nth_cat => ->.
have <-: (i < n) <=> (i %/ n = 0) by rewrite -divz_eq0 // ge0_i.
case: (i < n) => [lt_in|/lerNgt le_ni]; 2: rewrite ih ?subr_ge0 //.
+ by rewrite modz_small // ge0_i ltr_normr ?lt_in.
+ by move=> x bx; have := eqz x; apply; rewrite /= bx.
rewrite subrE -mulN1r modzMDr subrE; congr.
case: (n = 0)=> [^zn ->/=|nz_n]; 2: by rewrite divzMDr 1?addrC.
rewrite divz0 /= eq_sym nth_neg ?oppr_lt0 // => {ih}; move: eqz.
by case: bs => // c bs /(_ c) /=; rewrite zn size_eq0 => ->.
qed.
