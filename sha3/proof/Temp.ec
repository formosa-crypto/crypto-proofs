(* Temporary File for Auxiliary Lemmas *)

require import Option Fun Pair Int IntExtra IntDiv Real List NewDistr.
require import Ring StdRing StdOrder StdBigop BitEncoding.
(*---*) import IntID IntOrder BitChunking.

(* Add to IntDiv? *)

lemma dvdz_lt (x y z : int) :
  0 < z => z %| x => z %| y => x < y => x + z <= y.
proof.
move=> gt0_z z_dvd_x z_dvd_y.
have -> : x = (x %/ z) * z by rewrite divzK.
have -> : y = (y %/ z) * z by rewrite divzK.
pose u := x %/ z; pose v := y %/ z; move=> u_tim_z_lt_v_tim_z.
have u_lt_v : u < v by rewrite -(@ltr_pmul2r z).
have -> : v = u + (v - u) by ring.
rewrite mulrDl ler_add2l ler_pemull 1:ltrW //.
by rewrite - (@ler_add2r u) - addrA addNr /= lez_add1r.
qed.

(* Add to BitEncoding? *)

lemma chunk_cat r (xs ys : 'a list) :
  0 < r => r %| size xs => chunk r (xs ++ ys) = chunk r xs ++ chunk r ys.
proof.
move=> ge0_r r_dvd_siz_xs; rewrite /chunk size_cat divzDl //.
(rewrite mkseq_add; first 2 rewrite divz_ge0 // size_ge0); congr.
apply eq_in_mkseq=> i [ge0_i i_lt_siz_xs_div_r] /=.
have i_tim_r_lt_siz_xs : i * r < size xs
  by rewrite ltz_divRL // in i_lt_siz_xs_div_r.
have i_tim_r_add_r_le_siz_xs : i * r + r <= size xs 
  by rewrite dvdz_lt // dvdz_mull dvdzz.
rewrite mulrC drop_cat i_tim_r_lt_siz_xs /= take_cat.
cut r_le_siz_drop : r <= size (drop (i * r) xs)
  by rewrite size_drop 1:divr_ge0 // 1:ltrW // max_ler
             ler_subr_addr /= 1:ltrW // addrC.
rewrite ler_eqVlt in r_le_siz_drop.
elim r_le_siz_drop=> [r_eq_siz_drop | -> //].
rewrite {1 6 8} r_eq_siz_drop /= take0 cats0 take_size //.
apply eq_in_mkseq=> i [ge0_i lt_siz_ys_i] /=.
have -> : r * (size xs %/ r + i) = size xs + r * i
  by rewrite mulrDr mulrC divzK.
rewrite drop_cat.
case (size xs + r * i < size xs)=> [/gtr_addl lt0_r_tim_i | _].
have contrad : 0 <= r * i < 0 by split; [rewrite divr_ge0 1:ltrW |].
rewrite ler_lt_asym in contrad; elim contrad.
have -> // : size xs + r * i - size xs = r * i by ring.
qed.

(* Add to Common? *)

theory ForCommon.

require import Common.

lemma chunk_cat (xs ys : 'a list) :
  r %| size xs => chunk r (xs ++ ys) = chunk r xs ++ chunk r ys.
proof.
exact /chunk_cat /gt0_r.
qed.

end ForCommon.
