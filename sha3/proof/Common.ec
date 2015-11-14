(* -------------------------------------------------------------------- *)
require import Fun Pair Int Real List NewDistr.
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
