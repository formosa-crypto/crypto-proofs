(** This is a theory for the Squeezeless sponge: where the ideal
    functionality is a fixed-output-length random oracle whose output
    length is the input block size. We prove its security even when
    padding is not prefix-free. **)
require import Fun Option Pair Int Real NewList NewFSet NewFMap Utils.
require (*..*) AWord LazyRP LazyRO Indifferentiability.
(* TODO: Clean up the Bitstring and Word theories
      -- Make use of those new versions. *)
(*...*) import Dprod Dexcepted.
(* TODO: Datatype definitions and distributions should
     be properly separated and reorganized. *)

op r : { int | 0 < r } as lt0_r.
op c : { int | 0 < c } as lt0_c.

(** Clarify assumptions on the distributions as we go. As this is currently
    written, we are hiding some pretty heavy axioms behind cloning. **)
type block.
op dblock: block distr.

clone import AWord as Block with
  op   length      <- r,
  type word        <- block,
  op   Dword.dword <- dblock
proof leq0_length by smt.

type capacity.
op dcapacity: capacity distr.

clone AWord as Capacity with
  op   length      <- c,
  type word        <- capacity,
  op   Dword.dword <- dcapacity
proof leq0_length by smt.

type state  = block  *  capacity.
op   dstate = dblock * dcapacity.

(** The following is just lining up type definitions and defines the
    Indifferentiability experiment. Importantly, it defines neither
    ideal primitive nor ideal functionality: only their type. **)
type p_query = [
  | F  of state
  | Fi of state
].

op is_F (q : p_query) =
  with q = F  s => true
  with q = Fi s => false.

op is_Fi (q : p_query) =
  with q = F  s => false
  with q = Fi s => true.

op get_query (q : p_query) =
  with q = F  s => s
  with q = Fi s => s.

clone include Indifferentiability with
  type p_in  <- p_query,
  type p_out <- state,
  type f_in  <- block list,
  type f_out <- block.

(** Ideal Functionality **)
clone import LazyRO as Functionality with
  type from <- block list,
  type to   <- block,
  op   d    <- dblock.

(** Ideal Primitive for the Random Transformation case **)
clone import LazyRP as Primitive with
  type D <- state,
  op   d <- dstate.

(*** TODO: deal with these.
       - lining up names and types should be easier than it is... ***)
module RP_to_P (O : RP) = {
  proc init = O.init
  proc oracle(q : p_query) = {
    var r;

    if (is_F q) {
      r <@ O.f(get_query q);
    } else {
      r <@ O.fi(get_query q);
    }
    return r;
  }
}.

module RO_to_F (O : RO): Functionality = {
  proc init   = O.init
  proc oracle = O.f
}.

(** We can now define the squeezeless sponge construction **)
module SqueezelessSponge (P : Primitive): Construction(P), Functionality = {
  proc init = P.init

  proc oracle(p : block list): block = {
    var (sa,sc) <- (Block.zeros,Capacity.zeros);

    if (size p >= 1 /\ p <> [Block.zeros]) {
      while (p <> []) { (* Absorption *)
        (sa,sc) <@ P.oracle(F (sa ^ head witness p,sc));
        p <- behead p;
      }
    }
    return sa;          (* Squeezing phase (non-iterated) *)
  }
}.

(** And the corresponding simulator **)
op find_chain: (state,state) fmap -> state -> (block list * block) option.

module PreSimulator (F : Functionality) = {
  var m, mi: (state,state) fmap

  proc init() = {
    F.init();
    m  <- map0;
    mi <- map0;
  }

  proc f(x:state) = {
    var pvo, p, v, h, y;

    if (!mem (dom m) x) {
      pvo <- find_chain m x;
      if (pvo <> None) {
        (p,v) <- oget pvo;
        h <@ F.oracle(rcons p v);
        y <$ dcapacity;
      } else {
        (h,y) <$ dstate;
      }
      m.[x] <- (h,y);
      mi.[(h,y)] <- x;
    }
    return oget m.[x];
  }

  proc fi(x:state) = {
    var y;

    if (!mem (dom mi) x) {
      y <$ dstate;
      mi.[x] <- y;
      m.[y] <- x;
    }
    return oget mi.[x];
  }
}.

module P = RP_to_P(Primitive.P).
module F = RO_to_F(H).
module S(F : Functionality) = RP_to_P(PreSimulator(F)).

section.
  declare module D : Self.Distinguisher {P, F, S}.

  (** Inlining oracles into the experiment for clarity **)
  (* TODO: Drop init from the Distinguisher parameters' signatures *)
  local module Ideal = {
    var ro : (block list,block) fmap
    var m, mi : (state,state) fmap

    module F = {
      proc init(): unit = { }

      proc oracle(x : block list): block = {
        if (!mem (dom ro) x) {
          ro.[x] <$ dblock;
        }
        return oget ro.[x];
      }
    }

    module S = {
      proc init(): unit = { }

      proc f(x : state): state = {
        var pvo, p, v, h, y;

        if (!mem (dom m) x) {
          pvo <- find_chain m x;
          if (pvo <> None) {
            (p,v) <- oget pvo;
            h <@ F.oracle(rcons p v);
            y <$ dcapacity;
          } else {
            (h,y) <$ dstate;
          }
          m.[x] <- (h,y);
          mi.[(h,y)] <- x;
        }
        return oget m.[x];
      }

      proc fi(x:state) = {
        var y;

        if (!mem (dom mi) x) {
          y <$ dstate;
          mi.[x] <- y;
          m.[y] <- x;
        }
        return oget mi.[x];
      }

      proc oracle(q : p_query): state = {
        var r;

        if (is_F q) {
          r <@ f(get_query q);
        } else {
          r <@ fi(get_query q);
        }
        return r;
      }
    }

    proc main(): bool = {
      var b;

      ro <- map0;
      m  <- map0;
      mi <- map0;
      b  <@ D(F,S).distinguish();
      return b;
    }
  }.

  local module Concrete = {
    var m, mi: (state,state) fmap

    module P = {
      proc init(): unit = { }

      proc f(x : state): state = {
        var y;

        if (!mem (dom m) x) {
          y <$ dstate \ (rng m);
          m.[x]  <- y;
          mi.[y] <- x;
        }
        return oget m.[x];
      }

      proc fi(x : state): state = {
        var y;

        if (!mem (dom mi) x) {
          y <$ dstate \ (rng mi);
          mi.[x] <- y;
          m.[y]  <- x;
        }
        return oget mi.[x];
      }

      proc oracle(q : p_query): state = {
        var r;

        if (is_F q) {
          r <@ f(get_query q);
        } else {
          r <@ fi(get_query q);
        }
        return r;
      }

    }

    module C = {
      proc init(): unit = { }

      proc oracle(p : block list): block = {
        var (sa,sc) <- (Block.zeros,Capacity.zeros);

        if (size p >= 1 /\ p <> [Block.zeros]) {
          while (p <> []) { (* Absorption *)
            (sa,sc) <@ P.oracle(F (sa ^ head witness p,sc));
            p <- behead p;
          }
        }
        return sa;          (* Squeezing phase (non-iterated) *)
      }
    }

    proc main(): bool = {
      var b;

      m  <- map0;
      mi <- map0;
      b  <@ D(C,P).distinguish();
      return b;
    }    
  }.

  (** Result: The adversary's advantage in distinguishing the modular
      defs if equal to that of distinguishing these **)
  local lemma Inlined_pr &m:
    `|Pr[Indif(SqueezelessSponge(P),P,D).main() @ &m: res]
      - Pr[Indif(F,S(F),D).main() @ &m: res]|
    = `|Pr[Concrete.main() @ &m: res]
        - Pr[Ideal.main() @ &m: res]|.
  proof. by do !congr; expect 2 (byequiv=> //=; proc; inline *; sim; auto). qed.

  (** An intermediate game where we don't care about the permutation
      being a bijection anymore... **)
  local module Concrete_F = {
    var m, mi: (state,state) fmap

    module P = {
      proc init(): unit = { }

      proc f(x : state): state = {
        var y;

        if (!mem (dom m) x) {
          y <$ dstate;
          m.[x]  <- y;
          mi.[y] <- x;
        }
        return oget m.[x];
      }

      proc fi(x : state): state = {
        var y;

        if (!mem (dom mi) x) {
          y <$ dstate;
          mi.[x] <- y;
          m.[y]  <- x;
        }
        return oget mi.[x];
      }

      proc oracle(q : p_query): state = {
        var r;

        if (is_F q) {
          r <@ f(get_query q);
        } else {
          r <@ fi(get_query q);
        }
        return r;
      }

    }

    module C = {
      proc init(): unit = { }

      proc oracle(p : block list): block = {
        var (sa,sc) <- (Block.zeros,Capacity.zeros);

        if (size p >= 1 /\ p <> [Block.zeros]) {
          while (p <> []) { (* Absorption *)
            (sa,sc) <@ P.oracle(F (sa ^ head witness p,sc));
            p <- behead p;
          }
        }
        return sa;          (* Squeezing phase (non-iterated) *)
      }
    }

    proc main(): bool = {
      var b;

      m  <- map0;
      mi <- map0;
      b  <@ D(C,P).distinguish();
      return b;
    }
  }.

  (** Result (expected): The distance between Concrete and Concrete_F
      is bounded by N^2/|state|, where N is the total cost (in terms
      of queries to P and P^-1) of the adversary's queries **)

                 (** TODO: express and prove **)

  (** And now for the interesting bits **)
  (** Inform the primitive interface of queries made by the
      distinguisher on its functionality interface, keep track of
      primitive call paths in a coloured graph. **)
  (** The following invariants should always hold at adversary
      boundaries (they may be violated locally, but should always be
      fixed (say, by setting bad) before returning control, and the
      adversary should not be able to violate them himself):
        - if paths[x] = (_,(p,v)), then following path p through m
          from (0^r,0^c) leads to state (v,x); (in particular, this
          implies (v,x) \in rng m;
        - unless bad occurs (identify which ones), for every sc, there
          is at most one sa such that (sa,sc) \in rng m;
        - unless bad occurs (identify which ones), if paths[x] =
          (o,(p,_)) and paths[x'] = (o',(p++p',_)), then o' <= o;
          (todo: maybe change the direction of that order relation so
          it corresponds to "order of appearance along paths"?)

      The next step in the proof will probably be to eagerly sample
      all values of the rate and introduce some indirection on
      capacities so that they are only sampled (and propagated) just
      before being given to the adversary. This is easier to do if all
      samplings are independent, hence the move away from a random
      permutation. Some side-effects remain worrying.
   **)
  type caller = [ | I | D ].

  op (<=) (o1 o2 : caller) = o1 = I \/ o2 = D.

  op max (o1 o2 : caller) =
    with o1 = I => o2
    with o1 = D => D.

  local module Game0 = {
    var m, mi               : (state,caller * state) fmap
    var paths               : (capacity,caller * (block list * block)) fmap
    var bext, bred          : bool
    var bcoll, bsuff, bmitm : bool

    module S = {
      (** Inner interface **)
      proc f(o : caller, x : state): state = {
        var o', y, pv, p, v, x';

        o' <- oapp fst D paths.[x.`2];
        bext <- bext \/ (o' <= o);

        if (!mem (dom m) x) {
          y <$ dstate;
          if (mem (dom paths) x.`2) {
            (o',pv)      <- oget paths.[x.`2];
            (p,v)        <- pv;
            bcoll        <- bcoll \/ (mem (dom paths) y.`2);
            bsuff        <- bsuff \/ (mem (image (snd \o snd) (rng m)) y.`2);
            paths.[y.`2] <- (max o o',(rcons p (v ^ x.`1),y.`1));
          }
          m.[x]  <- (o,y);
          mi.[y] <- (o,x);
        } else {
          (o',y)  <- oget m.[x];
          m.[x]   <- (max o o',y);
          if (mem (dom mi) y) {
            (o',x') <- oget mi.[y];
            mi.[y]  <- (max o o',x');
          }
        }
        return snd (oget m.[x]);
      }

      proc fi(x : state): state = {
        var o', y, x';

        if (!mem (dom mi) x) {
          y <$ dstate;
          mi.[x] <- (D,y);
          m.[y]  <- (D,x);
          bmitm  <- bmitm \/ (mem (dom paths) y.`2);
        } else {
          (o',y)  <- oget mi.[x];
          bred    <- bred \/ o' = I;
          mi.[x]  <- (D,y);
          if (mem (dom m) y) {
            (o',x') <- oget m.[y];
            m.[y]   <- (D,x');
          }
        }
        return snd (oget mi.[x]);
      }

      (** Distinguisher interface **)
      proc init() = { }

      proc oracle(q : p_query): state = {
        var r;

        if (is_F q) {
          r <@ f(D,get_query q);
        } else {
          r <@ fi(get_query q);
        }
        return r;
      }

    }

    module C = {
      proc init(): unit = { }

      proc oracle(p : block list): block = {
        var (sa,sc) <- (Block.zeros,Capacity.zeros);

        if (size p >= 1 /\ p <> [Block.zeros]) {
          while (p <> []) {
            (sa,sc) <@ S.f(I,(sa ^ head witness p,sc));
            p <- behead p;
          }
        }
        return sa;
      }
    }

    proc main(): bool = {
      var b;

      m     <- map0;
      mi    <- map0;
      bext  <- false;
      bred  <- false;
      bcoll <- false;
      bsuff <- false;
      bmitm <- false;
      (* the empty path is initially known by the adversary to lead to capacity 0^c *)
      paths <- map0.[Capacity.zeros <- (D,([<:block>],Block.zeros))];
      b     <@ D(C,S).distinguish();
      return b;
    }    
  }.

  (** Result: the instrumented system and the concrete system are
      perfectly equivalent **)
  (** This proof is done brutally because it is *just* program verification. *)
  local equiv Game0_P_S_eq:
    Concrete_F.P.f ~ Game0.S.f:
         arg{1} = arg{2}.`2
      /\ (forall x, Concrete_F.m.[x]{1} = omap snd (Game0.m.[x]){2})
      /\ (forall x, Concrete_F.mi.[x]{1} = omap snd (Game0.mi.[x]){2})
      ==> ={res}
          /\ (forall x, Concrete_F.m.[x]{1} = omap snd (Game0.m.[x]){2})
          /\ (forall x, Concrete_F.mi.[x]{1} = omap snd (Game0.mi.[x]){2}).
  proof.
    proc. inline *.
    conseq (_:    x{1} = x{2} (* FIXME: conseq extend *)
               /\ (forall x, Concrete_F.m.[x]{1} = omap snd (Game0.m.[x]){2})
               /\ (forall x, Concrete_F.mi.[x]{1} = omap snd (Game0.mi.[x]){2})
               /\ image snd (rng Game0.m{2}) = rng Concrete_F.m{1} (* Helper *)
               ==> _).
      progress. apply fsetP=> x; rewrite imageP in_rng; split=> [[[o s]]|[t]].
        by rewrite in_rng /snd /= => [[t h] ->>] {s}; exists t; rewrite H h.
      by rewrite H=> h; exists (oget Game0.m{2}.[t]); smt.
    sp; if; 1:smt.
      by auto; progress; expect 3 smt.
    by auto; progress; expect 5 smt.
  qed.

  local equiv Game0_Pi_Si_eq:
    Concrete_F.P.fi ~ Game0.S.fi:
         ={arg}
      /\ (forall x, Concrete_F.m.[x]{1} = omap snd (Game0.m.[x]){2})
      /\ (forall x, Concrete_F.mi.[x]{1} = omap snd (Game0.mi.[x]){2})
      ==> ={res}
          /\ (forall x, Concrete_F.m.[x]{1} = omap snd (Game0.m.[x]){2})
          /\ (forall x, Concrete_F.mi.[x]{1} = omap snd (Game0.mi.[x]){2}).
  proof.
    proc. inline *.
    conseq (_:    x{1} = x{2} (* FIXME: conseq extend *)
               /\ (forall x, Concrete_F.m.[x]{1} = omap snd (Game0.m.[x]){2})
               /\ (forall x, Concrete_F.mi.[x]{1} = omap snd (Game0.mi.[x]){2})
               /\ image snd (rng Game0.mi{2}) = rng Concrete_F.mi{1} (* Helper *)
               ==> _).
      progress. apply fsetP=> x; rewrite imageP in_rng; split=> [[[o s]]|[t]].
        by rewrite in_rng /snd /= => [[t h] ->>] {s}; exists t; rewrite H0 h.
      by rewrite H0=> h; exists (oget Game0.mi{2}.[t]); smt.
    sp; if; 1:smt.
      by auto; progress; expect 3 smt.
    by auto; progress; expect 5 smt.
  qed.

  local lemma Game0_pr &m:
    `|Pr[Concrete_F.main() @ &m: res]
      - Pr[Ideal.main() @ &m: res]|
    = `|Pr[Game0.main() @ &m: res]
        - Pr[Ideal.main() @ &m: res]|.
  proof.
    do !congr.
    byequiv=> //=.
    proc.
    call (_:    (forall x, Concrete_F.m.[x]{1} = omap snd (Game0.m.[x]){2})
             /\ (forall x, Concrete_F.mi.[x]{1} = omap snd (Game0.mi.[x]){2})).
      proc; if=> //=.
        by call Game0_P_S_eq.
        by call Game0_Pi_Si_eq.
        proc. sp; if=> //=.
        while (   ={sa,sc,p}
               /\ (forall x, Concrete_F.m.[x]{1} = omap snd (Game0.m.[x]){2})
               /\ (forall x, Concrete_F.mi.[x]{1} = omap snd (Game0.mi.[x]){2})).
          inline Concrete_F.P.oracle. rcondt{1} 2; 1:by auto.
          wp; call Game0_P_S_eq.
          by auto.
        by auto.
    by auto; smt.
  qed.
end section.

(* That Self is unfortunate *)
lemma PermutationLemma:
  exists epsilon,
    forall (D <: Self.Distinguisher) &m,
    `|Pr[Indif(SqueezelessSponge(P),P,D).main() @ &m: res]
      - Pr[Indif(F,S(F),D).main() @ &m: res]|
  < epsilon.
proof. admit. qed.
