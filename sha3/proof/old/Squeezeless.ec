(** This is a theory for the Squeezeless sponge: where the ideal
    functionality is a fixed-output-length random oracle whose output
    length is the input block size. We prove its security even when
    padding is not prefix-free. **)
require import Fun Option Pair Int Real List FSet NewFMap Utils.
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

print Indifferentiability.

clone include Indifferentiability with
  type p     <- state, 
  type f_in  <- block list,
  type f_out <- block
  rename [module] "GReal" as "RealIndif"
         [module] "GIdeal"  as "IdealIndif".

(** Ideal Functionality **)
clone import LazyRO as Functionality with
  type from <- block list,
  type to   <- block,
  op   d    <- dblock.

(** Ideal Primitive for the Random Transformation case **)
clone import LazyRP as Primitive with
  type D <- state,
  op   d <- dstate.

(** We can now define the squeezeless sponge construction **)
module SqueezelessSponge (P:PRIMITIVE): CONSTRUCTION(P), FUNCTIONALITY = {
  proc init () = {} 

  proc f(p : block list): block = {
    var (sa,sc) <- (Block.zeros,Capacity.zeros);

    if (1 <= size p /\ p <> [Block.zeros]) {
      while (p <> []) { (* Absorption *)
        (sa,sc) <@ P.f((sa ^ head witness p,sc));
        p <- behead p;
      }
    }
    return sa;          (* Squeezing phase (non-iterated) *)
  }
}.

(** And the corresponding simulator **)
op find_chain: (state,state) fmap -> state -> (block list * block) option.

module S (F : FUNCTIONALITY) = {
  var m, mi: (state,state) fmap

  proc init() = {
    m  <- map0;
    mi <- map0;
  }

  proc f(x:state) = {
    var pvo, p, v, h, y;

    if (!mem (dom m) x) {
      pvo <- find_chain m x;
      if (pvo <> None) {
        (p,v) <- oget pvo;
        h <@ F.f(rcons p v);
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

section.
  declare module D : Self.DISTINGUISHER {P, H, S}.

  (** Inlining oracles into the experiment for clarity **)
  (* TODO: Drop init from the Distinguisher parameters' signatures *)
  local module Ideal = {
    var ro : (block list,block) fmap
    var m, mi : (state,state) fmap

    module F = {
      proc init(): unit = { }

      proc f(x : block list): block = {
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
            h <@ F.f(rcons p v);
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

    }

    module C = {
      proc init(): unit = { }

      proc f(p : block list): block = {
        var (sa,sc) <- (Block.zeros,Capacity.zeros);

        if (1 <= size p /\ p <> [Block.zeros]) {
          while (p <> []) { (* Absorption *)
            (sa,sc) <@ P.f((sa ^ head witness p,sc));
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
      defs is equal to that of distinguishing these **)
  local lemma Inlined_pr &m:
    `|Pr[RealIndif(SqueezelessSponge,P,D).main() @ &m: res]
      - Pr[IdealIndif(H,S,D).main() @ &m: res]|
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

    }

    module C = {
      proc init(): unit = { }

      proc f(p : block list): block = {
        var (sa,sc) <- (Block.zeros,Capacity.zeros);

        if (1 <= size p /\ p <> [Block.zeros]) {
          while (p <> []) { (* Absorption *)
            (sa,sc) <@ P.f((sa ^ head witness p,sc));
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

  pred is_pre_permutation (m mi : ('a,'a) fmap) =
       (forall x, mem (rng m) x => mem (dom mi) x)
    /\ (forall x, mem (rng mi) x => mem (dom m) x).

  lemma half_permutation_set (m' mi' : ('a,'a) fmap) x' y':
       (forall x, mem (rng m') x => mem (dom mi') x)
    => (forall x, mem (rng m'.[x' <- y']) x => mem (dom mi'.[y' <- x']) x).
  proof.
    move=> h x0.
    rewrite rng_set domP !in_fsetU in_fset1 => [/rng_rem_le in_rng|//=].
    by rewrite h.
  qed.

  lemma pre_permutation_set (m mi : ('a,'a) fmap) x y:
    is_pre_permutation m mi =>
    is_pre_permutation m.[x <- y] mi.[y <- x].
  proof.
    move=> [dom_mi dom_m].
    by split; apply/half_permutation_set.
  qed.    

print FUNCTIONALITY.
  local module Game0 = {
    var m, mi               : (state,state) fmap
    var mcol, micol         : (state,caller) fmap (* colouring maps for m, mi *)
    var paths               : (capacity,block list * block) fmap
    var pathscol            : (capacity,caller) fmap (* colouring maps for paths *)
    var bext, bred          : bool
    var bcoll, bsuff, bmitm : bool

    module S = {
      (** Inner interface **)
      proc fg(o : caller, x : state): state = {
        var o', y, pv, p, v;

        o' <- odflt D pathscol.[x.`2];
        bext <- bext \/ (o' <= o);

        if (!mem (dom m) x) {
          y <$ dstate;
          if (mem (dom paths) x.`2) {
            o'              <- oget pathscol.[x.`2];
            pv              <- oget paths.[x.`2];
            (p,v)           <- pv;
            bcoll           <- bcoll \/ (mem (dom paths) y.`2);
            bsuff           <- bsuff \/ (mem (image snd (rng m)) y.`2);
            pathscol.[y.`2] <- max o o';
            paths.[y.`2]    <- (rcons p (v ^ x.`1),y.`1);
          }
          mcol.[x]  <- o;
          m.[x]     <- y;
          micol.[y] <- o;
          mi.[y]    <- x;
        } else {
          o'        <- oget mcol.[x];
          mcol.[x]  <- max o o';
          y         <- oget m.[x];
          o'        <- oget micol.[y];
          micol.[y] <- max o o';
        }
        return oget m.[x];
      }

      proc f(x:state):state = {
        var r; 
        r <@ fg(D,x);
        return r;
      }

      proc fi(x : state): state = {
        var o', y;

        if (!mem (dom mi) x) {
          y <$ dstate;
          micol.[x] <- D;
          mi.[x]    <- y;
          mcol.[y]  <- D;
          m.[y]     <- x;
          bmitm     <- bmitm \/ (mem (dom paths) y.`2);
        } else {
          o'        <- oget micol.[x];
          bred      <- bred \/ o' = I;
          y         <- oget mi.[x];
          micol.[x] <- D;
          mcol.[y]  <- D;
        }
        return oget mi.[x];
      }

      (** Distinguisher interface **)
      proc init() = { }

    }

    module C = {
      proc init(): unit = { }

      proc f(p : block list): block = {
        var (sa,sc) <- (Block.zeros,Capacity.zeros);

        if (1 <= size p /\ p <> [Block.zeros]) {
          while (p <> []) {
            (sa,sc) <@ S.fg(I,(sa ^ head witness p,sc));
            p <- behead p;
          }
        }
        return sa;
      }
    }

    proc main(): bool = {
      var b;

      mcol     <- map0;
      m        <- map0;
      micol    <- map0;
      mi       <- map0;
      bext     <- false;
      bred     <- false;
      bcoll    <- false;
      bsuff    <- false;
      bmitm    <- false;
      (* the empty path is initially known by the adversary to lead to capacity 0^c *)
      pathscol <- map0.[Capacity.zeros <- D];
      paths    <- map0.[Capacity.zeros <- ([<:block>],Block.zeros)];
      b        <@ D(C,S).distinguish();
      return b;
    }    
  }.

  (** Result: the instrumented system and the concrete system are
      perfectly equivalent **)
  local equiv Game0_P_S_eq:
    Concrete_F.P.f ~ Game0.S.fg:
         arg{1} = arg{2}.`2
      /\ ={m,mi}(Concrete_F,Game0)
      /\ is_pre_permutation (Concrete_F.m){1} (Concrete_F.mi){1}
      ==> ={res}
          /\ ={m,mi}(Concrete_F,Game0)
          /\ is_pre_permutation (Concrete_F.m){1} (Concrete_F.mi){1}.
  proof.
    proc. inline *.
    sp; if=> //=; 2:by auto.
    auto; progress [-split].
    by rewrite pre_permutation_set.
  qed.

  local equiv Game0_Pi_Si_eq:
    Concrete_F.P.fi ~ Game0.S.fi:
         ={arg}
      /\ ={m,mi}(Concrete_F,Game0)
      /\ is_pre_permutation (Concrete_F.m){1} (Concrete_F.mi){1}
      ==> ={res}
          /\ ={m,mi}(Concrete_F,Game0)
          /\ is_pre_permutation (Concrete_F.m){1} (Concrete_F.mi){1}.
  proof.
    proc. inline *.
    sp; if=> //=; 2:by auto.
    auto; progress [-split].
    by rewrite pre_permutation_set.
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
    call (_:    ={m,mi}(Concrete_F,Game0)
             /\ is_pre_permutation Concrete_F.m{1} Concrete_F.mi{1}).
      + by proc *;inline Game0.S.f;wp;call Game0_P_S_eq;auto.
      + by proc *;call Game0_Pi_Si_eq.
      + proc. sp; if=> //=.
        while (   ={sa,sc,p}
               /\ ={m,mi}(Concrete_F,Game0)
               /\ is_pre_permutation Concrete_F.m{1} Concrete_F.mi{1}).
          wp; call Game0_P_S_eq.
          by auto.
        by auto.
    by auto; smt.
  qed.

  (** Split the simulator map into distinct rate and capacity maps **)
  pred map_split (m0 : (state,state) fmap) (a1 : (state,block) fmap) (c1 : (state,capacity) fmap) =
       (forall x, mem (dom m0) x = mem (dom a1) x)
    /\ (forall x, mem (dom m0) x = mem (dom c1) x)
    /\ (forall x, mem (dom m0) x => m0.[x] = Some (oget a1.[x],oget c1.[x])).

  lemma map_split_set m0 a1 c1 s a c:
    map_split m0 a1 c1 =>
    map_split m0.[s <- (a,c)] a1.[s <- a] c1.[s <- c]
  by [].

  local module Game1 = {
    var mcol,micol          : (state,caller) fmap
    var rate, ratei         : (state,block) fmap
    var cap, capi           : (state,capacity) fmap
    var pathscol            : (capacity,caller) fmap
    var paths               : (capacity,block list * block) fmap
    var bext, bred          : bool
    var bcoll, bsuff, bmitm : bool

    module S = {
      (** Inner interface **)
      proc fg(o : caller, x : state): state = {
        var o', ya, yc, pv, p, v;

        o' <- odflt D pathscol.[x.`2];
        bext <- bext \/ (o' <= o);

        if (!mem (dom rate) x) {
          (ya,yc) <$ dstate;
          if (mem (dom paths) x.`2) {
            o'            <- oget pathscol.[x.`2];
            pv            <- oget paths.[x.`2];
            (p,v)         <- pv;
            bcoll         <- bcoll \/ (mem (dom paths) yc);
            bsuff         <- bsuff \/ (mem (rng cap) yc);
            pathscol.[yc] <- max o o';
            paths.[yc]    <- (rcons p (v ^ x.`1),ya);
          }
          rate.[x]        <- ya;
          ratei.[(ya,yc)] <- x.`1;
          cap.[x]         <- yc;
          capi.[(ya,yc)]  <- x.`2;
          mcol.[x]        <- o;
          micol.[(ya,yc)] <- o;
        } else {
          o'              <- oget mcol.[x];
          mcol.[x]        <- max o o';
          ya              <- oget rate.[x];
          yc              <- oget cap.[x];
          o'              <- oget micol.[(ya,yc)];
          micol.[(ya,yc)] <- max o o';
        }
        return (oget rate.[x],oget cap.[x]);
      }

      proc f(x:state):state = {
        var r; 
        r <@ fg(D,x);
        return r;
      }

      proc fi(x : state): state = {
        var ya, yc;

        if (!mem (dom ratei) x) {
          (ya,yc)        <$ dstate;
          micol.[x]      <- D;
          ratei.[x]      <- ya;
          capi.[x]       <- yc;
          mcol.[(ya,yc)] <- D;
          rate.[(ya,yc)] <- x.`1;
          cap.[(ya,yc)]  <- x.`2;
          bmitm  <- bmitm \/ (mem (dom paths) yc);
        } else {
          bred           <- bred \/ oget micol.[x] = I;
          micol.[x]      <- D;
          ya             <- oget ratei.[x];
          yc             <- oget capi.[x];
          mcol.[(ya,yc)] <- D;
        }
        return (oget ratei.[x],oget capi.[x]);
      }

      (** Distinguisher interface **)
      proc init() = { }

    }

    module C = {
      proc init(): unit = { }

      proc f(p : block list): block = {
        var (sa,sc) <- (Block.zeros,Capacity.zeros);

        if (1<= size p /\ p <> [Block.zeros]) {
          while (p <> []) {
            (sa,sc) <@ S.fg(I,(sa ^ head witness p,sc));
            p <- behead p;
          }
        }
        return sa;
      }
    }

    proc main(): bool = {
      var b;

      mcol     <- map0;
      micol    <- map0;
      rate     <- map0;
      ratei    <- map0;
      cap      <- map0;
      capi     <- map0;
      bext     <- false;
      bred     <- false;
      bcoll    <- false;
      bsuff    <- false;
      bmitm    <- false;
      (* the empty path is initially known by the adversary to lead to capacity 0^c *)
      pathscol <- map0.[Capacity.zeros <- D];
      paths    <- map0.[Capacity.zeros <- ([<:block>],Block.zeros)];
      b        <@ D(C,S).distinguish();
      return b;
    }    
  }.

  local equiv Game1_S_S_eq:
    Game0.S.fg ~ Game1.S.fg:
         ={arg}
      /\ ={pathscol,paths}(Game0,Game1)
      /\ map_split Game0.m{1}  Game1.rate{2}  Game1.cap{2}
      /\ map_split Game0.mi{1} Game1.ratei{2} Game1.capi{2}
      /\ is_pre_permutation (Game0.m){1} (Game0.mi){1}
      ==>    ={res}
          /\ ={pathscol,paths}(Game0,Game1)
          /\ map_split Game0.m{1}  Game1.rate{2}  Game1.cap{2}
          /\ map_split Game0.mi{1} Game1.ratei{2} Game1.capi{2}
          /\ is_pre_permutation (Game0.m){1} (Game0.mi){1}.
  proof. 
    proc. inline *.
    sp; if; 1:by progress [-split]; move: H=> [->].
    + auto; progress [-split].
      move: H3; case yL=> ya yc H3; case (x{2})=> xa xc.
      by rewrite !getP_eq !map_split_set ?pre_permutation_set.
    + auto; progress [-split].
      rewrite H H0 H1 /=.
      by move: H=> [_ [_ ->]].
  qed.

  local equiv Game1_Si_Si_eq:
    Game0.S.fi ~ Game1.S.fi:
         ={arg}
      /\ ={pathscol,paths}(Game0,Game1)
      /\ map_split Game0.m{1}  Game1.rate{2}  Game1.cap{2}
      /\ map_split Game0.mi{1} Game1.ratei{2} Game1.capi{2}
      /\ is_pre_permutation (Game0.m){1} (Game0.mi){1}
      ==>    ={res}
          /\ ={pathscol,paths}(Game0,Game1)
          /\ map_split Game0.m{1}  Game1.rate{2}  Game1.cap{2}
          /\ map_split Game0.mi{1} Game1.ratei{2} Game1.capi{2}
          /\ is_pre_permutation (Game0.m){1} (Game0.mi){1}.
  proof.
    proc. inline *.
    sp; if; 1:by progress [-split]; move: H0=> [->].
    + auto; progress [-split].
      move: H3; case yL=> ya yc H3; case (x{2})=> xa xc.
      by rewrite !getP_eq !map_split_set ?pre_permutation_set.
    + auto; progress [-split].
      rewrite H H0 H1 /=.
      by move: H0=> [_ [_ ->]].
  qed.

  local lemma Game1_pr &m:
    `|Pr[Game0.main() @ &m: res]
      - Pr[Ideal.main() @ &m: res]|
    = `|Pr[Game1.main() @ &m: res]
        - Pr[Ideal.main() @ &m: res]|.
  proof.
    do !congr. byequiv=> //=; proc.
    call (_:    ={pathscol,paths}(Game0,Game1)
             /\ map_split Game0.m{1}  Game1.rate{2}  Game1.cap{2}
             /\ map_split Game0.mi{1} Game1.ratei{2} Game1.capi{2}
             /\ is_pre_permutation Game0.m{1} Game0.mi{1}).
    + by proc;call Game1_S_S_eq.
    + by apply Game1_Si_Si_eq.
    + proc; sp; if=> //=.
      while (   ={sa,sc,p}
             /\ ={pathscol,paths}(Game0,Game1)
             /\ map_split Game0.m{1}  Game1.rate{2}  Game1.cap{2}
             /\ map_split Game0.mi{1} Game1.ratei{2} Game1.capi{2}
             /\ is_pre_permutation Game0.m{1} Game0.mi{1})=> //.
      by wp; call Game1_S_S_eq.
    by auto; smt.
  qed.
end section.

(* That Self is unfortunate *)
lemma PermutationLemma:
  exists epsilon,
    forall (D <: Self.DISTINGUISHER) &m,
    `|Pr[RealIndif(SqueezelessSponge,P,D).main() @ &m: res]
      - Pr[IdealIndif(H,S,D).main() @ &m: res]|
  < epsilon.
proof. admit. qed.
