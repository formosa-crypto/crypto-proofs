pragma -oldip.
require import Pred Fun Option Pair Int Real RealExtra StdOrder Ring StdBigop.
require import List FSet NewFMap Utils Common SLCommon RndO FelTactic Mu_mem.
(*...*) import Dprod Dexcepted Capacity IntOrder Bigreal RealOrder BRA.

require (*..*) Gext.

module IF = {
  proc init = F.RO.init
  proc f(p:block list) = {
    var sa <- b0;
    if (1 <= size p /\ p <> [b0]) {
      sa <@ F.RO.get(p);
    }
    return sa;
  }
}.

module S(F : DFUNCTIONALITY) = {
  var m, mi               : smap
  var paths               : (capacity, block list * block) fmap

  proc init() = {
    m     <- map0;
    mi    <- map0;
    (* the empty path is initially known by the adversary to lead to capacity 0^c *)
    paths    <- map0.[c0 <- ([<:block>],b0)];
  }

  proc f(x : state): state = {
    var p, v, y, y1, y2;

    if (!mem (dom m) x) {
      if (mem (dom paths) x.`2) {
        (p,v) <- oget paths.[x.`2]; 
        y1    <- F.f (rcons p (v +^ x.`1));
      } else {
        y1 <$ bdistr;
      }
      y2 <$ cdistr;
      y <- (y1,y2);
      m.[x]             <- y;
      mi.[y]            <- x;
      if (mem (dom paths) x.`2) {
        (p,v) <- oget paths.[x.`2]; 
        paths.[y.`2] <- (rcons p (v +^ x.`1), y.`1);
      }
    } else {   
      y <- oget m.[x];
    }
    return y;
  }

  proc fi(x : state): state = {
    var y, y1, y2;

    if (!mem (dom mi) x) {
      y1       <$ bdistr;
      y2       <$ cdistr;
      y        <- (y1,y2);
      mi.[x]            <- y;
      m.[y]             <- x;
    } else {
      y <- oget mi.[x];
    }
    return y;
  }
  
}.

section.

declare module D: DISTINGUISHER{C, Perm, F.RO, F.FRO,S }.
local clone import Gext as Gext0.

local module G3(RO:F.RO) = {

  module C = {
 
    proc f(p : block list): block = {
      var sa, sa';
      var h, i <- 0; 
      sa <- b0;
      if (1 <= size p /\ p <> [b0]) {
        while (i < size p ) {
          if (mem (dom G1.mh) (sa +^ nth witness p i, h)) {
            RO.sample(take (i+1) p);
            (sa, h) <- oget G1.mh.[(sa +^ nth witness p i, h)];
          } else {
            RRO.sample(G1.chandle);
            sa'                 <@ RO.get(take (i+1) p);
            sa                  <- sa +^ nth witness p i;
            G1.mh.[(sa,h)]      <- (sa', G1.chandle);
            G1.mhi.[(sa',G1.chandle)] <- (sa, h);
            (sa,h)              <- (sa',G1.chandle);
            G1.chandle          <- G1.chandle + 1;
          }
          i        <- i + 1;
        }
        sa <- RO.get(p);
      }
      return sa;
    }
  }
 
  module S = {
 
    proc f(x : state): state = {
      var p, v, y, y1, y2, hy2, hx2, handles_,t;
 
      if (!mem (dom G1.m) x) {
        if (mem (dom G1.paths) x.`2) {
          (p,v) <- oget G1.paths.[x.`2]; 
          y1    <- RO.get (rcons p (v +^ x.`1));
        } else {
          y1 <$ bdistr;
        }
        y2 <$ cdistr;
        y <- (y1, y2);
        handles_ <@ RRO.restrK();
        if (!mem (rng handles_) x.`2) {
          RRO.set(G1.chandle, x.`2);
          G1.chandle <- G1.chandle + 1;
        }
        handles_ <- RRO.restrK();
        hx2      <- oget (hinvc handles_ x.`2);
        t        <@ RRO.in_dom((oget G1.mh.[(x.`1,hx2)]).`2, Unknown);
        if (mem (dom G1.mh) (x.`1, hx2) /\ t) {
          hy2                  <- (oget G1.mh.[(x.`1, hx2)]).`2;
          FRO.m.[hy2]          <- (y2,Known);
          G1.m.[x]             <- y;
          G1.mi.[y]            <- x;
        } else {
          hy2                  <- G1.chandle;
          G1.chandle           <- G1.chandle + 1;
          RRO.set(hy2, y.`2); 
          G1.m.[x]             <- y;
          G1.mh.[(x.`1, hx2)]  <- (y.`1, hy2);
          G1.mi.[y]            <- x;
          G1.mhi.[(y.`1, hy2)] <- (x.`1, hx2);
        }
        if (mem (dom G1.paths) x.`2) {
          (p,v) <- oget G1.paths.[x.`2]; 
          G1.paths.[y.`2] <- (rcons p (v +^ x.`1), y.`1);
        }
      } else {   
        y <- oget G1.m.[x];
      }
      return y;
    }
 
    proc fi(x : state): state = {
      var y, y1, y2, hx2, hy2, handles_, t;
 
      if (!mem (dom G1.mi) x) {
        handles_ <@ RRO.restrK();
        if (!mem (rng handles_) x.`2) {
          RRO.set(G1.chandle, x.`2);
          G1.chandle <- G1.chandle + 1;
        }
        handles_ <@ RRO.restrK();
        hx2      <- oget (hinvc handles_ x.`2);
        t        <@ RRO.in_dom((oget G1.mhi.[(x.`1,hx2)]).`2, Unknown);
        y1       <$ bdistr;
        y2       <$ cdistr;
        y        <- (y1,y2);
        if (mem (dom G1.mhi) (x.`1, hx2) /\ t) {
          (y1,hy2)             <- oget G1.mhi.[(x.`1, hx2)];
          FRO.m.[hy2]          <- (y2,Known);
          G1.mi.[x]            <- y;
          G1.m.[y]             <- x;
        } else {
          hy2                  <- G1.chandle;
          G1.chandle           <- G1.chandle + 1;
          RRO.set(hy2, y.`2); 
          G1.mi.[x]            <- y;
          G1.mhi.[(x.`1, hx2)] <- (y.`1, hy2);
          G1.m.[y]             <- x;
          G1.mh.[(y.`1, hy2)]  <- (x.`1, hx2);
        }
      } else {
        y <- oget G1.mi.[x];
      }
      return y;
    }
 
  }
 
  proc distinguish(): bool = {
    var b;
 
    RO.init();
    G1.m     <- map0;
    G1.mi    <- map0;
    G1.mh    <- map0;
    G1.mhi   <- map0;
 
    (* the empty path is initially known by the adversary to lead to capacity 0^c *)
    RRO.init();
    RRO.set(0,c0);
    G1.paths    <- map0.[c0 <- ([<:block>],b0)];
    G1.chandle  <- 1;
    b        <@ DRestr(D,C,S).distinguish();
    return b;
  }    
}.

local equiv G2_G3: Eager(G2(DRestr(D))).main2 ~ G3(F.LRO).distinguish : ={glob D} ==> ={res}.
proof.
  proc;wp;call{1} RRO_resample_ll;inline *;wp.
  call (_: ={FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c}); last by auto.

  + proc;sp;if=> //.
    call (_: ={FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c});2:by auto.
    if=> //;2:by sim.
    swap{1} [3..7] -2;swap{2} [4..8] -3.
    seq 5 5:(={hx2,t,x,FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c} /\
             (t = in_dom_with FRO.m (oget G1.mh.[(x.`1, hx2)]).`2 Unknown){1});
      1:by inline *;auto.
    seq 3 4:(={y,x,FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c});
      2:by sim.  
    if=>//.
    + seq 2 2:(={y1,hx2,t,x,FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c}
               /\ (t = in_dom_with FRO.m (oget G1.mh.[(x.`1, hx2)]).`2 Unknown){1}).
      + by inline *;auto=> /> ? _;rewrite Block.DWord.bdistr_ll.
      case ((mem (dom G1.mh) (x.`1, hx2) /\ t){1});
          [rcondt{1} 3;2:rcondt{2} 3| rcondf{1} 3;2:rcondf{2} 3];
          1,2,4,5:(by move=>?;conseq (_:true);auto);2:by sim.
      inline *;rcondt{1} 6;1:by auto=>/>. 
      wp;rnd;auto;progress[-split];rewrite DWord.cdistr_ll /= => ?_?->.
      by rewrite !getP /= oget_some.
    case ((mem (dom G1.mh) (x.`1, hx2) /\ t){1});
          [rcondt{1} 4;2:rcondt{2} 4| rcondf{1} 4;2:rcondf{2} 4];
          1,2,4,5:(by move=>?;conseq (_:true);auto);2:by sim.
    inline *;rcondt{1} 7;1:by auto=>/>. 
    wp;rnd;auto;rnd{1};auto;progress[-split]. 
    rewrite Block.DWord.supportP DWord.cdistr_ll /==> ?_?->.
    by rewrite !getP /= oget_some.
    
  + proc;sp;if=>//.
    call (_: ={FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c});2:by auto.
    if=> //;2:sim. 
    swap{1} 8 -3. 
    seq 6 6 : (={y1,hx2,t,x,FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c}
               /\ (t = in_dom_with FRO.m (oget G1.mhi.[(x.`1, hx2)]).`2 Unknown){1}).
    + by inline *;auto.
    case ((mem (dom G1.mhi) (x.`1, hx2) /\ t){1});
          [rcondt{1} 3;2:rcondt{2} 3| rcondf{1} 3;2:rcondf{2} 3];
          1,2,4,5:(by move=>?;conseq (_:true);auto);2:by sim.
    inline *;rcondt{1} 6;1:by auto=>/>. 
    wp;rnd;auto;progress[-split];rewrite DWord.cdistr_ll /= => ?_?->.
    by rewrite !getP /= oget_some.

  proc;sp;if=>//.
  call (_: ={FRO.m,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.chandle,G1.paths,C.c});2:by auto.
  by inline F.LRO.sample;sim.
qed.

local equiv G3_G3: G3(F.LRO).distinguish ~ G3(F.RO).distinguish : ={glob G3,F.RO.m} ==> ={res}.
proof. symmetry;conseq (F.RO_LRO_D G3)=> //. qed.
  
local module G4(RO:F.RO) = {

  module C = {
 
    proc f(p : block list): block = {
      var sa;
      var h, i <- 0; 
      sa <- b0;
      if (1 <= size p /\ p <> [b0]) {
        while (i < size p ) {
          RO.sample(take (i+1) p);
          i        <- i + 1;
        }
        sa <- RO.get(p);
      }
      return sa;
    }
  }
 
  module S = {
 
    proc f(x : state): state = {
      var p, v, y, y1, y2;
 
      if (!mem (dom G1.m) x) {
        if (mem (dom G1.paths) x.`2) {
          (p,v) <- oget G1.paths.[x.`2]; 
          y1    <- RO.get (rcons p (v +^ x.`1));
        } else {
          y1 <$ bdistr;
        }
        y2 <$ cdistr;
        y <- (y1,y2);
        G1.m.[x]             <- y;
        G1.mi.[y]            <- x;
        if (mem (dom G1.paths) x.`2) {
          (p,v) <- oget G1.paths.[x.`2]; 
          G1.paths.[y.`2] <- (rcons p (v +^ x.`1), y.`1);
        }
      } else {   
        y <- oget G1.m.[x];
      }
      return y;
    }
 
    proc fi(x : state): state = {
      var y, y1, y2;
 
      if (!mem (dom G1.mi) x) {
        y1       <$ bdistr;
        y2       <$ cdistr;
        y        <- (y1,y2);
        G1.mi.[x]            <- y;
        G1.m.[y]             <- x;
      } else {
        y <- oget G1.mi.[x];
      }
      return y;
    }
 
  }
 
  proc distinguish(): bool = {
    var b;
 
    RO.init();
    G1.m     <- map0;
    G1.mi    <- map0;
    (* the empty path is initially known by the adversary to lead to capacity 0^c *)
    G1.paths    <- map0.[c0 <- ([<:block>],b0)];
    b        <@ DRestr(D,C,S).distinguish();
    return b;
  }    
}.

local equiv G3_G4 : G3(F.RO).distinguish ~ G4(F.RO).distinguish : ={glob D} ==> ={res}.
proof.
  proc;inline *;wp.
  call (_: ={G1.m,G1.mi,G1.paths,F.RO.m,C.c});last by auto.
  + proc;sp;if=>//.
    call (_: ={G1.m,G1.mi,G1.paths,F.RO.m,C.c});last by auto.
    if => //;2:sim.
    seq 3 3: (={x,y1,y2,y,G1.m,G1.mi,G1.paths,F.RO.m,C.c});1:by sim.
    sim;seq 5 0: (={x,y1,y2,y,G1.m,G1.mi,G1.paths,F.RO.m,C.c});1:by inline *;auto.
    by if{1};sim;inline *;auto.
  + proc;sp;if=>//.
    call (_: ={G1.m,G1.mi,G1.paths,F.RO.m,C.c});last by auto.
    if => //;2:sim.
    seq 5 0: (={x,G1.m,G1.mi,G1.paths,F.RO.m,C.c});1:by inline *;auto.
    seq 3 3: (={x,y1,y2,y,G1.m,G1.mi,G1.paths,F.RO.m,C.c});1:by sim.
    by if{1};sim;inline *;auto.
  proc;sp;if=>//.
  call (_: ={G1.m,G1.mi,G1.paths,F.RO.m,C.c});last by auto.
  sp;if=>//;sim; while(={i,p,F.RO.m})=>//.
  inline F.RO.sample F.RO.get;if{1};1:by auto. 
  by sim;inline *;auto;progress;apply DWord.cdistr_ll.
qed.
  
local equiv G4_G4 : G4(F.RO).distinguish ~ G4(F.LRO).distinguish : ={glob G4,F.RO.m} ==> ={res}.
proof. conseq (F.RO_LRO_D G4)=> //. qed.

local equiv G4_Ideal : G4(F.LRO).distinguish ~ IdealIndif(IF,S,DRestr(D)).main :
   ={glob D} ==> ={res}.
proof.
  proc;inline *;wp.
  call (_: ={C.c,F.RO.m} /\ G1.m{1}=S.m{2} /\ G1.mi{1}=S.mi{2} /\ G1.paths{1}=S.paths{2}).
  + proc;sp;if=>//.
    call (_: ={C.c,F.RO.m} /\ G1.m{1}=S.m{2} /\ G1.mi{1}=S.mi{2} /\ G1.paths{1}=S.paths{2});
      2: by auto.
    if=>//;sim;if=> //;2:by auto.
    inline{2} IF.f;rcondt{2} 4.
    + auto;progress. smt w=(size_rcons List.size_ge0). 
      admit.
    by inline *;sim.
  + by sim.     
  + proc;sp;if=>//.
    call (_: ={F.RO.m});2:by auto.
    sp;if=>//;sim.
    by while{1} (true) (size p - i){1};auto;1:inline*;auto=>/#.
  by auto.
qed.

axiom D_ll :
 forall (F <: DFUNCTIONALITY{D}) (P <: DPRIMITIVE{D}),
   islossless P.f =>
   islossless P.fi => islossless F.f => islossless D(F, P).distinguish.

lemma Real_Ideal &m: 
  Pr[GReal(D).main() @ &m: res /\ C.c <= max_size] <=
  Pr[IdealIndif(IF,S,DRestr(D)).main() @ &m :res] +
   ((max_size + 1) ^ 2)%r * mu dstate (pred1 witness) + 
   max_size%r * ((2*max_size)%r / (2^c)%r) + 
   max_size%r * ((2*max_size)%r / (2^c)%r).
proof.
  apply (ler_trans _ _ _ (Real_G2 D D_ll &m)).
  rewrite !(ler_add2l, ler_add2r);apply lerr_eq.
  apply (eq_trans _ Pr[G3(F.LRO).distinguish() @ &m : res]);1:by byequiv G2_G3.
  apply (eq_trans _ Pr[G3(F.RO ).distinguish() @ &m : res]);1:by byequiv G3_G3.
  apply (eq_trans _ Pr[G4(F.RO ).distinguish() @ &m : res]);1:by byequiv G3_G4.
  apply (eq_trans _ Pr[G4(F.LRO).distinguish() @ &m : res]);1:by byequiv G4_G4.
  by byequiv G4_Ideal.
qed.
  
end section.
