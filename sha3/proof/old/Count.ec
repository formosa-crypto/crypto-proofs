require import Pred Fun Option Pair Int Real StdOrder Ring.
require import List FSet NewFMap Utils Common SLCommon.
(*...*) import Dprod Dexcepted Capacity IntOrder.

module type ORACLES = {
  proc *init() : unit 
  proc p  (_:state)      : state
  proc pi (_:state)      : state
  proc f  (_:block list) : block 
}.
 
module type ODISTINGUISHER = {
  proc p  (_:state)      : state
  proc pi (_:state)      : state
  proc f  (_:block list) : block 
}.
  
module type DISTINGUISHER1 (O:ODISTINGUISHER) = {
  proc distinguish () : bool
}.

module ToC (D:DISTINGUISHER, O:ODISTINGUISHER) = {
  module F = { 
    proc f = O.f 
  }
  module P = { 
    proc f  = O.p 
    proc fi = O.pi
  }
  proc distinguisher = D(F,P).distinguish
}.

module OfC(F:DFUNCTIONALITY, P:DPRIMITIVE) = {
  proc f  = F.f
  proc p  = P.f
  proc pi = P.fi
}.

module OC (O:ODISTINGUISHER) = {

  var c : int

  proc f (bs:block list) = {
    var b;
    c <- c + size bs;
    b     <@ O.f(bs);
    return b;
  }

  proc p (x:state) = {
    var y;
    c <- c + 1;
    y     <@ O.p(x);
    return y;
  }

  proc pi(x:state) = {
    var y;
    c <- c + 1;
    y     <@ O.pi(x);
    return y;
  } 

}.


module OCRestr (O:ODISTINGUISHER) = {

  proc f (bs:block list) = {
    var b = b0;
    if (OC.c + size bs <= max_size) {
      OC.c <- OC.c + size bs;
      b     <@ O.f(bs);
    }
    return b;
  }

  proc p (x:state) = {
    var y = (b0,c0);
    if (OC.c + 1 <= max_size) {
      OC.c <- OC.c + 1;
      y     <@ O.p(x);
    }
    return y;
  }

  proc pi(x:state) = {
    var y = (b0,c0);
    if (OC.c + 1 <= max_size) {
      OC.c <- OC.c + 1;
      y     <@ O.pi(x);
    }
    return y;
  } 

}.

module Main1 (O:ORACLES,D:DISTINGUISHER1) = {

  proc main() : bool = {
    var b;
    O.init(); 
    b <@ D(O).distinguish();
    return b;
  }

}.

module Main2 (O:ORACLES,D:DISTINGUISHER1) = {

  proc main() : bool = {
    var b;
    O.init(); 
    OC.c <- 0;
    b <@ D(OCRestr(O)).distinguish();
    return b;
  }

}.

section.

   declare module O:ODISTINGUISHER{OC}.

   declare module D : DISTINGUISHER1 {O,OC}.

   axiom D_ll (O <: ODISTINGUISHER{D}):
    islossless O.p => islossless O.pi => islossless O.f => 
    islossless D(O).distinguish.

   axiom D_max : hoare [D(OC(O)).distinguish : OC.c = 0 ==> OC.c <= max_size].

   axiom f_ll  : phoare [O.f:true ==> true] = 1%r.
   axiom p_ll  : phoare [O.p:true ==> true] = 1%r.
   axiom pi_ll : phoare [O.pi:true ==> true] = 1%r.

   equiv D_DRestr : D(O).distinguish ~ D(OCRestr(O)).distinguish : 
                    ={glob D, glob O} /\ OC.c{2} = 0 ==> ={res,glob D, glob O}.
   proof.
     transitivity D(OC(O)).distinguish 
         (={glob D, glob O} ==> ={res,glob D, glob O})
         (={glob D, glob O, OC.c} /\ OC.c{1} = 0 ==> ={res,glob D, glob O})=>//.
     + by move=> ?&mr[][]-> -> ->;exists (glob O){mr}, (glob D){mr}, 0.
     + by proc (={glob O})=>//;proc *;inline *;sim.
     symmetry.
     conseq (_: ={glob D, glob O,OC.c} /\ OC.c{2} = 0 ==> 
                OC.c{2} <= max_size => ={res,glob D, glob O}) _
            (_: OC.c = 0 ==> OC.c <= max_size)=>//;1:by smt ml=0.
     + apply D_max.
     proc (max_size < OC.c) (={glob O, OC.c})=>//.
     + smt ml=0.
     + by move=> O' ???;apply (D_ll O'). 
     + proc;sp 1 0;if{1};1:by call(_:true);auto.
       by call{2} p_ll;auto=> /#. 
     + by move=> ?_;proc;sp;if;auto;call p_ll;auto.
     + by move=> _;proc;call p_ll;auto=> /#.
     + proc;sp 1 0;if{1};1:by call(_:true);auto.
       by call{2} pi_ll;auto=> /#. 
     + by move=> ?_;proc;sp;if;auto;call pi_ll;auto.
     + by move=> _;proc;call pi_ll;auto=> /#.
     + proc;sp 1 0;if{1};1:by call(_:true);auto.
       by call{2} f_ll;auto=> /#. 
     + by move=> ?_;proc;sp;if;auto;call f_ll;auto.
     by move=> _;proc;call f_ll;auto; smt ml=0 w=size_ge0.
   qed.

end section.

section.

  declare module O:ORACLES{OC}.

  declare module D : DISTINGUISHER1 {O,OC}.

  axiom D_ll (O <: ODISTINGUISHER{D}):
   islossless O.p => islossless O.pi => islossless O.f => 
   islossless D(O).distinguish.

  axiom D_max : hoare [D(OC(O)).distinguish : OC.c = 0 ==> OC.c <= max_size].

  axiom f_ll  : phoare [O.f:true ==> true] = 1%r.
  axiom p_ll  : phoare [O.p:true ==> true] = 1%r.
  axiom pi_ll : phoare [O.pi:true ==> true] = 1%r.

  equiv Main1_Main2 : Main1(O,D).main ~ Main2(O,D).main: 
    ={glob D} ==> ={res, glob D, glob O}.
  proof.
    proc;call (D_DRestr O D D_ll D_max f_ll p_ll pi_ll);wp;call(_:true);auto.
  qed.

  lemma Pr_Main1_Main2 &m : 
    Pr[Main1(O,D).main()@&m:res] = Pr[Main2(O,D).main()@&m:res].
  proof. by byequiv Main1_Main2. qed.
 
end section.
