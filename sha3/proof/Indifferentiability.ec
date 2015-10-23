(* -------------------------------------------------------------------- *)
abstract theory Types.
(** A primitive: the building block we assume ideal **)
type p.

module type Primitive = {
  proc init(): unit
  proc f(x : p): p
  proc fi(x : p): p
}.

(** A functionality: the target construction **)
type f_in, f_out.

module type Functionality = {
  proc init(): unit
  proc f(x : f_in): f_out
}.

(** A construction takes a primitive and builds a functionality.
    A simulator takes a functionality and simulates the primitive.
    A distinguisher gets oracle access to a primitive and a
      functionality and returns a boolean (its guess as to whether it
      is playing with constructed functionality and ideal primitive or
      with ideal functionality and simulated primitive). **)
module type Construction (P : Primitive) = {
  proc init() : unit {  }
  proc f(x : f_in): f_out { P.f }
}.

module type Simulator (F : Functionality) = {
  proc init() : unit {  }
  proc f(x : p) : p { F.f }
  proc fi(x : p) : p { F.f }
}.

module type Distinguisher (F : Functionality, P : Primitive) = {
  proc distinguish(): bool { P.f P.fi F.f }
}.
end Types.

(* -------------------------------------------------------------------- *)
abstract theory Core.
clone import Types.

module Indif (F : Functionality, P : Primitive, D : Distinguisher) = {
  proc main(): bool = {
    var b;

         P.init();
         F.init();
    b <@ D(F,P).distinguish();
    return b;
  }
}.

module Real(P:Primitive, C:Construction) = Indif(C(P),P).
module Ideal(F:Functionality, S:Simulator) = Indif(F,S(F)).
(* (C <: Construction) applied to (P <: Primitive) is indifferentiable
   from (F <: Functionality) if there exists (S <: Simulator) such
   that, for all (D <: Distinguisher),
      | Pr[Real(P,C,D): res] - Pr[Ideal(F,S,D): res] | is small.
   We avoid the existential by providing a concrete construction for S
   and the `small` by providing a concrete bound. *)
end Core.
