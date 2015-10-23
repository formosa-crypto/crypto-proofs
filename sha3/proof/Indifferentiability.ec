(* -------------------------------------------------------------------- *)
abstract theory Types.
(** A primitive: the building block we assume ideal **)
type p.

(** A functionality: the target construction **)
type f_in, f_out.
end Types.

(* -------------------------------------------------------------------- *)
abstract theory Core.
clone import Types.

module type PRIMITIVE = {
  proc init(): unit
  proc f(x : p): p
  proc fi(x : p): p
}.

module type FUNCTIONALITY = {
  proc init(): unit
  proc f(x : f_in): f_out
}.

(** A construction takes a primitive and builds a functionality.
    A simulator takes a functionality and simulates the primitive.
    A distinguisher gets oracle access to a primitive and a
      functionality and returns a boolean (its guess as to whether it
      is playing with constructed functionality and ideal primitive or
      with ideal functionality and simulated primitive). **)
module type CONSTRUCTION (P : PRIMITIVE) = {
  proc init() : unit
  proc f(x : f_in): f_out { P.f }
}.

module type SIMULATOR (F : FUNCTIONALITY) = {
  proc init() : unit
  proc f(x : p) : p { F.f }
  proc fi(x : p) : p { F.f }
}.

module type DISTINGUISHER (F : FUNCTIONALITY, P : PRIMITIVE) = {
  proc distinguish(): bool { P.f P.fi F.f }
}.

module Indif (F : FUNCTIONALITY, P : PRIMITIVE, D : DISTINGUISHER) = {
  proc main(): bool = {
    var b;

         P.init();
         F.init();
    b <@ D(F,P).distinguish();
    return b;
  }
}.

module Real(P : PRIMITIVE, C : CONSTRUCTION) = Indif(C(P),P).
module Ideal(F : FUNCTIONALITY, S : SIMULATOR) = Indif(F,S(F)).

(* (C <: CONSTRUCTION) applied to (P <: PRIMITIVE) is indifferentiable
   from (F <: FUNCTIONALITY) if there exists (S <: SIMULATOR) such
   that, for all (D <: DISTINGUISHER),
      | Pr[Real(P,C,D): res] - Pr[Ideal(F,S,D): res] | is small.
   We avoid the existential by providing a concrete construction for S
   and the `small` by providing a concrete bound. *)
end Core.