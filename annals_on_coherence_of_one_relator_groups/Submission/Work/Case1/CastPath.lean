/-
# Casting paths and arrows along vertex equalities

Mathlib provides `Quiver.Hom.cast` and `Quiver.Path.cast` (`Mathlib.Combinatorics.Quiver.Cast`).
All the lemmas we need about them are proved by *eliminating the equalities* at the level of the
statement (where both sides are variables), after which the cast is `rfl`; this file collects the
ones needed by the small-model construction of `Submission/Work/Case1/smallModel.lean`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Relator

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u v

namespace Work.Case1

open Quiver

namespace PathCast

variable {U : Type u} [Quiver U] [Quiver.HasInvolutiveReverse U]

/-- Casting a path ending in an arrow along equalities of the endpoints. -/
theorem cast_cons {a b c a' b' c' : U} (q : Quiver.Path a b) (e : b ⟶ c)
    (h1 : a = a') (h2 : b = b') (h3 : c = c') :
    (q.cons e).cast h1 h3 = (q.cast h1 h2).cons (e.cast h2 h3) := by
  cases h1; cases h2; cases h3; rfl

/-- Casting a concatenation of paths. -/
theorem cast_comp {a b c a' b' c' : U} (p : Quiver.Path a b) (q : Quiver.Path b c)
    (h1 : a = a') (h2 : b = b') (h3 : c = c') :
    (p.comp q).cast h1 h3 = (p.cast h1 h2).comp (q.cast h2 h3) := by
  cases h1; cases h2; cases h3; rfl

/-- Casting the reversal of a path. -/
theorem cast_reverse {a b a' b' : U} (p : Quiver.Path a b) (h1 : a = a') (h2 : b = b') :
    (p.cast h1 h2).reverse = (p.reverse).cast h2 h1 := by
  cases h1; cases h2; rfl

/-- Casting a path does not change its length. -/
theorem cast_length {a b a' b' : U} (p : Quiver.Path a b) (h1 : a = a') (h2 : b = b') :
    (p.cast h1 h2).length = p.length := by
  cases h1; cases h2; rfl

/-- Casting a path does not change its arrow list. -/
theorem cast_arrowList {a b a' b' : U} (p : Quiver.Path a b) (h1 : a = a') (h2 : b = b') :
    (p.cast h1 h2).arrowList = p.arrowList := by
  cases h1; cases h2; rfl

/-- Casting a path does not change its vertex list. -/
theorem cast_vertices {a b a' b' : U} (p : Quiver.Path a b) (h1 : a = a') (h2 : b = b') :
    (p.cast h1 h2).vertices = p.vertices := by
  cases h1; cases h2; rfl

/-- Casting a path does not change reducedness. -/
theorem cast_isReduced {a b a' b' : U} (p : Quiver.Path a b) (h1 : a = a') (h2 : b = b') :
    (p.cast h1 h2).IsReduced ↔ p.IsReduced := by
  cases h1; cases h2
  rw [Quiver.Path.cast_rfl_rfl]

/-- Casting a path along equalities of its endpoints with themselves does not change it. -/
theorem cast_self {a b : U} (p : Quiver.Path a b) (h1 : a = a) (h2 : b = b) :
    p.cast h1 h2 = p := by
  rw [Subsingleton.elim h1 rfl, Subsingleton.elim h2 rfl, Quiver.Path.cast_rfl_rfl]

/-- Casting a path back along the reverse equalities returns it. -/
theorem cast_cast_symm {a b a' b' : U} (p : Quiver.Path a b) (h1 : a = a') (h2 : b = b') :
    (p.cast h1 h2).cast h1.symm h2.symm = p := by
  rw [Quiver.Path.cast_cast]
  exact cast_self p _ _

/-- Casting commutes with the free-groupoid product `pmul`. -/
theorem cast_pmul {a b c a' b' c' : U} (p : Quiver.Path a b) (q : Quiver.Path b c)
    (h1 : a = a') (h2 : b = b') (h3 : c = c') :
    Work.ORLocInd.Howie.pmul (p.cast h1 h2) (q.cast h2 h3) =
      (Work.ORLocInd.Howie.pmul p q).cast h1 h3 := by
  cases h1; cases h2; cases h3; rfl

/-- Casting commutes with `red`. -/
theorem cast_red {a b a' b' : U} (p : Quiver.Path a b) (h1 : a = a') (h2 : b = b') :
    Work.ORLocInd.Howie.red (p.cast h1 h2) = (Work.ORLocInd.Howie.red p).cast h1 h2 := by
  cases h1; cases h2; rfl

/-- Casting commutes with the powers `compPower` of a closed path. -/
theorem cast_compPower {a a' : U} (p : Quiver.Path a a) (m : ℕ) (h1 h2 : a = a') :
    (p.cast h1 h2).compPower m = (p.compPower m).cast h1 h2 := by
  cases h1; cases h2; rfl

/-- Conjugating a path by a cast of itself along an endpoint equality: the two `pmul` expressions
are equal (they differ only by casts which cancel). -/
theorem cast_conj_loop {a b a' : U} (X : Quiver.Path a b) (Y : Quiver.Path b b) (h : b = a') :
    Work.ORLocInd.Howie.pmul (X.cast rfl h)
        (Work.ORLocInd.Howie.pmul (Y.cast h h) (X.cast rfl h).reverse) =
      Work.ORLocInd.Howie.pmul X (Work.ORLocInd.Howie.pmul Y X.reverse) := by
  rw [cast_reverse X rfl h, cast_pmul Y X.reverse h h rfl,
    cast_pmul X (Work.ORLocInd.Howie.pmul Y X.reverse) rfl h rfl, Quiver.Path.cast_rfl_rfl]

end PathCast

/-- Reversal commutes with `Quiver.Hom.cast`. -/
theorem hom_cast_reverse {U : Type u} [Quiver U] [Quiver.HasReverse U] {x y x' y' : U}
    (h1 : x = x') (h2 : y = y') (e : x ⟶ y) :
    Quiver.reverse (Quiver.Hom.cast h1 h2 e) = Quiver.Hom.cast h2 h1 (Quiver.reverse e) := by
  cases h1; cases h2; rfl

/-- `Quiver.Hom.cast` is injective at fixed endpoint equalities. -/
theorem cast_injective {U : Type u} [Quiver U] {x y x' y' : U} (h1 : x = x') (h2 : y = y') :
    Function.Injective (fun e : x ⟶ y => Quiver.Hom.cast h1 h2 e) := by
  cases h1; cases h2
  intro a b h
  exact h

/-- `Quiver.Hom.cast` does not depend on the proofs of the endpoint equalities. -/
theorem hom_cast_irrel {U : Type u} [Quiver U] {x y x' y' : U} (h1 h1' : x = x')
    (h2 h2' : y = y') (e : x ⟶ y) : e.cast h1 h2 = e.cast h1' h2' := by
  rw [Subsingleton.elim h1 h1', Subsingleton.elim h2 h2']

end Work.Case1
