/-
  WilC5 — translating a type over a set of elements of the term hull into a type over constants.

  Let `N` be an `L[[SatCTotal]]`-structure and `z : SatIdx κ`.  Given a function
  `f : A → L[[C z]].Term Empty` whose terms name the elements of `A` in `N`, we can translate a
  formula `φ` with parameters indexed by `A` into a formula with parameters indexed by the terms in
  `Set.range f`, using the variable substitution `Sum.inl a ↦ (f a)`.

  This is the syntactic input to the final saturation argument: a type over a small set of elements
  of the term hull (each named by a closed term at a common level `z`) becomes a `SatTyp2`-type over
  `C z`, to which the witness axioms of the construction apply.
-/
import Mathlib
import Submission.Work.WilC5.SatHull

open FirstOrder Language
open scoped FirstOrder

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilC5

variable (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M] (κ : Cardinal.{0})

/-- The relabelling of an `L`-formula with parameters indexed by `A` into an `L[[C z]]`-formula
with parameters indexed by the closed terms in the range of `f`. -/
noncomputable def SatRelab (z : SatIdx κ) {A : Type}
    (f : A → (L[[SatC L M κ z]]).Term Empty) : L.Formula (A ⊕ Fin 1) →
      (L[[SatC L M κ z]]).Formula (Set.range f ⊕ Fin 1) :=
  fun φ => (L.lhomWithConstants (SatC L M κ z)).onFormula
    (φ.subst fun i => match i with
      | Sum.inl a => Term.var (Sum.inl ⟨f a, Set.mem_range_self a⟩)
      | Sum.inr k => Term.var (Sum.inr k))

end Work.WilC5
