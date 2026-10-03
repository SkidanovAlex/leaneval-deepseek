import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The slices of Peluse's dual function

`sl P f₀ f₁ y x = f₀ (x - P y) · f₁ (x + y - P y)` is the `y`-th "slice" of the dual function
`dualFn M P f₀ f₁`, i.e. the pointwise identity

  `dualFn M P f₀ f₁ x = M⁻¹ ∑_{y ∈ [1,M]} sl P f₀ f₁ y x`

holds by definition.  These slices are the objects whose cube terms appear in the conclusion of
`Work.Peluse.Ulower.lemma74_denseSet` (they are the `F_{ℓ,y}` of Peluse's Lemma 7.4), while the
hypothesis of that lemma is about the cube term of the *average*.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

/-- The `y`-th slice of the dual function: `sl P f₀ f₁ y x = f₀ (x - P y) · f₁ (x + y - P y)`. -/
def sl (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ) (y : ℕ) : ℤ → ℂ :=
  fun x => f₀ (x - P.eval ((y : ℤ))) * f₁ (x + (y : ℤ) - P.eval ((y : ℤ)))

/-- The dual function is the average of its slices (definitional). -/
lemma dualFn_eq_avg (M : ℕ) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ) :
    Work.Peluse.dualFn M P f₀ f₁
      = fun x => ((M : ℂ))⁻¹ * ∑ y ∈ Finset.Icc 1 M, sl P f₀ f₁ y x := by
  funext x
  simp only [Work.Peluse.dualFn, sl]

end

end Work.Peluse.Ulower
