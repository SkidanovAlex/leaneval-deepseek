import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB4.RealFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Bomb_self_nonneg` — positive semi-definiteness of the Bombieri form

The Bombieri (Fock) form `Work.BoseB4.bomb m` on the real Fock space
`RealFock m = (Fin m →₀ ℕ) →₀ ℝ` is the coefficientwise pairing weighted by the
multi-index factorial,

    ⟪p, q⟫ = Σ_α α! · p_α · q_α,

so on the diagonal it is a sum of manifestly nonnegative terms:

    ⟪p, p⟫ = Σ_α α! · (p_α)²,     α! = ∏_l (α_l)! ≥ 0.

This module records the diagonal evaluation lemma `bomb_apply_self` (the
diagonal case of the evaluation of `bomb` as a `Finsupp.sum`), the nonnegativity
`bomb_mfac_nonneg` of the multi-index weight, and the resulting
`Bomb_self_nonneg`.  Together with the symmetry of `bomb` this is what makes
`bomb` a semi-inner product — the ingredient behind the Cauchy–Schwarz
inequality used to build the bosonic Fock Hilbert space of node B4.

Everything here is `sorry`-free and rests only on the standard axioms
(`propext`, `Quot.sound`, `Classical.choice`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-- Evaluation of the Bombieri form on the diagonal: `⟪p, p⟫ = Σ_α α! · (p_α)²`,
written as a `Finsupp.sum` over the support of `p`. -/
theorem bomb_apply_self {m : ℕ} (p : RealFock m) :
    bomb m p p = p.sum (fun α c => c * (mfac α * c)) := by
  rw [bomb, Finsupp.lsum_apply]
  rw [Finsupp.sum_of_support_subset p (Finset.Subset.refl _)
    (fun b x =>
      ⇑(LinearMap.toSpanSingleton ℝ (RealFock m →ₗ[ℝ] ℝ) (mfac b • Finsupp.lapply b)) x)
    (fun i _ => by simp)]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Finsupp.lapply_apply]
  ring

/-- The multi-index factorial `mfac α = ∏_l (α_l)!` is nonnegative. -/
lemma bomb_mfac_nonneg {m : ℕ} (α : Fin m →₀ ℕ) : 0 ≤ mfac α := by
  rw [mfac, Finsupp.prod]
  exact Finset.prod_nonneg fun i _ => by positivity

/-- **The Bombieri form is positive semi-definite**: `⟪p, p⟫ ≥ 0`. -/
theorem Bomb_self_nonneg {m : ℕ} (p : Work.BoseB4.RealFock m) :
    0 ≤ Work.BoseB4.bomb m p p := by
  rw [bomb_apply_self]
  refine Finsupp.sum_nonneg fun α _ => ?_
  rw [show p α * (mfac α * p α) = mfac α * (p α * p α) by ring]
  exact mul_nonneg (bomb_mfac_nonneg α) (mul_self_nonneg _)

end Work.BoseB4
