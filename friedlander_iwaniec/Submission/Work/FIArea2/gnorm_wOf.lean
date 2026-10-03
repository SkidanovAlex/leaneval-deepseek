/-
# `|w|²` in terms of the parametrising pair `(c₁,c₂)` — the phase of (6.9)

`Work.FIArea2.sum_gBox_eq_sum_congruences` rewrites `C(z₁,z₂)` as a sum over the pairs `(c₁,c₂)`
with `Δ ∣ c₁²z₂ − c₂²z₁` of `f(|w|²)`, where `w = wOf z₁ z₂ c₁ c₂` is the (unique) Gaussian integer
with `Re(wz₁) = c₁²`, `Re(wz₂) = c₂²`.  The Poisson step needs the *explicit* value of the phase,

  `|w|² · Δ² = |c₁²z₂ − c₂²z₁|²`,

which is what this file proves (from (6.3) `c₁²z₂ − c₂²z₁ = Δ·ī·w̄`, `Work.FIArea2.cForm_parametric_sq`,
by taking norms in `ℤ[i]`).
-/
import Mathlib
import Submission.Work.FIArea2.area2_r3

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `norm` is invariant under conjugation in `ℤ[i]`. -/
lemma norm_star_eq (w : GaussianInt) : (star w).norm = w.norm := by
  simp [Zsqrtd.norm_def]

/-- `norm` of the imaginary unit is `1`. -/
lemma norm_I : (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt).norm = 1 := by
  simp [Zsqrtd.norm_def]

/-- **The phase of (6.9)**: for the parametrising point `w = wOf z₁ z₂ c₁ c₂` of a pair with
`Δ ∣ c₁²z₂ − c₂²z₁`,

  `|w|²·Δ² = |c₁²z₂ − c₂²z₁|²`. -/
theorem norm_wOf_eq (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) {c1 c2 : ℤ}
    (h : ∃ w : GaussianInt, Work.FIPlan.cForm w z1 = c1 * c1 ∧
      Work.FIPlan.cForm w z2 = c2 * c2) :
    (wOf z1 z2 c1 c2).norm * (Work.FIPlan.Delta z1 z2) ^ 2
      = ((c1 : GaussianInt) ^ 2 * z2 - (c2 : GaussianInt) ^ 2 * z1).norm := by
  obtain ⟨w, h1, h2⟩ := h
  rw [← wOf_unique hΔ h1 h2]
  have hpar := cForm_parametric_sq h1 h2
  have hn := congrArg Zsqrtd.norm hpar
  rw [Zsqrtd.norm_mul, Zsqrtd.norm_mul, Zsqrtd.norm_intCast, norm_star_eq, norm_I,
    mul_one] at hn
  rw [hn]
  ring

end

end Work.FIArea2
