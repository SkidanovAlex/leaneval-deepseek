import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FITop3.Defs3
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.S15box

set_option linter.unusedVariables false

namespace Work.FIArea2.R6

/-- **`Δ(z₁,z₂) = 0` destroys coprimality (for primitive `z₁` of norm `> 1`).**

Let `z₁` lie in the polar box (5.14) — in particular `Pa.N < |z₁|²`, with `Pa.N ≥ 1` by
`Params.hN1` — and let `z₁` be primitive, i.e. `(z₁, z̄₁) = 1`.  If `Δ(z₁,z₂) = Im(z̄₁z₂) = 0`,
then `z̄₁z₂` is real, which (by the Bézout relation `a z₁ + b z̄₁ = 1` coming from primitivity)
forces `z₁ ∣ z₂`: multiply `a z₁ + b z̄₁ = 1` by `z₂` and use `z̄₁z₂ = z₁z̄₂`.  Hence
`(z₁,z₂) = 1` would make `z₁` a unit, so `|z₁|² = 1`, contradicting `|z₁|² > Pa.N ≥ 1`.

(The polar-box hypothesis on `z₂` is not needed: the argument shows more generally that
`Δ(z₁,z₂) = 0` with `z₁` primitive of norm `> 1` already implies `¬(z₁,z₂) = 1`.) -/
theorem not_coprime_of_Delta_eq_zero {Pa : Work.FITop.Params} {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2)
    (hp1 : Work.FIPlan.IsPrimitive z1) (hΔ : Work.FIPlan.Delta z1 z2 = 0) :
    ¬ Work.FIPlan.GaussCoprime z1 z2 := by
  intro hcop
  -- `Δ(z₁,z₂) = 0` says that `z̄₁ z₂` is real
  have hD : (star z1 * z2).im = 0 := by
    rw [Work.FIPlan.Delta] at hΔ; exact hΔ
  -- hence `z̄₁ z₂ = z₁ z̄₂`
  have hzw : star z1 * z2 = z1 * star z2 := by
    have hw : star (star z1 * z2) = star z1 * z2 := by
      apply Zsqrtd.ext
      · rw [Zsqrtd.re_star]
      · rw [Zsqrtd.im_star, hD, neg_zero]
    rw [← hw, star_mul, star_star]
    ring
  -- Bézout from primitivity, multiplied by `z₂`, gives `z₁ ∣ z₂`
  obtain ⟨a, b, hab⟩ := hp1
  have hdvd : z1 ∣ z2 := by
    have h1' : z1 ∣ a * z1 * z2 := ⟨a * z2, by ring⟩
    have h2' : z1 ∣ b * (star z1 * z2) := ⟨b * star z2, by rw [hzw]; ring⟩
    have hsum : z2 = a * z1 * z2 + b * (star z1 * z2) := by
      have h := congrArg (fun t => t * z2) hab
      rw [add_mul, one_mul] at h
      conv_lhs => rw [← h]
      ring
    rw [hsum]
    exact dvd_add h1' h2'
  -- coprimality plus `z₁ ∣ z₂` makes `z₁` a unit, i.e. `|z₁|² = 1`
  have hunit : IsUnit z1 := (show IsCoprime z1 z2 from hcop).isUnit_of_dvd hdvd
  have hgn : Work.FIPlan.gnorm z1 = 1 := by
    show z1.norm.natAbs = 1
    exact Zsqrtd.norm_eq_one_iff.mpr hunit
  -- contradicting `|z₁|² > Pa.N ≥ 1`
  obtain ⟨-, hz1n, -, -, -⟩ := h1
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
  rw [hgn] at hz1n
  push_cast at hz1n
  linarith

end Work.FIArea2.R6
