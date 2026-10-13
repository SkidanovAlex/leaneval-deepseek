import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.psiP_div_cos_defs
import Submission.Work.FTS_EllLimOK.ProducerH.integral_rpow_zero_one
import Submission.Work.FTS_EllLimOK.ProducerH.cs_rpow_bounded

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise Cauchy–Schwarz bound for the `psiP` representation

This file proves `psiP_pointwise_cs`: on the open quadrant `Qd = (0,∞) × (0,π/2)`, where
`Φ = psiP α Φ` and `|U'| ≤ M` for `U' = Uprime α Φ`, the quotient `Φ/cos θ` satisfies

`(Φ z θ / cos θ)² ≤ (4/(3α)) ∫₀¹ v^{3/α-1} U'(zv,θ)² dv`.

The proof is the classical Cauchy–Schwarz argument.  In `v`, the representation
`psiP α Φ z θ = -(sin 2θ/α) ∫₀¹ v^{3/α-1} U'(zv,θ) dv` (the fixed point hypothesis) gives
`Φ z θ / cos θ = -(2 sin θ/α) ∫₀¹ v^{3/α-1} U'(zv,θ) dv`; Cauchy–Schwarz in `v`
(`Work.FTS_EllLimOK.ProducerH.cs_rpow_bounded`) gives
`(∫₀¹ v^β U')² ≤ (∫₀¹ v^β)(∫₀¹ v^β U'²) = (α/3) ∫₀¹ v^β U'²` for `β = 3/α - 1`
(`integral_rpow_zero_one`), and `sin²θ ≤ 1` gives the constant `4/(3α)`. -/

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false

/-- **Pointwise Cauchy–Schwarz bound for the `psiP` representation.**
On the open quadrant, where `Φ = psiP α Φ`, and with `|U'| ≤ M` (`U' = Uprime α Φ`), the quotient
`Φ/cos θ` satisfies `(Φ z θ/cos θ)² ≤ (4/(3α)) ∫₀¹ v^{3/α-1} U'(zv,θ)² dv`.

Route: `Φ z θ = -(sin 2θ/α) ∫₀¹ v^β U'(zv,θ) dv` (the fixed-point hypothesis + the definition of
`psiP`), so `Φ/cos θ = -(2 sin θ/α) ∫₀¹ v^β U'(zv,θ) dv` (as `cos θ ≠ 0` on the quadrant);
Cauchy–Schwarz in `v` on `(0,1)` (Hölder with `p = q = 2`) gives
`(∫₀¹ v^β U')² ≤ (∫₀¹ v^β)(∫₀¹ v^β U'²) = (1/(β+1)) ∫₀¹ v^β U'² = (α/3)∫₀¹ v^β U'²` for
`β = 3/α - 1` (`integral_rpow`), and `sin²θ ≤ 1`. -/
theorem psiP_pointwise_cs {α : ℝ} (hα : 0 < α) {Φ : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hpsi : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Φ z θ = Work.FTS.StreamBdryIface.psiP α Φ z θ)
    (hbnd : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.FTS.StreamBdryIface.Uprime α Φ z θ| ≤ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      (Φ z θ / Real.cos θ) ^ 2
        ≤ (4 / (3 * α)) * ∫ v in (0 : ℝ)..1,
            v ^ (Work.FTS_EllLimOK.ProducerH.beta α)
              * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ) ^ 2 := by
  intro z θ hzθ
  -- unfold the quadrant, then the fixed point and the definition of `psiP`
  have hzθ' : (z, θ) ∈ Work.Construction.Qd := hzθ
  simp only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hzθ'
  obtain ⟨hz, hθ0, hθ1⟩ := hzθ'
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have hQd : ∀ w : ℝ, 0 < w → (w, θ) ∈ Work.Construction.Qd := by
    intro w hw
    simp only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    exact ⟨hw, hθ0, hθ1⟩
  have hΦ : Φ z θ = -(Work.Construction.s2 θ / α) *
      ∫ v in (0:ℝ)..1, v ^ beta α * Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ := by
    rw [hpsi z θ (hQd z hz)]
    rfl
  set I : ℝ := ∫ v in (0:ℝ)..1, v ^ beta α *
    Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ with hI
  set J : ℝ := ∫ v in (0:ℝ)..1, v ^ beta α *
    (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2 with hJ
  -- `Φ / cos θ = -(2 sin θ / α) · I`
  have hquot : Φ z θ / Real.cos θ = -(2 * Real.sin θ / α) * I := by
    rw [hΦ, Work.Construction.s2_eq, Real.sin_two_mul]
    field_simp
  have hsq : (Φ z θ / Real.cos θ)^2 = (4 * (Real.sin θ)^2 / α^2) * I^2 := by
    rw [hquot]; ring
  -- Cauchy–Schwarz in `v`
  have hβ : -1 < beta α := by
    rw [beta]
    have : 0 < 3 / α := by positivity
    linarith
  have ha : ∀ v, v ∈ Set.Ioc (0:ℝ) 1 →
      |Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ| ≤ M := by
    intro v hv
    exact hbnd (z * v) θ (hQd (z*v) (mul_pos hz hv.1))
  have hcs : I^2 ≤ (∫ v in (0:ℝ)..1, v ^ beta α) * J := by
    rw [hI, hJ]
    exact cs_rpow_bounded hβ hM ha
  have hInt : ∫ v in (0:ℝ)..1, v ^ beta α = α / 3 := by
    rw [integral_rpow_zero_one hβ]
    have h3 : beta α + 1 = 3 / α := by rw [beta]; ring
    rw [h3, one_div_div]
  -- assemble the arithmetic
  calc (Φ z θ / Real.cos θ)^2
      = (4 * (Real.sin θ)^2 / α^2) * I^2 := hsq
    _ ≤ (4 / α^2) * I^2 := by
        have h1 : 4 * Real.sin θ ^ 2 ≤ 4 := by nlinarith [Real.sin_sq_le_one θ]
        have h2 : 4 * Real.sin θ ^ 2 / α^2 ≤ 4 / α^2 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg I)
    _ ≤ (4 / α^2) * ((α/3) * J) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 4/α^2)
        rw [← hInt]
        exact hcs
    _ = (4 / (3 * α)) * J := by
        rw [← mul_assoc]
        congr 1
        field_simp

end Work.FTS_EllLimOK.ProducerH
