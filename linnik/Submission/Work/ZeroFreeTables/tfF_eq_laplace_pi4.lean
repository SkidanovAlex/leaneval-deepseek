/-
# ZeroFreeTables — `tfF_eq_laplace_pi4`

The shape description `tfF` of Heath-Brown's Table 7 test function is the Laplace
transform of the `θ = π/4` member of the HB Lemma 7.1 family:

`tfF λ z = ∫₀^{2γ(λ)} e^{−zt} · tf71f (π/4) λ t dt`,  `γ(λ) = tf71γ (π/4) λ`.

Both sides are the same integral.  At `θ = π/4` the parameters of the HB Lemma 7.1
family collapse (`tan θ = 1`, `ζ = λ`, `sin 2θ = 1`, `sin θ = √2/2`, `γ = π/(4λ)`),
so HB's closed form `tf71cf (π/4) λ` is literally `λ · tfShape (λ ·)`; and the
substitution `u = λt` turns `∫₀^{π/2} e^{−(z/λ)u} tfShape u du` into
`∫₀^{π/(2λ)} e^{−zt} · λ · tfShape (λt) dt`.

The proof is done from scratch here, using only the definitions
(`HBTable7_defs`, `testFn71_defs` via `testFn7_1`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_defs
import Submission.Work.ZeroFreeTables.testFn7_1

open scoped Real
open MeasureTheory intervalIntegral

noncomputable section

namespace Work.ZeroFreeTables

/-- At `θ = π/4` the parameters of HB Lemma 7.1 give `γ = (π/4)/λ`. -/
theorem tfF_pi4_gamma (lam : ℝ) (hlam : 0 < lam) :
    tf71γ (Real.pi / 4) lam = Real.pi / (4 * lam) := by
  unfold tf71γ tf71ζ
  rw [Real.tan_pi_div_four, mul_one]
  field_simp

/-- HB's closed form `tf71cf` at `θ = π/4` is exactly `λ` times the shape
`tfShape` at `λ t`. -/
theorem tfF_pi4_cf (lam t : ℝ) (hlam : 0 < lam) :
    tf71cf (Real.pi / 4) lam t = lam * tfShape (lam * t) := by
  have h1 : Real.sin (2 * (Real.pi / 4) - lam * Real.tan (Real.pi / 4) * t)
      = Real.cos (lam * t) := by
    rw [Real.tan_pi_div_four,
      show 2 * (Real.pi / 4) - lam * 1 * t = Real.pi / 2 - lam * t by ring,
      Real.sin_pi_div_two_sub]
  have h2 : Real.sin (Real.pi / 4 - lam * Real.tan (Real.pi / 4) * t)
        / Real.sin (Real.pi / 4) = Real.cos (lam * t) - Real.sin (lam * t) := by
    rw [Real.tan_pi_div_four,
      show Real.pi / 4 - lam * 1 * t = Real.pi / 4 - lam * t by ring,
      Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hs : (Real.sqrt 2 / 2 : ℝ) ≠ 0 := by positivity
    rw [show Real.sqrt 2 / 2 * Real.cos (lam * t) - Real.sqrt 2 / 2 * Real.sin (lam * t)
        = (Real.sqrt 2 / 2) * (Real.cos (lam * t) - Real.sin (lam * t)) by ring,
      mul_div_cancel_left₀ _ hs]
  have h3 : Real.sin (2 * (Real.pi / 4)) = 1 := by
    rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  unfold tf71cf tfShape tf71γ tf71ζ
  rw [h1, h2, h3, Real.tan_pi_div_four]
  simp only [mul_one]
  field_simp
  ring

theorem tfF_eq_laplace_pi4 (lam z : ℝ) (hlam : 0 < lam) :
    Work.ZeroFreeTables.tfF lam z =
      ∫ t in (0:ℝ)..(2 * Work.ZeroFreeTables.tf71γ (Real.pi/4) lam),
        Real.exp (-(z * t)) * Work.ZeroFreeTables.tf71f (Real.pi/4) lam t := by
  have hγ : tf71γ (Real.pi / 4) lam = Real.pi / (4 * lam) := tfF_pi4_gamma lam hlam
  have h2γ : 2 * tf71γ (Real.pi / 4) lam = Real.pi / (2 * lam) := by
    rw [hγ]; field_simp; ring
  have hb : (0 : ℝ) ≤ Real.pi / (2 * lam) := by positivity
  rw [tfF]
  -- substitute `u = λ t` in the shape integral
  have hsub : (∫ u in (0:ℝ)..(Real.pi/2), Real.exp (-(z / lam) * u) * tfShape u)
      = ∫ t in (0:ℝ)..(Real.pi / (2 * lam)),
          Real.exp (-(z * t)) * (lam * tfShape (lam * t)) := by
    have h := intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ))
      (b := Real.pi / (2 * lam))
      (f := fun u : ℝ => Real.exp (-(z / lam) * u) * tfShape u) lam
    simp only [mul_zero] at h
    rw [show lam * (Real.pi / (2 * lam)) = Real.pi / 2 by field_simp,
      smul_eq_mul] at h
    rw [← h, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    have hz : -(z / lam) * (lam * t) = -(z * t) := by field_simp
    simp only [hz]
    ring
  rw [hsub, h2γ]
  -- the two integrands agree pointwise on `[0, 2γ]`
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hb] at ht
  obtain ⟨ht0, ht1⟩ := ht
  show Real.exp (-(z * t)) * (lam * tfShape (lam * t))
      = Real.exp (-(z * t)) * tf71f (Real.pi / 4) lam t
  rw [← tfF_pi4_cf lam t hlam]
  unfold tf71f
  rw [if_pos ht0, min_eq_left (by rw [h2γ]; exact ht1)]

end Work.ZeroFreeTables
