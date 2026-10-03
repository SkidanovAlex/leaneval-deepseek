import Mathlib

namespace Work.FatouCH.Ends

open Set Metric
open scoped Topology intervalIntegral

/-- The integral of the tail bound `t ↦ 2K/t² + 2K exp(-κt/8)` over `[T₁,T₂]` is at most
`2K/T₁ + (16K/κ) exp(-κT₁/8)`. -/
theorem endsTailIntegral {K κ T₁ T₂ : ℝ} (hK : 0 ≤ K) (hκ : 0 < κ) (h1 : 0 < T₁)
    (h12 : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, (2 * K / t ^ 2 + 2 * K * Real.exp (-(κ * t / 8))) ≤
      2 * K / T₁ + 16 * K / κ * Real.exp (-(κ * T₁ / 8)) := by
  have hT2 : 0 < T₂ := lt_of_lt_of_le h1 h12
  have hmem : ∀ x ∈ uIcc T₁ T₂, 0 < x := by
    intro x hx
    have hx' : x ∈ Icc T₁ T₂ := by rwa [uIcc_of_le h12] at hx
    linarith [hx'.1]
  -- the two summands are continuous on `[T₁,T₂]`, hence interval integrable
  have hcont1 : ContinuousOn (fun t : ℝ => 2 * K / t ^ 2) (uIcc T₁ T₂) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx; exact ne_of_gt (pow_pos (hmem x hx) 2)
  have hcont2 : ContinuousOn (fun t : ℝ => 2 * K * Real.exp (-(κ * t / 8))) (uIcc T₁ T₂) := by
    fun_prop
  have hint1 : IntervalIntegrable (fun t : ℝ => 2 * K / t ^ 2) MeasureTheory.volume T₁ T₂ :=
    hcont1.intervalIntegrable
  have hint2 : IntervalIntegrable (fun t : ℝ => 2 * K * Real.exp (-(κ * t / 8)))
      MeasureTheory.volume T₁ T₂ := hcont2.intervalIntegrable
  -- first summand: `∫ 2K/t² = 2K/T₁ - 2K/T₂ ≤ 2K/T₁`
  have hA : ∫ t in T₁..T₂, 2 * K / t ^ 2 = 2 * K / T₁ - 2 * K / T₂ := by
    have hderiv : ∀ x ∈ uIcc T₁ T₂,
        HasDerivAt (fun t : ℝ => -(2 * K) / t) (2 * K / x ^ 2) x := by
      intro x hx
      have hxne : x ≠ 0 := ne_of_gt (hmem x hx)
      have h := (hasDerivAt_const x (-(2 * K))).div (hasDerivAt_id x) hxne
      convert h using 1
      · ext t; simp only [Pi.div_apply, id_eq]
      · simp only [id_eq]; ring
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint1
    rw [h]
    ring
  -- second summand: `∫ 2K exp(-κt/8) = (16K/κ)(exp(-κT₁/8) - exp(-κT₂/8))`
  have hB : ∫ t in T₁..T₂, 2 * K * Real.exp (-(κ * t / 8))
      = 16 * K / κ * (Real.exp (-(κ * T₁ / 8)) - Real.exp (-(κ * T₂ / 8))) := by
    have hderiv : ∀ x ∈ uIcc T₁ T₂,
        HasDerivAt (fun t : ℝ => -(16 * K / κ) * Real.exp (-(κ * t / 8)))
          (2 * K * Real.exp (-(κ * x / 8))) x := by
      intro x _
      have hg : HasDerivAt (fun t : ℝ => -(κ * t / 8)) (-(κ / 8)) x := by
        have h1' : HasDerivAt (fun t : ℝ => κ * t / 8) (κ / 8) x := by
          have h0 : HasDerivAt (fun t : ℝ => κ * t) κ x := by
            simpa using (hasDerivAt_id x).const_mul κ
          exact h0.div_const 8
        exact h1'.neg
      have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(κ * t / 8)))
          (Real.exp (-(κ * x / 8)) * (-(κ / 8))) x := hg.exp
      have hF : HasDerivAt (fun t : ℝ => -(16 * K / κ) * Real.exp (-(κ * t / 8)))
          (-(16 * K / κ) * (Real.exp (-(κ * x / 8)) * (-(κ / 8)))) x :=
        hexp.const_mul (-(16 * K / κ))
      convert hF using 1
      field_simp
      ring
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint2
    rw [h]
    ring
  rw [intervalIntegral.integral_add hint1 hint2]
  have h2' : ∫ t in T₁..T₂, 2 * K / t ^ 2 ≤ 2 * K / T₁ := by
    rw [hA]
    have : 0 ≤ 2 * K / T₂ := div_nonneg (by linarith) (le_of_lt hT2)
    linarith
  have h3' : ∫ t in T₁..T₂, 2 * K * Real.exp (-(κ * t / 8))
      ≤ 16 * K / κ * Real.exp (-(κ * T₁ / 8)) := by
    rw [hB]
    have h16 : 0 ≤ 16 * K / κ := div_nonneg (by linarith) (le_of_lt hκ)
    have hexp2 : 0 ≤ Real.exp (-(κ * T₂ / 8)) := (Real.exp_pos _).le
    have hsub : Real.exp (-(κ * T₁ / 8)) - Real.exp (-(κ * T₂ / 8))
        ≤ Real.exp (-(κ * T₁ / 8)) := by linarith
    exact mul_le_mul_of_nonneg_left hsub h16
  linarith [h2', h3']

end Work.FatouCH.Ends
