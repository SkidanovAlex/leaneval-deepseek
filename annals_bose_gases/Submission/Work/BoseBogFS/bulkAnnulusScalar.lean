import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open MeasureTheory intervalIntegral

/-- Derivative of the explicit antiderivative used in `bulkAnnulusScalar`: the derivative of

`r ↦ δ r³/3 + η r⁴/2 + ((B + ηT + A)/2) (δ r + η r²) + A² (36 c₁ log r + 12 e_T r)`

is the (algebraically rearranged, `r ≠ 0`) integrand of `bulkAnnulusScalar`. -/
private theorem hasDerivAt_Hfun {δ η B A c1 eT T r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r : ℝ => δ * r ^ 3 / 3 + η * r ^ 4 / 2
        + ((B + η * T + A) / 2) * (δ * r + η * r ^ 2)
        + A ^ 2 * (36 * c1 * Real.log r + 12 * eT * r))
      (δ * r ^ 2 + 2 * η * r ^ 3 + ((B + η * T + A) / 2) * (δ + 2 * η * r)
        + A ^ 2 * (36 * c1 / r + 12 * eT)) r := by
  have h1 : HasDerivAt (fun y : ℝ => δ * y ^ 3 / 3) ((δ * ((3:ℝ) * r ^ ((3:ℕ) - 1))) / 3) r :=
    ((hasDerivAt_pow 3 r).const_mul δ).div_const 3
  have h2 : HasDerivAt (fun y : ℝ => η * y ^ 4 / 2) ((η * ((4:ℝ) * r ^ ((4:ℕ) - 1))) / 2) r :=
    ((hasDerivAt_pow 4 r).const_mul η).div_const 2
  have h3 : HasDerivAt (fun y : ℝ => ((B + η * T + A) / 2) * (δ * y + η * y ^ 2))
      (((B + η * T + A) / 2) * (δ * 1 + η * ((2:ℝ) * r ^ ((2:ℕ) - 1)))) r :=
    (((hasDerivAt_id r).const_mul δ).add ((hasDerivAt_pow 2 r).const_mul η)).const_mul
      ((B + η * T + A) / 2)
  have h4 : HasDerivAt (fun y : ℝ => A ^ 2 * (36 * c1 * Real.log y + 12 * eT * y))
      (A ^ 2 * ((36 * c1) * r⁻¹ + (12 * eT) * 1)) r :=
    (((Real.hasDerivAt_log (ne_of_gt hr)).const_mul (36 * c1)).add
      ((hasDerivAt_id r).const_mul (12 * eT))).const_mul (A ^ 2)
  exact (((h1.add h2).add h3).add h4).congr_deriv (by ring)

theorem bulkAnnulusScalar {δ η B A c1 eT T : ℝ}
    (hc1 : 0 < c1) (heT : 0 ≤ eT) (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hAB : A ≤ B + η * T) (hle : 4 * c1 ≤ T) :
    (∫ r in Set.Ioc (4 * c1) T,
        r ^ 2 * ((δ + 2 * η * r) * (1 + (B + η * T + A) / (2 * r ^ 2))
          + A ^ 2 * (36 * c1 / r ^ 3 + 12 * eT / r ^ 2)))
      ≤ δ * T ^ 3 / 3 + η * T ^ 4 / 2 + (B + η * T) * (δ * T + η * T ^ 2)
        + A ^ 2 * (36 * c1 * (Real.log T - Real.log (4 * c1)) + 12 * eT * T) := by
  have h4c1 : (0 : ℝ) < 4 * c1 := by linarith
  have hT : (0 : ℝ) ≤ T := by linarith
  -- The integrand simplifies, on the strictly positive interval `(4 c₁, T]`, to a function
  -- whose antiderivative is explicit.
  have hpoint : Set.EqOn
      (fun r : ℝ => r ^ 2 * ((δ + 2 * η * r) * (1 + (B + η * T + A) / (2 * r ^ 2))
          + A ^ 2 * (36 * c1 / r ^ 3 + 12 * eT / r ^ 2)))
      (fun r : ℝ => δ * r ^ 2 + 2 * η * r ^ 3 + ((B + η * T + A) / 2) * (δ + 2 * η * r)
          + A ^ 2 * (36 * c1 / r + 12 * eT))
      (Set.uIcc (4 * c1) T) := by
    intro r hr
    have hr0 : 0 < r := by
      have h1 : 4 * c1 ≤ r := by
        rcases Set.mem_uIcc.mp hr with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1
        · exact le_trans hle h1
      linarith
    field_simp
  have hcont : ContinuousOn
      (fun r : ℝ => δ * r ^ 3 / 3 + η * r ^ 4 / 2
        + ((B + η * T + A) / 2) * (δ * r + η * r ^ 2)
        + A ^ 2 * (36 * c1 * Real.log r + 12 * eT * r)) (Set.Icc (4 * c1) T) := by
    have hlog : ContinuousOn Real.log (Set.Icc (4 * c1) T) :=
      Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith [hx.1, h4c1])
    fun_prop
  have hderiv : ∀ x ∈ Set.Ioo (4 * c1) T,
      HasDerivAt (fun r : ℝ => δ * r ^ 3 / 3 + η * r ^ 4 / 2
        + ((B + η * T + A) / 2) * (δ * r + η * r ^ 2)
        + A ^ 2 * (36 * c1 * Real.log r + 12 * eT * r))
      (δ * x ^ 2 + 2 * η * x ^ 3 + ((B + η * T + A) / 2) * (δ + 2 * η * x)
        + A ^ 2 * (36 * c1 / x + 12 * eT)) x := by
    intro x hx
    exact hasDerivAt_Hfun (lt_trans h4c1 hx.1)
  have hint : IntervalIntegrable
      (fun r : ℝ => δ * r ^ 2 + 2 * η * r ^ 3 + ((B + η * T + A) / 2) * (δ + 2 * η * r)
        + A ^ 2 * (36 * c1 / r + 12 * eT)) volume (4 * c1) T := by
    apply ContinuousOn.intervalIntegrable
    have hne : ∀ r ∈ Set.uIcc (4 * c1) T, r ≠ 0 := by
      intro r hr
      have h1 : 4 * c1 ≤ r := by
        rcases Set.mem_uIcc.mp hr with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1
        · exact le_trans hle h1
      linarith
    have hinv : ContinuousOn (fun r : ℝ => 36 * c1 / r) (Set.uIcc (4 * c1) T) := by
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro r hr; exact hne r hr
    fun_prop
  have hfund : ∫ r in (4 * c1)..T,
      (fun r : ℝ => δ * r ^ 2 + 2 * η * r ^ 3 + ((B + η * T + A) / 2) * (δ + 2 * η * r)
        + A ^ 2 * (36 * c1 / r + 12 * eT)) r
      = (fun r : ℝ => δ * r ^ 3 / 3 + η * r ^ 4 / 2 + ((B + η * T + A) / 2) * (δ * r + η * r ^ 2)
        + A ^ 2 * (36 * c1 * Real.log r + 12 * eT * r)) T
        - (fun r : ℝ => δ * r ^ 3 / 3 + η * r ^ 4 / 2 + ((B + η * T + A) / 2) * (δ * r + η * r ^ 2)
        + A ^ 2 * (36 * c1 * Real.log r + 12 * eT * r)) (4 * c1) :=
    integral_eq_sub_of_hasDerivAt_of_le hle hcont hderiv hint
  rw [← intervalIntegral.integral_of_le hle]
  rw [intervalIntegral.integral_congr hpoint]
  rw [hfund]
  dsimp only
  have h1 : 0 ≤ δ * (4 * c1) ^ 3 / 3 := by positivity
  have h2 : 0 ≤ η * (4 * c1) ^ 4 / 2 := by positivity
  have h3 : 0 ≤ A ^ 2 * (12 * eT * (4 * c1)) := by positivity
  have h5 : 0 ≤ ((B + η * T + A) / 2) * (δ * (4 * c1) + η * (4 * c1) ^ 2) := by
    apply mul_nonneg
    · linarith
    · positivity
  have h4 : ((B + η * T + A) / 2) * (δ * T + η * T ^ 2) ≤ (B + η * T) * (δ * T + η * T ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  linarith [h1, h2, h3, h4, h5]

end Work.BoseBogFS
