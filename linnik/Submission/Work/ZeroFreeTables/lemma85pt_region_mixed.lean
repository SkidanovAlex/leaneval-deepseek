import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_engine85

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory MeromorphicOn
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.ZeroFreeTables

open Work.LinnikAreas.DhRepel

/-- **Mixed assembly of HB Lemma 8.5.**  Variant of `lemma8_5_assembly` in which the `χ₁`
`K`-sum is bounded with constant `c₁` while the other three (`χ₂`, `χ₁χ₂`, `χ₁χ₂⁻¹`) are bounded
with constant `c`; the resulting coefficient is `c₁ + 2c`. -/
theorem lemma8_5_assembly_mixed {q : ℕ} [NeZero q] {f : ℝ → ℝ} {x₀ L c₁ c ε β₂ γ₂ J₂ J₁ J₀ : ℝ}
    (hf : ∀ t, 0 ≤ f t) (hx₀ : 0 < x₀) (hL : 0 < L)
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) (χ₁ χ₂ : DirichletCharacter ℂ q)
    (h0 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β₂ : ℂ)).re
              * f (Real.log n / L)) ≤ L * J₂ + f 0 * ε * L)
    (h1 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            (χ₁ (n : ZMod q) / (n : ℂ) ^ (β₂ : ℂ)).re * f (Real.log n / L))
          ≤ -L * J₁ + f 0 * (c₁ + ε) * L)
    (h2 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I)).re
              * f (Real.log n / L))
          ≤ -L * J₀ + f 0 * (c + ε) * L)
    (h3 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I)).re
              * f (Real.log n / L)) ≤ f 0 * (c + ε) * L)
    (h4 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₂⁻¹) (n : ZMod q) / (n : ℂ) ^ ((β₂ : ℂ) - (γ₂ : ℂ) * Complex.I)).re
              * f (Real.log n / L)) ≤ f 0 * (c + ε) * L) :
    0 ≤ J₂ - J₁ - J₀ + f 0 * (c₁ + 2 * c + 4 * ε) := by
  have hpos := Commons.NumberTheory.Linnik.Ksum_positivity (q := q) (f := f) hf hx₀ hL hsupp χ₁ χ₂
    (β := β₂) (γ₁ := 0) (γ₂ := γ₂)
  simp only [Complex.ofReal_zero, zero_mul, add_zero, zero_add, zero_sub, neg_mul, ← sub_eq_add_neg] at hpos
  have hmain : 0 ≤ L * (J₂ - J₁ - J₀ + f 0 * (c₁ + 2 * c + 4 * ε)) := by
    calc (0:ℝ) ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (χ₁ (n : ZMod q) / (n : ℂ) ^ (β₂ : ℂ)).re * f (Real.log n / L)
            + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I)).re * f (Real.log n / L))
            + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β₂ : ℂ)).re * f (Real.log n / L))
            + 1/2 * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * ((χ₁ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I)).re * f (Real.log n / L))
            + 1/2 * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * ((χ₁ * χ₂⁻¹) (n : ZMod q) / (n : ℂ) ^ ((β₂ : ℂ) - (γ₂ : ℂ) * Complex.I)).re * f (Real.log n / L)) := hpos
      _ ≤ (-L * J₁ + f 0 * (c₁ + ε) * L) + (-L * J₀ + f 0 * (c + ε) * L) + (L * J₂ + f 0 * ε * L) + 1/2 * (f 0 * (c + ε) * L) + 1/2 * (f 0 * (c + ε) * L) := by linarith only [h0, h1, h2, h3, h4]
      _ = L * (J₂ - J₁ - J₀ + f 0 * (c₁ + 2 * c + 4 * ε)) := by ring
  exact (mul_nonneg_iff_of_pos_left hL).mp hmain

theorem lemma85pt_region_mixed (x₀ B c₁ c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hfnn : ∀ t : ℝ, 0 ≤ f t)
      (hF : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1)
        (hχ₂χ₁ : χ₂ ≠ χ₁)
        (hχ₁χ₂ : χ₁ * χ₂ ≠ 1) (hχ₁χ₂' : χ₁ * χ₂⁻¹ ≠ 1)
        [NeZero χ₁.conductor] [NeZero χ₂.conductor]
        [NeZero (χ₁ * χ₂).conductor] [NeZero (χ₁ * χ₂⁻¹).conductor]
        {β₁ β₂ γ₂ : ℝ}
        (hβ₁ : |1 - β₁| ≤ δ) (hβ₂ : |1 - β₂| ≤ δ)
        (hγ₂ : |γ₂| + 1 ≤ 10 * Real.log (q : ℝ))
        (hpt₁ : |1 - β₁| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hpt₂ : |1 - β₂| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hzero₁ : DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0)
        (hzero₂ : DirichletCharacter.LFunction χ₂ ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I) = 0)
        (hmaxA : ∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * χ₂).primitiveCharacter u = 0 →
          |u.im| ≤ |γ₂| + 1 → u.re ≤ β₂)
        (hmaxB : ∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * χ₂⁻¹).primitiveCharacter u = 0 →
          |u.im| ≤ |γ₂| + 1 → u.re ≤ β₂)
        (hmaxC : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
          |u.im| ≤ 1 → u = (β₁ : ℂ) ∨ u.re ≤ β₂)
        (hmaxD : ∀ u : ℂ, DirichletCharacter.LFunction χ₂.primitiveCharacter u = 0 →
          |u.im| ≤ |γ₂| + 1 → u.re ≤ β₂)
        (hdivC : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
            (Metric.closedBall 0 (|γ₂| + 2))) (β₁ : ℂ) ≠ 0)
        (hdivD : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
            (Metric.closedBall 0 (|γ₂| + 2))) ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I) ≠ 0)
        (H₁ : Commons.NumberTheory.Linnik.L52Hyp χ₁ c₁ ε δ)
        (H₂ : Commons.NumberTheory.Linnik.L52Hyp χ₂ c ε δ)
        (H₃ : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂) c ε δ)
        (H₄ : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂⁻¹) c ε δ),
      0 ≤ (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β₂)) * t) * f t)
        - (∫ t in (0:ℝ)..x₀,
            Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β₂))) * t) * f t)
        - (∫ t in (0:ℝ)..x₀, f t)
        + f 0 * (c₁ + 2 * c + 4 * ε) := by

  intro f hcont hsupp hf2 hBnd hf0 hfnn hF ε hε δ hδ0 hδ1
  obtain ⟨q₀p, hq₀p⟩ := (Commons.NumberTheory.Linnik.Ksum_principal_le x₀ B hx₀ hB) hcont hsupp hf2 hBnd hε hf0
  obtain ⟨q₀a, hq₀a⟩ := (Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi x₀ B c hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hF hε hδ0 hδ1
  obtain ⟨q₀b, hq₀b⟩ := (Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi x₀ B c hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hF hε hδ0 hδ1
  obtain ⟨q₀n, hq₀n⟩ := (Ksum_le_single_ne_of_L52_phi x₀ B c₁ hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hF hε hδ0 hδ1
  refine ⟨max (max (max q₀p q₀a) q₀b) q₀n + 6, ?_⟩
  intro q _inst hq χ₁ χ₂ hχ₁ hχ₂ hχ₂χ₁ hχ₁χ₂ hχ₁χ₂' _ic₁ _ic₂ _ic₃ _ic₄ β₁ β₂ γ₂
    hβ₁ hβ₂ hγ₂ hpt₁ hpt₂ hzero₁ hzero₂ hmaxA hmaxB hmaxC hmaxD hdivC hdivD H₁ H₂ H₃ H₄
  have hq6 : 6 ≤ q := by omega
  have hq1 : 1 < q := by omega
  have hLpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hq_ge_p : q₀p ≤ q := by omega
  have hq_ge_a : q₀a ≤ q := by omega
  have hq_ge_b : q₀b ≤ q := by omega
  have hq_ge_n : q₀n ≤ q := by omega
  have hneA : (χ₁ * χ₂).primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₁χ₂
    rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₁ * χ₂), h]
    exact DirichletCharacter.changeLevel_one (χ₁ * χ₂).conductor_dvd_level
  have hneB : (χ₁ * χ₂⁻¹).primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₁χ₂'
    rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₁ * χ₂⁻¹), h]
    exact DirichletCharacter.changeLevel_one (χ₁ * χ₂⁻¹).conductor_dvd_level
  have hneC : χ₁.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₁
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, h]
    exact DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level
  have hneD : χ₂.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₂
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₂, h]
    exact DirichletCharacter.changeLevel_one χ₂.conductor_dvd_level
  have habsβ₂ : |β₂ - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    rw [abs_sub_comm]; exact hpt₂
  have hβ₂_ge : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ β₂ := by
    have h : 1 - β₂ ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := (abs_le.mp hpt₂).2
    linarith only [h]
  have hT_C : |((β₂:ℂ) : ℂ).im| + δ ≤ 1 := by
    have h : ((β₂:ℂ) : ℂ).im = 0 := by simp
    rw [h, abs_zero]; linarith only [hδ1]
  have hT_D : |(((β₂:ℂ) + (γ₂:ℂ)*Complex.I) : ℂ).im| + δ ≤ |γ₂| + 1 := by
    have h : (((β₂:ℂ) + (γ₂:ℂ)*Complex.I) : ℂ).im = γ₂ := by simp
    rw [h]; linarith [abs_nonneg γ₂, hδ1]
  have hT_B : |(((β₂:ℂ) - (γ₂:ℂ)*Complex.I) : ℂ).im| + δ ≤ |γ₂| + 1 := by
    have h : (((β₂:ℂ) - (γ₂:ℂ)*Complex.I) : ℂ).im = -γ₂ := by simp
    rw [h, abs_neg]; linarith [abs_nonneg γ₂, hδ1]
  have hzwC : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|((β₂:ℂ) : ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (((β₂:ℂ) : ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ (β₁:ℂ) → u.re ≤ ((β₂:ℂ) : ℂ).re :=
    window_hzero_of_Lzero_T χ₁.primitiveCharacter hneC hδ1 hT_C (by simp) hmaxC
  have hzwD : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + ((((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re :=
    window_le_of_Lzero_T χ₂.primitiveCharacter hneD hδ1 hT_D (by simp) hmaxD
  have hzwA : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction (χ₁*χ₂).primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + ((((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re :=
    window_le_of_Lzero_T (χ₁*χ₂).primitiveCharacter hneA hδ1 hT_D (by simp) hmaxA
  have hzwB : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction (χ₁*χ₂⁻¹).primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)-(γ₂:ℂ)*Complex.I):ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + ((((β₂:ℂ)-(γ₂:ℂ)*Complex.I):ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ (((β₂:ℂ)-(γ₂:ℂ)*Complex.I):ℂ).re :=
    window_le_of_Lzero_T (χ₁*χ₂⁻¹).primitiveCharacter hneB hδ1 hT_B (by simp) hmaxB
  have hβ₁_mem : (β₁:ℂ) ∈ Metric.closedBall 0 2 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs]
    have h1 : -(δ) ≤ 1 - β₁ := (abs_le.mp hβ₁).1
    have h2 : 1 - β₁ ≤ δ := (abs_le.mp hβ₁).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hdivC2 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|((β₂:ℂ):ℂ).im| + 2))) (β₁:ℂ) ≠ 0 := by
    have h : ((β₂:ℂ):ℂ).im = 0 := by simp
    rw [h, abs_zero, zero_add]
    rw [← divisor_closedBall_congr (R := 2) (R' := |γ₂| + 2) (by linarith [abs_nonneg γ₂])
      (fun z _ => (DirichletCharacter.differentiable_completedLFunction hneC).analyticAt z) hβ₁_mem]
    exact hdivC
  have hdivD' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im| + 2))) ((β₂:ℂ)+(γ₂:ℂ)*Complex.I) ≠ 0 := by
    have h : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im = γ₂ := by simp
    rw [h]; exact hdivD
  have hρnn : 0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-((((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))) * (t:ℂ))) * ((f t:ℝ):ℂ)).re := by
    have hcast : ((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ)) = (((β₂ - β₁) * Real.log (q:ℝ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast]
    exact laplaceIntegral_re_nonneg hx₀.le hfnn
  have hwin1 : ‖(1:ℂ) + (((β₂:ℂ):ℂ).im : ℂ) * Complex.I - (β₁:ℂ)‖ ≤ δ := by
    have h1 : (((β₂:ℂ):ℂ).im : ℂ) = 0 := by simp
    rw [h1, zero_mul, add_zero]
    have h2 : ‖(1:ℂ) - (β₁:ℂ)‖ = |1 - β₁| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [h2]; exact hβ₁
  have hwin2 : ‖(1:ℂ) + ((((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im : ℂ) * Complex.I - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I)‖ ≤ δ := by
    have h1 : ((((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im : ℂ) = (γ₂:ℂ) := by
      have h : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im = γ₂ := by simp
      rw [h]
    rw [h1]
    have h2 : ‖(1:ℂ) + (γ₂:ℂ)*Complex.I - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I)‖ = |1 - β₂| := by
      rw [show (1:ℂ) + (γ₂:ℂ)*Complex.I - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I) = ((1 - β₂ : ℝ):ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [h2]; exact hβ₂
  have hsim_1 : |((β₂:ℂ):ℂ).im| ≤ 10 * Real.log (q:ℝ) := by
    have h : ((β₂:ℂ):ℂ).im = 0 := by simp
    rw [h, abs_zero]; linarith [hLpos]
  have hsim_2 : |(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im| ≤ 10 * Real.log (q:ℝ) := by
    have h : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im = γ₂ := by simp
    rw [h]; linarith [hγ₂]
  have hsim_4 : |(((β₂:ℂ)-(γ₂:ℂ)*Complex.I):ℂ).im| ≤ 10 * Real.log (q:ℝ) := by
    have h : (((β₂:ℂ)-(γ₂:ℂ)*Complex.I):ℂ).im = -γ₂ := by simp
    rw [h, abs_neg]; linarith [hγ₂]
  have hre_1 : ((β₂:ℂ):ℂ).re = β₂ := by simp
  have hre_2 : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re = β₂ := by simp
  have hre_4 : (((β₂:ℂ)-(γ₂:ℂ)*Complex.I):ℂ).re = β₂ := by simp
  have hsre_1 : |((β₂:ℂ):ℂ).re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by rw [hre_1]; exact habsβ₂
  have hsre_2 : |(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by rw [hre_2]; exact habsβ₂
  have hsre_4 : |(((β₂:ℂ)-(γ₂:ℂ)*Complex.I):ℂ).re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by rw [hre_4]; exact habsβ₂
  have hge_1 : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ ((β₂:ℂ):ℂ).re := by rw [hre_1]; exact hβ₂_ge
  have hge_2 : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re := by rw [hre_2]; exact hβ₂_ge
  have hge_4 : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ (((β₂:ℂ)-(γ₂:ℂ)*Complex.I):ℂ).re := by rw [hre_4]; exact hβ₂_ge
  have hb1 := hq₀n (q := q) hq_ge_n χ₁ hχ₁ hsre_1 hsim_1 hge_1 H₁ hdivC2 hwin1 hρnn hzwC
  have hb2 := hq₀b (q := q) hq_ge_b χ₂ hχ₂ hsre_2 hsim_2 hge_2 H₂ hdivD' hwin2 hzwD
  have hb3 := hq₀a (q := q) hq_ge_a (χ₁ * χ₂) hχ₁χ₂ hsre_2 hsim_2 hge_2 H₃ hzwA
  have hb4 := hq₀a (q := q) hq_ge_a (χ₁ * χ₂⁻¹) hχ₁χ₂' hsre_4 hsim_4 hge_4 H₄ hzwB
  have hb0 := hq₀p (q := q) hq_ge_p (β := β₂) (lam := Real.log (q:ℝ) * (1 - β₂)) rfl habsβ₂
  have hRe1 : (∫ t in (0:ℝ)..x₀, Complex.exp (-((((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))) * (t:ℂ))) * ((f t:ℝ):ℂ)).re
      = ∫ t in (0:ℝ)..x₀, Real.exp (-((Real.log (q:ℝ) * (1 - β₁)) - (Real.log (q:ℝ) * (1 - β₂))) * t) * f t := by
    have hz1 : (((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))).im = 0 := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_im]
    rw [re_integral_exp_ofReal (z := ((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))) hz1 f]
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    have h : (((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))).re = (β₂ - β₁) * Real.log (q:ℝ) := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
    have harg : -((((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))).re * t)
        = -((Real.log (q:ℝ) * (1 - β₁)) - (Real.log (q:ℝ) * (1 - β₂))) * t := by
      rw [h]; ring
    rw [harg]
  have hRe2 : (∫ t in (0:ℝ)..x₀, Complex.exp (-(((((β₂:ℂ)+(γ₂:ℂ)*Complex.I) - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I)) * (Real.log (q:ℝ))) * (t:ℂ))) * ((f t:ℝ):ℂ)).re
      = ∫ t in (0:ℝ)..x₀, f t := by
    have hzero : ((β₂:ℂ)+(γ₂:ℂ)*Complex.I) - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I) = 0 := sub_self _
    simp only [hzero, zero_mul, neg_zero, Complex.exp_zero, one_mul]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
  have h0 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β₂ : ℂ)).re * f (Real.log n / Real.log (q:ℝ)))
      ≤ Real.log (q:ℝ) * (∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q:ℝ) * (1 - β₂)) * t) * f t)
        + f 0 * ε * Real.log (q:ℝ) := hb0
  have h1 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (χ₁ (n : ZMod q) / (n : ℂ) ^ (β₂ : ℂ)).re * f (Real.log n / Real.log (q:ℝ)))
      ≤ -Real.log (q:ℝ) * (∫ t in (0:ℝ)..x₀, Real.exp (-((Real.log (q:ℝ) * (1 - β₁)) - (Real.log (q:ℝ) * (1 - β₂))) * t) * f t)
        + f 0 * (c₁ + ε) * Real.log (q:ℝ) := by
    rw [hRe1] at hb1; exact hb1
  have h2 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I)).re * f (Real.log n / Real.log (q:ℝ)))
      ≤ -Real.log (q:ℝ) * (∫ t in (0:ℝ)..x₀, f t) + f 0 * (c + ε) * Real.log (q:ℝ) := by
    rw [hRe2] at hb2; exact hb2
  have h3 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I)).re * f (Real.log n / Real.log (q:ℝ)))
      ≤ f 0 * (c + ε) * Real.log (q:ℝ) := hb3
  have h4 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₂⁻¹) (n : ZMod q) / (n : ℂ) ^ ((β₂ : ℂ) - (γ₂ : ℂ) * Complex.I)).re * f (Real.log n / Real.log (q:ℝ)))
      ≤ f 0 * (c + ε) * Real.log (q:ℝ) := hb4
  exact lemma8_5_assembly_mixed (q := q) (L := Real.log (q:ℝ)) (c₁ := c₁) (c := c) (ε := ε) (β₂ := β₂) (γ₂ := γ₂)
    hfnn hx₀ hLpos hsupp χ₁ χ₂ h0 h1 h2 h3 h4

end Work.ZeroFreeTables
