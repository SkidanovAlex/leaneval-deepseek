import Mathlib
import Submission.Work.ZeroFreeTables.XY.KsumChiTwoZerosWindow

open DirichletCharacter

namespace Work.ZeroFreeTables.OffAxis

/-- Elementary unweighting step: if the two retained kernels `F1`, `F2` are non-negative and the
divisor weights `w1`, `w2` are `≥ 1`, then dropping the weights only increases the (negative)
`-L`-multiple of their weighted sum. -/
private lemma neg_mul_weighted_le (L w1 w2 F1 F2 : ℝ) (hL : 0 ≤ L) (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2)
    (hF1 : 0 ≤ F1) (hF2 : 0 ≤ F2) :
    -(L) * (w1 * F1 + w2 * F2) ≤ -(L) * F1 - L * F2 := by
  have h1 : F1 ≤ w1 * F1 := by
    have := mul_le_mul_of_nonneg_right hw1 hF1
    simpa using this
  have h2 : F2 ≤ w2 * F2 := by
    have := mul_le_mul_of_nonneg_right hw2 hF2
    simpa using this
  have hs : F1 + F2 ≤ w1 * F1 + w2 * F2 := add_le_add h1 h2
  have h := mul_le_mul_of_nonpos_left hs (by linarith only [hL] : -(L) ≤ 0)
  calc -(L) * (w1 * F1 + w2 * F2) ≤ -(L) * (F1 + F2) := h
    _ = -(L) * F1 - L * F2 := by ring

/-- Two-zero window form of the parametric HB Lemma 5.2 bound, with general `c` and with the
two retained zeros' `F`-terms kept unweighted.  Model the proof on
`Submission/Work/ZeroFreeTables/XY/KsumChiTwoZerosWindow.lean` (same statement with `c = 1/8`
hard-coded and weighted retained terms): combine
`Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim` (which accepts a general `c`
and gives `Ksum ≤ -L * (weighted window sum) + f 0 * (c+ε) * L`) with
`Work.ZeroFreeTables.XY.windowSum_ge_two` (two retained zeros in the window dominate the weighted
window sum), then use the divisor weights `≥ 1` and the two kernels `≥ 0` to unweight the retained
terms.  Alternatively copy the shorter proof of
`Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi`
(`Submission/Work/NumberTheory/Linnik/scratch_l62app_phi.lean`), which is the one-zero case of
exactly this statement. -/
theorem KsumLeTwoOfL52 (x₀ B : ℝ) (c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hF : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hχ : χ ≠ 1) {s ρ ρ' : ℂ},
        |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
        |s.im| ≤ 10 * Real.log (q : ℝ) →
        1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ s.re →
        Commons.NumberTheory.Linnik.L52Hyp χ c ε δ →
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) ρ ≠ 0 →
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) ρ' ≠ 0 →
        ρ ≠ ρ' →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ →
        ρ.re ≤ s.re → ρ'.re ≤ s.re →
        (∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
            ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re) →
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / Real.log (q : ℝ)))
          ≤ -(Real.log (q : ℝ)) *
              (∫ t in (0:ℝ)..x₀,
                Complex.exp (-(((s - ρ) * ((Real.log (q:ℝ) : ℂ))) * (t : ℂ)))
                  * ((f t : ℝ) : ℂ)).re
            - (Real.log (q : ℝ)) *
              (∫ t in (0:ℝ)..x₀,
                Complex.exp (-(((s - ρ') * ((Real.log (q:ℝ) : ℂ))) * (t : ℂ)))
                  * ((f t : ℝ) : ℂ)).re
            + f 0 * (c + ε) * Real.log (q : ℝ) := by
  intro f hcont hsupp hf2 hBnd hf0 hF ε hε δ hδ0 hδ1
  obtain ⟨q₀, hq₀⟩ := (Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim
    x₀ B c hx₀ hB) hcont hsupp hf2 hBnd hf0 hε hδ0 hδ1
  refine ⟨q₀, ?_⟩
  intro q _inst hq χ _instc hχ s ρ ρ' hsre hsim hs1 hH hdiv hdiv' hne hwin hwin' hρre hρ're hzw
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hLnn : (0:ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg (by
    have hq1 : (1:ℕ) ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast hq1)
  have hHraw : ∀ s : ℂ, 1 + 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) ≤ s.re →
      s.re ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
      |s.im| ≤ 10 * Real.log (q : ℝ) →
      (-logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) s).re
        + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
            (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
        ≤ (c + ε/4) * Real.log (q : ℝ) := hH
  have hK := hq₀ hq χ hχ hHraw s hsre hsim hs1
  -- the two-zero window lower bound
  have hzw' : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ ρ → u ≠ ρ' → u.re ≤ s.re :=
    fun u hu hu2 _ _ => hzw u hu hu2
  have hlow := Work.ZeroFreeTables.XY.windowSum_ge_two x₀ (Real.log (q : ℝ))
    χ.primitiveCharacter hχ' (f := f) (s := s) (ρ := ρ) (ρ' := ρ') (δ := δ)
    hLnn hF hdiv hdiv' hne hwin hwin' hzw'
  -- divisor weights are `≥ 1`
  have hDnn : ∀ u : ℂ, (0:ℝ) ≤ ((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) := by
    intro u
    have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z
    exact Commons.Analysis.Complex.divisor_nonneg_on_closedBall hAn u
  have hw1 : (1:ℝ) ≤ (((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ) := by
    have h0Z : (0:ℤ) ≤ (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) ρ := by
      exact_mod_cast hDnn ρ
    have h1Z : (1:ℤ) ≤ (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) ρ := by omega
    exact_mod_cast h1Z
  have hw2 : (1:ℝ) ≤ (((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) ρ' : ℤ) : ℝ) := by
    have h0Z : (0:ℤ) ≤ (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) ρ' := by
      exact_mod_cast hDnn ρ'
    have h1Z : (1:ℤ) ≤ (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) ρ' := by omega
    exact_mod_cast h1Z
  -- the two kernels are non-negative
  have hF1nn : 0 ≤ (∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((s - ρ) * ((Real.log (q:ℝ) : ℂ))) * (t : ℂ)))
        * ((f t : ℝ) : ℂ)).re := by
    refine hF ((s - ρ) * ((Real.log (q:ℝ) : ℂ))) ?_
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg (by rw [Complex.sub_re]; linarith) hLnn
  have hF2nn : 0 ≤ (∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((s - ρ') * ((Real.log (q:ℝ) : ℂ))) * (t : ℂ)))
        * ((f t : ℝ) : ℂ)).re := by
    refine hF ((s - ρ') * ((Real.log (q:ℝ) : ℂ))) ?_
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg (by rw [Complex.sub_re]; linarith) hLnn
  -- combine
  have hchain : -(Real.log (q : ℝ)) *
        (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
          (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
            ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (Real.log (q : ℝ))) * (t : ℂ)))
              * ((f t : ℝ) : ℂ)).re) else 0))
      ≤ -(Real.log (q : ℝ)) *
            (∫ t in (0:ℝ)..x₀,
              Complex.exp (-(((s - ρ) * ((Real.log (q:ℝ) : ℂ))) * (t : ℂ)))
                * ((f t : ℝ) : ℂ)).re
        - (Real.log (q : ℝ)) *
            (∫ t in (0:ℝ)..x₀,
              Complex.exp (-(((s - ρ') * ((Real.log (q:ℝ) : ℂ))) * (t : ℂ)))
                * ((f t : ℝ) : ℂ)).re := by
    refine (mul_le_mul_of_nonpos_left hlow (by linarith only [hLnn] : -(Real.log (q:ℝ)) ≤ 0)).trans ?_
    exact neg_mul_weighted_le (Real.log (q : ℝ))
      ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ))
      ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|s.im| + 2))) ρ' : ℤ) : ℝ))
      (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - ρ) * ((Real.log (q:ℝ) : ℂ))) * (t : ℂ)))
          * ((f t : ℝ) : ℂ)).re
      (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - ρ') * ((Real.log (q:ℝ) : ℂ))) * (t : ℂ)))
          * ((f t : ℝ) : ℂ)).re
      hLnn hw1 hw2 hF1nn hF2nn
  exact hK.trans (add_le_add hchain le_rfl)

end Work.ZeroFreeTables.OffAxis
