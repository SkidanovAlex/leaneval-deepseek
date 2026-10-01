import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.ZeroFreeTables.XY.KsumChiTwoZerosWindow

namespace Work.OffAxis

/-- Two-zero window form of the parametric HB Lemma 5.2 bound at `c = 1/6`, with the two retained zeros' `F`-terms kept unweighted: the companion of `Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi` (the one-zero case, in `Submission/Work/NumberTheory/Linnik/scratch_l62app_phi.lean`, whose proof this copies) in which two distinct zeros `ρ ≠ ρ'` of `χ` lie in the window of the point `s`, both with `Re ≤ Re s`. Route: `Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim` gives `Ksum ≤ -log q · (weighted window sum) + f 0 (1/6+ε) log q`; dominate the weighted window sum by the two retained kernels (`Work.ZeroFreeTables.XY.windowSum_ge_two`, which lives in `Submission/Work/ZeroFreeTables/XY/KsumChiTwoZerosWindow.lean` — add that import) and unweight with `divisor weights ≥ 1`, `kernel ≥ 0`. (This is the same statement as the placeholder `Work.ZeroFreeTables.OffAxis/KsumLeTwoOfL52` with the general `c` specialised to `1/6`.) -/
theorem KsumLeTwoMain6 (x₀ B : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
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
        Commons.NumberTheory.Linnik.L52Hyp χ (1/6) ε δ →
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
            + f 0 * (1/6 + ε) * Real.log (q : ℝ) := by
  intro f hcont hsupp hf2 hBnd hf0 hF ε hε δ hδ0 hδ1
  obtain ⟨q₀, hq₀⟩ := (Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim
    x₀ B (1/6) hx₀ hB) hcont hsupp hf2 hBnd hf0 hε hδ0 hδ1
  refine ⟨q₀, ?_⟩
  intro q _inst hq χ _instc hχ s ρ ρ' hsre hsim hs1 hH hdiv hdiv' hne hwin hwin' hρre hρ're hzw
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hLnn : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg (by
    have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast h1)
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z
  have hDnn : ∀ u : ℂ, (0:ℤ) ≤ (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) u :=
    fun u => (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn) u
  have hKraw := hq₀ hq χ hχ hH s hsre hsim hs1
  set W : ℝ := (∑ᶠ u : ℂ, (((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * ((Real.log (q:ℝ) : ℂ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re) else 0)) with hWdef
  set Fρ : ℝ := (∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((s - ρ) * ((Real.log (q:ℝ) : ℂ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
    with hFρdef
  set Fρ' : ℝ := (∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((s - ρ') * ((Real.log (q:ℝ) : ℂ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
    with hFρ'def
  set dρ : ℝ := (((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ) with hdρdef
  set dρ' : ℝ := (((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|s.im| + 2))) ρ' : ℤ) : ℝ) with hdρ'def
  have hKr : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / Real.log (q:ℝ)))
      ≤ -(Real.log (q:ℝ)) * W + f 0 * (1/6 + ε) * Real.log (q:ℝ) := by
    simpa only [← hWdef] using hKraw
  have hlow := Work.ZeroFreeTables.XY.windowSum_ge_two x₀ (Real.log (q:ℝ))
    χ.primitiveCharacter hχ'
    (f := f) (s := s) (ρ := ρ) (ρ' := ρ') (δ := δ) hLnn hF hdiv hdiv' hne hwin hwin'
    (fun u hu hw _ _ => hzw u hu hw)
  have hlowW : dρ * Fρ + dρ' * Fρ' ≤ W := by
    simpa only [← hWdef, ← hFρdef, ← hFρ'def, ← hdρdef, ← hdρ'def] using hlow
  have hFρnn : 0 ≤ Fρ := by
    rw [hFρdef]
    refine hF ((s - ρ) * ((Real.log (q:ℝ) : ℂ))) ?_
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have h : 0 ≤ (s - ρ).re := by rw [Complex.sub_re]; linarith
    exact mul_nonneg h hLnn
  have hFρ'nn : 0 ≤ Fρ' := by
    rw [hFρ'def]
    refine hF ((s - ρ') * ((Real.log (q:ℝ) : ℂ))) ?_
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have h : 0 ≤ (s - ρ').re := by rw [Complex.sub_re]; linarith
    exact mul_nonneg h hLnn
  have hdρ1 : (1:ℝ) ≤ dρ := by
    rw [hdρdef]
    have hD1 : (1:ℤ) ≤ (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) ρ := by
      have hpos := lt_of_le_of_ne (hDnn ρ) (Ne.symm hdiv)
      omega
    exact_mod_cast hD1
  have hdρ'1 : (1:ℝ) ≤ dρ' := by
    rw [hdρ'def]
    have hD1 : (1:ℤ) ≤ (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) ρ' := by
      have hpos := lt_of_le_of_ne (hDnn ρ') (Ne.symm hdiv')
      omega
    exact_mod_cast hD1
  have hmain : Fρ + Fρ' ≤ W := by
    have h1 : Fρ ≤ dρ * Fρ := by
      have h := mul_le_mul_of_nonneg_right hdρ1 hFρnn
      simpa using h
    have h2 : Fρ' ≤ dρ' * Fρ' := by
      have h := mul_le_mul_of_nonneg_right hdρ'1 hFρ'nn
      simpa using h
    linarith only [hlowW, h1, h2]
  have hstep1 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / Real.log (q:ℝ)))
      ≤ -(Real.log (q:ℝ)) * W + f 0 * (1/6 + ε) * Real.log (q:ℝ) := hKr
  have hstep2 : -(Real.log (q:ℝ)) * W + f 0 * (1/6 + ε) * Real.log (q:ℝ)
      ≤ -(Real.log (q:ℝ)) * (Fρ + Fρ') + f 0 * (1/6 + ε) * Real.log (q:ℝ) :=
    add_le_add (mul_le_mul_of_nonpos_left hmain (by linarith only [hLnn])) le_rfl
  have hstep3 : -(Real.log (q:ℝ)) * (Fρ + Fρ') + f 0 * (1/6 + ε) * Real.log (q:ℝ)
      = -(Real.log (q:ℝ)) * Fρ - (Real.log (q:ℝ)) * Fρ'
        + f 0 * (1/6 + ε) * Real.log (q:ℝ) := by
    ring
  exact hstep1.trans (hstep2.trans (le_of_eq hstep3))


end Work.OffAxis
