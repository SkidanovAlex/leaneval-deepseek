import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarDefs
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarHyp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Elementary consequences of `FarHyp`: the `u`-slots are dominated by `FarR`

For every `j ≤ k+1` the far-window integral of the `j`-th `u`-slot against the *top* weight
`qW k γ` is bounded by `FarR k γ u g`: this is a monotone comparison between `rpow`s, plus the
observation that every summand of `FarR` is nonnegative.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by
    linarith [hθ.2, Real.pi_pos]⟩

/-- The top weight is nonnegative on `Iθ`. -/
theorem qW_nonneg {k : ℕ} {γ θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ qW k γ θ :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

/-- The `j`-th slot weight `sin(2θ)^{2j-4-γ}` is nonnegative on `Iθ`. -/
theorem slotWeight_nonneg {j : ℕ} {γ θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

/-- For `sin (2θ) ∈ [0,1]` the `rpow` is antitone in the exponent (both exponents nonzero, so
that the degenerate endpoint `sin (2θ) = 0` is harmless). -/
theorem rpow_sin_le_rpow_sin {a b θ : ℝ} (hab : b ≤ a) (ha : a ≠ 0) (hb : b ≠ 0)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) a ≤ Real.rpow (Real.sin (2 * θ)) b := by
  rcases eq_or_lt_of_le (sin_two_nonneg_Iθ hθ) with h0 | hpos
  · rw [← h0, show Real.rpow (0 : ℝ) a = 0 from Real.zero_rpow ha,
      show Real.rpow (0 : ℝ) b = 0 from Real.zero_rpow hb]
  · exact Real.rpow_le_rpow_of_exponent_ge hpos (Real.sin_le_one _) hab

/-- `2k - γ > 0` for `k ≥ 2`, `γ ≤ 5/4`. -/
theorem two_k_sub_gamma_pos {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} (hγ : γ ≤ 5 / 4) :
    0 < 2 * (k : ℝ) - γ := by
  have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

/-- The top weight is at most the `j`-th slot weight, for `3 ≤ j ≤ k+2`. -/
theorem qW_le_slotWeight {k j : ℕ} (hk : 2 ≤ k) {γ : ℝ} (hγ : γ ≤ 5 / 4) (hj3 : 3 ≤ j)
    (hjk : j ≤ k + 2) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    qW k γ θ ≤ Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) := by
  have ha : 2 * (k : ℝ) - γ ≠ 0 := ne_of_gt (two_k_sub_gamma_pos hk hγ)
  have hb : 2 * (j : ℝ) - 4 - γ ≠ 0 := by
    have hj : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj3
    intro h
    linarith
  refine rpow_sin_le_rpow_sin ?_ ha hb hθ
  have hjk' : (j : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast hjk
  linarith

/-- The top weight is at most `σ^{-η}` (`k ≥ 2`, `2k - γ ≥ 2.75 > -η`). -/
theorem qW_le_sEta {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} (hγ : γ ≤ 5 / 4) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    qW k γ θ ≤ Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) := by
  have ha : 2 * (k : ℝ) - γ ≠ 0 := ne_of_gt (two_k_sub_gamma_pos hk hγ)
  have hb : (-(Work.Spaces.eta)) ≠ 0 := by
    have := Work.Spaces.eta_pos
    linarith
  refine rpow_sin_le_rpow_sin ?_ ha hb hθ
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have := Work.Spaces.eta_pos
  linarith

/-- The top weight is at most `1` (`2k - γ ≥ 2.75 > 0`). -/
theorem qW_le_one {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} (hγ : γ ≤ 5 / 4) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : qW k γ θ ≤ 1 :=
  Real.rpow_le_one (sin_two_nonneg_Iθ hθ) (Real.sin_le_one _)
    (le_of_lt (two_k_sub_gamma_pos hk hγ))

/-- Every summand of `FarR` is nonnegative. -/
theorem FarR_nonneg {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g) :
    0 ≤ FarR k γ u g := by
  have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have h3 : 0 ≤ ∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
      (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
    Finset.sum_nonneg (fun j _ => MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (slotWeight_nonneg hθ)))
  have h4 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have h5 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have h6 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  simp only [FarR]
  linarith

/-- **The `u`-slots are dominated by `FarR`.**  For every `j ≤ k+1`, the far-window integral of
the `j`-th `u`-slot against the top weight `qW k γ` is at most `FarR k γ u g`. -/
theorem u_slot_le_FarR (k : ℕ) (hk : 2 ≤ k) {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g)
    {j : ℕ} (hj : j ≤ k + 1) :
    ∫ θ in farSet, (iteratedDeriv j u θ) ^ 2 * qW k γ θ ≤ FarR k γ u g := by
  have hγ2 := h.hγ2
  simp only [qW]
  -- nonnegativity of each summand of `FarR` (in the unfolded form)
  have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have h3 : 0 ≤ ∑ j' ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
      (iteratedDeriv j' u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j' : ℝ) - 4 - γ) :=
    Finset.sum_nonneg (fun j' _ => MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (slotWeight_nonneg hθ)))
  have h4 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have h5 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have h6 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have haesm : ∀ {f : ℝ → ℝ}, (∀ᵐ θ ∂(volume.restrict farSet), θ ∈ farSet → 0 ≤ f θ) →
      True := fun _ => trivial
  rcases lt_or_ge j 3 with hj3 | hj3
  · interval_cases j
    · -- `j = 0`
      have h1 : ∫ θ in farSet, (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) ≤ ∫ θ in farSet, (u θ) ^ 2 := by
        refine MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict farSet) ?_ ?_ ?_
        · filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume)
            (show MeasurableSet farSet from measurableSet_Icc)] with θ hθ
          exact mul_nonneg (sq_nonneg _) (qW_nonneg (farSet_subset_Iθ hθ))
        · exact h.hH6.mono_set farSet_subset_Iθ
        · filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume)
            (show MeasurableSet farSet from measurableSet_Icc)] with θ hθ
          have hq := qW_le_one hk hγ2 (farSet_subset_Iθ hθ)
          simp only [qW] at hq
          exact mul_le_of_le_one_right (sq_nonneg _) hq
      have h2' : ∫ θ in farSet, (u θ) ^ 2 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
        farIntegral_le_Iθ h.hH6 (fun θ _ => sq_nonneg _)
      have hL : ∫ θ in farSet, (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
        le_trans h1 h2'
      simp only [iteratedDeriv_zero]
      simp only [FarR]
      linarith
    · -- `j = 1`
      have h1 : ∫ θ in farSet, (deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          ≤ ∫ θ in farSet, (deriv u θ) ^ 2 := by
        refine MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict farSet) ?_ ?_ ?_
        · filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume)
            (show MeasurableSet farSet from measurableSet_Icc)] with θ hθ
          exact mul_nonneg (sq_nonneg _) (qW_nonneg (farSet_subset_Iθ hθ))
        · exact h.hH5.mono_set farSet_subset_Iθ
        · filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume)
            (show MeasurableSet farSet from measurableSet_Icc)] with θ hθ
          have hq := qW_le_one hk hγ2 (farSet_subset_Iθ hθ)
          simp only [qW] at hq
          exact mul_le_of_le_one_right (sq_nonneg _) hq
      have h2' : ∫ θ in farSet, (deriv u θ) ^ 2 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
        farIntegral_le_Iθ h.hH5 (fun θ _ => sq_nonneg _)
      have hL : ∫ θ in farSet, (deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 := le_trans h1 h2'
      simp only [iteratedDeriv_one]
      simp only [FarR]
      linarith
    · -- `j = 2`
      have heq : iteratedDeriv 2 u = fun θ => deriv (deriv u) θ := by
        funext θ
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
      have h1 : ∫ θ in farSet, (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          ≤ ∫ θ in farSet, (deriv (deriv u) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) := by
        refine MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict farSet) ?_ ?_ ?_
        · filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume)
            (show MeasurableSet farSet from measurableSet_Icc)] with θ hθ
          exact mul_nonneg (sq_nonneg _) (qW_nonneg (farSet_subset_Iθ hθ))
        · exact h.hH4.mono_set farSet_subset_Iθ
        · filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume)
            (show MeasurableSet farSet from measurableSet_Icc)] with θ hθ
          have hq := qW_le_sEta hk hγ2 (farSet_subset_Iθ hθ)
          simp only [qW] at hq
          exact mul_le_mul_of_nonneg_left hq (sq_nonneg _)
      have h2' : ∫ θ in farSet, (deriv (deriv u) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))
          ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
        farIntegral_le_Iθ h.hH4
          (fun θ hθ => mul_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
      have hL : ∫ θ in farSet, (iteratedDeriv 2 u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) := by
        rw [heq]
        exact le_trans h1 h2'
      simp only [heq, Pi.sub_apply]
      simp only [FarR]
      linarith
  · -- `j ≥ 3`
    have hmem : j ∈ Finset.Icc 3 (k + 1) := Finset.mem_Icc.mpr ⟨hj3, hj⟩
    have hInt := h.hH3 j hmem
    have h1 : ∫ θ in farSet, (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
        ≤ ∫ θ in farSet, (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) := by
      refine MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict farSet) ?_ ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume)
          (show MeasurableSet farSet from measurableSet_Icc)] with θ hθ
        exact mul_nonneg (sq_nonneg _) (qW_nonneg (farSet_subset_Iθ hθ))
      · exact hInt.mono_set farSet_subset_Iθ
      · filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume)
          (show MeasurableSet farSet from measurableSet_Icc)] with θ hθ
        have hq := qW_le_slotWeight hk hγ2 hj3 (by omega) (farSet_subset_Iθ hθ)
        simp only [qW] at hq
        exact mul_le_mul_of_nonneg_left hq (sq_nonneg _)
    have h2' : ∫ θ in farSet, (iteratedDeriv j u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)
        ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
      farIntegral_le_Iθ hInt (fun θ hθ => mul_nonneg (sq_nonneg _) (slotWeight_nonneg hθ))
    have hsum : ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)
        ≤ ∑ j' ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
            (iteratedDeriv j' u θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (j' : ℝ) - 4 - γ) :=
      Finset.single_le_sum (f := fun j' => ∫ θ in Work.Spaces.Iθ,
          (iteratedDeriv j' u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j' : ℝ) - 4 - γ))
        (fun j' _ => MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (slotWeight_nonneg hθ))) hmem
    have hL := le_trans h1 (le_trans h2' hsum)
    simp only [FarR]
    linarith

end Work.FTS.EllipticEst.remov.TopCoreB
