/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg/mixedTrunc/collarAe`

The a.e. slice honesty of the mixed slot `V = z ∂_z ∂_θ u`, the two collar monotonicity
inequalities (`∫_{0}^{δ} ≤ ∫_{Iθ}` and `∫_{π/2-δ}^{π/2} ≤ ∫_{Iθ}`), and the outer
integrability of the two collar energies truncated by `χ_n · w²`.

All the analytic input is the outer finiteness `(H2)` of `MixedHon`, together with the
boundedness of `χ_n · w²` on the support of the radial cut-off.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedDefs
import Submission.Work.FTS.EllipticEst.Deleg.mixedTrunc.QuadBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Deleg.mixedTrunc

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary facts -/

/-- `wt z = w z ^ 2` is continuous on the open half-line. -/
theorem continuousOn_wt : ContinuousOn Work.FTS.EllipticEst.AeColl.wt (Set.Ioi 0) := by
  have hw : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact ContinuousOn.pow ((continuous_const.add continuous_id).continuousOn) 2
    · exact ContinuousOn.pow (continuous_id.continuousOn) 2
    · intro z hz
      exact pow_ne_zero 2 (ne_of_gt hz)
  have h : Work.FTS.EllipticEst.AeColl.wt = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl
  rw [h]
  exact ContinuousOn.pow hw 2

/-- `σ θ = sin(2θ)^{-η}` is continuous on the open interval `(0, π/2)`. -/
theorem continuousOn_sigθ :
    ContinuousOn Work.FTS.EllipticEst.AeColl.sigθ (Set.Ioo 0 (Real.pi / 2)) := by
  have h : Work.FTS.EllipticEst.AeColl.sigθ
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl
  rw [h]
  refine ContinuousOn.rpow_const ?_ ?_
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.mono
      (Set.subset_univ _)
  · intro θ hθ
    left
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))

/-- The two collar intervals are contained in `Iθ`. -/
theorem Ioo_left_subset_Iθ {δ : ℝ} (hδ2 : 4 * δ ≤ Real.pi / 2) :
    Set.Ioo 0 δ ⊆ Work.Spaces.Iθ := by
  have hpi : δ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  intro θ hθ
  exact ⟨le_of_lt hθ.1, le_trans (le_of_lt hθ.2) hpi⟩

theorem Ioo_right_subset_Iθ {δ : ℝ} (hδ2 : 4 * δ ≤ Real.pi / 2) :
    Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
  have hpi : δ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  intro θ hθ
  exact ⟨by linarith [hθ.1], le_of_lt hθ.2⟩

/-! ## The sup of `χ_n · w²` on the support of the radial cut-off -/

/-- An explicit bound for `χ_n z · w z ^ 2`. -/
def wtC (n : ℕ) : ℝ := ((1 + 3 * ((n : ℝ) + 1)) ^ 2 * ((n : ℝ) + 1) ^ 2) ^ 2

theorem wtC_nonneg (n : ℕ) : 0 ≤ wtC n := by rw [wtC]; positivity

theorem wt_le_wtC {n : ℕ} {z : ℝ} (hc : Work.FTS.EllipticEst.cut n z ≠ 0) :
    Work.FTS.EllipticEst.AeColl.wt z ≤ wtC n := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlo : 1 / ((n : ℝ) + 1) < z := by
    by_contra h
    push_neg at h
    exact hc (Work.FTS.EllipticEst.cut_apply_zero_of_le n h)
  have hhi : z < 3 * ((n : ℝ) + 1) := by
    by_contra h
    push_neg at h
    exact hc (Work.FTS.EllipticEst.cut_apply_zero_of_ge n h)
  have hzpos : 0 < z := lt_trans (div_pos one_pos hn) hlo
  have hzp : (1 : ℝ) < ((n : ℝ) + 1) ^ 2 * z ^ 2 := by
    have h1 : 1 < ((n : ℝ) + 1) * z := by
      rw [div_lt_iff₀ hn] at hlo
      linarith
    nlinarith [h1, hn, hzpos]
  have h1 : (1 + z) ^ 2 ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hw : Work.Spaces.w z ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 * ((n : ℝ) + 1) ^ 2 := by
    rw [Work.Spaces.w, div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    calc (1 + z) ^ 2 ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 := h1
      _ = (1 + 3 * ((n : ℝ) + 1)) ^ 2 * 1 := by ring
      _ ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 * (((n : ℝ) + 1) ^ 2 * z ^ 2) :=
          mul_le_mul_of_nonneg_left (le_of_lt hzp) (sq_nonneg _)
      _ = (1 + 3 * ((n : ℝ) + 1)) ^ 2 * ((n : ℝ) + 1) ^ 2 * z ^ 2 := by ring
  rw [Work.FTS.EllipticEst.AeColl.wt, wtC]
  exact pow_le_pow_left₀ (Work.FTS.EllipticEst.AngSecond.w_nonneg z) hw 2

theorem cut_mul_wt_abs_le (n : ℕ) (z : ℝ) :
    |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z| ≤ wtC n := by
  have hB0 := wtC_nonneg n
  have hwt0 : 0 ≤ Work.FTS.EllipticEst.AeColl.wt z := Work.FTS.EllipticEst.AeColl.wt_nonneg z
  rcases eq_or_ne (Work.FTS.EllipticEst.cut n z) 0 with h | h
  · rw [h, zero_mul, abs_zero]; exact hB0
  · have h1 := wt_le_wtC h
    have h2 : 0 ≤ Work.FTS.EllipticEst.cut n z := Work.FTS.EllipticEst.cut_nonneg n z
    have h3 : Work.FTS.EllipticEst.cut n z ≤ 1 := Work.FTS.EllipticEst.cut_le_one n z
    rw [abs_of_nonneg (mul_nonneg h2 hwt0)]
    calc Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z
        ≤ 1 * Work.FTS.EllipticEst.AeColl.wt z := mul_le_mul_of_nonneg_right h3 hwt0
      _ ≤ 1 * wtC n := mul_le_mul_of_nonneg_left h1 zero_le_one
      _ = wtC n := one_mul _

theorem cut_mul_wt_le (n : ℕ) (z : ℝ) :
    Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z ≤ wtC n := by
  have h := cut_mul_wt_abs_le n z
  rwa [abs_of_nonneg (mul_nonneg (Work.FTS.EllipticEst.cut_nonneg n z)
    (Work.FTS.EllipticEst.AeColl.wt_nonneg z))] at h

/-! ## Strong measurability of the collar slices -/

/-- The collar integral `z ↦ ∫_{S} σ · (z∂_z∂_θu)²` is a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_collar_Ioo (u : ℝ → ℝ → ℝ) {S : Set ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hS : MeasurableSet S) (hSI : S ⊆ Work.Spaces.Iθ) :
    MeasureTheory.AEStronglyMeasurable (fun z => ∫ θ in S,
        Work.FTS.EllipticEst.AeColl.sigθ θ
          * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hVz : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Vz u p.1 p.2) quad :=
    continuousOn_Vz_quad hu
  have hVz2 : ContinuousOn
      (fun p : ℝ × ℝ => (Work.FTS.EllipticEst.AeColl.Vz u p.1 p.2) ^ 2) quad :=
    ContinuousOn.pow hVz 2
  have hsig : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2) quad :=
    ContinuousOn.comp continuousOn_sigθ
      (ContinuousOn.mono (continuous_snd.continuousOn) (Set.subset_univ _))
      (fun p hp => hp.2)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2
      * (Work.FTS.EllipticEst.AeColl.Vz u p.1 p.2) ^ 2) quad :=
    ContinuousOn.mul hsig hVz2
  exact aesm_thetaIntegral_Ioi hcont hS hSI

/-! ## The outer integrability of one collar energy -/

/-- If the `z`-marginal `G z = ∫_{Iθ} σ (z∂_z∂_θu)²` is integrable and the collar integral
over `S` is dominated by it a.e., then the truncated collar energy `χ_n w² ∫_S σ V²` is
integrable. -/
theorem collar_outer_integrable (u : ℝ → ℝ → ℝ) (n : ℕ) {S : Set ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hS : MeasurableSet S) (hSI : S ⊆ Work.Spaces.Iθ)
    (hSle : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in S, Work.FTS.EllipticEst.AeColl.sigθ θ
        * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.sigθ θ
          * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
    (hGint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.AeColl.sigθ θ * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
      Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z
      * (∫ θ in S, Work.FTS.EllipticEst.AeColl.sigθ θ
        * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)) (Set.Ioi 0) := by
  have hGil : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.AeColl.sigθ θ * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hGint.mono_set Set.Ioi_subset_Ici_self
  have hdom : MeasureTheory.Integrable (fun z => wtC n * (∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.AeColl.sigθ θ * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hGil.const_mul (wtC n)
  have hcut : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.cut n z) (Set.Ioi 0) :=
    (Work.FTS.EllipticEst.cut_contDiff n).continuous.continuousOn
  have hcwaesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    ContinuousOn.aestronglyMeasurable (ContinuousOn.mul hcut continuousOn_wt) measurableSet_Ioi
  have haesm : MeasureTheory.AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z
      * (∫ θ in S, Work.FTS.EllipticEst.AeColl.sigθ θ
        * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    MeasureTheory.AEStronglyMeasurable.mul hcwaesm (aesm_collar_Ioo u hu hS hSI)
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  filter_upwards [hSle] with z hzle
  have hSnn : 0 ≤ ∫ θ in S, Work.FTS.EllipticEst.AeColl.sigθ θ
      * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg hS (fun θ hθ =>
      mul_nonneg (Work.FTS.EllipticEst.AeColl.sigθ_nonneg_of_mem (hSI hθ)) (sq_nonneg _))
  have hGnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.sigθ θ
      * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
      mul_nonneg (Work.FTS.EllipticEst.AeColl.sigθ_nonneg_of_mem hθ) (sq_nonneg _))
  have hcw : 0 ≤ Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z :=
    mul_nonneg (Work.FTS.EllipticEst.cut_nonneg n z) (Work.FTS.EllipticEst.AeColl.wt_nonneg z)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcw hSnn)]
  calc Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in S, Work.FTS.EllipticEst.AeColl.sigθ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
      ≤ Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.sigθ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hzle hcw
    _ ≤ wtC n * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.sigθ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right (cut_mul_wt_le n z) hGnn

/-! ## The target -/

theorem collarAe (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hδ2 : 4 * δ ≤ Real.pi / 2)
    (hu : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hMixed : Work.FTS.EllipticEst.Deleg.MixedHon u) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2
          * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioo 0 (Real.pi / 2)))
    ∧ (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (∫ θ in Set.Ioo 0 δ, Work.FTS.EllipticEst.AeColl.sigθ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
          ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.sigθ θ
              * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
    ∧ (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
            Work.FTS.EllipticEst.AeColl.sigθ θ
              * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
          ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.sigθ θ
              * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
    ∧ MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo 0 δ, Work.FTS.EllipticEst.AeColl.sigθ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)) (Set.Ioi 0)
    ∧ MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
            Work.FTS.EllipticEst.AeColl.sigθ θ
              * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)) (Set.Ioi 0) := by
  -- `(H1)` in the multiplication order of the statement
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ
        * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2) Work.Spaces.Iθ := by
    filter_upwards [hMixed.1] with z hz
    have h2 : (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ
          * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
        = (fun θ => (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2
            * Work.FTS.EllipticEst.AeColl.sigθ θ) := by
      funext θ; ring
    rw [h2]; exact hz
  -- the two collar monotonicity inequalities
  have hB : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Set.Ioo 0 δ, Work.FTS.EllipticEst.AeColl.sigθ θ
          * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.sigθ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2 := by
    filter_upwards [hslice] with z hz
    have hf_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        0 ≤ Work.FTS.EllipticEst.AeColl.sigθ θ
          * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2 := by
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
        measurableSet_Icc)] with θ hθ
      exact mul_nonneg (Work.FTS.EllipticEst.AeColl.sigθ_nonneg_of_mem hθ) (sq_nonneg _)
    exact MeasureTheory.integral_mono_measure
      (MeasureTheory.Measure.restrict_mono (Ioo_left_subset_Iθ hδ2) le_rfl) hf_ae hz
  have hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
          Work.FTS.EllipticEst.AeColl.sigθ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.sigθ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2 := by
    filter_upwards [hslice] with z hz
    have hf_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        0 ≤ Work.FTS.EllipticEst.AeColl.sigθ θ
          * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2 := by
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
        measurableSet_Icc)] with θ hθ
      exact mul_nonneg (Work.FTS.EllipticEst.AeColl.sigθ_nonneg_of_mem hθ) (sq_nonneg _)
    exact MeasureTheory.integral_mono_measure
      (MeasureTheory.Measure.restrict_mono (Ioo_right_subset_Iθ hδ2) le_rfl) hf_ae hz
  -- `(H2)`: the `z`-marginal of `V` is integrable
  have hGint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.AeColl.sigθ θ * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
      Work.Spaces.Iz := by
    have hfun : (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.sigθ θ
          * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
        = (fun z => ∫ θ in Work.Spaces.Iθ,
            (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig θ) := by
      funext z
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      show Work.FTS.EllipticEst.AeColl.sigθ θ * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2
        = (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ
      have hV : Work.FTS.EllipticEst.AeColl.Vz u z θ
          = z * Work.Spaces.pz (Work.Spaces.pth u) z θ := rfl
      rw [hV, Work.FTS.EllipticEst.AeColl.sigθ_eq_sig]
      ring
    rw [hfun]
    exact hMixed.2
  refine ⟨?_, hB, hC, ?_, ?_⟩
  · exact hMixed.1.mono fun z hz => hz.mono_set Set.Ioo_subset_Icc_self
  · exact collar_outer_integrable u n hu measurableSet_Ioo (Ioo_left_subset_Iθ hδ2) hB hGint
  · exact collar_outer_integrable u n hu measurableSet_Ioo (Ioo_right_subset_Iθ hδ2) hC hGint

end Work.FTS.EllipticEst.Deleg.mixedTrunc
