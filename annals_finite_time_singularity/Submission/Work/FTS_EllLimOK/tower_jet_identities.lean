import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.EllipticEst.Core.HkSqLHSv2Slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slice-level reduction for `HkSqLHS_le_summands_v2`

For a fixed `z`, the iterated-integral definition of `HkSq` reduces, at the level of the
angular integral, to the sum of the summands appearing in `HkSqLHS_le_summands_v2`:

`∫_θ HkIntegrand α k (α • D_z∂_θV) z θ ≤ α² (∑_r mixIntS(D_z^rV)(z) + ∑_{i,j} mixedIntS α i j V (z))`.

The proof is

* `v2_zBlock_ae`, `v2_mixedBlock_ae` (a.e. identification of the two blocks of `HkIntegrand`);
* `integral_add_le_nonneg` and `integral_finset_sum_le` subadditivity of the Bochner integral
  for nonnegative a.e.-measurable functions (this is where the `AEMeasurable` facts
  `v2_aesm_zSummand`, `v2_aesm_mSummand` are consumed, and where the junk-value convention of
  the Bochner integral is used in the helpful direction);
* `v2_sliceId`, `v2_mixedId` identification of the single-slice integrals with `mixIntS`,
  `mixedIntS`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

set_option autoImplicit false

/-! ## Subadditivity of the Bochner integral, two-term case -/

/-- `∫ (f + g) ≤ ∫ f + ∫ g` for nonnegative a.e.-measurable functions (the two-term case of
`integral_finset_sum_le`). -/
theorem integral_add_le_nonneg {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g : α → ℝ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) :
    ∫ a, (f a + g a) ∂μ ≤ ∫ a, f a ∂μ + ∫ a, g a ∂μ := by
  have h := integral_finset_sum_le (μ := μ) (s := Finset.range 2) (ι := ℕ)
    (f := fun i : ℕ => fun a => if i = 0 then f a else g a) ?hm ?hn
  · have h1 : ∀ a, (∑ i ∈ Finset.range 2, (if i = 0 then f a else g a)) = f a + g a := by
      intro a
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    have h2 : (∑ i ∈ Finset.range 2, ∫ a, (if i = 0 then f a else g a) ∂μ)
        = ∫ a, f a ∂μ + ∫ a, g a ∂μ := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h1), h2] at h
    exact h
  · intro i _
    by_cases hi : i = 0
    · simpa only [hi, if_true] using hf
    · simpa only [if_neg hi] using hg
  · intro i _
    by_cases hi : i = 0
    · simpa only [hi, if_true] using hf0
    · simpa only [if_neg hi] using hg0

/-- A finite sum of a.e.-measurable real functions is a.e.-measurable, in the pointwise form
`a ↦ ∑ i ∈ s, f i a`. -/
theorem aemeasurable_finset_sum_apply {ι α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {s : Finset ι} {f : ι → α → ℝ}
    (h : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (fun a => ∑ i ∈ s, f i a) μ := by
  have hmain : AEMeasurable (∑ i ∈ s, f i) μ := Finset.aemeasurable_sum s h
  refine (aemeasurable_congr ?_).mpr hmain
  exact Filter.Eventually.of_forall (fun a => by simp only [Finset.sum_apply])

/-! ## The single-slice identifications -/

/-- The `θ`-integral of one pure `D_z`-summand is the corresponding `mixIntS`. -/
theorem v2_sliceId (u : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
      = mixIntS u z := by
  show _ = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))

/-- The `θ`-integral of one mixed summand is the corresponding `mixedIntS`. -/
theorem v2_mixedId (α : ℝ) (i j : ℕ) (u : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.thGam α θ)
      = mixedIntS α i j u z := by
  show _ = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth u) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))

/-! ## Measurability and nonnegativity of the blocks -/

/-- The pure `D_z` block is a.e. strongly measurable as a function of `θ`. -/
theorem v2_aesm_zSummand {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (k : ℕ) :
    ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ : ℝ => ∑ r ∈ Finset.range (k + 1),
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  exact aemeasurable_finset_sum_apply (fun r _ => by
    simpa only [Work.FTS.EllipticEst.thEta] using
      v2_aesm_slice ((hV.DzIter r).pth.Dz) (-(Work.Spaces.eta)) z hz)

/-- The mixed block is a.e. strongly measurable as a function of `θ`. -/
theorem v2_aesm_mSummand {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (α : ℝ)
    (k : ℕ) :
    ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
          else 0)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  exact aemeasurable_finset_sum_apply (fun i _ => aemeasurable_finset_sum_apply (fun j _ => by
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      simpa only [Work.FTS.EllipticEst.thGam] using
        v2_aesm_slice ((hV.pth).mixed (j + 1) i) (-(Work.Spaces.gam α)) z hz
    · simp only [if_neg hc]
      exact aemeasurable_const))

/-- The pure `D_z` block is nonnegative a.e. -/
theorem v2_nn_zSummand (k : ℕ) {V : ℝ → ℝ → ℝ} (z : ℝ) :
    0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => ∑ r ∈ Finset.range (k + 1),
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  refine Finset.sum_nonneg (fun r _ => ?_)
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Work.FTS.EllipticEst.thEta_nonneg hθ)

/-- The mixed block is nonnegative a.e. -/
theorem v2_nn_mSummand (α : ℝ) (k : ℕ) {V : ℝ → ℝ → ℝ} (z : ℝ) :
    0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
          else 0) := by
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
  by_cases hc : 1 ≤ i ∧ i + j ≤ k
  · simp only [if_pos hc]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.EllipticEst.thGam_nonneg hθ)
  · simp only [if_neg hc]
    exact le_refl 0

/-! ## The two blocks of the slice inequality -/

/-- The pure `D_z` block of the slice inequality. -/
theorem v2_zSlice_le (k : ℕ) {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) :
    ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ∑ r ∈ Finset.range (k + 1),
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ ∑ r ∈ Finset.range (k + 1), mixIntS (Work.Spaces.DzIter r V) z := by
  intro z hz
  refine le_trans (integral_finset_sum_le (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (s := Finset.range (k + 1)) (f := fun r : ℕ => fun θ : ℝ =>
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) ?_ ?_) ?_
  · intro r _
    simpa only [Work.FTS.EllipticEst.thEta] using
      v2_aesm_slice ((hV.DzIter r).pth.Dz) (-(Work.Spaces.eta)) z hz
  · intro r _
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  · exact Finset.sum_le_sum (fun r _ => le_of_eq (v2_sliceId (Work.Spaces.DzIter r V) z))

/-- The mixed block of the slice inequality. -/
theorem v2_mSlice_le (k : ℕ) {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V) :
    ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
          else 0)
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0 := by
  intro z hz
  refine le_trans (integral_finset_sum_le (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (s := Finset.range (k + 1)) (f := fun i : ℕ => fun θ : ℝ =>
      ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
        else 0) ?_ ?_) ?_
  · intro i _
    exact aemeasurable_finset_sum_apply (fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        simpa only [Work.FTS.EllipticEst.thGam] using
          v2_aesm_slice ((hV.pth).mixed (j + 1) i) (-(Work.Spaces.gam α)) z hz
      · simp only [if_neg hc]
        exact aemeasurable_const)
  · intro i _
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    refine Finset.sum_nonneg (fun j _ => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Work.FTS.EllipticEst.thGam_nonneg hθ)
    · simp only [if_neg hc]
      exact le_refl 0
  · refine Finset.sum_le_sum (fun i _ => ?_)
    refine le_trans (integral_finset_sum_le (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (s := Finset.range (k + 1)) (f := fun j : ℕ => fun θ : ℝ =>
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
        else 0) ?_ ?_) ?_
    · intro j _
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        simpa only [Work.FTS.EllipticEst.thGam] using
          v2_aesm_slice ((hV.pth).mixed (j + 1) i) (-(Work.Spaces.gam α)) z hz
      · simp only [if_neg hc]
        exact aemeasurable_const
    · intro j _
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Work.FTS.EllipticEst.thGam_nonneg hθ)
      · simp only [if_neg hc]
        exact le_refl 0
    · refine Finset.sum_le_sum (fun j _ => ?_)
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        exact le_of_eq (v2_mixedId α i j V z)
      · simp only [if_neg hc]
        exact le_of_eq (MeasureTheory.integral_zero ℝ ℝ)

/-! ## The slice inequality -/

/-- **The slice-level reduction.**  For `0 < α`, `V` of class `C^∞` on the open quadrant and
`z ∈ [0,∞)`, the angular integral of `HkIntegrand α k (α • D_z∂_θV)` is bounded by `α²` times
the two families of summands of `HkSqLHS_le_summands_v2`. -/
theorem v2_slice_le (k : ℕ) {α : ℝ} {V : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hV : Work.FTS.EllipticEst.SmoothOpen V) :
    ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ)
        ≤ α ^ 2 * ((∑ r ∈ Finset.range (k + 1), mixIntS (Work.Spaces.DzIter r V) z)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)) := by
  intro z hz
  have h3a := v2_zBlock_ae (k := k) (α := α) (V := V) hV z hz
  have h3b := v2_mixedBlock_ae (k := k) (α := α) hα (V := V) hV z hz
  have hcomb : (fun θ : ℝ => Work.Spaces.HkIntegrand α k
        (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ =>
        α ^ 2 * (∑ r ∈ Finset.range (k + 1),
            (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
            else 0)) := by
    filter_upwards [h3a, h3b] with θ h1 h2
    simp only [Work.Spaces.HkIntegrand]
    beta_reduce at h1 h2
    rw [h1, h2]
  have hfac : (∫ θ in Work.Spaces.Iθ,
        (α ^ 2 * (∑ r ∈ Finset.range (k + 1),
            (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                  * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
              else 0)))
      = α ^ 2 * ∫ θ in Work.Spaces.Iθ,
          ((∑ r ∈ Finset.range (k + 1),
              (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
                * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                    * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ
                else 0)) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  rw [MeasureTheory.integral_congr_ae hcomb, hfac]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg α)
  refine le_trans (integral_add_le_nonneg (v2_aesm_zSummand hV k z hz)
    (v2_aesm_mSummand hV α k z hz) (v2_nn_zSummand (V := V) k z)
    (v2_nn_mSummand α k (V := V) z)) ?_
  exact add_le_add (v2_zSlice_le k hV z hz) (v2_mSlice_le (α := α) k hV z hz)

end Work.EllipticEst.Core
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.PthHkIntegrandLeOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000


end Work.FTS.EllipticEst.ThetaU
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSlotAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Pointwise

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-! ## Differentiation of an interval integral in the spatial variable -/

/-- **Parametric differentiation of an interval integral** (the `IntervalIntegral` form of
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, in the shape used below:
the differentiation variable is the *first* argument of `G`, the integration variable `s` the
second one).

The hypotheses are those of Mathlib's lemma with the `∀ᶠ x in 𝓝 x₀` replaced by
`∀ x ∈ Ioo x₁ x₂` (so that the callers can discharge them from pointwise bounds). -/
theorem hasDerivAt_intervalIntegral_of_deriv_le {G G' : ℝ → ℝ → ℝ} {bound : ℝ → ℝ}
    {a b x₀ x₁ x₂ : ℝ} (hx₁ : x₁ < x₀) (hx₂ : x₀ < x₂)
    (hG_meas : ∀ x ∈ Set.Ioo x₁ x₂,
      AEStronglyMeasurable (fun s : ℝ => G s x) (volume.restrict (Set.uIoc a b)))
    (hG_int : IntervalIntegrable (fun s : ℝ => G s x₀) volume a b)
    (hG'_meas : AEStronglyMeasurable (fun s : ℝ => G' s x₀) (volume.restrict (Set.uIoc a b)))
    (h_bound : ∀ t ∈ Set.uIoc a b, ∀ x ∈ Set.Ioo x₁ x₂, |G' t x| ≤ bound t)
    (h_bound_int : IntervalIntegrable bound volume a b)
    (h_diff : ∀ t ∈ Set.uIoc a b, ∀ x ∈ Set.Ioo x₁ x₂, HasDerivAt (fun x' => G t x') (G' t x) x) :
    HasDerivAt (fun x => ∫ s in a..b, G s x) (∫ s in a..b, G' s x₀) x₀ := by
  have hmem : Set.Ioo x₁ x₂ ∈ 𝓝 x₀ := isOpen_Ioo.mem_nhds ⟨hx₁, hx₂⟩
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun x s => G s x) (F' := fun x s => G' s x) (bound := bound)
    (x₀ := x₀) (s := Set.Ioo x₁ x₂) hmem ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hmem] with x hx
    exact hG_meas x hx
  · exact hG_int
  · exact hG'_meas
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun t ht x hx => ?_))
    simpa [Real.norm_eq_abs] using h_bound t ht x hx
  · exact h_bound_int
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun t ht x hx => ?_))
    exact h_diff t ht x hx

/-- The `θ`-slice derivative of a `C^∞`-on-`Q0` function (the companion of the workspace lemma
`Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice`, which is the `z`-direction). -/
theorem SmoothOpen.hasDerivAt_slice_th {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun θ' => F z θ') (Work.Spaces.pth F z θ) θ := by
  have hd : DifferentiableAt ℝ (fun θ' => F z θ') θ :=
    ((hF.curry_θ hz).differentiableOn (by rw [Work.Stability.smoothOrder]; simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  simpa only [Work.Spaces.pth] using hd.hasDerivAt

/-- A continuous function strictly positive on a compact interval has a positive lower bound. -/
theorem exists_pos_min_sin_two {θlo θhi : ℝ} (h0 : 0 < θlo) (h1 : θhi < Real.pi / 2) :
    ∃ smin : ℝ, 0 < smin ∧ ∀ y ∈ Set.Icc θlo θhi, smin ≤ Real.sin (2 * y) := by
  have hpos : ∀ y ∈ Set.Icc θlo θhi, (0:ℝ) < Real.sin (2 * y) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le h0 hy.1
    have hy1 : y < Real.pi / 2 := lt_of_le_of_lt hy.2 h1
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  obtain ⟨a', ha'pos, ha'⟩ := (isCompact_Icc).exists_forall_le' (f := fun y => Real.sin (2 * y))
    (by fun_prop) (a := 0) hpos
  exact ⟨a', ha'pos, ha'⟩

/-! ## Locality of the iterated operators on an open set -/

/-- `∂_z` is local on an open set. -/
theorem pz_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) {z θ : ℝ} (hzθ : (z, θ) ∈ V) :
    Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (Continuous.prodMk_left θ).continuousAt.eventually (hV.mem_nhds hzθ)
  have hev : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun z' => g z' θ) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  simpa only [Work.Spaces.pz] using hev.deriv_eq

/-- `∂_θ` is local on an open set. -/
theorem pth_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) {z θ : ℝ} (hzθ : (z, θ) ∈ V) :
    Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (Continuous.prodMk_right z).continuousAt.eventually (hV.mem_nhds hzθ)
  have hev : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ') := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  simpa only [Work.Spaces.pth] using hev.deriv_eq

/-- The iterates `D_z^j` are local on an open set. -/
theorem DzIter_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j f))
      (Function.uncurry (Work.Spaces.DzIter j g)) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro p hp
    have hzp : Work.Spaces.pz (Work.Spaces.DzIter j f) p.1 p.2
        = Work.Spaces.pz (Work.Spaces.DzIter j g) p.1 p.2 := pz_congr_of_isOpen hV ih hp
    show p.1 * Work.Spaces.pz (Work.Spaces.DzIter j f) p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j g) p.1 p.2
    rw [hzp]

/-- The mixed slots `D_z^jD_θ^i` are local on an open set. -/
theorem mixed_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed j i f))
      (Function.uncurry (Work.Spaces.mixed j i g)) V := by
  intro p hp
  have h1 : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i f))
      (Function.uncurry (Work.Spaces.DthIter i g)) V :=
    Work.Blocks.Half.DthIter_congrOn hV h i
  exact DzIter_congr_of_isOpen hV h1 j hp

/-! ## The angular induction -/

/-- **The angular part of the exchange.**  For a family `H` with the hypotheses described at the
top of the file, the `D_θ`-iterates (`i ≤ 4`) of the interval integral are the interval integrals
of the `D_θ`-iterates, on the interior of the closed box. -/
theorem DthIter_intervalIntegral_eq {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0:ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (H s) z θ)
        (volume.restrict (Set.Icc (0:ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed k l (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    (l : ℕ) (hl : l ≤ 4) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0:ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have hsubIoc : Set.Ioc a b ⊆ Set.Icc (0:ℝ) T := fun t ht =>
    ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  induction l with
  | zero => intro z θ _; rfl
  | succ l ih =>
    intro z θ hzθ
    rw [Set.mem_prod] at hzθ
    obtain ⟨hzz, hθθ⟩ := hzθ
    have hzcl : z ∈ Set.Icc z₁ z₂ := ⟨le_of_lt hzz.1, le_of_lt hzz.2⟩
    have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      hboxQ ⟨hzcl, ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩⟩
    obtain ⟨hz0, hθ0, hθπ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzQ
    set θlo : ℝ := max θ₁ (θ / 2) with hθlo
    set θhi : ℝ := min θ₂ ((θ + Real.pi / 2) / 2) with hθhi
    have hθlo_lt : θlo < θ := by
      rw [hθlo]; exact max_lt hθθ.1 (by linarith)
    have hθ_lt_θhi : θ < θhi := by
      rw [hθhi]; exact lt_min hθθ.2 (by linarith)
    have hθlo0 : 0 < θlo := lt_of_lt_of_le (by linarith : (0:ℝ) < θ / 2) (le_max_right _ _)
    have hθhi_lt : θhi < Real.pi / 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    obtain ⟨smin, hsmin_pos, hsmin_le⟩ := exists_pos_min_sin_two hθlo0 hθhi_lt
    have hmem_box : ∀ y ∈ Set.Ioo θlo θhi,
        (z, y) ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ := by
      intro y hy
      exact ⟨hzcl, ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hy.1),
        le_of_lt (lt_of_lt_of_le hy.2 (min_le_left _ _))⟩⟩
    have hyQ : ∀ y ∈ Set.Ioo θlo θhi, (z, y) ∈ Work.FTS.EllipticEst.Q0 :=
      fun y hy => hboxQ (hmem_box y hy)
    have hyf : ∀ y ∈ Set.Ioo θlo θhi, 0 < y ∧ y < Real.pi / 2 := by
      intro y hy
      obtain ⟨-, hy1, hy2⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hyQ y hy)
      exact ⟨hy1, hy2⟩
    have hcore := hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b)
      (G := fun t y => Work.Spaces.DthIter l (H t) z y)
      (G' := fun t y => Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y))
      (bound := fun _ => C / smin) hθlo_lt hθ_lt_θhi ?_ ?_ ?_ ?_ ?_ ?_
    rotate_left
    · intro y hy
      have := (hmeas 0 l z y (hyQ y hy)).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [Work.Spaces.mixed_zero_left] using this
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine IntegrableOn.of_bound ?_ ?_ C ?_
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
      · have h1 := (hmeas 0 l z θ hzQ).mono_measure (Measure.restrict_mono hsubIoc le_rfl)
        simpa only [Work.Spaces.mixed_zero_left] using h1
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs]
        have htT : t ∈ Set.Icc (0:ℝ) T := hsubIoc ht
        have := hbdd t htT 0 l (by omega) (z, θ) ⟨hzcl, ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩⟩
        simpa only [Work.Spaces.mixed_zero_left] using this
    · have h1 := (hmeas 0 (l + 1) z θ hzQ).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [div_eq_mul_inv] using h1.mul_const (Real.sin (2 * θ))⁻¹
    · intro t ht y hy
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hsinpos : 0 < Real.sin (2 * y) :=
        lt_of_lt_of_le hsmin_pos (hsmin_le y (Set.Ioo_subset_Icc_self hy))
      have hb := hbdd t htT 0 (l + 1) (by omega) (z, y) (hmem_box y hy)
      calc |Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y)|
          = |Work.Spaces.mixed 0 (l + 1) (H t) z y| / Real.sin (2 * y) := by
            rw [abs_div, abs_of_pos hsinpos]
        _ ≤ C / Real.sin (2 * y) := div_le_div_of_nonneg_right hb (le_of_lt hsinpos)
        _ ≤ C / smin := div_le_div_of_nonneg_left hC hsmin_pos
            (hsmin_le y (Set.Ioo_subset_Icc_self hy))
    · exact intervalIntegrable_const
    · intro t ht y hy
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hder := SmoothOpen.hasDerivAt_slice_th
        (Work.FTS.LocData.contDiffOn_DthIter Work.FTS.EllipticEst.isOpen_Q0
          (hsm t htT) l) hz0 (hyf y hy)
      have hid : Work.Spaces.pth (Work.Spaces.DthIter l (H t)) z y
          = Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y) := by
        simpa only [Work.Spaces.mixed_zero_left] using
          Work.FTS.StrongEps.LocUnif.pth_mixed_div 0 l (hsm t htT) z y (hyQ y hy)
      exact hder.congr_deriv hid
    have hev : (fun y => Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z y) =ᶠ[𝓝 θ]
        (fun y => ∫ s in a..b, Work.Spaces.DthIter l (H s) z y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθθ] with y hy
      exact ih (by omega) z y ⟨hzz, hy⟩
    have hpth : Work.Spaces.pth (Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ)) z θ
        = ∫ s in a..b, Work.Spaces.mixed 0 (l + 1) (H s) z θ / Real.sin (2 * θ) := by
      show deriv (fun y => Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z y) θ = _
      rw [hev.deriv_eq, hcore.deriv]
    have hsinne : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    calc Work.Spaces.DthIter (l + 1) (fun z θ => ∫ s in a..b, H s z θ) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth
            (Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ)) z θ := by
          rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      _ = Real.sin (2 * θ) * (∫ s in a..b,
            Work.Spaces.mixed 0 (l + 1) (H s) z θ / Real.sin (2 * θ)) := by rw [hpth]
      _ = Real.sin (2 * θ) * ((∫ s in a..b,
            Work.Spaces.mixed 0 (l + 1) (H s) z θ) / Real.sin (2 * θ)) := by
          rw [intervalIntegral.integral_div]
      _ = ∫ s in a..b, Work.Spaces.mixed 0 (l + 1) (H s) z θ :=
          mul_div_cancel₀ _ hsinne
      _ = ∫ s in a..b, Work.Spaces.DthIter (l + 1) (H s) z θ := rfl

/-! ## The radial induction -/

/-- **The radial part of the exchange.**  For a family `H` with the hypotheses described at the
top of the file, the `D_z`-iterates of the interval integral of `D_θ^i (H s)` are the interval
integrals of `D_z^j D_θ^i (H s)`, for `j + i ≤ 4`. -/
theorem DzIter_intervalIntegral_eq {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0:ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (H s) z θ)
        (volume.restrict (Set.Icc (0:ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed k l (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    (k l : ℕ) (hkl : k + l ≤ 4) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.DzIter k (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) z θ
        = ∫ s in a..b, Work.Spaces.DzIter k (Work.Spaces.DthIter l (H s)) z θ := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0:ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have hsubIoc : Set.Ioc a b ⊆ Set.Icc (0:ℝ) T := fun t ht =>
    ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  induction k with
  | zero => intro z θ _; rfl
  | succ k ih =>
    intro z θ hzθ
    rw [Set.mem_prod] at hzθ
    obtain ⟨hzz, hθθ⟩ := hzθ
    have hθcl : θ ∈ Set.Icc θ₁ θ₂ := ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩
    have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      hboxQ ⟨⟨le_of_lt hzz.1, le_of_lt hzz.2⟩, hθcl⟩
    obtain ⟨hz0, hθ0, hθπ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzQ
    set zlo : ℝ := max z₁ (z / 2) with hzlo
    have hzlo_lt : zlo < z := by
      rw [hzlo]; exact max_lt hzz.1 (by linarith)
    have hmem_box : ∀ x ∈ Set.Ioo zlo z₂,
        (x, θ) ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ := by
      intro x hx
      exact ⟨⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx.1), le_of_lt hx.2⟩, hθcl⟩
    have hxQ : ∀ x ∈ Set.Ioo zlo z₂, (x, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      fun x hx => hboxQ (hmem_box x hx)
    have hxpos : ∀ x ∈ Set.Ioo zlo z₂, 0 < x := fun x hx =>
      lt_of_lt_of_le (by linarith : (0:ℝ) < z / 2)
        (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx.1))
    have hcore := hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b)
      (G := fun t x => Work.Spaces.DzIter k (Work.Spaces.DthIter l (H t)) x θ)
      (G' := fun t x => Work.Spaces.mixed (k + 1) l (H t) x θ / x)
      (bound := fun _ => C * (2 / z)) hzlo_lt hzz.2 ?_ ?_ ?_ ?_ ?_ ?_
    rotate_left
    · intro x hx
      have := (hmeas k l x θ (hxQ x hx)).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [Work.Spaces.mixed] using this
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine IntegrableOn.of_bound ?_ ?_ C ?_
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
      · have h1 := (hmeas k l z θ hzQ).mono_measure (Measure.restrict_mono hsubIoc le_rfl)
        simpa only [Work.Spaces.mixed] using h1
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs]
        have htT : t ∈ Set.Icc (0:ℝ) T := hsubIoc ht
        exact hbdd t htT k l (by omega) (z, θ) ⟨⟨le_of_lt hzz.1, le_of_lt hzz.2⟩, hθcl⟩
    · have h1 := (hmeas (k + 1) l z θ hzQ).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [div_eq_mul_inv] using h1.mul_const z⁻¹
    · intro t ht x hx
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hx2 : z / 2 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx.1)
      have hb := hbdd t htT (k + 1) l (by omega) (x, θ) (hmem_box x hx)
      calc |Work.Spaces.mixed (k + 1) l (H t) x θ / x|
          = |Work.Spaces.mixed (k + 1) l (H t) x θ| / x := by
            rw [abs_div, abs_of_pos (hxpos x hx)]
        _ ≤ C / x := div_le_div_of_nonneg_right hb (le_of_lt (hxpos x hx))
        _ ≤ C / (z / 2) := div_le_div_of_nonneg_left hC (by linarith) hx2
        _ = C * (2 / z) := by field_simp
    · exact intervalIntegrable_const
    · intro t ht x hx
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hder : HasDerivAt (fun x' => Work.Spaces.mixed k l (H t) x' θ)
          (Work.Spaces.pz (Work.Spaces.mixed k l (H t)) x θ) x :=
        Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice
          (Work.FTS.LocData.contDiffOn_mixed Work.FTS.EllipticEst.isOpen_Q0 (hsm t htT) k l)
          (θ := θ) ⟨hθ0, hθπ2⟩ (hxpos x hx)
      exact hder.congr_deriv
        (Work.FTS.StrongEps.LocUnif.pz_mixed_div k l (hsm t htT) x θ (hxQ x hx))
    have hloc : (fun x => Work.Spaces.DzIter k
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) x θ)
        =ᶠ[𝓝 z] (fun x => ∫ s in a..b, Work.Spaces.DzIter k (Work.Spaces.DthIter l (H s)) x θ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hzz] with x hx
      exact ih (by omega) x θ ⟨hx, hθθ⟩
    have hpz : Work.Spaces.pz (Work.Spaces.DzIter k
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ)) z θ
        = ∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ / z := by
      show deriv (fun x => Work.Spaces.DzIter k
        (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) x θ) z = _
      rw [hloc.deriv_eq, hcore.deriv]
    have hzne : z ≠ 0 := ne_of_gt hz0
    calc Work.Spaces.DzIter (k + 1)
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter k
            (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ)) z θ := by
          rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      _ = z * (∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ / z) := by rw [hpz]
      _ = z * ((∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ) / z) := by
          rw [intervalIntegral.integral_div]
      _ = ∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ := mul_div_cancel₀ _ hzne
      _ = ∫ s in a..b, Work.Spaces.DzIter (k + 1) (Work.Spaces.DthIter l (H s)) z θ := rfl

/-! ## The exchange for `mixed j i` -/

/-- **The exchange of `mixed j i` (`j + i ≤ 4`) with the interval integral.** -/
theorem mixed_intervalIntegral_eq {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0:ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (H s) z θ)
        (volume.restrict (Set.Icc (0:ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed k l (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ 4) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := by
  have hbox_open : IsOpen (Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂) := isOpen_Ioo.prod isOpen_Ioo
  intro z θ hzθ
  have hA := DthIter_intervalIntegral_eq (H := H) haT hbT hab hC hsm hmeas hbdd hboxQ i (by omega)
  have hB := DzIter_intervalIntegral_eq (H := H) haT hbT hab hC hsm hmeas hbdd hboxQ j i hji z θ hzθ
  have hA' : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => ∫ s in a..b, H s z θ)))
      (Function.uncurry (fun z θ => ∫ s in a..b, Work.Spaces.DthIter i (H s) z θ))
      (Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂) := fun p hp => hA p.1 p.2 hp
  have hloc := DzIter_congr_of_isOpen hbox_open hA' j hzθ
  simp only [Function.uncurry] at hloc
  calc Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
      = Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => ∫ s in a..b, H s z θ)) z θ := rfl
    _ = Work.Spaces.DzIter j (fun z θ => ∫ s in a..b, Work.Spaces.DthIter i (H s) z θ) z θ := hloc
    _ = ∫ s in a..b, Work.Spaces.DzIter j (Work.Spaces.DthIter i (H s)) z θ := hB
    _ = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := rfl

/-! ## The compact box around a compact subset of the open quadrant -/


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.LocTower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false
set_option maxHeartbeats 1000000


/-! ## The extraction data -/

/-- **The data produced by the extraction.**  A subsequence `φ`, the limits `F c d` of the
families `mixed c d (G (φ n))` (`c + d ≤ 4`), their local uniform convergence on `Q0`, and the two
"tower" relations obtained by differentiating the *definitional* relations
`mixed (c+1) d (G n) = D_z (mixed c d (G n))` and `mixed c (d+1) (G n) = D_θ (mixed c d (G n))`
along the sequence. -/
structure LimData (G : ℕ → ℝ → ℝ → ℝ) (φ : ℕ → ℕ) (F : ℕ → ℕ → ℝ → ℝ → ℝ) : Prop where
  /-- the fifteen families converge locally uniformly on `Q0`. -/
  conv : ∀ (c d : ℕ), c + d ≤ 4 → TendstoLocallyUniformlyOn
    (fun n p => Work.Spaces.mixed c d (G (φ n)) p.1 p.2)
    (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0
  /-- the `z`-tower relation `D_z (F c d) = F (c+1) d`. -/
  dz : ∀ (c d : ℕ), c + d ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
    HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z
  /-- the `θ`-tower relation `D_θ (F c d) = F c (d+1)`. -/
  dth : ∀ (c d : ℕ), c + d ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
    HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ

/-- The limits of the extraction are continuous on `Q0` (locally uniform limits of the continuous
functions `mixed c d (G (φ n))`). -/
theorem LimData.continuousOn {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n)) (h : LimData G φ F)
    (c d : ℕ) (hcd : c + d ≤ 4) :
    ContinuousOn (fun p : ℝ × ℝ => F c d p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  refine (h.conv c d hcd).continuousOn (Frequently.of_forall fun n => ?_)
  exact (show ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.mixed c d (G (φ n)))) Work.FTS.EllipticEst.Q0 from
    (hsm (φ n)).mixed c d).continuousOn

/-! ## `C⁴` for `F 0 0`, via the `(log z, log tan θ)`-coordinates -/

/-- In the coordinates `u = log z`, `v = log tan θ` the operators `D_z` and `D_θ` become the
plain derivatives `∂_u` and `2 ∂_v`; consequently the limits `F c d` (scaled by `2^{-d}`) form a
partial-derivative tower on all of `ℝ²`, and the partial-tower lemma
`Work.FTS.StrongLWP.Sobolev.contDiffOn_four_of_partial_tower` gives `C⁴` for `F 0 0` after
composing back with `(z,θ) ↦ (log z, log tan θ)`, which is smooth on `Q0`. -/
theorem contDiffOn_four_of_LimData {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n)) (h : LimData G φ F) :
    ContDiffOn ℝ 4 (Function.uncurry (F 0 0)) Work.FTS.EllipticEst.Q0 := by
  classical
  -- the composed family (the factor `2^{-d}` makes `D_θ = 2 ∂_v` into `∂_v`)
  set S : ℕ → ℕ → ℝ → ℝ → ℝ := fun c d u v =>
    F c d (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ d with hSdef
  -- the composed map lands in the open quadrant
  have hmemQ : ∀ p : ℝ × ℝ, (Real.exp p.1, Real.arctan (Real.exp p.2))
      ∈ Work.FTS.EllipticEst.Q0 := by
    intro p
    refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos p.1, ?_, ?_⟩
    · rw [Real.arctan_pos]; exact Real.exp_pos p.2
    · exact Real.arctan_lt_pi_div_two _
  have hΦcont : Continuous fun p : ℝ × ℝ =>
      (Real.exp p.1, Real.arctan (Real.exp p.2)) := by fun_prop
  -- continuity of every tower entry on `ℝ²`
  have hcont : ∀ a b : ℕ, a + b ≤ 4 →
      ContinuousOn (fun p : ℝ × ℝ => S a b p.1 p.2) Set.univ := by
    intro a b hab
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        F a b (Real.exp p.1) (Real.arctan (Real.exp p.2))) Set.univ :=
      (h.continuousOn hsm a b hab).comp hΦcont.continuousOn (fun p _ => hmemQ p)
    exact h1.div_const _
  -- the `u`-derivative relation
  have hsz : ∀ a b : ℕ, a + b ≤ 3 → ∀ u v : ℝ,
      HasDerivAt (fun u' : ℝ => S a b u' v) (S (a + 1) b u v) u := by
    intro a b hab u v
    have hθ : Real.arctan (Real.exp v) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨by rw [Real.arctan_pos]; exact Real.exp_pos v, Real.arctan_lt_pi_div_two _⟩
    have hzQ : (Real.exp u, Real.arctan (Real.exp v)) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos u, hθ⟩
    have hd := h.dz a b hab (Real.exp u) (Real.arctan (Real.exp v)) hzQ
    have hcomp := hd.comp u (Real.hasDerivAt_exp u)
    have hval : F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) / Real.exp u
        * Real.exp u = F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) := by
      field_simp
    rw [hval] at hcomp
    have h2 := hcomp.div_const (2 ^ b)
    show HasDerivAt (fun u' : ℝ => F a b (Real.exp u') (Real.arctan (Real.exp v)) / 2 ^ b)
      (F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ b) u
    exact h2
  -- the `v`-derivative relation
  have hth : ∀ a b : ℕ, a + b ≤ 3 → ∀ u v : ℝ,
      HasDerivAt (fun v' : ℝ => S a b u v') (S a (b + 1) u v) v := by
    intro a b hab u v
    have hθ : Real.arctan (Real.exp v) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨by rw [Real.arctan_pos]; exact Real.exp_pos v, Real.arctan_lt_pi_div_two _⟩
    have hzQ : (Real.exp u, Real.arctan (Real.exp v)) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos u, hθ⟩
    have hd := h.dth a b hab (Real.exp u) (Real.arctan (Real.exp v)) hzQ
    have hcomp := hd.comp v (hasDerivAt_arctan_exp v)
    have hsin : Real.sin (2 * Real.arctan (Real.exp v)) ≠ 0 := by
      rw [show Real.sin (2 * Real.arctan (Real.exp v))
            = 2 * Real.exp v / (1 + (Real.exp v) ^ 2) from by
        have hS : (0 : ℝ) < 1 + (Real.exp v) ^ 2 := by positivity
        rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
        rw [show (2 : ℝ) * (Real.exp v / √(1 + (Real.exp v) ^ 2))
              * (1 / √(1 + (Real.exp v) ^ 2))
            = 2 * Real.exp v / (√(1 + (Real.exp v) ^ 2)) ^ 2 from by ring]
        rw [Real.sq_sqrt hS.le]]
      positivity
    have hval : F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v))
          / Real.sin (2 * Real.arctan (Real.exp v))
          * (Real.sin (2 * Real.arctan (Real.exp v)) / 2)
        = F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 := by
      field_simp
    rw [hval] at hcomp
    have h2 := hcomp.div_const (2 ^ b)
    have hgoal : HasDerivAt (fun v' : ℝ => F a b (Real.exp u) (Real.arctan (Real.exp v')) / 2 ^ b)
        (F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 / 2 ^ b) v := h2
    have hval2 : F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 / 2 ^ b
        = F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ (b + 1) := by
      rw [pow_succ]
      ring
    rw [hval2] at hgoal
    show HasDerivAt (fun v' : ℝ => F a b (Real.exp u) (Real.arctan (Real.exp v')) / 2 ^ b)
      (F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ (b + 1)) v
    exact hgoal
  -- the partial-derivative tower on `ℝ²`
  have h4 := Work.FTS.StrongLWP.Sobolev.contDiffOn_four_of_partial_tower
    (φ := fun u v => S 0 0 u v) (D := S) isOpen_univ (fun u v => rfl) hcont
    (fun a b hab z θ _ => hsz a b hab z θ) (fun a b hab z θ _ => hth a b hab z θ)
  -- transfer back through the smooth inverse coordinate change
  have hcomp2 : ContDiffOn ℝ 4
      ((fun p : ℝ × ℝ => S 0 0 p.1 p.2) ∘
        (fun p : ℝ × ℝ => (Real.log p.1, Real.log (Real.tan p.2))))
      Work.FTS.EllipticEst.Q0 :=
    h4.comp (contDiffOn_logLog_Q0 4) (fun p _ => Set.mem_univ _)
  refine hcomp2.congr fun p hp => ?_
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have htan : Real.tan p.2 ≠ 0 :=
    ne_of_gt (Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1)
  have hθπ : p.2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith⟩
  simp only [Function.comp_apply, Function.uncurry]
  rw [hSdef]
  simp only [Real.exp_log hz, Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1),
    Real.arctan_tan hθπ.1 hθπ.2, pow_zero, div_one]

/-! ## Identification of the limits with the mixed derivatives of `F 0 0` -/

/-- **The limits are the mixed derivatives of the limit function.**  This uses only the tower
relations of `LimData` and the *definitional* identities `DzIter (c+1) = Dz ∘ DzIter c` and
`DthIter (d+1) = Dth ∘ DthIter d`. -/
theorem identify {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (h : LimData G φ F) :
    ∀ (c d : ℕ), c + d ≤ 4 → Set.EqOn (fun p : ℝ × ℝ => F c d p.1 p.2)
      (fun p : ℝ × ℝ => Work.Spaces.mixed c d (F 0 0) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  classical
  -- first: `F 0 d = D_θ^d (F 0 0)`, by the `θ`-tower relations
  have step1 : ∀ d : ℕ, d ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      F 0 d z θ = Work.Spaces.DthIter d (F 0 0) z θ := by
    intro d
    induction d with
    | zero => intro _ z θ _; rfl
    | succ d ih =>
        intro hd z θ hzθ
        have hprev : d ≤ 4 := by omega
        have heq : ∀ θ' : ℝ, (z, θ') ∈ Work.FTS.EllipticEst.Q0 →
            F 0 d z θ' = Work.Spaces.DthIter d (F 0 0) z θ' :=
          fun θ' hθ' => ih hprev z θ' hθ'
        have hderiv : deriv (fun θ' : ℝ => F 0 d z θ') θ
            = deriv (fun θ' : ℝ => Work.Spaces.DthIter d (F 0 0) z θ') θ := by
          refine Filter.EventuallyEq.deriv_eq ?_
          have hsl : {θ' : ℝ | (z, θ') ∈ Work.FTS.EllipticEst.Q0} ∈ 𝓝 θ :=
            (Work.FTS.EllipticEst.isOpen_Q0.preimage
              (by fun_prop : Continuous fun θ' : ℝ => (z, θ'))).mem_nhds hzθ
          filter_upwards [hsl] with θ' hθ'
          exact heq θ' hθ'
        obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
        have hsin : Real.sin (2 * θ) ≠ 0 :=
          ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
        have hval := (h.dth 0 d (by omega) z θ hzθ).deriv
        calc F 0 (d + 1) z θ
            = Real.sin (2 * θ) * (F 0 (d + 1) z θ / Real.sin (2 * θ)) := by field_simp
          _ = Real.sin (2 * θ) * deriv (fun θ' : ℝ => F 0 d z θ') θ := by rw [hval]
          _ = Real.sin (2 * θ) *
                deriv (fun θ' : ℝ => Work.Spaces.DthIter d (F 0 0) z θ') θ := by rw [hderiv]
          _ = Work.Spaces.DthIter (d + 1) (F 0 0) z θ := rfl
  -- then: `F c d = D_z^c (D_θ^d (F 0 0))`, by the `z`-tower relations
  have step2 : ∀ d : ℕ, d ≤ 4 → ∀ c : ℕ, c + d ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      F c d z θ = Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z θ := by
    intro d hd c
    induction c with
    | zero =>
        intro hcd z θ hzθ
        exact step1 d hd z θ hzθ
    | succ c ih =>
        intro hcd z θ hzθ
        have hprev : c + d ≤ 4 := by omega
        have heq : ∀ z' : ℝ, (z', θ) ∈ Work.FTS.EllipticEst.Q0 →
            F c d z' θ = Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z' θ :=
          fun z' hz' => ih hprev z' θ hz'
        have hderiv : deriv (fun z' : ℝ => F c d z' θ) z
            = deriv (fun z' : ℝ =>
                Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z' θ) z := by
          refine Filter.EventuallyEq.deriv_eq ?_
          have hsl : {z' : ℝ | (z', θ) ∈ Work.FTS.EllipticEst.Q0} ∈ 𝓝 z :=
            (Work.FTS.EllipticEst.isOpen_Q0.preimage
              (by fun_prop : Continuous fun z' : ℝ => (z', θ))).mem_nhds hzθ
          filter_upwards [hsl] with z' hz'
          exact heq z' hz'
        obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
        have hval := (h.dz c d (by omega) z θ hzθ).deriv
        calc F (c + 1) d z θ
            = z * (F (c + 1) d z θ / z) := by field_simp
          _ = z * deriv (fun z' : ℝ => F c d z' θ) z := by rw [hval]
          _ = z * deriv (fun z' : ℝ =>
                Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z' θ) z := by rw [hderiv]
          _ = Work.Spaces.DzIter (c + 1) (Work.Spaces.DthIter d (F 0 0)) z θ := rfl
  intro c d hcd p hp
  have hd4 : d ≤ 4 := by omega
  exact step2 d hd4 c hcd p.1 p.2 hp

/-! ## The tower relations for the limits -/

/-- **The tower relations of `LimData` from the convergence alone.**  Differentiating the
*definitional* identities `mixed (c+1) d (G n) = D_z (mixed c d (G n))` and
`mixed c (d+1) (G n) = D_θ (mixed c d (G n))` along the convergent subsequence gives the two
relations `D_z (F c d) = F (c+1) d` and `D_θ (F c d) = F c (d+1)`; the second one uses the
commutation `D_θ ∘ D_z^c = D_z^c ∘ D_θ` on the `C^∞` functions `G (φ n)`
(`DzDthIterCommOn_smooth`). -/
theorem limData_of_conv {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hconv : ∀ (c d : ℕ), c + d ≤ 4 → TendstoLocallyUniformlyOn
      (fun n p => Work.Spaces.mixed c d (G (φ n)) p.1 p.2)
      (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0) :
    LimData G φ F := by
  refine ⟨hconv, ?_, ?_⟩
  · -- the `z`-relations
    intro c d hcd z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hsl : ∀ z' ∈ Set.Ioi (0 : ℝ), (z', θ) ∈ Work.FTS.EllipticEst.Q0 :=
      fun z' hz' => ⟨hz', hθ0, hθ1⟩
    have hinv : ContinuousOn (fun p : ℝ × ℝ => (p.1)⁻¹) Work.FTS.EllipticEst.Q0 :=
      continuousOn_fst.inv₀ fun p hp => ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    have hdiv : TendstoLocallyUniformlyOn
        (fun (n : ℕ) (p : ℝ × ℝ) => Work.Spaces.mixed (c + 1) d (G (φ n)) p.1 p.2 / p.1)
        (fun p : ℝ × ℝ => F (c + 1) d p.1 p.2 / p.1) Filter.atTop
        Work.FTS.EllipticEst.Q0 := by
      have h1 := tendstoLocallyUniformlyOn_mul_continuousOn
        Work.FTS.EllipticEst.isOpen_Q0 (hconv (c + 1) d (by omega)) hinv
      simpa only [div_eq_mul_inv, mul_comm] using h1
    have hf' : TendstoLocallyUniformlyOn
        (fun n (z' : ℝ) => Work.Spaces.mixed (c + 1) d (G (φ n)) z' θ / z')
        (fun z' : ℝ => F (c + 1) d z' θ / z') Filter.atTop (Set.Ioi 0) :=
      tendstoLocallyUniformlyOn_slice_fst hsl hdiv
    have hf : TendstoLocallyUniformlyOn
        (fun n (z' : ℝ) => Work.Spaces.mixed c d (G (φ n)) z' θ)
        (fun z' : ℝ => F c d z' θ) Filter.atTop (Set.Ioi 0) :=
      tendstoLocallyUniformlyOn_slice_fst hsl (hconv c d (by omega))
    have hder : ∀ᶠ n in Filter.atTop, ∀ z' ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun z'' : ℝ => Work.Spaces.mixed c d (G (φ n)) z'' θ)
          (Work.Spaces.mixed (c + 1) d (G (φ n)) z' θ / z') z' := by
      refine Eventually.of_forall fun n z' hz' => ?_
      have hd := ((hsm (φ n)).mixed c d).hasDerivAt_slice ⟨hθ0, hθ1⟩ hz'
      rwa [(mixed_partials_of_smoothOpen c d (hsm (φ n))).1 z' θ (hsl z' hz')] at hd
    have hmain : HasDerivAt (fun z' : ℝ => F c d z' θ)
        ((fun z' : ℝ => F (c + 1) d z' θ / z') z) z := by
      refine hasDerivAt_of_tendstoLocallyUniformlyOn
        (f' := fun n (z' : ℝ) => Work.Spaces.mixed (c + 1) d (G (φ n)) z' θ / z')
        (g' := fun z' : ℝ => F (c + 1) d z' θ / z') isOpen_Ioi hf' hder ?_ hz
      intro z' hz'
      exact hf.tendsto_at hz'
    exact hmain
  · -- the `θ`-relations
    intro c d hcd z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hsl : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2), (z, θ') ∈ Work.FTS.EllipticEst.Q0 :=
      fun θ' hθ' => ⟨hz, hθ'⟩
    have hsin0 : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin (2 * p.2) ≠ 0 := by
      intro p hp
      obtain ⟨-, hp0, hp1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hinv : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2))⁻¹)
        Work.FTS.EllipticEst.Q0 :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).inv₀ hsin0
    have hdiv : TendstoLocallyUniformlyOn
        (fun (n : ℕ) (p : ℝ × ℝ) => Work.Spaces.mixed c (d + 1) (G (φ n)) p.1 p.2
          / Real.sin (2 * p.2))
        (fun p : ℝ × ℝ => F c (d + 1) p.1 p.2 / Real.sin (2 * p.2)) Filter.atTop
        Work.FTS.EllipticEst.Q0 := by
      have h1 := tendstoLocallyUniformlyOn_mul_continuousOn
        Work.FTS.EllipticEst.isOpen_Q0 (hconv c (d + 1) (by omega)) hinv
      simpa only [div_eq_mul_inv, mul_comm] using h1
    have hf' : TendstoLocallyUniformlyOn
        (fun n (θ' : ℝ) => Work.Spaces.mixed c (d + 1) (G (φ n)) z θ' / Real.sin (2 * θ'))
        (fun θ' : ℝ => F c (d + 1) z θ' / Real.sin (2 * θ')) Filter.atTop
        (Set.Ioo 0 (π / 2)) :=
      tendstoLocallyUniformlyOn_slice_snd hsl hdiv
    have hf : TendstoLocallyUniformlyOn
        (fun n (θ' : ℝ) => Work.Spaces.mixed c d (G (φ n)) z θ')
        (fun θ' : ℝ => F c d z θ') Filter.atTop (Set.Ioo 0 (π / 2)) :=
      tendstoLocallyUniformlyOn_slice_snd hsl (hconv c d (by omega))
    have hder : ∀ᶠ n in Filter.atTop, ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        HasDerivAt (fun θ'' : ℝ => Work.Spaces.mixed c d (G (φ n)) z θ'')
          (Work.Spaces.mixed c (d + 1) (G (φ n)) z θ' / Real.sin (2 * θ')) θ' := by
      refine Eventually.of_forall fun n θ' hθ' => ?_
      have hd : HasDerivAt (fun θ'' : ℝ => Work.Spaces.mixed c d (G (φ n)) z θ'')
          (Work.Spaces.pth (Work.Spaces.mixed c d (G (φ n))) z θ') θ' :=
        (((hsm (φ n)).mixed c d).curry_θ hz).contDiffAt
          (isOpen_Ioo.mem_nhds hθ') |>.differentiableAt (by simp) |>.hasDerivAt
      rwa [(mixed_partials_of_smoothOpen c d (hsm (φ n))).2.1 z θ' (hsl θ' hθ')] at hd
    have hmain : HasDerivAt (fun θ' : ℝ => F c d z θ')
        ((fun θ' : ℝ => F c (d + 1) z θ' / Real.sin (2 * θ')) θ) θ := by
      refine hasDerivAt_of_tendstoLocallyUniformlyOn
        (f' := fun n (θ' : ℝ) => Work.Spaces.mixed c (d + 1) (G (φ n)) z θ' / Real.sin (2 * θ'))
        (g' := fun θ' : ℝ => F c (d + 1) z θ' / Real.sin (2 * θ')) isOpen_Ioo hf' hder ?_
        ⟨hθ0, hθ1⟩
      intro θ' hθ'
      exact hf.tendsto_at hθ'
    exact hmain


end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.mixed_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps

/-- Additivity of the mixed operator `D_z^j D_θ^i` on the open quadrant, for data that are
`C^∞` on the (open) quadrant.

This is the instance of the general additivity `Work.FTS.EllipticEst.SmoothOpen.mixed_add`
for the raw hypothesis shape `∀ n, ContDiffOn ℝ n (Function.uncurry ·) Q0` used by the
downstream statements; the two shapes are equivalent by
`Work.FTS.EllipticEst.smoothOpen_iff_forall`.

(Note: `open scoped Real` is needed for the `π` of the `Set.Ioo 0 (π / 2)` hypothesis to be
`Real.pi`, matching `Work.FTS.EllipticEst.Q0`; without it `π` would be auto-bound as an
arbitrary real.) -/
theorem mixed_add {j i : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.mixed j i (fun z' θ' => f z' θ' + g z' θ') z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ :=
  Work.FTS.EllipticEst.SmoothOpen.mixed_add
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mpr hf)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mpr hg)
    j i z θ hz hθ.1 hθ.2

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS_EllLimOK.LimTower_dz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

/-- **The `(1a)` tower, radial and angular halves.**

Let `G n` be a sequence of functions which are `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)`
and let the mixed jets `mixed c d (G (φ n)) = D_z^c D_θ^d (G (φ n))` converge locally uniformly
on `Q0` to `F c d`, for all `c + d ≤ 2`.  Then the limiting first-order jets are differentiable
with the derivatives predicted by the operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ`:

* `∂_z (F c d) = F (c+1) d / z` (the recursion `D_z^{c+1} = z ∂_z ∘ D_z^c`);
* `∂_θ (F c d) = F c (d+1) / sin(2θ)` (the recursion `D_θ^{d+1} = sin(2θ) ∂_θ ∘ D_θ^d`).

The proof is `hasDerivAt_of_tendstoLocallyUniformlyOn` applied slicewise: on each `z`-slice
(with `θ ∈ (0,π/2)` fixed) the functions `z ↦ mixed c d (G (φ n)) z θ` are differentiable with
derivative `mixed (c+1) d (G (φ n)) z θ / z` (the defining recursion of `D_z`), which converges
locally uniformly to `F (c+1) d · θ / ·`; and the `θ`-slices are handled the same way using the
commutation `D_θ D_z^c = D_z^c D_θ` of the two operators on `C^∞`-functions (Lean name:
`mixed_partials_of_smoothOpen`). -/
theorem LimTower_dz {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hconv : ∀ (c d : ℕ), c + d ≤ 2 → TendstoLocallyUniformlyOn
      (fun n p => Work.Spaces.mixed c d (G (φ n)) p.1 p.2)
      (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0) :
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z) ∧
      (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) := by
  have hinv : ContinuousOn (fun p : ℝ × ℝ => p.1⁻¹) Work.FTS.EllipticEst.Q0 :=
    ContinuousOn.inv₀ continuousOn_fst
      (fun p hp => ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2))⁻¹)
      Work.FTS.EllipticEst.Q0 :=
    ContinuousOn.inv₀
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      (fun p hp => by
        obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        exact ne_of_gt (Work.FTS.StrongEps.LocUnif.sin_two_pos_Q0 ⟨h0, h1⟩))
  constructor
  · -- the radial half: `∂_z (F c d) = F (c+1) d / z`
    intro c d hcd z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hmem : ∀ x : ℝ, 0 < x → (x, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hx, hθ0, hθ1⟩
    have hcd2 : c + 1 + d ≤ 2 := by omega
    have hmul := Work.FTS.StrongEps.LocUnif.tendstoLocallyUniformlyOn_mul_continuousOn
      (U := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0
      (hconv (c + 1) d hcd2) hinv
    have hslice := Work.FTS.StrongEps.LocUnif.tendstoLocallyUniformlyOn_slice_fst
      (U := Work.FTS.EllipticEst.Q0) (θ := θ) (W := Set.Ioi (0 : ℝ)) hmem hmul
    have hf' : TendstoLocallyUniformlyOn
        (fun n x => x⁻¹ * Work.Spaces.mixed (c + 1) d (G (φ n)) x θ)
        (fun x => x⁻¹ * F (c + 1) d x θ) Filter.atTop (Set.Ioi (0 : ℝ)) := hslice
    have hf : ∀ᶠ n in Filter.atTop, ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun z' : ℝ => Work.Spaces.mixed c d (G (φ n)) z' θ)
          (x⁻¹ * Work.Spaces.mixed (c + 1) d (G (φ n)) x θ) x :=
      Filter.Eventually.of_forall fun n x hx => by
        have hd := ((hsm (φ n)).mixed c d).hasDerivAt_slice (θ := θ) ⟨hθ0, hθ1⟩ hx
        refine hd.congr_deriv ?_
        rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen c d
          (hsm (φ n))).1 x θ (hmem x hx), div_eq_mul_inv, mul_comm]
    have hfg : ∀ x ∈ Set.Ioi (0 : ℝ), Tendsto
        (fun n => Work.Spaces.mixed c d (G (φ n)) x θ) Filter.atTop (𝓝 (F c d x θ)) :=
      fun x hx => (hconv c d (by omega)).tendsto_at (hmem x hx)
    have key := hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioi hf' hf hfg hz
    exact key.congr_deriv (by rw [div_eq_mul_inv, mul_comm])
  · -- the angular half: `∂_θ (F c d) = F c (d+1) / sin 2θ`
    intro c d hcd z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hmem : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (π / 2) →
        (z, t) ∈ Work.FTS.EllipticEst.Q0 :=
      fun t ht => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, ht.1, ht.2⟩
    have hcd2 : c + (d + 1) ≤ 2 := by omega
    have hmul := Work.FTS.StrongEps.LocUnif.tendstoLocallyUniformlyOn_mul_continuousOn
      (U := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0
      (hconv c (d + 1) hcd2) hsin
    have hslice := Work.FTS.StrongEps.LocUnif.tendstoLocallyUniformlyOn_slice_snd
      (U := Work.FTS.EllipticEst.Q0) (z := z) (W := Set.Ioo (0 : ℝ) (π / 2)) hmem hmul
    have hf' : TendstoLocallyUniformlyOn
        (fun n t => (Real.sin (2 * t))⁻¹ * Work.Spaces.mixed c (d + 1) (G (φ n)) z t)
        (fun t => (Real.sin (2 * t))⁻¹ * F c (d + 1) z t)
        Filter.atTop (Set.Ioo (0 : ℝ) (π / 2)) := hslice
    have hf : ∀ᶠ n in Filter.atTop, ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2),
        HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed c d (G (φ n)) z θ')
          ((Real.sin (2 * t))⁻¹ * Work.Spaces.mixed c (d + 1) (G (φ n)) z t) t :=
      Filter.Eventually.of_forall fun n t ht => by
        have hd : HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed c d (G (φ n)) z θ')
            (Work.Spaces.pth (Work.Spaces.mixed c d (G (φ n))) z t) t :=
          (((hsm (φ n)).mixed c d).curry_θ hz).contDiffAt
            (isOpen_Ioo.mem_nhds ⟨ht.1, ht.2⟩) |>.differentiableAt (by simp) |>.hasDerivAt
        refine hd.congr_deriv ?_
        rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen c d
          (hsm (φ n))).2.1 z t (hmem t ht), div_eq_mul_inv, mul_comm]
    have hfg : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2), Tendsto
        (fun n => Work.Spaces.mixed c d (G (φ n)) z t) Filter.atTop (𝓝 (F c d z t)) :=
      fun t ht => (hconv c d (by omega)).tendsto_at (hmem t ht)
    have key := hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioo hf' hf hfg ⟨hθ0, hθ1⟩
    exact key.congr_deriv (by rw [div_eq_mul_inv, mul_comm])

end Work.FTS_EllLimOK
end
-- ===== merged: Submission.Work.FTS_EllLimOK.SmoothOpen_tower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

theorem SmoothOpen_tower {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun z' : ℝ => Work.Spaces.mixed c d G z' θ)
          (Work.Spaces.mixed (c + 1) d G z θ / z) z) ∧
      (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed c d G z θ')
          (Work.Spaces.mixed c (d + 1) G z θ / Real.sin (2 * θ)) θ) := by
  have hpp := fun (c d : ℕ) =>
    Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen c d hG
  constructor
  · -- the radial tower `∂_z (D_z^c D_θ^d G) = D_z^{c+1} D_θ^d G / z`
    intro c d _ z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hd := (hG.mixed c d).hasDerivAt_slice (θ := θ) ⟨hθ0, hθ1⟩ hz
    rwa [(hpp c d).1 z θ hzθ] at hd
  · -- the angular tower `∂_θ (D_z^c D_θ^d G) = D_z^c D_θ^{d+1} G / sin 2θ`
    intro c d _ z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hd : HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed c d G z θ')
        (Work.Spaces.pth (Work.Spaces.mixed c d G) z θ) θ :=
      (((hG.mixed c d).curry_θ hz).contDiffAt
          (isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩)).differentiableAt (by simp) |>.hasDerivAt
    rwa [(hpp c d).2.1 z θ hzθ] at hd

end Work.FTS_EllLimOK
end
-- ===== merged: Submission.Work.FTS_EllLimOK.tower_jet_identities =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK


end Work.FTS_EllLimOK
end
