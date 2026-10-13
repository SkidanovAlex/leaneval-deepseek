import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! The remaining one-dimensional estimate after the angular integration by parts:
`|(q-1)·∫_z (L₁₂f·w²)·∫_θ cos(2θ)σ^{-q}h²| ≤ C₄|f|_{ℋ⁴}·|f|²_{ℋ⁶}`. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option maxHeartbeats 1600000

theorem end_bound_fts {α : ℝ} {f : ℝ → ℝ → ℝ} {a b : ℕ} {q C₄ : ℝ} (hα : 0 < α)
    (hmem6 : Work.Spaces.HkMem α 6 f) (hab : a + b ≤ 6)
    (hqabs : |q - 1| ≤ 1)
    (hC : ∀ z ∈ Work.Spaces.Iz, |Work.Construction.L12 f z| ≤ C₄ * Work.Spaces.HkNorm α 4 f)
    (hleaf : Work.FTS.TransportS.IsLeafW α a
      (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
    (hout : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iz)
    (hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ) :
    |(q - 1) * (∫ z in Work.Spaces.Iz,
        (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2))|
      ≤ C₄ * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f := by
  -- nonnegativity of the `σ^{-q}`-weighted square, a.e. in `θ`
  have hsnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ Real.sin (2 * θ) :=
    (Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ).mono fun θ hθ =>
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
  -- `C₄·|f|_{ℋ⁴} ≥ 0` follows from `hC` (at `z = 1`); no separate sign hypothesis is needed
  have hX0 : 0 ≤ C₄ * Work.Spaces.HkNorm α 4 f :=
    le_trans (abs_nonneg (Work.Construction.L12 f 1))
      (hC 1 (Set.mem_Ici.mpr (by norm_num)))
  -- the `θ`-majorant of the inner integral
  have hinner_le : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      |∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2|
        ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    filter_upwards [hslice] with z hz
    refine (MeasureTheory.abs_integral_le_integral_abs).trans ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) hz ?_
    filter_upwards [hsnn] with θ hθ
    have hσ : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := Real.rpow_nonneg hθ _
    have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |(Real.sin (2 * θ)) ^ (-q)| = (Real.sin (2 * θ)) ^ (-q) := abs_of_nonneg hσ
    have h3 : |(Work.Spaces.mixed b a f z θ) ^ 2|
        = (Work.Spaces.mixed b a f z θ) ^ 2 := abs_of_nonneg (sq_nonneg _)
    rw [abs_mul, abs_mul, h2, h3]
    calc (|Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-q))
          * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ (1 * (Real.sin (2 * θ)) ^ (-q))
          * (Work.Spaces.mixed b a f z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcos hσ) (sq_nonneg _)
      _ = (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed b a f z θ) ^ 2 := by ring
  -- the pointwise bound by the `L₁₂`-majorant
  have hmaj_le : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      |(Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2)|
        ≤ C₄ * Work.Spaces.HkNorm α 4 f * ((Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
    filter_upwards [hinner_le, MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hzin hz
    have hDnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [hsnn] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg hθ _) (sq_nonneg _)
    have hW2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    calc |(Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2)|
        = |Work.Construction.L12 f z| * (Work.Spaces.w z) ^ 2
          * |∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hW2]
      _ ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
          refine mul_le_mul (mul_le_mul (hC z hz) le_rfl (sq_nonneg _) hX0) hzin
            (abs_nonneg _) (mul_nonneg hX0 hW2)
      _ = C₄ * Work.Spaces.HkNorm α 4 f * ((Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by ring
  -- the majorant is integrable
  have hmaj : MeasureTheory.IntegrableOn (fun z => C₄ * Work.Spaces.HkNorm α 4 f
      * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2)) Work.Spaces.Iz :=
    hout.const_mul _
  -- the final chain
  have htarget : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          * (Work.Spaces.mixed b a f z θ) ^ 2
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  have hleafslab := Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6 hα hmem6 a b
    (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) hab hleaf
  calc |(q - 1) * (∫ z in Work.Spaces.Iz,
        (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2))|
      = |q - 1| * |∫ z in Work.Spaces.Iz,
          (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| := by rw [abs_mul]
    _ ≤ 1 * |∫ z in Work.Spaces.Iz,
          (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| :=
        mul_le_mul_of_nonneg_right hqabs (abs_nonneg _)
    _ = |∫ z in Work.Spaces.Iz,
          (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| := one_mul _
    _ ≤ ∫ z in Work.Spaces.Iz,
        |(Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, C₄ * Work.Spaces.HkNorm α 4 f * ((Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => abs_nonneg _) hmaj hmaj_le
    _ = C₄ * Work.Spaces.HkNorm α 4 f * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
        rw [MeasureTheory.integral_const_mul]
    _ = C₄ * Work.Spaces.HkNorm α 4 f * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by rw [htarget]
    _ ≤ C₄ * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f :=
        mul_le_mul_of_nonneg_left hleafslab hX0

end Work.FTS.StrongPersist.H6Pair6Aux
