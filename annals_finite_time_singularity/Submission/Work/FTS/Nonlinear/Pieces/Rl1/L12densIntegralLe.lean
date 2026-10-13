import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.H2.InvOneAddSq
import Submission.Work.Coercivity.L12dens_sq_slice
import Submission.Work.FTS.H2.CS1D
import Submission.Work.FTS.H2.L12densSlice
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.densNormCS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.Rl1

open MeasureTheory Set
open scoped Real

theorem L12densIntegralLe {f : ℝ → ℝ → ℝ}
    (hsl : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (f s θ) ^ 2) Work.Spaces.Iθ)
    (hint : MeasureTheory.IntegrableOn
      (fun s => Work.Spaces.w s * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)) (Set.Ioi (0 : ℝ))) :
    (∫ s in Set.Ioi (0 : ℝ), ‖Work.Construction.L12dens f s‖)
      ≤ Real.sqrt 6 * Real.sqrt
          (∫ s in Set.Ioi (0 : ℝ), Work.Spaces.w s * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)) := by
  classical
  -- Cauchy–Schwarz in `s`, with `A s = √3 √(w s · ∫_θ f s θ²)` and `B s = 1/(1+s)`:
  -- `‖L₁₂dens f s‖ ≤ √3 √(φ s)/s = A s · B s` a.e., `∫ A² = 3 ∫ w φ` and `∫ B² ≤ 2`.
  set A : ℝ → ℝ := fun s =>
    Real.sqrt 3 * Real.sqrt (Work.Spaces.w s * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)) with hA
  set B : ℝ → ℝ := fun s => 1 / (1 + s) with hB
  have hφnn : ∀ s : ℝ, 0 ≤ (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) := fun s =>
    MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ _ => by positivity)
  have hwnn : ∀ s : ℝ, 0 ≤ Work.Spaces.w s := fun s => by rw [Work.Spaces.w]; positivity
  have hGint : MeasureTheory.Integrable
      (fun s => Work.Spaces.w s * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hint
  have hA2 : ∀ s, A s ^ 2 = 3 * (Work.Spaces.w s * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)) := by
    intro s
    have hG : 0 ≤ Work.Spaces.w s * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) :=
      mul_nonneg (hwnn s) (hφnn s)
    show (Real.sqrt 3 * Real.sqrt (Work.Spaces.w s * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2))) ^ 2
        = 3 * (Work.Spaces.w s * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2))
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hG]
  have hAint : MeasureTheory.Integrable (fun s => A s ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hGint.const_mul 3).congr (Filter.Eventually.of_forall fun s => (hA2 s).symm)
  have hAaesm : MeasureTheory.AEStronglyMeasurable A
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hcont : Continuous (fun x : ℝ => Real.sqrt 3 * Real.sqrt x) :=
      continuous_const.mul Real.continuous_sqrt
    exact hcont.comp_aestronglyMeasurable hGint.aestronglyMeasurable
  have hAmem : MeasureTheory.MemLp A 2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAaesm).mpr hAint
  have hBaesm : MeasureTheory.AEStronglyMeasurable B
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (by fun_prop : Measurable (fun s : ℝ => 1 / (1 + s))).aestronglyMeasurable
  have hBint : MeasureTheory.Integrable (fun s => B s ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := Work.FTS.H2.InvOneAddSq.1
  have hBmem : MeasureTheory.MemLp B 2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hBaesm).mpr hBint
  have hA0 : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] A :=
    Filter.Eventually.of_forall fun s => by
      show 0 ≤ Real.sqrt 3 * Real.sqrt (Work.Spaces.w s * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2))
      exact mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg _)
  have hB0 : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] B := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    have hsp : (0 : ℝ) < s := hs
    show 0 ≤ 1 / (1 + s)
    exact div_nonneg zero_le_one (by linarith)
  -- the a.e. pointwise domination
  have hbd : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ‖Work.Construction.L12dens f s‖ ≤ A s * B s := by
    filter_upwards [hsl, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hsl_s hs
    have hsp : (0 : ℝ) < s := hs
    have hsq := Work.Coercivity.L12dens_sq_slice f Work.Coercivity.integral_Itheta_K hsp hsl_s
    have hx : |Work.Construction.L12dens f s|
        ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s :=
      Work.FTS.H2.abs_le_sqrt_three_mul_sqrt_div hsp (hφnn s) hsq
    rw [Real.norm_eq_abs]
    refine hx.trans (le_of_eq ?_)
    show Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
        = (Real.sqrt 3 * Real.sqrt (Work.Spaces.w s * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)))
            * (1 / (1 + s))
    have h1 : Work.Spaces.w s * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
        = ((1 + s) / s) ^ 2 * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) := by
      rw [Work.Spaces.w]; field_simp
    have hs0 : s ≠ 0 := ne_of_gt hsp
    have h1s : (1 : ℝ) + s ≠ 0 := by positivity
    rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    field_simp
  have hcs := Work.FTS.Nonlinear.Pieces.Rl1.densNormCS (h := f) hAmem hBmem hA0 hB0 hbd
  have hAint_eq : (∫ s in Set.Ioi (0 : ℝ), A s ^ 2)
      = 3 * (∫ s in Set.Ioi (0 : ℝ),
          Work.Spaces.w s * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => hA2 s)
  have hBint_le : (∫ s in Set.Ioi (0 : ℝ), B s ^ 2) ≤ 2 := Work.FTS.H2.InvOneAddSq.2
  refine hcs.trans ?_
  calc Real.sqrt (∫ s in Set.Ioi (0 : ℝ), A s ^ 2)
        * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), B s ^ 2)
      = (Real.sqrt 3 * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), Work.Spaces.w s
            * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)))
          * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), B s ^ 2) := by
        rw [hAint_eq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    _ ≤ (Real.sqrt 3 * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), Work.Spaces.w s
            * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2))) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hBint_le) (by positivity)
    _ = Real.sqrt 6 * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), Work.Spaces.w s
            * (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)) := by
        have h32 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
          rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
        rw [← h32]; ring

end Work.FTS.Nonlinear.Pieces.Rl1
