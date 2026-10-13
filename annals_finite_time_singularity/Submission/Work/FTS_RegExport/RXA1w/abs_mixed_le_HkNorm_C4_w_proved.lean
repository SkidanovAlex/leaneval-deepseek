import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.C4.HkSqSwap_C4
import Submission.Work.FTS_RegExport.RXA1w.AngularHardy
import Submission.Work.FTS_RegExport.RXA1w.SliceAgmon

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# RX-A1w — the weighted interior `L^∞`–`ℋ⁴` trade-off at the finite order `C⁴`

For `0 < β ≤ 1` there is `C = C(β) ≥ 0` such that every `C⁴` datum `f` on the open quadrant
which is honestly in `ℋ⁴` and satisfies the boundary traces `BdryTraces β 4` obeys

`|D_z^bD_θ^a f (z,θ)| ≤ C · z^{3/2}/(1+z)² · |f|_{ℋ⁴}`   for `a + b ≤ 2`, `z > 0`, `0 < θ < π/2`.

The chain (see the sibling modules `AgmonZ`, `Helpers`, `AngularHardy`, `SliceAgmon`):

1. angular Hardy at the fixed radial variable `z` (`angular_hardy_C4`);
2. the weighted radial Agmon inequality in `z` (`agmonZ_weight`) on the resulting angular
   slice, with the two Agmon energy slots dominated by the `ℋ⁴`-integrand
   (`mixed_slice_pointwise_le`);
3. Tonelli (`HkSqSwap_C4`) sums the resulting a.e. bound over the angle.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1w

theorem abs_mixed_le_HkNorm_C4_w_proved {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Work.FTS.Galerkin.Fn,
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem β 4 f → Work.FTS.Nonlin.BdryTraces β 4 f →
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a f z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * Work.Spaces.HkNorm β 4 f := by
  have hγ1 : 0 < Work.Spaces.gam β - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  refine ⟨Real.sqrt (500 / (Work.Spaces.gam β - 1)), Real.sqrt_nonneg _, ?_⟩
  intro f h4 hmem htr b a hab z θ hz hθ0 hθ1
  have hHT := angular_hardy_C4 hβ hβ1 h4 hmem htr b a hab hz θ ⟨hθ0, hθ1⟩
  obtain ⟨hswap, hTint, -⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 h4 hmem
  have hrhs : MeasureTheory.Integrable
      (fun σ => 5 * (z ^ 3 / (1 + z) ^ 4)
        * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ))
      (volume.restrict Work.Spaces.Iθ) := hTint.const_mul _
  have hmono := integral_mono_of_nonneg
    (ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ =>
      mul_nonneg (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hσ) _) (sq_nonneg _))
    hrhs (mixed_slice_pointwise_le hβ h4 hmem htr b a hab hz)
  have hIntegral : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2)
      ≤ 5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f := by
    calc (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
          * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2)
        ≤ ∫ σ in Work.Spaces.Iθ, 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := hmono
      _ = 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
                Work.Spaces.HkIntegrand β 4 f s σ) := by
          rw [MeasureTheory.integral_const_mul]
      _ = 5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f := by rw [hswap]
  have hK : 0 ≤ 100 / (Work.Spaces.gam β - 1) := div_nonneg (by norm_num) hγ1.le
  have hmain : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ (500 / (Work.Spaces.gam β - 1)) * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f := by
    have h1 : (100 / (Work.Spaces.gam β - 1))
          * (5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f)
        = (500 / (Work.Spaces.gam β - 1)) * (z ^ 3 / (1 + z) ^ 4)
          * Work.Spaces.HkSq β 4 f := by ring
    rw [← h1]
    exact le_trans hHT (mul_le_mul_of_nonneg_left hIntegral hK)
  have hC0 : 0 ≤ 500 / (Work.Spaces.gam β - 1) := div_nonneg (by norm_num) hγ1.le
  have hA0 : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 :=
    div_nonneg (Real.rpow_nonneg hz.le _) (by positivity)
  have hA0sq : (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) ^ 2 = z ^ 3 / (1 + z) ^ 4 := by
    rw [div_pow]
    congr 1
    · rw [← Real.rpow_natCast (z ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hz.le]
      norm_num
    · ring
  have hsq : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ (Real.sqrt (500 / (Work.Spaces.gam β - 1)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
          * Real.sqrt (Work.Spaces.HkSq β 4 f)) ^ 2 := by
    calc (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ (500 / (Work.Spaces.gam β - 1)) * (z ^ 3 / (1 + z) ^ 4)
            * Work.Spaces.HkSq β 4 f := hmain
      _ = (500 / (Work.Spaces.gam β - 1))
            * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) ^ 2 * Work.Spaces.HkSq β 4 f := by
          rw [hA0sq]
      _ = (Real.sqrt (500 / (Work.Spaces.gam β - 1)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Real.sqrt (Work.Spaces.HkSq β 4 f)) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hC0, Real.sq_sqrt (Work.Spaces.HkSq_nonneg β 4 f)]
          <;> try ring
  have hfin : |Work.Spaces.mixed b a f z θ|
      ≤ Real.sqrt (500 / (Work.Spaces.gam β - 1)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
          * Work.Spaces.HkNorm β 4 f := by
    have hnn : 0 ≤ Real.sqrt (500 / (Work.Spaces.gam β - 1))
        * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * Real.sqrt (Work.Spaces.HkSq β 4 f) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hA0) (Real.sqrt_nonneg _)
    calc |Work.Spaces.mixed b a f z θ|
        = Real.sqrt ((Work.Spaces.mixed b a f z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((Real.sqrt (500 / (Work.Spaces.gam β - 1))
            * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Real.sqrt (Work.Spaces.HkSq β 4 f)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (500 / (Work.Spaces.gam β - 1)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Real.sqrt (Work.Spaces.HkSq β 4 f) := Real.sqrt_sq hnn
      _ = Real.sqrt (500 / (Work.Spaces.gam β - 1)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Work.Spaces.HkNorm β 4 f := rfl
  exact hfin

end Work.FTS_RegExport.RXA1w
