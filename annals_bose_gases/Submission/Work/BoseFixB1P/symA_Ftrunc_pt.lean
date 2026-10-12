import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.ProfHatDecay
import Submission.Work.OneBodyKin.famSym_Ftrunc_tendsto
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1P.symA_Ftrunc_pt` — pointwise convergence of the truncated unprojected symbol

The unprojected symbol of the moving-box family is

    `symA ℓ F q = (2π)⁻³ ∫_p F ‖q + ℓ⁻¹ • p‖ · profHat(p)² dp`

(`Work.OneBodyKin.Defs`).  For the truncated FS cut-off `Ftrunc c n ↑ fsKinCoeff c` the truncated
symbols converge, *pointwise in `q`*, to the symbol at the full FS cut-off:

    `symA ℓ (Ftrunc c n) q → symA ℓ (fsKinCoeff c) q`.

## Proof

The `symA` integrand `Ftrunc c n ‖q + ℓ⁻¹ • p‖ · profHat(p)²` has, uniformly in `n`, the
integrable dominating function

    `((1+|c|)² ((1+‖q‖) max 1 ℓ⁻¹)² C²)·(1+‖p‖)⁻¹⁰`,

where `C` is the constant of the profile decay `ProfHatDecay`.  Indeed the symbol factor is
estimated by `Ftrunc_le_fsKinCoeff` + `fsKinCoeff_le_mul_sq`, the shift by
`onePlusNorm_add_le`/`onePlusNorm_smul_le` (with `ℓ⁻¹ > 0`), and the squared profile by
`|profHat p| ≤ C/(1+‖p‖)⁶`; the resulting power is `(1+‖p‖)^{2-12} = (1+‖p‖)^{-10}`, integrable
on `ℝ³` (`integrable_inv_onePlusNorm_pow`, `10 > 3`).  Lebesgue dominated convergence
(`MeasureTheory.tendsto_integral_of_dominated_convergence`) with the pointwise limit
`Ftrunc c n r → fsKinCoeff c r` (`Ftrunc_tendsto`) finishes.

This is the public, `symA`-only form of the *private* lemma `tendsto_symA_Ftrunc` of
`Submission/Work/OneBodyKin/famSym_Ftrunc_tendsto.lean`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1P

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **Domination of the `symA` integrand.**  With `hd` the profile decay and `ℓ > 0`, the
integrand of `symA ℓ (Ftrunc c n) q` is bounded, *uniformly in `n`*, by the integrable weight
`((1+|c|)²((1+‖q‖) max 1 ℓ⁻¹)²C²)·(1+‖p‖)^{-10}`. -/
private lemma symA_integrand_bound_pt {ℓ c C : ℝ} (hℓ : 0 < ℓ) (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |Work.OneBodyKin.profHat p| ≤ C / (1 + ‖p‖) ^ 6) (q : ℝ³) :
    ∀ (n : ℕ) (p : ℝ³),
      ‖Work.OneBodyKin.Ftrunc c n ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2‖
        ≤ ((1 + |c|) ^ 2 * ((1 + ‖q‖) * max 1 ℓ⁻¹) ^ 2 * C ^ 2) * ((1 + ‖p‖) ^ 10)⁻¹ := by
  intro n p
  have hx : (0 : ℝ) < 1 + ‖p‖ := by positivity
  have hQ : (0 : ℝ) ≤ 1 + ‖q‖ := by positivity
  have hshift : 1 + ‖q + ℓ⁻¹ • p‖ ≤ ((1 + ‖q‖) * max 1 ℓ⁻¹) * (1 + ‖p‖) := by
    have h1 := Work.OneBodyKin.onePlusNorm_add_le q (ℓ⁻¹ • p)
    have h2 := Work.OneBodyKin.onePlusNorm_smul_le ℓ⁻¹ p
    have h3 : |ℓ⁻¹| = ℓ⁻¹ := abs_of_pos (inv_pos.mpr hℓ)
    calc 1 + ‖q + ℓ⁻¹ • p‖ ≤ (1 + ‖q‖) * (1 + ‖ℓ⁻¹ • p‖) := h1
      _ ≤ (1 + ‖q‖) * (max 1 |ℓ⁻¹| * (1 + ‖p‖)) := mul_le_mul_of_nonneg_left h2 hQ
      _ = ((1 + ‖q‖) * max 1 ℓ⁻¹) * (1 + ‖p‖) := by rw [h3]; ring
  have hprof : Work.OneBodyKin.profHat p ^ 2 ≤ (C / (1 + ‖p‖) ^ 6) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hd p) 2
  have hf0 : 0 ≤ Work.OneBodyKin.Ftrunc c n ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2 :=
    mul_nonneg (Work.OneBodyKin.Ftrunc_nonneg c n _) (sq_nonneg _)
  have hC2 : (1 + ‖p‖) ^ 2 * (C / (1 + ‖p‖) ^ 6) ^ 2 = C ^ 2 * ((1 + ‖p‖) ^ 10)⁻¹ := by
    field_simp
  rw [Real.norm_of_nonneg hf0]
  calc Work.OneBodyKin.Ftrunc c n ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2
      ≤ fsKinCoeff c ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2 :=
        mul_le_mul_of_nonneg_right (Work.OneBodyKin.Ftrunc_le_fsKinCoeff c n _) (sq_nonneg _)
    _ ≤ ((1 + |c|) ^ 2 * (1 + ‖q + ℓ⁻¹ • p‖) ^ 2) * Work.OneBodyKin.profHat p ^ 2 :=
        mul_le_mul_of_nonneg_right
          (Work.OneBodyKin.fsKinCoeff_le_mul_sq c _ (norm_nonneg _)) (sq_nonneg _)
    _ ≤ ((1 + |c|) ^ 2 * (((1 + ‖q‖) * max 1 ℓ⁻¹) * (1 + ‖p‖)) ^ 2)
          * (C / (1 + ‖p‖) ^ 6) ^ 2 := by
        refine mul_le_mul ?_ hprof (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hshift 2) (sq_nonneg _)
    _ = ((1 + |c|) ^ 2 * ((1 + ‖q‖) * max 1 ℓ⁻¹) ^ 2 * C ^ 2) * ((1 + ‖p‖) ^ 10)⁻¹ := by
        field_simp

/-- **`symA` converges along the truncations** (pointwise in `q`). -/
theorem symA_Ftrunc_pt {ℓ c : ℝ} (hℓ : 0 < ℓ) (q : EuclideanSpace ℝ (Fin 3)) :
    Filter.Tendsto (fun n : ℕ => Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q)
      Filter.atTop (nhds (Work.OneBodyKin.symA ℓ (Submission.BoseGases.fsKinCoeff c) q)) := by
  obtain ⟨C, hC, hd⟩ := Work.OneBodyKin.ProfHatDecay
  have hbound := symA_integrand_bound_pt (c := c) hℓ hC hd q
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ³ => ((1 + |c|) ^ 2 * ((1 + ‖q‖) * max 1 ℓ⁻¹) ^ 2 * C ^ 2)
        * ((1 + ‖p‖) ^ 10)⁻¹) :=
    (Work.OneBodyKin.integrable_inv_onePlusNorm_pow (k := 10) (by norm_num)).const_mul _
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun p : ℝ³ =>
        Work.OneBodyKin.Ftrunc c n ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2) volume := by
    intro n
    have hcont : Continuous (fun p : ℝ³ => q + ℓ⁻¹ • p) :=
      continuous_const.add (continuous_id.const_smul ℓ⁻¹)
    have h1 : Measurable (fun p : ℝ³ => Work.OneBodyKin.Ftrunc c n ‖q + ℓ⁻¹ • p‖) :=
      (Work.OneBodyKin.measurable_Ftrunc c n).comp (continuous_norm.comp hcont).measurable
    have h2 : Measurable (fun p : ℝ³ => Work.OneBodyKin.profHat p ^ 2) :=
      (Work.OneBodyKin.continuous_profHat.pow 2).measurable
    exact (h1.mul h2).aestronglyMeasurable
  have hlim : ∀ᵐ p ∂(volume : Measure ℝ³),
      Filter.Tendsto
        (fun n : ℕ =>
          Work.OneBodyKin.Ftrunc c n ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2)
        Filter.atTop
        (nhds (fsKinCoeff c ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2)) :=
    Filter.Eventually.of_forall fun p =>
      (Work.OneBodyKin.Ftrunc_tendsto c ‖q + ℓ⁻¹ • p‖).mul_const
        (Work.OneBodyKin.profHat p ^ 2)
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := fun (n : ℕ) (p : ℝ³) =>
        Work.OneBodyKin.Ftrunc c n ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2)
      (f := fun p : ℝ³ => fsKinCoeff c ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2)
      (fun p : ℝ³ =>
        ((1 + |c|) ^ 2 * ((1 + ‖q‖) * max 1 ℓ⁻¹) ^ 2 * C ^ 2) * ((1 + ‖p‖) ^ 10)⁻¹)
      hmeas hInt (fun n => Filter.Eventually.of_forall (hbound n)) hlim
  have hthis := hmain.const_mul (((2 * Real.pi) ^ 3)⁻¹)
  simpa only [Work.OneBodyKin.symA] using hthis

end Work.BoseFixB1P
