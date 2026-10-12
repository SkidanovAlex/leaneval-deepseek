import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.cnPlus_eq_slotSum
import Submission.Work.BSKinetic.familyForm_zero_eq
import Submission.Work.BSKinetic.locKinEnWordBox_of_familyBound
import Submission.Work.BSKinetic.tBwordBInd_slotSwap_and_integrable
import Submission.Work.OneBodyKin.Phi_far_nonneg
import Submission.Work.OneBodyKin.SecondOrder.boxHat_one_sub_sq_le
import Submission.Work.OneBodyKin.SecondOrder.symA_zero_small
import Submission.Work.OneBodyKin.SecondOrder.symD_diff_bound_uniform
import Submission.Work.OneBodyKin.SecondOrder.symD_fsKinCoeff_small
import Submission.Work.OneBodyKin.SymBound_iff_SymBoundOne
import Submission.Work.OneBodyKin.SymbolIntegral_fsKinCoeff
import Submission.Work.OneBodyKin.dSpace_eq_fourier
import Submission.Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq
import Submission.Work.OneBodyKin.symA_fsKinCoeff_far_le
import Submission.Work.OneBodyKin.symD_second_order
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.symA_Ftrunc_pt` — the unprojected symbol converges along the radial truncations

The FS cut-off coefficient `fsKinCoeff c = [· − c]₊²` is the *pointwise increasing* limit of the
radial truncations `Ftrunc c n r = if r ≤ n then [r − c]₊² else 0` (`OneBodyKin/TruncDefs.lean`).
The unprojected moving-box symbol is

    `symA ℓ F q = (2π)⁻³ ∫_p F ‖q + ℓ⁻¹ • p‖ · profHat(p)² dp`     (`OneBodyKin/Defs.lean`),

so the present lemma is the statement that the family of symbols is *continuous along the
truncation*: `symA ℓ (Ftrunc c n) q → symA ℓ (fsKinCoeff c) q` for every momentum `q`.

## The argument

Lebesgue dominated convergence in `p` (a Bochner integral, hence requiring honest integrability).
All three factors of the integrand are nonnegative, so the absolute value can be dropped, and:

* the truncation factor is dominated uniformly in `n` by the quadratic growth
  `Ftrunc c n r ≤ [r − c]₊² ≤ (1+|c|)²(1+r)²` (`fsKinCoeff_le_mul_sq`);
* the shift `q + ℓ⁻¹ • p` is absorbed with `1 + ‖a + b‖ ≤ (1+‖a‖)(1+‖b‖)` and
  `1 + ‖t • p‖ ≤ max 1 |t| (1 + ‖p‖)`, giving
  `1 + ‖q + ℓ⁻¹•p‖ ≤ ((1+‖q‖) max 1 ℓ⁻¹)(1 + ‖p‖)`;
* the profile is estimated by the polynomial decay `|profHat p| ≤ C (1 + ‖p‖)^{-6}`
  (`Work.OneBodyKin.ProfHatDecay`, the only *external* input; the present statement carries no
  decay hypothesis, so it is instantiated here).

Altogether the integrand is bounded by the integrable weight
`(1+|c|)²((1+‖q‖) max 1 ℓ⁻¹)²C² · (1 + ‖p‖)^{-10}` (the exponent `-10 = 2·(-6) + 2` is what makes
the `p`-integral finite in dimension three, `integrable_inv_onePlusNorm_pow` with `k = 10 > 3`),
and the pointwise limit of the integrands is `fsKinCoeff c ‖q+ℓ⁻¹•p‖ profHat(p)²`
(`Ftrunc_tendsto`).

The same computation for `famSym` (all three of `symA`, `symD`, `symC`) is in
`Work.OneBodyKin.famSym_Ftrunc_tendsto`; here only the `symA` half is needed and it is re-derived
so that the statement carries no decay hypothesis.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. Domination of the `symA` integrand -/

/-- **Domination of the `symA` integrand.**  With `hd` the profile decay and `ℓ > 0`, the
integrand of `symA ℓ (Ftrunc c n) q` is bounded, *uniformly in `n`*, by the integrable weight
`((1+|c|)²((1+‖q‖) max 1 ℓ⁻¹)²C²)·(1+‖p‖)^{-10}`. -/
private lemma symA_integrand_bound {ℓ c C : ℝ} (hℓ : 0 < ℓ) (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |Work.OneBodyKin.profHat p| ≤ C / (1 + ‖p‖) ^ 6) (q : ℝ³) :
    ∀ (n : ℕ) (p : ℝ³),
      ‖Work.OneBodyKin.Ftrunc c n ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2‖
        ≤ ((1 + |c|) ^ 2 * ((1 + ‖q‖) * max 1 ℓ⁻¹) ^ 2 * C ^ 2)
            * ((1 + ‖p‖) ^ 10)⁻¹ := by
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

/-! ## 2. Convergence of `symA` along the truncations -/

/-- **`symA` converges along the truncations** (conditional form, with the profile decay as an
explicit hypothesis). -/
private lemma tendsto_symA_Ftrunc {ℓ c C : ℝ} (hℓ : 0 < ℓ) (hC : 0 ≤ C)
    (hd : ∀ p : ℝ³, |Work.OneBodyKin.profHat p| ≤ C / (1 + ‖p‖) ^ 6) (q : ℝ³) :
    Filter.Tendsto (fun n : ℕ => Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q)
      Filter.atTop (nhds (Work.OneBodyKin.symA ℓ (fsKinCoeff c) q)) := by
  have hbound := symA_integrand_bound (c := c) hℓ hC hd q
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
      Filter.Tendsto (fun n : ℕ =>
          Work.OneBodyKin.Ftrunc c n ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2)
        Filter.atTop
        (nhds (fsKinCoeff c ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2)) :=
    Filter.Eventually.of_forall fun p =>
      (Work.OneBodyKin.Ftrunc_tendsto c ‖q + ℓ⁻¹ • p‖).mul_const (Work.OneBodyKin.profHat p ^ 2)
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := fun (n : ℕ) (p : ℝ³) =>
        Work.OneBodyKin.Ftrunc c n ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2)
      (f := fun p : ℝ³ => fsKinCoeff c ‖q + ℓ⁻¹ • p‖ * Work.OneBodyKin.profHat p ^ 2)
      (fun p : ℝ³ =>
        ((1 + |c|) ^ 2 * ((1 + ‖q‖) * max 1 ℓ⁻¹) ^ 2 * C ^ 2) * ((1 + ‖p‖) ^ 10)⁻¹)
      hmeas hInt (fun n => Filter.Eventually.of_forall (hbound n)) hlim
  have hthis := hmain.const_mul (((2 * Real.pi) ^ 3)⁻¹)
  simpa only [Work.OneBodyKin.symA] using hthis

/-- **The unprojected symbol at the truncated cut-off converges, for every fixed momentum `q`,
to the symbol at the full FS cut-off.**  The decay hypothesis is discharged by
`Work.OneBodyKin.ProfHatDecay`, so this is the statement requested by the small-box programme. -/
theorem symA_Ftrunc_pt {ℓ c : ℝ} (hℓ : 0 < ℓ) (q : EuclideanSpace ℝ (Fin 3)) :
    Filter.Tendsto (fun n : ℕ => Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q)
      Filter.atTop (nhds (Work.OneBodyKin.symA ℓ (Submission.BoseGases.fsKinCoeff c) q)) := by
  obtain ⟨C, hC0, hd⟩ := Work.OneBodyKin.ProfHatDecay
  exact tendsto_symA_Ftrunc (c := c) hℓ hC0 hd q

end Work.BoseFixB1
