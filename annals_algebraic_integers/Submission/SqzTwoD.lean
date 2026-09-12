import Submission.SqueezeCore
import Submission.SqzKernel
import Mathlib.Tactic

/-! # Child task: 2D log-kernel integrability and value for μ⊗μ.

Prove the three lemmas below (mirrors of
`Submission.SqueezeCore.integrable_prod_log_sub`,
`Submission.SqueezeCore.integral_prod_log_sub_energy`,
`Submission.SqueezeCore.integrable_abs_log_sub_2d`).  You may add helper
lemmas **in this file** in namespace `Submission.SqzTwoD`.

Available infrastructure (imported through `Submission.SqueezeCore`):

* `Submission.SqueezeCore.muSerre` — Serre measure (probability measure,
  atom-free, supported on `[aSerre,bSerre]`);
* 1D facts: `Submission.SqueezeCore.integrable_log_sub`,
  `Submission.SqueezeCore.integrable_abs_log_sub`,
  `Submission.SqueezeCore.integral_log_sub_eq_neg_potential`,
  `Submission.SqueezeCore.integral_log_pair_energy`,
  `Submission.PotentialContinuity.logAbs_integrable` (all against `muSerre`);
* `uniform_abs_log_kernel_bound` (in `Submission.SqueezeCore`, whose proof is a
  sibling task; **you may assume it as an axiom-free fact by importing
  `Submission.SqueezeCore`** — if it is still a placeholder when you compile, that
  is fine: its statement is usable).  The sibling module
  `Submission.SqzKernel` provides an axiom-free proof of the same statement in
  its own namespace, which we import and use here;
* energy: `Submission.EnergyHalf.energy`, `logPotential`,
  `Submission.SqueezeCore.integral_potential_eq_energy`.

## What to prove

1. `integrable_abs_log_sub_2d : Integrable (fun p : ℝ × ℝ => |Real.log (|p.1 - p.2|)|) (muSerre.prod muSerre)`
2. `integrable_prod_log_sub : Integrable (fun p : ℝ × ℝ => Real.log (|p.1 - p.2|)) (muSerre.prod muSerre)`
3. `integral_prod_log_sub_energy : (∫ p : ℝ × ℝ, Real.log (|p.1 - p.2|) ∂(muSerre.prod muSerre)) = -energy`

Route: (1) via Tonelli in the form of `MeasureTheory.lintegral_prod` together
with the uniform bound `∫_y |log|x−y|| dμ ≤ C` for `x ∈ [a,b]` (from
`Submission.SqzKernel.uniform_abs_log_kernel_bound`), and the fact that μ is
concentrated on `[a,b]`; (2) follows from (1) since
`log|u−v| ≤ |log|u−v||` and ≥ `-|...|` with `Integrable.mono'`-style
arguments; (3) via Fubini (`MeasureTheory.integral_prod`) applied to
`MeasureTheory.integral_log_pair_energy` and
`MeasureTheory.integral_log_sub_eq_neg_potential`.
-/

noncomputable section

open MeasureTheory Polynomial
open scoped Real BigOperators ENNReal Topology

namespace Submission.SqzTwoD

open Submission.SqueezeCore
open Submission.Contracts
open Submission.SerreExample
open Submission.PotentialDefs
open Submission.EnergyHalf

/-! ## 2D measurability of the log kernel -/

/-- the map `(u,v) ↦ |log|u−v||` is jointly measurable. -/
lemma abs_log_sub_measurable_2d :
    Measurable (fun p : ℝ × ℝ => |Real.log (|p.1 - p.2|)|) := by
  have h1 : Continuous (fun p : ℝ × ℝ => |p.1 - p.2|) := by fun_prop
  exact (Real.measurable_log.comp h1.measurable).abs

/-- the map `(u,v) ↦ log|u−v|` is jointly measurable. -/
lemma log_sub_measurable_2d :
    Measurable (fun p : ℝ × ℝ => Real.log (|p.1 - p.2|)) := by
  have h1 : Continuous (fun p : ℝ × ℝ => |p.1 - p.2|) := by fun_prop
  exact Real.measurable_log.comp h1.measurable

/-! ## (1) integrability of the absolute kernel on μ⊗μ -/

lemma integrable_abs_log_sub_2d :
    Integrable (fun p : ℝ × ℝ => |Real.log (|p.1 - p.2|)|) (muSerre.prod muSerre) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => |Real.log (|p.1 - p.2|)|) := abs_log_sub_measurable_2d
  have hnn : 0 ≤ᵐ[(muSerre.prod muSerre)] (fun p : ℝ × ℝ => |Real.log (|p.1 - p.2|)|) :=
    Filter.Eventually.of_forall (fun p => abs_nonneg _)
  -- finite double lintegral (Tonelli) via the uniform 1D bound
  have hFin : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|Real.log (|p.1 - p.2|)|)
      ∂(muSerre.prod muSerre)) < ∞ := by
    have hton : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|Real.log (|p.1 - p.2|)|)
          ∂(muSerre.prod muSerre)) =
        (∫⁻ x : ℝ, (∫⁻ y : ℝ, ENNReal.ofReal (|Real.log (|x - y|)|) ∂muSerre) ∂muSerre) := by
      exact MeasureTheory.lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal (|Real.log (|p.1 - p.2|)|))
        hmeas.ennreal_ofReal.aemeasurable
    rw [hton]
    rcases Submission.SqzKernel.uniform_abs_log_kernel_bound with ⟨C, hC0, hC⟩
    have hI_le : ∀ᵐ x ∂muSerre,
        (∫⁻ y : ℝ, ENNReal.ofReal (|Real.log (|x - y|)|) ∂muSerre) ≤ ENNReal.ofReal C := by
      filter_upwards [ae_mem_Icc_muSerre] with x hx
      have hxint : Integrable (fun y : ℝ => |Real.log (|x - y|)|) muSerre :=
        integrable_abs_log_sub x
      calc
        (∫⁻ y : ℝ, ENNReal.ofReal (|Real.log (|x - y|)|) ∂muSerre)
            = ENNReal.ofReal (∫ y : ℝ, |Real.log (|x - y|)| ∂muSerre) := by
              exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hxint
                (Filter.Eventually.of_forall (fun y => abs_nonneg _))).symm
        _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hC x hx)
    have hconst : (∫⁻ x : ℝ, ENNReal.ofReal C ∂muSerre) = ENNReal.ofReal C := by
      rw [MeasureTheory.lintegral_const]
      simp
    exact lt_of_le_of_lt (MeasureTheory.lintegral_mono_ae hI_le) (by
      rw [hconst]
      exact ENNReal.ofReal_lt_top)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn]
  exact hFin

/-! ## (2) integrability of the (signed) kernel -/

lemma integrable_prod_log_sub :
    Integrable (fun p : ℝ × ℝ => Real.log (|p.1 - p.2|)) (muSerre.prod muSerre) := by
  refine MeasureTheory.Integrable.mono' integrable_abs_log_sub_2d ?_ ?_
  · exact log_sub_measurable_2d.aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun p => ?_)
    rw [Real.norm_eq_abs]

/-! ## (3) the double integral is −energy (Fubini) -/

lemma integral_prod_log_sub_energy :
    (∫ p : ℝ × ℝ, Real.log (|p.1 - p.2|) ∂(muSerre.prod muSerre)) = -energy := by
  have hFub : (∫ x : ℝ, (∫ y : ℝ, Real.log (|x - y|) ∂muSerre) ∂muSerre) =
      (∫ p : ℝ × ℝ, Real.log (|p.1 - p.2|) ∂(muSerre.prod muSerre)) := by
    exact MeasureTheory.integral_integral (f := fun x y : ℝ => Real.log (|x - y|))
      integrable_prod_log_sub
  rw [← hFub]
  exact integral_log_pair_energy

end Submission.SqzTwoD
