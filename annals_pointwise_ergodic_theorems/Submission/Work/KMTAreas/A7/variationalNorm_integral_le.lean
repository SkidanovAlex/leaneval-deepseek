import Mathlib
import Submission.VarNorm

/-!
# Minkowski's inequality for the variational norm

The `r`-variational norm `PointwiseErgodicTheorems.variationalNorm r a` of a sequence
`a : ℕ → ℂ` is the sum of two suprema (`Submission.PointwiseErgodicTheorems.variationalNorm_eq_add`):

* the supremum part `⨆ n, ‖a n‖ₑ`;
* the variation part `varPart r a`, the supremum, over all monotone index maps `N` and all `J`,
  of the `ℓ^r` norm `‖(a (N (i + 1)) - a (N i))_i‖` of the successive differences of `a` along `N`.

The lemma below says that this norm commutes with the Bochner integral in the weak (Minkowski)
form: for a `σ`-finite measure `ν` on `ℝ` and a family `g : ℝ → ℕ → ℂ` whose `n`-th member is
`ν`-integrable for every `n`, the variational norm of the family of integrals
`n ↦ ∫ g t n ∂ν` is at most the integral of the variational norms of the integrands:

  `variationalNorm r (fun n => ∫ g t n ∂ν) ≤ ∫⁻ t, variationalNorm r (fun n => g t n) ∂ν`.

The two terms are treated separately and the results are added, using the additivity of the
`ℝ≥0∞`-valued integral `lintegral_add_left'` — whose hypothesis is the almost everywhere
measurability of the countable supremum `t ↦ ⨆ n, ‖g t n‖ₑ`, which is supplied by
`AEMeasurable.iSup` and the a.e. strong measurability of each integrand.

* The supremum part: `‖∫ g t n ∂ν‖ₑ ≤ ∫⁻ t, ‖g t n‖ₑ ∂ν` (`enorm_integral_le_lintegral_enorm`),
  then take the supremum over `n`, which is at most the integral of the supremum.
* The variation part: for a monotone `N` and `J : ℕ`, the vector of increments has coordinates
  `(∫ g t (N (i + 1)) ∂ν) - (∫ g t (N i) ∂ν) = ∫ (g t (N (i + 1)) - g t (N i)) ∂ν`
  (`integral_sub`), so it is the Bochner integral of the `ℓ^r`-valued function
  `t ↦ WithLp.toLp r (fun i => g t (N (i + 1)) - g t (N i))`
  (the integral commutes with the continuous linear equivalence `PiLp.continuousLinearEquiv`,
  whose inverse is `WithLp.toLp r`, and `eval_integral` reads off the coordinates).  Minkowski's
  inequality in the finite-dimensional Banach space `ℓ^r` is then
  `enorm_integral_le_lintegral_enorm` once more.
-/

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators

set_option linter.style.haveILetI false

theorem variationalNorm_integral_le {r : NNReal} (hr : 1 ≤ r) {ν : MeasureTheory.Measure ℝ}
    [MeasureTheory.SFinite ν] {g : ℝ → ℕ → ℂ}
    (hint : ∀ n : ℕ, MeasureTheory.Integrable (fun t : ℝ => g t n) ν) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => MeasureTheory.integral ν (fun t : ℝ => g t n))
      ≤ MeasureTheory.lintegral ν (fun t : ℝ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => g t n)) := by
  haveI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  set a : ℕ → ℂ := fun n => ∫ t, g t n ∂ν with ha
  -- The supremum part: the supremum of the integrals is bounded by the integral of the supremum.
  have hS : (⨆ n : ℕ, ‖a n‖ₑ) ≤ ∫⁻ t, (⨆ n : ℕ, ‖g t n‖ₑ) ∂ν := by
    refine iSup_le fun n => ?_
    calc ‖a n‖ₑ = ‖∫ t, g t n ∂ν‖ₑ := rfl
      _ ≤ ∫⁻ t, ‖g t n‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t, (⨆ n : ℕ, ‖g t n‖ₑ) ∂ν :=
          lintegral_mono fun t => le_iSup (fun n : ℕ => ‖g t n‖ₑ) n
  -- The countable supremum of the extended norms is almost everywhere measurable.
  have hmeasS : AEMeasurable (fun t : ℝ => ⨆ n : ℕ, ‖g t n‖ₑ) ν :=
    AEMeasurable.iSup fun n => (hint n).aestronglyMeasurable.enorm
  -- The variation part: Minkowski's inequality in the finite-dimensional space `ℓ^r`.
  have hV : Submission.PointwiseErgodicTheorems.varPart r a ≤
      ∫⁻ t, Submission.PointwiseErgodicTheorems.varPart r (fun n : ℕ => g t n) ∂ν := by
    unfold Submission.PointwiseErgodicTheorems.varPart
    refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
    set F : ℝ → (Fin J → ℂ) := fun t i => g t (N (i + 1)) - g t (N i) with hF
    have hFint : ∀ i : Fin J, Integrable (fun t => F t i) ν := by
      intro i
      simp only [hF]
      exact (hint (N (i + 1))).sub (hint (N i))
    -- The coordinates of the integral of `F` are the differences of the integrals.
    have hcoord : (∫ t, F t ∂ν) = fun i : Fin J => a (N (i + 1)) - a (N i) := by
      funext i
      rw [eval_integral hFint i]
      simp only [hF]
      rw [integral_sub (hint (N (i + 1))) (hint (N i))]
    -- The integral commutes with `WithLp.toLp r` (a continuous linear equivalence).
    have hCLE : (∫ t, WithLp.toLp r (F t) ∂ν) = WithLp.toLp r (∫ t, F t ∂ν) :=
      (PiLp.continuousLinearEquiv (r : ℝ≥0∞) ℝ (fun _ : Fin J => ℂ)).symm.integral_comp_comm F
    calc ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => a (N (i + 1)) - a (N i))‖
        = ENNReal.ofReal ‖WithLp.toLp r (∫ t, F t ∂ν)‖ := by rw [hcoord]
      _ = ‖∫ t, WithLp.toLp r (F t) ∂ν‖ₑ := by rw [← hCLE, ofReal_norm]
      _ ≤ ∫⁻ t, ‖WithLp.toLp r (F t)‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t, Submission.PointwiseErgodicTheorems.varPart r (fun n : ℕ => g t n) ∂ν := by
          refine lintegral_mono fun t => ?_
          rw [← ofReal_norm]
          simp only [hF]
          refine le_iSup_of_le (f := fun J' => ⨆ (N' : ℕ → ℕ) (_ : Monotone N'),
              ENNReal.ofReal ‖WithLp.toLp r
                (fun i : Fin J' => g t (N' (i + 1)) - g t (N' i))‖) J ?_
          exact le_iSup₂ (f := fun (N' : ℕ → ℕ) (_ : Monotone N') =>
              ENNReal.ofReal ‖WithLp.toLp r
                (fun i : Fin J => g t (N' (i + 1)) - g t (N' i))‖) N hN
  calc PointwiseErgodicTheorems.variationalNorm r a
      = (⨆ n : ℕ, ‖a n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r a :=
          Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r a
    _ ≤ (∫⁻ t, (⨆ n : ℕ, ‖g t n‖ₑ) ∂ν) +
          (∫⁻ t, Submission.PointwiseErgodicTheorems.varPart r (fun n : ℕ => g t n) ∂ν) :=
          add_le_add hS hV
    _ = ∫⁻ t, ((⨆ n : ℕ, ‖g t n‖ₑ) +
          Submission.PointwiseErgodicTheorems.varPart r (fun n : ℕ => g t n)) ∂ν :=
          (lintegral_add_left' hmeasS _).symm
    _ = ∫⁻ t, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => g t n) ∂ν :=
          lintegral_congr fun t =>
            (Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r
              (fun n : ℕ => g t n)).symm

end Work.KMTAreas.A7
