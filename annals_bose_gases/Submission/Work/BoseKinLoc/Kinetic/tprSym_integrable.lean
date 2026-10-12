import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.integrable_kinFT_sq
import Submission.Work.BoseKinLoc.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the two-regime symbol `tprSym` against `‖fhat ψ‖²`

The two-regime symbol of BS `lm:kinloc` (FS `eq:Fs`) is

    `tprSym ℓ σ C p = if (5/6)(σℓ)⁻¹ ≤ ‖p‖ then ((‖p‖ − (2σℓ)⁻¹)₊)² else Cσ³‖p‖²`,

i.e. a quadratic-in-`p` function which is *globally dominated* by `max 1 (Cσ³) · ‖p‖²`:
in the far region `((r − c)₊)² ≤ r²` because `c ≥ 0`, and in the near region the bound
is `Cσ³ r²` directly.  Hence for a smooth compactly supported state `ψ` the integrand
`p ↦ tprSym ℓ σ C p · ‖fhat ψ p‖²` is dominated by `max 1 (Cσ³) · ‖p‖²‖fhat ψ p‖²`,
which is integrable (`Work.SmallBoxTBWord.integrable_kinFT_energy_cspt`); the details
are measurability (the symbol is a piecewise of two continuous functions of `‖p‖`) and
the pointwise bound.

This is exactly what makes the momentum integral on the right of `TprimeBound` and of
the two-regime assembly `assembly_symbol` well defined (non-junk).
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Work.BoseKinLoc.Kinetic

/-- The two-regime symbol is nonnegative for positive data. -/
lemma tprSym_nonneg {ℓ σ C : ℝ} (_hℓ : 0 < ℓ) (hσ : 0 < σ) (hC : 0 < C)
    (p : EuclideanSpace ℝ (Fin 3)) : 0 ≤ Work.BoseKinLoc.tprSym ℓ σ C p := by
  unfold Work.BoseKinLoc.tprSym Submission.BoseGases.fsKinCoeff
  split_ifs with h
  · exact sq_nonneg _
  · positivity

/-- **Global domination of the two-regime symbol by a constant times `‖p‖²`.**
In the far region the symbol is `((‖p‖ − (2σℓ)⁻¹)₊)² ≤ ‖p‖²` (the subtracted threshold is
nonnegative), and in the near region it is `Cσ³‖p‖² ≤ max 1 (Cσ³)·‖p‖²`. -/
lemma tprSym_le_max_mul_sq {ℓ σ C : ℝ} (hℓ : 0 < ℓ) (hσ : 0 < σ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseKinLoc.tprSym ℓ σ C p ≤ max 1 (C * σ ^ 3) * ‖p‖ ^ 2 := by
  unfold Work.BoseKinLoc.tprSym Submission.BoseGases.fsKinCoeff
  split_ifs with h
  · have hc : 0 ≤ (2 * (σ * ℓ))⁻¹ := by positivity
    have h1 : max (‖p‖ - (2 * (σ * ℓ))⁻¹) 0 ≤ ‖p‖ := max_le (by linarith) (norm_nonneg p)
    have h2 : (max (‖p‖ - (2 * (σ * ℓ))⁻¹) 0) ^ 2 ≤ ‖p‖ ^ 2 :=
      pow_le_pow_left₀ (le_max_right _ _) h1 2
    calc (max (‖p‖ - (2 * (σ * ℓ))⁻¹) 0) ^ 2
        ≤ ‖p‖ ^ 2 := h2
      _ = 1 * ‖p‖ ^ 2 := by ring
      _ ≤ max 1 (C * σ ^ 3) * ‖p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

/-- The two-regime symbol is (Borel) measurable: it is a piecewise, on the closed set
`{p | (5/6)(σℓ)⁻¹ ≤ ‖p‖}`, of two continuous functions of `‖p‖`. -/
lemma tprSym_aestronglyMeasurable {ℓ σ C : ℝ} :
    AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.tprSym ℓ σ C p) volume := by
  have hcont1 : Continuous
      (fun p : EuclideanSpace ℝ (Fin 3) => (max (‖p‖ - (2 * (σ * ℓ))⁻¹) 0) ^ 2) := by
    fun_prop
  have hcont2 : Continuous (fun p : EuclideanSpace ℝ (Fin 3) => C * σ ^ 3 * ‖p‖ ^ 2) := by
    fun_prop
  have hset : MeasurableSet {p : EuclideanSpace ℝ (Fin 3) | (5 / 6) * (σ * ℓ)⁻¹ ≤ ‖p‖} :=
    measurableSet_le measurable_const continuous_norm.measurable
  have heq : (fun p : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.tprSym ℓ σ C p)
      = fun p : EuclideanSpace ℝ (Fin 3) =>
          if p ∈ {q : EuclideanSpace ℝ (Fin 3) | (5 / 6) * (σ * ℓ)⁻¹ ≤ ‖q‖}
          then (max (‖p‖ - (2 * (σ * ℓ))⁻¹) 0) ^ 2 else C * σ ^ 3 * ‖p‖ ^ 2 := by
    funext p
    by_cases h : (5 / 6) * (σ * ℓ)⁻¹ ≤ ‖p‖ <;>
      simp only [Work.BoseKinLoc.tprSym, Submission.BoseGases.fsKinCoeff,
        Set.mem_ofPred_eq, h, if_true, if_false]
  rw [heq]
  exact (Measurable.ite hset hcont1.measurable hcont2.measurable).aestronglyMeasurable

/-- **Integrability of `tprSym ℓ σ C · ‖fhat ψ‖²` for smooth compactly supported `ψ`.**
The symbol is dominated by `max 1 (Cσ³)·‖p‖²`, so the integrand is dominated by
`max 1 (Cσ³) · (‖p‖²‖fhat ψ p‖²)`, which is integrable by
`Work.SmallBoxTBWord.integrable_kinFT_energy_cspt`. -/
theorem tprSym_integrable {ℓ σ C : ℝ} (hℓ : 0 < ℓ) (hσ : 0 < σ) (hC : 0 < C)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.tprSym ℓ σ C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) := by
  -- the `kinetic energy` integrand `‖p‖²‖fhat ψ p‖²` is integrable
  have hbase : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖p‖ ^ 2 * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) := by
    simpa only [Work.BoseKinLoc.fhat] using
      Work.SmallBoxTBWord.integrable_kinFT_energy_cspt ψ hψ hcs
  have hfsq : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) := by
    simpa only [Work.BoseKinLoc.fhat] using Work.BSKinetic.integrable_kinFT_sq ψ hψ hcs
  have hmeas : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.tprSym ℓ σ C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) volume :=
    tprSym_aestronglyMeasurable.mul hfsq.aestronglyMeasurable
  refine Integrable.mono' (hbase.const_mul (max 1 (C * σ ^ 3))) hmeas
    (Filter.Eventually.of_forall (fun p => ?_))
  have h1 := tprSym_le_max_mul_sq hℓ hσ (C := C) p
  have h2 := tprSym_nonneg hℓ hσ hC p
  have h3 : 0 ≤ ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h2 h3)]
  calc Work.BoseKinLoc.tprSym ℓ σ C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2
      ≤ (max 1 (C * σ ^ 3) * ‖p‖ ^ 2) * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 h3
    _ = max 1 (C * σ ^ 3) * (‖p‖ ^ 2 * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) := by ring

end Work.BoseKinLoc.Kinetic
