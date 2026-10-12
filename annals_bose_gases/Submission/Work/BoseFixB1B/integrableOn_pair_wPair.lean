import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.potGapAdditivityStratum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

open MeasureTheory
open scoped BigOperators
open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- A continuous function on the (compact) analysis box is bounded there by a nonnegative
constant. -/
private lemma exists_abs_bound_abox' {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ}
    (hΦc : Continuous Φ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ abox n ℓ, |Φ x| ≤ C := by
  obtain ⟨C, hC⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn
    (s := abox n ℓ) (f := Φ) hΦc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hC x hx
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- PROOF ROUTE (for the prover): the import cone `Submission.KernelFibreBound` supplies
`chiSup`, `chiR0`, `wPair`, `X`, `abox`, `abox_compact`; `Submission.PairInt` supplies
`Submission.BoseGases.null_preimage_pair_whole` and `pairInt_sq`; and
`Submission.Work.BoseFixB1B.potGapAdditivityStratum` supplies
`Submission.Work.BoseFixB1B.integrableOn_mul_abs_v_pair` (box integrability of
`x ↦ Ψ x * |vv (x p.1 - x p.2)|` for `Ψ` measurable and bounded on the box, from `MemLp vv 1`;
its `pairSet N` is `{p | p.1 ≠ p.2}`, and `ij.1 < ij.2` implies `ij.1 ≠ ij.2`).
Use the pointwise domination `|wPair ℓ vv x y| ≤ chiSup²·2·|vv (x - y)|`
(`Submission.BoseGases.abs_chiScale_le_chiSup`, `Submission.BoseGases.wScaled_abs_le_two`), the
integrability of the majorant `fun x => (Φ x)^2 * ∑_{i<j} chiSup²·2·|vv (x i - x j)|` (a finite sum
of the above; `Φ` is continuous, hence bounded on the compact box), and `Integrable.mono'` with
the a.e. measurability of `x ↦ ∑_{i<j} wPair ℓ vv (x i) (x j)` (via the `AEMeasurable.mk`
representative of `vv` and `null_preimage_pair_whole`). -/
theorem integrableOn_pair_wPair {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) {vv : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv1 : MeasureTheory.MemLp vv 1)
    (hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → vv z = 0)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
        Submission.BoseGases.wPair ℓ vv (x ij.1.1) (x ij.1.2)))
      (Submission.BoseGases.abox n ℓ) := by
  classical
  have hvi : Integrable vv := memLp_one_iff_integrable.mp hv1
  obtain ⟨B, hB0, hBb⟩ := exists_abs_bound_abox' (n := n) hℓ hΦc
  -- `Φ²` is measurable and bounded on the box
  have hΦ2m : Measurable (fun x : X n => (Φ x) ^ 2) := hΦc.measurable.pow_const 2
  have hB2 : ∀ x ∈ abox n ℓ, |(Φ x) ^ 2| ≤ B ^ 2 := by
    intro x hx
    rw [abs_of_nonneg (sq_nonneg (Φ x)), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg (Φ x)) (by simpa [Real.norm_eq_abs] using hBb x hx) 2
  -- the constant of the pointwise domination
  let K : ℝ := chiSup * (2 * (Real.sqrt chiNormSq)⁻¹)
  have hK0 : 0 ≤ K := by
    refine mul_nonneg (le_of_lt chiSup_pos) (mul_nonneg (by norm_num) ?_)
    exact inv_nonneg.mpr (le_of_lt (Real.sqrt_pos.mpr chiNormSq_pos))
  let μ : Measure (X n) := volume.restrict (abox n ℓ)
  -- integrability of the majorant, one pair at a time
  have hpair : ∀ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
      Integrable (fun x : X n => K * ((Φ x) ^ 2 * |vv (x ij.1.1 - x ij.1.2)|)) μ := by
    intro ij
    have hne : (ij : Fin n × Fin n).1 ≠ (ij : Fin n × Fin n).2 := ne_of_lt ij.2
    have hp : (ij : Fin n × Fin n) ∈ Submission.BoseGases.pairSet n := by
      simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hne
    have h := integrableOn_mul_abs_v_pair (N := n) (v := vv) hv1 hℓ hΦ2m
      (C := B ^ 2) (sq_nonneg B) hB2 (p := (ij : Fin n × Fin n)) hp
    exact h.integrable.const_mul K
  have hGint : Integrable (fun x : X n =>
      ∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
        K * ((Φ x) ^ 2 * |vv (x ij.1.1 - x ij.1.2)|)) μ := by
    refine integrable_finsetSum (μ := μ)
      (s := (Finset.univ : Finset {ij : Fin n × Fin n | ij.1 < ij.2}))
      (f := fun (ij : {ij : Fin n × Fin n | ij.1 < ij.2}) (x : X n) =>
        K * ((Φ x) ^ 2 * |vv (x ij.1.1 - x ij.1.2)|)) ?_
    intro ij _
    exact hpair ij
  -- a.e. strong measurability of the target function
  have hΦ2sm : AEStronglyMeasurable (fun x : X n => (Φ x) ^ 2) μ := hΦ2m.aestronglyMeasurable
  have hSsm : AEStronglyMeasurable (fun x : X n =>
      ∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
        Submission.BoseGases.wPair ℓ vv (x ij.1.1) (x ij.1.2)) μ := by
    have h := Finset.aestronglyMeasurable_sum (μ := μ)
      (s := (Finset.univ : Finset {ij : Fin n × Fin n | ij.1 < ij.2}))
      (f := fun (ij : {ij : Fin n × Fin n | ij.1 < ij.2}) (x : X n) =>
        Submission.BoseGases.wPair ℓ vv (x ij.1.1) (x ij.1.2))
      (by
        intro ij _
        exact aesm_wPair_pair (N := n) hℓ hvi ij.1.1 ij.1.2 (ne_of_lt ij.2))
    refine h.congr ?_
    filter_upwards with x
    simp [Finset.sum_apply]
  have htarget : AEStronglyMeasurable (fun x : X n => (Φ x) ^ 2 *
      (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
        Submission.BoseGases.wPair ℓ vv (x ij.1.1) (x ij.1.2))) μ := by
    refine (hΦ2sm.mul hSsm).congr ?_
    filter_upwards with x
    simp [Pi.mul_apply]
  -- pointwise domination by the majorant
  have hdom : ∀ᵐ x ∂μ, ‖(Φ x) ^ 2 *
      (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
        Submission.BoseGases.wPair ℓ vv (x ij.1.1) (x ij.1.2))‖
      ≤ ∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
          K * ((Φ x) ^ 2 * |vv (x ij.1.1 - x ij.1.2)|) := by
    refine ae_of_all _ (fun x => ?_)
    have hsum : |∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
          Submission.BoseGases.wPair ℓ vv (x ij.1.1) (x ij.1.2)|
        ≤ ∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
            K * |vv (x ij.1.1 - x ij.1.2)| := by
      refine le_trans (Finset.abs_sum_le_sum_abs
        (fun ij : {ij : Fin n × Fin n | ij.1 < ij.2} =>
          Submission.BoseGases.wPair ℓ vv (x ij.1.1) (x ij.1.2)) Finset.univ) ?_
      refine Finset.sum_le_sum (fun ij _ => ?_)
      simpa [K] using
        wPair_abs_bound_le (ℓ := ℓ) (R := R) hℓ hsupp hRℓ (x ij.1.1) (x ij.1.2)
    have hmuls : (Φ x) ^ 2 * (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
          K * |vv (x ij.1.1 - x ij.1.2)|)
        = ∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
            K * ((Φ x) ^ 2 * |vv (x ij.1.1 - x ij.1.2)|) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun ij _ => by ring)
    calc ‖(Φ x) ^ 2 * (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
            Submission.BoseGases.wPair ℓ vv (x ij.1.1) (x ij.1.2))‖
        = (Φ x) ^ 2 * |∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
            Submission.BoseGases.wPair ℓ vv (x ij.1.1) (x ij.1.2)| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Φ x))]
      _ ≤ (Φ x) ^ 2 * (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
            K * |vv (x ij.1.1 - x ij.1.2)|) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg (Φ x))
      _ = ∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
            K * ((Φ x) ^ 2 * |vv (x ij.1.1 - x ij.1.2)|) := hmuls
  exact Integrable.mono' hGint htarget hdom

end Work.BoseFixB1B
