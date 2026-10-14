import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The slots of order `≤ m-1` of `J_ε u` are dominated by `Jint` (Jensen with the probability
kernel `Jker ρ ε`, no price). -/
theorem low_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε α c z θ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hα : α ∈ Set.Ioc 0 1) {m : ℕ} (hm : 2 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad)
    (hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (c * (|p.1| + |p.2|)) * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2))
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
      ≤ Jint ρ ε α c u m z θ := by
  refine (HkSqAux.ofReal_GJ_le ρ hρ.moll hε hα hu hWη hWγ (le_of_lt hz)
    (⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ : θ ∈ Work.Spaces.Iθ) (m - 1)).trans ?_
  rw [Jint]
  refine lintegral_mono fun p => ?_
  exact mul_le_mul_left (mul_le_mul_left
    (ENNReal.ofReal_le_ofReal (Jker_le_Psi ρ hρ.moll.nonneg hε hε1 p)) _) _

/-- **The pointwise one-order smoothing step.** -/
theorem step_pointwise (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε α c : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hα : α ∈ Set.Ioc 0 1) {m : ℕ} (hm : 2 ≤ m) (hm8 : m ≤ 8)
    {u : ℝ → ℝ → ℝ} (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad)
    (hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (c * (|p.1| + |p.2|)) * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
      ≤ ENNReal.ofReal (ε⁻¹ * Bconst ρ) * Jint ρ ε α c u m z θ := by
  have hlow := low_le ρ hρ hε hε1 hα hm hu hWη hWγ hz hθ
  have hzslot := zslot_le (α := α) (c := c) ρ hρ hε hε1 hm hu hz hθ (hWη z θ hz hθ)
  have hslots : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (m + 1),
      ENNReal.ofReal (if 1 ≤ i ∧ i + j = m then
          (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε u) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ := by
    intro i hi j hj
    by_cases hc' : 1 ≤ i ∧ i + j = m
    · rw [if_pos hc']
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        have him : i = m := by omega
        subst him
        simpa only [Work.Spaces.mixed_zero_left] using
          slot_theta_le (α := α) (c := c) ρ hρ hε hε1 hm hu hz hθ (hWγ z θ hz hθ)
      · exact slot_z_le (α := α) (c := c) ρ hρ hε hε1 hm hu hz hθ (hWγ z θ hz hθ)
          hjpos hc'.1 hc'.2
    · rw [if_neg hc']
      simp
  have hmsum : ENNReal.ofReal (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j = m then
          (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε u) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (81 : ℝ≥0∞) * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ) := by
    have hnn : ∀ i ∈ Finset.range (m + 1),
        0 ≤ ∑ j ∈ Finset.range (m + 1),
          (if 1 ≤ i ∧ i + j = m then
            (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε u) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
      fun i _ => Finset.sum_nonneg fun j _ => by split_ifs with h <;> simp [sq_nonneg]
    rw [ofReal_sum_of_nonneg _ _ hnn]
    have hinner : ∀ i ∈ Finset.range (m + 1),
        ENNReal.ofReal (∑ j ∈ Finset.range (m + 1),
          (if 1 ≤ i ∧ i + j = m then
            (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε u) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = ∑ j ∈ Finset.range (m + 1), (if 1 ≤ i ∧ i + j = m then
              ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε u) z θ
                * Work.Spaces.Wt α z θ) ^ 2) else 0) := by
      intro i _
      rw [ofReal_sum_of_nonneg _ _ (fun j _ => by split_ifs with h <;> simp [sq_nonneg])]
      exact Finset.sum_congr rfl fun j _ => by
        by_cases h : 1 ≤ i ∧ i + j = m
        · simp only [if_pos h]
        · simp only [if_neg h, ENNReal.ofReal_zero]
    calc (∑ i ∈ Finset.range (m + 1), ENNReal.ofReal (∑ j ∈ Finset.range (m + 1),
            (if 1 ≤ i ∧ i + j = m then
              (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε u) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)))
        = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
            (if 1 ≤ i ∧ i + j = m then
              ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε u) z θ
                * Work.Spaces.Wt α z θ) ^ 2) else 0) :=
          Finset.sum_congr rfl fun i hi => hinner i hi
      _ ≤ ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
            (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => by
            by_cases h : 1 ≤ i ∧ i + j = m
            · simpa only [if_pos h] using hslots i hi j hj
            · rw [if_neg h]
              simp
      _ = ((m + 1 : ℕ) : ℝ≥0∞) * (((m + 1 : ℕ) : ℝ≥0∞)
            * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ)) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (81 : ℝ≥0∞) * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ) := by
          have hcard : (((m + 1 : ℕ) : ℝ≥0∞)) ≤ 9 := by
            have : m + 1 ≤ 9 := by omega
            exact_mod_cast this
          calc ((m + 1 : ℕ) : ℝ≥0∞)
                * (((m + 1 : ℕ) : ℝ≥0∞)
                  * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ))
              ≤ (9 : ℝ≥0∞) * (9 * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ)) :=
                (mul_le_mul_right (mul_le_mul_left hcard _) _).trans (mul_le_mul_left hcard _)
            _ = 81 * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ) := by
                rw [← mul_assoc]
                congr 1
                norm_num
  have htop : ENNReal.ofReal (TopSq α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
      ≤ ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ
        + (81 : ℝ≥0∞) * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ) := by
    rw [TopSq]
    rw [ENNReal.ofReal_add (sq_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
        split_ifs with h <;> simp [sq_nonneg])]
    exact add_le_add hzslot hmsum
  have hsplit := HkIntegrand_le_prev_add_TopSq α m (by omega : 1 ≤ m)
    (Work.FTS.StrongEps.Jeps ρ ε u) z θ
  have h1 : 0 ≤ Work.Spaces.HkIntegrand α (m - 1) (Work.FTS.StrongEps.Jeps ρ ε u) z θ :=
    Work.Spaces.HkIntegrand_nonneg α (m - 1) _ _ _
  have h2 : 0 ≤ TopSq α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ :=
    TopSq_nonneg α m _ z θ
  have hstep1 : ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
      ≤ ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
        + ENNReal.ofReal (TopSq α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ) := by
    rw [← ENNReal.ofReal_add h1 h2]
    exact ENNReal.ofReal_le_ofReal hsplit
  have hstep2 : ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
        + ENNReal.ofReal (TopSq α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
      ≤ Jint ρ ε α c u m z θ
        + (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ
          + (81 : ℝ≥0∞) * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ)) :=
    add_le_add hlow htop
  have h100le : 100 * Mmax ρ ε ≤ ε⁻¹ * Bconst ρ := by
    have h := Mmax_le ρ hρ hε hε1
    rw [Bconst]
    have hεi : 0 ≤ ε⁻¹ := by positivity
    have hDm : 0 ≤ Dm ρ := le_trans zero_le_one (le_max_left _ _)
    nlinarith [h, hεi, hDm]
  have hchain : Jint ρ ε α c u m z θ
        + (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ
          + (81 : ℝ≥0∞) * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ))
      ≤ ENNReal.ofReal (ε⁻¹ * Bconst ρ) * Jint ρ ε α c u m z θ := by
    set X : ℝ≥0∞ := ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ with hX
    have hX1 : Jint ρ ε α c u m z θ ≤ X := by
      have h := mul_le_mul_left (one_le_ofReal_Mmax ρ ε) (Jint ρ ε α c u m z θ)
      rw [hX]
      simpa only [one_mul] using h
    have h100c : (((100 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal (100 : ℝ) :=
      (ENNReal.ofReal_natCast 100).symm
    have heq100 : (((100 : ℕ) : ℝ≥0∞)) * X
        = ENNReal.ofReal (100 * Mmax ρ ε) * Jint ρ ε α c u m z θ := by
      rw [hX, h100c, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100)]
    calc Jint ρ ε α c u m z θ
            + (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ + 81 * X)
        = (1 : ℝ≥0∞) * Jint ρ ε α c u m z θ + 82 * X := by rw [hX]; ring
      _ ≤ X + 82 * X := add_le_add (by simpa only [one_mul] using hX1) le_rfl
      _ = 83 * X := by ring
      _ ≤ ((100 : ℕ) : ℝ≥0∞) * X := by
          refine mul_le_mul_left ?_ _
          norm_num
      _ = ENNReal.ofReal (100 * Mmax ρ ε) * Jint ρ ε α c u m z θ := heq100
      _ ≤ ENNReal.ofReal (ε⁻¹ * Bconst ρ) * Jint ρ ε α c u m z θ :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal h100le) _
  exact hstep1.trans (hstep2.trans hchain)

end Work.FTS.StrongEps.StepFacts
