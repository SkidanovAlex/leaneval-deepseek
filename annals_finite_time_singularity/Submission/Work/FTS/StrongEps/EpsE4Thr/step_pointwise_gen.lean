import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.StepFacts.StepPointwise
import Submission.Work.FTS.StrongEps.StepFacts.SlotBounds
import Submission.Work.FTS.StrongEps.StepFacts.HkMemJepsStepAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.StrongEps.StepFacts

set_option maxHeartbeats 2000000

/-- The cardinal-count bookkeeping: `(m+1) • ((m+1) • X) = ((m+1)^2) * X`. -/
private lemma natCast_succ_mul_succ (m : ℕ) {X : ℝ≥0∞} :
    ((m + 1 : ℕ) : ℝ≥0∞) * (((m + 1 : ℕ) : ℝ≥0∞) * X)
      = (((m + 1) ^ 2 : ℕ) : ℝ≥0∞) * X := by
  rw [← mul_assoc, ← Nat.cast_mul]
  congr 1
  ring

/-- `((m+1)^2 : ℕ)` cast to `ℝ≥0∞`, plus `2`, is the cast of `(m+1)^2 + 2`. -/
private lemma natCast_sq_add_two (m : ℕ) :
    (((m + 1) ^ 2 : ℕ) : ℝ≥0∞) + 2 = ((((m + 1) ^ 2 + 2 : ℕ) : ℝ≥0∞)) := by
  push_cast
  ring

/-- **The pointwise one-order smoothing step, at every order `m ≥ 2`.**

This is `StepFacts.step_pointwise` with its restriction `m ≤ 8` removed: the arithmetic of the
proof never used the numerical bound `9` on the number of terms of the double sum — the honest
count of the top mixed slots is `(m+1)²`, so the constant is `(m+1)² + 2` times `Mmax` (compare
the frozen version, whose constant `ε⁻¹ Bconst = 200 ε⁻¹ Dm` is obtained by losing
`(m+1)² + 2 ≤ 100` and `100 Mmax ≤ ε⁻¹ Bconst`, both of which need `m ≤ 8`).

The estimate is assembled exactly as in the frozen case: the slots of order `≤ m-1` are handled
by Jensen (`low_le`, no price), the pure `D_z^m`-slot by the `z`-route (`zslot_le`), the mixed
top slots `D_z^j D_θ^i`, `i ≥ 1`, by the two routed slot bounds (`slot_theta_le` for `j = 0`,
`slot_z_le` for `j ≥ 1`), and everything is summed with `HkIntegrand_le_prev_add_TopSq`. -/
theorem step_pointwise_gen (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε α c : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : α ∈ Set.Ioc 0 1) {m : ℕ} (hm : 2 ≤ m)
    {u : ℝ → ℝ → ℝ} (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad)
    (hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (c * (|p.1| + |p.2|)) * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
      ≤ ENNReal.ofReal ((((m + 1 : ℕ) ^ 2 + 2 : ℕ) : ℝ)
            * Work.FTS.StrongEps.StepFacts.Mmax ρ ε)
          * Work.FTS.StrongEps.StepFacts.Jint ρ ε α c u m z θ := by
  -- the slots of order `≤ m - 1`: Jensen with the probability kernel, no price
  have hlow := low_le ρ hρ hε hε1 hα hm hu hWη hWγ hz hθ
  -- the pure `D_z^m`-slot
  have hzslot := zslot_le (α := α) (c := c) ρ hρ hε hε1 hm hu hz hθ (hWη z θ hz hθ)
  -- the mixed top slots `D_z^j D_θ^i` with `i ≥ 1`, `i + j = m`
  have hslots : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (m + 1),
      ENNReal.ofReal (if 1 ≤ i ∧ i + j = m then
          (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε u) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ := by
    intro i _ j _
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
  -- the whole double sum of top mixed slots, counted as `(m+1)²` terms
  have hmsum : ENNReal.ofReal (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j = m then
          (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε u) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (((m + 1) ^ 2 : ℕ) : ℝ≥0∞)
        * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ) := by
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
      _ = (((m + 1) ^ 2 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ) :=
          natCast_succ_mul_succ m
  -- `TopSq` against the reference `lintegral`
  have htop : ENNReal.ofReal (TopSq α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
      ≤ ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ
        + (((m + 1) ^ 2 : ℕ) : ℝ≥0∞)
          * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ) := by
    rw [TopSq]
    rw [ENNReal.ofReal_add (sq_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
        split_ifs with h <;> simp [sq_nonneg])]
    exact add_le_add hzslot hmsum
  -- the splitting of the integrand
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
  have hstep2 : ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1)
        (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
        + ENNReal.ofReal (TopSq α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
      ≤ Jint ρ ε α c u m z θ
        + (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ
          + (((m + 1) ^ 2 : ℕ) : ℝ≥0∞)
            * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ)) :=
    add_le_add hlow htop
  -- the numerical bookkeeping: `Mmax ≥ 1` lets `Jint` be absorbed into the `(m+1)² + 2` terms
  have hX1 : Jint ρ ε α c u m z θ
      ≤ ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ := by
    simpa only [one_mul] using
      mul_le_mul_left (one_le_ofReal_Mmax ρ ε) (Jint ρ ε α c u m z θ)
  have hfinal : Jint ρ ε α c u m z θ
      + (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ
        + (((m + 1) ^ 2 : ℕ) : ℝ≥0∞)
          * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ))
      ≤ ENNReal.ofReal ((((m + 1 : ℕ) ^ 2 + 2 : ℕ) : ℝ) * Mmax ρ ε)
          * Jint ρ ε α c u m z θ := by
    calc Jint ρ ε α c u m z θ
          + (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ
            + (((m + 1) ^ 2 : ℕ) : ℝ≥0∞)
              * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ))
        ≤ (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ)
            + (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ
              + (((m + 1) ^ 2 : ℕ) : ℝ≥0∞)
                * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ)) :=
          add_le_add_left hX1 _
      _ = ((((m + 1) ^ 2 : ℕ) : ℝ≥0∞) + 2)
            * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ) := by ring
      _ = ((((m + 1) ^ 2 + 2 : ℕ) : ℝ≥0∞))
            * (ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ) := by
          rw [natCast_sq_add_two]
      _ = ENNReal.ofReal ((((m + 1 : ℕ) ^ 2 + 2 : ℕ) : ℝ) * Mmax ρ ε)
            * Jint ρ ε α c u m z θ := by
          rw [← ENNReal.ofReal_natCast ((m + 1) ^ 2 + 2), ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (((m + 1) ^ 2 + 2 : ℕ) : ℝ))]
  exact hstep1.trans (hstep2.trans hfinal)

end Work.FTS.StrongEps.EpsE4Thr
