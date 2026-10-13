/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/GainPt.lean`

The **pointwise `m`-order gain**: the whole level-`M` integrand of `J_ε f` is dominated by
`Cgain ρ ε M` times the `p`-average (against the single routed density `LamFull ρ ε c M`) of the
level-`k` integrand of `f`.  Assembles the two per-slot bounds `zslot_le_gain`, `mslot_le_gain`
over the `(M+1) + (M+1)²` slots of `HkIntegrand α M`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.StepFacts.OfRealTools
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainSlot.zslot_le_gain
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainSlot.mslot_le_gain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem HkIntegrand_Jeps_gain_pt {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε α c : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 ≤ c) {M k : ℕ} (hk : 1 ≤ k)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hWη : ∀ p : ℝ × ℝ, Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ Real.exp (c * (|p.1| + |p.2|))
        * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hWγ : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :
    ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
      ≤ ENNReal.ofReal (Cgain ρ ε M)
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (LamFull ρ ε c M p)
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
  set J : ℝ≥0∞ := ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (LamFull ρ ε c M p)
      * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
          (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) with hJdef
  set Kg : ℝ≥0∞ := ENNReal.ofReal (KgainBig ρ ε M) with hKgdef
  set A : ℝ := ∑ a ∈ Finset.range (M + 1),
    (Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 with hAdef
  set B : ℝ := ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (M + 1),
    (if 1 ≤ i ∧ i + j ≤ M then
      (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0) with hBdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact Finset.sum_nonneg fun a _ => sq_nonneg _
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs with h <;> simp [sq_nonneg]
  have hsplit : Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ = A + B := by
    simp only [Work.Spaces.HkIntegrand]
    rw [← hAdef, ← hBdef]
  -- the per-slot bounds, and the two finite sums
  have hslotA : ∀ a ∈ Finset.range (M + 1),
      ENNReal.ofReal ((Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) ≤ Kg * J := by
    intro a ha
    have haM : a ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    simpa only [hJdef, hKgdef] using
      GainSlot.zslot_le_gain hρ hε hε1 hc hf hz hθ hWη haM
  have hslotB : ∀ i ∈ Finset.range (M + 1), ∀ j ∈ Finset.range (M + 1),
      ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ M then
        (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0) ≤ Kg * J := by
    intro i _ j _
    by_cases hc' : 1 ≤ i ∧ i + j ≤ M
    · rw [if_pos hc']
      simpa only [hJdef, hKgdef] using
        GainSlot.mslot_le_gain hρ hε hε1 hc hk hf hz hθ hWγ hc'.1 hc'.2
    · rw [if_neg hc']
      simp only [ENNReal.ofReal_zero]
      exact zero_le
  have hA_le : (∑ a ∈ Finset.range (M + 1),
      ENNReal.ofReal ((Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ≤ ((M + 1 : ℕ) : ℝ≥0∞) * (Kg * J) := by
    refine (Finset.sum_le_card_nsmul (Finset.range (M + 1)) _ (Kg * J) hslotA).trans ?_
    rw [Finset.card_range]
    exact Work.FTS.StrongEps.StepFacts.nsmul_le_natCast_mul (M + 1) (Kg * J)
  have hB_le : (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (M + 1),
      ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ M then
        (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) ≤ (((M + 1) * (M + 1) : ℕ) : ℝ≥0∞) * (Kg * J) := by
    have hinner : ∀ i ∈ Finset.range (M + 1),
        (∑ j ∈ Finset.range (M + 1), ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ M then
          (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ((M + 1 : ℕ) : ℝ≥0∞) * (Kg * J) := fun i hi =>
      (Finset.sum_le_card_nsmul (Finset.range (M + 1)) _ (Kg * J)
        (fun j hj => hslotB i hi j hj)).trans (by
          rw [Finset.card_range]
          exact Work.FTS.StrongEps.StepFacts.nsmul_le_natCast_mul (M + 1) (Kg * J))
    refine (Finset.sum_le_card_nsmul (Finset.range (M + 1)) _ _ hinner).trans ?_
    rw [Finset.card_range, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
  -- the `ofReal` split and the numerical bookkeeping
  have hpt : ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
      = ENNReal.ofReal A + ENNReal.ofReal B := by
    rw [hsplit, ENNReal.ofReal_add hA0 hB0]
  have h1 : ENNReal.ofReal A = ∑ a ∈ Finset.range (M + 1),
      ENNReal.ofReal ((Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    rw [hAdef, ENNReal.ofReal_sum_of_nonneg]
    exact fun a _ => sq_nonneg _
  have h2 : ENNReal.ofReal B = ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (M + 1),
      ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ M then
        (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
          * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    rw [hBdef, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg]
      exact fun j _ => by split_ifs with h <;> simp [sq_nonneg]
    · exact fun i _ => Finset.sum_nonneg fun j _ => by
        split_ifs with h <;> simp [sq_nonneg]
  have hAB : ENNReal.ofReal A + ENNReal.ofReal B
      ≤ ((((M + 1) + (M + 1) * (M + 1) : ℕ)) : ℝ≥0∞) * (Kg * J) := by
    rw [h1, h2]
    refine (add_le_add hA_le hB_le).trans (le_of_eq ?_)
    rw [← add_mul, ← Nat.cast_add]
  have hC : ENNReal.ofReal (Cgain ρ ε M) * J
      = ((((M + 1) + (M + 1) * (M + 1) : ℕ)) : ℝ≥0∞) * (Kg * J) := by
    rw [Cgain, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ← hKgdef]
    rw [pow_two, mul_assoc]
  rw [hpt]
  exact hAB.trans (le_of_eq hC.symm)

end Work.FTS.StrongEps.EpsE4Thr
