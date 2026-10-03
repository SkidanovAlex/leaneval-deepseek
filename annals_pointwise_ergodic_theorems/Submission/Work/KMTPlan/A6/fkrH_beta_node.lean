import Mathlib
import Submission.Work.KMTPlan.A6.FkrBasic

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- `fkrH` vanishes at the left endpoint `β 0` (the initial node of the interpolation). -/
lemma fkrH_beta_zero (K : ℕ) (β : ℕ → ℝ) (w : ℕ → X → ℂ) (x : X) (hβ0 : 0 ≤ β 0)
    (hβmono : Monotone β) (hβK : β K = 1) :
    fkrH K β w x (β 0) = 0 := by
  have hβ01 : β 0 ≤ 1 := by
    rw [← hβK]; exact hβmono (Nat.zero_le K)
  unfold fkrH
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  rw [fkrPhi_beta β hβ0 hβmono (k := k) (q := 0) hβ01, if_neg (by omega)]
  simp

/-- **The node identity for `fkrH`.**  If the densities `w k x` are the increments of `g` divided
by the block lengths `β k - β (k-1)` (in the multiplicative form of `hdens`) and `β` is monotone
with `β 0 ≥ 0`, `β K = 1`, then `fkrH` reproduces the values `g` at every node `β i`, `i ≤ K`. -/
lemma fkrH_beta_node {X : Type*} [MeasurableSpace X] {K : ℕ} {β : ℕ → ℝ}
    {w g : ℕ → X → ℂ} {x : X}
    (hβ0 : 0 ≤ β 0) (hβmono : Monotone β) (hβK : β K = 1)
    (hdens : ∀ k ∈ Finset.Icc 1 K, w k x * ((β k - β (k - 1) : ℝ) : ℂ) = g k x - g (k - 1) x)
    {i : ℕ} (hi : i ≤ K) :
    Work.KMTPlan.A6.fkrH K β w x (β i) = g i x - g 0 x := by
  have hβ1K : ∀ k ≤ K, β k ≤ 1 := fun k hk => by rw [← hβK]; exact hβmono hk
  have hz : fkrH K β w x (β 0) = 0 := fkrH_beta_zero K β w x hβ0 hβmono hβK
  have h := fkrH_chain K β w g x hβ0 hβmono hβ1K hdens (Nat.zero_le i) hi
  rw [hz, sub_zero] at h
  exact h

end Work.KMTPlan.A6
