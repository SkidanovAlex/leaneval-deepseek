import Mathlib
import Submission.Work.Analysis.Probability.greedyDefs

/-!
# Monotonicity of the greedy `δ`-jump times

The greedy chain `t k = greedyTime x δ k` is monotone: `t k ≤ t (k + 1)` always.
Indeed, if `t k = ⊤` the chain has stopped and `t (k + 1) = ⊤` as well, while for
`t k < ⊤` we have `t (k + 1) = nextJump x δ (t k).toNat`, and `nextJump` is either
`⊤` or the first `n > (t k).toNat` with `δ < |x n - x ((t k).toNat)|`, hence always
at least `(t k).toNat`.  Together with `monotone_nat_of_le_succ` this gives
`Monotone (greedyTime x δ)`.
-/

open scoped ENat

namespace Work.Analysis.Probability

/-! ## Elementary properties of `nextJump` -/

private lemma nextJump_eq_find {x : ℕ → ℝ} {δ : ℝ} {a : ℕ}
    (h : ∃ n : ℕ, a < n ∧ δ < |x n - x a|) :
    nextJump x δ a = ((Nat.find h : ℕ) : ℕ∞) := by
  classical
  show dite (∃ n : ℕ, a < n ∧ δ < |x n - x a|)
    (fun h => ((Nat.find h : ℕ) : ℕ∞)) (fun _ => ⊤) = _
  rw [dif_pos h]

private lemma nextJump_eq_top {x : ℕ → ℝ} {δ : ℝ} {a : ℕ}
    (h : ¬ ∃ n : ℕ, a < n ∧ δ < |x n - x a|) :
    nextJump x δ a = ⊤ := by
  classical
  show dite (∃ n : ℕ, a < n ∧ δ < |x n - x a|)
    (fun h => ((Nat.find h : ℕ) : ℕ∞)) (fun _ => ⊤) = _
  rw [dif_neg h]

/-- `nextJump x δ a` is either `⊤` or some `n > a`, so it always lies at least at `a`. -/
private lemma coe_le_nextJump (x : ℕ → ℝ) (δ : ℝ) (a : ℕ) :
    ((a : ℕ) : ℕ∞) ≤ nextJump x δ a := by
  classical
  by_cases h : ∃ n : ℕ, a < n ∧ δ < |x n - x a|
  · rw [nextJump_eq_find h, ENat.natCast_le_natCast]
    exact Nat.le_of_lt (Nat.find_spec h).1
  · rw [nextJump_eq_top h]
    exact le_top

/-! ## Monotonicity of the greedy chain -/

private lemma greedyTime_succ_eq (x : ℕ → ℝ) (δ : ℝ) (k : ℕ) :
    greedyTime x δ (k + 1) =
      (if greedyTime x δ k < ⊤ then nextJump x δ ((greedyTime x δ k).toNat) else ⊤) := rfl

/-- The greedy chain is nondecreasing: `t k ≤ t (k+1)`. -/
private lemma greedyTime_le_succ (x : ℕ → ℝ) (δ : ℝ) (k : ℕ) :
    greedyTime x δ k ≤ greedyTime x δ (k + 1) := by
  rw [greedyTime_succ_eq]
  by_cases h : greedyTime x δ k < ⊤
  · have hcoe : (((greedyTime x δ k).toNat : ℕ) : ℕ∞) = greedyTime x δ k :=
      ENat.natCast_toNat (ne_of_lt h)
    rw [if_pos h, ← hcoe]
    exact coe_le_nextJump x δ _
  · rw [if_neg h]
    exact le_top

theorem greedyTime_mono (x : ℕ → ℝ) (δ : ℝ) : Monotone (greedyTime x δ) := by
  exact monotone_nat_of_le_succ (greedyTime_le_succ x δ)

end Work.Analysis.Probability
