import Mathlib
import Submission.Work.ChenPlan.LinearSieve.basic

/-!
# `1 ≤ Utab s` for `s > 0`

The upper envelope `Submission.ChenPlan.Utab` is built from two pieces:
* for `s < 3/2`, the Selberg/Rosser–Iwaniec value `(1005/1000) * 2 * e^γ / s`, which is `≥ 1`
  on `(0, 3/2)` because `e^γ > 1` and `(1005/1000) * 2 ≥ 3/2`;
* for `s ≥ 3/2`, a table entry, and every entry of `utabList` is `≥ 1008/1000 > 1`.

The table is a concrete `List ℚ`; the two small facts we need about it are that all its entries
are `≥ 1` (decidable, checked by `decide +kernel`) and that `List.getD` at an in-range index
returns an entry (and not the default), for which we use the `getD_one_le` induction.
-/

namespace Work.ChenPlan.LinearSieve.Utab

/-- Every entry of the table `utabList` is `≥ 1`. -/
lemma one_le_utabList : ∀ x ∈ Submission.ChenPlan.utabList, (1 : ℚ) ≤ x := by
  decide +kernel

/-- `List.getD` at an in-range index is an entry of the list, hence `≥ 1` (the default value,
which is not assumed to be `≥ 1`, is only reached out of range). -/
lemma getD_one_le {d : ℚ} :
    ∀ (l : List ℚ), (∀ x ∈ l, 1 ≤ x) → ∀ n, n < l.length → 1 ≤ l.getD n d := by
  intro l
  induction l with
  | nil => intro _ n hn; simp at hn
  | cons a t ih =>
    intro h n hn
    cases n with
    | zero => simpa using h a (by simp)
    | succ k =>
      have hk : k < t.length := by simp at hn; omega
      exact ih (fun x hx => h x (by simp [hx])) k hk

theorem one_le_Utab {s : ℝ} (hs : 0 < s) : 1 ≤ Submission.ChenPlan.Utab s := by
  rw [Submission.ChenPlan.Utab]
  split_ifs with h
  · -- `s < 3/2`: the Selberg value `(1005/1000) * 2 * e^γ / s`
    have hexp : (1 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant :=
      Real.one_le_exp (by linarith [Real.one_half_lt_eulerMascheroniConstant])
    rw [le_div_iff₀ hs]
    nlinarith [hexp]
  · -- `s ≥ 3/2`: a table value, and all table values are `≥ 1`
    have hlen : min (⌊(s - 3 / 2) * 20⌋₊) 70 < Submission.ChenPlan.utabList.length := by
      simp [Submission.ChenPlan.utabList]
    have hget : (1 : ℚ) ≤ Submission.ChenPlan.utabList.getD (min (⌊(s - 3 / 2) * 20⌋₊) 70) 0 :=
      getD_one_le _ one_le_utabList _ hlen
    exact_mod_cast hget

end Work.ChenPlan.LinearSieve.Utab
