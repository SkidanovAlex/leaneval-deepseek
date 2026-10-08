import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.pLength_spec`

The upper `p`-series of a `p`-solvable finite group reaches `⊤` and then stays there, so the
"`p`-length" `pLength p G` — half the minimal index at which the series reaches `⊤` — really
bounds the index: the series is already `⊤` at stage `2 * pLength p G + 1`.

The mathematical content is twofold:

* the series is increasing (`pCoreSeries p G n ≤ pCoreSeries p G (n+1)`), so once it hits `⊤`
  it remains `⊤` forever; this is what `2 * pLength + 1` buys us;
* `pLength p G = Nat.find h.out / 2` and `n ≤ 2 * (n / 2) + 1`, so the chosen index is at
  least `Nat.find h.out`, the first stage at which the series is `⊤`.
-/

noncomputable section

open Classical

namespace Work.Fitting

/-- Once the upper `p`-series of `G` reaches `⊤` at stage `n`, it stays `⊤` at stage `n + 1`:
the next term contains the previous one, and the previous one was all of `G`. -/
theorem pCoreSeries_succ_eq_top_of_eq_top (p : ℕ) (G : Type*) [Group G] (n : ℕ)
    (h : Work.Fitting.pCoreSeries p G n = ⊤) :
    Work.Fitting.pCoreSeries p G (n + 1) = ⊤ := by
  have hle : Work.Fitting.pCoreSeries p G n ≤ Work.Fitting.pCoreSeries p G (n + 1) := by
    rw [Work.Fitting.pCoreSeries_succ]
    intro x hx
    rw [Subgroup.mem_comap]
    have h1 : QuotientGroup.mk' (Work.Fitting.pCoreSeries p G n) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact Subgroup.one_mem _
  rw [h] at hle
  exact top_le_iff.mp hle

/-- Once the upper `p`-series of `G` reaches `⊤`, it is `⊤` at every larger index. -/
theorem pCoreSeries_eq_top_of_le (p : ℕ) (G : Type*) [Group G] {n m : ℕ}
    (hn : Work.Fitting.pCoreSeries p G n = ⊤) (hm : n ≤ m) :
    Work.Fitting.pCoreSeries p G m = ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => simpa using hn
  | succ k ih =>
      rw [Nat.add_succ]
      exact pCoreSeries_succ_eq_top_of_eq_top p G (n + k) (ih (Nat.le_add_right n k))

theorem pLength_spec (p : ℕ) (G : Type*) [Group G] [Finite G] (h : Work.Fitting.IsPSolvable p G) :
    Work.Fitting.pCoreSeries p G (2 * Work.Fitting.pLength p G + 1) = ⊤ := by
  have hspec : Work.Fitting.pCoreSeries p G (Nat.find h.out) = ⊤ := Nat.find_spec h.out
  have hpL : Work.Fitting.pLength p G = Nat.find h.out / 2 := by
    unfold Work.Fitting.pLength
    rw [dite_eq_left h]
  rw [hpL]
  exact pCoreSeries_eq_top_of_le p G hspec (by omega)

end Work.Fitting
