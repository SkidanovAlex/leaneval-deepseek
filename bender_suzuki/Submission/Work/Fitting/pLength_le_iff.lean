import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.pLength_le_iff`

The `p`-length of a finite `p`-solvable group is half the least index `m` at which the
upper `p`-series `1 ≤ O_{p'}(G) ≤ O_{p',p}(G) ≤ O_{p',p,p'}(G) ≤ ...` reaches `G`
(`pLength p G = Nat.find h.out / 2`), and the series is increasing.  Consequently

`pLength p G ≤ n ↔ pCoreSeries p G (2 * n + 1) = ⊤`.

* `→`: from `m / 2 ≤ n` we get `m ≤ 2 * n + 1`, and the series, being `⊤` at `m`
  (`Nat.find_spec`), stays `⊤` at any later index (monotonicity).
* `←`: if the series is `⊤` at `2 * n + 1` then the least such index satisfies
  `m ≤ 2 * n + 1` (`Nat.find_min'`), hence `m / 2 ≤ n`.

The only arithmetic ingredient is `m / 2 ≤ n ↔ m ≤ 2 * n + 1` for `m n : ℕ`.
-/

noncomputable section

open Classical

namespace Work.Fitting

/-- Each term of the upper `p`-series is contained in the next one. -/
private theorem pCoreSeries_le_succ' (p : ℕ) (G : Type*) [Group G] (n : ℕ) :
    Work.Fitting.pCoreSeries p G n ≤ Work.Fitting.pCoreSeries p G (n + 1) := by
  rw [Work.Fitting.pCoreSeries_succ]
  intro x hx
  rw [Subgroup.mem_comap]
  have h1 : QuotientGroup.mk' (Work.Fitting.pCoreSeries p G n) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx
  rw [h1]
  exact Subgroup.one_mem _

/-- The upper `p`-series is increasing. -/
private theorem pCoreSeries_mono' (p : ℕ) (G : Type*) [Group G] {n m : ℕ} (h : n ≤ m) :
    Work.Fitting.pCoreSeries p G n ≤ Work.Fitting.pCoreSeries p G m :=
  monotone_nat_of_le_succ (fun i => pCoreSeries_le_succ' p G i) h

/-- Once the upper `p`-series is `⊤` at some index, it is `⊤` at every larger index. -/
private theorem pCoreSeries_eq_top_of_le' (p : ℕ) (G : Type*) [Group G] {n m : ℕ}
    (hn : Work.Fitting.pCoreSeries p G n = ⊤) (hm : n ≤ m) :
    Work.Fitting.pCoreSeries p G m = ⊤ := by
  have h := pCoreSeries_mono' p G hm
  rw [hn] at h
  exact top_le_iff.mp h

theorem pLength_le_iff (p : ℕ) (G : Type*) [Group G] [Finite G]
    (h : Work.Fitting.IsPSolvable p G) (n : ℕ) :
    Work.Fitting.pLength p G ≤ n ↔ Work.Fitting.pCoreSeries p G (2 * n + 1) = ⊤ := by
  have hpL : Work.Fitting.pLength p G = Nat.find h.out / 2 := by
    unfold Work.Fitting.pLength
    rw [dite_eq_left h]
  have hfind : ∀ m : ℕ, Work.Fitting.pCoreSeries p G m = ⊤ ↔ Nat.find h.out ≤ m :=
    fun m => ⟨fun hm => Nat.find_min' h.out hm,
      fun hm => pCoreSeries_eq_top_of_le' p G (Nat.find_spec h.out) hm⟩
  rw [hpL, hfind (2 * n + 1)]
  omega

end Work.Fitting
