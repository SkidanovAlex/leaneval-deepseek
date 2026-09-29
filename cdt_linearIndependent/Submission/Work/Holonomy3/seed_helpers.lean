import Mathlib
import Submission.CDT.Discrepancy

/-!
# Helper lemmas for the "seed sum estimate"

Small, fully proved facts shared by the pieces of `Submission.Work.Holonomy3.seed_sum_estimate`
(the paper's `(seed sum est)` of the "Seeding" step of the fine holonomy bound):

* `cnt_zero_eq_card_filter_lt` — the half-open count `cnt t 0 u` is the number of points `t j < u`;
* `abs_cnt_sub_le` — the count form of the box discrepancy: `disc t ≤ ε` implies
  `|cnt t 0 u - N·u| ≤ N·ε` for `0 ≤ u ≤ 1`;
* `sum_Fin_cast_div` — the exact total `∑_{j : Fin d} j/d = (d-1)/2`.
-/

namespace Work.Holonomy3

open Submission.CDT.Discrepancy

/-- The half-open count `cnt t 0 u` is the number of points `t j < u`, when all `t j ≥ 0`. -/
lemma cnt_zero_eq_card_filter_lt {N : ℕ} {t : Fin N → ℝ} (ht : ∀ j, 0 ≤ t j) (u : ℝ) :
    cnt t 0 u = (Finset.univ.filter (fun j : Fin N => t j < u)).card := by
  unfold cnt
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico]
  exact ⟨fun h => h.2, fun h => ⟨ht j, h⟩⟩

/-- **The count form of the box discrepancy.**  If `disc t ≤ ε` then for every `0 ≤ u ≤ 1` the
number of points of `t` in `[0,u)` differs from `N·u` by at most `N·ε`. -/
lemma abs_cnt_sub_le {N : ℕ} (t : Fin N → ℝ) {ε u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1)
    (h : disc t ≤ ε) : |(cnt t 0 u : ℝ) - (N:ℝ) * u| ≤ (N:ℝ) * ε := by
  have key : |u - (cnt t 0 u : ℝ) / (N:ℝ)| ≤ ε := by
    have hmem : |u - (cnt t 0 u : ℝ) / (N:ℝ)| ∈
        (fun p : ℝ × ℝ => |(p.2 - p.1) - (cnt t p.1 p.2 : ℝ) / (N:ℝ)|) ''
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} :=
      ⟨(0, u), ⟨le_rfl, h0, h1⟩, by simp⟩
    calc |u - (cnt t 0 u : ℝ) / (N:ℝ)| ≤ disc t := by
          rw [disc]; exact le_csSup (disc_bddAbove t) hmem
      _ ≤ ε := h
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [cnt]
  · have hN' : (N:ℝ) ≠ 0 := by positivity
    have h1' : (N:ℝ) * (u - (cnt t 0 u : ℝ)/N) = (N:ℝ) * u - (cnt t 0 u : ℝ) := by
      rw [mul_sub, mul_div_cancel₀ _ hN']
    have h2 : (N:ℝ) * |u - (cnt t 0 u : ℝ) / (N:ℝ)| = |(N:ℝ) * u - (cnt t 0 u : ℝ)| := by
      rw [← h1', abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ))]
    calc |(cnt t 0 u : ℝ) - (N:ℝ) * u| = |(N:ℝ) * u - (cnt t 0 u : ℝ)| := by rw [abs_sub_comm]
      _ = (N:ℝ) * |u - (cnt t 0 u : ℝ)/(N:ℝ)| := h2.symm
      _ ≤ (N:ℝ) * ε := mul_le_mul_of_nonneg_left key (by positivity)

/-- The exact total `∑_{j : Fin d} j/d = (d-1)/2`. -/
lemma sum_Fin_cast_div {d : ℕ} (hd : 0 < d) :
    (∑ j : Fin d, (j:ℝ)/(d:ℝ)) = ((d:ℝ)-1)/2 := by
  have hrange : (∑ j : Fin d, (j:ℝ)) = (∑ i ∈ Finset.range d, (i:ℝ)) := by
    rw [Fin.sum_univ_eq_sum_range]
  have hgauss : (∑ i ∈ Finset.range d, (i:ℝ)) * 2 = (d:ℝ) * ((d:ℝ) - 1) := by
    have h2 := congrArg (fun n : ℕ => (n:ℝ)) (Finset.sum_range_id_mul_two d)
    push_cast at h2
    rw [Nat.cast_sub (show 1 ≤ d by omega)] at h2
    simp only [Nat.cast_one] at h2
    exact h2
  have hsum : (∑ i ∈ Finset.range d, (i:ℝ)) = (d:ℝ) * ((d:ℝ) - 1) / 2 := by linarith
  rw [← Finset.sum_div, hrange, hsum]
  field_simp

end Work.Holonomy3
