import Mathlib
import Submission.Work.Holonomy3.defs

namespace Work.Holonomy3

open Submission.CDT.Discrepancy

/-- The discrepancy objective at a valid interval `[a,b) ⊆ [0,1]` is at most `disc t`. -/
lemma abs_sub_cnt_div_le_disc (ε : ℝ) {n : ℕ} (t : Fin n → ℝ)
    (h : disc t ≤ ε) {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (h1 : b ≤ 1) :
    |(b - a) - (cnt t a b : ℝ) / (n : ℝ)| ≤ ε := by
  have hmem : |(b - a) - (cnt t a b : ℝ) / (n : ℝ)| ∈
      (fun p : ℝ × ℝ => |(p.2 - p.1) - (cnt t p.1 p.2 : ℝ) / (n : ℝ)|) ''
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} :=
    ⟨(a, b), ⟨h0, hab, h1⟩, rfl⟩
  have hle : |(b - a) - (cnt t a b : ℝ) / (n : ℝ)| ≤ disc t := by
    rw [disc]
    exact le_csSup (disc_bddAbove t) hmem
  linarith

/-- The points in `[0,s)` form a subset of the points `≤ s`. -/
lemma cnt_zero_le_count {n : ℕ} (t : Fin n → ℝ) (s : ℝ) :
    cnt t 0 s ≤ (Finset.univ.filter (fun j : Fin n => t j ≤ s)).card := by
  unfold cnt
  refine Finset.card_le_card ?_
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico] at hj ⊢
  exact le_of_lt hj.2

/-- The points `≤ s` form a subset of the points in `[0,b)` for any `b > s`. -/
lemma count_le_cnt_zero {n : ℕ} (t : Fin n → ℝ) (ht : ∀ j, t j ∈ Set.Ico 0 1)
    {s b : ℝ} (hsb : s < b) :
    (Finset.univ.filter (fun j : Fin n => t j ≤ s)).card ≤ cnt t 0 b := by
  unfold cnt
  refine Finset.card_le_card ?_
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico] at hj ⊢
  exact ⟨(ht j).1, lt_of_le_of_lt hj hsb⟩

/-- **The counting form of the box discrepancy.** If the box discrepancy of `t : Fin N → ℝ` (with
all `t j ∈ [0,1)`) is at most `ε`, then for every `i` the number of indices `j` with `t j ≤ t i`
differs from `N · t i` by at most `N ε + 1`. This is the "sorted rearrangement" estimate `(tru 2)`
of the paper. -/
theorem count_le_of_disc (ε : ℝ) (hε : 0 ≤ ε) {N : ℕ} (t : Fin N → ℝ)
    (ht : ∀ j, t j ∈ Set.Ico 0 1) (h : Submission.CDT.Discrepancy.disc t ≤ ε) (i : Fin N) :
    |((Finset.univ.filter (fun j : Fin N => t j ≤ t i)).card : ℝ) - (N : ℝ) * t i| ≤
      (N : ℝ) * ε + 1 := by
  obtain ⟨hs0, hs1⟩ := ht i
  have hN0 : (0:ℝ) < N := by exact_mod_cast (Fin.pos i)
  set c : ℕ := (Finset.univ.filter (fun j : Fin N => t j ≤ t i)).card with hc
  rw [abs_le]
  constructor
  · -- lower bound: the points in `[0, t i)` are counted by `disc`
    have hcs : cnt t 0 (t i) ≤ c := by rw [hc]; exact cnt_zero_le_count t (t i)
    have hcs' : (cnt t 0 (t i) : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcs
    have hb := abs_sub_cnt_div_le_disc ε t h (a := 0) (b := t i) le_rfl hs0 (le_of_lt hs1)
    have h2 : (cnt t 0 (t i) : ℝ) ≥ (N : ℝ) * t i - (N : ℝ) * ε := by
      have key : t i - (cnt t 0 (t i) : ℝ) / (N : ℝ) ≤ ε := by
        have h1 := (abs_le.mp hb).2; linarith
      have hkey : t i - ε ≤ (cnt t 0 (t i) : ℝ) / (N : ℝ) := by linarith
      have hk := (le_div_iff₀ hN0).mp hkey
      nlinarith [hk]
    have hNε : 0 ≤ (N:ℝ) * ε := mul_nonneg (le_of_lt hN0) hε
    linarith
  · -- upper bound: enlarge `[0, t i)` by a `δ` with `N δ ≤ 1` and `t i + δ ≤ 1`
    set δ : ℝ := min ((1 - t i)/2) (1/((N:ℝ)+1)) with hδ
    have hδpos : 0 < δ := by rw [hδ]; exact lt_min (by linarith) (by positivity)
    have hδle1 : δ ≤ 1 - t i := by
      have h1 := min_le_left ((1 - t i)/2) (1/((N:ℝ)+1))
      have h2 : 0 ≤ 1 - t i := by linarith
      linarith
    have hδle2 : δ ≤ 1/((N:ℝ)+1) := by rw [hδ]; exact min_le_right _ _
    have hNδ : (N:ℝ) * δ ≤ 1 := by
      have h1 : (N:ℝ) * δ ≤ (N:ℝ) * (1/((N:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left hδle2 (le_of_lt hN0)
      have h2 : (N:ℝ) * (1/((N:ℝ)+1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        linarith
      linarith
    have hbs : t i < t i + δ := by linarith
    have hb1 : t i + δ ≤ 1 := by linarith
    have hb := abs_sub_cnt_div_le_disc ε t h (a := 0) (b := t i + δ) le_rfl (by linarith) hb1
    have hkey : (cnt t 0 (t i + δ) : ℝ) ≤ (N:ℝ) * t i + (N:ℝ) * ε + 1 := by
      have key : (cnt t 0 (t i + δ) : ℝ) / (N:ℝ) ≤ t i + δ + ε := by
        have h1 := (abs_le.mp hb).1
        linarith
      have hk := (div_le_iff₀ hN0).mp key
      nlinarith [hk, hNδ]
    have hcs : c ≤ cnt t 0 (t i + δ) := by rw [hc]; exact count_le_cnt_zero t ht hbs
    have hcs' : (c:ℝ) ≤ (cnt t 0 (t i + δ) : ℝ) := by exact_mod_cast hcs
    linarith

end Work.Holonomy3
