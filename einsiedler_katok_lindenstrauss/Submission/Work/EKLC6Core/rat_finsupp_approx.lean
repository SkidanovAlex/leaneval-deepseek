import Mathlib

namespace Work.EKLC6Core

/-- For any real number `x` and `ε > 0` there is a rational `r` with `|x - r| < ε`. -/
lemma exists_rat_abs_sub_lt (x : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ r : ℚ, |x - (r : ℝ)| < ε :=
  exists_rat_near x hε

theorem rat_finsupp_approx (ι : Finset ℕ) (c : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ) : ∃ q : ℕ →₀ ℚ, q.support ⊆ ι ∧ ∑ n ∈ ι, |c n - (q n : ℝ)| < δ := by
  classical
  rcases ι.eq_empty_or_nonempty with h | h
  · refine ⟨0, ?_, ?_⟩
    · rw [h]; simp
    · rw [h]; simp only [Finset.sum_empty]; exact hδ
  · set k : ℕ := ι.card with hk
    set ε : ℝ := δ / ((k : ℝ) + 1) with hεdef
    have hε : 0 < ε := by rw [hεdef]; exact div_pos hδ (by positivity)
    choose f hf using fun n => exists_rat_abs_sub_lt (c n) hε
    set g : ℕ → ℚ := fun n => if n ∈ ι then f n else 0 with hgdef
    have hg : ∀ n, g n ≠ 0 → n ∈ ι := by
      intro n hn; by_contra h'; simp [hgdef, h'] at hn
    refine ⟨Finsupp.onFinset ι g hg, Finsupp.support_onFinset_subset, ?_⟩
    have hterm : ∀ n ∈ ι, |c n - ((Finsupp.onFinset ι g hg) n : ℝ)| < ε := by
      intro n hn
      rw [Finsupp.onFinset_apply]
      have hgn : g n = f n := by simp [hgdef, hn]
      rw [hgn]; exact hf n
    have hk1 : (k : ℝ) / ((k : ℝ) + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    calc ∑ n ∈ ι, |c n - ((Finsupp.onFinset ι g hg) n : ℝ)|
        < ∑ _n ∈ ι, ε := Finset.sum_lt_sum_of_nonempty h hterm
      _ = (k : ℝ) * ε := by rw [hk, Finset.sum_const, nsmul_eq_mul]
      _ = δ * ((k : ℝ) / ((k : ℝ) + 1)) := by
            rw [hεdef]; ring
      _ < δ * 1 := mul_lt_mul_of_pos_left hk1 hδ
      _ = δ := by ring

end Work.EKLC6Core
