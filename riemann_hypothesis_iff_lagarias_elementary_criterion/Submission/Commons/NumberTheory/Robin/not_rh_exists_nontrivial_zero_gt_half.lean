import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

namespace Commons.NumberTheory.Robin

/-- If `s` is a nontrivial zero of the Riemann zeta function and `s ≠ 1`, then its symmetric
point `1 - s` is also a zero. This uses the completed functional equation, so it avoids the
explicit non-vanishing hypotheses on the gamma factor that appear in `riemannZeta_one_sub`. -/
lemma riemannZeta_zero_of_one_sub {s : ℂ} (hz : riemannZeta s = 0) (hs1 : s ≠ 1)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1)) :
    riemannZeta (1 - s) = 0 := by
  have hs0 : s ≠ 0 := by
    intro hs0
    rw [hs0, riemannZeta_zero] at hz
    norm_num at hz
  have hΓs : Gammaℝ s ≠ 0 := by
    intro hΓ
    rw [Gammaℝ_eq_zero_iff] at hΓ
    rcases hΓ with ⟨n, hn⟩
    rcases n with _ | k
    · simp at hn
      exact hs0 hn
    · refine htriv ⟨k, ?_⟩
      simpa [Nat.cast_succ, mul_add, two_mul, add_comm, add_left_comm, add_assoc] using hn
  have hquot : completedRiemannZeta s / Gammaℝ s = 0 := by
    rw [← riemannZeta_def_of_ne_zero hs0, hz]
  have hΛ : completedRiemannZeta s = 0 := by
    have := congrArg (fun x : ℂ => x * Gammaℝ s) hquot
    rwa [zero_mul, div_mul_cancel₀ _ hΓs] at this
  have h1s : 1 - s ≠ 0 := by
    intro h
    exact hs1 (sub_eq_zero.mp h).symm
  rw [riemannZeta_def_of_ne_zero h1s, completedRiemannZeta_one_sub, hΛ, zero_div]

/-- Negating the definition of the Riemann hypothesis gives a nontrivial zero which is not on the
critical line. -/
lemma exists_nontrivial_zero_ne_half_of_not_rh (h : ¬ RiemannHypothesis) :
    ∃ s : ℂ, riemannZeta s = 0 ∧ (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1 ∧ s.re ≠ 1 / 2 := by
  by_contra hc
  apply h
  intro s hz htriv hs1
  by_contra hne
  exact hc ⟨s, hz, htriv, hs1, hne⟩

theorem not_rh_exists_nontrivial_zero_gt_half (h : ¬ RiemannHypothesis) :
    ∃ s : ℂ, riemannZeta s = 0 ∧ 1 / 2 < s.re ∧ s.re < 1 ∧
      (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1 := by
  rcases exists_nontrivial_zero_ne_half_of_not_rh h with ⟨s, hz, htriv, hs1, hne⟩
  have hs_lt_one : s.re < 1 := by
    by_contra hnot
    have hle : 1 ≤ s.re := le_of_not_gt hnot
    exact (riemannZeta_ne_zero_of_one_le_re hle) hz
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨1 - s, ?_, ?_, ?_, ?_, ?_⟩
    · exact riemannZeta_zero_of_one_sub hz hs1 htriv
    · have : (1 - s).re = 1 - s.re := by simp
      rw [this]
      linarith
    · have hz' : riemannZeta (1 - s) = 0 := riemannZeta_zero_of_one_sub hz hs1 htriv
      by_contra hnot
      have hle : 1 ≤ (1 - s).re := le_of_not_gt hnot
      exact (riemannZeta_ne_zero_of_one_le_re hle) hz'
    · intro htriv'
      rcases htriv' with ⟨n, hn⟩
      have hs_eq : s = 1 + 2 * (n + 1 : ℂ) := by
        calc
          s = 1 - (1 - s) := by ring
          _ = 1 - (-2 * (n + 1 : ℂ)) := by rw [hn]
          _ = 1 + 2 * (n + 1 : ℂ) := by ring
      have hs_re : s.re = 1 + 2 * (n + 1 : ℝ) := by
        rw [hs_eq]
        norm_num
      have hnonneg : 0 ≤ (n + 1 : ℝ) := by positivity
      nlinarith
    · intro ht1
      have hs0 : s = 0 := by
        calc
          s = 1 - (1 - s) := by ring
          _ = 1 - 1 := by rw [ht1]
          _ = 0 := by ring
      rw [hs0, riemannZeta_zero] at hz
      norm_num at hz
  · exact ⟨s, hz, hgt, hs_lt_one, htriv, hs1⟩

end Commons.NumberTheory.Robin