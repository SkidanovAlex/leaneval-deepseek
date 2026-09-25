import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace Commons.NumberTheory.Zeta

/-- The completed Riemann zeta function does not vanish on the half-plane `1 < re s`:
near the pole at `s = 1` it equals `π ^ (-s/2) * Γ (s/2) * ζ s`, where `ζ` is nonvanishing
and the gamma factor has no zeros or poles. We avoid the gamma factor entirely by using
`riemannZeta s = completedRiemannZeta s / Gammaℝ s` together with `riemannZeta_ne_zero_of_one_le_re`. -/
lemma completedRiemannZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  intro h
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  have hz : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
  exact riemannZeta_ne_zero_of_one_le_re (le_of_lt hs) hz

/-- If the completed Riemann zeta function vanishes at `u`, then `u` is either `0`, `1`, or a
nontrivial zero of `riemannZeta`: the negative even integers (the trivial zeros of `ζ`) are not
zeros of `Λ`, since `Λ (-2 * (n+1)) = Λ (2 * (n+1) + 3)` and `Λ` is nonvanishing on `re > 1`. -/
lemma not_trivial_zero_of_completedRiemannZeta_zero {u : ℂ}
    (hu : completedRiemannZeta u = 0) : ¬ ∃ n : ℕ, u = -2 * (n + 1) := by
  rintro ⟨n, hn⟩
  have h1u : completedRiemannZeta (1 - u) ≠ 0 := by
    apply completedRiemannZeta_ne_zero_of_one_lt_re
    have hcast : (1 : ℂ) - u = ((2 * (n : ℝ) + 3 : ℝ) : ℂ) := by
      rw [hn]
      push_cast
      ring
    rw [hcast, Complex.ofReal_re]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [completedRiemannZeta_one_sub, hu] at h1u
  exact h1u rfl

theorem completedRiemannZeta_zero_re_eq_half (h : RiemannHypothesis) {u : ℂ}
    (hu : completedRiemannZeta u = 0) (h0 : u ≠ 0) (h1 : u ≠ 1) : u.re = 1 / 2 := by
  have hzu : riemannZeta u = 0 := by
    rw [riemannZeta_def_of_ne_zero h0, hu, zero_div]
  exact h u hzu (not_trivial_zero_of_completedRiemannZeta_zero hu) h1

end Commons.NumberTheory.Zeta