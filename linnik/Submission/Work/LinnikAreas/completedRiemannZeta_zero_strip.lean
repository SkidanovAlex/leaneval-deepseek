import Mathlib

namespace Work.LinnikAreas

/-- The completed Riemann zeta function `Λ` does not vanish in the closed half-plane
`re ρ ≥ 1`: there `Λ ρ = ζ ρ / Gammaℝ ρ` and `ζ` is zero-free.

Concretely, if `Λ ρ = 0` then `ρ.re < 1`. -/
theorem re_lt_one_of_completedRiemannZeta_eq_zero {ρ : ℂ}
    (hρ : completedRiemannZeta ρ = 0) : ρ.re < 1 := by
  by_contra h
  replace h : 1 ≤ ρ.re := not_lt.mp h
  -- `Λ ρ = ζ ρ / Gammaℝ ρ`, so `Λ ρ = 0` forces `ζ ρ = 0`, which is impossible for `ρ.re ≥ 1`.
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    simp only [Complex.zero_re] at h
    exact absurd h (by norm_num)
  have hz : riemannZeta ρ = 0 := by
    rw [riemannZeta_def_of_ne_zero hρ0, hρ, zero_div]
  exact riemannZeta_ne_zero_of_one_le_re h hz

/-- The completed Riemann zeta function `Λ` does not vanish in the closed half-plane
`re ρ ≤ 0`: the functional equation `Λ (1 - ρ) = Λ ρ` transports such a zero to a zero
with real part `≥ 1`, where `re_lt_one_of_completedRiemannZeta_eq_zero` forbids it. -/
theorem zero_lt_re_of_completedRiemannZeta_eq_zero {ρ : ℂ}
    (hρ : completedRiemannZeta ρ = 0) : 0 < ρ.re := by
  by_contra h
  replace h : ρ.re ≤ 0 := not_lt.mp h
  have h2 : completedRiemannZeta (1 - ρ) = 0 := by
    rw [completedRiemannZeta_one_sub, hρ]
  have h3 : (1 - ρ).re < 1 := re_lt_one_of_completedRiemannZeta_eq_zero h2
  simp only [Complex.sub_re, Complex.one_re] at h3
  linarith

/-- **The zeros of the completed Riemann zeta function lie in the critical strip**:
if `Λ ρ = 0` then `0 < re ρ < 1`. -/
theorem completedRiemannZeta_zero_strip {ρ : ℂ} (hρ : completedRiemannZeta ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 :=
  ⟨zero_lt_re_of_completedRiemannZeta_eq_zero hρ,
    re_lt_one_of_completedRiemannZeta_eq_zero hρ⟩

end Work.LinnikAreas
