import Mathlib

namespace Work.LinnikAreas.Zeta1Aux

/-- `ζ₁` and `ζ` have the same zeros away from `s = 1`, and `ζ₁ 1 = 1 ≠ 0`. -/
lemma riemannZeta_eq_zero_of_riemannZeta₁_eq_zero {ρ : ℂ} (hρ : riemannZeta₁ ρ = 0) :
    riemannZeta ρ = 0 := by
  have hρne1 : ρ ≠ 1 := by
    intro h
    rw [h, riemannZeta₁_one] at hρ
    exact one_ne_zero hρ
  rw [riemannZeta_eq_inv_sub_mul hρne1, hρ, mul_zero]

/-- If `cos (π s / 2) = 0` then `s` is a real (half-)integer; in particular `s.im = 0`. -/
lemma im_eq_zero_of_cos_pi_mul_div_two_eq_zero {s : ℂ}
    (h : Complex.cos ((Real.pi : ℂ) * s / 2) = 0) : s.im = 0 := by
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
  have hk1 : (Real.pi : ℂ) * s / 2 = (2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2 := by
    simpa using hk
  have hk' : ((Real.pi : ℂ) / 2) * s = ((Real.pi : ℂ) / 2) * (2 * (k : ℂ) + 1) := by
    linear_combination hk1
  have hp : ((Real.pi : ℂ) / 2) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) two_ne_zero
  have hseq := mul_left_cancel₀ hp hk'
  rw [hseq]
  simp

/-- **Zeros of `riemannZeta₁` off the real axis lie in the critical strip.**

`riemannZeta₁ s = (s-1)·ζ(s)` away from `s = 1`, and `ζ₁ 1 = 1`, hence the zeros of `ζ₁`
are exactly the zeros of `ζ`.  For a zero `ρ` with `ρ.im ≠ 0` we prove `0 < ρ.re < 1`:

* `ρ.re < 1`: otherwise `1 ≤ ρ.re`, contradicting Mathlib's `riemannZeta_ne_zero_of_one_le_re`
  (a zero of `ζ₁` is a zero of `ζ` because `ζ₁ 1 = 1 ≠ 0`).
* `0 < ρ.re`: otherwise `Re (1 - ρ) ≥ 1`, and the functional equation `riemannZeta_one_sub`
  at `s = 1 - ρ` (legitimate: `s ≠ 1` since `ζ 0 = -1/2 ≠ 0`, and `s ≠ -n` for `n : ℕ` since
  `Re s ≥ 1 > 0`) gives
  `0 = ζ (1 - s) = 2 * (2π)^{-s} * Γ s * cos (π s / 2) * ζ s`.
  All factors except `cos (π s / 2)` are non-zero (`Re s ≥ 1`), so `cos (π s / 2) = 0`, i.e.
  `s = 1 + 2k` for some `k : ℤ`; then `Re s ≥ 1` forces `k ≥ 0` and `ρ = 1 - s = -2k` is real,
  contradicting `ρ.im ≠ 0`. -/
theorem zeta1_zero_strip {ρ : ℂ} (hρ : riemannZeta₁ ρ = 0) (him : ρ.im ≠ 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  have hζρ : riemannZeta ρ = 0 := riemannZeta_eq_zero_of_riemannZeta₁_eq_zero hρ
  have hlt : ρ.re < 1 := by
    by_contra h
    simp only [not_lt] at h
    exact riemannZeta_ne_zero_of_one_le_re h hζρ
  refine ⟨?_, hlt⟩
  by_contra hle
  simp only [not_lt] at hle
  -- reflect about the critical line: `s = 1 - ρ` has `Re s ≥ 1`
  set s : ℂ := 1 - ρ with hs
  have hre : 1 ≤ s.re := by
    rw [hs]
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have h1s : 1 - s = ρ := by rw [hs]; ring
  have hs1 : s ≠ 1 := by
    intro h
    have hρ0 : ρ = 0 := by
      have h1 : (1 : ℂ) - ρ = 1 := by rw [← hs]; exact h
      linear_combination -h1
    exact him (by rw [hρ0]; simp)
  have hsn : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hn
    have h1 : s.re = -(n : ℝ) := by rw [hn]; simp
    linarith
  -- the functional equation at `s`
  have hFE := riemannZeta_one_sub hsn hs1
  -- hence `cos (π s / 2) = 0`
  have hcos0 : Complex.cos ((Real.pi : ℂ) * s / 2) = 0 := by
    have h0 : 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
        Complex.cos ((Real.pi : ℂ) * s / 2) * riemannZeta s = 0 := by
      rw [← hFE, h1s, hζρ]
    have hζs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre
    have h0' : 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
        Complex.cos ((Real.pi : ℂ) * s / 2) = 0 := (mul_eq_zero.mp h0).resolve_right hζs
    have hcp : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff]
      exact Or.inl (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hgam : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    exact (mul_eq_zero.mp h0').resolve_left
      (mul_ne_zero (mul_ne_zero two_ne_zero hcp) hgam)
  -- `s` is a real integer, so `ρ = 1 - s` is real, contradiction
  have hρim : ρ.im = 0 := by
    have h0 := im_eq_zero_of_cos_pi_mul_div_two_eq_zero hcos0
    rw [← h1s]
    simp [h0]
  exact him hρim

end Work.LinnikAreas.Zeta1Aux
