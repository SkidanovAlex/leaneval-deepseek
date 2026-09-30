import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The upper bound `‖L(s, χ)‖ ≤ ζ(Re s)` for `Re s > 1`

For a Dirichlet character `χ` modulo `N` and a complex number `s` in the half-plane of absolute
convergence `1 < Re s`, the Dirichlet `L`-function is dominated by the Riemann zeta function
evaluated at the real part:

  `‖L(s, χ)‖ ≤ ζ(Re s)`,

where `ζ(Re s)` is written as `(riemannZeta (Re s)).re` (the Riemann zeta function is real on
the real axis).

The proof is the elementary comparison of the two absolutely convergent Dirichlet series
`L(s, χ) = ∑_n χ(n) n^{-s}` and `ζ(σ) = ∑_n n^{-σ}`: term by term `‖χ(n) n^{-s}‖ ≤ n^{-σ}`
because `‖χ(n)‖ ≤ 1`, and the Dirichlet series of `ζ(σ)` is a series of nonnegative real
numbers, so that its sum coincides with its real part.
-/

namespace Work.BMF

/-- The `n`-th term of the `L`-series of the constant sequence `1` at a real point `σ` is a
nonnegative real number, whence its norm equals its real part. -/
private lemma norm_term_one_eq_re (σ : ℝ) (n : ℕ) :
    ‖LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n‖ = (LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    simp [LSeries.term_def]
  · rw [LSeries.norm_term_eq, LSeries.term_of_ne_zero hn, ite_eq_right hn]
    simp only [Pi.one_apply, norm_one, Complex.ofReal_re]
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n) σ]
    simp only [one_div, ← Complex.ofReal_inv, Complex.ofReal_re]

/-- The sum of the norms of the terms of the `L`-series of the constant sequence `1` at a real
point `σ > 1` is the Riemann zeta function at `σ`. -/
private lemma tsum_norm_term_one (σ : ℝ) (hσ : 1 < σ) :
    ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n‖ = (riemannZeta (σ : ℂ)).re := by
  rw [tsum_congr (fun n => norm_term_one_eq_re σ n)]
  rw [← Complex.re_tsum (LSeriesSummable_one_iff.mpr (by simpa using hσ))]
  exact congrArg Complex.re (LSeries_one_eq_riemannZeta (s := (σ : ℂ)) hσ)

theorem vk_L_upper {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (riemannZeta (s.re : ℂ)).re := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hs' : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
  have hsum1 : Summable (LSeries.term (1 : ℕ → ℂ) ((s.re : ℝ) : ℂ)) :=
    LSeriesSummable_one_iff.mpr hs'
  have hle : ∀ n : ℕ,
      ‖LSeries.term (fun k => χ (k : ZMod N)) s n‖
        ≤ ‖LSeries.term (1 : ℕ → ℂ) ((s.re : ℝ) : ℂ) n‖ := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [LSeries.norm_term_eq, ite_eq_right hn, Complex.ofReal_re,
        Pi.one_apply, norm_one]
      exact div_le_div_of_nonneg_right
        (by simpa using DirichletCharacter.norm_le_one χ (n : ZMod N))
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hsumχ : Summable (LSeries.term (fun k => χ (k : ZMod N)) s) :=
    Summable.of_norm_bounded hsum1.norm hle
  calc ‖LSeries (fun k => χ (k : ZMod N)) s‖
      = ‖∑' n, LSeries.term (fun k => χ (k : ZMod N)) s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term (fun k => χ (k : ZMod N)) s n‖ :=
        norm_tsum_le_tsum_norm hsumχ.norm
    _ ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) ((s.re : ℝ) : ℂ) n‖ :=
        Summable.tsum_le_tsum hle hsumχ.norm hsum1.norm
    _ = (riemannZeta (s.re : ℂ)).re := tsum_norm_term_one s.re hs

end Work.BMF

