import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.Alg.Q2PR.nondegen_key`

A purely algebraic identity on the complex plane: for complex numbers `p q r` with `‖p‖ ≠ ‖r‖`,
putting `s = star r * q + p * star q` and `d = ‖r‖² - ‖p‖²` (a nonzero real number), one has

`r * (s / d) - p * star (s / d) = q`.

The point is that the conjugate-linear part cancels: writing `d` for `‖r‖² - ‖p‖²`,

`r * (r̄ q + p q̄) - p * (r q̄ + p̄ q) = (r r̄ - p p̄) q = d q`,

because `r p q̄ = p r q̄` and `r r̄ = ‖r‖²`, `p p̄ = ‖p‖²`.
-/

namespace Work.Diff.Alg.Q2PR

theorem nondegen_key (p q r : ℂ) (hpr : ‖p‖ ≠ ‖r‖) :
    r * ((star r * q + p * star q) / ((‖r‖^2 - ‖p‖^2 : ℝ) : ℂ))
      - p * star ((star r * q + p * star q) / ((‖r‖^2 - ‖p‖^2 : ℝ) : ℂ)) = q := by
  -- `↑(‖r‖²) = r * star r` and the same for `p`
  have hr2 : ((‖r‖^2 : ℝ) : ℂ) = r * star r := by
    rw [← Complex.normSq_eq_norm_sq r]
    exact (Complex.mul_conj r).symm
  have hp2 : ((‖p‖^2 : ℝ) : ℂ) = p * star p := by
    rw [← Complex.normSq_eq_norm_sq p]
    exact (Complex.mul_conj p).symm
  -- the denominator is nonzero
  have hD0 : ((‖r‖^2 - ‖p‖^2 : ℝ) : ℂ) ≠ 0 := by
    intro h
    have h1 : ‖r‖^2 - ‖p‖^2 = 0 := Complex.ofReal_eq_zero.mp h
    have h2 : ‖r‖^2 = ‖p‖^2 := sub_eq_zero.mp h1
    have h3 : ‖r‖ = ‖p‖ := (sq_eq_sq₀ (norm_nonneg r) (norm_nonneg p)).mp h2
    exact hpr h3.symm
  -- the relevant conjugate
  have hs : star (star r * q + p * star q) = r * star q + star p * q := by
    simp only [star_add, star_mul, star_star]
    ring
  -- the denominator is real, hence fixed by conjugation
  have hDstar : star (((‖r‖^2 - ‖p‖^2 : ℝ) : ℂ)) = ((‖r‖^2 - ‖p‖^2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  -- numerator identity: the `star q` terms cancel
  have hnum : r * (star r * q + p * star q) - p * (r * star q + star p * q)
      = ((‖r‖^2 - ‖p‖^2 : ℝ) : ℂ) * q := by
    have h1 : r * (star r * q + p * star q) - p * (r * star q + star p * q)
        = (r * star r - p * star p) * q := by ring
    rw [h1, ← hr2, ← hp2, ← Complex.ofReal_sub]
  rw [star_div₀, hs, hDstar, ← mul_div_assoc, ← mul_div_assoc, div_sub_div_same, hnum,
    mul_div_cancel_left₀ q hD0]

end Work.Diff.Alg.Q2PR
