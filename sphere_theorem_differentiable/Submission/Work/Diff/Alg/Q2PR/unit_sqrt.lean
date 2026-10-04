import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Q2PR

/-- Every complex number `ω` of modulus one has a square root `t` which is itself of modulus one
(in the form `t * star t = 1`). -/
theorem unit_sqrt (ω : ℂ) (hω : ‖ω‖ = 1) : ∃ t : ℂ, t ^ 2 = ω ∧ t * star t = 1 := by
  -- A square root exists by the fundamental theorem of algebra.
  obtain ⟨t, ht⟩ := Complex.isSquare ω
  have ht2 : t ^ 2 = ω := by rw [pow_two]; exact ht.symm
  -- `t * star t` is the (real, nonnegative) squared modulus of `t`.
  have hm : t * star t = (Complex.normSq t : ℂ) := by
    simp only [Complex.star_def]; exact Complex.mul_conj t
  refine ⟨t, ht2, ?_⟩
  -- Squaring `t * star t` gives `t ^ 2 * star (t ^ 2) = ω * star ω = ‖ω‖ ^ 2 = 1`.
  have hsq : (Complex.normSq t : ℂ) ^ 2 = 1 := by
    rw [← hm, mul_pow, ← star_pow, ht2]
    have hmω : ω * star ω = (Complex.normSq ω : ℂ) := by
      simp only [Complex.star_def]; exact Complex.mul_conj ω
    rw [hmω, Complex.normSq_eq_norm_sq, hω]
    norm_num
  have hreal : (Complex.normSq t) ^ 2 = (1 : ℝ) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one] at hsq
    exact Complex.ofReal_inj.mp hsq
  -- Nonnegativity rules out the negative root `-1`.
  have hnn := Complex.normSq_nonneg t
  have hn1 : Complex.normSq t = 1 := by nlinarith
  rw [hm, hn1, Complex.ofReal_one]

end Work.Diff.Alg.Q2PR
