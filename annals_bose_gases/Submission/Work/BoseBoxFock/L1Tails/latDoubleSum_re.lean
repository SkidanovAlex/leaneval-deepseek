import Mathlib.Analysis.Complex.Basic
import Submission.Work.BoseBoxFock.L1Tails.latDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.L1Tails

/-- The Kronecker collapse of the double sum that the box-wave orthogonality produces: after
substituting `∫_{boxL ℓ} latWave (kappaL ℓ (m - n)) = if m = n then ℓ³ else 0`, the remaining
finite double sum over the finite set `S` of coefficients has real part `ℓ³ * ∑ n ∈ S, ‖c n‖²`.

Proof hints: `Finset.sum_eq_single` collapses the inner sum over `m` (at `m = n` the term is
`conj (c n) * c n * ((ℓ^3 : ℝ) : ℂ)`), then `Complex.conj_mul'`
(`(starRingEnd ℂ) z * z = ↑‖z‖ ^ 2`), `Complex.ofReal_re`, `Complex.ofReal_mul`,
`Complex.ofReal_pow` and `Finset.mul_sum` extract the real part and the factor `ℓ ^ 3`. -/
theorem latDoubleSum_re (ℓ : ℝ) (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ) :
    (∑ n ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (c n) * c m * (if m = n then ((ℓ ^ 3 : ℝ) : ℂ) else 0)).re
      = ℓ ^ 3 * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  -- collapse the inner sum over `m` with Kronecker's delta
  have hinner : ∀ n ∈ S,
      (∑ m ∈ S, (starRingEnd ℂ) (c n) * c m * (if m = n then ((ℓ ^ 3 : ℝ) : ℂ) else 0))
        = ((ℓ ^ 3 * ‖c n‖ ^ 2 : ℝ) : ℂ) := by
    intro n hn
    rw [Finset.sum_eq_single n]
    · rw [if_pos rfl, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
      ring_nf
    · intro b _ hbn; rw [if_neg hbn, mul_zero]
    · intro hnS; exact absurd hn hnS
  rw [Finset.sum_congr rfl hinner, ← Complex.ofReal_sum, Complex.ofReal_re, Finset.mul_sum]

end Work.BoseBoxFock.L1Tails
