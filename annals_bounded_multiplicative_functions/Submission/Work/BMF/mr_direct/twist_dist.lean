import Mathlib
import ChallengeDeps
import Submission.Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Twisting the pretentious distance `𝔻` by `n^{it}` phases

For `f : ℕ → ℂ` and reals `t, u, x` the pretentious distance satisfies

`𝔻 (f · n^{-it}) (n^{iu}) x = 𝔻 f (n^{i(t+u)}) x`.

Both sides are sums over the primes `p ≤ x`, with the same index set, and the summands
agree pointwise because for a prime `p`

`f(p) p^{-it} conj(p^{iu}) = f(p) conj(p^{i(t+u)})`,

using `conj(p^{w}) = p^{conj w}` for a real base `p ≥ 0` and `conj(iu) = -iu`, `conj(i(t+u)) = -i(t+u)`.
-/

namespace Work.BMF.mr_direct

open BoundedMultiplicativeFunctions

/-- Conjugation commutes with an exponentiation of a natural (in particular, real
nonnegative) base. -/
lemma star_natCast_cpow_nat (n : ℕ) (w : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ w) = (n : ℂ) ^ (starRingEnd ℂ) w := by
  have h := Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg (y := (n : ℝ))
    (Nat.cast_nonneg n) w
  simpa using h

/-- The pointwise identity underlying `twist_dist`, at a prime `p`. -/
lemma twist_pointwise_nat (f : ℕ → ℂ) (t u : ℝ) {p : ℕ} (hp : p.Prime) :
    f p * (p : ℂ) ^ (-(Complex.I * t)) * (starRingEnd ℂ) ((p : ℂ) ^ (Complex.I * u))
      = f p * (starRingEnd ℂ) ((p : ℂ) ^ (Complex.I * (t + u))) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h₁ : (starRingEnd ℂ) ((p : ℂ) ^ (Complex.I * u)) = (p : ℂ) ^ (-(Complex.I * u)) := by
    have h := star_natCast_cpow_nat p (Complex.I * (u : ℂ))
    simpa using h
  have h₂ : (starRingEnd ℂ) ((p : ℂ) ^ (Complex.I * (t + u))) =
      (p : ℂ) ^ (-(Complex.I * (t + u))) := by
    have h := star_natCast_cpow_nat p (Complex.I * ((t : ℂ) + (u : ℂ)))
    simpa using h
  rw [h₁, h₂]
  rw [show f p * ↑p ^ (-(Complex.I * ↑t)) * ↑p ^ (-(Complex.I * ↑u))
        = f p * (↑p ^ (-(Complex.I * ↑t)) * ↑p ^ (-(Complex.I * ↑u))) by ring]
  rw [← Complex.cpow_add (-(Complex.I * ↑t)) (-(Complex.I * ↑u)) hp0]
  rw [show -(Complex.I * (t : ℂ)) + -(Complex.I * (u : ℂ))
        = -(Complex.I * ((t : ℂ) + (u : ℂ))) by ring]

theorem twist_dist (f : ℕ → ℂ) (x t u : ℝ) :
    BoundedMultiplicativeFunctions.𝔻 (fun n ↦ f n * (n : ℂ) ^ (-(Complex.I * t)))
        (fun n ↦ (n : ℂ) ^ (Complex.I * u)) x
      = BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * (t + u))) x := by
  unfold BoundedMultiplicativeFunctions.𝔻
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  show (1 - (f p * (p : ℂ) ^ (-(Complex.I * t)) *
        (starRingEnd ℂ) ((p : ℂ) ^ (Complex.I * u))).re) / (p : ℝ)
      = (1 - (f p * (starRingEnd ℂ) ((p : ℂ) ^ (Complex.I * (t + u)))).re) / (p : ℝ)
  rw [twist_pointwise_nat f t u (Nat.prime_of_mem_primesLE hp)]

end Work.BMF.mr_direct
