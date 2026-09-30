import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.Psi1_L2_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Rewriting `Psi1 f (1+α+iτ)` as a sum over the natural numbers

`Psi1 f s = -Σ_p f p · log p · p^{-s}` is defined in `halasz_series_aux` as a `tsum` over the
subtype `Nat.Primes`.  For the archimedean analysis of `∫ ‖Psi1 f (1+α+iτ)‖² dτ` it is convenient
to regard it as a `tsum` over all of `ℕ`, supported on the primes, with the complex power
`p^{-(1+α+iτ)}` split into the real decay `p^{-(1+α)}` and the oscillating factor
`exp (-(τ log p) i)`.

The pointwise identity is a direct consequence of `Complex.ofReal_cpow` (real exponent) together
with `Complex.cpow_def_of_ne_zero` / `Complex.ofReal_log` (imaginary exponent).
-/

namespace Work.BMF

open Finset Real Complex

/-- Splitting the complex power at `s = (1+α) + τi` into magnitude and oscillation:
`n^{-((1+α)+τi)} = n^{-(1+α)} · exp (-(τ log n) i)` for `n` a positive integer. -/
lemma cpow_ofReal_add_mul_I (n : ℕ) (hn : n.Prime) (α τ : ℝ) :
    ((n : ℂ)) ^ (-(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I))
      = (((n : ℝ) ^ (-(1 + α)) : ℝ) : ℂ) * Complex.exp (-(τ * Real.log n) * Complex.I) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    simp only [Nat.cast_ne_zero]; exact hn.ne_zero
  have hsplit : -(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
      = (((-(1 + α) : ℝ)) : ℂ) + (-((τ : ℂ) * Complex.I)) := by push_cast; ring
  rw [hsplit, Complex.cpow_add _ _ hn0]
  rw [show (n : ℂ) ^ (((-(1 + α) : ℝ)) : ℂ) = (((n:ℝ)^(-(1+α)) : ℝ) : ℂ) by
        have h : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
        rw [h, Complex.ofReal_cpow (Nat.cast_nonneg n) (-(1+α))]]
  rw [show (n : ℂ) ^ (-((τ : ℂ) * Complex.I)) = Complex.exp (-(τ * Real.log n) * Complex.I) by
        rw [Complex.cpow_def_of_ne_zero hn0, Complex.natCast_log]
        congr 1
        ring]

theorem Psi1_L2_psi_rewrite (f : ℕ → ℂ) (α τ : ℝ) :
    Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
      = ∑' n : ℕ, (if n.Prime then
          -((f n * (Real.log n : ℂ)) * (((n : ℝ) ^ (-(1 + α)) : ℝ) : ℂ))
            * Complex.exp (-(τ * Real.log n) * Complex.I) else 0) := by
  unfold Psi1
  -- Reindex the sum over `Nat.Primes` as a sum over `ℕ` with the prime indicator.
  change (∑' p : ↥({n : ℕ | n.Prime} : Set ℕ),
      -(f ↑p * (Real.log (↑p : ℕ) : ℂ) * (↑p : ℂ) ^
        (-(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)))) = _
  rw [tsum_subtype (s := {n : ℕ | n.Prime})
        (f := fun n : ℕ => -(f n * (Real.log n : ℂ) * (n : ℂ) ^
            (-(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I))))]
  apply tsum_congr
  intro n
  rw [Set.indicator_apply]
  by_cases h : n.Prime
  · simp only [Set.mem_ofPred_eq, h, ite_true]
    rw [cpow_ofReal_add_mul_I n h α τ]
    ring
  · simp only [Set.mem_ofPred_eq, h, ite_false]

end Work.BMF
