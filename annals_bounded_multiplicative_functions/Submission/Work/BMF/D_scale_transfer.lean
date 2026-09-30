import Mathlib
import Submission.Work.BMF.H6_imports
import Submission.Work.BMF.D_scale_aux_sum
import Submission.Work.BMF.D_scale_term_bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Scaling transfer for the pretentious distance `𝔻`

The pretentious distance `𝔻 f g X` of the challenge is (the square root of) a sum over the
primes `p ≤ ⌊X⌋₊`.  When the cut-off is only *lowered* by a bounded factor `K ≥ 1`
(`Y / K ≤ Y' ≤ Y`), the extra contribution of the primes in `(Y', Y]` is bounded by a
constant depending on `K` alone: for one-bounded `f, g` each summand lies in `[0, 2/p]`, and
there are at most `K` "copies" of the range `(Y', K Y']` in units of `2 / Y'`.  Hence
`𝔻 f g Y ≤ 𝔻 f g Y' + (2K)^{1/2}`, obtained from
`√(S + 2K) ≤ √S + √(2K)`.
-/

namespace Work.BMF

theorem D_scale_transfer (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
      ∀ (Y Y' : ℝ), 11 ≤ Y' → Y / K ≤ Y' → Y' ≤ Y →
        BoundedMultiplicativeFunctions.𝔻 f g Y ≤ BoundedMultiplicativeFunctions.𝔻 f g Y' + C := by
  refine ⟨(2 * K) ^ (1 / 2 : ℝ), Real.rpow_nonneg (by linarith) _, ?_⟩
  intro f g hf hg Y Y' hY' hYK hY'Y
  let t : ℕ → ℝ := fun p => (1 - (f p * star (g p)).re) / (p : ℝ)
  have htb := D_scale_term_bounds f g hf hg
  have ht0 : ∀ p, 0 ≤ t p := htb.1
  have ht2 : ∀ p, t p ≤ 2 / (p : ℝ) := htb.2
  have hD : ∀ X : ℝ, BoundedMultiplicativeFunctions.𝔻 f g X =
      (∑ p ∈ ⌊X⌋₊.primesLE, t p) ^ (1 / 2 : ℝ) := fun X => rfl
  have hmain : (∑ p ∈ ⌊Y⌋₊.primesLE, t p) ≤
      (∑ p ∈ ⌊Y'⌋₊.primesLE, t p) + 2 * K :=
    D_scale_aux_sum hK hY' hYK hY'Y t ht0 ht2
  have hA0 : 0 ≤ ∑ p ∈ ⌊Y⌋₊.primesLE, t p := Finset.sum_nonneg (fun p _ => ht0 p)
  have hB0 : 0 ≤ ∑ p ∈ ⌊Y'⌋₊.primesLE, t p := Finset.sum_nonneg (fun p _ => ht0 p)
  have h2K0 : (0 : ℝ) ≤ 2 * K := by linarith
  rw [hD Y, hD Y']
  calc (∑ p ∈ ⌊Y⌋₊.primesLE, t p) ^ (1 / 2 : ℝ)
      ≤ ((∑ p ∈ ⌊Y'⌋₊.primesLE, t p) + 2 * K) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (z := 1 / 2) hA0 hmain (by norm_num)
    _ ≤ (∑ p ∈ ⌊Y'⌋₊.primesLE, t p) ^ (1 / 2 : ℝ) + (2 * K) ^ (1 / 2 : ℝ) :=
        Real.rpow_add_le_add_rpow (p := 1 / 2) (a := ∑ p ∈ ⌊Y'⌋₊.primesLE, t p)
          (b := 2 * K) hB0 h2K0 (by norm_num) (by norm_num)

end Work.BMF
