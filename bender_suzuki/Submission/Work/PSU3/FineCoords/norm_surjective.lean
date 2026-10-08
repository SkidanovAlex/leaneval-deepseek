import Mathlib
import Submission.Work.PSU3.GaloisField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3.FineCoords

open Work.PSU3

/-- The distinguished involution `σE` of `GaloisField 2 (2 * n)` is the `2ⁿ`-power
Frobenius `x ↦ x ^ (2 ^ n)`. -/
lemma σE_eq_pow (n : ℕ) (x : GaloisField 2 (2 * n)) :
    σE x = x ^ (2 ^ n) := by
  change (iterateFrobenius (GaloisField 2 (2 * n)) 2 n) x = x ^ 2 ^ n
  exact iterateFrobenius_def 2 n x

/-- The norm map `μ ↦ μ · σE μ` of `GF(2^(2n))` over the fixed field of `σE` is
surjective onto the elements fixed by `σE`.  Explicitly, for `n ≥ 1` the element
`μ = w ^ (2 ^ (n-1))` already satisfies `μ · σE μ = w`; for `n = 0` we square-root
`w` (squaring is onto in a finite field of characteristic two). -/
theorem norm_surjective (n : ℕ) (w : GaloisField 2 (2 * n))
    (hw : σE w = w) (hw0 : w ≠ 0) :
    ∃ μ : (GaloisField 2 (2 * n))ˣ,
      (μ : GaloisField 2 (2 * n)) * σE (μ : GaloisField 2 (2 * n)) = w := by
  rcases n with _ | k
  · -- `n = 0`: `σE` is the identity, so we need a square root of `w`.
    have hσ : ∀ x : GaloisField 2 (2 * 0), σE x = x ^ 2 ^ 0 := σE_eq_pow 0
    have hsurj : Function.Surjective (fun x : GaloisField 2 (2 * 0) => x ^ 2) := by
      apply Finite.surjective_of_injective
      intro a b hab
      change a ^ 2 = b ^ 2 at hab
      exact CharTwo.sq_inj.mp hab
    obtain ⟨μ, hμ⟩ := hsurj w
    change μ ^ 2 = w at hμ
    have hμ0 : μ ≠ 0 := by
      intro h0
      rw [h0, pow_two, zero_mul] at hμ
      exact hw0 hμ.symm
    refine ⟨Units.mk0 μ hμ0, ?_⟩
    rw [Units.val_mk0]
    have hs : σE μ = μ := by simpa using hσ μ
    rw [hs, ← pow_two]
    exact hμ
  · -- `n = k + 1`: take `μ = w ^ (2 ^ k)`.
    have hσ : ∀ x : GaloisField 2 (2 * (k + 1)), σE x = x ^ (2 ^ (k + 1)) :=
      σE_eq_pow (k + 1)
    refine ⟨Units.mk0 (w ^ (2 ^ k)) (pow_ne_zero _ hw0), ?_⟩
    rw [Units.val_mk0]
    have hfix : σE (w ^ (2 ^ k)) = w ^ (2 ^ k) := by
      rw [map_pow, hw]
    rw [hfix]
    have h2 : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
      rw [← two_mul, ← pow_succ']
    rw [← pow_add, h2, ← hσ w, hw]

end Work.PSU3.FineCoords
