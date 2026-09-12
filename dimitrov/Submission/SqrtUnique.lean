import Mathlib

/-!
# Uniqueness of the formal square root with constant term 1

`Submission.PowRev.powRev_sqrt_integral` produces an integer sequence
`a : ℕ → ℤ` with `a 0 = 1` whose convolution square is the coefficient
sequence of the polynomial `G := (pow2 P).reflect d * (pow4 P).reflect d`:

    (∑ i ∈ range (k+1), a i * a (k - i)) = G.coeff k          (all k)

i.e. `(∑ aₖ wᵏ)² = G(w)` in the ring of formal power series.  Any holomorphic
function `f` on a neighbourhood of `0` with `f 0 = 1` and `f² = G` has Taylor
coefficients `f⁽ᵏ⁾(0)/k!` that satisfy the same convolution identities (the
Taylor series of `f²` is the convolution square of the Taylor series of `f`),
so — by the uniqueness lemma in this file — those Taylor coefficients equal
`a`.  This is how the *integer coefficients* enter the analytic engine: the
holomorphic square root produced on a simply connected domain (see
`Submission.HoloSqrt`) automatically has Taylor coefficients equal to the
integer sequence `a` at `0`, giving the "integer coefficients" hypothesis
required by the rationality theorem (Pólya / Bertrandias).

## Lemma

`sqrt_seq_unique`: two sequences `b, c : ℕ → ℂ` with the same first value
`b 0 = c 0 = 1` and the same convolution square are equal.

*Proof by induction on `k`.*  For `k = 0` both are `1`.  For `k > 0`, isolate
the terms `i = 0` and `i = k` in the convolution at `k`:

    (∑ i ∈ range (k+1), b i * b (k - i)) = b 0 * b k + b k * b 0
                                            + (∑ i ∈ range (k+1) with 0 < i and i < k, ...)
                                          = 2 * b k + (middle terms)

The middle terms involve only indices `< k`, which agree by the induction
hypothesis, and the total sums agree by hypothesis, so `2 * (b k - c k) = 0`,
hence `b k = c k` in `ℂ`.

You may add helper lemmas.  Do NOT change the statement of `sqrt_seq_unique`.
No sorries may remain in this file.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Submission.SqrtUnique

/-- Two sequences over `ℂ` with the same first value `1` and the same
convolution square are equal. -/
theorem sqrt_seq_unique {b c : ℕ → ℂ} (hb0 : b 0 = 1) (hc0 : c 0 = 1)
    (hconv : ∀ k : ℕ, (∑ i ∈ Finset.range (k + 1), b i * b (k - i)) =
        (∑ i ∈ Finset.range (k + 1), c i * c (k - i))) :
    ∀ k : ℕ, b k = c k := by
  have main : ∀ n : ℕ, (∀ m : ℕ, m < n → b m = c m) → b n = c n := by
    intro n ihn
    cases n with
    | zero =>
        simp [hb0, hc0]
    | succ k =>
        -- The convolution identity at index `k + 1`.
        have hEq0 : (∑ i ∈ Finset.range (k + 1 + 1), b i * b (k + 1 - i))
                  = (∑ i ∈ Finset.range (k + 1 + 1), c i * c (k + 1 - i)) := by
          simpa using hconv (k + 1)
        -- Rewrite the left convolution: isolate `i = 0` and `i = k + 1`.
        have hmid_b : (∑ j ∈ Finset.range k, b (j + 1) * b (k + 1 - (j + 1)))
                    = ∑ j ∈ Finset.range k, b (j + 1) * b (k - j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < k := Finset.mem_range.mp hj
          rw [show k + 1 - (j + 1) = k - j by omega]
        have hmid_c : (∑ j ∈ Finset.range k, c (j + 1) * c (k + 1 - (j + 1)))
                    = ∑ j ∈ Finset.range k, c (j + 1) * c (k - j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < k := Finset.mem_range.mp hj
          rw [show k + 1 - (j + 1) = k - j by omega]
        have eq_b : (∑ i ∈ Finset.range (k + 1 + 1), b i * b (k + 1 - i))
                  = b 0 * b (k + 1) + (∑ j ∈ Finset.range k, b (j + 1) * b (k - j))
                      + b (k + 1) * b 0 := by
          rw [Finset.sum_range_succ]
          rw [Finset.sum_range_succ']
          rw [hmid_b]
          simp
          ring_nf
        have eq_c : (∑ i ∈ Finset.range (k + 1 + 1), c i * c (k + 1 - i))
                  = c 0 * c (k + 1) + (∑ j ∈ Finset.range k, c (j + 1) * c (k - j))
                      + c (k + 1) * c 0 := by
          rw [Finset.sum_range_succ]
          rw [Finset.sum_range_succ']
          rw [hmid_c]
          simp
          ring_nf
        -- The middle terms involve only indices `< k + 1`, so they agree.
        have hM : (∑ j ∈ Finset.range k, b (j + 1) * b (k - j))
                = (∑ j ∈ Finset.range k, c (j + 1) * c (k - j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < k := Finset.mem_range.mp hj
          have h1 : b (j + 1) = c (j + 1) := ihn (j + 1) (Nat.succ_lt_succ hjlt)
          have h2 : b (k - j) = c (k - j) := by
            exact ihn (k - j) (by omega)
          rw [h1, h2]
        have hCore :
            b 0 * b (k + 1) + (∑ j ∈ Finset.range k, b (j + 1) * b (k - j)) + b (k + 1) * b 0
            = c 0 * c (k + 1) + (∑ j ∈ Finset.range k, c (j + 1) * c (k - j)) + c (k + 1) * c 0 := by
          calc
            b 0 * b (k + 1) + (∑ j ∈ Finset.range k, b (j + 1) * b (k - j)) + b (k + 1) * b 0
                = (∑ i ∈ Finset.range (k + 1 + 1), b i * b (k + 1 - i)) := eq_b.symm
            _ = (∑ i ∈ Finset.range (k + 1 + 1), c i * c (k + 1 - i)) := hEq0
            _ = c 0 * c (k + 1) + (∑ j ∈ Finset.range k, c (j + 1) * c (k - j)) + c (k + 1) * c 0 := eq_c
        rw [hM, hb0, hc0] at hCore
        have hCore1 :
            b (k + 1) + (∑ j ∈ Finset.range k, c (j + 1) * c (k - j)) + b (k + 1)
            = c (k + 1) + (∑ j ∈ Finset.range k, c (j + 1) * c (k - j)) + c (k + 1) := by
          simpa [one_mul, mul_one] using hCore
        -- Cancel the common middle term, then divide by 2.
        have hCore2 : b (k + 1) + b (k + 1) = c (k + 1) + c (k + 1) := by
          calc
            b (k + 1) + b (k + 1)
                = b (k + 1) + (∑ j ∈ Finset.range k, c (j + 1) * c (k - j)) + b (k + 1)
                    - (∑ j ∈ Finset.range k, c (j + 1) * c (k - j)) := by ring
            _ = c (k + 1) + (∑ j ∈ Finset.range k, c (j + 1) * c (k - j)) + c (k + 1)
                    - (∑ j ∈ Finset.range k, c (j + 1) * c (k - j)) := by rw [hCore1]
            _ = c (k + 1) + c (k + 1) := by ring
        have htwo : 2 * b (k + 1) = 2 * c (k + 1) := by
          simpa [two_mul] using hCore2
        exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) htwo
  exact fun n => Nat.strong_induction_on n main

end Submission.SqrtUnique

end
