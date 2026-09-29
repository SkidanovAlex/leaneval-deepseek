import Mathlib
import Submission.Work.Resample.auDefs

/-!
# Arithmetic of the window centre `auK` (paper §4.2, Lemma 4.9 setup)

`Work.Resample.auK s t k = ⌊(2ks+t)/(2t)⌋ = round (k s / t)`, the centre of the `k`-th output
window of the 1-D Gaussian resampling word.

This file records the three elementary facts about it that the resampling word needs, for
`2 ≤ s`, `s < t < 2^p`, `k < t`:

* `auK s t k < 2^p`                    (the centre is a valid `p`-bit index),
* `auK s t k ≤ auK s t (k+1)`          (the centres advance monotonically),
* `auK s t (k+1) ≤ auK s t k + 1`      (they advance by at most one).

The three helper lemmas below are the components: monotonicity in `k` is `Nat.div_le_div_right`,
the step bound is `Nat.add_div_le_div_add_div_add_one` together with `(2s)/(2t) = 0` (because
`s < t`), and the size bound is `auK s t k ≤ k` (because `s ≤ t`) combined with `k < t < 2^p`.
-/

set_option autoImplicit false

namespace Work.Resample

/-- If `s ≤ t` then the window centre never passes its index: `⌊(2ks+t)/(2t)⌋ ≤ k`. -/
lemma auKArith_le_self (s t k : ℕ) (hst : s ≤ t) : auK s t k ≤ k := by
  unfold auK
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht; simp
  · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * t)]
    nlinarith [Nat.mul_le_mul_left (2 * k) hst, ht]

/-- The window centre is monotone in the output index `k`. -/
lemma auKArith_mono (s t : ℕ) : Monotone (auK s t) := by
  intro a b hab
  unfold auK
  apply Nat.div_le_div_right
  exact Nat.add_le_add_right (Nat.mul_le_mul_right s (Nat.mul_le_mul_left 2 hab)) t

/-- For `s < t` consecutive window centres differ by at most one: `K_{k+1} ≤ K_k + 1`. -/
lemma auKArith_step (s t k : ℕ) (hst : s < t) (ht : 0 < t) :
    auK s t (k + 1) ≤ auK s t k + 1 := by
  have h2 : 2 * s < 2 * t := by omega
  have hd : (2 * s) / (2 * t) = 0 := Nat.div_eq_of_lt h2
  unfold auK
  have h1 : 2 * (k + 1) * s + t = (2 * k * s + t) + 2 * s := by ring
  rw [h1]
  calc ((2 * k * s + t) + 2 * s) / (2 * t)
      ≤ (2 * k * s + t) / (2 * t) + (2 * s) / (2 * t) + 1 :=
        Nat.add_div_le_div_add_div_add_one _ _ _
    _ = (2 * k * s + t) / (2 * t) + 1 := by rw [hd]

theorem auKArith (p s t k : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p) (hk : k < t) :
    Work.Resample.auK s t k < 2 ^ p ∧ Work.Resample.auK s t k ≤ Work.Resample.auK s t (k + 1) ∧
      Work.Resample.auK s t (k + 1) ≤ Work.Resample.auK s t k + 1 := by
  have ht : 0 < t := by omega
  have hle : auK s t k ≤ k := auKArith_le_self s t k (le_of_lt hst)
  exact ⟨lt_of_le_of_lt hle (lt_trans hk htp),
    auKArith_mono s t (Nat.le_succ k), auKArith_step s t k hst ht⟩

end Work.Resample
