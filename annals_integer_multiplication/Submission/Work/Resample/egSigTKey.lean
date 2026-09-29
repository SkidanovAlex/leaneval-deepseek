import Mathlib
import Submission.Work.Resample.sliceB1defs

namespace Work.Resample

/-- The index map `σ_t k = (-s·k) mod t` of `P̃_t` is a permutation of `{0,…,t-1}` (for
`gcd s t = 1`): it satisfies `σ_t k + s·k ≡ 0 (mod t)` for every `k`, and it is injective
on the range `[0,t)`. -/
theorem egSigTKey (s t : ℕ) (hcop : Nat.Coprime s t) (ht : 0 < t) :
    (∀ k : ℕ, (s * k + Work.Resample.egSigT s t k) % t = 0) ∧
    (∀ k k' : ℕ, k < t → k' < t → Work.Resample.egSigT s t k = Work.Resample.egSigT s t k' → k = k') := by
  -- `σ_t k = (t - s·k % t) % t` is congruent to `-(s·k)`, hence `s·k + σ_t k ≡ 0`.
  have hmod : ∀ k : ℕ, (s * k + egSigT s t k) % t = 0 := by
    intro k
    show (s * k + (t - s * k % t) % t) % t = 0
    have hrlt : s * k % t < t := Nat.mod_lt _ ht
    have hle : s * k % t ≤ t := le_of_lt hrlt
    have h3 : s * k + (t - s * k % t) % t ≡ 0 [MOD t] := by
      have h1 : s * k + (t - s * k % t) % t ≡ (s * k % t) + (t - s * k % t) [MOD t] :=
        (Nat.mod_modEq (s * k) t).symm.add (Nat.mod_modEq (t - s * k % t) t)
      have h2 : (s * k % t) + (t - s * k % t) ≡ 0 [MOD t] := by
        rw [Nat.add_sub_of_le hle]
        show t % t = 0 % t
        rw [Nat.mod_self, Nat.zero_mod]
      exact h1.trans h2
    change (s * k + (t - s * k % t) % t) % t = 0 % t at h3
    rwa [Nat.zero_mod] at h3
  -- Injectivity on `[0,t)`: `s·k + σ_t k ≡ 0` and `σ_t k = σ_t k'` force `s·k ≡ s·k'`,
  -- and `s` is invertible mod `t`.
  refine ⟨hmod, ?_⟩
  intro k k' hk hk' heq
  have hB : s * k ≡ s * k' [MOD t] := Nat.ModEq.add_right_cancel' (egSigT s t k) (by
    show (s * k + egSigT s t k) % t = (s * k' + egSigT s t k) % t
    rw [hmod k, heq, hmod k'])
  have hC : k ≡ k' [MOD t] := Nat.ModEq.cancel_left_of_coprime hcop.symm hB
  exact Nat.ModEq.eq_of_lt_of_lt hC hk hk'

end Work.Resample
