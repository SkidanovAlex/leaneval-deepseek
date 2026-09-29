import Mathlib
import Submission.Work.Resample.lamDefs

/-!
# `egSigT s t k = (-(k·s)) mod t` (`Work.Resample.sigFmod`)

The index map `σ_t k = (-s·k) mod t` of `P̃_t` was defined in `sliceB1defs` by the *natural*
formula `egSigT s t k = (t - s·k % t) % t` (the `t - …` handles the minus sign inside `ℕ`).
This module identifies it with the *integer* remainder `Int.fmod (-(k·s)) t`, which is the
form produced by the `fmod` primitive of the compiled word (paper Prop. 4.7).

The proof is a `ℤ`-level identity: for any `A`, `T : ℤ` the fixed-point remainder of `-A`
satisfies `(-A) % T = (T - A % T) % T` (`emod_T_sub_emod`), so subtracting the natural
remainder `s·k % t` from `t` and reducing mod `t` is exactly `Int.fmod (-(k·s)) t`.
-/

set_option autoImplicit false

namespace Work.Resample

/-- Two integers congruent modulo `n` have the same Euclidean remainder modulo `n`. -/
lemma emod_eq_of_modEq {a b n : ℤ} (h : a ≡ b [ZMOD n]) : a % n = b % n := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  simpa using dvd_neg.mpr (Int.modEq_iff_dvd.mp h)

/-- The remainder of `-A` modulo `T` is the remainder of `T - A % T`: the sign flip of
`Int.fmod` is exactly the `T - …` correction (valid for every `T`, including `T = 0`). -/
lemma emod_T_sub_emod (A T : ℤ) : (T - A % T) % T = (-A) % T := by
  have hrA : A % T ≡ A [ZMOD T] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨A / T, by rw [Int.emod_def]; ring⟩
  have h2 : T - A % T ≡ -(A % T) [ZMOD T] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-1, by ring⟩
  exact emod_eq_of_modEq (h2.trans hrA.neg)

theorem sigFmod (s t k : ℕ) (ht : 0 < t) :
    ((Work.Resample.egSigT s t k : ℕ) : ℤ) = Int.fmod (-((k : ℤ) * (s : ℤ))) (t : ℤ) := by
  have hT : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht
  have hle : s * k % t ≤ t := le_of_lt (Nat.mod_lt _ ht)
  rw [egSigT, Int.natCast_emod, Nat.cast_sub hle, Int.natCast_emod, Nat.cast_mul,
      Int.fmod_eq_emod_of_nonneg _ (le_of_lt hT)]
  rw [show -((k : ℤ) * (s : ℤ)) = -((s : ℤ) * (k : ℤ)) by ring]
  exact emod_T_sub_emod ((s : ℤ) * (k : ℤ)) ((t : ℤ))

end Work.Resample
