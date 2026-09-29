import Mathlib
import Submission.Work.Cert.aLoop_aux
import Submission.Work.Cert.aInv_step
import Submission.Work.Cert.aInv_base

/-! # The `A`-accumulator loop meets its invariant after `KTH = 12` steps

`aLoop qr qi rq m 12 1 s₀` is the state of the triangular theta-sum accumulator after the twelve
steps `aStep … 1, …, aStep … 12` from the initial state `s₀ = ⟨S, 0, S, 0, S, 0, S, S, 0, 0⟩`
(`1 + 0·i` in mantissa units, `T = 0`, budgets `0`).  The invariant `AInv` is preserved by one step
(`aInv_step`) and holds after the first step (`aInv_base`), so it holds at index `12`; unfolding
`aLoop` identifies the twelve-fold iteration of `aStep` with the recursive chain `aSt`. -/

namespace Work.Cert

open Complex Finset

noncomputable section

/-- The state reached by the `A`-loop after `k` completed steps, i.e. after applying
`aStep … 1, aStep … 2, …, aStep … k` to the loop's initial state.  This is the same state as
`aLoop qr qi rq m k 1 ⟨S, 0, S, 0, S, 0, S, S, 0, 0⟩` (`aSt_eq_aLoop`), organised so that the
induction `aInv_step` applies step by step. -/
def aSt (qr qi rq m : ℤ) : ℕ → TS
  | 0 => ⟨S, 0, S, 0, S, 0, S, S, 0, 0⟩
  | k + 1 => aStep qr qi rq m (k + 1) (aSt qr qi rq m k)

lemma aSt_zero (qr qi rq m : ℤ) :
    aSt qr qi rq m 0 = ⟨S, 0, S, 0, S, 0, S, S, 0, 0⟩ := rfl

lemma aSt_succ (qr qi rq m : ℤ) (k : ℕ) :
    aSt qr qi rq m (k + 1) = aStep qr qi rq m (k + 1) (aSt qr qi rq m k) := rfl

/-- Unfolding `aLoop` twelve times (it applies the steps `aStep … 1, …, aStep … 12` from the
front) identifies it with the recursive chain `aSt`. -/
lemma aSt_eq_aLoop (qr qi rq m : ℤ) :
    aSt qr qi rq m 12 = aLoop qr qi rq m 12 1 ⟨S, 0, S, 0, S, 0, S, S, 0, 0⟩ := rfl

/-- The invariant `AInv` holds at every index `k + 1 ≥ 1` along the loop. -/
theorem aSt_inv (hcxmul : ∀ a b c d : ℤ,
      ‖cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d‖ ≤ 3 / ((S : ℝ)))
    (qr qi rq m : ℤ) (hm : 1 ≤ m) (hrq : 0 ≤ rq) (hμ : mub m ≤ 79 / 100)
    (hz : ‖qc qr qi‖ ≤ mub m) (k : ℕ) :
    AInv qr qi rq m (k + 1) (aSt qr qi rq m (k + 1)) := by
  induction k with
  | zero =>
    rw [aSt_succ, aSt_zero]
    exact aInv_base hcxmul qr qi rq m hm hrq hμ hz
  | succ k ih =>
    rw [aSt_succ]
    exact aInv_step hcxmul qr qi rq m hm hrq hμ hz (k + 1) (by omega) _ ih

theorem aLoop_inv (hcxmul : ∀ a b c d : ℤ, ‖cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d‖ ≤ 3 / ((S : ℝ)))
    (qr qi rq m : ℤ) (hm : 1 ≤ m) (hrq : 0 ≤ rq) (hμ : mub m ≤ 79 / 100) (hz : ‖qc qr qi‖ ≤ mub m) :
    AInv qr qi rq m KTH (aLoop qr qi rq m KTH 1 ⟨S, 0, S, 0, S, 0, S, S, 0, 0⟩) := by
  have h : AInv qr qi rq m 12 (aSt qr qi rq m 12) := aSt_inv hcxmul qr qi rq m hm hrq hμ hz 11
  have hK : KTH = 12 := rfl
  rw [hK, ← aSt_eq_aLoop]
  exact h

end

end Work.Cert
