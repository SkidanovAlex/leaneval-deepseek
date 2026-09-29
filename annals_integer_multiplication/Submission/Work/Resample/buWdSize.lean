import Mathlib
import Submission.Work.Resample.buKit

namespace Work.Resample

open HvdH

set_option autoImplicit false

/-- The tabulated diagonal weight `buWd p α s t ℓ` is the quotient of the Horner iterate
`auH p (buZb p α s t ℓ) (auNstep p)` by a power of two; it therefore has the same uniform size
bound `buHQ p` as the iterates `auH`, hence `isz`-size `buSZ p`. -/
theorem buWdSize (p α s t : ℕ) (ℓ : ℤ) (hαp : α ^ 2 ≤ p) (hs : 0 < s) (hsp : s < 2 ^ p)
    (hp : 100 ≤ p) :
    (Work.Resample.buWd p α s t ℓ).natAbs ≤ 2 ^ (Work.Resample.buHQ p - 1) ∧
    HvdH.isz (Work.Resample.buWd p α s t ℓ) ≤ Work.Resample.buSZ p := by
  have hZb : (buZb p α s t ℓ).natAbs ≤ 2 ^ (11 * p + 210) :=
    le_trans (natAbs_buZb_le p α s t ℓ hαp hs hsp hp)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hH : (auH p (buZb p α s t ℓ) (auNstep p)).natAbs ≤ 2 ^ (buHQ p - 1) :=
    natAbs_auH_le_buHQ p (buZb p α s t ℓ) (auNstep p) hp hZb le_rfl
  have hwd : (Work.Resample.buWd p α s t ℓ).natAbs ≤ 2 ^ (Work.Resample.buHQ p - 1) := by
    unfold buWd
    rw [Int.natAbs_tdiv]
    exact le_trans (Nat.div_le_self _ _) hH
  exact ⟨hwd, isz_le_buSZ_of (by simp only [buSZ, buHQ]; omega) hwd⟩

end Work.Resample
