import Mathlib
import Submission.Work.C17.lead_defs
import Submission.Work.C17.lead_api
import Submission.Work.C17.reg_sigma

/-!
# The local ratio `ρ = (x-1)⁻¹ = σ(x)/x` of the deck involution at `0`

The deck involution `σ : x ↦ x/(x-1)` of `ℚ(x)` acts on the local parameter at the fixed point
`x = 0` by `σ(x) = x·ρ` with `ρ = (x-1)⁻¹`.  Here `ρ` is a unit of the local ring at `0`
(`ordAtT 0 ρ = 0`) whose value at `0` is `-1`, so that `σ` is a local isomorphism at `0` with
differential `-1`.

This module collects the elementary facts about `ρ` used by `Work.C17.sigma_lead`.
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc

noncomputable section

/-- `ρ = (x-1)⁻¹`: the ratio `σ(x)/x` of the deck involution at the fixed point `0`. -/
def rhoS : RatFunc ℚ := (xQ - 1)⁻¹

theorem xQ_sub_one_ne_zero_sigma_defs : (xQ - 1 : RatFunc ℚ) ≠ 0 := unit0_ne_zero unit0_X_sub_one

theorem rhoS_ne_zero : rhoS ≠ 0 := by
  rw [rhoS]; exact inv_ne_zero xQ_sub_one_ne_zero_sigma_defs

theorem unit0_rhoS : Unit0 rhoS := by
  rw [rhoS]; exact unit0_inv unit0_X_sub_one

theorem reg_rhoS : Reg rhoS := unit0_to_reg unit0_rhoS

/-- `σ(x) = x·ρ`. -/
theorem sigmaQ_xQ_eq : sigmaQ xQ = xQ * rhoS := by
  rw [sigmaQ_X, rhoS, div_eq_mul_inv]

theorem unit0_pow {g : RatFunc ℚ} (hg : Unit0 g) (n : ℕ) : Unit0 (g ^ n) := by
  induction n with
  | zero => simpa using unit0_one
  | succ n ih => rw [pow_succ]; exact unit0_mul ih hg

/-- Integer powers of a unit of the local ring are regular at `0`. -/
theorem reg_zpow {g : RatFunc ℚ} (hg : Unit0 g) (e : ℤ) : Reg (g ^ e) := by
  rcases lt_or_ge 0 e with he | he
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (le_of_lt he)
    rw [hn, zpow_natCast]
    exact reg_pow (unit0_to_reg hg) n
  · have h0 : (0 : ℤ) ≤ -e := by omega
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h0
    have he' : e = -(n : ℤ) := by omega
    rw [he', zpow_neg, zpow_natCast]
    exact reg_inv_of_unit (unit0_pow hg n)

end

end Work.C17
