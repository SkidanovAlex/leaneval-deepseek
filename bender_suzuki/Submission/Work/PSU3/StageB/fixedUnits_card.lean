import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.GaloisField.fixedField_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

/-- The `σE`-fixed units of `E n = GF(2^(2n))` are the nonzero `σE`-fixed elements of `E n`:
the unit `a` is sent to its field element `↑a`, and a nonzero fixed element `x` back to
`Units.mk0 x`. -/
noncomputable def fixedUnitsEquiv (n : ℕ) :
    {a : (Work.PSU3.E n)ˣ // Work.PSU3.σE (a : Work.PSU3.E n) = a} ≃
      {x : Work.PSU3.E n // Work.PSU3.σE x = x ∧ x ≠ 0} where
  toFun a := ⟨(a.1 : Work.PSU3.E n), a.2, Units.ne_zero a.1⟩
  invFun x := ⟨Units.mk0 x.1 x.2.2, by rw [Units.val_mk0]; exact x.2.1⟩
  left_inv a := by
    apply Subtype.ext
    apply Units.ext
    exact Units.val_mk0 (Units.ne_zero a.1)
  right_inv x := by
    apply Subtype.ext
    exact Units.val_mk0 x.2.2

/-- The number of nonzero `σE`-fixed elements of `E n = GF(2^(2n))` is `2 ^ n - 1`: there are
`2 ^ n` fixed elements in all (the fixed field `GF(2 ^ n)`), and exactly one of them is `0`. -/
theorem fixedNonzero_card (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {x : Work.PSU3.E n // Work.PSU3.σE x = x ∧ x ≠ 0} = 2 ^ n - 1 := by
  classical
  have hfixed : Nat.card {x : Work.PSU3.E n // Work.PSU3.σE x = x} = 2 ^ n :=
    Work.PSU3.GaloisField.fixedField_card n hn
  have hcoe1 : Nat.card {x : Work.PSU3.E n // Work.PSU3.σE x = x ∧ x ≠ 0} =
      ({x : Work.PSU3.E n | Work.PSU3.σE x = x ∧ x ≠ 0}).ncard := Nat.card_coe_set_eq _
  have hcoe2 : ({x : Work.PSU3.E n | Work.PSU3.σE x = x ∧ x ≠ 0}) =
      ({x : Work.PSU3.E n | Work.PSU3.σE x = x} \ {0}) := by
    ext x; simp
  rw [hcoe1, hcoe2]
  have hzero : (0 : Work.PSU3.E n) ∈ {x : Work.PSU3.E n | Work.PSU3.σE x = x} := by simp
  have h := Set.ncard_sdiff_singleton_add_one hzero
  have hsn : ({x : Work.PSU3.E n | Work.PSU3.σE x = x}).ncard = 2 ^ n := by
    rw [← Nat.card_coe_set_eq]; exact hfixed
  rw [hsn] at h
  exact Nat.eq_sub_of_add_eq h

theorem fixedUnits_card (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {a : (Work.PSU3.E n)ˣ // Work.PSU3.σE (a : Work.PSU3.E n) = a} = 2 ^ n - 1 := by
  rw [Nat.card_congr (fixedUnitsEquiv n)]
  exact fixedNonzero_card n hn

end Work.PSU3.StageB
