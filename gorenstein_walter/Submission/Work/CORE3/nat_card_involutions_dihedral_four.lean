import Mathlib

/-!
# The involutions of `DihedralGroup 4`

`DihedralGroup 4` is the dihedral group of order `8` (the symmetry group of the square),
with elements `r i` (`i : ZMod 4`) and `sr i` (`i : ZMod 4`).

* every reflection `sr i` has order `2` (`DihedralGroup.orderOf_sr`);
* a rotation `r i` has order `4 / gcd 4 i.val`, hence order `2` only for `i = 2`.

So the group has exactly five involutions: the central rotation `r 2` and the four reflections.
We prove this by exhibiting an explicit equivalence between `{x // orderOf x = 2}` and
`ZMod 4 ⊕ Unit`, and computing the cardinality of the latter.
-/

namespace Work.CORE3

open DihedralGroup

/-- The only rotation in `DihedralGroup 4` (the dihedral group of order `8`) of order two is
`r 2`. -/
lemma r_eq_two_of_orderOf_eq_two {i : ZMod 4} (h : orderOf (DihedralGroup.r i) = 2) :
    i = 2 := by
  have h4 : orderOf (DihedralGroup.r i) = 4 / Nat.gcd 4 i.val := DihedralGroup.orderOf_r i
  rw [h4] at h
  have hgcd : Nat.gcd 4 i.val = 2 := by
    have hdvd : Nat.gcd 4 i.val ∣ 4 := Nat.gcd_dvd_left 4 i.val
    have h2 := Nat.div_mul_cancel hdvd
    rw [h] at h2
    omega
  have hne0 : i.val ≠ 0 := by
    intro h0
    rw [h0] at hgcd
    norm_num at hgcd
  have hdvd2 : 2 ∣ i.val := hgcd ▸ Nat.gcd_dvd_right 4 i.val
  have hlt : i.val < 4 := ZMod.val_lt i
  have hval : i.val = 2 := by omega
  rw [← ZMod.natCast_zmod_val i, hval]
  norm_num

/-- The central rotation `r 2` is an involution. -/
lemma orderOf_r_two : orderOf (DihedralGroup.r 2 : DihedralGroup 4) = 2 := by
  rw [DihedralGroup.orderOf_r]
  decide

/-- The involutions of `DihedralGroup 4` are the four reflections together with the central
rotation `r 2`. -/
noncomputable def d4InvolutionEquiv :
    {x : DihedralGroup 4 // orderOf x = 2} ≃ (ZMod 4 ⊕ Unit) where
  toFun x := match x.1 with
    | DihedralGroup.r _ => Sum.inr ()
    | DihedralGroup.sr i => Sum.inl i
  invFun y := match y with
    | Sum.inl i => ⟨DihedralGroup.sr i, DihedralGroup.orderOf_sr i⟩
    | Sum.inr _ => ⟨DihedralGroup.r 2, orderOf_r_two⟩
  left_inv x := by
    obtain ⟨y, hy⟩ := x
    rcases y with i | i
    · exact Subtype.ext (congrArg DihedralGroup.r (r_eq_two_of_orderOf_eq_two hy).symm)
    · exact Subtype.ext rfl
  right_inv y := by
    rcases y with i | u
    · rfl
    · exact congrArg Sum.inr (Subsingleton.elim u ())

theorem nat_card_involutions_dihedral_four :
    Nat.card {x : DihedralGroup 4 // orderOf x = 2} = 5 := by
  rw [Nat.card_congr d4InvolutionEquiv, Nat.card_sum, Nat.card_zmod, Nat.card_unique]

end Work.CORE3
