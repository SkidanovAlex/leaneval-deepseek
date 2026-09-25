import Mathlib
import Submission.NK.LocalAnabelian.Basic
import Submission.NK.LocalCFT.Units.EllRank.Defs
import Submission.NK.LocalCFT.Units.numIndexSubgroups_eq_nIdx

namespace NK.LocalCFT.Units

open scoped Classical

/-- The number of additive subgroups of index `n` of an additive commutative group `B`
equals the number of (multiplicative) subgroups of index `n` of `Multiplicative B`.

`AddSubgroup.toSubgroup` is an order isomorphism `AddSubgroup B ≃o Subgroup (Multiplicative B)`
and it preserves the index (`AddSubgroup.index_toSubgroup`), so it restricts to a bijection
between the subgroups of index `n` on the two sides. -/
theorem nIdx_eq_numIndexSubgroups_multiplicative (n : ℕ) (B : Type*) [AddCommGroup B] :
    NK.LocalCFT.Units.EllRank.nIdx n B =
      NK.LocalAnabelian.numIndexSubgroups n (Multiplicative B) := by
  unfold NK.LocalCFT.Units.EllRank.nIdx NK.LocalAnabelian.numIndexSubgroups
  refine Nat.card_congr (Equiv.subtypeEquiv AddSubgroup.toSubgroup.toEquiv ?_)
  intro K
  change K.index = n ↔ (AddSubgroup.toSubgroup K).index = n
  rw [AddSubgroup.index_toSubgroup]

/-- The identity on the underlying set, viewed as a group isomorphism between a subgroup
`V ≤ A` of a commutative group and the `Multiplicative`-structure on the corresponding
additive subgroup `↥(V.toAddSubgroup)`. -/
noncomputable def subtypeMulEquiv (A : Type*) [CommGroup A] (V : Subgroup A) :
    ↥V ≃* Multiplicative ↥(V.toAddSubgroup) where
  toFun x := Multiplicative.ofAdd ⟨Additive.ofMul (x : A), by
    rw [Additive.mem_toAddSubgroup]; exact x.2⟩
  invFun y := ⟨Additive.toMul ((Multiplicative.toAdd y : ↥(V.toAddSubgroup)) : Additive A), by
    have hy := (Multiplicative.toAdd y : ↥(V.toAddSubgroup)).2
    rw [Additive.mem_toAddSubgroup] at hy
    exact hy⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

theorem numIndexSubgroups_eq_nIdx_subtype (n : ℕ) (A : Type*) [CommGroup A] (V : Subgroup A) :
    NK.LocalAnabelian.numIndexSubgroups n V =
      NK.LocalCFT.Units.EllRank.nIdx n ↥(V.toAddSubgroup) := by
  rw [nIdx_eq_numIndexSubgroups_multiplicative n ↥(V.toAddSubgroup)]
  exact NK.LocalAnabelian.numIndexSubgroups_congr (subtypeMulEquiv A V) n

end NK.LocalCFT.Units
