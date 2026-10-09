import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.SetTheory.Cardinal.Finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.GroupTheory.Hom

/-- For an additive group homomorphism `f : A →+ B`, the cardinality of the domain `A` is
the product of the cardinalities of the range and the kernel of `f`.  Since `Nat.card` of an
infinite type is `0`, the statement also covers the case where `A` is infinite.

Proof: choosing, for each element of the range, one preimage gives a set-theoretic
bijection `A ≃ f.range × f.ker` (`x ↦ (f x, x - s (f x))`, inverse `(y, k) ↦ k + s y`),
so `Nat.card A = Nat.card (f.range × f.ker) = Nat.card f.range * Nat.card f.ker`. -/
lemma card_range_mul_card_ker_add {A B : Type*} [AddGroup A] [AddGroup B] (f : A →+ B) :
    Nat.card ↥f.range * Nat.card ↥f.ker = Nat.card A := by
  classical
  -- Choose, for each element `y` of the range, a preimage `s y`.
  let s : f.range → A := fun y => Classical.choose (AddMonoidHom.mem_range.mp y.2)
  have hs : ∀ y : f.range, f (s y) = y.1 := by
    intro y
    exact Classical.choose_spec (AddMonoidHom.mem_range.mp y.2)
  -- The forward map `x ↦ (f x, x - s (f x))`.
  let toFun : A → f.range × f.ker := fun x =>
    ⟨⟨f x, AddMonoidHom.mem_range.mpr ⟨x, rfl⟩⟩,
     ⟨x - s ⟨f x, AddMonoidHom.mem_range.mpr ⟨x, rfl⟩⟩,
       (AddMonoidHom.mem_ker).mpr (by
         rw [f.map_sub, hs ⟨f x, AddMonoidHom.mem_range.mpr ⟨x, rfl⟩⟩, sub_self])⟩⟩
  -- The inverse map `(y, k) ↦ k + s y`.
  let invFun : f.range × f.ker → A := fun yk => yk.2.1 + s yk.1
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    dsimp [invFun, toFun]
    rw [sub_add_cancel]
  have hright : Function.RightInverse invFun toFun := by
    intro yk
    rcases yk with ⟨y, k⟩
    have hf1 : f (k.1 + s y) = y.1 := by
      rw [f.map_add, AddMonoidHom.mem_ker.mp k.2, hs y, zero_add]
    have hsnd : k.1 + s y - s ⟨f (k.1 + s y), AddMonoidHom.mem_range.mpr ⟨k.1 + s y, rfl⟩⟩ = k.1 := by
      have hsub : (⟨f (k.1 + s y), AddMonoidHom.mem_range.mpr ⟨k.1 + s y, rfl⟩⟩ : f.range) = y :=
        Subtype.ext hf1
      rw [congrArg s hsub, add_sub_cancel_right]
    apply Prod.ext
    · dsimp [toFun, invFun]
      exact Subtype.ext hf1
    · dsimp [toFun, invFun]
      exact Subtype.ext hsnd
  have hequiv : A ≃ f.range × f.ker := ⟨toFun, invFun, hleft, hright⟩
  calc
    Nat.card ↥f.range * Nat.card ↥f.ker = Nat.card (f.range × f.ker) := (Nat.card_prod f.range f.ker).symm
    _ = Nat.card A := (Nat.card_congr hequiv).symm

end Commons.GroupTheory.Hom