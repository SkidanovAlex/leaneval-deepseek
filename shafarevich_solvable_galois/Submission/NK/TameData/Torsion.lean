import Mathlib.GroupTheory.Torsion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameData

universe u

/-! ## Torsion subgroups and `Nat.card` -/

/-- **The torsion subgroup of an abelian group is, as a type, the type of elements of finite
order.** -/
theorem natCard_torsion_eq_natCard_isOfFinOrder (G : Type u) [CommGroup G] :
    Nat.card ↥(CommGroup.torsion G) = Nat.card {x : G // IsOfFinOrder x} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => CommGroup.mem_torsion x)

/-- **The elements of finite order in a product are the pairs of elements of finite order**, so
their number is the product of the numbers of torsion elements of the two factors. -/
theorem natCard_isOfFinOrder_prod (A : Type u) (B : Type u) [Monoid A] [Monoid B] :
    Nat.card {x : A × B // IsOfFinOrder x} =
      Nat.card {a : A // IsOfFinOrder a} * Nat.card {b : B // IsOfFinOrder b} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr ((Equiv.subtypeEquivRight fun x : A × B => IsOfFinOrder.prod_iff).trans
    Equiv.subtypeProdEquivProd)

/-- **A torsion-free group has exactly one element of finite order**, namely `1`. -/
theorem natCard_isOfFinOrder_eq_one (G : Type u) [Monoid G] [IsMulTorsionFree G] :
    Nat.card {x : G // IsOfFinOrder x} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, IsOfFinOrder.one⟩⟩⟩
  rw [(isOfFinOrder_iff_eq_one a.1).mp a.2, (isOfFinOrder_iff_eq_one b.1).mp b.2]

/-- **Every element of a finite cyclic group has finite order**: the number of elements of finite
order of `Multiplicative (ZMod n)` (for `n ≠ 0`) is `n`. -/
theorem natCard_isOfFinOrder_multiplicative_zmod (n : ℕ) [NeZero n] :
    Nat.card {x : Multiplicative (ZMod n) // IsOfFinOrder x} = n := by
  have h : ∀ x : Multiplicative (ZMod n), IsOfFinOrder x := fun x => by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, NeZero.pos n, by ext; simp [toAdd_pow]⟩
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv h), Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card]

end NK.TameData
