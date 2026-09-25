import Mathlib
import Submission.NK.NUV2.ArtinBridge.KummerSUnitField
import Submission.NK.GlobalCFTdeep.SecondInequality.finrank_kummerAdjoin
import Submission.NK.GlobalCFTdeep.SecondInequality.tUnits_index_powSubgroup

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct

noncomputable section

namespace NK.NUV2.ArtinBridge

/-- The Kummer `S`-field `K(U(S)^{1/p})` is finite dimensional over `K`.

Route: `finiteDimensional_kummerAdjoin_of_finite` applies with the subgroup
`T = TUnits S ⊔ Kˣ^p` (the inclusion `Kˣ^p ≤ T` is `le_sup_right`), and the quotient
`T ⧸ Kˣ^p` is finite because it is `(TUnits S).(TUnits S)^p` (`tUnits_inf_powSubgroup`) and
`tUnits_index_powSubgroup` gives that index as `p ^ Nat.card S`. -/
theorem finiteDimensional_kummerSUnitField {K : Type} [Field K] [NumberField K] {Ω : Type*}
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] {p : ℕ} (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S) :
    FiniteDimensional K ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S) := by
  classical
  -- `T = U ⊔ Kˣ^p` with `U = TUnits S` the group of `S`-units.
  set U : Subgroup Kˣ :=
    NK.GlobalCFTdeep.TUnits (L := K) (S : Set (NK.GlobalCFT.Place K)) with hU
  set P : Subgroup Kˣ := NK.LocalAnabelian.powSubgroup p K with hP
  -- the hypothesis on `S` in terms of `Place.IsInfinite`
  have hinfS : ∀ w : NK.GlobalCFT.Place K, w.IsInfinite → w ∈ S := by
    intro w hw
    obtain ⟨w', rfl⟩ := NK.GlobalCFT.Place.isInfinite_iff.mp hw
    exact hSinf w'
  -- `U ⊓ Kˣ^p = U^p`
  have hUP : U ⊓ P = Subgroup.map (powMonoidHom p) U :=
    NK.NUV2.ArtinBridge.tUnits_inf_powSubgroup hp S
  -- `[U : U^p] = p ^ |S|`
  have hindexU : ((Subgroup.map (powMonoidHom p) U).subgroupOf U).index = p ^ Nat.card S :=
    NK.GlobalCFTdeep.SecondInequality.tUnits_index_powSubgroup p hp hζ S hinfS
  -- the index of `Kˣ^p` in `T = U ⊔ Kˣ^p` is `[(U ⊓ Kˣ^p) : U] = [U^p : U]`, by the second
  -- isomorphism theorem for the pair `(U, Kˣ^p)`.
  have hidx : (P.subgroupOf (U ⊔ P)).index = p ^ Nat.card S := by
    change P.relIndex (U ⊔ P) = p ^ Nat.card S
    rw [Subgroup.relIndex_sup_right U P,
      (Subgroup.inf_relIndex_left U P).symm,
      show (U ⊓ P) = Subgroup.map (powMonoidHom p) U from hUP]
    exact hindexU
  -- hence `T ⧸ Kˣ^p` is finite
  haveI : Finite (↥(U ⊔ P) ⧸ (P.subgroupOf (U ⊔ P))) := by
    refine (Nat.card_ne_zero.mp ?_).2
    rw [← Subgroup.index_eq_card, hidx]
    exact pow_ne_zero _ hp.ne_zero
  -- Kummer theory then gives the finiteness of the degree
  exact NK.GlobalCFTdeep.SecondInequality.finiteDimensional_kummerAdjoin_of_finite
    (K' := Ω) hp hζ (U ⊔ P) le_sup_right

end NK.NUV2.ArtinBridge
