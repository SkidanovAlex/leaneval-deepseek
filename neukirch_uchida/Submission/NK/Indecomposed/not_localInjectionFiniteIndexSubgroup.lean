import Mathlib
import Submission.NK.LocalDecomposition.Defs

/-!
# `NK.Indecomposed.not_localInjectionFiniteIndexSubgroup`

The general form `NK.LocalDecomposition.LocalInjectionFiniteIndexSubgroup κ κ'` of Neukirch's
Korollar 1 is *unsatisfiable* whenever there is at least one place `𝔮` of a number field whose
local absolute Galois group `Gal(L'/L_𝔮)` is infinite (which holds for every finite prime):
the statement quantifies over *all* intermediate fields `κ₀` of `κ'/κ`, and at `κ₀ = ⊤` the group
`Gal(κ'/↥⊤) = Gal(κ'/κ')` is trivial, so `H = ⊥` is an admissible subgroup of
`Gal(L'/L_𝔮)`, and the required conclusion `0 < H.relIndex ⊤ = Nat.card Gal(L'/L_𝔮)` fails because
an infinite group has `Nat.card = 0`.

The hypothesis `hInf : Infinite (Gal(L'/𝔮.adicCompletion L))` isolates exactly the arithmetic input
used; the refutation itself is purely group-theoretic.
-/
universe u

namespace NK.Indecomposed

theorem not_localInjectionFiniteIndexSubgroup {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] (L : Type u) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (hInf : Infinite (Gal(L'/𝔮.adicCompletion L))) :
    ¬ NK.LocalDecomposition.LocalInjectionFiniteIndexSubgroup κ κ' := by
  classical
  intro h
  -- `Gal(κ'/↥⊤) = Gal(κ'/κ')` is trivial: it consists of the automorphisms of `κ'` fixing `κ'`.
  have hsub : Subsingleton (Gal(κ'/↥(⊤ : IntermediateField κ κ'))) := by
    constructor
    intro f g
    refine AlgEquiv.ext (fun x => ?_)
    obtain ⟨r, hr⟩ : ∃ r : ↥(⊤ : IntermediateField κ κ'),
        algebraMap ↥(⊤ : IntermediateField κ κ') κ' r = x :=
      ⟨⟨x, by simp⟩, by rw [IntermediateField.algebraMap_apply]⟩
    rw [← hr, AlgEquiv.commutes, AlgEquiv.commutes]
  -- Hence the trivial subgroup is admissible for the universal quantifier over `H`.
  have hne : Nonempty ((⊥ : Subgroup Gal(L'/𝔮.adicCompletion L)) ≃*
      Gal(κ'/↥(⊤ : IntermediateField κ κ'))) :=
    ⟨{ toFun := fun _ => 1
       invFun := fun _ => 1
       left_inv := fun x => Subsingleton.elim _ _
       right_inv := fun y => Subsingleton.elim _ _
       map_mul' := fun x y => by simp }⟩
  -- Apply the (alleged) statement at `κ₀ = ⊤`, `H = ⊥`.
  have h1 := h ⊤ L 𝔮 L' ⊥ hne
  -- `⊥.relIndex ⊤ = Nat.card Gal(L'/L_𝔮) = 0` because the group is infinite.
  rw [Subgroup.relIndex_top_right, Subgroup.index_bot,
    Nat.card_eq_zero.mpr (Or.inr hInf)] at h1
  exact absurd h1 (by simp)

end NK.Indecomposed
