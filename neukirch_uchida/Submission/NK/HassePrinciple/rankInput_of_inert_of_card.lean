import Mathlib
import Submission.NK.HassePrinciple.RankInput
import Submission.NK.HassePrinciple.Inert
import Submission.NK.HassePrinciple.locAt_bijective_of_le_stabSubgroup

/-!
# Neukirch's rank count from an inert place

This module assembles the two halves of Neukirch's input `NK.HassePrinciple.RankInput`:

* the local computation `card_global` (`H²(U, Z/p)` finite of order at most `p`), which is passed
  in as a hypothesis `hcard` — this is local Tate duality at `κ`;
* the rank count `rank`: for every closed labelled `U`, a place `A` whose decomposition group
  contains `U` (`hinert`) has, by
  `NK.HassePrinciple.locAt_bijective_of_le_stabSubgroup`, a *bijective* localisation
  `locAt p U A : H²(U, Z/p) → H²(U ⊓ D_A, Z/p)`.  A bijection is in particular a surjection whose
  target is at least as large as its source, which is exactly the `rank` field.

Note that the hypothesis `Nontrivial (H2Profinite p U)` of `RankInput.rank` is unused: at an inert
place the localisation is bijective irrespective of whether the group is trivial.
-/

universe u

namespace NK.HassePrinciple

/-- **Neukirch's input to the Hasse principle from an inert place.**  Suppose

* `hcard` — for every closed subgroup `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)`, the group
  `H²(U, Z/p)` is finite (local Tate duality at `κ`);
* `hinert` — for every such `U` there is a place `A` of `K'` over a finite prime of `K` whose
  decomposition group contains `U`.

Then `NK.HassePrinciple.RankInput p K K' κ κ'` holds: at the place `A` of `hinert` the
localisation is bijective (`locAt_bijective_of_le_stabSubgroup`), hence surjective with target at
least as large as source. -/
theorem rankInput_of_inert_of_card {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] (p : ℕ) (hp : p.Prime)
    (hcard : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) →
      Finite (NK.BrauerHasse.H2Profinite p U))
    (hinert : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∃ A : NK.BrauerHasse.OverFinitePrime K K',
        U ≤ NK.BrauerHasse.stabSubgroup A.1) :
    NK.HassePrinciple.RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p where
  hp := hp
  card_global := hcard
  rank U hU hκ _ := by
    obtain ⟨A, hA⟩ := hinert U hU hκ
    have hbij := locAt_bijective_of_le_stabSubgroup (K := K) (K' := K') p A hA
    exact ⟨A, hbij.2, (Nat.card_congr (Equiv.ofBijective _ hbij)).le⟩

end NK.HassePrinciple
