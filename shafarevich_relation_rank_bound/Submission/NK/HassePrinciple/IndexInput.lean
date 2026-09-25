/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Hasse principle from a local-degree condition (no cohomology in the input)

Umbrella development: `Submission/Work/HassePrinciple/` (README §15).

This module gives a third form of the input of the Hasse principle
`NK.BrauerHasse.Sha2Vanishing`, in which *no cohomology occurs at all*:

`NK.HassePrinciple.IndexInput p K K' κ κ'` — for every closed subgroup `U ≤ Gal(K'/K)`
isomorphic to `Gal(κ'/κ)` there is a place `A` of `K'` over a finite prime of `K` at whose
decomposition group the **local degree is prime to `p` at every finite level**:

  `∀ L : FiniteGaloisIntermediateField K K', Nat.Coprime ((localInclHom U A L).range).index p`.

The reduction is `NK.HassePrinciple.sha2Vanishing_of_indexInput`, and it is unconditional: the
transfer argument for finite groups (`NK.HassePrinciple.H2_map_injective_of_coprime_index`,
applied to the level-wise localisation) shows that at such a place the *level-wise* localisation
`locLevel` is injective, so a level class whose fine localisation vanishes at that place is already
zero — and the vanishing of the colimit localisation at that place supplies a level at which this
happens.

Two remarks on the status of the input.

* It is **strictly weaker than Neukirch's inert-place conclusion** `∃A, U ≤ D_A`: if `U` is
  contained in the decomposition group of `A`, the level groups coincide and the index is `1`
  (`NK.HassePrinciple.indexInput_of_inert`).  So `IndexInput` is implied by the conclusion of the
  local characterisation of decomposition groups — and it is a much weaker requirement: it only
  asks the local degree to avoid the prime `p`.
* It is **not** the Hasse principle in disguise as a formal statement: nothing in it mentions
  cohomology, localisation or the Brauer group.  It says that the arithmetic of `E = K'^U` is such
  that some place of `E` has a `p`-primary-free local extension tower over `K'.

For `p` odd and `U` `p`-adic, the field of the Neukirch–Uchida development, the relevant
quantitative input is Neukirch's rank count (`NK.HassePrinciple.RankInput`); `IndexInput` is the
cohomology-free sufficient condition recorded here because it is the sharpest statement of the
*arithmetic* content of the Hasse principle that this chapter can isolate.
-/

import Submission.NK.HassePrinciple.Defs
import Submission.NK.HassePrinciple.Inert
import Submission.NK.HassePrinciple.H2_map_injective_of_coprime_index
import Submission.NK.HassePrinciple.finite_levelGroup
import Submission.NK.HassePrinciple.loc_injective_of_le_stabSubgroup

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The level-wise localisation is injective where the local index is prime to `p` -/

/-- **The local inclusion of the level groups is injective**: `(U ⊓ D_A)/((U ⊓ D_A) ∩ G_L)` is a
subgroup of `U/(U ∩ G_L)`, by the standard isomorphism theorem for quotient maps
(`quotientGroupMap_injective_of_comap_le`). -/
lemma localInclHom_injective (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    Function.Injective (localInclHom U A L) := by
  rw [localInclHom]
  intro x y hxy
  exact quotientGroupMap_injective_of_comap_le (Subgroup.inclusion inf_le_left)
    (L.fixingSubgroup.subgroupOf U) (L.fixingSubgroup.subgroupOf (U ⊓ stabSubgroup A))
    (fun z hz => hz) (fun z hz => hz) hxy

/-- **The level-wise localisation at a place with prime-to-`p` local index is injective.**  This is
the transfer argument for finite groups: the restriction `H²(Γ_L, Z/p) → H²(Γ_A(L), Z/p)` is
followed by the corestriction back to a map which is multiplication by the index, an integer
invertible modulo `p` because the level cohomology is a `Z/p`-module
(`NK.HassePrinciple.H2_map_injective_of_coprime_index`). -/
theorem level_eq_zero_of_locLevel_eq_zero_of_coprime_index (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (L : FiniteGaloisIntermediateField K K')
    (h : Nat.Coprime (Subgroup.index (MonoidHom.range (localInclHom U A.1 L))) p)
    {a : LevelH2 p U L} (ha : (locLevel p U A.1 L) a = 0) : a = 0 := by
  have ha' : (H2.map (localInclHom U A.1 L)).hom a = 0 := ha
  exact (H2_map_injective_of_coprime_index (p := p) (localInclHom U A.1 L)
    (localInclHom_injective U A.1 L) h) (by simp [ha'])

/-! ## The input and the reduction -/

section Input

variable {p : ℕ} {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The local-degree input of the Hasse principle.**  For every closed subgroup `U ≤ Gal(K'/K)`
isomorphic to `Gal(κ'/κ)` there is a place `A` of `K'` over a finite prime of `K` such that, at
every finite Galois level `L`, the local level group `(U ⊓ D_A)/((U ⊓ D_A) ∩ Gal(K'/L))` has index
prime to `p` in the level group `U/(U ∩ Gal(K'/L))`.

Equivalently: the local degree of `K'`-over-`K` at `A`, measured inside `U`, has no factor `p` at any
finite level.  This is implied by Neukirch's conclusion `∃A, U ≤ D_A`
(`NK.HassePrinciple.indexInput_of_inert`, where the index is `1`) and it is much weaker. -/
def IndexInput (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) →
      ∃ A : OverFinitePrime K K', ∀ L : FiniteGaloisIntermediateField K K',
        Nat.Coprime (Subgroup.index (MonoidHom.range (localInclHom U A.1 L))) p

/-- **The Hasse principle from the local-degree input.**  A class of `H²(U, Z/p)` whose localisation
vanishes at every place of `K'` over a finite prime of `K` is zero.

The proof: represent the class at a finite level `L`; at the place `A` supplied by the input, the
vanishing of the colimit localisation is witnessed at some finite level `M ≥ L`
(`loc_ofLevel_eq_zero_iff`), so the level class dies at `A` at the level `M`; the level-wise
localisation at `A` is injective at the level `M` (prime-to-`p` index, previous lemma), so the
inflated level class is already zero. -/
theorem sha2Vanishing_of_indexInput
    (h : IndexInput (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' := by
  intro U hU hκ x hx
  obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective (p := p) (U := U) x
  obtain ⟨A, hA⟩ := h U hU hκ
  obtain ⟨M, hLM, hM⟩ :=
    (loc_ofLevel_eq_zero_iff (K := K) (K' := K') p (U := U) A L a).mp (hx A)
  have hzero : (locLevel p U A.1 M) ((levelMap p (U := U) hLM) a) = 0 := by
    rw [levelMap_locLevel_apply]
    exact hM
  have hinf : (levelMap p (U := U) hLM) a = 0 :=
    level_eq_zero_of_locLevel_eq_zero_of_coprime_index p A M (hA M) hzero
  rw [← H2Profinite.ofLevel_levelMap (p := p) (U := U) hLM a, hinf]
  exact ofLevel_zero (p := p) (U := U) M

/-! ## The local-degree input is weaker than Neukirch's inert-place conclusion -/

/-- **If every labelled `U` is contained in the decomposition group of some place, then the
local-degree input holds**: at such a place the local and global level groups coincide, so the local
index is `1`, which is prime to `p`.  This shows that `IndexInput` is not vacuous: it is implied by
Neukirch's conclusion `∃A, U ≤ D_A`, which is the statement the consumer's development proves. -/
theorem indexInput_of_inert (p : ℕ)
    (h : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∃ A : OverFinitePrime K K', U ≤ stabSubgroup A.1) :
    IndexInput (K := K) (K' := K') (κ := κ) (κ' := κ') p := by
  intro U hU hκ
  obtain ⟨A, hA⟩ := h U hU hκ
  refine ⟨A, fun L => ?_⟩
  rw [show (MonoidHom.range (localInclHom U A.1 L)) = ⊤ from
    MonoidHom.range_eq_top.mpr (localInclHom_bijective_of_le_stabSubgroup A.1 hA L).2,
    Subgroup.index_top]
  exact Nat.coprime_one_left p


/-- **The consumer-facing corollary of the local-degree route**: from `NK.HassePrinciple.IndexInput`
together with the local Brauer input `NK.BrauerHasse.LocalH2Input`, every non-zero class of
`H²(H, Z/p)` (`H ≤ Gal(K'/K)` closed and isomorphic to `Gal(κ'/κ)`) has a non-zero local component at
some place of `K'` over a finite prime of `K`. -/
theorem exists_loc_ne_zero_of_indexInput_and_localH2Input
    (h : IndexInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (_hl : NK.BrauerHasse.LocalH2Input p K K' κ κ') (H : Subgroup Gal(K'/K))
    (hH : IsClosed (H : Set Gal(K'/K))) (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  NK.BrauerHasse.exists_loc_ne_zero p (sha2Vanishing_of_indexInput h) H hH hκ hx


/-- **Neukirch's characterisation of decomposition groups from the local-degree input**: a closed,
self-normalising subgroup `H ≤ Gal(K'/K)` isomorphic to the absolute Galois group of a `p`-adic
field is the decomposition group of a place of `K'` over a finite prime of `K`, with the
Hasse-principle hypothesis discharged by `NK.HassePrinciple.IndexInput` (no cohomology in the
input). -/
theorem exists_decompositionGroup_of_indexInput {p : ℕ} (hp : p.Prime)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H) (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (hLoc : NK.BrauerHasse.LocalH2Input p K K' κ κ')
    (h : IndexInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hStep : NK.BrauerHasse.LocalDecompositionCriterion p K K' κ κ') :
    ∃ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ ∧
      MulAction.stabilizer Gal(K'/K) A = H :=
  NK.BrauerHasse.exists_decompositionGroup_of_localGalois p hp H hH hN hκ hLoc
    (sha2Vanishing_of_indexInput h) hStep

end Input

end NK.HassePrinciple
