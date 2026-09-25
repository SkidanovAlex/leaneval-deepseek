import Mathlib
import Submission.NK.HassePrinciple.LevelCoincidence
import Submission.NK.HassePrinciple.loc_injective_of_le_stabSubgroup

/-!
# `U ≤ D_A` if and only if the local level inclusions are surjective

Let `U ≤ Gal(K'/K)` be a subgroup and `A` a place of `K'` with decomposition group
`D_A = stabSubgroup A`.  For every finite Galois intermediate field `L` the *local level group*
`(U ⊓ D_A)/((U ⊓ D_A) ∩ Gal(K'/L))` maps into the (global) level group `U/(U ∩ Gal(K'/L))` by
`localInclHom U A L`, the map induced by the inclusion `U ⊓ D_A ↪ U`.

This module proves the equivalence

`U ≤ D_A ↔ ∀ L, Surjective (localInclHom U A L)`.

* `⟹` is the easy half: if `U ≤ D_A` then `U ⊓ D_A = U` and the inclusion is the identity on the
  underlying groups, so the induced quotient map is bijective
  (`localInclHom_bijective_of_le_stabSubgroup`).
* `⟸` is the substantive half.  Surjectivity at the level `L` says that every coset `u·(U ∩ G_L)`
  with `u ∈ U` has a representative in `U ⊓ D_A`; unwinding the quotient (this is the general group
  theoretic lemma `le_sup_of_surjective_inclusionQuotient` below) it says exactly
  `U ≤ D_A ⊔ G_L`, where `G_L = Gal(K'/L) = L.fixingSubgroup`.  As this holds for *every* level
  `L`, the profinite identity `⋂_L (D_A ⊔ G_L) = D_A`
  (`iInf_sup_fixingSubgroup_eq_stabSubgroup`, via `le_stabSubgroup_of_forall_le_sup_fixingSubgroup`)
  forces `U ≤ D_A`.

The reverse direction is the reason the Hasse principle has to be formulated with surjectivity
rather than with the level-wise bijectivity: the local and the global level systems coincide only
above an inert place.

## Main results

* `NK.HassePrinciple.le_sup_of_surjective_inclusionQuotient` — the abstract group-theoretic core;
* `NK.HassePrinciple.le_sup_fixingSubgroup_of_surjective` — its level-wise form at a place;
* `NK.HassePrinciple.le_stabSubgroup_iff_localInclHom_surjective` — the equivalence.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

/-! ## The abstract group-theoretic core -/

/-- **A surjective quotient inclusion forces `U ≤ D ⊔ N`.**  Let `U, D, N ≤ G` with `N` normal and
consider the map `(U ⊓ D)/(N ∩ (U ⊓ D)) →* U/(N ∩ U)` induced by the inclusion `U ⊓ D ↪ U`.  If it
is surjective, then `U ≤ D ⊔ N`.

Indeed, surjectivity applied to the class of `u ∈ U` produces `v ∈ U ⊓ D` and `z ∈ N ∩ U` with
`u = v·z`; as `v ∈ D` and `z ∈ N`, this gives `u ∈ D ⊔ N`.  (For `U ≤ D` the hypothesis is
automatic and the conclusion holds trivially; the content is the converse, which is what the
application to decomposition groups needs.) -/
lemma le_sup_of_surjective_inclusionQuotient {G : Type u} [Group G] {U D N : Subgroup G}
    [N.Normal]
    (h : Function.Surjective (QuotientGroup.map (N.subgroupOf (U ⊓ D)) (N.subgroupOf U)
      (Subgroup.inclusion (inf_le_left : U ⊓ D ≤ U)) (fun x hx => by simpa using hx))) :
    U ≤ D ⊔ N := by
  intro u hu
  obtain ⟨x, hx⟩ := h (QuotientGroup.mk' (N.subgroupOf U) ⟨u, hu⟩)
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf (U ⊓ D)) x
  have hx' : ((Subgroup.inclusion (inf_le_left : U ⊓ D ≤ U) v : ↥U) : ↥U ⧸ N.subgroupOf U)
      = QuotientGroup.mk' (N.subgroupOf U) ⟨u, hu⟩ := by
    simpa only [QuotientGroup.map_mk'] using hx
  obtain ⟨z, hz, hz'⟩ := (QuotientGroup.mk'_eq_mk' (N := N.subgroupOf U)).mp hx'
  have hzN : (z : G) ∈ N := (Subgroup.mem_subgroupOf).mp hz
  have huv : u = (v : G) * (z : G) := by
    have h1 := congrArg (Subtype.val) hz'
    simp only [Subgroup.coe_mul, Subgroup.coe_inclusion] at h1
    exact h1.symm
  rw [huv]
  exact mul_mem (Subgroup.mem_sup_left v.2.2) (Subgroup.mem_sup_right hzN)

/-! ## The level-wise form at a place -/

/-- **Surjectivity of the local level inclusion at `L` forces `U ≤ D_A ⊔ Gal(K'/L)`.**  This is
`le_sup_of_surjective_inclusionQuotient` for `N = Gal(K'/L) = L.fixingSubgroup` and
`D = D_A = stabSubgroup A`; the inclusions `(U ⊓ D_A)/(...) →* U/(...)` of the two lemmas
coincide by definition of `localInclHom`. -/
lemma le_sup_fixingSubgroup_of_surjective {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] {U : Subgroup Gal(K'/K)} (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K')
    (h : Function.Surjective (localInclHom U A L)) :
    U ≤ stabSubgroup A ⊔ L.fixingSubgroup :=
  le_sup_of_surjective_inclusionQuotient (U := U) (D := stabSubgroup A) (N := L.fixingSubgroup) h

/-! ## The equivalence -/

theorem le_stabSubgroup_iff_localInclHom_surjective {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K'] {U : Subgroup Gal(K'/K)} (A : ValuationSubring K') : U ≤ NK.BrauerHasse.stabSubgroup A ↔ ∀ L : FiniteGaloisIntermediateField K K', Function.Surjective (NK.BrauerHasse.localInclHom U A L) := by
  constructor
  · -- If `U ≤ D_A` the local and the global level groups coincide, so the inclusion is bijective.
    intro hU L
    exact (localInclHom_bijective_of_le_stabSubgroup A hU L).2
  · -- Surjectivity at every level gives `U ≤ D_A ⊔ Gal(K'/L)` for every `L`; the intersection of
    -- these over a cofinal family of levels is exactly the closed subgroup `D_A`.
    intro h
    exact le_stabSubgroup_of_forall_le_sup_fixingSubgroup A
      fun L => le_sup_fixingSubgroup_of_surjective A L (h L)

end NK.HassePrinciple
