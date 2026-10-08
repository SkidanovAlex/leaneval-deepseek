/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# Number of conjugates of a subgroup

The orbit–stabiliser theorem for the conjugation action of a group `G` on its subgroups:
the set `{P^g | g : G}` of conjugates of a subgroup `P` has cardinality equal to the index
of the normaliser `N_G(P)`.

The conjugation action on subgroups is available in Mathlib under the `Pointwise` locale as the
action of `ConjAct G` on `Subgroup G` (`Subgroup.pointwiseMulAction`).  The two identifications
needed are

* `toConjAct_smul_eq_conjSub` : `(toConjAct g) • P = conjSub g P`,
* `stabilizer_eq` : the stabiliser of `P` is `N_G(P)` pulled back along `ConjAct.ofConjAct`,

and the result is then `MulAction.index_stabilizer` together with
`Subgroup.index_comap_of_surjective`.
-/
import Mathlib
import Submission.Work.CORE4.Defs

open scoped Pointwise

namespace Work.CORE4

/-- Conjugating a subgroup by `g : G` agrees with acting on it by `ConjAct.toConjAct g`. -/
private lemma toConjAct_smul_eq_conjSub {G : Type} [Group G] (P : Subgroup G) (g : G) :
    ConjAct.toConjAct g • P = Work.GW2.conjSub g P := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    refine ⟨s, hs, ?_⟩
    rw [← hxs, ConjAct.toConjAct_smul_eq_mulAut_conj, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  · intro hx
    rw [Work.GW2.conjSub, Subgroup.mem_map] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    refine ⟨s, hs, ?_⟩
    rw [ConjAct.toConjAct_smul_eq_mulAut_conj]
    simpa using hxs

/-- The `G`-orbit of `P` under conjugation is the set of conjugates of `P`. -/
private lemma orbit_eq {G : Type} [Group G] (P : Subgroup G) :
    MulAction.orbit (ConjAct G) P = {X : Subgroup G | ∃ g : G, X = Work.GW2.conjSub g P} := by
  ext X
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨a, rfl⟩
    have h := toConjAct_smul_eq_conjSub P (ConjAct.ofConjAct a)
    rw [ConjAct.toConjAct_ofConjAct] at h
    exact ⟨ConjAct.ofConjAct a, h⟩
  · rintro ⟨g, rfl⟩
    exact ⟨ConjAct.toConjAct g, toConjAct_smul_eq_conjSub P g⟩

/-- The stabiliser of `P` in the conjugation action is the normaliser of `P` in `G`,
pulled back along `ConjAct.ofConjAct`. -/
private lemma stabilizer_eq {G : Type} [Group G] (P : Subgroup G) :
    MulAction.stabilizer (ConjAct G) P
      = Subgroup.comap ConjAct.ofConjAct.toMonoidHom (Subgroup.normalizer (P : Set G)) := by
  ext a
  rw [MulAction.mem_stabilizer_iff]
  show a • P = P ↔ ConjAct.ofConjAct a ∈ Subgroup.normalizer (P : Set G)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h := toConjAct_smul_eq_conjSub P (ConjAct.ofConjAct a)
  rw [ConjAct.toConjAct_ofConjAct] at h
  rw [h]
  rfl

theorem ConjSubgroupCount (G : Type) [Group G] [Finite G] (P : Subgroup G) :
    {X : Subgroup G | ∃ g : G, X = Work.GW2.conjSub g P}.ncard =
      (Subgroup.normalizer (P : Set G)).index := by
  rw [← orbit_eq P]
  rw [← MulAction.index_stabilizer (ConjAct G) P]
  rw [stabilizer_eq P]
  exact Subgroup.index_comap_of_surjective (Subgroup.normalizer (P : Set G))
    ConjAct.ofConjAct.surjective

end Work.CORE4
