/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area DSTR, `Work.DSTR`)

# DS1 — heredity of the Sylow 2-shape (Bender 1981 §1.6)

`Work.DSTR.dihOrCycHered` proves `Work.GW2.DihOrCycHeredProp` from the two elementary
facts about the dihedral groups themselves (`Work.GW2.DihedralSubgroupProp`,
`Work.GW2.DihedralQuotientProp`): the shape "Sylow 2-subgroups are cyclic or dihedral"
passes to subgroups and to quotients.

The argument is pure Sylow bookkeeping around a `Prop`-valued predicate on groups,

* `DihOrCycType G := IsCyclic G ∨ ∃ n, G ≃* DihedralGroup n`

(`DihOrCycSylow X` is literally `∀ P : Sylow 2 X, DihOrCycType P`) together with the two
inheritance statements

* `dihOrCycType_subgroup` (uses `hsub`), and
* `dihOrCycType_quotient` (uses `hquo` and the first isomorphism theorem),

and the two Sylow reductions

* `sylowSubReduction`: a Sylow 2-subgroup of `K ≤ X` is isomorphic to a subgroup of a
  Sylow 2-subgroup of `X`, and
* `sylowQuotReduction`: a Sylow 2-subgroup of `X ⧸ N` is a quotient of a Sylow
  2-subgroup of `X` (Mathlib's `Sylow.mapSurjective_surjective`).
-/
import Mathlib
import Submission.Work.DSTR.Defs

open scoped MatrixGroups

namespace Work.DSTR

set_option linter.style.haveILetI false

/-! ## The shape predicate -/

/-- The shape "cyclic or dihedral" for a group.  This is the `Prop` that `DihOrCycSylow`
demands of each Sylow 2-subgroup. -/
def DihOrCycType (G : Type*) [Group G] : Prop :=
  IsCyclic G ∨ ∃ n : ℕ, Nonempty (G ≃* DihedralGroup n)

/-- The shape is invariant under isomorphism. -/
theorem dihOrCycType_mulEquiv_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    DihOrCycType G ↔ DihOrCycType H := by
  constructor
  · rintro (h | ⟨n, ⟨f⟩⟩)
    · exact .inl ((MulEquiv.isCyclic e).mp h)
    · exact .inr ⟨n, ⟨e.symm.trans f⟩⟩
  · rintro (h | ⟨n, ⟨f⟩⟩)
    · exact .inl ((MulEquiv.isCyclic e).mpr h)
    · exact .inr ⟨n, ⟨e.trans f⟩⟩

/-! ## Inheritance of the shape -/

/-- Subgroups of cyclic groups are cyclic, and by `hsub` subgroups of dihedral groups are
cyclic or dihedral; hence the shape passes to subgroups. -/
theorem dihOrCycType_subgroup (hsub : Work.GW2.DihedralSubgroupProp) {G : Type*} [Group G]
    (hG : DihOrCycType G) (S : Subgroup G) : DihOrCycType ↥S := by
  rcases hG with hc | ⟨n, ⟨e⟩⟩
  · haveI : IsCyclic G := hc
    exact .inl inferInstance
  · -- transport `S` into `DihedralGroup n` along `e` and apply `hsub`
    refine (dihOrCycType_mulEquiv_iff
      (Subgroup.equivMapOfInjective S e.toMonoidHom e.injective)).mpr ?_
    rcases hsub n (S.map e.toMonoidHom) with hc | ⟨m, ⟨f⟩⟩
    · exact .inl hc
    · exact .inr ⟨m, ⟨f⟩⟩

/-- Quotients of cyclic groups are cyclic, and by `hquo` quotients of dihedral groups are
cyclic or dihedral: a surjection from a group of the shape onto `H` exhibits `H` as a
quotient of that group (first isomorphism theorem). -/
theorem dihOrCycType_quotient (hquo : Work.GW2.DihedralQuotientProp) {G : Type*} [Group G]
    (hG : DihOrCycType G) (N : Subgroup G) [N.Normal] : DihOrCycType (G ⧸ N) := by
  rcases hG with hc | ⟨n, ⟨e⟩⟩
  · haveI : IsCyclic G := hc
    exact .inl (isCyclic_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N))
  · -- `Dₙ → G → G ⧸ N` is onto, so `G ⧸ N ≃* Dₙ ⧸ ker`
    let φ : DihedralGroup n →* G ⧸ N := (QuotientGroup.mk' N).comp e.symm.toMonoidHom
    have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective N).comp e.symm.surjective
    exact (dihOrCycType_mulEquiv_iff
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)).mp (hquo n φ.ker)

/-! ## Sylow reductions -/

/-- A Sylow 2-subgroup `Q` of `K ≤ X` is isomorphic to a subgroup of some Sylow
2-subgroup `P` of `X`: namely to its image under `K ↪ X`. -/
theorem sylowSubReduction {X : Type*} [Group X] (K : Subgroup X) (Q : Sylow 2 K) :
    ∃ (P : Sylow 2 X) (S : Subgroup X) (_e : ↥Q ≃* ↥S), S ≤ P := by
  have hQ : IsPGroup 2 (Subgroup.map K.subtype (Q : Subgroup K)) :=
    Q.isPGroup'.map K.subtype
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  exact ⟨P, Subgroup.map K.subtype (Q : Subgroup K),
    Subgroup.equivMapOfInjective (Q : Subgroup K) K.subtype K.subtype_injective, hP⟩

/-- A Sylow 2-subgroup `Q` of `X ⧸ N` is a quotient of a Sylow 2-subgroup `P` of `X`:
`Sylow.mapSurjective` makes the quotient homomorphism surjective on Sylow subgroups, and
the restriction of the quotient map to `P` is onto `Q`. -/
theorem sylowQuotReduction {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (Q : Sylow 2 (X ⧸ N)) : ∃ (P : Sylow 2 X) (φ : ↥P →* ↥Q), Function.Surjective φ := by
  have hf : Function.Surjective (QuotientGroup.mk' N : X →* X ⧸ N) :=
    QuotientGroup.mk'_surjective N
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hf 2 Q
  have hcoe : Subgroup.map (QuotientGroup.mk' N) (P : Subgroup X) = (Q : Subgroup (X ⧸ N)) := by
    rw [← Sylow.coe_mapSurjective hf P, hP]
  let F : ↥P →* (X ⧸ N) := (QuotientGroup.mk' N).comp (Subgroup.subtype (P : Subgroup X))
  have hF : ∀ x : ↥P, F x ∈ (Q : Subgroup (X ⧸ N)) := by
    intro x
    rw [← hcoe]
    exact ⟨x.1, x.2, rfl⟩
  refine ⟨P, F.codRestrict (Q : Subgroup (X ⧸ N)) hF, ?_⟩
  intro y
  have hy : y.1 ∈ Subgroup.map (QuotientGroup.mk' N) (P : Subgroup X) := by
    rw [hcoe]
    exact y.2
  obtain ⟨x, hx, hfx⟩ := (Subgroup.mem_map).mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩

/-! ## DS1 -/

/-- **DS1** (`Work.GW2.DihOrCycHeredProp`): the shape "Sylow 2-subgroups are cyclic or dihedral" is inherited by subgroups and by quotients.  `hsub`/`hquo` are the corresponding raw facts about `DihedralGroup n`. -/
theorem dihOrCycHered (hsub : Work.GW2.DihedralSubgroupProp)
    (hquo : Work.GW2.DihedralQuotientProp) : Work.GW2.DihOrCycHeredProp := by
  intro X _ _ hX
  constructor
  · -- subgroups: `Q ≃* S ≤ P`, and `S` sits in the Sylow 2-subgroup `P` of `X`
    intro K Q
    obtain ⟨P, S, e, hle⟩ := sylowSubReduction K Q
    have hP : DihOrCycType ↥P := hX P
    have h1 : DihOrCycType ↥(S.subgroupOf P) := dihOrCycType_subgroup hsub hP (S.subgroupOf P)
    have h2 : DihOrCycType ↥S :=
      (dihOrCycType_mulEquiv_iff (Subgroup.subgroupOfEquivOfLe hle)).mp h1
    exact (dihOrCycType_mulEquiv_iff e).mpr h2
  · -- quotients: `Q` is a quotient of the Sylow 2-subgroup `P` of `X`
    intro N _ Q
    obtain ⟨P, φ, hφ⟩ := sylowQuotReduction N Q
    rcases hX P with hc | ⟨n, ⟨e⟩⟩
    · haveI : IsCyclic ↥P := hc
      exact Or.inl (isCyclic_of_surjective φ hφ)
    · let ψ : DihedralGroup n →* ↥Q := φ.comp e.symm.toMonoidHom
      have hψ : Function.Surjective ψ := hφ.comp e.symm.surjective
      have hker := hquo n ψ.ker
      exact (dihOrCycType_mulEquiv_iff
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).mp hker

end Work.DSTR
