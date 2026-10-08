/-
# CORE4 — the relative Fitting subgroup `F(A)` is transported by automorphisms of `G`

For every subgroup `A ≤ G` and every automorphism `φ` of `G` one has

  `F(A^φ) = F(A)^φ`,

where `F(K) = fittingIn K` is the Fitting subgroup of `K`, viewed inside the ambient
group `G` (`Work.GW2.fittingIn K = (Work.GW2.fitting K).map K.subtype`).

This is the "characteristic subgroup" step used whenever a maximal-subgroup argument of
Bender 1970/1981 is applied to a conjugate (or, more generally, an isomorphic image) of
the subgroup under consideration: `F(K)` is a characteristic subgroup of `K`, hence
compatible with every automorphism of the ambient group that carries `K` onto `K'`.

The mathematical content is the invariance of the two ingredients of
`Work.GW2.fitting G = (sSup {N ≤ G | N.Normal ∧ IsNilpotent N}).normalCore`:

* a join of normal nilpotent subgroups is transported to a join of normal nilpotent
  subgroups (nilpotency of a subgroup is preserved by isomorphism, and normality is
  preserved by a *surjective* map — this is why no finiteness hypothesis is needed);
* the normal core is the largest *normal* subgroup contained in a given subgroup, and
  the "largest" description (`Subgroup.normal_le_normalCore`) is manifestly
  isomorphism-invariant.

Everything below is stated for an arbitrary group isomorphism `A ≃* B` (the case needed
in the application is the one induced by `Subgroup.equivMapOfInjective`), and then
specialised to `φ : G ≃* G`.
-/
import Mathlib
import Submission.Work.CORE4.Defs

set_option linter.style.haveILetI false

namespace Work.CORE4

/-! ## 0. `F(G)` is preserved by an isomorphism of groups -/

/-- The Fitting subgroup is transported *into* itself by a group isomorphism:
`F(A).map e ≤ F(B)`.  Both ingredients of `F` are covered: `e` maps normal nilpotent
subgroups of `A` onto normal nilpotent subgroups of `B` (here the surjectivity of `e` is
used for normality), and the normal core is handled by its universal property. -/
theorem fitting_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Work.GW2.fitting A).map e.toMonoidHom ≤ Work.GW2.fitting B := by
  haveI : (Subgroup.map e.toMonoidHom
      ((sSup {N : Subgroup A | N.Normal ∧ Group.IsNilpotent N}).normalCore)).Normal :=
    (Subgroup.normalCore_normal _).map e.toMonoidHom e.surjective
  have hmain : Subgroup.map e.toMonoidHom
        ((sSup {N : Subgroup A | N.Normal ∧ Group.IsNilpotent N}).normalCore)
      ≤ sSup {N : Subgroup B | N.Normal ∧ Group.IsNilpotent N} := by
    refine le_trans (Subgroup.map_mono (f := e.toMonoidHom) (Subgroup.normalCore_le _)) ?_
    rw [Subgroup.map_le_iff_le_comap, sSup_le_iff]
    intro N hN
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨hN.1.map e.toMonoidHom e.surjective, ?_⟩
    haveI : Group.IsNilpotent ↥N := hN.2
    exact Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective N e.toMonoidHom e.injective)
  show (Subgroup.map e.toMonoidHom
      ((sSup {N : Subgroup A | N.Normal ∧ Group.IsNilpotent N}).normalCore)) ≤ Work.GW2.fitting B
  rw [Work.GW2.fitting]
  exact Subgroup.normal_le_normalCore.mpr hmain

/-- `F(A).map e = F(B)` for an isomorphism `e : A ≃* B`; the reverse inclusion follows by
applying the previous lemma to `e.symm`. -/
theorem fitting_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Work.GW2.fitting A).map e.toMonoidHom = Work.GW2.fitting B := by
  refine le_antisymm (fitting_map_le e) ?_
  have h := Subgroup.map_mono (f := e.toMonoidHom) (fitting_map_le e.symm)
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by ext x; simp
  rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h

/-! ## 1. The relative Fitting subgroup `F(A) = fittingIn A` -/

/-- `F(A) = F(A^φ)^φ⁻¹`, i.e. `F(A.map φ) = F(A).map φ` for an automorphism `φ` of the
ambient group.  It suffices to know the abstract statement for the induced isomorphism
`A ≃* A.map φ` and to identify the two inclusions `A ↪ G` and `A.map φ ↪ G`. -/
theorem FittingInConj {G : Type} [Group G] (A : Subgroup G) (φ : G ≃* G) :
    Work.GW2.fittingIn (A.map φ.toMonoidHom) = (Work.GW2.fittingIn A).map φ.toMonoidHom := by
  unfold Work.GW2.fittingIn
  rw [← fitting_map_mulEquiv (Subgroup.equivMapOfInjective A φ.toMonoidHom φ.injective)]
  rw [Subgroup.map_map]
  have hcomp : (A.map φ.toMonoidHom).subtype.comp
      (Subgroup.equivMapOfInjective A φ.toMonoidHom φ.injective).toMonoidHom
      = φ.toMonoidHom.comp A.subtype := by ext x; rfl
  rw [hcomp, ← Subgroup.map_map]

end Work.CORE4
