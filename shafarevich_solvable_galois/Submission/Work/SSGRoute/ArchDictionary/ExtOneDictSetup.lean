import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.ExtOnePre
import Submission.Work.SSGRoute.ExtOneSES
import Submission.Work.SSGRoute.ext_one_iso_divisible_cohomology
import Submission.Work.SSGRoute.homRepShortComplex_shortExact
import Submission.Work.SSGRoute.ext_one_homRepFree_subsingleton
import Submission.Work.SSGRoute.homRepFree_coind_iso
import Submission.Work.SSGRoute.freeLift_id_epi
import Submission.Work.SSGRoute.moduleInjective_coeff_of_divisible
import Submission.Work.SSGRoute.ArchDictionary.ExtCokerDefs
import Submission.Work.SSGRoute.ArchDictionary.freeCoverLiftExists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The dictionary `Ext¹_G(M,N) ≅ Ext¹_G(ℤ, Hom_ℤ(M,N))`, built explicitly

Here we build, for a `G`-module `N` whose underlying abelian group is divisible (equivalently, an
injective `ℤ`-module), an explicit additive equivalence

`dictEquiv N M : Ext¹_G(M,N) ≃+ Ext¹_G(ℤ, Hom_ℤ(M,N))`

which is *natural* in `M`; the naturality is proved in
`ArchDictionary/extOneDictNatural.lean`.

The construction follows `Work.SSGRoute.ext_one_iso_divisible_cohomology`, but replaces every
`Classical.choose` of a `Nonempty` by an explicit term, which is what makes naturality provable:

```
Ext¹(M,N) ≅ Ext¹(S.X₃,N) --extCokerEquiv-->  Ext⁰(S.X₁,N)/im Ext⁰(S.X₂,N)
     --coverCongr-->  Ext⁰(ℤ, Hom(S.X₁,N))/im Ext⁰(ℤ, Hom(S.X₂,N))
     --(extCokerEquivCov)⁻¹-->  Ext¹(ℤ, Hom(S.X₃,N)) = Ext¹(ℤ, Hom(M,N)),
```

where `S = coverS M` is the *canonical* free presentation
`0 → R → ℤ[G]^{M.V} --coverProj--> M → 0`.

The key points that make this work are

* the free cover is canonical, so a morphism `u : M' ⟶ M` induces a canonical morphism of
  presentations `coverMap u : coverS M' ⟶ coverS M` with `(coverMap u).τ₃ = u` definitionally
  (the middle component is chosen once and for all by `freeCoverLiftExists`);
* every auxiliary equivalence (`unitHomEquiv`, `unitHomExtEquiv`) is the explicit one from
  `ext_one_iso_divisible_cohomology`, and its naturality (`unitHomExtEquiv_symm_precomp`) is
  available.

All definitions here (`coverProj`, `coverS`, `coverMid`, `coverMap`, `homCoverS`, `homCoverMap`)
are `abbrev`s, i.e. *reducible*, so that their components unfold at every transparency level.
This matters for rewriting: the equations `(coverS M).X₃ = M` and `(homCoverS M N).X₃ =
homRep (coverS M).X₁ N` then hold syntactically as well as definitionally.  (`homRepShortComplex`
itself is only *semireducibly* reducible, hence the local copy `homCoverS`.)
-/

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute.ArchDictionary

variable {G : Type} [Group G]

noncomputable section

/-! ## The canonical free cover -/

/-- The canonical surjection `ℤ[G]^{M.V} ↠ M`, whose value on the basis vector `m` is `m`. -/
noncomputable abbrev coverProj (M : Rep.{0} Coeff G) : Rep.free Coeff G M.V ⟶ M :=
  Rep.freeLift Coeff G M (fun m : M.V => m)

instance coverProj_epi (M : Rep.{0} Coeff G) : Epi (coverProj M) := freeLift_id_epi G M

/-- The canonical free presentation `0 → R → ℤ[G]^{M.V} → M → 0` of `M`. -/
noncomputable abbrev coverS (M : Rep.{0} Coeff G) : ShortComplex (Rep.{0} Coeff G) :=
  ShortComplex.mk (Limits.kernel.ι (coverProj M)) (coverProj M)
    (Limits.kernel.condition (coverProj M))

theorem coverS_shortExact (M : Rep.{0} Coeff G) : (coverS M).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel (coverProj M))
    (inferInstanceAs (Mono (Limits.kernel.ι (coverProj M))))
    (inferInstanceAs (Epi (coverProj M)))

instance coverS_projective (M : Rep.{0} Coeff G) : Projective (coverS M).X₂ :=
  Rep.free_projective

/-- The comparison map between the free covers, chosen once and for all from
`freeCoverLiftExists`. -/
noncomputable abbrev coverMid (M' M : Rep.{0} Coeff G) (u : M' ⟶ M) :
    Rep.free Coeff G M'.V ⟶ Rep.free Coeff G M.V :=
  Classical.choose (freeCoverLiftExists G M' M u)

lemma coverMid_spec (M' M : Rep.{0} Coeff G) (u : M' ⟶ M)
    (x : Rep.free Coeff G M'.V) :
    (coverProj M).hom ((coverMid M' M u).hom x) = u.hom ((coverProj M').hom x) :=
  Classical.choose_spec (freeCoverLiftExists G M' M u) x

lemma coverMid_comp (M' M : Rep.{0} Coeff G) (u : M' ⟶ M) :
    coverMid M' M u ≫ coverProj M = coverProj M' ≫ u := by
  apply Rep.free_ext
  intro i
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact coverMid_spec M' M u (Finsupp.single i (MonoidAlgebra.single 1 1))

/-- **The canonical morphism of free presentations induced by `u : M' ⟶ M`.**  Its third
component is `u` definitionally, which is what the naturality proof of the dictionary uses. -/
noncomputable abbrev coverMap (M' M : Rep.{0} Coeff G) (u : M' ⟶ M) :
    coverS M' ⟶ coverS M :=
  ShortComplex.homMk
    (Limits.kernel.lift (coverProj M) (Limits.kernel.ι (coverProj M') ≫ coverMid M' M u) (by
      rw [Category.assoc, coverMid_comp, ← Category.assoc, Limits.kernel.condition,
        Limits.zero_comp]))
    (coverMid M' M u) u
    (Limits.kernel.lift_ι (coverProj M) (Limits.kernel.ι (coverProj M') ≫ coverMid M' M u) _)
    (coverMid_comp M' M u)

/-! ## The dual short complex, as a local (reducible) copy of `homRepShortComplex` -/

/-- The dual short complex `0 → Hom(X₃,N) → Hom(X₂,N) → Hom(X₁,N) → 0` of the canonical
presentation, written with a reducible body so that its components unfold during rewriting. -/
noncomputable abbrev homCoverS (M : Rep.{0} Coeff G) (N : Rep.{0} Coeff G) :
    ShortComplex (Rep.{0} Coeff G) :=
  ShortComplex.mk (homRepPre (coverS M).X₃ (coverS M).X₂ N (coverS M).g)
    (homRepPre (coverS M).X₂ (coverS M).X₁ N (coverS M).f)
    (by
      rw [homRepPre_comp (coverS M).X₃ (coverS M).X₂ (coverS M).X₁ N (coverS M).g (coverS M).f,
        (coverS M).zero]
      exact homRepPre_zero (coverS M).X₃ (coverS M).X₁ N)

/-- The two commutation relations of the canonical morphism of free presentations, stated with
`u` itself (the third component of `coverMap M' M u` is definitionally `u`). -/
lemma coverMap_comm₁₂ (M' M : Rep.{0} Coeff G) (u : M' ⟶ M) :
    (coverMap M' M u).τ₁ ≫ (coverS M).f = (coverS M').f ≫ coverMid M' M u :=
  (coverMap M' M u).comm₁₂

lemma coverMap_comm₂₃ (M' M : Rep.{0} Coeff G) (u : M' ⟶ M) :
    coverMid M' M u ≫ (coverS M).g = (coverS M').g ≫ u :=
  (coverMap M' M u).comm₂₃

/-- **The morphism of short complexes `Hom(-,N)` applied to `u : M' ⟶ M`** (contravariantly):
`homCoverS M N ⟶ homCoverS M' N`. -/
noncomputable abbrev homCoverMap (M' M : Rep.{0} Coeff G) (u : M' ⟶ M) (N : Rep.{0} Coeff G) :
    homCoverS M N ⟶ homCoverS M' N :=
  ShortComplex.homMk
    (homRepPre (coverS M).X₃ (coverS M').X₃ N u)
    (homRepPre (coverS M).X₂ (coverS M').X₂ N (coverMid M' M u))
    (homRepPre (coverS M).X₁ (coverS M').X₁ N (coverMap M' M u).τ₁)
    (by
      rw [homRepPre_comp, homRepPre_comp, coverMap_comm₂₃])
    (by
      rw [homRepPre_comp, homRepPre_comp, coverMap_comm₁₂])

/-! ## The dictionary -/

/-- The hom-complex of the canonical presentation is short exact for injective coefficients. -/
theorem homCoverShortExact (M : Rep.{0} Coeff G) (N : Rep.{0} Coeff G)
    (hInj : Module.Injective Coeff N.V) : (homCoverS M N).ShortExact :=
  homRepShortComplex_shortExact G (coverS M) (coverS_shortExact M) N hInj

/-- Vanishing of `Ext¹_G(ℤ, Hom_ℤ(ℤ[G]^{M.V}, N))` (Shapiro). -/
theorem homCoverSubsingleton (M : Rep.{0} Coeff G) (N : Rep.{0} Coeff G) :
    Subsingleton (Abelian.Ext (unitRep G) (homCoverS M N).X₂ 1) :=
  let h := homRepFree_coind_iso G M.V N
  ext_one_homRepFree_subsingleton G M.V N h.choose h.choose_spec

/-- The degree-zero transport `Ext⁰(ℤ, Hom(S.X₁,N)) ≅ Ext⁰(S.X₁,N)`, matching up the two cokernel
descriptions. -/
theorem coverCongrAux (M : Rep.{0} Coeff G) (N : Rep.{0} Coeff G) :
    AddSubgroup.map (unitHomExtEquiv (coverS M).X₁ N).symm.toAddMonoidHom
        ((extRestrict (coverS M) N)).range
      = (extGMap (homCoverS M N) (unitRep G)).range := by
  show AddSubgroup.map (unitHomExtEquiv (coverS M).X₁ N).symm.toAddMonoidHom
        (((Abelian.Ext.mk₀ (coverS M).f).precomp N (zero_add 0))).range
      = ((Abelian.Ext.mk₀ (homRepPre (coverS M).X₂ (coverS M).X₁ N (coverS M).f)).postcomp
          (unitRep G) (zero_add 0)).range
  apply le_antisymm
  · intro b hb
    rw [AddSubgroup.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    rw [AddMonoidHom.mem_range] at ha ⊢
    obtain ⟨z, rfl⟩ := ha
    refine ⟨(unitHomExtEquiv (coverS M).X₂ N).symm z, ?_⟩
    exact (unitHomExtEquiv_symm_precomp (coverS M).X₂ (coverS M).X₁ N (coverS M).f z).symm
  · intro b hb
    rw [AddMonoidHom.mem_range] at hb
    obtain ⟨y, rfl⟩ := hb
    rw [AddSubgroup.mem_map]
    refine ⟨((Abelian.Ext.mk₀ (coverS M).f).precomp N (zero_add 0))
        ((unitHomExtEquiv (coverS M).X₂ N) y), ⟨(unitHomExtEquiv (coverS M).X₂ N) y, rfl⟩, ?_⟩
    have h := unitHomExtEquiv_symm_precomp (coverS M).X₂ (coverS M).X₁ N (coverS M).f
      ((unitHomExtEquiv (coverS M).X₂ N) y)
    rw [AddEquiv.symm_apply_apply] at h
    exact h

/-- The isomorphism of the two cokernel descriptions. -/
noncomputable abbrev coverCongr (M : Rep.{0} Coeff G) (N : Rep.{0} Coeff G) :
    (Abelian.Ext (coverS M).X₁ N 0 ⧸ (extRestrict (coverS M) N).range) ≃+
      (Abelian.Ext (unitRep G) (homRep (coverS M).X₁ N) 0 ⧸
        (extGMap (homCoverS M N) (unitRep G)).range) :=
  QuotientAddGroup.congr (extRestrict (coverS M) N).range
    (extGMap (homCoverS M N) (unitRep G)).range
    (unitHomExtEquiv (coverS M).X₁ N).symm (coverCongrAux M N)

lemma coverCongr_mk (M : Rep.{0} Coeff G) (N : Rep.{0} Coeff G)
    (a : Abelian.Ext (coverS M).X₁ N 0) :
    coverCongr M N (QuotientAddGroup.mk a)
      = QuotientAddGroup.mk ((unitHomExtEquiv (coverS M).X₁ N).symm a) := rfl

/-- **The dictionary** `Ext¹_G(M,N) ≃+ Ext¹_G(ℤ, Hom_ℤ(M,N))`, for divisible `N`. -/
noncomputable abbrev dictEquiv (N : Rep.{0} Coeff G) (hInj : Module.Injective Coeff N.V)
    (M : Rep.{0} Coeff G) :
    Abelian.Ext M N 1 ≃+ Abelian.Ext (unitRep G) (homRep M N) 1 :=
  (extCokerEquiv (coverS M) (coverS_shortExact M) N).trans
    ((coverCongr M N).trans
      ((extCokerEquivCov (homCoverS M N) (homCoverShortExact M N hInj)
        (unitRep G) (homCoverSubsingleton M N)).symm))

/-- **Computation rule for the dictionary**: on classes coming from the connecting map of the
canonical presentation, `dictEquiv` is the canonical degree-zero transport. -/
lemma dictEquiv_extClass (N : Rep.{0} Coeff G) (hInj : Module.Injective Coeff N.V)
    (M : Rep.{0} Coeff G) (a : Abelian.Ext (coverS M).X₁ N 0) :
    dictEquiv N hInj M ((coverS_shortExact M).extClass.comp a (add_zero 1)) =
      ((unitHomExtEquiv (coverS M).X₁ N).symm a).comp
        (homCoverShortExact M N hInj).extClass (zero_add 1) := by
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply]
  rw [extCokerEquiv_extClass (coverS M) (coverS_shortExact M) N a, coverCongr_mk]
  rw [← extCokerEquivCov_extClass (homCoverS M N) (homCoverShortExact M N hInj) (unitRep G)
      (homCoverSubsingleton M N) ((unitHomExtEquiv (coverS M).X₁ N).symm a),
    AddEquiv.symm_apply_apply]

end

end Work.SSGRoute.ArchDictionary
