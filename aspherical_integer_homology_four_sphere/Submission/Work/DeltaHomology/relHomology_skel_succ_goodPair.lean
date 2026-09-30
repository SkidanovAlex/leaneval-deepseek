import Mathlib
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.isIso_relHomologyMap_of_deformationRetract
import Submission.Work.DeltaHomology.exists_deformationRetract_punctSkel
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Homology

open scoped unitInterval

universe u

/-- **Transport of a deformation retract along a homeomorphism.**  If `e : Y ≃ₜ Y'` is a
homeomorphism and `hA : ∀ y : Y', y ∈ A' ↔ e.symm y ∈ A` says that `A' ⊆ Y'` is the
preimage of `A ⊆ Y` (equivalently `A' = e '' A`), then a deformation retraction of `Y` onto
`A` transports to one of `Y'` onto `A'`: the retraction is `Y' → Y → A → A'` and the homotopy
is conjugated by `e`.

The statement is a `def` rather than a `theorem` because `Work.Homology.DeformationRetract`
carries data (the retraction) and hence is not a proposition. -/
noncomputable def transportDeformationRetract {Y Y' : TopCat.{u}} {A : Set Y} {A' : Set Y'}
    (e : Y ≃ₜ Y') (hA : ∀ y : Y', y ∈ A' ↔ e.symm y ∈ A) (h : DeformationRetract Y A) :
    DeformationRetract Y' A' := by
  have hmem : ∀ a : A, e a ∈ A' := fun a => (hA (e a)).mpr (by simp)
  let eh : Y ⟶ Y' := TopCat.ofHom ⟨⇑e, e.continuous⟩
  let ei : Y' ⟶ Y := TopCat.ofHom ⟨⇑e.symm, e.symm.continuous⟩
  let φ : TopCat.of A ⟶ TopCat.of A' :=
    TopCat.ofHom ⟨fun a => ⟨e a, hmem a⟩, (e.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let ψ : TopCat.of A' ⟶ TopCat.of A :=
    TopCat.ofHom ⟨fun y => ⟨e.symm y, (hA y).mp y.2⟩,
      (e.symm.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hei : ∀ y : Y', ei y = e.symm y := fun y => rfl
  have heh : ∀ y : Y, eh y = e y := fun y => rfl
  have hφe : ∀ a : A, φ a = ⟨e a, hmem a⟩ := fun a => rfl
  have hψe : ∀ y : A', ψ y = ⟨e.symm y, (hA y).mp y.2⟩ := fun y => rfl
  have hφ : ∀ a : A, (φ a : Y') = e a := fun a => congrArg Subtype.val (hφe a)
  have hψ : ∀ y : A', (ψ y : Y) = e.symm y := fun y => congrArg Subtype.val (hψe y)
  have hfix : ∀ (z : Y) (hz : z ∈ A), h.retract z = ⟨z, hz⟩ := by
    intro z hz
    have h0 := congrArg (fun (f : TopCat.of A ⟶ TopCat.of A) => f ⟨z, hz⟩) h.retract_incl
    rw [CategoryTheory.comp_apply, CategoryTheory.id_apply, Work.Homology.incl_apply] at h0
    exact h0
  have hψφ : ψ ≫ φ = 𝟙 (TopCat.of A') := by
    apply TopCat.ext; intro y
    rw [CategoryTheory.comp_apply, CategoryTheory.id_apply, hψe]
    apply Subtype.ext
    rw [hφ]
    exact e.apply_symm_apply (y : Y')
  have hφincl : φ ≫ incl A' = incl A ≫ eh := by
    apply TopCat.ext; intro a
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, Work.Homology.incl_apply,
      Work.Homology.incl_apply, hφ, heh]
  have hincl : incl A' ≫ ei = ψ ≫ incl A := by
    apply TopCat.ext; intro y
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, Work.Homology.incl_apply,
      Work.Homology.incl_apply, hei]
    exact (hψ y).symm
  refine ⟨ei ≫ h.retract ≫ φ, ?_, ?_⟩
  · apply TopCat.ext; intro y
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply,
      CategoryTheory.id_apply]
    apply Subtype.ext
    rw [Work.Homology.incl_apply, hei, hfix (e.symm y) ((hA y).mp y.2), hφ]
    exact e.apply_symm_apply (y : Y')
  · obtain ⟨H⟩ := h.homotopy
    have hcomp : (ei ≫ h.retract ≫ φ) ≫ incl A' = ei ≫ (h.retract ≫ incl A) ≫ eh := by
      simp only [Category.assoc]
      rw [hφincl]
    rw [hcomp]
    refine ⟨ContinuousMap.Homotopy.mk
      ⟨fun p : I × Y' => e (H (p.1, e.symm p.2)), ?_⟩ ?_ ?_⟩
    · exact e.continuous.comp
        (H.continuous.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
    · intro y
      have hgoal : (ei ≫ (h.retract ≫ incl A) ≫ eh) y
          = e (incl A (h.retract (e.symm (y : Y')))) := by
        rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, hei, heh,
          Work.Homology.incl_apply]
        rfl
      have hH : H (0, e.symm (y : Y')) = incl A (h.retract (e.symm (y : Y'))) := by
        have h0 := H.map_zero_left (e.symm (y : Y'))
        rw [CategoryTheory.comp_apply] at h0
        exact h0
      show e (H (0, e.symm (y : Y'))) = (ei ≫ (h.retract ≫ incl A) ≫ eh) y
      rw [hgoal, hH]
    · intro y
      have hH : H (1, e.symm y) = e.symm y := H.map_one_left (e.symm y)
      show e (H (1, e.symm y)) = (𝟙 Y') y
      rw [hH, CategoryTheory.id_apply, e.apply_symm_apply]

/-- The image form of `transportDeformationRetract`: a deformation retraction of `Y` onto `A`
transports along a homeomorphism `e : Y ≃ₜ Y'` to a deformation retraction of `Y'` onto the
image `e '' A`. -/
noncomputable def DeformationRetract.of_homeomorph {Y Y' : TopCat.{u}} (e : Y ≃ₜ Y') {A : Set Y}
    (h : DeformationRetract Y A) : DeformationRetract Y' (e '' A) :=
  transportDeformationRetract e (fun y => by
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩) h

namespace Work.DeltaHomology

/-- **The punctured `(k+1)`-skeleton is a good neighbourhood of the `k`-skeleton.**
`χ.punctSkel (k+1)` is the `(k+1)`-skeleton with the barycentres of its `(k+1)`-simplices
removed; by the collar theorem
(`Submission.Work.DeltaHomology.exists_deformationRetract_punctSkel`) the `k`-skeleton is a
deformation retract of it.  Hence the identity of `X^{k+1}` induces an isomorphism between the
relative homologies of the pairs `(X^{k+1}, X^k)` and `(X^{k+1}, punctSkel (k+1))`.

Route: apply `isIso_relHomologyMap_of_deformationRetract`
(`Submission.Work.DeltaHomology.isIso_relHomologyMap_of_deformationRetract`) with ambient space
`TopCat.of (χ.skelSet (k+1))`, `A = {x : ↥(skelSet (k+1)) | (x : X) ∈ skelSet k}` and
`U = {x : ↥(skelSet (k+1)) | (x : X) ∈ punctSkel (k+1)}`, and take its `Nonempty` iso.  The
hypothesis `h` is stated in the ambient space `TopCat.of (punctSkel (k+1))`; transport it to
the ambient space `TopCat.of U` along the canonical homeomorphism of the two spaces
(the maps `retrSubHom`/`retrSubInv` of
`Submission/Work/DeltaHomology/isIso_relHomologyMap_of_deformationRetract.lean`): a
deformation retract transports along a homeomorphism of the ambient spaces, so it is worth
proving the general lemma "if `e : Y ≃ₜ Y'` and `DeformationRetract Y A` then
`DeformationRetract Y' (e '' A)`" first.  You may also discharge `h` entirely by applying
`exists_deformationRetract_punctSkel` (already proved) and then transporting, but the
statement below keeps `h` as a hypothesis. -/
theorem relHomology_skel_succ_goodPair {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (k m : ℕ)
    (h : DeformationRetract (TopCat.of (R.toDeltaSimplexMap.punctSkel (k + 1)))
      {x : ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) |
        (x : X) ∈ R.toDeltaSimplexMap.skelSet k}) :
    Nonempty (relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
        {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
          (x : X) ∈ R.toDeltaSimplexMap.skelSet k} ≅
      relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
        {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
          (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}) := by
  set W : Set X := R.toDeltaSimplexMap.skelSet (k + 1) with hW
  set A : Set ↥W := {x | (x : X) ∈ R.toDeltaSimplexMap.skelSet k} with hA
  set U : Set ↥W := {x | (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)} with hU
  have hAU : A ⊆ U := fun x hx => DeltaSimplexMap.skelSet_subset_punctSkel_succ R k hx
  have hPU : ∀ y : ↥(R.toDeltaSimplexMap.punctSkel (k + 1)), (y : X) ∈ W :=
    fun y => R.toDeltaSimplexMap.punctSkel_subset_skelSet (k + 1) y.2
  let e : TopCat.of (R.toDeltaSimplexMap.punctSkel (k + 1)) ≃ₜ TopCat.of U :=
    { toFun := fun y => ⟨⟨(y : X), hPU y⟩, y.2⟩
      invFun := fun u => ⟨(u : X), u.2⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun u => Subtype.ext (Subtype.ext rfl)
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  have hU' : DeformationRetract (TopCat.of U) {x : ↥U | (x : ↥W) ∈ A} :=
    transportDeformationRetract e
      (A := {x : ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) |
        (x : X) ∈ R.toDeltaSimplexMap.skelSet k})
      (A' := {x : ↥U | (x : ↥W) ∈ A}) (fun y => Iff.rfl) h
  have hIso : IsIso (relHomologyMap ZMod m (pairHomOfSubset hAU)) :=
    isIso_relHomologyMap_of_deformationRetract (X := TopCat.of W) (A := A) (U := U) hAU hU' m
  exact ⟨@asIso (ModuleCat ℤ) _ _ _ (relHomologyMap ZMod m (pairHomOfSubset hAU)) hIso⟩

end Work.DeltaHomology

/-! ## The same lemma under its flat name

The lemma above is registered in the namespace `Work.DeltaHomology.Work.DeltaHomology` (the
file carries two identical `namespace Work.DeltaHomology` lines, as it was delivered).  The
statement below is the *same* lemma, restated in the namespace `Work.DeltaHomology`, which is
the name under which the rest of the project refers to it
(`Work.DeltaHomology.relHomology_skel_succ_goodPair`). -/
theorem relHomology_skel_succ_goodPair {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (k m : ℕ)
    (h : DeformationRetract (TopCat.of (R.toDeltaSimplexMap.punctSkel (k + 1)))
      {x : ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) |
        (x : X) ∈ R.toDeltaSimplexMap.skelSet k}) :
    Nonempty (relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
        {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
          (x : X) ∈ R.toDeltaSimplexMap.skelSet k} ≅
      relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
        {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
          (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}) := by
  exact _root_.Work.DeltaHomology.Work.DeltaHomology.relHomology_skel_succ_goodPair R k m h

end Work.DeltaHomology
