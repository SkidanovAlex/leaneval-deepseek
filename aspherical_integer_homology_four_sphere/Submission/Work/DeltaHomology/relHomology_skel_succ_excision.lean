import Mathlib
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.isClosed_skelSet
import Submission.Work.DeltaHomology.barycenter_not_mem_skelSet_of_lt
import Submission.Work.DeltaHomology.closure_skelSet_interior_punctSkel
import Submission.Work.Homology.Corollaries
import Submission.Work.Homology.Spheres
import Submission.Work.Cohomology.localHomology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Homology

namespace Work.DeltaHomology

noncomputable section

/-! ## Homeomorphism invariance of relative singular homology

A homeomorphism of spaces which carries one subspace onto another induces an isomorphism of
the relative homology of the two pairs.  This is the bookkeeping needed to transport the
correctly topologised subspace in which the excision theorem is stated to the avatar in which
the result is wanted. -/

/-- **A homeomorphism of pairs induces an isomorphism of relative homology.**  If `e : X ≃ₜ Y`
carries the subspace `A ⊆ X` onto the subspace `B ⊆ Y`, then `H_n(X, A) ≅ H_n(Y, B)`.

Route: `e` and its restriction to the subspaces are homotopy equivalences, and a morphism of
pairs which is a quasi-isomorphism on both spaces induces a quasi-isomorphism on the relative
chain complexes (`Work.Cohomology.relChainsMapOf_homologyMap_isIso`, a five-lemma at the level
of the short exact sequences of the pairs). -/
theorem relHomology_iso_of_homeomorph_pair {X Y : TopCat} {A : Set X} {B : Set Y}
    (e : X ≃ₜ Y) (he : ∀ x : X, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    Nonempty (relHomology ZMod n X A ≅ relHomology ZMod n Y B) := by
  let hsub : (TopCat.of A) ≃ₜ (TopCat.of B) :=
    { toFun := fun a => ⟨e a, (he a).mp a.2⟩
      invFun := fun b => ⟨e.symm b, (he (e.symm b)).mpr (by rw [e.apply_symm_apply]; exact b.2)⟩
      left_inv := fun a => Subtype.ext (e.left_inv a)
      right_inv := fun b => Subtype.ext (e.right_inv b)
      continuous_toFun := Continuous.subtype_mk (e.continuous.comp continuous_subtype_val)
        (fun a => (he a).mp a.2)
      continuous_invFun := Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val)
        (fun b => (he (e.symm b)).mpr (by rw [e.apply_symm_apply]; exact b.2)) }
  let f : X ⟶ Y := TopCat.ofHom e.toHomotopyEquiv.toFun
  let g : TopCat.of A ⟶ TopCat.of B := TopCat.ofHom hsub.toHomotopyEquiv.toFun
  have hf : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) k) :=
    fun k => Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv e.toHomotopyEquiv k
  have hg : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g) k) :=
    fun k => Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv hsub.toHomotopyEquiv k
  have hw : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B := by
    apply TopCat.hom_ext
    ext z
    simp [Work.Cohomology.subtypeIncl, Homeomorph.coe_toHomotopyEquiv, f, g]
    rfl
  have hI : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf X Y A B f g hw) n) :=
    Work.Cohomology.relChainsMapOf_homologyMap_isIso (X := X) (Y := Y) (A := A) (B := B)
      (f := f) (g := g) (w := hw) (n := n) hf hg
  exact ⟨@asIso _ _ _ _ (HomologicalComplex.homologyMap
    (Work.Cohomology.relChainsMapOf X Y A B f g hw) n) hI⟩

/-- **Excision of the `k`-skeleton.**  The `k`-skeleton is closed in `X` and contained in the
interior of `punctSkel (k+1)` (which is open, being the complement of the finite set of
barycentres of the `(k+1)`-simplices, and contains the `k`-skeleton by
`barycenter_not_mem_skelSet_of_lt`).  Hence the pair `(X^{k+1}, punctSkel (k+1))` may be
excised along the `k`-skeleton: its relative homology agrees with that of the pair of
complements of `X^k` inside `X^{k+1} ∖ X^k`.

Route: use `Work.Homology.relHomology_excision` (the closure form, from
`Submission/Work/Homology/Spheres.lean`) in the ambient space `TopCat.of (χ.skelSet (k+1))`
with `A = {x : ↥(skelSet (k+1)) | (x : X) ∈ punctSkel (k+1)}` and
`Z = {x : ↥(skelSet (k+1)) | (x : X) ∈ skelSet k}`, then identify the resulting subspace
`{x : ↥(skelSet (k+1)) | (x : X) ∉ skelSet k}` with the subspace
`{x : X | x ∈ skelSet (k+1) ∧ x ∉ skelSet k}` of `X` (the two sets are equal, so use
`TopCat.of` congruence and `Homeomorph.setCongr`).  The hypotheses are: `skelSet k` is closed
(`isClosed_skelSet`) and `punctSkel (k+1) ⊆ skelSet (k+1)` is open in `skelSet (k+1)`
because its complement is a finite union of singletons `{cellBarycenter}`, which is closed. -/
theorem relHomology_skel_succ_excision {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (k m : ℕ) :
    Nonempty (relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
        {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
          (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)} ≅
      relHomology ZMod m
        (TopCat.of {x : X | x ∈ R.toDeltaSimplexMap.skelSet (k + 1) ∧
          x ∉ R.toDeltaSimplexMap.skelSet k})
        {x : ↥{x : X | x ∈ R.toDeltaSimplexMap.skelSet (k + 1) ∧
          x ∉ R.toDeltaSimplexMap.skelSet k} |
          (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}) := by
  have hclo : closure {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
        (x : X) ∈ R.toDeltaSimplexMap.skelSet k} ⊆
      interior {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
        (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)} :=
    closure_skelSet_interior_punctSkel R k
  obtain ⟨e1⟩ := Work.Homology.relHomology_excision
    (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
    {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
      (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}
    {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
      (x : X) ∈ R.toDeltaSimplexMap.skelSet k} hclo m
  let eT : (TopCat.of {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
        x ∉ {y : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
          (y : X) ∈ R.toDeltaSimplexMap.skelSet k}}) ≃ₜ
      (TopCat.of {x : X | x ∈ R.toDeltaSimplexMap.skelSet (k + 1) ∧
        x ∉ R.toDeltaSimplexMap.skelSet k}) :=
    { toFun := fun x => ⟨(x : ↥(R.toDeltaSimplexMap.skelSet (k + 1))), x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      continuous_toFun := Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val) (fun x => ⟨x.1.2, x.2⟩)
      continuous_invFun := Continuous.subtype_mk
        (Continuous.subtype_mk continuous_subtype_val (fun y => y.2.1)) (fun y => y.2.2) }
  refine ⟨e1 ≪≫ (relHomology_iso_of_homeomorph_pair eT ?_ m).some⟩
  intro x
  exact Iff.rfl

end

end Work.DeltaHomology
