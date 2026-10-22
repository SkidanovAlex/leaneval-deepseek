import Mathlib
import ChallengeDeps
import Submission.Work.ANALYTIC.PrTop
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.solidEquiv_splitEpi
import Submission.Work.ANALYTIC.solidNull_zfree_tensor
import Submission.Work.ANALYTIC.profinite_HI_pt
import Submission.Work.ANALYTIC.kernel_prTop_tensor
import Submission.Work.ATOM.Defs
import Submission.Work.FLAT.Main

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

open _root_.LightCondensed _root_.LightCondensed.Solid

/-! ## Assembly of AN5

`prTop S : S × I ⟶ S` (`I = [0,1]`) is a split epimorphism with section
`Submission.Blueprint.i₀ S : S ⟶ S × I` (`Work.ANALYTIC.i₀_prTop`).  Its kernel is, by the strong
monoidality of `ℤ[-]` and the exactness of `ℤ[S] ⊗ -` (area FLAT), the tensor product
`ℤ[S] ⊗ ker (ℤ[prTop pt] : ℤ[[0,1]] ⟶ ℤ)`, and solid-nullness is preserved by tensoring with the
free object `ℤ[S]`.  Hence AN5 for `S` reduces to the point case, i.e. to the
solid-contractibility of the interval:

* `Work.ANALYTIC.solidEquiv_splitEpi` — `SolidEquiv (ℤ[f]) ↔ SolidNull (ℤ[ker f])` for a split epi;
* `Work.ANALYTIC.solidNull_zfree_tensor` — `SolidNull A → SolidNull (ℤ[S] ⊗ A)`;
* `Work.ANALYTIC.kernel_prTop_tensor` — `ker ℤ[prTop S] ≅ ℤ[S] ⊗ ker ℤ[prTop pt]`;
* `Work.ANALYTIC.profinite_HI_pt` — the point case. -/

/-! ## Status

The four reductions above are proved and imported here; the assembly of `profinite_HI` below is
complete and typechecks against them:

* `Work.ANALYTIC.solidEquiv_splitEpi` — PROVED;
* `Work.ANALYTIC.solidNull_zfree_tensor` — PROVED;
* `Work.ANALYTIC.kernel_prTop_tensor` — PROVED;
* `Work.ANALYTIC.profinite_HI_pt` — the analytic core (`L■ℤ[[0,1]] ≅ ℤ`), still in progress.

So `Work.ANALYTIC.profinite_HI` is *conditional only on* `profinite_HI_pt`, and
`Submission/Work/ANALYTIC/profinite_HI.lean` is sorry-free as soon as that file is. -/

/-- `SolidNull` is invariant under isomorphism of the underlying light condensed abelian group. -/
theorem solidNull_of_iso {A B : LightCondAb} (e : A ≅ B)
    (h : SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj A)) :
    SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj B) := by
  intro N
  haveI := h N
  refine ⟨fun f g => ?_⟩
  let i := (DerivedCategory.singleFunctor LightCondAb 0).mapIso e
  have h1 : i.hom ≫ f = i.hom ≫ g := Subsingleton.elim _ _
  calc f = i.inv ≫ (i.hom ≫ f) := (Iso.inv_hom_id_assoc i f).symm
    _ = i.inv ≫ (i.hom ≫ g) := by rw [h1]
    _ = g := Iso.inv_hom_id_assoc i g

/-- **AN5 (REFS/04 §2): homotopy invariance of `ℤ[-]` for light profinite `S`.**  The projection
`pr : S × [0,1] ⟶ S` induces a solid-equivalence `ℤ[S × [0,1]] ⟶ ℤ[S]`. -/
theorem profinite_HI (S : LightProfinite.{0}) :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        (freeLightCondAbOfTopFunctor.map (prTop (LightProfinite.toTopCat.obj S)))) := by
  -- the section relation, for `S` and for the point
  have hs : freeLightCondAbOfTopFunctor.map
        (Submission.Blueprint.i₀ (LightProfinite.toTopCat.obj S)) ≫
      freeLightCondAbOfTopFunctor.map (prTop (LightProfinite.toTopCat.obj S)) = 𝟙 _ := by
    rw [← Functor.map_comp, i₀_prTop]
    simp
  have hspt : freeLightCondAbOfTopFunctor.map
        (Submission.Blueprint.i₀
          (LightProfinite.toTopCat.obj (LightProfinite.of PUnit.{1}))) ≫
      freeLightCondAbOfTopFunctor.map
        (prTop (LightProfinite.toTopCat.obj (LightProfinite.of PUnit.{1}))) = 𝟙 _ := by
    rw [← Functor.map_comp, i₀_prTop]
    simp
  -- the point case: solid-nullness of the kernel of the augmentation of the interval
  have hpt : SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj (Limits.kernel
      (freeLightCondAbOfTopFunctor.map
        (prTop (LightProfinite.toTopCat.obj (LightProfinite.of PUnit.{1})))))) :=
    (solidEquiv_splitEpi _ _ hspt).mp profinite_HI_pt
  -- tensoring with `ℤ[S]` preserves solid-nullness
  have h2 : SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj
      (Work.ATOM.tmul ((LightCondensed.free (R := ℤ)).obj S.toCondensed)
        (Limits.kernel (freeLightCondAbOfTopFunctor.map
          (prTop (LightProfinite.toTopCat.obj (LightProfinite.of PUnit.{1}))))))) :=
    solidNull_zfree_tensor S hpt
  -- identify the kernel of `ℤ[prTop S]` with that tensor product and conclude
  obtain ⟨e⟩ := kernel_prTop_tensor S
  exact (solidEquiv_splitEpi _ _ hs).mpr (solidNull_of_iso e.symm h2)

end

end Work.ANALYTIC
