import Mathlib
import Submission.Work.ANALYTIC.PrTop
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ATOM.Defs
import Submission.Work.FLAT.Main

set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

/-!
# `ker (ℤ[prTop S]) ≅ ℤ[S] ⊗ ker (ℤ[prTop *])`

This is the categorical input of AN5 (`Submission/Work/ANALYTIC/profinite_HI.lean`): the kernel of
the map `ℤ[pr : S × [0,1] ⟶ S]` induced by the projection `prTop S` is the tensor product of
`ℤ[S]` with the kernel of the projection for the point.

The proof rests on two facts.

* `ℤ[-]` is a strong monoidal functor on topological spaces: the functor
  `F = freeLightCondAbOfTopFunctor = topCatToLightCondSet ⋙ free ℤ` is strong monoidal with respect
  to the cartesian monoidal structures.  Here `topCatToLightCondSet` — the sheaf of continuous maps
  into a topological space — preserves finite products because it is a right adjoint
  (`LightCondSet.topCatAdjunction`), and `free ℤ` is monoidal because `ℤ` is a ring.
  Writing `g := F.map (toUnit I) : F(I) ⟶ F(𝟙_)` for the unique map to the point, naturality of
  the tensorator in the second variable gives
  `F(prTop S) = F(fst S I) = μ⁻¹ ≫ (F S ◁ g) ≫ F(ρ_S)`, and unitality identifies
  `F(ρ_S) = (… ) ≫ ρ`; comparing the kernels, both on the domain (via `μ⁻¹`) and on the target
  (via the isomorphism `F(ρ_S)`), proves
  `ker (F(prTop S)) ≅ ker (F S ◁ g)`.
* `ℤ[S]` is flat (area FLAT, `Work.FLAT.tensorLeft_free_preservesFiniteLimits`), so the functor
  `ℤ[S] ⊗ -` preserves kernels, and `ker (F S ◁ g) ≅ F S ⊗ ker g`.

The point case is the same chain with `S = *`, where `F(*) ≅ 𝟙_ LightCondAb` (via the monoidal
unit isomorphism `εIso`), and the left unitor identifies `ker (F(*) ◁ g) ≅ ker g`.

Everything here is a statement about kernels of morphisms in `LightCondAb`, transported along the
canonical isomorphisms of `CategoryTheory.Limits.kernel.mapIso`. -/

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

/-- The interval `[0,1]`, as an object of `TopCat`; this is the object whose tensor product with
`Y` is the domain `↥Y × ↥unitInterval` of `prTop Y`. -/
abbrev unitIntervalTopCat : TopCat.{0} := TopCat.of ↥unitInterval

/-- `topCatToLightCondSet` — the light condensed set of continuous maps into a topological space —
preserves finite products (indeed all limits), being a right adjoint. -/
instance instMonoidalTopCatToLightCondSet : (topCatToLightCondSet.{0}).Monoidal :=
  ((Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts _).mpr (by
    have : Functor.IsRightAdjoint (topCatToLightCondSet.{0}) :=
      LightCondSet.topCatAdjunction.isRightAdjoint
    infer_instance)).some

/-- `ℤ[-]` is a strong monoidal functor from topological spaces (with the cartesian monoidal
structure) to light condensed abelian groups. -/
instance instMonoidalFreeLightCondAbOfTopFunctor : freeLightCondAbOfTopFunctor.Monoidal :=
  inferInstance

/-- The image under `ℤ[-]` of the unique map `I ⟶ *`: the map `ℤ[I] ⟶ ℤ[*]` whose kernel is the
"augmentation ideal" of the interval. -/
abbrev freeToUnit : freeLightCondAbOfTopFunctor.obj unitIntervalTopCat ⟶
    freeLightCondAbOfTopFunctor.obj (𝟙_ TopCat.{0}) :=
  freeLightCondAbOfTopFunctor.map (SemiCartesianMonoidalCategory.toUnit unitIntervalTopCat)

/-- `prTop Y` is the first projection `fst Y I` of the cartesian monoidal structure. -/
lemma prTop_eq_fst (Y : TopCat.{0}) :
    prTop Y = SemiCartesianMonoidalCategory.fst Y unitIntervalTopCat := by
  rw [SemiCartesianMonoidalCategory.fst_def]
  ext x
  simp only [CategoryTheory.comp_apply, TopCat.whiskerLeft_apply, TopCat.rightUnitor_hom_apply,
    prTop, TopCat.hom_ofHom, ContinuousMap.coe_mk]
  rfl

/-- Naturality of the tensorator `μ` of `ℤ[-]` in the second variable, in the form used here. -/
lemma map_whiskerLeft_eq {Y Z : TopCat.{0}} (X : TopCat.{0}) (f : Y ⟶ Z) :
    freeLightCondAbOfTopFunctor.map (X ◁ f) =
      (Functor.Monoidal.μIso freeLightCondAbOfTopFunctor X Y).inv ≫
        (freeLightCondAbOfTopFunctor.obj X ◁ freeLightCondAbOfTopFunctor.map f) ≫
          (Functor.Monoidal.μIso freeLightCondAbOfTopFunctor X Z).hom := by
  rw [Iso.eq_inv_comp, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_hom]
  exact (Functor.LaxMonoidal.μ_natural_right (F := freeLightCondAbOfTopFunctor) X f).symm

/-- `F(fst X I) = F(X ◁ toUnit I) ≫ F(ρ_X)`, where the second factor is an isomorphism, so the
kernels agree. -/
lemma kernel_prTop_step_fst (X : TopCat.{0}) :
    Nonempty (kernel (freeLightCondAbOfTopFunctor.map (SemiCartesianMonoidalCategory.fst X unitIntervalTopCat)) ≅
      kernel (freeLightCondAbOfTopFunctor.map (X ◁ SemiCartesianMonoidalCategory.toUnit unitIntervalTopCat))) := by
  have h : freeLightCondAbOfTopFunctor.map (SemiCartesianMonoidalCategory.fst X unitIntervalTopCat) =
      freeLightCondAbOfTopFunctor.map (X ◁ SemiCartesianMonoidalCategory.toUnit unitIntervalTopCat) ≫
        (freeLightCondAbOfTopFunctor.mapIso (ρ_ X)).hom := by
    rw [SemiCartesianMonoidalCategory.fst_def, Functor.map_comp]
    rfl
  exact ⟨kernel.mapIso _ _ (Iso.refl _) (freeLightCondAbOfTopFunctor.mapIso (ρ_ X)).symm (by
    rw [h, Iso.symm_hom]
    simp only [Iso.refl_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Category.id_comp])⟩

/-- Since `F = ℤ[-]` is strong monoidal, `F(X ◁ toUnit I)` equals `F(X) ◁ freeToUnit` up to the
tensorators, hence the two kernels agree. -/
lemma kernel_prTop_step_tensor (X : TopCat.{0}) :
    Nonempty (kernel (freeLightCondAbOfTopFunctor.map (X ◁ SemiCartesianMonoidalCategory.toUnit unitIntervalTopCat)) ≅
      kernel (freeLightCondAbOfTopFunctor.obj X ◁ freeToUnit)) := by
  have h := map_whiskerLeft_eq X (SemiCartesianMonoidalCategory.toUnit unitIntervalTopCat)
  exact ⟨kernel.mapIso _ _ (Functor.Monoidal.μIso freeLightCondAbOfTopFunctor X unitIntervalTopCat).symm
    (Functor.Monoidal.μIso freeLightCondAbOfTopFunctor X (𝟙_ TopCat.{0})).symm (by
      rw [h, Iso.symm_hom, Iso.symm_hom]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])⟩

/-- Flatness of `ℤ[S]` turns `ker (ℤ[S] ◁ freeToUnit)` into `ℤ[S] ⊗ ker freeToUnit`.  This is the
`S`-side of the comparison: the kernel of the projection for `S`. -/
lemma kernel_prTop_interval (S : LightProfinite.{0}) :
    Nonempty (kernel (freeLightCondAbOfTopFunctor.map (prTop (LightProfinite.toTopCat.obj S))) ≅
      freeLightCondAbOfTopFunctor.obj (LightProfinite.toTopCat.obj S) ⊗ kernel freeToUnit) := by
  have hfin : PreservesFiniteLimits
      (tensorLeft (freeLightCondAbOfTopFunctor.obj (LightProfinite.toTopCat.obj S))) :=
    Work.FLAT.tensorLeft_free_preservesFiniteLimits (LightProfinite.toTopCat.obj S).toLightCondSet
  letI := hfin
  refine ⟨?_⟩
  rw [prTop_eq_fst (LightProfinite.toTopCat.obj S)]
  refine (kernel_prTop_step_fst _).some.trans ((kernel_prTop_step_tensor _).some.trans ?_)
  exact (PreservesKernel.iso
    (tensorLeft (freeLightCondAbOfTopFunctor.obj (LightProfinite.toTopCat.obj S))) freeToUnit).symm

/-- The point case: the kernel of `ℤ[prTop *]` is the kernel of `freeToUnit` (compare with
`ker (ℤ[S] ◁ freeToUnit)` via the unit isomorphism `F(*) ≅ 𝟙_` and the left unitor). -/
lemma kernel_prTop_point :
    Nonempty (kernel (freeLightCondAbOfTopFunctor.map
        (prTop (LightProfinite.toTopCat.obj (LightProfinite.of PUnit.{1})))) ≅ kernel freeToUnit) := by
  refine ⟨?_⟩
  rw [prTop_eq_fst (LightProfinite.toTopCat.obj (LightProfinite.of PUnit.{1}))]
  refine (kernel_prTop_step_fst (𝟙_ TopCat.{0})).some.trans
    ((kernel_prTop_step_tensor (𝟙_ TopCat.{0})).some.trans ?_)
  refine (kernel.mapIso _ _
    (MonoidalCategory.whiskerRightIso (Functor.Monoidal.εIso freeLightCondAbOfTopFunctor).symm
      (freeLightCondAbOfTopFunctor.obj unitIntervalTopCat))
    (MonoidalCategory.whiskerRightIso (Functor.Monoidal.εIso freeLightCondAbOfTopFunctor).symm
      (freeLightCondAbOfTopFunctor.obj (𝟙_ TopCat.{0}))) ?_).trans
    (kernel.mapIso (𝟙_ LightCondAb ◁ freeToUnit) freeToUnit
      (λ_ (freeLightCondAbOfTopFunctor.obj unitIntervalTopCat))
      (λ_ (freeLightCondAbOfTopFunctor.obj (𝟙_ TopCat.{0}))) ?_)
  · simp only [MonoidalCategory.whiskerRightIso_hom]
    exact MonoidalCategory.whisker_exchange (Functor.Monoidal.εIso freeLightCondAbOfTopFunctor).symm.hom freeToUnit
  · simpa only [id_tensorHom] using MonoidalCategory.leftUnitor_naturality freeToUnit

theorem kernel_prTop_tensor (S : LightProfinite.{0}) :
    Nonempty (CategoryTheory.Limits.kernel
        (CategoryTheory.Functor.map _root_.LightCondensed.Solid.freeLightCondAbOfTopFunctor
          (Work.ANALYTIC.prTop (LightProfinite.toTopCat.obj S))) ≅
      Work.ATOM.tmul
        ((LightCondensed.free (R := ℤ)).obj S.toCondensed)
        (CategoryTheory.Limits.kernel
          (CategoryTheory.Functor.map _root_.LightCondensed.Solid.freeLightCondAbOfTopFunctor
            (Work.ANALYTIC.prTop
              (LightProfinite.toTopCat.obj (LightProfinite.of PUnit.{1})))))) := by
  obtain ⟨hS⟩ := kernel_prTop_interval S
  obtain ⟨hPt⟩ := kernel_prTop_point
  refine ⟨hS.trans (MonoidalCategory.tensorIso
    ((LightCondensed.free (R := ℤ)).mapIso
      (lightProfiniteToLightCondSetIsoTopCatToLightCondSet.app S)).symm hPt.symm)⟩

end

end Work.ANALYTIC
