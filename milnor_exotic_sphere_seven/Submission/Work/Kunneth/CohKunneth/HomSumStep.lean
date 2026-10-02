import Mathlib
import Submission.Work.Kunneth.CohKunneth.EZStep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

open Work.Cohomology (dualComplex dualComplexMap Cochain cochainDiff cohomologyClassOf
  cohomologyClassOf_congr)

variable {C D : ChainComplex (ModuleCat ℤ) ℕ} {M : ℕ → ModuleCat ℤ}

/-- The transpose of the "section of the homology projection" `tpMap 𝟙 ι`, as a cochain map
`dual(C ⊗ D) ⟶ dual(C ⊗ sumShift M)`: the step that replaces the second factor by its
homology. -/
noncomputable def homSumDualMap (ι : sumShift M ⟶ D) :
    dualComplex ℤ (tpC C D) ⟶ dualComplex ℤ (tpC C (sumShift M)) :=
  dualComplexMap ℤ (tpC C (sumShift M)) (tpC C D)
    (tpMap C C (sumShift M) D (𝟙 C) ι)

/-- The inverse direction on homology: the transpose of `tpMap 𝟙 π`. -/
noncomputable def homSumDualMapInv (π : D ⟶ sumShift M) :
    dualComplex ℤ (tpC C (sumShift M)) ⟶ dualComplex ℤ (tpC C D) :=
  dualComplexMap ℤ (tpC C D) (tpC C (sumShift M)) (tpMap C C D (sumShift M) (𝟙 C) π)

/-- The conjugate composite is exactly the identity (no homotopy needed). -/
theorem homSumDualMapInv_comp_homSumDualMap (π : D ⟶ sumShift M) (ι : sumShift M ⟶ D)
    (hιπ : ι ≫ π = 𝟙 (sumShift M)) :
    homSumDualMapInv π ≫ homSumDualMap ι = 𝟙 (dualComplex ℤ (tpC C (sumShift M))) := by
  rw [homSumDualMap, homSumDualMapInv, ← Work.Cohomology.dualComplexMap_comp ℤ
    (tpMap C C (sumShift M) D (𝟙 C) ι) (tpMap C C D (sumShift M) (𝟙 C) π)]
  rw [tpMap_comp, Category.id_comp, hιπ, tpMap_id, Work.Cohomology.dualComplexMap_id]

/-- The conjugated composite is the transpose of `tpMap 𝟙 (π ≫ ι)`. -/
theorem homSumDualMap_comp_homSumDualMapInv (π : D ⟶ sumShift M) (ι : sumShift M ⟶ D) :
    homSumDualMap ι ≫ homSumDualMapInv π
      = dualComplexMap ℤ (tpC C D) (tpC C D) (tpMap C C D D (𝟙 C) (π ≫ ι)) := by
  rw [homSumDualMap, homSumDualMapInv, ← Work.Cohomology.dualComplexMap_comp ℤ
    (tpMap C C D (sumShift M) (𝟙 C) π) (tpMap C C (sumShift M) D (𝟙 C) ι)]
  rw [tpMap_comp, Category.id_comp]

theorem homologyMap_homSumDualMapInv_comp_homSumDualMap (π : D ⟶ sumShift M)
    (ι : sumShift M ⟶ D) (hιπ : ι ≫ π = 𝟙 (sumShift M)) (n : ℕ) :
    HomologicalComplex.homologyMap (homSumDualMapInv π) n
        ≫ HomologicalComplex.homologyMap (homSumDualMap ι) n
      = 𝟙 ((dualComplex ℤ (tpC C (sumShift M))).homology n) := by
  rw [← HomologicalComplex.homologyMap_comp, homSumDualMapInv_comp_homSumDualMap π ι hιπ,
    HomologicalComplex.homologyMap_id]

theorem homologyMap_homSumDualMap_comp_homSumDualMapInv (π : D ⟶ sumShift M)
    (ι : sumShift M ⟶ D) (hH : Homotopy (π ≫ ι) (𝟙 D)) (n : ℕ) :
    HomologicalComplex.homologyMap (homSumDualMap ι) n
        ≫ HomologicalComplex.homologyMap (homSumDualMapInv π) n
      = 𝟙 ((dualComplex ℤ (tpC C D)).homology n) := by
  rw [← HomologicalComplex.homologyMap_comp, homSumDualMap_comp_homSumDualMapInv π ι]
  have hhomot : Homotopy
      (dualComplexMap ℤ (tpC C D) (tpC C D) (tpMap C C D D (𝟙 C) (𝟙 D)))
      (dualComplexMap ℤ (tpC C D) (tpC C D) (tpMap C C D D (𝟙 C) (π ≫ ι))) :=
    Work.Cohomology.dualHomotopy ℤ
      (Classical.choice (tpMap_homotopy C C D D (𝟙 C) (𝟙 C) (π ≫ ι) (𝟙 D)
        (Homotopy.refl _) hH))
  rw [(Homotopy.homologyMap_eq hhomot n).symm, tpMap_id,
    Work.Cohomology.dualComplexMap_id, HomologicalComplex.homologyMap_id]

/-- **The step replacing the second factor by its homology**, on cohomology. -/
noncomputable def homSumIso (π : D ⟶ sumShift M) (ι : sumShift M ⟶ D)
    (hιπ : ι ≫ π = 𝟙 (sumShift M)) (hH : Homotopy (π ≫ ι) (𝟙 D)) (n : ℕ) :
    (dualComplex ℤ (tpC C D)).homology n
      ≅ (dualComplex ℤ (tpC C (sumShift M))).homology n :=
  Iso.mk (HomologicalComplex.homologyMap (homSumDualMap ι) n)
    (HomologicalComplex.homologyMap (homSumDualMapInv π) n)
    (homologyMap_homSumDualMap_comp_homSumDualMapInv π ι hH n)
    (homologyMap_homSumDualMapInv_comp_homSumDualMap π ι hιπ n)

/-- **The value rule of the splitting step**: the transpose of `tpMap 𝟙 ι`, evaluated on an
element of the tensor product, is the original cochain evaluated on the `tpMapLin`-image. -/
theorem homSumDualMap_apply (ι : sumShift M ⟶ D) (n : ℕ)
    (γ : ↥((dualComplex ℤ (tpC C D)).X n)) (x : tpX C (sumShift M) n) :
    (show tpX C (sumShift M) n →ₗ[ℤ] ℤ from
        ((homSumDualMap (C := C) (D := D) ι).f n).hom γ) x
      = (show tpX C D n →ₗ[ℤ] ℤ from γ)
          ((tpMapLin C C (sumShift M) D (𝟙 C) ι n) x) := by
  have h := Work.Cohomology.dualComplexMapComp_apply ℤ (tpC C (sumShift M)) (tpC C D)
    (tpMap C C (sumShift M) D (𝟙 C) ι) n (show tpX C D n →ₗ[ℤ] ℤ from γ) x
  rw [tpMap_f, ModuleCat.hom_ofHom] at h
  exact h

/-- The value of the pulled-back tensor cochain on the `(p,q)`-summand is `α(u)·β(ι h)`. -/
theorem homSumDualMap_value (ι : sumShift M ⟶ D) (p q : ℕ)
    (α : ↥(C.X p) →ₗ[ℤ] ℤ) (β : ↥(D.X q) →ₗ[ℤ] ℤ)
    (u : ↥(C.X p)) (h : ↥(M q)) :
    (show tpX C (sumShift M) (p + q) →ₗ[ℤ] ℤ from
        ((homSumDualMap (C := C) (D := D) ι).f (p + q)).hom
          (tensorCochain C D (p + q) ⟨(p, q), rfl⟩ α β))
        (tpLof C (sumShift M) (p + q) ⟨(p, q), rfl⟩ (u ⊗ₜ[ℤ] h))
      = α u * β ((ι.f q).hom h) := by
  rw [homSumDualMap_apply, tpMapLin_tmul, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_apply]
  exact tensorCochain_tpLof_tmul C D (p + q) ⟨(p, q), rfl⟩ α β u ((ι.f q).hom h)

end

end Work.Kunneth
