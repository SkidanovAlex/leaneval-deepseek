import Mathlib
import Submission.Work.DSG2.Segre.Basic

/-!
# The Segre embedding is a morphism over `Spec A` (area DSG2)

The chart-wise Segre maps `Work.DSG2.Segre.sigma k` are all morphisms over `Spec A`, hence so is
their gluing: `σ ≫ toSpec N = fst ≫ toSpec A a`.
-/

open CategoryTheory AlgebraicGeometry Limits MvPolynomial
open scoped TensorProduct

namespace Work.DSG2.Segre

universe u

variable (A : Type u) [CommRing A] (a b : ℕ)

@[reassoc (attr := simp)]
lemma chartIso_inv_chartIncl (k : Fin (a+1) × Fin (b+1)) :
    (chartIso A a b k).inv ≫ chartIncl A a b k.1 k.2 = (V A a b k).ι := by
  rw [← chartIso_hom_ι A a b k, Iso.inv_hom_id_assoc]

@[reassoc]
lemma chartIncl_fst (k : Fin (a+1) × Fin (b+1)) :
    chartIncl A a b k.1 k.2 ≫ pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) =
      Spec.map (CommRingCat.ofHom (algebraMap (chartRingA A a k.1) (chartRing A a b k))) ≫
        Work.DSG4c.chartι A a k.1 := by
  simp only [chartIncl]
  rw [Category.assoc, pullback.map, pullback.lift_fst, ← Category.assoc, pullbackSpecIso_inv_fst']

@[reassoc]
lemma chartIso_hom_sigmaChart (k : Fin (a+1) × Fin (b+1)) :
    (chartIso A a b k).hom ≫ sigmaChart A a b k =
      Spec.map (CommRingCat.ofHom (segreChart A a b k)) := by
  simp only [sigmaChart]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

lemma segreChart_algebraMap (k : Fin (a+1) × Fin (b+1)) (c : A) :
    segreChart A a b k (algebraMap A (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k)) c) =
      algebraMap A (chartRing A a b k) c := by
  rw [segreChart, RingHom.comp_apply, awayChart_algebraMap,
    Work.DSG4c.ChartPushout.polyToChart_chartMap]
  simp

/-- The chart-wise Segre maps are morphisms over `Spec A`. -/
lemma sigma_toSpec (k : Fin (a+1) × Fin (b+1)) :
    sigma A a b k ≫ DSMap.PSpace.toSpec A (segreN a b) =
      (V A a b k).ι ≫ pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) ≫
        DSMap.PSpace.toSpec A a := by
  apply (cancel_epi (chartIso A a b k).hom).mp
  have hL : (chartIso A a b k).hom ≫ (sigma A a b k ≫ DSMap.PSpace.toSpec A (segreN a b)) =
      Spec.map (CommRingCat.ofHom ((segreChart A a b k).comp
        (Work.DSG4c.chartMap A (segreN a b) (toIdx a b k)))) := by
    simp only [sigma, Category.assoc]
    rw [← Category.assoc, chartIso_hom_sigmaChart, Work.DSG4c.chartι_comp_toSpec,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hR : (chartIso A a b k).hom ≫ ((V A a b k).ι ≫
      pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) ≫
        DSMap.PSpace.toSpec A a) =
      Spec.map (CommRingCat.ofHom ((algebraMap (chartRingA A a k.1) (chartRing A a b k)).comp
        (Work.DSG4c.chartMap A a k.1))) := by
    rw [← Category.assoc, chartIso_hom_ι, ← Category.assoc, chartIncl_fst, Category.assoc,
      Work.DSG4c.chartι_comp_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hψ : (segreChart A a b k).comp (Work.DSG4c.chartMap A (segreN a b) (toIdx a b k)) =
      (algebraMap (chartRingA A a k.1) (chartRing A a b k)).comp
        (Work.DSG4c.chartMap A a k.1) := by
    ext c
    rw [RingHom.comp_apply, RingHom.comp_apply, ← awayChart_algebraMap A (segreN a b) (toIdx a b k),
      segreChart_algebraMap, ← awayChart_algebraMap A a k.1]
    exact (IsScalarTower.algebraMap_apply A (chartRingA A a k.1) (chartRing A a b k) c).symm
  rw [hL, hR, ← hψ]

/-- The glued Segre map is a morphism over `Spec A`. -/
theorem glue_toSpec (hcompat : ∀ k k' : Fin (a+1) × Fin (b+1),
      CategoryTheory.CategoryStruct.comp
          (CategoryTheory.Limits.pullback.fst (V A a b k).ι (V A a b k').ι) (sigma A a b k) =
        CategoryTheory.CategoryStruct.comp
          (CategoryTheory.Limits.pullback.snd (V A a b k).ι (V A a b k').ι) (sigma A a b k')) :
    ((cover A a b).glueMorphisms (sigma A a b) hcompat) ≫ DSMap.PSpace.toSpec A (segreN a b) =
      (pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)) ≫
        DSMap.PSpace.toSpec A a := by
  apply (cover A a b).hom_ext
  intro k
  have h1 : (cover A a b).f k ≫
      Scheme.Cover.glueMorphisms (cover A a b) (sigma A a b) hcompat = sigma A a b k :=
    Scheme.Cover.ι_glueMorphisms (cover A a b) (sigma A a b) hcompat k
  rw [← Category.assoc, h1]
  exact sigma_toSpec A a b k

end Work.DSG2.Segre
