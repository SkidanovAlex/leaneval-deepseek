import Mathlib
import Submission.Work.LerayHirsch.LhTwoCoverDefs
import Submission.Work.LerayHirsch.LhGlueDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [-instance] AddCommGroup.toIntModule

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom Work.Cohomology
open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- Element-level formula for `luTM`. -/
theorem luTM_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (A : Set Y) (n : ℕ) (c : RelCoh ℤ n Y A) (k : ℕ)
    (z : ↑(pdCoh (TopCat.of X) (∅ : Set X) k)) :
    (luTM π A n c k).hom z
      = (mixedCupC ℤ A k n) ((CohMap π ℤ k).hom ((pdCohIso X k).hom z)) c := by
  simp only [luTM_eq_relPb_Ttop, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [Ttop_apply, relPb_apply]

/-- The mixed cup product, composed with `pdCohIso`. -/
theorem pdCohIso_mixedCup {X : Type} [TopologicalSpace X] (m n : ℕ) (x : Coh ℤ m X)
    (y : RelCoh ℤ n X (∅ : Set X)) :
    (pdCohIso X (m + n)).hom ((mixedCupC ℤ (∅ : Set X) m n) x y)
      = cupH' ℤ (Work.Whitney.ssB X) m n x ((pdCohIso X n).hom y) :=
  mixedCup_relToAbs (X := X) (∅ : Set X) m n x y

/-- **The `i`-th summand of the Leray–Hirsch comparison map, in the `Coh` model.** -/
theorem MvCM_translate (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (i : lhIdx m k) (a : ↑(pdCoh (TopCat.of B) (∅ : Set B) (k - 2 * (i : ℕ)))) :
    (pdCohIso (ProjSpace Z) k).hom ((MvCM Z k i).hom a)
      = cohTransportLM (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)
          ((cupH' ℤ (Work.Whitney.ssB (ProjSpace Z)) (k - 2 * (i : ℕ)) (2 * (i : ℕ))
            ((CohMap (projMap Z) ℤ (k - 2 * (i : ℕ))).hom
              ((pdCohIso B (k - 2 * (i : ℕ))).hom a)) (zetaPow Z i))) := by
  simp only [MvCM, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [pdCohIso_pdCast, luTM_apply]
  rw [show (pdCohIso (ProjSpace Z) (k - 2 * (i : ℕ) + 2 * (i : ℕ))).hom
        ((mixedCupC ℤ (∅ : Set (ProjSpace Z)) (k - 2 * (i : ℕ)) (2 * (i : ℕ)))
          ((CohMap (projMap Z) ℤ (k - 2 * (i : ℕ))).hom
            ((pdCohIso B (k - 2 * (i : ℕ))).hom a)) (zetaRel Z i))
      = cupH' ℤ (Work.Whitney.ssB (ProjSpace Z)) (k - 2 * (i : ℕ)) (2 * (i : ℕ))
          ((CohMap (projMap Z) ℤ (k - 2 * (i : ℕ))).hom
            ((pdCohIso B (k - 2 * (i : ℕ))).hom a))
          ((pdCohIso (ProjSpace Z) (2 * (i : ℕ))).hom (zetaRel Z i)) from
    pdCohIso_mixedCup (X := ProjSpace Z) (k - 2 * (i : ℕ)) (2 * (i : ℕ))
      ((CohMap (projMap Z) ℤ (k - 2 * (i : ℕ))).hom
        ((pdCohIso B (k - 2 * (i : ℕ))).hom a)) (zetaRel Z i)]
  rw [show (pdCohIso (ProjSpace Z) (2 * (i : ℕ))).hom (zetaRel Z i) = zetaPow Z i from by
    rw [zetaRel]
    exact Iso.inv_hom_id_apply (pdCohIso (ProjSpace Z) (2 * (i : ℕ))) (zetaPow Z i)]
  rfl

/-- **The comparison map `MvTM` is the Leray–Hirsch map `lhAny`** (in the `Coh` model). -/
theorem MvTM_translate (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (x : ↑(MvM B m k)) :
    (pdCohIso (ProjSpace Z) k).hom ((MvTM Z k).hom x)
      = lhAny Z k (fun i => (pdCohIso B (k - 2 * (i : ℕ))).hom (x i)) := by
  rw [MvTM_apply, lhAny, lhAnyLM]
  rw [show (pdCohIso (ProjSpace Z) k).hom (∑ i : lhIdx m k, (MvCM Z k i).hom (x i))
      = ∑ i : lhIdx m k, (pdCohIso (ProjSpace Z) k).hom ((MvCM Z k i).hom (x i)) from
    map_sum _ _ Finset.univ]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvCM_translate, lhAnySummand]
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, evalLM]
  congr 1

end
end Work.LerayHirsch

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom Work.Cohomology
open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- **The comparison map `MvTM` is the Leray–Hirsch map `lhAny`** (in the `Coh` model). -/
theorem MvTM_translate_canonical (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (x : ↑(MvM B m k)) :
    (Work.Thom.pdCohIso (Work.LerayHirsch.ProjSpace Z) k).hom
        ((Work.LerayHirsch.MvTM Z k).hom x)
      = Work.LerayHirsch.lhAny Z k
          (fun i => (Work.Thom.pdCohIso B (k - 2 * (i : ℕ))).hom (x i)) :=
  MvTM_translate Z k x

end
end Work.LerayHirsch
