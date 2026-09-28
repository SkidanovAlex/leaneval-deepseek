import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.MixedCup
import Submission.Work.Cohomology.relCupHNatural
import Submission.Work.Cohomology.sph3DiscMixedDefs

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.Thom

open CategoryTheory

noncomputable section

/-- **Naturality of the mixed Alexander–Whitney product on the relative cochains of a map of
pairs.**  Pulling back the product `a ⌣ b` of an absolute cochain `a` with a relative cochain `b`
is the product of the pullbacks. -/
lemma relMapLM_cup {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B) (m n : ℕ)
    (a : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of Y)) m)
    (b : Work.Cohomology.relKern ℤ (TopCat.of Y) B n)
    (hmem : Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of Y)) a b.1 ∈
      Work.Cohomology.relKern ℤ (TopCat.of Y) B (m + n)) :
    ((Work.Cohomology.relMapLM ℤ A B (TopCat.ofHom f) hf (m + n)
        ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of Y)) a b.1, hmem⟩).1) =
      Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X))
        (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
            (ModuleCat.of ℤ ℤ)).f m).hom.dualMap a)
        ((Work.Cohomology.relMapLM ℤ A B (TopCat.ofHom f) hf n b).1) := by
  rw [Work.Cohomology.relMapLM_coe, Work.Cohomology.relMapLM_coe]
  simp only [Work.Cohomology.dualChainMap_f_hom, Work.Cohomology.chainMap_f_eq]
  exact (Work.Cohomology.cupNatural ℤ (TopCat.toSSet.map (TopCat.ofHom f)) a b.1).symm

/-- **Naturality of the mixed cup product under a map of pairs.**  For a continuous map `f : X → Y` carrying `A ⊆ X` into `B ⊆ Y`, an absolute class `x ∈ H^m(Y;ℤ)` and a relative class `z ∈ H^n(Y,B;ℤ)`, `f^*(x ⌣ z) = (f^*x) ⌣ (f^*z)`; both sides live in `H^{m+n}(X,A;ℤ)`. -/
theorem mixedCupC_pairNatural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B) (m n : ℕ)
    (x : Coh ℤ m Y) (z : RelCoh ℤ n Y B) :
    (relCohMap f A B hf ℤ (m + n)).hom ((mixedCupC ℤ B m n) x z)
      = (mixedCupC ℤ A m n) ((CohMap f ℤ m).hom x)
          ((relCohMap f A B hf ℤ n).hom z) := by
  change (relCohMap f A B hf ℤ (m + n)).hom
      ((Work.Cohomology.mixedCup (TopCat.of Y) B m n) x z)
    = (Work.Cohomology.mixedCup (TopCat.of X) A m n) ((CohMap f ℤ m).hom x)
        ((relCohMap f A B hf ℤ n).hom z)
  obtain ⟨a, ha, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of Y)) m x
  obtain ⟨b, hb, rfl⟩ := Work.Cohomology.exists_relClassOf ℤ (TopCat.of Y) B n z
  obtain ⟨hmemY, hcocY, hcupY⟩ :=
    Work.Cohomology.mixedCup_apply (TopCat.of Y) B m n a b ha hb
  have hCoh : (CohMap f ℤ m).hom
        (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of Y)) a ha) =
      Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of X))
        (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
            (ModuleCat.of ℤ ℤ)).f m).hom.dualMap a)
        (Work.Cohomology.cochainDiff_dualMap_chainComplexMap ℤ
          (TopCat.toSSet.map (TopCat.ofHom f)) a ha) :=
    Work.Cohomology.singularCohomologyMap_classOf ℤ (TopCat.ofHom f) a ha
  have hRel := @Work.Cohomology.homologyMap_relComplexMap_relClassOf ℤ _ (TopCat.of X)
    (TopCat.of Y) A B (TopCat.ofHom f) hf n b hb
  obtain ⟨hmemX, hcocX, hcupX⟩ := Work.Cohomology.mixedCup_apply (TopCat.of X) A m n
    (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
        (ModuleCat.of ℤ ℤ)).f m).hom.dualMap a)
    (@Work.Cohomology.relMapLM ℤ _ (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom f) hf n b)
    (Work.Cohomology.cochainDiff_dualMap_chainComplexMap ℤ
      (TopCat.toSSet.map (TopCat.ofHom f)) a ha)
    (@Work.Cohomology.relDiffLM_relMapLM ℤ _ (TopCat.of X) (TopCat.of Y) A B
      (TopCat.ofHom f) hf n b hb)
  have hL1 := @Work.Cohomology.homologyMap_relComplexMap_relClassOf ℤ _ (TopCat.of X)
    (TopCat.of Y) A B (TopCat.ofHom f) hf (m + n)
    ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of Y)) a b.1, hmemY⟩ hcocY
  have heq : (@Work.Cohomology.relMapLM ℤ _ (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom f)
        hf (m + n)
        ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of Y)) a b.1, hmemY⟩)
      = ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X))
          (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
              (ModuleCat.of ℤ ℤ)).f m).hom.dualMap a)
          ((@Work.Cohomology.relMapLM ℤ _ (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom f)
            hf n b).1), hmemX⟩ := by
    apply Subtype.ext
    exact relMapLM_cup f A B hf m n a b hmemY
  rw [hcupY, hL1, hCoh, hRel, hcupX]
  exact Work.Cohomology.relClassOf_congr ℤ (TopCat.of X) A _ _ heq

end

end Work.Thom
