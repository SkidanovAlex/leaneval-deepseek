import Mathlib
import Submission.Work.Whitney.TCMProdDefs
import Submission.Work.Whitney.tcmUnitLeftOne
import Submission.Work.Whitney.tcmModelMul
import Submission.Work.Whitney.tcmF_inv_general

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.unusedVariables false

/-!
# The `n = 0` case of the rank-one model product formula

The target `Work.Whitney.tcmProd_rankOne_zero` is the first case `n = 0` of

  `tcmProd Y n 1 (Mpun n Y) (Mpun 1 Y) = (-1)^n • Mpun (n+1) Y`

(the general `n` is `Work.Whitney.tcmProd_rankOne_signed`), and it is *sign-free*: it is the **left
unit law** of the model product, because the degree-`0` class `Mpun 0 Y` sits over the empty closed
set `tcmA Y 0 1 = ∅` and the rank-one class sits over `tcmC Y 0 1`, which is the punctured set in
the `ℝ^0 × ℝ^1` coordinates.

## The proof

Write `A := tcmA Y 0 1`, `C := tcmC Y 0 1`, `X := tcmX Y 0 1` and let

* `M := relCohMap (id : C(X,X)) C (A ∪ C) (Or.inr)` — the map `H^1(X, A∪C) → H^1(X, C)`,
* `Φ := relCohMap (Fib.tcmF_inv Y 0 1) (Punct Y 1) (A ∪ C) …` — the coordinate identification into
  the punctured group,
* `Φ' := relCohMap (Fib.tcmF_inv Y 0 1) (Punct Y 1) C …`.

Then

* `Φ = M ≫ Φ'` — `relCohMap_compA` with the identity (the pair conditions `Or.inr`/the two
  membership statements agree),
* `M (cup) = pr₂^*(Mpun 1 Y)` — the **left unit law** `Work.Whitney.tcmRelCup_unit_left_one` (proved
  in `tcmUnitLeftOne.lean`) applied to `u = pr₁^*(Mpun 0 Y)`, whose absolute image is `1` because
  `Mpun 0` is the unit class (`Work.Whitney.relToAbs_Mpun_zero`) and pullback fixes `1`
  (`Work.Thom.CohMap_oneH`),
* `Φ' (pr₂^*(Mpun 1 Y)) = Mpun 1 Y` — `pr₂ ∘ tcmF_inv = id`, so `pr₂^* ≫ Φ' = 1`
  (`relCohMap_compA` + `relCohMap_congrA` + `relCohMap_idA`),

whence `tcmProd Y 0 1 (Mpun 0 Y) (Mpun 1 Y) = Φ(cup) = Φ'(M cup) = Φ'(pr₂^*(Mpun 1 Y)) = Mpun 1 Y`.

The only genuine input is the left unit law; everything else is bookkeeping with the inverse
`Fib.tcmF_inv` of the coordinate identification `tcmF`, whose second fibre coordinate is *unchanged*
(`ℝ^0 × ℝ^1 ≅ ℝ^{0+1}` keeps the second factor).
-/

namespace Work.Whitney

open Work.Thom
open CategoryTheory

noncomputable section

/-! ## The coordinate identification to the punctured group and back -/

/-- In the identification `ℝ^0 × ℝ^1 ≅ ℝ^{0+1}` the second fibre coordinate is unchanged: the
`ℝ^0` component is a subsingleton. -/
theorem tcmSumLin_symm_zero_snd (u : EuclideanSpace ℝ (Fin (0+1))) :
    ((tcmSumLin 0 1).symm u).2 = u := by
  have h : (tcmSumLin 0 1).symm = EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 0) (m := 1) := by
    simp [tcmSumLin]
  rw [h]
  ext j
  rw [Work.Thom.finAddEquivProd_snd]
  rw [finSumFinEquiv_apply_right]
  simp

/-- The pair condition of `Fib.tcmF_inv Y 0 1` over the second summand: the punctured part of
`B × ℝ^1` is carried into the closed set `tcmC Y 0 1` (the points with non-zero second fibre
coordinate). -/
theorem tcmF_inv_mem_tcmC_of_punct (Y : Type) [TopologicalSpace Y] :
    ∀ x ∈ Punct Y 1, Fib.tcmF_inv Y 0 1 x ∈ tcmC Y 0 1 := by
  intro x hx
  simp only [Set.mem_ofPred_eq, Fib.tcmF_inv_apply, tcmC]
  rw [tcmSumLin_symm_zero_snd x.2]
  exact hx

/-- **`tcmPr2` is a left inverse of the coordinate identification**: on `Y × ℝ^{0+1} ≅ Y × ℝ^1` the
projection onto the second summand undoes `Fib.tcmF_inv Y 0 1`. -/
theorem tcmPr2_comp_tcmF_inv_zero (Y : Type) [TopologicalSpace Y] :
    (tcmPr2 Y 0 1).comp (Fib.tcmF_inv Y 0 1)
      = ContinuousMap.id (Y × EuclideanSpace ℝ (Fin 1)) := by
  apply ContinuousMap.ext
  intro y
  exact Prod.ext rfl (tcmSumLin_symm_zero_snd y.2)

/-- The pair condition of `tcmPr2 ∘ Fib.tcmF_inv Y 0 1`: the composite preserves the punctured
part. -/
theorem tcmPr2_comp_tcmF_inv_mem_punct (Y : Type) [TopologicalSpace Y] :
    ∀ x ∈ Punct Y 1, (tcmPr2 Y 0 1).comp (Fib.tcmF_inv Y 0 1) x ∈ Punct Y 1 := by
  intro x hx
  show ((tcmSumLin 0 1).symm x.2).2 ≠ 0
  rw [tcmSumLin_symm_zero_snd x.2]
  exact hx

/-! ## The two factorisations of the structure maps -/

/-- **The coordinate identification factors through the second closed set**: pulling a class of
`H^1(tcmX, A ∪ C)` back along `Fib.tcmF_inv Y 0 1` is the same as first restricting to the `C`-pair
and then pulling back. -/
theorem tcmPhiFactor (Y : Type) [TopologicalSpace Y] :
    (relCohMap (Fib.tcmF_inv Y 0 1) (Punct Y 1) (tcmA Y 0 1 ∪ tcmC Y 0 1)
        (tcmF_inv_mem_punct_union Y 0 1) ℤ 1)
      = (relCohMap (ContinuousMap.id (tcmX Y 0 1)) (tcmC Y 0 1) (tcmA Y 0 1 ∪ tcmC Y 0 1)
          (fun x hx => Or.inr hx) ℤ 1)
        ≫ (relCohMap (Fib.tcmF_inv Y 0 1) (Punct Y 1) (tcmC Y 0 1)
            (tcmF_inv_mem_tcmC_of_punct Y) ℤ 1) := by
  rw [relCohMap_compA (Punct Y 1) (tcmC Y 0 1) (tcmA Y 0 1 ∪ tcmC Y 0 1)
      (Fib.tcmF_inv Y 0 1) (ContinuousMap.id (tcmX Y 0 1))
      (tcmF_inv_mem_tcmC_of_punct Y) (fun x hx => Or.inr hx)
      (tcmF_inv_mem_punct_union Y 0 1) ℤ 1]
  rw [relCohMap_congrA (Punct Y 1) (tcmA Y 0 1 ∪ tcmC Y 0 1)
      (ContinuousMap.id_comp (Fib.tcmF_inv Y 0 1)) (tcmF_inv_mem_punct_union Y 0 1)
      (tcmF_inv_mem_punct_union Y 0 1) ℤ 1]

/-- **The pullback along `tcmPr2` is a section of the pullback along the coordinate
identification**: `pr₂^* ≫ (Fib.tcmF_inv Y 0 1)^* = 1` on `H^1(Y × ℝ^1, Punct Y 1)`, because
`tcmPr2 ∘ Fib.tcmF_inv Y 0 1 = id`. -/
theorem tcmPhi_pr2 (Y : Type) [TopologicalSpace Y] :
    (relCohMap (tcmPr2 Y 0 1) (tcmC Y 0 1) (Punct Y 1) (fun x hx => hx) ℤ 1)
      ≫ (relCohMap (Fib.tcmF_inv Y 0 1) (Punct Y 1) (tcmC Y 0 1)
          (tcmF_inv_mem_tcmC_of_punct Y) ℤ 1)
      = CategoryTheory.CategoryStruct.id
          (RelCoh ℤ 1 (Y × EuclideanSpace ℝ (Fin 1)) (Punct Y 1)) := by
  rw [relCohMap_compA (Punct Y 1) (tcmC Y 0 1) (Punct Y 1)
      (Fib.tcmF_inv Y 0 1) (tcmPr2 Y 0 1) (tcmF_inv_mem_tcmC_of_punct Y) (fun x hx => hx)
      (tcmPr2_comp_tcmF_inv_mem_punct Y) ℤ 1]
  rw [relCohMap_congrA (Punct Y 1) (Punct Y 1) (tcmPr2_comp_tcmF_inv_zero Y)
      (tcmPr2_comp_tcmF_inv_mem_punct Y) (fun _ h => h) ℤ 1]
  rw [relCohMap_idA (Punct Y 1) ℤ 1]

/-! ## The lemma -/

/-- **The `n = 0` case of the rank-one model product formula** (the left unit law of the model
product): over any base the external product of the rank-`0` and rank-`1` model classes is the
rank-`1` model class. -/
theorem tcmProd_rankOne_zero (Y : Type) [TopologicalSpace Y] [Subsingleton Y] :
    Work.Whitney.tcmProd Y 0 1 (Work.Thom.Mpun 0 Y) (Work.Thom.Mpun 1 Y)
      = Work.Thom.Mpun 1 Y := by
  -- the absolute image of `pr₁^*(Mpun 0 Y)` is the unit class
  have hu : (Work.Thom.relToAbs ℤ (tcmA Y 0 1) 0).hom
      ((relCohMap (tcmPr1 Y 0 1) (tcmA Y 0 1) (Punct Y 0) (fun x hx => hx) ℤ 0).hom
        (Mpun 0 Y))
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (tcmX Y 0 1))) := by
    have hnat := relCohMap_relToAbs (tcmPr1 Y 0 1) (tcmA Y 0 1) (Punct Y 0) (fun x hx => hx) ℤ 0
    have h := congrArg (fun φ => φ.hom (Mpun 0 Y)) hnat
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [relToAbs_Mpun_zero Y, CohMap_oneH] at h
    exact h
  -- the left unit law of the relative–relative cup
  have hM : (relCohMap (ContinuousMap.id (tcmX Y 0 1)) (tcmC Y 0 1)
        (tcmA Y 0 1 ∪ tcmC Y 0 1) (fun x hx => Or.inr hx) ℤ 1).hom
      ((tcmRelCup (tcmA Y 0 1) (tcmC Y 0 1) (isOpen_tcmA Y 0 1) (isOpen_tcmC Y 0 1) 0 1)
        ((relCohMap (tcmPr1 Y 0 1) (tcmA Y 0 1) (Punct Y 0) (fun x hx => hx) ℤ 0).hom
          (Mpun 0 Y))
        ((relCohMap (tcmPr2 Y 0 1) (tcmC Y 0 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom
          (Mpun 1 Y)))
      = (relCohMap (tcmPr2 Y 0 1) (tcmC Y 0 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom
          (Mpun 1 Y) :=
    tcmRelCup_unit_left_one (tcmA Y 0 1) (tcmC Y 0 1) (isOpen_tcmA Y 0 1) (isOpen_tcmC Y 0 1)
      _ _ hu
  show (relCohMap (Fib.tcmF_inv Y 0 1) (Punct Y 1) (tcmA Y 0 1 ∪ tcmC Y 0 1)
        (tcmF_inv_mem_punct_union Y 0 1) ℤ 1).hom
      ((tcmRelCup (tcmA Y 0 1) (tcmC Y 0 1) (isOpen_tcmA Y 0 1) (isOpen_tcmC Y 0 1) 0 1)
        ((relCohMap (tcmPr1 Y 0 1) (tcmA Y 0 1) (Punct Y 0) (fun x hx => hx) ℤ 0).hom
          (Mpun 0 Y))
        ((relCohMap (tcmPr2 Y 0 1) (tcmC Y 0 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom
          (Mpun 1 Y)))
      = Mpun 1 Y
  rw [tcmPhiFactor Y]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hM]
  have hΦ' := congrArg (fun φ : RelCoh ℤ 1 (Y × EuclideanSpace ℝ (Fin 1)) (Punct Y 1) ⟶
      RelCoh ℤ 1 (Y × EuclideanSpace ℝ (Fin 1)) (Punct Y 1) => φ.hom (Mpun 1 Y))
    (tcmPhi_pr2 Y)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at hΦ'
  exact hΦ'

end

end Work.Whitney
