import Mathlib
import Submission.Work.Thom.realSumStable
import Submission.Work.Thom.chernClass_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The complexification of a real bundle *isomorphism*

`Work.Thom.nonempty_complexificationCore_bundleIso` proves that the complexification of an
isomorphism `Z ⊕ ε¹ ≅ Z'` is an isomorphism.  This module proves the general statement: an
isomorphism of two real bundles with the *same* model fibre `ℝ^k` complexifies to an isomorphism
`ℂ Z ≅ ℂ Z'` (the gauge `b ↦ cxTrans (e.clmGen b)`).

Since `Work.Thom.complexificationCore` takes the model fibre to be `EuclideanSpace ℂ (Fin k)` with
the *same* `k`, an isomorphism between real bundles whose ranks are equal only propositionally must
be transported across the rank equality first; `Work.Agree.chernClass_complexificationCore_eq`
below does exactly that (it `subst`s the rank equality and then applies
`Work.Thom.chernClass_BundleIso`), so that the Chern classes of the complexifications agree.
-/

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-- **Complexification of an isomorphism of real bundles with a common model fibre.**  The gauge is
`b ↦ cxTrans (e.clmGen b)`, the complexification of the fibrewise linear isomorphism. -/
theorem nonempty_complexificationCore_bundleIso {B : Type} [TopologicalSpace B] {k : ℕ}
    {ι ι' : Type}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin k)) ι')
    (e : Work.Thom.BundleIso Z Z') :
    Nonempty (Work.Thom.BundleIso (Work.Thom.complexificationCore Z)
      (Work.Thom.complexificationCore Z')) := by
  refine ⟨{ hom := fun b => (Work.Thom.cxTrans (e.clmGen b)).toLinearMap
            inv := fun b =>
              (Work.Thom.cxTrans ((Work.Thom.BundleIso.symm e).clmGen b)).toLinearMap
            left_inv := fun b x => ?_
            right_inv := fun b y => ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · show Work.Thom.cxTrans ((Work.Thom.BundleIso.symm e).clmGen b)
        (Work.Thom.cxTrans (e.clmGen b) x) = x
    rw [← ContinuousLinearMap.comp_apply, ← Work.Thom.cxTrans_comp]
    have hcomp : ((Work.Thom.BundleIso.symm e).clmGen b).comp (e.clmGen b) = 1 := by
      apply ContinuousLinearMap.ext
      intro z
      rw [ContinuousLinearMap.comp_apply, Work.Thom.BundleIso.clmGen_apply,
        Work.Thom.BundleIso.clmGen_apply]
      exact e.left_inv b z
    rw [hcomp, Work.Thom.cxTrans_one]
    rfl
  · show Work.Thom.cxTrans (e.clmGen b)
        (Work.Thom.cxTrans ((Work.Thom.BundleIso.symm e).clmGen b) y) = y
    rw [← ContinuousLinearMap.comp_apply, ← Work.Thom.cxTrans_comp]
    have hcomp : (e.clmGen b).comp ((Work.Thom.BundleIso.symm e).clmGen b) = 1 := by
      apply ContinuousLinearMap.ext
      intro z
      rw [ContinuousLinearMap.comp_apply, Work.Thom.BundleIso.clmGen_apply,
        Work.Thom.BundleIso.clmGen_apply]
      exact e.right_inv b z
    rw [hcomp, Work.Thom.cxTrans_one]
    rfl
  · refine Work.Thom.continuous_totalSpaceMap_clm (Work.Thom.complexificationCore Z)
      (Work.Thom.complexificationCore Z') (ContinuousMap.id B)
      (fun b => Work.Thom.cxTrans (e.clmGen b)) ?_
    intro i₁ i₂
    refine (Work.Thom.continuousOn_cxTrans_chartExpression Z Z' e i₁ i₂).congr
      (fun b _ => ?_)
    simp only [ContinuousMap.id_apply, Work.Thom.complexificationCore_indexAt]
    rw [Work.Thom.complexificationCore_coordChange_clm Z i₁ _ b,
      Work.Thom.complexificationCore_coordChange_clm Z' _ i₂ b]
    rw [← Work.Thom.cxTrans_comp, ← Work.Thom.cxTrans_comp]
  · refine Work.Thom.continuous_totalSpaceMap_clm (Work.Thom.complexificationCore Z')
      (Work.Thom.complexificationCore Z) (ContinuousMap.id B)
      (fun b => Work.Thom.cxTrans ((Work.Thom.BundleIso.symm e).clmGen b)) ?_
    intro i₁ i₂
    refine (Work.Thom.continuousOn_cxTrans_chartExpression Z' Z
      (Work.Thom.BundleIso.symm e) i₁ i₂).congr (fun b _ => ?_)
    simp only [ContinuousMap.id_apply, Work.Thom.complexificationCore_indexAt]
    rw [Work.Thom.complexificationCore_coordChange_clm Z _ i₂ b,
      Work.Thom.complexificationCore_coordChange_clm Z' i₁ _ b]
    rw [← Work.Thom.cxTrans_comp, ← Work.Thom.cxTrans_comp]

/-- **The Chern classes of the complexification are invariant under isomorphism.**  Two real
bundles over the same base with equal (but possibly syntactically different) ranks and isomorphic
have complexifications with equal Chern classes. -/
theorem chernClass_complexificationCore_eq {B : Type} [TopologicalSpace B] {k k' : ℕ}
    {ι ι' : Type} [Fintype ι] [Fintype ι'] (h : k = k')
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin k')) ι')
    (e : Work.Thom.BundleIso Z Z') (j : ℕ) :
    Work.Thom.chernClass k j (Work.Thom.complexificationCore Z)
      = Work.Thom.chernClass k' j (Work.Thom.complexificationCore Z') := by
  subst h
  obtain ⟨e'⟩ := nonempty_complexificationCore_bundleIso Z Z' e
  exact Work.Thom.chernClass_BundleIso (Work.Thom.complexificationCore Z)
    (Work.Thom.complexificationCore Z') e'

/-- `Nonempty` form of `Work.Agree.chernClass_complexificationCore_eq`. -/
theorem chernClass_complexificationCore_eq' {B : Type} [TopologicalSpace B] {k k' : ℕ}
    {ι ι' : Type} [Fintype ι] [Fintype ι'] (h : k = k')
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin k')) ι')
    (he : Nonempty (Work.Thom.BundleIso Z Z')) (j : ℕ) :
    Work.Thom.chernClass k j (Work.Thom.complexificationCore Z)
      = Work.Thom.chernClass k' j (Work.Thom.complexificationCore Z') := by
  obtain ⟨e⟩ := he
  exact chernClass_complexificationCore_eq h Z Z' e j

end

end Work.Agree
