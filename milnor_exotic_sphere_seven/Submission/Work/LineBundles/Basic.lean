import Submission.Work.LineBundles.Defs
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Elementary lemmas about `c₁` of line bundles

* `Work.LineBundles.c1_bundleComap_const` — the pullback of a line bundle along a **constant** map
  has vanishing `c₁` (it factors through the one-point space, whose positive-degree cohomology
  vanishes).
* `Work.LineBundles.nonempty_bundleIso_tensorLine_comm` / `c1_tensorLine_comm` — the tensor product
  of line bundles is commutative, so `c₁(L ⊗ M) = c₁(M ⊗ L)`.
-/

namespace Work.LineBundles

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-- **The pullback of a line bundle along a constant map has vanishing `c₁`**: it is the pullback of
a bundle over the one-point space, and `H²(pt) = 0`. -/
theorem c1_bundleComap_const {ι : Type} [Fintype ι] (Z : LineCore B ι) (b : B) :
    c1 (bundleComap Z (ContinuousMap.const B b)) = 0 := by
  have hcomp : (ContinuousMap.const PUnit b : C(PUnit, B)).comp
      (ContinuousMap.const B PUnit.unit) = (ContinuousMap.const B b : C(B, B)) := by
    ext y
    rfl
  rw [← hcomp, ← Work.Thom.bundleComap_comp Z (ContinuousMap.const PUnit b)
    (ContinuousMap.const B PUnit.unit)]
  refine Work.Thom.chernClass_bundleComap_eq_zero_of_subsingleton
    (W := bundleComap Z (ContinuousMap.const PUnit b))
    (f := ContinuousMap.const B PUnit.unit) (j := 1) ?_
  exact Work.Thom.subsingleton_cohomology_punit (k := 2 * 1) (by norm_num)

/-- The **commutativity of the tensor product of line-bundle cores**, as a bundle isomorphism: the
two cores have the same transition scalars in the swapped order. -/
theorem nonempty_bundleIso_tensorLine_comm {ι₁ ι₂ : Type}
    (L : LineCore B ι₁) (M : LineCore B ι₂) :
    Nonempty (Work.Thom.BundleIso (Work.Gen.tensorLine L M) (Work.Gen.tensorLine M L)) := by
  refine Work.Whitney.nonempty_bundleIso_of_gauge_fibre (Work.Gen.tensorLine L M)
    (Work.Gen.tensorLine M L)
    (ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 1))) (Equiv.prodComm ι₁ ι₂) ?_ ?_ ?_
  · intro i
    rw [Work.Gen.tensorLine_baseSet, Work.Gen.tensorLine_baseSet, Equiv.prodComm_apply,
      Prod.swap_prod_mk]
    exact Set.inter_comm _ _
  · intro b
    rfl
  · intro i b
    rw [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp,
      Work.Gen.tensorLine_coordChange, Work.Gen.tensorLine_coordChange]
    congr 1
    simp only [Work.Gen.tensorLine_indexAt, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    ring

/-- **`c₁` is commutative on tensor products of line bundles.** -/
theorem c1_tensorLine_comm {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (L : LineCore B ι₁) (M : LineCore B ι₂) :
    c1 (Work.Gen.tensorLine L M) = c1 (Work.Gen.tensorLine M L) :=
  Work.Thom.chernClass_BundleIso _ _
    (Classical.choice (nonempty_bundleIso_tensorLine_comm L M))

end

end Work.LineBundles
