import Submission.Work.LineBundles.Connected
import Submission.Work.LineBundles.Patch.patching
import Submission.Work.Whitney.chernProductSum_eq_fin
import Submission.Work.LineBundles.PathComp.pathConnectedSpace_pathComp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Additivity of `c₁` on the tensor product: the chapter's main statements

* `Work.LineBundles.tensorLine_c1_additive_pathConnected` — the theorem over a path connected base,
  from the divisibility `Work.LineBundles.divisibility`.
* `Work.LineBundles.tensorLine_c1_additive_of_components` — the theorem over an arbitrary base, given
  that every path component of the base (as the subspace `Work.LineBundles.pathComp`) is path
  connected (which is `Work.LineBundles.PathComp.pathConnectedSpace_pathComp`); the reduction is the
  component patching `Work.LineBundles.Patch.patching`.
* `Work.LineBundles.whitneySum_c1` and `Work.LineBundles.whitneySumFormula_one_one` — the Whitney
  (1,1) form, `c₁(L₁ ⊕ L₂) = c₁(L₁) + c₁(L₂)`, obtained by the determinant trick
  (`Work.Gen.chernClass_one_whitneySum_eq_tensorLine`) from the tensor form.
-/

namespace Work.LineBundles

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The path connected case, unconditionally -/

/-- **Additivity of `c₁` on the tensor product of line bundles over a path connected base**
(unconditional: the divisibility is proved in `Submission/Work/LineBundles/Divis.lean`). -/
theorem tensorLine_c1_additive_pathConnected [PathConnectedSpace B] {ι₁ ι₂ : Type}
    [Fintype ι₁] [Fintype ι₂] (L : LineCore B ι₁) (M : LineCore B ι₂) :
    c1 (Work.Gen.tensorLine L M) = c1 L + c1 M :=
  tensorLine_c1_additive_connected divisibility L M

/-! ## The Whitney sum in degree `1` -/

/-- The right-hand side of the Whitney formula in degree `1` collapses to the sum of the two first
Chern classes. -/
theorem chernProductSum_one_eq_add {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (L : LineCore B ι₁) (M : LineCore B ι₂) :
    Work.Whitney.chernProductSum L M 1 = c1 L + c1 M := by
  have htrans : ∀ {n : ℕ} (h : n = n) (x : Work.Thom.Coh ℤ n B),
      Work.Thom.cohTransport h x = x := by
    intro n h x
    rw [Subsingleton.elim h rfl, Work.Thom.cohTransport_rfl]
  rw [Work.Whitney.chernProductSum_eq_fin, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, Nat.sub_zero, Nat.sub_self, Nat.mul_zero]
  rw [htrans, htrans]
  rw [Work.Thom.chernClass_zero_eq_oneH L, Work.Thom.chernClass_zero_eq_oneH M]
  have h1 : (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 0 2)
      (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) (c1 M) = c1 M :=
    Work.Cohomology.cupH'_one_left ℤ (Work.Whitney.ssB B) 2 (c1 M)
  have h2 : (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) 2 0)
      (c1 L) (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) = c1 L :=
    Work.Cohomology.cupH'_one_right ℤ (Work.Whitney.ssB B) 2 (c1 L)
  rw [h1, h2, add_comm]

/-- **The Whitney sum formula in degree `1` for two line bundles over a path connected base**:
`c₁(L₁ ⊕ L₂) = c₁(L₁) + c₁(L₂)`. -/
theorem whitneySum_c1_pathConnected [PathConnectedSpace B] {ι₁ ι₂ : Type}
    [Fintype ι₁] [Fintype ι₂] (L : LineCore B ι₁) (M : LineCore B ι₂) :
    Work.Thom.chernClass (1 + 1) 1 (Work.Whitney.whitneySum L M) = c1 L + c1 M := by
  rw [Work.Gen.chernClass_one_whitneySum_eq_tensorLine L M]
  exact tensorLine_c1_additive_pathConnected L M

/-! ## The general case, from the component patching -/

/-- **Additivity of `c₁` on the tensor product of line bundles over an arbitrary base**, given that
the path components of the base are path connected (an instance, supplied by
`Work.LineBundles.PathComp.pathConnectedSpace_pathComp`).

The proof: the defect `δ = c₁(L ⊗ M) - c₁(L) - c₁(M)` vanishes on every path component by the
path connected case applied to the component, and the component patching
(`Work.LineBundles.Patch.patching`) turns that into `δ = 0`. -/
theorem tensorLine_c1_additive_of_components
    (hpc : ∀ {B : Type} [TopologicalSpace B] (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of B))),
      PathConnectedSpace ↥(pathComp B c))
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (L : LineCore B ι₁) (M : LineCore B ι₂) :
    c1 (Work.Gen.tensorLine L M) = c1 L + c1 M := by
  have hcomp : ∀ c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of B)),
      (Work.Thom.CohMap (pathCompIncl B c) ℤ 2).hom
        (c1 (Work.Gen.tensorLine L M) - c1 L - c1 M) = 0 := by
    intro c
    haveI := hpc c
    have h := tensorLine_c1_additive_pathConnected
      (L := bundleComap L (pathCompIncl B c)) (M := bundleComap M (pathCompIncl B c))
    rw [map_sub, map_sub, c1_bundleComap (Work.Gen.tensorLine L M) (pathCompIncl B c),
      c1_bundleComap L (pathCompIncl B c), c1_bundleComap M (pathCompIncl B c),
      Work.Gen.tensorLine_bundleComap, h]
    abel
  have h0 := Work.LineBundles.Patch.patching 2 (c1 (Work.Gen.tensorLine L M) - c1 L - c1 M) hcomp
  have h1 : c1 (Work.Gen.tensorLine L M) - c1 L = c1 M := sub_eq_zero.mp h0
  have h2 : c1 (Work.Gen.tensorLine L M) = c1 M + c1 L := sub_eq_iff_eq_add.mp h1
  rw [h2, add_comm]

/-! ## The theorem, unconditionally -/

/-- **Additivity of `c₁` on the tensor product of complex line bundles** — the headline result of
this chapter, over an **arbitrary topological base**, with no hypotheses at all.

The path components of the base are path connected
(`Work.LineBundles.PathComp.pathConnectedSpace_pathComp`), which is exactly the input of
`tensorLine_c1_additive_of_components`. -/
theorem tensorLine_c1_additive {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (L : LineCore B ι₁) (M : LineCore B ι₂) :
    c1 (Work.Gen.tensorLine L M) = c1 L + c1 M :=
  tensorLine_c1_additive_of_components
    (fun c => Work.LineBundles.PathComp.pathConnectedSpace_pathComp c) L M

/-- **The Whitney sum formula in degree `1` for two complex line bundles** over an arbitrary
topological base: `c₁(L₁ ⊕ L₂) = c₁(L₁) + c₁(L₂)` (the determinant trick plus
`tensorLine_c1_additive`). -/
theorem whitneySum_c1 {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (L : LineCore B ι₁) (M : LineCore B ι₂) :
    Work.Thom.chernClass (1 + 1) 1 (Work.Whitney.whitneySum L M) = c1 L + c1 M := by
  rw [Work.Gen.chernClass_one_whitneySum_eq_tensorLine L M]
  exact tensorLine_c1_additive L M

/-- **The degree-`1` input of the Whitney sum formula in ranks `(1,1)`**, in exactly the shape that
`Work.Gen.whitneySumFormulaOneOne` consumes (so that only the degree-`2` top-class
multiplicativity of the WHITNEY area is needed to deduce
`Work.LerayHirsch.WhitneySumFormula 1 1`; see `WhitneyOneOne.lean`). -/
theorem whitneySumOneOne_degree_one {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (L : LineCore B ι₁) (M : LineCore B ι₂) :
    Work.Thom.chernClass (1 + 1) 1 (Work.Whitney.whitneySum L M)
      = Work.Whitney.chernProductSum L M 1 := by
  rw [whitneySum_c1 L M, chernProductSum_one_eq_add L M]

end

end Work.LineBundles
