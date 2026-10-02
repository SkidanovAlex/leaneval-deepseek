import Mathlib
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.complexPullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The Whitney sum of gluing data over an arbitrary field

`Submission/Work/TangentClasses/Bundle.lean` defines the Whitney sum `RealBundle.sum` of two *real*
gluing data.  The Whitney formula for Pontryagin and Chern classes (G2c of `README.md`
ADDENDUM 22) needs the same operation over `ℂ`, so this module defines it once, for an arbitrary
`NontriviallyNormedField`, as `Work.Thom.bundleSum`: the index type is `ι₁ × ι₂`, the model fibre is
`F₁ × F₂`, and the transition function is the block-diagonal `coordChange p q x × coordChange' p q x`.

Its defining equations are `rfl`, it is compatible with `Work.Thom.bundleComap`
(`Work.Thom.bundleComap_bundleSum`), and the trivial bundle is a unit
(`Work.Thom.bundleSum_trivial`), which is the bundle-level statement of *stability*.
-/

namespace Work.Thom

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
variable {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
variable {ι₁ ι₂ : Type*}

/-- **The Whitney sum (direct sum) of two gluing data** over a common refinement of the two covers
(indexed by `ι₁ × ι₂`): the transition function is the block-diagonal
`(coordChange₁) × (coordChange₂)` on the product fibre `F₁ × F₂`. -/
noncomputable def bundleSum (Z₁ : VectorBundleCore 𝕜 B F₁ ι₁) (Z₂ : VectorBundleCore 𝕜 B F₂ ι₂) :
    VectorBundleCore 𝕜 B (F₁ × F₂) (ι₁ × ι₂) where
  baseSet p := Z₁.baseSet p.1 ∩ Z₂.baseSet p.2
  isOpen_baseSet p := (Z₁.isOpen_baseSet p.1).inter (Z₂.isOpen_baseSet p.2)
  indexAt x := (Z₁.indexAt x, Z₂.indexAt x)
  mem_baseSet_at x := ⟨Z₁.mem_baseSet_at x, Z₂.mem_baseSet_at x⟩
  coordChange p q x := (Z₁.coordChange p.1 q.1 x).prodMap (Z₂.coordChange p.2 q.2 x)
  coordChange_self p x hx v := by
    rw [ContinuousLinearMap.coe_prodMap']
    exact Prod.ext (Z₁.coordChange_self p.1 x hx.1 v.1) (Z₂.coordChange_self p.2 x hx.2 v.2)
  continuousOn_coordChange p q :=
    ((Z₁.continuousOn_coordChange p.1 q.1).mono fun _ hx => ⟨hx.1.1, hx.2.1⟩).prod_mapL 𝕜
      ((Z₂.continuousOn_coordChange p.2 q.2).mono fun _ hx => ⟨hx.1.2, hx.2.2⟩)
  coordChange_comp p q r x hx v := by
    rw [ContinuousLinearMap.coe_prodMap', ContinuousLinearMap.coe_prodMap',
      ContinuousLinearMap.coe_prodMap']
    exact Prod.ext
      (Z₁.coordChange_comp p.1 q.1 r.1 x ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2.1⟩ v.1)
      (Z₂.coordChange_comp p.2 q.2 r.2 x ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩ v.2)

@[simp] theorem bundleSum_baseSet (Z₁ : VectorBundleCore 𝕜 B F₁ ι₁)
    (Z₂ : VectorBundleCore 𝕜 B F₂ ι₂) (p : ι₁ × ι₂) :
    (bundleSum Z₁ Z₂).baseSet p = Z₁.baseSet p.1 ∩ Z₂.baseSet p.2 := rfl

@[simp] theorem bundleSum_indexAt (Z₁ : VectorBundleCore 𝕜 B F₁ ι₁)
    (Z₂ : VectorBundleCore 𝕜 B F₂ ι₂) (x : B) :
    (bundleSum Z₁ Z₂).indexAt x = (Z₁.indexAt x, Z₂.indexAt x) := rfl

@[simp] theorem bundleSum_coordChange (Z₁ : VectorBundleCore 𝕜 B F₁ ι₁)
    (Z₂ : VectorBundleCore 𝕜 B F₂ ι₂) (p q : ι₁ × ι₂) (x : B) :
    (bundleSum Z₁ Z₂).coordChange p q x =
      (Z₁.coordChange p.1 q.1 x).prodMap (Z₂.coordChange p.2 q.2 x) := rfl

/-- **The Whitney sum commutes with the pullback**, definitionally. -/
theorem bundleComap_bundleSum {B' : Type*} [TopologicalSpace B'] (f : C(B', B))
    (Z₁ : VectorBundleCore 𝕜 B F₁ ι₁) (Z₂ : VectorBundleCore 𝕜 B F₂ ι₂) :
    bundleComap (bundleSum Z₁ Z₂) f = bundleSum (bundleComap Z₁ f) (bundleComap Z₂ f) := rfl

/-- **Adding a trivial summand does not change the underlying affine/gluing structure**: the Whitney
sum with the trivial bundle has the constant transition functions in the second factor (the
bundle-level form of *stability* of the characteristic classes). -/
theorem bundleSum_trivial_coordChange {ι₀ : Type*} [Inhabited ι₀]
    (Z : VectorBundleCore 𝕜 B F₁ ι₁) (p q : ι₁ × ι₀) (x : B) :
    (bundleSum Z (trivialVectorBundleCore 𝕜 B F₂ ι₀)).coordChange p q x
      = (Z.coordChange p.1 q.1 x).prodMap (ContinuousLinearMap.id 𝕜 F₂) := by
  rw [bundleSum_coordChange]
  rfl

end

end Work.Thom
