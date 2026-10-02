import Mathlib
import Submission.Work.Thom.ThomAPI

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
# The direct sum of two gluing-data bundles, in the standard fibre

This module starts the *Whitney* subproject (`Submission/Work/Whitney/`): the direct sum of two
complex (resp. real) gluing-data bundles over a common base, presented in the **standard** fibre
`EuclideanSpace ℂ (Fin (m₁ + m₂))` (resp. `EuclideanSpace ℝ (Fin (k₁ + k₂))`), over the **product
cover** `ι₁ × ι₂`.  The standard fibre is what the Chern recursion `Work.Thom.chernClass` requires
(its arguments are bundles with model fibre exactly `EuclideanSpace ℂ (Fin m)`).

The construction is

* `Work.Whitney.sumCore e Z₁ Z₂` — for an arbitrary continuous linear equivalence
  `e : F₁ × F₂ ≃L[𝕜] F`, the gluing data with base set `Z₁.baseSet i ∩ Z₂.baseSet j`, index map
  `x ↦ (Z₁.indexAt x, Z₂.indexAt x)` and transition functions
  `e ∘ (coordChange₁ p q x × coordChange₂ p q x) ∘ e⁻¹` — the block-diagonal transitions
  transported along `e`;
* `Work.Whitney.whitneySum` — the complex case, with `e = Work.Whitney.sumFibreC m₁ m₂`
  (the explicit splitting `ℂ^{m₁} × ℂ^{m₂} ≃L[ℂ] ℂ^{m₁+m₂}` of
  `EuclideanSpace.finAddEquivProd`);
* `Work.Whitney.whitneySumR` — the real case, with `e = Work.Whitney.sumFibreR k₁ k₂`.

Both are *definitions* (no `Classical.choose`): the defining equations
`whitneySum_baseSet`, `whitneySum_indexAt`, `whitneySum_coordChange` hold by `rfl`, the sum commutes
with the pullback `Work.Thom.bundleComap` (`whitneySum_bundleComap`), and the trivial bundle is a
unit (`whitneySum_trivial_right_coordChange`).

## The compatibility with the real/complex structure

The explicit splittings are chosen so that they commute with `Work.Thom.cxOfReal`; the two modules
that record this are `Submission/Work/Whitney/SumFibreCx.lean`
(`Work.Whitney.sumFibreC_cxOfReal`, `Work.Whitney.sumFibreC_cxRePart`, ...) and
`Submission/Work/Whitney/Complexify.lean`, which uses them to prove

* `Work.Whitney.complexificationCore_whitneySumR` —
  `(Z₁ ⊕ Z₂) ⊗_ℝ ℂ = (Z₁ ⊗_ℝ ℂ) ⊕ (Z₂ ⊗_ℝ ℂ)`;
* `Work.Whitney.realification_whitneySum` —
  `(W₁ ⊕ W₂)_ℝ = (W₁)_ℝ ⊕ (W₂)_ℝ`.

These are the bundle-level form of deliverable item 1 of the Whitney subproject.
-/

namespace Work.Whitney

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The explicit splittings -/

/-- **The explicit splitting `ℂ^{m₁} × ℂ^{m₂} ≃L[ℂ] ℂ^{m₁+m₂}`** (coordinate concatenation, via
`EuclideanSpace.finAddEquivProd`).  Being *explicit* (not a `Classical.choose`, unlike
`Work.Thom.prodFinEquiv`) is what makes it comparable with its real counterpart. -/
noncomputable def sumFibreC (m₁ m₂ : ℕ) :
    (EuclideanSpace ℂ (Fin m₁) × EuclideanSpace ℂ (Fin m₂)) ≃L[ℂ]
      EuclideanSpace ℂ (Fin (m₁ + m₂)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := m₁) (m := m₂)).symm

/-- **The explicit splitting `ℝ^{k₁} × ℝ^{k₂} ≃L[ℝ] ℝ^{k₁+k₂}`**. -/
noncomputable def sumFibreR (k₁ k₂ : ℕ) :
    (EuclideanSpace ℝ (Fin k₁) × EuclideanSpace ℝ (Fin k₂)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (k₁ + k₂)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k₁) (m := k₂)).symm

/-! ## The direct sum of gluing data along an arbitrary splitting -/

section SumCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F₁ F₂ F : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {ι₁ ι₂ : Type*}

/-- **The direct sum of two gluing data, glued along a splitting `e : F₁ × F₂ ≃L[𝕜] F`.**  Over the
product cover `ι₁ × ι₂` the transition function of the sum is the block-diagonal transition
`coordChange₁ p q x × coordChange₂ p q x` (on the product fibre `F₁ × F₂`) transported along `e`.
This is `Work.Thom.bundleSum` with the fibre changed to `F` along `e`; the point of doing it in one
step (rather than as `bundleSum` followed by `Work.Thom.exists_coreMapFibre`) is that the defining
equations below are `rfl`. -/
noncomputable def sumCore (e : (F₁ × F₂) ≃L[𝕜] F)
    (Z₁ : VectorBundleCore 𝕜 B F₁ ι₁) (Z₂ : VectorBundleCore 𝕜 B F₂ ι₂) :
    VectorBundleCore 𝕜 B F (ι₁ × ι₂) where
  baseSet p := Z₁.baseSet p.1 ∩ Z₂.baseSet p.2
  isOpen_baseSet p := (Z₁.isOpen_baseSet p.1).inter (Z₂.isOpen_baseSet p.2)
  indexAt x := (Z₁.indexAt x, Z₂.indexAt x)
  mem_baseSet_at x := ⟨Z₁.mem_baseSet_at x, Z₂.mem_baseSet_at x⟩
  coordChange p q x :=
    (e : (F₁ × F₂) →L[𝕜] F).comp
      (((Z₁.coordChange p.1 q.1 x).prodMap (Z₂.coordChange p.2 q.2 x)).comp
        ((e.symm : F →L[𝕜] (F₁ × F₂))))
  coordChange_self p x hx v := by
    have h : (Z₁.coordChange p.1 p.1 x).prodMap (Z₂.coordChange p.2 p.2 x) (e.symm v) = e.symm v := by
      rw [ContinuousLinearMap.coe_prodMap']
      exact Prod.ext (Z₁.coordChange_self p.1 x hx.1 (e.symm v).1)
        (Z₂.coordChange_self p.2 x hx.2 (e.symm v).2)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [h]
    exact e.apply_symm_apply v
  continuousOn_coordChange p q := by
    have h₁ : ContinuousOn
        (fun x => (Z₁.coordChange p.1 q.1 x).prodMap (Z₂.coordChange p.2 q.2 x))
        ((Z₁.baseSet p.1 ∩ Z₂.baseSet p.2) ∩ (Z₁.baseSet q.1 ∩ Z₂.baseSet q.2)) :=
      ((Z₁.continuousOn_coordChange p.1 q.1).mono fun _ hx => ⟨hx.1.1, hx.2.1⟩).prod_mapL 𝕜
        ((Z₂.continuousOn_coordChange p.2 q.2).mono fun _ hx => ⟨hx.1.2, hx.2.2⟩)
    exact ContinuousOn.clm_comp continuousOn_const
      (ContinuousOn.clm_comp h₁ continuousOn_const)
  coordChange_comp p q r x hx v := by
    have hpq : x ∈ Z₁.baseSet p.1 ∩ Z₁.baseSet q.1 ∩ Z₁.baseSet r.1 :=
      ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2.1⟩
    have hpq' : x ∈ Z₂.baseSet p.2 ∩ Z₂.baseSet q.2 ∩ Z₂.baseSet r.2 :=
      ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩
    have hcomp : ∀ w : F₁ × F₂,
        (Z₁.coordChange q.1 r.1 x).prodMap (Z₂.coordChange q.2 r.2 x)
            ((Z₁.coordChange p.1 q.1 x).prodMap (Z₂.coordChange p.2 q.2 x) w) =
          (Z₁.coordChange p.1 r.1 x).prodMap (Z₂.coordChange p.2 r.2 x) w := by
      intro w
      have h₁ := Z₁.coordChange_comp p.1 q.1 r.1 x hpq w.1
      have h₂ := Z₂.coordChange_comp p.2 q.2 r.2 x hpq' w.2
      simp only [ContinuousLinearMap.coe_prodMap']
      exact Prod.ext h₁ h₂
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact congrArg e (hcomp (e.symm v))

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F₁ F₂ F : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The transport of a block-diagonal endomorphism along a splitting.**  This is the transition
function of `Work.Whitney.sumCore e Z₁ Z₂` at a point, and the object whose behaviour under
`Work.Thom.cxTrans` governs the compatibility of the direct sum with complexification. -/
noncomputable def transportEnd (e : (F₁ × F₂) ≃L[𝕜] F)
    (T₁ : F₁ →L[𝕜] F₁) (T₂ : F₂ →L[𝕜] F₂) : F →L[𝕜] F :=
  (e : (F₁ × F₂) →L[𝕜] F).comp ((T₁.prodMap T₂).comp (e.symm : F →L[𝕜] (F₁ × F₂)))

@[simp] theorem sumCore_coordChange_eq_transportEnd (e : (F₁ × F₂) ≃L[𝕜] F)
    (Z₁ : VectorBundleCore 𝕜 B F₁ ι₁) (Z₂ : VectorBundleCore 𝕜 B F₂ ι₂)
    (p q : ι₁ × ι₂) (x : B) :
    (sumCore e Z₁ Z₂).coordChange p q x
      = transportEnd e (Z₁.coordChange p.1 q.1 x) (Z₂.coordChange p.2 q.2 x) := rfl

@[simp] theorem sumCore_baseSet (e : (F₁ × F₂) ≃L[𝕜] F)
    (Z₁ : VectorBundleCore 𝕜 B F₁ ι₁) (Z₂ : VectorBundleCore 𝕜 B F₂ ι₂) (p : ι₁ × ι₂) :
    (sumCore e Z₁ Z₂).baseSet p = Z₁.baseSet p.1 ∩ Z₂.baseSet p.2 := rfl

@[simp] theorem sumCore_indexAt (e : (F₁ × F₂) ≃L[𝕜] F)
    (Z₁ : VectorBundleCore 𝕜 B F₁ ι₁) (Z₂ : VectorBundleCore 𝕜 B F₂ ι₂) (x : B) :
    (sumCore e Z₁ Z₂).indexAt x = (Z₁.indexAt x, Z₂.indexAt x) := rfl

@[simp] theorem sumCore_coordChange (e : (F₁ × F₂) ≃L[𝕜] F)
    (Z₁ : VectorBundleCore 𝕜 B F₁ ι₁) (Z₂ : VectorBundleCore 𝕜 B F₂ ι₂)
    (p q : ι₁ × ι₂) (x : B) :
    (sumCore e Z₁ Z₂).coordChange p q x =
      (e : (F₁ × F₂) →L[𝕜] F).comp
        (((Z₁.coordChange p.1 q.1 x).prodMap (Z₂.coordChange p.2 q.2 x)).comp
          ((e.symm : F →L[𝕜] (F₁ × F₂)))) := rfl

end SumCore

/-! ## The complex and real direct sums -/

/-- **The Whitney sum of two complex gluing-data bundles**, in the standard fibre
`EuclideanSpace ℂ (Fin (m₁ + m₂))` and over the product cover `ι₁ × ι₂`.  This is the operation the
Whitney formula `c(E ⊕ F) = c(E)c(F)` is about. -/
noncomputable def whitneySum {m₁ m₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m₁ + m₂))) (ι₁ × ι₂) :=
  sumCore (sumFibreC m₁ m₂) Z₁ Z₂

/-- **The Whitney sum of two real gluing-data bundles**, in the standard fibre
`EuclideanSpace ℝ (Fin (k₁ + k₂))` and over the product cover `ι₁ × ι₂`. -/
noncomputable def whitneySumR {k₁ k₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₁)) ι₁)
    (Z₂ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₂)) ι₂) :
    VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin (k₁ + k₂))) (ι₁ × ι₂) :=
  sumCore (sumFibreR k₁ k₂) Z₁ Z₂

@[simp] theorem whitneySum_baseSet {m₁ m₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (p : ι₁ × ι₂) :
    (whitneySum Z₁ Z₂).baseSet p = Z₁.baseSet p.1 ∩ Z₂.baseSet p.2 := rfl

@[simp] theorem whitneySum_indexAt {m₁ m₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (x : B) :
    (whitneySum Z₁ Z₂).indexAt x = (Z₁.indexAt x, Z₂.indexAt x) := rfl

/-- The transition functions of the complex Whitney sum: the block-diagonal transition functions,
conjugated by the splitting `Work.Whitney.sumFibreC`. -/
@[simp] theorem whitneySum_coordChange {m₁ m₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (p q : ι₁ × ι₂) (x : B) :
    (whitneySum Z₁ Z₂).coordChange p q x =
      (sumFibreC m₁ m₂ : (EuclideanSpace ℂ (Fin m₁) × EuclideanSpace ℂ (Fin m₂)) →L[ℂ]
          EuclideanSpace ℂ (Fin (m₁ + m₂))).comp
        (((Z₁.coordChange p.1 q.1 x).prodMap (Z₂.coordChange p.2 q.2 x)).comp
          ((sumFibreC m₁ m₂).symm : EuclideanSpace ℂ (Fin (m₁ + m₂)) →L[ℂ]
            (EuclideanSpace ℂ (Fin m₁) × EuclideanSpace ℂ (Fin m₂)))) := rfl

@[simp] theorem whitneySumR_baseSet {k₁ k₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₁)) ι₁)
    (Z₂ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₂)) ι₂) (p : ι₁ × ι₂) :
    (whitneySumR Z₁ Z₂).baseSet p = Z₁.baseSet p.1 ∩ Z₂.baseSet p.2 := rfl

@[simp] theorem whitneySumR_indexAt {k₁ k₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₁)) ι₁)
    (Z₂ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₂)) ι₂) (x : B) :
    (whitneySumR Z₁ Z₂).indexAt x = (Z₁.indexAt x, Z₂.indexAt x) := rfl

@[simp] theorem whitneySumR_coordChange {k₁ k₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₁)) ι₁)
    (Z₂ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₂)) ι₂)
    (p q : ι₁ × ι₂) (x : B) :
    (whitneySumR Z₁ Z₂).coordChange p q x =
      (sumFibreR k₁ k₂ : (EuclideanSpace ℝ (Fin k₁) × EuclideanSpace ℝ (Fin k₂)) →L[ℝ]
          EuclideanSpace ℝ (Fin (k₁ + k₂))).comp
        (((Z₁.coordChange p.1 q.1 x).prodMap (Z₂.coordChange p.2 q.2 x)).comp
          ((sumFibreR k₁ k₂).symm : EuclideanSpace ℝ (Fin (k₁ + k₂)) →L[ℝ]
            (EuclideanSpace ℝ (Fin k₁) × EuclideanSpace ℝ (Fin k₂)))) := rfl

/-! ## Functoriality -/

/-- **The direct sum commutes with the pullback** (definitionally). -/
theorem sumCore_bundleComap {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F₁ F₂ F : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι₁ ι₂ : Type*} {B' : Type} [TopologicalSpace B'] (e : (F₁ × F₂) ≃L[𝕜] F)
    (Z₁ : VectorBundleCore 𝕜 B F₁ ι₁) (Z₂ : VectorBundleCore 𝕜 B F₂ ι₂) (f : C(B', B)) :
    Work.Thom.bundleComap (sumCore e Z₁ Z₂) f
      = sumCore (B := B') e (Work.Thom.bundleComap Z₁ f) (Work.Thom.bundleComap Z₂ f) := by
  refine Work.Thom.bundleCore_ext (funext fun p => ?_) rfl (fun p q x => rfl)
  exact Set.preimage_inter

/-- **The complex Whitney sum commutes with the pullback.** -/
theorem whitneySum_bundleComap {m₁ m₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    {B' : Type} [TopologicalSpace B'] (f : C(B', B)) :
    Work.Thom.bundleComap (whitneySum Z₁ Z₂) f
      = whitneySum (Work.Thom.bundleComap Z₁ f) (Work.Thom.bundleComap Z₂ f) :=
  sumCore_bundleComap (sumFibreC m₁ m₂) Z₁ Z₂ f

/-- **The real Whitney sum commutes with the pullback.** -/
theorem whitneySumR_bundleComap {k₁ k₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₁)) ι₁)
    (Z₂ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₂)) ι₂)
    {B' : Type} [TopologicalSpace B'] (f : C(B', B)) :
    Work.Thom.bundleComap (whitneySumR Z₁ Z₂) f
      = whitneySumR (Work.Thom.bundleComap Z₁ f) (Work.Thom.bundleComap Z₂ f) :=
  sumCore_bundleComap (sumFibreR k₁ k₂) Z₁ Z₂ f

/-! ## The trivial bundle is a unit -/

/-- **The transition functions of the sum with a trivial bundle**: the second factor is constant. -/
theorem sumCore_trivial_coordChange {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F₁ F₂ F : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι₁ : Type*} {ι₀ : Type*} [Inhabited ι₀] (e : (F₁ × F₂) ≃L[𝕜] F)
    (Z : VectorBundleCore 𝕜 B F₁ ι₁) (p q : ι₁ × ι₀) (x : B) :
    (sumCore e Z (trivialVectorBundleCore 𝕜 B F₂ ι₀)).coordChange p q x =
      (e : (F₁ × F₂) →L[𝕜] F).comp
        (((Z.coordChange p.1 q.1 x).prodMap (ContinuousLinearMap.id 𝕜 F₂)).comp
          ((e.symm : F →L[𝕜] (F₁ × F₂)))) := by
  rw [sumCore_coordChange]
  rfl

end

end Work.Whitney
