import Mathlib
import Submission.Work.Agree.whitneySumRComm
import Submission.Work.Agree.whitneySumRCongr
import Submission.Work.Agree.whitneySumR_sum_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Associativity and rotation for the real Whitney sum

The real Whitney sum `Work.Whitney.whitneySumR` is glued along the explicit splitting
`Work.Whitney.sumFibreR : ℝ^k × ℝ^l ≃L ℝ^{k+l}` of the fibre, which makes its transition functions
conjugated block-diagonals rather than honest block-diagonals.  This module proves that the operation
is associative (`Work.Agree.whitneySumRAssoc`) and that the last two summands may be interchanged
(`Work.Agree.whitneySumRRotate`).

## The strategy

Rather than conjugating by a hand-built associator of the `sumFibreR` splitings, we pass through the
*honest* product-fibre sum `Work.TangentClasses.RealBundle.sum` (`Z.sum W` has fibre `F₁ × F₂` and
transition functions the honest block-diagonal `Z.coordChange ∘prod W.coordChange`).  There

* associativity is the constant gauge `ContinuousLinearEquiv.prodAssoc.symm`, whose conjugation
  identity is the elementary product identity `Work.Agree.prodMap_prodAssoc`;
* commutativity is the constant gauge `ContinuousLinearEquiv.prodComm`, whose conjugation identity is
  `Work.Whitney.prodMap_prodComm_swap`;
* congruence in both arguments is `Work.Agree.nonempty_bundleIso_sumCore_congr` transported across
  the identification `Work.Agree.sumCore_refl_eq_sum` of the identity splitting with `.sum`.

The conversions `whitneySumR Z W ≅ Z.sum W` are `Work.Agree.whitneySumR_sum_iso`, and the
associativity of `whitneySumR` is then a five-step composite of those.
-/

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## The product associativity identity -/

/-- **The product of two linear maps commutes with the associator**: `(T₁ × (T₂ × T₃))` conjugated
by `prodAssoc.symm` is `((T₁ × T₂) × T₃)`. -/
theorem prodMap_prodAssoc {𝕜 : Type*} [Semiring 𝕜] {E F G : Type*}
    [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
    [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F]
    [TopologicalSpace G] [AddCommMonoid G] [Module 𝕜 G]
    (T₁ : E →L[𝕜] E) (T₂ : F →L[𝕜] F) (T₃ : G →L[𝕜] G) :
    (((ContinuousLinearEquiv.prodAssoc 𝕜 E F G).symm : (E × (F × G)) →L[𝕜] ((E × F) × G))).comp
        (T₁.prodMap (T₂.prodMap T₃))
      = ((T₁.prodMap T₂).prodMap T₃).comp
        ((ContinuousLinearEquiv.prodAssoc 𝕜 E F G).symm : (E × (F × G)) →L[𝕜] ((E × F) × G)) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x₁, x₂, x₃⟩
  simp [ContinuousLinearMap.coe_prodMap']

/-! ## The identity splitting produces `.sum` -/

/-- **The sum glued along the identity splitting is the honest product sum.** -/
theorem sumCore_refl_eq_sum {B : Type} [TopologicalSpace B]
    {F₁ F₂ : Type} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℝ B F₁ ι₁) (Z₂ : VectorBundleCore ℝ B F₂ ι₂) :
    Work.Whitney.sumCore (ContinuousLinearEquiv.refl ℝ (F₁ × F₂)) Z₁ Z₂
      = Work.TangentClasses.RealBundle.sum Z₁ Z₂ := by
  refine Work.Thom.bundleCore_ext ?_ ?_ ?_
  · rfl
  · rfl
  · intro i j x
    apply ContinuousLinearMap.ext
    intro v
    simp [Work.Whitney.transportEnd, ContinuousLinearMap.coe_prodMap']

/-! ## Congruence of `.sum` -/

/-- **Congruence of the honest product sum in both arguments**: isomorphic summands (with possibly
different model fibres) have isomorphic sums. -/
theorem sum_congr {B : Type} [TopologicalSpace B]
    {F₁ F₁' F₂ F₂' : Type}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₁'] [NormedSpace ℝ F₁'] [FiniteDimensional ℝ F₁']
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    [NormedAddCommGroup F₂'] [NormedSpace ℝ F₂'] [FiniteDimensional ℝ F₂']
    {ι₁ ι₁' ι₂ ι₂' : Type}
    (Z : VectorBundleCore ℝ B F₁ ι₁) (Z' : VectorBundleCore ℝ B F₁' ι₁')
    (W : VectorBundleCore ℝ B F₂ ι₂) (W' : VectorBundleCore ℝ B F₂' ι₂')
    (e : Work.Thom.BundleIso Z Z') (e' : Work.Thom.BundleIso W W') :
    Nonempty (Work.Thom.BundleIso (RealBundle.sum Z W) (RealBundle.sum Z' W')) := by
  have h1 := sumCore_refl_eq_sum Z W
  have h2 := sumCore_refl_eq_sum Z' W'
  obtain ⟨φ⟩ := Work.Agree.nonempty_bundleIso_sumCore_congr
    (ContinuousLinearEquiv.refl ℝ (F₁ × F₂)) (ContinuousLinearEquiv.refl ℝ (F₁' × F₂'))
    Z Z' W W' e e'
  exact ⟨h1 ▸ h2 ▸ φ⟩

/-- Congruence of the honest product sum, in the `Nonempty` form. -/
theorem nonempty_sum_congr {B : Type} [TopologicalSpace B]
    {F₁ F₁' F₂ F₂' : Type}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₁'] [NormedSpace ℝ F₁'] [FiniteDimensional ℝ F₁']
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    [NormedAddCommGroup F₂'] [NormedSpace ℝ F₂'] [FiniteDimensional ℝ F₂']
    {ι₁ ι₁' ι₂ ι₂' : Type}
    (Z : VectorBundleCore ℝ B F₁ ι₁) (Z' : VectorBundleCore ℝ B F₁' ι₁')
    (W : VectorBundleCore ℝ B F₂ ι₂) (W' : VectorBundleCore ℝ B F₂' ι₂')
    (hZ : Nonempty (Work.Thom.BundleIso Z Z'))
    (hW : Nonempty (Work.Thom.BundleIso W W')) :
    Nonempty (Work.Thom.BundleIso (RealBundle.sum Z W) (RealBundle.sum Z' W')) := by
  obtain ⟨e⟩ := hZ
  obtain ⟨e'⟩ := hW
  exact sum_congr Z Z' W W' e e'

/-! ## Associativity and commutativity of `.sum` -/

/-- **The honest product sum is associative.** -/
theorem sum_assoc {B : Type} [TopologicalSpace B]
    {F₁ F₂ F₃ : Type} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    {ι₁ ι₂ ι₃ : Type}
    (Z : VectorBundleCore ℝ B F₁ ι₁) (W : VectorBundleCore ℝ B F₂ ι₂)
    (V : VectorBundleCore ℝ B F₃ ι₃) :
    Nonempty (Work.Thom.BundleIso (RealBundle.sum Z (RealBundle.sum W V))
      (RealBundle.sum (RealBundle.sum Z W) V)) := by
  refine Work.Whitney.nonempty_bundleIso_of_gauge_fibre
    (RealBundle.sum Z (RealBundle.sum W V)) (RealBundle.sum (RealBundle.sum Z W) V)
    ((ContinuousLinearEquiv.prodAssoc ℝ F₁ F₂ F₃).symm) (Equiv.prodAssoc ι₁ ι₂ ι₃).symm ?_ ?_ ?_
  · intro i
    obtain ⟨i₁, i₂, i₃⟩ := i
    simp only [RealBundle.sum_baseSet, Equiv.prodAssoc_symm_apply]
    exact Set.inter_assoc _ _ _
  · intro b
    simp only [RealBundle.sum_indexAt, Equiv.prodAssoc_symm_apply]
  · intro i b
    obtain ⟨i₁, i₂, i₃⟩ := i
    apply ContinuousLinearMap.ext
    rintro ⟨x₁, x₂, x₃⟩
    simp only [RealBundle.sum_indexAt, RealBundle.sum_coordChange, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_prodMap']
    exact congrArg (fun f => f (x₁, x₂, x₃)) (prodMap_prodAssoc
      (Z.coordChange (Z.indexAt b) i₁ b) (W.coordChange (W.indexAt b) i₂ b)
      (V.coordChange (V.indexAt b) i₃ b)).symm

/-- **The honest product sum is commutative.** -/
theorem sum_comm {B : Type} [TopologicalSpace B]
    {F₁ F₂ : Type} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {ι₁ ι₂ : Type}
    (Z : VectorBundleCore ℝ B F₁ ι₁) (W : VectorBundleCore ℝ B F₂ ι₂) :
    Nonempty (Work.Thom.BundleIso (RealBundle.sum Z W) (RealBundle.sum W Z)) := by
  refine Work.Whitney.nonempty_bundleIso_of_gauge_fibre
    (RealBundle.sum Z W) (RealBundle.sum W Z)
    (ContinuousLinearEquiv.prodComm ℝ F₁ F₂) (Equiv.prodComm ι₁ ι₂) ?_ ?_ ?_
  · intro i
    obtain ⟨i₁, i₂⟩ := i
    simp only [RealBundle.sum_baseSet, Equiv.prodComm_apply, Prod.swap_prod_mk]
    exact Set.inter_comm _ _
  · intro b
    simp only [RealBundle.sum_indexAt, Equiv.prodComm_apply, Prod.swap_prod_mk]
  · intro i b
    obtain ⟨i₁, i₂⟩ := i
    apply ContinuousLinearMap.ext
    rintro ⟨x₁, x₂⟩
    simp only [RealBundle.sum_indexAt, RealBundle.sum_coordChange, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_prodMap']
    exact congrArg (fun f => f (x₁, x₂))
      (Work.Whitney.prodMap_prodComm_swap (Z.coordChange (Z.indexAt b) i₁ b)
        (W.coordChange (W.indexAt b) i₂ b))

/-! ## The targets -/

/-- **The real Whitney sum is associative.**  `Z ⊕ (W ⊕ V) ≅ (Z ⊕ W) ⊕ V`: the model fibres
`ℝ^{k+(l+m)}` and `ℝ^{(k+l)+m}` and the covers `ι₁ × (ι₂ × ι₃)`, `(ι₁ × ι₂) × ι₃` differ, but the
bundles are canonically isomorphic. -/
theorem whitneySumRAssoc {B : Type} [TopologicalSpace B] {k l m : ℕ} {ι₁ ι₂ ι₃ : Type}
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι₁)
    (W : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin l)) ι₂)
    (V : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin m)) ι₃) :
    Nonempty (Work.Thom.BundleIso
      (Work.Whitney.whitneySumR Z (Work.Whitney.whitneySumR W V))
      (Work.Whitney.whitneySumR (Work.Whitney.whitneySumR Z W) V)) := by
  obtain ⟨e1⟩ := whitneySumR_sum_iso Z (Work.Whitney.whitneySumR W V)
  obtain ⟨e2⟩ := whitneySumR_sum_iso W V
  obtain ⟨e3⟩ := sum_assoc Z W V
  obtain ⟨e4⟩ := whitneySumR_sum_iso Z W
  obtain ⟨e5⟩ := whitneySumR_sum_iso (Work.Whitney.whitneySumR Z W) V
  obtain ⟨e6⟩ := sum_congr Z Z (Work.Whitney.whitneySumR W V) (RealBundle.sum W V)
    (Work.Thom.BundleIso.refl Z) e2
  obtain ⟨e7⟩ := sum_congr (RealBundle.sum Z W) (Work.Whitney.whitneySumR Z W) V V
    e4.symm (Work.Thom.BundleIso.refl V)
  exact ⟨e1.trans (e6.trans (e3.trans (e7.trans e5.symm)))⟩

/-- **The last two summands of a triple Whitney sum may be interchanged.** -/
theorem whitneySumRRotate {B : Type} [TopologicalSpace B] {k l m : ℕ} {ι₁ ι₂ ι₃ : Type}
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι₁)
    (W : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin l)) ι₂)
    (V : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin m)) ι₃) :
    Nonempty (Work.Thom.BundleIso
      (Work.Whitney.whitneySumR (Work.Whitney.whitneySumR Z W) V)
      (Work.Whitney.whitneySumR (Work.Whitney.whitneySumR Z V) W)) := by
  obtain ⟨a1⟩ := whitneySumRAssoc Z W V
  obtain ⟨a2⟩ := whitneySumRCongr Z Z (Work.Whitney.whitneySumR W V)
    (Work.Whitney.whitneySumR V W) ⟨Work.Thom.BundleIso.refl Z⟩ (whitneySumRComm W V)
  obtain ⟨a3⟩ := whitneySumRAssoc Z V W
  exact ⟨a1.symm.trans (a2.trans a3)⟩

end

end Work.Agree
