import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Agree.whitneySumRCongr
import Submission.Work.Agree.whitneySumRAssoc
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm

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
# Functoriality and associativity of the complex direct sum

This module provides the two geometric inputs of the induction that proves the Whitney sum formula
for the Chern classes of `Submission/Work/LerayHirsch/`:

* `Work.LerayHirsch.nonempty_bundleIso_whitneySum_first` — **functoriality in the first argument**:
  `Z₁ ≅ Z₁'` gives `Z₁ ⊕ Z₂ ≅ Z₁' ⊕ Z₂`.  This is a one-line consequence of the general congruence
  `Work.Agree.nonempty_bundleIso_sumCore_congr` (with the second isomorphism the identity);
* `Work.LerayHirsch.nonempty_bundleIso_whitneySum_assoc` — **associativity**:
  `(Z₁ ⊕ Z₂) ⊕ Z₃ ≅ Z₁ ⊕ (Z₂ ⊕ Z₃)`.

For the associativity we follow the strategy of the real counterpart
`Work.Agree.whitneySumRAssoc`: rather than juggling the `sumFibreC`-conjugated block-diagonals of
the `whitneySum` presentation directly, pass through the *honest* product-fibre sum
`Work.Thom.bundleSum` (fibre `F₁ × F₂`, transitions the honest block-diagonal `T₁ × T₂`), where

* `whitneySum Z W ≅ bundleSum Z W` is the gauge `sumFibreC` (`nonempty_bundleIso_whitneySum_bundleSum`),
* `bundleSum Z₁ (bundleSum Z₂ Z₃) ≅ bundleSum (bundleSum Z₁ Z₂) Z₃` is the *constant* gauge
  `ContinuousLinearEquiv.prodAssoc.symm`, whose conjugation identity is the elementary product
  identity `Work.Agree.prodMap_prodAssoc`,
* `bundleSum` is congruent in both arguments (`nonempty_bundleIso_bundleSum_congr`).

Associativity of `whitneySum` is then the five-step composite.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## Functoriality of `whitneySum` -/

/-- **Functoriality of the complex direct sum in its first argument**: an isomorphism of bundles
`Z₁ ≅ Z₁'` (with possibly different model fibres `Fin m₁`, `Fin m₁'`) induces an isomorphism
`Z₁ ⊕ Z₂ ≅ Z₁' ⊕ Z₂`. -/
theorem nonempty_bundleIso_whitneySum_first {m₁ m₁' m₂ : ℕ} {ι₁ ι₁' ι₂ : Type}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₁' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁')) ι₁')
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (e : BundleIso Z₁ Z₁') :
    Nonempty (BundleIso (Work.Whitney.whitneySum Z₁ Z₂)
      (Work.Whitney.whitneySum Z₁' Z₂)) := by
  obtain ⟨φ⟩ := Work.Agree.nonempty_bundleIso_sumCore_congr (𝕜 := ℂ)
    (Work.Whitney.sumFibreC m₁ m₂) (Work.Whitney.sumFibreC m₁' m₂) Z₁ Z₁' Z₂ Z₂ e (BundleIso.refl Z₂)
  exact ⟨φ⟩

/-! ## The honest product sum -/

/-- The sum glued along the *identity* splitting is the honest product sum `Work.Thom.bundleSum`. -/
theorem sumCore_refl_eq_bundleSum {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℂ B F₁ ι₁) (Z₂ : VectorBundleCore ℂ B F₂ ι₂) :
    Work.Whitney.sumCore (ContinuousLinearEquiv.refl ℂ (F₁ × F₂)) Z₁ Z₂
      = Work.Thom.bundleSum Z₁ Z₂ := by
  refine Work.Thom.bundleCore_ext ?_ ?_ ?_
  · rfl
  · rfl
  · intro i j x
    apply ContinuousLinearMap.ext
    intro v
    simp [Work.Whitney.transportEnd, ContinuousLinearMap.coe_prodMap']

/-- **The complex `whitneySum` is isomorphic to the honest product sum.** -/
theorem nonempty_bundleIso_whitneySum_bundleSum {m₁ m₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Nonempty (BundleIso (Work.Whitney.whitneySum Z₁ Z₂) (Work.Thom.bundleSum Z₁ Z₂)) := by
  refine Work.Whitney.nonempty_bundleIso_of_gauge_fibre (Work.Whitney.whitneySum Z₁ Z₂)
    (Work.Thom.bundleSum Z₁ Z₂) ((Work.Whitney.sumFibreC m₁ m₂).symm) (Equiv.refl (ι₁ × ι₂))
    ?_ ?_ ?_
  · intro i
    simp only [Work.Whitney.whitneySum_baseSet, Work.Thom.bundleSum_baseSet, Equiv.refl_apply]
  · intro b
    simp only [Work.Whitney.whitneySum_indexAt, Work.Thom.bundleSum_indexAt, Equiv.refl_apply]
  · intro i b
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, Work.Whitney.whitneySum_coordChange,
      Work.Thom.bundleSum_coordChange, Work.Whitney.whitneySum_indexAt,
      Work.Thom.bundleSum_indexAt, Equiv.refl_apply, ContinuousLinearMap.coe_prodMap',
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- **Congruence of the honest product sum** in both arguments. -/
theorem nonempty_bundleIso_bundleSum_congr {F₁ F₁' F₂ F₂' : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [FiniteDimensional ℂ F₁]
    [NormedAddCommGroup F₁'] [NormedSpace ℂ F₁'] [FiniteDimensional ℂ F₁']
    [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [FiniteDimensional ℂ F₂]
    [NormedAddCommGroup F₂'] [NormedSpace ℂ F₂'] [FiniteDimensional ℂ F₂']
    {ι₁ ι₁' ι₂ ι₂' : Type}
    (Z : VectorBundleCore ℂ B F₁ ι₁) (Z' : VectorBundleCore ℂ B F₁' ι₁')
    (W : VectorBundleCore ℂ B F₂ ι₂) (W' : VectorBundleCore ℂ B F₂' ι₂')
    (e : BundleIso Z Z') (e' : BundleIso W W') :
    Nonempty (BundleIso (Work.Thom.bundleSum Z W) (Work.Thom.bundleSum Z' W')) := by
  have h1 := sumCore_refl_eq_bundleSum Z W
  have h2 := sumCore_refl_eq_bundleSum Z' W'
  obtain ⟨φ⟩ := Work.Agree.nonempty_bundleIso_sumCore_congr (𝕜 := ℂ)
    (ContinuousLinearEquiv.refl ℂ (F₁ × F₂)) (ContinuousLinearEquiv.refl ℂ (F₁' × F₂'))
    Z Z' W W' e e'
  exact ⟨h1 ▸ h2 ▸ φ⟩

/-- **Associativity of the honest product sum.** -/
theorem nonempty_bundleIso_bundleSum_assoc {F₁ F₂ F₃ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    [NormedAddCommGroup F₃] [NormedSpace ℂ F₃] {ι₁ ι₂ ι₃ : Type}
    (Z₁ : VectorBundleCore ℂ B F₁ ι₁) (Z₂ : VectorBundleCore ℂ B F₂ ι₂)
    (Z₃ : VectorBundleCore ℂ B F₃ ι₃) :
    Nonempty (BundleIso (Work.Thom.bundleSum Z₁ (Work.Thom.bundleSum Z₂ Z₃))
      (Work.Thom.bundleSum (Work.Thom.bundleSum Z₁ Z₂) Z₃)) := by
  refine Work.Whitney.nonempty_bundleIso_of_gauge_fibre
    (Work.Thom.bundleSum Z₁ (Work.Thom.bundleSum Z₂ Z₃))
    (Work.Thom.bundleSum (Work.Thom.bundleSum Z₁ Z₂) Z₃)
    ((ContinuousLinearEquiv.prodAssoc ℂ F₁ F₂ F₃).symm) (Equiv.prodAssoc ι₁ ι₂ ι₃).symm ?_ ?_ ?_
  · intro i
    obtain ⟨i₁, i₂, i₃⟩ := i
    simp only [Work.Thom.bundleSum_baseSet, Equiv.prodAssoc_symm_apply]
    exact Set.inter_assoc _ _ _
  · intro b
    simp only [Work.Thom.bundleSum_indexAt, Equiv.prodAssoc_symm_apply]
  · intro i b
    obtain ⟨i₁, i₂, i₃⟩ := i
    apply ContinuousLinearMap.ext
    rintro ⟨x₁, x₂, x₃⟩
    simp only [Work.Thom.bundleSum_indexAt, Work.Thom.bundleSum_coordChange,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap']
    exact congrArg (fun f => f (x₁, x₂, x₃)) (Work.Agree.prodMap_prodAssoc
      (Z₁.coordChange (Z₁.indexAt b) i₁ b) (Z₂.coordChange (Z₂.indexAt b) i₂ b)
      (Z₃.coordChange (Z₃.indexAt b) i₃ b)).symm

/-! ## Associativity of `whitneySum` -/

/-- **Associativity of the complex direct sum**: `(Z₁ ⊕ Z₂) ⊕ Z₃ ≅ Z₁ ⊕ (Z₂ ⊕ Z₃)`. -/
theorem nonempty_bundleIso_whitneySum_assoc {m₁ m₂ m₃ : ℕ} {ι₁ ι₂ ι₃ : Type}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (Z₃ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₃)) ι₃) :
    Nonempty (BundleIso (Work.Whitney.whitneySum (Work.Whitney.whitneySum Z₁ Z₂) Z₃)
      (Work.Whitney.whitneySum Z₁ (Work.Whitney.whitneySum Z₂ Z₃))) := by
  obtain ⟨e1⟩ := nonempty_bundleIso_whitneySum_bundleSum (Work.Whitney.whitneySum Z₁ Z₂) Z₃
  obtain ⟨e2⟩ := nonempty_bundleIso_whitneySum_bundleSum Z₂ Z₃
  obtain ⟨e3⟩ := nonempty_bundleIso_bundleSum_assoc Z₁ Z₂ Z₃
  obtain ⟨e4⟩ := nonempty_bundleIso_whitneySum_bundleSum Z₁ Z₂
  obtain ⟨e5⟩ := nonempty_bundleIso_whitneySum_bundleSum Z₁ (Work.Whitney.whitneySum Z₂ Z₃)
  obtain ⟨e6⟩ := nonempty_bundleIso_bundleSum_congr Z₁ Z₁ (Work.Whitney.whitneySum Z₂ Z₃)
    (Work.Thom.bundleSum Z₂ Z₃) (BundleIso.refl Z₁) e2
  obtain ⟨e7⟩ := nonempty_bundleIso_bundleSum_congr (Work.Thom.bundleSum Z₁ Z₂)
    (Work.Whitney.whitneySum Z₁ Z₂) Z₃ Z₃ e4.symm (BundleIso.refl Z₃)
  exact ⟨e1.trans (e7.symm.trans (e3.symm.trans (e6.symm.trans e5.symm)))⟩

end

end Work.LerayHirsch
