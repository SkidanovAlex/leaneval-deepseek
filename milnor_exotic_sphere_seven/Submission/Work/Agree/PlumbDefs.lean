import Mathlib
import Submission.Work.Thom.Iso
import Submission.Work.Thom.coreMorphism

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Reindexing gluing data along a covering family, and the self-isomorphism

`Work.Agree.reindexCore Z σ hσ` presents the gluing datum `Z` over the (reindexed) cover `ι'`, using
the covering family `σ : ι' → ι`.  If `σ` covers the base then `reindexCore Z σ hσ` is isomorphic to
`Z` itself (`Work.Agree.nonempty_bundleIso_reindexCore_self`): reindexing is only a change of the
presentation.

This is the `ι'' = ι` case of the comparison of two reindexings of the same core.  It is what allows
one to drop the finite-chart-cover reindexing `… .reindex (chartCover …)` from the four-step
presentation of the complexified tangent bundle of a compact manifold
(`Work.Thom.complexifiedTangentBundleFinite`).
-/

namespace Work.Agree

open Work.TangentClasses

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Reindexing a gluing datum along a covering family.**  Same cover pieces, but indexed by `ι'`;
the rest of the structure is pulled back along `σ`. -/
def reindexCore {ι : Type*} (Z : VectorBundleCore 𝕜 B F ι) {ι' : Type*} (σ : ι' → ι)
    (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) : VectorBundleCore 𝕜 B F ι' where
  baseSet i := Z.baseSet (σ i)
  isOpen_baseSet i := Z.isOpen_baseSet (σ i)
  indexAt x := Classical.choose (hσ x)
  mem_baseSet_at x := Classical.choose_spec (hσ x)
  coordChange i j x := Z.coordChange (σ i) (σ j) x
  coordChange_self i x hx v := Z.coordChange_self (σ i) x hx v
  continuousOn_coordChange i j := Z.continuousOn_coordChange (σ i) (σ j)
  coordChange_comp i j l x hx v := Z.coordChange_comp (σ i) (σ j) (σ l) x hx v

@[simp] theorem reindexCore_baseSet {ι : Type*} (Z : VectorBundleCore 𝕜 B F ι) {ι' : Type*}
    (σ : ι' → ι) (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) (i : ι') :
    (reindexCore Z σ hσ).baseSet i = Z.baseSet (σ i) := rfl

@[simp] theorem reindexCore_coordChange {ι : Type*} (Z : VectorBundleCore 𝕜 B F ι) {ι' : Type*}
    (σ : ι' → ι) (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) (i j : ι') (x : B) :
    (reindexCore Z σ hσ).coordChange i j x = Z.coordChange (σ i) (σ j) x := rfl

/-- **A reindexing along a covering family is isomorphic to the original bundle.**  The isomorphism
is the coordinate-change gauge `Z.coordChange (σ (indexAt b)) (Z.indexAt b) b`. -/
theorem nonempty_bundleIso_reindexCore_self {𝕜 : Type} [NontriviallyNormedField 𝕜]
    {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type} (Z : VectorBundleCore 𝕜 B F ι)
    {ι' : Type} (σ : ι' → ι) (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) :
    Nonempty (Work.Thom.BundleIso (reindexCore Z σ hσ) Z) := by
  set T : B → F →L[𝕜] F :=
    fun b => Z.coordChange (σ ((reindexCore Z σ hσ).indexAt b)) (Z.indexAt b) b with hT
  refine ⟨{ hom := fun b => (T b).toLinearMap
            inv := fun b =>
              (Z.coordChange (Z.indexAt b) (σ ((reindexCore Z σ hσ).indexAt b)) b).toLinearMap
            left_inv := ?_
            right_inv := ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · intro b x
    show Z.coordChange (Z.indexAt b) (σ ((reindexCore Z σ hσ).indexAt b)) b
        (Z.coordChange (σ ((reindexCore Z σ hσ).indexAt b)) (Z.indexAt b) b x) = x
    have h1 : b ∈ Z.baseSet (σ ((reindexCore Z σ hσ).indexAt b)) :=
      (reindexCore Z σ hσ).mem_baseSet_at b
    have h2 : b ∈ Z.baseSet (Z.indexAt b) := Z.mem_baseSet_at b
    rw [Z.coordChange_comp (σ ((reindexCore Z σ hσ).indexAt b)) (Z.indexAt b)
        (σ ((reindexCore Z σ hσ).indexAt b)) b ⟨⟨h1, h2⟩, h1⟩ x,
      Z.coordChange_self (σ ((reindexCore Z σ hσ).indexAt b)) b h1 x]
  · intro b y
    show Z.coordChange (σ ((reindexCore Z σ hσ).indexAt b)) (Z.indexAt b) b
        (Z.coordChange (Z.indexAt b) (σ ((reindexCore Z σ hσ).indexAt b)) b y) = y
    have h1 : b ∈ Z.baseSet (σ ((reindexCore Z σ hσ).indexAt b)) :=
      (reindexCore Z σ hσ).mem_baseSet_at b
    have h2 : b ∈ Z.baseSet (Z.indexAt b) := Z.mem_baseSet_at b
    rw [Z.coordChange_comp (Z.indexAt b) (σ ((reindexCore Z σ hσ).indexAt b))
        (Z.indexAt b) b ⟨⟨h2, h1⟩, h2⟩ y,
      Z.coordChange_self (Z.indexAt b) b h2 y]
  · refine Work.Thom.continuous_totalSpaceMap_clm (reindexCore Z σ hσ) Z
      (ContinuousMap.id B) T ?_
    intro i₁ i₂
    refine (Z.continuousOn_coordChange (σ i₁) i₂).congr (fun b hb => ?_)
    have hb1 : b ∈ Z.baseSet (σ i₁) := hb.1
    have hb2 : b ∈ Z.baseSet i₂ := hb.2
    have h3 : b ∈ Z.baseSet (σ ((reindexCore Z σ hσ).indexAt b)) :=
      (reindexCore Z σ hσ).mem_baseSet_at b
    have h4 : b ∈ Z.baseSet (Z.indexAt b) := Z.mem_baseSet_at b
    show ((Z.coordChange (Z.indexAt b) i₂ b).comp
        ((T b).comp ((reindexCore Z σ hσ).coordChange i₁ ((reindexCore Z σ hσ).indexAt b) b)))
        = Z.coordChange (σ i₁) i₂ b
    simp only [hT, reindexCore_coordChange]
    apply ContinuousLinearMap.ext
    intro x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      Z.coordChange_comp (σ i₁) (σ ((reindexCore Z σ hσ).indexAt b)) (Z.indexAt b) b
        ⟨⟨hb1, h3⟩, h4⟩ x,
      Z.coordChange_comp (σ i₁) (Z.indexAt b) i₂ b ⟨⟨hb1, h4⟩, hb2⟩ x]
  · refine Work.Thom.continuous_totalSpaceMap_clm Z (reindexCore Z σ hσ)
      (ContinuousMap.id B) (fun b =>
        Z.coordChange (Z.indexAt b) (σ ((reindexCore Z σ hσ).indexAt b)) b) ?_
    intro i₁ i₂
    refine (Z.continuousOn_coordChange i₁ (σ i₂)).congr (fun b hb => ?_)
    have hb1 : b ∈ Z.baseSet i₁ := hb.1
    have hb2 : b ∈ Z.baseSet (σ i₂) := hb.2
    have h3 : b ∈ Z.baseSet (σ ((reindexCore Z σ hσ).indexAt b)) :=
      (reindexCore Z σ hσ).mem_baseSet_at b
    have h4 : b ∈ Z.baseSet (Z.indexAt b) := Z.mem_baseSet_at b
    show (((reindexCore Z σ hσ).coordChange ((reindexCore Z σ hσ).indexAt b) i₂ b).comp
        ((Z.coordChange (Z.indexAt b) (σ ((reindexCore Z σ hσ).indexAt b)) b).comp
          (Z.coordChange i₁ (Z.indexAt b) b))) = Z.coordChange i₁ (σ i₂) b
    simp only [reindexCore_coordChange]
    apply ContinuousLinearMap.ext
    intro x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      Z.coordChange_comp i₁ (Z.indexAt b) (σ ((reindexCore Z σ hσ).indexAt b)) b
        ⟨⟨hb1, h4⟩, h3⟩ x,
      Z.coordChange_comp i₁ (σ ((reindexCore Z σ hσ).indexAt b)) (σ i₂) b
        ⟨⟨hb1, h3⟩, hb2⟩ x]

end

end Work.Agree
