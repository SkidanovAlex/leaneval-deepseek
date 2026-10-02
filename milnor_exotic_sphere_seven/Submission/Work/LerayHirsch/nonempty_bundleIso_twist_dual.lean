import Mathlib
import Submission.Work.LerayHirsch.Twist
import Submission.Work.Gen.DualLineCore
import Submission.Work.Gen.EulerToolkit
import Submission.Work.Gen.chernClass_tensorLine_of_nowhereZeroSection

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Untwisting by a line bundle: `L ⊗ (L* ⊗ E) ≅ E`

For a complex **line** bundle `L` (`Work.LerayHirsch.twistCore` is the tensor product with an
arbitrary complex bundle, `Work.Gen.dualLineCore L = L*` the dual line bundle), the double twist
`L ⊗ (L* ⊗ E)` is isomorphic to `E`.

The isomorphism is the identity on fibres: on the cover of `L ⊗ (L* ⊗ E)` whose charts are
`p = (i, (i', e))` the inverse factor `scl (L.c_{i' i})` cancels the factor `scl (L.c_{i i'})`, and
the compatibility conditions reduce to the cocycle identity of the transitions of `L` (via
`Work.Gen.scl_cc_comp`) together with the cocycle identity of those of `E`.  Everything is packaged
by `Work.Thom.nonempty_bundleIso_of_gauge`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {ιL ιE : Type} {n : ℕ}

/-! ## The double twist `L ⊗ (L* ⊗ E)` -/

/-- **The base sets of the double twist** `L ⊗ (L* ⊗ E)`, in the order the computations use. -/
theorem twistCore_dual_twist_baseSet
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE)
    (p : ιL × (ιL × ιE)) :
    (twistCore L (twistCore (Work.Gen.dualLineCore L) E)).baseSet p
      = L.baseSet p.1 ∩ (L.baseSet p.2.1 ∩ E.baseSet p.2.2) := by
  rw [twistCore_baseSet, twistCore_baseSet, Work.Gen.dualLineCore_baseSet]

/-- **The transition functions of the double twist** `L ⊗ (L* ⊗ E)`: the two line-bundle factors
are the transition of `L` from `p.1` to `q.1` and the transition of `L*` from `p.2.1` to `q.2.1`,
i.e. the transition of `L` from `q.2.1` to `p.2.1`. -/
theorem twistCore_dual_twist_coordChange
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE)
    (p q : ιL × (ιL × ιE)) (x : B) :
    (twistCore L (twistCore (Work.Gen.dualLineCore L) E)).coordChange p q x
      = Work.Gen.scl (L.coordChange p.1 q.1 x) •
        (Work.Gen.scl (L.coordChange q.2.1 p.2.1 x) • E.coordChange p.2.2 q.2.2 x) := by
  rw [twistCore_coordChange, twistCore_coordChange, Work.Gen.dualLineCore_coordChange]

/-! ## The scalar identities coming from the cocycle of `L` -/

/-- **Cancellation of the two line-bundle factors in the source-chart compatibility**: the product
of the scalars of `c_{i₁ i₂}`, `c_{j₁ i₁}`, `c_{i₂ j₂}` is the scalar of `c_{j₁ j₂}`, by the
cocycle identity for `L`, first at `(j₁, i₁, i₂)` and then at `(j₁, i₂, j₂)`. -/
theorem scl_twist_cancel_source (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (i₁ i₂ j₁ j₂ : ιL) (b : B)
    (hi₁ : b ∈ L.baseSet i₁) (hi₂ : b ∈ L.baseSet i₂)
    (hj₁ : b ∈ L.baseSet j₁) (hj₂ : b ∈ L.baseSet j₂) :
    Work.Gen.scl (L.coordChange i₁ i₂ b) * Work.Gen.scl (L.coordChange j₁ i₁ b) *
      Work.Gen.scl (L.coordChange i₂ j₂ b) = Work.Gen.scl (L.coordChange j₁ j₂ b) := by
  have h1 := Work.Gen.scl_cc_comp L j₁ i₁ i₂ b ⟨⟨hj₁, hi₁⟩, hi₂⟩
  have h2 := Work.Gen.scl_cc_comp L j₁ i₂ j₂ b ⟨⟨hj₁, hi₂⟩, hj₂⟩
  rw [h2, h1]
  ring

/-- **Cancellation of the two line-bundle factors in the target-chart compatibility**: this time
the cocycle identity for `L` is used at `(j₂, i₂, i₁)` and then at `(j₂, i₁, j₁)`. -/
theorem scl_twist_cancel_inv (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (i₁ i₂ j₁ j₂ : ιL) (b : B)
    (hi₁ : b ∈ L.baseSet i₁) (hi₂ : b ∈ L.baseSet i₂)
    (hj₁ : b ∈ L.baseSet j₁) (hj₂ : b ∈ L.baseSet j₂) :
    Work.Gen.scl (L.coordChange i₁ j₁ b) * Work.Gen.scl (L.coordChange j₂ i₂ b) *
      Work.Gen.scl (L.coordChange i₂ i₁ b) = Work.Gen.scl (L.coordChange j₂ j₁ b) := by
  have h1 := Work.Gen.scl_cc_comp L j₂ i₂ i₁ b ⟨⟨hj₂, hi₂⟩, hi₁⟩
  have h2 := Work.Gen.scl_cc_comp L j₂ i₁ j₁ b ⟨⟨hj₂, hi₁⟩, hj₁⟩
  rw [h2, h1]
  ring

/-! ## The theorem -/

/-- **`L ⊗ (L* ⊗ E) ≅ E`**: a line bundle cancels against its dual.  The isomorphism is the
identity on fibres, with the gauge family `p = (i, (i', e)) ↦ scl (L.c_{i i'}) • E.c_{e t}`. -/
theorem nonempty_bundleIso_twist_dual {B : Type} [TopologicalSpace B] {ιL ιE : Type} {n : ℕ}
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE) :
    Nonempty (Work.Thom.BundleIso
      (Work.LerayHirsch.twistCore L (Work.LerayHirsch.twistCore (Work.Gen.dualLineCore L) E)) E) := by
  refine Work.Thom.nonempty_bundleIso_of_gauge
    (twistCore L (twistCore (Work.Gen.dualLineCore L) E)) E
    (fun p t b => Work.Gen.scl (L.coordChange p.1 p.2.1 b) • E.coordChange p.2.2 t b)
    (fun p t b => Work.Gen.scl (L.coordChange p.2.1 p.1 b) • E.coordChange t p.2.2 b)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- continuity of the gauge
    intro p t
    rw [twistCore_dual_twist_baseSet]
    have h1 : ContinuousOn (fun b => Work.Gen.scl (L.coordChange p.1 p.2.1 b))
        ((L.baseSet p.1 ∩ (L.baseSet p.2.1 ∩ E.baseSet p.2.2)) ∩ E.baseSet t) :=
      (Work.Gen.continuous_scl.comp_continuousOn
        (L.continuousOn_coordChange p.1 p.2.1)).mono (fun b hb => ⟨hb.1.1, hb.1.2.1⟩)
    have h2 : ContinuousOn (fun b => E.coordChange p.2.2 t b)
        ((L.baseSet p.1 ∩ (L.baseSet p.2.1 ∩ E.baseSet p.2.2)) ∩ E.baseSet t) :=
      (E.continuousOn_coordChange p.2.2 t).mono (fun b hb => ⟨hb.1.2.2, hb.2⟩)
    exact h1.smul h2
  · -- continuity of the inverse gauge
    intro p t
    rw [twistCore_dual_twist_baseSet]
    have h1 : ContinuousOn (fun b => Work.Gen.scl (L.coordChange p.2.1 p.1 b))
        ((L.baseSet p.1 ∩ (L.baseSet p.2.1 ∩ E.baseSet p.2.2)) ∩ E.baseSet t) :=
      (Work.Gen.continuous_scl.comp_continuousOn
        (L.continuousOn_coordChange p.2.1 p.1)).mono (fun b hb => ⟨hb.1.2.1, hb.1.1⟩)
    have h2 : ContinuousOn (fun b => E.coordChange t p.2.2 b)
        ((L.baseSet p.1 ∩ (L.baseSet p.2.1 ∩ E.baseSet p.2.2)) ∩ E.baseSet t) :=
      (E.continuousOn_coordChange t p.2.2).mono (fun b hb => ⟨hb.2, hb.1.2.2⟩)
    exact h1.smul h2
  · -- target-chart compatibility: `E.c_{t t'} ∘ gauge p t = gauge p t'`
    intro p t t' b hb ht ht'
    rw [twistCore_dual_twist_baseSet] at hb
    obtain ⟨-, -, he⟩ := hb
    rw [ContinuousLinearMap.comp_smul,
      VectorBundleCore.coordChange_linear_comp E p.2.2 t t' b ⟨⟨he, ht⟩, ht'⟩]
  · -- source-chart compatibility: `gauge p t ∘ Z.c_{p' p} = gauge p' t`
    intro p t p' b hb hb' ht
    rw [twistCore_dual_twist_baseSet] at hb hb'
    obtain ⟨hi₁, hi₂, he⟩ := hb
    obtain ⟨hj₁, hj₂, hf⟩ := hb'
    rw [twistCore_dual_twist_coordChange]
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_smul, smul_smul, smul_smul]
    rw [VectorBundleCore.coordChange_linear_comp E p'.2.2 p.2.2 t b ⟨⟨hf, he⟩, ht⟩]
    rw [scl_twist_cancel_source L p.1 p.2.1 p'.1 p'.2.1 b hi₁ hi₂ hj₁ hj₂]
  · -- target-chart compatibility of the inverse gauge
    intro p t t' b hb ht ht'
    rw [twistCore_dual_twist_baseSet] at hb
    obtain ⟨-, -, he⟩ := hb
    rw [ContinuousLinearMap.smul_comp,
      VectorBundleCore.coordChange_linear_comp E t' t p.2.2 b ⟨⟨ht', ht⟩, he⟩]
  · -- source-chart compatibility of the inverse gauge
    intro p t p' b hb hb' ht
    rw [twistCore_dual_twist_baseSet] at hb hb'
    obtain ⟨hi₁, hi₂, he⟩ := hb
    obtain ⟨hj₁, hj₂, hf⟩ := hb'
    rw [twistCore_dual_twist_coordChange]
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul, smul_smul, smul_smul]
    rw [VectorBundleCore.coordChange_linear_comp E t p.2.2 p'.2.2 b ⟨⟨ht, he⟩, hf⟩]
    rw [scl_twist_cancel_inv L p.1 p.2.1 p'.1 p'.2.1 b hi₁ hi₂ hj₁ hj₂]
  · -- the two gauges are inverse to each other at matching indices
    intro p t b v hb
    rw [twistCore_dual_twist_baseSet] at hb
    obtain ⟨⟨hi₁, hi₂, he⟩, ht⟩ := hb
    rw [smul_apply, smul_apply, map_smul,
      E.coordChange_comp p.2.2 t p.2.2 b ⟨⟨he, ht⟩, he⟩ v,
      E.coordChange_self p.2.2 b he v, smul_smul,
      Work.Gen.scl_cc_recip L p.1 p.2.1 b hi₁ hi₂]
    simp
  · intro p t b v hb
    rw [twistCore_dual_twist_baseSet] at hb
    obtain ⟨⟨hi₁, hi₂, he⟩, ht⟩ := hb
    rw [smul_apply, smul_apply, map_smul,
      E.coordChange_comp t p.2.2 t b ⟨⟨ht, he⟩, ht⟩ v,
      E.coordChange_self t b ht v, smul_smul,
      Work.Gen.scl_cc_recip L p.2.1 p.1 b hi₂ hi₁]
    simp

end

end Work.LerayHirsch
