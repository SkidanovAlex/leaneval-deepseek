import Mathlib
import Submission.Work.LerayHirsch.Twist
import Submission.Work.Thom.BundleIso_comap_exists
import Submission.Work.Gen.LineTensor

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Functoriality of the twist: `E ≅ F` gives `L ⊗ E ≅ L ⊗ F`

The fibrewise map of the twist of a bundle isomorphism `e : E ≅ F` by a line bundle `L` is `e.hom`
itself; only the continuity of the induced map of total spaces has to be checked, and that is the
chart expression `(scl L.c) • (F.c ∘ e.clmGen ∘ E.c)`, a continuous scalar multiple of the chart
expression of `e` (`Work.Thom.continuousOn_chartExpressionCLM_gen`).
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ιL ιE ιF : Type} {n : ℕ}

/-- **The chart expression of the twist of a bundle isomorphism.**  In the charts `i₁ = (l₁,e₁)` of
`L ⊗ E` and `i₂ = (l₂,f₂)` of `L ⊗ F`, the trivialised matrix of `L ⊗ e` is
`(scl L.c_{l₂ l₁}) · (F.c_{f₂} ∘ e.clmGen ∘ E.c_{e₁})`. -/
theorem twistCore_chartExpression (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιF)
    (e : BundleIso E F) (i₁ : ιL × ιE) (i₂ : ιL × ιF) (b : B) :
    ((twistCore L F).coordChange ((twistCore L F).indexAt b) i₂ b).comp
        ((e.clmGen b).comp ((twistCore L E).coordChange i₁ ((twistCore L E).indexAt b) b))
      = (Work.Gen.scl (L.coordChange (L.indexAt b) i₂.1 b) *
          Work.Gen.scl (L.coordChange i₁.1 (L.indexAt b) b)) •
        ((F.coordChange (F.indexAt b) i₂.2 b).comp
          ((e.clmGen b).comp (E.coordChange i₁.2 (E.indexAt b) b))) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, twistCore_coordChange, twistCore_indexAt,
    ContinuousLinearMap.smul_apply, smul_apply, map_smul, smul_smul]
  rw [mul_comm]

/-- **The twist of a bundle isomorphism**: `L ⊗ E ≅ L ⊗ F` from `E ≅ F`. -/
theorem nonempty_bundleIso_twist_congr (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιF)
    (e : BundleIso E F) :
    Nonempty (BundleIso (twistCore L E) (twistCore L F)) := by
  -- the product of the two `L`-transitions, as a chart expression of the identity of `L`
  have hcomp : ∀ (l₁ l₂ : ιL), ContinuousOn (fun b : B =>
      (L.coordChange (L.indexAt b) l₂ b).comp (L.coordChange l₁ (L.indexAt b) b))
      (L.baseSet l₁ ∩ L.baseSet l₂) := by
    intro l₁ l₂
    refine (continuousOn_chartExpressionCLM_gen L L (BundleIso.refl L) l₁ l₂).congr ?_
    intro b hb
    ext v
    simp only [ContinuousLinearMap.comp_apply, BundleIso.clmGen_apply, BundleIso.refl_hom,
      LinearMap.id_coe, id_eq]
  have hscalar : ∀ (l₁ l₂ : ιL), ContinuousOn (fun b : B =>
      Work.Gen.scl (L.coordChange (L.indexAt b) l₂ b) *
        Work.Gen.scl (L.coordChange l₁ (L.indexAt b) b))
      (L.baseSet l₁ ∩ L.baseSet l₂) := by
    intro l₁ l₂
    refine (Work.Gen.continuous_scl.comp_continuousOn (hcomp l₁ l₂)).congr ?_
    intro b hb
    exact (Work.Gen.scl_comp _ _).symm
  have hmid : ∀ (i₁ : ιL × ιE) (i₂ : ιL × ιF), ContinuousOn (fun b : B =>
      (F.coordChange (F.indexAt b) i₂.2 b).comp
        ((e.clmGen b).comp (E.coordChange i₁.2 (E.indexAt b) b)))
      (E.baseSet i₁.2 ∩ F.baseSet i₂.2) :=
    fun i₁ i₂ => continuousOn_chartExpressionCLM_gen E F e i₁.2 i₂.2
  have hchart : ∀ (i₁ : ιL × ιE) (i₂ : ιL × ιF), ContinuousOn (fun b : B =>
      ((twistCore L F).coordChange ((twistCore L F).indexAt b) i₂ b).comp
        ((e.clmGen b).comp ((twistCore L E).coordChange i₁ ((twistCore L E).indexAt b) b)))
      ((twistCore L E).baseSet i₁ ∩ (twistCore L F).baseSet i₂) := by
    intro i₁ i₂
    have hc : ContinuousOn (fun b : B =>
        Work.Gen.scl (L.coordChange (L.indexAt b) i₂.1 b) *
          Work.Gen.scl (L.coordChange i₁.1 (L.indexAt b) b))
        ((twistCore L E).baseSet i₁ ∩ (twistCore L F).baseSet i₂) :=
      (hscalar i₁.1 i₂.1).mono (fun b hb => ⟨hb.1.1, hb.2.1⟩)
    have hM : ContinuousOn (fun b : B =>
        (F.coordChange (F.indexAt b) i₂.2 b).comp
          ((e.clmGen b).comp (E.coordChange i₁.2 (E.indexAt b) b)))
        ((twistCore L E).baseSet i₁ ∩ (twistCore L F).baseSet i₂) :=
      (hmid i₁ i₂).mono (fun b hb => ⟨hb.1.2, hb.2.2⟩)
    refine (hc.smul hM).congr ?_
    intro b hb
    exact twistCore_chartExpression L E F e i₁ i₂ b
  have hchart' : ∀ (i₂ : ιL × ιF) (i₁ : ιL × ιE), ContinuousOn (fun b : B =>
      ((twistCore L E).coordChange ((twistCore L E).indexAt b) i₁ b).comp
        (((BundleIso.symm e).clmGen b).comp
          ((twistCore L F).coordChange i₂ ((twistCore L F).indexAt b) b)))
      ((twistCore L F).baseSet i₂ ∩ (twistCore L E).baseSet i₁) := by
    intro i₂ i₁
    have hc : ContinuousOn (fun b : B =>
        Work.Gen.scl (L.coordChange (L.indexAt b) i₁.1 b) *
          Work.Gen.scl (L.coordChange i₂.1 (L.indexAt b) b))
        ((twistCore L F).baseSet i₂ ∩ (twistCore L E).baseSet i₁) :=
      (hscalar i₂.1 i₁.1).mono (fun b hb => ⟨hb.1.1, hb.2.1⟩)
    have hM : ContinuousOn (fun b : B =>
        (E.coordChange (E.indexAt b) i₁.2 b).comp
          (((BundleIso.symm e).clmGen b).comp (F.coordChange i₂.2 (F.indexAt b) b)))
        ((twistCore L F).baseSet i₂ ∩ (twistCore L E).baseSet i₁) :=
      ((continuousOn_chartExpressionCLM_gen F E (BundleIso.symm e) i₂.2 i₁.2)).mono
        (fun b hb => ⟨hb.1.2, hb.2.2⟩)
    refine (hc.smul hM).congr ?_
    intro b hb
    exact twistCore_chartExpression L F E (BundleIso.symm e) i₂ i₁ b
  refine ⟨{ hom := fun b => e.hom b
            inv := fun b => e.inv b
            left_inv := fun b x => e.left_inv b x
            right_inv := fun b y => e.right_inv b y
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · refine (continuous_totalSpaceMap_clm_gen (twistCore L E) (twistCore L F)
      (ContinuousMap.id B) (fun b => e.clmGen b) (fun i₁ i₂ => hchart i₁ i₂)).congr
      (fun p => ?_)
    apply Bundle.TotalSpace.ext
    · rfl
    · exact heq_of_eq (BundleIso.clmGen_apply e p.1 p.2)
  · refine (continuous_totalSpaceMap_clm_gen (twistCore L F) (twistCore L E)
      (ContinuousMap.id B) (fun b => (BundleIso.symm e).clmGen b)
      (fun i₂ i₁ => hchart' i₂ i₁)).congr (fun p => ?_)
    apply Bundle.TotalSpace.ext
    · rfl
    · exact heq_of_eq (BundleIso.clmGen_apply (BundleIso.symm e) p.1 p.2)

end

end Work.LerayHirsch
