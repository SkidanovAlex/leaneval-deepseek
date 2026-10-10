import Mathlib
import Submission.Work.MotC5N3.LamAS.asML
import Submission.Work.MotC5N3.LamAS.Setup
import Submission.Work.MotC5N3.TwistField.kleinField_eq_adjoin_genXY
import Submission.Work.MotV5.adjoin_genX_genY

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.MotC5N3.LamAS

/-- **The image of `M = L(E)` in `OmA K D` is `Ω = kleinField K D ⊔ LImage D L`.** -/
theorem asIota_range (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K]
    [CharP K 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ : K) :
    (asIota D f₁ f₂).fieldRange =
      Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂) := by
  classical
  have hgood : D.Good := hD.1
  have hadj : IntermediateField.adjoin ↥(asL2 f₁ f₂)
        ({Work.MotV.genX (asE2 D f₁ f₂),
          Work.MotV.genY (asE2 D f₁ f₂)} :
          Set (asML D f₁ f₂)) = ⊤ :=
    Work.MotV5.adjoin_genX_genY ↥(asL2 f₁ f₂) (asE2 D f₁ f₂)
  have hklein : ∀ z : OmA K D, z ∈ ({Work.MotV.genX (D.E.baseChange (KbA K)),
        Work.MotV.genY (D.E.baseChange (KbA K))} : Set (OmA K D)) →
      z ∈ Work.MotC5N3.kleinField K D := by
    intro z hz
    rw [Work.MotC5N3.kleinField_eq_adjoin_genXY 𝕜 D hgood]
    exact IntermediateField.subset_adjoin _ _ hz
  refine le_antisymm ?_ ?_
  · rintro y hy
    rw [AlgHom.mem_fieldRange] at hy
    obtain ⟨x, rfl⟩ := hy
    have hx : x ∈ IntermediateField.adjoin ↥(asL2 f₁ f₂)
        ({Work.MotV.genX (asE2 D f₁ f₂),
          Work.MotV.genY (asE2 D f₁ f₂)} :
          Set (asML D f₁ f₂)) := by
      rw [hadj]; trivial
    refine IntermediateField.adjoin_induction ↥(asL2 f₁ f₂)
      (p := fun z _ => asIota D f₁ f₂ z ∈
        Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂))
      (fun z hz => ?_) (fun c => ?_) (fun z w _ _ hz hw => ?_)
      (fun z _ hz => ?_) (fun z w _ _ hz hw => ?_) hx
    · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · rw [asIota_genX]
        exact (le_sup_left : Work.MotC5N3.kleinField K D ≤
          Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂))
          (hklein _ (Set.mem_insert _ _))
      · rw [asIota_genY]
        exact (le_sup_left : Work.MotC5N3.kleinField K D ≤
          Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂))
          (hklein _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    · rw [asIota_algebraMap]
      exact (le_sup_right : LImage D (asL2 f₁ f₂) ≤
          Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂))
        ((mem_LImage_iff D (asL2 f₁ f₂) _).mpr ⟨c, c.2, rfl⟩)
    · rw [map_add]; exact add_mem hz hw
    · rw [map_inv₀]; exact inv_mem hz
    · rw [map_mul]; exact mul_mem hz hw
  · rw [sup_le_iff]
    refine ⟨?_, ?_⟩
    · rw [Work.MotC5N3.kleinField_eq_adjoin_genXY 𝕜 D hgood, IntermediateField.adjoin_le_iff]
      intro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact AlgHom.mem_fieldRange.mpr
          ⟨Work.MotV.genX (asE2 D f₁ f₂), asIota_genX D f₁ f₂⟩
      · exact AlgHom.mem_fieldRange.mpr
          ⟨Work.MotV.genY (asE2 D f₁ f₂), asIota_genY D f₁ f₂⟩
    · rw [LImage]
      intro z hz
      obtain ⟨l, hl, rfl⟩ := (IntermediateField.mem_map
        (S := asL2 f₁ f₂)
        (f := IsScalarTower.toAlgHom K (KbA K) (OmA K D))).mp hz
      exact AlgHom.mem_fieldRange.mpr
        ⟨algebraMap ↥(asL2 f₁ f₂) (asML D f₁ f₂) ⟨l, hl⟩, asIota_algebraMap D f₁ f₂ ⟨l, hl⟩⟩

end Work.MotC5N3.LamAS
