import Mathlib
import Submission.Work.MotV5.LamAS.asML
import Submission.Work.MotV5.LamAS.Setup
import Submission.Work.MotV5.kleinField_eq_adjoin_genXY
import Submission.Work.MotC.adjoin_genX_genY_eq_top
import Submission.Work.MotV5.adjoin_genX_genY

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.MotV5.LamAS

/-- **The image of `M = L(E)` in `Om D = Kb(E)` is `Ω = kleinField D ⊔ LImage D L`.**  With `L = asL2 f₁ f₂` the two-root Artin–Schreier field, the base-change map `asIota` from the `L`-model `M = asML D f₁ f₂ = L(E)` into the algebraic-closure model `Om D` has range exactly the compositum of the geometric part `kleinField D` and the image `LImage D L` of the constants. -/
theorem asIota_range (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ : RatFunc 𝕜) :
    (Work.MotV5.LamAS.asIota D f₁ f₂).fieldRange =
      Work.MotV5.kleinField D ⊔ Work.MotV5.LamAS.LImage D (Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) := by
  classical
  have hgood : D.Good := hD.1
  -- the two generators of `M = L(genX, genY)` over `L`
  have hadj : IntermediateField.adjoin ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)
        ({Work.MotV.genX (Work.MotV5.LamAS.asE2 D f₁ f₂),
          Work.MotV.genY (Work.MotV5.LamAS.asE2 D f₁ f₂)} :
          Set (Work.MotV5.LamAS.asML D f₁ f₂)) = ⊤ :=
    Work.MotV5.adjoin_genX_genY ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)
      (Work.MotV5.LamAS.asE2 D f₁ f₂)
  -- the generators of `kleinField D`
  have hklein : ∀ z : Work.MotV.Om D, z ∈ ({Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜)),
        Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜))} : Set (Work.MotV.Om D)) →
      z ∈ Work.MotV5.kleinField D := by
    intro z hz
    rw [Work.MotV5.kleinField_eq_adjoin_genXY 𝕜 D hgood]
    exact IntermediateField.subset_adjoin _ _ hz
  refine le_antisymm ?_ ?_
  · -- `ι(M) ⊆ Ω`: every element of `M = L(genX, genY)` lands in `Ω`
    rintro y hy
    rw [AlgHom.mem_fieldRange] at hy
    obtain ⟨x, rfl⟩ := hy
    have hx : x ∈ IntermediateField.adjoin ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)
        ({Work.MotV.genX (Work.MotV5.LamAS.asE2 D f₁ f₂),
          Work.MotV.genY (Work.MotV5.LamAS.asE2 D f₁ f₂)} :
          Set (Work.MotV5.LamAS.asML D f₁ f₂)) := by
      rw [hadj]; trivial
    refine IntermediateField.adjoin_induction ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)
      (p := fun z _ => Work.MotV5.LamAS.asIota D f₁ f₂ z ∈
        Work.MotV5.kleinField D ⊔ Work.MotV5.LamAS.LImage D
          (Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂))
      (fun z hz => ?_) (fun c => ?_) (fun z w _ _ hz hw => ?_)
      (fun z _ hz => ?_) (fun z w _ _ hz hw => ?_) hx
    · -- the two generators `genX`, `genY` of `M` map to generators of `kleinField D`
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · rw [Work.MotV5.LamAS.asIota_genX]
        exact (le_sup_left : Work.MotV5.kleinField D ≤
          Work.MotV5.kleinField D ⊔ Work.MotV5.LamAS.LImage D
            (Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂))
          (hklein _ (Set.mem_insert _ _))
      · rw [Work.MotV5.LamAS.asIota_genY]
        exact (le_sup_left : Work.MotV5.kleinField D ≤
          Work.MotV5.kleinField D ⊔ Work.MotV5.LamAS.LImage D
            (Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂))
          (hklein _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    · -- the constants of `L` land in `LImage D L`
      rw [Work.MotV5.LamAS.asIota_algebraMap]
      exact (le_sup_right : Work.MotV5.LamAS.LImage D
        (Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) ≤
          Work.MotV5.kleinField D ⊔ Work.MotV5.LamAS.LImage D
            (Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂))
        ((Work.MotV5.LamAS.mem_LImage_iff D
          (Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) _).mpr ⟨c, c.2, rfl⟩)
    · rw [map_add]; exact add_mem hz hw
    · rw [map_inv₀]; exact inv_mem hz
    · rw [map_mul]; exact mul_mem hz hw
  · -- `Ω ⊆ ι(M)`
    rw [sup_le_iff]
    refine ⟨?_, ?_⟩
    · rw [Work.MotV5.kleinField_eq_adjoin_genXY 𝕜 D hgood, IntermediateField.adjoin_le_iff]
      intro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact AlgHom.mem_fieldRange.mpr
          ⟨Work.MotV.genX (Work.MotV5.LamAS.asE2 D f₁ f₂),
            Work.MotV5.LamAS.asIota_genX D f₁ f₂⟩
      · exact AlgHom.mem_fieldRange.mpr
          ⟨Work.MotV.genY (Work.MotV5.LamAS.asE2 D f₁ f₂),
            Work.MotV5.LamAS.asIota_genY D f₁ f₂⟩
    · rw [Work.MotV5.LamAS.LImage]
      intro z hz
      obtain ⟨l, hl, rfl⟩ := (IntermediateField.mem_map
        (S := Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)
        (f := IsScalarTower.toAlgHom (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D))).mp hz
      exact AlgHom.mem_fieldRange.mpr
        ⟨algebraMap ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)
            (Work.MotV5.LamAS.asML D f₁ f₂) ⟨l, hl⟩,
          Work.MotV5.LamAS.asIota_algebraMap D f₁ f₂ ⟨l, hl⟩⟩

end Work.MotV5.LamAS
