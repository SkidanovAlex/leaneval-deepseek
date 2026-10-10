import Mathlib
import Submission.Work.MotK.TwRuling.sdW_four_ne_zero
import Submission.Work.MotAS.TwistField

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.ASChart3

-- `asTwY D g i = ∑ j, algebraMap (Kb 𝕜) (Om D) ((asM (asRoot g))⁻¹ i j) * kleinCoord D (Kb 𝕜) j`
-- (TwistField.lean), the coefficients lie in `Kb 𝕜`, and `kleinCoord D L` is by definition a
-- `Kb 𝕜`-combination of `kleinBas D (Kb 𝕜) = sdBas (D.E.baseChange (Kb 𝕜))` (they are the same
-- `![1, x, y, x², xy]`; `rfl`).
-- Route: `rw [Work.MotAS.asTwY]`, then `Finset.sum_mem` / `Submodule.smul_mem` with
-- `← Algebra.smul_def`, and for each `kleinCoord D (Kb 𝕜) j` use
-- `Work.MotV.kleinCoord_eq_sum` (or unfold `kleinCoord`/`kleinBas`) and `sdBas`'s definitional
-- equality with `kleinBas`.  No hypothesis on `D` or `g` is needed, and no characteristic
-- hypothesis: `asTwY`'s coefficients are *defined* through `(asM _)⁻¹` and are already in `Kb 𝕜`.
theorem asTwY_mem_span (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (i : Fin 5) :
    Work.MotAS.asTwY D g i ∈ Submodule.span (Work.MotV.Kb 𝕜)
      (Set.range (Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotV.Kb 𝕜)))) := by
  -- `kleinBas` and `sdBas` are the same five functions `![1, x, y, x², xy]`.
  have hbas : ∀ m : Fin 5, Work.MotV.kleinBas D (Work.MotV.Kb 𝕜) m =
      Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotV.Kb 𝕜)) m := fun m => rfl
  -- Each Klein coordinate lies in the span.
  have hklein : ∀ j : Fin 5, Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) j ∈
      Submodule.span (Work.MotV.Kb 𝕜)
        (Set.range (Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotV.Kb 𝕜)))) := by
    intro j
    rw [Work.MotV.kleinCoord_eq_sum]
    apply Submodule.sum_mem
    intro m _
    rw [hbas m, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  rw [Work.MotAS.asTwY]
  apply Submodule.sum_mem
  intro j _
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (hklein j)

end Work.MotAS.ASChart3
