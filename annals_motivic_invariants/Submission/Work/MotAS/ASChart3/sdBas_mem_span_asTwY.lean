import Mathlib
import Submission.Work.MotK.TwRuling.sdW_four_ne_zero
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.twistFieldAS_eq

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.ASChart3

-- Here `[CharP 𝕜 5]` is essential: it is exactly what makes the Vandermonde matrix
-- `asM (asRoot g)` invertible (`asM_mul_asMinv` / `asMinv_mul_asM` in
-- `Submission/Work/MotAS/asM_mul_asMinv.lean`, `asMinv_mul_asM.lean`).
-- Route: `asTwY = asNO D g *ᵥ asKap D` (`Work.MotAS.asTwY_eq_mulVec`) and
-- `asMO D g *ᵥ asTwY = asKap D` (`Work.MotAS.asMO_mulVec_asTwY`), so every
-- `kleinCoord D (Kb 𝕜) i` is a `Kb 𝕜`-combination of the `asTwY D g j`; then `hD.spans`
-- writes `kleinBas D (Kb 𝕜) m = sdBas (D.E.baseChange (Kb 𝕜)) m` as a `𝕜`-combination of the
-- `kleinCoord`s.  Conclude with `Finset.sum_mem` / `Submodule.smul_mem` / `Submodule.subset_span`.
theorem sdBas_mem_span_asTwY (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : D.Good) (g : RatFunc 𝕜) (m : Fin 5) :
    Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotV.Kb 𝕜)) m
      ∈ Submodule.span (Work.MotV.Kb 𝕜) (Set.range (Work.MotAS.asTwY D g)) := by
  -- `sdBas` and `kleinBas` are the same basis `![1, x, y, x², xy]` of `L(5·O)`.
  have hsd : ∀ m : Fin 5, Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotV.Kb 𝕜)) m =
      Work.MotV.kleinBas D (Work.MotV.Kb 𝕜) m := by
    intro m; fin_cases m <;> rfl
  -- `D.Good.spans` writes the basis in the `kleinCoord`s over `Kb 𝕜`.
  obtain ⟨e, he⟩ := hD.spans
  rw [hsd m, he (Work.MotV.Kb 𝕜) m]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  -- Each `kleinCoord i = asKap i` is a `Kb 𝕜`-combination of the `asTwY j`
  -- (`asMO D g *ᵥ asTwY D g = asKap D`, whose entries are images of `asM (asRoot g)`).
  have hκ : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i ∈
      Submodule.span (Work.MotV.Kb 𝕜) (Set.range (Work.MotAS.asTwY D g)) := by
    have h := congrFun (Work.MotAS.asMO_mulVec_asTwY D g) i
    simp only [Work.MotAS.asKap] at h
    rw [← h]
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    rw [show Work.MotAS.asMO D g i j = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)
        (Work.MotAS.asM (Work.MotV5.asRoot g) i j) from rfl, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hκ

end Work.MotAS.ASChart3
