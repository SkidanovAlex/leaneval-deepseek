import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dth
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Assembly

/-- `RegQ` is closed under `D_θ`, in the sharp range `α ≥ -1/10`: the interior smoothness
comes from `SmoothQuad (D_θ f)`, the `ℋⁿ`-membership from the pointwise domination of the
`D_θ`-shifted integrands (`HkIntegrand α n (D_θ f) ≤ HkIntegrand α (n+1) f`, valid exactly
for `η ≤ γ(α)`, i.e. `α ≥ -1/10`), and the boundary traces from the reindexing
`mixed b a (D_θ f) = mixed b (a+1) f`. -/
theorem RegQ_dth_ge (α : ℝ) (hα : -(1/10 : ℝ) ≤ α) {n : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.Nonlin.RegQ α (n + 1) f) :
    Work.FTS.Nonlin.RegQ α n (Work.Spaces.Dth f) := by
  obtain ⟨hsm, hmem, hbd⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · exact Work.FTS.CoercivityFix.QuadPorts.smoothQuad_Dth hsm
  · exact Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge α n hα ⟨hsm, hmem, hbd⟩
  · intro a b hab
    have key : ∀ z θ, Work.Spaces.mixed b a (Work.Spaces.Dth f) z θ
        = Work.Spaces.mixed b (a + 1) f z θ := fun z θ => by
      rw [Work.FTS.CoercivityFix.QuadPorts.mixed_Dth_shift]
    simpa only [key] using hbd (a + 1) b (by omega)

end Work.FTS.CoercivityFix.Assembly
