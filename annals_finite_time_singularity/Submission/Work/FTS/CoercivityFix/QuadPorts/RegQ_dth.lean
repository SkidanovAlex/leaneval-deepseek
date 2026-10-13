import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.QuadAux
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.CoercivityFix.QuadPorts

/-- `D_θ` raises the angular order of the mixed derivatives by one:
`D_z^j D_θ^i (D_θ f) = D_z^j D_θ^{i+1} f`. -/
theorem mixed_Dth_shift (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth f) = Work.Spaces.mixed j (i + 1) f := by
  simp only [Work.Spaces.mixed]
  have h : Work.Spaces.Dth f = Work.Spaces.DthIter 1 f := rfl
  rw [h, Work.Spaces.DthIter_add_right]

/-- `D_θ` preserves `C^∞`-smoothness on the open quadrant. -/
theorem smoothQuad_Dth {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth f) := by
  have h := hf.DthIter 1
  rwa [show Work.Spaces.DthIter 1 f = Work.Spaces.Dth f from rfl] at h

theorem RegQ_dth (α : ℝ) (hα : 0 < α) {n : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.Nonlin.RegQ α (n + 1) f) :
    Work.FTS.Nonlin.RegQ α n (Work.Spaces.Dth f) := by
  obtain ⟨hsm, hmem, hbd⟩ := h
  have hsm' : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth f) := smoothQuad_Dth hsm
  refine ⟨hsm', ?_, ?_⟩
  · -- the `ℋⁿ`-membership, by domination of the integrands
    refine Work.FTS.LocData.HkMem_of_majorant α n
      (f := Work.Spaces.Dth f)
      (M := fun z θ => Work.Spaces.HkIntegrand α (n + 1) f z θ) ?_ ?_ ?_ ?_
    · exact Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α n (Work.Spaces.Dth f) hsm'
    · exact hmem.1
    · exact hmem.2
    · intro z hz θ hθ
      exact Work.Coercivity.HkIntegrand_Dth_le α hα n f z θ hz hθ
  · -- the boundary traces, by the reindexing of the mixed derivatives
    intro a b hab
    have key : ∀ z θ, Work.Spaces.mixed b a (Work.Spaces.Dth f) z θ
        = Work.Spaces.mixed b (a + 1) f z θ := fun z θ => by rw [mixed_Dth_shift]
    simpa only [key] using hbd (a + 1) b (by omega)

end Work.FTS.CoercivityFix.QuadPorts
