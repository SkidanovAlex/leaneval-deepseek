import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.RotBasics.PS

namespace Work.TMComp.IDSPrufer

open Work.TMComp.RotBasics

theorem pruferStep_dir_nonhalf (a t : ℝ) (hcase : t - (⌊t + 1 / 2⌋ : ℝ) ≠ -1 / 2) :
    ∃ r : ℝ, 0 < r ∧
      (a * Real.cos (Real.pi * t) - Real.sin (Real.pi * t), Real.cos (Real.pi * t)) =
        (r * Real.cos (Real.pi * Work.TMContract.pruferStep a t),
         r * Real.sin (Real.pi * Work.TMContract.pruferStep a t)) := by
  obtain ⟨ρ, hρ, h⟩ := pruferStep_smul_eq a t
  refine ⟨ρ, hρ, ?_⟩
  have hc : (⟨a * Real.cos (Real.pi * t) - Real.sin (Real.pi * t),
      Real.cos (Real.pi * t)⟩ : ℂ) = ρ • vc (Work.TMContract.pruferStep a t) := by
    rw [← smul_comp a t]
    exact h
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · have := congrArg Complex.re hc
    simpa [vc, Complex.smul_re] using this
  · have := congrArg Complex.im hc
    simpa [vc, Complex.smul_im] using this

end Work.TMComp.IDSPrufer
