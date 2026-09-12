import Mathlib

/-!
Global instances making *nested* continuous-linear-map spaces normed (the default
instance chain stops at depth three in the pinned Mathlib revision).
-/

open ContinuousLinearMap

namespace Submission.CLMInstances

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The space `E →L (E →L (E →L ℝ))` of second derivatives of `Bilin`-valued families. -/
abbrev TripleBilin (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))

noncomputable instance tripleBilin_normedAddCommGroup [FiniteDimensional ℝ E] :
    NormedAddCommGroup (TripleBilin E) := by
  letI : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  infer_instance

noncomputable instance tripleBilin_normedSpace [FiniteDimensional ℝ E] :
    NormedSpace ℝ (TripleBilin E) := by
  letI : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  infer_instance

noncomputable instance tripleBilin_completeSpace [FiniteDimensional ℝ E] :
    CompleteSpace (TripleBilin E) := by
  letI : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  infer_instance

end

end Submission.CLMInstances
