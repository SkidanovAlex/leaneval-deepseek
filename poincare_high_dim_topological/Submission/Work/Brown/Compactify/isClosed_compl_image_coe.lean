import Mathlib
import Submission.Work.Brown.Basic

namespace Work.Brown.Compactify

theorem isClosed_compl_image_coe {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U) : IsClosed (((↑) '' U : Set (OnePoint X))ᶜ) := by
  rw [← isOpen_compl_iff, compl_compl, OnePoint.isOpen_image_coe]
  exact hU

end Work.Brown.Compactify
