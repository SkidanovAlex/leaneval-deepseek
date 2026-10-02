import Mathlib
import Submission.Work.TangentClasses.Cohomology
import Submission.Work.Cohomology.homotopyInvariance

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.TangentClasses

open CategoryTheory

/-- Homotopic continuous maps induce the same pullback on singular cohomology.

`HMap f n` is `f^* : H^n(B₂;ℤ) → H^n(B₁;ℤ)` in the chapter's cohomology model, and
`TopCat.Homotopy (TopCat.ofHom φ) (TopCat.ofHom φ')` is *definitionally* the type
`ContinuousMap.Homotopy φ φ'`, so this is exactly the homotopy invariance of singular
cohomology (`Work.Cohomology.homotopyInvariance`). -/
theorem HMap_homotopic {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂] {φ φ' : C(B₁, B₂)}
    (h : ContinuousMap.Homotopic φ φ') (n : ℕ) :
    Work.TangentClasses.HMap φ n = Work.TangentClasses.HMap φ' n := by
  obtain ⟨H⟩ := h
  exact Work.Cohomology.homotopyInvariance ℤ (TopCat.of B₁) (TopCat.of B₂) H n

end Work.TangentClasses
