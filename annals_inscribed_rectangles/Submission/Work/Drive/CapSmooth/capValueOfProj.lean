import Mathlib
import Submission.Work.Drive.lensToProj_capTorus
import Submission.Work.Drive.cappingSpace_homeomorph_prod
import Submission.Work.Drive.exists_cappingModel_projectivization

/-!
# The value of `cappingSpaceHomeoProj` on a point of the cap piece

`Work.Drive.cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³` is the concrete homeomorphism
along which the transparent smooth structure `Work.Drive.cappingCharted` of the capping space is
transported (`Submission/Work/Drive/cappingCharted.lean`).  Its configuration-piece value is recorded
in `Submission/Work/Drive/contMDiffAt_cappingSpace_configPiece.lean`
(`Work.Drive.cappingSpaceHomeoProj_confPiece`, proved there); this file records the **cap-piece**
value, which is the missing half and the first step of every smoothness statement about a map into
the capping space that uses the cap solid torus (the cap of a capped plane is such a map).

The formula necessarily involves a chosen square root `w` of `circleOf θ` — the cap coordinate of
`LensSpace` is the *square* of a unit complex number — and `Work.Drive.lensToProj_capTorus` supplies
the identification with the sphere lift `Work.Drive.capProjVecOf w d`.
-/

namespace Work.Drive.CapSmooth

open Manifold
open scoped Manifold ContDiff

/-- **The value of `cappingSpaceHomeoProj` on a cap-piece point.** -/
theorem cappingSpaceHomeoProj_capValue (p : ℝ × UnitAddCircle × ℂ) (h1 : 0 < p.1)
    (h2 : ‖p.2.2‖ ≤ 1) {w : ℂ} (hw : w ^ 2 = circleOf p.2.1) :
    Work.Drive.cappingSpaceHomeoProj
        (Quotient.mk'' (Sum.inr (⟨p, h1, h2⟩ : Work.Drive.CapPiece) :
          Work.Drive.ConfigPiece ⊕ Work.Drive.CapPiece))
      = (⟨p.1, h1⟩, Projectivization.mk ℝ (Work.Drive.capProjVecOf w p.2.2)
          (Work.Drive.capProjVecOf_ne_zero (Work.Drive.norm_eq_one_of_sq_eq_circleOf hw) h2)) := by
  have hΦ : Work.Drive.Φ (Quotient.mk'' (Sum.inr (⟨p, h1, h2⟩ : Work.Drive.CapPiece) :
      Work.Drive.ConfigPiece ⊕ Work.Drive.CapPiece))
      = Work.Drive.toProdCap (⟨p, h1, h2⟩ : Work.Drive.CapPiece) := rfl
  have hproj : Work.Drive.cappingSpaceHomeoProj
      (Quotient.mk'' (Sum.inr (⟨p, h1, h2⟩ : Work.Drive.CapPiece) :
        Work.Drive.ConfigPiece ⊕ Work.Drive.CapPiece))
      = ((Work.Drive.Φ (Quotient.mk'' (Sum.inr (⟨p, h1, h2⟩ : Work.Drive.CapPiece) :
            Work.Drive.ConfigPiece ⊕ Work.Drive.CapPiece))).1,
          Work.Drive.lensToProj ((Work.Drive.Φ (Quotient.mk'' (Sum.inr (⟨p, h1, h2⟩ :
            Work.Drive.CapPiece) : Work.Drive.ConfigPiece ⊕ Work.Drive.CapPiece))).2)) := rfl
  rw [hproj, hΦ]
  simp only [Work.Drive.toProdCap, Work.Drive.capTorusOf]
  refine Prod.ext (Subtype.ext rfl) ?_
  rw [Work.Drive.lensToProj_capTorus p.2.1
    ⟨p.2.2, Work.Drive.mem_closedBall_of_norm_le_one h2⟩ hw]

end Work.Drive.CapSmooth
