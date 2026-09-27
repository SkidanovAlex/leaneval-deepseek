import Mathlib
import Submission.Work.Drive.cappingCharted
import Submission.Work.Drive.lensToProj_capTorus
import Submission.Work.Drive.cappingProjCoords
import Submission.Work.Drive.exists_cappingModel_projectivization
import Submission.Work.Drive.cappingSpace_homeomorph_prod

namespace Work.Drive

/-!
# The value of `cappingSpaceHomeoProj` on the cap piece

`Work.Drive.cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³` is the composite of the explicit
homeomorphism `Φ : CappingSpace ≃ₜ (0,∞) × LensSpace` of
`Submission/Work/Drive/cappingSpace_homeomorph_prod.lean` (which keeps the radial coordinate and
passes the slice coordinates to the lens space) with the identification
`lensSpaceHomeoProj = lensToProj : LensSpace ≃ₜ ℝP³` of
`Submission/Work/Drive/exists_cappingModel_projectivization.lean`.

On a cap piece point `p = (r, θ, d) ∈ (0,∞) × S¹ × D²` this reads
`cappingSpaceHomeoProj [inr p] = (r, lensToProj [inl (θ, d)])`, and the sphere lift of the cap torus
point `(θ, d)` is the projectivisation of `Work.Drive.capProjVecOf w d` for any square root `w` of
`circleOf θ` (`Work.Drive.lensToProj_capTorus`).  This file supplies both steps, the first as an
`rfl`-level unfolding of `Φ` and the second by rewriting with `lensToProj_capTorus` and killing the
irrelevant non-vanishing proof with `Work.Drive.projectivizationMk_congr`.
-/

/-- **The value of `cappingSpaceHomeoProj` on a cap piece point, before the sphere lift.**  The map
`Work.Drive.Φ : CappingSpace → (0,∞) × LensSpace` sends `(r, θ, d)` to `(r, [θ, d])`
(`Work.Drive.toProdCap`), so the value of `cappingSpaceHomeoProj`, which is `Φ` followed by the slice
identification `lensSpaceHomeoProj`, is `(r, lensToProj [θ, d])`. -/
lemma cappingSpaceHomeoProj_capPiece_val (r : ℝ) (θ : UnitAddCircle) (d : ℂ) (hr : 0 < r)
    (hd : ‖d‖ ≤ 1) :
    cappingSpaceHomeoProj
        (Quotient.mk'' (Sum.inr (⟨(r, θ, d), hr, hd⟩ : CapPiece)) : CappingSpace)
      = (⟨r, hr⟩,
          lensToProj (Quotient.mk'' (Sum.inl ((θ,
            ⟨d, mem_closedBall_of_norm_le_one hd⟩) : CapTorus)) : LensSpace)) := rfl

theorem cappingSpaceHomeoProj_capPiece (p : ℝ × UnitAddCircle × ℂ)
    (h1 : 0 < p.1) (h2 : ‖p.2.2‖ ≤ 1) {w : ℂ} (hw : w ^ 2 = circleOf p.2.1) :
    cappingSpaceHomeoProj
        (Quotient.mk'' (Sum.inr (⟨p, h1, h2⟩ : CapPiece) : ConfigPiece ⊕ CapPiece))
      = (⟨p.1, h1⟩,
          Projectivization.mk ℝ (capProjVecOf w p.2.2)
            (capProjVecOf_ne_zero (norm_eq_one_of_sq_eq_circleOf hw) h2)) := by
  -- the value of `cappingSpaceHomeoProj` before the sphere lift
  have h := cappingSpaceHomeoProj_capPiece_val p.1 p.2.1 p.2.2 h1 h2
  rw [h]
  refine Prod.ext rfl ?_
  -- the sphere lift of the cap torus point `(θ, d)` with the chosen square root `w`
  refine (lensToProj_capTorus p.2.1 ⟨p.2.2, mem_closedBall_of_norm_le_one h2⟩ hw).trans ?_
  -- the two non-vanishing proofs are irrelevant
  exact projectivizationMk_congr ℝ (Eucl 3)

end Work.Drive
