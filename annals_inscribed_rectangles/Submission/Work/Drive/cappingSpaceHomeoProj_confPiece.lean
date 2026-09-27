import Mathlib
import Submission.Work.Drive.cappingCharted
import Submission.Work.Drive.lensToProj_confTorus
import Submission.Work.Drive.cappingProjCoords
import Submission.Work.Drive.exists_cappingModel_projectivization
import Submission.Work.Drive.cappingSpace_homeomorph_prod
import Submission.Work.Drive.stripConfigInterface

namespace Work.Drive

/-- **The projective coordinate of a configuration point of the capping space.**

**Renamed** (session 9, node `Work.Drive.parityCore_of_isSmoothEmbedding`): the declaration was
`Work.Drive.cappingSpaceHomeoProj_confPiece`, but a lemma of that name already exists in
`Submission/Work/Drive/contMDiffAt_cappingSpace_configPiece.lean` (with the conclusion
`(⟨r,·⟩, lensToProj ⟦inr (d,η)⟧)` instead of the projectivisation `mk ℝ (confProjVecOf u d)`), and two
declarations of one name make the two modules mutually unimportable (verified).  This is the strictly
more explicit form; a consumer needing both uses `cappingSpaceHomeoProj_confPiece_proj` and
`lensToProj_confPiece`.

`cappingSpaceHomeoProj` is the composite `CappingSpace → (0,∞) × LensSpace → (0,∞) × ℝP³` of
`Φ` (`cappingSpace_homeomorph_prod`) with `lensToProj` (`exists_cappingModel_projectivization`), so on a
configuration point it evaluates to
`((Φ x).1, lensToProj ((Φ x).2))`.  For `x = ⟦inl (confPiece p h1 h2)⟧` the first component is the radial
coordinate `(confOf p).1` (with its positivity proof `h1`, which `Φ` reads off through `toProdConfig`),
and the slice coordinate is the class of `(⟨(confOf p).2.1, _⟩, (confOf p).2.2)` in the configuration
solid torus.  The explicit formula `lensToProj_confTorus` then identifies the projective class with
`confProjVecOf u ((confOf p).2.1)`, where `u` is any square root of `circleOf ((confOf p).2.2)`. -/
theorem cappingSpaceHomeoProj_confPiece_proj (p : (ℝ × ℝ) × UnitAddCircle × ℝ)
    (h1 : 0 < (confOf p).1) (h2 : ‖(confOf p).2.1‖ ≤ 1) {u : ℂ}
    (hu : u ^ 2 = circleOf ((confOf p).2.2)) :
    cappingSpaceHomeoProj (Quotient.mk'' (Sum.inl (confPiece p h1 h2) : ConfigPiece ⊕ CapPiece))
      = (⟨(confOf p).1, h1⟩,
          Projectivization.mk ℝ (confProjVecOf u ((confOf p).2.1))
            (confProjVecOf_ne_zero (norm_eq_one_of_sq_eq_circleOf hu) h2)) := by
  -- `cappingSpaceHomeoProj = cappingSpaceHomeoSlice.trans (refl.prodCongr lensSpaceHomeoProj)` and
  -- `cappingSpaceHomeoSlice` has underlying map `Φ`, so the composite is
  -- `x ↦ ((Φ x).1, lensToProj ((Φ x).2))`, and `Φ (⟦inl a⟧) = toProdConfig a`.
  rw [show cappingSpaceHomeoProj
        (Quotient.mk'' (Sum.inl (confPiece p h1 h2) : ConfigPiece ⊕ CapPiece))
      = ((⟨(confOf p).1, h1⟩ : Set.Ioi (0:ℝ)),
          lensToProj (Quotient.mk'' (Sum.inr (⟨(confOf p).2.1,
            mem_closedBall_of_norm_le_one h2⟩, (confOf p).2.2)
            : CapTorus ⊕ ConfTorus) : LensSpace))
      from rfl]
  -- the slice coordinate is the configuration solid torus point `(⟨(confOf p).2.1, _⟩, (confOf p).2.2)`
  exact Prod.ext rfl
    (lensToProj_confTorus ⟨(confOf p).2.1, mem_closedBall_of_norm_le_one h2⟩ (confOf p).2.2 hu)

end Work.Drive
