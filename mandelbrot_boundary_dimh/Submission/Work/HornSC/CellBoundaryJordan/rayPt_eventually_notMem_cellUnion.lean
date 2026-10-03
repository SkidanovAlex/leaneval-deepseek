import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.RayDefs
import Submission.Work.HornSC.Cells

namespace Work.HornSC.CellBoundaryJordan

/-- The ray `t ↦ a + t (1 + εI)` leaves the finite union of lattice cells `cellUnion A` for all
sufficiently large `t`: the union of finitely many unit cells is bounded, while the real part of
the ray point (hence its norm) tends to `+∞`. -/
lemma rayPt_eventually_notMem_cellUnion (A : Finset (ℤ × ℤ)) (a : ℂ) (ε : ℝ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → rayPt a ε t ∉ cellUnion A := by
  obtain ⟨R, hRpos, hR⟩ := (isCompact_cellUnion A).isBounded.exists_pos_norm_le
  refine ⟨R + ‖a‖ + 1, fun t ht hmem => ?_⟩
  have hle : ‖rayPt a ε t‖ ≤ R := hR _ hmem
  -- the real part of the ray point exceeds `R` once `t ≥ R + ‖a‖ + 1`
  have hbound : R + 1 ≤ (rayPt a ε t).re := by
    rw [rayPt_re]
    have ha : -‖a‖ ≤ a.re := (abs_le.mp (Complex.abs_re_le_norm a)).1
    linarith
  have hlt : R < ‖rayPt a ε t‖ := by
    have h1 : |(rayPt a ε t).re| ≤ ‖rayPt a ε t‖ := Complex.abs_re_le_norm _
    have h2 : |(rayPt a ε t).re| = (rayPt a ε t).re := abs_of_pos (by linarith)
    linarith
  linarith

end Work.HornSC.CellBoundaryJordan
