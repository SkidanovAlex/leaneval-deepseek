import Mathlib
import Submission.Work.Mostow.nearId_blk
import Submission.Work.Mostow.fermiW_chart
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.fermi_inv
import Submission.Work.Mostow.nib_hdist_fermiW_le
import Submission.Work.Mostow.nib_hdist_lt_of_disp_lt

/-!
# `nearId_blk_char`: the characteristic (two-scale) form of near-identity for a block isometry

For the block element `blk 1 m 1 R` (the identity on the stratum, `R` on the normal fibre) the
`η`-near-identity property at a point `fermiW 1 m v W` of the stratum is *equivalent* to the
pointwise bound `‖R W' - W'‖ < 2 sinh (η/2)` for the normal vectors `W'` whose Fermi point
`fermiW 1 m v W'` still lies in the unit ball around `fermiW 1 m v W`.

This is the exact form used in the GAP-A strata chain: near-identity statements about the block
element can be traded back and forth with purely Euclidean statements about `R` on `E m`.

Route.  `cosh (hdist (fermiW v W) (blk 1 m 1 R • fermiW v W)) = 1 + ‖R W - W‖² / 2`, and
`1 + ‖R W - W‖²/2 < 1 + (2 sinh (η/2))²/2 = cosh η`, so hyperbolicity of `cosh` gives the
equivalence in both directions; the converse direction also uses that, of two Fermi points with
the same normal coordinates, the one with coincident tangential coordinates is the closer one
(`nib_hdist_fermiW_le`), so the normal part `nrmC 1 m u` of an arbitrary point `u` of the unit
ball lies in the ball considered by the pointwise condition.
-/

namespace Work.Mostow

open Submission.Mostow

theorem nearIdAtBlkChar (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1) (hA : Submission.Mostow.POActionProp (1 + m))
    (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) (v : Submission.Mostow.E 1)
    (W : Submission.Mostow.E m) (η : ℝ) :
    Submission.Mostow.NearIdAt (Submission.Mostow.blk 1 m 1 R) (Submission.Mostow.fermiW 1 m v W) η ↔
      ∀ W' : Submission.Mostow.E m,
        Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W) (Submission.Mostow.fermiW 1 m v W') ≤ 1 →
        ‖R W' - W'‖ < 2 * Real.sinh (η / 2) := by
  constructor
  · -- forward: near-identity at `fermiW v W` bounds the displacement at each `fermiW v W'` in the ball
    intro hni W' hW'
    exact nib_disp_lt_of_hdist_lt m hA1 hI1 hA hI R v W' η (hni _ hW')
  · -- reverse: the pointwise bound spreads to the whole unit ball, thanks to the slice inequality
    intro hpt u hu
    have hsurj := nib_fermiW_surj m u
    have hslice : hdist (fermiW 1 m v W) (fermiW 1 m v (nrmC 1 m u)) ≤ 1 := by
      have h1 := nib_hdist_fermiW_le m v ((Real.sqrt (1 + ‖nrmC 1 m u‖ ^ 2))⁻¹ • tanC 1 m u)
        W (nrmC 1 m u)
      rw [hsurj] at h1
      refine le_trans h1 ?_
      rw [hI.2.1 u (fermiW 1 m v W)]
      exact hu
    have hdisp : ‖R (nrmC 1 m u) - nrmC 1 m u‖ < 2 * Real.sinh (η / 2) := hpt _ hslice
    have hgoal : hdist u (blk 1 m 1 R • u) < η := by
      rw [← hsurj]
      exact nib_hdist_lt_of_disp_lt m hA1 hI1 hA hI R _ (nrmC 1 m u) η hdisp
    exact hgoal

end Work.Mostow
