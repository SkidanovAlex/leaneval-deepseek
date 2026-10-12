import Mathlib.Analysis.InnerProductSpace.Calculus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/TauSmAdm/Radial.lean`

Auxiliary material for `Work.BoseBoxFock.tauSm_admissible`.

**`radial_contDiff`.**  If `f : ℝ → ℝ` is `C^∞` and vanishes on `(-∞, 1]`, then the radial
function `p ↦ f ‖p‖` on `ℝ³` is `C^∞`: away from the origin this is the chain rule with the
smoothness of the norm (`contDiffAt_norm`), and at the origin the function agrees on a
neighbourhood of `0` with the constant `f 0 = 0`.

This is applied to `f = tauProf = tauPhi` (which is `C^∞` and vanishes on `(-∞,1]`), giving the
smoothness conjunct of `tauSm_admissible`.
-/

noncomputable section

open Metric

namespace Work.BoseBoxFock.TauSmAdm

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- If `f : ℝ → ℝ` is smooth and vanishes on `(-∞, 1]`, then `p ↦ f ‖p‖` is smooth on `ℝ³`. -/
theorem radial_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (h0 : ∀ r ≤ 1, f r = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 => f ‖p‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : E3) one_pos] with p hp
    rw [Metric.mem_ball, dist_zero_right] at hp
    exact h0 ‖p‖ (le_of_lt hp)
  · exact (hf.contDiffAt).comp x (contDiffAt_norm ℝ hx)

end Work.BoseBoxFock.TauSmAdm
