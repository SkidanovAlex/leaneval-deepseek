import Mathlib
import Submission.Work.SphereJordan.pairingSetup
import Submission.Work.SphereJordan.pairingPieces
import Submission.Work.SphereJordan.span_pairing_plan
import Submission.Work.SphereJordan.tgtUpPC_isSimple
import Submission.Work.SphereJordan.incrOn
import Submission.Work.SphereJordan.odd_windNumber_of_mem_V

namespace Work.SphereJordan

open Set

/-- **The three pairing identities of the two-cuts configuration.**

For a simple closed plane curve `γ` in the open unit disc with Schoenflies datum `S`, the
configuration `H : SpanHyp`, and a point `x` of the bounded side, the winding numbers of the four
four-arc curves about `x` satisfy the three identities

* `w (upPC true) + w (dnPC false) = 1`,
* `w (upPC false) + w (dnPC true) = 1`,
* `w (upPC true) + w (dnPC true) = 1 + w γ`.

Each is proved by decomposing the loop of each four-arc curve into the increments of its four
quarter arcs (`upLoop_decomp_true` etc.): the two crosscuts appear once in each direction and
cancel, one of the two `γ`-arcs cancels against its reverse, and the two outer semicircles
together traverse the unit circle once. -/
theorem windNumber_pairing_identities {γ : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : Work.SphereJordan.SpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    (Work.Smooth.SphereJordan.windNumber (H.upPC true).γ (H.upPC true).cont x
      + Work.Smooth.SphereJordan.windNumber (H.dnPC false).γ (H.dnPC false).cont x = 1) ∧
    (Work.Smooth.SphereJordan.windNumber (H.upPC false).γ (H.upPC false).cont x
      + Work.Smooth.SphereJordan.windNumber (H.dnPC true).γ (H.dnPC true).cont x = 1) ∧
    (Work.Smooth.SphereJordan.windNumber (H.upPC true).γ (H.upPC true).cont x
      + Work.Smooth.SphereJordan.windNumber (H.dnPC true).γ (H.dnPC true).cont x
      = 1 + Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `w (upPC true) + w (dnPC false) = 1`
    have hsum : incr' (upLoop H x true) + incr' (dnLoop H x false) =
        ((1 : ℤ) : ℂ) * kappa := by
      rw [upLoop_decomp_true H hx, dnLoop_decomp_false H hx]
      rw [show
        (incOn (outerC S) (continuous_outerC S) x 0 Real.pi +
            incOn (cutC₂ H) (continuous_cutC₂ H) x 0 1 +
            incOn γ.γ γ.cont x H.θ₂ H.θ₁ +
            incOn (cutC₁ H) (continuous_cutC₁ H) x 1 0) +
          (incOn (outerC S) (continuous_outerC S) x Real.pi (2 * Real.pi) +
            incOn (cutC₁ H) (continuous_cutC₁ H) x 0 1 +
            incOn γ.γ γ.cont x H.θ₁ H.θ₂ +
            incOn (cutC₂ H) (continuous_cutC₂ H) x 1 0) =
        (incOn (outerC S) (continuous_outerC S) x 0 Real.pi +
            incOn (outerC S) (continuous_outerC S) x Real.pi (2 * Real.pi)) +
          (incOn (cutC₂ H) (continuous_cutC₂ H) x 0 1 +
            incOn (cutC₂ H) (continuous_cutC₂ H) x 1 0) +
          (incOn γ.γ γ.cont x H.θ₂ H.θ₁ + incOn γ.γ γ.cont x H.θ₁ H.θ₂) +
          (incOn (cutC₁ H) (continuous_cutC₁ H) x 1 0 +
            incOn (cutC₁ H) (continuous_cutC₁ H) x 0 1) from by ring]
      rw [incr_outer_pair H hx, incr_cut₂_pair H hx, incr_gamma_pair_A H hx,
        incr_cut₁_pair H hx]
      ring
    have hloop := loopIndex_pair_eq (upLoop_ne H hx true) (dnLoop_ne H hx false)
      (upLoop_closed H x true) (dnLoop_closed H x false) hsum
    rw [windNumber_upLoop H x true, windNumber_dnLoop H x false]
    exact hloop
  · -- `w (upPC false) + w (dnPC true) = 1`
    have hsum : incr' (upLoop H x false) + incr' (dnLoop H x true) =
        ((1 : ℤ) : ℂ) * kappa := by
      rw [upLoop_decomp_false H hx, dnLoop_decomp_true H hx]
      rw [show
        (incOn (outerC S) (continuous_outerC S) x 0 Real.pi +
            incOn (cutC₂ H) (continuous_cutC₂ H) x 0 1 +
            incOn γ.γ γ.cont x H.θ₂ (H.θ₁ - 2 * Real.pi) +
            incOn (cutC₁ H) (continuous_cutC₁ H) x 1 0) +
          (incOn (outerC S) (continuous_outerC S) x Real.pi (2 * Real.pi) +
            incOn (cutC₁ H) (continuous_cutC₁ H) x 0 1 +
            incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ +
            incOn (cutC₂ H) (continuous_cutC₂ H) x 1 0) =
        (incOn (outerC S) (continuous_outerC S) x 0 Real.pi +
            incOn (outerC S) (continuous_outerC S) x Real.pi (2 * Real.pi)) +
          (incOn (cutC₂ H) (continuous_cutC₂ H) x 0 1 +
            incOn (cutC₂ H) (continuous_cutC₂ H) x 1 0) +
          (incOn γ.γ γ.cont x H.θ₂ (H.θ₁ - 2 * Real.pi) +
            incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂) +
          (incOn (cutC₁ H) (continuous_cutC₁ H) x 1 0 +
            incOn (cutC₁ H) (continuous_cutC₁ H) x 0 1) from by ring]
      rw [incr_outer_pair H hx, incr_cut₂_pair H hx, incr_gamma_pair_B H hx,
        incr_cut₁_pair H hx]
      ring
    have hloop := loopIndex_pair_eq (upLoop_ne H hx false) (dnLoop_ne H hx true)
      (upLoop_closed H x false) (dnLoop_closed H x true) hsum
    rw [windNumber_upLoop H x false, windNumber_dnLoop H x true]
    exact hloop
  · -- `w (upPC true) + w (dnPC true) = 1 + w γ`
    have hsum : incr' (upLoop H x true) + incr' (dnLoop H x true) =
        (((1 + Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x : ℤ)) : ℂ) * kappa := by
      rw [upLoop_decomp_true H hx, dnLoop_decomp_true H hx]
      rw [show
        (incOn (outerC S) (continuous_outerC S) x 0 Real.pi +
            incOn (cutC₂ H) (continuous_cutC₂ H) x 0 1 +
            incOn γ.γ γ.cont x H.θ₂ H.θ₁ +
            incOn (cutC₁ H) (continuous_cutC₁ H) x 1 0) +
          (incOn (outerC S) (continuous_outerC S) x Real.pi (2 * Real.pi) +
            incOn (cutC₁ H) (continuous_cutC₁ H) x 0 1 +
            incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ +
            incOn (cutC₂ H) (continuous_cutC₂ H) x 1 0) =
        (incOn (outerC S) (continuous_outerC S) x 0 Real.pi +
            incOn (outerC S) (continuous_outerC S) x Real.pi (2 * Real.pi)) +
          (incOn (cutC₂ H) (continuous_cutC₂ H) x 0 1 +
            incOn (cutC₂ H) (continuous_cutC₂ H) x 1 0) +
          (incOn γ.γ γ.cont x H.θ₂ H.θ₁ +
            incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂) +
          (incOn (cutC₁ H) (continuous_cutC₁ H) x 1 0 +
            incOn (cutC₁ H) (continuous_cutC₁ H) x 0 1) from by ring]
      rw [incr_outer_pair H hx, incr_cut₂_pair H hx, incr_gamma_pair_C H hx,
        incr_cut₁_pair H hx]
      push_cast
      ring
    have hloop := loopIndex_pair_eq (upLoop_ne H hx true) (dnLoop_ne H hx true)
      (upLoop_closed H x true) (dnLoop_closed H x true) hsum
    rw [windNumber_upLoop H x true, windNumber_dnLoop H x true]
    exact hloop

end Work.SphereJordan
