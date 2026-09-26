import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.pairingSetup
import Submission.Work.Smooth.SphereJordan.PCopy.pairingPieces
import Submission.Work.Smooth.SphereJordan.PCopy.span_pairing_plan
import Submission.Work.Smooth.SphereJordan.PCopy.tgtUpPC_isSimple
import Submission.Work.SphereJordan.incrOn
import Submission.Work.SphereJordan.odd_windNumber_of_mem_V

namespace Work.SphereJordan

open Set

/-- **The three pairing identities of the two-pccuts configuration.**

For a simple closed plane curve `γ` in the open unit disc with Schoenflies datum `S`, the
configuration `H : pcSpanHyp`, and a point `x` of the bounded side, the winding numbers of the four
four-arc curves about `x` satisfy the three identities

* `w (pcupPC true) + w (pcdnPC false) = 1`,
* `w (pcupPC false) + w (pcdnPC true) = 1`,
* `w (pcupPC true) + w (pcdnPC true) = 1 + w γ`.

Each is proved by decomposing the loop of each four-arc curve into the increments of its four
quarter arcs (`pcupLoop_decomp_true` etc.): the two crosscuts appear once in each direction and
cancel, one of the two `γ`-arcs cancels against its reverse, and the two outer semicircles
together traverse the unit circle once. -/
theorem pcwindNumber_pairing_identities {γ : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : Work.SphereJordan.pcSpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    (Work.Smooth.SphereJordan.windNumber (H.pcupPC true).γ (H.pcupPC true).cont x
      + Work.Smooth.SphereJordan.windNumber (H.pcdnPC false).γ (H.pcdnPC false).cont x = 1) ∧
    (Work.Smooth.SphereJordan.windNumber (H.pcupPC false).γ (H.pcupPC false).cont x
      + Work.Smooth.SphereJordan.windNumber (H.pcdnPC true).γ (H.pcdnPC true).cont x = 1) ∧
    (Work.Smooth.SphereJordan.windNumber (H.pcupPC true).γ (H.pcupPC true).cont x
      + Work.Smooth.SphereJordan.windNumber (H.pcdnPC true).γ (H.pcdnPC true).cont x
      = 1 + Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `w (pcupPC true) + w (pcdnPC false) = 1`
    have hsum : pcincr' (pcupLoop H x true) + pcincr' (pcdnLoop H x false) =
        ((1 : ℤ) : ℂ) * pckappa := by
      rw [pcupLoop_decomp_true H hx, pcdnLoop_decomp_false H hx]
      rw [show
        (incOn (pcouterC S) (pccontinuous_outerC S) x 0 Real.pi +
            incOn (pccutC₂ H) (pccontinuous_cutC₂ H) x 0 1 +
            incOn γ.γ γ.cont x H.θ₂ H.θ₁ +
            incOn (pccutC₁ H) (pccontinuous_cutC₁ H) x 1 0) +
          (incOn (pcouterC S) (pccontinuous_outerC S) x Real.pi (2 * Real.pi) +
            incOn (pccutC₁ H) (pccontinuous_cutC₁ H) x 0 1 +
            incOn γ.γ γ.cont x H.θ₁ H.θ₂ +
            incOn (pccutC₂ H) (pccontinuous_cutC₂ H) x 1 0) =
        (incOn (pcouterC S) (pccontinuous_outerC S) x 0 Real.pi +
            incOn (pcouterC S) (pccontinuous_outerC S) x Real.pi (2 * Real.pi)) +
          (incOn (pccutC₂ H) (pccontinuous_cutC₂ H) x 0 1 +
            incOn (pccutC₂ H) (pccontinuous_cutC₂ H) x 1 0) +
          (incOn γ.γ γ.cont x H.θ₂ H.θ₁ + incOn γ.γ γ.cont x H.θ₁ H.θ₂) +
          (incOn (pccutC₁ H) (pccontinuous_cutC₁ H) x 1 0 +
            incOn (pccutC₁ H) (pccontinuous_cutC₁ H) x 0 1) from by ring]
      rw [pcincr_outer_pair H hx, pcincr_cut₂_pair H hx, pcincr_gamma_pair_A H hx,
        pcincr_cut₁_pair H hx]
      ring
    have hloop := pcloopIndex_pair_eq (pcupLoop_ne H hx true) (pcdnLoop_ne H hx false)
      (pcupLoop_closed H x true) (pcdnLoop_closed H x false) hsum
    rw [pcwindNumber_upLoop H x true, pcwindNumber_dnLoop H x false]
    exact hloop
  · -- `w (pcupPC false) + w (pcdnPC true) = 1`
    have hsum : pcincr' (pcupLoop H x false) + pcincr' (pcdnLoop H x true) =
        ((1 : ℤ) : ℂ) * pckappa := by
      rw [pcupLoop_decomp_false H hx, pcdnLoop_decomp_true H hx]
      rw [show
        (incOn (pcouterC S) (pccontinuous_outerC S) x 0 Real.pi +
            incOn (pccutC₂ H) (pccontinuous_cutC₂ H) x 0 1 +
            incOn γ.γ γ.cont x H.θ₂ (H.θ₁ - 2 * Real.pi) +
            incOn (pccutC₁ H) (pccontinuous_cutC₁ H) x 1 0) +
          (incOn (pcouterC S) (pccontinuous_outerC S) x Real.pi (2 * Real.pi) +
            incOn (pccutC₁ H) (pccontinuous_cutC₁ H) x 0 1 +
            incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ +
            incOn (pccutC₂ H) (pccontinuous_cutC₂ H) x 1 0) =
        (incOn (pcouterC S) (pccontinuous_outerC S) x 0 Real.pi +
            incOn (pcouterC S) (pccontinuous_outerC S) x Real.pi (2 * Real.pi)) +
          (incOn (pccutC₂ H) (pccontinuous_cutC₂ H) x 0 1 +
            incOn (pccutC₂ H) (pccontinuous_cutC₂ H) x 1 0) +
          (incOn γ.γ γ.cont x H.θ₂ (H.θ₁ - 2 * Real.pi) +
            incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂) +
          (incOn (pccutC₁ H) (pccontinuous_cutC₁ H) x 1 0 +
            incOn (pccutC₁ H) (pccontinuous_cutC₁ H) x 0 1) from by ring]
      rw [pcincr_outer_pair H hx, pcincr_cut₂_pair H hx, pcincr_gamma_pair_B H hx,
        pcincr_cut₁_pair H hx]
      ring
    have hloop := pcloopIndex_pair_eq (pcupLoop_ne H hx false) (pcdnLoop_ne H hx true)
      (pcupLoop_closed H x false) (pcdnLoop_closed H x true) hsum
    rw [pcwindNumber_upLoop H x false, pcwindNumber_dnLoop H x true]
    exact hloop
  · -- `w (pcupPC true) + w (pcdnPC true) = 1 + w γ`
    have hsum : pcincr' (pcupLoop H x true) + pcincr' (pcdnLoop H x true) =
        (((1 + Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x : ℤ)) : ℂ) * pckappa := by
      rw [pcupLoop_decomp_true H hx, pcdnLoop_decomp_true H hx]
      rw [show
        (incOn (pcouterC S) (pccontinuous_outerC S) x 0 Real.pi +
            incOn (pccutC₂ H) (pccontinuous_cutC₂ H) x 0 1 +
            incOn γ.γ γ.cont x H.θ₂ H.θ₁ +
            incOn (pccutC₁ H) (pccontinuous_cutC₁ H) x 1 0) +
          (incOn (pcouterC S) (pccontinuous_outerC S) x Real.pi (2 * Real.pi) +
            incOn (pccutC₁ H) (pccontinuous_cutC₁ H) x 0 1 +
            incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ +
            incOn (pccutC₂ H) (pccontinuous_cutC₂ H) x 1 0) =
        (incOn (pcouterC S) (pccontinuous_outerC S) x 0 Real.pi +
            incOn (pcouterC S) (pccontinuous_outerC S) x Real.pi (2 * Real.pi)) +
          (incOn (pccutC₂ H) (pccontinuous_cutC₂ H) x 0 1 +
            incOn (pccutC₂ H) (pccontinuous_cutC₂ H) x 1 0) +
          (incOn γ.γ γ.cont x H.θ₂ H.θ₁ +
            incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂) +
          (incOn (pccutC₁ H) (pccontinuous_cutC₁ H) x 1 0 +
            incOn (pccutC₁ H) (pccontinuous_cutC₁ H) x 0 1) from by ring]
      rw [pcincr_outer_pair H hx, pcincr_cut₂_pair H hx, pcincr_gamma_pair_C H hx,
        pcincr_cut₁_pair H hx]
      push_cast
      ring
    have hloop := pcloopIndex_pair_eq (pcupLoop_ne H hx true) (pcdnLoop_ne H hx true)
      (pcupLoop_closed H x true) (pcdnLoop_closed H x true) hsum
    rw [pcwindNumber_upLoop H x true, pcwindNumber_dnLoop H x true]
    exact hloop

end Work.SphereJordan
