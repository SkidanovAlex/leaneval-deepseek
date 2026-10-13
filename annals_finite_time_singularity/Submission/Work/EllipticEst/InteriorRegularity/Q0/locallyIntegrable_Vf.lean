/-
Local integrability of the transported unknown `Vf α Ψ` on the strip.

The hypothesis `LocallyIntegrableOn (Function.uncurry Ψ) Q0` constrains `Ψ` only on the *open*
quadrant `(0,∞) × (0,π/2)`; the conclusion is local integrability of `Vf α Ψ` on the open strip
`stripE = {0 < θ < π/2}`.  Since every point of `stripE` has a compact neighbourhood contained in
`stripE`, and the change of variables `(σ,θ) ↦ (e^{ασ}, θ)` is a diffeomorphism from the strip onto
the quadrant (Jacobian `α e^{ασ} ≠ 0`), the conclusion follows from the change-of-variables formula
(the hypothesis is used exactly in the form `IntegrableOn (uncurry Ψ) (Φ '' K)` for `K ⊆ stripE`
compact — where `Φ '' K` is a compact subset of the *open* quadrant, so the boundary behaviour of
`Ψ` plays no role).

Structure of the proof:

* `integrableOn_pullback_wtRR` (`Q0/integrableOn_pullback_wtRR.lean`) — the change-of-variables
  integrability statement in the `(σ,θ)`-coordinates of `Q0.RRDefs`;
* `locallyIntegrableOn_VRR` — local integrability of the `ℝ × ℝ`-transported unknown on the
  half-strip `stripRR`, from the change-of-variables statement via the compact-set criterion
  `MeasureTheory.locallyIntegrableOn_iff`;
* `locallyIntegrableOn_coords_of_stripRR`
  (`Q0/locallyIntegrableOn_coords_of_stripRR.lean`) — transfer of local integrability from the
  half-strip `stripRR ⊆ ℝ × ℝ` to the strip `stripE ⊆ E2` along the measure preserving bijection
  `coords`;
* `cplx_Vf_eq_VRR` — the identification `↑(Vf α Ψ x) = ↑(VRR α Ψ (x 0) (x 1))`, an immediate
  consequence of `Q0.VRR_eq_Vf` and `Q0.coords_mk`;
* `locallyIntegrable_Vf` — the target, by rewriting with the identification.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.InteriorRegularity.Q0.Defs
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRDefs
import Submission.Work.EllipticEst.InteriorRegularity.Q0.integrableOn_pullback_wtRR
import Submission.Work.EllipticEst.InteriorRegularity.Q0.locallyIntegrableOn_coords_of_stripRR
import Submission.Work.EllipticEst.InteriorRegularity.Q0.stripWeakQ0_of_RR
import Submission.Work.EllipticEst.InteriorRegularity.Strip
import Submission.Work.EllipticEst.InteriorRegularity.VT.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

/-- **Local integrability of the `(σ,θ)`-transported unknown on the half-strip.**

The half-strip `stripRR = ℝ × (0,π/2)` is open, so by the compact-set criterion
`MeasureTheory.locallyIntegrableOn_iff` it suffices to check integrability on a compact
`K ⊆ stripRR`; there `VRR α Ψ` coincides with the pure change-of-variables integrand
`wtRR α σ θ · Ψ (e^{ασ}, θ)` handled by `integrableOn_pullback_wtRR` (the `if θ ∈ (0,π/2)` in the
definition of `VRR` is discharged by the hypothesis `K ⊆ stripRR`). -/
theorem locallyIntegrableOn_VRR {α : ℝ} (hα : α ≠ 0) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.LocallyIntegrableOn
      (fun q : ℝ × ℝ => (VRR α Ψ q.1 q.2 : ℂ)) stripRR := by
  have hopen : IsLocallyClosed (stripRR : Set (ℝ × ℝ)) :=
    (isOpen_univ.prod isOpen_Ioo).isLocallyClosed
  rw [MeasureTheory.locallyIntegrableOn_iff hopen]
  intro K hK hKc
  refine (integrableOn_pullback_wtRR hα hΨ hKc hK).congr_fun (fun p hp => ?_) hKc.measurableSet
  have hp' : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := (hK hp).2
  rw [VRR, if_pos hp']

/-- The transported unknown of `Q0.Defs` agrees with the `(σ,θ)`-transported unknown of
`Q0.RRDefs` under the coordinate identification: this is `Q0.VRR_eq_Vf` at the coordinates of
the point `x`. -/
theorem cplx_Vf_eq_VRR (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (x : E2) :
    ((Vf α Ψ x : ℝ) : ℂ) = ((VRR α Ψ (x 0) (x 1) : ℝ) : ℂ) := by
  have h := VRR_eq_Vf α Ψ (x 0) (x 1)
  rw [coords_mk x] at h
  exact congrArg (fun r : ℝ => (r : ℂ)) h.symm

theorem locallyIntegrable_Vf {α : ℝ} (hα : α ≠ 0) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.LocallyIntegrableOn
      (fun x : E2 => (Work.EllipticEst.InteriorRegularity.Q0.Vf α Ψ x : ℂ))
      Work.EllipticEst.InteriorRegularity.stripE := by
  have h1 : MeasureTheory.LocallyIntegrableOn
      (fun x : E2 => (VRR α Ψ (x 0) (x 1) : ℂ))
      Work.EllipticEst.InteriorRegularity.stripE :=
    locallyIntegrableOn_coords_of_stripRR (locallyIntegrableOn_VRR hα hΨ)
  exact h1.congr (Filter.Eventually.of_forall fun x => (cplx_Vf_eq_VRR α Ψ x).symm)

end Work.EllipticEst.InteriorRegularity.Q0
