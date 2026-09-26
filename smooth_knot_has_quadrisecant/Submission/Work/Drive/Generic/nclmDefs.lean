import Mathlib
import Submission.Work.Drive.AB.pinSetup
import Submission.Work.Drive.AB.windowDataSmall
import Submission.Work.Drive.AB.needleHalfspaceProfile
import Submission.Work.Drive.AB.chordEndNormLower
import Submission.Work.Drive.AB.needleFam_inner_eq_devAvg
import Submission.Work.Drive.AB.arcPointDeviationBound
import Submission.Work.Drive.lensConcaveInChordCoord
import Submission.Work.Drive.Generic.angVelNum_pos_of_chordConcave
import Submission.Work.Drive.AB.needleShiftedNotOnLine
import Submission.Work.Drive.interp_error_upper

/-!
# The chart of the needle's loops, as functions of the arc fraction

Auxiliary vocabulary for `Work.Drive.Generic.needleChartLoop_margin`: the `(v, e)`-coordinates of
the point at fraction `ξ` of the retained arc, relative to the needle's chart centre `chartC`, and
the derivatives of these two functions of `ξ`.
-/

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

variable {r : ℝ → Space} {d : BandArcData}

/-- The collapsed end of the band arc. -/
noncomputable def nclmRho {d : BandArcData} (D : Work.Drive.SweepData d) : ℝ := Work.Drive.taR D 0

/-- The `v`-coordinate of the point at fraction `ξ` of the retained arc, relative to `chartC`. -/
noncomputable def nclmAX (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε σ : ℝ) (v : Space) : ℝ → ℝ :=
  fun ξ => inner ℝ (Work.Drive.sweepArc' r D σ ξ - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v

/-- The `chartE`-coordinate of the point at fraction `ξ` of the retained arc, relative to
`chartC`. -/
noncomputable def nclmAH (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε σ : ℝ) (v : Space) : ℝ → ℝ :=
  fun ξ => inner ℝ (Work.Drive.sweepArc' r D σ ξ - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
    (Work.Drive.chartE r D lam δ₁ δ₂ ε v)

/-- The retained arc as a curve in the arc parameter. -/
lemma nclm_sweepArc'_eq (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d) (σ : ℝ) :
    Work.Drive.sweepArc' r D σ
      = fun s : ℝ => r (Work.Drive.taR D σ + s * Work.Drive.sweepW' D σ) := by
  funext s; rw [Work.Drive.sweepArc']

/-- The derivative of the retained arc in the arc parameter. -/
lemma nclm_hasDerivAt_arc {r : ℝ → Space} (hr : IsSmoothKnot r) (a w : ℝ) (ξ : ℝ) :
    HasDerivAt (fun s : ℝ => r (a + s * w)) (w • velocity r (a + ξ * w)) ξ := by
  have hlin : HasDerivAt (fun s : ℝ => a + s * w) w ξ := by
    simpa using ((hasDerivAt_id ξ).mul_const w).const_add a
  have hr' : HasDerivAt r (velocity r (a + ξ * w)) (a + ξ * w) :=
    ((hr.smooth.differentiable (by simp)) _).hasDerivAt
  exact hr'.scomp ξ hlin

/-- The derivative of `nclmAX`. -/
lemma nclm_deriv_nclmAX {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) (lam δ₁ δ₂ ε σ : ℝ) (v : Space) (ξ : ℝ) :
    deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ
      = Work.Drive.sweepW' D σ *
        inner ℝ (velocity r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) v := by
  have harc : HasDerivAt (Work.Drive.sweepArc' r D σ)
      (Work.Drive.sweepW' D σ • velocity r
        (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) ξ := by
    rw [nclm_sweepArc'_eq]
    exact nclm_hasDerivAt_arc hr (Work.Drive.taR D σ) (Work.Drive.sweepW' D σ) ξ
  have hvec : HasDerivAt (fun s : ℝ => Work.Drive.sweepArc' r D σ s -
      Work.Drive.chartC r D lam δ₁ δ₂ ε v)
      (Work.Drive.sweepW' D σ • velocity r
        (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) ξ :=
    harc.sub_const _
  have h := hvec.inner ℝ (hasDerivAt_const ξ v)
  change deriv (fun η : ℝ => inner ℝ (Work.Drive.sweepArc' r D σ η -
    Work.Drive.chartC r D lam δ₁ δ₂ ε v) v) ξ = _
  rw [h.deriv]
  simp only [inner_zero_right, zero_add, inner_smul_left, RCLike.conj_to_real]

/-- The derivative of `nclmAH`. -/
lemma nclm_deriv_nclmAH {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) (lam δ₁ δ₂ ε σ : ℝ) (v : Space) (ξ : ℝ) :
    deriv (nclmAH r D lam δ₁ δ₂ ε σ v) ξ
      = Work.Drive.sweepW' D σ *
        inner ℝ (velocity r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ))
          (Work.Drive.chartE r D lam δ₁ δ₂ ε v) := by
  have harc : HasDerivAt (Work.Drive.sweepArc' r D σ)
      (Work.Drive.sweepW' D σ • velocity r
        (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) ξ := by
    rw [nclm_sweepArc'_eq]
    exact nclm_hasDerivAt_arc hr (Work.Drive.taR D σ) (Work.Drive.sweepW' D σ) ξ
  have hvec : HasDerivAt (fun s : ℝ => Work.Drive.sweepArc' r D σ s -
      Work.Drive.chartC r D lam δ₁ δ₂ ε v)
      (Work.Drive.sweepW' D σ • velocity r
        (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) ξ :=
    harc.sub_const _
  have h := hvec.inner ℝ (hasDerivAt_const ξ (Work.Drive.chartE r D lam δ₁ δ₂ ε v))
  change deriv (fun η : ℝ => inner ℝ (Work.Drive.sweepArc' r D σ η -
    Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)) ξ = _
  rw [h.deriv]
  simp only [inner_zero_right, zero_add, inner_smul_left, RCLike.conj_to_real]

end Work.Drive.Generic
