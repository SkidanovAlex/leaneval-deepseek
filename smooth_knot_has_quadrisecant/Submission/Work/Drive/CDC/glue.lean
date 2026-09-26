import Mathlib
import Submission.Work.Drive.Generic.nclmData
import Submission.Work.Drive.AB.pinSetup
import Submission.Work.Drive.Generic.nclmChart
import Submission.Work.Drive.Generic.nclmBasic
import Submission.Work.Drive.Generic.nclmWindow
import Submission.Work.Drive.Generic.nclmDev
import Submission.Work.Drive.Generic.nclm_blur_close_scale
import Submission.Work.Drive.AB.windowDataSmall
import Submission.Work.Drive.AB.arcZoneWindow
import Submission.Work.Drive.AB.chordEndNormLower
import Submission.Work.Drive.H2.chartE_accel_neg
import Submission.Work.Drive.H2.baseHeight_lower
import Submission.Work.Drive.H2.basePoint_v_coord
import Submission.Work.Drive.H2.chartUp_norm_bound
import Submission.Work.Drive.H2.chordZoneClosed
import Submission.Work.Drive.lensConcaveInChordCoord
import Submission.Work.Drive.Nclm.curv_sign

/-!
# Glue lemmas for `nclm_chartDataC`

The elementary pieces of the producer `Work.Drive.Generic.nclm_chartDataC` that are not already
supplied by the `Generic`/`H2`/`Nclm` lanes: the chord-length upper bound, the small-width
threshold, the monotonicity/differentiability clauses of the arc's chart coordinates, the
chord-concavity of the profile and the two deviation bounds of the chamfer clauses.
-/

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
/-! ## Auxiliary identities for the chart coordinates

The elementary (but lengthy) bookkeeping that the proof of `nclm_chartData` consumes: the chart
centre/up-direction identities, the second derivatives of the chart coordinates of the retained arc,
the curvature condition and the concavity of the profile in the chart. -/

/-- `chartE` is a unit vector. -/
lemma cdc_nclm_chartE_norm {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    {lam δ₁ δ₂ ε : ℝ} {v : Space} (hup : Work.Drive.chartUp r D lam δ₁ δ₂ ε v ≠ 0) :
    ‖Work.Drive.chartE r D lam δ₁ δ₂ ε v‖ = 1 := by
  rw [Work.Drive.chartE]
  exact norm_smul_inv_norm hup

/-- `chartE` is orthogonal to the unit chord direction `v`. -/
lemma cdc_nclm_chartE_inner_v {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε : ℝ) {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (Work.Drive.chartE r D lam δ₁ δ₂ ε v) v = 0 := by
  rw [Work.Drive.chartE, real_inner_smul_left, Work.Drive.inner_chartUp_v r D lam δ₁ δ₂ ε hv,
    mul_zero]

/-- `chartE` is orthogonal to `v` (the other order). -/
lemma cdc_nclm_inner_v_chartE {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε : ℝ) {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ v (Work.Drive.chartE r D lam δ₁ δ₂ ε v) = 0 := by
  rw [← real_inner_comm, cdc_nclm_chartE_inner_v D lam δ₁ δ₂ ε hv]

/-- `chartE` is the normalisation of `chartUp`: their pairing is `‖chartUp‖`. -/
lemma cdc_nclm_chartUp_inner_chartE {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε : ℝ) {v : Space} (hup : Work.Drive.chartUp r D lam δ₁ δ₂ ε v ≠ 0) :
    inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
      = ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
  have h : ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ ≠ 0 := norm_ne_zero_iff.mpr hup
  rw [Work.Drive.chartE, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

/-- The chart centre relative to the chord's `a`-end. -/
lemma cdc_nclm_chartC_sub_chordEndA {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε : ℝ) {v : Space} :
    Work.Drive.chartC r D lam δ₁ δ₂ ε v - Work.Drive.chordEndA r D δ₂ ε
      = Work.Drive.nCoord r D lam δ₁ δ₂ ε v 0 • v
        + (‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2) • Work.Drive.chartE r D lam δ₁ δ₂ ε v := by
  rw [Work.Drive.chartC]; abel

/-- The `v`-coordinate of the chart centre relative to the chord's `a`-end. -/
lemma cdc_nclm_inner_chartC_v {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε : ℝ) {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (Work.Drive.chartC r D lam δ₁ δ₂ ε v - Work.Drive.chordEndA r D δ₂ ε) v
      = Work.Drive.nCoord r D lam δ₁ δ₂ ε v 0 := by
  have h2 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq v, hv]; norm_num
  rw [cdc_nclm_chartC_sub_chordEndA D lam δ₁ δ₂ ε, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, h2, cdc_nclm_chartE_inner_v D lam δ₁ δ₂ ε hv, mul_zero, add_zero, mul_one]

/-- The `chartE`-coordinate of the chart centre relative to the chord's `a`-end. -/
lemma cdc_nclm_inner_chartC_chartE {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε : ℝ) {v : Space} (hv : ‖v‖ = 1) (hup : Work.Drive.chartUp r D lam δ₁ δ₂ ε v ≠ 0) :
    inner ℝ (Work.Drive.chartC r D lam δ₁ δ₂ ε v - Work.Drive.chordEndA r D δ₂ ε)
      (Work.Drive.chartE r D lam δ₁ δ₂ ε v) = ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
  have h2 : inner ℝ (Work.Drive.chartE r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
      = 1 := by
    rw [real_inner_self_eq_norm_sq (Work.Drive.chartE r D lam δ₁ δ₂ ε v),
      show ‖Work.Drive.chartE r D lam δ₁ δ₂ ε v‖ = 1 from cdc_nclm_chartE_norm D hup]
    norm_num
  rw [cdc_nclm_chartC_sub_chordEndA D lam δ₁ δ₂ ε, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, cdc_nclm_inner_v_chartE D lam δ₁ δ₂ ε hv, mul_zero, zero_add, h2, mul_one]

/-- The base point's height above the chord's `a`-end, in the `chartE` direction. -/
lemma cdc_nclm_inner_needle_chartE {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε : ℝ) {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0 - Work.Drive.chordEndA r D δ₂ ε)
      (Work.Drive.chartE r D lam δ₁ δ₂ ε v) = ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
  have h : inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0 - Work.Drive.chordEndA r D δ₂ ε)
      (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) = ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ ^ 2 :=
    Work.Drive.inner_shiftedNeedle_chartUp r D lam δ₁ δ₂ ε hv
  have hE : Work.Drive.chartE r D lam δ₁ δ₂ ε v
      = (‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖)⁻¹ • Work.Drive.chartUp r D lam δ₁ δ₂ ε v := rfl
  rw [hE, real_inner_smul_right, h]
  rcases eq_or_ne (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) 0 with h0 | h0
  · rw [h0]; simp
  · field_simp

/-- `nclmAX` is the `v`-coordinate of the retained arc relative to the base point. -/
lemma cdc_nclm_nclmAX_eq {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε σ : ℝ) {v : Space} (hv : ‖v‖ = 1) (ξ : ℝ) :
    nclmAX r D lam δ₁ δ₂ ε σ v ξ
      = inner ℝ (Work.Drive.sweepArc' r D σ ξ - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0) v := by
  have hCN : inner ℝ (Work.Drive.chartC r D lam δ₁ δ₂ ε v
      - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0) v = 0 := by
    have h1 := cdc_nclm_inner_chartC_v (r := r) D lam δ₁ δ₂ ε (v := v) hv
    have h2 : inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0
        - Work.Drive.chordEndA r D δ₂ ε) v = Work.Drive.nCoord r D lam δ₁ δ₂ ε v 0 := rfl
    rw [show Work.Drive.chartC r D lam δ₁ δ₂ ε v - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0
        = (Work.Drive.chartC r D lam δ₁ δ₂ ε v - Work.Drive.chordEndA r D δ₂ ε)
          - (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0 - Work.Drive.chordEndA r D δ₂ ε)
        from by abel, inner_sub_left, h1, h2, sub_self]
  change inner ℝ (Work.Drive.sweepArc' r D σ ξ - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v = _
  rw [show Work.Drive.sweepArc' r D σ ξ - Work.Drive.chartC r D lam δ₁ δ₂ ε v
      = (Work.Drive.sweepArc' r D σ ξ - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0)
        - (Work.Drive.chartC r D lam δ₁ δ₂ ε v - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0)
      from by abel, inner_sub_left, hCN, sub_zero]

/-- `nclmAH` is the `chartE`-coordinate of the retained arc relative to the base point, shifted up
by half the chart height. -/
lemma cdc_nclm_nclmAH_eq {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε σ : ℝ) {v : Space} (hv : ‖v‖ = 1) (ξ : ℝ)
    (hup : Work.Drive.chartUp r D lam δ₁ δ₂ ε v ≠ 0) :
    nclmAH r D lam δ₁ δ₂ ε σ v ξ
      = inner ℝ (Work.Drive.sweepArc' r D σ ξ - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0)
          (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
        + ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
  have hCN : inner ℝ (Work.Drive.chartC r D lam δ₁ δ₂ ε v
      - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
      = -(‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2) := by
    rw [show Work.Drive.chartC r D lam δ₁ δ₂ ε v - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0
        = (Work.Drive.chartC r D lam δ₁ δ₂ ε v - Work.Drive.chordEndA r D δ₂ ε)
          - (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0 - Work.Drive.chordEndA r D δ₂ ε)
        from by abel, inner_sub_left,
      cdc_nclm_inner_chartC_chartE D lam δ₁ δ₂ ε hv hup,
      cdc_nclm_inner_needle_chartE D lam δ₁ δ₂ ε hv]
    ring
  change inner ℝ (Work.Drive.sweepArc' r D σ ξ - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
      (Work.Drive.chartE r D lam δ₁ δ₂ ε v) = _
  rw [show Work.Drive.sweepArc' r D σ ξ - Work.Drive.chartC r D lam δ₁ δ₂ ε v
      = (Work.Drive.sweepArc' r D σ ξ - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0)
        - (Work.Drive.chartC r D lam δ₁ δ₂ ε v - Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0)
      from by abel, inner_sub_left, hCN]
  ring



/-- Binet–Cauchy for the cross product (the four-argument form). -/
lemma cdc_nclm_inner_crossv_crossv (a b c d : Space) :
    inner ℝ (Work.Drive.crossv a b) (Work.Drive.crossv c d)
      = inner ℝ a c * inner ℝ b d - inner ℝ a d * inner ℝ b c := by
  simp only [Work.Drive.inner_eq_dot, Work.Drive.crossv_ofLp]
  exact cross_dot_cross a.ofLp b.ofLp c.ofLp d.ofLp

/-- The second derivative of the `v`-coordinate of the retained arc. -/
lemma cdc_nclm_deriv2_nclmAX {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) (lam δ₁ δ₂ ε σ : ℝ) (v : Space) (ξ : ℝ) :
    deriv (deriv (nclmAX r D lam δ₁ δ₂ ε σ v)) ξ
      = (Work.Drive.sweepW' D σ) ^ 2 *
          inner ℝ (deriv (deriv r) (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) v := by
  have hfun : deriv (nclmAX r D lam δ₁ δ₂ ε σ v)
      = fun s : ℝ => Work.Drive.sweepW' D σ *
          inner ℝ (velocity r (Work.Drive.taR D σ + s * Work.Drive.sweepW' D σ)) v :=
    funext (nclm_deriv_nclmAX hr D lam δ₁ δ₂ ε σ v)
  rw [hfun]
  have hvel : Differentiable ℝ (velocity r) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) := ((contDiff_infty_iff_deriv (𝕜 := ℝ)).mp h1).2
    rw [show velocity r = deriv r from rfl]
    exact h2.differentiable (by simp)
  have hlin : HasDerivAt (fun s : ℝ => Work.Drive.taR D σ + s * Work.Drive.sweepW' D σ)
      (Work.Drive.sweepW' D σ) ξ := by
    simpa using ((hasDerivAt_id ξ).mul_const (Work.Drive.sweepW' D σ)).const_add (Work.Drive.taR D σ)
  have hcomp := (hvel (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)).hasDerivAt.scomp ξ hlin
  have hinner := hcomp.inner ℝ (hasDerivAt_const ξ v)
  have h : HasDerivAt (fun s : ℝ => inner ℝ (velocity r (Work.Drive.taR D σ + s * Work.Drive.sweepW' D σ)) v)
      (Work.Drive.sweepW' D σ * inner ℝ (deriv (velocity r) (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) v) ξ := by
    simpa [real_inner_smul_left] using hinner
  have h2 := h.const_mul (Work.Drive.sweepW' D σ)
  rw [h2.deriv]
  simp only [show velocity r = deriv r from rfl]
  ring

/-- The second derivative of the `chartE`-coordinate of the retained arc. -/
lemma cdc_nclm_deriv2_nclmAH {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) (lam δ₁ δ₂ ε σ : ℝ) (v : Space) (ξ : ℝ) :
    deriv (deriv (nclmAH r D lam δ₁ δ₂ ε σ v)) ξ
      = (Work.Drive.sweepW' D σ) ^ 2 *
          inner ℝ (deriv (deriv r) (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ))
            (Work.Drive.chartE r D lam δ₁ δ₂ ε v) := by
  have hfun : deriv (nclmAH r D lam δ₁ δ₂ ε σ v)
      = fun s : ℝ => Work.Drive.sweepW' D σ *
          inner ℝ (velocity r (Work.Drive.taR D σ + s * Work.Drive.sweepW' D σ))
            (Work.Drive.chartE r D lam δ₁ δ₂ ε v) :=
    funext (nclm_deriv_nclmAH hr D lam δ₁ δ₂ ε σ v)
  rw [hfun]
  have hvel : Differentiable ℝ (velocity r) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) := ((contDiff_infty_iff_deriv (𝕜 := ℝ)).mp h1).2
    rw [show velocity r = deriv r from rfl]
    exact h2.differentiable (by simp)
  have hlin : HasDerivAt (fun s : ℝ => Work.Drive.taR D σ + s * Work.Drive.sweepW' D σ)
      (Work.Drive.sweepW' D σ) ξ := by
    simpa using ((hasDerivAt_id ξ).mul_const (Work.Drive.sweepW' D σ)).const_add (Work.Drive.taR D σ)
  have hcomp := (hvel (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)).hasDerivAt.scomp ξ hlin
  have hinner := hcomp.inner ℝ (hasDerivAt_const ξ (Work.Drive.chartE r D lam δ₁ δ₂ ε v))
  have h : HasDerivAt (fun s : ℝ => inner ℝ (velocity r (Work.Drive.taR D σ + s * Work.Drive.sweepW' D σ))
        (Work.Drive.chartE r D lam δ₁ δ₂ ε v))
      (Work.Drive.sweepW' D σ * inner ℝ (deriv (velocity r) (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ))
        (Work.Drive.chartE r D lam δ₁ δ₂ ε v)) ξ := by
    simpa [real_inner_smul_left] using hinner
  have h2 := h.const_mul (Work.Drive.sweepW' D σ)
  rw [h2.deriv]
  simp only [show velocity r = deriv r from rfl]
  ring

/-- The cross-product sign of a retained arc gives the `hcurv` condition of
`Work.Drive.lensConcaveInChordCoord` for the chart coordinates. -/
lemma cdc_nclm_curv_of_cross {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) {σ : ℝ} (hW : 0 < Work.Drive.sweepW' D σ)
    (lam δ₁ δ₂ ε : ℝ) {v : Space}
    (hcross : ∀ x : ℝ, Work.Drive.taR D σ ≤ x → x ≤ Work.Drive.tbR D σ →
      inner ℝ (Work.Drive.crossv (velocity r x) (deriv (deriv r) x))
        (Work.Drive.crossv v (Work.Drive.chartE r D lam δ₁ δ₂ ε v)) ≤ 0) :
    ∀ ξ ∈ Set.Ioo (0:ℝ) 1,
      deriv (deriv (nclmAH r D lam δ₁ δ₂ ε σ v)) ξ * deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ
        - deriv (nclmAH r D lam δ₁ δ₂ ε σ v) ξ * deriv (deriv (nclmAX r D lam δ₁ δ₂ ε σ v)) ξ
      ≤ 0 := by
  intro ξ hξ
  have hWr : Work.Drive.sweepW' D σ = Work.Drive.tbR D σ - Work.Drive.taR D σ := rfl
  have hxmem : Work.Drive.taR D σ ≤ Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ
      ∧ Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ ≤ Work.Drive.tbR D σ := by
    constructor
    · nlinarith [hW, hξ.1]
    · nlinarith [hW, hξ.2, hWr]
  have hc := hcross _ hxmem.1 hxmem.2
  rw [cdc_nclm_inner_crossv_crossv] at hc
  rw [cdc_nclm_deriv2_nclmAH hr D lam δ₁ δ₂ ε σ v ξ, cdc_nclm_deriv2_nclmAX hr D lam δ₁ δ₂ ε σ v ξ,
    nclm_deriv_nclmAX hr D lam δ₁ δ₂ ε σ v ξ, nclm_deriv_nclmAH hr D lam δ₁ δ₂ ε σ v ξ]
  have h3 : (0:ℝ) < (Work.Drive.sweepW' D σ) ^ 3 := by positivity
  nlinarith [hc, h3]

/-- The profile of the retained arc is concave in the chart's `v`-coordinate. -/
lemma cdc_nclm_chordConcave {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) (lam δ₁ δ₂ ε σ : ℝ) {v : Space}
    (hmono : StrictMonoOn (nclmAX r D lam δ₁ δ₂ ε σ v) (Set.Icc (0:ℝ) 1))
    (hxpos : ∀ ξ ∈ Set.Ioo (0:ℝ) 1, 0 < deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ)
    (hcurv : ∀ ξ ∈ Set.Ioo (0:ℝ) 1,
      deriv (deriv (nclmAH r D lam δ₁ δ₂ ε σ v)) ξ * deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ
        - deriv (nclmAH r D lam δ₁ δ₂ ε σ v) ξ * deriv (deriv (nclmAX r D lam δ₁ δ₂ ε σ v)) ξ
      ≤ 0) :
    ∀ ξ₁ ∈ Set.Icc (0:ℝ) 1, ∀ ξ₂ ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      ∀ ξ ∈ Set.Icc (0:ℝ) 1,
        nclmAX r D lam δ₁ δ₂ ε σ v ξ = t * nclmAX r D lam δ₁ δ₂ ε σ v ξ₁
          + (1 - t) * nclmAX r D lam δ₁ δ₂ ε σ v ξ₂ →
        t * nclmAH r D lam δ₁ δ₂ ε σ v ξ₁ + (1 - t) * nclmAH r D lam δ₁ δ₂ ε σ v ξ₂
          ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ := by
  have haff : ContDiff ℝ ⊤ (fun ξ : ℝ => Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ) :=
    contDiff_const.add (contDiff_id.mul contDiff_const)
  have hsm : ContDiff ℝ ⊤ (fun ξ : ℝ => r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) :=
    hr.smooth.comp haff
  have hXinf : ContDiff ℝ ⊤ (nclmAX r D lam δ₁ δ₂ ε σ v) :=
    ContDiff.inner ℝ (hsm.sub contDiff_const) contDiff_const
  have hHinf : ContDiff ℝ ⊤ (nclmAH r D lam δ₁ δ₂ ε σ v) :=
    ContDiff.inner ℝ (hsm.sub contDiff_const) contDiff_const
  exact Work.Drive.lensConcaveInChordCoord hmono (hXinf.of_le le_top).contDiffOn
    (hHinf.of_le le_top).contDiffOn hxpos hcurv



/-! ## Min-extraction helpers -/

lemma cdc_le_left {a b c : ℝ} (h : a ≤ min b c) : a ≤ b := le_trans h (min_le_left b c)
lemma cdc_le_right {a b c : ℝ} (h : a ≤ min b c) : a ≤ c := le_trans h (min_le_right b c)
lemma cdc_lt_left {a b c : ℝ} (h : a < min b c) : a < b := lt_of_lt_of_le h (min_le_left b c)
lemma cdc_lt_right {a b c : ℝ} (h : a < min b c) : a < c := lt_of_lt_of_le h (min_le_right b c)

/-! ## The chord-length upper bound -/

/-- **An upper bound for the needle's chord length.**  The blurred chord is the bump-average of the
loops' chords, each of which is at most `M * W(σ) ≤ 2 M W(ε)` by the Lipschitz bound `M` of the
knot and the window comparison. -/
theorem cdc_ell_upper {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) :
    ∃ Cℓ : ℝ, 0 < Cℓ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ Λ : ℝ, 0 < Λ ∧ Λ ≤ ε / 2 ∧ ∀ δ₂ : ℝ, 0 < δ₂ → δ₂ ≤ Λ →
        ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖
          ≤ Cℓ * Work.Drive.sweepW' D ε := by
  obtain ⟨M, hM0, hM⟩ := Work.Drive.exists_knot_lipschitz hr
  refine ⟨2 * M, by positivity, ?_⟩
  intro ε hε0 hε12
  have hε1 : ε < 1 := by linarith
  obtain ⟨Λw, hΛw0, hWin⟩ := Work.Drive.Generic.nclm_window_eps D hε0 hε1
  refine ⟨min Λw (ε / 2), lt_min hΛw0 (by linarith), min_le_right _ _, ?_⟩
  intro δ₂ hδ₂ hδ₂Λ
  have hδ₂w : δ₂ ≤ Λw := le_trans hδ₂Λ (min_le_left _ _)
  have hδ₂ε : δ₂ ≤ ε / 2 := le_trans hδ₂Λ (min_le_right _ _)
  have hwσ : ∀ v : ℝ, v ∈ Set.Icc (-1 : ℝ) 1 →
      0 < Work.Drive.sweepW' D (ε - δ₂ * v) ∧
      Work.Drive.sweepW' D (ε - δ₂ * v) ≤ 2 * Work.Drive.sweepW' D ε := by
    intro v hv
    have h1 : ε - δ₂ ≤ ε - δ₂ * v := by nlinarith [hδ₂, hv.2]
    have h2 : ε - δ₂ * v ≤ ε + δ₂ := by nlinarith [hδ₂, hv.1]
    have hWε : 0 < Work.Drive.sweepW' D ε := Work.Drive.wds_sweepW'_pos D hε0 hε1
    have hwin := hWin δ₂ (ε - δ₂ * v) hδ₂ hδ₂w hδ₂ε h1 h2
    exact ⟨lt_of_lt_of_le (by linarith) hwin.1, hwin.2.1⟩
  rw [Work.Drive.chordEndB_sub_chordEndA r D hr.smooth.continuous δ₂ ε]
  have hcont : Continuous fun v : ℝ =>
      r (Work.Drive.tbR D (ε - δ₂ * v)) - r (Work.Drive.taR D (ε - δ₂ * v)) :=
    (hr.smooth.continuous.comp ((Work.Drive.continuous_tbR D).comp (by fun_prop))).sub
      (hr.smooth.continuous.comp ((Work.Drive.continuous_taR D).comp (by fun_prop)))
  calc ‖∫ v in (-1 : ℝ)..1,
        Work.Drive.sweepBump v • (r (Work.Drive.tbR D (ε - δ₂ * v)) - r (Work.Drive.taR D (ε - δ₂ * v)))‖
      ≤ ∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v * (2 * M * Work.Drive.sweepW' D ε) := by
        refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num)) ?_
        rw [show (fun v : ℝ => ‖Work.Drive.sweepBump v •
              (r (Work.Drive.tbR D (ε - δ₂ * v)) - r (Work.Drive.taR D (ε - δ₂ * v)))‖)
            = (fun v : ℝ => Work.Drive.sweepBump v *
              ‖r (Work.Drive.tbR D (ε - δ₂ * v)) - r (Work.Drive.taR D (ε - δ₂ * v))‖) from by
          funext v; rw [norm_smul, Real.norm_of_nonneg (Work.Drive.sweepBump_nonneg v)]]
        refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
        · exact (Work.Drive.sweepBump_continuous.mul hcont.norm).intervalIntegrable _ _
        · exact (Work.Drive.sweepBump_continuous.mul continuous_const).intervalIntegrable _ _
        · intro v hv
          obtain ⟨hwv, hwv2⟩ := hwσ v hv
          have hbdd : ‖r (Work.Drive.tbR D (ε - δ₂ * v)) - r (Work.Drive.taR D (ε - δ₂ * v))‖
              ≤ 2 * M * Work.Drive.sweepW' D ε := by
            have hs : Work.Drive.sweepW' D (ε - δ₂ * v)
                = Work.Drive.tbR D (ε - δ₂ * v) - Work.Drive.taR D (ε - δ₂ * v) := rfl
            have h1 := hM (Work.Drive.tbR D (ε - δ₂ * v)) (Work.Drive.taR D (ε - δ₂ * v))
            rw [abs_of_nonneg (by simpa only [Work.Drive.sweepW'] using hwv.le)] at h1
            nlinarith [h1, hwv2, hM0, hs]
          exact mul_le_mul_of_nonneg_left hbdd (Work.Drive.sweepBump_nonneg v)
    _ = 2 * M * Work.Drive.sweepW' D ε := by
        rw [intervalIntegral.integral_mul_const, Work.Drive.integral_sweepBump, one_mul]

/-! ## A small-width threshold -/

/-- **The retained width tends to `0` at the collapsed end**: for every `c₀ > 0` there is `ε₀ > 0`
with `sweepW' D ε ≤ c₀` for `ε ∈ (0, ε₀]`. -/
theorem cdc_window_small {d : BandArcData} (D : Work.Drive.SweepData d) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → Work.Drive.sweepW' D ε ≤ c₀ := by
  have hcont : Continuous (Work.Drive.sweepW' D) := Work.Drive.arcWin_sweepW'_continuous D
  have h0 : Work.Drive.sweepW' D 0 = 0 := Work.Drive.sweepW'_zero D
  obtain ⟨δ, hδ, hspec⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := 0)) c₀ hc₀
  refine ⟨min δ 1 / 2, by positivity, ?_⟩
  intro ε hε0 hεδ
  have hd : dist (Work.Drive.sweepW' D ε) (Work.Drive.sweepW' D 0) < c₀ := by
    refine hspec ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hε0.le]
    have h2 : min δ 1 ≤ δ := min_le_left δ 1
    linarith
  rw [h0, Real.dist_eq, sub_zero] at hd
  exact le_of_lt (lt_of_abs_lt hd)

/-! ## The differentiability of the ordinate -/

/-- `nclmAH` is differentiable at every point. -/
lemma cdc_diff_H {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) (lam δ₁ δ₂ ε σ : ℝ) (v : Space) (ξ : ℝ) :
    DifferentiableAt ℝ (nclmAH r D lam δ₁ δ₂ ε σ v) ξ := by
  have harc : HasDerivAt (fun s : ℝ => r (Work.Drive.taR D σ + s * Work.Drive.sweepW' D σ))
      (Work.Drive.sweepW' D σ • velocity r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) ξ :=
    Work.Drive.Generic.nclm_hasDerivAt_arc hr (Work.Drive.taR D σ) (Work.Drive.sweepW' D σ) ξ
  have h := (harc.sub_const (Work.Drive.chartC r D lam δ₁ δ₂ ε v)).inner ℝ
    (hasDerivAt_const ξ (Work.Drive.chartE r D lam δ₁ δ₂ ε v))
  show DifferentiableAt ℝ (fun η : ℝ => inner ℝ
      (Work.Drive.sweepArc' r D σ η - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
      (Work.Drive.chartE r D lam δ₁ δ₂ ε v)) ξ
  rw [Work.Drive.Generic.nclm_sweepArc'_eq]
  exact h.differentiableAt

/-! ## The monotonicity and differentiability clauses of the arc's chart coordinates -/

/-- **Clauses 12-15 of the chart data**: the abscissa `nclmAX` is strictly increasing on `[0,1]`,
its derivative is positive on `(0,1)` and at least `m * sweepW' D σ / 8` on `(lam, 1-lam)`, and the
ordinate `nclmAH` is differentiable.  Everything is read off the tangent pairing `m / 4 ≤
⟪velocity r x, v⟫` on the retained arcs and `nclm_deriv_nclmAX`. -/
theorem cdc_arc_mono {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) {lam δ₁ δ₂ ε m : ℝ} {v : Space}
    (hm : 0 < m) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (htan : ∀ (σ x : ℝ), ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ) →
      m / 4 ≤ inner ℝ (velocity r x) v)
    (hW : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → 0 < Work.Drive.sweepW' D σ) :
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      StrictMonoOn (nclmAX r D lam δ₁ δ₂ ε σ v) (Set.Icc (0 : ℝ) 1)) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Ioo (0 : ℝ) 1,
      0 < deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Ioo lam (1 - lam),
      m * Work.Drive.sweepW' D σ / 8 ≤ deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (nclmAH r D lam δ₁ δ₂ ε σ v) ξ) := by
  have hmem : ∀ (σ : ℝ), ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
      Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ
        ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ) := by
    intro σ h1 h2 ξ hξ
    have hw := hW σ h1 h2
    have hw' : 0 < Work.Drive.tbR D σ - Work.Drive.taR D σ := by
      simpa only [Work.Drive.sweepW'] using hw
    have hs : Work.Drive.sweepW' D σ = Work.Drive.tbR D σ - Work.Drive.taR D σ := rfl
    constructor
    · nlinarith [hξ.1, hw', hw, hs]
    · nlinarith [hξ.2, hw', hw, hs]
  have hx13 : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Ioo (0 : ℝ) 1,
      0 < deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ := by
    intro σ h1 h2 ξ hξ
    rw [Work.Drive.Generic.nclm_deriv_nclmAX hr]
    have hxmem := hmem σ h1 h2 ξ ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
    have h := htan σ (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ) h1 h2 hxmem
    have hw := hW σ h1 h2
    nlinarith [h, hm, hw]
  refine ⟨?_, hx13, ?_, ?_⟩
  · intro σ h1 h2
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) ?_ ?_
    · refine Continuous.continuousOn ?_
      show Continuous fun ξ : ℝ => inner ℝ
        (Work.Drive.sweepArc' r D σ ξ - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v
      rw [Work.Drive.Generic.nclm_sweepArc'_eq]
      exact (((hr.smooth.continuous.comp
        (continuous_const.add (continuous_id.mul continuous_const))).sub
          continuous_const).inner continuous_const)
    · intro x hx
      rw [interior_Icc] at hx
      exact hx13 σ h1 h2 x hx
  · intro σ h1 h2 ξ hξ
    rw [Work.Drive.Generic.nclm_deriv_nclmAX hr]
    have hxmem := hmem σ h1 h2 ξ ⟨le_trans hlam0 hξ.1.le, le_trans hξ.2.le (by linarith)⟩
    have h := htan σ (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ) h1 h2 hxmem
    have hw := hW σ h1 h2
    nlinarith [h, hm, hw]
  · intro σ h1 h2 ξ hξ
    exact cdc_diff_H hr D lam δ₁ δ₂ ε σ v ξ

/-! ## The chord-concavity of the profile -/

/-- **Clause 16 of the chart data**: `nclmAH` is concave in the chord coordinate `nclmAX`.  It is
`cdc_nclm_chordConcave` fed with the curvature sign `cdc_nclm_curv_of_cross`. -/
theorem cdc_arc_concave {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) {lam δ₁ δ₂ ε σ : ℝ} {v : Space}
    (hW : 0 < Work.Drive.sweepW' D σ)
    (hmono : StrictMonoOn (nclmAX r D lam δ₁ δ₂ ε σ v) (Set.Icc (0 : ℝ) 1))
    (hxpos : ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, 0 < deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ)
    (hcross : ∀ x : ℝ, Work.Drive.taR D σ ≤ x → x ≤ Work.Drive.tbR D σ →
      inner ℝ (Work.Drive.crossv (velocity r x) (deriv (deriv r) x))
        (Work.Drive.crossv v (Work.Drive.chartE r D lam δ₁ δ₂ ε v)) ≤ 0) :
    ∀ ξ₁ ∈ Set.Icc (0 : ℝ) 1, ∀ ξ₂ ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
        nclmAX r D lam δ₁ δ₂ ε σ v ξ
            = t * nclmAX r D lam δ₁ δ₂ ε σ v ξ₁
              + (1 - t) * nclmAX r D lam δ₁ δ₂ ε σ v ξ₂ →
        t * nclmAH r D lam δ₁ δ₂ ε σ v ξ₁
            + (1 - t) * nclmAH r D lam δ₁ δ₂ ε σ v ξ₂
          ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ :=
  cdc_nclm_chordConcave hr D lam δ₁ δ₂ ε σ hmono hxpos
    (cdc_nclm_curv_of_cross hr D hW lam δ₁ δ₂ ε hcross)

/-! ## The deviation clauses of the chamfers -/

/-- **Clause 20 of the chart data**: the four pairings of the loops' deviations at the chamfer
fractions `ξ = lam`, `1 - lam`.  The two inequalities on `chartE` are the *signed* deviation bound
`Work.Drive.Generic.nclm_dev_scalar_ge` with the acceleration hypothesis `⟪r'', chartE⟫ ≤ -cE`; the
two absolute bounds on `v` are `Work.Drive.Generic.nclm_dev_scalar_le` with the global bound `K` of
`‖r''‖` (so `cK := K`).  Note `ξ (1 - ξ) = lam (1 - lam)` at both fractions. -/
theorem cdc_dev {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) {lam δ₁ δ₂ ε σ cE K : ℝ} {v : Space}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hW : 0 < Work.Drive.sweepW' D σ)
    (hacc : ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
      inner ℝ (deriv (deriv r) x) (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ≤ -cE)
    (haccK : ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
      |inner ℝ (deriv (deriv r) x) v| ≤ K) :
    lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * cE
        ≤ inner ℝ (Work.Drive.loopDev r D σ (1 - lam))
          (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ∧
      lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * cE
        ≤ inner ℝ (Work.Drive.loopDev r D σ lam)
          (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ∧
      |inner ℝ (Work.Drive.loopDev r D σ (1 - lam)) v|
        ≤ lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * K ∧
      |inner ℝ (Work.Drive.loopDev r D σ lam) v|
        ≤ lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * K := by
  have hm1 : (1 - lam) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hm2 : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨hlam0, hlam1⟩
  have h1 := Work.Drive.Generic.nclm_dev_scalar_ge (D := D) (r := r) hr
    (y := Work.Drive.chartE r D lam δ₁ δ₂ ε v) (c := cE) (σ := σ) (ξ := 1 - lam) hW hm1 hacc
  have h2 := Work.Drive.Generic.nclm_dev_scalar_ge (D := D) (r := r) hr
    (y := Work.Drive.chartE r D lam δ₁ δ₂ ε v) (c := cE) (σ := σ) (ξ := lam) hW hm2 hacc
  have h3 := Work.Drive.Generic.nclm_dev_scalar_le (D := D) (r := r) hr (y := v)
    (B := K) (σ := σ) (ξ := 1 - lam) hW hm1 haccK
  have h4 := Work.Drive.Generic.nclm_dev_scalar_le (D := D) (r := r) hr (y := v)
    (B := K) (σ := σ) (ξ := lam) hW hm2 haccK
  have e1 : (1 - lam) * (1 - (1 - lam)) / 2 = lam * (1 - lam) / 2 := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1] at h1; exact h1
  · exact h2
  · rw [e1] at h3; exact h3
  · exact h4

/-! ## The final smallness bookkeeping -/

/-- **Clause 21 of the chart data**: the smallness `4 (h/2) cK ≤ ℓ cE / 8`, from `h ≤ 2 Ch W²`,
`cℓ W ≤ ℓ` and `W ≤ cℓ cE / (32 Ch cK)`. -/
theorem cdc_final_arith {h ℓ W cℓ Ch cE cK : ℝ}
    (hW : 0 < W) (hcℓ : 0 < cℓ) (hCh : 0 < Ch) (hcE : 0 < cE) (hcK : 0 < cK)
    (hh : h ≤ 2 * Ch * W ^ 2) (hℓ : cℓ * W ≤ ℓ)
    (hsmall : W ≤ cℓ * cE / (32 * Ch * cK)) :
    4 * (h / 2) * cK ≤ ℓ * cE / 8 := by
  have hd : 0 < 32 * Ch * cK := by positivity
  rw [le_div_iff₀ hd] at hsmall
  have h2 : cℓ * W * cE ≤ ℓ * cE := mul_le_mul_of_nonneg_right hℓ hcE.le
  nlinarith [hh, hsmall, h2, hcℓ, hcE, hcK, hCh, hW]

end Work.Drive.Generic
