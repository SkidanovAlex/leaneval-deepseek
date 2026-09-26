import Mathlib
import Submission.Work.Drive.AB.pinSetup
import Submission.Work.Drive.AB.windowDataSmall
import Submission.Work.Drive.H2.chamfer_pos_data
import Submission.Work.Drive.H2.chordZoneClosed
import Submission.Work.Drive.H2.basePoint_v_coord
import Submission.Work.Drive.H2.chartUp_norm_bound
import Submission.Work.Drive.H2.baseHeight_lower
import Submission.Work.Drive.Generic.nclmWindow
import Submission.Work.Drive.Generic.nclm_blur_close_scale
import Submission.Work.Drive.Generic.nclmDev

namespace Work.Drive.CDC

set_option maxHeartbeats 4000000

open LeanEval.KnotTheory.Quadrisecant

variable {r : ℝ → Space} {d : BandArcData} {D : SweepData d}

/-! ## The chart coordinates of the arc and chord points in the `(v, chartE)` frame -/

/-- The `v`-pairing of the *chord* point at fraction `ξ`, relative to the chart centre. -/
lemma sweepChord'_sub_chartC_inner_v {lam δ₁ δ₂ ε σ ξ : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (sweepChord' r D σ ξ - chartC r D lam δ₁ δ₂ ε v) v
      = (1 - ξ) * inner ℝ (r (taR D σ) - chordEndA r D δ₂ ε) v
        + ξ * inner ℝ (r (tbR D σ) - chordEndB r D δ₂ ε) v
        + ξ * inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) v
        - nCoord r D lam δ₁ δ₂ ε v 0 := by
  have hv1 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hve : inner ℝ (chartE r D lam δ₁ δ₂ ε v) v = 0 := H2.chartE_inner_v hv
  rw [sweepChord', chartC]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hv1, hve, mul_one, mul_zero]
  ring

/-- The `chartE`-pairing of the *chord* point at fraction `ξ`, relative to the chart centre. -/
lemma sweepChord'_sub_chartC_inner_e {lam δ₁ δ₂ ε σ ξ : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (sweepChord' r D σ ξ - chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v)
      = (1 - ξ) * inner ℝ (r (taR D σ) - chordEndA r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v)
        + ξ * inner ℝ (r (tbR D σ) - chordEndB r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v)
        + ξ * inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v)
        - (‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) * ‖chartE r D lam δ₁ δ₂ ε v‖ ^ 2 := by
  have hve : inner ℝ v (chartE r D lam δ₁ δ₂ ε v) = 0 := by
    rw [real_inner_comm]; exact H2.chartE_inner_v (r := r) (D := D) hv
  rw [sweepChord', chartC]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hve, mul_zero,
    real_inner_self_eq_norm_sq]
  ring

/-- The `v`-pairing of the *arc* point at fraction `ξ`, relative to the chart centre. -/
lemma sweepArc'_sub_chartC_inner_v {lam δ₁ δ₂ ε σ ξ : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (sweepArc' r D σ ξ - chartC r D lam δ₁ δ₂ ε v) v
      = inner ℝ (loopDev r D σ ξ) v
        + (1 - ξ) * inner ℝ (r (taR D σ) - chordEndA r D δ₂ ε) v
        + ξ * inner ℝ (r (tbR D σ) - chordEndB r D δ₂ ε) v
        + ξ * inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) v
        - nCoord r D lam δ₁ δ₂ ε v 0 := by
  have hsplit : sweepArc' r D σ ξ - chartC r D lam δ₁ δ₂ ε v
      = loopDev r D σ ξ + (sweepChord' r D σ ξ - chartC r D lam δ₁ δ₂ ε v) := by
    rw [loopDev, sweepArc', sweepChord']; abel
  rw [hsplit, inner_add_left, sweepChord'_sub_chartC_inner_v (r := r) (D := D) (σ := σ) hv]
  ring

/-- The two endpoint pairings with `chartE`, against the chord ends. -/
lemma inner_taR_sub_chartC_chartE {lam δ₁ δ₂ ε σ : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (r (taR D σ) - chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v)
      = inner ℝ (r (taR D σ) - chordEndA r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v)
        - (‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) * ‖chartE r D lam δ₁ δ₂ ε v‖ ^ 2 := by
  have hve : inner ℝ v (chartE r D lam δ₁ δ₂ ε v) = 0 := by
    rw [real_inner_comm]; exact H2.chartE_inner_v (r := r) (D := D) hv
  rw [chartC]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hve, mul_zero,
    real_inner_self_eq_norm_sq]
  ring

lemma inner_tbR_sub_chartC_chartE {lam δ₁ δ₂ ε σ : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (r (tbR D σ) - chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v)
      = inner ℝ (r (tbR D σ) - chordEndB r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v)
        + inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v)
        - (‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) * ‖chartE r D lam δ₁ δ₂ ε v‖ ^ 2 := by
  have hve : inner ℝ v (chartE r D lam δ₁ δ₂ ε v) = 0 := by
    rw [real_inner_comm]; exact H2.chartE_inner_v (r := r) (D := D) hv
  rw [chartC]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hve, mul_zero,
    real_inner_self_eq_norm_sq]
  ring

/-- The endpoint pairings with `v`. -/
lemma inner_taR_sub_chartC_v {lam δ₁ δ₂ ε σ : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (r (taR D σ) - chartC r D lam δ₁ δ₂ ε v) v
      = inner ℝ (r (taR D σ) - chordEndA r D δ₂ ε) v - nCoord r D lam δ₁ δ₂ ε v 0 := by
  have hv1 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hve : inner ℝ (chartE r D lam δ₁ δ₂ ε v) v = 0 := H2.chartE_inner_v hv
  rw [chartC]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hv1, hve, mul_one, mul_zero]
  ring

lemma inner_tbR_sub_chartC_v {lam δ₁ δ₂ ε σ : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (r (tbR D σ) - chartC r D lam δ₁ δ₂ ε v) v
      = inner ℝ (r (tbR D σ) - chordEndB r D δ₂ ε) v
        + inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) v
        - nCoord r D lam δ₁ δ₂ ε v 0 := by
  have hv1 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hve : inner ℝ (chartE r D lam δ₁ δ₂ ε v) v = 0 := H2.chartE_inner_v hv
  rw [chartC]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hv1, hve, mul_one, mul_zero]
  ring

/-- **The chart positions of the arc's ends and of the chord** (the twelve `hend`-clauses of
`Work.Drive.Generic.nclmDataC`).  Route: `Work.Drive.Generic.nclm_blur_close_scale` (a small `c`)
gives the endpoint and loop-chord closeness at scale `c * W ^ 2`, `H2.basePoint_v_coord` the
clause `nCoord (0) = ℓ/2 ± W^2 K/2`, `H2.chartUp_norm_bound` the bound `‖chartUp‖ ≤ W^2 K`, and
`H2.sweep_chart_bounds` the two chart coordinates of the retained arc and of its chord at fraction
`ξ ∈ [0,1]` with error `2 W^2 K`, where `K` is a global bound of `‖r''‖` from
`H2.H2_accel_bound`.  All the remaining work is arithmetic, with `ε₀` chosen so that
`W^2 K` is small against `ℓ` (which is `≥ cℓ * W`) and against `h = ‖chartUp‖` (which is
`≥ c * W^2` by `H2.baseHeight_lower`); the clauses `(k)`, `(l)` must NOT be read off
`sweep_chart_bounds` alone (its error `2 W^2 K` may exceed `h`) but from the convex-combination
form `sweepChord' σ ξ = (1-ξ) • r (taR σ) + ξ • r (tbR σ)` together with the endpoint clauses
`(e)`, `(f)` and their two-sided ("`≥ -h/2 - c W^2`") versions. -/
theorem cdc_endpointChart {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space} (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ Λ : ℝ, 0 < Λ ∧ Λ ≤ ε / 2 ∧
        ∀ lam δ₁ δ₂ : ℝ, 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
          0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ v : LeanEval.KnotTheory.Quadrisecant.Space, ‖v‖ = 1 →
          Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
        ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4
              ≤ Work.Drive.Generic.nclmAX r D lam δ₁ δ₂ ε σ v (1 - lam)
            ∧ Work.Drive.Generic.nclmAX r D lam δ₁ δ₂ ε σ v lam
              ≤ -(‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4)
            ∧ |inner ℝ (r (Work.Drive.taR D σ) - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v|
              ≤ 3 * ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4
            ∧ |inner ℝ (r (Work.Drive.tbR D σ) - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v|
              ≤ 3 * ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4
            ∧ inner ℝ (r (Work.Drive.taR D σ) - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
              ≤ -(‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 4)
            ∧ inner ℝ (r (Work.Drive.tbR D σ) - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
              ≤ -(‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 4)
            ∧ 3 * ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4
              ≤ inner ℝ (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)) v
            ∧ |inner ℝ (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ))
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
              ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 16
            ∧ inner ℝ (Work.Drive.sweepChord' r D σ lam
                  - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v
              ≤ -(‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4)
            ∧ ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4
              ≤ inner ℝ (Work.Drive.sweepChord' r D σ (1 - lam)
                  - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v
            ∧ |inner ℝ (Work.Drive.sweepChord' r D σ lam
                  - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
              ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖
            ∧ |inner ℝ (Work.Drive.sweepChord' r D σ (1 - lam)
                  - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
              ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
  obtain ⟨K, hK1, hKb⟩ := H2.H2_accel_bound (r := r) hr
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  obtain ⟨εc, hεc0, hεc1, cL, hcL0, hcL⟩ := H2.chordLen_lower (r := r) (D := D) hr
  obtain ⟨cφ, hcφ0, εφ, hεφ0, hεφ1, hbh⟩ := H2.baseHeight_lower (r := r) (D := D) hr hinfl
  obtain ⟨εG, hεG0, hεG⟩ :=
    Generic.nclm_blur_close_scale (r := r) (D := D) hr (cφ / 16) (by positivity)
  obtain ⟨εT, hεT0, hεT1, hεT⟩ := windowDataSmall (r := r) hr D
    (min (cL / (128 * K)) (cL / (16 * cφ))) (lt_min (by positivity) (by positivity))
  refine ⟨min (min (min εc εφ) (min εG εT)) (1 / 4), ?_, ?_, ?_⟩
  · exact lt_min (lt_min (lt_min hεc0 hεφ0) (lt_min hεG0 hεT0)) (by norm_num)
  · exact le_trans (min_le_right _ _) (by norm_num)
  · intro ε hε0 hεle
    have hεc' : ε ≤ εc :=
      le_trans hεle (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
    have hεφ' : ε ≤ εφ :=
      le_trans hεle (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
    have hεG' : ε ≤ εG :=
      le_trans hεle (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hεT' : ε ≤ εT :=
      le_trans hεle (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hε14 : ε ≤ 1 / 4 := le_trans hεle (min_le_right _ _)
    have hε12' : ε ≤ 1 / 2 := by linarith
    have hε1 : ε < 1 := by linarith
    set W : ℝ := sweepW' D ε with hWdef
    have hWpos : 0 < W := by rw [hWdef]; exact wds_sweepW'_pos D hε0 hε1
    set τ : ℝ := (cφ / 16) * W ^ 2 with hτdef
    have hτ0 : 0 ≤ τ := by rw [hτdef]; positivity
    -- the two-sided smallness of the blurred data
    obtain ⟨Λc, hΛc0, hΛcle, hΛc⟩ := hcL ε hε0 hεc'
    obtain ⟨Λφ, hΛφ0, hΛφ12, hΛφ⟩ := hbh ε hε0 hεφ'
    obtain ⟨Λg, hΛg0, hΛg⟩ := hεG ε hε0 hεG'
    obtain ⟨Λw, hΛw0, hΛw⟩ := Generic.nclm_window_eps (D := D) hε0 hε1
    set Λ : ℝ := min (min (ε / 2) (1 / 8)) (min Λc (min Λφ (min Λg Λw))) with hΛdef
    have hΛpos : 0 < Λ := by
      rw [hΛdef]
      exact lt_min (lt_min (by linarith) (by norm_num))
        (lt_min hΛc0 (lt_min hΛφ0 (lt_min hΛg0 hΛw0)))
    have hΛε2 : Λ ≤ ε / 2 := by
      rw [hΛdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hΛ18 : Λ ≤ 1 / 8 := by
      rw [hΛdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hΛΛc : Λ ≤ Λc := by
      rw [hΛdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hΛΛφ : Λ ≤ Λφ := by
      rw [hΛdef]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hΛΛg : Λ ≤ Λg := by
      rw [hΛdef]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hΛΛw : Λ ≤ Λw := by
      rw [hΛdef]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    refine ⟨Λ, hΛpos, hΛε2, ?_⟩
    intro lam δ₁ δ₂ hlam0 hlamΛ hlam12 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε
    have hlam18 : lam ≤ 1 / 8 := le_trans hlamΛ hΛ18
    have hlam4 : lam ≤ 1 / 4 := by linarith
    have hδ₁4 : δ₁ ≤ period / 4 := by
      have hp : period = 2 * Real.pi := rfl
      have h18 : (1 : ℝ) / 8 ≤ period / 4 := by rw [hp]; linarith [Real.pi_gt_three]
      exact le_trans (le_trans hδ₁Λ hΛ18) h18
    intro v hv hvC
    set ℓ : ℝ := ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ with hℓdef
    intro σ hσlo hσhi
    -- the window data at σ
    have hδ₂Λw : δ₂ ≤ Λw := le_trans hδ₂Λ hΛΛw
    have hWσpos : 0 < sweepW' D σ :=
      Generic.nclm_window_wpos D hδ₂0 hδ₂ε hε0 hε12' hσlo hσhi
    have hWσ2 : sweepW' D σ ≤ 2 * W :=
      (hΛw δ₂ σ hδ₂0 hδ₂Λw hδ₂ε hσlo hσhi).2.1
    have hWσfun : ∀ σ' : ℝ, ε - δ₂ ≤ σ' → σ' ≤ ε + δ₂ → sweepW' D σ' ≤ 2 * W :=
      fun σ' h1 h2 => (hΛw δ₂ σ' hδ₂0 hδ₂Λw hδ₂ε h1 h2).2.1
    -- smallness of `W`
    have hWsmall : W ≤ 2 * min (cL / (128 * K)) (cL / (16 * cφ)) := by
      obtain ⟨hd, -, -⟩ := hεT (ε / 2) ε (by linarith) le_rfl hε0 hεT'
      have h0 := hd ε (by linarith) (by linarith) 0 (by norm_num) (by norm_num)
      have h1 := hd ε (by linarith) (by linarith) 1 (by norm_num) (by norm_num)
      simp only [zero_mul, one_mul, add_zero] at h0 h1
      have htb : taR D ε + sweepW' D ε = tbR D ε := by rw [sweepW']; ring
      rw [htb] at h1
      have hkey : W = (tbR D ε - taR D 0) - (taR D ε - taR D 0) := by rw [hWdef, sweepW']; ring
      rw [hkey]
      linarith [(abs_le.mp h0).1, (abs_le.mp h1).2]
    have hW128 : 128 * K * min (cL / (128 * K)) (cL / (16 * cφ)) ≤ cL := by
      have h2 : min (cL / (128 * K)) (cL / (16 * cφ)) ≤ cL / (128 * K) := min_le_left _ _
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 128 * K)
      rwa [mul_div_cancel₀ cL (by positivity : (128 : ℝ) * K ≠ 0)] at h3
    have hW64 : 64 * K * W ≤ cL := by
      have h4 : 64 * K * W ≤ 64 * K * (2 * min (cL / (128 * K)) (cL / (16 * cφ))) :=
        mul_le_mul_of_nonneg_left hWsmall (by positivity)
      have h5 : 64 * K * (2 * min (cL / (128 * K)) (cL / (16 * cφ)))
          = 128 * K * min (cL / (128 * K)) (cL / (16 * cφ)) := by ring
      linarith [h4, h5, hW128]
    have hWcφ16 : 16 * cφ * min (cL / (128 * K)) (cL / (16 * cφ)) ≤ cL := by
      have h2 : min (cL / (128 * K)) (cL / (16 * cφ)) ≤ cL / (16 * cφ) := min_le_right _ _
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 16 * cφ)
      rwa [mul_div_cancel₀ cL (by positivity : (16 : ℝ) * cφ ≠ 0)] at h3
    have hη0 : 0 ≤ min (cL / (128 * K)) (cL / (16 * cφ)) :=
      le_of_lt (lt_min (by positivity) (by positivity))
    have hW4cφ : 4 * cφ * W ≤ cL := by
      have h4 : 4 * cφ * W ≤ 4 * cφ * (2 * min (cL / (128 * K)) (cL / (16 * cφ))) :=
        mul_le_mul_of_nonneg_left hWsmall (by positivity)
      have h5 : 4 * cφ * (2 * min (cL / (128 * K)) (cL / (16 * cφ)))
          = 8 * cφ * min (cL / (128 * K)) (cL / (16 * cφ)) := by ring
      have h6 : 8 * cφ * min (cL / (128 * K)) (cL / (16 * cφ))
          ≤ 16 * cφ * min (cL / (128 * K)) (cL / (16 * cφ)) := by nlinarith [hη0, hcφ0]
      linarith [h4, h5, h6, hWcφ16]
    -- the length of the needle's chord
    have hℓlow : cL * W ≤ ℓ := hΛc δ₂ hδ₂0 (le_trans hδ₂Λ hΛΛc)
    have hℓ0 : 0 ≤ ℓ := le_trans (mul_nonneg hcL0.le hWpos.le) hℓlow
    have hℓge : 32 * K * W ^ 2 ≤ ℓ := by
      have h2 : 32 * K * W ≤ cL := by linarith [hW64]
      have h3 : 32 * K * W ^ 2 = (32 * K * W) * W := by ring
      have h4 := mul_le_mul_of_nonneg_right h2 hWpos.le
      linarith [h4, h3, hℓlow]
    have hℓpos : 0 < ℓ := by
      have hWsq : 0 < W ^ 2 := pow_pos hWpos 2
      nlinarith [hℓge, hWsq, hK0]
    have hW2K : W ^ 2 * K ≤ ℓ / 32 := by nlinarith [hℓge]
    have hτℓ : τ ≤ ℓ / 64 := by
      have hkey : 4 * cφ * W ^ 2 ≤ cL * W := by
        have h := mul_le_mul_of_nonneg_right hW4cφ hWpos.le
        rwa [show 4 * cφ * W * W = 4 * cφ * W ^ 2 from by ring] at h
      have h3 : 4 * cφ * W ^ 2 ≤ ℓ := le_trans hkey hℓlow
      have h1 : 64 * ((cφ / 16) * W ^ 2) = 4 * cφ * W ^ 2 := by ring
      have h2 : (64 : ℝ) * (ℓ / 64) = ℓ := by ring
      linarith [h1, h2, h3]
    -- the vector data
    set A : Space := r (taR D σ) - chordEndA r D δ₂ ε with hAdef
    set B : Space := r (tbR D σ) - chordEndB r D δ₂ ε with hBdef
    set E : Space := (r (tbR D σ) - r (taR D σ))
      - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) with hEdef
    set ν : ℝ := nCoord r D lam δ₁ δ₂ ε v 0 with hνdef
    set hup : ℝ := ‖chartUp r D lam δ₁ δ₂ ε v‖ with hhupdef
    set e : Space := chartE r D lam δ₁ δ₂ ε v with hedef
    have hv1 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
    have hee : ‖e‖ ≤ 1 := H2.chartE_norm_le_one r D lam δ₁ δ₂ ε v
    have hve : inner ℝ v e = 0 := by
      rw [hedef, real_inner_comm]; exact H2.chartE_inner_v hv
    have hCbv : inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) v = ℓ := by
      rw [hvC, real_inner_smul_left, hv1, mul_one]
    have hCbe : inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) e = 0 := by
      rw [hvC, real_inner_smul_left, hve, mul_zero]
    have hblur := hΛg δ₂ σ hδ₂0 (le_trans hδ₂Λ hΛΛg) hδ₂ε hσlo hσhi
    have hA : ‖A‖ ≤ τ := hblur.1
    have hB : ‖B‖ ≤ τ := hblur.2.1
    have hE : ‖E‖ ≤ τ := hblur.2.2.1
    have hAv : |inner ℝ A v| ≤ τ := by
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      rw [hv, mul_one]; exact hA
    have hBv : |inner ℝ B v| ≤ τ := by
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      rw [hv, mul_one]; exact hB
    have hAe : |inner ℝ A e| ≤ τ := by
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      calc ‖A‖ * ‖e‖ ≤ τ * 1 := mul_le_mul hA hee (norm_nonneg _) hτ0
        _ = τ := by ring
    have hBe : |inner ℝ B e| ≤ τ := by
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      calc ‖B‖ * ‖e‖ ≤ τ * 1 := mul_le_mul hB hee (norm_nonneg _) hτ0
        _ = τ := by ring
    have hEv : |inner ℝ E v| ≤ τ := by
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      rw [hv, mul_one]; exact hE
    have hEe : |inner ℝ E e| ≤ τ := by
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      calc ‖E‖ * ‖e‖ ≤ τ * 1 := mul_le_mul hE hee (norm_nonneg _) hτ0
        _ = τ := by ring
    have hν : |ν - ℓ / 2| ≤ W ^ 2 * K / 2 :=
      H2.basePoint_v_coord (r := r) (D := D) hr hK0.le hWpos.le hlam0.le hlam12 hδ₁0 hδ₁4
        hδ₂0 hδ₂ε hε0 hε12' hv hKb hWσfun hvC
    have hup_le : hup ≤ W ^ 2 * K :=
      H2.chartUp_norm_bound (r := r) (D := D) hr hK0.le hWpos.le hlam0.le hlam12 hδ₁0 hδ₁4
        hδ₂0 hδ₂ε hε0 hε12' hv hKb hWσfun hvC
    have hupge : cφ * W ^ 2 ≤ hup :=
      hΛφ lam δ₁ δ₂ hlam0 (le_trans hlamΛ hΛΛφ) hδ₁0 (le_trans hδ₁Λ hΛΛφ) hδ₂0
        (le_trans hδ₂Λ hΛΛφ) hδ₂ε v hv hvC
    have hup0 : 0 ≤ hup := norm_nonneg _
    have hτh : τ ≤ hup / 16 := by
      have h1 : 16 * ((cφ / 16) * W ^ 2) = cφ * W ^ 2 := by ring
      nlinarith [h1, hupge]
    -- the two-sided bounds on the deviations
    have hWs : (sweepW' D σ) ^ 2 ≤ 4 * W ^ 2 := by nlinarith [hWσ2, hWpos.le]
    have hdevv : ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
        |inner ℝ (loopDev r D σ ξ) v| ≤ W ^ 2 * K / 2 := by
      intro ξ hξ
      have h1 := Generic.nclm_dev_scalar_le (D := D) (r := r) hr (y := v) (B := K)
        (σ := σ) (ξ := ξ) hWσpos hξ (fun x _ => by
          calc |inner ℝ (deriv (deriv r) x) v| ≤ ‖deriv (deriv r) x‖ * ‖v‖ :=
                abs_real_inner_le_norm _ _
            _ = ‖deriv (deriv r) x‖ := by rw [hv, mul_one]
            _ ≤ K := hKb x)
      have hfac : ξ * (1 - ξ) / 2 ≤ 1 / 8 := by nlinarith [sq_nonneg (ξ - 1 / 2)]
      calc |inner ℝ (loopDev r D σ ξ) v|
          ≤ ξ * (1 - ξ) / 2 * (sweepW' D σ) ^ 2 * K := h1
        _ ≤ (1 / 8) * (4 * W ^ 2) * K := by gcongr
        _ = W ^ 2 * K / 2 := by ring
    have hdeve : ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
        |inner ℝ (loopDev r D σ ξ) e| ≤ W ^ 2 * K / 2 := by
      intro ξ hξ
      have h1 := Generic.nclm_dev_scalar_le (D := D) (r := r) hr (y := e) (B := K)
        (σ := σ) (ξ := ξ) hWσpos hξ (fun x _ => by
          calc |inner ℝ (deriv (deriv r) x) e| ≤ ‖deriv (deriv r) x‖ * ‖e‖ :=
                abs_real_inner_le_norm _ _
            _ ≤ K * 1 := mul_le_mul (hKb x) hee (norm_nonneg _) hK0.le
            _ = K := mul_one K)
      have hfac : ξ * (1 - ξ) / 2 ≤ 1 / 8 := by nlinarith [sq_nonneg (ξ - 1 / 2)]
      calc |inner ℝ (loopDev r D σ ξ) e|
          ≤ ξ * (1 - ξ) / 2 * (sweepW' D σ) ^ 2 * K := h1
        _ ≤ (1 / 8) * (4 * W ^ 2) * K := by gcongr
        _ = W ^ 2 * K / 2 := by ring
    -- the four chart identities
    have hidA : ∀ ξ : ℝ, inner ℝ (sweepArc' r D σ ξ - chartC r D lam δ₁ δ₂ ε v) v
        = inner ℝ (loopDev r D σ ξ) v + (1 - ξ) * inner ℝ A v + ξ * inner ℝ B v
          + ξ * ℓ - ν := by
      intro ξ
      rw [sweepArc'_sub_chartC_inner_v (r := r) (D := D) (σ := σ) (ξ := ξ) (lam := lam)
        (δ₁ := δ₁) (δ₂ := δ₂) (ε := ε) hv, hCbv]
    have hidC : ∀ ξ : ℝ, inner ℝ (sweepChord' r D σ ξ - chartC r D lam δ₁ δ₂ ε v) v
        = (1 - ξ) * inner ℝ A v + ξ * inner ℝ B v + ξ * ℓ - ν := by
      intro ξ
      rw [sweepChord'_sub_chartC_inner_v (r := r) (D := D) (σ := σ) (ξ := ξ) (lam := lam)
        (δ₁ := δ₁) (δ₂ := δ₂) (ε := ε) hv, hCbv]
    have hidCe : ∀ ξ : ℝ, inner ℝ (sweepChord' r D σ ξ - chartC r D lam δ₁ δ₂ ε v) e
        = (1 - ξ) * inner ℝ A e + ξ * inner ℝ B e - (hup / 2) * ‖e‖ ^ 2 := by
      intro ξ
      rw [sweepChord'_sub_chartC_inner_e (r := r) (D := D) (σ := σ) (ξ := ξ)
        (lam := lam) (δ₁ := δ₁) (δ₂ := δ₂) (ε := ε) hv, hCbe, mul_zero, add_zero]
    have hE1 : inner ℝ (r (taR D σ) - chartC r D lam δ₁ δ₂ ε v) v = inner ℝ A v - ν :=
      inner_taR_sub_chartC_v (r := r) (D := D) (σ := σ) (lam := lam) (δ₁ := δ₁) (δ₂ := δ₂)
        (ε := ε) hv
    have hE2 : inner ℝ (r (tbR D σ) - chartC r D lam δ₁ δ₂ ε v) v
        = inner ℝ B v + ℓ - ν := by
      rw [inner_tbR_sub_chartC_v (r := r) (D := D) (σ := σ) (lam := lam) (δ₁ := δ₁)
        (δ₂ := δ₂) (ε := ε) hv, hCbv]
    have hEe1 : inner ℝ (r (taR D σ) - chartC r D lam δ₁ δ₂ ε v) e
        = inner ℝ A e - (hup / 2) * ‖e‖ ^ 2 :=
      inner_taR_sub_chartC_chartE (r := r) (D := D) (σ := σ) (lam := lam) (δ₁ := δ₁)
        (δ₂ := δ₂) (ε := ε) hv
    have hEe2 : inner ℝ (r (tbR D σ) - chartC r D lam δ₁ δ₂ ε v) e
        = inner ℝ B e + inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) e
          - (hup / 2) * ‖e‖ ^ 2 :=
      inner_tbR_sub_chartC_chartE (r := r) (D := D) (σ := σ) (lam := lam) (δ₁ := δ₁)
        (δ₂ := δ₂) (ε := ε) hv
    have hEe2' : inner ℝ (r (tbR D σ) - chartC r D lam δ₁ δ₂ ε v) e
        = inner ℝ B e - (hup / 2) * ‖e‖ ^ 2 := by rw [hEe2, hCbe, add_zero]
    have hcoe : (1 : ℝ) - (1 - lam) = lam := by ring
    have hξ1 : (1 - lam) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hξl : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨hlam0.le, by linarith⟩
    have hνhi : ν ≤ ℓ / 2 + W ^ 2 * K / 2 := by linarith [(abs_le.mp hν).2]
    have hνlo : ℓ / 2 - W ^ 2 * K / 2 ≤ ν := by linarith [(abs_le.mp hν).1]
    have hfacl : (3 / 8) * ℓ ≤ (1 - lam) * ℓ := by nlinarith [hlam18, hℓpos]
    have hfacl' : lam * ℓ ≤ (1 / 8) * ℓ := mul_le_mul_of_nonneg_right hlam18 hℓ0
    have hsumv : ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
        -τ ≤ (1 - ξ) * inner ℝ A v + ξ * inner ℝ B v ∧
          (1 - ξ) * inner ℝ A v + ξ * inner ℝ B v ≤ τ := by
      intro ξ hξ
      have hξ0 : 0 ≤ ξ := hξ.1
      have hξ1' : 0 ≤ 1 - ξ := by linarith [hξ.2]
      have h3 : (1 - ξ) * τ + ξ * τ = τ := by ring
      have h3v : (1 - ξ) * τ + ξ * τ = τ := h3
      constructor
      · have h1 : -((1 - ξ) * τ) ≤ (1 - ξ) * inner ℝ A v := by
          have h := mul_le_mul_of_nonneg_left (abs_le.mp hAv).1 hξ1'
          rwa [mul_neg] at h
        have h2 : -(ξ * τ) ≤ ξ * inner ℝ B v := by
          have h := mul_le_mul_of_nonneg_left (abs_le.mp hBv).1 hξ0
          rwa [mul_neg] at h
        linarith [h1, h2, h3, h3v]
      · have h1 : (1 - ξ) * inner ℝ A v ≤ (1 - ξ) * τ :=
          mul_le_mul_of_nonneg_left (abs_le.mp hAv).2 hξ1'
        have h2 : ξ * inner ℝ B v ≤ ξ * τ := mul_le_mul_of_nonneg_left (abs_le.mp hBv).2 hξ0
        linarith [h1, h2, h3, h3v]
    have hsume : ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
        |(1 - ξ) * inner ℝ A e + ξ * inner ℝ B e| ≤ τ := by
      intro ξ hξ
      have hξ0 : 0 ≤ ξ := hξ.1
      have hξ1' : 0 ≤ 1 - ξ := by linarith [hξ.2]
      have h3 : (1 - ξ) * τ + ξ * τ = τ := by ring
      rw [abs_le]
      constructor
      · have h1 : -((1 - ξ) * τ) ≤ (1 - ξ) * inner ℝ A e := by
          have h := mul_le_mul_of_nonneg_left (abs_le.mp hAe).1 hξ1'
          rwa [mul_neg] at h
        have h2 : -(ξ * τ) ≤ ξ * inner ℝ B e := by
          have h := mul_le_mul_of_nonneg_left (abs_le.mp hBe).1 hξ0
          rwa [mul_neg] at h
        linarith [h1, h2, h3]
      · have h1 : (1 - ξ) * inner ℝ A e ≤ (1 - ξ) * τ :=
          mul_le_mul_of_nonneg_left (abs_le.mp hAe).2 hξ1'
        have h2 : ξ * inner ℝ B e ≤ ξ * τ := mul_le_mul_of_nonneg_left (abs_le.mp hBe).2 hξ0
        linarith [h1, h2, h3]
    have hee2 : ‖e‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg e]
    have hh2 : (hup / 2) * ‖e‖ ^ 2 ≤ hup / 2 := by
      have h := mul_le_mul_of_nonneg_left hee2 (by positivity : (0 : ℝ) ≤ hup / 2)
      rwa [mul_one] at h
    have hh2' : 0 ≤ (hup / 2) * ‖e‖ ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change ℓ / 4 ≤ inner ℝ (sweepArc' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v) v
      rw [hidA (1 - lam), hcoe]
      have hdev := (abs_le.mp (hdevv (1 - lam) hξ1)).1
      have hsum := (hsumv (1 - lam) hξ1).1
      linarith [hdev, hsum, hνhi, hfacl, hW2K, hτℓ]
    · change inner ℝ (sweepArc' r D σ lam - chartC r D lam δ₁ δ₂ ε v) v ≤ -(ℓ / 4)
      rw [hidA lam]
      have hdev := (abs_le.mp (hdevv lam hξl)).2
      have hsum := (hsumv lam hξl).2
      linarith [hdev, hsum, hνlo, hfacl', hW2K, hτℓ]
    · rw [hE1, abs_le]
      constructor <;>
        linarith [(abs_le.mp hAv).1, (abs_le.mp hAv).2, hνhi, hνlo, hW2K, hτℓ, hℓ0]
    · rw [hE2, abs_le]
      constructor <;>
        linarith [(abs_le.mp hBv).1, (abs_le.mp hBv).2, hνhi, hνlo, hW2K, hτℓ, hℓ0]
    · rw [hEe1]
      rcases eq_or_ne (chartUp r D lam δ₁ δ₂ ε v) 0 with hz | hne
      · have hup0' : hup = 0 := by rw [hhupdef, hz, norm_zero]
        have he0 : e = 0 := by rw [hedef, chartE, hz, norm_zero, inv_zero, zero_smul]
        rw [he0, hup0']
        norm_num
      · have he1 : ‖e‖ = 1 := by
          rw [hedef, chartE, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
          exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)
        have h1 := (abs_le.mp hAe).2
        rw [he1, one_pow, mul_one]
        linarith [h1, hτh]
    · rw [hEe2']
      rcases eq_or_ne (chartUp r D lam δ₁ δ₂ ε v) 0 with hz | hne
      · have hup0' : hup = 0 := by rw [hhupdef, hz, norm_zero]
        have he0 : e = 0 := by rw [hedef, chartE, hz, norm_zero, inv_zero, zero_smul]
        rw [he0, hup0']
        norm_num
      · have he1 : ‖e‖ = 1 := by
          rw [hedef, chartE, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
          exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)
        have h1 := (abs_le.mp hBe).2
        rw [he1, one_pow, mul_one]
        linarith [h1, hτh]
    · have hsplit : r (tbR D σ) - r (taR D σ)
          = (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) + E := by rw [hEdef]; abel
      rw [hsplit, inner_add_left, hCbv]
      have h1 := (abs_le.mp hEv).1
      linarith [h1, hτℓ, hℓpos]
    · have hsplit : r (tbR D σ) - r (taR D σ)
          = (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) + E := by rw [hEdef]; abel
      rw [hsplit, inner_add_left, hCbe, zero_add]
      exact le_trans hEe hτh
    · rw [hidC lam]
      have hsum := (hsumv lam hξl).2
      linarith [hsum, hfacl', hνlo, hW2K, hτℓ]
    · rw [hidC (1 - lam), hcoe]
      have hsum := (hsumv (1 - lam) hξ1).1
      linarith [hsum, hfacl, hνhi, hW2K, hτℓ]
    · rw [hidCe lam, abs_le]
      have hs := hsume lam hξl
      constructor <;> linarith [(abs_le.mp hs).1, (abs_le.mp hs).2, hh2, hh2', hτh, hup0]
    · rw [hidCe (1 - lam), hcoe, abs_le]
      have hs := hsume (1 - lam) hξ1
      constructor <;> linarith [(abs_le.mp hs).1, (abs_le.mp hs).2, hh2, hh2', hτh, hup0]

end Work.Drive.CDC
