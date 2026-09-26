import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.needleProfileDefs
import Submission.Work.Drive.arcZoneWindow
import Submission.Work.Drive.cInfKnot

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology

/-!
# Window data at the collapsed end of the chord sweep

For an analytic knot `r`, a band-arc sweep `D` and any `δ > 0` there is `ε₀ > 0` with the following
property: whenever `0 < δ₂ ≤ ε/2` and `0 < ε ≤ ε₀`, then

* every point of the retained arc of every loop in the window `[ε - δ₂, ε + δ₂]` is within `δ` of the
  collapsed end `ρ = taR D 0` (the whole arc is a `δ`-small neighbourhood of `ρ`);
* the needle's chord `chordEndB - chordEndA` is non-degenerate, and its unit direction is within `δ`
  of the unit tangent at `ρ`.

The proof is a direct `ε`-estimate: each chord `r (tbR σ) - r (taR σ)` is the velocity integral over a
short interval at distance `≤ O(ε)` from `ρ`, so after the `σ`-average (`chordEndB_sub_chordEndA`) the
whole vector is `∫ bump v • (W(σ_v) v₀ + O(W(σ_v)))`, the positive part `K := ∫ bump v * W(σ_v) > 0`
(`integral_sweepBump_mul_sweepW_pos`) dominates, and the usual unit-vector Lipschitz estimate gives the
direction bound.
-/

section Helpers

/-! ## `clampI` and the extended lift data -/

theorem wds_clampI_eq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    clampI x = (⟨x, h0, h1⟩ : Set.Icc (0 : ℝ) 1) := by
  refine Subtype.ext ?_
  simp only [clampI]
  rw [max_eq_right h0, min_eq_right h1]

theorem wds_taR_eq {d : BandArcData} (D : SweepData d) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    taR D x = D.ta ⟨x, h0, h1⟩ := by
  rw [taR, wds_clampI_eq h0 h1]

theorem wds_tbR_eq {d : BandArcData} (D : SweepData d) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    tbR D x = D.tb ⟨x, h0, h1⟩ := by
  rw [tbR, wds_clampI_eq h0 h1]

theorem wds_sweepW'_eq {d : BandArcData} (D : SweepData d) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    sweepW' D x = sweepW D ⟨x, h0, h1⟩ := by
  rw [sweepW', wds_taR_eq D h0 h1, wds_tbR_eq D h0 h1]
  rfl

/-- The width of the retained arc is positive at every interior parameter. -/
theorem wds_sweepW'_pos {d : BandArcData} (D : SweepData d) {x : ℝ}
    (h0 : 0 < x) (h1 : x < 1) : 0 < sweepW' D x := by
  rw [wds_sweepW'_eq D h0.le h1.le]
  exact (sweepW_pos_lt D _ ⟨h0, h1⟩).1

/-- **Positivity of the bump-weighted width** over the sweep window `[ε-δ₂, ε+δ₂]`. -/
theorem wds_K_pos {d : BandArcData} (D : SweepData d) {δ₂ ε : ℝ}
    (hε0 : 0 < ε) (hδ₂0 : 0 < δ₂) (hδ₂ : δ₂ ≤ ε / 2) (hε1 : 3 * ε / 2 < 1) :
    0 < ∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (ε - δ₂ * v) := by
  have hσ : ∀ v ∈ Set.Icc (-1 : ℝ) 1, 0 < ε - δ₂ * v ∧ ε - δ₂ * v < 1 := by
    intro v hv
    constructor
    · nlinarith [hε0, hδ₂0, hδ₂, hv.1, hv.2]
    · nlinarith [hε0, hδ₂0, hδ₂, hε1, hv.1, hv.2]
  have hWc : ∀ v ∈ Set.Icc (-1 : ℝ) 1, 0 < sweepW' D (ε - δ₂ * v) := by
    intro v hv
    obtain ⟨h1, h2⟩ := hσ v hv
    exact wds_sweepW'_pos D h1 h2
  refine intervalIntegral.integral_pos (by norm_num : (-1 : ℝ) < 1) ?_ ?_ ⟨0, by norm_num, ?_⟩
  · exact (sweepBump_continuous.mul
      ((arcWin_sweepW'_continuous D).comp (by fun_prop))).continuousOn
  · intro v hv
    exact mul_nonneg (sweepBump_nonneg v) (hWc v ⟨hv.1.le, hv.2⟩).le
  · have hb : 0 < sweepBump 0 := by
      rw [sweepBump]
      exact mul_pos (Real.smoothTransition.pos_of_pos (by norm_num))
        (Real.smoothTransition.pos_of_pos (by norm_num))
    have hw := hWc 0 (by norm_num)
    simpa using mul_pos hb hw

/-! ## Abstract estimates -/

/-- **The unit-vector Lipschitz estimate**: near a non-zero vector `y`, normalisation is
`2/‖y‖`-Lipschitz. -/
theorem wds_norm_unit_sub_le {x y : Space} (hy : y ≠ 0) (h : ‖x - y‖ ≤ ‖y‖ / 2) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 4 * ‖x - y‖ / ‖y‖ := by
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hxge : ‖y‖ / 2 ≤ ‖x‖ := by
    have habs := abs_norm_sub_norm_le x y
    have h2 : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by
      have h3 := neg_le_of_abs_le habs
      linarith
    linarith
  have hxn : 0 < ‖x‖ := by linarith
  have hdecomp : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y
      = ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by
    rw [smul_sub, sub_smul]; abel
  have hb1 : ‖‖x‖⁻¹ • (x - y)‖ = ‖x‖⁻¹ * ‖x - y‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hxn.le)]
  have hb3 : ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ = |‖x‖ - ‖y‖| / ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : ‖x‖⁻¹ - ‖y‖⁻¹ = (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) := by
      field_simp
    rw [h1, abs_div, abs_of_pos (mul_pos hxn hyn)]
    field_simp
    rw [abs_sub_comm]
  have hstep : ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ / ‖x‖ := by
    calc ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖
        = ‖‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := by rw [hdecomp]
      _ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := norm_add_le _ _
      _ = ‖x‖⁻¹ * ‖x - y‖ + |‖x‖ - ‖y‖| / ‖x‖ := by rw [hb1, hb3]
      _ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ := by
            have h4 : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
            have h5 : ‖x‖⁻¹ * ‖x - y‖ = ‖x - y‖ / ‖x‖ := by rw [inv_mul_eq_div]
            rw [h5]
            gcongr
      _ = 2 * ‖x - y‖ / ‖x‖ := by ring
  refine le_trans hstep ?_
  have h2 : ‖x‖⁻¹ ≤ 2 * ‖y‖⁻¹ := by
    have h4 : (‖y‖ / 2)⁻¹ = 2 * ‖y‖⁻¹ := by
      rw [div_eq_mul_inv, mul_inv, inv_inv, mul_comm]
    rw [← h4]
    exact (inv_le_inv₀ hxn (by linarith : 0 < ‖y‖ / 2)).mpr hxge
  have hnn : 0 ≤ 2 * ‖x - y‖ := by positivity
  have hfin : 2 * ‖x - y‖ / ‖x‖ ≤ 4 * ‖x - y‖ / ‖y‖ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc 2 * ‖x - y‖ * ‖x‖⁻¹ ≤ 2 * ‖x - y‖ * (2 * ‖y‖⁻¹) :=
          mul_le_mul_of_nonneg_left h2 hnn
      _ = 4 * ‖x - y‖ * ‖y‖⁻¹ := by ring
  linarith

/-- **The bump integral estimate**: if a continuous vector field `G` is pointwise dominated by a
continuous scalar `g` on `[-1,1]`, then so is its bump-smoothed integral. -/
theorem wds_norm_integral_bump_le {G : ℝ → Space} {g : ℝ → ℝ}
    (hGc : Continuous G) (hgc : Continuous g)
    (hpt : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ‖G v‖ ≤ g v) :
    ‖∫ v in (-1 : ℝ)..1, sweepBump v • G v‖
      ≤ ∫ v in (-1 : ℝ)..1, sweepBump v * g v := by
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1:ℝ) ≤ 1)) ?_
  refine intervalIntegral.integral_mono_on (by norm_num : (-1:ℝ) ≤ 1) ?_ ?_ ?_
  · exact (sweepBump_continuous.smul hGc).norm.intervalIntegrable _ _
  · exact (sweepBump_continuous.mul hgc).intervalIntegrable _ _
  · intro v hv
    rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]
    exact mul_le_mul_of_nonneg_left (hpt v ⟨hv.1, hv.2⟩) (sweepBump_nonneg v)

/-- **The chord direction estimate.**  If `V = K v₀ + E` with `K > 0`, `‖E‖ ≤ lam * K` and
`lam ≤ ‖v₀‖/2`, then `V ≠ 0` and its unit direction is within `4 lam / ‖v₀‖` of that of `v₀`. -/
theorem wds_direction_bound {v₀ V : Space} {K lam : ℝ}
    (hv₀ : v₀ ≠ 0) (hK : 0 < K) (hlam : lam ≤ ‖v₀‖ / 2)
    (hbound : ‖V - K • v₀‖ ≤ lam * K) :
    V ≠ 0 ∧ ‖‖V‖⁻¹ • V - ‖v₀‖⁻¹ • v₀‖ ≤ 4 * lam / ‖v₀‖ := by
  have hv₀n : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀
  have hKv₀ : ‖K • v₀‖ = K * ‖v₀‖ := by
    rw [norm_smul, Real.norm_of_nonneg hK.le]
  have hKne : (K • v₀) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hKv₀
    nlinarith [hK, hv₀n]
  have hxy : ‖V - K • v₀‖ ≤ ‖K • v₀‖ / 2 := by
    rw [hKv₀]
    nlinarith [hbound, hlam, hK, hv₀n]
  have hunit := wds_norm_unit_sub_le hKne hxy
  have hunit' : ‖v₀‖⁻¹ • v₀ = ‖K • v₀‖⁻¹ • (K • v₀) := by
    rw [hKv₀, smul_smul, mul_inv, mul_comm K⁻¹ ‖v₀‖⁻¹,
      mul_assoc, inv_mul_cancel₀ (ne_of_gt hK), mul_one]
  have hnormV : K * ‖v₀‖ / 2 ≤ ‖V‖ := by
    have h1 : ‖K • v₀‖ ≤ ‖V‖ + ‖V - K • v₀‖ := by
      have := norm_le_norm_add_norm_sub' (K • v₀) V
      simpa [norm_sub_rev, add_comm] using this
    rw [hKv₀] at h1
    nlinarith [h1, hbound, hlam, hK, hv₀n]
  refine ⟨?_, ?_⟩
  · intro hV
    rw [hV, norm_zero] at hnormV
    nlinarith [hnormV, hK, hv₀n]
  · rw [hunit']
    refine le_trans hunit ?_
    rw [hKv₀]
    have h1 : 4 * ‖V - K • v₀‖ / (K * ‖v₀‖) ≤ 4 * (lam * K) / (K * ‖v₀‖) := by
      gcongr
    refine le_trans h1 (le_of_eq ?_)
    field_simp

/-- **The chord is its width times the tangent, up to the variation of the velocity.** -/
theorem wds_norm_chord_sub_le {r : ℝ → Space} (hr : IsSmoothKnot r)
    {a b : ℝ} (hab : a ≤ b) {v₀ : Space} {lam : ℝ}
    (hvel : ∀ x ∈ Set.Icc a b, ‖velocity r x - v₀‖ ≤ lam) :
    ‖(r b - r a) - (b - a) • v₀‖ ≤ lam * (b - a) := by
  have hvelcont : Continuous (velocity r) := by
    have h : Continuous (deriv r) := hr.smooth.continuous_deriv (by simp : (1 : WithTop ℕ∞) ≤ ⊤)
    rw [show velocity r = deriv r from rfl]
    exact h
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt r (velocity r x) x := fun x _ =>
    ((hr.smooth.differentiable (by simp)) x).hasDerivAt
  have hint : IntervalIntegrable (velocity r) volume a b := hvelcont.intervalIntegrable _ _
  have hchord : r b - r a = ∫ x in a..b, velocity r x :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint).symm
  have hconst : ∫ x in a..b, v₀ = (b - a) • v₀ := intervalIntegral.integral_const v₀
  have hsub : (∫ x in a..b, velocity r x) - (∫ x in a..b, v₀)
      = ∫ x in a..b, (velocity r x - v₀) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
  rw [hchord, ← hconst, hsub]
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := lam) ?_) ?_
  · intro x hx
    rw [Set.uIoc_of_le hab] at hx
    exact hvel x ⟨hx.1.le, hx.2⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr hab)]

end Helpers

set_option maxHeartbeats 400000 in
theorem windowDataSmall {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ (δ₂ ε : ℝ), 0 < δ₂ → δ₂ ≤ ε / 2 → 0 < ε → ε ≤ ε₀ →
      (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 →
        |Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ - Work.Drive.taR D 0| ≤ δ) ∧
      (Work.Drive.chordEndB r D δ₂ ε ≠ Work.Drive.chordEndA r D δ₂ ε) ∧
      ‖(‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖⁻¹ •
          (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε)) -
        (‖deriv r (Work.Drive.taR D 0)‖⁻¹ •
          deriv r (Work.Drive.taR D 0))‖ ≤ δ := by
  set v₀ : Space := deriv r (taR D 0) with hv₀
  have hv₀ne : v₀ ≠ 0 := by
    rw [hv₀]
    exact hr.regular (taR D 0)
  have hv₀pos : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀ne
  set mδ : ℝ := min δ 1 with hmδ
  have hmδpos : 0 < mδ := lt_min hδ zero_lt_one
  have hmδle1 : mδ ≤ 1 := min_le_right _ _
  have hmδleδ : mδ ≤ δ := min_le_left _ _
  set lam : ℝ := ‖v₀‖ * mδ / 8 with hlam
  have hlamp : 0 < lam := by rw [hlam]; positivity
  have hlamle : lam ≤ ‖v₀‖ / 2 := by
    rw [hlam]; nlinarith [hv₀pos, hmδle1]
  have hlamδ : 4 * lam / ‖v₀‖ ≤ δ := by
    have h1 : 4 * (‖v₀‖ * mδ / 8) / ‖v₀‖ = mδ / 2 := by
      field_simp
      ring
    rw [hlam, h1]
    linarith [hmδleδ]
  have hvelcont : Continuous (velocity r) := by
    have h : Continuous (deriv r) := hr.smooth.continuous_deriv (by simp : (1 : WithTop ℕ∞) ≤ ⊤)
    rw [show velocity r = deriv r from rfl]
    exact h
  obtain ⟨ρvel, hρvelpos, hρvel⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : ℝ,
      |x - taR D 0| < ρ → ‖velocity r x - v₀‖ ≤ lam := by
    obtain ⟨ρ, hρ, hspec⟩ :=
      Metric.continuousAt_iff.mp (hvelcont.continuousAt (x := taR D 0)) lam hlamp
    refine ⟨ρ, hρ, ?_⟩
    intro x hx
    have h2 := hspec (x := x) (by rw [Real.dist_eq]; exact hx)
    rw [dist_eq_norm] at h2
    rw [show velocity r (taR D 0) = deriv r (taR D 0) from rfl, ← hv₀] at h2
    exact le_of_lt h2
  set w0 : ℝ := min (δ / 2) (ρvel / 4) with hw0
  have hw0pos : 0 < w0 := lt_min (by linarith) (by linarith)
  have hw0leδ : 2 * w0 ≤ δ := by
    have h := min_le_left (δ / 2) (ρvel / 4)
    rw [hw0]; linarith
  have hw0leρ : 2 * w0 < ρvel := by
    have h := min_le_right (δ / 2) (ρvel / 4)
    rw [hw0]; linarith
  obtain ⟨η, hη, hηspec⟩ := exists_window_small D hw0pos
  refine ⟨min (2 * η / 3) (1 / 2), lt_min (by positivity) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro δ₂ ε hδ₂pos hδ₂ε hεpos hεε₀
  have hεη : ε ≤ 2 * η / 3 := le_trans hεε₀ (min_le_left _ _)
  have hεhalf : ε ≤ 1 / 2 := le_trans hεε₀ (min_le_right _ _)
  have hε32 : 3 * ε / 2 < 1 := by linarith
  have hσw_le : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → 0 ≤ σ ∧ σ ≤ η := by
    intro σ h1 h2
    refine ⟨by linarith, ?_⟩
    nlinarith [hεη, hεpos, hδ₂ε, h2]
  refine ⟨?_, ?_⟩
  · -- Clause 1: the retained arcs of the window lie in a `δ`-ball around `ρ`.
    intro σ hσlo hσhi ξ hξ0 hξ1
    obtain ⟨hσ0, hση⟩ := hσw_le σ hσlo hσhi
    obtain ⟨hA, hB⟩ := hηspec σ hσ0 hση
    have hWpos : (0 : ℝ) < sweepW' D σ := by
      refine wds_sweepW'_pos D (by linarith) ?_
      nlinarith [hσhi, hδ₂ε, hεhalf]
    have hd2 : |tbR D σ - taR D 0| ≤ 2 * w0 := by
      have heq : tbR D σ - taR D 0 = (taR D σ - taR D 0) + sweepW' D σ := by
        rw [sweepW']; ring
      rw [heq]
      calc |(taR D σ - taR D 0) + sweepW' D σ|
          ≤ |taR D σ - taR D 0| + |sweepW' D σ| := abs_add_le _ _
        _ ≤ w0 + w0 := add_le_add hA (by rw [abs_of_pos hWpos]; exact hB)
        _ = 2 * w0 := by ring
    have htarget : taR D σ + ξ * sweepW' D σ - taR D 0
        = (1 - ξ) * (taR D σ - taR D 0) + ξ * (tbR D σ - taR D 0) := by
      rw [sweepW']; ring
    rw [htarget]
    have hmain : |(1 - ξ) * (taR D σ - taR D 0) + ξ * (tbR D σ - taR D 0)| ≤ 2 * w0 := by
      rw [abs_le] at hA hd2 ⊢
      exact ⟨by nlinarith [hA.1, hd2.1, hξ0, hξ1],
             by nlinarith [hA.2, hd2.2, hξ0, hξ1]⟩
    linarith [hmain, hw0leδ]
  · -- Clauses 2 and 3: the needle's chord.
    set σv : ℝ → ℝ := fun v => ε - δ₂ * v with hσv
    have hσvc : Continuous σv := by rw [hσv]; fun_prop
    have hσvlo : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ε / 2 ≤ σv v := by
      intro v hv
      have hv1 : δ₂ * v ≤ δ₂ := by nlinarith [hδ₂pos, hv.2]
      rw [hσv]; linarith
    have hσvhi : ∀ v ∈ Set.Icc (-1 : ℝ) 1, σv v ≤ 3 * ε / 2 := by
      intro v hv
      have hv2 : -δ₂ ≤ δ₂ * v := by nlinarith [hδ₂pos, hv.1]
      rw [hσv]; linarith
    have hσvpos : ∀ v ∈ Set.Icc (-1 : ℝ) 1, 0 < σv v := fun v hv =>
      by linarith [hσvlo v hv, hεpos]
    have hσvlt1 : ∀ v ∈ Set.Icc (-1 : ℝ) 1, σv v < 1 := fun v hv =>
      by linarith [hσvhi v hv, hε32]
    have hσvη : ∀ v ∈ Set.Icc (-1 : ℝ) 1, σv v ≤ η := fun v hv =>
      by linarith [hσvhi v hv, hεη]
    have hWpos : ∀ v ∈ Set.Icc (-1 : ℝ) 1, 0 < sweepW' D (σv v) := fun v hv =>
      wds_sweepW'_pos D (hσvpos v hv) (hσvlt1 v hv)
    have htac : Continuous fun v : ℝ => taR D (σv v) := (arcWin_taR_continuous D).comp hσvc
    have htbc : Continuous fun v : ℝ => tbR D (σv v) := (arcWin_tbR_continuous D).comp hσvc
    have hWc : Continuous fun v : ℝ => sweepW' D (σv v) :=
      (arcWin_sweepW'_continuous D).comp hσvc
    have hrc : Continuous r := hr.smooth.continuous
    have hvelwin : ∀ v ∈ Set.Icc (-1 : ℝ) 1,
        ∀ x ∈ Set.Icc (taR D (σv v)) (tbR D (σv v)), ‖velocity r x - v₀‖ ≤ lam := by
      intro v hv x hx
      obtain ⟨hA, hB⟩ := hηspec (σv v) (by linarith [hσvpos v hv]) (hσvη v hv)
      have hd2 : |tbR D (σv v) - taR D 0| ≤ 2 * w0 := by
        have heq : tbR D (σv v) - taR D 0
            = (taR D (σv v) - taR D 0) + sweepW' D (σv v) := by
          rw [sweepW']; ring
        rw [heq]
        calc |(taR D (σv v) - taR D 0) + sweepW' D (σv v)|
            ≤ |taR D (σv v) - taR D 0| + |sweepW' D (σv v)| := abs_add_le _ _
          _ ≤ w0 + w0 := add_le_add hA (by rw [abs_of_pos (hWpos v hv)]; exact hB)
          _ = 2 * w0 := by ring
      have hxbd : |x - taR D 0| ≤ 2 * w0 := by
        rw [abs_le] at hA hd2 ⊢
        exact ⟨by linarith [hA.1, hx.1, hw0pos], by linarith [hd2.2, hx.2]⟩
      exact hρvel x (lt_of_le_of_lt hxbd hw0leρ)
    set G : ℝ → Space :=
      fun v => (r (tbR D (σv v)) - r (taR D (σv v))) - sweepW' D (σv v) • v₀ with hG
    have hGc : Continuous G := by
      rw [hG]
      exact ((hrc.comp htbc).sub (hrc.comp htac)).sub (hWc.smul continuous_const)
    set g : ℝ → ℝ := fun v => lam * sweepW' D (σv v) with hg
    have hgc : Continuous g := by rw [hg]; exact continuous_const.mul hWc
    set K : ℝ := ∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (σv v) with hK
    have hKpos : 0 < K := by
      rw [hK]
      exact wds_K_pos D hεpos hδ₂pos hδ₂ε hε32
    have hpt : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ‖G v‖ ≤ g v := by
      intro v hv
      have hab : taR D (σv v) ≤ tbR D (σv v) := by
        have h := hWpos v hv
        rw [sweepW'] at h
        linarith
      have := wds_norm_chord_sub_le (a := taR D (σv v)) (b := tbR D (σv v)) hr
        hab (hvelwin v hv)
      rw [hG, hg]
      simpa only [sweepW'] using this
    set E : Space := ∫ v in (-1 : ℝ)..1, sweepBump v • G v with hE
    have hEbound : ‖E‖ ≤ lam * K := by
      rw [hE]
      refine le_trans (wds_norm_integral_bump_le hGc hgc hpt) ?_
      rw [hg, hK]
      rw [show (fun v : ℝ => sweepBump v * (lam * sweepW' D (σv v)))
          = (fun v : ℝ => lam * (sweepBump v * sweepW' D (σv v))) from by funext v; ring]
      rw [intervalIntegral.integral_const_mul]
    set V : Space := chordEndB r D δ₂ ε - chordEndA r D δ₂ ε with hV
    have hVdecomp : V = K • v₀ + E := by
      rw [hV, hE, chordEndB_sub_chordEndA r D hrc δ₂ ε]
      rw [show (fun v : ℝ => sweepBump v • (r (tbR D (σv v)) - r (taR D (σv v))))
          = (fun v : ℝ => sweepBump v • (sweepW' D (σv v) • v₀) + sweepBump v • G v) from by
        funext v
        rw [hG, ← smul_add, add_sub_cancel]]
      rw [intervalIntegral.integral_add]
      · rw [show (fun v : ℝ => sweepBump v • (sweepW' D (σv v) • v₀))
            = (fun v : ℝ => (sweepBump v * sweepW' D (σv v)) • v₀) from by
          funext v; rw [smul_smul]]
        rw [intervalIntegral.integral_smul_const, hK]
      · exact (sweepBump_continuous.smul (hWc.smul continuous_const)).intervalIntegrable _ _
      · exact (sweepBump_continuous.smul hGc).intervalIntegrable _ _
    have hVB := wds_direction_bound hv₀ne hKpos hlamle
      (by rw [show V - K • v₀ = E from by rw [hVdecomp]; abel]; exact hEbound)
    refine ⟨?_, ?_⟩
    · intro h
      exact hVB.1 (by rw [hV, h]; abel)
    · exact le_trans hVB.2 hlamδ

end Work.Drive
