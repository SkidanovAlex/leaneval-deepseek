import Mathlib
import Submission.Work.Drive.AB.pinSetup
import Submission.Work.Drive.AB.windowDataSmall
import Submission.Work.Drive.AB.needleHalfspaceProfile
import Submission.Work.Drive.AB.chordEndNormLower
import Submission.Work.Drive.Generic.nclmDefs
import Submission.Work.Drive.Generic.nclmBasic
import Submission.Work.Drive.Generic.nclmDev
import Submission.Work.Drive.Generic.nclmE0
import Submission.Work.Drive.Generic.nclmWindow
import Submission.Work.Drive.Generic.nclmChart
import Submission.Work.Drive.Generic.nclm_chartUp_inner

/-!
# A lower bound for the needle's base height

`Work.Drive.chartUp r D lam δ₁ δ₂ ε v` is the offset of the (shifted) needle's base point from the
*line* of its chord; it is perpendicular to the unit chord direction `v`.  This module proves that
this offset is bounded below, uniformly in the box `(lam, δ₁, δ₂)`, by a fixed multiple of the
square of the retained width `sweepW' D ε`:

    c * (sweepW' D ε) ^ 2 ≤ ‖chartUp r D lam δ₁ δ₂ ε v‖ .

The mechanism is the *definite transverse curvature* at the collapsed end `ρ = taR D 0` of the band
arc (`hinfl` = absence of inflections).  With `e₀` the normalised transverse part of the acceleration
`r''(ρ)` (`Work.Drive.Generic.nclmE0`), the second-order structure of the deviation
(`Work.Drive.Generic.nclm_dev_scalar_ge`) gives, on every retained arc of the `σ`-window,

    (ξ (1-ξ)/2) * W(σ)^2 * κ ≤ ⟪loopDev (σ, ξ), -e₀⟫ ,   κ = ⟪r''(ρ), e₀⟫ = ‖transverse part‖ > 0 ,

whence `⟪chartUp, -e₀⟫ ≥ W(ε)^2 * κ / 256 − W(ε)^2 * dve * K / 2` by the double-average identity
`Work.Drive.Generic.nclm_chartUp_inner` and `Work.Drive.Generic.nclm_chartUp_bounds`, where `dve` is
the misalignment of the chord direction with the tangent at `ρ` (freely small, by
`Work.Drive.windowDataSmall`) and `K` a global bound of the acceleration.  Choosing the needle's
`δ`-window small enough that `dve * K/2 ≤ κ/512` leaves the margin.
-/

namespace Work.Drive.H2

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

noncomputable section

/-- **A positive global bound for the acceleration.** -/
lemma H2_accel_bound {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ x : ℝ, ‖deriv (deriv r) x‖ ≤ K := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_iteratedDeriv_knot hr 2
  refine ⟨max B 1, le_max_right _ _, fun x => ?_⟩
  have h1 : iteratedDeriv 2 r = deriv (deriv r) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  rw [← h1]
  exact le_trans (hB x) (le_max_left _ _)

theorem baseHeight_lower {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ
      ![deriv r t, deriv (deriv r) t])
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ Λ : ℝ, 0 < Λ ∧ Λ < 1 / 2 ∧
        ∀ lam δ₁ δ₂ : ℝ, 0 < lam → lam ≤ Λ → 0 < δ₁ → δ₁ ≤ Λ → 0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ v : LeanEval.KnotTheory.Quadrisecant.Space, ‖v‖ = 1 →
          Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
          c * (Work.Drive.sweepW' D ε) ^ 2 ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
  -- a positive global bound for the acceleration
  obtain ⟨K, hK1, hKb⟩ := H2_accel_bound hr
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  -- the transverse frame at the collapsed end and the half-space constant
  set e₀ : Space := Work.Drive.Generic.nclmE0 r D with he₀
  set T : Space := Work.Drive.Generic.nclmT r D with hT
  set b₀ : Space := Work.Drive.Generic.nclmB0 r D with hb₀
  set κ : ℝ := inner ℝ e₀ (deriv (deriv r) (Work.Drive.taR D 0)) with hκ
  have hκpos : 0 < κ := by
    have h1 : inner ℝ (deriv (deriv r) (Work.Drive.taR D 0)) (Work.Drive.Generic.nclmE0 r D)
        = ‖Work.Drive.Generic.nclmW r D‖ :=
      Work.Drive.Generic.nclm_inner_r''_E0 hr hinfl D
    rw [hκ, he₀, real_inner_comm, h1]
    exact norm_pos_iff.mpr (Work.Drive.Generic.nclmW_ne_zero hr hinfl D)
  -- the smallness radius of the direction window
  set sg : ℝ := min 1 (κ / (256 * K)) with hsg
  have hsg0 : 0 < sg := lt_min one_pos (by positivity)
  have hsgK : sg * K ≤ κ / 256 := by
    rw [hsg]
    have h1 : min (1 : ℝ) (κ / (256 * K)) ≤ κ / (256 * K) := min_le_right _ _
    calc min (1 : ℝ) (κ / (256 * K)) * K ≤ (κ / (256 * K)) * K :=
          mul_le_mul_of_nonneg_right h1 hK0.le
      _ = κ / 256 := by field_simp
  -- the direction window and the definite half-space on the window's arcs
  obtain ⟨εW, hεW0, hεW1, hwds⟩ := Work.Drive.windowDataSmall hr D sg hsg0
  obtain ⟨εA, hεA0, hεA12, hAcc⟩ :=
    Work.Drive.Generic.nclm_acc hr D (e₀ := e₀) (by rw [← hκ]; exact hκpos)
  refine ⟨κ / 256, by positivity, min (min εA εW) (1 / 2),
    lt_min (lt_min hεA0 hεW0) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro ε hε0 hεle
  have hεA' : ε ≤ εA := le_trans hεle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεW' : ε ≤ εW := le_trans hεle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεhalf : ε ≤ 1 / 2 := le_trans hεle (min_le_right _ _)
  have hε1 : ε < 1 := by linarith
  obtain ⟨Λw, hΛw0, hΛw⟩ := Work.Drive.Generic.nclm_window_eps D hε0 hε1
  refine ⟨min (min Λw (period / 16)) (1 / 4), lt_min (lt_min hΛw0 (by linarith [period_pos]))
    (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  have hΛlew : min (min Λw (period / 16)) (1 / 4) ≤ Λw :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hΛ16 : min (min Λw (period / 16)) (1 / 4) ≤ period / 16 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hΛ14 : min (min Λw (period / 16)) (1 / 4) ≤ 1 / 4 := min_le_right _ _
  intro lam δ₁ δ₂ hlam0 hlamΛ hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε
  have hδ₂Λw : δ₂ ≤ Λw := le_trans hδ₂Λ hΛlew
  have hδ₁16 : δ₁ ≤ period / 16 := le_trans hδ₁Λ hΛ16
  have hδ₁4 : δ₁ ≤ period / 4 := by linarith [period_pos]
  have hlam12 : lam < 1 / 2 := by linarith
  have hlam1 : lam ≤ 1 := by linarith
  intro v hv hcv
  -- the chord vector, its non-vanishing, and `v` as its unit direction
  set C : Space := Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε with hC
  obtain ⟨-, hCne, hdir⟩ := hwds δ₂ ε hδ₂0 hδ₂ε hε0 hεW'
  have hCne' : C ≠ 0 := by
    rw [hC]
    exact sub_ne_zero.mpr hCne
  have hvunit : v = ‖C‖⁻¹ • C := by
    have h2 : ‖C‖ ≠ 0 := norm_ne_zero_iff.mpr hCne'
    have hgen : ∀ x : Space, x = ‖C‖ • v → ‖C‖⁻¹ • x = v := fun x hx => by
      rw [hx, smul_smul, inv_mul_cancel₀ h2, one_smul]
    exact (hgen C hcv).symm
  have hTval : T = (‖deriv r (Work.Drive.taR D 0)‖)⁻¹ • deriv r (Work.Drive.taR D 0) := rfl
  have hdir' : ‖v - T‖ ≤ sg := by
    rw [hvunit, hTval]
    exact hdir
  have hdve : |inner ℝ v e₀| ≤ sg := by
    have hT0 : inner ℝ T e₀ = 0 := by
      rw [hT, he₀, real_inner_comm]
      exact Work.Drive.Generic.nclm_inner_E0_T hr hinfl D
    have h1 : inner ℝ v e₀ = inner ℝ (v - T) e₀ := by
      rw [inner_sub_left, hT0, sub_zero]
    rw [h1]
    calc |inner ℝ (v - T) e₀| ≤ ‖v - T‖ * ‖e₀‖ := abs_real_inner_le_norm _ _
      _ = ‖v - T‖ := by rw [he₀, Work.Drive.Generic.nclmE0_norm hr hinfl D, mul_one]
      _ ≤ sg := hdir'
  have hdvb : |inner ℝ v b₀| ≤ sg := by
    have hT0 : inner ℝ T b₀ = 0 := by
      rw [hT, hb₀, real_inner_comm]
      exact Work.Drive.Generic.nclm_inner_T_B0 hr hinfl D
    have h1 : inner ℝ v b₀ = inner ℝ (v - T) b₀ := by
      rw [inner_sub_left, hT0, sub_zero]
    rw [h1]
    calc |inner ℝ (v - T) b₀| ≤ ‖v - T‖ * ‖b₀‖ := abs_real_inner_le_norm _ _
      _ = ‖v - T‖ := by rw [hb₀, Work.Drive.Generic.nclmB0_norm hr hinfl D, mul_one]
      _ ≤ sg := hdir'
  -- the window data
  have hWεpos : 0 < Work.Drive.sweepW' D ε := Work.Drive.wds_sweepW'_pos D hε0 hε1
  have hwslo : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      Work.Drive.sweepW' D ε / 2 ≤ Work.Drive.sweepW' D σ :=
    fun σ h1 h2 => (hΛw δ₂ σ hδ₂0 hδ₂Λw hδ₂ε h1 h2).1
  have hwshi : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      Work.Drive.sweepW' D σ ≤ 2 * Work.Drive.sweepW' D ε :=
    fun σ h1 h2 => (hΛw δ₂ σ hδ₂0 hδ₂Λw hδ₂ε h1 h2).2.1
  have hwpos : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → 0 ≤ Work.Drive.sweepW' D σ :=
    fun σ h1 h2 => le_of_lt (lt_of_lt_of_le (by positivity) (hwslo σ h1 h2))
  -- the deviation estimates, uniformly on the window
  have hdev : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ : ℝ, ξ ∈ Set.Icc (0 : ℝ) 1 →
      ξ * (1 - ξ) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * (κ / 2)
          ≤ inner ℝ (Work.Drive.loopDev r D σ ξ) (-e₀) ∧
      |inner ℝ (Work.Drive.loopDev r D σ ξ) b₀|
          ≤ ξ * (1 - ξ) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * K ∧
      |inner ℝ (Work.Drive.loopDev r D σ ξ) v|
          ≤ ξ * (1 - ξ) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * K ∧
      ‖Work.Drive.loopDev r D σ ξ‖
          ≤ ξ * (1 - ξ) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * K := by
    intro σ hσ1 hσ2 ξ hξ
    have hWpos : 0 < Work.Drive.sweepW' D σ :=
      Work.Drive.Generic.nclm_window_wpos D hδ₂0 hδ₂ε hε0 hεhalf hσ1 hσ2
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hbd : ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
          inner ℝ (deriv (deriv r) x) (-e₀) ≤ -(κ / 2) := by
        intro x hx
        have h1 : κ / 2 ≤ inner ℝ e₀ (deriv (deriv r) x) :=
          hAcc δ₂ ε σ x hδ₂0 hδ₂ε hε0 hεA' hσ1 hσ2 hx
        rw [inner_neg_right, real_inner_comm]
        linarith
      have h := Work.Drive.Generic.nclm_dev_scalar_ge (D := D) (r := r) hr
        (y := -e₀) (c := κ / 2) hWpos hξ hbd
      simpa using h
    · refine Work.Drive.Generic.nclm_dev_scalar_le (D := D) (r := r) hr (y := b₀) (B := K)
        hWpos hξ ?_
      intro x hx
      calc |inner ℝ (deriv (deriv r) x) b₀| ≤ ‖deriv (deriv r) x‖ * ‖b₀‖ :=
            abs_real_inner_le_norm _ _
        _ = ‖deriv (deriv r) x‖ := by
            rw [hb₀, Work.Drive.Generic.nclmB0_norm hr hinfl D, mul_one]
        _ ≤ K := hKb x
    · refine Work.Drive.Generic.nclm_dev_scalar_le (D := D) (r := r) hr (y := v) (B := K)
        hWpos hξ ?_
      intro x hx
      calc |inner ℝ (deriv (deriv r) x) v| ≤ ‖deriv (deriv r) x‖ * ‖v‖ :=
            abs_real_inner_le_norm _ _
        _ = ‖deriv (deriv r) x‖ := by rw [hv, mul_one]
        _ ≤ K := hKb x
    · by_cases h0 : Work.Drive.loopDev r D σ ξ = 0
      · have h1 : 0 ≤ ξ * (1 - ξ) := mul_nonneg hξ.1 (by linarith [hξ.2])
        have h2 : 0 ≤ ξ * (1 - ξ) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * K :=
          mul_nonneg (mul_nonneg (div_nonneg h1 (by norm_num)) (sq_nonneg _)) hK0.le
        rw [h0, norm_zero]
        exact h2
      · set y : Space := (‖Work.Drive.loopDev r D σ ξ‖)⁻¹ • Work.Drive.loopDev r D σ ξ with hy
        have hyn : ‖y‖ = 1 := by
          rw [hy, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
            inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]
        have hbd : ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
            |inner ℝ (deriv (deriv r) x) y| ≤ K := by
          intro x hx
          calc |inner ℝ (deriv (deriv r) x) y| ≤ ‖deriv (deriv r) x‖ * ‖y‖ :=
                abs_real_inner_le_norm _ _
            _ = ‖deriv (deriv r) x‖ := by rw [hyn, mul_one]
            _ ≤ K := hKb x
        have h := Work.Drive.Generic.nclm_dev_scalar_le (D := D) (r := r) hr (y := y) (B := K)
          hWpos hξ hbd
        have hval : inner ℝ (Work.Drive.loopDev r D σ ξ) y
            = ‖Work.Drive.loopDev r D σ ξ‖ := by
          rw [hy, real_inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp
        rwa [hval, abs_of_nonneg (norm_nonneg _)] at h
  -- the chart identity
  have hid : ∀ y : Space, inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) y
      = Work.Drive.Generic.bumpAvg₂ (fun v' u =>
          inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (Work.Drive.Generic.arcFracQ lam δ₁ u)) y
            - inner ℝ v y * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
                (Work.Drive.Generic.arcFracQ lam δ₁ u)) v) := by
    intro y
    rw [Work.Drive.Generic.nclm_chartUp_inner hr.smooth.continuous D hlam12 hδ₁0 hδ₁4 hv hcv y]
    unfold Work.Drive.Generic.bumpAvg₂
    refine intervalIntegral.integral_congr (fun v' _ => ?_)
    congr 1
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
    simp only [Work.Drive.Generic.arcFrac_quarter_eq hδ₁0 hδ₁4 hu]
  -- the chart bound
  have hbounds := (Work.Drive.Generic.nclm_chartUp_bounds (r := r) (d := d) hr D (hv := hv)
      (hid := hid) (hlam0 := hlam0.le) (hlam1 := hlam1) (hδ₁0 := hδ₁0) (hδ₁16 := hδ₁16)
      (hδ₂0 := hδ₂0.le) (hwpos := hwpos) (hW := hWεpos) (hc := by positivity)
      (hK := hK0.le) (hKn := hK0.le) (hwslo := hwslo) (hwshi := hwshi)
      (W := Work.Drive.sweepW' D ε) (c := κ / 2) (K := K) (Kn := K) (dve := sg) (dvb := sg)
      (hdev := hdev) (hdve := hdve) (hdvb := hdvb)).1
  have hstep : κ / 256 * (Work.Drive.sweepW' D ε) ^ 2
      ≤ inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) (-e₀) := by
    have h2 : (Work.Drive.sweepW' D ε) ^ 2 * sg * K / 2
        ≤ (Work.Drive.sweepW' D ε) ^ 2 * (κ / 256) / 2 := by
      have h3 : (Work.Drive.sweepW' D ε) ^ 2 * (sg * K)
          ≤ (Work.Drive.sweepW' D ε) ^ 2 * (κ / 256) :=
        mul_le_mul_of_nonneg_left hsgK (sq_nonneg _)
      linarith [h3]
    nlinarith [hbounds, h2, sq_nonneg (Work.Drive.sweepW' D ε), hκpos]
  calc κ / 256 * (Work.Drive.sweepW' D ε) ^ 2
      ≤ inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) (-e₀) := hstep
    _ ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
        have h := real_inner_le_norm (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) (-e₀)
        rw [norm_neg, he₀, Work.Drive.Generic.nclmE0_norm hr hinfl D, mul_one] at h
        exact h

end

end Work.Drive.H2
