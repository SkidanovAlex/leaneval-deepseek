import Mathlib
import Submission.Work.Drive.Generic.nclmPkg
import Submission.Work.Drive.Generic.nclm_blur_close_scale
import Submission.Work.Drive.Generic.nclmWindow
import Submission.Work.Drive.Generic.nclmDev
import Submission.Work.Drive.Generic.nclmBasic
import Submission.Work.Drive.Generic.nclmChart
import Submission.Work.Drive.AB.windowDataSmall
import Submission.Work.Drive.H2.chartE_accel_neg
import Submission.Work.Drive.H2.baseHeight_lower
import Submission.Work.Drive.CDC.glue
import Submission.Work.Drive.CDC.cdc_aux
import Submission.Work.Drive.CDC.cdc_endpointChart

/-!
# The endpoint package of the needle's chart data

`Work.Drive.Generic.nclmPkgEndpoints` collects the *positional* clauses of the needle's chart: the
bound `|H̃| ≤ 2 ‖chartUp‖` of the arc's height profile (against the chart's centre), and the twelve
inequalities of the arc's and the chord's endpoints.

The twelve endpoint inequalities are the content of `Work.Drive.CDC.cdc_endpointChart` (proved in
that module); the height-profile bound is proved here (`Work.Drive.Generic.nclm_H_bound`).

The height bound is the only *sharp* clause of the package: unlike the twelve inequalities, whose
margins are of order `W` (or `‖chartUp‖`), it compares two quantities that are both of order `W ^ 2`
— the height `H̃` of the raw arc above the chart's centre and the chart's height `‖chartUp‖`.  The
mechanism is the *signed* deviation structure of the arc:

* `⟪loopDev (σ, ξ), chartE⟫ = -(ξ (1-ξ)/2) * W(σ)^2 * ⟪r'' (ζ), chartE⟫` for a point `ζ` of the
  retained arc, and the acceleration against the chart direction has a *definite sign*
  (`⟪r'' (x), chartE⟫ ≤ -c < 0` on the window's arcs, the absence of inflections);
* consequently the raw arc lies on one side of the chart's chord, its height above the chart's
  centre is between `-‖chartUp‖/2` and `‖chartUp‖/2` up to an error of order `W ^ 3`, and the
  weighted average that produces `chartUp` (the `σ`- and `δ₁`-blur of the arc's midpoint) is at
  least `(3/32) (1-η)^2 W^2 c₀` — the same order as the height itself.
-/

noncomputable section
namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

set_option maxHeartbeats 3000000

variable {r : ℝ → Space} {d : BandArcData}

/-- **The chart height is bounded below by the signed deviation of the arc.**  If the acceleration
against the chart direction `chartE` is at most `-c₀` on the whole window's arcs, then the weighted
average `⟪chartUp, chartE⟫ = ‖chartUp‖` of the signed deviations is at least
`(3/32) (1 - η)^2 W^2 c₀`, where `W` is the reference width at `ε` and `(1 - η) W` bounds the
widths of the window below.

The arc fraction of the blurred middle lies in `[1/4, 3/4]`, hence `ξ (1-ξ)/2 ≥ 3/32`; this is the
only numerical input. -/
lemma nclm_chartUp_chartE_lower {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) {lam δ₁ δ₂ ε c₀ η W : ℝ} {v : Space}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1 / 2) (hδ₁0 : 0 < δ₁) (hδ₁16 : δ₁ ≤ period / 16)
    (hv : ‖v‖ = 1)
    (hb : Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v)
    (hδ₂0 : 0 < δ₂) (hWpos : 0 < W) (hc₀ : 0 ≤ c₀) (hη1 : η ≤ 1)
    (hwin : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → (1 - η) * W ≤ Work.Drive.sweepW' D σ)
    (hdev : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
      (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * c₀
        ≤ inner ℝ (Work.Drive.loopDev r D σ ξ) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)) :
    (3 / 32) * (1 - η) ^ 2 * W ^ 2 * c₀
      ≤ inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)
          (Work.Drive.chartE r D lam δ₁ δ₂ ε v) := by
  have hδ₁4 : δ₁ ≤ period / 4 := by
    have hp : (0 : ℝ) < period := period_pos
    linarith
  have hEv : inner ℝ v (Work.Drive.chartE r D lam δ₁ δ₂ ε v) = 0 :=
    cdc_nclm_inner_v_chartE D lam δ₁ δ₂ ε hv
  have hid := H2.chartUp_inner_arcFracQ (r := r) hr (D := D) (v := v) hlam1 hδ₁0 hδ₁4 hv hb
    (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
  rw [hid, H2.bumpAvg₂_congr_Icc (fun v' _ u _ => by rw [hEv, zero_mul, sub_zero])]
  have hg : Continuous (Function.uncurry (fun v' u : ℝ =>
      inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u))
        (Work.Drive.chartE r D lam δ₁ δ₂ ε v))) :=
    (continuous_loopDevQ hr.continuous D lam δ₁ δ₂ ε).inner continuous_const
  have hpt : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      (3 / 32) * (1 - η) ^ 2 * W ^ 2 * c₀
        ≤ inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u))
            (Work.Drive.chartE r D lam δ₁ δ₂ ε v) := by
    intro v' hv' u hu
    have hσ1 : ε - δ₂ ≤ ε - δ₂ * v' := by nlinarith [hδ₂0, hv'.2]
    have hσ2 : ε - δ₂ * v' ≤ ε + δ₂ := by nlinarith [hδ₂0, hv'.1]
    have hξ : arcFracQ lam δ₁ u ∈ Set.Icc (0 : ℝ) 1 := by
      obtain ⟨h1, h2⟩ := arcFracQ_mem hlam0 (by linarith) hδ₁0 hδ₁16 hu
      exact ⟨by linarith, by linarith⟩
    have hφ : (3 / 32 : ℝ) ≤ arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) / 2 := by
      obtain ⟨h1, h2⟩ := arcFracQ_mem hlam0 (by linarith) hδ₁0 hδ₁16 hu
      nlinarith
    have hw := hwin _ hσ1 hσ2
    have hw2 : ((1 - η) * W) ^ 2 ≤ (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (1 - η) * W := mul_nonneg (by linarith [hη1]) hWpos.le
      exact pow_le_pow_left₀ h0 hw 2
    have hdev' := hdev _ hσ1 hσ2 _ hξ
    calc (3 / 32) * (1 - η) ^ 2 * W ^ 2 * c₀
        = (3 / 32) * ((1 - η) * W) ^ 2 * c₀ := by ring
      _ ≤ (arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) / 2)
            * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 * c₀ := by
          refine mul_le_mul_of_nonneg_right ?_ hc₀
          exact mul_le_mul hφ hw2 (sq_nonneg _)
            (mul_nonneg (mul_nonneg hξ.1 (by linarith [hξ.2])) (by norm_num))
      _ ≤ inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u))
            (Work.Drive.chartE r D lam δ₁ δ₂ ε v) := hdev'
  exact bumpAvg₂_ge' hg hpt


/-- **The height profile of the retained arc, against the chart's centre.**  For every box of the
window, the height `H̃` of the arc point at every fraction `ξ ∈ [lam, 1-lam]` above the chart's
centre is bounded by twice the chart's height `‖chartUp‖`.

The proof: the chart direction `E` satisfies `⟪r'' (x), E⟫ ≤ -c₀ < 0` on the whole window
(`H2.chartE_accel_neg`), so the *signed* deviation bound `nclm_dev_scalar_ge` gives
`⟪loopDev (σ, ξ), E⟫ ≥ (ξ (1-ξ)/2) w(σ)^2 c₀ ≥ 0` (the arc lies on one side of the chord), while
`nclm_dev_scalar_le` bounds it above by the same expression with `s₀ + ε₁` in place of `c₀`.  The
two constants differ by the Lipschitz variation of `r''` across the window's arcs, which is
`ε₁ = CL (1+2η) W ≪ c₀` because the arcs are all within `(1+2η) W` of each other (the sharp window
`cdc_window_sharp`) and `W` is small.  The weighted average `⟪chartUp, E⟫ = ‖chartUp‖` is then at
least `(3/32) (1-η)^2 W^2 c₀` by `nclm_chartUp_chartE_lower`, which is the same order as the arc's
height, and the numerical bookkeeping closes. -/
theorem nclm_H_bound {r : ℝ → Space} (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ Λ : ℝ, 0 < Λ ∧
        ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
          0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ (v : LeanEval.KnotTheory.Quadrisecant.Space), ‖v‖ = 1 →
          Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
        ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          ∀ ξ ∈ Set.Icc lam (1 - lam),
            |nclmAH r D lam δ₁ δ₂ ε σ v ξ| ≤ 2 * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
  obtain ⟨K, hK1, hKb⟩ := H2.H2_accel_bound (r := r) hr
  obtain ⟨C₀, hC₀0, hC₀⟩ := nclm_lipschitz_r'' (r := r) hr
  set CL : ℝ := C₀ + 1 with hCLdef
  obtain ⟨cA, hcA0, εA, hεA0, hεA12, haccE⟩ := H2.chartE_accel_neg (r := r) hr hinfl (D := D)
  obtain ⟨cB, hcB0, εB, hεB0, hεB1, hbaseH⟩ := H2.baseHeight_lower (r := r) hr hinfl (D := D)
  set η : ℝ := 1 / 64 with hηdef
  have hη0 : 0 < η := by rw [hηdef]; norm_num
  have hη1 : η ≤ 1 := by rw [hηdef]; norm_num
  set c : ℝ := cA / 128 with hcdef
  have hc0 : 0 < c := by rw [hcdef]; linarith
  obtain ⟨εG, hεG0, hεG⟩ := nclm_blur_close_scale (r := r) hr D c hc0
  set Wmax : ℝ := cA / (8 * CL * (1 + 2 * η)) with hWmaxdef
  have hWmax0 : 0 < Wmax := by rw [hWmaxdef]; positivity
  obtain ⟨εS, hεS0, hεS⟩ := cdc_window_small (d := d) D hWmax0
  refine ⟨min (min (min εA εB) (min εG εS)) (1 / 4),
    lt_min (lt_min (lt_min hεA0 hεB0) (lt_min hεG0 hεS0)) (by norm_num), ?_⟩
  intro ε hε0 hεle
  have hεA' : ε ≤ εA :=
    le_trans hεle (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hεB' : ε ≤ εB :=
    le_trans hεle (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hεG' : ε ≤ εG :=
    le_trans hεle (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hεS' : ε ≤ εS :=
    le_trans hεle (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hε14 : ε ≤ 1 / 4 := le_trans hεle (min_le_right _ _)
  have hε1 : ε < 1 := by linarith
  set W : ℝ := Work.Drive.sweepW' D ε with hWdef
  have hWpos : 0 < W := by
    rw [hWdef]; exact Work.Drive.wds_sweepW'_pos D hε0 hε1
  have hWle : W ≤ Wmax := by rw [hWdef]; exact hεS ε hε0 hεS'
  obtain ⟨Λw, hΛw0, -, hΛw⟩ := CDC.cdc_window_sharp (d := d) D hε0 hε1 hη0
  obtain ⟨ΛA, hΛA0, -, hΛA1⟩ := haccE ε hε0 hεA'
  obtain ⟨ΛB, hΛB0, -, hΛB1⟩ := hbaseH ε hε0 hεB'
  obtain ⟨ΛG, hΛG0, hΛG1⟩ := hεG ε hε0 hεG'
  set Λ : ℝ := min (min Λw (min ΛA ΛB)) (min ΛG (min (period / 16) (period / 4))) with hΛdef
  have hΛpos : 0 < Λ := by
    rw [hΛdef]
    have hp16 : (0:ℝ) < period / 16 := by linarith [period_pos]
    have hp4 : (0:ℝ) < period / 4 := by linarith [period_pos]
    exact lt_min (lt_min hΛw0 (lt_min hΛA0 hΛB0)) (lt_min hΛG0 (lt_min hp16 hp4))
  refine ⟨Λ, hΛpos, ?_⟩
  have hΛw' : Λ ≤ Λw := by rw [hΛdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hΛA' : Λ ≤ ΛA := by
    rw [hΛdef]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hΛB' : Λ ≤ ΛB := by
    rw [hΛdef]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hΛG' : Λ ≤ ΛG := by rw [hΛdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hΛ16 : Λ ≤ period / 16 := by
    rw [hΛdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hΛ4 : Λ ≤ period / 4 := by
    rw [hΛdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  intro lam δ₁ δ₂ hlam0 hlamΛ hlam12 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε
  have hlamΛw : lam ≤ Λw := le_trans hlamΛ hΛw'
  have hlamΛA : lam ≤ ΛA := le_trans hlamΛ hΛA'
  have hlamΛB : lam ≤ ΛB := le_trans hlamΛ hΛB'
  have hδ₁ΛA : δ₁ ≤ ΛA := le_trans hδ₁Λ hΛA'
  have hδ₁ΛB : δ₁ ≤ ΛB := le_trans hδ₁Λ hΛB'
  have hδ₁16 : δ₁ ≤ period / 16 := le_trans hδ₁Λ hΛ16
  have hδ₁4 : δ₁ ≤ period / 4 := le_trans hδ₁Λ hΛ4
  have hδ₂Λw : δ₂ ≤ Λw := le_trans hδ₂Λ hΛw'
  have hδ₂ΛA : δ₂ ≤ ΛA := le_trans hδ₂Λ hΛA'
  have hδ₂ΛB : δ₂ ≤ ΛB := le_trans hδ₂Λ hΛB'
  have hδ₂ΛG : δ₂ ≤ ΛG := le_trans hδ₂Λ hΛG'
  have hwσ : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      |Work.Drive.sweepW' D σ - W| ≤ η * W ∧
        |Work.Drive.taR D σ - Work.Drive.taR D ε| ≤ η * W := by
    intro σ h1 h2
    have h := hΛw δ₂ σ hδ₂0 hδ₂Λw h1 h2
    exact ⟨by simpa [hWdef] using h.1, by simpa [hWdef] using h.2.1⟩
  have hwinlo : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → (1 - η) * W ≤ Work.Drive.sweepW' D σ := by
    intro σ h1 h2
    have h := (abs_le.mp (hwσ σ h1 h2).1).1
    linarith
  intro v hv hb
  set E : Space := Work.Drive.chartE r D lam δ₁ δ₂ ε v with hEdef
  set hh : ℝ := ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ with hhdef
  have hhpos : 0 < hh := by
    have h := hΛB1 lam δ₁ δ₂ hlam0 hlamΛB hδ₁0 hδ₁ΛB hδ₂0 hδ₂ΛB hδ₂ε v hv hb
    have h2 : 0 < cB * (Work.Drive.sweepW' D ε) ^ 2 :=
      mul_pos hcB0 (pow_pos (by rw [← hWdef]; exact hWpos) 2)
    rw [hhdef]
    linarith
  have hup : Work.Drive.chartUp r D lam δ₁ δ₂ ε v ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hhpos)
  have hEnorm : ‖E‖ = 1 := by rw [hEdef]; exact cdc_nclm_chartE_norm D hup
  have hEv : inner ℝ E v = 0 := by rw [hEdef]; exact cdc_nclm_chartE_inner_v D lam δ₁ δ₂ ε hv
  have hEv' : inner ℝ v E = 0 := by rw [real_inner_comm]; exact hEv
  have hEE : inner ℝ E E = 1 := by rw [real_inner_self_eq_norm_sq, hEnorm]; norm_num
  have hhE : inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) E = hh := by
    rw [hEdef, hhdef]; exact cdc_nclm_chartUp_inner_chartE D lam δ₁ δ₂ ε hup
  -- the acceleration of the reference point of the window's arcs
  have hs₀ : cA ≤ -inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E := by
    have h := hΛA1 lam δ₁ δ₂ hlam0 hlamΛA hδ₁0 hδ₁ΛA hδ₂0 hδ₂ΛA hδ₂ε v hv hb ε
      (by linarith) (by linarith) (Work.Drive.taR D ε) le_rfl ?_
    · have hiter : iteratedDeriv 2 r (Work.Drive.taR D ε)
          = deriv (deriv r) (Work.Drive.taR D ε) := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
      rw [hiter] at h
      rw [hEdef]
      linarith
    · have h := hWpos
      rw [hWdef, Work.Drive.sweepW'] at h
      linarith
  set s₀ : ℝ := -inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E with hs₀def
  have hs₀cA : cA ≤ s₀ := hs₀
  set ε₁ : ℝ := CL * (1 + 2 * η) * W with hε₁def
  have hε₁0 : 0 ≤ ε₁ := by rw [hε₁def]; positivity
  have hCL0 : 0 < CL := by rw [hCLdef]; linarith
  have hε₁le : ε₁ ≤ cA / 8 := by
    have h1 : CL * (1 + 2 * η) * W ≤ CL * (1 + 2 * η) * Wmax :=
      mul_le_mul_of_nonneg_left hWle (by positivity)
    have h2 : CL * (1 + 2 * η) * Wmax = cA / 8 := by
      rw [hWmaxdef]
      field_simp
    rw [hε₁def]
    exact le_trans h1 h2.le
  set c₀ : ℝ := s₀ - ε₁ with hc₀def
  have hs₀pos : 0 < s₀ := lt_of_lt_of_le hcA0 hs₀cA
  have hc₀ge : 7 * cA / 8 ≤ c₀ := by rw [hc₀def]; linarith [hs₀cA, hε₁le]
  have hc₀pos : 0 < c₀ := lt_of_lt_of_le (by linarith : (0:ℝ) < 7 * cA / 8) hc₀ge
  have hc₀nn : 0 ≤ c₀ := hc₀pos.le
  have hε₁s₀ : 8 * ε₁ ≤ s₀ := by linarith [hs₀cA, hε₁le]
  have hs₀c₀ : s₀ + ε₁ ≤ (9 / 7) * c₀ := by
    rw [hc₀def]; linarith [hε₁s₀]
  have hc_le : c ≤ c₀ / 112 := by
    rw [hcdef]; linarith [hc₀ge, hcA0]
  -- the variation of the acceleration across the window's arcs
  have hvar : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
        |inner ℝ (deriv (deriv r) x) E
            - inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E| ≤ ε₁ := by
    intro σ h1 h2 x hx
    have hspread : |x - Work.Drive.taR D ε| ≤ (1 + 2 * η) * W := by
      have hta := (hwσ σ h1 h2).2
      have hw := (hwσ σ h1 h2).1
      have hwle : Work.Drive.sweepW' D σ ≤ (1 + η) * W := by
        have := (abs_le.mp hw).2; linarith
      have hxw : |x - Work.Drive.taR D σ| ≤ Work.Drive.sweepW' D σ := by
        have hsweq : Work.Drive.sweepW' D σ
            = Work.Drive.tbR D σ - Work.Drive.taR D σ := rfl
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2, hsweq]
      have hsum : x - Work.Drive.taR D ε
          = (x - Work.Drive.taR D σ) + (Work.Drive.taR D σ - Work.Drive.taR D ε) := by ring
      calc |x - Work.Drive.taR D ε|
          = |(x - Work.Drive.taR D σ) + (Work.Drive.taR D σ - Work.Drive.taR D ε)| := by
            rw [hsum]
        _ ≤ |x - Work.Drive.taR D σ| + |Work.Drive.taR D σ - Work.Drive.taR D ε| :=
            abs_add_le _ _
        _ ≤ Work.Drive.sweepW' D σ + η * W := by linarith
        _ ≤ (1 + η) * W + η * W := by linarith
        _ = (1 + 2 * η) * W := by ring
    rw [← inner_sub_left]
    calc |inner ℝ (deriv (deriv r) x - deriv (deriv r) (Work.Drive.taR D ε)) E|
        ≤ ‖deriv (deriv r) x - deriv (deriv r) (Work.Drive.taR D ε)‖ * ‖E‖ :=
          abs_real_inner_le_norm _ _
      _ = ‖deriv (deriv r) x - deriv (deriv r) (Work.Drive.taR D ε)‖ := by rw [hEnorm, mul_one]
      _ ≤ C₀ * |x - Work.Drive.taR D ε| := hC₀ x _
      _ ≤ C₀ * ((1 + 2 * η) * W) := mul_le_mul_of_nonneg_left hspread hC₀0.le
      _ ≤ CL * (1 + 2 * η) * W := by
          have h0 : 0 ≤ (1 + 2 * η) * W := by positivity
          rw [hCLdef]
          nlinarith [h0]
  have hacc₀ : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
        inner ℝ (deriv (deriv r) x) E ≤ -c₀ := by
    intro σ h1 h2 x hx
    have hv' := (abs_le.mp (hvar σ h1 h2 x hx)).2
    have hb' : inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E = -s₀ := by
      rw [hs₀def]; ring
    have hsplit : inner ℝ (deriv (deriv r) x) E
        = inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E
          + (inner ℝ (deriv (deriv r) x) E
            - inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E) := by ring
    rw [hsplit, hb', hc₀def]
    linarith
  have haccS : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
        |inner ℝ (deriv (deriv r) x) E| ≤ s₀ + ε₁ := by
    intro σ h1 h2 x hx
    have hv' := hvar σ h1 h2 x hx
    have hb' : |inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E| = s₀ := by
      have : inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E = -s₀ := by
        rw [hs₀def]; ring
      rw [this, abs_neg, abs_of_pos hs₀pos]
    have haux : |inner ℝ (deriv (deriv r) x) E|
        ≤ |inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E|
          + |inner ℝ (deriv (deriv r) x) E
            - inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E| := by
      have h := abs_add_le (inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E)
        (inner ℝ (deriv (deriv r) x) E
          - inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E)
      have heq : inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E
          + (inner ℝ (deriv (deriv r) x) E
            - inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E)
          = inner ℝ (deriv (deriv r) x) E := by ring
      rwa [heq] at h
    calc |inner ℝ (deriv (deriv r) x) E|
        ≤ |inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E|
          + |inner ℝ (deriv (deriv r) x) E
            - inner ℝ (deriv (deriv r) (Work.Drive.taR D ε)) E| := haux
      _ ≤ s₀ + ε₁ := by rw [hb']; linarith only [hv']
  -- the two signed deviation bounds of the arc against the chart direction
  have hdevLo : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
      (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * c₀
        ≤ inner ℝ (Work.Drive.loopDev r D σ ξ) E := by
    intro σ h1 h2 ξ hξ
    have hw : 0 < Work.Drive.sweepW' D σ := by
      have h1' : (0:ℝ) < (1 - η) * W := mul_pos (by rw [hηdef]; norm_num) hWpos
      linarith only [h1', hwinlo σ h1 h2]
    exact nclm_dev_scalar_ge (D := D) (r := r) hr (y := E) (c := c₀) (σ := σ) (ξ := ξ)
      hw hξ (fun x hx => hacc₀ σ h1 h2 x hx)
  have hdevHi : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
      inner ℝ (Work.Drive.loopDev r D σ ξ) E
        ≤ (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * (s₀ + ε₁) := by
    intro σ h1 h2 ξ hξ
    have hw : 0 < Work.Drive.sweepW' D σ := by
      have h1' : (0:ℝ) < (1 - η) * W := mul_pos (by rw [hηdef]; norm_num) hWpos
      linarith only [h1', hwinlo σ h1 h2]
    exact le_trans (le_abs_self _) (nclm_dev_scalar_le (D := D) (r := r) hr (y := E)
      (B := s₀ + ε₁) (σ := σ) (ξ := ξ) hw hξ (fun x hx => haccS σ h1 h2 x hx))
  -- the chart height is of the same order
  have hbase : (3 / 32) * (1 - η) ^ 2 * W ^ 2 * c₀ ≤ hh := by
    have h := nclm_chartUp_chartE_lower (r := r) hr D (v := v) hlam0.le hlam12 hδ₁0 hδ₁16 hv hb
      hδ₂0 hWpos hc₀nn hη1 hwinlo hdevLo
    rw [hhE] at h
    exact h
  intro σ hσlo hσhi
  -- the endpoint pairings
  have ha₁ : |inner ℝ (r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε)
      E| ≤ c * W ^ 2 := by
    have h := (hΛG1 δ₂ σ hδ₂0 hδ₂ΛG hδ₂ε hσlo hσhi).1
    calc |inner ℝ (r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε) E|
        ≤ ‖r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε‖ * ‖E‖ :=
          abs_real_inner_le_norm _ _
      _ = ‖r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε‖ := by rw [hEnorm, mul_one]
      _ ≤ c * W ^ 2 := by rw [hWdef]; exact h
  have hb₁ : |inner ℝ (r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε)
      E| ≤ c * W ^ 2 := by
    have h := (hΛG1 δ₂ σ hδ₂0 hδ₂ΛG hδ₂ε hσlo hσhi).2.1
    calc |inner ℝ (r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε) E|
        ≤ ‖r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε‖ * ‖E‖ :=
          abs_real_inner_le_norm _ _
      _ = ‖r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε‖ := by rw [hEnorm, mul_one]
      _ ≤ c * W ^ 2 := by rw [hWdef]; exact h
  have hW2 : (0:ℝ) ≤ W ^ 2 := sq_nonneg W
  intro ξ hξ
  have hξ01 : ξ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hξ.1, hlam0], by linarith [hξ.2]⟩
  have hBvE : inner ℝ (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε) E = 0 := by
    rw [hb, real_inner_smul_left, hEv', mul_zero]
  have hdec : Work.Drive.sweepArc' r D σ ξ - Work.Drive.chordEndA r D δ₂ ε
      = Work.Drive.loopDev r D σ ξ
        + (1 - ξ) • (r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε)
        + ξ • (r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε)
        + ξ • (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε) := by
    simp only [Work.Drive.loopDev, Work.Drive.sweepArc']
    module
  have hξ0 : 0 ≤ 1 - ξ := by linarith [hξ.2]
  have hξ1 : 0 ≤ ξ := by linarith [hξ.1, hlam0]
  have harcU : inner ℝ (Work.Drive.sweepArc' r D σ ξ - Work.Drive.chordEndA r D δ₂ ε) E
      ≤ (1 / 8) * (1 + η) ^ 2 * W ^ 2 * (s₀ + ε₁) + c * W ^ 2 := by
    rw [hdec, inner_add_left, inner_add_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left, hBvE, mul_zero, add_zero]
    have hdev := hdevHi σ hσlo hσhi ξ hξ01
    have hwle : Work.Drive.sweepW' D σ ≤ (1 + η) * W := by
      have := (abs_le.mp (hwσ σ hσlo hσhi).1).2; linarith
    have hw0 : 0 ≤ Work.Drive.sweepW' D σ := le_trans (by positivity : (0:ℝ) ≤ (1-η)*W)
      (hwinlo σ hσlo hσhi)
    have hsq : (Work.Drive.sweepW' D σ) ^ 2 ≤ ((1 + η) * W) ^ 2 :=
      pow_le_pow_left₀ hw0 hwle 2
    have hφ : ξ * (1 - ξ) / 2 ≤ (1 / 8 : ℝ) := by
      nlinarith [hξ01.1, hξ01.2, sq_nonneg (ξ - 1 / 2)]
    have hs₀ε₁nn : 0 ≤ s₀ + ε₁ := by linarith [hs₀pos, hε₁0]
    have ha₁' : (1 - ξ) * inner ℝ (r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε) E
        ≤ (1 - ξ) * (c * W ^ 2) :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) ha₁) hξ0
    have hb₁' : ξ * inner ℝ (r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε) E
        ≤ ξ * (c * W ^ 2) :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hb₁) hξ1
    have hstep : (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * (s₀ + ε₁)
        ≤ (1 / 8) * ((1 + η) * W) ^ 2 * (s₀ + ε₁) := by
      have h1 : (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 ≤ (1 / 8) * ((1 + η) * W) ^ 2 :=
        mul_le_mul hφ hsq (sq_nonneg _) (by norm_num)
      exact mul_le_mul_of_nonneg_right h1 hs₀ε₁nn
    have hsum : (1 - ξ) * (c * W ^ 2) + ξ * (c * W ^ 2) = c * W ^ 2 := by ring
    calc inner ℝ (Work.Drive.loopDev r D σ ξ) E
          + (1 - ξ) * inner ℝ (r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε) E
          + ξ * inner ℝ (r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε) E
        ≤ (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * (s₀ + ε₁)
          + (1 - ξ) * (c * W ^ 2) + ξ * (c * W ^ 2) := by linarith [hdev, ha₁', hb₁']
      _ ≤ (1 / 8) * ((1 + η) * W) ^ 2 * (s₀ + ε₁) + c * W ^ 2 := by linarith [hstep, hsum]
      _ = (1 / 8) * (1 + η) ^ 2 * W ^ 2 * (s₀ + ε₁) + c * W ^ 2 := by ring
  have harcL : -c * W ^ 2 ≤
      inner ℝ (Work.Drive.sweepArc' r D σ ξ - Work.Drive.chordEndA r D δ₂ ε) E := by
    rw [hdec, inner_add_left, inner_add_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left, hBvE, mul_zero, add_zero]
    have hdev := hdevLo σ hσlo hσhi ξ hξ01
    have hφnn : 0 ≤ ξ * (1 - ξ) / 2 := by nlinarith [hξ01.1, hξ01.2]
    have hw2nn : 0 ≤ (Work.Drive.sweepW' D σ) ^ 2 := sq_nonneg _
    have hdev' : 0 ≤ inner ℝ (Work.Drive.loopDev r D σ ξ) E := by
      have := mul_nonneg (mul_nonneg hφnn hw2nn) hc₀nn
      linarith [hdev]
    have hsum : -((1 - ξ) * (c * W ^ 2)) + -(ξ * (c * W ^ 2)) = -(c * W ^ 2) := by ring
    have ha₁' : -((1 - ξ) * (c * W ^ 2)) ≤
        (1 - ξ) * inner ℝ (r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε) E := by
      have h1 : -(c * W ^ 2) ≤ inner ℝ (r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε) E := by
        have h := neg_abs_le (inner ℝ (r (Work.Drive.taR D σ) - Work.Drive.chordEndA r D δ₂ ε) E)
        linarith only [h, ha₁]
      have h2 := mul_le_mul_of_nonneg_left h1 hξ0
      have h3 : (1 - ξ) * (-(c * W ^ 2)) = -((1 - ξ) * (c * W ^ 2)) := by ring
      rwa [h3] at h2
    have hb₁' : -(ξ * (c * W ^ 2)) ≤
        ξ * inner ℝ (r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε) E := by
      have h1 : -(c * W ^ 2) ≤ inner ℝ (r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε) E := by
        have h := neg_abs_le (inner ℝ (r (Work.Drive.tbR D σ) - Work.Drive.chordEndB r D δ₂ ε) E)
        linarith only [h, hb₁]
      have h2 := mul_le_mul_of_nonneg_left h1 hξ1
      have h3 : ξ * (-(c * W ^ 2)) = -(ξ * (c * W ^ 2)) := by ring
      rwa [h3] at h2
    linarith only [hdev', ha₁', hb₁', hsum]
  have hnum2 : (1 / 8 : ℝ) * (1 + η) ^ 2 * (9 / 7) + 1 / 112
      ≤ (2 : ℝ) * ((3 / 32 : ℝ) * (1 - η) ^ 2) := by
    rw [hηdef]; norm_num
  have hnum3 : (1 / 112 : ℝ) ≤ (3 / 2 : ℝ) * ((3 / 32 : ℝ) * (1 - η) ^ 2) := by
    rw [hηdef]; norm_num
  have hkey : nclmAH r D lam δ₁ δ₂ ε σ v ξ
      = inner ℝ (Work.Drive.sweepArc' r D σ ξ - Work.Drive.chordEndA r D δ₂ ε) E - hh / 2 := by
    have hcC := cdc_nclm_chartC_sub_chordEndA (r := r) D lam δ₁ δ₂ ε (v := v)
    show inner ℝ (Work.Drive.sweepArc' r D σ ξ - Work.Drive.chartC r D lam δ₁ δ₂ ε v) E = _
    rw [show Work.Drive.sweepArc' r D σ ξ - Work.Drive.chartC r D lam δ₁ δ₂ ε v
        = (Work.Drive.sweepArc' r D σ ξ - Work.Drive.chordEndA r D δ₂ ε)
          - (Work.Drive.chartC r D lam δ₁ δ₂ ε v - Work.Drive.chordEndA r D δ₂ ε)
        from by abel,
      inner_sub_left, hcC, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hEv', hEE, mul_one, mul_zero, zero_add]
    try ring
  rw [hkey, abs_le]
  constructor
  · -- the lower bound
    have h1 : -c * W ^ 2 - hh / 2 ≤ inner ℝ (Work.Drive.sweepArc' r D σ ξ
        - Work.Drive.chordEndA r D δ₂ ε) E - hh / 2 := by linarith [harcL]
    have h2 : -(2 * hh) ≤ -c * W ^ 2 - hh / 2 := by
      have h3 : c * W ^ 2 ≤ (3 / 2) * hh := by
        have h4 : c * W ^ 2 ≤ (c₀ / 112) * W ^ 2 := mul_le_mul_of_nonneg_right hc_le hW2
        have h5 : (c₀ / 112) * W ^ 2 = (1 / 112) * (W ^ 2 * c₀) := by ring
        have h6 : (1 / 112 : ℝ) * (W ^ 2 * c₀)
            ≤ (3 / 2 : ℝ) * ((3 / 32 : ℝ) * (1 - η) ^ 2 * (W ^ 2 * c₀)) := by
          have h := mul_le_mul_of_nonneg_right hnum3 (by positivity : (0:ℝ) ≤ W ^ 2 * c₀)
          have heq : (3 / 2 : ℝ) * ((3 / 32 : ℝ) * (1 - η) ^ 2) * (W ^ 2 * c₀)
              = (3 / 2 : ℝ) * ((3 / 32 : ℝ) * (1 - η) ^ 2 * (W ^ 2 * c₀)) := by ring
          rwa [heq] at h
        have h7 : (3 / 2 : ℝ) * ((3 / 32 : ℝ) * (1 - η) ^ 2 * (W ^ 2 * c₀)) ≤ (3 / 2) * hh := by
          have heq : (3 / 32 : ℝ) * (1 - η) ^ 2 * (W ^ 2 * c₀)
              = (3 / 32) * (1 - η) ^ 2 * W ^ 2 * c₀ := by ring
          rw [heq]
          exact mul_le_mul_of_nonneg_left hbase (by norm_num)
        linarith only [h4, h5, h6, h7]
      linarith only [h3]
    linarith only [h1, h2]
  · -- the upper bound
    have h1 : inner ℝ (Work.Drive.sweepArc' r D σ ξ - Work.Drive.chordEndA r D δ₂ ε) E - hh / 2
        ≤ (1 / 8) * (1 + η) ^ 2 * W ^ 2 * (s₀ + ε₁) + c * W ^ 2 - hh / 2 := by
      linarith [harcU]
    have h2 : (1 / 8) * (1 + η) ^ 2 * W ^ 2 * (s₀ + ε₁) + c * W ^ 2
        ≤ (2 : ℝ) * ((3 / 32) * (1 - η) ^ 2 * W ^ 2 * c₀) := by
      have h4 : (1 / 8) * (1 + η) ^ 2 * W ^ 2 * (s₀ + ε₁)
          ≤ (1 / 8) * (1 + η) ^ 2 * W ^ 2 * ((9 / 7) * c₀) :=
        mul_le_mul_of_nonneg_left hs₀c₀ (by positivity)
      have h5 : c * W ^ 2 ≤ (c₀ / 112) * W ^ 2 := mul_le_mul_of_nonneg_right hc_le hW2
      have h6 : (1 / 8) * (1 + η) ^ 2 * W ^ 2 * ((9 / 7) * c₀) + (c₀ / 112) * W ^ 2
          = ((1 / 8) * (1 + η) ^ 2 * (9 / 7) + 1 / 112) * (W ^ 2 * c₀) := by ring
      have h7 : ((1 / 8) * (1 + η) ^ 2 * (9 / 7) + 1 / 112) * (W ^ 2 * c₀)
          ≤ (2 : ℝ) * ((3 / 32 : ℝ) * (1 - η) ^ 2) * (W ^ 2 * c₀) :=
        mul_le_mul_of_nonneg_right hnum2 (by positivity : (0:ℝ) ≤ W ^ 2 * c₀)
      have h8 : (2 : ℝ) * ((3 / 32 : ℝ) * (1 - η) ^ 2) * (W ^ 2 * c₀)
          = (2 : ℝ) * ((3 / 32) * (1 - η) ^ 2 * W ^ 2 * c₀) := by ring
      linarith only [h4, h5, h6, h7, h8]
    have h3 : hh / 2 ≤ (2 : ℝ) * hh := by linarith only [hhpos]
    have h4 : (2 : ℝ) * ((3 / 32) * (1 - η) ^ 2 * W ^ 2 * c₀) ≤ 2 * hh :=
      mul_le_mul_of_nonneg_left hbase (by norm_num)
    linarith only [h1, h2, h3, h4]


/-- **The endpoint package of the needle's chart data.**

The height-profile bound is `Work.Drive.Generic.nclm_H_bound`; the twelve endpoint inequalities are
`Work.Drive.CDC.cdc_endpointChart`. -/
theorem nclm_clauseEndpoints {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    Work.Drive.Generic.nclmPkgEndpoints r D := by
  obtain ⟨εH, hεH0, hHb⟩ := nclm_H_bound hr hinfl D
  obtain ⟨εE, hεE0, -, hEb⟩ := Work.Drive.CDC.cdc_endpointChart hr hinfl D
  refine ⟨min εH εE, lt_min hεH0 hεE0, ?_⟩
  intro ε hε0 hεle
  have hεH : ε ≤ εH := le_trans hεle (min_le_left _ _)
  have hεE : ε ≤ εE := le_trans hεle (min_le_right _ _)
  obtain ⟨ΛH, hΛH0, hHb'⟩ := hHb ε hε0 hεH
  obtain ⟨ΛE, hΛE0, -, hEb'⟩ := hEb ε hε0 hεE
  refine ⟨min ΛH ΛE, lt_min hΛH0 hΛE0, ?_⟩
  intro lam δ₁ δ₂ hlam0 hlamΛ hlam12 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε
  have hlamΛH : lam ≤ ΛH := le_trans hlamΛ (min_le_left _ _)
  have hlamΛE : lam ≤ ΛE := le_trans hlamΛ (min_le_right _ _)
  have hδ₁ΛH : δ₁ ≤ ΛH := le_trans hδ₁Λ (min_le_left _ _)
  have hδ₁ΛE : δ₁ ≤ ΛE := le_trans hδ₁Λ (min_le_right _ _)
  have hδ₂ΛH : δ₂ ≤ ΛH := le_trans hδ₂Λ (min_le_left _ _)
  have hδ₂ΛE : δ₂ ≤ ΛE := le_trans hδ₂Λ (min_le_right _ _)
  intro v hv hcv
  exact ⟨fun σ h1 h2 ξ hξ => hHb' lam δ₁ δ₂ hlam0 hlamΛH hlam12 hδ₁0 hδ₁ΛH hδ₂0 hδ₂ΛH hδ₂ε
      v hv hcv σ h1 h2 ξ hξ,
    fun σ h1 h2 => hEb' lam δ₁ δ₂ hlam0 hlamΛE hlam12 hδ₁0 hδ₁ΛE hδ₂0 hδ₂ΛE hδ₂ε
      v hv hcv σ h1 h2⟩

end Work.Drive.Generic

