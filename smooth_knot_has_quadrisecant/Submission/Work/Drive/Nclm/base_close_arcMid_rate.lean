import Mathlib
import Submission.Work.Drive.AB.shiftedNeedleChart
import Submission.Work.Drive.AB.shiftedNeedleBlur
import Submission.Work.Drive.AB.needleArcZoneMono
import Submission.Work.Drive.AB.windowDataSmall
import Submission.Work.Drive.Generic.nclmDefs
import Submission.Work.Drive.Nclm.base_close_arcMid

/-!
# The rate form of `base_close_arcMid`

`Work.Drive.Nclm.base_close_arcMid` shows that the base point of the shifted needle is
*arbitrarily close* to the midpoint `sweepArc' r D sg (1/2)` of the retained arc over the window.
Here the same comparison is made with an *explicit rate*: the distance is at most
`cN * (sweepW' D ε)^2`, i.e. of the order of the square of the width of the retained arc at the
window centre, with a constant `cN` that the caller prescribes (and a threshold `Λ` chosen after
`ε`).

The point of the rate form is that the width appears *squared*: the two leading errors of the naive
comparison,

* the drift of the left lift `taR` across the window `[ε - δ₂, ε + δ₂]`, and
* the drift of the width `sweepW'` across the window,

are first-order in the window width `2 δ₂ ≤ 2 Λ`, and `Λ` may be taken as small as
`cN * sweepW' D ε * period / (64 M)` — first order in the *width*, hence the product is second
order.  The `δ₁`-drift of the branch fraction `ξ` contributes `O(δ₁) * W`, likewise second order.

The proof is the same skeleton as `base_close_arcMid` (double bump average, then a pointwise
comparison of every loop point of the doubled window with `sweepArc' r D sg (1/2)`), but the
pointwise comparison no longer goes through the collapsed end `taR D 0`: it compares directly with
the midpoint at `sg`, using the *uniform* window modulus of `taR` and of `sweepW'` on the compact
`[ε - 1, ε + 1]` (`window_modulus_real`).
-/

set_option maxHeartbeats 4000000

noncomputable section

namespace Work.Drive.Nclm

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-- **Real-valued uniform window modulus.**  For a continuous `F : ℝ → ℝ` and every `t > 0` there
is `Λ > 0` with `Λ ≤ ε / 2` such that `F` is `t`-constant on the whole window
`[ε - δ₂, ε + δ₂]` (as soon as `δ₂ ≤ Λ`).  This is the one-dimensional companion of
`Work.Drive.H2.exists_window_modulus`; the modulus is the one supplied by the uniform continuity of
`F` on the compact `[ε - 1, ε + 1]`, which contains every evaluation point as soon as `Λ ≤ ε / 2`
and `ε ≤ 2`. -/
lemma window_modulus_real {F : ℝ → ℝ} (hF : Continuous F) {ε t : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 2) (ht : 0 < t) :
    ∃ Λ : ℝ, 0 < Λ ∧ Λ ≤ ε / 2 ∧
      ∀ δ₂ : ℝ, 0 < δ₂ → δ₂ ≤ Λ → ∀ y : ℝ, ε - δ₂ ≤ y → y ≤ ε + δ₂ →
        ∀ v ∈ Set.Icc (-1 : ℝ) 1, |F (ε - δ₂ * v) - F y| ≤ t := by
  have huc := (isCompact_Icc (a := ε - 1) (b := ε + 1)).uniformContinuousOn_of_continuous
    hF.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη0, hηb⟩ := huc t ht
  refine ⟨min (ε / 2) (η / 4), lt_min (by linarith) (by linarith),
    min_le_left _ _, ?_⟩
  intro δ₂ hδ₂ hδ₂L y hylo hyhi v hv
  have hδ₂ε : δ₂ ≤ ε / 2 := hδ₂L.trans (min_le_left _ _)
  have hδ₂η : δ₂ ≤ η / 4 := hδ₂L.trans (min_le_right _ _)
  have hvabs : |v| ≤ 1 := abs_le.mpr ⟨hv.1, hv.2⟩
  have hδv : |δ₂ * v| ≤ δ₂ := by
    rw [abs_mul, abs_of_pos hδ₂]
    calc δ₂ * |v| ≤ δ₂ * 1 := mul_le_mul_of_nonneg_left hvabs hδ₂.le
      _ = δ₂ := mul_one δ₂
  obtain ⟨hδv1, hδv2⟩ := abs_le.mp hδv
  have hymem : y ∈ Set.Icc (ε - 1) (ε + 1) := ⟨by linarith, by linarith⟩
  have hxm : ε - δ₂ * v ∈ Set.Icc (ε - 1) (ε + 1) := ⟨by linarith, by linarith⟩
  have hdist : dist y (ε - δ₂ * v) < η := by
    rw [Real.dist_eq]
    have h1 : |y - ε| ≤ δ₂ := by rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have h2 : y - (ε - δ₂ * v) = (y - ε) + δ₂ * v := by ring
    rw [h2]
    have := abs_add_le (y - ε) (δ₂ * v)
    linarith
  have hres := hηb y hymem (ε - δ₂ * v) hxm hdist
  rw [Real.dist_eq, abs_sub_comm] at hres
  exact hres.le

theorem base_close_arcMid_rate {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∀ cN : ℝ, 0 < cN → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ Λ : ℝ, 0 < Λ ∧ Λ ≤ 1 / 4 ∧
        ∀ lam δ₁ δ₂ : ℝ, 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
          0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          ‖Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0 - Work.Drive.sweepArc' r D σ (1 / 2)‖
            ≤ cN * (Work.Drive.sweepW' D ε) ^ 2 := by
  intro cN hcN
  have hp : (0 : ℝ) < period := period_pos
  obtain ⟨M, hM0, hLip⟩ := Work.Drive.exists_knot_lipschitz hr
  have hMne : M ≠ 0 := ne_of_gt hM0
  have hcNne : cN ≠ 0 := ne_of_gt hcN
  have hrcont : Continuous r := hr.smooth.continuous
  -- the smallness threshold for the width
  obtain ⟨η₁, hη₁0, hη₁⟩ := Work.Drive.exists_window_small D (by positivity : (0 : ℝ) < 8 * M / cN)
  refine ⟨min η₁ (1 / 2), lt_min hη₁0 (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro ε hε0 hεε₀
  have hεη : ε ≤ η₁ := hεε₀.trans (min_le_left _ _)
  have hε12 : ε ≤ 1 / 2 := hεε₀.trans (min_le_right _ _)
  have hε1 : ε < 1 := by linarith
  have hε2 : ε ≤ 2 := by linarith
  have hWεle : Work.Drive.sweepW' D ε ≤ 8 * M / cN := (hη₁ ε hε0.le hεη).2
  set W : ℝ := Work.Drive.sweepW' D ε with hWdef
  have hWpos : 0 < W := by
    rw [hWdef]
    exact Work.Drive.wds_sweepW'_pos D hε0 hε1
  have hWmul : cN * W ≤ 8 * M := by
    calc cN * W ≤ cN * (8 * M / cN) := mul_le_mul_of_nonneg_left hWεle hcN.le
      _ = 8 * M := by field_simp
  set t : ℝ := cN * W ^ 2 / (16 * M) with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have htW : t ≤ W / 2 := by
    rw [htdef, div_le_iff₀ (by positivity : (0 : ℝ) < 16 * M)]
    nlinarith [hWmul, hWpos]
  -- the two window moduli
  obtain ⟨Λa, hΛa0, -, hΛa⟩ :=
    window_modulus_real (F := Work.Drive.taR D) (Work.Drive.arcWin_taR_continuous D)
      hε0 hε2 htpos
  obtain ⟨Λb, hΛb0, -, hΛb⟩ :=
    window_modulus_real (F := Work.Drive.sweepW' D) (Work.Drive.arcWin_sweepW'_continuous D)
      hε0 hε2 htpos
  set Λ : ℝ := min (min (1 / 4) (period / 4))
    (min (min Λa Λb) (cN * W * period / (64 * M))) with hΛdef
  have hΛpos : 0 < Λ := by
    rw [hΛdef]
    exact lt_min (lt_min (by norm_num) (by positivity))
      (lt_min (lt_min hΛa0 hΛb0) (by positivity))
  have hΛ14 : Λ ≤ 1 / 4 := by
    rw [hΛdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hΛp4 : Λ ≤ period / 4 := by
    rw [hΛdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hΛa' : Λ ≤ Λa := by
    rw [hΛdef]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hΛb' : Λ ≤ Λb := by
    rw [hΛdef]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hΛrate : Λ ≤ cN * W * period / (64 * M) := by
    rw [hΛdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨Λ, hΛpos, hΛ14, ?_⟩
  intro lam δ₁ δ₂ hlam0 hlamΛ hlam12 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε sg hsglo hsghi
  have hδ₁p4 : δ₁ ≤ period / 4 := hδ₁Λ.trans hΛp4
  have hδ₂Λa : δ₂ ≤ Λa := hδ₂Λ.trans hΛa'
  have hδ₂Λb : δ₂ ≤ Λb := hδ₂Λ.trans hΛb'
  -- the pointwise comparison inside the doubled window
  have hpoint : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      ‖Work.Drive.sweepLoopChamfer r D lam (ε - δ₂ * v) (period / 4 - δ₁ * u)
        - Work.Drive.sweepArc' r D sg (1 / 2)‖
        ≤ M * ((3 / 2) * t + 4 * W * Λ / period) := by
    intro u hu v hv
    have hu1 : -1 ≤ u := hu.1
    have hu2 : u ≤ 1 := hu.2
    have hv1 : -1 ≤ v := hv.1
    have hv2 : v ≤ 1 := hv.2
    have huab : |u| ≤ 1 := abs_le.mpr ⟨hu1, hu2⟩
    have hvab : |v| ≤ 1 := abs_le.mpr ⟨hv1, hv2⟩
    set sv : ℝ := ε - δ₂ * v with hsvdef
    -- the loop parameter window stays in the first half of one cell
    have hδ₁u_le : δ₁ * u ≤ δ₁ := by nlinarith [hu2, hδ₁0]
    have hδ₁u_ge : -δ₁ ≤ δ₁ * u := by nlinarith [hu1, hδ₁0]
    have hτ0 : 0 ≤ period / 4 - δ₁ * u := by nlinarith [hδ₁p4, hδ₁u_le, hp]
    have hτ1 : period / 4 - δ₁ * u < period := by nlinarith [hδ₁p4, hδ₁u_ge, hp]
    have hsp : Work.Drive.sweepParam (period / 4 - δ₁ * u) ≤ 1 / 2 := by
      rw [Work.Drive.sweepParam_eq_div ⟨hτ0, hτ1⟩, div_le_iff₀ hp]
      nlinarith [hδ₁u_ge, hδ₁p4, hp]
    rw [Work.Drive.sweepLoopChamfer_arcZone' D hsp]
    set ξ : ℝ := lam + (1 - 2 * lam) * (2 * Work.Drive.sweepParam (period / 4 - δ₁ * u))
      with hξdef
    -- the branch fraction is close to `1/2`
    have hξb : |ξ - 1 / 2| ≤ 2 * δ₁ / period := by
      rw [hξdef, Work.Drive.sweepParam_eq_div ⟨hτ0, hτ1⟩]
      have hid : lam + (1 - 2 * lam) * (2 * ((period / 4 - δ₁ * u) / period)) - 1 / 2
          = -(1 - 2 * lam) * (2 * (δ₁ * u) / period) := by
        field_simp
        ring
      rw [hid, abs_mul, abs_neg]
      have h1 : |1 - 2 * lam| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have h2 : |2 * (δ₁ * u) / period| ≤ 2 * δ₁ / period := by
        rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hp]
        have h3 : |δ₁ * u| ≤ δ₁ := by
          rw [abs_mul, abs_of_pos hδ₁0]
          calc δ₁ * |u| ≤ δ₁ * 1 := mul_le_mul_of_nonneg_left huab hδ₁0.le
            _ = δ₁ := mul_one δ₁
        exact div_le_div_of_nonneg_right (by linarith : 2 * |δ₁ * u| ≤ 2 * δ₁) hp.le
      calc |1 - 2 * lam| * |2 * (δ₁ * u) / period| ≤ 1 * (2 * δ₁ / period) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 2 * δ₁ / period := by ring
    -- the window differences of the two lifts
    have hta_mid : |Work.Drive.taR D sv - Work.Drive.taR D sg| ≤ t :=
      hΛa δ₂ hδ₂0 hδ₂Λa sg hsglo hsghi v hv
    have hWsg : |Work.Drive.sweepW' D sv - Work.Drive.sweepW' D sg| ≤ t :=
      hΛb δ₂ hδ₂0 hδ₂Λb sg hsglo hsghi v hv
    have hWeps : |Work.Drive.sweepW' D sv - W| ≤ t := by
      have h := hΛb δ₂ hδ₂0 hδ₂Λb ε (by linarith) (by linarith) v hv
      rwa [← hWdef] at h
    have hδ₂v : |δ₂ * v| ≤ δ₂ := by
      rw [abs_mul, abs_of_pos hδ₂0]
      calc δ₂ * |v| ≤ δ₂ * 1 := mul_le_mul_of_nonneg_left hvab hδ₂0.le
        _ = δ₂ := mul_one δ₂
    obtain ⟨hδ₂v1, hδ₂v2⟩ := abs_le.mp hδ₂v
    have hWv_nonneg : 0 ≤ Work.Drive.sweepW' D sv := by
      have h1 : 0 < sv := by rw [hsvdef]; nlinarith [hδ₂v2, hδ₂ε, hε0]
      have h2 : sv < 1 := by rw [hsvdef]; nlinarith [hδ₂v1, hδ₂ε, hε12]
      exact (Work.Drive.wds_sweepW'_pos D h1 h2).le
    have hWv_bd : Work.Drive.sweepW' D sv ≤ 2 * W := by
      have h := (abs_le.mp hWeps).2
      linarith [h, htW]
    have hξW : |ξ - 1 / 2| * Work.Drive.sweepW' D sv ≤ 4 * W * Λ / period := by
      have h1 : |ξ - 1 / 2| ≤ 2 * Λ / period := by
        have h2 : 2 * δ₁ / period ≤ 2 * Λ / period :=
          div_le_div_of_nonneg_right (by linarith [hδ₁Λ]) hp.le
        linarith [hξb, h2]
      have h3 : 0 ≤ 2 * Λ / period := by positivity
      calc |ξ - 1 / 2| * Work.Drive.sweepW' D sv
          ≤ (2 * Λ / period) * (2 * W) := mul_le_mul h1 hWv_bd hWv_nonneg h3
        _ = 4 * W * Λ / period := by ring
    -- the parameter difference
    have hdiff : |(Work.Drive.taR D sv + ξ * Work.Drive.sweepW' D sv)
        - (Work.Drive.taR D sg + (1 / 2) * Work.Drive.sweepW' D sg)|
        ≤ (3 / 2) * t + 4 * W * Λ / period := by
      have hsplit : (Work.Drive.taR D sv + ξ * Work.Drive.sweepW' D sv)
          - (Work.Drive.taR D sg + (1 / 2) * Work.Drive.sweepW' D sg)
          = (Work.Drive.taR D sv - Work.Drive.taR D sg)
            + (ξ - 1 / 2) * Work.Drive.sweepW' D sv
            + (1 / 2) * (Work.Drive.sweepW' D sv - Work.Drive.sweepW' D sg) := by ring
      rw [hsplit]
      have hAB : |(Work.Drive.taR D sv - Work.Drive.taR D sg)
            + (ξ - 1 / 2) * Work.Drive.sweepW' D sv
            + (1 / 2) * (Work.Drive.sweepW' D sv - Work.Drive.sweepW' D sg)|
          ≤ |Work.Drive.taR D sv - Work.Drive.taR D sg|
            + |(ξ - 1 / 2) * Work.Drive.sweepW' D sv|
            + |(1 / 2) * (Work.Drive.sweepW' D sv - Work.Drive.sweepW' D sg)| := by
        have h1 := abs_add_le ((Work.Drive.taR D sv - Work.Drive.taR D sg)
          + (ξ - 1 / 2) * Work.Drive.sweepW' D sv)
          ((1 / 2) * (Work.Drive.sweepW' D sv - Work.Drive.sweepW' D sg))
        have h2 := abs_add_le (Work.Drive.taR D sv - Work.Drive.taR D sg)
          ((ξ - 1 / 2) * Work.Drive.sweepW' D sv)
        linarith
      have h3 : |(ξ - 1 / 2) * Work.Drive.sweepW' D sv|
          = |ξ - 1 / 2| * Work.Drive.sweepW' D sv := by
        rw [abs_mul, abs_of_nonneg hWv_nonneg]
      have h4 : |(1 / 2) * (Work.Drive.sweepW' D sv - Work.Drive.sweepW' D sg)|
          ≤ (1 / 2) * t := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        linarith [hWsg]
      calc |(Work.Drive.taR D sv - Work.Drive.taR D sg)
            + (ξ - 1 / 2) * Work.Drive.sweepW' D sv
            + (1 / 2) * (Work.Drive.sweepW' D sv - Work.Drive.sweepW' D sg)|
          ≤ |Work.Drive.taR D sv - Work.Drive.taR D sg|
            + |(ξ - 1 / 2) * Work.Drive.sweepW' D sv|
            + |(1 / 2) * (Work.Drive.sweepW' D sv - Work.Drive.sweepW' D sg)| := hAB
        _ = |Work.Drive.taR D sv - Work.Drive.taR D sg|
            + |ξ - 1 / 2| * Work.Drive.sweepW' D sv
            + |(1 / 2) * (Work.Drive.sweepW' D sv - Work.Drive.sweepW' D sg)| := by rw [h3]
        _ ≤ t + 4 * W * Λ / period + (1 / 2) * t := add_le_add (add_le_add hta_mid hξW) h4
        _ = (3 / 2) * t + 4 * W * Λ / period := by ring
    show ‖r (Work.Drive.taR D sv + ξ * Work.Drive.sweepW' D sv)
        - r (Work.Drive.taR D sg + (1 / 2) * Work.Drive.sweepW' D sg)‖
        ≤ M * ((3 / 2) * t + 4 * W * Λ / period)
    exact (hLip _ _).trans (mul_le_mul_of_nonneg_left hdiff hM0.le)
  -- the two bump averages
  have hinner : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ‖Work.Drive.loopBlur r D lam δ₂ ε (period / 4 - δ₁ * u)
        - Work.Drive.sweepArc' r D sg (1 / 2)‖
        ≤ M * ((3 / 2) * t + 4 * W * Λ / period) := by
    intro u hu
    have h := bumpAvg_norm_sub_le
      (F := fun v : ℝ => Work.Drive.sweepLoopChamfer r D lam (ε - δ₂ * v) (period / 4 - δ₁ * u))
      (c := Work.Drive.sweepArc' r D sg (1 / 2))
      (η := M * ((3 / 2) * t + 4 * W * Λ / period))
      (intervalIntegrable_bump_chamfer hrcont D lam δ₂ ε (period / 4 - δ₁ * u))
      (fun v hv => hpoint u hu v hv)
    simpa only [Work.Drive.loopBlur] using h
  have hneedle : Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0
      = ∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u • Work.Drive.loopBlur r D lam δ₂ ε
          (period / 4 - δ₁ * u) := by
    rw [show Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0
        = Work.Drive.needleFam r D lam δ₁ δ₂ ε (period / 4) from by
      simp only [Work.Drive.shiftedNeedle, zero_add]]
    exact Work.Drive.needleFam_eq_blur_loop hrcont D lam δ₁ δ₂ ε (period / 4)
  rw [hneedle]
  refine (bumpAvg_norm_sub_le
    (F := fun u : ℝ => Work.Drive.loopBlur r D lam δ₂ ε (period / 4 - δ₁ * u))
    (c := Work.Drive.sweepArc' r D sg (1 / 2))
    (η := M * ((3 / 2) * t + 4 * W * Λ / period))
    (intervalIntegrable_bump_loopBlur hrcont D lam δ₂ ε δ₁ (period / 4)) hinner).trans ?_
  -- the final bookkeeping
  have hMt : M * t = cN * W ^ 2 / 16 := by
    rw [htdef]; field_simp
  have hMΛ : M * Λ ≤ cN * W * period / 64 := by
    calc M * Λ ≤ M * (cN * W * period / (64 * M)) :=
          mul_le_mul_of_nonneg_left hΛrate hM0.le
      _ = cN * W * period / 64 := by field_simp
  have hfour : 4 * W * (M * Λ) / period ≤ 4 * W * (cN * W * period / 64) / period := by
    apply div_le_div_of_nonneg_right _ hp.le
    exact mul_le_mul_of_nonneg_left hMΛ (by positivity : (0 : ℝ) ≤ 4 * W)
  calc M * ((3 / 2) * t + 4 * W * Λ / period)
      = 3 * (M * t) / 2 + 4 * W * (M * Λ) / period := by ring
    _ ≤ 3 * (cN * W ^ 2 / 16) / 2 + 4 * W * (cN * W * period / 64) / period := by
        rw [hMt]
        exact add_le_add le_rfl hfour
    _ = 5 * cN * W ^ 2 / 32 := by field_simp; ring
    _ ≤ cN * W ^ 2 := by nlinarith [sq_nonneg W, hcN]

end Work.Drive.Nclm
