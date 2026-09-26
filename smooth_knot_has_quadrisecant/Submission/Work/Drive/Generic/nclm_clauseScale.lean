import Mathlib
import Submission.Work.Drive.Generic.nclmPkg
import Submission.Work.Drive.Generic.nclmWindow
import Submission.Work.Drive.Generic.nclmChart
import Submission.Work.Drive.AB.chordEndNormLower
import Submission.Work.Drive.AB.windowDataSmall
import Submission.Work.Drive.H2.baseHeight_lower
import Submission.Work.Drive.H2.chartUp_norm_bound

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

noncomputable section

/-! ## Helper lemmas for the scale package

The two estimates below are the only analytic content of `nclmPkgScale`.

* `nclm_clauseScale_int_ge`: the bump-weighted average of the retained width over the window is at
  least the width at the centre `ε` (half of it, using the window comparability).
* `nclm_clauseScale_chord_upper`: the needle's chord is at most `2 M w(ε)` long, `M` a Lipschitz
  constant of the knot. -/

/-- The bump-weighted average of the retained width over the window `[ε - δ₂, ε + δ₂]` dominates
`w(ε)/2`, provided the width in the window is at least `w(ε)/2`. -/
lemma nclm_clauseScale_int_ge {d : BandArcData} (D : Work.Drive.SweepData d) (δ₂ ε : ℝ)
    (hδ₂0 : 0 ≤ δ₂)
    (hpt : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      Work.Drive.sweepW' D ε / 2 ≤ Work.Drive.sweepW' D σ) :
    Work.Drive.sweepW' D ε / 2
      ≤ ∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v * Work.Drive.sweepW' D (ε - δ₂ * v) := by
  have hWc : Continuous fun v : ℝ => Work.Drive.sweepW' D (ε - δ₂ * v) :=
    (Work.Drive.continuous_sweepW' D).comp
      (continuous_const.sub (continuous_const.mul continuous_id))
  have hle : ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      Work.Drive.sweepBump v * (Work.Drive.sweepW' D ε / 2)
        ≤ Work.Drive.sweepBump v * Work.Drive.sweepW' D (ε - δ₂ * v) := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    have hσlo : ε - δ₂ ≤ ε - δ₂ * v := by
      have := mul_le_mul_of_nonneg_left hv2 hδ₂0; linarith
    have hσhi : ε - δ₂ * v ≤ ε + δ₂ := by
      have := mul_le_mul_of_nonneg_left hv1 hδ₂0; linarith
    exact mul_le_mul_of_nonneg_left (hpt _ hσlo hσhi) (Work.Drive.sweepBump_nonneg v)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (a := (-1 : ℝ)) (b := 1)
    (f := fun v : ℝ => Work.Drive.sweepBump v * (Work.Drive.sweepW' D ε / 2))
    (g := fun v : ℝ => Work.Drive.sweepBump v * Work.Drive.sweepW' D (ε - δ₂ * v))
    (by norm_num)
    ((Work.Drive.sweepBump_continuous.mul continuous_const).intervalIntegrable _ _)
    ((Work.Drive.sweepBump_continuous.mul hWc).intervalIntegrable _ _) hle
  have heq : (∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v * (Work.Drive.sweepW' D ε / 2))
      = Work.Drive.sweepW' D ε / 2 := by
    rw [intervalIntegral.integral_mul_const, Work.Drive.integral_sweepBump, one_mul]
  linarith [hmono, heq]

/-- The needle's chord `chordEndB - chordEndA` is bounded by `2 M w(ε)`, where `M` is a Lipschitz
constant of `r` and the retained width in the window is at most `2 w(ε)`. -/
lemma nclm_clauseScale_chord_upper {r : ℝ → Space} {d : BandArcData}
    (D : Work.Drive.SweepData d) (hcont : Continuous r) (δ₂ ε M : ℝ) (hM : 0 ≤ M)
    (hlip : ∀ x y : ℝ, ‖r x - r y‖ ≤ M * |x - y|)
    (hlo : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      Work.Drive.sweepW' D ε / 2 ≤ Work.Drive.sweepW' D σ)
    (hhi : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      Work.Drive.sweepW' D σ ≤ 2 * Work.Drive.sweepW' D ε)
    (hδ₂0 : 0 ≤ δ₂) (hWpos : 0 ≤ Work.Drive.sweepW' D ε) :
    ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖
      ≤ 2 * M * Work.Drive.sweepW' D ε := by
  rw [Work.Drive.chordEndB_sub_chordEndA r D hcont δ₂ ε]
  set G : ℝ → Space :=
    fun v => r (Work.Drive.tbR D (ε - δ₂ * v)) - r (Work.Drive.taR D (ε - δ₂ * v)) with hG
  have hGc : Continuous G :=
    (hcont.comp ((Work.Drive.continuous_tbR D).comp (by fun_prop))).sub
      (hcont.comp ((Work.Drive.continuous_taR D).comp (by fun_prop)))
  have hInt1 : IntervalIntegrable (fun v : ℝ => ‖Work.Drive.sweepBump v • G v‖) volume
      (-1) 1 :=
    ((Work.Drive.sweepBump_continuous.smul hGc).norm).intervalIntegrable _ _
  have hInt2 : IntervalIntegrable
      (fun v : ℝ => Work.Drive.sweepBump v * (2 * M * Work.Drive.sweepW' D ε)) volume
      (-1) 1 :=
    (Work.Drive.sweepBump_continuous.mul continuous_const).intervalIntegrable _ _
  have hle : ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      ‖Work.Drive.sweepBump v • G v‖
        ≤ Work.Drive.sweepBump v * (2 * M * Work.Drive.sweepW' D ε) := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    have hσlo : ε - δ₂ ≤ ε - δ₂ * v := by
      have := mul_le_mul_of_nonneg_left hv2 hδ₂0; linarith
    have hσhi : ε - δ₂ * v ≤ ε + δ₂ := by
      have := mul_le_mul_of_nonneg_left hv1 hδ₂0; linarith
    have hWσpos : 0 ≤ Work.Drive.sweepW' D (ε - δ₂ * v) :=
      le_trans (by positivity : (0 : ℝ) ≤ Work.Drive.sweepW' D ε / 2) (hlo _ hσlo hσhi)
    have habs : |Work.Drive.tbR D (ε - δ₂ * v) - Work.Drive.taR D (ε - δ₂ * v)|
        = Work.Drive.sweepW' D (ε - δ₂ * v) := by
      rw [Work.Drive.sweepW']; exact abs_of_nonneg hWσpos
    have h1 : ‖G v‖ ≤ M * Work.Drive.sweepW' D (ε - δ₂ * v) := by
      have h := hlip (Work.Drive.tbR D (ε - δ₂ * v)) (Work.Drive.taR D (ε - δ₂ * v))
      rwa [habs] at h
    rw [norm_smul, Real.norm_of_nonneg (Work.Drive.sweepBump_nonneg v)]
    have h2 : Work.Drive.sweepW' D (ε - δ₂ * v) ≤ 2 * Work.Drive.sweepW' D ε :=
      hhi _ hσlo hσhi
    calc Work.Drive.sweepBump v * ‖G v‖
        ≤ Work.Drive.sweepBump v * (M * Work.Drive.sweepW' D (ε - δ₂ * v)) :=
          mul_le_mul_of_nonneg_left h1 (Work.Drive.sweepBump_nonneg v)
      _ ≤ Work.Drive.sweepBump v * (2 * M * Work.Drive.sweepW' D ε) := by
          refine mul_le_mul_of_nonneg_left ?_ (Work.Drive.sweepBump_nonneg v)
          nlinarith [hM, h2]
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (a := (-1 : ℝ)) (b := 1)
    (f := fun v : ℝ => ‖Work.Drive.sweepBump v • G v‖)
    (g := fun v : ℝ => Work.Drive.sweepBump v * (2 * M * Work.Drive.sweepW' D ε))
    (by norm_num) hInt1 hInt2 hle
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (a := (-1 : ℝ)) (b := 1) (f := fun v : ℝ => Work.Drive.sweepBump v • G v) (by norm_num)
  have heq : (∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v * (2 * M * Work.Drive.sweepW' D ε))
      = 2 * M * Work.Drive.sweepW' D ε := by
    rw [intervalIntegral.integral_mul_const, Work.Drive.integral_sweepBump, one_mul]
  linarith [hnorm, hmono, heq]

theorem nclm_clauseScale {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    Work.Drive.Generic.nclmPkgScale r D := by
  unfold Work.Drive.Generic.nclmPkgScale
  obtain ⟨M, hM0, hlip⟩ := Work.Drive.exists_knot_lipschitz hr
  obtain ⟨K, hK1, hKb⟩ := Work.Drive.H2.H2_accel_bound hr
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  obtain ⟨εc, cl, hεc0, hcl0, hclbound⟩ := Work.Drive.chordEndNormLower hr D
  obtain ⟨cb, hcb0, εb, hεb0, _hεb1, hbound⟩ := Work.Drive.H2.baseHeight_lower hr hinfl D
  refine ⟨min (min εc εb) (1 / 2), lt_min (lt_min hεc0 hεb0) (by norm_num), ?_⟩
  intro ε hε0 hεle
  have hεc : ε ≤ εc := le_trans hεle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεb : ε ≤ εb := le_trans hεle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεhalf : ε ≤ 1 / 2 := le_trans hεle (min_le_right _ _)
  have hε1 : ε < 1 := by linarith
  have hWpos : 0 < Work.Drive.sweepW' D ε := Work.Drive.wds_sweepW'_pos D hε0 hε1
  obtain ⟨Λw, hΛw0, hΛw⟩ := Work.Drive.Generic.nclm_window_eps (D := D) hε0 hε1
  obtain ⟨Λb, hΛb0, _hΛb12, hbase⟩ := hbound ε hε0 hεb
  have hper : (0 : ℝ) < LeanEval.KnotTheory.Quadrisecant.period :=
    LeanEval.KnotTheory.Quadrisecant.period_pos
  refine ⟨cl / 2, 2 * M, cb / 2, K / 2,
    min (min Λb Λw) (LeanEval.KnotTheory.Quadrisecant.period / 4),
    by positivity, by positivity, by positivity, by positivity, ?_, ?_⟩
  · exact lt_min (lt_min hΛb0 hΛw0) (by linarith)
  · intro lam δ₁ δ₂ hlam0 hlamΛ hlam12 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε
    have hΛb_le : min (min Λb Λw) (LeanEval.KnotTheory.Quadrisecant.period / 4) ≤ Λb :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hΛw_le : min (min Λb Λw) (LeanEval.KnotTheory.Quadrisecant.period / 4) ≤ Λw :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hΛp_le : min (min Λb Λw) (LeanEval.KnotTheory.Quadrisecant.period / 4)
        ≤ LeanEval.KnotTheory.Quadrisecant.period / 4 := min_le_right _ _
    have hlamΛb : lam ≤ Λb := le_trans hlamΛ hΛb_le
    have hδ₁Λb : δ₁ ≤ Λb := le_trans hδ₁Λ hΛb_le
    have hδ₂Λb : δ₂ ≤ Λb := le_trans hδ₂Λ hΛb_le
    have hδ₂Λw : δ₂ ≤ Λw := le_trans hδ₂Λ hΛw_le
    have hδ₁4 : δ₁ ≤ LeanEval.KnotTheory.Quadrisecant.period / 4 := le_trans hδ₁Λ hΛp_le
    have hwin : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
        Work.Drive.sweepW' D ε / 2 ≤ Work.Drive.sweepW' D σ ∧
        Work.Drive.sweepW' D σ ≤ 2 * Work.Drive.sweepW' D ε :=
      fun σ h1 h2 =>
        ⟨(hΛw δ₂ σ hδ₂0 hδ₂Λw hδ₂ε h1 h2).1, (hΛw δ₂ σ hδ₂0 hδ₂Λw hδ₂ε h1 h2).2.1⟩
    have hlo : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
        Work.Drive.sweepW' D ε / 2 ≤ Work.Drive.sweepW' D σ := fun σ h1 h2 => (hwin σ h1 h2).1
    have hhi : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
        Work.Drive.sweepW' D σ ≤ 2 * Work.Drive.sweepW' D ε :=
      fun σ h1 h2 => (hwin σ h1 h2).2
    have hInt := nclm_clauseScale_int_ge D δ₂ ε hδ₂0.le hlo
    have hcl := hclbound δ₂ ε hδ₂0 hδ₂ε hε0 hεc
    have hlow : cl / 2 * Work.Drive.sweepW' D ε
        ≤ ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ := by
      have h1 : cl * (Work.Drive.sweepW' D ε / 2)
          ≤ cl * ∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v * Work.Drive.sweepW' D (ε - δ₂ * v) :=
        mul_le_mul_of_nonneg_left hInt hcl0.le
      have h2 : cl / 2 * Work.Drive.sweepW' D ε
          = cl * (Work.Drive.sweepW' D ε / 2) := by ring
      rw [h2]; linarith
    have hup := nclm_clauseScale_chord_upper D hr.smooth.continuous δ₂ ε M hM0.le hlip
      hlo hhi hδ₂0.le hWpos.le
    intro v hv hcv
    have hbase' := hbase lam δ₁ δ₂ hlam0 hlamΛb hδ₁0 hδ₁Λb hδ₂0 hδ₂Λb hδ₂ε v hv hcv
    have hhi' := Work.Drive.H2.chartUp_norm_bound (r := r) (d := d) (D := D) hr (K := K)
      (W := Work.Drive.sweepW' D ε) (lam := lam) (δ₁ := δ₁) (δ₂ := δ₂) (ε := ε) (v := v)
      hK0.le hWpos.le hlam0.le hlam12 hδ₁0 hδ₁4 hδ₂0 hδ₂ε hε0 hεhalf hv hKb hhi hcv
    have hchartUp_pos : 0 < ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
      have h1 : 0 < cb * (Work.Drive.sweepW' D ε) ^ 2 := mul_pos hcb0 (pow_pos hWpos 2)
      linarith
    have hCpos : 0 < ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ :=
      lt_of_lt_of_le (mul_pos (by positivity : (0 : ℝ) < cl / 2) hWpos) hlow
    have hE : ‖Work.Drive.chartE r D lam δ₁ δ₂ ε v‖ = 1 := by
      have hne : ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ ≠ 0 := ne_of_gt hchartUp_pos
      rw [Work.Drive.chartE, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hne]
    have hEv : inner ℝ (Work.Drive.chartE r D lam δ₁ δ₂ ε v) v = 0 := by
      rw [Work.Drive.chartE, real_inner_smul_left, Work.Drive.inner_chartUp_v r D lam δ₁ δ₂ ε hv,
        mul_zero]
    have hlowCh : cb / 2 * (Work.Drive.sweepW' D ε) ^ 2
        ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by linarith
    have hhiCh : ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2
        ≤ K / 2 * (Work.Drive.sweepW' D ε) ^ 2 := by nlinarith [hhi']
    exact ⟨hwin, hCpos, hlow, hup, hE, hEv, hlowCh, hhiCh⟩

end

end Work.Drive.Generic
