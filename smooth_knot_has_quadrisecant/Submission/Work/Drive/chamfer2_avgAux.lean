import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.sweepBlurFacts

/-!
# `Work.Drive.chamfer2_avg_ne_zero` — the geometry-free half

Continuity of the lift data of `Work.Drive.SweepData` and the *averaging step*: a single direction
`n` whose pairing with the tail-chamfer direction
`U₂(σ) = sweepArc' r D σ lam - sweepChord' r D σ lam` is uniformly bounded below by `c > 0` on the
window `[sg - δ₂, sg + δ₂]` forces the window integral to be non-zero (pair with `n` and use
`∫ sweepBump = 1`).

This is the part of `Work.Drive.chamfer2_avg_ne_zero` that carries no geometry: the corner wedges
(or any other half-space input) feed it.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-! ## Continuity of the lift data and of the two sides of the chamfer -/

lemma continuous_clampI_avg : Continuous clampI := by
  unfold clampI
  fun_prop

lemma continuous_taR {d : BandArcData} (D : SweepData d) : Continuous (taR D) :=
  D.cont_ta.comp continuous_clampI_avg

lemma continuous_tbR {d : BandArcData} (D : SweepData d) : Continuous (tbR D) :=
  D.cont_tb.comp continuous_clampI_avg

lemma continuous_sweepW' {d : BandArcData} (D : SweepData d) : Continuous (sweepW' D) :=
  (continuous_tbR D).sub (continuous_taR D)

lemma continuous_sweepArc' {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (hr : Continuous r) (lam : ℝ) :
    Continuous (fun σ : ℝ => sweepArc' r D σ lam) := by
  have h1 : Continuous (fun σ : ℝ => taR D σ + lam * sweepW' D σ) :=
    (continuous_taR D).add ((continuous_sweepW' D).const_mul lam)
  exact hr.comp h1

lemma continuous_sweepChord' {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (hr : Continuous r) (lam : ℝ) :
    Continuous (fun σ : ℝ => sweepChord' r D σ lam) := by
  have h1 : Continuous (fun σ : ℝ => r (taR D σ)) := hr.comp (continuous_taR D)
  have h2 : Continuous (fun σ : ℝ => r (tbR D σ)) := hr.comp (continuous_tbR D)
  exact (h1.const_smul (1 - lam)).add (h2.const_smul lam)

/-! ## The averaging step -/

/-- **The averaging step.**  A *single* direction `n` whose pairing with the tail-chamfer direction
`sweepArc' - sweepChord'` is uniformly bounded below by `c > 0` on the whole window
`[sg - δ₂, sg + δ₂]` forces the window integral to be non-zero: pairing it with `n` and using
`∫ sweepBump = 1` gives `⟪n, F⟫ ≥ c > 0`.

This is the content-free half of `Work.Drive.chamfer2_avg_ne_zero`: it is what the corner wedges
(or any other half-space input) feed. -/
theorem window_integral_ne_zero_of_uniform_pos {r : ℝ → Space} {d : BandArcData}
    (D : SweepData d) {sg δ₂ lam c : ℝ} (hδ₂ : 0 < δ₂) {n : Space} (hc : 0 < c)
    (hcont : Continuous (fun v : ℝ => sweepBump v •
        (sweepArc' r D (sg - δ₂ * v) lam - sweepChord' r D (sg - δ₂ * v) lam)))
    (h : ∀ σ : ℝ, sg - δ₂ ≤ σ → σ ≤ sg + δ₂ →
      c ≤ inner ℝ n (sweepArc' r D σ lam - sweepChord' r D σ lam)) :
    (∫ v in (-1 : ℝ)..1, sweepBump v •
        (sweepArc' r D (sg - δ₂ * v) lam - sweepChord' r D (sg - δ₂ * v) lam)) ≠ 0 := by
  intro hzero
  set F : Space := ∫ v in (-1 : ℝ)..1, sweepBump v •
    (sweepArc' r D (sg - δ₂ * v) lam - sweepChord' r D (sg - δ₂ * v) lam) with hF
  have hint : IntervalIntegrable (fun v : ℝ => sweepBump v •
      (sweepArc' r D (sg - δ₂ * v) lam - sweepChord' r D (sg - δ₂ * v) lam))
      MeasureTheory.volume (-1) 1 := hcont.intervalIntegrable _ _
  -- pairing the integral with `n`
  have hpair : inner ℝ n F = ∫ v in (-1 : ℝ)..1,
      sweepBump v * inner ℝ n (sweepArc' r D (sg - δ₂ * v) lam
        - sweepChord' r D (sg - δ₂ * v) lam) := by
    have h1 : innerSL ℝ n F = ∫ v in (-1 : ℝ)..1,
        sweepBump v * innerSL ℝ n (sweepArc' r D (sg - δ₂ * v) lam
          - sweepChord' r D (sg - δ₂ * v) lam) := by
      rw [hF, ← ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ n) hint]
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      simp
    simpa only [innerSL_apply_apply] using h1
  -- the pointwise bound on the integrand
  have hbound : ∀ v : ℝ, -1 ≤ v → v ≤ 1 →
      sweepBump v * c ≤ sweepBump v * inner ℝ n (sweepArc' r D (sg - δ₂ * v) lam
        - sweepChord' r D (sg - δ₂ * v) lam) := by
    intro v hv1 hv2
    have hσ1 : sg - δ₂ ≤ sg - δ₂ * v := by nlinarith [hδ₂, hv1]
    have hσ2 : sg - δ₂ * v ≤ sg + δ₂ := by nlinarith [hδ₂, hv2]
    exact mul_le_mul_of_nonneg_left (h (sg - δ₂ * v) hσ1 hσ2) (sweepBump_nonneg v)
  have hInt1 : IntervalIntegrable (fun v : ℝ => sweepBump v * c)
      MeasureTheory.volume (-1) 1 :=
    (sweepBump_continuous.mul_const c).intervalIntegrable _ _
  have hInt2 : IntervalIntegrable (fun v : ℝ => sweepBump v * inner ℝ n
      (sweepArc' r D (sg - δ₂ * v) lam - sweepChord' r D (sg - δ₂ * v) lam))
      MeasureTheory.volume (-1) 1 := by
    have hc1 : Continuous (fun v : ℝ => sweepBump v * inner ℝ n
        (sweepArc' r D (sg - δ₂ * v) lam - sweepChord' r D (sg - δ₂ * v) lam)) := by
      have h2 : Continuous (fun v : ℝ => inner ℝ n (sweepBump v •
          (sweepArc' r D (sg - δ₂ * v) lam - sweepChord' r D (sg - δ₂ * v) lam))) :=
        continuous_const.inner hcont
      refine h2.congr (fun v => ?_)
      simp [real_inner_smul_right]
    exact hc1.intervalIntegrable _ _
  have hmono : (∫ v in (-1 : ℝ)..1, sweepBump v * c)
      ≤ ∫ v in (-1 : ℝ)..1, sweepBump v * inner ℝ n (sweepArc' r D (sg - δ₂ * v) lam
          - sweepChord' r D (sg - δ₂ * v) lam) :=
    intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hInt1 hInt2
      (fun v hv => hbound v (le_of_lt hv.1) (le_of_lt hv.2))
  have hconst : (∫ v in (-1 : ℝ)..1, sweepBump v * c) = c := by
    rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]
  -- conclude: `⟪n, F⟫ ≥ c > 0` while `⟪n, F⟫ = 0`
  have hkey : 0 < ∫ v in (-1 : ℝ)..1, sweepBump v * inner ℝ n (sweepArc' r D (sg - δ₂ * v) lam
      - sweepChord' r D (sg - δ₂ * v) lam) :=
    lt_of_lt_of_le hc (by rw [← hconst]; exact hmono)
  rw [← hpair] at hkey
  rw [hzero, inner_zero_right] at hkey
  exact lt_irrefl 0 hkey
end Work.Drive
