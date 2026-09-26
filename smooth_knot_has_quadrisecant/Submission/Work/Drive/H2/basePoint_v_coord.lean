import Mathlib
import Submission.Work.Drive.AB.pinSetup
import Submission.Work.Drive.AB.needleFam_inner_eq_devAvg
import Submission.Work.Drive.Generic.nclmDev
import Submission.Work.Drive.Generic.nclmWindow
import Submission.Work.Drive.Generic.nclmBasic

/-!
# The chord coordinate of the needle's base point

Let `N = shiftedNeedle r D lam δ₁ δ₂ ε` be the double `sweepBump`-blur of the chamfered sweep loop
(blurred in the loop parameter at scale `δ₁` and in the sweep parameter at scale `δ₂`), and let
`v` be the *unit* direction of its chord `C⃗ = chordEndB - chordEndA`.  This module proves that the
chord coordinate of the needle's base point `N 0` (the middle of the retained arc) is the *midpoint*
of the chord up to `O(W² K)`, where `W` bounds half of the retained width `sweepW'` on the blur
window and `K` bounds the acceleration:

    |⟪N 0 - chordEndA, v⟫ - ‖C⃗‖ / 2| ≤ W² K / 2 .

The proof is the deviation formula `Work.Drive.needleFam_inner_eq_devAvg` at the loop parameter
`period / 4`, where the `sweepBump`-average of the arc fraction is exactly `1/2`
(`Work.Drive.Generic.integral_sweepBump_arcFrac`), combined with the pointwise second-order bound
`Work.Drive.Generic.nclm_dev_scalar_le` on the deviation `loopDev` and the two elementary integral
bounds (a `sweepBump`-average of a pointwise bound is a bound).
-/

namespace Work.Drive.H2

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-- The pointwise bound on the loop deviation, in the exact form used by the target.  Kept as a
separate helper to keep the main proof a sequence of short steps. -/
theorem loopDev_inner_abs_le {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {K W lam δ₁ δ₂ ε : ℝ} {v : Space}
    (hK : 0 ≤ K) (_hW : 0 ≤ W) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1 / 2)
    (hδ₁0 : 0 < δ₁) (hδ₁4 : δ₁ ≤ period / 4)
    (hδ₂0 : 0 < δ₂) (hδ₂ε : δ₂ ≤ ε / 2) (hε0 : 0 < ε) (hε12 : ε ≤ 1 / 2)
    (hv : ‖v‖ = 1)
    (hacc : ∀ x : ℝ, ‖deriv (deriv r) x‖ ≤ K)
    (hWσ : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → Work.Drive.sweepW' D σ ≤ 2 * W) :
    ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
        (Work.Drive.arcFrac lam δ₁ (period / 4) u)) v| ≤ W ^ 2 * K / 2 := by
  intro v' hv' u hu
  have hσlo : ε - δ₂ ≤ ε - δ₂ * v' := by nlinarith [hδ₂0, hv'.2]
  have hσhi : ε - δ₂ * v' ≤ ε + δ₂ := by nlinarith [hδ₂0, hv'.1]
  have hw : 0 < Work.Drive.sweepW' D (ε - δ₂ * v') :=
    Work.Drive.Generic.nclm_window_wpos D hδ₂0 hδ₂ε hε0 hε12 hσlo hσhi
  have hs0 : 0 ≤ Work.Drive.sweepParam (period / 4 - δ₁ * u) :=
    (Work.Drive.sweepParam_mem _).1
  have hs1 : Work.Drive.sweepParam (period / 4 - δ₁ * u) ≤ 1 / 2 :=
    Work.Drive.sweepParam_quarter_sub_le hδ₁0.le hδ₁4 hu
  have hξ : Work.Drive.arcFrac lam δ₁ (period / 4) u ∈ Set.Icc (0 : ℝ) 1 := by
    have hcoe : 0 ≤ 1 - 2 * lam := by linarith
    have htwos : 0 ≤ 2 * Work.Drive.sweepParam (period / 4 - δ₁ * u) := by linarith
    have htwos1 : 2 * Work.Drive.sweepParam (period / 4 - δ₁ * u) ≤ 1 := by linarith
    have hrw : Work.Drive.arcFrac lam δ₁ (period / 4) u
        = lam + (1 - 2 * lam) * (2 * Work.Drive.sweepParam (period / 4 - δ₁ * u)) := rfl
    rw [hrw]
    constructor
    · have hprod := mul_nonneg hcoe htwos
      linarith
    · have hprod := mul_le_mul_of_nonneg_left htwos1 hcoe
      linarith
  have hbdd : ∀ x ∈ Set.Icc (Work.Drive.taR D (ε - δ₂ * v'))
      (Work.Drive.tbR D (ε - δ₂ * v')), |inner ℝ (deriv (deriv r) x) v| ≤ K := by
    intro x _
    calc |inner ℝ (deriv (deriv r) x) v| ≤ ‖deriv (deriv r) x‖ * ‖v‖ :=
          abs_real_inner_le_norm _ _
      _ = ‖deriv (deriv r) x‖ := by rw [hv, mul_one]
      _ ≤ K := hacc x
  have hd := Work.Drive.Generic.nclm_dev_scalar_le (D := D) (r := r) hr (y := v) (B := K)
    (σ := ε - δ₂ * v') (ξ := Work.Drive.arcFrac lam δ₁ (period / 4) u) hw hξ hbdd
  -- the width bound
  have hWb : Work.Drive.sweepW' D (ε - δ₂ * v') ≤ 2 * W := hWσ _ hσlo hσhi
  have h4 : (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 ≤ (2 * W) ^ 2 :=
    pow_le_pow_left₀ hw.le hWb 2
  have hA : Work.Drive.arcFrac lam δ₁ (period / 4) u
      * (1 - Work.Drive.arcFrac lam δ₁ (period / 4) u) / 2 ≤ 1 / 8 := by
    have hsq : (0 : ℝ) ≤ (2 * Work.Drive.arcFrac lam δ₁ (period / 4) u - 1) ^ 2 := sq_nonneg _
    have h : Work.Drive.arcFrac lam δ₁ (period / 4) u
        * (1 - Work.Drive.arcFrac lam δ₁ (period / 4) u) ≤ 1 / 4 := by nlinarith [hsq]
    linarith
  refine hd.trans ?_
  have hmid : Work.Drive.arcFrac lam δ₁ (period / 4) u
        * (1 - Work.Drive.arcFrac lam δ₁ (period / 4) u) / 2
        * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2
      ≤ (1 / 8) * (2 * W) ^ 2 := by
    calc Work.Drive.arcFrac lam δ₁ (period / 4) u
          * (1 - Work.Drive.arcFrac lam δ₁ (period / 4) u) / 2
          * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2
        = (Work.Drive.arcFrac lam δ₁ (period / 4) u
            * (1 - Work.Drive.arcFrac lam δ₁ (period / 4) u) / 2)
            * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 := by ring
      _ ≤ (1 / 8) * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 :=
          mul_le_mul_of_nonneg_right hA (sq_nonneg _)
      _ ≤ (1 / 8) * (2 * W) ^ 2 := mul_le_mul_of_nonneg_left h4 (by norm_num)
  calc Work.Drive.arcFrac lam δ₁ (period / 4) u
        * (1 - Work.Drive.arcFrac lam δ₁ (period / 4) u) / 2
        * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 * K
      = (Work.Drive.arcFrac lam δ₁ (period / 4) u
          * (1 - Work.Drive.arcFrac lam δ₁ (period / 4) u) / 2
          * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2) * K := by ring
    _ ≤ ((1 / 8) * (2 * W) ^ 2) * K := mul_le_mul_of_nonneg_right hmid hK
    _ = W ^ 2 * K / 2 := by ring

theorem basePoint_v_coord {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} {D : Work.Drive.SweepData d}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {K W lam δ₁ δ₂ ε : ℝ} {v : LeanEval.KnotTheory.Quadrisecant.Space}
    (hK : 0 ≤ K) (hW : 0 ≤ W) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1 / 2)
    (hδ₁0 : 0 < δ₁) (hδ₁4 : δ₁ ≤ LeanEval.KnotTheory.Quadrisecant.period / 4)
    (hδ₂0 : 0 < δ₂) (hδ₂ε : δ₂ ≤ ε / 2) (hε0 : 0 < ε) (hε12 : ε ≤ 1 / 2)
    (hv : ‖v‖ = 1)
    (hacc : ∀ x : ℝ, ‖deriv (deriv r) x‖ ≤ K)
    (hWσ : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → Work.Drive.sweepW' D σ ≤ 2 * W)
    (hCv : Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
        = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v) :
    |inner ℝ (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0 - Work.Drive.chordEndA r D δ₂ ε) v
        - ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 2| ≤ W ^ 2 * K / 2 := by
  have hzone : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
      Work.Drive.sweepParam (LeanEval.KnotTheory.Quadrisecant.period / 4 - δ₁ * u) ≤ 1 / 2 :=
    fun u hu => Work.Drive.sweepParam_quarter_sub_le hδ₁0.le hδ₁4 hu
  -- the deviation formula at the middle of the retained arc
  have hid := Work.Drive.needleFam_inner_eq_devAvg (r := r) (D := D) (lam := lam) (δ₁ := δ₁)
    (δ₂ := δ₂) (ε := ε) (t := LeanEval.KnotTheory.Quadrisecant.period / 4)
    hr.smooth.continuous hlam1 hzone (e := v)
  rw [Work.Drive.Generic.integral_sweepBump_arcFrac hδ₁0 hδ₁4] at hid
  -- the chord pairing
  have hCv' : inner ℝ (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε) v
      = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ := by
    conv_lhs => rw [hCv]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
    ring
  have hgoal : inner ℝ (Work.Drive.needleFam r D lam δ₁ δ₂ ε
        (LeanEval.KnotTheory.Quadrisecant.period / 4) - Work.Drive.chordEndA r D δ₂ ε) v
      - ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 2
      = ∫ v' in (-1 : ℝ)..1, Work.Drive.sweepBump v' *
          ∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u *
            inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
              (Work.Drive.arcFrac lam δ₁ (LeanEval.KnotTheory.Quadrisecant.period / 4) u)) v := by
    rw [hid, hCv']
    ring
  -- the pointwise bound
  have hpt := loopDev_inner_abs_le (r := r) hr (D := D) (K := K) (W := W) (lam := lam)
    (δ₁ := δ₁) (δ₂ := δ₂) (ε := ε) (v := v) hK hW hlam0 hlam1 hδ₁0 hδ₁4 hδ₂0 hδ₂ε hε0 hε12 hv
    hacc hWσ
  -- the inner `sweepBump`-average
  have hInner : ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      |∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u *
        inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
          (Work.Drive.arcFrac lam δ₁ (LeanEval.KnotTheory.Quadrisecant.period / 4) u)) v|
        ≤ W ^ 2 * K / 2 := by
    intro v' hv'
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le (a := (-1 : ℝ)) (b := 1) (μ := volume)
      (g := fun u : ℝ => Work.Drive.sweepBump u * (W ^ 2 * K / 2)) (by norm_num) ?_ ?_).trans ?_
    · filter_upwards with u hu
      rw [norm_mul, Real.norm_of_nonneg (Work.Drive.sweepBump_nonneg u)]
      exact mul_le_mul_of_nonneg_left (hpt v' hv' u ⟨le_of_lt hu.1, hu.2⟩)
        (Work.Drive.sweepBump_nonneg u)
    · exact (Work.Drive.sweepBump_continuous.mul continuous_const).intervalIntegrable _ _
    · rw [intervalIntegral.integral_mul_const, Work.Drive.integral_sweepBump, one_mul]
  -- the outer `sweepBump`-average
  have hOuter : |∫ v' in (-1 : ℝ)..1, Work.Drive.sweepBump v' *
        ∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u *
          inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
            (Work.Drive.arcFrac lam δ₁ (LeanEval.KnotTheory.Quadrisecant.period / 4) u)) v|
      ≤ W ^ 2 * K / 2 := by
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le (a := (-1 : ℝ)) (b := 1) (μ := volume)
      (g := fun v' : ℝ => Work.Drive.sweepBump v' * (W ^ 2 * K / 2)) (by norm_num) ?_ ?_).trans ?_
    · filter_upwards with v' hv'
      rw [norm_mul, Real.norm_of_nonneg (Work.Drive.sweepBump_nonneg v')]
      exact mul_le_mul_of_nonneg_left (hInner v' ⟨le_of_lt hv'.1, hv'.2⟩)
        (Work.Drive.sweepBump_nonneg v')
    · exact (Work.Drive.sweepBump_continuous.mul continuous_const).intervalIntegrable _ _
    · rw [intervalIntegral.integral_mul_const, Work.Drive.integral_sweepBump, one_mul]
  simp only [Work.Drive.shiftedNeedle, zero_add]
  rw [hgoal]
  exact hOuter

end Work.Drive.H2
