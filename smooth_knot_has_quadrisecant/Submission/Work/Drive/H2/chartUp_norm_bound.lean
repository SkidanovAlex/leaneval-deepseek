import Mathlib
import Submission.Work.Drive.AB.pinSetup
import Submission.Work.Drive.AB.needleFam_inner_eq_devAvg
import Submission.Work.Drive.Generic.nclmDev
import Submission.Work.Drive.Generic.nclmWindow
import Submission.Work.Drive.Generic.nclmBasic
import Submission.Work.Drive.Generic.nclmChart
import Submission.Work.Drive.Generic.nclm_chartUp_inner

namespace Work.Drive.H2

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-- Two double `sweepBump`-averages agree as soon as the integrands agree on the square
`[-1,1]²`. -/
lemma bumpAvg₂_congr_Icc {f g : ℝ → ℝ → ℝ}
    (h : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1, f v' u = g v' u) :
    Work.Drive.Generic.bumpAvg₂ f = Work.Drive.Generic.bumpAvg₂ g := by
  unfold Work.Drive.Generic.bumpAvg₂
  refine intervalIntegral.integral_congr (fun v' hv' => ?_)
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hv'
  congr 1
  refine intervalIntegral.integral_congr (fun u hu => ?_)
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
  rw [h v' hv' u hu]

theorem chartUp_norm_bound {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
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
    ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ ≤ W ^ 2 * K := by
  have hW2K : (0 : ℝ) ≤ W ^ 2 * K := by positivity
  rcases eq_or_ne (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) 0 with hzero | hne
  · rw [hzero, norm_zero]
    exact hW2K
  have hcont : Continuous r := hr.smooth.continuous
  have hzone : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
      Work.Drive.sweepParam (LeanEval.KnotTheory.Quadrisecant.period / 4 - δ₁ * u) ≤ 1 / 2 :=
    fun u hu => Work.Drive.sweepParam_quarter_sub_le hδ₁0.le hδ₁4 hu
  have hid := Work.Drive.Generic.nclm_chartUp_inner (r := r) (D := D) (lam := lam)
    (δ₁ := δ₁) (δ₂ := δ₂) (ε := ε) (v := v) hcont hlam1 hδ₁0 hδ₁4 hv hCv
  have hchart_ne : ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  set y : Space :=
    (‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖)⁻¹ • Work.Drive.chartUp r D lam δ₁ δ₂ ε v with hy
  have hy_norm : ‖y‖ = 1 := by
    rw [hy, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hchart_ne]
  have hchart_v : inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) v = 0 :=
    inner_chartUp_v r D lam δ₁ δ₂ ε hv
  have hv_y : inner ℝ v y = 0 := by
    rw [hy, real_inner_smul_right,
      real_inner_comm (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) v, hchart_v, mul_zero]
  have hchart_inner : inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) y
      = ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
    rw [hy, real_inner_smul_right, real_inner_self_eq_norm_sq, sq]
    rw [← mul_assoc, inv_mul_cancel₀ hchart_ne, one_mul]
  have hξmem : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
      Work.Drive.Generic.arcFracQ lam δ₁ u ∈ Set.Icc (0 : ℝ) 1 := by
    intro u hu
    rw [← Work.Drive.Generic.arcFrac_quarter_eq hδ₁0 hδ₁4 hu]
    have hsp0 : 0 ≤ Work.Drive.sweepParam
        (LeanEval.KnotTheory.Quadrisecant.period / 4 - δ₁ * u) :=
      (Work.Drive.sweepParam_mem _).1
    have hsp1 : Work.Drive.sweepParam
        (LeanEval.KnotTheory.Quadrisecant.period / 4 - δ₁ * u) ≤ 1 / 2 := hzone u hu
    have hrw : Work.Drive.arcFrac lam δ₁ (LeanEval.KnotTheory.Quadrisecant.period / 4) u
        = lam + (1 - 2 * lam) * (2 * Work.Drive.sweepParam
            (LeanEval.KnotTheory.Quadrisecant.period / 4 - δ₁ * u)) := rfl
    rw [hrw]
    constructor <;> nlinarith
  have hkey : inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) y
      = Work.Drive.Generic.bumpAvg₂ (fun v' u =>
          inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
            (Work.Drive.Generic.arcFracQ lam δ₁ u)) y) := by
    rw [hid y]
    refine bumpAvg₂_congr_Icc (fun v' _ u hu => ?_)
    rw [hv_y, zero_mul, sub_zero, ← Work.Drive.Generic.arcFrac_quarter_eq hδ₁0 hδ₁4 hu]
  have hbound : |Work.Drive.Generic.bumpAvg₂ (fun v' u =>
      inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
        (Work.Drive.Generic.arcFracQ lam δ₁ u)) y)| ≤ W ^ 2 * K := by
    refine Work.Drive.Generic.bumpAvg₂_abs_le' ?_ ?_
    · have hL : Continuous (fun p : ℝ × ℝ => Work.Drive.loopDev r D (ε - δ₂ * p.1)
          (Work.Drive.Generic.arcFracQ lam δ₁ p.2)) :=
        Work.Drive.Generic.continuous_loopDevQ hcont D lam δ₁ δ₂ ε
      exact hL.inner continuous_const
    · intro v' hv' u hu
      have hσlo : ε - δ₂ ≤ ε - δ₂ * v' := by nlinarith [hv'.2, hδ₂0]
      have hσhi : ε - δ₂ * v' ≤ ε + δ₂ := by nlinarith [hv'.1, hδ₂0]
      have hσ0 : 0 < ε - δ₂ * v' := by linarith
      have hσ1 : ε - δ₂ * v' < 1 := by linarith
      have hw : 0 < Work.Drive.sweepW' D (ε - δ₂ * v') :=
        Work.Drive.wds_sweepW'_pos D hσ0 hσ1
      have hbdd : ∀ x ∈ Set.Icc (Work.Drive.taR D (ε - δ₂ * v'))
          (Work.Drive.tbR D (ε - δ₂ * v')),
          |inner ℝ (deriv (deriv r) x) y| ≤ K := by
        intro x _
        calc |inner ℝ (deriv (deriv r) x) y|
            ≤ ‖deriv (deriv r) x‖ * ‖y‖ := abs_real_inner_le_norm _ _
          _ = ‖deriv (deriv r) x‖ := by rw [hy_norm, mul_one]
          _ ≤ K := hacc x
      have hdev := Work.Drive.Generic.nclm_dev_scalar_le (D := D) (r := r) hr hw
        (hξmem u hu) hbdd
      refine hdev.trans ?_
      have hξle : Work.Drive.Generic.arcFracQ lam δ₁ u
            * (1 - Work.Drive.Generic.arcFracQ lam δ₁ u) / 2 ≤ 1 / 8 := by
        nlinarith [(hξmem u hu).1, (hξmem u hu).2,
          sq_nonneg (Work.Drive.Generic.arcFracQ lam δ₁ u - 1 / 2)]
      have hsqle : (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 ≤ (2 * W) ^ 2 :=
        sq_le_sq' (by linarith [hw.le, hW]) (hWσ _ hσlo hσhi)
      have h1 : (Work.Drive.Generic.arcFracQ lam δ₁ u
            * (1 - Work.Drive.Generic.arcFracQ lam δ₁ u) / 2)
            * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 ≤ (1 / 8) * (2 * W) ^ 2 :=
        mul_le_mul hξle hsqle (sq_nonneg _) (by norm_num)
      calc (Work.Drive.Generic.arcFracQ lam δ₁ u
              * (1 - Work.Drive.Generic.arcFracQ lam δ₁ u) / 2)
              * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 * K
          ≤ (1 / 8) * (2 * W) ^ 2 * K := mul_le_mul_of_nonneg_right h1 hK
        _ = W ^ 2 * K / 2 := by ring
        _ ≤ W ^ 2 * K := by nlinarith [mul_nonneg (sq_nonneg W) hK]
  calc ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖
      = inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) y := hchart_inner.symm
    _ ≤ |inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) y| := le_abs_self _
    _ = |Work.Drive.Generic.bumpAvg₂ (fun v' u => inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
          (Work.Drive.Generic.arcFracQ lam δ₁ u)) y)| := by rw [hkey]
    _ ≤ W ^ 2 * K := hbound

end Work.Drive.H2
