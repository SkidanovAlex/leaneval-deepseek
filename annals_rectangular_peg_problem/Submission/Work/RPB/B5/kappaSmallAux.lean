import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.kappaDefs

/-!
# B5: elementary facts for the "small `δ`" regime of the `κ`-collar

This file collects the elementary (purely algebraic / one-variable) facts that the proof of
`Work.RPB.B5.kappa_shape_geom_small` uses in the regime `σ ∈ [0, δ]`, `δ > 0` small.

In that regime the two cutoffs of `Submission/Work/RPB/B5/kappaDefs.lean` have saturated:

* `krpf δ σ = 1` and `kphc δ k σ = 0` (both are switched by `kstp ((σ - δ)/δ)`, which vanishes for
  `σ ≤ δ`), so the "far family" is the plain rescaled curve `krd σ • CI.c τ`
  (`kfsh_of_le`), and likewise the target circle is `krd σ • e^{it}` (`ktarg_of_le`);
* `xfade δ σ = 1` (already `xfade_one` in `kappaDefs`).

Also collected here: the two-sided clamp bound `|kclamp δ σ| ≤ δ` (so that `ρh` is always evaluated
strictly inside `(-κ,κ)`), the definition `kGam = √2 • CI.c` of the reference curve family, and the
estimate `|krd σ - √2| ≤ √2 σ` for `σ ≥ 0`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## The reference curve family `√2 • CI.c` -/

/-- The reference embedded family: `√2` times the curve isotopy.  This is the curve that the glued
shape `kshape` approximates for small `δ`. -/
def kGam (CI : Work.RPV.CurveIsotopy) (τ t : ℝ) : ℂ := (Real.sqrt 2 : ℂ) * CI.c τ t

theorem kGam_apply (CI : Work.RPV.CurveIsotopy) (τ t : ℝ) :
    kGam CI τ t = (Real.sqrt 2 : ℂ) * CI.c τ t := rfl

theorem kGam_per (CI : Work.RPV.CurveIsotopy) (τ t : ℝ) :
    kGam CI τ (t + 2 * Real.pi) = kGam CI τ t := by
  rw [kGam_apply, kGam_apply, CI.per]

/-- At `τ = 0` the reference family is the circle of radius `√2`. -/
theorem kGam_zero (CI : Work.RPV.CurveIsotopy) (t : ℝ) :
    kGam CI 0 t = (Real.sqrt 2 : ℂ) * Complex.exp (t * Complex.I) := by
  rw [kGam_apply, CI.start]

theorem contDiff_kGam (CI : Work.RPV.CurveIsotopy) :
    ContDiff ℝ 1 (fun z : ℝ × ℝ => kGam CI z.1 z.2) := by
  have h2 : ContDiff ℝ 1 (fun z : ℝ × ℝ => CI.c z.1 z.2) := CI.smooth.of_le (by norm_num)
  have h := (contDiff_const (c := (Real.sqrt 2 : ℂ))).mul h2
  simpa only [kGam] using h

theorem contDiff_kGam_slice (CI : Work.RPV.CurveIsotopy) (τ : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => kGam CI τ t) := by
  have h2 : ContDiff ℝ 1 (fun t : ℝ => CI.c τ t) := by
    have h : ContDiff ℝ 1 (fun z : ℝ × ℝ => CI.c z.1 z.2) := CI.smooth.of_le (by norm_num)
    simpa [Function.comp_def] using h.comp ((contDiff_const (c := τ)).prodMk contDiff_id)
  have h := (contDiff_const (c := (Real.sqrt 2 : ℂ))).mul h2
  simpa only [kGam] using h

theorem deriv_kGam (CI : Work.RPV.CurveIsotopy) (τ t : ℝ) :
    deriv (fun s : ℝ => kGam CI τ s) t = (Real.sqrt 2 : ℂ) * deriv (fun s : ℝ => CI.c τ s) t := by
  have hd : DifferentiableAt ℝ (fun s : ℝ => CI.c τ s) t := by
    have h : ContDiff ℝ 1 (fun s : ℝ => CI.c τ s) := by
      have h0 : ContDiff ℝ 1 (fun z : ℝ × ℝ => CI.c z.1 z.2) := CI.smooth.of_le (by norm_num)
      simpa [Function.comp_def] using h0.comp ((contDiff_const (c := τ)).prodMk contDiff_id)
    exact h.contDiffAt.differentiableAt (by norm_num)
  show deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t = _
  exact deriv_const_mul (Real.sqrt 2 : ℂ) hd

theorem deriv_kGam_ne (CI : Work.RPV.CurveIsotopy) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) : deriv (fun s : ℝ => kGam CI τ s) t ≠ 0 := by
  rw [deriv_kGam]
  refine mul_ne_zero ?_ (CI.imm τ hτ t)
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'

/-! ## The small-`δ` regime of the cutoffs -/

theorem krpf_of_le {δ σ : ℝ} (hδ : 0 < δ) (h : σ ≤ δ) : krpf δ σ = 1 := by
  unfold krpf
  have hz : kstp ((σ - δ) / δ) = 0 :=
    kstp_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  rw [hz, sub_zero]

theorem kphc_of_le {δ : ℝ} (hδ : 0 < δ) (k : ℤ) {σ : ℝ} (h : σ ≤ δ) :
    kphc δ k σ = 0 := by
  unfold kphc
  have hz : kstp ((σ - δ) / δ) = 0 :=
    kstp_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  rw [hz, mul_zero]

theorem ktarg_of_le {δ : ℝ} (hδ : 0 < δ) (k : ℤ) {σ t : ℝ} (h : σ ≤ δ) :
    ktarg δ k σ t = (krd σ : ℂ) * Complex.exp (t * Complex.I) := by
  unfold ktarg
  rw [kphc_of_le hδ k h]
  push_cast
  simp

theorem kfsh_of_le (CI : Work.RPV.CurveIsotopy) {δ : ℝ} (hδ : 0 < δ) (k : ℤ) {σ τ t : ℝ}
    (h : σ ≤ δ) : kfsh CI δ k τ σ t = (krd σ : ℂ) * CI.c τ t := by
  unfold kfsh
  rw [krpf_of_le hδ h, kphc_of_le hδ k h, one_mul, add_zero]

theorem abs_kclamp_le' {δ σ : ℝ} (hδ : 0 < δ) : |kclamp δ σ| ≤ δ := abs_kclamp_le hδ

/-- For `σ ∈ [0, δ]` and any `d > δ` the clamp is strictly inside `(-d, d)`. -/
theorem kclamp_mem_Ioo {δ d σ : ℝ} (hδ : 0 < δ) (hd : δ < d) (hσ : σ ∈ Set.Icc (0 : ℝ) δ) :
    kclamp δ σ ∈ Set.Ioo (-d) d := by
  have h := abs_kclamp_le hδ (σ := σ)
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem kblf_nonneg (δ σ : ℝ) : 0 ≤ kblf δ σ := kstp_nonneg _

theorem kblf_le_one (δ σ : ℝ) : kblf δ σ ≤ 1 := kstp_le_one _

theorem kbbmp_nonneg (δ τ : ℝ) : 0 ≤ kbbmp δ τ := by
  unfold kbbmp; linarith [kstp_le_one (τ / δ)]

theorem kbbmp_le_one (δ τ : ℝ) : kbbmp δ τ ≤ 1 := by
  unfold kbbmp; linarith [kstp_nonneg (τ / δ)]

/-! ## The radius `krd σ = √(2 + 2σ)` -/

theorem krd_pos {σ : ℝ} (h : 0 ≤ σ) : 0 < krd σ := by
  unfold krd
  exact Real.sqrt_pos.mpr (by linarith)

theorem krd_ge_sqrt_two {σ : ℝ} (h : 0 ≤ σ) : Real.sqrt 2 ≤ krd σ := by
  unfold krd
  exact Real.sqrt_le_sqrt (by linarith)

/-- The key estimate of the small-`δ` regime: `|√(2 + 2σ) - √2| ≤ √2 σ` for `σ ≥ 0`. -/
theorem abs_krd_sub_sqrt_two_le {σ : ℝ} (h : 0 ≤ σ) :
    |krd σ - Real.sqrt 2| ≤ Real.sqrt 2 * σ := by
  have h1 : Real.sqrt 2 ≤ krd σ := krd_ge_sqrt_two h
  have hfac : krd σ = Real.sqrt 2 * Real.sqrt (1 + σ) := by
    unfold krd
    rw [show 2 + 2 * σ = 2 * (1 + σ) by ring, Real.sqrt_mul (by norm_num)]
  have hsq : Real.sqrt (1 + σ) ≤ 1 + σ := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith [h]
  rw [abs_of_nonneg (by linarith), hfac]
  have h2pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [hsq, h2pos]

end Work.RPB.B5
