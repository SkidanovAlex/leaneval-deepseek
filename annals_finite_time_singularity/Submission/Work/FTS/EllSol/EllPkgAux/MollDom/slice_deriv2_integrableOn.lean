/-
# `Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv2_integrableOn`

For a **trace-class** datum `G` (`Work.FTS.EllSol.EllPkgAux.TraceClass G`) and a radius
`w > 0`, the second angular derivative of the slice `θ ↦ G w θ` is integrable on `Iθ`:

  `IntegrableOn (fun s => deriv (deriv (fun s' => G w s')) s) Iθ`.

The whole content is the *honesty* of the first component of `SliceHonestOpen G`, which is
part of `TraceClass`: the squared second derivative, weighted by the radial weight and by
`σ_η = sin(2θ)^{-η}`, is integrable on `Iθ`.

Two elementary ingredients turn that square into a bound for the function itself:

* on the open interval `(0, π/2)` one has `sin(2θ) ∈ (0, 1]`, hence
  `σ_η θ = sin(2θ)^{-η} ≥ 1`, and the radial weight satisfies
  `(w w)² = ((1+w)/w)⁴ ≥ 1` for `w > 0`; thus
  `f(θ)² ≤ f(θ)² · (w w)² · σ_η θ` there;
* `|x| ≤ x² + 1` for every real `x`.

Hence `|f| ≤ f² · (w w)² · σ_η + 1` off the null set `{0, π/2}`, and the right-hand side is
integrable on `Iθ` (the honest hypothesis plus the constant `1`, `Iθ` having finite measure).
The target function is a.e. strongly measurable because, on the open interval, it is the
`θ`-slice of `pth (pth G)`, which is continuous on the open quadrant `Q0` (from
`SmoothOpen.pth`, part of `TraceClass`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option maxHeartbeats 800000

theorem slice_deriv2_integrableOn (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {w : ℝ} (hw : 0 < w) :
    MeasureTheory.IntegrableOn (fun s : ℝ => deriv (deriv (fun s' : ℝ => G w s')) s)
      Work.Spaces.Iθ := by
  obtain ⟨hS, -, -, -, -, -, -, hHon⟩ := hT
  -- the honest hypothesis: the weighted square of the angular second derivative is integrable
  have hgf : MeasureTheory.IntegrableOn
      (fun s : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 * (Work.Spaces.w w) ^ 2
        * Work.FTS.EllipticEst.thEta s) Work.Spaces.Iθ := hHon.1 w hw
  -- the target is the `θ`-slice of `pth (pth G)` at `z = w`
  rw [show (fun s : ℝ => deriv (deriv (fun s' : ℝ => G w s')) s)
      = fun s : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w s from rfl]
  -- `Iθ` carries the same restricted measure as the open interval `(0, π/2)`
  have hIθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))).symm
  -- the constant `1` is integrable on the finite-measure interval `Iθ`
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  have hdom : MeasureTheory.IntegrableOn
      (fun s : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 * (Work.Spaces.w w) ^ 2
        * Work.FTS.EllipticEst.thEta s + 1) Work.Spaces.Iθ := hgf.add h1
  -- a.e. strong measurability: on the open interval the slice is the composition of the
  -- continuous `pth (pth G)` on `Q0` with `s ↦ (w, s)`
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w s)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [hIθ]
    have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w s)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
          Work.FTS.EllipticEst.Q0 := ((hS.pth).pth).continuousOn
      have hg : ContinuousOn (fun s : ℝ => (w, s)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
        fun_prop
      exact h2.comp hg (fun s hs => ⟨hw, hs⟩)
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  -- the pointwise domination
  have hbound : ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.pth (Work.Spaces.pth G) w s‖
        ≤ (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta s + 1 := by
    rw [hIθ]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with s hs
    have hσ : 1 ≤ Work.FTS.EllipticEst.thEta s := by
      have hsinpos : 0 < Real.sin (2 * s) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2, Real.pi_pos])
      have hsinle : Real.sin (2 * s) ≤ 1 := Real.sin_le_one _
      rw [Work.FTS.EllipticEst.thEta]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hsinpos hsinle
        (by norm_num [Work.Spaces.eta])
    have hW : 1 ≤ (Work.Spaces.w w) ^ 2 := by
      have h1w : 1 ≤ Work.Spaces.w w := by
        rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < w ^ 2)]
        nlinarith
      calc (1 : ℝ) = 1 ^ 2 := by norm_num
        _ ≤ (Work.Spaces.w w) ^ 2 := pow_le_pow_left₀ (by norm_num) h1w 2
    have hprod : 1 ≤ (Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta s :=
      one_le_mul_of_one_le_of_one_le hW hσ
    have hfsq : (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2
        ≤ (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta s := by
      calc (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2
          = (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2
              * ((Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta s) :=
            mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
        _ = (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 * (Work.Spaces.w w) ^ 2
              * Work.FTS.EllipticEst.thEta s := by ring
    have habs : |Work.Spaces.pth (Work.Spaces.pth G) w s|
        ≤ (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|Work.Spaces.pth (Work.Spaces.pth G) w s| - 1),
        abs_nonneg (Work.Spaces.pth (Work.Spaces.pth G) w s),
        sq_abs (Work.Spaces.pth (Work.Spaces.pth G) w s)]
    rw [Real.norm_eq_abs]
    linarith [habs, hfsq]
  exact MeasureTheory.Integrable.mono' hdom haesm hbound

end Work.FTS.EllSol.EllPkgAux.MollDom
