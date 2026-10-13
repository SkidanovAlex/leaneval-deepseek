import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.eigenFTCPoleDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `WeakPureAux/eigenPoleHalves` — the two halves of the eigen-slice pole bound

For a `C^2` function `u` on `(0, π/2)` with `Lzero1 u = mu * u` (the eigenrelation of the
`Lzero1`-slice), the running quantities of the `(Dfun, Rfun)` system are bounded:

* right half: `∃ B ≥ 0, ∀ θ ∈ [π/4, π/2), |Rfun u θ| ≤ |Rfun u (π/4)| + B · Ki θ`
  (`Rfun_right_const`), obtained from `Rfun_run_bound` together with the uniform bound on the
  running mass `Gd u θ = ∫_{π/4}^{θ}|Rfun u| · ew` (`Gd_bound`);
* left half: the mirror statement with `Kl`
  (`Rfun_left_const`), from `Rfun_run_bound_left` and `GdL u θ = ∫_{θ}^{π/4}|Rfun u| · ew`
  bounded (`GdL_bound`).

Both uniform bounds are constant-coefficient Grönwall inequalities: the weights satisfy
`ew · Ki ≤ π⁴/128` on `[π/4, π/2)` and `ew · Kl ≤ π³/16` on `(0, π/4]`, which makes the
coefficient of the running mass bounded, so Mathlib's
`norm_le_gronwallBound_of_norm_deriv_right_le` applies (directly on the right half, and to the
mirrored primitive `x ↦ ∫_0^x |Rfun u (π/4 - t)| ew (π/4 - t) dt` on the left half).
-/

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

theorem Dfun_run_bound_left {u : ℝ → ℝ} {mu : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (heig : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ = mu * u θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4)) :
    |LzeroGrowth.Dfun u θ| ≤ |LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ := by
  have hq : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hpt : ∀ s ∈ Set.Icc θ (Real.pi / 4),
      |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|
        = 2 * |mu| * (|LzeroGrowth.Rfun u s| * ew s) := by
    intro s hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, hs.1], by linarith [hθ.2, hs.2, Real.pi_pos]⟩
    have hsin : 0 < Real.sin (2 * s) := LzeroGrowth.sin_two_pos hs'
    have hsinθ : 0 ≤ Real.sin s :=
      (Real.sin_pos_of_pos_of_lt_pi hs'.1 (by linarith [hs'.2, Real.pi_pos])).le
    have hu_eq : u s = LzeroGrowth.Rfun u s * Real.sin (2 * s) :=
      (Work.FTS.EllipticEst.H2W.Lzero1Growth.Rfun_mul_sin (u := u) hs').symm
    have hL : Work.FTS.EllipticEst.Lzero1 u s = mu * u s := heig s hs'
    rw [hL, hu_eq, ew, Work.Elliptic.sinCos2]
    rw [abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (mul_nonneg hsinθ (sq_nonneg (Real.cos s))),
      abs_of_pos hsin]
    ring
  have hftc := Dfun_ftc hu hθ' hq hθ.2
  have h1 : |LzeroGrowth.Dfun u (Real.pi / 4) - LzeroGrowth.Dfun u θ|
      ≤ ∫ s in θ..(Real.pi / 4),
          |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s| := by
    rw [hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hθ.2
  have hcontL : ContinuousOn
      (fun s : ℝ => |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|)
      (Set.Icc θ (Real.pi / 4)) :=
    (((Work.FTS.EllipticEst.H2W.Lzero1Growth.continuousOn_Lzero1 hu).const_mul 2 |>.mono
        (fun s hs => ⟨by linarith [hθ.1, hs.1, Real.pi_pos],
          by linarith [hθ.2, hs.2, Real.pi_pos]⟩)).mul
      continuous_sinCos2.continuousOn).abs
  have hcontR : ContinuousOn (LzeroGrowth.Rfun u) (Set.Icc θ (Real.pi / 4)) :=
    (continuousOn_Rfun hu).mono (fun s hs =>
      ⟨by linarith [hθ.1, hs.1, Real.pi_pos], by linarith [hθ.2, hs.2, Real.pi_pos]⟩)
  have h3 : (∫ s in θ..(Real.pi / 4),
        |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|)
      ≤ ∫ s in θ..(Real.pi / 4),
          2 * |mu| * (|LzeroGrowth.Rfun u s| * ew s) :=
    intervalIntegral.integral_mono_on hθ.2 (hcontL.intervalIntegrable_of_Icc hθ.2)
      (((hcontR.abs).mul ew_continuous.continuousOn).const_mul (2 * |mu|)
        |>.intervalIntegrable_of_Icc hθ.2)
      (fun s hs => (hpt s hs).le)
  have h4 : (∫ s in θ..(Real.pi / 4),
        2 * |mu| * (|LzeroGrowth.Rfun u s| * ew s))
      = 2 * |mu| * GdL u θ := by
    rw [GdL, intervalIntegral.integral_const_mul]
  have habs : |LzeroGrowth.Dfun u θ - LzeroGrowth.Dfun u (Real.pi / 4)|
      = |LzeroGrowth.Dfun u (Real.pi / 4) - LzeroGrowth.Dfun u θ| := abs_sub_comm _ _
  calc |LzeroGrowth.Dfun u θ|
      = |LzeroGrowth.Dfun u (Real.pi / 4)
          + (LzeroGrowth.Dfun u θ - LzeroGrowth.Dfun u (Real.pi / 4))| := by
        congr 1; ring
    _ ≤ |LzeroGrowth.Dfun u (Real.pi / 4)|
          + |LzeroGrowth.Dfun u θ - LzeroGrowth.Dfun u (Real.pi / 4)| := abs_add_le _ _
    _ = |LzeroGrowth.Dfun u (Real.pi / 4)|
          + |LzeroGrowth.Dfun u (Real.pi / 4) - LzeroGrowth.Dfun u θ| := by rw [habs]
    _ ≤ |LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ :=
        add_le_add le_rfl (le_trans h1 (le_trans h3 (le_of_eq h4)))

theorem GdL_mono {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.pi / 4) : GdL u b ≤ GdL u a := by
  have hint1 : IntervalIntegrable (fun s : ℝ => |LzeroGrowth.Rfun u s| * ew s)
      volume a b :=
    (continuousOn_absRfun_mul_ew hu ⟨ha, by linarith [hab, hb, Real.pi_pos]⟩
      ⟨by linarith [ha, Real.pi_pos], by linarith [Real.pi_pos]⟩).intervalIntegrable_of_Icc hab
  have hint2 : IntervalIntegrable (fun s : ℝ => |LzeroGrowth.Rfun u s| * ew s)
      volume b (Real.pi / 4) :=
    (continuousOn_absRfun_mul_ew hu ⟨by linarith [ha, hab], by linarith [hb, Real.pi_pos]⟩
      ⟨by linarith [ha, Real.pi_pos], by linarith [Real.pi_pos]⟩).intervalIntegrable_of_Icc hb
  have hsplit : GdL u a
      = (∫ s in a..b, |LzeroGrowth.Rfun u s| * ew s) + GdL u b := by
    rw [GdL, GdL]
    exact (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  have hnn : 0 ≤ ∫ s in a..b, |LzeroGrowth.Rfun u s| * ew s := by
    have h := intervalIntegral.integral_mono_on hab
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b) hint1
      (fun s hs => mul_nonneg (abs_nonneg _) (ew_nonneg ⟨by linarith [ha, hs.1],
        by linarith [hb, hs.2, Real.pi_pos]⟩))
    simpa using h
  linarith [hsplit, hnn]

theorem Rfun_run_bound_left {u : ℝ → ℝ} {mu : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (heig : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ = mu * u θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4)) :
    |LzeroGrowth.Rfun u θ|
      ≤ |LzeroGrowth.Rfun u (Real.pi / 4)|
        + (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ) * Kl θ := by
  have hq : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hq0 : (0 : ℝ) < Real.pi / 4 := hq.1
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hftc := Rfun_ftc_ek hu hθ' hq hθ.2
  have h2 : ∀ s ∈ Set.Icc θ (Real.pi / 4),
      |ek s * (-(LzeroGrowth.Dfun u s))|
        ≤ (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ) * ek s := by
    intro s hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, hs.1, Real.pi_pos], by linarith [hθ.2, hs.2, Real.pi_pos]⟩
    have hk : 0 ≤ ek s := ek_nonneg hs'
    have hD := Dfun_run_bound_left (u := u) (mu := mu) hu heig (θ := s)
      ⟨by linarith [hθ.1, hs.1], by linarith [hs.2, hθ.2]⟩
    have hG : GdL u s ≤ GdL u θ := GdL_mono hu hθ.1 hs.1 hs.2
    have h2m : (0 : ℝ) ≤ 2 * |mu| := by positivity
    have hstep : |LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u s
        ≤ |LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ := by
      linarith [mul_le_mul_of_nonneg_left hG h2m]
    rw [abs_mul, abs_neg, abs_of_nonneg hk]
    calc ek s * |LzeroGrowth.Dfun u s|
        ≤ ek s * (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u s) :=
          mul_le_mul_of_nonneg_left hD hk
      _ ≤ ek s * (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ) :=
          mul_le_mul_of_nonneg_left hstep hk
      _ = (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ) * ek s := by ring
  have h1 : |LzeroGrowth.Rfun u (Real.pi / 4) - LzeroGrowth.Rfun u θ|
      ≤ ∫ s in θ..(Real.pi / 4), |ek s * (-(LzeroGrowth.Dfun u s))| := by
    rw [hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hθ.2
  have hcont1 : ContinuousOn
      (fun s : ℝ => |ek s * (-(LzeroGrowth.Dfun u s))|) (Set.Icc θ (Real.pi / 4)) :=
    (ContinuousOn.mul (continuousOn_ek hθ.1 (by linarith [hθ.2, Real.pi_pos]))
      (((Work.FTS.EllipticEst.H2W.Lzero1Growth.continuousOn_Dfun hu).mono (fun s hs =>
        ⟨by linarith [hθ.1, hs.1], by linarith [hθ.2, hs.2, Real.pi_pos]⟩)).neg)).abs
  have hcont2 : ContinuousOn
      (fun s : ℝ => (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ) * ek s)
      (Set.Icc θ (Real.pi / 4)) :=
    continuousOn_const.mul (continuousOn_ek hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  have h3 := intervalIntegral.integral_mono_on (μ := volume) hθ.2
    (hcont1.intervalIntegrable_of_Icc hθ.2) (hcont2.intervalIntegrable_of_Icc hθ.2) h2
  have h4 : (∫ s in θ..(Real.pi / 4),
        (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ) * ek s)
      = (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ) * Kl θ := by
    rw [Kl]
    exact intervalIntegral.integral_const_mul _ _
  have hkey : |LzeroGrowth.Rfun u (Real.pi / 4) - LzeroGrowth.Rfun u θ|
      ≤ (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ) * Kl θ :=
    le_trans (le_trans h1 h3) (le_of_eq h4)
  have habs : |LzeroGrowth.Rfun u θ - LzeroGrowth.Rfun u (Real.pi / 4)|
      = |LzeroGrowth.Rfun u (Real.pi / 4) - LzeroGrowth.Rfun u θ| := abs_sub_comm _ _
  calc |LzeroGrowth.Rfun u θ|
      = |LzeroGrowth.Rfun u (Real.pi / 4)
          + (LzeroGrowth.Rfun u θ - LzeroGrowth.Rfun u (Real.pi / 4))| := by
        congr 1; ring
    _ ≤ |LzeroGrowth.Rfun u (Real.pi / 4)|
          + |LzeroGrowth.Rfun u θ - LzeroGrowth.Rfun u (Real.pi / 4)| := abs_add_le _ _
    _ = |LzeroGrowth.Rfun u (Real.pi / 4)|
          + |LzeroGrowth.Rfun u (Real.pi / 4) - LzeroGrowth.Rfun u θ| := by rw [habs]
    _ ≤ |LzeroGrowth.Rfun u (Real.pi / 4)|
          + (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ) * Kl θ :=
        add_le_add le_rfl hkey

/-! ## The Grönwall step on the left half -/

theorem GdL_bound {u : ℝ → ℝ} {mu : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (heig : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ = mu * u θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4), GdL u θ ≤ C := by
  set P : ℝ := 2 * |mu| * (Real.pi ^ 3 / 16) with hPdef
  set Q : ℝ := |LzeroGrowth.Rfun u (Real.pi / 4)|
    + |LzeroGrowth.Dfun u (Real.pi / 4)| * (Real.pi ^ 3 / 16) with hQdef
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQdef]; positivity
  have hmass : ∀ y ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
      |LzeroGrowth.Rfun u y| * ew y ≤ P * GdL u y + Q := by
    intro y hy
    have hy2 : y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
    have hew0 : 0 ≤ ew y := ew_nonneg hy2
    have hR := Rfun_run_bound_left hu heig hy
    have h1 := mul_le_mul_of_nonneg_right hR hew0
    have hKlw : Kl y * ew y ≤ Real.pi ^ 3 / 16 := by
      rw [mul_comm]; exact ew_mul_Kl_le hy
    have hA1 : |LzeroGrowth.Rfun u (Real.pi / 4)| * ew y
        ≤ |LzeroGrowth.Rfun u (Real.pi / 4)| * 1 :=
      mul_le_mul_of_nonneg_left (ew_le_one y) (abs_nonneg _)
    have hD1 : |LzeroGrowth.Dfun u (Real.pi / 4)| * (Kl y * ew y)
        ≤ |LzeroGrowth.Dfun u (Real.pi / 4)| * (Real.pi ^ 3 / 16) :=
      mul_le_mul_of_nonneg_left hKlw (abs_nonneg _)
    have hG0 : 0 ≤ GdL u y := GdL_nonneg hu hy
    have hP1 : 2 * |mu| * GdL u y * (Kl y * ew y) ≤ P * GdL u y := by
      have h := mul_le_mul_of_nonneg_left hKlw (by positivity : (0 : ℝ) ≤ 2 * |mu| * GdL u y)
      rw [hPdef]
      nlinarith [h]
    have hexp : (|LzeroGrowth.Rfun u (Real.pi / 4)|
          + (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u y) * Kl y) * ew y
        = |LzeroGrowth.Rfun u (Real.pi / 4)| * ew y
          + |LzeroGrowth.Dfun u (Real.pi / 4)| * (Kl y * ew y)
          + 2 * |mu| * GdL u y * (Kl y * ew y) := by ring
    have hsum : (|LzeroGrowth.Rfun u (Real.pi / 4)|
          + (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u y) * Kl y) * ew y
        ≤ P * GdL u y + Q := by
      rw [hexp, hQdef]
      linarith [hA1, hD1, hP1]
    linarith [h1, hsum]
  set g : ℝ → ℝ := fun t => |LzeroGrowth.Rfun u (Real.pi / 4 - t)| * ew (Real.pi / 4 - t)
    with hgdef
  have hgopen : ∀ t ∈ Set.Ioo (-(1 : ℝ) / 4) (Real.pi / 4), ContinuousAt g t := by
    intro t ht
    have hy : Real.pi / 4 - t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [ht.2], by linarith [ht.1, Real.pi_gt_three]⟩
    have hRfun : ContinuousAt (LzeroGrowth.Rfun u) (Real.pi / 4 - t) := by
      have h1 : ContinuousAt u (Real.pi / 4 - t) :=
        (Work.FTS.EllipticEst.H2W.Lzero1Growth.hasDerivAt_u hu hy).continuousAt
      have h2 : ContinuousAt (fun s : ℝ => Real.sin (2 * s)) (Real.pi / 4 - t) := by
        fun_prop
      have h3 : Real.sin (2 * (Real.pi / 4 - t)) ≠ 0 := ne_of_gt (LzeroGrowth.sin_two_pos hy)
      exact h1.div h2 h3
    have hf : ContinuousAt (fun s : ℝ => |LzeroGrowth.Rfun u s| * ew s) (Real.pi / 4 - t) :=
      (hRfun.abs).mul ew_continuous.continuousAt
    have hlin : ContinuousAt (fun t : ℝ => Real.pi / 4 - t) t :=
      continuousAt_const.sub continuousAt_id
    have hcomp := hf.comp hlin
    rw [hgdef]
    exact hcomp
  have hprim : ∀ b ∈ Set.Ico (0 : ℝ) (Real.pi / 4),
      (∫ t in (0 : ℝ)..b, g t) ≤ gronwallBound 0 P Q b := by
    intro b hb
    have hb0 : 0 ≤ b := hb.1
    have hblt : b < Real.pi / 4 := hb.2
    have hgcont : ContinuousOn g (Set.Icc 0 b) := fun x hx =>
      (hgopen x ⟨by linarith [hx.1, hx.2, hblt], by linarith [hx.2, hblt]⟩).continuousWithinAt
    have hgint : IntegrableOn g (Set.Icc 0 b) := hgcont.integrableOn_Icc
    have hcontIoc : ContinuousOn (fun x : ℝ => ∫ t in Set.Ioc (0 : ℝ) x, g t)
        (Set.Icc 0 b) := intervalIntegral.continuousOn_primitive hgint
    have hcont : ContinuousOn (fun x : ℝ => ∫ t in (0 : ℝ)..x, g t) (Set.Icc 0 b) :=
      hcontIoc.congr (fun x hx => intervalIntegral.integral_of_le hx.1)
    have hderiv : ∀ x ∈ Set.Ico (0 : ℝ) b,
        HasDerivWithinAt (fun x : ℝ => ∫ t in (0 : ℝ)..x, g t) (g x) (Set.Ici x) x := by
      intro x hx
      have hxlt : x < Real.pi / 4 := lt_of_lt_of_le hx.2 hblt.le
      have hint : IntervalIntegrable g volume (0 : ℝ) x :=
        (hgcont.mono (fun y hy => ⟨hy.1, by linarith [hy.2, hx.2]⟩)).intervalIntegrable_of_Icc hx.1
      have hcontAt : ContinuousAt g x := hgopen x ⟨by linarith [hx.1], hxlt⟩
      have hmeas : StronglyMeasurableAtFilter g (𝓝 x) volume :=
        ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo (-(1 : ℝ) / 4) (Real.pi / 4))
          isOpen_Ioo hgopen x ⟨by linarith [hx.1], hxlt⟩
      exact (intervalIntegral.integral_hasDerivAt_right hint hmeas hcontAt).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Ico (0 : ℝ) b, ‖g x‖
        ≤ P * ‖∫ t in (0 : ℝ)..x, g t‖ + Q := by
      intro x hx
      have hxlt : x < Real.pi / 4 := lt_of_lt_of_le hx.2 hblt.le
      have hy : Real.pi / 4 - x ∈ Set.Ioc (0 : ℝ) (Real.pi / 4) :=
        ⟨by linarith [hxlt], by linarith [hx.1]⟩
      have hy2 : Real.pi / 4 - x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
      have hgnn : 0 ≤ g x := mul_nonneg (abs_nonneg _) (ew_nonneg hy2)
      have hval := hmass (Real.pi / 4 - x) hy
      have hnorm : ‖g x‖ = |LzeroGrowth.Rfun u (Real.pi / 4 - x)| * ew (Real.pi / 4 - x) := by
        rw [hgdef, Real.norm_eq_abs, abs_of_nonneg hgnn]
      rw [hnorm]
      have hchange : (∫ t in (0 : ℝ)..x, g t) = GdL u (Real.pi / 4 - x) := by
        have h := intervalIntegral.integral_comp_sub_left
          (f := fun s : ℝ => |LzeroGrowth.Rfun u s| * ew s) (a := (0 : ℝ)) (b := x)
          (Real.pi / 4)
        rw [hgdef]
        refine h.trans ?_
        rw [GdL]
        congr 1 <;> ring
      have hle : P * GdL u (Real.pi / 4 - x) + Q
          ≤ P * ‖∫ t in (0 : ℝ)..x, g t‖ + Q := by
        rw [hchange]
        exact add_le_add (mul_le_mul_of_nonneg_left (le_abs_self _) hP0) le_rfl
      linarith [hval, hle]
    have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := fun x : ℝ => ∫ t in (0 : ℝ)..x, g t)
      (f' := g) (a := (0 : ℝ)) (b := b) (δ := (0 : ℝ)) (K := P) (ε := Q)
      hcont hderiv (by simp) hbound
    have hb' := hmain b ⟨hb0, le_rfl⟩
    rw [sub_zero] at hb'
    exact le_trans (le_abs_self _) hb'
  refine ⟨gronwallBound 0 P Q (Real.pi / 4), ?_, ?_⟩
  · have h := gronwallBound_mono (δ := (0 : ℝ)) (K := P) (ε := Q) le_rfl hQ0 hP0
      (show (0 : ℝ) ≤ Real.pi / 4 by linarith [Real.pi_pos])
    rw [gronwallBound_x0] at h
    exact h
  · intro θ hθ
    have hb : Real.pi / 4 - θ ∈ Set.Ico (0 : ℝ) (Real.pi / 4) :=
      ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    have h := hprim (Real.pi / 4 - θ) hb
    have hchange : (∫ t in (0 : ℝ)..(Real.pi / 4 - θ), g t) = GdL u θ := by
      have h2 := intervalIntegral.integral_comp_sub_left
        (f := fun s : ℝ => |LzeroGrowth.Rfun u s| * ew s) (a := (0 : ℝ))
        (b := Real.pi / 4 - θ) (Real.pi / 4)
      rw [hgdef]
      refine h2.trans ?_
      rw [GdL]
      congr 1 <;> ring
    rw [hchange] at h
    refine le_trans h ?_
    have hmono := gronwallBound_mono (δ := (0 : ℝ)) (K := P) (ε := Q) le_rfl hQ0 hP0
    exact hmono (show Real.pi / 4 - θ ≤ Real.pi / 4 by linarith [hθ.1])

theorem Rfun_left_const {u : ℝ → ℝ} {mu : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (heig : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ = mu * u θ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
      |LzeroGrowth.Rfun u θ|
        ≤ |LzeroGrowth.Rfun u (Real.pi / 4)| + B * Kl θ := by
  obtain ⟨C, hC, hbound⟩ := GdL_bound hu heig
  refine ⟨|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * C, by positivity, fun θ hθ => ?_⟩
  have h1 := Rfun_run_bound_left hu heig hθ
  have hKl : 0 ≤ Kl θ := Kl_nonneg hθ
  have hcoef : |LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ
      ≤ |LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * C := by
    have h := hbound θ hθ
    have h2m : (0 : ℝ) ≤ 2 * |mu| := by positivity
    linarith [mul_le_mul_of_nonneg_left h h2m]
  calc |LzeroGrowth.Rfun u θ|
      ≤ |LzeroGrowth.Rfun u (Real.pi / 4)|
          + (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * GdL u θ) * Kl θ := h1
    _ ≤ |LzeroGrowth.Rfun u (Real.pi / 4)|
          + (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * C) * Kl θ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef hKl)



/-! ## The right half -/

theorem Gd_bound {u : ℝ → ℝ} {mu : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (heig : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ = mu * u θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2), Gd u θ ≤ C := by
  set P : ℝ := 2 * |mu| * (Real.pi ^ 4 / 128) with hPdef
  set Q : ℝ := |LzeroGrowth.Rfun u (Real.pi / 4)|
    + |LzeroGrowth.Dfun u (Real.pi / 4)| * (Real.pi ^ 4 / 128) with hQdef
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQdef]; positivity
  have hmass : ∀ y ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      |LzeroGrowth.Rfun u y| * ew y ≤ P * Gd u y + Q := by
    intro y hy
    have hy2 : y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos, hy.1], hy.2⟩
    have hew0 : 0 ≤ ew y := ew_nonneg hy2
    have hR := Rfun_run_bound hu heig hy
    have h1 := mul_le_mul_of_nonneg_right hR hew0
    have hKiw : Ki y * ew y ≤ Real.pi ^ 4 / 128 := by
      rw [mul_comm]; exact ew_mul_Ki_le hy
    have hA1 : |LzeroGrowth.Rfun u (Real.pi / 4)| * ew y
        ≤ |LzeroGrowth.Rfun u (Real.pi / 4)| * 1 :=
      mul_le_mul_of_nonneg_left (ew_le_one y) (abs_nonneg _)
    have hD1 : |LzeroGrowth.Dfun u (Real.pi / 4)| * (Ki y * ew y)
        ≤ |LzeroGrowth.Dfun u (Real.pi / 4)| * (Real.pi ^ 4 / 128) :=
      mul_le_mul_of_nonneg_left hKiw (abs_nonneg _)
    have hG0 : 0 ≤ Gd u y := Gd_nonneg hu hy.1 hy.2
    have hP1 : 2 * |mu| * Gd u y * (Ki y * ew y) ≤ P * Gd u y := by
      have h := mul_le_mul_of_nonneg_left hKiw (by positivity : (0 : ℝ) ≤ 2 * |mu| * Gd u y)
      rw [hPdef]
      nlinarith [h]
    have hexp : (|LzeroGrowth.Rfun u (Real.pi / 4)|
          + (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u y) * Ki y) * ew y
        = |LzeroGrowth.Rfun u (Real.pi / 4)| * ew y
          + |LzeroGrowth.Dfun u (Real.pi / 4)| * (Ki y * ew y)
          + 2 * |mu| * Gd u y * (Ki y * ew y) := by ring
    have hsum : (|LzeroGrowth.Rfun u (Real.pi / 4)|
          + (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u y) * Ki y) * ew y
        ≤ P * Gd u y + Q := by
      rw [hexp, hQdef]
      linarith [hA1, hD1, hP1]
    linarith [h1, hsum]
  have hprim : ∀ T ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      Gd u T ≤ gronwallBound 0 P Q (T - Real.pi / 4) := by
    intro T hT
    have hle : (Real.pi / 4 : ℝ) ≤ T := hT.1.le
    set F : ℝ → ℝ := fun s => |LzeroGrowth.Rfun u s| * ew s with hFdef
    have hFat : ∀ y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ContinuousAt F y := by
      intro y hy
      have hR : ContinuousAt (LzeroGrowth.Rfun u) y := by
        have h1 : ContinuousAt u y :=
          (Work.FTS.EllipticEst.H2W.Lzero1Growth.hasDerivAt_u hu hy).continuousAt
        have h2 : ContinuousAt (fun s : ℝ => Real.sin (2 * s)) y := by fun_prop
        exact h1.div h2 (ne_of_gt (LzeroGrowth.sin_two_pos hy))
      rw [hFdef]
      exact (hR.abs).mul ew_continuous.continuousAt
    have hFcont : ContinuousOn F (Set.Icc (Real.pi / 4) T) := fun y hy =>
      (hFat y ⟨by linarith [Real.pi_pos, hy.1], lt_of_le_of_lt hy.2 hT.2⟩).continuousWithinAt
    have hFint : IntegrableOn F (Set.Icc (Real.pi / 4) T) := hFcont.integrableOn_Icc
    have hcontIoc : ContinuousOn (fun x : ℝ => ∫ t in Set.Ioc (Real.pi / 4) x, F t)
        (Set.Icc (Real.pi / 4) T) := intervalIntegral.continuousOn_primitive hFint
    have hcont : ContinuousOn (Gd u) (Set.Icc (Real.pi / 4) T) := by
      refine hcontIoc.congr (fun x hx => ?_)
      rw [Gd, hFdef]
      exact intervalIntegral.integral_of_le hx.1
    have hderiv : ∀ x ∈ Set.Ico (Real.pi / 4) T,
        HasDerivWithinAt (Gd u) (F x) (Set.Ici x) x := by
      intro x hx
      have hx2 : x ∈ Set.Ico (Real.pi / 4) (Real.pi / 2) := ⟨hx.1, lt_of_lt_of_le hx.2 hT.2.le⟩
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [Real.pi_pos, hx.1], hx2.2⟩
      have hint : IntervalIntegrable F volume (Real.pi / 4) x :=
        (hFcont.mono (fun y hy => ⟨hy.1, le_trans hy.2 hx.2.le⟩)).intervalIntegrable_of_Icc hx.1
      have hmeas : StronglyMeasurableAtFilter F (𝓝 x) volume :=
        ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo (0 : ℝ) (Real.pi / 2))
          isOpen_Ioo hFat x hx'
      exact (intervalIntegral.integral_hasDerivAt_right hint hmeas (hFat x hx')).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Ico (Real.pi / 4) T, ‖F x‖ ≤ P * ‖Gd u x‖ + Q := by
      intro x hx
      have hx2 : x ∈ Set.Ico (Real.pi / 4) (Real.pi / 2) := ⟨hx.1, lt_of_lt_of_le hx.2 hT.2.le⟩
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [Real.pi_pos, hx.1], hx2.2⟩
      have hFnn : 0 ≤ F x := by
        rw [hFdef]; exact mul_nonneg (abs_nonneg _) (ew_nonneg hx')
      have hval := hmass x hx2
      have hnorm : ‖F x‖ = |LzeroGrowth.Rfun u x| * ew x := by
        rw [hFdef, Real.norm_eq_abs, abs_of_nonneg hFnn]
      rw [hnorm]
      have hle2 : P * Gd u x + Q ≤ P * ‖Gd u x‖ + Q :=
        add_le_add (mul_le_mul_of_nonneg_left (le_abs_self _) hP0) le_rfl
      linarith [hval, hle2]
    have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := Gd u) (f' := F) (a := (Real.pi / 4 : ℝ)) (b := T) (δ := (0 : ℝ)) (K := P) (ε := Q)
      hcont hderiv (by simp only [Gd, intervalIntegral.integral_same, norm_zero, le_refl]) hbound
    have hT' := hmain T ⟨hle, le_rfl⟩
    have hGnn : 0 ≤ Gd u T := Gd_nonneg hu hT.1.le hT.2
    rw [Real.norm_eq_abs, abs_of_nonneg hGnn] at hT'
    exact hT'
  have hCnn : 0 ≤ gronwallBound 0 P Q (Real.pi / 4) := by
    have h := gronwallBound_mono (δ := (0 : ℝ)) (K := P) (ε := Q) le_rfl hQ0 hP0
      (show (0 : ℝ) ≤ Real.pi / 4 by linarith [Real.pi_pos])
    rw [gronwallBound_x0] at h
    exact h
  refine ⟨gronwallBound 0 P Q (Real.pi / 4), hCnn, fun θ hθ => ?_⟩
  rcases eq_or_lt_of_le hθ.1 with heq | hlt
  · rw [← heq]
    simp only [Gd, intervalIntegral.integral_same]
    exact hCnn
  · have h := hprim θ ⟨hlt, hθ.2⟩
    have hmono := gronwallBound_mono (δ := (0 : ℝ)) (K := P) (ε := Q) le_rfl hQ0 hP0
      (show θ - Real.pi / 4 ≤ Real.pi / 4 by linarith [hθ.2])
    exact le_trans h hmono

theorem Rfun_right_const {u : ℝ → ℝ} {mu : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (heig : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ = mu * u θ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      |LzeroGrowth.Rfun u θ|
        ≤ |LzeroGrowth.Rfun u (Real.pi / 4)| + B * Ki θ := by
  obtain ⟨C, hC, hbound⟩ := Gd_bound hu heig
  refine ⟨|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * C, by positivity, fun θ hθ => ?_⟩
  have h1 := Rfun_run_bound hu heig hθ
  have hKi : 0 ≤ Ki θ := Ki_nonneg hθ.1 hθ.2
  have hcoef : |LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ
      ≤ |LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * C := by
    have h := hbound θ hθ
    have h2m : (0 : ℝ) ≤ 2 * |mu| := by positivity
    linarith [mul_le_mul_of_nonneg_left h h2m]
  calc |LzeroGrowth.Rfun u θ|
      ≤ |LzeroGrowth.Rfun u (Real.pi / 4)|
          + (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ) * Ki θ := h1
    _ ≤ |LzeroGrowth.Rfun u (Real.pi / 4)|
          + (|LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * C) * Ki θ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef hKi)


end

end Work.FTS.EllipticEst.H2W.WeakPureAux
