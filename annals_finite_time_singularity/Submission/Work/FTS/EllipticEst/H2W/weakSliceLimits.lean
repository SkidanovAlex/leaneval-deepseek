import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.H2.ZibpLimit
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
import Submission.Work.FTS.EllipticEst.integrableAbsOfSqSeta
import Submission.Work.FTS.EllipticEst.SliceLocal.integrableOn_sinCos2_Lzero1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology

/-! # The endpoint behaviour of a weighted-`H²` angular slice

This module proves `Work.FTS.EllipticEst.H2W.weakSliceLimits`: a function `u` of class `C^n` on
`(0, π/2)` for every `n`, vanishing at both endpoints, whose second derivative satisfies

  `∫_{Iθ} (u'')² · sEta < ∞`,   `∫_{Iθ} (Lzero1 u)² · sEta < ∞`,   `sEta θ = sin(2θ)^{-η}`,

has a finite limit and a finite limit of `u'` at `0⁺`, tends to `0` at `(π/2)⁻`, and has a
(Lebesgue) integrable second derivative on `Iθ`.

The argument:
* the weight satisfies `sEta ≥ 1` on `(0, π/2)`, so the first hypothesis is at least as strong as
  `u'' ∈ L²(0, π/2) ⊂ L¹(0, π/2)`, and (by Newton–Leibniz) `u'`, `u` are bounded near every
  endpoint;
* the existence of the limits at `0⁺` is then exactly
  `exists_tendsto_nhdsGT_zero_of_integrableOn_deriv` applied to `u` and to `u'`;
* at the right endpoint we integrate the identity `(tan θ · u)' = Lzero1 u + u'' + 6u`
  (`Lzero1 u = -u'' + (tan θ · u)' - 6u`): the right-hand side is integrable on `(π/4, π/2)`, so
  `tan θ · u θ` has a finite limit at `(π/2)⁻`; since `u θ = (tan θ · u θ) · (cos θ / sin θ)` and
  `cos θ / sin θ → 0`, we get `u θ → 0`.
-/

/-- **Right endpoint limit of a function with integrable derivative.**  If `f` is differentiable
with derivative `f'` on the open interval `(a, b)` and `f'` is Lebesgue integrable there, then
`f` has a finite limit at `b` from the left.  (Mirror image of
`Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv`.) -/
theorem exists_tendsto_nhdsLT_of_integrableOn_deriv {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint : MeasureTheory.IntegrableOn f' (Set.Ioo a b)) :
    ∃ L : ℝ, Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds L) := by
  set c : ℝ := (a + b) / 2 with hcdef
  have hac : a < c := by rw [hcdef]; linarith
  have hcb : c < b := by rw [hcdef]; linarith
  have hIoo_cb : IntegrableOn f' (Set.Ioo c b) :=
    hint.mono_set (Set.Ioo_subset_Ioo_left hac.le)
  have hIcc : IntegrableOn f' (Set.Icc c b) volume :=
    hIoo_cb.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (a := c) (b := b)).symm
  have hcont_u : ContinuousOn (fun x => ∫ t in c..x, f' t) (Set.uIcc c b) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [Set.uIcc_of_le hcb.le]; exact hIcc)
  have hcont : ContinuousOn (fun x => ∫ t in c..x, f' t) (Set.Icc c b) := by
    rwa [Set.uIcc_of_le hcb.le] at hcont_u
  refine ⟨f c + ∫ t in c..b, f' t, ?_⟩
  have hg : Tendsto (fun x => f c + ∫ t in c..x, f' t) (nhdsWithin b (Set.Iio b))
      (nhds (f c + ∫ t in c..b, f' t)) := by
    have hcw : ContinuousWithinAt (fun x => ∫ t in c..x, f' t) (Set.Icc c b) b :=
      hcont.continuousWithinAt (Set.right_mem_Icc.mpr hcb.le)
    have hle : nhdsWithin b (Set.Iio b) ≤ nhdsWithin b (Set.Icc c b) := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hcb]
      exact nhdsWithin_mono b Set.Ioo_subset_Icc_self
    exact (hcw.mono_left hle).const_add (f c)
  refine hg.congr' ?_
  have hmem : Set.Ioo c b ∈ nhdsWithin b (Set.Iio b) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hcb]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with x hx
  have hcx : c ≤ x := hx.1.le
  have hFTC : ∫ t in c..x, f' t = f x - f c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hderiv y (by
        rw [Set.uIcc_of_le hcx] at hy
        exact ⟨lt_of_lt_of_le hac hy.1, lt_of_le_of_lt hy.2 hx.2⟩))
      ((show IntegrableOn f' (Set.uIcc c x) volume from by
          rw [Set.uIcc_of_le hcx]
          exact hIcc.mono_set (Set.Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable)
  linarith [hFTC]

/-- **Squeeze at the right endpoint.**  If `tan θ · u θ` has a finite limit at `(π/2)⁻`, then
`u θ → 0`: near `π/2` one has `u θ = (tan θ · u θ) · (cos θ / sin θ)` and `cos θ / sin θ → 0`. -/
theorem tendsto_zero_right_of_tan_mul_tendsto {u : ℝ → ℝ} {M : ℝ}
    (h : Filter.Tendsto (fun θ : ℝ => Real.tan θ * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds M)) :
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have h1 : Filter.Tendsto (fun θ : ℝ => Real.cos θ / Real.sin θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hc : ContinuousAt (fun θ : ℝ => Real.cos θ / Real.sin θ) (Real.pi / 2) :=
      Real.continuous_cos.continuousAt.div Real.continuous_sin.continuousAt
        (by simp [Real.sin_pi_div_two])
    have hle : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ nhds (Real.pi / 2) :=
      nhdsWithin_le_nhds
    have := hc.tendsto.mono_left hle
    simpa [Real.cos_pi_div_two, Real.sin_pi_div_two] using this
  have h2 : Filter.Tendsto (fun θ : ℝ => Real.tan θ * u θ * (Real.cos θ / Real.sin θ))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have := h.mul h1
    simpa using this
  refine h2.congr' ?_
  have hmem : Set.Ioo (Real.pi / 4) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT (a := Real.pi / 4) (b := Real.pi / 2)
      (by linarith [Real.pi_pos])]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with θ hθ
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hsin : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
      (by linarith [hθ.2, Real.pi_pos]))
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-- **Derivative of `θ ↦ tan θ · u θ` in the shape used by the right-endpoint integral.**  On the
open interval this derivative is `Lzero1 u + u'' + 6u` by the definition of `Lzero1`. -/
theorem hasDerivAt_tan_mul_Lzero1 {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => Real.tan t * u t)
      (Work.FTS.EllipticEst.Lzero1 u θ + deriv (fun t : ℝ => deriv u t) θ + 6 * u θ) θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hu2 : ContDiffAt ℝ 2 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hdiff : DifferentiableAt ℝ (fun t : ℝ => Real.tan t * u t) θ :=
    (Real.differentiableAt_tan.mpr hcos).mul (hu2.differentiableAt (by norm_num))
  have h := hdiff.hasDerivAt
  convert h using 1
  simp only [Work.FTS.EllipticEst.Lzero1]
  ring

/-- **Boundedness of `u` and of `u'` on the right half of the slice.**  On `(π/4, π/2)` both
`u` and `u'` are bounded, with an explicit constant obtained from Newton–Leibniz applied to
`u'` (whose derivative `u''` is integrable on the right half because `sEta ≥ 1` there). -/
theorem abs_deriv_and_abs_le_right {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 < C ∧ (∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), |deriv u θ| ≤ C)
      ∧ (∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), |u θ| ≤ C) := by
  have hU : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hq : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hsq : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (fun t => deriv u t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u h2
  have hD2abs : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t => deriv u t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq u hsq
  have hD2tailAbs : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t => deriv u t) θ|)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    hD2abs.mono_set (Set.Ioo_subset_Ioo_left hU.le)
  have hD2tail : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv (fun t => deriv u t) θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    rw [MeasureTheory.IntegrableOn]
    refine (MeasureTheory.integrable_norm_iff ?_).mp ?_
    · exact (measurable_deriv (fun t : ℝ => deriv u t)).aestronglyMeasurable
    · rw [MeasureTheory.IntegrableOn] at hD2tailAbs
      simpa [Real.norm_eq_abs] using hD2tailAbs
  have hderiv2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x := by
    intro x hx
    have h2' : ContDiffAt ℝ 2 u x := hu.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd1 : ContDiffAt ℝ 1 (deriv u) x := h2'.derivWithin (by norm_num)
    exact (hd1.differentiableAt (by norm_num)).hasDerivAt
  have hu1 : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
  have hderiv1 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (deriv u x) x := by
    intro x hx
    exact ((hu1.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hcd : ContinuousOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    fun x hx => (hderiv2 x hx).continuousAt.continuousWithinAt
  set K : ℝ := ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) θ| with hK
  have hKnn : 0 ≤ K := by
    rw [hK]; exact integral_nonneg fun _ => abs_nonneg _
  set M : ℝ := |deriv u (Real.pi / 4)| + K with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; linarith [abs_nonneg (deriv u (Real.pi / 4)), hKnn]
  -- bound on `u'` on the right half
  have hud : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), |deriv u θ| ≤ M := by
    intro θ hθ
    have hle : Real.pi / 4 ≤ θ := hθ.1.le
    have hFTC : ∫ s in (Real.pi / 4)..θ, deriv (fun t => deriv u t) s
        = deriv u θ - deriv u (Real.pi / 4) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
      · rw [Set.uIcc_of_le hle] at hx
        exact hderiv2 x ⟨lt_of_lt_of_le hU hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
        exact hD2tail.mono_set (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hθ.2⟩)
    have hb : |deriv u θ - deriv u (Real.pi / 4)| ≤ K := by
      have h1 : |∫ s in (Real.pi / 4)..θ, deriv (fun t => deriv u t) s|
          ≤ ∫ s in (Real.pi / 4)..θ, |deriv (fun t => deriv u t) s| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (μ := volume) hle
            (f := fun s => deriv (fun t => deriv u t) s)
      have h2' : ∫ s in (Real.pi / 4)..θ, |deriv (fun t => deriv u t) s| ≤ K := by
        rw [hK, intervalIntegral.integral_of_le hle]
        exact MeasureTheory.setIntegral_mono_set hD2abs
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (Filter.Eventually.of_forall fun x hx =>
            ⟨lt_trans hU hx.1, lt_of_le_of_lt hx.2 hθ.2⟩)
      rw [← hFTC]
      exact h1.trans h2'
    have htri : |deriv u θ| ≤ |deriv u (Real.pi / 4)| + |deriv u θ - deriv u (Real.pi / 4)| := by
      have := abs_add_le (deriv u (Real.pi / 4)) (deriv u θ - deriv u (Real.pi / 4))
      simpa using this
    rw [hMdef]; linarith [htri, hb]
  -- bound on `u` on the right half
  have huBd : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |u θ| ≤ |u (Real.pi / 4)| + M * (Real.pi / 2) := by
    intro θ hθ
    have hle : Real.pi / 4 ≤ θ := hθ.1.le
    have hFTC : ∫ s in (Real.pi / 4)..θ, deriv u s = u θ - u (Real.pi / 4) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
      · rw [Set.uIcc_of_le hle] at hx
        exact hderiv1 x ⟨lt_of_lt_of_le hU hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
      · have hsub : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
          rw [Set.uIcc_of_le hle]
          exact fun x hx => ⟨lt_of_lt_of_le hU hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
        exact (hcd.mono hsub).intervalIntegrable
    have h1 : |∫ s in (Real.pi / 4)..θ, deriv u s| ≤ M * (Real.pi / 2) := by
      have h2' : |∫ s in (Real.pi / 4)..θ, deriv u s| ≤ M * |θ - Real.pi / 4| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_of_norm_le_const (f := deriv u) (C := M)
            (a := Real.pi / 4) (b := θ) (fun s hs => by
              rw [Set.uIoc, Set.mem_Ioc, min_eq_left hθ.1.le, max_eq_right hθ.1.le] at hs
              rw [Real.norm_eq_abs]
              exact hud s ⟨hs.1, lt_of_le_of_lt hs.2 hθ.2⟩)
      have h3 : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
        rw [abs_of_pos (by linarith [hθ.1])]
        linarith [hθ.2, Real.pi_pos]
      exact h2'.trans (mul_le_mul_of_nonneg_left h3 hMnn)
    have htri : |u θ| ≤ |u (Real.pi / 4)| + |u θ - u (Real.pi / 4)| := by
      have := abs_add_le (u (Real.pi / 4)) (u θ - u (Real.pi / 4))
      simpa using this
    have h4 : |u θ - u (Real.pi / 4)| ≤ M * (Real.pi / 2) := by
      rw [← hFTC]; exact h1
    linarith [htri, h4]
  refine ⟨max 1 (|u (Real.pi / 4)| + M * (Real.pi / 2)),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_, ?_⟩
  · intro θ hθ
    have h1 : |deriv u θ| ≤ M := hud θ hθ
    have h3 : M ≤ M * (Real.pi / 2) := by nlinarith [hMnn, Real.pi_gt_three]
    have h2' : M ≤ |u (Real.pi / 4)| + M * (Real.pi / 2) := by
      linarith [h3, abs_nonneg (u (Real.pi / 4))]
    exact h1.trans (h2'.trans (le_max_right _ _))
  · intro θ hθ
    exact (huBd θ hθ).trans (le_max_right _ _)

theorem weakSliceLimits (u : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hA : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    (∃ U : ℝ, Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds U)) ∧
      (∃ L : ℝ, Filter.Tendsto (deriv u) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) ∧
      Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
      MeasureTheory.IntegrableOn (fun θ => deriv (fun t => deriv u t) θ) Work.Spaces.Iθ := by
  have hU : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hq : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := hu 2
  -- ## Differentiability of `u` and of `u'` on the open interval
  have hderiv2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x := by
    intro x hx
    have h2' : ContDiffAt ℝ 2 u x := hu2.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd1 : ContDiffAt ℝ 1 (deriv u) x := h2'.derivWithin (by norm_num)
    exact (hd1.differentiableAt (by norm_num)).hasDerivAt
  -- ## Integrability of `(u'')²`, of `|u''|` and of `u''` on `Iθ`
  have hsq : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (fun t => deriv u t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u h2
  have hD2absIoo : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t => deriv u t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq u hsq
  have hD2abs : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t => deriv u t) θ|)
      Work.Spaces.Iθ :=
    hD2absIoo.congr_set_ae
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  have hD2mem : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => deriv (fun t => deriv u t) θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (measurable_deriv (fun t : ℝ => deriv u t)).aestronglyMeasurable
  have hD2int : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv (fun t => deriv u t) θ)
      Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn]
    refine (MeasureTheory.integrable_norm_iff hD2mem).mp ?_
    rw [MeasureTheory.IntegrableOn] at hD2abs
    simpa [Real.norm_eq_abs] using hD2abs
  refine ⟨?_, ?_, ?_, hD2int⟩
  · -- ## The limit of `u` at `0⁺`
    exact Work.FTS.EllipticEst.sliceLimitLeftExists u hu h2
  · -- ## The limit of `u'` at `0⁺`
    refine Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
      (f := deriv u) (f' := fun θ : ℝ => deriv (fun t => deriv u t) θ) hU ?_ ?_
    · intro x hx
      exact hderiv2 x ⟨hx.1, by linarith [hx.2]⟩
    · exact hD2int.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt (by linarith [hx.2])⟩)
  · -- ## The limit of `u` at `(π/2)⁻`
    obtain ⟨C, hC0, -, hCb⟩ := abs_deriv_and_abs_le_right hu2 h2
    have hcontL : ContinuousOn (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.SliceLocal.continuousOn_Lzero1_of_contDiffOn_two u hu2
    have hLabs : MeasureTheory.IntegrableOn (fun θ : ℝ => |Work.FTS.EllipticEst.Lzero1 u θ|)
        Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.integrableAbsOfSqSeta hcontL hA
    have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ := fun x hx =>
      ⟨le_of_lt (lt_trans hU hx.1), le_of_lt hx.2⟩
    -- integrability of the three summands on the right tail
    have hLtail : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 u θ)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
      rw [MeasureTheory.IntegrableOn]
      refine (MeasureTheory.integrable_norm_iff ?_).mp ?_
      · exact (hcontL.mono (Set.Ioo_subset_Ioo_left hU.le)).aestronglyMeasurable
          measurableSet_Ioo
      · have h := hLabs.mono_set hsub
        rw [MeasureTheory.IntegrableOn] at h
        simpa [Real.norm_eq_abs] using h
    have hD2tail : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv (fun t => deriv u t) θ)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hD2int.mono_set hsub
    have hutail : MeasureTheory.IntegrableOn u (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
      refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ C ?_
      · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
      · exact (hu2.continuousOn.mono (Set.Ioo_subset_Ioo_left hU.le)).aestronglyMeasurable
          measurableSet_Ioo
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => ?_)
        rw [Real.norm_eq_abs]
        exact hCb x hx
    have hsumtail : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 u θ + deriv (fun t => deriv u t) θ + 6 * u θ)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      (hLtail.add hD2tail).add (hutail.const_mul 6)
    -- integrate `(tan θ · u)'` on the right tail and squeeze
    obtain ⟨M, hM⟩ := exists_tendsto_nhdsLT_of_integrableOn_deriv hq
      (fun x hx => hasDerivAt_tan_mul_Lzero1 hu2 ⟨lt_trans hU hx.1, hx.2⟩) hsumtail
    exact tendsto_zero_right_of_tan_mul_tendsto hM

end Work.FTS.EllipticEst.H2W
