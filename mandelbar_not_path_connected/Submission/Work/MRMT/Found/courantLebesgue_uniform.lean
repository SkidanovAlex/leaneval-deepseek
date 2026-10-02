import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.exists_fderiv_ne_zero_in_ball
import Submission.Work.MRMT.Found.dzSq_integral_le_area
import Submission.Work.MRMT.Found.exists_radius_sq_shell_le
import Submission.Work.MRMT.Found.argChange_boundedComponent
import Submission.Work.MRMT.Found.hasArgChange_of_homotopy
import Submission.Work.MRMT.Found.exists_linRep_of_det_pos
import Submission.Work.MRMT.Found.hasArgChange_one_of_det_pos
import Submission.Work.MRMT.Found.dist_le_of_frontier_subset
import Submission.Work.MRMT.Found.sq_integral_le_integral_sq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A uniform Courant--Lebesgue estimate for injective `C¹` plane maps with bounded dilatation

For every `0 ≤ k < 1` there is a constant `c > 0`, depending on `k` alone (in particular *not* on
the map), such that for every injective `C¹` map `F : ℂ → ℂ` whose complex dilatation is bounded
by `k` pointwise, and all `z₀, z` with `‖z - z₀‖ ≤ 1/4`,

`‖F z - F z₀‖² ≤ c · volume (F '' ball z₀ 1) / log (1/‖z - z₀‖)`.

The constant is explicit: `c = 5 (1+k)² 2π/(1-k²)`.

This is the classical Courant--Lebesgue argument for quasiconformal maps in the elementary form
needed by the mandelbar project:

* pick `c ∈ B(z₀, δ/2)` with `fderiv ℝ F c ≠ 0` (exists by injectivity), so that `∂F c ≠ 0`
  and the Jacobian at `c` is positive;
* the shell lemma gives a radius `r ∈ (3δ/2, 1/2)` for which the `∂`-energy on the circle of
  radius `r` around `c` is bounded by (a constant times) the `∂`-energy over `B(c,1/2)` divided by
  `log (R/a)`;
* that energy is controlled by the area of `F '' B(z₀,1)` via the change-of-variables formula and
  the pointwise distortion inequality;
* the loop `t ↦ F (c + r e^{2πit}) - F c` has argument change `1` (linearisation at `c`, using
  orientation preservation), hence bounds a bounded component `D` of its complement containing both
  `F z - F c` and `F z₀ - F c`; any two points of `D` are at distance at most the maximal distance
  between two points of the loop, `(1+k) 2π r ∫₀¹ ‖∂F‖`;
* finally `log (1/‖z-z₀‖) ≤ 5 log (R/a)` for `‖z-z₀‖ ≤ 1/4`, which converts the `log (R/a)`
  denominator into `log (1/‖z-z₀‖)`.

The helper material (the loop parametrisation) lives in the namespace
`Work.MRMT.Found.CourantLebesgue` so that it does not clash with the parallel development of the
non-uniform version of the statement; the local linearisation/argument-change lemma is imported
from `Submission.Work.MRMT.Found.hasArgChange_one_of_det_pos`.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Complex Function
open scoped Topology ENNReal

set_option maxHeartbeats 1000000

namespace Work.MRMT.Found

namespace CourantLebesgue

/-! ## The real Fréchet derivative in Wirtinger form -/

/-- For any `f : ℂ → ℂ` and `z w : ℂ`, the real Fréchet derivative applied to `w` is
`∂f(z) * w + ∂̄f(z) * conj w`. -/
theorem fderiv_apply_eq (f : ℂ → ℂ) (z w : ℂ) :
    (fderiv ℝ f z) w = dz f z * w + dzbar f z * star w := by
  simpa only [dz, dzbar] using Work.MRMT.Wirtinger.realLinearMap_apply_eq (fderiv ℝ f z) w

/-- If `‖∂̄f(z)‖ ≤ k ‖∂f(z)‖` with `k ≥ 0`, then `‖Df(z) w‖ ≤ (1+k) ‖∂f(z)‖ ‖w‖`. -/
theorem norm_fderiv_apply_le {f : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hdil : ∀ z : ℂ, ‖dzbar f z‖ ≤ k * ‖dz f z‖) (z w : ℂ) :
    ‖(fderiv ℝ f z) w‖ ≤ (1 + k) * ‖dz f z‖ * ‖w‖ := by
  rw [fderiv_apply_eq]
  calc ‖dz f z * w + dzbar f z * star w‖
      ≤ ‖dz f z * w‖ + ‖dzbar f z * star w‖ := norm_add_le _ _
    _ = ‖dz f z‖ * ‖w‖ + ‖dzbar f z‖ * ‖w‖ := by rw [norm_mul, norm_mul, norm_star]
    _ ≤ ‖dz f z‖ * ‖w‖ + (k * ‖dz f z‖) * ‖w‖ := by
        have hb := mul_le_mul_of_nonneg_right (hdil z) (norm_nonneg w)
        linarith
    _ = (1 + k) * ‖dz f z‖ * ‖w‖ := by ring

/-- `∂f` is continuous when `f` is `C¹`. -/
theorem continuous_dz (f : ℂ → ℂ) (hc : ContDiff ℝ 1 f) : Continuous (dz f) := by
  have hd : Continuous (fderiv ℝ f) := hc.continuous_fderiv (by norm_num)
  unfold dz
  exact ((hd.clm_apply continuous_const).sub
    (continuous_const.mul (hd.clm_apply continuous_const))).div_const 2

/-- `∂̄f` is continuous when `f` is `C¹`. -/
theorem continuous_dzbar_one (f : ℂ → ℂ) (hc : ContDiff ℝ 1 f) : Continuous (dzbar f) := by
  have hd : Continuous (fderiv ℝ f) := hc.continuous_fderiv (by norm_num)
  unfold dzbar
  exact ((hd.clm_apply continuous_const).add
    (continuous_const.mul (hd.clm_apply continuous_const))).div_const 2

/-! ## The circle loop and its length -/

def circLoopC (c : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  c + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

/-- The same circle, with the casts pushed inward. -/
lemma circLoopC_eq (c : ℂ) (r t : ℝ) :
    circLoopC c r t = c + r * Complex.exp (2 * Real.pi * t * Complex.I) := by
  rw [circLoopC]; push_cast; ring

/-- The derivative of `circLoopC`. -/
def circLoopD (r : ℝ) (t : ℝ) : ℂ :=
  (r : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

theorem continuous_circLoopC (c : ℂ) (r : ℝ) : Continuous (circLoopC c r) := by
  unfold circLoopC; fun_prop

theorem circLoopC_zero (c : ℂ) (r : ℝ) : circLoopC c r 0 = c + (r : ℂ) := by
  simp [circLoopC]

theorem circLoopC_one (c : ℂ) (r : ℝ) : circLoopC c r 1 = c + (r : ℂ) := by
  unfold circLoopC
  rw [show (((2 * Real.pi * 1 : ℝ) : ℂ) * Complex.I) = 2 * (Real.pi : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_two_pi_mul_I, mul_one]

theorem circLoopC_add_int (c : ℂ) (r : ℝ) (n : ℤ) (t : ℝ) :
    circLoopC c r (t + n) = circLoopC c r t := by
  unfold circLoopC
  have hexp : Complex.exp (((2 * Real.pi * (t + ↑n) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    rw [show (((2 * Real.pi * (t + ↑n) : ℝ) : ℂ) * Complex.I)
        = (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast; ring]
    rw [Complex.exp_add, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, mul_one]
  rw [hexp]

theorem circLoopC_fract (c : ℂ) (r : ℝ) (t : ℝ) :
    circLoopC c r t = circLoopC c r (Int.fract t) := by
  have h : t = Int.fract t + (⌊t⌋ : ℝ) := (Int.fract_add_floor t).symm
  conv_lhs => rw [h]
  rw [circLoopC_add_int]

theorem hasDerivAt_circLoopC (c : ℂ) (r t : ℝ) : HasDerivAt (circLoopC c r) (circLoopD r t) t := by
  unfold circLoopC circLoopD
  have h2 : HasDerivAt (fun s : ℝ => (2 * Real.pi * s : ℝ)) (2 * Real.pi) t :=
    hasDerivAt_const_mul (2 * Real.pi)
  have h1 : HasDerivAt (fun s : ℝ => ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) t := h2.ofReal_comp.mul_const Complex.I
  have h3 := h1.cexp
  have h4 := h3.const_mul (r : ℂ)
  have h5 := h4.const_add c
  convert h5 using 1
  ring

theorem norm_circLoopD (r t : ℝ) (hr : 0 ≤ r) : ‖circLoopD r t‖ = 2 * Real.pi * r := by
  unfold circLoopD
  have hexp : ‖Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    have : (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I).re = 0 := by simp [Complex.mul_re]
    rw [this, Real.exp_zero]
  rw [norm_mul, norm_mul, norm_mul, hexp, mul_one, Complex.norm_I, mul_one, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hr, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  ring


/-- The image under `F` of the circle of radius `r` around `c`, translated so that `t = 0`
maps to `0`. -/
def loopF (F : ℂ → ℂ) (c : ℂ) (r : ℝ) (t : ℝ) : ℂ := F (circLoopC c r t) - F c

variable {F : ℂ → ℂ} {k : ℝ}

theorem loopF_add_int (F : ℂ → ℂ) (c : ℂ) (r : ℝ) (n : ℤ) (t : ℝ) :
    loopF F c r (t + n) = loopF F c r t := by
  unfold loopF; rw [circLoopC_add_int]

theorem loopF_fract (F : ℂ → ℂ) (c : ℂ) (r : ℝ) (t : ℝ) :
    loopF F c r t = loopF F c r (Int.fract t) := by
  unfold loopF; rw [circLoopC_fract]

theorem loopF_zero (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : loopF F c r 0 = F (c + (r : ℂ)) - F c := by
  simp [loopF, circLoopC_zero]

theorem loopF_one (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : loopF F c r 1 = F (c + (r : ℂ)) - F c := by
  simp [loopF, circLoopC_one]

theorem loopF_loop (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : loopF F c r 1 = loopF F c r 0 := by
  rw [loopF_one, loopF_zero]

theorem continuous_loopF (hF : ContDiff ℝ 1 F) (c : ℂ) (r : ℝ) : Continuous (loopF F c r) :=
  (hF.continuous.comp (continuous_circLoopC c r)).sub continuous_const

theorem hasDerivAt_loopF (hF : ContDiff ℝ 1 F) (c : ℂ) (r t : ℝ) :
    HasDerivAt (loopF F c r) ((fderiv ℝ F (circLoopC c r t)) (circLoopD r t)) t := by
  have h1 := hasDerivAt_circLoopC c r t
  have h2 : HasFDerivAt F (fderiv ℝ F (circLoopC c r t)) (circLoopC c r t) :=
    (hF.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
  exact (h2.comp_hasDerivAt t h1).sub_const (F c)

theorem continuous_derivLoopF (hF : ContDiff ℝ 1 F) (c : ℂ) (r : ℝ) :
    Continuous (fun t : ℝ => (fderiv ℝ F (circLoopC c r t)) (circLoopD r t)) := by
  have hd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hD : Continuous (circLoopD r) := by unfold circLoopD; fun_prop
  exact Continuous.clm_apply (hd.comp (continuous_circLoopC c r)) hD

theorem norm_deriv_loopF_le {F : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hdil : ∀ z : ℂ, ‖dzbar F z‖ ≤ k * ‖dz F z‖)
    (c : ℂ) (r t : ℝ) (hr : 0 ≤ r) :
    ‖(fderiv ℝ F (circLoopC c r t)) (circLoopD r t)‖
      ≤ (1 + k) * (2 * Real.pi * r) * ‖dz F (circLoopC c r t)‖ := by
  have h := norm_fderiv_apply_le hk hdil (circLoopC c r t) (circLoopD r t)
  rw [norm_circLoopD r t hr] at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

theorem norm_loopF_sub_le {F : ℂ → ℂ} {k : ℝ} (hF : ContDiff ℝ 1 F) (hk : 0 ≤ k)
    (hdil : ∀ z : ℂ, ‖dzbar F z‖ ≤ k * ‖dz F z‖) (c : ℂ) {r : ℝ} (hr : 0 < r)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖loopF F c r s - loopF F c r t‖
      ≤ (1 + k) * (2 * Real.pi * r) * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖) := by
  have hderiv : ∀ u ∈ Set.uIcc s t,
      HasDerivAt (loopF F c r) ((fderiv ℝ F (circLoopC c r u)) (circLoopD r u)) u :=
    fun u _ => hasDerivAt_loopF hF c r u
  have hcdz : Continuous (fun u : ℝ => ‖dz F (circLoopC c r u)‖) :=
    ((continuous_dz F hF).comp (continuous_circLoopC c r)).norm
  have hcd2 : Continuous
      (fun u : ℝ => (1 + k) * (2 * Real.pi * r) * ‖dz F (circLoopC c r u)‖) :=
    hcdz.const_mul ((1 + k) * (2 * Real.pi * r))
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun u : ℝ => (fderiv ℝ F (circLoopC c r u)) (circLoopD r u)) volume a b :=
    fun a b => (continuous_derivLoopF hF c r).intervalIntegrable a b
  have hnn : ∀ u : ℝ, 0 ≤ (1 + k) * (2 * Real.pi * r) * ‖dz F (circLoopC c r u)‖ :=
    fun u => mul_nonneg (mul_nonneg (by linarith) (by positivity)) (norm_nonneg _)
  have hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      (∫ u in a..b, (1 + k) * (2 * Real.pi * r) * ‖dz F (circLoopC c r u)‖)
        ≤ ∫ u in (0 : ℝ)..1, (1 + k) * (2 * Real.pi * r) * ‖dz F (circLoopC c r u)‖ := by
    intro a b ha hab hb1
    refine intervalIntegral.integral_mono_interval ha hab hb1 ?_ ?_
    · filter_upwards with x; exact hnn x
    · exact hcd2.intervalIntegrable 0 1
  rcases le_total s t with hst | hts
  · have hftc : ∫ u in s..t, (fun u : ℝ => (fderiv ℝ F (circLoopC c r u)) (circLoopD r u)) u
        = loopF F c r t - loopF F c r s :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint s t)
    have h1 : ‖loopF F c r s - loopF F c r t‖
        ≤ ∫ u in s..t, ‖(fderiv ℝ F (circLoopC c r u)) (circLoopD r u)‖ := by
      have h2 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
        (f := fun u : ℝ => (fderiv ℝ F (circLoopC c r u)) (circLoopD r u)) hst
      rw [hftc, norm_sub_rev] at h2
      simpa using h2
    calc ‖loopF F c r s - loopF F c r t‖
        ≤ ∫ u in s..t, ‖(fderiv ℝ F (circLoopC c r u)) (circLoopD r u)‖ := h1
      _ ≤ ∫ u in s..t, (1 + k) * (2 * Real.pi * r) * ‖dz F (circLoopC c r u)‖ := by
          refine intervalIntegral.integral_mono_on hst ?_ ?_ (fun u _ => ?_)
          · exact (continuous_derivLoopF hF c r).norm.intervalIntegrable s t
          · exact hcd2.intervalIntegrable s t
          · exact norm_deriv_loopF_le hk hdil c r u hr.le
      _ ≤ ∫ u in (0 : ℝ)..1, (1 + k) * (2 * Real.pi * r) * ‖dz F (circLoopC c r u)‖ :=
          hmono s t hs.1 hst ht.2
      _ = (1 + k) * (2 * Real.pi * r) * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖) :=
          intervalIntegral.integral_const_mul _ _
  · have hftc : ∫ u in t..s, (fun u : ℝ => (fderiv ℝ F (circLoopC c r u)) (circLoopD r u)) u
        = loopF F c r s - loopF F c r t :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u hu => hderiv u (Set.uIcc_comm t s ▸ hu)) (hint t s)
    have h1 : ‖loopF F c r s - loopF F c r t‖
        ≤ ∫ u in t..s, ‖(fderiv ℝ F (circLoopC c r u)) (circLoopD r u)‖ := by
      have h2 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
        (f := fun u : ℝ => (fderiv ℝ F (circLoopC c r u)) (circLoopD r u)) hts
      rw [hftc] at h2
      simpa using h2
    calc ‖loopF F c r s - loopF F c r t‖
        ≤ ∫ u in t..s, ‖(fderiv ℝ F (circLoopC c r u)) (circLoopD r u)‖ := h1
      _ ≤ ∫ u in t..s, (1 + k) * (2 * Real.pi * r) * ‖dz F (circLoopC c r u)‖ := by
          refine intervalIntegral.integral_mono_on hts ?_ ?_ (fun u _ => ?_)
          · exact (continuous_derivLoopF hF c r).norm.intervalIntegrable t s
          · exact hcd2.intervalIntegrable t s
          · exact norm_deriv_loopF_le hk hdil c r u hr.le
      _ ≤ ∫ u in (0 : ℝ)..1, (1 + k) * (2 * Real.pi * r) * ‖dz F (circLoopC c r u)‖ :=
          hmono t s ht.1 hts hs.2
      _ = (1 + k) * (2 * Real.pi * r) * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖) :=
          intervalIntegral.integral_const_mul _ _

theorem norm_loopF_sub_le_all {F : ℂ → ℂ} {k : ℝ} (hF : ContDiff ℝ 1 F) (hk : 0 ≤ k)
    (hdil : ∀ z : ℂ, ‖dzbar F z‖ ≤ k * ‖dz F z‖) (c : ℂ) {r : ℝ} (hr : 0 < r) (s t : ℝ) :
    ‖loopF F c r s - loopF F c r t‖
      ≤ (1 + k) * (2 * Real.pi * r) * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖) := by
  rw [loopF_fract F c r s, loopF_fract F c r t]
  exact norm_loopF_sub_le hF hk hdil c hr
    ⟨Int.fract_nonneg s, le_of_lt (Int.fract_lt_one s)⟩
    ⟨Int.fract_nonneg t, le_of_lt (Int.fract_lt_one t)⟩



theorem det_pos_of_fderiv_ne_zero {F : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hdil : ∀ z : ℂ, ‖dzbar F z‖ ≤ k * ‖dz F z‖) {c : ℂ} (hc : fderiv ℝ F c ≠ 0) :
    0 < (fderiv ℝ F c).det := by
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith
  have hdet := Work.MRMT.Sobolev.det_fderiv_eq F c
  have hsq : ‖dzbar F c‖ ^ 2 ≤ k ^ 2 * ‖dz F c‖ ^ 2 := by
    have h := mul_self_le_mul_self (norm_nonneg (dzbar F c)) (hdil c)
    rw [← sq, ← sq] at h
    calc ‖dzbar F c‖ ^ 2 ≤ (k * ‖dz F c‖) ^ 2 := h
      _ = k ^ 2 * ‖dz F c‖ ^ 2 := by ring
  have hge : (1 - k ^ 2) * ‖dz F c‖ ^ 2 ≤ (fderiv ℝ F c).det := by
    rw [hdet]; nlinarith
  have hnn : 0 ≤ (fderiv ℝ F c).det := le_trans (mul_nonneg hk2.le (sq_nonneg _)) hge
  refine lt_of_le_of_ne hnn (Ne.symm ?_)
  intro h0
  have hdz : dz F c = 0 := by
    have h1 : ‖dz F c‖ ^ 2 = 0 := by nlinarith [hge, h0, hk2]
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1)
  have hdzb : dzbar F c = 0 := by
    have h1 : ‖dzbar F c‖ ≤ 0 := by
      simpa [hdz] using hdil c
    exact norm_eq_zero.mp (le_antisymm h1 (norm_nonneg _))
  exact hc (by ext w; rw [fderiv_apply_eq, hdz, hdzb]; simp)


end CourantLebesgue

open CourantLebesgue

theorem courantLebesgue_uniform (k : ℝ) (hk : 0 ≤ k) (hk1 : k < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ {F : ℂ → ℂ}, ContDiff ℝ 1 F → Function.Injective F →
      (∀ z : ℂ, ‖Work.MRMT.dzbar F z‖ ≤ k * ‖Work.MRMT.dz F z‖) →
      ∀ z₀ z : ℂ, ‖z - z₀‖ ≤ 1 / 4 →
        ‖F z - F z₀‖ ^ 2 ≤
          c * ((MeasureTheory.volume : MeasureTheory.Measure ℂ) (F '' Metric.ball z₀ 1)).toReal /
            Real.log (1 / ‖z - z₀‖) := by
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith
  refine ⟨5 * (1 + k) ^ 2 * (2 * Real.pi) / (1 - k ^ 2), div_pos (by positivity) hk2, ?_⟩
  intro F hF hinj hdil z₀ z hδ
  by_cases hzz : z = z₀
  · subst hzz; simp
  set δ := ‖z - z₀‖ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
  have hδle : δ ≤ 1 / 4 := by rw [hδdef]; exact hδ
  obtain ⟨c, hcball, hcderiv⟩ :=
    exists_fderiv_ne_zero_in_ball hF hinj z₀ (by positivity : (0 : ℝ) < δ / 2)
  have hcdist : ‖c - z₀‖ < δ / 2 := by
    rw [Metric.mem_ball, dist_eq_norm] at hcball; exact hcball
  have hdet : 0 < (fderiv ℝ F c).det := det_pos_of_fderiv_ne_zero hk hk1 hdil hcderiv
  set R : ℝ := 1 / 2 with hRdef
  set a : ℝ := 3 * δ / 2 with hadef
  have ha : 0 < a := by rw [hadef]; positivity
  have haR : a < R := by rw [hadef, hRdef]; linarith
  have hlogR : 0 < Real.log (R / a) := by
    apply Real.log_pos
    rw [one_lt_div (by positivity), hRdef, hadef]
    linarith
  obtain ⟨r, hr, hshell⟩ := exists_radius_sq_shell_le (f := fun w : ℂ => ‖dz F (c + w)‖ ^ 2)
    (((continuous_dz F hF).comp (continuous_const.add continuous_id)).norm.pow 2)
    (fun w => sq_nonneg _) ha haR
  have hrpos : 0 < r := lt_trans ha hr.1
  set A := ((MeasureTheory.volume : MeasureTheory.Measure ℂ) (F '' Metric.ball z₀ 1)).toReal with hAdef
  -- ### The integral of `‖∂F‖²` over the ball `B(c,R)`.
  have hball : (∫ w in Metric.ball (0 : ℂ) R, ‖dz F (c + w)‖ ^ 2)
      ≤ (1 - k ^ 2)⁻¹ * A := by
    have htrans : (∫ w in Metric.ball (0 : ℂ) R, ‖dz F (c + w)‖ ^ 2)
        = ∫ y in Metric.ball c R, ‖dz F y‖ ^ 2 := by
      have hmp : MeasureTheory.MeasurePreserving (fun w : ℂ => w + c) volume volume :=
        measurePreserving_add_right volume c
      have hind : ∀ w : ℂ, (Metric.ball c R).indicator (fun y => ‖dz F y‖ ^ 2) (w + c)
          = (Metric.ball (0 : ℂ) R).indicator (fun w => ‖dz F (c + w)‖ ^ 2) w := by
        intro w
        by_cases hw : w ∈ Metric.ball (0 : ℂ) R
        · have hw' : w + c ∈ Metric.ball c R := by
            simpa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right] using hw
          simp only [Set.indicator_of_mem hw, Set.indicator_of_mem hw']
          rw [add_comm]
        · have hw' : w + c ∉ Metric.ball c R := by
            intro h; exact hw (by simpa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right] using h)
          simp only [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw']
      calc (∫ w in Metric.ball (0 : ℂ) R, ‖dz F (c + w)‖ ^ 2)
          = ∫ w, (Metric.ball (0 : ℂ) R).indicator (fun w => ‖dz F (c + w)‖ ^ 2) w :=
            (MeasureTheory.integral_indicator measurableSet_ball).symm
        _ = ∫ w, (Metric.ball c R).indicator (fun y => ‖dz F y‖ ^ 2) (w + c) := by
            refine integral_congr_ae ?_; filter_upwards with w; rw [hind]
        _ = ∫ y, (Metric.ball c R).indicator (fun y => ‖dz F y‖ ^ 2) y :=
            hmp.integral_comp (Homeomorph.addRight c).measurableEmbedding _
        _ = ∫ y in Metric.ball c R, ‖dz F y‖ ^ 2 := MeasureTheory.integral_indicator measurableSet_ball
    rw [htrans]
    have hfin : (MeasureTheory.volume : MeasureTheory.Measure ℂ) (F '' Metric.ball z₀ 1) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono (Set.image_mono Metric.ball_subset_closedBall))
        ((isCompact_closedBall z₀ 1).image hF.continuous).measure_lt_top)
    refine (dzSq_integral_le_area hk hk1 hF hinj hdil c (by rw [hRdef]; norm_num)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hk2.le)
    refine ENNReal.toReal_mono hfin (measure_mono ?_)
    rintro y ⟨w, hw, rfl⟩
    refine ⟨w, ?_, rfl⟩
    have h2 : dist c z₀ < δ / 2 := by simpa [dist_eq_norm] using hcdist
    have h4 : dist w z₀ < R + δ / 2 := lt_of_le_of_lt (dist_triangle w c z₀) (add_lt_add hw h2)
    simp only [Metric.mem_ball]
    rw [hRdef] at h4
    linarith [hδle]
  -- ### The shell bound at the good radius `r`.
  have hTeq : (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖ ^ 2)
      = ∫ t in (0 : ℝ)..1, ‖dz F (c + r * Complex.exp (2 * Real.pi * t * Complex.I))‖ ^ 2 := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have hc : circLoopC c r t = c + r * Complex.exp (2 * Real.pi * t * Complex.I) := by
      rw [circLoopC]; push_cast; ring
    rw [hc]
  have hr2T : (2 * Real.pi * r) ^ 2 * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖ ^ 2)
      ≤ (2 * Real.pi) ^ 2 * ((1 / (2 * Real.pi)) * ((1 - k ^ 2)⁻¹ * A)) / Real.log (R / a) := by
    have hshell' : r ^ 2 * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖ ^ 2)
        ≤ (1 / (2 * Real.pi)) * (∫ w in Metric.ball (0 : ℂ) R, ‖dz F (c + w)‖ ^ 2) / Real.log (R / a) := by
      rw [le_div_iff₀ hlogR]
      have h := hshell
      rw [← hTeq] at h
      calc r ^ 2 * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖ ^ 2) * Real.log (R / a)
          = Real.log (R / a) * (r ^ 2 * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖ ^ 2)) := by ring
        _ ≤ (1 / (2 * Real.pi)) * (∫ w in Metric.ball (0 : ℂ) R, ‖dz F (c + w)‖ ^ 2) := h
    have h2 : r ^ 2 * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖ ^ 2)
        ≤ (1 / (2 * Real.pi)) * ((1 - k ^ 2)⁻¹ * A) / Real.log (R / a) := by
      refine hshell'.trans ?_
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hball (by positivity)) hlogR.le
    calc (2 * Real.pi * r) ^ 2 * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖ ^ 2)
        = (2 * Real.pi) ^ 2 * (r ^ 2 * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖ ^ 2)) := by ring
      _ ≤ (2 * Real.pi) ^ 2 * ((1 / (2 * Real.pi)) * ((1 - k ^ 2)⁻¹ * A) / Real.log (R / a)) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = (2 * Real.pi) ^ 2 * ((1 / (2 * Real.pi)) * ((1 - k ^ 2)⁻¹ * A)) / Real.log (R / a) := by ring
  -- ### The image loop and the separation of `F z` and `F z₀`.
  set γ : ℝ → ℂ := fun t => F (circLoopC c r t) - F c with hγdef
  have hγcont : Continuous γ := by rw [hγdef]; exact continuous_loopF hF c r
  have hγloop : γ 1 = γ 0 := by rw [hγdef]; exact loopF_loop F c r
  have hnormC : ∀ t : ℝ, ‖circLoopC c r t - c‖ = r := by
    intro t
    rw [circLoopC, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hrpos.le]
    have hz : (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I).re = 0 := by simp [Complex.mul_re]
    rw [Complex.norm_exp, hz, Real.exp_zero, mul_one]
  have hγne : ∀ t, γ t ≠ 0 := by
    intro t ht
    have h1 : F (circLoopC c r t) = F c := by rw [hγdef] at ht; simpa using sub_eq_zero.mp ht
    have h2 : circLoopC c r t = c := hinj h1
    have h3 : ‖circLoopC c r t - c‖ = 0 := by rw [h2, sub_self, norm_zero]
    rw [hnormC t] at h3
    linarith
  have hac : Work.MRMT.QC.HasArgChange γ 1 := by
    rw [hγdef]
    exact (by
      simpa only [circLoopC_eq] using
        hasArgChange_one_of_det_pos (F := F) hF hinj hdet (ρ := r) hrpos)
  obtain ⟨D, hDopen, hDbdd, hDfront, hD0, hDmax⟩ :=
    argChange_boundedComponent hγcont hγloop hγne (by norm_num) hac
  have hmem : ∀ y : ℂ, ‖y - c‖ < r → F y - F c ∈ D := by
    intro y hy
    have hcont : ContinuousOn (fun ρ : ℝ => F (c + (ρ : ℂ) * (y - c)) - F c) (Set.Icc (0 : ℝ) 1) :=
      (((hF.continuous.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).sub
        continuous_const)).continuousOn
    have hsub : Set.image (fun ρ : ℝ => F (c + (ρ : ℂ) * (y - c)) - F c) (Set.Icc (0 : ℝ) 1)
        ⊆ (Set.range γ)ᶜ := by
      rintro w ⟨ρ, hρ, rfl⟩ hw
      rw [hγdef, Set.mem_range] at hw
      obtain ⟨t, ht⟩ := hw
      have h1 : F (c + (ρ : ℂ) * (y - c)) = F (circLoopC c r t) := by
        have ht' : F (c + (ρ : ℂ) * (y - c)) - F c = F (circLoopC c r t) - F c := ht.symm
        exact sub_left_inj.mp ht'
      have h2 : c + (ρ : ℂ) * (y - c) = circLoopC c r t := hinj h1
      have h3 : ‖c + (ρ : ℂ) * (y - c) - c‖ = r := by rw [h2, hnormC t]
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real] at h3
      have h5 : |ρ| ≤ 1 := by rw [abs_of_nonneg hρ.1]; exact hρ.2
      have h6 : r ≤ ‖y - c‖ := by rw [← h3]; exact mul_le_of_le_one_left (norm_nonneg _) h5
      linarith
    have h0mem : (0 : ℂ) ∈ Set.image (fun ρ : ℝ => F (c + (ρ : ℂ) * (y - c)) - F c) (Set.Icc (0 : ℝ) 1) :=
      ⟨0, by norm_num, by simp⟩
    have hymem : F y - F c ∈ Set.image (fun ρ : ℝ => F (c + (ρ : ℂ) * (y - c)) - F c) (Set.Icc (0 : ℝ) 1) :=
      ⟨1, by norm_num, by simp⟩
    exact hDmax _ (isPreconnected_Icc.image _ hcont) hsub h0mem hymem
  have hzmem : F z - F c ∈ D := by
    apply hmem
    have h1 : ‖z - c‖ ≤ ‖z - z₀‖ + ‖z₀ - c‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]; exact dist_triangle z z₀ c
    have h2 : ‖z₀ - c‖ < δ / 2 := by rw [norm_sub_rev]; exact hcdist
    have h4 : a < r := hr.1
    rw [hadef] at h4
    linarith
  have hz₀mem : F z₀ - F c ∈ D := by
    apply hmem
    rw [norm_sub_rev]; linarith [hcdist, hδpos, ha, hr.1, hadef]
  have hLgate : ∀ s t : ℝ, ‖γ s - γ t‖
      ≤ (1 + k) * (2 * Real.pi * r) * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖) := by
    intro s t; rw [hγdef]
    exact norm_loopF_sub_le_all hF hk hdil c hrpos s t
  have hsep : ‖F z - F z₀‖ ≤ (1 + k) * (2 * Real.pi * r) * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖) := by
    have h := dist_le_of_frontier_subset hDopen hDbdd hDfront hLgate (F z - F c) hzmem (F z₀ - F c) hz₀mem
    have he : (F z - F c) - (F z₀ - F c) = F z - F z₀ := by ring
    rwa [he] at h
  have hJ : (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖) ^ 2
      ≤ ∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖ ^ 2 :=
    sq_integral_le_integral_sq (((continuous_dz F hF).comp (continuous_circLoopC c r)).norm)
  have hMnn : 0 ≤ (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖) :=
    intervalIntegral.integral_nonneg zero_le_one (fun u _ => norm_nonneg _)
  -- ### Arithmetic.
  have hlogcmp : Real.log (1 / δ) ≤ 5 * Real.log (R / a) := by
    have hRaeq : R / a = 1 / (3 * δ) := by rw [hRdef, hadef]; field_simp
    rw [hRaeq]
    have hδne : δ ≠ 0 := ne_of_gt hδpos
    have hsplit : Real.log (1 / (3 * δ)) = Real.log (1 / δ) - Real.log 3 := by
      rw [show (1:ℝ) / (3 * δ) = (1 / δ) / 3 by ring,
        Real.log_div (div_ne_zero one_ne_zero hδne) (by norm_num)]
    rw [hsplit]
    have h4 : Real.log 4 ≤ Real.log (1 / δ) := by
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ hδpos]; linarith
    have h54 : 5 * Real.log 3 ≤ 4 * Real.log 4 := by
      have h1 : Real.log (3 ^ 5 : ℝ) = 5 * Real.log 3 := Real.log_pow 3 5
      have h2 : Real.log (4 ^ 4 : ℝ) = 4 * Real.log 4 := Real.log_pow 4 4
      have h3 : Real.log (3 ^ 5 : ℝ) ≤ Real.log (4 ^ 4 : ℝ) :=
        Real.log_le_log (by norm_num) (by norm_num)
      rw [h1, h2] at h3; exact h3
    linarith
  have hlogδ : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    rw [one_lt_div hδpos]; linarith
  have hmain : ‖F z - F z₀‖ ^ 2 ≤ 5 * (1 + k) ^ 2 * (2 * Real.pi) * A / (1 - k ^ 2) / Real.log (1 / δ) := by
    have hAnn : 0 ≤ A := ENNReal.toReal_nonneg
    have hlog5 : Real.log (1 / δ) / 5 ≤ Real.log (R / a) := by linarith [hlogcmp]
    have hrecip : 1 / Real.log (R / a) ≤ 5 / Real.log (1 / δ) := by
      have h1 := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < Real.log (1 / δ) / 5) hlog5
      rwa [one_div_div] at h1
    have hJ' : ((1 + k) * (2 * Real.pi * r) * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖)) ^ 2
        = (1 + k) ^ 2 * (2 * Real.pi * r) ^ 2 * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖) ^ 2 := by ring
    have hstep3 : (1 + k) ^ 2 * (2 * Real.pi * r) ^ 2 * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖ ^ 2)
        ≤ (1 + k) ^ 2 * ((2 * Real.pi) ^ 2 * ((1 / (2 * Real.pi)) * ((1 - k ^ 2)⁻¹ * A)) / Real.log (R / a)) := by
      have h := mul_le_mul_of_nonneg_left hr2T (show (0:ℝ) ≤ (1 + k) ^ 2 by positivity)
      calc (1 + k) ^ 2 * (2 * Real.pi * r) ^ 2 * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖ ^ 2)
          = (1 + k) ^ 2 * ((2 * Real.pi * r) ^ 2 * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖ ^ 2)) := by ring
        _ ≤ (1 + k) ^ 2 * ((2 * Real.pi) ^ 2 * ((1 / (2 * Real.pi)) * ((1 - k ^ 2)⁻¹ * A)) / Real.log (R / a)) := h
    have hstep4 : (1 + k) ^ 2 * ((2 * Real.pi) ^ 2 * ((1 / (2 * Real.pi)) * ((1 - k ^ 2)⁻¹ * A)) / Real.log (R / a))
        = (1 + k) ^ 2 * ((2 * Real.pi) * ((1 - k ^ 2)⁻¹ * A) / Real.log (R / a)) := by field_simp
    have hstep5 : (1 + k) ^ 2 * ((2 * Real.pi) * ((1 - k ^ 2)⁻¹ * A) / Real.log (R / a))
        ≤ (1 + k) ^ 2 * ((2 * Real.pi) * ((1 - k ^ 2)⁻¹ * A) * (5 / Real.log (1 / δ))) := by
      have hC : (0 : ℝ) ≤ (1 + k) ^ 2 * ((2 * Real.pi) * ((1 - k ^ 2)⁻¹ * A)) :=
        mul_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (mul_nonneg (inv_nonneg.mpr hk2.le) hAnn))
      have h1 : (1 + k) ^ 2 * ((2 * Real.pi) * ((1 - k ^ 2)⁻¹ * A) / Real.log (R / a))
          = (1 + k) ^ 2 * ((2 * Real.pi) * ((1 - k ^ 2)⁻¹ * A)) * (1 / Real.log (R / a)) := by
        rw [div_eq_mul_inv]; ring
      have h2 : (1 + k) ^ 2 * ((2 * Real.pi) * ((1 - k ^ 2)⁻¹ * A) * (5 / Real.log (1 / δ)))
          = (1 + k) ^ 2 * ((2 * Real.pi) * ((1 - k ^ 2)⁻¹ * A)) * (5 / Real.log (1 / δ)) := by ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left hrecip hC
    have hstep6 : (1 + k) ^ 2 * ((2 * Real.pi) * ((1 - k ^ 2)⁻¹ * A) * (5 / Real.log (1 / δ)))
        = 5 * (1 + k) ^ 2 * (2 * Real.pi) * A / (1 - k ^ 2) / Real.log (1 / δ) := by field_simp
    have hLnn : (0:ℝ) ≤ (1 + k) * (2 * Real.pi * r) * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖) :=
      mul_nonneg (mul_nonneg (by linarith) (by positivity)) hMnn
    calc ‖F z - F z₀‖ ^ 2
        ≤ ((1 + k) * (2 * Real.pi * r) * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖)) ^ 2 := by
          rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hLnn]; exact hsep
      _ = (1 + k) ^ 2 * (2 * Real.pi * r) ^ 2 * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖) ^ 2 := hJ'
      _ ≤ (1 + k) ^ 2 * (2 * Real.pi * r) ^ 2 * (∫ u in (0 : ℝ)..1, ‖dz F (circLoopC c r u)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hJ (by positivity)
      _ ≤ (1 + k) ^ 2 * ((2 * Real.pi) ^ 2 * ((1 / (2 * Real.pi)) * ((1 - k ^ 2)⁻¹ * A)) / Real.log (R / a)) := hstep3
      _ = (1 + k) ^ 2 * ((2 * Real.pi) * ((1 - k ^ 2)⁻¹ * A) / Real.log (R / a)) := hstep4
      _ ≤ (1 + k) ^ 2 * ((2 * Real.pi) * ((1 - k ^ 2)⁻¹ * A) * (5 / Real.log (1 / δ))) := hstep5
      _ = 5 * (1 + k) ^ 2 * (2 * Real.pi) * A / (1 - k ^ 2) / Real.log (1 / δ) := hstep6
  calc ‖F z - F z₀‖ ^ 2
      ≤ 5 * (1 + k) ^ 2 * (2 * Real.pi) * A / (1 - k ^ 2) / Real.log (1 / δ) := hmain
    _ = (5 * (1 + k) ^ 2 * (2 * Real.pi) / (1 - k ^ 2)) * A / Real.log (1 / δ) := by
        field_simp

end Work.MRMT.Found
