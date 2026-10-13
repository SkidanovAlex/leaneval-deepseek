import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel
import Submission.Work.FTS.PressureOn.Auxiliary.integral_heatKernel
import Submission.Work.FTS.PressureOn.Auxiliary.deriv_heatKernel_time
import Submission.Work.FTS.PressureOn.Auxiliary.hasDerivAt_heatKernel_time
import Submission.Work.FTS.PressureOn.Auxiliary.laplaceTrace_comp_sub
import Submission.Work.FTS.PressureOn.Auxiliary.integral_abs_heatKernel_sub_le
import Submission.Work.FTS.PressureOn.Auxiliary.tendsto_tail_heatKernel
import Submission.Work.FTS.PressureOn.Auxiliary.integral_mul_laplaceTrace_heatKernel_eq_zero
import Submission.Work.FTS.PressureOn.Auxiliary.integrable_gaussMajorant
import Submission.Work.FTS.PressureOn.Auxiliary.abs_deriv_heatKernel_time_le
import Submission.Work.FTS.PressureOn.Auxiliary.tendsto_integral_heatKernel_smul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Liouville's theorem for bounded harmonic functions on `ℝ³`

A bounded smooth function `u : ℝ³ → ℝ` whose Hessian trace `laplaceTrace u` vanishes everywhere is
constant.  The proof is the classical heat-kernel argument: the heat regularisation
`heatReg u t x = ∫ y, u y * heatKernel t (x - y)` of a harmonic function is independent of the time
`t` (differentiate under the integral sign, use the heat equation `∂_t γ = Δγ` and integrate by
parts against the harmonic function), is independent of `x` (let `t → ∞` and use the `L¹` modulus
of continuity of the Gaussian), and converges to `u` as `t → 0⁺` (the heat kernel is an
approximate identity).
-/

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-! ### Helper lemmas -/

/-- The heat regularisation `u * γ_t` of `u`. -/
def heatReg (u : R3 → ℝ) (t : ℝ) (x : R3) : ℝ := ∫ y, u y * heatKernel t (x - y)

lemma heatReg_apply (u : R3 → ℝ) (t : ℝ) (x : R3) :
    heatReg u t x = ∫ y, u y * heatKernel t (x - y) := rfl

/-- Substituting `y = x - w` in the heat regularisation. -/
lemma heatReg_eq_sub (u : R3 → ℝ) (t : ℝ) (x : R3) :
    heatReg u t x = ∫ y, u (x - y) * heatKernel t y := by
  rw [heatReg]
  rw [← MeasureTheory.integral_sub_left_eq_self
    (fun z : R3 => u (x - z) * heatKernel t z) volume x]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
    simp only [sub_sub_cancel])

/-- A function whose integral does not vanish is integrable. -/
lemma integrable_of_integral_ne_zero {f : R3 → ℝ} (h : ∫ z, f z ≠ 0) : Integrable f := by
  by_contra hf
  exact h (MeasureTheory.integral_undef hf)

lemma integrable_heatKernel {t : ℝ} (ht : 0 < t) : Integrable (heatKernel t) := by
  refine integrable_of_integral_ne_zero ?_
  rw [integral_heatKernel t ht]
  norm_num

lemma integrable_heatKernel_sub {t : ℝ} (ht : 0 < t) (x : R3) :
    Integrable (fun y : R3 => heatKernel t (x - y)) := by
  refine integrable_of_integral_ne_zero ?_
  rw [MeasureTheory.integral_sub_left_eq_self (fun z : R3 => heatKernel t z) volume x,
    integral_heatKernel t ht]
  norm_num

lemma integral_heatKernel_sub {t : ℝ} (ht : 0 < t) (x : R3) :
    ∫ y, heatKernel t (x - y) = 1 := by
  rw [MeasureTheory.integral_sub_left_eq_self (fun z : R3 => heatKernel t z) volume x,
    integral_heatKernel t ht]

/-- The explicit value of the Laplacian of the heat kernel, obtained by combining the heat
equation (as a `deriv`) with the explicit time derivative. -/
lemma laplaceTrace_heatKernel_eq (t : ℝ) (ht : 0 < t) (z : R3) :
    laplaceTrace (heatKernel t) z
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (‖z‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) *
          Real.exp (-(‖z‖ ^ 2 / (4 * t))) := by
  rw [← (hasDerivAt_heatKernel_time t ht z).deriv, deriv_heatKernel_time t ht z]

lemma continuous_heatKernel (t : ℝ) (ht : 0 < t) : Continuous (heatKernel t) := by
  have h : heatKernel t = fun z : R3 =>
      (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / (4 * t))) := rfl
  rw [h]
  refine continuous_const.mul (Real.continuous_exp.comp ?_)
  exact ((continuous_norm.pow 2).div_const (4 * t)).neg

lemma continuous_explicit (t : ℝ) :
    Continuous (fun y : R3 => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
      (‖y‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) * Real.exp (-(‖y‖ ^ 2 / (4 * t)))) := by
  have h1 : Continuous (fun y : R3 => ‖y‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t) : R3 → ℝ) :=
    ((continuous_norm.pow 2).div_const (4 * t ^ 2)).sub continuous_const
  have h2 : Continuous (fun y : R3 => Real.exp (-(‖y‖ ^ 2 / (4 * t)))) :=
    Real.continuous_exp.comp (((continuous_norm.pow 2).div_const (4 * t)).neg)
  have h3 : Continuous (fun y : R3 => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
      ((‖y‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) * Real.exp (-(‖y‖ ^ 2 / (4 * t))))) :=
    continuous_const.mul (h1.mul h2)
  refine h3.congr ?_
  intro y
  ring

lemma norm_sub_sq_le (x y : R3) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  have h2 : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [h2, sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y]

lemma norm_sq_le_two (x y : R3) : ‖y‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖x‖ ^ 2 := by
  have h : ‖y‖ ≤ ‖x - y‖ + ‖x‖ := by
    calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ = ‖x - y‖ + ‖x‖ := by rw [norm_sub_rev]
  have h2 : ‖y‖ ^ 2 ≤ (‖x - y‖ + ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [h2, sq_nonneg (‖x - y‖ - ‖x‖), norm_nonneg x, norm_nonneg (x - y)]

/-- Integrability of `u` times a translated heat kernel. -/
lemma integrable_mul_heatKernel_sub {t : ℝ} (ht : 0 < t) {u : R3 → ℝ} {M : ℝ}
    (hM : ∀ x, |u x| ≤ M) (hu : Continuous u) (x : R3) :
    Integrable (fun y : R3 => u y * heatKernel t (x - y)) := by
  refine Integrable.mono' ((integrable_heatKernel_sub ht x).const_mul M) ?_ ?_
  · exact ((hu.measurable.mul ((continuous_heatKernel t ht).measurable.comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable)
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg (le_of_lt ht) (x - y))]
    exact mul_le_mul_of_nonneg_right (hM y) (heatKernel_nonneg (le_of_lt ht) (x - y))

/-- Integrability of the absolute value of a difference of translated heat kernels. -/
lemma integrable_abs_heatKernel_sub {t : ℝ} (ht : 0 < t) (h : R3) :
    Integrable (fun z : R3 => |heatKernel t (z + h) - heatKernel t z|) := by
  have h1 : Integrable (fun z : R3 => heatKernel t (z + h)) := by
    have h0 := integrable_heatKernel_sub ht (-h)
    refine h0.congr (Filter.Eventually.of_forall fun z => ?_)
    change heatKernel t (-h - z) = heatKernel t (z + h)
    rw [show -h - z = -(z + h) by abel, heatKernel_even]
  have h2 : Integrable (fun z : R3 => heatKernel t z) := integrable_heatKernel ht
  refine Integrable.mono' (h1.add h2) ?_ ?_
  · exact ((((continuous_heatKernel t ht).comp (continuous_id.add continuous_const)).sub
      (continuous_heatKernel t ht)).abs.aestronglyMeasurable)
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_abs]
    simp only [Pi.add_apply]
    rw [abs_le]
    constructor <;> linarith [heatKernel_nonneg (le_of_lt ht) z,
      heatKernel_nonneg (le_of_lt ht) (z + h)]

/-! ### Liouville's theorem -/

theorem bounded_harmonic_const (u : EuclideanSpace ℝ (Fin 3) → ℝ) (hu : ∀ n : ℕ, ContDiff ℝ n u)
    (hlap : ∀ x, Work.FTS.PressureOn.laplaceTrace u x = 0)
    (hbdd : ∃ C, ∀ x, |u x| ≤ C) : ∃ c : ℝ, ∀ x, u x = c := by
  obtain ⟨M, hM⟩ := hbdd
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  have hucont : Continuous u := (hu 0).continuous
  -- ## Step 1: the time derivative of the heat regularisation vanishes
  have hderiv : ∀ (x : R3) (t : ℝ), 0 < t → HasDerivAt (fun r : ℝ => heatReg u r x) 0 t := by
    intro x t ht
    have hbt : (0 : ℝ) < t / 2 := by linarith
    set C₁ : ℝ := (4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) with hC₁
    set a₀ : ℝ := 3 / t + 2 * ‖x‖ ^ 2 / t ^ 2 with ha₀
    set b₀ : ℝ := 2 / t ^ 2 with hb₀
    set c₀ : ℝ := 1 / (16 * t) with hc₀
    set E : ℝ := Real.exp (‖x‖ ^ 2 / (8 * t)) with hE
    set bound : R3 → ℝ := fun y =>
      M * C₁ * (E * ((a₀ + b₀ * ‖y‖ ^ 2) * Real.exp (-(c₀ * ‖y‖ ^ 2)))) with hbound
    have hC₁pos : 0 ≤ C₁ := by rw [hC₁]; positivity
    have hEpos : 0 ≤ E := by rw [hE]; positivity
    have ha₀pos : 0 ≤ a₀ := by rw [ha₀]; positivity
    have hb₀pos : 0 ≤ b₀ := by rw [hb₀]; positivity
    have hc₀pos : 0 < c₀ := by rw [hc₀]; positivity
    have habs : ∀ y : R3, 0 ≤ a₀ + b₀ * ‖y‖ ^ 2 := by
      intro y; nlinarith [ha₀pos, hb₀pos, sq_nonneg ‖y‖]
    have hbound_int : Integrable bound := by
      rw [hbound]
      exact ((integrable_gaussMajorant a₀ b₀ c₀ ha₀pos hb₀pos hc₀pos).const_mul E).const_mul (M * C₁)
    have hpd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure R3))
      (F := fun r y => u y * heatKernel r (x - y))
      (F' := fun r y => u y * laplaceTrace (heatKernel r) (x - y))
      (bound := bound) (s := Set.Ioo (t / 2) (2 * t)) (x₀ := t)
      (IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩)
      (by
        filter_upwards [IsOpen.mem_nhds isOpen_Ioi ht] with r hr
        exact ((hucont.measurable.mul (((contDiff_heatKernel r hr 2).continuous.measurable).comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable))
      (integrable_mul_heatKernel_sub ht hM hucont x)
      (by
        rw [show (fun y : R3 => u y * laplaceTrace (heatKernel t) (x - y)) =
            (fun y : R3 => u y * ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
              (‖x - y‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) *
              Real.exp (-(‖x - y‖ ^ 2 / (4 * t))))) from by
          funext y; rw [laplaceTrace_heatKernel_eq t ht (x - y)]]
        exact (hucont.measurable.mul ((continuous_explicit t).comp
          (continuous_const.sub continuous_id)).measurable).aestronglyMeasurable)
      (by
        filter_upwards with y r hr
        have hrpos : 0 < r := lt_of_lt_of_le hbt (le_of_lt hr.1)
        have h2 : |laplaceTrace (heatKernel r) (x - y)| ≤
            C₁ * ((3 / t + ‖x - y‖ ^ 2 / t ^ 2) * Real.exp (-(‖x - y‖ ^ 2 / (8 * t)))) := by
          have h2' := abs_deriv_heatKernel_time_le t ht r (le_of_lt hr.1) (le_of_lt hr.2) (x - y)
          calc |laplaceTrace (heatKernel r) (x - y)|
              = |deriv (fun s : ℝ => heatKernel s (x - y)) r| := by
                rw [laplaceTrace_heatKernel_eq r hrpos (x - y),
                  ← deriv_heatKernel_time r hrpos (x - y)]
            _ ≤ (4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) * (3 / t + ‖x - y‖ ^ 2 / t ^ 2) *
                  Real.exp (-(‖x - y‖ ^ 2 / (8 * t))) := h2'
            _ = C₁ * ((3 / t + ‖x - y‖ ^ 2 / t ^ 2) *
                  Real.exp (-(‖x - y‖ ^ 2 / (8 * t)))) := by rw [hC₁]; ring
        have hA : 3 / t + ‖x - y‖ ^ 2 / t ^ 2 ≤ a₀ + b₀ * ‖y‖ ^ 2 := by
          rw [ha₀, hb₀]
          have h := norm_sub_sq_le x y
          have ht2 : (0 : ℝ) < t ^ 2 := by positivity
          have h' : ‖x - y‖ ^ 2 / t ^ 2 ≤ (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) / t ^ 2 :=
            div_le_div_of_nonneg_right h (le_of_lt ht2)
          have e : (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) / t ^ 2
              = 2 * ‖x‖ ^ 2 / t ^ 2 + 2 / t ^ 2 * ‖y‖ ^ 2 := by ring
          rw [e] at h'
          linarith
        have hB : Real.exp (-(‖x - y‖ ^ 2 / (8 * t))) ≤ E * Real.exp (-(c₀ * ‖y‖ ^ 2)) := by
          rw [hE, hc₀, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have h := norm_sq_le_two x y
          have h16 : (0 : ℝ) < 16 * t := by positivity
          have h' : ‖y‖ ^ 2 / (16 * t) ≤ (2 * ‖x - y‖ ^ 2 + 2 * ‖x‖ ^ 2) / (16 * t) :=
            div_le_div_of_nonneg_right h (le_of_lt h16)
          have e : (2 * ‖x - y‖ ^ 2 + 2 * ‖x‖ ^ 2) / (16 * t)
              = ‖x - y‖ ^ 2 / (8 * t) + ‖x‖ ^ 2 / (8 * t) := by ring
          have h'' : ‖y‖ ^ 2 / (16 * t) ≤ ‖x - y‖ ^ 2 / (8 * t) + ‖x‖ ^ 2 / (8 * t) := by
            rw [← e]; exact h'
          have e2 : 1 / (16 * t) * ‖y‖ ^ 2 = ‖y‖ ^ 2 / (16 * t) := by ring
          rw [e2]
          linarith
        have h5 : (3 / t + ‖x - y‖ ^ 2 / t ^ 2) * Real.exp (-(‖x - y‖ ^ 2 / (8 * t)))
            ≤ E * ((a₀ + b₀ * ‖y‖ ^ 2) * Real.exp (-(c₀ * ‖y‖ ^ 2))) := by
          have hAB := mul_le_mul hA hB (le_of_lt (Real.exp_pos _)) (habs y)
          calc (3 / t + ‖x - y‖ ^ 2 / t ^ 2) * Real.exp (-(‖x - y‖ ^ 2 / (8 * t)))
              ≤ (a₀ + b₀ * ‖y‖ ^ 2) * (E * Real.exp (-(c₀ * ‖y‖ ^ 2))) := hAB
            _ = E * ((a₀ + b₀ * ‖y‖ ^ 2) * Real.exp (-(c₀ * ‖y‖ ^ 2))) := by ring
        calc ‖u y * laplaceTrace (heatKernel r) (x - y)‖
            = |u y| * |laplaceTrace (heatKernel r) (x - y)| := by
              rw [Real.norm_eq_abs, abs_mul]
          _ ≤ M * (C₁ * ((3 / t + ‖x - y‖ ^ 2 / t ^ 2) *
                Real.exp (-(‖x - y‖ ^ 2 / (8 * t))))) :=
              mul_le_mul (hM y) h2 (abs_nonneg _) hM0
          _ ≤ M * (C₁ * (E * ((a₀ + b₀ * ‖y‖ ^ 2) * Real.exp (-(c₀ * ‖y‖ ^ 2))))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hC₁pos) hM0
          _ = bound y := by rw [hbound]; ring)
      hbound_int
      (by
        filter_upwards with y r hr
        exact (hasDerivAt_heatKernel_time r (lt_of_lt_of_le hbt (le_of_lt hr.1)) (x - y)).const_mul
          (u y))
    have hval : (∫ y, u y * laplaceTrace (heatKernel t) (x - y)) = 0 := by
      rw [← integral_mul_laplaceTrace_heatKernel_eq_zero u hu hlap M hM x t ht]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only []
      rw [laplaceTrace_comp_sub (heatKernel t) (contDiff_heatKernel t ht 2) x y]
    have hpd0 : HasDerivAt (fun r : ℝ => ∫ y, u y * heatKernel r (x - y)) 0 t := by
      rw [← hval]
      exact hpd.2
    exact hpd0
  -- ## Step 2: `heatReg u · x` is constant in `t`
  have hconst : ∀ (x : R3) (s t : ℝ), 0 < s → 0 < t → heatReg u s x = heatReg u t x := by
    intro x s t hs ht
    have hkey : ∀ τ ∈ Set.uIcc s t, HasDerivAt (fun r : ℝ => heatReg u r x) 0 τ := by
      intro τ hτ
      rw [Set.uIcc, Set.mem_Icc] at hτ
      exact hderiv x τ (lt_of_lt_of_le (lt_min hs ht) hτ.1)
    have hsub : (∫ τ in s..t, (0 : ℝ)) = heatReg u t x - heatReg u s x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r : ℝ => heatReg u r x)
        (f' := fun _ : ℝ => 0) hkey intervalIntegrable_const
    rw [intervalIntegral.integral_zero] at hsub
    linarith
  -- ## Step 3: the value at `t = 1` does not depend on the point
  have hspread : ∀ x₁ x₂ : R3, heatReg u 1 x₁ = heatReg u 1 x₂ := by
    intro x₁ x₂
    have hkey : ∀ t : ℝ, 0 < t →
        |heatReg u 1 x₁ - heatReg u 1 x₂| ≤ M * (4 * ‖x₁ - x₂‖ / Real.sqrt t) := by
      intro t ht
      rw [hconst x₁ 1 t one_pos ht, hconst x₂ 1 t one_pos ht, heatReg, heatReg]
      rw [← integral_sub (integrable_mul_heatKernel_sub ht hM hucont x₁)
        (integrable_mul_heatKernel_sub ht hM hucont x₂)]
      rw [show (fun y : R3 => u y * heatKernel t (x₁ - y) - u y * heatKernel t (x₂ - y))
            = fun y : R3 => u y * (heatKernel t (x₁ - y) - heatKernel t (x₂ - y)) from by
          funext y; ring]
      rw [← MeasureTheory.integral_sub_left_eq_self
        (fun w : R3 => u w * (heatKernel t (x₁ - w) - heatKernel t (x₂ - w))) volume x₂]
      rw [show (fun z : R3 => u (x₂ - z) *
              (heatKernel t (x₁ - (x₂ - z)) - heatKernel t (x₂ - (x₂ - z))))
            = fun z : R3 => u (x₂ - z) *
              (heatKernel t (z + (x₁ - x₂)) - heatKernel t z) from by
          funext z
          rw [show x₂ - (x₂ - z) = z by abel,
            show x₁ - (x₂ - z) = z + (x₁ - x₂) by abel]]
      have h4 : |∫ z, u (x₂ - z) * (heatKernel t (z + (x₁ - x₂)) - heatKernel t z)|
          ≤ ∫ z, |u (x₂ - z) * (heatKernel t (z + (x₁ - x₂)) - heatKernel t z)| := by
        rw [← Real.norm_eq_abs]
        exact MeasureTheory.norm_integral_le_integral_norm _
      refine h4.trans ?_
      have h5 : (∫ z, |u (x₂ - z) * (heatKernel t (z + (x₁ - x₂)) - heatKernel t z)|)
          ≤ M * ∫ z, |heatKernel t (z + (x₁ - x₂)) - heatKernel t z| := by
        have h6 : (∫ z, |u (x₂ - z) * (heatKernel t (z + (x₁ - x₂)) - heatKernel t z)|)
            ≤ ∫ z, M * |heatKernel t (z + (x₁ - x₂)) - heatKernel t z| := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
            ((integrable_abs_heatKernel_sub ht (x₁ - x₂)).const_mul M) ?_
          filter_upwards with z
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hM (x₂ - z)) (abs_nonneg _)
        rwa [integral_const_mul] at h6
      refine h5.trans ?_
      have h7 : (∫ z, |heatKernel t (z + (x₁ - x₂)) - heatKernel t z|)
          ≤ 4 * ‖x₁ - x₂‖ / Real.sqrt t := by
        have hR4 := integral_abs_heatKernel_sub_le (-(x₁ - x₂)) t ht
        have hc : (fun z : R3 => |heatKernel t (z + (x₁ - x₂)) - heatKernel t z|)
            = fun z : R3 => |heatKernel t (z - (-(x₁ - x₂))) - heatKernel t z| := by
          funext z
          rw [sub_neg_eq_add]
        rw [hc]
        simpa [norm_sub_rev] using hR4
      exact mul_le_mul_of_nonneg_left h7 hM0
    have hlim : Tendsto (fun t : ℝ => M * (4 * ‖x₁ - x₂‖ / Real.sqrt t)) atTop (𝓝 0) := by
      have hsqrt : Tendsto (fun t : ℝ => Real.sqrt t) atTop atTop := Real.tendsto_sqrt_atTop
      have hinv : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hsqrt
      have h0 : Tendsto (fun t : ℝ => M * (4 * ‖x₁ - x₂‖) * (Real.sqrt t)⁻¹) atTop
          (𝓝 (M * (4 * ‖x₁ - x₂‖) * 0)) := tendsto_const_nhds.mul hinv
      rw [mul_zero] at h0
      refine h0.congr' ?_
      filter_upwards with t
      rw [div_eq_mul_inv]
      ring
    have habs0 : |heatReg u 1 x₁ - heatReg u 1 x₂| ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim
        (eventually_atTop.2 ⟨1, fun t ht => hkey t (by linarith)⟩)
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm habs0 (abs_nonneg _)))
  -- ## Step 4: the heat regularisation converges to `u` as `t → 0⁺`
  have hconc : ∀ x : R3, heatReg u 1 x = u x := by
    intro x
    have h1 := tendsto_integral_heatKernel_smul u hucont ⟨M, hM⟩ x
    have h2 : Tendsto (fun t : ℝ => ∫ y, u (x - y) * heatKernel t y)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (heatReg u 1 x)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hconst x 1 t one_pos ht, heatReg_eq_sub u t x]
    exact tendsto_nhds_unique h2 h1
  refine ⟨u 0, fun x => ?_⟩
  rw [← hconc x, ← hconc 0]
  exact hspread x 0

end

end Work.FTS.PressureOn.Auxiliary
