import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dirichlet integral

We prove `Commons.Analysis.Fourier.dirichlet_integral` below:

    lim_{T→∞} ∫_0^T sin(x)/x dx = π/2

## Method

For a finite upper limit `T ≥ 0` write, for `x > 0`, the Laplace identity
`1/x = ∫_0^∞ e^{−xy} dy`, and use Fubini on the half-strip `(0, T] × (0, ∞)`:

    ∫_0^T sin(x)/x dx = ∫_0^∞ [∫_0^T e^{−xy} sin(x) dx] dy .

The inner integral is computed exactly by the fundamental theorem of calculus:

    ∫_0^T e^{−xy} sin(x) dx = (1 − e^{−yT}(cos T + y sin T)) / (1 + y²) .

The outer integral over `y > 0` is then shown to tend to
`∫_0^∞ (1+y²)⁻¹ dy = π/2` as `T → ∞` by dominated convergence, since
`e^{−yT}(cos T + y sin T) → 0` pointwise for `y > 0` and
`|1 − e^{−yT}(cos T + y sin T)|/(1+y²) ≤ 2/(1+y²)` for `T ≥ 1`.
-/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology

namespace Commons.Analysis.Fourier

/-- The exact inner `x`-integral of `e^{-xy} sin x`, as a function of the upper limit `T`
and the parameter `y`. -/
def Kernel (T y : ℝ) : ℝ :=
  (1 - Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)) / (1 + y ^ 2)

/-! ## Laplace transform of the indicator of the positive half-line -/

/-- For `x > 0`, `∫_0^∞ e^{-xy} dy = 1 / x`. -/
lemma exp_neg_Ioi (x : ℝ) (hx : 0 < x) :
    (∫ y : ℝ in Ioi (0 : ℝ), Real.exp (-(x * y))) = x⁻¹ := by
  have h := integral_exp_mul_Ioi (a := -x) (by linarith) (0 : ℝ)
  simpa [neg_mul, neg_div, div_neg, hx.ne'] using h

/-- For `x > 0`, `sin x / x = ∫_0^∞ e^{-xy} sin x dy`. -/
lemma sin_laplace (x : ℝ) (hx : 0 < x) :
    (∫ y : ℝ in Ioi (0 : ℝ), Real.sin x * Real.exp (-(x * y))) = Real.sin x / x := by
  calc
    (∫ y : ℝ in Ioi (0 : ℝ), Real.sin x * Real.exp (-(x * y))) = Real.sin x * (∫ y : ℝ in Ioi (0 : ℝ), Real.exp (-(x * y))) := by
      rw [← integral_const_mul]
    _ = Real.sin x / x := by rw [exp_neg_Ioi x hx, div_eq_mul_inv]

/-! ## Exact computation of the finite `x`-integral -/

/-- Antiderivative of `x ↦ e^{-yx} sin x`. -/
lemma exp_neg_mul_sin_antideriv (y x : ℝ) :
    HasDerivAt (fun z : ℝ => (-(Real.exp (-(y * z)) * (Real.cos z + y * Real.sin z))) / (1 + y ^ 2))
      (Real.exp (-(y * x)) * Real.sin x) x := by
  have hlin : HasDerivAt (fun z : ℝ => -(y * z)) (-y) x := by
    convert! ((hasDerivAt_id x).const_mul y).neg using 1 <;> ring
  have he : HasDerivAt (fun z : ℝ => Real.exp (-(y * z))) (Real.exp (-(y * x)) * (-y)) x := by
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_exp (-(y * x))).comp x hlin
  have hsum : HasDerivAt (fun z : ℝ => Real.cos z + y * Real.sin z) (-Real.sin x + y * Real.cos x) x := by
    have h := (Real.hasDerivAt_cos x).add ((Real.hasDerivAt_sin x).const_mul y)
    convert! h using 1 <;> ring
  have hG : HasDerivAt (fun z : ℝ => Real.exp (-(y * z)) * (Real.cos z + y * Real.sin z))
      (-(1 + y ^ 2) * Real.exp (-(y * x)) * Real.sin x) x := by
    have h := he.mul hsum
    convert! h using 1 <;> ring
  have hF0 := (hG.neg).div_const (1 + y ^ 2)
  convert! hF0 using 1
  all_goals
    try field_simp [show (1 + y ^ 2 : ℝ) ≠ 0 by nlinarith [sq_nonneg y]]
    try ring

/-- `∫_0^T e^{-yx} sin x dx = (1 - e^{-yT} (cos T + y sin T)) / (1 + y²)`. -/
lemma integral_exp_neg_mul_sin (T y : ℝ) :
    (∫ x in (0 : ℝ)..T, Real.exp (-(y * x)) * Real.sin x) = Kernel T y := by
  let F : ℝ → ℝ := fun z => (-(Real.exp (-(y * z)) * (Real.cos z + y * Real.sin z))) / (1 + y ^ 2)
  have hint : IntervalIntegrable (fun x => Real.exp (-(y * x)) * Real.sin x) volume (0 : ℝ) T := by
    exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-(y * x)) * Real.sin x).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F) (f' := fun x => Real.exp (-(y * x)) * Real.sin x)]
  · dsimp [F, Kernel]
    field_simp [show (1 + y ^ 2 : ℝ) ≠ 0 by nlinarith [sq_nonneg y]]
    simp [exp_zero, cos_zero, sin_zero]
    ring
  · intro x hx
    dsimp [F]
    exact exp_neg_mul_sin_antideriv y x
  · exact hint

/-- The same integral with the factors commuted. -/
lemma integral_sin_exp_neg (T y : ℝ) :
    (∫ x in (0 : ℝ)..T, Real.sin x * Real.exp (-(x * y))) = Kernel T y := by
  have h := integral_exp_neg_mul_sin T y
  rw [← h]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp
  rw [mul_comm x y, mul_comm]

/-! ## Fubini over the half-strip `(0, T] × (0, ∞)` -/

/-- `‖sin x · e^{-xy}‖` as a function of `y` integrates to `|sin x| / x` for `x > 0`. -/
lemma abs_norm_strip (x : ℝ) (hx : 0 < x) :
    (∫ y : ℝ in Ioi (0 : ℝ), |Real.sin x * Real.exp (-(x * y))|) = |Real.sin x| * x⁻¹ := by
  have hnorm : (fun y : ℝ => |Real.sin x * Real.exp (-(x * y))|)
      = fun y : ℝ => |Real.sin x| * Real.exp (-(x * y)) := by
    funext y
    rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  rw [hnorm, integral_const_mul, exp_neg_Ioi x hx]

/-- `(x, y) ↦ sin x · e^{-xy}` is integrable over the half-strip `(0, T] × (0, ∞)`. -/
lemma integrable_strip (T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (fun z : ℝ × ℝ => Real.sin z.1 * Real.exp (-(z.1 * z.2)))
      (Ioc 0 T ×ˢ Ioi (0 : ℝ)) (volume.prod volume) := by
  rw [IntegrableOn]
  rw [← Measure.prod_restrict (Ioc 0 T) (Ioi (0 : ℝ))]
  let f : ℝ × ℝ → ℝ := fun z => Real.sin z.1 * Real.exp (-(z.1 * z.2))
  have h1f : AEStronglyMeasurable f ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    dsimp [f]
    exact (by fun_prop : Continuous fun z : ℝ × ℝ => Real.sin z.1 * Real.exp (-(z.1 * z.2))).aestronglyMeasurable
  rw [integrable_prod_iff (μ := volume.restrict (Ioc 0 T)) (ν := volume.restrict (Ioi (0 : ℝ))) (f := f) h1f]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hxmem
    dsimp [f]
    have hx : 0 < x := hxmem.1
    have hExp : IntegrableOn (fun y : ℝ => Real.exp (-(x * y))) (Ioi (0 : ℝ)) volume := by
      simpa [neg_mul] using (integrableOn_exp_mul_Ioi (a := -x) (by linarith) (0 : ℝ))
    change Integrable (fun y : ℝ => Real.sin x * Real.exp (-(x * y))) (volume.restrict (Ioi (0 : ℝ)))
    exact (hExp.integrable.const_mul (Real.sin x))
  · let g : ℝ → ℝ := fun x => ∫ y : ℝ in Ioi (0 : ℝ), ‖Real.sin x * Real.exp (-(x * y))‖
    have hc_sinc : Continuous fun x : ℝ => |Real.sinc x| := continuous_abs.comp Real.continuous_sinc
    have h_int_sinc : IntegrableOn (fun x : ℝ => |Real.sinc x|) (Ioc 0 T) volume := by
      refine (hc_sinc.integrableOn_Icc (a := 0) (b := T)).mono_set ?_
      intro x hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    have h_eq : g =ᵐ[volume.restrict (Ioc 0 T)] (fun x : ℝ => |Real.sinc x|) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hxmem
      dsimp [g]
      rw [abs_norm_strip x hxmem.1]
      rw [Real.sinc_of_ne_zero (ne_of_gt hxmem.1), div_eq_mul_inv, abs_mul]
      rw [abs_of_nonneg (inv_nonneg.mpr (le_of_lt hxmem.1))]
    have h1 : Integrable (fun x : ℝ => |Real.sinc x|) (volume.restrict (Ioc 0 T)) := h_int_sinc
    exact Integrable.congr h1 h_eq.symm

/-- **Fubini identity**: for `T ≥ 0`, `∫_0^T sin x / x dx` equals the outer `y`-integral
of the exact inner `x`-integral. -/
lemma dirichlet_eq_kernel (T : ℝ) (hT : 0 ≤ T) :
    (∫ x in (0 : ℝ)..T, Real.sin x / x) = ∫ y in Ioi (0 : ℝ), Kernel T y := by
  let s : Set ℝ := Ioc 0 T
  let t : Set ℝ := Ioi (0 : ℝ)
  let f : ℝ × ℝ → ℝ := fun z => Real.sin z.1 * Real.exp (-(z.1 * z.2))
  have hs_meas : MeasurableSet s := by dsimp [s]; exact measurableSet_Ioc
  have ht_meas : MeasurableSet t := by dsimp [t]; exact measurableSet_Ioi
  have hf : IntegrableOn f (s ×ˢ t) (volume.prod volume) := by
    dsimp [s, t, f]
    exact integrable_strip T hT
  have hfsw : IntegrableOn (fun w : ℝ × ℝ => f w.swap) (t ×ˢ s) (volume.prod volume) := by
    rw [IntegrableOn]
    rw [← Measure.prod_restrict t s]
    change Integrable (f ∘ Prod.swap) ((volume.restrict t).prod (volume.restrict s))
    rw [integrable_swap_iff (μ := volume.restrict s) (ν := volume.restrict t) (f := f)]
    rw [Measure.prod_restrict s t]
    exact hf
  calc
    (∫ x in (0 : ℝ)..T, Real.sin x / x)
        = ∫ x in s, Real.sin x / x := by
          dsimp [s]
          rw [intervalIntegral.integral_of_le (μ := volume) hT]
    _ = ∫ x in s, ∫ y in t, f (x, y) := by
          apply setIntegral_congr_ae hs_meas
          filter_upwards [] with x
          intro hxmem
          have hx : 0 < x := by dsimp [s] at hxmem; exact hxmem.1
          dsimp [f, t]
          exact (sin_laplace x hx).symm
    _ = ∫ z in s ×ˢ t, f z := by
          exact (setIntegral_prod f hf).symm
    _ = ∫ z' in t ×ˢ s, (fun w : ℝ × ℝ => f w.swap) z' := by
          exact (setIntegral_prod_swap s t f).symm
    _ = ∫ y in t, ∫ x in s, f (x, y) := by
          exact setIntegral_prod (fun w : ℝ × ℝ => f w.swap) hfsw
    _ = ∫ y in Ioi (0 : ℝ), Kernel T y := by
          dsimp [t]
          apply setIntegral_congr_ae ht_meas
          filter_upwards [] with y
          intro hymem
          dsimp [s, f]
          calc
            (∫ x in Ioc 0 T, Real.sin x * Real.exp (-(x * y))) = ∫ x in (0 : ℝ)..T, Real.sin x * Real.exp (-(x * y)) := by
              rw [← intervalIntegral.integral_of_le (μ := volume) hT]
            _ = Kernel T y := integral_sin_exp_neg T y

/-! ## The outer `y`-integral: dominated convergence as `T → ∞` -/

/-- `|cos T + y sin T| ≤ 1 + y` for `y ≥ 0`. -/
lemma abs_cos_add_mul_sin_le (y T : ℝ) (hy : 0 ≤ y) :
    |Real.cos T + y * Real.sin T| ≤ 1 + y := by
  calc
    |Real.cos T + y * Real.sin T| ≤ |Real.cos T| + |y * Real.sin T| := abs_add_le _ _
    _ = |Real.cos T| + y * |Real.sin T| := by rw [abs_mul, abs_of_nonneg hy]
    _ ≤ 1 + y * 1 := by
      exact add_le_add (Real.abs_cos_le_one T) (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one T) hy)
    _ = 1 + y := by ring

/-- `e^{-yT}(1 + y) ≤ 1` for `T ≥ 1` and `y ≥ 0`. -/
lemma exp_neg_mul_one_add_le_one (T y : ℝ) (hT : 1 ≤ T) (hy : 0 ≤ y) :
    Real.exp (-(y * T)) * (1 + y) ≤ 1 := by
  have hy' : (1 + y : ℝ) ≥ 0 := by linarith
  have he1 : Real.exp (-(y * T)) ≤ Real.exp (-y) := by
    rw [Real.exp_le_exp]
    have hm : y * 1 ≤ y * T := by
      exact mul_le_mul_of_nonneg_left hT hy
    linarith
  have he2 : Real.exp (-y) * (1 + y) ≤ 1 := by
    have hle : 1 + y ≤ Real.exp y := by simpa [add_comm] using Real.add_one_le_exp y
    have hpos : 0 ≤ Real.exp (-y) := (Real.exp_pos (-y)).le
    calc
      Real.exp (-y) * (1 + y) ≤ Real.exp (-y) * Real.exp y := by
        exact mul_le_mul_of_nonneg_left hle hpos
      _ = 1 := by
        rw [Real.exp_neg, mul_comm, mul_inv_cancel₀ (Real.exp_ne_zero y)]
  calc
    Real.exp (-(y * T)) * (1 + y) ≤ Real.exp (-y) * (1 + y) := by
      exact mul_le_mul_of_nonneg_right he1 hy'
    _ ≤ 1 := he2

/-- Dominating bound: `|Kernel T y| ≤ 2/(1+y²)` for `T ≥ 1` and `y ≥ 0`. -/
lemma kernel_norm_bound (T y : ℝ) (hT : 1 ≤ T) (hy : 0 ≤ y) :
    |Kernel T y| ≤ 2 * (1 + y ^ 2)⁻¹ := by
  have hden_pos : 0 < 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  have hb : |Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)| ≤ 1 := by
    calc
      |Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)|
          = Real.exp (-(y * T)) * |Real.cos T + y * Real.sin T| := by
            rw [abs_mul, abs_of_nonneg (Real.exp_pos (-(y * T))).le]
      _ ≤ Real.exp (-(y * T)) * (1 + y) := by
            exact mul_le_mul_of_nonneg_left (abs_cos_add_mul_sin_le y T hy) (Real.exp_pos (-(y * T))).le
      _ ≤ 1 := exp_neg_mul_one_add_le_one T y hT hy
  have hnum : |1 - Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)| ≤ 2 := by
    calc
      |1 - Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)|
          ≤ 1 + |Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)| := by
            simpa [sub_eq_add_neg] using (abs_sub (1 : ℝ) (Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)))
      _ ≤ 1 + 1 := by linarith [hb]
      _ = 2 := by norm_num
  calc
    |Kernel T y| = |1 - Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)| / (1 + y ^ 2) := by
      dsimp [Kernel]
      rw [abs_div, abs_of_nonneg hden_pos.le]
    _ ≤ 2 / (1 + y ^ 2) := by
      exact div_le_div_of_nonneg_right hnum hden_pos.le
    _ = 2 * (1 + y ^ 2)⁻¹ := by rw [div_eq_mul_inv]

/-- `e^{-yT} (cos T + y sin T) → 0` for `y > 0`. -/
lemma exp_neg_mul_cos_sin_tendsto (y : ℝ) (hy : 0 < y) :
    Tendsto (fun T : ℝ => Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)) atTop (𝓝 0) := by
  have he0 : Tendsto (fun T : ℝ => Real.exp (-(y * T))) atTop (𝓝 0) := by
    have hyT : Tendsto (fun T : ℝ => y * T) atTop atTop := by
      simpa [mul_comm] using (Filter.Tendsto.atTop_mul_const (r := y) hy tendsto_id)
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hyT
  have hbnd : ∀ T, |Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)|
      ≤ (1 + y) * Real.exp (-(y * T)) := by
    intro T
    calc
      |Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)|
          = Real.exp (-(y * T)) * |Real.cos T + y * Real.sin T| := by
            rw [abs_mul, abs_of_nonneg (Real.exp_pos (-(y * T))).le]
      _ ≤ Real.exp (-(y * T)) * (1 + y) := by
            exact mul_le_mul_of_nonneg_left (abs_cos_add_mul_sin_le y T hy.le) (Real.exp_pos (-(y * T))).le
      _ = (1 + y) * Real.exp (-(y * T)) := by ring
  have hg0 : Tendsto (fun T : ℝ => (1 + y) * Real.exp (-(y * T))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul he0)
  have hz : Tendsto (fun T : ℝ => |Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)|) atTop (𝓝 0) := by
    exact squeeze_zero (fun T => abs_nonneg _) hbnd hg0
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa using hz

/-- Pointwise limit of the kernel: `Kernel T y → (1+y²)⁻¹` for `y > 0`. -/
lemma tendsto_kernel (y : ℝ) (hy : 0 < y) :
    Tendsto (fun T : ℝ => Kernel T y) atTop (𝓝 ((1 + y ^ 2)⁻¹)) := by
  have hprod := exp_neg_mul_cos_sin_tendsto y hy
  have hnum : Tendsto (fun T : ℝ => 1 - Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)) atTop (𝓝 1) := by
    simpa [sub_eq_add_neg] using tendsto_const_nhds.sub hprod
  have hk : Tendsto (fun T : ℝ => (1 - Real.exp (-(y * T)) * (Real.cos T + y * Real.sin T)) / (1 + y ^ 2))
      atTop (𝓝 (1 / (1 + y ^ 2))) := by
    exact hnum.div_const (1 + y ^ 2)
  simpa [Kernel, one_div] using hk

/-- The kernel integral tends to `π/2`. -/
lemma tendsto_kernel_integral :
    Tendsto (fun T : ℝ => ∫ y in Ioi (0 : ℝ), Kernel T y) atTop (𝓝 (Real.pi / 2)) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hdc : Tendsto (fun T : ℝ => ∫ y, Kernel T y ∂μ) atTop (𝓝 (∫ y, (1 + y ^ 2)⁻¹ ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
      (F := fun T : ℝ => fun y : ℝ => Kernel T y) (f := fun y : ℝ => (1 + y ^ 2)⁻¹)
      (bound := fun y : ℝ => 2 * (1 + y ^ 2)⁻¹) ?hF_meas ?h_bound ?bound_int ?h_lim
    · filter_upwards [] with T
      apply Continuous.aestronglyMeasurable
      have hc1 : Continuous (fun y : ℝ => Real.exp (-(y * T))) := by fun_prop
      have hc2 : Continuous (fun y : ℝ => Real.cos T + y * Real.sin T) := by fun_prop
      have hc3 : Continuous (fun y : ℝ => (1 + y ^ 2)⁻¹) := by
        apply Continuous.inv₀
        · fun_prop
        · intro y
          nlinarith [sq_nonneg y]
      dsimp [Kernel]
      exact hc1.mul hc2 |>.neg.const_add 1 |>.mul hc3
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      simpa using kernel_norm_bound T y hT hy.le
    · change IntegrableOn (fun y : ℝ => 2 * (1 + y ^ 2)⁻¹) (Ioi (0 : ℝ)) volume
      have h := (integrable_inv_one_add_sq.const_mul (2 : ℝ))
      exact h.integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact tendsto_kernel y hy
  have hval : (∫ y, (1 + y ^ 2)⁻¹ ∂μ) = Real.pi / 2 := by
    dsimp [μ]
    change ∫ y in Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ = Real.pi / 2
    simp
  simpa [μ, hval] using hdc

/-- Dirichlet integral: `lim_{T→∞} ∫_0^T sin(x)/x dx = π/2`. -/
theorem dirichlet_integral :
    Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin x / x) atTop (𝓝 (Real.pi / 2)) := by
  have hEq : (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin x / x) =ᶠ[atTop]
      (fun T : ℝ => ∫ y in Ioi (0 : ℝ), Kernel T y) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact dirichlet_eq_kernel T hT
  exact Filter.Tendsto.congr' hEq.symm tendsto_kernel_integral

end Commons.Analysis.Fourier
