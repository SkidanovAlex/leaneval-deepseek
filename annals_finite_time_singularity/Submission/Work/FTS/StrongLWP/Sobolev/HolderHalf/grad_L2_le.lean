import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.Blocks.IMC.cs_integral_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

open MeasureTheory

/-!
# The two-dimensional `L²`-gradient interpolation inequality

For a `C²` compactly supported function `v : ℝ × ℝ → ℝ` we prove

`∫ ‖fderiv ℝ v‖² ≤ 4 √(∫ v²) √(∫ ‖fderiv ℝ (fderiv ℝ v)‖²)`.

The proof has three ingredients.

* A norm computation on `ℝ × ℝ` (whose norm is the sup norm): for a linear functional `ℓ` the
  dual norm is bounded by the sum of the absolute values of its two coordinate values, whence
  `‖ℓ‖² ≤ (ℓ (1,1))² + (ℓ (1,-1))²`.
* Integration by parts in the two diagonal directions `(1,1)` and `(1,-1)`
  (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`): for `w = ∂_u v`,
  `∫ w² = -∫ (∂_u w) v ≤ |∫ (∂_u w) v|`.
* Cauchy–Schwarz (`Work.Blocks.IMC.cs_integral_mul_le`) and the pointwise bound
  `|∂_u w| ≤ ‖fderiv ℝ (fderiv ℝ v)‖` valid for `‖u‖ = 1`.
-/

/-- The square of a compactly supported real function has compact support. -/
private lemma hasCompactSupport_sq {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (fun x => f x ^ 2) := by
  have h : HasCompactSupport (f * f) := hf.mul_right (f' := f)
  rwa [show (f * f) = fun x => f x ^ 2 from by funext x; simp [Pi.mul_apply, sq]] at h

/-- The norm of a compactly supported function has compact support. -/
private lemma hasCompactSupport_norm {α : Type*} [TopologicalSpace α] {E : Type*}
    [NormedAddCommGroup E] {f : α → E} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => ‖f x‖) := hf.norm

/-- Rewriting the pointwise square as a product. -/
private lemma integrable_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (h : Integrable (fun x => f x * f x) μ) : Integrable (fun x => f x ^ 2) μ :=
  h.congr (Filter.Eventually.of_forall fun x => by simp [sq])

/-- `x ↦ f x ^ 2` is integrable for a continuous compactly supported `f`. -/
private lemma integrable_sq_of {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {f : α → ℝ} (hc : Continuous f) (hf : HasCompactSupport f) :
    Integrable (fun x => f x ^ 2) μ :=
  integrable_sq ((hc.mul hc).integrable_of_hasCompactSupport
    (by simpa only [Pi.mul_apply] using hf.mul_right (f' := f)))

/-- `x ↦ ‖f x‖ ^ 2` is integrable for a continuous compactly supported `f`. -/
private lemma integrable_norm_sq_of {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {E : Type*} [NormedAddCommGroup E] {f : α → E} (hc : Continuous f)
    (hf : HasCompactSupport f) : Integrable (fun x => ‖f x‖ ^ 2) μ :=
  integrable_sq ((hc.norm.mul hc.norm).integrable_of_hasCompactSupport
    (by simpa only [Pi.mul_apply] using
      (hasCompactSupport_norm hf).mul_right (f' := fun x => ‖f x‖)))

/-- The dual norm on `ℝ × ℝ` (with the sup norm) is bounded by the sum of the absolute values of
the two coordinate values. -/
private lemma norm_bound (ℓ : ℝ × ℝ →L[ℝ] ℝ) : ‖ℓ‖ ≤ |ℓ (1,0)| + |ℓ (0,1)| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  have h1 : y = y.1 • ((1:ℝ),0) + y.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  have hℓy : ℓ y = y.1 * ℓ (1,0) + y.2 * ℓ (0,1) := by
    conv_lhs => rw [h1]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hℓy, Real.norm_eq_abs]
  calc |y.1 * ℓ (1, 0) + y.2 * ℓ (0, 1)|
      ≤ |y.1 * ℓ (1, 0)| + |y.2 * ℓ (0, 1)| := abs_add_le _ _
    _ = |y.1| * |ℓ (1, 0)| + |y.2| * |ℓ (0, 1)| := by rw [abs_mul, abs_mul]
    _ ≤ ‖y‖ * |ℓ (1, 0)| + ‖y‖ * |ℓ (0, 1)| := by
        have h1 : |y.1| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using norm_fst_le y
        have h2 : |y.2| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using norm_snd_le y
        nlinarith [abs_nonneg (ℓ (1,0)), abs_nonneg (ℓ (0,1)), norm_nonneg y]
    _ = (|ℓ (1, 0)| + |ℓ (0, 1)|) * ‖y‖ := by ring

/-- Squaring: the `ℓ²`-norm of a linear functional on `ℝ × ℝ` is dominated by its values on the
two diagonal directions `(1,1)` and `(1,-1)`. -/
private lemma norm_sq_le_diag (ℓ : ℝ × ℝ →L[ℝ] ℝ) :
    ‖ℓ‖ ^ 2 ≤ (ℓ (1,1)) ^ 2 + (ℓ (1,-1)) ^ 2 := by
  have hb := norm_bound ℓ
  have h11 : ℓ (1,1) = ℓ (1,0) + ℓ (0,1) := by
    have : ((1:ℝ),(1:ℝ)) = ((1:ℝ),0) + ((0:ℝ),(1:ℝ)) := by ext <;> norm_num
    rw [this, map_add]
  have h1m : ℓ (1,-1) = ℓ (1,0) - ℓ (0,1) := by
    have : ((1:ℝ),(-1:ℝ)) = ((1:ℝ),0) - ((0:ℝ),(1:ℝ)) := by ext <;> norm_num
    rw [this, map_sub]
  rw [h11, h1m]
  calc ‖ℓ‖ ^ 2 ≤ (|ℓ (1,0)| + |ℓ (0,1)|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ ≤ (ℓ (1,0) + ℓ (0,1)) ^ 2 + (ℓ (1,0) - ℓ (0,1)) ^ 2 := by
        nlinarith [sq_nonneg (|ℓ (1,0)| - |ℓ (0,1)|), sq_abs (ℓ (1,0)), sq_abs (ℓ (0,1)),
          abs_nonneg (ℓ (1,0)), abs_nonneg (ℓ (0,1))]

/-- The directional `L²`-gradient bound: for a unit vector `u`,
`∫ ((fderiv ℝ v x) u)² ≤ √(∫ v²) √(∫ ‖fderiv ℝ (fderiv ℝ v)‖²)`. -/
private lemma grad_dir_le {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v)
    {u : ℝ × ℝ} (hu : ‖u‖ = 1) :
    ∫ x, ((fderiv ℝ v x) u) ^ 2 ≤ Real.sqrt (∫ x, (v x) ^ 2) *
      Real.sqrt (∫ x, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) := by
  set w : ℝ × ℝ → ℝ := fun x => (fderiv ℝ v x) u with hw
  have hwcd : ContDiff ℝ 1 w := by
    rw [hw]
    have h1 : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (fderiv ℝ v p.1) p.2) :=
      hv.contDiff_fderiv_apply (m := 1) (by norm_num)
    have h2 : ContDiff ℝ 1 (fun x : ℝ × ℝ => (x, u)) := by fun_prop
    exact h1.comp h2
  have hdfv : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hcw : HasCompactSupport w := hc.fderiv_apply ℝ u
  have hdw : Continuous (fun x => (fderiv ℝ w x) u) :=
    (hwcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdcw : HasCompactSupport (fun x => (fderiv ℝ w x) u) := hcw.fderiv_apply ℝ u
  have hdv : Continuous (fun x => (fderiv ℝ v x) u) :=
    (hv.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hA1 : Integrable (fun x => ((fderiv ℝ w x) u) ^ 2) :=
    integrable_sq_of (f := fun x => (fderiv ℝ w x) u) hdw hdcw
  have hA2 : Integrable (fun x => (v x) ^ 2) :=
    integrable_sq_of (f := v) hdfv.continuous hc
  have hI1 : Integrable (fun x => (fderiv ℝ w x) u * v x) := by
    refine (hdw.mul hdfv.continuous).integrable_of_hasCompactSupport ?_
    simpa only [Pi.mul_apply] using hdcw.mul_right (f' := v)
  have hI2 : Integrable (fun x => w x * (fderiv ℝ v x) u) := by
    refine (hwcd.continuous.mul hdv).integrable_of_hasCompactSupport ?_
    simpa only [Pi.mul_apply] using hcw.mul_right (f' := (fun x => (fderiv ℝ v x) u))
  have hI3 : Integrable (fun x => w x * v x) := by
    refine (hwcd.continuous.mul hdfv.continuous).integrable_of_hasCompactSupport ?_
    simpa only [Pi.mul_apply] using hcw.mul_right (f' := v)
  have hIBP : ∫ x, w x * (fderiv ℝ v x) u = -∫ x, (fderiv ℝ w x) u * v x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := w) (g := v) (v := u) hI1 hI2 hI3
      (fun x _ => hwcd.differentiable (by norm_num) x) (fun x _ => hdfv x)
  have hw2 : ∫ x, (w x) ^ 2 = ∫ x, w x * (fderiv ℝ v x) u := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [hw]
    ring
  have hchain : ∀ x, fderiv ℝ w x =
      (ContinuousLinearMap.apply ℝ ℝ u).comp (fderiv ℝ (fderiv ℝ v) x) := by
    intro x
    rw [hw]
    have hdf' : Differentiable ℝ (fderiv ℝ v) :=
      (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ ℝ u)).comp x
      ((hdf' x).hasFDerivAt)
    simpa [Function.comp_def] using h.fderiv
  have hbd : ∀ x, ‖(fderiv ℝ w x) u‖ ≤ ‖fderiv ℝ (fderiv ℝ v) x‖ := by
    intro x
    rw [hchain x]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    calc ‖(fderiv ℝ (fderiv ℝ v) x u) u‖
        ≤ ‖fderiv ℝ (fderiv ℝ v) x u‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ v) x‖ * ‖u‖) * ‖u‖ := by
          have h1 := ContinuousLinearMap.le_opNorm (fderiv ℝ (fderiv ℝ v) x) u
          nlinarith [norm_nonneg u, norm_nonneg (fderiv ℝ (fderiv ℝ v) x)]
      _ = ‖fderiv ℝ (fderiv ℝ v) x‖ := by rw [hu]; ring
  have hBcs : HasCompactSupport (fun x => fderiv ℝ (fderiv ℝ v) x) :=
    hc.of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_fderiv_subset (𝕜 := ℝ) (f := fderiv ℝ v)).trans
        (tsupport_fderiv_subset (𝕜 := ℝ) (f := v)))
  have hBc1 : Continuous (fun x => fderiv ℝ (fderiv ℝ v) x) :=
    (hv.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hA3 : Integrable (fun x => ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) :=
    integrable_norm_sq_of (f := fun x => fderiv ℝ (fderiv ℝ v) x) hBc1 hBcs
  have h2 : ∫ x, ((fderiv ℝ w x) u) ^ 2 ≤ ∫ x, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2 := by
    apply integral_mono hA1 hA3
    intro x
    have hx := pow_le_pow_left₀ (norm_nonneg ((fderiv ℝ w x) u)) (hbd x) 2
    rwa [Real.norm_eq_abs, sq_abs] at hx
  have hCS := Work.Blocks.IMC.cs_integral_mul_le volume (hdw.aestronglyMeasurable)
    (hdfv.continuous.aestronglyMeasurable) hA1 hA2
  calc ∫ x, ((fderiv ℝ v x) u) ^ 2
      = ∫ x, (w x) ^ 2 := by simp only [hw]
    _ = ∫ x, w x * (fderiv ℝ v x) u := hw2
    _ = -∫ x, (fderiv ℝ w x) u * v x := hIBP
    _ ≤ |∫ x, (fderiv ℝ w x) u * v x| := neg_le_abs _
    _ ≤ Real.sqrt (∫ x, ((fderiv ℝ w x) u) ^ 2) * Real.sqrt (∫ x, (v x) ^ 2) := hCS
    _ ≤ Real.sqrt (∫ x, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) * Real.sqrt (∫ x, (v x) ^ 2) := by
        apply mul_le_mul_of_nonneg_right
        · exact Real.sqrt_le_sqrt h2
        · exact Real.sqrt_nonneg _
    _ = Real.sqrt (∫ x, (v x) ^ 2) * Real.sqrt (∫ x, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) := by
        ring

theorem grad_L2_le {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v) :
    ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 2 ≤ 4 * Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
      * Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) := by
  have hvcf : Continuous (fun x : ℝ × ℝ => fderiv ℝ v x) := hv.continuous_fderiv (by norm_num)
  have hc11 : HasCompactSupport (fun x : ℝ × ℝ => (fderiv ℝ v x) ((1:ℝ),1)) :=
    hc.fderiv_apply ℝ ((1:ℝ),1)
  have hc1m : HasCompactSupport (fun x : ℝ × ℝ => (fderiv ℝ v x) ((1:ℝ),-1)) :=
    hc.fderiv_apply ℝ ((1:ℝ),-1)
  have hcd11 : Continuous (fun x : ℝ × ℝ => (fderiv ℝ v x) ((1:ℝ),1)) :=
    hvcf.clm_apply continuous_const
  have hcd1m : Continuous (fun x : ℝ × ℝ => (fderiv ℝ v x) ((1:ℝ),-1)) :=
    hvcf.clm_apply continuous_const
  have hf1 : Integrable (fun x : ℝ × ℝ => ((fderiv ℝ v x) ((1:ℝ),1)) ^ 2) :=
    integrable_sq_of (f := fun x : ℝ × ℝ => (fderiv ℝ v x) ((1:ℝ),1)) hcd11 hc11
  have hf2 : Integrable (fun x : ℝ × ℝ => ((fderiv ℝ v x) ((1:ℝ),-1)) ^ 2) :=
    integrable_sq_of (f := fun x : ℝ × ℝ => (fderiv ℝ v x) ((1:ℝ),-1)) hcd1m hc1m
  have hL : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 2) :=
    integrable_norm_sq_of (f := fderiv ℝ v) hvcf (hc.fderiv ℝ)
  have hpt : ∀ x : ℝ × ℝ,
      ‖fderiv ℝ v x‖ ^ 2 ≤ ((fderiv ℝ v x) ((1:ℝ),1)) ^ 2 + ((fderiv ℝ v x) ((1:ℝ),-1)) ^ 2 :=
    fun x => norm_sq_le_diag (fderiv ℝ v x)
  have h1 : ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 2 ≤
      ∫ x : ℝ × ℝ, (((fderiv ℝ v x) ((1:ℝ),1)) ^ 2 + ((fderiv ℝ v x) ((1:ℝ),-1)) ^ 2) :=
    integral_mono hL (hf1.add hf2) hpt
  rw [integral_add hf1 hf2] at h1
  have e1 := grad_dir_le hv hc (u := ((1:ℝ),1)) (by norm_num)
  have e2 := grad_dir_le hv hc (u := ((1:ℝ),-1)) (by norm_num)
  have hX : 0 ≤ Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) *
      Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 2
      ≤ (∫ x : ℝ × ℝ, ((fderiv ℝ v x) ((1:ℝ),1)) ^ 2) +
          ∫ x : ℝ × ℝ, ((fderiv ℝ v x) ((1:ℝ),-1)) ^ 2 := h1
    _ ≤ Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) *
            Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) +
          Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) *
            Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) := add_le_add e1 e2
    _ = 2 * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) *
            Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) := by ring
    _ ≤ 4 * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) *
            Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) := by
        nlinarith [hX]
    _ = 4 * Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
          * Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) := by ring

end Work.FTS.StrongLWP.Sobolev.HolderHalf
