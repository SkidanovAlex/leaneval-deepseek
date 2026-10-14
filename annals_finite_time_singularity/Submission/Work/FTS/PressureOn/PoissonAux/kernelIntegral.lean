import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Auxiliary.heatKernel_tail_le
import Submission.Work.FTS.PressureOn.Auxiliary.integral_mul_div_eq_neg_inner_gradient
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.Physical.Clock.clockInv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical

open PhysClock

/-! ## The inverse clock of `Clock.exists_inverse_clock` -/

/-- The inverse clock selected by `Work.FTS.Physical.Clock.exists_inverse_clock`: the (unique)
fake time `τ(t)` with `t(τ(t)) = t` for `t ∈ [0,T)`. -/
noncomputable def tauInv (C : PhysClock) : ℝ → ℝ :=
  (Work.FTS.Physical.Clock.exists_inverse_clock C).choose

/-- The defining properties of `tauInv`: the clock identity, nonnegativity, the clock comparison
`T - t ≤ 2A(τ(t))` and differentiability on the open interval `(0,T)`. -/
theorem tauInv_spec (C : PhysClock) :
    (∀ t ∈ Set.Ico 0 C.T, C.t (tauInv C t) = t) ∧
      (∀ t ∈ Set.Ico 0 C.T, 0 ≤ tauInv C t) ∧
      (∀ t ∈ Set.Ico 0 C.T, C.T - t ≤ 2 * C.A (tauInv C t)) ∧
      ∀ t ∈ Set.Ioo 0 C.T, HasDerivAt (tauInv C) ((C.A (tauInv C t))⁻¹) t :=
  (Work.FTS.Physical.Clock.exists_inverse_clock C).choose_spec

/-- `t(τ(t)) = t` for every physical time `t < T`. -/
theorem tauInv_clock (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    C.t (tauInv C t) = t :=
  (tauInv_spec C).1 t ht

/-- The inverse clock takes nonnegative values. -/
theorem tauInv_nonneg (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) : 0 ≤ tauInv C t :=
  (tauInv_spec C).2.1 t ht


/-- The inverse clock is differentiable on `(0,T)`, with derivative `1/A(τ(t))`. -/
theorem tauInv_hasDerivAt (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ioo 0 C.T) :
    HasDerivAt (tauInv C) ((C.A (tauInv C t))⁻¹) t :=
  (tauInv_spec C).2.2.2 t ht

/-- The inverse clock is *strictly* positive on `(0,T)`: if `τ(t) = 0` then `t = t(0) = 0`. -/
theorem tauInv_pos (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ioo 0 C.T) : 0 < tauInv C t := by
  have hmem : t ∈ Set.Ico 0 C.T := ⟨ht.1.le, ht.2⟩
  rcases lt_or_eq_of_le (tauInv_nonneg C hmem) with h | h
  · exact h
  · exfalso
    have h1 : C.t (tauInv C t) = 0 := by rw [← h]; exact PhysClock.t_zero C
    rw [tauInv_clock C hmem] at h1
    exact absurd h1 (ne_of_gt ht.1)

/-- `τ(t) → 0` as `t → 0⁺` (the inverse clock is continuous at `0` from the right). -/
theorem tauInv_tendsto_zero (C : PhysClock) :
    Tendsto (tauInv C) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT (Work.FTS.Physical.Clock.T_pos C)] with y hy
    have hmem : y ∈ Set.Ico 0 C.T := ⟨hy.1.le, hy.2⟩
    linarith [tauInv_nonneg C hmem, hb]
  · have hTb : 0 < C.t b := by
      have h := (Work.FTS.Physical.Clock.t_strictMonoOn C) (Set.mem_Ici.mpr le_rfl)
        (Set.mem_Ici.mpr hb.le) hb
      rwa [PhysClock.t_zero] at h
    filter_upwards [Ioo_mem_nhdsGT (lt_min hTb (Work.FTS.Physical.Clock.T_pos C))] with y hy
    have hy' : y ∈ Set.Ico 0 C.T := ⟨hy.1.le, lt_of_lt_of_le hy.2 (min_le_right _ _)⟩
    have hylt : y < C.t b := lt_of_lt_of_le hy.2 (min_le_left _ _)
    have hiff := (Work.FTS.Physical.Clock.t_strictMonoOn C).lt_iff_lt
      (Set.mem_Ici.mpr (tauInv_nonneg C hy'))
      (show b ∈ Set.Ici (0 : ℝ) from hb.le)
    rw [tauInv_clock C hy'] at hiff
    exact hiff.mp hylt

/-- `τ(t) > 0` eventually as `t → 0⁺`. -/
theorem eventually_tauInv_pos (C : PhysClock) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), tauInv C t ∈ Set.Ioi 0 := by
  filter_upwards [Ioo_mem_nhdsGT (Work.FTS.Physical.Clock.T_pos C)] with y hy
  exact tauInv_pos C hy

/-- **The inverse clock converges to `0` in `𝓝[>] 0`**: it maps right-neighbourhoods of `0` to
right-neighbourhoods of `0`.  This is what allows the slope limit of the clock to be composed
with the inverse clock. -/
theorem tauInv_tendsto_nhdsGT (C : PhysClock) :
    Tendsto (tauInv C) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨tauInv_tendsto_zero C, eventually_tauInv_pos C⟩

/-! ## The extended inverse clock -/

/-- **The extended inverse clock.**  The inverse clock `τ(·)` of the dynamic rescaling, continued
to the left of `0` by its tangent line `t ↦ t·A(0)⁻¹` at `0`.  The point of the extension is that
the resulting function has a genuine (two-sided) derivative `A(0)⁻¹` at `t = 0`, which the strip
transport `Work.FTS.Physical.bsAdmissibleStripFull_comp_clock` demands.

For `t ∈ [0,T)` the value is the true inverse clock; for `t ≥ T` the value is irrelevant (the
reconstruction never evaluates it there). -/
noncomputable def clockInv (C : PhysClock) (t : ℝ) : ℝ :=
  if t ≤ 0 then t * (C.A 0)⁻¹ else tauInv C t

theorem clockInv_of_nonpos {C : PhysClock} {t : ℝ} (h : t ≤ 0) :
    clockInv C t = t * (C.A 0)⁻¹ :=
  if_pos h

theorem clockInv_of_pos {C : PhysClock} {t : ℝ} (h : 0 < t) : clockInv C t = tauInv C t :=
  if_neg (not_le.mpr h)

@[simp] theorem clockInv_zero (C : PhysClock) : clockInv C 0 = 0 := by
  rw [clockInv_of_nonpos le_rfl, zero_mul]

/-- On `[0,T)` the extended clock is the true inverse clock: `t(τ(t)) = t`. -/
theorem clockInv_clock (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    C.t (clockInv C t) = t := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, clockInv_zero, PhysClock.t_zero]
  · rw [clockInv_of_pos h]; exact tauInv_clock C ht

/-- The extended clock is nonnegative on `[0,T)`. -/
theorem clockInv_nonneg (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    0 ≤ clockInv C t := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, clockInv_zero]
  · rw [clockInv_of_pos h]; exact tauInv_nonneg C ht


/-- The extended clock is strictly positive on `(0,T)`. -/
theorem clockInv_pos_of_pos (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ioo 0 C.T) :
    0 < clockInv C t := by
  rw [clockInv_of_pos ht.1]
  exact tauInv_pos C ht

/-- **The extended clock is monotone**: `t ≤ t'` implies `τ(t) ≤ τ(t')` on `[0,T)`. -/
theorem clockInv_mono (C : PhysClock) {t t' : ℝ} (ht : t ∈ Set.Ico 0 C.T)
    (ht' : t' ∈ Set.Ico 0 C.T) (htt' : t ≤ t') : clockInv C t ≤ clockInv C t' := by
  have h1 := clockInv_clock C ht
  have h2 := clockInv_clock C ht'
  by_contra hcon
  push_neg at hcon
  have hlt := (Work.FTS.Physical.Clock.t_strictMonoOn C (clockInv_nonneg C ht')
    (clockInv_nonneg C ht) hcon)
  rw [h2, h1] at hlt
  exact absurd hlt (not_lt.mpr htt')

/-- The extended clock is differentiable on `(0,T)`, with derivative `1/A(τ(t))`. -/
theorem clockInv_hasDerivAt (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ioo 0 C.T) :
    HasDerivAt (clockInv C) ((C.A (clockInv C t))⁻¹) t := by
  have heq : clockInv C =ᶠ[𝓝 t] tauInv C := by
    filter_upwards [isOpen_Ioi.mem_nhds ht.1] with s hs using clockInv_of_pos hs
  have hder : HasDerivAt (tauInv C) ((C.A (tauInv C t))⁻¹) t := tauInv_hasDerivAt C ht
  rw [clockInv_of_pos ht.1]
  exact hder.congr_of_eventuallyEq heq

/-! ## The derivative of the extended clock at `t = 0`

The left branch is the tangent line, so the left derivative is `A(0)⁻¹` outright; the right
derivative is the limit of the slopes `τ(t)/t = τ(t)/t(τ(t))`, which is `A(0)⁻¹` by the slope
limit of the clock (`Clock.clock_slope_tendsto`) composed with `τ(·) → 0⁺`
(`tauInv_tendsto_nhdsGT`). -/

/-- **The extended clock is differentiable at `0` with derivative `A(0)⁻¹`.**

This is the endpoint datum that makes the strip transport applicable: the natural inverse clock
has no derivative at `t = 0`, whereas the extension by the tangent line does.  The two one-sided
derivatives are computed separately and glued with `HasDerivWithinAt.union` along
`Iic 0 ∪ Ioi 0 = univ`. -/
theorem clockInv_hasDerivAt_zero (C : PhysClock) :
    HasDerivAt (clockInv C) ((C.A 0)⁻¹) 0 := by
  have hleft : HasDerivWithinAt (clockInv C) ((C.A 0)⁻¹) (Set.Iic 0) 0 := by
    have hlin : HasDerivWithinAt (fun s : ℝ => s * (C.A 0)⁻¹) ((C.A 0)⁻¹) (Set.Iic (0 : ℝ)) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).hasDerivWithinAt (s := Set.Iic (0 : ℝ))).mul_const
        ((C.A 0)⁻¹)
      simpa using h
    refine hlin.congr (fun y hy => ?_) ?_
    · rw [clockInv_of_nonpos hy]
    · rw [clockInv_of_nonpos le_rfl]
  have hright : HasDerivWithinAt (clockInv C) ((C.A 0)⁻¹) (Set.Ioi 0) 0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi 0)]
    have hslope : slope (clockInv C) 0 = fun y : ℝ => clockInv C y / y := by
      funext y
      rw [slope_fun_def_field]
      simp [clockInv_zero]
    rw [hslope]
    have hsl := (Work.FTS.Physical.Clock.clock_slope_tendsto C).2.comp (tauInv_tendsto_nhdsGT C)
    refine Filter.Tendsto.congr' ?_ hsl
    filter_upwards [Ioo_mem_nhdsGT (Work.FTS.Physical.Clock.T_pos C)] with y hy
    have hmem : y ∈ Set.Ico 0 C.T := ⟨hy.1.le, hy.2⟩
    rw [Function.comp_apply, tauInv_clock C hmem, clockInv_of_pos hy.1]
  have hglue : HasDerivWithinAt (clockInv C) ((C.A 0)⁻¹) (Set.Iic 0 ∪ Set.Ioi 0) 0 :=
    hleft.union hright
  rw [Set.Iic_union_Ioi] at hglue
  exact hasDerivWithinAt_univ.mp hglue


end Work.FTS.Physical
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.heatKernelShiftAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section


/-- **The translating chain rule for the Fréchet derivative.** -/
lemma fderiv_comp_sub_const (G : R3 → ℝ) (x y : R3) :
    fderiv ℝ (fun w : R3 => G (w - x)) y = fderiv ℝ G (y - x) :=
  fderiv_comp_sub x

/-- **The translating chain rule for gradients.**  `gradient` is unchanged by precomposing with
the translation `y' ↦ y' - x`. -/
lemma gradient_comp_sub_const (Φ : R3 → ℝ) (x y : R3) :
    gradient (fun y' : R3 => Φ (y' - x)) y = gradient Φ (y - x) := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, inner_gradient_left, fderiv_comp_sub_const Φ x y]

/-- **The translating chain rule for the Laplace trace.**  `laplaceTrace` is unchanged by
precomposing with the translation `y' ↦ y' - x`. -/
lemma laplaceTrace_comp_sub_const (Φ : R3 → ℝ) (x y : R3) :
    laplaceTrace (fun y' : R3 => Φ (y' - x)) y = laplaceTrace Φ (y - x) := by
  rw [Work.FTS.PressureOn.laplaceTrace, Work.FTS.PressureOn.laplaceTrace]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun w : R3 => fderiv ℝ (fun y' : R3 => Φ (y' - x)) w (FiniteTimeSingularity.e i))
      = (fun w : R3 => fderiv ℝ Φ (w - x) (FiniteTimeSingularity.e i)) := by
    funext w
    rw [fderiv_comp_sub_const Φ x w]
  rw [h1]
  rw [show (fun w : R3 => fderiv ℝ Φ (w - x) (FiniteTimeSingularity.e i))
      = (fun w : R3 => (fun z : R3 => fderiv ℝ Φ z (FiniteTimeSingularity.e i))
          (w - x)) from rfl]
  rw [fderiv_comp_sub_const (fun z : R3 => fderiv ℝ Φ z (FiniteTimeSingularity.e i)) x y]

/-- The gradient of a function of `‖·‖²`: `∇ (F ∘ ‖·‖²) z = 2F'(‖z‖²) • z`. -/
lemma gradient_comp_normSq_eq (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (z : R3) :
    gradient (fun x : R3 => F (‖x‖ ^ 2)) z = (2 * deriv F (‖z‖ ^ 2)) • z := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, gradient_comp_normSq F hF z]
  simp only [smul_apply, innerSL_apply_apply, real_inner_smul_left, smul_eq_mul]

/-- The norm of the gradient is the operator norm of the derivative. -/
lemma norm_gradient_eq_norm_fderiv (f : R3 → ℝ) (y : R3) :
    ‖gradient f y‖ = ‖fderiv ℝ f y‖ := by
  rw [gradient]
  exact LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ R3).symm (fderiv ℝ f y)


/-! ## Derivatives and integrability of the shifted heat kernel -/

/-- The derivative of `s ↦ exp (-(c s))`. -/
lemma deriv_exp_neg_mul (c s : ℝ) :
    deriv (fun s : ℝ => Real.exp (-(c * s))) s = -c * Real.exp (-(c * s)) := by
  have hfun : (fun s : ℝ => -(c * s)) = fun s : ℝ => (-c) * s := by
    funext t
    ring
  have hd2 : DifferentiableAt ℝ (fun s : ℝ => -(c * s)) s := by
    rw [hfun]
    fun_prop
  have hcomp : deriv (fun s : ℝ => Real.exp (-(c * s))) s
      = deriv Real.exp (-(c * s)) * deriv (fun s : ℝ => -(c * s)) s := by
    have h := deriv_comp (𝕜 := ℝ) (𝕜' := ℝ) s (h := fun s : ℝ => -(c * s)) (h₂ := Real.exp)
      Real.differentiable_exp.differentiableAt hd2
    simpa only [Function.comp_def] using h
  rw [hcomp, Real.deriv_exp, hfun, deriv_const_mul_id]
  ring

lemma deriv_expProfile (A c s : ℝ) :
    deriv (fun s : ℝ => A * Real.exp (-(c * s))) s = -(A * c) * Real.exp (-(c * s)) := by
  have hd : DifferentiableAt ℝ (fun s : ℝ => Real.exp (-(c * s))) s := by fun_prop
  rw [deriv_const_mul A hd, deriv_exp_neg_mul]
  ring

lemma deriv_deriv_expProfile (A c s : ℝ) :
    deriv (deriv (fun s : ℝ => A * Real.exp (-(c * s)))) s
      = (A * c ^ 2) * Real.exp (-(c * s)) := by
  rw [show deriv (fun s : ℝ => A * Real.exp (-(c * s)))
        = fun s : ℝ => -(A * c) * Real.exp (-(c * s)) from funext (deriv_expProfile A c)]
  have hd : DifferentiableAt ℝ (fun s : ℝ => Real.exp (-(c * s))) s := by fun_prop
  rw [deriv_const_mul (-(A * c)) hd, deriv_exp_neg_mul]
  ring

lemma contDiff_expProfile (A c : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (fun s : ℝ => A * Real.exp (-(c * s))) := by
  have h1 : ContDiff ℝ n (fun s : ℝ => -(c * s)) :=
    ((contDiff_const (𝕜 := ℝ) (c := c)).mul contDiff_id).neg
  exact ((contDiff_const (𝕜 := ℝ) (c := A)).mul (Real.contDiff_exp.comp h1))

lemma contDiff_heatKernel (t : ℝ) (ht : 0 < t) (n : ℕ∞) :
    ContDiff ℝ n (heatKernel t) := by
  have h : heatKernel t = fun z : R3 => (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-((4 * t)⁻¹ * s))) (‖z‖ ^ 2) := by
    funext z
    rw [heatKernel_eq_const_mul_exp ht]
  rw [h]
  exact (contDiff_expProfile _ _ n).comp (contDiff_norm_sq ℝ)

lemma contDiff_heatKernel_comp_sub (t : ℝ) (ht : 0 < t) (x : R3) (n : ℕ∞) :
    ContDiff ℝ n (fun y' : R3 => heatKernel t (x - y')) :=
  (contDiff_heatKernel t ht n).comp (contDiff_const.sub contDiff_id)

/-- The heat kernel, shifted: `γ_t (x - y) = A exp (-(c ‖y - x‖²))`. -/
lemma heatKernel_shift_eq (t : ℝ) (ht : 0 < t) (x y : R3) :
    heatKernel t (x - y) = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) := by
  rw [heatKernel_eq_const_mul_exp ht, norm_sub_rev]

/-- **The Laplace trace of the shifted heat kernel.** -/
lemma laplaceTrace_heatKernel_shift (t : ℝ) (ht : 0 < t) (x y : R3) :
    laplaceTrace (fun y' : R3 => heatKernel t (x - y')) y
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          ((4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 - 6 * (4 * t)⁻¹) *
            Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2))) := by
  have hpoint : (fun y' : R3 => heatKernel t (x - y'))
      = fun y' : R3 => (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-((4 * t)⁻¹ * s))) (‖y' - x‖ ^ 2) := by
    funext y'
    rw [heatKernel_shift_eq t ht x y']
  rw [hpoint, laplaceTrace_comp_sub_const
    (fun z : R3 => (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-((4 * t)⁻¹ * s))) (‖z‖ ^ 2)) x y]
  rw [Work.FTS.PressureOn.PoissonAux.laplaceTrace_normSq
    (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-((4 * t)⁻¹ * s)))
    (contDiff_expProfile _ _ 2) (y - x)]
  rw [deriv_expProfile _ _ (‖y - x‖ ^ 2), deriv_deriv_expProfile _ _ (‖y - x‖ ^ 2)]
  ring

/-- **The gradient of the shifted heat kernel.** -/
lemma gradient_heatKernel_shift (t : ℝ) (ht : 0 < t) (x y : R3) :
    gradient (fun y' : R3 => heatKernel t (x - y')) y
      = -(((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹) *
          Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2))) • (y - x)) := by
  have hpoint : (fun y' : R3 => heatKernel t (x - y'))
      = fun y' : R3 => (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-((4 * t)⁻¹ * s))) (‖y' - x‖ ^ 2) := by
    funext y'
    rw [heatKernel_shift_eq t ht x y']
  rw [hpoint, gradient_comp_sub_const
    (fun z : R3 => (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-((4 * t)⁻¹ * s))) (‖z‖ ^ 2)) x y,
    gradient_comp_normSq_eq (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-((4 * t)⁻¹ * s))) (contDiff_expProfile _ _ 1) (y - x),
    deriv_expProfile _ _ (‖y - x‖ ^ 2)]
  rw [← neg_smul]
  congr 1
  ring

lemma integrable_heatKernel_shift (t : ℝ) (ht : 0 < t) (x : R3) :
    Integrable (fun y : R3 => heatKernel t (x - y)) := by
  have hc : (0 : ℝ) < (4 * t)⁻¹ := by positivity
  have hbase : Integrable (fun y : R3 =>
      ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) + 0 * ‖y - x‖ ^ 2) *
        Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2))) :=
    gaussShift.integrable_poly_exp_neg_normSq_sub _ 0 _ (by positivity) le_rfl hc x
  refine hbase.congr (Eventually.of_forall fun y => ?_)
  show ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) + 0 * ‖y - x‖ ^ 2) *
      Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) = heatKernel t (x - y)
  rw [heatKernel_shift_eq t ht x y]
  ring

lemma integrable_laplaceTrace_heatKernel_shift (t : ℝ) (ht : 0 < t) (x : R3) :
    Integrable (fun y : R3 => laplaceTrace (fun y' : R3 => heatKernel t (x - y')) y) := by
  have hcpos : (0 : ℝ) < (4 * t)⁻¹ := by positivity
  have hApos : (0 : ℝ) < (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by positivity
  have hbound := gaussShift.integrable_poly_exp_neg_normSq_sub
    ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (6 * (4 * t)⁻¹))
    ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (4 * ((4 * t)⁻¹) ^ 2)) (4 * t)⁻¹
    (by positivity) (by positivity) hcpos x
  refine Integrable.mono' hbound ?_ ?_
  · exact (Green.continuous_laplaceTrace _
      (contDiff_heatKernel_comp_sub t ht x 2)).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, laplaceTrace_heatKernel_shift t ht x y]
    have hexp : 0 < Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) := Real.exp_pos _
    have h1 : |4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 - 6 * (4 * t)⁻¹|
        ≤ 4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 + 6 * (4 * t)⁻¹ := by
      rw [abs_le]
      constructor <;> nlinarith [hcpos, sq_nonneg (‖y - x‖), sq_nonneg (4 * t)⁻¹]
    rw [abs_mul, abs_mul, abs_of_pos hApos, abs_of_pos hexp]
    have hAe : (0 : ℝ) ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := le_of_lt hApos
    have hkey : |4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 - 6 * (4 * t)⁻¹|
          * Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2))
        ≤ (4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 + 6 * (4 * t)⁻¹)
          * Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hexp)
    have h4 : (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          (|4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 - 6 * (4 * t)⁻¹|
            * Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)))
        ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          ((4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 + 6 * (4 * t)⁻¹)
            * Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left hkey hAe
    refine le_trans h4 (le_of_eq ?_)
    ring

lemma integrable_gradient_heatKernel_shift (t : ℝ) (ht : 0 < t) (x : R3) :
    Integrable (fun y : R3 => ‖gradient (fun y' : R3 => heatKernel t (x - y')) y‖) := by
  have hcpos : (0 : ℝ) < (4 * t)⁻¹ := by positivity
  have hApos : (0 : ℝ) < (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by positivity
  have hbound := gaussShift.integrable_poly_exp_neg_normSq_sub
    ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹))
    ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹)) (4 * t)⁻¹
    (by positivity) (by positivity) hcpos x
  refine Integrable.mono' hbound ?_ ?_
  · exact (Green.contDiff_gradient _
      (contDiff_heatKernel_comp_sub t ht x 2)).continuous.norm.aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [gradient_heatKernel_shift t ht x y, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
        (2 * (4 * t)⁻¹) * Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)))]
    have h1 : ‖y - x‖ ≤ 1 + ‖y - x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖y - x‖ - 1), norm_nonneg (y - x)]
    have h2 : (0 : ℝ) ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹) *
        Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) := by positivity
    calc (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹) *
            Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) * ‖y - x‖
        ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹) *
            Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) * (1 + ‖y - x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹)
            + (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹) * ‖y - x‖ ^ 2)
            * Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) := by
          ring

end

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.integral_abs_heatKernel_sub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `L¹` modulus of continuity of the heat kernel on `ℝ³`

`‖γ_t(· - h) - γ_t(·)‖_{L¹(ℝ³)} ≤ 4 ‖h‖ / √t`, where `γ_t` is the heat kernel
`γ_t z = (4πt)^{-3/2} exp (-‖z‖²/(4t))`.

## Proof

Write `c = (4πt)^{-3/2}`, so that `γ_t z = c · exp (-‖z‖²/(4t))` and `γ_t` is smooth with
`∇γ_t z = -γ_t z · z/(2t)`; hence the directional derivative of `s ↦ γ_t (z - s • h)` is
`γ_t (z - s • h) · ⟪z - s • h, h⟫ / (2t)`, whose absolute value is at most
`(‖h‖/(2t)) · ‖z - s • h‖ · γ_t (z - s • h) =: φ (z, s) ≥ 0`.

By the fundamental theorem of calculus and the triangle inequality for the integral,

  `|γ_t (z - h) - γ_t z| ≤ ∫_0^1 φ (z, s) ds   (z ∈ ℝ³)`,

and integrating over `z` against the Lebesgue measure reduces (by the shear-averaging identity
`ihak_interval_shift_mean`, i.e. Fubini plus translation invariance) to

  `∫_z |γ_t (z - h) - γ_t z| ≤ (‖h‖/(2t)) ∫_w ‖w‖ γ_t w dw`.

The last integral is bounded with the elementary Gaussian pointwise inequality
`r exp(-r²/(4t)) ≤ 2√t exp(-r²/(8t))` (`ihak_r_exp_gauss_le`), which gives

  `∫_w ‖w‖ γ_t w dw ≤ c · 2√t · ∫_w exp(-(‖w‖²/(8t))) dw = c · 2√t · (8πt)^{3/2} = 4√2 √t`,

and `(‖h‖/(2t)) · 4√2 √t = 2√2 ‖h‖/√t ≤ 4 ‖h‖/√t`. -/

open MeasureTheory
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

theorem integral_abs_heatKernel_sub_le (h : Work.FTS.PressureOn.R3) (t : ℝ) (ht : 0 < t) :
    ∫ z : Work.FTS.PressureOn.R3,
        |Work.FTS.PressureOn.Auxiliary.heatKernel t (z - h) - Work.FTS.PressureOn.Auxiliary.heatKernel t z|
      ≤ 4 * ‖h‖ / Real.sqrt t := by
  -- ## Constants
  set c : ℝ := (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) with hc_def
  have hcpos : 0 < c := by
    rw [hc_def]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hsqrtpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hγnn : ∀ w : R3, 0 ≤ heatKernel t w := fun w => heatKernel_nonneg ht.le w
  -- ## Differentiability of `γ_t` in the space variable
  have hγcont : Continuous (fun w : R3 => heatKernel t w) := by
    unfold heatKernel
    fun_prop
  have hcurve : ∀ z : R3, Continuous (fun s : ℝ => z - s • h) := fun z =>
    continuous_const.sub (continuous_id.smul continuous_const)
  have hcont_deriv : ∀ z : R3, Continuous (fun s : ℝ =>
      heatKernel t (z - s • h) * (inner ℝ (z - s • h) h) / (2 * t)) := fun z =>
    (((hγcont.comp (hcurve z)).mul ((hcurve z).inner continuous_const))).div_const _
  have hderiv : ∀ (z : R3) (s : ℝ), HasDerivAt (fun r : ℝ => heatKernel t (z - r • h))
      (heatKernel t (z - s • h) * (inner ℝ (z - s • h) h) / (2 * t)) s :=
    fun z s => ihak_hasDerivAt_heatKernel_sub_smul t ht z h s
  -- ## The pointwise fundamental-theorem-of-calculus bound
  have hFTC : ∀ z : R3,
      (∫ s in (0 : ℝ)..1, heatKernel t (z - s • h) * (inner ℝ (z - s • h) h) / (2 * t))
        = heatKernel t (z - h) - heatKernel t z := by
    intro z
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun r : ℝ => heatKernel t (z - r • h))
      (f' := fun s : ℝ => heatKernel t (z - s • h) * (inner ℝ (z - s • h) h) / (2 * t))
      (fun s _ => hderiv z s) ((hcont_deriv z).intervalIntegrable 0 1)
    simpa using h
  have hφ : ∀ z : R3, |heatKernel t (z - h) - heatKernel t z|
      ≤ ∫ s in (0 : ℝ)..1, ‖h‖ / (2 * t) * (‖z - s • h‖ * heatKernel t (z - s • h)) := by
    intro z
    rw [← hFTC z]
    refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      ((hcont_deriv z).abs.intervalIntegrable 0 1) ?_ (fun s _ => ?_)
    · exact ((continuous_const.mul ((continuous_norm.comp (hcurve z)).mul
        (hγcont.comp (hcurve z)))).intervalIntegrable 0 1)
    · have hw : 0 ≤ heatKernel t (z - s • h) := hγnn _
      have h2t : 0 < 2 * t := by positivity
      calc |heatKernel t (z - s • h) * inner ℝ (z - s • h) h / (2 * t)|
          = heatKernel t (z - s • h) * |inner ℝ (z - s • h) h| / (2 * t) := by
            rw [abs_div, abs_mul, abs_of_nonneg hw, abs_of_pos h2t]
        _ ≤ heatKernel t (z - s • h) * (‖z - s • h‖ * ‖h‖) / (2 * t) := by
            gcongr
            exact abs_real_inner_le_norm _ _
        _ = ‖h‖ / (2 * t) * (‖z - s • h‖ * heatKernel t (z - s • h)) := by ring
  have hφ' : ∀ z : R3, |heatKernel t (z - h) - heatKernel t z|
      ≤ ‖h‖ / (2 * t) * (∫ s in (0 : ℝ)..1, ‖z - s • h‖ * heatKernel t (z - s • h)) := by
    intro z
    simpa only [intervalIntegral.integral_const_mul] using hφ z
  -- ## The shear-averaging identity for `w ↦ ‖w‖ γ_t w`
  have hg0cont : Continuous (fun w : R3 => ‖w‖ * heatKernel t w) :=
    continuous_norm.mul hγcont
  have hg0bound : ∀ w : R3, |‖w‖ * heatKernel t w|
      ≤ (c * (2 * Real.sqrt t)) * Real.exp (-((1 / (8 * t)) * ‖w‖ ^ 2)) := by
    intro w
    have hw : 0 ≤ ‖w‖ := norm_nonneg w
    have hgnn : 0 ≤ heatKernel t w := hγnn w
    have h1 := ihak_r_exp_gauss_le t ‖w‖ ht hw
    have h2 : |‖w‖ * heatKernel t w|
        = c * (‖w‖ * Real.exp (-(‖w‖ ^ 2 / (4 * t)))) := by
      rw [abs_of_nonneg (mul_nonneg hw hgnn), hc_def]
      unfold heatKernel
      ring
    rw [h2]
    calc c * (‖w‖ * Real.exp (-(‖w‖ ^ 2 / (4 * t))))
        ≤ c * (2 * Real.sqrt t * Real.exp (-(‖w‖ ^ 2 / (8 * t)))) :=
          mul_le_mul_of_nonneg_left h1 hcpos.le
      _ = (c * (2 * Real.sqrt t)) * Real.exp (-((1 / (8 * t)) * ‖w‖ ^ 2)) := by
          rw [show -(‖w‖ ^ 2 / (8 * t)) = -((1 / (8 * t)) * ‖w‖ ^ 2) by ring]
          ring
  have hgaussint : Integrable
      (fun w : R3 => (c * (2 * Real.sqrt t)) * Real.exp (-((1 / (8 * t)) * ‖w‖ ^ 2))) volume :=
    (ihak_integrable_rexp_normSq (1 / (8 * t)) (by positivity)).const_mul _
  have hg0int : Integrable (fun w : R3 => ‖w‖ * heatKernel t w) volume := by
    refine hgaussint.mono' hg0cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => ?_)
    exact hg0bound w
  obtain ⟨hIntAvg, hAvgVal⟩ := ihak_interval_shift_mean hg0cont (c * (2 * Real.sqrt t))
    (1 / (8 * t)) (by positivity) (by positivity) hg0bound h
  -- ## Monotonicity of the outer integral
  have hInt2 : Integrable (fun z : R3 =>
      ‖h‖ / (2 * t) * (∫ s in (0 : ℝ)..1, ‖z - s • h‖ * heatKernel t (z - s • h))) volume :=
    hIntAvg.const_mul _
  have step1 : ∫ z : R3, |heatKernel t (z - h) - heatKernel t z|
      ≤ ‖h‖ / (2 * t) * ∫ z : R3,
          (∫ s in (0 : ℝ)..1, ‖z - s • h‖ * heatKernel t (z - s • h)) := by
    have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _) hInt2
      (Filter.Eventually.of_forall fun z => hφ' z)
    rwa [MeasureTheory.integral_const_mul] at h
  -- ## Evaluation of the averaged integral and of the Gaussian integral
  have step2 : ‖h‖ / (2 * t) * (∫ z : R3,
        (∫ s in (0 : ℝ)..1, ‖z - s • h‖ * heatKernel t (z - s • h)))
      ≤ ‖h‖ / (2 * t) * (∫ z : R3, ‖z‖ * heatKernel t z) :=
    mul_le_mul_of_nonneg_left (le_of_eq hAvgVal) (by positivity)
  have hg0le : ∀ w : R3, ‖w‖ * heatKernel t w
      ≤ (c * (2 * Real.sqrt t)) * Real.exp (-((1 / (8 * t)) * ‖w‖ ^ 2)) := fun w =>
    le_of_abs_le (hg0bound w)
  have step3 : ∫ z : R3, ‖z‖ * heatKernel t z
      ≤ (c * (2 * Real.sqrt t)) * (Real.pi / (1 / (8 * t))) ^ ((3 : ℝ) / 2) := by
    have hEq : ∫ z : R3, (c * (2 * Real.sqrt t)) * Real.exp (-((1 / (8 * t)) * ‖z‖ ^ 2))
        = (c * (2 * Real.sqrt t)) * (Real.pi / (1 / (8 * t))) ^ ((3 : ℝ) / 2) := by
      rw [MeasureTheory.integral_const_mul,
        ihak_integral_rexp_normSq (1 / (8 * t)) (by positivity)]
    rw [← hEq]
    exact integral_mono hg0int hgaussint (fun w => hg0le w)
  -- ## The final arithmetic
  have hfinal : ‖h‖ / (2 * t) * ((c * (2 * Real.sqrt t)) * (Real.pi / (1 / (8 * t))) ^
        ((3 : ℝ) / 2)) ≤ 4 * ‖h‖ / Real.sqrt t := by
    have hA : (0 : ℝ) < 4 * Real.pi * t := by positivity
    have hpidiv : Real.pi / (1 / (8 * t)) = 8 * Real.pi * t := by
      rw [div_eq_mul_inv, inv_div]
      ring
    rw [hpidiv]
    have hA32 : (4 * Real.pi * t) ^ ((3 : ℝ) / 2) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hA _)
    have hcube : c * (8 * Real.pi * t) ^ ((3 : ℝ) / 2) = 2 * Real.sqrt 2 := by
      have h1 : c * (8 * Real.pi * t) ^ ((3 : ℝ) / 2)
          = ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹
            * (2 ^ ((3 : ℝ) / 2) * (4 * Real.pi * t) ^ ((3 : ℝ) / 2)) := by
        rw [hc_def, show (8 : ℝ) * Real.pi * t = 2 * (4 * Real.pi * t) by ring,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hA.le, Real.rpow_neg hA.le]
      have h2 : (2 : ℝ) ^ ((3 : ℝ) / 2) = 2 * Real.sqrt 2 := by
        rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, ← Real.sqrt_eq_rpow]
      calc c * (8 * Real.pi * t) ^ ((3 : ℝ) / 2)
          = ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹
            * (2 ^ ((3 : ℝ) / 2) * (4 * Real.pi * t) ^ ((3 : ℝ) / 2)) := h1
        _ = 2 ^ ((3 : ℝ) / 2) := by
            rw [mul_comm (((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹)
              (2 ^ ((3 : ℝ) / 2) * (4 * Real.pi * t) ^ ((3 : ℝ) / 2)), mul_assoc,
              mul_inv_cancel₀ hA32, mul_one]
        _ = 2 * Real.sqrt 2 := h2
    have hcombine : ‖h‖ / (2 * t) * (2 * Real.sqrt t) = ‖h‖ / Real.sqrt t := by
      have h1 : ‖h‖ / (2 * t) * (2 * Real.sqrt t) = ‖h‖ * Real.sqrt t / t := by ring
      rw [h1, div_eq_div_iff (ne_of_gt ht) (ne_of_gt hsqrtpos), mul_assoc, hsq]
    have h22 : 2 * Real.sqrt 2 ≤ 4 := by
      have h2 : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      linarith
    calc ‖h‖ / (2 * t) * ((c * (2 * Real.sqrt t)) * (8 * Real.pi * t) ^ ((3 : ℝ) / 2))
        = (‖h‖ / (2 * t) * (2 * Real.sqrt t)) * (c * (8 * Real.pi * t) ^ ((3 : ℝ) / 2)) := by
          ring
      _ = (‖h‖ / Real.sqrt t) * (2 * Real.sqrt 2) := by rw [hcombine, hcube]
      _ = (2 * Real.sqrt 2) * (‖h‖ / Real.sqrt t) := by ring
      _ ≤ 4 * (‖h‖ / Real.sqrt t) :=
          mul_le_mul_of_nonneg_right h22 (by positivity)
      _ = 4 * ‖h‖ / Real.sqrt t := by ring
  exact step1.trans (step2.trans ((mul_le_mul_of_nonneg_left step3 (by positivity)).trans hfinal))

end

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.integral_inner_laplaceTraceVec_comm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity MeasureTheory

namespace Work.FTS.PressureOn.Auxiliary

open Work.FTS.PressureOn.Green

/-- For real numbers the inner product is the product. -/
private lemma inner_real_coord (a b : ℝ) : inner ℝ a b = a * b := by
  rw [RCLike.inner_apply]; simp; ring

theorem integral_inner_laplaceTraceVec_comm (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hV : ∀ n : ℕ, ContDiff ℝ n V) (hW : ∀ n : ℕ, ContDiff ℝ n W)
    (hWc : HasCompactSupport W) :
    ∫ x, inner ℝ (V x) (Work.FTS.PressureOn.laplaceTraceVec W x)
      = ∫ x, inner ℝ (Work.FTS.PressureOn.laplaceTraceVec V x) (W x) := by
  -- the two pointwise coordinate expansions of the inner products
  have hptL : ∀ x, inner ℝ (V x) (Work.FTS.PressureOn.laplaceTraceVec W x)
      = ∑ j : Fin 3, (V x) j * Work.FTS.PressureOn.laplaceTrace (fun y => (W y) j) x := by
    intro x
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IgslvAux.laplaceTraceVec_coord W (hW 2) x j, inner_real_coord]
  have hptR : ∀ x, inner ℝ (Work.FTS.PressureOn.laplaceTraceVec V x) (W x)
      = ∑ j : Fin 3, Work.FTS.PressureOn.laplaceTrace (fun y => (V y) j) x * (W x) j := by
    intro x
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IgslvAux.laplaceTraceVec_coord V (hV 2) x j, inner_real_coord]
  -- integrability of the coordinate summands
  have hintL : ∀ j : Fin 3, Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (V x) j * Work.FTS.PressureOn.laplaceTrace (fun y => (W y) j) x) :=
    fun j => (integrable_inner_laplaceTraceVec_coord V W hV hW hWc j).1
  have hintR : ∀ j : Fin 3, Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      Work.FTS.PressureOn.laplaceTrace (fun y => (V y) j) x * (W x) j) :=
    fun j => (integrable_inner_laplaceTraceVec_coord V W hV hW hWc j).2
  calc ∫ x, inner ℝ (V x) (Work.FTS.PressureOn.laplaceTraceVec W x)
      = ∫ x, ∑ j : Fin 3,
          (V x) j * Work.FTS.PressureOn.laplaceTrace (fun y => (W y) j) x := by
        rw [funext hptL]
    _ = ∑ j : Fin 3, ∫ x,
          (V x) j * Work.FTS.PressureOn.laplaceTrace (fun y => (W y) j) x := by
        simpa using integral_finsetSum Finset.univ (fun j _ => hintL j)
    _ = ∑ j : Fin 3, ∫ x,
          Work.FTS.PressureOn.laplaceTrace (fun y => (V y) j) x * (W x) j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm (fun y => (V y) j)
          (fun y => (W y) j) (IgslvAux.contDiff_coord V (hV 2) j)
          (IgslvAux.contDiff_coord W (hW 2) j) (IgslvAux.hasCompactSupport_coord W hWc j)
    _ = ∫ x, ∑ j : Fin 3,
          Work.FTS.PressureOn.laplaceTrace (fun y => (V y) j) x * (W x) j := by
        simpa using (integral_finsetSum Finset.univ (fun j _ => hintR j)).symm
    _ = ∫ x, inner ℝ (Work.FTS.PressureOn.laplaceTraceVec V x) (W x) := by
        rw [funext (fun x => (hptR x).symm)]

end Work.FTS.PressureOn.Auxiliary
end
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.tendsto_integral_heatKernel_smul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The heat kernel on `ℝ³` is an approximate identity at `t → 0⁺`

For a continuous bounded `u : ℝ³ → ℝ` and every `x`,

  `∫ y, u (x - y) * γ_t y → u x`  as `t → 0⁺`,

where `γ_t z = (4πt)^{-3/2} exp (-‖z‖²/(4t))` is the heat kernel
(`Work.FTS.PressureOn.Auxiliary.heatKernel`).

The proof is the textbook `ε/δ` argument for an approximate identity, in the form needed for a
merely *bounded* (not necessarily integrable) `u`:

* the kernel is a probability density, `∫ γ_t = 1` and `γ_t ∈ L¹`
  (`Work.FTS.PressureOn.Auxiliary.heatKernel_integral_one`);
* its mass outside the ball of radius `δ` decays like `2^{3/2} exp (-δ²/(8t))`
  (`Work.FTS.PressureOn.Auxiliary.heatKernel_tail_le`);
* by continuity of `u` at `x`, `u (x - y)` is close to `u x` for `‖y‖ < δ` and `γ_t` has total
  mass `1`, so the inner part contributes at most `ε/4`; the outer part is bounded by
  `2‖u‖_∞ · (tail mass)`, which is `< ε/4` for `t` small enough.
-/

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

theorem tendsto_integral_heatKernel_smul (u : Work.FTS.PressureOn.R3 → ℝ) (hu : Continuous u)
    (hbdd : ∃ C, ∀ x, |u x| ≤ C) (x : Work.FTS.PressureOn.R3) :
    Filter.Tendsto (fun t : ℝ =>
        ∫ y, u (x - y) * Work.FTS.PressureOn.Auxiliary.heatKernel t y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (u x)) := by
  obtain ⟨C, hC⟩ := hbdd
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (u x)) (hC x)
  -- `A` is the constant multiplying the tail mass in the outer estimate.
  set A : ℝ := 2 * C * 2 ^ (3 / 2 : ℝ) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h4 : 0 < ε / 4 := by linarith
  -- Continuity of `u` at `x`, transported to the shifted variable `x - y`.
  have hcontAt : ContinuousAt u x := hu.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.continuousAt_iff.mp hcontAt) (ε / 4) h4
  have hδ' : ∀ y : R3, ‖y‖ < δ → |u (x - y) - u x| < ε / 4 := by
    intro y hy
    have hdist : dist (x - y) x < δ := by
      rw [dist_eq_norm]
      have hxy : x - y - x = -y := by abel
      rw [hxy, norm_neg]
      exact hy
    have hd : dist (u (x - y)) (u x) < ε / 4 := hδ hdist
    rwa [Real.dist_eq] at hd
  -- The tolerance for the tail mass: `A * ε' ≤ ε/4`.
  set ε' : ℝ := ε / (4 * (A + 1)) with hε'def
  have hε'pos : 0 < ε' := by rw [hε'def]; positivity
  have hAε' : A * ε' ≤ ε / 4 := by
    rw [hε'def]
    have h1 : A * (ε / (4 * (A + 1))) = (ε / 4) * (A / (A + 1)) := by
      field_simp
    rw [h1]
    have h2 : A / (A + 1) ≤ 1 := by
      rw [div_le_one (by linarith : (0:ℝ) < A + 1)]
      linarith
    calc (ε / 4) * (A / (A + 1)) ≤ (ε / 4) * 1 :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = ε / 4 := by ring
  -- The time scale on which the tail mass is `< ε'`.
  set M : ℝ := max (Real.log (1 / ε')) 1 with hMdef
  set t₀ : ℝ := δ ^ 2 / (8 * M) with ht₀def
  have hM1 : (1:ℝ) ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have ht₀pos : 0 < t₀ := by
    rw [ht₀def]; exact div_pos (pow_pos hδpos 2) (by linarith)
  have hmem : Ioo (0:ℝ) t₀ ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT ht₀pos
  filter_upwards [hmem] with t ht
  obtain ⟨ht0, htt₀⟩ := ht
  have hexp_le : Real.exp (-(δ ^ 2 / (8 * t))) ≤ ε' := by
    have h1 : Real.log (1 / ε') ≤ δ ^ 2 / (8 * t) := by
      have hMle : M ≤ δ ^ 2 / (8 * t) := by
        have h8t : (0:ℝ) < 8 * t := by linarith
        have h8M : (0:ℝ) < 8 * M := by linarith
        have hlt : t * (8 * M) < t₀ * (8 * M) := mul_lt_mul_of_pos_right htt₀ h8M
        rw [ht₀def, div_mul_cancel₀ _ (ne_of_gt h8M)] at hlt
        exact le_of_lt ((lt_div_iff₀ h8t).mpr (by nlinarith))
      exact le_trans (by rw [hMdef]; exact le_max_left _ _) hMle
    calc Real.exp (-(δ ^ 2 / (8 * t))) ≤ Real.exp (-(Real.log (1 / ε'))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = ε' := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
  -- Integrability bookkeeping.
  obtain ⟨hIntγ, hγ1⟩ := heatKernel_integral_one t ht0
  have hcontu : Continuous fun y : R3 => u (x - y) :=
    hu.comp (continuous_const.sub continuous_id)
  have hIntU : Integrable (fun y : R3 => u (x - y) * heatKernel t y) := by
    refine Integrable.mono' (hIntγ.const_mul C) ?_ ?_
    · exact hcontu.aestronglyMeasurable.mul hIntγ.aestronglyMeasurable
    · filter_upwards with y
      have h1 : |u (x - y)| ≤ C := hC (x - y)
      have h2 : 0 ≤ heatKernel t y := heatKernel_nonneg ht0.le y
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
      exact mul_le_mul_of_nonneg_right h1 h2
  have hIntUx : Integrable (fun y : R3 => u x * heatKernel t y) := hIntγ.const_mul (u x)
  have h2C : ∀ y : R3, |u (x - y) - u x| ≤ 2 * C := by
    intro y
    have h1 : |u (x - y)| ≤ C := hC (x - y)
    have h2 : |u x| ≤ C := hC x
    calc |u (x - y) - u x| ≤ |u (x - y)| + |u x| := abs_sub _ _
      _ ≤ C + C := add_le_add h1 h2
      _ = 2 * C := by ring
  have hIntAbs : Integrable (fun y : R3 => |u (x - y) - u x| * heatKernel t y) := by
    refine Integrable.mono' (hIntγ.const_mul (2 * C)) ?_ ?_
    · exact (((hcontu.sub continuous_const).abs).aestronglyMeasurable).mul
        hIntγ.aestronglyMeasurable
    · filter_upwards with y
      have h2 : 0 ≤ heatKernel t y := heatKernel_nonneg ht0.le y
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg (abs_nonneg _)]
      exact mul_le_mul_of_nonneg_right (h2C y) h2
  -- Rewrite the difference `∫ u(x-y)γ_t - u x` as the integral of the difference.
  have hsub : (∫ y, u (x - y) * heatKernel t y) - u x
      = ∫ y, (u (x - y) - u x) * heatKernel t y := by
    have hconst : u x = ∫ y, u x * heatKernel t y := by
      rw [MeasureTheory.integral_const_mul, hγ1, mul_one]
    conv_lhs => rw [hconst]
    rw [← MeasureTheory.integral_sub hIntU hIntUx]
    congr 1
    ext y
    ring
  have hnorm : |(∫ y, u (x - y) * heatKernel t y) - u x|
      ≤ ∫ y, |u (x - y) - u x| * heatKernel t y := by
    rw [hsub]
    calc |∫ y, (u (x - y) - u x) * heatKernel t y|
        ≤ ∫ y, |(u (x - y) - u x) * heatKernel t y| := abs_integral_le_integral_abs
      _ = ∫ y, |u (x - y) - u x| * heatKernel t y := by
          congr 1
          ext y
          rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ht0.le y)]
  -- Split into the inner ball and the outer tail.
  have hsplit : (∫ y, |u (x - y) - u x| * heatKernel t y)
      = (∫ y in Metric.ball (0 : R3) δ, |u (x - y) - u x| * heatKernel t y)
        + (∫ y in (Metric.ball (0 : R3) δ)ᶜ, |u (x - y) - u x| * heatKernel t y) :=
    (integral_add_compl Metric.isOpen_ball.measurableSet hIntAbs).symm
  have hpiece1 : (∫ y in Metric.ball (0 : R3) δ, |u (x - y) - u x| * heatKernel t y)
      ≤ ε / 4 := by
    have h1 : (∫ y in Metric.ball (0 : R3) δ, |u (x - y) - u x| * heatKernel t y)
        ≤ ∫ y in Metric.ball (0 : R3) δ, (ε / 4) * heatKernel t y := by
      apply setIntegral_mono_on hIntAbs.integrableOn
        ((hIntγ.const_mul (ε / 4)).integrableOn) Metric.isOpen_ball.measurableSet
      intro y hy
      have hy' : ‖y‖ < δ := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
        exact hy
      exact mul_le_mul_of_nonneg_right (le_of_lt (hδ' y hy')) (heatKernel_nonneg ht0.le y)
    refine le_trans h1 ?_
    rw [MeasureTheory.integral_const_mul]
    calc (ε / 4) * ∫ y in Metric.ball (0 : R3) δ, heatKernel t y
        ≤ (ε / 4) * ∫ y : R3, heatKernel t y :=
          mul_le_mul_of_nonneg_left
            (setIntegral_le_integral hIntγ (Eventually.of_forall fun y => heatKernel_nonneg ht0.le y))
            (by linarith)
      _ = ε / 4 := by rw [hγ1, mul_one]
  have hpiece2 : (∫ y in (Metric.ball (0 : R3) δ)ᶜ, |u (x - y) - u x| * heatKernel t y)
      ≤ ε / 4 := by
    have h1 : (∫ y in (Metric.ball (0 : R3) δ)ᶜ, |u (x - y) - u x| * heatKernel t y)
        ≤ ∫ y in (Metric.ball (0 : R3) δ)ᶜ, (2 * C) * heatKernel t y := by
      apply setIntegral_mono_on hIntAbs.integrableOn
        ((hIntγ.const_mul (2 * C)).integrableOn) Metric.isOpen_ball.measurableSet.compl
      intro y _
      exact mul_le_mul_of_nonneg_right (h2C y) (heatKernel_nonneg ht0.le y)
    refine le_trans h1 ?_
    rw [MeasureTheory.integral_const_mul]
    have hset : (Metric.ball (0 : R3) δ)ᶜ = {y : R3 | δ ≤ ‖y‖} := by
      ext y
      rw [Set.mem_compl_iff, Metric.mem_ball, dist_eq_norm, sub_zero]
      exact not_lt
    have htail : (∫ y in (Metric.ball (0 : R3) δ)ᶜ, heatKernel t y)
        ≤ 2 ^ (3 / 2 : ℝ) * Real.exp (-(δ ^ 2 / (8 * t))) := by
      rw [hset]
      exact heatKernel_tail_le t δ ht0 hδpos
    calc (2 * C) * ∫ y in (Metric.ball (0 : R3) δ)ᶜ, heatKernel t y
        ≤ (2 * C) * (2 ^ (3 / 2 : ℝ) * Real.exp (-(δ ^ 2 / (8 * t)))) :=
          mul_le_mul_of_nonneg_left htail (by linarith)
      _ = A * Real.exp (-(δ ^ 2 / (8 * t))) := by rw [hAdef]; ring
      _ ≤ A * ε' := mul_le_mul_of_nonneg_left hexp_le hA0
      _ ≤ ε / 4 := hAε'
  calc dist (∫ y, u (x - y) * heatKernel t y) (u x)
      = |(∫ y, u (x - y) * heatKernel t y) - u x| := Real.dist_eq _ _
    _ ≤ ∫ y, |u (x - y) - u x| * heatKernel t y := hnorm
    _ = (∫ y in Metric.ball (0 : R3) δ, |u (x - y) - u x| * heatKernel t y)
        + (∫ y in (Metric.ball (0 : R3) δ)ᶜ, |u (x - y) - u x| * heatKernel t y) := hsplit
    _ ≤ ε / 4 + ε / 4 := add_le_add hpiece1 hpiece2
    _ = ε / 2 := by ring
    _ < ε := by linarith

end

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.Deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open Work.FTS.Physical (physVel)
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

noncomputable section

/-- **The time derivative of the reconstructed potential**:
`potTDeriv ω x t = -∫ y, ⟪∇Nfund (x - y), ∂_t(u × ω)(y,t)⟫`. -/
noncomputable def potTDeriv (ω : R3 → ℝ → R3) (x : R3) (t : ℝ) : ℝ :=
  -∫ y, inner ℝ (nablaNfund (x - y))
    (FiniteTimeSingularity.timeDeriv (lamb (physVel ω) ω) y t)


/-- The `x`-component of the derivative of `q.uncurry`: `innerSL Φ` with
`Φ = ∂_t u - u×ω`. -/
noncomputable def potGradCLM (ω : R3 → ℝ → R3) (x : R3) (t : ℝ) : R3 →L[ℝ] ℝ :=
  innerSL ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) x t
    - crossVec (physVel ω x t) (ω x t))

/-- The full derivative of `q.uncurry` at `(x,t)`, as a continuous linear map on `R3 × ℝ`. -/
noncomputable def potFDeriv (ω : R3 → ℝ → R3) (x : R3) (t : ℝ) : R3 × ℝ →L[ℝ] ℝ :=
  (potGradCLM ω x t).comp (ContinuousLinearMap.fst ℝ R3 ℝ)
    + ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ R3 ℝ) (potTDeriv ω x t)

end

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.MollAux.weak_harmonic_mollified_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

open MeasureTheory

/-- **The mollified pair is weakly harmonic.**

Let `q : ℝ³ → ℝ` and `Φ : ℝ³ → ℝ³` be continuous and such that the distribution
`D = Φ - ∇q` is annihilated by both `∇φ` (`hdiv`) and `∇×ψ` (`hcurl`).  Then, for every smooth
compactly supported `W`, the *mollified* field `mollV n Φ - ∇(moll n q)` is orthogonal to
`laplaceTraceVec W`.

The three ingredients of the proof are

* `Work.FTS.PressureOn.Weyl.dpair_laplaceTraceVec_eq_zero`: the un-mollified pair pairs to zero
  against `ΔV` for every smooth compactly supported `V`; applied to `V = mollV n W`, which is
  again smooth with compact support (a convolution of two compactly supported functions);
* `Dpair_convolution`: the pairing `Dpair q Φ f = ∫⟪Φ, f⟫ + ∫ q · div f` is invariant under
  replacing `(q, Φ)` by the mollified pair and `f` by `ρ ⋆ f`;
* `Auxiliary.convolution_laplaceTraceVec_comm`: `ρ ⋆ (ΔW) = Δ(ρ ⋆ W)`.

These give `Dpair (moll n q) (mollV n Φ) (laplaceTraceVec W) = 0`, and the final identity
`∫⟪mollV n Φ - ∇(moll n q), ΔW⟫ = Dpair (moll n q) (mollV n Φ) (ΔW)` is the integration by parts
`∫ f · div V = -∫⟪∇f, V⟫` (`Auxiliary.integral_mul_div_eq_neg_inner_gradient`). -/
theorem weak_harmonic_mollified_diff
    (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hq : Continuous q) (hΦ : Continuous Φ)
    (hdiv : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) →
      HasCompactSupport φ →
      ∫ x, inner ℝ (Φ x) (gradient φ x)
        = -∫ x, q x * Work.FTS.PressureOn.laplaceTrace φ x)
    (hcurl : ∀ ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ x, inner ℝ (Φ x) (FiniteTimeSingularity.vorticity ψ x) = 0)
    (n : ℕ) (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hW : ∀ m : ℕ, ContDiff ℝ m W) (hWc : HasCompactSupport W) :
    ∫ x, inner ℝ (Work.FTS.PressureOn.mollV n Φ x
        - gradient (Work.FTS.PressureOn.moll n q) x)
      (Work.FTS.PressureOn.laplaceTraceVec W x) = 0 := by
  -- the mollifier `rho n`
  have hρ : ∀ m : ℕ, ContDiff ℝ m (rho n) := (rho_props n).1
  have hρc : HasCompactSupport (rho n) := (rho_props n).2.1
  have hρeven : ∀ z, rho n (-z) = rho n z := (rho_props n).2.2.2.2.1
  -- the test field `ΔW` and its mollification `mollV n W`
  have hΔs : ∀ m : ℕ, ContDiff ℝ m (laplaceTraceVec W) :=
    (laplaceTraceVec_smooth_compact W hW).1
  have hΔc : HasCompactSupport (laplaceTraceVec W) :=
    (laplaceTraceVec_smooth_compact W hW).2 hWc
  have hWVs : ∀ m : ℕ, ContDiff ℝ m (mollV n W) :=
    MollSB.contDiff_mollV n W (hW 0).continuous
  have hWVc : HasCompactSupport (mollV n W) := by
    unfold mollV
    exact hρc.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hWc
  -- step 1: the un-mollified pair, tested against `Δ (mollV n W)`, pairs to zero
  have hWeyl := Work.FTS.PressureOn.Weyl.dpair_laplaceTraceVec_eq_zero q Φ hq hΦ hdiv hcurl
    (mollV n W) hWVs hWVc
  -- step 2: the pairing is invariant under the mollification
  have hconv : Dpair q Φ (mollV n (laplaceTraceVec W))
      = Dpair (moll n q) (mollV n Φ) (laplaceTraceVec W) :=
    Dpair_convolution q Φ (rho n) (laplaceTraceVec W) hρ hρc hρeven hΔs hΔc hq hΦ
  -- step 3: the Laplacian commutes with the convolution
  have hcomm : mollV n (laplaceTraceVec W) = laplaceTraceVec (mollV n W) :=
    Auxiliary.convolution_laplaceTraceVec_comm (rho n) W hρ hρc hW
  have hkey : Dpair (moll n q) (mollV n Φ) (laplaceTraceVec W) = 0 := by
    rw [← hconv, hcomm]
    exact hWeyl
  -- step 4: expand the pairing by integration by parts
  have hms : ∀ m : ℕ, ContDiff ℝ m (moll n q) := MollSB.contDiff_moll n q hq
  have hIBP := Auxiliary.integral_mul_div_eq_neg_inner_gradient (moll n q) (laplaceTraceVec W)
    hms hΔs hΔc
  have hint1 : Integrable (fun x => inner ℝ (mollV n Φ x) (laplaceTraceVec W x)) :=
    Continuous.integrable_of_hasCompactSupport
      (((MollSB.contDiff_mollV n Φ hΦ 0).continuous).inner (hΔs 0).continuous)
      (HasCompactSupport.intro hΔc (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_right]))
  have hint2 : Integrable (fun x => inner ℝ (gradient (moll n q) x) (laplaceTraceVec W x)) := by
    have h1 : (fun x => inner ℝ (gradient (moll n q) x) (laplaceTraceVec W x))
        = fun x => (fderiv ℝ (moll n q) x) (laplaceTraceVec W x) := by
      funext x
      rw [inner_gradient_left]
    rw [h1]
    exact Continuous.integrable_of_hasCompactSupport
      (((hms 1).continuous_fderiv_apply (by norm_num)).comp
        (continuous_id.prodMk (hΔs 0).continuous))
      (HasCompactSupport.intro hΔc (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport hx, map_zero]))
  have hD : Dpair (moll n q) (mollV n Φ) (laplaceTraceVec W)
      = ∫ x, inner ℝ (mollV n Φ x - gradient (moll n q) x) (laplaceTraceVec W x) := by
    rw [Dpair, hIBP]
    rw [show (fun x => inner ℝ (mollV n Φ x - gradient (moll n q) x) (laplaceTraceVec W x))
        = fun x => inner ℝ (mollV n Φ x) (laplaceTraceVec W x)
            - inner ℝ (gradient (moll n q) x) (laplaceTraceVec W x) from
      funext fun x => inner_sub_left _ _ _]
    rw [integral_sub hint1 hint2]
    ring
  rw [← hD]
  exact hkey

end Work.FTS.PressureOn.MollAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Metric Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

/-! ## The truncated kernel is `C²` -/

/-- The truncated Newtonian kernel `x ↦ smallCut ε x * newtonKernel x` is `C²` for `ε > 0`: it is
`cutProfile ε (‖x‖²)`, and `cutProfile ε` is `C²` (`contDiff_cutProfile`). -/
lemma contDiff_smallCut_mul_newtonKernel (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 2 (fun x : R3 => smallCut ε x * newtonKernel x) := by
  have h1 : ContDiff ℝ (2 : ℕ∞) (fun x : R3 => cutProfile ε (‖x‖ ^ 2)) :=
    (contDiff_cutProfile ε hε).comp (contDiff_norm_sq (𝕜 := ℝ) (n := (2 : ℕ∞)))
  refine contDiffOn_univ.1 ((contDiffOn_univ.2 h1).congr ?_)
  intro x _
  exact (cutProfile_normSq ε x).symm

/-! ## Green's identity for each truncation -/

/-- **Green's identity applied to the truncation.**  For `ε > 0`,

`∫ x, (smallCut ε x * newtonKernel x) * laplaceTrace Ψ x = ∫ x, massKernel ε x * Ψ x`,

because the two integrands differ by a divergence
(`Green.integral_mul_laplaceTrace_comm`), and away from the single point `0` the Laplacian of the
truncated kernel is the mass kernel (`laplaceTrace_cutKernel`). -/
lemma integral_cutKernel_mul_laplaceTrace_eq (ε : ℝ) (hε : 0 < ε) {Ψ : R3 → ℝ}
    (hΨ2 : ContDiff ℝ 2 Ψ) (hΨcs : HasCompactSupport Ψ) :
    ∫ x, (smallCut ε x * newtonKernel x) * laplaceTrace Ψ x
      = ∫ x, massKernel ε x * Ψ x := by
  have hcut : ContDiff ℝ 2 (fun x : R3 => smallCut ε x * newtonKernel x) :=
    contDiff_smallCut_mul_newtonKernel ε hε
  rw [Green.integral_mul_laplaceTrace_comm _ _ hcut hΨ2 hΨcs]
  refine integral_congr_ae ?_
  have hne : ∀ᵐ x ∂(volume : Measure R3), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hne] with x hx
  rw [laplaceTrace_cutKernel ε hε hx]

/-! ## The `ε → 0⁺` limit of the truncated side -/

/-- **Dominated convergence for the truncated kernel.**  As `ε → 0⁺` the truncated kernel
`smallCut ε · newtonKernel` tends pointwise (off the origin) to `newtonKernel`, so
`∫ x, (smallCut ε x * N x) ΔΨ x → ∫ x, N x ΔΨ x` for `Ψ` of class `C²` with compact support. -/
lemma tendsto_integral_cutKernel {Ψ : R3 → ℝ} (hΨ2 : ContDiff ℝ 2 Ψ)
    (hΨcs : HasCompactSupport Ψ) :
    Tendsto (fun ε : ℝ => ∫ x, (smallCut ε x * newtonKernel x) * laplaceTrace Ψ x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, newtonKernel x * laplaceTrace Ψ x)) := by
  have hcont : Continuous (laplaceTrace Ψ) := Green.continuous_laplaceTrace Ψ hΨ2
  have hinte : Integrable (fun x : R3 => newtonKernel x * laplaceTrace Ψ x) :=
    KI.integrable_newtonKernel_mul_laplaceTrace hΨ2 hΨcs
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x : R3 => ‖newtonKernel x * laplaceTrace Ψ x‖) ?_ ?_ hinte.norm ?_
  · -- a.e. strong measurability
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hsc : Measurable (fun x : R3 => smallCut ε x) :=
      (contDiff_smallCut ε hε 0).continuous.measurable
    exact ((hsc.mul Green.measurable_newtonKernel).mul hcont.measurable).aestronglyMeasurable
  · -- domination
    filter_upwards with ε
    filter_upwards with x
    have habs : ‖smallCut ε x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (smallCut_nonneg ε x)]
      exact smallCut_le_one ε x
    calc ‖(smallCut ε x * newtonKernel x) * laplaceTrace Ψ x‖
        = ‖smallCut ε x‖ * ‖newtonKernel x‖ * ‖laplaceTrace Ψ x‖ := by
          rw [norm_mul, norm_mul]
      _ = ‖smallCut ε x‖ * (‖newtonKernel x‖ * ‖laplaceTrace Ψ x‖) := by ring
      _ ≤ 1 * (‖newtonKernel x‖ * ‖laplaceTrace Ψ x‖) :=
          mul_le_mul_of_nonneg_right habs (by positivity)
      _ = ‖newtonKernel x * laplaceTrace Ψ x‖ := by rw [one_mul, norm_mul]
  · -- pointwise convergence
    filter_upwards with x
    by_cases hx : x = 0
    · subst hx
      have h0 : newtonKernel (0 : R3) = 0 := by simp [newtonKernel]
      rw [h0]
      simp
    · -- for `x ≠ 0` the cutoff tends to `1`
      have hδ : 0 < ‖x‖ / Real.sqrt 2 := by positivity
      have hmem : Ioo (0 : ℝ) (‖x‖ / Real.sqrt 2) ∈ 𝓝[>] (0 : ℝ) := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨Iio _, Iio_mem_nhds hδ, fun y hy => ⟨hy.2, hy.1⟩⟩
      have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun ε : ℝ => radialCut (‖x‖ ^ 2 / ε ^ 2)) := by
        filter_upwards [hmem] with ε hε
        refine (radialCut_eq_zero ?_).symm
        rw [le_div_iff₀ (pow_pos hε.1 2)]
        have h2 : ε * Real.sqrt 2 < ‖x‖ := by
          have h := hε.2
          rw [lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))] at h
          exact h
        have h4 : (ε * Real.sqrt 2) ^ 2 < ‖x‖ ^ 2 := by
          rw [sq_lt_sq,
            abs_of_nonneg (mul_nonneg (le_of_lt hε.1) (Real.sqrt_nonneg 2)),
            abs_of_nonneg (norm_nonneg x)]
          exact h2
        have h5 : (ε * Real.sqrt 2) ^ 2 = 2 * ε ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          ring
        linarith
      have h0 : Tendsto (fun ε : ℝ => radialCut (‖x‖ ^ 2 / ε ^ 2))
          (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_const_nhds.congr' hev
      have hsm : Tendsto (fun ε : ℝ => smallCut ε x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
          tendsto_const_nhds
        have h := h1.sub h0
        simpa only [Pi.sub_apply, smallCut_apply, sub_zero] using h
      simpa using (hsm.mul tendsto_const_nhds).mul tendsto_const_nhds

/-! ## The centred fundamental identity -/

/-- **The centred fundamental solution identity.**  For `Ψ` of class `C²` with compact support,

`∫ x, newtonKernel x * laplaceTrace Ψ x = -Ψ 0`.

This is the `y = 0` case of `kernelIntegral`; the general case is deduced from it by translation. -/
lemma kernelIntegral_zero {Ψ : R3 → ℝ} (hΨ2 : ContDiff ℝ 2 Ψ) (hΨcs : HasCompactSupport Ψ) :
    ∫ x, newtonKernel x * laplaceTrace Ψ x = -Ψ 0 := by
  have hΨc : Continuous Ψ := hΨ2.continuous
  -- the per-`ε` identity: truncate, use Green, then rescale the mass kernel
  have hper : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ x, (smallCut ε x * newtonKernel x) * laplaceTrace Ψ x)
        = (∫ x, massKernel 1 x * Ψ (ε • x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [integral_cutKernel_mul_laplaceTrace_eq ε hε hΨ2 hΨcs]
    have hp : ∀ x : R3, massKernel ε x * Ψ x
        = (ε ^ 3)⁻¹ * (massKernel 1 (ε⁻¹ • x) * Ψ x) := by
      intro x
      rw [KI.massKernel_scale ε hε x]
      ring
    calc ∫ x, massKernel ε x * Ψ x
        = ∫ x, (ε ^ 3)⁻¹ * (massKernel 1 (ε⁻¹ • x) * Ψ x) :=
          integral_congr_ae (Eventually.of_forall hp)
      _ = (ε ^ 3)⁻¹ * ∫ x, massKernel 1 (ε⁻¹ • x) * Ψ x := integral_const_mul _ _
      _ = (ε ^ 3)⁻¹
            * ∫ x, (fun u : R3 => massKernel 1 u * Ψ (ε • u)) (ε⁻¹ • x) := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall ?_)
          intro x
          show massKernel 1 (ε⁻¹ • x) * Ψ x
            = massKernel 1 (ε⁻¹ • x) * Ψ (ε • (ε⁻¹ • x))
          rw [smul_inv_smul₀ (ne_of_gt hε)]
      _ = (ε ^ 3)⁻¹ * (|ε ^ 3| * ∫ x, massKernel 1 x * Ψ (ε • x)) := by
          rw [Measure.integral_comp_inv_smul (volume : Measure R3)
            (fun u : R3 => massKernel 1 u * Ψ (ε • u)) ε]
          simp [R3, smul_eq_mul]
      _ = ∫ x, massKernel 1 x * Ψ (ε • x) := by
          rw [abs_of_pos (pow_pos hε 3),
            inv_mul_cancel_left₀ (pow_ne_zero 3 (ne_of_gt hε))]
  -- the limit of the rescaled mass kernel is `-Ψ 0`
  have hlim2 : Tendsto (fun ε : ℝ => ∫ x, massKernel 1 x * Ψ (ε • x))
      (𝓝[>] (0 : ℝ)) (𝓝 (-Ψ 0)) := by
    have hpeak := KI.massKernel_peak hΨc
    rw [KI.massKernel_one_mass] at hpeak
    simpa using hpeak
  have hlim1 : Tendsto (fun ε : ℝ => ∫ x, massKernel 1 x * Ψ (ε • x))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, newtonKernel x * laplaceTrace Ψ x)) :=
    (tendsto_integral_cutKernel hΨ2 hΨcs).congr' hper
  exact tendsto_nhds_unique hlim1 hlim2

/-! ## The fundamental solution identity -/

theorem kernelIntegral {ψ : R3 → ℝ} (hψ : ∀ n : ℕ, ContDiff ℝ n ψ) (hcs : HasCompactSupport ψ)
    (y : R3) :
    ∫ x, newtonKernel (x - y) * laplaceTrace ψ x = -ψ y := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ 2
  -- the translate of `ψ` by `y` is again `C²` with compact support
  have hshift2 : ContDiff ℝ 2 (fun z : R3 => ψ (z + y)) :=
    hψ2.comp (contDiff_id.add contDiff_const)
  have hshift : HasCompactSupport (fun z : R3 => ψ (z + y)) := by
    have h := hcs.comp_homeomorph (Homeomorph.addRight y)
    simpa only [Function.comp_def, Homeomorph.coe_addRight] using h
  -- the translate of the integral
  have hsub : ∫ x, newtonKernel (x - y) * laplaceTrace ψ x
      = ∫ x, newtonKernel x * laplaceTrace ψ (x + y) := by
    have h := integral_sub_right_eq_self (μ := volume)
      (fun z : R3 => newtonKernel z * laplaceTrace ψ (z + y)) y
    simpa only [sub_add_cancel] using h
  -- the Laplace trace commutes with translation
  have hEq : (fun x : R3 => newtonKernel x * laplaceTrace ψ (x + y))
      = fun x : R3 => newtonKernel x * laplaceTrace (fun z : R3 => ψ (z + y)) x := by
    funext x
    rw [KI.laplaceTrace_comp_add ψ hψ2 y x]
  rw [hsub, hEq]
  have hz := kernelIntegral_zero hshift2 hshift
  simpa using hz

end Work.FTS.PressureOn.PoissonAux
end
