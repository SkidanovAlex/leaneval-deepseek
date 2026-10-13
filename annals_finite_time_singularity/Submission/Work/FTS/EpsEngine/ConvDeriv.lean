/-
# Derivatives of a convolution with a smooth compactly supported kernel, for a merely
locally integrable second factor.

`J_ε` is, in the log coordinates `s = log z`, `ζ = log tan θ`, the convolution
`Jker ρ ε ⋆ logPull f` (`Work.FTS.StrongEps.Jeps_eq_conv`, in
`Submission/Work/FTS/StrongEps/Jeps_contDiffOn.lean`).  The point of this module is that the
derivatives of that convolution can be *routed onto the kernel*, even when `f` is only locally
integrable (after the log-pull): `∂₁` and `∂₂` act on the smooth compactly supported kernel, by a
change of variables in the shift parameter `p`.

This is the analytic half of `mixed_Jeps_kernel_locInt`
(`Submission/Work/FTS/EpsEngine/mixed_Jeps_kernel_locInt.lean`): the chain rule that turns
`D_z = ∂_s`, `D_θ = 2 ∂_ζ` into the `(j,i)`-derivatives of the convolution is
`Work.FTS.EpsEngine.mixed_logCoords` (a separate module).

The one-step statements are `conv_hasDerivAt_fst`/`conv_hasDerivAt_snd`; the iterated statement
is `conv_Kd`.  All rest on `HasCompactSupport.hasFDerivAt_convolution_left`
(`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`), whose derivatives are computed by
evaluating the Fréchet derivative of the convolution in the coordinate directions `(1,0)`, `(0,1)`
(`fderiv_apply_inl`/`fderiv_apply_inr`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Convolution
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.FTS.StrongEps (partFst partSnd Kd Kd_zero_eq Kd_succ_eq Kd_smooth Kd_compact)

/-! ## Evaluating the Fréchet derivative in the coordinate directions -/

/-- The directional derivative in the first coordinate, from the Fréchet derivative. -/
theorem fderiv_apply_inl {A : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hA : DifferentiableAt ℝ A p) :
    fderiv ℝ A p (1, 0) = partFst A p := by
  have hγ : HasDerivAt (fun s : ℝ => (s, p.2)) (1, 0) p.1 := by
    simpa only [ContinuousLinearMap.inl_apply] using
      ((hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2).hasDerivAt)
  have h := hA.hasFDerivAt.comp_hasDerivAt p.1 hγ
  have hderiv : deriv (fun s : ℝ => A (s, p.2)) p.1 = (fderiv ℝ A p) (1, 0) := h.deriv
  exact hderiv.symm

/-- The directional derivative in the second coordinate, from the Fréchet derivative. -/
theorem fderiv_apply_inr {A : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hA : DifferentiableAt ℝ A p) :
    fderiv ℝ A p (0, 1) = partSnd A p := by
  have hγ : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 := by
    simpa only [ContinuousLinearMap.inr_apply] using
      ((hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2).hasDerivAt)
  have h := hA.hasFDerivAt.comp_hasDerivAt p.2 hγ
  have hderiv : deriv (fun t : ℝ => A (p.1, t)) p.2 = (fderiv ℝ A p) (0, 1) := h.deriv
  exact hderiv.symm

/-! ## The one-step derivatives of the convolution -/

/-- **The derivative of a convolution in the first coordinate.**  For a kernel `A` that is `C^∞`
with compact support and a merely locally integrable second factor `w`, the derivative of
`s ↦ ∫ p, A p * w (s - p.1, y - p.2)` is the convolution with `∂₁A`.  The derivative is pushed
onto `A` by a change of variable in `p`, so no regularity of `w` is needed. -/
theorem conv_hasDerivAt_fst {A w : ℝ × ℝ → ℝ} (hA : ∀ n : ℕ, ContDiff ℝ n A)
    (hAs : HasCompactSupport A) (hw : MeasureTheory.LocallyIntegrable w MeasureTheory.volume)
    (x y : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ p : ℝ × ℝ, A p * w (s - p.1, y - p.2))
      (∫ p : ℝ × ℝ, partFst A p * w (x - p.1, y - p.2)) x := by
  have hF : HasFDerivAt (fun X : ℝ × ℝ => ∫ p : ℝ × ℝ, A p * w (X - p))
      ((fderiv ℝ A ⋆[ContinuousLinearMap.precompL (ℝ × ℝ) (ContinuousLinearMap.lsmul ℝ ℝ),
        MeasureTheory.volume] w) (x, y)) (x, y) := by
    have h := hAs.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hA 1) hw (x, y)
    rwa [show (A ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] w)
        = fun X : ℝ × ℝ => ∫ p : ℝ × ℝ, A p * w (X - p) from by
      funext X
      rw [MeasureTheory.convolution_def]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]] at h
  have hval : ((fderiv ℝ A ⋆[ContinuousLinearMap.precompL (ℝ × ℝ) (ContinuousLinearMap.lsmul ℝ ℝ),
        MeasureTheory.volume] w) (x, y)) (1, 0)
      = ∫ p : ℝ × ℝ, partFst A p * w (x - p.1, y - p.2) := by
    rw [MeasureTheory.convolution_def]
    rw [ContinuousLinearMap.integral_apply _ (1, 0)]
    · refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply,
        smul_eq_mul]
      rw [fderiv_apply_inl ((hA 1).differentiable one_ne_zero).differentiableAt]
      rfl
    · exact (hAs.fderiv ℝ).convolutionExists_left _
        ((hA 1).continuous_fderiv one_ne_zero) hw (x, y)
  have hγ : HasDerivAt (fun s : ℝ => (s, y)) (1, 0) x := by
    simpa only [ContinuousLinearMap.inl_apply] using
      ((hasFDerivAt_prodMk_left (𝕜 := ℝ) x y).hasDerivAt)
  have hcomp := hF.comp_hasDerivAt x hγ
  rw [hval] at hcomp
  convert hcomp using 1
  funext s
  simp only [Function.comp_apply]
  rfl

/-- **The derivative of a convolution in the second coordinate.**  Same as `conv_hasDerivAt_fst`,
with `∂₂A` in place of `∂₁A`. -/
theorem conv_hasDerivAt_snd {A w : ℝ × ℝ → ℝ} (hA : ∀ n : ℕ, ContDiff ℝ n A)
    (hAs : HasCompactSupport A) (hw : MeasureTheory.LocallyIntegrable w MeasureTheory.volume)
    (x y : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ p : ℝ × ℝ, A p * w (x - p.1, t - p.2))
      (∫ p : ℝ × ℝ, partSnd A p * w (x - p.1, y - p.2)) y := by
  have hF : HasFDerivAt (fun X : ℝ × ℝ => ∫ p : ℝ × ℝ, A p * w (X - p))
      ((fderiv ℝ A ⋆[ContinuousLinearMap.precompL (ℝ × ℝ) (ContinuousLinearMap.lsmul ℝ ℝ),
        MeasureTheory.volume] w) (x, y)) (x, y) := by
    have h := hAs.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hA 1) hw (x, y)
    rwa [show (A ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] w)
        = fun X : ℝ × ℝ => ∫ p : ℝ × ℝ, A p * w (X - p) from by
      funext X
      rw [MeasureTheory.convolution_def]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]] at h
  have hval : ((fderiv ℝ A ⋆[ContinuousLinearMap.precompL (ℝ × ℝ) (ContinuousLinearMap.lsmul ℝ ℝ),
        MeasureTheory.volume] w) (x, y)) (0, 1)
      = ∫ p : ℝ × ℝ, partSnd A p * w (x - p.1, y - p.2) := by
    rw [MeasureTheory.convolution_def]
    rw [ContinuousLinearMap.integral_apply _ (0, 1)]
    · refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply,
        smul_eq_mul]
      rw [fderiv_apply_inr ((hA 1).differentiable one_ne_zero).differentiableAt]
      rfl
    · exact (hAs.fderiv ℝ).convolutionExists_left _
        ((hA 1).continuous_fderiv one_ne_zero) hw (x, y)
  have hγ : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y := by
    simpa only [ContinuousLinearMap.inr_apply] using
      ((hasFDerivAt_prodMk_right (𝕜 := ℝ) x y).hasDerivAt)
  have hcomp := hF.comp_hasDerivAt y hγ
  rw [hval] at hcomp
  convert hcomp using 1
  funext t
  simp only [Function.comp_apply]
  rfl

/-! ## The iterated statement -/

/-- `Kd A j 0` is the `j`-fold `∂₁`, i.e. `(partFst^[j]) A`. -/
theorem Kd_fst_iter (A : ℝ × ℝ → ℝ) (j : ℕ) : Kd A j 0 = (partFst^[j]) A := by
  induction j with
  | zero => simp only [Kd_zero_eq, Function.iterate_zero_apply]
  | succ j ih => rw [Kd_succ_eq, ih, Function.iterate_succ_apply']

/-- `Kd A j i` is `(∂₁^j)(∂₂^i A)`. -/
theorem Kd_iterate (A : ℝ × ℝ → ℝ) (j i : ℕ) :
    Kd A j i = (partFst^[j]) ((partSnd^[i]) A) := by
  induction j with
  | zero => simp only [Kd_zero_eq, Function.iterate_zero_apply]
  | succ j ih => rw [Kd_succ_eq, ih, Function.iterate_succ_apply']

/-- **The iterated derivatives of the convolution in the second coordinate**, expressed as the
convolution with the iterated `∂₂`-derivatives of the kernel. -/
theorem partSnd_iter_conv {A w : ℝ × ℝ → ℝ} (hA : ∀ n : ℕ, ContDiff ℝ n A)
    (hAs : HasCompactSupport A) (hw : MeasureTheory.LocallyIntegrable w MeasureTheory.volume)
    (x : ℝ) (i : ℕ) :
    ∀ y : ℝ, iteratedDeriv i (fun t : ℝ => ∫ p : ℝ × ℝ, A p * w (x - p.1, t - p.2)) y
      = ∫ p : ℝ × ℝ, (partSnd^[i]) A p * w (x - p.1, y - p.2) := by
  induction i with
  | zero => intro y; simp
  | succ i ih =>
    intro y
    have hsm : ∀ n : ℕ, ContDiff ℝ n ((partSnd^[i]) A) := Kd_smooth A hA 0 i
    have hcs : HasCompactSupport ((partSnd^[i]) A) := Kd_compact A hAs 0 i
    have hd := conv_hasDerivAt_snd hsm hcs hw x y
    have hfun : (fun t : ℝ =>
          iteratedDeriv i (fun t' : ℝ => ∫ p : ℝ × ℝ, A p * w (x - p.1, t' - p.2)) t)
        = fun t : ℝ => ∫ p : ℝ × ℝ, (partSnd^[i]) A p * w (x - p.1, t - p.2) :=
      funext (fun t => ih t)
    rw [iteratedDeriv_succ]
    change deriv (fun t : ℝ =>
      iteratedDeriv i (fun t' : ℝ => ∫ p : ℝ × ℝ, A p * w (x - p.1, t' - p.2)) t) y = _
    rw [hfun, hd.deriv]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [Function.iterate_succ_apply']

/-- **The iterated derivatives of the convolution in the first coordinate**, expressed as the
convolution with the iterated `∂₁`-derivatives of the kernel. -/
theorem partFst_iter_conv {A w : ℝ × ℝ → ℝ} (hA : ∀ n : ℕ, ContDiff ℝ n A)
    (hAs : HasCompactSupport A) (hw : MeasureTheory.LocallyIntegrable w MeasureTheory.volume)
    (y : ℝ) (j : ℕ) :
    ∀ x : ℝ, iteratedDeriv j (fun s : ℝ => ∫ p : ℝ × ℝ, A p * w (s - p.1, y - p.2)) x
      = ∫ p : ℝ × ℝ, (partFst^[j]) A p * w (x - p.1, y - p.2) := by
  induction j with
  | zero => intro x; simp
  | succ j ih =>
    intro x
    have hsm : ∀ n : ℕ, ContDiff ℝ n ((partFst^[j]) A) := by
      rw [← Kd_fst_iter A j]; exact Kd_smooth A hA j 0
    have hcs : HasCompactSupport ((partFst^[j]) A) := by
      rw [← Kd_fst_iter A j]; exact Kd_compact A hAs j 0
    have hd := conv_hasDerivAt_fst hsm hcs hw x y
    have hfun : (fun s : ℝ =>
          iteratedDeriv j (fun s' : ℝ => ∫ p : ℝ × ℝ, A p * w (s' - p.1, y - p.2)) s)
        = fun s : ℝ => ∫ p : ℝ × ℝ, (partFst^[j]) A p * w (s - p.1, y - p.2) :=
      funext (fun s => ih s)
    rw [iteratedDeriv_succ]
    change deriv (fun s : ℝ =>
      iteratedDeriv j (fun s' : ℝ => ∫ p : ℝ × ℝ, A p * w (s' - p.1, y - p.2)) s) x = _
    rw [hfun, hd.deriv]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [Function.iterate_succ_apply']

/-- **The mixed iterated derivatives of the convolution**: the derivative `∂₁^j ∂₂^i` of
`X ↦ ∫ p, A p * w (X - p)` is the convolution of `w` with `Kd A j i = ∂₁^j ∂₂^i A`. -/
theorem conv_Kd {A w : ℝ × ℝ → ℝ} (hA : ∀ n : ℕ, ContDiff ℝ n A)
    (hAs : HasCompactSupport A) (hw : MeasureTheory.LocallyIntegrable w MeasureTheory.volume)
    (j i : ℕ) (x y : ℝ) :
    iteratedDeriv j (fun s : ℝ =>
        iteratedDeriv i (fun t : ℝ => ∫ p : ℝ × ℝ, A p * w (s - p.1, t - p.2)) y) x
      = ∫ p : ℝ × ℝ, Kd A j i p * w (x - p.1, y - p.2) := by
  have hinner : (fun s : ℝ =>
        iteratedDeriv i (fun t : ℝ => ∫ p : ℝ × ℝ, A p * w (s - p.1, t - p.2)) y)
      = fun s : ℝ => ∫ p : ℝ × ℝ, (partSnd^[i]) A p * w (s - p.1, y - p.2) :=
    funext (fun s => partSnd_iter_conv hA hAs hw s i y)
  rw [hinner]
  have hsm : ∀ n : ℕ, ContDiff ℝ n ((partSnd^[i]) A) := Kd_smooth A hA 0 i
  have hcs : HasCompactSupport ((partSnd^[i]) A) := Kd_compact A hAs 0 i
  rw [partFst_iter_conv hsm hcs hw y j x]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  rw [Kd_iterate]

end Work.FTS.EpsEngine
