/-
# `Work.FTS.EllSol.VthAuxC.helpersC` — the calculus lemmas of the `V^{th}` slot on `ClassC`

Local `SmoothOpen`/`L₀` calculus used by the assembly of `Work.FTS.EllSol.ellVth_transferC`:

* `vthC_smoothOpen_add`, `vthC_smoothOpen_sub`, `vthC_smoothOpen_neg`,
  `vthC_smoothOpen_tan_mul` — closure of `SmoothOpen` under the operations occurring in
  `Ξ = Ψ̂ - Ḡ sin 2θ` and in `Vop Ξ = ∂_θΞ - tan θ · Ξ`;
* `vthC_Lzero_add` — `L₀` is additive on the open quadrant (`deriv`-bookkeeping);
* `vthC_pth_Vop_eq` — `∂_θ(Vop U) = -(L₀U + 6U)`, the `SmoothOpen` version of
  `Work.FTS.EllipticEst.RegQ.vms_pth_Vop_eq`;
* `vthC_inv_sqrt_gam_sub_one` — `1/√(γ-1) = √10 · α^{-1/2}`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Algebra
import Submission.Work.FTS.EllSol.Defs
import Submission.Work.FTS.EllSol.ropBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

set_option autoImplicit false

/-- `Ξ = EllResid α g Ψ = ellShift α g Ψ - Ḡ(α,g)·sin 2θ` as *functions* (the exact algebraic
identity behind the cancellation of the `1/α`-terms). -/
theorem vthC_EllResid_eq_ellShift (α : ℝ) (g Ψ : ℝ → ℝ → ℝ) :
    Work.Elliptic.EllResid α g Ψ
      = fun z θ => ellShift α g Ψ z θ + (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ) := by
  funext z θ
  rw [Work.FTS.EllSol.EllResid_eq_ellShift_sub_Gbar_point α g Ψ z θ, ellShift_apply]
  ring

theorem vthC_smoothOpen_add {f h : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + h z θ) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hf
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => h p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hh
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ + h z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ => f z θ + h z θ)
      = fun p : ℝ × ℝ => f p.1 p.2 + h p.1 p.2 := rfl
  rw [hfun]
  exact h1.add h2

theorem vthC_smoothOpen_sub {f h : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - h z θ) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hf
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => h p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hh
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ - h z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ => f z θ - h z θ)
      = fun p : ℝ × ℝ => f p.1 p.2 - h p.1 p.2 := rfl
  rw [hfun]
  exact h1.sub h2

theorem vthC_smoothOpen_neg {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => - f z θ) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hf
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => - f z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ => - f z θ)
      = fun p : ℝ × ℝ => - f p.1 p.2 := rfl
  rw [hfun]
  exact h1.neg

theorem vthC_smoothOpen_tan_mul {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * f z θ) := by
  have htan : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.tan p.2)
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.2)
        Work.FTS.EllipticEst.Q0 := contDiffOn_snd
    have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin p.2)
        Work.FTS.EllipticEst.Q0 := h1.sin
    have hcos : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.cos p.2)
        Work.FTS.EllipticEst.Q0 := h1.cos
    refine (ContDiffOn.div hsin hcos ?_).congr (fun p hp => ?_)
    · intro p hp
      have hp2 : p.2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [hp.2.1, Real.pi_pos], by linarith [hp.2.2]⟩
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo hp2)
    · exact Real.tan_eq_sin_div_cos p.2
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hf
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => Real.tan θ * f z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ => Real.tan θ * f z θ)
      = fun p : ℝ × ℝ => Real.tan p.2 * f p.1 p.2 := rfl
  rw [hfun]
  exact htan.mul h2

/-- `L₀` is additive on the open quadrant. -/
theorem vthC_Lzero_add {f h : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hh : Work.FTS.EllipticEst.SmoothOpen h)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Elliptic.Lzero (fun z' θ' => f z' θ' + h z' θ') z θ
      = Work.Elliptic.Lzero f z θ + Work.Elliptic.Lzero h z θ := by
  have hcos : Real.cos θ ≠ 0 := by
    have h1 : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo h1)
  have hf2 : ContDiffAt ℝ 2 (fun t => f z t) θ :=
    ((hf.curry_θ hz).contDiffAt (isOpen_Ioo.mem_nhds hθ)).of_le (by norm_num)
  have hh2 : ContDiffAt ℝ 2 (fun t => h z t) θ :=
    ((hh.curry_θ hz).contDiffAt (isOpen_Ioo.mem_nhds hθ)).of_le (by norm_num)
  have hev1 : (fun θ' => deriv (fun t => f z t + h z t) θ')
      =ᶠ[𝓝 θ] (fun θ' => deriv (fun t => f z t) θ' + deriv (fun t => h z t) θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    have hf2' : ContDiffAt ℝ 2 (fun t => f z t) θ' :=
      ((hf.curry_θ hz).contDiffAt (isOpen_Ioo.mem_nhds hθ')).of_le (by norm_num)
    have hh2' : ContDiffAt ℝ 2 (fun t => h z t) θ' :=
      ((hh.curry_θ hz).contDiffAt (isOpen_Ioo.mem_nhds hθ')).of_le (by norm_num)
    rw [show (fun t => f z t + h z t) = (fun t => f z t) + (fun t => h z t) from rfl,
      deriv_add (hf2'.differentiableAt (by norm_num)) (hh2'.differentiableAt (by norm_num))]
  have hd1f : ContDiffAt ℝ 1 (deriv (fun t => f z t)) θ := hf2.derivWithin (by norm_num)
  have hd1h : ContDiffAt ℝ 1 (deriv (fun t => h z t)) θ := hh2.derivWithin (by norm_num)
  have hsum2 : HasDerivAt (fun θ' => deriv (fun t => f z t) θ' + deriv (fun t => h z t) θ')
      (deriv (deriv (fun t => f z t)) θ + deriv (deriv (fun t => h z t)) θ) θ :=
    ((hd1f.differentiableAt (by norm_num)).hasDerivAt).add
      ((hd1h.differentiableAt (by norm_num)).hasDerivAt)
  have hsecond : deriv (fun θ' => deriv (fun t => f z t + h z t) θ') θ
      = deriv (deriv (fun t => f z t)) θ + deriv (deriv (fun t => h z t)) θ :=
    (hsum2.congr_of_eventuallyEq hev1).deriv
  have hevtan : (fun θ' => Real.tan θ' * (f z θ' + h z θ'))
      =ᶠ[𝓝 θ] (fun θ' => Real.tan θ' * f z θ' + Real.tan θ' * h z θ') := by
    filter_upwards with θ'
    ring
  have hdtf : DifferentiableAt ℝ (fun θ' => Real.tan θ' * f z θ') θ :=
    (Real.differentiableAt_tan.mpr hcos).mul (hf2.differentiableAt (by norm_num))
  have hdth : DifferentiableAt ℝ (fun θ' => Real.tan θ' * h z θ') θ :=
    (Real.differentiableAt_tan.mpr hcos).mul (hh2.differentiableAt (by norm_num))
  have htan : deriv (fun θ' => Real.tan θ' * (f z θ' + h z θ')) θ
      = deriv (fun θ' => Real.tan θ' * f z θ') θ
        + deriv (fun θ' => Real.tan θ' * h z θ') θ := by
    rw [hevtan.deriv_eq]
    rw [show (fun θ' => Real.tan θ' * f z θ' + Real.tan θ' * h z θ')
        = (fun θ' => Real.tan θ' * f z θ') + (fun θ' => Real.tan θ' * h z θ') from rfl,
      deriv_add hdtf hdth]
  simp only [Work.Elliptic.Lzero, Work.Spaces.pth, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero]
  rw [hsecond, htan]
  ring

/-- `∂_θ(Vop U) = -(L₀U + 6U)` for `U` merely `C^∞` on the open quadrant. -/
theorem vthC_pth_Vop_eq {U : ℝ → ℝ → ℝ} (hU : Work.FTS.EllipticEst.SmoothOpen U)
    {α z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pth (Work.FTS.EllipticEst.Vop α U) z θ
      = -(Work.Elliptic.Lzero U z θ + 6 * U z θ) := by
  have hcos : Real.cos θ ≠ 0 := by
    have h1 : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo h1)
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => U z θ')
      (Set.Ioo 0 (Real.pi / 2)) := hU.curry_θ hz
  have hU2 : ContDiffAt ℝ 2 (fun θ' => U z θ') θ :=
    (hslice.contDiffAt (isOpen_Ioo.mem_nhds hθ)).of_le (by norm_num)
  have hfd : HasDerivAt (fun θ' => U z θ') (deriv (fun θ' => U z θ') θ) θ :=
    (hU2.differentiableAt (by norm_num)).hasDerivAt
  have hd1 : ContDiffAt ℝ 1 (deriv (fun θ' => U z θ')) θ := hU2.derivWithin (by norm_num)
  have hfd2 : HasDerivAt (deriv (fun θ' => U z θ')) (deriv (deriv (fun θ' => U z θ')) θ) θ :=
    (hd1.differentiableAt (by norm_num)).hasDerivAt
  have htan0 : HasDerivAt (fun θ' => Real.tan θ' * U z θ')
      ((1 / Real.cos θ ^ 2) * U z θ + Real.tan θ * deriv (fun θ' => U z θ') θ) θ :=
    (Real.hasDerivAt_tan hcos).mul hfd
  have htan : HasDerivAt (fun θ' => Real.tan θ' * U z θ')
      (deriv (fun θ' => Real.tan θ' * U z θ') θ) θ :=
    htan0.congr_deriv htan0.deriv.symm
  have hsub : HasDerivAt (fun θ' => deriv (fun t => U z t) θ' - Real.tan θ' * U z θ')
      (deriv (deriv (fun t => U z t)) θ - deriv (fun θ' => Real.tan θ' * U z θ') θ) θ :=
    hfd2.sub htan
  have hfun : (fun θ' => Work.FTS.EllipticEst.Vop α U z θ')
      = fun θ' => deriv (fun t => U z t) θ' - Real.tan θ' * U z θ' := by
    funext θ'; simp only [Work.FTS.EllipticEst.Vop, Work.Spaces.pth]
  show deriv (fun θ' => Work.FTS.EllipticEst.Vop α U z θ') θ = _
  rw [hfun, hsub.deriv]
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]
  ring

/-- `1/√(γ-1) = √10 · α^{-1/2}` for `α > 0`. -/
theorem vthC_inv_sqrt_gam_sub_one {α : ℝ} (hα : 0 < α) :
    1 / Real.sqrt (Work.Spaces.gam α - 1) = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
  rw [Work.Spaces.gam_sub_one, Real.sqrt_div hα.le 10, one_div, inv_div]
  have hinv : α ^ (-(1 / 2 : ℝ)) = (Real.sqrt α)⁻¹ := by
    rw [Real.rpow_neg hα.le, ← Real.sqrt_eq_rpow]
  rw [hinv, inv_eq_one_div, div_eq_mul_inv, one_div]

end Work.FTS.EllSol
