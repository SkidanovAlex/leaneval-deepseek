import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## 1. Smoothness infrastructure for the open quadrant -/



/-- `Work.Stability.smoothOrder` is not zero (it is the genuine smooth order `∞`). -/
theorem smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]



/-- `SmoothOpen` is closed under multiplication by a constant. -/
theorem smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    SmoothOpen (fun z θ => c * f z θ) := by
  have hfun : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact (contDiffOn_const : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => c)
    Work.FTS.EllipticEst.Q0).mul hf

/-- `SmoothOpen` only depends on the values on the open quadrant. -/
theorem smoothOpen_congr {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f)
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → g z θ = f z θ) : SmoothOpen g :=
  hf.congr (fun p hp => by
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact h p.1 p.2 hz hθ0 hθ1)


/-- `SmoothOpen` is closed under iterated `∂_θ`. -/
theorem smoothOpen_pthIter {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (n : ℕ) :
    SmoothOpen (Work.Spaces.pthIter n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth



/-! ## 2. Additivity and separation of the iterated derivatives -/



/-- On the open quadrant the iterated `∂_θ`-operators are additive for `SmoothOpen` data. -/
theorem pthIter_add_on_Q0 {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) (n : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pthIter n f z θ + Work.Spaces.pthIter n g z θ := by
  induction n with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨h1, h2⟩
      have heq : (fun θ' => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ' + Work.Spaces.pthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n f z θ') θ :=
        (((smoothOpen_pthIter hf n).curry_θ hz).differentiableOn smoothOrder_ne_zero
          |>.differentiableAt (isOpen_Ioo.mem_nhds hθ))
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n g z θ') θ :=
        (((smoothOpen_pthIter hg n).curry_θ hz).differentiableOn smoothOrder_ne_zero
          |>.differentiableAt (isOpen_Ioo.mem_nhds hθ))
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pth]
      exact heq.deriv_eq.trans (deriv_add hd1 hd2)


/-- `∂_θ (R z · sin 2θ) = R z · 2 cos 2θ`. -/
theorem pth_radial_sin (R : ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => R z * Real.sin (2 * θ))
      = fun z θ => R z * (2 * Real.cos (2 * θ)) := by
  funext z θ
  have hd : DifferentiableAt ℝ (fun θ' : ℝ => Real.sin (2 * θ')) θ :=
    ((Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)).differentiableAt
  have key : deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = Real.cos (2 * θ) * (2 * 1) :=
    ((Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)).deriv
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul (R z) hd, key]
  ring

/-- `∂_θ² (R z · sin 2θ) = R z · (-4 sin 2θ)`. -/
theorem pthIter_two_radial_sin (R : ℝ → ℝ) :
    Work.Spaces.pthIter 2 (fun z θ => R z * Real.sin (2 * θ))
      = fun z θ => R z * (-4 * Real.sin (2 * θ)) := by
  show Work.Spaces.pth (Work.Spaces.pth (fun z θ => R z * Real.sin (2 * θ)))
      = fun z θ => R z * (-4 * Real.sin (2 * θ))
  rw [pth_radial_sin R]
  funext z θ
  have hd : DifferentiableAt ℝ (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ :=
    (((Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)).const_mul
      2).differentiableAt
  have key : deriv (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ
      = 2 * (-Real.sin (2 * θ) * (2 * 1)) :=
    (((Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)).const_mul 2).deriv
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul (R z) hd, key]
  ring


/-! ## 3. `HkMem` is closed under addition on the open quadrant -/

/-- **`ℋ^k` is closed under addition** for `SmoothOpen` data. -/
theorem HkMem_add_open (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) := by
  have hfg : SmoothOpen (fun z θ => f z θ + g z θ) := smoothOpen_add hf hg
  refine Work.FTS.LocData.HkMem_of_majorant α k (f := fun z θ => f z θ + g z θ)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α k f z θ
      + 2 * Work.Spaces.HkIntegrand α k g z θ)
    (hfg.continuousOn_HkIntegrand α k) ?_ ?_ ?_
  · intro z hz
    exact ((hmf.1 z hz).const_mul 2).add ((hmg.1 z hz).const_mul 2)
  · have htarget : IntegrableOn (fun z : ℝ => 2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ) + 2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ)) Work.Spaces.Iz :=
      (hmf.2.const_mul 2).add (hmg.2.const_mul 2)
    refine Integrable.congr htarget ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_add ((hmf.1 z hz).const_mul 2) ((hmg.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    exact Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn α k hf hg z hz θ hθ

/-! ## 4. The analytic facts about `F_*`, `L₁₂`, `Gsing` and `Ḡ` from `EllHyp` -/


/-! ## 5. The angular moment of the straightened solution, and the orthogonality identity -/





/-! ## 6. The pointwise straightening identities on the open quadrant -/






/-! ## 7. The straightening transfers -/


end Work.FTS.EllipticEst.RPFresh
