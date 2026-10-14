import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.ProjPair.proj_pair_conj_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.SlotWCommon
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.PkgJets.pinBase
import Submission.Work.FTS_MuLipC.RowN.FaDens
import Submission.Work.FTS_RegExport.RXB.l12dens_weighted_bound
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.bSlotTop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

theorem bSlotTop (D : ℝ) (hD : 0 < D) :
    ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ))
        ≤ C * Work.Spaces.HkNorm α k F :=
  Work.FTS.EllipticEst.Prop.BSlotTop.B_slot_bound_fts D hD

end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ConvDeriv =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.slotW_LGammaT_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

theorem slotW_LGammaT_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    {f : Work.FTS.Galerkin.Fn} (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f)
    (hHH : Work.Coercivity.HardyHyp f) (hG : Work.Coercivity.GammaL2Bnd α) :
    (1 / 5) * Work.Coercivity.Ef f - 1000 * Work.Coercivity.EDthW f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGammaT α f) f := by
  have hα1' : α ≤ 1 := by linarith [hα1]
  have hf2 : RegQo α 2 f := regQo_mono (by norm_num) hf.1
  have hs : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  -- the two halves of the slot estimate
  have hA : (1 / 4) * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGamma α f) f :=
    OpenCoer.LGammaCoercive.LGamma_coercive_O hα hα1' hf2 hIP hHH hG
  have hB := OpenCoer.ProjPair.proj_pair_conj_O hα hα1' hf2 hIP hG
  have hBle : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.Proj α (Work.Coercivity.Transport f)) f
      ≤ (1 / 20) * Work.Coercivity.Ef f + 1000 * Work.Coercivity.EDthW f :=
    le_trans (le_abs_self _) hB.2
  -- the integrability of the two pairings, for `wip_sub_left`
  have hsub := Work.FTS.CoercivityFix.Coer1.wip_sub_left
    (ρ := fun z _ => Work.Spaces.w z ^ 2) (A := Work.Coercivity.LGamma α f)
    (B := Work.Coercivity.Proj α (Work.Coercivity.Transport f)) (C := f)
    (OpenCoer.intLG_O α hα hα1' hIP hs hHH) hB.1
  have hLGT : Work.Coercivity.LGammaT α f
      = (fun z θ => Work.Coercivity.LGamma α f z θ
          - Work.Coercivity.Proj α (Work.Coercivity.Transport f) z θ) := rfl
  rw [hLGT, hsub]
  linarith [hA, hBle]

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSpace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice famOf dynLin dynRHS)

set_option autoImplicit false

/-! ## The weighted size `EpsSq` -/

/-- The weight `w / sin(2θ)^{γ/2}` of the mixed slots of the scheme (its square is `wtG`). -/
def epsW (α : ℝ) (z θ : ℝ) : ℝ :=
  Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2)

/-- **The weighted `L²`-size of the scheme**: the level-`0` energy of the mixed slots, written as a
sum of squares so that the integrand is nonnegative everywhere (as in `Work.Spaces.HkSq`). -/
def EpsSq (α : ℝ) (f : Fn) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (f z θ * epsW α z θ) ^ 2

/-- **Membership in the weighted space `X` of the scheme**: the integrand of `EpsSq` is
integrable (so that `EpsSq` is an honest finite energy rather than Lean's junk value `0`). -/
def EpsMem (α : ℝ) (f : Fn) : Prop :=
  MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2)
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)

theorem EpsSq_nonneg (α : ℝ) (f : Fn) : 0 ≤ EpsSq α f :=
  MeasureTheory.integral_nonneg fun z =>
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _

theorem EpsSq_zero (α : ℝ) : EpsSq α (fun _ _ => 0) = 0 := by
  simp only [EpsSq, mul_zero, sq, mul_zero]
  simp

theorem EpsSq_congr {α : ℝ} {f f' : Fn} (h : ∀ z θ, f z θ = f' z θ) :
    EpsSq α f = EpsSq α f' := by
  simp only [EpsSq, h]

/-! ## The right-hand side as a function of a profile -/



end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.FixedAtoms5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.StrongEps.ClassCRHS

/-! ## Auxiliary facts

The five level-`5` atoms of this file are separable products `a(θ)·r(z)` of an angular
factor `a ∈ {SA0 α, SA1 α, 4α·SA0 α, 4α·SA1 α}` (with `SA0 = αΓ/c`, `SA1 = αD_θΓ/c`) and a
radial factor `r ∈ {SR0, SR2, hKer²}`.  The two derivatives of the engine used below are:

* the `D_θ`-iterates of a constant multiple of a `θ`-only function, and
* the two identifications of the `FK`-products with such separated products
  (`FK(F_*)·D_θF_* = (4α·SA1)(θ)·hKer²` and `FK(F_*)·F_* = (4α·SA0)(θ)·hKer²`). -/

/-- `D_θ`-iterates of a constant multiple of a `θ`-only function. -/
private lemma DthIter_rad_const_mul (c : ℝ) (i : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ (θ' : ℝ) => c * g θ') z θ
      = c * Work.Spaces.DthIter i (fun _ (θ' : ℝ) => g θ') z θ := by
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => c * g θ') z θ,
    Work.Spaces.dthU_iter_const_mul i c g]
  show c * Work.Spaces.dthU^[i] g θ
    = c * Work.Spaces.DthIter i (fun _ (θ' : ℝ) => g θ') z θ
  rw [Work.FTS.LocData.DthIter_rad_eq i g z θ]

/-- A crude product comparison used to combine the five `ℋ⁵`-bounds into one constant. -/
private lemma shift_le {a S S4 c c' : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S) (hS4 : 0 ≤ S4)
    (hc : 0 ≤ c) (hcc : c ≤ c') : a * S * c ≤ a * (S + S4) * c' := by
  have hS' : 0 ≤ S + S4 := by linarith
  have h1 : S * c ≤ (S + S4) * c' := mul_le_mul (le_add_of_nonneg_right hS4) hcc hc hS'
  calc a * S * c = a * (S * c) := by ring
    _ ≤ a * ((S + S4) * c') := mul_le_mul_of_nonneg_left h1 ha
    _ = a * (S + S4) * c' := by ring

/-- `FK(F_*)·D_θF_* = (4α·SA1)(θ)·(hKer z)²`. -/
private lemma sep_FK_Dth {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
      = fun z θ => (4 * α * SA1 α θ) * (Work.Spaces.hKer z) ^ 2 := by
  funext z θ
  have hFK : Work.Construction.FK (Work.Construction.Fstar α) z = α * Work.FM.Fstar z := by
    rw [Work.FTS.Nonlin.FK_Fstar hα hα1, Work.FM.Fstar]
  have hpth : Work.Spaces.pth (Work.Construction.Fstar α) z θ
      = (α * Work.FM.Fstar z / Work.Spaces.c α)
        * deriv (fun t => Work.Spaces.Gam α t) θ := by
    rw [Work.Spaces.pth]
    rw [show (fun θ' : ℝ => Work.Construction.Fstar α z θ')
        = fun θ' : ℝ => (α * Work.FM.Fstar z / Work.Spaces.c α)
            * Work.Spaces.Gam α θ' from by
      funext θ'
      rw [Work.Construction.Fstar]
      ring]
    rw [Work.Spaces.deriv_const_mul']
  rw [Work.Spaces.Dth, hFK, hpth]
  simp only [Work.Spaces.dthU_apply, Work.Spaces.hKer_apply, SA1, Work.FM.Fstar]
  ring_nf

/-- `FK(F_*)·F_* = (4α·SA0)(θ)·(hKer z)²`. -/
private lemma sep_FK_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ)
      = fun z θ => (4 * α * SA0 α θ) * (Work.Spaces.hKer z) ^ 2 := by
  funext z θ
  have hFK : Work.Construction.FK (Work.Construction.Fstar α) z = α * Work.FM.Fstar z := by
    rw [Work.FTS.Nonlin.FK_Fstar hα hα1, Work.FM.Fstar]
  rw [hFK]
  simp only [SA0, Work.Construction.Fstar, Work.Spaces.hKer_apply, Work.FM.Fstar]
  ring_nf

theorem FixedAtoms5 (hE : Work.FTS.StrongEps.H5.AngRad5.AngRadEngine5) :
    ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∃ C : ℝ, 0 < C ∧
      Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ C ∧
      Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C ∧
      Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ C ∧
      Work.FTS.VocabO.HQo α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C ∧
      Work.FTS.VocabO.HQo α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ) ≤ C := by
  obtain ⟨Ceng, hCengpos, hEng⟩ := hE
  intro α hαI
  obtain ⟨hα, hα1⟩ := Set.mem_Ioc.mp hαI
  -- ## the angular slot data of `SA0 = αΓ/c` and `SA1 = α D_θΓ/c`
  obtain ⟨B0, B1, hB0pos, hB1pos, hSA0bd, hSA0sl, hSA1bd, hSA1sl, -, -⟩ :=
    Work.FTS.StrongEps.H5.AngSlotBounds2 α hα hα1
  -- ## the angular mass of the sharp majorant `SGmj α = Γ(α + sin 2θ)`
  obtain ⟨M, hMpos, hMmass⟩ := Work.FTS.StrongEps.ClassCRHS.SGmj_mass
  obtain ⟨hMint, hMbd⟩ := hMmass α hα hα1
  have hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ SGmj α θ := fun θ hθ => SGmj_nonneg hα hθ
  -- ## the radial level-`5` data of `SR0`, `SR2` and `hKer²`
  obtain ⟨Cp0, hCp0pos, hCp0⟩ := Work.FTS.StrongEps.H5.Atoms.DzIter_SR0_le5
  obtain ⟨Cp2, hCp2pos, hCp2⟩ := Work.FTS.StrongEps.H5.Atoms.DzIter_SR2_le5
  obtain ⟨Cphk, hCphkpos, hCphk⟩ := Work.FTS.StrongEps.H5.Atoms.DzIter_hKerSq_le5
  have hSR0sm : ∀ n : ℕ, ContDiffOn ℝ n SR0 (Set.Ioi 0) := contDiffOn_SR0
  have hSR2sm : ∀ n : ℕ, ContDiffOn ℝ n SR2 (Set.Ioi 0) := contDiffOn_SR2
  have hhksm : ∀ n : ℕ, ContDiffOn ℝ n (fun z => (Work.Spaces.hKer z) ^ 2) (Set.Ioi 0) :=
    fun n => (Work.FTS.Nonlinear.Open.row23_contDiffOn_hKer n).pow 2
  obtain ⟨Cr0, hCr0pos, hCr0⟩ :=
    Work.FTS.StrongEps.H5.RadMem5 (r := SR0) hCp0pos hSR0sm hCp0
  obtain ⟨Cr2, hCr2pos, hCr2⟩ :=
    Work.FTS.StrongEps.H5.RadMem5 (r := SR2) hCp2pos hSR2sm hCp2
  obtain ⟨Crhk, hCrhkpos, hCrhk⟩ := Work.FTS.StrongEps.H5.RadMem5
    (r := fun z => (Work.Spaces.hKer z) ^ 2) hCphkpos hhksm hCphk
  have hSR0open : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => SR0 z) :=
    Work.FTS.Nonlinear.Open.row23_smoothOpen_radial hSR0sm
  have hSR2open : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => SR2 z) :=
    Work.FTS.Nonlinear.Open.row23_smoothOpen_radial hSR2sm
  have hHksm_open : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => (Work.Spaces.hKer z) ^ 2) :=
    Work.FTS.Nonlinear.Open.row23_smoothOpen_radial hhksm
  -- ## the `4α`-scaled angular factors of the two `FK`-products
  have h4αnn : (0 : ℝ) ≤ 4 * α := by positivity
  have hsm40 : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => 4 * α * SA0 α θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (4 * α) (smoothOpen_SA0 α)
  have hsm41 : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => 4 * α * SA1 α θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (4 * α) (smoothOpen_SA1 α)
  have hF0bd : ∀ θ ∈ Work.Spaces.Iθ, |4 * α * SA0 α θ| ≤ 4 * B0 := by
    intro θ hθ
    rw [abs_mul, abs_of_nonneg h4αnn]
    calc 4 * α * |SA0 α θ| ≤ 4 * α * B0 :=
          mul_le_mul_of_nonneg_left (hSA0bd θ hθ) h4αnn
      _ = 4 * (α * B0) := by ring
      _ ≤ 4 * B0 := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 4)
          exact mul_le_of_le_one_left hB0pos.le hα1
  have hF0sl : ∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => 4 * α * SA0 α θ') 0 θ|
        ≤ (4 * B1) * SGmj α θ := by
    intro i hi1 hi5 θ hθ
    rw [DthIter_rad_const_mul (4 * α) i (fun θ' => SA0 α θ') 0 θ, abs_mul,
      abs_of_nonneg h4αnn]
    calc 4 * α * |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => SA0 α θ') 0 θ|
        ≤ 4 * α * (B1 * SGmj α θ) :=
          mul_le_mul_of_nonneg_left (hSA0sl i hi1 hi5 θ hθ) h4αnn
      _ = 4 * (α * (B1 * SGmj α θ)) := by ring
      _ ≤ 4 * (B1 * SGmj α θ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 4)
          exact mul_le_of_le_one_left (mul_nonneg hB1pos.le (hGnn θ hθ)) hα1
      _ = (4 * B1) * SGmj α θ := by ring
  have hF1bd : ∀ θ ∈ Work.Spaces.Iθ, |4 * α * SA1 α θ| ≤ 4 * B0 := by
    intro θ hθ
    rw [abs_mul, abs_of_nonneg h4αnn]
    calc 4 * α * |SA1 α θ| ≤ 4 * α * B0 :=
          mul_le_mul_of_nonneg_left (hSA1bd θ hθ) h4αnn
      _ = 4 * (α * B0) := by ring
      _ ≤ 4 * B0 := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 4)
          exact mul_le_of_le_one_left hB0pos.le hα1
  have hF1sl : ∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => 4 * α * SA1 α θ') 0 θ|
        ≤ (4 * B1) * SGmj α θ := by
    intro i hi1 hi5 θ hθ
    rw [DthIter_rad_const_mul (4 * α) i (fun θ' => SA1 α θ') 0 θ, abs_mul,
      abs_of_nonneg h4αnn]
    calc 4 * α * |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => SA1 α θ') 0 θ|
        ≤ 4 * α * (B1 * SGmj α θ) :=
          mul_le_mul_of_nonneg_left (hSA1sl i hi1 hi5 θ hθ) h4αnn
      _ = 4 * (α * (B1 * SGmj α θ)) := by ring
      _ ≤ 4 * (B1 * SGmj α θ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 4)
          exact mul_le_of_le_one_left (mul_nonneg hB1pos.le (hGnn θ hθ)) hα1
      _ = (4 * B1) * SGmj α θ := by ring
  -- ## the five applications of the angular `×` radial engine
  have hK0 := hEng hα hα1 (a := SA0 α) (r := SR0) (G := SGmj α)
    (B0 := B0) (B1 := B1) (M := M) (Crad := Cr0 * Cp0)
    (smoothOpen_SA0 α) hSR0open hGnn hMint hB0pos.le hB1pos.le hMpos.le
    (mul_pos hCr0pos hCp0pos).le hSA0bd hSA0sl hMbd (hCr0 α hαI).1 (hCr0 α hαI).2
  have hK1 := hEng hα hα1 (a := SA1 α) (r := SR0) (G := SGmj α)
    (B0 := B0) (B1 := B1) (M := M) (Crad := Cr0 * Cp0)
    (smoothOpen_SA1 α) hSR0open hGnn hMint hB0pos.le hB1pos.le hMpos.le
    (mul_pos hCr0pos hCp0pos).le hSA1bd hSA1sl hMbd (hCr0 α hαI).1 (hCr0 α hαI).2
  have hK2 := hEng hα hα1 (a := SA0 α) (r := SR2) (G := SGmj α)
    (B0 := B0) (B1 := B1) (M := M) (Crad := Cr2 * Cp2)
    (smoothOpen_SA0 α) hSR2open hGnn hMint hB0pos.le hB1pos.le hMpos.le
    (mul_pos hCr2pos hCp2pos).le hSA0bd hSA0sl hMbd (hCr2 α hαI).1 (hCr2 α hαI).2
  have hK3 := hEng hα hα1 (a := fun θ => 4 * α * SA1 α θ)
    (r := fun z => (Work.Spaces.hKer z) ^ 2) (G := SGmj α)
    (B0 := 4 * B0) (B1 := 4 * B1) (M := M) (Crad := Crhk * Cphk)
    hsm41 hHksm_open hGnn hMint (by positivity) (by positivity) hMpos.le
    (mul_pos hCrhkpos hCphkpos).le hF1bd hF1sl hMbd (hCrhk α hαI).1 (hCrhk α hαI).2
  have hK4 := hEng hα hα1 (a := fun θ => 4 * α * SA0 α θ)
    (r := fun z => (Work.Spaces.hKer z) ^ 2) (G := SGmj α)
    (B0 := 4 * B0) (B1 := 4 * B1) (M := M) (Crad := Crhk * Cphk)
    hsm40 hHksm_open hGnn hMint (by positivity) (by positivity) hMpos.le
    (mul_pos hCrhkpos hCphkpos).le hF0bd hF0sl hMbd (hCrhk α hαI).1 (hCrhk α hαI).2
  -- ## the packaged constant
  set S : ℝ := Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) with hSdef
  set S4 : ℝ := Real.sqrt ((4 * B0) ^ 2 * 10 ^ 4 + 5 * (4 * B1) ^ 2 * M) with hS4def
  set K : ℝ := Ceng * (S + S4) * (Cr0 * Cp0 + Cr2 * Cp2 + Crhk * Cphk) + 1 with hKdef
  have hSnn : 0 ≤ S := by rw [hSdef]; exact Real.sqrt_nonneg _
  have hS4nn : 0 ≤ S4 := by rw [hS4def]; exact Real.sqrt_nonneg _
  have hKpos : 0 < K := by
    have h1 : 0 ≤ Cr0 * Cp0 := (mul_pos hCr0pos hCp0pos).le
    have h2 : 0 ≤ Cr2 * Cp2 := (mul_pos hCr2pos hCp2pos).le
    have h3 : 0 ≤ Crhk * Cphk := (mul_pos hCrhkpos hCphkpos).le
    have hprod : 0 ≤ Ceng * (S + S4) * (Cr0 * Cp0 + Cr2 * Cp2 + Crhk * Cphk) :=
      mul_nonneg (mul_nonneg hCengpos.le (by linarith)) (by linarith)
    rw [hKdef]
    linarith
  have e0 : Ceng * S * (Cr0 * Cp0) ≤ K := by
    have h := shift_le (a := Ceng) (S := S) (S4 := S4) (c := Cr0 * Cp0)
      (c' := Cr0 * Cp0 + Cr2 * Cp2 + Crhk * Cphk) hCengpos.le hSnn hS4nn
      (mul_pos hCr0pos hCp0pos).le (by linarith [(mul_pos hCr2pos hCp2pos).le,
        (mul_pos hCrhkpos hCphkpos).le])
    rw [hKdef]
    linarith
  have e2 : Ceng * S * (Cr2 * Cp2) ≤ K := by
    have h := shift_le (a := Ceng) (S := S) (S4 := S4) (c := Cr2 * Cp2)
      (c' := Cr0 * Cp0 + Cr2 * Cp2 + Crhk * Cphk) hCengpos.le hSnn hS4nn
      (mul_pos hCr2pos hCp2pos).le (by linarith [(mul_pos hCr0pos hCp0pos).le,
        (mul_pos hCrhkpos hCphkpos).le])
    rw [hKdef]
    linarith
  have e3 : Ceng * S4 * (Crhk * Cphk) ≤ K := by
    have h := shift_le (a := Ceng) (S := S4) (S4 := S) (c := Crhk * Cphk)
      (c' := Cr0 * Cp0 + Cr2 * Cp2 + Crhk * Cphk) hCengpos.le hS4nn hSnn
      (mul_pos hCrhkpos hCphkpos).le (by linarith [(mul_pos hCr0pos hCp0pos).le,
        (mul_pos hCr2pos hCp2pos).le])
    have hswap : S4 + S = S + S4 := by ring
    rw [hswap] at h
    rw [hKdef]
    linarith
  -- ## the five norm bounds with the single constant `K`
  have hK0b : Work.Spaces.HkNorm α 5 (fun z θ => SA0 α θ * SR0 z) ≤ Ceng * S * (Cr0 * Cp0) := by
    rw [hSdef]; exact hK0.2
  have hK1b : Work.Spaces.HkNorm α 5 (fun z θ => SA1 α θ * SR0 z) ≤ Ceng * S * (Cr0 * Cp0) := by
    rw [hSdef]; exact hK1.2
  have hK2b : Work.Spaces.HkNorm α 5 (fun z θ => SA0 α θ * SR2 z) ≤ Ceng * S * (Cr2 * Cp2) := by
    rw [hSdef]; exact hK2.2
  have hK3b : Work.Spaces.HkNorm α 5
      (fun z θ => (4 * α * SA1 α θ) * (Work.Spaces.hKer z) ^ 2)
        ≤ Ceng * S4 * (Crhk * Cphk) := by
    rw [hS4def]; exact hK3.2
  have hK4b : Work.Spaces.HkNorm α 5
      (fun z θ => (4 * α * SA0 α θ) * (Work.Spaces.hKer z) ^ 2)
        ≤ Ceng * S4 * (Crhk * Cphk) := by
    rw [hS4def]; exact hK4.2
  -- ## the transfers to the literal atoms
  have hq0 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      SA0 α θ * SR0 z = z / (1 + z) * Work.Construction.Fstar α z θ :=
    fun z θ hz _ _ => agree0 hα hα1 hz
  have hq1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      SA1 α θ * SR0 z
        = z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ :=
    fun z θ hz _ _ => agree1 hα hα1 hz
  have hq2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      SA0 α θ * SR2 z
        = z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ :=
    fun z θ hz _ _ => agree2 hα hα1 hz
  have hs0 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => SA0 α θ * SR0 z) :=
    Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad (smoothOpen_SA0 α) hSR0open
  have hs1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => SA1 α θ * SR0 z) :=
    Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad (smoothOpen_SA1 α) hSR0open
  have hs2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => SA0 α θ * SR2 z) :=
    Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad (smoothOpen_SA0 α) hSR2open
  have hs3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (4 * α * SA1 α θ) * (Work.Spaces.hKer z) ^ 2) :=
    Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad hsm41 hHksm_open
  have hs4 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (4 * α * SA0 α θ) * (Work.Spaces.hKer z) ^ 2) :=
    Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad hsm40 hHksm_open
  -- ## atom 0: `z/(1+z)·F_* = SA0(θ)·SR0(z)`
  have hQ0 : Work.FTS.VocabO.HQo α 5
      (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) :=
    ⟨hs0.congr hq0, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 5 hK0.1
      (fun z hz θ hθ => hq0 z θ hz hθ.1 hθ.2)⟩
  have hb0 : Work.Spaces.HkNorm α 5
      (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ K := by
    show Real.sqrt (Work.Spaces.HkSq α 5
      (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ)) ≤ K
    rw [← Work.FTS.EllipticEst.HkSq_congr_open α 5 hq0]
    exact le_trans hK0b e0
  -- ## atom 1: `z/(1+z)·D_θF_* = SA1(θ)·SR0(z)`
  have hQ1 : Work.FTS.VocabO.HQo α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) :=
    ⟨hs1.congr hq1, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 5 hK1.1
      (fun z hz θ hθ => hq1 z θ hz hθ.1 hθ.2)⟩
  have hb1 : Work.Spaces.HkNorm α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ K := by
    show Real.sqrt (Work.Spaces.HkSq α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)) ≤ K
    rw [← Work.FTS.EllipticEst.HkSq_congr_open α 5 hq1]
    exact le_trans hK1b e0
  -- ## atom 2: `z/(1+z)·D_zF_* = SA0(θ)·SR2(z)`
  have hQ2 : Work.FTS.VocabO.HQo α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    ⟨hs2.congr hq2, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 5 hK2.1
      (fun z hz θ hθ => hq2 z θ hz hθ.1 hθ.2)⟩
  have hb2 : Work.Spaces.HkNorm α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ K := by
    show Real.sqrt (Work.Spaces.HkSq α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)) ≤ K
    rw [← Work.FTS.EllipticEst.HkSq_congr_open α 5 hq2]
    exact le_trans hK2b e2
  -- ## atom 3: `FK(F_*)·D_θF_*`
  have hQ3 : Work.FTS.VocabO.HQo α 5
      (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) := by
    rw [sep_FK_Dth hα hα1]
    exact ⟨hs3, hK3.1⟩
  have hb3 : Work.Spaces.HkNorm α 5
      (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ K := by
    rw [sep_FK_Dth hα hα1]
    exact le_trans hK3b e3
  -- ## atom 4: `FK(F_*)·F_*`
  have hQ4 : Work.FTS.VocabO.HQo α 5
      (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ) := by
    rw [sep_FK_Fstar hα hα1]
    exact ⟨hs4, hK4.1⟩
  have hb4 : Work.Spaces.HkNorm α 5
      (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ) ≤ K := by
    rw [sep_FK_Fstar hα hα1]
    exact le_trans hK4b e3
  exact ⟨K, hKpos, hQ0, hb0, hQ1, hb1, hQ2, hb2, hQ3, hb3, hQ4, hb4⟩

end Work.FTS.StrongEps.H5.Atoms
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000

namespace Work.FTS.StrongEps


end Work.FTS.StrongEps
end
