import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.Nonlinear.FstarPkg.c2mInv_mixed
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.VInteg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 800000






end Work.EllipticEst.InteriorRegularity.VT
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.localEquationLoc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The pointwise Leibniz computation behind the localized equation: for `ψ = χ·φc` and with the
cut-off data `χ' ≡ 1`, `σ ≡ 1`, `tt ≡ tan θ` on the open set `U ⊇ tsupport χ` (and `U` avoiding
the poles of `tan`), the sum of the eight terms of the local equation vanishes pointwise. -/
private theorem pointwiseIdentityLoc {χ χ' σ tt φc : E2 → ℂ} {U : Set E2}
    (hU : IsOpen U) (htsU : tsupport χ ⊆ U) (hcosU : ∀ x ∈ U, Real.cos (x 1) ≠ 0)
    (hχs : ∀ n : ℕ, ContDiff ℝ n χ) (hχ's : ∀ n : ℕ, ContDiff ℝ n χ')
    (hσs : ∀ n : ℕ, ContDiff ℝ n σ) (htts : ∀ n : ℕ, ContDiff ℝ n tt)
    (hφs : ∀ n : ℕ, ContDiff ℝ n φc)
    (hσ1 : ∀ x ∈ U, σ x = 1) (htt1 : ∀ x ∈ U, tt x = (Real.tan (x 1) : ℂ))
    (hχ'1 : ∀ x ∈ U, χ' x = 1) (x : E2) :
    χ x * (d0 (d0 φc) x + d1 (d1 φc) x)
      + χ x * d0 (fun y => (5 * σ y) * φc y) x
      - χ x * d1 (fun y => (σ y * tt y) * φc y) x
      + χ x * (6 * σ x) * φc x
      - χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)
      + χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x
      + χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x
      + Kop (fun y => χ y * φc y) x = 0 := by
  have hχd : ∀ y : E2, DifferentiableAt ℝ χ y := fun y => (hχs 1).differentiable (by norm_num) y
  have hσd : ∀ y : E2, DifferentiableAt ℝ σ y := fun y => (hσs 1).differentiable (by norm_num) y
  have httd : ∀ y : E2, DifferentiableAt ℝ tt y := fun y => (htts 1).differentiable (by norm_num) y
  have hφd : ∀ y : E2, DifferentiableAt ℝ φc y := fun y => (hφs 1).differentiable (by norm_num) y
  have hd0χd : ∀ y : E2, DifferentiableAt ℝ (d0 χ) y :=
    fun y => (Loc.contDiff_d0 hχs 1).differentiable (by norm_num) y
  have hd1χd : ∀ y : E2, DifferentiableAt ℝ (d1 χ) y :=
    fun y => (Loc.contDiff_d1 hχs 1).differentiable (by norm_num) y
  have hd0φd : ∀ y : E2, DifferentiableAt ℝ (d0 φc) y :=
    fun y => (Loc.contDiff_d0 hφs 1).differentiable (by norm_num) y
  have hd1φd : ∀ y : E2, DifferentiableAt ℝ (d1 φc) y :=
    fun y => (Loc.contDiff_d1 hφs 1).differentiable (by norm_num) y
  have e2 : d0 (fun y => (5 * σ y) * φc y) x = (5 * σ x) * d0 φc x + (5 * d0 σ x) * φc x := by
    rw [Loc.d0_mul (f := fun y => 5 * σ y) (g := φc) (x := x)
        ((differentiableAt_const (c := (5 : ℂ))).mul (hσd x)) (hφd x),
      Loc.d0_const_mul (5 : ℂ) (hσd x)]
  have e3 : d1 (fun y => (σ y * tt y) * φc y) x
      = (σ x * tt x) * d1 φc x + (σ x * d1 tt x + d1 σ x * tt x) * φc x := by
    rw [Loc.d1_mul (f := fun y => σ y * tt y) (g := φc) (x := x) ((hσd x).mul (httd x)) (hφd x),
      Loc.d1_mul (f := σ) (g := tt) (x := x) (hσd x) (httd x)]
  have e4 : d0 (fun y => (2 * d0 χ y) * φc y) x
      = (2 * d0 χ x) * d0 φc x + (2 * d0 (d0 χ) x) * φc x := by
    rw [Loc.d0_mul (f := fun y => 2 * d0 χ y) (g := φc) (x := x)
        ((differentiableAt_const (c := (2 : ℂ))).mul (hd0χd x)) (hφd x),
      Loc.d0_const_mul (2 : ℂ) (hd0χd x)]
  have e5 : d1 (fun y => (2 * d1 χ y) * φc y) x
      = (2 * d1 χ x) * d1 φc x + (2 * d1 (d1 χ) x) * φc x := by
    rw [Loc.d1_mul (f := fun y => 2 * d1 χ y) (g := φc) (x := x)
        ((differentiableAt_const (c := (2 : ℂ))).mul (hd1χd x)) (hφd x),
      Loc.d1_const_mul (2 : ℂ) (hd1χd x)]
  have eK : Kop (fun y => χ y * φc y) x
      = - (d0 (d0 (fun y => χ y * φc y)) x) - (d1 (d1 (fun y => χ y * φc y)) x)
        - 5 * d0 (fun y => χ y * φc y) x
        + (Real.tan (x 1) : ℂ) * d1 (fun y => χ y * φc y) x
        + (((Real.tan (x 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ x * φc x) := by
    rw [show Kop (fun y => χ y * φc y) = fun z : E2 =>
        - d0 (d0 (fun y => χ y * φc y)) z - d1 (d1 (fun y => χ y * φc y)) z
        - 5 * d0 (fun y => χ y * φc y) z
        + (Real.tan (z 1) : ℂ) * d1 (fun y => χ y * φc y) z
        + (((Real.tan (z 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ z * φc z) from rfl]
  rw [e2, e3, e4, e5, eK]
  rw [Loc.d0_d0_mul (f := χ) (g := φc) hχd hφd hd0χd hd0φd x,
      Loc.d1_d1_mul (f := χ) (g := φc) hχd hφd hd1χd hd1φd x,
      Loc.d0_mul (f := χ) (g := φc) (x := x) (hχd x) (hφd x),
      Loc.d1_mul (f := χ) (g := φc) (x := x) (hχd x) (hφd x)]
  simp only [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_ofNat]
  by_cases hx : x ∈ U
  · have hσx : σ x = 1 := hσ1 x hx
    have httx : tt x = (Real.tan (x 1) : ℂ) := htt1 x hx
    have hχ'x : χ' x = 1 := hχ'1 x hx
    have hevσ : σ =ᶠ[𝓝 x] (fun _ : E2 => (1 : ℂ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hσ1 y hy
    have hd0σ : d0 σ x = 0 := by rw [Loc.d0_congr hevσ, Loc.d0_const]
    have hd1σ : d1 σ x = 0 := by rw [Loc.d1_congr hevσ, Loc.d1_const]
    have hevtt : tt =ᶠ[𝓝 x] (fun y : E2 => (Real.tan (y 1) : ℂ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact htt1 y hy
    have hcos : Real.cos (x 1) ≠ 0 := hcosU x hx
    have hd1tt : d1 tt x = 1 + ((Real.tan (x 1) : ℂ)) ^ 2 := by
      rw [Loc.d1_congr hevtt, Loc.d1_tan' x hcos]
    rw [hσx, httx, hχ'x, hd0σ, hd1σ, hd1tt]
    ring
  · have hxt : x ∉ tsupport χ := fun h => hx (htsU h)
    have hW : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
    have hxW : x ∈ (tsupport χ)ᶜ := hxt
    have hχ0W : ∀ y ∈ (tsupport χ)ᶜ, χ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
    have hevχ : χ =ᶠ[𝓝 x] (0 : E2 → ℂ) := Filter.eventuallyEq_of_mem (hW.mem_nhds hxW) hχ0W
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hxt
    have hd0χ : d0 χ x = 0 := Loc.d0_eq_zero_of_eventuallyEq_zero hevχ
    have hd1χ : d1 χ x = 0 := Loc.d1_eq_zero_of_eventuallyEq_zero hevχ
    have hevd0χ : d0 χ =ᶠ[𝓝 x] (0 : E2 → ℂ) :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hxW)
        (fun y hy => Loc.d0_eq_zero_of_eventuallyEq_zero
          (Filter.eventuallyEq_of_mem (hW.mem_nhds hy) hχ0W))
    have hevd1χ : d1 χ =ᶠ[𝓝 x] (0 : E2 → ℂ) :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hxW)
        (fun y hy => Loc.d1_eq_zero_of_eventuallyEq_zero
          (Filter.eventuallyEq_of_mem (hW.mem_nhds hy) hχ0W))
    have hd0d0χ : d0 (d0 χ) x = 0 := Loc.d0_eq_zero_of_eventuallyEq_zero hevd0χ
    have hd1d1χ : d1 (d1 χ) x = 0 := Loc.d1_eq_zero_of_eventuallyEq_zero hevd1χ
    rw [hχx, hd0χ, hd1χ, hd0d0χ, hd1d1χ]
    ring

/-- The pairing form of the localized distributional equation.  From the weak identity for `(V,G)` on `W` one gets, for every test function `φ`, the identity obtained by testing the weak formulation against `χ·φ` and rewriting with the cut-off data (`χ' ≡ 1`, `σ ≡ 1`, `tt ≡ tan θ` on the open `U ⊇ tsupport χ`).

Warning: do NOT import `Submission.Work.EllipticEst.InteriorRegularity.IR.Defs` (it re-declares `stripE` and clashes with `Strip.lean`). The helper lemmas `d0_mul`, `d1_mul`, `d0_add`, `d1_add`, `d0_congr`, `d1_congr`, `d0_eq_zero_of_eventuallyEq_zero`, `d1_eq_zero_of_eventuallyEq_zero`, `d0_d0_mul`, `d1_d1_mul`, `d1_tan`, `d0_const_mul`, `d1_const_mul` in `Submission/Work/EllipticEst/InteriorRegularity/LocalEquation.lean` are proved (that file's `localEquation` itself is not; re-prove the helpers or copy them into a sorry-free file of your own). -/
theorem localEquationLoc {V G : Work.EllipticEst.InteriorRegularity.E2 → ℂ}
    {W : Set Work.EllipticEst.InteriorRegularity.E2}
    (hweak : ∀ ψ : Work.EllipticEst.InteriorRegularity.E2 → ℂ,
      (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      Function.support ψ ⊆ W →
      ∫ x, V x * Work.EllipticEst.InteriorRegularity.Kop ψ x = ∫ x, G x * ψ x)
    {χ χ' σ tt : Work.EllipticEst.InteriorRegularity.E2 → ℂ}
    {U : Set Work.EllipticEst.InteriorRegularity.E2}
    (hχc : HasCompactSupport χ) (hχs : ∀ n : ℕ, ContDiff ℝ n χ)
    (hχ'c : HasCompactSupport χ') (hχ's : ∀ n : ℕ, ContDiff ℝ n χ')
    (hσc : HasCompactSupport σ) (hσs : ∀ n : ℕ, ContDiff ℝ n σ)
    (httc : HasCompactSupport tt) (htts : ∀ n : ℕ, ContDiff ℝ n tt)
    (hU : IsOpen U) (htsU : tsupport χ ⊆ U) (hUsub : U ⊆ W)
    (hχ'1 : ∀ x ∈ U, χ' x = 1) (hσ1 : ∀ x ∈ U, σ x = 1)
    (htt1 : ∀ x ∈ U, tt x = (Real.tan (x 1) : ℂ))
    (hV : MeasureTheory.Integrable V) (hG : MeasureTheory.Integrable G)
    (φ : SchwartzMap Work.EllipticEst.InteriorRegularity.E2 ℂ) :
    (∫ x, (χ x * (Work.EllipticEst.InteriorRegularity.d0 (Work.EllipticEst.InteriorRegularity.d0 (φ : Work.EllipticEst.InteriorRegularity.E2 → ℂ)) x
          + Work.EllipticEst.InteriorRegularity.d1 (Work.EllipticEst.InteriorRegularity.d1 (φ : Work.EllipticEst.InteriorRegularity.E2 → ℂ)) x)) * V x)
      = - (∫ x, (χ x * Work.EllipticEst.InteriorRegularity.d0 (fun y => (5 * σ y) * φ y) x) * V x)
        + (∫ x, (χ x * Work.EllipticEst.InteriorRegularity.d1 (fun y => (σ y * tt y) * φ y) x) * V x)
        - (∫ x, (χ x * (6 * σ x) * φ x) * V x)
        + (∫ x,
            (χ' x * (((Work.EllipticEst.InteriorRegularity.d0 (Work.EllipticEst.InteriorRegularity.d0 χ) x + Work.EllipticEst.InteriorRegularity.d1 (Work.EllipticEst.InteriorRegularity.d1 χ) x)
              - 5 * Work.EllipticEst.InteriorRegularity.d0 χ x + tt x * Work.EllipticEst.InteriorRegularity.d1 χ x) * φ x)) * V x)
        - (∫ x, (χ' x * Work.EllipticEst.InteriorRegularity.d0 (fun y => (2 * Work.EllipticEst.InteriorRegularity.d0 χ y) * φ y) x) * V x)
        - (∫ x, (χ' x * Work.EllipticEst.InteriorRegularity.d1 (fun y => (2 * Work.EllipticEst.InteriorRegularity.d1 χ y) * φ y) x) * V x)
        - (∫ x, (χ x * φ x) * G x) := by
  set φc : E2 → ℂ := (φ : E2 → ℂ) with hφc
  have hφs : ∀ n : ℕ, ContDiff ℝ n φc := by
    intro n
    rw [hφc]
    exact φ.smooth n
  -- the test function `ψ = χ·φc`
  have hψsm : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => χ y * φc y) :=
    fun n => (hχs n).mul (hφs n)
  have hψcs : HasCompactSupport (fun y : E2 => χ y * φc y) := hχc.mul_right
  have hψsupp : Function.support (fun y : E2 => χ y * φc y) ⊆ W := by
    intro y hy
    exact hUsub (htsU (subset_tsupport χ (Function.support_mul_subset_left χ φc hy)))
  have hwk := hweak (fun y : E2 => χ y * φc y) hψsm hψcs hψsupp
  -- integrability of the integrands
  have hVint : ∀ {a : E2 → ℂ}, Continuous a → HasCompactSupport a →
      Integrable (fun x => a x * V x) := by
    intro a ha hac
    simpa only [smul_eq_mul] using
      hV.locallyIntegrable.integrable_smul_left_of_hasCompactSupport ha hac
  have h5σφ : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => (5 * σ y) * φc y) :=
    fun n => ((contDiff_const (c := (5 : ℂ))).mul (hσs n)).mul (hφs n)
  have hσtt : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => (σ y * tt y) * φc y) :=
    fun n => ((hσs n).mul (htts n)).mul (hφs n)
  have h2d0χ : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => (2 * d0 χ y) * φc y) :=
    fun n => ((contDiff_const (c := (2 : ℂ))).mul (Loc.contDiff_d0 hχs n)).mul (hφs n)
  have h2d1χ : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => (2 * d1 χ y) * φc y) :=
    fun n => ((contDiff_const (c := (2 : ℂ))).mul (Loc.contDiff_d1 hχs n)).mul (hφs n)
  have hρ : ∀ n : ℕ, ContDiff ℝ n
      (fun x : E2 => (d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) :=
    fun n => (((Loc.contDiff_d0 (Loc.contDiff_d0 hχs) n).add
        (Loc.contDiff_d1 (Loc.contDiff_d1 hχs) n)).sub
      ((contDiff_const (c := (5 : ℂ))).mul (Loc.contDiff_d0 hχs n))).add
      ((htts n).mul (Loc.contDiff_d1 hχs n))
  have hc1 : Continuous (fun x : E2 => χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) :=
    (hχs 0).continuous.mul (((Loc.contDiff_d0 (Loc.contDiff_d0 hφs) 0).continuous).add
      ((Loc.contDiff_d1 (Loc.contDiff_d1 hφs) 0).continuous))
  have hc2 : Continuous (fun x : E2 => χ x * d0 (fun y => (5 * σ y) * φc y) x) :=
    (hχs 0).continuous.mul ((Loc.contDiff_d0 h5σφ 0).continuous)
  have hc3 : Continuous (fun x : E2 => χ x * d1 (fun y => (σ y * tt y) * φc y) x) :=
    (hχs 0).continuous.mul ((Loc.contDiff_d1 hσtt 0).continuous)
  have hc4 : Continuous (fun x : E2 => χ x * (6 * σ x) * φc x) :=
    ((hχs 0).continuous.mul ((contDiff_const (c := (6 : ℂ))).mul (hσs 0)).continuous).mul
      (hφs 0).continuous
  have hc5 : Continuous (fun x : E2 => χ' x *
      (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) :=
    (hχ's 0).continuous.mul (((hρ 0).continuous).mul (hφs 0).continuous)
  have hc6 : Continuous (fun x : E2 => χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) :=
    (hχ's 0).continuous.mul ((Loc.contDiff_d0 h2d0χ 0).continuous)
  have hc7 : Continuous (fun x : E2 => χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) :=
    (hχ's 0).continuous.mul ((Loc.contDiff_d1 h2d1χ 0).continuous)
  -- a continuous compactly supported representative of `Kop (χ·φc)`
  obtain ⟨K, hKc, hKcs, hKeq⟩ :=
    kopRepresentative (χ := χ) (φc := φc) (tt := tt) hU hχc htsU hχs hφs htts htt1
  have hInt1 : Integrable (fun x => (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x) :=
    hVint hc1 hχc.mul_right
  have hInt2 : Integrable (fun x => (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x) :=
    hVint hc2 hχc.mul_right
  have hInt3 : Integrable (fun x => (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x) :=
    hVint hc3 hχc.mul_right
  have hInt4 : Integrable (fun x => (χ x * (6 * σ x) * φc x) * V x) :=
    hVint hc4 ((hχc.mul_right (f' := fun x : E2 => 6 * σ x)).mul_right (f' := φc))
  have hInt5 : Integrable
      (fun x => (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x))
        * V x) :=
    hVint hc5 hχ'c.mul_right
  have hInt6 : Integrable (fun x => (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x) :=
    hVint hc6 hχ'c.mul_right
  have hInt7 : Integrable (fun x => (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x) :=
    hVint hc7 hχ'c.mul_right
  have hInt8 : Integrable (fun x => K x * V x) := hVint hKc hKcs
  -- the pointwise identity
  set B : E2 → ℂ := fun x =>
    χ x * (d0 (d0 φc) x + d1 (d1 φc) x)
      + χ x * d0 (fun y => (5 * σ y) * φc y) x
      - χ x * d1 (fun y => (σ y * tt y) * φc y) x
      + χ x * (6 * σ x) * φc x
      - χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)
      + χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x
      + χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x
      + K x with hBdef
  have hBzero : ∀ x : E2, B x = 0 := by
    intro x
    simp only [hBdef]
    rw [← hKeq x]
    exact pointwiseIdentityLoc hU htsU (cosNeZeroOfEqTanOn hU htts htt1) hχs hχ's hσs htts
      hφs hσ1 htt1 hχ'1 x
  have hzero : ∫ x, B x * V x = 0 := by simp [hBzero]
  have hlin : ∫ x, B x * V x
      = (∫ x, (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x)
        + (∫ x, (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x)
        - (∫ x, (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x)
        + (∫ x, (χ x * (6 * σ x) * φc x) * V x)
        - (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) * V x)
        + (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x)
        + (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x)
        + (∫ x, K x * V x) := by
    have hcongr : ∫ x, B x * V x
        = ∫ x, ((χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x
            + (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x
            - (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x
            + (χ x * (6 * σ x) * φc x) * V x
            - (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x))
                * V x
            + (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x
            + (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x
            + K x * V x) := by
      rw [show (fun x : E2 => B x * V x)
          = (fun x => ((χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x
            + (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x
            - (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x
            + (χ x * (6 * σ x) * φc x) * V x
            - (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x))
                * V x
            + (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x
            + (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x
            + K x * V x)) from funext (fun x => by simp only [hBdef]; ring)]
    rw [hcongr]
    exact Loc.integral_lin8 hInt1 hInt2 hInt3 hInt4 hInt5 hInt6 hInt7 hInt8
  have hIK : (∫ x, K x * V x) = (∫ x, (χ x * φc x) * G x) := by
    rw [show (fun x : E2 => K x * V x) = (fun x => V x * Kop (fun y => χ y * φc y) x) from
      funext (fun x => by rw [← hKeq x]; ring)]
    rw [hwk]
    rw [show (fun x : E2 => G x * (χ x * φc x)) = (fun x => (χ x * φc x) * G x) from
      funext (fun x => by ring)]
  have h1 : ∫ x, B x * V x
      = (∫ x, (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x)
        + (∫ x, (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x)
        - (∫ x, (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x)
        + (∫ x, (χ x * (6 * σ x) * φc x) * V x)
        - (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) * V x)
        + (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x)
        + (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x)
        + (∫ x, (χ x * φc x) * G x) := by
    rw [hlin, hIK]
  have h2 : (∫ x, (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x)
        + (∫ x, (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x)
        - (∫ x, (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x)
        + (∫ x, (χ x * (6 * σ x) * φc x) * V x)
        - (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) * V x)
        + (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x)
        + (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x)
        + (∫ x, (χ x * φc x) * G x) = 0 := by
    rw [← h1]
    exact hzero
  have h3 : (∫ x, (χ x * (d0 (d0 φc) x + d1 (d1 φc) x)) * V x)
      = - (∫ x, (χ x * d0 (fun y => (5 * σ y) * φc y) x) * V x)
        + (∫ x, (χ x * d1 (fun y => (σ y * tt y) * φc y) x) * V x)
        - (∫ x, (χ x * (6 * σ x) * φc x) * V x)
        + (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φc x)) * V x)
        - (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φc y) x) * V x)
        - (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φc y) x) * V x)
        - (∫ x, (χ x * φc x) * G x) := by
    linear_combination h2
  exact h3

end Work.EllipticEst.InteriorRegularity.VT
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.QuadAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The open quadrant on which `Work.FTS.LocData.SmoothQuad` is stated. -/
def Quad : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (0 : ℝ) (π / 2)

theorem isOpen_Quad : IsOpen Quad := isOpen_Ioi.prod isOpen_Ioo

theorem mem_Quad_iff {z θ : ℝ} : ((z, θ) ∈ Quad) ↔ -1 < z ∧ 0 < θ ∧ θ < π / 2 := by
  simp only [Quad, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Prod.fst, Prod.snd]

/-- `SmoothQuad` gives `C^∞` (hence `C^2`) at every interior point of the open quadrant. -/
theorem SmoothQuad.contDiffAt {f : Fn} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry f) (z, θ) := by
  have hmem : (z, θ) ∈ Quad := mem_Quad_iff.mpr ⟨by linarith, hθ, hθ2⟩
  exact (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Quad from hf).contDiffAt
    (isOpen_Quad.mem_nhds hmem)

theorem SmoothQuad.contDiffAt_two {f : Fn} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
  (SmoothQuad.contDiffAt hf hz hθ hθ2).of_le (by simp [Work.Stability.smoothOrder])


/-- Clairaut/Schwarz for the slice derivatives, from the interior class `SmoothQuad`. -/
theorem pz_pth_comm {f : Fn} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.pz (Work.Spaces.pth f) z θ = Work.Spaces.pth (Work.Spaces.pz f) z θ :=
  Work.Spaces.pz_pth_comm (SmoothQuad.contDiffAt_two hf hz hθ hθ2)

/-- `D_z` and `D_θ` commute, from `SmoothQuad`. -/
theorem Dz_Dth_comm {f : Fn} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.Dz (Work.Spaces.Dth f) z θ = Work.Spaces.Dth (Work.Spaces.Dz f) z θ :=
  Work.Spaces.Dz_Dth_comm (SmoothQuad.contDiffAt_two hf hz hθ hθ2)



end Work.FTS.CoercivityFix
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.TopSlotAux.AtopClean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000





/-! ## Auxiliaries for the `A`-part of the top angular slot

Everything below is bookkeeping for the proof of `A_top_slot_bound`: the pointwise bound on the
open quadrant of `|D_θ^k (z²∂_z²Ψ)|` by the slots of `D_z(∂_θθΨ)`, `∂_θθΨ` and `z²∂_zzΨ`. -/

/-- The open quadrant. -/
private def QQ : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

private theorem isOpen_QQ : IsOpen QQ := isOpen_Ioi.prod isOpen_Ioo


private theorem sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private theorem sin_two_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) := (sin_two_pos_of_mem hθ).le

/-- The zeroth coefficient of `D_θ^m` vanishes for `m ≥ 1` (both sides are operators with no
zeroth order term). -/
private theorem dthCoef_zero_fun {m : ℕ} (hm : 1 ≤ m) :
    selfdth.dthCoef m 0 = fun _ : ℝ => (0 : ℝ) := by
  induction m with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        funext θ
        show Real.sin (2 * θ) * (deriv (selfdth.dthCoef 0 0) θ
          + (if 1 ≤ 0 then selfdth.dthCoef 0 (0 - 1) θ else 0)) = 0
        simp [selfdth.dthCoef]
      · have h0 := ih hk
        funext θ
        show Real.sin (2 * θ) * (deriv (selfdth.dthCoef k 0) θ
          + (if 1 ≤ 0 then selfdth.dthCoef k (0 - 1) θ else 0)) = 0
        rw [h0]
        simp

private theorem dthCoef_apply_zero {m : ℕ} (hm : 1 ≤ m) (θ : ℝ) :
    selfdth.dthCoef m 0 θ = 0 := congrFun (dthCoef_zero_fun hm) θ

/-! ## The sharpened reverse expansion

`D_θ^m = Σ_{r ≤ m} a_{m,r} ∂_θ^r` with `a_{m,0} = 0` for `m ≥ 1` gives, on solving for the top
term, the *reverse* expansion without any zeroth-order term. -/

/-- **Sharpened reverse expansion.**  For every `m` there is `C > 0` such that for every `f` which
is `C^∞` at the point `(z,θ)` and every `θ ∈ (0,π/2)`,

  `sin(2θ)^m |∂_θ^m f(z,θ)| ≤ C (|D_θ^m f(z,θ)| + Σ_{1 ≤ r < m} sin(2θ)^r |∂_θ^r f(z,θ)|)`.

The point is the absence of the `r = 0` term, which is what `a_{m,0} = 0` buys. -/
private theorem sharp_reverse (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry f) (z, θ)) →
      (Real.sin (2 * θ)) ^ m * |Work.Spaces.pthIter m f z θ|
        ≤ C * (|Work.Spaces.DthIter m f z θ|
            + ∑ r ∈ Finset.Icc 1 (m - 1),
                (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) := by
  classical
  choose K hKpos hKbd using fun r => selfdth.DthCoef_sin_pow_bound m r
  have hKnn : (0 : ℝ) ≤ ∑ r ∈ Finset.range (m + 1), K r :=
    Finset.sum_nonneg fun i _ => (hKpos i).le
  refine ⟨1 + ∑ r ∈ Finset.range (m + 1), K r, by linarith, fun f z θ hθ hf => ?_⟩
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem hθ
  have hexp := selfdth.DthIter_expansion_local m f z θ hf
  have hself : selfdth.dthCoef m m θ = (Real.sin (2 * θ)) ^ m :=
    congrFun (selfdth.dthCoef_self m) θ
  have hsplit : (Real.sin (2 * θ)) ^ m * Work.Spaces.pthIter m f z θ
      = Work.Spaces.DthIter m f z θ
        - ∑ r ∈ Finset.range m,
            selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ := by
    rw [hexp, Finset.sum_range_succ, hself]
    ring
  have habs : |(Real.sin (2 * θ)) ^ m * Work.Spaces.pthIter m f z θ|
      = (Real.sin (2 * θ)) ^ m * |Work.Spaces.pthIter m f z θ| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hs.le m)]
  rw [← habs, hsplit]
  have htri : |Work.Spaces.DthIter m f z θ
        - ∑ r ∈ Finset.range m,
            selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ|
      ≤ |Work.Spaces.DthIter m f z θ|
        + ∑ r ∈ Finset.range m,
            |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ| := by
    have h1 : |Work.Spaces.DthIter m f z θ
          - ∑ r ∈ Finset.range m,
              selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ|
        ≤ |Work.Spaces.DthIter m f z θ|
          + |∑ r ∈ Finset.range m,
              selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ| := by
      simpa using abs_sub_le (Work.Spaces.DthIter m f z θ) 0
        (∑ r ∈ Finset.range m,
          selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ)
    have h2 : |∑ r ∈ Finset.range m,
          selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ|
        ≤ ∑ r ∈ Finset.range m,
            |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      exact le_of_eq (Finset.sum_congr rfl fun r _ => abs_mul _ _)
    exact le_trans h1 (add_le_add le_rfl h2)
  refine le_trans htri ?_
  have h0 : (∑ r ∈ Finset.range m,
        |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ|)
      = ∑ r ∈ Finset.Icc 1 (m - 1),
          |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ| := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simp
    · have hmem : 0 ∈ Finset.range m := Finset.mem_range.mpr hmpos
      have hset : (Finset.range m).erase 0 = Finset.Icc 1 (m - 1) := by
        ext r
        simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
        omega
      have h1 : (∑ r ∈ (Finset.range m).erase 0,
            |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ|)
          + |selfdth.dthCoef m 0 θ| * |Work.Spaces.pthIter 0 f z θ|
          = ∑ r ∈ Finset.range m,
            |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ| :=
        Finset.sum_erase_add (Finset.range m)
          (fun r => |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ|) hmem
      rw [hset, dthCoef_apply_zero hmpos] at h1
      simp only [abs_zero, zero_mul, add_zero] at h1
      exact h1.symm
  rw [h0]
  have hb : ∀ r ∈ Finset.Icc 1 (m - 1),
      |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ|
        ≤ (1 + ∑ i ∈ Finset.range (m + 1), K i)
          * ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) := by
    intro r hr
    obtain ⟨hr1, hrle⟩ := Finset.mem_Icc.mp hr
    have hr' : r ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    have hKle : K r ≤ 1 + ∑ i ∈ Finset.range (m + 1), K i := by
      have := Finset.single_le_sum (fun i _ => (hKpos i).le) hr'
      linarith
    have hbb := hKbd r θ
    rw [abs_of_pos hs] at hbb
    have hspow : 0 ≤ (Real.sin (2 * θ)) ^ r := pow_nonneg hs.le r
    calc |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ|
        ≤ (K r * (Real.sin (2 * θ)) ^ r) * |Work.Spaces.pthIter r f z θ| := by
          exact mul_le_mul_of_nonneg_right hbb (abs_nonneg _)
      _ = K r * ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) := by ring
      _ ≤ (1 + ∑ i ∈ Finset.range (m + 1), K i)
            * ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) :=
          mul_le_mul_of_nonneg_right hKle (mul_nonneg hspow (abs_nonneg _))
  calc |Work.Spaces.DthIter m f z θ|
        + ∑ r ∈ Finset.Icc 1 (m - 1),
            |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ|
      ≤ |Work.Spaces.DthIter m f z θ|
        + ∑ r ∈ Finset.Icc 1 (m - 1),
            (1 + ∑ i ∈ Finset.range (m + 1), K i)
              * ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) :=
        add_le_add le_rfl (Finset.sum_le_sum hb)
    _ ≤ (1 + ∑ i ∈ Finset.range (m + 1), K i)
          * (|Work.Spaces.DthIter m f z θ|
            + ∑ r ∈ Finset.Icc 1 (m - 1),
                (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) := by
        have h1 : (1 : ℝ) ≤ 1 + ∑ i ∈ Finset.range (m + 1), K i := by linarith
        have hA : |Work.Spaces.DthIter m f z θ|
            ≤ (1 + ∑ i ∈ Finset.range (m + 1), K i) * |Work.Spaces.DthIter m f z θ| :=
          le_mul_of_one_le_left (abs_nonneg _) h1
        have hB : ∑ r ∈ Finset.Icc 1 (m - 1),
            (1 + ∑ i ∈ Finset.range (m + 1), K i)
              * ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|)
            = (1 + ∑ i ∈ Finset.range (m + 1), K i)
              * ∑ r ∈ Finset.Icc 1 (m - 1),
                  (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ| := by
          rw [Finset.mul_sum]
        rw [hB]
        linarith [hA]

/-- **Elimination of the lower order terms.**  For `m ≥ 1` there is `C > 0` such that for every
`f` which is `C^∞` at `(z,θ)` and every `θ ∈ (0,π/2)`,

  `sin(2θ)^m |∂_θ^m f(z,θ)| ≤ C Σ_{1 ≤ q ≤ m} |D_θ^q f(z,θ)|`. -/
private theorem elimination (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry f) (z, θ)) →
      (Real.sin (2 * θ)) ^ m * |Work.Spaces.pthIter m f z θ|
        ≤ C * ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ| := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨C, hCpos, hC⟩ := sharp_reverse m
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · -- `m = 1`
      have hm1 : m = 1 := by omega
      subst hm1
      refine ⟨C, hCpos, fun f z θ hθ hf => ?_⟩
      have h := hC f z θ hθ hf
      have h0 : (∑ r ∈ Finset.Icc 1 (1 - 1),
          (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) = 0 := by
        rw [show (Finset.Icc 1 (1 - 1)) = (∅ : Finset ℕ) from by decide, Finset.sum_empty]
      rw [h0, add_zero] at h
      have h1 : (∑ q ∈ Finset.Icc 1 1, |Work.Spaces.DthIter q f z θ|)
          = |Work.Spaces.DthIter 1 f z θ| := by
        rw [show (Finset.Icc 1 1) = ({1} : Finset ℕ) from by decide, Finset.sum_singleton]
      rw [h1]
      simpa using h
    · -- `m ≥ 2`: use the sharpened reverse bound and the induction hypothesis
      have hfac : ∀ r : ℕ, ∃ Cr : ℝ, 0 < Cr ∧ (r ∈ Finset.Icc 1 (m - 1) →
          ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
            (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry f) (z, θ)) →
            (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|
              ≤ Cr * ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ|) := by
        intro r
        by_cases hr : r ∈ Finset.Icc 1 (m - 1)
        · obtain ⟨hr1, hrle⟩ := Finset.mem_Icc.mp hr
          have hrm : r < m := by omega
          obtain ⟨Cr, hCrpos, hCr⟩ := ih r hrm hr1
          refine ⟨Cr, hCrpos, fun _ f z θ hθ hf => ?_⟩
          have hsub : Finset.Icc 1 r ⊆ Finset.Icc 1 m := by
            intro q hq
            obtain ⟨hq1, hqr⟩ := Finset.mem_Icc.mp hq
            exact Finset.mem_Icc.mpr ⟨hq1, by omega⟩
          have hmono : (∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q f z θ|)
              ≤ ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ| :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => abs_nonneg _)
          exact le_trans (hCr f z θ hθ hf) (mul_le_mul_of_nonneg_left hmono hCrpos.le)
        · exact ⟨1, one_pos, fun h => absurd h hr⟩
      choose C' hC'pos hC' using hfac
      have hC'nn : (0 : ℝ) ≤ ∑ r ∈ Finset.Icc 1 (m - 1), C' r :=
        Finset.sum_nonneg fun r _ => (hC'pos r).le
      refine ⟨C * (1 + ∑ r ∈ Finset.Icc 1 (m - 1), C' r),
        by nlinarith [hCpos, hC'nn], fun f z θ hθ hf => ?_⟩
      have h := hC f z θ hθ hf
      have hb : ∑ r ∈ Finset.Icc 1 (m - 1), (Real.sin (2 * θ)) ^ r
            * |Work.Spaces.pthIter r f z θ|
          ≤ (∑ r ∈ Finset.Icc 1 (m - 1), C' r)
              * ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ| := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun r hr => hC' r hr f z θ hθ hf
      have hDm : |Work.Spaces.DthIter m f z θ|
          ≤ ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ| := by
        have hm' : m ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨hm, le_refl m⟩
        exact Finset.single_le_sum (s := Finset.Icc 1 m)
          (f := fun q => |Work.Spaces.DthIter q f z θ|) (fun q _ => abs_nonneg _) hm'
      calc (Real.sin (2 * θ)) ^ m * |Work.Spaces.pthIter m f z θ|
          ≤ C * (|Work.Spaces.DthIter m f z θ|
              + ∑ r ∈ Finset.Icc 1 (m - 1), (Real.sin (2 * θ)) ^ r
                  * |Work.Spaces.pthIter r f z θ|) := h
        _ ≤ C * ((∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ|)
              + (∑ r ∈ Finset.Icc 1 (m - 1), C' r)
                * ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ|) :=
            mul_le_mul_of_nonneg_left (add_le_add hDm hb) hCpos.le
        _ = C * (1 + ∑ r ∈ Finset.Icc 1 (m - 1), C' r)
              * ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ| := by ring

/-! ## Iterated derivatives: coefficient extraction, congruence, commutation

The next lemmas are the pointwise calculus needed to compare the weighted slots of the
`ℋ^k`-integrands with the plain `θ`-derivatives appearing in the expansion of `D_θ^k`. -/

/-- Two functions agree on the open quadrant. -/
private def EqQ (f g : ℝ → ℝ → ℝ) : Prop := ∀ z θ : ℝ, (z, θ) ∈ QQ → f z θ = g z θ

/-- Extracting a `z`-dependent coefficient from the iterated `θ`-derivative. -/
private theorem pthIter_const_mul_z (m : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter m (fun z θ => c z * g z θ)
      = fun z θ => c z * Work.Spaces.pthIter m g z θ := by
  induction m with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      funext z θ
      show deriv (fun θ' => c z * Work.Spaces.pthIter k g z θ') θ
        = c z * deriv (fun θ' => Work.Spaces.pthIter k g z θ') θ
      rw [deriv_const_mul_field]

/-- `pthIter (m+n) f = pthIter m (pthIter n f)`. -/
private theorem pthIter_add' (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- Extracting a `θ`-dependent coefficient from the plain `z`-derivative. -/
private theorem pz_const_mul_th (a : ℝ → ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => a θ * h z θ) z θ = a θ * Work.Spaces.pz h z θ := by
  show deriv (fun z' => a θ * h z' θ) z = a θ * deriv (fun z' => h z' θ) z
  rw [deriv_const_mul_field]

/-- `z² ∂_z² Φ = D_z² Φ - D_z Φ`, at a point where the `z`-slice of `∂_z Φ` is differentiable. -/
private theorem zsq_pzIter2_eq (Φ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Φ z' θ) z) :
    z ^ 2 * Work.Spaces.pzIter 2 Φ z θ
      = Work.Spaces.DzIter 2 Φ z θ - Work.Spaces.DzIter 1 Φ z θ := by
  have heq : (fun z' : ℝ => z' * Work.Spaces.pz Φ z' θ)
      = id * (fun z' => Work.Spaces.pz Φ z' θ) := rfl
  have hd : deriv (id * (fun z' => Work.Spaces.pz Φ z' θ)) z
      = 1 * Work.Spaces.pz Φ z θ + z * Work.Spaces.pzIter 2 Φ z θ := by
    rw [deriv_mul differentiableAt_id h, deriv_id]
    rfl
  rw [show Work.Spaces.DzIter 2 Φ z θ
        = z * deriv (id * (fun z' => Work.Spaces.pz Φ z' θ)) z from by
      show z * deriv (fun z' => z' * Work.Spaces.pz Φ z' θ) z = _
      rw [heq],
    show Work.Spaces.DzIter 1 Φ z θ = z * Work.Spaces.pz Φ z θ from rfl, hd]
  ring

/-! ## Congruence on the open quadrant -/

private theorem pth_congr_QQ {f g : ℝ → ℝ → ℝ} (h : EqQ f g) {z θ : ℝ} (hz : (z, θ) ∈ QQ) :
    Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ QQ :=
    (Continuous.prodMk_right z).continuousAt.eventually (isOpen_QQ.mem_nhds hz)
  have hslice : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ') := by
    filter_upwards [hnb] with θ' hθ'
    exact h z θ' hθ'
  have hder := hslice.deriv_eq
  simpa only [Work.Spaces.pth] using hder

private theorem pz_congr_QQ {f g : ℝ → ℝ → ℝ} (h : EqQ f g) {z θ : ℝ} (hz : (z, θ) ∈ QQ) :
    Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ QQ :=
    (Continuous.prodMk_left θ).continuousAt.eventually (isOpen_QQ.mem_nhds hz)
  have hslice : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun z' => g z' θ) := by
    filter_upwards [hnb] with z' hz'
    exact h z' θ hz'
  have hder := hslice.deriv_eq
  simpa only [Work.Spaces.pz] using hder

private theorem Dth_congr_QQ {f g : ℝ → ℝ → ℝ} (h : EqQ f g) {z θ : ℝ} (hz : (z, θ) ∈ QQ) :
    Work.Spaces.Dth f z θ = Work.Spaces.Dth g z θ :=
  congrArg (fun t => Real.sin (2 * θ) * t) (pth_congr_QQ h hz)

private theorem pthIter_congr_QQ (m : ℕ) {f g : ℝ → ℝ → ℝ} (h : EqQ f g) :
    EqQ (Work.Spaces.pthIter m f) (Work.Spaces.pthIter m g) := by
  induction m with
  | zero => exact h
  | succ k ih => intro z θ hz; exact pth_congr_QQ ih hz



/-! ## Smoothness of the iterates on the open quadrant -/

private theorem pthIter_smooth {G : ℝ → ℝ → ℝ} (hG : SmoothOpen G) (m : ℕ) :
    SmoothOpen (Work.Spaces.pthIter m G) := by
  induction m with
  | zero => simpa using hG
  | succ k ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

private theorem zsq_pzIter2_smooth {G : ℝ → ℝ → ℝ} (hG : SmoothOpen G) :
    SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 G z θ) := by
  have h1 : SmoothOpen (Work.Spaces.pzIter 2 G) := hG.pzIter 2
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  exact h2.mul h1

/-! ## Commutation of the `θ`-derivatives with the `z`-derivatives -/

private theorem pz_pth_comm_pt {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    Work.Spaces.pz (Work.Spaces.pth f) z θ = Work.Spaces.pth (Work.Spaces.pz f) z θ :=
  Work.Spaces.pz_pth_comm h

private theorem pth_pz_comm_pt {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    Work.Spaces.pth (Work.Spaces.pz f) z θ = Work.Spaces.pz (Work.Spaces.pth f) z θ :=
  (pz_pth_comm_pt h).symm


/-- `D_θ` commutes with `∂_z`. -/
private theorem Dth_pz_comm_pt {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Spaces.Dth (Work.Spaces.pz g) z θ = Work.Spaces.pz (Work.Spaces.Dth g) z θ := by
  have h1 : Work.Spaces.Dth (Work.Spaces.pz g) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.pz g) z θ := rfl
  have h2 : Work.Spaces.pz (Work.Spaces.Dth g) z θ
      = Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth g) z θ :=
    pz_const_mul_th (fun θ => Real.sin (2 * θ)) (Work.Spaces.pth g) z θ
  rw [h1, pth_pz_comm_pt h, h2]

/-- `∂_θ^m` commutes with `∂_z` on the open quadrant. -/
private theorem pthIter_pz_comm_QQ (m : ℕ) {G : ℝ → ℝ → ℝ} (hG : SmoothOpen G) :
    EqQ (Work.Spaces.pthIter m (Work.Spaces.pz G)) (Work.Spaces.pz (Work.Spaces.pthIter m G)) := by
  induction m with
  | zero => intro z θ _; rfl
  | succ k ih =>
      intro z θ hy
      rw [Work.Spaces.pthIter_succ, pth_congr_QQ ih hy]
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pthIter k G)) (z, θ) :=
        ((pthIter_smooth hG k).forall 2).contDiffAt (isOpen_QQ.mem_nhds hy)
      rw [pth_pz_comm_pt hcd]
      rfl

/-- `D_θ` commutes with `∂_z^j` on the open quadrant. -/
private theorem Dth_pzIter_comm_QQ (j : ℕ) {G : ℝ → ℝ → ℝ} (hG : SmoothOpen G) :
    EqQ (Work.Spaces.Dth (Work.Spaces.pzIter j G))
      (Work.Spaces.pzIter j (Work.Spaces.Dth G)) := by
  induction j with
  | zero => intro z θ _; rfl
  | succ k ih =>
      intro z θ hy
      rw [Work.Spaces.pzIter_succ,
        Dth_pz_comm_pt (((hG.pzIter k).forall 2).contDiffAt (isOpen_QQ.mem_nhds hy)),
        pz_congr_QQ ih hy]
      rfl

/-- `D_θ^m` commutes with `∂_z^j` on the open quadrant. -/
private theorem DthIter_pzIter_comm_QQ (m j : ℕ) {G : ℝ → ℝ → ℝ} (hG : SmoothOpen G) :
    EqQ (Work.Spaces.DthIter m (Work.Spaces.pzIter j G))
      (Work.Spaces.pzIter j (Work.Spaces.DthIter m G)) := by
  induction m with
  | zero => intro z θ _; rfl
  | succ k ih =>
      intro z θ hy
      rw [Work.Spaces.DthIter_succ, Dth_congr_QQ ih hy,
        Dth_pzIter_comm_QQ j (hG.DthIter k) z θ hy]
      rfl

/-- `∂_θ^m` commutes with `∂_z^j` on the open quadrant. -/
private theorem pthIter_pzIter_comm_QQ (m j : ℕ) {G : ℝ → ℝ → ℝ} (hG : SmoothOpen G) :
    EqQ (Work.Spaces.pthIter m (Work.Spaces.pzIter j G))
      (Work.Spaces.pzIter j (Work.Spaces.pthIter m G)) := by
  induction j with
  | zero => intro z θ _; rfl
  | succ k ih =>
      intro z θ hy
      rw [Work.Spaces.pzIter_succ, pthIter_pz_comm_QQ m (hG.pzIter k) z θ hy,
        pz_congr_QQ ih hy]
      rfl

/-! ## Two elementary summation bounds -/


/-- A crude bound for the cardinality of `Icc a b`. -/
private theorem card_Icc_le (a b C : ℕ) (h : b < C) : ((Finset.Icc a b).card : ℝ) ≤ (C : ℝ) := by
  have h1 : (Finset.Icc a b).card ≤ C := by
    have := Finset.card_le_card (s := Finset.Icc a b) (t := Finset.range C)
      (fun x hx => by
        obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp hx
        exact Finset.mem_range.mpr (by omega))
    simpa [Finset.card_range] using this
  exact_mod_cast h1

/-! ## The pointwise bound on the open quadrant

Write `A = z²∂_z²Ψ` and `B = ∂_θθΨ`.  On the open quadrant the exact expansion of `D_θ^k` gives
`D_θ^k A = Σ_{r ≤ k} a_{k,r}(θ) ∂_θ^r A`, with `a_{k,0} = 0` and `|a_{k,r}| ≤ K sin(2θ)^r`.  Each
term is compared with slots of the two `ℋ^{k-1}`-integrands of `A` and of `D_z B`:

* for `1 ≤ r ≤ k-1` the elimination of the lower order terms applied to `A` gives
  `sin(2θ)^r |∂_θ^r A| ≤ C Σ_{1 ≤ q ≤ r} |D_θ^q A|`;
* for `r = k` one writes `∂_θ^k A = z²∂_z²(∂_θ^kΨ) = z²D_θ^{k-2}∂_z²B` and applies the
  elimination to `∂_z²B`, whose `D_θ^q`-derivatives are the slots of `D_z B`. -/

/-- **The pointwise bound**: on the open quadrant, `(D_θ^k A · Wt)²` is dominated by the sum of
the two `ℋ^{k-1}`-integrands of `A` and of `D_z B`. -/
private theorem A_top_pointwise (k : ℕ) (hk : 3 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (Ψ : ℝ → ℝ → ℝ), SmoothOpen Ψ → ∀ z θ : ℝ, (z, θ) ∈ QQ →
      (Work.Spaces.DthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          * Work.Spaces.Wt α z θ) ^ 2
        ≤ K * (Work.Spaces.HkIntegrand α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            + Work.Spaces.HkIntegrand α (k - 1)
              (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ) := by
  classical
  choose Kc hKcpos hKcbd using fun r => selfdth.DthCoef_sin_pow_bound k r
  have hKcNn : (0 : ℝ) ≤ ∑ r ∈ Finset.range (k + 1), Kc r :=
    Finset.sum_nonneg fun r _ => (hKcpos r).le
  have hE : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ (1 ≤ m → ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry f) (z, θ)) →
      (Real.sin (2 * θ)) ^ m * |Work.Spaces.pthIter m f z θ|
        ≤ C * ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ|) := by
    intro m
    by_cases hm : 1 ≤ m
    · obtain ⟨C, hCpos, hC⟩ := elimination m hm
      exact ⟨C, hCpos, fun _ => hC⟩
    · exact ⟨1, one_pos, fun h => absurd h hm⟩
  choose Ce hCepos hCe using hE
  have hCeNn : (0 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 (k - 1), Ce m :=
    Finset.sum_nonneg fun m _ => (hCepos m).le
  set Km : ℝ := (∑ r ∈ Finset.range (k + 1), Kc r) + 1 with hKm
  set Ke : ℝ := (∑ m ∈ Finset.Icc 1 (k - 1), Ce m) + 1 with hKe
  have hKm1 : 1 ≤ Km := by rw [hKm]; linarith
  have hKe1 : 1 ≤ Ke := by rw [hKe]; linarith
  have hKmnn : 0 ≤ Km := le_trans zero_le_one hKm1
  have hKenn : 0 ≤ Ke := le_trans zero_le_one hKe1
  refine ⟨(((k : ℝ) + 3) ^ 4 * (Km * Ke) ^ 2 * 16) + 1, by positivity, ?_⟩
  intro α Ψ hΨ z θ hz
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := hz.2
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem hθ
  have hspos : 0 ≤ Real.sin (2 * θ) := hs.le
  have hwt : 0 ≤ Work.Spaces.Wt α z θ := by
    rw [Work.Spaces.Wt, Work.Spaces.w, Work.Spaces.wTheta]
    refine mul_nonneg (div_nonneg (by positivity) (by positivity)) ?_
    exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
      by linarith [hθ.2, Real.pi_pos]⟩) _
  set A : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hAdef
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hBdef
  have hA_sm : SmoothOpen A := zsq_pzIter2_smooth hΨ
  have hB_sm : SmoothOpen B := pthIter_smooth hΨ 2
  have hAcd : ∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry A) (z, θ) :=
    fun n => (hA_sm.forall n).contDiffAt (isOpen_QQ.mem_nhds hz)
  have hB2cd : ∀ n : ℕ, ContDiffAt ℝ n
      (Function.uncurry (Work.Spaces.pzIter 2 B)) (z, θ) :=
    fun n => ((hB_sm.pzIter 2).forall n).contDiffAt (isOpen_QQ.mem_nhds hz)
  set HA : ℝ := Work.Spaces.HkIntegrand α (k - 1) A z θ with hHA
  set HB : ℝ := Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.DzIter 1 B) z θ with hHB
  have hHAnn : 0 ≤ HA := Work.Spaces.HkIntegrand_nonneg α (k - 1) A z θ
  have hHBnn : 0 ≤ HB := Work.Spaces.HkIntegrand_nonneg α (k - 1) (Work.Spaces.DzIter 1 B) z θ
  -- slots of `A`
  have hslotA : ∀ q ∈ Finset.Icc 1 (k - 1),
      (Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ HA := by
    intro q hq
    obtain ⟨hq1, hqk⟩ := Finset.mem_Icc.mp hq
    have h1 : (Work.Spaces.mixed 0 q A z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α (k - 1) A z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α (k - 1) A z θ q 0 hq1 (by omega)
    rw [Work.Spaces.mixed_zero_left] at h1
    rw [hHA]
    exact h1
  -- slots of `D_z B`
  have hcommDz : ∀ (q : ℕ) (z' θ' : ℝ), (z', θ') ∈ QQ →
      Work.Spaces.DthIter q (Work.Spaces.DzIter 1 B) z' θ'
        = Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z' θ' := fun q z' θ' hz' =>
    (Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen B hB_sm q
      (show (z', θ') ∈ Work.FTS.EllipticEst.Q0 from hz')).symm
  have hslotB1 : ∀ q ∈ Finset.Icc 1 (k - 2),
      (Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ HB := by
    intro q hq
    obtain ⟨hq1, hqk⟩ := Finset.mem_Icc.mp hq
    have h1 : (Work.Spaces.mixed 0 q (Work.Spaces.DzIter 1 B) z θ
        * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.DzIter 1 B) z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α (k - 1) (Work.Spaces.DzIter 1 B) z θ q 0 hq1
        (by omega)
    rw [Work.Spaces.mixed_zero_left, hcommDz q z θ hz] at h1
    rw [hHB]
    exact h1
  have hslotB2 : ∀ q ∈ Finset.Icc 1 (k - 2),
      (Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ HB := by
    intro q hq
    obtain ⟨hq1, hqk⟩ := Finset.mem_Icc.mp hq
    have h1 : (Work.Spaces.mixed 1 q (Work.Spaces.DzIter 1 B) z θ
        * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.DzIter 1 B) z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α (k - 1) (Work.Spaces.DzIter 1 B) z θ q 1 hq1
        (by omega)
    have h3 : Work.Spaces.mixed 1 q (Work.Spaces.DzIter 1 B) z θ
        = Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ := by
      have hcongr := Step.DzIter_congr_of_isOpen isOpen_QQ
        (fun y hy => hcommDz q y.1 y.2 hy) 1 hz
      exact hcongr
    rw [h3] at h1
    rw [hHB]
    exact h1
  -- the slot sums
  set SA : ℝ := ∑ q ∈ Finset.Icc 1 (k - 1), |Work.Spaces.DthIter q A z θ| with hSA
  set SB : ℝ := ∑ q ∈ Finset.Icc 1 (k - 2),
    (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ|
      + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ|) with hSB
  have hSAnn : 0 ≤ SA := Finset.sum_nonneg fun q _ => abs_nonneg _
  have hSBnn : 0 ≤ SB := Finset.sum_nonneg fun q _ => by positivity
  -- the two slot sums, by Cauchy-Schwarz
  have hSAW : (SA * Work.Spaces.Wt α z θ) ^ 2
      ≤ ((k : ℝ) + 3) * (((k : ℝ) + 3) * HA) := by
    have hcard : ((Finset.Icc 1 (k - 1)).card : ℝ) ≤ (k : ℝ) + 3 := by
      simpa using card_Icc_le 1 (k - 1) (k + 3) (by omega)
    have heq : SA * Work.Spaces.Wt α z θ
        = ∑ q ∈ Finset.Icc 1 (k - 1),
            |Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ| := by
      rw [hSA, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [abs_mul, abs_of_nonneg hwt]
    rw [heq]
    have hsq : ∀ q ∈ Finset.Icc 1 (k - 1),
        (|Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ|) ^ 2 ≤ HA := by
      intro q hq
      simpa only [sq_abs] using hslotA q hq
    have h2 : (∑ q ∈ Finset.Icc 1 (k - 1),
          (|Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ|) ^ 2)
        ≤ ((k : ℝ) + 3) * HA := by
      calc (∑ q ∈ Finset.Icc 1 (k - 1),
            (|Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ|) ^ 2)
          ≤ ∑ _q ∈ Finset.Icc 1 (k - 1), HA := Finset.sum_le_sum hsq
        _ = ((Finset.Icc 1 (k - 1)).card : ℝ) * HA := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((k : ℝ) + 3) * HA := mul_le_mul_of_nonneg_right hcard hHAnn
    calc (∑ q ∈ Finset.Icc 1 (k - 1),
          |Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ|) ^ 2
        ≤ ((Finset.Icc 1 (k - 1)).card : ℝ)
          * ∑ q ∈ Finset.Icc 1 (k - 1),
              (|Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ|) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ ((k : ℝ) + 3) * (((k : ℝ) + 3) * HA) :=
          mul_le_mul hcard h2 (by positivity) (by positivity)
  have hSBW : (SB * Work.Spaces.Wt α z θ) ^ 2
      ≤ ((k : ℝ) + 3) * (((k : ℝ) + 3) * (4 * HB)) := by
    have hcard : ((Finset.Icc 1 (k - 2)).card : ℝ) ≤ (k : ℝ) + 3 := by
      simpa using card_Icc_le 1 (k - 2) (k + 3) (by omega)
    have heq : SB * Work.Spaces.Wt α z θ
        = ∑ q ∈ Finset.Icc 1 (k - 2),
            (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|
              + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
                * Work.Spaces.Wt α z θ|) := by
      rw [hSB, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [add_mul, abs_mul, abs_of_nonneg hwt]
    rw [heq]
    have hsq : ∀ q ∈ Finset.Icc 1 (k - 2),
        (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|
          + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|) ^ 2
        ≤ 4 * HB := by
      intro q hq
      have h2 : (Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ
          * Work.Spaces.Wt α z θ) ^ 2 ≤ HB := hslotB2 q hq
      have h3 : (Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
          * Work.Spaces.Wt α z θ) ^ 2 ≤ HB := hslotB1 q hq
      have h4 : |Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ| ^ 2
          ≤ HB := by simpa only [sq_abs] using h2
      have h5 : |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ| ^ 2
          ≤ HB := by simpa only [sq_abs] using h3
      have h7 : (0:ℝ) ≤ |Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ
          * Work.Spaces.Wt α z θ| := abs_nonneg _
      have h8 : (0:ℝ) ≤ |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
          * Work.Spaces.Wt α z θ| := abs_nonneg _
      nlinarith [h4, h5, h7, h8]
    have h2 : (∑ q ∈ Finset.Icc 1 (k - 2),
          (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|
            + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
              * Work.Spaces.Wt α z θ|) ^ 2) ≤ ((k : ℝ) + 3) * (4 * HB) := by
      calc (∑ q ∈ Finset.Icc 1 (k - 2),
            (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|
              + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
                * Work.Spaces.Wt α z θ|) ^ 2)
          ≤ ∑ _q ∈ Finset.Icc 1 (k - 2), (4 * HB) := Finset.sum_le_sum hsq
        _ = ((Finset.Icc 1 (k - 2)).card : ℝ) * (4 * HB) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((k : ℝ) + 3) * (4 * HB) := mul_le_mul_of_nonneg_right hcard (by positivity)
    calc (∑ q ∈ Finset.Icc 1 (k - 2),
          (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|
            + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
              * Work.Spaces.Wt α z θ|)) ^ 2
        ≤ ((Finset.Icc 1 (k - 2)).card : ℝ)
          * ∑ q ∈ Finset.Icc 1 (k - 2),
              (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|
                + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
                  * Work.Spaces.Wt α z θ|) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ ((k : ℝ) + 3) * (((k : ℝ) + 3) * (4 * HB)) :=
          mul_le_mul hcard h2 (by positivity) (by positivity)
  have hA2 : ∀ z' θ' : ℝ, (z', θ') ∈ QQ → Work.Spaces.pthIter 2 A z' θ'
      = z' ^ 2 * Work.Spaces.pzIter 2 B z' θ' := by
    intro z' θ' hz'
    have e1 : Work.Spaces.pthIter 2 A
        = fun z θ => z ^ 2 * Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ := by
      rw [hAdef]
      exact pthIter_const_mul_z 2 (fun z => z ^ 2) (Work.Spaces.pzIter 2 Ψ)
    have hv := congrFun (congrFun e1 z') θ'
    rw [hv, pthIter_pzIter_comm_QQ 2 2 hΨ z' θ' hz']
  -- the term-by-term bound
  have hterm : ∀ r ∈ Finset.Icc 1 k,
      (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r A z θ| ≤ Ke * (SA + SB) := by
    have keyk : (Real.sin (2 * θ)) ^ k * |Work.Spaces.pthIter k A z θ| ≤ Ke * (SA + SB) := by
      -- the value of `∂_θ^k A` in terms of `∂_z² (∂_θ^{k-2} ∂_θ² Ψ)`
      have h2k : 2 ≤ k := by omega
      have e1 : Work.Spaces.pthIter k A
          = Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 A) := by
        have h := pthIter_add' (k - 2) 2 A
        rw [Nat.sub_add_cancel h2k] at h
        exact h
      have e3 := pthIter_const_mul_z (k - 2) (fun z => z ^ 2) (Work.Spaces.pzIter 2 B)
      have e5 : Work.Spaces.pthIter (k - 2) B = Work.Spaces.pthIter k Ψ := by
        have h := pthIter_add' (k - 2) 2 Ψ
        rw [Nat.sub_add_cancel h2k] at h
        rw [hBdef]
        exact h.symm
      have hcong := pthIter_congr_QQ (k - 2) (f := Work.Spaces.pthIter 2 A)
        (g := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 B z θ)
        (fun z' θ' hz' => hA2 z' θ' hz')
      have e4 : ∀ z' θ' : ℝ, (z', θ') ∈ QQ →
          Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z' θ'
            = Work.Spaces.pzIter 2 (Work.Spaces.pthIter (k - 2) B) z' θ' :=
        fun z' θ' hz' => pthIter_pzIter_comm_QQ (k - 2) 2 hB_sm z' θ' hz'
      have h1 : Work.Spaces.pthIter k A z θ
          = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter k Ψ) z θ := by
        calc Work.Spaces.pthIter k A z θ
            = Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 A) z θ := by rw [e1]
          _ = Work.Spaces.pthIter (k - 2)
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 B z θ) z θ := hcong z θ hz
          _ = z ^ 2 * Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ := by rw [e3]
          _ = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter (k - 2) B) z θ := by
              rw [e4 z θ hz]
          _ = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter k Ψ) z θ := by rw [e5]
      have h2 := hCe (k - 2) (by omega) (Work.Spaces.pzIter 2 B) z θ hθ hB2cd
      have h3 : ∀ q : ℕ, Work.Spaces.DthIter q (Work.Spaces.pzIter 2 B) z θ
          = Work.Spaces.pzIter 2 (Work.Spaces.DthIter q B) z θ := fun q =>
        DthIter_pzIter_comm_QQ q 2 hB_sm z θ hz
      have h4 : ∀ q : ℕ, z ^ 2 * |Work.Spaces.pzIter 2 (Work.Spaces.DthIter q B) z θ|
          ≤ |Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ|
            + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ| := by
        intro q
        have hdiff : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DthIter q B) z θ
            = Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ
              - Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ :=
          zsq_pzIter2_eq (Work.Spaces.DthIter q B)
            (((hB_sm.DthIter q).pz).hasDerivAt_slice hθ hz.1).differentiableAt
        have hshow : z ^ 2 * |Work.Spaces.pzIter 2 (Work.Spaces.DthIter q B) z θ|
            = |z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DthIter q B) z θ| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ z ^ 2)]
        rw [hshow, hdiff]
        have ha := le_abs_self (Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ)
        have ha' := neg_le_abs (Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ)
        have hb := le_abs_self (Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ)
        have hb' := neg_le_abs (Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ)
        exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      have h5z : z ^ 2 * ∑ q ∈ Finset.Icc 1 (k - 2),
            |Work.Spaces.DthIter q (Work.Spaces.pzIter 2 B) z θ| ≤ SB := by
        rw [Finset.mul_sum, hSB]
        refine Finset.sum_le_sum fun q hq => ?_
        rw [h3 q]
        exact h4 q
      have hstep : z ^ 2 * ((Real.sin (2 * θ)) ^ (k - 2)
            * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|)
          ≤ z ^ 2 * (Ce (k - 2) * ∑ q ∈ Finset.Icc 1 (k - 2),
              |Work.Spaces.DthIter q (Work.Spaces.pzIter 2 B) z θ|) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg z)
      have hstep' : z ^ 2 * (Ce (k - 2) * ∑ q ∈ Finset.Icc 1 (k - 2),
              |Work.Spaces.DthIter q (Work.Spaces.pzIter 2 B) z θ|)
          = Ce (k - 2) * (z ^ 2 * ∑ q ∈ Finset.Icc 1 (k - 2),
              |Work.Spaces.DthIter q (Work.Spaces.pzIter 2 B) z θ|) := by ring
      have hfin : z ^ 2 * ((Real.sin (2 * θ)) ^ (k - 2)
            * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|)
          ≤ Ce (k - 2) * SB := by
        rw [hstep'] at hstep
        exact le_trans hstep (mul_le_mul_of_nonneg_left h5z (hCepos (k - 2)).le)
      have hpow : (Real.sin (2 * θ)) ^ k
          = ((Real.sin (2 * θ)) ^ (k - 2)) * (Real.sin (2 * θ)) ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
        nlinarith [Real.sin_le_one (2 * θ), hspos]
      have hkey1 : |Work.Spaces.pzIter 2 (Work.Spaces.pthIter k Ψ) z θ|
          = |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ| := by
        rw [← e5]
        exact congrArg (fun t => |t|) (e4 z θ hz).symm
      have hfin2 : (Real.sin (2 * θ)) ^ k * |Work.Spaces.pthIter k A z θ|
          ≤ z ^ 2 * ((Real.sin (2 * θ)) ^ (k - 2)
              * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|) := by
        rw [h1, abs_mul, abs_of_nonneg (sq_nonneg z), hpow, hkey1]
        rw [show ((Real.sin (2 * θ)) ^ (k - 2) * (Real.sin (2 * θ)) ^ 2)
              * (z ^ 2 * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|)
            = z ^ 2 * ((Real.sin (2 * θ)) ^ (k - 2)
              * ((Real.sin (2 * θ)) ^ 2
                * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|)) from by ring]
        have hsp : 0 ≤ (Real.sin (2 * θ)) ^ (k - 2) := pow_nonneg hspos _
        have hpn : 0 ≤ |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ| := abs_nonneg _
        have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
        have hs2' : (Real.sin (2 * θ)) ^ 2
            * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|
            ≤ |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ| :=
          mul_le_of_le_one_left hpn hs2
        have h1' : (Real.sin (2 * θ)) ^ (k - 2)
            * ((Real.sin (2 * θ)) ^ 2
              * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|)
            ≤ (Real.sin (2 * θ)) ^ (k - 2)
              * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ| :=
          mul_le_mul_of_nonneg_left hs2' hsp
        exact mul_le_mul_of_nonneg_left h1' hz2
      have hCen : Ce (k - 2) ≤ Ke := by
        rw [hKe]
        have hmem : k - 2 ∈ Finset.Icc 1 (k - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have := Finset.single_le_sum (fun m _ => (hCepos m).le) hmem
        linarith
      refine le_trans hfin2 (le_trans hfin ?_)
      have hcenn : 0 ≤ Ce (k - 2) := (hCepos (k - 2)).le
      nlinarith [hCen, hcenn, hSAnn, hSBnn]
    intro r hr
    obtain ⟨hr1, hrk⟩ := Finset.mem_Icc.mp hr
    rcases lt_or_eq_of_le hrk with hrlt | hreq
    · have hCr : Ce r ≤ Ke := by
        rw [hKe]
        have hrmem : r ∈ Finset.Icc 1 (k - 1) := Finset.mem_Icc.mpr ⟨hr1, by omega⟩
        have := Finset.single_le_sum (fun m _ => (hCepos m).le) hrmem
        linarith
      have h1 := hCe r hr1 A z θ hθ hAcd
      have h2 : (∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q A z θ|) ≤ SA := by
        rw [hSA]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => abs_nonneg _)
        intro q hq
        obtain ⟨hq1, hqr⟩ := Finset.mem_Icc.mp hq
        exact Finset.mem_Icc.mpr ⟨hq1, by omega⟩
      have hsum_nn : 0 ≤ ∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q A z θ| :=
        Finset.sum_nonneg fun q _ => abs_nonneg _
      have hCrnn : 0 ≤ Ce r := (hCepos r).le
      have hstep : (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r A z θ|
          ≤ Ce r * ∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q A z θ| := h1
      have hstep2 : Ce r * (∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q A z θ|)
          ≤ Ke * SA := by
        have hk1 : Ce r * (∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q A z θ|)
            ≤ Ke * (∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q A z θ|) :=
          mul_le_mul_of_nonneg_right hCr hsum_nn
        exact le_trans hk1 (mul_le_mul_of_nonneg_left h2 hKenn)
      exact le_trans (le_trans hstep hstep2) (mul_le_mul_of_nonneg_left (by linarith) hKenn)
    · rw [hreq]
      exact keyk
  -- the expansion
  have hcoef : ∀ r : ℕ, |selfdth.dthCoef k r θ| ≤ Km * (Real.sin (2 * θ)) ^ r := by
    intro r
    rcases lt_or_ge k r with hr | hr
    · have h0 : selfdth.dthCoef k r θ = 0 :=
        congrFun (selfdth.dthCoef_zero_of_gt hr) θ
      rw [h0]
      simp only [abs_zero]
      positivity
    · have hr' : r ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
      have h1 := hKcbd r θ
      rw [abs_of_pos hs] at h1
      have h2 : Kc r ≤ Km := by
        rw [hKm]
        have := Finset.single_le_sum (fun i _ => (hKcpos i).le) hr'
        linarith
      exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (pow_nonneg hspos r))
  have hexp := selfdth.DthIter_expansion_local k A z θ hAcd
  have hstep1 : |Work.Spaces.DthIter k A z θ|
      ≤ Km * ∑ i ∈ Finset.range k,
          (Real.sin (2 * θ)) ^ (i + 1) * |Work.Spaces.pthIter (i + 1) A z θ| := by
    have h := hexp
    rw [Finset.sum_range_succ'] at h
    have hz0 : selfdth.dthCoef k 0 θ * Work.Spaces.pthIter 0 A z θ = 0 := by
      have h0 : selfdth.dthCoef k 0 = fun _ : ℝ => (0 : ℝ) :=
        dthCoef_zero_fun (by omega)
      rw [h0]
      simp
    rw [hz0, add_zero] at h
    rw [h]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc |selfdth.dthCoef k (i + 1) θ * Work.Spaces.pthIter (i + 1) A z θ|
        = |selfdth.dthCoef k (i + 1) θ| * |Work.Spaces.pthIter (i + 1) A z θ| :=
          abs_mul _ _
      _ ≤ (Km * (Real.sin (2 * θ)) ^ (i + 1)) * |Work.Spaces.pthIter (i + 1) A z θ| :=
          mul_le_mul_of_nonneg_right (hcoef (i + 1)) (abs_nonneg _)
      _ = Km * ((Real.sin (2 * θ)) ^ (i + 1)
            * |Work.Spaces.pthIter (i + 1) A z θ|) := by ring
  have hstep2 : Km * ∑ i ∈ Finset.range k,
        (Real.sin (2 * θ)) ^ (i + 1) * |Work.Spaces.pthIter (i + 1) A z θ|
      ≤ Km * ((k : ℝ) * (Ke * (SA + SB))) := by
    refine mul_le_mul_of_nonneg_left ?_ hKmnn
    have hle : ∑ i ∈ Finset.range k,
          (Real.sin (2 * θ)) ^ (i + 1) * |Work.Spaces.pthIter (i + 1) A z θ|
        ≤ ∑ _i ∈ Finset.range k, (Ke * (SA + SB)) :=
      Finset.sum_le_sum fun i hi => by
        refine hterm (i + 1) (Finset.mem_Icc.mpr
          ⟨Nat.succ_le_succ (Nat.zero_le i), by
            have := Finset.mem_range.mp hi; omega⟩)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    exact hle
  have key : (Work.Spaces.DthIter k A z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ (Km * ((k : ℝ) * (Ke * (SA + SB)))) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by
    have habs : |Work.Spaces.DthIter k A z θ| ≤ Km * ((k : ℝ) * (Ke * (SA + SB))) :=
      le_trans hstep1 hstep2
    have hsq : (Work.Spaces.DthIter k A z θ) ^ 2
        ≤ (Km * ((k : ℝ) * (Ke * (SA + SB)))) ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg (Work.Spaces.DthIter k A z θ)) habs
      have h' : |Work.Spaces.DthIter k A z θ| ^ 2
          ≤ (Km * ((k : ℝ) * (Ke * (SA + SB)))) ^ 2 := by
        simpa [pow_two] using h
      rwa [sq_abs] at h'
    calc (Work.Spaces.DthIter k A z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.DthIter k A z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ (Km * ((k : ℝ) * (Ke * (SA + SB)))) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
  have expand : (Km * ((k : ℝ) * (Ke * (SA + SB)))) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      ≤ (Km * ((k : ℝ) * Ke)) ^ 2 * 2
        * ((SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2) := by
    have hfac : (Km * ((k : ℝ) * (Ke * (SA + SB)))) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
        = (Km * ((k : ℝ) * Ke)) ^ 2 * ((SA + SB) * Work.Spaces.Wt α z θ) ^ 2 := by ring
    rw [hfac]
    have h2 : ((SA + SB) * Work.Spaces.Wt α z θ) ^ 2
        ≤ 2 * ((SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2) := by
      have he : (SA + SB) * Work.Spaces.Wt α z θ
          = SA * Work.Spaces.Wt α z θ + SB * Work.Spaces.Wt α z θ := by ring
      have h3 : (SA * Work.Spaces.Wt α z θ + SB * Work.Spaces.Wt α z θ) ^ 2
          ≤ 2 * ((SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2) := by
        nlinarith [sq_nonneg (SA * Work.Spaces.Wt α z θ - SB * Work.Spaces.Wt α z θ)]
      rw [he]
      exact h3
    have hnn : (0 : ℝ) ≤ (Km * ((k : ℝ) * Ke)) ^ 2 := by positivity
    calc (Km * ((k : ℝ) * Ke)) ^ 2 * ((SA + SB) * Work.Spaces.Wt α z θ) ^ 2
        ≤ (Km * ((k : ℝ) * Ke)) ^ 2
            * (2 * ((SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 hnn
      _ = (Km * ((k : ℝ) * Ke)) ^ 2 * 2
            * ((SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2) := by ring
  refine le_trans key (le_trans expand ?_)
  rw [hHA, hHB]
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsum : (SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2
      ≤ ((((k : ℝ) + 3) ^ 2) + (((k : ℝ) + 3) ^ 2 * 4)) * (HA + HB) := by
    have hA' : (SA * Work.Spaces.Wt α z θ) ^ 2 ≤ ((k : ℝ) + 3) ^ 2 * HA := by
      have h := hSAW
      nlinarith [h, hHAnn]
    have hB' : (SB * Work.Spaces.Wt α z θ) ^ 2 ≤ ((k : ℝ) + 3) ^ 2 * (4 * HB) := by
      have h := hSBW
      nlinarith [h, hHBnn]
    nlinarith [hA', hB', hHAnn, hHBnn]
  calc (Km * ((k : ℝ) * Ke)) ^ 2 * 2
        * ((SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2)
      ≤ (Km * ((k : ℝ) * Ke)) ^ 2 * 2
          * (((((k : ℝ) + 3) ^ 2) + (((k : ℝ) + 3) ^ 2 * 4)) * (HA + HB)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (((k : ℝ) + 3) ^ 4 * (Km * Ke) ^ 2 * 16) * (HA + HB) := by
        have h16 : (0:ℝ) ≤ HA + HB := by linarith
        have h17 : (Km * ((k : ℝ) * Ke)) ^ 2 * 2
            * ((((k : ℝ) + 3) ^ 2) + (((k : ℝ) + 3) ^ 2 * 4))
            ≤ ((k : ℝ) + 3) ^ 4 * (Km * Ke) ^ 2 * 16 := by
          have h18 : (0:ℝ) ≤ (k:ℝ) + 3 := by positivity
          have h19 : (0:ℝ) ≤ Km * Ke := by positivity
          nlinarith [h18, h19, hk3, sq_nonneg Km, sq_nonneg Ke, sq_nonneg ((k:ℝ) + 3),
            sq_nonneg (Km * Ke), sq_nonneg (Km * Ke - 1), sq_nonneg ((k:ℝ) - 3)]
        have h20 := mul_le_mul_of_nonneg_right h17 h16
        linarith [h20]
    _ ≤ ((((k : ℝ) + 3) ^ 4 * (Km * Ke) ^ 2 * 16) + 1) * (HA + HB) := by
        have h16 : (0:ℝ) ≤ HA + HB := by linarith
        nlinarith [h16]

/-! ## The measure-theoretic comparison

`Tk_le_of_pointwise` (proved in `Submission.Work.FTS.EllipticEst.remov.ATop.Tk_le_of_pointwise`)
integrates the pointwise bound of `A_top_pointwise` against its honest majorant; it is the
measure-theoretic half of the target below. -/


end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RegQ` is monotone in the order `k`

`Work.FTS.Nonlin.RegQ α k f = SmoothQuad f ∧ HkMem α k f ∧ BdryTraces α k f`.

* `SmoothQuad f` does not mention `k` at all.
* `HkMem α k f` is monotone: the `ℋ^{k+1}`-integrand dominates the `ℋ^k`-integrand, so the
  integrability certificates for the bigger integrand give those for the smaller one
  (`Work.GalerkinFix.RegQ.HkMem_mono_Q`, iterated here).
* `BdryTraces α k f` is a *conjunction over pairs* `a + b ≤ k`, hence weakening `k` weakens the
  condition.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalerkinFix.RegQ

set_option autoImplicit false

/-- Iterated form of `HkMem_mono_Q`: `HkMem` descends in the order, inside the class
`SmoothQuad`. -/
private theorem HkMem_desc {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f)
    (k : ℕ) : ∀ k' : ℕ, k' ≤ k → Work.Spaces.HkMem α k f → Work.Spaces.HkMem α k' f := by
  induction k with
  | zero =>
    intro k' hk h
    obtain rfl : k' = 0 := Nat.le_zero.mp hk
    exact h
  | succ k ih =>
    intro k' hk h
    rcases Nat.eq_or_lt_of_le hk with hEq | hLt
    · subst hEq
      exact h
    · exact ih k' (Nat.lt_succ_iff.mp hLt) (Work.GalerkinFix.RegQ.HkMem_mono_Q hf h)

/-- **The `RegQ`-class is monotone in the order**: `RegQ α k f → RegQ α k' f` for `k' ≤ k`. -/
theorem regQ_mono {α : ℝ} {k k' : ℕ} {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.Nonlin.RegQ α k f) (hk : k' ≤ k) : Work.FTS.Nonlin.RegQ α k' f := by
  obtain ⟨hs, hm, hb⟩ := hf
  exact ⟨hs, HkMem_desc hs k k' hk hm, fun a b hab => hb a b (le_trans hab hk)⟩

end Work.FTS.GalerkinFix.RegQ
end
end
-- ===== merged: Submission.Work.FTS.H2.HQ.LinfQpt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces

namespace Work.FTS.H2.HQ

/-- **Elgindi's Corollary `SecondDerivativesBounded` (tex 1094) in the interior class `RegQ`,
pointwise form.**

For `f` in the interior class `Work.FTS.Nonlin.RegQ α 4` (`= SmoothQuad f ∧ HkMem α 4 f ∧
BdryTraces α 4 f`) and `a + b ≤ 2`, every mixed derivative of order `≤ 2` is bounded on the
*open* quadrant by `C/√(γ-1)·|f|_{ℋ⁴}`, `C` universal.  The bound is claimed only inside the
quadrant: `RegQ` leaves the values on the lines `θ = 0`, `θ = π/2` (and at `z = 0`) free.

The second and third arguments are the interior one-dimensional Hardy inequalities
(`Work.FTS.H2.HQ.HardyThetaQ` — angular, with the `θ → 0⁺` limit of the function as its
vanishing hypothesis — and `Work.FTS.H2.HQ.HardyZQ` — radial, `C¹` on `(0,∞)` with decay at
`∞`), taken as hypotheses so that this statement is independent of them; they are instantiated
from those two files at the point of use.  Everything else the proof needs is in
`Submission/Work/FTS/H2/HQ/Glue.lean`.

Route (as in `Work.Spaces.SupMixedLeH4`/`Linf_H2`, but with the boundary behaviour supplied by
`BdryTraces` instead of `SmoothNbhd`/`VanishTheta`): for `z > 0` and `0 < θ < π/2`,
* apply the angular Hardy inequality to the `θ`-slice `σ ↦ mixed b a f z σ`: its limit at
  `0⁺` is `0` by `Work.FTS.H2.HQ.BdryTraces.tendsto_theta_zero` (the angular clause of
  `BdryTraces` carries the *singular* weight `sin(2θ)^{1-γ}`, hence forces the vanishing), and
  the Hardy integrand `(pth (mixed b a f) z σ)² sin(2σ)^{2-γ}` is integrable because it equals
  `(mixed b (a+1) f z σ · Wt(z,σ))²/w(z)²` on the open quadrant
  (`Work.FTS.H2.HQ.Wt_sq_quad`, the `D_θ`-commutation of `D_z^b` from
  `Work.FTS.LocData.DzDthIterCommOn`/`Work.FTS.H2.HQ.DthIter_mul_quad`, and the slot
  integrability `Work.FTS.H2.HQ.integrableOn_slice_mixed_Wt_sq`);
* apply the radial Hardy inequality to the `z`-slice of `pth (mixed b a f)` (equivalently to
  `mixed b (a+1) f · Wt`), whose decay at `z → ∞` is
  `Work.FTS.H2.HQ.BdryTraces.tendsto_atTop_zero`;
* conclude `(mixed b a f z θ)² ≤ C/(γ-1)·∫∫ (mixed (b+1) (a+1) f · Wt)²` (an `ℋ⁴`-slot,
  `≤ HkSq α 4 f` by `Work.Spaces.L2Sq_mixed_le_HkSq`/`slotM_quad`), using
  `sin(2θ)·sin(2θ)^{-γ} = sin(2θ)^{1-γ}`-type weight algebra and `(b+1)+(a+1) ≤ 4`.
The case `a = 0` is the same chain with the `D_θ`-derivative taken first and the slots
`(b+1, 1)` (for `b ≤ 2`, total order `≤ 4`). -/
theorem LinfQpt : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn) (b a : ℕ),
    0 < α → α ≤ 1 → a + b ≤ 2 → Work.FTS.Nonlin.RegQ α 4 f →
    (∀ (u : ℝ → ℝ → ℝ) (z : ℝ), Work.FTS.LocData.SmoothQuad u → z ∈ Set.Ioi (-1) →
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth u z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ →
      ∀ θ ∈ Set.Ioo 0 (π / 2), (u z θ) ^ 2 ≤
        (100 / (Work.Spaces.gam α - 1)) * MeasureTheory.integral
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (fun σ => (Work.Spaces.pth u z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))) →
    (∀ (v : ℝ → ℝ), ContDiffOn ℝ 1 v (Set.Ioi (0 : ℝ)) →
      Filter.Tendsto v Filter.atTop (nhds 0) →
      MeasureTheory.IntegrableOn (fun s => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)
        Work.Spaces.Iz →
      ∀ z ∈ Set.Ioi (0 : ℝ), (v z) ^ 2 ≤ MeasureTheory.integral
        (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun s => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)) →
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ C / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.FTS.Nonlin.Xn α f := by
  refine ⟨10, by norm_num, ?_⟩
  intro α f b a hα hα1 hab hreg hAng hRad z hz θ hθ0 hθ1
  obtain ⟨hsq, hmem, hbd⟩ := hreg
  have hγ1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγne : gam α ≠ 0 := ne_of_gt (gam_pos hα)
  -- the `θ`-first slot of the `ℋ⁴`-norm at order `(b+1, a+1)`
  obtain ⟨hTle, hTint, hTae⟩ :=
    Work.FTS.H2.slotM_quad α f hsq hmem (b + 1) (a + 1) (by omega) (by omega)
  have hptslot : ∀ σ ∈ Iθ, ∀ z : ℝ, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2
      = (Real.sin (2 * σ)) ^ (-(gam α))
        * ((mixed (b + 1) (a + 1) f z σ) ^ 2 * (w z) ^ 2) := by
    intro σ hσ z
    rw [show Wt α z σ = w z * (Real.sin (2 * σ)) ^ (-(gam α / 2)) from rfl, mul_pow,
      Work.FTS.H2.Wt_sq α hα z σ hσ]
    ring
  set B : ℝ → ℝ := fun σ => ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ) ^ 2 * (w z) ^ 2
    with hBdef
  have hBae : (fun σ => (Real.sin (2 * σ)) ^ (-(gam α)) * B σ)
      =ᵐ[volume.restrict Iθ]
      fun σ => ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2 := by
    filter_upwards [hTae, ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)]
      with σ _hσint hσI
    rw [hBdef]
    have hstep : (Real.sin (2 * σ)) ^ (-(gam α))
          * (∫ z in Iz, (mixed (b + 1) (a + 1) f z σ) ^ 2 * (w z) ^ 2)
        = ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2 := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ici fun z _ => (hptslot σ hσI z).symm
    exact hstep
  have hTint' : Integrable (fun σ => (Real.sin (2 * σ)) ^ (-(gam α)) * B σ)
      (volume.restrict Iθ) := hTint.congr hBae.symm
  set T : ℝ := ∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(gam α)) * B σ with hTdef
  have hTle' : T ≤ HkSq α 4 f := by
    rw [hTdef]
    rw [show (∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(gam α)) * B σ)
        = ∫ σ in Iθ, ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2
        from integral_congr_ae hBae]
    exact hTle
  have hKnn : 0 ≤ 100 / (gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the boundary limit at `θ → 0⁺`, from the angular clause of `BdryTraces`
  have hlim0 : Tendsto (fun θ' => mixed b a f z θ') (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    BdryTraces.tendsto_theta_zero hα hbd (by omega) hz
  -- integrability of the angular Hardy integrand, from the mixed slot
  have hDth_int := Work.FTS.H2.integrableOn_Dth_mixed_slice α f hsq hmem b a (by omega) hz
  have hDth_int2 : IntegrableOn
      (fun σ => (Real.sin (2 * σ)) ^ (-(gam α)) * (Dth (mixed b a f) z σ) ^ 2) Iθ :=
    hDth_int.congr_fun (fun σ _ => by ring) measurableSet_Icc
  have hint_ang : IntegrableOn
      (fun σ => (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ :=
    hDth_int2.congr_fun (fun σ hσ => by
      calc (Real.sin (2 * σ)) ^ (-(gam α)) * (Dth (mixed b a f) z σ) ^ 2
          = (Dth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α)) := by ring
        _ = (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) :=
            (Work.FTS.H2.pth_sq_mul_sin_eq α hα hα1 (mixed b a f) z σ hσ).symm)
      measurableSet_Icc
  -- the angular Hardy inequality (hypothesis)
  have hHT := hAng (mixed b a f) z (hsq.mixed b a) (Set.mem_Ioi.mpr (by linarith)) hlim0
    hint_ang θ ⟨hθ0, hθ1⟩
  have hI1 : (∫ σ in Iθ, (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
      = ∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(gam α)) * (Dth (mixed b a f) z σ) ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    rw [Work.FTS.H2.pth_sq_mul_sin_eq α hα hα1 (mixed b a f) z σ hσ]
    ring
  -- the radial Hardy inequality (hypothesis) on almost every `θ`-slice
  have hrad : ∀ᵐ σ ∂(volume.restrict Iθ),
      (Real.sin (2 * σ)) ^ (-(gam α)) * (Dth (mixed b a f) z σ) ^ 2
        ≤ (Real.sin (2 * σ)) ^ (-(gam α)) * B σ := by
    filter_upwards [hTae, ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)]
      with σ hσint hσI
    rcases eq_or_lt_of_le hσI.1 with hσeq | hσpos
    · have hsin0 : Real.sin (2 * σ) = 0 := by rw [← hσeq]; simp
      have hz0 : (Real.sin (2 * σ)) ^ (-(gam α)) = 0 := by
        rw [hsin0]; exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    rcases eq_or_lt_of_le hσI.2 with hσeq | hσlt
    · have hsin0 : Real.sin (2 * σ) = 0 := by
        rw [hσeq, show 2 * (π / 2) = π by ring, Real.sin_pi]
      have hz0 : (Real.sin (2 * σ)) ^ (-(gam α)) = 0 := by
        rw [hsin0]; exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    · have hσ' : σ ∈ Set.Ioo 0 (π / 2) := ⟨hσpos, hσlt⟩
      rw [Work.FTS.H2.Dth_mixed_quad hsq b a hz hσ']
      refine mul_le_mul_of_nonneg_left ?_
        (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hσI) _)
      have hcd : ContDiffOn ℝ 1 (fun s => mixed b (a + 1) f s σ) (Set.Ioi (0 : ℝ)) :=
        ((hsq.mixed b (a + 1)).curry_z hσ').of_le (by simp [Work.Stability.smoothOrder])
          |>.mono (Set.Ioi_subset_Ioi (by norm_num))
      have hdec : Tendsto (fun s => mixed b (a + 1) f s σ) atTop (nhds 0) :=
        BdryTraces.tendsto_atTop_zero hbd (by omega) hσ'
      exact hRad (fun s => mixed b (a + 1) f s σ) hcd hdec hσint z (Set.mem_Ioi.mpr hz)
  have hIntLe : (∫ σ in Iθ, (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
      ≤ T := by
    rw [hI1, hTdef]
    exact integral_mono_ae hDth_int2 hTint' hrad
  have hfin : (mixed b a f z θ) ^ 2 ≤ (100 / (gam α - 1)) * T :=
    le_trans hHT (mul_le_mul_of_nonneg_left hIntLe hKnn)
  have hsqrt : Real.sqrt (100 / (gam α - 1)) = 10 / Real.sqrt (gam α - 1) := by
    have h2 : (0 : ℝ) ≤ 10 / Real.sqrt (gam α - 1) :=
      div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq h2]
    congr 1
    rw [div_pow, Real.sq_sqrt hγ1.le]
    norm_num
  have hfinal : Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 f)
      = 10 / Real.sqrt (gam α - 1) * HkNorm α 4 f := by
    rw [Real.sqrt_mul hKnn, hsqrt]
    simp only [HkNorm]
  calc |mixed b a f z θ| = Real.sqrt ((mixed b a f z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((100 / (gam α - 1)) * T) := Real.sqrt_le_sqrt hfin
    _ ≤ Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 f) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTle' hKnn)
    _ = 10 / Real.sqrt (gam α - 1) * HkNorm α 4 f := hfinal
    _ = 10 / Real.sqrt (gam α - 1) * Work.FTS.Nonlin.Xn α f := rfl

end Work.FTS.H2.HQ
end
end
-- ===== merged: Submission.Work.FTS.H2.Q.WtoH_Mixed_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Q

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary absolute-value bookkeeping -/

/-- Comparison of powers: `|z^k X| ≤ |(z+1)^k X|` for `z ≥ 0`. -/
private lemma abs_mul_pow_le_succ (z X : ℝ) (hz : 0 ≤ z) (k : ℕ) :
    |z ^ k * X| ≤ |(z + 1) ^ k * X| := by
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hz k),
    abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) k)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz (by linarith) k) (abs_nonneg X)

/-- Triangle inequality for three weighted terms. -/
private lemma abs_comb3_le {Cst : ℝ} (hCst : 0 ≤ Cst) {a b c : ℝ} (ha : |a| ≤ Cst)
    (hb : |b| ≤ Cst) (hc : |c| ≤ Cst) {A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    |A * a + B * b + D * c| ≤ (A + B + D) * Cst := by
  have h1 : |A * a| ≤ A * Cst := by
    rw [abs_mul, abs_of_nonneg hA]
    exact mul_le_mul_of_nonneg_left ha hA
  have h2 : |B * b| ≤ B * Cst := by
    rw [abs_mul, abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_left hb hB
  have h3 : |D * c| ≤ D * Cst := by
    rw [abs_mul, abs_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left hc hD
  have htri : |A * a + B * b + D * c| ≤ |A * a| + |B * b| + |D * c| := by
    calc |A * a + B * b + D * c| ≤ |A * a + B * b| + |D * c| := abs_add_le _ _
      _ ≤ (|A * a| + |B * b|) + |D * c| := by linarith [abs_add_le (A * a) (B * b)]
      _ = |A * a| + |B * b| + |D * c| := by ring
  calc |A * a + B * b + D * c| ≤ |A * a| + |B * b| + |D * c| := htri
    _ ≤ A * Cst + B * Cst + D * Cst := by linarith
    _ = (A + B + D) * Cst := by ring


/-! ## From the `𝒲^{4,∞}`-bounds on `(z+1)³/z²·f` to bounds on `∂_z^j κ` -/



/-! ## The elementary weighted estimate -/

/-- If `|(z+1)^{j+3} K j| ≤ 6000 M Φ` for `j ≤ l ≤ 3`, `z > 0`, `M, Φ ≥ 0`, then the
weighted expression `((z+1)³ z^l/z²)·(z²K_l + 2l z K_{l-1} + l(l-1)K_{l-2})` is
`≤ 200000 M Φ`. -/
private theorem arith_aux {z : ℝ} (hz : 0 < z) {M Φ : ℝ} (hM : 0 ≤ M) (hΦ : 0 ≤ Φ)
    (l : ℕ) (hl : l ≤ 3) (K : ℕ → ℝ)
    (hK : ∀ j ≤ l, |(z + 1) ^ (j + 3) * K j| ≤ 6000 * (M * Φ)) :
    |(z + 1) ^ 3 * z ^ l / z ^ 2 * (z ^ 2 * K l + (2 * (l : ℝ)) * z * K (l - 1)
        + ((l : ℝ) * ((l : ℝ) - 1)) * K (l - 2))| ≤ 200000 * (M * Φ) := by
  have hMΦ : 0 ≤ M * Φ := mul_nonneg hM hΦ
  have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
  have hterm : ∀ j ≤ l, |z ^ j * ((z + 1) ^ 3 * K j)| ≤ 6000 * (M * Φ) := by
    intro j hj
    refine le_trans (abs_mul_pow_le_succ z ((z + 1) ^ 3 * K j) hz0 j) ?_
    have h2 : (z + 1) ^ j * ((z + 1) ^ 3 * K j) = (z + 1) ^ (j + 3) * K j := by
      rw [← mul_assoc, ← pow_add]
    rw [h2]
    exact hK j hj
  interval_cases l
  · -- l = 0
    have hid : (z + 1) ^ 3 * z ^ 0 / z ^ 2
          * (z ^ 2 * K 0 + (2 * ((0 : ℕ) : ℝ)) * z * K (0 - 1)
              + (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1)) * K (0 - 2))
        = 1 * (z ^ 0 * ((z + 1) ^ 3 * K 0))
          + (2 * ((0 : ℕ) : ℝ)) * (z ^ 0 * ((z + 1) ^ 3 * K 0))
          + (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1)) * (z ^ 0 * ((z + 1) ^ 3 * K 0)) := by
      have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 0 (by norm_num))
      (hterm 0 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 1
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 1 / z ^ 2
          * (z ^ 2 * K 1 + (2 * ((1 : ℕ) : ℝ)) * z * K (1 - 1)
              + (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) - 1)) * K (1 - 2))
        = 1 * (z ^ 1 * ((z + 1) ^ 3 * K 1))
          + (2 * ((1 : ℕ) : ℝ)) * (z ^ (1 - 1) * ((z + 1) ^ 3 * K (1 - 1)))
          + (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) - 1))
              * (z ^ (1 - 2) * ((z + 1) ^ 3 * K (1 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 1 (by norm_num))
      (hterm 0 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 2
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 2 / z ^ 2
          * (z ^ 2 * K 2 + (2 * ((2 : ℕ) : ℝ)) * z * K (2 - 1)
              + (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1)) * K (2 - 2))
        = 1 * (z ^ 2 * ((z + 1) ^ 3 * K 2))
          + (2 * ((2 : ℕ) : ℝ)) * (z ^ (2 - 1) * ((z + 1) ^ 3 * K (2 - 1)))
          + (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1))
              * (z ^ (2 - 2) * ((z + 1) ^ 3 * K (2 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 2 (by norm_num))
      (hterm 1 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 3
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 3 / z ^ 2
          * (z ^ 2 * K 3 + (2 * ((3 : ℕ) : ℝ)) * z * K (3 - 1)
              + (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1)) * K (3 - 2))
        = 1 * (z ^ 3 * ((z + 1) ^ 3 * K 3))
          + (2 * ((3 : ℕ) : ℝ)) * (z ^ (3 - 1) * ((z + 1) ^ 3 * K (3 - 1)))
          + (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1))
              * (z ^ (3 - 2) * ((z + 1) ^ 3 * K (3 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 3 (by norm_num))
      (hterm 2 (by norm_num)) (hterm 1 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]


/-! ## The transfer -/



end Work.FTS.H2.Q
end
end
-- ===== merged: Submission.Work.FTS.H2.Q.WtoH_Radial_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Q

open Work.Spaces

set_option autoImplicit false


end Work.FTS.H2.Q
end
end
-- ===== merged: Submission.Work.FTS.H2.Q.hkIntegrand_le_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Q

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The pointwise bound for `HkIntegrand` -/



end Work.FTS.H2.Q
end
end
-- ===== merged: Submission.Work.FTS.H2.T1Q.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

/-! ## the interior angular slice supremum -/

/-- `supAbsThO u z` is the supremum of `|u z θ|` over `θ ∈ (0,π/2)`, at the fixed radial
variable `z`.  This is the interior version of `Work.FTS.H2.supAbsTh` (which takes the
supremum over the *closed* interval `Iθ`): for `SmoothQuad` data the values on the boundary
lines `θ = 0, π/2` are unconstrained, so only the open interval is meaningful. -/
def supAbsThO (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := sSup {y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |u z θ|}

theorem abs_le_supAbsThO {u : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (h : BddAbove {y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |u z θ|}) :
    |u z θ| ≤ supAbsThO u z :=
  le_csSup h ⟨θ, hθ, rfl⟩

theorem supAbsThO_le {u : ℝ → ℝ → ℝ} {z C : ℝ}
    (h : ∀ θ ∈ Set.Ioo 0 (π / 2), |u z θ| ≤ C) : supAbsThO u z ≤ C :=
  csSup_le ⟨|u z (π / 4)|, π / 4, ⟨by positivity, by linarith [Real.pi_pos]⟩, rfl⟩
    (fun y hy => by rcases hy with ⟨θ, hθ, rfl⟩; exact h θ hθ)

end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.LocDataExt.Monotone =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The `ℋ^k`-integrand is monotone in the order**: every summand is a square and the index
sets grow with `k`. -/
theorem HkIntegrand_mono {α : ℝ} {m k : ℕ} (hmk : m ≤ k) (f : Fn) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α m f z θ ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  refine add_le_add ?_ ?_
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun i _ _ => sq_nonneg _)
  · have hinner : ∀ i : ℕ,
        (∑ j ∈ Finset.range (m + 1),
          (if 1 ≤ i ∧ i + j ≤ m then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ (∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
      intro i
      refine le_trans (Finset.sum_le_sum (fun j _ => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun j _ _ => ?_))
      · by_cases hc : 1 ≤ i ∧ i + j ≤ m
        · rw [if_pos hc, if_pos ⟨hc.1, le_trans hc.2 hmk⟩]
        · rw [if_neg hc]
          by_cases h2 : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos h2]; exact sq_nonneg _
          · rw [if_neg h2]
      · by_cases h2 : 1 ≤ i ∧ i + j ≤ k
        · rw [if_pos h2]; exact sq_nonneg _
        · rw [if_neg h2]
    calc (∑ i ∈ Finset.range (m + 1),
          (∑ j ∈ Finset.range (m + 1),
            (if 1 ≤ i ∧ i + j ≤ m then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)))
        ≤ ∑ i ∈ Finset.range (m + 1),
            (∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
          Finset.sum_le_sum (fun i _ => hinner i)
      _ ≤ ∑ i ∈ Finset.range (k + 1),
            (∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (by omega)) ?_
          intro i _ _
          exact Finset.sum_nonneg (fun j _ => by
            by_cases h2 : 1 ≤ i ∧ i + j ≤ k
            · rw [if_pos h2]; exact sq_nonneg _
            · rw [if_neg h2])

/-- **`ℋ^k`-membership is monotone in the order** for functions of the interior class
`SmoothQuad`. -/
theorem HkMem_mono {α : ℝ} {m k : ℕ} (hmk : m ≤ k) {f : Fn}
    (hf : Work.FTS.LocData.SmoothQuad f) (hk : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α m f :=
  Work.FTS.LocData.HkMem_of_majorant (f := f)
    (M := fun z θ => Work.Spaces.HkIntegrand α k f z θ) α m
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α m f hf)
    hk.1 hk.2 (fun z _ θ _ => HkIntegrand_mono hmk f z θ)

/-- **The interior class `RegQ` is monotone in the order.** -/
theorem RegQ_mono {α : ℝ} {m k : ℕ} (hmk : m ≤ k) {f : Fn}
    (hf : Work.FTS.Nonlin.RegQ α k f) : Work.FTS.Nonlin.RegQ α m f :=
  ⟨hf.1, HkMem_mono hmk hf.1 hf.2.1, fun a b hab => hf.2.2 a b (le_trans hab hmk)⟩

end Work.FTS.LocDataExt
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.DzHzDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

/-- The radial factor `H(z) = 2z(1-z)/(1+z)³` of `D_z F_*`:
`D_z F_*(z,θ) = α · (Γ(θ)/c(α)) · H(z)` for `z > -1` (the value at `z ≤ -1` is irrelevant,
only `z ≥ 0` is ever used). -/
noncomputable def Hz (z : ℝ) : ℝ := 2 * z * (1 - z) / (1 + z) ^ 3

/-- The universal weighted bound for the radial factor of `D_z F_*`:
`|(z+1)^k H^{(k)}(z)| ≤ HB k` for all `z ≥ 0`.  The constant comes from
`pzIter_hKer_bound` at the orders `k` and `k+1`:
`HB k = 2 · ((k+1)!(k+2) + k·k!(k+1))`. -/
noncomputable def HB (k : ℕ) : ℝ :=
  2 * (((k + 1).factorial : ℝ) * (k + 2) + (k : ℝ) * ((k.factorial : ℝ) * (k + 1)))

lemma HB_nonneg (k : ℕ) : 0 ≤ HB k := by
  rw [HB]; positivity

/-- On `z > -1` the radial factor of `D_z F_*` is `2 · z · h'(z)` for `h = hKer`; this is
the form in which its iterated derivatives are computed from the closed form
`Work.Spaces.iter_deriv_hKerClosed`. -/
lemma Hz_eq_mul_deriv {z : ℝ} (hz : -1 < z) :
    Hz z = 2 * (z * deriv Work.Spaces.hKer z) := by
  have hderiv : deriv Work.Spaces.hKer z = (1 - z) / (1 + z) ^ 3 := by
    have h := Work.Spaces.iter_deriv_hKerClosed 1 z hz
    simp only [Function.iterate_one] at h
    rw [show Work.Spaces.hKer = (fun z : ℝ => z / (1 + z) ^ 2) from rfl]
    rw [h, Work.Spaces.hKerClosed]
    norm_num
    field_simp
    ring
  rw [Hz, hderiv]
  field_simp

end Work.FTS.Nonlinear.FstarPkg
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.FstarPkg

/-- The angular moment of the fundamental profile `F_*`:
`(F_*, K)_{L²_θ}(z) = α · F_*(z)`, because `F_*(z,θ) = α (Γ(θ)/c(α)) F_*(z)` and
`c(α) = ∫_θ Γ(θ) K(θ)` is non-zero (`Work.Spaces.c_bounds`). -/
theorem FK_Fstar {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Construction.FK (Work.Construction.Fstar α) z = α * (2 * z / (1 + z) ^ 2) := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  rw [Work.Construction.FK]
  have h1 : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Construction.Fstar α z θ * Work.Spaces.K θ
        = (α * Work.FM.Fstar z / Work.Spaces.c α) * (Work.Spaces.Gam α θ * Work.Spaces.K θ) := by
    intro θ _
    simp only [Work.Construction.Fstar]
    ring
  rw [MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc h1]
  rw [MeasureTheory.integral_const_mul]
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ) = Work.Spaces.c α
      from rfl]
  rw [div_mul_cancel₀ (α * Work.FM.Fstar z) hc, Work.FM.Fstar]

end Work.FTS.Nonlinear.FstarPkg
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.Fstar_W =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

/-! ## The factorization `F_* = a · (Γ ⊗ h)` and its iterated derivatives -/

/-- `F_*(z,θ) = a · Γ(θ) · h(z)` with `a = 2α/c` and `h(z) = z/(1+z)²`: the profile of the
paper is the product of the angular factor `Γ` and the radial factor `h`. -/
lemma Fstar_eq_factored (α : ℝ) :
    Work.Construction.Fstar α
      = fun z θ => ((2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ) * Work.Spaces.hKer z := by
  funext z θ
  simp only [Work.Construction.Fstar, Work.FM.Fstar, Work.Spaces.hKer]
  ring

/-- The `z`-iterates of `F_*` factor through the `z`-iterates of `h = z/(1+z)²`. -/
lemma pzIter_Fstar_eq (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (Work.Construction.Fstar α) z θ
      = ((2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ) * deriv^[k] Work.Spaces.hKer z := by
  rw [Fstar_eq_factored α, Work.Spaces.pzIter_decomp]

/-- `D_θ^j F_* = a · (D_θ^j Γ) ⊗ h`: the angular operator `D_θ = sin(2θ)∂_θ` acts only on
`Γ`. -/
lemma DthIter_Fstar_eq (α : ℝ) (j : ℕ) :
    Work.Spaces.DthIter j (Work.Construction.Fstar α)
      = fun z θ => ((2 * α / Work.Spaces.c α)
          * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ) * Work.Spaces.hKer z := by
  funext z θ
  rw [Fstar_eq_factored α, Work.Spaces.DthIter_decomp]
  simp only [Work.Spaces.dthU_iter_const_mul]

/-- The mixed iterates of `F_*`: `∂_z^k D_θ^j F_* = a · (D_θ^j Γ) ⊗ h^{(k)}`. -/
lemma pzIter_DthIter_Fstar_eq (α : ℝ) (j k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j (Work.Construction.Fstar α)) z θ
      = ((2 * α / Work.Spaces.c α)
          * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ)
          * deriv^[k] Work.Spaces.hKer z := by
  rw [DthIter_Fstar_eq α j, Work.Spaces.pzIter_decomp]

/-! ## The two pointwise estimates -/

/-- The prefactor `a = 2α/c` is bounded by `20 α`, since `c(α) ≥ 1/10`. -/
lemma Fstar_coef_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    |2 * α / Work.Spaces.c α| ≤ 20 * α := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hnum : 0 ≤ 2 * α := by linarith
  rw [abs_of_nonneg (div_nonneg hnum (le_of_lt hcpos))]
  rw [div_le_iff₀ hcpos]
  nlinarith

/-- The radial `𝒲^{4,∞}`-summands of `F_*` are bounded by `20 α · k!(k+1)`. -/
lemma Fstar_z_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Construction.Fstar α) z θ| ≤
      20 * α * ((k.factorial : ℝ) * (k + 1)) := by
  have hcoef := Fstar_coef_le α hα hα1
  have hGam := Work.Spaces.Gam_bounds α θ hα hθ
  have hker : |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) :=
    Work.Spaces.pzIter_hKer_bound k z hz
  rw [pzIter_Fstar_eq]
  rw [show (z + 1) ^ k * (((2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ)
        * deriv^[k] Work.Spaces.hKer z)
      = ((2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ)
        * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z) by ring]
  rw [abs_mul]
  have h1 : |(2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ| ≤ 20 * α := by
    rw [abs_mul, abs_of_nonneg hGam.1]
    calc |2 * α / Work.Spaces.c α| * Work.Spaces.Gam α θ ≤ (20 * α) * 1 :=
          mul_le_mul hcoef hGam.2 hGam.1 (by linarith)
      _ = 20 * α := by ring
  calc |(2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ|
        * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
      ≤ (20 * α) * ((k.factorial : ℝ) * (k + 1)) :=
        mul_le_mul h1 hker (abs_nonneg _) (by positivity)
    _ = 20 * α * ((k.factorial : ℝ) * (k + 1)) := by ring

/-- The angular `𝒲^{4,∞}`-summands of `F_*` are bounded by `20 α · tBound (j-1) 0 · k!(k+1)`:
each `D_θ` costs one factor `α` (`dthU_Gam_le`), and the resulting `α Γ` is absorbed by the
weight (`Gam_mul_weight_le`). -/
lemma Fstar_mixed_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j k : ℕ) (hj : 1 ≤ j)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (Work.Construction.Fstar α)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤
      20 * α * (Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))) := by
  have hT0 : 0 ≤ Work.Spaces.tBound (j - 1) 0 := Work.Spaces.tBound_nonneg _ _
  have hK0 : 0 ≤ (k.factorial : ℝ) * (k + 1) := by positivity
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hw0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    Work.Spaces.gamma_weight_nonneg α θ hα hθ
  have hdth := Work.Spaces.dthU_Gam_le j hj α hα hα1 θ hθ
  have hgamw : α * Work.Spaces.Gam α θ
      * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 1 := by
    rw [← mul_div_assoc]
    exact Work.Spaces.Gam_mul_weight_le α θ hα hθ
  have hcoef : |2 * α / Work.Spaces.c α| ≤ 20 * α := Fstar_coef_le α hα hα1
  have hker : |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
      ≤ (k.factorial : ℝ) * (k + 1) := Work.Spaces.pzIter_hKer_bound k z hz
  rw [pzIter_DthIter_Fstar_eq]
  rw [show (z + 1) ^ k * (2 * α / Work.Spaces.c α
          * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ
          * deriv^[k] Work.Spaces.hKer z)
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
      = (2 * α / Work.Spaces.c α) * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ
        * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z)
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) from by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hw0]
  have hstep1 : |(2 * α / Work.Spaces.c α)
        * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ|
      ≤ |2 * α / Work.Spaces.c α| * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hdth (abs_nonneg _)
  have hTK0 : 0 ≤ |2 * α / Work.Spaces.c α| * Work.Spaces.tBound (j - 1) 0
      * ((k.factorial : ℝ) * (k + 1)) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hT0) hK0
  have hstep2 : |(2 * α / Work.Spaces.c α)
        * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ|
        * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ (|2 * α / Work.Spaces.c α| * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ))
        * ((k.factorial : ℝ) * (k + 1))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
    apply mul_le_mul_of_nonneg_right _ hw0
    exact mul_le_mul hstep1 hker (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (le_of_lt hα) hT0) hG0))
  refine le_trans hstep2 ?_
  rw [show (|2 * α / Work.Spaces.c α| * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ))
        * ((k.factorial : ℝ) * (k + 1))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      = (|2 * α / Work.Spaces.c α| * Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1)))
        * (α * Work.Spaces.Gam α θ
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) from by ring]
  calc (|2 * α / Work.Spaces.c α| * Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1)))
        * (α * Work.Spaces.Gam α θ
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
      ≤ (|2 * α / Work.Spaces.c α| * Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))) * 1 :=
        mul_le_mul_of_nonneg_left hgamw hTK0
    _ = |2 * α / Work.Spaces.c α| * (Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))) := by ring
    _ ≤ (20 * α) * (Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hT0 hK0)
    _ = 20 * α * (Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))) := by ring

/-! ## Assembly -/

/-- The universal constant `KB` multiplying `20 α`: the sum of all the (α-independent)
pointwise bounds of the summands of `𝒲^{4,∞}(F_*)`. -/
noncomputable def KB : ℝ :=
  (∑ k ∈ Finset.range 5, (k.factorial : ℝ) * (k + 1))
    + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
        (if 1 ≤ j ∧ k + j ≤ 4 then
          Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1)) else 0)

lemma KB_nonneg : 0 ≤ KB := by
  rw [KB]
  refine add_nonneg (Finset.sum_nonneg fun k _ => by positivity) ?_
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  split_ifs with h
  · exact mul_nonneg (Work.Spaces.tBound_nonneg _ _) (by positivity)
  · norm_num

/-- The `𝒲^{4,∞}`-norm of `F_*` is at most `20 α · KB`. -/
lemma WlInf_Fstar_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) ≤ 20 * α * KB := by
  have hKB : 20 * α * KB =
      (∑ k ∈ Finset.range 5, 20 * α * ((k.factorial : ℝ) * (k + 1)))
        + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
            (20 * α * (if 1 ≤ j ∧ k + j ≤ 4 then
              Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1)) else 0)) := by
    rw [KB, mul_add]
    congr 1
    · rw [Finset.mul_sum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
  rw [Work.Spaces.WlInf, hKB]
  apply add_le_add
  · exact Finset.sum_le_sum fun k hk =>
      Work.Spaces.supAbs_le fun z hz θ hθ => Fstar_z_bound α hα hα1 k z θ hz hθ
  · apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    split_ifs with hcond
    · exact Work.Spaces.supAbs_le fun z hz θ hθ =>
        Fstar_mixed_bound α hα hα1 j k hcond.1 z θ hz hθ
    · simp

/-- `F_* ∈ 𝒲^{4,∞}` for `0 < α ≤ 1`.  Every `SupFinite` predicate is witnessed by the
explicit bound of `Fstar_z_bound` / `Fstar_mixed_bound`. -/
lemma WlInfMem_Fstar (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 4 (Work.Construction.Fstar α) := by
  constructor
  · intro k hk
    refine ⟨20 * α * ((k.factorial : ℝ) * (k + 1)), fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact Fstar_z_bound α hα hα1 k z θ hz hθ
  · intro j hj k hk hj1 hjk
    refine ⟨20 * α * (Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))),
      fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact Fstar_mixed_bound α hα hα1 j k hj1 z θ hz hθ

theorem Fstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (Work.Construction.Fstar α) ∧
      Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) ≤ C * α := by
  refine ⟨20 * KB + 1, by linarith [KB_nonneg], fun α hα hα1 =>
    ⟨WlInfMem_Fstar α hα hα1, ?_⟩⟩
  refine le_trans (WlInf_Fstar_le α hα hα1) ?_
  nlinarith [KB_nonneg, hα]

end Work.FTS.Nonlinear.FstarPkg
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.GamSinRpowMulLeOne =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Γ(θ) · sin(2θ)^{-α/5} ≤ 1` on `Iθ`

This is the elementary pointwise angular estimate used throughout the `𝒲^{l,∞}`-norm
bounds of the `F_*`-package (see `Work.Spaces.Gam_mul_weight_le`, whose proof contains
exactly this estimate, and `Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial`).

## Mathematics

Write `s = sin θ`, `c = cos θ` and `A = s c²`; on `Iθ = [0, π/2]` both `s` and `c` lie
in `[0,1]`, `Γ(θ) = A ^ (α/3)` and `sin(2θ) = 2 s c`.  The numerical core is
`A ^ 5 ≤ sin(2θ) ^ 3`: indeed `A ^ 5 = (s² c⁷)(s³ c³) ≤ s³ c³ ≤ 8 s³ c³ = (2 s c)³`
because `0 ≤ s, c ≤ 1`.  Raising to the power `α/15 ≥ 0` gives `Γ(θ) ≤ sin(2θ) ^ (α/5)`,
and multiplying by the nonnegative factor `sin(2θ)^{-α/5}`, with
`x ^ (α/5) · x ^ (-(α/5)) ≤ 1` (equality for `x > 0`, and `0` for `x = 0`), gives the
claim.
-/

namespace Work.FTS.Nonlinear.FstarPkg

open scoped Real

/-- `sin(2θ) ≥ 0` on `Iθ = [0,π/2]`. -/
lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  rw [Real.sin_two_mul]
  positivity

/-- On `Iθ = [0,π/2]` the angular weight `Γ` is dominated by the corresponding power of
`sin(2θ)`: `Γ(θ) ≤ sin(2θ)^{α/5}`. -/
lemma Gam_le_sin_two_rpow {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  set A : ℝ := Real.sin θ * Real.cos θ ^ 2 with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hGamA : Work.Spaces.Gam α θ = A ^ (α / 3) := by
    simp only [Work.Spaces.Gam]; rw [hA]
  have he0 : 0 ≤ Real.sin (2 * θ) := by rw [Real.sin_two_mul]; positivity
  -- The numerical core: `A ^ 5 ≤ sin(2θ) ^ 3`.
  have hA5r : A ^ (5 : ℝ) ≤ (Real.sin (2 * θ)) ^ (3 : ℝ) := by
    have hm : A ^ 5 ≤ (Real.sin (2 * θ)) ^ 3 := by
      rw [hA, Real.sin_two_mul]
      have h1 : (Real.sin θ) ^ 2 * (Real.cos θ) ^ 7 ≤ 1 := by
        have a : (Real.sin θ) ^ 2 ≤ 1 := pow_le_one₀ (n := 2) hs0 hs1
        have b : (Real.cos θ) ^ 7 ≤ 1 := pow_le_one₀ (n := 7) hc0 hc1
        nlinarith [mul_le_mul a b (pow_nonneg hc0 7) (by norm_num : (0:ℝ) ≤ 1)]
      have hQ : 0 ≤ (Real.sin θ) ^ 3 * (Real.cos θ) ^ 3 := by positivity
      have step : ((Real.sin θ) ^ 2 * (Real.cos θ) ^ 7) * ((Real.sin θ) ^ 3 * (Real.cos θ) ^ 3)
          ≤ 1 * ((Real.sin θ) ^ 3 * (Real.cos θ) ^ 3) :=
        mul_le_mul_of_nonneg_right h1 hQ
      nlinarith [step, hQ, sq_nonneg (Real.sin θ * Real.cos θ)]
    simpa using hm
  -- Raise to the nonnegative power `α/15`.
  have h1 : A ^ (α / 3) = (A ^ (5:ℝ)) ^ (α / 15) := by
    rw [← Real.rpow_mul hA0 5 (α / 15), show (5:ℝ) * (α / 15) = α / 3 by ring]
  have h2 : ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) = (Real.sin (2 * θ)) ^ (α / 5) := by
    rw [← Real.rpow_mul he0 3 (α / 15), show (3:ℝ) * (α / 15) = α / 5 by ring]
  have h3 : (A ^ (5:ℝ)) ^ (α / 15) ≤ ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hA0 5) hA5r (by linarith)
  rw [← h1, h2] at h3
  rwa [hGamA]

theorem GamSinRpowMulLeOne {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ 1 := by
  -- `α ≤ 1` is not needed for the estimate, but it is part of the requested interface.
  have _hα1 := hα1
  have he0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hGam : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
    Gam_le_sin_two_rpow hα hθ
  have h1 : Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
      ≤ (Real.sin (2 * θ)) ^ (α / 5) * (Real.sin (2 * θ)) ^ (-(α / 5)) :=
    mul_le_mul_of_nonneg_right hGam (Real.rpow_nonneg he0 _)
  have h2 : (Real.sin (2 * θ)) ^ (α / 5) * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ 1 := by
    rcases eq_or_lt_of_le he0 with h | h
    · rw [← h, Real.zero_rpow (by linarith : α / 5 ≠ 0),
          Real.zero_rpow (by linarith : -(α / 5) ≠ 0)]
      norm_num
    · rw [← Real.rpow_add h (α / 5) (-(α / 5)), show α / 5 + -(α / 5) = 0 by ring,
          Real.rpow_zero]
  exact le_trans h1 h2

end Work.FTS.Nonlinear.FstarPkg
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.WlInf_congr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

/-! ## Congruence of the `𝒲^{l,∞}`-norm

Both `WlInf` and `WlInfMem` are built out of suprema over the domain `Iz ×ˢ Iθ` of the
functions `(z+1)^k ∂_z^k f` and `(z+1)^k ∂_z^k D_θ^j f · sin(2θ)^{-α/5}/(α+sin 2θ)`.
Since `Iz = [0,∞)`, the hypothesis `∀ z, -1 < z → f z = g z` constrains `f` and `g` on the
whole domain, and on the open right half-plane `(-1,∞)` it makes all the `z`-derivatives
coincide as well (`∂_z` is local); the `θ`-derivatives need no neighbourhood because the
hypothesis already holds for *every* `θ`.  Hence all the functions whose suprema enter the
definition agree on `Iz ×ˢ Iθ` and the two norms coincide. -/

/-- A point of `Iz = [0,∞)` is `> -1`. -/
private lemma neg_one_lt_of_mem_Iz {z : ℝ} (hz : z ∈ Work.Spaces.Iz) : -1 < z := by
  have : (0 : ℝ) ≤ z := hz
  linarith

/-- Two functions which agree on the open right half-plane `(-1,∞)` have the same derivative
at every point `z > -1` (the derivative is a local notion). -/
private lemma deriv_congr_Ioi {F G : ℝ → ℝ} {z : ℝ} (hz : -1 < z)
    (h : ∀ z' : ℝ, -1 < z' → F z' = G z') : deriv F z = deriv G z :=
  Filter.EventuallyEq.deriv_eq
    (Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioi hz) fun z' hz' => h z' hz')

/-- If `f` and `g` agree for every `z > -1` (and every `θ`), then so do all their iterated
plain `z`-derivatives. -/
private lemma pzIter_congr {f g : ℝ → ℝ → ℝ}
    (hfg : ∀ z, -1 < z → ∀ θ, f z θ = g z θ) (k : ℕ) :
    ∀ z, -1 < z → ∀ θ, Work.Spaces.pzIter k f z θ = Work.Spaces.pzIter k g z θ := by
  induction k with
  | zero => exact hfg
  | succ k ih =>
      intro z hz θ
      show deriv (fun z' => Work.Spaces.pzIter k f z' θ) z
        = deriv (fun z' => Work.Spaces.pzIter k g z' θ) z
      exact deriv_congr_Ioi hz fun z' hz' => ih z' hz' θ


/-- If `f` and `g` agree for every `z > -1` (and every `θ`), then so do all their iterated
`D_θ`-derivatives (at any `z > -1`). -/
private lemma DthIter_congr {f g : ℝ → ℝ → ℝ}
    (hfg : ∀ z, -1 < z → ∀ θ, f z θ = g z θ) (j : ℕ) :
    ∀ z, -1 < z → ∀ θ, Work.Spaces.DthIter j f z θ = Work.Spaces.DthIter j g z θ := by
  induction j with
  | zero => exact hfg
  | succ j ih =>
      intro z hz θ
      show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter j f z θ') θ
        = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter j g z θ') θ
      rw [funext (fun θ' => ih z hz θ')]

/-- The sets whose suprema define `supAbs` coincide as soon as the two functions agree on the
domain `Iz ×ˢ Iθ`. -/
private lemma supSet_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = g z θ) :
    {y : ℝ | ∃ z ∈ Work.Spaces.Iz, ∃ θ ∈ Work.Spaces.Iθ, y = |f z θ|}
      = {y : ℝ | ∃ z ∈ Work.Spaces.Iz, ∃ θ ∈ Work.Spaces.Iθ, y = |g z θ|} := by
  ext y
  constructor
  · rintro ⟨z, hz, θ, hθ, rfl⟩
    exact ⟨z, hz, θ, hθ, congrArg abs (h z hz θ hθ)⟩
  · rintro ⟨z, hz, θ, hθ, rfl⟩
    exact ⟨z, hz, θ, hθ, (congrArg abs (h z hz θ hθ)).symm⟩

/-- `supAbs` only depends on the values of the function on the domain `Iz ×ˢ Iθ`. -/
private lemma supAbs_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = g z θ) :
    Work.Spaces.supAbs f = Work.Spaces.supAbs g :=
  congrArg sSup (supSet_congr h)

/-- `SupFinite` only depends on the values of the function on the domain `Iz ×ˢ Iθ`. -/
private lemma SupFinite_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = g z θ) :
    Work.Spaces.SupFinite f ↔ Work.Spaces.SupFinite g := by
  unfold Work.Spaces.SupFinite
  rw [supSet_congr h]

-- Intended full name: `Work.FTS.Nonlinear.FstarPkg.WlInf_congr`
-- (declare it inside `namespace Work.FTS.Nonlinear.FstarPkg`).  `WlInf` and `WlInfMem` are
-- the `𝒲^{l,∞}`-norm and its membership predicate of `Submission/Work/Spaces/Defs.lean`; both
-- are built from `pzIter k f`, `pzIter k (DthIter j f)` evaluated at `(z,θ) ∈ Iz ×ˢ Iθ`.
theorem WlInf_congr {f g : ℝ → ℝ → ℝ}
    (hfg : ∀ z, -1 < z → ∀ θ, f z θ = g z θ) (α : ℝ) (l : ℕ) :
    Work.Spaces.WlInf α l f = Work.Spaces.WlInf α l g ∧
      (Work.Spaces.WlInfMem α l f ↔ Work.Spaces.WlInfMem α l g) := by
  -- the `z`-slots of `WlInf` agree
  have hz : ∀ k : ℕ,
      Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ)
        = Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k g z θ) := by
    intro k
    refine supAbs_congr fun z hz θ hθ => ?_
    rw [pzIter_congr hfg k z (neg_one_lt_of_mem_Iz hz) θ]
  -- the mixed `(z,θ)`-slots of `WlInf` agree
  have hm : ∀ j k : ℕ,
      Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        = Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
    intro j k
    refine supAbs_congr fun z hz θ hθ => ?_
    rw [pzIter_congr (DthIter_congr hfg j) k z (neg_one_lt_of_mem_Iz hz) θ]
  -- the corresponding `SupFinite` statements agree
  have hSFz : ∀ k : ℕ,
      Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ)
        ↔ Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k g z θ) := by
    intro k
    refine SupFinite_congr fun z hz θ hθ => ?_
    rw [pzIter_congr hfg k z (neg_one_lt_of_mem_Iz hz) θ]
  have hSFm : ∀ j k : ℕ,
      Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ↔ Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
    intro j k
    refine SupFinite_congr fun z hz θ hθ => ?_
    rw [pzIter_congr (DthIter_congr hfg j) k z (neg_one_lt_of_mem_Iz hz) θ]
  refine ⟨?_, ?_⟩
  · have h1 : (∑ k ∈ Finset.range (l + 1),
          Work.Spaces.supAbs fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ)
        = ∑ k ∈ Finset.range (l + 1),
          Work.Spaces.supAbs fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k g z θ :=
      Finset.sum_congr rfl fun k _ => hz k
    have h2 : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          if 1 ≤ j ∧ k + j ≤ l then
            Work.Spaces.supAbs fun z θ => (z + 1) ^ k
              * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
          else 0)
        = ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          if 1 ≤ j ∧ k + j ≤ l then
            Work.Spaces.supAbs fun z θ => (z + 1) ^ k
              * Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
          else 0 := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      split_ifs with hc
      · exact hm j k
      · rfl
    simp only [Work.Spaces.WlInf]
    rw [h1, h2]
  · constructor
    · intro h
      exact ⟨fun k hk => (hSFz k).mp (h.1 k hk),
             fun j hj k hk hj1 hkj => (hSFm j k).mp (h.2 j hj k hk hj1 hkj)⟩
    · intro h
      exact ⟨fun k hk => (hSFz k).mpr (h.1 k hk),
             fun j hj k hk hj1 hkj => (hSFm j k).mpr (h.2 j hj k hk hj1 hkj)⟩

end Work.FTS.Nonlinear.FstarPkg
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

/-! ## The two functions, and the transfer of the profile identity -/

/-- The radial factor `2α/(1+z)` of `L₁₂(F_*)`. -/
def invH (α : ℝ) : ℝ → ℝ := fun z => 2 * α / (1 + z)

/-- The function whose `𝒲^{4,∞}`-norm the lemma is about. -/
def c2mL12 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z

@[simp] theorem invH_apply (α z : ℝ) : invH α z = 2 * α / (1 + z) := rfl

@[simp] theorem c2mL12_apply (α z θ : ℝ) : c2mL12 α z θ =
    Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z := rfl

/-- The identity `L₁₂(F_*) = 2α/(1+z)` holds on the open set `(-1,∞)`. -/
theorem eqOn_L12_invH (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Set.EqOn (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) (invH α)
      (Set.Ioi (-1)) := by
  intro z hz
  exact L12_Fstar_eq_of_gt_neg_one hα hα1 hz

/-- All iterated derivatives of two functions agreeing on the open set `(-1,∞)` agree
on `(-1,∞)`. -/
theorem deriv_iter_eqOn {F H : ℝ → ℝ} (h : Set.EqOn F H (Set.Ioi (-1))) (k : ℕ) :
    Set.EqOn (deriv^[k] F) (deriv^[k] H) (Set.Ioi (-1)) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      intro z hz
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact Filter.EventuallyEq.deriv_eq
        (Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hz) (fun y hy => ih hy))

/-- The iterated `z`-derivatives of `c2m(θ)·F` and `c2m(θ)·H` agree on the domain when
`F = H` on `(-1,∞)`. -/
theorem pzIter_c2m_mul_eq {F H : ℝ → ℝ} (h : Set.EqOn F H (Set.Ioi (-1))) (k : ℕ)
    {z θ : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    Work.Spaces.pzIter k (fun z θ => Work.Construction.c2m θ * F z) z θ
      = Work.Spaces.pzIter k (fun z θ => Work.Construction.c2m θ * H z) z θ := by
  rw [Work.Spaces.pzIter_decomp k (fun θ => Work.Construction.c2m θ) F z θ,
    Work.Spaces.pzIter_decomp k (fun θ => Work.Construction.c2m θ) H z θ,
    deriv_iter_eqOn h k hz]

/-- The iterated `z`-derivatives of `D_θ^j (c2m·F)` and `D_θ^j (c2m·H)` agree on the
domain when `F = H` on `(-1,∞)`. -/
theorem pzIter_DthIter_c2m_mul_eq {F H : ℝ → ℝ} (h : Set.EqOn F H (Set.Ioi (-1)))
    (j k : ℕ) {z θ : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j
        (fun z θ => Work.Construction.c2m θ * F z)) z θ
      = Work.Spaces.pzIter k (Work.Spaces.DthIter j
        (fun z θ => Work.Construction.c2m θ * H z)) z θ := by
  have hF : Work.Spaces.DthIter j (fun z θ => Work.Construction.c2m θ * F z)
      = fun z θ => Work.Spaces.dthU^[j] (Work.Construction.c2m) θ * F z := by
    funext z θ
    exact Work.Spaces.DthIter_decomp j Work.Construction.c2m F z θ
  have hH : Work.Spaces.DthIter j (fun z θ => Work.Construction.c2m θ * H z)
      = fun z θ => Work.Spaces.dthU^[j] (Work.Construction.c2m) θ * H z := by
    funext z θ
    exact Work.Spaces.DthIter_decomp j Work.Construction.c2m H z θ
  rw [hF, hH]
  rw [Work.Spaces.pzIter_decomp k (fun θ => Work.Spaces.dthU^[j] Work.Construction.c2m θ)
        F z θ,
    Work.Spaces.pzIter_decomp k (fun θ => Work.Spaces.dthU^[j] Work.Construction.c2m θ)
        H z θ,
    deriv_iter_eqOn h k hz]

/-! ## The two pointwise bounds for `c2m · L₁₂(F_*)` -/

/-- The `z`-part: `|(z+1)^k ∂_z^k (c2m·L₁₂(F_*))| ≤ 4α·k!` on the domain. -/
theorem bound_z (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (hk : k ≤ 4)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (c2mL12 α) z θ| ≤ 4 * α * (k.factorial : ℝ) := by
  have hunf : c2mL12 α = fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z := rfl
  rw [hunf]
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  have heq := pzIter_c2m_mul_eq (F := fun z => Work.Construction.L12
      (Work.Construction.Fstar α) z) (H := invH α) (eqOn_L12_invH α hα hα1) k
      (z := z) (θ := θ) hz1
  rw [heq]
  exact c2mInv_points α z θ hα hα1 hz0 k hk

/-- The mixed part: `|(z+1)^k ∂_z^k D_θ^j (c2m·L₁₂(F_*)) · sin(2θ)^{-α/5}/(α+sin 2θ)| ≤ K α`
on the domain, for the universal constant `K` of `c2mInv_mixed`. -/
theorem bound_mixed (K : ℝ) (hK : ∀ (α z θ : ℝ), 0 < α → α ≤ 1 → 0 ≤ z →
      θ ∈ Work.Spaces.Iθ → ∀ (j k : ℕ), 1 ≤ j → j ≤ 4 → k ≤ 4 →
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z)))) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j k : ℕ) (hj1 : 1 ≤ j) (hj4 : j ≤ 4) (hk : k ≤ 4)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (c2mL12 α)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ K * α := by
  have hunf : c2mL12 α = fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z := rfl
  rw [hunf]
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  have heq := pzIter_DthIter_c2m_mul_eq (F := fun z => Work.Construction.L12
      (Work.Construction.Fstar α) z) (H := invH α) (eqOn_L12_invH α hα hα1) j k
      (z := z) (θ := θ) hz1
  rw [heq]
  exact hK α z θ hα hα1 hz0 hθ j k hj1 hj4 hk

/-! ## The two sums -/

/-- The constant of the final estimate: the `z`-sum `4·(0!+1!+2!+3!+4!)` plus the 25
mixed summands of `c2mInv_mixed` (all bounded by `K α`). -/
def CW (K : ℝ) : ℝ := (∑ k ∈ Finset.range 5, 4 * (k.factorial : ℝ)) + 25 * K + 1


/-- The double sum of a constant over `range 5 × range 5`. -/
theorem sum_range5_const_mul (c : ℝ) :
    (∑ _j ∈ Finset.range 5, ∑ _k ∈ Finset.range 5, c) = 25 * c := by
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The `z`-sum, with the constant `α` pulled out. -/
theorem sum_range5_four_factorial_mul (α : ℝ) :
    (∑ k ∈ Finset.range 5, 4 * α * (k.factorial : ℝ))
      = (∑ k ∈ Finset.range 5, 4 * (k.factorial : ℝ)) * α := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem CW_pos (K : ℝ) (hK : 0 < K) : 0 < CW K := by
  have h1 : 0 ≤ ∑ k ∈ Finset.range 5, 4 * (k.factorial : ℝ) :=
    Finset.sum_nonneg fun k _ => by positivity
  have h2 : 0 < 25 * K := by linarith
  rw [CW]
  linarith

/-! ## The main theorem -/

theorem c2m_L12Fstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) ∧
      Work.Spaces.WlInf α 4 (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) ≤ C * α := by
  obtain ⟨K, hKpos, hK⟩ := c2mInv_mixed
  have hK' : ∀ (α z θ : ℝ), 0 < α → α ≤ 1 → 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      ∀ (j k : ℕ), 1 ≤ j → j ≤ 4 → k ≤ 4 →
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z)))) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ K * α := hK
  refine ⟨CW K, CW_pos K hKpos, fun α hα hα1 => ⟨?_, ?_⟩⟩
  · -- membership: every summand is bounded
    constructor
    · intro k hk
      exact ⟨4 * α * (k.factorial : ℝ), fun y hy => by
        rcases hy with ⟨z, hz, θ, hθ, rfl⟩
        exact bound_z α hα hα1 k hk hz⟩
    · intro j hj k hk hj1 hjk
      exact ⟨K * α, fun y hy => by
        rcases hy with ⟨z, hz, θ, hθ, rfl⟩
        exact bound_mixed K hK' α hα hα1 j k hj1 hj hk hz hθ⟩
  · -- the norm estimate
    have hzsum : (∑ k ∈ Finset.range 5, Work.Spaces.supAbs (fun z θ =>
          (z + 1) ^ k * Work.Spaces.pzIter k (c2mL12 α) z θ))
        ≤ ∑ k ∈ Finset.range 5, 4 * α * (k.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk4 : k ≤ 4 := by
        have := Finset.mem_range.mp hk
        omega
      exact Work.Spaces.supAbs_le fun z hz θ _ => bound_z α hα hα1 k hk4 hz
    have hmsum : (∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
          (if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.supAbs (fun z θ =>
            (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (c2mL12 α)) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0))
        ≤ ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5, K * α := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      by_cases hc : 1 ≤ j ∧ k + j ≤ 4
      · rw [if_pos hc]
        have hj4 : j ≤ 4 := by
          have := Finset.mem_range.mp hj
          omega
        have hk4 : k ≤ 4 := by
          have := Finset.mem_range.mp hk
          omega
        exact Work.Spaces.supAbs_le fun z hz θ hθ =>
          bound_mixed K hK' α hα hα1 j k hc.1 hj4 hk4 hz hθ
      · rw [if_neg hc]
        exact mul_nonneg hKpos.le hα.le
    calc Work.Spaces.WlInf α 4 (c2mL12 α)
        = (∑ k ∈ Finset.range 5, Work.Spaces.supAbs (fun z θ =>
              (z + 1) ^ k * Work.Spaces.pzIter k (c2mL12 α) z θ))
          + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
              (if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.supAbs (fun z θ =>
                (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (c2mL12 α)) z θ
                  * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) := rfl
      _ ≤ (∑ k ∈ Finset.range 5, 4 * α * (k.factorial : ℝ))
          + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5, K * α := add_le_add hzsum hmsum
      _ = (∑ k ∈ Finset.range 5, 4 * (k.factorial : ℝ)) * α + 25 * (K * α) := by
        rw [sum_range5_four_factorial_mul, sum_range5_const_mul]
      _ ≤ CW K * α := by
        rw [CW]
        nlinarith [hα.le, hKpos.le]

end Work.FTS.Nonlinear.FstarPkg
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Interface =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
-- NOTE: the *proofs* of the fields live in the modules named in the field docstrings
-- (`FTS/H2/HProdQ.lean`, `WProdQ.lean`, `WtoHQ.lean`, `L12HQ.lean`, `L12ZeroQ.lean`,
-- `Spaces/ProductRuleInW.lean`, `Spaces/radial_prod.lean`, `N4Fields/`).  They are deliberately
-- NOT imported here: `FTS/H2/LinfQ.lean` and `FTS/H2/L12densIntegrable.lean` both declare a
-- `Qd` and cannot be imported together (see `FTS/H2/NOTES_H2.md` §7), so importing the proofs
-- into this interface module would make the chapter unbuildable.  Consumers import the proof
-- modules and the interface separately.

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlin

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `RegQ`-level contract (N3-fix) — norm-level only -/

/-- **The `RegQ`-level norm facts consumed by N4.**

Every field is an inequality between *norms* of the paper's function spaces (no `IP` occurs, no
field concludes `RegQ` of a derived object), and each is a `SmoothNbhd`-free restatement of a
theorem already in the tree; the constant `Ci` is universal and `α₂` is the range of `α`.  The
factor `α^{-1/2}` is the only permitted loss in `α` (design §2.3, §5 T9): it is
`1/√(γ-1) = √10 α^{-1/2}` with `γ = 1 + α/10`. -/
structure N4Norm (Ci α₂ : ℝ) : Prop where
  pos : 0 < Ci ∧ 0 < α₂
  /-- `ℋ⁴` is closed under products, with the loss `√10 α^{-1/2}` (`HProdQ`, tex 1086). -/
  prod : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, RegQ α 4 f → RegQ α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
    Xn α (fun z θ => f z θ * g z θ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g
  /-- Multiplication by a `𝒲^{4,∞}` function (`WProdQ`, tex 1096). -/
  wprod : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.LocData.SmoothQuad f →
    Work.Spaces.WlInfMem α 4 f → RegQ α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
    Xn α (fun z θ => f z θ * g z θ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Xn α g
  /-- `𝒲^{4,∞}` controls `ℋ⁴` through the weight `(z+1)³/z²` (`WtoHQ`, tex 1160). -/
  wtoh : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, Work.FTS.LocData.SmoothQuad f →
    Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) → RegQ α 4 f →
    Xn α f ≤ Ci * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
  /-- `L₁₂` maps the `ℋ⁴`-class into itself, losslessly (`L12HQ`, tex 1119). -/
  l12H : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, RegQ α 4 g → Work.Construction.L12 g 0 = 0 →
    Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
    Xn α (fun z θ => Work.Construction.L12 g z) ≤ Ci * Xn α g
  /-- The zero mode of `L₁₂` is controlled by the `ℋ⁴`-norm (`L12ZeroQ`, tex 1519). -/
  l12zero : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, RegQ α 4 f →
    |Work.Construction.L12 f 0| ≤ Ci * Xn α f
  /-- **The angular moment `FK g = ∫_θ K(θ) g(z,θ) dθ`.**  For `RegQ` data with vanishing zero
  mode, `FK g` is again an `ℋ⁴`-function (it is the radial function `-D_z L₁₂(g) = Qang g 0`,
  the first angular moment of `g`) and is controlled by `Xn α g`.  This is the norm-level half
  of the design's `fk` (§3.2), needed by rows 20, 21, 24 and 25 of the table. -/
  fkH : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, RegQ α 4 g → Work.Construction.L12 g 0 = 0 →
    Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧
    Xn α (fun z _ => Work.Construction.FK g z) ≤ Ci * Xn α g
  /-- `z ↦ L₁₂(g)(z)` is differentiable on `(0,∞)` in the interior class; this is the analytic
  input of the four-way split of `N` (design `L-N4.2`; the density `L12dens g` is continuous
  there, `Work.FM.hasDerivAt_L12`).  Needed by `Pieces/splits`. -/
  l12diff : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, Work.FTS.LocData.SmoothQuad g →
    Work.Spaces.HkMem α 4 g → ∀ z ∈ Set.Ioi (0 : ℝ),
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z
  /-- Multiplication by a function of `z` alone is **lossless** in `α` (`radial_prod`,
  design §3.2).  The decay hypotheses are the `z = ∞` clauses of `BdryTraces`, which the
  `RegQ` data supply. -/
  radialMul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (r : ℝ → ℝ) (g : Fn),
    Work.FTS.LocData.SmoothQuad (fun z _ => r z) → Work.FTS.LocData.SmoothQuad g →
    Work.Spaces.HkMem α 4 (fun z _ => r z) → Work.Spaces.HkMem α 4 g →
    (∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => r z) z 0)
      Filter.atTop (nhds 0)) →
    (∀ b : ℕ, b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b g z θ) Filter.atTop (nhds 0)) →
    Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) ∧
    Xn α (fun z θ => r z * g z θ) ≤ Ci * Xn α (fun z _ => r z) * Xn α g
  /-- Multiplication by an angular profile is lossless in `α` (`HkMul_ang_le`, `Work.Blocks`).

  Two hypotheses are needed and *both* are necessary: `a` is bounded, and its `D_θ`-iterates
  vanish at least like `sin(2θ)` — without the second, `a = 1 + θ^q` (`q < α/5`) breaks the
  conclusion, because the heavy weight `sin(2θ)^{-γ/2}` is unbounded at the boundary.  The
  concrete profiles of the table (`sin(2θ)`, `sin²θ`, `cos(2θ)`, `c2m = cos2θ - sin²θ`) satisfy
  both. -/
  angmul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (f : Fn),
    Work.Spaces.SmoothInt (fun _ (θ : ℝ) => a θ) →
    (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ci) →
    (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ci * Real.sin (2 * θ)) →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) ∧
    Xn α (fun z θ => a θ * f z θ) ≤ Ci * Ci * Xn α f
  /-- Multiplication by an angular profile in the `𝒲^{4,∞}`-norm.  **All three hypotheses are
  necessary**: `a` must be *honestly* smooth (`SmoothInt`; `WlInfMem` alone constrains only the
  totalised derivatives and cannot see oscillations at the non-differentiability points —
  see `N4Fields/NOTES_wang_field_false.md`), its `D_θ`-iterates must vanish like `sin(2θ)` (the
  mixed weight `sin(2θ)^{-α/5}/(α+sin 2θ)` is unbounded at the boundary), and `h` must be
  honestly smooth as well. -/
  wang : ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (h : Fn),
    Work.Spaces.SmoothInt (fun _ (θ : ℝ) => a θ) → Work.Spaces.SmoothInt h →
    (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ci) →
    (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ci * Real.sin (2 * θ)) →
    Work.Spaces.WlInfMem α 4 h →
    Work.Spaces.WlInfMem α 4 (fun z θ => a θ * h z θ) ∧
    Work.Spaces.WlInf α 4 (fun z θ => a θ * h z θ) ≤ Ci * Ci * Work.Spaces.WlInf α 4 h
  /-- Multiplication by a `z`-profile in the `𝒲^{4,∞}`-norm.  As for `wang`, both factors must
  be *honestly* smooth (`SmoothInt`): with only `WlInfMem` the field is false
  (`n4norm_refuted.lean`). -/
  wrad : ∀ α ∈ Set.Ioc 0 α₂, ∀ (φ : ℝ → ℝ) (h : Fn),
    Work.Spaces.SmoothInt (fun z _ => φ z) → Work.Spaces.SmoothInt h →
    Work.Spaces.WlInfMem α 4 (fun z _ => φ z) → Work.Spaces.WlInfMem α 4 h →
    Work.Spaces.WlInfMem α 4 (fun z θ => φ z * h z θ) ∧
    Work.Spaces.WlInf α 4 (fun z θ => φ z * h z θ)
      ≤ Ci * Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h
  /-- **The `𝒲^{4,∞}`-product rule**, with the flat vanishing of one factor on the two angular
  boundary lines which makes the boundary values of `pzIter k` harmless.  This replaces the
  false field `wmul` of the old interface (`H2/AuxProdWFalse.lean`); the pointwise interior
  bound is `H2.prodW_interior_bound`. -/
  wmul : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
    Work.FTS.LocData.SmoothQuad f → Work.FTS.LocData.SmoothQuad g →
    Work.Spaces.WlInfMem α 4 f → Work.Spaces.WlInfMem α 4 g →
    (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ,
      Work.Spaces.pzIter k g z 0 = 0 ∧ Work.Spaces.pzIter k g z (π / 2) = 0) →
    Work.Spaces.WlInfMem α 4 (fun z θ => f z θ * g z θ) ∧
    Work.Spaces.WlInf α 4 (fun z θ => f z θ * g z θ)
      ≤ Ci * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g

/-! ## The `IP`-level contract (N2/N3 for the concrete `IP₄`) -/

/-- **The `IP`-level facts consumed by N4.**

`IP` is the paper's concrete `ℋ⁴` inner product.  The clauses `cs`/`add`/`smul`/`congr` are
the ones of `UnifIP` with the hypothesis `RegQ` required only on the *test function* `g`; the
`RegQ`-hypothesis of the frozen `UnifIP.cs` on the *first* argument is unsatisfiable for the
pieces of `N₀` (see the module docstring of `Defs.lean`).  `t1`–`st` are the transport
estimates of design §3.3 L-N4.5, obtained by summing the per-slot estimates of §H2 over the
slots of `IP₄` (`Work.FTS.H2.Transport1/2/3`, `SpecialTransport`, restated in the interior
class).  This structure is satisfiable (`IP ≡ 0` inhabits it). -/
structure N4Extra (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop where
  pos : 0 < Ct ∧ 0 < α₂
  /-- Cauchy–Schwarz against the `ℋ⁴`-norm. -/
  cs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, RegQ α 4 g → |IP α f g| ≤ Ct * Xn α f * Xn α g
  /-- Additivity in the first argument. -/
  add : ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn, RegQ α 4 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g
  /-- Homogeneity in the first argument. -/
  smul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (c : ℝ) (f g : Fn), RegQ α 4 g →
    IP α (fun z θ => c * f z θ) g = c * IP α f g
  /-- Negation in the first argument (a consequence of `smul`, recorded for convenience). -/
  neg : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, RegQ α 4 g →
    IP α (fun z θ => -f z θ) g = -IP α f g
  /-- `IP` only depends on the first argument through its values on the open quadrant `Qd`. -/
  congr : ∀ α ∈ Set.Ioc 0 α₂, ∀ f f' g : Fn, RegQ α 4 g →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP α f g = IP α f' g
  /-- The `D_z`-self-pairing, lossless: design §5 T5.  This is `UnifIP.Dz_self` with the
  hypothesis `CoerAdm` relaxed to `RegQ` (the direct integration by parts needs only the
  `ℋ⁴`-finiteness of `g`, not the `L₁₂(g)(0) = 0` zero mode).  It must **not** be routed
  through `Transport3`, whose `α^{-1/2}` loss breaks the bootstrap of design §2.3. -/
  dz : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, RegQ α 4 g → |IP α (Work.Spaces.Dz g) g| ≤ Ct * Xn α g ^ 2
  /-- `T1Q`: transport with `D_θ` and an `ℋ⁴`-coefficient (tex 1119). -/
  t1 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g ^ 2
  /-- `T2Q`: transport with `D_z` and an `ℋ⁴`-coefficient. -/
  t2 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g ^ 2
  /-- `T3Q`: transport with `D_z` and a `𝒲^{4,∞}`-coefficient (tex 1213). -/
  t3 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.Spaces.WlInfMem α 4 f → RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Xn α g ^ 2
  /-- `T3Q` with `D_θ` and a `𝒲^{4,∞}`-coefficient. -/
  t4 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.Spaces.WlInfMem α 4 f → RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Xn α g ^ 2
  /-- `STQ`: `SpecialTransport` (tex 1258), the derivative falling on a coefficient which
  vanishes at the angular ends. -/
  st : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.Spaces.VanishTheta f →
    Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f) → RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.pth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) * Xn α g ^ 2

end Work.FTS.Nonlin
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Mu =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlin

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `μ̄` -/


/-! ## `μ` -/

/-- `μ̄` with a scaling constant `K ≥ 0`. -/
theorem mubar_bound_mul {N0v Nv : Fn} {α X K : ℝ} (hK : 0 ≤ K)
    (h0 : |Work.Construction.L12 N0v 0|
      ≤ K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h1 : |Work.Construction.L12 Nv 0|
      ≤ K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)) :
    |Work.Construction.mubar N0v Nv| ≤ 2 * (K * (α ^ 2 + Real.sqrt α * X
      + α ^ (-(3 / 2 : ℝ)) * X ^ 2)) := by
  rw [Work.Construction.mubar]
  have h := abs_add_le (Work.Construction.L12 N0v 0) (Work.Construction.L12 Nv 0)
  linarith

/-- **Design L-N4.8, with a scaling constant `K ≥ 0`.**  From the paper's three zero-mode
estimates (each carrying a constant `K`) one gets
`|μ| ≤ 4K(α + α^{-1}X + α^{-5/2}X²)`, with `X = |g|_{ℋ⁴}`.  The constant `μ` is the
sign-corrected `Construction.mufunS` and the proof is `Work.Construction.mu_bound_mulS`. -/
theorem mu_bound_mul {α X K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) (hK : 0 ≤ K)
    {N0v Nv g : Fn}
    (h0 : |Work.Construction.L12 N0v 0|
      ≤ K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h1 : |Work.Construction.L12 Nv 0|
      ≤ K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h2 : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ K * X) :
    |Work.Construction.mufunS α N0v Nv g|
      ≤ 4 * (K * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)) :=
  Work.Construction.mu_bound_mulS hα hα1 hX hK h0 h1 h2


/-! ## Smallness of `μ` -/

/-- **`|μ| ≤ 1/2`** under the a-priori bound `X ≤ α^{7/4}` (design §2.5). -/
theorem mu_le_half (C : ℝ) (hC : 0 < C) :
    ∃ α₄ : ℝ, 0 < α₄ ∧ ∀ α : ℝ, 0 < α → α ≤ α₄ → ∀ X : ℝ, 0 ≤ X →
      X ≤ α ^ (7 / 4 : ℝ) → ∀ μ : ℝ,
      |μ| ≤ C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) → |μ| ≤ 1 / 2 := by
  have h6C : (0 : ℝ) < 6 * C := by linarith
  refine ⟨min 1 ((1 / (6 * C)) ^ (4 / 3 : ℝ)),
    lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _), ?_⟩
  intro α hα hαle X hX0 hX μ hμ
  have hα1 : α ≤ 1 := le_trans hαle (min_le_left _ _)
  have hαc : α ≤ (1 / (6 * C)) ^ (4 / 3 : ℝ) := le_trans hαle (min_le_right _ _)
  have h1 : α ^ (-(1 : ℝ)) * X ≤ α ^ (3 / 4 : ℝ) := by
    have hrw : α ^ (-(1 : ℝ)) * α ^ (7 / 4 : ℝ) = α ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hα]; norm_num
    calc α ^ (-(1 : ℝ)) * X ≤ α ^ (-(1 : ℝ)) * α ^ (7 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hX (Real.rpow_nonneg hα.le _)
      _ = α ^ (3 / 4 : ℝ) := hrw
  have h2 : α ^ (-(5 / 2 : ℝ)) * X ^ 2 ≤ α := by
    have hX2 : X ^ 2 ≤ (α ^ (7 / 4 : ℝ)) ^ 2 := by nlinarith
    have hpow : α ^ (-(5 / 2 : ℝ)) * (α ^ (7 / 4 : ℝ)) ^ 2 = α := by
      have hsq : (α ^ (7 / 4 : ℝ)) ^ 2 = α ^ (7 / 2 : ℝ) := by
        rw [← Real.rpow_natCast (α ^ (7 / 4 : ℝ)) 2, ← Real.rpow_mul hα.le]; norm_num
      rw [hsq, ← Real.rpow_add hα]; norm_num
    calc α ^ (-(5 / 2 : ℝ)) * X ^ 2 ≤ α ^ (-(5 / 2 : ℝ)) * (α ^ (7 / 4 : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hX2 (Real.rpow_nonneg hα.le _)
      _ = α := hpow
  have h3' : α ^ (3 / 4 : ℝ) ≤ 1 / (6 * C) := by
    have h4 : ((1 / (6 * C)) ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) = 1 / (6 * C) := by
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / (6 * C)),
        show (4 / 3 : ℝ) * (3 / 4) = 1 by norm_num, Real.rpow_one]
    calc α ^ (3 / 4 : ℝ) ≤ ((1 / (6 * C)) ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow hα.le hαc (by norm_num)
      _ = 1 / (6 * C) := h4
  have hαle' : α ≤ α ^ (3 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (x := α)
      (y := (1 : ℝ)) (z := (3 / 4 : ℝ)) (by norm_num)
    rwa [Real.rpow_one] at h
  have hsum : α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2 ≤ 3 * (1 / (6 * C)) := by
    linarith [h1, h2, hαle', h3']
  have hfin : C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hsum hC.le
    have he : C * (3 * (1 / (6 * C))) = 1 / 2 := by field_simp; ring
    linarith [h, he.le, he.ge]
  linarith [hμ, hfin]

/-! ## The paper's choice of `λ` -/

/-- For `μ ≠ -1` the paper's choice `λ = -2μ/(1+μ)` satisfies `μ + λ + μλ = -μ`. -/
theorem lamfun_add {μ : ℝ} (hμ : μ ≠ -1) :
    μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ = -μ := by
  have h1μ : (1 + μ) ≠ 0 := by intro h; exact hμ (by linarith)
  rw [Work.Construction.lamfun]
  have hfac : μ + (-2 * μ / (1 + μ)) + μ * (-2 * μ / (1 + μ))
      = μ + (-2 * μ / (1 + μ)) * (1 + μ) := by ring
  rw [hfac, div_mul_cancel₀ (-2 * μ) h1μ]
  ring

end Work.FTS.Nonlin
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.L12_zero_le_weak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces

open scoped Real Topology
open MeasureTheory Set Filter

/-- Elementary square-root algebra: for `x ≥ 0` and `r > 0`,
`√(3 · x · ((1+r)/r)²) = √3 · √x · ((1+r)/r)`. -/
private lemma sqrt_three_mul_sq_div {x : ℝ} (hx : 0 ≤ x) {r : ℝ} (hr : 0 < r) :
    Real.sqrt (3 * (x * ((1 + r) / r) ^ 2))
      = Real.sqrt 3 * Real.sqrt x * ((1 + r) / r) := by
  have hy : 0 ≤ (1 + r) / r := div_nonneg (by linarith) (le_of_lt hr)
  rw [Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (x * ((1 + r) / r) ^ 2),
    Real.sqrt_mul hx (((1 + r) / r) ^ 2), Real.sqrt_sq hy]
  ring

/-- **The "weak" `L₁₂(0)` bound.**  With only the two integrability hypotheses — the angular
slices `θ ↦ f(r,θ)²` are integrable on `Iθ` for a.e. `r > 0`, and the Hardy-weighted angular
energy `r ↦ (∫_θ f(r,θ)²)·((1+r)/r)²` is integrable on `(0,∞)` — one has
`|L₁₂(f)(0)| ≤ 3 √(∫_{r>0} (∫_θ f(r,θ)²)((1+r)/r)²)`.

This is the Cauchy–Schwarz argument of `Work.FTS.H2.L12ZeroQ` stripped of all regularity
assumptions: the slicewise bound `|L₁₂dens(f)(r)| ≤ √3 √(∫_θ f(r,θ)²)/r`
(`Work.Coercivity.L12dens_sq_slice`) holds for a.e. `r`, and the radial singularity `1/r` is
split as `((1+r)/r)·(1/(1+r))` with the tail weight `(1/(1+r))² ∈ L²(0,∞)` of `L²`-norm `≤ √2`
(`Work.FTS.H2.InvOneAddSq`).  Measurability of the angular energy is not assumed: the massaged
majorant `A(r) = √(3 (∫_θ f(r,θ)²)((1+r)/r)²)` is built from the *assumed* integrable function,
and no measurability or integrability of the density itself is used (`Work.FTS.H2.CS1D` is
unconditional). -/
theorem L12_zero_le_weak (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f r θ) ^ 2) Work.Spaces.Iθ)
    (hfin : MeasureTheory.IntegrableOn
      (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (Set.Ioi (0 : ℝ))) :
    |Work.Construction.L12 f 0| ≤ 3 * Real.sqrt
      (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) with hμdef
  set φ : ℝ → ℝ := fun r => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2 with hφdef
  set Wt : ℝ → ℝ := fun r => ((1 + r) / r) ^ 2 with hWtdef
  set A : ℝ → ℝ := fun r => Real.sqrt (3 * (φ r * Wt r)) with hAdef
  set B : ℝ → ℝ := fun r => 1 / (1 + r) with hBdef
  set g : ℝ → ℝ := fun r => Work.FM.L12dens Work.Spaces.K f r with hgdef
  set X : ℝ := ∫ r in Set.Ioi (0 : ℝ),
      (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 with hXdef
  have hr_mem : ∀ᵐ r ∂μ, r ∈ Set.Ioi (0 : ℝ) :=
    MeasureTheory.ae_restrict_mem measurableSet_Ioi
  -- the angular energy is everywhere nonnegative, as is the Hardy weight
  have hφ0 : ∀ r : ℝ, 0 ≤ φ r := fun r =>
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun θ => sq_nonneg (f r θ))
  have hWt0 : ∀ r : ℝ, 0 ≤ Wt r := fun r => by rw [hWtdef]; exact sq_nonneg _
  -- the majorant `A` is a.e. strongly measurable by construction
  have hA_meas : MeasureTheory.AEStronglyMeasurable A μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable (hfin.aestronglyMeasurable.const_mul 3)
  -- `A²` is the Hardy-weighted angular energy, times `3`
  have hpt : ∀ r : ℝ, A r ^ 2 = 3 * (φ r * Wt r) := by
    intro r
    rw [hAdef]
    dsimp only
    exact Real.sq_sqrt (mul_nonneg (by norm_num) (mul_nonneg (hφ0 r) (hWt0 r)))
  have hA_int : MeasureTheory.Integrable (fun r : ℝ => A r ^ 2) μ := by
    have h3 : MeasureTheory.Integrable (fun r : ℝ => 3 * (φ r * Wt r)) μ := hfin.const_mul 3
    exact h3.congr (Filter.Eventually.of_forall fun r => (hpt r).symm)
  have hmemA : MeasureTheory.MemLp A 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hA_meas).mpr hA_int
  -- the tail weight `1/(1+r)`
  have hB_meas : MeasureTheory.AEStronglyMeasurable B μ := by
    rw [hμdef, hBdef]
    exact (ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
      (fun r hr => by
        have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
        exact ne_of_gt (by show (0 : ℝ) < 1 + r; linarith))).aestronglyMeasurable
      measurableSet_Ioi
  have hB_int : MeasureTheory.Integrable (fun r : ℝ => B r ^ 2) μ := by
    rw [hμdef, hBdef]
    exact (Work.FTS.H2.InvOneAddSq).1
  have hmemB : MeasureTheory.MemLp B 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hB_meas).mpr hB_int
  -- a.e. nonnegativity of the two factors
  have hA0 : 0 ≤ᵐ[μ] A := Filter.Eventually.of_forall fun r => Real.sqrt_nonneg _
  have hB0 : 0 ≤ᵐ[μ] B := by
    filter_upwards [hr_mem] with r hr
    rw [hBdef]
    exact div_nonneg zero_le_one (by linarith [Set.mem_Ioi.mp hr])
  -- the pointwise (a.e.) slicewise bound
  have hbd : ∀ᵐ r ∂μ, |g r| ≤ A r * B r := by
    filter_upwards [hsl, hr_mem] with r hslr hr
    have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
    have hsq : (Work.FM.L12dens Work.Spaces.K f r) ^ 2 ≤ 3 * φ r / r ^ 2 :=
      Work.Coercivity.L12dens_sq_slice f Work.Coercivity.integral_Itheta_K hr' hslr
    have hb : |Work.FM.L12dens Work.Spaces.K f r|
        ≤ Real.sqrt 3 * Real.sqrt (φ r) / r :=
      Work.FTS.H2.abs_le_sqrt_three_mul_sqrt_div hr' (hφ0 r) hsq
    have hkey : A r * B r = Real.sqrt 3 * Real.sqrt (φ r) / r := by
      have hAval : A r = Real.sqrt 3 * Real.sqrt (φ r) * ((1 + r) / r) := by
        rw [hAdef, hWtdef]
        exact sqrt_three_mul_sq_div (hφ0 r) hr'
      rw [hAval, hBdef]
      have h2 : ((1 + r) / r) * (1 / (1 + r)) = 1 / r := by
        have hr0 : r ≠ 0 := ne_of_gt hr'
        have h1r : (1 : ℝ) + r ≠ 0 := by linarith
        field_simp
      calc Real.sqrt 3 * Real.sqrt (φ r) * ((1 + r) / r) * (1 / (1 + r))
          = Real.sqrt 3
              * (Real.sqrt (φ r) * (((1 + r) / r) * (1 / (1 + r)))) := by ring
        _ = Real.sqrt 3 * (Real.sqrt (φ r) * (1 / r)) := by rw [h2]
        _ = Real.sqrt 3 * Real.sqrt (φ r) / r := by ring
    rw [hgdef, hkey]
    exact hb
  -- Cauchy–Schwarz in the radial variable
  have hcs := Work.FTS.H2.CS1D (μ := μ) (g := g) (A := A) (B := B)
    hmemA hmemB hA0 hB0 hbd
  have hLHS : (∫ r, g r ∂μ) = Work.Construction.L12 f 0 := by
    rw [hμdef, hgdef]
    rfl
  have hA2 : (∫ r, A r ^ 2 ∂μ) = 3 * X := by
    rw [hμdef]
    calc ∫ r in Set.Ioi (0 : ℝ), A r ^ 2
        = ∫ r in Set.Ioi (0 : ℝ), 3 * (φ r * Wt r) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r _ => hpt r)
      _ = 3 * ∫ r in Set.Ioi (0 : ℝ), φ r * Wt r :=
          MeasureTheory.integral_const_mul 3 (fun r : ℝ => φ r * Wt r)
      _ = 3 * X := rfl
  have hB2 : (∫ r, B r ^ 2 ∂μ) ≤ 2 := by
    rw [hμdef, hBdef]
    exact (Work.FTS.H2.InvOneAddSq).2
  have hfinal : |Work.Construction.L12 f 0| ≤ Real.sqrt (3 * X) * Real.sqrt 2 := by
    rw [← hLHS]
    exact hcs.trans (mul_le_mul (Real.sqrt_le_sqrt hA2.le) (Real.sqrt_le_sqrt hB2)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hsqrt : Real.sqrt (3 * X) * Real.sqrt 2 = Real.sqrt 6 * Real.sqrt X := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) X]
    rw [show Real.sqrt 3 * Real.sqrt X * Real.sqrt 2
        = (Real.sqrt 3 * Real.sqrt 2) * Real.sqrt X from by ring]
    rw [show Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 from by
      rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (2 : ℝ)]
      norm_num]
  have h6 : Real.sqrt 6 ≤ 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]
  calc |Work.Construction.L12 f 0|
      ≤ Real.sqrt (3 * X) * Real.sqrt 2 := hfinal
    _ = Real.sqrt 6 * Real.sqrt X := hsqrt
    _ ≤ 3 * Real.sqrt X := mul_le_mul_of_nonneg_right h6 (Real.sqrt_nonneg X)

end Work.FTS.Nonlinear.Pieces
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FaSum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

/-!
## `FaSum` — the triangle inequality for the `L¹(ℝ⁺, r⁻¹dr)`-norm

The weight `K θ * ·` and the `r`-weight `r⁻¹` are nonnegative, so the ~"norm" carried by the
double `lintegral`
`‖f‖ := ∫⁻ r in (0,∞), r⁻¹ * ∫⁻ θ in Iθ, |K θ * f r θ|`
is subadditive: if `N` splits on the open quadrant `Qd` as a *finite* sum `∑ k, p k` (the
twenty summands of the nonlinearity `N`), then `‖N‖ ≤ ∑ k ‖p k‖`.

The only point of care is that the split `hsplit` is assumed on the **open** quadrant, whereas
the inner integral runs over the **closed** interval `Iθ = [0, π/2]`.  On the two endpoints the
weight `K` vanishes (`K 0 = K (π/2) = 0`), so the identity propagates for every `r > 0`.

### A parser fix required by the statement as requested

The third hypothesis of the requested statement writes the integrand of the `AEMeasurable`
hypothesis *without the closing bar* of the absolute value,
`ENNReal.ofReal |Work.Spaces.K θ * p k r θ`.  With Mathlib's global absolute-value notation
(`macro:max atomic("|" noWs) a:term noWs "|"`) that is a *parse error*, so the requested
statement cannot be elaborated as it stands (the same integrand is written correctly, with both
bars, in the fourth hypothesis `hout`).

We do not touch the statement: instead we register, **locally to this file**, the missing
`|·|`-without-closing-bar notation (a prefix `|` whose argument is a full term *not* followed by
`|`), which expands to exactly the same `abs` as the standard notation.  Every other occurrence
of `|·|` in the file -- and of the standard `|·|` in files that import this one -- is unaffected,
because the auxiliary parser requires that no `|` follows the argument (so the standard notation
is selected whenever both bars are present) and because the declaration is `local`, hence not
exported.

This is the only way the *requested text* can be elaborated: with the text as requested plus
this notation the third hypothesis means the same thing as the fourth. -/

open Lean Parser in
/-- `notFollowedBy`-guard for the local absolute-value notation without the closing bar. -/
private def noClosingBar : Parser :=
  notFollowedBy (symbol "|") "the closing `|` of the absolute value notation is omitted here"

open Lean Parser in
local macro:max atomic("|" noWs) a:term noClosingBar : term => `(abs $a)


end Work.FTS.Nonlinear.Pieces.rl1Tools
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.Pvec =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

open Work.FTS.Galerkin (Fn)

/-- The twenty summands of `N`, enumerated in the order
`N₁^{gg}, N₁^{gs}, N₁^{sg}, N₁^{ss}, N₂^{gg}, …, N₅^{ss}`. -/
def pv (α : ℝ) (g Φs Φg : Fn) : Fin 20 → Fn :=
  ![Work.FTS.Nonlin.N1gg α g Φg, Work.FTS.Nonlin.N1gs α g Φg,
    Work.FTS.Nonlin.N1sg α Φs g, Work.FTS.Nonlin.N1ss α Φs,
    Work.FTS.Nonlin.N2gg α g Φg, Work.FTS.Nonlin.N2gs α g Φg,
    Work.FTS.Nonlin.N2sg α Φs g, Work.FTS.Nonlin.N2ss α Φs,
    Work.FTS.Nonlin.N3gg α g Φg, Work.FTS.Nonlin.N3gs α g Φg,
    Work.FTS.Nonlin.N3sg α Φs g, Work.FTS.Nonlin.N3ss α Φs,
    Work.FTS.Nonlin.N4gg α g, Work.FTS.Nonlin.N4gs α g,
    Work.FTS.Nonlin.N4sg α g, Work.FTS.Nonlin.N4ss α,
    Work.FTS.Nonlin.N5gg g, Work.FTS.Nonlin.N5gs α g,
    Work.FTS.Nonlin.N5sg α g, Work.FTS.Nonlin.N5ss α]

end Work.FTS.Nonlinear.Pieces.rl1Tools
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.QuadMeasAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

/-- The product measure of the statement: `volume` restricted to `(0,∞)`, times `volume`
restricted to `Iθ = [0,π/2]`. -/
abbrev QdMeas : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- The open quadrant `(0,∞) × (0,π/2)` of the interior estimates. -/
abbrev Qd2 : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)

/-- `(0,∞) × Iθ` and the open quadrant agree outside the two angular boundary lines, a null
set. -/
theorem qd_ae : (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
    =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume] Qd2 :=
  MeasureTheory.Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _)
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm

/-- A function continuous on the open quadrant is a.e. strongly measurable for the product
measure `QdMeas`. -/
theorem aesm_of_contOn_Qd {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) Qd2) :
    AEStronglyMeasurable (Function.uncurry f) QdMeas := by
  have hUm : MeasurableSet Qd2 := (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable (Function.uncurry f)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict Qd2) :=
    hf.aestronglyMeasurable hUm
  rw [QdMeas, MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set qd_ae]
  exact hmain

/-- `SmoothQuad` (that is `C^∞` on the open strip `(-1,∞) × (0,π/2)`) implies a.e. strong
measurability for `QdMeas`. -/
theorem aesm_of_smoothQuad {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    AEStronglyMeasurable (Function.uncurry f) QdMeas :=
  aesm_of_contOn_Qd (h.continuousOn.mono fun p hp =>
    ⟨show (-1 : ℝ) < p.1 by linarith [show (0 : ℝ) < p.1 from hp.1], hp.2⟩)

end Work.FTS.Nonlinear.Pieces.rl1Tools
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.blockMeas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# `blockMeas` — a.e.-measurability of the blocks of the `rl1` rows

The `rl1`-estimates of the N4 chapter integrate the pieces of `N` against the radial weight
`r⁻¹` and the angular weight `K`, on the domain `(0,∞) × Iθ` with the measure `dz dθ`.  Every
`lintegral`/`integral` bookkeeping along the way needs the a.e.-measurability of the integrands
with respect to the product measure

  `bmMeasure = (volume.restrict (Ioi 0)).prod (volume.restrict Iθ)`,

and that is what this file supplies: the sixteen blocks of the `rl1` rows (the datum `g` and
its three first `D`-derivatives, the angular moment `FK g`, the six elliptic coefficients
`Rop/Uop/Vop` of both stream functions `Φ̃_g` and `Φ̃_*`, and the whole `F_*`-package with its
angular moment) are all a.e.-measurable.

The measure is the planar Lebesgue measure restricted to the open quadrant `(0,∞) × (0,π/2)`
(the boundary lines are null), so continuity on the open quadrant suffices; that continuity
comes from `SmoothQuad`, which the packages `GalClass`, `StarPkg`, `EllPkgG` provide for every
block except the `Φ̃_*`-coefficients.  For those one needs `SmoothQuad (Φ̃_*)`, i.e. the
smoothness of `Θ_*(α) = (1/(4α)) sin 2θ · L₁₂(F_*)`, which holds because `F_*` is *separable*
and `L₁₂` therefore collapses to `const · 2/(1+z)`; that computation (`L12_Fstar_general`) is
the only non-formal input here, and it is done for **every** real `α` (the packages carry no
positivity hypothesis on `α`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

/-! ## The measure of the block, and continuity on the open quadrant -/


/-- The product measure of the `rl1` block: Lebesgue measure on `z > 0` times Lebesgue
measure on `Iθ = [0,π/2]`. -/
abbrev bmMeasure : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- The restricted product measure agrees with the planar Lebesgue measure restricted to the
open quadrant: `Iθ` and `(0,π/2)` differ by the two endpoints. -/
theorem ae_prod_eq :
    (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ) =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm
  exact MeasureTheory.Measure.set_prod_ae_eq Filter.EventuallyEq.rfl hθ





/-! ## The three operators preserve `C^∞`-smoothness on the open quadrant -/

theorem sq_pth {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.pth f) :=
  Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU h



/-- `ℛ`, `𝒰` and `𝒱` preserve `C^∞`-smoothness on the open quadrant.  (`𝒰 = -3Ψ - α·D_zΨ`,
`𝒱 = ∂_θΨ - tan θ·Ψ`, and `ℛ` is the same rational expression divided by `cos θ`, which is
non-zero on the quadrant; `tan = sin/cos`.) -/
theorem smoothQuad_ops {α : ℝ} {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad Ψ) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Rop α Ψ) ∧
    Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α Ψ) ∧
    Work.FTS.LocData.SmoothQuad (Work.Construction.Vop Ψ) := by
  have hpz : Work.FTS.LocData.SmoothQuad (Work.Spaces.pz Ψ) :=
    Work.FTS.LocData.contDiffOn_pz Work.Spaces.isOpen_quadU h
  have hpth : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth Ψ) := sq_pth h
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Work.Spaces.quadU :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Work.Spaces.quadU :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have hne : ∀ p ∈ Work.Spaces.quadU, Real.cos p.2 ≠ 0 := by
    intro p hp
    have h2 : p.2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
      ⟨by linarith [(Set.mem_Ioo.mp hp.2).1, Real.pi_pos],
        by linarith [(Set.mem_Ioo.mp hp.2).2]⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo h2)
  have htan : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.tan p.2) Work.Spaces.quadU := by
    rw [show (fun p : ℝ × ℝ => Real.tan p.2) = fun p => Real.sin p.2 / Real.cos p.2 from
      funext fun p => Real.tan_eq_sin_div_cos p.2]
    exact hsin.div hcos hne
  -- `𝒰`
  have hUaux : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => -3 * Function.uncurry Ψ p
        - α * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p) Work.Spaces.quadU :=
    (contDiffOn_const.mul h).sub ((contDiffOn_const.mul contDiffOn_fst).mul hpz)
  have hU : Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α Ψ) :=
    hUaux.congr (fun p _ => rfl)
  -- `𝒱`
  have hVaux : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.pth Ψ) p
        - Real.tan p.2 * Function.uncurry Ψ p) Work.Spaces.quadU :=
    hpth.sub (htan.mul h)
  have hV : Work.FTS.LocData.SmoothQuad (Work.Construction.Vop Ψ) :=
    hVaux.congr (fun p _ => rfl)
  -- `ℛ`
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p) Work.Spaces.quadU :=
    (contDiffOn_const.mul hsin).mul h
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.Spaces.quadU :=
    ((contDiffOn_const.mul hsin).mul contDiffOn_fst).mul hpz
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.Spaces.quadU :=
    hcos.mul hpth
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p
        + α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p) Work.Spaces.quadU :=
    (h1.add h2).add h3
  have hRaux : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (2 * Real.sin p.2 * Function.uncurry Ψ p
        + α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p) / Real.cos p.2)
      Work.Spaces.quadU :=
    hnum.div hcos hne
  have hR : Work.FTS.LocData.SmoothQuad (Work.Construction.Rop α Ψ) :=
    hRaux.congr (fun p _ => rfl)
  exact ⟨hR, hU, hV⟩

/-! ## The angular density of `L₁₂(F_*)`: the profile is separable

`F_*(z,θ) = α (Γ(θ)/c(α)) · F_{*,rad}(z)` is a function of `θ` times a function of `z`, so the
angular integration in `L₁₂dens` factors out and leaves a *constant* `L12FstarConst α` times
`F_{*,rad}(s)/s` — with no hypothesis on `α` (when `c(α) = 0` both sides are `0`). -/





/-! ## The angular moment `FK f` -/


/-! ## The target -/


end Work.FTS.Nonlinear.Pieces.rl1Tools
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The two model equations -/

/-- **The radial model equation.**  `Gz` is the decaying solution of the Euler-type equation

`−(α²z²Gz'') − α(5+α) z Gz' = (5α/4)·φ(z)`,   `φ = VocabO.phiR`,

i.e. `bslOp α (Gz · sin 2θ) = (5α/4)φ·sin 2θ` on the quadrant (the `θ`-operator `L₀` kills
`sin 2θ`).  The explicit solution is `GzProfile` (`Gz.lean`), which is the paper's `G`.
Note the sign convention: with `Gsing α F` the elliptic section's singular term (solving
`α²z²G'' + α(5+α)zG' = (15/4)F_*`), one has `GzProfile α = −Gsing α (Construction.Fstar α)`. -/
def GzOde (α : ℝ) (Gz : ℝ → ℝ) : Prop :=
  ∀ z, 0 < z →
    -(α ^ 2 * z ^ 2 * iteratedDeriv 2 Gz z) - α * (5 + α) * z * deriv Gz z
      = (5 * α / 4) * Work.FTS.VocabO.phiR z

/-- **The angular model.**  `ψ` solves the explicit 1-D problem `L₀ψ = Γ̄` on `(0,π/2)` with
Dirichlet data at both endpoints, the moment normalisation `∫ψ sinθcos²θ = 0` (which pins down
the free additive multiple of `sin 2θ ∈ ker L₀`), and is smooth on the open interval.

The existence statement is `Psi0_exists` (`Psi0.lean`).  The moment condition is what makes the
source `α²φψ` of the remainder have vanishing `F_*`-moment, as required by the weak-class
elliptic estimates (`TT.EllWeakPos`). -/
structure AngModel (α : ℝ) (ψ : ℝ → ℝ) : Prop where
  /-- smooth on the open angular interval -/
  smooth : ContDiffOn ℝ Work.Stability.smoothOrder ψ (Set.Ioo 0 (π / 2))
  /-- continuous up to the endpoints -/
  cont : ContinuousOn ψ (Set.Icc 0 (π / 2))
  /-- left Dirichlet value -/
  bdry0 : ψ 0 = 0
  /-- right Dirichlet value -/
  bdry1 : ψ (π / 2) = 0
  /-- the model equation -/
  eq : ∀ θ ∈ Set.Ioo 0 (π / 2),
    Work.FTS.EllipticEst.Lzero1 ψ θ = Work.FTS.VocabO.GamBar α θ
  /-- the moment normalisation -/
  moment : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0

/-! ## The decomposition of `Φ_*` -/

/-- The **two-term model** `Gz(z)·sin 2θ + α·φ(z)·ψ(θ)`: the part of `Φ_*` whose
`bslOp`-image is `F_* − α²(𝒜φ)ψ` (`phiStar_remainder_source`). -/
def Model (α : ℝ) (Gz ψ : ℝ → ℝ) : Fn :=
  fun z θ => Gz z * Real.sin (2 * θ) + α * Work.FTS.VocabO.phiR z * ψ θ

/-- The **remainder source** `α²·(𝒜φ)(z)·ψ(θ)`: the `O(α²)` separable source left after the
telescoping.  It is orthogonal to `sin θ cos²θ` at every `z` (by `AngModel.moment`), so the
weak-class elliptic estimates apply to it. -/
def RemSource (α : ℝ) (ψ : ℝ → ℝ) : Fn :=
  fun z θ => α ^ 2 * Work.FTS.VocabO.phiA α z * ψ θ


/-! ## The explicit radial profile and the residual splitting -/

/-- **The explicit radial profile** `Gz = −Gsing α (F_*)`, the decaying solution of `GzOde`
(the paper's explicit `G`).  Its `𝒲`-size is `O(α)` (`Gz.lean`). -/
def GzProfile (α : ℝ) : ℝ → ℝ := fun z => -(Work.Elliptic.Gsing α (Work.Construction.Fstar α) z)

/-- The radial factor of the singular part `Θ = (1/4α) sin 2θ L₁₂(F_*)`: one has
`Θ(z,θ) = ThetaProfile z · sin 2θ`. -/
def ThetaProfile : ℝ → ℝ := fun z => 1 / (2 * (1 + z))

/-- The **flat radial factor of `Φ̃_* = Φ_* − Θ`**:  writing
`Φ_* = Gz(z) sin 2θ + α φ(z) ψ(θ) + R`, one has

`Φ̃_* = Aprof α(z)·sin 2θ + α φ(z) ψ(θ) + R`,   `Aprof α = GzProfile α − 1/(2(1+z))`,

and `Aprof α = −Gbar α (F_*)` is of size `O(α)` in `𝒲^{4,∞}`. -/
def Aprof (α : ℝ) : ℝ → ℝ := fun z => GzProfile α z - ThetaProfile z

/-- The explicit expansion of `Φ̃_*` used by the sup-estimates: the flat part, the separable
model part and the remainder. -/
def PhiTilExpansion (α : ℝ) (ψ : ℝ → ℝ) (R : Fn) : Fn :=
  fun z θ => Aprof α z * Real.sin (2 * θ) + α * Work.FTS.VocabO.phiR z * ψ θ + R z θ

/-- `Φ_*` is presented as `Model + R` with `Gz` solving the radial model, `ψ` the angular
model and `R` solving the `O(α²)` remainder equation.  This is the interface consumed by the
sup-estimate nodes; `Uop`, `Vop`, `Rop` of `Φ̃_*` are then read off from `PhiTilExpansion`. -/
structure StarSplit (α : ℝ) (Φs : Fn) (Gz ψ : ℝ → ℝ) (R : Fn) : Prop where
  hα : 0 < α
  gz : GzOde α Gz
  ang : AngModel α ψ
  decomp : Φs = fun z θ => Model α Gz ψ z θ + R z θ
  rem_eq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
    Work.Elliptic.bslOp α R z θ = RemSource α ψ z θ
  rem_smooth : Work.FTS.EllipticEst.SmoothOpen R
  rem_dir0 : ∀ z, R z 0 = 0
  rem_dir1 : ∀ z, R z (π / 2) = 0
  rem_decay : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => R z θ) atTop (𝓝 0)
  rem_mom : ∀ z, 0 < z → Work.Elliptic.Fstar R z = 0

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces

namespace Work.FTS.StrongEps.SupPort

set_option maxHeartbeats 1600000

/-! ## The angular Hardy inequality in the `SmoothOpen` (open quadrant) form

The file `Submission/Work/FTS/H2/LinfQ.lean` proves the same inequality (`HardyThetaO`) for the
class `Work.FTS.LocData.SmoothQuad`, i.e. smoothness on the open strip `(-1,∞) × (0,π/2)`.
Here the hypothesis is the weaker `Work.FTS.EllipticEst.SmoothOpen`, smoothness on the open
quadrant `(0,∞) × (0,π/2)` only, which is what the `SupPort`/`StrongEps` layer provides.  The
proof of `HardyThetaO` uses the smoothness hypothesis *only* through the two one-variable facts

* `θ ↦ g z θ` is `C^∞` on `(0,π/2)` (its Cauchy–Schwarz/FTC factors), and
* `θ ↦ ∂_θ g z θ` is `C^∞` on `(0,π/2)` (continuity of the integrand),

which follow from `SmoothOpen` at every fixed `z > 0` by slicing.  Everything else — the
fundamental theorem on `[ε,θ]` with the boundary value supplied by the limit hypothesis `h0`,
the weighted Cauchy–Schwarz inequality, and the bound `∫_{Iθ} sin(2θ)^{γ-2} ≤ 100/(γ-1)` of
`Work.Spaces.sin_two_rpow` — is unchanged.
-/

/-- `0 ≤ sin(2θ)` on the angular interval `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem HardyThetaOpen (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ) (z : ℝ)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hz : 0 < z)
    (h0 : Filter.Tendsto (fun θ => g z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth g z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), (g z θ) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) * ∫ σ in Work.Spaces.Iθ,
        (Work.Spaces.pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  have hγ1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hp1 : -1 < gam α - 2 := by rw [gam]; linarith
  have hp0 : gam α - 2 ≤ 0 := by rw [gam]; linarith
  have hne0 : Work.Stability.smoothOrder ≠ 0 := Work.FTS.LocData.smoothOrder_ne_zero
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => g z θ')
      (Set.Ioo 0 (π / 2)) := hg.curry_θ hz
  have hdth : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => Work.Spaces.pth g z θ')
      (Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_slice_θ (hg.pth) hz
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  set A : ℝ := ∫ σ in Iθ, (pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hσ) _)
  have hKnn : 0 ≤ 100 / (gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the bound at every `ε ∈ (0,θ)`
  have hkey : ∀ ε ∈ Set.Ioo 0 θ, (g z θ - g z ε) ^ 2 ≤ (100 / (gam α - 1)) * A := by
    intro ε hε
    have hεθ : ε ≤ θ := le_of_lt hε.2
    have hsub : Set.uIcc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      intro x hx
      rw [Set.uIcc_of_le hεθ] at hx
      exact ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_le_of_lt hx.2 hθ1⟩
    have hsubI : Set.Icc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      rw [← Set.uIcc_of_le hεθ]; exact hsub
    have hcontθ : ContinuousOn (fun θ' => g z θ') (Set.Icc ε θ) :=
      hslice.continuousOn.mono hsubI
    have hpthcont : ContinuousOn (fun s => pth g z s) (Set.uIcc ε θ) :=
      hdth.continuousOn.mono hsub
    have hderiv : ∀ x ∈ Set.Ioo ε θ, HasDerivAt (fun θ' => g z θ') (pth g z x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        ⟨lt_trans hε.1 hx.1, lt_trans hx.2 hθ1⟩
      exact ((hslice.differentiableOn hne0).differentiableAt
        (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have hintε : IntervalIntegrable (fun s => pth g z s) volume ε θ := hpthcont.intervalIntegrable
    have hFTC : ∫ s in ε..θ, pth g z s = g z θ - g z ε :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεθ hcontθ hderiv hintε
    have hsincont : ∀ c : ℝ,
        ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ c) (Set.uIcc ε θ) := fun c =>
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun s hs => Or.inl (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo (hsub hs))))
    have hcs := hardyZ_interval_integral_mul_le_sqrt ε θ hεθ
      (hpthcont.mul (hsincont ((2 - gam α) / 2))) (hsincont ((gam α - 2) / 2))
    have hcongr : ∫ s in ε..θ,
          (pth g z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2))
            * (Real.sin (2 * s)) ^ ((gam α - 2) / 2)
        = ∫ s in ε..θ, pth g z s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' := hsub hs
      have hsin : 0 < Real.sin (2 * s) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hs'
      have h1 : (Real.sin (2 * s)) ^ ((2 - gam α) / 2)
          * (Real.sin (2 * s)) ^ ((gam α - 2) / 2) = 1 := by
        rw [← Real.rpow_add hsin, show (2 - gam α) / 2 + (gam α - 2) / 2 = 0 by ring,
          Real.rpow_zero]
      rw [mul_assoc, h1, mul_one]
    have hAint : ∫ s in ε..θ, (pth g z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2 ≤ A := by
      have hEq : ∫ s in ε..θ, (pth g z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2
          = ∫ s in ε..θ, (pth g z s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        have hs' := hsub hs
        have h1 : ((Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2
            = (Real.sin (2 * s)) ^ (2 - gam α) := by
          rw [pow_two, ← Real.rpow_add (Work.FTS.H2.sin_two_pos_of_mem_Ioo hs')]
          congr 1
          ring
        rw [mul_pow, h1]
      rw [hEq, hAdef]
      exact Work.FTS.H2.interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1 hint fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _)
    have hBint : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((gam α - 2) / 2)) ^ 2
        ≤ 100 / (gam α - 1) := by
      have hEq : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((gam α - 2) / 2)) ^ 2
          = ∫ s in ε..θ, (Real.sin (2 * s)) ^ (gam α - 2) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [pow_two, ← Real.rpow_add (Work.FTS.H2.sin_two_pos_of_mem_Ioo (hsub hs))]
        congr 1
        ring
      rw [hEq]
      refine le_trans (Work.FTS.H2.interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1
        (sin_two_rpow (gam α - 2) hp1 hp0).1
        (fun x hx => Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _)) ?_
      have h2 := (sin_two_rpow (gam α - 2) hp1 hp0).2
      rwa [show (gam α - 2) + 1 = gam α - 1 by ring] at h2
    have hstep : |g z θ - g z ε| ≤ Real.sqrt A * Real.sqrt (100 / (gam α - 1)) := by
      rw [← hFTC, ← hcongr]
      exact le_trans hcs (mul_le_mul (Real.sqrt_le_sqrt hAint) (Real.sqrt_le_sqrt hBint)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hsq : (g z θ - g z ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (gam α - 1))) ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (g z θ - g z ε), hstep])
        (le_trans (le_abs_self _) hstep)
    calc (g z θ - g z ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (gam α - 1))) ^ 2 := hsq
      _ = A * (100 / (gam α - 1)) := by rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hKnn]
      _ = (100 / (gam α - 1)) * A := by ring
  -- pass to the limit `ε → 0⁺`
  have hlim : Tendsto (fun ε => (g z θ - g z ε) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 ((g z θ) ^ 2)) := by
    have h1 : Tendsto (fun ε => g z θ - g z ε) (𝓝[>] (0 : ℝ)) (𝓝 (g z θ - 0)) :=
      tendsto_const_nhds.sub h0
    simpa using h1.pow 2
  refine le_of_tendsto hlim ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [isOpen_Iio.mem_nhds hθ0] with ε hε hε0
  exact hkey ε ⟨hε0, hε⟩

end Work.FTS.StrongEps.SupPort
end
end
