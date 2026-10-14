import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.Elliptic.WtoHAux
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.HkSqZfar
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.distEq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter LineDeriv TemperedDistribution
open scoped Real Topology SchwartzMap Laplacian

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Temperate growth of the multipliers -/

/-- A compactly supported `C^∞` function has temperate growth. -/
theorem htg_of_cc {f : E2 → ℂ} (hc : HasCompactSupport f) (hs : ∀ n : ℕ, ContDiff ℝ n f) :
    Function.HasTemperateGrowth f := by
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr hs
  have hcoe : (⇑(hc.toSchwartzMap hfs) : E2 → ℂ) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun hc hfs)
  have h := (hc.toSchwartzMap hfs).hasTemperateGrowth
  rwa [hcoe] at h

/-- `d0` of a compactly supported `C^∞` function has temperate growth. -/
theorem htg_d0 {f : E2 → ℂ} (hc : HasCompactSupport f) (hs : ∀ n : ℕ, ContDiff ℝ n f) :
    Function.HasTemperateGrowth (d0 f) := by
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr hs
  have hcoe : (⇑(hc.toSchwartzMap hfs) : E2 → ℂ) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun hc hfs)
  have hkey : d0 f = (⇑(LineDeriv.lineDerivOp e0 (hc.toSchwartzMap hfs)) : E2 → ℂ) := by
    funext x
    change lineDeriv ℝ f x e0 = (LineDeriv.lineDerivOp e0 (hc.toSchwartzMap hfs)) x
    rw [SchwartzMap.lineDerivOp_apply, hcoe]
  rw [hkey]
  exact (LineDeriv.lineDerivOp e0 (hc.toSchwartzMap hfs)).hasTemperateGrowth

/-- `d1` of a compactly supported `C^∞` function has temperate growth. -/
theorem htg_d1 {f : E2 → ℂ} (hc : HasCompactSupport f) (hs : ∀ n : ℕ, ContDiff ℝ n f) :
    Function.HasTemperateGrowth (d1 f) := by
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr hs
  have hcoe : (⇑(hc.toSchwartzMap hfs) : E2 → ℂ) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun hc hfs)
  have hkey : d1 f = (⇑(LineDeriv.lineDerivOp e1 (hc.toSchwartzMap hfs)) : E2 → ℂ) := by
    funext x
    change lineDeriv ℝ f x e1 = (LineDeriv.lineDerivOp e1 (hc.toSchwartzMap hfs)) x
    rw [SchwartzMap.lineDerivOp_apply, hcoe]
  rw [hkey]
  exact (LineDeriv.lineDerivOp e1 (hc.toSchwartzMap hfs)).hasTemperateGrowth

/-- `d0 ∘ d0` of a compactly supported `C^∞` function has temperate growth. -/
theorem htg_d0d0 {f : E2 → ℂ} (hc : HasCompactSupport f) (hs : ∀ n : ℕ, ContDiff ℝ n f) :
    Function.HasTemperateGrowth (d0 (d0 f)) := by
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr hs
  have hcoe : (⇑(hc.toSchwartzMap hfs) : E2 → ℂ) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun hc hfs)
  have hkey : d0 f = (⇑(LineDeriv.lineDerivOp e0 (hc.toSchwartzMap hfs)) : E2 → ℂ) := by
    funext x
    change lineDeriv ℝ f x e0 = (LineDeriv.lineDerivOp e0 (hc.toSchwartzMap hfs)) x
    rw [SchwartzMap.lineDerivOp_apply, hcoe]
  have hkey2 : d0 (d0 f)
      = (⇑(LineDeriv.lineDerivOp e0 (LineDeriv.lineDerivOp e0 (hc.toSchwartzMap hfs))) :
          E2 → ℂ) := by
    funext x
    change lineDeriv ℝ (d0 f) x e0
      = (LineDeriv.lineDerivOp e0 (LineDeriv.lineDerivOp e0 (hc.toSchwartzMap hfs))) x
    rw [SchwartzMap.lineDerivOp_apply, hkey]
  rw [hkey2]
  exact (LineDeriv.lineDerivOp e0
    (LineDeriv.lineDerivOp e0 (hc.toSchwartzMap hfs))).hasTemperateGrowth

/-- `d1 ∘ d1` of a compactly supported `C^∞` function has temperate growth. -/
theorem htg_d1d1 {f : E2 → ℂ} (hc : HasCompactSupport f) (hs : ∀ n : ℕ, ContDiff ℝ n f) :
    Function.HasTemperateGrowth (d1 (d1 f)) := by
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr hs
  have hcoe : (⇑(hc.toSchwartzMap hfs) : E2 → ℂ) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun hc hfs)
  have hkey : d1 f = (⇑(LineDeriv.lineDerivOp e1 (hc.toSchwartzMap hfs)) : E2 → ℂ) := by
    funext x
    change lineDeriv ℝ f x e1 = (LineDeriv.lineDerivOp e1 (hc.toSchwartzMap hfs)) x
    rw [SchwartzMap.lineDerivOp_apply, hcoe]
  have hkey2 : d1 (d1 f)
      = (⇑(LineDeriv.lineDerivOp e1 (LineDeriv.lineDerivOp e1 (hc.toSchwartzMap hfs))) :
          E2 → ℂ) := by
    funext x
    change lineDeriv ℝ (d1 f) x e1
      = (LineDeriv.lineDerivOp e1 (LineDeriv.lineDerivOp e1 (hc.toSchwartzMap hfs))) x
    rw [SchwartzMap.lineDerivOp_apply, hkey]
  rw [hkey2]
  exact (LineDeriv.lineDerivOp e1
    (LineDeriv.lineDerivOp e1 (hc.toSchwartzMap hfs))).hasTemperateGrowth

/-! ## Germ lemmas for `d0`, `d1` -/

/-- A directional derivative only depends on the germ of the function. -/
theorem lineDeriv_congr_of_eventuallyEq {f g : E2 → ℂ} {x m : E2}
    (h : f =ᶠ[𝓝 x] g) : lineDeriv ℝ f x m = lineDeriv ℝ g x m := by
  have hc : Tendsto (fun t : ℝ => x + t • m) (𝓝 0) (𝓝 x) := by
    have h0 : (x + (0 : ℝ) • m) = x := by simp
    simpa only [h0] using
      (tendsto_const_nhds.add (tendsto_id.smul tendsto_const_nhds) :
        Tendsto (fun t : ℝ => x + t • m) (𝓝 0) (𝓝 (x + (0 : ℝ) • m)))
  change deriv (fun t : ℝ => f (x + t • m)) 0 = deriv (fun t : ℝ => g (x + t • m)) 0
  exact (h.comp_tendsto hc).deriv_eq

/-- `d0` only depends on the germ of the function. -/
theorem d0_congr_of_eventuallyEq {f g : E2 → ℂ} {x : E2} (h : f =ᶠ[𝓝 x] g) :
    d0 f x = d0 g x :=
  lineDeriv_congr_of_eventuallyEq (m := e0) h

/-- `d1` only depends on the germ of the function. -/
theorem d1_congr_of_eventuallyEq {f g : E2 → ℂ} {x : E2} (h : f =ᶠ[𝓝 x] g) :
    d1 f x = d1 g x :=
  lineDeriv_congr_of_eventuallyEq (m := e1) h

/-- If two functions agree on a neighbourhood of `x`, then so do their derivatives. -/
theorem d0_eventuallyEq {f g : E2 → ℂ} {x : E2} (h : f =ᶠ[𝓝 x] g) :
    d0 f =ᶠ[𝓝 x] d0 g := by
  obtain ⟨s, hs, hsub⟩ := h.exists_mem
  obtain ⟨V, hVs, hVopen, hxV⟩ := mem_nhds_iff.mp hs
  filter_upwards [hVopen.mem_nhds hxV] with y hy
  exact d0_congr_of_eventuallyEq (Filter.eventually_iff.mpr
    (Filter.mem_of_superset (hVopen.mem_nhds hy) (fun z hz => hsub (hVs hz))))

/-- If two functions agree on a neighbourhood of `x`, then so do their derivatives. -/
theorem d1_eventuallyEq {f g : E2 → ℂ} {x : E2} (h : f =ᶠ[𝓝 x] g) :
    d1 f =ᶠ[𝓝 x] d1 g := by
  obtain ⟨s, hs, hsub⟩ := h.exists_mem
  obtain ⟨V, hVs, hVopen, hxV⟩ := mem_nhds_iff.mp hs
  filter_upwards [hVopen.mem_nhds hxV] with y hy
  exact d1_congr_of_eventuallyEq (Filter.eventually_iff.mpr
    (Filter.mem_of_superset (hVopen.mem_nhds hy) (fun z hz => hsub (hVs hz))))

/-- Second order version of `d0_congr_of_eventuallyEq`. -/
theorem d0d0_congr_of_eventuallyEq {f g : E2 → ℂ} {x : E2} (h : f =ᶠ[𝓝 x] g) :
    d0 (d0 f) x = d0 (d0 g) x :=
  d0_congr_of_eventuallyEq (d0_eventuallyEq h)

/-- Second order version of `d1_congr_of_eventuallyEq`. -/
theorem d1d1_congr_of_eventuallyEq {f g : E2 → ℂ} {x : E2} (h : f =ᶠ[𝓝 x] g) :
    d1 (d1 f) x = d1 (d1 g) x :=
  d1_congr_of_eventuallyEq (d1_eventuallyEq h)

/-! ## Pairings of the distributional expression with a test function -/

/-- `g · A` paired with a test function `φ`, in integral form. -/
theorem smulLeftCLM_apply_pair {V χ : E2 → ℂ} {A : TemperedDistribution E2 ℂ}
    (hpair : Pair V χ A) {g : E2 → ℂ} (hg : Function.HasTemperateGrowth g)
    (φ : SchwartzMap E2 ℂ) :
    (TemperedDistribution.smulLeftCLM ℂ g A) φ
      = ∫ x, (χ x * (g x * (φ : E2 → ℂ) x)) * V x := by
  have h := hpair (SchwartzMap.smulLeftCLM ℂ g φ)
  rw [TemperedDistribution.smulLeftCLM_apply_apply, h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
  ring

/-- `g · A` paired with a test function `φ`, in the other bracketing. -/
theorem smulLeftCLM_apply_pair' {V χ : E2 → ℂ} {A : TemperedDistribution E2 ℂ}
    (hpair : Pair V χ A) {g : E2 → ℂ} (hg : Function.HasTemperateGrowth g)
    (φ : SchwartzMap E2 ℂ) :
    (TemperedDistribution.smulLeftCLM ℂ g A) φ
      = ∫ x, (χ x * g x * (φ : E2 → ℂ) x) * V x := by
  rw [smulLeftCLM_apply_pair hpair hg φ]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  ring

/-- `g · ∂_{e₀} A` paired with a test function `φ`, in integral form. -/
theorem smulLeftCLM_d0_pair {V χ : E2 → ℂ} {A : TemperedDistribution E2 ℂ}
    (hpair : Pair V χ A) {g : E2 → ℂ} (hg : Function.HasTemperateGrowth g)
    (φ : SchwartzMap E2 ℂ) :
    (TemperedDistribution.smulLeftCLM ℂ g (LineDeriv.lineDerivOp e0 A)) φ
      = - ∫ x, (χ x * d0 (fun y => g y * (φ : E2 → ℂ) y) x) * V x := by
  have h := hpair (LineDeriv.lineDerivOp e0 (SchwartzMap.smulLeftCLM ℂ g φ))
  rw [TemperedDistribution.smulLeftCLM_apply_apply, TemperedDistribution.lineDerivOp_apply_apply,
    map_neg, h]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  have hS : (⇑(SchwartzMap.smulLeftCLM ℂ g φ) : E2 → ℂ) = fun y => g y * (φ : E2 → ℂ) y := by
    funext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
  rw [show (LineDeriv.lineDerivOp e0 (SchwartzMap.smulLeftCLM ℂ g φ)) x • (χ x * V x)
      = lineDeriv ℝ (⇑(SchwartzMap.smulLeftCLM ℂ g φ)) x e0 * (χ x * V x) from by
    rw [SchwartzMap.lineDerivOp_apply, smul_eq_mul]]
  rw [hS]
  rw [show d0 (fun y => g y * (φ : E2 → ℂ) y) x
      = lineDeriv ℝ (fun y => g y * (φ : E2 → ℂ) y) x e0 from rfl]
  ring

/-- `g · ∂_{e₁} A` paired with a test function `φ`, in integral form. -/
theorem smulLeftCLM_d1_pair {V χ : E2 → ℂ} {A : TemperedDistribution E2 ℂ}
    (hpair : Pair V χ A) {g : E2 → ℂ} (hg : Function.HasTemperateGrowth g)
    (φ : SchwartzMap E2 ℂ) :
    (TemperedDistribution.smulLeftCLM ℂ g (LineDeriv.lineDerivOp e1 A)) φ
      = - ∫ x, (χ x * d1 (fun y => g y * (φ : E2 → ℂ) y) x) * V x := by
  have h := hpair (LineDeriv.lineDerivOp e1 (SchwartzMap.smulLeftCLM ℂ g φ))
  rw [TemperedDistribution.smulLeftCLM_apply_apply, TemperedDistribution.lineDerivOp_apply_apply,
    map_neg, h]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  have hS : (⇑(SchwartzMap.smulLeftCLM ℂ g φ) : E2 → ℂ) = fun y => g y * (φ : E2 → ℂ) y := by
    funext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
  rw [show (LineDeriv.lineDerivOp e1 (SchwartzMap.smulLeftCLM ℂ g φ)) x • (χ x * V x)
      = lineDeriv ℝ (⇑(SchwartzMap.smulLeftCLM ℂ g φ)) x e1 * (χ x * V x) from by
    rw [SchwartzMap.lineDerivOp_apply, smul_eq_mul]]
  rw [hS]
  rw [show d1 (fun y => g y * (φ : E2 → ℂ) y) x
      = lineDeriv ℝ (fun y => g y * (φ : E2 → ℂ) y) x e1 from rfl]
  ring

/-- `-A` paired with a test function `φ`, in integral form. -/
theorem neg_apply_pair {V χ : E2 → ℂ} {A : TemperedDistribution E2 ℂ}
    (hpair : Pair V χ A) (φ : SchwartzMap E2 ℂ) :
    (-A) φ = - ∫ x, (χ x * (φ : E2 → ℂ) x) * V x := by
  have h := hpair φ
  have hneg : (-A) φ = -(A φ) := by simp
  rw [hneg, h]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [smul_eq_mul]
  ring

/-! ## A smooth cutoff which is `1` near the supports -/

/-- There is a smooth compactly supported `ξ : E2 → ℂ` equal to `1` on a neighbourhood of
`tsupport χ ∪ tsupport χ'`. -/
theorem exists_cutoff_cc {χ χ' : E2 → ℂ} (hχc : HasCompactSupport χ)
    (hχ'c : HasCompactSupport χ') :
    ∃ ξ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n ξ) ∧ HasCompactSupport ξ ∧
      (∀ x, x ∈ tsupport χ ∪ tsupport χ' → ξ =ᶠ[𝓝 x] 1) ∧
      (∀ x, x ∈ tsupport χ ∪ tsupport χ' → ξ x = 1) := by
  have hKb : Bornology.IsBounded (tsupport χ ∪ tsupport χ') :=
    hχc.isBounded.union hχ'c.isBounded
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E2)).mp hKb
  have hR' : tsupport χ ∪ tsupport χ' ⊆ Metric.closedBall (0 : E2) |R| := by
    intro x hx
    have h1 : x ∈ Metric.closedBall (0 : E2) R := hR hx
    rw [Metric.mem_closedBall] at h1 ⊢
    exact h1.trans (le_abs_self R)
  let b : ContDiffBump (0 : E2) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  have hb1 : ∀ x, x ∈ tsupport χ ∪ tsupport χ' → b x = 1 := by
    intro x hx
    apply b.one_of_mem_closedBall
    have hxR : x ∈ Metric.closedBall (0 : E2) |R| := hR' hx
    rw [Metric.mem_closedBall] at hxR ⊢
    show dist x 0 ≤ |R| + 1
    linarith
  have hbev : ∀ x, x ∈ tsupport χ ∪ tsupport χ' → b =ᶠ[𝓝 x] 1 := by
    intro x hx
    apply b.eventuallyEq_one_of_mem_ball
    have hxR : x ∈ Metric.closedBall (0 : E2) |R| := hR' hx
    rw [Metric.mem_closedBall] at hxR
    rw [Metric.mem_ball]
    show dist x 0 < |R| + 1
    linarith
  refine ⟨fun x => (b x : ℂ), fun n => ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have hb : ContDiff ℝ n b := b.contDiff
    have h : ContDiff ℝ n (fun x : E2 => Complex.ofRealCLM (b x)) :=
      Complex.ofRealCLM.contDiff.comp hb
    simpa only [Complex.ofRealCLM_apply] using h
  · refine b.hasCompactSupport.mono' ?_
    intro x hx
    have hx' : b x ≠ 0 := fun h => hx (by simp [h])
    exact subset_tsupport b (Function.mem_support.mpr hx')
  · filter_upwards [hbev x hx] with y hy
    show (b y : ℂ) = 1
    rw [hy]
    norm_num
  · show (b x : ℂ) = 1
    rw [hb1 x hx]
    norm_num

/-! ## The distributional identity -/

theorem distEq {V G : E2 → ℂ} {A A' Ad : TemperedDistribution E2 ℂ} {χ χ' σc tt : E2 → ℂ}
    (hpair : Work.EllipticEst.InteriorRegularity.Q0.Pair V χ A)
    (hpair' : Work.EllipticEst.InteriorRegularity.Q0.Pair V χ' A')
    (hpairG : Work.EllipticEst.InteriorRegularity.Q0.Pair G χ Ad)
    (hloc : Work.EllipticEst.InteriorRegularity.Q0.LocalId V G χ χ' σc tt)
    (hintV : MeasureTheory.Integrable (fun x : E2 => χ x * V x))
    (hintV' : MeasureTheory.Integrable (fun x : E2 => χ' x * V x))
    (hintG : MeasureTheory.Integrable (fun x : E2 => χ x * G x))
    (hχc : HasCompactSupport χ) (hχs : ∀ n : ℕ, ContDiff ℝ n χ)
    (hχ'c : HasCompactSupport χ') (hχ's : ∀ n : ℕ, ContDiff ℝ n χ')
    (hσc : HasCompactSupport σc) (hσs : ∀ n : ℕ, ContDiff ℝ n σc)
    (httc : HasCompactSupport tt) (htts : ∀ n : ℕ, ContDiff ℝ n tt) :
    Laplacian.laplacian A
      = - Ad
        + TemperedDistribution.smulLeftCLM ℂ (fun x => 5 * σc x)
            (LineDeriv.lineDerivOp Work.EllipticEst.InteriorRegularity.e0 A)
        - TemperedDistribution.smulLeftCLM ℂ (fun x => σc x * tt x)
            (LineDeriv.lineDerivOp Work.EllipticEst.InteriorRegularity.e1 A)
        - TemperedDistribution.smulLeftCLM ℂ (fun x => 6 * σc x) A
        + TemperedDistribution.smulLeftCLM ℂ
            (fun x => Work.EllipticEst.InteriorRegularity.d0 (Work.EllipticEst.InteriorRegularity.d0 χ) x
              + Work.EllipticEst.InteriorRegularity.d1 (Work.EllipticEst.InteriorRegularity.d1 χ) x
              - 5 * Work.EllipticEst.InteriorRegularity.d0 χ x
              + tt x * Work.EllipticEst.InteriorRegularity.d1 χ x) A'
        + TemperedDistribution.smulLeftCLM ℂ
            (fun x => 2 * Work.EllipticEst.InteriorRegularity.d0 χ x)
            (LineDeriv.lineDerivOp Work.EllipticEst.InteriorRegularity.e0 A')
        + TemperedDistribution.smulLeftCLM ℂ
            (fun x => 2 * Work.EllipticEst.InteriorRegularity.d1 χ x)
            (LineDeriv.lineDerivOp Work.EllipticEst.InteriorRegularity.e1 A') := by
  -- temperate growth of the multipliers
  have hσt : Function.HasTemperateGrowth σc := htg_of_cc hσc hσs
  have httt : Function.HasTemperateGrowth tt := htg_of_cc httc htts
  have hg1 : Function.HasTemperateGrowth (fun x : E2 => 5 * σc x) :=
    (Function.HasTemperateGrowth.const (5 : ℂ)).mul hσt
  have hg2 : Function.HasTemperateGrowth (fun x : E2 => σc x * tt x) := hσt.mul httt
  have hg3 : Function.HasTemperateGrowth (fun x : E2 => 6 * σc x) :=
    (Function.HasTemperateGrowth.const (6 : ℂ)).mul hσt
  have hg4 : Function.HasTemperateGrowth (fun x : E2 =>
      d0 (d0 χ) x + d1 (d1 χ) x - 5 * d0 χ x + tt x * d1 χ x) := by
    have h1 : Function.HasTemperateGrowth (d0 (d0 χ)) := htg_d0d0 hχc hχs
    have h2 : Function.HasTemperateGrowth (d1 (d1 χ)) := htg_d1d1 hχc hχs
    have h3 : Function.HasTemperateGrowth (d0 χ) := htg_d0 hχc hχs
    have h4 : Function.HasTemperateGrowth (d1 χ) := htg_d1 hχc hχs
    have h5 : Function.HasTemperateGrowth (fun x : E2 => 5 * d0 χ x) :=
      (Function.HasTemperateGrowth.const (5 : ℂ)).mul h3
    have h6 : Function.HasTemperateGrowth (fun x : E2 => tt x * d1 χ x) := httt.mul h4
    have h7 : Function.HasTemperateGrowth (fun x : E2 =>
        d0 (d0 χ) x + d1 (d1 χ) x) := h1.add h2
    have h8 : Function.HasTemperateGrowth (fun x : E2 =>
        d0 (d0 χ) x + d1 (d1 χ) x - 5 * d0 χ x) := h7.sub h5
    exact h8.add h6
  have hg5 : Function.HasTemperateGrowth (fun x : E2 => 2 * d0 χ x) :=
    (Function.HasTemperateGrowth.const (2 : ℂ)).mul (htg_d0 hχc hχs)
  have hg6 : Function.HasTemperateGrowth (fun x : E2 => 2 * d1 χ x) :=
    (Function.HasTemperateGrowth.const (2 : ℂ)).mul (htg_d1 hχc hχs)
  -- the cutoff
  obtain ⟨ξ, hξs, hξc, hξev, hξ1⟩ := exists_cutoff_cc hχc hχ'c
  ext φ
  -- push the evaluation at `φ` inside the right hand side
  conv_rhs => simp only [add_apply, sub_apply, neg_apply]
  -- the auxiliary test function
  set φ' : E2 → ℂ := fun y => ξ y * (φ : E2 → ℂ) y with hφ'
  have hφ's : ∀ n : ℕ, ContDiff ℝ n φ' := by
    intro n
    rw [hφ']
    exact (hξs n).mul (φ.smooth n)
  have hφ'c : HasCompactSupport φ' := by
    rw [hφ']
    refine hξc.mono' ?_
    intro x hx
    have hx' : ξ x ≠ 0 := fun h => hx (by simp [h])
    exact subset_tsupport ξ (Function.mem_support.mpr hx')
  have hφ'x : ∀ x, x ∈ tsupport χ ∪ tsupport χ' → φ' x = (φ : E2 → ℂ) x := by
    intro x hx
    rw [hφ']
    simp [hξ1 x hx]
  have hφ'g : ∀ x, x ∈ tsupport χ ∪ tsupport χ' → φ' =ᶠ[𝓝 x] (φ : E2 → ℂ) := by
    intro x hx
    filter_upwards [hξev x hx] with y hy
    rw [hφ']
    simp [hy]
  have hχK : ∀ {x : E2}, χ x ≠ 0 → x ∈ tsupport χ ∪ tsupport χ' := fun {x} hx =>
    Or.inl (subset_tsupport χ (Function.mem_support.mpr hx))
  have hχ'K : ∀ {x : E2}, χ' x ≠ 0 → x ∈ tsupport χ ∪ tsupport χ' := fun {x} hx =>
    Or.inr (subset_tsupport χ' (Function.mem_support.mpr hx))
  -- the pairing evaluations at a general Schwartz test function
  have hL : (Laplacian.laplacian A) φ
      = ∫ x, (χ x * (d0 (d0 (φ : E2 → ℂ)) x + d1 (d1 (φ : E2 → ℂ)) x)) * V x := by
    rw [TemperedDistribution.laplacian_apply_apply]
    have h := hpair (Laplacian.laplacian φ)
    rw [h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    have hlap : (Laplacian.laplacian φ) x
        = d0 (d0 (φ : E2 → ℂ)) x + d1 (d1 (φ : E2 → ℂ)) x := by
      rw [schwartzMap_laplacian_apply]
      rfl
    rw [hlap, smul_eq_mul]
    ring
  have hT0 : -(Ad φ) = - ∫ x, (χ x * (φ : E2 → ℂ) x) * G x := neg_apply_pair hpairG φ
  have hT1 : (TemperedDistribution.smulLeftCLM ℂ (fun x => 5 * σc x)
        (LineDeriv.lineDerivOp e0 A)) φ
      = - ∫ x, (χ x * d0 (fun y => (5 * σc y) * (φ : E2 → ℂ) y) x) * V x :=
    smulLeftCLM_d0_pair hpair hg1 φ
  have hT2 : (TemperedDistribution.smulLeftCLM ℂ (fun x => σc x * tt x)
        (LineDeriv.lineDerivOp e1 A)) φ
      = - ∫ x, (χ x * d1 (fun y => (σc y * tt y) * (φ : E2 → ℂ) y) x) * V x :=
    smulLeftCLM_d1_pair hpair hg2 φ
  have hT3 : (TemperedDistribution.smulLeftCLM ℂ (fun x => 6 * σc x) A) φ
      = ∫ x, (χ x * (6 * σc x) * (φ : E2 → ℂ) x) * V x :=
    smulLeftCLM_apply_pair' hpair hg3 φ
  have hT4 : (TemperedDistribution.smulLeftCLM ℂ
        (fun x => d0 (d0 χ) x
          + d1 (d1 χ) x
          - 5 * d0 χ x
          + tt x * d1 χ x) A') φ
      = ∫ x, (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x
          + tt x * d1 χ x) * (φ : E2 → ℂ) x)) * V x :=
    smulLeftCLM_apply_pair hpair' hg4 φ
  have hT5 : (TemperedDistribution.smulLeftCLM ℂ (fun x => 2 * d0 χ x)
        (LineDeriv.lineDerivOp e0 A')) φ
      = - ∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * (φ : E2 → ℂ) y) x) * V x :=
    smulLeftCLM_d0_pair hpair' hg5 φ
  have hT6 : (TemperedDistribution.smulLeftCLM ℂ (fun x => 2 * d1 χ x)
        (LineDeriv.lineDerivOp e1 A')) φ
      = - ∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * (φ : E2 → ℂ) y) x) * V x :=
    smulLeftCLM_d1_pair hpair' hg6 φ
  -- the localized identity, transferred from the cutoff test function to `φ`
  have e0 : ∫ x, (χ x * (d0 (d0 φ') x + d1 (d1 φ') x)) * V x
      = ∫ x, (χ x * (d0 (d0 (φ : E2 → ℂ)) x + d1 (d1 (φ : E2 → ℂ)) x)) * V x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hx : χ x = 0
    · rw [hx]; ring
    · have hg := hφ'g x (hχK hx)
      rw [d0d0_congr_of_eventuallyEq hg, d1d1_congr_of_eventuallyEq hg]
  have e1 : ∫ x, (χ x * d0 (fun y => (5 * σc y) * φ' y) x) * V x
      = ∫ x, (χ x * d0 (fun y => (5 * σc y) * (φ : E2 → ℂ) y) x) * V x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hx : χ x = 0
    · rw [hx]; ring
    · have hg := hφ'g x (hχK hx)
      have hg' : (fun y => (5 * σc y) * φ' y)
          =ᶠ[𝓝 x] (fun y => (5 * σc y) * (φ : E2 → ℂ) y) := by
        filter_upwards [hg] with y hy
        rw [hy]
      rw [d0_congr_of_eventuallyEq hg']
  have e2 : ∫ x, (χ x * d1 (fun y => (σc y * tt y) * φ' y) x) * V x
      = ∫ x, (χ x * d1 (fun y => (σc y * tt y) * (φ : E2 → ℂ) y) x) * V x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hx : χ x = 0
    · rw [hx]; ring
    · have hg := hφ'g x (hχK hx)
      have hg' : (fun y => (σc y * tt y) * φ' y)
          =ᶠ[𝓝 x] (fun y => (σc y * tt y) * (φ : E2 → ℂ) y) := by
        filter_upwards [hg] with y hy
        rw [hy]
      rw [d1_congr_of_eventuallyEq hg']
  have e3 : ∫ x, (χ x * (6 * σc x) * φ' x) * V x
      = ∫ x, (χ x * (6 * σc x) * (φ : E2 → ℂ) x) * V x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hx : χ x = 0
    · rw [hx]; ring
    · rw [hφ'x x (hχK hx)]
  have e4 : ∫ x, (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x
          + tt x * d1 χ x) * φ' x)) * V x
      = ∫ x, (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x
          + tt x * d1 χ x) * (φ : E2 → ℂ) x)) * V x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hx : χ' x = 0
    · rw [hx]; ring
    · rw [hφ'x x (hχ'K hx)]
  have e5 : ∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φ' y) x) * V x
      = ∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * (φ : E2 → ℂ) y) x) * V x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hx : χ' x = 0
    · rw [hx]; ring
    · have hg := hφ'g x (hχ'K hx)
      have hg' : (fun y => (2 * d0 χ y) * φ' y)
          =ᶠ[𝓝 x] (fun y => (2 * d0 χ y) * (φ : E2 → ℂ) y) := by
        filter_upwards [hg] with y hy
        rw [hy]
      rw [d0_congr_of_eventuallyEq hg']
  have e6 : ∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φ' y) x) * V x
      = ∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * (φ : E2 → ℂ) y) x) * V x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hx : χ' x = 0
    · rw [hx]; ring
    · have hg := hφ'g x (hχ'K hx)
      have hg' : (fun y => (2 * d1 χ y) * φ' y)
          =ᶠ[𝓝 x] (fun y => (2 * d1 χ y) * (φ : E2 → ℂ) y) := by
        filter_upwards [hg] with y hy
        rw [hy]
      rw [d1_congr_of_eventuallyEq hg']
  have e7 : ∫ x, (χ x * φ' x) * G x
      = ∫ x, (χ x * (φ : E2 → ℂ) x) * G x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hx : χ x = 0
    · rw [hx]; ring
    · rw [hφ'x x (hχK hx)]
  have hlocφ : ∫ x, (χ x * (d0 (d0 (φ : E2 → ℂ)) x + d1 (d1 (φ : E2 → ℂ)) x)) * V x
      = - (∫ x, (χ x * d0 (fun y => (5 * σc y) * (φ : E2 → ℂ) y) x) * V x)
        + (∫ x, (χ x * d1 (fun y => (σc y * tt y) * (φ : E2 → ℂ) y) x) * V x)
        - (∫ x, (χ x * (6 * σc x) * (φ : E2 → ℂ) x) * V x)
        + (∫ x, (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x
            + tt x * d1 χ x) * (φ : E2 → ℂ) x)) * V x)
        - (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * (φ : E2 → ℂ) y) x) * V x)
        - (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * (φ : E2 → ℂ) y) x) * V x)
        - (∫ x, (χ x * (φ : E2 → ℂ) x) * G x) := by
    have h := hloc φ' hφ's hφ'c
    rw [e0, e1, e2, e3, e4, e5, e6, e7] at h
    exact h
  rw [hL, hT0, hT1, hT2, hT3, hT4, hT5, hT6]
  exact hlocφ.trans (by ring)

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.Td =====
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

/-- The tempered distribution of an integrable function on `E2`. -/
def Td (f : E2 → ℂ) (hf : Integrable f) : 𝓢'(E2, ℂ) :=
  Lp.toTemperedDistribution (memLp_one_iff_integrable.mpr hf).toLp

theorem Td_apply (f : E2 → ℂ) (hf : Integrable f) (ψ : 𝓢(E2, ℂ)) :
    Td f hf ψ = ∫ x, ψ x • f x := by
  rw [Td, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_one_iff_integrable.mpr hf).coeFn_toLp] with x hx
  rw [hx]




/-- A compactly supported `C^∞` function has temperate growth. -/
theorem hasTemperateGrowth_of_cc {f : E2 → ℂ} (hc : HasCompactSupport f)
    (hs : ∀ n : ℕ, ContDiff ℝ n f) : Function.HasTemperateGrowth f := by
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr hs
  have hcoe : (⇑(hc.toSchwartzMap hfs) : E2 → ℂ) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun hc hfs)
  have h := (hc.toSchwartzMap hfs).hasTemperateGrowth
  rwa [hcoe] at h


/-- The distribution of a compactly supported `C^∞` function lies in every `H^s`. -/
theorem Td_memSobolev_of_smooth_compact {f : E2 → ℂ} (hint : Integrable f)
    (hc : HasCompactSupport f) (hs : ∀ n : ℕ, ContDiff ℝ n f) (s : ℝ) :
    TemperedDistribution.MemSobolev s 2 (Td f hint) := by
  have hf1 : MemLp f 1 volume := memLp_one_iff_integrable.mpr hint
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr hs
  have hcoe : (⇑(hc.toSchwartzMap hfs) : E2 → ℂ) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun hc hfs)
  have hf2 : MemLp f 2 volume := by
    have h := (hc.toSchwartzMap hfs).memLp 2 volume
    rwa [hcoe] at h
  have hmain : TemperedDistribution.MemSobolev s 2
      (Lp.toTemperedDistribution hf2.toLp) := Q0.ccMemSobolev (s := s) (f := f) (hf := hf2) hc hs
  have heq : Lp.toTemperedDistribution hf1.toLp = Lp.toTemperedDistribution hf2.toLp := by
    ext ψ
    rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [hf1.coeFn_toLp, hf2.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  rw [Td, heq]
  exact hmain

/-- A bound for a continuous compactly supported function. -/
theorem exists_norm_bound_of_cc {g : E2 → ℂ} (hc : HasCompactSupport g)
    (hs : ∀ n : ℕ, ContDiff ℝ n g) : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hc.isCompact.exists_bound_of_continuousOn
    ((hs 0).continuous.continuousOn)
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport g
  · exact le_trans (hC x hx) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact le_max_right _ _

/-- An integrable function times a compactly supported smooth function is integrable. -/
theorem integrable_mul_of_cc {f : E2 → ℂ} (hf : Integrable f) {g : E2 → ℂ}
    (hc : HasCompactSupport g) (hs : ∀ n : ℕ, ContDiff ℝ n g) :
    Integrable (fun x => g x * f x) := by
  obtain ⟨C, hC⟩ := exists_norm_bound_of_cc hc hs
  refine Integrable.mono' (hf.norm.const_mul C) ?_ ?_
  · exact ((hs 0).continuous.aestronglyMeasurable).mul hf.aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- `L¹ ⊂ H^{-2}` in the `Td` notation (dimension `2 ≤ 3`). -/
theorem Td_memSobolev_neg_two {f : E2 → ℂ} (hf : Integrable f) :
    TemperedDistribution.MemSobolev (-2) 2 (Td f hf) := by
  rw [Td]
  exact memSobolev_neg_two (E := E2) (by rw [finrank_E2]; norm_num)
    (memLp_one_iff_integrable.mpr hf)

/- The distribution `Td f` of an integrable function is kept opaque for elaboration: this
keeps the unification of the large expressions in the Sobolev tower cheap.  All the lemmas about
`Td` are proved above, before the attribute is set. -/
attribute [irreducible] Td

end Work.EllipticEst.InteriorRegularity.VT
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.kopRepresentative =====
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
set_option maxHeartbeats 1600000

/-- `Kop` with the multiplier `tan (· 1)` replaced by an arbitrary multiplier `tt`. -/
def KopWith (tt ψ : E2 → ℂ) : E2 → ℂ := fun x =>
  - d0 (d0 ψ) x - d1 (d1 ψ) x - 5 * d0 ψ x + tt x * d1 ψ x + (tt x ^ 2 - 5) * ψ x

/-- `KopWith tt ψ` is continuous as soon as `ψ` together with its first and second directional
derivatives is continuous, and `tt` is continuous. -/
theorem continuous_kopWith {tt ψ : E2 → ℂ} (hψ : Continuous ψ)
    (hd0ψ : Continuous (d0 ψ)) (hd1ψ : Continuous (d1 ψ))
    (hd0d0ψ : Continuous (d0 (d0 ψ))) (hd1d1ψ : Continuous (d1 (d1 ψ)))
    (htt : Continuous tt) : Continuous (KopWith tt ψ) := by
  unfold KopWith
  have hA : Continuous (fun x : E2 => -d0 (d0 ψ) x - d1 (d1 ψ) x - 5 * d0 ψ x) :=
    (hd0d0ψ.neg.sub hd1d1ψ).sub (hd0ψ.const_mul 5)
  have hB : Continuous (fun x : E2 => tt x * d1 ψ x) := htt.mul hd1ψ
  have hC : Continuous (fun x : E2 => (tt x ^ 2 - 5) * ψ x) :=
    ((htt.pow 2).sub continuous_const).mul hψ
  exact (hA.add hB).add hC

theorem kopRepresentative {χ φc tt : Work.EllipticEst.InteriorRegularity.E2 → ℂ}
    {U : Set Work.EllipticEst.InteriorRegularity.E2} (hU : IsOpen U)
    (hχc : HasCompactSupport χ) (htsU : tsupport χ ⊆ U)
    (hχs : ∀ n : ℕ, ContDiff ℝ n χ) (hφs : ∀ n : ℕ, ContDiff ℝ n φc)
    (htts : ∀ n : ℕ, ContDiff ℝ n tt)
    (htt1 : ∀ x ∈ U, tt x = (Real.tan (x 1) : ℂ)) :
    ∃ K : Work.EllipticEst.InteriorRegularity.E2 → ℂ,
      Continuous K ∧ HasCompactSupport K ∧
        ∀ x, Work.EllipticEst.InteriorRegularity.Kop (fun y => χ y * φc y) x = K x := by
  have hψsm : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => χ y * φc y) :=
    fun n => (hχs n).mul (hφs n)
  have hψc : Continuous (fun y : E2 => χ y * φc y) := (hψsm 0).continuous
  have hd0ψc : Continuous (d0 (fun y : E2 => χ y * φc y)) := (Loc.contDiff_d0 hψsm 0).continuous
  have hd1ψc : Continuous (d1 (fun y : E2 => χ y * φc y)) := (Loc.contDiff_d1 hψsm 0).continuous
  have hd0d0ψc : Continuous (d0 (d0 (fun y : E2 => χ y * φc y))) :=
    (Loc.contDiff_d0 (fun n => Loc.contDiff_d0 hψsm n) 0).continuous
  have hd1d1ψc : Continuous (d1 (d1 (fun y : E2 => χ y * φc y))) :=
    (Loc.contDiff_d1 (fun n => Loc.contDiff_d1 hψsm n) 0).continuous
  have httc : Continuous tt := (htts 0).continuous
  have hKcontW : Continuous (KopWith tt (fun y : E2 => χ y * φc y)) :=
    continuous_kopWith hψc hd0ψc hd1ψc hd0d0ψc hd1d1ψc httc
  -- `Kop ψ` vanishes identically off the topological support of `χ`
  have hKzero : ∀ x : E2, x ∉ tsupport χ → Kop (fun y : E2 => χ y * φc y) x = 0 := by
    intro x hx
    have hW : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
    have hχ0W : ∀ y ∈ (tsupport χ)ᶜ, χ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
    have hψev : (fun y : E2 => χ y * φc y) =ᶠ[𝓝 x] 0 :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hx)
        (fun y hy => by simp [hχ0W y hy])
    have hψx : χ x * φc x = 0 := by rw [hχ0W x hx, zero_mul]
    have hd0 : d0 (fun y : E2 => χ y * φc y) x = 0 :=
      Loc.d0_eq_zero_of_eventuallyEq_zero hψev
    have hd1 : d1 (fun y : E2 => χ y * φc y) x = 0 :=
      Loc.d1_eq_zero_of_eventuallyEq_zero hψev
    have hd0ev : d0 (fun y : E2 => χ y * φc y) =ᶠ[𝓝 x] 0 :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hx)
        (fun y hy => Loc.d0_eq_zero_of_eventuallyEq_zero
          (Filter.eventuallyEq_of_mem (hW.mem_nhds hy) (fun z hz => by simp [hχ0W z hz])))
    have hd1ev : d1 (fun y : E2 => χ y * φc y) =ᶠ[𝓝 x] 0 :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hx)
        (fun y hy => Loc.d1_eq_zero_of_eventuallyEq_zero
          (Filter.eventuallyEq_of_mem (hW.mem_nhds hy) (fun z hz => by simp [hχ0W z hz])))
    have hd0d0 : d0 (d0 (fun y : E2 => χ y * φc y)) x = 0 :=
      Loc.d0_eq_zero_of_eventuallyEq_zero hd0ev
    have hd1d1 : d1 (d1 (fun y : E2 => χ y * φc y)) x = 0 :=
      Loc.d1_eq_zero_of_eventuallyEq_zero hd1ev
    have eK : Kop (fun y : E2 => χ y * φc y) x
        = - d0 (d0 (fun y : E2 => χ y * φc y)) x - d1 (d1 (fun y : E2 => χ y * φc y)) x
          - 5 * d0 (fun y : E2 => χ y * φc y) x
          + (Real.tan (x 1) : ℂ) * d1 (fun y : E2 => χ y * φc y) x
          + (((Real.tan (x 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ x * φc x) := by
      rw [show Kop (fun y : E2 => χ y * φc y) = fun z : E2 =>
          - d0 (d0 (fun y : E2 => χ y * φc y)) z - d1 (d1 (fun y : E2 => χ y * φc y)) z
            - 5 * d0 (fun y : E2 => χ y * φc y) z
            + (Real.tan (z 1) : ℂ) * d1 (fun y : E2 => χ y * φc y) z
            + (((Real.tan (z 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ z * φc z) from rfl]
    rw [eK, hd0d0, hd1d1, hd0, hd1, hψx]
    ring
  have hKsub : tsupport (Kop (fun y : E2 => χ y * φc y)) ⊆ tsupport χ := by
    show closure (Function.support (Kop (fun y : E2 => χ y * φc y))) ⊆ tsupport χ
    exact closure_minimal (fun x hx => by
      rw [Function.mem_support] at hx
      by_contra hxn
      exact hx (hKzero x hxn)) (isClosed_tsupport χ)
  have hKcc : HasCompactSupport (Kop (fun y : E2 => χ y * φc y)) :=
    IsCompact.of_isClosed_subset hχc (isClosed_tsupport (Kop (fun y : E2 => χ y * φc y))) hKsub
  -- on `U` the function agrees with the globally continuous `KopWith tt`
  have hKop_eq : ∀ w ∈ U, Kop (fun y : E2 => χ y * φc y) w
      = KopWith tt (fun y : E2 => χ y * φc y) w := by
    intro w hw
    have h1 : tt w = (Real.tan (w 1) : ℂ) := htt1 w hw
    have h2 : (((Real.tan (w 1)) ^ 2 - 5 : ℝ) : ℂ) = ((Real.tan (w 1) : ℂ)) ^ 2 - 5 := by
      push_cast
      ring
    have e1 : Kop (fun y : E2 => χ y * φc y) w
        = - d0 (d0 (fun y : E2 => χ y * φc y)) w - d1 (d1 (fun y : E2 => χ y * φc y)) w
          - 5 * d0 (fun y : E2 => χ y * φc y) w
          + (Real.tan (w 1) : ℂ) * d1 (fun y : E2 => χ y * φc y) w
          + (((Real.tan (w 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ w * φc w) := by
      rw [show Kop (fun y : E2 => χ y * φc y) = fun z : E2 =>
          - d0 (d0 (fun y : E2 => χ y * φc y)) z - d1 (d1 (fun y : E2 => χ y * φc y)) z
            - 5 * d0 (fun y : E2 => χ y * φc y) z
            + (Real.tan (z 1) : ℂ) * d1 (fun y : E2 => χ y * φc y) z
            + (((Real.tan (z 1)) ^ 2 - 5 : ℝ) : ℂ) * (χ z * φc z) from rfl]
    have e2 : KopWith tt (fun y : E2 => χ y * φc y) w
        = - d0 (d0 (fun y : E2 => χ y * φc y)) w - d1 (d1 (fun y : E2 => χ y * φc y)) w
          - 5 * d0 (fun y : E2 => χ y * φc y) w
          + tt w * d1 (fun y : E2 => χ y * φc y) w
          + (tt w ^ 2 - 5) * (χ w * φc w) := by
      rw [show KopWith tt (fun y : E2 => χ y * φc y) = fun z : E2 =>
          - d0 (d0 (fun y : E2 => χ y * φc y)) z - d1 (d1 (fun y : E2 => χ y * φc y)) z
            - 5 * d0 (fun y : E2 => χ y * φc y) z
            + tt z * d1 (fun y : E2 => χ y * φc y) z
            + (tt z ^ 2 - 5) * (χ z * φc z) from rfl]
    rw [e1, e2, h1, ← h2]
  have hKcont : Continuous (Kop (fun y : E2 => χ y * φc y)) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · have hev : Kop (fun y : E2 => χ y * φc y)
          =ᶠ[𝓝 x] KopWith tt (fun y : E2 => χ y * φc y) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hKop_eq
      exact (continuousAt_congr hev).mpr hKcontW.continuousAt
    · have hxn : x ∉ tsupport χ := fun h => hx (htsU h)
      have hev : Kop (fun y : E2 => χ y * φc y) =ᶠ[𝓝 x] (fun _ : E2 => (0 : ℂ)) :=
        Filter.eventuallyEq_of_mem ((isClosed_tsupport χ).isOpen_compl.mem_nhds hxn)
          (fun y hy => hKzero y hy)
      exact hev.continuousAt
  exact ⟨Kop (fun y : E2 => χ y * φc y), hKcont, hKcc, fun x => rfl⟩

end Work.EllipticEst.InteriorRegularity.VT
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori

open Work.FTS.Nonlin
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif ConvPoint Slab muDyn lamDyn dynLin dynRHS prof)

set_option autoImplicit false

/-! ## The constants of the a-priori bound (design §2.1–2.2)

They are all *explicit* functions of the constants of `UnifIP` and of N4's `pairing_bound`. -/

/-- The dissipation scale `κ = cc·clo/Cup` of the bootstrap (design §2.1). -/
def kappa (cc clo Cup : ℝ) : ℝ := cc * clo / Cup

/-- The radius `C₀ = max(2C_N/κ, 2√(Ccs/clo))` of the a-priori ball (design §2.2). -/
def C0 (CcN cc clo Cup Ccs : ℝ) : ℝ :=
  max (2 * CcN / kappa cc clo Cup) (2 * Real.sqrt (Ccs / clo))

/-- The smallness threshold of the closing inequality:
`α_cl = min(1, (16(C₀+C₀²+C₀³)²)⁻¹)`; for `α ≤ α_cl` one has
`(C₀+C₀²)√α + C₀³α^{3/2} < 1` (`alphaCl_key`). -/
def alphaCl (C₀ : ℝ) : ℝ := min 1 (1 / (16 * (C₀ + C₀ ^ 2 + C₀ ^ 3) ^ 2))

/-- The smallness threshold of the a-priori bound (design §2.2):
`α₅ = min{1/4, α₂, α₄, α_cl, C₀^{-4}}`.  The last term guarantees `C₀α² ≤ α^{7/4}`, the
smallness under which N4's pairing estimate applies (`C0_mul_sq_le`). -/
def alpha5 (CcN cc clo Cup Ccs α₂ α₄ : ℝ) : ℝ :=
  min (min (1 / 4) α₂) (min α₄ (min (alphaCl (C0 CcN cc clo Cup Ccs))
    ((C0 CcN cc clo Cup Ccs) ^ (-(4 : ℝ)))))

/-- The radius `R = √clo·C₀·α²` of the coefficient ball (`DynInputs.R`, design §2.3). -/
def Rstar (clo C₀ α : ℝ) : ℝ := Real.sqrt clo * C₀ * α ^ 2


/-! ## The two hypotheses of the chapter

* `PairData` is the *output* of N4's `pairing_bound` (design §3.6): the modulation bound plus the
  pairing estimate for the assembled right-hand side, with `C_N` and the range `α₄` exhibited.
* `GalEnergyIneq` is the inequality the bootstrap consumes: it is the conjunction of the N2
  coercivity clause and the N4 pairing estimate *after* they have been assembled with the exact
  Galerkin energy identity.  The assembly is `galerkin_energy_ineq` (design §4 L-N5.4); it is the
  only place where the structural facts `RegQ α 4 (𝓛_Γ^T gₙ)`, `RegQ α 4 (gRHS …)` and the
  `IP`-orthonormality of the Galerkin span are used. -/

/-- The modulation constant `μ` of the *total* stream function `Φ = Φs + Φg`, as a function of the
profile `g` (this is `muDyn α Φ g τ` with the families evaluated).  It is
`Construction.mufunS`, the sign-corrected constant of `FTS_MUFUN_SIGN.md` §5, so that
`2α·muOf = μ̄ + L₁₂(Transport g)(0)`. -/
def muOf (α : ℝ) (g Φ : Fn) : ℝ :=
  Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
    (Work.Construction.N α (Work.Construction.Ftot α g) Φ) g

/-- The pairing of N4's right-hand side `gRHS` with the profile `g`, at the modulations
`μ = muOf α g Φ`, `λ = lamfun μ`. -/
def rhsPair (IP : ℝ → Fn → Fn → ℝ) (α : ℝ) (g Φ : Fn) : ℝ :=
  IP α (Work.Construction.gRHS α (muOf α g Φ) (Work.Construction.lamfun (muOf α g Φ))
    (Work.Construction.Ftot α g) Φ g) g

/-- **The output of N4's `pairing_bound`** (design §3.6), with the two constants exhibited: a
universal `C_N > 0` and a range `α₄` such that, for `0 < α ≤ α₄` and every admissible pair
(`g ∈ GalClass`, `Φ_* ∈ StarPkg`, `Φ_g ∈ EllPkgG`) with `|g|_{ℋ⁴} ≤ α^{7/4}`, the modulation
constant and the pairing obey the paper's estimate. -/
structure PairData (IP : ℝ → Fn → Fn → ℝ) (CcN Ce Cs α₄ : ℝ) : Prop where
  /-- the universal constant of the estimate. -/
  hCcN : 0 < CcN
  /-- the range of `α` of the estimate. -/
  hα₄ : 0 < α₄
  /-- the modulation bound and the pairing bound of N4. -/
  bound : ∀ α : ℝ, 0 < α → α ≤ α₄ → ∀ g Φs Φg : Fn,
    GalClass α g → StarPkg α Cs Φs → EllPkgG α Ce g Φg → Xn α g ≤ α ^ (7 / 4 : ℝ) →
    |muOf α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * (α + α ^ (-(1 : ℝ)) * Xn α g + α ^ (-(5 / 2 : ℝ)) * Xn α g ^ 2)
      ∧ |muOf α g (fun z θ => Φs z θ + Φg z θ)| ≤ 1 / 2
      ∧ |rhsPair IP α g (fun z θ => Φs z θ + Φg z θ)| ≤ CcN * Pbd α (Xn α g)

/-- **The Galerkin energy inequality** (design §4 L-N5.4): along every solution `c` of the
projected ODE on `[0,T]`, at every time at which the profile is small enough for N4's pairing
estimate to apply (`|gₙ|_{ℋ⁴} ≤ α^{7/4}`, the paper's smallness hypothesis), the fake-time
derivative `E' = 2 Σ_k c_k ċ_k` of the coefficient energy is bounded by minus the dissipation plus
the nonlinearity.  The smallness hypothesis is not a restriction: the energy bootstrap only uses
the inequality at the barrier level, where `|gₙ|_{ℋ⁴} ≤ C₀α² ≤ α^{7/4}` (`C0_mul_sq_le`). -/
def GalEnergyIneq (IP : ℝ → Fn → Fn → ℝ) (α cc CcN : ℝ) (φ : ℕ → Fn) (Psi : Fam → Fam)
    (g₀ : Fn) : Prop :=
  ∀ (n : ℕ) (T : ℝ) (c : ℝ → Fin n → ℝ),
    IsSolOn (galField α (IP α) φ n Psi) (coeffOf (IP α) g₀ φ n) T c →
    ∀ τ ∈ Set.Icc 0 T, Xn α (galFun φ (c τ)) ≤ α ^ (7 / 4 : ℝ) →
      2 * (∑ k : Fin n, c τ k * galField α (IP α) φ n Psi τ (c τ) k)
        ≤ -2 * cc * Work.Spaces.HkSq α 4 (galFun φ (c τ))
          + 2 * CcN * Pbd α (Xn α (galFun φ (c τ)))

/-- The four a-priori fields of N6's `DynInputs`, in the exact shapes of design §1.3 and §4:
`hInit`, `hCoeffBound`, `hProfileBdd` and `hLimBound`.  They are stated *conditionally on* the
Galerkin energy inequality `hE`, which is the a-priori input of the chapter (N2's coercivity
assembled with N4's pairing estimate by `galerkin_energy_ineq`); with `hE` fixed, each field has
literally the shape of the corresponding field of `Work.FTS.Galerkin.DynInputs`. -/
structure AprioriFields (IP : ℝ → Fn → Fn → ℝ) (α C₀ clo cc CcN : ℝ) (φ : ℕ → Fn)
    (Psi : Fam → Fam) (g₀ : Fn) (hE : GalEnergyIneq IP α cc CcN φ Psi g₀) : Prop where
  /-- **`hInit`** (design L-N5.6): the projected datum lies in the a-priori ball. -/
  hInit : ∀ n : ℕ, ∑ k : Fin n, (coeffOf (IP α) g₀ φ n k) ^ 2 ≤ (Rstar clo C₀ α) ^ 2
  /-- **`hCoeffBound`** (design L-N5.7): every Galerkin solution stays in the a-priori ball. -/
  hCoeffBound : ∀ (n : ℕ) (T : ℝ), 0 ≤ T → ∀ c : ℝ → Fin n → ℝ,
    IsSolOn (galField α (IP α) φ n Psi) (coeffOf (IP α) g₀ φ n) T c →
    ∀ τ ∈ Set.Icc 0 T, ∑ k : Fin n, (c τ k) ^ 2 ≤ (Rstar clo C₀ α) ^ 2
  /-- **`hProfileBdd`** (design L-N5.10): the Galerkin profiles are uniformly bounded on compact
  subsets of the slab. -/
  hProfileBdd : ∀ c, IsGalFam α (IP α) φ Psi (Rstar clo C₀ α) c →
    ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Slab →
      ∃ Cb : ℝ, ∀ n : ℕ, ∀ p ∈ K, |prof φ c n p| ≤ Cb
  /-- **`hLimBound`** (design §1.3, L-N5.9): the limit of a convergent subsequence of Galerkin
  profiles obeys the same a-priori bound. -/
  hLimBound : ∀ c, IsGalFam α (IP α) φ Psi (Rstar clo C₀ α) c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    (∀ τ : ℝ, 0 ≤ τ → LocData.SmoothQuad (slice g τ)) →
    ∀ τ : ℝ, 0 ≤ τ → Xn α (slice g τ) ≤ C₀ * α ^ 2

end Work.FTS.Apriori
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Basic =====
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

/-! ## The clean operator and its defects -/

/-- **The clean operator** `𝓛̂ = 𝓛 − Transport`: the paper's `𝓛` with the angular-transport
term subtracted and **no nonlocal term**.  It is the operator whose coercivity the modified
induction propagates: `D_θ` commutes with it *exactly*, and its `D_z`-commutator is the
explicit bounded function `E2hat`. -/
def Lhat (f : Fn) : Fn := Work.Coercivity.L f - Work.Coercivity.Transport f

/-- Unfolded: `𝓛̂f = f + D_z f − 2f/(1+z) − 3 D_θ f/(1+z)`. -/
theorem Lhat_eq (f : Fn) (z θ : ℝ) :
    Lhat f z θ = f z θ + Work.Spaces.Dz f z θ - 2 * f z θ / (1 + z)
      - 3 * Work.Spaces.Dth f z θ / (1 + z) := by
  simp only [Lhat, Pi.sub_apply, Work.Coercivity.L, Work.Coercivity.Transport]

/-- **The `D_z`-commutator defect of `Lhat`**, explicitly:
`Ê₂ f = (2zf + 3z·D_θf)/(1+z)²`.  Compare with the paper's `E₂`, which contains the
nonlocal pieces `D_z[(2zΓ/(c(1+z)²))L₁₂ f]`; here they are absent, which is why this
defect is bounded by `(|f| + |D_θ f|)` with absolute constants and *uniformly in α*. -/
def E2hat (f : Fn) : Fn := fun z θ =>
  (2 * z * f z θ + 3 * z * Work.Spaces.Dth f z θ) / (1 + z) ^ 2

/-- Unfolded `E2hat`. -/
theorem E2hat_eq (f : Fn) (z θ : ℝ) :
    E2hat f z θ = (2 * z * f z θ + 3 * z * Work.Spaces.Dth f z θ) / (1 + z) ^ 2 := rfl

/-- **The pointwise bound on the `D_z`-defect**: on `z ≥ 0`, `|Ê₂ f| ≤ (2|f| + 3|D_θ f|)/4`.
This is the only estimate the induction needs about the defect, and it carries no `α`. -/
theorem E2hat_abs_le (f : Fn) {z θ : ℝ} (hz : 0 ≤ z) :
    |E2hat f z θ| ≤ (2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) / 4 := by
  rw [E2hat_eq]
  have hden : 0 < (1 + z) ^ 2 := by positivity
  have hzle : z / (1 + z) ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ hden]; nlinarith [sq_nonneg (1 - z)]
  have hnum : |2 * z * f z θ + 3 * z * Work.Spaces.Dth f z θ|
      ≤ (2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) * z := by
    calc |2 * z * f z θ + 3 * z * Work.Spaces.Dth f z θ|
        ≤ |2 * z * f z θ| + |3 * z * Work.Spaces.Dth f z θ| := abs_add_le _ _
      _ = 2 * z * |f z θ| + 3 * z * |Work.Spaces.Dth f z θ| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul,
            abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num), abs_of_nonneg hz,
            abs_of_nonneg (show (0:ℝ) ≤ 3 by norm_num)]
      _ ≤ (2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) * z := le_of_eq (by ring)
  have hZ : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz hden.le
  calc |(2 * z * f z θ + 3 * z * Work.Spaces.Dth f z θ) / (1 + z) ^ 2|
      = |2 * z * f z θ + 3 * z * Work.Spaces.Dth f z θ| / (1 + z) ^ 2 := by
        rw [abs_div, abs_of_pos hden]
    _ ≤ ((2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) * z) / (1 + z) ^ 2 :=
        div_le_div_of_nonneg_right hnum hden.le
    _ = (2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) * (z / (1 + z) ^ 2) := by ring
    _ ≤ (2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) * (1 / 4) :=
        mul_le_mul_of_nonneg_left hzle (by positivity)
    _ = (2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) / 4 := by ring

/-- **The transfer defect** `𝓛_Γ^T f − 𝓛̂f`: everything in `𝓛_Γ^T` that is not in `𝓛̂`,
i.e. the nonlocal term `−(2zΓ/(c(1+z)²))L₁₂ f` and the projector correction
`(Γ/c)(2z²/(1+z)³)L₁₂(Transport f)(0)` (the `Proj`-part of `𝓛_Γ^T`). -/
def Corr (α : ℝ) (f : Fn) : Fn := Work.Coercivity.LGammaT α f - Lhat f

/-- Unfolded `Corr`. -/
theorem Corr_eq (α : ℝ) (f : Fn) (z θ : ℝ) :
    Corr α f z θ = -(2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
        * Work.Coercivity.L12f f z
      + (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := by
  simp only [Corr, Pi.sub_apply, Lhat_eq, Work.Coercivity.LGammaT, Work.Coercivity.LGamma,
    Work.Coercivity.Proj, Work.Coercivity.L, Work.Coercivity.Transport]
  ring

/-- **The decomposition of the paper's operator**: `𝓛_Γ^T = 𝓛̂ + Corr`. -/
theorem LGammaT_eq_Lhat_add_Corr (α : ℝ) (f : Fn) :
    Work.Coercivity.LGammaT α f = Lhat f + Corr α f := by
  funext z θ
  simp only [Pi.add_apply, Corr, Pi.sub_apply]
  ring

/-! ## The concrete inner products -/


/-- The paper's recursion, one step, with *explicit* step coefficients. -/
def step (c₁ c₂ : ℝ) (IP : Fn → Fn → ℝ) : Fn → Fn → ℝ :=
  Work.Coercivity.HkIPStep c₁ c₂ IP

end Work.FTS.CoercivityFix
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.ATop.Tk_le_of_pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# From a pointwise bound to a bound on the top angular slot

The top angular slot of the level-`k` integrand of `A` is

  `Step.Tk α k A = ∫_z∈Iz ∫_θ∈Iθ (D_θ^k A · Wt α)²`

(`Work.FTS.EllipticEst.remov.Step.Tk`, with `D_θ^k A = mixed 0 k A`).  This file shows that a
*pointwise* domination of that single slot by `K` times the sum of the level-`(k-1)` integrands
of `A` and of a second function `Φ` integrates to

  `Tk α k A ≤ K * (HkSq α (k-1) A + HkSq α (k-1) Φ)`.

Two features of the statement deserve a comment.

* The pointwise hypothesis is assumed only on the **open** quadrant (`0 < z`, `0 < θ < π/2`)
  — the region where the divisions by `sin(2θ)` and by `z` are meaningful.  The domain of
  integration, however, is the closed quadrant `Iz × Iθ`.  The boundary `{z = 0} ∪ {θ = 0} ∪
  {θ = π/2}` is a null set, so it is irrelevant; the proof nevertheless treats it honestly:
  on the `θ`-boundary the hypothesis holds a.e. in `θ` (`θ ↦ θ ∈ Ioo 0 (π/2)` is true off the
  two-point null set `{0, π/2}`), which is exactly what `integral_mono_of_nonneg` consumes, and
  on the `z`-boundary `Wt α 0 θ = 0`, so the slot itself vanishes there.

* Nothing beyond `HkMem α (k-1)` of the two functions is assumed: those hypotheses give the
  integrability of the dominating function at both stages of the iteration, while the dominated
  slot is never assumed integrable (`integral_mono_of_nonneg` needs only nonnegativity of the
  smaller function).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.ATop

set_option autoImplicit false

/-- Off the two endpoints of `Iθ`, the angular variable lies in the open interval `(0,π/2)`
almost everywhere.  This is what allows the pointwise hypothesis (which is stated on the open
quadrant) to be used inside the integral over the closed interval. -/
private lemma ae_mem_Ioo_restrict_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  change ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
    θ ∈ Set.Ioo 0 (Real.pi / 2)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_
    (Set.Finite.measure_zero (s := ({(0 : ℝ), Real.pi / 2} : Set ℝ)) (Set.toFinite _)
      MeasureTheory.volume)
  intro θ hθ
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ioo, not_imp, not_and, not_lt] at hθ
  obtain ⟨h1, h2⟩ := hθ
  rcases eq_or_lt_of_le h1.1 with h | h
  · simp [← h]
  · have : θ = Real.pi / 2 := le_antisymm h1.2 (h2 h)
    simp [this]

/-- The weight `Wt` vanishes on the axis `z = 0` (where `w 0 = 0` by Lean's convention for
division by zero). -/
private lemma Wt_zero_left (α θ : ℝ) : Work.Spaces.Wt α 0 θ = 0 := by
  simp [Work.Spaces.Wt, Work.Spaces.w]

theorem Tk_le_of_pointwise {α : ℝ} {k : ℕ} {K : ℝ} {A Φ : ℝ → ℝ → ℝ} (hK : 0 ≤ K)
    (hmemA : Work.Spaces.HkMem α (k - 1) A)
    (hmemΦ : Work.Spaces.HkMem α (k - 1) Φ)
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DthIter k A z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
            + Work.Spaces.HkIntegrand α (k - 1) Φ z θ)) :
    Work.FTS.EllipticEst.remov.Step.Tk α k A
      ≤ K * (Work.Spaces.HkSq α (k - 1) A + Work.Spaces.HkSq α (k - 1) Φ) := by
  -- The `θ`-slice bound, valid on the whole half-line `Iz`.
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ,
            K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + Work.Spaces.HkIntegrand α (k - 1) Φ z θ) := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (((hmemA.1 z hz).add (hmemΦ.1 z hz)).const_mul K) ?_
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · -- the boundary slice `z = 0`: the slot vanishes identically
      subst hz0
      refine Filter.Eventually.of_forall fun θ => ?_
      beta_reduce
      rw [Work.Spaces.mixed_zero_left]
      rw [Wt_zero_left, mul_zero, sq, mul_zero]
      exact mul_nonneg hK (add_nonneg (Work.Spaces.HkIntegrand_nonneg α (k - 1) A 0 θ)
        (Work.Spaces.HkIntegrand_nonneg α (k - 1) Φ 0 θ))
    · -- interior slices: the pointwise hypothesis holds a.e. in `θ`
      filter_upwards [ae_mem_Ioo_restrict_Iθ] with θ hθ
      rw [Work.Spaces.mixed_zero_left]
      exact hpt z θ hzpos hθ.1 hθ.2
  -- Integration in `z`.
  have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
            + Work.Spaces.HkIntegrand α (k - 1) Φ z θ) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) ?_ ?_
    · -- the dominating double integral is honest
      refine MeasureTheory.Integrable.congr
        ((hmemA.2.const_mul K).add (hmemΦ.2.const_mul K)) ?_
      change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))),
        K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
          + K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) Φ z θ)
        = ∫ θ in Work.Spaces.Iθ, K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + Work.Spaces.HkIntegrand α (k - 1) Φ z θ)
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      refine Filter.Eventually.of_forall fun z hz => ?_
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add (hmemA.1 z hz) (hmemΦ.1 z hz), mul_add]
    · change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))),
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ,
            K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + Work.Spaces.HkIntegrand α (k - 1) Φ z θ)
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      exact Filter.Eventually.of_forall fun z hz => hinner z hz
  -- Evaluation of the dominating double integral.
  have hcong : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
          + Work.Spaces.HkIntegrand α (k - 1) Φ z θ))
      = K * (Work.Spaces.HkSq α (k - 1) A + Work.Spaces.HkSq α (k - 1) Φ) := by
    have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
            + Work.Spaces.HkIntegrand α (k - 1) Φ z θ))
        = ∫ z in Work.Spaces.Iz,
            (K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
              + K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) Φ z θ)) := by
      refine MeasureTheory.integral_congr_ae ?_
      change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))),
        (∫ θ in Work.Spaces.Iθ, K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + Work.Spaces.HkIntegrand α (k - 1) Φ z θ))
        = K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
              + K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) Φ z θ)
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      refine Filter.Eventually.of_forall fun z hz => ?_
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add (hmemA.1 z hz) (hmemΦ.1 z hz), mul_add]
    rw [h1, MeasureTheory.integral_add (hmemA.2.const_mul K) (hmemΦ.2.const_mul K),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      Work.Spaces.HkSq, Work.Spaces.HkSq]
    ring
  rw [Work.FTS.EllipticEst.remov.Step.Tk, Work.Spaces.HkSq, Work.Spaces.HkSq]
  exact le_trans hmain hcong.le

end Work.FTS.EllipticEst.remov.ATop
end
end
-- ===== merged: Submission.Work.FTS.GalerkinFix.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

open Work.FTS.Nonlin (RegQ GalClass CoerAdm UnifIP GalBasis StarPkg EllPkgG PsiCan Xn)

set_option autoImplicit false

/-! ## The admissible data of the fixed theorem -/

/-- **The admissible data of the fixed Galerkin existence theorem** (design §1.2, row `DataAdm`):
the localised datum class `LocData.DataAdm` of the route, together with the vanishing of the zero
mode `L₁₂(·)(0)` and the interior regularity class `RegQ α 5` (which supplies the boundary traces at
order `5` and the honest `ℋ⁵`-membership needed by N5's a-priori estimate). -/
def DataAdm (α : ℝ) (g₀ : Fn) : Prop :=
  Work.FTS.LocData.DataAdm α g₀ ∧ Construction.L12 g₀ 0 = 0 ∧ RegQ α 5 g₀

theorem DataAdm.locData {α : ℝ} {g₀ : Fn} (h : DataAdm α g₀) :
    Work.FTS.LocData.DataAdm α g₀ := h.1

theorem DataAdm.l12 {α : ℝ} {g₀ : Fn} (h : DataAdm α g₀) : Construction.L12 g₀ 0 = 0 := h.2.1


/-- **The corrected density of the Galerkin span**: density in the class `V₀ = {f ∈ ℋ⁴ : L₁₂(f)(0)
= 0}` of the interior-regular class (design §1.2, row `hφ_dense`).  Density relative to
`Coercivity.HkAdm`, which contains the analyticity hypothesis `SmoothNbhd`, is both hard and useless:
the flow does not preserve the zero modes of `HkAdm`, and the fundamental lemma is needed only on
`V₀`. -/
def DenseSpan (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) : Prop :=
  ∀ f : Fn, RegQ α 4 f → Construction.L12 f 0 = 0 → ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (c : Fin n → ℝ), Spaces.HkNorm α 4 (fun z θ => f z θ - galFun φ c z θ) < ε

/-! ## The compactness inputs of the corrected bundle

The delivered bundle asked for a *uniform local Lipschitz bound* on the Gelarkin profiles
(`hProfileLip`).  That is not what the estimates give: the `ℋ⁴`-ball contains profiles `θ^s` which
are only `C^β` for `β < γ - 1 = α/10` (design §1.2).  The compactness extraction of
`Extraction.lean` uses a Lipschitz modulus only through the `ε`/`3` argument, and a *modulus of
continuity* suffices.  The corrected input is therefore uniform local **equicontinuity**, split into
its two sources, which are the two estimates the paper actually provides:

* in the space variables: the Hölder embedding `|g|_{C^β} ≤ C_β|g|_{ℋ²}` for `β < γ-1` (tex 1057,
  Corollary `Linfty`), i.e. a uniform `ℋ²`-bound gives a modulus in `(z,θ)` (`EquicontSpace`);
* in the fake time: the estimate `|∂_τg|_{ℋ³} ≤ Cα² exp(-cτ)` (tex 1580) together with the pointwise
  bound of `Linf_H2` (`EquicontTau`);

see `Submission/Work/FTS/GalerkinFix/Equicont.lean` for the chapter that combines them. -/

/-- **Uniform local boundedness** of a sequence of profiles on the fake-time slab (N5 through the
paper's `Linf_H2`: a uniform `ℋ⁴`-bound gives pointwise bounds on compact subsets). -/
def ProfileBdd (G : ℕ → (ℝ × ℝ × ℝ) → ℝ) : Prop :=
  ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Slab →
    ∃ C : ℝ, ∀ n : ℕ, ∀ p ∈ K, |G n p| ≤ C

/-- **Uniform local equicontinuity** of a sequence of profiles on the fake-time slab — the corrected
compactness input replacing `hProfileLip`, obtained from `EquicontSpace` and `EquicontTau` by
`Work.FTS.GalerkinFix.profileEquicont_of_parts` and `…_of_box`. -/
def ProfileEquicont (G : ℕ → (ℝ × ℝ × ℝ) → ℝ) : Prop :=
  ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Slab → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ Slab, dist p q ≤ δ → |G n p - G n q| ≤ ε

/-- The rectangle `[0,Z] × [0,π/2] × [0,T]` of the self-similar slab. -/
def box (Z T : ℝ) : Set (ℝ × ℝ × ℝ) := Set.Icc 0 Z ×ˢ (Set.Icc 0 (π / 2) ×ˢ Set.Icc 0 T)

theorem mem_box {Z T : ℝ} {p : ℝ × ℝ × ℝ} :
    p ∈ box Z T ↔ p.1 ∈ Set.Icc 0 Z ∧ p.2.1 ∈ Set.Icc 0 (π / 2) ∧ p.2.2 ∈ Set.Icc 0 T :=
  Iff.rfl


/-- **Spatial equicontinuity of a sequence of profiles**, with a modulus on every rectangle of the
slab (uniform in the truncation `n` and in the fake time `τ`).  This is the `(z,θ)`-half of the
corrected compactness input; it is supplied by a uniform Hölder modulus of the profiles (the scalar
estimate `Linf_H2`, tex 1057), which in *this* vocabulary must come with the continuity of the
profiles up to the angular boundary: `SmoothQuad` + `VanishTheta` alone do not force the one-sided
limits at `θ = 0, π/2` (see `Submission/Work/FTS/GalerkinFix/README.md` §2.1 and
`Work.FTS.GalerkinFix.LinfQ.holder_modulus_of_HkNorm_two_continuous`).  The reduction from such a
modulus to this statement is `Work.FTS.GalerkinFix.equicontSpace_of_holderBound`. -/
def EquicontSpace (G : ℕ → (ℝ × ℝ × ℝ) → ℝ) : Prop :=
  ∀ Z T : ℝ, 0 ≤ Z → 0 ≤ T → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ,
    ∀ τ ∈ Set.Icc 0 T, ∀ z ∈ Set.Icc 0 Z, ∀ θ ∈ Set.Icc 0 (π / 2),
      ∀ z' ∈ Set.Icc 0 Z, ∀ θ' ∈ Set.Icc 0 (π / 2),
        |z - z'| ≤ δ → |θ - θ'| ≤ δ → |G n (z, θ, τ) - G n (z', θ', τ)| ≤ ε

/-- **Equicontinuity of a sequence of profiles in the fake time**, with a modulus on every rectangle
of the slab (uniform in the truncation `n`).  This is the `τ`-half of the corrected compactness
input; it is supplied by the paper's estimate `|∂_τg|_{ℋ³} ≤ Cα² exp(-cτ)` through
`Work.FTS.GalerkinFix.equicontTau_of_galFam_fieldBound`. -/
def EquicontTau (G : ℕ → (ℝ × ℝ × ℝ) → ℝ) : Prop :=
  ∀ Z T : ℝ, 0 ≤ Z → 0 ≤ T → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ,
    ∀ z ∈ Set.Icc 0 Z, ∀ θ ∈ Set.Icc 0 (π / 2),
      ∀ t ∈ Set.Icc 0 T, ∀ s ∈ Set.Icc 0 T,
        |t - s| ≤ δ → |G n (z, θ, t) - G n (z, θ, s)| ≤ ε


/-- The profile family of a Galerkin coefficient family, as a function on the fake-time slab. -/
def profileFam (φ : ℕ → Fn) (c : ∀ n : ℕ, ℝ → Fin n → ℝ) : ℕ → (ℝ × ℝ × ℝ) → ℝ :=
  fun n p => prof φ c n p

@[simp] theorem profileFam_apply (φ : ℕ → Fn) (c : ∀ n : ℕ, ℝ → Fin n → ℝ) (n : ℕ)
    (p : ℝ × ℝ × ℝ) : profileFam φ c n p = prof φ c n p := rfl

/-! ## The corrected a-priori bundle -/

/-- **The corrected a-priori input bundle of the Galerkin existence theorem** (design §1.2–1.3).

Every field is a statement *about* the objects of the argument; there is no existence assertion
among them — existence of a solution of the dynamic modulated equation is what
`Work.FTS.Galerkin.exists_dynGSol_of_ode` proves from this bundle.

* `IP`, `α₂`, `cc`, `clo`, `Cup`, `Ccs`, `hIP` (N2): the `ℋ⁴` inner product with the *uniform*
  coercivity/comparability/Cauchy–Schwarz constants of `Work.FTS.Nonlin.UnifIP`.  Its linearity is
  restricted to the regular class `RegQ α 4`.
* `φ`, `hφ` (N6 step 2): the Galerkin basis, as `GalBasis α IP φ` — `IP`-orthonormal and with every
  Galerkin combination in `GalClass α`.  The old fields `hφ_orth`/`hφ_adm`/`hφ_vanish` are replaced
  by this single class (they are its consequences: `Work.FTS.GalerkinFix.galBasis_orth`,
  `…_vanish`).
* `hφ_dense` (N6 step 2): density of the span in `V₀` (`DenseSpan`).
* `Φs`, `Cs`, `hΦs` (N3): the stream function of `F_*` and its `𝒲^{l,∞}` package (`StarPkg`).
* `EllSol`, `Ce`, `hEllSol` (N1): the *canonical* stream-function operator, defined on `GalClass`
  with the elliptic package `EllPkgG` (source `g`, stream function `EllSol g`).
* `hPsi` (N1): the stream function of the profile `F_* + G(τ)` is `PsiCan Φs EllSol G` and solves
  the elliptic law `Law`, for every family whose slices are in `GalClass`.
* `R`, `hR` (N5): the radius of the a-priori ball.
* `L : ℕ → ℝ`, `K : ℕ → ℝ`, `hField_lip`, `hField_bound`, `hField_cont` (N4): the projected vector
  field is Lipschitz/bounded/`τ`-continuous on the ball of radius `2R` of `Fin n → ℝ`, **with
  constants depending on the truncation** `n` (they cannot be uniform: `𝓛_Γ^T` is unbounded).
* `hInit`, `hCoeffBound` (N5): the projected datum and every Galerkin solution stay in the ball.
* `hProfileBdd` (N5): uniform local bounds on the profiles.
* `hProfileEquicont` (N4+N5): uniform local **equicontinuity** of the profiles — the compactness
  input (replaces `hProfileLip`).
* `hRegLimit` (N5/N7): the regularity package of the limit.
* `hDataLimit` (N6 step 2): the `τ = 0` slice of the limit is the datum.
* `hPsiLim` (N1): the stream functions have a locally uniform limit.
* `hGalWeak` (N1+N4): the tested equations and the elliptic law pass to the limit.
* `hDetermines` (N6 step 6): the fundamental lemma for the dense Galerkin span.
* `hLimBound` (N5): the a-priori `ℋ⁴`-bound `C₀α²` for the **limit** of the Galerkin family
  (replaces `hApriori`, which asked the same for *every* solution of the dynamic equation). -/
structure DynInputs (Law : Fn → Fn → Prop) (α : ℝ) (g₀ : Fn) (C₀ : ℝ) where
  /-- the `ℋ⁴` inner product (N2). -/
  IP : ℝ → Fn → Fn → ℝ
  /-- the range of validity of the uniform inner-product bounds (N2). -/
  α₂ : ℝ
  /-- the coercivity constant of `𝓛_Γ^T` (N2). -/
  cc : ℝ
  /-- the lower comparability constant of `IP` (N2). -/
  clo : ℝ
  /-- the upper comparability constant of `IP` (N2). -/
  Cup : ℝ
  /-- the Cauchy–Schwarz constant of `IP` (N2). -/
  Ccs : ℝ
  /-- **the uniform inner-product structure** (N2). -/
  hIP : UnifIP IP α₂ cc clo Cup Ccs
  /-- the Galerkin test sequence (N6 step 2). -/
  φ : ℕ → Fn
  /-- **the Galerkin basis class**: `IP`-orthonormal, with every Galerkin combination in
  `GalClass` (N6 step 2, corrected). -/
  hφ : GalBasis α IP φ
  /-- the span of the test sequence is dense in `V₀` (N6 step 2, corrected). -/
  hφ_dense : DenseSpan α IP φ
  /-- the stream function of `F_*` (N3). -/
  Φs : Fn
  /-- the canonical stream-function operator for the perturbation (N1). -/
  EllSol : Fn → Fn
  /-- the `𝒲^{l,∞}` constant of the profile (N3). -/
  Cs : ℝ
  /-- the elliptic constant of the perturbation's stream function (N1). -/
  Ce : ℝ
  /-- the stream function of `F_*` and its `𝒲^{l,∞}` package (N3). -/
  hΦs : StarPkg α Cs Φs
  /-- the elliptic package of the perturbation's stream function, on the Galerkin class (N1). -/
  hEllSol : ∀ g : Fn, GalClass α g → EllPkgG α Ce g (EllSol g)
  /-- the stream function of `F_* + G(τ)` is `PsiCan Φs EllSol G`, and it satisfies the elliptic law
  at every `τ ≥ 0` for families whose slices lie in `GalClass` (N1). -/
  hPsi : ∀ G : Fam, (∀ τ : ℝ, 0 ≤ τ → GalClass α (slice G τ)) → ∀ τ : ℝ, 0 ≤ τ →
    Law (Construction.Ftau α G τ) (slice (PsiCan Φs EllSol G) τ)
  /-- the radius of the a-priori ball for the coefficients. -/
  R : ℝ
  hR : 0 < R
  /-- a bound for the projected vector field on the ball of radius `2R`, depending on the
  truncation (N4). -/
  L : ℕ → ℝ
  hL : ∀ n : ℕ, 0 < L n
  /-- a Lipschitz constant for the projected vector field on the ball of radius `2R`, depending on
  the truncation (N4). -/
  K : ℕ → ℝ
  hK : ∀ n : ℕ, 0 ≤ K n
  /-- the projected vector field is Lipschitz in the coefficients, with truncation-dependent
  constant (N4). -/
  hField_lip : ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
    LipschitzOnWith ⟨K n, hK n⟩ (galField α (IP α) φ n (PsiCan Φs EllSol) τ)
      (Metric.closedBall 0 (2 * R))
  /-- the projected vector field is bounded on the ball of radius `2R`, with truncation-dependent
  constant (N4). -/
  hField_bound : ∀ (n : ℕ) (τ : ℝ) (c : Fin n → ℝ), 0 ≤ τ →
    c ∈ Metric.closedBall 0 (2 * R) → ‖galField α (IP α) φ n (PsiCan Φs EllSol) τ c‖ ≤ L n
  /-- the projected vector field is continuous in fake time (N1 + N4). -/
  hField_cont : ∀ (n : ℕ) (c : Fin n → ℝ), c ∈ Metric.closedBall 0 (2 * R) →
    ContinuousOn (fun τ => galField α (IP α) φ n (PsiCan Φs EllSol) τ c) (Set.Ici 0)
  /-- the projected datum lies in the a-priori ball, in the energy (`ℓ²`) form. -/
  hInit : ∀ n : ℕ, ∑ k : Fin n, (coeffOf (IP α) g₀ φ n k) ^ 2 ≤ R ^ 2
  /-- **the a-priori estimate**: the coefficients of every Galerkin solution stay in the ball
  (N5, using the exact energy identity of step 4). -/
  hCoeffBound : ∀ (n : ℕ) (T : ℝ), 0 ≤ T → ∀ c : ℝ → Fin n → ℝ,
    IsSolOn (galField α (IP α) φ n (PsiCan Φs EllSol)) (coeffOf (IP α) g₀ φ n) T c →
    ∀ τ ∈ Set.Icc 0 T, ∑ k : Fin n, (c τ k) ^ 2 ≤ R ^ 2
  /-- **uniform local bounds on the Galerkin profiles** (N5 through the paper's `Linf_H2`). -/
  hProfileBdd : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c →
    ProfileBdd (profileFam φ c)
  /-- **uniform spatial equicontinuity of the Galerkin profiles** (N4 + N5): the `(z,θ)`-half of the
  corrected compactness input, supplied by the paper's Hölder embedding
  `|g|_{C^β} ≤ C_β|g|_{ℋ²}` (`β < γ-1`, tex 1057) from a uniform `ℋ²`-bound on the profiles. -/
  hProfileSpace : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c →
    EquicontSpace (profileFam φ c)
  /-- **uniform equicontinuity of the Galerkin profiles in the fake time** (N4 + N5): the
  `τ`-half of the corrected compactness input, supplied by the paper's estimate
  `|∂_τg|_{ℋ³} ≤ Cα² exp(-cτ)` (tex 1580) through
  `Work.FTS.GalerkinFix.equicontTau_of_galFam_fieldBound`.  These two fields replace the delivered
  `hProfileLip`. -/
  hProfileTau : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c →
    EquicontTau (profileFam φ c)
  /-- **the regularity package of the limit** (N5/N7). -/
  hRegLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → RegPkg α g
  /-- **the datum is the limit of the projected data** (N6 step 2). -/
  hDataLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → ∀ z θ, g z θ 0 = g₀ z θ
  /-- **the stream functions have a locally uniform limit** (N1). -/
  hPsiLim : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ∃ Φ : Fam, ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ
  /-- **the tested equations pass to the limit** (N1 + N4). -/
  hGalWeak : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g Φ : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ →
    IsDynWeakOn α (IP α) φ g Φ ∧ (∀ τ : ℝ, 0 ≤ τ → Law (Construction.Ftau α g τ) (slice Φ τ))
  /-- **the fundamental lemma of the calculus of variations** for the dense Galerkin span
  (N6 step 6). -/
  hDetermines : WeakDetermines α (IP α) φ
  /-- **the a-priori estimate in limit form** (N5): the limit of the Galerkin family obeys the
  uniform `ℋ⁴`-bound `C₀α²`.  This replaces the delivered field `hApriori`. -/
  hLimBound : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ∀ τ : ℝ, 0 ≤ τ → Spaces.HkNorm α 4 (slice g τ) ≤ C₀ * α ^ 2

/-- The stream-function assignment of the bundle: the canonical operator `PsiCan Φs EllSol` of
N1, i.e. `Ψ(F_* + g) = Φ_* + EllSol(g)`. -/
def DynInputs.Psi {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ : ℝ}
    (hin : DynInputs Law α g₀ C₀) : Fam → Fam :=
  PsiCan hin.Φs hin.EllSol


@[simp] theorem DynInputs.Psi_apply {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ : ℝ}
    (hin : DynInputs Law α g₀ C₀) (G : Fam) (z θ τ : ℝ) :
    hin.Psi G z θ τ = hin.Φs z θ + hin.EllSol (slice G τ) z θ := rfl

end Work.FTS.Galerkin
end
end
-- ===== merged: Submission.Work.FTS.H2.L12ZeroQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

/-! ## Ingredients of `L12ZeroQ`

The estimate `|L₁₂(f)(0)| ≤ C|f|_{ℋ⁴}` of Elgindi's Proposition `muestimate` in the interior
class `Work.FTS.Nonlin.RegQ α 4 f = SmoothQuad f ∧ HkMem α 4 f ∧ BdryTraces α 4 f` differs
from `Work.FTS.H2.L12ZeroLe` (the `SmoothNbhd` = analyticity version) only in the three
regularity inputs `SliceFacts`, `PhiWeight`, `L12densSlice`:

* the squared angular slice `θ ↦ (f z θ)²` is integrable on `Iθ` for `z > 0`
  (`l12q_slice_sq_integrableOn`) — in the interior class this comes from `HkMem` (the `i = 0`
  term of `HkIntegrand` dominates `f² w²` and `w ≥ 1`) and the `SmoothQuad`-continuity of the
  slice on the *open* interval (the endpoints are null);
* the angular density bound `|L₁₂dens(f)(z)| ≤ √3 √(∫_θ f(z,θ)²)/z` on a slice follows
  (`l12q_l12dens_slice`);
* the Hardy-weighted angular energy `r ↦ (∫_θ f(r,θ)²)·((1+r)/r)²` is a.e. strongly measurable
  on `(0,∞)` (`l12q_aesm`, `l12q_phi_aesm`), by Fubini from the joint continuity on the open
  quadrant (`Work.Spaces.aesm_of_continuousOn_Qd`), replacing the `SmoothNbhd`-based
  `Work.FTS.H2.PhiWeightAesm`;
* the radial comparison `∫_{r>0} (∫_θ f(r,θ)²)·((1+r)/r)² ≤ HkSq α 4 f` needs no smoothness at
  all and is proved from `HkMem` directly (`l12q_phiWeight_le`, using the pointwise Hardy-weight
  comparison of `Work.FTS.H2.L12Q.phiWeight_slice_le`).

The assembly below is that of `L12ZeroLe` verbatim: Cauchy–Schwarz in `r` against
`(1/(1+r))²` (`∫_{r>0} (1+r)^{-2} ≤ 2`), then `√3·√2 ≤ 3`. -/

/-- **Joint continuity of `(z,θ) ↦ (f z θ)²` on the open quadrant**, from `SmoothQuad f` (which
gives `C^∞` on `Ioi (-1) ×ˢ Ioo 0 (π/2)`; restrict to the smaller `Ioi 0 ×ˢ Ioo 0 (π/2)`). -/
private theorem l12q_quad_continuous (f : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hsub : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2))
      ⊆ (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := by
    rintro p hp
    rw [Set.mem_prod] at hp ⊢
    exact ⟨by simp only [Set.mem_Ioi] at hp ⊢; linarith [hp.1], hp.2⟩
  have h1 : ContinuousOn (Function.uncurry f) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
    hsm.continuousOn.mono hsub
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := h1.pow 2
  simpa only [Function.uncurry] using h2

/-- **A.e. strong measurability of the angular energy in the interior class** (`SmoothQuad f`):
`r ↦ ∫_θ f(r,θ)²` on `(0,∞)`.  Replaces the `SmoothNbhd`-based route of
`Work.FTS.H2.SliceFacts`: by Fubini from the joint continuity of `(r,θ) ↦ (f r θ)²` on the open
quadrant (`Work.Spaces.aesm_of_continuousOn_Qd`), then restrict `Iz` to `Ioi 0`. -/
theorem l12q_phi_aesm (f : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad f) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hquad : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (l12q_quad_continuous f hsm)
  have hslicemeas : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right' hquad
  have hmono : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) ≤
      MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self
  exact hslicemeas.mono_measure hmono

/-- **Integrability of the squared angular slice in the interior class.**  For `SmoothQuad f`
and `HkMem α 4 f`, every radial slice `θ ↦ (f z θ)²` with `z > 0` is integrable on `Iθ`.

Supplies the slice-integrability hypothesis of `Work.Coercivity.L12dens_sq_slice` in the class
`Work.FTS.Nonlin.RegQ`, where `Work.FTS.H2.slice_sq_integrableOn` (hypothesis `SmoothNbhd`)
cannot be used.  For a.e. `θ ∈ Iθ` (all `θ ∈ Ioo 0 (π/2)`) one has `0 < sin(2θ) ≤ 1` and
`w z ≥ 1`, so `(f z θ)² ≤ (f z θ·(w z/sin(2θ)^{η/2}))² ≤ HkIntegrand α 4 f z θ`
(`Work.Spaces.sq_le_HkIntegrand_z`, `i = 0`); the majorant is integrable on `Iθ` by `hmem.1`,
and the dominated function is a.e. strongly measurable there by
`Work.Spaces.aesm_slice_of_continuousOn_Qd` (continuity on the open quadrant from `hsm`). -/
theorem l12q_slice_sq_integrableOn (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (l12q_quad_continuous f hsm) hz
  refine MeasureTheory.Integrable.mono' (hmem.1 z (le_of_lt hz)) haesm ?_
  -- the pointwise bound only fails on the two null endpoints
  have hcongr : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := (π / 2))).symm
  rw [hcongr]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 (by have := Work.Spaces.eta_pos; linarith)
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs0 _
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hz]
  have hkey : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div hspos]
    exact le_trans hsle hw1
  have hW2 : 1 ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    have h := mul_le_mul hkey hkey (zero_le_one) (le_trans zero_le_one hkey)
    simpa only [one_mul, pow_two] using h
  have hpt : (f z θ) ^ 2 ≤ (f z θ * (Work.Spaces.w z
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (f z θ) ^ 2 = (f z θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (f z θ) ^ 2
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)
      _ = (f z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := (mul_pow _ _ 2).symm
  calc ‖(f z θ) ^ 2‖ = (f z θ) ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    _ ≤ (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hpt
    _ = (Work.Spaces.DzIter 0 f z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ 0 (by norm_num)

/-- **A.e. strong measurability of the Hardy-weighted angular energy in the interior class**
(`SmoothQuad f`): `r ↦ (∫_θ f(r,θ)²)·((1+r)/r)²` on `(0,∞)`.  Replaces the `SmoothNbhd`-based
`Work.FTS.H2.PhiWeightAesm`: `l12q_phi_aesm` gives the angular energy and the Hardy weight
`r ↦ ((1+r)/r)²` is continuous on `(0,∞)`. -/
theorem l12q_aesm (f : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad f) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hw : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : ContinuousOn (fun r : ℝ => ((1 + r) / r) ^ 2) (Set.Ioi (0 : ℝ)) :=
      ((continuousOn_const.add continuousOn_id).div continuousOn_id
        (fun r hr => ne_of_gt (Set.mem_Ioi.mp hr))).pow 2
    exact h1.aestronglyMeasurable measurableSet_Ioi
  exact (l12q_phi_aesm f hsm).mul hw

/-- **The angular Cauchy–Schwarz bound for the `L₁₂` density on one radial slice**, with the
slice-square integrability as an explicit hypothesis (in the interior class it is
`l12q_slice_sq_integrableOn`).  This is `Work.FTS.H2.L12densSlice` with its `SmoothNbhd`
hypothesis replaced by `IntegrableOn (fun θ => (f z θ)²) Iθ`. -/
theorem l12q_l12dens_slice (f : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ) :
    |Work.Elliptic.L12dens f z|
      ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z := by
  have hsq := Work.Coercivity.L12dens_sq_slice f Work.Coercivity.integral_Itheta_K hz hsl
  have hX : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      fun θ _ => by positivity
  rw [L12dens_eq_FM_K f z]
  exact abs_le_sqrt_three_mul_sqrt_div hz hX hsq

/-- **The radial Hardy-weight comparison.**  For `HkMem α 4 f` (no smoothness hypothesis),
`∫_{r>0} (∫_θ f(r,θ)²)·((1+r)/r)² ≤ HkSq α 4 f`: the slicewise comparison is
`Work.FTS.H2.L12Q.phiWeight_slice_le`, the majorant `r ↦ ∫_θ HkIntegrand α 4 f r θ` is
integrable on `(0,∞)` by `HkMem`, and `∫_{Iz}` is `∫_{Ioi 0}` (`MeasureTheory.Ioi_ae_eq_Ici`). -/
theorem l12q_phiWeight_le (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 f) :
    (∫ r in Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      ≤ Work.Spaces.HkSq α 4 f := by
  have hslice := Work.FTS.H2.L12Q.phiWeight_slice_le α f hmem
  have hK : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      (Set.Ioi (0 : ℝ)) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hle : (∫ r in Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      ≤ ∫ r in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 f r θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hK ?_
    · exact Filter.Eventually.of_forall fun r =>
        mul_nonneg (integral_nonneg fun θ => sq_nonneg _) (sq_nonneg _)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact hslice r hr
  refine le_trans hle ?_
  rw [MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  rfl

/-- **Integrability of the Hardy-weighted angular energy.**  From `HkMem α 4 f` and the a.e.
strong measurability `l12q_aesm` of the weighted energy, dominated by the integrable majorant
`r ↦ ∫_θ HkIntegrand α 4 f r θ`. -/
theorem l12q_phiWeight_integrable (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.IntegrableOn
      (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  have hslice := Work.FTS.H2.L12Q.phiWeight_slice_le α f hmem
  have hK : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      (Set.Ioi (0 : ℝ)) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  refine hK.mono' (l12q_aesm f hsm) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  rw [Real.norm_of_nonneg (mul_nonneg (integral_nonneg fun θ => sq_nonneg _) (sq_nonneg _))]
  exact hslice r hr

/-- Elgindi's `muestimate` (tex 1516, first line of the proof) in the *interior* class
`Work.FTS.Nonlin.RegQ` of the frozen `Submission/Work/FTS/Vocab.lean`: for
`RegQ α 4 f`, `|L₁₂(f)(0)| ≤ C |f|_{ℋ⁴}`, `C` universal.  This is the design document's
`L12ZeroQ` (§3.3 L-N4.5), the form in which N4 bounds every `L₁₂(piece)(0)`.

`RegQ α 4 f = SmoothQuad f ∧ HkMem α 4 f ∧ BdryTraces α 4 f` replaces `Spaces.SmoothNbhd`
(= analyticity on a neighbourhood of the closed quadrant) in `Work.FTS.H2.L12ZeroLe`, which is
the same statement with `SmoothNbhd`.  The proof is the paper's: `|L₁₂(f)(0)| ≤ C|((z+1)/z)f|_{L²}`
(split the `θ`-integral by Cauchy–Schwarz against `K ∈ L²(Iθ)` and the `r`-integral against
`(1+r)^{-2}`), then `∫∫ f² w ≤ ∫∫ f² w²/sin(2θ)^η ≤ HkSq α 4 f`; slice measurability and
integrability come from `SmoothQuad` and `HkMem` instead of `SmoothNbhd`. -/
theorem L12ZeroQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
    Work.FTS.Nonlin.RegQ α 4 f → |Work.Elliptic.L12 f 0| ≤ C * Work.FTS.Nonlin.Xn α f := by
  refine ⟨3, by norm_num, ?_⟩
  intro α f hα hα1 hreg
  obtain ⟨hsm, hmem, _hbdry⟩ := hreg
  -- the slicewise regularity inputs
  have hslice : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ :=
    fun z hz => l12q_slice_sq_integrableOn α f hsm hmem hz
  have hdens : ∀ r : ℝ, 0 < r → |Work.Elliptic.L12dens f r|
      ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) / r :=
    fun r hr => l12q_l12dens_slice f hr (hslice r hr)
  -- the radial inputs
  have hPhiw_le := l12q_phiWeight_le α f hmem
  have hPhiw_int := l12q_phiWeight_integrable α f hsm hmem
  have hPhi_aesm := l12q_phi_aesm f hsm
  have hPhi0 : ∀ r : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2 := fun r =>
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun θ => sq_nonneg _)
  -- abbreviations
  set A : ℝ → ℝ := fun r => Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      * ((1 + r) / r) with hAdef
  set B : ℝ → ℝ := fun r => 1 / (1 + r) with hBdef
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) with hμdef
  -- ## nonnegativity of `A` and `B` a.e.
  have hAe0 : ∀ᵐ r ∂μ, 0 ≤ A r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    rw [hAdef]
    have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg _))
      (div_nonneg (by linarith) (le_of_lt hr'))
  have hBe0 : ∀ᵐ r ∂μ, 0 ≤ B r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    rw [hBdef]
    have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
    exact div_nonneg zero_le_one (by linarith)
  -- ## `A` is a.e. strongly measurable
  have hAmeas : MeasureTheory.AEStronglyMeasurable A μ := by
    rw [hμdef, hAdef]
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun r : ℝ => Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hPhi_aesm
    have h2 : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => (1 + r) / r)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (ContinuousOn.div (continuousOn_const.add continuousOn_id) continuousOn_id
        (fun r hr => ne_of_gt hr)).aestronglyMeasurable measurableSet_Ioi
    exact (aestronglyMeasurable_const.mul h1).mul h2
  -- ## `A²` is integrable and is the Hardy-weighted angular energy
  have hpt : ∀ r : ℝ,
      A r ^ 2 = 3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) := by
    intro r
    rw [hAdef, mul_pow, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sq_sqrt (hPhi0 r)]
    ring
  have h33 : MeasureTheory.Integrable
      (fun r : ℝ => 3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)) μ := by
    rw [hμdef]
    exact hPhiw_int.const_mul 3
  have hAint : MeasureTheory.Integrable (fun r => A r ^ 2) μ := by
    refine h33.congr ?_
    filter_upwards with r
    exact (hpt r).symm
  have hmemA : MeasureTheory.MemLp A 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAmeas).mpr hAint
  -- ## `B` is a.e. strongly measurable and `B²` is integrable
  obtain ⟨hB_int, hB_le⟩ := InvOneAddSq
  have hBmeas : MeasureTheory.AEStronglyMeasurable B μ := by
    rw [hμdef, hBdef]
    have h2 : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => 1 / (1 + r))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
        (fun r hr => by
          have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
          exact ne_of_gt (by show (0 : ℝ) < 1 + r; linarith))).aestronglyMeasurable
        measurableSet_Ioi
    simpa only using h2
  have hBint : MeasureTheory.Integrable (fun r => B r ^ 2) μ := by
    rw [hμdef, hBdef]
    exact hB_int
  have hmemB : MeasureTheory.MemLp B 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hBmeas).mpr hBint
  -- ## the pointwise bound on the density
  have hbd : ∀ᵐ r ∂μ, |Work.Elliptic.L12dens f r| ≤ A r * B r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    have h5 := hdens r (Set.mem_Ioi.mp hr)
    have hr1 : 1 + r ≠ 0 := by have h := Set.mem_Ioi.mp hr; linarith
    have h5' : |Work.Elliptic.L12dens f r|
        ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * r⁻¹ := by
      simpa only [div_eq_mul_inv] using h5
    have hkey : ((1 + r) / r) * (1 / (1 + r)) = r⁻¹ := by
      field_simp
    rw [hAdef, hBdef]
    dsimp only
    calc |Work.Elliptic.L12dens f r|
        ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * r⁻¹ := h5'
      _ = Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
            * (((1 + r) / r) * (1 / (1 + r))) := by rw [hkey]
      _ = Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
            * ((1 + r) / r) * (1 / (1 + r)) := by ring
  -- ## Cauchy–Schwarz in the radial variable
  have hcs := CS1D (μ := μ) (g := fun r => Work.Elliptic.L12dens f r)
    hmemA hmemB hAe0 hBe0 hbd
  -- ## the two `L²` norms
  have hA2le : ∫ r, A r ^ 2 ∂μ ≤ 3 * Work.Spaces.HkSq α 4 f := by
    rw [hμdef]
    have hpt' : ∀ r ∈ Set.Ioi (0 : ℝ),
        A r ^ 2 = 3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) :=
      fun r _ => hpt r
    calc ∫ r in Set.Ioi (0 : ℝ), A r ^ 2
        = ∫ r in Set.Ioi (0 : ℝ),
            3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt'
      _ = 3 * ∫ r in Set.Ioi (0 : ℝ),
            (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 :=
          MeasureTheory.integral_const_mul 3 _
      _ ≤ 3 * Work.Spaces.HkSq α 4 f := mul_le_mul_of_nonneg_left hPhiw_le (by norm_num)
  have hB2le : ∫ r, B r ^ 2 ∂μ ≤ 2 := by
    rw [hμdef]
    have hfun : (fun r : ℝ => B r ^ 2) = fun r : ℝ => (1 / (1 + r)) ^ 2 := by
      funext r
      rw [hBdef]
    rw [hfun]
    exact hB_le
  -- ## assembly
  have hfinal : |Work.Elliptic.L12 f 0| ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 f) * Real.sqrt 2 := by
    have h1 : (∫ r, Work.Elliptic.L12dens f r ∂μ) = Work.Elliptic.L12 f 0 := rfl
    rw [← h1]
    refine hcs.trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hA2le) (Real.sqrt_le_sqrt hB2le)
      (Real.sqrt_nonneg (∫ r, B r ^ 2 ∂μ)) (Real.sqrt_nonneg _)
  have hsqrt : Real.sqrt (3 * Work.Spaces.HkSq α 4 f) * Real.sqrt 2
      = Real.sqrt 6 * Work.Spaces.HkNorm α 4 f := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (Work.Spaces.HkSq α 4 f),
      Work.Spaces.HkNorm]
    rw [show Real.sqrt 3 * Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt 2
        = (Real.sqrt 3 * Real.sqrt 2) * Real.sqrt (Work.Spaces.HkSq α 4 f) from by ring]
    rw [show Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 from by
      rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (2 : ℝ)]
      norm_num]
  have h6le : Real.sqrt 6 ≤ 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]
  calc |Work.Elliptic.L12 f 0|
      ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 f) * Real.sqrt 2 := hfinal
    _ = Real.sqrt 6 * Work.Spaces.HkNorm α 4 f := hsqrt
    _ ≤ 3 * Work.Spaces.HkNorm α 4 f :=
        mul_le_mul_of_nonneg_right h6le (Work.Spaces.HkNorm_nonneg α 4 f)
    _ = 3 * Work.FTS.Nonlin.Xn α f := rfl

end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.LinfQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-! ## The open quadrant `(0,∞) × (0,π/2)`

Everything in this file happens on the open quadrant: `supAbsO` is the supremum over it, the
regularity class `RegQ` only constrains the function there, and the weights are continuous
there.  The complement of the open quadrant inside `Iz ×ˢ Iθ` is null for the product of the
restricted Lebesgue measures, which is what makes `aesm_of_continuousOn_Qd` applicable. -/

lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (h : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2, Real.pi_pos])

lemma one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (w z) ^ 2 := by
  have h1 : (1 : ℝ) ≤ w z := by
    rw [w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith
  calc (1 : ℝ) = 1 ^ 2 := by ring
    _ ≤ (w z) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2

/-- `Wt α z θ² = w(z)² sin(2θ)^{-γ}` on the open quadrant (no hypothesis on `α`: the base
`sin(2θ)` is positive there). -/
lemma Wt_sq_Ioo (α z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (w z * (Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ 2
      = (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hstep : ((Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  rw [mul_pow, hstep]


/-! ## Almost everywhere strong measurability and integrability of a mixed slot -/

/-- The weighted square of a mixed `D`-derivative of a `SmoothQuad` function is almost
everywhere strongly measurable for the product of the restricted Lebesgue measures: it is
*continuous* on the open quadrant, whose complement in `Iz ×ˢ Iθ` is null. -/
theorem aesm_mixed_Wt_sq_prod_quad (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : SmoothQuad f) (j i : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
  aesm_of_continuousOn_Qd _
    ((((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf j i).continuousOn.mono
        Qd_subset_quadU).mul (continuousOn_Wt_Qd α)).pow 2)

/-- The `θ`-slice measurability of a mixed slot at a fixed `z > 0`. -/
theorem aesm_slice_mixed_Wt_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : SmoothQuad f) (j i : ℕ)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => (mixed j i f z θ * Wt α z θ) ^ 2)
      (volume.restrict Iθ) :=
  aesm_slice_of_continuousOn_Qd _
    ((((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf j i).continuousOn.mono
        Qd_subset_quadU).mul (continuousOn_Wt_Qd α)).pow 2) hz

/-- The a.e. domination of a mixed slot by the `ℋ⁴`-integrand, in the norm form required by
`Integrable.mono'`. -/
lemma slot_norm_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (z θ : ℝ) :
    ‖(mixed j i f z θ * Wt α z θ) ^ 2‖ ≤ HkIntegrand α 4 f z θ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij

/-- The `θ`-slice of the weighted mixed slot is integrable on `Iθ`, for every `z ∈ Iz`, by
domination by the corresponding summand of `HkIntegrand α 4 f`. -/
theorem integrableOn_slice_mixed_Wt_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : SmoothQuad f)
    (hmem : HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) {z : ℝ} (hz : z ∈ Iz) :
    IntegrableOn (fun θ => (mixed j i f z θ * Wt α z θ) ^ 2) Iθ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have hzero : (fun θ => (mixed j i f 0 θ * Wt α 0 θ) ^ 2) = fun _ => (0 : ℝ) := by
      funext θ
      simp [Wt, w]
    rw [hzero]
    exact integrableOn_zero
  · refine MeasureTheory.Integrable.mono' (hmem.1 z hz)
      (aesm_slice_mixed_Wt_sq α f hf j i hzpos) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    exact slot_norm_le_HkIntegrand α f j i hi hij z θ

/-- **The mixed slot of the `ℋ⁴` norm, in the `θ`-first order.**  For a `SmoothQuad` function
`f` of class `ℋ⁴` and a mixed slot `1 ≤ i`, `i + j ≤ 4`:

* the `θ`-first iterated integral of `(D_z^jD_θ^i f · W)²` is bounded by the squared `ℋ⁴` norm;
* it is integrable in `θ`;
* for almost every `θ` the unweighted `z`-slice `(D_z^jD_θ^i f)² w²` is integrable on `Iz` (this
  is the integrability input of the radial Hardy inequality). -/
theorem slotM_quad (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : SmoothQuad f) (hmem : HkMem α 4 f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (∫ θ in Iθ, ∫ z in Iz, (mixed j i f z θ * Wt α z θ) ^ 2) ≤ HkSq α 4 f
    ∧ IntegrableOn (fun θ => ∫ z in Iz, (mixed j i f z θ * Wt α z θ) ^ 2) Iθ
    ∧ (∀ᵐ θ ∂(volume.restrict Iθ),
        IntegrableOn (fun z => (mixed j i f z θ) ^ 2 * (w z) ^ 2) Iz) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ (mixed j i f z θ * Wt α z θ) ^ 2 := fun z θ => sq_nonneg _
  have hAE := aesm_mixed_Wt_sq_prod_quad α f hf j i
  have hslice : ∀ᵐ z ∂(volume.restrict Iz),
      Integrable (fun θ => (mixed j i f z θ * Wt α z θ) ^ 2) (volume.restrict Iθ) := by
    filter_upwards [hAE.prodMk_left,
      ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz_meas hz
    refine MeasureTheory.Integrable.mono' (hmem.1 z hz) hz_meas ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    exact slot_norm_le_HkIntegrand α f j i hi hij z θ
  have houter : Integrable
      (fun z => ∫ θ, (mixed j i f z θ * Wt α z θ) ^ 2 ∂(volume.restrict Iθ))
      (volume.restrict Iz) := by
    refine MeasureTheory.Integrable.mono' hmem.2 hAE.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hmem.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij))
  obtain ⟨hint, hval⟩ := integrable_prod_of_iterated hnn hAE hslice houter
  have hswap := MeasureTheory.integral_integral_swap hint
  have hL2 : (∫ z in Iz, ∫ θ in Iθ, (mixed j i f z θ * Wt α z θ) ^ 2) ≤ HkSq α 4 f := by
    simpa only [L2Sq] using L2Sq_mixed_le_HkSq α 4 f hmem i j hi hij
  refine ⟨?_, ?_, ?_⟩
  · rw [← hswap]
    exact hL2
  · exact hint.integral_prod_right
  · have haeeq : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Iθ := MeasureTheory.Ioo_ae_eq_Icc
    have hIoo : volume.restrict Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
      Measure.restrict_congr_set haeeq.symm
    rw [hIoo] at hint ⊢
    filter_upwards [hint.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with θ hsliceθ hθmem
    have hθI : θ ∈ Iθ := ⟨le_of_lt hθmem.1, le_of_lt hθmem.2⟩
    have hsin : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθmem
    have hmul : (Real.sin (2 * θ)) ^ gam α * (Real.sin (2 * θ)) ^ (-(gam α)) = 1 := by
      rw [← Real.rpow_add hsin, show gam α + -(gam α) = 0 by ring, Real.rpow_zero]
    have hEq : (fun z => (mixed j i f z θ) ^ 2 * (w z) ^ 2)
        = fun z => (Real.sin (2 * θ)) ^ gam α
            * (mixed j i f z θ * Wt α z θ) ^ 2 := by
      funext z
      have h1 : (mixed j i f z θ * Wt α z θ) ^ 2
          = (mixed j i f z θ) ^ 2 * ((w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) := by
        rw [show Wt α z θ = w z * (Real.sin (2 * θ)) ^ (-(gam α / 2)) from rfl, mul_pow,
          Wt_sq_Ioo α z θ hθmem]
      rw [h1]
      rw [show (Real.sin (2 * θ)) ^ gam α
            * ((mixed j i f z θ) ^ 2 * ((w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))))
          = ((mixed j i f z θ) ^ 2 * (w z) ^ 2)
              * ((Real.sin (2 * θ)) ^ gam α * (Real.sin (2 * θ)) ^ (-(gam α))) by ring]
      rw [hmul, mul_one]
    rw [hEq]
    exact hsliceθ.const_mul _

/-! ## The iterated `D`-operators commute on the open quadrant -/

/-- On an open set on which `g` is `C^∞` (in the *genuine* smooth order `smoothOrder`, not the
analytic order), `D_z` commutes with every iterate of `D_θ`. -/
theorem DzDthIterCommOn_quad {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hGi : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) V :=
        Work.FTS.LocData.contDiffOn_DthIter hV hg i
      have hF : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (hGi.contDiffAt (hV.mem_nhds hy)).of_le (by simp [Work.Stability.smoothOrder])
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i g) hF
      show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2)
              * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-- On an open set on which `g` is `C^∞`, `D_z^b` commutes with `D_θ^a`. -/
theorem DzIter_DthIter_comm_quad {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.DzIter b g))) V := by
  induction b with
  | zero => intro p hp; rfl
  | succ b ih =>
      intro p hp
      have hstep : Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2 :=
        DzDthIterCommOn_quad hV (Work.FTS.LocData.contDiffOn_DzIter hV hg b) a hp
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.pz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen hV ih hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      rw [hpz]
      show Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      exact hstep

/-- The key consequence: `D_θ` of `D_z^b D_θ^a f` is `D_z^b D_θ^{a+1} f` on the open
quadrant, for a `SmoothQuad` function. -/
theorem Dth_mixed_quad {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (b a : ℕ) {z θ : ℝ}
    (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (mixed b a f) z θ = mixed b (a + 1) f z θ := by
  have hquad : (z, θ) ∈ Work.Spaces.quadU := by
    refine ⟨?_, hθ⟩
    exact Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hz])
  have h1 : Function.uncurry
      (Work.Spaces.DzIter b (Work.Spaces.DthIter 1 (Work.Spaces.DthIter a f))) (z, θ)
      = Function.uncurry
        (Work.Spaces.DthIter 1 (Work.Spaces.DzIter b (Work.Spaces.DthIter a f))) (z, θ) :=
    (DzIter_DthIter_comm_quad Work.Spaces.isOpen_quadU
      (Work.FTS.LocData.contDiffOn_DthIter Work.Spaces.isOpen_quadU hf a) b 1) hquad
  simpa only [Function.uncurry, mixed, DthIter_succ, DthIter_zero] using h1.symm


/-! ## The two Hardy inequalities in the interior form

`RegQ` only gives smoothness inside the open quadrant and one-sided limits at the boundary, so
the Hardy inequalities of `Work.Spaces.HardyTheta`/`HardyZ` (which are phrased for `SmoothNbhd`,
i.e. for smoothness on a neighbourhood of the *closed* quadrant) cannot be applied directly.
Both are re-proved here in the interior form: the angular one from the fundamental theorem on
`[ε,θ]` followed by `ε → 0⁺` (the boundary value is the limit from the right), the radial one
from the fundamental theorem on `[z,B]` followed by `B → ∞` (the boundary value is the limit at
infinity). -/

/-- Monotonicity of the interval integral against the set integral over `Iθ`. -/
lemma interval_integral_le_setIntegral_Iθ {F : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < π / 2) (hint : IntegrableOn F Iθ) (hnn : ∀ x ∈ Iθ, 0 ≤ F x) :
    (∫ x in a..b, F x) ≤ ∫ x in Iθ, F x := by
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_Icc hnn) ?_
  exact Eventually.of_forall fun x hx =>
    ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩

/-- **The angular Hardy inequality in the interior form.**  For a `SmoothQuad` function `g`
whose `θ`-slice at fixed `z > -1` is smooth on `(0,π/2)`, tends to `0` at `θ = 0⁺` and has
`(∂_θ g)² sin(2θ)^{2-γ}` integrable,

  `g(z,θ)² ≤ (100/(γ-1)) ∫_Iθ (∂_θ g(z,σ))² sin(2σ)^{2-γ}`   for `0 < θ < π/2`.

The boundary value at `0` is used only through the limit hypothesis `h0`. -/
theorem HardyThetaO (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ) (z : ℝ)
    (hg : SmoothQuad g) (hz : z ∈ Set.Ioi (-1))
    (h0 : Tendsto (fun θ => g z θ) (𝓝[>] 0) (𝓝 0))
    (hint : IntegrableOn (fun σ => (pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), (g z θ) ^ 2 ≤
      (100 / (gam α - 1)) * ∫ σ in Iθ, (pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) := by
  have hγ1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hp1 : -1 < gam α - 2 := by rw [gam]; linarith
  have hp0 : gam α - 2 ≤ 0 := by rw [gam]; linarith
  have hne0 : Work.Stability.smoothOrder ≠ 0 := by simp [Work.Stability.smoothOrder]
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => g z θ') (Set.Ioo 0 (π / 2)) :=
    hg.curry_θ hz
  have hdth : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => pth g z θ')
      (Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_slice_θ
      (Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hg) hz
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  set A : ℝ := ∫ σ in Iθ, (pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hσ) _)
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
        ⟨lt_trans hε.1 hx.1, lt_of_lt_of_le hx.2 hθ1.le⟩
      exact ((hslice.differentiableOn hne0).differentiableAt
        (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have hintε : IntervalIntegrable (fun s => pth g z s) volume ε θ := hpthcont.intervalIntegrable
    have hFTC : ∫ s in ε..θ, pth g z s = g z θ - g z ε :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεθ hcontθ hderiv hintε
    have hsincont : ∀ c : ℝ,
        ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ c) (Set.uIcc ε θ) := fun c =>
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun s hs => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo (hsub hs))))
    have hcs := hardyZ_interval_integral_mul_le_sqrt ε θ hεθ
      (hpthcont.mul (hsincont ((2 - gam α) / 2))) (hsincont ((gam α - 2) / 2))
    have hcongr : ∫ s in ε..θ,
          (pth g z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2))
            * (Real.sin (2 * s)) ^ ((gam α - 2) / 2)
        = ∫ s in ε..θ, pth g z s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' := hsub hs
      have hsin : 0 < Real.sin (2 * s) := sin_two_pos_of_mem_Ioo hs'
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
          rw [pow_two, ← Real.rpow_add (sin_two_pos_of_mem_Ioo hs')]
          congr 1
          ring
        rw [mul_pow, h1]
      rw [hEq, hAdef]
      exact interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1 hint fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hx) _)
    have hBint : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((gam α - 2) / 2)) ^ 2
        ≤ 100 / (gam α - 1) := by
      have hEq : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((gam α - 2) / 2)) ^ 2
          = ∫ s in ε..θ, (Real.sin (2 * s)) ^ (gam α - 2) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [pow_two, ← Real.rpow_add (sin_two_pos_of_mem_Ioo (hsub hs))]
        congr 1
        ring
      rw [hEq]
      refine le_trans (interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1
        (sin_two_rpow (gam α - 2) hp1 hp0).1
        (fun x hx => Real.rpow_nonneg (sin_two_nonneg hx) _)) ?_
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

/-- The algebraic identity behind the weighted Cauchy–Schwarz step of the *radial* Hardy
inequality: `(z v' w(z)) · (z/(1+z)²) = v'` for `z > 0`. -/
lemma mul_w_mul_psi_eq (v : ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    (s * deriv v s * w s) * (s / (1 + s) ^ 2) = deriv v s := by
  have h1 : (1 + s) ≠ 0 := ne_of_gt (by linarith)
  simp only [w]
  field_simp

/-- **The radial Hardy inequality in the interior form.**  For a function `v` of class `C¹` on
`(0,∞)` with `v → 0` at `+∞` and `(z v')² w(z)²` integrable on `[0,∞)`,

  `v(z)² ≤ ∫_0^∞ (s v'(s))² w(s)² ds`   for `z > 0`. -/
theorem hardyZ_open {v : ℝ → ℝ} (hcd : ContDiffOn ℝ 1 v (Set.Ioi (0 : ℝ)))
    (hdec : Tendsto v atTop (𝓝 0))
    (hint : IntegrableOn (fun s => (s * deriv v s) ^ 2 * (w s) ^ 2) Iz) :
    ∀ z ∈ Set.Ioi (0 : ℝ), (v z) ^ 2 ≤ ∫ s in Iz, (s * deriv v s) ^ 2 * (w s) ^ 2 := by
  set P : ℝ := ∫ s in Iz, (s * deriv v s) ^ 2 * (w s) ^ 2 with hPdef
  have hPnn : 0 ≤ P := integral_nonneg fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hderivcont : ContinuousOn (deriv v) (Set.Ioi (0 : ℝ)) := by
    have h := hcd.continuousOn_derivWithin isOpen_Ioi.uniqueDiffOn le_rfl
    exact h.congr fun x hx => (derivWithin_of_isOpen isOpen_Ioi hx).symm
  intro z hz
  have hz0 : 0 < z := hz
  have hkey : ∀ B, z ≤ B → |v z| ≤ |v B| + Real.sqrt P := by
    intro B hzB
    have hcont : ContinuousOn v (Set.Icc z B) :=
      hcd.continuousOn.mono fun x hx => lt_of_lt_of_le hz0 hx.1
    have hderiv : ∀ x ∈ Set.Ioo z B, HasDerivAt v (deriv v x) x := by
      intro x hx
      exact ((hcd.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds (lt_of_lt_of_le hz0 hx.1.le))).hasDerivAt
    have hderivIcc : ContinuousOn (deriv v) (Set.Icc z B) :=
      hderivcont.mono fun x hx => lt_of_lt_of_le hz0 hx.1
    have hcontU : ContinuousOn (deriv v) (Set.uIcc z B) := by
      rw [Set.uIcc_of_le hzB]
      exact hderivIcc
    have hintB : IntervalIntegrable (deriv v) volume z B := hcontU.intervalIntegrable
    have hFTC : ∫ s in z..B, deriv v s = v B - v z :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hzB hcont hderiv hintB
    have hcontA : ContinuousOn (fun s => s * deriv v s * w s) (Set.uIcc z B) := by
      rw [Set.uIcc_of_le hzB]
      have h1 : ContinuousOn (fun s : ℝ => s * deriv v s) (Set.Icc z B) :=
        continuousOn_id.mul (hderivIcc)
      have h2 : ContinuousOn w (Set.Icc z B) := by
        unfold w
        refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
          (continuousOn_id.pow 2) fun x hx => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz0 hx.1))
      exact h1.mul h2
    have hcontψ : ContinuousOn (fun s : ℝ => s / (1 + s) ^ 2) (Set.uIcc z B) := by
      rw [Set.uIcc_of_le hzB]
      refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2)
        fun x hx => pow_ne_zero 2 (ne_of_gt (by linarith [lt_of_lt_of_le hz0 hx.1]))
    have hcs := hardyZ_interval_integral_mul_le_sqrt z B hzB hcontA hcontψ
    have hcongr : ∫ x in z..B, (x * deriv v x * w x) * (x / (1 + x) ^ 2)
        = ∫ x in z..B, deriv v x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hzB] at hx
      exact mul_w_mul_psi_eq v (lt_of_lt_of_le hz0 hx.1)
    have hA2le : ∫ x in z..B, (x * deriv v x * w x) ^ 2 ≤ P := by
      have h1 : ∫ x in z..B, (x * deriv v x * w x) ^ 2
          = ∫ x in z..B, (x * deriv v x) ^ 2 * (w x) ^ 2 := by
        refine intervalIntegral.integral_congr fun x _ => by ring
      rw [h1, hPdef]
      exact hardyZ_integral_Ioc_le_integral_Iz hz0.le hzB hint
        fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hψle : ∫ x in z..B, (x / (1 + x) ^ 2) ^ 2 ≤ 1 :=
      hardyZ_integral_psi_sq_le_one hz0.le hzB
    have hchain : |∫ x in z..B, deriv v x| ≤ Real.sqrt P := by
      rw [← hcongr]
      calc |∫ x in z..B, (x * deriv v x * w x) * (x / (1 + x) ^ 2)|
          ≤ Real.sqrt (∫ x in z..B, (x * deriv v x * w x) ^ 2)
              * Real.sqrt (∫ x in z..B, (x / (1 + x) ^ 2) ^ 2) := hcs
        _ ≤ Real.sqrt P * Real.sqrt 1 :=
            mul_le_mul (Real.sqrt_le_sqrt hA2le) (Real.sqrt_le_sqrt hψle)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = Real.sqrt P := by rw [Real.sqrt_one, mul_one]
    have hchain' : |v B - v z| ≤ Real.sqrt P := by
      rw [← hFTC]
      exact hchain
    have hsplit : v z = v B - (v B - v z) := by ring
    calc |v z| = |v B - (v B - v z)| := congrArg abs hsplit
      _ ≤ |v B| + |v B - v z| := abs_sub _ _
      _ ≤ |v B| + Real.sqrt P := by linarith [hchain']
  have hlim : Tendsto (fun B => |v B| + Real.sqrt P) atTop (𝓝 (Real.sqrt P)) := by
    simpa using hdec.abs.add_const (Real.sqrt P)
  have hev : ∀ᶠ B in atTop, |v z| ≤ |v B| + Real.sqrt P :=
    (eventually_ge_atTop z).mono fun B hB => hkey B hB
  have hle : |v z| ≤ Real.sqrt P := ge_of_tendsto hlim hev
  calc (v z) ^ 2 = |v z| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt P) ^ 2 := by nlinarith [hle, abs_nonneg (v z), Real.sqrt_nonneg P]
    _ = P := Real.sq_sqrt hPnn

/-! ## The boundary limits supplied by `BdryTraces`

`BdryTraces` records, for each mixed derivative, the two limits
`z·(D_z^jD_θ^i f·w)² → 0` (as `z → 0⁺` and as `z → ∞`) and
`sin(2θ)^{1-γ}·(D_z^jD_θ^i f)² → 0` (as `θ → 0⁺` and as `θ → (π/2)⁻`).  The two lemmas below
turn the second clauses into the *vanishing of the derivative itself* at the boundary, which is
what the Hardy inequalities need: `w → 1` at `∞` kills the radial weight, and `sin(2θ)^{γ-1} → 0`
(recall `γ > 1`) kills the angular one. -/

/-- `w(z) = (1+z)²/z² → 1` at `+∞`. -/
lemma tendsto_w_atTop : Tendsto w atTop (𝓝 1) := by
  have hev : (fun z : ℝ => w z) =ᶠ[atTop] fun z => (1 + 1 / z) ^ 2 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with z hz
    have hz0 : z ≠ 0 := by linarith
    have h1 : w z = ((1 + z) / z) ^ 2 := by rw [w, div_pow]
    have h2 : (1 + z) / z = 1 + 1 / z := by
      rw [add_div, div_self hz0]
      ring
    rw [h1, h2]
  have hlim : Tendsto (fun z : ℝ => (1 + 1 / z) ^ 2) atTop (𝓝 1) := by
    have h : Tendsto (fun z : ℝ => (1 + z⁻¹)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_inv_atTop_zero
    simpa using h.pow 2
  exact hlim.congr' hev.symm

/-- The radial clause of `BdryTraces` forces the mixed derivative itself to vanish at `z → ∞`. -/
lemma tendsto_atTop_zero_of_traces {u : ℝ → ℝ}
    (h : Tendsto (fun z => z * (u z * w z) ^ 2) atTop (𝓝 0)) : Tendsto u atTop (𝓝 0) := by
  have hF : Tendsto (fun z : ℝ => (u z * w z) ^ 2) atTop (𝓝 0) := by
    have hev : (fun z : ℝ => (u z * w z) ^ 2) =ᶠ[atTop]
        fun z => (z * (u z * w z) ^ 2) * (1 / z) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with z hz
      have hz0 : z ≠ 0 := by linarith
      field_simp
    have hz : Tendsto (fun z : ℝ => (z * (u z * w z) ^ 2) * (1 / z)) atTop (𝓝 0) := by
      simpa using h.mul tendsto_inv_atTop_zero
    exact hz.congr' hev.symm
  have hw2 : Tendsto (fun z : ℝ => (w z) ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_w_atTop.pow 2
  have hsq : Tendsto (fun z : ℝ => (u z) ^ 2) atTop (𝓝 0) := by
    have hwinv : Tendsto (fun z : ℝ => ((w z) ^ 2)⁻¹) atTop (𝓝 1) := by
      simpa using hw2.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hdiv : Tendsto (fun z : ℝ => (u z * w z) ^ 2 * ((w z) ^ 2)⁻¹) atTop (𝓝 0) := by
      simpa using hF.mul hwinv
    have hev : (fun z : ℝ => (u z) ^ 2) =ᶠ[atTop]
        fun z => (u z * w z) ^ 2 * ((w z) ^ 2)⁻¹ := by
      filter_upwards [Filter.eventually_ge_atTop 1] with z hz
      have hwne : w z ≠ 0 := by
        rw [w]
        exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (by linarith))
      field_simp
    exact hdiv.congr' hev.symm
  have habs : Tendsto (fun z : ℝ => |u z|) atTop (𝓝 0) := by
    have hcomp := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    rw [Function.comp_def] at hcomp
    have h2 : (fun z : ℝ => Real.sqrt ((u z) ^ 2)) = fun z => |u z| :=
      funext fun z => Real.sqrt_sq_eq_abs (u z)
    rw [h2] at hcomp
    simpa using hcomp
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  simpa only [Real.norm_eq_abs] using habs

/-- The angular clause of `BdryTraces` forces the mixed derivative itself to vanish at `θ → 0⁺`
(here `1 - γ < 0`, so `sin(2θ)^{γ-1}` tends to `0`). -/
lemma tendsto_nhdsGT_zero_of_traces (α : ℝ) (hα : 0 < α) {u : ℝ → ℝ}
    (h : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - gam α) * (u θ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hγ1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγne : gam α ≠ 0 := by rintro h0; rw [h0] at hγ1; norm_num at hγ1
  have hsinlim : Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (gam α - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsin : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcont : ContinuousAt (fun θ : ℝ => Real.sin (2 * θ)) 0 :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt
      simpa using hcont.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    have hc : Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (gam α - 1))
        (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ (gam α - 1))) :=
      (Real.continuousAt_rpow_const 0 (gam α - 1) (Or.inr hγ1.le)).tendsto.comp hsin
    rw [Real.zero_rpow (ne_of_gt hγ1)] at hc
    exact hc
  have hprod : Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (gam α - 1)
        * ((Real.sin (2 * θ)) ^ (1 - gam α) * (u θ) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hsinlim.mul h
  have heq : (fun θ => (u θ) ^ 2) =ᶠ[𝓝[>] (0 : ℝ)]
      fun θ => (Real.sin (2 * θ)) ^ (gam α - 1)
        * ((Real.sin (2 * θ)) ^ (1 - gam α) * (u θ) ^ 2) := by
    have hlt : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < π / 2 :=
      Filter.Eventually.filter_mono (nhdsWithin_le_nhds)
        (isOpen_Iio.mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2))
    filter_upwards [eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0), hlt] with θ hθ0 hθlt
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Set.mem_Ioi.mp hθ0])
        (by linarith [hθlt, Real.pi_pos])
    rw [← mul_assoc, ← Real.rpow_add hsin, show (gam α - 1) + (1 - gam α) = 0 by ring,
      Real.rpow_zero, one_mul]
  have hsq : Tendsto (fun θ => (u θ) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := hprod.congr' heq.symm
  have habs : Tendsto (fun θ => |u θ|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcomp := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    rw [Function.comp_def] at hcomp
    have h2 : (fun θ : ℝ => Real.sqrt ((u θ) ^ 2)) = fun θ => |u θ| :=
      funext fun θ => Real.sqrt_sq_eq_abs (u θ)
    rw [h2] at hcomp
    simpa using hcomp
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  simpa only [Real.norm_eq_abs] using habs

/-- The radial Hardy inequality applied to the `θ`-slice of a mixed derivative. -/
lemma mixed_slice_hardyZ (α : ℝ) (f : ℝ → ℝ → ℝ) (hsq : SmoothQuad f)
    (hbd : Work.FTS.Nonlin.BdryTraces α 4 f) (j i : ℕ) (hij : i + j ≤ 4) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo 0 (π / 2))
    (hint : IntegrableOn (fun z => (mixed (j + 1) i f z σ) ^ 2 * (w z) ^ 2) Iz) :
    ∀ z ∈ Set.Ioi (0 : ℝ), (mixed j i f z σ) ^ 2
      ≤ ∫ s in Iz, (mixed (j + 1) i f s σ) ^ 2 * (w s) ^ 2 := by
  have hcd : ContDiffOn ℝ 1 (fun z => mixed j i f z σ) (Set.Ioi (0 : ℝ)) :=
    ((hsq.mixed j i).curry_z hσ).of_le (by simp [Work.Stability.smoothOrder])
      |>.mono (Set.Ioi_subset_Ioi (by norm_num))
  have hdec : Tendsto (fun z => mixed j i f z σ) atTop (𝓝 0) :=
    tendsto_atTop_zero_of_traces ((hbd i j hij).1 σ hσ |>.2)
  intro z hz
  exact hardyZ_open hcd hdec hint z hz

/-- Almost every `θ ∈ Iθ` lies in the *open* interval `(0,π/2)`. -/
lemma ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have hIoo : volume.restrict Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [hIoo]
  exact ae_restrict_mem measurableSet_Ioo


/-- The `θ`-slice of `(D_θ u)² sin(2θ)^{-γ}` is a.e. strongly measurable, for `u` a mixed
derivative of a `SmoothQuad` function. -/
lemma aesm_slice_Dth_mixed_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hsq : SmoothQuad f) (b a : ℕ) {z : ℝ}
    (hz : 0 < z) :
    AEStronglyMeasurable
      (fun σ => (Work.Spaces.Dth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α)))
      (volume.restrict Iθ) := by
  have hDthc : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.Dth (mixed b a f) p.1 p.2) Qd :=
    ((Work.FTS.LocData.contDiffOn_Dth Work.Spaces.isOpen_quadU
        (hsq.mixed b a)).continuousOn.mono Qd_subset_quadU)
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.Dth (mixed b a f) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(gam α))) Qd :=
    (hDthc.pow 2).mul (continuousOn_sin_rpow_Qd (-(gam α)))
  exact aesm_slice_of_continuousOn_Qd _ hcont hz

/-- The `θ`-slice of `(D_θ u)² sin(2θ)^{-γ}` is integrable on `Iθ` for `z > 0`, by domination by
the corresponding mixed slot of `HkIntegrand α 4 f`. -/
lemma integrableOn_Dth_mixed_slice (α : ℝ) (f : ℝ → ℝ → ℝ) (hsq : SmoothQuad f)
    (hmem : HkMem α 4 f) (b a : ℕ) (hij : (a + 1) + b ≤ 4) {z : ℝ} (hz : 0 < z) :
    IntegrableOn
      (fun σ => (Work.Spaces.Dth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α))) Iθ := by
  have hW : IntegrableOn (fun σ => (mixed b (a + 1) f z σ * Wt α z σ) ^ 2) Iθ :=
    integrableOn_slice_mixed_Wt_sq α f hsq hmem b (a + 1) (by omega) hij (le_of_lt hz)
  refine MeasureTheory.Integrable.mono' hW (aesm_slice_Dth_mixed_sq α f hsq b a hz) ?_
  filter_upwards [ae_mem_Ioo_Iθ] with σ hσ
  have hsin : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo hσ
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)),
    Dth_mixed_quad hsq b a hz hσ]
  rw [show (mixed b (a + 1) f z σ * Wt α z σ) ^ 2
      = (mixed b (a + 1) f z σ) ^ 2
        * ((w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α))) from by
    rw [show Wt α z σ = w z * (Real.sin (2 * σ)) ^ (-(gam α / 2)) from rfl, mul_pow,
      Wt_sq_Ioo α z σ hσ]]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact le_mul_of_one_le_left (Real.rpow_nonneg hsin.le _) (one_le_w_sq hz)

/-- **The `L^∞`-`ℋ⁴` trade-off in the interior class.**  For `f` of class `RegQ α 4` and
`a + b ≤ 2`, the mixed derivative `D_z^b D_θ^a f` is bounded on the open quadrant by
`10/√(γ-1)·|f|_{ℋ⁴}`.

Proof: at each `z > 0` the angular Hardy inequality (`HardyThetaO`, with the vanishing at
`θ = 0⁺` supplied by the angular clause of `BdryTraces`, through
`tendsto_nhdsGT_zero_of_traces`) bounds `(D_z^bD_θ^a f)(z,θ)²` by
`(100/(γ-1))∫_θ (D_θD_z^bD_θ^a f)² sin(2θ)^{-γ}`, and at each `θ` the radial Hardy inequality
(`mixed_slice_hardyZ`) bounds `(D_θD_z^bD_θ^a f)(z,θ)²` by the `z`-integral of
`(D_z^{b+1}D_θ^{a+1}f)² w²`.  The iterated integral produced this way is exactly the `θ`-first
form of the mixed slot `(i,j) = (a+1,b+1)` of the `ℋ⁴` integrand, which is `≤ HkSq α 4 f` by
`slotM_quad`. -/
theorem mixed_supAbsO_le (α : ℝ) (f : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsq : SmoothQuad f) (hmem : HkMem α 4 f) (hbd : Work.FTS.Nonlin.BdryTraces α 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) :
    supAbsO (mixed b a f) ≤ 10 / Real.sqrt (gam α - 1) * HkNorm α 4 f := by
  have hγ1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγne : gam α ≠ 0 := ne_of_gt (by linarith : 0 < gam α)
  obtain ⟨hTle, hTint, hTae⟩ :=
    slotM_quad α f hsq hmem (b + 1) (a + 1) (by omega) (by omega)
  have hptslot : ∀ σ ∈ Iθ, ∀ z : ℝ, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2
      = (Real.sin (2 * σ)) ^ (-(gam α))
        * ((mixed (b + 1) (a + 1) f z σ) ^ 2 * (w z) ^ 2) := by
    intro σ hσ z
    rw [show Wt α z σ = w z * (Real.sin (2 * σ)) ^ (-(gam α / 2)) from rfl, mul_pow,
      Wt_sq α hα z σ hσ]
    ring
  set B : ℝ → ℝ := fun σ => ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ) ^ 2 * (w z) ^ 2 with hBdef
  have hBae : (fun σ => (Real.sin (2 * σ)) ^ (-(gam α)) * B σ)
      =ᵐ[volume.restrict Iθ]
      fun σ => ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2 := by
    filter_upwards [hTae, ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)]
      with σ hσint hσI
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
  have hTnn : 0 ≤ T := by
    rw [hTdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (Real.rpow_nonneg (sin_two_nonneg hσ) _)
        (integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hKnn : 0 ≤ 100 / (gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the pointwise bound on the open quadrant
  have hpoint : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |mixed b a f z θ| ≤ Real.sqrt ((100 / (gam α - 1)) * T) := by
    intro z θ hz0 hθ0 hθ1
    have hθI : θ ∈ Iθ := ⟨hθ0.le, hθ1.le⟩
    have hlim0 : Tendsto (fun θ' => mixed b a f z θ') (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsGT_zero_of_traces α hα ((hbd a b (by omega)).2 z (Set.mem_Ioi.mpr hz0) |>.1)
    have hDth_int := integrableOn_Dth_mixed_slice α f hsq hmem b a (by omega) hz0
    have hDth_int2 : IntegrableOn
        (fun σ => (Real.sin (2 * σ)) ^ (-(gam α))
          * (Work.Spaces.Dth (mixed b a f) z σ) ^ 2) Iθ :=
      hDth_int.congr_fun (fun σ _ => by ring) measurableSet_Icc
    have hint_ang : IntegrableOn
        (fun σ => (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ :=
      hDth_int2.congr_fun (fun σ hσ => by
        calc (Real.sin (2 * σ)) ^ (-(gam α))
              * (Work.Spaces.Dth (mixed b a f) z σ) ^ 2
            = (Work.Spaces.Dth (mixed b a f) z σ) ^ 2
                * (Real.sin (2 * σ)) ^ (-(gam α)) := by ring
          _ = (pth (mixed b a f) z σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - gam α) :=
              (pth_sq_mul_sin_eq α hα hα1 (mixed b a f) z σ hσ).symm) measurableSet_Icc
    have hHT := HardyThetaO α hα hα1 (mixed b a f) z (hsq.mixed b a)
      (Set.mem_Ioi.mpr (by linarith)) hlim0 hint_ang θ ⟨hθ0, hθ1⟩
    have hI1 : (∫ σ in Iθ, (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
        = ∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(gam α))
            * (Work.Spaces.Dth (mixed b a f) z σ) ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
      rw [pth_sq_mul_sin_eq α hα hα1 (mixed b a f) z σ hσ]
      ring
    have hrad : ∀ᵐ σ ∂(volume.restrict Iθ),
        (Real.sin (2 * σ)) ^ (-(gam α)) * (Work.Spaces.Dth (mixed b a f) z σ) ^ 2
          ≤ (Real.sin (2 * σ)) ^ (-(gam α)) * B σ := by
      filter_upwards [hTae, ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)]
        with σ hσint hσI
      rcases eq_or_lt_of_le hσI.1 with hσeq | hσpos
      · have hsin0 : Real.sin (2 * σ) = 0 := by rw [← hσeq]; simp
        have hz : (Real.sin (2 * σ)) ^ (-(gam α)) = 0 := by
          rw [hsin0]
          exact Real.zero_rpow (neg_ne_zero.mpr hγne)
        simp [hz]
      rcases eq_or_lt_of_le hσI.2 with hσeq | hσlt
      · have hsin0 : Real.sin (2 * σ) = 0 := by
          rw [hσeq, show 2 * (π / 2) = π by ring, Real.sin_pi]
        have hz : (Real.sin (2 * σ)) ^ (-(gam α)) = 0 := by
          rw [hsin0]
          exact Real.zero_rpow (neg_ne_zero.mpr hγne)
        simp [hz]
      · have hσ' : σ ∈ Set.Ioo 0 (π / 2) := ⟨hσpos, hσlt⟩
        rw [Dth_mixed_quad hsq b a hz0 hσ']
        exact mul_le_mul_of_nonneg_left
          (mixed_slice_hardyZ α f hsq hbd b (a + 1) (by omega) hσ' hσint z
            (Set.mem_Ioi.mpr hz0))
          (Real.rpow_nonneg (sin_two_nonneg hσI) _)
    have hIntLe : (∫ σ in Iθ, (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
        ≤ T := by
      rw [hI1, hTdef]
      exact integral_mono_ae hDth_int2 hTint' hrad
    have hfin : (mixed b a f z θ) ^ 2 ≤ (100 / (gam α - 1)) * T :=
      le_trans hHT (mul_le_mul_of_nonneg_left hIntLe hKnn)
    calc |mixed b a f z θ| = Real.sqrt ((mixed b a f z θ) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((100 / (gam α - 1)) * T) := Real.sqrt_le_sqrt hfin
  refine le_trans (supAbsO_le (g := mixed b a f)
    (C := Real.sqrt ((100 / (gam α - 1)) * T)) hpoint) ?_
  have h1 : Real.sqrt ((100 / (gam α - 1)) * T)
      ≤ Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 f) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTle' hKnn)
  refine le_trans h1 ?_
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
  exact le_of_eq hfinal



end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.Q.Base =====
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
set_option maxHeartbeats 1600000

/-! ## Two order bookkeeping helpers -/

/-- Transport of `ContDiffAt` from the analytic order `⊤` down to the genuine smooth order. -/
theorem contDiffAt_sm_of_top {f : ℝ → ℝ} {x : ℝ}
    (h : ContDiffAt ℝ (⊤ : WithTop ℕ∞) f x) :
    ContDiffAt ℝ Work.Stability.smoothOrder f x :=
  h.of_le (by simp [Work.Stability.smoothOrder])


/-- `deriv` preserves `C^∞`-smoothness on an open set, at the genuine smooth order. -/
theorem contDiffOn_deriv_sm {u : ℝ → ℝ} {s : Set ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder u s) (hs : IsOpen s) :
    ContDiffOn ℝ Work.Stability.smoothOrder (deriv u) s :=
  h.deriv_of_isOpen hs (by simp [Work.Stability.smoothOrder])

/-! ## Leibniz rules at the genuine smooth order -/

/-- Leibniz rule for `∂_z^k` of a product, at a point where both `z`-slices are `C^∞` in the
genuine smooth order.  (The `⊤`-version is `Work.Elliptic.pzIter_mul_local`.) -/
theorem pzIter_mul_local_sm (k : ℕ) {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hu : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => u z' θ) z)
    (hv : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => v z' θ) z) :
    pzIter k (fun z θ => u z θ * v z θ) z θ
      = ∑ c ∈ Finset.range (k + 1),
          (k.choose c : ℝ) * (pzIter c u z θ * pzIter (k - c) v z θ) := by
  rw [pzIter_eq_iteratedDeriv k (fun z θ => u z θ * v z θ) z θ]
  have hfun : (fun z' => (fun z θ => u z θ * v z θ) z' θ)
      = (fun z' => u z' θ) * (fun z' => v z' θ) := rfl
  rw [hfun, iteratedDeriv_mul (hu.of_le (by simp [Work.Stability.smoothOrder]))
    (hv.of_le (by simp [Work.Stability.smoothOrder]))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← pzIter_eq_iteratedDeriv c u z θ, ← pzIter_eq_iteratedDeriv (k - c) v z θ]
  ring

/-- `∂_z^m (z² κ) = z² ∂_z^m κ + 2m z ∂_z^{m-1} κ + m(m-1) ∂_z^{m-2} κ` for `m ≤ 4`, at a
point where the `z`-slice of `κ` is `C^∞`.  (The `⊤`-version is
`Work.Elliptic.pzIter_sq_mul`.) -/
theorem pzIter_sq_mul_sm (m : ℕ) (hm : m ≤ 4) {κ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hκ : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => κ z' θ) z) :
    pzIter m (fun z θ => z ^ 2 * κ z θ) z θ
      = z ^ 2 * pzIter m κ z θ + (2 * (m : ℝ)) * z * pzIter (m - 1) κ z θ
        + ((m : ℝ) * ((m : ℝ) - 1)) * pzIter (m - 2) κ z θ := by
  have hu : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' : ℝ => z' ^ 2) z :=
    contDiffAt_sm_of_top (contDiffAt_id.pow 2)
  have h := pzIter_mul_local_sm (u := fun z _ => z ^ 2) (v := κ) m hu hκ
  rcases m with _ | _ | _ | _ | _ | m
  · rw [h, Finset.sum_range_one]
    simp
  · rw [h, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_sq, Work.Elliptic.pzIter_two_sq]
    norm_num [Nat.choose]
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_sq, Work.Elliptic.pzIter_two_sq,
      Work.Elliptic.pzIter_three_sq]
    norm_num [Nat.choose]
    ring
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_sq, Work.Elliptic.pzIter_two_sq,
      Work.Elliptic.pzIter_three_sq, Work.Elliptic.pzIter_four_sq]
    norm_num [Nat.choose]
    ring
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_sq, Work.Elliptic.pzIter_two_sq,
      Work.Elliptic.pzIter_three_sq, Work.Elliptic.pzIter_four_sq]
    norm_num [Nat.choose]
    ring
  · omega

/-- `∂_z^m ((1+z)³ κ) = (1+z)³∂_z^mκ + 3m(1+z)²∂_z^{m-1}κ + 3m(m-1)(1+z)∂_z^{m-2}κ
+ m(m-1)(m-2)∂_z^{m-3}κ` for `m ≤ 4`, at a point where the `z`-slice of `κ` is `C^∞`.  (The
`⊤`-version is `Work.Elliptic.pzIter_three_mul`.) -/
theorem pzIter_three_mul_sm (m : ℕ) (hm : m ≤ 4) {κ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hκ : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => κ z' θ) z) :
    pzIter m (fun z θ => (z + 1) ^ 3 * κ z θ) z θ
      = (z + 1) ^ 3 * pzIter m κ z θ
        + (3 * (m : ℝ)) * (z + 1) ^ 2 * pzIter (m - 1) κ z θ
        + (3 * (m : ℝ) * ((m : ℝ) - 1)) * (z + 1) * pzIter (m - 2) κ z θ
        + ((m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2)) * pzIter (m - 3) κ z θ := by
  have hu : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' : ℝ => (z' + 1) ^ 3) z :=
    contDiffAt_sm_of_top ((contDiffAt_id.add contDiffAt_const).pow 3)
  have h := pzIter_mul_local_sm (u := fun z _ => (z + 1) ^ 3) (v := κ) m hu hκ
  rcases m with _ | _ | _ | _ | _ | m
  · rw [h, Finset.sum_range_one]
    simp
  · rw [h, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_cube, Work.Elliptic.pzIter_two_cube]
    norm_num [Nat.choose]
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_cube, Work.Elliptic.pzIter_two_cube,
      Work.Elliptic.pzIter_three_cube]
    norm_num [Nat.choose]
    ring
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_cube, Work.Elliptic.pzIter_two_cube,
      Work.Elliptic.pzIter_three_cube, Work.Elliptic.pzIter_four_cube]
    norm_num [Nat.choose]
    ring
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_cube, Work.Elliptic.pzIter_two_cube,
      Work.Elliptic.pzIter_three_cube, Work.Elliptic.pzIter_four_cube]
    norm_num [Nat.choose]
    ring
  · omega

/-! ## The Stirling expansion of `D_z^n`, in the genuine smooth order -/

/-- If the `z`-slice `z ↦ h z θ` is `C^∞` on `(-1,∞)`, then so is each of its iterated
`z`-derivatives.  (The `⊤`-version is `Work.Spaces.pzIter_slice_contDiff`.) -/
theorem pzIter_slice_contDiff_sm {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi (-1))) :
    ∀ k : ℕ, ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => pzIter k h z' θ)
      (Set.Ioi (-1)) := by
  intro k
  induction k with
  | zero => simpa using hsmooth
  | succ n ih =>
    have h : ContDiffOn ℝ Work.Stability.smoothOrder
        (deriv (fun z' => pzIter n h z' θ)) (Set.Ioi (-1)) :=
      contDiffOn_deriv_sm ih isOpen_Ioi
    simpa [pzIter_succ, pz] using h

/-- Differentiability at an interior point of the `z`-slices of the iterated `z`-derivatives
of `h`, at the genuine smooth order. -/
theorem differentiableAt_pzIter_slice_sm {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi (-1)))
    (k : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    DifferentiableAt ℝ (fun z' => pzIter k h z' θ) z :=
  ((pzIter_slice_contDiff_sm hsmooth k).contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt
    Work.FTS.LocData.smoothOrder_ne_zero

/-! Three elementary `z`-calculus facts (private in `Work.Spaces.DzIter_le_of_pzIter`, hence
copied here). -/

private theorem deriv_zpow_sm (k : ℕ) (z : ℝ) :
    deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id k
  rw [show (fun z' : ℝ => z') ^ k = (fun z' : ℝ => z' ^ k) from rfl] at h
  have h1 : deriv (fun z' : ℝ => z') z = 1 := deriv_id z
  rw [h, h1]
  ring

private theorem deriv_pzIter_slice_sm (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    deriv (fun z' => pzIter k h z' θ) z = pzIter (k + 1) h z θ := rfl

private theorem z_mul_term_sm (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B)
      = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | m
  · ring
  · rw [pow_succ]; push_cast; ring

/-- **The expansion of `D_z = z ∂_z` in terms of the Stirling numbers**, at the genuine smooth
order: for a function whose `z`-slices are `C^∞` on `(-1,∞)`,
`D_z^n h = ∑_{k≤n} S(n,k) z^k ∂_z^k h` on `(-1,∞) × ℝ`.  (The `⊤`-version is
`Work.Spaces.DzIter_eq_sum_scoef`.) -/
theorem DzIter_eq_sum_scoef_sm {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi (-1))) :
    ∀ n : ℕ, ∀ z ∈ Set.Ioi (-1),
      DzIter n h z θ = ∑ k ∈ Finset.range (n + 1),
        (scoef n k : ℝ) * (z ^ k * pzIter k h z θ) := by
  intro n
  induction n with
  | zero =>
    intro z hz
    simp [DzIter, scoef]
  | succ n ih =>
    intro z hz
    have hdiff : ∀ k : ℕ, DifferentiableAt ℝ (fun z' => pzIter k h z' θ) z := fun k =>
      differentiableAt_pzIter_slice_sm hsmooth k hz
    have hd1 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k) z := fun k =>
      differentiableAt_pow k
    have hd3 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k * pzIter k h z' θ) z :=
      fun k => (hd1 k).mul (hdiff k)
    have hev : (fun z' => DzIter n h z' θ)
        =ᶠ[𝓝 z] (fun z' => ∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * (z' ^ k * pzIter k h z' θ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih z' hz'
    have hterm : ∀ k : ℕ, deriv (fun z' : ℝ => (scoef n k : ℝ) * (z' ^ k * pzIter k h z' θ)) z
        = (scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
            + z ^ k * pzIter (k + 1) h z θ) := by
      intro k
      rw [deriv_const_mul (d := fun z' : ℝ => z' ^ k * pzIter k h z' θ)
        (scoef n k : ℝ) (hd3 k)]
      congr 1
      have hmul := deriv_mul (c := fun z' : ℝ => z' ^ k)
        (d := fun z' : ℝ => pzIter k h z' θ) (hd1 k) (hdiff k)
      have hmul' : deriv (fun z' : ℝ => z' ^ k * pzIter k h z' θ) z
          = deriv (fun z' : ℝ => z' ^ k) z * pzIter k h z θ
            + z ^ k * deriv (fun z' : ℝ => pzIter k h z' θ) z := hmul
      rw [hmul', deriv_zpow_sm, deriv_pzIter_slice_sm]
    have hderiv : deriv (fun z' => DzIter n h z' θ) z
        = ∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
              + z ^ k * pzIter (k + 1) h z θ) := by
      rw [Filter.EventuallyEq.deriv_eq hev]
      have hsumfun : (fun z' => ∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * (z' ^ k * pzIter k h z' θ))
          = (∑ k ∈ Finset.range (n + 1),
              fun z' => (scoef n k : ℝ) * (z' ^ k * pzIter k h z' θ)) := by
        funext z'
        simp [Finset.sum_apply]
      rw [hsumfun, deriv_sum (fun k hk => (hd3 k).const_mul (scoef n k : ℝ))]
      exact Finset.sum_congr rfl fun k hk => hterm k
    calc DzIter (n + 1) h z θ
        = z * deriv (fun z' => DzIter n h z' θ) z := by simp [DzIter_succ, Dz, pz]
      _ = z * (∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
              + z ^ k * pzIter (k + 1) h z θ)) := by rw [hderiv]
      _ = ∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * ((k : ℝ) * z ^ k * pzIter k h z θ
              + z ^ (k + 1) * pzIter (k + 1) h z θ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have h1 : z * ((scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
                + z ^ k * pzIter (k + 1) h z θ))
              = (scoef n k : ℝ) * (z * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
                + z ^ k * pzIter (k + 1) h z θ)) := by ring
          rw [h1, z_mul_term_sm]
      _ = ∑ j ∈ Finset.range (n + 2), (scoef (n + 1) j : ℝ) * (z ^ j * pzIter j h z θ) :=
          Work.Spaces.scoef_sum_shift n (fun k => pzIter k h z θ) z


/-! ## The triangular estimate at the genuine smooth order -/

/-- **The triangular estimate**, at the genuine smooth order (the exact analogue of
`Work.Elliptic.tri_bound`, whose hypothesis on `κ` is analyticity).  If
`G = (z+1)³ κ` and `|(z+1)^j ∂_z^j G| ≤ Λ` for `j ≤ J` (`J ≤ 4`) at a point with `z > 0`, then
`|(z+1)^{j+3} ∂_z^j κ| ≤ 6000 Λ` for `j ≤ J`. -/
theorem tri_bound_sm {G κ : ℝ → ℝ → ℝ} (hG : G = fun z θ => (z + 1) ^ 3 * κ z θ)
    {z θ Λ : ℝ} {J : ℕ} (hJ : J ≤ 4) (hz : 0 < z)
    (hκ : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => κ z' θ) z)
    (hbound : ∀ j ≤ J, |(z + 1) ^ j * pzIter j G z θ| ≤ Λ) :
    ∀ j ≤ J, |(z + 1) ^ (j + 3) * pzIter j κ z θ| ≤ 6000 * Λ := by
  have hΛ : 0 ≤ Λ := le_trans (abs_nonneg _) (hbound 0 (Nat.zero_le J))
  set B : ℕ → ℝ := fun k => (z + 1) ^ (k + 3) * pzIter k κ z θ with hB
  set Gv : ℕ → ℝ := fun k => (z + 1) ^ k * pzIter k G z θ with hGv
  have hid0 : Gv 0 = B 0 := by
    have h := pzIter_three_mul_sm (κ := κ) 0 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hid1 : Gv 1 = B 1 + 3 * B 0 := by
    have h := pzIter_three_mul_sm (κ := κ) 1 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hid2 : Gv 2 = B 2 + 6 * B 1 + 6 * B 0 := by
    have h := pzIter_three_mul_sm (κ := κ) 2 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hid3 : Gv 3 = B 3 + 9 * B 2 + 18 * B 1 + 6 * B 0 := by
    have h := pzIter_three_mul_sm (κ := κ) 3 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hid4 : Gv 4 = B 4 + 12 * B 3 + 36 * B 2 + 24 * B 1 := by
    have h := pzIter_three_mul_sm (κ := κ) 4 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hGk : ∀ k ≤ J, |Gv k| ≤ Λ := by
    intro k hk
    rw [hGv]
    simpa using hbound k hk
  have b0 : |B 0| ≤ Λ := by rw [← hid0]; exact hGk 0 (Nat.zero_le J)
  have b1 (hJ1 : 1 ≤ J) : |B 1| ≤ 4 * Λ := by
    have h1 : B 1 = Gv 1 - 3 * B 0 := by linarith [hid1]
    have hA : |3 * B 0| = 3 * |B 0| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    calc |B 1| = |Gv 1 - 3 * B 0| := by rw [h1]
      _ ≤ |Gv 1| + |3 * B 0| := abs_sub _ _
      _ = |Gv 1| + 3 * |B 0| := by rw [hA]
      _ ≤ Λ + 3 * Λ := add_le_add (hGk 1 hJ1) (by linarith [b0])
      _ = 4 * Λ := by ring
  have b2 (hJ2 : 2 ≤ J) : |B 2| ≤ 31 * Λ := by
    have h2 : B 2 = Gv 2 - 6 * B 1 - 6 * B 0 := by linarith [hid2]
    have hA : |6 * B 1| = 6 * |B 1| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hB' : |6 * B 0| = 6 * |B 0| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    calc |B 2| = |Gv 2 - 6 * B 1 - 6 * B 0| := by rw [h2]
      _ ≤ |Gv 2| + 6 * |B 1| + 6 * |B 0| := by
          refine le_trans (Work.Elliptic.abs_three_le _ _ _) ?_
          rw [hA, hB']
      _ ≤ Λ + 6 * (4 * Λ) + 6 * Λ := by
          refine add_le_add (add_le_add (hGk 2 hJ2) ?_) ?_
          · linarith [b1 (by omega)]
          · linarith [b0]
      _ = 31 * Λ := by ring
  have b3 (hJ3 : 3 ≤ J) : |B 3| ≤ 358 * Λ := by
    have h3 : B 3 = Gv 3 - 9 * B 2 - 18 * B 1 - 6 * B 0 := by linarith [hid3]
    have hA : |9 * B 2| = 9 * |B 2| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hB' : |18 * B 1| = 18 * |B 1| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hC : |6 * B 0| = 6 * |B 0| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    calc |B 3| = |Gv 3 - 9 * B 2 - 18 * B 1 - 6 * B 0| := by rw [h3]
      _ ≤ |Gv 3| + 9 * |B 2| + 18 * |B 1| + 6 * |B 0| := by
          refine le_trans (Work.Elliptic.abs_four_le _ _ _ _) ?_
          rw [hA, hB', hC]
      _ ≤ Λ + 9 * (31 * Λ) + 18 * (4 * Λ) + 6 * Λ := by
          refine add_le_add (add_le_add (add_le_add (hGk 3 hJ3) ?_) ?_) ?_
          · linarith [b2 (by omega)]
          · linarith [b1 (by omega)]
          · linarith [b0]
      _ = 358 * Λ := by ring
  have b4 (hJ4 : 4 ≤ J) : |B 4| ≤ 5509 * Λ := by
    have h4 : B 4 = Gv 4 - 12 * B 3 - 36 * B 2 - 24 * B 1 := by linarith [hid4]
    have hA : |12 * B 3| = 12 * |B 3| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hB' : |36 * B 2| = 36 * |B 2| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hC : |24 * B 1| = 24 * |B 1| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    calc |B 4| = |Gv 4 - 12 * B 3 - 36 * B 2 - 24 * B 1| := by rw [h4]
      _ ≤ |Gv 4| + 12 * |B 3| + 36 * |B 2| + 24 * |B 1| := by
          refine le_trans (Work.Elliptic.abs_four_le _ _ _ _) ?_
          rw [hA, hB', hC]
      _ ≤ Λ + 12 * (358 * Λ) + 36 * (31 * Λ) + 24 * (4 * Λ) := by
          refine add_le_add (add_le_add (add_le_add (hGk 4 hJ4) ?_) ?_) ?_
          · linarith [b3 (by omega)]
          · linarith [b2 (by omega)]
          · linarith [b1 (by omega)]
      _ = 5509 * Λ := by ring
  intro j hj
  rcases j with _ | _ | _ | _ | _ | j
  · show |B 0| ≤ 6000 * Λ
    exact le_trans b0 (by nlinarith [hΛ])
  · show |B 1| ≤ 6000 * Λ
    exact le_trans (b1 hj) (by nlinarith [hΛ])
  · show |B 2| ≤ 6000 * Λ
    exact le_trans (b2 hj) (by nlinarith [hΛ])
  · show |B 3| ≤ 6000 * Λ
    exact le_trans (b3 hj) (by nlinarith [hΛ])
  · show |B 4| ≤ 6000 * Λ
    exact le_trans (b4 hj) (by nlinarith [hΛ])
  · omega

/-! ## Smoothness of `divZ2 f` on the open quadrant -/






/-! ## The Leibniz expansions of `∂_z^m f` through `f = z²·divZ2 f` -/



end Work.FTS.H2.Q
end
end
-- ===== merged: Submission.Work.FTS.LocData.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## `ℋ^k`-bookkeeping -/

/-- Negation preserves `ℋ^k`-membership. -/
theorem HkMem_neg (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => -f z θ) := by
  constructor
  · intro z hz
    refine IntegrableOn.congr_fun (hf.1 z hz) (fun θ _ => ?_) measurableSet_Icc
    exact (HkIntegrand_neg α k f z θ).symm
  · have h : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ)
        = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      rw [funext (fun θ => HkIntegrand_neg α k f z θ)]
    rw [h]
    exact hf.2

/-- The `ℋ^k`-functional is invariant under negation. -/
theorem HkSq_neg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => -f z θ) = Work.Spaces.HkSq α k f := by
  simp only [Work.Spaces.HkSq]
  exact setIntegral_congr_fun measurableSet_Ici
    (fun z _ => setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => HkIntegrand_neg α k f z θ))


/-! ## The localised perturbation of the profile -/

/-- The far part `zfar L F_*` of the reference profile is `C^∞` on the quadrant (product of the
cut-off factor `1 - χ(·/L)` with `F_*`). -/
theorem SmoothQuad_zfar_Fstar (α L : ℝ) :
    SmoothQuad (Work.Stability.zfar L (Work.Construction.Fstar α)) := by
  have hone : SmoothQuad (fun _ _ : ℝ => (1 : ℝ)) :=
    smoothQuad_of_contDiffOn_uncurry contDiffOn_const
  have hchi : SmoothQuad (fun z θ => (1 : ℝ) - Work.Stability.chi (z / L)) :=
    smoothQuad_sub hone (SmoothQuad_chi_div L)
  have hmain : (fun z θ => (1 - Work.Stability.chi (z / L)) * Work.Construction.Fstar α z θ)
      = Work.Stability.zfar L (Work.Construction.Fstar α) := by
    funext z θ
    rw [Work.Stability.zfar_apply]
  rw [← hmain]
  exact smoothQuad_mul hchi (Fstar_smoothQuad α)

/-- `locG` as a sum: `locG α L β h = -zfar L F_* + β·h`. -/
theorem locG_as_sum (α L β : ℝ) (h : ℝ → ℝ → ℝ) :
    locG α L β h
      = fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ + β * h z θ := by
  funext z θ
  exact locG_eq_zfar α L β h z θ

/-- **The pointwise majorant of the `ℋ⁴`-integrand of `locG`.**  If `K² angMaj/(1+z)²` dominates
the `ℋ⁴`-integrand of the bump `hLoc α`, then `(2·10⁵ α² + 2β²K²)·angMaj/(1+z)²` dominates the
`ℋ⁴`-integrand of `locG α L β (hLoc α)`. -/
theorem HkIntegrand_locG_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L β K Cz : ℝ} (hL : 1 ≤ L)
    (hCz : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2)
    (hK : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (hLoc α) z θ ≤ K ^ 2 * angMaj α θ / (1 + z) ^ 2)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 4 (locG α L β (hLoc α)) z θ
      ≤ (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) * angMaj α θ / (1 + z) ^ 2 := by
  rw [locG_as_sum]
  have hsq : SmoothQuad (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ) :=
    smoothQuad_neg (SmoothQuad_zfar_Fstar α L)
  have hsq2 : SmoothQuad (fun z θ => β * hLoc α z θ) := smoothQuad_const_mul β (SmoothQuad_hLoc α)
  have hstep := HkIntegrand_add_le α 4 hsq hsq2 hz hθ
  have hneg : Work.Spaces.HkIntegrand α 4
      (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ) z θ
      = Work.Spaces.HkIntegrand α 4
          (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ :=
    HkIntegrand_neg α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
  have hcm : Work.Spaces.HkIntegrand α 4 (fun z θ => β * hLoc α z θ) z θ
      = β ^ 2 * Work.Spaces.HkIntegrand α 4 (hLoc α) z θ :=
    HkIntegrand_const_mul α 4 β (hLoc α) z θ
  have hzfar := hCz z hz θ hθ
  have hbump := hK z hz θ hθ
  have hang : 0 ≤ angMaj α θ := angMaj_nonneg hθ
  have hden : 0 < (1 + z) ^ 2 := pow_pos (by linarith [show (0:ℝ) ≤ z from hz]) 2
  rw [hneg, hcm] at hstep
  refine le_trans hstep ?_
  have h1 : 2 * Work.Spaces.HkIntegrand α 4
        (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
      ≤ 2 * (Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2) := by linarith
  have h2 : 2 * (β ^ 2 * Work.Spaces.HkIntegrand α 4 (hLoc α) z θ)
      ≤ 2 * (β ^ 2 * (K ^ 2 * angMaj α θ / (1 + z) ^ 2)) := by
    have hβ2 : 0 ≤ β ^ 2 := sq_nonneg β
    nlinarith [hbump, hβ2, hang, hden]
  have h3 : 2 * (Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2)
      + 2 * (β ^ 2 * (K ^ 2 * angMaj α θ / (1 + z) ^ 2))
      = (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) * angMaj α θ / (1 + z) ^ 2 := by
    ring
  linarith [h1, h2, h3]

/-- The majorant `c·angMaj α θ/(1+z)²` is integrable in `θ` for every `z ∈ Iz`, and its
`z`-integral is integrable on `Iz`. -/
theorem integrableOn_angMaj_majorant (α c : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => c * angMaj α θ / (1 + z) ^ 2) Work.Spaces.Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, c * angMaj α θ / (1 + z) ^ 2)
        Work.Spaces.Iz := by
  obtain ⟨hint, hbound⟩ := angMaj_mem α hα hα1
  have hbound' : ∫ θ in Work.Spaces.Iθ, angMaj α θ ≤ 1000 / (3 * α) + 10001 := hbound
  constructor
  · intro z hz
    have h3 : IntegrableOn (fun θ => (c / (1 + z) ^ 2) * angMaj α θ) Work.Spaces.Iθ :=
      hint.const_mul (c / (1 + z) ^ 2)
    refine h3.congr_fun (fun θ _ => ?_) measurableSet_Icc
    ring
  · have hbase : IntegrableOn (fun x : ℝ => (x + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
    have hconst : IntegrableOn (fun x : ℝ => (∫ θ in Work.Spaces.Iθ, c * angMaj α θ)
        * (x + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      hbase.const_mul _
    have hval : ∫ θ in Work.Spaces.Iθ, c * angMaj α θ
        = c * ∫ θ in Work.Spaces.Iθ, angMaj α θ := integral_const_mul c _
    have heq : ∀ z ∈ Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, c * angMaj α θ / (1 + z) ^ 2)
          = (∫ θ in Work.Spaces.Iθ, c * angMaj α θ) * (z + 1) ^ (-2 : ℝ) := by
      intro z hz
      have hzpos : (0 : ℝ) < z + 1 := by linarith [Set.mem_Ioi.mp hz]
      rw [show (fun θ => c * angMaj α θ / (1 + z) ^ 2)
          = fun θ => (c * angMaj α θ) * (z + 1) ^ (-2 : ℝ) from by
        funext θ
        rw [show ((z + 1) ^ (-2 : ℝ)) = ((z + 1) ^ 2)⁻¹ by
          rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hzpos),
            Real.rpow_two]]
        ring]
      rw [integral_mul_const]
    have hfin : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, c * angMaj α θ / (1 + z) ^ 2)
        (Set.Ioi (0 : ℝ)) :=
      hconst.congr_fun (fun z hz => (heq z hz).symm) measurableSet_Ioi
    rw [Work.Spaces.Iz]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hfin

/-- **`locG α L β (hLoc α)` lies in `ℋ⁴`** (with `L ≥ 1`): the localised perturbation is
dominated by the integrable majorant `(2·10⁵ α² + 2β²K²)·angMaj α θ/(1+z)²`. -/
theorem HkMem_locG (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L β K Cz : ℝ} (hL : 1 ≤ L)
    (hCz : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2)
    (hK : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (hLoc α) z θ ≤ K ^ 2 * angMaj α θ / (1 + z) ^ 2) :
    Work.Spaces.HkMem α 4 (locG α L β (hLoc α)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 4 (locG α L β (hLoc α)) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_HkIntegrand_smoothQuad α 4 _ (SmoothQuad_locG α L β hα hα1 (SmoothQuad_hLoc α))
  refine HkMem_of_majorant (f := locG α L β (hLoc α))
    (M := fun z θ => (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) * angMaj α θ / (1 + z) ^ 2)
    α 4 hcont ?_ ?_ ?_
  · exact (integrableOn_angMaj_majorant α (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) hα hα1).1
  · exact (integrableOn_angMaj_majorant α (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) hα hα1).2
  · intro z hz θ hθ
    exact HkIntegrand_locG_le α hα hα1 hL hCz hK hz hθ

/-- **`zfar L F_* ∈ ℋ⁴`.**  The far part of the reference profile is dominated pointwise by the
integrable majorant `10⁵α²·angMaj α θ/(1+z)²` (`HkIntegrand_zfar_Fstar_le`); this is the `ℋ⁴`
membership of the localised tail.  (The sibling module `HkMem_zfar_Fstar` states the same fact.) -/
theorem HkMem_zfar_Fstar_direct (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L : ℝ} (hL : 1 ≤ L) :
    Work.Spaces.HkMem α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) := by
  obtain ⟨Cz, -, hCz⟩ := HkIntegrand_zfar_Fstar_le
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
      (Work.Stability.zfar L (Work.Construction.Fstar α)) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_HkIntegrand_smoothQuad α 4 _ (SmoothQuad_zfar_Fstar α L)
  refine HkMem_of_majorant
    (f := Work.Stability.zfar L (Work.Construction.Fstar α))
    (M := fun z θ => (Cz * α ^ 2) * angMaj α θ / (1 + z) ^ 2)
    α 4 hcont ?_ ?_ ?_
  · exact (integrableOn_angMaj_majorant α (Cz * α ^ 2) hα hα1).1
  · exact (integrableOn_angMaj_majorant α (Cz * α ^ 2) hα hα1).2
  · intro z hz θ hθ
    have h := hCz α hα hα1 L hL z hz θ hθ
    calc Work.Spaces.HkIntegrand α 4
          (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2 := h
      _ = (Cz * α ^ 2) * angMaj α θ / (1 + z) ^ 2 := by ring

/-- **`hLoc α ∈ ℋ⁴`**: domination of the `ℋ⁴`-integrand of the bump by the integrable majorant
`K²·angMaj α θ/(1+z)²` (`HkIntegrand_hLoc_le`). -/
theorem HkMem_hLoc_direct (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {K : ℝ}
    (hK : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (hLoc α) z θ ≤ K ^ 2 * angMaj α θ / (1 + z) ^ 2) :
    Work.Spaces.HkMem α 4 (hLoc α) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 (hLoc α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_HkIntegrand_smoothQuad α 4 _ (SmoothQuad_hLoc α)
  refine HkMem_of_majorant (f := hLoc α) (M := fun z θ => K ^ 2 * angMaj α θ / (1 + z) ^ 2)
    α 4 hcont ?_ ?_ ?_
  · exact (integrableOn_angMaj_majorant α (K ^ 2) hα hα1).1
  · exact (integrableOn_angMaj_majorant α (K ^ 2) hα hα1).2
  · intro z hz θ hθ
    exact hK z hz θ hθ

/-- **The `L^{-1}`-decay of the far part in `ℋ⁴`**: there is `C` with
`HkSq α 4 (zfar L F_*) ≤ C·α/L` for `L ≥ 1`.  This is the pointwise majorant
`HkIntegrand_zfar_Fstar_le` fed into the far-tail bound `Work.Stability.HkSqZfar`. -/
theorem HkSq_zfar_Fstar_le_direct (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, ∀ L : ℝ, 1 ≤ L →
      Work.Spaces.HkSq α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) ≤ C * α / L := by
  obtain ⟨Cz, hCznn, hCz⟩ := HkIntegrand_zfar_Fstar_le
  have hslice := (integrableOn_angMaj_majorant α (Cz * α ^ 2) hα hα1).1
  have hCang : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, angMaj α θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => angMaj_nonneg hθ)
  refine ⟨Cz * (∫ θ in Work.Spaces.Iθ, angMaj α θ), fun L hL => ?_⟩
  have hLpos : 0 < L := by linarith
  have hMnn : (0 : ℝ) ≤ Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ) :=
    mul_nonneg (mul_nonneg hCznn (sq_nonneg α)) hCang
  have hmajint : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
        (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
        ≤ (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) / z ^ 2 := by
    intro z hz
    by_cases hzL : z < L
    · have hzero : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ) = 0 :=
        Work.Stability.integral_HkIntegrand_zfar_eq_zero (α := α) (k := 4) (Z := L) hLpos
          ⟨hz, hzL⟩
      rw [hzero]
      positivity
    · push_neg at hzL
      have hle : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
            (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2 := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ))
          (hslice z hz) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hCz α hα hα1 L hL z hz θ hθ
      have hval : (∫ θ in Work.Spaces.Iθ, Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2)
          = (Cz * α ^ 2 / (1 + z) ^ 2) * (∫ θ in Work.Spaces.Iθ, angMaj α θ) := by
        rw [show (fun θ => Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2)
            = fun θ => (Cz * α ^ 2 / (1 + z) ^ 2) * angMaj α θ from by funext θ; ring]
        rw [integral_const_mul]
      have hden : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith [hz]
      have hstep : (Cz * α ^ 2 / (1 + z) ^ 2) * (∫ θ in Work.Spaces.Iθ, angMaj α θ)
          ≤ (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) / z ^ 2 := by
        have hA : (0 : ℝ) ≤ Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ) := hMnn
        have hz2 : (0 : ℝ) < z ^ 2 := by nlinarith [hzL]
        have hB : ((1 + z) ^ 2)⁻¹ ≤ (z ^ 2)⁻¹ := by
          have h := one_div_le_one_div_of_le hz2 hden
          simpa [one_div] using h
        calc (Cz * α ^ 2 / (1 + z) ^ 2) * (∫ θ in Work.Spaces.Iθ, angMaj α θ)
            = (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) * ((1 + z) ^ 2)⁻¹ := by
              ring
          _ ≤ (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) * (z ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_left hB hA
          _ = (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) / z ^ 2 := by ring
      linarith [hle, hval.le, hval.ge, hstep]
  have hdom : Work.Stability.FarTailDom α 4
      (Real.sqrt (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ))) L
      (Work.Construction.Fstar α) := by
    intro z hz hzL
    rw [Real.sq_sqrt hMnn]
    exact hmajint z hz
  have hkey := Work.Stability.HkSqZfar (α := α) (k := 4)
    (M := Real.sqrt (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ))) (Z := L)
    (f := Work.Construction.Fstar α) hLpos (Real.sqrt_nonneg _) hdom
  rw [Real.sq_sqrt hMnn] at hkey
  refine le_trans hkey ?_
  have hα2 : α ^ 2 ≤ α := by nlinarith [hα, hα1]
  have hCL : (0 : ℝ) ≤ Cz * (∫ θ in Work.Spaces.Iθ, angMaj α θ) := mul_nonneg hCznn hCang
  have h1 : Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)
      ≤ (Cz * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) * α := by nlinarith [hα2, hCL, hα.le]
  have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (inv_pos.mpr hLpos))
  simpa [div_eq_mul_inv] using h2

/-! ## The datum `g = locG` is admissible -/

/-- The bump `hLoc α = φ·Γ` vanishes for `z ≤ 3/4` (its radial factor is `χ(4· - 5)`). -/
theorem bumpZ_eq_zero_of_le {z : ℝ} (hz : z ≤ 3 / 4) : bumpZ z = 0 := by
  rw [bumpZ_apply, Work.Stability.chi_eq_zero]
  have h1 : 4 * z - 5 ≤ -2 := by linarith
  have h2 : |4 * z - 5| = -(4 * z - 5) := abs_of_nonpos (by linarith)
  rw [h2]; linarith

/-- The bump `hLoc α = φ·Γ` vanishes for `z ≥ 7/4`. -/
theorem bumpZ_eq_zero_of_ge {z : ℝ} (hz : 7 / 4 ≤ z) : bumpZ z = 0 := by
  rw [bumpZ_apply, Work.Stability.chi_eq_zero]
  have h1 : 4 * z - 5 ≥ 2 := by linarith
  have h2 : |4 * z - 5| = 4 * z - 5 := abs_of_nonneg (by linarith)
  rw [h2]; linarith

theorem hLoc_eq_zero_of_le (α : ℝ) {z : ℝ} (hz : z ≤ 3 / 4) (θ : ℝ) : hLoc α z θ = 0 := by
  rw [hLoc_apply, bumpZ_eq_zero_of_le hz, zero_mul]


/-- **`locG α L β (hLoc α)` is an admissible datum**: `C^∞` on the quadrant, vanishing on the
angular boundary and to second order at the axis `z = 0`, and honestly in `ℋ⁴`. -/
theorem dataAdm_locG (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L β K Cz : ℝ} (hL : 1 ≤ L)
    (hCz : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2)
    (hK : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (hLoc α) z θ ≤ K ^ 2 * angMaj α θ / (1 + z) ^ 2) :
    DataAdm α (locG α L β (hLoc α)) := by
  refine ⟨SmoothQuad_locG α L β hα hα1 (SmoothQuad_hLoc α), ?_, ?_,
    HkMem_locG α hα hα1 hL hCz hK⟩
  · have hv := (hLoc_vanishing α hα).1
    exact vanishTheta_locG α L β hα hα1 (fun z => ⟨hv.1 z, hv.2 z⟩)
  · exact zero_slice_locG α L β hα hα1 (fun z θ hz => hLoc_eq_zero_of_le α hz θ) hL

/-- **The `ℋ⁴`-bound on the localised perturbation of the datum**: for `β = N/D`,
`HkNorm α 4 (locG α L β (hLoc α)) ≤ √(2C₀α/L) + √2·|β|·√C₁`, where `C₀` bounds
`L·HkSq α 4 (zfar L F_*)` and `C₁` bounds `HkSq α 4 (hLoc α)`. -/
theorem HkNorm_locG_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L β C₀ C₁ : ℝ} (hL : 1 ≤ L)
    (hC₀nn : 0 ≤ C₀) (hC₁nn : 0 ≤ C₁)
    (hmemH : Work.Spaces.HkMem α 4 (hLoc α))
    (hC₀ : Work.Spaces.HkSq α 4 (Work.Stability.zfar L (Work.Construction.Fstar α))
      ≤ C₀ * α / L)
    (hC₁ : Work.Spaces.HkSq α 4 (hLoc α) ≤ C₁) :
    Work.Spaces.HkNorm α 4 (locG α L β (hLoc α))
      ≤ Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt 2 * |β| * Real.sqrt C₁ := by
  have hmemT : Work.Spaces.HkMem α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) :=
    HkMem_zfar_Fstar_direct α hα hα1 hL
  have hmeqb : Work.Spaces.HkMem α 4 (fun z θ => β * hLoc α z θ) :=
    HkMem_const_mul α 4 β hmemH
  -- the sum bound
  have hsum := HkSq_add_le α 4 (smoothQuad_neg (SmoothQuad_zfar_Fstar α L))
    (smoothQuad_const_mul β (SmoothQuad_hLoc α)) (HkMem_neg α 4 hmemT) hmeqb
  have heq : (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
      + β * hLoc α z θ) = locG α L β (hLoc α) := by
    funext z θ
    exact (locG_eq_zfar α L β (hLoc α) z θ).symm
  rw [heq] at hsum
  have hsq : Work.Spaces.HkSq α 4 (locG α L β (hLoc α))
      ≤ 2 * (C₀ * α / L) + 2 * β ^ 2 * C₁ := by
    have hneg : Work.Spaces.HkSq α 4
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
        = Work.Spaces.HkSq α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) :=
      HkSq_neg α 4 _
    have hcm : Work.Spaces.HkSq α 4 (fun z θ => β * hLoc α z θ)
        = β ^ 2 * Work.Spaces.HkSq α 4 (hLoc α) := HkSq_const_mul α 4 β hmemH
    rw [hneg, hcm] at hsum
    have h1 : 2 * Work.Spaces.HkSq α 4 (Work.Stability.zfar L (Work.Construction.Fstar α))
        ≤ 2 * (C₀ * α / L) := by linarith
    have h2 : 2 * (β ^ 2 * Work.Spaces.HkSq α 4 (hLoc α)) ≤ 2 * (β ^ 2 * C₁) := by
      nlinarith [sq_nonneg β]
    linarith
  -- the square roots
  have hsq0 : 0 ≤ Work.Spaces.HkSq α 4 (locG α L β (hLoc α)) :=
    Work.Spaces.HkSq_nonneg α 4 _
  have hmono : Real.sqrt (Work.Spaces.HkSq α 4 (locG α L β (hLoc α)))
      ≤ Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁) := Real.sqrt_le_sqrt hsq
  have hLpos : 0 < L := by linarith
  have h2C₀ : (0 : ℝ) ≤ 2 * (C₀ * α / L) := by
    have : 0 ≤ C₀ * α / L := div_nonneg (mul_nonneg hC₀nn hα.le) hLpos.le
    linarith
  have h2C₁ : (0 : ℝ) ≤ 2 * β ^ 2 * C₁ := by
    have : 0 ≤ β ^ 2 * C₁ := mul_nonneg (sq_nonneg β) hC₁nn
    linarith
  have hsplit : Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁)
      ≤ Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁) := by
    have h1 : 2 * (C₀ * α / L) + 2 * β ^ 2 * C₁
        ≤ (Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁)) ^ 2 := by
      have ha := Real.sq_sqrt h2C₀
      have hb := Real.sq_sqrt h2C₁
      have ha' := Real.sqrt_nonneg (2 * (C₀ * α / L))
      have hb' := Real.sqrt_nonneg (2 * β ^ 2 * C₁)
      nlinarith [ha, hb, ha', hb']
    calc Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁)
        ≤ Real.sqrt ((Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁)) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁) :=
          Real.sqrt_sq (by positivity)
  have hscal : Real.sqrt (2 * β ^ 2 * C₁) = Real.sqrt 2 * |β| * Real.sqrt C₁ := by
    rw [show (2 : ℝ) * β ^ 2 * C₁ = 2 * β ^ 2 * C₁ by ring,
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * β ^ 2) C₁,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (β ^ 2), Real.sqrt_sq_eq_abs]
  calc Work.Spaces.HkNorm α 4 (locG α L β (hLoc α))
      = Real.sqrt (Work.Spaces.HkSq α 4 (locG α L β (hLoc α))) := rfl
    _ ≤ Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁) := hmono
    _ ≤ Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁) := hsplit
    _ = Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt 2 * |β| * Real.sqrt C₁ := by rw [hscal]

/-! ## The main theorem -/

/-- **THE LOCALISED DATUM IS SMALL** (node N9 of the route).  For every `ε > 0` there is `L₀`
such that for every `L ≥ L₀` there is a scalar `β` with `|β| ≤ ε`, the perturbation
`g = locData α L β (hLoc α) - F_*` `L₁₂`-orthogonal at `z = 0` (`L₁₂(g)(0) = 0`), of
`𝓗⁴`-distance `HkNorm α 4 g ≤ ε` from the reference profile `F_*`, and *admissible* in the
datum class `DataAdm α` of the existence theorem (N6). -/
theorem locData_small (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ ε > 0, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∃ β : ℝ,
      |β| ≤ ε ∧
        Work.Construction.L12 (locG α L β (hLoc α)) 0 = 0 ∧
        Work.Spaces.HkNorm α 4 (locG α L β (hLoc α)) ≤ ε ∧
        DataAdm α (locG α L β (hLoc α)) := by
  intro ε hε
  obtain ⟨C₀, hC₀⟩ := HkSq_zfar_Fstar_le_direct α hα hα1
  obtain ⟨Cz, hCznn, hCz⟩ := HkIntegrand_zfar_Fstar_le
  obtain ⟨K, hKnn, hKmaj⟩ := HkIntegrand_hLoc_le α hα hα1
  have hmemH : Work.Spaces.HkMem α 4 (hLoc α) := HkMem_hLoc_direct α hα hα1 hKmaj
  set C₁ : ℝ := Work.Spaces.HkSq α 4 (hLoc α) with hC₁def
  have hC₁ : Work.Spaces.HkSq α 4 (hLoc α) ≤ C₁ := le_of_eq hC₁def.symm
  have hC₁nn : (0 : ℝ) ≤ C₁ := by rw [hC₁def]; exact Work.Spaces.HkSq_nonneg α 4 _
  have hDpos : 0 < Work.Construction.L12 (hLoc α) 0 := (L12_hLoc α hα hα1).2
  set D : ℝ := Work.Construction.L12 (hLoc α) 0 with hDdef
  have hDpos' : 0 < D := hDpos
  have hC₀nn : 0 ≤ C₀ := by
    have h : 0 ≤ C₀ * α / 1 :=
      le_trans (Work.Spaces.HkSq_nonneg α 4 _)
        (by simpa using hC₀ 1 le_rfl)
    nlinarith [hα]
  have hC₁nn' : 0 ≤ C₁ := hC₁nn
  set L₀ : ℝ := max 1 (max (8 * C₀ * α / ε ^ 2)
    (max (4 * α / (ε * D)) (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)))) with hL₀
  refine ⟨L₀, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : 8 * C₀ * α / ε ^ 2 ≤ L := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
    exact this
  have hL3 : 4 * α / (ε * D) ≤ L := by
    have h1 : max (4 * α / (ε * D)) (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)) ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    exact le_trans (le_max_left _ _) h1
  have hL4 : 8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D) ≤ L := by
    have h1 : max (4 * α / (ε * D)) (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)) ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    exact le_trans (le_max_right _ _) h1
  have hεpos : 0 < ε := hε
  -- the normalising scalar
  refine ⟨Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0 / D, ?_, ?_, ?_, ?_⟩
  · -- `|β| ≤ ε`
    have hN : |Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0|
        ≤ 4 * α / L := L12_zfar_Fstar_abs_le α hα hα1 hL1
    have hLpos : 0 < L := by linarith
    have hden : 0 < ε * D := mul_pos hεpos hDpos'
    have h3 : 4 * α / L ≤ ε * D := by
      rw [div_le_iff₀ hLpos]
      have h3' : 4 * α ≤ ε * D * L := by
        rw [div_le_iff₀ hden] at hL3
        linarith [hL3]
      linarith [h3']
    rw [abs_div, abs_of_pos hDpos', div_le_iff₀ hDpos']
    linarith [hN, h3]
  · -- the `L₁₂`-orthogonality
    rw [L12_locG α L _ hα hα1 hL1]
    have hDne : D ≠ 0 := ne_of_gt hDpos'
    field_simp
    ring
  · -- the `𝓗⁴`-bound
    refine le_trans (HkNorm_locG_le α hα hα1 hL1 hC₀nn hC₁nn hmemH (hC₀ L hL1) hC₁) ?_
    have hN : |Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0|
        ≤ 4 * α / L := L12_zfar_Fstar_abs_le α hα hα1 hL1
    have hLpos : 0 < L := by linarith
    have hβb : |Work.Construction.L12 (Work.Stability.zfar L
        (Work.Construction.Fstar α)) 0 / D| ≤ 4 * α / (L * D) := by
      rw [abs_div, abs_of_pos hDpos']
      rw [show 4 * α / (L * D) = (4 * α / L) / D by field_simp]
      rw [div_le_iff₀ hDpos', div_mul_cancel₀ _ (ne_of_gt hDpos')]
      exact hN
    have harg1 : 2 * (C₀ * α / L) ≤ (ε / 2) ^ 2 := by
      have h2 : 8 * C₀ * α ≤ ε ^ 2 * L := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < ε ^ 2)] at hL2
        linarith [hL2]
      rw [show (2 : ℝ) * (C₀ * α / L) = 2 * C₀ * α / L by ring]
      rw [div_le_iff₀ hLpos]
      nlinarith [h2]
    have hsqrt1 : Real.sqrt (2 * (C₀ * α / L)) ≤ ε / 2 := by
      calc Real.sqrt (2 * (C₀ * α / L)) ≤ Real.sqrt ((ε / 2) ^ 2) := Real.sqrt_le_sqrt harg1
        _ = ε / 2 := Real.sqrt_sq (by linarith)
    have hβterm : Real.sqrt 2 * |Work.Construction.L12 (Work.Stability.zfar L
        (Work.Construction.Fstar α)) 0 / D| * Real.sqrt C₁ ≤ ε / 2 := by
      have h2 : 0 ≤ Real.sqrt 2 * Real.sqrt C₁ :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      calc Real.sqrt 2 * |Work.Construction.L12 (Work.Stability.zfar L
            (Work.Construction.Fstar α)) 0 / D| * Real.sqrt C₁
          = (Real.sqrt 2 * Real.sqrt C₁) * |Work.Construction.L12 (Work.Stability.zfar L
              (Work.Construction.Fstar α)) 0 / D| := by ring
        _ ≤ (Real.sqrt 2 * Real.sqrt C₁) * (4 * α / (L * D)) :=
            mul_le_mul_of_nonneg_left hβb h2
        _ = (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)) * (ε / (2 * L)) := by
            field_simp
            ring
        _ ≤ L * (ε / (2 * L)) := mul_le_mul_of_nonneg_right hL4 (by positivity)
        _ = ε / 2 := by field_simp
    linarith [hsqrt1, hβterm]
  · -- admissibility
    exact dataAdm_locG α hα hα1 hL1
      (fun z hz θ hθ => hCz α hα hα1 L hL1 z hz θ hθ) hKmaj

/-! ## Compactly supported vorticity in physical variables -/




end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlin

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)

set_option autoImplicit false

/-! ## The stream functions of the two halves of `F = F_* + g` -/

/-- `Φ̃_g = Φ_g - (1/(4α)) sin(2θ) L₁₂(g)`: the elliptic residual belonging to the
perturbation (the argument of the elliptic estimates of N1). -/
def PhiTg (α : ℝ) (g Φg : Fn) : Fn := Work.Construction.PhiTil α g Φg

/-- `Φ̃_* = Φ_s - (1/(4α)) sin(2θ) L₁₂(F_*)`: the elliptic residual belonging to `F_*`
(the argument of `PhiStarRegularity`, N3). -/
def PhiTs (α : ℝ) (Φs : Fn) : Fn :=
  Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs

@[simp] theorem PhiTg_apply (α : ℝ) (g Φg : Fn) (z θ : ℝ) :
    PhiTg α g Φg z θ = Work.Construction.PhiTil α g Φg z θ := rfl

@[simp] theorem PhiTs_apply (α : ℝ) (Φs : Fn) (z θ : ℝ) :
    PhiTs α Φs z θ = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ := rfl

/-! ## The pieces of `N₀` (design §3.4 rows 1--7)

The names `N01, …, N06`, `N04a/b`, `N05a/b` are those of `Work.Construction.Terms`;
they are re-stated here only to fix the *shapes* the rows are about.  Row 1 is the
pair `N01 + N02`; row 3 is `N04a`; row 4 is `N04b`; row 5 is `N05a`; row 6 is `N05b`;
row 7 is `N06`; row 2 is `N03`.
-/

/-- Row 1: the two pure-`F_*` terms `N01 + N02` of `N₀`. -/
def N0fix (α : ℝ) : Fn := fun z θ =>
  Work.Construction.N01 α (Work.Construction.Ftot α (fun _ _ => 0)) (fun _ _ => 0) z θ
    + Work.Construction.N02 α (Work.Construction.Ftot α (fun _ _ => 0)) (fun _ _ => 0) z θ

/-- Row 2: `N₀₃ = (1/α) L₁₂(g) g`. -/
def N03g (α : ℝ) (g : Fn) : Fn := Work.Construction.N03 α (Work.Construction.Ftot α g) g

/-- Row 3: `N₀₄ᵃ = (3/(2α)) sin(2θ) L₁₂(g) ∂_θF_*`. -/
def N04aF (α : ℝ) (g : Fn) : Fn :=
  Work.Construction.N04a α (Work.Construction.Ftot α g) g

/-- Row 4: `N₀₄ᵇ = (3/(2α)) L₁₂(g) D_θ g`. -/
def N04bF (α : ℝ) (g : Fn) : Fn :=
  Work.Construction.N04b α (Work.Construction.Ftot α g) g

/-- Row 5: `N₀₅ᵃ = -c2m(θ) L₁₂(g) D_z F_*`. -/
def N05aF (α : ℝ) (g : Fn) : Fn :=
  Work.Construction.N05a α (Work.Construction.Ftot α g) g

/-- Row 6: `N₀₅ᵇ = -c2m(θ) L₁₂(g) D_z g`. -/
def N05bF (α : ℝ) (g : Fn) : Fn :=
  Work.Construction.N05b α (Work.Construction.Ftot α g) g

/-- Row 7: `N₀₆ = -c2m(θ) L₁₂(F_*) D_z g`, i.e. `-c2m(θ)·(2α/(1+z))·D_z g`. -/
def N06F (α : ℝ) (g : Fn) : Fn :=
  Work.Construction.N06 α (Work.Construction.Ftot α g) g

/-! ## The four-way splits of `N₁, …, N₅` (design §3.4 rows 8--26)

Following the paper, `Φ̃ = Φ̃_g + Φ̃_*` and `F = F_* + g`, so each `N_i` splits into
`N_i^{gg} + N_i^{gs} + N_i^{sg} + N_i^{ss}`, the first index recording which stream
function (`g` for `Φ̃_g`, `s` for `Φ̃_*`) and the second which profile (`g` for the
`g`-factor, `s` for the `F_*`-factor) occurs.  The labels of the design table:
`N_i^{gg} = N i gg`, `N_i^{g*} = N i gs`, `N_i^{*g} = N i sg`, `N_i^{**} = N i ss`.
-/

/-- `N₁^{gg} = 2ℛ(Φ̃_g) g` (row 8). -/
def N1gg (α : ℝ) (g Φg : Fn) : Fn :=
  fun z θ => 2 * Work.Construction.Rop α (PhiTg α g Φg) z θ * g z θ

/-- `N₁^{gs} = 2ℛ(Φ̃_g) F_*` (row 9). -/
def N1gs (α : ℝ) (g Φg : Fn) : Fn :=
  fun z θ => 2 * Work.Construction.Rop α (PhiTg α g Φg) z θ * Work.Construction.Fstar α z θ

/-- `N₁^{sg} = 2ℛ(Φ̃_*) g` (row 10). -/
def N1sg (α : ℝ) (Φs g : Fn) : Fn :=
  fun z θ => 2 * Work.Construction.Rop α (PhiTs α Φs) z θ * g z θ

/-- `N₁^{ss} = 2ℛ(Φ̃_*) F_*` (row 11). -/
def N1ss (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => 2 * Work.Construction.Rop α (PhiTs α Φs) z θ * Work.Construction.Fstar α z θ

/-- `N₂^{gg} = -2U(Φ̃_g) ∂_θ g` (row 12). -/
def N2gg (α : ℝ) (g Φg : Fn) : Fn :=
  fun z θ => -2 * Work.Construction.Uop α (PhiTg α g Φg) z θ * Work.Spaces.pth g z θ

/-- `N₂^{gs} = -2U(Φ̃_g) ∂_θ F_*` (row 13). -/
def N2gs (α : ℝ) (g Φg : Fn) : Fn :=
  fun z θ => -2 * Work.Construction.Uop α (PhiTg α g Φg) z θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ

/-- `N₂^{sg} = -2U(Φ̃_*) ∂_θ g` (row 14). -/
def N2sg (α : ℝ) (Φs g : Fn) : Fn :=
  fun z θ => -2 * Work.Construction.Uop α (PhiTs α Φs) z θ * Work.Spaces.pth g z θ

/-- `N₂^{ss} = -2U(Φ̃_*) ∂_θ F_*` (row 15). -/
def N2ss (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => -2 * Work.Construction.Uop α (PhiTs α Φs) z θ
    * Work.Spaces.pth (Work.Construction.Fstar α) z θ

/-- `N₃^{gg} = -2α V(Φ̃_g) D_z g` (row 16). -/
def N3gg (α : ℝ) (g Φg : Fn) : Fn :=
  fun z θ => -2 * α * Work.Construction.Vop (PhiTg α g Φg) z θ * Work.Spaces.Dz g z θ

/-- `N₃^{gs} = -2α V(Φ̃_g) D_z F_*` (row 17). -/
def N3gs (α : ℝ) (g Φg : Fn) : Fn :=
  fun z θ => -2 * α * Work.Construction.Vop (PhiTg α g Φg) z θ
    * Work.Spaces.Dz (Work.Construction.Fstar α) z θ

/-- `N₃^{sg} = -2α V(Φ̃_*) D_z g` (row 18). -/
def N3sg (α : ℝ) (Φs g : Fn) : Fn :=
  fun z θ => -2 * α * Work.Construction.Vop (PhiTs α Φs) z θ * Work.Spaces.Dz g z θ

/-- `N₃^{ss} = -2α V(Φ̃_*) D_z F_*` (row 19). -/
def N3ss (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => -2 * α * Work.Construction.Vop (PhiTs α Φs) z θ
    * Work.Spaces.Dz (Work.Construction.Fstar α) z θ

/-- `N₄^{gg} = -(1/2) sin(2θ) FK(g) ∂_θ g = -(1/2) FK(g) D_θ g` (row 20). -/
def N4gg (α : ℝ) (g : Fn) : Fn :=
  fun z θ => -(1 / 2) * Work.Construction.FK g z * Work.Spaces.Dth g z θ

/-- `N₄^{gs} = -(1/2) sin(2θ) FK(g) ∂_θ F_*` (row 21). -/
def N4gs (α : ℝ) (g : Fn) : Fn :=
  fun z θ => -(1 / 2) * Work.Construction.s2 θ * Work.Construction.FK g z
    * Work.Spaces.pth (Work.Construction.Fstar α) z θ

/-- `N₄^{sg} = -(1/2) FK(F_*) D_θ g` (row 22). -/
def N4sg (α : ℝ) (g : Fn) : Fn :=
  fun z θ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z
    * Work.Spaces.Dth g z θ

/-- `N₄^{ss} = -(1/2) sin(2θ) FK(F_*) ∂_θ F_*` (row 23). -/
def N4ss (α : ℝ) : Fn :=
  fun z θ => -(1 / 2) * Work.Construction.s2 θ
    * Work.Construction.FK (Work.Construction.Fstar α) z
    * Work.Spaces.pth (Work.Construction.Fstar α) z θ

/-- `N₅^{gg} = -sin²θ FK(g) g` (row 24). -/
def N5gg (g : Fn) : Fn :=
  fun z θ => -(Real.sin θ) ^ 2 * Work.Construction.FK g z * g z θ

/-- `N₅^{gs} = -sin²θ FK(g) F_*` (row 25a). -/
def N5gs (α : ℝ) (g : Fn) : Fn :=
  fun z θ => -(Real.sin θ) ^ 2 * Work.Construction.FK g z
    * Work.Construction.Fstar α z θ

/-- `N₅^{sg} = -sin²θ FK(F_*) g` (row 25b). -/
def N5sg (α : ℝ) (g : Fn) : Fn :=
  fun z θ => -(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z * g z θ

/-- `N₅^{ss} = -sin²θ FK(F_*) F_*` (row 26). -/
def N5ss (α : ℝ) : Fn :=
  fun z θ => -(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z
    * Work.Construction.Fstar α z θ

/-! ## The pieces of `N_*` (design §3.4 row `N_*`; §3.5 L-N4.9) -/



/-- `N_*` with the paper's choice `λ = -2μ/(1+μ)`: `μ (D_z g - g)`. -/
def NstarLam (μ : ℝ) (g : Fn) : Fn :=
  fun z θ => μ * (Work.Spaces.Dz g z θ - g z θ)

/-! ## The `μ̄`-term -/

/-- The `μ̄ AK` term of `gRHS`, with `μ̄ = L₁₂(N₀) + L₁₂(N)`. -/
def MuAK (α : ℝ) (g Φs Φg : Fn) : Fn := fun z θ =>
  Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
      (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) * Work.Construction.AK α z θ

/-! ## The monomials of `Pbd`, and the elementary comparisons

`Pbd α X = α²X + √α X² + α^{-3/2}X³ + α^{-5/2}X⁴` is the polynomial of the paper's
estimate (frozen in `Vocab.lean`).  Every per-piece bound of design §3.4 is one of
`α²`, `α²X`, `√α X`, `√α X²`, `α^{3/2}X`, `α^{3/2}X²`, `α^{-1/2}X²`, `α^{-1}X²`,
`α^{-3/2}X³`, `X²`; the lemmas below reduce each of these to `Pbd α X`.
-/

/-- `α²·X ≤ Pbd α X` (only the nonnegativity of the remaining three summands is used). -/
theorem alpha_sq_mul_le_Pbd {α X : ℝ} (hα : 0 < α) (hX : 0 ≤ X) :
    α ^ 2 * X ≤ Pbd α X := by
  have h1 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg α) (by positivity)
  have h2 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  have h3 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  rw [Pbd]; linarith


/-- `√α·X² ≤ Pbd α X`. -/
theorem sqrt_mul_sq_le_Pbd {α X : ℝ} (hα : 0 < α) (hX : 0 ≤ X) :
    Real.sqrt α * X ^ 2 ≤ Pbd α X := by
  have h0 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX
  have h2 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  have h3 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  rw [Pbd]; linarith

/-- `α^{-1/2}X³ ≤ Pbd α X` for `0 < α ≤ 1`. -/
theorem rpow_neg_half_mul_cube_le_Pbd {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    α ^ (-(1 / 2 : ℝ)) * X ^ 3 ≤ Pbd α X := by
  have hle : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
  have h : α ^ (-(1 / 2 : ℝ)) * X ^ 3 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
    mul_le_mul_of_nonneg_right hle (by positivity)
  have h0 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX
  have h3 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg α) (by positivity)
  have h4 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  rw [Pbd] at *; linarith

/-- `α^{-1}X³ ≤ Pbd α X` for `0 < α ≤ 1`. -/
theorem rpow_neg_one_mul_cube_le_Pbd {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    α ^ (-(1 : ℝ)) * X ^ 3 ≤ Pbd α X := by
  have hle : α ^ (-(1 : ℝ)) ≤ α ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
  have h : α ^ (-(1 : ℝ)) * X ^ 3 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
    mul_le_mul_of_nonneg_right hle (by positivity)
  have h0 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX
  have h3 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg α) (by positivity)
  have h4 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  rw [Pbd] at *; linarith

/-- `α^{3/2}X² ≤ Pbd α X` for `0 < α ≤ 1`. -/
theorem rpow_three_half_mul_sq_le_Pbd {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    α ^ (3 / 2 : ℝ) * X ^ 2 ≤ Pbd α X := by
  have hle : α ^ (3 / 2 : ℝ) ≤ Real.sqrt α := by
    rw [Real.sqrt_eq_rpow]
    have h : α ^ (3 / 2 : ℝ) = α ^ (1 / 2 : ℝ) * α ^ (1 : ℝ) := by
      rw [← Real.rpow_add hα]; norm_num
    rw [h, Real.rpow_one]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hα.le _) hα1
  have hs : Real.sqrt α * X ^ 2 ≤ Pbd α X := sqrt_mul_sq_le_Pbd hα hX
  have h : α ^ (3 / 2 : ℝ) * X ^ 2 ≤ Real.sqrt α * X ^ 2 :=
    mul_le_mul_of_nonneg_right hle (by positivity)
  linarith

/-- `X³ ≤ Pbd α X` for `0 < α ≤ 1`. -/
theorem cube_le_Pbd {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    X ^ 3 ≤ Pbd α X := by
  have hle : (1 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (x := α)
      (y := (0 : ℝ)) (z := -(3 / 2 : ℝ)) (by norm_num)
    simpa using h
  have h : X ^ 3 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 := by
    simpa using mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ X ^ 3)
  have h0 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX
  have h3 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg α) (by positivity)
  have h4 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  rw [Pbd] at *; linarith

end Work.FTS.Nonlin
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gSlots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# `gSlots`: the six `z`-slot bounds for a perturbation `g ∈ ℛ⁴(α)`

This file proves the six conjuncts of `gSlots`, the `z`-slots of the nonlinear estimates
for the perturbation `g` of the self-similar profile.

* The first three conjuncts are the *unweighted* `L²`-masses
  `∫ w(z) · ∫_θ (·)²` of `g`, `D_θ g` and `D_z g`: each is dominated by a single summand
  of the `ℋ⁴`-integrand (`g²` by the `D_z⁰`-slot, `(D_θg)²` by the mixed `(i,j) = (1,0)`-slot
  and `(D_zg)²` by the `D_z¹`-slot), whence by `HkSq α 4 g`.

* The last three conjuncts are the *weighted* `1/z`-masses
  `∫ z⁻¹ · A(z)` with `A = √(∫_θ g²)`, `A = ∫_θ |D_θ g|`, `A = ∫_θ |∂_θ g|`.
  Here the sharp machinery is needed: an *angular* Cauchy–Schwarz
  (`∫_θ |∂_θ g| ≤ √(∫_θ (D_θ g)² sin(2θ)^{-γ}) · √(∫_θ sin(2θ)^{γ-2})`, where the fact that
  `γ - 1 = α/10` is what produces the constant `√(10/α)`), followed by a *radial*
  Cauchy–Schwarz against the square-integrable weight `z ↦ z/(1+z)² = 1/(z·w(z))`
  (with `∫_0^∞ (z/(1+z)²)² dz = 1/3 ≤ 1`), which converts `∫ z⁻¹ A` into `√(HkSq α 4 g)`.

All constants are deliberately crude: the statements only need `1 ≤ 20`, `√(π/2) ≤ 20` and
`10 ≤ 300`, so every loss of a factor is harmless.
-/

/-! ## Elementary facts about the weight and the angular interval -/

lemma w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; exact div_nonneg (sq_nonneg _) (sq_nonneg _)

lemma w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

lemma one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : (0:ℝ) < z ^ 2 := by positivity
  rw [Work.Spaces.w, one_le_div hz2]
  nlinarith [sq_nonneg z]

/-- The two endpoints `0` and `π/2` of `Iθ` are null: the angular measure of `Iθ` is that of
the open interval. -/
lemma restrict_Iθ_eq_Ioo : volume.restrict Work.Spaces.Iθ
    = volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2)) := by
  rw [Work.Spaces.Iθ]
  exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm

lemma ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
  rw [restrict_Iθ_eq_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)

lemma sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) : 0 < Real.sin (2*θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `HkSq` is the iterated integral over `(0,∞)`: the `z = 0` slice is irrelevant. -/
lemma HkSq_eq_integral_Ioi (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 4 g = ∫ z in Set.Ioi (0:ℝ), ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 g z θ := by
  rw [Work.Spaces.HkSq, Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]

/-- The elementary amplification behind every slot bound: for `w₀ ≥ 1`, `0 < s ≤ 1`,
`p ≥ 0` the `w₀`-weighted square is dominated by the `w₀/s^{p/2}`-weighted one. -/
lemma w_mul_sq_le (x w0 s p : ℝ) (hw : 1 ≤ w0) (hs : 0 < s) (hs1 : s ≤ 1) (hp : 0 ≤ p) :
    w0 * x ^ 2 ≤ (x * (w0 / s ^ (p / 2))) ^ 2 := by
  have hsp : 0 < s ^ (p/2) := Real.rpow_pos_of_pos hs _
  have hsp1 : s ^ (p/2) ≤ 1 := Real.rpow_le_one hs.le hs1 (by linarith)
  have hsp2 : (s ^ (p/2)) ^ 2 ≤ w0 := by
    have h2 : (s^(p/2)) * (s^(p/2)) ≤ 1 * 1 := mul_self_le_mul_self hsp.le hsp1
    nlinarith [h2, hw, sq_nonneg (s^(p/2))]
  have hwpos : 0 < w0 := lt_of_lt_of_le zero_lt_one hw
  have hcoef : w0 ≤ (w0 / s ^ (p/2)) ^ 2 := by
    have hsp2pos : 0 < (s^(p/2))^2 := pow_pos hsp 2
    have h := div_le_div_of_nonneg_left (sq_nonneg w0) hsp2pos hsp2
    have hw0 : w0 = w0 ^ 2 / w0 := by field_simp
    calc w0 = w0 ^ 2 / w0 := hw0
      _ ≤ w0 ^ 2 / (s ^ (p/2)) ^ 2 := h
      _ = (w0 / s ^ (p/2)) ^ 2 := by rw [div_pow]
  calc w0 * x^2 ≤ (w0 / s^(p/2))^2 * x^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg x)
    _ = (x * (w0 / s^(p/2)))^2 := by ring

/-! ## The pointwise slot bounds -/

lemma slot_g (α : ℝ) {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    Work.Spaces.w z * (g z θ)^2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs := sin_two_pos hθ
  have hs1 : Real.sin (2*θ) ≤ 1 := Real.sin_le_one _
  have h1 := w_mul_sq_le (g z θ) (Work.Spaces.w z) (Real.sin (2*θ)) Work.Spaces.eta
    (one_le_w_of_pos hz) hs hs1 (by norm_num [Work.Spaces.eta])
  have h2 := Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 0 (by norm_num)
  simpa using le_trans h1 h2


lemma slot_Dz (α : ℝ) {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    Work.Spaces.w z * (Work.Spaces.Dz g z θ)^2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs := sin_two_pos hθ
  have hs1 : Real.sin (2*θ) ≤ 1 := Real.sin_le_one _
  have h1 := w_mul_sq_le (Work.Spaces.DzIter 1 g z θ) (Work.Spaces.w z) (Real.sin (2*θ))
    Work.Spaces.eta (one_le_w_of_pos hz) hs hs1 (by norm_num [Work.Spaces.eta])
  have h2 := Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 1 (by norm_num)
  simpa [Work.Spaces.Dz] using le_trans h1 h2

/-! ## The three unweighted slots -/


/-! ## The radial weight `z ↦ z/(1+z)² = 1/(z·w(z))` and its integrals -/

lemma integrableOn_one_div_one_add_sq : IntegrableOn (fun z : ℝ => 1/(1+z)^2) (Set.Ioi 0) := by
  have h := integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := 0) (m := 1)
    (by norm_num) (by norm_num : (-1:ℝ) < 0)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx1 : (0:ℝ) < x + 1 := by linarith [Set.mem_Ioi.mp hx]
  simp only []
  rw [Real.rpow_neg hx1.le, Real.rpow_two, one_div]
  ring_nf

lemma integral_one_div_one_add_sq : ∫ z in Set.Ioi (0:ℝ), 1/(1+z)^2 = 1 := by
  have hint : IntegrableOn (fun x : ℝ => ((1+x)^2)⁻¹) (Set.Ioi 0) :=
    integrableOn_one_div_one_add_sq.congr_fun (fun x _ => by simp only []; rw [one_div])
      measurableSet_Ioi
  have hderiv : ∀ x ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun z : ℝ => -((1+z)⁻¹)) (((1+x)^2)⁻¹) x := by
    intro x hx
    have hx1 : (0:ℝ) < 1 + x := by linarith [Set.mem_Ici.mp hx]
    have h2 := ((hasDerivAt_id x).const_add (1:ℝ)).inv (by simpa using hx1.ne')
    have h3 : HasDerivAt (fun z : ℝ => -((1+z)⁻¹)) (-(-1/(1+x)^2)) x := h2.neg
    convert h3 using 1
    ring
  have hlim : Tendsto (fun z : ℝ => -((1+z)⁻¹)) atTop (𝓝 0) := by
    have h : Tendsto (fun z : ℝ => (1+z)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop (1:ℝ) tendsto_id)
    simpa using h.neg
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  simp only [show ((1:ℝ)+0)⁻¹ = 1 by norm_num, zero_sub, neg_neg] at hval
  have hcongr : ∫ z in Set.Ioi (0:ℝ), 1/(1+z)^2
      = ∫ z in Set.Ioi (0:ℝ), ((1+z)^2)⁻¹ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => by
      show 1/(1+z)^2 = ((1+z)^2)⁻¹; rw [one_div])
  rw [hcongr, hval]

/-- `z ↦ z/(1+z)²` is dominated by `z ↦ 1/(1+z)²` on `(0,∞)`. -/
lemma G_bound {z : ℝ} (hz : 0 < z) : (z/(1+z)^2)^2 ≤ 1/(1+z)^2 := by
  have hz2 : (0:ℝ) < (1+z)^2 := by positivity
  have hkey : z^2 ≤ (1+z)^2 := by
    have h : (1+z)^2 = z^2 + (1 + 2*z) := by ring
    linarith
  rw [div_pow, div_le_div_iff₀ (by positivity : (0:ℝ) < ((1+z)^2)^2) hz2]
  nlinarith [mul_le_mul_of_nonneg_right hkey (show (0:ℝ) ≤ (1+z)^2 by positivity)]

lemma integrableOn_G_sq : IntegrableOn (fun z : ℝ => (z/(1+z)^2)^2) (Set.Ioi 0) := by
  refine Integrable.mono' integrableOn_one_div_one_add_sq ?_ ?_
  · have hden : ContinuousOn (fun z : ℝ => (1+z)^2) (Set.Ioi 0) :=
      ((continuous_const.add continuous_id).pow 2).continuousOn
    have hcont : ContinuousOn (fun z : ℝ => z/(1+z)^2) (Set.Ioi 0) :=
      ContinuousOn.div continuousOn_id hden (fun z hz => by
        have h1 : (0:ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
        positivity)
    exact (hcont.pow 2).aestronglyMeasurable measurableSet_Ioi
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact G_bound (Set.mem_Ioi.mp hz)

lemma integral_G_sq_le_one : ∫ z in Set.Ioi (0:ℝ), (z/(1+z)^2)^2 ≤ 1 := by
  have h := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => sq_nonneg (z/(1+z)^2)) integrableOn_one_div_one_add_sq
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => G_bound (Set.mem_Ioi.mp hz)))
  rwa [integral_one_div_one_add_sq] at h


/-! ## The weighted angular slots and the angular Cauchy–Schwarz estimates -/

/-- `w₀²·x² ≤ (x·(w₀/s^{p/2}))²` for `w₀ > 0`, `0 < s ≤ 1`, `p ≥ 0`: stripping the weight
`w₀` costs only the integrable factor `s^{-p}`. -/
lemma wsq_mul_sq_le (x w0 s p : ℝ) (hw : 0 < w0) (hs : 0 < s) (hs1 : s ≤ 1) (hp : 0 ≤ p) :
    w0 ^ 2 * x ^ 2 ≤ (x * (w0 / s ^ (p / 2))) ^ 2 := by
  have hsp : 0 < s ^ (p/2) := Real.rpow_pos_of_pos hs _
  have hsp1 : s ^ (p/2) ≤ 1 := Real.rpow_le_one hs.le hs1 (by linarith)
  have hsp2 : (s ^ (p/2)) ^ 2 ≤ 1 := by
    have h2 : (s^(p/2)) * (s^(p/2)) ≤ 1 * 1 := mul_self_le_mul_self hsp.le hsp1
    linarith
  have hcoef : w0 ^ 2 ≤ (w0 / s ^ (p/2)) ^ 2 := by
    rw [div_pow]
    have hsp2pos : 0 < (s^(p/2))^2 := pow_pos hsp 2
    calc w0 ^ 2 = w0 ^ 2 / 1 := by ring
      _ ≤ w0 ^ 2 / (s ^ (p/2)) ^ 2 := div_le_div_of_nonneg_left (sq_nonneg w0) hsp2pos hsp2
  calc w0^2 * x^2 ≤ (w0 / s^(p/2))^2 * x^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg x)
    _ = (x * (w0 / s^(p/2)))^2 := by ring

/-- The mixed weight squared: `Wt² = w²·sin(2θ)^{-γ}`. -/
lemma Wt_sq (α : ℝ) {z θ : ℝ} (hs : 0 ≤ Real.sin (2*θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * Real.sin (2*θ) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  congr 1
  rw [← Real.rpow_two, ← Real.rpow_mul hs]
  congr 1
  ring

/-- `w(z)²·g² ≤ HkIntegrand α 4 g`: the `D_z⁰`-slot dominates the `w²`-weighted square. -/
lemma w2_sq_le_HkIntegrand (α : ℝ) {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    (Work.Spaces.w z)^2 * (g z θ)^2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs := sin_two_pos hθ
  have hs1 : Real.sin (2*θ) ≤ 1 := Real.sin_le_one _
  have h1 := wsq_mul_sq_le (g z θ) (Work.Spaces.w z) (Real.sin (2*θ)) Work.Spaces.eta
    (w_pos_of_pos hz) hs hs1 (by norm_num [Work.Spaces.eta])
  exact le_trans h1 (Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 0 (by norm_num))

/-- `w(z)²·(D_θ g)²·sin(2θ)^{-γ} ≤ HkIntegrand α 4 g`: the mixed `(i,j) = (1,0)`-slot. -/
lemma w2_Dth_sq_le_HkIntegrand (α : ℝ) (hα : 0 < α) {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    (Work.Spaces.w z)^2
        * ((Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α)))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs := sin_two_pos hθ
  have hWt2 := Wt_sq α (z := z) (θ := θ) hs.le
  have h2 : ((Work.Spaces.Dth g z θ) * Work.Spaces.Wt α z θ)^2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    simpa using Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 0 (by norm_num) (by norm_num)
  have heq : ((Work.Spaces.Dth g z θ) * Work.Spaces.Wt α z θ)^2
      = (Work.Spaces.w z)^2
        * ((Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α))) := by
    rw [mul_pow, hWt2]; ring
  rwa [heq] at h2

/-- `(D_θ g)²·sin(2θ)^{-γ} ≤ HkIntegrand α 4 g`: the same slot without the `w²`. -/
lemma Dth_sq_le_HkIntegrand (α : ℝ) (hα : 0 < α) {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    (Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs := sin_two_pos hθ
  have hWt2 := Wt_sq α (z := z) (θ := θ) hs.le
  have h2 : ((Work.Spaces.Dth g z θ) * Work.Spaces.Wt α z θ)^2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    simpa using Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 0 (by norm_num) (by norm_num)
  have heq : ((Work.Spaces.Dth g z θ) * Work.Spaces.Wt α z θ)^2
      = (Work.Spaces.w z)^2
        * ((Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α))) := by
    rw [mul_pow, hWt2]; ring
  rw [heq] at h2
  have hw2 : 1 ≤ (Work.Spaces.w z)^2 := by
    nlinarith [one_le_w_of_pos hz, w_nonneg z]
  have hx : 0 ≤ (Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
  calc (Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α))
      = 1 * ((Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α))) :=
        (one_mul _).symm
    _ ≤ (Work.Spaces.w z)^2
          * ((Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_right hw2 hx
    _ ≤ Work.Spaces.HkIntegrand α 4 g z θ := h2

lemma wsq_mul_slice_le (α : ℝ) (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z →
      (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hmem.1 z (le_of_lt hz)) ?_
  rw [restrict_Iθ_eq_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => w2_sq_le_HkIntegrand α hz hθ)

lemma wsq_mul_slice_Dth_le (α : ℝ) (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z →
      (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z (le_of_lt hz)) ?_
  · rw [restrict_Iθ_eq_Ioo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos hθ)) _)))
  · rw [restrict_Iθ_eq_Ioo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => w2_Dth_sq_le_HkIntegrand α hα hz hθ)

/-- `D_θ g = sin(2θ)·∂_θ g` and `sin(2θ) > 0` on the open interval. -/
lemma abs_Dth_eq {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    |Work.Spaces.Dth g z θ| = Real.sin (2*θ) * |Work.Spaces.pth g z θ| := by
  rw [Work.Spaces.Dth, abs_mul, abs_of_pos (sin_two_pos hθ)]

/-- The `θ`-slice of `D_θ g` is continuous on the open interval. -/
lemma continuousOn_Dth_slice {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.Dth g z θ) (Set.Ioo (0:ℝ) (Real.pi/2)) := by
  have hcd := Work.FTS.LocData.contDiffOn_slice_θ
    (Work.FTS.LocData.contDiffOn_DthIter (isOpen_Ioi.prod isOpen_Ioo) hsm 1)
    (show z ∈ Set.Ioi (-1) by simp only [Set.mem_Ioi]; linarith)
  have hcont : ContinuousOn (fun θ => Work.Spaces.DthIter 1 g z θ) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    ContDiffOn.continuousOn hcd
  simpa using hcont


/-- Angular Cauchy–Schwarz for `∂_θ g`. -/
lemma slice_pth_abs_le_sqrt (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → ∫ θ in Work.Spaces.Iθ, |Work.Spaces.pth g z θ|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) := by
  intro z hz
  have hm : ∀ f : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in Set.Ioo 0 (Real.pi/2), f θ :=
    fun f => by rw [restrict_Iθ_eq_Ioo]
  rw [hm (fun θ => |Work.Spaces.pth g z θ|),
    hm (fun θ => (Work.Spaces.Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))),
    hm (fun θ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2))]
  set u : ℝ → ℝ := fun θ =>
    |Work.Spaces.Dth g z θ| * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)/2) with hu
  set v : ℝ → ℝ := fun θ => (Real.sin (2*θ)) ^ ((Work.Spaces.gam α)/2 - 1) with hv
  have hsin_c : ContinuousOn (fun θ : ℝ => Real.sin (2*θ)) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hDth_c := continuousOn_Dth_slice hsm hz
  have hcontU : ContinuousOn u (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    hDth_c.abs.mul (hsin_c.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ))))
  have hcontV : ContinuousOn v (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    hsin_c.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))
  have huv : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), u θ * v θ = |Work.Spaces.pth g z θ| := by
    intro θ hθ
    have hs := sin_two_pos hθ
    have h1 : (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)/2) * (Real.sin (2*θ)) ^ ((Work.Spaces.gam α)/2 - 1)
        = (Real.sin (2*θ)) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hs]
      congr 1
      ring
    rw [hu, hv, mul_assoc, h1, abs_Dth_eq hθ, Real.rpow_neg_one]
    rw [mul_comm (Real.sin (2*θ)) (|Work.Spaces.pth g z θ|), mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hs), mul_one]
  have hu2 : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      (u θ)^2 = (Work.Spaces.Dth g z θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) := by
    intro θ hθ
    have hs := sin_two_pos hθ
    rw [hu]
    have h2 : ((Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)/2))^2
        = (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hs.le]
      congr 1
      ring
    rw [mul_pow, sq_abs, h2]
  have hv2 : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      (v θ)^2 = (Real.sin (2*θ)) ^ (Work.Spaces.gam α - 2) := by
    intro θ hθ
    have hs := sin_two_pos hθ
    rw [hv]
    rw [← Real.rpow_two, ← Real.rpow_mul hs.le]
    congr 1
    ring
  have hU2 : Integrable (fun θ => (u θ)^2) (volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))) := by
    have hHm : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
        (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      (hmem.1 z (le_of_lt hz)).mono_set (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    refine Integrable.mono' hHm ((hcontU.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hu2 θ hθ]
    exact Dth_sq_le_HkIntegrand α hα hz hθ
  have hV2 : Integrable (fun θ => (v θ)^2) (volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))) := by
    have hgamgt : -1 < Work.Spaces.gam α - 2 := by unfold Work.Spaces.gam; linarith
    have hgamle : Work.Spaces.gam α - 2 ≤ 0 := by unfold Work.Spaces.gam; linarith
    have hS : IntegrableOn (fun θ => (Real.sin (2*θ)) ^ (Work.Spaces.gam α - 2))
        (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      ((Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2) hgamgt hgamle).1).mono_set
        (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    refine hS.congr ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => (hv2 θ hθ).symm)
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2)))
    (hcontU.aestronglyMeasurable measurableSet_Ioo)
    (hcontV.aestronglyMeasurable measurableSet_Ioo) hU2 hV2
  have hcongr : ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), |Work.Spaces.pth g z θ|
      = ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), u θ * v θ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => (huv θ hθ).symm)
  have hu2eq : ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (u θ)^2
      = ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2),
          (Work.Spaces.Dth g z θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => hu2 θ hθ)
  have hv2eq : ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (v θ)^2
      = ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (Real.sin (2*θ)) ^ (Work.Spaces.gam α - 2) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => hv2 θ hθ)
  rw [hcongr]
  calc ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), u θ * v θ
      ≤ |∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), u θ * v θ| := le_abs_self _
    _ ≤ Real.sqrt (∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (u θ)^2)
          * Real.sqrt (∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (v θ)^2) := hcs
    _ = Real.sqrt (∫ θ in Set.Ioo (0:ℝ) (Real.pi/2),
            (Work.Spaces.Dth g z θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)))
          * Real.sqrt (∫ θ in Set.Ioo (0:ℝ) (Real.pi/2),
            (Real.sin (2*θ)) ^ (Work.Spaces.gam α - 2)) := by rw [hu2eq, hv2eq]




end Work.FTS.Nonlinear.Pieces.rl1Tools
end
-- ===== merged: Submission.Work.FTS.VocabO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! Scratch type-check of the statements of `FTS/ELL_H2_LEAD.md` (Claude, 2026-10-04).
Definitions only (no theorems, no sorry); the node statements are in ELL_H2_STATEMENTS.lean.txt. -/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

/-! LEAD-FROZEN (curric-46, 2026-10-04): open-quadrant packages and transport clauses replacing the uninhabited EllPkgG/StarPkg of FTS/Vocab.lean. Design: Submission/Work/FTS/ELL_H2_LEAD.md. Do not edit. -/

namespace Work.FTS.VocabO

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Part A -/

/-! ## Part B: the flat angular coefficient norm, and the transport replacements -/

/-- open-quadrant sups of `D_z^b D_θ^i ∂_θ f`, `b + i ≤ l` -/
def CoefTh (l : ℕ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ∑ b ∈ Finset.range (l + 1), ∑ i ∈ Finset.range (l + 1),
    if b + i ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0

def CoefThMem (l : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ b i : ℕ, b + i ≤ l → ∃ K : ℝ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
    |Work.Spaces.mixed b i (Work.Spaces.pth f) z θ| ≤ K

/-- B3. the replacement `N4Extra` transport clauses (IP form). -/
def T2Clause (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f → CoefThMem 1 f →
    Work.FTS.Nonlin.RegQ α 4 g → Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f + CoefTh 1 f) * Work.FTS.Nonlin.Xn α g ^ 2

def T3Clause (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f → CoefThMem 3 f →
    Work.FTS.Nonlin.RegQ α 4 g → Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (Work.Spaces.WlInf α 4 f + CoefTh 3 f)
          * Work.FTS.Nonlin.Xn α g ^ 2

/-! ## Part B: the open-quadrant packages (replacing the uninhabited frozen ones) -/

/-- coefficient class: interior `C^∞` (z > 0 only) + honesty, NO `BdryTraces`. -/
def HQo (α : ℝ) (k : ℕ) (f : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen f ∧ Work.Spaces.HkMem α k f

/-- the plain D-type `𝒲^{l,∞}` norm: open-quadrant sups of `D_z^b D_θ^j f`, `b + j ≤ l`
(no `(z+1)^k∂_z^k`, no angular weight; `WDp α l f ≤ C_l · WlInf α l f` on `SmoothOpen`). -/
def WDp (l : ℕ) (f : Fn) : ℝ :=
  ∑ b ∈ Finset.range (l + 1), ∑ j ∈ Finset.range (l + 1),
    if b + j ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) else 0

def WDMem (l : ℕ) (f : Fn) : Prop :=
  ∀ b j : ℕ, b + j ≤ l → ∃ K : ℝ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
    |Work.Spaces.mixed b j f z θ| ≤ K

structure EllPkgGo (α Ce : ℝ) (g Φg : Fn) : Prop where
  sol : Work.Elliptic.IsBslSol α g Φg
  smooth : Work.FTS.EllipticEst.SmoothOpen Φg
  R : HQo α 4 (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ∧
      Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg))
        ≤ Ce * Work.FTS.Nonlin.Xn α g
  U : HQo α 4 (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ
        / Work.Construction.s2 θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ
        / Work.Construction.s2 θ) ≤ Ce * Work.FTS.Nonlin.Xn α g
  V : HQo α 4 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
        ≤ Ce * Work.FTS.Nonlin.Xn α g
  vanishU : Work.Spaces.VanishTheta (Work.Construction.Uop α (Work.Construction.PhiTil α g Φg))
  Vth : CoefThMem 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      CoefTh 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
        ≤ Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g

structure StarPkgo (α Cs : ℝ) (Φs : Fn) : Prop where
  sol : Work.Elliptic.IsBslSol α (Work.Construction.Fstar α) Φs
  smooth : Work.FTS.EllipticEst.SmoothOpen Φs
  R : WDMem 4 (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ) ∧
      WDp 4 (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
        ≤ Cs * α
  dU : WDMem 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))) ∧
      WDp 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))) ≤ Cs * α
  V : WDMem 4 (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) ∧
      WDp 4 (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) ≤ Cs * α
  vanishU : Work.Spaces.VanishTheta (Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))
  Vth : CoefThMem 3 (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) ∧
      CoefTh 3 (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) ≤ Cs * α

/-! ## Part B: the `Φ_*` decomposition -/

/-- angular part of `F_*` with the `sin 2θ`-moment removed: `∫ Γ̄ sinθcos²θ = 0`. -/
def GamBar (α θ : ℝ) : ℝ := Work.Spaces.Gam α θ / Work.Spaces.c α - (5 / 4) * Real.sin (2 * θ)

/-- the radial profile `φ = 2z/(1+z)²` and `𝒜φ = αz²φ'' + (5+α)zφ'`. -/
def phiR (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2
def phiA (α z : ℝ) : ℝ :=
  α * z ^ 2 * iteratedDeriv 2 phiR z + (5 + α) * z * deriv phiR z

end Work.FTS.VocabO
end
end
