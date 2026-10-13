/-
Interior regularity of `bslOp α`: the distributional identity satisfied by the localized unknown.

This module proves `Q0.distEq`: from the pairing hypotheses `Pair V χ A`, `Pair V χ' A'`,
`Pair G χ Ad` (the localized distributions are represented by the integrable functions
`χ · V`, `χ' · V`, `χ · G`) and the localized integral identity `LocalId V G χ χ' σc tt`
(which holds for *compactly supported* smooth test functions), the distributional equation

  `Δ A = - Ad + (5σ)·∂_0 A - (σ·tt)·∂_1 A - (6σ)·A
            + (Δχ - 5∂_0χ + tt·∂_1χ)·A' + (2∂_0χ)·∂_0 A' + (2∂_1χ)·∂_1 A'`

holds on all Schwartz functions.

The only non-elementary point is the passage from the *compactly supported* test functions of
`LocalId` to arbitrary Schwartz functions: since all the coefficients (`χ`, `χ'`, `σc`, `tt`) are
compactly supported, multiplying a test function by a smooth bump `ξ` which is `1` on a
neighbourhood of `tsupport χ ∪ tsupport χ'` does not change any of the integrals appearing in the
identity (`integral_conj`-style pointwise comparison, using that `d0`, `d1` only see the germ of
the test function).
-/
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.EllipticEst.InteriorRegularity.Q0.Defs
import Submission.Work.EllipticEst.InteriorRegularity.Q0.laplacian_smulLeftCLM
import Submission.Work.EllipticEst.InteriorRegularity.Strip

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
