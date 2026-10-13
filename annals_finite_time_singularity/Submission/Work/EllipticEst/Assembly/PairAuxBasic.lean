/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary calculus for the `bslOp` pairing: slices, Fréchet derivatives, support

Helper lemmas used by `Work.EllipticEst.Assembly.bslOp_pairing_self` and by its auxiliaries
`PairAuxDiv` and `PairAuxRest`:

* `θ`-slices and iterated `θ`-derivatives of a function smooth on the open quadrant;
* the bridge between the Fréchet derivative of a plane function and its slice derivatives;
* `bslOp α ψ` vanishes off the topological support of `ψ`, and is continuous on the open
  quadrant for `ψ` smooth there;
* the pairing weight `z^{(5-α)/α} cos θ` is continuous on the open quadrant.
-/
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.EllipticEst.Assembly.PairDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Assembly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Iterated `θ`-derivatives of a function smooth on the open quadrant -/

theorem smoothOpen_pthIter {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (i : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- Multiplication by `tan θ` preserves smoothness on the open quadrant. -/
theorem smoothOpen_tan_mul {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * F z θ) := by
  have htan : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.tan p.2)
      Work.FTS.EllipticEst.Q0 := by
    rw [show (fun p : ℝ × ℝ => Real.tan p.2)
        = fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2 from
      funext fun p => Real.tan_eq_sin_div_cos p.2]
    refine ContDiffOn.div ((Real.contDiff_sin.comp contDiff_snd).contDiffOn)
      ((Real.contDiff_cos.comp contDiff_snd).contDiffOn) (fun p hp => ?_)
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      by linarith [Real.pi_pos]⟩)
  exact htan.mul hF

/-! ## Slice derivatives of a function smooth on the open quadrant -/

theorem hasDerivAt_slice_θ {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => F z θ') (Work.Spaces.pth F z θ) θ :=
  (((hF.curry_θ hz).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds hθ)).hasDerivAt

theorem hasDerivAt_slice_pth {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => Work.Spaces.pth F z θ') (Work.Spaces.pthIter 2 F z θ) θ := by
  have h := hasDerivAt_slice_θ hF.pth hz hθ
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h

theorem hasDerivAt_slice_z {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun z' => F z' θ) (Work.Spaces.pz F z θ) z :=
  hF.hasDerivAt_slice hθ hz

theorem hasDerivAt_slice_pz {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun z' => Work.Spaces.pz F z' θ) (Work.Spaces.pzIter 2 F z θ) z := by
  have h := hF.hasDerivAt_slice_pzIter 1 hθ hz
  simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h

/-! ## The bridge from the Fréchet derivative of a plane function to its slice derivatives -/

theorem fderiv_fst_eq_deriv {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (h : DifferentiableAt ℝ f x) :
    deriv (fun z : ℝ => f (z, x.2)) x.1 = (fderiv ℝ f x) (1, 0) := by
  have hc : HasDerivAt (fun z : ℝ => ((z, x.2) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) x.1 :=
    (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
  have hcomp : HasDerivAt (fun z : ℝ => f (z, x.2))
      ((fderiv ℝ f x) ((1, 0) : ℝ × ℝ)) x.1 := by
    have hh := h.hasFDerivAt.comp_hasDerivAt x.1 hc
    simpa only [Function.comp_def] using hh
  exact hcomp.deriv

theorem fderiv_snd_eq_deriv {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (h : DifferentiableAt ℝ f x) :
    deriv (fun θ : ℝ => f (x.1, θ)) x.2 = (fderiv ℝ f x) (0, 1) := by
  have hc : HasDerivAt (fun θ : ℝ => ((x.1, θ) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) x.2 :=
    (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
  have hcomp : HasDerivAt (fun θ : ℝ => f (x.1, θ))
      ((fderiv ℝ f x) ((0, 1) : ℝ × ℝ)) x.2 := by
    have hh := h.hasFDerivAt.comp_hasDerivAt x.2 hc
    simpa only [Function.comp_def] using hh
  exact hcomp.deriv

/-! ## Vanishing on the complement of the (topological) support -/

/-- Off the topological support of `g`, the function is locally zero on a *product* of open
sets, so that also its slices (and the slices of its slices) are locally zero. -/
theorem exists_isOpen_local_zero_of_notMem_tsupport {g : ℝ → ℝ → ℝ} {x : ℝ × ℝ}
    (hx : x ∉ tsupport (Function.uncurry g)) :
    ∃ U V : Set ℝ, IsOpen U ∧ IsOpen V ∧ x.1 ∈ U ∧ x.2 ∈ V ∧
      ∀ z ∈ U, ∀ θ ∈ V, g z θ = 0 := by
  have hs : (tsupport (Function.uncurry g))ᶜ ∈ 𝓝 x :=
    (isClosed_tsupport _).isOpen_compl.mem_nhds hx
  have hs' : (tsupport (Function.uncurry g))ᶜ ∈ 𝓝 x.1 ×ˢ 𝓝 x.2 := by
    rw [nhds_prod_eq] at hs; exact hs
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hs'
  obtain ⟨U', hU'sub, hU'open, hxU'⟩ := mem_nhds_iff.mp hU
  obtain ⟨V', hV'sub, hV'open, hxV'⟩ := mem_nhds_iff.mp hV
  refine ⟨U', V', hU'open, hV'open, hxU', hxV', fun z hz θ hθ => ?_⟩
  by_contra hne
  have hmem : (z, θ) ∈ Function.support (Function.uncurry g) := Function.mem_support.mpr hne
  exact (hUV ⟨hU'sub hz, hV'sub hθ⟩) (subset_tsupport _ hmem)

/-- `bslOp α ψ` vanishes off the topological support of `ψ` (all of its derivatives -- plain,
iterated and the `tan θ·ψ` combination -- are derivatives of a locally vanishing function). -/
theorem bslOp_eq_zero_off_tsupport {α : ℝ} {ψ : ℝ → ℝ → ℝ} {x : ℝ × ℝ}
    (hx : x ∉ tsupport (Function.uncurry ψ)) : Work.Elliptic.bslOp α ψ x.1 x.2 = 0 := by
  obtain ⟨U, V, hUopen, hVopen, hxU, hxV, hzero⟩ :=
    exists_isOpen_local_zero_of_notMem_tsupport hx
  have hUmem : U ∈ 𝓝 x.1 := hUopen.mem_nhds hxU
  have hVmem : V ∈ 𝓝 x.2 := hVopen.mem_nhds hxV
  have hzslice : ∀ z ∈ U, ∀ θ ∈ V, (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 z] (fun z' => ψ z' θ) := by
    intro z hz θ hθ
    filter_upwards [hUopen.mem_nhds hz] with z' hz'
    exact (hzero z' hz' θ hθ).symm
  have htslice : ∀ z ∈ U, ∀ θ ∈ V, (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 θ] (fun θ' => ψ z θ') := by
    intro z hz θ hθ
    filter_upwards [hVopen.mem_nhds hθ] with θ' hθ'
    exact (hzero z hz θ' hθ').symm
  have h0 : ψ x.1 x.2 = 0 := hzero x.1 hxU x.2 hxV
  have hpz : Work.Spaces.pz ψ x.1 x.2 = 0 :=
    ((hzslice x.1 hxU x.2 hxV).deriv_eq).symm.trans (deriv_const x.1 0)
  have hpz' : ∀ z ∈ U, ∀ θ ∈ V, Work.Spaces.pz ψ z θ = 0 := by
    intro z hz θ hθ
    exact ((hzslice z hz θ hθ).deriv_eq).symm.trans (deriv_const z 0)
  have hpth' : ∀ z ∈ U, ∀ θ ∈ V, Work.Spaces.pth ψ z θ = 0 := by
    intro z hz θ hθ
    exact ((htslice z hz θ hθ).deriv_eq).symm.trans (deriv_const θ 0)
  have hpz2 : Work.Spaces.pzIter 2 ψ x.1 x.2 = 0 := by
    have hs : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x.1] (fun z => Work.Spaces.pz ψ z x.2) := by
      filter_upwards [hUmem] with z hz
      exact (hpz' z hz x.2 hxV).symm
    exact ((hs.deriv_eq).symm.trans (deriv_const x.1 0))
  have hpth2 : Work.Spaces.pthIter 2 ψ x.1 x.2 = 0 := by
    have hs : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x.2] (fun θ => Work.Spaces.pth ψ x.1 θ) := by
      filter_upwards [hVmem] with θ hθ
      exact (hpth' x.1 hxU θ hθ).symm
    exact ((hs.deriv_eq).symm.trans (deriv_const x.2 0))
  have htan : Work.Spaces.pth (fun z θ' => Real.tan θ' * ψ z θ') x.1 x.2 = 0 := by
    have hs : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x.2] (fun θ => Real.tan θ * ψ x.1 θ) := by
      filter_upwards [hVmem] with θ hθ
      rw [hzero x.1 hxU θ hθ, mul_zero]
    exact ((hs.deriv_eq).symm.trans (deriv_const x.2 0))
  rw [Work.Elliptic.bslOp_apply]
  simp only [Work.Elliptic.Lzero]
  rw [hpz2, hpz, hpth2, htan, h0]
  ring

/-! ## Continuity of `bslOp` on the open quadrant -/

theorem continuousOn_bslOp_smoothOpen {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ContinuousOn (fun x : ℝ × ℝ => Work.Elliptic.bslOp α F x.1 x.2)
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun x : ℝ × ℝ => Work.Spaces.pzIter 2 F x.1 x.2)
      Work.FTS.EllipticEst.Q0 := (hF.pzIter 2).continuousOn
  have h2 : ContinuousOn (fun x : ℝ × ℝ => Work.Spaces.pz F x.1 x.2)
      Work.FTS.EllipticEst.Q0 := hF.pz.continuousOn
  have h3 : ContinuousOn (fun x : ℝ × ℝ => Work.Spaces.pthIter 2 F x.1 x.2)
      Work.FTS.EllipticEst.Q0 := (smoothOpen_pthIter hF 2).continuousOn
  have h4 : ContinuousOn (fun x : ℝ × ℝ => Work.Spaces.pth
      (fun z θ' => Real.tan θ' * F z θ') x.1 x.2) Work.FTS.EllipticEst.Q0 :=
    ((smoothOpen_tan_mul hF).pth).continuousOn
  have h5 : ContinuousOn (fun x : ℝ × ℝ => F x.1 x.2) Work.FTS.EllipticEst.Q0 :=
    hF.continuousOn
  have hc1 : ContinuousOn (fun x : ℝ × ℝ => -(α ^ 2 * x.1 ^ 2))
      Work.FTS.EllipticEst.Q0 := by fun_prop
  have hc2 : ContinuousOn (fun x : ℝ × ℝ => α * (5 + α) * x.1)
      Work.FTS.EllipticEst.Q0 := by fun_prop
  have hc3 : ContinuousOn (fun _ : ℝ × ℝ => (6 : ℝ)) Work.FTS.EllipticEst.Q0 :=
    continuousOn_const
  have hsum : ContinuousOn (fun x : ℝ × ℝ =>
      -(α ^ 2 * x.1 ^ 2) * Work.Spaces.pzIter 2 F x.1 x.2
        - (α * (5 + α) * x.1) * Work.Spaces.pz F x.1 x.2
        + (-(Work.Spaces.pthIter 2 F x.1 x.2)
            + Work.Spaces.pth (fun z θ' => Real.tan θ' * F z θ') x.1 x.2
            - 6 * F x.1 x.2)) Work.FTS.EllipticEst.Q0 :=
    ((hc1.mul h1).sub (hc2.mul h2)).add ((h3.neg.add h4).sub (hc3.mul h5))
  simpa only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] using hsum

theorem continuousOn_pairWeight (α : ℝ) :
    ContinuousOn (pairWeight α) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun x : ℝ × ℝ => x.1 ^ pairBeta α) Work.FTS.EllipticEst.Q0 :=
    continuous_fst.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hx).1))
  have h2 : ContinuousOn (fun x : ℝ × ℝ => Real.cos x.2) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_cos.comp continuous_snd).continuousOn
  change ContinuousOn (fun x : ℝ × ℝ => x.1 ^ pairBeta α * Real.cos x.2)
      Work.FTS.EllipticEst.Q0
  exact h1.mul h2

end Work.EllipticEst.Assembly
