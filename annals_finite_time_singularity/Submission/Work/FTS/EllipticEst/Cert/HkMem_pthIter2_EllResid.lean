import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.L12Iterate
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Gbar_sin
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.Fstar_contDiffOn
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Defs
import Submission.Work.Elliptic.integral_sin_two_mul_sinCos2
import Submission.Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

/-! ## Auxiliary calculus

`F_*(g) = ∫_θ g(z,θ) sinθcos²θ dθ` is `C^∞` on `(0,∞)` for every `g` smooth on a
neighbourhood of the closed quadrant (the parametric integral of a smooth integrand over the
compact angular interval); and a function of one variable whose derivative is a prescribed
`C^∞` function is itself `C^∞` (the primitive lemma needed for `L₁₂` and `Ḡ`). -/

/-- The angular weight `sinθcos²θ` is continuous. -/
theorem continuous_sinCos2_fts : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop

/-- The `θ`-slice of a function smooth on a neighbourhood of the closed quadrant is continuous
on `[0, π/2]`. -/
theorem continuousOn_slice_of_smoothNbhd {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g)
    {z : ℝ} (hz : -1 < z) : ContinuousOn (fun θ : ℝ => g z θ) Work.Spaces.Iθ := by
  have h : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := hg.continuousOn
  have hmap : ContinuousOn (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) Work.Spaces.Iθ :=
    continuousOn_const.prodMk continuousOn_id
  refine h.comp hmap ?_
  intro θ hθ
  obtain ⟨h0, h1⟩ := hθ
  exact ⟨hz, by linarith, by linarith [Real.pi_pos]⟩

/-- **`F_*(g)` is `C^∞` on `(0,∞)`** for every `g` smooth on a neighbourhood of the closed
quadrant.  This is the parametric-integral lemma
`Work.FTS.EllipticEst.contDiffOn_infty_integral_Itheta_Ioi_neg_one` with the angular weight
`sin θ cos²θ`, restricted to `(0,∞)` (the lemma gives `C^∞` on `(-1,∞)`). -/
theorem contDiffOn_fstar_of_smoothNbhd (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0) := by
  intro m
  have hφ : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ :=
    continuous_sinCos2_fts.continuousOn
  have hbig : ContDiffOn ℝ ∞
      (fun z => ∫ θ in Work.Spaces.Iθ, g z θ * Work.Elliptic.sinCos2 θ) (Set.Ioi (-1)) :=
    Work.FTS.EllipticEst.contDiffOn_infty_integral_Itheta_Ioi_neg_one g Work.Elliptic.sinCos2
      hg hφ
  have hmono : ContDiffOn ℝ m
      (fun z => ∫ θ in Work.Spaces.Iθ, g z θ * Work.Elliptic.sinCos2 θ) (Set.Ioi 0) :=
    (contDiffOn_infty.mp hbig m).mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))
  exact hmono

/-- **A primitive of a `C^∞` function is `C^∞`.**  If `f` has derivative `g` at every point of
`(0,∞)` and `g` is `C^∞` there, then so is `f` (`contDiffOn_infty_iff_deriv_of_isOpen` on the
open set `Ioi 0`). -/
theorem contDiffOn_infty_of_hasDerivAt {f g : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt f (g z) z)
    (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0)) :
    ∀ m : ℕ, ContDiffOn ℝ m f (Set.Ioi 0) := by
  have hgTop : ContDiffOn ℝ ∞ g (Set.Ioi 0) := contDiffOn_infty.mpr hg
  have hfTop : ContDiffOn ℝ ∞ f (Set.Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt, ?_⟩
    exact hgTop.congr (fun z hz => (hderiv z hz).deriv)
  exact contDiffOn_infty.mp hfTop

/-- **`L₁₂(F)` is `C^∞` on `(0,∞)`** as soon as `F_*(F)` is `C^∞` there and `r ↦ F_*(F)(r)/r`
is integrable on `(0,∞)`.  The derivative is `-(3 F_*(F)(z)/z)`, which is `C^∞` on `(0,∞)`
(`HasDerivAt_L12_of_Fstar_facts` plus the primitive lemma). -/
theorem L12_contDiffOn_Ioi (F : ℝ → ℝ → ℝ)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 0)) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.L12 F) (Set.Ioi 0) := by
  refine contDiffOn_infty_of_hasDerivAt
    (Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts F hFsm hFint) ?_
  intro m
  have h2 : ContDiffOn ℝ m (fun z : ℝ => 3 * Work.Elliptic.Fstar F z / z) (Set.Ioi 0) :=
    (contDiffOn_const.mul (hFsm m)).div contDiffOn_id (fun z hz => ne_of_gt hz)
  exact h2.neg

/-- **`Ḡ(α,F)` is `C^∞` on `(0,∞)`.**  Since `Gsing α F = G* + Ḡ` and
`G* = -(1/(4α)) L₁₂(F)`, one has `Ḡ = Gsing + (1/(4α))·L₁₂(F)`; both terms are `C^∞` on
`(0,∞)` (`Gsing_smooth_ode_of_facts`, `L12_contDiffOn_Ioi`). -/
theorem Gbar_contDiffOn_Ioi (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 0)) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0) := by
  have hL12 := L12_contDiffOn_Ioi F hFsm hFint
  have hL12d := Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts F hFsm hFint
  have hGsing := (Gsing_smooth_ode_of_facts α F hα hFsm hFint hL12d).1
  intro m
  have hsum : ContDiffOn ℝ m
      (fun z => Work.Elliptic.Gsing α F z + (1 / (4 * α)) * Work.Elliptic.L12 F z)
      (Set.Ioi 0) :=
    (hGsing m).add (contDiffOn_const.mul (hL12 m))
  refine hsum.congr fun z _ => ?_
  simp only [Work.Elliptic.Gbar, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
  ring

/-- Differentiability of the `θ`-slice of a function smooth on a neighbourhood of the closed
quadrant, at an interior point: the `θ`-derivative is the plain partial `∂_θ`
(`Work.Spaces.pth`). -/
theorem hasDerivAt_slice_pth_of_smoothNbhd {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    {z θ : ℝ} (hz : -1 < z) (hθ0 : -1 < θ) (hθ1 : θ < π / 2 + 1) :
    HasDerivAt (fun θ' : ℝ => f z θ') (Work.Spaces.pth f z θ) θ := by
  have hF : DifferentiableAt ℝ (Function.uncurry f) (z, θ) := by
    have h : DifferentiableOn ℝ (Function.uncurry f)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) :=
      hf.differentiableOn (by decide)
    exact h.differentiableAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz, hθ0, hθ1⟩)
  have hstream : DifferentiableAt ℝ (fun θ' : ℝ => ((z, θ') : ℝ × ℝ)) θ := by fun_prop
  have hcomp : DifferentiableAt ℝ (Function.uncurry f ∘ fun θ' : ℝ => (z, θ')) θ :=
    hF.comp θ hstream
  have hslice : DifferentiableAt ℝ (fun θ' : ℝ => f z θ') θ := by
    simpa [Function.comp_def, Function.uncurry] using hcomp
  simpa only [Work.Spaces.pth] using hslice.hasDerivAt

/-- The iterated form: the `θ`-slice of `∂_θ^n f` has derivative `∂_θ^{n+1} f`. -/
theorem hasDerivAt_slice_pthIter_of_smoothNbhd {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (n : ℕ) {z θ : ℝ} (hz : -1 < z) (hθ0 : -1 < θ) (hθ1 : θ < π / 2 + 1) :
    HasDerivAt (fun θ' : ℝ => Work.Spaces.pthIter n f z θ')
      (Work.Spaces.pthIter (n + 1) f z θ) θ :=
  hasDerivAt_slice_pth_of_smoothNbhd (smoothNbhd_pthIter hf n) hz hθ0 hθ1

/-- **The second `θ`-derivative of the residual** `EllResid α F Ψ = Ψ - (1/(4α)) sin 2θ · L₁₂(F)`
on the open quadrant:

  `∂_θθ (EllResid α F Ψ) = ∂_θθΨ + (1/α)·(sin 2θ · L₁₂(F))`,

because `∂_θθ(sin 2θ) = -4 sin 2θ` and `-(1/(4α))·(-4) = 1/α`. -/
theorem pthIter2_EllResid_pointwise (α : ℝ) (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.Spaces.SmoothNbhd Ψ) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
      = Work.Spaces.pthIter 2 Ψ z θ
        + (1 / α) * (Real.sin (2 * θ) * Work.Elliptic.L12 F z) := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hz' : (-1 : ℝ) < z := by linarith
  -- the first derivative of the residual, as a function of `θ`
  have hstep1 : ∀ θ' : ℝ, 0 < θ' → θ' < π / 2 →
      Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ'
        = Work.Spaces.pth Ψ z θ'
          - ((1 / (4 * α)) * (2 * Real.cos (2 * θ'))) * Work.Elliptic.L12 F z := by
    intro θ' h0 h1
    have hsin' : HasDerivAt (fun θ'' : ℝ => Real.sin (2 * θ'')) (2 * Real.cos (2 * θ')) θ' := by
      simpa [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_sin (2 * θ')).comp θ'
          ((hasDerivAt_const (x := θ') (c := (2 : ℝ))).mul (hasDerivAt_id θ'))
    have hslice' : HasDerivAt (fun θ'' : ℝ => Ψ z θ'') (Work.Spaces.pth Ψ z θ') θ' :=
      hasDerivAt_slice_pth_of_smoothNbhd hΨ hz' (by linarith) (by linarith [Real.pi_pos])
    have hd := hslice'.sub ((hsin'.const_mul (1 / (4 * α))).mul_const
      (Work.Elliptic.L12 F z))
    have hfun : ((fun θ'' : ℝ => Ψ z θ'')
          - (fun θ'' : ℝ => ((1 / (4 * α)) * Real.sin (2 * θ''))
              * Work.Elliptic.L12 F z))
        = fun θ'' : ℝ => Ψ z θ''
            - ((1 / (4 * α)) * Real.sin (2 * θ'')) * Work.Elliptic.L12 F z := by
      funext θ''
      simp [Pi.sub_apply]
    rw [hfun] at hd
    simpa only [Work.Spaces.pth, Work.Elliptic.EllResid] using hd.deriv
  -- the derivative of `θ' ↦ (1/(4α))·2cos 2θ'`: it is `(1/(4α))·(-4 sin 2θ)`
  have hcos : HasDerivAt (fun θ' : ℝ => 2 * Real.cos (2 * θ')) (-(4 * Real.sin (2 * θ))) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(2 * Real.sin (2 * θ))) θ := by
      simpa [Function.comp_def, mul_comm, mul_assoc] using
        (Real.hasDerivAt_cos (2 * θ)).comp θ
          ((hasDerivAt_const (x := θ) (c := (2 : ℝ))).mul (hasDerivAt_id θ))
    have h2 := h1.const_mul 2
    have he : 2 * (-(2 * Real.sin (2 * θ))) = -(4 * Real.sin (2 * θ)) := by ring
    rwa [he] at h2
  have hd2 : HasDerivAt (fun θ' : ℝ =>
        ((1 / (4 * α)) * (2 * Real.cos (2 * θ'))) * Work.Elliptic.L12 F z)
      (((1 / (4 * α)) * (-(4 * Real.sin (2 * θ)))) * Work.Elliptic.L12 F z) θ :=
    (hcos.const_mul (1 / (4 * α))).mul_const (Work.Elliptic.L12 F z)
  -- the second derivative
  have hev : (fun θ' : ℝ => Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.pth Ψ z θ'
        - ((1 / (4 * α)) * (2 * Real.cos (2 * θ'))) * Work.Elliptic.L12 F z) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩] with θ' hθ'
    exact hstep1 θ' hθ'.1 hθ'.2
  have hmain : Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
      = deriv (fun θ' : ℝ => Work.Spaces.pth Ψ z θ'
          - ((1 / (4 * α)) * (2 * Real.cos (2 * θ'))) * Work.Elliptic.L12 F z) θ := by
    show deriv (fun θ' : ℝ => Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ') θ = _
    rw [Filter.EventuallyEq.deriv_eq hev]
  have hslice2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.pth Ψ z θ')
      (Work.Spaces.pthIter 2 Ψ z θ) θ := by
    have h := hasDerivAt_slice_pthIter_of_smoothNbhd (f := Ψ) (z := z) (θ := θ) hΨ 1 hz'
      (by linarith) (by linarith [Real.pi_pos])
    simpa using h
  have hdsub := hslice2.sub hd2
  have hdeq : (fun θ' : ℝ => Work.Spaces.pth Ψ z θ'
        - ((1 / (4 * α)) * (2 * Real.cos (2 * θ'))) * Work.Elliptic.L12 F z)
      = ((fun θ' : ℝ => Work.Spaces.pth Ψ z θ')
          - (fun θ' : ℝ => ((1 / (4 * α)) * (2 * Real.cos (2 * θ')))
              * Work.Elliptic.L12 F z)) := by
    funext θ'
    simp [Pi.sub_apply]
  rw [hmain, hdeq, hdsub.deriv]
  field_simp
  try ring

/-- **The smooth integrand `FstarInt α Ψ` is smooth on a neighbourhood of the closed quadrant**
whenever `Ψ` is: it is a sum of products of the derivatives `∂_z²Ψ`, `∂_zΨ`, `∂_θ²Ψ`, `∂_θΨ`, `Ψ`
with polynomials in `z` and functions of `θ` alone. -/
theorem fstarInt_smoothNbhd_fts (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (h : Work.Spaces.SmoothNbhd Ψ) :
    Work.Spaces.SmoothNbhd (FstarInt α Ψ) := by
  have hsin : Work.Spaces.SmoothNbhd (fun _ θ : ℝ => Real.sin θ) :=
    smoothNbhd_snd_comp Real.sin Real.contDiff_sin
  have hcos : Work.Spaces.SmoothNbhd (fun _ θ : ℝ => Real.cos θ) :=
    smoothNbhd_snd_comp Real.cos Real.contDiff_cos
  have hcos2 : Work.Spaces.SmoothNbhd (fun _ θ : ℝ => Real.cos θ ^ 2) :=
    smoothNbhd_snd_comp (fun θ => Real.cos θ ^ 2) (Real.contDiff_cos.pow 2)
  have hsincos : Work.Spaces.SmoothNbhd (fun _ θ : ℝ => Real.sin θ * Real.cos θ) :=
    smoothNbhd_mul' hsin hcos
  have hpz1 : Work.Spaces.SmoothNbhd (fun z θ => Work.Spaces.pz Ψ z θ) :=
    Work.Spaces.smoothNbhd_pzIter h 1
  have hpz2 : Work.Spaces.SmoothNbhd (fun z θ => Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.Spaces.smoothNbhd_pzIter h 2
  have hpth1 : Work.Spaces.SmoothNbhd (fun z θ => Work.Spaces.pth Ψ z θ) :=
    smoothNbhd_pthIter h 1
  have hpth2 : Work.Spaces.SmoothNbhd (fun z θ => Work.Spaces.pthIter 2 Ψ z θ) :=
    smoothNbhd_pthIter h 2
  have hz2 : Work.Spaces.SmoothNbhd (fun z _ : ℝ => z ^ 2) := smoothNbhd_pow_fst 2
  have hz1 : Work.Spaces.SmoothNbhd (fun z _ : ℝ => z) := smoothNbhd_fst
  have hA : Work.Spaces.SmoothNbhd
      (fun z θ => (-(α ^ 2) * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
        - Work.Spaces.pthIter 2 Ψ z θ - 6 * Ψ z θ) := by
    refine smoothNbhd_sub (smoothNbhd_sub (smoothNbhd_sub ?_ ?_) ?_) ?_
    · exact smoothNbhd_mul' (smoothNbhd_const_mul (-(α ^ 2)) hz2) hpz2
    · exact smoothNbhd_mul' (smoothNbhd_const_mul (α * (5 + α)) hz1) hpz1
    · exact hpth2
    · exact smoothNbhd_const_mul 6 h
  have hB : Work.Spaces.SmoothNbhd
      (fun z θ => Real.sin θ * Ψ z θ
        + Real.sin θ * (Real.sin θ * Real.cos θ) * Work.Spaces.pth Ψ z θ) := by
    refine smoothNbhd_add (smoothNbhd_mul' hsin h) ?_
    exact smoothNbhd_mul' (smoothNbhd_mul' hsin hsincos) hpth1
  refine SmoothNbhd_congr (f := fun z θ =>
      ((-(α ^ 2) * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
        - Work.Spaces.pthIter 2 Ψ z θ - 6 * Ψ z θ) * (Real.sin θ * Real.cos θ ^ 2)
      + (Real.sin θ * Ψ z θ
        + Real.sin θ * (Real.sin θ * Real.cos θ) * Work.Spaces.pth Ψ z θ)) ?_ ?_
  · exact smoothNbhd_add (smoothNbhd_mul' hA (smoothNbhd_mul' hsin hcos2)) hB
  · intro z θ
    rw [FstarInt_apply, Work.Elliptic.sinCos2]
    ring

/-- **The angular moment as the integral of the smooth integrand.**  On the open quadrant
`F = bslOp α Ψ`, and multiplying by the weight `sinθcos²θ` turns `bslOp α Ψ` into `FstarInt α Ψ`
(`bslOp_mul_sinCos2_eq`); the two integrands therefore agree off the two endpoints of `Iθ`, a
null set, so the `θ`-integrals agree. -/
theorem fstar_eq_integral_fstarInt_fts (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    ∀ z, 0 < z → Work.Elliptic.Fstar F z = ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ := by
  intro z hz
  have hz' : (-1 : ℝ) < z := by linarith
  have hae : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  calc Work.Elliptic.Fstar F z
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), F z θ * Work.Elliptic.sinCos2 θ := by
        rw [Work.Elliptic.Fstar]
        exact (MeasureTheory.setIntegral_congr_set hae).symm
    _ = ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
        rw [hsol.1 z hz θ hθ.1 hθ.2]
    _ = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), FstarInt α Ψ z θ := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
        obtain ⟨hθ0, hθ1⟩ := hθ
        exact bslOp_mul_sinCos2_eq α Ψ
          (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩))
          ((hasDerivAt_slice_pth_of_smoothNbhd hsm hz' (by linarith)
            (by linarith [Real.pi_pos])).differentiableAt)
    _ = ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ :=
        MeasureTheory.setIntegral_congr_set hae

/-- **`F_*(F)` is `C^∞` on `(0,∞)`** for the source `F` of a solution of (PolarBSL) with `Ψ`
smooth on a neighbourhood of the closed quadrant. -/
theorem fstar_smooth_of_sol_fts (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) := by
  intro m
  have hI : Work.Spaces.SmoothNbhd (FstarInt α Ψ) := fstarInt_smoothNbhd_fts α Ψ hsm
  have hbig : ContDiffOn ℝ ∞
      (fun z => ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ * (1 : ℝ)) (Set.Ioi (-1)) :=
    Work.FTS.EllipticEst.contDiffOn_infty_integral_Itheta_Ioi_neg_one (FstarInt α Ψ)
      (fun _ : ℝ => (1 : ℝ)) hI continuousOn_const
  have hmono : ContDiffOn ℝ m
      (fun z => ∫ θ in Work.Spaces.Iθ, FstarInt α Ψ z θ * (1 : ℝ)) (Set.Ioi 0) :=
    (contDiffOn_infty.mp hbig m).mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))
  refine hmono.congr ?_
  intro z hz
  simpa only [mul_one] using fstar_eq_integral_fstarInt_fts α F Ψ hsm hsol z hz

/-- **The algebra of the orthogonality condition.**  If the straightened solution
`Ψ̂ = Ψ + Gsing α F · sin 2θ` is orthogonal to `sinθcos²θ` (`OrthCond Ψ̂`), then the angular
moment the condition computes forces `Gsing α F = -(15/4) F_*(Ψ)`, and since
`Gsing = -(1/(4α)) L₁₂(F) + Ḡ` this identifies `L₁₂(F)`:

  `L₁₂(F)(z) = 15α F_*(Ψ)(z) + 4α Ḡ(α,F)(z)`  for `z > 0`.

The only integral input is the value `∫_0^{π/2} sin 2θ · sinθcos²θ dθ = 4/15`
(`Work.Elliptic.integral_sin_two_mul_sinCos2`). -/
theorem L12_eq_of_orth {α : ℝ} (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.Spaces.SmoothNbhd Ψ)
    (hOrth : Work.Elliptic.OrthCond
      (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) :
    ∀ z, 0 < z →
      Work.Elliptic.L12 F z = 15 * α * Work.Elliptic.Fstar Ψ z + 4 * α * Work.Elliptic.Gbar α F z := by
  have hsplit : ∀ z, 0 < z →
      Work.Elliptic.Fstar (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z
        = Work.Elliptic.Fstar Ψ z + Work.Elliptic.Gsing α F z * (4 / 15) := by
    intro z hz
    have hslice : ContinuousOn (fun θ : ℝ => Ψ z θ) Work.Spaces.Iθ :=
      continuousOn_slice_of_smoothNbhd hΨ (by linarith)
    have hf : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      (hslice.mul continuous_sinCos2_fts.continuousOn).integrableOn_compact isCompact_Icc
    have hg : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
      have hcont : Continuous fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ := by
        unfold Work.Elliptic.sinCos2
        fun_prop
      exact hcont.continuousOn.integrableOn_compact isCompact_Icc
    simp only [Work.Elliptic.Fstar]
    rw [show (fun θ => (Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
          * Work.Elliptic.sinCos2 θ)
        = (fun θ => Ψ z θ * Work.Elliptic.sinCos2 θ
            + Work.Elliptic.Gsing α F z * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)) from by
      funext θ; ring]
    rw [MeasureTheory.integral_add hf (hg.const_mul _), MeasureTheory.integral_const_mul,
      Work.Elliptic.integral_sin_two_mul_sinCos2]
  intro z hz
  have h0 := hOrth z
  rw [hsplit z hz] at h0
  have hgs : Work.Elliptic.Gsing α F z = -(15 / 4) * Work.Elliptic.Fstar Ψ z := by
    have h : Work.Elliptic.Gsing α F z * (4 / 15) = -Work.Elliptic.Fstar Ψ z := by linarith
    linarith [h]
  have hdef : Work.Elliptic.Gstar α F z = -(1 / (4 * α)) * Work.Elliptic.L12 F z := rfl
  have hdef2 : Work.Elliptic.Gsing α F z
      = Work.Elliptic.Gstar α F z + Work.Elliptic.Gbar α F z := rfl
  rw [hdef2, hdef] at hgs
  have hα0 : α ≠ 0 := ne_of_gt hα
  have h1 : -(1 / (4 * α)) * Work.Elliptic.L12 F z
      = -(15 / 4) * Work.Elliptic.Fstar Ψ z - Work.Elliptic.Gbar α F z := by linarith
  have h2 : -(4 * α) * (-(1 / (4 * α)) * Work.Elliptic.L12 F z)
      = Work.Elliptic.L12 F z := by
    field_simp
  have h3 : -(4 * α) * (-(15 / 4) * Work.Elliptic.Fstar Ψ z - Work.Elliptic.Gbar α F z)
      = 15 * α * Work.Elliptic.Fstar Ψ z + 4 * α * Work.Elliptic.Gbar α F z := by
    field_simp
    ring
  calc Work.Elliptic.L12 F z
      = -(4 * α) * (-(1 / (4 * α)) * Work.Elliptic.L12 F z) := h2.symm
    _ = -(4 * α) * (-(15 / 4) * Work.Elliptic.Fstar Ψ z
          - Work.Elliptic.Gbar α F z) := by rw [h1]
    _ = 15 * α * Work.Elliptic.Fstar Ψ z + 4 * α * Work.Elliptic.Gbar α F z := h3

/-- A function of `z` which is `C^n` on `(0,∞)`, as a function of `(z,θ)`, is `C^n` on the
open quadrant. -/
theorem contDiffOn_comp_fst_Ioi {g : ℝ → ℝ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0)) (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => g p.1) Work.FTS.EllipticEst.Q0 := by
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => g p.1) Work.FTS.EllipticEst.Q0 := by
    simpa [Function.comp_def] using (contDiffOn_infty.mpr hg).comp contDiffOn_fst
      (fun p hp => (mem_Q0.mp hp).1)
  exact contDiffOn_infty.mp h n

/-- `(z,θ) ↦ sin 2θ` is `C^n` on the open quadrant. -/
theorem contDiffOn_sin_two_snd (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 := by
  have h : ContDiff ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) := by fun_prop
  exact h.contDiffOn

/-- **Smoothness of the residual `EllResid α F Ψ = Ψ - (1/(4α)) sin 2θ · L₁₂(F)` on the open
quadrant**: both `Ψ` (`SmoothNbhd`, hence smooth on the open quadrant) and
`(z,θ) ↦ sin 2θ · L₁₂(F)(z)` (`L₁₂(F)` being `C^∞` on `(0,∞)`) are `C^∞` there. -/
theorem smoothOpen_pthIter2_EllResid (α : ℝ) (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.Spaces.SmoothNbhd Ψ)
    (hL12sm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.L12 F) (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have hψ : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ))
      Work.FTS.EllipticEst.Q0 := by
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
      (Work.FTS.EllipticEst.RPFresh.smoothOpen_pthIter
        (Work.FTS.EllipticEst.RPFresh.smoothOpen_of_smoothNbhd hΨ) 2) n
  have hL12 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Elliptic.L12 F p.1)
      Work.FTS.EllipticEst.Q0 := contDiffOn_comp_fst_Ioi hL12sm n
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := contDiffOn_sin_two_snd n
  have hterm : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      (1 / α) * (Real.sin (2 * p.2) * Work.Elliptic.L12 F p.1))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul ((hsin.mul hL12).congr fun p _ => by ring)
  have hsum := hψ.add hterm
  refine hsum.congr fun p hp => ?_
  obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp hp
  exact pthIter2_EllResid_pointwise α hα hΨ hz hθ0 hθ1

/-- **Honesty (and smoothness) of `∂_θθ` of the residual of Theorem `RemovingL12`.**

With `W = EllResid α F Ψ = Ψ - (1/(4α)) sin 2θ · L₁₂(F)` and `Ψ̂ = Ψ + Gsing α F · sin 2θ`, the
orthogonality hypothesis `OrthCond Ψ̂` forces `L₁₂(F)(0) = 0`: evaluating the angular moment at
`z = 0` gives `0 = ∫_θ Ψ̂(0,θ) sinθcos²θ dθ = (Gsing α F 0)·(4/15)`, and `HkMem α k Ψ` forces
`Ψ(0,θ) = 0`.  Consequently `∂_θθW` vanishes at `z = 0` like `L₁₂(F)(z) = O(z^{3/2+})` and its
weighted `ℋ^k`-integrand is honest — this is the hypothesis that the subadditivity
`HkNorm_add_fts` needs in order to transfer `∂_θθ` across the identity

  `∂_θθW = ∂_θθΨ + (1/α) · sin 2θ · L₁₂(F)`   (resp.  `∂_θθΨ̂ = ∂_θθW - 4 (Ḡ·sin 2θ)`).

The `∂_θθΨ` half is `EllHyp.memDth2`, so the content is `HkMem` of `sin 2θ · L₁₂(F)`
(the sibling target `Cert/L12Sin_mem`) — equivalently: `D_z(L₁₂ F) = -3 F_*(F)`
(`Work.Elliptic.L12Iterate`), so all the `D_z`-iterates of `L₁₂(F)` are angular moments of
`F` (`Cert/HkMem_Fstar_sin`-type content), and the only new input is the *level-zero* weighted
integral `∫ (L₁₂(F)(z))² w(z)² dz < ∞`, the Hardy inequality
`Work.Coercivity.L12_w_sq_le` (proved: `∫ U²w² ≤ 107 ∫ A²w²` for the tail integral `U` with
angular average `A`), applied with `L₁₂(F)(0) = 0` (from `OrthCond Ψ̂`, via
`Work.Elliptic.L12_values`); it needs the *open-quadrant* analogue of its hypotheses
(`SmoothNbhd F` is not available from `EllHyp`, cf. `Cert/GbarSin/SmoothOpen_bslOp`).
Smoothness is `SmoothOpen`-congruence from `HasDerivAt_L12_of_Fstar_facts`. -/
theorem HkMem_pthIter2_EllResid (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ)
    (hOrth : Work.Elliptic.OrthCond
      (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) :
    Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) ∧
      (∀ n : ℕ, ContDiffOn ℝ n
        (Function.uncurry (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) := by
  have hα1 : α ≤ 1 := by linarith
  have hα0 : α ≠ 0 := ne_of_gt hα
  -- ### the analytic inputs
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    fstar_smooth_of_sol_fts α F Ψ hHyp.smoothNbhd hHyp.sol
  have hFint : MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) :=
    FstarDivIntegrableOfSolHk α k F Ψ hα hHyp.smoothNbhd hHyp.sol hHyp.memF
  have hL12sm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.L12 F) (Set.Ioi 0) :=
    L12_contDiffOn_Ioi F hFsm hFint
  have hFstarΨsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar Ψ) (Set.Ioi 0) :=
    contDiffOn_fstar_of_smoothNbhd Ψ hHyp.smoothNbhd
  have hGbarsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0) :=
    Gbar_contDiffOn_Ioi α F hα hFsm hFint
  -- ### the orthogonality identity identifies `L₁₂(F)`
  have hL12eq : ∀ z, 0 < z → Work.Elliptic.L12 F z
      = 15 * α * Work.Elliptic.Fstar Ψ z + 4 * α * Work.Elliptic.Gbar α F z :=
    fun z hz => L12_eq_of_orth hα hHyp.smoothNbhd hOrth z hz
  -- ### smoothness of the two separated pieces
  have hsu : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.RPFresh.smoothOpen_radial_sin hFstarΨsm
  have hsv : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.RPFresh.smoothOpen_radial_sin hGbarsm
  -- ### the two separated memberships, from the certificates
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.RPFresh.smoothOpen_of_smoothNbhd hHyp.smoothNbhd
  have hmem_u : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin_open α k Ψ hα hα1 hΨso hHyp.memPsi
  have hmem_v : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.HkMem_Gbar_sin α k F Ψ hα hα4 hHyp
  -- ### the `15·(F_*·sin 2θ) + 4·(Ḡ·sin 2θ)` combination
  have hmem_T : Work.Spaces.HkMem α k (fun z θ =>
      15 * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))
        + 4 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.RPFresh.HkMem_add_open α k
      (Work.FTS.EllipticEst.RPFresh.smoothOpen_const_mul 15 hsu)
      (Work.FTS.EllipticEst.RPFresh.smoothOpen_const_mul 4 hsv)
      (Work.FTS.LocData.HkMem_const_mul α k 15 hmem_u)
      (Work.FTS.LocData.HkMem_const_mul α k 4 hmem_v)
  -- ### the term `(1/α)·(sin 2θ · L₁₂(F))`, the same function on the open quadrant
  have hS : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / α) * (Real.sin (2 * θ) * Work.Elliptic.L12 F z)) :=
    Work.FTS.EllipticEst.RPFresh.smoothOpen_const_mul (1 / α)
      (Work.FTS.EllipticEst.RPFresh.smoothOpen_congr
        (Work.FTS.EllipticEst.RPFresh.smoothOpen_radial_sin hL12sm)
        (fun z θ _ _ _ => by ring))
  have hmem_S : Work.Spaces.HkMem α k
      (fun z θ => (1 / α) * (Real.sin (2 * θ) * Work.Elliptic.L12 F z)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k hmem_T
      (fun z hz θ hθ => by
        rw [hL12eq z hz]
        field_simp
        try ring)
  -- ### add `∂_θθΨ`
  have hψso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.RPFresh.smoothOpen_pthIter hΨso 2
  have hmem_G : Work.Spaces.HkMem α k (fun z θ => Work.Spaces.pthIter 2 Ψ z θ
      + (1 / α) * (Real.sin (2 * θ) * Work.Elliptic.L12 F z)) :=
    Work.FTS.EllipticEst.RPFresh.HkMem_add_open α k hψso hS hHyp.memDth2 hmem_S
  -- ### transfer to the residual through the pointwise identity
  have hWsmoothOpen : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) :=
    smoothOpen_pthIter2_EllResid α hα hHyp.smoothNbhd hL12sm
  refine ⟨?_, (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hWsmoothOpen⟩
  exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k hmem_G
    (fun z hz θ hθ =>
      (pthIter2_EllResid_pointwise α hα hHyp.smoothNbhd hz hθ.1 hθ.2).symm)

end

end Work.FTS.EllipticEst.Cert
