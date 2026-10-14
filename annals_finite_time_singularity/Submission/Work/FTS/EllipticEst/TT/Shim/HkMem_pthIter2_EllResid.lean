import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.Shim.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.TT.Shim.FstarIterateIntegrable
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK

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

/-- A function of `z` which is `C^∞` on `(0,∞)`, viewed as a function of `(z,θ)`, is `C^∞` on
the open quadrant. -/
theorem smoothOpen_radial {g : ℝ → ℝ} (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => g z) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  change ContDiffOn ℝ n (fun p : ℝ × ℝ => g p.1) Work.FTS.EllipticEst.Q0
  exact contDiffOn_infty.mp ((contDiffOn_infty.mpr hg).comp contDiffOn_fst
    fun p hp => (mem_Q0.mp hp).1) n










/-- `(z,θ) ↦ sin 2θ` is `C^n` on the open quadrant. -/
theorem contDiffOn_sin_two_snd (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 := by
  have h : ContDiff ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) := by fun_prop
  exact h.contDiffOn



end

end Work.FTS.EllipticEst.Cert
