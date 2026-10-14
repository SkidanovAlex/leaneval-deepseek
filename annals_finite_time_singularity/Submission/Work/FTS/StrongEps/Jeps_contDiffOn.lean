import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Have
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers
import Submission.Work.FTS.EllipticEst.TT.Shim.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.TT.Shim.HkMem_pthIter2_EllResid
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.HkMem_pthIter2_EllResid =====
section

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

end

end Work.FTS.EllipticEst.Cert
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Straight_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Integrability of the square of the angular moment -/

/-- On the domain `(0,∞)` the radial weight satisfies `1 ≤ w`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have h : Work.Spaces.w z = (1 + 1 / z) ^ 2 := by
    rw [Work.Spaces.w]
    field_simp
    ring
  rw [h]
  nlinarith [one_div_pos.mpr hz]






/-! ## Smoothness of the two radial functions used in the ODE argument -/



/-! ## `F_*(D_zΨ)²` for the data of `EllHyp` -/

/-- `z² F_*(∂_z²Ψ)(z) = F_*(z² ∂_z²Ψ)(z)`: the radial factor is constant in `θ`. -/
theorem zsq_mul_Fstar {g : ℝ → ℝ → ℝ} (z : ℝ) :
    z ^ 2 * Work.Elliptic.Fstar g z
      = Work.Elliptic.Fstar (fun z' θ => z ^ 2 * g z' θ) z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, ← MeasureTheory.integral_const_mul]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)



/-! ## The moment identity -/




/-! ## Weighted integrability of the angular moments

The estimates below are the *weighted* (`w²`) versions of `Fstar_sq_integrable`; they are what the
membership statements `R·sin 2θ ∈ ℋ^k` need, since the `ℋ^k`-integrand of a separated function
`R(z)·sin 2θ` is dominated by `w(z)²·Σ_{j≤k}(D_z^jR)(z)²` times an angular profile. -/

/-- `z ↦ w(z)²` is continuous on `(0,∞)`. -/
theorem continuousOn_w_sq : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z : ℝ => (1 + z) ^ 4 / z ^ 4 := by
    funext z
    rw [Work.Spaces.w]
    field_simp
  rw [hfun]
  refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun z hz => ?_)
  exact pow_ne_zero 4 (ne_of_gt (Set.mem_Ioi.mp hz))



/-! ## Weighted moment bounds for the radial iterates of the straightened pieces

These are the inputs of the membership statements `R·sin 2θ ∈ ℋ^k`: the sharp form of
`Work.FTS.EllipticEst.Cert.HkMem_radialSin_of_bound` needs the integrability of the weighted
radial iterates of `R`, and for the radial pieces `R` occurring here (`F_*(F)`,
`F_*(D_z^jΨ)`, …) that integrability comes from the weighted moment bounds above. -/

/-- `D_z^jΨ` is smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_DzIter {Ψ : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd Ψ) (j : ℕ) :
    Work.Spaces.SmoothNbhd (Work.Spaces.DzIter j Ψ) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ]
      exact Work.FTS.EllipticEst.Cert.smoothNbhd_mul' Work.FTS.EllipticEst.Cert.smoothNbhd_fst
        (Work.Spaces.smoothNbhd_pzIter ih 1)







end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.aemeasurable_L12_fam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set
open scoped Real

namespace Work.FTS.StrongEps.EpsE4Thr.JepsJoint


end Work.FTS.StrongEps.EpsE4Thr.JepsJoint
end
-- ===== merged: Submission.Work.FTS.StrongEps.Jeps_contDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Convolution
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-! ## The kernel `Jker ρ ε` -/

/-- The rescaled kernel `Jker ρ ε` is `C^n` as soon as `ρ` is. -/
theorem contDiff_Jker (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) (ε : ℝ) (n : ℕ) :
    ContDiff ℝ n (Jker ρ ε) := by
  have h1 : ContDiff ℝ n (fun p : ℝ × ℝ => ρ (ε⁻¹ • p)) :=
    (hρ.smooth n).comp (ContDiff.const_smul (ε⁻¹) (contDiff_id (n := (n : WithTop ℕ∞))))
  have h2 : ContDiff ℝ n (fun p : ℝ × ℝ => (ε⁻¹ ^ 2) * ρ (ε⁻¹ • p)) := by
    simpa only [smul_eq_mul] using h1.const_smul (ε⁻¹ ^ 2)
  exact h2

/-- The rescaled kernel `Jker ρ ε` is compactly supported: its support is contained in the
square of half-side `|ε|` (the support condition `IsMollKernel.support` holds on the closed unit
ball). -/
theorem hasCompactSupport_Jker (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (Jker ρ ε) := by
  refine HasCompactSupport.intro (K := Set.Icc (-|ε|) |ε| ×ˢ Set.Icc (-|ε|) |ε|)
    (isCompact_Icc.prod isCompact_Icc) ?_
  rintro ⟨x1, x2⟩ hx
  have hx' : ¬(-|ε| ≤ x1 ∧ x1 ≤ |ε|) ∨ ¬(-|ε| ≤ x2 ∧ x2 ≤ |ε|) := by
    simpa only [Set.mem_prod, Set.mem_Icc, not_and_or] using hx
  have aux : ∀ y : ℝ, ¬(-|ε| ≤ y ∧ y ≤ |ε|) → |ε| < |y| := by
    intro y hy
    rw [not_and_or, not_le, not_le] at hy
    rcases hy with h | h
    · have hy0 : y < 0 := by linarith [abs_nonneg ε, h]
      have : |y| = -y := abs_of_neg hy0
      linarith
    · have hy0 : 0 < y := by linarith [abs_nonneg ε, h]
      have : |y| = y := abs_of_nonneg hy0.le
      linarith
  have hbig : |ε| < |x1| ∨ |ε| < |x2| := by
    rcases hx' with h | h
    · exact Or.inl (aux x1 h)
    · exact Or.inr (aux x2 h)
  have habs_aux : ∀ y : ℝ, |ε| < |y| → (1 : ℝ) < (ε⁻¹ * y) ^ 2 := by
    intro y hy
    have h1 : (1 : ℝ) < |ε⁻¹ * y| := by
      rw [abs_mul, abs_inv, abs_of_pos hε, ← inv_mul_cancel₀ (ne_of_gt hε)]
      simpa [abs_of_pos hε] using mul_lt_mul_of_pos_left hy (inv_pos.mpr hε)
    have h2 : ((1 : ℝ)) ^ 2 < (ε⁻¹ * y) ^ 2 := by
      rw [sq_lt_sq]
      simpa using h1
    simpa using h2
  have hρ0 : ρ (ε⁻¹ • (x1, x2)) = 0 := by
    by_contra hne
    have hle := hρ.moll.support _ hne
    simp only [Prod.smul_mk, smul_eq_mul] at hle
    have hsum : (1 : ℝ) < (ε⁻¹ * x1) ^ 2 + (ε⁻¹ * x2) ^ 2 := by
      rcases hbig with h | h
      · nlinarith [habs_aux x1 h, sq_nonneg (ε⁻¹ * x2)]
      · nlinarith [habs_aux x2 h, sq_nonneg (ε⁻¹ * x1)]
    exact absurd hle (not_le.mpr hsum)
  simp only [Jker, hρ0, mul_zero]

/-! ## The log-coordinate map -/

/-- The log-coordinate map `p ↦ (log p.1, log (tan p.2))` is `C^∞` on the open quadrant. -/
theorem contDiffOn_logMap (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => (sOf p.1, zetaOf p.2)) Quad := by
  have htan : ContDiffOn ℝ n Real.tan (Set.Ioo 0 (π / 2)) := fun x hx =>
    (Real.contDiffAt_tan.mpr (ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩))).contDiffWithinAt
  refine ContDiffOn.prodMk ?_ ?_
  · exact Real.contDiffOn_log.comp contDiffOn_fst (fun p hp => by simpa using hp.1.ne')
  · exact Real.contDiffOn_log.comp (htan.comp contDiffOn_snd (fun p hp => hp.2))
      (fun p hp => by
        simp only [mem_compl_iff, mem_singleton_iff]
        exact ne_of_gt (Real.tan_pos_of_pos_of_lt_pi_div_two hp.2.1 hp.2.2))

/-! ## `J_ε` is the convolution in the log coordinates -/

/-- On the open quadrant, `J_ε f` is the convolution of `logPull f` with the kernel `Jker ρ ε`,
evaluated at the log coordinates `(s, ζ) = (log z, log tan θ)`. -/
theorem Jeps_eq_conv (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Jeps ρ ε f z θ
      = (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull f) (sOf z, zetaOf θ) := by
  rw [Jeps_eq_integral ρ ε f hz hθ, MeasureTheory.convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [show (sOf z, zetaOf θ) - p = (sOf z - p.1, zetaOf θ - p.2) from Prod.mk_sub_mk _ _ _ _,
    ← logPull_shift f hz hθ]

/-! ## The main statement -/

theorem Jeps_contDiffOn (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : MeasureTheory.LocallyIntegrable (logPull f) volume) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Jeps ρ ε f)) Quad := by
  intro n
  have hconv : ContDiff ℝ n
      (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull f) :=
    (hasCompactSupport_Jker ρ hρ hε).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (contDiff_Jker ρ hρ ε n) hf
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull f) (sOf p.1, zetaOf p.2))
      Quad :=
    hconv.comp_contDiffOn (contDiffOn_logMap n)
  refine hcomp.congr (fun p hp => ?_)
  exact Jeps_eq_conv ρ ε f hp.1 hp.2

end Work.FTS.StrongEps
end
end
