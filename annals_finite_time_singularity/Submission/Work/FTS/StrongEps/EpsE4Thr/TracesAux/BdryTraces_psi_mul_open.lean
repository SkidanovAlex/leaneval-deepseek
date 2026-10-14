import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.ConstructionInstance.Reduced =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- **The vorticity of the constructed solution**, as a *definition* from the profile/modulation
data: `ω(x,t) = λ̄(t)⁻¹·χ(ρ(x)/L)·F(ρ(x)^p/λ̄(t), θ(x))·e_θ(x)`. -/
def solVort {α : NNReal} (D : ProfileData α) : R3 → ℝ → R3 :=
  selfSimVort (profExp α) D.g D.L D.lam

theorem solVort_apply {α : NNReal} (D : ProfileData α) (x : R3) (t : ℝ) :
    solVort D x t = (D.lam t)⁻¹ •
      (Work.Stability.chi (Work.Cyl.rho x / D.L) •
        omegaSz (profExp α) D.g (Work.Cyl.rho x ^ profExp α / D.lam t) x) :=
  rfl

/-- **The datum identity (finding G)**: with the design's normalisation `λ̄(0) = 1`, the ansatz at
`t = 0` is exactly the `St1` cut-off datum, `solVort P · 0 = ω₀ = χ(ρ/L)·omegaS p g`.  This is the
consistency condition that ties the pointwise ansatz to the datum of the maximal solution; without
`hlam0` the two differ and the interface would be inconsistent. -/
theorem solVort_zero_eq_cutDatum {α : NNReal} (D : ProfileData α) :
    ∀ x : R3, solVort D x 0 = omega₀ (profExp α) D.g D.L x := by
  intro x
  rw [solVort_apply, D.hlam0, omega₀_apply, omegaS_eq_omegaSz, inv_one, one_smul,
    div_one]

/-- **The perturbation bound**: `|g| ≤ Cg` follows from the `ℋ²`-bound of the construction
(`abs_le_of_linf_H2`). -/
theorem bdd_g {α : NNReal} (D : ProfileData α) :
    ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |D.g z θ| ≤ D.Cg := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  intro z θ hz hθ
  exact le_trans
    (abs_le_of_linf_H2 hp hp1 D.hsmooth D.hvt D.hdec D.hmem z θ hz hθ) D.hCgbig

/-- **`hSupp`**: the cut-off makes the vorticity vanish outside `B(0,2L) ⊆ B(0,R)`. -/
theorem solVort_supp {α : NNReal} (D : ProfileData α) :
    ∀ t : ℝ, ∀ y : R3, solVort D y t ≠ 0 → y ∈ Metric.closedBall 0 D.R :=
  selfSimVort_support D.hL D.hRbig

/-- **`hBdd`**: `λ̄(t)·‖ω(x,t)‖ ≤ M`. -/
theorem solVort_bdd {α : NNReal} (D : ProfileData α) :
    ∀ t ∈ preWindow D.T, ∀ y : R3, D.lam t * ‖solVort D y t‖ ≤ D.M := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  intro t ht y
  exact le_trans (selfSimVort_bdd hp hp1 D.hCg (bdd_g D) D.hL (D.hlam t ht) y) D.hMprof

/-- **`hBddDt`**: `λ̄(t)²·‖∂ₜω(x,t)‖ ≤ M₁`. -/
theorem solVort_bddDt {α : NNReal} (D : ProfileData α) :
    ∀ t ∈ preWindow D.T, ∀ y : R3,
      (D.lam t) ^ 2 * ‖timeDeriv (solVort D) y t‖ ≤ D.M₁ := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  intro t ht y
  exact le_trans
    (bddDt_selfSimVort hp hp1 (bdd_g D) D.hg2 D.hgdiff D.hK D.hlam D.hlamdif D.hlamd ht y)
    D.hM₁big

/-- **`hansatz` (`St5`)**: at every `t ∈ [0,T)` there is a point where
`λ̄(t)·‖ω(x,t)‖ ≥ c₀star α · α`.  The witness is the maximising profile scale `z = 1`; the
cut-off is transparent there because `λ̄(t)^{1/p} < (2T)^{1/p} ≤ L`. -/
theorem solVort_hansatz {α : NNReal} (D : ProfileData α) :
    ∀ t ∈ Set.Ico 0 D.T, ∃ x : R3,
      c₀star α * (α : ℝ) ≤ D.lam t * ‖solVort D x t‖ := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  intro t ht
  have htpre : t ∈ preWindow D.T := ⟨by linarith [ht.1], ht.2⟩
  have hlt : 0 < D.lam t := D.hlam t htpre
  have hle2 : D.lam t ≤ 2 * D.T := by
    have h := D.hlam_le t ht
    linarith [h, ht.1, D.hT]
  have hsL : (D.lam t) ^ (1 / profExp α) ≤ D.L := by
    have h1 : 0 < 1 / profExp α := by positivity
    calc (D.lam t) ^ (1 / profExp α) ≤ (2 * D.T) ^ (1 / profExp α) :=
          Real.rpow_le_rpow hlt.le hle2 h1.le
      _ ≤ D.L := D.hLbig
  obtain ⟨x, hxρ, hx⟩ := exists_omegaSz_low_radius hp hp1 (bdd_g D) D.hsmall hlt hsL
  refine ⟨x, ?_⟩
  have hchi : Work.Stability.chi (Work.Cyl.rho x / D.L) = 1 := by
    refine Work.Stability.chi_eq_one ?_
    rw [abs_of_nonneg (div_nonneg (Work.Cyl.rho_nonneg x) D.hL.le), div_le_one D.hL]
    exact hxρ
  have heq : D.lam t * ‖solVort D x t‖
      = ‖omegaSz (profExp α) D.g (Work.Cyl.rho x ^ profExp α / D.lam t) x‖ := by
    rw [solVort_apply, mul_norm_inv_smul hlt, hchi, one_smul]
  rw [heq]
  have hc : c₀star α * (α : ℝ)
      = profExp α * Work.Spaces.Gam (profExp α) (Real.pi / 4)
          / (4 * Work.Spaces.c (profExp α)) := by
    rw [c₀star, profExp]; ring
  rw [hc]
  exact hx

/-- **`hDivω`**: the vorticity is the divergence-free swirl field of the `Cyl` dictionary. -/
theorem solVort_div {α : NNReal} (D : ProfileData α) :
    ∀ t ∈ preWindow D.T, FiniteTimeSingularity.div (solVort D · t) = 0 := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  intro t ht
  funext x
  exact div_selfSimVort hp hp1 D.hvt D.hsmooth D.hL (D.hlam t ht) x

/-- **`hωcont`**: the vorticity is continuous on the core. -/
theorem solVort_cont {α : NNReal} (D : ProfileData α) :
    ContinuousOn (Function.uncurry (solVort D))
      (Work.StabilityFar.coreRegion (D.R + 1) ×ˢ preWindow D.T) := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  exact continuousOn_selfSimVort hp hp1 D.hvt D.hquad0 D.hsmooth D.hL D.hlam D.hlamdif
    (R := D.R + 1) (by linarith [D.hR])

/-- **`hTh` in strip form**: on every strip `window S`, `0 < S`, `S + 1 < T`, the vorticity is
`α`-Hölder in time on the support ball, with a strip-dependent constant. -/
theorem solVort_timeHolder {α : NNReal} (D : ProfileData α) :
    ∀ S : ℝ, 0 < S → S + 1 < D.T → ∃ H : ℝ, 0 ≤ H ∧
      Work.StabilityFar.TimeHolderOnBall (α : ℝ) (solVort D) D.R S H := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  intro S hS hST
  have h := timeHolderOnBall_selfSimVort (p := profExp α) hp hp1 (bdd_g D) D.hg2 D.hgdiff
    (L := D.L) (lam := D.lam) (T := D.T) D.hK D.hlam D.hlamdif D.hlamd (R := D.R) D.hR S hS hST
  simpa only [solVort, profExp_div_three] using h

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.holder_omegaS_of_data =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- The self-similar vorticity `omegaS (3α) g` is `α`-Hölder, from the *explicit* conditions on
the perturbation `g`: smoothness near the closed quadrant, vanishing at `z = 0` and on the angular
boundaries, and the three uniform bounds — angular vanishing `|g| ≤ Cv·Γ(α,θ)`, radial modulus
`|g(z,θ)-g(z',θ)| ≤ Lg|z-z'|^α`, angular modulus `|g(z,θ)-g(z,θ')| ≤ Lθ|θ-θ'|^α`.  The `F_*` part
is handled by `Defs.Fstar_abs_le` and the explicit form of `Γ`. -/
theorem holder_omegaS_of_data {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1/3) {g : ℝ → ℝ → ℝ}
    {Cv Lg Lθ : ℝ} (hCv : 0 ≤ Cv) (hLg : 0 ≤ Lg) (hLθ : 0 ≤ Lθ)
    (hvt : Work.Spaces.VanishTheta g)
    (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hquad1 : ∀ θ : ℝ, Work.Spaces.pz g 0 θ = 0)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ)
    (hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ Lg * |z - z'| ^ α)
    (hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ α)
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) :
    Holder ⟨α, hα.le⟩ (Work.ConstructionInstance.omegaS (3 * α) g) := by
  have hα1 : α ≤ 1 := by linarith
  set ĝ : R3 → ℝ := fun x => g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|) with hĝ
  have hĝ_holder : Holder ⟨α, hα.le⟩ ĝ :=
    holder_gComp hα hα13 hCv hLg hLθ hvt hquad0 hquad1 hvan hzk hzth hsm
  obtain ⟨Ca, hCa0, hCa⟩ :=
    gComp_abs_le hα hα13 hCv hLg hLθ hvt hquad0 hquad1 hvan hzk hzth hsm
  have hE_holder : Holder ⟨α, hα.le⟩ (fun x : R3 => ĝ x • Work.Cyl.eTheta x) :=
    holder_smul_eTheta hα hα1 hCa0 hĝ_holder hCa
  obtain ⟨Cω, hCω⟩ := holder_omegaStar (β := α) hα hα1
  have hS_holder : Holder ⟨α, hα.le⟩
      (fun x : R3 => (3 * α / Work.Spaces.c (3 * α)) • omegaStar α x) :=
    ⟨Cω * ‖(3 * α / Work.Spaces.c (3 * α))‖₊, HolderWith.smul _ hCω⟩
  have hΦ_holder : Holder ⟨α, hα.le⟩
      (fun x : R3 => (3 * α / Work.Spaces.c (3 * α)) • omegaStar α x
        + ĝ x • Work.Cyl.eTheta x) := by
    obtain ⟨C₁, h₁⟩ := hS_holder
    obtain ⟨C₂, h₂⟩ := hE_holder
    exact ⟨C₁ + C₂, HolderWith.add h₁ h₂⟩
  have hhalf : ∀ x : R3, 0 ≤ x 2 → omegaS (3 * α) g x
      = (3 * α / Work.Spaces.c (3 * α)) • omegaStar α x + ĝ x • Work.Cyl.eTheta x := by
    intro x hx
    have hθ : 0 ≤ Work.Cyl.theta x := theta_nonneg_of_axial_nonneg hx
    have hAom : Aom α x = A0 α x := by
      rw [Aom, cSign, ite_eq_left hx, one_mul]
    have hGF : Gamma α (Work.Cyl.theta x) * Work.FM.Fstar (Work.Cyl.rho x ^ (3 * α))
        = A0 α x := by
      rw [← hAom, Gamma_mul_Fstar_eq_Aom α hα x]
    have hF : Work.Construction.Fstar (3 * α) (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.theta x)
        = (3 * α / Work.Spaces.c (3 * α)) * A0 α x := by
      have hGam : Work.Spaces.Gam (3 * α) (Work.Cyl.theta x) = Gamma α (Work.Cyl.theta x) := by
        rw [Work.Spaces.Gam, Gamma, show (3 * α) / 3 = α by ring]
      rw [Work.Construction.Fstar, hGam]
      conv_rhs => rw [← hGF]
      ring
    have hĝx : ĝ x = g (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.theta x) := by
      rw [hĝ]; simp only; rw [abs_of_nonneg hθ]
    rw [omegaS_apply', profile_of_nonneg hθ, hF, hĝx, omegaStar_apply,
      Gamma_mul_Fstar_eq_Aom α hα x, hAom, smul_smul, ← add_smul]
  have hplane : ∀ x : R3, x 2 = 0 →
      (3 * α / Work.Spaces.c (3 * α)) • omegaStar α x + ĝ x • Work.Cyl.eTheta x = 0 := by
    intro x hx
    have hθ0 : Work.Cyl.theta x = 0 := by
      rw [Work.Cyl.theta, Work.Cyl.axial, hx]; simp
    have hA0 : A0 α x = 0 := by
      simp [A0, hx, Real.zero_rpow (ne_of_gt hα)]
    have hAom : Aom α x = 0 := by
      rw [Aom, cSign, ite_eq_left (le_of_eq hx.symm), one_mul, hA0]
    have hĝ0 : ĝ x = 0 := by
      rw [hĝ]; simp only; rw [hθ0, abs_zero]; exact hvt.1 _
    rw [omegaStar_apply, Gamma_mul_Fstar_eq_Aom α hα x, hAom, hĝ0]
    simp
  have hodd : ∀ x : R3, omegaS (3 * α) g (Work.Cyl.reflZ x) = - omegaS (3 * α) g x := by
    intro x
    have hrho : Work.Cyl.rho (Work.Cyl.reflZ x) = Work.Cyl.rho x := by
      simp [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial, Work.Cyl.reflZ]
    have hth : Work.Cyl.theta (Work.Cyl.reflZ x) = - Work.Cyl.theta x := by
      simp [Work.Cyl.theta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.axial, Work.Cyl.reflZ,
        neg_div, Real.arctan_neg]
    have he : Work.Cyl.eTheta (Work.Cyl.reflZ x) = Work.Cyl.eTheta x := by
      simp [Work.Cyl.eTheta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.angularVec, Work.Cyl.reflZ]
    rw [omegaS_apply', omegaS_apply', hrho, hth, he,
      profile_odd (by positivity : (3:ℝ) * α ≠ 0) (fun z => hvt.1 z), neg_smul]
  exact holder_of_half_odd (ω := omegaS (3 * α) g)
    (Φ := fun x : R3 => (3 * α / Work.Spaces.c (3 * α)) • omegaStar α x
      + ĝ x • Work.Cyl.eTheta x) hα hΦ_holder hhalf hodd hplane

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## The angular profiles -/

theorem continuous_angZ : Continuous angZ := by
  unfold angZ
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
    (fun θ => Or.inr (by rw [Work.Spaces.eta]; norm_num))

theorem angZ_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angZ θ := by
  rw [angZ]
  exact Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _

theorem angZ_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : angZ θ ≤ 1 := by
  rw [angZ]
  exact Real.rpow_le_one (FstarHkOpen.sin_two_nonneg hθ) (FstarHkOpen.sin_two_le_one θ)
    (by rw [Work.Spaces.eta]; norm_num)

theorem integrableOn_angZ : MeasureTheory.IntegrableOn angZ Work.Spaces.Iθ :=
  FstarHkOpen.integrableOn_Iθ_of_abs_le
    (continuous_angZ.continuousOn.aestronglyMeasurable
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc))
    (fun θ hθ => by rw [abs_of_nonneg (angZ_nonneg hθ)]; exact angZ_le_one hθ)

theorem continuousOn_angA (α : ℝ) (i : ℕ) :
    ContinuousOn (angA α i) (Set.Ioo 0 (π / 2)) := by
  have hslice : ContDiffOn ℝ ⊤ (Work.FTS.EllipticEst.sinProf i)
      (Set.Ioo (-1) (Real.pi / 2 + 1)) := FstarHkOpen.smoothSlice_sinProf i
  have hsp : ContinuousOn (Work.FTS.EllipticEst.sinProf i) (Set.Ioo 0 (π / 2)) :=
    hslice.continuousOn.mono
      (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
  have hsin : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.rpow_const
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn) ?_
    intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))
  change ContinuousOn (fun θ => (Work.FTS.EllipticEst.sinProf i θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Set.Ioo 0 (π / 2))
  exact (hsp.pow 2).mul hsin

theorem angA_nonneg (α : ℝ) (i : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angA α i θ := by
  rw [angA]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _)

theorem angA_le_angK (α : ℝ) (i : ℕ) (h1 : 1 ≤ Work.Spaces.gam α)
    (h2 : Work.Spaces.gam α ≤ 2) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    angA α i θ ≤ FstarHkOpen.angK i :=
  FstarHkOpen.angK_bound i (Work.Spaces.gam α) h1 h2 hθ

theorem integrableOn_angA (α : ℝ) (i : ℕ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (angA α i) Work.Spaces.Iθ := by
  have hgam1 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
  have hgam2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  refine FstarHkOpen.integrableOn_Iθ_of_abs_le (C := FstarHkOpen.angK i) ?_ ?_
  · rw [show (MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ
        = (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)) from
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm]
    exact (continuousOn_angA α i).aestronglyMeasurable measurableSet_Ioo
  · intro θ hθ
    rw [abs_of_nonneg (angA_nonneg α i hθ)]
    exact angA_le_angK α i hgam1 hgam2 hθ

/-! ## The crude bound for the slice integrand -/

/-- A crude bound for `HkExp α k R z` on `Iθ`: the angular factors `angZ` resp. `angA`
are replaced by their bounds `1` resp. `angK i`. -/
def sliceConst (k : ℕ) (R : ℝ → ℝ) (z : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1),
      (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2
            * FstarHkOpen.angK i
        else 0

/-- The constant of the domination `∫_θ HkIntegrand (F_*·sin 2θ) ≤ K ∫_θ HkIntegrand F`. -/
def sliceK (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * (π / 2) ^ 2 * (1 + ((k : ℝ) + 1) * FstarHkOpen.angKsum k) + 1



theorem continuousOn_HkExp (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z : ℝ) :
    ContinuousOn (fun θ => HkExp α k R z θ) (Set.Ioo 0 (π / 2)) := by
  unfold HkExp
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum _ fun i _ => ?_
    exact continuousOn_const.mul continuous_angZ.continuousOn
  · refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      exact continuousOn_const.mul (continuousOn_angA α i)
    · simp only [if_neg hc]
      exact continuousOn_const

theorem HkExp_le_sliceConst (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) :
    ∀ θ ∈ Work.Spaces.Iθ, HkExp α k R z θ ≤ sliceConst k R z := by
  have hgam1 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
  have hgam2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  intro θ hθ
  have hZ1 : angZ θ ≤ 1 := angZ_le_one hθ
  unfold HkExp sliceConst
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum fun i hi => ?_
    have h2 : 0 ≤ (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * angZ θ
        ≤ (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hZ1 h2
      _ = (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
  · refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc]
      have h2 : 0 ≤ (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (angA_le_angK α i hgam1 hgam2 hθ) h2
    · rw [if_neg hc, if_neg hc]

/-! ## Integrability of a slice, from continuity and boundedness -/

theorem integrableOn_slice_of_bound (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z : ℝ) (hz : 0 < z)
    (C : ℝ)
    (hcont : ContinuousOn (fun θ => HkExp α k R z θ) (Set.Ioo 0 (π / 2)))
    (hbnd : ∀ θ ∈ Set.Ioo 0 (π / 2), HkExp α k R z θ ≤ C) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k
        (fun z θ => R z * Real.sin (2 * θ)) z θ) Work.Spaces.Iθ := by
  have hcongr : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) z θ
        = HkExp α k R z θ :=
    fun θ hθ => HkIntegrand_radial_sin α k R z θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α k
      (fun z θ => R z * Real.sin (2 * θ)) z θ)
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) :=
    (hcont.aestronglyMeasurable measurableSet_Ioo).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => (hcongr θ hθ).symm)
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => C) (Set.Ioo 0 (π / 2)) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hle : ∀ᵐ θ ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))),
      ‖Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) z θ‖ ≤ C :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k _ z θ),
        hcongr θ hθ]
      exact hbnd θ hθ
  refine MeasureTheory.IntegrableOn.congr_set_ae (t := Set.Ioo 0 (π / 2))
    (MeasureTheory.Integrable.mono' hconst haesm hle) ?_
  exact MeasureTheory.Ioo_ae_eq_Icc.symm

/-! ## The explicit measurable majorant of the slice integral -/

/-- The a.e. value of the slice integral `z ↦ ∫_θ HkIntegrand α k (F_*·sin 2θ) z θ`:
the angular integrals are evaluated and the radial factors are the moments
`Bmom F i z = F_*(D_z^i F)(z)`. -/
def Psi (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (∫ θ in Work.Spaces.Iθ, angZ θ)
      * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ)

theorem aestronglyMeasurable_Bmom (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (i : ℕ) :
    AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.Bmom F i z)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) := by
  have hsin : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ := by
    unfold Work.Elliptic.sinCos2
    fun_prop
  have h := aestronglyMeasurable_integral_Itheta_Q0 (Work.Spaces.DzIter i F)
    (hF.DzIter i).continuousOn Work.Elliptic.sinCos2 hsin
  rw [show ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz)
      = ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)) from by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  simpa only [Work.FTS.EllipticEst.Bmom, Work.FTS.EllipticEst.PsiInt] using h

theorem aestronglyMeasurable_w_sq :
    AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) := by
  have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    rw [show Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 from rfl]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  have h : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := hw.pow 2
  rw [show ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz)
      = ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)) from by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact h.aestronglyMeasurable measurableSet_Ioi

theorem aestronglyMeasurable_Psi (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    AEStronglyMeasurable (Psi α k F)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) := by
  have hB : ∀ i : ℕ, AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.Bmom F i z)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) :=
    fun i => aestronglyMeasurable_Bmom α k F hF i
  have hw := aestronglyMeasurable_w_sq
  have hsum1 : AEStronglyMeasurable (fun z : ℝ => ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) := by
    rw [show (fun z : ℝ => ∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
        = (∑ i ∈ Finset.range (k + 1),
            fun z : ℝ => (Work.Spaces.w z) ^ 2
              * (Work.FTS.EllipticEst.Bmom F i z) ^ 2) from by
      funext z
      rw [Finset.sum_apply]]
    exact Finset.aestronglyMeasurable_sum (Finset.range (k + 1))
      (fun i hi => hw.mul ((hB i).pow 2))
  have hsum2 : AEStronglyMeasurable (fun z : ℝ => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ))
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) := by
    rw [show (fun z : ℝ => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
            * (∫ θ in Work.Spaces.Iθ, angA α i θ))
        = (∑ i ∈ Finset.range (k + 1), fun z : ℝ => ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
            * (∫ θ in Work.Spaces.Iθ, angA α i θ)) from by
      funext z
      rw [Finset.sum_apply]]
    refine Finset.aestronglyMeasurable_sum (Finset.range (k + 1)) (fun i hi => ?_)
    rw [show (fun z : ℝ => ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
            * (∫ θ in Work.Spaces.Iθ, angA α i θ))
        = (∑ j ∈ Finset.range (k + 1), fun z : ℝ =>
          (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
            * (∫ θ in Work.Spaces.Iθ, angA α i θ)) from by
      funext z
      rw [Finset.sum_apply]]
    refine Finset.aestronglyMeasurable_sum (Finset.range (k + 1)) (fun j hj => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      exact (hw.mul ((hB j).pow 2)).mul aestronglyMeasurable_const
    · refine (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ)) _).congr ?_
      filter_upwards with z
      simp [if_neg hc]
  have hPsi : Psi α k F = fun z : ℝ =>
      (∫ θ in Work.Spaces.Iθ, angZ θ) * (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
      + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
            * (∫ θ in Work.Spaces.Iθ, angA α i θ) := rfl
  rw [hPsi]
  exact (aestronglyMeasurable_const.mul hsum1).add hsum2

/-! ## The a.e. evaluation of the slice integral -/

theorem ae_sliceIntegral_eq_Psi (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) :
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
        (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      =ᵐ[(MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz] Psi α k F := by
  have hrad : ∀ᵐ z ∂((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz),
      ∀ j : ℕ, j ≤ k →
        Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) j z
          = Work.FTS.EllipticEst.Bmom F j z := by
    rw [show ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz)
        = ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)) from by
      rw [Work.Spaces.Iz]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    exact radIter_Bmom_ae α k F hF hmem
  have hInt : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
        (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      = (Work.Spaces.w z) ^ 2 * ((∫ θ in Work.Spaces.Iθ, angZ θ)
              * (∑ i ∈ Finset.range (k + 1),
                  (Work.FTS.EllipticEst.radIter
                    (fun z => Work.FTS.EllipticEst.Bmom F 0 z) i z) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                (if 1 ≤ i ∧ i + j ≤ k then
                    (Work.FTS.EllipticEst.radIter
                      (fun z => Work.FTS.EllipticEst.Bmom F 0 z) j z) ^ 2 else 0)
                  * (∫ θ in Work.Spaces.Iθ, angA α i θ)) := by
    intro z
    rw [MeasureTheory.setIntegral_congr_ae
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (Eventually.of_forall fun θ hθ => HkIntegrand_radial_sin α k
        (fun z => Work.FTS.EllipticEst.Bmom F 0 z) z θ hθ)]
    exact integral_HkExp α k (fun z => Work.FTS.EllipticEst.Bmom F 0 z) z
      integrableOn_angZ (fun i => integrableOn_angA α i hα hα1)
  filter_upwards [hrad] with z hzrad
  rw [hInt z]
  have h1 : ∀ i ∈ Finset.range (k + 1),
      Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) i z
        = Work.FTS.EllipticEst.Bmom F i z :=
    fun i hi => hzrad i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hS1 : (∑ i ∈ Finset.range (k + 1),
        (Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) i z) ^ 2)
      = ∑ i ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.Bmom F i z) ^ 2 :=
    Finset.sum_congr rfl fun i hi => by rw [h1 i hi]
  have hS2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) j z) ^ 2
          else 0) * (∫ θ in Work.Spaces.Iθ, angA α i θ))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ) := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, h1 j hj]
    · rw [if_neg hc, if_neg hc]
  rw [hS1, hS2, Psi]
  rw [mul_add]
  congr 1
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]; ring
    · simp only [if_neg hc]; ring

/-! ## The pointwise bound on the majorant -/

theorem Phi_bound (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (z : ℝ) (hz : z ∈ Work.Spaces.Iz) :
    Psi α k F z ≤ sliceK k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
  have hgam1 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
  have hgam2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  -- Cauchy--Schwarz for the moments
  have hCS : ∀ i : ℕ, i ≤ k →
      (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2
        ≤ (π / 2) * FstarHkOpen.Uj F z i := by
    intro i hi
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · rw [← h0]
      have hw : Work.Spaces.w (0 : ℝ) = 0 := by rw [Work.Spaces.w]; norm_num
      have hU : FstarHkOpen.Uj F 0 i = 0 := by
        rw [FstarHkOpen.Uj, hw]
        simp
      rw [hU, hw]
      simp
    · have h := FstarDzIter_sq_mul_w_le_open α k F hF hmem i hi hpos
      rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
      simpa only [FstarHkOpen.Uj, mul_comm] using h
  -- the sum of the angular masses is dominated by the slice integral of the source
  have hSG : (∑ i ∈ Finset.range (k + 1), FstarHkOpen.Uj F z i)
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
    have hint : ∀ i ∈ Finset.range (k + 1), MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.DzIter i F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ :=
      fun i hi => Work.FTS.EllipticEst.integrableOn_zSummand α k hF hmem i
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hz
    have hsum : (∑ i ∈ Finset.range (k + 1), FstarHkOpen.Uj F z i)
        = ∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      simp only [FstarHkOpen.Uj]
      rw [← MeasureTheory.integral_finsetSum]
      exact hint
    rw [hsum]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Finset.sum_nonneg fun i _ => sq_nonneg _)
      (hmem.1 z hz) (Eventually.of_forall fun θ => ?_)
    rw [Work.Spaces.HkIntegrand]
    exact le_add_of_nonneg_right (Work.Spaces.hkMixedSum_nonneg α k F z θ)
  -- the angular integrals
  have hZnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, angZ θ) :=
    MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_Icc fun θ hθ => angZ_nonneg hθ)
  have hZle : (∫ θ in Work.Spaces.Iθ, angZ θ) ≤ π / 2 := by
    have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have h := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => angZ_nonneg hθ)
      hone
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => angZ_le_one hθ)
    calc (∫ θ in Work.Spaces.Iθ, angZ θ) ≤ (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) := h
      _ = π / 2 := FstarHkOpen.integral_Iθ_one
  have hAnn : ∀ i : ℕ, 0 ≤ (∫ θ in Work.Spaces.Iθ, angA α i θ) := fun i =>
    MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_Icc fun θ hθ => angA_nonneg α i hθ)
  have hAle : ∀ i : ℕ, (∫ θ in Work.Spaces.Iθ, angA α i θ)
      ≤ FstarHkOpen.angK i * (π / 2) := by
    intro i
    have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => FstarHkOpen.angK i)
        Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have h := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        fun θ hθ => angA_nonneg α i hθ)
      hone
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        fun θ hθ => angA_le_angK α i hgam1 hgam2 hθ)
    have hvol : MeasureTheory.volume.real (Set.Icc 0 (π / 2)) = π / 2 := by
      rw [MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), sub_zero]
    calc (∫ θ in Work.Spaces.Iθ, angA α i θ)
        ≤ ∫ θ in Work.Spaces.Iθ, FstarHkOpen.angK i := h
      _ = MeasureTheory.volume.real (Set.Icc 0 (π / 2)) * FstarHkOpen.angK i := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul]
          rfl
      _ = FstarHkOpen.angK i * (π / 2) := by rw [hvol]; ring
  have hUjnn : ∀ i : ℕ, 0 ≤ FstarHkOpen.Uj F z i := fun i => FstarHkOpen.Uj_nonneg F z i
  have hSGu : 0 ≤ ∑ i ∈ Finset.range (k + 1), FstarHkOpen.Uj F z i :=
    Finset.sum_nonneg fun i _ => hUjnn i
  have hSKnn : 0 ≤ FstarHkOpen.angKsum k := FstarHkOpen.angKsum_nonneg k
  have hmFnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
    MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
  -- every moment square is bounded by `(π/2) * (Σ Uj)`
  have hX : ∀ i ≤ k, (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2
      ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by
    intro i hi
    refine le_trans (hCS i hi) (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Finset.single_le_sum (fun j _ => hUjnn j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  -- every angular integral is bounded by `(Σ angK) * (π/2)`
  have hY : ∀ i ≤ k, (∫ θ in Work.Spaces.Iθ, angA α i θ)
      ≤ FstarHkOpen.angKsum k * (π / 2) := by
    intro i hi
    refine le_trans (hAle i) (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [FstarHkOpen.angKsum]
    exact Finset.single_le_sum (fun j _ => (FstarHkOpen.angK_pos j).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  -- the pure sum
  have hS1 : (∫ θ in Work.Spaces.Iθ, angZ θ)
        * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
      ≤ ((k : ℝ) + 1) * (π / 2) ^ 2
          * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by
    have hb : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
        ≤ ∑ i ∈ Finset.range (k + 1), (π / 2)
            * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) :=
      Finset.sum_le_sum fun i hi =>
        hX i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    have hb' : (∑ i ∈ Finset.range (k + 1), (π / 2)
          * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
        = ((k : ℝ) + 1) * ((π / 2)
            * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    have hsum_le : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
        ≤ ((k : ℝ) + 1) * ((π / 2)
            * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)) :=
      le_trans hb (le_of_eq hb')
    calc (∫ θ in Work.Spaces.Iθ, angZ θ)
          * (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
        ≤ (π / 2) * (((k : ℝ) + 1) * ((π / 2)
            * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))) :=
          mul_le_mul hZle hsum_le
            (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (by positivity)
      _ = ((k : ℝ) + 1) * (π / 2) ^ 2
            * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by ring
  -- the mixed sum
  have hCC : 0 ≤ ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
      * (FstarHkOpen.angKsum k * (π / 2)) :=
    mul_nonneg (mul_nonneg (by positivity) hSGu) (mul_nonneg hSKnn (by positivity))
  have hterm : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
        * (∫ θ in Work.Spaces.Iθ, angA α i θ)
      ≤ ((π / 2) * (∑ j' ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j'))
          * (FstarHkOpen.angKsum k * (π / 2)) := by
    intro i hi j hj
    have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hile : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc]
      exact mul_le_mul (hX j hjle) (hY i hile) (hAnn i)
        (mul_nonneg (by positivity) hSGu)
    · rw [if_neg hc, zero_mul]
      exact hCC
  have hS2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ))
      ≤ ((k : ℝ) + 1) * (((k : ℝ) + 1)
          * (((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
              * (FstarHkOpen.angKsum k * (π / 2)))) := by
    have h1 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ))
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ((π / 2) * (∑ j' ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j'))
              * (FstarHkOpen.angKsum k * (π / 2)) :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
    have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ((π / 2) * (∑ j' ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j'))
              * (FstarHkOpen.angKsum k * (π / 2)))
        = ((k : ℝ) + 1) * (((k : ℝ) + 1)
            * (((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
                * (FstarHkOpen.angKsum k * (π / 2)))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    linarith [h1, h2.le]
  have hid : ((k : ℝ) + 1) * (((k : ℝ) + 1)
        * (((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
            * (FstarHkOpen.angKsum k * (π / 2))))
      = ((k : ℝ) + 1) * (π / 2) ^ 2
          * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (((k : ℝ) + 1) * FstarHkOpen.angKsum k) := by ring
  have htot : ((k : ℝ) + 1) * (π / 2) ^ 2
        * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
      + ((k : ℝ) + 1) * (π / 2) ^ 2
        * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        * (((k : ℝ) + 1) * FstarHkOpen.angKsum k)
      ≤ sliceK k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
    have hfac : 0 ≤ ((k : ℝ) + 1) * (π / 2) ^ 2
        * (1 + ((k : ℝ) + 1) * FstarHkOpen.angKsum k) :=
      mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
        (by have := mul_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) hSKnn; linarith)
    have heq : ((k : ℝ) + 1) * (π / 2) ^ 2
          * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        + ((k : ℝ) + 1) * (π / 2) ^ 2
          * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (((k : ℝ) + 1) * FstarHkOpen.angKsum k)
        = ((k : ℝ) + 1) * (π / 2) ^ 2
            * (1 + ((k : ℝ) + 1) * FstarHkOpen.angKsum k)
          * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by ring
    rw [heq]
    refine le_trans (mul_le_mul_of_nonneg_left hSG hfac) ?_
    refine mul_le_mul_of_nonneg_right ?_ hmFnn
    rw [sliceK]
    linarith
  unfold Psi
  linarith [hS1, hS2, hid, htot]

/-! ## The a.e. domination of the slice integral -/

theorem slice_bound (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    ∀ᵐ z ∂((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
        ≤ sliceK k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
  filter_upwards [ae_sliceIntegral_eq_Psi α k F hα hα1 hF hmem,
    MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    with z hz hzI
  rw [hz]
  exact Phi_bound α k F hα hα1 hF hmem z hzI

/-! ## Membership in `ℋ^k` -/

theorem HkMem_bmom_sin_of_smoothOpen (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    Work.Spaces.HkMem α k (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) := by
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
      Work.Spaces.HkIntegrand α k
        (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · subst h0
      have hz0 : ∀ θ : ℝ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) 0 θ = 0 :=
        fun θ => by simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]
      refine MeasureTheory.IntegrableOn.congr_fun MeasureTheory.integrableOn_zero
        (fun θ _ => (hz0 θ).symm) (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
    · exact integrableOn_slice_of_bound α k (fun z => Work.FTS.EllipticEst.Bmom F 0 z) z
        hpos (sliceConst k (fun z => Work.FTS.EllipticEst.Bmom F 0 z) z)
        (continuousOn_HkExp α k _ z)
        (fun θ hθ => HkExp_le_sliceConst α k _ z hα hα1 θ
          ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k
        (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) :=
    (aestronglyMeasurable_Psi α k F hF).congr
      (ae_sliceIntegral_eq_Psi α k F hα hα1 hF hmem).symm
  refine ⟨hslice, ?_⟩
  refine MeasureTheory.Integrable.mono' (hmem.2.const_mul (sliceK k)) haesm ?_
  filter_upwards [slice_bound α k F hα hα1 hF hmem] with z hz
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ =>
    Work.Spaces.HkIntegrand_nonneg α k _ z θ)]
  exact hz


end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.HkMem_Gbar_sin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Work.FTS.EllipticEst.Cert.GbarSin

/-! ## The reduction of the source to `bslOp α Ψ` -/



/-! ## Continuity of the radial derivatives of `Ḡ` -/

/-- **Continuity of the Hardy operator on `(0,∞)`** for an `L¹`-loc integrand: this is the
continuity of the primitive (`continuousOn_primitive_Ioi`) times the continuous factor
`z ↦ z^(-β)`.  In particular no continuity of `u` itself is needed. -/
theorem HarOp_continuousOn (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    ContinuousOn (fun z => HarOp (bet α) (Uj F j) z) (Set.Ioi 0) := by
  have hprim : ContinuousOn
      (fun z => ∫ s in (0 : ℝ)..z, s ^ (bet α - 1) * Uj F j s) (Set.Ioi 0) :=
    continuousOn_primitive_Ioi fun z hz => intervalIntegrable_rpow_Uj α hα hα1 k F hF hmem j hj hz
  have hzpow : ContinuousOn (fun z : ℝ => z ^ (-(bet α))) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))
  have hfun : (fun z => HarOp (bet α) (Uj F j) z)
      = fun z => z ^ (-(bet α)) * ∫ s in (0 : ℝ)..z, s ^ (bet α - 1) * Uj F j s := by
    funext z; rfl
  rw [hfun]
  exact hzpow.mul hprim

/-- **The radial derivatives of `Ḡ` are continuous on `(0,∞)`**: by the exact radial identity
`D_z^j Ḡ = -(3/(4α))·HarOp (5/α)(F_*(D_z^j F))` and `HarOp_continuousOn`. -/
theorem rDzIter_Gbar_continuousOn (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    ContinuousOn (fun z => rDzIter j (Work.Elliptic.Gbar α F) z) (Set.Ioi 0) := by
  have hH := HarOp_continuousOn α hα hα1 k F hF hmem j hj
  refine (hH.const_mul (-(3 / (4 * α)))).congr ?_
  intro z hz
  exact rDzIter_Gbar_eq_open α hα hα1 k F hF hmem j hj hz

/-! ## Continuity of the `ℋ^k`-integrand of the target on the open quadrant -/

/-- The angular profile `D_θ^i (sin 2θ)` is continuous. -/
theorem continuousOn_sinIter (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => sinIter i p.2) Q0 := by
  have hpoly : Continuous (fun t : ℝ => (sinPoly i).eval t) := Polynomial.continuous _
  have hfun : (fun p : ℝ × ℝ => sinIter i p.2)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * (sinPoly i).eval (Real.cos (2 * p.2)) := by
    funext p; exact sinIter_eq_sinPoly i p.2
  rw [hfun]
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn.mul
    (hpoly.comp (Real.continuous_cos.comp (continuous_const.mul continuous_snd))).continuousOn

/-- The weight `Wt α z θ = w(z)·sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have h2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [h2]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by funext p; rfl
  rw [hfun]
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- **The `ℋ^k`-integrand of `Ḡ(α,F)·sin 2θ` is continuous on the open quadrant** for a source
`F` which is `C^∞` on `Q0` and lies in `ℋ^k`.

Indeed on `Q0` the factorisations
`D_z^i(Ḡ·sin 2θ) = (D_z^i Ḡ)·sin 2θ` and `D_z^j D_θ^i(Ḡ·sin 2θ) = (D_z^j Ḡ)·D_θ^i(sin 2θ)`
exhibit the integrand as a finite sum of products of continuous functions of `(z,θ)`. -/
theorem continuousOn_HkIntegrand_GbarSin (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ)
    (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k
        (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) p.1 p.2) Q0 := by
  have hz : ∀ i, i ≤ k → ContinuousOn
      (fun p : ℝ × ℝ => rDzIter i (Work.Elliptic.Gbar α F) p.1) Q0 := fun i hi =>
    (rDzIter_Gbar_continuousOn α hα hα1 k F hF hmem i hi).comp continuousOn_fst
      (fun p hp => hp.1)
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Q0 := by fun_prop
  have hwdiv : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1
        / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Q0 := continuousOn_wdivsin_Q0
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := continuousOn_Wt α
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ =>
      (∑ i ∈ Finset.range (k + 1), (rDzIter i (Work.Elliptic.Gbar α F) p.1
          * Real.sin (2 * p.2)
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (rDzIter j (Work.Elliptic.Gbar α F) p.1 * sinIter i p.2
                * Work.Spaces.Wt α p.1 p.2) ^ 2 else 0)) ?_ ?_
  · refine ContinuousOn.add ?_ ?_
    · refine continuousOn_finsetSum _ fun i hi => ?_
      exact (((hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).mul hsin).mul hwdiv).pow 2
    · refine continuousOn_finsetSum _ fun i _ =>
        continuousOn_finsetSum _ fun j _ => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        exact (((hz j (by omega)).mul (continuousOn_sinIter i)).mul hWt).pow 2
      · simp only [if_neg hc]
        exact continuousOn_const
  · intro p hp
    simp only [Work.Spaces.HkIntegrand]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [gbar_DzIter_target_eq α F i p.1 p.2]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc, if_pos hc, gbar_mixed_target_eq α F j i p.1 p.2]
      · rw [if_neg hc, if_neg hc]

/-! ## Membership in `ℋ^k` for a `C^∞` source on the open quadrant -/

/-- **`Ḡ(α,F)·sin 2θ ∈ ℋ^k`** for a source `F` which is `C^∞` on the open quadrant and lies
in `ℋ^k`.

The majorant is `M z θ = Kang k·w(z)²·Σ_{j≤k}(D_z^j Ḡ z)²`, whose `θ`-slices are
constant (`integrableOn_const`) and whose slice integral is integrable by the per-order weighted
bound `Gbar_rDzIter_bound`. -/
theorem HkMem_target_of_smoothOpen (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
  set M : ℝ → ℝ → ℝ := fun z θ => gbar_Kang k * (Work.Spaces.w z) ^ 2 *
    ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 with hM
  have hIθ_ne_top : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  refine Work.FTS.LocData.HkMem_of_majorant (α := α) (k := k)
    (f := fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) (M := M)
    (continuousOn_HkIntegrand_GbarSin α hα hα1 k F hF hmem) ?_ ?_ ?_
  · -- the `θ`-slices of the majorant are constant in `θ`
    intro z _
    exact MeasureTheory.integrableOn_const hIθ_ne_top
  · -- the slice integral of the majorant is integrable
    have hconst : ∀ z : ℝ, (fun θ : ℝ => M z θ) = fun _ : ℝ => gbar_Kang k *
        (Work.Spaces.w z) ^ 2 * ∑ j ∈ Finset.range (k + 1),
          (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := by
      intro z
      funext θ
      rw [hM]
    have hfun : (fun z => ∫ θ in Work.Spaces.Iθ, M z θ)
        = fun z => (π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
            ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)) := by
      funext z
      rw [hconst z, gbar_integral_Iθ_const]
      ring
    rw [hfun]
    have hsum : Integrable (fun z => ∑ j ∈ Finset.range (k + 1),
        (π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
          (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      gbar_integrable_finsetSum _ _ _ fun j hj =>
        ((Gbar_rDzIter_bound α hα hα1 k F hF hmem j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1.const_mul (gbar_Kang k)).const_mul _
    refine hsum.congr ?_
    filter_upwards with z
    simp only [Finset.mul_sum]
  · -- the pointwise domination
    intro z hz θ hθ
    exact gbar_HkIntegrand_target_le α hα hα1 k F z θ hz hθ

/-! ## The target theorem -/


end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeDataAof =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace AeDataAofAux

/-! ## §1 The operator identities on the open quadrant -/

/-- `∂_θ^i f` is `C^∞` on the open quadrant when `f` is. -/
theorem smoothOpen_pthIter {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i f) := by
  induction i with
  | zero => simpa using hf
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- Multiplication of a `SmoothOpen` function by the polynomial `z²` stays `SmoothOpen`. -/
theorem smoothOpen_zsq_mul {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * g z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => z ^ 2 * g z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ => z ^ 2 * g z θ)
      = (fun p : ℝ × ℝ => p.1 ^ 2) * Function.uncurry g := by funext p; rfl
  rw [hfun]
  exact (contDiffOn_fst.pow 2).mul hg

/-- **`z²∂_z²f = D_z²f − D_zf`** at every point of the open quadrant, for `f` which is `C^∞`
there. -/
theorem zsq_pzIter2_eq_open {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    z ^ 2 * Work.Spaces.pzIter 2 f z θ
      = Work.Spaces.DzIter 2 f z θ - Work.Spaces.DzIter 1 f z θ := by
  have hfd : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz f z' θ)
      (Work.Spaces.pz f z θ + z * Work.Spaces.pzIter 2 f z θ) z := by
    have h1 : HasDerivAt (fun z' : ℝ => z') 1 z := hasDerivAt_id z
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz f z' θ)
        (Work.Spaces.pzIter 2 f z θ) z := by
      have h := hf.hasDerivAt_slice_pzIter 1 hθ hz
      simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h
    have h := h1.mul h2
    convert h using 1
    ring
  have hDz : Work.Spaces.DzIter 1 f z θ = z * Work.Spaces.pz f z θ := rfl
  have hD2 : Work.Spaces.DzIter 2 f z θ
      = z * deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z := rfl
  rw [hDz, hD2, hfd.deriv]
  ring

/-- On the open quadrant, `∂_θ^m` commutes with `∂_z`. -/
theorem pz_pthIter_comm_Q0 {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) (m : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter m g)))
      (Function.uncurry (Work.Spaces.pthIter m (Work.Spaces.pz g)))
        Work.FTS.EllipticEst.Q0 := by
  induction m with
  | zero => intro p hp; rfl
  | succ k ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hpt : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pthIter k g)) (z, θ) :=
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pthIter k g)).mp
          (smoothOpen_pthIter hg k) 2).contDiffAt
            (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hpt)
      have hstep : Work.Spaces.pz (Work.Spaces.pthIter (k + 1) g) z θ
          = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pthIter k g)) z θ := by
        rw [Work.Spaces.pthIter_succ]
        exact Work.Spaces.pz_pth_comm hcd
      have hstep2 : Work.Spaces.pthIter (k + 1) (Work.Spaces.pz g) z θ
          = Work.Spaces.pth (Work.Spaces.pthIter k (Work.Spaces.pz g)) z θ := by
        rw [Work.Spaces.pthIter_succ]
      change Work.Spaces.pz (Work.Spaces.pthIter (k + 1) g) z θ
        = Work.Spaces.pthIter (k + 1) (Work.Spaces.pz g) z θ
      rw [hstep, hstep2]
      exact Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ih hpt

/-- On the open quadrant, `∂_θ^m` commutes with `∂_z^j`. -/
theorem pthIter_pzIter_comm_Q0 {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (m j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter m (Work.Spaces.pzIter j g)))
      (Function.uncurry (Work.Spaces.pzIter j (Work.Spaces.pthIter m g)))
        Work.FTS.EllipticEst.Q0 := by
  induction j with
  | zero => intro p hp; rfl
  | succ k ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hpt : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
      have hle : Work.Spaces.pthIter m (Work.Spaces.pz (Work.Spaces.pzIter k g)) z θ
          = Work.Spaces.pz (Work.Spaces.pthIter m (Work.Spaces.pzIter k g)) z θ :=
        (pz_pthIter_comm_Q0 (hg.pzIter k) m hpt).symm
      have hpz : Work.Spaces.pz (Work.Spaces.pthIter m (Work.Spaces.pzIter k g)) z θ
          = Work.Spaces.pz (Work.Spaces.pzIter k (Work.Spaces.pthIter m g)) z θ :=
        Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ih hpt
      change Work.Spaces.pthIter m (Work.Spaces.pzIter (k + 1) g) z θ
        = Work.Spaces.pzIter (k + 1) (Work.Spaces.pthIter m g) z θ
      rw [show Work.Spaces.pzIter (k + 1) g = Work.Spaces.pz (Work.Spaces.pzIter k g) from rfl,
        show Work.Spaces.pzIter (k + 1) (Work.Spaces.pthIter m g)
            = Work.Spaces.pz (Work.Spaces.pzIter k (Work.Spaces.pthIter m g)) from rfl,
        hle, hpz]

/-- A coefficient depending only on `z` passes through the iterated `θ`-derivatives. -/
theorem pthIter_fst_mul (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (m : ℕ) :
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

/-- **`∂_θ²(z²∂_z²Ψ) = z²∂_z²(∂_θ²Ψ)`** on the open quadrant. -/
theorem pthIter_two_zsq_pzIter2_eq {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  have hpt : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h2 : Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ :=
    congrFun (congrFun (pthIter_fst_mul (fun z : ℝ => z ^ 2)
      (Work.Spaces.pzIter 2 Ψ) 2) z) θ
  have h3 : Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ
      = Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ :=
    pthIter_pzIter_comm_Q0 hΨ 2 2 hpt
  rw [h2, h3]

/-! ## §2 The level-`0` `ℋ`-integrand -/

/-- `HkIntegrand α 0 f` is the weighted square of `f`. -/
theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp

/-- The `ℋ⁰`-integrand vanishes at `z = 0`. -/
theorem HkIntegrand_zero_z {α : ℝ} (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f 0 θ = 0 := by
  rw [HkIntegrand_zero_eq]
  simp [Work.Spaces.w]

/-- The `ℋ⁰`-integrand vanishes at `θ = 0`. -/
theorem HkIntegrand_zero_theta_zero {α : ℝ} (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z 0 = 0 := by
  rw [HkIntegrand_zero_eq, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero,
    Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  simp

/-- The `ℋ⁰`-integrand vanishes at `θ = π/2`. -/
theorem HkIntegrand_zero_theta_pi {α : ℝ} (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z (Real.pi / 2) = 0 := by
  rw [HkIntegrand_zero_eq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi,
    Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  simp

/-- **`ℋ⁰`-membership by a pointwise majorant.** -/
theorem HkMem_zero_of_majorant {α : ℝ} {f M : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hMsl : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 f z θ ≤ M z θ) :
    Work.Spaces.HkMem α 0 f := by
  have hC : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
        = fun p : ℝ × ℝ => (f p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      funext p
      exact HkIntegrand_zero_eq α f p.1 p.2
    rw [hfun]
    exact (hf.mul (Work.FTS.EllipticEst.continuousOn_wdivsin_Q0)).pow 2
  refine Work.Blocks.HkMem_of_majorant_aesm (α := α) (k := 0) (f := f) (M := M)
    ?_ ?_ hMsl hMz hle
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine (MeasureTheory.aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).congr ?_
      filter_upwards with θ
      exact (HkIntegrand_zero_z (α := α) f θ).symm
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hC hz0
  · exact (Work.Spaces.aesm_of_continuousOn_Qd _ hC).integral_prod_right'

/-- **A single radial summand of an honest `ℋ^k`-integrand is honest in `ℋ⁰`.** -/
theorem excess_zsummand_mem (α : ℝ) (k i : ℕ) (f : ℝ → ℝ → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : Work.Spaces.HkMem α k f) (hi : i ≤ k) :
    Work.Spaces.HkMem α 0 (Work.Spaces.DzIter i f) := by
  refine HkMem_zero_of_majorant (α := α) (f := Work.Spaces.DzIter i f)
    (M := fun z θ => Work.Spaces.HkIntegrand α k f z θ) hcont (fun z hz => hmem.1 z hz)
    hmem.2 ?_
  intro z hz θ hθ
  rw [HkIntegrand_zero_eq]
  exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ i hi

/-- **`ℋ⁰`-membership transfers along an identity on the open quadrant.** -/
theorem HkMem_zero_congr {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hg : Work.Spaces.HkMem α 0 g) :
    Work.Spaces.HkMem α 0 f := by
  refine HkMem_zero_of_majorant (α := α) (f := f)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α 0 g z θ) hf ?_ ?_ ?_
  · intro z hz
    exact (hg.1 z hz).const_mul 2
  · have h' := hg.2.const_mul 2
    refine h'.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz_eq | hz0
    · rw [← hz_eq, HkIntegrand_zero_z]
      exact mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 0 g 0 θ)
    · rcases eq_or_lt_of_le hθ.1 with hθ_eq | hθ0
      · rw [← hθ_eq, HkIntegrand_zero_theta_zero]
        exact mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 0 g z 0)
      · rcases eq_or_lt_of_le hθ.2 with hθ_eq | hθ1
        · rw [hθ_eq, HkIntegrand_zero_theta_pi]
          exact mul_nonneg (by norm_num)
            (Work.Spaces.HkIntegrand_nonneg α 0 g z (Real.pi / 2))
        · rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq, h z θ hz0 hθ0 hθ1]
          nlinarith [sq_nonneg (g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]

/-- **`z²∂_z²X ∈ ℋ⁰` from `X ∈ ℋ²`.** -/
theorem HkMem_zero_zsq_pzIter2 (α : ℝ) {X : ℝ → ℝ → ℝ}
    (hX : Work.FTS.EllipticEst.SmoothOpen X)
    (hmem : Work.Spaces.HkMem α 2 X) :
    Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) := by
  have hz2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 X) :=
    excess_zsummand_mem α 2 2 X (hX.DzIter 2).continuousOn hmem le_rfl
  have hz1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 X) :=
    excess_zsummand_mem α 2 1 X (hX.DzIter 1).continuousOn hmem (by norm_num)
  have hMnn : ∀ z θ, (0 : ℝ)
      ≤ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 X) z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 1 X) z θ := by
    intro z θ
    have h1 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.DzIter 2 X) z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.DzIter 1 X) z θ
    linarith
  refine HkMem_zero_of_majorant
    (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 X) z θ
      + 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 1 X) z θ)
    (smoothOpen_zsq_mul (hX.pzIter 2)).continuousOn ?_ ?_ ?_
  · intro z hz
    exact ((hz2.1 z hz).const_mul 2).add ((hz1.1 z hz).const_mul 2)
  · have h' := (hz2.2.const_mul 2).add (hz1.2.const_mul 2)
    refine h'.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [Pi.add_apply, MeasureTheory.integral_add ((hz2.1 z hz).const_mul 2)
      ((hz1.1 z hz).const_mul 2), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz_eq | hz0
    · rw [← hz_eq, HkIntegrand_zero_z]
      exact hMnn 0 θ
    · rcases eq_or_lt_of_le hθ.1 with hθ0_eq | hθ0
      · rw [← hθ0_eq, HkIntegrand_zero_theta_zero]
        exact hMnn z 0
      · rcases eq_or_lt_of_le hθ.2 with hθ1_eq | hθ1
        · rw [hθ1_eq, HkIntegrand_zero_theta_pi]
          exact hMnn z (Real.pi / 2)
        · have hid : z ^ 2 * Work.Spaces.pzIter 2 X z θ
              = Work.Spaces.DzIter 2 X z θ - Work.Spaces.DzIter 1 X z θ :=
            zsq_pzIter2_eq_open hX hz0 ⟨hθ0, hθ1⟩
          set A : ℝ := Work.Spaces.DzIter 2 X z θ with hAdef
          set B : ℝ := Work.Spaces.DzIter 1 X z θ with hBdef
          set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
            with hWdef
          have hL : Work.Spaces.HkIntegrand α 0
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ = ((A - B) * W) ^ 2 := by
            rw [HkIntegrand_zero_eq, hid]
          have hA2 : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 X) z θ = (A * W) ^ 2 :=
            HkIntegrand_zero_eq α (Work.Spaces.DzIter 2 X) z θ
          have hB1 : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 1 X) z θ = (B * W) ^ 2 :=
            HkIntegrand_zero_eq α (Work.Spaces.DzIter 1 X) z θ
          rw [hL, hA2, hB1]
          nlinarith [sq_nonneg (A * W + B * W)]

/-- **`∂_θ²(z²∂_z²Ψ) ∈ ℋ⁰`** from the honesty of `∂_θ²Ψ` at level `2`. -/
theorem HkMem_zero_pthIter2_zsq_pzIter2 {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hmemB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) :
    Work.Spaces.HkMem α 0
      (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
  have hBsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    smoothOpen_pthIter hΨ 2
  have hz2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) :=
    excess_zsummand_mem α 2 2 (Work.Spaces.pthIter 2 Ψ)
      ((hBsm.DzIter 2).continuousOn) hmemB le_rfl
  have hz1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
    excess_zsummand_mem α 2 1 (Work.Spaces.pthIter 2 Ψ)
      ((hBsm.DzIter 1).continuousOn) hmemB (by norm_num)
  have hcont : ContinuousOn
      (Function.uncurry (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hbase : ContinuousOn
        (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (continuousOn_fst.pow 2).mul ((hBsm.pzIter 2).continuousOn)
    refine hbase.congr ?_
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    show Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
    exact pthIter_two_zsq_pzIter2_eq hΨ hz ⟨hθ0, hθ1⟩
  have hMnn : ∀ z θ, (0 : ℝ)
      ≤ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
        + 2 * Work.Spaces.HkIntegrand α 0
            (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ := by
    intro z θ
    have h1 := Work.Spaces.HkIntegrand_nonneg α 0
      (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α 0
      (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ
    linarith
  change Work.Spaces.HkMem α 0
    (fun z θ => Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
  refine HkMem_zero_of_majorant (f := fun z θ =>
      Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
    (M := fun z θ =>
      2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
        + 2 * Work.Spaces.HkIntegrand α 0
            (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ) hcont ?_ ?_ ?_
  · intro z hz
    exact ((hz2.1 z hz).const_mul 2).add ((hz1.1 z hz).const_mul 2)
  · have h' := (hz2.2.const_mul 2).add (hz1.2.const_mul 2)
    refine h'.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [Pi.add_apply, MeasureTheory.integral_add ((hz2.1 z hz).const_mul 2)
      ((hz1.1 z hz).const_mul 2), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz_eq | hz0
    · rw [← hz_eq, HkIntegrand_zero_z]
      exact hMnn 0 θ
    · rcases eq_or_lt_of_le hθ.1 with hθ0_eq | hθ0
      · rw [← hθ0_eq, HkIntegrand_zero_theta_zero]
        exact hMnn z 0
      · rcases eq_or_lt_of_le hθ.2 with hθ1_eq | hθ1
        · rw [hθ1_eq, HkIntegrand_zero_theta_pi]
          exact hMnn z (Real.pi / 2)
        · have hid : Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              = Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
                - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ := by
            rw [pthIter_two_zsq_pzIter2_eq hΨ hz0 ⟨hθ0, hθ1⟩,
              zsq_pzIter2_eq_open hBsm hz0 ⟨hθ0, hθ1⟩]
          set A : ℝ := Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ with hAdef
          set B : ℝ := Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ with hBdef
          set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
            with hWdef
          have hL : Work.Spaces.HkIntegrand α 0
                (fun z θ => Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) z θ
              = ((A - B) * W) ^ 2 := by
            rw [HkIntegrand_zero_eq, hid]
          have hA2 : Work.Spaces.HkIntegrand α 0
                (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ = (A * W) ^ 2 :=
            HkIntegrand_zero_eq α (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
          have hB1 : Work.Spaces.HkIntegrand α 0
                (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ = (B * W) ^ 2 :=
            HkIntegrand_zero_eq α (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ
          rw [hL, hA2, hB1]
          nlinarith [sq_nonneg (A * W + B * W)]

/-! ## §3 The equation of the twisted datum -/

/-- `bslOp α` is local on the open quadrant. -/
theorem bslOp_congr_Q0 (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α f z θ = Work.Elliptic.bslOp α g z θ := by
  intro z θ hz hθ0 hθ1
  have hq : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have hEq : Set.EqOn (Function.uncurry f) (Function.uncurry g)
      Work.FTS.EllipticEst.Q0 := fun p hp =>
    h p.1 p.2 (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      (Work.FTS.EllipticEst.mem_Q0.mp hp).2.1 (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2
  have hpz1 : Work.Spaces.pz f z θ = Work.Spaces.pz g z θ :=
    Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hq
  have hpz2 : Work.Spaces.pzIter 2 f z θ = Work.Spaces.pzIter 2 g z θ := by
    have hEq2 : Set.EqOn (Function.uncurry (Work.Spaces.pz f))
        (Function.uncurry (Work.Spaces.pz g)) Work.FTS.EllipticEst.Q0 :=
      fun p hp => Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hp
    exact Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq2 hq
  have hpth2 : Work.Spaces.pthIter 2 f z θ = Work.Spaces.pthIter 2 g z θ := by
    have hEq2 : Set.EqOn (Function.uncurry (Work.Spaces.pth f))
        (Function.uncurry (Work.Spaces.pth g)) Work.FTS.EllipticEst.Q0 :=
      fun p hp => Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hp
    exact Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq2 hq
  have htan : Work.Spaces.pth (fun z θ => Real.tan θ * f z θ) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * g z θ) z θ := by
    refine Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ?_ hq
    intro p hp
    obtain ⟨ha, hb0, hb1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    simp only [Function.uncurry]
    rw [h p.1 p.2 ha hb0 hb1]
  have hpt : f z θ = g z θ := h z θ hz hθ0 hθ1
  simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, hpz2, hpz1, hpth2, htan, hpt]

/-- **The equation of the twisted datum**: `bslOp α (z²∂_z²Ψ) = D_z²F − D_zF` on the open
quadrant. -/
theorem bslOp_Aof_eq_Gof (α : ℝ) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (Aof Ψ) z θ = Gof F z θ := by
  intro z hz θ hθ0 hθ1
  have hq : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcd2 : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter 2 Ψ)) (z, θ) :=
    ((hΨ.DzIter 2).forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hq)
  have hcd1 : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter 1 Ψ)) (z, θ) :=
    ((hΨ.DzIter 1).forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hq)
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  have hloc : Work.Elliptic.bslOp α (Aof Ψ) z θ
      = Work.Elliptic.bslOp α
          (fun z θ => Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ) z θ :=
    bslOp_congr_Q0 α (fun a b ha hb0 hb1 => zsq_pzIter2_eq_open hΨ ha ⟨hb0, hb1⟩)
      z θ hz hθ0 hθ1
  have hlin := Work.FTS.EllipticEst.bslOp_sub α (Work.Spaces.DzIter 2 Ψ)
    (Work.Spaces.DzIter 1 Ψ) z θ hcos hcd2 hcd1
  have hE2 := Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 2 h.smooth h.eq z hz θ hθ0 hθ1
  have hE1 := Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.eq z hz θ hθ0 hθ1
  show Work.Elliptic.bslOp α (Aof Ψ) z θ
    = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ
  rw [hloc, hlin, hE2, hE1]

/-! ## §4 The boundary slices of the radial derivatives -/

/-- If the `θ = a` slice of `Ψ` vanishes identically, then so does the `θ = a` slice of
`∂_z²Ψ`. -/
theorem pzIter_two_eq_zero_of_slice_zero {Ψ : ℝ → ℝ → ℝ} {a : ℝ} (ha : ∀ z, Ψ z a = 0) :
    ∀ z, Work.Spaces.pzIter 2 Ψ z a = 0 := by
  have h1 : ∀ z, Work.Spaces.pz Ψ z a = 0 := by
    intro z
    have hfun : (fun z' : ℝ => Ψ z' a) = fun _ => (0 : ℝ) := funext fun z' => ha z'
    have hz : Work.Spaces.pz Ψ z a = deriv (fun z' : ℝ => Ψ z' a) z := rfl
    rw [hz, hfun]
    simp
  intro z
  have hfun : (fun z' : ℝ => Work.Spaces.pz Ψ z' a) = fun _ => (0 : ℝ) := funext h1
  have hz : Work.Spaces.pzIter 2 Ψ z a = deriv (fun z' : ℝ => Work.Spaces.pz Ψ z' a) z := rfl
  rw [hz, hfun]
  simp

/-! ## §5 Pointwise facts about the angular weights -/

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

theorem sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 θ := by
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos, hθ.1]) hθ.2
  simp only [Work.Elliptic.sinCos2]
  positivity

theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  show Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)


theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith

/-- The pointwise energy/slot comparison. -/
theorem sq_mul_sEta_le_slot {D z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) :
    D ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (D * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.FTS.EllipticEst.mul_w_sin_rpow_sq D (Work.Spaces.w z) hθ]
  have hse : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := sEta_nonneg hθ
  have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith [one_le_w hz]
  calc D ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.w z) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg D)
        calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * 1 := by ring
          _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2 :=
              mul_le_mul_of_nonneg_left hw2 hse
    _ = D ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring

/-! ## §6 The Taylor majorant for the angular slices of `D_z^i Ψ` -/

/-- The weighted `ℋ²`-slot of `g` at the radius `u`. -/
def slot (g : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g u θ
    * (Work.Spaces.w u / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

theorem slot_nonneg (g : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : 0 ≤ slot g i u :=
  integral_nonneg fun θ => sq_nonneg _

/-- The `u`-slice of a function `C^∞` on the open quadrant is `C²` on `(0,π/2)`. -/
theorem contDiffOn_slice_two {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {u : ℝ} (hu : 0 < u) :
    ContDiffOn ℝ 2 (fun θ : ℝ => g u θ) (Set.Ioo 0 (Real.pi / 2)) :=
  (hg.curry_θ hu).of_le (by simp [Work.Stability.smoothOrder])

theorem continuousOn_sin_rpow_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

theorem aesm_energy_slice {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) (i : ℕ)
    {u : ℝ} (hu : 0 < u) :
    AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.DzIter i g u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
    (((hg.DzIter i).continuousOn).pow 2 |>.mul continuousOn_sin_rpow_Q0) hu

/-- The `η`-weighted energy of a single radial summand of `g` is dominated by its `ℋ²`-slot. -/
theorem energy_le_slot_aux {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 g) (i : ℕ) (hi : i ≤ 2) {u : ℝ} (hu : 0 < u) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ slot g i u := by
  have hslot := Work.FTS.EllipticEst.integrableOn_zSummand α 2 hg hB i hi
    (Set.mem_Ici.mpr hu.le)
  have henergy : IntegrableOn (fun θ => (Work.Spaces.DzIter i g u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    Integrable.mono' hslot (aesm_energy_slice hg i hu) (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))]
      exact sq_mul_sEta_le_slot hθ hu)
  refine integral_mono_ae henergy hslot ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  exact sq_mul_sEta_le_slot hθ hu

/-- The `∂_θ²`-energy integrand of the slice `D_z^i Ψ` is integrable, `i ≤ 2`. -/
theorem integrableOn_pthIter2_slice {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2)
    {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ : ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hpt_eq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ
        = Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ :=
    fun θ hθ => Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ i
      (show (u, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hu, hθ⟩)
  have hae : (fun θ : ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt_eq] with θ hθ
    rw [hθ]
  refine Integrable.mono'
    (Work.FTS.EllipticEst.integrableOn_zSummand α 2 ((hΨ.pth).pth) hB i hi
      (Set.mem_Ici.mpr hu.le)) ?_ ?_
  · exact (aesm_energy_slice ((hΨ.pth).pth) i hu).congr hae.symm
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc,
      Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt_eq] with θ hθ hθeq
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg hθ)), hθeq]
    exact sq_mul_sEta_le_slot hθ hu

/-- The `∂_θ²`-energy of the slice `D_z^i Ψ` is bounded by the `ℋ²`-slot of `∂_θ²Ψ`. -/
theorem energy_pthIter2_le_slot {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2)
    {u : ℝ} (hu : 0 < u) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ slot (Work.Spaces.pthIter 2 Ψ) i u := by
  have hpt_eq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ
        = Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ :=
    fun θ hθ => Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ i
      (show (u, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hu, hθ⟩)
  have hae : (fun θ : ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt_eq] with θ hθ
    rw [hθ]
  refine le_trans (le_of_eq ?_) (energy_le_slot_aux ((hΨ.pth).pth) hB i hi hu)
  exact integral_congr_ae hae

/-- The majorant of `∫_θ |D_z^i Ψ(u,θ)| sinθcos²θ` delivered by the slice Taylor estimate. -/
def Bnd (Ψ : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  3 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
    + 9 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
    + 9 * (slot (Work.Spaces.pthIter 2 Ψ) i u + 1)

theorem Bnd_nonneg (Ψ : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : 0 ≤ Bnd Ψ i u := by
  rw [Bnd]
  have h := slot_nonneg (Work.Spaces.pthIter 2 Ψ) i u
  have h1 := abs_nonneg (Work.Spaces.DzIter i Ψ u (Real.pi / 4))
  have h2 := abs_nonneg (Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4))
  linarith

/-- **The angular slice bound** for `D_z^i Ψ`, `i ≤ 2`. -/
theorem slice_bound {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2) :
    ∀ u : ℝ, 0 < u →
      ∫ θ in Work.Spaces.Iθ, |Work.Spaces.DzIter i Ψ u θ| * Work.Elliptic.sinCos2 θ
        ≤ Bnd Ψ i u := by
  intro u hu
  have hE := integrableOn_pthIter2_slice hΨ hB i hi hu
  obtain ⟨-, hbound⟩ := Work.FTS.EllipticEst.Mine.SliceMomentTaylor
    (contDiffOn_slice_two (hΨ.DzIter i) hu) hE
  have hsqrt : Real.sqrt (∫ θ in Work.Spaces.Iθ,
        deriv (deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ)) θ ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ slot (Work.Spaces.pthIter 2 Ψ) i u + 1 := by
    have henergy : (∫ θ in Work.Spaces.Iθ,
          deriv (deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ)) θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ slot (Work.Spaces.pthIter 2 Ψ) i u :=
      energy_pthIter2_le_slot hΨ hB i hi hu
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ,
          deriv (deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ)) θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ Real.sqrt (slot (Work.Spaces.pthIter 2 Ψ) i u) := Real.sqrt_le_sqrt henergy
      _ ≤ slot (Work.Spaces.pthIter 2 Ψ) i u + 1 := by
          have h := slot_nonneg (Work.Spaces.pthIter 2 Ψ) i u
          nlinarith [Real.sq_sqrt h, sq_nonneg (Real.sqrt (slot (Work.Spaces.pthIter 2 Ψ) i u))]
  have hd1 : Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)
      = deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ) (Real.pi / 4) := rfl
  rw [Bnd]
  rw [← hd1] at hbound
  linarith [hbound, hsqrt]

/-- `Bnd Ψ i` is integrable on `(a,b] ⊂ (0,∞)`. -/
theorem Bnd_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2)
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (Bnd Ψ i) (Set.Ioc a b) := by
  have h4 : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hsub2 : Set.Ioc a b ⊆ Set.Icc a b := Set.Ioc_subset_Icc_self
  have h1 : IntegrableOn (fun u : ℝ => |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|)
      (Set.Icc a b) :=
    (((hΨ.DzIter i).curry_z h4).continuousOn.mono hsub).abs.integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn (fun u : ℝ => |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|)
      (Set.Icc a b) :=
    ((((hΨ.DzIter i).pth).curry_z h4).continuousOn.mono hsub).abs.integrableOn_compact
      isCompact_Icc
  have h3 : IntegrableOn (slot (Work.Spaces.pthIter 2 Ψ) i) (Set.Icc a b) :=
    (Work.FTS.EllipticEst.integrableOn_slice_Iz α 2 ((hΨ.pth).pth) hB i hi).mono_set
      (fun x hx => le_of_lt (lt_of_lt_of_le ha hx.1))
  have hsum : IntegrableOn (fun u : ℝ => 3 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
      + 9 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
      + 9 * (slot (Work.Spaces.pthIter 2 Ψ) i u + 1)) (Set.Ioc a b) :=
    (((h1.mono_set hsub2).const_mul 3).add ((h2.mono_set hsub2).const_mul 9)).add
      (((h3.mono_set hsub2).add (integrableOn_const (by
        rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))).const_mul 9)
  have hEq : Bnd Ψ i = fun u : ℝ => 3 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
      + 9 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
      + 9 * (slot (Work.Spaces.pthIter 2 Ψ) i u + 1) := rfl
  rw [hEq]
  exact hsum

/-- **Integrability of a divided fibre bound** (Tonelli from a fibre bound). -/
theorem integrableUncurryDivOfFibreBound {f : ℝ → ℝ → ℝ} {B : ℝ → ℝ} {s z : ℝ}
    (hs : 0 < s) (hsz : s ≤ z)
    (hae : AEStronglyMeasurable (Function.uncurry (fun r θ : ℝ => f r θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)))
    (hfib : ∀ r ∈ Set.Ioc s z, IntegrableOn (fun θ => f r θ) Work.Spaces.Iθ)
    (hle : ∀ r ∈ Set.Ioc s z, ∫ θ in Work.Spaces.Iθ, |f r θ| ≤ B r)
    (hB : IntegrableOn B (Set.Ioc s z)) :
    Integrable (Function.uncurry (fun r θ : ℝ => f r θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
  haveI : SFinite (volume.restrict (Set.Ioc s z)) := inferInstance
  haveI : SFinite (volume.restrict Work.Spaces.Iθ) := inferInstance
  have hG : Integrable (Function.uncurry (fun r θ : ℝ => |f r θ / r|))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine (Work.Spaces.integrable_prod_of_iterated (μ := volume.restrict (Set.Ioc s z))
      (ν := volume.restrict Work.Spaces.Iθ) (G := fun r θ => |f r θ / r|)
      (fun a b => abs_nonneg _) ?_ ?_ ?_).1
    · exact hae.norm.congr (Filter.Eventually.of_forall fun p => by
        simp only [Function.uncurry, Real.norm_eq_abs])
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
      have hr0 : 0 < r := lt_trans hs hr.1
      exact (((hfib r hr).norm.const_mul r⁻¹).congr
        (Filter.Eventually.of_forall fun θ => by
          simp only [Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr hr0)]
          ring))
    · refine (hB.const_mul s⁻¹).mono' ?_ ?_
      · exact (hae.norm.integral_prod_right'
          (μ := volume.restrict (Set.Ioc s z)) (ν := volume.restrict Work.Spaces.Iθ)).congr
          (Filter.Eventually.of_forall fun r => by
            simp only [Function.uncurry, Real.norm_eq_abs])
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
        have hr0 : 0 < r := lt_trans hs hr.1
        have hBnn : 0 ≤ B r := le_trans (integral_nonneg fun θ => abs_nonneg _) (hle r hr)
        rw [Real.norm_of_nonneg (integral_nonneg fun θ => abs_nonneg _)]
        have h1 : ∫ θ in Work.Spaces.Iθ, |f r θ / r| = (∫ θ in Work.Spaces.Iθ, |f r θ|) / r := by
          rw [← MeasureTheory.integral_div]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
          rw [abs_div, abs_of_pos hr0]
        rw [h1]
        have hstep1 : (∫ θ in Work.Spaces.Iθ, |f r θ|) / r ≤ B r / r :=
          div_le_div_of_nonneg_right (hle r hr) (le_of_lt hr0)
        have hstep2 : B r / r ≤ s⁻¹ * B r := by
          rw [div_eq_mul_inv, mul_comm (B r)]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ hs (le_of_lt hr.1)) hBnn
        linarith
  refine (MeasureTheory.integrable_norm_iff hae).mp ?_
  exact hG.congr (Filter.Eventually.of_forall fun p => by
    simp only [Function.uncurry, Real.norm_eq_abs])

/-- The box integrability of `∂_z(D_z^a Ψ)·sinθcos²θ`, `a ≤ 1`. -/
theorem integrable_box_pz_DzIter {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (a : ℕ) (ha : a ≤ 1)
    {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z) :
    Integrable (Function.uncurry (fun r θ : ℝ =>
      Work.Spaces.pz (Work.Spaces.DzIter a Ψ) r θ * Work.Elliptic.sinCos2 θ))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have ha2 : a + 1 ≤ 2 := by omega
  have hfib : ∀ r ∈ Set.Ioc s z,
      IntegrableOn (fun θ => Work.Spaces.DzIter (a + 1) Ψ r θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ := by
    intro r hr
    have hr0 : 0 < r := lt_trans hs hr.1
    exact (Work.FTS.EllipticEst.Mine.SliceMomentTaylor
      (contDiffOn_slice_two (hΨ.DzIter (a + 1)) hr0)
      (integrableOn_pthIter2_slice hΨ hB (a + 1) ha2 hr0)).1
  have hle : ∀ r ∈ Set.Ioc s z,
      ∫ θ in Work.Spaces.Iθ, |Work.Spaces.DzIter (a + 1) Ψ r θ * Work.Elliptic.sinCos2 θ|
        ≤ Bnd Ψ (a + 1) r := by
    intro r hr
    have hr0 : 0 < r := lt_trans hs hr.1
    have h := slice_bound hΨ hB (a + 1) ha2 r hr0
    refine le_trans (le_of_eq ?_) h
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    rw [abs_mul, abs_of_nonneg (sinCos2_nonneg_Iθ hθ)]
  have hBint : IntegrableOn (Bnd Ψ (a + 1)) (Set.Ioc s z) :=
    Bnd_integrableOn hΨ hB (a + 1) ha2 hs
  have hae : AEStronglyMeasurable
      (Function.uncurry (fun r θ : ℝ =>
        (Work.Spaces.DzIter (a + 1) Ψ r θ * Work.Elliptic.sinCos2 θ) / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter (a + 1) Ψ p.1 p.2
        * Work.Elliptic.sinCos2 p.2) / p.1) ?_).mono_measure ?_
    · refine ContinuousOn.div ?_ continuousOn_fst (fun p hp =>
        ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
      exact (((hΨ.DzIter (a + 1)).forall 0).continuousOn).mul
        (continuous_sinCos2.comp continuous_snd).continuousOn
    · rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
      exact MeasureTheory.Measure.restrict_mono
        (Set.prod_mono (fun r hr => le_of_lt (lt_trans hs hr.1)) subset_rfl) le_rfl
  have hdiv := integrableUncurryDivOfFibreBound (f := fun r θ =>
      Work.Spaces.DzIter (a + 1) Ψ r θ * Work.Elliptic.sinCos2 θ)
    (B := Bnd Ψ (a + 1)) hs hsz hae hfib hle hBint
  refine hdiv.congr ?_
  have hbox : ∀ᵐ p ∂((volume.restrict (Set.Ioc s z)).prod
      (volume.restrict Work.Spaces.Iθ)), p ∈ Set.Ioc s z ×ˢ Work.Spaces.Iθ := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.self_mem_ae_restrict (measurableSet_Ioc.prod measurableSet_Icc)
  filter_upwards [hbox] with p hp
  obtain ⟨r, θ⟩ := p
  obtain ⟨hr, -⟩ := hp
  have hr0 : 0 < r := lt_trans hs hr.1
  have hpz : Work.Spaces.pz (Work.Spaces.DzIter a Ψ) r θ
      = Work.Spaces.DzIter (a + 1) Ψ r θ / r := by
    show Work.Spaces.pz (Work.Spaces.DzIter a Ψ) r θ
      = Work.Spaces.Dz (Work.Spaces.DzIter a Ψ) r θ / r
    simp only [Work.Spaces.Dz]
    field_simp
  simp only [Function.uncurry, Function.uncurry_apply_pair, hpz]
  ring

/-! ## §7 The angular moment chain for `Ψ` -/

/-- `F_*(∂_z(D_z^a Ψ))(r) = F_*(D_z^{a+1}Ψ)(r)/r` for `r > 0`. -/
theorem Fstar_pz_DzIter_eq (Ψ : ℝ → ℝ → ℝ) (a : ℕ) {r : ℝ} (hr : 0 < r) :
    Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter a Ψ)) r
      = Work.Elliptic.Fstar (Work.Spaces.DzIter (a + 1) Ψ) r / r := by
  have hfun : (fun θ : ℝ => Work.Spaces.pz (Work.Spaces.DzIter a Ψ) r θ
        * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => (1 / r)
          * (Work.Spaces.DzIter (a + 1) Ψ r θ * Work.Elliptic.sinCos2 θ) := by
    funext θ
    have hpz : Work.Spaces.pz (Work.Spaces.DzIter a Ψ) r θ
        = Work.Spaces.DzIter (a + 1) Ψ r θ / r := by
      show Work.Spaces.pz (Work.Spaces.DzIter a Ψ) r θ
        = Work.Spaces.Dz (Work.Spaces.DzIter a Ψ) r θ / r
      simp only [Work.Spaces.Dz]
      field_simp
    rw [hpz]
    ring
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, hfun, MeasureTheory.integral_const_mul]
  ring

/-- **The radial moment chain for `Ψ`**: `F_*(D_z^aΨ)(z) − F_*(D_z^aΨ)(s) =
∫_s^z F_*(D_z^{a+1}Ψ)(r)/r dr`, for `a ≤ 1`. -/
theorem Fstar_DzIter_tower_Psi {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {a : ℕ} (ha : a ≤ 1)
    {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter a Ψ) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter a Ψ) s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (a + 1) Ψ) r / r := by
  have hsl : ∀ x : ℝ, 0 < x → IntegrableOn
      (fun θ => Work.Spaces.DzIter a Ψ x θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    intro x hx
    exact (Work.FTS.EllipticEst.Mine.SliceMomentTaylor
      (contDiffOn_slice_two (hΨ.DzIter a) hx)
      (integrableOn_pthIter2_slice hΨ hB a (by omega) hx)).1
  have h := Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz (f := Work.Spaces.DzIter a Ψ)
    (hΨ.DzIter a) hs hsz (hsl s hs) (hsl z (lt_of_lt_of_le hs hsz))
    (integrable_box_pz_DzIter hΨ hB a ha hs hsz)
  rw [h]
  refine intervalIntegral.integral_congr fun r hr => ?_
  have hr0 : 0 < r := by
    rw [Set.uIcc_of_le hsz] at hr
    exact lt_of_lt_of_le hs hr.1
  exact Fstar_pz_DzIter_eq Ψ a hr0

/-- **The angular moments of `D_z^j Ψ` vanish a.e., `j ≤ 2`.** -/
theorem Fstar_DzIter_Psi_ae {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ j : ℕ, j ≤ 2 → ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0 := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ) := h.memB
  -- the interval integrability of the divided moments
  have hInt : ∀ j : ℕ, j ≤ 2 → ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable
        (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r / r) volume a b := by
    intro j hj a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    have hBndI : MeasureTheory.IntegrableOn (Bnd Ψ j) (Set.Icc a b) :=
      (Bnd_integrableOn hΨ hB j hj ha).congr_set_ae
        (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b)).symm
    refine MeasureTheory.Integrable.mono' (hBndI.const_mul (1 / a)) ?_ ?_
    · -- a.e. strong measurability of the divided moment
      have hjoint : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.DzIter j Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
        Work.Spaces.aesm_of_continuousOn_Qd _
          (((hΨ.DzIter j).forall 0).continuousOn.mul
            (continuous_sinCos2.comp continuous_snd).continuousOn)
      have hF : AEStronglyMeasurable
          (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r)
          (volume.restrict Work.Spaces.Iz) := by
        have h' := hjoint.integral_prod_right' (μ := volume.restrict Work.Spaces.Iz)
          (ν := volume.restrict Work.Spaces.Iθ)
        simpa only [Work.Elliptic.Fstar, Function.uncurry_apply_pair] using h'
      have hIcc : (volume.restrict (Set.Icc a b)) ≤ (volume.restrict Work.Spaces.Iz) :=
        MeasureTheory.Measure.restrict_mono
          (fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)) le_rfl
      have h2 : AEStronglyMeasurable
          (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r * r⁻¹)
          (volume.restrict (Set.Icc a b)) :=
        (hF.mono_measure hIcc).mul (measurable_inv.aestronglyMeasurable :
          AEStronglyMeasurable (fun r : ℝ => r⁻¹) (volume.restrict (Set.Icc a b)))
      exact h2.congr (Filter.Eventually.of_forall fun r => div_eq_mul_inv _ _)
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with r hr
      have har : a ≤ r := hr.1
      have hrpos : 0 < r := lt_of_lt_of_le ha har
      have hb := slice_bound hΨ hB j hj r hrpos
      have hnorm : |Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r|
          ≤ ∫ θ in Work.Spaces.Iθ, |Work.Spaces.DzIter j Ψ r θ| * Work.Elliptic.sinCos2 θ := by
        rw [Work.Elliptic.Fstar]
        refine (MeasureTheory.norm_integral_le_integral_norm
          (fun θ : ℝ => Work.Spaces.DzIter j Ψ r θ * Work.Elliptic.sinCos2 θ)).trans ?_
        refine le_of_eq ?_
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg_Iθ hθ)]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hrpos]
      have hdiv : |Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r| / r
          ≤ Bnd Ψ j r / r := div_le_div_of_nonneg_right (le_trans hnorm hb) (le_of_lt hrpos)
      have hdiv2 : Bnd Ψ j r / r ≤ (1 / a) * Bnd Ψ j r := by
        rw [div_eq_mul_inv, mul_comm (Bnd Ψ j r), one_div]
        exact mul_le_mul_of_nonneg_right (inv_anti₀ ha har) (Bnd_nonneg Ψ j r)
      linarith
  -- the base case and the induction
  have h0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 0 Ψ) z = 0 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h.orthPsi
  have hstep : ∀ j : ℕ, j ≤ 1 →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0) →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) Ψ) z = 0 := by
    intro j hj hW
    have hraw := Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_moment_chain
      (W := fun z => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z)
      (V := fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) Ψ) r / r)
      (fun s t hs hst => Fstar_DzIter_tower_Psi hΨ hB (by omega) hs hst) hW
      (fun a b ha hab => hInt (j + 1) (by omega) a b ha hab)
    filter_upwards [hraw, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    rw [div_eq_zero_iff] at hz
    rcases hz with h' | h'
    · exact h'
    · exact absurd h' hzpos.ne'
  intro j hj
  interval_cases j
  · simpa using h0
  · exact hstep 0 (by norm_num) h0
  · exact hstep 1 (by norm_num) (hstep 0 (by norm_num) h0)

/-! ## §8 The angular moment chain for `F` -/

/-- `F_*(D_z²F − D_zF)(z) = F_*(D_z²F)(z) − F_*(D_zF)(z)` for `z > 0`. -/
theorem Fstar_DzIter_sub (α : ℝ) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 2 F) {z : ℝ}
    (hz : 0 < z) :
    Work.Elliptic.Fstar (fun z θ => Work.Spaces.DzIter 2 F z θ
        - Work.Spaces.DzIter 1 F z θ) z
      = Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z := by
  have hI1 := Work.FTS.EllipticEst.integrableOn_DzIter_mul_sinCos2 α 2 hF hmem 1
    (by norm_num) hz
  have hI2 := Work.FTS.EllipticEst.integrableOn_DzIter_mul_sinCos2 α 2 hF hmem 2
    (by norm_num) hz
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => (Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
        * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => Work.Spaces.DzIter 2 F z θ * Work.Elliptic.sinCos2 θ
          - Work.Spaces.DzIter 1 F z θ * Work.Elliptic.sinCos2 θ from by
    funext θ; ring]
  rw [MeasureTheory.integral_sub hI2 hI1]

/-- **The angular moments of `D_z^j F` vanish a.e., `j ≤ 2`.** -/
theorem Fstar_DzIter_F_ae (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ j : ℕ, j ≤ 2 → ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z = 0 := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
  have hmem : Work.Spaces.HkMem α 2 F := h.memF
  have hInt : ∀ j : ℕ, j ≤ 2 → ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r)
        volume a b := by
    intro j hj a b ha hab
    have h1 := Work.FTS.EllipticEst.integrableOn_Bmom_div α 2 hF hmem j hj a b ha hab
    have h2 : IntegrableOn
        (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r) (Set.Icc a b) :=
      h1.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => by
        show Work.FTS.EllipticEst.Bmom F j r / r
          = Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r
        rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]))
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact h2
  have h0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar F z = 0 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h.orthF
  have h1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0 := by
    have hraw := Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_moment_chain
      (W := Work.Elliptic.Fstar F)
      (V := fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) r / r)
      (fun s t hs hst => Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α 2 F hF
        hmem 0 (by norm_num) hs hst)
      h0 (hInt 1 (by norm_num))
    filter_upwards [hraw, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    rw [div_eq_zero_iff] at hz
    rcases hz with h' | h'
    · exact h'
    · exact absurd h' hzpos.ne'
  have h2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0 := by
    have hraw := Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_moment_chain
      (W := Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F))
      (V := fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) r / r)
      (fun s t hs hst => Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α 2 F hF
        hmem 1 (by norm_num) hs hst)
      h1 (hInt 2 (by norm_num))
    filter_upwards [hraw, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    rw [div_eq_zero_iff] at hz
    rcases hz with h' | h'
    · exact h'
    · exact absurd h' hzpos.ne'
  intro j hj
  interval_cases j
  · simpa using h0
  · exact h1
  · exact h2

/-! ## §9 The two moment conditions of the twisted datum -/

/-- `F_*` only depends on the integrand a.e. in `θ`. -/
theorem Fstar_congr_ae {f g : ℝ → ℝ → ℝ} {z : ℝ}
    (h : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), f z θ = g z θ) :
    Work.Elliptic.Fstar f z = Work.Elliptic.Fstar g z := by
  show (∫ θ in Work.Spaces.Iθ, f z θ * Work.Elliptic.sinCos2 θ)
    = ∫ θ in Work.Spaces.Iθ, g z θ * Work.Elliptic.sinCos2 θ
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with θ hθ
  rw [hθ]

theorem Aof_Gof_moments (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Aof Ψ) z = 0) ∧
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Gof F) z = 0) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ) := h.memB
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
  constructor
  · -- `F_*(z²∂_z²Ψ) = F_*(D_z²Ψ) − F_*(D_zΨ) = 0` a.e.
    have hmom := Fstar_DzIter_Psi_ae h
    filter_upwards [hmom 2 (by norm_num), hmom 1 (by norm_num),
      MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz2 hz1 hzpos
    have hsl2 : IntegrableOn
        (fun θ => Work.Spaces.DzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      (Work.FTS.EllipticEst.Mine.SliceMomentTaylor
        (contDiffOn_slice_two (hΨ.DzIter 2) hzpos)
        (integrableOn_pthIter2_slice hΨ hB 2 (by norm_num) hzpos)).1
    have hsl1 : IntegrableOn
        (fun θ => Work.Spaces.DzIter 1 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      (Work.FTS.EllipticEst.Mine.SliceMomentTaylor
        (contDiffOn_slice_two (hΨ.DzIter 1) hzpos)
        (integrableOn_pthIter2_slice hΨ hB 1 (by norm_num) hzpos)).1
    have hcongr : Work.Elliptic.Fstar (Aof Ψ) z
        = Work.Elliptic.Fstar (fun z θ => Work.Spaces.DzIter 2 Ψ z θ
            - Work.Spaces.DzIter 1 Ψ z θ) z :=
      Fstar_congr_ae (by
        filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
          (fun θ hθ => zsq_pzIter2_eq_open hΨ hzpos hθ)] with θ hθ
        show Aof Ψ z θ = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ
        rw [Aof_apply, hθ])
    have hsub : Work.Elliptic.Fstar (fun z θ => Work.Spaces.DzIter 2 Ψ z θ
          - Work.Spaces.DzIter 1 Ψ z θ) z
        = Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z
          - Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z := by
      rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar]
      rw [show (fun θ : ℝ => (Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ)
            * Work.Elliptic.sinCos2 θ)
          = fun θ : ℝ => Work.Spaces.DzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ
              - Work.Spaces.DzIter 1 Ψ z θ * Work.Elliptic.sinCos2 θ from by
        funext θ; ring]
      rw [MeasureTheory.integral_sub hsl2 hsl1]
    rw [hcongr, hsub, hz2, hz1, sub_self]
  · -- `F_*(z²∂_z²F) = F_*(D_z²F) − F_*(D_zF) = 0` a.e.
    have hmom := Fstar_DzIter_F_ae α F Ψ h
    filter_upwards [hmom 2 (by norm_num), hmom 1 (by norm_num),
      MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz2 hz1 hzpos
    have hcongr : Work.Elliptic.Fstar (Gof F) z
        = Work.Elliptic.Fstar (fun z θ => Work.Spaces.DzIter 2 F z θ
            - Work.Spaces.DzIter 1 F z θ) z := rfl
    rw [hcongr, Fstar_DzIter_sub α hF h.memF hzpos, hz2, hz1, sub_self]

end AeDataAofAux

/-! ## The target -/

/-- **The twisted datum `(z²∂_z²Ψ, z²∂_z²F)` is a datum of the a.e. class `AeData`.**
See the module docstring for the provenance of each field. -/
theorem AeDataAof (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    Work.FTS.EllipticEst.H2W.Ae.AeData α
      (Work.FTS.EllipticEst.H2W.Aof Ψ) (Work.FTS.EllipticEst.H2W.Gof F) := by
  obtain ⟨-, -, hAsm, -⟩ := Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0
  obtain ⟨hmomA, hmomG⟩ := AeDataAofAux.Aof_Gof_moments α F Ψ h
  refine ⟨hα, hα4, AeDataAofAux.bslOp_Aof_eq_Gof α h, ?_, ?_, ?_, ?_, ?_, ?_,
    hmomA, hmomG⟩
  · -- `A Ψ` vanishes on the `θ = 0` line
    intro z
    show Work.FTS.EllipticEst.H2W.Aof Ψ z 0 = 0
    rw [Aof_apply, AeDataAofAux.pzIter_two_eq_zero_of_slice_zero (fun z => h.zero z) z,
      mul_zero]
  · -- `A Ψ` vanishes on the `θ = π/2` line
    intro z
    show Work.FTS.EllipticEst.H2W.Aof Ψ z (Real.pi / 2) = 0
    rw [Aof_apply, AeDataAofAux.pzIter_two_eq_zero_of_slice_zero (fun z => h.pi_half z) z,
      mul_zero]
  · -- smoothness of `A Ψ` on the open quadrant
    intro n
    exact hAsm.forall n
  · -- `G F ∈ ℋ⁰`
    have hFsm : Work.FTS.EllipticEst.SmoothOpen F :=
      (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
    have hz := AeDataAofAux.HkMem_zero_zsq_pzIter2 α hFsm h.memF
    refine AeDataAofAux.HkMem_zero_congr (f := Gof F)
      (g := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 F z θ) ?_ ?_ hz
    · exact ((hFsm.DzIter 2).continuousOn).sub ((hFsm.DzIter 1).continuousOn)
    · intro z θ hz0 hθ0 hθ1
      show Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ
        = z ^ 2 * Work.Spaces.pzIter 2 F z θ
      exact (AeDataAofAux.zsq_pzIter2_eq_open hFsm hz0 ⟨hθ0, hθ1⟩).symm
  · -- `z²∂_z²(A Ψ) ∈ ℋ⁰`, from `A Ψ ∈ ℋ²`
    exact AeDataAofAux.HkMem_zero_zsq_pzIter2 α hAsm h.memA
  · -- `∂_θ²(A Ψ) ∈ ℋ⁰`
    exact AeDataAofAux.HkMem_zero_pthIter2_zsq_pzIter2
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth) h.memB

end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two =====
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
set_option maxHeartbeats 800000

/-- **The angular moment of `D_z F` vanishes for `k ≥ 2`.**

For `k ≥ 2` the moment chain `F_*(D_z^j F) z - F_*(D_z^j F) s = ∫_s^z F_*(D_z^{j+1}F) r/r dr`
(`FstarDzIter_chain_open`) is available *both* at `j = 0` and at `j = 1`.  From `j = 0`, with
`F_*(F) ≡ 0` (the hypothesis), the primitive of `r ↦ F_*(D_zF)(r)/r` vanishes identically, so
`F_*(D_zF) = 0` almost everywhere; from `j = 1` that function is itself an indefinite integral of
the locally integrable function `r ↦ F_*(D_z^2F)(r)/r`, hence continuous; a continuous function
which vanishes almost everywhere is identically zero.

This is the `F`-half of the removal of the lower-order term: it says that in the weak class
`EllWeakPos α k F Ψ` with `k ≥ 2` the radially differentiated data `(D_z F, D_z Ψ)` is again
orthogonal, which is what the induction hypothesis at level `k - 1` consumes. -/
theorem Fstar_DzIter_one_F_ge_two {α : ℝ} {k : ℕ} (hk : 2 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0 := by
  -- the source is `C^∞` on the open quadrant
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    (smoothOpen_slices_weak h 0).1
  -- and honestly in `ℋ¹`
  have hmem1 : Work.Spaces.HkMem α 1 F :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (by omega : 1 ≤ k)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hF) h.memF
  -- `B₁ = F_*(D_zF)` vanishes almost everywhere on `(0,∞)`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.FTS.EllipticEst.Bmom F 1 z = 0 := by
    have hd := Work.FTS.EllipticEst.Cert.radIter_bmom_ae_hasDerivAt α 1 hF hmem1
      (le_refl 1)
    rw [show (1 : ℕ) - 1 = 0 from rfl, MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hd
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hd] with z hzimp hzmem
    have hz0 : 0 < z := hzmem
    have hev : (fun w : ℝ => Work.FTS.EllipticEst.Bmom F 0 w) =ᶠ[𝓝 z]
        (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz0] with w hw
      rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
      simpa using h.orthF w hw
    have hder0 : HasDerivAt (fun _ : ℝ => (0 : ℝ))
        (Work.FTS.EllipticEst.Bmom F 1 z / z) z :=
      hev.hasDerivAt_iff.mp (hzimp hzmem)
    have hval : Work.FTS.EllipticEst.Bmom F 1 z / z = 0 :=
      (hder0.unique (hasDerivAt_const z 0))
    rw [div_eq_zero_iff] at hval
    rcases hval with h' | h'
    · exact h'
    · exact absurd h' hz0.ne'
  -- `B₁` is continuous on `(0,∞)`
  have hcont : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.Bmom F 1 z) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.radIter_bmom_continuousOn α k hF h.memF 1 (by omega)
  -- hence it is everywhere zero
  have hEq := MeasureTheory.Measure.eqOn_of_ae_eq hae hcont continuousOn_const
    (fun x hx => by rw [interior_Ioi]; exact subset_closure hx)
  intro z hz
  rw [← Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
  exact hEq hz

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.HkSq_step_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-!
# Integrating the pointwise induction step for `HkSq`

`Step.HkIntegrand_step_le` (in `EllEstUnifStepAux`) is the *pointwise* statement that the
level-`k` integrand `HkIntegrand α k f` is dominated on the open quadrant by the level-`(k-1)`
integrand, the level-`(k-1)` integrand of `D_z f` and the single top angular slot
`(mixed 0 k f · Wt)²`.

This file performs the (measure-theoretic) passage to the corresponding statement for the
squared norms `HkSq α k f = ∫∫ HkIntegrand α k f`.  Three things have to be supplied.

* The existing pointwise lemmas are stated for `ContDiffOn ℝ ⊤`, which in this Mathlib is
  *analyticity* (`ContDiffOn 𝕜 ⊤ f s → AnalyticOn 𝕜 f s`), while the hypothesis of the target
  is only `∀ n : ℕ, ContDiffOn ℝ n`, i.e. `C^∞` (`Work.Stability.smoothOrder`).  So the
  pointwise machinery is re-derived here at the genuine smooth order: the commutation
  `D_z (D_θ^i g) = D_θ^i (D_z g)` on the open quadrant (`DzDthIterCommOn_smooth`, using the
  `C^∞`-calculus `Work.FTS.LocData.contDiffOn_DzIter` of `SmoothChain`), and the two pointwise
  bounds `HkIntegrand_step_le_smooth` and `HkIntegrand_shift_le_smooth`.
* *Almost everywhere*: the pointwise bound only holds on the open quadrant `Qd`, which is
  co-null for the measure `(volume.restrict Iz).prod (volume.restrict Iθ)`.
* *Integrability* of the right-hand side: the level-`(k-1)` integrand of `D_z f` is a.e.
  dominated by a multiple of the level-`k` integrand of `f`, which is integrable by
  hypothesis, and the remaining two summands are honest slots of `HkIntegrand α k f`; joint
  measurability comes from the smoothness of `f` on the open quadrant
  (`Work.Spaces.aesm_of_continuousOn_Qd`).

All the bookkeeping is done on the product measure, where the iterated integrals of `HkSq`
are rewritten with `MeasureTheory.setIntegral_prod`.
-/

/-- The open quadrant `(0,∞) × (0,π/2)`, the set on which the pointwise step holds. -/
private def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

private lemma isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

private lemma sin_two_pos_Qd {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-! ## Continuity of the pieces of the integrand on the open quadrant -/

private lemma continuousOn_DzIter_Qd (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i g p.1 p.2) Qd :=
  (Work.FTS.LocData.contDiffOn_DzIter isOpen_Qd hg i).continuousOn

private lemma continuousOn_mixed_Qd (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2) Qd :=
  (Work.FTS.LocData.contDiffOn_mixed isOpen_Qd hg j i).continuousOn

private lemma continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  simp only [Work.Spaces.w]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt hp.1)

private lemma continuousOn_sinpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_Qd hp.2)))

private lemma continuousOn_Wt_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  exact continuousOn_w_Qd.mul (continuousOn_sinpow_Qd (-(Work.Spaces.gam α / 2)))

private lemma continuousOn_wdivsin_Qd :
    ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      Qd :=
  continuousOn_w_Qd.div (continuousOn_sinpow_Qd (Work.Spaces.eta / 2))
    (fun _p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_Qd hp.2) _))

/-- The `H^k` integrand is continuous on the open quadrant. -/
private lemma continuousOn_HkIntegrand_Qd (α : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α m g p.1 p.2) Qd := by
  simp only [Work.Spaces.HkIntegrand]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (m + 1)) (fun i _ => ?_)
    exact (((continuousOn_DzIter_Qd g hg i).mul continuousOn_wdivsin_Qd).pow 2)
  · refine continuousOn_finsetSum (Finset.range (m + 1)) (fun i _ =>
      continuousOn_finsetSum (Finset.range (m + 1)) (fun j _ => ?_))
    split_ifs with h
    · exact (((continuousOn_mixed_Qd g hg j i).mul (continuousOn_Wt_Qd α)).pow 2)
    · exact continuousOn_const

/-- A single weighted mixed slot is continuous on the open quadrant. -/
private lemma continuousOn_mixed_sq_Wt_Qd (α : ℝ) (j i : ℕ) (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd) :
    ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      Qd :=
  (((continuousOn_mixed_Qd g hg j i).mul (continuousOn_Wt_Qd α)).pow 2)

/-! ## `D_z` commutes with the iterates of `D_θ` at the genuine smooth order -/

/-- `D_z (D_θ^i g) = D_θ^i (D_z g)` on an open set on which `g` is `C^∞`.  This is the
analogue of `Work.Spaces.DzDthIterCommOn` for the genuine smooth order
`Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞)`, which is the order supplied by the
hypothesis `∀ n, ContDiffOn ℝ n` of `HkSq_step_le`. -/
private theorem DzDthIterCommOn_smooth {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hF : ContDiffAt ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (Work.FTS.LocData.contDiffOn_DthIter hV hg i).contDiffAt (hV.mem_nhds hy)
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i g)
          (hF.of_le (by simp [Work.Stability.smoothOrder]))
      show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
        = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2)
              * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-- **The diagonal slots shift**: for `1 ≤ i` and `i ≤ k - 1` the slot `D_z^{k-i}D_θ^i f` of
level `k` is the slot `D_z^{k-1-i}D_θ^i (D_z f)` of the shifted integrand. -/
private lemma mixed_diag_apply_smooth {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k - 1)
    (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) :
    Work.Spaces.mixed (k - i) i f z θ
      = Work.Spaces.mixed (k - 1 - i) i (Work.Spaces.Dz f) z θ := by
  have h1 : k - i = k - 1 - i + 1 := by omega
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Qd :=
    DzDthIterCommOn_smooth isOpen_Qd hg i
  have hpt : (z, θ) ∈ Qd := ⟨hz, hθ⟩
  show Work.Spaces.DzIter (k - i) (Work.Spaces.DthIter i f) z θ
    = Work.Spaces.DzIter (k - 1 - i) (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
  rw [h1, ← Step.DzIter_Dz (k - 1 - i) (Work.Spaces.DthIter i f)]
  exact Step.DzIter_congr_of_isOpen isOpen_Qd hcomm (k - 1 - i) hpt

/-- The shifted mixed slots: `D_z^j D_θ^i (D_z f) = D_z^{j+1}D_θ^i f` on the open quadrant. -/
private lemma mixed_shift_apply_smooth {j i : ℕ} (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Qd :=
    DzDthIterCommOn_smooth isOpen_Qd hg i
  have hpt : (z, θ) ∈ Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    Step.DzIter_congr_of_isOpen isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, Step.DzIter_Dz j (Work.Spaces.DthIter i f)]

/-! ## The two pointwise bounds at the genuine smooth order -/

/-- **The pointwise step**: the level-`k` integrand is bounded by the level-`(k-1)`
integrand, the level-`(k-1)` integrand of `D_z f` and the single top angular slot. -/
private theorem HkIntegrand_step_le_smooth {k : ℕ} (hk : 1 ≤ k) (α : ℝ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) :
    Work.Spaces.HkIntegrand α k f z θ ≤
      Work.Spaces.HkIntegrand α (k - 1) f z θ
        + ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
        + (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ :=
    Work.Spaces.HkIntegrand_nonneg α (k - 1) (Work.Spaces.Dz f) z θ
  have hzterm : (Work.Spaces.DzIter k f z θ * Step.Zu z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
    rw [Step.DzIter_eq_DzIter_Dz hk f]
    exact Work.Spaces.sq_le_HkIntegrand_z α (k - 1) (Work.Spaces.Dz f) z θ (k - 1) le_rfl
  have hD : (∑ i ∈ Finset.range k,
        (if 1 ≤ i then (Work.Spaces.mixed (k - i) i f z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (if 1 ≤ i then (Work.Spaces.mixed (k - i) i f z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
          ≤ Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
      intro i hi
      have hik : i ≤ k - 1 := by
        have := Finset.mem_range.mp hi
        omega
      by_cases hi1 : 1 ≤ i
      · rw [if_pos hi1]
        rw [mixed_diag_apply_smooth hi1 hik f hz hθ hg]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α (k - 1) (Work.Spaces.Dz f) z θ i
          (k - 1 - i) hi1 (by omega)
      · rw [if_neg hi1]
        exact hHnn
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hkey : (Work.Spaces.DzIter k f z θ * Step.Zu z θ) ^ 2
      + (∑ i ∈ Finset.range k,
          (if 1 ≤ i then (Work.Spaces.mixed (k - i) i f z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0))
      ≤ ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
    nlinarith [hzterm, hD, hHnn]
  rw [Step.HkIntegrand_eq α k f, Step.HkIntegrand_eq α (k - 1) f,
    Step.Zsum_succ hk f z θ, Step.Msum_succ hk α f z θ]
  linarith [hkey]

/-- **The shifted integrand is dominated by the level-`k` integrand** (every slot of the
shifted integrand is a slot of the level-`k` integrand, and each single slot is dominated by
the whole integrand). -/
private theorem HkIntegrand_shift_le_smooth (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [Step.DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2 := by
      unfold Step.Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Step.Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Step.Msum_eq_rows, show k - 1 + 1 = k from by omega]
    have hterm : ∀ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hstep : (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _j ∈ Finset.range (k - i), Work.Spaces.HkIntegrand α k f z θ := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        by_cases hi1 : 1 ≤ i
        · rw [if_pos hi1]
          rw [mixed_shift_apply_smooth f hz hθ hg]
          have hj' : i + (j + 1) ≤ k := by
            have := Finset.mem_range.mp hj
            omega
          exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hi1 hj'
        · rw [if_neg hi1]
          exact hHnn
      refine le_trans hstep ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : k - i ≤ k := by omega
        exact_mod_cast this
      have hci : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) := by positivity
      nlinarith [hHnn, hcast, hci]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ _i ∈ Finset.range k, (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ)
        = ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hsum.le
  rw [Step.HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [Step.HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Step.Zsum k f z θ + Step.Msum α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]

/-! ## Almost everywhere statements on the product measure -/

/-- A pointwise inequality on the open quadrant holds almost everywhere for the measure
`(volume.restrict Iz).prod (volume.restrict Iθ)`, since the open quadrant agrees with
`Iz ×ˢ Iθ` up to a null set. -/
private lemma ae_le_of_forall_on_Qd {F G : ℝ × ℝ → ℝ} (h : ∀ p ∈ Qd, F p ≤ G p) :
    F ≤ᵐ[(volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)] G := by
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume] Qd :=
    MeasureTheory.Measure.set_prod_ae_eq
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  rw [MeasureTheory.Measure.prod_restrict, Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_of_forall_mem isOpen_Qd.measurableSet h

/-- Monotonicity of the `H^k` integrand in the regularity index. -/
private lemma HkIntegrand_le_of_le (α : ℝ) {m n : ℕ} (hmn : m ≤ n) (f : ℝ → ℝ → ℝ)
    (z θ : ℝ) :
    Work.Spaces.HkIntegrand α m f z θ ≤ Work.Spaces.HkIntegrand α n f z θ :=
  Nat.le_induction le_rfl
    (fun l _ ih => le_trans ih (Work.Spaces.HkIntegrand_mono α l f z θ)) n hmn

/-- Integrability of a nonnegative function that is a.e. dominated by an integrable one. -/
private lemma integrable_of_le_of_nonneg {F G : ℝ × ℝ → ℝ} {ν : Measure (ℝ × ℝ)}
    (hF : ∀ p, 0 ≤ F p) (hG : Integrable G ν) (hFG : ∀ᵐ p ∂ν, F p ≤ G p)
    (hmeas : AEStronglyMeasurable F ν) : Integrable F ν :=
  hG.mono' hmeas (hFG.mono fun p hp => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hF p)]
    exact hp)

/-! ## The induction step for `HkSq` -/

theorem HkSq_step_le {k : ℕ} (hk : 1 ≤ k) (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hcd : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkSq α k f ≤ Work.Spaces.HkSq α (k - 1) f
      + ((k : ℝ) + 1) * Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f)
      + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  have hcdtop : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd := by
    have h' : ContDiffOn ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (Function.uncurry f) Qd := by
      rw [contDiffOn_iff_forall_nat_le]
      exact fun m _ => hcd m
    exact h'
  have hDz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dz f)) Qd :=
    Work.FTS.LocData.contDiffOn_Dz isOpen_Qd hcdtop
  have hk1 : k - 1 ≤ k := by omega
  -- the four integrands and the bounding function, on the product space
  set A : ℝ × ℝ → ℝ := fun p => Work.Spaces.HkIntegrand α k f p.1 p.2 with eA
  set A1 : ℝ × ℝ → ℝ := fun p => Work.Spaces.HkIntegrand α (k - 1) f p.1 p.2 with eA1
  set A2 : ℝ × ℝ → ℝ :=
    fun p => Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) p.1 p.2 with eA2
  set A3 : ℝ × ℝ → ℝ :=
    fun p => (Work.Spaces.mixed 0 k f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2 with eA3
  set F1 : ℝ × ℝ → ℝ := fun p => A1 p + ((k : ℝ) + 1) * A2 p with eF1
  set B : ℝ × ℝ → ℝ := fun p => F1 p + A3 p with eB
  set μ : Measure (ℝ × ℝ) :=
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) with eMu
  -- strong measurability, from continuity on the open quadrant
  have hA_aesm : AEStronglyMeasurable A μ := by
    rw [eA, eMu]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_HkIntegrand_Qd α k f hcdtop)
  have hA1_aesm : AEStronglyMeasurable A1 μ := by
    rw [eA1, eMu]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_HkIntegrand_Qd α (k - 1) f hcdtop)
  have hA2_aesm : AEStronglyMeasurable A2 μ := by
    rw [eA2, eMu]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_HkIntegrand_Qd α (k - 1) (Work.Spaces.Dz f) hDz)
  have hA3_aesm : AEStronglyMeasurable A3 μ := by
    rw [eA3, eMu]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_mixed_sq_Wt_Qd α 0 k f hcdtop)
  -- integrability of the level-`k` integrand, from the hypothesis `HkMem α k f`
  have hA_prod : Integrable A μ := by
    rw [eMu]
    rw [integrable_prod_iff hA_aesm]
    constructor
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
      rw [eA]
      exact hmem.1 z hz
    · refine hmem.2.congr ?_
      filter_upwards with z
      rw [eA]
      exact integral_congr_ae (Eventually.of_forall fun θ => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)])
  -- the three summands of the right-hand side
  have hA1_le : ∀ p, A1 p ≤ A p := fun p => by
    rw [eA1, eA]
    exact HkIntegrand_le_of_le α hk1 f p.1 p.2
  have hA1_int : Integrable A1 μ :=
    integrable_of_le_of_nonneg
      (fun p => by rw [eA1]; exact Work.Spaces.HkIntegrand_nonneg α (k - 1) f p.1 p.2)
      hA_prod (Eventually.of_forall hA1_le) hA1_aesm
  have hA3_le : ∀ p, A3 p ≤ A p := fun p => by
    rw [eA3, eA]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k f p.1 p.2 k 0 hk (by omega)
  have hA3_int : Integrable A3 μ :=
    integrable_of_le_of_nonneg
      (fun p => by rw [eA3]; exact sq_nonneg _)
      hA_prod (Eventually.of_forall hA3_le) hA3_aesm
  have hA2_le : ∀ p ∈ Qd, A2 p ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * A p := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    rw [eA2, eA]
    exact HkIntegrand_shift_le_smooth α hk f hz hθ hcdtop
  have hA2_bound : A2 ≤ᵐ[μ] fun p => ((k : ℝ) + (k : ℝ) * (k : ℝ)) * A p := by
    rw [eMu]
    exact ae_le_of_forall_on_Qd hA2_le
  have hA2_int : Integrable A2 μ :=
    integrable_of_le_of_nonneg
      (fun p => by
        rw [eA2]; exact Work.Spaces.HkIntegrand_nonneg α (k - 1) (Work.Spaces.Dz f) p.1 p.2)
      (hA_prod.const_mul _) hA2_bound hA2_aesm
  have hCA2_int : Integrable (fun p => ((k : ℝ) + 1) * A2 p) μ := hA2_int.const_mul _
  have hF1_int : Integrable F1 μ := by
    rw [eF1]
    exact hA1_int.add hCA2_int
  have hB_int : Integrable B μ := by
    rw [eB]
    exact hF1_int.add hA3_int
  -- the pointwise step, integrated
  have hA_le_B_pt : ∀ p ∈ Qd, A p ≤ B p := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    rw [eA, eB, eF1, eA1, eA2, eA3]
    exact HkIntegrand_step_le_smooth hk α f hz hθ hcdtop
  have hA_le_B : A ≤ᵐ[μ] B := by
    rw [eMu]
    exact ae_le_of_forall_on_Qd hA_le_B_pt
  have hA_nn : 0 ≤ᵐ[μ] A := Eventually.of_forall fun p => by
    rw [eA]; exact Work.Spaces.HkIntegrand_nonneg α k f p.1 p.2
  have hmain : ∫ p, A p ∂μ ≤ ∫ p, B p ∂μ :=
    integral_mono_of_nonneg hA_nn hB_int hA_le_B
  -- splitting the right-hand side
  have hsplitF1 : ∫ p, F1 p ∂μ
      = ∫ p, A1 p ∂μ + ∫ p, ((k : ℝ) + 1) * A2 p ∂μ := by
    rw [eF1]
    exact integral_add hA1_int hCA2_int
  have hsplit : ∫ p, B p ∂μ
      = (∫ p, A1 p ∂μ) + ((k : ℝ) + 1) * (∫ p, A2 p ∂μ) + ∫ p, A3 p ∂μ := by
    have h1 : ∫ p, B p ∂μ = ∫ p, F1 p ∂μ + ∫ p, A3 p ∂μ := by
      rw [eB]
      exact integral_add hF1_int hA3_int
    have h2 : ∫ p, F1 p ∂μ
        = (∫ p, A1 p ∂μ) + ((k : ℝ) + 1) * (∫ p, A2 p ∂μ) := by
      rw [hsplitF1, integral_const_mul]
    rw [h1, h2]
  -- product integrability of the pieces, and the conversion of the integrals
  have hA_prod' : Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [← MeasureTheory.Measure.prod_restrict, ← eMu]
    exact hA_prod
  have hA1_prod' : Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α (k - 1) f p.1 p.2)
      ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [← MeasureTheory.Measure.prod_restrict, ← eMu]
    exact hA1_int
  have hA2_prod' : Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) p.1 p.2)
      ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [← MeasureTheory.Measure.prod_restrict, ← eMu]
    exact hA2_int
  have hA3_prod' : Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed 0 k f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [← MeasureTheory.Measure.prod_restrict, ← eMu]
    exact hA3_int
  have hA_eq : ∫ p, A p ∂μ
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    rw [eA, eMu, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.setIntegral_prod
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2) hA_prod'
  have hA1_eq : ∫ p, A1 p ∂μ = Work.Spaces.HkSq α (k - 1) f := by
    rw [eA1, eMu, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.setIntegral_prod
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α (k - 1) f p.1 p.2) hA1_prod'
  have hA2_eq : ∫ p, A2 p ∂μ = Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f) := by
    rw [eA2, eMu, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.setIntegral_prod
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) p.1 p.2)
      hA2_prod'
  have hA3_eq : ∫ p, A3 p ∂μ
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [eA3, eMu, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.setIntegral_prod
      (fun p : ℝ × ℝ => (Work.Spaces.mixed 0 k f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      hA3_prod'
  calc Work.Spaces.HkSq α k f
      = ∫ p, A p ∂μ := hA_eq.symm
    _ ≤ ∫ p, B p ∂μ := hmain
    _ = (∫ p, A1 p ∂μ) + ((k : ℝ) + 1) * (∫ p, A2 p ∂μ) + ∫ p, A3 p ∂μ := hsplit
    _ = Work.Spaces.HkSq α (k - 1) f
          + ((k : ℝ) + 1) * Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f)
          + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        rw [hA1_eq, hA2_eq, hA3_eq]

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TracesAux

set_option maxHeartbeats 1600000

/-! ## A factor which depends only on `z` is `SmoothOpen`

`Work.FTS.EllipticEst.SmoothOpen` is genuine `C^∞` (the order `Work.Stability.smoothOrder`) on
the open quadrant `Q0 = (0,∞) × (0,π/2)`.  A function of `z` alone which is `C^∞` on `(0,∞)`
therefore belongs to it. -/

theorem smoothOpen_zOnly {ψ : ℝ → ℝ} (hψ : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => ψ z) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  exact (hψ n).comp contDiff_fst.contDiffOn
    (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-! ## `Zop = z ∂_z` as a derivation on the smooth functions of `(0,∞)`

This is `Work.FTS.LocData.Zop_DerivLike_smoothZd` with the strip `(-1,∞)` replaced by the
half-line `(0,∞)` — the base set on which `SmoothOpen` gives slice smoothness. -/

/-- The functions of one variable which are `C^∞` on `(0,∞)` in the genuine smooth order
`Work.Stability.smoothOrder = ((⊤ : ℕ∞) : ℕ∞ω)`, *not* in the analytic order `⊤`. -/
def SmoothZsm0 (u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder u (Set.Ioi 0)

/-- `SmoothZsm0` is closed under `+`, `*` and scalar multiples. -/
theorem SmoothZsm0_FunClass : Work.Spaces.FunClass SmoothZsm0 where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    show ContDiffOn ℝ Work.Stability.smoothOrder (fun p => c * A p) (Set.Ioi 0)
    exact ContDiffOn.const_smul c hA

/-- **`Zop u = fun z => z · u'(z)`** is a derivation-like operator on the functions `C^∞` on
`(0,∞)`, in the exact sense of `Work.Spaces.DerivLike`. -/
theorem Zop_DerivLike_smoothZ0 :
    Work.Spaces.DerivLike (Set.Ioi (0 : ℝ)) SmoothZsm0 Work.Spaces.Zop where
  add := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    show Work.Spaces.Zop (A + B) z = Work.Spaces.Zop A z + Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    show Work.Spaces.Zop (A * B) z = Work.Spaces.Zop A z * B z + A z * Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    intro z hz
    show Work.Spaces.Zop A z = Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [h.deriv isOpen_Ioi hz]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ Work.Stability.smoothOrder (fderiv ℝ A) (Set.Ioi 0) :=
      hA.fderiv_of_isOpen isOpen_Ioi (by simp)
    have hev : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (fderiv ℝ A z) 1)
        (Set.Ioi 0) :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun z : ℝ => z * (fderiv ℝ A z) 1) (Set.Ioi 0) :=
      (contDiff_id.contDiffOn).mul hev
    refine hfun.congr (fun z hz => ?_)
    show Work.Spaces.Zop A z = z * (fderiv ℝ A z) 1
    simp only [Work.Spaces.Zop]
    rw [fderiv_apply_one_eq_deriv]
  smul := fun c A hA => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    show Work.Spaces.Zop (fun p => c * A p) z = c * Work.Spaces.Zop A z
    simp only [Work.Spaces.Zop]
    rw [deriv_const_mul c hA']
    ring

/-! ## Two elementary facts about `D_θ` and a `z`-only factor -/

/-- `deriv` is scalar homogeneous **unconditionally**, unlike Mathlib's `deriv_const_mul`,
which needs differentiability: if `f` is not differentiable at `x` then neither is `c * f`
for `c ≠ 0`, so both sides are `0`. -/
private theorem deriv_const_mul_uncond (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

/-- `D_θ^i` commutes with multiplication by a factor depending only on `z`.  No smoothness is
needed: the only ingredient is the unconditional scalar linearity of `deriv`. -/
private theorem DthIter_zmul0 (i : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => a z * f z θ)
      = fun z θ => a z * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [Work.Spaces.DthIter_succ] at ih ⊢
      rw [ih]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_uncond]
      ring

/-! ## The Leibniz expansion with a `z`-only factor, on the open quadrant -/

/-- **Leibniz expansion (open quadrant) of a mixed derivative of a product with a `z`-only
factor.**  For `ψ : ℝ → ℝ` of class `C^∞` on `(0,∞)` and `x` of class `SmoothOpen`, and for
`z > 0`, `θ ∈ (0,π/2)`,
`D_z^j D_θ^i(ψ·x)(z,θ) = ∑_{b ≤ j} C(j,b)·(Zop^b ψ)(z)·(D_z^{j-b}D_θ^i x)(z,θ)`.

`D_θ^i` commutes with the `z`-only factor (`DthIter_zmul0`, no smoothness needed), which reduces
the claim to the single-operator Leibniz rule for `Zop` on the `z`-slice; there both factors are
`C^∞` on `(0,∞)` (`SmoothZsm0`), so `Work.Spaces.DerivLike.iterate_mul` applies with the
instance `Zop_DerivLike_smoothZ0`, and `Work.FTS.LocData.Zop_iterate_slice` identifies the
iterates of `Zop` with the slices of the `D_z`-iterates. -/
theorem mixed_zmul_zOnly (j i : ℕ) (ψ : ℝ → ℝ) (x : ℝ → ℝ → ℝ)
    (hψ : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioi 0))
    (hx : Work.FTS.EllipticEst.SmoothOpen x)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.mixed j i (fun z θ : ℝ => ψ z * x z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (Work.Spaces.Zop^[b] ψ z * Work.Spaces.mixed (j - b) i x z θ) := by
  have hψs : SmoothZsm0 ψ := by
    show ContDiffOn ℝ Work.Stability.smoothOrder ψ (Set.Ioi 0)
    exact contDiffOn_iff_forall_nat_le.mpr (fun m _ => hψ m)
  have hxs : SmoothZsm0 (fun z : ℝ => Work.Spaces.DthIter i x z θ) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.Spaces.DthIter i x z θ) (Set.Ioi 0)
    exact (hx.DthIter i).curry_z hθ
  have key := (Work.Spaces.DerivLike.iterate_mul Zop_DerivLike_smoothZ0 SmoothZsm0_FunClass
    j hψs hxs) hz
  have hL : Work.Spaces.mixed j i (fun z θ : ℝ => ψ z * x z θ) z θ
      = Work.Spaces.Zop^[j] (ψ * (fun z : ℝ => Work.Spaces.DthIter i x z θ)) z := by
    rw [Work.Spaces.mixed, DthIter_zmul0 i ψ x]
    exact congrFun (Work.FTS.LocData.Zop_iterate_slice j
      (fun z θ => ψ z * Work.Spaces.DthIter i x z θ) θ) z
  rw [hL, key]
  apply Finset.sum_congr rfl
  intro b hb
  have h1 : Work.Spaces.Zop^[b] (fun z : ℝ => ψ z) z = Work.Spaces.Zop^[b] ψ z := rfl
  have h2 : Work.Spaces.Zop^[j - b] (fun z : ℝ => Work.Spaces.DthIter i x z θ) z
      = Work.Spaces.mixed (j - b) i x z θ := by
    rw [Work.Spaces.mixed]
    exact (congrFun (Work.FTS.LocData.Zop_iterate_slice (j - b)
      (Work.Spaces.DthIter i x) θ) z).symm
  rw [h1, h2]

/-! ## The pointwise bound -/

/-- **Pointwise bound for the mixed derivative of a radial multiple.**  For `z > 0` and
`0 < θ < π/2`, the square of any mixed derivative `D_z^bD_θ^a(ψ·x)`, weighted by an arbitrary
nonnegative factor `ρ`, is bounded by `(b+1)` times the corresponding combination of the mixed
derivatives of `x` (weighted by `ρ`), with coefficients `(C(b,c)·K)²`. -/
theorem mixed_psi_mul_sq_le_open {k : ℕ} {ψ : ℝ → ℝ} {K ρ : ℝ} (hK : 0 ≤ K) (hρ : 0 ≤ ρ)
    (hKb : ∀ c ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[c] ψ z| ≤ K)
    (hψ : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioi 0))
    {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {a b : ℕ} (hab : a + b ≤ k) {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ))
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ * (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2 ≤
      ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
        ((b.choose c : ℝ) * K) ^ 2 * (ρ * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) := by
  have hcore : (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2 ≤
      ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
        ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2 := by
    rw [mixed_zmul_zOnly b a ψ g hψ hg hz hθ]
    calc (∑ c ∈ Finset.range (b + 1),
            (b.choose c : ℝ) * (Work.Spaces.Zop^[c] ψ z * Work.Spaces.mixed (b - c) a g z θ)) ^ 2
        ≤ ((Finset.range (b + 1)).card : ℝ) * ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * (Work.Spaces.Zop^[c] ψ z
              * Work.Spaces.mixed (b - c) a g z θ)) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * (Work.Spaces.Zop^[c] ψ z
              * Work.Spaces.mixed (b - c) a g z θ)) ^ 2 := by
          simp
      _ ≤ ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Finset.sum_le_sum fun c hc => ?_
          have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
          have hsq : (Work.Spaces.Zop^[c] ψ z) ^ 2 ≤ K ^ 2 := by
            have h := pow_le_pow_left₀ (abs_nonneg (Work.Spaces.Zop^[c] ψ z))
              (hKb c (by omega) z hz) 2
            rwa [sq_abs] at h
          have e1 : ((b.choose c : ℝ) * (Work.Spaces.Zop^[c] ψ z
                * Work.Spaces.mixed (b - c) a g z θ)) ^ 2
              = ((b.choose c : ℝ) ^ 2 * (Work.Spaces.Zop^[c] ψ z) ^ 2)
                * (Work.Spaces.mixed (b - c) a g z θ) ^ 2 := by ring
          have e2 : ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2
              = ((b.choose c : ℝ) ^ 2 * K ^ 2)
                * (Work.Spaces.mixed (b - c) a g z θ) ^ 2 := by ring
          rw [e1, e2]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) (sq_nonneg _)
  calc ρ * (Work.Spaces.mixed b a (fun z θ => ψ z * g z θ) z θ) ^ 2
      ≤ ρ * (((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcore hρ
    _ = ((b : ℝ) + 1) * (ρ * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) := by ring
    _ = ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 * (ρ * (Work.Spaces.mixed (b - c) a g z θ) ^ 2) := by
        rw [Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun c _ => by ring

/-! ## The four traces -/

/-- **`BdryTraces` is preserved by multiplication with a bounded radial multiplier**
(open-quadrant version of `Work.FTS.CoercivityFix.PsiMul.BdryTraces_psi_mul`, which asks for
`SmoothQuad` of the factor and of the datum, i.e. `C^∞` on the *strip* `z > -1`).

For `ψ : ℝ → ℝ` of class `C^∞` on `(0,∞)` whose `Zop`-iterates `Zop^c ψ = (z∂_z)^c ψ`
(`Work.Spaces.Zop`) are bounded by `K` up to order `k`, and `x` of class `SmoothOpen`
(`C^∞` on the *open quadrant* `(0,∞) × (0,π/2)`) with `BdryTraces α k x`, the product
`(z,θ) ↦ ψ(z)·x(z,θ)` again has `BdryTraces α k`.

Route: `OpenPkg.ProdOpen.leibniz_open_mixed` expands the mixed derivative of the product of
two `SmoothOpen` factors on the quadrant; since `(z,θ) ↦ ψ z` is `SmoothOpen` (from `hψ`),
the terms with `a > 0` vanish and the expansion collapses to
`D_z^bD_θ^a(ψ·x) = Σ_{c≤b} C(b,c)·(Zop^c ψ)(z)·(D_z^{b-c}D_θ^a x)(z,θ)`,
in which every slot `(a, b-c)` has `a + (b-c) ≤ a + b ≤ k`, so the four traces of the product
are squeezed between `0` and a finite combination of the traces of `x`. -/
theorem BdryTraces_psi_mul_open {α : ℝ} (k : ℕ) {ψ : ℝ → ℝ} {K : ℝ}
    {x : Work.FTS.Galerkin.Fn}
    (hK : 0 ≤ K)
    (hZ : ∀ c : ℕ, c ≤ k → ∀ z : ℝ, 0 < z → |Work.Spaces.Zop^[c] ψ z| ≤ K)
    (hψ : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioi 0))
    (hxsm : Work.FTS.EllipticEst.SmoothOpen x)
    (hx : Work.FTS.Nonlin.BdryTraces α k x) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => ψ z * x z θ) := by
  have hKb : ∀ c ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[c] ψ z| ≤ K :=
    fun c hc z hz => hZ c hc z hz
  -- the two angular intervals are eventually true along the two one-sided filters
  have hIoo0 : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioo (-1) (π / 2), isOpen_Ioo,
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      fun x hx => ⟨hx.2, hx.1.2⟩⟩
  have hIooπ : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[<] (π / 2) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioo (π / 4) (π / 2 + 1), isOpen_Ioo,
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      fun x hx => ⟨by linarith [hx.1.1, Real.pi_pos], hx.2⟩⟩
  intro a b hab
  refine ⟨?_, ?_⟩
  · intro θ hθ
    refine ⟨?_, ?_⟩
    · -- radial trace at `z → 0⁺`
      refine squeeze_zero'
        (g := fun z => ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 *
            (z * (Work.Spaces.mixed (b - c) a x z θ * Work.Spaces.w z) ^ 2)) ?_ ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact mul_nonneg (le_of_lt hz) (sq_nonneg _)
      · filter_upwards [self_mem_nhdsWithin] with z hz
        have hbnd : (z * (Work.Spaces.w z) ^ 2) *
              (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ) ^ 2 ≤
              ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  ((z * (Work.Spaces.w z) ^ 2) * (Work.Spaces.mixed (b - c) a x z θ) ^ 2) :=
          mixed_psi_mul_sq_le_open hK
            (mul_nonneg (le_of_lt hz) (sq_nonneg (Work.Spaces.w z))) hKb hψ hxsm hab hz hθ
        calc z * (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ * Work.Spaces.w z) ^ 2
            = (z * (Work.Spaces.w z) ^ 2) *
                (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ) ^ 2 := by ring
          _ ≤ ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 * ((z * (Work.Spaces.w z) ^ 2) *
                  (Work.Spaces.mixed (b - c) a x z θ) ^ 2) := hbnd
          _ = ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  (z * (Work.Spaces.mixed (b - c) a x z θ * Work.Spaces.w z) ^ 2) := by
              congr 1
              exact Finset.sum_congr rfl fun c _ => by ring
      · have hsum : Tendsto (fun z => ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 *
              (z * (Work.Spaces.mixed (b - c) a x z θ * Work.Spaces.w z) ^ 2))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have h := tendsto_finsetSum (Finset.range (b + 1)) (fun c hc => by
            have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            exact (((hx a (b - c) (by omega)).1 θ hθ).1).const_mul
              (((b.choose c : ℝ) * K) ^ 2))
          simpa using h
        simpa using hsum.const_mul ((b : ℝ) + 1)
    · -- radial trace at `z → ∞`
      refine squeeze_zero'
        (g := fun z => ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 *
            (z * (Work.Spaces.mixed (b - c) a x z θ * Work.Spaces.w z) ^ 2)) ?_ ?_ ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        exact mul_nonneg (le_of_lt hz) (sq_nonneg _)
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        have hbnd : (z * (Work.Spaces.w z) ^ 2) *
              (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ) ^ 2 ≤
              ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  ((z * (Work.Spaces.w z) ^ 2) * (Work.Spaces.mixed (b - c) a x z θ) ^ 2) :=
          mixed_psi_mul_sq_le_open hK
            (mul_nonneg (le_of_lt hz) (sq_nonneg (Work.Spaces.w z))) hKb hψ hxsm hab hz hθ
        calc z * (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ * Work.Spaces.w z) ^ 2
            = (z * (Work.Spaces.w z) ^ 2) *
                (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ) ^ 2 := by ring
          _ ≤ ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 * ((z * (Work.Spaces.w z) ^ 2) *
                  (Work.Spaces.mixed (b - c) a x z θ) ^ 2) := hbnd
          _ = ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  (z * (Work.Spaces.mixed (b - c) a x z θ * Work.Spaces.w z) ^ 2) := by
              congr 1
              exact Finset.sum_congr rfl fun c _ => by ring
      · have hsum : Tendsto (fun z => ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 *
              (z * (Work.Spaces.mixed (b - c) a x z θ * Work.Spaces.w z) ^ 2))
            atTop (𝓝 0) := by
          have h := tendsto_finsetSum (Finset.range (b + 1)) (fun c hc => by
            have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            exact (((hx a (b - c) (by omega)).1 θ hθ).2).const_mul
              (((b.choose c : ℝ) * K) ^ 2))
          simpa using h
        simpa using hsum.const_mul ((b : ℝ) + 1)
  · intro z hz
    refine ⟨?_, ?_⟩
    · -- angular trace at `θ → 0⁺`
      refine squeeze_zero'
        (g := fun θ => ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 *
            (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b - c) a x z θ) ^ 2)) ?_ ?_ ?_
      · filter_upwards [hIoo0] with θ hθ
        have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))) _
        exact mul_nonneg hsin (sq_nonneg _)
      · filter_upwards [hIoo0] with θ hθ
        have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))) _
        have hbnd : Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
              (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ) ^ 2 ≤
              ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                    * (Work.Spaces.mixed (b - c) a x z θ) ^ 2) :=
          mixed_psi_mul_sq_le_open hK hsin hKb hψ hxsm hab hz hθ
        exact hbnd
      · have hsum : Tendsto (fun θ => ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 *
              (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                * (Work.Spaces.mixed (b - c) a x z θ) ^ 2))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have h := tendsto_finsetSum (Finset.range (b + 1)) (fun c hc => by
            have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            exact (((hx a (b - c) (by omega)).2 z hz).1).const_mul
              (((b.choose c : ℝ) * K) ^ 2))
          simpa using h
        simpa using hsum.const_mul ((b : ℝ) + 1)
    · -- angular trace at `θ → (π/2)⁻`
      refine squeeze_zero'
        (g := fun θ => ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
          ((b.choose c : ℝ) * K) ^ 2 *
            (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b - c) a x z θ) ^ 2)) ?_ ?_ ?_
      · filter_upwards [hIooπ] with θ hθ
        have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))) _
        exact mul_nonneg hsin (sq_nonneg _)
      · filter_upwards [hIooπ] with θ hθ
        have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))) _
        have hbnd : Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
              (Work.Spaces.mixed b a (fun z θ => ψ z * x z θ) z θ) ^ 2 ≤
              ((b : ℝ) + 1) * ∑ c ∈ Finset.range (b + 1),
                ((b.choose c : ℝ) * K) ^ 2 *
                  (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                    * (Work.Spaces.mixed (b - c) a x z θ) ^ 2) :=
          mixed_psi_mul_sq_le_open hK hsin hKb hψ hxsm hab hz hθ
        exact hbnd
      · have hsum : Tendsto (fun θ => ∑ c ∈ Finset.range (b + 1),
            ((b.choose c : ℝ) * K) ^ 2 *
              (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                * (Work.Spaces.mixed (b - c) a x z θ) ^ 2))
            (𝓝[<] (π / 2)) (𝓝 0) := by
          have h := tendsto_finsetSum (Finset.range (b + 1)) (fun c hc => by
            have hc' : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            exact (((hx a (b - c) (by omega)).2 z hz).2).const_mul
              (((b.choose c : ℝ) * K) ^ 2))
          simpa using h
        simpa using hsum.const_mul ((b : ℝ) + 1)

end Work.FTS.StrongEps.EpsE4Thr.TracesAux
end
end
