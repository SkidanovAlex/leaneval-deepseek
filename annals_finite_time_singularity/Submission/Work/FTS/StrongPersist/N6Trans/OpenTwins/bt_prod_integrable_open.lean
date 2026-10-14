import Mathlib
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Have
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.SolutionDelivery.Slices
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.holderWith_of_dist_le
-- ===== merged: Submission.Work.ConstructionInstance.Data =====
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

/-- `Work.Cyl.rho` is invariant under the reflection `Work.LWP.reflZ`. -/
theorem rho_reflZ (x : R3) : Work.Cyl.rho (Work.LWP.reflZ x) = Work.Cyl.rho x := by
  have h1 : Work.Cyl.radSq (Work.LWP.reflZ x) = Work.Cyl.radSq x := by
    simp [Work.Cyl.radSq, Work.LWP.reflZ]
  have h2 : Work.Cyl.axial (Work.LWP.reflZ x) = -Work.Cyl.axial x := by
    simp [Work.Cyl.axial, Work.LWP.reflZ]
  rw [Work.Cyl.rho, Work.Cyl.rho, h1, h2, neg_sq]

theorem flipZ_smul (c : ℝ) (v : R3) : Work.LWP.flipZ (c • v) = c • Work.LWP.flipZ v := by
  ext i
  fin_cases i <;> simp [Work.LWP.flipZ]

/-- The cut-off is applied to a field of parity `IsOddVorticity`: the radial cut-off factor is
invariant under `reflZ` and `flipZ` is linear, so the parity is preserved. -/
theorem isOddVorticity_cutDatum {L : ℝ} {ω : R3 → R3}
    (hω : Work.LWP.IsOddVorticity ω) :
    Work.LWP.IsOddVorticity (Work.SolutionDelivery.cutDatum L ω) := by
  intro x
  rw [Work.SolutionDelivery.cutDatum, Work.Stability.omegaCut, Work.Stability.omegaCut,
    rho_reflZ, hω x, flipZ_smul, smul_neg]

/-- **The `Cyl` rotation dictionary for the cut-off datum, unconditionally**: the Biot–Savart
field of `omega₀ p g L = χ(ρ/L)·omegaS p g` is axisymmetric without swirl.  Indeed `omegaS p g` is
of the form `f(radial, axial) • e_θ` (take
`f r z = profile p g (rhoP r z ^ p) (thetaP r z)`) and the cut-off factor is radial, so the same
holds for `omega₀`; `isAxiNoSwirl_biotSavart` (this directory, a proof by rotation equivariance of
the Boole integral) then applies.  No hypothesis on `g` is used. -/
theorem isAxiNoSwirl_omega₀ (p : ℝ) (g : ℝ → ℝ → ℝ) (L : ℝ) :
    Work.Cyl.IsAxiNoSwirl (Work.LWP.biotSavart (omega₀ p g L)) := by
  refine isAxiNoSwirl_biotSavart (f := fun r z =>
    Work.Stability.chi (Work.Cyl.rhoP r z / L) *
      profile p g (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z)) (fun x => ?_)
  have hrho : Work.Cyl.rho x = Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) := by
    rw [Work.Cyl.rho, Work.Cyl.rhoP, Work.Cyl.radial]
    congr 1
    simp only [Work.Cyl.radSq, Work.Cyl.axial]
    rw [Real.sq_sqrt (by positivity)]
  have hth : Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) := rfl
  rw [omega₀_apply, omegaS_apply', hrho, hth, smul_smul]

/-- **The residual interface of the construction.**  Every field is a statement about the objects
of another chapter; `NOTES.md` records which chapter delivers it and which are proved here. -/
structure ConstructionData (α : NNReal) where
  /-- the LWP chapter's analytic inputs -/
  lwp : Work.LWP.LWPInputs α
  /-- the perturbation `g` of the self-similar profile `F = F_* + g` -/
  g : ℝ → ℝ → ℝ
  /-- `g` vanishes on the two angular boundaries -/
  hvt : Work.Spaces.VanishTheta g
  /-- `g` is `C^∞` on a neighbourhood of the closed quadrant (the `St1`-class of the fixed point) -/
  hsmooth : Work.Stability.SmoothFar g
  /-- `g` vanishes at `z = 0` (`Work.Stability.QuadVanish`) -/
  hquad0 : ∀ θ : ℝ, g 0 θ = 0
  /-- `∂_z g` vanishes at `z = 0` (`Work.Stability.QuadVanish`) -/
  hquad : ∀ θ : ℝ, Work.Spaces.pz g 0 θ = 0
  /-- the `L^∞` bound of `g`, from `Work.Spaces.Linf_H2` and the `ℋ²`-bound of the fixed point -/
  Cg : ℝ
  /-- `Cg ≥ 0` -/
  hCg : 0 ≤ Cg
  /-- `|g| ≤ Cg` on the closed quadrant -/
  hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg
  /-- the scalar profile `x ↦ F(ρ(x)^p, θ(x))` is measurable in the physical variables (it is
  `C^∞` off the axis and the plane, and the odd extension is measurable); `Meas.lean` derives the
  measurability of the vector-valued vorticity from this -/
  hmeasP : MeasureTheory.AEStronglyMeasurable
    (fun x : R3 => profile (profExp α) g (Work.Cyl.Rc (profExp α) x) (Work.Cyl.theta x))
    MeasureTheory.volume
  /-- the `St1` cut-off parameter -/
  L : ℝ
  /-- `L > 0` -/
  hL : 0 < L
  /-- the **uniform angular vanishing** of the perturbation: `|g| ≤ Cv·Γ(α,θ)` (this is what
  makes `g` compatible with the `Γ`-vanishing of `F_*` and kills the direction jumps of `e_θ` near
  the axis) -/
  Cv : ℝ
  /-- `Cv ≥ 0` -/
  hCv : 0 ≤ Cv
  /-- `|g z θ| ≤ Cv·Γ(α,θ)` on the closed quadrant -/
  hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cv * Gamma (α : ℝ) θ
  /-- the **uniform radial modulus** of the perturbation: `|g(z,θ)-g(z',θ)| ≤ Lg·|z-z'|^α`
  (without it `omegaS` oscillates at the self-similar scale `z = ρ^{3α}` faster than `α`-Hölder
  allows; `NOTES.md` §4 records the counterexample) -/
  Lg : ℝ
  /-- `Lg ≥ 0` -/
  hLg : 0 ≤ Lg
  /-- the radial modulus -/
  hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
    |g z θ - g z' θ| ≤ Lg * |z - z'| ^ (α : ℝ)
  /-- the **uniform angular modulus** of the perturbation: `|g(z,θ)-g(z,θ')| ≤ Lθ·|θ-θ'|^α`
  (idem, `NOTES.md` §4) -/
  Lθ : ℝ
  /-- `Lθ ≥ 0` -/
  hLθ : 0 ≤ Lθ
  /-- the angular modulus -/
  hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
    |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ (α : ℝ)
  /-- **the paper's regime `α ≤ 1/3`** (equivalently profile exponent `p = 3α ≤ 1`), in which the
  construction is run -/
  hα13 : (α : ℝ) ≤ 1 / 3
  /-- **the `C^{1,α}` clause demanded by `Work.SolutionDelivery.ConstructedSolution`.**  This is
  *not* a property of the construction: `Refute.lean` proves that for every profile exponent
  `p < 1` the field `omegaS p 0` is not even differentiable at the origin, so for `α < 1/3`
  (the paper's regime, and in particular at `p = profExp α`) this field is *false*.  It is
  recorded here so that the interface can be instantiated at all; the repair is certified in
  `Repair.lean`. -/
  hcdh : IsContDiffHolder ℝ α (omegaS (profExp α) g)
  /-- the support radius of the vorticity -/
  R : ℝ
  /-- `R > 0` -/
  hR : 0 < R
  /-- the `L^∞` bound for the vorticity -/
  M : ℝ
  /-- `M ≥ 0` -/
  hM : 0 ≤ M
  /-- the profile is bounded by `M` (so that the same `M` bounds both `ωS` and `ω`); this is what
  `Basic.omegaS_norm_le` produces, from `hgbdd` and `Gamma ≤ 1` -/
  hMprof : 20 * profExp α + Cg ≤ M
  /-- the `L^∞` bound for `∂ₜω` -/
  M₁ : ℝ
  /-- `M₁ ≥ 0` -/
  hM₁ : 0 ≤ M₁
  /-- the maximal time -/
  T : ℝ
  /-- the LWP chapter's maximal solution with datum `u₀ = BS ω₀` -/
  hmax : Work.LWP.MaximalSolution α (Work.LWP.biotSavart (omega₀ (profExp α) g L)) T
  /-- `u.uncurry` is `C¹` on a neighbourhood of the two-sided window -/
  smooth : ContDiffOn ℝ 1 hmax.u.uncurry (Set.univ ×ˢ Work.SolutionDelivery.extWindow T)
  /-- the vorticity of the constructed solution -/
  ω : R3 → ℝ → R3
  /-- `u(x,t) = BS(ω(·,t)) x` on the open extended window -/
  bsSliceExt : ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ x : R3,
    hmax.u x t = Work.LWP.biotSavart (fun y => ω y t) x
  /-- the vorticity slices are supported in `B(0,R)` -/
  hSupp : ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ y : R3,
    ω y t ≠ 0 → y ∈ Metric.closedBall 0 R
  /-- `ω` is bounded by `M` -/
  hBdd : ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ y : R3, ‖ω y t‖ ≤ M
  /-- `∂ₜω` is bounded by `M₁` -/
  hBddDt : ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ y : R3, ‖timeDeriv ω y t‖ ≤ M₁
  /-- the vorticity slices are divergence free -/
  hDivω : ∀ t ∈ Work.SolutionDelivery.extWindow T,
    FiniteTimeSingularity.div (ω · t) = 0
  /-- the core `C^{1,α}` regularity of the vorticity -/
  hωcore : IsContDiffHolderOn ℝ α ω.uncurry
    (Work.StabilityFar.coreRegion (R + 1) ×ˢ Work.SolutionDelivery.extWindow T)
  /-- the modulation -/
  lam : ℝ → ℝ
  /-- `λ̄ > 0` on `[0,T)` -/
  hlam_pos : ∀ t ∈ Set.Ico 0 T, 0 < lam t
  /-- `λ̄(t) ≤ 2(T-t)` -/
  hlam_le : ∀ t ∈ Set.Ico 0 T, lam t ≤ 2 * (T - t)
  /-- the profile constant of `Work.StabilityFar.Profile.exists_Fstar_add_ge` -/
  c₀ : ℝ
  /-- `c₀ > 0` -/
  hc₀ : 0 < c₀
  /-- the `St5` interface -/
  hansatz : ∀ t ∈ Set.Ico 0 T, ∃ x : R3, c₀ * (α : ℝ) ≤ lam t * ‖ω x t‖



end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.isOdd_biotSavart_solVort =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-! ## The `Cyl` dictionary under the reflection `reflZ` -/

/-- The three dimensional radius is invariant under the reflection in the plane `x₃ = 0`. -/
private lemma rho_reflZL (x : R3) : Work.Cyl.rho (Work.LWP.reflZ x) = Work.Cyl.rho x := by
  have h1 : Work.Cyl.radSq (Work.LWP.reflZ x) = Work.Cyl.radSq x := by
    simp [Work.Cyl.radSq, Work.LWP.reflZ]
  have h2 : Work.Cyl.axial (Work.LWP.reflZ x) = -Work.Cyl.axial x := by
    simp [Work.Cyl.axial, Work.LWP.reflZ]
  rw [Work.Cyl.rho, Work.Cyl.rho, h1, h2, neg_sq]

/-- The polar angle changes sign under the reflection in the plane `x₃ = 0`. -/
private lemma theta_reflZL (x : R3) :
    Work.Cyl.theta (Work.LWP.reflZ x) = - Work.Cyl.theta x := by
  simp [Work.Cyl.theta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.axial, Work.LWP.reflZ,
    neg_div, Real.arctan_neg]

/-- The angular frame vector `e_θ` is invariant under the reflection in the plane `x₃ = 0`. -/
private lemma eTheta_reflZL (x : R3) :
    Work.Cyl.eTheta (Work.LWP.reflZ x) = Work.Cyl.eTheta x := by
  simp [Work.Cyl.eTheta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.angularVec, Work.LWP.reflZ]

/-- The flip of the third component is real-linear. -/
private lemma flipZ_smulL (c : ℝ) (v : R3) :
    Work.LWP.flipZ (c • v) = c • Work.LWP.flipZ v := by
  ext i
  fin_cases i <;> simp [Work.LWP.flipZ]

/-- The flip of the third component fixes `e_θ` (which lies in the plane `x₃ = 0`). -/
private lemma flipZ_eThetaL (x : R3) : Work.LWP.flipZ (Work.Cyl.eTheta x) = Work.Cyl.eTheta x := by
  ext i
  fin_cases i <;> simp [Work.LWP.flipZ, Work.Cyl.eTheta]

/-! ## The parity dictionary for `(ρ,θ)`-swirl fields -/

/-- **A field `x ↦ W(ρ(x),θ(x)) • e_θ(x)` whose scalar is odd in the angular variable is in the
parity class `IsOddVorticity`.**  (The cut-off and the modulation only enter through the scalar
`W`, so this covers `omegaS`, the cut datum and every slice `solVort P · t` at once.) -/
theorem isOddVorticity_smul_eTheta {W : ℝ → ℝ → ℝ} (hW : ∀ ρ θ, W ρ (-θ) = - W ρ θ) :
    Work.LWP.IsOddVorticity
      (fun x : R3 => W (Work.Cyl.rho x) (Work.Cyl.theta x) • Work.Cyl.eTheta x) := by
  intro x
  show W (Work.Cyl.rho (Work.LWP.reflZ x)) (Work.Cyl.theta (Work.LWP.reflZ x))
        • Work.Cyl.eTheta (Work.LWP.reflZ x)
      = - Work.LWP.flipZ (W (Work.Cyl.rho x) (Work.Cyl.theta x) • Work.Cyl.eTheta x)
  rw [rho_reflZL, theta_reflZL, eTheta_reflZL, hW, neg_smul, flipZ_smulL, flipZ_eThetaL]

/-! ## The slice of the constructed vorticity as a swirl field -/

/-- The scalar profile of the slice `t` of the constructed vorticity: the field is
`x ↦ scalarProfile P t (ρ x) (θ x) • e_θ(x)`. -/
private noncomputable def scalarProfile {α : NNReal} (P : ProfileData α) (t : ℝ)
    (ρ θ : ℝ) : ℝ :=
  (P.lam t)⁻¹ * Work.Stability.chi (ρ / P.L)
    * profile (profExp α) P.g (ρ ^ profExp α / P.lam t) θ

/-- `solVort P · t` is a `(ρ,θ)`-swirl field, pointwise. -/
private lemma solVort_apply_scalarProfile {α : NNReal} (P : ProfileData α) (t : ℝ) (y : R3) :
    solVort P y t
      = scalarProfile P t (Work.Cyl.rho y) (Work.Cyl.theta y) • Work.Cyl.eTheta y := by
  rw [solVort_apply, omegaSz_apply]
  simp only [scalarProfile, smul_smul]
  ring_nf

/-- The same, as an identity of functions. -/
private lemma solVort_eq_smul_eTheta {α : NNReal} (P : ProfileData α) (t : ℝ) :
    (fun y : R3 => solVort P y t)
      = fun y => scalarProfile P t (Work.Cyl.rho y) (Work.Cyl.theta y) • Work.Cyl.eTheta y :=
  funext (solVort_apply_scalarProfile P t)

/-- The scalar profile of the slice is odd in the angular variable: this is `profile_odd` for the
odd extension `profile (profExp α) P.g`, the perturbation vanishing at `θ = 0`. -/
private lemma scalarProfile_odd {α : NNReal} (P : ProfileData α) (t : ℝ) :
    ∀ ρ θ : ℝ, scalarProfile P t ρ (-θ) = - scalarProfile P t ρ θ := by
  have hp : profExp α ≠ 0 := ne_of_gt (profExp_pos P.hα)
  have hg0 : ∀ z : ℝ, P.g z 0 = 0 := P.hvt.1
  intro ρ θ
  rw [scalarProfile, scalarProfile, profile_odd hp hg0]
  ring

/-- **The parity of every slice of the constructed vorticity.** -/
theorem isOddVorticity_solVort {α : NNReal} (P : ProfileData α) (t : ℝ) :
    Work.LWP.IsOddVorticity (fun y => solVort P y t) := by
  have h := isOddVorticity_smul_eTheta (scalarProfile_odd P t)
  rwa [← solVort_eq_smul_eTheta P t] at h

/-! ## The slice as a function of `(radial, axial)` -/

/-- **The `(radial, axial)` form of the slice**: `ρ` and `θ` are functions of `(radial x, axial x)`,
so the slice is `f(radial x)(axial x) • e_θ(x)`, the shape consumed by
`isAxiNoSwirl_biotSavart`. -/
private lemma solVort_eq_radialAxial {α : NNReal} (P : ProfileData α) (t : ℝ) (y : R3) :
    solVort P y t
      = scalarProfile P t (Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y))
          (Work.Cyl.thetaP (Work.Cyl.radial y) (Work.Cyl.axial y)) • Work.Cyl.eTheta y := by
  rw [solVort_apply_scalarProfile]
  have hρ : Work.Cyl.rho y = Work.Cyl.rhoP (Work.Cyl.radial y) (Work.Cyl.axial y) := by
    rw [Work.Cyl.rho, Work.Cyl.rhoP, Work.Cyl.radial_sq]
  have hθ : Work.Cyl.theta y = Work.Cyl.thetaP (Work.Cyl.radial y) (Work.Cyl.axial y) := rfl
  rw [hρ, hθ]

/-- **The Biot–Savart field of every slice of the constructed vorticity is axisymmetric without
swirl**: the slice is a swirl field of the shape `f(radial, axial) • e_θ`, so
`isAxiNoSwirl_biotSavart` (equivariance of the Boole integral under the rotations about the
`x₃`-axis and under the reflection `x₁ ↦ -x₁`) applies. -/
theorem isAxiNoSwirl_biotSavart_solVort {α : NNReal} (P : ProfileData α) (t : ℝ) :
    Work.Cyl.IsAxiNoSwirl (Work.LWP.biotSavart (fun y => solVort P y t)) :=
  isAxiNoSwirl_biotSavart (f := fun r a =>
      scalarProfile P t (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a))
    (fun y => solVort_eq_radialAxial P t y)

/-! ## The target -/

theorem isOdd_biotSavart_solVort {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      FiniteTimeSingularity.IsOdd
        (Work.LWP.biotSavart (fun y => Work.ConstructionInstance.solVort P y t)) := by
  intro t _
  exact Work.SolutionDelivery.isOdd_biotSavart_of_axiNoSwirl (isOddVorticity_solVort P t)
    (isAxiNoSwirl_biotSavart_solVort P t)

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.lam_pos_le_on_Icc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **A uniform positive lower bound for `λ̄` on the initial strip `[0,S]`.**

The hypotheses are exactly the `λ̄`-fields of the construction: `λ̄` is positive on
`preWindow T = (-2,T)` and differentiable (hence continuous) there, and `0 ≤ S < T`.  Then
`Set.Icc 0 S` is a compact interval contained in the open half-window `preWindow T`, so the
continuous function `λ̄` attains its minimum there, and that minimum is positive because
`λ̄ > 0` on `preWindow T`. -/
theorem lam_pos_le_on_Icc {lam : ℝ → ℝ} {T S : ℝ} (hS : 0 ≤ S) (hST : S < T)
    (hlam : ∀ t ∈ preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ preWindow T, HasDerivAt lam (deriv lam t) t) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc 0 S, m ≤ lam t := by
  have hsub : Set.Icc (0 : ℝ) S ⊆ preWindow T := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2, hST]⟩
  have hcontpre : ContinuousOn lam (preWindow T) :=
    fun t ht => (hlamdif t ht).continuousAt.continuousWithinAt
  have hcont : ContinuousOn lam (Set.Icc (0 : ℝ) S) := hcontpre.mono hsub
  have hne : (Set.Icc (0 : ℝ) S).Nonempty := ⟨0, by simp [hS]⟩
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  exact ⟨lam a, hlam a (hsub ha), fun t ht => hmin ht⟩

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.solVort_holder =====
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

/-! ## The cylindrical coordinates under a positive dilation -/

/-- `ρ` is positively homogeneous: `ρ(c • x) = c·ρ(x)` for `c ≥ 0`. -/
lemma solVort_holder_radial_smul {c : ℝ} (hc : 0 ≤ c) (x : R3) :
    Work.Cyl.radial (c • x) = c * Work.Cyl.radial x := by
  rw [Work.Cyl.radial, Work.Cyl.radial,
    show Work.Cyl.radSq (c • x) = c ^ 2 * Work.Cyl.radSq x by simp [Work.Cyl.radSq]; ring,
    Real.sqrt_mul (by positivity) (Work.Cyl.radSq x), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

/-- `ρ(c • x) = c·ρ(x)` for `c ≥ 0` (`ρ(x) = ‖x‖`). -/
lemma solVort_holder_rho_smul {c : ℝ} (hc : 0 ≤ c) (x : R3) :
    Work.Cyl.rho (c • x) = c * Work.Cyl.rho x := by
  rw [Work.Cyl.rho_eq_norm, Work.Cyl.rho_eq_norm, norm_smul, Real.norm_of_nonneg hc]

/-- The angular vector field is homogeneous: `angularVec (c • x) = c • angularVec x`. -/
lemma solVort_holder_angularVec_smul (c : ℝ) (x : R3) :
    Work.Cyl.angularVec (c • x) = c • Work.Cyl.angularVec x := by
  ext i; fin_cases i <;> simp [Work.Cyl.angularVec]

/-- The azimuthal angle is invariant under a positive dilation: `θ(c • x) = θ(x)`. -/
lemma solVort_holder_theta_smul {c : ℝ} (hc : 0 < c) (x : R3) :
    Work.Cyl.theta (c • x) = Work.Cyl.theta x := by
  rw [Work.Cyl.theta, Work.Cyl.theta]
  congr 1
  rw [show Work.Cyl.axial (c • x) = c * Work.Cyl.axial x by simp [Work.Cyl.axial],
    solVort_holder_radial_smul hc.le]
  field_simp

/-- The azimuthal frame vector is invariant under a positive dilation: `e_θ(c • x) = e_θ(x)`. -/
lemma solVort_holder_eTheta_smul {c : ℝ} (hc : 0 < c) (x : R3) :
    Work.Cyl.eTheta (c • x) = Work.Cyl.eTheta x := by
  rw [Work.Cyl.eTheta, Work.Cyl.eTheta, solVort_holder_radial_smul hc.le,
    solVort_holder_angularVec_smul, smul_smul]
  congr 1
  field_simp

/-! ## The spatial Hölder regularity of the slices -/


end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.solVort_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology

namespace Work.ConstructionInstance

theorem solVort_integrable {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      MeasureTheory.Integrable (fun x => Work.ConstructionInstance.solVort P x t) := by
  intro t ht
  have hsmeas : MeasurableSet (Metric.closedBall (0 : R3) (P.R + 1)) :=
    isClosed_closedBall.measurableSet
  -- the slice of the vorticity is continuous on the ball
  have hcont : ContinuousOn (fun x : R3 => solVort P x t)
      (Metric.closedBall (0 : R3) (P.R + 1)) := by
    have hmaps : Set.MapsTo (fun x : R3 => (x, t)) (Metric.closedBall (0 : R3) (P.R + 1))
        (Work.StabilityFar.coreRegion (P.R + 1) ×ˢ preWindow P.T) := by
      intro x hx
      refine ⟨?_, ht⟩
      show ‖x‖ ≤ P.R + 1
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact hx
    have hc : Continuous (fun x : R3 => (x, t)) := continuous_id.prodMk continuous_const
    exact (solVort_cont P).comp hc.continuousOn hmaps
  have haes : AEStronglyMeasurable (fun x : R3 => solVort P x t)
      (volume.restrict (Metric.closedBall (0 : R3) (P.R + 1))) :=
    ContinuousOn.aestronglyMeasurable hcont hsmeas
  have hfin : volume (Metric.closedBall (0 : R3) (P.R + 1)) < ⊤ := measure_closedBall_lt_top
  have hbound : ∀ᵐ x ∂(volume.restrict (Metric.closedBall (0 : R3) (P.R + 1))),
      ‖solVort P x t‖ ≤ P.M / P.lam t := by
    refine Eventually.of_forall (fun x => ?_)
    rw [le_div_iff₀ (P.hlam t ht), mul_comm]
    exact solVort_bdd P t ht x
  have hIntOn : IntegrableOn (fun x : R3 => solVort P x t)
      (Metric.closedBall (0 : R3) (P.R + 1)) volume :=
    IntegrableOn.of_bound hfin haes (P.M / P.lam t) hbound
  have hsupp : Function.support (fun x : R3 => solVort P x t) ⊆
      Metric.closedBall (0 : R3) (P.R + 1) := by
    intro x hx
    rw [Function.mem_support] at hx
    exact closedBall_subset_closedBall (by linarith) (solVort_supp P t x hx)
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hIntOn

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.solVort_isBoundedFun =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- The `L^∞` box `λ̄(t)·‖ω(x,t)‖ ≤ M` of `solVort_bdd` gives the pointwise norm bound
`‖ω(x,t)‖ ≤ M/λ̄(t)` used below. -/
theorem solVort_norm_le {α : NNReal} (P : ProfileData α) {t : ℝ}
    (ht : t ∈ preWindow P.T) (x : R3) :
    ‖solVort P x t‖ ≤ P.M / P.lam t := by
  have hpos : 0 < P.lam t := P.hlam t ht
  rw [le_div_iff₀ hpos, mul_comm]
  exact solVort_bdd P t ht x

theorem solVort_isBoundedFun {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      IsBoundedFun (fun x => Work.ConstructionInstance.solVort P x t) := by
  intro t ht
  exact Work.Stability.isBoundedFun_of_forall_norm_le
    (f := fun x => solVort P x t) (C := P.M / P.lam t) (fun x => solVort_norm_le P ht x)

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.timeDeriv_selfSimVort_le_Icc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The `∂ₜ` box of the constructed vorticity, in the `Icc`-normalised form.**

`bddDt_selfSimVort` gives `λ̄(t)²·‖∂ₜω(y,t)‖ ≤ K·(20p + Cg + Cg')` on `preWindow T`.  On the
initial strip `[0,S]` one has `λ̄(t) ≥ m > 0` (`hmle`), hence `m² ≤ λ̄(t)²`, and dividing the box
by `λ̄(t)²` and comparing the resulting reciprocal factors gives the stated uniform bound
`‖∂ₜω(y,t)‖ ≤ K·(20p + Cg + Cg')/m²` for every `t ∈ [0,S]`. -/
theorem timeDeriv_selfSimVort_le_Icc {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    {Cg Cg' K : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg')
    (hgdiff : ∀ z θ : ℝ, 0 < z →
      HasDerivAt (fun z' => profile p g z' θ) (Work.Spaces.pz (profile p g) z θ) z)
    {L : ℝ} {lam : ℝ → ℝ} {T S m : ℝ} (hK : 0 ≤ K)
    (hlam : ∀ t ∈ preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ preWindow T, HasDerivAt lam (deriv lam t) t)
    (hlamd : ∀ t ∈ preWindow T, |deriv lam t| ≤ K)
    (hm : 0 < m) (hsub : Set.Icc (0 : ℝ) S ⊆ preWindow T)
    (hmle : ∀ t ∈ Set.Icc (0 : ℝ) S, m ≤ lam t)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S) (y : R3) :
    ‖FiniteTimeSingularity.timeDeriv (selfSimVort p g L lam) y t‖
      ≤ K * (20 * p + Cg + Cg') / m ^ 2 := by
  have htT : t ∈ preWindow T := hsub ht
  have hbox : (lam t) ^ 2 * ‖FiniteTimeSingularity.timeDeriv (selfSimVort p g L lam) y t‖
      ≤ K * (20 * p + Cg + Cg') :=
    bddDt_selfSimVort hp hp1 hgbdd hg2 hgdiff hK hlam hlamdif hlamd htT y
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgbdd 0 0 le_rfl hI0)
  have hCg' : 0 ≤ Cg' := by simpa using hg2 0 0 le_rfl hI0
  have hsum : 0 ≤ 20 * p + Cg + Cg' := by linarith
  have hmlt : m ≤ lam t := hmle t ht
  have hlt : 0 < lam t := lt_of_lt_of_le hm hmlt
  have hlt2 : 0 < (lam t) ^ 2 := by positivity
  have hm2 : 0 < m ^ 2 := by positivity
  have hsq : m ^ 2 ≤ (lam t) ^ 2 := by nlinarith [hm.le, hmlt]
  have hKh : 0 ≤ K * (20 * p + Cg + Cg') := mul_nonneg hK hsum
  calc ‖FiniteTimeSingularity.timeDeriv (selfSimVort p g L lam) y t‖
      = (lam t) ^ 2 * ‖FiniteTimeSingularity.timeDeriv (selfSimVort p g L lam) y t‖
          / (lam t) ^ 2 :=
        (mul_div_cancel_left₀ _ (ne_of_gt hlt2)).symm
    _ ≤ K * (20 * p + Cg + Cg') / (lam t) ^ 2 :=
        div_le_div_of_nonneg_right hbox hlt2.le
    _ ≤ K * (20 * p + Cg + Cg') / m ^ 2 :=
        div_le_div_of_nonneg_left hKh hm2 hsq

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.timeHolderOnBall_of_timeDeriv_le_Icc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open Set Metric
open scoped Topology

theorem timeHolderOnBall_of_timeDeriv_le_Icc {α Λ R S : ℝ} (hS : 0 ≤ S) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hΛ : 0 ≤ Λ)
    {ω : R3 → ℝ → R3}
    (hdiff : ∀ z ∈ Metric.closedBall (0 : R3) R, ∀ s ∈ Set.Icc 0 S,
      HasDerivAt (fun t => ω z t) (FiniteTimeSingularity.timeDeriv ω z s) s)
    (hbd : ∀ z ∈ Metric.closedBall (0 : R3) R, ∀ s ∈ Set.Icc 0 S,
      ‖FiniteTimeSingularity.timeDeriv ω z s‖ ≤ Λ) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ z ∈ Metric.closedBall (0 : R3) R, ∀ t ∈ Set.Icc 0 S, ∀ τ ∈ Set.Icc 0 S,
        ‖ω z t - ω z τ‖ ≤ H * |t - τ| ^ α := by
  refine ⟨Λ * max S 1, mul_nonneg hΛ (le_trans zero_le_one (le_max_right _ _)), ?_⟩
  intro z hz t ht τ hτ
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) S) := convex_Icc _ _
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) S, DifferentiableAt ℝ (fun t => ω z t) x :=
    fun x hx => (hdiff z hz x hx).differentiableAt
  have hbnd : ∀ x ∈ Set.Icc (0 : ℝ) S, ‖deriv (fun t => ω z t) x‖ ≤ Λ := by
    intro x hx
    simpa only [FiniteTimeSingularity.timeDeriv] using hbd z hz x hx
  have hmvt : ‖ω z t - ω z τ‖ ≤ Λ * |t - τ| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hderiv hbnd hconv hτ ht
    simpa only [Real.norm_eq_abs] using h
  have hdt : |t - τ| ≤ S := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [ht.2, hτ.1], by linarith [hτ.2, ht.1]⟩
  have hkey := Work.SolutionDelivery.Holder.self_le_max_mul_rpow (d := |t - τ|) (D := S) (α := α)
    (abs_nonneg _) hdt hα0.le hα1
  calc ‖ω z t - ω z τ‖ ≤ Λ * |t - τ| := hmvt
    _ ≤ Λ * (max S 1 * |t - τ| ^ α) := mul_le_mul_of_nonneg_left hkey hΛ
    _ = (Λ * max S 1) * |t - τ| ^ α := by ring

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.FTS.Apriori.Arith =====
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

set_option autoImplicit false

/-! ## Positivity and comparison of the constants -/

theorem kappa_pos {cc clo Cup : ℝ} (hcc : 0 < cc) (hclo : 0 < clo) (hCup : 0 < Cup) :
    0 < kappa cc clo Cup := div_pos (mul_pos hcc hclo) hCup

theorem C0_pos {CcN cc clo Cup Ccs : ℝ} (hCcN : 0 < CcN) (hcc : 0 < cc) (hclo : 0 < clo)
    (hCup : 0 < Cup) (hCcs : 0 < Ccs) : 0 < C0 CcN cc clo Cup Ccs :=
  lt_max_iff.mpr (Or.inl (div_pos (by linarith) (kappa_pos hcc hclo hCup)))

/-- The positivity of `C₀` needs only `Ccs > 0` and `clo > 0` (the second branch of the max). -/
theorem C0_pos' {CcN cc clo Cup Ccs : ℝ} (hclo : 0 < clo) (hCcs : 0 < Ccs) :
    0 < C0 CcN cc clo Cup Ccs :=
  lt_of_lt_of_le (by positivity : 0 < 2 * Real.sqrt (Ccs / clo)) (le_max_right _ _)

/-- The comparison `2C_N ≤ κC₀` that the closing inequality uses: it is exactly
`C₀ ≥ 2C_N/κ` multiplied by `κ > 0`. -/
theorem C0_ge {CcN cc clo Cup Ccs : ℝ} (hcc : 0 < cc) (hclo : 0 < clo) (hCup : 0 < Cup) :
    2 * CcN ≤ kappa cc clo Cup * C0 CcN cc clo Cup Ccs := by
  have hκ := kappa_pos hcc hclo hCup
  have hle : 2 * CcN / kappa cc clo Cup ≤ C0 CcN cc clo Cup Ccs := le_max_left _ _
  rw [div_le_iff₀ hκ] at hle
  linarith [hle, mul_comm (C0 CcN cc clo Cup Ccs) (kappa cc clo Cup)]

/-- The comparison `Ccs < clo·C₀²` used for the initial datum: it is exactly
`C₀ ≥ 2√(Ccs/clo)` squared. -/
theorem Ccs_lt_lower {CcN cc clo Cup Ccs : ℝ} (hcc : 0 < cc) (hclo : 0 < clo) (hCup : 0 < Cup)
    (hCcs : 0 < Ccs) : Ccs < clo * C0 CcN cc clo Cup Ccs ^ 2 := by
  have hle : 2 * Real.sqrt (Ccs / clo) ≤ C0 CcN cc clo Cup Ccs := le_max_right _ _
  have hnn : 0 ≤ 2 * Real.sqrt (Ccs / clo) := by positivity
  have hsq : (2 * Real.sqrt (Ccs / clo)) ^ 2 ≤ (C0 CcN cc clo Cup Ccs) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hnn hle
  have hval : (2 * Real.sqrt (Ccs / clo)) ^ 2 = 4 * Ccs / clo := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hCcs.le hclo.le)]
    norm_num
    ring
  rw [hval, div_le_iff₀ hclo] at hsq
  linarith

theorem alphaCl_pos {C₀ : ℝ} (hC₀ : 0 < C₀) : 0 < alphaCl C₀ := by
  refine lt_min_iff.mpr ⟨by norm_num, ?_⟩
  have h : 0 < (C₀ + C₀ ^ 2 + C₀ ^ 3) ^ 2 := by positivity
  positivity

theorem alphaCl_le_one (C₀ : ℝ) : alphaCl C₀ ≤ 1 := min_le_left _ _







/-- **The threshold of the closing inequality**: for `α ≤ alphaCl C₀`,
`(C₀+C₀²)√α + C₀³α^{3/2} < 1`. -/
theorem alphaCl_key {C₀ α : ℝ} (hC₀ : 0 < C₀) (hα : 0 < α) (hαCl : α ≤ alphaCl C₀) :
    (C₀ + C₀ ^ 2) * Real.sqrt α + C₀ ^ 3 * α ^ (3 / 2 : ℝ) < 1 := by
  set D : ℝ := C₀ + C₀ ^ 2 + C₀ ^ 3 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hα1 : α ≤ 1 := le_trans hαCl (alphaCl_le_one C₀)
  have hαinv : α ≤ 1 / (16 * D ^ 2) := le_trans hαCl (min_le_right _ _)
  have hsqrt : Real.sqrt α ≤ 1 / (4 * D) := by
    have h := Real.sqrt_le_sqrt hαinv
    have hval : Real.sqrt (1 / (16 * D ^ 2)) = 1 / (4 * D) := by
      rw [show (1 : ℝ) / (16 * D ^ 2) = (1 / (4 * D)) ^ 2 by field_simp; ring]
      rw [Real.sqrt_sq (by positivity)]
    rwa [hval] at h
  have hsqrtnn : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  have h32 : α ^ (3 / 2 : ℝ) ≤ Real.sqrt α := by
    have h : α ^ (3 / 2 : ℝ) = α * Real.sqrt α := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hα, Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [h]
    nlinarith [hsqrtnn, hα1]
  have h1 : (C₀ + C₀ ^ 2) * Real.sqrt α ≤ 1 / 4 := by
    have h2 : (C₀ + C₀ ^ 2) * Real.sqrt α ≤ (C₀ + C₀ ^ 2) * (1 / (4 * D)) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    have h3 : (C₀ + C₀ ^ 2) * (1 / (4 * D)) = (C₀ + C₀ ^ 2) / (4 * D) := by ring
    rw [h3] at h2
    have h4 : (C₀ + C₀ ^ 2) / (4 * D) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * D)]
      nlinarith [hD]
    linarith
  have h2 : C₀ ^ 3 * α ^ (3 / 2 : ℝ) ≤ 1 / 4 := by
    have h2a : C₀ ^ 3 * α ^ (3 / 2 : ℝ) ≤ C₀ ^ 3 * Real.sqrt α :=
      mul_le_mul_of_nonneg_left h32 (by positivity)
    have h2b : C₀ ^ 3 * Real.sqrt α ≤ C₀ ^ 3 * (1 / (4 * D)) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    have h2c : C₀ ^ 3 * (1 / (4 * D)) = C₀ ^ 3 / (4 * D) := by ring
    rw [h2c] at h2b
    have h2d : C₀ ^ 3 / (4 * D) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * D)]
      nlinarith [hD]
    linarith
  linarith

/-! ## The polynomial `Pbd` -/

theorem Pbd_mono {α X Y : ℝ} (hα : 0 < α) (hX : 0 ≤ X) (hXY : X ≤ Y) :
    Pbd α X ≤ Pbd α Y := by
  have hY : 0 ≤ Y := le_trans hX hXY
  have h1 : α ^ 2 * X ≤ α ^ 2 * Y := mul_le_mul_of_nonneg_left hXY (sq_nonneg α)
  have hX2 : X ^ 2 ≤ Y ^ 2 := by nlinarith
  have h2 : Real.sqrt α * X ^ 2 ≤ Real.sqrt α * Y ^ 2 :=
    mul_le_mul_of_nonneg_left hX2 (Real.sqrt_nonneg α)
  have hX3 : X ^ 3 ≤ Y ^ 3 := by
    have h := mul_le_mul hX2 hXY hX (by positivity : (0:ℝ) ≤ Y ^ 2)
    nlinarith [h]
  have h3 : α ^ (-(3 / 2 : ℝ)) * X ^ 3 ≤ α ^ (-(3 / 2 : ℝ)) * Y ^ 3 :=
    mul_le_mul_of_nonneg_left hX3 (Real.rpow_nonneg hα.le _)
  have hX4 : X ^ 4 ≤ Y ^ 4 := by
    have h := mul_le_mul hX2 hX2 (by positivity) (by positivity)
    nlinarith [h]
  have h4 : α ^ (-(5 / 2 : ℝ)) * X ^ 4 ≤ α ^ (-(5 / 2 : ℝ)) * Y ^ 4 :=
    mul_le_mul_of_nonneg_left hX4 (Real.rpow_nonneg hα.le _)
  simp only [Pbd]
  linarith

/-- Helper: `α^{3/2} = (√α)³`. -/
theorem rpow_three_halves {α : ℝ} (hα : 0 < α) :
    α ^ (3 / 2 : ℝ) = (Real.sqrt α) ^ 3 := by
  have h : α ^ (3 / 2 : ℝ) = α * Real.sqrt α := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hα, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [h, show (Real.sqrt α) ^ 3 = (Real.sqrt α) ^ 2 * Real.sqrt α by ring,
    Real.sq_sqrt hα.le]

/-- Helper: `α^{5/2} = (√α)⁵`. -/
theorem rpow_five_halves {α : ℝ} (hα : 0 < α) :
    α ^ (5 / 2 : ℝ) = (Real.sqrt α) ^ 5 := by
  have h : α ^ (5 / 2 : ℝ) = α ^ 2 * Real.sqrt α := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hα, Real.rpow_two,
      Real.sqrt_eq_rpow]
  rw [h, show (Real.sqrt α) ^ 5 = ((Real.sqrt α) ^ 2) ^ 2 * Real.sqrt α by ring,
    Real.sq_sqrt hα.le]

/-- The exact value of `Pbd` at `C₀α²`. -/
theorem Pbd_at {α C₀ : ℝ} (hα : 0 < α) :
    Pbd α (C₀ * α ^ 2)
      = α ^ 4 * (C₀ + (C₀ ^ 2 + C₀ ^ 3) * Real.sqrt α + C₀ ^ 4 * α ^ (3 / 2 : ℝ)) := by
  set s : ℝ := Real.sqrt α with hsdef
  have hs2 : s ^ 2 = α := by rw [hsdef]; exact Real.sq_sqrt hα.le
  have hspos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hα
  have hα2 : α ^ 2 = s ^ 4 := by rw [← hs2]; ring
  have hα4 : α ^ 4 = s ^ 8 := by rw [← hs2]; ring
  have h32 : α ^ (3 / 2 : ℝ) = s ^ 3 := rpow_three_halves hα
  have h52 : α ^ (5 / 2 : ℝ) = s ^ 5 := rpow_five_halves hα
  have hn3 : α ^ (-(3 / 2 : ℝ)) = (s ^ 3)⁻¹ := by rw [Real.rpow_neg hα.le, h32]
  have hn5 : α ^ (-(5 / 2 : ℝ)) = (s ^ 5)⁻¹ := by rw [Real.rpow_neg hα.le, h52]
  have hm : Pbd α (C₀ * α ^ 2) = s ^ 8 * (C₀ + (C₀ ^ 2 + C₀ ^ 3) * s + C₀ ^ 4 * s ^ 3) := by
    rw [Pbd, ← hsdef]
    rw [hn3, hn5, hα2]
    field_simp
    ring
  rw [hm, hα4, h32]



end Work.FTS.Apriori
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Profile.Support =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Profile

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.Spaces

/-- `sin (2θ) ≥ 0` on the angular interval. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])







end Work.FTS.Apriori.Profile
end
end
-- ===== merged: Submission.Work.FTS.Apriori.ZeroMode =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.Apriori

open Work.FTS.Nonlin
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif ConvPoint Slab muDyn lamDyn dynLin dynRHS prof)

set_option autoImplicit false

/-- **`N_*` at the paper's modulation**: with `λ = lamfun μ`, the linear term collapses to
`μ(D_zg − g)` (the `μ + λ + μλ = −μ` identity of the paper, tex 1356). -/
theorem Nstar_lamfun {μ : ℝ} (hμ : μ ≠ -1) (g : Fn) :
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g
      = fun z θ => μ * (Work.Spaces.Dz g z θ - g z θ) := by
  have h1μ : (1 : ℝ) + μ ≠ 0 := by intro h; exact hμ (by linarith)
  have hkey : μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ = -μ := by
    simp only [Work.Construction.lamfun]
    field_simp
    ring
  funext z θ
  simp only [Work.Construction.Nstar, hkey]
  ring


end Work.FTS.Apriori
end
end
-- ===== merged: Submission.Work.FTS.Apriori.ZeroMode.L12_Dz_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.Apriori.ZeroMode


end Work.FTS.Apriori.ZeroMode
end
-- ===== merged: Submission.Work.FTS.Apriori.ZeroMode.L12_LGamma_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.ZeroMode

theorem L12_LGamma_zero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hdiff : ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s => f s θ) (Work.Spaces.pz f z θ) z)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ, ContinuousOn (fun s => Work.Spaces.pz f s θ) (Set.Ici 0))
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun s => f s θ) Filter.atTop (nhds 0))
    (hvan : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    (hintL : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.Gam α p.2
        * (Work.Coercivity.L12f f p.1 / (1 + p.1) ^ 2)) (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    (hintL2 : MeasureTheory.IntegrableOn
      (fun z => Work.Construction.L12dens f z) (Set.Ioi 0))
    (hint3 : MeasureTheory.IntegrableOn
      (fun z => Work.Construction.L12dens (Work.Coercivity.LGamma α f) z) (Set.Ioi 0)) :
    Work.Construction.L12 (Work.Coercivity.LGamma α f) 0
      = - Work.Construction.L12 f 0 := by
  have H : L12Hyp α f := ⟨hα, hα1, hdiff, hcont, hdec, hvan, hint, hintL, hintL2, hint3⟩
  have hSR := ZM_slice_relation H
  have hslice : ∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ) Work.Spaces.Iθ :=
    hSR.2.1
  -- `r * L₁₂dens f r = -NOf f r`
  have hrel : ∀ r : ℝ, 0 < r → r * uOf f r = - NOf f r := by
    intro r hr
    have h3 := hSR.2.2 r hr
    have hdiv : uOf f r = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f r θ) / r := by
      show Work.FM.L12dens Work.Spaces.K f r = _
      exact Work.FM.L12dens_eq (K := Work.Spaces.K) (f := f) (ne_of_gt hr)
    rw [hdiv, h3]
    field_simp
  have hNL := ZM_Nfun_limits H
  have hNcont : ContinuousOn (NOf f) (Set.Ici 0) := hNL.1
  have hNtop : Filter.Tendsto (NOf f) Filter.atTop (𝓝 0) := hNL.2.1
  have hR0 : Filter.Tendsto (ROf f) (𝓝[>] (0:ℝ)) (𝓝 (ROf f 0)) := hNL.2.2.1
  have hRtop : Filter.Tendsto (fun r : ℝ => ROf f r / (1 + r)) Filter.atTop (𝓝 0) := hNL.2.2.2
  have hN0 : NOf f 0 = 0 :=
    ZM_Nfun_zero H hrel (hNcont.continuousWithinAt (by simp))
  -- continuity of `uOf f` on `(0,∞)`, from `uOf f r = -NOf f r / r`
  have hu : ContinuousOn (uOf f) (Set.Ioi 0) := by
    have hnil : ∀ r ∈ Set.Ioi (0:ℝ), uOf f r = - NOf f r / r := by
      intro r hr
      rw [eq_div_iff (ne_of_gt hr)]
      have h := hrel r hr
      linarith
    refine ContinuousOn.congr ?_ hnil
    exact (hNcont.mono (Set.Ioi_subset_Ici_self)).neg.div continuousOn_id
      (fun r hr => ne_of_gt hr)
  have hMF := ZM_mderiv_fubini H
  have hibp := ZM_IBP_R H hu
  have hae := ZM_density_ae H hslice
  have hGint : MeasureTheory.IntegrableOn (GOf α f) (Set.Ioi 0) := H.hint3
  have huint : MeasureTheory.IntegrableOn (uOf f) (Set.Ioi 0) := H.hintL2
  exact zm_main H hslice hrel hNcont hNtop hR0 hRtop hN0 hMF.1 hMF.2.1 hibp hae hGint huint

end Work.FTS.Apriori.ZeroMode
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The angular weight and the weighted energies -/

/-- The angular weight `sin(2θ)^{-β}` of the pairings of `H1IP`. -/
def sig (β θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-β)

/-- The pair weight `ρ_β(z,θ) = w(z)²·sin(2θ)^{-β}`.  With `β = η` and `β = gam α` this is
exactly the weight of the first two resp. the fourth pairing of `Work.Coercivity.H1IP`. -/
def Rho (β : ℝ) : Fn := fun z θ => Work.Spaces.w z ^ 2 * sig β θ


/-- `Rho (gam α)` is the angular weight `Work.Coercivity.thetaW α` of the `γ`-estimates of
§6. -/
theorem Rho_gam (α : ℝ) : Rho (Work.Spaces.gam α) = Work.Coercivity.thetaW α := rfl

/-- The two ways of writing the half-weight agree: `(w/sin(2θ)^{β/2})² = w²·sin(2θ)^{-β}`. -/
theorem wdiv_sq (β z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (β / 2)) ^ 2
      = Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : ((Real.sin (2 * θ)) ^ (β / 2)) ^ 2 = (Real.sin (2 * θ)) ^ β := by
    rw [sq, ← Real.rpow_add hs]
    congr 1
    ring
  rw [div_pow, h1, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hs)]

/-- The two ways of writing the full angular weight agree:
`(u · Wt α)² = u²·w²·sin(2θ)^{-gam α}` on the open angular interval. -/
theorem Wt_sq (α : ℝ) (u : Fn) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (u z θ * Work.Spaces.Wt α z θ) ^ 2
      = u z θ ^ 2 * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [sq, ← Real.rpow_add hs]
    congr 1
    ring
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [mul_pow, mul_pow, h1]
  ring

/-- The `β`-weighted energy `E_β(u) = ∫∫ u² w² sin(2θ)^{-β}`. -/
def En (β : ℝ) (u : Fn) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    u z θ ^ 2 * Work.Spaces.w z ^ 2 * sig β θ

/-- The unweighted (in `θ`) energy `∫∫ u² w²`. -/
def EnOne (u : Fn) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, u z θ ^ 2 * Work.Spaces.w z ^ 2

/-- Almost every angle of `Iθ` lies in the *open* interval `(0,π/2)` (the two endpoints form
a null set).  This is the a.e. statement that lets the `SmoothQuad` identities — which hold on
the open quadrant only — be used under the integral. -/
theorem ae_restrict_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  have hset : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ :=
    MeasureTheory.Ioo_ae_eq_Icc
  rw [← MeasureTheory.Measure.restrict_congr_set hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- `sin(2θ) ≥ 0` on the closed angular interval. -/
theorem sin_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- If `θ ∈ Iθ` and `sin(2θ) > 0` then `θ` is in the *open* angular interval. -/
theorem mem_Ioo_of_mem_Iθ_of_sin_pos {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (h : 0 < Real.sin (2 * θ)) : θ ∈ Set.Ioo 0 (π / 2) := by
  refine ⟨lt_of_le_of_ne hθ.1 ?_, lt_of_le_of_ne hθ.2 ?_⟩
  · intro h0
    rw [← h0, mul_zero, Real.sin_zero] at h
    exact absurd h (lt_irrefl 0)
  · intro h0
    rw [h0, show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi] at h
    exact absurd h (lt_irrefl 0)

/-- The half-weight identity on the *closed* angular interval (at the endpoints both sides
vanish). -/
theorem sig_div_sq_Iθ (β : ℝ) (hβ : β ≠ 0) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (β / 2)) ^ 2 = Work.Spaces.w z ^ 2 * sig β θ := by
  have hβ2 : β / 2 ≠ 0 := by intro hc; exact hβ (by linarith)
  rcases eq_or_lt_of_le (sin_nonneg_of_mem_Iθ hθ) with h | h
  · rw [sig]
    rw [← h, Real.zero_rpow hβ2, div_zero, sq, mul_zero,
      Real.zero_rpow (by intro hc; exact hβ (by linarith)), mul_zero]
  · rw [wdiv_sq β z θ (mem_Ioo_of_mem_Iθ_of_sin_pos hθ h)]
    rfl

/-- The full angular-weight identity on the *closed* angular interval. -/
theorem Wt_sq_self_Iθ (α : ℝ) (z θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2 = Work.Spaces.w z ^ 2 * sig (Work.Spaces.gam α) θ := by
  have hγ : Work.Spaces.gam α ≠ 0 := by rw [Work.Spaces.gam]; intro hc; linarith
  have hγ2 : -(Work.Spaces.gam α / 2) ≠ 0 := by intro hc; exact hγ (by linarith)
  have hγ' : -(Work.Spaces.gam α) ≠ 0 := by intro hc; exact hγ (by linarith)
  have hfun : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [hfun]
  rcases eq_or_lt_of_le (sin_nonneg_of_mem_Iθ hθ) with h | h
  · rw [sig, ← h, Real.zero_rpow hγ2, Real.zero_rpow hγ']
    ring
  · rw [mul_pow, sig]
    rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from by
      rw [sq, ← Real.rpow_add h]
      congr 1
      ring]

theorem En_nonneg (β : ℝ) (u : Fn) : 0 ≤ En β u := by
  rw [En]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with z _
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Real.rpow_nonneg (sin_nonneg_of_mem_Iθ hθ) _)

theorem EnOne_nonneg (u : Fn) : 0 ≤ EnOne u := by
  rw [EnOne]
  exact integral_nonneg fun _ => integral_nonneg fun _ =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ## The integration-by-parts hypotheses in the interior class

`Work.Coercivity.IBP` is the package that makes the `z`-integration by parts of §6 valid; its
smoothness field is `Spaces.SmoothNbhd` (**analyticity** on a neighbourhood of the closed
quadrant), which the cut-off data of the route cannot satisfy (design §5 T1).  The package
below is the *interior* replacement: genuine `C^∞` on the open quadrant (`SmoothQuad`),
together with the same boundary limits and the a.e. (in `θ`) honesty of the two one-dimensional
integrals of the fundamental theorem of calculus.  Every instance needed here comes from
`RegQ α 2 f` by `Work.Spaces.HkMem` (see `IntFacts.lean`). -/

/-- The analytic hypotheses of the `z`-integration by parts in the interior class: `u` is
`C^∞` on the open quadrant, the boundary term `z(u w)²` vanishes at `z = 0⁺` and `z = ∞` for
every angle in the *open* interval (`Ioo 0 (π/2)`; this is exactly the first conjunct of
`BdryTraces` in the pairs `(0,0)`, `(1,0)`, `(0,1)` — the endpoints `θ = 0, π/2` are not
constrained by `RegQ`), and for
almost every angle the two one-dimensional integrals of the fundamental theorem of calculus
are honest. -/
structure ZIBP (u : Fn) : Prop where
  smooth : Work.FTS.LocData.SmoothQuad u
  bd0 : ∀ θ ∈ Set.Ioo 0 (π / 2),
    Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0)
  bdTop : ∀ θ ∈ Set.Ioo 0 (π / 2),
    Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) Filter.atTop (𝓝 0)
  intSq : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    IntegrableOn (fun z => (u z θ * Work.Spaces.w z) ^ 2) (Set.Ioi 0)
  intDeriv : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    IntegrableOn (fun z => deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z) (Set.Ioi 0)

/-! ## The integrability bundle

In this development the weighted pairings of `H1IP` are *honest* real numbers: every integrand
that occurs below is `IntegrableOn` the quadrant, and the certificates are collected once and
for all in the structure `IntPkg` (proved for `RegQ α 2 f` in `IntPkg/IntPkg_Q`).  This keeps
the four coercivity estimates of `Estimates.lean` purely algebraic.

The fields fall into five groups:

* `sqDzEta`, `sqMixedEta`, `sqMixedGam`, `sqDzOne`, `sqMixedOne` — the squared blocks with the
  `η`, `γ` and plain radial weights (all dominated by the summands of `HkIntegrand α 2 f`);
* `intL_*` — the `𝓛`-pairings `𝓛u·u·ρ` occurring in the estimates;
* `intLhat_Dz_eta`, `intE2hat_Dz_eta` — the two pieces of the `D_z`-commutator split for `Lhat`;
* `hint_*` — the transport pairings `D_θu·u·ρ/(1+z)`;
* `zibp_*` — the `z`-integration-by-parts hypotheses for the three functions used. -/

structure IntPkg (α : ℝ) (f : Fn) : Prop where
  /-- the squared `D_z`-blocks with the `η`-weight -/
  sqDzEta : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared mixed blocks with the `η`-weight -/
  sqMixedEta : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared mixed blocks with the `γ`-weight -/
  sqMixedGam : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      (Work.Spaces.mixed j i f z θ) ^ 2 * Rho (Work.Spaces.gam α) z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared `D_z`-blocks with the plain radial weight -/
  sqDzOne : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared mixed blocks with the plain radial weight -/
  sqMixedOne : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `f` with the `η`-weight -/
  intL_f_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L f z θ * f z θ * Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_z f` with the `η`-weight -/
  intL_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dz f) z θ
      * Work.Spaces.Dz f z θ * Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_θ f` with the `γ`-weight -/
  intL_Dth_gam : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dth f) z θ
      * Work.Spaces.Dth f z θ * Rho (Work.Spaces.gam α) z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `f` with the plain radial weight -/
  intL_f_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `Lhat`-pairing of `D_z f` with the `η`-weight -/
  intLhat_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
      * Work.Spaces.Dz f z θ * Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `D_z`-commutator defect against `D_z f` with the `η`-weight -/
  intE2hat_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.E2hat f z θ
      * Work.Spaces.Dz f z θ * Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `f` with the `η`-weight -/
  hint_f_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * f z θ
      * Rho Work.Spaces.eta z θ / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `D_z f` with the `η`-weight -/
  hint_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
      * Rho Work.Spaces.eta z θ / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `D_θ f` with the `γ`-weight -/
  hint_Dth_gam : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dth f) z θ
      * Work.Spaces.Dth f z θ * Rho (Work.Spaces.gam α) z θ / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `f` with the plain radial weight -/
  hint_f_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * f z θ
      * Work.Spaces.w z ^ 2 / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `z`-integration-by-parts hypotheses for `f` -/
  zibp_f : ZIBP f
  /-- the `z`-integration-by-parts hypotheses for `D_z f` -/
  zibp_Dz : ZIBP (Work.Spaces.Dz f)
  /-- the `z`-integration-by-parts hypotheses for `D_θ f` -/
  zibp_Dth : ZIBP (Work.Spaces.Dth f)

/-! ## The pointwise core of the `z`-integration by parts

The paper's identity `(LW)`, `𝓛(g)·w = g·w + z∂_z(g·w)`, in the interior class `SmoothQuad`.
Both lemmas below are the `SmoothQuad` counterparts of `Work.Coercivity.l_self_w_sq_eq` and
`Work.Coercivity.deriv_zw_sq_eq`; the only change is that the differentiability of the `z`-slice
comes from `SmoothQuad.curry_z` instead of from `Spaces.SmoothNbhd`.  They are stated on the
*open* angular interval (`θ ∈ Ioo 0 (π/2)`), which is what `SmoothQuad` provides, and are used
under the integral only for a.e. `θ`. -/



/-! ## The `wip`'s of `H1IP` in terms of the `En`-functionals -/

/-- The `β`-weighted `wip` of a function with itself is its `β`-energy. -/
theorem wip_Rho_self (β : ℝ) (u : Fn) :
    Work.Coercivity.wip (Rho β) u u = En β u := by
  rw [Work.Coercivity.wip, En]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  simp only [Rho, sig]
  ring

/-- The plain `wip` of a function with itself is `EnOne`. -/
theorem wip_one_self (u : Fn) :
    Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) u u = EnOne u := by
  rw [Work.Coercivity.wip, EnOne]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  ring

/-! ## Identification with the energies of the coercivity chapter -/

/-- On `Iθ` the two expressions for the half-weight coincide: `(sin(2θ)^{-β/2})² = sin(2θ)^{-β}`. -/
theorem sin_half_sq (β θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    ((Real.sin (2 * θ)) ^ (-(β / 2))) ^ 2 = (Real.sin (2 * θ)) ^ (-β) := by
  rcases eq_or_lt_of_le (sin_nonneg_of_mem_Iθ hθ) with h | h
  · rw [← h]
    rcases eq_or_ne β 0 with rfl | hβ
    · norm_num
    · have h1 : -(β / 2) ≠ 0 := by intro hc; exact hβ (by linarith)
      have h2 : -β ≠ 0 := by intro hc; exact hβ (by linarith)
      rw [Real.zero_rpow h1, Real.zero_rpow h2]
      norm_num
  · rw [sq, ← Real.rpow_add h]
    congr 1
    ring

/-- `EfEta u = ∫∫ u² w² sin(2θ)^{-η}`. -/
theorem EfEta_eq_En (u : Fn) : Work.Coercivity.EfEta u = En Work.Spaces.eta u := by
  unfold Work.Coercivity.EfEta Work.Spaces.L2Sq En Work.Coercivity.wtEta
    Work.Coercivity.wtGam sig
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rw [mul_pow, mul_pow, sin_half_sq Work.Spaces.eta θ hθ]
  ring

/-- `EDz u = ∫∫ (D_zu)² w² sin(2θ)^{-η}`. -/
theorem EDz_eq_En (u : Fn) : Work.Coercivity.EDz u = En Work.Spaces.eta (Work.Spaces.Dz u) := by
  unfold Work.Coercivity.EDz Work.Spaces.L2Sq En Work.Coercivity.wtEta
    Work.Coercivity.wtGam sig
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rw [mul_pow, mul_pow, sin_half_sq Work.Spaces.eta θ hθ]
  ring

/-- `EDth α u = ∫∫ (D_θu)² w² sin(2θ)^{-γ}`. -/
theorem EDth_eq_En (α : ℝ) (u : Fn) :
    Work.Coercivity.EDth α u = En (Work.Spaces.gam α) (Work.Spaces.Dth u) := by
  unfold Work.Coercivity.EDth Work.Spaces.L2Sq En Work.Coercivity.wtGam sig
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rw [mul_pow, mul_pow, sin_half_sq (Work.Spaces.gam α) θ hθ]
  ring

/-- `Ef u = ∫∫ u² w²`. -/
theorem Ef_eq_EnOne (u : Fn) : Work.Coercivity.Ef u = EnOne u := by
  unfold Work.Coercivity.Ef Work.Spaces.L2Sq EnOne
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  ring

/-! ## The monotonicity of the angular weight

For `s ∈ (0,1]` and `p ≤ q` we have `s^{-p} ≤ s^{-q}` (`Real.rpow_le_rpow_of_exponent_ge`);
hence on the *open* angular interval, where `0 < sin(2θ) ≤ 1`,

  `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}`  and  `1 = sin(2θ)^{-0} ≤ sin(2θ)^{-η}`.

(The endpoints `θ = 0, π/2`, where `sin(2θ) = 0` and Lean's `rpow` takes the junk value, are
null sets; the comparisons are therefore only used under the integral in their a.e. form.) -/

theorem eta_le_gam (α : ℝ) (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam]
  have := Work.Spaces.eta_lt_one
  linarith

theorem sig_eta_le_sig_gam (α : ℝ) (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    sig Work.Spaces.eta θ ≤ sig (Work.Spaces.gam α) θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  rw [sig, sig]
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith [eta_le_gam α hα])

theorem one_le_sig_eta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    1 ≤ sig Work.Spaces.eta θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_exponent_ge hs hs1
    (show -(Work.Spaces.eta) ≤ -(0 : ℝ) by
      have := Work.Spaces.eta_pos; linarith)
  rw [sig]
  simpa using h



end Work.FTS.CoercivityFix.Coer1
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.HardyBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

theorem HkMem_four_of_five (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (h : Work.Spaces.HkMem α 5 f) : Work.Spaces.HkMem α 4 f := by
  have hmono : ∀ z θ, Work.Spaces.HkIntegrand α 4 f z θ ≤ Work.Spaces.HkIntegrand α 5 f z θ :=
    fun z θ => Work.Coercivity.HkIntegrand_le_succ α 4 f z θ
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 f hsm
  have haesmJoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  constructor
  · intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with h0 | hpos
    · subst h0
      refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
      simp [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
    · have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
          (volume.restrict Work.Spaces.Iθ) :=
        Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hpos
      exact (h.1 z hz).mono' haesm (Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)]
        exact hmono z θ)
  · have haesm : AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        (volume.restrict Work.Spaces.Iz) := haesmJoint.integral_prod_right'
    refine h.2.mono' haesm ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)]
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
      (h.1 z hz) (Filter.Eventually.of_forall fun θ => hmono z θ)

/-- The radial `ℋ⁴`-energy density `B α f s = ∫_θ HkIntegrand α 4 f s θ`. -/
def B4 (α : ℝ) (f : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ

theorem B4_nonneg (α : ℝ) (f : ℝ → ℝ → ℝ) (s : ℝ) : 0 ≤ B4 α f s :=
  integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f s θ

theorem B4_integrableOn (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.IntegrableOn (B4 α f) (Set.Ioi (0 : ℝ)) :=
  hmem.2.mono_set Set.Ioi_subset_Ici_self

/-- Pointwise domination of the squared slice by the `ℋ⁴`-integrand on the open quadrant. -/
theorem slice_sq_le_HkIntegrand_div_w_sq (α : ℝ) {f : ℝ → ℝ → ℝ} {s θ : ℝ} (hs : 0 < s)
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (f s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2 := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
  have hSpos : 0 < S := by rw [hSdef]; exact Real.rpow_pos_of_pos hsin _
  have hSsq : S ^ 2 ≤ 1 := by
    have h2 : S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
      rw [hSdef, ← Real.rpow_natCast, ← Real.rpow_mul hsin.le]; norm_num
    calc S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := h2
      _ ≤ 1 := Real.rpow_le_one hsin.le (Real.sin_le_one _) (le_of_lt Work.Spaces.eta_pos)
  have hkey : (f s θ * (Work.Spaces.w s / S)) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f s θ := by
    simpa only [Work.Spaces.DzIter_zero] using
      Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ 0 (by norm_num)
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hstep : (f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f s θ := by
    calc (f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        ≤ (f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 / S ^ 2 := by
          rw [le_div_iff₀ (pow_pos hSpos 2)]
          nlinarith [mul_nonneg (sq_nonneg (f s θ)) (sq_nonneg (Work.Spaces.w s)), hSsq]
      _ = (f s θ * (Work.Spaces.w s / S)) ^ 2 := by rw [mul_pow, div_pow, mul_div_assoc]
      _ ≤ _ := hkey
  exact (le_div_iff₀ (pow_pos hwpos 2)).mpr hstep


/-- `∫_θ (f s θ)² ≤ B4 α f s / w(s)²` for `s > 0` (the slice `L²`-bound against the
`ℋ⁴`-integrand). -/
theorem phi_le_B4_div_w_sq (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 f)
    {s : ℝ} (hs : 0 < s) :
    ∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2 ≤ B4 α f s / (Work.Spaces.w s) ^ 2 := by
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hpt : (fun θ => (f s θ) ^ 2) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2) := by
    have hcongr : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (π / 2))).symm
    rw [hcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => slice_sq_le_HkIntegrand_div_w_sq α hs hθ.1 hθ.2)
  have hg : MeasureTheory.Integrable
      (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := (hmem.1 s hs.le).div_const _
  have h := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => sq_nonneg (f s θ)) hg hpt
  rwa [MeasureTheory.integral_div] at h


/-- The pointwise bound behind `intB`: `(∫_θ f z θ²)/z^{2j} ≤ B4 α f z` for `z > 0`, `j ≤ 2`. -/
theorem phi_div_rpow_le_B4 (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) (j : ℕ) (hj : j ≤ 2) :
    (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z ^ (2 * (j : ℝ)) ≤ B4 α f z := by
  have hwpos : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have h1 : ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 ≤ B4 α f z / (Work.Spaces.w z) ^ 2 :=
    phi_le_B4_div_w_sq α hmem hz
  have hB : 0 ≤ B4 α f z := B4_nonneg α f z
  -- `w(z)^2 * z^{2j} ≥ 1`
  have key : 1 ≤ Work.Spaces.w z ^ 2 * z ^ (2 * (j : ℝ)) := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with h | h | h
    · subst h
      rw [show (2 * ((0 : ℕ) : ℝ)) = 0 by norm_num, Real.rpow_zero, mul_one]
      have hw1 : 1 ≤ Work.Spaces.w z := by
        rw [Work.Spaces.w, one_le_div (by positivity)]
        nlinarith
      nlinarith
    · subst h
      rw [show (2 * ((1 : ℕ) : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [Work.Spaces.w, div_pow]
      field_simp
      nlinarith [sq_nonneg z, sq_nonneg (1 + z), le_of_lt hz]
    · subst h
      rw [show (2 * ((2 : ℕ) : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [Work.Spaces.w, div_pow]
      field_simp
      have h1z : (1 : ℝ) ≤ 1 + z := by linarith
      have h4 : (1 : ℝ) ^ 4 ≤ (1 + z) ^ 4 := pow_le_pow_left₀ (by norm_num) h1z 4
      norm_num at h4
      linarith
  have hden_pos : 0 < Work.Spaces.w z ^ 2 * z ^ (2 * (j : ℝ)) :=
    mul_pos (pow_pos hwpos 2) (Real.rpow_pos_of_pos hz _)
  have h2 : B4 α f z / (Work.Spaces.w z) ^ 2 / z ^ (2 * (j : ℝ)) ≤ B4 α f z := by
    rw [div_div, div_le_iff₀ hden_pos]
    nlinarith
  calc (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z ^ (2 * (j : ℝ))
      ≤ B4 α f z / (Work.Spaces.w z) ^ 2 / z ^ (2 * (j : ℝ)) :=
        div_le_div_of_nonneg_right h1 (le_of_lt (Real.rpow_pos_of_pos hz _))
    _ ≤ B4 α f z := h2





/-- The tail of the `L₁₂`-density is minus the primitive: for `z > 0`,
`L12f f z = -∫_0^z L12dens K f`. -/
theorem L12f_eq_neg_prim {f : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0) {z : ℝ} (hz : 0 < z) :
    Work.Coercivity.L12f f z
      = -∫ s in (0 : ℝ)..z, Work.FM.L12dens Work.Spaces.K f s := by
  set G : ℝ → ℝ := fun s => Work.FM.L12dens Work.Spaces.K f s with hGdef
  have h1 : MeasureTheory.IntegrableOn G (Set.Ioc (0 : ℝ) z) :=
    hint.mono_set fun t ht => ht.1
  have h2 : MeasureTheory.IntegrableOn G (Set.Ioi z) :=
    hint.mono_set (Set.Ioi_subset_Ioi hz.le)
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) z) (Set.Ioi z) := by
    rw [Set.disjoint_left]
    intro t ht1 ht2
    exact absurd ht2 (not_lt.mpr ht1.2)
  have hU : Set.Ioc (0 : ℝ) z ∪ Set.Ioi z = Set.Ioi (0 : ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact lt_trans hz h
    · intro h
      rcases lt_trichotomy t z with h' | h' | h'
      · exact Or.inl ⟨h, h'.le⟩
      · exact Or.inl ⟨h, le_of_eq h'⟩
      · exact Or.inr h'
  have hsum := MeasureTheory.setIntegral_union hdisj (measurableSet_Ioi) h1 h2
  rw [hU] at hsum
  have hl12' : ∫ s in Set.Ioi (0 : ℝ), G s = 0 := by
    simpa [G, Work.Coercivity.L12f, Work.FM.L12] using hl12
  have hkey : ∫ s in Set.Ioi z, G s = -∫ s in Set.Ioc (0 : ℝ) z, G s := by linarith
  rw [Work.Coercivity.L12f, Work.FM.L12, hkey, intervalIntegral.integral_of_le hz.le]

/-- Cauchy–Schwarz with the constant function `1` on `(0,z]`:
`(∫_{(0,z]} Ψ)² ≤ z · ∫_{(0,z]} Ψ²`. -/
theorem cs_one {z : ℝ} (hz : 0 < z) {Ψ : ℝ → ℝ}
    (hΨ : MemLp Ψ 2 (volume.restrict (Set.Ioc 0 z))) :
    (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 ≤ z * ∫ s in Set.Ioc 0 z, (Ψ s) ^ 2 := by
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc 0 z)) := memLp_const 1
  have hcs := Work.Spaces.cs_integral h1 hΨ
  have hone : (∫ s in Set.Ioc 0 z, (1 : ℝ) ^ 2) = z := by
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, one_pow, mul_one]
    rw [MeasureTheory.Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hmul : (∫ s in Set.Ioc 0 z, (1 : ℝ) * Ψ s) = ∫ s in Set.Ioc 0 z, Ψ s := by
    simp
  rw [hmul, hone] at hcs
  linarith




/-- `∫_{s>z} s⁻² = 1/z`. -/
theorem integral_Ioi_inv_sq {z : ℝ} (hz : 0 < z) :
    ∫ s in Set.Ioi z, (s⁻¹) ^ 2 = 1 / z := by
  have h := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := z) (by norm_num) hz
  have h1 : ∫ s in Set.Ioi z, s ^ (-2 : ℝ) = 1 / z := by
    rw [h, show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    field_simp
  rw [← h1]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs0 : 0 < s := lt_trans hz hs
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hs0.le, Real.rpow_natCast,
    inv_pow]

theorem inv_sq_integrableOn {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun s : ℝ => (s⁻¹) ^ 2) (Set.Ioi z) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := z) (by norm_num) hz).congr_fun
    (fun s hs => ?_) measurableSet_Ioi
  have hs0 : 0 < s := lt_trans hz hs
  show s ^ (-2 : ℝ) = (s⁻¹) ^ 2
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hs0.le, Real.rpow_natCast,
    inv_pow]

theorem inv_memLp_Ioi {z : ℝ} (hz : 0 < z) :
    MemLp (fun s : ℝ => s⁻¹) 2 (volume.restrict (Set.Ioi z)) :=
  (MeasureTheory.memLp_two_iff_integrable_sq measurable_inv.aestronglyMeasurable).mpr
    (inv_sq_integrableOn hz)





theorem B4_tail_tendsto (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Filter.Tendsto (fun z : ℝ => ∫ s in Set.Ioi z, B4 α f s) Filter.atTop (𝓝 0) :=
  MeasureTheory.tendsto_integral_Ioi_zero (b := fun z : ℝ => z) tendsto_id

/-- `L12f f` is continuous on `(0,∞)` as soon as the density is continuous there. -/
theorem L12f_continuousOn {f : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z) :
    ContinuousOn (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) := by
  intro z hz
  exact ((Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := f) (a := 0) (ρ := z)
    hint (hcont z hz) hz).continuousAt).continuousWithinAt

/-- A.e. strong measurability of `L12f f` on any subset of `(0,∞)`. -/
theorem L12f_aesm_mono {f : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z)
    {u : Set ℝ} (hu : u ⊆ Set.Ioi (0 : ℝ)) :
    AEStronglyMeasurable (Work.Coercivity.L12f f) (volume.restrict u) :=
  (L12f_continuousOn hint hcont).aestronglyMeasurable measurableSet_Ioi |>.mono_measure
    (MeasureTheory.Measure.restrict_mono_set volume hu)

/-- The density is a.e. strongly measurable on `(1,∞)` as soon as it is continuous there. -/
theorem L12dens_aesm_Ioi {f : ℝ → ℝ → ℝ}
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z) :
    AEStronglyMeasurable (Work.FM.L12dens Work.Spaces.K f) (volume.restrict (Set.Ioi 1)) := by
  have hcontOn : ContinuousOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi (0 : ℝ)) :=
    fun z hz => (hcont z hz).continuousWithinAt
  exact (hcontOn.aestronglyMeasurable measurableSet_Ioi).mono_measure
    (MeasureTheory.Measure.restrict_mono_set volume (Set.Ioi_subset_Ioi zero_le_one))

/-- `∫_{(0,z]} B4 → 0` as `z → 0⁺`. -/
theorem Ioc_B4_tendsto_zero (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 f) :
    Filter.Tendsto (fun z => ∫ s in Set.Ioc 0 z, B4 α f s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  set g : ℝ → ℝ := (Set.Ioi (0 : ℝ)).indicator (B4 α f) with hgdef
  have hg_int : MeasureTheory.Integrable g volume := by
    rw [hgdef, MeasureTheory.integrable_indicator_iff measurableSet_Ioi]
    exact B4_integrableOn α f hmem
  have hg_aesm : AEStronglyMeasurable g volume := hg_int.aestronglyMeasurable
  have hmain : Filter.Tendsto (fun z => ∫ s, (Set.Ioc 0 z).indicator g s ∂volume)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (F := fun (z : ℝ) (s : ℝ) => (Set.Ioc 0 z).indicator g s)
      (f := fun _ : ℝ => (0 : ℝ)) (bound := fun s => |g s|) (l := 𝓝[>] (0 : ℝ))
      (Filter.Eventually.of_forall fun z => hg_aesm.indicator measurableSet_Ioc)
      (Filter.Eventually.of_forall fun z => Filter.Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs]
        by_cases hs : s ∈ Set.Ioc 0 z
        · rw [Set.indicator_of_mem hs]
        · rw [Set.indicator_of_notMem hs, abs_zero]
          exact abs_nonneg _)
      hg_int.abs
      (Filter.Eventually.of_forall fun s => ?_)
    simpa using h
    by_cases hs : (0 : ℝ) < s
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Ioo_mem_nhdsGT hs] with z hz
      rw [Set.indicator_of_notMem]
      exact fun hmem => absurd hmem.2 (not_le.mpr hz.2)
    · have hz0 : g s = 0 := by
        rw [hgdef, Set.indicator_of_notMem]
        simp only [Set.mem_Ioi, not_lt]
        linarith [not_lt.mp hs]
      rw [show (fun z => (Set.Ioc 0 z).indicator g s) = fun _ => (0 : ℝ) from
        funext fun z => by
          rw [Set.indicator_of_notMem]
          exact fun hmem => absurd hmem.1 (not_lt.mpr (not_lt.mp hs))]
      exact tendsto_const_nhds
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
  rw [hgdef, Set.indicator_of_mem]
  exact hs.1








end Work.FTS.CoercivityFix.Coer1T
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.LhatCalc

set_option autoImplicit false

namespace DthAux

/-! ## The open quadrant of `SmoothQuad`

`Work.FTS.LocData.SmoothQuad g = ContDiffOn ℝ smoothOrder (uncurry g) QuadL`, where
`QuadL = (-1,∞) × (0,π/2)`. -/

/-- The open quadrant on which `Work.FTS.LocData.SmoothQuad` is stated. -/
abbrev QuadL : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (0 : ℝ) (π / 2)

theorem isOpen_QuadL : IsOpen QuadL := isOpen_Ioi.prod isOpen_Ioo

theorem mem_QuadL_iff {z θ : ℝ} : ((z, θ) ∈ QuadL) ↔ -1 < z ∧ 0 < θ ∧ θ < π / 2 := by
  rw [QuadL, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]



theorem smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]

theorem smoothOrder_add_one : Work.Stability.smoothOrder + 1 = Work.Stability.smoothOrder := rfl

/-! ## Differential calculus in the genuine smooth order

The two lemmas below are the `smoothOrder`-analogues of `Work.Spaces.contDiffOn_uncurry_pz` and
`Work.Spaces.contDiffOn_uncurry_pth`; a `SmoothQuad` datum is only `C^∞`, so the `⊤`-versions
do not apply to it.  The proofs are those of the `⊤`-versions with `⊤` replaced by
`smoothOrder` and `le_rfl` by `le_of_eq smoothOrder_add_one`. -/

theorem contDiffOn_uncurry_pz_sm {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (n := Work.Stability.smoothOrder) smoothOrder_ne_zero).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) hV.uniqueDiffOn
      (le_of_eq smoothOrder_add_one)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

theorem contDiffOn_uncurry_pth_sm {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (n := Work.Stability.smoothOrder) smoothOrder_ne_zero).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) hV.uniqueDiffOn
      (le_of_eq smoothOrder_add_one)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-! ## Two `θ`-derivative computations -/

/-- **The `θ`-derivative of `𝓛`**: at an interior point of the quadrant, where `g` is `C^∞`,
`∂_θ(𝓛 g) = ∂_θ g + z ∂_z∂_θ g − (2/(1+z)) ∂_θ g`.  (The `⊤`-version is
`Work.Coercivity.pth_L`; here the class is `SmoothQuad`, i.e. the genuine smooth order.) -/
theorem pth_L_of_smooth {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) {z θ : ℝ}
    (hy : (z, θ) ∈ V) :
    Work.Spaces.pth (Work.Coercivity.L g) z θ
      = Work.Spaces.pth g z θ + z * Work.Spaces.pz (Work.Spaces.pth g) z θ
        - (2 / (1 + z)) * Work.Spaces.pth g z θ := by
  have hcf : ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry g) (z, θ) :=
    hcd.contDiffAt (hV.mem_nhds hy)
  have hcd2 : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ) :=
    hcf.of_le (by simp [Work.Stability.smoothOrder])
  have hgθ : DifferentiableAt ℝ (fun θ' => g z θ') θ :=
    Work.Spaces.differentiableAt_curry_right (hcf.differentiableAt smoothOrder_ne_zero)
  have hpz_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz g)) V :=
    contDiffOn_uncurry_pz_sm hV hcd
  have hpzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz g z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpz_sm.contDiffAt (hV.mem_nhds hy)).differentiableAt smoothOrder_ne_zero)
  have e : (fun θ' => Work.Coercivity.L g z θ')
      = (fun θ' => g z θ' + z * Work.Spaces.pz g z θ' - (2 / (1 + z)) * g z θ') := by
    funext θ'; simp only [Work.Coercivity.L, Work.Spaces.Dz]; ring
  show deriv (fun θ' => Work.Coercivity.L g z θ') θ = _
  rw [e]
  rw [show (fun θ' : ℝ => g z θ' + z * Work.Spaces.pz g z θ' - (2 / (1 + z)) * g z θ')
      = (((fun θ' : ℝ => g z θ') + (fun θ' : ℝ => z * Work.Spaces.pz g z θ'))
          - (fun θ' : ℝ => (2 / (1 + z)) * g z θ')) from rfl]
  rw [deriv_sub (hgθ.add (hpzθ.const_mul z)) (hgθ.const_mul (2 / (1 + z)))]
  rw [deriv_add hgθ (hpzθ.const_mul z)]
  rw [deriv_const_mul_field, deriv_const_mul_field]
  rw [show deriv (fun θ' => g z θ') θ = Work.Spaces.pth g z θ from rfl,
      show deriv (fun θ' => Work.Spaces.pz g z θ') θ
        = Work.Spaces.pth (Work.Spaces.pz g) z θ from rfl,
      ← Work.Spaces.pz_pth_comm hcd2]

/-- `deriv (fun θ' => sin (2θ')) θ = 2 cos (2θ)`. -/
theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ h2
  simpa [Function.comp_def, mul_comm] using h

/-- **The `θ`-derivative of `D_θ g`**: `∂_θ D_θ g = 2cos(2θ) ∂_θ g + sin(2θ) ∂_θ² g`, as soon
as the `θ`-slice of `∂_θ g` is differentiable at `θ`. -/
theorem pth_Dth_eq {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth g z θ') θ) :
    Work.Spaces.pth (Work.Spaces.Dth g) z θ
      = 2 * Real.cos (2 * θ) * Work.Spaces.pth g z θ
        + Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.pth g) z θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ') * Work.Spaces.pth g z θ')
      (2 * Real.cos (2 * θ) * Work.Spaces.pth g z θ
        + Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.pth g) z θ) θ :=
    (hasDerivAt_sin_two θ).mul h.hasDerivAt
  show deriv (fun θ' => Work.Spaces.Dth g z θ') θ = _
  rw [show (fun θ' => Work.Spaces.Dth g z θ')
      = (fun θ' => Real.sin (2 * θ') * Work.Spaces.pth g z θ') from by
    funext θ'; simp only [Work.Spaces.Dth]]
  exact h2.deriv

end DthAux

open DthAux

/-! ## The `D_θ`-commutator of `𝓛̂` -/

/-- **`D_θ` commutes exactly with `𝓛̂ = 𝓛 − Transport`**:
`D_θ(𝓛̂ f) = 𝓛̂(D_θ f)` for every `C^∞` datum on the open quadrant.  There is no commutator
term, no nonlocal contribution and no zero-mode hypothesis. -/
theorem Dth_Lhat {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ := by
  have hlt : -1 < z := by linarith
  have hmem : (z, θ) ∈ QuadL := mem_QuadL_iff.mpr ⟨hlt, hθ, hθ2⟩
  have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) QuadL := hf
  have hcf : ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry f) (z, θ) :=
    hcd.contDiffAt (isOpen_QuadL.mem_nhds hmem)
  have hfθ : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right (hcf.differentiableAt smoothOrder_ne_zero)
  have hpz_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz f)) QuadL := contDiffOn_uncurry_pz_sm isOpen_QuadL hcd
  have hpzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpz_sm.contDiffAt (isOpen_QuadL.mem_nhds hmem)).differentiableAt smoothOrder_ne_zero)
  have hpth_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth f)) QuadL := contDiffOn_uncurry_pth_sm isOpen_QuadL hcd
  have hpthθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpth_sm.contDiffAt (isOpen_QuadL.mem_nhds hmem)).differentiableAt smoothOrder_ne_zero)
  have dL : DifferentiableAt ℝ (fun θ' => Work.Coercivity.L f z θ') θ := by
    rw [show (fun θ' => Work.Coercivity.L f z θ')
        = (fun θ' => f z θ' + z * Work.Spaces.pz f z θ' - (2 / (1 + z)) * f z θ') from by
      funext θ'; simp only [Work.Coercivity.L, Work.Spaces.Dz]; ring]
    exact (hfθ.add (hpzθ.const_mul z)).sub (hfθ.const_mul (2 / (1 + z)))
  have hDθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dth f z θ') θ := by
    rw [show (fun θ' => Work.Spaces.Dth f z θ')
        = (fun θ' => Real.sin (2 * θ') * Work.Spaces.pth f z θ') from by
      funext θ'; simp only [Work.Spaces.Dth]]
    exact ((hasDerivAt_sin_two θ).differentiableAt).mul hpthθ
  have dTr : DifferentiableAt ℝ (fun θ' => Work.Coercivity.Transport f z θ') θ := by
    rw [show (fun θ' => Work.Coercivity.Transport f z θ')
        = (fun θ' => (3 / (1 + z)) * Work.Spaces.Dth f z θ') from by
      funext θ'; simp only [Work.Coercivity.Transport]; ring]
    exact hDθ.const_mul (3 / (1 + z))
  have hpth : Work.Spaces.pth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.Spaces.pth (Work.Coercivity.L f) z θ
        - Work.Spaces.pth (Work.Coercivity.Transport f) z θ := by
    show deriv (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ') θ = _
    rw [show (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ')
        = ((fun θ' => Work.Coercivity.L f z θ')
            - fun θ' => Work.Coercivity.Transport f z θ') from by
      funext θ'; simp only [Work.FTS.CoercivityFix.Lhat, Pi.sub_apply]]
    rw [deriv_sub dL dTr]
    rfl
  rw [show Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.FTS.CoercivityFix.Lhat f) z θ from rfl]
  rw [hpth]
  rw [Work.FTS.CoercivityFix.Lhat_eq (Work.Spaces.Dth f) z θ]
  rw [pth_L_of_smooth isOpen_QuadL hcd hmem, Work.Coercivity.pth_Transport]
  rw [show Work.Spaces.Dz (Work.Spaces.Dth f) z θ
      = z * Work.Spaces.pz (Work.Spaces.Dth f) z θ from rfl]
  rw [Work.Coercivity.pz_Dth_val]
  rw [show Work.Spaces.Dth (Work.Spaces.Dth f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.Dth f) z θ from rfl]
  rw [show Work.Spaces.Dth f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ from rfl]
  rw [pth_Dth_eq (g := f) hpthθ]
  ring

end Work.FTS.CoercivityFix.LhatCalc

end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.LhatCalc.Dz_Lhat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.LhatCalc

set_option autoImplicit false

/-! ## The open quadrant and the smoothness of the plain partials

`Work.FTS.LocData.SmoothQuad f` is smoothness of `Function.uncurry f` **on the open set**
`quadU = (-1,∞) × (0,π/2)`, in the order `Work.Stability.smoothOrder`.  Everything below is
local at an interior point `(z,θ)` of `quadU`, so we re-derive the few smoothness facts we
need from the class directly (rather than importing the heavy `QuadAux` module).
-/

/-- The open quadrant on which `Work.FTS.LocData.SmoothQuad` is stated. -/
private def quadU : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)

private lemma isOpen_quadU : IsOpen quadU := isOpen_Ioi.prod isOpen_Ioo

private lemma mem_quadU_iff {z θ : ℝ} :
    ((z, θ) ∈ quadU) ↔ -1 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
  rw [quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

private lemma mem_quadU {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    (z, θ) ∈ quadU :=
  mem_quadU_iff.mpr ⟨by linarith, hθ, hθ2⟩

private lemma smoothQuad_contDiffAt {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry f) (z, θ) :=
  (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadU from hf).contDiffAt
    (isOpen_quadU.mem_nhds (mem_quadU hz hθ hθ2))

private lemma smoothQuad_contDiffAt_two {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
  (smoothQuad_contDiffAt hf hz hθ hθ2).of_le (by simp [Work.Stability.smoothOrder])

/-- The `z`-partial of a `C^∞`-on-`quadU` function is `C^∞` on `quadU`. -/
private lemma contDiffOn_uncurry_pz_quadU {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) quadU) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pz G)) quadU := by
  have hchain : ∀ p ∈ quadU, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (n := Work.Stability.smoothOrder)
        (by simp [Work.Stability.smoothOrder])).differentiableAt (isOpen_quadU.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) quadU := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) isOpen_quadU.uniqueDiffOn
      (by simp [Work.Stability.smoothOrder])
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen isOpen_quadU hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) quadU := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The `θ`-partial of a `C^∞`-on-`quadU` function is `C^∞` on `quadU`. -/
private lemma contDiffOn_uncurry_pth_quadU {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) quadU) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pth G)) quadU := by
  have hchain : ∀ p ∈ quadU, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (n := Work.Stability.smoothOrder)
        (by simp [Work.Stability.smoothOrder])).differentiableAt (isOpen_quadU.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) quadU := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) isOpen_quadU.uniqueDiffOn
      (by simp [Work.Stability.smoothOrder])
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen isOpen_quadU hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) quadU := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

section Slices

variable {f : ℝ → ℝ → ℝ}

/-- The `z`-slices of `∂_z f` are differentiable at an interior point of the quadrant. -/
private lemma diff_z_pz (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z :=
  Work.Spaces.differentiableAt_curry_left
    (((contDiffOn_uncurry_pz_quadU
        (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadU from hf)).contDiffAt
      (isOpen_quadU.mem_nhds (mem_quadU hz hθ hθ2))).differentiableAt
      (by simp [Work.Stability.smoothOrder]))

/-- The `θ`-slices of `∂_z f` are differentiable at an interior point of the quadrant. -/
private lemma diff_th_pz (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ :=
  Work.Spaces.differentiableAt_curry_right
    (((contDiffOn_uncurry_pz_quadU
        (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadU from hf)).contDiffAt
      (isOpen_quadU.mem_nhds (mem_quadU hz hθ hθ2))).differentiableAt
      (by simp [Work.Stability.smoothOrder]))

/-- The `z`-slices of `∂_θ f` are differentiable at an interior point of the quadrant. -/
private lemma diff_z_pth (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z :=
  Work.Spaces.differentiableAt_curry_left
    (((contDiffOn_uncurry_pth_quadU
        (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadU from hf)).contDiffAt
      (isOpen_quadU.mem_nhds (mem_quadU hz hθ hθ2))).differentiableAt
      (by simp [Work.Stability.smoothOrder]))

/-- The `z`-slices of `f` are differentiable at an interior point of the quadrant. -/
private lemma diff_z_self (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun z' => f z' θ) z :=
  Work.Spaces.differentiableAt_curry_left
    ((smoothQuad_contDiffAt hf hz hθ hθ2).differentiableAt
      (by simp [Work.Stability.smoothOrder]))

end Slices

/-! ## The plain `z`-derivatives of the pieces -/

private lemma deriv_z_self {f : ℝ → ℝ → ℝ} {z θ : ℝ} :
    deriv (fun z' => f z' θ) z = Work.Spaces.pz f z θ := rfl

private lemma deriv_z_mul_pz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z
      = Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ := by
  have hh := (hasDerivAt_id z).mul hpzz.hasDerivAt
  have h2 : deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z
      = deriv (id * fun z' : ℝ => Work.Spaces.pz f z' θ) z := rfl
  rw [h2, hh.deriv]
  simp only [id_eq, one_mul]
  rfl

private lemma deriv_z_two_div {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hfz : DifferentiableAt ℝ (fun z' => f z' θ) z) :
    deriv (fun z' : ℝ => 2 * f z' θ / (1 + z')) z
      = 2 * Work.Spaces.pz f z θ / (1 + z) - 2 * f z θ / (1 + z) ^ 2 := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hh := (hfz.hasDerivAt.const_mul (2 : ℝ)).div
    ((hasDerivAt_const (x := z) (1 : ℝ)).add (hasDerivAt_id z)) (by simpa using hden)
  have h2 : deriv (fun z' : ℝ => 2 * f z' θ / (1 + z')) z
      = deriv ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z := rfl
  rw [h2, hh.deriv]
  simp only [Pi.add_apply, id_eq, zero_add]
  rw [deriv_z_self]
  field_simp
  try ring_nf

private lemma deriv_z_three_div {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hpthz : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z) :
    deriv (fun z' : ℝ => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) z
      = 3 * (Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ) / (1 + z)
        - 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z θ) / (1 + z) ^ 2 := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hh := (((hasDerivAt_const (x := z) (Real.sin (2 * θ))).mul hpthz.hasDerivAt).const_mul
    (3 : ℝ)).div ((hasDerivAt_const (x := z) (1 : ℝ)).add (hasDerivAt_id z))
    (by simpa using hden)
  have h2 : deriv (fun z' : ℝ => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) z
      = deriv ((fun y : ℝ => (fun _ : ℝ => (3 : ℝ)) y
            * ((fun _ : ℝ => Real.sin (2 * θ)) * fun z' => Work.Spaces.pth f z' θ) y)
          / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z := rfl
  rw [h2, hh.deriv]
  simp only [Pi.add_apply, Pi.mul_apply, id_eq, zero_add, zero_mul]
  rw [show deriv (fun z' => Work.Spaces.pth f z' θ) z
      = Work.Spaces.pz (Work.Spaces.pth f) z θ from rfl]
  field_simp
  try ring_nf

private lemma deriv_z_Dz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    deriv (fun z' => Work.Spaces.Dz f z' θ) z
      = Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ := by
  have hh := (hasDerivAt_id z).mul hpzz.hasDerivAt
  have h1 : (fun z' => Work.Spaces.Dz f z' θ)
      = (id * fun z' : ℝ => Work.Spaces.pz f z' θ) := by
    funext z'; rfl
  rw [h1, hh.deriv]
  simp only [id_eq, one_mul]
  rfl

private lemma deriv_th_Dz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ) :
    deriv (fun θ' => Work.Spaces.Dz f z θ') θ = z * Work.Spaces.pth (Work.Spaces.pz f) z θ := by
  have hh := (hasDerivAt_const (x := θ) z).mul hpzθ.hasDerivAt
  have h1 : (fun θ' => Work.Spaces.Dz f z θ')
      = ((fun _ : ℝ => z) * fun θ' => Work.Spaces.pz f z θ') := by
    funext θ'; rfl
  rw [h1, hh.deriv]
  simp only [zero_mul, zero_add]
  rfl

/-! ## The `z`-derivatives of the slices of `𝓛 f` and of `Transport f` -/

private lemma pz_L_eq {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hfz : DifferentiableAt ℝ (fun z' => f z' θ) z)
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    Work.Spaces.pz (Work.Coercivity.L f) z θ
      = Work.Spaces.pz f z θ + (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
        - 2 * Work.Spaces.pz f z θ / (1 + z) + 2 * f z θ / (1 + z) ^ 2 := by
  show deriv (fun z' => Work.Coercivity.L f z' θ) z = _
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hid : DifferentiableAt ℝ (id * fun z' : ℝ => Work.Spaces.pz f z' θ) z :=
    differentiableAt_id.mul hpzz
  have hq : DifferentiableAt ℝ
      ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z :=
    (hfz.const_mul 2).div ((differentiableAt_const _).add differentiableAt_id)
      (by simpa using hden)
  have h1 : (fun z' => Work.Coercivity.L f z' θ)
      = (((fun z' : ℝ => f z' θ) + (id * fun z' : ℝ => Work.Spaces.pz f z' θ))
          - ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ)))) := by
    funext z'; rfl
  rw [h1, deriv_sub (hfz.add hid) hq, deriv_add hfz hid]
  rw [show deriv (id * fun z' : ℝ => Work.Spaces.pz f z' θ) z
      = deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z from rfl]
  rw [show deriv ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z
      = deriv (fun z' : ℝ => 2 * f z' θ / (1 + z')) z from rfl]
  rw [deriv_z_mul_pz hpzz, deriv_z_two_div hz hfz, deriv_z_self]
  ring

private lemma pz_Transport_eq {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hpthz : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z) :
    Work.Spaces.pz (Work.Coercivity.Transport f) z θ
      = 3 * (Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ) / (1 + z)
        - 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z θ) / (1 + z) ^ 2 := by
  show deriv (fun z' => Work.Coercivity.Transport f z' θ) z = _
  have h1 : (fun z' => Work.Coercivity.Transport f z' θ)
      = (fun z' : ℝ => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) := by
    funext z'; rfl
  rw [h1, deriv_z_three_div hz hpthz]

private lemma diff_slice_L {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hfz : DifferentiableAt ℝ (fun z' => f z' θ) z)
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    DifferentiableAt ℝ (fun z' => Work.Coercivity.L f z' θ) z := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  rw [show (fun z' => Work.Coercivity.L f z' θ)
      = (fun z' => f z' θ + z' * Work.Spaces.pz f z' θ - 2 * f z' θ / (1 + z')) from by
    funext z'; rfl]
  exact (hfz.add (differentiableAt_id.mul hpzz)).sub
    ((hfz.const_mul 2).div ((differentiableAt_const _).add differentiableAt_id)
      (by simpa using hden))

private lemma diff_slice_Transport {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hpthz : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z) :
    DifferentiableAt ℝ (fun z' => Work.Coercivity.Transport f z' θ) z := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  rw [show (fun z' => Work.Coercivity.Transport f z' θ)
      = (fun z' => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) from by
    funext z'; rfl]
  exact (((differentiableAt_const (c := Real.sin (2 * θ))).mul hpthz).const_mul 3).div
    ((differentiableAt_const (c := (1 : ℝ))).add differentiableAt_id) (by simpa using hden)

/-! ## The commutator identity -/

/-- **The `D_z`-commutator of the clean operator** `𝓛̂ = 𝓛 − Transport`:
`D_z(𝓛̂ f) = 𝓛̂(D_z f) + Ê₂ f`, with the explicit bounded defect
`Ê₂ f = (2zf + 3z D_θ f)/(1+z)²`. -/
theorem Dz_Lhat {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hfz := diff_z_self hf hz hθ hθ2
  have hpzz := diff_z_pz hf hz hθ hθ2
  have hpzθ := diff_th_pz hf hz hθ hθ2
  have hpthz := diff_z_pth hf hz hθ hθ2
  have hLz := diff_slice_L (θ := θ) hz hfz hpzz
  have hTz := diff_slice_Transport (θ := θ) hz hpthz
  -- the plain `z`-derivatives of the two summands of `𝓛̂`
  have hpzL := pz_L_eq (θ := θ) hz hfz hpzz
  have hpzT := pz_Transport_eq (θ := θ) hz hpthz
  have hpzLhat : Work.Spaces.pz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.Spaces.pz (Work.Coercivity.L f) z θ
        - Work.Spaces.pz (Work.Coercivity.Transport f) z θ := by
    show deriv (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ) z = _
    have h1 : (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ)
        = ((fun z' => Work.Coercivity.L f z' θ)
            - fun z' => Work.Coercivity.Transport f z' θ) := by
      funext z'; rfl
    rw [h1, deriv_sub hLz hTz]
    rfl
  have hLHS : Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = z * (Work.Spaces.pz (Work.Coercivity.L f) z θ
          - Work.Spaces.pz (Work.Coercivity.Transport f) z θ) := by
    show z * deriv (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ) z = _
    rw [show deriv (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ) z
        = Work.Spaces.pz (Work.FTS.CoercivityFix.Lhat f) z θ from rfl, hpzLhat]
  -- the right-hand side
  have hDzDz : Work.Spaces.Dz (Work.Spaces.Dz f) z θ
      = z * (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ) := by
    show z * deriv (fun z' => Work.Spaces.Dz f z' θ) z = _
    rw [deriv_z_Dz hpzz]
  have hDthDz : Work.Spaces.Dth (Work.Spaces.Dz f) z θ
      = Real.sin (2 * θ) * (z * Work.Spaces.pth (Work.Spaces.pz f) z θ) := by
    show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.Dz f z θ') θ = _
    rw [deriv_th_Dz hpzθ]
  have hRHS : Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ
      = (z * Work.Spaces.pz f z θ
          + z * (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
          - 2 * (z * Work.Spaces.pz f z θ) / (1 + z)
          - 3 * (Real.sin (2 * θ) * (z * Work.Spaces.pth (Work.Spaces.pz f) z θ)) / (1 + z))
        + (2 * z * f z θ + 3 * z * (Real.sin (2 * θ) * Work.Spaces.pth f z θ)) / (1 + z) ^ 2 := by
    rw [Work.FTS.CoercivityFix.Lhat_eq (Work.Spaces.Dz f), Work.FTS.CoercivityFix.E2hat_eq]
    rw [hDzDz, hDthDz]
    rw [show Work.Spaces.Dz f z θ = z * Work.Spaces.pz f z θ from rfl,
      show Work.Spaces.Dth f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ from rfl]
  -- Clairaut's theorem finishes the identification `∂_θ∂_z f = ∂_z∂_θ f`
  have hcl := Work.Spaces.pz_pth_comm (smoothQuad_contDiffAt_two hf hz hθ hθ2)
  rw [hLHS, hRHS, hpzL, hpzT, hcl]
  field_simp
  try ring_nf

end Work.FTS.CoercivityFix.LhatCalc
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.StepAssembly.H1IP_congr_qd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.StepAssembly

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The iterated integral over `Iz × Iθ` equals the iterated integral over the open quadrant
`(0,∞) × (0,π/2)`: the difference is a null set, and both components are Bochner integrals. -/
lemma wip_eq_Ioi_Ioo (F : ℝ → ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), F z θ := by
  have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), F z θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    exact MeasureTheory.integral_Icc_eq_integral_Ioo
  rw [h1]
  exact MeasureTheory.integral_Ici_eq_integral_Ioi

/-- **Congruence of `wip` in its first argument on the open quadrant**, with no hypotheses. -/
lemma wip_congr_Qd {ρ A A' B : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → A z θ = A' z θ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ A' B := by
  simp only [Work.Coercivity.wip]
  rw [wip_eq_Ioi_Ioo (fun z θ => A z θ * B z θ * ρ z θ),
    wip_eq_Ioi_Ioo (fun z θ => A' z θ * B z θ * ρ z θ)]
  refine MeasureTheory.setIntegral_congr_fun
    (isOpen_Ioi (a := (0 : ℝ))).measurableSet (fun z hz => ?_)
  refine MeasureTheory.setIntegral_congr_fun
    (isOpen_Ioo (a := (0 : ℝ)) (b := Real.pi / 2)).measurableSet (fun θ hθ => ?_)
  rw [h z θ ⟨hz, hθ⟩]

/-- `D_z` preserves equality on the open quadrant (derivatives are local and `Qd` is open). -/
lemma Dz_congr_Qd {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  intro z θ hzθ
  have hz : (0 : ℝ) < z := hzθ.1
  have heq : Set.EqOn (fun t => f t θ) (fun t => f' t θ) (Set.Ioi 0) :=
    fun t ht => h t θ ⟨ht, hzθ.2⟩
  have hd := (heq.deriv isOpen_Ioi) hz
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hd]

/-- `D_θ` preserves equality on the open quadrant. -/
lemma Dth_congr_Qd {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  intro z θ hzθ
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : Set.EqOn (fun t => f z t) (fun t => f' z t) (Set.Ioo 0 (Real.pi / 2)) :=
    fun t ht => h z t ⟨hzθ.1, ht⟩
  have hd := (heq.deriv isOpen_Ioo) hθ
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hd]

/-- **The congruence of `H1IP α` in its first argument**, with no regularity hypotheses. -/
theorem H1IP_congr_qd (α : ℝ) {f f' g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    Work.Coercivity.H1IP α f g = Work.Coercivity.H1IP α f' g := by
  have hDz := Dz_congr_Qd h
  have hDth := Dth_congr_Qd h
  simp only [Work.Coercivity.H1IP]
  have h1 := wip_congr_Qd
    (ρ := (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
    (A := Work.Spaces.Dz f) (A' := Work.Spaces.Dz f') (B := Work.Spaces.Dz g) hDz
  have h2 := wip_congr_Qd
    (ρ := (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
    (A := f) (A' := f') (B := g) h
  have h3 := wip_congr_Qd
    (ρ := (fun z _ => Work.Spaces.w z ^ 2)) (A := f) (A' := f') (B := g) h
  have h4 := wip_congr_Qd
    (ρ := (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)))
    (A := Work.Spaces.Dth f) (A' := Work.Spaces.Dth f') (B := Work.Spaces.Dth g) hDth
  rw [h1, h2, h3, h4]

end Work.FTS.CoercivityFix.StepAssembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.E2hat_contDiffOn_three =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.CoercivityFix.Transfer.AuxE2

set_option autoImplicit false


end Work.FTS.CoercivityFix.Transfer.AuxE2
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.Profiles =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The radial shapes occurring in `𝓛_Γ^T` -/

/-- The `z`-factor `a(z) = 2z/(c(1+z)²)` of the nonlocal term of `𝓛_Γ`. -/
def ampA (α : ℝ) (z : ℝ) : ℝ := 2 * z / (Work.Spaces.c α * (1 + z) ^ 2)

/-- The `z`-factor `b(z) = 2z²/(1+z)³` of the projector correction. -/
def ampB (α : ℝ) (z : ℝ) : ℝ := 2 * z ^ 2 / (1 + z) ^ 3

/-- `D_z a = z·a'`, the `D_z`-derivative of the nonlocal `z`-factor. -/
def dAmpA (α : ℝ) (z : ℝ) : ℝ := z * deriv (ampA α) z

/-- `D_z b = z·b'`, the `D_z`-derivative of the projector correction's `z`-factor. -/
def dAmpB (α : ℝ) (z : ℝ) : ℝ := z * deriv (ampB α) z

/-- **The radial profile of the transfer defect**: `Corr α f = Γ(θ)·radA α f z`. -/
def radA (α : ℝ) (f : Fn) (z : ℝ) : ℝ :=
  -ampA α z * Work.Coercivity.L12f f z
    + (ampB α z / Work.Spaces.c α) * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0

/-- **The radial profile produced by `D_z`**: with `C₀(f) = L₁₂(Transport f)(0)`,
`radS α f z = −(D_z a)(z)·L₁₂ f(z) − a(z)·z·(L₁₂ f)'(z) + (b'(z)/c)·C₀(f)`.

Note the middle term: by the fundamental theorem of calculus
`z·(L₁₂ f)'(z) = −⟨K, f(z,·)⟩` (`Transfer.L12_deriv_eq`), i.e. an angular moment of `f` and
**not** an `L₁₂` of the differentiated datum.  This is exactly the point of design
`N45_DESIGN_LEAD.md` §5 T2. -/
def radS (α : ℝ) (f : Fn) (z : ℝ) : ℝ :=
  -dAmpA α z * Work.Coercivity.L12f f z
    - ampA α z * (z * deriv (Work.Coercivity.L12f f) z)
    + (dAmpB α z / Work.Spaces.c α) * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0

/-! ## The two defects -/

/-- **The `D_θ`-defect of the transfer.**  It is `α`-small: `|D_θΓ| ≤ 2αΓ` on `Iθ`. -/
def E1 (α : ℝ) (f : Fn) : Fn := fun z θ =>
  (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) * radA α f z

/-- **The `D_z`-defect of the transfer**: the clean defect `Ê₂` of `𝓛̂` plus the angular factor
`Γ` times the radial profile `radS`. -/
def E2 (α : ℝ) (f : Fn) : Fn := fun z θ =>
  Work.FTS.CoercivityFix.E2hat f z θ + Work.Spaces.Gam α θ * radS α f z

/-! ## `Corr` is `Γ` times a radial profile -/

/-- **`Corr α f = Γ(θ)·radA α f z`**: the transfer defect is a product of an angular function
and a radial one.  This is the structural fact the whole transfer rests on. -/
theorem Corr_eq_radA (α : ℝ) (f : Fn) (z θ : ℝ) :
    Work.FTS.CoercivityFix.Corr α f z θ = Work.Spaces.Gam α θ * radA α f z := by
  rw [Work.FTS.CoercivityFix.Corr_eq]
  simp only [radA, ampA, ampB]
  ring

/-- `radA` unfolded. -/
theorem radA_eq (α : ℝ) (f : Fn) (z : ℝ) :
    radA α f z = -(2 * z / (Work.Spaces.c α * (1 + z) ^ 2))
        * Work.Coercivity.L12f f z
      + (2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := rfl

/-- `E1` unfolded. -/
theorem E1_eq (α : ℝ) (f : Fn) (z θ : ℝ) :
    E1 α f z θ = (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) * radA α f z := rfl

/-- `E2` unfolded. -/
theorem E2_eq (α : ℝ) (f : Fn) (z θ : ℝ) :
    E2 α f z θ = Work.FTS.CoercivityFix.E2hat f z θ + Work.Spaces.Gam α θ * radS α f z := rfl

end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.differentiableAt_Lhat_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer


end Work.FTS.CoercivityFix.Transfer
end
-- ===== merged: Submission.Work.FTS.EllSol.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn Fam slice galFun)

set_option autoImplicit false

/-- **The shifted unknown** `Ψ ↦ Ψ + Gsing α g · sin 2θ` of §'The singular term': the function
to which the paper's elliptic estimates (`TT.EllWeakPos`/`TT.EllEstUnif`) are applied.  It is the
third component of `EllClassO`, and the difference `ellShift α g Ψ - Ψ = Gsing α g · sin 2θ`
carries the singular part of the stream function. -/
def ellShift (α : ℝ) (g Ψ : Fn) : Fn :=
  fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)

@[simp] theorem ellShift_apply (α : ℝ) (g Ψ : Fn) (z θ : ℝ) :
    ellShift α g Ψ z θ = Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ) := rfl

/-- **The solution class of the Hamel construction** (item (b) of the design, verbatim).

`Ψ` solves the elliptic problem `bslOp α Ψ = g` on the open quadrant (`IsBslSol`), is `C^∞` on
the open quadrant (`SmoothOpen`), and the *straightened* unknown `Ψ + Gsing α g · sin 2θ` is an
honest weak solution of the elliptic problem with source `orthSource g` (`TT.EllWeakPos`, the
class in which the paper's Proposition `prop:Hk` is stated — see
`Submission/Work/FTS/EllipticEst/TT/WeakDefs.lean`). -/
def EllClassO (α : ℝ) (g Ψ : Fn) : Prop :=
  Work.Elliptic.IsBslSol α g Ψ ∧ Work.FTS.EllipticEst.SmoothOpen Ψ ∧
  Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g) (ellShift α g Ψ)







/-! ## Elementary API of the class -/

theorem EllClassO.sol {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.Elliptic.IsBslSol α g Ψ := h.1

theorem EllClassO.smooth {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.FTS.EllipticEst.SmoothOpen Ψ := h.2.1



/-- The weak class is inhabited at `(F, Ψ) = (0, 0)`. -/
theorem ellWeakPos_zero (α : ℝ) (k : ℕ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α k (0 : Fn) (0 : Fn) := by
  have hz2 : (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (0 : Fn) z θ) = 0 := by
    funext z θ; rw [Work.FTS.EllipticEst.pzIter_zero_fun]; simp
  have hd2 : Work.Spaces.pthIter 2 (0 : Fn) = 0 :=
    Work.FTS.EllipticEst.pthIter_zero_fun 2
  have hzp : (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 (0 : Fn)) z θ) = 0 := by
    funext z θ; rw [hd2, Work.FTS.EllipticEst.pz_zero_fun]; simp
  refine ⟨?_, fun z => rfl, fun z => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz θ h0 h1
    have h := (Work.FTS.EllipticEst.IsBslSol_zero α).1 z hz θ h0 h1
    simpa using h
  · intro z hz; simp [Work.Elliptic.Fstar]
  · intro z hz; simp [Work.Elliptic.Fstar]
  · intro n
    change ContDiffOn ℝ n (fun _ : ℝ × ℝ => (0 : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
    exact contDiffOn_const
  · exact Work.FTS.EllipticEst.HkMem_zero α k
  · rw [hz2]; exact Work.FTS.EllipticEst.HkMem_zero α k
  · rw [hd2]; exact Work.FTS.EllipticEst.HkMem_zero α k
  · rw [hzp]; exact Work.FTS.EllipticEst.HkMem_zero α k

/-- `Gsing α 0 = 0`. -/
theorem Gsing_zero (α : ℝ) : Work.Elliptic.Gsing α (0 : Fn) = 0 := by
  funext z
  simp [Work.Elliptic.Gsing, Work.Elliptic.Gstar, Work.Elliptic.Gbar,
    Work.Elliptic.Fstar, Work.Elliptic.L12, Work.Elliptic.L12dens]

/-- `orthSource 0 = 0`. -/
theorem orthSource_zero : Work.Elliptic.orthSource (0 : Fn) = 0 := by
  funext z θ
  simp [Work.Elliptic.orthSource, Work.Elliptic.Fstar]


end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.HkMemRadialSin =====
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
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-! ## The two gadgets

The proof of `HkMemRadialSin` needs two elementary facts:

* the radial iterate `radIter` of `OpenQAux` (the exact `D_z`-iterate of a function of `z`
  alone, appearing in the separated form `HkExp`) is the *same* operator as the one-variable
  `rDzIter` of `GbarSetup` (the one appearing in the hypotheses `hint`, `hcont`);
* the separated integrand `HkExp α k R z θ` is dominated, uniformly in `θ ∈ Iθ`, by the
  radial majorant `(1 + angKsum k)·w(z)²·Σ_{j≤k} (rDzIter j R z)²` — the same computation as
  `Cert.GbarSin.gbar_HkIntegrand_target_le`, with the angular constant `angK i` bounding
  `angA α i θ = (D_θ^i sin 2θ)² sin(2θ)^{-γ}` and `1` bounding `angZ θ = sin(2θ)^{2-η}`. -/





end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AlphaDzDthDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

set_option autoImplicit false



end Work.FTS.EllipticEst.Cores
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.ESV.HkMem_zero_sliceData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The `D_z`-iterates of a datum of the weak class are honest at level `0`.  The `j`-th
radial summand of the honest `ℋ²`-integrand is dominated by the whole integrand, and
continuity of the summand on the open quadrant (which is what the domination lemma needs)
comes from smoothness of `D_z^j` of the three fields of the class. -/
theorem HkMem_zero_sliceData (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (j : ℕ) (hj : j ≤ 2) :
    Work.Spaces.HkMem α 0 (Work.Spaces.DzIter j F) ∧
      Work.Spaces.HkMem α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ) ∧
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) := by
  -- smoothness of the datum and of its fields on the open quadrant
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mpr h.smooth
  obtain ⟨hSFj, hSΨj, hSGj, hSBj⟩ :=
    Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h j
  refine ⟨?_, ?_, ?_⟩
  · -- the source: the `j`-th radial summand of `HkIntegrand α 2 F`
    exact Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 j F
      hSFj.continuousOn h.memF hj
  · -- the radial second derivative: the same summand for `z²∂_z²Ψ`, transported along
    -- `z²∂_z²(D_z^jΨ) = D_z^j(z²∂_z²Ψ)` on the open quadrant
    have hG : Work.Spaces.HkMem α 0
        (Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 j _
        hSGj.continuousOn h.memA hj
    have hS2 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ) :=
      Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_zsq_mul ((hSΨ.DzIter j).pzIter 2)
    refine Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr hS2.continuousOn ?_ hG
    intro z θ hz hθ hlt
    have hE := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hSΨ j 0
      (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hz, hθ, hlt⟩)
    simpa only [Function.uncurry, Work.Spaces.mixed_zero_right] using hE
  · -- the angular second derivative: the same summand for `∂_θθΨ`, transported along
    -- `∂_θθ(D_z^jΨ) = D_z^j(∂_θθΨ)` on the open quadrant
    have hB : Work.Spaces.HkMem α 0
        (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 j _
        hSBj.continuousOn h.memB hj
    have hS3 : Work.FTS.EllipticEst.SmoothOpen
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl (hSΨ.DzIter j) 2
    refine Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr hS3.continuousOn ?_ hB
    intro z θ hz hθ hlt
    have hE := Work.EllipticEst.H2W.pthIter2_DzIter_comm hSΨ j
      (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hz, hθ, hlt⟩)
    simpa only [Function.uncurry] using hE

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.ESV.HkMem_zero_slices =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Helper A : `∂_θ^n` commutes with multiplication by the first variable -/

theorem pthIter_const_mul_fst (n : ℕ) (h : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter n (fun z θ => z * h z θ)
      = fun z θ => z * Work.Spaces.pthIter n h z θ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      funext z θ
      simp only [Work.Spaces.pth, deriv_const_mul_field]

/-! ## Helper B : Clairaut for `∂_z` against `∂_θ²` -/

theorem pz_pthIter_two_eqOn {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter 2 g)))
      (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.pz g)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h2 : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      ContDiffAt ℝ 2 (Function.uncurry g) p := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Work.FTS.EllipticEst.DzAmgm.contDiffAt_two_of_mem hg hz ⟨hθ0, hθ1⟩
  have h2' : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth g)) p := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Work.FTS.EllipticEst.DzAmgm.contDiffAt_two_of_mem (hg.pth) hz ⟨hθ0, hθ1⟩
  have hEqOn : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth g)))
      (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz g))) Work.FTS.EllipticEst.Q0 :=
    fun p hp => Work.Spaces.pz_pth_comm (h2 p hp)
  intro p hp
  have e2 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth g)) p.1 p.2
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth g)) p.1 p.2 :=
    Work.Spaces.pz_pth_comm (h2' p hp)
  have e1 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth g)) p.1 p.2
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz g)) p.1 p.2 :=
    Work.Spaces.pth_congr_of_isOpen (f := Work.Spaces.pz (Work.Spaces.pth g))
      (f' := Work.Spaces.pth (Work.Spaces.pz g)) Work.FTS.EllipticEst.isOpen_Q0 hEqOn hp
  show Work.Spaces.pz (Work.Spaces.pthIter 2 g) p.1 p.2
      = Work.Spaces.pthIter 2 (Work.Spaces.pz g) p.1 p.2
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact e2.trans e1

/-! ## Helper C : `∂_θ²` commutes with `D_z` -/

theorem pthIter_two_Dz_eqOn {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.Dz g)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pthIter 2 g)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  intro p hp
  have h1 : Work.Spaces.pthIter 2 (Work.Spaces.Dz g) p.1 p.2
      = p.1 * Work.Spaces.pthIter 2 (Work.Spaces.pz g) p.1 p.2 := by
    rw [show Work.Spaces.Dz g = fun z θ => z * Work.Spaces.pz g z θ from rfl,
      pthIter_const_mul_fst]
  have h2 : Work.Spaces.pz (Work.Spaces.pthIter 2 g) p.1 p.2
      = Work.Spaces.pthIter 2 (Work.Spaces.pz g) p.1 p.2 := pz_pthIter_two_eqOn hg hp
  show Work.Spaces.pthIter 2 (Work.Spaces.Dz g) p.1 p.2
      = Work.Spaces.Dz (Work.Spaces.pthIter 2 g) p.1 p.2
  rw [h1]
  simp only [Work.Spaces.Dz]
  rw [← h2]

/-! ## Helper D : the requested commutation of `∂_θ²` with `D_z^j` -/

theorem pthIter_two_DzIter_comm (f : ℝ → ℝ → ℝ) (j : ℕ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      have hstep := (pthIter_two_Dz_eqOn (hf.DzIter j)).trans
        (Work.FTS.EllipticEst.DzAmgm.Q0_Dz_congr ih)
      simpa only [Work.Spaces.DzIter_succ] using hstep

/-! ## Helper E : `bslOp α Ψ` is `C^∞` on the open quadrant for `Ψ` merely `C^∞` there -/

theorem smoothOpen_bslOp_of_smoothOpen (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) := by
  have hzsq : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z ^ 2) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
  have hz : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-(α ^ 2))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hzsq
          (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2)))
      (fun z θ _ _ _ => by ring)
  have hB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hz
          (Work.FTS.EllipticEst.SmoothOpen.pz hΨso)))
      (fun z θ _ _ _ => by ring)
  have htΨ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl htan hΨso
  have hC : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
            (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2))
          (Work.FTS.EllipticEst.SmoothOpen.pth htΨ))
        (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 hΨso))
      (fun z θ _ _ _ => by simp only [Work.Elliptic.Lzero])
  exact Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hA hB) hC)
    (fun z θ _ _ _ => by simp only [Work.Elliptic.bslOp_apply])

/-! ## Helper F : the source of the weak class is `C^∞` on the open quadrant -/

theorem SmoothOpen_F_weak (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen F := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  exact Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (smoothOpen_bslOp_of_smoothOpen α Ψ hΨso)
    (fun z θ hz hθ0 hθ1 => h.eq z hz θ hθ0 hθ1)

/-! ## The target lemma -/

theorem HkMem_zero_slices (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ j : ℕ, j ≤ 2 → Work.Spaces.HkMem α 0 (Work.Spaces.DzIter j F) ∧
      Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ) ∧
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) := by
  intro j hj
  have hFso : Work.FTS.EllipticEst.SmoothOpen F := SmoothOpen_F_weak α 2 F Ψ h
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hQso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_zsq_mul (hΨso.pzIter 2)
  refine ⟨?_, ?_, ?_⟩
  · exact Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 j F
      (hFso.DzIter j).continuousOn h.memF hj
  · refine Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr
      (g := Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) ?_ ?_ ?_
    · exact (Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_zsq_mul
        ((hΨso.DzIter j).pzIter 2)).continuousOn
    · intro z θ hz hθ0 hθ1
      have hE := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hΨso j 0
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)
      simpa only [Function.uncurry_apply_pair, Work.Spaces.mixed_zero_right] using hE
    · exact Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        (hQso.DzIter j).continuousOn h.memA hj
  · refine Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr
      (g := Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) ?_ ?_ ?_
    · exact (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl
        (hΨso.DzIter j) 2).continuousOn
    · intro z θ hz hθ0 hθ1
      exact pthIter_two_DzIter_comm Ψ j hΨso
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)
    · exact Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 j
        (Work.Spaces.pthIter 2 Ψ)
        ((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2).DzIter j).continuousOn
        h.memB hj

end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.ESV.aSliceHonest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## `∂_θ`-iterates of a function smooth on the open quadrant -/

/-- `∂_θ^i f` is again `C^∞` on the open quadrant when `f` is. -/
theorem smoothOpen_pthIter_H2W {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i f) := by
  induction i with
  | zero => simpa using hf
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-! ## Clairaut at the level of the iterated plain derivatives -/

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
          (smoothOpen_pthIter_H2W hg k) 2).contDiffAt
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

/-! ## The pointwise identity for the slice of `z²∂_z²Ψ` -/

/-- **The second angular derivative of the radial slice `z²∂_z²Ψ z ·`, in `Qop`-form.**
On the open quadrant it equals `z²∂_z²(∂_θ²Ψ)`: the factor `z²` is constant in `θ`, and the
plain `θ`- and `z`-derivatives commute (Clairaut). -/
theorem deriv_deriv_zsq_pzIter2_Qop {Ψ : ℝ → ℝ → ℝ} (hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hinner : ∀ t : ℝ,
      deriv (fun θ' : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t
        = z ^ 2 * deriv (fun θ' : ℝ => Work.Spaces.pzIter 2 Ψ z θ') t :=
    fun t => deriv_const_mul_field (z ^ 2)
  calc deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ
      = deriv (fun t => z ^ 2 * deriv (fun θ' => Work.Spaces.pzIter 2 Ψ z θ') t) θ := by
        congr 1 with t; exact hinner t
    _ = z ^ 2 * deriv (fun t => deriv (fun θ' => Work.Spaces.pzIter 2 Ψ z θ') t) θ :=
        deriv_const_mul_field (z ^ 2)
    _ = z ^ 2 * Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ := rfl
    _ = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
        rw [show Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ
            = Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
          from pthIter_pzIter_comm_Q0 hSΨ 2 2 hmem]

/-- **The second angular derivative of the radial slice `z²∂_z²Ψ z ·`, in `D_z`-form.**
`z²∂_z² = D_z² - D_z`, so the slice is the difference of the two radial summands of the
`ℋ²`-integrand of `∂_θ²Ψ`. -/
theorem deriv_deriv_zsq_pzIter2_eq {Ψ : ℝ → ℝ → ℝ} (hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ
      = Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
        - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ := by
  rw [deriv_deriv_zsq_pzIter2_Qop hSΨ hz hθ]
  exact Work.FTS.EllipticEst.DzAmgm.Qop_eq_Dz2_sub_Dz (smoothOpen_pthIter_H2W hSΨ 2) hz hθ

/-! ## Honesty of a slice from `ℋ⁰`-membership -/

/-- **An `ℋ⁰`-membership makes every angular slice η-weighted-square honest.**  If
`g ∈ ℋ⁰` then for every `z > 0` the slice `θ ↦ g z θ² sin(2θ)^{-η}` is integrable on `Iθ`:
the `ℋ⁰`-integrand is `(g z θ · w(z)/sin(2θ)^{η/2})²`, and for `z > 0` the factor `w(z)² ≠ 0`
can be divided out. -/
theorem integrable_slice_sq_sEta_of_HkMem {α : ℝ} {g : ℝ → ℝ → ℝ} {z : ℝ}
    (hz : 0 < z) (h : Work.Spaces.HkMem α 0 g) :
    MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hw : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun (h.1 z hzI)
      (fun θ hθ => Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_eq α g z θ) hIθ
  have h2 := h1.const_mul ((Work.Spaces.w z) ^ 2)⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun h2 (fun θ hθ => ?_) hIθ
  rw [Work.FTS.EllipticEst.sEta,
    Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ]
  field_simp

/-! ## The target -/

theorem aSliceHonest : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      ∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ =>
            (deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  intro α F Ψ hα hα4 h z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- at `z = 0` the slice is identically zero
    subst hz0
    have hzero : (fun θ : ℝ =>
        (deriv (fun t => deriv (fun θ' => (0 : ℝ) ^ 2 * Work.Spaces.pzIter 2 Ψ 0 θ') t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) = fun _ => (0 : ℝ) := by
      have hfun : (fun θ' : ℝ => (0 : ℝ) ^ 2 * Work.Spaces.pzIter 2 Ψ 0 θ')
          = fun _ => (0 : ℝ) := by
        funext t; ring
      funext θ
      rw [hfun]
      simp
    rw [hzero]
    exact integrableOn_zero
  · -- the `ℋ²`-membership of `∂_θ²Ψ` and its two radial summands
    have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mpr h.smooth
    have hSH : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
      smoothOpen_pthIter_H2W hSΨ 2
    have hb1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 1 (Work.Spaces.pthIter 2 Ψ)
        ((hSH.DzIter 1).continuousOn) h.memB (by norm_num)
    have hb2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 2 (Work.Spaces.pthIter 2 Ψ)
        ((hSH.DzIter 2).continuousOn) h.memB (by norm_num)
    -- the two-variable slice function is continuous on the open quadrant
    have hcontG : ContinuousOn
        (Function.uncurry (fun z θ =>
          deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have hbase : ContinuousOn
          (fun p : ℝ × ℝ =>
            p.1 ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
          Work.FTS.EllipticEst.Q0 :=
        (continuousOn_fst.pow 2).mul ((hSH.pzIter 2).continuousOn)
      refine hbase.congr ?_
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact deriv_deriv_zsq_pzIter2_Qop hSΨ hz ⟨hθ0, hθ1⟩
    -- honesty of the slice function, by domination with the two radial summands
    have hGfun : Work.Spaces.HkMem α 0
        (fun z θ => deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ) := by
      refine Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_of_majorant (α := α)
        (f := fun z θ =>
          deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ)
        (M := fun z θ =>
          2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
            + 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ)
        hcontG ?_ ?_ ?_
      · intro z hz
        exact ((hb2.1 z hz).const_mul 2).add ((hb1.1 z hz).const_mul 2)
      · have h' := (hb2.2.const_mul 2).add (hb1.2.const_mul 2)
        refine h'.congr ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        rw [Pi.add_apply, MeasureTheory.integral_add ((hb2.1 z hz).const_mul 2)
          ((hb1.1 z hz).const_mul 2), MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
      · intro z hz θ hθ
        have hMnn : 0 ≤ 2 * Work.Spaces.HkIntegrand α 0
              (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
            + 2 * Work.Spaces.HkIntegrand α 0
              (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ := by
          have h₁ := Work.Spaces.HkIntegrand_nonneg α 0
            (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
          have h₂ := Work.Spaces.HkIntegrand_nonneg α 0
            (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ
          linarith
        rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz_eq | hz_pos
        · -- `z = 0`
          subst hz_eq
          rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_z]
          exact hMnn
        · rcases eq_or_lt_of_le hθ.1 with hθ_eq | hθ_pos
          · -- `θ = 0`
            subst hθ_eq
            rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_theta_zero]
            exact hMnn
          · rcases eq_or_lt_of_le hθ.2 with hθ_eq | hθ_lt
            · -- `θ = π/2`
              subst hθ_eq
              rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_theta_pi]
              exact hMnn
            · -- interior: use the pointwise identity and AM–GM
              rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_eq,
                deriv_deriv_zsq_pzIter2_eq hSΨ hz_pos ⟨hθ_pos, hθ_lt⟩,
                Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_eq,
                Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_eq]
              set A := Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ with hA
              set B := Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ with hB
              set c := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hc
              nlinarith [sq_nonneg (A * c + B * c), sq_nonneg (A * c), sq_nonneg (B * c)]
    exact integrable_slice_sq_sEta_of_HkMem hzpos hGfun

end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Fstar_DzIter_two_F =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The level-`2` moment of the source vanishes almost everywhere** (the sharp conclusion
carried by `EllWeakPos α 2 F Ψ`).

The moment chain at `j = 1` (available because `1 + 1 ≤ 2`) together with the proved vanishing
of `F_*(D_zF)` says that `r ↦ F_*(D_z²F)(r)/r` has vanishing integral over every interval
`[s,z] ⊆ (0,∞)`; that function is locally integrable by `HkMem α 2 F`, so it vanishes a.e. -/
theorem Fstar_DzIter_two_F_ae (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0 := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
  have h1 : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0 :=
    fun z hz => Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two (α := α) (k := 2)
      (by norm_num) h z hz
  have hfr : (fun r : ℝ => Work.FTS.EllipticEst.Bmom F 2 r / r)
      = fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) r / r := by
    funext r
    rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
  -- the moment chain at `j = 1`: the primitive of `B_2/r` vanishes identically
  have hchain : ∀ s z : ℝ, 0 < s → 0 < z →
      ∫ r in s..z, Work.FTS.EllipticEst.Bmom F 2 r / r = 0 := by
    intro s z hs hz
    rw [hfr]
    rcases le_total s z with hsz | hzs
    · have hcr := Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α 2 F hF h.memF 1
        (by norm_num : 1 + 1 ≤ 2) hs hsz
      rw [← hcr, h1 z hz, h1 s hs, sub_zero]
    · have hcr := Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α 2 F hF h.memF 1
        (by norm_num : 1 + 1 ≤ 2) hz hzs
      have hcr' : ∫ r in z..s, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) r / r = 0 := by
        rw [← hcr]
        rw [h1 s hs, h1 z hz, sub_zero]
      rw [intervalIntegral.integral_symm, hcr', neg_zero]
  -- on each compact `[a,b] ⊆ (0,∞)`, the primitive of `B_2/r` is identically zero near every
  -- point of `[a,b]`, so the Lebesgue differentiation theorem forces `B_2 = 0` a.e. there
  have key : ∀ n : ℕ, ∀ᵐ x ∂(MeasureTheory.volume.restrict
      (Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2))),
      Work.FTS.EllipticEst.Bmom F 2 x = 0 := by
    intro n
    set a : ℝ := 1 / ((n : ℝ) + 1) with ha
    set b : ℝ := (n : ℝ) + 2 with hb
    have hpos : 0 < a := by rw [ha]; positivity
    have hlt : a < b := by
      have hbpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [ha, hb, div_lt_iff₀ hbpos]
      nlinarith
    have hle : a ≤ b := hlt.le
    have hInt : IntervalIntegrable (fun r : ℝ => Work.FTS.EllipticEst.Bmom F 2 r / r)
        volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
      exact Work.FTS.EllipticEst.integrableOn_Bmom_div α 2 hF h.memF 2 le_rfl a b hpos hlt
    have hldt := IntervalIntegrable.ae_hasDerivAt_integral hInt
    rw [Set.uIcc_of_le hle] at hldt
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hldt] with x hx
    intro hxmem
    have hxpos : 0 < x := lt_of_lt_of_le hpos hxmem.1
    have hder : HasDerivAt (fun y : ℝ => ∫ t in a..y, Work.FTS.EllipticEst.Bmom F 2 t / t)
        (Work.FTS.EllipticEst.Bmom F 2 x / x) x :=
      hx hxmem a ⟨le_rfl, hle⟩
    have hev : (fun y : ℝ => ∫ t in a..y, Work.FTS.EllipticEst.Bmom F 2 t / t)
        =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hxpos] with y hy
      exact hchain a y hpos hy
    have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ))
        (Work.FTS.EllipticEst.Bmom F 2 x / x) x := hev.hasDerivAt_iff.mp hder
    have hval : Work.FTS.EllipticEst.Bmom F 2 x / x = 0 :=
      (h0.unique (hasDerivAt_const x 0))
    rw [div_eq_zero_iff] at hval
    rcases hval with h' | h'
    · exact h'
    · exact absurd h' hxpos.ne'
  have keynull : ∀ n : ℕ, volume {x | x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2)
      ∧ ¬ (Work.FTS.EllipticEst.Bmom F 2 x = 0)} = 0 := by
    intro n
    have hh := key n
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff] at hh
    have hset : {x | x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2)
        ∧ ¬ (Work.FTS.EllipticEst.Bmom F 2 x = 0)}
        = {x | ¬ (x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) →
            Work.FTS.EllipticEst.Bmom F 2 x = 0)} := by
      ext x
      simp only [Set.mem_setOf_eq, not_imp]
    rw [hset]
    exact hh
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null keynull)
  intro x hx
  have hx' : x ∈ Set.Ioi 0 ∧ ¬ (Work.FTS.EllipticEst.Bmom F 2 x = 0) := by
    have hx'' : x ∈ Set.Ioi 0 ∧ ¬ (Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) x = 0) := by
      simpa only [Set.mem_setOf_eq, not_imp] using hx
    refine ⟨hx''.1, ?_⟩
    intro hb
    exact hx''.2 (by rwa [← Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter])
  obtain ⟨hx0, hxn⟩ := hx'
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ,
      1 / ((n : ℝ) + 1) ≤ x ∧ x ≤ (n : ℝ) + 2 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (max x (1 / x))
    refine ⟨n, ?_, ?_⟩
    · have hx1 : 1 / x ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
      have : 1 ≤ x * (n : ℝ) := by
        rw [div_le_iff₀ hx0] at hx1
        linarith
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith
    · have hxn' : x ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
      linarith
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  exact ⟨⟨hn1, hn2⟩, hxn⟩



end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RegQ

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Part 1 — the one-variable operator `D_ω u = ω · u'` -/


namespace SliceD

/-- The one-variable operator `D_ω u = ω · u'` (totalised derivative).  The two instances used
below are `ω = id` (the `z`-direction, `D_z` on slices) and `ω = sin (2·)` (the `θ`-direction,
`D_θ` on slices). -/
def Dop (ω u : ℝ → ℝ) : ℝ → ℝ := fun x => ω x * deriv u x

/-- Iterated `D_ω`. -/
def DopIter (ω : ℝ → ℝ) : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, u => u
  | n + 1, u => Dop ω (DopIter ω n u)

@[simp] theorem DopIter_zero (ω u : ℝ → ℝ) : DopIter ω 0 u = u := rfl

@[simp] theorem DopIter_succ (ω u : ℝ → ℝ) (n : ℕ) :
    DopIter ω (n + 1) u = Dop ω (DopIter ω n u) := rfl








end SliceD

/-! ## Part 2 — the two-variable calculus on the open quadrant -/

namespace Q2

/-- The open quadrant `(0,∞) × (0,π/2)`, the domain of the smoothness hypothesis. -/
abbrev Qd : Set (ℝ × ℝ) := Work.FTS.EllipticEst.Q0

theorem isOpen_Qd : IsOpen Qd := Work.FTS.EllipticEst.isOpen_Q0


/-- The coefficient of the `θ`-direction operator on `θ`-slices. -/
def wT : ℝ → ℝ := fun θ => Real.sin (2 * θ)



/-! ### Finite-order smoothness of the partial derivatives -/

/-- `∂_θ` drops one order of differentiability. -/
theorem contDiffOn_pth_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) (Function.uncurry G) U) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) U := by
  have hchain : ∀ p ∈ U, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) U := by
    have h' := h.fderivWithin (m := (n : WithTop ℕ∞)) hU.uniqueDiffOn (by simp)
    exact h'.congr (fun p hp => (fderivWithin_of_isOpen hU hp).symm)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) U := by
    simpa using hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  simpa only [Function.uncurry] using hchain p hp

/-- `∂_z` drops one order of differentiability. -/
theorem contDiffOn_pz_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) (Function.uncurry G) U) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) U := by
  have hchain : ∀ p ∈ U, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) U := by
    have h' := h.fderivWithin (m := (n : WithTop ℕ∞)) hU.uniqueDiffOn (by simp)
    exact h'.congr (fun p hp => (fderivWithin_of_isOpen hU hp).symm)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) U := by
    simpa using hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  simpa only [Function.uncurry] using hchain p hp

/-- `D_z = z ∂_z` drops one order of differentiability. -/
theorem contDiffOn_Dz_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) (Function.uncurry G) U) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) U := by
  have hfun : Function.uncurry (Work.Spaces.Dz G)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact (contDiffOn_fst.mul (contDiffOn_pz_fin hU h)).congr (fun p _ => rfl)

/-- `D_θ = sin 2θ · ∂_θ` drops one order of differentiability. -/
theorem contDiffOn_Dth_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) (Function.uncurry G) U) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth G)) U := by
  have hfun : Function.uncurry (Work.Spaces.Dth G)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) U :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn.of_le le_top
  exact (hsin.mul (contDiffOn_pth_fin hU h)).congr (fun p _ => rfl)

/-- `D_θ^i` drops `i` orders of differentiability. -/
theorem contDiffOn_DthIter_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry G) U) :
    ∀ i ≤ n, ContDiffOn ℝ (n - i : ℕ) (Function.uncurry (Work.Spaces.DthIter i G)) U := by
  intro i
  induction i with
  | zero => intro _; simpa using h
  | succ i ih =>
    intro hi
    have hi' : i ≤ n := by omega
    have h1 : ContDiffOn ℝ (n - i : ℕ) (Function.uncurry (Work.Spaces.DthIter i G)) U := ih hi'
    have h2 : ContDiffOn ℝ (n - i - 1 + 1 : ℕ)
        (Function.uncurry (Work.Spaces.DthIter i G)) U := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n - i)]; exact h1
    have h3 : ContDiffOn ℝ (n - i - 1 : ℕ)
        (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DthIter i G))) U :=
      contDiffOn_Dth_fin hU h2
    have heq : n - (i + 1) = n - i - 1 := by omega
    rw [heq, Work.Spaces.DthIter_succ]
    exact h3

/-- `D_z^j` drops `j` orders of differentiability. -/
theorem contDiffOn_DzIter_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry G) U) :
    ∀ j ≤ n, ContDiffOn ℝ (n - j : ℕ) (Function.uncurry (Work.Spaces.DzIter j G)) U := by
  intro j
  induction j with
  | zero => intro _; simpa using h
  | succ j ih =>
    intro hj
    have hj' : j ≤ n := by omega
    have h1 : ContDiffOn ℝ (n - j : ℕ) (Function.uncurry (Work.Spaces.DzIter j G)) U := ih hj'
    have h2 : ContDiffOn ℝ (n - j - 1 + 1 : ℕ)
        (Function.uncurry (Work.Spaces.DzIter j G)) U := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n - j)]; exact h1
    have h3 : ContDiffOn ℝ (n - j - 1 : ℕ)
        (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DzIter j G))) U :=
      contDiffOn_Dz_fin hU h2
    have heq : n - (j + 1) = n - j - 1 := by omega
    rw [heq, Work.Spaces.DzIter_succ]
    exact h3

/-! ### Slices -/

/-- The `z`-slice of a function smooth to finite order on a product of sets. -/
theorem contDiffOn_slice_z_fin {G : ℝ → ℝ → ℝ} {s t : Set ℝ} {n : ℕ}
    (hG : ContDiffOn ℝ n (Function.uncurry G) (s ×ˢ t)) {θ : ℝ} (hθ : θ ∈ t) :
    ContDiffOn ℝ n (fun z => G z θ) s :=
  (hG.comp (((contDiffOn_id : ContDiffOn ℝ n (fun z : ℝ => z) s)).prodMk
    (contDiffOn_const (c := θ))) (fun z hz => ⟨hz, hθ⟩)).congr (fun z _ => rfl)

/-- The `θ`-slice of a function smooth to finite order on a product of sets. -/
theorem contDiffOn_slice_θ_fin {G : ℝ → ℝ → ℝ} {s t : Set ℝ} {n : ℕ}
    (hG : ContDiffOn ℝ n (Function.uncurry G) (s ×ˢ t)) {z : ℝ} (hz : z ∈ s) :
    ContDiffOn ℝ n (fun θ => G z θ) t :=
  (hG.comp ((contDiffOn_const (c := z)).prodMk
    ((contDiffOn_id : ContDiffOn ℝ n (fun θ : ℝ => θ) t))) (fun θ hθ => ⟨hz, hθ⟩)).congr
    (fun θ _ => rfl)

/-! ### The `D`-iterates on slices -/


/-- The `D_θ`-iterates act on the `θ`-slices through the one-variable operator `SliceD.Dop wT`. -/
theorem DthIter_slice_eq (X : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i X z θ = SliceD.DopIter wT i (fun θ' => X z θ') θ := by
  induction i generalizing θ with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, SliceD.DopIter_succ]
      simp only [Work.Spaces.Dth, Work.Spaces.pth, SliceD.Dop, wT]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (Eventually.of_forall fun θ' => ih θ')

/-! ### The `θ`-identity at levels `≤ k-1` -/


/-! ### The slot inequality -/


end Q2

/-! ## Part 3 — the integrand estimate and the assembly -/

/-- Constants: `deriv` is homogeneous under multiplication by a constant, unconditionally
(no differentiability is needed: if `f` is not differentiable at `x` then neither is `c * f`
for `c ≠ 0`, and both sides are `0`). -/
theorem deriv_const_mul_uncond (c x : ℝ) (f : ℝ → ℝ) :
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

/-- **The linearity of the iterated operators.**  Every operator of the `ℋ^k`-calculus
(`D_z^i`, `D_θ^i`, `D_z^jD_θ^i`) commutes with multiplication by a constant, unconditionally. -/
theorem DzIter_const_mul (j : ℕ) (c : ℝ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => c * X z θ)
      = fun z θ => c * Work.Spaces.DzIter j X z θ := by
  induction j with
  | zero => funext z θ; simp
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih]
      funext z θ
      show z * deriv (fun z' => c * Work.Spaces.DzIter j X z' θ) z
        = c * (z * deriv (fun z' => Work.Spaces.DzIter j X z' θ) z)
      rw [deriv_const_mul_uncond]
      ring

theorem DthIter_const_mul (i : ℕ) (c : ℝ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * X z θ)
      = fun z θ => c * Work.Spaces.DthIter i X z θ := by
  induction i with
  | zero => funext z θ; simp
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => c * Work.Spaces.DthIter i X z θ') θ
        = c * (Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i X z θ') θ)
      rw [deriv_const_mul_uncond]
      ring

theorem mixed_const_mul (j i : ℕ) (c : ℝ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * X z θ)
      = fun z θ => c * Work.Spaces.mixed j i X z θ := by
  funext z θ
  simp only [Work.Spaces.mixed]
  rw [DthIter_const_mul i c X]
  exact congrFun (congrFun (DzIter_const_mul j c (Work.Spaces.DthIter i X)) z) θ




/-- At `sin (2θ) = 0` the weighted `ℋ^k`-integrand vanishes. -/
theorem HkIntegrand_zero_sin_fts (α : ℝ) (k : ℕ) (X : ℝ → ℝ → ℝ) {θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) (z : ℝ) :
    Work.Spaces.HkIntegrand α k X z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i X z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i X z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · have hm : Work.Spaces.mixed j i X z θ = 0 := by
        rw [Work.Spaces.mixed]
        exact Work.Spaces.DzIter_eq_zero_of_slice_zero
          (Work.Spaces.DthIter_eq_zero_of_sin hs i hc.1) j z
      rw [hm, zero_mul, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]





end Work.FTS.EllipticEst.RegQ
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.UopHk.removingL12Honest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `removingL12Honest`

Target (Elgindi, Annals **194** (2021), §'Elliptic Regularity Estimates', Theorem
`RemovingL12`, tex 1034) in the *interior* class `EllHypQ` of `Submission/Work/FTS/EllipticEst/RegQ.lean`:

  `α² |z²∂_zzΨ|_{ℋ^k} + |∂_θθ(Ψ - (1/(4α)) sin 2θ · L₁₂(F))|_{ℋ^k} ≤ C |F|_{ℋ^k}`.

## The route, and the structural facts about the class proved here

* `sliceTendsto_zero_left` / `sliceTendsto_zero_right`: **a datum of `RegQ α k f` (i.e. of
  `BdryTraces`) has vanishing slice limits at both angular endpoints, for `α > 0`.**  This is
  the structural difference between the interior class `RegQ` and the trace-free classes
  (`EllHypT`, `TT.EllWeakPos`): `BdryTraces` demands
  `sin(2θ)^{1-γ} f(z,θ)² → 0` as `θ → 0⁺`, and `1 - γ = -α/10 < 0` makes the prefactor
  `sin(2θ)^{1-γ} ≥ 1` near the endpoint, so `f(z,θ)² ≤ sin(2θ)^{1-γ} f(z,θ)² → 0`.
  Equivalently the `θ = 0` **limit** of every slice vanishes (the counterexample of
  `Submission/Work/FTS/EllipticEst/Cores/honestFstarFacts.lean` — which refutes the corresponding
  smoothness statement for the trace-free class `EllHypT` — therefore does *not* lie in
  `EllHypQ`).

* `mixed_tendsto_zero_left`: the same for every mixed derivative `D_z^bD_θ^a f` for which the
  class carries the traces (`RegQ α k (mixed b a f)`).

These are the boundary inputs the straightening `Ψ ↦ Ψ + Gsing α F · sin 2θ` needs in order to
upgrade a datum of `EllHypQ` to one of the weak class `TT.EllWeakPos` (where the a-priori
`ℋ^k` estimate `prop:Hk` is stated).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.UopHk

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Vanishing of the slice limits at the angular endpoints -/




/-! ## The consequences for a datum of `EllHypQ` -/



end Work.FTS.EllipticEst.UopHk

namespace Work.FTS.EllipticEst.UopHk


end Work.FTS.EllipticEst.UopHk
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Uop_bound_reg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. Elementary closure facts -/

/-- `Work.FTS.LocData.SmoothQuad` (genuine `C^∞` on `z > -1`, `0 < θ < π/2`) restricts to
`SmoothOpen` (genuine `C^∞` on `z > 0`, `0 < θ < π/2`). -/
theorem smoothOpen_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad f) : SmoothOpen f := by
  refine h.mono ?_
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp (show (p.1, p.2) ∈ Q0 from hp)
  simp only [Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨by linarith, hθ0, hθ1⟩

/-- Differences of `SmoothOpen` functions are `SmoothOpen`. -/
theorem smoothOpen_sub' {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ - g z θ) := by
  rw [SmoothOpen] at hf hg ⊢
  have h : (Function.uncurry fun z θ => f z θ - g z θ)
      = (fun p : ℝ × ℝ => Function.uncurry f p) - (fun p : ℝ × ℝ => Function.uncurry g p) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact ContDiffOn.sub hf hg

/-- Scalar multiples of `SmoothOpen` functions are `SmoothOpen`. -/
theorem smoothOpen_const_mul' (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    SmoothOpen (fun z θ => c * f z θ) := by
  rw [SmoothOpen] at hf ⊢
  have h : (Function.uncurry fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact (contDiffOn_const (c := c) (s := Q0)).mul hf

/-- `Uop α f = -3f - α·D_zf` on the open quadrant, where `D_z = z ∂_z`. -/
theorem Uop_eq_neg_three_sub_Dz (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Uop α f = fun z θ => -3 * f z θ - α * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Uop, Work.Spaces.Dz]
  ring

/-- `SmoothOpen` of the `Uop`-expression for a `SmoothOpen` datum. -/
theorem smoothOpen_Uop {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    SmoothOpen (Uop α f) := by
  rw [Uop_eq_neg_three_sub_Dz]
  have h1 : SmoothOpen (fun z θ => -3 * f z θ) := smoothOpen_const_mul' (-3) hf
  have h2 : SmoothOpen (fun z θ => α * Work.Spaces.Dz f z θ) :=
    smoothOpen_const_mul' α hf.Dz
  exact smoothOpen_sub' h1 h2

/-- `SmoothQuad` of the `Uop`-expression. -/
theorem smoothQuad_Uop {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad f) : Work.FTS.LocData.SmoothQuad (Uop α f) := by
  rw [Uop_eq_neg_three_sub_Dz]
  refine Work.FTS.LocData.smoothQuad_sub ?_ ?_
  · exact Work.FTS.LocData.smoothQuad_const_mul (-3) h
  · have h1 : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz f) := by
      simpa using Work.FTS.LocData.SmoothQuad.DzIter h 1
    exact Work.FTS.LocData.smoothQuad_const_mul α h1


/-! ## 1. The four analytic inputs (RegQ restatements of the `EllHyp` chain) -/





/-! ## 2. The assembly -/


/-! ## 3. The four analytic inputs, and the target -/






end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ZTracesAux.slot_sin_le_HkIntegrand_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ZTracesAux

theorem slot_sin_le_HkIntegrand_gen {α : ℝ} {f : ℝ → ℝ → ℝ} {m : ℕ}
    (b a : ℕ) (hab : a + 1 + b ≤ m) (s : ℝ) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
      * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) ≤ Work.Spaces.HkIntegrand α m f s σ := by
  -- `sin(2σ) > 0` on the open angular interval.
  have hS : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  -- The `(i,j) = (a+1,b)` slot of the mixed sum of `HkIntegrand` dominates.
  have hbase : (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.Wt α s σ) ^ 2
      ≤ Work.Spaces.HkIntegrand α m f s σ :=
    Work.Spaces.sq_le_HkIntegrand_mixed α m f s σ (a + 1) b (by omega) hab
  -- `(sin(2σ)^{-γ/2})² = sin(2σ)^{-γ}`.
  have hP : (Real.sin (2 * σ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = Real.sin (2 * σ) ^ (-(Work.Spaces.gam α)) := by
    rw [sq, ← Real.rpow_add hS]
    congr 1
    ring
  -- The left-hand side is exactly that slot.
  have hkey : (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.Wt α s σ) ^ 2 := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta]
    simp only [mul_pow]
    rw [hP]
    ring
  rw [hkey]
  exact hbase

end Work.FTS.EpsEngine.ZTracesAux
end
-- ===== merged: Submission.Work.FTS.GalBasis.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn galFun)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

/-! ## The test-function class -/

/-- `f` is supported in the box `[a,b] × [δ, π/2-δ]` (it vanishes off the closed box). -/
def SuppIn (f : Fn) (a b δ : ℝ) : Prop :=
  ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → f z θ = 0



theorem SuppIn.mono {f : Fn} {a b a' b' δ δ' : ℝ} (h : SuppIn f a b δ)
    (ha : a' ≤ a) (hb : b ≤ b') (hδ : δ' ≤ δ) (hδ' : π / 2 - δ ≤ π / 2 - δ') :
    SuppIn f a' b' δ' := by
  intro z θ hz
  refine h z θ ?_
  rcases hz with hz | hz
  · exact Or.inl fun hc => hz ⟨le_trans ha hc.1, le_trans hc.2 hb⟩
  · exact Or.inr fun hc => hz ⟨le_trans hδ hc.1, le_trans hc.2 hδ'⟩

/-- The compactly supported smooth class: `g` is `C^m` on the open box `(a,b) × (δ, π/2-δ)`
and supported in a strictly smaller box.  This is the class produced by the cutoffs of
`Cutoff.lean` and consumed by the approximation lemma of `Approx.lean`. -/
def CcOn (m : ℕ) (g : Fn) : Prop :=
  ∃ a b δ : ℝ, 0 < a ∧ a < b ∧ 0 < δ ∧ δ < π / 2 ∧
    ContDiffOn ℝ m (Function.uncurry g) (Set.Ioo a b ×ˢ Set.Ioo δ (π / 2 - δ)) ∧
    ∃ a' b' δ' : ℝ, a < a' ∧ a' < b' ∧ b' < b ∧ δ < δ' ∧ δ' < π / 2 - δ' ∧
      SuppIn g a' b' δ'

theorem CcOn.contDiffOn {m : ℕ} {g : Fn} (h : CcOn m g) :
    ∃ a b δ : ℝ, 0 < a ∧ a < b ∧ 0 < δ ∧ δ < π / 2 ∧
      ContDiffOn ℝ m (Function.uncurry g) (Set.Ioo a b ×ˢ Set.Ioo δ (π / 2 - δ)) := by
  obtain ⟨a, b, δ, ha, hab, hδ, hδ2, hd, -⟩ := h
  exact ⟨a, b, δ, ha, hab, hδ, hδ2, hd⟩

theorem CcOn.supp {m : ℕ} {g : Fn} (h : CcOn m g) :
    ∃ a' b' δ' : ℝ, 0 < a' ∧ a' < b' ∧ 0 < δ' ∧ δ' < π / 2 ∧ SuppIn g a' b' δ' := by
  obtain ⟨a, b, δ, ha, hab, hδ, hδ2, -, a', b', δ', haa, hab', hbb, hδδ, hδδ2, hs⟩ := h
  exact ⟨a', b', δ', lt_trans ha haa, hab', lt_trans hδ hδδ,
    by linarith [hδ, hδδ, hδδ2], hs⟩

/-- **The test functions of the Galerkin basis**: globally `C^∞` (order `(⊤ : ℕ∞)`, the honest
`C^∞` order, *not* the analytic order `⊤ : ℕ∞ω`) and supported strictly inside a box
`[a,b] × [δ, π/2-δ]` with `0 < a < b`, `0 < δ < π/2`. -/
def Ccφ (f : Fn) : Prop :=
  ∃ a b δ : ℝ, 0 < a ∧ a < b ∧ 0 < δ ∧ δ < π / 2 ∧
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f) ∧
    ∃ a' b' δ' : ℝ, a < a' ∧ a' < b' ∧ b' < b ∧ δ < δ' ∧ δ' < π / 2 - δ' ∧
      SuppIn f a' b' δ'

theorem Ccφ.contDiff {f : Fn} (h : Ccφ f) : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f) := by
  obtain ⟨-, -, -, -, -, -, -, hd, -⟩ := h; exact hd

theorem Ccφ.supp {f : Fn} (h : Ccφ f) :
    ∃ a b δ : ℝ, 0 < a ∧ a < b ∧ 0 < δ ∧ δ < π / 2 ∧ SuppIn f a b δ := by
  obtain ⟨a, b, δ, ha, hab, hδ, hδ2, -, a', b', δ', haa, hab', hbb, hδδ, hδδ2, hs⟩ := h
  exact ⟨a', b', δ', lt_trans ha haa, hab', lt_trans hδ hδδ,
    by linarith [hδ, hδδ, hδδ2], hs⟩




/-- The test functions with vanishing `L₁₂`-zero-mode: the class in which the basis elements
(and hence all their finite combinations) live. -/
def Coreφ (f : Fn) : Prop := Ccφ f ∧ Work.Construction.L12 f 0 = 0

theorem Coreφ.cc {f : Fn} (h : Coreφ f) : Ccφ f := h.1
theorem Coreφ.l12 {f : Fn} (h : Coreφ f) : Work.Construction.L12 f 0 = 0 := h.2

/-! ## The explicit countable family of test functions

The family is indexed by seven natural numbers, decoded from a single one by `Nat.pair`.
Each element is a monomial `z^p θ^q` times the product of four smooth *steps* — two in `z`
and two in `θ` — of common mesh `1/(n+1)`; the support is the rational box
`[m₁/(n+1), m₂/(n+1)] × [m₃/(n+1), m₄/(n+1)]`. -/

/-- The smooth *step* of mesh `1/(n+1)` starting at `m/(n+1)`: `0` for `t ≤ m/(n+1)`,
`1` for `t ≥ (m+1)/(n+1)`. -/
def stp (n m : ℕ) (t : ℝ) : ℝ := Real.smoothTransition (((n : ℝ) + 1) * t - (m : ℝ))

/-- The reversed smooth *step*: `1` for `t ≤ (m-1)/(n+1)`, `0` for `t ≥ m/(n+1)`. -/
def ustp (n m : ℕ) (t : ℝ) : ℝ := Real.smoothTransition ((m : ℝ) - ((n : ℝ) + 1) * t)






/-- The `z`-factor of a family element. -/
def famZ (n m₁ m₂ : ℕ) : ℝ → ℝ := fun z => stp n m₁ z * ustp n m₂ z

/-- The `θ`-factor of a family element. -/
def famTh (n m₃ m₄ : ℕ) : ℝ → ℝ := fun θ => stp n m₃ θ * ustp n m₄ θ

/-- The raw family element: a monomial times a product of four steps. -/
def famRaw (p q n m₁ m₂ m₃ m₄ : ℕ) : Fn :=
  fun z θ => z ^ p * θ ^ q * (famZ n m₁ m₂ z * famTh n m₃ m₄ θ)

















/-- **The designated far bump** `Gfar`: the family element with `p = q = 0` and `n = 3` on the
box `[40/4, 80/4] × [1/4, 5/4] = [10,20] × [0.25,1.25]` (inside the quadrant, and with `z`-box
disjoint from the boxes `[1/3,2/3]` used in the independence argument of `GramSchmidt.lean`).
It is used to adjust the zero mode `L₁₂(·)(0)`. -/
def Gfar : Fn := famRaw 0 0 3 40 80 1 5

/-- The zero mode of the far bump, `c₀ = L₁₂(Gfar)(0)`.  It is positive (`c0_pos`), which is
what makes the adjustment `testFam` well behaved. -/
def c0 : ℝ := Work.Construction.L12 Gfar 0













/-! ## The density statements of the design -/


/-- The `ℋ⁴`-density of the span of a sequence in an abstract class `K`, in the shape used by
the assembly: every element of `K` is the `ℋ⁴`-limit of finite combinations. -/
def DenseIn (α : ℝ) (K : Fn → Prop) (φ : ℕ → Fn) : Prop :=
  ∀ f : Fn, K f → ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (c : Fin n → ℝ), Work.Spaces.HkNorm α 4 (fun z θ => f z θ - galFun φ c z θ) < ε

theorem DenseIn.mono {α : ℝ} {K K' : Fn → Prop} {φ : ℕ → Fn} (h : DenseIn α K φ)
    (hKK' : ∀ f, K' f → K f) : DenseIn α K' φ :=
  fun f hf => h f (hKK' f hf)

end Work.FTS.GalBasis
end
end
-- ===== merged: Submission.Work.FTS.Galerkin.Inhabit.dataAdm_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Inhabit

/-! ## Elementary facts about the identically zero profile

Every operator occurring in `Work.Spaces.HkIntegrand`, `Work.Spaces.DecayInZ`,
`Work.Spaces.DecayMixed` and in the `L₁₂`-clause of `Work.Coercivity.HkAdm` is built from
`∂_z`, `∂_θ` and multiplications by functions of the variables alone, hence maps the zero
profile to itself; consequently all the required integrands vanish identically, all the
required iterated derivatives are the zero function (whose integrals along `z → ∞` tend to
`0` trivially), and `L₁₂(0) = 0`.  The helpers below record this, and the target theorem is
then immediate. -/





















end Work.FTS.Galerkin.Inhabit
end
-- ===== merged: Submission.Work.FTS.GalerkinFix.Equicont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalerkinFix

open Work.FTS.Galerkin (Slab box mem_box profileFam IsGalFam)

set_option autoImplicit false

/-! ## Coordinate bounds against the product metric on `ℝ × ℝ × ℝ` -/







/-! ## The two one-directional moduli give the joint modulus on every box -/


/-! ## A modulus on every box gives a modulus on every compact subset of the slab -/


/-! ## Pointwise bounds on the fake-time derivative give `EquicontTau` -/


end Work.FTS.GalerkinFix
end
end
-- ===== merged: Submission.Work.FTS.H2.HQ.DthDzIterComm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.H2.HQ

/-! ## The commutation identity on the open strip

`Work.FTS.LocData.SmoothQuad f` is, by definition, smoothness of `Function.uncurry f` in the
*genuine* smooth order `Work.Stability.smoothOrder` on the open strip
`Work.Spaces.quadU = (-1,∞) × (0,π/2)`.  Both curvilinear derivatives are local, so the
induction of `Work.Spaces.Dth_DzIter_comm_eqOn` goes through verbatim with `nbhU` replaced by
`quadU`: at each step Clairaut (`Work.Spaces.Dz_Dth_comm`, which only asks for `C²` at the
point) moves the outer `D_z` past the `D_θ`, and the two `z`-slices are then compared by the
induction hypothesis through `Work.Spaces.pz_congr_of_isOpen`. -/

/-- **`D_θ` commutes with every iterate of `D_z` on the open strip `quadU = (-1,∞) × (0,π/2)`.**

For `g` of class `C^∞` (`Work.Stability.smoothOrder`) on `quadU` and every `b : ℕ`, the
functions `D_θ (D_z^b g)` and `D_z^b (D_θ g)` agree on `quadU`.  The induction hypothesis is
used through the congruence lemma `Work.Spaces.pz_congr_of_isOpen`, which is available because
`quadU` is open. -/
theorem Dth_DzIter_comm_quadU {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Work.Spaces.quadU)
    (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b g)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth g))) Work.Spaces.quadU := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      intro y hy
      -- `D_z^b g` is `C^∞` (hence `C²`) on the open strip, so Clairaut applies at `y`.
      have hG : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DzIter b g)) Work.Spaces.quadU :=
        Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hg b
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter b g)) y :=
        (hG.contDiffAt (Work.Spaces.isOpen_quadU.mem_nhds hy)).of_le
          (by simp [Work.Stability.smoothOrder])
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DzIter b g) hcd
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth g)) y.1 y.2
      rw [← hcomm]
      -- The two `z`-slices agree on the open set `quadU` by the induction hypothesis,
      -- so their derivatives at `y` agree.
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b g)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth g)) y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen Work.Spaces.isOpen_quadU ih hy]

/-- **`D_θ` commutes past every iterate of `D_z` in the interior class `SmoothQuad`.**

`Work.Spaces.Dth_DzIter_comm_eqOn` (proved) is the same statement for
`Work.Spaces.SmoothNbhd` functions (analyticity on a neighbourhood of the closed quadrant),
which is false for the cut-off `χ`, for `F_*` and for the stream functions.  Here `f` is
`SmoothQuad` (genuine `C^∞` on the open strip `(-1,∞) × (0,π/2)`) and the identity

  `D_θ (D_z^j f) = D_z^j (D_θ f) =: mixed j 1 f`

is claimed at the points `z ∈ Iz`, `0 < θ < π/2` of the domain.

Route: copy the proof of `Work.Spaces.Dth_DzIter_comm_eqOn` (`Submission/Work/Spaces/mixed_comm.lean`)
together with its ingredient `Work.Spaces.Dz_Dth_comm_eqOn`, replacing `nbhU` by
`Work.Spaces.quadU` and the class `SmoothNbhd` by `SmoothQuad`, and using
`Work.Spaces.Dz_Dth_comm` (Clairaut for the two curvilinear derivatives, `C²` at the point),
with `ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter b f)) (z,θ)` obtained from
`Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hf b` and
`Work.Spaces.isOpen_quadU.mem_nhds`, together with the congr lemmas
`Work.Spaces.pz_congr_of_isOpen`/`Work.Spaces.pth_congr_of_isOpen` (proved for an arbitrary
open set) in the induction step.  Note the definitional identities
`Work.Spaces.mixed j 1 f = Work.Spaces.DzIter j (Work.Spaces.Dth f)`.
`Submission/Work/FTS/H2/LinfQ.lean` contains a draft of this proof
(`DzDthIterCommOn_quad`, `DzIter_DthIter_comm_quad`, `Dth_mixed_quad`); note that that file
does not compile, so do not import it — write your own. -/
theorem DthDzIterComm (j : ℕ) (f : ℝ → ℝ → ℝ) (hf : Work.FTS.LocData.SmoothQuad f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.Dth (Work.Spaces.DzIter j f) z θ = Work.Spaces.mixed j 1 f z θ := by
  -- `SmoothQuad f` *is* the hypothesis of the open-strip lemma, since
  -- `Work.Spaces.quadU = (-1,∞) × (0,π/2)` is exactly the strip in `SmoothQuad`, and
  -- `Work.Spaces.Iz = [0,∞) ⊆ (-1,∞)`.
  intro z hz θ hθ
  have hz' : (-1 : ℝ) < z := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    linarith
  have hy : (z, θ) ∈ Work.Spaces.quadU := ⟨hz', hθ⟩
  have h := Dth_DzIter_comm_quadU (g := f) hf j hy
  simpa [Function.uncurry, Work.Spaces.mixed, Work.Spaces.DthIter] using h

end Work.FTS.H2.HQ
end
-- ===== merged: Submission.Work.FTS.H2.HQ.ZsummandQDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.HQ

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-! ## The auxiliary data of the `Z`-summand

For the Leibniz expansion `D_z^i (f·g) = ∑_{b≤i} C(i,b) D_z^b f · D_z^{i-b} g` we keep, for
each `b ≤ i`, the factor with index `> 2` (in `L²`, with the light weight `w/sin(2θ)^{η/2}`)
and bound the other factor pointwise by `PwBd` (`b ≤ 2`: the factor is `D_z^b f`, bounded by
`Cf`; `b > 2`: the factor is `D_z^{i-b} g` with `i - b ≤ 2`, bounded by `Cg`). -/

/-- The square of the `L^∞`-bound of the factor kept by the pointwise estimate:
`Cf/(γ-1)·|f|²_{ℋ⁴}` when `b ≤ 2` (the factor `D_z^b f` is bounded by it) and
`Cg/(γ-1)·|g|²_{ℋ⁴}` otherwise. -/
def zsGamQ (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (b : ℕ) : ℝ :=
  if b ≤ 2 then (Cf / (gam α - 1)) * HkSq α 4 f else (Cg / (gam α - 1)) * HkSq α 4 g

/-- The function whose weighted `D_z`-iterate is kept in the `L²`-norm. -/
def zsFunQ (f g : ℝ → ℝ → ℝ) (b : ℕ) : ℝ → ℝ → ℝ := if b ≤ 2 then g else f

/-- The order of the weighted `D_z`-iterate kept in the `L²`-norm. -/
def zsIdxQ (i b : ℕ) : ℕ := if b ≤ 2 then i - b else b

/-- The summand of the majorant: the absolute value of the retained weighted derivative. -/
def zsFbQ (f g : ℝ → ℝ → ℝ) (i b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => |DzIter (zsIdxQ i b) (zsFunQ f g b) z θ
    * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|

/-- The coefficient of the summand `zsFbQ f g i b` in the majorant. -/
def zsAAQ (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i b : ℕ) : ℝ :=
  |(i.choose b : ℝ)| * Real.sqrt (zsGamQ α f g Cf Cg b)

/-- The majorant: the value of the pointwise estimate for the Leibniz expansion. -/
def zsVQ (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑ b ∈ Finset.range (i + 1), zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ

/-! ## Definitional unfolding lemmas -/

theorem zsGamQ_apply (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (b : ℕ) :
    zsGamQ α f g Cf Cg b
      = if b ≤ 2 then (Cf / (gam α - 1)) * HkSq α 4 f
        else (Cg / (gam α - 1)) * HkSq α 4 g := rfl

theorem zsFunQ_apply (f g : ℝ → ℝ → ℝ) (b : ℕ) :
    zsFunQ f g b = if b ≤ 2 then g else f := rfl

theorem zsIdxQ_apply (i b : ℕ) : zsIdxQ i b = if b ≤ 2 then i - b else b := rfl

theorem zsFbQ_apply (f g : ℝ → ℝ → ℝ) (i b : ℕ) (z θ : ℝ) :
    zsFbQ f g i b z θ = |DzIter (zsIdxQ i b) (zsFunQ f g b) z θ
      * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := rfl

theorem zsAAQ_apply (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i b : ℕ) :
    zsAAQ α f g Cf Cg i b = |(i.choose b : ℝ)| * Real.sqrt (zsGamQ α f g Cf Cg b) := rfl

theorem zsVQ_apply (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i : ℕ) (z θ : ℝ) :
    zsVQ α f g Cf Cg i z θ
      = ∑ b ∈ Finset.range (i + 1), zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ := rfl

/-! ## Elementary properties -/

theorem zsGamQ_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (b : ℕ) (hb2 : b ≤ 2) :
    zsGamQ α f g Cf Cg b = (Cf / (gam α - 1)) * HkSq α 4 f := by
  rw [zsGamQ_apply]; exact if_pos hb2

theorem zsGamQ_eq' (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (b : ℕ) (hb2 : ¬ b ≤ 2) :
    zsGamQ α f g Cf Cg b = (Cg / (gam α - 1)) * HkSq α 4 g := by
  rw [zsGamQ_apply]; exact if_neg hb2

theorem zsFunQ_eq (f g : ℝ → ℝ → ℝ) (b : ℕ) (hb2 : b ≤ 2) : zsFunQ f g b = g := by
  rw [zsFunQ_apply]; exact if_pos hb2

theorem zsFunQ_eq' (f g : ℝ → ℝ → ℝ) (b : ℕ) (hb2 : ¬ b ≤ 2) : zsFunQ f g b = f := by
  rw [zsFunQ_apply]; exact if_neg hb2

theorem zsIdxQ_eq (i b : ℕ) (hb2 : b ≤ 2) : zsIdxQ i b = i - b := by
  rw [zsIdxQ_apply]; exact if_pos hb2

theorem zsIdxQ_eq' (i b : ℕ) (hb2 : ¬ b ≤ 2) : zsIdxQ i b = b := by
  rw [zsIdxQ_apply]; exact if_neg hb2

theorem zsFbQ_eq (f g : ℝ → ℝ → ℝ) (i b : ℕ) (hb2 : b ≤ 2) :
    zsFbQ f g i b = fun z θ => |DzIter (i - b) g z θ
      * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
  funext z θ
  simp only [zsFbQ_apply, zsIdxQ_eq i b hb2, zsFunQ_eq f g b hb2]

theorem zsFbQ_eq' (f g : ℝ → ℝ → ℝ) (i b : ℕ) (hb2 : ¬ b ≤ 2) :
    zsFbQ f g i b = fun z θ => |DzIter b f z θ
      * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
  funext z θ
  simp only [zsFbQ_apply, zsIdxQ_eq' i b hb2, zsFunQ_eq' f g b hb2]

theorem zsAAQ_mul_zsFbQ_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i b : ℕ) (z θ : ℝ)
    (hb2 : b ≤ 2) :
    zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ
      = |(i.choose b : ℝ)| * Real.sqrt ((Cf / (gam α - 1)) * HkSq α 4 f)
        * |DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
  simp only [zsAAQ_apply, zsGamQ_eq α f g Cf Cg b hb2, zsFbQ_apply, zsIdxQ_eq i b hb2,
    zsFunQ_eq f g b hb2]

theorem zsAAQ_mul_zsFbQ_eq' (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i b : ℕ) (z θ : ℝ)
    (hb2 : ¬ b ≤ 2) :
    zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ
      = |(i.choose b : ℝ)| * Real.sqrt ((Cg / (gam α - 1)) * HkSq α 4 g)
        * |DzIter b f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
  simp only [zsAAQ_apply, zsGamQ_eq' α f g Cf Cg b hb2, zsFbQ_apply, zsIdxQ_eq' i b hb2,
    zsFunQ_eq' f g b hb2]

theorem zsGamQ_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (hγ : 0 < gam α - 1)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (b : ℕ) : 0 ≤ zsGamQ α f g Cf Cg b := by
  rw [zsGamQ_apply]
  split_ifs with h
  · exact mul_nonneg (div_nonneg hCf hγ.le) (HkSq_nonneg α 4 f)
  · exact mul_nonneg (div_nonneg hCg hγ.le) (HkSq_nonneg α 4 g)

theorem zsAAQ_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i b : ℕ) :
    0 ≤ zsAAQ α f g Cf Cg i b := by
  rw [zsAAQ_apply]
  exact mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

theorem zsFbQ_nonneg (f g : ℝ → ℝ → ℝ) (i b : ℕ) (z θ : ℝ) :
    0 ≤ zsFbQ f g i b z θ := by
  rw [zsFbQ_apply]
  exact abs_nonneg _

theorem zsVQ_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i : ℕ) (z θ : ℝ) :
    0 ≤ zsVQ α f g Cf Cg i z θ := by
  rw [zsVQ_apply]
  exact Finset.sum_nonneg fun b _ => mul_nonneg (zsAAQ_nonneg α f g Cf Cg i b)
    (zsFbQ_nonneg f g i b z θ)

/-- The `γ - 1 = α/10` of the paper is positive for `α > 0`. -/
theorem gam_sub_one_pos {α : ℝ} (hα : 0 < α) : 0 < gam α - 1 := by
  rw [gam_sub_one]; linarith

/-- The light weight vanishes on the two degenerate lines of the quadrant: at `z = 0` and
where `sin(2θ) = 0`. -/
theorem light_eq_zero_of_sin {z θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    w z / (Real.sin (2 * θ)) ^ (eta / 2) = 0 := by
  rw [h, Real.zero_rpow (by norm_num [eta]), div_zero]

/-- The light weight vanishes at `z = 0`. -/
theorem light_eq_zero_of_z {θ : ℝ} : w 0 / (Real.sin (2 * θ)) ^ (eta / 2) = 0 := by
  simp [w]

end Work.FTS.H2.HQ
end
end
-- ===== merged: Submission.Work.FTS.H2.PhiStarE5.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.PhiStarE5

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0 smoothOpen_of_forall)

set_option autoImplicit false
noncomputable section

/-! ## 1. `SmoothOpen` bookkeeping -/

/-- `SmoothOpen` is closed under pointwise subtraction. -/
theorem smoothOpen_sub {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ - g z θ) := by
  have hfun : Function.uncurry (fun z θ => f z θ - g z θ)
      = Function.uncurry f - Function.uncurry g := by
    funext p; rfl
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ - g z θ)) Q0
  rw [hfun]
  exact ContDiffOn.sub hf hg

/-- `SmoothOpen` is closed under pointwise multiplication. -/
theorem smoothOpen_mul {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ * g z θ) := by
  have hfun : Function.uncurry (fun z θ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := by
    funext p; rfl
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ * g z θ)) Q0
  rw [hfun]
  exact ContDiffOn.mul hf hg

/-- A radial function is `SmoothOpen`. -/
theorem smoothOpen_radial {r : ℝ → ℝ} (hr : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0)) :
    SmoothOpen (fun z _ => r z) := by
  refine smoothOpen_of_forall (fun n => ?_)
  exact (hr n).comp contDiffOn_fst (fun p hp => (mem_Q0.mp hp).1)


/-! ## 2. Smoothness of the two factors `φ` and `Γ` -/


/-- `Γ(θ) = (sinθcos²θ)^{α/3}` is `C^∞` on `(0,π/2)`. -/
theorem contDiffOn_Gam (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.Gam α θ) (Set.Ioo 0 (π / 2)) := by
  have hbase : ContDiffOn ℝ n (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo 0 (π / 2)) := by fun_prop
  have hpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have h := hbase.rpow_const_of_ne (p := α / 3) hpos
  refine h.congr (fun θ _ => ?_)
  simp only [Work.Spaces.Gam]

/-- `Γ̄ = Γ/c - (5/4) sin 2θ` is `C^∞` on `(0,π/2)`. -/
theorem contDiffOn_GamBar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    ContDiffOn ℝ n (fun θ : ℝ => Work.FTS.VocabO.GamBar α θ) (Set.Ioo 0 (π / 2)) := by
  have hc : (0 : ℝ) < Work.Spaces.c α := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have hGam := contDiffOn_Gam α n
  have hsin : ContDiffOn ℝ n (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) := by
    fun_prop
  have h1 : ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.Gam α θ / Work.Spaces.c α)
      (Set.Ioo 0 (π / 2)) :=
    ContDiffOn.div hGam contDiffOn_const (fun θ _ => ne_of_gt hc)
  have h2 : ContDiffOn ℝ n (fun θ : ℝ => (5 / 4 : ℝ) * Real.sin (2 * θ))
      (Set.Ioo 0 (π / 2)) :=
    ContDiffOn.mul contDiffOn_const hsin
  exact (ContDiffOn.sub h1 h2).congr (fun θ _ => by
    simp only [Work.FTS.VocabO.GamBar])
end

end Work.FTS.H2.PhiStarE5
end
-- ===== merged: Submission.Work.FTS.H2.Q.WtoWQ_f_bound_mixed =====
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

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.Spaces

/-! ## The Leibniz expansion of `D_θ^{b+1} f` on the open quadrant

`D_θ f = sin(2θ)·∂_θ f`, so the `b`-th iterate of `D_θ` on this product expands by the
binomial convolution of `D_θ`, and `D_θ^i (sin 2·) = sin(2θ)·γ_i(θ)` with `γ_i = sigCoeff i`.
This is the `SmoothQuad` counterpart of `Work.Elliptic.WtoW_f_expand` (which needs the
analyticity hypothesis `SmoothNbhd`, unavailable for the cut-off data of the route). -/




end Work.FTS.H2.Q
end
end
-- ===== merged: Submission.Work.FTS.LocDataExt.Majorant5 =====
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
set_option maxHeartbeats 1600000

/-! ## The generic separable majorant -/

/-- The angular jet bound `(D_θ^iΓ)² ≤ 10¹⁰·Γ²` on `Iθ`, for `i ≤ 5`, from
`DthIter_Gam_abs_le5`. -/
theorem hGam5 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {i : ℕ} (hi : i ≤ 5) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by
  have h := DthIter_Gam_abs_le5 i hi α hα hα1 hθ
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow] at h2
  have h10 : ((100000 : ℝ)) ^ 2 = (10 : ℝ) ^ 10 := by norm_num
  calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (100000 : ℝ) ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := h2
    _ = (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by rw [h10]

/-- **The generic pointwise majorant of the `ℋ^k`-integrand of a separable datum.**  If the
radial factor satisfies `((D_z^jρ)(z)·w z)² ≤ R/(1+z)²` for `j ≤ k` and the angular factor the
jet bound `(D_θ^iΓ)² ≤ Rθ·Γ²` for `i ≤ k`, then the `ℋ^k`-integrand of `ρ(z)·Γ(θ)` is bounded
by `((k+1) + (k+1)²Rθ)·R·angMaj α θ/(1+z)²`. -/
theorem HkIntegrand_sepGam_le (α : ℝ) (hα : 0 < α) (k : ℕ) {ρ : ℝ → ℝ} {R Rθ : ℝ}
    (hR : 0 ≤ R) (hRθ : 0 ≤ Rθ)
    (hB : ∀ j ≤ k, ∀ z ∈ Work.Spaces.Iz, ∀ θ' : ℝ,
      (Work.Spaces.DzIter j (fun z _ => ρ z) z θ' * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2)
    (hΓ : ∀ i ≤ k, ∀ θ' ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ') ^ 2)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
      ≤ (((k + 1 : ℕ) : ℝ) + (((k + 1) ^ 2 : ℕ) : ℝ) * Rθ) * R
          * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθ
  have hang0 : 0 ≤ Work.FTS.LocData.angMaj α θ := Work.FTS.LocData.angMaj_nonneg hθ
  have hden : 0 ≤ (1 + z) ^ 2 := by positivity
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  -- the `D_z`-block
  have hT1 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ∑ _i ∈ Finset.range (k + 1), (R / (1 + z) ^ 2 * Work.FTS.LocData.angMaj α θ) := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
    rw [congrFun (congrFun (DzIter_sepGam α ρ i) z) θ,
      Work.FTS.LocData.sep_sq1 (Work.Spaces.DzIter i (fun z _ => ρ z) z θ)
        (Work.Spaces.Gam α θ) (Work.Spaces.w z) (Real.sin (2 * θ)) (Work.Spaces.eta) hs0]
    have h1 := hB i hik z hz θ
    have h2 : (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ Work.FTS.LocData.angMaj α θ :=
      Work.FTS.LocData.Gam_sq_rpow_le_angMaj_eta α hθ
    have h3 : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    exact mul_le_mul h1 h2 h3 (by positivity)
  -- the mixed block
  have hT2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
          (R * Rθ * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) := by
    refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc]
      rw [Finset.mem_range] at hi hj
      rw [congrFun (congrFun (mixed_sepGam α ρ j i) z) θ, Work.Spaces.Wt, Work.Spaces.wTheta,
        Work.FTS.LocData.sep_sq2 (Work.Spaces.DzIter j (fun z _ => ρ z) z θ)
          (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) (Work.Spaces.w z)
          (Real.sin (2 * θ)) (Work.Spaces.gam α) hs0]
      have h1 := hB j (by omega) z hz θ
      have h2 := hΓ i (by omega) θ hθ
      have h3 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
      have h4 : 0 ≤ (Work.Spaces.DzIter j (fun z _ => ρ z) z θ * Work.Spaces.w z) ^ 2 :=
        sq_nonneg _
      calc (Work.Spaces.DzIter j (fun z _ => ρ z) z θ * Work.Spaces.w z) ^ 2
            * ((Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ (R / (1 + z) ^ 2) * (Rθ * (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^
              (-(Work.Spaces.gam α))) := by
            refine mul_le_mul h1 ?_ (mul_nonneg (sq_nonneg _) h3) (by positivity)
            exact mul_le_mul_of_nonneg_right h2 h3
        _ = R * Rθ * (((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
              / (1 + z) ^ 2 := by ring
        _ ≤ R * Rθ * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
            refine div_le_div_of_nonneg_right ?_ hden
            exact mul_le_mul_of_nonneg_left (Work.FTS.LocData.Gam_sq_rpow_le_angMaj_gam α hθ)
              (by positivity)
    · rw [if_neg hc]
      exact div_nonneg (mul_nonneg (mul_nonneg hR hRθ) hang0) hden
  -- putting the two blocks together
  have hHk : Work.Spaces.HkIntegrand α k (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
      = (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0) := rfl
  rw [hHk]
  refine le_trans (add_le_add hT1 hT2) ?_
  have h1 : (∑ _i ∈ Finset.range (k + 1), (R / (1 + z) ^ 2 * Work.FTS.LocData.angMaj α θ))
      = ((k + 1 : ℕ) : ℝ) * (R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have h2 : (∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
        (R * Rθ * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2))
      = (((k + 1) ^ 2 : ℕ) : ℝ) * (Rθ * (R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [h1, h2]
  have h3 : (0 : ℝ) ≤ R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 :=
    div_nonneg (mul_nonneg hR hang0) hden
  have h4 : ((k + 1 : ℕ) : ℝ) ≤ (((k + 1 : ℕ) : ℝ) + (((k + 1) ^ 2 : ℕ) : ℝ) * Rθ) := by
    have : (0 : ℝ) ≤ (((k + 1) ^ 2 : ℕ) : ℝ) * Rθ := by positivity
    linarith
  have h5 : ((k + 1 : ℕ) : ℝ) * (R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
        + (((k + 1) ^ 2 : ℕ) : ℝ) * (Rθ * (R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2))
      ≤ (((k + 1 : ℕ) : ℝ) + (((k + 1) ^ 2 : ℕ) : ℝ) * Rθ)
          * (R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) := by
    nlinarith [h3, hRθ, h4, Nat.cast_nonneg (α := ℝ) (k + 1),
      Nat.cast_nonneg (α := ℝ) ((k + 1) ^ 2)]
  refine le_trans h5 ?_
  rw [show (((k + 1 : ℕ) : ℝ) + (((k + 1) ^ 2 : ℕ) : ℝ) * Rθ)
        * (R * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
      = (((k + 1 : ℕ) : ℝ) + (((k + 1) ^ 2 : ℕ) : ℝ) * Rθ) * R
        * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 from by ring]

/-! ## The bump at order `5` -/




end Work.FTS.LocDataExt
end
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.MeridianDyn.Bridge.Pieces

/-! ## The angular slice of `K · f / s`

`Work.Spaces.K θ = 3 sin θ cos²θ` is bounded by `3` everywhere, and `sin(2θ)^{η/2} ≤ 1` while
`w s ≥ 1` for `s > 0`.  So on the angular interval `Iθ` the `i = 0` term of `HkIntegrand α 4 f`
dominates `(f s θ)²` (`Work.Spaces.sq_le_HkIntegrand_z`), which gives the square-integrability
of the slice; the slice itself is then `L¹` because `Iθ` has finite measure, and
`K θ · f s θ / s` is a bounded (`≤ 3/s`) multiple of it.

Only *interior* smoothness (`SmoothOpen`, i.e. `C^∞` on the open quadrant) is used, through the
a.e. strong measurability of the slice (`Work.Spaces.aesm_slice_of_continuousOn_Qd`); the two
endpoints `θ = 0, π/2` are null. -/

/-- `|K θ| ≤ 3` for every `θ`. -/
private theorem abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hcos : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg (sq_nonneg (Real.cos θ))]
  nlinarith [abs_nonneg (Real.sin θ)]

/-- `θ ↦ K θ` is continuous. -/
private theorem continuous_K : Continuous Work.Spaces.K := by
  have h : Work.Spaces.K = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 := by
    funext θ; rfl
  rw [h]
  exact (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)

/-- The angular slice `θ ↦ (f s θ)²` of an `HkMem α 4` datum with interior smoothness is
integrable on `Iθ` for `s > 0`.  This is `Work.FTS.H2.l12q_slice_sq_integrableOn` with the
hypothesis `SmoothQuad f` weakened to `SmoothOpen f`. -/
private theorem slice_sq_integrableOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ := by
  -- the squared slice is a.e. strongly measurable (continuity on the open quadrant)
  have hquad : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      hsm.continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := h1.pow 2
    simpa only [Function.uncurry] using h2
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f s θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) hquad hs
  -- domination by the `i = 0` term of `HkIntegrand`
  have hsI : s ∈ Work.Spaces.Iz := le_of_lt hs
  refine (hmem.1 s hsI).mono' haesm ?_
  -- the pointwise bound only fails on the two null endpoints
  have hcongr : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := π / 2)).symm
  rw [hcongr]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 (by have := Work.Spaces.eta_pos; linarith)
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs0 _
  have hw1 : 1 ≤ Work.Spaces.w s := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hs]
  have hkey : 1 ≤ Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div hspos]
    exact le_trans hsle hw1
  have hW2 : 1 ≤ (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    have h := mul_le_mul hkey hkey (zero_le_one) (le_trans zero_le_one hkey)
    simpa only [one_mul, pow_two] using h
  have hpt : (f s θ) ^ 2 ≤ (f s θ * (Work.Spaces.w s
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (f s θ) ^ 2 = (f s θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (f s θ) ^ 2
            * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)
      _ = (f s θ * (Work.Spaces.w s
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := (mul_pow _ _ 2).symm
  calc ‖(f s θ) ^ 2‖ = (f s θ) ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    _ ≤ (f s θ * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hpt
    _ = (Work.Spaces.DzIter 0 f s θ * (Work.Spaces.w s
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
    _ ≤ Work.Spaces.HkIntegrand α 4 f s θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ 0 (by norm_num)

/-- The slice `θ ↦ K θ · f s θ / s` is integrable on `Iθ` for `s > 0`. -/
theorem sliceK_integrableOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ := by
  intro s hs
  -- the slice square and its measurability
  have hsq := slice_sq_integrableOn hsm hmem hs
  have hfm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => f s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f) hsm.continuousOn hs
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.K θ / s) * f s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((continuous_K.div_const s).aestronglyMeasurable).mul hfm
  -- the integrable majorant `(3/(2s))·(f² + 1)`
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const
      (by rw [Work.Spaces.Iθ]; exact ne_of_lt measure_Icc_lt_top) (by simp)
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (3 / (2 * s)) * ((f s θ) ^ 2 + 1)) Work.Spaces.Iθ :=
    (hsq.add hconst).const_mul _
  -- the pointwise bound `|K θ|·|f s θ|/s ≤ (3/(2s))·(f² + 1)`
  have hbd : ∀ θ : ℝ, ‖(Work.Spaces.K θ / s) * f s θ‖
      ≤ (3 / (2 * s)) * ((f s θ) ^ 2 + 1) := by
    intro θ
    have hK := abs_K_le_three θ
    have key : 2 * |f s θ| ≤ (f s θ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|f s θ| - 1), sq_abs (f s θ)]
    have hc : 0 ≤ 3 / (2 * s) := div_nonneg (by norm_num) (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hs]
    calc |Work.Spaces.K θ| / s * |f s θ|
        ≤ 3 / s * |f s θ| :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hK (le_of_lt hs))
            (abs_nonneg _)
      _ = (3 / (2 * s)) * (2 * |f s θ|) := by field_simp
      _ ≤ (3 / (2 * s)) * ((f s θ) ^ 2 + 1) := mul_le_mul_of_nonneg_left key hc
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.K θ / s) * f s θ)
      Work.Spaces.Iθ := by
    refine hmaj.mono' haesm ?_
    exact Filter.Eventually.of_forall hbd
  -- reassociate `K θ / s * f s θ` into `K θ * f s θ / s`
  refine hint.congr_fun (fun θ _ => ?_) ?_
  · ring
  · rw [Work.Spaces.Iθ]; exact measurableSet_Icc

end Work.FTS.MeridianDyn.Bridge.Pieces
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.WtoH_OpenAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The open quadrant `(0,∞) × (0,π/2)` on which the weights are honest. -/
abbrev QO : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_QO : IsOpen QO := isOpen_Ioi.prod isOpen_Ioo

/-! ## `divZ2 f` on the open quadrant -/

/-- `divZ2 f = f/z²` is `C^∞` (genuine smooth order) on the open quadrant, for
`SmoothOpen f`. -/
theorem contDiffOn_divZ2_QO {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Elliptic.divZ2 f)) QO := by
  have hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) QO := by
    simpa only [Work.FTS.EllipticEst.SmoothOpen, Work.FTS.EllipticEst.Q0] using hsm
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => p.1 ^ 2) QO := contDiffOn_fst.pow 2
  have hdiv := hf.div hden (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  refine hdiv.congr fun p hp => ?_
  rfl

/-- The `z`-slices of `divZ2 f` are `C^∞` (genuine smooth order) on `(0,∞)`, for
`SmoothOpen f` and `θ ∈ (0,π/2)`. -/
theorem contDiffOn_divZ2_zslice_O {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => Work.Elliptic.divZ2 f z' θ)
      (Set.Ioi 0) :=
  Work.FTS.LocData.contDiffOn_slice_z (contDiffOn_divZ2_QO hsm) hθ

/-- The `z`-slices of `divZ2 f` are `C^∞` (genuine smooth order) at every `z > 0`. -/
theorem contDiffAt_divZ2_zslice_O {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ∀ z : ℝ, 0 < z →
      ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => Work.Elliptic.divZ2 f z' θ) z :=
  fun z hz => (contDiffOn_divZ2_zslice_O hsm hθ).contDiffAt (isOpen_Ioi.mem_nhds hz)

/-- The `z`-slices of the `D_θ`-iterates of `divZ2 f` are `C^∞` (genuine smooth order) on
`(0,∞)`, for `SmoothOpen f` and `θ ∈ (0,π/2)`. -/
theorem contDiffOn_DthIter_divZ2_zslice_O {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ) (Set.Ioi 0) :=
  Work.FTS.LocData.contDiffOn_slice_z
    (Work.FTS.LocData.contDiffOn_DthIter isOpen_QO (contDiffOn_divZ2_QO hsm) i) hθ

/-- The `z`-slices of the `D_θ`-iterates of `divZ2 f` are `C^∞` at every `z > 0`. -/
theorem contDiffAt_DthIter_divZ2_zslice_O {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ∀ z : ℝ, 0 < z → ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ) z :=
  fun z hz => (contDiffOn_DthIter_divZ2_zslice_O hsm i hθ).contDiffAt
    (isOpen_Ioi.mem_nhds hz)

/-! ## The Leibniz expansions of `∂_z^m f` through `f = z²·divZ2 f` -/

/-- `∂_z^m f = z² ∂_z^m κ + 2m z ∂_z^{m-1} κ + m(m-1) ∂_z^{m-2} κ` with
`κ = divZ2 f`, for `SmoothOpen f`, `z > 0` and `θ ∈ (0,π/2)`. -/
theorem pzIter_divZ2_expansion_aux_O {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    {m : ℕ} (hm : m ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pzIter m f z θ = z ^ 2 * Work.Spaces.pzIter m (Work.Elliptic.divZ2 f) z θ
      + (2 * (m : ℝ)) * z * Work.Spaces.pzIter (m - 1) (Work.Elliptic.divZ2 f) z θ
      + ((m : ℝ) * ((m : ℝ) - 1))
          * Work.Spaces.pzIter (m - 2) (Work.Elliptic.divZ2 f) z θ := by
  have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Elliptic.divZ2 f z' θ) z :=
    contDiffAt_divZ2_zslice_O hsm hθ z hz
  have hcongr : Work.Spaces.pzIter m f z θ
      = Work.Spaces.pzIter m (fun z θ => z ^ 2 * Work.Elliptic.divZ2 f z θ) z θ := by
    refine Work.Elliptic.pzIter_congr_nhds m ?_
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
    exact Work.Elliptic.divZ2_eq_mul (ne_of_gt hz')
  rw [hcongr, Work.FTS.H2.Q.pzIter_sq_mul_sm m hm hκ]

/-- `∂_z^l D_θ^i f = z² ∂_z^l κ + 2l z ∂_z^{l-1}κ + l(l-1) ∂_z^{l-2}κ` with
`κ = D_θ^i (divZ2 f)`, for `SmoothOpen f`, `z > 0`, `θ ∈ (0,π/2)` and `l ≤ 4`. -/
theorem expand_aux_O {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i l : ℕ)
    (hl : l ≤ 4) {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pzIter l (Work.Spaces.DthIter i f) z θ
      = z ^ 2 * Work.Spaces.pzIter l (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ
        + (2 * (l : ℝ)) * z
            * Work.Spaces.pzIter (l - 1) (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ
        + ((l : ℝ) * ((l : ℝ) - 1))
            * Work.Spaces.pzIter (l - 2) (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ := by
  have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ) z :=
    contDiffAt_DthIter_divZ2_zslice_O hsm i hθ z hz
  have hmemIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 z :=
    isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; exact hz)
  have hev : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ,
      Work.Spaces.DthIter i f z' θ' = z' ^ 2 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ' := by
    filter_upwards [hmemIoi] with z' hz' θ'
    exact Work.Elliptic.DthIter_divZ2_eq i (ne_of_gt hz')
  rw [Work.Elliptic.pzIter_congr_of_eventually (u := Work.Spaces.DthIter i f)
    (v := fun z θ => z ^ 2 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z θ)
    (z := z) (θ := θ) l hev]
  exact Work.FTS.H2.Q.pzIter_sq_mul_sm l hl hκ

/-! ## The triangular estimate for `D_θ^i (divZ2 f)` -/

/-- The triangular estimate of `tri_aux_sm`, in the open-quadrant class `SmoothOpen`: the
`𝒲^{4,∞}`-bounds on `(z+1)^j ∂_z^j D_θ^i ((z+1)³/z²·f)` give
`|(z+1)^{j+3} ∂_z^j D_θ^i (divZ2 f)| ≤ 6000·Λ` for `j ≤ l`. -/
theorem tri_aux_O {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ))
    {i l : ℕ} (hi : 1 ≤ i) (hli : l + i ≤ 4) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hGev : ∀ z' : ℝ, 0 < z' → ∀ θ' : ℝ,
      Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) z' θ'
        = (z' + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ') :
    ∀ j ≤ l, |(z + 1) ^ (j + 3) * Work.Spaces.pzIter j (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ|
      ≤ 6000 * (Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  set Λ : ℝ := Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) with hΛ
  have hmemIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 z :=
    isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith)
  have hev : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ,
      Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) z' θ'
        = (z' + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ' := by
    filter_upwards [hmemIoi] with z' hz' θ'
    exact hGev z' hz' θ'
  have hbound : ∀ j ≤ l,
      |(z + 1) ^ j * Work.Spaces.pzIter j
        (fun z θ => (z + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z θ) z θ| ≤ Λ := by
    intro j hj
    have hji : j + i ≤ 4 := by omega
    have h1 := Work.Spaces.factor_bound α hα (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
      hmem j i (by omega) (fun _ => hji) z θ (le_of_lt hz)
      ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [if_neg (by omega : ¬ (i = 0))] at h1
    have hEq : Work.Spaces.pzIter j
          (fun z θ => (z + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z θ) z θ
        = Work.Spaces.pzIter j
          (Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)) z θ :=
      (Work.Elliptic.pzIter_congr_of_eventually
        (u := Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ))
        (v := fun z θ => (z + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z θ)
        (z := z) (θ := θ) j hev).symm
    rw [hEq, hΛ]
    exact h1
  have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ) z :=
    contDiffAt_DthIter_divZ2_zslice_O hsm i hθ z hz
  have hmain : ∀ j ≤ l,
      |(z + 1) ^ (j + 3) * Work.Spaces.pzIter j (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ|
        ≤ 6000 * Λ :=
    Work.FTS.H2.Q.tri_bound_sm
      (G := fun z θ => (z + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z θ)
      (κ := Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) rfl (by omega) hz hκ hbound
  intro j hj
  have hj' := hmain j hj
  rw [hΛ] at hj'
  exact hj'

end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row11Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.RNP

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


/-- The angular factor `Bv(θ) = 2α·Γ(θ)/c(α)` of row 11: away from `z = 0` it is exactly
`((z+1)²/z)·F_*(z,θ)`. -/
def Bv (α : ℝ) : ℝ → ℝ := fun θ => 2 * α * (Work.Spaces.Gam α θ / Work.Spaces.c α)

/-- The weighted coefficient `ℛ̃(Φ̃_*) = ((z+1)/z)·ℛ(Φ̃_*)` of the star package. -/
def Rv (α : ℝ) (Φs : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (z + 1) / z * Work.Construction.Rop α
    (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ

/-- The weighted piece of row 11: `G = ((z+1)³/z²)·N₁^{**}` — the function whose
`𝒲^{4,∞}`-norm controls `|N₁^{**}|_{ℋ⁴}` through `WtoH`. -/
def Gv (α : ℝ) (Φs : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (z + 1) ^ 3 / z ^ 2 * Work.FTS.Nonlin.N1ss α Φs z θ



/-! ## Two elementary facts about iterated `z`-derivatives and constants

`deriv_const_mul_loc` is the unconditional product rule for a constant (Lean's `deriv` is `0`
at a non-differentiable point, and `c•f` is differentiable at `z` iff `f` is, for `c ≠ 0`, so
the two junk values agree); `pzIter_const_mul` is its iterate.  (The sibling
`RowsN0Aux.deriv_const_mul'` of `Pieces/Basic.lean` is the same statement; it is reproved here
so that this module depends only on `Nonlinear/Defs`.  The neighbouring `DthIter_const_mul` is
taken from `Pieces/Basic.lean` by the consumers.) -/

theorem deriv_const_mul_loc (c : ℝ) (g : ℝ → ℝ) (z : ℝ) :
    deriv (fun z' => c * g z') z = c * deriv g z := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc; simp
  · by_cases hg : DifferentiableAt ℝ g z
    · exact deriv_const_mul c hg
    · have hnon : ¬ DifferentiableAt ℝ (fun z' => c * g z') z := by
        intro h
        have h2 : DifferentiableAt ℝ (fun z' => c⁻¹ * (c * g z')) z := h.const_mul c⁻¹
        have heq : (fun z' => c⁻¹ * (c * g z')) = g := by
          funext z'; rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
        rw [heq] at h2
        exact hg h2
      rw [deriv_zero_of_not_differentiableAt hnon,
        deriv_zero_of_not_differentiableAt hg, mul_zero]

theorem pzIter_const_mul (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter k (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pzIter k f z θ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ]
    funext z θ
    show deriv (fun z' => c * Work.Spaces.pzIter k f z' θ) z
      = c * deriv (fun z' => Work.Spaces.pzIter k f z' θ) z
    exact deriv_const_mul_loc c (fun z' => Work.Spaces.pzIter k f z' θ) z

end Work.FTS.Nonlinear.Pieces.RNP
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Aux.GamBar_dthU_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `D_θ`-bounds for the angular source `Γ̄ = Γ/c − (5/4) sin 2θ`

The angular part of the `Φ_*`-profile is `Γ̄(θ) = Γ(θ)/c − (5/4) sin 2θ`, where
`Γ(θ) = (sin θ cos²θ)^{α/3}` (`Work.Spaces.Gam`) and `c = c(α) ∈ [1/10, 10]`
(`Work.Spaces.c_bounds`) is the normalisation constant.

This file proves that `Γ̄` is bounded uniformly for `0 < α ≤ 1/4`, and that its
iterated `D_θ`-derivatives (`D_θ φ = sin 2θ · φ'`, `Work.Spaces.dthU`) satisfy

  `|D_θ^j Γ̄(θ)| ≤ cc j · α · Γ(θ) + dd j · sin 2θ`   (`1 ≤ j ≤ 5`)

on the open quadrant `(0, π/2)`, with constants independent of `α`.

**Route.**  `D_θ^j` is applied to the two summands separately.  For `Γ` the exact
formula `D_θ^j Γ = α · Tfun (j-1) α · Γ` (`Work.Spaces.dthU_iter_Gam`) together with
the uniform bound `|Tfun| ≤ tBound` (`Work.Spaces.dthU_iter_Tfun_le`) gives the first
summand; for `sin 2θ` one uses the elementary estimate `|D_θ^j sin 2·| ≤ D j · sin 2θ`
(`sin_two_dthU_le` below), which follows from the compactness of `[0, π/2]`: the ordinary
derivatives of `D_θ^i (sin 2·)` are continuous hence bounded there.

Because `D_θ^j (f + g)` is only available on an *open* set (the summands are not
globally smooth — `Γ` is not differentiable at `θ = 0, π/2`), the splitting is
formalised as an `Set.EqOn` on `(0, π/2)`: writing
`dGam α j = Γ` (`j = 0`) resp. `dGam α j = α · Tfun (j-1) α · Γ` (`j ≥ 1`) and
`Giter j = D_θ^j (sin 2·)`, one proves by induction on `j` that
`D_θ^j Γ̄ = (1/c) · dGam α j − (5/4) · Giter j` on `(0, π/2)`
(`GamBar_iter_EqOn`), using `dthU_EqOn_of_eqOn` (a function identity on an open set
is preserved by `D_θ`) and the one-step identity `dGam_step`, which is the recurrence
`α Tfun j α Γ ↦ α Tfun (j+1) α Γ` (`dthU_Tfun_mul_Gam_aux`) plus its `j = 0` case
(`dthU_Gam`).
-/

namespace Work.FTS.PhiStar.Psi0Aux

open scoped Real Topology
open Set Filter

noncomputable section

local notation "C∞" => (⊤ : ℕ∞)

/-! ## Congruence of `D_θ` on an open set -/

/-- `D_θ` only depends on the germ of the function: two functions agreeing on an open
set have `D_θ`-derivatives agreeing there. -/
lemma dthU_EqOn_of_eqOn {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (h : Set.EqOn f g s) :
    Set.EqOn (Work.Spaces.dthU f) (Work.Spaces.dthU g) s := by
  intro θ hθ
  simp only [Work.Spaces.dthU_apply]
  rw [Filter.EventuallyEq.deriv_eq (h.eventuallyEq_of_mem (hs.mem_nhds hθ))]

/-! ## The two summands of `Γ̄` -/

/-- `sin 2θ`, as a function of `θ`. -/
noncomputable def S2 : ℝ → ℝ := fun θ => Real.sin (2 * θ)

/-- `Giter j = D_θ^j (sin 2·)`. -/
noncomputable def Giter (j : ℕ) : ℝ → ℝ := Work.Spaces.dthU^[j] S2

/-- The `j`-th `D_θ`-iterate of `Γ` on `(0, π/2)`: `dGam α 0 = Γ` and
`dGam α (j+1) = α · Tfun j α · Γ` (`= D_θ^{j+1} Γ` there). -/
noncomputable def dGam (α : ℝ) : ℕ → ℝ → ℝ
  | 0 => Work.Spaces.Gam α
  | (j+1) => fun θ => α * Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ

/-- The right-hand side of the decomposition of `D_θ^j Γ̄` on `(0, π/2)`. -/
noncomputable def Fbar (α : ℝ) (j : ℕ) : ℝ → ℝ :=
  fun θ => (1 / Work.Spaces.c α) * dGam α j θ - (5 / 4) * Giter j θ

lemma Fbar_apply (α : ℝ) (j : ℕ) (θ : ℝ) : Fbar α j θ
    = (1 / Work.Spaces.c α) * dGam α j θ - (5 / 4) * Giter j θ := rfl

lemma Fbar_zero_apply (α : ℝ) (θ : ℝ) : Fbar α 0 θ = Work.FTS.VocabO.GamBar α θ := by
  change (1 / Work.Spaces.c α) * Work.Spaces.Gam α θ - (5 / 4) * Real.sin (2 * θ)
    = Work.Spaces.Gam α θ / Work.Spaces.c α - (5 / 4) * Real.sin (2 * θ)
  ring

/-! ## Smoothness of the two summands -/

lemma contDiff_S2 : ContDiff ℝ C∞ S2 := by
  show ContDiff ℝ C∞ (fun θ : ℝ => Real.sin (2 * θ))
  fun_prop

lemma Giter_contDiff (j : ℕ) : ContDiff ℝ C∞ (Giter j) := by
  simpa only [Giter] using Work.Spaces.dthU_iter_smooth contDiff_S2 j

lemma Giter_differentiableAt (j : ℕ) (θ : ℝ) : DifferentiableAt ℝ (Giter j) θ :=
  ((Giter_contDiff j).differentiable (by simp)).differentiableAt

lemma dGam_diff (α : ℝ) (j : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : DifferentiableAt ℝ (dGam α j) θ := by
  cases j with
  | zero =>
      simp only [dGam]
      exact Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2
  | succ j =>
      simp only [dGam]
      exact (Work.Spaces.Tfun_smooth j α).differentiable (by simp) |>.differentiableAt.const_mul α
        |>.mul (Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2)

/-! ## The two auxiliary estimates -/

/-- **The iterated `D_θ`-derivatives of `sin 2θ` are `O(sin 2θ)`.**
The proof is non-computational: `D_θ (sin 2·) = sin 2θ · (2 cos 2θ)` and, more
generally, `D_θ^{i+1} (sin 2·) = sin 2θ · (D_θ^i (sin 2·))'`, so it suffices to bound
the ordinary derivatives of the iterates; those are continuous (the iterates are
`C^∞`) on the compact interval `[0, π/2]`, hence bounded by compactness, and the
bounds may be fed back as one constant. -/
lemma sin_two_dthU_le :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ m : ℕ, m ≤ 5 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.dthU^[m] (fun t : ℝ => Real.sin (2 * t)) θ| ≤ D m * Real.sin (2 * θ) := by
  have key : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv (Giter i) θ| ≤ C := by
    intro i
    have hcont : ContinuousOn (deriv (Giter i)) (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
      ((Giter_contDiff i).continuous_deriv (by simp)).continuousOn
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
    refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
    have := hC θ hθ
    rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)
  choose C hC0 hCbd using key
  refine ⟨fun _ => max 1 (∑ i ∈ Finset.range 7, C i), ?_, ?_⟩
  · intro m
    exact le_trans zero_le_one (le_max_left _ _)
  · intro m hm θ hθ
    have hθI : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    rcases m with _ | i
    · change |S2 θ| ≤ max 1 (∑ i ∈ Finset.range 7, C i) * Real.sin (2 * θ)
      rw [S2, abs_of_nonneg hsin0]
      calc Real.sin (2 * θ) = 1 * Real.sin (2 * θ) := by ring
        _ ≤ max 1 (∑ i ∈ Finset.range 7, C i) * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hsin0
    · change |Work.Spaces.dthU^[i + 1] S2 θ| ≤ max 1 (∑ i ∈ Finset.range 7, C i)
        * Real.sin (2 * θ)
      have hstep : Work.Spaces.dthU^[i + 1] S2 θ
          = Real.sin (2 * θ) * deriv (Giter i) θ := by
        rw [Function.iterate_succ_apply', Work.Spaces.dthU_apply]
        rfl
      rw [hstep, abs_mul, abs_of_nonneg hsin0]
      have hi7 : i < 7 := by omega
      have hCi : C i ≤ ∑ j ∈ Finset.range 7, C j :=
        Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_range.mpr hi7)
      have hCD : C i ≤ max 1 (∑ j ∈ Finset.range 7, C j) :=
        le_trans hCi (le_max_right _ _)
      calc Real.sin (2 * θ) * |deriv (Giter i) θ|
          ≤ Real.sin (2 * θ) * C i := mul_le_mul_of_nonneg_left (hCbd i θ hθI) hsin0
        _ ≤ Real.sin (2 * θ) * max 1 (∑ j ∈ Finset.range 7, C j) :=
            mul_le_mul_of_nonneg_left hCD hsin0
        _ = max 1 (∑ j ∈ Finset.range 7, C j) * Real.sin (2 * θ) := by ring

/-- **The recurrence `D_θ (α · Tfun j α · Γ) = α · Tfun (j+1) α · Γ`** on `(0, π/2)`,
by the product rule and `Work.Spaces.Tfun_succ`, using `D_θ Γ = α q Γ`
(`Work.Spaces.dthU_Gam`). -/
lemma dthU_Tfun_mul_Gam_aux (j : ℕ) (α : ℝ) (hα : 0 < α) : Set.EqOn
    (Work.Spaces.dthU (fun θ : ℝ => α * Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ))
    (fun θ : ℝ => α * Work.Spaces.Tfun (j + 1) α θ * Work.Spaces.Gam α θ)
    (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  intro θ hθ
  have hG : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.Gam α t) θ :=
    Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2
  have hT : DifferentiableAt ℝ (Work.Spaces.Tfun j α) θ :=
    ((Work.Spaces.Tfun_smooth j α).differentiable (by simp)).differentiableAt
  have hmul : Work.Spaces.dthU (fun θ : ℝ => Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ) θ
      = Work.Spaces.dthU (Work.Spaces.Tfun j α) θ * Work.Spaces.Gam α θ
        + Work.Spaces.Tfun j α θ * Work.Spaces.dthU (fun t : ℝ => Work.Spaces.Gam α t) θ :=
    Work.Spaces.dthU_mul_apply (Work.Spaces.Tfun j α)
      (fun t : ℝ => Work.Spaces.Gam α t) θ hT hG
  have hfun : (fun θ : ℝ => α * Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ)
      = (fun θ : ℝ => α * (Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ)) := by
    funext t; ring
  calc Work.Spaces.dthU (fun θ : ℝ => α * Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ) θ
      = α * Work.Spaces.dthU (fun θ : ℝ => Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ) θ := by
        rw [hfun, Work.Spaces.dthU_const_mul]
    _ = α * (Work.Spaces.dthU (Work.Spaces.Tfun j α) θ * Work.Spaces.Gam α θ
          + Work.Spaces.Tfun j α θ * Work.Spaces.dthU (fun t : ℝ => Work.Spaces.Gam α t) θ) := by
        rw [hmul]
    _ = α * (Real.sin (2 * θ) * deriv (Work.Spaces.Tfun j α) θ * Work.Spaces.Gam α θ
          + Work.Spaces.Tfun j α θ * (α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ)) := by
        rw [Work.Spaces.dthU_apply, Work.Spaces.dthU_Gam α θ hα hθ]
    _ = α * Work.Spaces.Tfun (j + 1) α θ * Work.Spaces.Gam α θ := by
        rw [Work.Spaces.Tfun_succ]; ring

/-! ## The one-step recurrence for `dGam` -/

lemma dthU_dGam_zero (α : ℝ) (hα : 0 < α) :
    Set.EqOn (Work.Spaces.dthU (dGam α 0)) (dGam α 1) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  intro θ hθ
  have h := Work.Spaces.dthU_Gam α θ hα hθ
  simpa only [dGam, Work.Spaces.Tfun_zero] using h

lemma dGam_step (α : ℝ) (hα : 0 < α) (j : ℕ) :
    Set.EqOn (Work.Spaces.dthU (dGam α j)) (dGam α (j + 1))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  cases j with
  | zero => exact dthU_dGam_zero α hα
  | succ i => simpa only [dGam] using dthU_Tfun_mul_Gam_aux i α hα

/-! ## The decomposition of `D_θ^j Γ̄` -/

lemma Fbar_step (α : ℝ) (hα : 0 < α) (j : ℕ) :
    Set.EqOn (Work.Spaces.dthU (Fbar α j)) (Fbar α (j + 1))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  intro θ hθ
  have hA : DifferentiableAt ℝ (fun θ : ℝ => (1 / Work.Spaces.c α) * dGam α j θ) θ :=
    (dGam_diff α j hθ).const_mul _
  have hB : DifferentiableAt ℝ (fun θ : ℝ => (5 / 4) * Giter j θ) θ :=
    (Giter_differentiableAt j θ).const_mul _
  have hderiv : deriv (Fbar α j) θ
      = (1 / Work.Spaces.c α) * deriv (dGam α j) θ - (5 / 4) * deriv (Giter j) θ := by
    change deriv ((fun θ : ℝ => (1 / Work.Spaces.c α) * dGam α j θ)
      - (fun θ : ℝ => (5 / 4) * Giter j θ)) θ = _
    rw [deriv_sub hA hB, Work.Spaces.deriv_const_mul', Work.Spaces.deriv_const_mul']
  have h1 : Real.sin (2 * θ) * deriv (dGam α j) θ = dGam α (j + 1) θ := by
    have h := dGam_step α hα j hθ
    simpa only [Work.Spaces.dthU_apply] using h
  have h2 : Real.sin (2 * θ) * deriv (Giter j) θ = Giter (j + 1) θ := by
    simp only [Giter, Function.iterate_succ_apply', Work.Spaces.dthU_apply]
  calc Work.Spaces.dthU (Fbar α j) θ
      = Real.sin (2 * θ) * deriv (Fbar α j) θ := by rw [Work.Spaces.dthU_apply]
    _ = Real.sin (2 * θ) * ((1 / Work.Spaces.c α) * deriv (dGam α j) θ
          - (5 / 4) * deriv (Giter j) θ) := by rw [hderiv]
    _ = (1 / Work.Spaces.c α) * (Real.sin (2 * θ) * deriv (dGam α j) θ)
          - (5 / 4) * (Real.sin (2 * θ) * deriv (Giter j) θ) := by ring
    _ = (1 / Work.Spaces.c α) * dGam α (j + 1) θ - (5 / 4) * Giter (j + 1) θ := by rw [h1, h2]
    _ = Fbar α (j + 1) θ := by
        change _ = (1 / Work.Spaces.c α) * dGam α (j + 1) θ - (5 / 4) * Giter (j + 1) θ
        rfl

/-- **The decomposition of the iterated `D_θ`-derivatives of `Γ̄`.**  On the open
quadrant, `D_θ^j Γ̄ = (1/c)·dGam α j − (5/4)·Giter j`. -/
lemma GamBar_iter_EqOn (α : ℝ) (hα : 0 < α) (j : ℕ) :
    Set.EqOn (Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α)) (Fbar α j)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  induction j with
  | zero =>
      intro θ _
      simp only [Function.iterate_zero_apply]
      exact (Fbar_zero_apply α θ).symm
  | succ j ih =>
      intro θ hθ
      rw [Function.iterate_succ_apply']
      rw [dthU_EqOn_of_eqOn isOpen_Ioo ih hθ]
      exact Fbar_step α hα j hθ

/-! ## The pointwise bound on `dGam` -/

lemma dGam_le (α : ℝ) (j : ℕ) (hα : 0 < α) (hα1 : α ≤ 1) (hj : 1 ≤ j) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |dGam α j θ| ≤ α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hG := Work.Spaces.Gam_bounds α θ hα hθI
  have hT : |Work.Spaces.Tfun i α θ| ≤ Work.Spaces.tBound i 0 := by
    simpa only [Function.iterate_zero_apply] using
      Work.Spaces.dthU_iter_Tfun_le i α hα hα1 θ hθI 0
  simp only [dGam]
  rw [abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hG.1]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (le_of_lt hα)) hG.1

/-! ## The target -/

theorem GamBar_dthU_le :
    (∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.VocabO.GamBar α θ| ≤ K) ∧
    (∃ cc dd : ℕ → ℝ, (∀ j, 0 ≤ cc j) ∧ (∀ j, 0 ≤ dd j) ∧
      ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ j : ℕ, 1 ≤ j → j ≤ 5 →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ|
          ≤ cc j * α * Work.Spaces.Gam α θ + dd j * Real.sin (2 * θ)) := by
  obtain ⟨D, hD0, hD⟩ := sin_two_dthU_le
  constructor
  · refine ⟨12, by norm_num, ?_⟩
    intro α hα hα1 θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hc := (Work.Spaces.c_bounds α hα (by linarith)).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    have hG := Work.Spaces.Gam_bounds α θ hα hθI
    have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
      rw [abs_div, abs_of_pos hcpos, abs_of_nonneg hG.1]
      calc Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 1 / Work.Spaces.c α :=
            div_le_div_of_nonneg_right hG.2 (le_of_lt hcpos)
        _ ≤ 10 := by
            have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 10) hc
            have h2 : (1 : ℝ) / (1 / 10) = 10 := by norm_num
            linarith
    have h2 : |(5 / 4) * Real.sin (2 * θ)| ≤ 5 / 4 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      have := Real.abs_sin_le_one (2 * θ)
      linarith
    have h3 : |Work.Spaces.Gam α θ / Work.Spaces.c α - 5 / 4 * Real.sin (2 * θ)|
        ≤ |Work.Spaces.Gam α θ / Work.Spaces.c α| + |5 / 4 * Real.sin (2 * θ)| := by
      calc |Work.Spaces.Gam α θ / Work.Spaces.c α - 5 / 4 * Real.sin (2 * θ)|
          = |Work.Spaces.Gam α θ / Work.Spaces.c α + -(5 / 4 * Real.sin (2 * θ))| := by
            ring_nf
        _ ≤ |Work.Spaces.Gam α θ / Work.Spaces.c α| + |-(5 / 4 * Real.sin (2 * θ))| :=
            abs_add_le _ _
        _ = |Work.Spaces.Gam α θ / Work.Spaces.c α| + |5 / 4 * Real.sin (2 * θ)| := by
            rw [abs_neg]
    change |Work.Spaces.Gam α θ / Work.Spaces.c α - 5 / 4 * Real.sin (2 * θ)| ≤ 12
    linarith
  · refine ⟨fun j => 10 * Work.Spaces.tBound (j - 1) 0, fun j => (5 / 4) * D j, ?_, ?_, ?_⟩
    · intro j
      have := Work.Spaces.tBound_nonneg (j - 1) 0
      linarith
    · intro j
      have := hD0 j
      linarith
    · intro α hα hα1 j hj1 hj5 θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hc := (Work.Spaces.c_bounds α hα (by linarith)).1
      have hG := Work.Spaces.Gam_bounds α θ hα hθI
      have heq := GamBar_iter_EqOn α hα j hθ
      have h4 : |(1 / Work.Spaces.c α) * dGam α j θ|
          ≤ 10 * Work.Spaces.tBound (j - 1) 0 * α * Work.Spaces.Gam α θ := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Work.Spaces.c α)]
        have h1' := dGam_le α j hα (by linarith) hj1 hθ
        have hle : (1 / Work.Spaces.c α) ≤ 10 := by
          have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 10) hc
          have h2 : (1 : ℝ) / (1 / 10) = 10 := by norm_num
          linarith
        have hnn : 0 ≤ α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ :=
          mul_nonneg (mul_nonneg (le_of_lt hα) (Work.Spaces.tBound_nonneg _ _)) hG.1
        calc (1 / Work.Spaces.c α) * |dGam α j θ|
            ≤ (1 / Work.Spaces.c α) * (α * Work.Spaces.tBound (j - 1) 0
                * Work.Spaces.Gam α θ) := mul_le_mul_of_nonneg_left h1' (by positivity)
          _ ≤ 10 * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ) :=
              mul_le_mul_of_nonneg_right hle hnn
          _ = 10 * Work.Spaces.tBound (j - 1) 0 * α * Work.Spaces.Gam α θ := by ring
      have h2 : |(5 / 4) * Giter j θ| ≤ ((5 / 4) * D j) * Real.sin (2 * θ) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4)]
        have h := hD j hj5 θ hθ
        have hG2 : |Giter j θ| ≤ D j * Real.sin (2 * θ) := by
          change |Work.Spaces.dthU^[j] S2 θ| ≤ D j * Real.sin (2 * θ)
          exact h
        linarith [hG2]
      have h3 : |(1 / Work.Spaces.c α) * dGam α j θ - (5 / 4) * Giter j θ|
          ≤ |(1 / Work.Spaces.c α) * dGam α j θ| + |(5 / 4) * Giter j θ| := by
        calc |(1 / Work.Spaces.c α) * dGam α j θ - (5 / 4) * Giter j θ|
            = |(1 / Work.Spaces.c α) * dGam α j θ + -((5 / 4) * Giter j θ)| := by ring_nf
          _ ≤ |(1 / Work.Spaces.c α) * dGam α j θ| + |-((5 / 4) * Giter j θ)| :=
              abs_add_le _ _
          _ = |(1 / Work.Spaces.c α) * dGam α j θ| + |(5 / 4) * Giter j θ| := by rw [abs_neg]
      rw [heq, Fbar_apply]
      show |(1 / Work.Spaces.c α) * dGam α j θ - (5 / 4) * Giter j θ|
        ≤ 10 * Work.Spaces.tBound (j - 1) 0 * α * Work.Spaces.Gam α θ
          + 5 / 4 * D j * Real.sin (2 * θ)
      linarith [h3, h4, h2]

end

end Work.FTS.PhiStar.Psi0Aux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.phiASeriesDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Finset

namespace Work.FTS.PhiStar.Series.Deleg

/-- The coefficient of `(1+z)^{-(n+1)}` in the expansion of `𝒜φ = VocabO.phiA α`:
`2α-10`, `30-14α`, `24α-20`, `-12α` for `n = 0,1,2,3`. -/
def phiAcoef (α : ℝ) : ℕ → ℝ
  | 0 => 2 * α - 10
  | 1 => 30 - 14 * α
  | 2 => 24 * α - 20
  | _ => -12 * α

/-- `𝒜φ` written in powers of `u = 1/(1+z)`, together with its formal `k`-th derivative:
`(d/dz)^k (1+z)^m = (∏_{i<k}(m-i))·(1+z)^{m-k}`, so `phiAseries α k` is the closed form of
`iteratedDeriv k (phiA α)` on `z > 0`. -/
def phiAseries (α : ℝ) (k : ℕ) : ℝ → ℝ := fun z =>
  ∑ n ∈ Finset.range 4, phiAcoef α n * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
    * (1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ))

end Work.FTS.PhiStar.Series.Deleg
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.StrongEps.ClassCRHS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The `k`-th §8 piece of `N α (F_*+w) (Φs+Φg)` (order `N1gg, N1gs, …, N5ss`). -/
def PB (α : ℝ) (w Φs Φg : Fn) : ℕ → Fn
  | 0 => Work.FTS.Nonlin.N1gg α w Φg
  | 1 => Work.FTS.Nonlin.N1gs α w Φg
  | 2 => Work.FTS.Nonlin.N1sg α Φs w
  | 3 => Work.FTS.Nonlin.N1ss α Φs
  | 4 => Work.FTS.Nonlin.N2gg α w Φg
  | 5 => Work.FTS.Nonlin.N2gs α w Φg
  | 6 => Work.FTS.Nonlin.N2sg α Φs w
  | 7 => Work.FTS.Nonlin.N2ss α Φs
  | 8 => Work.FTS.Nonlin.N3gg α w Φg
  | 9 => Work.FTS.Nonlin.N3gs α w Φg
  | 10 => Work.FTS.Nonlin.N3sg α Φs w
  | 11 => Work.FTS.Nonlin.N3ss α Φs
  | 12 => Work.FTS.Nonlin.N4gg α w
  | 13 => Work.FTS.Nonlin.N4gs α w
  | 14 => Work.FTS.Nonlin.N4sg α w
  | 15 => Work.FTS.Nonlin.N4ss α
  | 16 => Work.FTS.Nonlin.N5gg w
  | 17 => Work.FTS.Nonlin.N5gs α w
  | 18 => Work.FTS.Nonlin.N5sg α w
  | _ => Work.FTS.Nonlin.N5ss α

/-- The `k`-th *product form* of the §8 pieces: a scalar times a product of a coefficient with a
factor.  `(z+1)/z`-weighted star coefficients are paired with the `z/(1+z)`-scaled factor, so
that the two factors of each product are separately `ℋ⁴`-honest (or one is `𝒲^{4,∞}`). -/
def NBlk (α : ℝ) (w Φs Φg : Fn) : ℕ → Fn
  | 0 => fun z θ => 2 * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ * w z θ)
  | 1 => fun z θ => 2 * (Work.Construction.Fstar α z θ
      * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ)
  | 2 => fun z θ => 2 * ((z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      * (z / (1 + z) * w z θ))
  | 3 => fun z θ => 2 * ((z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      * (z / (1 + z) * Work.Construction.Fstar α z θ))
  | 4 => fun z θ => (-2) * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ
      / Work.Construction.s2 θ * Work.Spaces.Dth w z θ)
  | 5 => fun z θ => (-2) * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ))
  | 6 => fun z θ => (-2) * ((z + 1) / z * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      / Work.Construction.s2 θ) * (z / (1 + z) * Work.Spaces.Dth w z θ))
  | 7 => fun z θ => (-2) * ((z + 1) / z * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      / Work.Construction.s2 θ) * (z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ))
  | 8 => fun z θ => (-(2 * α)) * (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg) z θ
      * Work.Spaces.Dz w z θ)
  | 9 => fun z θ => (-(2 * α)) * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg) z θ)
  | 10 => fun z θ => (-(2 * α)) * ((z + 1) / z * Work.Construction.Vop
      (Work.FTS.Nonlin.PhiTs α Φs) z θ * (z / (1 + z) * Work.Spaces.Dz w z θ))
  | 11 => fun z θ => (-(2 * α)) * ((z + 1) / z * Work.Construction.Vop
      (Work.FTS.Nonlin.PhiTs α Φs) z θ
      * (z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ))
  | 12 => fun z θ => (-(1 / 2)) * (Work.Construction.FK w z * Work.Spaces.Dth w z θ)
  | 13 => fun z θ => (-(1 / 2)) * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      * Work.Construction.FK w z)
  | 14 => fun z θ => (1 / 2) * (((-(2 * α)) * Work.Spaces.hKer z)
      * Work.Spaces.Dth w z θ)
  | 15 => fun z θ => (-(1 / 2)) * (Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
  | 16 => fun z θ => -(Real.sin θ) ^ 2 * (Work.Construction.FK w z * w z θ)
  | 17 => fun z θ => -(Real.sin θ) ^ 2 * (Work.Construction.Fstar α z θ * Work.Construction.FK w z)
  | 18 => fun z θ => -(Real.sin θ) ^ 2 * (Work.Construction.FK (Work.Construction.Fstar α) z
      * w z θ)
  | _ => fun z θ => -(Real.sin θ) ^ 2 * (Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Construction.Fstar α z θ)

/-- `PB` enumerates the pieces in the order of the split of `N`. -/
theorem PB_sum_eq (α : ℝ) (w Φs Φg : Fn) (z θ : ℝ) :
    (∑ k ∈ Finset.range 20, PB α w Φs Φg k z θ)
      = (Work.FTS.Nonlin.N1gg α w Φg z θ + Work.FTS.Nonlin.N1gs α w Φg z θ
          + Work.FTS.Nonlin.N1sg α Φs w z θ + Work.FTS.Nonlin.N1ss α Φs z θ)
        + (Work.FTS.Nonlin.N2gg α w Φg z θ + Work.FTS.Nonlin.N2gs α w Φg z θ
          + Work.FTS.Nonlin.N2sg α Φs w z θ + Work.FTS.Nonlin.N2ss α Φs z θ)
        + (Work.FTS.Nonlin.N3gg α w Φg z θ + Work.FTS.Nonlin.N3gs α w Φg z θ
          + Work.FTS.Nonlin.N3sg α Φs w z θ + Work.FTS.Nonlin.N3ss α Φs z θ)
        + (Work.FTS.Nonlin.N4gg α w z θ + Work.FTS.Nonlin.N4gs α w z θ
          + Work.FTS.Nonlin.N4sg α w z θ + Work.FTS.Nonlin.N4ss α z θ)
        + (Work.FTS.Nonlin.N5gg w z θ + Work.FTS.Nonlin.N5gs α w z θ
          + Work.FTS.Nonlin.N5sg α w z θ + Work.FTS.Nonlin.N5ss α z θ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, PB]
  ring

end Work.FTS.StrongEps.ClassCRHS
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.SupPort.HardyThetaO_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.SupPort.HardyThetaO_open`

The **angular Hardy inequality in the open-quadrant class**: if `g` is `C^∞` on the open
quadrant `Q0 = (0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen g`, *not* the analytic
neighbourhood class `SmoothNbhd` and *not* `SmoothQuad`), if `z > 0`, if the `θ`-slice
`θ ↦ g z θ` tends to `0` at `θ = 0⁺` and if the weighted angular energy
`(∂_θ g(z,σ))² sin(2σ)^{2-γ}` is integrable over `Iθ = [0,π/2]`, then

  `g(z,θ)² ≤ (100/(γ-1)) ∫_Iθ (∂_θ g(z,σ))² sin(2σ)^{2-γ} dσ`   for every `0 < θ < π/2`,

where `γ = Work.Spaces.gam α = 1 + α/10`.

This is the open-quadrant form of `Work.Spaces.HardyTheta` (`SmoothNbhd`, analytic on a
neighbourhood of the closed quadrant) and of `Work.FTS.H2.HardyThetaO` (`SmoothQuad`, `C^∞` on
`z > -1`).  Neither of those applies here: `SmoothOpen` only constrains `g` on `z > 0`, so no
smoothness of the extended `z`-slice is available.  The proof below keeps only what is
actually used: the two one-variable facts

* `θ ↦ g z θ` is `C^∞` on `(0,π/2)`  (`SmoothOpen.curry_θ`), and
* `θ ↦ ∂_θ g z θ` is `C^∞` on `(0,π/2)` (`SmoothOpen.pth` + `SmoothOpen.curry_θ`).

Everything else is the classical argument, isolated in the helper `hardyThetaO_slice`
(a statement about a single one-variable function), so that the main theorem is the two-line
instantiation `u = fun θ => g z θ`.

**Notation trap.**  The statement of `HardyThetaO_open` is written with a bare `π`.  Without
`open scoped Real` that identifier is *not* `Real.pi`: under the default `autoImplicit` option
it is auto-bound as an implicit variable, and the statement then reads `∀ {π : ℝ}, … ∀ θ ∈
Set.Ioo 0 (π/2), …` — which is **false** (only `θ < π/2` in the genuine sense is constrained by
`SmoothOpen`, so a large bump of `g z ·` at `θ = 3` contradicts the bound for `π = 10`).  The
declaration below therefore opens the real notation so that the statement means what it was
written to mean, exactly as in the consumers (`HardyThetaO_open` is invoked at
`θ ∈ Set.Ioo 0 (Real.pi / 2)`); the statement text is unchanged.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongEps.SupPort

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary angular facts -/

/-- `sin (2θ) ≥ 0` on the closed angular interval `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ) > 0` for `0 < θ < π/2`. -/
private lemma sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## The Hardy inequality for a single `θ`-slice -/


/-! ## The open-quadrant form -/


end Work.FTS.StrongEps.SupPort
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP

open Work.FTS.Galerkin (Fn Fam slice gdot IsDynGSolWith IsDynEqOn dynLin dynRHS)

set_option autoImplicit false

/-! ## The elliptic law `IsBslSolPos` -/

/-- **The positivised elliptic (Biot–Savart) law of the strong route.**

`IsBslSolPos α F Ψ` is the paper's (PolarBSL) problem

  `α²z²∂_zzΨ + α(5+α)z∂_zΨ - Lzero Ψ = F`  on the open quadrant `z > 0`, `0 < θ < π/2`,

together with

* the Dirichlet data `Ψ z 0 = Ψ z (π/2) = 0` **only for `z ≥ 0`** (the frozen `IsBslSol` asks it for
  every real `z`, which no solution of the local problem with data on `Iz` satisfies — audit
  `FTS_INTEGRATION_AUDIT.md` §3, the `Slab`-pinning trap), and
* the decay `Ψ z θ → 0` as `z → ∞`, for every `θ ∈ Iθ`.

This is the `Law` argument of `IsDynGSolWith` in the strong-solution route: the local solution of
S1 is only defined for `z ≥ 0`, so the two identifications at `θ = 0, π/2` are only known there. -/
def IsBslSolPos (α : ℝ) (F Ψ : Fn) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
    (∀ z, 0 ≤ z → Ψ z 0 = 0 ∧ Ψ z (π / 2) = 0) ∧
      (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0))


/-- The equation clause of `IsBslSolPos`, on the open quadrant. -/
theorem IsBslSolPos.eq {α : ℝ} {F Ψ : Fn} (h : IsBslSolPos α F Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Elliptic.bslOp α Ψ z θ = F z θ := h.1 z hz θ hθ hθ2


/-- The far-field decay of `IsBslSolPos`. -/
theorem IsBslSolPos.tendsto {α : ℝ} {F Ψ : Fn} (h : IsBslSolPos α F Ψ) :
    ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0) := h.2.2

/-! ## The regularity package `RegPkgMin` (design §3, verbatim) -/

/-- **The regularity package of the strong-solution route** — `FTS_STRONG_ROUTE.md` §3, copied
verbatim.

It is what the physical bridge (`RegPkgGal`, design §4) consumes: joint `C¹` in `(z,τ)`, `C⁴` at
every `τ ≥ 0`, continuity in `τ` up to `τ = 0` at every point of the open quadrant, `ℋ⁴`-membership
at every `τ ≥ 0`, a uniform `ℋ³`-bound on `∂_τg` for `τ > 0`, and vanishing on the angular
boundaries for `z ≥ 0`.

Compared with the frozen `Work.FTS.Galerkin.RegPkg` it drops: the `τ ∈ (-1,0)` region, the `z < 0`
half-line, the `C^∞` smoothness (replaced by `C⁴`), and the `ℋ⁵`-membership (`mem5`); nothing
downstream of `RegPkgGal` uses any of them (design §1). -/
structure RegPkgMin (α : ℝ) (g : Fam) : Prop where
  /-- joint `C¹` in the interior of the quadrant, for every fake time `τ > 0`. -/
  c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0)
  /-- `C⁴` in the space variables at every `τ ≥ 0`. -/
  c4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0
  /-- continuity in the fake time up to `τ = 0`, at every point of the open quadrant. -/
  cont : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ContinuousOn (fun τ => g z θ τ) (Set.Ici 0)
  /-- `ℋ⁴`-membership at every `τ ≥ 0`. -/
  mem4 : ∀ τ, 0 ≤ τ → Work.Spaces.HkMem α 4 (slice g τ)
  /-- a uniform `ℋ³`-bound on the fake-time derivative, for `τ > 0`. -/
  dbd : ∀ S, 0 < S → ∃ Cd, ∀ τ, 0 < τ → τ < S →
    Work.Spaces.HkMem α 3 (gdot g τ) ∧ Work.Spaces.HkNorm α 3 (gdot g τ) ≤ Cd
  /-- vanishing on the angular boundaries, for `z ≥ 0`. -/
  vanish : ∀ τ, 0 ≤ τ → ∀ z, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0



/-! ## The order-`6` size `Xn6`, and the `ℋ⁶`-package `RegPkgH6` -/

/-- The size `|g|_{ℋ⁶}` of the strong-solution route (the order-`6` companion of
`Work.FTS.Nonlin.Xn`). -/
abbrev Xn6 (α : ℝ) (g : Fn) : ℝ := Work.Spaces.HkNorm α 6 g

/-- The order-`4` size, under the name used by this chapter.  It is *definitionally*
`Work.FTS.Nonlin.Xn α g`. -/
abbrev Xn4 (α : ℝ) (g : Fn) : ℝ := Work.Spaces.HkNorm α 4 g


/-- **The `ℋ⁶`-package of a strong solution on `[0,T]`**: `RegPkgMin`, order-`6` membership and a
uniform `ℋ⁶`-bound on the interval.  This is the conclusion of S1 and of the persistence theorem
S2, and the input of the continuation argument S5. -/
structure RegPkgH6 (α : ℝ) (T : ℝ) (g : Fam) : Prop where
  /-- the finite-order regularity package of the strong route. -/
  min : RegPkgMin α g
  /-- `ℋ⁶`-membership at every `τ ∈ [0,T]`. -/
  mem6 : ∀ τ, 0 ≤ τ → τ ≤ T → Work.Spaces.HkMem α 6 (slice g τ)
  /-- a uniform `ℋ⁶`-bound on `[0,T]`. -/
  bd6 : ∃ C, ∀ τ, 0 ≤ τ → τ ≤ T → Xn6 α (slice g τ) ≤ C




/-! ## The bundled conclusion of S1 -/

/-- The dynamic modulated equation restricted to the interval `[0,T]`: the within-derivative on
`[0,T]` of the `τ`-slice of `g` equals the RHS.  It is the local form needed by a local
well-posedness statement (which asserts nothing beyond `T`); the frozen `IsDynEqOn` is the same
statement for all `τ ≥ 0`. -/
def IsDynEqOnT (α : ℝ) (T : ℝ) (Φ g : Fam) : Prop :=
  ∀ τ, 0 ≤ τ → τ ≤ T → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    HasDerivWithinAt (fun s => g z θ s) (dynLin α g τ z θ + dynRHS α Φ g τ z θ)
      (Set.Icc 0 T) τ

/-- The packaged solution of the dynamic modulated problem *on the interval* `[0,T]`: the elliptic
law holds at every `τ ∈ [0,T]` and the dynamic equation holds within `[0,T]`.  Unlike
`IsDynGSolWith` (a statement for all `τ ≥ 0`, i.e. a solution global in the fake time), this is the
form in which a *local* existence theorem is proved. -/
def IsDynGSolOnT (Law : Fn → Fn → Prop) (α T : ℝ) (Φ g : Fam) : Prop :=
  (∀ τ, 0 ≤ τ → τ ≤ T → Law (Work.Construction.Ftau α g τ) (slice Φ τ)) ∧ IsDynEqOnT α T Φ g


/-- **The bundled conclusion of the local well-posedness theorem `lwp_H6` (S1).**

There is a positive time `T`, the datum is attained at `τ = 0`, `(Φ,g)` solves the dynamic
modulated equation with the positivised elliptic law `IsBslSolPos α` *on* `[0,T]`, and `g`
satisfies the `ℋ⁶`-package `RegPkgH6 α T`.

This is a *definition of the conclusion*, not a reduction of S1: the statement of S1 is
`∃ T Φ g, LWPSol α T g₀ Φ g`, and it does not follow from any new axiom introduced here.  A
solution which is global in `τ` (as the existing `Open2`-style chains produce) is converted into
this form by `LWPSol.ofGlobal`. -/
structure LWPSol (α T : ℝ) (g₀ : Fn) (Φ g : Fam) : Prop where
  /-- the time is positive. -/
  pos : 0 < T
  /-- the datum is attained at `τ = 0`. -/
  init : ∀ z θ, g z θ 0 = g₀ z θ
  /-- the dynamic modulated equation with the positivised elliptic law, on `[0,T]`. -/
  sol : IsDynGSolOnT (IsBslSolPos α) α T Φ g
  /-- the `ℋ⁶`-package on `[0,T]`. -/
  h6 : RegPkgH6 α T g


theorem LWPSol.law {α T : ℝ} {g₀ : Fn} {Φ g : Fam} (h : LWPSol α T g₀ Φ g) :
    ∀ τ, 0 ≤ τ → τ ≤ T → IsBslSolPos α (Work.Construction.Ftau α g τ) (slice Φ τ) := h.sol.1


end Work.FTS.StrongLWP
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.OpenTwins

set_option autoImplicit false

/-! ## The weight is continuous on the open quadrant -/

private theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    have hθ : p.2 ∈ Set.Ioo (0 : ℝ) (π / 2) := hp.2
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  refine hw.mul ?_
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-! ## A.e. strong measurability of the integrand -/

private theorem aesm_mixed_Wt_sq_prod_open (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((hf.mixed j i).continuousOn.mul (continuousOn_Wt_Q0 α)).pow 2
  exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont

/-! ## Angular slices are integrable, by domination by `HkIntegrand α 4 f` -/

private theorem slice_integrable_aux (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Integrable (fun θ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := by
  filter_upwards [hAE.prodMk_left,
    ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    with z hz_meas hz
  refine Integrable.mono' (hmem.1 z hz) hz_meas ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij

/-! ## The iterated integral is integrable, by domination by `hmem.2` -/

private theorem outer_integrable_aux (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    Integrable (fun z => ∫ θ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict Work.Spaces.Iz) := by
  refine Integrable.mono' hmem.2 hAE.integral_prod_right' ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
  exact integral_mono_of_nonneg
    (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ _ => sq_nonneg _))
    (hmem.1 z hz)
    (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij))

/-! ## Assembly -/

theorem bt_prod_integrable_open (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ =>
          (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ∧ MeasureTheory.integral
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))
          (fun p : ℝ × ℝ =>
            (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
    fun z θ => sq_nonneg _
  have hAE := aesm_mixed_Wt_sq_prod_open α f hf j i
  have hslice := slice_integrable_aux α f hmem j i hi hij hAE
  have houter := outer_integrable_aux α f hmem j i hi hij hAE
  obtain ⟨hint, hval⟩ := Work.Spaces.integrable_prod_of_iterated hnn hAE hslice houter
  refine ⟨hint, ?_⟩
  rw [hval]
  simp only [Work.Spaces.L2Sq]

end Work.FTS.StrongPersist.N6Trans.OpenTwins
end
end
