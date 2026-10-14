import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.scoef_sum_shift
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.L12Add
-- ===== merged: Submission.Work.Blocks.alphaDz_pth_core_clean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Blocks

/-!
# The `α D_z ∂_θ` interpolation core

This file contains the target `Work.Blocks.alphaDz_pth_core_clean` together with the small
vocabulary layer (`sig`, `mixI`, `ddI`, `ttI`, `dI`, `mixLin`, `Honest`) in which the analytic
interpolation lemma that the proof consumes (`Work.Blocks.interp_core`) is phrased.

Mathematically the target is the *interpolation* estimate of the paper's §7,

`α² ∫∫ (D_z∂_θG)² w² σ_η ≤ C (α⁴ ∫∫ (D_z²G)² w² σ_η + ∫∫ (∂_θ²G)² w² σ_η
                              + α² ∫∫ (D_zG)² w² σ_η)`,

applied summand by summand to the `z`-family of the weighted `ℋ^k`-integrand of `D_z∂_θV` with
`G := D_z^j V`, plus the algebraic treatment of the mixed (`D_θ`) family.
-/

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The angular weight `σ_η(θ) = sin(2θ)^{-η}` (written out rather than imported so that this
module only depends on `Mathlib` and the two definitional modules). -/
noncomputable def sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))






/-- The honesty package of the interpolation's right hand side: the three functionals
`ddI`, `ttI`, `dI` are honest both slicewise (in `θ`, for every `z ∈ Iz`) and after
integration in `z`. -/
noncomputable def Honest (G : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ)
    Work.Spaces.Iθ) ∧
  (∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ)
    Work.Spaces.Iθ) ∧
  (∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ)
    Work.Spaces.Iθ) ∧
  IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ)
    Work.Spaces.Iz ∧
  IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ)
    Work.Spaces.Iz ∧
  IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sig θ)
    Work.Spaces.Iz

/-! ## Elementary facts about the weights -/

theorem w_zero : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]

theorem sig_pos {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) : 0 < sig θ := by
  rw [sig]
  exact Real.rpow_pos_of_pos
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])) _

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sig_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sig θ := by
  rw [sig]; exact Real.rpow_nonneg (sin_two_nonneg hθ) _

theorem sig_zero_left : sig 0 = 0 := by
  rw [sig, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
    Real.zero_rpow (by norm_num [Work.Spaces.eta])]

theorem sig_zero_right : sig (Real.pi / 2) = 0 := by
  rw [sig, show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi,
    Real.zero_rpow (by norm_num [Work.Spaces.eta])]

theorem gam_pos {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

theorem Wt_zero_left {α : ℝ} (hα : 0 < α) (z : ℝ) : Work.Spaces.Wt α z 0 = 0 := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
    Real.zero_rpow (by rw [Work.Spaces.gam]; intro h; linarith), mul_zero]


theorem Wt_zero_z (α θ : ℝ) : Work.Spaces.Wt α 0 θ = 0 := by
  rw [Work.Spaces.Wt, w_zero, zero_mul]

/-! ## Commutation of `∂_θ` with the `D_z`-iterates on the open quadrant -/

/-- `∂_θ (D_z g) = D_z (∂_θ g)` at a point where `g` is `C²`. -/
theorem pth_Dz_apply {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Spaces.pth (Work.Spaces.Dz g) z θ = Work.Spaces.Dz (Work.Spaces.pth g) z θ := by
  have h1 : Work.Spaces.pth (Work.Spaces.Dz g) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz g) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz g z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz g z θ') θ
    rw [deriv_const_mul_field]
  have h3 : Work.Spaces.pth (Work.Spaces.pz g) z θ = Work.Spaces.pz (Work.Spaces.pth g) z θ :=
    (Work.Spaces.pz_pth_comm hg).symm
  rw [h1, h3]
  rfl

/-- `D_z^j (D_z g) = D_z^{j+1} g`. -/
theorem DzIter_succ_apply (j : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (Work.Spaces.Dz g) = Work.Spaces.DzIter (j + 1) g := by
  induction j with
  | zero => rfl
  | succ j ih =>
      calc Work.Spaces.DzIter (j + 1) (Work.Spaces.Dz g)
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.Dz g)) := rfl
        _ = Work.Spaces.Dz (Work.Spaces.DzIter (j + 1) g) := by rw [ih]
        _ = Work.Spaces.DzIter (j + 1 + 1) g := rfl

/-- A `C^∞`-on-the-open-quadrant function is `C²` at every point of the open quadrant. -/
theorem SmoothOpen.contDiffAt_two {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
  ((hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      Work.FTS.EllipticEst.Q0).contDiffAt
    (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩))).of_le
    (by simp [Work.Stability.smoothOrder])

theorem SmoothOpen.DzIter_contDiffAt_two {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ)
    (hθ' : θ < Real.pi / 2) :
    ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter j f)) (z, θ) :=
  SmoothOpen.contDiffAt_two (hf.DzIter j) hz hθ hθ'

/-- `∂_θ` commutes with the `D_z`-iterates on the open quadrant. -/
theorem pth_DzIter_eqOn_Q0 {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth f)))
      Work.FTS.EllipticEst.Q0 := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ, hθ'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hstep : Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j f)) z θ
          = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f)) z θ :=
        pth_Dz_apply (SmoothOpen.DzIter_contDiffAt_two hf j hz hθ hθ')
      have hcongr : Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f)) z θ
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ := by
        have hev : (fun z' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter j f) z' θ)
            =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.DzIter j (Work.Spaces.pth f) z' θ) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ, hθ'⟩)
        simp only [Work.Spaces.Dz, Work.Spaces.pz]
        rw [hev.deriv_eq]
      show Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter (j + 1) f)) (z, θ)
          = Function.uncurry (Work.Spaces.DzIter (j + 1) (Work.Spaces.pth f)) (z, θ)
      simp only [Function.uncurry]
      rw [show Work.Spaces.DzIter (j + 1) f
            = Work.Spaces.Dz (Work.Spaces.DzIter j f) from rfl,
          hstep, hcongr]
      rw [show Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f))
            = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.pth f)) from
            (DzIter_succ_apply j (Work.Spaces.pth f)).symm]
      rw [DzIter_succ_apply j (Work.Spaces.pth f)]

/-! ## The `lintegral` presentation of a weighted energy -/






/-- At `z = 0` the radial weight vanishes and with it every summand of the `ℋ^k`-integrand. -/
theorem HkIntegrand_zero_z (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, w_zero, zero_div, mul_zero, Work.Spaces.Wt,
    Work.Spaces.wTheta, zero_mul]
  simp



end Work.Blocks
end
-- ===== merged: Submission.Work.EllipticEst.Assembly.PairDefs =====
section

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

/-- The exponent `β = (5-α)/α` of the pairing weight.  With this exponent the radial part of
`bslOp` is in divergence form: `z^β(-α²z²∂_zz - α(5+α)z∂_z) = -∂_z(α²z^{β+2}∂_z)`, because
`α²(β+2) = α(5+α)`. -/
def pairBeta (α : ℝ) : ℝ := (5 - α) / α

/-- The pairing weight `z^{(5-α)/α}·cos θ` on which `bslOp α` is self-adjoint. -/
def pairWeight (α : ℝ) : ℝ × ℝ → ℝ := fun x => x.1 ^ pairBeta α * Real.cos x.2

/-- The radial component of the divergence form of `bslOp α`:
`A = α²z^{β+2}cos θ·(∂_zφ·Φ - ∂_zΦ·φ)`. -/
def pairRad (α : ℝ) (Φ φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun x =>
  α ^ 2 * x.1 ^ (pairBeta α + 2) * Real.cos x.2
    * (Work.Spaces.pz φ x.1 x.2 * Φ x.1 x.2 - Work.Spaces.pz Φ x.1 x.2 * φ x.1 x.2)

/-- The angular component of the divergence form of `bslOp α`:
`B = z^β cos θ·(∂_θφ·Φ - ∂_θΦ·φ)`. -/
def pairAng (α : ℝ) (Φ φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun x =>
  x.1 ^ pairBeta α * Real.cos x.2
    * (Work.Spaces.pth φ x.1 x.2 * Φ x.1 x.2 - Work.Spaces.pth Φ x.1 x.2 * φ x.1 x.2)

@[simp] theorem pairBeta_def (α : ℝ) : pairBeta α = (5 - α) / α := rfl

@[simp] theorem pairWeight_apply (α : ℝ) (x : ℝ × ℝ) :
    pairWeight α x = x.1 ^ pairBeta α * Real.cos x.2 := rfl

@[simp] theorem pairRad_apply (α : ℝ) (Φ φ : ℝ → ℝ → ℝ) (x : ℝ × ℝ) :
    pairRad α Φ φ x = α ^ 2 * x.1 ^ (pairBeta α + 2) * Real.cos x.2
      * (Work.Spaces.pz φ x.1 x.2 * Φ x.1 x.2 - Work.Spaces.pz Φ x.1 x.2 * φ x.1 x.2) :=
  rfl

@[simp] theorem pairAng_apply (α : ℝ) (Φ φ : ℝ → ℝ → ℝ) (x : ℝ × ℝ) :
    pairAng α Φ φ x = x.1 ^ pairBeta α * Real.cos x.2
      * (Work.Spaces.pth φ x.1 x.2 * Φ x.1 x.2 - Work.Spaces.pth Φ x.1 x.2 * φ x.1 x.2) :=
  rfl

/-- The exact matching of exponents behind the divergence form:
`α²(β+2) = α(5+α)` for `β = (5-α)/α`. -/
theorem sq_mul_pairBeta_add_two {α : ℝ} (hα : α ≠ 0) :
    α ^ 2 * (pairBeta α + 2) = α * (5 + α) := by
  rw [pairBeta_def]
  field_simp
  ring

end Work.EllipticEst.Assembly
end
end
-- ===== merged: Submission.Work.EllipticEst.Assembly.eq_zero_of_test_integral_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The fundamental lemma of the calculus of variations on an open set of `ℝ × ℝ`

`Work.EllipticEst.Assembly.eq_zero_of_test_integral_zero`:

If `G` is continuous on an open set `U ⊆ ℝ × ℝ` and the integral `∫_U G φ` vanishes for every
`C^∞` compactly supported test function `φ` whose (topological) support lies in `U`, then `G`
vanishes at every point of `U`.

Proof.  Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`
(`Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff`) gives the a.e. statement
`∀ᵐ x ∂volume, x ∈ U → G x = 0`; the test-function hypothesis of that theorem is exactly ours,
the only difference being that its integral is taken over the whole space, which is harmless
because `φ` vanishes off `tsupport φ ⊆ U`
(`MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero`).  Finally the a.e. statement is
upgraded to a pointwise one: `{x ∈ U | G x ≠ 0}` is open (continuity at every point of the open
set `U`), so if it were nonempty it would have positive measure, contradicting the a.e. vanishing.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Work.EllipticEst.Assembly

theorem eq_zero_of_test_integral_zero {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {G : ℝ × ℝ → ℝ} (hG : ContinuousOn G U)
    (h : ∀ φ : (ℝ × ℝ) → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
      tsupport φ ⊆ U → ∫ x in U, G x * φ x = 0) :
    ∀ x ∈ U, G x = 0 := by
  -- Step 1: `G` vanishes a.e. on `U`.
  have hae : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), x ∈ U → G x = 0 := by
    refine IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hU ?_ ?_
    · -- continuity on the open set `U` gives local integrability there
      exact hG.locallyIntegrableOn hU.measurableSet
    · intro g hg hgsupp htsupp
      -- `g x • G x = G x * g x` for real-valued `G`
      have hfun : (fun x : ℝ × ℝ => g x • G x) = fun x => G x * g x := by
        funext x; rw [smul_eq_mul, mul_comm]
      rw [hfun]
      -- the integral over `U` of `G * g` is the integral over the whole space, as `g` vanishes
      -- off `U`
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (fun x hx => ?_)]
      · exact h g (fun n => hg.of_le (WithTop.coe_le_coe.mpr le_top)) hgsupp htsupp
      · have : g x = 0 := by
          by_contra hgx
          exact hx (htsupp (subset_closure (Function.mem_support.mpr hgx)))
        rw [this, mul_zero]
  -- Step 2: the (relatively) open set `{x ∈ U | G x ≠ 0}` is null, hence empty.
  intro x hx
  by_contra hne
  have hSopen : IsOpen {y : ℝ × ℝ | y ∈ U ∧ G y ≠ 0} := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyU, hyG⟩
    have hcont : ContinuousAt G y := hG.continuousAt (hU.mem_nhds hyU)
    have h1 : ∀ᶠ z in 𝓝 y, G z ≠ 0 := hcont.eventually_ne hyG
    filter_upwards [h1, hU.mem_nhds hyU] with z hz1 hz2
    exact ⟨hz2, hz1⟩
  have hSnull : volume {y : ℝ × ℝ | y ∈ U ∧ G y ≠ 0} = 0 := by
    have h0 := MeasureTheory.ae_iff.mp hae
    rwa [show {x : ℝ × ℝ | ¬ (x ∈ U → G x = 0)} = {y : ℝ × ℝ | y ∈ U ∧ G y ≠ 0} from by
          ext y; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, not_imp]] at h0
  have hSne : ({y : ℝ × ℝ | y ∈ U ∧ G y ≠ 0} : Set _).Nonempty := ⟨x, hx, hne⟩
  have hpos : 0 < volume {y : ℝ × ℝ | y ∈ U ∧ G y ≠ 0} := hSopen.measure_pos volume hSne
  rw [hSnull] at hpos
  exact lt_irrefl 0 hpos

end Work.EllipticEst.Assembly
end
-- ===== merged: Submission.Work.EllipticEst.Core.HkSqLHSv2Meas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Measurability of the weighted angular slices used by `HkSqLHS_le_summands_v2`

Two facts are needed to compare the iterated Bochner integral `HkSq` with the sum of its
summands:

* `v2_aesm_slice` — for `u` of class `C^∞` on the open quadrant and every real exponent `e`,
  the function `θ ↦ (u z θ)² (w z)² sin(2θ)^e` is `AEMeasurable` on `[0,π/2]`;
* `v2_aesm_integral` — the same expression integrated in `θ` is `AEMeasurable` as a function
  of `z` on `[0,∞)`.

Both are instances of the general principle "continuity on the open quadrant gives a.e. strong
measurability for the restricted measures" (`Work.Spaces.aesm_of_continuousOn_Qd`,
`Work.Spaces.aesm_slice_of_continuousOn_Qd`), together with
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` for the second one.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

set_option autoImplicit false

/-- The squared radial weight `(w z)²` is continuous on the open quadrant. -/
theorem continuousOn_w_sq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hfun : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      = fun p : ℝ × ℝ => (((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2) := by
    funext p
    simp only [Work.Spaces.w]
  rw [hfun]
  exact (((continuousOn_const.add continuousOn_fst).pow 2).div (continuousOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))).pow 2

/-- `θ ↦ sin(2θ)^e` is continuous on the open quadrant, for every real exponent `e`. -/
theorem continuousOn_sin_rpow_Q0 (e : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ e)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hsinpos : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2), 0 < Real.sin (2 * p.2) := by
    rintro ⟨z, θ⟩ ⟨-, hθ0, hθ1⟩
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- **Measurability of the weighted angular slice.**  For `u` of class `C^∞` on the open
quadrant, any real exponent `e` and every `z ∈ [0,∞)`, the function
`θ ↦ (u z θ)² (w z)² sin(2θ)^e` is `AEMeasurable` for `volume.restrict [0,π/2]`. -/
theorem v2_aesm_slice {u : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (e : ℝ) :
    ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable
        (fun θ : ℝ => (u z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ e)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hzero : (fun θ : ℝ => (u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ e) = fun _ : ℝ => (0 : ℝ) := by
      rw [← hz0]
      funext θ
      simp only [Work.Spaces.w]
      norm_num
    rw [hzero]
    exact aemeasurable_const
  · have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ e)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((hu.continuousOn.pow 2).mul continuousOn_w_sq_Q0).mul (continuousOn_sin_rpow_Q0 e)
    exact (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos).aemeasurable

/-- **Measurability in `z` of the weighted angular integral.**  For `u` of class `C^∞` on the
open quadrant and any real exponent `e`, the function
`z ↦ (w z)² ∫_θ (u z θ)² sin(2θ)^e dθ` is `AEMeasurable` for `volume.restrict [0,∞)`. -/
theorem v2_aesm_integral {u : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (e : ℝ) :
    AEMeasurable
      (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * (Real.sin (2 * θ)) ^ e)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * ((u p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ e))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    continuousOn_w_sq_Q0.mul ((hu.continuousOn.pow 2).mul (continuousOn_sin_rpow_Q0 e))
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * ((u p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ e))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have h2 : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ, ((Work.Spaces.w z) ^ 2
        * ((u z θ) ^ 2 * (Real.sin (2 * θ)) ^ e))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    haesm.integral_prod_right'
  have heq : (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * (Real.sin (2 * θ)) ^ e)
      = fun z : ℝ => ∫ θ, ((Work.Spaces.w z) ^ 2
        * ((u z θ) ^ 2 * (Real.sin (2 * θ)) ^ e))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    funext z
    rw [MeasureTheory.integral_const_mul]
  rw [heq]
  exact h2.aemeasurable

end Work.EllipticEst.Core
end
end
-- ===== merged: Submission.Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The angular moment `F_*(f)` is an antiderivative of `F_*(∂_z f)`.**

With `F_*(g)(r) = ∫_θ g(r,θ) sinθcos²θ dθ` (`Work.Elliptic.Fstar`) and
`∂_z f = Work.Spaces.pz f`, integrating the identity `∂_r (f(r,θ) sinθcos²θ) =
∂_z f(r,θ) sinθcos²θ` over the box `[s,z] × [0,π/2]` — first in `θ`, then in `r` —
gives

  `F_*(f)(z) - F_*(f)(s) = ∫_s^z F_*(∂_z f)(r) dr`.

The proof avoids differentiating under the `θ`-integral: for each fixed `θ` the map
`r ↦ f(r,θ)` is `C^∞` on `(0,∞)` (which contains `[s,z]` when `0 < s`), so the
fundamental theorem of calculus applies pointwise on the slice
(`SmoothOpen.curry_z`, `SmoothOpen.hasDerivAt_slice`), and the resulting iterated
integral over `[s,z] × [0,π/2]` is interchanged with Tonelli–Fubini using the
integrability of the box integrand (the hypothesis `hbox`). -/
theorem Fstar_sub_eq_integral_pz {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z)
    (hsl_s : MeasureTheory.IntegrableOn (fun θ => f s θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hsl_z : MeasureTheory.IntegrableOn (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hbox : MeasureTheory.Integrable
      (Function.uncurry (fun r θ : ℝ => Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    Work.Elliptic.Fstar f z - Work.Elliptic.Fstar f s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz f) r := by
  -- the fundamental theorem of calculus on the `z`-slice at a fixed interior angle
  have hftc_θ : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ∫ r in s..z, Work.Spaces.pz f r θ = f z θ - f s θ := by
    intro θ hθ
    have hmem : Set.Icc s z ⊆ Set.Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le hs hr.1
    have hcont : ContinuousOn (fun r => f r θ) (Set.Icc s z) :=
      (hf.curry_z hθ).continuousOn.mono hmem
    have hderiv : ∀ r ∈ Set.Ioo s z, HasDerivAt (fun r' => f r' θ) (Work.Spaces.pz f r θ) r :=
      fun r hr => hf.hasDerivAt_slice hθ (lt_of_lt_of_le hs (le_of_lt hr.1))
    have hint : IntervalIntegrable (fun r => Work.Spaces.pz f r θ) MeasureTheory.volume s z :=
      (((hf.pz).curry_z hθ).continuousOn.mono hmem).intervalIntegrable_of_Icc hsz
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsz hcont hderiv hint
  -- the pointwise identity on the angular interval (the weight vanishes at the endpoints)
  have hpoint : ∀ θ ∈ Work.Spaces.Iθ,
      f z θ * Work.Elliptic.sinCos2 θ - f s θ * Work.Elliptic.sinCos2 θ
        = ∫ r in s..z, Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ := by
    intro θ hθ
    rcases eq_or_ne θ 0 with rfl | h0
    · simp [Work.Elliptic.sinCos2]
    · rcases eq_or_ne θ (π / 2) with rfl | h1
      · simp [Work.Elliptic.sinCos2, Real.cos_pi_div_two]
      · have hθ' : θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
          ⟨lt_of_le_of_ne hθ.1 (Ne.symm h0), lt_of_le_of_ne hθ.2 h1⟩
        rw [intervalIntegral.integral_mul_const, hftc_θ θ hθ']
        ring
  -- the left hand side is the `θ`-first iterated integral
  have hL : Work.Elliptic.Fstar f z - Work.Elliptic.Fstar f s
      = ∫ θ in Work.Spaces.Iθ, ∫ r in s..z,
          Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ := by
    simp only [Work.Elliptic.Fstar]
    rw [← MeasureTheory.integral_sub hsl_z hsl_s]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
  -- the right hand side is the `r`-first iterated integral (Tonelli–Fubini, `hbox`)
  have key : (∫ θ in Work.Spaces.Iθ, ∫ r in s..z,
        Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ)
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz f) r := by
    have h1 := MeasureTheory.integral_prod_symm
      (f := Function.uncurry (fun r θ : ℝ => Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ))
      (μ := MeasureTheory.volume.restrict (Set.Ioc s z))
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hbox
    have h2 := MeasureTheory.integral_prod
      (f := Function.uncurry (fun r θ : ℝ => Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ))
      (μ := MeasureTheory.volume.restrict (Set.Ioc s z))
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hbox
    simp only [Function.uncurry_apply_pair] at h1 h2
    simp_rw [intervalIntegral.integral_of_le hsz]
    rw [← h1, h2]
    simp only [Work.Elliptic.Fstar]
  exact hL.trans key

end Work.EllipticEst.H2W
end
-- ===== merged: Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.H2W

open scoped Real Topology
open Set Filter

/-- One step of the commutation of `∂_θ` with `D_z = z ∂_z`: at a point where `g` is `C²`,
`∂_θ (D_z g) = D_z (∂_θ g)`. -/
theorem pth_Dz_apply {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Spaces.pth (Work.Spaces.Dz g) z θ = Work.Spaces.Dz (Work.Spaces.pth g) z θ := by
  have h1 : Work.Spaces.pth (Work.Spaces.Dz g) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz g) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz g z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz g z θ') θ
    rw [deriv_const_mul_field]
  have h3 : Work.Spaces.pth (Work.Spaces.pz g) z θ = Work.Spaces.pz (Work.Spaces.pth g) z θ :=
    (Work.Spaces.pz_pth_comm hg).symm
  rw [h1, h3]
  rfl

/-- `∂_θ` commutes with the iterates of `D_z` on the open quadrant: for `f` of class `C^∞`
on `(0,∞) × (0,π/2)` one has `∂_θ (D_z^j f) = D_z^j (∂_θ f)` there. -/
theorem pth_DzIter_eqOn_Q0 {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth f)))
      Work.FTS.EllipticEst.Q0 := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ, hθ'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter j f)) (z, θ) :=
        ((hf.DzIter j).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩))).of_le
          (by simp [Work.Stability.smoothOrder])
      have hstep : Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j f)) z θ
          = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f)) z θ :=
        pth_Dz_apply hcd
      have hcongr : Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f)) z θ
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ := by
        have hev : (fun z' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter j f) z' θ)
            =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.DzIter j (Work.Spaces.pth f) z' θ) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ, hθ'⟩)
        simp only [Work.Spaces.Dz, Work.Spaces.pz]
        rw [hev.deriv_eq]
      show Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter (j + 1) f)) (z, θ)
          = Function.uncurry (Work.Spaces.DzIter (j + 1) (Work.Spaces.pth f)) (z, θ)
      simp only [Function.uncurry]
      rw [show Work.Spaces.DzIter (j + 1) f
            = Work.Spaces.Dz (Work.Spaces.DzIter j f) from rfl, hstep, hcongr]
      rfl

/-- The second angular derivative `∂_θ²` commutes with the iterates of `D_z = z ∂_z` on the
open quadrant: for `f` of class `C^∞` on `(0,∞) × (0,π/2)`,
`∂_θ² (D_z^i f) = D_z^i (∂_θ² f)` there. -/
theorem pthIter2_DzIter_comm {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i f)))
      (Function.uncurry (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 f)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hp
  obtain ⟨hz, hθ, hθ'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hθ'⟩
  have hL : Work.Spaces.pthIter 2 (Work.Spaces.DzIter i f)
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.DzIter i f)) := by
    rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  have hR : Work.Spaces.pthIter 2 f
      = Work.Spaces.pth (Work.Spaces.pth f) := by
    rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  have hstep1 : Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.DzIter i f)) z θ
      = Work.Spaces.pth (Work.Spaces.DzIter i (Work.Spaces.pth f)) z θ := by
    have hev : (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter i f) z θ')
        =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.DzIter i (Work.Spaces.pth f) z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθIoo] with θ' hθ'
      exact pth_DzIter_eqOn_Q0 hf i
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩)
    show deriv (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter i f) z θ') θ
        = deriv (fun θ' : ℝ => Work.Spaces.DzIter i (Work.Spaces.pth f) z θ') θ
    rw [hev.deriv_eq]
  have hstep2 : Work.Spaces.pth (Work.Spaces.DzIter i (Work.Spaces.pth f)) z θ
      = Work.Spaces.DzIter i (Work.Spaces.pth (Work.Spaces.pth f)) z θ :=
    pth_DzIter_eqOn_Q0 hf.pth i (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩)
  simp only [Function.uncurry]
  rw [hL, hR, hstep1, hstep2]

end Work.EllipticEst.H2W
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Strip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory TemperedDistribution FourierTransform Filter Set
open scoped SchwartzMap BesselPotentialSpace ENNReal Topology LineDeriv Laplacian

namespace Work.EllipticEst.InteriorRegularity

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

/-- The two-dimensional Euclidean space used throughout. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The first coordinate direction `e₀` (`s`-direction). -/
def e0 : E2 := EuclideanSpace.basisFun (Fin 2) ℝ 0

/-- The second coordinate direction `e₁` (`θ`-direction). -/
def e1 : E2 := EuclideanSpace.basisFun (Fin 2) ℝ 1

/-- The strip `{0 < θ < π/2}` in the `(s,θ)`-plane. -/
def stripE : Set E2 := {x : E2 | x 1 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)}

/-- The `s`-coordinate. -/
def Sc (x : E2) : ℝ := x 0


/-- Reinterpret a curried function as a function on `E2`. -/
def curry (F : ℝ → ℝ → ℝ) : E2 → ℝ := fun x => F (x 0) (x 1)

/-- Complex valued version of `curry`. -/
def curryC (F : ℝ → ℝ → ℂ) : E2 → ℂ := fun x => F (x 0) (x 1)

/-- The point of `E2` with coordinates `(s, θ)`. -/
def coords (s θ : ℝ) : E2 :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then s else θ)

theorem curryC_curry'_apply (F : ℝ → ℝ → ℂ) (s θ : ℝ) : curryC F (coords s θ) = F s θ := by
  simp [curryC, coords]


/-- The directional derivative in the `e₀` direction. -/
def d0 (f : E2 → ℂ) : E2 → ℂ := fun x => lineDeriv ℝ f x e0

/-- The directional derivative in the `e₁` direction. -/
def d1 (f : E2 → ℂ) : E2 → ℂ := fun x => lineDeriv ℝ f x e1

/-- The second order operator `Kop` transported to `E2`: for `ψ` a test function,
`Kop ψ = -∂_ss ψ - ∂_θθ ψ - 5 ∂_s ψ + tan θ ∂_θ ψ + (tan² θ - 5) ψ`.

This is `bslOp α φ` evaluated at `(exp (α s), θ)` when `φ (z,θ) = ψ ((1/α) log z, θ)`,
as a function of the strip coordinates; see `Vfun`, `Gfun` and `StripWeak` below. -/
def Kop (ψ : E2 → ℂ) : E2 → ℂ := fun x =>
  - d0 (d0 ψ) x - d1 (d1 ψ) x - 5 * d0 ψ x + (Real.tan (x 1) : ℂ) * d1 ψ x
    + (((Real.tan (x 1)) ^ 2 - 5 : ℝ) : ℂ) * ψ x

/-- The weight `α z^(p+1) cos θ` with `z = exp (α s)`, `p+1 = (5+2α)/α`. -/
def wt (α : ℝ) : E2 → ℝ := fun x =>
  α * (Real.exp (α * x 0)) ^ ((5 + 2 * α) / α) * Real.cos (x 1)


/-- The source of the strip problem: `G = α z · F · ω`; zero outside the strip. -/
def Gfun (α : ℝ) (F : ℝ → ℝ → ℝ) : E2 → ℝ :=
  stripE.indicator (fun x => wt α x * F (Real.exp (α * x 0)) (x 1))



end Work.EllipticEst.InteriorRegularity
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.pullbackIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.VT

open scoped Real Topology
open MeasureTheory Set

/-- The determinant of `(c • 1).prodMap 1` acting on `ℝ × ℝ` is `c`. -/
private theorem det_toSpanSingleton_prodMap_one (c : ℝ) :
    ((ContinuousLinearMap.toSpanSingleton ℝ c).prodMap (1 : ℝ →L[ℝ] ℝ)).det = c := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    LinearMap.det_ring]
  simp


end Work.EllipticEst.InteriorRegularity.VT
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.box_of_compactSupport =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.EllipticEst.ModalSolution

/-- A compact subset of the open quadrant `(0,∞) × (0,π/2)` is contained in a box
`(a,b) × (c,d)` with `0 < a < b` and `0 < c < d < π/2`.

(The box is obtained from the extreme value theorem applied to the two coordinates on the
compact set; note that no condition links the box to the support -- it only has to *contain*
it, and to be contained in the closed strip `[0,∞) × [0,π/2)`.) -/
private theorem exists_box_of_isCompact_subset_Q0 {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsub : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ a b c d : ℝ, 0 < a ∧ a < b ∧ 0 < c ∧ c < d ∧ d < π / 2 ∧
      K ⊆ Set.Ioo a b ×ˢ Set.Ioo c d := by
  obtain rfl | hne := K.eq_empty_or_nonempty
  · exact ⟨1, 2, 1 / 4, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num,
      by linarith [Real.pi_gt_three], Set.empty_subset _⟩
  · -- the extreme value theorem for the two coordinates on the compact set `K`
    obtain ⟨p₁, hp₁K, hmin₁⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
    obtain ⟨p₂, hp₂K, hmax₁⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
    obtain ⟨q₁, hq₁K, hmin₂⟩ := hK.exists_isMinOn hne continuous_snd.continuousOn
    obtain ⟨q₂, hq₂K, hmax₂⟩ := hK.exists_isMaxOn hne continuous_snd.continuousOn
    have hpp : p₁.1 ≤ p₂.1 := (isMinOn_iff.mp hmin₁) p₂ hp₂K
    have hqq : q₁.2 ≤ q₂.2 := (isMinOn_iff.mp hmin₂) q₂ hq₂K
    have hp₁ : 0 < p₁.1 := (hsub hp₁K).1
    have hq₁ : 0 < q₁.2 := (hsub hq₁K).2.1
    have hq₂ : q₂.2 < π / 2 := (hsub hq₂K).2.2
    refine ⟨p₁.1 / 2, p₂.1 + 1, q₁.2 / 2, (q₂.2 + π / 2) / 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · linarith [Real.pi_pos]
    · linarith
    · intro p hpK
      have h1 : p₁.1 / 2 < p.1 := by
        have h := (isMinOn_iff.mp hmin₁) p hpK
        linarith
      have h2 : p.1 < p₂.1 + 1 := by
        have h := (isMaxOn_iff.mp hmax₁) p hpK
        linarith
      have h3 : q₁.2 / 2 < p.2 := by
        have h := (isMinOn_iff.mp hmin₂) p hpK
        linarith
      have h4 : p.2 < (q₂.2 + π / 2) / 2 := by
        have h := (isMaxOn_iff.mp hmax₂) p hpK
        linarith
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

theorem box_of_compactSupport {ψ : ℝ → ℝ → ℝ}
    (hc : HasCompactSupport (Function.uncurry ψ))
    (hs : tsupport (Function.uncurry ψ) ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ a b c d : ℝ, 0 < a ∧ a < b ∧ 0 < c ∧ c < d ∧ d < π / 2 ∧
      ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → ψ p.1 p.2 = 0 := by
  obtain ⟨a, b, c, d, ha, hab, hcc, hcd, hd, hbox⟩ :=
    exists_box_of_isCompact_subset_Q0 hc.isCompact hs
  refine ⟨a, b, c, d, ha, hab, hcc, hcd, hd, fun p hp => ?_⟩
  -- the box contains the support of `ψ`, hence `ψ` vanishes outside it
  change Function.uncurry ψ p = 0
  exact image_eq_zero_of_notMem_tsupport fun h => hp (hbox h)

end Work.EllipticEst.ModalSolution
end
-- ===== merged: Submission.Work.FTS.ClassC.zTail_lintegral_le_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- **The ENNReal `D_z`-slot estimate in the open-quadrant smoothness class, for an arbitrary
order `k`.**  For `g` of class `C^∞` on the open quadrant and `HkMem α k g`, and for any
`i ≤ k`,

  `∫⁻_θ ∫⁻_s ofReal (D_z^i g(s,θ)² · w(s)²) ≤ ofReal (HkSq α k g)`.

This is `Work.Spaces.Slots.lintegral_DzIter_le_HkSq_of_smooth` (which asks for the stronger
`SmoothNbhd`, i.e. smoothness on a neighbourhood of the *closed* quadrant, and is stated for
`k = 4`) with `SmoothNbhd` relaxed to `SmoothOpen` and `k` arbitrary: the only place where the
smoothness is used is the a.e. strong measurability of the uncurried integrand, which holds for
merely continuous (indeed `SmoothOpen`) data, cf. `Work.Spaces.aesm_of_continuousOn_Qd`. -/
theorem lintegral_DzIter_le_HkSq_open {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g)
    (i : ℕ) (hi : i ≤ k) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
        MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α k g) := by
  -- Continuity of the (uncurried) integrand on the open quadrant.
  have hcontW : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
          = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
      rw [hfun]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => ?_)
      exact pow_ne_zero 2 (ne_of_gt hp.1)
    exact h1.pow 2
  have hcontF : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.DzIter i g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (((Work.FTS.EllipticEst.SmoothOpen.DzIter hso i).continuousOn).pow 2).mul hcontW
  -- A.e. strong measurability of the integrand for the product of the restricted measures.
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.DzIter i g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcontF
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
      ((Work.Spaces.DzIter i g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    haesm.aemeasurable.ennreal_ofReal
  -- Tonelli: exchange the two `∫⁻`.
  have hswap : MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
        MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
        MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2))) :=
    MeasureTheory.lintegral_lintegral_swap hmeas
  -- Pointwise comparison with the `H^k`-integrand on the open angular interval.
  have hpt : ∀ s θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        ≤ Work.Spaces.HkIntegrand α k g s θ := by
    intro s θ h0 h1
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Work.Spaces.Slots.one_le_sin_two_rpow_neg_eta h0 h1
    have hkey := Work.Spaces.sq_le_HkIntegrand_z α k g s θ i hi
    have heq : (Work.Spaces.DzIter i g s θ
        * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
      have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
        norm_num
      rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
      ring
    calc (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        = (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left hone (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (Work.Spaces.DzIter i g s θ
            * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := heq.symm
      _ ≤ Work.Spaces.HkIntegrand α k g s θ := hkey
  -- The slicewise comparison (a.e. in `θ`, then `ofReal` of the honest angular integral).
  have hstep : ∀ s ∈ Work.Spaces.Iz,
      MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2))
        ≤ ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ) := by
    intro s hs
    calc MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2))
        ≤ MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k g s θ)) :=
          MeasureTheory.lintegral_mono_ae (Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo
            (fun θ h0 h1 => ENNReal.ofReal_le_ofReal (hpt s θ h0 h1)))
      _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 s hs)
            (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g s θ)).symm
  -- The marginal `∫⁻` is `ofReal` of `HkSq`.
  have hfinal : MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ))
      = ENNReal.ofReal (Work.Spaces.HkSq α k g) := by
    rw [Work.Spaces.HkSq]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
      (Eventually.of_forall fun s =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g s θ)).symm
  calc MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
        MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
        MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
          ENNReal.ofReal ((Work.Spaces.DzIter i g s θ) ^ 2 * (Work.Spaces.w s) ^ 2))) :=
        hswap.symm
    _ ≤ MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ)) :=
        MeasureTheory.lintegral_mono_ae
          (MeasureTheory.ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iz
            from measurableSet_Ici) hstep)
    _ = ENNReal.ofReal (Work.Spaces.HkSq α k g) := hfinal

/-- **The `θ`-integral of the radial tail of `g` is bounded by the squared `H^k`-norm.**
For `g` of class `C^∞` on the open quadrant with `HkMem α k g` (`1 ≤ k`),

`∫⁻_θ zTail g θ = ∫⁻_θ ∫⁻_s ofReal (D_z g(s,θ)² w(s)²) ≤ ofReal (HkSq α k g)`. -/
theorem zTail_lintegral_le_HkSq {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g) (hk : 1 ≤ k) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (fun θ => Work.FTS.ClassC.zTail g θ)
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α k g) := by
  have h := lintegral_DzIter_le_HkSq_open (g := g) hso hmem 1 hk
  simpa [Work.FTS.ClassC.zTail] using h

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.CmpSupp.src_int_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.CmpSupp


end Work.FTS.ClassCHon.CmpSupp
end
-- ===== merged: Submission.Work.FTS.ClassCHon.SliceMassAux.slice_sq_ftc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.ClassCHon.SliceMassAux

theorem slice_sq_ftc {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z₁ z₂ θ : ℝ} (hz₁ : 0 < z₁) (hz₁₂ : z₁ ≤ z₂) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (F z₂ θ) ^ 2 - (F z₁ θ) ^ 2
      = ∫ s in z₁..z₂, 2 * F s θ * Work.Spaces.pz F s θ := by
  -- The interval of integration lies in the interior of the positive half-line.
  have hsub : Set.uIcc z₁ z₂ ⊆ Set.Ioi (0 : ℝ) := by
    intro s hs
    rw [Set.uIcc_of_le hz₁₂] at hs
    exact lt_of_lt_of_le hz₁ hs.1
  -- The integrand is continuous there (it is a product of `C^∞` slices of `F` and `pz F`).
  have hcont : ContinuousOn (fun s => 2 * F s θ * Work.Spaces.pz F s θ) (Set.uIcc z₁ z₂) :=
    ((continuousOn_const.mul (hF.curry_z hθ).continuousOn).mul
      (hF.pz.curry_z hθ).continuousOn).mono hsub
  have hint : IntervalIntegrable (fun s => 2 * F s θ * Work.Spaces.pz F s θ)
      MeasureTheory.volume z₁ z₂ :=
    hcont.intervalIntegrable
  -- Pointwise: the derivative of the squared slice is `2 F · ∂_z F`.
  have hderiv : ∀ s ∈ Set.uIcc z₁ z₂,
      HasDerivAt (fun s' : ℝ => (F s' θ) ^ 2) (2 * F s θ * Work.Spaces.pz F s θ) s := by
    intro s hs
    have hs0 : 0 < s := hsub hs
    have h := (hF.hasDerivAt_slice hθ hs0).pow 2
    convert h using 1
    ring
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint).symm

end Work.FTS.ClassCHon.SliceMassAux
end
-- ===== merged: Submission.Work.FTS.ClassCHon.SliceMassUpgrade.ofReal_sliceMass_pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory

namespace Work.FTS.ClassCHon.SliceMassUpgrade

set_option linter.style.haveILetI false in
/-- The Cauchy–Schwarz inequality `(∫_{z₁}^{z₂} g)² ≤ (z₂ - z₁) ∫_{z₁}^{z₂} g²` for a function
`g` continuous on the compact interval `[z₁,z₂]` with `z₁ ≤ z₂`. -/
theorem interval_integral_sq_le_measure_mul {g : ℝ → ℝ} {z₁ z₂ : ℝ} (hz₁₂ : z₁ ≤ z₂)
    (hg : ContinuousOn g (Set.Icc z₁ z₂)) :
    (∫ s in z₁..z₂, g s) ^ 2 ≤ (z₂ - z₁) * ∫ s in z₁..z₂, (g s) ^ 2 := by
  have hAESM : AEStronglyMeasurable g (volume.restrict (Set.Ioc z₁ z₂)) :=
    (hg.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hIntSq : Integrable (fun s : ℝ => (g s) ^ 2) (volume.restrict (Set.Ioc z₁ z₂)) :=
    ((hg.pow 2).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hu : MemLp g 2 (volume.restrict (Set.Ioc z₁ z₂)) :=
    (memLp_two_iff_integrable_sq hAESM).mpr hIntSq
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc z₁ z₂)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top⟩
  have hv : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc z₁ z₂)) :=
    MemLp.of_bound measurable_const.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun _ => by simp))
  have hcs := Work.Spaces.cs_integral hu hv
  have hIocI : (∫ x in Set.Ioc z₁ z₂, g x * 1) = ∫ s in z₁..z₂, g s := by
    rw [intervalIntegral.integral_of_le hz₁₂]
    simp only [mul_one]
  have hIocJ : (∫ x in Set.Ioc z₁ z₂, (g x) ^ 2) = ∫ s in z₁..z₂, (g s) ^ 2 := by
    rw [intervalIntegral.integral_of_le hz₁₂]
  have hIoc1 : (∫ x in Set.Ioc z₁ z₂, (1 : ℝ) ^ 2) = z₂ - z₁ := by
    have h : (∫ x in Set.Ioc z₁ z₂, (1 : ℝ)) = z₂ - z₁ := by
      rw [← intervalIntegral.integral_of_le hz₁₂, intervalIntegral.integral_const]
      simp
    simpa using h
  rw [hIocI, hIocJ, hIoc1] at hcs
  linarith [hcs]


end Work.FTS.ClassCHon.SliceMassUpgrade
end
-- ===== merged: Submission.Work.FTS.ClassCHon.SliceMassUpgrade.sliceMass_dz_comparison_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped ENNReal Real

namespace Work.FTS.ClassCHon.SliceMassUpgrade

/-- The same comparison as `sliceMass_dz_comparison`, with an arbitrary weight `τ`
in place of `sEta`.  The only property of the weight that is used is that it is the
*same* function in both integrands: the right-hand integrand is `s²` times the
left-hand one, and `(z₁²)⁻¹ · s² ≥ 1` since `0 < z₁ ≤ s`. -/
theorem sliceMass_dz_comparison_gen {F : ℝ → ℝ → ℝ} {τ : ℝ → ℝ} {z₁ s : ℝ}
    (hz₁ : 0 < z₁) (hz₁s : z₁ ≤ s) :
    (∫⁻ θ in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
      ≤ (ENNReal.ofReal (z₁ ^ 2))⁻¹
        * ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2) := by
  set A : ENNReal := ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
        ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2) with hA
  have hInt : (∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2))
      = ENNReal.ofReal (s ^ 2) * A := by
    rw [show (∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2))
        = ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2) from
        MeasureTheory.lintegral_congr (fun θ => by
          rw [show τ θ * (s * Work.Spaces.pz F s θ) ^ 2
              = s ^ 2 * (τ θ * (Work.Spaces.pz F s θ) ^ 2) from by ring]
          exact ENNReal.ofReal_mul (by positivity))]
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hInt, ← mul_assoc]
  have h1 : (1 : ENNReal) ≤ (ENNReal.ofReal (z₁ ^ 2))⁻¹ * ENNReal.ofReal (s ^ 2) := by
    have hz1sq_pos : (0 : ℝ) < z₁ ^ 2 := by positivity
    have hsge : z₁ ^ 2 ≤ s ^ 2 := by nlinarith
    have hreal : (1 : ℝ) ≤ (z₁ ^ 2)⁻¹ * s ^ 2 := by
      calc (1 : ℝ) = (z₁ ^ 2)⁻¹ * z₁ ^ 2 := (inv_mul_cancel₀ (by positivity : z₁ ^ 2 ≠ 0)).symm
        _ ≤ (z₁ ^ 2)⁻¹ * s ^ 2 := mul_le_mul_of_nonneg_left hsge (by positivity)
    rw [← ENNReal.ofReal_inv_of_pos hz1sq_pos]
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (z₁ ^ 2)⁻¹)]
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal hreal
  exact le_mul_of_one_le_left' h1

end Work.FTS.ClassCHon.SliceMassUpgrade
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.HkMemAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-- **Membership in `ℋ^k` by an almost-everywhere majorant.**

If the integrand `HkIntegrand α k f` is continuous on the open quadrant, if a majorant `M`
has integrable angular slices and an integrable angular integral, and if the domination
`HkIntegrand α k f z θ ≤ M z θ` holds for every `z ∈ Iz` and almost every `θ ∈ (0, π/2)`, then
`f ∈ ℋ^k`.  (The closed-quadrant version `Work.FTS.LocData.HkMem_of_majorant` requires the
domination at *every* point of `Iz ×ˢ Iθ`; here only the interior angles are needed, which is
what the additivity of the `D`-operators on the open quadrant delivers.) -/
theorem HkMem_of_majorant_ae (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      Work.FTS.EllipticEst.Q0)
    (hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Set.Icc 0 (π / 2) := MeasureTheory.Ioo_ae_eq_Icc
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iθ := by
    intro z hz
    show IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) (Set.Icc 0 (π / 2))
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
      exact (Work.FTS.LocData.HkIntegrand_zero_fst α k f θ).symm
    · refine MeasureTheory.IntegrableOn.congr_set_ae ?_ hIoo.symm
      have hMioo : IntegrableOn (fun θ => M z θ) (Set.Ioo 0 (π / 2)) :=
        (hMslice z hz).congr_set_ae hIoo
      have hsl : ContinuousOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
          (Set.Ioo 0 (π / 2)) :=
        Work.FTS.LocData.continuousOn_slice_theta (G := Work.Spaces.HkIntegrand α k f)
          hcont hz0
      refine MeasureTheory.Integrable.mono' hMioo
        (hsl.aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [hle z hz] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
      exact hθ
  have houter : IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := by
    have hKnn : ∀ z ∈ Work.Spaces.Iz,
        0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
    have hKle : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
      intro z hz
      have hIθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (π / 2) := by
        show Set.Icc (0 : ℝ) (π / 2) =ᵐ[volume] Set.Ioo 0 (π / 2)
        exact hIoo.symm
      rw [MeasureTheory.setIntegral_congr_set hIθ,
        MeasureTheory.setIntegral_congr_set hIθ]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
        ((hMslice z hz).congr_set_ae hIoo) ?_
      filter_upwards [hle z hz] with θ hθ
      exact hθ
    refine MeasureTheory.Integrable.mono' hMz ?_ ?_
    · have hprod : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact hcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      have h1 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict (Set.Ioi 0)) :=
        hprod.integral_prod_right'
      have h2 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict Work.Spaces.Iz) := by
        rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
        exact h1
      have hfun : (fun z => ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.HkIntegrand α k f z θ)
          = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
        funext z
        exact MeasureTheory.setIntegral_congr_set hIoo
      rw [← hfun]
      exact h2
    · have hbnd : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
          ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ‖
            ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
        exact Filter.Eventually.of_forall fun z hz => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hKnn z hz)]
          exact hKle z hz
      exact hbnd
  exact ⟨hslice, houter⟩

end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.pzSqSeta_box_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∂_z f · sin(2θ)^{-η/2}` is `L²` on every compact `z`-box

The `θ`-weighted `L²`-mass of the plain `z`-derivative `∂_z f` over a compact box
`z ∈ [a,b]` (`0 < a`) is finite for `f ∈ SmoothQuad ∩ ℋ⁴`:

  `IntegrableOn (fun (s,θ) => (∂_z f s θ)² · sin(2θ)^{-η}) ([a,b] × [0,π/2])`.

The point of the box is the radial weight `w(z) = (1+z)²/z²`: on `[a,b]` it is bounded
below (`1 ≤ (b²/(1+a)⁴)·z²w(z)²`), so the boxed `∂_z`-slot is dominated by the first
`D_z`-slot term `(D_z f · w/sin(2θ)^{η/2})²` of the `ℋ⁴`-integrand
(`Pieces.pzSqSeta_le_Dz1_mul`), which is integrable because `HkMem α 4 f` gives the
iterated integrability of the whole `ℋ⁴`-integrand and `SmoothQuad` its a.e. strong
measurability on the product measure (`Work.Spaces.integrable_prod_of_iterated`).
-/

namespace Work.FTS.CoercivityFix.Coer1T.Hardy

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The open quadrant `(0,∞) × (0,π/2)` and continuity of the two integrands -/

/-- The open quadrant `(0,∞) × (0,π/2)`, on which both weights `w` and `sin(2θ)^{-c}`
are honest continuous functions. -/
private def QdPos : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)

private lemma QdPos_subset_quadU : QdPos ⊆ Work.Spaces.quadU := by
  intro p hp
  rw [QdPos, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
  rw [Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨by linarith [hp.1], hp.2⟩

private lemma sin_two_pos_of_mem_QdPos {p : ℝ × ℝ} (hp : p ∈ QdPos) :
    0 < Real.sin (2 * p.2) := by
  rw [QdPos, Set.mem_prod, Set.mem_Ioo] at hp
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
    (by linarith [hp.2.2, Real.pi_pos])

/-- `θ ↦ sin(2θ)^c` is continuous on the open quadrant (where `sin(2θ) ≠ 0`). -/
private lemma continuousOn_sin_rpow_QdPos (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) QdPos :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_of_mem_QdPos hp)))

/-- The radial weight `w` is continuous on the open quadrant. -/
private lemma continuousOn_w_QdPos :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) QdPos := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  rw [QdPos, Set.mem_prod, Set.mem_Ioi] at hp
  exact pow_ne_zero 2 (ne_of_gt hp.1)

/-- `D_z f` is continuous on the open quadrant for `SmoothQuad f`. -/
private lemma continuousOn_Dz_QdPos {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter 1 f p.1 p.2) QdPos :=
  ((Work.FTS.LocData.contDiffOn_DzIter (V := Work.Spaces.quadU) Work.Spaces.isOpen_quadU
    hsm 1).continuousOn).mono QdPos_subset_quadU

/-- The `D_z`-slot integrand `(D_z f · w/sin(2θ)^{η/2})²` of the `ℋ⁴`-integrand is
continuous on the open quadrant. -/
private lemma continuousOn_Dz1slot_QdPos {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter 1 f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)) QdPos := by
  have hDz := continuousOn_Dz_QdPos hsm
  have hw : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) QdPos :=
    continuousOn_w_QdPos.div (continuousOn_sin_rpow_QdPos _)
      (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_QdPos hp) _))
  show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.1 p.2
    * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) QdPos
  exact (hDz.mul hw).pow 2


/-! ## Integrability of the `D_z`-slot on the product measure -/

/-- The `ℋ⁴`-integrand of a `SmoothQuad` function is integrable for the product of the two
restricted Lebesgue measures: `HkMem` supplies the iterated integrability and `SmoothQuad`
the a.e. strong measurability on the product (`Work.Spaces.integrable_prod_of_iterated`). -/
private lemma integrable_HkIntegrand_prod (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hAESM : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    show MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 f hsm)
  refine (Work.Spaces.integrable_prod_of_iterated
    (G := fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ) hAESM ?_ ?_).1
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hmem.1
  · exact hmem.2

/-- The first `D_z`-slot of the `ℋ⁴`-integrand is integrable for the product measure. -/
private lemma integrable_Dz1slot_prod (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter 1 f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hHint := integrable_HkIntegrand_prod α hsm hmem
  refine MeasureTheory.Integrable.mono' hHint ?_ ?_
  · exact Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_Dz1slot_QdPos hsm)
  · filter_upwards with p
    show ‖(Work.Spaces.DzIter 1 f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2‖
      ≤ Work.Spaces.HkIntegrand α 4 f p.1 p.2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_z α 4 f p.1 p.2 1 (by norm_num)

/-! ## The statement -/


end

end Work.FTS.CoercivityFix.Coer1T.Hardy
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Norm.HkReg_closure =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

/-! ## The smoothness half: `SmoothNbhd` is closed under the vector-space operations

`SmoothNbhd f` is `ContDiffOn ℝ ⊤ (Function.uncurry f) nbhU`, and `Function.uncurry`
commutes with `+`, `-` and scalar multiplication definitionally, so these are the
corresponding `ContDiffOn` closure lemmas. -/




/-! ## The `ℋ^k` half: negation and subtraction

`HkIntegrand α k (-f) = HkIntegrand α k f` holds unconditionally (the totalised `deriv`
is odd), so negation is the scalar case `c = -1` up to the identification
`(-1) * f z θ = -f z θ`. -/

/-- `ℋ^k` is closed under negation. -/
theorem HkMem_neg (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hmf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => -f z θ) := by
  have h := HkMem_const_mul α k (-1) hf hmf
  have hfun : (fun z θ : ℝ => (-1 : ℝ) * f z θ) = (fun z θ : ℝ => -f z θ) := by
    funext z θ
    exact neg_one_mul (f z θ)
  rwa [hfun] at h


/-! ## The closure of `HkReg` -/






end Work.FTS.CoercivityStep.Norm
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The honest elliptic solution class** of the Galerkin chapter (design §1 (b)).

`EllClassO α g Ψ` says: `Ψ` solves the elliptic problem with source `g` on the open quadrant
(with the Dirichlet data and the decay), `Ψ` is `C^∞` on the open quadrant, and the shifted
unknown `Ψ + Gsing α g · sin 2θ` is a datum of the weak hypothesis class of the `ℋ^4`
elliptic estimate, with the orthogonalised source `orthSource g`.

This is the definition of `Submission/Work/FTS/FTS_ELL_GALERKIN_STMTS.lean` (namespace
`Work.FTS.ScratchC46`), copied verbatim into the namespace of the area. -/
def EllClassO (α : ℝ) (g Ψ : Fn) : Prop :=
  Work.Elliptic.IsBslSol α g Ψ ∧ Work.FTS.EllipticEst.SmoothOpen Ψ ∧
  Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
    (fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ))

/-- **The shifted unknown** `Ψ ↦ Ψ + Gsing α g · sin 2θ` of §'The singular term'.

`shiftSing α g Ψ` is the quantity that the `ℋ^k` estimates of the paper are applied to: it is
`Ψ` plus the radial multiple of `sin 2θ` that removes the non-orthogonal part of the source.  It
is the third component of `EllClassO`. -/
def shiftSing (α : ℝ) (g Ψ : Fn) : Fn :=
  fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)

@[simp] theorem shiftSing_apply (α : ℝ) (g Ψ : Fn) (z θ : ℝ) :
    shiftSing α g Ψ z θ = Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ) := rfl

/-- `shiftSing α g` is (definitionally) the function written out in `EllClassO`. -/
theorem shiftSing_eq (α : ℝ) (g Ψ : Fn) :
    shiftSing α g Ψ = fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ) := rfl

/-- The second component of `EllClassO`. -/
theorem EllClassO.smoothOpen {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.FTS.EllipticEst.SmoothOpen Ψ := h.2.1



/-- The equation clause of an `EllClassO` element, on the open quadrant. -/
theorem EllClassO.eq {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = g z θ :=
  h.1.1

/-- The two Dirichlet values of an `EllClassO` element. -/
theorem EllClassO.vanish {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.Spaces.VanishTheta Ψ := ⟨h.1.2.1, h.1.2.2.1⟩

/-- The decay clause of an `EllClassO` element. -/
theorem EllClassO.decay {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (𝓝 0) := h.1.2.2.2


end Work.FTS.EllExist
end
end
-- ===== merged: Submission.Work.FTS.EllExist.SmoothOpenSep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist

set_option autoImplicit false

/-- A radial factor `C^n` on `(0,∞)` for every `n` times a `C^∞` angular factor is `C^∞` on the
open quadrant. -/
theorem sep_mul_open {g χ : ℝ → ℝ} (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0))
    (hχ : ContDiff ℝ ⊤ χ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => g z * χ θ) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
  intro n
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => g p.1)
      Work.FTS.EllipticEst.Q0 :=
    (hg n).comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have h2 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => χ p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hχn : ContDiff ℝ (n : WithTop ℕ∞) χ := hχ.of_le le_top
    exact hχn.contDiffOn.comp contDiffOn_snd fun p _ => Set.mem_univ p.2
  have hfun : Function.uncurry (fun z θ => g z * χ θ)
      = fun p : ℝ × ℝ => g p.1 * χ p.2 := rfl
  rw [hfun]
  exact h1.mul h2

/-- `SmoothOpen` is closed under multiplication by a constant. -/
theorem const_mul_open (c : ℝ) {F : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * F z θ) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall] at h ⊢
  intro n
  have hfun : Function.uncurry (fun z θ => c * F z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry F p := rfl
  rw [hfun]
  exact (contDiffOn_const (c := c)).mul (h n)

end Work.FTS.EllExist
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.aeStronglyMeasurable_exp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

/-- The half-strip `ℝ × (0, π/2)` is of full measure for the product measure
`volume.prod (volume.restrict Iθ)`: inside `Iθ = [0, π/2]` the complement of `(0, π/2)` consists
of the two endpoints `0`, `π/2`, which are null. -/
theorem ae_mem_halfStrip :
    ∀ᵐ (p : ℝ × ℝ) ∂(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      p ∈ ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
  have hIθ : (MeasureTheory.volume.restrict Work.Spaces.Iθ : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    show (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (π / 2)) : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))
    exact (MeasureTheory.restrict_Ioo_eq_restrict_Icc (μ := MeasureTheory.volume)
      (a := (0 : ℝ)) (b := π / 2)).symm
  rw [MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
    (MeasurableSet.univ.prod (measurableSet_Ioo (a := (0 : ℝ)) (b := π / 2)))]
  filter_upwards with x
  rw [hIθ]
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioo (a := (0 : ℝ)) (b := π / 2))]
    with y hy
  exact ⟨trivial, hy⟩

theorem aeStronglyMeasurable_exp {X : ℝ → ℝ → ℝ}
    (hX : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the (measurable, co-null) half-strip on which the datum is continuous
  have hmeasS : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasurableSet.univ.prod (measurableSet_Ioo (a := (0 : ℝ)) (b := π / 2))
  -- on that half-strip the datum is continuous: the map `p ↦ (exp p.1, p.2)` is continuous and
  -- sends the half-strip into the open quadrant `Q0` on which `X` is continuous
  have hcont : ContinuousOn (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
    have hφ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
      (Real.continuous_exp.comp continuous_fst).prodMk continuous_snd
    have h : ContinuousOn ((Function.uncurry X) ∘ (fun p : ℝ × ℝ => (Real.exp p.1, p.2)))
        ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
      hX.comp hφ.continuousOn (fun p hp => ⟨Real.exp_pos p.1, (Set.mem_prod.mp hp).2⟩)
    exact h
  rw [← MeasureTheory.Measure.restrict_eq_self_of_ae_mem ae_mem_halfStrip]
  exact hcont.aestronglyMeasurable hmeasS

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.SliceAux =====
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

set_option autoImplicit false

/-- **The `θ`-derivative of the slice of `D_zG`.**  For `G` smooth on the open quadrant, `z > 0`
and `θ ∈ (0,π/2)`, the derivative of `θ' ↦ D_zG z θ'` at `θ` is `D_z(∂_θG) z θ`. -/
theorem deriv_slice_Dz {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => Work.Spaces.Dz G z θ') θ = Work.Spaces.Dz (Work.Spaces.pth G) z θ := by
  have hcd : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ) :=
    (hG.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ⟩))).of_le (by norm_num)
  have h1 : Work.Spaces.pth (Work.Spaces.pz G) z θ = Work.Spaces.pz (Work.Spaces.pth G) z θ :=
    (Work.Spaces.pz_pth_comm (f := G) hcd).symm
  calc deriv (fun θ' => Work.Spaces.Dz G z θ') θ
      = deriv (fun θ' => z * Work.Spaces.pz G z θ') θ := rfl
    _ = z * deriv (fun θ' => Work.Spaces.pz G z θ') θ := by rw [deriv_const_mul_field]
    _ = z * Work.Spaces.pth (Work.Spaces.pz G) z θ := rfl
    _ = z * Work.Spaces.pz (Work.Spaces.pth G) z θ := by rw [h1]
    _ = Work.Spaces.Dz (Work.Spaces.pth G) z θ := rfl

/-- **The second `θ`-derivative of the slice of `D_zG`.**  For `G` smooth on the open quadrant,
`z > 0` and `θ ∈ (0,π/2)`, the second derivative of `θ' ↦ D_zG z θ'` at `θ` is `D_z(∂_θ²G) z θ`. -/
theorem deriv_deriv_slice_Dz {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ
      = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ := by
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hev : (fun θ'' => deriv (fun θ' => Work.Spaces.Dz G z θ') θ'')
      =ᶠ[𝓝 θ] (fun θ'' => Work.Spaces.Dz (Work.Spaces.pth G) z θ'') := by
    filter_upwards [hmem] with θ'' hθ''
    exact deriv_slice_Dz hG hz hθ''
  have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth G)) (z, θ) :=
    ((hG.pth).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ⟩))).of_le (by norm_num)
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth G)) z θ
      = Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth G)) z θ :=
    (Work.Spaces.pz_pth_comm (f := Work.Spaces.pth G) hcd).symm
  calc deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ
      = deriv (fun θ'' => Work.Spaces.Dz (Work.Spaces.pth G) z θ'') θ := hev.deriv_eq
    _ = deriv (fun θ'' => z * Work.Spaces.pz (Work.Spaces.pth G) z θ'') θ := rfl
    _ = z * deriv (fun θ'' => Work.Spaces.pz (Work.Spaces.pth G) z θ'') θ := by
        rw [deriv_const_mul_field]
    _ = z * Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth G)) z θ := rfl
    _ = z * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth G)) z θ := by rw [h2]
    _ = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ := rfl


end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeS1.l2Dictionary =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeS1

/-- **The `L²`-dictionary**: for a function `f` whose weighted square `(f · w)²` is
a.e.-strongly-measurable for the product measure on `Iz × Iθ`, whose every angular fibre
`θ ↦ (f z θ · w z)²` is integrable on `Iθ`, and whose `∫⁻`-integral
`∫⁻_z ofReal(w z²) · (∫⁻_θ ofReal(f z θ²))` is finite, the iterated Bochner integral
`L2Sq (f · w)` is honest (`L2Mem`) and equals the `toReal` of that `∫⁻`-integral. -/
theorem l2Dictionary {f : ℝ → ℝ → ℝ}
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => (f z θ * Work.Spaces.w z) ^ 2) Work.Spaces.Iθ)
    (hfin : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2))) ≠ ⊤) :
    Work.Spaces.L2Mem (fun z θ => f z θ * Work.Spaces.w z) ∧
    Work.Spaces.L2Sq (fun z θ => f z θ * Work.Spaces.w z)
      = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2))).toReal := by
  -- ## the a.e. pointwise identity
  have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)
        = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2)) := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    have hne : ∀ᵐ z ∂(MeasureTheory.volume : Measure ℝ), z ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with z hz hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz)
    have hwz : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
    have hint : MeasureTheory.Integrable (fun θ => (f z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h1 : MeasureTheory.Integrable (fun θ => (f z θ * Work.Spaces.w z) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hsl z hzI
      refine (h1.div_const ((Work.Spaces.w z) ^ 2)).congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
      field_simp
    have hval : (∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)
        = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 := by
      rw [show (∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)
            = ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 from
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)]
      rw [MeasureTheory.integral_mul_const]
      ring
    rw [hval, ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
    congr 1
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
  -- ## the lintegral identity
  have hLint : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2)) :=
    MeasureTheory.lintegral_congr_ae hpt
  have hΦne : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)) ≠ ⊤ := by
    rw [hLint]; exact hfin
  -- ## measurability of the outer integrand
  have hmsl : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h' := hmeas.integral_prod_right'
    simpa using h'
  -- ## the two conclusions
  have hIntOuter : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmsl
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _)).mp hΦne
  have hL2 : Work.Spaces.L2Sq (fun z θ => f z θ * Work.Spaces.w z)
      = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2))).toReal := by
    rw [Work.Spaces.L2Sq, ← hLint]
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hmsl
  exact ⟨⟨hsl, hIntOuter⟩, hL2⟩

end Work.FTS.EllipticEst.AeS1
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.TermAgmon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open MeasureTheory Set Filter

set_option autoImplicit false

private theorem ennreal_factor_swap (c c0 A : ENNReal) : c * (c0 * A) = c0 * (c * A) := by
  ring

private theorem ennreal_factor_common (c c0 c4 A B : ENNReal) :
    c * (c0 * (c4 * A + B)) = c0 * (c4 * (c * A) + c * B) := by
  ring

/-- Pulling the angular factor `ofReal (wth θ ^ 2)` inside a `z`-`lintegral`. -/
private theorem ofReal_sq_mul_lintegral (wth : ℝ → ℝ) (θ : ℝ) (Y : ℝ → ℝ) :
    ENNReal.ofReal (wth θ ^ 2) *
        MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (fun z => ENNReal.ofReal (Y z))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (fun z => ENNReal.ofReal (wth θ ^ 2 * Y z)) := by
  rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (wth θ ^ 2)) _
    ENNReal.ofReal_ne_top]
  exact MeasureTheory.lintegral_congr
    (fun z => (ENNReal.ofReal_mul (sq_nonneg (wth θ))).symm)

/-- The radial weight `w` is continuous on the open quadrant. -/
private theorem continuousOn_w_fst :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1)

/-! ## Step 1: the pointwise-in-`θ` inequality -/

private theorem pointwise (C1 α : ℝ) (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ)
    (hgen : ∀ (β : ℝ) (h : ℝ → ℝ), 0 < β → β ≤ 1 →
      ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ)) →
      ENNReal.ofReal (β ^ 2) *
          MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (β ^ 4) *
                MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal
                    ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))
              + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2))))
    (hα : 0 < α) (hα1 : α ≤ 1) (hV : SmoothOpen V) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ENNReal.ofReal (α ^ 2) *
        MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (fun z => ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) *
              MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                (fun z => ENNReal.ofReal
                  ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                (fun z => ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))) := by
  have h := hgen α (fun z' => V z' θ) hα hα1 (hV.curry_z hθ)
  -- the three rewriting identities, pulling `ofReal (wth θ ^ 2)` inside
  have hL : ENNReal.ofReal (wth θ ^ 2) *
      MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal
          ((Work.Spaces.w z) ^ 2 * (z * deriv (fun z' => V z' θ) z) ^ 2))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2)) := by
    rw [ofReal_sq_mul_lintegral]
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    congr 1
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    ring
  have hA : ENNReal.ofReal (wth θ ^ 2) *
      MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal
          ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv (fun z' => V z' θ)) z) ^ 2))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal
          ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2)) := by
    rw [ofReal_sq_mul_lintegral]
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    congr 1
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
    ring
  have hB : ENNReal.ofReal (wth θ ^ 2) *
      MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)) := by
    rw [ofReal_sq_mul_lintegral]
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    congr 1
    ring
  have hmul : ENNReal.ofReal (wth θ ^ 2) * (ENNReal.ofReal (α ^ 2) * MeasureTheory.lintegral
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal
          ((Work.Spaces.w z) ^ 2 * (z * deriv (fun z' => V z' θ) z) ^ 2)))
      ≤ ENNReal.ofReal (wth θ ^ 2) *
        (ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * MeasureTheory.lintegral
              (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (fun z => ENNReal.ofReal
                ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv (fun z' => V z' θ)) z) ^ 2))
            + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)))) :=
    mul_le_mul_of_nonneg_left h (zero_le : (0 : ENNReal) ≤ _)
  have hL'
      : ENNReal.ofReal (wth θ ^ 2) * (ENNReal.ofReal (α ^ 2) * MeasureTheory.lintegral
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (fun z => ENNReal.ofReal
            ((Work.Spaces.w z) ^ 2 * (z * deriv (fun z' => V z' θ) z) ^ 2)))
        = ENNReal.ofReal (α ^ 2) * MeasureTheory.lintegral
            (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (fun z => ENNReal.ofReal
              ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2)) := by
    rw [ennreal_factor_swap, hL]
  have hR' : ENNReal.ofReal (wth θ ^ 2) *
        (ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * MeasureTheory.lintegral
              (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (fun z => ENNReal.ofReal
                ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv (fun z' => V z' θ)) z) ^ 2))
            + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))))
      = ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * MeasureTheory.lintegral
              (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (fun z => ENNReal.ofReal
                ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (fun z => ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))) := by
    rw [ennreal_factor_common, hA, hB]
  rw [hL', hR'] at hmul
  exact hmul




/-- **Unconditional subadditivity of the Lebesgue integral with measurable cofactors.**
For arbitrary (possibly nonmeasurable) `f` and measurable `g, h`:
`∫⁻ f·(g+h) ≤ ∫⁻ f·g + ∫⁻ f·h`.  This is the direction of `le_lintegral_add` that is not
available unconditionally in Mathlib; the proof uses the characterisation of the integral as a
supremum over measurable functions below it, splitting such a `u` into `u₁ ≤ f·g` and `u₂ ≤ f·h`
by the ratio `g/(g+h)`, with the two cases `g = ⊤` and `g + h = ⊤` treated separately. -/
private theorem lintegral_mul_add_le_aux {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {f g h : α → ENNReal} (hg : Measurable g) (hh : Measurable h) :
    MeasureTheory.lintegral μ (fun a => f a * (g a + h a))
      ≤ MeasureTheory.lintegral μ (fun a => f a * g a)
        + MeasureTheory.lintegral μ (fun a => f a * h a) := by
  classical
  rw [← iSup_lintegral_measurable_le_eq_lintegral (μ := μ)
    (fun a => f a * (g a + h a))]
  refine iSup_le fun u => iSup_le fun hum => iSup_le fun hule => ?_
  let ratio : α → ENNReal := fun a => g a * (g a + h a)⁻¹
  let ratio2 : α → ENNReal := fun a => h a * (g a + h a)⁻¹
  let S : Set α := {a | g a = ⊤} ∩ {a | g a + h a = ⊤}
  let T : Set α := {a | g a ≠ ⊤} ∩ {a | g a + h a = ⊤}
  let u1 : α → ENNReal := fun a => u a * ratio a + S.indicator u a
  let u2 : α → ENNReal := fun a => u a * ratio2 a + T.indicator u a
  have hratio : Measurable ratio := hg.mul (hg.add hh).inv
  have hratio2 : Measurable ratio2 := hh.mul (hg.add hh).inv
  have hgTop : MeasurableSet {a : α | g a = ⊤} := hg (measurableSet_singleton ⊤)
  have hghTop : MeasurableSet {a : α | g a + h a = ⊤} :=
    (hg.add hh) (measurableSet_singleton ⊤)
  have hS : MeasurableSet S := hgTop.inter hghTop
  have hT : MeasurableSet T := hgTop.compl.inter hghTop
  have hu1m : Measurable u1 := (hum.mul hratio).add (hum.indicator hS)
  have hu2m : Measurable u2 := (hum.mul hratio2).add (hum.indicator hT)
  have hratio_top : ∀ a, g a = ⊤ → ratio a = 0 := by
    intro a ha
    have hsum_top : g a + h a = ⊤ := by rw [ha]; simp
    simp only [ratio, hsum_top, ENNReal.inv_top, mul_zero]
  have hratio_gh_top : ∀ a, g a + h a = ⊤ → ratio a = 0 := by
    intro a ha
    simp only [ratio, ha, ENNReal.inv_top, mul_zero]
  have hratio2_top : ∀ a, g a + h a = ⊤ → ratio2 a = 0 := by
    intro a ha
    simp only [ratio2, ha, ENNReal.inv_top, mul_zero]
  have hS_of : ∀ a, g a = ⊤ → a ∈ S := by
    intro a ha
    refine ⟨ha, ?_⟩
    simp only [Set.mem_ofPred_eq]
    rw [ha]
    simp
  have hS_not' : ∀ a, g a ≠ ⊤ → a ∉ S := fun a hne hmem => hne hmem.1
  have hS_not : ∀ a, g a + h a ≠ ⊤ → a ∉ S := fun a hne hmem => hne hmem.2
  have hT_of : ∀ a, g a ≠ ⊤ → g a + h a = ⊤ → a ∈ T := fun a h1 h2 => ⟨h1, h2⟩
  have hT_not : ∀ a, g a = ⊤ → a ∉ T := fun a htop hmem => hmem.1 htop
  have hT_not' : ∀ a, g a + h a ≠ ⊤ → a ∉ T := fun a hne hmem => hne hmem.2
  have hsum : ∀ a, u1 a + u2 a = u a := by
    intro a
    by_cases hg_top : g a = ⊤
    · have hgh_top : g a + h a = ⊤ := by rw [hg_top]; simp
      simp only [u1, u2, Set.indicator_of_mem (hS_of a hg_top) u,
        Set.indicator_of_notMem (hT_not a hg_top) u, hratio_top a hg_top,
        hratio2_top a hgh_top]
      ring
    · by_cases hgh_top : g a + h a = ⊤
      · simp only [u1, u2, Set.indicator_of_notMem (hS_not' a hg_top) u,
          Set.indicator_of_mem (hT_of a hg_top hgh_top) u, hratio_gh_top a hgh_top,
          hratio2_top a hgh_top]
        ring
      · have hS' : a ∉ S := hS_not a hgh_top
        have hT' : a ∉ T := hT_not' a hgh_top
        by_cases h0 : g a + h a = 0
        · have hu0 : u a = 0 := by
            have hle0 : u a ≤ f a * (g a + h a) := hule a
            rw [h0, mul_zero] at hle0
            exact le_antisymm hle0 bot_le
          simp only [u1, u2, Set.indicator_of_notMem hS' u,
            Set.indicator_of_notMem hT' u, hu0]
          simp
        · have hinv := ENNReal.mul_inv_cancel h0 hgh_top
          simp only [u1, u2, Set.indicator_of_notMem hS' u,
            Set.indicator_of_notMem hT' u, add_zero]
          simp only [ratio, ratio2]
          calc u a * (g a * (g a + h a)⁻¹) + u a * (h a * (g a + h a)⁻¹)
              = u a * ((g a + h a) * (g a + h a)⁻¹) := by ring
            _ = u a * 1 := by rw [hinv]
            _ = u a := mul_one _
  have hle1 : ∀ a, u1 a ≤ f a * g a := by
    intro a
    have hu_le : u a ≤ f a * (g a + h a) := hule a
    by_cases hg_top : g a = ⊤
    · have hgh_top : g a + h a = ⊤ := by rw [hg_top]; simp
      have hfg : f a * (g a + h a) = f a * g a := by rw [hgh_top, hg_top]
      simp only [u1, Set.indicator_of_mem (hS_of a hg_top) u, hratio_top a hg_top,
        mul_zero, zero_add]
      exact le_trans hu_le (le_of_eq hfg)
    · by_cases hgh_top : g a + h a = ⊤
      · simp only [u1, Set.indicator_of_notMem (hS_not' a hg_top) u, add_zero,
          hratio_gh_top a hgh_top, mul_zero]
        exact bot_le
      · have hS' : a ∉ S := hS_not a hgh_top
        simp only [u1, Set.indicator_of_notMem hS' u, add_zero]
        simp only [ratio]
        by_cases h0 : g a + h a = 0
        · have hg0 : g a = 0 := (add_eq_zero.mp h0).1
          have hL : u a * (g a * (g a + h a)⁻¹) = 0 := by
            rw [h0, ENNReal.inv_zero, hg0, zero_mul, mul_zero]
          have hR : f a * g a = 0 := by rw [hg0, mul_zero]
          rw [hL, hR]
        · have hinv := ENNReal.mul_inv_cancel h0 hgh_top
          calc u a * (g a * (g a + h a)⁻¹)
              ≤ (f a * (g a + h a)) * (g a * (g a + h a)⁻¹) :=
                mul_le_mul_of_nonneg_right hu_le bot_le
            _ = (f a * g a) * ((g a + h a) * (g a + h a)⁻¹) := by ring
            _ = (f a * g a) * 1 := by rw [hinv]
            _ = f a * g a := mul_one _
  have hle2 : ∀ a, u2 a ≤ f a * h a := by
    intro a
    have hu_le : u a ≤ f a * (g a + h a) := hule a
    by_cases hg_top : g a = ⊤
    · have hgh_top : g a + h a = ⊤ := by rw [hg_top]; simp
      simp only [u2, Set.indicator_of_notMem (hT_not a hg_top) u, add_zero,
        hratio2_top a hgh_top, mul_zero]
      exact bot_le
    · by_cases hgh_top : g a + h a = ⊤
      · have hh_top : h a = ⊤ := by
          rcases ENNReal.add_eq_top.mp hgh_top with h' | h'
          · exact absurd h' hg_top
          · exact h'
        have hfg : f a * (g a + h a) = f a * h a := by rw [hgh_top, hh_top]
        simp only [u2, Set.indicator_of_mem (hT_of a hg_top hgh_top) u,
          hratio2_top a hgh_top, mul_zero, zero_add]
        exact le_trans hu_le (le_of_eq hfg)
      · have hT' : a ∉ T := hT_not' a hgh_top
        simp only [u2, Set.indicator_of_notMem hT' u, add_zero]
        simp only [ratio2]
        by_cases h0 : g a + h a = 0
        · have hh0 : h a = 0 := (add_eq_zero.mp h0).2
          have hL : u a * (h a * (g a + h a)⁻¹) = 0 := by
            rw [h0, ENNReal.inv_zero, hh0, zero_mul, mul_zero]
          have hR : f a * h a = 0 := by rw [hh0, mul_zero]
          rw [hL, hR]
        · have hinv := ENNReal.mul_inv_cancel h0 hgh_top
          calc u a * (h a * (g a + h a)⁻¹)
              ≤ (f a * (g a + h a)) * (h a * (g a + h a)⁻¹) :=
                mul_le_mul_of_nonneg_right hu_le bot_le
            _ = (f a * h a) * ((g a + h a) * (g a + h a)⁻¹) := by ring
            _ = (f a * h a) * 1 := by rw [hinv]
            _ = f a * h a := mul_one _
  calc MeasureTheory.lintegral μ u
      = MeasureTheory.lintegral μ (fun a => u1 a + u2 a) :=
        MeasureTheory.lintegral_congr (fun a => (hsum a).symm)
    _ = MeasureTheory.lintegral μ u1 + MeasureTheory.lintegral μ u2 :=
        MeasureTheory.lintegral_add_left hu1m u2
    _ ≤ MeasureTheory.lintegral μ (fun a => f a * g a)
          + MeasureTheory.lintegral μ (fun a => f a * h a) :=
        add_le_add (MeasureTheory.lintegral_mono hle1) (MeasureTheory.lintegral_mono hle2)


/-- **The `θ`-integrated weighted Agmon inequality (the interface consumed by the term-by-term
assembly of `HkNorm_Dz_amgm`).**

Assume the one-dimensional weighted Agmon inequality in `lintegral` form with constant `C1`
(`FTS/EllipticEst/Blocks/DzAgmonLintegral`):

  `∀ β h, 0 < β → β ≤ 1 → C^∞ h on (0,∞) →`
  `ofReal(β²) ∫⁻_z ofReal(w(z)² (z h')²) ≤ ofReal(C1²) ( ofReal(β⁴) ∫⁻_z ofReal(w(z)² (z²h'')²) + ∫⁻_z ofReal(w(z)² h²) )`.

Then the same inequality holds with the `z`-integration *inside* an angular integration with an
arbitrary nonnegative angular weight `wth`:

  `ofReal(α²) ∫⁻_θ∈(0,π/2) ∫⁻_{z>0} ofReal((D_zV · w z · wth θ)²)`
  `  ≤ ofReal(C1²) ( ofReal(α⁴) ∫⁻_θ ∫⁻_z ofReal((z² ∂_z²V · w z · wth θ)²) + ∫⁻_θ ∫⁻_z ofReal((V · w z · wth θ)²) )`

for every `V` smooth (`C^∞`) on the open quadrant and every `0 < α ≤ 1`.

ROUTE.  For `θ ∈ (0,π/2)` apply `hgen` to the slice `h = V(·,θ)` (smooth on `(0,∞)` by
`Work.FTS.EllipticEst.SmoothOpen.curry_z`), rewrite
`z · ∂_z(V(·,θ)) = D_z V (·,θ)` and `z² ∂_z²(V(·,θ)) = z² ∂_z²V (·,θ)` (definitional), multiply
both sides by `ofReal (wth θ)²` (`≥ 0`) and use
`ofReal(wth θ²) * ofReal(u²) = ofReal((wth θ · u)²)` together with `lintegral_const_mul` to move
the `θ`-weight inside the `z`-lintegral, then integrate the resulting inequality over
`θ ∈ (0,π/2)` (`lintegral_mono`).  A.e. (for `θ ∈ (0,π/2)`) suffices, so no smoothness at
`θ = 0, π/2` is needed; the a.e. strong measurability of the `z`-slices of the integrand comes
from continuity of the uncurried integrand on the open quadrant
(`Work.Spaces.aesm_of_continuousOn_Qd`, `SmoothOpen.continuousOn_*`). -/
theorem TermAgmon (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (β : ℝ) (h : ℝ → ℝ), 0 < β → β ≤ 1 →
      ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ)) →
      ENNReal.ofReal (β ^ 2) *
          MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (β ^ 4) *
                MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal
                    ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))
              + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2)))) :
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) *
          (MeasureTheory.lintegral
              (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
              (fun θ => MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                (fun z => ENNReal.ofReal
                  ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))))
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) *
                (MeasureTheory.lintegral
                    (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
                    (fun θ => MeasureTheory.lintegral
                      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                      (fun z => ENNReal.ofReal
                        ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))))
              + (MeasureTheory.lintegral
                  (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
                  (fun θ => MeasureTheory.lintegral
                    (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                    (fun z => ENNReal.ofReal
                      ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))) := by
  intro α V wth hα hα1 hV hwth
  set cf : ℝ → ENNReal := fun θ => ENNReal.ofReal (wth θ ^ 2) with hcf
  set Lf : ℝ → ENNReal := fun θ => ∫⁻ z in Set.Ioi (0 : ℝ),
    ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2) with hLf
  set Af : ℝ → ENNReal := fun θ => ∫⁻ z in Set.Ioi (0 : ℝ),
    ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2)
    with hAf
  set Bf : ℝ → ENNReal := fun θ => ∫⁻ z in Set.Ioi (0 : ℝ),
    ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2) with hBf
  set A0 : ℝ → ENNReal := fun θ => ∫⁻ z in Set.Ioi (0 : ℝ),
    ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z) ^ 2) with hA0
  set B0 : ℝ → ENNReal := fun θ => ∫⁻ z in Set.Ioi (0 : ℝ),
    ENNReal.ofReal ((V z θ * Work.Spaces.w z) ^ 2) with hB0
  -- the pointwise-in-θ inequality
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ENNReal.ofReal (α ^ 2) * Lf θ
        ≤ ENNReal.ofReal (C1 ^ 2) * (ENNReal.ofReal (α ^ 4) * Af θ + Bf θ) := by
    intro θ hθ
    exact pointwise C1 α V wth hgen hα hα1 hV hθ
  have hmono : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ENNReal.ofReal (α ^ 2) * Lf θ)
      ≤ ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal (C1 ^ 2) * (ENNReal.ofReal (α ^ 4) * Af θ + Bf θ) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall (fun θ hθ => hpt θ hθ)
  -- splitting off the common angular factor
  have hAf_cf : ∀ θ, Af θ = cf θ * A0 θ := by
    intro θ
    show (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
      = ENNReal.ofReal (wth θ ^ 2) * (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z) ^ 2))
    rw [ofReal_sq_mul_lintegral wth θ
      (fun z => (z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z) ^ 2)]
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    congr 1
    ring
  have hBf_cf : ∀ θ, Bf θ = cf θ * B0 θ := by
    intro θ
    show (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))
      = ENNReal.ofReal (wth θ ^ 2) * (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((V z θ * Work.Spaces.w z) ^ 2))
    rw [ofReal_sq_mul_lintegral wth θ (fun z => (V z θ * Work.Spaces.w z) ^ 2)]
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    congr 1
    ring
  -- a.e. measurability of the angular slices of the two radial integrals
  have hA0m : AEMeasurable A0 (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (p.1 ^ 2 * Work.Spaces.pzIter 2 V p.1 p.2 * Work.Spaces.w p.1) ^ 2) Q0 :=
      (((continuousOn_fst.pow 2).mul ((hV.pzIter 2).continuousOn)).mul
        continuousOn_w_fst).pow 2
    have h := aemeasurable_lintegral_of_continuousOn_Qd hcont
    simpa only [hA0] using h
  have hB0m : AEMeasurable B0 (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (V p.1 p.2 * Work.Spaces.w p.1) ^ 2) Q0 :=
      (((hV.continuousOn).mul continuousOn_w_fst)).pow 2
    have h := aemeasurable_lintegral_of_continuousOn_Qd hcont
    simpa only [hB0] using h
  obtain ⟨A0', hA0'meas, hA0'ae⟩ := hA0m
  obtain ⟨B0', hB0'meas, hB0'ae⟩ := hB0m
  -- the unconditional subadditivity with measurable cofactors
  have hkey := lintegral_mul_add_le_aux
    (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (f := cf) (g := fun θ => ENNReal.ofReal (α ^ 4) * A0' θ) (h := B0')
    (hA0'meas.const_mul _) hB0'meas
  -- rewriting the two sides of `hkey`
  have hi : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (ENNReal.ofReal (α ^ 4) * Af θ + Bf θ))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          cf θ * (ENNReal.ofReal (α ^ 4) * A0' θ + B0' θ) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hA0'ae, hB0'ae] with θ h1 h2
    rw [hAf_cf θ, hBf_cf θ, h1, h2]
    ring
  have hii : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        cf θ * (ENNReal.ofReal (α ^ 4) * A0' θ))
      = ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Af θ) := by
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (α ^ 4)) _
      ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hA0'ae] with θ h1
    rw [hAf_cf θ, h1]
    ring
  have hiii : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), cf θ * B0' θ)
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Bf θ := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hB0'ae] with θ h1
    rw [← h1, hBf_cf θ]
  have hsub : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (ENNReal.ofReal (α ^ 4) * Af θ + Bf θ))
      ≤ ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Af θ)
        + ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Bf θ := by
    rw [hi]
    calc (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          cf θ * (ENNReal.ofReal (α ^ 4) * A0' θ + B0' θ))
        ≤ (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              cf θ * (ENNReal.ofReal (α ^ 4) * A0' θ))
            + ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), cf θ * B0' θ := hkey
      _ = ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Af θ)
            + ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Bf θ := by rw [hii, hiii]
  calc ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Lf θ)
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ENNReal.ofReal (α ^ 2) * Lf θ :=
        (MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (α ^ 2)) _
          ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal (C1 ^ 2) * (ENNReal.ofReal (α ^ 4) * Af θ + Bf θ) := hmono
    _ = ENNReal.ofReal (C1 ^ 2) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (ENNReal.ofReal (α ^ 4) * Af θ + Bf θ)) :=
        MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (C1 ^ 2)) _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Af θ)
            + ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Bf θ) :=
        mul_le_mul_of_nonneg_left hsub (zero_le : (0 : ENNReal) ≤ _)


end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.moment_relation =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## Fubini on the box `[a,b] × Iθ` -/

/-- **Fubini on a radial box.**  For a function jointly integrable on `[a,b] × Iθ` the two
iterated integrals agree.  This is `MeasureTheory.integral_integral_swap` after rewriting the
restriction of the planar Lebesgue measure to the box as the product of the restrictions
(`MeasureTheory.Measure.prod_restrict`). -/
lemma integral_Icc_integral_Itheta_swap {g : ℝ → ℝ → ℝ} {a b : ℝ}
    (hg : MeasureTheory.IntegrableOn (Function.uncurry g) (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :
    ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ, g s θ)
      = ∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc a b, g s θ) := by
  have hg' : Integrable (Function.uncurry g)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hg
  exact MeasureTheory.integral_integral_swap hg'

/-! ## The radial fundamental rule of calculus on a slice -/

/-- **The `z`-slice moment.**  For `u` smooth on the open quadrant, an interior angle
`θ ∈ (0,π/2)` and `0 < a < b`, the integral over `[a,b]` of `∂_z u(·,θ) · sinθcos²θ` is
`(u b θ - u a θ) · sinθcos²θ`: the constant `sinθcos²θ` factors out of the integral and the
fundamental rule of calculus along the (smooth) radial slice does the rest. -/
lemma integral_Icc_pz_mul_sinCos2 (u : ℝ → ℝ → ℝ) (hu : Work.FTS.EllipticEst.SmoothOpen u)
    {a b θ : ℝ} (ha : 0 < a) (hab : a < b) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ
      = (u b θ - u a θ) * Work.Elliptic.sinCos2 θ := by
  -- the radial derivative is continuous on the interval
  have hcont : ContinuousOn (fun r : ℝ => Work.Spaces.pz u r θ) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact ((hu.pz).curry_z hθ).continuousOn.mono (fun r hr => lt_of_lt_of_le ha hr.1)
  -- and is the derivative of the slice at every interior point
  have hderiv : ∀ r ∈ Set.uIcc a b,
      HasDerivAt (fun r : ℝ => u r θ) (Work.Spaces.pz u r θ) r := by
    intro r hr
    rw [Set.uIcc_of_le hab.le] at hr
    exact hu.hasDerivAt_slice hθ (lt_of_lt_of_le ha hr.1)
  have hFTC : ∫ s in Set.Icc a b, Work.Spaces.pz u s θ = u b θ - u a θ := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [← hFTC]
  exact MeasureTheory.integral_mul_const _ _

/-! ## Joint integrability of the moment integrand on the box -/

/-- **Joint integrability of `∂_z u · sinθcos²θ` on a radial box.**  From the weighted
`L²`-integrability of `∂_z u` (`hbox`, the weight being `sin(2θ)^{-η}`) and the smoothness of
`u` on the open quadrant, the product `∂_z u · sinθcos²θ` is jointly integrable on
`[a,b] × Iθ`.

The bound is the AM–GM inequality applied to the factorisation
`∂_z u · sinθcos²θ = (∂_z u · sin(2θ)^{-η/2}) · (sinθcos²θ · sin(2θ)^{η/2})`; since
`|sinθcos²θ| ≤ 1` and `0 ≤ sin(2θ) ≤ 1` on `Iθ`, the second factor is bounded by `1` and the
square of the first is `(∂_z u)² sin(2θ)^{-η}`, whence the pointwise domination
`|∂_z u · sinθcos²θ| ≤ ½ (∂_z u)² sin(2θ)^{-η} + ½`.
A.e. strong measurability comes from `SmoothOpen u`: `∂_z u` is continuous on the open
quadrant, and the box differs from the open quadrant only by null lines. -/
lemma integrableOn_box_pz_mul_sinCos2 (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  have hηne : -(Work.Spaces.eta) ≠ 0 := by norm_num [Work.Spaces.eta]
  -- the box has finite measure
  have hvolFin : volume (Set.Icc a b ×ˢ Work.Spaces.Iθ) < ⊤ :=
    (isCompact_Icc.prod (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)).measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :=
    isFiniteMeasure_restrict.mpr hvolFin.ne
  -- the dominating function is integrable
  have hbase : Integrable (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) := hbox a b ha hab
  have hdom : Integrable (fun p : ℝ × ℝ => (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2)
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :=
    (hbase.const_mul (1 / 2)).add (integrable_const (1 / 2))
  -- a.e. strong measurability, from continuity of `∂_z u` on the open quadrant
  have hsub : Set.Icc a b ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
    Set.prod_mono (fun x hx => le_trans (le_of_lt ha) hx.1) subset_rfl
  have hmono : volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono hsub le_rfl
  have haesm : AEStronglyMeasurable
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      ((hu.pz).continuousOn.mul (((by unfold Work.Elliptic.sinCos2; fun_prop :
        Continuous Work.Elliptic.sinCos2).comp continuous_snd).continuousOn))).mono_measure hmono
  -- the pointwise domination
  have hpt : ∀ᵐ p ∂(volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)),
      ‖Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) p‖
        ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2 := by
    rw [MeasureTheory.ae_restrict_iff' (s := Set.Icc a b ×ˢ Work.Spaces.Iθ)
      (measurableSet_Icc.prod measurableSet_Icc)]
    refine Filter.Eventually.of_forall fun p hp => ?_
    have hθ : p.2 ∈ Work.Spaces.Iθ := hp.2
    have hx0 : 0 ≤ Real.sin (2 * p.2) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
    have hx1 : Real.sin (2 * p.2) ≤ 1 := Real.sin_le_one _
    -- `|sinθcos²θ| ≤ 1`
    have hC : |Work.Elliptic.sinCos2 p.2| ≤ 1 := by
      rw [Work.Elliptic.sinCos2, abs_mul]
      have h1 : |Real.sin p.2| ≤ 1 := Real.abs_sin_le_one p.2
      have h2 : |Real.cos p.2 ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (sq_nonneg (Real.cos p.2))]
        nlinarith [Real.abs_cos_le_one p.2, abs_nonneg (Real.cos p.2), sq_abs (Real.cos p.2)]
      calc |Real.sin p.2| * |Real.cos p.2 ^ 2| ≤ 1 * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    show ‖Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
        ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2
    -- AM–GM for the radial factor
    have hAF : |Work.Spaces.pz u p.1 p.2|
        ≤ (1 / 2) * (Work.Spaces.pz u p.1 p.2) ^ 2 + 1 / 2 := by
      nlinarith [sq_abs (Work.Spaces.pz u p.1 p.2),
        sq_nonneg (|Work.Spaces.pz u p.1 p.2| - 1)]
    by_cases hx : Real.sin (2 * p.2) = 0
    · -- at the degenerate angles `sinθcos²θ` vanishes and the weight kills the other term
      have hC0 : Work.Elliptic.sinCos2 p.2 = 0 := by
        have h2 : Real.sin p.2 * Real.cos p.2 = 0 := by
          have h3 := Real.sin_two_mul p.2
          rw [hx] at h3
          linarith
        rw [Work.Elliptic.sinCos2]
        rcases mul_eq_zero.mp h2 with h | h
        · rw [h, zero_mul]
        · rw [pow_two, h, mul_zero, mul_zero]
      rw [hC0, hx, Real.zero_rpow hηne]
      simp only [mul_zero, norm_zero]
      norm_num
    · have hxpos : 0 < Real.sin (2 * p.2) := lt_of_le_of_ne hx0 (Ne.symm hx)
      -- the weight `sin(2θ)^{-η}` is at least `1`
      have hxle : 1 ≤ (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
        have h1 : (Real.sin (2 * p.2)) ^ (Work.Spaces.eta) ≤ 1 :=
          Real.rpow_le_one hx0 hx1 (by norm_num [Work.Spaces.eta])
        have h2 : 0 < (Real.sin (2 * p.2)) ^ (Work.Spaces.eta) := Real.rpow_pos_of_pos hxpos _
        rw [Real.rpow_neg hxpos.le]
        exact (one_le_inv₀ h2).mpr h1
      have hstep : ‖Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
          ≤ |Work.Spaces.pz u p.1 p.2| := by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) hC
      have hle2 : (1 / 2) * (Work.Spaces.pz u p.1 p.2) ^ 2 + 1 / 2
          ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2 := by
        have h4 := mul_le_mul_of_nonneg_left hxle (sq_nonneg (Work.Spaces.pz u p.1 p.2))
        nlinarith
      linarith
  exact Integrable.mono' hdom haesm hpt

/-! ## The target -/

/-- **The angular moment is an antiderivative of its `z`-derivative.**  For a function `u` smooth on the open quadrant whose slices and whose `z`-derivative's weighted square are integrable,

`F_*(u)(b) = F_*(u)(a) + ∫_a^b (∫_θ ∂_z u(s,θ) sin θ cos²θ dθ) ds`,

i.e. `d/dz F_*(u)(z) = ∫_θ ∂_z u(z,θ) sinθcos²θ dθ`, with `F_*(u)(z) = ∫_θ u(z,θ) sinθcos²θ dθ` (`Work.Elliptic.Fstar`).  This is the analytic input that makes the angular moment `F_*` a function of the *radial* Hardy/integration-by-parts arguments of the paper (`L₁₂(F)(z) = 3∫_z^∞ F_*(F)(r)/r dr`, Lemma `L12H`, `HardyInequality4`).

ROUTE (Fubini + FTC, as in the sibling file `Submission.Work.FTS.EllipticEst.moment_relation`): from `hbox`, Cauchy–Schwarz with `sinCos2 θ · sin(2θ)^{η/2}` (integrable on `Iθ`) gives the joint integrability of `|∂_z u · sinCos2|` on `[a,b] × Iθ`; for each `θ`, `SmoothOpen` gives `∫_a^b ∂_z u(s,θ) ds = u b θ - u a θ`; `hsl` gives the `θ`-integrability of the difference; then `MeasureTheory.integral_integral_swap` (or `intervalIntegral.integral_integral_swap`) finishes. -/
theorem moment_relation (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Work.Elliptic.Fstar u b = Work.Elliptic.Fstar u a
      + ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) := by
  have hb : 0 < b := lt_trans ha hab
  -- joint integrability on the box
  have hjoint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) :=
    integrableOn_box_pz_mul_sinCos2 u hu hbox ha hab
  -- the slice identity holds for a.e. angle
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
        = (u b θ - u a θ) * Work.Elliptic.sinCos2 θ := by
    have hst : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
    rw [MeasureTheory.Measure.restrict_congr_set hst]
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Set.Ioo 0 (Real.pi / 2))
      measurableSet_Ioo] with θ hθ
    exact integral_Icc_pz_mul_sinCos2 u hu ha hab hθ
  -- Fubini, then the `θ`-integral of the difference
  have hkey : ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
      = Work.Elliptic.Fstar u b - Work.Elliptic.Fstar u a := by
    rw [integral_Icc_integral_Itheta_swap hjoint]
    calc ∫ θ in Work.Spaces.Iθ,
          (∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ, (u b θ - u a θ) * Work.Elliptic.sinCos2 θ :=
          MeasureTheory.integral_congr_ae hae
      _ = ∫ θ in Work.Spaces.Iθ,
            (u b θ * Work.Elliptic.sinCos2 θ - u a θ * Work.Elliptic.sinCos2 θ) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
          ring
      _ = (∫ θ in Work.Spaces.Iθ, u b θ * Work.Elliptic.sinCos2 θ)
            - (∫ θ in Work.Spaces.Iθ, u a θ * Work.Elliptic.sinCos2 θ) :=
          MeasureTheory.integral_sub (hsl b hb) (hsl a ha)
      _ = Work.Elliptic.Fstar u b - Work.Elliptic.Fstar u a := rfl
  linarith [hkey]

end Work.FTS.EllipticEst.Blocks
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.GbarSin.SmoothOpen_bslOp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert.GbarSin

open scoped Real
open Work.FTS.EllipticEst (Q0)


end Work.FTS.EllipticEst.Cert.GbarSin
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.truncThetaIbpSep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Elementary facts -/

lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])






/-- Linearity of a set integral over four `ℝ`-valued functions. -/
lemma integral_lin4 {μ : MeasureTheory.Measure ℝ} {s : Set ℝ} (f1 f2 f3 f4 : ℝ → ℝ)
    (c1 c2 c3 c4 : ℝ)
    (h1 : MeasureTheory.IntegrableOn f1 s μ) (h2 : MeasureTheory.IntegrableOn f2 s μ)
    (h3 : MeasureTheory.IntegrableOn f3 s μ) (h4 : MeasureTheory.IntegrableOn f4 s μ) :
    (∫ x in s, c1 * f1 x - c2 * f2 x - c3 * f3 x + c4 * f4 x ∂μ)
      = c1 * (∫ x in s, f1 x ∂μ) - c2 * (∫ x in s, f2 x ∂μ)
        - c3 * (∫ x in s, f3 x ∂μ) + c4 * (∫ x in s, f4 x ∂μ) := by
  have h12 : MeasureTheory.IntegrableOn (fun x => c1 * f1 x - c2 * f2 x) s μ :=
    (h1.const_mul c1).sub (h2.const_mul c2)
  have h123 : MeasureTheory.IntegrableOn (fun x => c1 * f1 x - c2 * f2 x - c3 * f3 x) s μ :=
    h12.sub (h3.const_mul c3)
  rw [MeasureTheory.integral_add h123 (h4.const_mul c4),
    MeasureTheory.integral_sub h12 (h3.const_mul c3),
    MeasureTheory.integral_sub (h1.const_mul c1) (h2.const_mul c2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-! ## Clairaut: the `θ`-derivatives of the `z`-slice of `∂_z u` -/

/-- `(θ ↦ z ∂_z u z θ)' θ = z ∂_z∂_θu z θ`. -/
lemma deriv_slice_pz (u : ℝ → ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => z * Work.Spaces.pz u z θ') θ
      = z * Work.Spaces.pz (Work.Spaces.pth u) z θ := by
  have hmem : (z, θ) ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨hz, hθ⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
    (hu 2).contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)
  have hp : Work.Spaces.pth (Work.Spaces.pz u) z θ = Work.Spaces.pz (Work.Spaces.pth u) z θ :=
    (Work.Spaces.pz_pth_comm hcd).symm
  rw [deriv_const_mul_field]
  exact congrArg (fun t => z * t) hp

/-- `(θ ↦ ∂_θ(z ∂_z u z ·))' θ = z ∂_z∂_θ∂_θu z θ`. -/
lemma deriv_deriv_slice_pz (u : ℝ → ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => deriv (fun θ'' => z * Work.Spaces.pz u z θ'') θ') θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hu
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  -- the inner derivative, identified on a neighbourhood of `θ`
  have hnhds : (fun θ' => deriv (fun θ'' => z * Work.Spaces.pz u z θ'') θ')
      =ᶠ[𝓝 θ] fun θ' => z * Work.Spaces.pz (Work.Spaces.pth u) z θ' := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact deriv_slice_pz u hu hz hθ'
  rw [Filter.EventuallyEq.deriv_eq hnhds, deriv_const_mul_field]
  congr 1
  have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth u)) (z, θ) :=
    ((hS.pth).forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have hp : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth u)) z θ
      = Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth u)) z θ :=
    (Work.Spaces.pz_pth_comm hcd).symm
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using hp

/-! ## The inner (`θ`)-integral identity at a fixed `z`

This is `sliceThetaIbpSep` transported along the two Clairaut identities: for `z > 0` the slice
`v = (θ ↦ z ∂_z u z θ)` has `v' = z ∂_z∂_θu` and `v'' = z ∂_z∂_θ∂_θu`. -/

theorem inner_ident (u : ℝ → ℝ → ℝ) (ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hψ : ContDiff ℝ 2 ψ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b < Real.pi / 2) (hsupp : tsupport ψ ⊆ Set.Ioo a b)
    {z : ℝ} (hz : 0 < z) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * ((z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)))
      = -2 * Work.Spaces.eta * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (z * Work.Spaces.pz u z θ)^2)
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
            * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                  * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2)
        - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta))
            * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                  * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
                      - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                        * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2)
        + (1/2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * deriv (deriv ψ) θ
              * (z * Work.Spaces.pz u z θ)^2) := by
  have hv : ContDiffOn ℝ 2 (fun θ => z * Work.Spaces.pz u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hS : Work.FTS.EllipticEst.SmoothOpen u :=
      Work.FTS.EllipticEst.smoothOpen_of_forall hu
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ => Work.Spaces.pz u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (hS.pz).curry_θ hz
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ => z * Work.Spaces.pz u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      contDiffOn_const.mul h1
    exact h2.of_le (by simp)
  have hslice := sliceThetaIbpSep2 (fun θ => z * Work.Spaces.pz u z θ) ψ hv hψ
    ⟨a, b, ha, hab, hb, hsupp⟩
  -- identify the second derivative of the slice
  have hv'' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (fun θ' => z * Work.Spaces.pz u z θ')) θ
        = z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ :=
    fun θ hθ => deriv_deriv_slice_pz u hu hz hθ
  have hv' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ' => z * Work.Spaces.pz u z θ') θ
        = z * Work.Spaces.pz (Work.Spaces.pth u) z θ :=
    fun θ hθ => deriv_slice_pz u hu hz hθ
  -- rewrite the four integrals of the slice identity into the stated shape
  have e1 : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * ((fun θ' => z * Work.Spaces.pz u z θ') θ
              * deriv (deriv (fun θ' => z * Work.Spaces.pz u z θ')) θ))
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * ((z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)) :=
    setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => by rw [hv'' θ hθ])
  have e2 : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * ((fun θ' => z * Work.Spaces.pz u z θ') θ)^2)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (z * Work.Spaces.pz u z θ)^2 :=
    setIntegral_congr_fun measurableSet_Ioo (fun θ _ => rfl)
  have e3 : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (deriv (fun θ' => z * Work.Spaces.pz u z θ') θ)^2)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2 :=
    setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => by rw [hv' θ hθ])
  have e4 : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (deriv (fun θ' => z * Work.Spaces.pz u z θ') θ
              - (1 + Work.Spaces.eta) * (fun θ' => z * Work.Spaces.pz u z θ') θ
                * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
              - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2 :=
    setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => by rw [hv' θ hθ])
  have e5 : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * deriv (deriv ψ) θ
          * ((fun θ' => z * Work.Spaces.pz u z θ') θ)^2)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * deriv (deriv ψ) θ
          * (z * Work.Spaces.pz u z θ)^2 :=
    setIntegral_congr_fun measurableSet_Ioo (fun θ _ => rfl)
  rw [e1, e2, e3, e4, e5] at hslice
  exact hslice

/-! ## Integrability of the four angular integrands (at a fixed `z > 0`) -/


/-! ## The corrected truncated identity

The statement below differs from the requested `truncThetaIbp` in exactly two ways:

* the hypothesis `hψsupp` (about `Function.support ψ`) is replaced by `hψsep` (the *closed*
  support `tsupport ψ` is separated from both corners, which is what kills the angular boundary
  bracket);
* the RHS is a *single* iterated integral of the four-term combination (with each of the four
  angular pairings written as an explicit `θ`-integral).  Splitting it into the four separate
  iterated integrals of the requested statement needs only the linearity of the outer integral
  and is done in `truncThetaIbpSep_split` below, under the corresponding integrability
  hypotheses. -/

theorem truncThetaIbpSep (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupp : Function.support χ ⊆ Set.Ioi (0:ℝ))
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hψsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), χ z * (Work.Spaces.w z)^2
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ))
    = ∫ z in Set.Ioi 0,
        (-2 * Work.Spaces.eta
            * (χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                  * (z * Work.Spaces.pz u z θ)^2))
          - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
            * (χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                  * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
          - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta))
            * (χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                  * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
                      - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                        * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2))
          + (1/2) * (χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
                  * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2))) := by
  obtain ⟨a, b, ha, hab, hb, hsupp⟩ := hψsep
  refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
  have hzpos : 0 < z := hz
  -- pull the `θ`-independent factor `χ z · w z ^ 2` out of the LHS integral
  have hL : (∫ θ in Set.Ioo 0 (Real.pi / 2), χ z * (Work.Spaces.w z)^2
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ))
      = χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
            * ((z * Work.Spaces.pz u z θ)
                * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ))) := by
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)
  rw [hL, inner_ident u ψ hu hψ ha hab hb hsupp hzpos]
  ring

/-- **The corrected angular truncated identity in the exact shape of the requested statement.**

Same statement as `truncThetaIbpSep`, with the RHS written as the four separate iterated integrals
of the request.  The passage from the single-integral form needs the linearity of the outer `z`
-integral, hence the four integrability hypotheses `ho1`–`ho4` (which hold automatically in the
intended application, where `χ` is compactly supported in `(0,∞)` and the four `θ`-integrands are
bounded on `tsupport χ × [a,b]`). -/
theorem truncThetaIbpSep_split (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupp : Function.support χ ⊆ Set.Ioi (0:ℝ))
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hψsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b)
    (ho1 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (z * Work.Spaces.pz u z θ)^2))
      (Set.Ioi 0))
    (ho2 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
      (Set.Ioi 0))
    (ho3 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
              - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2))
      (Set.Ioi 0))
    (ho4 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
          * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2))
      (Set.Ioi 0)) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), χ z * (Work.Spaces.w z)^2
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ))
      = -2 * Work.Spaces.eta * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                * (z * Work.Spaces.pz u z θ)^2))
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
        - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
                    - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                      * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2))
        + (1/2) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
                * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2)) := by
  rw [truncThetaIbpSep u χ ψ hu hχ hχc hχsupp hψ hψc hψsep]
  rw [integral_lin4
    (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (z * Work.Spaces.pz u z θ)^2))
    (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
    (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
            - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
              * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2))
    (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
        * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2))
    (-2 * Work.Spaces.eta) ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
    (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) (1/2) ho1 ho2 ho3 ho4]

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.DiagEstEllT

set_option autoImplicit false

/-- **`HkMem` by an a.e. angular domination by a sum, from continuity of the integrand on the
open quadrant.**  The smoothness of `h` is used for exactly one purpose, the a.e. strong
measurability of `HkIntegrand α k h`; taking that as an explicit hypothesis makes the lemma
applicable to data (such as the straightened datum `Ψ + Gsing α F · sin 2θ`) which are honest on
the open quadrant but not `C^∞` there.  The continuity hypothesis is available for every datum
that is `C^k` on the open quadrant
(`Cores.DiagEstEllT.continuousOn_HkIntegrand_of_contDiffOn`). -/
theorem HkMem_of_add_dominated_cont (α : ℝ) (k : ℕ) {f g h : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      Work.FTS.EllipticEst.Q0)
    (hf : Work.Spaces.HkMem α k f) (hg : Work.Spaces.HkMem α k g)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k h z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkMem α k h := by
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α k h z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [show (fun θ => Work.Spaces.HkIntegrand α k h z θ) = fun _ => (0 : ℝ) from by
        funext θ; rw [← hz0, Work.Spaces.HkIntegrand_zero_z]]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  constructor
  · -- every angular slice of the integrand of `h` is integrable on `Iθ`
    intro z hz
    refine Integrable.mono'
      (((hf.1 z hz).const_mul 2).add ((hg.1 z hz).const_mul 2)) (hslice z hz) ?_
    filter_upwards [hle z hz] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k h z θ)]
    exact hθ
  · -- the `z`-integral of the angular slices is integrable on `Iz`
    refine Integrable.mono'
      (((hf.2).const_mul 2).add ((hg.2).const_mul 2)) hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem hmesz] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem hmesθ
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k h z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hmono : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
            2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ :=
      integral_mono_of_nonneg
        (ae_restrict_of_forall_mem hmesθ
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k h z θ))
        (((hf.1 z hz).const_mul 2).add ((hg.1 z hz).const_mul 2))
        (hle z hz)
    have hcalc : (∫ θ in Work.Spaces.Iθ,
          2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ)
        = 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := by
      rw [integral_add ((hf.1 z hz).const_mul 2) ((hg.1 z hz).const_mul 2),
        integral_const_mul, integral_const_mul]
    exact le_trans hmono hcalc.le

/-- **`HkMem` by an a.e. angular domination by a sum, from open-quadrant smoothness** (the
specialisation of `HkMem_of_add_dominated_cont` to `SmoothOpen` data). -/
theorem HkMem_of_add_dominated_open (α : ℝ) (k : ℕ) {f g h : ℝ → ℝ → ℝ}
    (hsmh : Work.FTS.EllipticEst.SmoothOpen h)
    (hf : Work.Spaces.HkMem α k f) (hg : Work.Spaces.HkMem α k g)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k h z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkMem α k h :=
  HkMem_of_add_dominated_cont α k (hsmh.continuousOn_HkIntegrand α k) hf hg hle

end Work.FTS.EllipticEst.Cores.DiagEstEllT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.difQuotSubDerivBoundD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- `sinθcos²θ` vanishes on `Iθ` only at the two endpoints. -/
private theorem sinCos2_ne_zero_iff {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Elliptic.sinCos2 θ ≠ 0 ↔ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  constructor
  · intro h
    have hsin : Real.sin θ ≠ 0 := fun h0 => h (by rw [Work.Elliptic.sinCos2, h0, zero_mul])
    have hcos : Real.cos θ ≠ 0 := fun h0 => h (by rw [Work.Elliptic.sinCos2, h0]; ring)
    refine ⟨lt_of_le_of_ne hθ.1 (fun h0 => hsin (by rw [← h0, Real.sin_zero])),
      lt_of_le_of_ne hθ.2 ?_⟩
    intro h2
    exact hcos (by rw [h2, Real.cos_pi_div_two])
  · intro h
    rw [Work.Elliptic.sinCos2]
    refine mul_ne_zero ?_ (pow_ne_zero 2 ?_)
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1])
        (by linarith [h.2, Real.pi_pos]))
    · exact ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [h.1, Real.pi_pos], by linarith [h.2, Real.pi_pos]⟩)

/-- The radial second derivative of a slice is continuous on `(0,∞)`. -/
private theorem continuousOn_pzIter_two_slice {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ContinuousOn (fun y : ℝ => Work.Spaces.pzIter 2 u y θ) (Set.Ioi 0) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have h2 : ContDiffOn ℝ 2 (fun y : ℝ => u y θ) (Set.Ioi 0) :=
    contDiffOn_iff_forall_nat_le.mp (hSO.curry_z hθ) 2 le_top
  have hd1 : ContDiffOn ℝ 1 (deriv (fun y : ℝ => u y θ)) (Set.Ioi 0) :=
    h2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hd2 : ContDiffOn ℝ 0 (deriv (deriv (fun y : ℝ => u y θ))) (Set.Ioi 0) :=
    hd1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hid : (fun y : ℝ => Work.Spaces.pzIter 2 u y θ)
      = fun y : ℝ => deriv (deriv (fun y' : ℝ => u y' θ)) y := by
    funext y
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  rw [hid]
  exact hd2.continuousOn

theorem difQuotSubDerivBoundD {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hψ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hp1 : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {z hh : ℝ} (hz : 0 < z) (hh0 : 0 < hh) (hhz : hh < z / 2)
    (hbox : MeasureTheory.IntegrableOn
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (Set.Icc (z - hh) z ×ˢ Work.Spaces.Iθ)) :
    |(Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
        - Work.Elliptic.Fstar (Work.Spaces.pz u) z|
      ≤ ∫ θ in Work.Spaces.Iθ,
          (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
            * |Work.Elliptic.sinCos2 θ| := by
  have hz' : 0 < z - hh := by linarith
  have hlt : z - hh < z := by linarith
  have hle : z - hh ≤ z := le_of_lt hlt
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  -- ## Step 1: the difference of the two moments
  have hsub : Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)
      = ∫ θ in Work.Spaces.Iθ,
          (u z θ - u (z - hh) θ) * Work.Elliptic.sinCos2 θ := by
    rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar,
      ← MeasureTheory.integral_sub (hψ z hz) (hψ (z - hh) hz')]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  -- ## Step 2: the pointwise slice bound
  have hslice : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |(u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ|
        ≤ ∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ| := by
    intro θ hθ
    -- the fundamental rule of calculus along the slice
    have hderiv1 : ∀ x ∈ Set.uIcc (z - hh) z,
        HasDerivAt (fun y : ℝ => u y θ) (Work.Spaces.pz u x θ) x := by
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      exact hSO.hasDerivAt_slice hθ (lt_of_lt_of_le hz' hx.1)
    have hcont1 : ContinuousOn (fun x : ℝ => Work.Spaces.pz u x θ)
        (Set.uIcc (z - hh) z) := by
      rw [Set.uIcc_of_le hle]
      exact ((hSO.pz).curry_z hθ).continuousOn.mono (fun x hx => lt_of_lt_of_le hz' hx.1)
    have hFTC1 : ∫ x in (z - hh)..z, Work.Spaces.pz u x θ = u z θ - u (z - hh) θ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv1 hcont1.intervalIntegrable
    -- the mean-value bound on the derivative
    have hMVT : ∀ x ∈ Set.Icc (z - hh) z,
        |Work.Spaces.pz u x θ - Work.Spaces.pz u z θ|
          ≤ ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hz' hx.1
      have hxx : x ≤ z := hx.2
      have hderiv2 : ∀ y ∈ Set.uIcc x z,
          HasDerivAt (fun y : ℝ => Work.Spaces.pz u y θ) (Work.Spaces.pzIter 2 u y θ) y := by
        intro y hy
        rw [Set.uIcc_of_le hxx] at hy
        have hy0 : 0 < y := lt_of_lt_of_le hxpos hy.1
        have h1 := hSO.hasDerivAt_slice_pzIter 1 hθ hy0
        simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h1
      have hcont2 : ContinuousOn (fun y : ℝ => Work.Spaces.pzIter 2 u y θ) (Set.uIcc x z) := by
        rw [Set.uIcc_of_le hxx]
        exact (continuousOn_pzIter_two_slice hsm hθ).mono (fun y hy => lt_of_lt_of_le hxpos hy.1)
      have hFTC2 : ∫ y in x..z, Work.Spaces.pzIter 2 u y θ
          = Work.Spaces.pz u z θ - Work.Spaces.pz u x θ :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv2 hcont2.intervalIntegrable
      have hcontabs : ContinuousOn (fun y : ℝ => |Work.Spaces.pzIter 2 u y θ|)
          (Set.uIcc (z - hh) z) := by
        rw [Set.uIcc_of_le hle]
        exact (continuousOn_pzIter_two_slice hsm hθ).abs.mono
          (fun y hy => lt_of_lt_of_le hz' hy.1)
      have hle1 : ∫ y in x..z, |Work.Spaces.pzIter 2 u y θ|
          ≤ ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| :=
        intervalIntegral.integral_mono_interval hx.1 hxx le_rfl
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
            (fun y _ => abs_nonneg _))
          hcontabs.intervalIntegrable
      calc |Work.Spaces.pz u x θ - Work.Spaces.pz u z θ|
          = |∫ y in x..z, Work.Spaces.pzIter 2 u y θ| := by rw [hFTC2, abs_sub_comm]
        _ ≤ ∫ y in x..z, |Work.Spaces.pzIter 2 u y θ| :=
            intervalIntegral.abs_integral_le_integral_abs hxx
        _ ≤ ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| := hle1
    -- assemble
    have hconst : ∫ x in (z - hh)..z, Work.Spaces.pz u z θ = hh * Work.Spaces.pz u z θ := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    have hInt1 : ∫ x in (z - hh)..z, (Work.Spaces.pz u x θ - Work.Spaces.pz u z θ)
        = (u z θ - u (z - hh) θ) - hh * Work.Spaces.pz u z θ := by
      rw [intervalIntegral.integral_sub hcont1.intervalIntegrable intervalIntegrable_const,
        hFTC1, hconst]
    have hdiff : (u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ
        = (1 / hh) * ∫ x in (z - hh)..z,
            (Work.Spaces.pz u x θ - Work.Spaces.pz u z θ) := by
      rw [hInt1]
      field_simp
    rw [hdiff, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / hh)]
    have hbnd : |∫ x in (z - hh)..z, (Work.Spaces.pz u x θ - Work.Spaces.pz u z θ)|
        ≤ hh * ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| := by
      calc |∫ x in (z - hh)..z, (Work.Spaces.pz u x θ - Work.Spaces.pz u z θ)|
          ≤ ∫ x in (z - hh)..z, |Work.Spaces.pz u x θ - Work.Spaces.pz u z θ| :=
            intervalIntegral.abs_integral_le_integral_abs hle
        _ ≤ ∫ x in (z - hh)..z, ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| := by
            refine intervalIntegral.integral_mono_on hle ?_ intervalIntegrable_const ?_
            · exact ((hcont1.sub continuousOn_const).abs).intervalIntegrable
            · intro x hx
              exact hMVT x hx
        _ = hh * ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| := by
            rw [intervalIntegral.integral_const]
            simp only [smul_eq_mul]
            ring
    calc (1 / hh) * |∫ x in (z - hh)..z, (Work.Spaces.pz u x θ - Work.Spaces.pz u z θ)|
        ≤ (1 / hh) * (hh * ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ|) :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
      _ = ∫ y in (z - hh)..z, |Work.Spaces.pzIter 2 u y θ| := by
          field_simp
  -- ## Step 3: integrate the pointwise bound against `|sinθcos²θ|`
  have hAsub : (Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
      = ∫ θ in Work.Spaces.Iθ,
          ((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ := by
    rw [hsub, ← MeasureTheory.integral_div]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  have hintA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (u z θ - u (z - hh) θ) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      ((hψ z hz).sub (hψ (z - hh) hz')).congr
        (Filter.Eventually.of_forall fun θ => by simp only [Pi.sub_apply]; ring)
    refine (h1.div_const hh).congr (Filter.Eventually.of_forall fun θ => ?_)
    ring
  have hcomb : (Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
        - Work.Elliptic.Fstar (Work.Spaces.pz u) z
      = ∫ θ in Work.Spaces.Iθ,
          (((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ
            - Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ) := by
    rw [hAsub, Work.Elliptic.Fstar,
      ← MeasureTheory.integral_sub hintA (hp1 z hz)]
  -- the majorant is integrable in `θ`
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
        * |Work.Elliptic.sinCos2 θ|) Work.Spaces.Iθ := by
    have hjoint : MeasureTheory.Integrable
        (Function.uncurry (fun x θ : ℝ =>
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
        ((MeasureTheory.volume.restrict (Set.Icc (z - hh) z)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [MeasureTheory.Measure.prod_restrict]
      exact hbox
    have h1 : MeasureTheory.Integrable
        (fun θ : ℝ => ∫ x, |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|
          ∂(MeasureTheory.volume.restrict (Set.Icc (z - hh) z)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hjoint.integral_prod_right
    refine h1.congr ?_
    filter_upwards with θ
    rw [intervalIntegral.integral_of_le hle,
      MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc),
      ← MeasureTheory.integral_mul_const]
  -- the pointwise bound on the integrand
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ
          - Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ‖
        ≤ (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
            * |Work.Elliptic.sinCos2 θ| := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, show ((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ
        - Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ
        = (((u z θ - u (z - hh) θ) / hh) - Work.Spaces.pz u z θ)
          * Work.Elliptic.sinCos2 θ from by ring, abs_mul]
    by_cases hs : Work.Elliptic.sinCos2 θ = 0
    · simp [hs]
    · exact mul_le_mul_of_nonneg_right
        (hslice θ ((sinCos2_ne_zero_iff hθ).mp hs)) (abs_nonneg _)
  calc |(Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
          - Work.Elliptic.Fstar (Work.Spaces.pz u) z|
      = ‖∫ θ in Work.Spaces.Iθ,
          (((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ
            - Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ)‖ := by
        rw [hcomb, Real.norm_eq_abs]
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          ‖((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ
            - Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
            * |Work.Elliptic.sinCos2 θ| := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ hmaj_int hpt
        exact Filter.Eventually.of_forall fun θ => norm_nonneg _

end Work.FTS.EllipticEst.Dispatch
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.DzAmgm.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.DzAmgm

set_option autoImplicit false

/-! ## The angular weights -/

/-- The angular weight `sin(2θ)^{-η/2}` of the *pure* (`D_z`-) summands of `HkIntegrand`:
`(w z / sin(2θ)^{η/2}) = w z · angZ θ` on the quadrant. -/
def angZ (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))

/-- The angular weight `sin(2θ)^{-γ/2}` of the *mixed* summands: `Wt α z θ = w z · angM α θ`. -/
def angM (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))

/-- The second radial derivative `z² ∂_z² f` appearing in the hypotheses of `HkNorm_Dz_amgm`. -/
def zsqPz2 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ

/-! ## The term functionals -/

/-- The honest `L²·L²` size of the `m`-th pure summand `D_z^m f · w · angZ` of `HkIntegrand`.
Written as a nested `lintegral` over `Iθ × Iz`, angular variable first (the order in which the
sliced interpolation is applied). -/
def TZ (f : ℝ → ℝ → ℝ) (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
    ENNReal.ofReal ((Work.Spaces.DzIter m f z θ * Work.Spaces.w z * angZ θ) ^ 2)

/-- The honest `L²·L²` size of the mixed summand `D_z^j D_θ^i f · Wt α`. -/
def TM (α : ℝ) (f : ℝ → ℝ → ℝ) (i j : ℕ) : ℝ≥0∞ :=
  ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
    ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)

/-- The honest (`lintegral`) version of `HkSq α k f`: the nested `lintegral` of
`ENNReal.ofReal (HkIntegrand α k f ·)`, angular variable first. -/
def LkSq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
    ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ)

/-! ## Elementary properties -/

/-- On the angular interval the pure angular weight is nonnegative. -/
theorem angZ_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angZ θ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _

/-- On the angular interval the mixed angular weight is nonnegative. -/
theorem angM_nonneg_of_mem {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angM α θ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _



end Work.FTS.EllipticEst.DzAmgm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.DzAmgm

/-- **`D_θ^i` commutes with `D_z` on the open quadrant, for `C^∞` (not analytic) data.**

For `f` smooth on the open quadrant `Q0 = (0,∞) × (0,π/2)` and every `i : ℕ`,

`D_θ^i (D_z f) = D_z (D_θ^i f)`  on `Q0`.

This is the `C^∞` version of `Work.Spaces.DzDthIterCommOn` (whose hypothesis
`ContDiffOn ℝ ⊤ …` is *analyticity* in this Mathlib, whereas the elliptic chapter's `SmoothOpen`
only provides `C^∞ = Work.Stability.smoothOrder`).

Route.  Induct on `i`.  The induction step is the single-operator commutation
`Work.Spaces.Dz_Dth_comm`, which needs `ContDiffAt ℝ 2 (Function.uncurry (DthIter i f)) y` at
`y ∈ Q0`; that is available because `DthIter i f` is itself `C^∞` on `Q0`
(`Work.FTS.EllipticEst.SmoothOpen.DthIter`, i.e. `ContDiffOn` of the iterates, restricted with
`ContDiffOn.of_le (2 ≤ smoothOrder)`).  The remaining steps are the local congruence of the
`θ`-derivative on an open neighbourhood, exactly as in the existing `⊤`-version: compare the two
sides pointwise at `y ∈ Q0`, using that both functions agree on the open set `Q0` around `y`. -/
theorem DthIterDzCommOpen (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f) (a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter a f)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.Dz f))) Q0 := by
  induction a with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      -- `D_θ^i f` is `C^∞` on `Q0`, hence `C²` at the interior point `y ∈ Q0`.
      have hF : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i f)) y :=
        ((smoothOpen_iff_forall _).mp (hf.DthIter i) 2).contDiffAt (isOpen_Q0.mem_nhds hy)
      -- Move the outer `D_z` past the outermost `D_θ` using Clairaut/Schwarz at `y`.
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm hF
      show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz f)) y.1 y.2
      rw [hcomm]
      -- The two functions agree on the open set `Q0` (induction hypothesis), so their
      -- `θ`-derivatives agree at `y`.
      show Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i f)) y.1 y.2
          = Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz f))
              y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen isOpen_Q0 ih hy]

end Work.FTS.EllipticEst.DzAmgm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.DzIter_slice_FTC_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

theorem DzIter_slice_FTC_open {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (j : ℕ) {s z θ : ℝ} (hs : 0 < s) (hsz : s ≤ z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.DzIter j F z θ - Work.Spaces.DzIter j F s θ
      = ∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ := by
  -- the derivative along the slice is continuous on the interval, hence interval integrable
  have hcont' : ContinuousOn (fun r : ℝ => Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)
      (Set.uIcc s z) := by
    rw [Set.uIcc_of_le hsz]
    exact ((hF.DzIter j).pz.curry_z hθ).continuousOn.mono
      (fun r hr => lt_of_lt_of_le hs hr.1)
  -- the slice is differentiable at every interior point of the interval, with derivative `pz`
  have hderiv : ∀ r ∈ Set.uIcc s z,
      HasDerivAt (fun r : ℝ => Work.Spaces.DzIter j F r θ)
        (Work.Spaces.pz (Work.Spaces.DzIter j F) r θ) r := by
    intro r hr
    rw [Set.uIcc_of_le hsz] at hr
    exact hF.hasDerivAt_slice_DzIter j hθ (lt_of_lt_of_le hs hr.1)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont'.intervalIntegrable).symm

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.GbarSin.continuousOn_HkIntegrand_radial_sin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.GbarSin

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The angular profile `sinIter i` is continuous -/



/-! ## The mixed derivative of a radial profile times `sin 2θ` -/


/-! ## The weight `Wt` is continuous on the open quadrant -/

/-- `Wt α z θ = w(z)·sin(2θ)^{-γ/2}` is continuous on the open quadrant, where
`z ≠ 0` and `sin(2θ) > 0`. -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1))
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-! ## The main lemma -/


end Work.FTS.EllipticEst.GbarSin
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.ShiftC.integrableOn_sinCos2_pzIter2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W/ShiftC/integrableOn_sinCos2_pzIter2`

Box integrability of `sinθcos²θ·|∂_z²Ψ|` from the box integrability of the *difference*
`sinθcos²θ·|Lzero Ψ − F|` and of `sinθcos²θ·|∂_zΨ|`, granted the equation `bslOp α Ψ = F` on the
open quadrant.

The whole content is the *level identity* (`Lzero_eq_bslOp_add_radial_pz2`)

  `Lzero Ψ = F + α²z²∂_z²Ψ + α(5+α)z ∂_zΨ`   on `(0,∞) × (0,π/2)`,

which on a box `[a,b] × Iθ` with `0 < a < b` gives the pointwise bound

  `|∂_z²Ψ(s,θ)| ≤ (|Lzero Ψ − F| + α(5+α)·b·|∂_zΨ(s,θ)|) / (α²·a²)`,

so that after multiplication by the nonnegative weight `sinθcos²θ` the target integrand is
dominated by a constant multiple of the sum of the two integrable integrands.  The a.e. strong
measurability of the target comes from the `C^∞`-smoothness of `Ψ` on the open quadrant
(`SmoothOpen`), the level identity holding a.e. on the box (the exceptional set being contained in
the two null lines `θ = 0`, `θ = π/2`).

Every declaration in this file is fully proved and rests only on the axioms
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.EllipticEst.H2W.ShiftC

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## The elementary angular fact -/


/-! ## The level identity on the open quadrant, and almost everywhere on a box -/



/-! ## A.e. strong measurability on a box of a function continuous on the open quadrant -/


/-! ## The main theorem -/


end

end Work.FTS.EllipticEst.H2W.ShiftC
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Slot11Src.integrableOn_mixed_slot_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Slot11Src

set_option autoImplicit false

/-- The weight `W = w(z)·sin(2θ)^{-γ/2}` is continuous on the open quadrant
`(0,∞) × (0,π/2)`, where both factors are finite. -/
private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    rw [Set.mem_prod] at hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    rw [Set.mem_prod] at hp
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  have hsin : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact hw.mul hsin

/-- **Integrability in `z` of one mixed slot of the `ℋ^k`-integrand.**

For `f` of class `C^∞` on the open quadrant and honestly in `ℋ^k`, the function
`z ↦ ∫_θ (D_z^j D_θ^i f · W)²` is integrable on `Iz = [0,∞)`, for every slot with
`1 ≤ i` and `i + j ≤ k`: the summand is one of the (nonnegative) summands of
`HkIntegrand α k f`, so its `θ`-slice integral is dominated by the `θ`-slice integral of
`HkIntegrand α k f`, whose `z`-integral is integrable by `hmem`.  The only thing needed on
top of the pointwise domination is the a.e. strong measurability of that `z`-integral,
which comes from the continuity of the slot on the open quadrant (the complement of the
quadrant inside `Iz × Iθ` is null for the product measure). -/
theorem integrableOn_mixed_slot_sq (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz := by
  -- The slot square is jointly continuous on the open quadrant.
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (((hf.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)).pow 2
  -- Hence its `z`-slice integrals are a.e. strongly measurable.
  have haesm : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2
        * Work.Spaces.Wt α p.1 p.2) ^ 2) hcont).integral_prod_right'
  -- Domination by the `ℋ^k`-integrand, whose `z`-slice integral is integrable.
  refine Integrable.mono' hmem.2 haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) (fun z hz => ?_)
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
    integral_nonneg_of_ae (Eventually.of_forall fun θ => sq_nonneg _)
  rw [Real.norm_of_nonneg hnn]
  exact integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 z hz)
    (Eventually.of_forall fun θ =>
      Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij)

end Work.FTS.EllipticEst.H2W.Slot11Src
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.lzero1SliceGrowth =====
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
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! The `C²`-version of the Wronskian chain of `H2W.lzeroGrowthSlice`.  The definitions
`Dfun`, `Rfun`, `Mfun`, `Bfun` and the smoothness-free elementary lemmas are imported from
`Work.FTS.EllipticEst.H2W.LzeroGrowth`; only the lemmas whose proof consumed the smoothness
hypothesis are redone here, at `ContDiffOn ℝ 2`. -/
namespace Lzero1Growth

open LzeroGrowth

/-! ## Derivative bookkeeping at `C²` -/

theorem hasDerivAt_u {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : HasDerivAt u (deriv u θ) θ :=
  (hasDerivAt_of_contDiffOn isOpen_Ioo hu).1 θ hθ


theorem continuousOn_deriv1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
  (hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn

theorem continuousOn_deriv2 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun θ => deriv (deriv u) θ) (Set.Ioo 0 (Real.pi / 2)) :=
  ((hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).deriv_of_isOpen isOpen_Ioo
    (m := 0) (by norm_num)).continuousOn

theorem continuousOn_tan_mul {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun θ => deriv (fun t => Real.tan t * u t) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hc0 : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn
  have hc1 : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) := continuousOn_deriv1 hu
  have hg : ContinuousOn
      (fun θ : ℝ => (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun θ : ℝ => 1 / Real.cos θ ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
      refine ContinuousOn.div continuousOn_const (Real.continuous_cos.continuousOn.pow 2) ?_
      intro θ hθ
      exact pow_ne_zero 2 (cos_ne_zero hθ)
    have h2 : ContinuousOn (fun θ : ℝ => Real.tan θ * deriv u θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      have ht : ContinuousOn Real.tan (Set.Ioo 0 (Real.pi / 2)) :=
        Real.continuousOn_tan.mono (fun x hx => cos_ne_zero hx)
      rw [show (fun θ : ℝ => Real.tan θ * deriv u θ) = Real.tan * deriv u from rfl]
      exact ht.mul hc1
    exact (h1.mul hc0).add h2
  refine ContinuousOn.congr hg ?_
  intro θ hθ
  show deriv (fun t => Real.tan t * u t) θ
    = (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ
  have hm' : HasDerivAt (fun t => Real.tan t * u t)
      ((1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ) θ :=
    (Real.hasDerivAt_tan (cos_ne_zero hθ)).mul (hasDerivAt_u hu hθ)
  rw [hm'.deriv]

/-- `Lzero1 u` is continuous on the open interval (only `C²` is needed). -/
theorem continuousOn_Lzero1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) := by
  have hc0 : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn
  have hc2 : ContinuousOn (fun θ => deriv (deriv u) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_deriv2 hu
  have hm : ContinuousOn (fun θ => deriv (fun t => Real.tan t * u t) θ)
      (Set.Ioo 0 (Real.pi / 2)) := continuousOn_tan_mul hu
  refine ContinuousOn.congr (f := fun θ =>
    -(deriv (deriv u) θ) + deriv (fun t => Real.tan t * u t) θ - 6 * u θ) ?_ ?_
  · exact ((hc2.neg).add hm).sub (hc0.const_mul 6)
  · intro θ hθ
    simp only [Work.FTS.EllipticEst.Lzero1]


/-! ## The two exact identities -/




/-! ## The bound on `Dfun` and the two growth bounds for `Rfun` -/








/-! ## From the two `Rfun` bounds to the pointwise growth of `u` -/



end Lzero1Growth


end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.pzIterSliceGrowth3LocReduction =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W/pzIterSliceGrowth3LocReduction` — the reduction of the locally uniform slice growth to a
source-mass bound

Target of the node `Work.FTS.EllipticEst.H2W.pzIterSliceGrowth3Loc`: for a datum
`WeakPos2 α F Ψ` (`0 < α ≤ 1/4`) and for almost every `z₀ > 0` there is `ε ∈ (0, z₀)` and a
*single* constant `C ≥ 0` with

  `|∂_z^j Ψ(z,θ)| ≤ C·(θ⁻¹ + (π/2-θ)⁻¹)`  for all `j ≤ 3`, all `z ∈ (z₀-ε, z₀+ε)`,
  all `θ ∈ (0, π/2)`.

This file proves the **reduction**: the target follows from the *locally uniform* bound on the
pole-weighted `L¹` **mass of the source of each of the four slices** together with the same
quantity's local boundedness at the reference angle `π/4` (`SliceSourceMassBound` below).

## What is genuinely new here

The sibling node `H2W/pzIterPoleBoundUpTo4` proves the *almost everywhere in `z`* version of the
same conclusion (for `m ≤ 4`) by extracting, for each `z` separately, a constant from the
one-variable theorem `WeakPureAux.lzeroSlicePoleBound`, whose conclusion is an `∃ C`.  That
extraction is *not* uniform in `z`: the constant of the one-variable theorem is a function of the
slice's source mass and of the slice's data at `π/4`, and the theorem does not record the
dependence.  For the *local* (uniform in `z`) form one needs the quantitative version

> `SliceB.lzeroGrowthQuantL1` — `|u θ| ≤ C·(K u + |u(π/4)| + |u'(π/4)|)·(θ⁻¹ + (π/2-θ)⁻¹)` with a
> *universal* `C` and `K u := ∫_{Iθ} sinθcos²θ·|Lzero1 u|`,

which this file consumes.  With it the reduction is mechanical:

* the slice `θ ↦ ∂_z^m Ψ(z,·)` is `C^∞` on `(0,π/2)` for every `z > 0` (the class is `C^∞` on the
  open quadrant), so the quantitative theorem applies to it;
* the source-mass term is bounded uniformly on the neighbourhood by the hypothesis;
* the *data* term `|∂_z^mΨ(z,π/4)| + |∂_θ∂_z^mΨ(z,π/4)|` is *continuous in `z`*, hence bounded on
  the compact interval `[z₀-ε, z₀+ε]` — this is what makes the constant uniform in `z`
  (`exists_sliceData_bound_single`), and it uses only the `C^∞` clause of the class.

## The remaining input

`SliceSourceMassBound Ψ` is *not* a consequence of `WeakPos2` by any argument available in the
tree: the source of the `m`-th slice is
`∂_z^m F + α²z²∂_z^{m+2}Ψ + (2α²m + α(5+α))z∂_z^{m+1}Ψ + (α²m(m-1) + α(5+α)m)∂_z^mΨ`
(see `H2W/pzIterPoleBoundUpTo4`), so its mass involves the slices at levels `m+1`, `m+2` and, at
the top level `m = 3`, the honesty of `∂_z³F`, which the class does not provide.  See
`NOTES_pzIterSliceGrowth3Loc_reduction.md` beside this file (the regress has no base case; the
statement is the chapter's level-`0` bottleneck in its locally uniform form).
-/

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## The `θ`-slices of the iterated `z`-derivatives are `C^∞` on the open angular interval -/

/-- The `θ`-slices `θ ↦ ∂_z^m Ψ(z,θ)` of a datum which is `C^∞` on the open quadrant are `C^∞`
on `(0, π/2)` at every `z > 0`, at every order. -/
theorem contDiffOn_slice_pzIter {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) (m : ℕ) :
    ∀ n : ℕ, ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.pzIter m Ψ z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hQ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hcur := (hQ.pzIter m).curry_θ hz
  intro n
  exact (contDiffOn_iff_forall_nat_le.mp hcur) n le_top

/-! ## The data term at `θ = π/4` is locally bounded in `z` -/


/-! ## The source-mass hypothesis -/


/-! ## The reduction -/


end

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.pzIter_slice_FTC_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

theorem pzIter_slice_FTC_open {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (j : ℕ) {s z θ : ℝ} (hs : 0 < s) (hsz : s ≤ z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pzIter j F z θ - Work.Spaces.pzIter j F s θ
      = ∫ r in s..z, Work.Spaces.pzIter (j + 1) F r θ := by
  -- the derivative along the slice is continuous on the interval, hence interval integrable
  have hcont' : ContinuousOn (fun r : ℝ => Work.Spaces.pzIter (j + 1) F r θ)
      (Set.uIcc s z) := by
    rw [Set.uIcc_of_le hsz]
    exact ((hF.pzIter j).pz.curry_z hθ).continuousOn.mono
      (fun r hr => lt_of_lt_of_le hs hr.1)
  -- the slice is differentiable at every point of the interval, with derivative the next partial
  have hderiv : ∀ r ∈ Set.uIcc s z,
      HasDerivAt (fun r : ℝ => Work.Spaces.pzIter j F r θ)
        (Work.Spaces.pzIter (j + 1) F r θ) r := by
    intro r hr
    rw [Set.uIcc_of_le hsz] at hr
    exact hF.hasDerivAt_slice_pzIter j hθ (lt_of_lt_of_le hs hr.1)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont'.intervalIntegrable).symm

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.AesmCross.aesmProdCross =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.AesmCross

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## Continuity of the two weights on the open quadrant

The point of these two elementary lemmas is that they are *local to the open quadrant*: the
radial weight `w2 z = ((1+z)²/z²)²` is continuous wherever `z ≠ 0`, and the angular weight
`sig θ = sin(2θ)^{-η}` is continuous wherever `sin(2θ) ≠ 0`; both conditions hold on
`Q0 = (0,∞) × (0,π/2)`.  Nothing is asserted on the boundary `z = 0` or `θ ∈ {0, π/2}`,
which is all that is needed since that boundary is null. -/

/-- The radial factor `w2 z = w z ^ 2` of the weight is continuous on the open quadrant. -/
lemma continuousOn_w2_quadrant :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.w2 p.1)
      Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.w2 p.1)
      = fun p : ℝ × ℝ => (((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2) := by
    funext p
    rw [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]
  rw [hfun]
  refine ContinuousOn.pow ?_ 2
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))

/-- The angular factor `sig θ = sin(2θ)^{-η}` of the weight is continuous on the open
quadrant. -/
lemma continuousOn_sig_quadrant :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.sig p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.sig p.2)
      = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
    funext p
    rw [Work.FTS.EllipticEst.AngSecond.sig]
  rw [hfun]
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- **The product of two functions, each of which agrees on the open quadrant with a smooth
function, is a.e. strongly measurable** for the product of the restrictions of Lebesgue
measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`.

Indeed, on the open quadrant the product `g · h` coincides with the product `g' · h'` of the
two smooth representatives, and `g' h' w2 σ` is continuous there (the two weights being
continuous on the quadrant, so that no boundary behaviour of `w2` at `z = 0` or of `σ` at
`θ = 0, π/2` is ever used); the complement of the open quadrant inside `Iz ×ˢ Iθ` is
contained in the three coordinate hyperplanes and hence is null. -/
theorem aesmProdCross {g h g' h' : ℝ → ℝ → ℝ} (hg' : Work.FTS.EllipticEst.SmoothOpen g')
    (hh' : Work.FTS.EllipticEst.SmoothOpen h')
    (hgg : Work.FTS.EllipticEst.AgreeOnQ g g') (hhh : Work.FTS.EllipticEst.AgreeOnQ h h') :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.1 p.2 * h p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
        * Work.FTS.EllipticEst.AngSecond.sig p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- `Iz` and `Iθ` agree a.e. with the open half-line and the open interval, so the product of
  -- the restricted measures is the restriction of the planar Lebesgue measure to the quadrant.
  have hz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume] Work.FTS.EllipticEst.Q0 :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  have hμ : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (MeasureTheory.volume.prod MeasureTheory.volume).restrict Work.FTS.EllipticEst.Q0 := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_congr_set hprod
  rw [hμ]
  -- The smooth representative is continuous on the open quadrant, hence a.e. strongly measurable.
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => g' p.1 p.2 * h' p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
        * Work.FTS.EllipticEst.AngSecond.sig p.2) Work.FTS.EllipticEst.Q0 :=
    ((hg'.continuousOn.mul hh'.continuousOn).mul continuousOn_w2_quadrant).mul
      continuousOn_sig_quadrant
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => g' p.1 p.2 * h' p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
        * Work.FTS.EllipticEst.AngSecond.sig p.2)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict Work.FTS.EllipticEst.Q0) := by
    rw [← hμ]
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  -- Transfer along the a.e. equality on the (conull) open quadrant.
  refine haesm.congr ?_
  refine (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume.prod MeasureTheory.volume)
    (s := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0.measurableSet).mpr ?_
  refine Eventually.of_forall fun p hp => ?_
  obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  show g' p.1 p.2 * h' p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
      * Work.FTS.EllipticEst.AngSecond.sig p.2
    = g p.1 p.2 * h p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
      * Work.FTS.EllipticEst.AngSecond.sig p.2
  rw [hgg p.1 p.2 hz0 hθ0 hθ1, hhh p.1 p.2 hz0 hθ0 hθ1]

end Work.FTS.EllipticEst.Honest.AesmCross
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.AesmCross.aesmSliceCross =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest.AesmCross

/-- **A slice of a function agreeing with a `C^∞`-on-`Q0` function.**  If `F'` is `C^∞` on the
open quadrant and `F` agrees with `F'` on the open quadrant, then for every `z > 0` the angular
slice `θ ↦ F z θ` is a.e. strongly measurable for the measure `volume.restrict Iθ`.

Indeed the slice map `θ ↦ (z, θ)` sends the open interval `(0, π/2)` into the open quadrant, so on
`(0, π/2)` the slice of `F` coincides with the (continuous) slice of `F'`; and `(0, π/2)` equals
`Iθ` up to the null endpoints. -/
theorem aesm_slice_of_agreeOnQ {F F' : ℝ → ℝ → ℝ}
    (hF' : Work.FTS.EllipticEst.SmoothOpen F') (hF : Work.FTS.EllipticEst.AgreeOnQ F F')
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable (fun θ => F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  -- On the open interval the slice of `F` is the slice of `F'`, which is continuous there.
  have hcont : ContinuousOn (fun θ : ℝ => F z θ) (Set.Ioo 0 (π / 2)) :=
    (hF'.curry_θ hz).continuousOn.congr fun θ hθ => hF z θ hz hθ.1 hθ.2
  have h1 : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => F z θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  -- `(0, π/2)` and `Iθ = [0, π/2]` differ by the two null endpoints.
  have hset : (Set.Ioo (0 : ℝ) (π / 2)) =ᵐ[MeasureTheory.volume]
      (Set.Icc (0 : ℝ) (π / 2)) := MeasureTheory.Ioo_ae_eq_Icc
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    (MeasureTheory.Measure.restrict_congr_set hset).symm
  rw [hmeas]
  exact h1

/-- **The angular weight `σ θ = sin(2θ)^{-η}`** is a.e. strongly measurable for the measure
`volume.restrict Iθ`: it is continuous on the open interval `(0, π/2)`, where `sin(2θ) > 0`. -/
theorem aesm_sig : MeasureTheory.AEStronglyMeasurable
    (fun θ => Work.FTS.EllipticEst.AngSecond.sig θ)
    (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hcont : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (π / 2)) := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    simpa [Work.FTS.EllipticEst.AngSecond.sig] using
      hsin.rpow_const fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ))
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have hset : (Set.Ioo (0 : ℝ) (π / 2)) =ᵐ[MeasureTheory.volume]
      (Set.Icc (0 : ℝ) (π / 2)) := MeasureTheory.Ioo_ae_eq_Icc
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    (MeasureTheory.Measure.restrict_congr_set hset).symm
  rw [hmeas]
  exact h1

theorem aesmSliceCross {g h g' h' : ℝ → ℝ → ℝ} (hg' : Work.FTS.EllipticEst.SmoothOpen g')
    (hh' : Work.FTS.EllipticEst.SmoothOpen h')
    (hgg : Work.FTS.EllipticEst.AgreeOnQ g g') (hhh : Work.FTS.EllipticEst.AgreeOnQ h h') :
    ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.AEStronglyMeasurable
        (fun θ => g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- at `z = 0` the radial weight `w 0²` vanishes, so the slice is identically zero
    subst hz0
    refine (MeasureTheory.aestronglyMeasurable_const (b := (0 : ℝ))).congr ?_
    filter_upwards with θ
    simp [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]
  · -- for `z > 0` each factor is a.e. strongly measurable
    exact (((aesm_slice_of_agreeOnQ hg' hgg hzpos).mul
      (aesm_slice_of_agreeOnQ hh' hhh hzpos)).mul
      MeasureTheory.aestronglyMeasurable_const).mul aesm_sig

end Work.FTS.EllipticEst.Honest.AesmCross
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The hypothesis class -/

/-- **The honest class of the level-`0` `η`-weighted elliptic estimate.**  `(F,Ψ)` solves
`(PolarBSL)` on the *open* quadrant, has the Dirichlet data and the pointwise decay at `z → ∞`,
satisfies the two solvability conditions `OrthCond F`, `OrthCond Ψ`, is smooth on the open
quadrant, the three `ℋ⁰`-integrands of `F`, `z²∂_zzΨ`, `∂_θθΨ` are honest, and the two *mixed*
level-`1/2` slots of `Ψ` — the `ℋ⁰`-integrands of `z ∂_z∂_θΨ` and of `z ∂_z∂_θ²Ψ` — are honest
(the fields `memMix1`, `memMix2` below; they are the level-`1/2` honesty that the transcription
of Proposition `H2` had been carrying silently). -/
structure Hon (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : Prop where
  /-- `0 < α`. -/
  hα : 0 < α
  /-- `α ≤ 1/4`. -/
  hα4 : α ≤ 1 / 4
  /-- `(PolarBSL)` holds on the open quadrant. -/
  eq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ
  /-- The Dirichlet datum at `θ = 0`. -/
  d0 : ∀ z, Ψ z 0 = 0
  /-- The Dirichlet datum at `θ = π/2`. -/
  dπ : ∀ z, Ψ z (π / 2) = 0
  /-- Pointwise decay at `z → ∞`. -/
  dec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (nhds 0)
  /-- The solvability condition on the source. -/
  orthF : Work.Elliptic.OrthCond F
  /-- The solvability condition on the solution (Step 1 of `prop:L2`). -/
  orthΨ : Work.Elliptic.OrthCond Ψ
  /-- Smoothness on the open quadrant. -/
  sm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
  /-- Honesty of the source. -/
  memF : Work.Spaces.HkMem α 0 F
  /-- Honesty of `z²∂_zzΨ`. -/
  memA : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  /-- Honesty of `∂_θθΨ`. -/
  memB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)
  /-- **The mixed `(1,1)`-slot honesty: the level-`0` honesty of `z ∂_z∂_θΨ`.**

  This is *not* a consequence of the fields above; it is the level-`1/2` honesty that the
  transcription of Proposition `H2` had been carrying silently, and that the workspace records as
  one of the two exact obstructions to the `I₁` coercivity of Step 2
  (`Final/NOTES_honI1Lower_session_revival.md` §2, "Wall A").  Its role is to make the a.e.-`z`
  angular traces of `G = z∂_zΨ` vanish: `HkMem α 0 (z∂_z∂_θ²Ψ)`-type slice data plus this field
  gives `Final/honGSliceTraceAe`, hence `Final/honGHNonpos`.  Data constructed by *converting*
  from a class that has the regularity (`EllHyp`, `SmoothNbhd`, `SmN`, or the paper's data, which
  is smooth on a closed neighbourhood of the quadrant and compactly supported in `z`) satisfies
  it. -/
  memMix1 : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pth Ψ) z θ)
  /-- **The mixed `(1,2)`-slot honesty: the level-`0` honesty of `z ∂_z∂_θ²Ψ`.**

  This is the second of the two level-`1/2` slots, and the hypothesis of the `z`-integration by
  parts engine `H2W.WeakAux.I1_ibp_identity_open` that drives the `I₁` coercivity
  (`Final/honI1Lower_of_mixedHon`, whose conclusion is verbatim the `I₁` slot consumed by
  `Honest.step3BAngularClean`, hence by `Honest.step2Angular` and by the Step-3 angular estimate
  `Final.step3Angle_fts`). -/
  memMix2 : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)

/-! ## The angular weight and its elementary algebra -/

/-- `sin(2θ) ≥ 0` on `Iθ = [0,π/2]`. -/
theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- **The elementary algebra of the angular weight**: for `0 ≤ s`,
`(w / s^{η/2})² = w² · s^{-η}`. -/
theorem sq_weight_eq {w s : ℝ} (hs : 0 ≤ s) :
    (w / s ^ (Work.Spaces.eta / 2)) ^ 2 = w ^ 2 * s ^ (-(Work.Spaces.eta)) := by
  have heta : Work.Spaces.eta ≠ 0 := by norm_num [Work.Spaces.eta]
  have hhalf : Work.Spaces.eta / 2 ≠ 0 := by positivity
  rcases eq_or_lt_of_le hs with h0 | hpos
  · subst h0
    rw [Real.zero_rpow hhalf, div_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), Real.zero_rpow (neg_ne_zero.mpr heta)]
    ring
  · have hsq : (s ^ (Work.Spaces.eta / 2)) ^ 2 = s ^ Work.Spaces.eta := by
      rw [sq, ← Real.rpow_add hpos]
      congr 1
      norm_num [Work.Spaces.eta]
    rw [div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hpos)]

/-! ## The level-`0` integrand, and the identification of `HkSq α 0` with the `IP`-pairing -/

/-- **The level-`0` `HkSq`-integrand.**  At level `0` the mixed-derivative sum of
`Work.Spaces.HkIntegrand` is empty, so the integrand is the single square
`(g z θ · w z / sin(2θ)^{η/2})²`. -/
theorem HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.pzIter_zero, Finset.range_one,
    Finset.sum_singleton]
  norm_num

/-- **`HkSq α 0` as the iterated integral of the square of the weighted profile.** -/
theorem HkSq_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ =>
    HkIntegrand_zero_eq α g z θ

/-- The pointwise identity behind `IP_self_eq_HkSq`, on the angular interval. -/
theorem sq_profile_eq (g : ℝ → ℝ → ℝ) (z θ : ℝ) (hsin : 0 ≤ Real.sin (2 * θ)) :
    (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [mul_pow, sq_weight_eq hsin]
  ring

/-- **`HkSq α 0 g` is the `IP`-pairing of `g` with itself**:
`IP g g = ∫_z ∫_θ g² w² σ = HkSq α 0 g`. -/
theorem IP_self_eq_HkSq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    AngSecond.IP g g = Work.Spaces.HkSq α 0 g := by
  rw [HkSq_zero_eq]
  unfold AngSecond.IP
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  unfold AngSecond.w2 AngSecond.sig
  simp only [sq_profile_eq g z θ (sin_two_nonneg_of_mem_Iθ hθ)]
  ring

/-! ## Nonnegativity and homogeneity -/

theorem HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand]
  refine add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity

/-- The level-`0` `HkSq` of any function is nonnegative. -/
theorem HkSq_zero_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.HkSq α 0 g := by
  rw [Work.Spaces.HkSq]
  exact integral_nonneg fun z => integral_nonneg fun θ => HkIntegrand_nonneg α 0 g z θ

/-- `(√ (HkSq α 0 g))² = HkSq α 0 g`. -/
theorem hksq_sqrt_sq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    (Real.sqrt (Work.Spaces.HkSq α 0 g)) ^ 2 = Work.Spaces.HkSq α 0 g :=
  Real.sq_sqrt (HkSq_zero_nonneg α g)

/-- **Homogeneity of `HkSq α 0` under multiplication by a constant.** -/
theorem HkSq_zero_const_mul (α c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 (fun z θ => c * g z θ) = c ^ 2 * Work.Spaces.HkSq α 0 g := by
  rw [HkSq_zero_eq, HkSq_zero_eq]
  rw [show (fun z => ∫ θ in Work.Spaces.Iθ, (c * g z θ *
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 from by
    funext z
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [← MeasureTheory.integral_const_mul]


/-! ## Monotonicity of `HkSq α 0` -/


/-! ## The equation, rearranged -/

/-- **`(PolarBSL)` solved for the second derivatives.**  On the open quadrant,
`α² z²∂_zzΨ = -F - α(5+α) z∂_zΨ - ∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`, which is the equation in the
form used by Step 3 of the estimate. -/
theorem Hon.eq_solve {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      = -F z θ - α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)
        - Work.Spaces.pthIter 2 Ψ z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ := by
  have hb := h.eq z hz θ h0 h1
  rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at hb
  linarith [hb]


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.integrable_hkIntegrand_prod =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine

theorem integrable_hkIntegrand_prod {α : ℝ} {k : ℕ} {Z : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry (fun s θ => Work.Spaces.HkIntegrand α k Z s θ))
      Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α k Z) :
    MeasureTheory.Integrable
      (Function.uncurry (fun s θ => Work.Spaces.HkIntegrand α k Z s θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- `HkIntegrand` is a sum of squares, so Tonelli's criterion in its iterated form applies:
  -- the integrand is continuous on the open quadrant (hence a.e. strongly measurable for
  -- `(dz)|_{Iz} ⊗ (dθ)|_{Iθ}`), its angular slices are integrable and the outer integral is
  -- integrable -- the last two are the two halves of `HkMem`.
  refine (Work.Spaces.integrable_prod_of_iterated
    (fun a b => Work.Spaces.HkIntegrand_nonneg α k Z a b)
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont) ?_ ?_).1
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    exact hmem.1 z hz
  · exact hmem.2

end Work.FTS.EllipticEst.Mine
end
-- ===== merged: Submission.Work.FTS.EllipticEst.PsiInt_sq_mul_w_le_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## The elementary angular facts (local copies) -/

/-- `sin(2θ) ≥ 0` on `Iθ = [0,π/2]`. -/
private theorem sin_two_nonneg_loc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) ≤ 1`. -/
private theorem sin_two_le_one_loc (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `|sinθ cos²θ| ≤ 1` on `Iθ`. -/
private theorem abs_sinCos2_le_one_loc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  have hsin : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg (Real.cos θ)) hcos 2
    rw [sq_abs] at h
    simpa using h
  have hcos2nn : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  calc |Work.Elliptic.sinCos2 θ| = |Real.sin θ| * Real.cos θ ^ 2 := by
        rw [Work.Elliptic.sinCos2, abs_mul, abs_of_nonneg hcos2nn]
    _ ≤ 1 := by nlinarith [hsin, hcos2, abs_nonneg (Real.sin θ)]

/-- `sinθ cos²θ` vanishes wherever `sin 2θ` does. -/
private theorem sinCos2_eq_zero_of_sin_two_eq_zero_loc {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.Elliptic.sinCos2 θ = 0 := by
  have h2 : Real.sin θ * Real.cos θ = 0 := by
    have h3 : 2 * (Real.sin θ * Real.cos θ) = 0 := by
      rw [← h, Real.sin_two_mul]; ring
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  rcases mul_eq_zero.mp h2 with h3 | h3
  · simp [Work.Elliptic.sinCos2, h3]
  · simp [Work.Elliptic.sinCos2, h3]

/-- A function on `Iθ` bounded by a constant is integrable there. -/
private theorem integrableOn_Iθ_of_abs_le_loc {f : ℝ → ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ)) {C : ℝ}
    (h : ∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ C) : IntegrableOn f Work.Spaces.Iθ := by
  refine Integrable.mono'
    (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := C)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) hm ?_
  rw [Work.Spaces.Iθ, ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun θ hθ => by simpa [Real.norm_eq_abs] using h θ hθ

/-- The cross-term identity of Cauchy--Schwarz for the radial moment. -/
private theorem cs_cross_eq_loc (u : ℝ → ℝ → ℝ) (j : ℕ) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter j u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      * (Work.Elliptic.sinCos2 θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        / Work.Spaces.w z)
    = Work.Spaces.DzIter j u z θ * Work.Elliptic.sinCos2 θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_loc hθ
  have hW : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 hz.ne')
  have he : Work.Spaces.eta / 2 ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  by_cases hs : Real.sin (2 * θ) = 0
  · have hc : Work.Elliptic.sinCos2 θ = 0 := sinCos2_eq_zero_of_sin_two_eq_zero_loc hs
    rw [hs, Real.zero_rpow he, div_zero, hc]
    ring
  · have hspos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hne : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≠ 0 :=
      (Real.rpow_pos_of_pos hspos _).ne'
    field_simp

/-! ## Cauchy--Schwarz for the radial moment -/

/-- **Cauchy--Schwarz for the radial moment** (open-quadrant source).  The mass of the
radial moment `PsiInt u j z` is controlled by the `j`-th `L²`-summand of the `H^k`-integrand
of `u`. -/
theorem PsiInt_sq_mul_w_le_open (u : ℝ → ℝ → ℝ) (hu : Work.FTS.EllipticEst.SmoothOpen u) (j : ℕ) {z : ℝ}
    (hz : 0 < z)
    (hU : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter j u z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ) :
    (Work.FTS.EllipticEst.PsiInt u j z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (Real.pi / 2) * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hz0 : (0 : ℝ) < z := hz
  have hIθ : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hWpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]
    exact div_pos (pow_pos (by linarith) 2) (pow_pos hz0 2)
  set V : ℝ → ℝ := fun θ => Work.Elliptic.sinCos2 θ
    * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) / Work.Spaces.w z with hVdef
  have hUmem : MemLp (fun θ : ℝ => Work.Spaces.DzIter j u z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) 2
      (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      (hu.aesm_slice_summand j hz0)).mpr hU
  have hVcont : Continuous V := by
    rw [hVdef]
    have h₁ : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ := by
      unfold Work.Elliptic.sinCos2; fun_prop
    have h₂ : Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
      refine Continuous.rpow (by fun_prop) continuous_const (fun θ => Or.inr ?_)
      rw [Work.Spaces.eta]; norm_num
    exact (h₁.mul h₂).div_const _
  have hVabs : ∀ θ ∈ Work.Spaces.Iθ, |V θ| ≤ 1 / Work.Spaces.w z := by
    intro θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_loc hθ
    have hpow1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hs0 (sin_two_le_one_loc θ) (by rw [Work.Spaces.eta]; norm_num)
    have habs : |Work.Elliptic.sinCos2 θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0 _)]
      calc |Work.Elliptic.sinCos2 θ| * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          ≤ 1 * 1 := mul_le_mul (abs_sinCos2_le_one_loc hθ) hpow1
            (Real.rpow_nonneg hs0 _) zero_le_one
        _ = 1 := by ring
    rw [hVdef, abs_div, abs_of_pos hWpos]
    exact div_le_div_of_nonneg_right habs hWpos.le
  have hV2 : IntegrableOn (fun θ : ℝ => (V θ) ^ 2) Work.Spaces.Iθ := by
    refine integrableOn_Iθ_of_abs_le_loc (hVcont.aestronglyMeasurable.pow 2)
      (C := (1 / Work.Spaces.w z) ^ 2) ?_
    intro θ hθ
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (abs_nonneg (V θ)) (hVabs θ hθ) 2
    rwa [sq_abs] at h
  have hVmem : MemLp V 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hVcont.aestronglyMeasurable).mpr hV2
  have hcs := Work.Spaces.cs_integral hUmem hVmem
  have hcross : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) * V θ)
      = PsiInt u j z := by
    rw [PsiInt]
    exact setIntegral_congr_fun hIθ (fun θ hθ => by rw [hVdef]; exact cs_cross_eq_loc u j hz0 hθ)
  have hVb : ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 ≤ (Real.pi / 2) / (Work.Spaces.w z) ^ 2 := by
    have hconst : ∫ θ in Work.Spaces.Iθ, (1 / Work.Spaces.w z) ^ 2
        = (Real.pi / 2) / (Work.Spaces.w z) ^ 2 := by
      have hvol : volume.real Work.Spaces.Iθ = Real.pi / 2 := by
        rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
        ring
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
      ring
    rw [← hconst]
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
      (integrableOn_const (s := Work.Spaces.Iθ) (C := (1 / Work.Spaces.w z) ^ 2)
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) ?_
    show ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), (V θ) ^ 2 ≤ (1 / Work.Spaces.w z) ^ 2
    rw [ae_restrict_iff' hIθ]
    exact Eventually.of_forall fun θ hθ => by
      have h := pow_le_pow_left₀ (abs_nonneg (V θ)) (hVabs θ hθ) 2
      rwa [sq_abs] at h
  have hA : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j u z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    integral_nonneg fun θ => sq_nonneg _
  have hstep : (PsiInt u j z) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter j u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      * ((Real.pi / 2) / (Work.Spaces.w z) ^ 2) := by
    rw [hcross] at hcs
    exact le_trans hcs (mul_le_mul_of_nonneg_left hVb hA)
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hWpos.ne'
  calc (PsiInt u j z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          * ((Real.pi / 2) / (Work.Spaces.w z) ^ 2)) * (Work.Spaces.w z) ^ 2 :=
        mul_le_mul_of_nonneg_right hstep (sq_nonneg _)
    _ = (Real.pi / 2) * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_assoc, div_mul_cancel₀ (Real.pi / 2) hw2, mul_comm]

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.MixedAGN_finite =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RPFresh


end Work.FTS.EllipticEst.RPFresh
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.OpIdentMixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false

/-! ## Congruence of the iterated `D_z` on an open set -/

/-- The iterated operator `D_z^j` is local: two functions which agree on an open set `V` have
equal `D_z^j` at every point of `V`. -/
lemma DzIter_congr_of_isOpen {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j g))
      (Function.uncurry (Work.Spaces.DzIter j g')) V := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
      intro y hy
      have hp := Work.Spaces.pz_congr_of_isOpen hV ih hy
      show y.1 * Work.Spaces.pz (Work.Spaces.DzIter j g) y.1 y.2
        = y.1 * Work.Spaces.pz (Work.Spaces.DzIter j g') y.1 y.2
      rw [hp]

/-! ## `D_z` commutes with the iterates of `D_θ`, at the genuine smooth order -/

/-- On an open set `V` on which `g` is `C^∞` in the genuine smooth order
`Work.Stability.smoothOrder`, the operator `D_z` commutes with every iterate of `D_θ`:
`D_z (D_θ^i g) = D_θ^i (D_z g)` on `V`.  (The smooth-order counterpart of
`Work.Spaces.DzDthIterCommOn`.) -/
lemma Dz_DthIter_comm_of_isOpen {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      -- `D_θ^i g` is `C^∞`, hence `C²`, at the point `y`: Clairaut applies.
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
      -- The two functions now agree on the open set `V` by the induction hypothesis, so their
      -- `θ`-derivatives agree at `y`.
      show Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-! ## The identity -/

theorem OpIdentMixed {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (i j : ℕ) {z θ : ℝ}
    (hz : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Spaces.pth V)) z θ
      = Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ := by
  -- `∂_θ V` is `C^∞` on the open quadrant `Q0`.
  have hgp : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth V)) Work.FTS.EllipticEst.Q0 := hV.pth
  -- `D_z` commutes with `D_θ^i`, so the two functions agree on `Q0`.
  have hcomm := Dz_DthIter_comm_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hgp i
  -- `D_z^j` is local, so it preserves that agreement at `(z,θ)`.
  have hkey := DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hcomm.symm j
  change Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz (Work.Spaces.pth V))) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i (Work.Spaces.pth V)) z θ
  rw [show Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i (Work.Spaces.pth V))
      = Work.Spaces.DzIter j
          (Work.Spaces.Dz (Work.Spaces.DthIter i (Work.Spaces.pth V))) from
    Work.Spaces.DzIter_add_right j 1 _]
  exact hkey hz

end Work.FTS.EllipticEst.RPFresh
end
-- ===== merged: Submission.Work.FTS.EllipticEst.SmoothOpenAdd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

variable {f g F G : ℝ → ℝ → ℝ}

/-- `SmoothOpen` is closed under pointwise addition.

(Named `smoothOpen_add`, not `SmoothOpen.add`: the latter would be picked up by the dot
notation `hf.add` for `hf : SmoothOpen f`, and would then be its own recursive call.) -/
theorem smoothOpen_add (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ + g z θ) := by
  have hfun : Function.uncurry (fun z θ => f z θ + g z θ)
      = Function.uncurry f + Function.uncurry g := by
    funext p; rfl
  rw [SmoothOpen, hfun]
  exact ContDiffOn.add hf hg

/-- Two functions agreeing on the open quadrant have the same `D_z`-iterates there. -/
theorem SmoothOpen.DzIter_congr
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j F z θ = Work.Spaces.DzIter j G z θ := by
  induction j with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n F z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq]

/-- The iterated `D_z`-operator is additive on the open quadrant for `SmoothOpen` data. -/
theorem SmoothOpen.DzIter_add (hf : SmoothOpen f) (hg : SmoothOpen g) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ + g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        ((hf.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n g z' θ) z :=
        ((hg.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd : deriv (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n f z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter n g z' θ) z := deriv_add hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- The iterated `D_θ`-operator is additive on the open quadrant for `SmoothOpen` data. -/
theorem SmoothOpen.DthIter_add (hf : SmoothOpen f) (hg : SmoothOpen g) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨h1, h2⟩
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => f z θ + g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n f z θ' + Work.Spaces.DthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n f z θ') θ :=
        (((hf.DthIter n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n g z θ') θ :=
        (((hg.DthIter n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd : deriv (fun θ' => Work.Spaces.DthIter n f z θ' + Work.Spaces.DthIter n g z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter n g z θ') θ := deriv_add hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

/-- The mixed operators `D_z^j D_θ^i` are additive on the open quadrant for `SmoothOpen`
data. -/
theorem SmoothOpen.mixed_add (hf : SmoothOpen f) (hg : SmoothOpen g) (j i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := by
  intro z θ hz h1 h2
  have hcongr := SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i (fun z θ => f z θ + g z θ))
    (G := fun z θ => Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ)
    (fun z θ hz h1 h2 => SmoothOpen.DthIter_add hf hg i z θ hz h1 h2) j z θ hz h1 h2
  have hadd := SmoothOpen.DzIter_add (hf.DthIter i) (hg.DthIter i) j z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.SrcBnd.GsrcPthOne =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.SrcBnd


end Work.FTS.EllipticEst.SrcBnd
end
-- ===== merged: Submission.Work.FTS.EllipticEst.SrcBnd.SlotAESM =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.SrcBnd

open MeasureTheory Set

/-- The radius weight `w z = (1+z)²/z²` is continuous on the open quadrant: it is a rational
function whose denominator does not vanish there. -/
theorem continuousOn_w_fst_Q0 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
    Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- Iterated `∂_θ` preserves `C^∞`-smoothness on the open quadrant. -/
theorem smoothOpen_pthIter {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (n : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter n f) := by
  induction n with
  | zero => simpa using hF
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

theorem SlotAESM (n : ℕ) {σ : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hσc : ContinuousOn (fun p : ℝ × ℝ => σ p.2) Work.FTS.EllipticEst.Q0) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
        (fun θ => (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter n f z θ) ^ 2 * σ θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter n f z θ) ^ 2 * σ θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  -- The uncurried integrand of both conjuncts is continuous on the open quadrant.
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * ((Work.Spaces.pthIter n f p.1 p.2) ^ 2 * σ p.2))
      Work.FTS.EllipticEst.Q0 :=
    (continuousOn_w_fst_Q0.pow 2).mul
      (((smoothOpen_pthIter hf n).continuousOn.pow 2).mul hσc)
  constructor
  · -- Angular slices: for `z > 0` this is a.e. strong measurability of a continuous slice, and
    -- at `z = 0` the whole integrand vanishes because `w 0 = 0`.
    intro z hz
    have hz0 : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz0 with h0 | hpos
    · subst h0
      have hzero : (fun θ : ℝ => (Work.Spaces.w 0) ^ 2 *
          ((Work.Spaces.pthIter n f 0 θ) ^ 2 * σ θ)) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        simp [Work.Spaces.w]
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ =>
          (Work.Spaces.w p.1) ^ 2 * ((Work.Spaces.pthIter n f p.1 p.2) ^ 2 * σ p.2))
        hcont hpos
  · -- The `z`-integral of the joint integrand is a.e. strongly measurable for the product
    -- measure `(volume.restrict Iz) ⊗ (volume.restrict Iθ)`, hence a.e. strongly measurable
    -- for the first factor alone (the Bochner integral needs no integrability for this).
    exact (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * ((Work.Spaces.pthIter n f p.1 p.2) ^ 2 * σ p.2))
      hcont).integral_prod_right'

end Work.FTS.EllipticEst.SrcBnd
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.OpenMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ESW.OpenMem`: two structural facts, isolated from `EllHyp_certificates`

The cone of `Submission/Work/FTS/EllipticEst/EllHyp_certificates.lean` is unusable from the
`TT.est_step_weak` assembly: the latter is *imported* by `TT.propHk_core` (hence by
`remov.propHk_fts`), so anything that reaches `propHk_fts` would create an import cycle.

Two of the facts declared there are needed by `ESW.ShiftWeak` (the weak-class `D_z`-shift),
namely

* `Work.FTS.EllipticEst.SmoothOpen.zsq_mul` — `SmoothOpen Ψ → SmoothOpen (z²·Ψ)`;
* `Work.FTS.EllipticEst.HkMem_of_majorant_ae` — membership in `ℋ^k` from an a.e. majorant;

this module reproduces both, verbatim, under the namespace `Work.FTS.EllipticEst.TT.ESW` and
with the (clean) cone `Spaces.Defs + OpenQDefs + FTS.LocData.HkMem_of_majorant`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Multiplication of a `SmoothOpen` function by `z ^ 2` keeps it `SmoothOpen`. -/
theorem SmoothOpen_zsq_mul {Ψ : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Ψ z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => z ^ 2 * Ψ z θ)) Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (fun z θ => z ^ 2 * Ψ z θ)
      = fun p : ℝ × ℝ => p.1 ^ 2 * Ψ p.1 p.2 from rfl]
  have hu' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hu
  exact ((contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).pow 2).mul hu'

/-- **Membership in `ℋ^k` by an almost-everywhere majorant.**  The closed-quadrant version
`Work.FTS.LocData.HkMem_of_majorant` requires the domination at every point of
`[0,∞) × [0,π/2]`; here it is only required for almost every interior angle. -/
theorem HkMem_of_majorant_ae (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      Work.FTS.EllipticEst.Q0)
    (hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Set.Icc 0 (π / 2) := MeasureTheory.Ioo_ae_eq_Icc
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iθ := by
    intro z hz
    show IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) (Set.Icc 0 (π / 2))
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
      exact (Work.FTS.LocData.HkIntegrand_zero_fst α k f θ).symm
    · refine MeasureTheory.IntegrableOn.congr_set_ae ?_ hIoo.symm
      have hMioo : IntegrableOn (fun θ => M z θ) (Set.Ioo 0 (π / 2)) :=
        (hMslice z hz).congr_set_ae hIoo
      have hsl : ContinuousOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
          (Set.Ioo 0 (π / 2)) :=
        Work.FTS.LocData.continuousOn_slice_theta (G := Work.Spaces.HkIntegrand α k f) hcont hz0
      refine MeasureTheory.Integrable.mono' hMioo
        (hsl.aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [hle z hz] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
      exact hθ
  have houter : IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := by
    have hKnn : ∀ z ∈ Work.Spaces.Iz,
        0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
    have hKle : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
      intro z hz
      have hIθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (π / 2) := by
        show Set.Icc (0 : ℝ) (π / 2) =ᵐ[volume] Set.Ioo 0 (π / 2)
        exact hIoo.symm
      rw [MeasureTheory.setIntegral_congr_set hIθ,
        MeasureTheory.setIntegral_congr_set hIθ]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
        ((hMslice z hz).congr_set_ae hIoo) ?_
      filter_upwards [hle z hz] with θ hθ
      exact hθ
    refine MeasureTheory.Integrable.mono' hMz ?_ ?_
    · have hprod : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact hcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      have h1 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict (Set.Ioi 0)) :=
        hprod.integral_prod_right'
      have h2 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict Work.Spaces.Iz) := by
        rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
        exact h1
      have hfun : (fun z => ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.HkIntegrand α k f z θ)
          = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
        funext z
        exact MeasureTheory.setIntegral_congr_set hIoo
      rw [← hfun]
      exact h2
    · have hbnd : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
          ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ‖
            ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
        exact Filter.Eventually.of_forall fun z hz => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hKnn z hz)]
          exact hKle z hz
      exact hbnd
  exact ⟨hslice, houter⟩

end Work.FTS.EllipticEst.TT.ESW
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open =====
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

/-! ## `HkMem` descends in the order, on the open-quadrant regularity class

`Work.Spaces.HkMem α k f` says that the `ℋ^k`-integrand of `f` has honest iterated
integrals over `Iz × Iθ` (`dz dθ`).  Since `HkIntegrand α (k+1) f` is obtained from
`HkIntegrand α k f` by adding the squares of the finitely many new weighted derivatives,
the integrand is pointwise monotone in the index (`Work.Spaces.HkIntegrand_mono`, iterated
to `k ≤ l` below).  Hence honesty at order `l` implies honesty at every lower order `k ≤ l`,
provided the smaller integrand is a.e. strongly measurable — and that is available as soon
as `f` is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, because the integrand is then
continuous there (`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`, the open
quadrant being all of `Iz × Iθ` up to the null boundary segments).

The whole descent is an instance of the general domination lemma
`Work.FTS.LocData.HkMem_of_majorant`, with the majorant `M = HkIntegrand α l f` supplied by
the hypothesis `hm : HkMem α l f`.  This is the weak-class replacement for
`Work.FTS.CoercivityStep.Norm.HkMem_descend`, which requires the (much stronger)
`SmoothNbhd` hypothesis. -/

/-- The `ℋ^k`-integrand is monotone in the exponent: for `k ≤ l` every summand of
`HkIntegrand α k f` occurs in `HkIntegrand α l f` with the same value, and all summands are
squares, hence nonnegative.  This is `Work.Spaces.HkIntegrand_mono` iterated. -/
private theorem HkIntegrand_mono_le (α : ℝ) {k l : ℕ} (hkl : k ≤ l) (f : ℝ → ℝ → ℝ)
    (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand α l f z θ :=
  Nat.le_induction (le_refl _)
    (fun n _ ih => le_trans ih (Work.Spaces.HkIntegrand_mono α n f z θ)) l hkl

/-- **`HkMem` descends in the order, on the open-quadrant regularity class.**  If `f` is `C^∞`
on the open quadrant `(0,∞) × (0,π/2)` and its `ℋ^l`-integrand is honest, then its
`ℋ^k`-integrand is honest for every `k ≤ l`: the integrand is monotone in the index
(`Work.Spaces.HkIntegrand_mono`) and dominated by the honest one, while smoothness on the open
quadrant (whose complement in `Iz × Iθ` is null) supplies a.e. strong measurability.  This is the
weak-class replacement for `Work.FTS.CoercivityStep.Norm.HkMem_descend`, which requires
`SmoothNbhd`. -/
theorem HkMem_descend_open {α : ℝ} {k l : ℕ} {f : ℝ → ℝ → ℝ} (hkl : k ≤ l)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hm : Work.Spaces.HkMem α l f) : Work.Spaces.HkMem α k f :=
  Work.FTS.LocData.HkMem_of_majorant α k
    ((Work.FTS.EllipticEst.smoothOpen_of_forall hf).continuousOn_HkIntegrand α k)
    hm.1 hm.2
    (fun z _ θ _ => HkIntegrand_mono_le α hkl f z θ)

end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.SliceDatum =====
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

/-! ## The Dirichlet data is preserved by `D_z^j` -/

/-- If `Ψ z 0 = 0` for every `z`, then `(D_z^jΨ) z 0 = 0` for every `z`: the slice
`z ↦ Ψ z 0` is the zero function, so each of its `z`-derivatives vanishes. -/
theorem DzIter_zero_at_zero (Ψ : ℝ → ℝ → ℝ) (j : ℕ) (h : ∀ z, Ψ z 0 = 0) :
    ∀ z, Work.Spaces.DzIter j Ψ z 0 = 0 := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro z
    have hfun : (fun z' => Work.Spaces.DzIter j Ψ z' 0) = fun _ => (0 : ℝ) :=
      funext fun z' => ih z'
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    rw [hfun, deriv_const]
    ring

/-- If `Ψ z (π/2) = 0` for every `z`, then `(D_z^jΨ) z (π/2) = 0` for every `z`. -/
theorem DzIter_zero_at_pi_half (Ψ : ℝ → ℝ → ℝ) (j : ℕ) (h : ∀ z, Ψ z (Real.pi / 2) = 0) :
    ∀ z, Work.Spaces.DzIter j Ψ z (Real.pi / 2) = 0 := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro z
    have hfun : (fun z' => Work.Spaces.DzIter j Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
      funext fun z' => ih z'
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    rw [hfun, deriv_const]
    ring

/-! ## Smoothness of the data and of the slices, in the `open-quadrant` shape -/

/-- The smoothness field of `EllWeakPos` is the `SmoothOpen` of `OpenQDefs`. -/
theorem EllWeakPos.smoothOpen {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen Ψ :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mpr (h.smooth)

/-- The slices of a datum of the weak class are again smooth on the open quadrant. -/
theorem EllWeakPos.smoothOpen_DzIter {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPos α k F Ψ) (j : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j Ψ) :=
  (h.smoothOpen).DzIter j

end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Slot11.Sig2SliceAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.Slot11

set_option autoImplicit false

/-- Every slice of a `SmoothOpen` function is differentiable on the open angular interval.
(A local copy of `Work.FTS.EllipticEst.Mine.differentiableAt_slice_of_smoothOpen`, so that the
shifted Step-4 estimate does not have to import the heavy `Mine/SrcDerivSlice` chain.) -/
theorem differentiableAt_slice_of_smoothOpen {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {z : ℝ} (hz : 0 < z)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun t => g z t) θ := by
  have hcd := hg.curry_θ hz
  have hd : DifferentiableOn ℝ (fun t => g z t) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcd.differentiableOn (by simp [Work.Stability.smoothOrder])
  exact hd.differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-- The angular weight `sin(2θ)^{2-γ}` is measurable (it is continuous for `γ ≤ 3/2`). -/
theorem measurable_sig2 {γ : ℝ} (hγ2 : γ ≤ 3 / 2) :
    Measurable fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ) := by
  have hq : 0 ≤ 2 - γ := by linarith
  have h1 : Continuous fun x : ℝ => x ^ (2 - γ) := Real.continuous_rpow_const hq
  have h2 : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
  exact (h1.comp h2).measurable

/-- `sin(2θ)^{2-γ} ≤ 1` on `Iθ`, for `γ ≤ 3/2`. -/
theorem sig2_le_one_of_mem_Iθ {γ : ℝ} (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 := by
  refine Real.rpow_le_one ?_ (Real.sin_le_one _) (by linarith)
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

end Work.FTS.EllipticEst.TT.Slot11
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.interpGammaDefs =====
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

/-- The angular weight `σ_a(θ) = sin(2θ)^{2-γ(α)}` of the fixed-weight interpolation: the
exponent `2 - γ(α) = 1 - α/10` lies in `[0.975, 1)`, so the weight is bounded on `Iθ` and
vanishes at both endpoints.  This is the weight carried by the left-hand side of `interpGamma`. -/
def sigA (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)

/-- The T-adjoint coefficient `b z = (z-3)/(1+z)`, `|b| ≤ 3`. -/
def bcoef (z : ℝ) : ℝ := (z - 3) / (1 + z)

/-- `Xint α G = ∫∫ (D_z∂_θG)² w² σ_a`: the left-hand side of the interpolation. -/
def Xint (α : ℝ) (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ

/-- `DDint α G = ∫∫ (D_z²G + b D_zG)² w² σ_a`: the radial slot produced by the radial
integration by parts. -/
def DDint (α : ℝ) (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz (Work.Spaces.Dz G) z θ + bcoef z * Work.Spaces.Dz G z θ) ^ 2
      * (Work.Spaces.w z) ^ 2 * sigA α θ

/-- `TTint α G = ∫∫ (∂_θ²G)² w² σ_a`: the angular slot. -/
def TTint (α : ℝ) (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pthIter 2 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ

/-! ## Elementary facts about the angular weights -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem gam_sub_two_exponent (α : ℝ) : 2 - Work.Spaces.gam α = 1 - α / 10 := by
  rw [Work.Spaces.gam]; ring

/-- On `Iθ` the weight `σ_a = sin(2θ)^{2-γ}` is nonnegative. -/
theorem sigA_nonneg (α θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sigA α θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- On the open interval the weight `σ_a` is strictly positive. -/
theorem sigA_pos (α θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 < sigA α θ :=
  Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo hθ) _


/-- **The key weight comparison.**  For `α ≤ 1` one has `sin(2θ)^{2-γ} ≤ sin(2θ)^{-η}` on `Iθ`:
the light weight of the interpolation is dominated by the heavy weight `σ_η` of the `ℋ^k`
norms.  (`2 - γ ≥ -η` because `γ = 1 + α/10 ≤ 2 + η`.) -/
theorem sigA_le_sEta {α θ : ℝ} (hα : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ) :
    sigA α θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · -- at the two endpoints both weights vanish
    rw [sigA, ← h0]
    refine le_of_eq ?_
    rw [Real.zero_rpow (by rw [gam_sub_two_exponent]; linarith),
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  · have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hgam : Work.Spaces.gam α ≤ 2 + Work.Spaces.eta := by
      rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
    refine Real.rpow_le_rpow_of_exponent_ge hpos hs1 ?_
    linarith


/-- The squared half-weight identity `(sin(2θ)^{η/2})² = sin(2θ)^{η}`. -/
theorem sin_rpow_half_sq_eta {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  calc ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
    _ = (Real.sin (2 * θ)) ^ ((Work.Spaces.eta / 2) * 2) := (Real.rpow_mul hs _ _).symm
    _ = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by congr 1; ring


/-- At `k = 0` the `ℋ^k`-integrand is the single square `(f · w / sin(2θ)^{η/2})²`. -/
theorem hkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- **The `k = 0` integrand is `f² w² σ_η`.** -/
theorem hkIntegrand_zero_eq' (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have h1 : (((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))⁻¹) ^ 2
      = ((Real.sin (2 * θ)) ^ Work.Spaces.eta)⁻¹ := by
    rw [inv_pow, sin_rpow_half_sq_eta hθ]
  rw [hkIntegrand_zero_eq, div_eq_mul_inv, mul_pow, mul_pow, h1, ← Real.rpow_neg hs]
  ring


/-! ## Dominating the light-weight integrals by the heavy-weight ones

The three `ℋ⁰`-slots of `interpGamma` are integrals against `σ_η = sin(2θ)^{-η}`, and `HkMem`
makes them honest.  Because `σ_a ≤ σ_η` pointwise on `Iθ`, every nonnegative integrand has its
`σ_a`-integral bounded by the `σ_η`-one; this is the only place where the two weights are
compared.
-/



end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.UopHk

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The definitional index shift `D_z^i (D_z f) = D_z^{i+1} f` -/

/-- The `D_z`-iterates of `D_z f` are the `D_z`-iterates of `f`, shifted by one
(this is `Work.Spaces.DzIter_add_right` together with the definitional `D_z^1 = D_z`). -/
theorem DzIter_Dz_eq (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (Work.Spaces.Dz f) = Work.Spaces.DzIter (i + 1) f := by
  rw [Work.Spaces.DzIter_add_right]
  rfl

/-! ## 2. `D_z` commutes with the iterates of `D_θ` at the genuine smooth order

`Work.Spaces.DzDthIterCommOn` is stated for the analytic order `⊤`; the hypothesis
`SmoothOpen` only supplies `Work.Stability.smoothOrder = ∞`.  The proof below is that of
`Work.FTS.CoercivityFix.QuadPorts.DzDthIterCommOn_quad`, with the fixed strip replaced by an
arbitrary open set. -/

/-- On an open set on which `g` is `C^∞` (genuine smooth order), `D_z` commutes with every
iterate of `D_θ`. -/
theorem Dz_DthIter_comm_of_isOpen {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
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

/-- On an open set on which `g` is `C^∞` (genuine smooth order), `D_z^b` commutes with
`D_θ^a`. -/
theorem DzIter_DthIter_comm_of_isOpen {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.DzIter b g))) V := by
  induction b with
  | zero => intro p hp; rfl
  | succ b ih =>
      intro p hp
      have hstep : Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2 :=
        Dz_DthIter_comm_of_isOpen hV
          (Work.FTS.LocData.contDiffOn_DzIter hV hg b) a hp
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.pz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen hV ih hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      rw [hpz]
      show Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      exact hstep

/-! ## 3. The index shift `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`

* `mixed_Dz_shift_Q0` is the identity on the open quadrant, where Clairaut is available;
* `mixed_Dz_shift` extends it to the whole domain `Iz × Iθ`, where the boundary points are
  handled by the vanishing of the two operators.
-/

/-- **The index shift on the open quadrant.** -/
theorem mixed_Dz_shift_Q0 {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (b a : ℕ) {z θ : ℝ}
    (hQ : (z, θ) ∈ Q0) :
    Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (b + 1) a f z θ := by
  have hDzf : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have h1 : Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ
      = Work.Spaces.DthIter a (Work.Spaces.DzIter b (Work.Spaces.Dz f)) z θ := by
    simpa only [Work.Spaces.mixed, Function.uncurry] using
      (DzIter_DthIter_comm_of_isOpen isOpen_Q0 hDzf b a hQ)
  have h2 : Work.Spaces.DzIter b (Work.Spaces.Dz f) = Work.Spaces.DzIter (b + 1) f :=
    DzIter_Dz_eq b f
  have h3 : Work.Spaces.DthIter a (Work.Spaces.DzIter (b + 1) f) z θ
      = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a f) z θ := by
    simpa only [Function.uncurry] using
      (DzIter_DthIter_comm_of_isOpen isOpen_Q0 hf (b + 1) a hQ).symm
  calc Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ
      = Work.Spaces.DthIter a (Work.Spaces.DzIter b (Work.Spaces.Dz f)) z θ := h1
    _ = Work.Spaces.DthIter a (Work.Spaces.DzIter (b + 1) f) z θ := by rw [h2]
    _ = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a f) z θ := h3
    _ = Work.Spaces.mixed (b + 1) a f z θ := rfl

/-! ### The boundary cases: everything vanishes -/

/-- At `z = 0`, every `D_z`-iterate of order `≥ 1` vanishes. -/
private lemma DzIter_succ_apply_zero (b : ℕ) (H : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.DzIter (b + 1) H 0 θ = 0 := by
  show (0 : ℝ) * Work.Spaces.pz (Work.Spaces.DzIter b H) 0 θ = 0
  rw [zero_mul]

/-- If the `θ`-slice of `H` at `z = 0` vanishes identically, so do all of its `D_θ`-iterates. -/
private lemma DthIter_slice_zero_of_slice_zero (a : ℕ) {H : ℝ → ℝ → ℝ}
    (hH : ∀ θ' : ℝ, H 0 θ' = 0) :
    (fun θ' => Work.Spaces.DthIter a H 0 θ') = fun _ => (0 : ℝ) := by
  induction a with
  | zero => funext θ'; exact hH θ'
  | succ a ih =>
      funext θ'
      have hpth : Work.Spaces.pth (Work.Spaces.DthIter a H) 0 θ' = 0 := by
        show deriv (fun θ'' => Work.Spaces.DthIter a H 0 θ'') θ' = 0
        rw [ih]
        simp
      show Real.sin (2 * θ') * Work.Spaces.pth (Work.Spaces.DthIter a H) 0 θ' = 0
      rw [hpth, mul_zero]

/-- If the `θ`-slice of `H` at a fixed angle vanishes identically in `z`, so do all of its
`D_z`-iterates. -/
private lemma DzIter_apply_of_zslice_zero (b : ℕ) {H : ℝ → ℝ → ℝ} {θ : ℝ}
    (hH : ∀ z' : ℝ, H z' θ = 0) : ∀ z : ℝ, Work.Spaces.DzIter b H z θ = 0 := by
  induction b with
  | zero => exact hH
  | succ b ih =>
      intro z
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter b H) z θ = 0 := by
        show deriv (fun z' => Work.Spaces.DzIter b H z' θ) z = 0
        rw [show (fun z' => Work.Spaces.DzIter b H z' θ) = fun _ => (0 : ℝ) from funext ih]
        simp
      show z * Work.Spaces.pz (Work.Spaces.DzIter b H) z θ = 0
      rw [hpz, mul_zero]

/-- At `z = 0`, a mixed derivative of a function whose `θ`-slice at `z = 0` vanishes is zero. -/
private lemma mixed_apply_zero_fst_of_slice_zero (b a : ℕ) {H : ℝ → ℝ → ℝ}
    (hH : ∀ θ' : ℝ, H 0 θ' = 0) (θ : ℝ) : Work.Spaces.mixed b a H 0 θ = 0 := by
  rcases b with _ | b
  · exact congrFun (DthIter_slice_zero_of_slice_zero a hH) θ
  · exact DzIter_succ_apply_zero b (Work.Spaces.DthIter a H) θ

/-- At an angle with `sin(2θ) = 0`, a mixed derivative of angular order `a ≥ 1` vanishes. -/
private lemma mixed_apply_of_sin_zero (b a : ℕ) (ha : 1 ≤ a) (H : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.mixed b a H z θ = 0 := by
  have hslice : ∀ z' : ℝ, Work.Spaces.DthIter a H z' θ = 0 := by
    intro z'
    rcases a with _ | a
    · exact absurd ha (by omega)
    · exact Work.Spaces.DthIter_succ_eq_zero_of_sin_eq_zero a H hs
  exact DzIter_apply_of_zslice_zero b hslice z

/-- **The index shift on the whole domain**:
`D_z^b D_θ^a (D_z f) = D_z^{b+1} D_θ^a f` on `Iz × Iθ`, for `f` smooth on the open quadrant.
At the interior points this is the commutation of `D_z` and `D_θ`; at `z = 0` and at the angular
endpoints both sides vanish. -/
theorem mixed_Dz_shift {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (b a : ℕ) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (b + 1) a f z θ := by
  have hDz0 : ∀ θ' : ℝ, Work.Spaces.Dz f 0 θ' = 0 := fun θ' => by
    show (0 : ℝ) * Work.Spaces.pz f 0 θ' = 0
    rw [zero_mul]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rcases a with _ | a
    · show Work.Spaces.DzIter b (Work.Spaces.Dz f) 0 θ = Work.Spaces.DzIter (b + 1) f 0 θ
      rw [DzIter_Dz_eq]
    · rw [mixed_apply_zero_fst_of_slice_zero b (a + 1) hDz0 θ]
      exact (DzIter_succ_apply_zero b (Work.Spaces.DthIter (a + 1) f) θ).symm
  · by_cases hθin : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
    · exact mixed_Dz_shift_Q0 hf b a ⟨hzpos, hθin⟩
    · have hs : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθin
      rcases a with _ | a
      · show Work.Spaces.DzIter b (Work.Spaces.Dz f) z θ = Work.Spaces.DzIter (b + 1) f z θ
        rw [DzIter_Dz_eq]
      · rw [mixed_apply_of_sin_zero b (a + 1) (by omega) (Work.Spaces.Dz f) hs]
        exact (mixed_apply_of_sin_zero (b + 1) (a + 1) (by omega) f hs).symm

/-! ## 4. Pointwise domination of the `ℋ^n`-integrands -/

/-- A sum over `i ≤ n` of `F (i+1)` is dominated by the sum over `a ≤ n+1` of `F a` when
`F ≥ 0` (the extra term being `F 0`). -/
private lemma SumSuccRange_le (n : ℕ) (F : ℕ → ℝ) (hF : ∀ a, 0 ≤ F a) :
    (∑ i ∈ Finset.range (n + 1), F (i + 1)) ≤ ∑ a ∈ Finset.range (n + 2), F a := by
  have h2 : (∑ a ∈ Finset.range (n + 2), F a)
      = (∑ i ∈ Finset.range (n + 1), F (i + 1)) + F 0 :=
    Finset.sum_range_succ' F (n + 1)
  linarith [hF 0]

/-- **Every summand of `HkIntegrand α n (D_z f)` is a summand of `HkIntegrand α (n+1) f`**, with
the same weight: the pure summands by `D_z^i (D_z f) = D_z^{i+1} f`, the mixed summands by the
index shift `mixed_Dz_shift`.  Hence the pointwise domination of the two integrands. -/
theorem HkIntegrand_Dz_le_succ (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α n (Work.Spaces.Dz f) z θ
      ≤ Work.Spaces.HkIntegrand α (n + 1) f z θ := by
  set H : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hH
  set W : ℝ := Work.Spaces.Wt α z θ with hW
  have hLHS : Work.Spaces.HkIntegrand α n (Work.Spaces.Dz f) z θ
      = (∑ i ∈ Finset.range (n + 1),
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (if 1 ≤ i ∧ i + j ≤ n
              then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have hRHS : Work.Spaces.HkIntegrand α (n + 1) f z θ
      = (∑ a ∈ Finset.range (n + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2)
        + (∑ a ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2),
            (if 1 ≤ a ∧ a + b ≤ n + 1
              then (Work.Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have h1 : (∑ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * H) ^ 2)
      ≤ ∑ a ∈ Finset.range (n + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2 := by
    refine le_trans (le_of_eq ?_) (SumSuccRange_le n
      (fun a => (Work.Spaces.DzIter a f z θ * H) ^ 2) (fun a => sq_nonneg _))
    exact Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dz_eq i f])
  have h2 : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
              (if 1 ≤ i ∧ i + j ≤ n
                then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ * W) ^ 2 else 0))
      = (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
              (if 1 ≤ i ∧ i + j ≤ n
                then (Work.Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ n
    · rw [ite_eq_left hc, ite_eq_left hc, mixed_Dz_shift hf j i hz hθ]
    · rw [ite_eq_right hc, ite_eq_right hc]
  have hkey : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
              (if 1 ≤ i ∧ i + j ≤ n
                then (Work.Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0))
      ≤ (∑ a ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2),
            (if 1 ≤ a ∧ a + b ≤ n + 1
              then (Work.Spaces.mixed b a f z θ * W) ^ 2 else 0)) :=
    Work.Coercivity.SumShiftZ_le n
      (fun a b => (Work.Spaces.mixed b a f z θ * W) ^ 2) (fun a b => sq_nonneg _)
  have hnn : 0 ≤ ∑ a ∈ Finset.range (n + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  rw [hLHS, hRHS]
  linarith [h1, h2, hkey, hnn]

/-! ## 5. The `ℋ^n`-membership of `D_z f` -/

/-- **The membership step**: for `f` which is `C^∞` on the open quadrant and in `ℋ^{n+1}`, the
radial derivative `D_z f` lies in `ℋ^n`.  This is `Work.FTS.LocData.HkMem_of_majorant` with the
majorant the `(n+1)`-integrand of `f` itself, the pointwise domination being
`HkIntegrand_Dz_le_succ` and the measurability input the continuity of the integrand of `D_z f`
on the open quadrant. -/
theorem HkMem_Dz_of_smoothOpen (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f)
    (h : Work.Spaces.HkMem α (n + 1) f) : Work.Spaces.HkMem α n (Work.Spaces.Dz f) :=
  Work.FTS.LocData.HkMem_of_majorant α n
    (f := Work.Spaces.Dz f)
    (M := fun z θ => Work.Spaces.HkIntegrand α (n + 1) f z θ)
    ((SmoothOpen.Dz hf).continuousOn_HkIntegrand α n)
    h.1 h.2
    (fun z hz θ hθ => HkIntegrand_Dz_le_succ α n hf z θ hz hθ)

/-! ## 6. The target -/


end Work.FTS.EllipticEst.UopHk
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory
open scoped Real Topology

/-- **Measurability of the angular integral of a source on the open quadrant.**

If `g` is continuous on the open quadrant `Q0 = (0,∞) × (0,π/2)` and `φ` is continuous
on `Iθ = [0,π/2]`, then the angular integral
`z ↦ ∫_θ g z θ · φ θ dθ` is a.e. strongly measurable for the restricted Lebesgue
measure on `(0,∞)`.

Indeed the uncurried product is continuous on `Q0`, which is of full measure inside
`Iz × Iθ`, so the product function is a.e. strongly measurable for the product of the
restricted measures (`Work.Spaces.aesm_of_continuousOn_Qd`); integrating out the
`θ`-variable preserves a.e. strong measurability (Fubini for Bochner integrals,
`AEStronglyMeasurable.integral_prod_right'`). -/
theorem aestronglyMeasurable_integral_Itheta_Q0 (g : ℝ → ℝ → ℝ)
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ Work.Spaces.Iθ) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, g z θ * φ θ)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  -- The uncurried product is continuous on the open quadrant.
  have hgmul : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 * φ p.2) Q0 := by
    refine hg.mul ?_
    exact hφ.comp continuous_snd.continuousOn fun p hp => by
      obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
      exact ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  -- Hence it is a.e. strongly measurable for the product of the restricted measures.
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.1 p.2 * φ p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hgmul
  -- Integrating out `θ` preserves a.e. strong measurability.
  have h := MeasureTheory.AEStronglyMeasurable.integral_prod_right'
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) haesm
  -- `Iz = [0,∞)` agrees with `(0,∞)` up to the null set `{0}`.
  have hz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hz] at h
  simpa using h

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.exists_bslSol_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false


/- The `SmoothInt`-slice variant of the statement above was carried here as the `Prop`-valued
`def bslSolExistenceSmoothIntFts` until 2026-10-08.  It was **removed**: `Work.Spaces.SmoothInt`
demands *analyticity* (`ContDiffOn ℝ ⊤`, and in this Mathlib `⊤ : ℕ∞ω` is the analytic order `ω`,
not `C^∞`) of `Ψ` on a neighbourhood of `z = 0`, which the modal solution cannot have (its radial
amplitudes behave like `z^{2m/α}` with generically non-integral exponent); the statement is
therefore not true for arbitrary `F`, and no consumer used it.  The existence statement that *is*
consumed, `bslSolExistenceFts`, is proved in `Final/bslSolExistence_fts.lean`. -/

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.integrableOn_box_of_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!

# Integrability on a box from integrability of the slices

Fubini–Tonelli bookkeeping used by the elliptic estimates of §'Elliptic Regularity
Estimates'.  For a source `g` which is

* continuous on the open quadrant `Q0 = (0,∞) × (0,π/2)`;
* nonnegative;
* slicewise integrable in `θ` on `Iθ = [0,π/2]` for every `s ∈ [a,b]` (`a > 0`);
* such that the *iterated* integral `s ↦ ∫_{Iθ} g s θ dθ` is integrable on `[a,b]`,

the uncurried `g` is integrable on the box `[a,b] × Iθ`.

The point of the lemma is that no *joint* measurability hypothesis is assumed: it is
deduced from continuity on the open quadrant, which differs from the box only by the two
null lines `θ = 0`, `θ = π/2` (note `a > 0`, so the radial boundary `z = 0` is not in the
box at all).  This is exactly the situation of the `z`-estimates, where the source is
`C^∞` only on the open quadrant.

PROOF.  `Measure.prod_restrict` turns the restricted planar Lebesgue measure on the box
into the product `(volume|{a ≤ · ≤ b}).prod (volume|Iθ)`, and
`Work.Spaces.aesm_of_continuousOn_Qd` (continuity on the open quadrant ⇒ a.e. strong
measurability for `(volume|Iz).prod (volume|Iθ)`) descends to the box by monotonicity of
the restricted measures (the box is contained in `Iz ×ˢ Iθ`, using `a > 0`).  The two
remaining hypotheses are precisely the slice and iterated-integral inputs of
`Work.Spaces.integrable_prod_of_iterated`, Tonelli for a nonnegative function.
-/

namespace Work.FTS.EllipticEst

set_option linter.unusedVariables false

theorem integrableOn_box_of_slice {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hnn : ∀ z θ : ℝ, 0 ≤ g z θ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hsl : ∀ s ∈ Set.Icc a b, MeasureTheory.IntegrableOn (fun θ : ℝ => g s θ) Work.Spaces.Iθ)
    (hint : MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, g s θ) (Set.Icc a b)) :
    MeasureTheory.IntegrableOn (Function.uncurry g) (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  -- The box sits inside `Iz ×ˢ Iθ` because `a > 0`.
  have hbox : Set.Icc a b ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
    Set.prod_mono (fun x hx => le_trans (le_of_lt ha) hx.1) subset_rfl
  -- Restricting the product measure is monotone in the set.
  have hmono : (MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono hbox le_rfl
  -- Continuity on the open quadrant gives a.e. strong measurability on the box.
  have hAE : MeasureTheory.AEStronglyMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => g p.1 p.2) hg).mono_measure hmono
  -- The two Fubini inputs, read off from the hypotheses.
  have hslice : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
      MeasureTheory.Integrable (fun θ : ℝ => g s θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
    simpa only [MeasureTheory.IntegrableOn] using hsl s hs
  have houter : MeasureTheory.Integrable
      (fun s : ℝ => ∫ θ, g s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Icc a b)) := by
    simpa only [MeasureTheory.IntegrableOn] using hint
  have hfin := (Work.Spaces.integrable_prod_of_iterated (G := g) hnn hAE hslice houter).1
  -- Identify the product measure with the restriction of the planar Lebesgue measure.
  have hEq : ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict]
    rfl
  rw [hEq] at hfin
  exact hfin

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.integrableOn_slice_l2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Set Filter
open scoped Real Topology

theorem integrableOn_slice_l2 (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (i : ℕ) (hi : i ≤ k) :
    ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter i F s θ * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (Set.Icc a b) := by
  intro a b ha hab
  -- The uncurried squared summand is a.e. strongly measurable for the product measure
  -- `(dz)|_{Iz} × (dθ)|_{Iθ}`: it is continuous on the open quadrant, which exhausts the
  -- closed quadrant up to a null set.
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter i F p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_summand i)).pow 2
  -- Integrating out `θ` (Fubini for Bochner integrals) gives the measurability of the
  -- angular `L²`-slice in `s`.
  have haesm : AEStronglyMeasurable
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i F s θ
        * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hjoint.integral_prod_right'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa only using h
  -- Domination: the `θ`-integral of the squared summand is pointwise bounded by the
  -- `θ`-integral of the full `ℋ^k`-integrand, which is integrable in `z` by hypothesis.
  have hInt : MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i F s θ
        * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz := by
    refine hmem.2.mono' haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with s hs
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hmem.1 s hs)
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        fun θ _ => Work.Spaces.sq_le_HkIntegrand_z α k F s θ i hi)
  -- `[a,b] ⊆ Iz` because `0 < a`.
  exact hInt.mono_set fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.integrable_prod_sq_restrict_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 800000

/-- On the whole half-line `Iz` the iterated angular integral of a single weighted `D_z`-slot
of an `ℋ^k`-function is integrable: it is measurable by Fubini for Bochner integrals
(`AEStronglyMeasurable.integral_prod_right'`, the joint integrand being a.e. strongly
measurable by continuity on the open quadrant) and pointwise dominated by the iterated
integral of `HkIntegrand`, which is integrable by `hmem.2` (`sq_le_HkIntegrand_z`). -/
theorem integrableOn_slice_Iz (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (i : ℕ) (hi : i ≤ k) :
    MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter i F s θ * (Work.Spaces.w s
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iz := by
  -- a.e. strong measurability of the uncurried squared summand for `(dz)|_{Iz} × (dθ)|_{Iθ}`
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter i F p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_summand i)).pow 2
  -- Fubini for Bochner integrals: integrate out `θ` to get measurability in `s`
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i F s θ
        * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hjoint.integral_prod_right'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa only using h
  -- domination by the iterated integral of the full `ℋ^k`-integrand
  refine hmem.2.mono' haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with s hs
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
  exact MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => sq_nonneg _)
    (hmem.1 s hs)
    (MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ _ => Work.Spaces.sq_le_HkIntegrand_z α k F s θ i hi))

theorem integrable_prod_sq_restrict_open (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (i : ℕ) (hi : i ≤ k) {a b : ℝ} (ha : 0 ≤ a) :
    MeasureTheory.Integrable
      (Function.uncurry (fun r θ : ℝ => (Work.Spaces.DzIter i F r θ
        * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- `Ioc a b ⊆ Iz` because `a ≥ 0`.
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iz := fun r hr =>
    Set.mem_Ici.mpr (le_of_lt (lt_of_le_of_lt ha hr.1))
  have hbox : Set.Ioc a b ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
    Set.prod_mono hsub subset_rfl
  -- The measure on the box is the restriction of the measure on the closed quadrant.
  have hmono : (MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono hbox le_rfl
  -- a.e. strong measurability on the box, by monotonicity of the restricted measure.
  have hAE : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun r θ : ℝ => (Work.Spaces.DzIter i F r θ
        * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    ((Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_summand i)).pow 2).mono_measure
      hmono
  -- The angular slices are integrable at every `r ∈ (a,b]`.
  have hslice : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
      MeasureTheory.Integrable (fun θ : ℝ => (Work.Spaces.DzIter i F r θ
        * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with r hr
    exact integrableOn_zSummand α k hF hmem i hi (hsub hr)
  -- The iterated integral is integrable on `(a,b]` by the half-line version.
  have houter : MeasureTheory.Integrable
      (fun r : ℝ => ∫ θ, (Work.Spaces.DzIter i F r θ
        * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (integrableOn_slice_Iz α k hF hmem i hi).mono_set hsub
  exact (Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun r θ : ℝ => (Work.Spaces.DzIter i F r θ
      * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun r θ => sq_nonneg _) hAE hslice houter).1

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.SliceAlgebra =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Algebraic identities for the weak-class slices

* `Lzero1` applied to the `z`-slice of `Ψ` is the slice of `Lzero` (definitional).
* `D_z²Ψ = z²∂_z²Ψ + z∂_zΨ` on the open quadrant.
* On the open quadrant, the equation `bslOp α Ψ = F` rewrites as
  `Lzero1 (Ψ z ·) = F z · + α² D_z²Ψ + 5α D_zΨ` for the *slices*.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- `Lzero1` applied to the `z`-slice of `Ψ` is the slice of `Work.Elliptic.Lzero`. -/
theorem Lzero1_slice_eq (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ = Work.Elliptic.Lzero Ψ z θ := rfl

/-- **`D_z²Ψ` splits as `z²∂_z²Ψ + z∂_zΨ`.** -/
theorem srcB_DzIter_two_eq (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 2 Ψ z θ
      = z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ + z * Work.Spaces.pz Ψ z θ := by
  have hd : HasDerivAt (fun z' : ℝ => Work.Spaces.pz Ψ z' θ)
      (Work.Spaces.pzIter 2 Ψ z θ) z := by
    have h := (hΨ.pz).hasDerivAt_slice hθ hz
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h
  have hprod := (hasDerivAt_id z).mul hd
  show z * deriv (id * fun z' : ℝ => Work.Spaces.pz Ψ z' θ) z
    = z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ + z * Work.Spaces.pz Ψ z θ
  rw [hprod.deriv]
  simp only [one_mul, id_eq]
  ring

/-- **The slice equation in the `D_z`-form.** -/
theorem Lzero1_slice_eq_source {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
      = F z θ + α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ + 5 * α * Work.Spaces.DzIter 1 Ψ z θ := by
  have hbsl := heq z θ hz hθ.1 hθ.2
  simp only [Work.Elliptic.bslOp] at hbsl
  have hL : Work.Elliptic.Lzero Ψ z θ
      = F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ := by
    linarith [hbsl]
  rw [Lzero1_slice_eq, hL, srcB_DzIter_two_eq Ψ hΨ hz hθ]
  show F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
    = F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ + z * Work.Spaces.pz Ψ z θ)
      + 5 * α * (z * Work.Spaces.pz Ψ z θ)
  ring

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.aesmPzMulSinCos2Box =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound


end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.pzSliceFtcBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The one-dimensional FTC bound along a radial slice of `pz Ψ`

For a source `Ψ : ℝ → ℝ → ℝ` of class `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, an
angular slice of `∂_zΨ` obeys the elementary fundamental-theorem-of-calculus estimate

`‖∂_zΨ(z,θ)·sinCos2 θ‖ ≤ ‖∂_zΨ(z₀,θ)·sinCos2 θ‖ + ∫_{a..b} ‖∂_z²Ψ(s,θ)·sinCos2 θ‖`

for all `0 < a ≤ b`, `z₀ ∈ [a,b]` and `z ∈ (a,b]`: the slice `s ↦ ∂_z²Ψ(s,θ)` is continuous
on `(0,∞)`, so `∂_zΨ(z,θ) - ∂_zΨ(z₀,θ)` is its integral over the interval between `z₀` and
`z`, and the triangle inequality together with monotonicity of the interval integral of the
nonnegative function `|∂_z²Ψ(·,θ)|` bounds this by the integral over the whole `[a,b]`.

The angular weight `sinCos2 θ = sin θ · cos²θ` is a nonnegative constant along the slice, so
it factors out of the absolute values and out of the integral.

The proof rests on `Submission.Work.FTS.EllipticEst.OpenQDefs` for the smoothness of the
slices of a smooth-open-quadrant function and its iterated `∂_z`-derivatives.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false

/-- **Fundamental-theorem-of-calculus bound.**  If `f'` is the derivative of `f` at every
point of `[a,b]` and `f'` is interval integrable there, then the increment of `f` between two
points of `[a,b]` is bounded by the integral of `|f'|` over the whole interval:

`|f x - f y| ≤ ∫_{a..b} |f'|`   for all `x, y ∈ [a,b]`.

Indeed `f x - f y = ∫_y^x f'` (the interval integral is defined on both orientations), and the
integral of `|f'|` over the segment joining `x` and `y` is at most the integral over `[a,b]`
because `|f'| ≥ 0`. -/
lemma abs_sub_le_integral_abs_deriv {f f' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b)
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |f x - f y| ≤ ∫ s in a..b, |f' s| := by
  have hsub : Set.uIcc y x ⊆ Set.uIcc a b :=
    Set.uIcc_subset_uIcc_iff_mem.mpr ⟨Set.Icc_subset_uIcc hy, Set.Icc_subset_uIcc hx⟩
  have hFTC : (∫ s in y..x, f' s) = f x - f y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hderiv t (hsub ht))
      (hint.mono_set hsub)
  rw [← hFTC]
  rcases le_total y x with hle | hle
  · have h1 : |∫ s in y..x, f' s| ≤ ∫ s in y..x, |f' s| :=
      intervalIntegral.abs_integral_le_integral_abs hle
    have h2 : (∫ s in y..x, |f' s|) ≤ ∫ s in a..b, |f' s| :=
      intervalIntegral.integral_mono_interval hy.1 hle hx.2
        (Filter.Eventually.of_forall (fun s => abs_nonneg (f' s))) hint.abs
    linarith
  · have hsym : (∫ s in y..x, f' s) = -(∫ s in x..y, f' s) := intervalIntegral.integral_symm x y
    have h1 : |∫ s in x..y, f' s| ≤ ∫ s in x..y, |f' s| :=
      intervalIntegral.abs_integral_le_integral_abs hle
    have h2 : (∫ s in x..y, |f' s|) ≤ ∫ s in a..b, |f' s| :=
      intervalIntegral.integral_mono_interval hx.1 hle hy.2
        (Filter.Eventually.of_forall (fun s => abs_nonneg (f' s))) hint.abs
    rw [hsym, abs_neg]
    linarith

/-- **The slice FTC bound with the angular weight.**  For a source smooth on the open quadrant,
the weighted `∂_z`-slice satisfies
`‖∂_zΨ(z,θ)·sinCos2 θ‖ ≤ ‖∂_zΨ(z₀,θ)·sinCos2 θ‖ + ∫_{a..b} ‖∂_z²Ψ(s,θ)·sinCos2 θ‖`. -/
theorem pzSliceFtcBound {Ψ : ℝ → ℝ → ℝ} {a b z₀ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hz₀ : z₀ ∈ Set.Icc a b) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : z ∈ Set.Ioc a b) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ‖Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ‖ ≤
      ‖Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ‖ +
        ∫ s in a..b, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖ := by
  -- the angular weight is a nonnegative constant along the slice
  set c := Work.Elliptic.sinCos2 θ with hcdef
  have hc : 0 ≤ c := by
    rw [hcdef, Work.Elliptic.sinCos2]
    exact mul_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hθ.1) (by linarith [Real.pi_pos, hθ.2]))
      (sq_nonneg _)
  have hzab : z ∈ Set.Icc a b := ⟨le_of_lt hz.1, hz.2⟩
  -- the second `∂_z`-derivative of the slice is continuous, hence interval integrable
  have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact ((hΨ.pzIter 2).curry_z hθ).continuousOn.mono (fun s hs => lt_of_lt_of_le ha hs.1)
  have hint : IntervalIntegrable (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ) volume a b :=
    hcont.intervalIntegrable
  -- the first `∂_z`-derivative of the slice differentiates to the second one
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun s : ℝ => Work.Spaces.pz Ψ s θ) (Work.Spaces.pzIter 2 Ψ x θ) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    simpa using hΨ.hasDerivAt_slice_pzIter 1 hθ hxpos
  -- the FTC bound for the unweighted slices
  have hmain : |Work.Spaces.pz Ψ z θ| ≤ |Work.Spaces.pz Ψ z₀ θ| +
      ∫ s in a..b, |Work.Spaces.pzIter 2 Ψ s θ| := by
    have hsplit : Work.Spaces.pz Ψ z₀ θ + (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ)
        = Work.Spaces.pz Ψ z θ := by ring
    have hFT : |Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ| ≤
        ∫ s in a..b, |Work.Spaces.pzIter 2 Ψ s θ| :=
      abs_sub_le_integral_abs_deriv hderiv hint hzab hz₀
    calc |Work.Spaces.pz Ψ z θ|
        = |Work.Spaces.pz Ψ z₀ θ + (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ)| := by
          rw [hsplit]
      _ ≤ |Work.Spaces.pz Ψ z₀ θ| + |Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ| :=
          abs_add_le _ _
      _ ≤ |Work.Spaces.pz Ψ z₀ θ| + ∫ s in a..b, |Work.Spaces.pzIter 2 Ψ s θ| := by linarith
  -- multiply by the nonnegative weight `c`
  have hnorm : ‖Work.Spaces.pz Ψ z θ‖ ≤
      ‖Work.Spaces.pz Ψ z₀ θ‖ + ∫ s in a..b, ‖Work.Spaces.pzIter 2 Ψ s θ‖ := hmain
  have hmainmul := mul_le_mul_of_nonneg_right hnorm hc
  rw [add_mul] at hmainmul
  have hnorm_mul : ∀ x : ℝ, ‖x * c‖ = ‖x‖ * c := fun x => by
    rw [norm_mul, Real.norm_of_nonneg hc]
  have hInt_eq : (∫ s in a..b, ‖Work.Spaces.pzIter 2 Ψ s θ * c‖)
      = (∫ s in a..b, ‖Work.Spaces.pzIter 2 Ψ s θ‖) * c := by
    rw [show (fun s : ℝ => ‖Work.Spaces.pzIter 2 Ψ s θ * c‖)
        = (fun s : ℝ => ‖Work.Spaces.pzIter 2 Ψ s θ‖ * c) from
        funext (fun s => hnorm_mul (Work.Spaces.pzIter 2 Ψ s θ))]
    exact intervalIntegral.integral_mul_const c _
  rw [hnorm_mul (Work.Spaces.pz Ψ z θ), hnorm_mul (Work.Spaces.pz Ψ z₀ θ), hInt_eq]
  exact hmainmul

end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceAesmSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
theorem ae_mem_Ioo_of_mem_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) : Measure ℝ)
      = volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- `sEta` is continuous on the open angular interval. -/
theorem continuousOn_sEta_Ioo :
    ContinuousOn Work.FTS.EllipticEst.sEta (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  unfold Work.FTS.EllipticEst.sEta
  exact ContinuousOn.rpow hsin continuousOn_const (fun θ hθ => Or.inl (ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))))

/-- **A.e. strong measurability of the `η`-weighted square of an angular slice.**

If `A` is continuous on the open quadrant `Q0 = (0,∞) × (0,π/2)`, then for every `z > 0` the
slice `θ ↦ (A z θ)² · sEta θ` is a.e. strongly measurable for `volume.restrict Iθ`. -/
theorem aesm_slice_sq_mul_sEta {A : ℝ → ℝ → ℝ}
    (hA : ContinuousOn (Function.uncurry A) Work.FTS.EllipticEst.Q0) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => (A z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have hse : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      Work.FTS.EllipticEst.Q0 :=
    continuousOn_sEta_Ioo.comp continuous_snd.continuousOn
      (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      Work.FTS.EllipticEst.Q0 :=
    (hA.pow 2).mul hse
  exact Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) hcont hz

end Work.FTS.EllipticEst.remov.SourceBound
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.TopCoreB.SrcBoundDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TopCoreB/SrcBoundDefs`: the vocabulary of the source bound `srcBound`

The target `Work.FTS.EllipticEst.remov.TopCoreB.srcBound` bounds the
`sin(2θ)^{2k-γ}`-weighted `∂_θ^k`-norm of the *angular source*

  `G = F + α²·z²∂_z²Ψ + α(5+α)·D_zΨ`

(the right-hand side of the equation `Lzero1(Ψ z ·) = G`, i.e. `bslOp α Ψ = F` with the radial
part moved over) by the `ℋ^k`-slot quantities appearing on the right-hand side of the paper's
source estimate.  This module fixes the small vocabulary:

* `Abar Ψ = z²∂_z²Ψ` -- the second radial source term,
* `SrcG α F Ψ = F + α²·Abar Ψ + α(5+α)·D_zΨ` -- the angular source,
* `Maj α k cF cA cB F Ψ` -- the pointwise majorant of the source integrand obtained from the
  three slot recursions: the `∂_θ`-slots of `F` resp. `Abar Ψ` at order `≤ k` and of
  `∂_θ²(D_zΨ)` at order `≤ k-2`, weighted by `Wt α = w·sin(2θ)^{-γ/2}`.

All declarations here are `sorry`-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false

/-- `A = z²∂_z²Ψ`, the second term of the angular source (with its coefficient `α²`). -/
def Abar (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

@[simp] theorem Abar_apply (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Abar Ψ z θ = z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := rfl

/-- The angular source `G = F + α²z²∂_z²Ψ + α(5+α)z∂_zΨ` of the equation `Lzero1(Ψ z ·) = G`. -/
def SrcG (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => F z θ + α ^ 2 * Abar Ψ z θ + (α * (5 + α)) * Work.Spaces.DzIter 1 Ψ z θ

@[simp] theorem SrcG_apply (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    SrcG α F Ψ z θ = F z θ + α ^ 2 * Abar Ψ z θ
      + (α * (5 + α)) * Work.Spaces.DzIter 1 Ψ z θ := rfl

/-- The `j`-th angular slot of `X` against the mixed weight `Wt α` at fixed `(z,θ)`:
`(D_θ^j X · Wt α)²`. -/
def slot (α : ℝ) (j : ℕ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.mixed 0 j X z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The pointwise majorant of the source integrand produced by the three slot recursions: the
`∂_θ`-slots of `F` and of `Abar Ψ` of order `≤ k`, and the `∂_θ`-slots of
`∂_θ²(D_zΨ)` of order `≤ k-2`, with the coefficients of the source. -/
def Maj (α : ℝ) (k : ℕ) (cF cA cB : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    3 * cF * (∑ r ∈ Finset.Icc 1 k, slot α r F z θ)
      + 3 * α ^ 4 * cA * (∑ r ∈ Finset.Icc 1 k, slot α r (Abar Ψ) z θ)
      + 3 * (α * (5 + α)) ^ 2 * cB
          * (∑ r ∈ Finset.Icc 1 (k - 2),
              slot α r (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ)

theorem slot_nonneg (α : ℝ) (j : ℕ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ slot α j X z θ :=
  sq_nonneg _

theorem Maj_nonneg (α : ℝ) (k : ℕ) (cF cA cB : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hcF : 0 ≤ cF) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) (hα : 0 ≤ α) :
    0 ≤ Maj α k cF cA cB F Ψ z θ := by
  have h1 : 0 ≤ ∑ r ∈ Finset.Icc 1 k, slot α r F z θ :=
    Finset.sum_nonneg fun r _ => slot_nonneg α r F z θ
  have h2 : 0 ≤ ∑ r ∈ Finset.Icc 1 k, slot α r (Abar Ψ) z θ :=
    Finset.sum_nonneg fun r _ => slot_nonneg α r (Abar Ψ) z θ
  have h3 : 0 ≤ ∑ r ∈ Finset.Icc 1 (k - 2),
      slot α r (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ :=
    Finset.sum_nonneg fun r _ => slot_nonneg α r _ z θ
  simp only [Maj]
  have hα2 : (0 : ℝ) ≤ α * (5 + α) := by nlinarith
  have h4 : (0 : ℝ) ≤ 3 * cF * (∑ r ∈ Finset.Icc 1 k, slot α r F z θ) := by positivity
  have h5 : (0 : ℝ) ≤ 3 * α ^ 4 * cA * (∑ r ∈ Finset.Icc 1 k, slot α r (Abar Ψ) z θ) := by
    have : (0:ℝ) ≤ α ^ 4 := by positivity
    positivity
  have h6 : (0 : ℝ) ≤ 3 * (α * (5 + α)) ^ 2 * cB
      * (∑ r ∈ Finset.Icc 1 (k - 2),
          slot α r (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ) := by positivity
  linarith [h4, h5, h6]

end Work.FTS.EllipticEst.remov.TopCoreB
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.aeSliceFtcPzIter2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The fundamental theorem of calculus along a radial slice of `pzIter 2 Ψ`.**

For data of the weak class, and for almost every angle `θ` (the only angles that can fail are
the two endpoints `0`, `π/2` of `Iθ`), every radial slice `s ↦ ∂_z²Ψ(s,θ)` is interval
integrable and integrates to the difference of the first `∂_z`-derivative:

`∫_{r}^{ρ} ∂_z²Ψ(s,θ) ds = ∂_zΨ(ρ,θ) - ∂_zΨ(r,θ)`, for all `ρ ∈ [r, z₁]` with `r > 0`.

This is the elementary FTC that removes a `∂_z` between the `(k-1)`-level datum `D_z^{k-1}Ψ`
and the level-`k` estimate: the weak class gives `C^∞`-smoothness of `Ψ` on the open quadrant
`(0,∞) × (0,π/2)`, hence of every `z`-slice at an interior angle, and `pzIter 2 Ψ` is exactly
the `z`-derivative of the slice of `pzIter 1 Ψ = pz Ψ` there. -/
theorem aeSliceFtcPzIter2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    {r z₁ : ℝ} (hr : 0 < r) (hrz : r ≤ z₁) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ ρ ∈ Set.Icc r z₁,
        IntervalIntegrable (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ)
          MeasureTheory.volume r ρ ∧
        (∫ s in r..ρ, Work.Spaces.pzIter 2 Ψ s θ)
          = Work.Spaces.pz Ψ ρ θ - Work.Spaces.pz Ψ r θ
  := by
  -- `Ψ` is `C^∞` on the open quadrant, from the weak hypothesis bundle.
  have hF : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- It suffices to prove the claim at every *interior* angle.
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo ?_
  intro θ hθ ρ hρ
  have hle : r ≤ ρ := hρ.1
  -- The slice `s ↦ ∂_z²Ψ(s,θ)` is continuous, hence interval integrable.
  have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ) (Set.uIcc r ρ) := by
    rw [Set.uIcc_of_le hle]
    exact ((hF.pzIter 2).curry_z hθ).continuousOn.mono
      (fun s hs => lt_of_lt_of_le hr hs.1)
  have hint : IntervalIntegrable (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ)
      MeasureTheory.volume r ρ := hcont.intervalIntegrable
  refine ⟨hint, ?_⟩
  -- The slice `s ↦ ∂_zΨ(s,θ)` has derivative `∂_z²Ψ` at every point of `[r,ρ]`.
  have hderiv : ∀ x ∈ Set.uIcc r ρ,
      HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter 1 Ψ z' θ)
        (Work.Spaces.pzIter 2 Ψ x θ) x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hr hx.1
    have hd := hF.hasDerivAt_slice_pzIter 1 hθ hxpos
    simpa using hd
  -- The fundamental theorem of calculus on the interval.
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa using hftc

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.hkMemW0L2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `hkMemW0L2`: the `L²`-slice and `L¹`-moments of `z² ∂_z²Ψ` are honest, with the
`√(π/2)` Cauchy–Schwarz bound

For a datum `(F, Ψ)` of the weak hypothesis class `TT.EllWeakPos α k F Ψ` with `k ≥ 1`:

1. for every `z ∈ Iz` the angular slice
   `θ ↦ ((z² ∂_z²Ψ) · w(z)/sin(2θ)^{η/2})²` is integrable on `Iθ` (this is the `i = 0`
   term of the weighted `ℋ^k`-integrand of `A = z²∂_z²Ψ`, and `HkMem α k A` is part of the
   hypothesis class);
2. the `θ`-integral of that slice is integrable in `z` on `Iz`;
3. for every `z > 0` the `L¹(sinθcos²θ)`-moment of `∂_z²Ψ` is controlled by the weighted
   `L²`-slice of `A` through Cauchy–Schwarz: since `sinθcos²θ ≤ 1 ≤ w(z)/sin(2θ)^{η/2}`
   on the open quadrant, `|∂_z²Ψ|·sinθcos²θ ≤ |A·w/sin^{η/2}|/z²`, and the Cauchy–Schwarz
   inequality with the constant function `1` on `Iθ` (whose mass is `π/2`) gives the factor
   `√(π/2)`.

These are precisely the hypotheses `hQJ` and `hCs` of
`Submission/Work/FTS/EllipticEst/remov/_scratch_core.lean`.
-/

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter
open scoped Real Topology Interval

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Elementary angular facts -/

private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  obtain ⟨h0, h1⟩ := hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
  rw [Work.Elliptic.sinCos2]
  positivity

private lemma sinCos2_eq_zero_of_sin_two_eq_zero {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.Elliptic.sinCos2 θ = 0 := by
  have h2 : Real.sin θ * Real.cos θ = 0 := by
    have h3 : 2 * (Real.sin θ * Real.cos θ) = 0 := by rw [← h, Real.sin_two_mul]; ring
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  rcases mul_eq_zero.mp h2 with h3 | h3
  · rw [Work.Elliptic.sinCos2, h3]; ring
  · rw [Work.Elliptic.sinCos2, h3]; ring

/-- The radial weight is at least `1` on `z > 0`. -/
private lemma one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, one_le_div (pow_pos hz 2)]
  nlinarith [hz]

/-- `sinθcos²θ ≤ w(z)/sin(2θ)^{η/2}` on `Iθ`, for `z > 0`. -/
private lemma sinCos2_le_wdiv {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Elliptic.sinCos2 θ ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
  have hsin2 := sin_two_nonneg_Iθ hθ
  have hsc1 : Work.Elliptic.sinCos2 θ ≤ 1 := by
    obtain ⟨h0, h1⟩ := hθ
    have hs : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
    have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
    have hc2 : Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [Real.cos_le_one θ, hc0, Real.neg_one_le_cos θ]
    rw [Work.Elliptic.sinCos2]
    nlinarith [hs, hs0, hc2]
  by_cases h0 : Real.sin (2 * θ) = 0
  · rw [sinCos2_eq_zero_of_sin_two_eq_zero h0]
    exact div_nonneg (le_trans zero_le_one (one_le_w hz)) (Real.rpow_nonneg hsin2 _)
  · have hspos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hsin2 (Ne.symm h0)
    have hrpow : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hsin2 (Real.sin_le_one _) (by rw [Work.Spaces.eta]; norm_num)
    have hr : 1 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
      rw [one_le_div (Real.rpow_pos_of_pos hspos _)]
      exact le_trans hrpow (one_le_w hz)
    linarith

/-- `|x| ≤ x² + 1`. -/
private lemma abs_le_sq_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  nlinarith [sq_abs x, sq_nonneg (|x| - 1), abs_nonneg x]

/-- `(1/z²)·|z²·(F·R)| = |F|·|R|` for `z > 0`. -/
private lemma one_div_zsq_mul_abs (z F R : ℝ) (hz : 0 < z) :
    (1 / z ^ 2) * |z ^ 2 * (F * R)| = |F| * |R| := by
  have hz2 : z ^ 2 ≠ 0 := ne_of_gt (pow_pos hz 2)
  rw [one_div, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 2), ← mul_assoc,
    inv_mul_cancel₀ hz2, one_mul]

/-! ## The function `A = z²∂_z²Ψ` is smooth on the open quadrant -/

private lemma smoothOpen_zsq_pzIter2 {Ψ : ℝ → ℝ → ℝ}
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hs
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    Work.FTS.EllipticEst.Q0
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2)
      Work.FTS.EllipticEst.Q0 := contDiffOn_fst.pow 2
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Work.FTS.EllipticEst.Q0 :=
    hsm.pzIter 2
  rw [show Function.uncurry (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      = (fun p : ℝ × ℝ => p.1 ^ 2) * (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) from rfl]
  exact h2.mul h3

/-! ## The outer integrability of a single weighted `D_z`-summand on all of `Iz` -/

/-- **A single weighted `D_z`-summand of the `ℋ^k`-integrand has integrable `θ`-integral on
all of `Iz`** (the non-compact version of `Work.FTS.EllipticEst.integrableOn_slice_l2`, whose
proof establishes exactly this and then restricts to `[a,b]`). -/
private lemma outer_zSummand {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (i : ℕ) (hi : i ≤ k) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i F s θ
          * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz := by
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter i F p.1 p.2
        * (Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_summand i)).pow 2
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i F s θ
          * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hjoint.integral_prod_right'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa only using h
  refine hmem.2.mono' haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with s hs
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
  exact MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => sq_nonneg _)
    (hmem.1 s hs)
    (MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      fun θ _ => Work.Spaces.sq_le_HkIntegrand_z α k F s θ i hi)

/-! ## Cauchy–Schwarz (`L¹(sinθcos²θ)` against the weighted `L²`-slice) -/

/-- **The `√(π/2)` bound.**  For `F` with `A := z²F`, on the open quadrant
`|F|·sinθcos²θ ≤ (1/z²)·|A·w/sin(2θ)^{η/2}|`, so Cauchy–Schwarz with the constant function
`1` on `Iθ` (whose mass is `π/2`) gives
`∫_θ |F|·sinθcos²θ ≤ (1/z²)√(π/2)√(∫_θ (A·w/sin(2θ)^{η/2})²)`. -/
private lemma L1_le_sqrt_aux {F : ℝ → ℝ → ℝ}
    (haesm : ∀ z : ℝ, 0 < z → MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (z ^ 2 * F z θ)
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hU : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((z ^ 2 * F z θ)
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ) :
    ∀ z : ℝ, 0 < z → ∫ θ in Work.Spaces.Iθ, |F z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, ((z ^ 2 * F z θ)
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
  intro z hz
  have hz2 : (0 : ℝ) < z ^ 2 := pow_pos hz 2
  have hz2ne : z ^ 2 ≠ 0 := ne_of_gt hz2
  have hwpos : 0 < Work.Spaces.w z := lt_of_lt_of_le zero_lt_one (one_le_w hz)
  set β : ℝ → ℝ := fun θ => (z ^ 2 * F z θ)
    * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) with hβdef
  have hβeq : (fun θ : ℝ => (β θ) ^ 2)
      = fun θ : ℝ => ((z ^ 2 * F z θ)
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [hβdef]
  have hUβ : MeasureTheory.IntegrableOn (fun θ => (β θ) ^ 2) Work.Spaces.Iθ := by
    simpa only [hβeq] using hU z hz
  have haesmβ : MeasureTheory.AEStronglyMeasurable β
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    simpa only [hβdef] using haesm z hz
  have haesm_abs : MeasureTheory.AEStronglyMeasurable (fun θ => |β θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    simpa only [Real.norm_eq_abs] using haesmβ.norm
  -- `|β|` is integrable: `|β| ≤ β² + 1`.
  have hβabs : MeasureTheory.IntegrableOn (fun θ => |β θ|) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (g := fun θ => (β θ) ^ 2 + 1) ?_ haesm_abs ?_
    · have h1 : MeasureTheory.IntegrableOn (fun θ => (β θ) ^ 2 + 1) Work.Spaces.Iθ :=
        hUβ.add (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      exact MeasureTheory.IntegrableOn.integrable h1
    · filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
      exact abs_le_sq_add_one (β θ)
  have hβabsmul : MeasureTheory.IntegrableOn (fun θ => (1 / z ^ 2) * |β θ|) Work.Spaces.Iθ :=
    hβabs.const_mul _
  -- pointwise domination on `Iθ`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      |F z θ| * Work.Elliptic.sinCos2 θ ≤ (1 / z ^ 2) * |β θ| := by
    intro θ hθ
    have hsc := sinCos2_le_wdiv hz hθ
    have hr0 : 0 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
      div_nonneg (le_of_lt hwpos) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
    have hβval : β θ = z ^ 2 * (F z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) := by
      rw [hβdef]; ring
    rw [hβval, one_div_zsq_mul_abs z (F z θ)
      (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) hz, abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_left hsc (abs_nonneg _)
  have hmain : (∫ θ in Work.Spaces.Iθ, |F z θ| * Work.Elliptic.sinCos2 θ)
      ≤ (1 / z ^ 2) * ∫ θ in Work.Spaces.Iθ, |β θ| := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (f := fun θ => |F z θ| * Work.Elliptic.sinCos2 θ)
      (g := fun θ => (1 / z ^ 2) * |β θ|)
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Iθ hθ)))
      hβabsmul
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => hpt θ hθ))
    rwa [MeasureTheory.integral_const_mul] at h
  -- Cauchy–Schwarz with the constant function `1`
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ⟨by rw [Work.Spaces.Iθ, Measure.restrict_apply_univ, Real.volume_Icc];
        exact ENNReal.ofReal_lt_top⟩
  have hu : MeasureTheory.MemLp (fun θ => |β θ|) 2
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haesm_abs).mpr
      (hUβ.congr (Filter.Eventually.of_forall fun θ => (sq_abs (β θ)).symm))
  have hv : MeasureTheory.MemLp (fun _ : ℝ => (1 : ℝ)) 2
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := MeasureTheory.memLp_const 1
  have hcs := Work.Spaces.cs_integral hu hv
  have hvval : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2),
      intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  have hcs' : (∫ θ in Work.Spaces.Iθ, |β θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (β θ) ^ 2) * (Real.pi / 2) := by
    have h := hcs
    have h1 : (∫ x in Work.Spaces.Iθ, |β x| * (fun _ : ℝ => (1 : ℝ)) x)
        = ∫ x in Work.Spaces.Iθ, |β x| :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun x _ => by simp)
    have h2 : (∫ x in Work.Spaces.Iθ, |β x| ^ 2)
        = ∫ x in Work.Spaces.Iθ, (β x) ^ 2 :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun x _ => sq_abs (β x))
    have h3 : (∫ x in Work.Spaces.Iθ, ((fun _ : ℝ => (1 : ℝ)) x) ^ 2)
        = Real.pi / 2 := by
      have hfun : (fun x : ℝ => ((fun _ : ℝ => (1 : ℝ)) x) ^ 2)
          = fun _ : ℝ => (1 : ℝ) := by
        funext x; simp
      rw [hfun]
      simpa using hvval
    rw [h1, h2, h3] at h
    exact h
  have hsnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, |β θ| :=
    MeasureTheory.integral_nonneg fun θ => abs_nonneg _
  have hsqnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (β θ) ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hsqrt : (∫ θ in Work.Spaces.Iθ, |β θ|)
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (β θ) ^ 2) * Real.sqrt (Real.pi / 2) := by
    calc (∫ θ in Work.Spaces.Iθ, |β θ|)
        = Real.sqrt ((∫ θ in Work.Spaces.Iθ, |β θ|) ^ 2) := (Real.sqrt_sq hsnn).symm
      _ ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, (β θ) ^ 2) * (Real.pi / 2)) :=
          Real.sqrt_le_sqrt hcs'
      _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, (β θ) ^ 2) * Real.sqrt (Real.pi / 2) :=
          Real.sqrt_mul hsqnn _
  have key : (∫ θ in Work.Spaces.Iθ, |F z θ| * Work.Elliptic.sinCos2 θ)
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (β θ) ^ 2) := by
    calc (∫ θ in Work.Spaces.Iθ, |F z θ| * Work.Elliptic.sinCos2 θ)
        ≤ (1 / z ^ 2) * ∫ θ in Work.Spaces.Iθ, |β θ| := hmain
      _ ≤ (1 / z ^ 2) * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (β θ) ^ 2)
            * Real.sqrt (Real.pi / 2)) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = (1 / z ^ 2) * Real.sqrt (Real.pi / 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, (β θ) ^ 2) := by ring
  rwa [hβeq] at key

/-! ## The target -/

theorem hkMemW0L2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ) ∧
    (MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz) ∧
    (∀ z : ℝ, 0 < z → ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2))
  := by
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq_pzIter2 h.smooth
  -- (1) the angular slices are integrable: the `i = 0` weighted `D_z`-summand of `A`
  have hpart1 : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ := by
    intro z hz
    simpa only [Work.Spaces.DzIter_zero] using
      Work.FTS.EllipticEst.integrableOn_zSummand α k hA h.memA 0 (Nat.zero_le k) hz
  -- (2) the `θ`-integral of that slice is integrable in `z`
  have hpart2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz := by
    simpa only [Work.Spaces.DzIter_zero] using
      outer_zSummand (α := α) (k := k)
        (F := fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hA h.memA 0 (Nat.zero_le k)
  -- (3) Cauchy-Schwarz
  have hpart3 : ∀ z : ℝ, 0 < z → ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    intro z hz
    exact L1_le_sqrt_aux (F := fun z θ : ℝ => Work.Spaces.pzIter 2 Ψ z θ)
      (fun z hz => by
        simpa only [Work.Spaces.DzIter_zero] using hA.aesm_slice_summand 0 hz)
      (fun z hz => hpart1 z (Set.mem_Ici.mpr (le_of_lt hz)))
      z hz
  exact ⟨hpart1, hpart2, hpart3⟩

end

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.pzSliceFubiniZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Fubini for the `∂_z`-slice integrals of the angular moment, plus vanishing of the angular
integral when both `Fstar`-moments vanish.**

Since `Work.Elliptic.Fstar Ψ z = ∫_{Iθ} Ψ z θ sin θ cos²θ dθ`, the fundamental theorem of
calculus in `z` gives, for every angle `θ`,

`∫_{r}^{z₁} ∂_z Ψ z θ * sin θ cos²θ dz = (Ψ z₁ θ - Ψ r θ) * sin θ cos²θ`,

and upon integrating in `θ` the two `Fstar`-terms cancel because `Fstar Ψ r = Fstar Ψ z₁ = 0`.
The first conjunct is Tonelli/Fubini for the product measure on `Ioc r z₁ × Iθ`. -/
theorem pzSliceFubiniZero {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {r z₁ : ℝ} (hr : 0 < r) (hrz : r < z₁)
    (hΨr : MeasureTheory.Integrable (fun θ : ℝ => Ψ r θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hΨz : MeasureTheory.Integrable (fun θ : ℝ => Ψ z₁ θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hFr : Work.Elliptic.Fstar Ψ r = 0) (hFz : Work.Elliptic.Fstar Ψ z₁ = 0)
    (hrect : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc r z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∫ z in r..z₁, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      = (∫ θ in Work.Spaces.Iθ, ∫ z in r..z₁,
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) ∧
    (∫ θ in Work.Spaces.Iθ, ∫ z in r..z₁,
      Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) = 0
  := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- Tonelli/Fubini on the product `Ioc r z₁ × Iθ`.
  have hswap : (∫ z in Set.Ioc r z₁,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioc r z₁,
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ :=
    MeasureTheory.integral_integral_swap hrect
  constructor
  · have hout : (∫ z in r..z₁,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
        = ∫ z in Set.Ioc r z₁,
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) :=
      intervalIntegral.integral_of_le hrz.le
    have hin : (∫ θ in Work.Spaces.Iθ, ∫ z in r..z₁,
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioc r z₁,
            Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ := by
      refine MeasureTheory.setIntegral_congr_ae hmeasIθ ?_
      exact Filter.Eventually.of_forall (fun θ _ => intervalIntegral.integral_of_le hrz.le)
    exact hout.trans (hswap.trans hin.symm)
  · -- The `θ`-vanishing: integrate the `z`-FTC of the slice.
    have hsin0 : Work.Elliptic.sinCos2 0 = 0 := by simp [Work.Elliptic.sinCos2]
    have hsinpi : Work.Elliptic.sinCos2 (π / 2) = 0 := by simp [Work.Elliptic.sinCos2]
    have hpt : ∀ θ ∈ Work.Spaces.Iθ,
        (∫ z in r..z₁, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
          = (Ψ z₁ θ - Ψ r θ) * Work.Elliptic.sinCos2 θ := by
      intro θ hθ
      rw [intervalIntegral.integral_mul_const]
      by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
      · -- interior angle: the fundamental theorem of calculus in `z` for the slice
        have hderiv : ∀ x ∈ Set.uIcc r z₁,
            HasDerivAt (fun z' => Ψ z' θ) (Work.Spaces.pz Ψ x θ) x := by
          intro x hx
          rw [Set.uIcc_of_le hrz.le] at hx
          exact hsm.hasDerivAt_slice hθi (lt_of_lt_of_le hr hx.1)
        have hcont : ContinuousOn (fun z => Work.Spaces.pz Ψ z θ) (Set.uIcc r z₁) := by
          have hc : ContinuousOn (fun z => Work.Spaces.pz Ψ z θ) (Set.Ioi 0) :=
            ((hsm.pz).curry_z hθi).continuousOn
          refine hc.mono ?_
          intro x hx
          rw [Set.uIcc_of_le hrz.le] at hx
          exact lt_of_lt_of_le hr hx.1
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
      · -- endpoint angle: `sin θ cos²θ` vanishes, so both sides are zero
        have hθ' : θ = 0 ∨ θ = π / 2 := by
          rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
          rw [Set.mem_Ioo] at hθi
          by_cases h0 : 0 < θ
          · exact Or.inr (le_antisymm hθ.2 (not_lt.mp (fun hlt => hθi ⟨h0, hlt⟩)))
          · exact Or.inl (le_antisymm (not_lt.mp h0) hθ.1)
        rcases hθ' with h | h
        · rw [h, hsin0]; ring
        · rw [h, hsinpi]; ring
    have hpt_int : (∫ θ in Work.Spaces.Iθ, ∫ z in r..z₁,
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ, (Ψ z₁ θ - Ψ r θ) * Work.Elliptic.sinCos2 θ :=
      MeasureTheory.setIntegral_congr_ae hmeasIθ (Filter.Eventually.of_forall hpt)
    have hsplit : (∫ θ in Work.Spaces.Iθ, (Ψ z₁ θ - Ψ r θ) * Work.Elliptic.sinCos2 θ)
        = (∫ θ in Work.Spaces.Iθ, Ψ z₁ θ * Work.Elliptic.sinCos2 θ)
          - (∫ θ in Work.Spaces.Iθ, Ψ r θ * Work.Elliptic.sinCos2 θ) := by
      rw [show (fun θ => (Ψ z₁ θ - Ψ r θ) * Work.Elliptic.sinCos2 θ)
            = (fun θ => Ψ z₁ θ * Work.Elliptic.sinCos2 θ - Ψ r θ * Work.Elliptic.sinCos2 θ)
          from by funext θ; ring]
      exact MeasureTheory.integral_sub hΨz hΨr
    rw [hpt_int, hsplit]
    simp only [Work.Elliptic.Fstar] at hFz hFr
    rw [hFz, hFr]
    ring

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EpsEngine.aesm_uncurry_of_continuousOn_of_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open MeasureTheory Set Metric Filter
open scoped Real Topology
open Classical

noncomputable section

/-- The open quadrant `(0,∞) × (0,π/2)` on which the `s`-slices are continuous. -/
private def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

private lemma isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

/-- The mesh `1/(n+1)` of the `n`-th approximation. -/
private def eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private lemma eps_pos (n : ℕ) : 0 < eps n := by rw [eps]; positivity

/-- The `k`-th cell of the `n`-th approximation: the ball of radius `1/(n+1)` about `c k`,
intersected with the quadrant `Qd`, minus the union of the previous such balls.  These cells
are a measurable partition of `Qd` into pieces of radius `< 1/(n+1)`. -/
private def cells (c : ℕ → ℝ × ℝ) (n k : ℕ) : Set (ℝ × ℝ) :=
  (Metric.ball (c k) (eps n) ∩ Qd) \ (⋃ j ∈ Finset.range k, Metric.ball (c j) (eps n))

private lemma cells_subset_Qd (c : ℕ → ℝ × ℝ) (n k : ℕ) : cells c n k ⊆ Qd :=
  Set.sdiff_subset.trans Set.inter_subset_right

private lemma cells_subset_ball {c : ℕ → ℝ × ℝ} {n k : ℕ} {q : ℝ × ℝ}
    (hq : q ∈ cells c n k) : dist q (c k) < eps n := hq.1.1

private lemma measurableSet_cells (c : ℕ → ℝ × ℝ) (n k : ℕ) : MeasurableSet (cells c n k) := by
  refine (Metric.isOpen_ball.measurableSet.inter isOpen_Qd.measurableSet).diff ?_
  exact MeasurableSet.biUnion (Finset.countable_toSet (Finset.range k))
    (fun j _ => Metric.isOpen_ball.measurableSet)

/-- Every point of the quadrant lies in some cell of the `n`-th approximation. -/
private lemma exists_mem_cells {c : ℕ → ℝ × ℝ}
    (hc : ∀ q : ℝ × ℝ, ∀ ε > 0, ∃ k, dist q (c k) < ε) (n : ℕ) {q : ℝ × ℝ} (hq : q ∈ Qd) :
    ∃ k, q ∈ cells c n k := by
  obtain ⟨k, hk⟩ := hc q (eps n) (eps_pos n)
  have hex : ∃ j, dist q (c j) < eps n := ⟨k, hk⟩
  refine ⟨Nat.find hex, ⟨⟨Nat.find_spec hex, hq⟩, ?_⟩⟩
  intro hmem
  simp only [Set.mem_iUnion, Finset.mem_range] at hmem
  obtain ⟨j, hjlt, hjball⟩ := hmem
  exact Nat.find_min hex hjlt hjball

/-- Distinct cells of the same approximation are disjoint. -/
private lemma cells_disjoint {c : ℕ → ℝ × ℝ} {n k l : ℕ} (hkl : k ≠ l) :
    Disjoint (cells c n k) (cells c n l) := by
  rw [Set.disjoint_left]
  intro q hqk hql
  rcases lt_or_gt_of_ne hkl with h | h
  · have hmem : q ∈ ⋃ j ∈ Finset.range l, Metric.ball (c j) (eps n) :=
      Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr h, hqk.1.1⟩⟩
    exact hql.2 hmem
  · have hmem : q ∈ ⋃ j ∈ Finset.range k, Metric.ball (c j) (eps n) :=
      Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr h, hql.1.1⟩⟩
    exact hqk.2 hmem

/-- The `m`-th partial sum of the `n`-th locally constant approximation of `g`. -/
private def partialSum (g : ℝ → ℝ → ℝ → ℝ) (c : ℕ → ℝ × ℝ) (n m : ℕ) :
    ℝ × (ℝ × ℝ) → ℝ :=
  fun p => ∑ k ∈ Finset.range m,
    (cells c n k).indicator (fun _ : ℝ × ℝ => (1 : ℝ)) p.2 * g p.1 (c k).1 (c k).2

private lemma partialSum_apply (g : ℝ → ℝ → ℝ → ℝ) (c : ℕ → ℝ × ℝ) (n m : ℕ)
    (p : ℝ × (ℝ × ℝ)) :
    partialSum g c n m p = ∑ k ∈ Finset.range m,
      (cells c n k).indicator (fun _ : ℝ × ℝ => (1 : ℝ)) p.2 * g p.1 (c k).1 (c k).2 := rfl

/-- The `n`-th locally constant approximation of `g`. -/
private def approx (g : ℝ → ℝ → ℝ → ℝ) (c : ℕ → ℝ × ℝ) (n : ℕ) :
    ℝ × (ℝ × ℝ) → ℝ :=
  fun p => if h : ∃ k, p.2 ∈ cells c n k then g p.1 (c (Nat.find h)).1 (c (Nat.find h)).2 else 0

private lemma approx_apply (g : ℝ → ℝ → ℝ → ℝ) (c : ℕ → ℝ × ℝ) (n : ℕ)
    (p : ℝ × (ℝ × ℝ)) :
    approx g c n p = (if h : ∃ k, p.2 ∈ cells c n k then
      g p.1 (c (Nat.find h)).1 (c (Nat.find h)).2 else 0) := rfl

private lemma approx_eq_of_pos (g : ℝ → ℝ → ℝ → ℝ) (c : ℕ → ℝ × ℝ) (n : ℕ)
    (p : ℝ × (ℝ × ℝ)) (h : ∃ k, p.2 ∈ cells c n k) :
    approx g c n p = g p.1 (c (Nat.find h)).1 (c (Nat.find h)).2 := by
  rw [approx_apply]; exact dif_pos h

private lemma approx_eq_of_neg (g : ℝ → ℝ → ℝ → ℝ) (c : ℕ → ℝ × ℝ) (n : ℕ)
    (p : ℝ × (ℝ × ℝ)) (h : ¬ ∃ k, p.2 ∈ cells c n k) : approx g c n p = 0 := by
  rw [approx_apply]; exact dif_neg h

/-- Finite sums of a.e. strongly measurable functions are a.e. strongly measurable. -/
private lemma ae_finset_sum {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {f : ι → α → ℝ}
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun a => ∑ i ∈ s, f i a) μ := by
  induction s using Finset.induction with
  | empty => simpa using (aestronglyMeasurable_const (b := (0 : ℝ)) (μ := μ))
  | insert i s hi ih =>
      have h1 : AEStronglyMeasurable (f i) μ := hf i (Finset.mem_insert_self i s)
      have h2 : AEStronglyMeasurable (fun a => ∑ x ∈ s, f x a) μ :=
        ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
      refine (h1.add h2).congr (Filter.Eventually.of_forall fun a => ?_)
      simp only [Pi.add_apply, Finset.sum_insert hi]

/-- A.e. strong measurability is preserved by viewing a function of the first coordinate as a
function on a product. -/
private lemma ae_comp_fst {h : ℝ → ℝ} (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => h p.1) volume := by
  have h := hh.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (ℝ × ℝ))))
  exact h

/-- Each summand of the approximation is a.e. strongly measurable. -/
private lemma ae_term {g : ℝ → ℝ → ℝ → ℝ}
    (hmeas : ∀ q : ℝ × ℝ, AEStronglyMeasurable (fun s : ℝ => g s q.1 q.2) volume)
    (c : ℕ → ℝ × ℝ) (n k : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × (ℝ × ℝ) =>
        (cells c n k).indicator (fun _ : ℝ × ℝ => (1 : ℝ)) p.2 * g p.1 (c k).1 (c k).2)
      volume := by
  refine (Measurable.aestronglyMeasurable ?_).mul ?_
  · exact (Measurable.indicator measurable_const (measurableSet_cells c n k)).comp measurable_snd
  · exact ae_comp_fst (hmeas (c k))

private lemma ae_partialSum {g : ℝ → ℝ → ℝ → ℝ}
    (hmeas : ∀ q : ℝ × ℝ, AEStronglyMeasurable (fun s : ℝ => g s q.1 q.2) volume)
    (c : ℕ → ℝ × ℝ) (n m : ℕ) :
    AEStronglyMeasurable (partialSum g c n m) volume :=
  (ae_finset_sum (Finset.range m) (fun k _ => ae_term hmeas c n k)).congr
    (Filter.Eventually.of_forall fun _ => rfl)

/-- The partial sums converge (pointwise, in fact eventually constantly) to the approximant. -/
private lemma partialSum_tendsto {g : ℝ → ℝ → ℝ → ℝ} {c : ℕ → ℝ × ℝ} {n : ℕ}
    (hd : ∀ k l : ℕ, k ≠ l → Disjoint (cells c n k) (cells c n l)) (p : ℝ × (ℝ × ℝ)) :
    Tendsto (fun m => partialSum g c n m p) atTop (𝓝 (approx g c n p)) := by
  by_cases h : ∃ k, p.2 ∈ cells c n k
  · have hfind : p.2 ∈ cells c n (Nat.find h) := Nat.find_spec h
    rw [approx_eq_of_pos g c n p h]
    refine tendsto_atTop_of_eventually_const (i₀ := Nat.find h + 1) fun m hm => ?_
    rw [partialSum_apply, Finset.sum_eq_single (Nat.find h)]
    · rw [Set.indicator_of_mem hfind]; simp
    · intro k _ hne
      have hnk : p.2 ∉ cells c n k :=
        fun hmem => (Set.disjoint_left.mp (hd k (Nat.find h) hne)) hmem hfind
      rw [Set.indicator_of_notMem hnk]; simp
    · intro hnot
      exact absurd (Finset.mem_range.mpr hm) hnot
  · rw [approx_eq_of_neg g c n p h]
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun m => ?_)
    show (0 : ℝ) = partialSum g c n m p
    rw [partialSum_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    have hnk : p.2 ∉ cells c n k := fun hmem => h ⟨k, hmem⟩
    rw [Set.indicator_of_notMem hnk]; simp

private lemma ae_approx {g : ℝ → ℝ → ℝ → ℝ}
    (hmeas : ∀ q : ℝ × ℝ, AEStronglyMeasurable (fun s : ℝ => g s q.1 q.2) volume)
    (c : ℕ → ℝ × ℝ) (n : ℕ) :
    AEStronglyMeasurable (approx g c n) volume :=
  aestronglyMeasurable_of_tendsto_ae atTop (fun m => ae_partialSum hmeas c n m)
    (Filter.Eventually.of_forall fun p => partialSum_tendsto (fun k l hkl => cells_disjoint hkl) p)

/-- The approximants converge pointwise to `g`, using continuity on the open quadrant (and the
fact that the approximants are `0` off it). -/
private lemma approx_tendsto {g : ℝ → ℝ → ℝ → ℝ} {c : ℕ → ℝ × ℝ}
    (hcont : ∀ s : ℝ, ContinuousOn (fun q : ℝ × ℝ => g s q.1 q.2) Qd)
    (hzero : ∀ s : ℝ, ∀ q : ℝ × ℝ, q ∉ Qd → g s q.1 q.2 = 0)
    (hc : ∀ q : ℝ × ℝ, ∀ ε > 0, ∃ k, dist q (c k) < ε) (p : ℝ × (ℝ × ℝ)) :
    Tendsto (fun n => approx g c n p) atTop (𝓝 (g p.1 p.2.1 p.2.2)) := by
  by_cases hp : p.2 ∈ Qd
  · have hex : ∀ n, ∃ k, p.2 ∈ cells c n k := fun n => exists_mem_cells hc n hp
    have hdist : ∀ n, dist (c (Nat.find (hex n))) p.2 < eps n := by
      intro n
      have h := cells_subset_ball (c := c) (n := n) (k := Nat.find (hex n))
        (Nat.find_spec (hex n))
      rwa [dist_comm] at h
    have htend : Tendsto (fun n => c (Nat.find (hex n))) atTop (𝓝 p.2) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hdist n)) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hct : ContinuousAt (fun q : ℝ × ℝ => g p.1 q.1 q.2) p.2 :=
      (hcont p.1).continuousAt (isOpen_Qd.mem_nhds hp)
    have hcomp := hct.tendsto.comp htend
    refine hcomp.congr' (Filter.Eventually.of_forall fun n => ?_)
    show g p.1 (c (Nat.find (hex n))).1 (c (Nat.find (hex n))).2 = approx g c n p
    exact (approx_eq_of_pos g c n p (hex n)).symm
  · have hno : ∀ n, ¬ ∃ k, p.2 ∈ cells c n k := fun n ⟨k, hk⟩ => hp (cells_subset_Qd c n k hk)
    have hz : g p.1 p.2.1 p.2.2 = 0 := hzero p.1 p.2 hp
    rw [hz]
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => ?_)
    show (0 : ℝ) = approx g c n p
    exact (approx_eq_of_neg g c n p (hno n)).symm

/-- **Carathéodory measurability, in the shape needed by the local step of the `ε`-scheme.**  If
`g : ℝ → ℝ → ℝ → ℝ` is, for every `s`, continuous on the open quadrant `Q0` and zero off it, and if
for every `(z,θ)` the map `s ↦ g s z θ` is a.e. strongly measurable, then `(s,z,θ) ↦ g s z θ` is
a.e. strongly measurable for the product measure.  (Proof: cover `Q0` by countably many balls of
radius `1/k` **intersected with `Q0`**, disjointify, and approximate `g` in the second variable by
the locally constant family; each approximant is measurable and converges pointwise to `g`.) -/
theorem aesm_uncurry_of_continuousOn_of_zero {g : ℝ → ℝ → ℝ → ℝ}
    (hcont : ∀ s : ℝ, ContinuousOn (fun q : ℝ × ℝ => g s q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzero : ∀ s : ℝ, ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → g s q.1 q.2 = 0)
    (hmeas : ∀ q : ℝ × ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => g s q.1 q.2)
      MeasureTheory.volume) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      MeasureTheory.volume := by
  obtain ⟨t, ht_count, ht_dense⟩ := TopologicalSpace.exists_countable_dense (ℝ × ℝ)
  obtain ⟨c, hc_range⟩ := ht_count.exists_eq_range ht_dense.nonempty
  have hdense : Dense (Set.range c) := hc_range ▸ ht_dense
  have hc : ∀ q : ℝ × ℝ, ∀ ε > 0, ∃ k, dist q (c k) < ε := by
    intro q ε hε
    have hx : q ∈ closure (Set.range c) := by
      rw [hdense.closure_eq]; exact Set.mem_univ q
    obtain ⟨b, hb, hbd⟩ := Metric.mem_closure_iff.mp hx ε hε
    obtain ⟨k, rfl⟩ := hb
    exact ⟨k, hbd⟩
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => ae_approx hmeas c n)
    (Filter.Eventually.of_forall fun p => approx_tendsto hcont hzero hc p)

end

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.LNA.IntegrableOn_DzIter_sq_sEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut.LNA

theorem IntegrableOn_DzIter_sq_sEta {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) (hb4 : b ≤ 4)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  -- The `D_z`-summand of `HkIntegrand` is integrable on the angular slice
  -- (`Work.FTS.EllipticEst.integrableOn_zSummand`), and it differs from the target
  -- integrand by the *constant* factor `w z ^ 2 ≠ 0`.
  have hs := Work.FTS.EllipticEst.integrableOn_zSummand α 4 hsm hmem b hb4
    (Set.mem_Ici.mpr hz.le)
  have hwz : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]; positivity
  refine MeasureTheory.IntegrableOn.congr_fun (hs.const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
  · -- the two integrands agree *everywhere* on `Iθ`
    intro θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    show (Work.Spaces.w z ^ 2)⁻¹ * (Work.Spaces.DzIter b f z θ *
        (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = Work.Spaces.DzIter b f z θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
    rw [show (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
        = Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)) by
      rw [div_eq_mul_inv, ← Real.rpow_neg hs0]]
    have hsq : (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2
        = Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hs0]
      congr 1
      ring
    rw [mul_pow, mul_pow, hsq]
    rw [show ((Work.Spaces.w z) ^ 2)⁻¹ *
          ((Work.Spaces.DzIter b f z θ) ^ 2 *
            ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))))
        = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2) *
          ((Work.Spaces.DzIter b f z θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) by ring,
      inv_mul_cancel₀ (pow_ne_zero 2 hwz), one_mul]
  · rw [Work.Spaces.Iθ]; exact measurableSet_Icc

end Work.FTS.GalBasis.cc.Subcut.LNA
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The pointwise identity -/

/-- For `s > 0` and `θ ∈ Iθ`, the integrand of the `L₁₂`-density is the radial weight
`Wlam s = 1/(s·w s)` times the weighted datum `Gaz h = h·w/Sw` against the angular profile
`K·Sw`.  (At the endpoints `θ = 0, π/2`, where `Sw` vanishes, both sides vanish because so
does `K`.) -/
lemma K_mul_h_div_s_eq (h : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.K θ * h s θ / s
        = Wlam s * (Work.Spaces.K θ * Sw θ * Gaz h s θ) := by
  intro θ hθ
  rw [Gaz, Wlam, Work.Spaces.w]
  by_cases hS : Sw θ = 0
  · have hK : Work.Spaces.K θ = 0 := sw_eq_zero_imp_K_eq_zero hθ hS
    rw [hS, hK]
    simp
  · have hS' : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≠ 0 := by
      simpa only [Sw] using hS
    have h1s : (1 : ℝ) + s ≠ 0 := by linarith
    field_simp

/-- The `L₁₂`-density as a constant multiple of the angular integral of the weighted datum. -/
lemma L12dens_eq_weighted (h : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    Work.Construction.L12dens h s
      = Wlam s * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Sw θ * Gaz h s θ := by
  have hI : Work.Spaces.Iθ = Set.Icc 0 (π / 2) := rfl
  calc Work.Construction.L12dens h s
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s := by
        rw [Work.Construction.L12dens, Work.FM.L12dens, hI]
    _ = ∫ θ in Work.Spaces.Iθ, Wlam s * (Work.Spaces.K θ * Sw θ * Gaz h s θ) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => K_mul_h_div_s_eq h hs θ (by simpa only [hI] using hθ))] with θ hθ
        exact hθ
    _ = Wlam s * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Sw θ * Gaz h s θ :=
        integral_const_mul _ _

/-! ## The pointwise bound on the density -/

lemma abs_L12dens_le (α : ℝ) (h : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 h)
    {s : ℝ} (hs : 0 < s) :
    |Work.Construction.L12dens h s|
      ≤ Wlam s * (BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h s θ)) := by
  rw [L12dens_eq_weighted h hs, abs_mul, abs_of_nonneg (Wlam_nonneg hs.le)]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_K_S_Gaz_le α h (hmem.1 s hs.le)) (Wlam_nonneg hs.le)

/-! ## The main theorem -/

/-- Route (Cauchy–Schwarz, `α`-free).  `L12 h 0 = ∫_{s>0} ∫_θ K θ · h s θ / s`.  Put
`g := h · w / sin(2θ)^{η/2}`; then `K θ h/s = g · (K θ sin(2θ)^{η/2} s/(1+s)²)`, and the second
factor has finite `L²(dz dθ)`-norm (constant in `α`).  Hence
`|L12 h 0| ≤ (∫∫ g²)^{1/2} · (∫_θ K² sin^η)^{1/2} · (∫_s s²/(1+s)⁴)^{1/2}`,
and `∫∫ g² ≤ HkSq α 4 h` since `(DzIter 0 h · w/sin(2θ)^{η/2})² = g²` is the `i = 0` summand of
`HkIntegrand α 4 h` (all summands are squares).  Finally `HkNorm α 4 h = sqrt (HkSq α 4 h)`.
The only care needed is the integrability bookkeeping: `HkMem α 4 h` gives `IntegrableOn`
of the θ-slice for every `z ∈ Iz` and integrability of the marginal in `z`, and if the
`θ`-integral of `K θ h/s` is not integrable, `MeasureTheory.integral_undef` makes it `0`, which
is even better. -/
theorem abs_L12_le_HkNorm : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : Work.FTS.Galerkin.Fn),
    Work.Spaces.HkMem α 4 h → |Work.Construction.L12 h 0| ≤ C * Work.Spaces.HkNorm α 4 h := by
  refine ⟨BK * Real.sqrt W2 + 1, by nlinarith [BK_nonneg, Real.sqrt_nonneg W2], ?_⟩
  intro α h hmem
  have hbd : ∀ s ∈ Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s|
      ≤ Wlam s * (BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h s θ)) :=
    fun s hs => abs_L12dens_le α h hmem hs
  have hL12 : Work.Construction.L12 h 0
      = ∫ s in Set.Ioi (0 : ℝ), Work.Construction.L12dens h s := rfl
  calc |Work.Construction.L12 h 0|
      = |∫ s in Set.Ioi (0 : ℝ), Work.Construction.L12dens h s| := by rw [hL12]
    _ ≤ ∫ s in Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s| := by
        simpa only [Real.norm_eq_abs] using
          (MeasureTheory.norm_integral_le_integral_norm
            (μ := volume.restrict (Set.Ioi (0 : ℝ)))
            (f := fun s => Work.Construction.L12dens h s))
    _ ≤ BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 4 h) :=
        integral_abs_L12dens_le α h hmem hbd
    _ = (BK * Real.sqrt W2) * Work.Spaces.HkNorm α 4 h := by
        rw [Work.Spaces.HkNorm]
    _ ≤ (BK * Real.sqrt W2 + 1) * Work.Spaces.HkNorm α 4 h := by
        have hx := Work.Spaces.HkNorm_nonneg α 4 h
        nlinarith

end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option maxHeartbeats 800000

/-- The square of the weighted datum is the `D_z^0`-summand of the `ℋ^k`-integrand, at every
order `k`. -/
lemma Gaz_sq_le_HkIntegrand_gen (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Gaz h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k h z θ := by
  simpa only [Gaz, Sw, Work.Spaces.DzIter_zero] using
    Work.Spaces.sq_le_HkIntegrand_z α k h z θ 0 (Nat.zero_le k)

/-- At every order `k`, `|Gaz|` is dominated by the square root of the `ℋ^k`-integrand. -/
lemma abs_Gaz_le_sqrt_HkIntegrand_gen (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    |Gaz h z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α k h z θ) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Gaz_sq_le_HkIntegrand_gen α k h z θ)

theorem abs_integral_K_S_Gaz_le_gen (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ) {s : ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k h s θ)
      Work.Spaces.Iθ) :
    |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ
        * Work.FTS.GalBasis.cc.Gaz h s θ|
      ≤ Work.FTS.GalBasis.cc.BK
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h s θ) := by
  -- the angular profile, the weighted datum and the square root of the majorant
  set u : ℝ → ℝ := fun θ => Work.Spaces.K θ * Sw θ with hu
  set v : ℝ → ℝ := fun θ => Gaz h s θ with hv
  set w : ℝ → ℝ := fun θ => Real.sqrt (Work.Spaces.HkIntegrand α k h s θ) with hw
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hHk_nn : ∀ θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α k h s θ :=
    fun θ => Work.Spaces.HkIntegrand_nonneg α k h s θ
  have hw_nn : ∀ θ : ℝ, 0 ≤ w θ := by
    intro θ; rw [hw]; exact Real.sqrt_nonneg _
  -- the pointwise domination of the weighted datum by `w`
  have hvw : ∀ θ : ℝ, |v θ| ≤ w θ := by
    intro θ; rw [hv, hw]; exact abs_Gaz_le_sqrt_HkIntegrand_gen α k h s θ
  -- continuity/measurability
  have hcont_K : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hcont_u : Continuous u := by
    rw [hu]; exact hcont_K.mul continuous_sw
  have hw_aesm : AEStronglyMeasurable w (volume.restrict Work.Spaces.Iθ) := by
    rw [hw]
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  -- integrability of `u²` and of `w²`
  have hu2_int : IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    (hcont_u.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hw2_int : IntegrableOn (fun θ => (w θ) ^ 2) Work.Spaces.Iθ := by
    refine hint.congr_fun (fun θ _ => ?_) hIθ
    rw [hw]; exact (Real.sq_sqrt (hHk_nn θ)).symm
  -- integrability of the majorant `|u|·w`
  have huw_int : IntegrableOn (fun θ => |u θ| * w θ) Work.Spaces.Iθ := by
    have hmaj : IntegrableOn (fun θ => ((u θ) ^ 2 + (w θ) ^ 2) / 2) Work.Spaces.Iθ :=
      (hu2_int.add hw2_int).div_const 2
    refine hmaj.mono' ((hcont_u.abs.aestronglyMeasurable).mul hw_aesm) ?_
    filter_upwards with θ
    have h1 : 0 ≤ |u θ| := abs_nonneg _
    have h2 : 0 ≤ w θ := hw_nn θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1]
    have key : |u θ| * w θ ≤ (|u θ| ^ 2 + (w θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|u θ| - w θ), sq_nonneg (|u θ| + w θ)]
    rw [sq_abs (u θ)] at key
    exact key
  -- `L²`-membership of the two measurable factors
  have hMemLp_u : MemLp (fun θ => |u θ|) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => |u θ|) hcont_u.abs.aestronglyMeasurable).mpr
      (hu2_int.congr (Filter.Eventually.of_forall fun θ => (sq_abs (u θ)).symm))
  have hMemLp_w : MemLp w 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ) hw_aesm).mpr hw2_int
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt (u := fun θ => |u θ|)
    (v := w) hMemLp_u hMemLp_w
  -- the two square roots of the integrals
  have hsqrt_u : Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2) = BK := by
    rw [BK]
    congr 1
    simp only [hu]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun θ => sq_abs (Work.Spaces.K θ * Sw θ))
  have hsqrt_w : Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h s θ) := by
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    rw [hw]; exact Real.sq_sqrt (hHk_nn θ)
  -- the three steps
  have h1 : |∫ θ in Work.Spaces.Iθ, u θ * v θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun θ => u θ * v θ))
  have h2 : ∫ θ in Work.Spaces.Iθ, |u θ * v θ| ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) huw_int
      (Filter.Eventually.of_forall fun θ => ?_)
    show |u θ * v θ| ≤ |u θ| * w θ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hvw θ) (abs_nonneg _)
  have h3 : ∫ θ in Work.Spaces.Iθ, |u θ| * w θ
      = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := by
    rw [abs_of_nonneg]
    exact MeasureTheory.integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (hw_nn θ)
  calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Sw θ * Gaz h s θ|
      = |∫ θ in Work.Spaces.Iθ, u θ * v θ| := by simp only [hu, hv]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := h1
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := h2
    _ = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := h3
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2) := hcs
    _ = BK * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h s θ) := by
        rw [hsqrt_u, hsqrt_w]

end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.integral_abs_L12dens_le_Ioi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc

open MeasureTheory Filter

/-- Monotonicity of the set integral over the half-line: since `(z,∞) ⊆ (0,∞)` for `0 ≤ z`,
a nonnegative function integrable on `(0,∞)` has a smaller integral on `(z,∞)`. -/
lemma setIntegral_Ioi_le_Ioi_zero {f : ℝ → ℝ} {z : ℝ} (hz : 0 ≤ z)
    (hint : IntegrableOn f (Set.Ioi 0)) (hnn : ∀ s, 0 ≤ f s) :
    ∫ s in Set.Ioi z, f s ≤ ∫ s in Set.Ioi 0, f s :=
  setIntegral_mono_set hint (Filter.Eventually.of_forall hnn)
    (Filter.Eventually.of_forall fun x hx => by
      simp only [Set.mem_Ioi] at hx ⊢
      linarith)

/-- **The integrated pointwise bound on the `L₁₂`-density, on the tail `(z,∞)`.**
If `|L12dens h s| ≤ Wlam s · (BK · √(∫_θ HkIntegrand α k h s θ))` for every `s > z` and
`h ∈ ℋ^k_α`, then the same bound holds after integrating in `s` over `(z,∞)`, with a constant
that does not depend on `k` or on `z`:

`∫_{s>z} |L12dens h s| ≤ BK · √W2 · √(HkSq α k h)`.

This is Cauchy–Schwarz in the radial variable: the weight `Wlam` is square-integrable on
`(0,∞)` with `∫_{(0,∞)} Wlam² = W2`, and
`∫_{(z,∞)} (√(∫_θ HkIntegrand))² ≤ ∫_{(0,∞)} (√(∫_θ HkIntegrand))² = HkSq α k h`
(the sets `(0,∞)` and `ℤ = [0,∞)` differ by the null set `{0}`, and `(z,∞) ⊆ (0,∞)` for
`z ≥ 0`, where both integrands are nonnegative). -/
theorem integral_abs_L12dens_le_Ioi (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α k h) {z : ℝ} (hz : 0 ≤ z)
    (hbd : ∀ s ∈ Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h s θ))) :
    ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2
        * Real.sqrt (Work.Spaces.HkSq α k h) := by
  -- the angular marginal `H` and its square root `A`
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k h s θ
  have hAnn : ∀ s, 0 ≤ A s := fun s => Real.sqrt_nonneg _
  -- integrability of `H = A²` on `[0,∞)` and hence on `(z,∞)`
  have hH_int_Iz : IntegrableOn H Work.Spaces.Iz := by
    simpa only [hH] using hmem.2
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := by
    intro x hx
    simp only [Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith
  have hsub0 : Set.Ioi (0 : ℝ) ⊆ Work.Spaces.Iz := fun x hx => by
    simp only [Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    exact le_of_lt hx
  have hzle : ∀ s ∈ Set.Ioi z, (0 : ℝ) ≤ s := fun s hs => by
    simp only [Set.mem_Ioi] at hs
    linarith
  have hH_int : IntegrableOn H (Set.Ioi z) := hH_int_Iz.mono_set hsub
  have hH_int0 : IntegrableOn H (Set.Ioi 0) := hH_int_Iz.mono_set hsub0
  have hH_aesm : AEStronglyMeasurable H (volume.restrict (Set.Ioi z)) :=
    hH_int.aestronglyMeasurable
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi z)) := by
    rw [hA]
    exact (hH_aesm.aemeasurable.sqrt).aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi z) := by
    refine hH_int.congr ?_
    filter_upwards with s
    rw [hA]
    exact (Real.sq_sqrt (hHnn s)).symm
  have hA_memLp : MemLp A 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hA_aesm).mpr hA2_int
  -- the radial weight `Wlam` is square-integrable
  have hWlam_aesm : AEStronglyMeasurable Wlam (volume.restrict (Set.Ioi z)) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi z))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_)
      measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  have hWlam_sq_int : IntegrableOn (fun s => Wlam s ^ 2) (Set.Ioi z) :=
    Work.Elliptic.psi_sq_integrable_aux.mono_set (fun x hx => by
      simp only [Set.mem_Ioi] at hx ⊢
      linarith)
  have hWlam_memLp : MemLp Wlam 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hWlam_aesm).mpr hWlam_sq_int
  -- `∫_{(z,∞)} A² ≤ HkSq α k h`
  have hIz_eq : ∫ s in Work.Spaces.Iz, H s = Work.Spaces.HkSq α k h := by
    rw [hH]
    rfl
  have hA2sq_le : ∫ s in Set.Ioi z, A s ^ 2 ≤ Work.Spaces.HkSq α k h := by
    have h1 : ∫ s in Set.Ioi z, A s ^ 2 = ∫ s in Set.Ioi z, H s :=
      setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [hA]
        exact Real.sq_sqrt (hHnn s)
    have h2 : ∫ s in Set.Ioi z, H s ≤ ∫ s in Set.Ioi 0, H s :=
      setIntegral_Ioi_le_Ioi_zero hz hH_int0 hHnn
    have h3 : ∫ s in Set.Ioi 0, H s = ∫ s in Work.Spaces.Iz, H s :=
      MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici' (MeasureTheory.measure_singleton 0))
    calc ∫ s in Set.Ioi z, A s ^ 2 = ∫ s in Set.Ioi z, H s := h1
      _ ≤ ∫ s in Set.Ioi 0, H s := h2
      _ = ∫ s in Work.Spaces.Iz, H s := h3
      _ = Work.Spaces.HkSq α k h := hIz_eq
  -- Cauchy–Schwarz in the radial variable
  have hCS : ∫ s in Set.Ioi z, Wlam s * A s
      ≤ Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α k h) := by
    have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
      (u := Wlam) (v := A) (s := Set.Ioi z) hWlam_memLp hA_memLp
    have hnn : 0 ≤ ∫ s in Set.Ioi z, Wlam s * A s := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      show ∀ᵐ s ∂(volume.restrict (Set.Ioi z)), (0 : ℝ) ≤ Wlam s * A s
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun s hs => mul_nonneg (Wlam_nonneg (hzle s hs)) (hAnn s)
    rw [abs_of_nonneg hnn] at hcs
    refine le_trans hcs (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · refine Real.sqrt_le_sqrt ?_
      show ∫ s in Set.Ioi z, Wlam s ^ 2 ≤ W2
      exact setIntegral_Ioi_le_Ioi_zero hz Work.Elliptic.psi_sq_integrable_aux
        (fun s => sq_nonneg _)
    · exact Real.sqrt_le_sqrt hA2sq_le
  -- AM–GM, giving integrability of the majorant
  have hAMGM : ∀ s ∈ Set.Ioi z, Wlam s * A s ≤ Wlam s ^ 2 + A s ^ 2 := by
    intro s _
    nlinarith [sq_nonneg (Wlam s - A s)]
  have hsum_int : IntegrableOn (fun s => Wlam s ^ 2 + A s ^ 2) (Set.Ioi z) :=
    hWlam_sq_int.add hA2_int
  have hdom_int : IntegrableOn (fun s => BK * (Wlam s * A s)) (Set.Ioi z) := by
    refine Integrable.mono' (hsum_int.const_mul BK) ?_ ?_
    · exact (hWlam_aesm.mul hA_aesm).const_mul BK
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hnn : 0 ≤ BK * (Wlam s * A s) :=
        mul_nonneg BK_nonneg (mul_nonneg (Wlam_nonneg (hzle s hs)) (hAnn s))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hAMGM s hs) BK_nonneg
  have h2 : ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi z, BK * (Wlam s * A s) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg _) hdom_int ?_
    show ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      |Work.Construction.L12dens h s| ≤ BK * (Wlam s * A s)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hb := hbd s hs
    have hbA : |Work.Construction.L12dens h s| ≤ Wlam s * (BK * A s) := by
      simpa only [hA, hH] using hb
    calc |Work.Construction.L12dens h s| ≤ Wlam s * (BK * A s) := hbA
      _ = BK * (Wlam s * A s) := by ring
  have h3 : ∫ s in Set.Ioi z, BK * (Wlam s * A s)
      = BK * ∫ s in Set.Ioi z, Wlam s * A s :=
    MeasureTheory.integral_const_mul BK _
  have h4 : BK * ∫ s in Set.Ioi z, Wlam s * A s
      ≤ BK * (Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α k h)) :=
    mul_le_mul_of_nonneg_left hCS BK_nonneg
  calc ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi z, BK * (Wlam s * A s) := h2
    _ = BK * ∫ s in Set.Ioi z, Wlam s * A s := h3
    _ ≤ BK * (Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α k h)) := h4
    _ = BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α k h) := by ring

end Work.FTS.GalBasis.cc
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.radLeibniz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.GalFields.Norm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The one-variable operator `Zop u = z u'`: graded smoothness -/

/-- A `C^{n+1}` function on an open set has a `C^n` derivative there. -/
theorem contDiffOn_deriv_of_succ_V {u : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V) {n : ℕ}
    (hu : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) u V) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (deriv u) V := by
  have hfd : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fderiv ℝ u) V :=
    hu.fderiv_of_isOpen hV (by simp)
  have hev : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun z : ℝ => (fderiv ℝ u z) 1) V :=
    hfd.clm_apply contDiffOn_const
  refine hev.congr (fun z _ => ?_)
  rw [fderiv_apply_one_eq_deriv]

/-- Iterating `Zop u = z u'` raises the smoothness order: a `C^{b+k}` function has `C^k`
`Zop`-iterates of order `b`. -/
theorem contDiffOn_Zop_iter_nat {u : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V) :
    ∀ (b k : ℕ), ContDiffOn ℝ (((b + k : ℕ)) : WithTop ℕ∞) u V →
      ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Work.Spaces.Zop^[b] u) V := by
  intro b
  induction b with
  | zero =>
      intro k hu
      simpa using hu
  | succ b ih =>
      intro k hu
      have hu' : ContDiffOn ℝ (((b + (k + 1) : ℕ)) : WithTop ℕ∞) u V :=
        hu.of_le (Nat.cast_le.mpr (by omega : b + (k + 1) ≤ (b + 1) + k))
      have h1 := ih (k + 1) hu'
      have h2 : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (deriv (Work.Spaces.Zop^[b] u)) V :=
        contDiffOn_deriv_of_succ_V hV h1
      have h3 : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞)
          (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z) V :=
        (contDiff_id.contDiffOn).mul h2
      rw [Function.iterate_succ_apply']
      change ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞)
        (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z) V
      exact h3

/-- The `z`-slice of a `SmoothOpen` datum at an interior angle is `C^n` on `(0,∞)`, for
every finite order `n` (the finite-order form of `SmoothOpen.curry_z`, whose order is the
infinite `Stability.smoothOrder`). -/
theorem curry_z_nat_of_smoothOpen {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (n : ℕ) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun z => F z θ) (Set.Ioi (0 : ℝ)) := by
  have hφ : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun z : ℝ => (z, θ)) (Set.Ioi (0 : ℝ)) :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (0 : ℝ)) Work.FTS.EllipticEst.Q0 :=
    fun z hz => ⟨hz, hθ⟩
  refine ((hF.forall n).comp hφ hmap).congr (fun z _ => rfl)

/-- A `C^{b+1}` function has a differentiable `Zop`-iterate of order `b` on `V`. -/
theorem differentiableAt_Zop_iter_le {u : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V) {N b : ℕ}
    (hu : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) u V) (hb : b + 1 ≤ N) {z : ℝ} (hz : z ∈ V) :
    DifferentiableAt ℝ (Work.Spaces.Zop^[b] u) z := by
  have h1 : ContDiffOn ℝ (((b + 1 : ℕ)) : WithTop ℕ∞) u V := hu.of_le (Nat.cast_le.mpr hb)
  have h2 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (Work.Spaces.Zop^[b] u) V :=
    contDiffOn_Zop_iter_nat hV b 1 h1
  exact (h2.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hz)

/-! ## The graded Leibniz rule for `Zop` -/

/-- The `a`-th term of the Leibniz sum, differentiated: the factor `z` of `Zop` turns the
two product-rule halves into the `(a+1)`-st and the `(j-a+1)`-st `Zop`-iterate. -/
theorem Zop_deriv_term (u v : ℝ → ℝ) (z : ℝ) (j a : ℕ)
    (ha : DifferentiableAt ℝ (Work.Spaces.Zop^[a] u) z)
    (hb : DifferentiableAt ℝ (Work.Spaces.Zop^[j - a] v) z) :
    z * deriv (fun z' => (j.choose a : ℝ)
        * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[j - a] v z')) z =
      (j.choose a : ℝ)
        * (Work.Spaces.Zop^[a + 1] u z * Work.Spaces.Zop^[j - a] v z
            + Work.Spaces.Zop^[a] u z * Work.Spaces.Zop^[j - a + 1] v z) := by
  have hfun2 : (fun z' => (j.choose a : ℝ)
        * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[j - a] v z'))
      = (fun y => (j.choose a : ℝ)
        * ((Work.Spaces.Zop^[a] u * Work.Spaces.Zop^[j - a] v) y)) := rfl
  rw [hfun2, deriv_const_mul (j.choose a : ℝ) (ha.mul hb), deriv_mul ha hb,
    Function.iterate_succ_apply' Work.Spaces.Zop a u,
    Function.iterate_succ_apply' Work.Spaces.Zop (j - a) v,
    show Work.Spaces.Zop (Work.Spaces.Zop^[a] u) z
      = z * deriv (Work.Spaces.Zop^[a] u) z from rfl,
    show Work.Spaces.Zop (Work.Spaces.Zop^[j - a] v) z
      = z * deriv (Work.Spaces.Zop^[j - a] v) z from rfl]
  ring

/-- **The graded iterated Leibniz rule for `Zop u = z u'`**: on an open set `V` where both
factors are only `C^{i+1}`, the `i`-th iterate of `Zop` on the product is the binomial
convolution of the iterates of the factors. -/
theorem Zop_iter_mul_aux (i : ℕ) :
    ∀ (u v : ℝ → ℝ) (V : Set ℝ), IsOpen V →
      ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) u V →
      ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) v V →
      Set.EqOn (Work.Spaces.Zop^[i] (u * v))
        (fun z => ∑ a ∈ Finset.range (i + 1),
          (i.choose a : ℝ) * (Work.Spaces.Zop^[a] u z * Work.Spaces.Zop^[i - a] v z)) V := by
  induction i with
  | zero =>
      intro u v V hV hu hv z hz
      simp [Function.iterate_zero_apply]
  | succ i ih =>
      intro u v V hV hu hv z hz
      dsimp only
      rw [Function.iterate_succ_apply']
      have hu' : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) u V :=
        hu.of_le (Nat.cast_le.mpr (by omega : i + 1 ≤ i + 2))
      have hv' : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) v V :=
        hv.of_le (Nat.cast_le.mpr (by omega : i + 1 ≤ i + 2))
      have hih := ih u v V hV hu' hv'
      have hFa : ∀ a ≤ i, DifferentiableAt ℝ (Work.Spaces.Zop^[a] u) z := fun a ha =>
        differentiableAt_Zop_iter_le hV hu' (by omega : a + 1 ≤ i + 1) hz
      have hGb : ∀ b ≤ i, DifferentiableAt ℝ (Work.Spaces.Zop^[b] v) z := fun b hb =>
        differentiableAt_Zop_iter_le hV hv' (by omega : b + 1 ≤ i + 1) hz
      have hmem : ∀ a ∈ Finset.range (i + 1), DifferentiableAt ℝ
          (fun z' => (i.choose a : ℝ)
            * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[i - a] v z')) z := by
        intro a ha
        exact (((hFa a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))).mul
          (hGb (i - a) (Nat.sub_le i a))).const_mul _
      have hfun : (fun z' => ∑ a ∈ Finset.range (i + 1),
            (i.choose a : ℝ) * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[i - a] v z'))
          = ∑ a ∈ Finset.range (i + 1),
            (fun z' => (i.choose a : ℝ)
              * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[i - a] v z')) := by
        funext z'
        rw [Finset.sum_apply]
      have hderiv : deriv (Work.Spaces.Zop^[i] (u * v)) z
          = deriv (fun z' => ∑ a ∈ Finset.range (i + 1),
              (i.choose a : ℝ)
                * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[i - a] v z')) z :=
        (hih.deriv hV) hz
      have hkey : Work.Spaces.Zop (Work.Spaces.Zop^[i] (u * v)) z
          = ∑ a ∈ Finset.range (i + 1), z
              * deriv (fun z' => (i.choose a : ℝ)
                * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[i - a] v z')) z := by
        show z * deriv (Work.Spaces.Zop^[i] (u * v)) z
          = ∑ a ∈ Finset.range (i + 1), z
              * deriv (fun z' => (i.choose a : ℝ)
                * (Work.Spaces.Zop^[a] u z' * Work.Spaces.Zop^[i - a] v z')) z
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [hkey]
      trans ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
          (Work.Spaces.Zop^[a + 1] u z * Work.Spaces.Zop^[i - a] v z
            + Work.Spaces.Zop^[a] u z * Work.Spaces.Zop^[i - a + 1] v z)
      · exact Finset.sum_congr rfl (fun a ha => Zop_deriv_term u v z i a
          (hFa a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
          (hGb (i - a) (Nat.sub_le i a)))
      · exact Work.Spaces.leibniz_step i (fun b => Work.Spaces.Zop^[b] u z)
          (fun b => Work.Spaces.Zop^[b] v z)

/-- The graded iterated Leibniz rule for `Zop`, pointwise form. -/
theorem Zop_iter_mul_contDiffOn {i : ℕ} {u v : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V)
    (hu : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) u V)
    (hv : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) v V) :
    ∀ z ∈ V, Work.Spaces.Zop^[i] (u * v) z
      = ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)
          * (Work.Spaces.Zop^[a] u z * Work.Spaces.Zop^[i - a] v z) :=
  Zop_iter_mul_aux i u v V hV hu hv

/-! ## Two unconditional identities -/

/-- `deriv` is scalar homogeneous **unconditionally** (Mathlib's `deriv_const_mul` needs
differentiability): if `f` is not differentiable at `x` then neither is `c · f` for `c ≠ 0`,
so both sides are `0`. -/
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

/-- `D_θ^i` commutes with multiplication by a factor depending only on `z`.  No smoothness
is needed: the only ingredient is the unconditional scalar linearity of `deriv`. -/
theorem DthIter_zmul_rad (i : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
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

/-- The `Zop`-iterates of a one-variable function are the `DzdIter`s of `Work.Elliptic`. -/
theorem Zop_iter_eq_DzdIter (b : ℕ) (r : ℝ → ℝ) :
    Work.Spaces.Zop^[b] r = Work.Elliptic.DzdIter b r := by
  induction b with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Work.Elliptic.DzdIter_succ]
      rfl

/-! ## The two Leibniz rules for a radial factor -/


end Work.FTS.GalFields.Norm
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Tail.BoxCalc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Tail

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false














/-! ## Integrability of continuous functions on the box -/



/-! ## Additivity and scalar rules -/












end Work.FTS.GalFields.Tail
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Tail.SlotAdjoints =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Tail

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `SmoothOpen` closure (local copies of the elementary facts) -/

theorem SmoothOpen.add {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ + g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.add hg

theorem SmoothOpen.neg {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) := by
  have h : Function.uncurry (fun z θ => -f z θ)
      = fun p : ℝ × ℝ => -Function.uncurry f p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.neg

theorem SmoothOpen.mul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.mul hg

theorem SmoothOpen.const (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ _ : ℝ => c) := by
  have h : Function.uncurry (fun _ _ : ℝ => c) = fun _ : ℝ × ℝ => c := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact contDiffOn_const

theorem SmoothOpen.const_mul {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (c : ℝ) : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  have h : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact contDiffOn_const.mul hf

/-- `θ ↦ 2 cos(2θ)`, as a function on the quadrant, is `C^∞` on the open quadrant. -/
theorem SmoothOpen.cos2 :
    Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => 2 * Real.cos (2 * θ)) := by
  have h : Function.uncurry (fun _ θ : ℝ => 2 * Real.cos (2 * θ))
      = fun p : ℝ × ℝ => 2 * Real.cos (2 * p.2) := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact (show ContDiff ℝ ⊤ (fun p : ℝ × ℝ => 2 * Real.cos (2 * p.2)) from by
    fun_prop).contDiffOn.of_le le_top

/-! ## The adjoints -/

/-- The formal adjoint of `D_z = z ∂_z`: `adjZ G = -(G + z ∂_z G)`.  It satisfies
`∫_z (D_z u) · v = ∫_z u · (adjZ v)` whenever the boundary term `z u v` vanishes. -/
def adjZ (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => -(G z θ + Work.Spaces.Dz G z θ)

/-- The formal adjoint of `D_θ = sin(2θ) ∂_θ`:
`adjTh G = -(sin(2θ)·∂_θ G + 2 cos(2θ)·G)`.  It satisfies
`∫_θ (D_θ u) · v = ∫_θ u · (adjTh v)` whenever the boundary term `sin(2θ) u v` vanishes. -/
def adjTh (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Spaces.Dth G z θ + 2 * Real.cos (2 * θ) * G z θ)

/-- The `n`-fold iterate of `adjZ`. -/
def adjZIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, G => G
  | n + 1, G => adjZ (adjZIter n G)

/-- The `n`-fold iterate of `adjTh`. -/
def adjThIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, G => G
  | n + 1, G => adjTh (adjThIter n G)

@[simp] theorem adjZIter_zero (G : ℝ → ℝ → ℝ) : adjZIter 0 G = G := rfl
@[simp] theorem adjZIter_succ (n : ℕ) (G : ℝ → ℝ → ℝ) :
    adjZIter (n + 1) G = adjZ (adjZIter n G) := rfl
@[simp] theorem adjThIter_zero (G : ℝ → ℝ → ℝ) : adjThIter 0 G = G := rfl
@[simp] theorem adjThIter_succ (n : ℕ) (G : ℝ → ℝ → ℝ) :
    adjThIter (n + 1) G = adjTh (adjThIter n G) := rfl





/-! ## Smoothness of the adjoint iterates on the open quadrant -/





/-! ## The adjoints preserve vanishing off a box -/






end Work.FTS.GalFields.Tail
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Tail.boxInt_mixed_le_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Tail

set_option autoImplicit false

/-! ## The pointwise lower bounds for the weights on a box -/






/-! ## The algebraic consequence: a square dominated by its weighted version -/



/-! ## The pointwise bound on the box -/


/-! ## The box integral -/


end Work.FTS.GalFields.Tail
end
end
-- ===== merged: Submission.Work.FTS.Galerkin.Projection =====
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

set_option autoImplicit false

/-! ## The projected equation is a finite-dimensional ODE -/







/-! ## The exact energy identity -/






end Work.FTS.Galerkin
end
end
-- ===== merged: Submission.Work.FTS.H2.ModalSol.Prelim.support =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSol

/-- **Continuity of the mode-`m` radial Green's function** for a square-integrable source. -/
theorem radGreen_continuousOn (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0)) :
    ContinuousOn (Work.FTS.PhiStar.Radial.radGreen α m c) (Set.Ioi 0) := by
  sorry

/-- An `L²` function of the first variable times a continuous function on a compact box is
integrable on the box. -/
theorem integrableOn_mul_of_sq_integrable {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun z => c z ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    {a b c₀ d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc0 : 0 < c₀) (hcd : c₀ ≤ d)
    {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g (Set.Icc a b ×ˢ Set.Icc c₀ d)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => c p.1 * g p)
      (Set.Icc a b ×ˢ Set.Icc c₀ d) := by
  sorry


end Work.FTS.H2.ModalSol
end
end
-- ===== merged: Submission.Work.FTS.H2.PhiStarE5.Locality =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.PhiStarE5

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
noncomputable section

/-- **Locality of `bslOp`**: two functions agreeing on a neighbourhood of `(z,θ)` have the same
`bslOp`-value at `(z,θ)`. -/
theorem bslOp_congr_of_eventuallyEq (α : ℝ) {Ψ₁ Ψ₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ q in 𝓝 (z, θ), Ψ₁ q.1 q.2 = Ψ₂ q.1 q.2) :
    Work.Elliptic.bslOp α Ψ₁ z θ = Work.Elliptic.bslOp α Ψ₂ z θ := by
  obtain ⟨V, hVsub, hVopen, hzθV⟩ := mem_nhds_iff.mp h
  have hVz : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (hVopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hzθV
  have hVt : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hzθV
  have hevZ : (fun z' => Ψ₁ z' θ) =ᶠ[𝓝 z] (fun z' => Ψ₂ z' θ) :=
    hVz.mono (fun z' hz' => hVsub hz')
  have hevT : (fun θ' => Ψ₁ z θ') =ᶠ[𝓝 θ] (fun θ' => Ψ₂ z θ') :=
    hVt.mono (fun θ' hθ' => hVsub hθ')
  -- first `z`-derivative
  have hevZ1 : (fun z' => Work.Spaces.pz Ψ₁ z' θ) =ᶠ[𝓝 z]
      (fun z' => Work.Spaces.pz Ψ₂ z' θ) := by
    filter_upwards [hVz] with z' hz'
    have hmem : ∀ᶠ z'' in 𝓝 z', (z'', θ) ∈ V :=
      (hVopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hz'
    have hev : (fun z'' => Ψ₁ z'' θ) =ᶠ[𝓝 z'] (fun z'' => Ψ₂ z'' θ) :=
      hmem.mono (fun z'' hz'' => hVsub hz'')
    rw [show Work.Spaces.pz Ψ₁ z' θ = deriv (fun z'' => Ψ₁ z'' θ) z' from rfl,
      show Work.Spaces.pz Ψ₂ z' θ = deriv (fun z'' => Ψ₂ z'' θ) z' from rfl]
    exact Filter.EventuallyEq.deriv_eq hev
  -- second `z`-derivative
  have hevZ2 : (fun z' => Work.Spaces.pzIter 2 Ψ₁ z' θ) =ᶠ[𝓝 z]
      (fun z' => Work.Spaces.pzIter 2 Ψ₂ z' θ) := by
    filter_upwards [hVz] with z' hz'
    have hmem : ∀ᶠ z'' in 𝓝 z', (z'', θ) ∈ V :=
      (hVopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hz'
    have hev : (fun z'' => Work.Spaces.pz Ψ₁ z'' θ) =ᶠ[𝓝 z']
        (fun z'' => Work.Spaces.pz Ψ₂ z'' θ) := by
      filter_upwards [hmem] with z'' hz''
      have hmem2 : ∀ᶠ z₃ in 𝓝 z'', (z₃, θ) ∈ V :=
        (hVopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hz''
      have hev2 : (fun z₃ => Ψ₁ z₃ θ) =ᶠ[𝓝 z''] (fun z₃ => Ψ₂ z₃ θ) :=
        hmem2.mono (fun z₃ hz₃ => hVsub hz₃)
      rw [show Work.Spaces.pz Ψ₁ z'' θ = deriv (fun z₃ => Ψ₁ z₃ θ) z'' from rfl,
        show Work.Spaces.pz Ψ₂ z'' θ = deriv (fun z₃ => Ψ₂ z₃ θ) z'' from rfl]
      exact Filter.EventuallyEq.deriv_eq hev2
    rw [show Work.Spaces.pzIter 2 Ψ₁ z' θ = deriv (fun z'' => Work.Spaces.pz Ψ₁ z'' θ) z'
        from rfl,
      show Work.Spaces.pzIter 2 Ψ₂ z' θ = deriv (fun z'' => Work.Spaces.pz Ψ₂ z'' θ) z'
        from rfl]
    exact Filter.EventuallyEq.deriv_eq hev
  -- first `θ`-derivative
  have hevT1 : (fun θ' => Work.Spaces.pth Ψ₁ z θ') =ᶠ[𝓝 θ]
      (fun θ' => Work.Spaces.pth Ψ₂ z θ') := by
    filter_upwards [hVt] with θ' hθ'
    have hmem : ∀ᶠ θ'' in 𝓝 θ', (z, θ'') ∈ V :=
      (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hθ'
    have hev : (fun θ'' => Ψ₁ z θ'') =ᶠ[𝓝 θ'] (fun θ'' => Ψ₂ z θ'') :=
      hmem.mono (fun θ'' hθ'' => hVsub hθ'')
    rw [show Work.Spaces.pth Ψ₁ z θ' = deriv (fun θ'' => Ψ₁ z θ'') θ' from rfl,
      show Work.Spaces.pth Ψ₂ z θ' = deriv (fun θ'' => Ψ₂ z θ'') θ' from rfl]
    exact Filter.EventuallyEq.deriv_eq hev
  -- second `θ`-derivative
  have hevT2 : (fun θ' => Work.Spaces.pthIter 2 Ψ₁ z θ') =ᶠ[𝓝 θ]
      (fun θ' => Work.Spaces.pthIter 2 Ψ₂ z θ') := by
    filter_upwards [hVt] with θ' hθ'
    have hmem : ∀ᶠ θ'' in 𝓝 θ', (z, θ'') ∈ V :=
      (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hθ'
    have hev : (fun θ'' => Work.Spaces.pth Ψ₁ z θ'') =ᶠ[𝓝 θ']
        (fun θ'' => Work.Spaces.pth Ψ₂ z θ'') := by
      filter_upwards [hmem] with θ'' hθ''
      have hmem2 : ∀ᶠ θ₃ in 𝓝 θ'', (z, θ₃) ∈ V :=
        (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hθ''
      have hev2 : (fun θ₃ => Ψ₁ z θ₃) =ᶠ[𝓝 θ''] (fun θ₃ => Ψ₂ z θ₃) :=
        hmem2.mono (fun θ₃ hθ₃ => hVsub hθ₃)
      rw [show Work.Spaces.pth Ψ₁ z θ'' = deriv (fun θ₃ => Ψ₁ z θ₃) θ'' from rfl,
        show Work.Spaces.pth Ψ₂ z θ'' = deriv (fun θ₃ => Ψ₂ z θ₃) θ'' from rfl]
      exact Filter.EventuallyEq.deriv_eq hev2
    rw [show Work.Spaces.pthIter 2 Ψ₁ z θ' = deriv (fun θ'' => Work.Spaces.pth Ψ₁ z θ'') θ'
        from rfl,
      show Work.Spaces.pthIter 2 Ψ₂ z θ' = deriv (fun θ'' => Work.Spaces.pth Ψ₂ z θ'') θ'
        from rfl]
    exact Filter.EventuallyEq.deriv_eq hev
  -- the `∂_θ(tan θ · Ψ)` term
  have hevTtan : (fun θ' => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ₁ z θ) z θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ₂ z θ) z θ') := by
    filter_upwards [hVt] with θ' hθ'
    have hmem : ∀ᶠ θ'' in 𝓝 θ', (z, θ'') ∈ V :=
      (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hθ'
    have hev : (fun θ'' => Real.tan θ'' * Ψ₁ z θ'') =ᶠ[𝓝 θ']
        (fun θ'' => Real.tan θ'' * Ψ₂ z θ'') :=
      hmem.mono (fun θ'' hθ'' => by
        have h1 : Ψ₁ z θ'' = Ψ₂ z θ'' := hVsub hθ''
        show Real.tan θ'' * Ψ₁ z θ'' = Real.tan θ'' * Ψ₂ z θ''
        rw [h1])
    rw [show Work.Spaces.pth (fun z θ => Real.tan θ * Ψ₁ z θ) z θ'
          = deriv (fun θ'' => Real.tan θ'' * Ψ₁ z θ'') θ' from rfl,
      show Work.Spaces.pth (fun z θ => Real.tan θ * Ψ₂ z θ) z θ'
          = deriv (fun θ'' => Real.tan θ'' * Ψ₂ z θ'') θ' from rfl]
    exact Filter.EventuallyEq.deriv_eq hev
  have hpsi : Ψ₁ z θ = Ψ₂ z θ :=
    Filter.EventuallyEq.eq_of_nhds (f := fun q : ℝ × ℝ => Ψ₁ q.1 q.2)
      (g := fun q : ℝ × ℝ => Ψ₂ q.1 q.2) (x := (z, θ)) h
  have hpz1 : Work.Spaces.pz Ψ₁ z θ = Work.Spaces.pz Ψ₂ z θ := hevZ1.eq_of_nhds
  have hpz2 : Work.Spaces.pzIter 2 Ψ₁ z θ = Work.Spaces.pzIter 2 Ψ₂ z θ := hevZ2.eq_of_nhds
  have hpth1 : Work.Spaces.pth Ψ₁ z θ = Work.Spaces.pth Ψ₂ z θ := hevT1.eq_of_nhds
  have hpth2 : Work.Spaces.pthIter 2 Ψ₁ z θ = Work.Spaces.pthIter 2 Ψ₂ z θ := hevT2.eq_of_nhds
  have hpthtan : Work.Spaces.pth (fun z θ => Real.tan θ * Ψ₁ z θ) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * Ψ₂ z θ) z θ := hevTtan.eq_of_nhds
  rw [Work.Elliptic.bslOp_apply, Work.Elliptic.bslOp_apply]
  simp only [Work.Elliptic.Lzero, hpth2, hpthtan, hpz2, hpz1, hpsi]

end

end Work.FTS.H2.PhiStarE5
end
-- ===== merged: Submission.Work.FTS.LocData.HkSq_add_le =====
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

/-- **Subadditivity of `HkSq`** on the `SmoothQuad` data of the localisation chapter: if `a` and
`b` are `C^∞` on the open quadrant and both lie in `ℋ^k` *honestly* (`HkMem`), then so does their
sum, with the `2 + 2` bound

`HkSq α k (a+b) ≤ 2·HkSq α k a + 2·HkSq α k b`.

The proof is two monotonicity steps of the iterated integral: the pointwise inequality of the
integrable functions (`HkIntegrand_add_le`) integrated first over `θ ∈ Iθ`, then over `z ∈ Iz`.
The integrability of the dominating function `2·HkIntegrand a + 2·HkIntegrand b` is exactly the
`HkMem` certificates of `a` and `b`; no measurability of `HkIntegrand (a+b)` is needed
(`MeasureTheory.integral_mono_of_nonneg` takes the *larger* function integrable). -/
theorem HkSq_add_le (α : ℝ) (k : ℕ) {a b : ℝ → ℝ → ℝ} (hsa : SmoothQuad a)
    (hsb : SmoothQuad b) (ha : Work.Spaces.HkMem α k a) (hb : Work.Spaces.HkMem α k b) :
    Work.Spaces.HkSq α k (fun z θ => a z θ + b z θ)
      ≤ 2 * Work.Spaces.HkSq α k a + 2 * Work.Spaces.HkSq α k b := by
  -- The inner `θ`-integral, on the domain `Iz`.
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => a z θ + b z θ) z θ)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k a z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k b z θ) := by
    intro z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α k (fun z θ => a z θ + b z θ) z θ)
      (g := fun θ => 2 * Work.Spaces.HkIntegrand α k a z θ
        + 2 * Work.Spaces.HkIntegrand α k b z θ)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ)
      (((ha.1 z hz).const_mul 2).add ((hb.1 z hz).const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        fun θ hθ => HkIntegrand_add_le α k hsa hsb hz hθ)
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_add ((ha.1 z hz).const_mul 2)
          ((hb.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => a z θ + b z θ) z θ)
    (g := fun z => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k a z θ)
      + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k b z θ))
    (Eventually.of_forall fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k _ z θ)
    ((ha.2.const_mul 2).add (hb.2.const_mul 2))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  refine houter.trans_eq ?_
  rw [MeasureTheory.integral_add (ha.2.const_mul 2) (hb.2.const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.HlocFactor =====
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

/-! ## The factorisation of `hLoc` -/

/-- `hLoc α = φ(z)·Γ(θ)` written with the angular factor first, as required by
`DzIter_mul_theta_factor` / `DthIter_decomp`. -/
theorem hLoc_eq_Gam_mul_bumpZ (α : ℝ) :
    hLoc α = fun z θ => Work.Spaces.Gam α θ * bumpZ z := by
  funext z θ
  rw [hLoc_apply]
  ring

/-- **The `D_z`-derivatives of the bump separate**: `D_z^i (φ·Γ) = Γ · (T1^[i] φ)`. -/
theorem DzIter_hLoc (α : ℝ) (i : ℕ) :
    Work.Spaces.DzIter i (hLoc α)
      = fun z θ => Work.Spaces.Gam α θ * (T1^[i]) bumpZ z := by
  rw [hLoc_eq_Gam_mul_bumpZ α,
    DzIter_mul_theta_factor i (fun t => Work.Spaces.Gam α t) (fun z _ => bumpZ z)]
  funext z θ
  rw [DzIter_bumpZ_eq i θ z]

/-- **The `D_θ`-derivatives of the bump separate**: `D_θ^i (φ·Γ) = (dthU^[i] Γ) · φ`. -/
theorem DthIter_hLoc (α : ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (hLoc α)
      = fun z θ => Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ * bumpZ z := by
  rw [hLoc_eq_Gam_mul_bumpZ α]
  funext z θ
  exact Work.Spaces.DthIter_decomp i (fun t => Work.Spaces.Gam α t) bumpZ z θ

/-- **The mixed derivatives of the bump separate**: `D_z^j D_θ^i (φ·Γ) = (D_θ^i Γ)(0,·) · (T1^[j] φ)`.
(The angular factor is written as the two-variable iterate evaluated at `z = 0`, which is where
the angular estimate `DthIter_Gam_abs_le` is stated.) -/
theorem mixed_hLoc (α : ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (hLoc α)
      = fun z θ => Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
          * (T1^[j]) bumpZ z := by
  rw [Work.Spaces.mixed, DthIter_hLoc α i,
    DzIter_mul_theta_factor j (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t))
      (fun z _ => bumpZ z)]
  funext z θ
  rw [DzIter_bumpZ_eq j θ z, ← DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]

/-! ## Vanishing off the support -/

/-- Every `D_z`-iterate of the bump vanishes off the closed interval `[3/4, 7/4]`. -/
theorem T1_iterate_bumpZ_eq_zero {z : ℝ} (hz : z ∉ Set.Icc (3 / 4 : ℝ) (7 / 4)) (c : ℕ) :
    (T1^[c]) bumpZ z = 0 :=
  (T1_iterate_contDiff BumpZ_contDiff bumpZ_eq_zero_of_notMem_Icc c).2 z hz


/-- **`HkIntegrand α 4 (hLoc α)` vanishes off the support of the bump.**  Every summand of the
integrand is a square of a product in which one factor is a `D_z`-iterate of `bumpZ`, and all of
those vanish for `z ∉ [3/4, 7/4]`. -/
theorem HkIntegrand_hLoc_eq_zero_off {α z : ℝ} (hz : z ∉ Set.Icc (3 / 4 : ℝ) (7 / 4))
    (θ : ℝ) : Work.Spaces.HkIntegrand α 4 (hLoc α) z θ = 0 := by
  have h1 : ∀ i : ℕ, Work.Spaces.DzIter i (hLoc α) z θ = 0 := by
    intro i
    rw [congrFun (congrFun (DzIter_hLoc α i) z) θ, T1_iterate_bumpZ_eq_zero hz i, mul_zero]
  have h2 : ∀ j i : ℕ, Work.Spaces.mixed j i (hLoc α) z θ = 0 := by
    intro j i
    rw [congrFun (congrFun (mixed_hLoc α j i) z) θ, T1_iterate_bumpZ_eq_zero hz j, mul_zero]
  rw [Work.Spaces.HkIntegrand]
  have hs1 : (∑ i ∈ Finset.range 5,
      (Work.Spaces.DzIter i (hLoc α) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h1 i]
    ring
  have hs2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 then
        (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc, h2 j i]
      ring
    · rw [if_neg hc]
  rw [hs1, hs2, add_zero]

/-! ## The weight bound on the support -/

/-- **The weight is bounded by the far-field factor on the support of the bump.**  For
`z ∈ [3/4, 7/4]`,

  `w(z)² ≤ (1771561/1296)/(1+z)²`,

i.e. `(1+z)^6/z^4 ≤ (11/4)^6/(3/4)^4 = 1771561/1296`.  This is what converts the pointwise bound
`HkIntegrand ≤ K·w²·angMaj` of the bump (which holds on the whole quadrant, since `φ` is bounded)
into the far-field-decaying bound `≤ K²·angMaj/(1+z)²` of the localised data. -/
theorem w_sq_le_on_support {z : ℝ} (hz : z ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)) :
    (Work.Spaces.w z) ^ 2 ≤ (1771561 / 1296 : ℝ) / (1 + z) ^ 2 := by
  have hz0 : 0 < z := by linarith [hz.1]
  have hzne : z ≠ 0 := ne_of_gt hz0
  have hz4 : 0 < z ^ 4 := by positivity
  have hpos : 0 < (1 + z) ^ 2 := by positivity
  rw [le_div_iff₀ hpos, Work.Spaces.w]
  have hsplit : ((1 + z) ^ 2 / z ^ 2) ^ 2 * (1 + z) ^ 2 = (1 + z) ^ 6 / z ^ 4 := by
    field_simp
  rw [hsplit, div_le_iff₀ hz4]
  have h1 : (1 + z) ^ 6 ≤ (11 / 4 : ℝ) ^ 6 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith [hz.2]
  have h2 : ((3 : ℝ) / 4) ^ 4 ≤ z ^ 4 := pow_le_pow_left₀ (by norm_num) hz.1 4
  calc (1 + z) ^ 6 ≤ (11 / 4 : ℝ) ^ 6 := h1
    _ = (1771561 / 1296 : ℝ) * ((3 : ℝ) / 4) ^ 4 := by norm_num
    _ ≤ (1771561 / 1296 : ℝ) * z ^ 4 :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.L12_locG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

open MeasureTheory Set Filter
open scoped Real Topology

/-! ### Wrappers of the fundamental-model linearity in `Construction.L12` -/

/-- `L₁₂` is homogeneous in a constant, in the vocabulary of `Work.Construction`. -/
theorem L12_const_mul_C (c : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Construction.L12 (fun z θ => c * f z θ) z = c * Work.Construction.L12 f z :=
  Work.FM.L12_const_mul

/-- `L₁₂` is additive, in the vocabulary of `Work.Construction`. -/
theorem L12_add_C {f g : ℝ → ℝ → ℝ} {z : ℝ}
    (hf : ∀ s, MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ)
    (hg : ∀ s, MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * g s θ / s) Work.Spaces.Iθ)
    (hF : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi z))
    (hG : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi z)) :
    Work.Construction.L12 (fun z θ => f z θ + g z θ) z
      = Work.Construction.L12 f z + Work.Construction.L12 g z :=
  Work.FM.L12_add hf hg hF hG

/-! ### The `L₁₂`-value of the localised perturbation `locG`

`locG α L β h` is the difference between the localised profile `locData = F_*·χ(·/L) + βh`
and the profile `F_*` itself; pointwise (`locG_eq_zfar`)

  `locG α L β h = - zfar L F_* + β h`,

so the value of the *linear* functional `L₁₂(·)(0)` splits — provided the two summands have
integrable angular slices (they do: both are constant multiples of the slice of `F_*`, resp. of
`Γ·K`) and integrable densities on `(0,∞)`.  The latter two are the hypotheses `hzfar`, `hbump`
of the lemma below; they are discharged for `h = hLoc α` in `L12_locG`. -/
theorem L12_locG_of_integrable (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    (hzfar : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.Stability.zfar L (Work.Construction.Fstar α)))
      (Set.Ioi (0 : ℝ)))
    (hbump : MeasureTheory.IntegrableOn (fun s : ℝ => bumpZ s / s) (Set.Ioi (0 : ℝ))) :
    Work.Construction.L12 (locG α L β (hLoc α)) 0
      = -(Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0)
        + β * Work.Construction.L12 (hLoc α) 0 := by
  -- the pointwise decomposition of `locG` into its two summands
  have hfun : locG α L β (hLoc α)
      = fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)
          + β * hLoc α z θ := by
    funext z θ
    exact locG_eq_zfar α L β (hLoc α) z θ
  -- the angular slice of the negated far part: a constant multiple of the slice of `F_*`
  have hslice_neg : ∀ s : ℝ, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (-(Work.Stability.zfar L (Work.Construction.Fstar α) s θ)) / s)
      Work.Spaces.Iθ := by
    intro s
    have hc : MeasureTheory.IntegrableOn
        (fun θ => (-(1 - Work.Stability.chi (s / L))) *
          (Work.Spaces.K θ * Work.Construction.Fstar α s θ / s)) Work.Spaces.Iθ :=
      (Work.Stability.integrableOn_slice_Fstar α hα s).const_mul _
    refine hc.congr_fun (fun θ _ => ?_) measurableSet_Icc
    rw [Work.Stability.zfar_apply]
    ring
  -- the angular slice of `β h`: a constant multiple of `Γ·K`
  have hslice_beta : ∀ s : ℝ, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (β * hLoc α s θ) / s) Work.Spaces.Iθ := by
    intro s
    have hc : MeasureTheory.IntegrableOn
        (fun θ => (β * bumpZ s / s) * (Work.Spaces.Gam α θ * Work.Spaces.K θ)) Work.Spaces.Iθ :=
      (Work.Spaces.CAux.integrableOn_GamK α hα).const_mul _
    refine hc.congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [hLoc_apply]
    ring
  -- the density of the negated far part is the negated density
  have hdens_neg_pt : ∀ s : ℝ, Work.FM.L12dens Work.Spaces.K
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)) s
      = -(Work.FM.L12dens Work.Spaces.K
        (Work.Stability.zfar L (Work.Construction.Fstar α)) s) := by
    intro s
    simp only [Work.FM.L12dens]
    rw [show (∫ θ in Set.Icc 0 (π / 2),
          Work.Spaces.K θ * (-(Work.Stability.zfar L (Work.Construction.Fstar α) s θ)) / s)
        = ∫ θ in Set.Icc 0 (π / 2), -(Work.Spaces.K θ *
            Work.Stability.zfar L (Work.Construction.Fstar α) s θ / s) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
    rw [MeasureTheory.integral_neg]
  have hdens_neg : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)))
      (Set.Ioi (0 : ℝ)) := by
    refine hzfar.neg.congr_fun (fun s _ => ?_) measurableSet_Ioi
    exact (hdens_neg_pt s).symm
  -- the density of `β h` is `(β c) · (bumpZ s / s)`
  have hdens_beta_pt : ∀ s : ℝ, Work.FM.L12dens Work.Spaces.K (fun z θ => β * hLoc α z θ) s
      = (β * Work.Spaces.c α) * (bumpZ s / s) := by
    intro s
    rw [L12dens_const_mul Work.Spaces.K β (hLoc α) s, L12dens_hLoc α s]
    ring
  have hdens_beta : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (fun z θ => β * hLoc α z θ)) (Set.Ioi (0 : ℝ)) := by
    have hc : MeasureTheory.IntegrableOn (fun s : ℝ => (β * Work.Spaces.c α) * (bumpZ s / s))
        (Set.Ioi (0 : ℝ)) := hbump.const_mul _
    refine hc.congr_fun (fun s _ => ?_) measurableSet_Ioi
    exact (hdens_beta_pt s).symm
  -- additivity of `L₁₂` on the two summands
  have hadd : Work.Construction.L12
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)
          + β * hLoc α z θ) 0
      = Work.Construction.L12
          (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)) 0
        + Work.Construction.L12 (fun z θ => β * hLoc α z θ) 0 :=
    L12_add_C (f := fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ))
      (g := fun z θ => β * hLoc α z θ) (z := 0)
      hslice_neg hslice_beta hdens_neg hdens_beta
  -- the two homogeneous pieces
  have hneg_eq : Work.Construction.L12
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)) 0
      = -(Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0) := by
    have hfun2 : (fun r => Work.FM.L12dens Work.Spaces.K
          (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)) r)
        = fun r => -(Work.FM.L12dens Work.Spaces.K
          (Work.Stability.zfar L (Work.Construction.Fstar α)) r) :=
      funext fun r => hdens_neg_pt r
    simp only [Work.Construction.L12, Work.FM.L12]
    rw [hfun2, MeasureTheory.integral_neg]
  have hbeta_eq : Work.Construction.L12 (fun z θ => β * hLoc α z θ) 0
      = β * Work.Construction.L12 (hLoc α) 0 :=
    L12_const_mul_C β (hLoc α) 0
  calc Work.Construction.L12 (locG α L β (hLoc α)) 0
      = Work.Construction.L12
          (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)
            + β * hLoc α z θ) 0 := by rw [hfun]
    _ = Work.Construction.L12
          (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)) 0
        + Work.Construction.L12 (fun z θ => β * hLoc α z θ) 0 := hadd
    _ = -(Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0)
        + β * Work.Construction.L12 (hLoc α) 0 := by rw [hneg_eq, hbeta_eq]

theorem L12_locG (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    Work.Construction.L12 (locG α L β (hLoc α)) 0
      = -(Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0)
        + β * Work.Construction.L12 (hLoc α) 0 :=
  L12_locG_of_integrable α L β hα hα1 hL
    (integrableOn_L12dens_zfar α L hα hα1 hL) integrableOn_bumpZ_div

end Work.FTS.LocData
end
-- ===== merged: Submission.Work.FTS.LocData.PhiZ_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.LocData

set_option autoImplicit false

theorem PhiZ_eq (i : ℕ) (hi : i ≤ 4) (z θ : ℝ) :
    Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ = Phi i z θ := by
  -- `PhiR n` is continuous at the pole `-1` (it is a polynomial) …
  have hcont : ∀ n : ℕ, n ≤ 3 → ContinuousAt (fun w : ℝ => PhiR n w) (-1) := by
    intro n hn
    interval_cases n <;> simp only [PhiR_zero, PhiR_one, PhiR_two, PhiR_three] <;> fun_prop
  -- … and does not vanish there, so `PhiR n z/(1+z)^(n+2)` has a genuine pole at `-1`.
  have hne : ∀ n : ℕ, n ≤ 3 → PhiR n (-1) ≠ 0 := by
    intro n hn
    interval_cases n <;> simp only [PhiR_zero, PhiR_one, PhiR_two, PhiR_three] <;> norm_num
  have hmain : ∀ n : ℕ, n ≤ 4 → ∀ z : ℝ,
      Work.Spaces.DzIter n (fun z _ => Work.FM.Fstar z) z θ = PhiR n z / (1 + z) ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
        intro _ z
        simp only [Work.Spaces.DzIter_zero, PhiR_zero, Work.FM.Fstar]
    | succ n ih =>
        intro hn z
        have hprev : ∀ w : ℝ, Work.Spaces.DzIter n (fun z _ => Work.FM.Fstar z) w θ
            = PhiR n w / (1 + w) ^ (n + 2) := ih (by omega)
        have hn3 : n ≤ 3 := by omega
        -- one more `D_z` is `z ∂_z` of the previous iterate
        have hstep : Work.Spaces.DzIter (n + 1) (fun z _ => Work.FM.Fstar z) z θ
            = z * deriv (fun w : ℝ =>
                Work.Spaces.DzIter n (fun z _ => Work.FM.Fstar z) w θ) z := by
          simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
        rw [hstep]
        have hfun : (fun w : ℝ => Work.Spaces.DzIter n (fun z _ => Work.FM.Fstar z) w θ)
            = fun w : ℝ => PhiR n w / (1 + w) ^ (n + 2) := funext hprev
        rw [hfun]
        rcases eq_or_ne z (-1) with hz | hz
        · -- at the pole both sides are Lean's `_/0 = 0`
          subst hz
          rw [deriv_eq_zero_at_pole (PhiR n) (n + 2) (by omega) (hcont n hn3) (hne n hn3)]
          norm_num
        · -- off the pole, the explicit polynomial recursion
          have hexp : n + 1 + 2 = n + 3 := by omega
          rw [hexp]
          exact Phi_div_deriv n hn3 hz
  show Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ = PhiR i z / (1 + z) ^ (i + 2)
  exact hmain i hi z

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L₁₂`-density integrable from *continuity* on the open quadrant and `ℋ⁴`

This module proves `L12dens_integrableOn_of_continuousOn`: for a datum `f` which is
*merely continuous* on the open quadrant `Q0 = (0,∞) × (0,π/2)` (not smooth, not analytic)
and which lies in the weighted space `ℋ⁴` (`Work.Spaces.HkMem α 4 f`), the angular density

  `Work.FM.L12dens Work.Spaces.K f s = ∫_0^{π/2} K(θ) f(s,θ)/s dθ`,  `K(θ) = 3 sin θ cos²θ`,

is Lebesgue-integrable on `(0,∞)`.

This is `Work.FTS.H2.L12densIntegrable` with the hypothesis `SmoothQuad f` replaced by
`ContinuousOn (uncurry f) Q0`.  Reviewing that proof shows that smoothness is used *only*
through continuity of the uncurried datum on the open quadrant: for

* the a.e. strong measurability of the angular slices
  (`Work.Spaces.aesm_slice_of_continuousOn_Qd`), and
* the a.e. strong measurability of the density itself, via Fubini measurability of the slice
  integral (`Work.Spaces.aesm_of_continuousOn_Qd` +
  `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`),

both of whose hypotheses are literally `ContinuousOn g (Ioi 0 ×ˢ Ioo 0 (π/2))`.  Everything
else in that proof is the pointwise domination of `f²` by the `D_z⁰`-term of `HkIntegrand`
and Cauchy–Schwarz in `θ`; neither uses differentiability.  Note `Q0` is *definitionally*
`Ioi 0 ×ˢ Ioo 0 (π/2)`, so the hypothesis is exactly the one the two measurability lemmas
want.  The two endpoints `θ = 0`, `θ = π/2` are null, and `s = 0` is negligible on `(0,∞)`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.MeridianDyn.Bridge.Pieces

set_option linter.unusedVariables false

/-! ## Pointwise domination of the slice

The `D_z⁰`-term of `HkIntegrand α 4 f` carries the weight `w/sin(2θ)^{η/2}`; since
`sin(2θ)^{η/2} ≤ 1` and `w s ≥ 1` for `s > 0`, this term dominates `f² w²`, hence `f²` is
dominated by `HkIntegrand/(w s)²`.  The radial weight `w s = (1+s)²/s²` is exactly what
absorbs the `1/s` of the density in the Cauchy–Schwarz step. -/

/-- On the open quadrant, `(g s θ)² ≤ HkIntegrand α 4 g s θ / (w s)²`. -/
private lemma g_sq_le_HkIntegrand_div_w_sq (α : ℝ) (g : ℝ → ℝ → ℝ) {s θ : ℝ} (hs : 0 < s)
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (g s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ / (Work.Spaces.w s) ^ 2 := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
  have hSpos : 0 < S := by rw [hSdef]; exact Real.rpow_pos_of_pos hsin _
  have hSsq : S ^ 2 ≤ 1 := by
    have h2 : S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
      rw [hSdef, ← Real.rpow_natCast, ← Real.rpow_mul hsin.le]; norm_num
    calc S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := h2
      _ ≤ 1 := Real.rpow_le_one hsin.le (Real.sin_le_one _) (le_of_lt Work.Spaces.eta_pos)
  have hkey : (g s θ * (Work.Spaces.w s / S)) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
    simpa only [Work.Spaces.DzIter_zero] using
      Work.Spaces.sq_le_HkIntegrand_z α 4 g s θ 0 (by norm_num)
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hstep : (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
    calc (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        ≤ (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 / S ^ 2 := by
          rw [le_div_iff₀ (pow_pos hSpos 2)]
          nlinarith [mul_nonneg (sq_nonneg (g s θ)) (sq_nonneg (Work.Spaces.w s)), hSsq]
      _ = (g s θ * (Work.Spaces.w s / S)) ^ 2 := by
          rw [mul_pow, div_pow, mul_div_assoc]
      _ ≤ _ := hkey
  exact (le_div_iff₀ (pow_pos hwpos 2)).mpr hstep

/-! ## The pointwise bound on the density -/

/-- **The pointwise bound on the `L₁₂`-density.**  For `g` continuous on the open quadrant and
`g ∈ ℋ⁴`, and for `s > 0`,

`|L12dens g s| ≤ (√(∫_θ K(θ)² dθ) + 1)·(s/(1+s)²)·√(∫_θ HkIntegrand α 4 g s θ)`.

The angular integral is bounded by Cauchy–Schwarz in `θ` (`Work.Spaces.cs_integral`)
against `Ktheta ∈ L²` and the slice `L²`-norm `√(∫_θ (g s θ)²)`, which in turn is dominated
by `√(∫_θ HkIntegrand α 4 g s θ)/w s` through the pointwise domination above; the factor
`(1/(s·w s)) = s/(1+s)²` is the sublinear weight at the origin that makes the density
integrable there. -/
private lemma L12dens_abs_le_quad (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hC : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ} (hs : 0 < s) :
    |Work.Elliptic.L12dens g s|
      ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
        * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
  have hcontg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hC
  have haesm : AEStronglyMeasurable (fun θ => g s θ) (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hcontg hs
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hw1 : 1 ≤ Work.Spaces.w s := Work.Elliptic.one_le_w hs
  have hpk : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (g s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ / (Work.Spaces.w s) ^ 2 :=
    Work.Elliptic.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => g_sq_le_HkIntegrand_div_w_sq α g hs h0 h1)
  -- the θ-slice of `g²` is integrable on `Iθ`, dominated by the `ℋ⁴`-integrand
  have hSqInt : IntegrableOn (fun θ => (g s θ) ^ 2) Work.Spaces.Iθ := by
    refine Integrable.mono' (hmem.1 s hs.le) (haesm.pow 2) ?_
    filter_upwards [hpk] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    refine le_trans hθ ?_
    rw [div_le_iff₀ (pow_pos hwpos 2)]
    calc Work.Spaces.HkIntegrand α 4 g s θ
        = Work.Spaces.HkIntegrand α 4 g s θ * 1 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 4 g s θ * (Work.Spaces.w s) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [hw1]) (Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
  have hKmem : MemLp (fun θ => Work.Elliptic.Ktheta θ) 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      Work.Elliptic.continuous_ktheta.aestronglyMeasurable).mpr
      ((Work.Elliptic.continuous_ktheta.continuousOn.pow 2).integrableOn_compact isCompact_Icc)
  have hGmem : MemLp (fun θ => g s θ) 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haesm).mpr hSqInt
  have hcs := Work.Spaces.cs_integral hKmem hGmem
  have hA : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    integral_nonneg (fun θ => sq_nonneg _)
  have hH : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ :=
    integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
  have hintle : ∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) / (Work.Spaces.w s) ^ 2 := by
    have h := MeasureTheory.integral_mono_ae hSqInt ((hmem.1 s hs.le).div_const _) hpk
    rwa [MeasureTheory.integral_div] at h
  -- Cauchy–Schwarz in the angle, then the slice `L²`-bound
  have hab : |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s) := by
    have h1 : |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := by
      calc |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ|
          = Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ) ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)) := Real.sqrt_le_sqrt hcs
        _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := Real.sqrt_mul hA _
    have h2 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s := by
      calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)
          ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
              / (Work.Spaces.w s) ^ 2) := Real.sqrt_le_sqrt hintle
        _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
              / Real.sqrt ((Work.Spaces.w s) ^ 2) := Real.sqrt_div hH _
        _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
              / Work.Spaces.w s := by
            rw [Real.sqrt_sq_eq_abs, abs_of_pos hwpos]
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
  have key : (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s)) / s
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
    rw [Work.Spaces.w]; field_simp; try ring
  rw [Work.Elliptic.L12dens_eq_angMoment_div, Work.Elliptic.angMoment, abs_div, abs_of_pos hs]
  calc |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ| / s
      ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s)) / s := by
        rw [div_le_div_iff_of_pos_right hs]; exact hab
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := key
    _ ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1) * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)

/-! ## A.e. strong measurability of the density

The joint integrand `(s,θ) ↦ K(θ)·g(s,θ)/s` is continuous on the open quadrant, hence a.e.
strongly measurable for `(volume.restrict Iz).prod (volume.restrict Iθ)`
(`Work.Spaces.aesm_of_continuousOn_Qd`); Fubini measurability of the partial integral
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) then gives the a.e. strong
measurability of `s ↦ ∫_θ K(θ)·g(s,θ)/s = L12dens g s` for `volume.restrict Iz`. -/

/-- `L12dens g` is a.e. strongly measurable on `Iz = [0,∞)` for data that are continuous on
the open quadrant. -/
private lemma L12dens_aesm (g : ℝ → ℝ → ℝ)
    (hC : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    AEStronglyMeasurable (Work.Elliptic.L12dens g) (volume.restrict Work.Spaces.Iz) := by
  have hcontg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hC
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.Elliptic.continuous_ktheta.comp_continuousOn continuous_snd.continuousOn
  have hF : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * g p.1 p.2 / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (h1.mul hcontg).div continuousOn_fst (fun p hp => ne_of_gt hp.1)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * g p.1 p.2 / p.1) hF
  have h := hjoint.integral_prod_right' (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
  convert h using 1
  funext z
  rfl

/-! ## The main theorem -/

/-- `L12dens f ∈ L¹((0,∞))` from `ContinuousOn (uncurry f) Q0` and `HkMem α 4 f` alone (no
smoothness).  Route: `|L12dens f s| ≤ sqrt(∫_θ Ktheta²)·(1/w s)·sqrt(∫_θ HkIntegrand α 4 f s θ)`
for `s > 0` (Cauchy–Schwarz in `θ` against `Ktheta ∈ L²`, together with
`(f s θ)² ≤ HkIntegrand α 4 f s θ / (w s)²` for a.e. `θ`, which is
`Work.Spaces.sq_le_HkIntegrand_z` combined with `sin(2θ)^{η/2} ≤ 1` and `w ≥ 1`);
then AM–GM `2√H ≤ 1 + H` dominates the density by an integrable function, the two
integrable pieces being `(s/(1+s)²)² ∈ L¹((0,∞))` (`Work.Elliptic.psi_sq_integrable_aux`,
transferred to `Iz` by `Work.Elliptic.restrict_Ioi_eq_restrict_Iz`) and
`s ↦ ∫_θ HkIntegrand α 4 f s θ` (the second component of `Work.Spaces.HkMem`). -/
theorem L12dens_integrableOn_of_continuousOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) := by
  -- `Work.FM.L12dens Work.Spaces.K f` is definitionally `Work.Elliptic.L12dens f`
  change MeasureTheory.IntegrableOn (Work.Elliptic.L12dens f) (Set.Ioi 0)
  set C : ℝ := Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have haesm := L12dens_aesm f hC
  -- AM–GM domination of the density by an integrable function, a.e. on `Iz`
  have hbd : ∀ᵐ s ∂(volume.restrict Work.Spaces.Iz),
      ‖Work.Elliptic.L12dens f s‖ ≤ (C / 2) * ((s / (1 + s) ^ 2) ^ 2
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with s hs
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ s from hs) with h0 | hpos
    · -- at `s = 0` both sides are `0` (the density is divided by `0`, hence vanishes)
      subst h0
      have hz : Work.Elliptic.L12dens f 0 = 0 := by
        rw [Work.Elliptic.L12dens]; simp
      rw [hz, norm_zero]
      have hX : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f 0 θ :=
        integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f 0 θ)
      refine mul_nonneg (by linarith [hCpos]) ?_
      have h0' : ((0 : ℝ) / (1 + 0) ^ 2) ^ 2 = 0 := by norm_num
      rw [h0', zero_add]
      exact hX
    · have h1 := L12dens_abs_le_quad α f hC hmem hpos
      have hX : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ :=
        integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f s θ)
      have hAM : C * (s / (1 + s) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)
          ≤ (C / 2) * ((s / (1 + s) ^ 2) ^ 2
            + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ) := by
        nlinarith [sq_nonneg ((s / (1 + s) ^ 2)
            - Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)),
          Real.sq_sqrt hX]
      rw [Real.norm_eq_abs, hCdef]
      exact le_trans h1 hAM
  -- the dominating function is integrable on `Iz`
  have hH_int : IntegrableOn (fun s => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 f s θ) Work.Spaces.Iz := hmem.2
  have hpsi : IntegrableOn (fun s => (s / (1 + s) ^ 2) ^ 2) Work.Spaces.Iz := by
    change MeasureTheory.Integrable (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2)
      (volume.restrict Work.Spaces.Iz)
    rw [← Work.Elliptic.restrict_Ioi_eq_restrict_Iz]
    exact Work.Elliptic.psi_sq_integrable_aux
  have hdom : IntegrableOn (fun s => (C / 2) * ((s / (1 + s) ^ 2) ^ 2
      + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)) Work.Spaces.Iz :=
    (hpsi.add hH_int).const_mul (C / 2)
  have hIntIz : IntegrableOn (Work.Elliptic.L12dens f) Work.Spaces.Iz := hdom.mono' haesm hbd
  exact hIntIz.mono_set Set.Ioi_subset_Ici_self

end Work.FTS.MeridianDyn.Bridge.Pieces
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow10aux.PhiDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.NRow10aux

/-- `φ(z) = z / (1 + z)`: the bounded radial (i.e. `θ`-independent) factor whose multiplication
on `ℋ⁴` is the content of `Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk`. -/
def phiF (z : ℝ) : ℝ := z / (1 + z)




end Work.FTS.NonlinRows.NRow10aux
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.NRow10aux

set_option autoImplicit false

theorem hkmem_of_majorant (α : ℝ) (k : ℕ) {h f : ℝ → ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hsmh : Work.FTS.EllipticEst.SmoothOpen h) (hmf : Work.Spaces.HkMem α k f)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α k h z θ ≤ K * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkMem α k h ∧ Work.Spaces.HkSq α k h ≤ K * Work.Spaces.HkSq α k f := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hsmh.continuousOn_HkIntegrand α k
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.HkIntegrand α k h z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α k h 0 θ) = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => by simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz0
  have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hMslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ : ℝ => K * Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iθ :=
    fun z hz => (hmf.1 z hz).const_mul K
  have hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      K * Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := by
    have hfun : (fun z => ∫ θ in Work.Spaces.Iθ, K * Work.Spaces.HkIntegrand α k f z θ)
        = fun z => K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
      funext fun z => MeasureTheory.integral_const_mul K _
    rw [hfun]
    exact hmf.2.const_mul K
  have hle_ae : ∀ z ∈ Work.Spaces.Iz,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α k h z θ ≤ K * Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz
    have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) :=
      (MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0:ℝ))
          (b := (π/2)))).symm
    rw [hmeas]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hle z hz θ hθ)
  have hmem : Work.Spaces.HkMem α k h := by
    constructor
    · intro z hz
      refine MeasureTheory.Integrable.mono' (hMslice z hz) (hslice z hz) ?_
      filter_upwards [hle_ae z hz] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k h z θ)]
      exact hθ
    · refine MeasureTheory.Integrable.mono' hMz hjoint.integral_prod_right' ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ :=
        MeasureTheory.integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α k h z θ)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k h z θ)
        ((hmf.1 z hz).const_mul K) (hle_ae z hz)
  refine ⟨hmem, ?_⟩
  simp only [Work.Spaces.HkSq]
  have hstep : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
      ≤ ∫ z in Work.Spaces.Iz,
          K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k h z θ)
      (hmf.2.const_mul K) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have h2 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      have h3 := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k h z θ)
        ((hmf.1 z hz).const_mul K) (hle_ae z hz)
      rwa [MeasureTheory.integral_const_mul] at h3
    exact h2
  exact le_trans hstep (le_of_eq (MeasureTheory.integral_const_mul K _))

end Work.FTS.NonlinRows.NRow10aux
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_SmoothQuadPthFstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux


end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
-- ===== merged: Submission.Work.FTS.OpenPkg.ProdOpen.ProdDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.ProdOpen

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.Spaces

/-- The angular weight `w z / sin(2θ)^{η/2}` carried by the pure `D_z`-slots of
`HkIntegrand`. -/
def Hv (z θ : ℝ) : ℝ := w z / (Real.sin (2 * θ)) ^ (eta / 2)

/-- The `(γ-1)⁻¹`-block of the majorant of the open-quadrant product rule: this is the part
priced by the two `ℋ⁴`-norms of the factors. -/
def SInv (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (gam α - 1)⁻¹
    * (HkSq α 4 f * HkIntegrand α 4 g z θ + HkSq α 4 g * HkIntegrand α 4 f z θ)

/-- The two exceptional terms of the `(3,1)`-slot, both carrying the full weight `W`: the only
summands of `HkIntegrand α 4 (f·g)` that are out of reach of the pointwise bound `PwAny`. -/
def Texc (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ((DzIter 3 f z θ * Dth g z θ) ^ 2 + (Dth f z θ * DzIter 3 g z θ) ^ 2)
    * (Wt α z θ) ^ 2

/-- The target majorant, as a single expression. -/
def Maj (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ := SInv α f g z θ + Texc α f g z θ

theorem gam_sub_one_pos {α : ℝ} (hα : 0 < α) : 0 < gam α - 1 := by
  rw [gam_sub_one]; linarith


theorem inv_gam_sub_one_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ (gam α - 1)⁻¹ :=
  inv_nonneg.mpr (gam_sub_one_pos hα).le


theorem SInv_nonneg {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ SInv α f g z θ := by
  rw [SInv]
  refine mul_nonneg (inv_gam_sub_one_nonneg hα) ?_
  exact add_nonneg (mul_nonneg (HkSq_nonneg α 4 f) (HkIntegrand_nonneg α 4 g z θ))
    (mul_nonneg (HkSq_nonneg α 4 g) (HkIntegrand_nonneg α 4 f z θ))

theorem Texc_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ Texc α f g z θ := by
  rw [Texc]
  exact mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

theorem Maj_nonneg {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Maj α f g z θ :=
  add_nonneg (SInv_nonneg hα f g z θ) (Texc_nonneg α f g z θ)

/-- The `SInv`-block dominates its first summand. -/
theorem mul_inv_mul_le_SInv_left {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (gam α - 1)⁻¹ * (HkSq α 4 f * HkIntegrand α 4 g z θ) ≤ SInv α f g z θ := by
  rw [SInv]
  refine mul_le_mul_of_nonneg_left ?_ (inv_gam_sub_one_nonneg hα)
  exact le_add_of_nonneg_right (mul_nonneg (HkSq_nonneg α 4 g) (HkIntegrand_nonneg α 4 f z θ))

/-- The `SInv`-block dominates its second summand. -/
theorem mul_inv_mul_le_SInv_right {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (gam α - 1)⁻¹ * (HkSq α 4 g * HkIntegrand α 4 f z θ) ≤ SInv α f g z θ := by
  rw [SInv]
  refine mul_le_mul_of_nonneg_left ?_ (inv_gam_sub_one_nonneg hα)
  exact le_add_of_nonneg_left (mul_nonneg (HkSq_nonneg α 4 f) (HkIntegrand_nonneg α 4 g z θ))

end Work.FTS.OpenPkg.ProdOpen
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.ScoefOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.OpenPkg

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The slices of a `SmoothOpen` function -/

/-- The `z`-slice of a `SmoothOpen` function at an interior angle is `C^∞` on the open
half-line `(0,∞)` (in the genuine smooth order). -/
theorem smoothOpen_slice_z {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => f z θ) (Set.Ioi 0) :=
  Work.FTS.LocData.contDiffOn_slice_z hf hθ

/-- `D_θ` preserves the open-quadrant smooth class. -/
theorem smoothOpen_DthIter {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (a : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DthIter a f) :=
  Work.FTS.LocData.contDiffOn_DthIter Work.FTS.EllipticEst.isOpen_Q0 hf a

/-- The `z`-slice of `D_θ^a f` at an interior angle is `C^∞` on `(0,∞)`. -/
theorem smoothOpen_DthIter_slice_z {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (a : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => Work.Spaces.DthIter a f z θ) (Set.Ioi 0) :=
  Work.FTS.LocData.contDiffOn_slice_z (smoothOpen_DthIter hf a) hθ

/-! ## The Stirling expansion in the genuine smooth order on `(0,∞)` -/

private theorem deriv_zpow_open (k : ℕ) (z : ℝ) :
    deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id k
  rw [show (fun z' : ℝ => z') ^ k = (fun z' : ℝ => z' ^ k) from rfl] at h
  rw [h, deriv_id'']
  ring

private theorem z_mul_term_open (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B) = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | m
  · ring
  · rw [pow_succ]; push_cast; ring

/-- In the genuine smooth order, the `z`-slices of the iterated `z`-derivatives are again
smooth on the open half-line `(0,∞)`. -/
theorem pzIter_slice_contDiff_open {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi 0)) :
    ∀ k : ℕ, ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.pzIter k h z' θ) (Set.Ioi 0) := by
  intro k
  induction k with
  | zero => simpa using hsmooth
  | succ n ih =>
    have h := ih.deriv_of_isOpen isOpen_Ioi
      (le_of_eq (rfl : Work.Stability.smoothOrder + 1 = Work.Stability.smoothOrder))
    simpa [Work.Spaces.pzIter_succ, Work.Spaces.pz] using h

private theorem differentiableAt_pzIter_slice_open {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi 0)) (k : ℕ)
    {z : ℝ} (hz : z ∈ Set.Ioi 0) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k h z' θ) z :=
  ((pzIter_slice_contDiff_open hsmooth k).contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt
    (by simp)

private theorem deriv_pzIter_slice_open (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    deriv (fun z' => Work.Spaces.pzIter k h z' θ) z = Work.Spaces.pzIter (k + 1) h z θ := rfl

/-- **The Stirling expansion of `D_z^n` in the genuine smooth order, on the open half-line.**
For a function whose `z`-slice at the fixed angle `θ` is `C^∞` on `(0,∞)`,
`D_z^n h = ∑_{k≤n} S(n,k) z^k ∂_z^k h` on `(0,∞)`. -/
theorem DzIter_eq_sum_scoef_open {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi 0)) :
    ∀ n : ℕ, ∀ z ∈ Set.Ioi 0,
      Work.Spaces.DzIter n h z θ
        = ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * (z ^ k * Work.Spaces.pzIter k h z θ) := by
  intro n
  induction n with
  | zero =>
    intro z hz
    simp [Work.Spaces.DzIter, Work.Spaces.scoef]
  | succ n ih =>
    intro z hz
    have hdiff : ∀ k : ℕ, DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k h z' θ) z := fun k =>
      differentiableAt_pzIter_slice_open hsmooth k hz
    have hd1 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k) z := fun k =>
      differentiableAt_pow k
    have hd3 : ∀ k : ℕ,
        DifferentiableAt ℝ (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z :=
      fun k => (hd1 k).mul (hdiff k)
    have hev : (fun z' => Work.Spaces.DzIter n h z' θ)
        =ᶠ[𝓝 z] (fun z' => ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih z' hz'
    have hterm : ∀ k : ℕ,
        deriv (fun z' : ℝ => (Work.Spaces.scoef n k : ℝ)
            * (z' ^ k * Work.Spaces.pzIter k h z' θ)) z
        = (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
            + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
      intro k
      rw [deriv_const_mul (d := fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ)
        (Work.Spaces.scoef n k : ℝ) (hd3 k)]
      congr 1
      have hmul := deriv_mul (c := fun z' : ℝ => z' ^ k)
        (d := fun z' : ℝ => Work.Spaces.pzIter k h z' θ) (hd1 k) (hdiff k)
      have hmul' : deriv (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z
          = deriv (fun z' : ℝ => z' ^ k) z * Work.Spaces.pzIter k h z θ
            + z ^ k * deriv (fun z' : ℝ => Work.Spaces.pzIter k h z' θ) z := hmul
      rw [hmul', deriv_zpow_open, deriv_pzIter_slice_open]
    have hderiv : deriv (fun z' => Work.Spaces.DzIter n h z' θ) z
        = ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
              + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
      rw [Filter.EventuallyEq.deriv_eq hev]
      have hsumfun : (fun z' => ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ))
          = (∑ k ∈ Finset.range (n + 1),
              fun z' => (Work.Spaces.scoef n k : ℝ)
                * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
        funext z'
        simp [Finset.sum_apply]
      rw [hsumfun, deriv_sum (fun k hk => (hd3 k).const_mul (Work.Spaces.scoef n k : ℝ))]
      exact Finset.sum_congr rfl fun k hk => hterm k
    calc Work.Spaces.DzIter (n + 1) h z θ
        = z * deriv (fun z' => Work.Spaces.DzIter n h z' θ) z := by
          simp [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      _ = z * (∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
              + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) := by rw [hderiv]
      _ = ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ k * Work.Spaces.pzIter k h z θ
              + z ^ (k + 1) * Work.Spaces.pzIter (k + 1) h z θ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have h1 : z * ((Work.Spaces.scoef n k : ℝ)
                * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ))
              = (Work.Spaces.scoef n k : ℝ)
                * (z * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) := by ring
          rw [h1, z_mul_term_open]
      _ = ∑ j ∈ Finset.range (n + 2),
            (Work.Spaces.scoef (n + 1) j : ℝ) * (z ^ j * Work.Spaces.pzIter j h z θ) :=
          Work.Spaces.scoef_sum_shift n (fun k => Work.Spaces.pzIter k h z θ) z

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **A source compactly supported in the open quadrant.**  There is a rectangle
`[a,b] × [c,d]` with `0 < a`, `a < b`, `0 < c`, `c < d`, `d < π/2` outside of which `G`
vanishes identically. -/
def CptQ (G : ℝ → ℝ → ℝ) : Prop :=
  ∃ a b c d : ℝ, 0 < a ∧ a < b ∧ 0 < c ∧ c < d ∧ d < Real.pi / 2 ∧
    ∀ z θ, G z θ ≠ 0 → z ∈ Set.Icc a b ∧ θ ∈ Set.Icc c d

/-- **A `C^∞` source compactly supported in the open quadrant.**  `C^∞` means `C^n` on all of
`ℝ²` for every `n` (so the `z`- and `θ`-slices are smooth on all of `ℝ`, in particular on a
neighbourhood of the closed angular interval). -/
def SmoothCptQ (G : ℝ → ℝ → ℝ) : Prop :=
  (∀ n : ℕ, ContDiff ℝ n (Function.uncurry G)) ∧ CptQ G

/-! ## Projections -/

theorem SmoothCptQ.smooth {G : ℝ → ℝ → ℝ} (h : SmoothCptQ G) :
    ∀ n : ℕ, ContDiff ℝ n (Function.uncurry G) := h.1

theorem SmoothCptQ.cpt {G : ℝ → ℝ → ℝ} (h : SmoothCptQ G) : CptQ G := h.2

theorem SmoothCptQ.smoothOpen {G : ℝ → ℝ → ℝ} (h : SmoothCptQ G) :
    Work.FTS.EllipticEst.SmoothOpen G :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall G).mpr fun n => (h.1 n).contDiffOn

/-! ## The support rectangle -/

/-- The support rectangle of a `CptQ` source, in a form convenient for later `obtain`s. -/
theorem CptQ.exists_box {G : ℝ → ℝ → ℝ} (h : CptQ G) :
    ∃ a b c d : ℝ, 0 < a ∧ a < b ∧ 0 < c ∧ c < d ∧ d < Real.pi / 2 ∧
      (∀ z θ, G z θ ≠ 0 → (z, θ) ∈ Set.Icc a b ×ˢ Set.Icc c d) := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, H⟩ := h
  exact ⟨a, b, c, d, ha, hab, hc, hcd, hd, fun z θ hG => ⟨(H z θ hG).1, (H z θ hG).2⟩⟩








/-! ## Slices of a smooth compactly supported source -/

/-- Every `z`-slice of a `SmoothCptQ` source is `C^∞` on `ℝ`. -/
theorem SmoothCptQ.slice_contDiff {G : ℝ → ℝ → ℝ} (h : SmoothCptQ G) (z : ℝ) (n : ℕ) :
    ContDiff ℝ n (fun θ : ℝ => G z θ) := by
  have hlin : ContDiff ℝ n (fun θ : ℝ => (z, θ)) := contDiff_const.prodMk contDiff_id
  exact (h.1 n).comp hlin

/-- Every `z`-slice of a `SmoothCptQ` source is `C^∞` on the closed angular interval. -/
theorem SmoothCptQ.slice_contDiffOn {G : ℝ → ℝ → ℝ} (h : SmoothCptQ G) (z : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun θ : ℝ => G z θ) Work.Spaces.Iθ :=
  (h.slice_contDiff z n).contDiffOn

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## Test functions on the open quadrant -/

/-- **A test function on the open quadrant**: globally `C^∞`, compactly supported, with support
inside `Q0 = (0,∞) × (0,π/2)`.  (The support is *strictly* inside the open quadrant, so every
`θ`-derivative of a test function also vanishes at the angular endpoints and at `z = 0`.) -/
def TestQ0 (φ : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry φ)
    ∧ HasCompactSupport (Function.uncurry φ)
    ∧ tsupport (Function.uncurry φ) ⊆ Q0

theorem TestQ0.smooth {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry φ) := h.1

theorem TestQ0.cpt {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : HasCompactSupport (Function.uncurry φ) :=
  h.2.1

theorem TestQ0.tsupp {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    tsupport (Function.uncurry φ) ⊆ Q0 := h.2.2

theorem TestQ0.continuous {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    Continuous (Function.uncurry φ) := h.smooth.continuous

theorem TestQ0.continuousOn {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    ContinuousOn (Function.uncurry φ) Q0 := h.continuous.continuousOn

/-! ## The formal transposes of the elementary operators

For a test function `φ`, `∫_{Q0} (z ∂_z f)·φ = ∫_{Q0} f·(DzStar φ)` with
`DzStar φ = -(z ∂_z φ + φ)`, because the boundary term at `z = 0` carries the factor `z` while
the one at `z = ∞` dies from the compact support.  Likewise
`∫_{Q0} (sin 2θ ∂_θ f)·φ = ∫_{Q0} f·(DthStar φ)` with `DthStar φ = -(sin 2θ ∂_θ φ + 2 cos 2θ φ)`,
both angular boundary terms vanishing because `sin 2θ = 0` at the endpoints.  Iterating gives
the transposes of `D_z^j`, `D_θ^i` and of their compositions, and the plain derivatives have
transposes `±` themselves (two dimensions of integration by parts with compactly supported
test functions, no boundary terms at all). -/

/-- The transpose of `∂_z^j`: `pzIterStar j φ = (-1)^j ∂_z^j φ`. -/
def pzIterStar (j : ℕ) (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-1 : ℝ) ^ j * Work.Spaces.pzIter j φ z θ

/-- The transpose of `∂_θ^i`: `pthIterStar i φ = (-1)^i ∂_θ^i φ`. -/
def pthIterStar (i : ℕ) (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-1 : ℝ) ^ i * Work.Spaces.pthIter i φ z θ

/-- The transpose of `D_z = z ∂_z`: `DzStar φ = -(D_z φ + φ)`. -/
def DzStar (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Spaces.Dz φ z θ + φ z θ)

/-- The transpose of `D_θ = sin 2θ ∂_θ`: `DthStar φ = -(D_θ φ + 2 cos 2θ · φ)`. -/
def DthStar (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Spaces.Dth φ z θ + 2 * Real.cos (2 * θ) * φ z θ)

/-- The transpose of `D_z^j`: iterate `DzStar`. -/
def DzIterStar : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, φ => φ
  | n + 1, φ => DzIterStar n (DzStar φ)

/-- The transpose of `D_θ^i`: iterate `DthStar`. -/
def DthIterStar : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, φ => φ
  | n + 1, φ => DthIterStar n (DthStar φ)

/-- The transpose of `mixed j i = D_z^j D_θ^i`: `(D_θ^i)*` after `(D_z^j)*`. -/
def mixedStar (j i : ℕ) (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  DthIterStar i (DzIterStar j φ)

/-! ## The three slot operators and their transposes -/

/-- The first slot operator `f ↦ z² ∂_z² f`. -/
def slot1 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ

/-- The second slot operator `f ↦ ∂_θ² f`. -/
def slot2 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 f

/-- The third slot operator `f ↦ z ∂_z ∂_θ² f`. -/
def slot3 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.Dz (Work.Spaces.pthIter 2 f)

/-- The transpose of the first slot: the multiplication by `z²` is self-adjoint, so it stays on
the test function. -/
def slot1Star (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  pzIterStar 2 (fun z θ => z ^ 2 * φ z θ)

/-- The transpose of the second slot. -/
def slot2Star (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := pthIterStar 2 φ

/-- The transpose of the third slot. -/
def slot3Star (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := pthIterStar 2 (DzStar φ)

/-- The weight of the `(j,i)`-term of `HkIntegrand`: the pure weight `w/√sin^η` of the first
sum when `i = 0`, and `Wt = w·sin(2θ)^{-γ/2}` of the mixed double sum when `i ≥ 1`. -/
def termWeight (α : ℝ) (i : ℕ) : ℝ → ℝ → ℝ :=
  if i = 0 then fun z θ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
  else Work.Spaces.Wt α

/-- The pairs `(j,i)` indexing the terms of `HkIntegrand`: the pure terms `(j,0)` with `j ≤ k`
and the mixed terms `(j,i)` with `1 ≤ i` and `i + j ≤ k`. -/
def HkActivePairs (k : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.range (k + 1)).product (Finset.range (k + 1))).filter
    (fun p : ℕ × ℕ => p.2 = 0 ∧ p.1 ≤ k ∨ 1 ≤ p.2 ∧ p.2 + p.1 ≤ k))

/-- The three slot operators, indexed by `ℕ` (indices `≥ 2` repeat the third one). -/
def slot : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0 => slot1
  | 1 => slot2
  | _ => slot3

theorem slot_zero (f : ℝ → ℝ → ℝ) : slot 0 f = slot1 f := rfl
theorem slot_one (f : ℝ → ℝ → ℝ) : slot 1 f = slot2 f := rfl
theorem slot_two (f : ℝ → ℝ → ℝ) : slot 2 f = slot3 f := rfl

/-- The operator of the `(j,i)`-th sub-slot of the `r`-th slot, `f ↦ mixed j i (slot_r f)`. -/
def subSlot (r : ℕ) (j i : ℕ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Spaces.mixed j i (slot r f)

/-- The transpose of the `(j,i)`-th sub-slot of the `r`-th slot: the transpose of a composition
reverses the order, so the slot transpose acts *last*. -/
def subSlotStar (r : ℕ) (j i : ℕ) (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  match r with
  | 0 => slot1Star (mixedStar j i φ)
  | 1 => slot2Star (mixedStar j i φ)
  | _ => slot3Star (mixedStar j i φ)




@[simp] theorem subSlot_zero (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    subSlot 0 j i f = Work.Spaces.mixed j i (slot1 f) := by
  rw [subSlot, slot_zero]

@[simp] theorem subSlot_one (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    subSlot 1 j i f = Work.Spaces.mixed j i (slot2 f) := by
  rw [subSlot, slot_one]

@[simp] theorem subSlot_two (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    subSlot 2 j i f = Work.Spaces.mixed j i (slot3 f) := by
  rw [subSlot, slot_two]


end Work.FTS.PhiStar.Honesty.SlotsLimit
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Joint.tonelli_slices_of_integrableOn_Q0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.Joint

open MeasureTheory Set
open scoped Real

theorem tonelli_slices_of_integrableOn_Q0 {g : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => g p.1 p.2)
      Work.FTS.EllipticEst.Q0) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.IntegrableOn (fun θ : ℝ => g z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, g z θ)
        Work.Spaces.Iz := by
  -- ### `Iz = [0,∞)` differs from `(0,∞)` by the null set `{0}`
  have hIz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl, MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null (t := {0}) ?_ (measure_singleton 0)
      intro x hx
      rw [Set.mem_sdiff] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [Set.mem_Ici] at hx1
      rw [Set.mem_Ioi] at hx2
      rw [Set.mem_singleton_iff]
      exact le_antisymm (not_lt.mp hx2) hx1
    · rw [sdiff_eq_empty.mpr Set.Ioi_subset_Ici_self, measure_empty]
  -- ### `Iθ = [0,π/2]` differs from `(0,π/2)` by the null set `{0, π/2}`
  have hIθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl, MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
      · intro x hx
        simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx ⊢
        obtain ⟨⟨h0, h1⟩, h2⟩ := hx
        by_cases hx0 : x = 0
        · exact Or.inl hx0
        · right
          by_contra hx2
          exact h2 ⟨lt_of_le_of_ne h0 (Ne.symm hx0), lt_of_le_of_ne h1 hx2⟩
      · rw [Set.insert_eq,
          measure_union_null (measure_singleton (0 : ℝ)) (measure_singleton (π / 2))]
    · rw [sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]
  have hIz' := Measure.restrict_congr_set hIz
  have hIθ' := Measure.restrict_congr_set hIθ
  -- ### the product measure of the open half-strip is the restriction to `Q0`
  have hEq : (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
      = MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0 := by
    rw [show Work.FTS.EllipticEst.Q0 = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) from rfl]
    exact Measure.prod_restrict _ _
  have hprod : MeasureTheory.Integrable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))) := by
    rw [hEq]
    exact hint
  -- ### Tonelli: a.e. angular slice integrability, and integrability of the partial integral
  constructor
  · rw [hIz']
    refine (hprod.prod_right_ae).mono fun z hz => ?_
    rwa [MeasureTheory.IntegrableOn, hIθ']
  · rw [MeasureTheory.IntegrableOn, hIz', hIθ']
    exact hprod.integral_prod_left

end Work.FTS.PhiStar.Honesty.SlotsLimit.Joint
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux.locallyIntegrableOn_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux

open scoped MeasureTheory ENNReal Topology
open MeasureTheory Set Filter

/-- The elementary pointwise bound `|a| ≤ 1 + a²`, used to upgrade an `L²`-function on a set of
finite measure to an `L¹`-function. -/
lemma abs_le_one_add_sq (a : ℝ) : |a| ≤ 1 + a ^ 2 := by
  nlinarith [sq_nonneg (|a| - 1), sq_abs a, abs_nonneg a]

/-- **Local integrability from a weighted square bound.**  If `ρ` is continuous and positive on
the open quadrant `Q0`, `u` is a.e. strongly measurable on `Q0` and `u²ρ²` is integrable on
`Q0`, then `u` is locally integrable on `Q0` with respect to Lebesgue measure.

Note that no lower bound on `ρ` near the boundary of `Q0` is assumed: the argument is purely
local and works on a compact piece of `Q0`. -/
theorem locallyIntegrableOn_of_integrableOn_sq_mul_sq {ρ : ℝ → ℝ → ℝ} {u : ℝ × ℝ → ℝ}
    (hρpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < ρ p.1 p.2)
    (hρcont : ContinuousOn (Function.uncurry ρ) Work.FTS.EllipticEst.Q0)
    (hum : AEStronglyMeasurable u (volume.restrict Work.FTS.EllipticEst.Q0))
    (hu : IntegrableOn (fun p : ℝ × ℝ => (u p) ^ 2 * (ρ p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0) :
    LocallyIntegrableOn u Work.FTS.EllipticEst.Q0 volume := by
  intro x hx
  -- A small closed ball around `x`, entirely inside the open quadrant.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Work.FTS.EllipticEst.isOpen_Q0 x hx
  set r : ℝ := ε / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  set K : Set (ℝ × ℝ) := Metric.closedBall x r with hKdef
  have hKsub : K ⊆ Work.FTS.EllipticEst.Q0 := by
    rw [hKdef]
    intro p hp
    refine hball ?_
    have hp' : dist p x ≤ r := by simpa only [Metric.mem_closedBall] using hp
    rw [Metric.mem_ball]
    have : dist p x < ε := by rw [hrdef] at hp'; linarith
    exact this
  have hKc : IsCompact K := by rw [hKdef]; exact isCompact_closedBall x r
  have hKne : K.Nonempty := by
    rw [hKdef]; exact Metric.nonempty_closedBall.mpr hrpos.le
  have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
  -- `ρ` attains a positive minimum `m` on the compact set `K`.
  have hρcontK : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) K := hρcont.mono hKsub
  obtain ⟨p₀, hp₀K, hp₀min⟩ := hKc.exists_isMinOn hKne hρcontK
  set m : ℝ := ρ p₀.1 p₀.2 with hmdef
  have hmpos : 0 < m := hρpos p₀ (hKsub hp₀K)
  have hρge : ∀ p ∈ K, m ≤ ρ p.1 p.2 := fun p hp => hp₀min hp
  have hKmem : K ∈ 𝓝[Work.FTS.EllipticEst.Q0] x := by
    rw [hKdef]
    exact (Filter.le_def.mp nhdsWithin_le_nhds) _ (Metric.closedBall_mem_nhds x hrpos)
  refine ⟨K, hKmem, ?_⟩
  -- `u²ρ² ∈ L¹(K)`
  have hKint : IntegrableOn (fun p : ℝ × ℝ => (u p) ^ 2 * (ρ p.1 p.2) ^ 2) K :=
    hu.mono_set hKsub
  have hdom : Integrable (fun p : ℝ × ℝ => (u p) ^ 2 * (ρ p.1 p.2) ^ 2 / m ^ 2)
      (volume.restrict K) := hKint.div_const _
  -- hence `u² ∈ L¹(K)`, since `ρ ≥ m > 0` on `K`
  have hu2 : Integrable (fun p : ℝ × ℝ => (u p) ^ 2) (volume.restrict K) := by
    refine hdom.mono' ((hum.mono_measure ?_).pow 2) ?_
    · exact Measure.restrict_mono hKsub le_rfl
    · rw [ae_restrict_iff' hKmeas]
      refine Eventually.of_forall fun p hp => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 : m ^ 2 ≤ (ρ p.1 p.2) ^ 2 := by nlinarith [hρge p hp, hmpos]
      rw [le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg (u p))
  -- on the finite measure set `K`, `L² ⊆ L¹` via `|u| ≤ 1 + u²`
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hKc.measure_lt_top.ne
  have hone : Integrable (fun _ : ℝ × ℝ => (1 : ℝ)) (volume.restrict K) :=
    (integrable_const_iff (c := (1 : ℝ))).mpr (Or.inr hfin)
  have hbdd : Integrable (fun p : ℝ × ℝ => 1 + (u p) ^ 2) (volume.restrict K) :=
    hone.add hu2
  refine hbdd.mono' (hum.mono_measure (Measure.restrict_mono hKsub le_rfl)) ?_
  refine Eventually.of_forall fun p => ?_
  rw [Real.norm_eq_abs]
  exact abs_le_one_add_sq (u p)

/-- **The requested statement.**  On the open quadrant `Q0`, a function `u` with integrable
weighted square `u²ρ²` (`ρ` continuous and positive on `Q0`) differs from a continuous function
`v` by a locally integrable function. -/
theorem locallyIntegrableOn_sub {ρ : ℝ → ℝ → ℝ}
    (hρpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < ρ p.1 p.2)
    (hρcont : ContinuousOn (Function.uncurry ρ) Work.FTS.EllipticEst.Q0)
    {u v : ℝ × ℝ → ℝ}
    (hum : AEStronglyMeasurable u (volume.restrict Work.FTS.EllipticEst.Q0))
    (hu : IntegrableOn (fun p : ℝ × ℝ => (u p) ^ 2 * (ρ p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0)
    (hv : ContinuousOn v Work.FTS.EllipticEst.Q0) :
    LocallyIntegrableOn (fun p : ℝ × ℝ => u p - v p) Work.FTS.EllipticEst.Q0
      (volume.restrict Work.FTS.EllipticEst.Q0) := by
  have hu_loc : LocallyIntegrableOn u Work.FTS.EllipticEst.Q0
      (volume.restrict Work.FTS.EllipticEst.Q0) :=
    (locallyIntegrableOn_of_integrableOn_sq_mul_sq hρpos hρcont hum hu).mono_measure
      Measure.restrict_le_self
  have hv_loc : LocallyIntegrableOn v Work.FTS.EllipticEst.Q0
      (volume.restrict Work.FTS.EllipticEst.Q0) :=
    ContinuousOn.locallyIntegrableOn hv Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  exact hu_loc.sub hv_loc

end Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.aesm_uncurry_abs_pzF =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem aesm_uncurry_abs_pzF {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) {a b : ℝ} (ha : 0 < a) :
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun t θ : ℝ => |Work.Spaces.pz F t θ|))
      ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- On the open quadrant `(0,∞) × (0,π/2)` the function `(z,θ) ↦ |pz F z θ|` is continuous
  -- (`SmoothOpen.pz`), hence a.e. strongly measurable for the product of the restrictions of
  -- Lebesgue measure to `Iz = [0,∞)` and `Iθ = [0,π/2]` (`Work.Spaces.aesm_of_continuousOn_Qd`).
  have hbig : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |Work.Spaces.pz F p.1 p.2|)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hsm.pz).continuousOn.abs
  -- `Icc a b ⊆ Ioi 0 ⊆ Iz` since `0 < a`, so shrinking the radial measure preserves
  -- a.e. strong measurability.
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := by
    intro t ht
    exact le_trans (le_of_lt ha) ht.1
  have hmono : (MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Measure.prod_mono
      (MeasureTheory.Measure.restrict_mono hsub le_rfl) le_rfl
  exact hbig.mono_measure hmono

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.cmode_slice_mass_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped Real

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **The pointwise identity.**  On `Iθ`, the weighted square of `g` is the product of the
`σ`-weighted square, the radial weight `w z²` and the angular weight `σ θ`; this is
`AngSecond.sq_mul_W` with the abbreviations `w2`, `sig` unfolded. -/
private lemma sq_mul_W_explicit {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2 := by
  rw [Work.FTS.EllipticEst.AngSecond.sq_mul_W g hθ]
  rw [Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig]
  ring

/-- **The pointwise identity for `D_z`.**  On `Iθ` the second (`i = 1`) pure `D_z`-summand of
`HkIntegrand`, `(D_z F · w / sin(2θ)^{η/2})²`, is the `∂_zF`-mass times `z² · w z²`. -/
private lemma sq_mul_W_explicit_Dz {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter 1 F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.pz F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (z ^ 2 * (Work.Spaces.w z) ^ 2) := by
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  rw [show (z * Work.Spaces.pz F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.pz F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 * z ^ 2
      from by ring]
  rw [Work.FTS.EllipticEst.AngSecond.sq_mul_W (Work.Spaces.pz F) hθ]
  rw [Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig]
  ring

/-- **The slice-mass bound.**  For `F` smooth on the open quadrant and honestly in `ℋ¹`, and
every `z > 0`, the slice masses of `F` and of `∂_zF` (with the weight `sin(2θ)^{-η}`) are
integrable on `Iθ` and are bounded by the slice integral of `HkIntegrand α 1 F`, after
multiplying by the appropriate powers of the radial weight (`w z²` resp. `z² w z²`). -/
theorem cmode_slice_mass_le {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 1 F) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ,
          (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F z θ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.pz F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pz F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F z θ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  -- the two radial weights are non-zero (`z > 0`)
  have hw2pos : 0 < (Work.Spaces.w z) ^ 2 :=
    pow_pos (Work.FTS.EllipticEst.AngSecond.w_pos hz) 2
  have hzw2pos : 0 < z ^ 2 * (Work.Spaces.w z) ^ 2 := mul_pos (pow_pos hz 2) hw2pos
  -- the slice integrability of the `ℋ¹`-integrand
  have hHz := hF.1 z hzI
  -- the two single summands of `HkIntegrand α 1 F` that we compare with
  have hs0 := Work.FTS.EllipticEst.integrableOn_zSummand α 1 hsm hF 0 (by norm_num) hzI
  have hs1 := Work.FTS.EllipticEst.integrableOn_zSummand α 1 hsm hF 1 (by norm_num) hzI
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- integrability of the `F`-mass: it is the `i = 0` summand divided by `w z²`
    refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.Integrable.mul_const hs0 ((Work.Spaces.w z) ^ 2)⁻¹) ?_ measurableSet_Icc
    intro θ hθ
    change (Work.Spaces.DzIter 0 F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        * ((Work.Spaces.w z) ^ 2)⁻¹
      = (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    rw [Work.Spaces.DzIter_zero, sq_mul_W_explicit (g := F) hθ, mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hw2pos), mul_one]
  · -- the mass bound: pull out `w z²` and compare with the `i = 0` summand
    calc (∫ θ in Work.Spaces.Iθ,
          (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) * (Work.Spaces.w z) ^ 2
        = ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.w z) ^ 2 := (MeasureTheory.integral_mul_const _ _).symm
      _ = ∫ θ in Work.Spaces.Iθ,
            (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
          exact (sq_mul_W_explicit (g := F) hθ).symm
      _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F z θ := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun θ => sq_nonneg _) hHz
            (Filter.Eventually.of_forall fun θ => ?_)
          exact Work.Spaces.sq_le_HkIntegrand_z α 1 F z θ 0 (by norm_num)
  · -- integrability of the `∂_zF`-mass: it is the `i = 1` summand divided by `z² w z²`
    refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.Integrable.mul_const hs1 ((z ^ 2 * (Work.Spaces.w z) ^ 2))⁻¹) ?_
      measurableSet_Icc
    intro θ hθ
    change (Work.Spaces.DzIter 1 F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        * ((z ^ 2 * (Work.Spaces.w z) ^ 2))⁻¹
      = (Work.Spaces.pz F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    rw [sq_mul_W_explicit_Dz (F := F) hθ, mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hzw2pos), mul_one]
  · -- the `∂_zF`-mass bound: pull out `z² w z²` and compare with the `i = 1` summand
    calc (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pz F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (z ^ 2 * (Work.Spaces.w z) ^ 2) := (MeasureTheory.integral_mul_const _ _).symm
      _ = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 1 F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
          exact (sq_mul_W_explicit_Dz (F := F) hθ).symm
      _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F z θ := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun θ => sq_nonneg _) hHz
            (Filter.Eventually.of_forall fun θ => ?_)
          exact Work.Spaces.sq_le_HkIntegrand_z α 1 F z θ 1 (by norm_num)

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.hkIntegrand_bound_on_box =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open Set

/-- The box `[a,b] × [c,d]` with `0 < a` and `0 < c ≤ d < π/2` sits inside the open
quadrant `Q0 = (0,∞) × (0,π/2)` on which `SmoothOpen` grants smoothness. -/
theorem box_subset_Q0 {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < Real.pi / 2) :
    Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  simp only [Set.mem_Icc] at hz hθ
  exact Work.FTS.EllipticEst.mem_Q0.mpr
    ⟨by linarith [hz.1], by linarith [hθ.1], by linarith [hθ.2]⟩

/-- **The `ℋ^k`-integrand is bounded on a compact box contained in the open quadrant.**
`Work.Spaces.HkIntegrand α k G` is a finite sum of squares of weighted derivatives
(`D_z^i G · w/sin(2θ)^{η/2}` and `D_z^jD_θ^i G · W`), all of which are continuous on `Q0`
when `SmoothOpen G`; the weights are continuous and non-singular on the box because the box
stays away from `z = 0` and from `θ = 0, π/2`. -/
theorem hkIntegrand_bound_on_box {α : ℝ} {G : ℝ → ℝ → ℝ} {k : ℕ} {a b c d : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G) (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) (hd : d < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z θ : ℝ, z ∈ Set.Icc a b → θ ∈ Set.Icc c d →
      Work.Spaces.HkIntegrand α k G z θ ≤ C := by
  have hsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 :=
    box_subset_Q0 ha hc hd
  have hcomp : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k G p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (hsm.continuousOn_HkIntegrand α k).mono hsub
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont
  have hpt : ((a, c) : ℝ × ℝ) ∈ Set.Icc a b ×ˢ Set.Icc c d :=
    ⟨⟨le_refl a, hab⟩, ⟨le_refl c, hcd⟩⟩
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC _ hpt)
  refine ⟨C, hCnn, fun z θ hz hθ => ?_⟩
  have hb := hC (z, θ) ⟨hz, hθ⟩
  rw [Real.norm_eq_abs] at hb
  exact le_trans (le_abs_self _) hb

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.slice_abs_diff_le_uIoc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem slice_abs_diff_le_uIoc {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |F x θ - F y θ| ≤ ∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ| := by
  -- `Set.uIcc y x` lies in the open half-line `(0,∞)`.
  have hsub : Set.uIcc y x ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    rw [Set.uIcc] at ht
    exact lt_of_lt_of_le (lt_min hy hx) ht.1
  -- The `z`-slice of `∂_z F` is continuous there, hence interval integrable.
  have hint : IntervalIntegrable (fun t : ℝ => Work.Spaces.pz F t θ) MeasureTheory.volume y x :=
    ((hsm.pz.curry_z hθ).continuousOn.mono hsub).intervalIntegrable
  -- The slice `z ↦ F z θ` has derivative `∂_z F` throughout `uIcc y x`.
  have hderiv : ∀ t ∈ Set.uIcc y x,
      HasDerivAt (fun z : ℝ => F z θ) (Work.Spaces.pz F t θ) t :=
    fun t ht => hsm.hasDerivAt_slice hθ (hsub ht)
  -- Fundamental theorem of calculus on the interval `[y,x]`.
  have hftc : ∫ t in y..x, Work.Spaces.pz F t θ = F x θ - F y θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← hftc]
  -- Triangle inequality for the integral, over the unordered interval.
  have h := intervalIntegral.norm_integral_le_integral_norm_uIoc
    (a := y) (b := x) (f := fun t : ℝ => Work.Spaces.pz F t θ) (μ := MeasureTheory.volume)
  simpa only [Real.norm_eq_abs] using h

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.slice_abs_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular slices of `F` and `∂_zF` are `L¹`

For a source `F` which is `C^∞` on the open quadrant `(0,∞) × (0,π/2)` and honest in the
weighted space `ℋ^1` (`Work.Spaces.HkMem α 1 F`), the two angular slices at any radius
`t > 0`,

  `θ ↦ |F t θ|`  and  `θ ↦ |∂_zF t θ|`,

are integrable on `Iθ = [0, π/2]`.

The route is the `i = 0` resp. `i = 1` summand of `HkIntegrand α 1 F`: on the open
quadrant the weight factor `w z / sin(2θ)^{η/2}` is `≥ 1`, so the weighted squares dominate
the plain squares,

  `(F t θ)² ≤ HkIntegrand α 1 F t θ`,   `(∂_zF t θ)² ≤ (1/t²)·HkIntegrand α 1 F t θ`,

and `HkMem α 1 F` makes the right hand sides integrable on the slice.  On the finite
measure space `Iθ` an `L²` function is `L¹`, via the pointwise bound `|x| ≤ x² + 1`.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Elementary weight facts on the open quadrant -/

/-- `Iθ = [0,π/2]` is measurable. -/
private lemma measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

/-- On the open quadrant the weight factor `w z / sin(2θ)^{η/2}` is `≥ 1`: `w z ≥ 1` for
`z > 0` and `sin(2θ)^{η/2} ≤ 1`. -/
private lemma one_le_wdiv {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have hw : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div hz2]
    exact pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsinpos _
  have hsle : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hsinpos) (Real.sin_le_one _) (by rw [Work.Spaces.eta]; norm_num)
  rw [one_le_div hspos]
  exact le_trans hsle hw

/-- Multiplying by a factor `A ≥ 1` does not decrease a square. -/
private lemma sq_le_sq_mul_of_one_le {x A : ℝ} (hA : 1 ≤ A) : x ^ 2 ≤ (x * A) ^ 2 := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have habs : |x| ≤ |x * A| := by
    rw [abs_mul, abs_of_nonneg hA0]
    exact le_mul_of_one_le_right (abs_nonneg _) hA
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) habs 2

/-- The plain square of a function is dominated by its weighted square on the open
quadrant. -/
private lemma sq_le_wdiv_sq {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (g z θ) ^ 2
      ≤ (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
  sq_le_sq_mul_of_one_le (one_le_wdiv hz hθ)

/-- On the finite measure space `Iθ` an `L²` function is `L¹`. -/
private lemma integrableOn_abs_of_sq {u : ℝ → ℝ}
    (hsq : IntegrableOn (fun θ : ℝ => (u θ) ^ 2) Work.Spaces.Iθ)
    (haesm : AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ)) :
    IntegrableOn (fun θ : ℝ => |u θ|) Work.Spaces.Iθ := by
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (C := (1 : ℝ)) (s := Work.Spaces.Iθ)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hdom : IntegrableOn (fun θ : ℝ => (u θ) ^ 2 + 1) Work.Spaces.Iθ := hsq.add hconst
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => |u θ|) (volume.restrict Work.Spaces.Iθ) := by
    simpa only [Real.norm_eq_abs] using haesm.norm
  refine MeasureTheory.Integrable.mono' hdom hmeas ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ (fun θ _ => ?_)
  rw [Real.norm_of_nonneg (abs_nonneg (u θ))]
  nlinarith [sq_abs (u θ), sq_nonneg (|u θ| - 1)]

/-- The `i = 1` summand of `HkIntegrand α 1 F` dominates `(∂_zF t θ)²` up to the constant
`1/t²`. -/
private lemma sq_pz_le_HkIntegrand {α t : ℝ} {F : ℝ → ℝ → ℝ} (ht : 0 < t) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.pz F t θ) ^ 2
      ≤ (1 / t ^ 2) * Work.Spaces.HkIntegrand α 1 F t θ := by
  have hDz : Work.Spaces.DzIter 1 F t θ = t * Work.Spaces.pz F t θ := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  have hstep : (Work.Spaces.DzIter 1 F t θ
      * (Work.Spaces.w t / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α 1 F t θ :=
    Work.Spaces.sq_le_HkIntegrand_z α 1 F t θ 1 (by norm_num)
  have hmono : (t * Work.Spaces.pz F t θ) ^ 2
      ≤ (Work.Spaces.DzIter 1 F t θ
          * (Work.Spaces.w t / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [hDz]
    exact sq_le_sq_mul_of_one_le (one_le_wdiv ht hθ)
  have hkey : t ^ 2 * (Work.Spaces.pz F t θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 F t θ := by
    have h1 : t ^ 2 * (Work.Spaces.pz F t θ) ^ 2 = (t * Work.Spaces.pz F t θ) ^ 2 := by ring
    rw [h1]
    exact le_trans hmono hstep
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have h3 : (1 / t ^ 2) * Work.Spaces.HkIntegrand α 1 F t θ
      = Work.Spaces.HkIntegrand α 1 F t θ / t ^ 2 := by ring
  rw [h3]
  exact (le_div_iff₀ ht2).mpr (by rw [mul_comm]; exact hkey)

/-! ## The main lemma -/

theorem slice_abs_integrable {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 1 F)
    {t : ℝ} (ht : 0 < t) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => |F t θ|) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ : ℝ => |Work.Spaces.pz F t θ|) Work.Spaces.Iθ := by
  have htIz : t ∈ Work.Spaces.Iz := Set.mem_Ici.mpr ht.le
  have hHk : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ) Work.Spaces.Iθ :=
    hF.1 t htIz
  -- `Iθ` and the open interval `(0,π/2)` differ by a null set
  have hmeq : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  -- a.e. strong measurability of the two slices, from smoothness on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hsm.continuousOn
  have haesmF : AEStronglyMeasurable (fun θ : ℝ => F t θ) (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => F p.1 p.2) hcont ht
  have haesmP : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.pz F t θ)
      (volume.restrict Work.Spaces.Iθ) := by
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using
      hsm.aesm_slice_pzIter 1 ht
  -- the square of the `F`-slice is integrable, dominated by the `ℋ^1`-integrand
  have hsqF : IntegrableOn (fun θ : ℝ => (F t θ) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' hHk (haesmF.pow 2) ?_
    rw [hmeq]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact le_trans (sq_le_wdiv_sq ht hθ)
      (Work.Spaces.sq_le_HkIntegrand_z α 1 F t θ 0 (by norm_num))
  -- the square of the `∂_zF`-slice is integrable
  have hsqP : IntegrableOn (fun θ : ℝ => (Work.Spaces.pz F t θ) ^ 2) Work.Spaces.Iθ := by
    have hdom : IntegrableOn (fun θ : ℝ => (1 / t ^ 2) * Work.Spaces.HkIntegrand α 1 F t θ)
        Work.Spaces.Iθ := hHk.const_mul _
    refine MeasureTheory.Integrable.mono' hdom (haesmP.pow 2) ?_
    rw [hmeq]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact sq_pz_le_HkIntegrand ht hθ
  exact ⟨integrableOn_abs_of_sq hsqF haesmF, integrableOn_abs_of_sq hsqP haesmP⟩

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.SmoothAux.contDiffOn_of_families_nat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Filter

namespace Work.FTS.PhiStar.Series.SmoothAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The criterion `C^{n+1}` from `C^n` partial derivatives -/

/-- The continuous linear map `(x, y) ↦ ((a, b) ↦ a * x + b * y)` from `ℝ²` to `ℝ² →L[ℝ] ℝ`;
it is the total derivative of a function whose partial derivatives at the point are `x` and `y`. -/
def cclm : ℝ × ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ) :=
  (((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ))
  + (((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℝ))

lemma cclm_apply (p z : ℝ × ℝ) : cclm p z = z.1 * p.1 + z.2 * p.2 := by
  obtain ⟨x, y⟩ := p
  obtain ⟨a, b⟩ := z
  simp only [cclm, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  rfl

lemma cclm_eq (x y : ℝ) :
    cclm (x, y) = (ContinuousLinearMap.toSpanSingleton ℝ x).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ y) := by
  apply ContinuousLinearMap.ext
  intro z
  obtain ⟨a, b⟩ := z
  simp only [cclm_apply, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  ring

/-- **`C¹` from continuous partial derivatives.**  On an open set `U`, if both slice derivatives of
`f` exist everywhere on `U` and the corresponding partial-derivative functions `g`, `h` are
continuous on `U`, then `uncurry f` is differentiable at every point of `U`, with derivative the
continuous linear map whose matrix is `(g p, h p)`. -/
theorem hasFDerivAt_of_hasDerivAt_slices {f g h : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hg : ContinuousOn (Function.uncurry g) U)
    (hh : ContinuousOn (Function.uncurry h) U)
    (hz : ∀ (z θ : ℝ), (z, θ) ∈ U → HasDerivAt (fun z' => f z' θ) (g z θ) z)
    (hθ : ∀ (z θ : ℝ), (z, θ) ∈ U → HasDerivAt (fun θ' => f z θ') (h z θ) θ) :
    ∀ p ∈ U, HasFDerivAt (Function.uncurry f) (cclm (g p.1 p.2, h p.1 p.2)) p := by
  intro p hp
  have hcts : Continuous fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous
  have hdf₁ : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun z' => f z' v.2)
      (Function.uncurry (fun a b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (g a b)) v) v.1 :=
    mem_of_superset (hU.mem_nhds hp) fun v hv => (hz v.1 v.2 hv).hasFDerivAt
  have hdf₂ : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun θ' => f v.1 θ')
      (Function.uncurry (fun a b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (h a b)) v) v.2 :=
    mem_of_superset (hU.mem_nhds hp) fun v hv => (hθ v.1 v.2 hv).hasFDerivAt
  have hc₁ : ContinuousAt
      (Function.uncurry (fun a b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (g a b))) p :=
    hcts.continuousAt.comp (hg.continuousAt (hU.mem_nhds hp))
  have hc₂ : ContinuousAt
      (Function.uncurry (fun a b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (h a b))) p :=
    hcts.continuousAt.comp (hh.continuousAt (hU.mem_nhds hp))
  have hmain := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := p) (f := f)
    (f₁ := fun a b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (g a b))
    (f₂ := fun a b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (h a b))
    hdf₁ hdf₂ hc₁ hc₂
  refine hmain.hasFDerivAt.congr_fderiv ?_
  show (ContinuousLinearMap.toSpanSingleton ℝ (g p.1 p.2)).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ (h p.1 p.2)) = cclm (g p.1 p.2, h p.1 p.2)
  rw [cclm_eq]

/-- **`C^{n+1}` from `C^n` partial derivatives.**  If the two slice derivatives of `f` are given
pointwise on the open set `U` by the functions `g`, `h` and both of these are `C^n` on `U`, then
`f` is `C^{n+1}` on `U`. -/
theorem contDiffOn_succ_of_partials {f g h : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {n : ℕ}
    (hz : ∀ (z θ : ℝ), (z, θ) ∈ U → HasDerivAt (fun z' => f z' θ) (g z θ) z)
    (hθ : ∀ (z θ : ℝ), (z, θ) ∈ U → HasDerivAt (fun θ' => f z θ') (h z θ) θ)
    (hg : ContDiffOn ℝ n (Function.uncurry g) U)
    (hh : ContDiffOn ℝ n (Function.uncurry h) U) :
    ContDiffOn ℝ (n + 1) (Function.uncurry f) U := by
  have hF' : ∀ p ∈ U, HasFDerivAt (Function.uncurry f) (cclm (g p.1 p.2, h p.1 p.2)) p :=
    hasFDerivAt_of_hasDerivAt_slices hU hg.continuousOn hh.continuousOn hz hθ
  refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).2 ?_
  refine ⟨fun hn => absurd hn (by simp), fun p => cclm (g p.1 p.2, h p.1 p.2), ?_, ?_⟩
  · exact cclm.contDiff.comp_contDiffOn (hg.prodMk hh)
  · intro p hp
    exact (hF' p hp).hasFDerivWithinAt

/-! ## The corrected bootstrap -/


end Work.FTS.PhiStar.Series.SmoothAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.StarPkgo2Aux.ZeroOffFields =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.StarPkgo2Aux

set_option autoImplicit false

/-! ## A function vanishing on a half-line has zero derivative at the junction -/

/-- If `g` vanishes on `(-∞,a]`, then `deriv g a = 0`. -/
theorem zof_deriv_eq_zero_of_eqOn_Iic {g : ℝ → ℝ} {a : ℝ} (h : ∀ x : ℝ, x ≤ a → g x = 0) :
    deriv g a = 0 := by
  by_cases hd : DifferentiableAt ℝ g a
  · have ht : Tendsto (slope g a) (𝓝[Set.Iio a] a) (𝓝 (deriv g a)) :=
      hd.hasDerivAt.tendsto_slope.mono_left (nhdsWithin_mono a (fun z hz => ne_of_lt hz))
    have h0 : (fun z : ℝ => slope g a z) =ᶠ[𝓝[Set.Iio a] a] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [slope_def_field]
      rw [h z (le_of_lt hz), h a le_rfl]
      simp
    exact tendsto_nhds_unique (ht.congr' h0) tendsto_const_nhds
  · exact deriv_zero_of_not_differentiableAt hd

/-- If `g` vanishes on `[a,∞)`, then `deriv g a = 0`. -/
theorem zof_deriv_eq_zero_of_eqOn_Ici {g : ℝ → ℝ} {a : ℝ} (h : ∀ x : ℝ, a ≤ x → g x = 0) :
    deriv g a = 0 := by
  by_cases hd : DifferentiableAt ℝ g a
  · have ht : Tendsto (slope g a) (𝓝[Set.Ioi a] a) (𝓝 (deriv g a)) :=
      hd.hasDerivAt.tendsto_slope.mono_left (nhdsWithin_mono a (fun z hz => ne_of_gt hz))
    have h0 : (fun z : ℝ => slope g a z) =ᶠ[𝓝[Set.Ioi a] a] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [slope_def_field]
      rw [h z (le_of_lt hz), h a le_rfl]
      simp
    exact tendsto_nhds_unique (ht.congr' h0) tendsto_const_nhds
  · exact deriv_zero_of_not_differentiableAt hd

/-! ## The two partial derivatives of a function vanishing off `Q0` -/

/-- `∂_zΨ = 0` at every point off the open quadrant. -/
theorem zof_pz_eq_zero (Ψ : ℝ → ℝ → ℝ)
    (hZ : ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → Ψ z θ = 0) :
    ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → Work.Spaces.pz Ψ z θ = 0 := by
  intro z θ h
  rw [Work.Spaces.pz]
  rcases lt_trichotomy z 0 with hz | hz | hz
  · -- `z < 0`: the `z`-slice vanishes on the neighbourhood `(-∞,0)` of `z`
    have hfe : (fun z' : ℝ => Ψ z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hz] with z' hz'
      exact hZ z' θ (fun hmem =>
        absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).1 (not_lt.mpr (le_of_lt hz')))
    rw [hfe.deriv_eq, deriv_const]
  · -- `z = 0`: the `z`-slice vanishes on `(-∞,0]`
    subst hz
    exact zof_deriv_eq_zero_of_eqOn_Iic (fun x hx => hZ x θ (fun hmem =>
      absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).1 (not_lt.mpr hx)))
  · -- `z > 0`: then `θ ∉ (0,π/2)`, so the *whole* `z`-slice of `Ψ` vanishes
    have hfun : (fun z' : ℝ => Ψ z' θ) = fun _ => (0 : ℝ) := by
      funext z'
      exact hZ z' θ (fun hmem =>
        h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.1,
          (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.2⟩))
    rw [hfun, deriv_const]

/-- `∂_θΨ = 0` at every point off the open quadrant. -/
theorem zof_pth_eq_zero (Ψ : ℝ → ℝ → ℝ)
    (hZ : ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → Ψ z θ = 0) :
    ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → Work.Spaces.pth Ψ z θ = 0 := by
  intro z θ h
  rw [Work.Spaces.pth]
  by_cases hz : z ≤ 0
  · -- `z ≤ 0`: the whole `θ`-slice vanishes
    have hfun : (fun θ' : ℝ => Ψ z θ') = fun _ => (0 : ℝ) := by
      funext θ'
      exact hZ z θ' (fun hmem =>
        absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).1 (not_lt.mpr hz))
    rw [hfun, deriv_const]
  · have hz' : (0 : ℝ) < z := not_le.mp hz
    rcases lt_trichotomy θ 0 with hθ | hθ | hθ
    · -- `θ < 0`: the `θ`-slice vanishes on the neighbourhood `(-∞,0)` of `θ`
      have hfe : (fun θ' : ℝ => Ψ z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Iio.mem_nhds hθ] with θ' hθ'
        exact hZ z θ' (fun hmem =>
          absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.1 (not_lt.mpr (le_of_lt hθ')))
      rw [hfe.deriv_eq, deriv_const]
    · -- `θ = 0`: the `θ`-slice vanishes on `(-∞,0]`
      subst hθ
      exact zof_deriv_eq_zero_of_eqOn_Iic (fun y hy => hZ z y (fun hmem =>
        absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.1 (not_lt.mpr hy)))
    · -- `θ > 0`: with `z > 0` and `(z,θ) ∉ Q0` we get `π/2 ≤ θ`
      have hpi : Real.pi / 2 ≤ θ := by
        by_contra hcon
        exact h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ, not_le.mp hcon⟩)
      rcases lt_trichotomy θ (Real.pi / 2) with h2 | h2 | h2
      · exact absurd hpi (not_le.mpr h2)
      · -- `θ = π/2`: the `θ`-slice vanishes on `[π/2,∞)`
        subst h2
        exact zof_deriv_eq_zero_of_eqOn_Ici (fun y hy => hZ z y (fun hmem =>
          absurd hy (not_le.mpr (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.2)))
      · -- `θ > π/2`: the `θ`-slice vanishes on the neighbourhood `(π/2,∞)` of `θ`
        have hfe : (fun θ' : ℝ => Ψ z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Ioi.mem_nhds h2] with θ' hθ'
          exact hZ z θ' (fun hmem =>
            absurd (Work.FTS.EllipticEst.mem_Q0.mp hmem).2.2 (not_lt.mpr (le_of_lt hθ')))
        rw [hfe.deriv_eq, deriv_const]

/-! ## The target -/

theorem ZeroOffFields (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hZ : ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → Ψ z θ = 0) :
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 →
      (z + 1) / z * Work.Construction.Rop α Ψ z θ = 0) ∧
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → Work.Construction.Vop Ψ z θ = 0) ∧
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 →
      (z + 1) / z * Work.Construction.Vop Ψ z θ = 0) ∧
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 →
      Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ = 0) ∧
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 →
      (z + 1) / z * (Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ) = 0) := by
  have hpz := zof_pz_eq_zero Ψ hZ
  have hpth := zof_pth_eq_zero Ψ hZ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z θ h
    have h1 := hZ z θ h
    have h2 := hpz z θ h
    have h3 := hpth z θ h
    simp only [Work.Construction.Rop, h1, h2, h3]
    ring
  · intro z θ h
    have h1 := hZ z θ h
    have h3 := hpth z θ h
    simp only [Work.Construction.Vop, h1, h3]
    ring
  · intro z θ h
    have h1 := hZ z θ h
    have h3 := hpth z θ h
    simp only [Work.Construction.Vop, h1, h3]
    ring
  · intro z θ h
    have h1 := hZ z θ h
    have h2 := hpz z θ h
    simp only [Work.Construction.Uop, h1, h2]
    ring
  · intro z θ h
    have h1 := hZ z θ h
    have h2 := hpz z θ h
    simp only [Work.Construction.Uop, h1, h2]
    ring

end Work.FTS.PhiStar.StarPkgo2Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.iterSmooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Filter Set

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false

/-- `∂_z` costs one order of differentiability. -/
theorem contDiffOn_uncurry_pz_succ {n : ℕ∞ω} {V : Set (ℝ × ℝ)} {G : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hdiff : ∀ p ∈ V, DifferentiableAt ℝ (Function.uncurry G) p := fun p hp =>
    (h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp)
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := n) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr (fun p hp => Work.Spaces.pz_eq_fderiv (hdiff p hp))

/-- `∂_θ` costs one order of differentiability. -/
theorem contDiffOn_uncurry_pth_succ {n : ℕ∞ω} {V : Set (ℝ × ℝ)} {G : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hdiff : ∀ p ∈ V, DifferentiableAt ℝ (Function.uncurry G) p := fun p hp =>
    (h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp)
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := n) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr (fun p hp => Work.Spaces.pth_eq_fderiv (hdiff p hp))

/-- `D_z = z ∂_z` costs one order of differentiability. -/
theorem contDiffOn_uncurry_Dz_succ {n : ℕ∞ω} {V : Set (ℝ × ℝ)} {G : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dz G)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact (contDiffOn_fst).mul (contDiffOn_uncurry_pz_succ hV h)

/-- `D_θ = sin(2θ) ∂_θ` costs one order of differentiability. -/
theorem contDiffOn_uncurry_Dth_succ {n : ℕ∞ω} {V : Set (ℝ × ℝ)} {G : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dth G)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  exact hsin.mul (contDiffOn_uncurry_pth_succ hV h)


end Work.FTS.StrongEps.E5Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.continuousOn_uncurry_transport =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

/-- **The angular transport `3 sin(2θ) ∂_θf/(1+z)` is jointly continuous on the open
quadrant.**

`Transport f z θ = 3 D_θf(z,θ)/(1+z)` is the product of the continuous factor
`3 sin(2θ)/(1+z)` with the angular partial `∂_θf`.  The latter is continuous on `Q0` as soon
as `f` is `C¹` there: on the open quadrant the slice derivative `∂_θf` agrees with the
Fréchet derivative of `uncurry f` applied to the direction `(0,1)`, and the Fréchet
derivative of a `C¹` function on an open set is continuous.  Combined with the stability of
`∂_θ` inside `SmoothOpen` (`SmoothOpen.pth`) this gives the claim for every `SmoothOpen f`. -/
theorem continuousOn_uncurry_transport {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (Function.uncurry (Work.Coercivity.Transport f)) Work.FTS.EllipticEst.Q0 := by
  have hpth : ContinuousOn (Function.uncurry (Work.Spaces.pth f)) Work.FTS.EllipticEst.Q0 :=
    (h.pth).continuousOn
  have hsin : ContinuousOn (fun p : ℝ × ℝ => 3 * Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd))).continuousOn
  have hden : ContinuousOn (fun p : ℝ × ℝ => 1 + p.1) Work.FTS.EllipticEst.Q0 :=
    (continuous_const.add continuous_fst).continuousOn
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, (1 + p.1) ≠ 0 := by
    intro p hp
    have hp1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    exact ne_of_gt (by linarith)
  have hmain := (hsin.mul hpth).div hden hne
  refine hmain.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry_apply_pair, Work.Coercivity.Transport, Work.Spaces.Dth,
    Pi.mul_apply, Pi.div_apply]
  ring

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.prof_cont_ops =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false

/-- **`∂_z` of a `C¹` datum is continuous.**  On an open set `V`, the slicewise `z`-partial
`Work.Spaces.pz G` is continuous as soon as `G` is jointly `C¹` on `V`. -/
theorem continuousOn_uncurry_pz_of_contDiffOn_one {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ 1 (Function.uncurry G) V) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz G p.1 p.2) V := by
  have hdiff : ∀ p ∈ V, DifferentiableAt ℝ (Function.uncurry G) p := fun p hp =>
    (h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp)
  have hfd : ContDiffOn ℝ 0 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := (0 : WithTop ℕ∞)) hV.uniqueDiffOn (by norm_num)
    exact h'.congr (fun p hp => (fderivWithin_of_isOpen hV hp).symm)
  have hcomp : ContinuousOn (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    (hfd.clm_apply contDiffOn_const).continuousOn
  exact hcomp.congr (fun p hp => Work.Spaces.pz_eq_fderiv (hdiff p hp))

/-- **`∂_θ` of a `C¹` datum is continuous.**  On an open set `V`, the slicewise `θ`-partial
`Work.Spaces.pth G` is continuous as soon as `G` is jointly `C¹` on `V`. -/
theorem continuousOn_uncurry_pth_of_contDiffOn_one {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ 1 (Function.uncurry G) V) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth G p.1 p.2) V := by
  have hdiff : ∀ p ∈ V, DifferentiableAt ℝ (Function.uncurry G) p := fun p hp =>
    (h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp)
  have hfd : ContDiffOn ℝ 0 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := (0 : WithTop ℕ∞)) hV.uniqueDiffOn (by norm_num)
    exact h'.congr (fun p hp => (fderivWithin_of_isOpen hV hp).symm)
  have hcomp : ContinuousOn (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    (hfd.clm_apply contDiffOn_const).continuousOn
  exact hcomp.congr (fun p hp => Work.Spaces.pth_eq_fderiv (hdiff p hp))

/-- The angular factor `cos θ` does not vanish on the open quadrant. -/
theorem cos_ne_zero_of_mem_Q0 :
    ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
  intro p hp
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)

/-- `tan θ` is continuous on the open quadrant. -/
theorem continuousOn_tan_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 := by
  have h := Real.continuousOn_tan.comp continuousOn_snd
    (fun p hp => cos_ne_zero_of_mem_Q0 p hp)
  simpa only [Function.comp_def] using h

theorem prof_cont_ops {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 1 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Function.uncurry (Work.Construction.Rop α Ψ)) Work.FTS.EllipticEst.Q0 ∧
    ContinuousOn (Function.uncurry (Work.Construction.Uop α Ψ)) Work.FTS.EllipticEst.Q0 ∧
    ContinuousOn (Function.uncurry (Work.Construction.Vop Ψ)) Work.FTS.EllipticEst.Q0 := by
  have hV : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have hΨc : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hΨ.continuousOn
  have hpz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    continuousOn_uncurry_pz_of_contDiffOn_one hV hΨ
  have hpth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth Ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    continuousOn_uncurry_pth_of_contDiffOn_one hV hΨ
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    Real.continuous_sin.comp_continuousOn continuousOn_snd
  have hcos : ContinuousOn (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    Real.continuous_cos.comp_continuousOn continuousOn_snd
  have htan : ContinuousOn (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 :=
    continuousOn_tan_Q0
  refine ⟨?_, ?_, ?_⟩
  · -- `ℛ(Ψ) = (2 sin θ · Ψ + α sin θ · z ∂_zΨ + cos θ · ∂_θΨ)/cos θ`
    show ContinuousOn (fun p : ℝ × ℝ => (2 * Real.sin p.2 * Ψ p.1 p.2
        + α * Real.sin p.2 * p.1 * Work.Spaces.pz Ψ p.1 p.2
        + Real.cos p.2 * Work.Spaces.pth Ψ p.1 p.2) / Real.cos p.2)
        Work.FTS.EllipticEst.Q0
    refine ContinuousOn.div ?_ hcos cos_ne_zero_of_mem_Q0
    refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
    · exact ContinuousOn.mul (ContinuousOn.mul continuousOn_const hsin) hΨc
    · exact ContinuousOn.mul
        (ContinuousOn.mul (ContinuousOn.mul continuousOn_const hsin) continuousOn_fst) hpz
    · exact ContinuousOn.mul hcos hpth
  · -- `U(Ψ) = -3Ψ - α z ∂_zΨ`
    show ContinuousOn (fun p : ℝ × ℝ =>
        -3 * Ψ p.1 p.2 - α * p.1 * Work.Spaces.pz Ψ p.1 p.2) Work.FTS.EllipticEst.Q0
    refine ContinuousOn.sub (ContinuousOn.mul continuousOn_const hΨc) ?_
    exact ContinuousOn.mul (ContinuousOn.mul continuousOn_const continuousOn_fst) hpz
  · -- `V(Ψ) = ∂_θΨ - tan θ · Ψ`
    show ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth Ψ p.1 p.2 - Real.tan p.2 * Ψ p.1 p.2) Work.FTS.EllipticEst.Q0
    exact ContinuousOn.sub hpth (ContinuousOn.mul htan hΨc)

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux3.AngSlicePairLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux3

set_option maxHeartbeats 800000


end Work.FTS.StrongEps.E5Aux3
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.HkIntegrand_intervalIntegral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# `HkIntegrand` versus the interval integral in the parameter `s`

`Work.FTS.StrongEps.E5G.HkIntegrand_intervalIntegral_le` is the pointwise-in-`(z,θ)`
Cauchy–Schwarz ("Jensen") step of the `slice_lip_HkSq` route: if every slot
`D_z^j D_θ^i (H s) z θ` of the family `s ↦ H s` is measurable and bounded by `C` on
`uIoc a b`, and if the slots of the primitive `∫_s H s` are the integrals of the slots
(the exchange identity `hid`), then

`HkIntegrand α 4 (∫_s H s) z θ ≤ (b - a) · ∫_s HkIntegrand α 4 (H s) z θ`.

The proof is Cauchy–Schwarz in `s` slot by slot: each slot of `HkIntegrand α 4 (∫_s H s)`
is `W · ∫_s (slot of H s)`, whose square is `(∫_s φ)^2 ≤ (b - a) ∫_s φ^2`; summing over the
finitely many slots and using that the sum of the squares of the slots of `H s` is exactly
`HkIntegrand α 4 (H s) z θ` gives the claim.

Everything here is `sorry`-free.
-/

/-! ## Cauchy–Schwarz for the interval integral -/

/-- **Jensen/Cauchy–Schwarz for the interval integral.**
For `a ≤ b` and `f` with `f` and `f²` interval integrable on `[a,b]`,
`(∫_a^b f)² ≤ (b-a) · ∫_a^b f²`. -/
theorem intervalIntegral_sq_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun s => f s ^ 2) volume a b) :
    (∫ s in a..b, f s) ^ 2 ≤ (b - a) * ∫ s in a..b, (f s) ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    simp
  have hba : 0 < b - a := sub_pos.mpr h
  set M : ℝ := ∫ s in a..b, f s with hM
  have hint : IntervalIntegrable (fun s => (f s - M / (b - a)) ^ 2) volume a b := by
    have h1 : IntervalIntegrable
        (fun s => f s ^ 2 - 2 * (M / (b - a)) * f s + (M / (b - a)) ^ 2) volume a b :=
      (hf2.sub (hf.const_mul (2 * (M / (b - a))))).add intervalIntegrable_const
    refine h1.congr_ae (Filter.Eventually.of_forall fun s => ?_)
    ring
  have hnn : 0 ≤ ∫ s in a..b, (f s - M / (b - a)) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun s _ => sq_nonneg _
  have hcongr : (∫ s in a..b, (f s - M / (b - a)) ^ 2)
      = ∫ s in a..b, (f s ^ 2 - 2 * (M / (b - a)) * f s + (M / (b - a)) ^ 2) :=
    intervalIntegral.integral_congr (fun s _ => by ring)
  have hcalc : (∫ s in a..b, (f s ^ 2 - 2 * (M / (b - a)) * f s + (M / (b - a)) ^ 2))
      = (∫ s in a..b, f s ^ 2) - M ^ 2 / (b - a) := by
    rw [intervalIntegral.integral_add (hf2.sub (hf.const_mul (2 * (M / (b - a)))))
          intervalIntegrable_const,
        intervalIntegral.integral_sub hf2 (hf.const_mul (2 * (M / (b - a)))),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, hM]
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hcongr, hcalc] at hnn
  have h3 : M ^ 2 / (b - a) ≤ ∫ s in a..b, f s ^ 2 := by linarith
  have h4 : M ^ 2 ≤ (∫ s in a..b, f s ^ 2) * (b - a) := (div_le_iff₀ hba).mp h3
  rw [hM]
  calc (∫ s in a..b, f s) ^ 2 ≤ (∫ s in a..b, f s ^ 2) * (b - a) := h4
    _ = (b - a) * ∫ s in a..b, f s ^ 2 := by ring

/-- **Cauchy–Schwarz for a finite sum of slots.** -/
theorem finset_sum_sq_intervalIntegral_le {ι : Type*} (S : Finset ι) (F : ι → ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ i ∈ S, IntervalIntegrable (F i) volume a b)
    (hF2 : ∀ i ∈ S, IntervalIntegrable (fun s => F i s ^ 2) volume a b) :
    ∑ i ∈ S, (∫ s in a..b, F i s) ^ 2 ≤ (b - a) * ∫ s in a..b, ∑ i ∈ S, (F i s) ^ 2 := by
  calc ∑ i ∈ S, (∫ s in a..b, F i s) ^ 2
      ≤ ∑ i ∈ S, (b - a) * ∫ s in a..b, (F i s) ^ 2 :=
        Finset.sum_le_sum fun i hi => intervalIntegral_sq_le hab (hF i hi) (hF2 i hi)
    _ = (b - a) * ∑ i ∈ S, ∫ s in a..b, (F i s) ^ 2 := by rw [Finset.mul_sum]
    _ = (b - a) * ∫ s in a..b, ∑ i ∈ S, (F i s) ^ 2 := by
        rw [intervalIntegral.integral_finsetSum (fun i hi => hF2 i hi)]

/-- **Cauchy–Schwarz for a doubly indexed finite family of slots.** -/
theorem double_sum_sq_intervalIntegral_le (S T : Finset ℕ) (F : ℕ → ℕ → ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ i ∈ S, ∀ j ∈ T, IntervalIntegrable (F i j) volume a b)
    (hF2 : ∀ i ∈ S, ∀ j ∈ T, IntervalIntegrable (fun s => F i j s ^ 2) volume a b) :
    ∑ i ∈ S, ∑ j ∈ T, (∫ s in a..b, F i j s) ^ 2
      ≤ (b - a) * ∫ s in a..b, ∑ i ∈ S, ∑ j ∈ T, (F i j s) ^ 2 := by
  have hstep : ∀ i ∈ S, IntervalIntegrable (fun s => ∑ j ∈ T, (F i j s) ^ 2) volume a b :=
    fun i hi => by
      have h1 := IntervalIntegrable.sum T (f := fun j s => (F i j s) ^ 2)
        (fun j hj => hF2 i hi j hj)
      rwa [show (∑ j ∈ T, fun s => (F i j s) ^ 2) = fun s => ∑ j ∈ T, (F i j s) ^ 2 from
        funext fun s => Finset.sum_apply s T (fun j s => (F i j s) ^ 2)] at h1
  calc ∑ i ∈ S, ∑ j ∈ T, (∫ s in a..b, F i j s) ^ 2
      ≤ ∑ i ∈ S, (b - a) * ∫ s in a..b, ∑ j ∈ T, (F i j s) ^ 2 :=
        Finset.sum_le_sum fun i hi => finset_sum_sq_intervalIntegral_le T (F i) hab
          (fun j hj => hF i hi j hj) (fun j hj => hF2 i hi j hj)
    _ = (b - a) * ∑ i ∈ S, ∫ s in a..b, ∑ j ∈ T, (F i j s) ^ 2 := by rw [Finset.mul_sum]
    _ = (b - a) * ∫ s in a..b, ∑ i ∈ S, ∑ j ∈ T, (F i j s) ^ 2 := by
        rw [intervalIntegral.integral_finsetSum (f := fun i s => ∑ j ∈ T, (F i j s) ^ 2) hstep]

/-- A finite sum of interval-integrable functions is interval-integrable (uncurried form). -/
theorem intervalIntegrable_finsetSum {ι : Type*} (S : Finset ι) (F : ι → ℝ → ℝ) {a b : ℝ}
    (h : ∀ i ∈ S, IntervalIntegrable (F i) volume a b) :
    IntervalIntegrable (fun s => ∑ i ∈ S, F i s) volume a b := by
  have h1 := IntervalIntegrable.sum S (f := F) h
  rwa [show (∑ i ∈ S, F i) = fun s => ∑ i ∈ S, F i s from
    funext fun s => Finset.sum_apply s S F] at h1

/-- The main estimate. -/
theorem HkIntegrand_intervalIntegral_le {α a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    {H : ℝ → ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hmeas : ∀ (j i : ℕ), j + i ≤ 4 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.uIoc a b)))
    (hbdd : ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.uIoc a b,
      |Work.Spaces.mixed j i (H s) z θ| ≤ C)
    (hid : ∀ j i : ℕ, j + i ≤ 4 →
      Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ) :
    Work.Spaces.HkIntegrand α 4 (fun z θ => ∫ s in a..b, H s z θ) z θ
      ≤ (b - a) * ∫ s in a..b, Work.Spaces.HkIntegrand α 4 (H s) z θ := by
  set G : ℝ → ℝ → ℝ := fun z θ => ∫ s in a..b, H s z θ
  set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hW
  have hvol : volume (Set.uIoc a b) < ⊤ := by
    rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
  -- slot integrability, from measurability and the uniform bound on `uIoc a b`
  have hslot : ∀ (j i : ℕ), j + i ≤ 4 →
      IntervalIntegrable (fun s => Work.Spaces.mixed j i (H s) z θ) volume a b := by
    intro j i hji
    refine intervalIntegrable_iff.mpr ?_
    refine MeasureTheory.IntegrableOn.of_bound hvol (hmeas j i hji) C ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
    simpa [Real.norm_eq_abs] using hbdd j i hji s hs
  have hslot2 : ∀ (j i : ℕ), j + i ≤ 4 → ∀ c : ℝ,
      IntervalIntegrable (fun s => (Work.Spaces.mixed j i (H s) z θ * c) ^ 2) volume a b := by
    intro j i hji c
    refine intervalIntegrable_iff.mpr ?_
    refine MeasureTheory.IntegrableOn.of_bound hvol
      (((hmeas j i hji).mul_const c).pow 2) ((C * |c|) ^ 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
    have hb1 := hbdd j i hji s hs
    have hb2 : |Work.Spaces.mixed j i (H s) z θ * c| ≤ C * |c| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb1 (abs_nonneg c)
    rw [Real.norm_eq_abs, abs_sq]
    calc (Work.Spaces.mixed j i (H s) z θ * c) ^ 2
        = |Work.Spaces.mixed j i (H s) z θ * c| ^ 2 := (sq_abs _).symm
      _ ≤ (C * |c|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb2 2
  -- unfolding `HkIntegrand α 4 G z θ` into its two blocks
  have hId : Work.Spaces.HkIntegrand α 4 G z θ
      = (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i G z θ * W) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    rw [Work.Spaces.HkIntegrand, hW]
  -- the `D_z`-block
  have hPart1 : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i G z θ * W) ^ 2)
      ≤ (b - a) * ∫ s in a..b, ∑ i ∈ Finset.range 5,
          (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2 := by
    refine le_of_eq_of_le ?_ (finset_sum_sq_intervalIntegral_le (Finset.range 5)
      (fun i s => Work.Spaces.mixed i 0 (H s) z θ * W) hab ?_ ?_)
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi4 : i + 0 ≤ 4 := by have := Finset.mem_range.mp hi; omega
      rw [show Work.Spaces.DzIter i G z θ = ∫ s in a..b, Work.Spaces.mixed i 0 (H s) z θ
        from hid i 0 hi4]
      rw [intervalIntegral.integral_mul_const]
    · intro i hi
      have hi4 : i + 0 ≤ 4 := by have := Finset.mem_range.mp hi; omega
      exact (hslot i 0 hi4).mul_const W
    · intro i hi
      have hi4 : i + 0 ≤ 4 := by have := Finset.mem_range.mp hi; omega
      exact hslot2 i 0 hi4 W
  -- integrability of the mixed slots, in the "`if` inside the square" form
  have hF5 : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      IntervalIntegrable (fun s => if 1 ≤ i ∧ i + j ≤ 4 then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) volume a b := by
    intro i hi j hj
    by_cases h : 1 ≤ i ∧ i + j ≤ 4
    · have hfe : (fun s => if 1 ≤ i ∧ i + j ≤ 4 then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0)
          = fun s => Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ :=
        funext fun s => ite_eq_left h
      rw [hfe]
      have hij : j + i ≤ 4 := by omega
      exact (hslot j i hij).mul_const _
    · have hfe : (fun s => if 1 ≤ i ∧ i + j ≤ 4 then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) = fun _ => 0 :=
        funext fun s => ite_eq_right h
      rw [hfe]; exact intervalIntegrable_const
  have hF5sq : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      IntervalIntegrable (fun s => (if 1 ≤ i ∧ i + j ≤ 4 then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2) volume a b := by
    intro i hi j hj
    by_cases h : 1 ≤ i ∧ i + j ≤ 4
    · have hfe : (fun s => (if 1 ≤ i ∧ i + j ≤ 4 then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
          = fun s => (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 :=
        funext fun s => by rw [ite_eq_left h]
      rw [hfe]
      have hij : j + i ≤ 4 := by omega
      exact hslot2 j i hij _
    · have hfe : (fun s => (if 1 ≤ i ∧ i + j ≤ 4 then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2) = fun _ => 0 :=
        funext fun s => by rw [ite_eq_right h]; ring
      rw [hfe]; exact intervalIntegrable_const
  -- the mixed block
  have hPart2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (b - a) * ∫ s in a..b, ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2 := by
    have hmain := double_sum_sq_intervalIntegral_le (Finset.range 5) (Finset.range 5)
      (fun i j s => if 1 ≤ i ∧ i + j ≤ 4 then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) hab hF5 hF5sq
    have hL : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (∫ s in a..b, if 1 ≤ i ∧ i + j ≤ 4 then
              Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2 := by
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
      by_cases h : 1 ≤ i ∧ i + j ≤ 4
      · have hij : j + i ≤ 4 := by omega
        simp only [ite_eq_left h]
        rw [intervalIntegral.integral_mul_const, ← hid j i hij]
      · simp only [ite_eq_right h]
        simp
    rw [hL]
    exact hmain
  -- the slots of the family `H s` recombine into `HkIntegrand α 4 (H s) z θ`
  have hT : ∀ s : ℝ,
      (∑ i ∈ Finset.range 5, (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2
      = Work.Spaces.HkIntegrand α 4 (H s) z θ := by
    intro s
    have h1 : (∑ i ∈ Finset.range 5, (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
        = ∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (H s) z θ * W) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by simp only [Work.Spaces.mixed_zero_right]
    have h2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
        = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases h : 1 ≤ i ∧ i + j ≤ 4
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h]; ring
    rw [h1, h2, Work.Spaces.HkIntegrand, hW]
  have hT1int : IntervalIntegrable (fun s => ∑ i ∈ Finset.range 5,
      (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2) volume a b :=
    intervalIntegrable_finsetSum (Finset.range 5)
      (fun i s => (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
      (fun i hi => by
        have hi4 : i + 0 ≤ 4 := by have := Finset.mem_range.mp hi; omega
        exact hslot2 i 0 hi4 W)
  have hT2int : IntervalIntegrable (fun s => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2) volume a b :=
    intervalIntegrable_finsetSum (Finset.range 5)
      (fun i s => ∑ j ∈ Finset.range 5, (if 1 ≤ i ∧ i + j ≤ 4 then
        Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
      (fun i hi => intervalIntegrable_finsetSum (Finset.range 5)
        (fun j s => (if 1 ≤ i ∧ i + j ≤ 4 then
          Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
        (fun j hj => hF5sq i hi j hj))
  have hTint : (∫ s in a..b, ∑ i ∈ Finset.range 5, (Work.Spaces.mixed i 0 (H s) z θ * W) ^ 2)
      + (∫ s in a..b, ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ else 0) ^ 2)
      = ∫ s in a..b, Work.Spaces.HkIntegrand α 4 (H s) z θ := by
    rw [← intervalIntegral.integral_add hT1int hT2int]
    exact intervalIntegral.integral_congr (fun s _ => hT s)
  rw [hId]
  refine le_trans (add_le_add hPart1 hPart2) ?_
  rw [← hTint]
  exact le_of_eq (by ring)

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.hasFDerivAt_of_slot_tlu =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

theorem hasFDerivAt_of_slot_tlu {W : ℕ → ℝ → ℝ → ℝ} {F R : ℝ → ℝ → ℝ}
    {L : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)} {q : ℝ × ℝ} (hq : q ∈ Work.FTS.EllipticEst.Q0)
    (hd : ∀ n : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (Function.uncurry (W n)) p)
    (hW : TendstoLocallyUniformlyOn (fun n : ℕ => Function.uncurry (W n))
      (fun p : ℝ × ℝ => F p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0)
    (hL : TendstoLocallyUniformlyOn (fun n : ℕ => fderiv ℝ (Function.uncurry (W n))) L
      Filter.atTop Work.FTS.EllipticEst.Q0)
    (heq : ∀ p ∈ Work.FTS.EllipticEst.Q0, R p.1 p.2 = F p.1 p.2) :
    HasFDerivAt (Function.uncurry R) (L q) q := by
  -- The locally uniform limit `F` of the `W n` has Fréchet derivative `L` on the quadrant.
  have hF : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2) (L q) q :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn Work.FTS.EllipticEst.isOpen_Q0 hL
      (fun n p hp => (hd n p hp).hasFDerivAt)
      (fun p hp => hW.tendsto_at hp) hq
  -- `R` agrees with `F` on a neighbourhood of `q` (the quadrant is open), so the derivative
  -- is the same.
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hq] with p hp
  exact heq p hp

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.HomClsZeroRefute =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison
set_option autoImplicit false
set_option maxHeartbeats 800000


















/-! ## 3. The witness: the mode with the value at `θ = 0` overwritten -/






/-! ## 4. Locality: on the open quadrant `cex` has the same derivatives as `mode` -/






/-! ## 5. The witness satisfies every hypothesis of `HomClsZero` -/









/-! ## 6. `SmoothOpen` and `IsBslSol` for the witness -/




/-! ## 7. A function vanishing on the open quadrant is in `ℋ^k` -/










/-! ## 8. `ℋ⁶`-membership of the three modulation outputs of the witness -/




/-! ## 9. The counterexample -/




end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.integrableOn_theta_marginal_HkIntegrand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 800000
-- `hcd : c ≤ d` is only an (unused) hypothesis of the statement; `c ≤ d` guarantees that the
-- interval `Icc c d` below is the one meant, but the argument only needs `0 < c`.
set_option linter.unusedVariables false

/-- **Integrability of the angular marginal of the `ℋ^1`-integrand.**  For `W` smooth on the
open quadrant and honest in `ℋ^1`, and for `0 < c ≤ d`, the function
`θ ↦ ∫_{c}^{d} HkIntegrand α 1 W z θ dz` is integrable on `(0,π/2)`.

The proof is Tonelli for nonnegative functions together with the finiteness of the *iterated*
integral supplied by `HkMem`:

* the uncurried integrand `p ↦ HkIntegrand α 1 W p.1 p.2` is continuous on the open quadrant
  (`SmoothOpen.continuousOn_HkIntegrand`), hence a.e. strongly measurable for the product of the
  restrictions of Lebesgue measure to `Iz` and `Iθ` (`aesm_of_continuousOn_Qd`);
* Tonelli turns the double integral over `Iz ×ˢ Iθ` of `ofReal` of the integrand into the
  iterated integral of `ofReal`s; the inner integrals are the `ofReal`s of the honest integrals
  because each angular slice is integrable (`HkMem.1`), and the outer one is the `ofReal` of
  `HkSq α 1 W` because the radial marginal is integrable (`HkMem.2`);
* the rectangle `Icc c d ×ˢ Ioo 0 (π/2)` sits inside `Iz ×ˢ Iθ` (as `0 < c`), so the measure
  `(volume.restrict (Icc c d)).prod (volume.restrict (Ioo 0 (π/2)))` is at most
  `(volume.restrict Iz).prod (volume.restrict Iθ)` (`Measure.prod_mono`), and the ℓ-integral of
  the nonnegative integrand over the small rectangle is finite (`lintegral_mono'`);
* this gives `HasFiniteIntegral`, hence `Integrable`, of the uncurried integrand on the rectangle
  (unfolding `HasFiniteIntegral` and rewriting `‖·‖ₑ = ofReal (·)` with `lintegral_congr`), and
  `Integrable.integral_prod_right` integrates out `z`. -/
theorem integrableOn_theta_marginal_HkIntegrand {α : ℝ} {W : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => ∫ z in Set.Icc c d, Work.Spaces.HkIntegrand α 1 W z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hrect : MeasurableSet (Set.Icc c d ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    measurableSet_Icc.prod measurableSet_Ioo
  have hsub : Set.Icc c d ×ˢ Set.Ioo 0 (Real.pi / 2) ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨h1, h2⟩ := Set.mem_prod.mp hp
    exact ⟨lt_of_lt_of_le hc (Set.mem_Icc.mp h1).1, h2⟩
  -- the uncurried integrand is continuous on the closed rectangle
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 1 W p.1 p.2)
      (Set.Icc c d ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hsm.continuousOn_HkIntegrand α 1).mono hsub
  -- a.e. strong measurability of the integrand for the product measure on the rectangle
  have hAEs : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 1 W p.1 p.2)
      ((volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2)))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hcont.aestronglyMeasurable hrect
  -- a.e. measurability of `ofReal` of the integrand over the full quadrant
  have hAEMbig : AEMeasurable
      (Function.uncurry (fun z θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 W z θ)))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 1 W p.1 p.2)
      (hsm.continuousOn_HkIntegrand α 1)).aemeasurable.ennreal_ofReal
  -- Tonelli: the double ℓ-integral over the quadrant is the `ofReal` of `HkSq α 1 W`
  have hbig : ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 W p.1 p.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
      = ENNReal.ofReal (Work.Spaces.HkSq α 1 W) := by
    rw [← MeasureTheory.lintegral_lintegral (μ := volume.restrict Work.Spaces.Iz)
      (ν := volume.restrict Work.Spaces.Iθ) hAEMbig]
    rw [MeasureTheory.lintegral_congr_ae (MeasureTheory.ae_restrict_of_forall_mem hIz
      (fun z hz => (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
        (Filter.Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α 1 W z θ)).symm))]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 1 W z θ)]
    rfl
  -- the rectangle is contained in the quadrant
  have hAB : Set.Icc c d ⊆ Work.Spaces.Iz :=
    fun x hx => le_trans hc.le (Set.mem_Icc.mp hx).1
  have hBθ : Set.Ioo 0 (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨hx.1.le, hx.2.le⟩
  -- the rectangle measure is dominated by the quadrant measure
  have hmono : (volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2)))
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Measure.prod_mono
      (MeasureTheory.Measure.restrict_mono hAB le_rfl)
      (MeasureTheory.Measure.restrict_mono hBθ le_rfl)
  -- the ℓ-integral of `ofReal` of the integrand over the rectangle is finite
  have hsmall : ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 W p.1 p.2)
        ∂((volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2))))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 1 W) :=
    le_trans (MeasureTheory.lintegral_mono' hmono le_rfl) hbig.le
  have hfin : MeasureTheory.HasFiniteIntegral
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 1 W p.1 p.2)
      ((volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2)))) := by
    show ∫⁻ p, ‖Work.Spaces.HkIntegrand α 1 W p.1 p.2‖ₑ
      ∂((volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2)))) < ⊤
    rw [MeasureTheory.lintegral_congr (g := fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 W p.1 p.2))
      (fun p => by
        rw [Real.enorm_eq_ofReal_abs,
          abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 1 W p.1 p.2)])]
    exact lt_of_le_of_lt hsmall ENNReal.ofReal_lt_top
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 1 W p.1 p.2)
      ((volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2)))) :=
    ⟨hAEs, hfin⟩
  exact MeasureTheory.Integrable.integral_prod_right hInt

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.zSlice_sq_le_marginal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The `z`-slice estimate of the marginal `H^1`-integrand

For `W ∈ C^∞` on the open quadrant `(0,∞) × (0,π/2)` and in the weighted space
`ℋ¹`, the `z`-slice of `W` and of its radial derivative `∂_z W` on a positive interval
`[c,d]` is dominated by the `z`-slice of the marginal `H^1`-integrand `HkIntegrand α 1 W`,
with the constant `1 / min 1 (c²)`.

The proof is elementary: writing
`A z θ = w z / sin(2θ)^{η/2}`, the definition of `HkIntegrand` at `k = 1` unfolds to
`(W · A)² + (D_z W · A)² + (D_θ W · W_t)²`, and on `z ≥ c > 0`, `θ ∈ (0,π/2)` one has
`A ≥ 1` (since `w z ≥ 1` and `sin(2θ)^{η/2} ≤ 1`) and `z · A ≥ 1` (since
`z · w z = (1+z)²/z ≥ 1`), so that

`W² + (∂_z W)² ≤ (1/min 1 (c²)) · ((W·A)² + (z ∂_z W · A)²) ≤ (1/min 1 (c²)) · HkIntegrand`.

Integrating over `[c,d]` (all the slices are continuous, hence integrable, on the compact
interval) gives the claim. -/

/-- `sin (2θ) > 0` for `θ` in the open angular interval. -/
private lemma sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The `H^1`-integrand written out: at `k = 1` the two sums of `HkIntegrand` collapse to
the three terms `(W · A)²`, `(D_z W · A)²` and `(D_θ W · W_t)²`. -/
theorem HkIntegrand_one (α : ℝ) (W : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 1 W z θ
      = (W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + ((z * Work.Spaces.pz W z θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + (Work.Spaces.Dth W z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Work.Spaces.DzIter_zero, Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.mixed,
    Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  norm_num

theorem zSlice_sq_le_marginal {α : ℝ} {W : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Set.Icc c d, (W z θ) ^ 2) + (∫ z in Set.Icc c d, (Work.Spaces.pz W z θ) ^ 2)
      ≤ 1 / (min 1 (c ^ 2)) * ∫ z in Set.Icc c d, Work.Spaces.HkIntegrand α 1 W z θ := by
  -- this elementary slice estimate uses only the open-quadrant smoothness of `W`
  have _hmem := hmem
  have _hcd := hcd
  have hs_pos : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem hθ
  have hp_pos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs_pos _
  have hp_le_one : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
    refine Real.rpow_le_one hs_pos.le (Real.sin_le_one _) ?_
    norm_num [Work.Spaces.eta]
  have hm_pos : 0 < min 1 (c ^ 2) := lt_min one_pos (by positivity)
  have hm_le_one : min 1 (c ^ 2) ≤ 1 := min_le_left _ _
  have hinv_pos : 0 < 1 / (min 1 (c ^ 2)) := div_pos one_pos hm_pos
  -- the slice `z ↦ w z` is continuous on `[c,d]` (where `z ≥ c > 0`)
  have hw_cont : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Icc c d) := by
    show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Icc c d)
    refine ContinuousOn.div ((ContinuousOn.const_add continuousOn_id 1).pow 2)
      (continuousOn_id.pow 2) (fun z hz => ?_)
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hc hz.1))
  -- continuity of the `z`-slices of the ingredients of `HkIntegrand`
  have hcontW : ContinuousOn (fun z => W z θ) (Set.Icc c d) :=
    (hsm.curry_z hθ).continuousOn.mono (fun z hz => lt_of_lt_of_le hc hz.1)
  have hcontPz : ContinuousOn (fun z => Work.Spaces.pz W z θ) (Set.Icc c d) :=
    (hsm.pz.curry_z hθ).continuousOn.mono (fun z hz => lt_of_lt_of_le hc hz.1)
  have hcontDth : ContinuousOn (fun z => Work.Spaces.Dth W z θ) (Set.Icc c d) :=
    (hsm.Dth.curry_z hθ).continuousOn.mono (fun z hz => lt_of_lt_of_le hc hz.1)
  have hcontWt : ContinuousOn (fun z => Work.Spaces.Wt α z θ) (Set.Icc c d) :=
    (hw_cont.mul (continuousOn_const : ContinuousOn (fun _ : ℝ => Work.Spaces.wTheta α θ)
      (Set.Icc c d))).congr (fun z _ => rfl)
  have hcontA : ContinuousOn
      (fun z => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Icc c d) :=
    hw_cont.div continuousOn_const (fun z _ => ne_of_gt hp_pos)
  have hcontHk : ContinuousOn (fun z => Work.Spaces.HkIntegrand α 1 W z θ) (Set.Icc c d) := by
    have h1 : ContinuousOn
        (fun z => W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        (Set.Icc c d) := hcontW.mul hcontA
    have h2 : ContinuousOn
        (fun z => (z * Work.Spaces.pz W z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        (Set.Icc c d) := (continuousOn_id.mul hcontPz).mul hcontA
    have h3 : ContinuousOn (fun z => Work.Spaces.Dth W z θ * Work.Spaces.Wt α z θ)
        (Set.Icc c d) := hcontDth.mul hcontWt
    have hsum := (h1.pow 2).add ((h2.pow 2).add (h3.pow 2))
    refine hsum.congr ?_
    intro z _
    simp only [Pi.pow_apply, Pi.add_apply]
    rw [HkIntegrand_one]
    ring
  -- integrability of the three slices
  have hintHk : IntegrableOn (fun z => Work.Spaces.HkIntegrand α 1 W z θ) (Set.Icc c d) :=
    hcontHk.integrableOn_compact isCompact_Icc
  have hintW2 : IntegrableOn (fun z => (W z θ) ^ 2) (Set.Icc c d) :=
    (hcontW.pow 2).integrableOn_compact isCompact_Icc
  have hintPz2 : IntegrableOn (fun z => (Work.Spaces.pz W z θ) ^ 2) (Set.Icc c d) :=
    (hcontPz.pow 2).integrableOn_compact isCompact_Icc
  -- the pointwise bound on `[c,d]`
  have hpt : ∀ z ∈ Set.Icc c d,
      (W z θ) ^ 2 + (Work.Spaces.pz W z θ) ^ 2
        ≤ 1 / (min 1 (c ^ 2)) * Work.Spaces.HkIntegrand α 1 W z θ := by
    intro z hz
    have hz_pos : 0 < z := lt_of_lt_of_le hc hz.1
    have hw_ge_one : 1 ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w, le_div_iff₀ (by positivity : 0 < z ^ 2)]
      nlinarith
    have hA_ge_one : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
      rw [le_div_iff₀ hp_pos]
      simpa using le_trans hp_le_one hw_ge_one
    have hdiv_id : z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        = (1 + z) ^ 2 / (z * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
      rw [Work.Spaces.w]
      field_simp
    have hzA_ge_one : 1 ≤ z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
      rw [hdiv_id, le_div_iff₀ (by positivity : 0 < z * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))]
      nlinarith [hp_le_one, hz_pos]
    have hm_le_sq : min 1 (c ^ 2)
        ≤ (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      have h1 : (1 : ℝ)
          ≤ (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        nlinarith [hzA_ge_one]
      exact le_trans (min_le_left 1 (c ^ 2)) h1
    have hW_sq : (W z θ) ^ 2
        ≤ 1 / (min 1 (c ^ 2))
          * (W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      have hconv : 1 / (min 1 (c ^ 2))
            * (W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              / (min 1 (c ^ 2)) := by ring
      rw [hconv, le_div_iff₀ hm_pos]
      have hA_sq : (1 : ℝ)
          ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
        nlinarith [hA_ge_one, sq_nonneg
          (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) - 1)]
      have h1 := mul_le_mul_of_nonneg_left (le_trans hm_le_one hA_sq) (sq_nonneg (W z θ))
      have h2 : (W z θ) ^ 2
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          = (W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        ring
      linarith [h1, h2]
    have hpz_sq : (Work.Spaces.pz W z θ) ^ 2
        ≤ 1 / (min 1 (c ^ 2))
          * (z * Work.Spaces.pz W z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      have hconv : 1 / (min 1 (c ^ 2))
            * (z * Work.Spaces.pz W z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (z * Work.Spaces.pz W z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              / (min 1 (c ^ 2)) := by ring
      rw [hconv, le_div_iff₀ hm_pos]
      have h1 := mul_le_mul_of_nonneg_left hm_le_sq (sq_nonneg (Work.Spaces.pz W z θ))
      have h2 : (Work.Spaces.pz W z θ) ^ 2
            * (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (z * Work.Spaces.pz W z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        ring
      linarith [h1, h2]
    have hinner : (W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + (z * Work.Spaces.pz W z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α 1 W z θ := by
      rw [HkIntegrand_one]
      nlinarith [sq_nonneg (Work.Spaces.Dth W z θ * Work.Spaces.Wt α z θ)]
    have hsum2 : (W z θ) ^ 2 + (Work.Spaces.pz W z θ) ^ 2
        ≤ 1 / (min 1 (c ^ 2))
          * ((W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            + (z * Work.Spaces.pz W z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      rw [mul_add]
      linarith [hW_sq, hpz_sq]
    calc (W z θ) ^ 2 + (Work.Spaces.pz W z θ) ^ 2
        ≤ 1 / (min 1 (c ^ 2))
          * ((W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            + (z * Work.Spaces.pz W z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := hsum2
      _ ≤ 1 / (min 1 (c ^ 2)) * Work.Spaces.HkIntegrand α 1 W z θ :=
          mul_le_mul_of_nonneg_left hinner (le_of_lt hinv_pos)
  -- integrate the pointwise bound
  have hsum_int : (∫ z in Set.Icc c d,
        ((W z θ) ^ 2 + (Work.Spaces.pz W z θ) ^ 2))
      = (∫ z in Set.Icc c d, (W z θ) ^ 2)
        + ∫ z in Set.Icc c d, (Work.Spaces.pz W z θ) ^ 2 :=
    integral_add hintW2 hintPz2
  have hmono : (∫ z in Set.Icc c d, ((W z θ) ^ 2 + (Work.Spaces.pz W z θ) ^ 2))
      ≤ ∫ z in Set.Icc c d, 1 / (min 1 (c ^ 2)) * Work.Spaces.HkIntegrand α 1 W z θ := by
    refine integral_mono_of_nonneg (Eventually.of_forall (fun z => by positivity)) ?_
      (ae_restrict_of_forall_mem measurableSet_Icc hpt)
    exact hintHk.const_mul _
  calc (∫ z in Set.Icc c d, (W z θ) ^ 2) + (∫ z in Set.Icc c d, (Work.Spaces.pz W z θ) ^ 2)
      = (∫ z in Set.Icc c d, ((W z θ) ^ 2 + (Work.Spaces.pz W z θ) ^ 2)) := hsum_int.symm
    _ ≤ ∫ z in Set.Icc c d, 1 / (min 1 (c ^ 2)) * Work.Spaces.HkIntegrand α 1 W z θ := hmono
    _ = 1 / (min 1 (c ^ 2)) * ∫ z in Set.Icc c d, Work.Spaces.HkIntegrand α 1 W z θ :=
        integral_const_mul _ _

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.ZeroProfile =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-!
# The zero profile in the `ℋ^k`-bookkeeping

The five facts about the identically vanishing profile `fun _ _ : ℝ => 0` that the
"clamping" step of the Volterra remainder estimate needs: the iterated mixed operators
vanish, the `ℋ^k`-integrand vanishes (as a function), the profile is `C^∞` on the open
quadrant, and it is `ℋ^k`-honest with `ℋ^k`-norm `0`.
-/

theorem DthIter_zero_profile (n : ℕ) :
    Work.Spaces.DthIter n (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dth, Work.Spaces.pth]

theorem DzIter_zero_profile (n : ℕ) :
    Work.Spaces.DzIter n (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dz, Work.Spaces.pz]

theorem mixed_zero_profile (j i : ℕ) :
    Work.Spaces.mixed j i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  rw [Work.Spaces.mixed, DthIter_zero_profile i, DzIter_zero_profile j]

theorem HkIntegrand_zero_profile (α : ℝ) (k : ℕ) :
    Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  funext z θ
  simp only [Work.Spaces.HkIntegrand]
  have hz : ∀ i : ℕ, (Work.Spaces.DzIter i (fun _ _ : ℝ => (0 : ℝ)) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
    intro i; rw [DzIter_zero_profile i]; ring
  have hm : ∀ i j : ℕ, (if 1 ≤ i ∧ i + j ≤ k then
      (Work.Spaces.mixed j i (fun _ _ : ℝ => (0 : ℝ)) z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0) = 0 := by
    intro i j
    split_ifs with h
    · rw [mixed_zero_profile j i]; ring
    · rfl
  simp only [hz, hm, Finset.sum_const_zero, add_zero]

theorem smoothOpen_zero_profile :
    Work.FTS.EllipticEst.SmoothOpen (fun _ _ : ℝ => (0 : ℝ)) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h : Function.uncurry (fun _ _ : ℝ => (0 : ℝ)) = fun _ : ℝ × ℝ => 0 := rfl
  rw [h]; exact contDiffOn_const

theorem HkMem_zero_profile (α : ℝ) (k : ℕ) :
    Work.Spaces.HkMem α k (fun _ _ : ℝ => (0 : ℝ)) := by
  constructor
  · intro z hz
    rw [HkIntegrand_zero_profile]
    exact integrableOn_zero
  · rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) z θ) = fun _ => 0 from by
      funext z; rw [HkIntegrand_zero_profile]; simp]
    exact integrableOn_zero

theorem HkNorm_zero_profile (α : ℝ) (k : ℕ) :
    Work.Spaces.HkNorm α k (fun _ _ : ℝ => (0 : ℝ)) = 0 := by
  rw [Work.Spaces.HkNorm]
  rw [show Work.Spaces.HkSq α k (fun _ _ : ℝ => (0 : ℝ)) = 0 from by
    rw [Work.Spaces.HkSq]
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) z θ) = fun _ => 0 from by
      funext z; rw [HkIntegrand_zero_profile]; simp]
    simp]
  exact Real.sqrt_zero

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Work.HkSq_pos_of_continuousOn_ne =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Work



end Work.FTS.StrongEps.EpsE4Work
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.LamLocInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-- **The boundary trace is locally integrable.**

We do not need the trace hypothesis `htr` at all: the boundary bound `hbd`, evaluated at the single
interior angle `θ₀ = π/3 ∈ (π/4, π/2)`, already gives

  `|lam z| ≤ |f z θ₀| + c * √(Ibd α f z)`,   `c := √(100/(γ-1) * sin(2θ₀)^{γ-1})`,

for a.e. `z > 0`; and since `SmoothOpen f` makes the slice `z ↦ f z θ₀` continuous on `(0,∞)`,
the first term is bounded by a constant on the compact interval `[a,b]`.  The second term is
integrable by hypothesis `hD`, so `lam` is dominated by an integrable function on `[a,b]`. -/
theorem LamLocInt {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ} {lam : ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hlamm : Measurable lam)
    (htr : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        Filter.Tendsto (fun θ => f z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (lam z)))
    (hbd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (f z θ - lam z) ^ 2 ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 1)
          * (∫ σ in Work.Spaces.Iθ,
              (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hD : ∫⁻ u in Set.Icc a b, ENNReal.ofReal (Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2)) < ⊤) :
    ∫⁻ u in Set.Icc a b, ENNReal.ofReal |lam u| < ⊤ := by
  -- `γ - 1 = α/10 > 0`
  have hgam1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam]; linarith [hα.1]
  -- the interior angle `θ₀ = π/3` at which the boundary bound is evaluated
  set θ₀ : ℝ := Real.pi / 3 with hθ₀def
  have hθ₀ : θ₀ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := by
    rw [hθ₀def]; constructor <;> linarith [Real.pi_pos]
  have hθ₀pos : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [hθ₀def]; constructor <;> linarith [Real.pi_pos]
  have hsinθ₀ : 0 < Real.sin (2 * θ₀) := by
    have h2 : (2 : ℝ) * θ₀ = 2 * Real.pi / 3 := by rw [hθ₀def]; ring
    rw [h2]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  -- the constant `c` of the boundary bound at `θ₀`
  set c : ℝ := Real.sqrt (100 / (Work.Spaces.gam α - 1)
    * (Real.sin (2 * θ₀)) ^ (Work.Spaces.gam α - 1)) with hcdef
  have hc_nonneg : 0 ≤ c := Real.sqrt_nonneg _
  have hc_sq : c ^ 2 = 100 / (Work.Spaces.gam α - 1)
      * (Real.sin (2 * θ₀)) ^ (Work.Spaces.gam α - 1) :=
    Real.sq_sqrt (mul_nonneg (by positivity) (Real.rpow_nonneg hsinθ₀.le _))
  -- the slice `z ↦ f z θ₀` is continuous on `(0,∞)`, hence bounded on `[a,b]`
  have hcontθ : ContinuousOn (fun u : ℝ => f u θ₀) (Set.Icc a b) :=
    (hso.curry_z hθ₀pos).continuousOn.mono (fun z hz => lt_of_lt_of_le ha hz.1)
  obtain ⟨x₀, -, hx₀max⟩ :=
    isCompact_Icc.exists_isMaxOn (⟨a, le_rfl, hab⟩ : (Set.Icc a b).Nonempty) hcontθ.abs
  have hMnb : 0 ≤ |f x₀ θ₀| := abs_nonneg _
  have hM : ∀ u ∈ Set.Icc a b, |f u θ₀| ≤ |f x₀ θ₀| := fun u hu => hx₀max hu
  -- the boundary bound, restricted to the interval `[a,b]`
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hbdc : ∀ᵐ z ∂(volume.restrict (Set.Icc a b)),
      ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (f z θ - lam z) ^ 2 ≤ 100 / (Work.Spaces.gam α - 1)
          * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 1)
          * (∫ σ in Work.Spaces.Iθ,
              (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2) :=
    ae_restrict_of_ae_restrict_of_subset hsub hbd
  -- the a.e. pointwise domination of `lam` by an integrable function
  have hpoint : ∀ᵐ z ∂(volume.restrict (Set.Icc a b)),
      |lam z| ≤ |f x₀ θ₀| + c * Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2) := by
    refine (hbdc.and (ae_restrict_of_forall_mem measurableSet_Icc hM)).mono ?_
    rintro z ⟨hbz, hMz⟩
    have hbθ := hbz θ₀ hθ₀
    have hsq : (f z θ₀ - lam z) ^ 2 ≤ c ^ 2 * (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2) := by
      rw [hc_sq]; exact hbθ
    have hsqrt : |f z θ₀ - lam z| ≤ c * Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2) := by
      have h1 := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hc_nonneg] at h1
      exact h1
    calc |lam z| = |(lam z - f z θ₀) + f z θ₀| := by rw [sub_add_cancel]
      _ ≤ |lam z - f z θ₀| + |f z θ₀| := abs_add_le _ _
      _ = |f z θ₀ - lam z| + |f z θ₀| := by rw [abs_sub_comm]
      _ ≤ c * Real.sqrt (∫ σ in Work.Spaces.Iθ,
            (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2)
          + |f x₀ θ₀| := add_le_add hsqrt hMz
      _ = |f x₀ θ₀| + c * Real.sqrt (∫ σ in Work.Spaces.Iθ,
            (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2) := by ring
  -- the dominating function is an (essentially) constant plus a multiple of the `hD`-integrand
  have hsplit : ∀ u : ℝ, ENNReal.ofReal (|f x₀ θ₀| + c * Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2))
      = ENNReal.ofReal |f x₀ θ₀|
        + ENNReal.ofReal c * ENNReal.ofReal (Real.sqrt (∫ σ in Work.Spaces.Iθ,
            (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2)) := by
    intro u
    rw [ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg hc_nonneg (Real.sqrt_nonneg _)),
      ENNReal.ofReal_mul hc_nonneg]
  refine lt_of_le_of_lt (lintegral_mono_ae (hpoint.mono fun z hz => ENNReal.ofReal_le_ofReal hz)) ?_
  rw [lintegral_congr hsplit]
  rw [lintegral_add_left' aemeasurable_const]
  rw [lintegral_const_mul' (ENNReal.ofReal c) _ ENNReal.ofReal_ne_top]
  rw [setLIntegral_const]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Icc_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD⟩

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.SqrtDMeas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

set_option linter.unusedVariables false

namespace Work.FTS.StrongEps.EpsLocalPStar

theorem SqrtDMeas {α z ε : ℝ} (hα : α ∈ Set.Ioc 0 1) (hz : 0 < z) (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (fun q : ℝ => Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f (z * Real.exp (-(ε * q))) σ) ^ 2))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  -- `Iθ = [0, π/2]` and the open interval `(0, π/2)` carry the same restricted measure.
  have hIθ : (MeasureTheory.volume.restrict Work.Spaces.Iθ : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm
  -- The uncurried integrand is continuous on `ℝ × (0, π/2)`.
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
      * (Work.Spaces.pth f (z * Real.exp (-(ε * p.1))) p.2) ^ 2)
      (Set.univ ×ˢ Set.Ioo 0 (π / 2)) := by
    have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
        (Set.univ ×ˢ Set.Ioo 0 (π / 2)) := by
      have h1 : Continuous (fun p : ℝ × ℝ => Real.sin (2 * p.2)) := by fun_prop
      refine h1.continuousOn.rpow_const ?_
      intro p hp
      exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos])))
    have hpth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth f (z * Real.exp (-(ε * p.1))) p.2)
        (Set.univ ×ˢ Set.Ioo 0 (π / 2)) := by
      have hφ : Continuous (fun p : ℝ × ℝ => (z * Real.exp (-(ε * p.1)), p.2)) := by fun_prop
      have hmap : Set.MapsTo (fun p : ℝ × ℝ => (z * Real.exp (-(ε * p.1)), p.2))
          (Set.univ ×ˢ Set.Ioo 0 (π / 2)) Work.FTS.EllipticEst.Q0 := by
        intro p hp
        rw [Work.FTS.EllipticEst.mem_Q0]
        exact ⟨mul_pos hz (Real.exp_pos _), hp.2.1, hp.2.2⟩
      have h2 := (hso.pth).continuousOn.comp hφ.continuousOn hmap
      simpa [Function.comp_def, Function.uncurry] using h2
    exact hsin.mul (hpth.pow 2)
  -- `volume ⊗ (volume ↾ (0,π/2))` is the restriction of the planar measure to `ℝ × (0,π/2)`.
  have hprod : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) : MeasureTheory.Measure (ℝ × ℝ))
      = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
          (Set.univ ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [← MeasureTheory.Measure.prod_restrict (s := Set.univ) (t := Set.Ioo 0 (π / 2)),
      MeasureTheory.Measure.restrict_univ]
  -- Joint a.e. strong measurability of the integrand.
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth f (z * Real.exp (-(ε * p.1))) p.2) ^ 2)
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)))) : MeasureTheory.Measure (ℝ × ℝ)) := by
    have hmeas : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
      MeasurableSet.prod (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ)) measurableSet_Ioo
    have h := hcont.aestronglyMeasurable
      (μ := MeasureTheory.volume.prod MeasureTheory.volume) hmeas
    rw [← hprod] at h
    exact h
  -- Fubini measurability of the parametrised angular integral.
  have hint : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ => ∫ σ, (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth f (z * Real.exp (-(ε * q))) σ) ^ 2
        ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)))) MeasureTheory.volume :=
    hjoint.integral_prod_right'
  -- Compose with the continuous square root and change the measure back to `Iθ`.
  have := Real.continuous_sqrt.comp_aestronglyMeasurable hint
  simpa only [hIθ] using this

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.aemeasurable_traceSeq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A.e. measurability of the sampled boundary trace

For `f` of class `Work.FTS.EllipticEst.SmoothOpen` (i.e. `C^∞` on the open quadrant
`(0,∞) × (0,π/2)`) the sampled trace

`z ↦ limUnder atTop (fun n : ℕ => f z (1 / (n + 2)))`

is a.e. measurable w.r.t. `volume.restrict (Ioi 0)`.

The mathematical content is that `Filter.limUnder atTop` of a family of measurable
functions indexed by `ℕ` is measurable (`MeasureTheory.StronglyMeasurable.limUnder`:
`Filter.lim` is the limit of the filter when it exists, and the constant
`Classical.choice` junk value otherwise, so its measurability is not automatic).  The
only input needed is that each sampled slice `z ↦ f z θ_n`, `θ_n = 1/(n+2) ∈ (0, π/2)`,
is measurable on `Ioi 0`, which follows from `SmoothOpen.curry_z`: the `z`-slice at an
interior angle is `C^∞` on `Ioi 0`, hence continuous there.
-/

namespace Work.FTS.StrongEps.EpsLocalPStar

open MeasureTheory Set Filter

theorem aemeasurable_traceSeq {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    AEMeasurable
      (fun z : ℝ => Filter.limUnder Filter.atTop (fun n : ℕ => f z (1 / (n + 2 : ℝ))))
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
  -- Work on the subtype `Ioi 0`: a measurable function on it gives an a.e. measurable
  -- function for the restricted measure.
  refine aemeasurable_restrict_of_measurable_subtype measurableSet_Ioi ?_
  -- The sampled angles `1/(n+2)` lie in the open quadrant's angle range `(0, π/2)`.
  have hθn : ∀ n : ℕ, (1 : ℝ) / (n + 2 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) := by
    intro n
    constructor
    · positivity
    · have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
        have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hle : (1 : ℝ) / (n + 2 : ℝ) ≤ 1 / 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
      linarith [Real.pi_gt_three]
  -- Each sampled slice, viewed on the subtype `Ioi 0`, is continuous, hence strongly
  -- measurable.
  have hslice : ∀ n : ℕ, StronglyMeasurable
      (fun z : Set.Ioi (0:ℝ) => f z.1 (1 / (n + 2 : ℝ))) := by
    intro n
    exact ((hso.curry_z (hθn n)).continuousOn.comp_continuous
      continuous_subtype_val (fun z => z.2)).stronglyMeasurable
  -- `limUnder` of a sequence of strongly measurable functions is strongly measurable.
  have hlim : StronglyMeasurable
      (fun z : Set.Ioi (0:ℝ) => Filter.limUnder Filter.atTop
        (fun n : ℕ => f z.1 (1 / (n + 2 : ℝ)))) :=
    StronglyMeasurable.limUnder (l := Filter.atTop)
      (f := fun (n : ℕ) (z : Set.Ioi (0:ℝ)) => f z.1 (1 / (n + 2 : ℝ))) hslice
  exact hlim.measurable

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsWp.Dth_slice_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Dth_slice_le`

A small glue lemma for the strong-`ε` layer of the Elgindi project.

For a Galerkin family `G` whose `s`-slice is `C^∞` on the open quadrant, and for
`0 < z`, `0 < θ < π/2`, the angular derivative `D_θ = sin(2θ) ∂_θ` of the slice is dominated by
the two `∂_θ`-derivatives appearing in the split `F(τ) = F_* + g(τ)`:

`|D_θ (G · · s) z θ| ≤ |∂_θ (F_* + G · · s) z θ| + |∂_θ F_* z θ|`.

This is the triangle inequality for `∂_θ` (the slice of `F_*` is differentiable at every interior
angle, and the derivative splits, `∂_θ(F_* + g) = ∂_θF_* + ∂_θg`), together with `|sin(2θ)| ≤ 1`.
No smoothness of the family `G` in the angle beyond `SmoothOpen (slice G s)` is used.
-/

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongEps.EpsWp

/-- The `θ`-slice of the reference profile `F_* = α(Γ/c)·F_{*,rad}` is differentiable at every
interior angle `0 < θ < π/2`: there `sin θ · cos²θ > 0`, so the angular profile
`Γ(θ) = (sin θ cos²θ)^{α/3}` is differentiable by the chain rule for real powers, and the
remaining factor is a constant of the slice. -/
theorem differentiableAt_Fstar_slice_theta (α z θ : ℝ) (hθ : 0 < θ ∧ θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar α z θ') θ := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ.2⟩
  have hbase : Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by positivity
  have hGam : DifferentiableAt ℝ (fun θ' => Work.Spaces.Gam α θ') θ := by
    rw [show Work.Spaces.Gam α = fun y : ℝ => (Real.sin y * Real.cos y ^ 2) ^ (α / 3) from rfl]
    exact (Real.differentiableAt_sin.mul (Real.differentiableAt_cos.pow 2)).rpow_const
      (Or.inl hbase)
  have h := ((hGam.div_const (Work.Spaces.c α)).const_mul α).mul_const (Work.FM.Fstar z)
  simpa [Work.Construction.Fstar] using h

theorem Dth_slice_le {α : ℝ} {G : Work.FTS.Galerkin.Fam} {s z θ : ℝ}
    (hreg : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice G s))
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    |Work.Spaces.Dth (Work.FTS.Galerkin.slice G s) z θ| ≤
      |Work.Spaces.pth (Work.Construction.Ftau α G s) z θ|
        + |Work.Spaces.pth (Work.Construction.Fstar α) z θ| := by
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
  -- differentiability of the two `θ`-slices at `θ`
  have hGs : DifferentiableAt ℝ (fun θ' => G z θ' s) θ :=
    ((hreg.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hFs : DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar α z θ') θ :=
    differentiableAt_Fstar_slice_theta α z θ ⟨hθ0, hθ1⟩
  -- the `θ`-derivative of the full profile splits
  have hsplit : Work.Spaces.pth (Work.Construction.Ftau α G s) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ
        + Work.Spaces.pth (Work.FTS.Galerkin.slice G s) z θ := by
    simp only [Work.Spaces.pth, Work.Construction.Ftau, Work.FTS.Galerkin.slice]
    rw [show (fun θ' => Work.Construction.Fstar α z θ' + G z θ' s)
        = (fun θ' => Work.Construction.Fstar α z θ') + (fun θ' => G z θ' s) from rfl,
      deriv_add hFs hGs]
  have hpth_eq : Work.Spaces.pth (Work.FTS.Galerkin.slice G s) z θ
      = Work.Spaces.pth (Work.Construction.Ftau α G s) z θ
        - Work.Spaces.pth (Work.Construction.Fstar α) z θ := by
    rw [hsplit]; ring
  calc |Work.Spaces.Dth (Work.FTS.Galerkin.slice G s) z θ|
      = |Real.sin (2 * θ)| * |Work.Spaces.pth (Work.FTS.Galerkin.slice G s) z θ| := by
        rw [Work.Spaces.Dth, abs_mul]
    _ ≤ 1 * |Work.Spaces.pth (Work.FTS.Galerkin.slice G s) z θ| :=
        mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (2 * θ)) (abs_nonneg _)
    _ = |Work.Spaces.pth (Work.FTS.Galerkin.slice G s) z θ| := one_mul _
    _ = |Work.Spaces.pth (Work.Construction.Ftau α G s) z θ
            - Work.Spaces.pth (Work.Construction.Fstar α) z θ| := by rw [hpth_eq]
    _ ≤ |Work.Spaces.pth (Work.Construction.Ftau α G s) z θ|
          + |Work.Spaces.pth (Work.Construction.Fstar α) z θ| := by
        rw [abs_sub_le_iff]
        constructor <;>
          linarith [le_abs_self (Work.Spaces.pth (Work.Construction.Ftau α G s) z θ),
            le_abs_self (Work.Spaces.pth (Work.Construction.Fstar α) z θ),
            neg_abs_le (Work.Spaces.pth (Work.Construction.Ftau α G s) z θ),
            neg_abs_le (Work.Spaces.pth (Work.Construction.Fstar α) z θ)]

end Work.FTS.StrongEps.EpsWp
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.Bridge.ProjTransport =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsZero.Bridge

open MeasureTheory

/-- The angular profile `K(θ)Γ(θ)/c` is integrable on `Iθ`.  (Used to transfer the
integrability of the transport density to its projection: the projection subtracts a
constant multiple of `K Γ/c` from every `θ`-slice.) -/
theorem integrableOn_KGam_div_c {α : ℝ} (hα : 0 < α) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α) Work.Spaces.Iθ := by
  refine MeasureTheory.IntegrableOn.congr_fun
    ((Work.Spaces.CAux.integrableOn_GamK α hα).const_mul (Work.Spaces.c α)⁻¹)
    (fun θ _ => ?_) measurableSet_Icc
  show (Work.Spaces.c α)⁻¹ * (Work.Spaces.Gam α θ * Work.Spaces.K θ)
      = Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α
  ring

/-- **The pointwise identity underlying `ProjTransport`.**  The angular slice density of the
projection is the slice density of `f` minus the constant `L₁₂(f)(0)·2s/(1+s)³` times
`K Γ/c`:

`K(θ)·𝕡(f)(s,θ)/s = K(θ)·f(s,θ)/s - (L₁₂(f)(0)·2s²/(1+s)³/s)·(K(θ)Γ(θ)/c)`.

(This is `Proj_eq` rearranged so that the `z`-dependent correction profile and the angular
profile `K Γ/c` are separated.) -/
theorem slice_Proj_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (s θ : ℝ) :
    Work.Spaces.K θ * Work.Coercivity.Proj α f s θ / s
      = Work.Spaces.K θ * f s θ / s
        - (Work.Coercivity.L12f f 0 * (2 * s ^ 2 / (1 + s) ^ 3) / s)
          * (Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α) := by
  simp only [Work.Coercivity.Proj_eq]
  ring

theorem ProjTransport {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hslice : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s) Work.Spaces.Iθ)
    (hdens : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Coercivity.Transport f)) (Set.Ioi 0)) :
    (∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Coercivity.Proj α (Work.Coercivity.Transport f) s θ / s)
      Work.Spaces.Iθ) ∧
    MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Coercivity.Proj α (Work.Coercivity.Transport f)))
      (Set.Ioi 0) := by
  have hGK := integrableOn_KGam_div_c (α := α) hα
  refine ⟨?_, ?_⟩
  · -- the angular slices of the projection are the slices of `Transport f` minus a constant
    -- multiple of `K Γ/c`
    intro s hs
    have hcorr : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
            * (2 * s ^ 2 / (1 + s) ^ 3) / s)
          * (Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α)) Work.Spaces.Iθ :=
      hGK.const_mul _
    refine MeasureTheory.IntegrableOn.congr_fun ((hslice s hs).sub hcorr) (fun θ _ => ?_)
      measurableSet_Icc
    simp only [Pi.sub_apply]
    exact (slice_Proj_eq α (Work.Coercivity.Transport f) s θ).symm
  · -- the density of the projection is the density of `Transport f` minus an integrable
    -- correction profile
    have hproj := fun s (hs : s ∈ Set.Ioi (0:ℝ)) =>
      Work.Coercivity.Proj_L12dens α hα hα1 (Work.Coercivity.Transport f)
        (fun s hs => hslice s hs) hs
    have hcorr : MeasureTheory.IntegrableOn
        (fun s : ℝ => Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
          * (2 * s / (1 + s) ^ 3)) (Set.Ioi 0) :=
      Work.Coercivity.integrableOn_two_mul_div_cube.const_mul _
    refine MeasureTheory.IntegrableOn.congr_fun (hdens.sub hcorr) (fun s hs => ?_)
      measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [Work.Construction.L12dens, Work.Construction.L12dens, hproj s hs]

end Work.FTS.StrongEps.EpsZero.Bridge
end
-- ===== merged: Submission.Work.FTS.StrongEps.LGammaT_abs_le_on_compact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-- `|a / b| ≤ |a|` as soon as `1 ≤ b`. -/
private lemma abs_div_le_abs_of_one_le {a b : ℝ} (hb : 1 ≤ b) : |a / b| ≤ |a| := by
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le one_pos hb
  rw [abs_div, abs_of_nonneg hb0.le, div_le_iff₀ hb0]
  exact le_mul_of_one_le_right (abs_nonneg a) hb

/-- `|a - b| ≤ |a| + |b|`. -/
private lemma abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg] using abs_add_le a (-b)


end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.eBoxes =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The exhaustion boxes for the level-5 extraction
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Inner lower `z`-bound. -/
def ea (m : ℕ) : ℝ := 1 / ((m : ℝ) + 2)
/-- Inner upper `z`-bound. -/
def eb (m : ℕ) : ℝ := (m : ℝ) + 2
/-- Inner lower `θ`-bound. -/
def ec (m : ℕ) : ℝ := 1 / ((m : ℝ) + 2)
/-- Inner upper `θ`-bound. -/
def ed (m : ℕ) : ℝ := π / 2 - 1 / ((m : ℝ) + 2)
/-- Outer lower `z`-bound. -/
def ea₀ (m : ℕ) : ℝ := 1 / (2 * ((m : ℝ) + 2))
/-- Outer upper `z`-bound. -/
def eb₀ (m : ℕ) : ℝ := 2 * ((m : ℝ) + 2)
/-- Outer lower `θ`-bound. -/
def ec₀ (m : ℕ) : ℝ := 1 / (2 * ((m : ℝ) + 2))
/-- Outer upper `θ`-bound. -/
def ed₀ (m : ℕ) : ℝ := π / 2 - 1 / (2 * ((m : ℝ) + 2))

/-- The inner box of the exhaustion. -/
def eBox (m : ℕ) : Set (ℝ × ℝ) := Set.Icc (ea m) (eb m) ×ˢ Set.Icc (ec m) (ed m)

/-- The data box for the `z`-engine at stage `m`. -/
def eBoxZ (m : ℕ) : Set (ℝ × ℝ) := Set.Icc (ea₀ m) (eb₀ m) ×ˢ Set.Icc (ec m) (ed m)

/-- The data box for the `θ`-engine at stage `m`. -/
def eBoxT (m : ℕ) : Set (ℝ × ℝ) := Set.Icc (ea m) (eb m) ×ˢ Set.Icc (ec₀ m) (ed₀ m)

theorem ea_pos (m : ℕ) : 0 < ea m := by
  simp only [ea]; positivity


theorem ec_pos (m : ℕ) : 0 < ec m := by
  simp only [ec]; positivity

theorem ea₀_pos (m : ℕ) : 0 < ea₀ m := by
  simp only [ea₀]; positivity

theorem ec₀_pos (m : ℕ) : 0 < ec₀ m := by
  simp only [ec₀]; positivity

theorem ea₀_lt_ea (m : ℕ) : ea₀ m < ea m := by
  have h : 0 < (m : ℝ) + 2 := by positivity
  simp only [ea, ea₀]
  rw [div_lt_div_iff₀ (by positivity) h] <;> ring_nf <;> linarith

theorem two_le_natCast_add_two (m : ℕ) : (2 : ℝ) ≤ (m : ℝ) + 2 := by
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem ea_lt_eb (m : ℕ) : ea m < eb m := by
  have h : 0 < (m : ℝ) + 2 := by positivity
  have h2 : (2 : ℝ) ≤ (m : ℝ) + 2 := two_le_natCast_add_two m
  simp only [ea, eb]
  rw [div_lt_iff₀ h]
  nlinarith [h2, h]

theorem eb_lt_eb₀ (m : ℕ) : eb m < eb₀ m := by
  simp only [eb, eb₀]; linarith

theorem ec₀_lt_ec (m : ℕ) : ec₀ m < ec m := by
  have h : 0 < (m : ℝ) + 2 := by positivity
  simp only [ec, ec₀]
  rw [div_lt_div_iff₀ (by positivity) h] <;> ring_nf <;> linarith

theorem ec_lt_ed (m : ℕ) : ec m < ed m := by
  have h : 0 < (m : ℝ) + 2 := by positivity
  have h2 : (2 : ℝ) ≤ (m : ℝ) + 2 := two_le_natCast_add_two m
  have hp : 2 < π := by linarith [Real.pi_gt_three]
  have hb : 2 * (1 / ((m : ℝ) + 2)) ≤ 1 := by
    rw [mul_one_div, div_le_iff₀ h]; linarith [h2]
  have hc : (1 : ℝ) < π / 2 := by linarith [hp]
  simp only [ec, ed]
  linarith

theorem ed_lt_ed₀ (m : ℕ) : ed m < ed₀ m := by
  have h : 0 < (m : ℝ) + 2 := by positivity
  simp only [ed, ed₀]
  have h1 : 1 / (2 * ((m : ℝ) + 2)) < 1 / ((m : ℝ) + 2) := by
    rw [div_lt_div_iff₀ (by positivity) h] <;> ring_nf <;> linarith
  linarith

theorem ed₀_lt_pi (m : ℕ) : ed₀ m < π / 2 := by
  have h : 0 < 1 / (2 * ((m : ℝ) + 2)) := by positivity
  simp only [ed₀]; linarith

theorem ed_lt_pi (m : ℕ) : ed m < π / 2 :=
  lt_trans (ed_lt_ed₀ m) (ed₀_lt_pi m)

theorem eBox_subset_Q0 (m : ℕ) : eBox m ⊆ Work.FTS.EllipticEst.Q0 := by
  intro p hp
  have h1 : 0 < p.1 := lt_of_lt_of_le (ea_pos m) hp.1.1
  have h2 : 0 < p.2 := lt_of_lt_of_le (ec_pos m) hp.2.1
  have h3 : p.2 < π / 2 := lt_of_le_of_lt hp.2.2 (ed_lt_pi m)
  exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨h1, h2, h3⟩

theorem eBoxZ_subset_Q0 (m : ℕ) : eBoxZ m ⊆ Work.FTS.EllipticEst.Q0 := by
  intro p hp
  have h1 : 0 < p.1 := lt_of_lt_of_le (ea₀_pos m) hp.1.1
  have h2 : 0 < p.2 := lt_of_lt_of_le (ec_pos m) hp.2.1
  have h3 : p.2 < π / 2 := lt_of_le_of_lt hp.2.2 (ed_lt_pi m)
  exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨h1, h2, h3⟩

theorem eBoxT_subset_Q0 (m : ℕ) : eBoxT m ⊆ Work.FTS.EllipticEst.Q0 := by
  intro p hp
  have h1 : 0 < p.1 := lt_of_lt_of_le (ea_pos m) hp.1.1
  have h2 : 0 < p.2 := lt_of_lt_of_le (ec₀_pos m) hp.2.1
  have h3 : p.2 < π / 2 := lt_of_le_of_lt hp.2.2 (ed₀_lt_pi m)
  exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨h1, h2, h3⟩

theorem iUnion_eBox : (⋃ m : ℕ, eBox m) = Work.FTS.EllipticEst.Q0 := by
  ext p
  constructor
  · intro hp
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hp
    exact eBox_subset_Q0 m hm
  · intro hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    obtain ⟨N, hN⟩ := exists_nat_gt (max (max (1 / p.1) (1 / p.2))
      (max p.1 (1 / (π / 2 - p.2))))
    have hN1 : 1 / p.1 < (N : ℝ) := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hN2 : 1 / p.2 < (N : ℝ) := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hN3 : p.1 < (N : ℝ) := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    have hN4 : 1 / (π / 2 - p.2) < (N : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have hpos : 0 < π / 2 - p.2 := by linarith
    have hNpos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [ea, div_le_iff₀ hNpos]
      have hkey : 1 / p.1 * p.1 < (N : ℝ) * p.1 := mul_lt_mul_of_pos_right hN1 hz
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hz)] at hkey
      nlinarith [hkey]
    · rw [eb]; linarith
    · rw [ec, div_le_iff₀ hNpos]
      have hkey : 1 / p.2 * p.2 < (N : ℝ) * p.2 := mul_lt_mul_of_pos_right hN2 hθ0
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hθ0)] at hkey
      nlinarith [hkey]
    · rw [ed, le_sub_iff_add_le]
      have hkey : 1 / (π / 2 - p.2) * (π / 2 - p.2) < (N : ℝ) * (π / 2 - p.2) :=
        mul_lt_mul_of_pos_right hN4 hpos
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hpos)] at hkey
      have : 1 / ((N : ℝ) + 2) ≤ π / 2 - p.2 := by
        rw [div_le_iff₀ hNpos]
        have : (1 : ℝ) ≤ (π / 2 - p.2) * ((N : ℝ) + 2) := by nlinarith [hkey, hpos]
        linarith [this]
      linarith [this]

end Work.FTS.StrongEps.LocUnif.D5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.LocAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false
set_option maxHeartbeats 1000000


/-! ## Small auxiliary lemmas -/

/-- **Commutation of `D_z` with the iterates of `D_θ`, at the honest `C^∞` order.**  This is
`Work.Spaces.DzDthIterCommOn` with the analytic order `⊤` replaced by
`Work.Stability.smoothOrder` (which is what the open-quadrant class `SmoothOpen` provides). -/
theorem DzDthIterCommOn_smooth {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hF : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) V :=
        Work.FTS.LocData.contDiffOn_DthIter hV hg i
      have hFy : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (hF.contDiffAt (hV.mem_nhds hy)).of_le (by norm_num)
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i g) hFy
      show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
          = Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-- **Multiplication by a continuous function preserves local uniform convergence** on an open set. -/
theorem tendstoLocallyUniformlyOn_mul_continuousOn {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F : ℕ → ℝ × ℝ → ℝ} {f : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℝ}
    (hF : TendstoLocallyUniformlyOn F f Filter.atTop U) (hg : ContinuousOn g U) :
    TendstoLocallyUniformlyOn (fun n p => g p * F n p) (fun p => g p * f p) Filter.atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at hF ⊢
  intro K hKU hK
  have hFK := Metric.tendstoUniformlyOn_iff.mp (hF K hKU hK)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hg.mono hKU)
  have hCpos : 0 < max C 1 := lt_max_of_lt_right one_pos
  filter_upwards [hFK (ε / max C 1) (by positivity)] with n hn p hp
  rw [Real.dist_eq, abs_sub_comm]
  have h1 : |g p| ≤ max C 1 := by
    refine le_trans ?_ (le_max_left _ _)
    rw [← Real.norm_eq_abs]
    exact hC p hp
  have h2 : |F n p - f p| < ε / max C 1 := by
    rw [abs_sub_comm]
    simpa [Real.dist_eq] using hn p hp
  have h3 : |g p * F n p - g p * f p| = |g p| * |F n p - f p| := by
    rw [← mul_sub, abs_mul]
  rw [h3]
  calc |g p| * |F n p - f p| ≤ (max C 1) * |F n p - f p| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ < (max C 1) * (ε / max C 1) := mul_lt_mul_of_pos_left h2 hCpos
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hCpos)

/-- **Restriction of local uniform convergence to a `z`-slice.** -/
theorem tendstoLocallyUniformlyOn_slice_fst {U : Set (ℝ × ℝ)} {F : ℕ → ℝ × ℝ → ℝ}
    {f : ℝ × ℝ → ℝ} {θ : ℝ} {W : Set ℝ} (hW : ∀ z ∈ W, (z, θ) ∈ U)
    (hF : TendstoLocallyUniformlyOn F f Filter.atTop U) :
    TendstoLocallyUniformlyOn (fun n z' => F n (z', θ)) (fun z' => f (z', θ)) Filter.atTop W :=
  hF.comp (fun z' : ℝ => (z', θ)) hW (continuous_id.prodMk continuous_const).continuousOn

/-- **Restriction of local uniform convergence to a `θ`-slice.** -/
theorem tendstoLocallyUniformlyOn_slice_snd {U : Set (ℝ × ℝ)} {F : ℕ → ℝ × ℝ → ℝ}
    {f : ℝ × ℝ → ℝ} {z : ℝ} {W : Set ℝ} (hW : ∀ θ ∈ W, (z, θ) ∈ U)
    (hF : TendstoLocallyUniformlyOn F f Filter.atTop U) :
    TendstoLocallyUniformlyOn (fun n θ' => F n (z, θ')) (fun θ' => f (z, θ')) Filter.atTop W :=
  hF.comp (fun θ' : ℝ => (z, θ')) hW (continuous_const.prodMk continuous_id).continuousOn

/-- **The chain rule for the logarithmic substitution `v ↦ arctan (exp v)`.** -/
theorem hasDerivAt_arctan_exp (v : ℝ) :
    HasDerivAt (fun v' : ℝ => Real.arctan (Real.exp v'))
      (Real.sin (2 * Real.arctan (Real.exp v)) / 2) v := by
  have h1 : HasDerivAt (fun v' : ℝ => Real.exp v') (Real.exp v) v := Real.hasDerivAt_exp v
  have h2 : HasDerivAt Real.arctan (1 / (1 + (Real.exp v) ^ 2)) (Real.exp v) :=
    Real.hasDerivAt_arctan (Real.exp v)
  have h3 : HasDerivAt (fun v' : ℝ => Real.arctan (Real.exp v'))
      (1 / (1 + (Real.exp v) ^ 2) * Real.exp v) v := h2.comp v h1
  convert h3 using 1
  rw [show Real.sin (2 * Real.arctan (Real.exp v)) = 2 * Real.exp v / (1 + (Real.exp v) ^ 2) from by
    have hS : (0 : ℝ) < 1 + (Real.exp v) ^ 2 := by positivity
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    rw [show (2 : ℝ) * (Real.exp v / √(1 + (Real.exp v) ^ 2))
          * (1 / √(1 + (Real.exp v) ^ 2))
        = 2 * Real.exp v / (√(1 + (Real.exp v) ^ 2)) ^ 2 from by ring]
    rw [Real.sq_sqrt hS.le]]
  field_simp

/-- **Smoothness of the inverse coordinate change `(z,θ) ↦ (log z, log tan θ)` on `Q0`.** -/
theorem contDiffOn_logLog_Q0 (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => (Real.log p.1, Real.log (Real.tan p.2)))
      Work.FTS.EllipticEst.Q0 := by
  have hlog1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.log p.1) Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.log ?_ ?_
    · exact (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)).contDiffOn
    · intro p hp
      exact ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have htan : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 := by
    have h : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2)
        Work.FTS.EllipticEst.Q0 := by
      refine ContDiffOn.div (Real.contDiff_sin.comp_contDiffOn contDiff_snd.contDiffOn)
        (Real.contDiff_cos.comp_contDiffOn contDiff_snd.contDiffOn) ?_
      intro p hp
      obtain ⟨h1, h2, h3⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [h3]⟩)
    convert h using 1
    funext p
    exact Real.tan_eq_sin_div_cos p.2
  have hlog2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.log (Real.tan p.2))
      Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.log htan ?_
    intro p hp
    obtain ⟨h1, h2, h3⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.tan_pos_of_pos_of_lt_pi_div_two h2 h3)
  exact hlog1.prodMk hlog2


end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.basis_apply_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option maxHeartbeats 1000000

/-- `(2 : ℕ∞ω) ≤ Work.Stability.smoothOrder`: the honest smooth order `∞ = ((⊤ : ℕ∞) : ℕ∞ω)`
dominates the finite order `2`. -/
lemma two_le_smoothOrder : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
  rw [show Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞) from rfl]
  exact WithTop.coe_le_coe.mpr le_top

/-- The product of a `C²` cutoff `χ`, vanishing off a closed set `s`, with a function `g` which
is `C²` on an open set `U ⊇ s`, is `C²`.  (The `C²` version of
`Work.FTS.StrongLWP.Sobolev.eqc_contDiff_two_mul_of_forall_notMem_eq_zero`, whose hypothesis on
`g` is `ContDiffOn ℝ ⊤`, i.e. analyticity.) -/
lemma contDiff_two_mul_of_contDiffOn_two {χ g : ℝ × ℝ → ℝ} {s U : Set (ℝ × ℝ)}
    (hsc : IsClosed s) (hsU : s ⊆ U) (hU : IsOpen U) (hχ : ContDiff ℝ 2 χ)
    (hχ0 : ∀ x ∉ s, χ x = 0) (hg : ContDiffOn ℝ 2 g U) :
    ContDiff ℝ 2 (fun x => χ x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · have hxR : x ∈ s := by
      have hsub : tsupport χ ⊆ s :=
        hsc.closure_subset_iff.mpr (Function.support_subset_iff'.mpr hχ0)
      exact hsub hx
    exact hχ.contDiffAt.mul (hg.contDiffAt (hU.mem_nhds (hsU hxR)))
  · have hev : (fun y => χ y * g y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The four entries (on the standard basis of `ℝ × ℝ`) of the second Fréchet derivative of a
curried function `C²` on an open set, in terms of the iterated slice derivatives `∂_z`, `∂_θ`:
the order-`2` version of `Work.FTS.StrongLWP.Sobolev.eqc_fderiv_fderiv_basis_apply`. -/
lemma basis_apply_two {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) U) {z θ : ℝ} (hz : (z, θ) ∈ U) :
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (1, 0)
        = Work.Spaces.pzIter 2 G z θ ∧
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (0, 1)
        = Work.Spaces.pz (Work.Spaces.pth G) z θ ∧
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (1, 0)
        = Work.Spaces.pth (Work.Spaces.pz G) z θ ∧
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (0, 1)
        = Work.Spaces.pthIter 2 G z θ := by
  have hdat : ∀ y ∈ U, DifferentiableAt ℝ (Function.uncurry G) y := fun y hy =>
    (hG.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hfdOn : ContDiffOn ℝ 1 (fderiv ℝ (Function.uncurry G)) U :=
    hG.fderiv_of_isOpen hU (by norm_num)
  have hdat2 : ∀ y ∈ U, DifferentiableAt ℝ (fderiv ℝ (Function.uncurry G)) y := fun y hy =>
    (hfdOn.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  set Az : ℝ → ℝ → ℝ := fun z' θ' => fderiv ℝ (Function.uncurry G) (z', θ') (1, 0) with hAzdef
  set Aθ : ℝ → ℝ → ℝ := fun z' θ' => fderiv ℝ (Function.uncurry G) (z', θ') (0, 1) with hAθdef
  have hAz_sm : ContDiffOn ℝ 1 (Function.uncurry Az) U := hfdOn.clm_apply contDiffOn_const
  have hAθ_sm : ContDiffOn ℝ 1 (Function.uncurry Aθ) U := hfdOn.clm_apply contDiffOn_const
  have hAz_diff : DifferentiableAt ℝ (Function.uncurry Az) (z, θ) :=
    (hAz_sm.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hAθ_diff : DifferentiableAt ℝ (Function.uncurry Aθ) (z, θ) :=
    (hAθ_sm.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hAz_eq : Set.EqOn (Function.uncurry Az) (Function.uncurry (Work.Spaces.pz G)) U := by
    intro y hy
    exact (Work.Spaces.pz_eq_fderiv (hdat y hy)).symm
  have hAθ_eq : Set.EqOn (Function.uncurry Aθ) (Function.uncurry (Work.Spaces.pth G)) U := by
    intro y hy
    exact (Work.Spaces.pth_eq_fderiv (hdat y hy)).symm
  have key : ∀ v : ℝ × ℝ,
      fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y v) (z, θ)
        = (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip v := by
    intro v
    rw [fderiv_clm_apply (hdat2 (z, θ) hz) (differentiableAt_const v), fderiv_const_apply]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (1, 0)
        = ((fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip (1, 0)) (1, 0) := by
          rw [ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y (1, 0)) (z, θ) (1, 0) := by
          rw [key]
      _ = Work.Spaces.pz Az z θ := (Work.Spaces.pz_eq_fderiv hAz_diff).symm
      _ = Work.Spaces.pz (Work.Spaces.pz G) z θ :=
          Work.Spaces.pz_congr_of_isOpen hU hAz_eq hz
      _ = Work.Spaces.pzIter 2 G z θ := rfl
  · calc (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (0, 1)
        = ((fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip (0, 1)) (1, 0) := by
          rw [ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y (0, 1)) (z, θ) (1, 0) := by
          rw [key]
      _ = Work.Spaces.pz Aθ z θ := (Work.Spaces.pz_eq_fderiv hAθ_diff).symm
      _ = Work.Spaces.pz (Work.Spaces.pth G) z θ :=
          Work.Spaces.pz_congr_of_isOpen hU hAθ_eq hz
  · calc (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (1, 0)
        = ((fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip (1, 0)) (0, 1) := by
          rw [ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y (1, 0)) (z, θ) (0, 1) := by
          rw [key]
      _ = Work.Spaces.pth Az z θ := (Work.Spaces.pth_eq_fderiv hAz_diff).symm
      _ = Work.Spaces.pth (Work.Spaces.pz G) z θ :=
          Work.FTS.StrongLWP.Sobolev.eqc_pth_congr_of_isOpen hU hAz_eq hz
  · calc (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (0, 1)
        = ((fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)).flip (0, 1)) (0, 1) := by
          rw [ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ (fun y => fderiv ℝ (Function.uncurry G) y (0, 1)) (z, θ) (0, 1) := by
          rw [key]
      _ = Work.Spaces.pth Aθ z θ := (Work.Spaces.pth_eq_fderiv hAθ_diff).symm
      _ = Work.Spaces.pth (Work.Spaces.pth G) z θ :=
          Work.FTS.StrongLWP.Sobolev.eqc_pth_congr_of_isOpen hU hAθ_eq hz
      _ = Work.Spaces.pthIter 2 G z θ := rfl

/-- The operator norm of the second Fréchet derivative of a curried `C²` function on an open set
is bounded by the sum of the absolute values of its four basis entries. -/
lemma norm_fderiv_fderiv_le_basis {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) U) {z θ : ℝ} (hz : (z, θ) ∈ U) :
    ‖fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ)‖ ≤
      |Work.Spaces.pzIter 2 G z θ| + |Work.Spaces.pz (Work.Spaces.pth G) z θ|
        + |Work.Spaces.pth (Work.Spaces.pz G) z θ| + |Work.Spaces.pthIter 2 G z θ| := by
  obtain ⟨h1, h2, h3, h4⟩ := basis_apply_two hU hG hz
  have h := Work.FTS.StrongLWP.Sobolev.eqc_opNorm_le_basis_sum₂
    (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ))
  have e1 : (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (1, 0)
      = Work.Spaces.pzIter 2 G z θ := h1
  have e2 : (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (1, 0)) (0, 1)
      = Work.Spaces.pz (Work.Spaces.pth G) z θ := h2
  have e3 : (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (1, 0)
      = Work.Spaces.pth (Work.Spaces.pz G) z θ := h3
  have e4 : (fderiv ℝ (fderiv ℝ (Function.uncurry G)) (z, θ) (0, 1)) (0, 1)
      = Work.Spaces.pthIter 2 G z θ := h4
  rw [e1, e2, e3, e4] at h
  exact h

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.SupPort.AuxMixSq.aesm_zslice_mixed_sq_w =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.SupPort.AuxMixSq

/-- The square of the radial weight `w` is continuous away from `0`. -/
private lemma continuousOn_w_sq :
    ContinuousOn (fun s : ℝ => (Work.Spaces.w s) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hnum : ContinuousOn (fun s : ℝ => ((1 + s) ^ 2) ^ 2) (Set.Ioi (0 : ℝ)) :=
    ((continuousOn_const.add continuousOn_id).pow 2).pow 2
  have hden : ContinuousOn (fun s : ℝ => (s ^ 2) ^ 2) (Set.Ioi (0 : ℝ)) :=
    (continuousOn_id.pow 2).pow 2
  refine (hnum.div hden (fun z hz => ?_)).congr (fun z _ => ?_)
  · exact pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz))
  · show (Work.Spaces.w z) ^ 2 = ((1 + z) ^ 2) ^ 2 / (z ^ 2) ^ 2
    rw [Work.Spaces.w, div_pow]

theorem aesm_zslice_mixed_sq_w {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (j i : ℕ) {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 (π / 2)) :
    MeasureTheory.AEStronglyMeasurable
      (fun s => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn
      (fun s : ℝ => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    (((hF.mixed j i).curry_z hσ).continuousOn.pow 2).mul continuousOn_w_sq
  rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
  exact hcont.aestronglyMeasurable measurableSet_Ioi

end Work.FTS.StrongEps.SupPort.AuxMixSq
end
-- ===== merged: Submission.Work.FTS.StrongEps.aemeasurable_mixed_family =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open MeasureTheory Set Filter
open scoped Real Topology

/-- **Derivative of a measurable family.**  If the slices `y ↦ g s y` are differentiable
at `x` for almost every `s`, with derivative `g' s`, and if the slices
`s ↦ g s y` are a.e. strongly measurable for all `y` in a neighbourhood of `x`, then
`s ↦ g' s` is a.e. strongly measurable.  (The derivative is the pointwise limit of the
slope quotients along `y = x + r/(n+2)`.) -/
private lemma aesm_of_hasDerivAt_family {μ : Measure ℝ} {g : ℝ → ℝ → ℝ} {g' : ℝ → ℝ}
    {x r : ℝ} (hr : 0 < r)
    (hmeas : ∀ y ∈ Set.Ioo (x - r) (x + r), AEStronglyMeasurable (fun s => g s y) μ)
    (hder : ∀ᵐ s ∂μ, HasDerivAt (fun y => g s y) (g' s) x) :
    AEStronglyMeasurable g' μ := by
  have hmem : ∀ n : ℕ, x + r / ((n : ℝ) + 2) ∈ Set.Ioo (x - r) (x + r) := by
    intro n
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hp : 0 < r / ((n : ℝ) + 2) := div_pos hr h2
    have hl : r / ((n : ℝ) + 2) < r := by
      rw [div_lt_iff₀ h2]; nlinarith
    exact ⟨by linarith, by linarith⟩
  have hxn : x ∈ Set.Ioo (x - r) (x + r) := ⟨by linarith, by linarith⟩
  have hu : ∀ n : ℕ, AEStronglyMeasurable
      (fun s => (r / ((n : ℝ) + 2))⁻¹ * (g s (x + r / ((n : ℝ) + 2)) - g s x)) μ := by
    intro n
    exact ((hmeas _ (hmem n)).sub (hmeas _ hxn)).const_mul _
  have htend : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hg : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
      exact tendsto_const_nhds.div_atTop hg
    · exact Eventually.of_forall (fun n => ne_of_gt (div_pos hr (by positivity)))
  have hlim : ∀ᵐ s ∂μ, Tendsto (fun n : ℕ =>
      (r / ((n : ℝ) + 2))⁻¹ * (g s (x + r / ((n : ℝ) + 2)) - g s x)) atTop (𝓝 (g' s)) :=
    hder.mono (fun s hs => by
      have h := hs.tendsto_slope_zero.comp htend
      simpa only [Function.comp_def, smul_eq_mul] using h)
  exact aestronglyMeasurable_of_tendsto_ae atTop hu hlim

/-- The `θ`-derivative of the `θ`-slice of a function `C^∞` on the open quadrant
(the `θ`-analogue of `Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice`). -/
private lemma SmoothOpen_hasDerivAt_slice_θ {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' : ℝ => F z θ') (Work.Spaces.pth F z θ) θ := by
  have h : DifferentiableOn ℝ (fun θ' : ℝ => F z θ') (Set.Ioo 0 (π / 2)) :=
    (hF.curry_θ hz).differentiableOn (by norm_num)
  have h2 := (h.differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
  simpa only [Work.Spaces.pth] using h2

/-- **The `D_z`-iterates of a family with measurable values.**  If every slice `G s` is
`C^∞` on the open quadrant (a.e. in `s`) and the values `s ↦ G s z θ` are a.e. strongly
measurable for every point of the open quadrant, then so are the values of all the
`D_z`-iterates. -/
private lemma aesm_DzIter_family {μ : Measure ℝ} {G : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ᵐ s ∂μ, Work.FTS.EllipticEst.SmoothOpen (G s))
    (hbase : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s => G s z θ) μ) :
    ∀ (j : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s => Work.Spaces.DzIter j (G s) z θ) μ := by
  intro j
  induction j with
  | zero => intro z θ hzθ; simpa using hbase z θ hzθ
  | succ j ih =>
      intro z θ hzθ
      obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
      have hfull : AEStronglyMeasurable
          (fun s => Work.Spaces.pz (Work.Spaces.DzIter j (G s)) z θ) μ := by
        refine aesm_of_hasDerivAt_family
          (g := fun s y => Work.Spaces.DzIter j (G s) y θ)
          (g' := fun s => Work.Spaces.pz (Work.Spaces.DzIter j (G s)) z θ)
          (x := z) (r := z / 2) (by linarith) ?_ ?_
        · intro y hy
          exact ih y θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨by linarith [hy.1], hθ0, hθ1⟩)
        · filter_upwards [hsm] with s hs
          exact (hs.DzIter j).hasDerivAt_slice ⟨hθ0, hθ1⟩ hz0
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.Dz] using hfull.const_mul z

/-- **The `D_θ`-iterates of a family with measurable values** (the companion of
`aesm_DzIter_family`). -/
private lemma aesm_DthIter_family {μ : Measure ℝ} {G : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ᵐ s ∂μ, Work.FTS.EllipticEst.SmoothOpen (G s))
    (hbase : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s => G s z θ) μ) :
    ∀ (i : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s => Work.Spaces.DthIter i (G s) z θ) μ := by
  intro i
  induction i with
  | zero => intro z θ hzθ; simpa using hbase z θ hzθ
  | succ i ih =>
      intro z θ hzθ
      obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
      have hfull : AEStronglyMeasurable
          (fun s => Work.Spaces.pth (Work.Spaces.DthIter i (G s)) z θ) μ := by
        refine aesm_of_hasDerivAt_family
          (g := fun s y => Work.Spaces.DthIter i (G s) z y)
          (g' := fun s => Work.Spaces.pth (Work.Spaces.DthIter i (G s)) z θ)
          (x := θ) (r := min θ (π / 2 - θ) / 2) ?_ ?_ ?_
        · have h1 : 0 < θ := hθ0
          have h2 : 0 < π / 2 - θ := by linarith
          exact div_pos (lt_min h1 h2) two_pos
        · intro y hy
          have hy0 : 0 < y := by
            have := min_le_left θ (π / 2 - θ)
            linarith [hy.1]
          have hy1 : y < π / 2 := by
            have := min_le_right θ (π / 2 - θ)
            linarith [hy.2]
          exact ih z y (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hy0, hy1⟩)
        · filter_upwards [hsm] with s hs
          exact SmoothOpen_hasDerivAt_slice_θ (hs.DthIter i) hz0 ⟨hθ0, hθ1⟩
      simpa only [Work.Spaces.DthIter_succ, Work.Spaces.Dth] using
        hfull.const_mul (Real.sin (2 * θ))

/-- A property holding at every point of `[0,T]` holds a.e. for the restricted measure. -/
private lemma ae_restrict_Icc_of_forall {T : ℝ} {p : ℝ → Prop}
    (h : ∀ s ∈ Set.Icc (0 : ℝ) T, p s) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), p s := by
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall (fun s hs => h s hs)

theorem aemeasurable_mixed_family {T : ℝ} {H : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => H s z θ) (Set.Icc (0 : ℝ) T)) :
    ∀ (j i : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) := by
  intro j i z θ hzθ
  have hsm_ae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Work.FTS.EllipticEst.SmoothOpen (H s) :=
    ae_restrict_Icc_of_forall (fun s hs => hsm s hs)
  have hbaseH : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => H s z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun z θ hzθ => (hcont z θ hzθ).aestronglyMeasurable measurableSet_Icc
  have hDth := aesm_DthIter_family (G := H) hsm_ae hbaseH i
  have hsmG : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Spaces.DthIter i (H s) z θ) :=
    hsm_ae.mono (fun s hs => hs.DthIter i)
  have hbaseG : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.DthIter i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) := fun z θ hzθ => hDth z θ hzθ
  have h := aesm_DzIter_family (G := fun s => Work.Spaces.DthIter i (H s))
    hsmG hbaseG j z θ hzθ
  simpa only [Work.Spaces.mixed] using h

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.Degen.HkSqZeroOnQuad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.Degen

/-- The weight `w(z)/sin(2θ)^{η/2}` multiplying `D_z^0 h = h` in the `ℋ^k`-integrand. -/
private def HWt (z θ : ℝ) : ℝ :=
  Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)

private lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The product `h · HWt` is continuous on the open quadrant: both factors are (the weight is the
honest continuous weight `w(z)·sin(2θ)^{-η/2}` there). -/
private lemma continuousOn_mul_HWt {h : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen h) :
    ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2 * HWt p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hsm.continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => HWt p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hw := Work.FTS.EllipticEst.continuousOn_wdivsin_Q0
    simpa only [HWt, Work.FTS.EllipticEst.Q0] using hw
  exact h1.mul h2

/-- **`L²`-membership of the `D_z^0`-slot.**  The square of `h · HWt` is dominated pointwise by
the `ℋ^k`-integrand, whose angular slices and slice-integral are integrable by `HkMem`; the
a.e.-strong measurability comes from continuity on the open quadrant, and the single slice
`z = 0` is handled separately (there the weight `w` vanishes). -/
private lemma L2Mem_mul_HWt {α : ℝ} {k : ℕ} {h : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α k h) :
    Work.Spaces.L2Mem (fun z θ => h z θ * HWt z θ) := by
  have hcont := continuousOn_mul_HWt hsm
  constructor
  · intro z hz
    have h := Work.FTS.EllipticEst.integrableOn_zSummand α k hsm hm 0 (Nat.zero_le k) hz
    simpa only [HWt, Work.Spaces.DzIter_zero] using h
  · have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => (h p.1 p.2 * HWt p.1 p.2) ^ 2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ (hcont.pow 2)
    refine Integrable.mono' hm.2 hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => sq_nonneg _) (hm.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => by
          simpa only [HWt, Work.Spaces.DzIter_zero] using
            Work.Spaces.sq_le_HkIntegrand_z α k h z θ 0 (Nat.zero_le k)))

/-- The Lebesgue measure of a real interval `[a,b]`. -/
private lemma volume_Icc_real {a b : ℝ} (h : a ≤ b) :
    (MeasureTheory.volume : MeasureTheory.Measure ℝ).real (Set.Icc a b) = b - a := by
  have h1 : (MeasureTheory.volume : MeasureTheory.Measure ℝ).real (Set.Icc a b)
      = ((MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Icc a b)).toReal := rfl
  rw [h1, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]

/-- **A nonnegative continuous function on the open quadrant with vanishing `L²`-integral
vanishes on the open quadrant.**  This is the open-quadrant form of
`Work.FTS.EllipticEst.eq_zero_of_L2Sq_eq_zero`: the box used in the contradiction is taken so
small that it stays strictly inside the quadrant, where continuity is available. -/
theorem eq_zero_of_L2Sq_eq_zero_open {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.L2Mem g)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzero : Work.Spaces.L2Sq g = 0) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → g z θ = 0 := by
  intro z0 θ0 hz0 hθ0 hθ0π
  by_contra hne
  -- continuity of `g` at `(z0,θ0)`, which is interior to the open quadrant
  have hct : ContinuousAt (fun p : ℝ × ℝ => g p.1 p.2) (z0, θ0) :=
    hcont.continuousAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz0, hθ0, hθ0π⟩)
  have hε2 : 0 < |g z0 θ0| / 2 := by have := abs_pos.mpr hne; linarith
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hct (|g z0 θ0| / 2) hε2
  -- a box of half-width `ε/2`, small enough to stay inside the quadrant and the `δ`-ball
  set ε : ℝ := min δ (min (z0 / 2) (min (θ0 / 2) ((Real.pi / 2 - θ0) / 2))) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    exact lt_min hδpos (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hεδ : ε ≤ δ := by rw [hε]; exact min_le_left _ _
  have hεz : ε ≤ z0 / 2 := by
    rw [hε]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεθ : ε ≤ θ0 / 2 := by
    rw [hε]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεπ : ε ≤ (Real.pi / 2 - θ0) / 2 := by
    rw [hε]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  set zlo : ℝ := z0 - ε / 2 with hzlo
  set zhi : ℝ := z0 + ε / 2 with hzhi
  set tlo : ℝ := θ0 - ε / 2 with htlo
  set thi : ℝ := θ0 + ε / 2 with hthi
  have hzlo0 : 0 ≤ zlo := by rw [hzlo]; linarith
  have htlo0 : 0 ≤ tlo := by rw [htlo]; linarith
  have hthi_pi : thi ≤ Real.pi / 2 := by rw [hthi]; linarith
  have hzbox : Set.Icc zlo zhi ⊆ Work.Spaces.Iz := fun z hz => le_trans hzlo0 hz.1
  have htbox : Set.Icc tlo thi ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_trans htlo0 hθ.1, le_trans hθ.2 hthi_pi⟩
  have hzlo_lt : zlo < zhi := by rw [hzlo, hzhi]; linarith
  have htlo_lt : tlo < thi := by rw [htlo, hthi]; linarith
  -- on the box, `|g| ≥ |g z0 θ0| / 2`
  have hpoint : ∀ z ∈ Set.Icc zlo zhi, ∀ θ ∈ Set.Icc tlo thi,
      (|g z0 θ0| / 2) ^ 2 ≤ (g z θ) ^ 2 := by
    intro z hz θ hθ
    have hz1 : z0 - ε / 2 ≤ z := by rw [hzlo] at hz; exact hz.1
    have hz2 : z ≤ z0 + ε / 2 := by rw [hzhi] at hz; exact hz.2
    have ht1 : θ0 - ε / 2 ≤ θ := by rw [htlo] at hθ; exact hθ.1
    have ht2 : θ ≤ θ0 + ε / 2 := by rw [hthi] at hθ; exact hθ.2
    have hdist : dist (z, θ) (z0, θ0) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      refine ⟨?_, ?_⟩ <;> · rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hd : dist (g z θ) (g z0 θ0) < |g z0 θ0| / 2 := hδ hdist
    have h2 : |g z θ - g z0 θ0| < |g z0 θ0| / 2 := by
      simpa [Real.dist_eq] using hd
    have h3 : |g z0 θ0| ≤ |g z0 θ0 - g z θ| + |g z θ| := by
      calc |g z0 θ0| = |(g z0 θ0 - g z θ) + g z θ| := by ring_nf
        _ ≤ |g z0 θ0 - g z θ| + |g z θ| := abs_add_le _ _
    rw [abs_sub_comm] at h3
    have h4 : |g z0 θ0| / 2 < |g z θ| := by linarith
    have h5 : (|g z0 θ0| / 2) ^ 2 ≤ |g z θ| ^ 2 := by
      have h6 : |g z0 θ0| / 2 ≤ |g z θ| := le_of_lt h4
      nlinarith [abs_nonneg (g z0 θ0), abs_nonneg (g z θ)]
    rwa [sq_abs] at h5
  -- the box bound on the iterated integral
  have hstep1 : ∫ z in Set.Icc zlo zhi, (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
      ≤ Work.Spaces.L2Sq g := by
    rw [Work.Spaces.L2Sq]
    exact MeasureTheory.setIntegral_mono_set hmem.2
      (Filter.Eventually.of_forall (fun z => integral_nonneg (fun θ => sq_nonneg _)))
      (Filter.Eventually.of_forall fun z hz => hzbox hz)
  have hstep2 : ∫ z in Set.Icc zlo zhi, ((|g z0 θ0| / 2) ^ 2 * (thi - tlo))
      ≤ ∫ z in Set.Icc zlo zhi, (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _)
        (by linarith [htlo_lt])) (hmem.2.mono_set hzbox) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun z hz => ?_
    have h1 : (∫ θ in Set.Icc tlo thi, (|g z0 θ0| / 2) ^ 2)
        ≤ ∫ θ in Set.Icc tlo thi, (g z θ) ^ 2 :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)
        ((hmem.1 z (hzbox hz)).mono_set (fun θ hθ => htbox hθ))
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hpoint z hz θ hθ))
    have h2 : (∫ θ in Set.Icc tlo thi, (g z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 :=
      MeasureTheory.setIntegral_mono_set (hmem.1 z (hzbox hz))
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)
        (Filter.Eventually.of_forall fun θ hθ => htbox hθ)
    have h3 : (|g z0 θ0| / 2) ^ 2 * (thi - tlo)
        = ∫ θ in Set.Icc tlo thi, (|g z0 θ0| / 2) ^ 2 := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul,
        volume_Icc_real (le_of_lt htlo_lt)]
      ring
    rw [h3]
    exact le_trans h1 h2
  have hchain : (|g z0 θ0| / 2) ^ 2 * (thi - tlo) * (zhi - zlo) ≤ Work.Spaces.L2Sq g := by
    have h3 := hstep2
    rw [MeasureTheory.setIntegral_const, smul_eq_mul,
      volume_Icc_real (le_of_lt hzlo_lt)] at h3
    linarith [hstep1]
  have hpos : 0 < (|g z0 θ0| / 2) ^ 2 * (thi - tlo) * (zhi - zlo) := by
    have h1 : 0 < (|g z0 θ0| / 2) ^ 2 := by
      have := abs_pos.mpr hne
      positivity
    have h2 : 0 < thi - tlo := by linarith [htlo_lt]
    have h3 : 0 < zhi - zlo := by linarith [hzlo_lt]
    exact mul_pos (mul_pos h1 h2) h3
  rw [hzero] at hchain
  linarith

/-- **The vanishing of the `ℋ^k`-norm forces the profile to vanish on the open quadrant.**

`HkIntegrand` is a sum of squares whose `i = 0` summand in the pure `D_z`-sum is exactly
`(h z θ · w(z)/sin(2θ)^{η/2})²`, because `D_z^0 h = h`; hence `HkSq α k h = 0` gives the honest
vanishing of the iterated `L²`-integral of that summand (`L2Sq_DzIter_le_HkSq` at `i = 0`,
`HkMem` supplies the honesty).  The weight `w(z)/sin(2θ)^{η/2}` never vanishes on the open
quadrant, so the summand vanishes there by the box argument of
`eq_zero_of_L2Sq_eq_zero_open` (continuity on the open quadrant comes from `SmoothOpen`). -/
theorem HkSqZeroOnQuad {α : ℝ} {k : ℕ} {h : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α k h)
    (h0 : Work.Spaces.HkSq α k h = 0) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → h z θ = 0 := by
  -- the `D_z^0`-slot of the `ℋ^k`-integrand
  have hL2 : Work.Spaces.L2Sq (fun z θ => h z θ * HWt z θ) = 0 := by
    have hle := Work.Spaces.L2Sq_DzIter_le_HkSq α k h hm 0 (Nat.zero_le k)
    rw [h0] at hle
    have hle' : Work.Spaces.L2Sq (fun z θ => h z θ * HWt z θ) ≤ 0 := by
      simpa only [HWt, Work.Spaces.DzIter_zero] using hle
    have hnn : 0 ≤ Work.Spaces.L2Sq (fun z θ => h z θ * HWt z θ) := by
      rw [Work.Spaces.L2Sq]
      exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
    linarith
  have hmem' : Work.Spaces.L2Mem (fun z θ => h z θ * HWt z θ) := L2Mem_mul_HWt hsm hm
  have hcont' : ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2 * HWt p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_mul_HWt hsm
  have hzero := eq_zero_of_L2Sq_eq_zero_open hmem' hcont' hL2
  intro z θ hz hθ hθπ
  have hWne : HWt z θ ≠ 0 := by
    rw [HWt]
    refine div_ne_zero ?_
      (ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo ⟨hθ, hθπ⟩) _))
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  exact (mul_eq_zero.mp (hzero z θ hz hθ hθπ)).resolve_right hWne

end Work.FTS.StrongPersist.Degen
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.wip_Dz_ibp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `z`-integration by parts in the `wip` normalisation, with the boundary terms derived

`Work.Coercivity.wip ρ (Dz h) h = ∫_z ∫_θ (Dz h) h ρ` is computed by integrating by parts in
the radial variable `z` on `(0,∞)`: with `ρ = Φ(z) σ(θ)` the derivative of the primitive
`z ↦ (z Φ z) h(z,θ)² σ θ` splits into `2 (Dz h) h Φ σ + h² ∂_z(zΦ) σ`, so

  `wip (Φ σ) (Dz h) h = -(1/2) ∫_z ∫_θ h² ∂_z(zΦ) σ`

*provided the boundary terms vanish*.  None of the boundary limits is a hypothesis here: the
three integrability assumptions (of `h²Φσ`, of `(Dz h) h Φσ` and of `h² ∂_z(zΦ) σ`) already
force them.  The primitive has an integrable derivative, so it has both limits
(`zibp_lim_atTop`, `zibp_lim_nearZero`), and each limit must be `0` because `z ↦ z g z` with
`g = h²Φσ ∈ L¹` cannot be bounded below by a positive constant on a half-line.

The proof is carried out slice by slice in `θ` (for a.e. angle, where the slice of a
`SmoothOpen` function is `C^∞` in `z`) and assembled with Fubini.

## Conventions

`Iz = [0,∞)`, `Iθ = [0,π/2]`, `dz dθ` measure, `Dz f = z ∂_z f`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- `𝓝[≥] a` from `𝓝[>] a`: if `F → b` along `𝓝[>] a` and `F a = b`, then `F` tends to `F a`
along `𝓝[Ici a] a`.  (Local copy of the argument used in
`Work.FTS.StrongPersist.N6Trans.L6Flux.zibp_Ioi_of_integrable`.) -/
private theorem wip_Dz_tendsto_Ici_of_Ioi {F : ℝ → ℝ} {a b : ℝ}
    (h : Tendsto F (nhdsWithin a (Set.Ioi a)) (nhds b)) (hb : F a = b) :
    Tendsto F (nhdsWithin a (Set.Ici a)) (nhds (F a)) := by
  rw [hb]
  intro t ht
  obtain ⟨u, hau, hu⟩ := (nhdsGT_basis a).mem_iff.mp (h ht)
  refine (nhdsGE_basis_Ico a).mem_iff.mpr ⟨u, hau, ?_⟩
  rintro x ⟨hax, hxu⟩
  rcases eq_or_lt_of_le hax with rfl | hlt
  · simp only [Set.mem_preimage]
    rw [hb]
    exact mem_of_mem_nhds ht
  · exact hu ⟨hlt, hxu⟩

/-- `Iz = [0,∞)` and `(0,∞)` differ by the null set `{0}`. -/
private theorem wip_Dz_Iz_ae_eq_Ioi :
    Work.Spaces.Iz =ᵐ[(volume : Measure ℝ)] Set.Ioi (0 : ℝ) :=
  MeasureTheory.Ioi_ae_eq_Ici.symm

/-- The restricted measures of `Iz` and `(0,∞)` agree. -/
private theorem wip_Dz_restrict_Iz_eq_restrict_Ioi :
    (volume.restrict Work.Spaces.Iz : Measure ℝ) = volume.restrict (Set.Ioi (0 : ℝ)) :=
  MeasureTheory.Measure.restrict_congr_set wip_Dz_Iz_ae_eq_Ioi

/-- Almost every angle of `Iθ` lies in the *open* interval. -/
private theorem wip_Dz_ae_restrict_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have hset : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ := MeasureTheory.Ioo_ae_eq_Icc
  rw [← MeasureTheory.Measure.restrict_congr_set hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## The `z`-derivative of the primitive `z ↦ (z Φ(z)) h(z,θ)² σ(θ)` -/

/-- The pointwise `z`-derivative of the primitive `z ↦ (z·Φ z)·(h z θ)²·σ θ` at `z > 0` and
`θ ∈ (0,π/2)`: it splits into `2` times the `wip`-integrand `Dz h · h · Φ · σ` plus the
"derived coefficient" term `h² · ∂_z(zΦ) · σ`. -/
private theorem wip_Dz_prim_hasDerivAt {h : ℝ → ℝ → ℝ} {Φ σ : ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hΦ : ContDiffOn ℝ 1 Φ (Set.Ioi 0)) {θ z : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (hz : 0 < z) :
    HasDerivAt (fun z' => (z' * Φ z') * (h z' θ ^ 2 * σ θ))
      (h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ
        + 2 * (z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ)) z := by
  have hΦd : DifferentiableAt ℝ Φ z :=
    (hΦ.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hφ : HasDerivAt (fun z' : ℝ => z' * Φ z')
      (deriv (fun z' : ℝ => z' * Φ z') z) z :=
    (differentiableAt_id.mul hΦd).hasDerivAt
  have hV : HasDerivAt (fun z' : ℝ => h z' θ) (deriv (fun z' : ℝ => h z' θ) z) z :=
    hsm.hasDerivAt_slice hθ hz
  have hV2 : HasDerivAt (fun z' : ℝ => h z' θ ^ 2)
      (2 * h z θ * deriv (fun z' : ℝ => h z' θ) z) z := by
    have h' := hV.pow 2
    have hfun : (fun z' : ℝ => h z' θ ^ 2) = (fun z' : ℝ => h z' θ) ^ 2 := by
      funext z'; rfl
    rw [hfun]
    refine h'.congr_deriv ?_
    norm_num
  have h3 : HasDerivAt (fun z' : ℝ => h z' θ ^ 2 * σ θ)
      ((2 * h z θ * deriv (fun z' : ℝ => h z' θ) z) * σ θ) z := hV2.mul_const (σ θ)
  have h4 : HasDerivAt (fun z' : ℝ => (z' * Φ z') * (h z' θ ^ 2 * σ θ))
      (deriv (fun z' : ℝ => z' * Φ z') z * (h z θ ^ 2 * σ θ)
        + (z * Φ z) * ((2 * h z θ * deriv (fun z' : ℝ => h z' θ) z) * σ θ)) z :=
    hφ.mul h3
  refine h4.congr_deriv ?_
  ring

/-! ## The `z`-integration by parts on a single `θ`-slice -/

/-- **`z`-integration by parts on one `θ`-slice.**  For `θ ∈ (0,π/2)` and the two integrands
`(Dz h) h Φσ` and `h² ∂_z(zΦ) σ` integrable on `(0,∞)` (together with `h²Φσ ∈ L¹`, which is
what forces both boundary terms to vanish),
`∫_0^∞ (Dz h) h Φσ = -(1/2) ∫_0^∞ h² ∂_z(zΦ) σ`. -/
private theorem wip_Dz_slice_ibp {h : ℝ → ℝ → ℝ} {Φ σ : ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hΦ : ContDiffOn ℝ 1 Φ (Set.Ioi 0)) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hA : IntegrableOn (fun z => Work.Spaces.Dz h z θ * h z θ * Φ z * σ θ) (Set.Ioi 0))
    (hB : IntegrableOn (fun z => h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ)
      (Set.Ioi 0))
    (hG : IntegrableOn (fun z => h z θ ^ 2 * Φ z * σ θ) (Set.Ioi 0)) :
    ∫ z in Set.Ioi 0, Work.Spaces.Dz h z θ * h z θ * Φ z * σ θ
      = -(1 / 2) * ∫ z in Set.Ioi 0, h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ := by
  set ψ : ℝ → ℝ := fun z => (z * Φ z) * (h z θ ^ 2 * σ θ) with hψ
  have hψ0 : ψ 0 = 0 := by
    simp only [hψ]
    ring
  -- the derivative of the primitive is `deriv ψ`
  have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt ψ (deriv ψ z) z := by
    intro z hz
    have h := wip_Dz_prim_hasDerivAt (σ := σ) hsm hΦ hθ hz
    exact h.congr_deriv h.deriv.symm
  -- its explicit value
  have hderiv_eq : ∀ z ∈ Set.Ioi (0 : ℝ), deriv ψ z
      = h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ
        + 2 * (z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ) := by
    intro z hz
    exact (wip_Dz_prim_hasDerivAt (σ := σ) hsm hΦ hθ hz).deriv
  -- the `wip`-integrand, written with the plain partial derivative
  have hA' : IntegrableOn
      (fun z => z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ) (Set.Ioi 0) := hA
  have hB' : Integrable (fun z => h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ)
      (volume.restrict (Set.Ioi 0)) := hB
  have h2A : IntegrableOn
      (fun z => 2 * (z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ))
      (Set.Ioi 0) :=
    (show Integrable (fun z => z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ)
      (volume.restrict (Set.Ioi 0)) from hA').const_mul 2
  have h2A' : Integrable
      (fun z => 2 * (z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ))
      (volume.restrict (Set.Ioi 0)) := h2A
  -- the derivative is integrable
  have hint : IntegrableOn (deriv ψ) (Set.Ioi 0) := by
    have hsum : IntegrableOn (fun z => (h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ)
        + 2 * (z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ)) (Set.Ioi 0) :=
      hB.add h2A
    refine hsum.congr_fun_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact (hderiv_eq z hz).symm
  -- the `L¹`-bound needed for the boundary vanishing
  have hG2 : IntegrableOn (fun z => (Real.sqrt |Φ z * h z θ ^ 2 * σ θ|) ^ 2) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun z => |h z θ ^ 2 * Φ z * σ θ|) (Set.Ioi 0) :=
      (show Integrable (fun z => h z θ ^ 2 * Φ z * σ θ) (volume.restrict (Set.Ioi 0))
        from hG).abs
    refine h1.congr_fun (fun z _ => ?_) measurableSet_Ioi
    rw [Real.sq_sqrt (abs_nonneg (Φ z * h z θ ^ 2 * σ θ))]
    exact congrArg abs (by ring)
  have hbd : ∀ z, 0 ≤ z →
      |ψ z| ≤ 1 * (z * (Real.sqrt |Φ z * h z θ ^ 2 * σ θ|) ^ 2) := by
    intro z hz
    have hsqrt : (Real.sqrt |Φ z * h z θ ^ 2 * σ θ|) ^ 2 = |Φ z * h z θ ^ 2 * σ θ| :=
      Real.sq_sqrt (abs_nonneg _)
    rw [hsqrt, one_mul]
    have hL : |ψ z| = z * |Φ z * h z θ ^ 2 * σ θ| := by
      simp only [hψ, abs_mul, abs_of_nonneg hz]
      ring
    rw [hL]
  -- the two boundary limits, derived (not assumed)
  have htop : Tendsto ψ atTop (nhds 0) :=
    Work.FTS.H2.Transport3Aux.MismatchBad.zibp_lim_atTop
      (ψ := ψ) (ψ' := deriv ψ) (G := fun z => Real.sqrt |Φ z * h z θ ^ 2 * σ θ|)
      (C := 1) one_pos hderiv hint hbd hG2
  have h0 : Tendsto ψ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Work.FTS.H2.Transport3Aux.MismatchBad.zibp_lim_nearZero
      (ψ := ψ) (ψ' := deriv ψ) (G := fun z => Real.sqrt |Φ z * h z θ ^ 2 * σ θ|)
      (C := 1) one_pos hderiv hint hbd hG2
  have hcont : ContinuousWithinAt ψ (Set.Ici 0) 0 :=
    wip_Dz_tendsto_Ici_of_Ioi h0 hψ0
  -- the fundamental theorem of calculus on `(0,∞)`
  have hFTC : ∫ z in Set.Ioi 0, deriv ψ z = 0 := by
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htop, hψ0,
      sub_zero]
  have hsplit : ∫ z in Set.Ioi 0, deriv ψ z
      = (∫ z in Set.Ioi 0, h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ)
        + 2 * (∫ z in Set.Ioi 0, z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ) := by
    rw [show (∫ z in Set.Ioi 0, deriv ψ z)
        = ∫ z in Set.Ioi 0, ((h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ)
            + 2 * (z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ)) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => hderiv_eq z hz)]
    rw [MeasureTheory.integral_add hB' h2A', MeasureTheory.integral_const_mul]
  have hgoal : ∫ z in Set.Ioi 0, z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ
      = -(1 / 2) * ∫ z in Set.Ioi 0,
          h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ := by
    linarith [hFTC, hsplit]
  exact hgoal

/-! ## The main theorem -/

theorem wip_Dz_ibp {h : ℝ → ℝ → ℝ} {Φ σ : ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hΦ : ContDiffOn ℝ 1 Φ (Set.Ioi 0))
    (hint1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => h z θ ^ 2 * Φ z * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz h z θ * h z θ * Φ z * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint3 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z θ => Φ z * σ θ) (Work.Spaces.Dz h) h
      = -(1 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ) := by
  set μ : MeasureTheory.Measure ℝ := volume.restrict Work.Spaces.Iz with hμ
  set ν : MeasureTheory.Measure ℝ := volume.restrict Work.Spaces.Iθ with hν
  have hmeas : μ.prod ν = (volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [hμ, hν, MeasureTheory.Measure.prod_restrict,
      ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  -- the bundled integrands, viewed on the product
  set A : ℝ × ℝ → ℝ :=
    fun p => Work.Spaces.Dz h p.1 p.2 * h p.1 p.2 * Φ p.1 * σ p.2 with hAdef
  set B : ℝ × ℝ → ℝ :=
    fun p => h p.1 p.2 ^ 2 * deriv (fun z' => z' * Φ z') p.1 * σ p.2 with hBdef
  set Gg : ℝ × ℝ → ℝ := fun p => h p.1 p.2 ^ 2 * Φ p.1 * σ p.2 with hGdef
  have hAint : Integrable A (μ.prod ν) := by
    rw [hmeas]
    exact hint2
  have hBint : Integrable B (μ.prod ν) := by
    rw [hmeas]
    exact hint3
  have hGint : Integrable Gg (μ.prod ν) := by
    rw [hmeas]
    exact hint1
  -- the `wip` integral is the product-measure integral of `A`
  have hwip : Work.Coercivity.wip (fun z θ => Φ z * σ θ) (Work.Spaces.Dz h) h
      = ∫ z, ∫ θ, A (z, θ) ∂ν ∂μ := by
    simp only [Work.Coercivity.wip]
    rw [hμ, hν]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [A]
    ring
  -- the slice identity, for a.e. angle
  have hslice : ∀ᵐ θ ∂ν,
      (∫ z, A (z, θ) ∂μ) = -(1 / 2) * (∫ z, B (z, θ) ∂μ) := by
    filter_upwards [hAint.prod_left_ae, hBint.prod_left_ae, hGint.prod_left_ae,
      wip_Dz_ae_restrict_Iθ_mem_Ioo] with θ hIA hIB hIG hθIo
    have hIA' : IntegrableOn (fun z => Work.Spaces.Dz h z θ * h z θ * Φ z * σ θ)
        (Set.Ioi 0) := by
      rw [hμ, wip_Dz_restrict_Iz_eq_restrict_Ioi] at hIA
      exact hIA
    have hIB' : IntegrableOn (fun z => h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ)
        (Set.Ioi 0) := by
      rw [hμ, wip_Dz_restrict_Iz_eq_restrict_Ioi] at hIB
      exact hIB
    have hIG' : IntegrableOn (fun z => h z θ ^ 2 * Φ z * σ θ) (Set.Ioi 0) := by
      rw [hμ, wip_Dz_restrict_Iz_eq_restrict_Ioi] at hIG
      exact hIG
    have hgoal := wip_Dz_slice_ibp hsm hΦ hθIo hIA' hIB' hIG'
    rw [hμ, wip_Dz_restrict_Iz_eq_restrict_Ioi]
    exact hgoal
  calc Work.Coercivity.wip (fun z θ => Φ z * σ θ) (Work.Spaces.Dz h) h
      = ∫ z, ∫ θ, A (z, θ) ∂ν ∂μ := hwip
    _ = ∫ p, A p ∂(μ.prod ν) := (MeasureTheory.integral_prod A hAint).symm
    _ = ∫ θ, ∫ z, A (z, θ) ∂μ ∂ν := MeasureTheory.integral_prod_symm A hAint
    _ = ∫ θ, -(1 / 2) * (∫ z, B (z, θ) ∂μ) ∂ν :=
          MeasureTheory.integral_congr_ae hslice
    _ = -(1 / 2) * ∫ θ, ∫ z, B (z, θ) ∂μ ∂ν := by
          rw [MeasureTheory.integral_const_mul]
    _ = -(1 / 2) * ∫ p, B p ∂(μ.prod ν) := by
          rw [(MeasureTheory.integral_prod_symm B hBint).symm]
    _ = -(1 / 2) * (∫ z, ∫ θ, B (z, θ) ∂ν ∂μ) := by
          rw [MeasureTheory.integral_prod B hBint]
    _ = -(1 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ) := by
          rw [hμ, hν]

end Work.FTS.StrongPersist.H6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotProd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false

/-! ## Pointwise facts on `Iθ` and on the open quadrant -/

/-- `sin (2θ) ≥ 0` on `Iθ = [0, π/2]`. -/
private theorem sin_two_nonneg_Iθ_prv {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin (2θ) > 0` on the open quadrant. -/
private theorem sin_two_pos_Q0 {p : ℝ × ℝ}
    (hp : p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ))) :
    0 < Real.sin (2 * p.2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])

/-- `(a ^ p) ^ 2 = a ^ (2p)` for `a ≥ 0`. -/
private theorem sq_rpow_mul_two {a : ℝ} (ha : 0 ≤ a) (p : ℝ) :
    (a ^ p) ^ 2 = a ^ (p * 2) := by
  rw [← Real.rpow_natCast (a ^ p) 2]
  exact (Real.rpow_mul ha p 2).symm

/-- Squaring the weight `W = w · sin(2θ)^{-γ/2}` gives the raw weight
`w² · sin(2θ)^{-γ}` of the energy. -/
private theorem Wt_sq_eq (α z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have h1 : Work.Spaces.Wt α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [h1, mul_pow, sq_rpow_mul_two (sin_two_nonneg_Iθ_prv hθ) (-(Work.Spaces.gam α / 2)),
    show (-(Work.Spaces.gam α / 2)) * 2 = -(Work.Spaces.gam α) by ring]

/-- Squaring the weight `w / sin(2θ)^{η/2}` gives the raw weight `w² · sin(2θ)^{-η}`. -/
private theorem whz_sq_eq (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have ha := sin_two_nonneg_Iθ_prv hθ
  have h1 : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rw [div_eq_mul_inv, Real.rpow_neg ha (Work.Spaces.eta / 2)]
  rw [h1, mul_pow, sq_rpow_mul_two ha (-(Work.Spaces.eta / 2)),
    show (-(Work.Spaces.eta / 2)) * 2 = -(Work.Spaces.eta) by ring]

/-- The `γ`-slot integrand is the square of the weighted mixed derivative. -/
private theorem mixed_slot_eq (α z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) (X : ℝ) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * X ^ 2
      = (X * Work.Spaces.Wt α z θ) ^ 2 := by
  rw [mul_pow, Wt_sq_eq α z θ hθ]
  ring

/-- The `η`-slot integrand is the square of the weighted `D_z`-derivative. -/
private theorem z_slot_eq (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) (X : ℝ) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * X ^ 2
      = (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [mul_pow, whz_sq_eq z θ hθ]
  ring

/-- Almost every point of the product measure has its angular coordinate in `Iθ`. -/
private theorem ae_snd_mem_Iθ :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      p.2 ∈ Work.Spaces.Iθ := by
  rw [MeasureTheory.Measure.prod_restrict]
  exact (MeasureTheory.ae_restrict_mem
    (show MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from
      measurableSet_Ici.prod measurableSet_Icc)).mono (fun _ hp => hp.2)

/-! ## Continuity on the open quadrant -/

private theorem continuousOn_w_sq_Q0_prv :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := by
  have h : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by
    funext p; simp only [Work.Spaces.w]
  rw [h]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))).pow 2

private theorem continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := by
  have h : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; simp only [Work.Spaces.w]
  rw [h]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

private theorem continuousOn_sinpow_Q0 (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ q)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_Q0 hp)))

private theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := by
  have h : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [h]
  exact continuousOn_w_Q0.mul (continuousOn_sinpow_Q0 (-(Work.Spaces.gam α / 2)))

private theorem continuousOn_wdivsin_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1
        / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) :=
  continuousOn_w_Q0.div (continuousOn_sinpow_Q0 (Work.Spaces.eta / 2))
    (fun _p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_Q0 hp) _))

private theorem aesm_mixed_slot (α : ℝ) {j i : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (ContinuousOn.pow (((hf.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)) 2)

private theorem aesm_z_slot {i : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter i f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (ContinuousOn.pow (((hf.DzIter i).continuousOn).mul continuousOn_wdivsin_Q0) 2)

/-! ## The mixed slots -/

/-- **The `γ`-weighted mixed slots are jointly integrable.** -/
theorem mixedSlotProd (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α n f) :
    ∀ j i : ℕ, 1 ≤ i → i + j ≤ n → MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  intro j i hi hij
  have hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    aesm_mixed_slot α hsm
  -- the angular slices are dominated by the `HkIntegrand`-slice
  have hslice : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Integrable (fun θ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hAE.prodMk_left,
      ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hzm hz
    refine Integrable.mono' (hm.1 z hz) hzm ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
      with θ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α n f z θ i j hi hij
  -- the radial marginal is integrable, by the same domination
  have houter : Integrable
      (fun z => ∫ θ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict Work.Spaces.Iz) := by
    refine Integrable.mono' hm.2 hAE.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hm.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α n f z θ i j hi hij))
  -- Tonelli turns the iterated integral into the product integral
  have hnice : Integrable
      (Function.uncurry (fun z θ : ℝ =>
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.integrable_prod_of_iterated
      (G := fun z θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (fun _ _ => sq_nonneg _) hAE hslice houter).1
  -- and the statement's integrand agrees with it a.e. on the domain
  refine MeasureTheory.Integrable.congr hnice ?_
  filter_upwards [ae_snd_mem_Iθ] with p hp
  exact (mixed_slot_eq α p.1 p.2 hp (Work.Spaces.mixed j i f p.1 p.2)).symm

/-! ## The pure `D_z` slots -/

/-- **The `η`-weighted pure `D_z`-slots are jointly integrable.** -/
theorem zSlotProd' (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α n f) :
    ∀ i : ℕ, i ≤ n → MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter i f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  intro i hi
  have hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter i f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    aesm_z_slot hsm
  have hslice : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Integrable (fun θ => (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hAE.prodMk_left,
      ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hzm hz
    refine Integrable.mono' (hm.1 z hz) hzm ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
      with θ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_z α n f z θ i hi
  have houter : Integrable
      (fun z => ∫ θ, (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict Work.Spaces.Iz) := by
    refine Integrable.mono' hm.2 hAE.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hm.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => Work.Spaces.sq_le_HkIntegrand_z α n f z θ i hi))
  have hnice : Integrable
      (Function.uncurry (fun z θ : ℝ =>
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.integrable_prod_of_iterated
      (G := fun z θ : ℝ => (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (fun _ _ => sq_nonneg _) hAE hslice houter).1
  refine MeasureTheory.Integrable.congr hnice ?_
  filter_upwards [ae_snd_mem_Iθ] with p hp
  exact (z_slot_eq p.1 p.2 hp (Work.Spaces.DzIter i f p.1 p.2)).symm

/-! ## The two slots of the `ℋ^n`-integrand, jointly -/

theorem slotProd (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α n f) :
    (∀ i : ℕ, i ≤ n → MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter i f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ∧
    (∀ j i : ℕ, 1 ≤ i → i + j ≤ n → MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
  ⟨zSlotProd' α n hsm hm, mixedSlotProd α n hsm hm⟩

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6Gam.gamSliceCS11 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6Gam

open MeasureTheory Set Filter
open scoped Real Topology

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private lemma sin_two_nonneg_gsc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) > 0` on the open quadrant. -/
private lemma sin_two_pos_gsc {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    0 < Real.sin (2 * p.2) := by
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- `(z,θ) ↦ sin(2θ)^{-q}` is continuous on the open quadrant. -/
private lemma continuousOn_sin_rpow_gsc (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q)) Work.FTS.EllipticEst.Q0 :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_gsc hp)))

/-- The square of the mixed weight factorises: `(w·sin(2θ)^{-γ/2})² = w²·sin(2θ)^{-γ}` on `Iθ`. -/
private lemma Wt_sq_eq_gsc (α z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- **Cauchy–Schwarz in square-root form on the slice `Iθ`**: for `A`, `B` nonnegative on `Iθ`
and integrable there, `∫_Iθ √A·√B ≤ √(∫_Iθ A)·√(∫_Iθ B)`.  (The nonnegativity is needed only on
`Iθ`, which is all the application has.) -/
private lemma cs_sqrt_le_Iθ_gsc {A B : ℝ → ℝ}
    (hA : IntegrableOn A Work.Spaces.Iθ) (hB : IntegrableOn B Work.Spaces.Iθ)
    (hAnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ A θ) (hBnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ B θ) :
    (∫ θ in Work.Spaces.Iθ, Real.sqrt (A θ) * Real.sqrt (B θ))
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, A θ) * Real.sqrt (∫ θ in Work.Spaces.Iθ, B θ) := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsmA : AEStronglyMeasurable (fun θ => Real.sqrt (A θ))
      (volume.restrict Work.Spaces.Iθ) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hsmB : AEStronglyMeasurable (fun θ => Real.sqrt (B θ))
      (volume.restrict Work.Spaces.Iθ) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hAe : A =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Real.sqrt (A θ) ^ 2) :=
    (ae_restrict_mem hIθm).mono (fun θ hθ => (Real.sq_sqrt (hAnn θ hθ)).symm)
  have hBe : B =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Real.sqrt (B θ) ^ 2) :=
    (ae_restrict_mem hIθm).mono (fun θ hθ => (Real.sq_sqrt (hBnn θ hθ)).symm)
  have hAq : Integrable (fun θ => Real.sqrt (A θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    (show Integrable A (volume.restrict Work.Spaces.Iθ) from hA).congr hAe
  have hBq : Integrable (fun θ => Real.sqrt (B θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    (show Integrable B (volume.restrict Work.Spaces.Iθ) from hB).congr hBe
  have hAlp : MemLp (fun θ => Real.sqrt (A θ)) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq hsmA).mpr hAq
  have hBlp : MemLp (fun θ => Real.sqrt (B θ)) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq hsmB).mpr hBq
  have hcs := Work.Spaces.cs_integral hAlp hBlp
  have e1 : (∫ θ in Work.Spaces.Iθ, Real.sqrt (A θ) ^ 2) = ∫ θ in Work.Spaces.Iθ, A θ :=
    integral_congr_ae hAe.symm
  have e2 : (∫ θ in Work.Spaces.Iθ, Real.sqrt (B θ) ^ 2) = ∫ θ in Work.Spaces.Iθ, B θ :=
    integral_congr_ae hBe.symm
  rw [e1, e2] at hcs
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (A θ) * Real.sqrt (B θ) :=
    integral_nonneg (f := fun θ => Real.sqrt (A θ) * Real.sqrt (B θ))
      (fun θ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hP : 0 ≤ ∫ θ in Work.Spaces.Iθ, A θ := setIntegral_nonneg hIθm hAnn
  have hQ : 0 ≤ ∫ θ in Work.Spaces.Iθ, B θ := setIntegral_nonneg hIθm hBnn
  have hle := (Real.le_sqrt hnn (mul_nonneg hP hQ)).mpr hcs
  rwa [Real.sqrt_mul hP] at hle

/-- **The weighted angular Cauchy–Schwarz inequality for two mixed `D_θ`-slots.**  For any two
slots `(i₁,j₁)`, `(i₂,j₂)` with `1 ≤ i_k` and `i_k + j_k ≤ 6` (so that both slots occur in the
`ℋ⁶`-integrand), and every `z > 0`,
`∫_Iθ sin(2θ)^{-γ}·|D_z^{j₁}D_θ^{i₁}f|·|D_z^{j₂}D_θ^{i₂}f| ≤ √(∫ sin^{-γ}(D_z^{j₁}D_θ^{i₁}f)²)
·√(∫ sin^{-γ}(D_z^{j₂}D_θ^{i₂}f)²)`. -/
theorem gamSliceCS_weight (α : ℝ) (f : ℝ → ℝ → ℝ) (i₁ i₂ j₁ j₂ : ℕ)
    (hi₁ : 1 ≤ i₁) (hi₂ : 1 ≤ i₂) (hij₁ : i₁ + j₁ ≤ 6) (hij₂ : i₂ + j₂ ≤ 6)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.mixed j₁ i₁ f z θ| * |Work.Spaces.mixed j₂ i₂ f z θ|)
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j₁ i₁ f z θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j₂ i₂ f z θ) ^ 2) := by
  intro z hz
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsin : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => sin_two_nonneg_gsc hθ
  -- ## Integrability of the two weighted slot squares
  have hslot : ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 6 → IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f z θ) ^ 2) Work.Spaces.Iθ := by
    intro i j hi hij
    -- continuity of the slice integrand on the open quadrant
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 :=
      (continuousOn_sin_rpow_gsc (Work.Spaces.gam α)).mul
        (((hsm.mixed j i).forall 0).continuousOn.pow 2)
    have haesm : AEStronglyMeasurable (fun θ : ℝ =>
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
    -- the `w(z)²`-multiple of that integrand is dominated by the `ℋ⁶`-integrand
    have hbig : IntegrableOn (fun θ : ℝ => (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f z θ) ^ 2)) Work.Spaces.Iθ := by
      refine (hmem.1 z (le_of_lt hz)).mono' (haesm.const_mul ((Work.Spaces.w z) ^ 2)) ?_
      refine ae_restrict_of_forall_mem hIθm (fun θ hθ => ?_)
      have hs := hsin θ hθ
      have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f z θ) ^ 2) :=
        mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg hs _) (sq_nonneg _))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hkey : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j i f z θ) ^ 2) := by
        rw [mul_pow, Wt_sq_eq_gsc α z θ hs]
        ring
      rw [← hkey]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ i j hi hij
    -- divide the constant `w(z)² > 0` out
    have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
      have hpos : 0 < Work.Spaces.w z := by
        rw [Work.Spaces.w]
        exact div_pos (by positivity) (by positivity)
      exact pow_ne_zero 2 (ne_of_gt hpos)
    refine ((show Integrable _ (volume.restrict Work.Spaces.Iθ) from hbig).const_mul
      (((Work.Spaces.w z) ^ 2)⁻¹)).congr (Eventually.of_forall fun θ => ?_)
    exact inv_mul_cancel_left₀ hw _
  -- ## Cauchy–Schwarz with the pointwise square-root identity
  have hCS := cs_sqrt_le_Iθ_gsc
    (A := fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed j₁ i₁ f z θ) ^ 2)
    (B := fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed j₂ i₂ f z θ) ^ 2)
    (hslot i₁ j₁ hi₁ hij₁) (hslot i₂ j₂ hi₂ hij₂)
    (fun θ hθ => mul_nonneg (Real.rpow_nonneg (hsin θ hθ) _) (sq_nonneg _))
    (fun θ hθ => mul_nonneg (Real.rpow_nonneg (hsin θ hθ) _) (sq_nonneg _))
  refine le_trans (le_of_eq ?_) hCS
  refine setIntegral_congr_fun hIθm (fun θ hθ => ?_)
  have hρnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg (hsin θ hθ) _
  rw [Real.sqrt_mul hρnn, Real.sqrt_mul hρnn, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  rw [show (Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          * |Work.Spaces.mixed j₁ i₁ f z θ|)
        * (Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          * |Work.Spaces.mixed j₂ i₂ f z θ|)
      = (Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          * Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        * (|Work.Spaces.mixed j₁ i₁ f z θ| * |Work.Spaces.mixed j₂ i₂ f z θ|) from by ring,
    Real.mul_self_sqrt hρnn]
  ring

theorem gamSliceCS11 : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 1 1 f z θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 5 1 f z θ) ^ 2) := by
  intro α f _hα _hα1 hsm hmem z hz
  exact gamSliceCS_weight α f 1 1 1 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hsm hmem z hz

end Work.FTS.StrongPersist.H6Row6Gam
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMemOfContMajorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℋ^k`-membership from a continuous pointwise majorant

If the weighted `ℋ^k`-integrand of `h` is continuous on the open quadrant `Q0`, is dominated on
`Q0` by `K` times that of some `f ∈ ℋ^k`, and `h` is measurable where it matters (which the
continuity supplies), then `h ∈ ℋ^k`.

The point of the lemma is that the domination hypothesis is only required on the *open* quadrant
`(0,∞) × (0,π/2)`: the two angular endpoints `θ = 0, π/2` and the radial endpoint `z = 0` form a
null set, and at `z = 0` the integrand vanishes identically because the radial weight `w` does.
Hence it can be converted into an a.e. statement on the closed quadrant and fed into
`Integrable.mono'` against the (integrable) majorant `K · HkIntegrand α k f`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

theorem HkMemOfContMajorant (α : ℝ) (k : ℕ) {h f : ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      Work.FTS.EllipticEst.Q0)
    (hmf : Work.Spaces.HkMem α k f)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α k h z θ ≤ K * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkMem α k h := by
  -- a.e. strong measurability of the angular slices of the integrand of `h`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.HkIntegrand α k h z θ)
        (volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · -- at `z = 0` the radial weight vanishes and the integrand is identically zero
      subst h0
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α k h 0 θ) = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => by
          simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
          simp
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz0
  -- joint a.e. strong measurability of the integrand of `h`
  have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  -- the slice majorant is integrable
  have hMslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ : ℝ => K * Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iθ :=
    fun z hz => (hmf.1 z hz).const_mul K
  -- so is its `z`-integral
  have hMz : IntegrableOn (fun z => K * ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := hmf.2.const_mul K
  -- the domination, upgraded to an a.e. statement on the closed angular interval
  have hle_ae : ∀ z ∈ Work.Spaces.Iz,
      ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α k h z θ ≤ K * Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz
    have hmeas : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (π / 2)) :=
      (Measure.restrict_congr_set
        (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (π / 2)))).symm
    rw [hmeas]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hle z hz θ hθ)
  constructor
  · -- every angular slice of the integrand of `h` is integrable
    intro z hz
    refine Integrable.mono' (hMslice z hz) (hslice z hz) ?_
    filter_upwards [hle_ae z hz] with θ hθ
    rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k h z θ)]
    exact hθ
  · -- the `z`-integral of the angular slices is integrable
    refine Integrable.mono hMz hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k h z θ
    have hnnK : 0 ≤ K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
      mul_nonneg hK (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
    rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg hnnK]
    exact (integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k h z θ)
      ((hmf.1 z hz).const_mul K) (hle_ae z hz)).trans (le_of_eq (integral_const_mul K _))

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.ZmulCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option maxHeartbeats 1600000

/-! ## The constant -/

/-- The constant of the multiplier estimate: `((k+1)³ + (k+1)⁵)·4ᵏ + 1`.  It is explicit and
does not depend on `α`, `φ`, `K` or `g`. -/
def zmulConst (k : ℕ) : ℝ :=
  (((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2 + 1

theorem zmulConst_pos (k : ℕ) : 0 < zmulConst k := by
  have h1 : (0 : ℝ) < ((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5 := by positivity
  have h2 : (0 : ℝ) ≤ ((2 : ℝ) ^ k) ^ 2 := sq_nonneg _
  have h3 : (0 : ℝ) ≤ (((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2 :=
    mul_nonneg h1.le h2
  simp only [zmulConst]
  linarith

/-! ## Elementary helpers -/

/-- A function of one variable which is `C^∞` on a set is `C^n` there, for every finite `n`. -/
theorem contDiffOn_nat_of_smoothOrder {φ : ℝ → ℝ} {V : Set ℝ} (n : ℕ)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder φ V) : ContDiffOn ℝ n φ V :=
  h.of_le (by simp [Work.Stability.smoothOrder])

/-- The product of a `z`-only `C^∞` factor with a function `C^∞` on the *open* quadrant is
again `C^∞` on the open quadrant. -/
theorem smoothOpen_zmul {φ : ℝ → ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1)))
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => φ z * g z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen]
  have hfst : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => φ p.1)
      Work.FTS.EllipticEst.Q0 :=
    hsm.comp contDiffOn_fst (fun p hp => by
      have hp1 : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      exact Set.mem_Ioi.mpr (by linarith))
  exact hfst.mul hg

/-! ## The pointwise algebraic core -/

/-- **The algebraic core of the multiplier estimate.**  If at the point `(z,θ)` the two
Leibniz expansions of `D_z^i (φ·g)` and `D_z^jD_θ^i (φ·g)` hold (with the `z`-only multiplier
`φ`) and the iterated `Zop`-derivatives of `φ` at `z` are bounded by `K`, then the
`ℋᵏ`-integrand of `φ·g` is bounded by `zmulConst k·(1+K)²` times that of `g`. -/
theorem zmul_pt (α : ℝ) (k : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    {z θ : ℝ} (hB : ∀ b ≤ k, |Work.Spaces.Zop^[b] φ z| ≤ K)
    (hexpZ : ∀ i ≤ k, Work.Spaces.DzIter i (fun z θ => φ z * g z θ) z θ =
      ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
        (Work.Spaces.Zop^[b] φ z * Work.Spaces.DzIter (i - b) g z θ))
    (hexpM : ∀ j i, 1 ≤ i → i + j ≤ k →
      Work.Spaces.mixed j i (fun z θ => φ z * g z θ) z θ =
      ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
        (Work.Spaces.Zop^[b] φ z * Work.Spaces.mixed (j - b) i g z θ)) :
    Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
      ≤ zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ := by
  have hQnn : 0 ≤ Work.Spaces.HkIntegrand α k g z θ :=
    Work.Spaces.HkIntegrand_nonneg α k g z θ
  have hchoose : ∀ (m b : ℕ), m ≤ k → |((m.choose b : ℕ) : ℝ)| ≤ (2 : ℝ) ^ k := by
    intro m b hmk
    calc |((m.choose b : ℕ) : ℝ)| = ((m.choose b : ℕ) : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
      _ ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.choose_le_two_pow m b
      _ = (2 : ℝ) ^ m := by push_cast; ring
      _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hmk
  -- a partial sum of the radial block is bounded by the whole integrand
  have hzsum : ∀ i : ℕ, i ≤ k →
      (∑ m ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ Work.Spaces.HkIntegrand α k g z θ := by
    intro i hik
    rw [Work.Spaces.HkIntegrand]
    have hsub : (∑ m ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (∑ m ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro m hm
          exact Finset.mem_range.mpr (by
            have := Finset.mem_range.mp hm
            omega))
        (fun m _ _ => sq_nonneg _)
    exact le_trans hsub (le_add_of_nonneg_right (Work.Spaces.hkMixedSum_nonneg α k g z θ))
  -- a partial sum of a row of the mixed block is bounded by `(j+1)` integrands
  have hmsum : ∀ i j : ℕ, 1 ≤ i → i + j ≤ k →
      (∑ m ∈ Finset.range (j + 1),
        (Work.Spaces.mixed m i g z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ((j : ℝ) + 1) * Work.Spaces.HkIntegrand α k g z θ := by
    intro i j hi1 hij
    calc (∑ m ∈ Finset.range (j + 1),
          (Work.Spaces.mixed m i g z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∑ _m ∈ Finset.range (j + 1), Work.Spaces.HkIntegrand α k g z θ :=
          Finset.sum_le_sum fun m hm => by
            have hmj : m ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            exact Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ i m hi1 (by omega)
      _ = ((j : ℝ) + 1) * Work.Spaces.HkIntegrand α k g z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- ### the radial block of the product
  have hZi : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => φ z * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ (((k : ℝ) + 1) * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
          * Work.Spaces.HkIntegrand α k g z θ := by
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => φ z * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
            * Work.Spaces.HkIntegrand α k g z θ := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      -- multiply the Leibniz expansion by the weight, then Cauchy–Schwarz
      have hmul : Work.Spaces.DzIter i (fun z θ => φ z * g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.Zop^[b] φ z * (Work.Spaces.DzIter (i - b) g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
        rw [hexpZ i hik, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [hmul]
      have hbin := Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le (i := i) (D := (2 : ℝ) ^ k)
        (K := K) hK (x := fun b => Work.Spaces.Zop^[b] φ z)
        (y := fun m => Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        (fun b hb => hB b (le_trans hb hik))
        (fun b hb => hchoose i b hik)
      have hbin' : (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Spaces.Zop^[b] φ z * (Work.Spaces.DzIter (i - b) g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
          ≤ (((i : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
              * (∑ m ∈ Finset.range (i + 1),
                  (Work.Spaces.DzIter m g z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hbin
      refine le_trans hbin' ?_
      have hconst : (((i : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
          ≤ (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2 := by
        have hbase : ((i : ℝ) + 1) * (2 : ℝ) ^ k ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right
            (by
              have : (i : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hik
              linarith)
            (by positivity)
        have hle : ((i : ℝ) + 1) * (2 : ℝ) ^ k * K ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k * K :=
          mul_le_mul_of_nonneg_right hbase hK
        exact pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK)
          hle 2
      exact mul_le_mul hconst (hzsum i hik) (Finset.sum_nonneg fun m _ => sq_nonneg _)
        (by positivity)
    calc (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => φ z * g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (k + 1), ((((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
            * Work.Spaces.HkIntegrand α k g z θ) := Finset.sum_le_sum hterm
      _ = (((k : ℝ) + 1) * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
            * Work.Spaces.HkIntegrand α k g z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- ### the mixed block of the product
  have hMi : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => φ z * g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ (((k : ℝ) + 1) ^ 3 * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
          * Work.Spaces.HkIntegrand α k g z θ := by
    have hsummand : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => φ z * g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (((k : ℝ) + 1) * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
            * Work.Spaces.HkIntegrand α k g z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc]
        obtain ⟨hi1, hij⟩ := hc
        have hjn : j ≤ k := by omega
        have hmul : Work.Spaces.mixed j i (fun z θ => φ z * g z θ) z θ
              * Work.Spaces.Wt α z θ
            = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Spaces.Zop^[b] φ z
                    * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ)) := by
          rw [hexpM j i hi1 hij, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
        rw [hmul]
        have hbin := Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le (i := j) (D := (2 : ℝ) ^ k)
          (K := K) hK (x := fun b => Work.Spaces.Zop^[b] φ z)
          (y := fun m => Work.Spaces.mixed m i g z θ * Work.Spaces.Wt α z θ)
          (fun b hb => hB b (le_trans hb hjn))
          (fun b hb => hchoose j b hjn)
        have hbin' : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Spaces.Zop^[b] φ z * (Work.Spaces.mixed (j - b) i g z θ
                  * Work.Spaces.Wt α z θ))) ^ 2
            ≤ (((j : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
                * (∑ m ∈ Finset.range (j + 1),
                    (Work.Spaces.mixed m i g z θ * Work.Spaces.Wt α z θ) ^ 2) := by
          simpa only [Nat.cast_add, Nat.cast_one] using hbin
        refine le_trans hbin' ?_
        have hconst : (((j : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
            ≤ (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2 := by
          have hbase : ((j : ℝ) + 1) * (2 : ℝ) ^ k ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right
              (by
                have : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjn
                linarith)
              (by positivity)
          have hle : ((j : ℝ) + 1) * (2 : ℝ) ^ k * K ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k * K :=
            mul_le_mul_of_nonneg_right hbase hK
          exact pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK)
            hle 2
        have hA : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by
          have : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjn
          linarith
        have hAZ : 0 ≤ (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2 := by positivity
        calc (((j : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
              * (∑ m ∈ Finset.range (j + 1),
                  (Work.Spaces.mixed m i g z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
                * (((j : ℝ) + 1) * Work.Spaces.HkIntegrand α k g z θ) :=
              mul_le_mul hconst (hmsum i j hi1 hij)
                (Finset.sum_nonneg fun m _ => sq_nonneg _) hAZ
          _ ≤ (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2
                * (((k : ℝ) + 1) * Work.Spaces.HkIntegrand α k g z θ) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hQnn) hAZ
          _ = (((k : ℝ) + 1) * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
                * Work.Spaces.HkIntegrand α k g z θ := by ring
      · rw [if_neg hc]
        exact mul_nonneg (by positivity) hQnn
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (fun z θ => φ z * g z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
            ((((k : ℝ) + 1) * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
              * Work.Spaces.HkIntegrand α k g z θ) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hsummand i hi j hj
      _ = (((k : ℝ) + 1) ^ 3 * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
            * Work.Spaces.HkIntegrand α k g z θ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- ### add the two blocks and absorb `K² ≤ (1+K)²` together with the `+1`
  conv_lhs => rw [Work.Spaces.HkIntegrand]
  refine le_trans (add_le_add hZi hMi) ?_
  have hKsq : K ^ 2 ≤ (1 + K) ^ 2 := by nlinarith [hK]
  have hkey : (((k : ℝ) + 1) * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
        * Work.Spaces.HkIntegrand α k g z θ
      + (((k : ℝ) + 1) ^ 3 * (((k : ℝ) + 1) * (2 : ℝ) ^ k * K) ^ 2)
        * Work.Spaces.HkIntegrand α k g z θ
      = ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) * K ^ 2
        * Work.Spaces.HkIntegrand α k g z θ := by ring
  rw [hkey]
  have h0 : 0 ≤ ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) := by positivity
  have hstep1 : ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) * K ^ 2
        * Work.Spaces.HkIntegrand α k g z θ
      ≤ ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) * (1 + K) ^ 2
        * Work.Spaces.HkIntegrand α k g z θ := by
    calc ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) * K ^ 2
          * Work.Spaces.HkIntegrand α k g z θ
        = ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2)
            * (K ^ 2 * Work.Spaces.HkIntegrand α k g z θ) := by ring
      _ ≤ ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2)
            * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKsq hQnn) h0
      _ = ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) * (1 + K) ^ 2
            * Work.Spaces.HkIntegrand α k g z θ := by ring
  refine le_trans hstep1 ?_
  have h1 : 0 ≤ (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ :=
    mul_nonneg (by positivity) hQnn
  calc ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2) * (1 + K) ^ 2
        * Work.Spaces.HkIntegrand α k g z θ
      = ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2)
          * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ) := by ring
    _ ≤ ((((k : ℝ) + 1) ^ 3 + ((k : ℝ) + 1) ^ 5) * ((2 : ℝ) ^ k) ^ 2 + 1)
          * ((1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ) :=
        mul_le_mul_of_nonneg_right (by linarith) h1
    _ = zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ := by
        simp only [zmulConst]
        ring

end Work.FTS.StrongPersist.L3Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6.ProdDefs6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The angular weight `w z / sin(2θ)^{η/2}` carried by the pure `D_z`-slots of `HkIntegrand`. -/
abbrev Hv6 (z θ : ℝ) : ℝ := w z / (Real.sin (2 * θ)) ^ (eta / 2)

/-- The `(γ-1)⁻¹`-block of the level-six majorant: the part priced by the two `ℋ⁶`-norms of the
factors. -/
def SInv6 (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (gam α - 1)⁻¹
    * (HkSq α 6 f * HkIntegrand α 6 g z θ + HkSq α 6 g * HkIntegrand α 6 f z θ)

/-- The two exceptional terms of the `(5,1)`-slot, both carrying the full weight `W`. -/
def Texc6 (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ((DzIter 5 f z θ * Dth g z θ) ^ 2 + (Dth f z θ * DzIter 5 g z θ) ^ 2)
    * (Wt α z θ) ^ 2

/-- The target majorant, as a single expression. -/
def Maj6 (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ := SInv6 α f g z θ + Texc6 α f g z θ

theorem gam_sub_one_pos6 {α : ℝ} (hα : 0 < α) : 0 < gam α - 1 := by
  rw [gam_sub_one]; linarith


theorem inv_gam_sub_one_nonneg6 {α : ℝ} (hα : 0 < α) : 0 ≤ (gam α - 1)⁻¹ :=
  inv_nonneg.mpr (gam_sub_one_pos6 hα).le


theorem SInv6_nonneg {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ SInv6 α f g z θ := by
  rw [SInv6]
  refine mul_nonneg (inv_gam_sub_one_nonneg6 hα) ?_
  exact add_nonneg (mul_nonneg (HkSq_nonneg α 6 f) (HkIntegrand_nonneg α 6 g z θ))
    (mul_nonneg (HkSq_nonneg α 6 g) (HkIntegrand_nonneg α 6 f z θ))

theorem Texc6_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ Texc6 α f g z θ := by
  rw [Texc6]
  exact mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

theorem Maj6_nonneg {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Maj6 α f g z θ :=
  add_nonneg (SInv6_nonneg hα f g z θ) (Texc6_nonneg α f g z θ)

/-- The `SInv6`-block dominates its first summand. -/
theorem mul_inv_mul_le_SInv6_left {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 g z θ) ≤ SInv6 α f g z θ := by
  rw [SInv6]
  refine mul_le_mul_of_nonneg_left ?_ (inv_gam_sub_one_nonneg6 hα)
  exact le_add_of_nonneg_right (mul_nonneg (HkSq_nonneg α 6 g) (HkIntegrand_nonneg α 6 f z θ))

/-- The `SInv6`-block dominates its second summand. -/
theorem mul_inv_mul_le_SInv6_right {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (gam α - 1)⁻¹ * (HkSq α 6 g * HkIntegrand α 6 f z θ) ≤ SInv6 α f g z θ := by
  rw [SInv6]
  refine mul_le_mul_of_nonneg_left ?_ (inv_gam_sub_one_nonneg6 hα)
  exact le_add_of_nonneg_left (mul_nonneg (HkSq_nonneg α 6 f) (HkIntegrand_nonneg α 6 g z θ))

/-- `n.choose k ≤ 2^n ≤ 64` for `n ≤ 6`, hence `(n.choose k : ℝ)² ≤ 4096`. -/
theorem binom_sq_le_4096 (n k : ℕ) (hkn : k ≤ n) (hn : n ≤ 6) :
    (n.choose k : ℝ) ^ 2 ≤ 4096 := by
  have h1 : n.choose k ≤ 2 ^ n := by
    have h := Finset.single_le_sum (f := fun j => n.choose j) (fun j _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn))
    rwa [Nat.sum_range_choose] at h
  have h2 : n.choose k ≤ 64 := by
    calc n.choose k ≤ 2 ^ n := h1
      _ ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num) hn
      _ = 64 := by norm_num
  have h3 : (n.choose k : ℝ) ≤ 64 := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (n.choose k : ℝ) := by positivity
  nlinarith [h3, h4]

end Work.FTS.StrongPersist.N6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false

/-- **The honest boundary-trace predicate.**  For almost every angle `θ ∈ Iθ`, each of the
five order-`4` hard slots `Thard g k` (`k : Fin 5`) satisfies the two *radial* boundary
conditions of the frozen `BdryTraces α 4 g`: `z · (Thard g k z θ · w z)² → 0` both as
`z → 0⁺` and as `z → +∞`.

This is what replaces the `BdryTraces`-component of `RegQ α 4 g` in the honest transport
clauses; it is *derived* from `SmoothOpen g` together with `HkMem α 4 g` and `HkMem α 5 g`
in `Hon/TraceAe.lean`. -/
def TraceAe (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    ∀ k : Fin 5,
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0)

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.TermSixAux.sliceIntCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux.TermSixAux


end Work.FTS.StrongPersist.N6Trans.T1SixAux.TermSixAux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxDataH.tendsto_values_on_cbox =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.BoxDataH

/-- Convergence of `un n z θ` to `Ψ z θ` on the *closed* box `[a,b] × [0,π/2]` (`0 < a`),
given convergence on the open quadrant `Q0 = (0,∞) × (0,π/2)` and the vanishing of both the
sequence and its limit at the two boundary angles `θ = 0` and `θ = π/2`.

The only non-trivial case is the interior one, where `(z,θ) ∈ Q0`; at `θ = 0` and `θ = π/2`
(with `z ≥ 0`) the sequence is identically zero and so is the limit. -/
theorem tendsto_values_on_cbox {Ψ : ℝ → ℝ → ℝ} {un : ℕ → ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n => un n z θ) Filter.atTop (nhds (Ψ z θ)))
    (hvan0 : ∀ z : ℝ, Ψ z 0 = 0) (hvan1 : ∀ z : ℝ, Ψ z (Real.pi / 2) = 0)
    (hzero : ∀ n : ℕ, ∀ z : ℝ, 0 ≤ z → un n z 0 = 0 ∧ un n z (Real.pi / 2) = 0) :
    ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      Filter.Tendsto (fun n => un n z θ) Filter.atTop (nhds (Ψ z θ)) := by
  intro z hz θ hθ
  obtain ⟨hza, _⟩ := hz
  obtain ⟨hθ0, hθ2⟩ := hθ
  have hzpos : 0 < z := lt_of_lt_of_le ha hza
  have hz0 : 0 ≤ z := le_of_lt hzpos
  -- the sequence is constantly `0` when `θ = 0`
  have hvanish0 : (fun n : ℕ => un n z 0) = fun _ : ℕ => (0 : ℝ) := by
    funext n; exact (hzero n z hz0).1
  -- the sequence is constantly `0` when `θ = π/2`
  have hvanish1 : (fun n : ℕ => un n z (Real.pi / 2)) = fun _ : ℕ => (0 : ℝ) := by
    funext n; exact (hzero n z hz0).2
  by_cases h0 : θ = 0
  · -- boundary angle `θ = 0`
    rw [h0, hvan0 z, hvanish0]
    exact tendsto_const_nhds
  by_cases h2 : θ = Real.pi / 2
  · -- boundary angle `θ = π/2`
    rw [h2, hvan1 z, hvanish1]
    exact tendsto_const_nhds
  · -- interior angle: the point lies in the open quadrant
    exact hconv z θ (Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨hzpos, lt_of_le_of_ne hθ0 (Ne.symm h0), lt_of_le_of_ne hθ2 h2⟩)

end Work.FTS_EllLimOK.BoxDataH
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Decay.DecayTools =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.Decay

set_option autoImplicit false

/-! ## The `k = 0` angular integrand -/

/-- **The `k = 0` integrand is a single square.**  For `k = 0` the second (mixed) sum inside
`HkIntegrand` is empty (its condition is `1 ≤ i` with `i = 0`), so only the `D_z`-slot survives. -/
theorem HkIntegrand_zero_eq (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 Ψ z θ
      = (Ψ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- **The weight factor is `≥ 1` on `z ≥ 1`.**  `w z = (1+z)²/z² ≥ 1` for `z > 0` and
`sin(2θ)^{η/2} ≤ 1` for `θ ∈ (0,π/2)`, so their quotient is `≥ 1`. -/
theorem one_le_w_div_sin {z θ : ℝ} (hz : 1 ≤ z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  have hzpos : 0 < z := by linarith
  have h2θpos : 0 < 2 * θ := by linarith [hθ.1]
  have h2θlt : 2 * θ < Real.pi := by linarith [hθ.2]
  have hs : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi h2θpos h2θlt
  rw [one_le_div (Real.rpow_pos_of_pos hs _)]
  have h1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs) (Real.sin_le_one _)
      (by norm_num [Work.Spaces.eta])
  have h2 : 1 ≤ Work.Spaces.w z := by
    have hz2 : 0 < z ^ 2 := by positivity
    rw [Work.Spaces.w, one_le_div hz2]
    nlinarith
  linarith

/-! ## Slice derivatives at a `C²`-point -/

/-- The `z`-slice of a function that is jointly `C²` at `(z,θ)` has derivative `∂_z` there. -/
theorem deriv_slice_z_of_contDiffAt {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ)) :
    deriv (fun z' => G z' θ) z = Work.Spaces.pz G z θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) := h.differentiableAt (by norm_num)
  rw [show (fun z' => G z' θ) = fun z' => Function.uncurry G (z', θ) from rfl,
    Work.Spaces.deriv_slice_fst (Function.uncurry G) z θ hd, Work.Spaces.pz_eq_fderiv hd]

/-- The `θ`-slice of a function that is jointly `C²` at `(z,θ)` has derivative `∂_θ` there. -/
theorem deriv_slice_th_of_contDiffAt {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ)) :
    deriv (fun θ' => G z θ') θ = Work.Spaces.pth G z θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) := h.differentiableAt (by norm_num)
  rw [show (fun θ' => G z θ') = fun θ' => Function.uncurry G (z, θ') from rfl,
    Work.Spaces.deriv_slice_snd (Function.uncurry G) z θ hd, Work.Spaces.pth_eq_fderiv hd]

/-! ## The two mean-value bounds -/

/-- **The `z`-Lipschitz bound.**  If `|D_zΨ| = |z ∂_zΨ| ≤ C` with `C > 0` on the open quadrant,
then for `0 < z ≤ z'` and `θ ∈ (0,π/2)`,
`|Ψ z' θ - Ψ z θ| ≤ (C/z)·(z' - z)`.

Indeed `|∂_zΨ t θ| ≤ C/t ≤ C/z` for `t ∈ [z,z']`, and the mean value theorem on the convex set
`[z,z']` gives the claim (the slices are differentiable by `BoxReg`). -/
theorem abs_slice_z_sub_le {Ψ : ℝ → ℝ → ℝ} (hbox : BoxReg Ψ) {C z z' θ : ℝ}
    (hDz : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed 1 0 Ψ z θ| ≤ C)
    (hC : 0 < C) (hz : 0 < z) (hzz' : z ≤ z') (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |Ψ z' θ - Ψ z θ| ≤ C / z * (z' - z) := by
  have hdiff : ∀ t ∈ Set.Icc z z', DifferentiableAt ℝ (fun t => Ψ t θ) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hz ht.1
    exact Work.Spaces.differentiableAt_curry_left
      ((hbox.contDiffAt ⟨Set.mem_Ioi.mpr ht0, hθ⟩).differentiableAt (by norm_num))
  have hbound : ∀ t ∈ Set.Icc z z', |deriv (fun t => Ψ t θ) t| ≤ C / z := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hz ht.1
    have h2θpos : 0 < 2 * θ := by linarith [hθ.1]
    have h2θlt : 2 * θ < Real.pi := by linarith [hθ.2]
    have hs : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi h2θpos h2θlt
    rw [deriv_slice_z_of_contDiffAt ((hbox.contDiffAt ⟨Set.mem_Ioi.mpr ht0, hθ⟩))]
    have hmix : Work.Spaces.mixed 1 0 Ψ t θ = t * Work.Spaces.pz Ψ t θ := rfl
    have hDz' := hDz t θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨ht0, hθ.1, hθ.2⟩)
    rw [hmix, abs_mul, abs_of_pos ht0] at hDz'
    have hpz : |Work.Spaces.pz Ψ t θ| ≤ C / t := by
      rw [le_div_iff₀ ht0]
      linarith
    have hCt : C / t ≤ C / z := div_le_div_of_nonneg_left (le_of_lt hC) hz ht.1
    linarith
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc z z') (f := fun t => Ψ t θ)
    (C := C / z) hdiff hbound (convex_Icc z z') (left_mem_Icc.mpr hzz') (right_mem_Icc.mpr hzz')
  simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hzz')] using h

/-- **The `θ`-Lipschitz bound.**  If `|D_θΨ| = |sin(2θ) ∂_θΨ| ≤ C` with `C > 0` on the open
quadrant and `sin(2θ) ≥ s > 0` on the interval `[a,b] ⊆ (0,π/2)`, then for `z > 0` and
`θ, θ' ∈ [a,b]`, `|Ψ z θ' - Ψ z θ| ≤ (C/s)·|θ' - θ|`. -/
theorem abs_slice_th_sub_le {Ψ : ℝ → ℝ → ℝ} (hbox : BoxReg Ψ) {C s a b z : ℝ}
    (hDth : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed 0 1 Ψ z θ| ≤ C)
    (hC : 0 < C) (hz : 0 < z) (ha : 0 < a) (hb : b < π / 2)
    (hs : ∀ θ ∈ Set.Icc a b, s ≤ Real.sin (2 * θ)) (hs0 : 0 < s)
    {θ θ' : ℝ} (hθ : θ ∈ Set.Icc a b) (hθ' : θ' ∈ Set.Icc a b) :
    |Ψ z θ' - Ψ z θ| ≤ C / s * |θ' - θ| := by
  have hab : a ≤ b := le_trans hθ.1 hθ.2
  have hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun θ' => Ψ z θ') t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have htlt : t < π / 2 := lt_of_le_of_lt ht.2 hb
    exact Work.Spaces.differentiableAt_curry_right
      ((hbox.contDiffAt ⟨Set.mem_Ioi.mpr hz, ⟨ht0, htlt⟩⟩).differentiableAt (by norm_num))
  have hbound : ∀ t ∈ Set.Icc a b, |deriv (fun θ' => Ψ z θ') t| ≤ C / s := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have htlt : t < π / 2 := lt_of_le_of_lt ht.2 hb
    have hsin : 0 < Real.sin (2 * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [deriv_slice_th_of_contDiffAt (hbox.contDiffAt ⟨Set.mem_Ioi.mpr hz, ⟨ht0, htlt⟩⟩)]
    have hmix : Work.Spaces.mixed 0 1 Ψ z t = Real.sin (2 * t) * Work.Spaces.pth Ψ z t := rfl
    have hDth' := hDth z t (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, ht0, htlt⟩)
    rw [hmix, abs_mul, abs_of_pos hsin] at hDth'
    have hpth : |Work.Spaces.pth Ψ z t| ≤ C / Real.sin (2 * t) := by
      rw [le_div_iff₀ hsin]
      linarith
    have hle : C / Real.sin (2 * t) ≤ C / s :=
      div_le_div_of_nonneg_left (le_of_lt hC) hs0 (hs t ht)
    linarith
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc a b) (f := fun t => Ψ z t)
    (C := C / s) hdiff hbound (convex_Icc a b) hθ hθ'
  simpa [Real.norm_eq_abs] using h

/-! ## Localised lower bounds for the integrals -/

/-- **A local lower bound upgrades to a lower bound of the half-line integral.**  If `g ≥ 0`
everywhere, `g` is integrable on `(Z,∞)` and `g ≥ c` on the window `[z, z+1]` with `Z ≤ z`, then
`c ≤ ∫_{Z}^{∞} g`. -/
theorem integral_Ioi_ge_of_lower_bound {g : ℝ → ℝ} {Z z c : ℝ} (hz : Z ≤ z)
    (hgint : MeasureTheory.IntegrableOn g (Set.Ioi Z) volume)
    (hnonneg : ∀ t, 0 ≤ g t) (hlow : ∀ t ∈ Set.Icc z (z + 1), c ≤ g t) :
    c ≤ ∫ t in Set.Ioi Z, g t := by
  have hz1 : z ≤ z + 1 := by linarith
  have hsub : Set.Ioc z (z + 1) ⊆ Set.Ioi Z := fun t ht => lt_of_le_of_lt hz ht.1
  have hgIoc : MeasureTheory.IntegrableOn g (Set.Ioc z (z + 1)) := hgint.mono_set hsub
  have hgInt : IntervalIntegrable g volume z (z + 1) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hz1]
    exact hgIoc
  have hmono : (∫ t in z..(z + 1), (fun _ : ℝ => c) t) ≤ ∫ t in z..(z + 1), g t :=
    intervalIntegral.integral_mono_on hz1 intervalIntegrable_const hgInt hlow
  have hconst : (∫ t in z..(z + 1), (fun _ : ℝ => c) t) = c := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have htail : (∫ t in z..(z + 1), g t) ≤ ∫ t in Set.Ioi Z, g t := by
    rw [intervalIntegral.integral_of_le hz1]
    exact setIntegral_mono_set hgint (ae_of_all _ hnonneg) (ae_of_all _ hsub)
  linarith

/-- **A local lower bound upgrades to a lower bound of the angular integral.**  If `f ≥ 0` on
`Iθ`, `f` is integrable there and `f ≥ c` on `[a,b] ⊆ Iθ`, then `c·(b - a) ≤ ∫_{Iθ} f`. -/
theorem thetaIntegral_ge_of_lower_bound {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ) (hint : MeasureTheory.IntegrableOn f Work.Spaces.Iθ)
    (hnonneg : ∀ θ, 0 ≤ f θ) (hlow : ∀ θ ∈ Set.Icc a b, c ≤ f θ) :
    c * (b - a) ≤ ∫ θ in Work.Spaces.Iθ, f θ := by
  have hloc : MeasureTheory.IntegrableOn f (Set.Ioc a b) :=
    hint.mono_set (fun θ hθ => hsub hθ)
  have hInt : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
    exact hloc
  have hmono : (∫ θ in a..b, (fun _ : ℝ => c) θ) ≤ ∫ θ in a..b, f θ :=
    intervalIntegral.integral_mono_on hab intervalIntegrable_const hInt hlow
  have hconst : (∫ θ in a..b, (fun _ : ℝ => c) θ) = c * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have htail : (∫ θ in a..b, f θ) ≤ ∫ θ in Work.Spaces.Iθ, f θ := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_mono_set hint (ae_of_all _ hnonneg) (ae_of_all _ fun θ hθ => hsub hθ)
  linarith

end Work.FTS_EllLimOK.Decay
end
end
