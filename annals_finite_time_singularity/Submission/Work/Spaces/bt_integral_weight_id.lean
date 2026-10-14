import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.MinImports
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.scoef_sum_shift
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.CommutZQuadQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.Coercivity

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def quadQ : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

lemma isOpen_quadQ : IsOpen quadQ := isOpen_Ioi.prod isOpen_Ioo

/-- The class of uncurried functions which are `C^∞` on the open quadrant `quadQ`. -/
def SmoothQ (F : ℝ × ℝ → ℝ) : Prop := ContDiffOn ℝ ⊤ F quadQ

lemma SmoothQ.differentiableAt {F : ℝ × ℝ → ℝ} (h : SmoothQ F) {p : ℝ × ℝ}
    (hp : p ∈ quadQ) : DifferentiableAt ℝ F p :=
  (h.contDiffAt (isOpen_quadQ.mem_nhds hp)).differentiableAt (by norm_num)


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.DthU_iter_Gam_all =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `D_θ^{j+1} Γ = α · Tfun j α · Γ` on `(0, π/2)`, for **every** real `α`

The paper's angular identity is normally stated for `α > 0` (see
`Work.Spaces.dthU_iter_Gam`).  Here we remove that hypothesis: the identity is a
purely algebraic/analytic statement in `α` and holds for arbitrary real `α`.

The only place the positivity of `α` was used in the `Spaces` development is the
base case `D_θ Γ = α q Γ`, and there it is in fact unnecessary: the underlying
derivative computation is valid for every `α` because `sin θ · cos²θ > 0` on
`(0, π/2)`.  We reprove that base case harmlessly as `dthU_Gam_all`, and then
repeat the induction over `j`.
-/

open scoped Real Topology
open Set Filter

namespace Work.Coercivity



end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.EL12z_Kd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.Coercivity

theorem EL12z_Kd (f : ℝ → ℝ → ℝ) (hf : HardyHyp f)
    (hsl : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun z => (FM.L12dens Spaces.K f z) ^ 2) (Set.Ioi 0) ∧
      ∫ z in Set.Ioi (0 : ℝ), (FM.L12dens Spaces.K f z) ^ 2
        ≤ 3 * ∫ z in Set.Ioi (0 : ℝ), (∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2 := by
  -- The angular weight integrates to `1` over `Iθ` (normalisation of `K`).
  have hK : ∫ θ in Spaces.Iθ, Spaces.K θ = (1 : ℝ) := integral_Itheta_K
  -- The reference integrand `z ↦ (∫_θ (f z θ)²)/z²` is integrable, by `HardyHyp.intB` at `j = 1`.
  have hIntR : MeasureTheory.IntegrableOn
      (fun z => (∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2) (Set.Ioi (0 : ℝ)) := by
    have h := hf.intB 1 (by norm_num)
    simpa using h
  -- Pointwise (a.e.) Cauchy–Schwarz bound for the density `L12dens K f z = (1/z)∫_θ K f`.
  have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (FM.L12dens Spaces.K f z) ^ 2
        ≤ 3 * ((∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2) := by
    filter_upwards [hsl, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hzsl hz
    have h := L12dens_sq_slice f hK hz hzsl
    simpa only [mul_div_assoc] using h
  -- Measurability of the squared density on `(0,∞)`, from its continuity there.
  have hcontL : ContinuousOn (fun z => FM.L12dens Spaces.K f z) (Set.Ioi 0) :=
    fun z hz => (hf.hcont z hz).continuousWithinAt
  have hAesm : MeasureTheory.AEStronglyMeasurable
      (fun z => (FM.L12dens Spaces.K f z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hcontL.aestronglyMeasurable measurableSet_Ioi).pow 2
  -- Integrability of the squared density follows by a.e. domination.
  have hdom : MeasureTheory.IntegrableOn
      (fun z => 3 * ((∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2)) (Set.Ioi (0 : ℝ)) :=
    hIntR.const_mul 3
  have hnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ‖(FM.L12dens Spaces.K f z) ^ 2‖
        ≤ 3 * ((∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2) := by
    filter_upwards [hpt] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hz
  have hIntL : MeasureTheory.IntegrableOn
      (fun z => (FM.L12dens Spaces.K f z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    hdom.mono' hAesm hnn
  refine ⟨hIntL, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hIntL hdom hpt
  rw [MeasureTheory.integral_const_mul] at hmono
  exact hmono

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.L12dens_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The pointwise estimate on the density -/

/-- The angular integral defining the density is dominated by the square root of the
`ℋ^n`-integrand of the slice, with the weight `s/(1+s)²`: for `s > 0`,
`|L₁₂dens g s| ≤ C (s/(1+s)²) √(∫_θ HkIntegrand α n g s θ)`.

Only the `D_z^0`-term of `HkIntegrand` is used, so the statement is uniform in `n`. -/
private theorem L12dens_abs_le_gen_aux (α : ℝ) (n : ℕ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α n g) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s →
      |Work.Elliptic.L12dens g s| ≤ C * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) := by
  refine ⟨Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1, by positivity,
    fun s hs => ?_⟩
  have hw_pos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hsin_cont : ContinuousOn (fun θ => g s θ) (Set.uIcc (0 : ℝ) (π/2)) := by
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ π/2)]
    exact Work.Elliptic.continuousOn_slice_theta_Iθ g hsm (by simp only [Set.mem_Ioi]; linarith)
  -- pointwise domination of `g²` by the `ℋ^n`-integrand
  have hpt : ∀ θ : ℝ, 0 < θ → θ < π/2 →
      (g s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n g s θ / (Work.Spaces.w s) ^ 2 := by
    intro θ hθ0 hθ1
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
    have hS : 0 < S := by rw [hSdef]; exact Real.rpow_pos_of_pos hsin _
    have hkey := Work.Spaces.sq_le_HkIntegrand_z α n g s θ 0 (Nat.zero_le n)
    simp only [Work.Spaces.DzIter_zero] at hkey
    have hrewrite : (g s θ) ^ 2
        = (g s θ * (Work.Spaces.w s / S)) ^ 2 * (S / Work.Spaces.w s) ^ 2 := by
      rw [mul_pow, div_pow, div_pow]
      field_simp
    have hSsq : S ^ 2 ≤ (1 : ℝ) := by
      have h2 : S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
        rw [hSdef, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hsin)]
        norm_num
      calc S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := h2
        _ ≤ 1 := Real.rpow_le_one (le_of_lt hsin) (Real.sin_le_one _)
            (le_of_lt Work.Spaces.eta_pos)
    have hSw : (S / Work.Spaces.w s) ^ 2 ≤ 1 / (Work.Spaces.w s) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hSsq, pow_pos hw_pos 2]
    rw [hrewrite]
    refine le_trans (mul_le_mul_of_nonneg_right hkey (sq_nonneg _)) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hSw
      (Work.Spaces.HkIntegrand_nonneg α n g s θ)) ?_
    rw [one_div, div_eq_mul_inv]
  have hg2_int : IntegrableOn (fun θ => (g s θ) ^ 2) Work.Spaces.Iθ :=
    ((Work.Elliptic.continuousOn_slice_theta_Iθ g hsm
      (by simp only [Set.mem_Ioi]; linarith)).pow 2).integrableOn_compact isCompact_Icc
  have hk_int : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α n g s θ / (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iθ := (hmem.1 s hs.le).div_const _
  have hg2_le : ∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) / (Work.Spaces.w s) ^ 2 := by
    refine le_trans (integral_mono_ae hg2_int hk_int (Work.Elliptic.ae_restrict_Iθ_of_Ioo hpt)) ?_
    rw [MeasureTheory.integral_div]
  -- Cauchy–Schwarz in the angle
  have hCS : |Work.Elliptic.angMoment g s| ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := by
    have h := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt 0 (π/2) (by positivity)
      (f := Work.Elliptic.Ktheta) (g := fun θ => g s θ)
      Work.Elliptic.continuous_ktheta.continuousOn hsin_cont
    simpa only [Work.Elliptic.angMoment,
      ← Work.Elliptic.integral_Iθ_eq_interval_aux (fun θ => Work.Elliptic.Ktheta θ * g s θ),
      ← Work.Elliptic.integral_Iθ_eq_interval_aux (fun θ => Work.Elliptic.Ktheta θ ^ 2),
      ← Work.Elliptic.integral_Iθ_eq_interval_aux (fun θ => (g s θ) ^ 2)] using h
  have hsqrt_le : Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) / Work.Spaces.w s := by
    refine le_trans (Real.sqrt_le_sqrt hg2_le) ?_
    rw [Real.sqrt_div (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α n g s θ),
      Real.sqrt_sq_eq_abs, abs_of_pos hw_pos]
  have hmain : |Work.Elliptic.L12dens g s| ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * ((s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ)) := by
    have hstep : |Work.Elliptic.angMoment g s| / s
        ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ)
            / Work.Spaces.w s)) / s := by
      rw [div_le_div_iff_of_pos_right hs]
      exact le_trans hCS (mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg _))
    calc |Work.Elliptic.L12dens g s| = |Work.Elliptic.angMoment g s| / s := by
          rw [Work.Elliptic.L12dens_eq_angMoment_div, abs_div, abs_of_pos hs]
      _ ≤ _ := hstep
      _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * ((s / (1 + s) ^ 2)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ)) := by
          rw [Work.Spaces.w]
          field_simp
  refine le_trans hmain ?_
  have hX : 0 ≤ (s / (1 + s) ^ 2)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  calc Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * ((s / (1 + s) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ))
      ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
        * ((s / (1 + s) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hX
    _ = (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1) * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) := by ring

/-! ## Definitional identification of the two densities -/

/-- The elliptic `L₁₂`-density is the fundamental-model density: both are
`∫_θ K(θ) g(s,θ) dθ / s` with the angular weight `K(θ) = 3 sin θ cos²θ`, and
`Iθ = Icc 0 (π/2)`. -/
theorem L12dens_eq_fm (g : ℝ → ℝ → ℝ) :
    Work.FM.L12dens Work.Spaces.K g = Work.Elliptic.L12dens g := by
  funext s
  simp only [Work.FM.L12dens, Work.Elliptic.L12dens, Work.Spaces.Iθ,
    Work.Elliptic.Ktheta, Work.Spaces.K]

/-! ## Integrability -/

theorem L12dens_integrableOn (α : ℝ) (n : ℕ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α n g) :
    MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi 0) := by
  rw [L12dens_eq_fm g]
  obtain ⟨C, hCpos, hCbd⟩ := L12dens_abs_le_gen_aux α n g hsm hmem
  -- the two factors of the pointwise bound are integrable
  have hH_int : IntegrableOn
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) (Set.Ioi 0) :=
    hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hdom : IntegrableOn (fun s => (C / 2) * ((s / (1 + s) ^ 2) ^ 2
      + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ)) (Set.Ioi 0) :=
    (Work.Elliptic.psi_sq_integrable_aux.add hH_int).const_mul (C / 2)
  have hcontOn : ContinuousOn (Work.Elliptic.L12dens g) (Set.Ioi 0) :=
    Work.Elliptic.L12dens_continuousOn_aux g hsm
  refine hdom.mono' (hcontOn.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hHnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ :=
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α n g s θ
  have hAM : 2 * ((s / (1 + s) ^ 2)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ))
      ≤ (s / (1 + s) ^ 2) ^ 2
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ := by
    nlinarith [sq_nonneg ((s / (1 + s) ^ 2)
        - Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ)),
      Real.sq_sqrt hHnn]
  rw [Real.norm_eq_abs]
  calc |Work.Elliptic.L12dens g s| ≤ C * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) := hCbd s hs
    _ = (C / 2) * (2 * ((s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ))) := by ring
    _ ≤ (C / 2) * ((s / (1 + s) ^ 2) ^ 2
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) :=
        mul_le_mul_of_nonneg_left hAM (by linarith)

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.L12f_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- Under the Hardy hypotheses, `L₁₂(f)` has derivative `-L12dens K f` at every point of
`(0,∞)` (`Work.FM.hasDerivAt_L12`), hence is differentiable there and therefore
continuous on `(0,∞)`. -/
theorem L12f_continuousOn (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    ContinuousOn (fun z : ℝ => L12f f z) (Set.Ioi (0 : ℝ)) := by
  have hd : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun x : ℝ => L12f f x) (-(FM.L12dens Spaces.K f z)) z := by
    intro z hz
    exact Work.FM.hasDerivAt_L12 (K := Spaces.K) (f := f) (a := 0) (ρ := z)
      hfH.hint (hfH.hcont z hz) hz
  have hdiff : DifferentiableOn ℝ (fun z : ℝ => L12f f z) (Set.Ioi (0 : ℝ)) :=
    fun z hz => (hd z hz).differentiableAt.differentiableWithinAt
  exact hdiff.continuousOn

end Work.Coercivity
end
-- ===== merged: Submission.Work.Construction.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-! ## General helpers for the derivatives of a separated function `a(z) · b(θ)` -/

theorem deriv_const_mul_fun {a : ℝ} {b : ℝ → ℝ} (x : ℝ) :
    deriv (fun t : ℝ => a * b t) x = a * deriv b x := deriv_const_mul_field a

theorem deriv_mul_const_fun {a : ℝ} {b : ℝ → ℝ} (x : ℝ) :
    deriv (fun t : ℝ => b t * a) x = deriv b x * a := deriv_mul_const_field a

/-- `∂_θ (a(z) b(θ)) = a(z) ∂_θ b(θ)`. -/
theorem pth_mul_radial {a b : ℝ → ℝ} (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => a z * b θ) z θ = a z * deriv b θ := by
  rw [Work.Spaces.pth]
  beta_reduce
  exact deriv_const_mul_fun θ

/-- `∂_z (a(z) b(θ)) = (∂_z a(z)) b(θ)`. -/
theorem pz_mul_radial {a b : ℝ → ℝ} (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => a z * b θ) z θ = deriv a z * b θ := by
  rw [Work.Spaces.pz]
  beta_reduce
  exact deriv_mul_const_fun (a := b θ) (b := a) z

/-- `∂_θ sin(2θ) = 2 cos(2θ)`. -/
theorem deriv_sin_two (θ : ℝ) : deriv (fun t : ℝ => Real.sin (2 * t)) θ
    = 2 * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id' (𝕜 := ℝ) θ).const_mul (2 : ℝ)
  have h : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  rw [h.deriv]
  ring

/-! ## `z ∂_z L₁₂(F)(z) = - (F,K)_{L²_θ}(z)` -/

theorem mul_L12dens_eq_FK {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : z ≠ 0) :
    z * L12dens F z = FK F z := by
  rw [L12dens, FK, Work.FM.L12dens]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
    (fun θ _ => ?_)
  first | (field_simp; ring) | field_simp | ring

/-! ## The derivatives of the profile `F_*` -/

theorem pth_Fstar_eq {α z θ : ℝ} (hα : 0 < α) :
    Work.Spaces.pth (Fstar α) z θ
      = α * (deriv (fun t : ℝ => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
        * Work.FM.Fstar z := by
  have hfun : Fstar α = fun z θ => ((α / Work.Spaces.c α) * Work.FM.Fstar z)
      * Work.Spaces.Gam α θ := by
    funext z θ; rw [Fstar]; ring
  rw [hfun, pth_mul_radial]
  ring

theorem Dz_Fstar_eq {α z θ : ℝ} (hα : 0 < α) (hz : -1 < z) :
    Work.Spaces.Dz (Fstar α) z θ
      = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z * (1 - z) / (1 + z) ^ 3) := by
  have hfun : Fstar α = fun z θ => Work.FM.Fstar z
      * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) := by
    funext z θ; rw [Fstar]; ring
  rw [Work.Spaces.Dz, hfun, pz_mul_radial, Work.FM.deriv_Fstar z hz]
  ring

/-- `F_* - z∂_zF_* = 2α · (Γ/c) · 2z²/(1+z)³ = 2α · AK`; this is the combination that
appears when the modulation constant `λ` is chosen (tex 1357). -/
theorem Fstar_sub_DzFstar {α z θ : ℝ} (hα : 0 < α) (hz : -1 < z) :
    Fstar α z θ - Work.Spaces.Dz (Fstar α) z θ = 2 * α * AK α z θ := by
  have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
  rw [Dz_Fstar_eq hα hz, AK, Fstar, Work.FM.Fstar]
  rcases eq_or_ne (Work.Spaces.c α) 0 with hc | hc
  · simp [hc]
  · field_simp
    ring

/-- **The paper's identity (tex 1347)**: `F_* + z∂_zF_* - (1/α)L₁₂(F_*)F_* = 0`. -/
theorem Fstar_stationary_identity {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z) :
    Fstar α z θ + Work.Spaces.Dz (Fstar α) z θ
      - (1 / α) * L12 (Fstar α) z * Fstar α z θ = 0 := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
  rw [Dz_Fstar_eq hα (by linarith), L12_Fstar_eq hα hα1 hz, Fstar, Work.FM.Fstar]
  first | (field_simp; ring) | field_simp | ring

/-! ## The derivatives of the singular part `Θ` -/

/-- `∂_θ Θ = (1/(2α)) cos(2θ) L₁₂(F)`. -/
theorem pth_Theta_eq {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ} (z θ : ℝ) :
    Work.Spaces.pth (Theta α F) z θ = (1 / (2 * α)) * Real.cos (2 * θ) * L12 F z := by
  have hfun : Theta α F = fun z θ => L12 F z * ((1 / (4 * α)) * Real.sin (2 * θ)) := by
    funext z θ; rw [Theta, s2]; ring
  rw [hfun, pth_mul_radial]
  have hsin : deriv (fun t : ℝ => (1 / (4 * α)) * Real.sin (2 * t)) θ
      = (1 / (4 * α)) * (2 * Real.cos (2 * θ)) := by
    rw [deriv_const_mul_field (v := fun s : ℝ => Real.sin (2 * s)) (u := (1 / (4 * α))),
      deriv_sin_two]
  rw [hsin]
  first | (field_simp; ring) | field_simp | ring


/-! ## The projector profile `AK` -/

theorem L12dens_AK {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (s : ℝ) :
    L12dens (AK α) s = 2 * s / (1 + s) ^ 3 := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  rw [L12dens, Work.FM.L12dens]
  rcases eq_or_ne s 0 with rfl | hs
  · simp [AK]
  · have hpoint : (fun θ : ℝ => Work.Spaces.K θ * AK α s θ / s)
        = fun θ : ℝ => ((Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α)
            * (2 * s / (1 + s) ^ 3) := by
      funext θ
      rw [AK]
      first | (field_simp; ring) | field_simp | ring
    rw [hpoint, MeasureTheory.integral_mul_const]
    have hcint : (∫ a in Set.Icc 0 (Real.pi / 2),
        Work.Spaces.Gam α a * Work.Spaces.K a / Work.Spaces.c α) = 1 := by
      rw [MeasureTheory.integral_div]
      have hval : (∫ a in Set.Icc 0 (Real.pi / 2), Work.Spaces.Gam α a * Work.Spaces.K a)
          = Work.Spaces.c α := rfl
      rw [hval, div_self hc]
    rw [hcint, one_mul]

/-- The improper integral `∫_0^∞ 2s/(1+s)³ ds = 1`. -/
theorem integral_Ioi_two_mul_div_cube :
    ∫ s in Set.Ioi (0 : ℝ), 2 * s / (1 + s) ^ 3 = 1 := by
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun t : ℝ => -2 / (1 + t) + 1 / (1 + t) ^ 2)
    (g' := fun t : ℝ => 2 * t / (1 + t) ^ 3) (a := 0) (l := 0) ?_ ?_ ?_
  · rw [key]
    norm_num
  · intro x hx
    have hx0 : 0 ≤ x := hx
    have hx1 : (1 : ℝ) + x ≠ 0 := by positivity
    have h1 : HasDerivAt (fun t : ℝ => -2 / (1 + t)) (2 / (1 + x) ^ 2) x := by
      simpa using Work.FM.hasDerivAt_div_add_const (-2) 1 x hx1
    have h2 : HasDerivAt (fun t : ℝ => 1 / (1 + t) ^ 2) (-2 / (1 + x) ^ 3) x := by
      have hnum : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
      have hden : HasDerivAt (fun t : ℝ => (1 + t) ^ 2) (2 * (1 + x)) x :=
        Work.FM.hasDerivAt_one_add_sq x
      have h := hnum.div hden (pow_ne_zero 2 hx1)
      convert h using 1
      first | (field_simp; ring) | field_simp | ring
    have h3 : HasDerivAt (fun t : ℝ => -2 / (1 + t) + 1 / (1 + t) ^ 2)
        (2 / (1 + x) ^ 2 + -2 / (1 + x) ^ 3) x := h1.add h2
    have hve : 2 / (1 + x) ^ 2 + -2 / (1 + x) ^ 3 = 2 * x / (1 + x) ^ 3 := by
      first | (field_simp; ring) | field_simp | ring
    rw [hve] at h3
    exact h3
  · intro x hx
    have hx0 : 0 < x := hx
    have hx1 : (0 : ℝ) < 1 + x := by linarith
    positivity
  · have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
      tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
    have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹ ^ 2) atTop (𝓝 0) := by
      simpa using h2.pow 2
    have h4 := (h2.const_mul (-2 : ℝ)).add h3
    simpa [div_eq_mul_inv, inv_pow] using h4

/-- **`L₁₂(AK)(0) = 1`**: the projector profile `(Γ/c) 2z²/(1+z)³` is the (unique) radial
profile whose `L₁₂`-value at `0` is `1`, so that `𝕡` removes the `L₁₂(·)(0)`-component. -/
theorem L12_AK_eq_one {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    L12 (AK α) 0 = 1 := by
  rw [L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun (s := Set.Ioi 0) measurableSet_Ioi
    (fun s _ => show Work.FM.L12dens Work.Spaces.K (AK α) s = 2 * s / (1 + s) ^ 3
      from L12dens_AK hα hα1 s)]
  exact integral_Ioi_two_mul_div_cube

end Work.Construction
end
end
-- ===== merged: Submission.Work.Construction.hasDerivAt_OmegaAns =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.Construction


end Work.Construction
end
end
-- ===== merged: Submission.Work.ConstructionInstance.abs_le_of_linf_H2 =====
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

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ConstructionInstance

/-- **Pointwise `L^∞`(domain) bound for `H²` functions.**  This is the pointwise form of
`Work.Spaces.Linf_H2`: every value `g z θ` on the closed quadrant is bounded by
`100 / √(γ-1)` times the `H²`-norm.  The proof repeats the pointwise estimate
`(g z θ)² ≤ (100/(γ-1)) |g|²_{H²}` that `Linf_H2` establishes before passing to the
supremum, and then takes square roots. -/
theorem abs_le_of_linf_H2 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd g) (hvt : Work.Spaces.VanishTheta g)
    (hdec : Work.Spaces.DecayInZ 2 g) (hmem : Work.Spaces.HkMem α 2 g) :
    ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ 100 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 2 g := by
  have hgam1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hPhi_int : IntegrableOn (fun z => ∫ σ in Iθ, HkIntegrand α 2 g z σ) Iz := hmem.2
  have hbnd : IntegrableOn
      (fun z => (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 g z σ) Iz :=
    hPhi_int.const_mul _
  have hpoint : ∀ z ∈ Iz, ∀ θ ∈ Iθ, (g z θ) ^ 2 ≤ (100 / (gam α - 1)) * HkSq α 2 g := by
    intro z hz θ hθ
    have hAES : AEStronglyMeasurable
        (fun z' => (Dz g z' θ) ^ 2 * (w z') ^ 2) (volume.restrict Iz) := by
      have h1 : Measurable (fun z' => pz g z' θ) := by
        simpa [pz] using measurable_deriv (fun z'' => g z'' θ)
      have hD : Measurable (fun z' => Dz g z' θ) := measurable_id.mul h1
      have h2 : Measurable (fun z' => (Dz g z' θ) ^ 2) := by
        have : Measurable (fun z' => Dz g z' θ * Dz g z' θ) := hD.mul hD
        simpa [pow_two] using this
      have hw : Measurable w := by
        show Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
        have hnum : Measurable (fun z : ℝ => (1 + z) ^ 2) := by
          have h : Measurable (fun z : ℝ => (1 + z) * (1 + z)) :=
            (measurable_const.add measurable_id).mul (measurable_const.add measurable_id)
          simpa [pow_two] using h
        have hden : Measurable (fun z : ℝ => z ^ 2) := by
          have h : Measurable (fun z : ℝ => z * z) := measurable_id.mul measurable_id
          simpa [pow_two] using h
        exact hnum.div hden
      have hw2 : Measurable (fun z' => (w z') ^ 2) := by
        have : Measurable (fun z' => w z' * w z') := hw.mul hw
        simpa [pow_two] using this
      exact (h2.mul hw2).aestronglyMeasurable
    have hFint : IntegrableOn (fun z' => (Dz g z' θ) ^ 2 * (w z') ^ 2) Iz := by
      refine MeasureTheory.Integrable.mono' hbnd hAES ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z' hz' => by
        have hstep := Dz_HardyTheta_HkIntegrand α hα hα1 g hsm hvt hmem z' hz' θ hθ
        have hFnn : 0 ≤ (Dz g z' θ) ^ 2 * (w z') ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
        exact hstep)
    have hHZ : (g z θ) ^ 2 ≤ ∫ z' in Iz, (Dz g z' θ) ^ 2 * (w z') ^ 2 :=
      HardyZ g θ hsm hθ (by simpa using hdec 0 0 (by norm_num) θ hθ) hFint z hz
    have hIntLe : ∫ z' in Iz, (Dz g z' θ) ^ 2 * (w z') ^ 2
        ≤ (100 / (gam α - 1)) * HkSq α 2 g := by
      calc ∫ z' in Iz, (Dz g z' θ) ^ 2 * (w z') ^ 2
          ≤ ∫ z' in Iz, (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 g z' σ :=
            MeasureTheory.setIntegral_mono_of_nonneg
              (fun z' _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
              (fun z' hz' => Dz_HardyTheta_HkIntegrand α hα hα1 g hsm hvt hmem z' hz' θ hθ)
              hbnd
        _ = (100 / (gam α - 1)) * ∫ z' in Iz, ∫ σ in Iθ, HkIntegrand α 2 g z' σ := by
            rw [MeasureTheory.integral_const_mul]
        _ = (100 / (gam α - 1)) * HkSq α 2 g := rfl
    exact le_trans hHZ hIntLe
  have hAle : (100 / (gam α - 1)) * HkSq α 2 g
      ≤ (100 / Real.sqrt (gam α - 1)) ^ 2 * HkSq α 2 g := by
    rw [div_pow, Real.sq_sqrt hgam1.le]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by norm_num : (100 : ℝ) ≤ 100 ^ 2) hgam1.le)
      (HkSq_nonneg α 2 g)
  have hsqrt : Real.sqrt ((100 / (gam α - 1)) * HkSq α 2 g)
      ≤ (100 / Real.sqrt (gam α - 1)) * HkNorm α 2 g := by
    calc Real.sqrt ((100 / (gam α - 1)) * HkSq α 2 g)
        ≤ Real.sqrt ((100 / Real.sqrt (gam α - 1)) ^ 2 * HkSq α 2 g) := Real.sqrt_le_sqrt hAle
      _ = (100 / Real.sqrt (gam α - 1)) * Real.sqrt (HkSq α 2 g) := by
          rw [Real.sqrt_mul (sq_nonneg _),
              Real.sqrt_sq (div_nonneg (by norm_num) (Real.sqrt_nonneg _))]
      _ = (100 / Real.sqrt (gam α - 1)) * HkNorm α 2 g := rfl
  intro z θ hz hθ
  have hzIz : z ∈ Iz := by simpa [Iz] using hz
  exact le_trans (Real.abs_le_sqrt (hpoint z hzIz θ hθ)) hsqrt

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.profiles_of_axiNoSwirl_div =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Profiles of an axisymmetric no-swirl divergence-free field

Given a `C¹` axisymmetric no-swirl field `u : ℝ³ → ℝ³` which is divergence free, we extract its
radial and axial profiles `u_r, u_z : ℝ → ℝ → ℝ` (functions of the coordinates `(r, x₃)` of the
meridian half plane).  Off the symmetry axis `u = u_r e_r + u_z e₃`, the profiles are differentiable
on `r > 0`, and the divergence-free condition becomes the cylindrical divergence identity

  `∂_r u_r + u_r / r + ∂_z u_z = 0`.

The profiles are read off on the meridian `θ = 0`, where `u_r` and `u_z` are exactly the first and
third coordinates of `u` (the reflection symmetry of a no-swirl field kills the angular component
there), so no quotient by `r` is needed in their definition.
-/

set_option autoImplicit false

open Work.Cyl
open Filter
open scoped Topology

namespace Work.ConstructionInstance

/-- The point of the meridian `θ = 0` with radial coordinate `r` and axial coordinate `z`. -/
def mer (r z : ℝ) : R3 := !₂[r, 0, z]

@[simp] lemma mer_apply_zero (r z : ℝ) : (mer r z) 0 = r := by simp [mer]
@[simp] lemma mer_apply_one (r z : ℝ) : (mer r z) 1 = 0 := by simp [mer]
@[simp] lemma mer_apply_two (r z : ℝ) : (mer r z) 2 = z := by simp [mer]















end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.CoreResiduals.VorticityEquation.fderiv_comp_radial_axial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.VorticityEquation

open Work.Cyl

/-- The directional derivative of `y ↦ G (radial y) (axial y)` in the direction `v`, for a
two-variable function `G` differentiable at `(radial x, axial x)` and `x` off the symmetry axis.

The pair `(radial, axial)` moves with velocity `(x₀v₀+x₁v₁)/r` and `v₂`, so the derivative is
`∂_r G · (x₀v₀+x₁v₁)/r + ∂_z G · v₂`. -/
theorem fderiv_comp_radial_axial (G : ℝ → ℝ → ℝ) (x v : Work.Cyl.R3)
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : Work.Cyl.R3 => G (Work.Cyl.radial y) (Work.Cyl.axial y)) x v
      = Work.Cyl.pdR G (Work.Cyl.radial x) (Work.Cyl.axial x)
          * ((x 0 * v 0 + x 1 * v 1) / Work.Cyl.radial x)
        + Work.Cyl.pdZ G (Work.Cyl.radial x) (Work.Cyl.axial x) * v 2 := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  -- differentiability of the composite
  have hGd : DifferentiableAt ℝ (fun y : R3 => G (radial y) (axial y)) x := by
    have hpair : DifferentiableAt ℝ (fun y : R3 => (radial y, axial y)) x :=
      (differentiableAt_radial x hrne).hasFDerivAt.prodMk
        (differentiableAt_axial x).hasFDerivAt |>.differentiableAt
    have h := hG.comp x hpair
    convert h using 1
    funext y; rfl
  -- split `v` in the standard basis
  have hv : v = v 0 • e0 + v 1 • e1 + v 2 • eZ := by
    refine ext_coord ?_ ?_ ?_ <;> simp [e0, e1, eZ, FiniteTimeSingularity.e]
  -- the values of the differential on the three basis vectors
  have h0 : fderiv ℝ (fun y : R3 => G (radial y) (axial y)) x e0
      = pdR G (radial x) (axial x) * (x 0 / radial x) := by
    rw [fderiv_apply_eq_deriv_line _ _ _ hGd]
    exact (hasDerivAt_comp_cyl_e0 G x hG hr).deriv
  have h1 : fderiv ℝ (fun y : R3 => G (radial y) (axial y)) x e1
      = pdR G (radial x) (axial x) * (x 1 / radial x) := by
    rw [fderiv_apply_eq_deriv_line _ _ _ hGd]
    exact (hasDerivAt_comp_cyl_e1 G x hG hr).deriv
  have h2 : fderiv ℝ (fun y : R3 => G (radial y) (axial y)) x eZ
      = pdZ G (radial x) (axial x) := by
    rw [fderiv_apply_eq_deriv_line _ _ _ hGd]
    exact (hasDerivAt_comp_cyl_eZ G x hG hr).deriv
  have hsplit : fderiv ℝ (fun y : R3 => G (radial y) (axial y)) x v
      = fderiv ℝ (fun y : R3 => G (radial y) (axial y)) x (v 0 • e0 + v 1 • e1 + v 2 • eZ) :=
    congrArg (fderiv ℝ (fun y : R3 => G (radial y) (axial y)) x) hv
  rw [hsplit, map_add, map_add, map_smul, map_smul, map_smul, h0, h1, h2,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

end Work.CoreResiduals.VorticityEquation
end
-- ===== merged: Submission.Work.CoreResiduals.VorticityEquation.fderiv_cylField_angularVec =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.VorticityEquation

open Work.Cyl

/-- `angularVec x = -x₀ e₁ + x₁ e₀` is the linear vector `r e_θ`, written in the standard
basis. -/
private lemma angularVec_eq_smul_basis (x : R3) :
    angularVec x = (-x 1) • basisVec 0 + (x 0) • basisVec 1 := by
  apply ext_coord <;> simp [angularVec, basisVec, FiniteTimeSingularity.e]

/-- The derivative of `cylField ur uz` in the angular direction `angularVec x = r e_θ`.  Since the
field is `u_r(r,x₃) e_r + u_z(r,x₃) e₃` and `r e_θ` is tangent to the circle `r = const`, only the
`r e_r`-factor contributes: the profile factors differentiate to zero along this direction, and
`d(r e_r)[r e_θ] = r e_θ`. -/
theorem fderiv_cylField_angularVec (ur uz : ℝ → ℝ → ℝ) (x : Work.Cyl.R3)
    (hur : Work.Cyl.DiffAt2 ur (Work.Cyl.radial x) (Work.Cyl.axial x))
    (huz : Work.Cyl.DiffAt2 uz (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (Work.Cyl.cylField ur uz) x (Work.Cyl.angularVec x)
      = Work.Cyl.redR ur (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.angularVec x := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hd := differentiableAt_cylField ur uz x hur huz hr
  rw [angularVec_eq_smul_basis x, map_add, map_smul, map_smul]
  apply ext_coord
  · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [fderiv_apply_coord (cylField ur uz) x 0 0 hd, fderiv_apply_coord (cylField ur uz) x 1 0 hd,
      pd_cylField_00 ur uz x hur hr, pd_cylField_10 ur uz x hur hr]
    simp only [redR, basisVec_zero, basisVec_one, e0_apply_zero, e1_apply_zero]
    field_simp
    ring
  · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [fderiv_apply_coord (cylField ur uz) x 0 1 hd, fderiv_apply_coord (cylField ur uz) x 1 1 hd,
      pd_cylField_01 ur uz x hur hr, pd_cylField_11 ur uz x hur hr]
    simp only [redR, basisVec_zero, basisVec_one, e0_apply_one, e1_apply_one]
    field_simp
    ring
  · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [fderiv_apply_coord (cylField ur uz) x 0 2 hd, fderiv_apply_coord (cylField ur uz) x 1 2 hd,
      pd_cylField_02 ur uz x huz hr, pd_cylField_12 ur uz x huz hr]
    simp only [redR, basisVec_zero, basisVec_one, e0_apply_two, e1_apply_two]
    field_simp
    ring

end Work.CoreResiduals.VorticityEquation
end
-- ===== merged: Submission.Work.Cyl.alpha_mul_pow_mul_pdR =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial chain rule `r ↦ ρ ^ α`

If `F` is differentiable at `(ρ ^ α, θ)`, then differentiating `ρ' ↦ F (ρ' ^ α) θ` and using
`(ρ ^ α)' = α ρ ^ (α - 1)` gives `α ρ ^ α ∂_r F (ρ ^ α, θ) = ρ ∂_r (F (· ^ α, θ)) (ρ, θ)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Cyl


end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.differentiableAt_rho_theta_comp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-!
# Differentiability of `x ↦ F (ρ x) (θ x)`

The polar (spherical) coordinates `(ρ, θ)` are smooth functions of `x ∈ ℝ³` away from the
axis `r = 0`: `ρ = √(r² + x₃²)` is a composition of a smooth quadratic function with `√` (which
is differentiable off `0`), and `θ = arctan(x₃ / r)` is a composition of `arctan` with the
differentiable quotient `x₃ / r` (legitimate since `r ≠ 0` there).

Consequently, if `F` is differentiable as a function of two variables at the point
`(ρ x, θ x)`, then `y ↦ F (ρ y) (θ y)` is differentiable at `x`.  This is the composite
chain rule used to differentiate the reduced fields `F(ρ, θ)` of the paper.
-/

/-! ## Differentiability of the individual coordinates -/

/-- `ρ = √(radSq + axial²)` is differentiable away from the origin, i.e. whenever the radicand
does not vanish. -/
lemma differentiableAt_rho_of_ne (x : R3) (h : radSq x + axial x ^ 2 ≠ 0) :
    DifferentiableAt ℝ rho x := by
  have hcoord : ∀ i : Fin 3, DifferentiableAt ℝ (fun y : R3 => y i) x := fun i =>
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) x i).differentiableAt
  have hradSq : DifferentiableAt ℝ (fun y : R3 => radSq y) x := by
    show DifferentiableAt ℝ (fun y : R3 => y 0 ^ 2 + y 1 ^ 2) x
    exact ((hcoord 0).pow 2).add ((hcoord 1).pow 2)
  have hax : DifferentiableAt ℝ (fun y : R3 => axial y) x := differentiableAt_axial x
  have hsum : DifferentiableAt ℝ (fun y : R3 => radSq y + axial y ^ 2) x :=
    hradSq.add (hax.pow 2)
  exact hsum.sqrt h

/-- `ρ` is differentiable at any point off the axis (`radial x > 0`). -/
lemma differentiableAt_rho_of_radial_pos (x : R3) (hr : 0 < radial x) :
    DifferentiableAt ℝ rho x := by
  refine differentiableAt_rho_of_ne x ?_
  have hpos : 0 < radSq x := by rw [← radial_sq]; exact pow_pos hr 2
  exact ne_of_gt (add_pos_of_pos_of_nonneg hpos (sq_nonneg _))

/-- `θ = arctan(axial / radial)` is differentiable at any point off the axis. -/
lemma differentiableAt_theta_of_radial_ne (x : R3) (hr : radial x ≠ 0) :
    DifferentiableAt ℝ theta x := by
  have hax : DifferentiableAt ℝ (fun y : R3 => axial y) x := differentiableAt_axial x
  have hradial : DifferentiableAt ℝ (fun y : R3 => radial y) x := differentiableAt_radial x hr
  have hdiv : DifferentiableAt ℝ (fun y : R3 => axial y / radial y) x :=
    hax.mul (hradial.inv hr)
  exact hdiv.arctan

/-! ## The composite chain rule -/

theorem differentiableAt_rho_theta_comp (F : ℝ → ℝ → ℝ) (x : Work.Cyl.R3)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rho x) (Work.Cyl.theta x)) (hr : 0 < Work.Cyl.radial x) :
    DifferentiableAt ℝ (fun y : Work.Cyl.R3 => F (Work.Cyl.rho y) (Work.Cyl.theta y)) x := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hrho : DifferentiableAt ℝ rho x := differentiableAt_rho_of_radial_pos x hr
  have htheta : DifferentiableAt ℝ theta x := differentiableAt_theta_of_radial_ne x hrne
  have hpair : DifferentiableAt ℝ (fun y : R3 => (rho y, theta y)) x := hrho.prodMk htheta
  exact hF.comp x hpair

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.div_psiField =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The divergence of the stream-function field `psiField ψ`

Off the axis, the no-swirl axisymmetric field with stream function `ψ`,
`u_r = ∂_z ψ`, `u_z = -(ψ/r) - ∂_r ψ`, is divergence free.  Indeed, in the cylindrical
coordinates of `Work.Cyl`, `div u = ∂_r u_r + u_r/r + ∂_z u_z`, and with the above `u_r, u_z`

`∂_r u_r + u_r / r + ∂_z u_z = ∂_r ∂_z ψ + (∂_z ψ)/r - (∂_z ψ)/r - ∂_z ∂_r ψ = 0`

by the symmetry of the mixed second partials of `ψ`.

This file proves that statement (`Work.Cyl.div_psiField`).  Along the way it builds the small
amount of second-derivative API for the *curried* partials `pdR`, `pdZ` that the argument needs:
the pair map `(r,z) ↦ pdR ψ r z` (resp. `(r,z) ↦ pdZ ψ r z`) of a `C²` function is differentiable
(its value being `fderiv` of the uncurried function evaluated on `(1,0)`, resp. `(0,1)`), and the
two mixed second partials agree.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix

namespace Work.Cyl

/-! ## Differentiating the evaluation of a continuous linear map -/

private lemma fderiv_eval_const (G : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)) (v p₀ : ℝ × ℝ)
    (hG : DifferentiableAt ℝ G p₀) :
    fderiv ℝ (fun p => G p v) p₀ = (ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ G p₀) := by
  have hL : HasFDerivAt (fun y : (ℝ × ℝ) →L[ℝ] ℝ => y v)
      ((ContinuousLinearMap.apply ℝ ℝ v) : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ) (G p₀) := by
    have h0 := ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.apply ℝ ℝ v : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ) (x := G p₀)
    rw [show (⇑(ContinuousLinearMap.apply ℝ ℝ v : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ)) = (fun y => y v)
      from by funext y; exact ContinuousLinearMap.apply_apply v y] at h0
    exact h0
  have hcomp := hL.comp p₀ hG.hasFDerivAt
  rw [show (fun p => G p v) = ((fun y : (ℝ × ℝ) →L[ℝ] ℝ => y v) ∘ G) from rfl] at *
  exact hcomp.fderiv

/-! ## The pair maps of `pdR f` and `pdZ f` for a `C²` function -/

/-- If `(r,z) ↦ ψ r z` is `C²` near `(r,z)`, then `(r,z) ↦ ∂_r ψ (r,z)` is differentiable there:
it is the `fderiv` of the uncurried function, evaluated on `(1,0)`. -/
private theorem diffAt2_pdR_of_contDiffAt_two (f : ℝ → ℝ → ℝ) (r z : ℝ)
    (h : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (r, z)) : DiffAt2 (pdR f) r z := by
  show DifferentiableAt ℝ (fun p : ℝ × ℝ => pdR f p.1 p.2) (r, z)
  have hev : ∀ᶠ p in nhds ((r, z) : ℝ × ℝ),
      DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) p :=
    (h.eventually (by simp)).mono (fun p hp => hp.differentiableAt (by simp))
  have heq : (fun p : ℝ × ℝ => pdR f p.1 p.2) =ᶠ[nhds (r, z)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (1, 0)) := by
    filter_upwards [hev] with p hp
    exact (fderiv_prod_apply_fst f p.1 p.2 hp).symm
  rw [Filter.EventuallyEq.differentiableAt_iff heq]
  have hG : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) :=
    (h.fderiv_right_succ).differentiableAt_one
  exact hG.clm_apply (differentiableAt_const ((1, 0) : ℝ × ℝ))

/-- If `(r,z) ↦ ψ r z` is `C²` near `(r,z)`, then `(r,z) ↦ ∂_z ψ (r,z)` is differentiable there:
it is the `fderiv` of the uncurried function, evaluated on `(0,1)`. -/
private theorem diffAt2_pdZ_of_contDiffAt_two (f : ℝ → ℝ → ℝ) (r z : ℝ)
    (h : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (r, z)) : DiffAt2 (pdZ f) r z := by
  show DifferentiableAt ℝ (fun p : ℝ × ℝ => pdZ f p.1 p.2) (r, z)
  have hev : ∀ᶠ p in nhds ((r, z) : ℝ × ℝ),
      DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) p :=
    (h.eventually (by simp)).mono (fun p hp => hp.differentiableAt (by simp))
  have heq : (fun p : ℝ × ℝ => pdZ f p.1 p.2) =ᶠ[nhds (r, z)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (0, 1)) := by
    filter_upwards [hev] with p hp
    exact (fderiv_prod_apply_snd f p.1 p.2 hp).symm
  rw [Filter.EventuallyEq.differentiableAt_iff heq]
  have hG : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) :=
    (h.fderiv_right_succ).differentiableAt_one
  exact hG.clm_apply (differentiableAt_const ((0, 1) : ℝ × ℝ))

/-! ## Symmetry of the mixed second partials -/

/-- For a `C²` function of two variables, the two mixed second partials of the curried function
agree (`Clairaut`), the common value being the (symmetric) second `fderiv` of the uncurried
function evaluated on the two coordinate directions. -/
private theorem pdRZ_eq_pdZR_of_contDiffAt_two (f : ℝ → ℝ → ℝ) (r z : ℝ)
    (h : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (r, z)) : pdRZ f r z = pdZR f r z := by
  have hev : ∀ᶠ p in nhds ((r, z) : ℝ × ℝ),
      DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) p :=
    (h.eventually (by simp)).mono (fun p hp => hp.differentiableAt (by simp))
  have hdR : DiffAt2 (pdR f) r z := diffAt2_pdR_of_contDiffAt_two f r z h
  have hdZ : DiffAt2 (pdZ f) r z := diffAt2_pdZ_of_contDiffAt_two f r z h
  have hZev : (fun p : ℝ × ℝ => pdZ f p.1 p.2) =ᶠ[nhds (r, z)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (0, 1)) := by
    filter_upwards [hev] with p hp
    exact (fderiv_prod_apply_snd f p.1 p.2 hp).symm
  have hRev : (fun p : ℝ × ℝ => pdR f p.1 p.2) =ᶠ[nhds (r, z)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (1, 0)) := by
    filter_upwards [hev] with p hp
    exact (fderiv_prod_apply_fst f p.1 p.2 hp).symm
  have hG : DifferentiableAt ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) :=
    (h.fderiv_right_succ).differentiableAt_one
  have hsymm : IsSymmSndFDerivAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) (r, z) :=
    h.isSymmSndFDerivAt (by simp)
  have e1 : pdRZ f r z = fderiv ℝ (fun p : ℝ × ℝ => pdZ f p.1 p.2) (r, z) (1, 0) := by
    rw [show pdRZ f r z = pdR (pdZ f) r z from rfl,
      ← fderiv_prod_apply_fst (pdZ f) r z hdZ]
  have e4 : fderiv ℝ (fun p : ℝ × ℝ => pdR f p.1 p.2) (r, z) (0, 1) = pdZR f r z := by
    rw [fderiv_prod_apply_snd (pdR f) r z hdR]
    rfl
  calc pdRZ f r z
      = fderiv ℝ (fun p : ℝ × ℝ => pdZ f p.1 p.2) (r, z) (1, 0) := e1
    _ = fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (0, 1))
          (r, z) (1, 0) := by
        rw [Filter.EventuallyEq.fderiv_eq hZev]
    _ = (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) (1, 0)) (0, 1) := by
        rw [fderiv_eval_const _ (0, 1) (r, z) hG, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.apply_apply]
    _ = (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2)) (r, z) (0, 1)) (1, 0) :=
        hsymm.eq (1, 0) (0, 1)
    _ = fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (1, 0))
          (r, z) (0, 1) := by
        rw [fderiv_eval_const _ (1, 0) (r, z) hG, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.apply_apply]
    _ = fderiv ℝ (fun p : ℝ × ℝ => pdR f p.1 p.2) (r, z) (0, 1) := by
        rw [Filter.EventuallyEq.fderiv_eq hRev]
    _ = pdZR f r z := e4

/-! ## The two-variable field `u_z = -(ψ/r) - ∂_r ψ` -/

/-- The partial derivative in `z` of `u_z(r,z) = -(ψ r z)/r - ∂_r ψ (r,z)`. -/
private theorem pdZ_uz_eq (ψ : ℝ → ℝ → ℝ) (r z : ℝ)
    (hψ : DiffAt2 ψ r z) (hdR : DiffAt2 (pdR ψ) r z) :
    pdZ (fun r z => -(ψ r z / r) - pdR ψ r z) r z = -(pdZ ψ r z) / r - pdZR ψ r z := by
  have hA : HasDerivAt (fun z' : ℝ => ψ r z' / r) (pdZ ψ r z / r) z :=
    (differentiableAt_slice_snd ψ r z hψ).hasDerivAt.div_const r
  have hB : HasDerivAt (fun z' : ℝ => pdR ψ r z') (pdZR ψ r z) z := by
    have h : DifferentiableAt ℝ (fun z' : ℝ => pdR ψ r z') z :=
      hdR.comp z ((differentiableAt_const r).prodMk (differentiableAt_id (x := z)))
    exact h.hasDerivAt
  have hsum : HasDerivAt (fun z' : ℝ => -(ψ r z' / r) - pdR ψ r z')
      (-(pdZ ψ r z / r) - pdZR ψ r z) z := hA.neg.sub hB
  rw [pdZ, hsum.deriv, neg_div]

/-- Differentiability of the two-variable function `u_z(r,z) = -(ψ r z)/r - ∂_r ψ (r,z)` off the
axis. -/
private theorem diffAt2_uz (ψ : ℝ → ℝ → ℝ) (r z : ℝ) (hr : r ≠ 0)
    (hψ : DiffAt2 ψ r z) (hdR : DiffAt2 (pdR ψ) r z) :
    DiffAt2 (fun r z => -(ψ r z / r) - pdR ψ r z) r z := by
  show DifferentiableAt ℝ (fun p : ℝ × ℝ => -(ψ p.1 p.2 / p.1) - pdR ψ p.1 p.2) (r, z)
  have hψ' : DifferentiableAt ℝ (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z) := hψ
  have hdiv : DifferentiableAt ℝ (fun p : ℝ × ℝ => ψ p.1 p.2 / p.1) (r, z) := by
    fun_prop (disch := exact hr)
  have hdR' : DifferentiableAt ℝ (fun p : ℝ × ℝ => pdR ψ p.1 p.2) (r, z) := hdR
  exact hdiv.neg.sub hdR'

/-! ## The main theorem -/

theorem div_psiField (ψ : ℝ → ℝ → ℝ) (x : Work.Cyl.R3)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (Work.Cyl.radial x, Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    FiniteTimeSingularity.div (Work.Cyl.psiField ψ) x = 0 := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hdψ : DiffAt2 ψ (radial x) (axial x) := hψ.differentiableAt (by simp)
  have hdR : DiffAt2 (pdR ψ) (radial x) (axial x) := diffAt2_pdR_of_contDiffAt_two ψ _ _ hψ
  have hdZ : DiffAt2 (pdZ ψ) (radial x) (axial x) := diffAt2_pdZ_of_contDiffAt_two ψ _ _ hψ
  have huz : DiffAt2 (fun r z => -(ψ r z / r) - pdR ψ r z) (radial x) (axial x) :=
    diffAt2_uz ψ _ _ hrne hdψ hdR
  have hval := pdZ_uz_eq ψ (radial x) (axial x) hdψ hdR
  have hcl := pdRZ_eq_pdZR_of_contDiffAt_two ψ (radial x) (axial x) hψ
  show FiniteTimeSingularity.div
    (cylField (pdZ ψ) (fun r z => -(ψ r z / r) - pdR ψ r z)) x = 0
  rw [div_cylField (pdZ ψ) (fun r z => -(ψ r z / r) - pdR ψ r z) x hdZ huz hr]
  rw [show pdR (pdZ ψ) (radial x) (axial x) = pdRZ ψ (radial x) (axial x) from rfl, hval, hcl]
  ring

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.eTheta_sub_norm_mul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted Lipschitz bound for the angular frame vector `e_θ`

`e_θ(x) = r(x) e_θ(x) / r(x)` is a unit vector off the axis `r = 0`, but is `0` *on* the axis
(`eTheta` is defined as `(1/r) • angularVec` and `angularVec = 0` when `r = 0`), so it is
discontinuous there.  The geometric input needed by the paper is that the jump is controlled once
weighted by the radius: for all `x y : ℝ³`,

  `‖e_θ x - e_θ y‖ * r(y) ≤ 2 * dist x y`.

Proof.  Write `r = r(x)`, `s = r(y)`, `A = r e_θ(x) = (-x₁, x₀, 0)` and `B = r e_θ(y)`, so that
`e_θ(x) = (1/r) • A`, `e_θ(y) = (1/s) • B`, and `s • (e_θ x - e_θ y) = (s/r) • A - B`.

* If `r = 0` then `A = 0` and the left hand side is `‖B‖ = s ≤ |r - s| ≤ dist x y` (`r` is
  1-Lipschitz, `Work.Cyl.abs_radial_sub_le_dist`).
* If `r > 0`, multiplying by `r` reduces the claim to `‖s • A - r • B‖ ≤ 2 r * dist x y`.  Its
  square is `2 r² s² - 2 r s c` with `c = ⟪A,B⟫ = x₀y₀ + x₁y₁`, while
  `dist x y ² ≥ r² + s² - 2c`.  Comparing the two reduces the claim to the elementary arithmetic
  fact `0 ≤ 2r³ + r s² + c (s - 4r)` for `|c| ≤ r s` (`Work.Cyl.scalar_arith_key`), proved by a
  two-case linear argument in `c`.

The constant `2` is optimal but not attained: for `y = (1,0,0)` (so `e_θ y = (0,1,0)`) and
`x = ε • (-1,0,0)` (so `e_θ x = (0,-1,0)`) the two sides are `2` and `2(1+ε)`, whose ratio tends
to `1` as `ε → 0⁺`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix

namespace Work.Cyl

/-- `r e_θ = angularVec`: the angular frame vector scaled by the distance to the axis is the
(smooth) angular coordinate vector. -/
private lemma radial_smul_eTheta (x : R3) : radial x • eTheta x = angularVec x := by
  by_cases h : radial x = 0
  · have hA : angularVec x = 0 := by
      obtain ⟨h1, h2⟩ := (radial_eq_zero_iff x).mp h
      refine ext_coord ?_ ?_ ?_ <;> simp [angularVec, h1, h2]
    simp [eTheta, h, hA]
  · rw [eTheta, one_div, smul_smul, mul_inv_cancel₀ h, one_smul]

theorem eTheta_sub_norm_mul_le (x y : Work.Cyl.R3) :
    ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ * Work.Cyl.radial y ≤ 2 * dist x y := by
  have h1 : ‖eTheta x - eTheta y‖ * radial y = ‖radial y • (eTheta x - eTheta y)‖ := by
    rw [norm_smul_of_nonneg (radial_nonneg y), mul_comm]
  rw [h1]
  have hsmul : radial y • (eTheta x - eTheta y)
      = (radial y / radial x) • angularVec x - angularVec y := by
    rw [smul_sub]
    congr 1
    · simp only [eTheta, one_div, div_eq_mul_inv, one_mul, smul_smul]
    · rw [radial_smul_eTheta]
  rw [hsmul]
  by_cases h0 : radial x = 0
  · -- `x` is on the axis: `e_θ x = 0` and the claim is `r(y) ≤ 2 dist x y`
    have hA0 : angularVec x = 0 := by
      obtain ⟨h1, h2⟩ := (radial_eq_zero_iff x).mp h0
      refine ext_coord ?_ ?_ ?_ <;> simp [angularVec, h1, h2]
    rw [h0, hA0]
    simp only [div_zero, zero_smul, zero_sub, norm_neg]
    rw [norm_angularVec]
    have hb : radial y = |radial x - radial y| := by
      rw [h0, zero_sub, abs_neg, abs_of_nonneg (radial_nonneg y)]
    rw [hb]
    linarith [abs_radial_sub_le_dist x y, abs_nonneg (radial x - radial y)]
  · -- off the axis: reduce to a squared estimate
    have hpos : 0 < radial x := lt_of_le_of_ne (radial_nonneg x) (Ne.symm h0)
    have hcoef : radial x * (radial y * (radial x)⁻¹) = radial y := by
      rw [← mul_assoc, mul_comm (radial x) (radial y), mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hpos), mul_one]
    have hkey : radial x • ((radial y / radial x) • angularVec x - angularVec y)
        = radial y • angularVec x - radial x • angularVec y := by
      rw [smul_sub, smul_smul, div_eq_mul_inv, hcoef]
    have hmain : ‖radial y • angularVec x - radial x • angularVec y‖
        ≤ 2 * radial x * dist x y := by
      have hc : |x 0 * y 0 + x 1 * y 1| ≤ radial x * radial y := by
        rw [← inner_angularVec]; exact abs_inner_angularVec_le x y
      have hscal := scalar_arith_key (radial x) (radial y) (x 0 * y 0 + x 1 * y 1)
        (radial_nonneg x) (radial_nonneg y) hc
      have hAA : inner ℝ (angularVec x) (angularVec x) = radial x ^ 2 := by
        rw [real_inner_self_eq_norm_sq, norm_angularVec]
      have hBB : inner ℝ (angularVec y) (angularVec y) = radial y ^ 2 := by
        rw [real_inner_self_eq_norm_sq, norm_angularVec]
      have hAB : inner ℝ (angularVec x) (angularVec y) = x 0 * y 0 + x 1 * y 1 :=
        inner_angularVec x y
      have hBA : inner ℝ (angularVec y) (angularVec x) = x 0 * y 0 + x 1 * y 1 := by
        rw [inner_angularVec]; ring
      have hsqL : ‖radial y • angularVec x - radial x • angularVec y‖ ^ 2
          = 2 * radial x ^ 2 * radial y ^ 2
            - 2 * radial x * radial y * (x 0 * y 0 + x 1 * y 1) := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
          real_inner_smul_right, hAA, hBB, hAB, hBA]
        ring
      have hβ := radial_sq_sub_coord_le_dist_sq x y
      have hX : 0 ≤ 2 * radial x * dist x y := by positivity
      have hβ' : 4 * radial x ^ 2
            * (radial x ^ 2 + radial y ^ 2 - 2 * (x 0 * y 0 + x 1 * y 1))
          ≤ 4 * radial x ^ 2 * dist x y ^ 2 :=
        mul_le_mul_of_nonneg_left hβ (by positivity)
      have hscal' : 0 ≤ 2 * radial x
          * (2 * radial x ^ 3 + radial x * radial y ^ 2
              + (x 0 * y 0 + x 1 * y 1) * (radial y - 4 * radial x)) :=
        mul_nonneg (by positivity) hscal
      have hsq : ‖radial y • angularVec x - radial x • angularVec y‖ ^ 2
          ≤ (2 * radial x * dist x y) ^ 2 := by
        rw [hsqL]
        nlinarith [hβ', hscal']
      rw [sq_le_sq] at hsq
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hX] at hsq
    have hz : radial x * ‖(radial y / radial x) • angularVec x - angularVec y‖
        = ‖radial y • angularVec x - radial x • angularVec y‖ := by
      rw [← hkey, norm_smul_of_nonneg (le_of_lt hpos)]
    refine le_of_mul_le_mul_left ?_ hpos
    rw [hz]
    calc ‖radial y • angularVec x - radial x • angularVec y‖
        ≤ 2 * radial x * dist x y := hmain
      _ = radial x * (2 * dist x y) := by ring

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.fderiv_radial_apply =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

theorem fderiv_radial_apply (x v : Work.Cyl.R3) (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ Work.Cyl.radial x v = (x 0 * v 0 + x 1 * v 1) / Work.Cyl.radial x := by
  have hd : DifferentiableAt ℝ radial x := differentiableAt_radial x (ne_of_gt hr)
  rw [fderiv_apply_eq_deriv_line radial x v hd]
  -- the derivative along the line `t ↦ x + t • v` of the squared radius
  have h0 : HasDerivAt (fun t : ℝ => x 0 + t * v 0) (v 0) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v 0)).const_add (x 0)
  have h1 : HasDerivAt (fun t : ℝ => x 1 + t * v 1) (v 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v 1)).const_add (x 1)
  have hradsq : HasDerivAt (fun t : ℝ => radSq (x + t • v))
      (2 * (x 0 * v 0) + 2 * (x 1 * v 1)) 0 := by
    have hfun : (fun t : ℝ => radSq (x + t • v)) =
        fun t : ℝ => (x 0 + t * v 0) * (x 0 + t * v 0)
          + (x 1 + t * v 1) * (x 1 + t * v 1) := by
      funext t; simp [radSq, pow_two]
    rw [hfun]
    have h := (h0.mul h0).add (h1.mul h1)
    convert h using 1
    ring
  have hne : radSq (x + (0:ℝ) • v) ≠ 0 := by
    rw [zero_smul, add_zero, ← radial_sq]
    exact pow_ne_zero 2 (ne_of_gt hr)
  -- `radial` is `Real.sqrt ∘ radSq`, so the chain rule with `Real.hasDerivAt_sqrt` applies
  have hmain : (fun t : ℝ => radial (x + t • v)) =
      fun t : ℝ => Real.sqrt (radSq (x + t • v)) := by
    funext t; rw [radial]
  rw [hmain]
  have hder := hradsq.sqrt hne
  have hval : (2 * (x 0 * v 0) + 2 * (x 1 * v 1)) / (2 * Real.sqrt (radSq (x + (0:ℝ) • v)))
      = (x 0 * v 0 + x 1 * v 1) / radial x := by
    rw [zero_smul, add_zero, radial]
    have hpos : 0 < radSq x := by rw [← radial_sq]; positivity
    have hsne : Real.sqrt (radSq x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    field_simp
  rw [hval] at hder
  exact hder.deriv

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.isOdd_axiField =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Work.Cyl

namespace Work.Cyl

/-!
# Parity of the no-swirl field `axiField a b`

`axiField a b x = a (r²) (x₃) • (x₀, x₁, 0) + b (r²) (x₃) • e₃` with `r² = x₀² + x₁²`.

The parity condition `FiniteTimeSingularity.IsOdd` asks, for each component `i`, that the field
be odd in coordinate `i` and even in the other two.  Reflection in coordinate `0` (resp. `1`)
leaves `r²` and `x₃` unchanged and only flips the prefactor `x₀` (resp. `x₁`), so those two
conjuncts hold *unconditionally*.  Reflection in the axial coordinate `2` leaves `r²` unchanged
but sends `x₃ ↦ -x₃` inside the profiles, so the whole content of the definition is

* `a` is even in its second argument `x₃` — this is only forced for `r² > 0`, because on the
  axis (`r² = 0`) the first two components vanish identically and impose nothing on `a`;
* `b` is odd in its second argument `x₃` — forced for `r² ≥ 0`, including the axis, since the
  third component is exactly `b r² x₃`.

This is the "even in `r² > 0` / odd in `r² ≥ 0`" asymmetry of the statement.
-/

/-! ## Coordinates of `axiField` and of the vector notation -/







end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.isOdd_iff_reflections =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-!
# `IsOdd` as three reflection identities

`FiniteTimeSingularity.IsOdd u` is stated componentwise: for each coordinate `i`, the `i`-th
component of `u` is odd in coordinate `i` and even in the other two coordinates.  Since a vector
of `ℝ³` is exactly its three coordinates, this is the same as saying that `u` intertwines each
coordinate reflection of the *argument* with the corresponding reflection (sign flip) of the
*value*:

* `refl0`/`flip0` — reflection in the first coordinate,
* `refl1`/`flip1` — reflection in the second coordinate,
* `reflZ`/`flipZ` — reflection in the axial coordinate.

The proof is purely componentwise: writing `x = !₂[x₀, x₁, x₂]` turns each of the reflection
identities into the corresponding parity statement about the slices `t ↦ u !₂[t, x₁, x₂]`, and
conversely.
-/



end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.isOdd_of_reflZ_invariant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `IsOdd` from reflection antisymmetry for axisymmetric no-swirl fields

This module proves `Work.Cyl.isOdd_of_reflZ_invariant`: for an axisymmetric field without swirl
`u = u_r(r,x₃) e_r + u_z(r,x₃) e_z`, the single reflection identity

  `u (reflZ x) = flipZ (u x)`  (i.e. `u(x₀,x₁,-x₃) = (u₀,u₁,-u₂)(x₀,x₁,x₃)`)

already forces the full oddness `FiniteTimeSingularity.IsOdd u`, i.e. that each component `uᵢ` is
odd in the coordinate `i` and even in the two others.

The mechanism is exactly the parity asymmetry of `cylField` (compare
`Work.Cyl.isOdd_cylField`): reflection in the axial coordinate only touches the profiles through
`x₃ ↦ -x₃`, so the third component of the reflection identity reads

  `u_z(r,-x₃) = -u_z(r,x₃)`   (all `r ≥ 0`, including the axis),

while the first component, evaluated at `(r,0,x₃)` with `r > 0`, reads

  `u_r(r,-x₃) = u_r(r,x₃)`   (all `r > 0`).

Reflections in the two *transverse* coordinates `x₀`, `x₁` are free: they leave both `r²` and `x₃`
unchanged and only flip the prefactor `x₀` (resp. `x₁`), which is exactly the parity required of
the first (resp. second) component.

Self-contained: only `Coords`, `Frame`, `Basic` (and Mathlib) are used, so this lemma is available
independently of the `IsOdd`-characterization lemmas proved elsewhere in `Work.Cyl`.
-/

namespace Work.Cyl

/-! ### Coordinate computations for the vectors `!₂[a,b,c]` -/

private lemma cons_zero (a b c : ℝ) : (!₂[a, b, c] : R3) 0 = a := by simp

private lemma radial_cons (a b c : ℝ) : radial (!₂[a, b, c] : R3) = Real.sqrt (a ^ 2 + b ^ 2) := by
  simp [radial, radSq]

private lemma axial_cons (a b c : ℝ) : axial (!₂[a, b, c] : R3) = c := by simp [axial]

private lemma reflZ_cons (a b c : ℝ) : reflZ (!₂[a, b, c] : R3) = !₂[a, b, -c] := by
  refine ext_coord ?_ ?_ ?_ <;> simp [reflZ]

/-- On the ray `r ≥ 0` the radial coordinate of `(r, 0, z)` is `r` itself. -/
private lemma radial_axis {r : ℝ} (hr : 0 ≤ r) (z : ℝ) : radial (!₂[r, 0, z] : R3) = r := by
  rw [radial_cons, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hr]

/-! ### The two nontrivial components of `flipZ` -/

private lemma flipZ_zero (v : R3) : (flipZ v) 0 = v 0 := by simp [flipZ]

private lemma flipZ_two (v : R3) : (flipZ v) 2 = - v 2 := by simp [flipZ]

theorem isOdd_of_reflZ_invariant (u : Work.Cyl.R3 → Work.Cyl.R3) (hax : Work.Cyl.IsAxiNoSwirl u)
    (hrefl : ∀ x, u (Work.Cyl.reflZ x) = Work.Cyl.flipZ (u x)) :
    FiniteTimeSingularity.IsOdd u := by
  obtain ⟨ur, uz, rfl⟩ := hax
  -- The axial reflection identity, read on the ray `(r,0,z)`: `u_z` is odd in `x₃`, `r ≥ 0`.
  have hodd : OddZnn uz := by
    intro r hr z
    have h := congrArg (fun v : R3 => v 2) (hrefl (!₂[r, 0, z] : R3))
    rw [reflZ_cons, cylField_two, flipZ_two] at h
    rw [cylField_two, radial_axis hr (-z), radial_axis hr z, axial_cons, axial_cons] at h
    exact h
  -- Its first component, read on `(r,0,z)` with `r > 0`: `u_r` is even in `x₃`, `r > 0`.
  have heven : ∀ r, 0 < r → ∀ z, ur r (-z) = ur r z := by
    intro r hr z
    have h := congrArg (fun v : R3 => v 0) (hrefl (!₂[r, 0, z] : R3))
    rw [reflZ_cons, cylField_zero, flipZ_zero] at h
    rw [cylField_zero, radial_axis hr.le (-z), radial_axis hr.le z, axial_cons, axial_cons] at h
    rw [cons_zero, cons_zero, mul_div_cancel_right₀ _ hr.ne', mul_div_cancel_right₀ _ hr.ne'] at h
    exact h
  -- Now assemble `IsOdd`: the transverse reflections are parity-free, the axial one uses the two
  -- profile parities just established (note the asymmetry `r > 0` for `u_r`, `r ≥ 0` for `u_z`).
  refine ⟨?_, ?_, ?_⟩
  · -- reflection in the first coordinate
    intro x₁ x₂
    refine ⟨?_, ?_, ?_⟩
    · intro t
      simp only [cylField_zero, radial_cons, axial_cons, Matrix.cons_val_zero, neg_sq]
      ring
    · intro t
      simp only [cylField_one, radial_cons, axial_cons, Matrix.cons_val_one, Matrix.cons_val_zero,
        neg_sq]
    · intro t
      simp only [cylField_two, radial_cons, axial_cons, neg_sq]
  · -- reflection in the second coordinate
    intro x₀ x₂
    refine ⟨?_, ?_, ?_⟩
    · intro t
      simp only [cylField_zero, radial_cons, axial_cons, Matrix.cons_val_zero, neg_sq]
    · intro t
      simp only [cylField_one, radial_cons, axial_cons, Matrix.cons_val_one, Matrix.cons_val_zero,
        neg_sq]
      ring
    · intro t
      simp only [cylField_two, radial_cons, axial_cons, neg_sq]
  · -- reflection in the axial coordinate
    intro x₀ x₁
    refine ⟨?_, ?_, ?_⟩
    · intro t
      simp only [cylField_zero, radial_cons, axial_cons, Matrix.cons_val_zero]
      by_cases hx : x₀ = 0
      · simp [hx]
      · have hρ : 0 < Real.sqrt (x₀ ^ 2 + x₁ ^ 2) :=
          Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_ne_zero hx, sq_nonneg x₁])
        rw [heven _ hρ t]
    · intro t
      simp only [cylField_one, radial_cons, axial_cons, Matrix.cons_val_one, Matrix.cons_val_zero]
      by_cases hx : x₁ = 0
      · simp [hx]
      · have hρ : 0 < Real.sqrt (x₀ ^ 2 + x₁ ^ 2) :=
          Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_ne_zero hx, sq_nonneg x₀])
        rw [heven _ hρ t]
    · intro t
      simp only [cylField_two, radial_cons, axial_cons]
      exact hodd _ (Real.sqrt_nonneg _) t

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.pdR_comp_polar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix

namespace Work.Cyl

/-! ## Derivatives of the polar coordinate functions in the radial variable

`∂_r ρ = r/ρ` and `∂_r θ = -z/ρ²`, and the chain rule for `ρ^α`.  These are the radial
counterparts of `hasDerivAt_rhoP_snd` / `hasDerivAt_thetaP_snd`. -/

private lemma hasDerivAt_rhoP_fst (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => rhoP r' z) (r / rhoP r z) r := by
  have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
    have h : HasDerivAt (fun r' : ℝ => r' ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r)
    simpa using h.const_add (z ^ 2)
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hfun : (fun r' : ℝ => rhoP r' z) = fun r' => Real.sqrt (r' ^ 2 + z ^ 2) := by
    funext r'; rw [rhoP]
  rw [hfun]
  convert h using 1
  rw [rhoP]
  field_simp

private lemma hasDerivAt_thetaP_fst (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => thetaP r' z) (-z / rhoP r z ^ 2) r := by
  have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
    have h := (hasDerivAt_const (x := r) z).div (hasDerivAt_id r) (ne_of_gt hr)
    have hfun : ((fun x : ℝ => z) / id : ℝ → ℝ) = fun r' => z / r' := by
      funext x; simp [Pi.div_apply]
    rw [hfun] at h
    convert h using 1
    simp
  have h := hdiv.arctan
  have hfun : (fun r' : ℝ => thetaP r' z) = fun r' => Real.arctan (z / r') := by
    funext r'; rw [thetaP]
  rw [hfun]
  convert h using 1
  rw [rhoP]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

private lemma hasDerivAt_rhoP_fst_rpow (r z α : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => rhoP r' z ^ α) (α * rhoP r z ^ α * (r / rhoP r z ^ 2)) r := by
  have hne : rhoP r z ≠ 0 := rhoP_ne_zero hr z
  have hρ : HasDerivAt (fun r' : ℝ => rhoP r' z) (r / rhoP r z) r :=
    hasDerivAt_rhoP_fst r z hr
  have h := (Real.hasDerivAt_rpow_const (x := rhoP r z) (p := α) (Or.inl hne)).comp r hρ
  have hfun : ((fun x : ℝ => x ^ α) ∘ fun r' => rhoP r' z) = fun r' => rhoP r' z ^ α := by
    funext x; rfl
  rw [hfun] at h
  convert h using 1
  rw [Real.rpow_sub_one hne]
  field_simp


end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.pdR_comp_polar_rho =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

theorem pdR_comp_polar_rho (G : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdR (fun r' z' => G (Work.Cyl.rhoP r' z') (Work.Cyl.thetaP r' z')) r z =
      Real.cos (Work.Cyl.thetaP r z) * Work.Cyl.pdR G (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)
        - Real.sin (Work.Cyl.thetaP r z) / Work.Cyl.rhoP r z *
          Work.Cyl.pdZ G (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) := by
  -- The radial partial derivative of the polar pair `r' ↦ (ρ(r', z), θ(r', z))`,
  -- combined with the chain rule for a two-variable function, gives the claim.
  -- Step 1: `∂_r ρ(r', z) = r / ρ(r, z)`.
  have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
    have h := (hasDerivAt_pow 2 r).add_const (z ^ 2)
    simpa using h
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have hR : HasDerivAt (fun r' : ℝ => rhoP r' z) (r / rhoP r z) r := by
    have h := hsq.sqrt hne
    have hval : (2 * r) / (2 * Real.sqrt (r ^ 2 + z ^ 2)) = r / rhoP r z := by
      rw [rhoP]; field_simp
    rw [hval] at h
    exact h
  -- Step 2: `∂_r θ(r', z) = -z / (r² + z²) = -sin θ / ρ`.
  have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
    have hinv : HasDerivAt (fun r' : ℝ => (r')⁻¹) (-(r ^ 2)⁻¹) r :=
      hasDerivAt_inv (ne_of_gt hr)
    have h := hinv.const_mul z
    have hval : z * (-(r ^ 2)⁻¹) = -z / r ^ 2 := by rw [div_eq_mul_inv]; ring
    rw [hval] at h
    exact h
  have hT : HasDerivAt (fun r' : ℝ => thetaP r' z) (-z / (r ^ 2 + z ^ 2)) r := by
    have h := (Real.hasDerivAt_arctan (z / r)).comp r hdiv
    have hval : 1 / (1 + (z / r) ^ 2) * (-z / r ^ 2) = -z / (r ^ 2 + z ^ 2) := by
      field_simp
    rw [hval] at h
    exact h
  -- Step 3: rewrite `-z/(r²+z²)` as `-sin θ / ρ` and `r/ρ` as `cos θ`.
  have hid : -z / (r ^ 2 + z ^ 2) = -(Real.sin (thetaP r z) / rhoP r z) := by
    rw [sin_thetaP hr z]
    have hρ : rhoP r z ≠ 0 := rhoP_ne_zero hr z
    field_simp
    rw [rhoP_sq]
  -- Step 4: chain rule along the radial slice.
  have hcomp := hasDerivAt_comp_two G (fun r' : ℝ => rhoP r' z)
    (fun r' : ℝ => thetaP r' z) (r / rhoP r z) (-z / (r ^ 2 + z ^ 2)) r hG hR hT
  rw [pdR]
  change deriv (fun t : ℝ => G (rhoP t z) (thetaP t z)) r = _
  rw [hcomp.deriv, hid, cos_thetaP hr z]
  ring

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.pdZ_comp_polar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The axial chain rule for `(r,z) ↦ F(ρ(r,z)^α, θ(r,z))`

If `F` is differentiable at `(ρ(r,z)^α, θ(r,z))` and `r > 0`, then the axial partial derivative of
`(r,z) ↦ F(ρ(r,z)^α, θ(r,z))` is

`∂_z = (sin θ / ρ) · (α ρ^α ∂_ρ F) + (cos θ / ρ) · ∂_θ F`.

Indeed `∂_z (ρ^α) = α ρ^{α-1} ∂_z ρ = α ρ^{α-1} · z/ρ = (α ρ^α) · sin θ / ρ`, using
`∂_z ρ = z/ρ = sin θ`, and `∂_z θ = r/ρ² = (cos θ)/ρ`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-- `z ↦ ρ(r,z) = √(r²+z²)` has derivative `z/ρ = sin θ` in the axial variable. -/
lemma hasDerivAt_rhoP_polar (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun z' : ℝ => rhoP r z') (z / rhoP r z) z := by
  have hsq : HasDerivAt (fun z' : ℝ => r ^ 2 + z' ^ 2) (2 * z) z := by
    have h : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z)
    simpa using h.const_add (r ^ 2)
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hval : (2 * z) / (2 * Real.sqrt (r ^ 2 + z ^ 2)) = z / rhoP r z := by
    have hs : Real.sqrt (r ^ 2 + z ^ 2) ≠ 0 := by positivity
    rw [rhoP]; field_simp
  rw [hval] at h
  exact h

/-- `z ↦ θ(r,z) = arctan(z/r)` has derivative `r/ρ² = cos θ / ρ` in the axial variable. -/
lemma hasDerivAt_thetaP_polar (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun z' : ℝ => thetaP r z') (r / (r ^ 2 + z ^ 2)) z := by
  have hlin : HasDerivAt (fun z' : ℝ => z' / r) (1 / r) z := by
    simpa using (hasDerivAt_id z).div_const r
  have h := (Real.hasDerivAt_arctan (z / r)).comp z hlin
  have hval : 1 / (1 + (z / r) ^ 2) * (1 / r) = r / (r ^ 2 + z ^ 2) := by
    field_simp
  rw [hval] at h
  exact h

/-- `z ↦ ρ(r,z)^α` has derivative `α ρ^{α-1} · z/ρ`. -/
lemma hasDerivAt_rhoP_rpow_polar (r α z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun z' : ℝ => rhoP r z' ^ α) (α * rhoP r z ^ (α - 1) * (z / rhoP r z)) z := by
  have hbase := hasDerivAt_rhoP_polar r z hr
  have h := hbase.rpow_const (p := α) (Or.inl (ne_of_gt (rhoP_pos hr z)))
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

theorem pdZ_comp_polar (F : ℝ → ℝ → ℝ) (α r z : ℝ) (hr : 0 < r)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdZ (fun r' z' => F (Work.Cyl.rhoP r' z' ^ α) (Work.Cyl.thetaP r' z')) r z =
      Real.sin (Work.Cyl.thetaP r z) / Work.Cyl.rhoP r z *
          (α * Work.Cyl.rhoP r z ^ α * Work.Cyl.pdR F (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z))
        + Real.cos (Work.Cyl.thetaP r z) / Work.Cyl.rhoP r z *
          Work.Cyl.pdZ F (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
  have hR := hasDerivAt_rhoP_rpow_polar r α z hr
  have hZ := hasDerivAt_thetaP_polar r z hr
  have h := hasDerivAt_comp_two F (fun t : ℝ => rhoP r t ^ α) (fun t : ℝ => thetaP r t)
      (α * rhoP r z ^ (α - 1) * (z / rhoP r z)) (r / (r ^ 2 + z ^ 2)) z hF hR hZ
  have hpd : pdZ (fun r' z' => F (rhoP r' z' ^ α) (thetaP r' z')) r z =
      deriv (fun t : ℝ => F (rhoP r t ^ α) (thetaP r t)) z := rfl
  rw [hpd, h.deriv]
  rw [sin_thetaP hr z, cos_thetaP hr z]
  have hpow : rhoP r z ^ α = rhoP r z ^ (α - 1) * rhoP r z := by
    conv_lhs => rw [show α = (α - 1) + 1 by ring]
    rw [Real.rpow_add (rhoP_pos hr z), Real.rpow_one]
  rw [hpow, ← rhoP_sq r z]
  field_simp

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.pdZ_comp_polar_rho =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The axial chain rule for the polar change of variables `(r,z) ↦ (ρ,θ)`

If `G` is differentiable at `(ρ(r,z), θ(r,z))`, then the axial partial derivative of
`(r,z) ↦ G(ρ(r,z), θ(r,z))` is

`∂_z (G ∘ (ρ,θ)) = sin θ · ∂_ρ G + (cos θ / ρ) · ∂_θ G`.

Indeed `∂_z ρ = z/ρ = sin θ` and `∂_z θ = r/ρ² = cos θ / ρ`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-- `z ↦ ρ(r,z) = √(r²+z²)` has derivative `z/ρ = sin θ` in the axial variable. -/
lemma hasDerivAt_rhoP_snd (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun z' : ℝ => rhoP r z') (z / rhoP r z) z := by
  have hsq : HasDerivAt (fun z' : ℝ => r ^ 2 + z' ^ 2) (2 * z) z := by
    have h : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z)
    simpa using h.const_add (r ^ 2)
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hfun : (fun z' : ℝ => rhoP r z') = fun z' => Real.sqrt (r ^ 2 + z' ^ 2) := by
    funext z'; rw [rhoP]
  rw [hfun]
  convert h using 1
  rw [rhoP]
  field_simp

/-- `z ↦ θ(r,z) = arctan(z/r)` has derivative `r/ρ² = cos θ / ρ` in the axial variable. -/
lemma hasDerivAt_thetaP_snd (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun z' : ℝ => thetaP r z') (r / rhoP r z ^ 2) z := by
  have hdiv : HasDerivAt (fun z' : ℝ => z' / r) (1 / r) z := by
    have h : HasDerivAt (fun z' : ℝ => z') 1 z := hasDerivAt_id z
    simpa using h.div_const r
  have h := hdiv.arctan
  have hfun : (fun z' : ℝ => thetaP r z') = fun z' => Real.arctan (z' / r) := by
    funext z'; rw [thetaP]
  rw [hfun]
  convert h using 1
  rw [rhoP]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

theorem pdZ_comp_polar_rho (G : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdZ (fun r' z' => G (Work.Cyl.rhoP r' z') (Work.Cyl.thetaP r' z')) r z =
      Real.sin (Work.Cyl.thetaP r z) * Work.Cyl.pdR G (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z)
        + Real.cos (Work.Cyl.thetaP r z) / Work.Cyl.rhoP r z *
          Work.Cyl.pdZ G (Work.Cyl.rhoP r z) (Work.Cyl.thetaP r z) := by
  have hρ : rhoP r z ≠ 0 := rhoP_ne_zero hr z
  have h := hasDerivAt_comp_two G (fun z' => rhoP r z') (fun z' => thetaP r z')
      (z / rhoP r z) (r / rhoP r z ^ 2) z hG
      (hasDerivAt_rhoP_snd r z hr) (hasDerivAt_thetaP_snd r z hr)
  rw [pdZ, h.deriv, sin_thetaP hr z, cos_thetaP hr z]
  field_simp

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.vortTheta_psiField =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- The vorticity component `ω^θ` of the stream-function field `psiField ψ` is `-Lψ`, where `L` is
the axisymmetric elliptic operator `cylOp` of (3dBSL). -/
theorem vortTheta_psiField (ψ : ℝ → ℝ → ℝ) (r z : ℝ)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) (hr : r ≠ 0) :
    Work.Cyl.vortTheta (Work.Cyl.pdZ ψ) (fun r z => -(ψ r z / r) - Work.Cyl.pdR ψ r z) r z =
      -Work.Cyl.cylOp ψ r z := by
  -- `ψ(·, z)` is `C²` at `r`, hence so is its first derivative `pdR ψ · z`.
  have hslice : ContDiffAt ℝ 2 (fun r' : ℝ => ψ r' z) r := by
    have hg : ContDiffAt ℝ 2 (fun r' : ℝ => (r', z)) r := by fun_prop
    have h := hψ.comp r hg
    simpa [Function.comp_def] using h
  have hdψ : DifferentiableAt ℝ (fun r' : ℝ => ψ r' z) r := hslice.differentiableAt (by norm_num)
  have hdq : DifferentiableAt ℝ (fun r' : ℝ => ψ r' z / r') r := hdψ.div differentiableAt_id hr
  have hdiv : deriv (fun r' : ℝ => ψ r' z / r') r
      = (deriv (fun r' : ℝ => ψ r' z) r * r - ψ r z) / r ^ 2 := by
    rw [show (fun r' : ℝ => ψ r' z / r') = ((fun r' : ℝ => ψ r' z) / (id : ℝ → ℝ))
        from by funext r'; rfl]
    rw [deriv_div hdψ differentiableAt_id hr]
    simp
  have hdB : DifferentiableAt ℝ (fun r' : ℝ => deriv (fun r' : ℝ => ψ r' z) r') r := by
    have h1 : ContDiffAt ℝ 1 (deriv (fun r' : ℝ => ψ r' z)) r :=
      hslice.derivWithin (m := 1) (by norm_num)
    exact h1.differentiableAt (by norm_num)
  have hB : deriv (fun r' : ℝ => -(ψ r' z / r') - deriv (fun r' : ℝ => ψ r' z) r') r
      = -((deriv (fun r' : ℝ => ψ r' z) r * r - ψ r z) / r ^ 2)
        - deriv (fun r' : ℝ => deriv (fun r' : ℝ => ψ r' z) r') r := by
    rw [show (fun r' : ℝ => -(ψ r' z / r') - deriv (fun r' : ℝ => ψ r' z) r')
        = ((- fun r' : ℝ => ψ r' z / r') - fun r' : ℝ => deriv (fun r' : ℝ => ψ r' z) r')
        from by funext r'; rfl]
    rw [deriv_sub hdq.neg hdB]
    rw [deriv.neg]
    rw [hdiv]
  simp only [Work.Cyl.vortTheta, Work.Cyl.cylOp, Work.Cyl.pdZ, Work.Cyl.pdR, Work.Cyl.pdRR,
    Work.Cyl.pdZZ]
  rw [hB]
  field_simp
  ring

end Work.Cyl
end
-- ===== merged: Submission.Work.Elliptic.DivSinFactor =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open Work.Spaces

/-- `D_z` commutes with division by a function of `θ` alone: the factor `1/s(θ)` is a
constant as far as the `z`-derivative is concerned. -/
lemma Dz_div_const (F : ℝ → ℝ → ℝ) (s : ℝ → ℝ) (z θ : ℝ) :
    Dz (fun z θ => F z θ / s θ) z θ = Dz F z θ / s θ := by
  simp only [Dz, pz]
  rw [deriv_div_const]
  ring

theorem DivSinFactor (Φ : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter j (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
      = Work.Spaces.DzIter j Φ z θ / Real.sin (2 * θ) := by
  have hfun : Work.Spaces.DzIter j (fun z θ => Φ z θ / Real.sin (2 * θ))
      = fun z θ => Work.Spaces.DzIter j Φ z θ / Real.sin (2 * θ) := by
    induction j with
    | zero => rfl
    | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      exact Dz_div_const (Work.Spaces.DzIter n Φ) (fun θ => Real.sin (2 * θ)) z θ
  exact congrFun (congrFun hfun z) θ

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.Gsing_ode =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Derivative facts for the pieces of `Gsing` -/

/-- `Abar` has derivative `DAbar`. -/
private lemma hasDerivAt_Abar (α : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Abar α) (DAbar α z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hp : HasDerivAt (fun y : ℝ => y ^ (-(5 / α))) ((-(5 / α)) * z ^ (-(5 / α) - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hzne)
  have h := hp.const_mul (-(3 / (4 * α)))
  convert h using 1
  · ext y; rfl
  · show (-(3 / (4 * α)) * (-(5 / α))) * z ^ (-(5 / α) - 1)
        = -(3 / (4 * α)) * (-(5 / α) * z ^ (-(5 / α) - 1))
    ring

/-- `DAbar` has derivative `DDAbar`. -/
private lemma hasDerivAt_DAbar (α : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (DAbar α) (DDAbar α z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hp : HasDerivAt (fun y : ℝ => y ^ (-(5 / α) - 1))
      ((-(5 / α) - 1) * z ^ (-(5 / α) - 1 - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hzne)
  have h := hp.const_mul ((-(3 / (4 * α))) * (-(5 / α)))
  have hfun : (fun y : ℝ => ((-(3 / (4 * α))) * (-(5 / α))) * y ^ (-(5 / α) - 1))
      = DAbar α := rfl
  rw [hfun] at h
  simpa only [DDAbar] using h

/-- `Gstar` has derivative `DGstar`. -/
private lemma hasDerivAt_Gstar (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ}
    (hL12 : HasDerivAt (L12 F) (-(3 * Fstar F z / z)) z) :
    HasDerivAt (Gstar α F) (DGstar α F z) z := by
  have h := hL12.const_mul (-(1 / (4 * α)))
  have hfun : (fun y : ℝ => -(1 / (4 * α)) * L12 F y) = Gstar α F := rfl
  rw [hfun] at h
  simpa only [DGstar] using h

/-- `Gbar` has derivative `DGbar`. -/
private lemma hasDerivAt_Gbar (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hJ : HasDerivAt (Jfun α F) (z ^ ((5 - α) / α) * Fstar F z) z) :
    HasDerivAt (Gbar α F) (DGbar α F z) z := by
  have hA : HasDerivAt (Abar α) (DAbar α z) z := hasDerivAt_Abar α hz
  have h := hA.mul hJ
  have hfun : (Abar α * Jfun α F) = Gbar α F := rfl
  rw [hfun] at h
  simpa only [DGbar] using h

/-- `DGstar` has derivative `DDGstar`. -/
private lemma hasDerivAt_DGstar (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hFc : HasDerivAt (Fstar F) (deriv (Fstar F) z) z) :
    HasDerivAt (DGstar α F) (DDGstar α F z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hnum : HasDerivAt (fun y : ℝ => 3 * Fstar F y) (3 * deriv (Fstar F) z) z :=
    hFc.const_mul 3
  have hden : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have hquot : HasDerivAt (fun y : ℝ => 3 * Fstar F y / y)
      (((3 * deriv (Fstar F) z) * z - (3 * Fstar F z) * 1) / z ^ 2) z :=
    hnum.div hden hzne
  have hneg : HasDerivAt (fun y : ℝ => -(3 * Fstar F y / y))
      (-(((3 * deriv (Fstar F) z) * z - (3 * Fstar F z) * 1) / z ^ 2)) z := hquot.neg
  have h := hneg.const_mul (-(1 / (4 * α)))
  have hfun : (fun y : ℝ => -(1 / (4 * α)) * (-(3 * Fstar F y / y))) = DGstar α F := rfl
  rw [hfun] at h
  simpa only [DDGstar, mul_one] using h

/-- The function `y ↦ y^{(5-α)/α} F_*(y)` has derivative
`((5-α)/α) z^{(5-α)/α-1} F_*(z) + z^{(5-α)/α} F_*'(z)`. -/
private lemma hasDerivAt_rpow_mul_Fstar (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hFc : HasDerivAt (Fstar F) (deriv (Fstar F) z) z) :
    HasDerivAt (fun y : ℝ => y ^ ((5 - α) / α) * Fstar F y)
      (((5 - α) / α) * z ^ ((5 - α) / α - 1) * Fstar F z
        + z ^ ((5 - α) / α) * deriv (Fstar F) z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hp : HasDerivAt (fun y : ℝ => y ^ ((5 - α) / α))
      (((5 - α) / α) * z ^ ((5 - α) / α - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hzne)
  have h := hp.mul hFc
  have hfun : ((fun y : ℝ => y ^ ((5 - α) / α)) * Fstar F)
      = (fun y : ℝ => y ^ ((5 - α) / α) * Fstar F y) := rfl
  rw [hfun] at h
  exact h

/-- `DGbar` has derivative `DDGbar`. -/
private lemma hasDerivAt_DGbar (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hFc : HasDerivAt (Fstar F) (deriv (Fstar F) z) z)
    (hJ : HasDerivAt (Jfun α F) (z ^ ((5 - α) / α) * Fstar F z) z) :
    HasDerivAt (DGbar α F) (DDGbar α F z) z := by
  have hA : HasDerivAt (Abar α) (DAbar α z) z := hasDerivAt_Abar α hz
  have hA' : HasDerivAt (DAbar α) (DDAbar α z) z := hasDerivAt_DAbar α hz
  have hFq := hasDerivAt_rpow_mul_Fstar α F hz hFc
  have h1 : HasDerivAt (fun y : ℝ => DAbar α y * Jfun α F y)
      (DDAbar α z * Jfun α F z + DAbar α z * (z ^ ((5 - α) / α) * Fstar F z)) z :=
    hA'.mul hJ
  have h2 : HasDerivAt (fun y : ℝ => Abar α y * (y ^ ((5 - α) / α) * Fstar F y))
      (DAbar α z * (z ^ ((5 - α) / α) * Fstar F z)
        + Abar α z * (((5 - α) / α) * z ^ ((5 - α) / α - 1) * Fstar F z
            + z ^ ((5 - α) / α) * deriv (Fstar F) z)) z :=
    hA.mul hFq
  have h := h1.add h2
  have hfun : ((fun y : ℝ => DAbar α y * Jfun α F y)
      + (fun y : ℝ => Abar α y * (y ^ ((5 - α) / α) * Fstar F y))) = DGbar α F := rfl
  rw [hfun] at h
  have hval : DDAbar α z * Jfun α F z + DAbar α z * (z ^ ((5 - α) / α) * Fstar F z)
      + (DAbar α z * (z ^ ((5 - α) / α) * Fstar F z)
        + Abar α z * (((5 - α) / α) * z ^ ((5 - α) / α - 1) * Fstar F z
            + z ^ ((5 - α) / α) * deriv (Fstar F) z)) = DDGbar α F z := by
    rw [DDGbar]; ring
  rw [hval] at h
  exact h

theorem Gsing_ode (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => Work.Elliptic.L12 F z') (-(3 * Work.Elliptic.Fstar F z / z)) z)
    (hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z)
    (hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
        = (15 / 4) * Work.Elliptic.Fstar F z := by
  intro z hz
  have hzpos : 0 < z := hz
  have hFcz : HasDerivAt (Fstar F) (deriv (Fstar F) z) z := hFc z hz
  have hJz : HasDerivAt (Jfun α F) (z ^ ((5 - α) / α) * Fstar F z) z := by
    have h := hJ z hz
    have hfun : (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Fstar F s) = Jfun α F := rfl
    rw [hfun] at h
    exact h
  -- `Gsing` has derivative `DGstar + DGbar`
  have hGsing : HasDerivAt (Gsing α F) (DGstar α F z + DGbar α F z) z := by
    have h1 : HasDerivAt (Gstar α F) (DGstar α F z) z := hasDerivAt_Gstar α F (hL12 z hz)
    have h2 : HasDerivAt (Gbar α F) (DGbar α F z) z := hasDerivAt_Gbar α F hzpos hJz
    have h := h1.add h2
    have hfun : ((Gstar α F) + (Gbar α F)) = Gsing α F := rfl
    rw [hfun] at h
    exact h
  -- `deriv (Gsing α F)` agrees with `DGstar + DGbar` near `z`
  have hderiv_eq : deriv (Gsing α F) =ᶠ[𝓝 z] (DGstar α F + DGbar α F) := by
    have hmem : ∀ᶠ w in 𝓝 z, w ∈ Set.Ioi (0 : ℝ) :=
      Filter.eventually_mem_set.mpr (isOpen_Ioi.mem_nhds hz)
    refine hmem.mono ?_
    intro w hw
    have h1 : HasDerivAt (Gstar α F) (DGstar α F w) w := hasDerivAt_Gstar α F (hL12 w hw)
    have h2 : HasDerivAt (Gbar α F) (DGbar α F w) w :=
      hasDerivAt_Gbar α F hw (by
        have h := hJ w hw
        have hfun : (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Fstar F s) = Jfun α F := rfl
        rw [hfun] at h
        exact h)
    have h3 : HasDerivAt (Gsing α F) (DGstar α F w + DGbar α F w) w := by
      have h := h1.add h2
      have hfun : ((Gstar α F) + (Gbar α F)) = Gsing α F := rfl
      rw [hfun] at h
      exact h
    exact h3.deriv
  -- second derivative
  have hDG : HasDerivAt (DGstar α F + DGbar α F) (DDGstar α F z + DDGbar α F z) z := by
    have h1 : HasDerivAt (DGstar α F) (DDGstar α F z) z := hasDerivAt_DGstar α F hzpos hFcz
    have h2 : HasDerivAt (DGbar α F) (DDGbar α F z) z := hasDerivAt_DGbar α F hzpos hFcz hJz
    exact h1.add h2
  have hderiv2 : HasDerivAt (deriv (Gsing α F)) (DDGstar α F z + DDGbar α F z) z :=
    hDG.congr_of_eventuallyEq hderiv_eq
  have e1 : deriv (fun z' => deriv (Gsing α F) z') z = DDGstar α F z + DDGbar α F z :=
    hderiv2.deriv
  have e2 : deriv (Gsing α F) z = DGstar α F z + DGbar α F z := hGsing.deriv
  rw [e1, e2]
  exact Gsing_algebra α F z hα hzpos

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.PsiStar_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval ContDiff
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false




end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.bslOp_sing_source =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic


end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.continuousWithinAt_htPP_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic


end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.first_derivs_mul_pow_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open Work.Cyl

theorem first_derivs_mul_pow_rpow (Ψ : ℝ → ℝ → ℝ) (α ρ θ : ℝ) (hρ : 0 < ρ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (ρ ^ α, θ)) :
    Work.Cyl.pdR (fun p q => p ^ 2 * Ψ (p ^ α) q) ρ θ
        = 2 * ρ * Ψ (ρ ^ α) θ + α * ρ ^ (α + 1) * Work.Cyl.pdR Ψ (ρ ^ α) θ
      ∧ Work.Cyl.pdZ (fun p q => p ^ 2 * Ψ (p ^ α) q) ρ θ = ρ ^ 2 * Work.Cyl.pdZ Ψ (ρ ^ α) θ
      ∧ Work.Cyl.pdZZ (fun p q => p ^ 2 * Ψ (p ^ α) q) ρ θ = ρ ^ 2 * Work.Cyl.pdZZ Ψ (ρ ^ α) θ := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  refine ⟨?_, ?_, ?_⟩
  · -- radial derivative
    have hΨd : Work.Cyl.DiffAt2 Ψ (ρ ^ α) θ := hΨ.differentiableAt (by decide)
    have hslice : DifferentiableAt ℝ (fun u : ℝ => Ψ u θ) (ρ ^ α) :=
      differentiableAt_slice_fst Ψ (ρ ^ α) θ hΨd
    have hslice' : HasDerivAt (fun u : ℝ => Ψ u θ) (Work.Cyl.pdR Ψ (ρ ^ α) θ) (ρ ^ α) :=
      hslice.hasDerivAt
    have hpow : HasDerivAt (fun p : ℝ => p ^ α) (α * ρ ^ (α - 1)) ρ :=
      Real.hasDerivAt_rpow_const (Or.inl hρne)
    have hcomp₀ : HasDerivAt ((fun u : ℝ => Ψ u θ) ∘ (fun p : ℝ => p ^ α))
        (Work.Cyl.pdR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1))) ρ :=
      hslice'.comp ρ hpow
    have hcomp : HasDerivAt (fun p : ℝ => Ψ (p ^ α) θ)
        (Work.Cyl.pdR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1))) ρ := hcomp₀
    have h2 : HasDerivAt (fun p : ℝ => p ^ 2) (2 * ρ) ρ := by
      simpa using (hasDerivAt_pow 2 ρ)
    have hprod : HasDerivAt (fun r' : ℝ => r' ^ 2 * Ψ (r' ^ α) θ)
        (2 * ρ * Ψ (ρ ^ α) θ + ρ ^ 2 * (Work.Cyl.pdR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1)))) ρ :=
      h2.mul hcomp
    rw [Work.Cyl.pdR, hprod.deriv]
    have hpow2 : ρ ^ (2:ℝ) = ρ ^ 2 := Real.rpow_natCast ρ 2
    have hkey : ρ ^ (2:ℝ) * ρ ^ (α - 1) = ρ ^ (α + 1) := by
      rw [← Real.rpow_add hρ]
      congr 1
      ring
    rw [← hpow2, ← hkey]
    ring
  · -- axial derivative
    rw [Work.Cyl.pdZ, Work.Cyl.pdZ, deriv_const_mul_field]
  · -- second axial derivative
    have hfun : (fun z' => Work.Cyl.pdZ (fun p q => p ^ 2 * Ψ (p ^ α) q) ρ z')
        = fun z' => ρ ^ 2 * Work.Cyl.pdZ Ψ (ρ ^ α) z' := by
      funext z'
      rw [Work.Cyl.pdZ, Work.Cyl.pdZ, deriv_const_mul_field]
    rw [Work.Cyl.pdZZ, Work.Cyl.pdZZ, hfun, deriv_const_mul_field]

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.hardy_two_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedSimpArgs false








end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.htUEndpointBoundsZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic


end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.htU_interior_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- On the open interval `(0, π/2)` the denominator `sin (2θ)` of `htU f` does not vanish. -/
private lemma sin_two_ne_zero {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) : Real.sin (2 * x) ≠ 0 := by
  have h1 : 0 < 2 * x := by linarith [hx.1]
  have h2 : 2 * x < π := by linarith [hx.2]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)

/-- `htU f x * sin (2x) = f x` on `(0, π/2)`. -/
private lemma htU_mul_sin (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    (htU f) x * Real.sin (2 * x) = f x := by
  simp only [htU]
  exact div_mul_cancel₀ _ (sin_two_ne_zero hx)

/-- `f` is `C²` at every interior point of `[0, π/2]`. -/
private lemma contDiffAt_Ioo (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) : ContDiffAt ℝ 2 f x :=
  hf.contDiffAt (mem_of_superset (isOpen_Ioo.mem_nhds hx) Ioo_subset_Icc_self)

/-- `HasDerivAt` for `sin (2·)`. -/
private lemma hasDerivAt_sin_two_prv (x : ℝ) :
    HasDerivAt (fun z : ℝ => Real.sin (2 * z)) (2 * Real.cos (2 * x)) x := by
  have h1 : HasDerivAt (fun z : ℝ => 2 * z) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun z : ℝ => Real.sin (2 * z)) (Real.cos (2 * x) * 2) x := h1.sin
  rw [show Real.cos (2 * x) * 2 = 2 * Real.cos (2 * x) by ring] at h2
  exact h2

/-- `HasDerivAt` for `cos (2·)`. -/
private lemma hasDerivAt_cos_two_prv (x : ℝ) :
    HasDerivAt (fun z : ℝ => Real.cos (2 * z)) (-2 * Real.sin (2 * x)) x := by
  have h1 : HasDerivAt (fun z : ℝ => 2 * z) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun z : ℝ => Real.cos (2 * z)) (-Real.sin (2 * x) * 2) x := h1.cos
  rw [show -Real.sin (2 * x) * 2 = -2 * Real.sin (2 * x) by ring] at h2
  exact h2

/-- First-derivative identity: `u' sin(2x) + 2 u cos(2x) = f'` on `(0, π/2)`, obtained by
differentiating `u · sin(2·) = f`. -/
private lemma htU_deriv_one (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    deriv (htU f) x * Real.sin (2 * x) + 2 * (htU f) x * Real.cos (2 * x) = deriv f x := by
  have hUS : Set.EqOn ((htU f) * fun z : ℝ => Real.sin (2 * z)) f (Set.Ioo 0 (π / 2)) := by
    intro z hz
    simp only [Pi.mul_apply, htU]
    exact div_mul_cancel₀ _ (sin_two_ne_zero hz)
  have hEv : ((htU f) * fun z : ℝ => Real.sin (2 * z)) =ᶠ[𝓝 x] f :=
    Set.EqOn.eventuallyEq_of_mem hUS (isOpen_Ioo.mem_nhds hx)
  have hu : HasDerivAt (htU f) (deriv (htU f) x) x :=
    ((htU_contDiffAt f hf x hx).differentiableAt (by norm_num)).hasDerivAt
  have hS : HasDerivAt (fun z : ℝ => Real.sin (2 * z)) (2 * Real.cos (2 * x)) x :=
    hasDerivAt_sin_two_prv x
  have key : deriv ((htU f) * fun z : ℝ => Real.sin (2 * z)) x = deriv f x := hEv.deriv_eq
  rw [(hu.mul hS).deriv] at key
  convert key using 1
  ring

/-- Second-derivative identity: `u'' sin(2x) + 4 u' cos(2x) - 4 u sin(2x) = f''` on `(0, π/2)`,
obtained by differentiating the first-derivative identity. -/
private lemma htU_deriv_two (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    deriv (deriv (htU f)) x * Real.sin (2 * x) + 4 * Real.cos (2 * x) * deriv (htU f) x
      - 4 * Real.sin (2 * x) * (htU f) x = deriv (deriv f) x := by
  have hzero : (fun z : ℝ => deriv (htU f) z * Real.sin (2 * z) + 2 * (htU f) z * Real.cos (2 * z)
      - deriv f z) =ᶠ[𝓝 x] (0 : ℝ → ℝ) := by
    apply Set.EqOn.eventuallyEq_of_mem _ (isOpen_Ioo.mem_nhds hx)
    intro z hz
    have h := htU_deriv_one f hf hz
    simp only [Pi.zero_apply]
    linarith [h]
  have hzerod : deriv (fun z : ℝ => deriv (htU f) z * Real.sin (2 * z)
      + 2 * (htU f) z * Real.cos (2 * z) - deriv f z) x = 0 := by
    have h := hzero.deriv_eq
    simpa using h
  have hu : HasDerivAt (htU f) (deriv (htU f) x) x :=
    ((htU_contDiffAt f hf x hx).differentiableAt (by norm_num)).hasDerivAt
  have hdu : HasDerivAt (deriv (htU f)) (deriv (deriv (htU f)) x) x :=
    (((htU_contDiffAt f hf x hx).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hdf : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    (((contDiffAt_Ioo f hf hx).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hS : HasDerivAt (fun z : ℝ => Real.sin (2 * z)) (2 * Real.cos (2 * x)) x :=
    hasDerivAt_sin_two_prv x
  have hC : HasDerivAt (fun z : ℝ => Real.cos (2 * z)) (-2 * Real.sin (2 * x)) x :=
    hasDerivAt_cos_two_prv x
  have hA : HasDerivAt (fun z : ℝ => deriv (htU f) z * Real.sin (2 * z))
      (deriv (deriv (htU f)) x * Real.sin (2 * x)
        + deriv (htU f) x * (2 * Real.cos (2 * x))) x :=
    hdu.mul hS
  have hB : HasDerivAt (fun z : ℝ => 2 * (htU f) z * Real.cos (2 * z))
      ((2 * deriv (htU f) x) * Real.cos (2 * x)
        + (2 * (htU f) x) * (-2 * Real.sin (2 * x))) x :=
    (hu.const_mul 2).mul hC
  have hF : HasDerivAt (fun z : ℝ => deriv (htU f) z * Real.sin (2 * z)
      + 2 * (htU f) z * Real.cos (2 * z) - deriv f z)
      ((deriv (deriv (htU f)) x * Real.sin (2 * x)
          + deriv (htU f) x * (2 * Real.cos (2 * x)))
        + ((2 * deriv (htU f) x) * Real.cos (2 * x)
          + (2 * (htU f) x) * (-2 * Real.sin (2 * x)))
        - deriv (deriv f) x) x :=
    (hA.add hB).sub hdf
  rw [hF.deriv] at hzerod
  nlinarith [hzerod]

theorem htU_interior_facts (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) :
    ContDiffOn ℝ 2 (Work.Elliptic.htU f) (Set.Ioo 0 (π / 2)) ∧
    (∀ x ∈ Set.Ioo 0 (π / 2), deriv f x = iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) x) ∧
    (∀ x ∈ Set.Ioo 0 (π / 2),
        deriv (deriv f) x = iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) x) ∧
    (∀ x ∈ Set.Ioo 0 (π / 2),
        (Real.sin (2 * x)) ^ 2 * deriv (Work.Elliptic.htU f) x
          = deriv f x * Real.sin (2 * x) - 2 * Real.cos (2 * x) * f x) ∧
    (∀ x ∈ Set.Ioo 0 (π / 2),
        Real.sin (2 * x) * deriv (deriv (Work.Elliptic.htU f)) x
          = deriv (deriv f) x + 4 * f x - 4 * Real.cos (2 * x) * deriv (Work.Elliptic.htU f) x) ∧
    ContinuousOn (Work.Elliptic.htU f) (Set.Ioo 0 (π / 2)) ∧
    ContinuousOn (fun x => deriv (Work.Elliptic.htU f) x) (Set.Ioo 0 (π / 2)) ∧
    ContinuousOn (fun x => deriv (deriv (Work.Elliptic.htU f)) x) (Set.Ioo 0 (π / 2)) ∧
    ContinuousOn (fun x => deriv (deriv f) x) (Set.Ioo 0 (π / 2)) := by
  have hpi : (0 : ℝ) < π / 2 := by linarith [Real.pi_pos]
  have hCU : ContDiffOn ℝ 2 (htU f) (Set.Ioo 0 (π / 2)) :=
    fun x hx => (htU_contDiffAt f hf x hx).contDiffWithinAt
  refine ⟨hCU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 1) (uniqueDiffOn_Icc hpi)
        ((contDiffAt_Ioo f hf hx).of_le (by norm_num)) (Ioo_subset_Icc_self hx),
      iteratedDeriv_one]
  · intro x hx
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 2) (uniqueDiffOn_Icc hpi)
        ((contDiffAt_Ioo f hf hx).of_le (by norm_num)) (Ioo_subset_Icc_self hx),
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  · intro x hx
    have h1 := htU_deriv_one f hf hx
    have h2 := htU_mul_sin f hx
    linear_combination h1 * Real.sin (2 * x) - (2 * Real.cos (2 * x)) * h2
  · intro x hx
    have h1 := htU_deriv_two f hf hx
    have h2 := htU_mul_sin f hx
    nlinarith [h1, h2]
  · exact hCU.continuousOn
  · exact hCU.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  · have h1 : ContDiffOn ℝ 1 (deriv (htU f)) (Set.Ioo 0 (π / 2)) :=
      hCU.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    exact h1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  · have h1 : ContDiffOn ℝ 2 f (Set.Ioo 0 (π / 2)) := hf.mono Ioo_subset_Icc_self
    have h2 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (π / 2)) :=
      h1.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    exact h2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.FM.Core4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FM

/-! ## The self-similar family solves the model, and blows up -/







/-! ## The explicit solution formula `f = f₀/(1 - ½t L₁₂^K f₀)²` -/




end Work.FM
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Barrier =====
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

set_option autoImplicit false




end Work.FTS.Apriori
end
end
-- ===== merged: Submission.Work.FTS.Apriori.ZeroMode.ZM_IBP_R =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Apriori.ZeroMode

open scoped Real Topology
open MeasureTheory Set Filter

theorem ZM_IBP_R {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f)
    (hu : ContinuousOn (Work.FTS.Apriori.ZeroMode.uOf f) (Set.Ioi 0)) :
    ∀ ε ρ : ℝ, 0 < ε → ε < ρ →
      ∫ r in Set.Ioc ε ρ, Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r) ^ 2
        = -(Work.FTS.Apriori.ZeroMode.ROf f ρ / (1 + ρ))
          + Work.FTS.Apriori.ZeroMode.ROf f ε / (1 + ε)
          - ∫ r in Set.Ioc ε ρ, Work.FTS.Apriori.ZeroMode.uOf f r / (1 + r) := by
  intro ε ρ hε hερ
  have hερle : ε ≤ ρ := le_of_lt hερ
  -- `ROf f r = ∫_r^∞ uOf f s ds` is a primitive of `-uOf f` (`hasDerivAt_L12`), so the
  -- identity is integration by parts with the antiderivative `r ↦ -1/(1+r)` of `(1+r)⁻²`.
  -- First rewrite the two set integrals over `Ioc ε ρ` as interval integrals `ε..ρ`.
  have hIoc1 : (∫ r in ε..ρ, Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r) ^ 2)
      = ∫ r in Set.Ioc ε ρ, Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r) ^ 2 :=
    intervalIntegral.integral_of_le hερle
  have hIoc2 : (∫ r in ε..ρ, Work.FTS.Apriori.ZeroMode.uOf f r / (1 + r))
      = ∫ r in Set.Ioc ε ρ, Work.FTS.Apriori.ZeroMode.uOf f r / (1 + r) :=
    intervalIntegral.integral_of_le hερle
  rw [← hIoc1, ← hIoc2]
  -- the integration interval lies in `(0,∞)`
  have hsub : Set.uIcc ε ρ ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le hερle]
    intro x hx
    exact Set.mem_Ioi.mpr (lt_of_lt_of_le hε hx.1)
  -- the density is integrable on `(0,∞)` (hypothesis `hintL2` of `L12Hyp`)
  have hint : IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) := by
    simpa only [Work.Construction.L12dens] using H.hintL2
  have hudens : ContinuousOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) := hu
  -- `ROf f` has derivative `-(uOf f)`
  have hderiv_u : ∀ x ∈ Set.uIcc ε ρ, HasDerivAt (Work.FTS.Apriori.ZeroMode.ROf f)
      (-(Work.FTS.Apriori.ZeroMode.uOf f x)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hsub hx
    have hcont : ContinuousAt (Work.FM.L12dens Work.Spaces.K f) x :=
      hudens.continuousAt (isOpen_Ioi.mem_nhds hx0)
    exact Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := f) (a := 0) (ρ := x)
      hint hcont hx0
  -- `r ↦ -1/(1+r)` has derivative `(1+r)⁻²`
  have hderiv_v : ∀ x ∈ Set.uIcc ε ρ,
      HasDerivAt (fun r : ℝ => -1 / (1 + r)) (1 / (1 + x) ^ 2) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hsub hx
    have hne : (1 + x : ℝ) ≠ 0 := by positivity
    have hlin : HasDerivAt (fun r : ℝ => 1 + r) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have h := (hasDerivAt_const x (-1 : ℝ)).div hlin hne
    have hd : ((0 : ℝ) * (1 + x) - -1 * 1) / (1 + x) ^ 2 = 1 / (1 + x) ^ 2 := by
      congr 1; ring
    rw [hd] at h
    exact h
  have hInt_u : IntervalIntegrable (fun x : ℝ => -(Work.FTS.Apriori.ZeroMode.uOf f x))
      volume ε ρ :=
    (hu.neg.mono hsub).intervalIntegrable
  have hInt_v : IntervalIntegrable (fun x : ℝ => 1 / (1 + x) ^ 2) volume ε ρ := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · fun_prop
    · intro x hx
      have hx0 : (0 : ℝ) < x := hsub hx
      positivity
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := ε) (b := ρ)
    (u := Work.FTS.Apriori.ZeroMode.ROf f)
    (u' := fun x : ℝ => -(Work.FTS.Apriori.ZeroMode.uOf f x))
    (v := fun r : ℝ => -1 / (1 + r))
    (v' := fun x : ℝ => 1 / (1 + x) ^ 2)
    hderiv_u hderiv_v hInt_u hInt_v
  rw [show (∫ r in ε..ρ, Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r) ^ 2)
      = ∫ r in ε..ρ, Work.FTS.Apriori.ZeroMode.ROf f r * (1 / (1 + r) ^ 2) from
    intervalIntegral.integral_congr (fun x _ => by rw [div_eq_mul_one_div])]
  rw [hibp]
  rw [show (∫ x in ε..ρ, (-(Work.FTS.Apriori.ZeroMode.uOf f x)) * (-1 / (1 + x)))
      = ∫ x in ε..ρ, Work.FTS.Apriori.ZeroMode.uOf f x / (1 + x) from
    intervalIntegral.integral_congr (fun x _ => by ring_nf)]
  ring_nf

end Work.FTS.Apriori.ZeroMode
end
-- ===== merged: Submission.Work.FTS.Apriori.ZeroMode.ZM_Limits_L1 =====
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

set_option autoImplicit false

/-- The indicator of a measurable set of an `L¹`-function is integrable. -/
theorem zm_integrable_indicator {g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hg : IntegrableOn g s) : Integrable (s.indicator g) :=
  (integrable_indicator_iff hs).mpr hg

/-- The set integrals of an `L¹`-function over `(0,ε]` tend to `0` as `ε → 0⁺`. -/
theorem zm_tendsto_Ioc_zero {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioi 0)) :
    Tendsto (fun ε : ℝ => ∫ r in Set.Ioc (0:ℝ) ε, g r) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hgi : Integrable ((Set.Ioi (0:ℝ)).indicator g) :=
    zm_integrable_indicator measurableSet_Ioi hg
  have hfam : ∀ ε : ℝ, (∫ r in Set.Ioc (0:ℝ) ε, g r)
      = ∫ r : ℝ, (Set.Ioc (0:ℝ) ε).indicator g r :=
    fun ε => (integral_indicator measurableSet_Ioc).symm
  have hgoal : Tendsto (fun ε : ℝ => ∫ r : ℝ, (Set.Ioc (0:ℝ) ε).indicator g r)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := 𝓝[>] (0:ℝ))
      (F := fun ε : ℝ => fun r : ℝ => (Set.Ioc (0:ℝ) ε).indicator g r)
      (f := fun _ : ℝ => (0:ℝ))
      (fun a => ‖(Set.Ioi (0:ℝ)).indicator g a‖) ?_ ?_ hgi.norm ?_
    · simpa using h
    · filter_upwards with ε
      refine AEStronglyMeasurable.congr
        (show AEStronglyMeasurable ((Set.Ioc (0:ℝ) ε).indicator ((Set.Ioi (0:ℝ)).indicator g)) volume from
          AEStronglyMeasurable.indicator hgi.aestronglyMeasurable measurableSet_Ioc) ?_
      filter_upwards with r
      by_cases hr : r ∈ Set.Ioc (0:ℝ) ε
      · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr,
          Set.indicator_of_mem (show r ∈ Set.Ioi (0:ℝ) from hr.1)]
      · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards with r
      by_cases hr : r ∈ Set.Ioc (0:ℝ) ε
      · rw [Set.indicator_of_mem hr,
          Set.indicator_of_mem (show r ∈ Set.Ioi (0:ℝ) from hr.1)]
      · rw [Set.indicator_of_notMem hr]
        simp
    · filter_upwards with r
      by_cases hr : 0 < r
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
        rw [Set.indicator_of_notMem]
        exact fun h => absurd h.2 (not_le.mpr hε.2)
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards with ε
        rw [Set.indicator_of_notMem]
        exact fun h => absurd h.1 (not_lt.mpr (not_lt.mp hr))
  exact hgoal.congr' (Filter.Eventually.of_forall fun ε => (hfam ε).symm)

/-- The set integrals of an `L¹`-function over `(ε,ρ]` tend to the integral over `(ε,∞)`,
as `ρ → ∞`. -/
theorem zm_tendsto_Ioc_atTop {g : ℝ → ℝ} {ε : ℝ} (hg : IntegrableOn g (Set.Ioi ε)) :
    Tendsto (fun ρ : ℝ => ∫ r in Set.Ioc ε ρ, g r) atTop
      (𝓝 (∫ r in Set.Ioi ε, g r)) := by
  have hgi : Integrable ((Set.Ioi ε).indicator g) := zm_integrable_indicator measurableSet_Ioi hg
  have hfam : ∀ ρ : ℝ, (∫ r in Set.Ioc ε ρ, g r)
      = ∫ r : ℝ, (Set.Ioc ε ρ).indicator g r :=
    fun ρ => (integral_indicator measurableSet_Ioc).symm
  have hgoal : Tendsto (fun ρ : ℝ => ∫ r : ℝ, (Set.Ioc ε ρ).indicator g r) atTop
      (𝓝 (∫ r in Set.Ioi ε, g r)) := by
    have hpt : (∫ r in Set.Ioi ε, g r) = ∫ r : ℝ, (Set.Ioi ε).indicator g r :=
      (integral_indicator measurableSet_Ioi).symm
    rw [hpt]
    refine tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atTop)
      (F := fun ρ : ℝ => fun r : ℝ => (Set.Ioc ε ρ).indicator g r)
      (f := fun r : ℝ => (Set.Ioi ε).indicator g r)
      (fun a => ‖(Set.Ioi ε).indicator g a‖) ?_ ?_ hgi.norm ?_
    · filter_upwards with ρ
      refine AEStronglyMeasurable.congr
        (show AEStronglyMeasurable ((Set.Ioc ε ρ).indicator ((Set.Ioi ε).indicator g)) volume from
          AEStronglyMeasurable.indicator hgi.aestronglyMeasurable measurableSet_Ioc) ?_
      filter_upwards with r
      by_cases hr : r ∈ Set.Ioc ε ρ
      · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr,
          Set.indicator_of_mem (show r ∈ Set.Ioi ε from hr.1)]
      · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]
    · filter_upwards [Ioi_mem_atTop ε] with ρ hρ
      filter_upwards with r
      by_cases hr : r ∈ Set.Ioc ε ρ
      · rw [Set.indicator_of_mem hr,
          Set.indicator_of_mem (show r ∈ Set.Ioi ε from hr.1)]
      · rw [Set.indicator_of_notMem hr]
        simp
    · filter_upwards with r
      by_cases hr : ε < r
      · refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [Ioi_mem_atTop r] with ρ hρ
        rw [Set.indicator_of_mem (show r ∈ Set.Ioi ε from hr),
          Set.indicator_of_mem (show r ∈ Set.Ioc ε ρ from ⟨hr, le_of_lt hρ⟩)]
      · refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards with ρ
        rw [Set.indicator_of_notMem
            (show r ∉ Set.Ioi ε from fun h => absurd h (not_lt.mpr (not_lt.mp hr))),
          Set.indicator_of_notMem
            (show r ∉ Set.Ioc ε ρ from fun h => absurd h.1 (not_lt.mpr (not_lt.mp hr)))]
  exact hgoal.congr' (Filter.Eventually.of_forall fun ρ => (hfam ρ).symm)

end Work.FTS.Apriori.ZeroMode
end
end
-- ===== merged: Submission.Work.FTS.Apriori.ZeroMode.ZM_Nfun_limits =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Apriori.ZeroMode

open scoped Real Topology
open MeasureTheory Set Filter

/-- The standard DCT step for the a.e. convergence of `r ↦ A_r.indicator g x`. -/
lemma ae_tendsto_indicator_lt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ : α → ℝ} {S : Set α} {h : α → ℝ} {r₀ : ℝ}
    (hnull : μ (S ∩ {x | φ x = r₀}) = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun r : ℝ => ({x' | r < φ x'}).indicator (S.indicator h) x) (𝓝 r₀)
      (𝓝 (({x' | r₀ < φ x'}).indicator (S.indicator h) x)) := by
  classical
  have hae : ∀ᵐ x ∂μ, x ∉ S ∨ φ x ≠ r₀ := by
    rw [ae_iff]
    convert hnull using 2
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, not_or, not_not]
  filter_upwards [hae] with x hx
  rcases hx with hxS | hxphi
  · have hg0 : (S.indicator h) x = 0 := Set.indicator_of_notMem hxS h
    have h0 : ∀ r : ℝ, ({x' | r < φ x'}).indicator (S.indicator h) x = 0 := by
      intro r
      rw [Set.indicator_apply, hg0]
      simp
    simp only [h0]
    exact tendsto_const_nhds
  · rcases lt_or_gt_of_ne hxphi with hlt | hgt
    · have hev : (fun _ : ℝ => ({x' | r₀ < φ x'}).indicator (S.indicator h) x) =ᶠ[𝓝 r₀]
          (fun r : ℝ => ({x' | r < φ x'}).indicator (S.indicator h) x) := by
        filter_upwards [Ioi_mem_nhds hlt] with r hr
        have hm1 : x ∉ {x' : α | r < φ x'} := fun hc => not_lt.mpr (le_of_lt hr) (by simpa using hc)
        have hm2 : x ∉ {x' : α | r₀ < φ x'} := fun hc => not_lt.mpr (le_of_lt hlt) (by simpa using hc)
        rw [Set.indicator_of_notMem hm1 (S.indicator h),
            Set.indicator_of_notMem hm2 (S.indicator h)]
      exact tendsto_const_nhds.congr' hev
    · have hev : (fun _ : ℝ => ({x' | r₀ < φ x'}).indicator (S.indicator h) x) =ᶠ[𝓝 r₀]
          (fun r : ℝ => ({x' | r < φ x'}).indicator (S.indicator h) x) := by
        filter_upwards [Iio_mem_nhds hgt] with r hr
        have hm1 : x ∈ {x' : α | r < φ x'} := by simpa using hr
        have hm2 : x ∈ {x' : α | r₀ < φ x'} := by simpa using hgt
        rw [Set.indicator_of_mem hm1 (S.indicator h),
            Set.indicator_of_mem hm2 (S.indicator h)]
      exact tendsto_const_nhds.congr' hev

theorem tendsto_setIntegral_Ioi_atTop {u : ℝ → ℝ} (hu : IntegrableOn u (Ioi 0) volume) :
    Tendsto (fun r : ℝ => ∫ x in Ioi r, u x) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := (volume : Measure ℝ)) (f := u)
    (s := fun r : ℝ => Ioi r) (fun r => measurableSet_Ioi) (fun a b hab => Ioi_subset_Ioi hab)
    ⟨0, hu⟩
  rwa [show (⋂ r : ℝ, Ioi r) = (∅ : Set ℝ) from by
    ext x; simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall]
    exact ⟨x, lt_irrefl x⟩, setIntegral_empty] at h

theorem continuous_setIntegral_lt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℝ} {S : Set α} (hS : MeasurableSet S) (hint : IntegrableOn h S μ)
    {φ : α → ℝ} (hφ : Measurable φ) (hnull : ∀ r₀ : ℝ, μ (S ∩ {x | φ x = r₀}) = 0) :
    Continuous (fun r : ℝ => ∫ x in S ∩ {x | r < φ x}, h x ∂μ) := by
  classical
  rw [continuous_iff_continuousAt]
  intro r₀
  have hg : Integrable (S.indicator h) μ := (integrable_indicator_iff hS).mpr hint
  have haesm : AEStronglyMeasurable (S.indicator h) μ := hg.aestronglyMeasurable
  have hmeas : ∀ r : ℝ, MeasurableSet {x | r < φ x} := fun r => hφ measurableSet_Ioi
  have hkey : ∀ r : ℝ, (∫ x in S ∩ {x | r < φ x}, h x ∂μ)
      = ∫ x, ({x | r < φ x}).indicator (S.indicator h) x ∂μ := by
    intro r
    have h1 : (S ∩ {x | r < φ x}).indicator h
        = ({x | r < φ x}).indicator (S.indicator h) := by
      rw [indicator_indicator]
      exact congrArg (fun t => t.indicator h) (Set.inter_comm S {x | r < φ x})
    rw [← integral_indicator (hS.inter (hmeas r)), h1]
  simp_rw [hkey]
  exact tendsto_integral_filter_of_dominated_convergence (fun x => ‖S.indicator h x‖)
    (Eventually.of_forall fun r => haesm.indicator (hmeas r))
    (Eventually.of_forall fun _ => ae_of_all _ fun _ => norm_indicator_le_norm_self _ _)
    hg.norm (ae_tendsto_indicator_lt (hnull r₀))

theorem ZM_Nfun_limits {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) :
    ContinuousOn (Work.FTS.Apriori.ZeroMode.NOf f) (Set.Ici 0)
    ∧ Filter.Tendsto (Work.FTS.Apriori.ZeroMode.NOf f) Filter.atTop (𝓝 0)
    ∧ Filter.Tendsto (Work.FTS.Apriori.ZeroMode.ROf f) (𝓝[>] (0 : ℝ))
        (𝓝 (Work.FTS.Apriori.ZeroMode.ROf f 0))
    ∧ Filter.Tendsto (fun r : ℝ => Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r))
        Filter.atTop (𝓝 0) := by
  have hIθ : MeasurableSet (Work.Spaces.Iθ : Set ℝ) := by
    simp only [Work.Spaces.Iθ]; exact measurableSet_Icc
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) continuity of NOf on [0,∞)
    have hnull : ∀ r₀ : ℝ, (volume : Measure (ℝ × ℝ))
        ((Ioi 0 ×ˢ (Work.Spaces.Iθ : Set ℝ)) ∩ {p : ℝ × ℝ | p.1 = r₀}) = 0 := by
      intro r₀
      refine measure_mono_null (t := ({r₀} ×ˢ (univ : Set ℝ))) ?_ ?_
      · intro p hp
        exact ⟨hp.2, mem_univ p.2⟩
      · change (volume.prod volume) ({r₀} ×ˢ (univ : Set ℝ)) = 0
        rw [Measure.prod_prod]
        simp
    have hcont : Continuous (fun r : ℝ =>
        ∫ p in (Ioi 0 ×ˢ (Work.Spaces.Iθ : Set ℝ)) ∩ {p : ℝ × ℝ | r < p.1},
          Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2 ∂(volume : Measure (ℝ × ℝ))) :=
      continuous_setIntegral_lt (μ := (volume : Measure (ℝ × ℝ)))
        (h := fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
        (S := Ioi 0 ×ˢ (Work.Spaces.Iθ : Set ℝ))
        (measurableSet_Ioi.prod hIθ) H.hint measurable_fst hnull
    refine hcont.continuousOn.congr ?_
    intro r hr
    have hset : (Ioi 0 ×ˢ (Work.Spaces.Iθ : Set ℝ)) ∩ {p : ℝ × ℝ | r < p.1}
        = (Ioi r) ×ˢ (Work.Spaces.Iθ : Set ℝ) := by
      ext p
      show (p.1 ∈ Ioi (0:ℝ) ∧ p.2 ∈ (Work.Spaces.Iθ : Set ℝ)) ∧ r < p.1 ↔
        p.1 ∈ Ioi r ∧ p.2 ∈ (Work.Spaces.Iθ : Set ℝ)
      simp only [mem_Ioi]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩; exact ⟨⟨lt_of_le_of_lt hr h3, h2⟩, h3⟩
    simp only [Work.FTS.Apriori.ZeroMode.NOf_eq]
    rw [hset]
  · -- (2) NOf → 0 at +∞
    have hIinter : (⋂ r : ℝ, (Ioi r) ×ˢ (Work.Spaces.Iθ : Set ℝ))
        = (∅ : Set (ℝ × ℝ)) := by
      ext p
      simp only [mem_iInter, mem_prod, mem_Ioi, mem_empty_iff_false, iff_false, not_forall]
      exact ⟨p.1, fun h => lt_irrefl p.1 h.1⟩
    have h := tendsto_setIntegral_of_antitone (μ := (volume : Measure (ℝ × ℝ)))
      (f := fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (s := fun r : ℝ => (Ioi r) ×ˢ (Work.Spaces.Iθ : Set ℝ))
      (fun r => measurableSet_Ioi.prod hIθ)
      (fun a b hab => Set.prod_mono (Ioi_subset_Ioi hab) subset_rfl)
      ⟨0, H.hint⟩
    rw [hIinter, setIntegral_empty] at h
    simpa only [Work.FTS.Apriori.ZeroMode.NOf_eq] using h
  · -- (3) ROf is right-continuous at 0
    have hnull : ∀ r₀ : ℝ, (volume : Measure ℝ) (Ioi 0 ∩ {x : ℝ | x = r₀}) = 0 := by
      intro r₀
      refine measure_mono_null (t := ({r₀} : Set ℝ)) ?_ ?_
      · intro x hx; exact hx.2
      · exact Real.volume_singleton
    have hcont : Continuous (fun r : ℝ =>
        ∫ x in Ioi 0 ∩ {x : ℝ | r < x}, Work.Construction.L12dens f x ∂(volume : Measure ℝ)) :=
      continuous_setIntegral_lt (μ := (volume : Measure ℝ))
        (h := Work.Construction.L12dens f) (S := Ioi 0) measurableSet_Ioi H.hintL2
        measurable_id hnull
    have hF0 : (∫ x in Ioi 0 ∩ {x : ℝ | (0:ℝ) < x},
        Work.Construction.L12dens f x ∂(volume : Measure ℝ)) = ROf f 0 := by
      rw [show Ioi 0 ∩ {x : ℝ | (0:ℝ) < x} = Ioi 0 from by ext x; simp [Set.mem_Ioi]]
      simp only [Work.FTS.Apriori.ZeroMode.ROf_eq, Work.Coercivity.L12f, Work.FM.L12,
        Work.Construction.L12dens]
    have heq : ROf f =ᶠ[𝓝[>] (0:ℝ)] (fun r : ℝ =>
        ∫ x in Ioi 0 ∩ {x : ℝ | r < x}, Work.Construction.L12dens f x ∂(volume : Measure ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [show Ioi 0 ∩ {x : ℝ | r < x} = Ioi r from by
        ext x; simp only [mem_inter_iff, mem_Ioi]; constructor
        · rintro ⟨h1, h2⟩; exact h2
        · intro h2; exact ⟨lt_trans (by simpa using hr) h2, h2⟩]
      simp only [Work.FTS.Apriori.ZeroMode.ROf_eq, Work.Coercivity.L12f, Work.FM.L12,
        Work.Construction.L12dens]
    have h1 : Tendsto (fun r : ℝ =>
        ∫ x in Ioi 0 ∩ {x : ℝ | r < x}, Work.Construction.L12dens f x ∂(volume : Measure ℝ))
        (𝓝[>] (0:ℝ)) (𝓝 (ROf f 0)) := by
      have h2 : Tendsto (fun r : ℝ =>
          ∫ x in Ioi 0 ∩ {x : ℝ | r < x}, Work.Construction.L12dens f x ∂(volume : Measure ℝ))
          (𝓝[>] (0:ℝ))
          (𝓝 (∫ x in Ioi 0 ∩ {x : ℝ | (0:ℝ) < x},
            Work.Construction.L12dens f x ∂(volume : Measure ℝ))) :=
        (hcont.continuousAt (x := 0)).continuousWithinAt (s := Ioi (0:ℝ))
      rwa [hF0] at h2
    exact h1.congr' heq.symm
  · -- (4) ROf r / (1+r) → 0 at +∞
    have htail : Tendsto (ROf f) atTop (𝓝 0) := by
      have h := tendsto_setIntegral_Ioi_atTop
        (u := fun x => Work.Construction.L12dens f x) H.hintL2
      have e : (fun r : ℝ => ∫ x in Ioi r, Work.Construction.L12dens f x) = ROf f := by
        funext r
        simp only [Work.FTS.Apriori.ZeroMode.ROf_eq, Work.Coercivity.L12f, Work.FM.L12,
          Work.Construction.L12dens]
      rwa [e] at h
    have hinv : Tendsto (fun r : ℝ => (1 + r)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    have hmul := htail.mul hinv
    simpa [div_eq_mul_inv] using hmul

end Work.FTS.Apriori.ZeroMode
end
-- ===== merged: Submission.Work.FTS.Apriori.ZeroMode.ZM_Nfun_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Apriori.ZeroMode

open scoped Real Topology
open MeasureTheory Set Filter

theorem ZM_Nfun_zero {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f)
    (hrel : ∀ r : ℝ, 0 < r → r * Work.FTS.Apriori.ZeroMode.uOf f r
      = - Work.FTS.Apriori.ZeroMode.NOf f r)
    (hcont : ContinuousWithinAt (Work.FTS.Apriori.ZeroMode.NOf f) (Set.Ici 0) 0) :
    Work.FTS.Apriori.ZeroMode.NOf f 0 = 0 := by
  -- `uOf f = L12dens f`, which is integrable on `(0,∞)` by the hypothesis `hintL2`.
  have hInt : MeasureTheory.IntegrableOn (uOf f) (Set.Ioi 0) := H.hintL2
  -- `hcont` transfers from `[0,∞)` to the filter `𝓝[>] 0` of the right-hand neighbourhoods.
  have hcont' : Tendsto (NOf f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (NOf f 0)) :=
    hcont.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
  -- `hrel` identifies `r * uOf f r` with `-NOf f r` on `(0,∞)`.
  have hev : (fun r : ℝ => -NOf f r) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun r : ℝ => r * uOf f r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hrel r hr).symm
  -- Hence `r * uOf f r → -NOf f 0` as `r → 0⁺`.
  have hlim : Tendsto (fun r : ℝ => r * uOf f r) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-(NOf f 0))) := hcont'.neg.congr' hev
  -- Taking absolute values, the same is true of `|r * uOf f r|`, with limit `|-NOf f 0|`.
  have hlimAbs : Tendsto (fun r : ℝ => |r * uOf f r|) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds |-(NOf f 0)|) := hlim.abs
  -- `|uOf f|` is integrable on `(0,∞)`, and for `z > 0` it agrees with `|z * uOf f z| / z`.
  have hIntAbs : MeasureTheory.IntegrableOn (fun z : ℝ => |uOf f z|) (Set.Ioi 0) := hInt.abs
  have hIntDiv : MeasureTheory.IntegrableOn (fun z : ℝ => |z * uOf f z| / z) (Set.Ioi 0) :=
    hIntAbs.congr_fun (fun z hz => by
      rw [abs_mul, abs_of_pos hz, mul_div_cancel_left₀ _ (ne_of_gt hz)]) measurableSet_Ioi
  -- The integrability lemma forces the limit of `|r * uOf f r|` at `0⁺` to be `≤ 0`.
  have hle : |-(NOf f 0)| ≤ 0 :=
    Work.FTS.EllipticEst.le_zero_of_tendsto_nhdsGT_zero_of_integrableOn_div
      (F := fun z : ℝ => |z * uOf f z|) (fun z _ => abs_nonneg (z * uOf f z)) hIntDiv hlimAbs
  have hzero : -(NOf f 0) = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  exact neg_eq_zero.mp hzero

end Work.FTS.Apriori.ZeroMode
end
-- ===== merged: Submission.Work.FTS.Apriori.ZeroMode.ZM_density_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Apriori.ZeroMode

open scoped Real Topology
open MeasureTheory Set Filter

/-- For almost every `r > 0` the angular slice `θ ↦ K(θ) ∂_z f(r,θ)` is integrable on `Iθ`.
This is the a.e.-slice form of the joint integrability hypothesis `L12Hyp.hint` (Fubini on the
product `(0,∞) × Iθ`). -/
theorem ae_integrableOn_K_pz {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) :
    ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.pz f r θ)
        Work.Spaces.Iθ := by
  have h := H.hint
  rw [MeasureTheory.IntegrableOn, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    ← Measure.prod_restrict] at h
  filter_upwards [h.prod_right_ae] with r hr
  simpa [Work.Spaces.Iθ, MeasureTheory.IntegrableOn, Function.uncurry] using hr

/-- The angular normalisation: `∫_{Iθ} K(θ)Γ(θ) dθ = c(α)`. -/
theorem integral_K_Gam_eq_c (α : ℝ) :
    ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ = Work.Spaces.c α := by
  simp only [Work.Spaces.c]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-- Additivity of a set integral over a sum of four functions. -/
theorem setIntegral_add_four {s : Set ℝ} {a b c d : ℝ → ℝ}
    (ha : MeasureTheory.IntegrableOn a s) (hb : MeasureTheory.IntegrableOn b s)
    (hc : MeasureTheory.IntegrableOn c s) (hd : MeasureTheory.IntegrableOn d s) :
    (∫ x in s, (a x + b x + c x + d x))
      = (∫ x in s, a x) + (∫ x in s, b x) + (∫ x in s, c x) + (∫ x in s, d x) := by
  have h1 : (∫ x in s, a x) + (∫ x in s, b x) = (∫ x in s, a x + b x) :=
    (MeasureTheory.integral_add ha hb).symm
  have h2 : (∫ x in s, a x + b x) + (∫ x in s, c x) = (∫ x in s, a x + b x + c x) :=
    (MeasureTheory.integral_add (ha.add hb) hc).symm
  have h3 : (∫ x in s, a x + b x + c x) + (∫ x in s, d x)
      = (∫ x in s, a x + b x + c x + d x) :=
    (MeasureTheory.integral_add ((ha.add hb).add hc) hd).symm
  rw [← h3, ← h2, ← h1]

theorem ZM_density_ae {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f)
    (hslice : ∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ) Work.Spaces.Iθ) :
    ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.FTS.Apriori.ZeroMode.GOf α f r - Work.FTS.Apriori.ZeroMode.uOf f r
        = Work.FTS.Apriori.ZeroMode.mdOf f r
          - 2 * Work.FTS.Apriori.ZeroMode.uOf f r / (1 + r)
          - 2 * Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r) ^ 2 := by
  -- the normalisation constant does not vanish
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero H.hα H.hα1
  -- `K·Γ` is integrable on the angular interval (no integrability of `f` needed)
  have hGK : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
    simpa only [mul_comm] using Work.Spaces.CAux.integrableOn_GamK α H.hα
  filter_upwards [ae_integrableOn_K_pz H,
    MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hpz hr
  have hrpos : 0 < r := hr
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have h1r : (1 : ℝ) + r ≠ 0 := by positivity
  -- the four elementary pieces of the density of `𝓛_Γ f`
  set g1 : ℝ → ℝ := fun θ => Work.Spaces.K θ * f r θ / r with hg1
  set g2 : ℝ → ℝ := fun θ => Work.Spaces.K θ * Work.Spaces.pz f r θ with hg2
  set g3 : ℝ → ℝ := fun θ => (-2 / (1 + r)) * g1 θ with hg3
  set g4 : ℝ → ℝ :=
    fun θ => (-(2 * Work.FTS.Apriori.ZeroMode.ROf f r / (Work.Spaces.c α * (1 + r) ^ 2)))
      * (Work.Spaces.K θ * Work.Spaces.Gam α θ) with hg4
  have h1 : MeasureTheory.IntegrableOn g1 Work.Spaces.Iθ :=
    (hslice r hrpos).div_const r
  have h2 : MeasureTheory.IntegrableOn g2 Work.Spaces.Iθ := hpz
  have h3 : MeasureTheory.IntegrableOn g3 Work.Spaces.Iθ := by
    rw [hg3]; exact h1.const_mul _
  have h4 : MeasureTheory.IntegrableOn g4 Work.Spaces.Iθ := by
    rw [hg4]; exact hGK.const_mul _
  -- pointwise expansion of the density integrand
  have hpt : ∀ θ : ℝ,
      Work.Spaces.K θ * Work.Coercivity.LGamma α f r θ / r = (g1 + g2 + g3 + g4) θ := by
    intro θ
    simp only [hg1, hg2, hg3, hg4, Pi.add_apply, Work.Coercivity.LGamma, Work.Coercivity.L,
      Work.Spaces.Dz, ROf_eq]
    field_simp
    ring
  -- `GOf α f r` is the integral of the four pieces
  have hG : Work.FTS.Apriori.ZeroMode.GOf α f r
      = ∫ θ in Work.Spaces.Iθ, (g1 + g2 + g3 + g4) θ := by
    rw [show Work.FTS.Apriori.ZeroMode.GOf α f r
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Coercivity.LGamma α f r θ / r
        from rfl]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt θ)
  -- split the integral into the four pieces
  have hsplit : (∫ θ in Work.Spaces.Iθ, (g1 + g2 + g3 + g4) θ)
      = (∫ θ in Work.Spaces.Iθ, g1 θ) + (∫ θ in Work.Spaces.Iθ, g2 θ)
        + (∫ θ in Work.Spaces.Iθ, g3 θ) + (∫ θ in Work.Spaces.Iθ, g4 θ) :=
    setIntegral_add_four h1 h2 h3 h4
  -- value of each piece
  have hu1 : (∫ θ in Work.Spaces.Iθ, g1 θ) = Work.FTS.Apriori.ZeroMode.uOf f r := by
    rw [hg1]
    rfl
  have hu2 : (∫ θ in Work.Spaces.Iθ, g2 θ) = Work.FTS.Apriori.ZeroMode.mdOf f r := by
    rw [hg2]
    rfl
  have hu3 : (∫ θ in Work.Spaces.Iθ, g3 θ)
      = (-2 / (1 + r)) * Work.FTS.Apriori.ZeroMode.uOf f r := by
    have h3' : (∫ θ in Work.Spaces.Iθ, g3 θ)
        = (-2 / (1 + r)) * (∫ θ in Work.Spaces.Iθ, g1 θ) := by
      rw [hg3]; exact MeasureTheory.integral_const_mul _ _
    rw [h3', hu1]
  have hu4 : (∫ θ in Work.Spaces.Iθ, g4 θ)
      = (-(2 * Work.FTS.Apriori.ZeroMode.ROf f r / (Work.Spaces.c α * (1 + r) ^ 2)))
        * Work.Spaces.c α := by
    have h4' : (∫ θ in Work.Spaces.Iθ, g4 θ)
        = (-(2 * Work.FTS.Apriori.ZeroMode.ROf f r / (Work.Spaces.c α * (1 + r) ^ 2)))
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ) := by
      rw [hg4]; exact MeasureTheory.integral_const_mul _ _
    rw [h4', integral_K_Gam_eq_c]
  -- assemble
  have hmain : Work.FTS.Apriori.ZeroMode.GOf α f r
      = Work.FTS.Apriori.ZeroMode.uOf f r + Work.FTS.Apriori.ZeroMode.mdOf f r
        - 2 * Work.FTS.Apriori.ZeroMode.uOf f r / (1 + r)
        - 2 * Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r) ^ 2 := by
    rw [hG, hsplit, hu1, hu2, hu3, hu4]
    field_simp
    ring
  rw [hmain]
  ring

end Work.FTS.Apriori.ZeroMode
end
-- ===== merged: Submission.Work.FTS.Apriori.ZeroMode.ZM_mderiv_fubini =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Apriori.ZeroMode

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Fubini for the angular `z`-integral `mdOf` and its tail form `NOf`.**

`mdOf f r = ∫_{Iθ} K(θ) ∂_z f(r,θ) dθ` and `NOf f r = ∫_{(r,∞) × Iθ} K(θ) ∂_z f(z,θ)` are the
inner and the joint form of the same function; the joint integrability hypothesis `H.hint`
therefore makes `mdOf f` integrable on `(0,∞)` and turns `NOf` into the tail integral of
`mdOf`.  Consequently the difference over `(ε,ρ)` is `NOf f ε - NOf f ρ` and the integral over
`(0,∞)` is `NOf f 0`. -/
theorem ZM_mderiv_fubini {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) :
    MeasureTheory.IntegrableOn (Work.FTS.Apriori.ZeroMode.mdOf f) (Set.Ioi 0)
    ∧ (∀ ε ρ : ℝ, 0 < ε → ε < ρ →
        ∫ r in Set.Ioc ε ρ, Work.FTS.Apriori.ZeroMode.mdOf f r
          = Work.FTS.Apriori.ZeroMode.NOf f ε - Work.FTS.Apriori.ZeroMode.NOf f ρ)
    ∧ (∫ r in Set.Ioi 0, Work.FTS.Apriori.ZeroMode.mdOf f r
        = Work.FTS.Apriori.ZeroMode.NOf f 0) := by
  -- The joint integrand, as a function on the product space.
  set g : ℝ × ℝ → ℝ := fun p => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2 with hg_def
  -- `mdOf f` is the first marginal of `g`; `NOf f r` is its integral over `(r,∞) × Iθ`.
  have hgmd : mdOf f = fun r => ∫ θ, g (r, θ) ∂(volume.restrict Work.Spaces.Iθ) := by
    funext r
    simp only [mdOf_eq, hg_def]
  have hgprod : IntegrableOn g (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) (volume.prod volume) := H.hint
  have hgi : Integrable g ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict (s := Set.Ioi 0) (t := Work.Spaces.Iθ)]
    exact hgprod
  have hInt : IntegrableOn (fun r => ∫ θ, g (r, θ) ∂(volume.restrict Work.Spaces.Iθ))
      (Set.Ioi 0) :=
    hgi.integral_prod_left
  -- Fubini on a rectangle `s × Iθ`.
  have key : ∀ s : Set ℝ, s ⊆ Set.Ioi 0 →
      ∫ r in s, mdOf f r = ∫ p in s ×ˢ Work.Spaces.Iθ, g p := by
    intro s hs
    rw [hgmd]
    exact (MeasureTheory.setIntegral_prod g (hgprod.mono_set (Set.prod_mono hs Subset.rfl))).symm
  -- `NOf f r` is the tail integral of `mdOf f`, for `r ≥ 0`.
  have hN : ∀ r : ℝ, 0 ≤ r → NOf f r = ∫ s in Set.Ioi r, mdOf f s := by
    intro r hr
    rw [key (Set.Ioi r) (Set.Ioi_subset_Ioi hr)]
    simp only [NOf_eq, hg_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [hgmd]; exact hInt
  · intro ε ρ hε hερ
    have hε0 : 0 ≤ ε := le_of_lt hε
    have hρ0 : 0 ≤ ρ := le_of_lt (lt_trans hε hερ)
    rw [hN ε hε0, hN ρ hρ0, ← Set.Ioi_sdiff_Ioi (a := ε) (b := ρ)]
    exact MeasureTheory.setIntegral_sdiff measurableSet_Ioi
      (hInt.mono_set (Set.Ioi_subset_Ioi hε0)) (Set.Ioi_subset_Ioi (le_of_lt hερ))
  · rw [key (Set.Ioi 0) Subset.rfl]
    simp only [NOf_eq, hg_def]

end Work.FTS.Apriori.ZeroMode
end
-- ===== merged: Submission.Work.FTS.Apriori.ZeroMode.ZM_slice_relation =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Apriori.ZeroMode

open scoped Real Topology
open MeasureTheory Set Filter

/-
# The slice relation for the zero-mode identity

This file proves `ZM_slice_relation`, the first ingredient of the `L₁₂` zero-mode identity
`L₁₂(𝓛_Γ f)(0) = -L₁₂(f)(0)` of the Elgindi project.  In the notation of
`Submission/Work/FTS/Apriori/ZeroMode/L12_ZMDefs.lean`:

* `Kpz f p = K(p.2) · ∂_z f(p.1, p.2)` is the joint (radial, angular) integrand whose
  integrability `H.hint` is the only measure-theoretic input;
* the hypotheses `H.hdiff` (radial differentiability), `H.hdec` (decay at `∞`) and `H.hvan`
  give, for almost every `θ ∈ Iθ`, the radial fundamental theorem of calculus
  `∫_{Ioi r} K θ ∂_z f(u,θ) du = -(K θ f(r,θ))` **for every** `r > 0`;
* combining that a.e. identity with Tonelli/Fubini gives, again for every `r > 0`,
  the integrability of `θ ↦ K θ f(r,θ)` on `Iθ` (the finiteness of the `θ`-integral needs
  the `∫⁻`-bound `‖∫‖ₑ ≤ ∫⁻ ‖·‖ₑ` and the swap of the two `lintegral`s; the a.e.-strong
  measurability is the `θ`-slice of the jointly integrable integrand), and finally
  `∫_{Iθ} K θ f(r,θ) dθ = -NOf f r`, where `NOf f r` is the *joint* integral
  `∫_{(Ioi r) × Iθ} K(θ) ∂_z f(z,θ)`.

The remaining hypotheses of `L12Hyp` (`hα`, `hα1`, `hcont`, `hvan`, `hintL`, `hintL2`,
`hint3`) are not needed here; they are kept because the statement is part of the requested
interface of the zero-mode chapter.
-/

/-- The joint integrand `K(θ) · ∂_z f(z,θ)` as a function on the product `ℝ × ℝ`. -/
private noncomputable def Kpz (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2

/-- The radial averaging identity for the integrand `K(θ) ∂_z f`.

For almost every `θ ∈ Iθ` the radial function `u ↦ K(θ) · f(u,θ)` has derivative
`K(θ) · ∂_z f(u,θ)` on `(0,∞)`, is continuous up to `0`, tends to `0` at `+∞` and its
derivative is integrable on `(0,∞)`; hence the fundamental theorem of calculus gives the
identity for every `r > 0` at once (the good `θ`-set does not depend on `r`). -/
private theorem slice_relation_ae {α : ℝ} {f : ℝ → ℝ → ℝ}
    (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ r : ℝ, 0 < r →
      ∫ u in Set.Ioi r, Kpz f (u, θ) = -(Work.Spaces.K θ * f r θ) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- `H.hint`, read as integrability for the product of the two restricted measures
  have hprod0 : Integrable (Kpz f)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [Measure.prod_restrict]
    exact H.hint
  -- a.e. in `θ`, the radial slice of the integrand is integrable on `(0,∞)`
  have hslice : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      IntegrableOn (fun u => Kpz f (u, θ)) (Set.Ioi 0) := by
    simpa [IntegrableOn] using hprod0.prod_left_ae
  filter_upwards [hslice, self_mem_ae_restrict hIθ] with θ hInt hmem
  intro r hr
  have hderiv : ∀ x ∈ Set.Ioi r, HasDerivAt (fun u : ℝ => Work.Spaces.K θ * f u θ)
      (Work.Spaces.K θ * Work.Spaces.pz f x θ) x := fun x hx =>
    (H.hdiff θ hmem x (lt_trans hr hx)).const_mul (Work.Spaces.K θ)
  have hcont' : ContinuousWithinAt (fun u : ℝ => Work.Spaces.K θ * f u θ) (Set.Ici r) r :=
    ((H.hdiff θ hmem r hr).continuousAt.continuousWithinAt).const_mul (Work.Spaces.K θ)
  have hint' : IntegrableOn (fun u : ℝ => Work.Spaces.K θ * Work.Spaces.pz f u θ)
      (Set.Ioi r) :=
    hInt.mono_set (Set.Ioi_subset_Ioi (le_of_lt hr))
  have hlim' : Tendsto (fun u : ℝ => Work.Spaces.K θ * f u θ) atTop (𝓝 0) := by
    simpa using (H.hdec θ hmem).const_mul (Work.Spaces.K θ)
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont' hderiv hint' hlim'
  simpa [Kpz] using this

/-- Integrability of the angular slice `θ ↦ K(θ) f(r,θ)` on `Iθ`, for **every** `r > 0`.

The a.e.-strong measurability is `AEStronglyMeasurable.integral_prod_right'` applied to the
swapped jointly integrable integrand; the finiteness of the `∫⁻`-norm is the inequality
`‖∫‖ₑ ≤ ∫⁻ ‖·‖ₑ` together with the a.e. identity `slice_relation_ae` and Tonelli's theorem
for `lintegral`s. -/
private theorem slice_integrable {α : ℝ} {f : ℝ → ℝ → ℝ}
    (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ) Work.Spaces.Iθ := by
  have hA := slice_relation_ae H
  -- integrability of the integrand over `(r,∞) × Iθ`
  have hprod : Integrable (Kpz f)
      ((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)) := by
    have h0 : IntegrableOn (Kpz f) (Set.Ioi r ×ˢ Work.Spaces.Iθ) :=
      H.hint.mono_set (Set.prod_mono (Set.Ioi_subset_Ioi (le_of_lt hr)) subset_rfl)
    rw [Measure.prod_restrict]
    exact h0
  refine ⟨?_, ?_⟩
  · -- a.e. strong measurability, as the `θ`-slice of a jointly integrable function
    have hswapM : AEStronglyMeasurable (fun z : ℝ × ℝ => Kpz f z.swap)
        ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Ioi r))) :=
      hprod.1.prod_swap
    have h1 : AEStronglyMeasurable
        (fun θ : ℝ => ∫ u, Kpz f (u, θ) ∂(volume.restrict (Set.Ioi r)))
        (volume.restrict Work.Spaces.Iθ) := hswapM.integral_prod_right'
    refine (h1.neg).congr ?_
    filter_upwards [hA] with θ hθ
    simp only [Pi.neg_apply]
    rw [hθ r hr]
    ring
  · -- finiteness of the `θ`-integral of the norm
    change (∫⁻ θ, ‖Work.Spaces.K θ * f r θ‖ₑ ∂(volume.restrict Work.Spaces.Iθ)) < ⊤
    have hAEM : AEMeasurable (fun p : ℝ × ℝ => ‖Kpz f p‖ₑ)
        ((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)) :=
      hprod.1.aemeasurable.enorm
    have hcomp : ∫⁻ θ, ‖Work.Spaces.K θ * f r θ‖ₑ ∂(volume.restrict Work.Spaces.Iθ)
        ≤ ∫⁻ θ, (∫⁻ u, ‖Kpz f (u, θ)‖ₑ ∂(volume.restrict (Set.Ioi r)))
            ∂(volume.restrict Work.Spaces.Iθ) := by
      refine lintegral_mono_ae ?_
      filter_upwards [hA] with θ hθ
      have heq : ‖Work.Spaces.K θ * f r θ‖ₑ
          = ‖∫ u, Kpz f (u, θ) ∂(volume.restrict (Set.Ioi r))‖ₑ := by
        rw [hθ r hr, enorm_neg]
      rw [heq]
      exact enorm_integral_le_lintegral_enorm _
    have hswap : (∫⁻ θ, (∫⁻ u, ‖Kpz f (u, θ)‖ₑ ∂(volume.restrict (Set.Ioi r)))
            ∂(volume.restrict Work.Spaces.Iθ))
        = ∫⁻ p, ‖Kpz f p‖ₑ
            ∂((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)) := by
      rw [← lintegral_prod_symm (fun p : ℝ × ℝ => ‖Kpz f p‖ₑ) hAEM]
    exact lt_of_le_of_lt (le_trans hcomp (le_of_eq hswap)) hprod.2

/-- The angular slice identity `∫_{Iθ} K(θ) f(r,θ) dθ = -NOf f r` for every `r > 0`.

`NOf f r` is the joint integral of `K ∂_z f` over `(r,∞) × Iθ`; Fubini turns it into the
iterated integral, `slice_relation_ae` identifies the inner integral with `-(K θ f(r,θ))`
for a.e. `θ`, and the outer integration is linear. -/
private theorem slice_value {α : ℝ} {f : ℝ → ℝ → ℝ}
    (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) {r : ℝ} (hr : 0 < r) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f r θ)
      = - Work.FTS.Apriori.ZeroMode.NOf f r := by
  have hA := slice_relation_ae H
  have hprod : Integrable (Kpz f)
      ((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)) := by
    have h0 : IntegrableOn (Kpz f) (Set.Ioi r ×ˢ Work.Spaces.Iθ) :=
      H.hint.mono_set (Set.prod_mono (Set.Ioi_subset_Ioi (le_of_lt hr)) subset_rfl)
    rw [Measure.prod_restrict]
    exact h0
  -- `NOf f r` is the integral of the integrand against the product measure
  have hNof : Work.FTS.Apriori.ZeroMode.NOf f r
      = ∫ p, Kpz f p
          ∂((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)) := by
    show (∫ p in (Set.Ioi r) ×ˢ Work.Spaces.Iθ, Kpz f p) = _
    rw [show (volume : Measure (ℝ × ℝ))
        = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl]
    rw [Measure.prod_restrict]
  have hcurried : Integrable (Function.uncurry (fun u θ => Kpz f (u, θ)))
      ((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)) := hprod
  have hswap : (∫ p, Kpz f p
        ∂((volume.restrict (Set.Ioi r)).prod (volume.restrict Work.Spaces.Iθ)))
      = ∫ θ, (∫ u, Kpz f (u, θ) ∂(volume.restrict (Set.Ioi r)))
          ∂(volume.restrict Work.Spaces.Iθ) := by
    rw [integral_prod _ hprod, integral_integral_swap hcurried]
  have hinner : (∫ θ, (∫ u, Kpz f (u, θ) ∂(volume.restrict (Set.Ioi r)))
        ∂(volume.restrict Work.Spaces.Iθ))
      = ∫ θ, -(Work.Spaces.K θ * f r θ) ∂(volume.restrict Work.Spaces.Iθ) := by
    refine integral_congr_ae ?_
    filter_upwards [hA] with θ hθ
    exact hθ r hr
  have hmain : Work.FTS.Apriori.ZeroMode.NOf f r
      = -(∫ θ, Work.Spaces.K θ * f r θ ∂(volume.restrict Work.Spaces.Iθ)) := by
    rw [hNof, hswap, hinner, integral_neg]
  linarith [hmain]

theorem ZM_slice_relation {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) :
    (∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), ∀ r : ℝ, 0 < r →
      ∫ u in Set.Ioi r, Work.Spaces.K θ * Work.Spaces.pz f u θ
        = -(Work.Spaces.K θ * f r θ))
    ∧ (∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ) Work.Spaces.Iθ)
    ∧ (∀ r : ℝ, 0 < r →
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f r θ) = - Work.FTS.Apriori.ZeroMode.NOf f r) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Kpz] using slice_relation_ae H
  · intro r hr
    exact slice_integrable H hr
  · intro r hr
    exact slice_value H hr

end Work.FTS.Apriori.ZeroMode
end
-- ===== merged: Submission.Work.FTS.ClassCHon.RgCSTarget =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/RgCSTarget` — the Cauchy–Schwarz step of the `w²`-weighted Green bound

This is the `L²(w²)` step promised in `RgL2Pointwise.lean` (§3 of
`NOTES_EllNode7_session3.md`).  The kernel of `radGreen` is split against the weight `w`,

  `c t · t^{Q-1} = (c t · w t) · (t^{Q-1} / w t)`,

so that `Work.Coercivity.holder_two_mul` on `volume.restrict (Set.Ioc 0 z)` turns the near
integral into `√(∫ (c w)²) · √(∫ t^{2Q-2}/w²)`, and the second factor is controlled by the
(now proved) weight integral `WeightIntegrals.near_weight_integral_le`.  Retaining the
`1/(α(4m+5))` of `radGreen` and using `rgQ α m ≥ 8m` then gives the headline
`|radGreen α m c z| ≤ ‖c‖_{w²}/(4α m^{3/2})`.

The two *integrals* entering the statement (`∫_{Ioi 0}(c·w)²` and `∫_{Ioc 0 z}(t^{Q-1}/w)²`)
are hypotheses here; both are discharged in the intended application by the slicewise conjunct
of `HkMem` and by `near_pow_form` + boundedness on `Ioc 0 z` (see the note).  The measurability
of the kernel factor `t^{Q-1}/w t` is proved in this file (`aestronglyMeasurable_div_w`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.ClassCHon

local notation "w" => Work.Spaces.w

/-- **Measurability of the kernel factor** `t^{Q-1}/w(t)` on `(0,∞)`.

`w t = (1+t)²/t²` is `ContinuousOn (Ioi 0)`, `t^{Q-1}` is continuous there for `Q > 1`, and the
denominator never vanishes on `(0,∞)` — so the quotient is `ContinuousOn (Ioi 0)`, hence a.e.
strongly measurable on the restricted measure.  (Note: this cannot be done with `Continuous.div`
on `ℝ`, where the denominator of the `(1+t)²/t²` form vanishes at `t = 0` and `t = -1`.) -/
theorem aestronglyMeasurable_div_w {Q : ℝ} (hQ : 1 < Q) :
    AEStronglyMeasurable (fun t : ℝ => t ^ (Q - 1) / w t) (volume.restrict (Set.Ioi 0)) := by
  have hfe : (fun t : ℝ => t ^ (Q - 1) / w t)
      = fun t : ℝ => t ^ (Q - 1) * t ^ 2 / (1 + t) ^ 2 := by
    funext t
    rw [Work.Spaces.w, div_eq_mul_inv, inv_div]
    ring
  rw [hfe]
  have hnum : ContinuousOn (fun t : ℝ => t ^ (Q - 1) * t ^ 2) (Set.Ioi 0) :=
    (continuousOn_id.rpow_const (fun t _ => Or.inr (by linarith))).mul (continuousOn_id.pow 2)
  have hden : ContinuousOn (fun t : ℝ => (1 + t) ^ 2) (Set.Ioi 0) :=
    (continuousOn_const.add continuousOn_id).pow 2
  exact (hnum.div hden (fun t ht => pow_ne_zero 2 (ne_of_gt (by have h1 : (0:ℝ) < t := ht; linarith)))).aestronglyMeasurable
    measurableSet_Ioi
local notation "rq" => Work.FTS.EllExist.rgQ
local notation "rp" => Work.FTS.EllExist.rgP

/-- The decaying branch of `radGreen` is `z^{-q}` times the interval integral of the kernel:
the unfolding needed before Cauchy–Schwarz.  (`rgF1 α m c t` is *definitionally*
`c t * t^{q-1}`, so `rfl` closes the last step; `rgF1` must **not** be `rw`-ed.) -/
theorem rgG1_eq {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    Work.FTS.EllExist.rgG1 α m c z
      = z ^ (-(rq α m)) * ∫ t in Set.Ioc (0 : ℝ) z, c t * t ^ (rq α m - 1) := by
  rw [Work.FTS.EllExist.rgG1, Work.FTS.EllExist.rgA,
    intervalIntegral.integral_of_le hz.le]
  rfl

/-- The growing branch of `radGreen` (already a set integral). -/
theorem rgG2_eq {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ} :
    Work.FTS.EllExist.rgG2 α m c z
      = z ^ (rp α m) * ∫ t in Set.Ioi z, c t * t ^ (-(rp α m) - 1) := by
  rw [Work.FTS.EllExist.rgG2, Work.FTS.EllExist.rgB]
  rfl


/-- **Measurability of the kernel factor** `t^{e}/w(t)` on `(0,∞)`, for an *arbitrary* real
exponent `e` (the far branch of `radGreen` uses the negative exponent `-p-1`). -/
theorem aestronglyMeasurable_div_w' {e : ℝ} :
    AEStronglyMeasurable (fun t : ℝ => t ^ e / w t) (volume.restrict (Set.Ioi 0)) := by
  have hfe : (fun t : ℝ => t ^ e / w t)
      = fun t : ℝ => t ^ e * t ^ 2 / (1 + t) ^ 2 := by
    funext t
    rw [Work.Spaces.w, div_eq_mul_inv, inv_div]
    ring
  rw [hfe]
  have hnum : ContinuousOn (fun t : ℝ => t ^ e * t ^ 2) (Set.Ioi 0) :=
    (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))).mul (continuousOn_id.pow 2)
  have hden : ContinuousOn (fun t : ℝ => (1 + t) ^ 2) (Set.Ioi 0) :=
    (continuousOn_const.add continuousOn_id).pow 2
  exact (hnum.div hden (fun t ht => pow_ne_zero 2 (ne_of_gt (by have h1 : (0:ℝ) < t := ht; linarith)))).aestronglyMeasurable
    measurableSet_Ioi



end Work.FTS.ClassCHon
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.GamL2.Prelim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Technical preliminaries for `GammaL2Bnd`

The elementary ingredients of the angular `L²`-estimate `|Γ/c − K|₂ ≤ 7/10`
(the paper's `GammaAssumption`), with `Γ(θ) = (sinθ cos²θ)^{α/3}`,
`K(θ) = 3 sinθ cos²θ` on `Iθ = [0,π/2]`:

* the Bernoulli-type `rpow` inequality `u(1−u^p) ≤ p(1−u)` for `0 ≤ u ≤ 1`;
* the pointwise core `(u^p − 3u)² ≤ (1 − 3u)² + 6p(1−u)`;
* the three angular integrals `∫_{Iθ} 1 = π/2`, `∫_{Iθ} sinθcos²θ = 1/3`,
  `∫_{Iθ} (sinθcos²θ)² = π/32`;
* the resulting bound `∫_{Iθ}(Γ − K)² ≤ 25π/32 − 2 + 6p(π/2)`;
* the normalisation bounds `c ≤ 1` and `1 − c ≤ 3p(π/2)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T.GamL2

/-! ## The elementary `rpow` inequality -/

/-- For `0 < u ≤ 1` and `p ≥ 0`: `u (1 − u^p) ≤ p (1 − u)`.

This is the Bernoulli-type inequality obtained from `1 − u^p ≤ p(−log u)` (which
is `1 − e^{p log u} ≤ −p log u`, i.e. `1 + x ≤ e^x` applied to `x = p log u`) and
`−log u ≤ (1−u)/u` (which is `log x ≤ x − 1` at `x = u⁻¹`). -/
lemma unit_sub_pow_le (u p : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (hp : 0 ≤ p) :
    u * (1 - u ^ p) ≤ p * (1 - u) := by
  have h1 : 1 - u ^ p ≤ p * (-Real.log u) := by
    have h := Real.add_one_le_exp (Real.log u * p)
    rw [Real.rpow_def_of_pos hu0]
    linarith
  have h2 : -Real.log u ≤ (1 - u) / u := by
    have h := Real.one_sub_inv_le_log_of_pos hu0
    have h3 : -Real.log u ≤ u⁻¹ - 1 := by linarith
    have h4 : u⁻¹ - 1 = (1 - u) / u := by field_simp
    rwa [h4] at h3
  have h3 : u * (1 - u ^ p) ≤ u * (p * (-Real.log u)) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt hu0)
  refine le_trans h3 ?_
  have h5 : u * (p * (-Real.log u)) ≤ u * (p * ((1 - u) / u)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hp) (le_of_lt hu0)
  have h6 : u * (p * ((1 - u) / u)) = p * (1 - u) := by field_simp
  rwa [h6] at h5

/-- The same inequality in the form used for `u = sinθcos²θ` (where `u` may vanish
at the endpoints of `Iθ`). -/
lemma unit_sub_pow_le' (u p : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hp : 0 ≤ p) :
    u * (1 - u ^ p) ≤ p * (1 - u) := by
  rcases hu0.eq_or_lt with h | h
  · subst h
    rw [zero_mul, sub_zero, mul_one]
    exact hp
  · exact unit_sub_pow_le u p h hu1 hp

/-- The pointwise core of the estimate: for `0 ≤ u ≤ 1` and `0 < p ≤ 1`,

  `(u^p − 3u)² ≤ 1 − 6u + 6p(1 − u) + 9u² = (1 − 3u)² + 6p(1 − u)`.

Indeed `(u^p − 3u)² = (u^p)² − 6u·u^p + 9u²`, and `(u^p)² ≤ 1` while
`u·u^p ≥ u − p(1 − u)` (`unit_sub_pow_le'`). -/
lemma pow_sub_three_mul_sq_le (u p : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hp0 : 0 < p)
    (hp1 : p ≤ 1) :
    (u ^ p - 3 * u) ^ 2 ≤ 1 - 6 * u + 6 * p * (1 - u) + 9 * u ^ 2 := by
  rcases eq_or_lt_of_le hu0 with h | h
  · subst h
    rw [Real.zero_rpow (ne_of_gt hp0)]
    nlinarith [hp0]
  · have hup : u ^ p ≤ 1 := Real.rpow_le_one hu0 hu1 (le_of_lt hp0)
    have hup0 : 0 ≤ u ^ p := Real.rpow_nonneg hu0 p
    have hlow : u - p * (1 - u) ≤ u * u ^ p := by
      have h' := unit_sub_pow_le u p h hu1 (le_of_lt hp0)
      nlinarith [h']
    have hsq : (u ^ p - 3 * u) ^ 2 = (u ^ p) ^ 2 - 6 * (u * u ^ p) + 9 * u ^ 2 := by ring
    have hsq2 : (u ^ p) ^ 2 ≤ 1 := by nlinarith [hup, hup0]
    rw [hsq]
    nlinarith [hsq2, hlow]

/-! ## The three elementary angular integrals -/

/-- `∫_{Iθ} 1 = vol(Iθ) = π/2`. -/
lemma int_Iθ_one : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def,
      Work.Spaces.Iθ, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- `∫_{Iθ} sinθ cos²θ = 1/3`, from `∫_{Iθ} K = 1` and `K = 3 sinθcos²θ`. -/
lemma int_Iθ_sinCos2 : (∫ θ in Work.Spaces.Iθ, Real.sin θ * Real.cos θ ^ 2) = 1 / 3 := by
  have h : (∫ θ in Work.Spaces.Iθ, 3 * (Real.sin θ * Real.cos θ ^ 2)) = 1 := by
    rw [← Work.Coercivity.integral_Itheta_K]
    refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [Work.Spaces.K]; ring
  rw [MeasureTheory.integral_const_mul] at h
  linarith

/-- `∫_{Iθ} (sinθ cos²θ)² = π/32`. -/
lemma int_Iθ_sinCos2_sq :
    (∫ θ in Work.Spaces.Iθ, (Real.sin θ * Real.cos θ ^ 2) ^ 2) = Real.pi / 32 := by
  simpa only [Work.Elliptic.sinCos2] using Work.FTS.EllipticEst.ang_integrals.2.1

/-! ## Integrability on `Iθ` -/


end Work.FTS.CoercivityFix.Coer1T.GamL2
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_gpoly_iterate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter Polynomial

namespace Work.FTS.CoercivityFix.E2Bound

/-- The Möbius chart `z ↦ (z - 1)/(z + 1)` has derivative `2/(z+1)²`. -/
lemma hasDerivAt_zchart (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun w => zchart w) (2 / (z + 1) ^ 2) z := by
  have hz1 : z + 1 ≠ 0 := by intro h; exact hz (by linarith)
  have h : HasDerivAt (fun w : ℝ => (w - 1) / (w + 1)) (2 / (z + 1) ^ 2) z := by
    have hd := ((hasDerivAt_id z).sub_const 1).div ((hasDerivAt_id z).add_const 1) hz1
    convert hd using 1
    · funext w
      simp only [id_eq, Pi.div_apply]
    · simp only [id_eq]
      ring
  simpa only [zchart_apply] using h

/-- One step of the intertwining: on `(0,∞)`, `Zop` acting on `gpoly P` is
`gpoly (Tmul P)`. -/
lemma Zop_gpoly_step (P : Polynomial ℝ) {z : ℝ} (hz : 0 < z) :
    Work.Spaces.Zop (gpoly P) z = gpoly (Tmul P) z := by
  have hz1 : z + 1 ≠ 0 := by intro h; linarith
  have hchain : deriv (fun w => P.eval (zchart w)) z
      = (Polynomial.derivative P).eval (zchart z) * (2 / (z + 1) ^ 2) := by
    have h : HasDerivAt (fun w => P.eval (zchart w))
        ((Polynomial.derivative P).eval (zchart z) * (2 / (z + 1) ^ 2)) z :=
      (Polynomial.hasDerivAt P (zchart z)).comp z (hasDerivAt_zchart z (by intro h; linarith))
    exact h.deriv
  have hc : z * (2 / (z + 1) ^ 2) = (1 : ℝ) / 2 * (1 - (zchart z) ^ 2) := by
    rw [zchart]
    field_simp
    ring
  show z * deriv (fun w => P.eval (zchart w)) z = (Tmul P).eval (zchart z)
  rw [hchain]
  simp only [Tmul_apply, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  rw [mul_comm ((Polynomial.derivative P).eval (zchart z)) (2 / (z + 1) ^ 2), ← mul_assoc, hc]

end Work.FTS.CoercivityFix.E2Bound

namespace Work.FTS.CoercivityFix.E2Bound.SlotMul

theorem Zop_gpoly_iterate (P : Polynomial ℝ) (b : ℕ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Spaces.Zop^[b] (Work.FTS.CoercivityFix.E2Bound.gpoly P)) z
        = Work.FTS.CoercivityFix.E2Bound.gpoly
            (Work.FTS.CoercivityFix.E2Bound.Tmul^[b] P) z := by
  induction b with
  | zero => intro z hz; simp
  | succ b ih =>
    intro z hz
    have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
    have heq : (Work.Spaces.Zop^[b] (Work.FTS.CoercivityFix.E2Bound.gpoly P))
        =ᶠ[𝓝 z] Work.FTS.CoercivityFix.E2Bound.gpoly
            (Work.FTS.CoercivityFix.E2Bound.Tmul^[b] P) :=
      Filter.eventually_of_mem hmem (fun w hw => ih w hw)
    have hderiv : deriv (Work.Spaces.Zop^[b] (Work.FTS.CoercivityFix.E2Bound.gpoly P)) z
        = deriv (Work.FTS.CoercivityFix.E2Bound.gpoly
            (Work.FTS.CoercivityFix.E2Bound.Tmul^[b] P)) z := heq.deriv_eq
    rw [Function.iterate_succ_apply']
    rw [show Work.Spaces.Zop (Work.Spaces.Zop^[b] (Work.FTS.CoercivityFix.E2Bound.gpoly P)) z
        = Work.Spaces.Zop (Work.FTS.CoercivityFix.E2Bound.gpoly
            (Work.FTS.CoercivityFix.E2Bound.Tmul^[b] P)) z by
      simp only [Work.Spaces.Zop, hderiv]]
    rw [Work.FTS.CoercivityFix.E2Bound.Zop_gpoly_step
        (Work.FTS.CoercivityFix.E2Bound.Tmul^[b] P) hz]
    rw [Function.iterate_succ_apply']

end Work.FTS.CoercivityFix.E2Bound.SlotMul
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.E2Bound.zop_phi_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS.CoercivityFix.E2Bound

/-- Evaluating a polynomial at a point of `[-1,1]` is bounded by the sum of the absolute
values of its coefficients. -/
lemma poly_eval_abs_le (P : Polynomial ℝ) {y : ℝ} (hy : |y| ≤ 1) :
    |P.eval y| ≤ P.sum (fun _ a => |a|) := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc |∑ e ∈ P.support, P.coeff e * y ^ e|
      ≤ ∑ e ∈ P.support, |P.coeff e * y ^ e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ P.support, |P.coeff e| := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        rw [abs_mul, abs_pow]
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg y) hy)

/-- The intertwining identity: in the chart variable, `Zop` acts as `P ↦ ½(1 - X²)·P'`. -/
lemma Zop_gpoly (P : Polynomial ℝ) {z : ℝ} (hz : z ≠ -1) :
    Work.Spaces.Zop (gpoly P) z = gpoly (Tmul P) z := by
  have hz1 : z + 1 ≠ 0 := by intro h; exact hz (by linarith)
  have hzd : HasDerivAt zchart (2 / (z + 1) ^ 2) z := by
    change HasDerivAt (fun w : ℝ => (w - 1) / (w + 1)) (2 / (z + 1) ^ 2) z
    have h1 : HasDerivAt (fun w : ℝ => w - 1) 1 z := (hasDerivAt_id z).sub_const 1
    have h2 : HasDerivAt (fun w : ℝ => w + 1) 1 z := (hasDerivAt_id z).add_const 1
    have hdiv := h1.div h2 hz1
    have hval : (1 * (z + 1) - (z - 1) * 1) / (z + 1) ^ 2 = 2 / (z + 1) ^ 2 := by ring
    rw [hval] at hdiv
    exact hdiv
  have hcomp : HasDerivAt (fun w => P.eval (zchart w))
      (P.derivative.eval (zchart z) * (2 / (z + 1) ^ 2)) z :=
    (Polynomial.hasDerivAt P (zchart z)).comp z hzd
  rw [Work.Spaces.Zop]
  change z * deriv (fun w => P.eval (zchart w)) z = (Tmul P).eval (zchart z)
  rw [hcomp.deriv]
  simp only [Tmul, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  have hkey : z * (2 / (z + 1) ^ 2) = (1 - zchart z ^ 2) / 2 := by
    rw [zchart, div_pow]
    field_simp
    ring
  calc z * (P.derivative.eval (zchart z) * (2 / (z + 1) ^ 2))
      = P.derivative.eval (zchart z) * (z * (2 / (z + 1) ^ 2)) := by ring
    _ = P.derivative.eval (zchart z) * ((1 - zchart z ^ 2) / 2) := by rw [hkey]
    _ = 1 / 2 * (1 - zchart z ^ 2) * P.derivative.eval (zchart z) := by ring

/-- The base case: `φ(z) = z/(1+z)²` is the chart-side evaluation of `Pphi = ¼(1 - X²)`. -/
lemma gpoly_Pphi {z : ℝ} (hz : z ≠ -1) : gpoly Pphi z = z / (1 + z) ^ 2 := by
  have hz1 : z + 1 ≠ 0 := by intro h; exact hz (by linarith)
  simp only [gpoly, Pphi, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  rw [show z / (1 + z) ^ 2 = z / (z + 1) ^ 2 by ring]
  rw [zchart, div_pow]
  field_simp
  ring

/-- Every `Zop`-iterate of `φ` is the chart-side evaluation of the corresponding polynomial
iterate. -/
lemma Zop_iter_gpoly : ∀ (b : ℕ) (z : ℝ), 0 < z →
    Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z = gpoly (Tmul^[b] Pphi) z := by
  intro b
  induction b with
  | zero =>
      intro z hz
      simpa using (gpoly_Pphi (z := z) (zchart_ne_neg_one hz)).symm
  | succ b ih =>
      intro z hz
      have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
      have hev : Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) =ᶠ[𝓝 z]
          gpoly (Tmul^[b] Pphi) := by
        filter_upwards [hmem] with w hw
        exact ih w hw
      have hrec : z * deriv (gpoly (Tmul^[b] Pphi)) z = gpoly (Tmul (Tmul^[b] Pphi)) z := by
        simpa only [Work.Spaces.Zop] using Zop_gpoly (Tmul^[b] Pphi) (zchart_ne_neg_one hz)
      calc Work.Spaces.Zop^[b.succ] (fun z : ℝ => z / (1 + z) ^ 2) z
          = Work.Spaces.Zop (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2)) z :=
              congrFun (Function.iterate_succ_apply' Work.Spaces.Zop b _) z
        _ = z * deriv (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2)) z := rfl
        _ = z * deriv (gpoly (Tmul^[b] Pphi)) z := by rw [hev.deriv_eq]
        _ = gpoly (Tmul (Tmul^[b] Pphi)) z := hrec
        _ = gpoly (Tmul^[b.succ] Pphi) z :=
              congrArg (fun P => gpoly P z) (Function.iterate_succ_apply' Tmul b Pphi).symm

theorem zop_phi_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K := by
  have hbd : ∀ b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z →
      |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ C := by
    intro b
    refine ⟨(Tmul^[b] Pphi).sum (fun _ a => |a|), ?_, ?_⟩
    · rw [Polynomial.sum_def]
      exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
    · intro z hz
      rw [Zop_iter_gpoly b z hz]
      exact poly_eval_abs_le _ (abs_zchart_le_one hz)
  choose C hC using hbd
  refine ⟨∑ b ∈ Finset.range (n + 1), C b, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => (hC i).1)
  · intro b hb z hz
    have hbmem : b ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hb)
    have hle : C b ≤ ∑ i ∈ Finset.range (n + 1), C i :=
      Finset.single_le_sum (fun i _ => (hC i).1) hbmem
    exact le_trans ((hC b).2 z hz) hle

end Work.FTS.CoercivityFix.E2Bound
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.G1_endpoint_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

/-!
# The endpoint bound for the singular Green term `G1`

`G1 α m c z = z ^ (G1s α m) * G1A α m c z` with `G1s α m = -(2m+5)/α =: -a`, `a = G1a α m > 0`,
and `G1A α m c z = ∫_0^z c t t^{a-1} dt`.  This file proves the uniform endpoint bound

  `G1 α m c x ^ 2 / x ^ 3 ≤ G1CPhi α m c`  for every `0 < x < 1`,

with `G1CPhi α m c = G1C0 α m c ^ 2`, `G1C0 α m c = G1M0 c / 2 + 1/(2(2a+3))`,
`G1M0 c = ∫_{(0,1)} c z²/z⁴`.

Route (exactly the estimate recorded in the `G1_est` route comment): factor
`c t t^{a-1} = (c t / t²)·t^{a+1}` and apply Cauchy–Schwarz in `t` over `(0,x)`, bounding the
first factor by `G1M0 c` (monotonicity of the nonnegative integral) and evaluating the second,
`∫_0^x t^{2a+2} = x^{2a+3}/(2a+3)`.  This gives `G1A x² ≤ G1M0 c · x^{2a+3}/(2a+3)`, hence
(dividing by the positive `x^{2a+3}`) `G1 x²/x³ ≤ G1M0 c/(2a+3)`.  Finally
`G1M0 c/(2a+3) ≤ (G1M0 c/2 + 1/(2(2a+3)))²` is the elementary AM–GM identity
`4·(A/2)·(1/(2b)) = A/b` with `b = 2a+3` (equivalently `(A/2 - 1/(2b))² ≥ 0`).

The three ingredients are the lemmas
`Work.FTS.EllExist.Honesty.G1Endpoint.g1A_sq_le`,
`...G1_sq_div_cube_le` and `...g1_endpoint_const`.
-/

/-- **Endpoint bound for the singular Green term `G1`.**  For `0 < x < 1` the weighted square
`G1 x²/x³` is bounded by the constant `G1CPhi α m c`, uniformly in `x` (this is the `x → 0`
endpoint term of the energy identity `G1_energy_identity`). -/
theorem G1_endpoint_bound {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ∀ x : ℝ, 0 < x → x < 1 →
      Work.FTS.EllExist.Honesty.G1 α m c x ^ 2 / x ^ 3
        ≤ Work.FTS.EllExist.Honesty.G1CPhi α m c := by
  intro x hx0 hx1
  -- `b := 2a + 3 > 0`
  have hb : (0 : ℝ) < 2 * G1a α m + 3 := by
    have := G1a_pos hα m
    linarith
  -- Cauchy–Schwarz: `G1A x² ≤ G1M0 c · x^{2a+3}/(2a+3)`.
  have hcs := G1Endpoint.g1A_sq_le hα m hc h0 x hx0 hx1
  -- Scaling by `x^{-2a-3}`: `G1 x²/x³ ≤ G1M0 c/(2a+3)`.
  have hscale := G1Endpoint.G1_sq_div_cube_le (α := α) m (c := c) hx0 hcs
  -- AM–GM: `A/b ≤ (A/2 + 1/(2b))²`.
  have hconst := G1Endpoint.g1_endpoint_const (A := G1M0 c) (b := 2 * G1a α m + 3)
    (G1M0_nonneg c) hb
  rw [G1CPhi, G1C0]
  linarith

end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.G1_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open MeasureTheory Set

/-- `G1 α m c = z ↦ z^{s⁻} · G1A α m c z` is differentiable on `(0,∞)` with derivative
`(-a·G1 z + c z)/z`, `a = G1a α m = -G1s α m`: the product rule for `z^{s⁻} · ∫_0^z c t t^{a-1}dt`
gives `s⁻ z^{s⁻-1}A(z) + z^{s⁻}c z z^{a-1} = (s⁻ z^{s⁻}A(z) + c z)/z`, and `s⁻ = -a`. -/
theorem G1_hasDerivAt {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.FTS.EllExist.Honesty.G1 α m c)
        ((-(Work.FTS.EllExist.Honesty.G1a α m) * Work.FTS.EllExist.Honesty.G1 α m c z + c z) / z) z := by
  intro z hz
  have hzpos : 0 < z := hz
  have hz0 : z ≠ 0 := ne_of_gt hzpos
  have hInt : IntegrableOn (G1f α m c) (Set.Ioo 0 1) := G1f_integrableOn hα m hc h0
  have hA : HasDerivAt (G1A α m c) (G1f α m c z) z := G1A_hasDerivAt hc hInt z hz
  have hpow : HasDerivAt (fun w : ℝ => w ^ (G1s α m)) (G1s α m * z ^ (G1s α m - 1)) z :=
    Real.hasDerivAt_rpow_const (x := z) (p := G1s α m) (Or.inl hz0)
  have hprod : HasDerivAt (fun w : ℝ => w ^ (G1s α m) * G1A α m c w)
      ((G1s α m * z ^ (G1s α m - 1)) * G1A α m c z + z ^ (G1s α m) * G1f α m c z) z :=
    hpow.mul hA
  change HasDerivAt (fun w : ℝ => w ^ (G1s α m) * G1A α m c w)
    ((-(G1a α m) * (z ^ (G1s α m) * G1A α m c z) + c z) / z) z
  have hgf : G1f α m c z = c z * z ^ (G1a α m - 1) := by simp only [G1f, G1a]
  have h1 : z ^ (G1s α m - 1) = z ^ (G1s α m) / z := Real.rpow_sub_one hz0 (G1s α m)
  have h2 : z ^ (G1s α m) * z ^ (G1a α m - 1) = z⁻¹ := by
    rw [← Real.rpow_add (x := z) hzpos]
    have hsum : G1s α m + (G1a α m - 1) = -1 := by rw [G1s_eq_neg_G1a]; ring
    simp only [hsum, Real.rpow_neg_one]
  have h3 : z ^ (G1s α m) * (c z * z ^ (G1a α m - 1))
      = c z * (z ^ (G1s α m) * z ^ (G1a α m - 1)) := by ring
  have heq : (G1s α m * z ^ (G1s α m - 1)) * G1A α m c z + z ^ (G1s α m) * G1f α m c z
      = (-(G1a α m) * (z ^ (G1s α m) * G1A α m c z) + c z) / z := by
    rw [h1, hgf, h3, h2, G1s_eq_neg_G1a, div_eq_mul_inv]
    ring
  rw [← heq]
  exact hprod

end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.dthRecOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

/-!
# The recursion for the angular quotient, with only interior smoothness

`Work.Elliptic.DivSinRec` proves the recursion

`D_θ^i (h / sin 2θ) = D_θ^{i-1} h' - ∑_{l<i} C(i-1,l) · D_θ^{i-1-l}(2 cos 2θ) · D_θ^l (h/sin 2θ)`

for a slice `h` that is *analytic on an open neighbourhood* of `[0, π/2]` and vanishes at the two
endpoints.  That is more than the identity needs: it is a purely local consequence of the
first-order identity `D_θ (h / sin 2θ) = h' - (2 cos 2θ)·(h / sin 2θ)` on the open interval
`(0, π/2)` together with the Leibniz rule for the derivation `D_θ = sin(2θ) ∂_θ`.

The Leibniz rule for iterates of a derivation is supplied by the abstract machinery
`Work.Spaces.DerivLike` / `Work.Spaces.FunClass`, but the instances shipped with it
(`Work.Spaces.Lop_iter_mul_eqOn`, `Work.Spaces.DthIter_mul`) ask for `ContDiffOn ℝ ⊤`, i.e.
*analyticity*.  Here we instantiate the same machinery with the honest `C^∞`-on-an-open-set class
(`SmoothOn`, phrased with the finite orders `n : ℕ`), which is what the hypothesis
`ContDiffOn ℝ (↑(⊤ : ℕ∞))` provides, and redo the short argument of `DivSinRec`.
-/

/-- The class of functions that are `C^∞` on the open set `U`, expressed with the finite orders
`n : ℕ` so that it can be consumed by `Work.Spaces.FunClass` / `Work.Spaces.DerivLike`. -/
private def SmoothOn (U : Set ℝ) : (ℝ → ℝ) → Prop :=
  fun u => ∀ n : ℕ, ContDiffOn ℝ (n : WithTop ℕ∞) u U

/-- `SmoothOn U` is closed under `+`, `*` and scalar multiplication. -/
private lemma smoothOn_funClass (U : Set ℝ) : Work.Spaces.FunClass (SmoothOn U) where
  add := fun A B hA hB n => (hA n).add (hB n)
  mul := fun A B hA hB n => (hA n).mul (hB n)
  smul := fun c A hA n => by
    simpa only [Pi.smul_apply, smul_eq_mul] using (hA n).const_smul c

/-- `Work.Spaces.Lop = D_θ = sin(2θ) ∂_θ` is a derivation-like operator for the honest `C^∞`
class on an open set. -/
private lemma lop_derivLike_smooth (U : Set ℝ) (hU : IsOpen U) :
    Work.Spaces.DerivLike U (SmoothOn U) Work.Spaces.Lop where
  add := by
    intro A B hA hB θ hθ
    have dA : DifferentiableAt ℝ A θ :=
      ((hA 1).contDiffAt (hU.mem_nhds hθ)).differentiableAt (by norm_num)
    have dB : DifferentiableAt ℝ B θ :=
      ((hB 1).contDiffAt (hU.mem_nhds hθ)).differentiableAt (by norm_num)
    show Real.sin (2 * θ) * deriv (A + B) θ
        = Real.sin (2 * θ) * deriv A θ + Real.sin (2 * θ) * deriv B θ
    rw [show deriv (A + B) θ = deriv A θ + deriv B θ from by
      simpa only [Pi.add_apply] using deriv_add dA dB]
    ring
  mul := by
    intro A B hA hB θ hθ
    exact Work.Spaces.Lop_mul A B θ
      (((hA 1).contDiffAt (hU.mem_nhds hθ)).differentiableAt (by norm_num))
      (((hB 1).contDiffAt (hU.mem_nhds hθ)).differentiableAt (by norm_num))
  congr := by
    intro A B hAB θ hθ
    have hev : A =ᶠ[nhds θ] B := by
      filter_upwards [hU.mem_nhds hθ] with x hx
      exact hAB hx
    show Real.sin (2 * θ) * deriv A θ = Real.sin (2 * θ) * deriv B θ
    rw [hev.deriv_eq]
  preserve := by
    intro A hA n
    have h1 : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) A U := hA (n + 1)
    have hcast : (n : WithTop ℕ∞) + 1 ≤ ((n + 1 : ℕ) : WithTop ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_one]
    have hderiv := h1.deriv_of_isOpen hU hcast
    have hsin : ContDiffOn ℝ (n : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) U := by fun_prop
    exact hsin.mul hderiv
  smul := by
    intro c A hA θ hθ
    show Real.sin (2 * θ) * deriv (fun p => c * A p) θ = c * (Real.sin (2 * θ) * deriv A θ)
    rw [deriv_const_mul_field c]
    ring

/-- Linearity of the iterates of `D_θ` on `C^∞`-functions of an open set. -/
private lemma lop_iter_sub_smooth {U : Set ℝ} (hU : IsOpen U) {u v : ℝ → ℝ}
    (hu : SmoothOn U u) (hv : SmoothOn U v) (n : ℕ) :
    Set.EqOn (Work.Spaces.Lop^[n] (u - v))
      (fun θ => Work.Spaces.Lop^[n] u θ - Work.Spaces.Lop^[n] v θ) U := by
  have hD := lop_derivLike_smooth U hU
  have hP := smoothOn_funClass U
  have hw : SmoothOn U (fun p => (-1 : ℝ) * v p) := hP.smul (-1) v hv
  have h1 := Work.Spaces.DerivLike.iterate_add hD n hu hw
  have h2 := Work.Spaces.DerivLike.iterate_smul hD n (-1) hv
  have hfun : (u - v) = (u + fun p => (-1 : ℝ) * v p) := by
    funext p; simp only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, neg_one_mul]
  rw [hfun]
  refine h1.trans ?_
  intro θ hθ
  have h2θ := h2 hθ
  simp only [Pi.add_apply]
  rw [h2θ]
  ring

/-- The iterated Leibniz rule for `D_θ` on `C^∞`-functions of an open set. -/
private lemma Lop_iter_mul_smooth (u v : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hu : SmoothOn U u) (hv : SmoothOn U v) (j : ℕ) :
    Set.EqOn (Work.Spaces.Lop^[j] (u * v))
      (fun θ => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j - a] v θ)) U :=
  Work.Spaces.DerivLike.iterate_mul (lop_derivLike_smooth U hU) (smoothOn_funClass U) j hu hv

/-- `D_θ(h / sin 2θ) = h' - (2 cos 2θ)·(h / sin 2θ)` on the open set `U`, for `h` merely `C^∞`
there (in particular no analyticity and no endpoint information is needed). -/
private lemma Lop_SinQ_eqOn_smooth {U : Set ℝ} (hU : IsOpen U) {h : ℝ → ℝ}
    (hh : SmoothOn U h) (hne : ∀ x ∈ U, Real.sin (2 * x) ≠ 0) :
    Set.EqOn (Work.Spaces.Lop (Work.Elliptic.SinQ h))
      (fun θ => deriv h θ - (fun x : ℝ => 2 * Real.cos (2 * x)) θ * Work.Elliptic.SinQ h θ) U := by
  intro θ hθ
  have h1 : ContDiffOn ℝ (((1 : ℕ)) : WithTop ℕ∞) h U := hh 1
  have hsin1 : ContDiffOn ℝ (((1 : ℕ)) : WithTop ℕ∞) (fun x : ℝ => Real.sin (2 * x)) U := by
    fun_prop
  have hg1 : ContDiffOn ℝ (((1 : ℕ)) : WithTop ℕ∞) (Work.Elliptic.SinQ h) U := by
    show ContDiffOn ℝ (((1 : ℕ)) : WithTop ℕ∞) (fun x => h x / Real.sin (2 * x)) U
    exact h1.div hsin1 hne
  have hneθ : ∀ᶠ x in nhds θ, Real.sin (2 * x) ≠ 0 := by
    have hc : ContinuousAt (fun x : ℝ => Real.sin (2 * x)) θ := by fun_prop
    exact hc.eventually_ne (hne θ hθ)
  have heq : (fun x : ℝ => Real.sin (2 * x) * Work.Elliptic.SinQ h x) =ᶠ[nhds θ] h := by
    filter_upwards [hneθ] with x hx
    simp only [Work.Elliptic.SinQ]
    rw [mul_comm, div_mul_cancel₀ _ hx]
  have hdeq : deriv (fun x : ℝ => Real.sin (2 * x) * Work.Elliptic.SinQ h x) θ = deriv h θ :=
    heq.deriv_eq
  have dsin : DifferentiableAt ℝ (fun x : ℝ => Real.sin (2 * x)) θ := by fun_prop
  have dg : DifferentiableAt ℝ (Work.Elliptic.SinQ h) θ :=
    (hg1.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by norm_num)
  have hprod : deriv (fun x : ℝ => Real.sin (2 * x) * Work.Elliptic.SinQ h x) θ
      = deriv (fun x : ℝ => Real.sin (2 * x)) θ * Work.Elliptic.SinQ h θ
        + Real.sin (2 * θ) * deriv (Work.Elliptic.SinQ h) θ :=
    deriv_mul dsin dg
  rw [Work.Elliptic.deriv_sin_two θ] at hprod
  show Real.sin (2 * θ) * deriv (Work.Elliptic.SinQ h) θ
      = deriv h θ - 2 * Real.cos (2 * θ) * Work.Elliptic.SinQ h θ
  rw [← hdeq, hprod]
  ring

theorem dthRecOpen (i : ℕ) (hi : 1 ≤ i) (h : ℝ → ℝ)
    (hsm : ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ =
        Work.Elliptic.Dth1Iter (i - 1) (deriv h) θ -
          ∑ l ∈ Finset.range i, (Nat.choose (i - 1) l : ℝ) *
            (Work.Elliptic.Dth1Iter (i - 1 - l) (fun θ => 2 * Real.cos (2 * θ)) θ) *
            (Work.Elliptic.Dth1Iter l (Work.Elliptic.SinQ h) θ) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  intro θ hθ
  simp only [Nat.add_sub_cancel]
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hne : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * x) ≠ 0 := fun x hx =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos]))
  have hsmU : SmoothOn (Set.Ioo (0 : ℝ) (Real.pi / 2)) h := fun n =>
    hsm.of_le (by exact_mod_cast le_top)
  have hgU : SmoothOn (Set.Ioo (0 : ℝ) (Real.pi / 2)) (Work.Elliptic.SinQ h) := fun n => by
    show ContDiffOn ℝ (n : WithTop ℕ∞) (fun x => h x / Real.sin (2 * x))
      (Set.Ioo (0 : ℝ) (Real.pi / 2))
    exact (hsmU n).div (by fun_prop) hne
  have hφU : SmoothOn (Set.Ioo (0 : ℝ) (Real.pi / 2)) (fun x : ℝ => 2 * Real.cos (2 * x)) :=
    fun n => by fun_prop
  have hderU : SmoothOn (Set.Ioo (0 : ℝ) (Real.pi / 2)) (deriv h) := fun n =>
    (hsmU (n + 1)).deriv_of_isOpen isOpen_Ioo (by rw [Nat.cast_add, Nat.cast_one])
  have hφgU : SmoothOn (Set.Ioo (0 : ℝ) (Real.pi / 2))
      ((fun x : ℝ => 2 * Real.cos (2 * x)) * Work.Elliptic.SinQ h) := fun n =>
    (hφU n).mul (hgU n)
  have hD := lop_derivLike_smooth (Set.Ioo (0 : ℝ) (Real.pi / 2)) hU
  have hEq : Set.EqOn (Work.Spaces.Lop (Work.Elliptic.SinQ h))
      (fun θ => deriv h θ - (fun x : ℝ => 2 * Real.cos (2 * x)) θ * Work.Elliptic.SinQ h θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := Lop_SinQ_eqOn_smooth hU hsmU hne
  have h1 : Work.Spaces.Lop^[j + 1] (Work.Elliptic.SinQ h) θ
      = Work.Spaces.Lop^[j]
          (fun x : ℝ => deriv h x - (fun x : ℝ => 2 * Real.cos (2 * x)) x * Work.Elliptic.SinQ h x)
          θ := by
    rw [Function.iterate_succ_apply]
    exact (Work.Spaces.DerivLike.iterate_congr hD j hEq) hθ
  have h2 : Work.Spaces.Lop^[j]
        (fun x : ℝ => deriv h x - (fun x : ℝ => 2 * Real.cos (2 * x)) x * Work.Elliptic.SinQ h x) θ
      = Work.Spaces.Lop^[j] (deriv h) θ
        - Work.Spaces.Lop^[j]
            ((fun x : ℝ => 2 * Real.cos (2 * x)) * Work.Elliptic.SinQ h) θ :=
    (lop_iter_sub_smooth hU hderU hφgU j) hθ
  have h3 : Work.Spaces.Lop^[j]
        ((fun x : ℝ => 2 * Real.cos (2 * x)) * Work.Elliptic.SinQ h) θ
      = ∑ a ∈ Finset.range (j + 1), (Nat.choose j a : ℝ) *
          (Work.Spaces.Lop^[a] (fun x : ℝ => 2 * Real.cos (2 * x)) θ *
           Work.Spaces.Lop^[j - a] (Work.Elliptic.SinQ h) θ) :=
    (Lop_iter_mul_smooth (fun x : ℝ => 2 * Real.cos (2 * x)) (Work.Elliptic.SinQ h)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) hU hφU hgU j) hθ
  have hstep : Work.Spaces.Lop^[j + 1] (Work.Elliptic.SinQ h) θ
      = Work.Spaces.Lop^[j] (deriv h) θ
        - ∑ a ∈ Finset.range (j + 1), (Nat.choose j a : ℝ) *
            (Work.Spaces.Lop^[a] (fun x : ℝ => 2 * Real.cos (2 * x)) θ *
             Work.Spaces.Lop^[j - a] (Work.Elliptic.SinQ h) θ) := by
    rw [h1, h2, h3]
  have hsum : (∑ l ∈ Finset.range (j + 1), (Nat.choose j l : ℝ) *
        Work.Spaces.Lop^[j - l] (fun x : ℝ => 2 * Real.cos (2 * x)) θ *
        Work.Spaces.Lop^[l] (Work.Elliptic.SinQ h) θ)
      = ∑ a ∈ Finset.range (j + 1), (Nat.choose j a : ℝ) *
        (Work.Spaces.Lop^[a] (fun x : ℝ => 2 * Real.cos (2 * x)) θ *
         Work.Spaces.Lop^[j - a] (Work.Elliptic.SinQ h) θ) := by
    rw [← Finset.sum_range_reflect
      (fun a : ℕ => (Nat.choose j a : ℝ) *
        (Work.Spaces.Lop^[a] (fun x : ℝ => 2 * Real.cos (2 * x)) θ *
         Work.Spaces.Lop^[j - a] (Work.Elliptic.SinQ h) θ)) (j + 1)]
    apply Finset.sum_congr rfl
    intro l hl
    have hlj : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hsub : (j + 1) - 1 - l = j - l := by omega
    rw [hsub, Nat.sub_sub_self hlj, Nat.choose_symm hlj]
    ring
  simp only [Work.Elliptic.Dth1Iter_eq_iterate_Lop]
  rw [hstep, hsum]

end

end Work.FTS.EllSol.PkgK5
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.SRSAux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false



end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.SRSAux.TrigCompare =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak.SRSAux


end Work.FTS.EllipticEst.AngAWeak.SRSAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.SliceGronwallDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false










end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.ibp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

/-- Hints: with `V = angV h = G/sin 2θ` and `G = angG h`, `hg` gives `V' = h - 2 cot(2θ) V`,
hence `(V h)' = h² + V (h' - 2 cot(2θ) h)`: the integrand
`F θ = h θ² + V θ (deriv h θ - 2 cot(2θ) h θ)` is the derivative on `(0,π/2)` of
`angPhiC h = V · h`, which tends to `0` at both endpoints by `squeeze_zero'` (`hCg` gives
`|V| ≤ C sin²2θ` and `hbdd` gives `|h| ≤ C sin 2θ`, so `|V h| ≤ C² sin³2θ`).  `F` is
continuous on `Ioo 0 (π/2)` and bounded there (`hbdd'` bounds `h'`), so it is
`IntervalIntegrable` on `0..π/2`; conclude with
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` and the set-integral conversions.

The two analytic inputs are proved in the sibling files `AngGap/angPhiC_tendsto_zero`
(the vanishing of `angPhiC h` at both endpoints) and
`AngGap/angPhiC_integrand_intervalIntegrable` (interval integrability of `F`, of `h²` and
of `V · Q`). -/
theorem ibp (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (Work.FTS.EllipticEst.AngGap.angG h)
        (h θ * Real.sin (2 * θ)) θ)
    (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hbdd' : ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ C)
    (hCg : ∀ θ ∈ Set.Icc 0 (π / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2)
      = - (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngGap.angV h θ
            * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) := by
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  -- ## the two analytic inputs
  obtain ⟨hintF, hintH, hintV⟩ :=
    angPhiC_integrand_intervalIntegrable h hh hg C hC hbdd hbdd' hCg
  obtain ⟨htend0, htendπ⟩ := angPhiC_tendsto_zero h C hC hbdd hCg
  -- ## derivative of the primitive `angPhiC h = V · h` on `(0,π/2)`
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), HasDerivAt (angPhiC h)
      ((h θ) ^ 2 + angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) θ := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs
    have hG : HasDerivAt (angG h) (h θ * Real.sin (2 * θ)) θ := hg θ hθ
    have hH : HasDerivAt h (deriv h θ) θ :=
      ((hh.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)).differentiableAt (by norm_num)).hasDerivAt
    have hs' : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
      have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 θ := by
        simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
      simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    have hmain := HasDerivAt.div (hG.mul hH) hs' hsne
    have hfun : angPhiC h = (fun θ => angG h θ * h θ) / (fun θ : ℝ => Real.sin (2 * θ)) := by
      funext θ; simp only [angPhiC, angV, Pi.div_apply]; ring
    rw [hfun]
    refine hmain.congr_deriv ?_
    simp only [angV, Pi.mul_apply]
    rw [Real.cot_eq_cos_div_sin]
    field_simp
    ring_nf
  -- ## the fundamental theorem of calculus
  have hFTC : (∫ θ in (0 : ℝ)..(π / 2),
      ((h θ) ^ 2 + angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ))) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi2 hderiv hintF
      htend0 htendπ
    simpa using h
  have hsplit : (∫ θ in (0 : ℝ)..(π / 2),
        ((h θ) ^ 2 + angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)))
      = (∫ θ in (0 : ℝ)..(π / 2), (h θ) ^ 2)
        + (∫ θ in (0 : ℝ)..(π / 2), angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) :=
    intervalIntegral.integral_add hintH hintV
  have hmain : (∫ θ in (0 : ℝ)..(π / 2), (h θ) ^ 2)
      = - (∫ θ in (0 : ℝ)..(π / 2), angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) := by
    linarith
  -- ## transfer to the set integral over `Iθ`
  have hIθ : ∀ u : ℝ → ℝ, ∫ θ in Work.Spaces.Iθ, u θ = ∫ θ in (0 : ℝ)..(π / 2), u θ := by
    intro u
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi2.le]
  rw [hIθ (fun θ => (h θ) ^ 2),
    hIθ (fun θ => angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ))]
  simpa using hmain

end Work.FTS.EllipticEst.AngGap
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.Slice9PoincareDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.P9

set_option autoImplicit false

/-! ## Vocabulary for the constrained slice Poincaré inequality (`slicePoincare9_fts`)

The target is: for `f : ℝ → ℝ` of class `C²` on `[0,π/2]` with `f 0 = f (π/2) = 0` and
`∫_{Iθ} f θ · sinθcos²θ dθ = 0`, one has `9 ∫_{Iθ} f² ≤ ∫_{Iθ} (f')²`.

The route is the projection of `f` on the kernel direction `s2 θ = sin 2θ` of `-∂_θθ`:
`coeffA f = (4/π) ∫_{Iθ} f · s2` is the first sine coefficient (so that
`∫_{Iθ} f · s2 = (π/4) coeffA f`), and `residG f = f - coeffA f · s2` is the residual, which is
orthogonal to `s2`.  The constraint `∫_{Iθ} f · sinθcos²θ = 0` then bounds the coefficient by the
residual, and the gap-Wirtinger inequality `16 ∫ g² ≤ ∫ (g')²` on the orthogonal complement
closes.

Two technical points are solved once and for all here.

* The global `deriv F` of a function that is only `C²` *on the closed interval* is not
  continuous on `[0,π/2]` (its values at `0` and `π/2` depend on the values of `f` outside the
  interval), so `∫_{Iθ} (deriv F)²` is not obviously honest and the product rule for `deriv` is
  not available at the endpoints.  We therefore work with `w F = derivWithin F [0,π/2]`, which
  *is* continuous on the compact `[0,π/2]` as soon as `F` is `C²` there, and which agrees with
  `deriv F` almost everywhere on `Iθ` (`w_ae_eq_deriv` — true for every `F`).
* The elementary angular integrals (`∫ s2² = π/4`, `∫ sin²θcos⁴θ = π/32`,
  `∫ sinθcos²θ · s2 = 4/15`, `∫ (deriv s2)² = π`) are extracted from
  `Work.FTS.EllipticEst.ang_integrals`. -/

/-- `sin 2θ`, the first Dirichlet mode on `[0,π/2]` and the kernel direction of the `α = 0`
angular operator `L₀ = -∂_θθ + ∂_θ(tan θ ·) - 6` on `[0,π/2]`. -/
def s2 (θ : ℝ) : ℝ := Real.sin (2 * θ)

/-- The derivative of `F` *within* the closed interval `[0,π/2]`. -/
def w (F : ℝ → ℝ) : ℝ → ℝ := derivWithin F (Set.Icc 0 (π / 2))

/-- The first sine coefficient of `f`, `coeffA f = (4/π) ∫_{Iθ} f θ sin 2θ dθ`, normalised so
that `∫_{Iθ} f · sin2θ = (π/4) · coeffA f`. -/
def coeffA (f : ℝ → ℝ) : ℝ := (4 / π) * ∫ θ in Work.Spaces.Iθ, f θ * s2 θ

/-- The residual `residG f = f - coeffA f · sin 2θ`, orthogonal to `sin 2θ` in `L²(Iθ)`. -/
def residG (f : ℝ → ℝ) : ℝ → ℝ := fun θ => f θ - coeffA f * s2 θ

/-! ## Elementary facts about integrals over `Iθ` -/

/-- `∫_{Iθ}` is the interval integral over `0..π/2`. -/
theorem Iθ_eq_interval (G : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, G θ) = ∫ θ in (0 : ℝ)..(π / 2), G θ := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]

/-- `volume.real Iθ = π/2`. -/
theorem real_volume_Iθ : (volume.real Work.Spaces.Iθ) = π / 2 := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl, MeasureTheory.Measure.real,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]

/-- The interval `(0,π/2)` and `Iθ` carry the same restricted measure. -/
theorem restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- Rewriting an integral over `Iθ` under a pointwise equality. -/
theorem setIntegral_Iθ_congr {f g : ℝ → ℝ} (h : ∀ θ ∈ Work.Spaces.Iθ, f θ = g θ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in Work.Spaces.Iθ, g θ :=
  setIntegral_congr_fun measurableSet_Icc h

/-- A function continuous on the compact `Iθ` is integrable there. -/
theorem integrableOn_Iθ_of_continuousOn {g : ℝ → ℝ} (hg : ContinuousOn g Work.Spaces.Iθ) :
    IntegrableOn g Work.Spaces.Iθ :=
  hg.integrableOn_compact isCompact_Icc

/-- A globally continuous function is integrable on `Iθ`. -/
theorem integrableOn_Iθ_of_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    IntegrableOn g Work.Spaces.Iθ :=
  integrableOn_Iθ_of_continuousOn hg.continuousOn

/-! ## Continuity and differentiability of the elementary functions -/

theorem continuous_s2 : Continuous s2 := by unfold s2; fun_prop

theorem differentiableAt_s2 (θ : ℝ) : DifferentiableAt ℝ s2 θ := by unfold s2; fun_prop

theorem contDiff_s2 : ContDiff ℝ 2 s2 := by unfold s2; fun_prop

theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2; fun_prop

theorem abs_sinCos2_le_one (θ : ℝ) : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  have h2 : (Real.cos θ) ^ 2 ≤ 1 := by
    nlinarith [Real.abs_cos_le_one θ, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  have h1 : |Real.sin θ * Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ))]
    nlinarith [Real.abs_sin_le_one θ, abs_nonneg (Real.sin θ)]
  simpa [Work.Elliptic.sinCos2] using h1

/-! ## The elementary angular integrals -/

/-- `∫_{Iθ} sin²2θ = π/4`. -/
theorem integral_s2_sq : (∫ θ in Work.Spaces.Iθ, (s2 θ) ^ 2) = π / 4 := by
  simpa [s2] using Work.FTS.EllipticEst.ang_integrals.1

/-- `∫_{Iθ} sin²θcos⁴θ = π/32`. -/
theorem integral_sinCos2_sq :
    (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2) = π / 32 :=
  Work.FTS.EllipticEst.ang_integrals.2.1

/-- `∫_{Iθ} sinθcos²θ · sin2θ = 4/15`. -/
theorem integral_sinCos2_mul_s2 :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * s2 θ) = 4 / 15 := by
  simpa [s2] using Work.FTS.EllipticEst.ang_integrals.2.2.1

/-- `deriv (sin 2θ) = 2 cos 2θ`. -/
theorem deriv_s2 : deriv s2 = fun θ : ℝ => 2 * Real.cos (2 * θ) := by
  funext θ
  have h1 : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  rw [show s2 = fun θ : ℝ => Real.sin (2 * θ) from rfl, h2.deriv]
  ring

/-- `∫_{Iθ} (deriv sin2θ)² = ∫_{Iθ} 4cos²2θ = π`. -/
theorem integral_deriv_s2_sq : (∫ θ in Work.Spaces.Iθ, (deriv s2 θ) ^ 2) = π := by
  have hpt : ∀ θ : ℝ, (deriv s2 θ) ^ 2 = 4 - 4 * (s2 θ) ^ 2 := by
    intro θ
    rw [funext_iff.mp deriv_s2 θ]
    simp only [s2]
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ)]
  have hsplit : (∫ θ in Work.Spaces.Iθ, ((4 : ℝ) - 4 * (s2 θ) ^ 2))
      = (∫ θ in Work.Spaces.Iθ, (4 : ℝ)) - ∫ θ in Work.Spaces.Iθ, 4 * (s2 θ) ^ 2 :=
    MeasureTheory.integral_sub (f := fun _ : ℝ => (4 : ℝ))
      (g := fun θ : ℝ => 4 * (s2 θ) ^ 2)
      (integrableOn_Iθ_of_continuous continuous_const)
      (integrableOn_Iθ_of_continuous (continuous_const.mul (continuous_s2.pow 2)))
  calc (∫ θ in Work.Spaces.Iθ, (deriv s2 θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, ((4 : ℝ) - 4 * (s2 θ) ^ 2) :=
        setIntegral_Iθ_congr (fun θ _ => hpt θ)
    _ = (∫ θ in Work.Spaces.Iθ, (4 : ℝ)) - ∫ θ in Work.Spaces.Iθ, 4 * (s2 θ) ^ 2 := hsplit
    _ = 4 * (π / 2) - 4 * (π / 4) := by
        rw [MeasureTheory.setIntegral_const, real_volume_Iθ,
          MeasureTheory.integral_const_mul, integral_s2_sq]
        simp only [smul_eq_mul]
        ring
    _ = π := by ring

/-! ## The derivative `w` within the closed interval -/

/-- For every `F`, the derivative within `[0,π/2]` agrees with the global derivative almost
everywhere on `Iθ` (they can differ only at the two endpoints). -/
theorem w_ae_eq_deriv (F : ℝ → ℝ) :
    w F =ᵐ[volume.restrict Work.Spaces.Iθ] deriv F := by
  rw [← restrict_Ioo_eq_restrict_Iθ]
  refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  exact derivWithin_of_mem_nhds
    (Icc_mem_nhds (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))

/-- `w F` is continuous on `[0,π/2]` when `F` is `C²` there. -/
theorem continuousOn_w {F : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Set.Icc 0 (π / 2))) :
    ContinuousOn (w F) (Set.Icc 0 (π / 2)) :=
  hF.continuousOn_derivWithin (uniqueDiffOn_Icc (by positivity)) (by norm_num)

theorem integrableOn_w_sq {F : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Set.Icc 0 (π / 2))) :
    IntegrableOn (fun θ : ℝ => (w F θ) ^ 2) Work.Spaces.Iθ :=
  integrableOn_Iθ_of_continuousOn ((continuousOn_w hF).pow 2)


/-- `∫ (w F)² = ∫ (deriv F)²`: the two integrands agree a.e. on `Iθ`. -/
theorem integral_w_sq_eq_integral_deriv_sq (F : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, (w F θ) ^ 2) = ∫ θ in Work.Spaces.Iθ, (deriv F θ) ^ 2 := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [w_ae_eq_deriv F] with θ hθ
  rw [hθ]

/-- `∫ (w F · w G) = ∫ (deriv F · deriv G)`: the two integrands agree a.e. on `Iθ`. -/
theorem integral_w_mul_eq (F G : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, w F θ * w G θ)
      = ∫ θ in Work.Spaces.Iθ, deriv F θ * deriv G θ := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [w_ae_eq_deriv F, w_ae_eq_deriv G] with θ h1 h2
  rw [h1, h2]

/-- The derivative within `[0,π/2]` of `F - c · sin 2θ`. -/
theorem w_sub_const_mul {F : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Set.Icc 0 (π / 2))) (c : ℝ) :
    ∀ θ ∈ Set.Icc 0 (π / 2),
      w (fun θ' : ℝ => F θ' - c * s2 θ') θ = w F θ - c * w s2 θ := by
  intro θ hθ
  have hdF : DifferentiableWithinAt ℝ F (Set.Icc 0 (π / 2)) θ :=
    (hF.differentiableOn (by norm_num)) θ hθ
  have hds2 : DifferentiableWithinAt ℝ s2 (Set.Icc 0 (π / 2)) θ :=
    (differentiableAt_s2 θ).differentiableWithinAt
  have hdG : DifferentiableWithinAt ℝ (fun θ' : ℝ => c * s2 θ') (Set.Icc 0 (π / 2)) θ :=
    hds2.const_mul c
  have hfun : (fun θ' : ℝ => F θ' - c * s2 θ') = F - (fun θ' : ℝ => c * s2 θ') := by
    funext θ'; simp
  simp only [w, hfun]
  rw [derivWithin_sub hdF hdG, derivWithin_const_mul c hds2]

end Work.FTS.EllipticEst.P9
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.L12Aux.Fstar_L2_of_EllHyp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.L12Aux

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The open quadrant and the neighbourhood of `SmoothNbhd` -/

/-- The open quadrant `(0,∞) × (0,π/2)` on which the smoothness of `Ψ` is used
(the analytic content of the estimates lives here; the two boundary lines
`θ = 0`, `θ = π/2` are null for `volume.restrict Iθ`). -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

/-- The open neighbourhood `(-1,∞) × (-1,π/2+1)` of the closed quadrant on which
`Work.Spaces.SmoothNbhd` is stated. -/
abbrev nbhQ : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)

/-- The open quadrant sits inside the neighbourhood of the smoothness class. -/
theorem Qd_subset_nbhQ : Qd ⊆ nbhQ :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))
    (Set.Ioo_subset_Ioo (by norm_num : (-1 : ℝ) ≤ 0)
      (by linarith [Real.pi_pos] : π / 2 ≤ π / 2 + 1))

/-- The open interval `(0,π/2)` and the closed interval `Iθ` carry the same restriction of
Lebesgue measure, since they differ by the two null points `0` and `π/2`. -/
theorem restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-! ## Domination of the unweighted square by the `ℋ^k`-integrand -/

/-- The radial weight is at least `1` on `(0,∞)`. -/
theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith

/-- Multiplying by the radial weight does not decrease a square: `g² ≤ (g·w)²` for `z > 0`. -/
theorem sq_le_sq_mul_w {g : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    (g z θ) ^ 2 ≤ (g z θ * Work.Spaces.w z) ^ 2 := by
  have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by
    have := one_le_w_of_pos hz; nlinarith
  calc (g z θ) ^ 2 = (g z θ) ^ 2 * 1 := by ring
    _ ≤ (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
    _ = (g z θ * Work.Spaces.w z) ^ 2 := by ring

/-- **The pointwise domination.**  For `θ` in the *open* interval, where `sin(2θ) ∈ (0,1]`,
the square `(g·w)²` is bounded by the `ℋ^k`-integrand: the latter contains the `i = 0`
summand `(g·w·sin(2θ)^{-η/2})²` (`Work.Spaces.sq_le_HkIntegrand_z`), which is `(g·w)²`
divided by a factor `≤ 1`. -/
theorem sq_mul_w_le_HkIntegrand {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (g z θ * Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have ht0 : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  have ht1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
    calc (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ (1 : ℝ) ^ (Work.Spaces.eta / 2) :=
          Real.rpow_le_rpow hs0.le hs1
            (div_nonneg (le_of_lt Work.Spaces.eta_pos) (by norm_num))
      _ = 1 := Real.one_rpow _
  -- dividing by a number in `(0,1]` does not decrease a square
  have hstep : (g z θ * Work.Spaces.w z) ^ 2
      ≤ (g z θ * Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 ≤ 1 := by nlinarith [ht0, ht1]
    calc (g z θ * Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        ≤ (g z θ * Work.Spaces.w z) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (g z θ * Work.Spaces.w z) ^ 2 := by ring
  have hstep2 : (g z θ * Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    ring
  rw [hstep2] at hstep
  exact le_trans hstep (Work.Spaces.sq_le_HkIntegrand_z α k g z θ 0 (Nat.zero_le k))


/-- **The square of an `ℋ^k`-function is integrable on every angular slice.**  This is the
double use of `EllHyp.memPsi`: the `ℋ^k`-integrand of `Ψ` is integrable on the slice and
dominates `Ψ(z,θ)²` a.e., while the slice itself is measurable by smoothness. -/
theorem integrableOn_slice_sq {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α k g)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2) Work.Spaces.Iθ := by
  have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  refine Integrable.mono' (hmem.1 z hzIz) ?_ ?_
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2) Qd :=
      (hsm.continuousOn.mono Qd_subset_nbhQ).pow 2
    exact Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2)
      hcont hz
  · rw [← restrict_Ioo_eq_restrict_Iθ]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact le_trans (sq_le_sq_mul_w hz θ) (sq_mul_w_le_HkIntegrand hθ)






/-! ## A.e. strong measurability of the angular moment -/

/-- `θ ↦ sinθ cos²θ` is continuous. -/
theorem continuous_sinCos2 : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ :=
  Real.continuous_sin.mul (Real.continuous_cos.pow 2)


/-! ## The main statement -/


end Work.FTS.EllipticEst.Cert.L12Aux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.hasDerivAt_Gfun =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

/-- **The total-derivative identity underlying the θ-slice IBP.**
`Gfun v ψ θ = ψ θ · (σ θ · v θ · v' θ - η · (cos 2θ · σ₁ θ) · v θ²) - (1/2) · ψ' θ · σ θ · v θ²`
(see `SliceThetaIbpDefs`) is a boundary primitive for the slice identity `S2`: for
`v ∈ C²((0,π/2))`, `ψ ∈ C²(ℝ)` and `θ ∈ (0,π/2)` its derivative is the difference
`Lfun v ψ θ - RHSfun v ψ θ` of the two integrands of `sliceThetaIbpSep`.

Proof route (already prepared in `SliceThetaIbpDefs`): build the product-rule chain
`hσ := sst_hasDerivAt_sig hθ` (`(σ)' = -2η cos2θ σ₁`), `hsigc := hasDerivAt_sigc hθ`
(`(cos2θ σ₁)' = -2σ - 2(1+η)cos²2θ σ₂`), `sst_hasDerivAt_sig1` (`(σ₁)'`), the `HasDerivAt`s of
`v`, `deriv v` (`hv.contDiffAt`), `ψ`, `deriv ψ` (from `hψ : ContDiff ℝ 2 ψ`, e.g. via
`ContDiffOn.deriv_of_isOpen` on `Set.univ` and `DifferentiableOn.differentiableAt`), apply
`HasDerivAt.mul`, `.sub`, `.const_mul`, `.pow`, and finish with `convert h using 1` followed by
`rw [Rawk_eq v ψ hθ]; simp only [sigc]; ring` — the chain's derivative is exactly
`Rawk v ψ θ`, and `Rawk_eq : Rawk v ψ θ = Lfun v ψ θ - RHSfun v ψ θ` is already proved. -/
theorem hasDerivAt_Gfun (v ψ : ℝ → ℝ)
    (hv : ContDiffOn ℝ 2 v (Set.Ioo 0 (Real.pi / 2)))
    (hψ : ContDiff ℝ 2 ψ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Gfun v ψ)
      (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Lfun v ψ θ
        - Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.RHSfun v ψ θ) θ := by
  -- differentiability data: `v`, `v'` from `hv`; `ψ`, `ψ'` from `hψ`
  have hv1 : HasDerivAt v (deriv v θ) θ :=
    ((hv.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
  have hdv : ContDiffOn ℝ 1 (deriv v) (Set.Ioo 0 (Real.pi / 2)) :=
    hv.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hv2 : HasDerivAt (deriv v) (deriv (deriv v) θ) θ :=
    ((hdv.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
  have hψ1 : HasDerivAt ψ (deriv ψ θ) θ :=
    (hψ.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hdψ : ContDiffOn ℝ 1 (deriv ψ) Set.univ :=
    hψ.contDiffOn.deriv_of_isOpen isOpen_univ (m := 1) (by norm_num)
  have hψ2 : HasDerivAt (deriv ψ) (deriv (deriv ψ) θ) θ :=
    ((hdψ.differentiableOn (by norm_num)).differentiableAt
      (isOpen_univ.mem_nhds (Set.mem_univ θ))).hasDerivAt
  -- the derivative of the bracket `σ (v v') - η (c σ₁) v²`
  have hA : HasDerivAt
      (fun t => sig t * (v t * deriv v t) - Work.Spaces.eta * (sigc t * (v t) ^ 2))
      ((-2 * Work.Spaces.eta * Real.cos (2 * θ) * sig1 θ) * (v θ * deriv v θ)
        + sig θ * (deriv v θ * deriv v θ + v θ * deriv (deriv v) θ)
        - Work.Spaces.eta * ((-2 * sig θ - 2 * (1 + Work.Spaces.eta)
              * (Real.cos (2 * θ)) ^ 2 * sig2 θ) * (v θ) ^ 2
            + sigc θ * (2 * v θ ^ (2 - 1) * deriv v θ))) θ :=
    ((sst_hasDerivAt_sig hθ).mul (hv1.mul hv2)).sub
      (((hasDerivAt_sigc hθ).mul (hv1.pow 2)).const_mul Work.Spaces.eta)
  -- the derivative of the second summand `ψ' (σ v²)`
  have hB : HasDerivAt (fun t => deriv ψ t * (sig t * (v t) ^ 2))
      (deriv (deriv ψ) θ * (sig θ * (v θ) ^ 2)
        + deriv ψ θ * ((-2 * Work.Spaces.eta * Real.cos (2 * θ) * sig1 θ) * (v θ) ^ 2
            + sig θ * (2 * v θ ^ (2 - 1) * deriv v θ))) θ :=
    hψ2.mul ((sst_hasDerivAt_sig hθ).mul (hv1.pow 2))
  have hmain := (hψ1.mul hA).sub (hB.const_mul (1 / 2))
  -- the chain's derivative is `Rawk`, which equals `Lfun - RHSfun`
  refine hmain.congr_deriv ?_
  rw [← Rawk_eq v ψ hθ]
  unfold Rawk Lfun
  simp only [sigc]
  ring_nf

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.intervalIntegrable_pieces =====
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

/-- `θ ↦ sin(2θ)^p` is continuous on `[a,b]` as soon as `sin (2θ) ≠ 0` there (any real exponent
`p`; the base is then separated from `0`). -/
lemma continuousOn_sin_two_rpow {p a b : ℝ} (h : ∀ θ ∈ Set.Icc a b, Real.sin (2 * θ) ≠ 0) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (Set.Icc a b) := by
  have hc : Continuous fun θ : ℝ => Real.sin (2 * θ) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  exact hc.continuousOn.rpow_const fun θ hθ => Or.inl (h θ hθ)

/-- `θ ↦ cos(2θ)` is continuous on `[a,b]`. -/
lemma continuousOn_cos_two {a b : ℝ} :
    ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Icc a b) :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn

/-- **Interval integrability of the five integrands of the θ-slice identity.**  All of them are
continuous on the compact interval `[a,b] ⊂ (0,π/2)`: `sig θ = sin(2θ)^{-η}` and
`Real.sin (2θ)^{-1}` are continuous there (the sine does not vanish), `ψ` is `C²` on `ℝ`, and
`v`, `deriv v`, `deriv (deriv v)` are continuous on a neighbourhood of `[a,b]` because
`hv : ContDiffOn ℝ 2 v (Ioo 0 (π/2))`.  The last two conjuncts follow from the first five by the
elementary `IntervalIntegrable` combinators (`sub`, `add`, `const_mul`) and the definitions of
`RHSfun` and `GderivFun` in `SliceThetaIbpDefs`. -/
theorem intervalIntegrable_pieces (v ψ : ℝ → ℝ)
    (hv : ContDiffOn ℝ 2 v (Set.Ioo 0 (Real.pi / 2)))
    (hψ : ContDiff ℝ 2 ψ) {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2) (hab : a ≤ b) :
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Lfun v ψ) volume a b ∧
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Afun v ψ) volume a b ∧
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Bfun v ψ) volume a b ∧
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Cfun v ψ) volume a b ∧
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Dfun v ψ) volume a b ∧
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.RHSfun v ψ) volume a b ∧
    IntervalIntegrable (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GderivFun v ψ) volume a b := by
  -- the sine does not vanish on `[a,b]`
  have hsin : ∀ θ ∈ Set.Icc a b, Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    have h1 : 0 < 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ < Real.pi := by linarith [hθ.2]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  -- an open interval `(c,d)` with `[a,b] ⊆ (c,d) ⊆ (0,π/2)`
  obtain ⟨c, d, hc0, hca, hbd, hdpi⟩ : ∃ c d : ℝ, 0 < c ∧ c < a ∧ b < d ∧ d < Real.pi / 2 :=
    ⟨a / 2, (b + Real.pi / 2) / 2, by linarith, by linarith, by linarith, by linarith⟩
  have hcd : Set.Ioo c d ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_trans hc0 hx.1, lt_trans hx.2 hdpi⟩
  have hv' : ContDiffOn ℝ 2 v (Set.Ioo c d) := hv.mono hcd
  have hsub : Set.Icc a b ⊆ Set.Ioo c d :=
    fun x hx => ⟨lt_of_lt_of_le hca hx.1, lt_of_le_of_lt hx.2 hbd⟩
  -- continuity of `v` and its first two derivatives on `[a,b]`
  have hvc : ContinuousOn v (Set.Icc a b) := hv'.continuousOn.mono hsub
  have hdv : ContinuousOn (deriv v) (Set.Icc a b) :=
    (hv'.continuousOn_deriv_of_isOpen (n := 2) isOpen_Ioo (by norm_num)).mono hsub
  have hddv : ContinuousOn (deriv (deriv v)) (Set.Icc a b) :=
    ((hv'.deriv_of_isOpen (m := 1) (n := 2) isOpen_Ioo (by norm_num)).continuousOn_deriv_of_isOpen
      (n := 1) isOpen_Ioo (by norm_num)).mono hsub
  -- continuity of `ψ` and of its two derivatives
  have hψc : Continuous ψ := hψ.continuous
  have hψddc : Continuous (deriv (deriv ψ)) := by fun_prop
  -- continuity of the angular weights
  have hsig : ContinuousOn sig (Set.Icc a b) :=
    continuousOn_sin_two_rpow (p := -(Work.Spaces.eta)) hsin
  have hsininv : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(1 : ℝ))) (Set.Icc a b) :=
    continuousOn_sin_two_rpow (p := -(1 : ℝ)) hsin
  have hcos : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Icc a b) :=
    continuousOn_cos_two
  -- the five integrands
  have hL : ContinuousOn (Lfun v ψ) (Set.Icc a b) :=
    (hsig.mul hψc.continuousOn).mul (hvc.mul hddv)
  have hA : ContinuousOn (Afun v ψ) (Set.Icc a b) :=
    (hsig.mul hψc.continuousOn).mul (hvc.pow 2)
  have hB : ContinuousOn (Bfun v ψ) (Set.Icc a b) :=
    (hsig.mul hψc.continuousOn).mul (hdv.pow 2)
  have hCbase : ContinuousOn (fun θ : ℝ => deriv v θ - (1 + Work.Spaces.eta) * v θ
      * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) (Set.Icc a b) :=
    hdv.sub (((continuous_const.continuousOn.mul hvc).mul hcos).mul hsininv)
  have hC : ContinuousOn (Cfun v ψ) (Set.Icc a b) :=
    (hsig.mul hψc.continuousOn).mul (hCbase.pow 2)
  have hD : ContinuousOn (Dfun v ψ) (Set.Icc a b) :=
    (hsig.mul hψddc.continuousOn).mul (hvc.pow 2)
  have hRHS : ContinuousOn (RHSfun v ψ) (Set.Icc a b) :=
    (((hA.const_mul (-2 * Work.Spaces.eta)).sub
        (hB.const_mul ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)))).sub
      (hC.const_mul (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)))).add
      (hD.const_mul (1 / 2))
  have hG : ContinuousOn (GderivFun v ψ) (Set.Icc a b) := hL.sub hRHS
  exact ⟨ContinuousOn.intervalIntegrable_of_Icc hab hL,
    ContinuousOn.intervalIntegrable_of_Icc hab hA,
    ContinuousOn.intervalIntegrable_of_Icc hab hB,
    ContinuousOn.intervalIntegrable_of_Icc hab hC,
    ContinuousOn.intervalIntegrable_of_Icc hab hD,
    ContinuousOn.intervalIntegrable_of_Icc hab hRHS,
    ContinuousOn.intervalIntegrable_of_Icc hab hG⟩

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_left_integral_nonneg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000









end Work.FTS.EllipticEst.Cores.AeStep2Aux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Ae.SecDerivBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false

/-!
# Elementary facts about the weight `sEta θ = sin(2θ)^{-η}` (`η = 99/100`)

These are the pointwise and measurability facts used by the proof that a weighted `L²` bound
on `f''` forces `f` to be bounded on `(0, π/2)` with one-sided limits at both endpoints.
-/

lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
    by linarith [hθ.2, Real.pi_pos]⟩

lemma sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- `sEta θ = sin(2θ)^{-η} ≥ 1` on the open interval. -/
lemma one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  have h0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h2 : -(Work.Spaces.eta) ≤ 0 := by
    rw [Work.Spaces.eta]; norm_num
  calc (1 : ℝ) = 1 ^ (-(Work.Spaces.eta)) := by rw [Real.one_rpow]
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_nonpos h0 h1 h2

lemma measurable_sEta : Measurable sEta :=
  (Real.measurable_sin.comp (by fun_prop : Measurable fun θ : ℝ => 2 * θ)).pow measurable_const



end Work.FTS.EllipticEst.H2W.Ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Lzb.LzeroSingCosBoundClean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Lzb

open MeasureTheory

/-!
## Boundedness of `θ ↦ LzeroSing θ · cos θ` on `(0, π/2)`

`LzeroSing θ = sin(2θ) · ∫_{π/4}^{π/2-θ} I(s) ds` with `I(s) = 1/(sin s · sin(2s)²)`, so it
suffices to bound `J(θ) = ∫_{π/4}^{π/2-θ} I` from the two sides by the elementary pointwise
bounds `I(s) ≤ π²/(2 (π/2-s)²)` (for `s ≥ π/4`) and `I(s) ≤ π³/(8 s³)` (for `s ≤ π/4`),
combined with the exact evaluations of the two model integrals `∫ ds/(π/2-s)²` and `∫ ds/s³`.
-/

/-! ## Elementary positivity and integrability of the singular weight -/



/-! ## The two pointwise bounds on the weight -/



/-! ## The two model integrals -/




end Work.FTS.EllipticEst.H2W.Lzb
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.sliceStep5gDerivIdents =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open Filter Set

/-! ## The `tan`-form of the slice operator `L₀`

`Lzero1 u = -u'' + (tan θ · u)' - 6u`.  On the open interval `(0, π/2)` the derivative
`(tan θ · u)'` expands by the Leibniz rule, `(tan θ)' = 1 + tan²θ`, and
`(1 + tan²θ) - 6 = tan²θ - 5`:

  `Lzero1 u = -u'' + tan θ · u' + (tan²θ - 5) u`,

which is the first identity of `sliceStep5gDerivIdents`.  Differentiating once more with

  `(tan θ · u)'' = tan θ · u'' + 2(1 + tan²θ) u' + 2 tan θ (1 + tan²θ) u`

(this is `deriv_deriv_tan_mul` below) gives the second identity:

  `g' = -u''' + tan θ · u'' + (2tan²θ - 4) u' + (2tan θ + 2tan³θ) u`.

The two auxiliary lemmas `deriv_tan_mul`, `deriv_deriv_tan_mul` are exactly the two
derivatives of `θ ↦ tan θ · u θ` on `(0, π/2)`.
-/

/-- `(tan θ)' = 1 + tan²θ` (at a point where `cos θ ≠ 0`). -/
private lemma one_div_cos_sq {θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    1 / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  rw [Real.cos_sq_add_sin_sq]

/-- `cos θ ≠ 0` for `θ ∈ (0, π/2)`. -/
private lemma cos_ne_zero_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ ≠ 0 :=
  (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩).ne'

/-- `tan` is differentiable at any point where `cos` does not vanish. -/
private lemma differentiableAt_tan {θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    DifferentiableAt ℝ Real.tan θ :=
  ((Real.contDiffAt_tan (n := 1)).mpr hcos).differentiableAt (by norm_num)

/-- The first derivative of `θ ↦ tan θ · u θ` on `(0, π/2)`. -/
private lemma deriv_tan_mul (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun s => Real.tan s * u s) θ
      = (1 + Real.tan θ ^ 2) * u θ + Real.tan θ * deriv u θ := by
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos : Real.cos θ ≠ 0 := cos_ne_zero_of_mem_Ioo hθ
  have hu1 : HasDerivAt u (deriv u θ) θ :=
    ((hu.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  rw [show (fun s => Real.tan s * u s) = Real.tan * u from rfl,
    deriv_mul (differentiableAt_tan hcos) hu1.differentiableAt, Real.deriv_tan]
  rw [show 1 / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 from one_div_cos_sq hcos]

/-- The second derivative of `θ ↦ tan θ · u θ` on `(0, π/2)`. -/
private lemma deriv_deriv_tan_mul (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => deriv (fun s => Real.tan s * u s) t) θ
      = Real.tan θ * deriv (deriv u) θ + 2 * (1 + Real.tan θ ^ 2) * deriv u θ
        + 2 * Real.tan θ * (1 + Real.tan θ ^ 2) * u θ := by
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos : Real.cos θ ≠ 0 := cos_ne_zero_of_mem_Ioo hθ
  have hu1 : HasDerivAt u (deriv u θ) θ :=
    ((hu.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have hdu : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hu2 : HasDerivAt (deriv u) (deriv (deriv u) θ) θ :=
    ((hdu.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have hdt : DifferentiableAt ℝ Real.tan θ := differentiableAt_tan hcos
  -- the first derivative is, near `θ`, the explicit function of `u`, `u'`
  have hev : deriv (fun s => Real.tan s * u s) =ᶠ[𝓝 θ]
      (fun t => (1 + Real.tan t ^ 2) * u t + Real.tan t * deriv u t) := by
    filter_upwards [hmem] with t ht
    exact deriv_tan_mul u (hu.of_le (by norm_num)) ht
  have hdtpow : DifferentiableAt ℝ (fun t => Real.tan t ^ 2) θ := hdt.pow 2
  have hcst : DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) θ := differentiableAt_const (1 : ℝ)
  -- the derivative of `1 + tan²`
  have hA : deriv (fun t => 1 + Real.tan t ^ 2) θ
      = 2 * Real.tan θ * (1 + Real.tan θ ^ 2) := by
    rw [show (fun t => 1 + Real.tan t ^ 2)
          = (fun _ : ℝ => (1 : ℝ)) + (fun t => Real.tan t ^ 2) from rfl,
      deriv_add hcst hdtpow, deriv_const, zero_add]
    rw [show (fun t => Real.tan t ^ 2) = Real.tan ^ 2 from rfl, deriv_pow hdt 2,
      Real.deriv_tan]
    rw [show 1 / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 from one_div_cos_sq hcos]
    ring
  have h1diff : DifferentiableAt ℝ (fun t => 1 + Real.tan t ^ 2) θ := hcst.add hdtpow
  have hf : DifferentiableAt ℝ (fun t => (1 + Real.tan t ^ 2) * u t) θ :=
    h1diff.mul hu1.differentiableAt
  have hg : DifferentiableAt ℝ (fun t => Real.tan t * deriv u t) θ :=
    hdt.mul hu2.differentiableAt
  rw [hev.deriv_eq,
    show (fun t => (1 + Real.tan t ^ 2) * u t + Real.tan t * deriv u t)
        = (fun t => (1 + Real.tan t ^ 2) * u t) + fun t => Real.tan t * deriv u t from rfl,
    deriv_add hf hg]
  rw [show (fun t => (1 + Real.tan t ^ 2) * u t)
        = (fun t => 1 + Real.tan t ^ 2) * u from rfl,
    deriv_mul h1diff hu1.differentiableAt, hA]
  rw [show (fun t => Real.tan t * deriv u t) = Real.tan * deriv u from rfl,
    deriv_mul hdt hu2.differentiableAt, Real.deriv_tan]
  rw [show 1 / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 from one_div_cos_sq hcos]
  ring

theorem sliceStep5gDerivIdents (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      g θ = -(deriv (deriv u) θ) + Real.tan θ * deriv u θ
        + (Real.tan θ ^ 2 - 5) * u θ) ∧
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv g θ = -(deriv (deriv (deriv u)) θ) + Real.tan θ * deriv (deriv u) θ
        + (2 * Real.tan θ ^ 2 - 4) * deriv u θ
        + (2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) := by
  have hu1 : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
  have hu3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
  constructor
  · intro θ hθ
    have hder := deriv_tan_mul u hu1 hθ
    calc g θ = Work.FTS.EllipticEst.Lzero1 u θ := (hode θ hθ).symm
      _ = -(deriv (deriv u) θ) + deriv (fun s => Real.tan s * u s) θ - 6 * u θ := by
            simp only [Work.FTS.EllipticEst.Lzero1]
      _ = -(deriv (deriv u) θ)
            + ((1 + Real.tan θ ^ 2) * u θ + Real.tan θ * deriv u θ) - 6 * u θ := by
            rw [hder]
      _ = -(deriv (deriv u) θ) + Real.tan θ * deriv u θ
            + (Real.tan θ ^ 2 - 5) * u θ := by ring
  · intro θ hθ
    have hg := Work.FTS.EllipticEst.remov.slice_gprime_ident u g hu3 hode θ hθ
    have hder2 := deriv_deriv_tan_mul u hu2 hθ
    calc deriv g θ
        = - deriv (deriv (deriv u)) θ
          + deriv (fun t => deriv (fun s => Real.tan s * u s) t) θ - 6 * deriv u θ := hg
      _ = - deriv (deriv (deriv u)) θ
          + (Real.tan θ * deriv (deriv u) θ + 2 * (1 + Real.tan θ ^ 2) * deriv u θ
              + 2 * Real.tan θ * (1 + Real.tan θ ^ 2) * u θ) - 6 * deriv u θ := by
            rw [hder2]
      _ = -(deriv (deriv (deriv u)) θ) + Real.tan θ * deriv (deriv u) θ
          + (2 * Real.tan θ ^ 2 - 4) * deriv u θ
          + (2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ := by ring

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.aemeasurable_sliceSigmaLin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter
open scoped Real Topology ENNReal

namespace Work.FTS.EllipticEst.Honest

/-- The joint integrand `(z,θ) ↦ ofReal (sEta θ * Ψ z θ ^ 2)` is continuous on the open
quadrant `(0,∞) × (0,π/2)`: `hsm 0` supplies the continuity of `Ψ` there, `sin (2·)` is
strictly positive on `(0,π/2)`, so `sEta θ = sin (2θ) ^ (-η)` depends continuously on `θ`,
and `ENNReal.ofReal` is continuous. -/
theorem continuousOn_uncurry_sEta_mul_sq (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ =>
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta p.2 * (Ψ p.1 p.2) ^ 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hΨ : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hsm 0).continuousOn
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    apply Continuous.continuousOn
    fun_prop
  have hne : ∀ p ∈ (Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)), Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    have h1 : 0 < 2 * p.2 := by linarith [hp.2.1]
    have h2 : 2 * p.2 < Real.pi := by linarith [hp.2.2]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  have hsEta : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    simp only [Work.FTS.EllipticEst.sEta]
    exact hsin.rpow_const (fun p hp => Or.inl (hne p hp))
  exact ENNReal.continuous_ofReal.comp_continuousOn (hsEta.mul (hΨ.pow 2))

/-- The uncurried integrand of the slice `Σ`-linear form is a.e. strongly measurable for the
product of the restrictions of Lebesgue measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`; this is
`continuousOn_uncurry_sEta_mul_sq` transported along the a.e. equality
`Iz ×ˢ Iθ =ᵐ (0,∞) ×ˢ (0,π/2)`. -/
theorem aesm_uncurry_sEta_mul_sq (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta p.2 * (Ψ p.1 p.2) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hQm : MeasurableSet (Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.FTS.EllipticEst.sEta p.2 * (Ψ p.1 p.2) ^ 2))
      ((volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :=
    (continuousOn_uncurry_sEta_mul_sq Ψ hsm).aestronglyMeasurable hQm
  have hz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0:ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0:ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume]
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
  exact haesm

theorem aemeasurable_sliceSigmaLin (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (Ψ z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  refine AEMeasurable.lintegral_prod_right ?_
  exact (aesm_uncurry_sEta_mul_sq Ψ hsm).aemeasurable

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_normSq_pos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

set_option autoImplicit false









end Work.FTS.EllipticEst.LevelOneAsm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_orth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm


/-- `deriv (1 - u²) = -2u`. -/
lemma hasDerivAt_one_sub_sq (u : ℝ) :
    HasDerivAt (fun u : ℝ => (1 : ℝ) - u ^ 2) (-(2 * u)) u := by
  have h := (hasDerivAt_pow 2 u).const_sub (1 : ℝ)
  simpa using h






end Work.FTS.EllipticEst.LevelOneAsm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_span_dense =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-- Compatibility notation: in this Mathlib revision `AEMeasurable` is a root-level declaration
(the qualified name `MeasureTheory.AEMeasurable` does not resolve).  This notation is parse-time
only: it introduces no declaration and expands to the root-level `AEMeasurable`. -/
notation "MeasureTheory.AEMeasurable" => @AEMeasurable

noncomputable section

open scoped Real Topology Polynomial
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ

/-! ## Elementary facts about the interval -/

private lemma cos_nonneg_of_mem_Iθ_prv {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩

private lemma sin_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin θ :=
  Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩

private lemma integrableOn_one_Iθ : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Iθ :=
  integrableOn_const (μ := volume) (s := Iθ) (C := (1 : ℝ))
    (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

/-- A.e. point of `Iθ` is an interior point: the two endpoints form a null set. -/
private lemma ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [MeasureTheory.ae_iff]
  change (volume.restrict Iθ) ((Set.Ioo 0 (Real.pi / 2))ᶜ) = 0
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
  have hnull : volume ({0, Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) volume
  refine MeasureTheory.measure_mono_null ?_ hnull
  intro θ hθ
  have h1 : θ ∈ Iθ := hθ.2
  have h2 : θ ∉ Set.Ioo 0 (Real.pi / 2) := hθ.1
  by_cases h : θ ≤ 0
  · exact Or.inl (le_antisymm h h1.1)
  · refine Or.inr (le_antisymm h1.2 (le_of_not_gt fun hc => ?_))
    exact absurd ⟨lt_of_not_ge h, hc⟩ h2



/-! ## Integrability of the pieces -/










/-! ## The moments `(∗)` -/






/-! ## Continuous test functions `(∗∗)` -/


/-! ## Compact sets -/


/-! ## The density theorem -/


end Work.FTS.EllipticEst.LevelOneAsm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LzeroSingAuxDeriv =====
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


end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Phi_derivs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Auxiliary material for `Phi_derivs` -/

namespace Aux

/-- The open neighbourhood of the closed quadrant on which `SmoothNbhd` gives smoothness. -/
def PhiU : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1)

theorem isOpen_U : IsOpen PhiU := isOpen_Ioi.prod isOpen_Ioo

theorem mem_U {z θ : ℝ} : (z, θ) ∈ PhiU ↔ -1 < z ∧ -1 < θ ∧ θ < π/2 + 1 := by
  simp [PhiU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

/-- The slice `x ↦ w x θ` of a function differentiable on `ℝ × ℝ` is differentiable. -/
theorem differentiableAt_slice {w : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry w) (z, θ)) :
    DifferentiableAt ℝ (fun x => w x θ) z := by
  have hfd : HasFDerivAt (Function.uncurry w) (fderiv ℝ (Function.uncurry w) (z, θ)) (z, θ) :=
    h.hasFDerivAt
  have hcurve : HasFDerivAt (fun x : ℝ => (x, θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) z :=
    hasFDerivAt_prodMk_left z θ
  exact (hfd.comp z hcurve).differentiableAt

theorem hasDerivAt_slice {w : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry w) (z, θ)) :
    HasDerivAt (fun x => w x θ) (Work.Spaces.pz w z θ) z :=
  (differentiableAt_slice h).hasDerivAt


/-- `Work.Spaces.pz v` is smooth on the open neighbourhood `PhiU` of the closed quadrant, whenever
`v` is smooth there. -/
theorem contDiffOn_pz_backup {v : ℝ → ℝ → ℝ} (hs : Work.Spaces.SmoothNbhd v) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => Work.Spaces.pz v p.1 p.2) PhiU := by
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry v) PhiU := hs.of_le le_top
  have hdiff : DifferentiableOn ℝ (Function.uncurry v) PhiU :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_U).1 hG).1
  have hGf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry v) p) PhiU :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_U).1 hG).2
  have hZ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry v) p) ((1 : ℝ), (0 : ℝ))) PhiU :=
    hGf.clm_apply contDiffOn_const
  refine hZ.congr fun p hp => ?_
  have hd : HasFDerivAt (Function.uncurry v) (fderiv ℝ (Function.uncurry v) p) p :=
    (hdiff.differentiableAt (isOpen_U.mem_nhds hp)).hasFDerivAt
  have hcurve : HasFDerivAt (fun x : ℝ => (x, p.2)) (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 :=
    hasFDerivAt_prodMk_left p.1 p.2
  have hder := (hd.comp p.1 hcurve).hasDerivAt
  have hval : deriv (fun x => (Function.uncurry v) (x, p.2)) p.1
      = (fderiv ℝ (Function.uncurry v) p) ((1 : ℝ), (0 : ℝ)) := by
    rw [show (fun x => (Function.uncurry v) (x, p.2))
        = Function.uncurry v ∘ fun x : ℝ => (x, p.2) from by funext x; rfl]
    rw [hder.deriv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  show deriv (fun x => (Function.uncurry v) (x, p.2)) p.1
      = (fderiv ℝ (Function.uncurry v) p) ((1 : ℝ), (0 : ℝ))
  exact hval

end Aux

/-- The second `z`-derivative of a smooth function is smooth on `Aux.PhiU`. -/
theorem contDiffOn_pzIter_two {v : ℝ → ℝ → ℝ} (hs : Work.Spaces.SmoothNbhd v) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 v p.1 p.2) Aux.PhiU := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Work.Spaces.pz v p.1 p.2) Aux.PhiU := Aux.contDiffOn_pz_backup hs
  have hd1 : DifferentiableOn ℝ (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2) Aux.PhiU :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen Aux.isOpen_U).1 h1).1
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2) p) Aux.PhiU :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen Aux.isOpen_U).1 h1).2
  have h3 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2) p)
        ((1 : ℝ), (0 : ℝ))) Aux.PhiU :=
    h2.clm_apply contDiffOn_const
  refine h3.congr fun p hp => ?_
  have hd : HasFDerivAt (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2)
      (fderiv ℝ (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2) p) p :=
    (hd1.differentiableAt (Aux.isOpen_U.mem_nhds hp)).hasFDerivAt
  have hcurve : HasFDerivAt (fun x : ℝ => (x, p.2)) (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 :=
    hasFDerivAt_prodMk_left p.1 p.2
  have hder := (hd.comp p.1 hcurve).hasDerivAt
  have hval : deriv (fun x => Work.Spaces.pz v x p.2) p.1
      = (fderiv ℝ (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2) p) ((1 : ℝ), (0 : ℝ)) := by
    rw [show (fun x => Work.Spaces.pz v x p.2)
        = (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2) ∘ fun x : ℝ => (x, p.2) from by
          funext x; rfl]
    rw [hder.deriv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  exact hval


end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.SgamBound.abs_deriv_sub_le_integral_abs_D2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The mean-value bound for a slice: `|u'(θ) - u'(θ₀)| ≤ ∫_{Iθ} |u''|`

If `u` is `C^∞` on the open angular interval `(0, π/2)` and `|u''|` is integrable on
`Iθ = [0, π/2]`, then for any two interior points `θ, θ₀ ∈ (0, π/2)` the fundamental theorem
of calculus on the segment joining them gives

  `u'(θ) - u'(θ₀) = ∫_{θ₀}^{θ} u''`,

and since `|u''| ≥ 0` and the segment `[θ₀, θ]` (respectively `[θ, θ₀]`) is contained in
`Iθ`, the absolute value of this integral is at most `∫_{Iθ} |u''|`.
-/

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.SgamBound

theorem abs_deriv_sub_le_integral_abs_D2 {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hD2abs : MeasureTheory.IntegrableOn
      (fun θ => |Work.FTS.EllipticEst.TT.D2 u θ|) Work.Spaces.Iθ)
    {θ θ₀ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |deriv u θ - deriv u θ₀|
      ≤ ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x| := by
  have hπ : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  -- `D2 u` is definitionally the second derivative of `u`.
  have hD2 : Work.FTS.EllipticEst.TT.D2 u = deriv (deriv u) := rfl
  -- `u` is `C²`, so `deriv u` is `C¹` on the open interval.
  have hcd : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
  -- the segment joining `θ₀` and `θ` stays strictly inside `(0, π/2)`.
  have hsub : Set.uIcc θ₀ θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hθ₀.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hθ₀.2⟩
  -- Newton–Leibniz on that segment.
  have hFTC : (∫ x in θ₀..θ, deriv (deriv u) x) = deriv u θ - deriv u θ₀ :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hcd.mono hsub)
  have hD2abs' : MeasureTheory.IntegrableOn (fun x => |deriv (deriv u) x|) Work.Spaces.Iθ := by
    simpa only [hD2] using hD2abs
  have hgi : IntervalIntegrable (fun x => |deriv (deriv u) x|) volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hπ).mpr (by
      simpa only [Work.Spaces.Iθ] using hD2abs')
  -- the integral over `Iθ = [0, π/2]` is the interval integral over `0..π/2`.
  have hIeq : (∫ x in Work.Spaces.Iθ, |deriv (deriv u) x|)
      = ∫ x in (0 : ℝ)..(Real.pi / 2), |deriv (deriv u) x| := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hπ]
  rw [← hFTC, hD2]
  rcases le_total θ₀ θ with hle | hle
  · have h1 : |∫ x in θ₀..θ, deriv (deriv u) x| ≤ ∫ x in θ₀..θ, |deriv (deriv u) x| :=
      intervalIntegral.abs_integral_le_integral_abs hle
    have h2 : (∫ x in θ₀..θ, |deriv (deriv u) x|)
        ≤ ∫ x in Work.Spaces.Iθ, |deriv (deriv u) x| := by
      rw [hIeq]
      exact intervalIntegral.integral_mono_interval (le_of_lt hθ₀.1) hle (le_of_lt hθ.2)
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    linarith
  · have h1 : |∫ x in θ..θ₀, deriv (deriv u) x| ≤ ∫ x in θ..θ₀, |deriv (deriv u) x| :=
      intervalIntegral.abs_integral_le_integral_abs hle
    have h2 : (∫ x in θ..θ₀, |deriv (deriv u) x|)
        ≤ ∫ x in Work.Spaces.Iθ, |deriv (deriv u) x| := by
      rw [hIeq]
      exact intervalIntegral.integral_mono_interval (le_of_lt hθ.1) hle (le_of_lt hθ₀.2)
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    rw [intervalIntegral.integral_symm, abs_neg]
    linarith

end Work.FTS.EllipticEst.SgamBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.SgamBound

/-- Lagrange mean-value bound on a sub-interval of `(0, π/2)`: if `u` is smooth on the open
strip `(0, π/2)` and `|u'| ≤ K` there, then for `0 < a ≤ b < π/2`
`|u b - u a| ≤ K * (b - a)`.

Proof: `exists_deriv_eq_slope` supplies `c ∈ (a, b)` with
`deriv u c = (u b - u a) / (b - a)`; multiply by `b - a > 0` and use `|deriv u c| ≤ K`
(the point `c` lies in `(0, π/2)`, since `Icc a b ⊆ Ioo 0 (π/2)`). -/
private lemma abs_sub_le_mul_of_deriv_bound_aux {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    {K a b : ℝ} (ha : a ∈ Set.Ioo 0 (Real.pi / 2))
    (hb : b ∈ Set.Ioo 0 (Real.pi / 2)) (hab : a ≤ b)
    (hK : ∀ ξ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u ξ| ≤ K) :
    |u b - u a| ≤ K * (b - a) := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · -- Nontrivial interval: Lagrange's mean value theorem.
    have hsub : Set.Icc a b ⊆ Set.Ioo 0 (Real.pi / 2) := Set.Icc_subset_Ioo ha.1 hb.2
    have hcont : ContinuousOn u (Set.Icc a b) := (hsm 1).continuousOn.mono hsub
    have hdiff : DifferentiableOn ℝ u (Set.Ioo a b) :=
      ((hsm 1).differentiableOn (by norm_num)).mono
        (Set.Ioo_subset_Ioo ha.1.le hb.2.le)
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope u hlt hcont hdiff
    have hcI : c ∈ Set.Ioo 0 (Real.pi / 2) := hsub ⟨le_of_lt hc.1, le_of_lt hc.2⟩
    have hKc : |deriv u c| ≤ K := hK c hcI
    have hpos : 0 < b - a := sub_pos.mpr hlt
    have h2 : u b - u a = (b - a) * deriv u c := by
      rw [hcd]; field_simp
    rw [h2, abs_mul, abs_of_pos hpos, mul_comm K]
    exact mul_le_mul_of_nonneg_left hKc (le_of_lt hpos)
  · -- Degenerate interval: the two points coincide.
    subst heq
    simp

theorem abs_sub_le_mul_abs_sub_of_deriv_bound {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    {K θ θ₀ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2))
    (hK : ∀ ξ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u ξ| ≤ K) :
    |u θ - u θ₀| ≤ K * |θ - θ₀| := by
  rcases le_total θ₀ θ with hle | hle
  · -- `θ₀ ≤ θ`: apply the mean-value bound on `[θ₀, θ]`.
    have h := abs_sub_le_mul_of_deriv_bound_aux hsm hθ₀ hθ hle hK
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact h
  · -- `θ ≤ θ₀`: apply it on `[θ, θ₀]` and use symmetry of the absolute value.
    have h := abs_sub_le_mul_of_deriv_bound_aux hsm hθ hθ₀ hle hK
    rw [abs_sub_comm (u θ) (u θ₀), abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    exact h

end Work.FTS.EllipticEst.SgamBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.SliceLocal.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.SliceLocal

set_option autoImplicit false

/-- The data-determined angular function `Φ_g`: for `g = Lzero1 u`,
`Φ_g θ = (2 cos³θ)⁻¹ ∫_θ^{π/2} sin σ cos²σ g σ dσ`.  It equals `sin²θ · ∂_θ(u / sin 2θ)` for
every slice `u` of the weak class (see `PhiOf` and `PhiOf_eq_PhiG`). -/
def PhiG (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (2 * (Real.cos θ) ^ 3)⁻¹ * ∫ σ in θ..(Real.pi / 2), Real.sin σ * (Real.cos σ) ^ 2 * g σ


/-- `Ψ_g θ = -∫_θ^{π/2} Φ_g σ / sin²σ dσ`: the `u`-part of the slice that is determined by the
data.  The full slice is `sin 2θ · (c + Ψ_g)` with a single constant `c ∈ ℝ`. -/
def PsiG (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  -∫ σ in θ..(Real.pi / 2), PhiG g σ / (Real.sin σ) ^ 2



end Work.FTS.EllipticEst.SliceLocal
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.SliceLocal.integrableOn_sinCos2_Lzero1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.SliceLocal

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- On the open quadrant `(0, π/2)` the angular operator `Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u`
is continuous as soon as `u` is of class `C²` there (the `tan` singularity is excluded because
`cos θ ≠ 0` on the open quadrant). -/
theorem continuousOn_Lzero1_of_contDiffOn_two (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hk : ContDiffAt ℝ 2 u θ := hu.contDiffAt (hU.mem_nhds hθ)
  have hdu : ContDiffAt ℝ 1 (fun s => deriv u s) θ := hk.derivWithin (m := 1) (by norm_num)
  have hddu : ContDiffAt ℝ 0 (fun t => deriv (fun s => deriv u s) t) θ :=
    hdu.derivWithin (m := 0) (by norm_num)
  have htan : ContDiffAt ℝ 2 Real.tan θ := (Real.contDiffAt_tan (n := 2)).mpr hcos
  have hmul : ContDiffAt ℝ 2 (fun s => Real.tan s * u s) θ := htan.mul hk
  have hA : ContDiffAt ℝ 0 (fun t => deriv (fun s => Real.tan s * u s) t) θ :=
    hmul.derivWithin (m := 0) (by norm_num)
  have hB : ContDiffAt ℝ 0 (fun t => (6 : ℝ) * u t) θ :=
    (contDiffAt_const (c := (6 : ℝ))).mul (hk.of_le (by norm_num))
  have hsum : ContDiffAt ℝ 0
      (fun t => -deriv (fun s => deriv u s) t + deriv (fun s => Real.tan s * u s) t
        - 6 * u t) θ := (hddu.neg.add hA).sub hB
  exact hsum.continuousAt.continuousWithinAt

/-- **Integrability of the slice pairing against `sin θ cos²θ`.**  If `u` is of class `C²` on the
open quadrant and the weighted square of its angular operator is integrable on
`Iθ = [0, π/2]`, then `θ ↦ sin θ cos²θ · Lzero1 u θ` is integrable there.

Indeed `|sin θ cos²θ| ≤ 1` on `Iθ`, so the claim follows from the integrability of `|Lzero1 u|`,
which is `Work.FTS.EllipticEst.integrableAbsOfSqSeta` applied to the continuity of `Lzero1 u`
on the open quadrant. -/
theorem integrableOn_sinCos2_Lzero1 (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hF : MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun σ => Real.sin σ * (Real.cos σ) ^ 2 * Work.FTS.EllipticEst.Lzero1 u σ)
      Work.Spaces.Iθ := by
  have hcont : ContinuousOn (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_Lzero1_of_contDiffOn_two u hu
  -- the absolute value of the operator is integrable on the closed quadrant
  have hb : MeasureTheory.IntegrableOn (fun θ => |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableAbsOfSqSeta hcont hF
  -- the two endpoints form a null set: the restricted measures agree
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)).symm
  -- almost everywhere strong measurability of the operator and of the product
  have hbasm : AEStronglyMeasurable (Work.FTS.EllipticEst.Lzero1 u)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [hms]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  have haasm : AEStronglyMeasurable (fun σ : ℝ => Real.sin σ * (Real.cos σ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn.aestronglyMeasurable
      measurableSet_Icc
  have hfasm : AEStronglyMeasurable
      (fun σ => Real.sin σ * (Real.cos σ) ^ 2 * Work.FTS.EllipticEst.Lzero1 u σ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := haasm.mul hbasm
  -- the pointwise domination and the conclusion
  refine MeasureTheory.Integrable.mono' hb hfasm ?_
  filter_upwards with σ
  have h1 : |Real.sin σ| ≤ 1 := Real.abs_sin_le_one σ
  have h2 : |(Real.cos σ) ^ 2| ≤ 1 := by
    rw [abs_pow]
    nlinarith [Real.abs_cos_le_one σ, abs_nonneg (Real.cos σ)]
  have key : |Real.sin σ * (Real.cos σ) ^ 2 * Work.FTS.EllipticEst.Lzero1 u σ|
      = |Real.sin σ| * |(Real.cos σ) ^ 2| * |Work.FTS.EllipticEst.Lzero1 u σ| := by
    rw [abs_mul, abs_mul]
  rw [Real.norm_eq_abs, key]
  calc |Real.sin σ| * |(Real.cos σ) ^ 2| * |Work.FTS.EllipticEst.Lzero1 u σ|
      ≤ 1 * 1 * |Work.FTS.EllipticEst.Lzero1 u σ| := by gcongr
    _ = |Work.FTS.EllipticEst.Lzero1 u σ| := by ring

end Work.FTS.EllipticEst.SliceLocal
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Heta_le_of_sin_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real
open MeasureTheory Set

namespace Work.FTS.EllipticEst.TT



end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.abs_le_sin_mul_of_deriv_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## The elementary sine bound -/



/-! ## The mean value bound -/


/-! ## The target bound -/


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.iterFamilyA_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## Weight bounds on the open interval `(0, π/2)` -/

/-- `sin(2θ)^{-γ} ≥ 1` on `(0, π/2)` (the exponent `-γ ≤ 0`, the base `sin(2θ) ≤ 1`). -/
private theorem one_le_sGam {α : ℝ} (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 1 ≤ sGam α θ := by
  have h0 : 0 < Real.sin (2 * θ) := sin_two_pos hθ.1 hθ.2
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgn : 0 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.gam_pos hα)
  have hz : -(Work.Spaces.gam α) ≤ 0 := by linarith
  calc (1 : ℝ) = (1 : ℝ) ^ (-(Work.Spaces.gam α)) := (Real.one_rpow _).symm
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        Real.rpow_le_rpow_of_nonpos h0 h1 hz
    _ = sGam α θ := rfl

/-- `sin(2θ)^{-η} ≥ 1` on `(0, π/2)` (the exponent `-η ≤ 0`, the base `sin(2θ) ≤ 1`). -/
private theorem one_le_sEta_prv {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 1 ≤ sEta θ := by
  have h0 : 0 < Real.sin (2 * θ) := sin_two_pos hθ.1 hθ.2
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hz : -(Work.Spaces.eta) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  calc (1 : ℝ) = (1 : ℝ) ^ (-(Work.Spaces.eta)) := (Real.one_rpow _).symm
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_nonpos h0 h1 hz
    _ = sEta θ := rfl

/-- `sin(2θ)⁴ · sin(2θ)^{-γ} = sin(2θ)^{4-γ} ≤ 1` on `(0, π/2)`, because `α ≤ 1/4` gives
`4 - γ ≥ 0` while `0 < sin(2θ) ≤ 1`. -/
private theorem sGam_mul_sin_pow_four_le_one {α : ℝ} (hα4 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    sGam α θ * (Real.sin (2 * θ)) ^ 4 ≤ 1 := by
  have h0 : 0 < Real.sin (2 * θ) := sin_two_pos hθ.1 hθ.2
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : 0 ≤ 4 - Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  have hrw : sGam α θ * (Real.sin (2 * θ)) ^ 4
      = (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by
    have hx : (Real.sin (2 * θ)) ^ 4 = (Real.sin (2 * θ)) ^ (4 : ℝ) :=
      (Real.rpow_natCast (Real.sin (2 * θ)) 4).symm
    calc sGam α θ * (Real.sin (2 * θ)) ^ 4
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Real.sin (2 * θ)) ^ (4 : ℝ) := by rw [sGam, hx]
      _ = (Real.sin (2 * θ)) ^ ((-(Work.Spaces.gam α)) + 4) :=
          (Real.rpow_add h0 (-(Work.Spaces.gam α)) 4).symm
      _ = (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by
          rw [show (-(Work.Spaces.gam α)) + 4 = 4 - Work.Spaces.gam α by ring]
  rw [hrw]
  exact Real.rpow_le_one (le_of_lt h0) h1 hexp

/-! ## The binomial coefficient bound -/

/-- `C(m,j)² ≤ 4^m`, from `C(m,j) ≤ 2^m`. -/
private theorem choose_sq_le_four_pow (m j : ℕ) :
    ((m.choose j : ℝ)) ^ 2 ≤ (4 : ℝ) ^ m := by
  have hcj : (m.choose j : ℝ) ≤ (2 : ℝ) ^ m := by
    have h := Nat.choose_le_two_pow m j
    calc (m.choose j : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h
      _ = (2 : ℝ) ^ m := by push_cast; ring
  calc ((m.choose j : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ m) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hcj 2
    _ = (4 : ℝ) ^ m := by rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, sq]

/-! ## The estimate -/

theorem iterFamilyA_le {cA : ℕ → ℝ}
    (hcA : ∀ j θ, (Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ) ^ 2
      ≤ cA j * (Real.sin (2 * θ)) ^ 4)
    (hcAnn : ∀ j, 0 ≤ cA j) (m : ℕ) (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (g : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ)) ^ 2 *
        ((Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ) ^ 2
          * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2))
      * Work.FTS.EllipticEst.sGam α θ
      ≤ (∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cA j) *
        ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          + ∑ k ∈ Finset.range m,
              (Work.Elliptic.Dth1Iter (k + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ) := by
  have hW1 : 1 ≤ Work.FTS.EllipticEst.sGam α θ := one_le_sGam hα hθ
  have hW0 : 0 ≤ Work.FTS.EllipticEst.sGam α θ := le_trans zero_le_one hW1
  have hE1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta_prv hθ
  have hE0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := le_trans zero_le_one hE1
  have hs4 : (Real.sin (2 * θ)) ^ 4 * Work.FTS.EllipticEst.sGam α θ ≤ 1 := by
    rw [mul_comm]; exact sGam_mul_sin_pow_four_le_one hα4 hθ
  have hsum_nn : 0 ≤ ∑ k ∈ Finset.range m,
      (Work.Elliptic.Dth1Iter (k + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ :=
    Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) hW0
  -- every `(D_θ^k g θ)²`, `k ≤ m`, is dominated by the bracket of the statement
  have hB : ∀ k ≤ m, (Work.Elliptic.Dth1Iter k g θ) ^ 2
      ≤ (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + ∑ k' ∈ Finset.range m,
            (Work.Elliptic.Dth1Iter (k' + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Work.Elliptic.Dth1Iter_zero]
      have h1 : (g θ) ^ 2 ≤ (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        calc (g θ) ^ 2 = (g θ) ^ 2 * 1 := (mul_one _).symm
          _ ≤ (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
              mul_le_mul_of_nonneg_left hE1 (sq_nonneg _)
      exact le_trans h1 (le_add_of_nonneg_right hsum_nn)
    · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      subst hk'
      have hkm : k' < m := by omega
      have hmem : k' ∈ Finset.range m := Finset.mem_range.mpr hkm
      have h1 : (Work.Elliptic.Dth1Iter (k' + 1) g θ) ^ 2
          ≤ ∑ k'' ∈ Finset.range m,
              (Work.Elliptic.Dth1Iter (k'' + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ := by
        calc (Work.Elliptic.Dth1Iter (k' + 1) g θ) ^ 2
            = (Work.Elliptic.Dth1Iter (k' + 1) g θ) ^ 2 * 1 := (mul_one _).symm
          _ ≤ (Work.Elliptic.Dth1Iter (k' + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ :=
              mul_le_mul_of_nonneg_left hW1 (sq_nonneg _)
          _ ≤ ∑ k'' ∈ Finset.range m,
              (Work.Elliptic.Dth1Iter (k'' + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ :=
              Finset.single_le_sum (f := fun k'' =>
                (Work.Elliptic.Dth1Iter (k'' + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ)
                (fun k'' _ => mul_nonneg (sq_nonneg _) hW0) hmem
      exact le_trans h1 (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) hE0))
  -- step 1: pull `sGam` inside and use the certificate `hcA`
  have hstep1 : (∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ)) ^ 2 *
        ((Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ) ^ 2
          * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2))
      * Work.FTS.EllipticEst.sGam α θ
      ≤ ∑ j ∈ Finset.range (m + 1),
          ((m.choose j : ℝ)) ^ 2 * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro j hj
    have hAj := hcA j θ
    have hcAj := hcAnn j
    have hCn : 0 ≤ ((m.choose j : ℝ)) ^ 2 := sq_nonneg _
    have hB2 : 0 ≤ (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2 := sq_nonneg _
    calc ((m.choose j : ℝ)) ^ 2 *
            ((Work.Elliptic.Dth1Iter j (fun τ : ℝ => Real.sin (2 * τ) ^ 2) θ) ^ 2
              * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2)
            * Work.FTS.EllipticEst.sGam α θ
        ≤ ((m.choose j : ℝ)) ^ 2 *
            ((cA j * (Real.sin (2 * θ)) ^ 4)
              * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2)
            * Work.FTS.EllipticEst.sGam α θ := by
          refine mul_le_mul_of_nonneg_right ?_ hW0
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAj hB2) hCn
      _ = ((m.choose j : ℝ)) ^ 2 * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2
            * ((Real.sin (2 * θ)) ^ 4 * Work.FTS.EllipticEst.sGam α θ) := by ring
      _ ≤ ((m.choose j : ℝ)) ^ 2 * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hs4 (mul_nonneg (mul_nonneg hCn hcAj) hB2)
      _ = ((m.choose j : ℝ)) ^ 2 * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2 :=
          mul_one _
  -- step 2: `C(m,j)² ≤ 4^m`
  have hstep2 : (∑ j ∈ Finset.range (m + 1),
          ((m.choose j : ℝ)) ^ 2 * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2)
      ≤ ∑ j ∈ Finset.range (m + 1),
          (4 : ℝ) ^ m * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (choose_sq_le_four_pow m j) (hcAnn j)) (sq_nonneg _)
  -- step 3: replace the remaining iterate by the bracket
  have hstep3 : (∑ j ∈ Finset.range (m + 1),
          (4 : ℝ) ^ m * cA j * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2)
      ≤ (∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cA j) *
        ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          + ∑ k ∈ Finset.range m,
              (Work.Elliptic.Dth1Iter (k + 1) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro j hj
    have hcnn : 0 ≤ (4 : ℝ) ^ m * cA j :=
      mul_nonneg (pow_nonneg (by norm_num) m) (hcAnn j)
    exact mul_le_mul_of_nonneg_left (hB (m - j) (Nat.sub_le m j)) hcnn
  exact le_trans hstep1 (le_trans hstep2 hstep3)

end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.iterFamilyB_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

/-- Elementary comparison for the `D_θ`-iterates of the factor `2 cos(2θ)`.

Given nonnegative families `A`, `D` and a dominating family `cB ≥ 0` with `A j ≤ cB j`, the
binomial convolution `∑_j C(m,j)² · A j · D (m-j)` is bounded by
`(∑_j 4^m · cB j) · (∑_k D k)`.

Indeed `C(m,j) ≤ 2^m`, so `C(m,j)² ≤ 4^m`, whence each summand is at most
`4^m · cB j · D (m-j)`; and since `m - j ∈ range (m+1)` for `j ∈ range (m+1)` and all `D k ≥ 0`,
each `D (m-j)` is at most `∑_k D k`, the factor `4^m · cB j` being nonnegative. -/
private theorem sum_choose_sq_mul_le {A D cB : ℕ → ℝ} (m : ℕ)
    (hA : ∀ j, 0 ≤ A j) (hD : ∀ k, 0 ≤ D k)
    (hcB : ∀ j, A j ≤ cB j) (hcBnn : ∀ j, 0 ≤ cB j) :
    (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) ^ 2 * (A j * D (m - j)))
      ≤ (∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cB j) *
        (∑ k ∈ Finset.range (m + 1), D k) := by
  have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ m := pow_nonneg (by norm_num) m
  have hchoose : ∀ j, (m.choose j : ℝ) ^ 2 ≤ (4 : ℝ) ^ m := by
    intro j
    have h1 : (m.choose j : ℝ) ≤ (2 : ℝ) ^ m := by
      exact_mod_cast Nat.choose_le_two_pow m j
    have h0 : (0 : ℝ) ≤ (m.choose j : ℝ) := Nat.cast_nonneg _
    calc (m.choose j : ℝ) ^ 2 ≤ ((2 : ℝ) ^ m) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = (4 : ℝ) ^ m := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  have hjmem : ∀ j ∈ Finset.range (m + 1), m - j ∈ Finset.range (m + 1) := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  calc (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) ^ 2 * (A j * D (m - j)))
      ≤ ∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cB j * D (m - j) := by
        apply Finset.sum_le_sum
        intro j _
        have hA' : 0 ≤ A j := hA j
        have hD' : 0 ≤ D (m - j) := hD _
        calc (m.choose j : ℝ) ^ 2 * (A j * D (m - j))
            ≤ (4 : ℝ) ^ m * (cB j * D (m - j)) :=
              mul_le_mul (hchoose j) (mul_le_mul_of_nonneg_right (hcB j) hD')
                (mul_nonneg hA' hD') h4
          _ = (4 : ℝ) ^ m * cB j * D (m - j) := by ring
    _ ≤ ∑ j ∈ Finset.range (m + 1),
          (4 : ℝ) ^ m * cB j * (∑ k ∈ Finset.range (m + 1), D k) := by
        apply Finset.sum_le_sum
        intro j hj
        have hs := Finset.single_le_sum (f := D) (fun i _ => hD i) (hjmem j hj)
        exact mul_le_mul_of_nonneg_left hs (mul_nonneg h4 (hcBnn j))
    _ = (∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cB j) *
          (∑ k ∈ Finset.range (m + 1), D k) := by
        rw [Finset.sum_mul]

theorem iterFamilyB_le {cB : ℕ → ℝ}
    (hcB : ∀ j θ, (Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2 ≤ cB j)
    (hcBnn : ∀ j, 0 ≤ cB j) (m : ℕ) (α : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (g : ℝ → ℝ) :
    (∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ)) ^ 2 *
        ((Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2
          * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2))
      * Work.FTS.EllipticEst.sGam α θ
      ≤ (∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cB j) *
        (∑ k ∈ Finset.range (m + 1),
            (Work.Elliptic.Dth1Iter k g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ) := by
  have hsGam : 0 ≤ Work.FTS.EllipticEst.sGam α θ := by
    rw [Work.FTS.EllipticEst.sGam]
    apply Real.rpow_nonneg
    apply Real.sin_nonneg_of_mem_Icc
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hA : ∀ j, 0 ≤ (Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2 :=
    fun j => sq_nonneg _
  have hD : ∀ k, 0 ≤ (Work.Elliptic.Dth1Iter k g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ :=
    fun k => mul_nonneg (sq_nonneg _) hsGam
  have hkey := sum_choose_sq_mul_le (m := m)
    (A := fun j => (Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2)
    (D := fun k => (Work.Elliptic.Dth1Iter k g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ)
    (cB := cB) hA hD (fun j => hcB j θ) hcBnn
  calc (∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ)) ^ 2 *
        ((Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2
          * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2)) * Work.FTS.EllipticEst.sGam α θ
      = (∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ)) ^ 2 *
          ((Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2
            * ((Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ))) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ ≤ (∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cB j) *
        (∑ k ∈ Finset.range (m + 1),
            (Work.Elliptic.Dth1Iter k g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ) := hkey

end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.WeakMoment.Open.ULeIntegralDerivBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `|u θ| ≤ (π/2) · A` from `u 0 = 0` and `|u'| ≤ A`

Elementary integral form of the mean value inequality on the angular interval:

if `u` is `C^∞` on the open interval `(0, π/2)`, continuous on `Iθ = [0, π/2]`, vanishes at
`θ = 0`, and `|u'| ≤ A` on `(0, π/2)`, then `|u θ| ≤ (π/2) · A` for every `θ ∈ (0, π/2)`.

Proof: Newton–Leibniz on `[0, θ]` (`∫_0^θ u' = u θ - u 0 = u θ`, the derivative being
integrable there because it is continuous on `(0, θ]` and bounded by `A`), followed by the
standard bound `|∫_0^θ u'| ≤ A · θ ≤ A · (π/2)`.
-/

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.WeakMoment.Open

theorem ULeIntegralDerivBound {u : ℝ → ℝ} {A : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hcont : ContinuousOn u Work.Spaces.Iθ) (h0 : u 0 = 0) (hA0 : 0 ≤ A)
    (hA : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv u θ| ≤ A) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u θ| ≤ (Real.pi / 2) * A := by
  intro θ hθ
  have hθ0 : (0 : ℝ) < θ := hθ.1
  have hθπ : θ < Real.pi / 2 := hθ.2
  -- `u` is continuous on the closed interval `[0, π/2]`.
  have hcont' : ContinuousOn u (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    simpa only [Work.Spaces.Iθ] using hcont
  have hcontIcc : ContinuousOn u (Set.Icc 0 θ) :=
    hcont'.mono (fun x hx => ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 hθπ)⟩)
  -- `u` is differentiable on `(0, θ)` with derivative `deriv u`.
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) θ, HasDerivAt u (deriv u x) x := by
    intro x hx
    have hxπ : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, lt_trans hx.2 hθπ⟩
    have hnhds : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 x := isOpen_Ioo.mem_nhds hxπ
    have hd : DifferentiableAt ℝ u x :=
      ((hsm 1).differentiableOn (by norm_num) x hxπ).differentiableAt hnhds
    exact hd.hasDerivAt
  -- `deriv u` is continuous on `(0, θ]` (it is `C¹` on `(0, π/2)`).
  have hderivCont : ContinuousOn (deriv u) (Set.Ioc 0 θ) := by
    have hcd : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hsm 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact hcd.continuousOn.mono (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hθπ⟩)
  -- hence it is integrable there (bounded by `A`, and the interval has finite measure).
  have hIntOn : IntegrableOn (deriv u) (Set.Ioc (0 : ℝ) θ) := by
    refine IntegrableOn.of_bound ?_
      (hderivCont.aestronglyMeasurable (μ := volume) measurableSet_Ioc) A ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall (fun x hx => ?_)
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, lt_of_le_of_lt hx.2 hθπ⟩
      simpa [Real.norm_eq_abs] using hA x hx'
  have hint : IntervalIntegrable (deriv u) volume (0 : ℝ) θ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hθ0.le).mpr hIntOn
  -- Newton–Leibniz on `[0, θ]`.
  have hFTC : ∫ x in (0 : ℝ)..θ, deriv u x = u θ - u 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ0.le hcontIcc hderiv hint
  -- the triangle inequality for the integral, with the pointwise bound `|u'| ≤ A`.
  have hnorm : ‖u θ‖ ≤ A * θ := by
    have hb : ∀ x ∈ Set.uIoc (0 : ℝ) θ, ‖deriv u x‖ ≤ A := by
      intro x hx
      rw [uIoc_of_le hθ0.le] at hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, lt_of_le_of_lt hx.2 hθπ⟩
      simpa [Real.norm_eq_abs] using hA x hx'
    have h1 : ‖∫ x in (0 : ℝ)..θ, deriv u x‖ ≤ A * |θ - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [hFTC, h0, sub_zero] at h1
    rwa [sub_zero, abs_of_pos hθ0] at h1
  have h2 : |u θ| ≤ A * θ := by
    rw [← Real.norm_eq_abs]; exact hnorm
  have h3 : A * θ ≤ (Real.pi / 2) * A := by
    have := mul_le_mul_of_nonneg_left (le_of_lt hθπ) hA0
    linarith
  linarith

end Work.FTS.EllipticEst.WeakMoment.Open
end
-- ===== merged: Submission.Work.FTS.EllipticEst.aesm_F_mul_Psi_of_sol =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Auxiliary lemmas -/



/-- `Work.Spaces.pthIter` preserves `C^∞`-smoothness on an open set. -/
theorem contDiffOn_uncurry_pthIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (k : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pthIter k G)) V := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Work.Spaces.pthIter_succ]; exact Work.Spaces.contDiffOn_uncurry_pth hV ih



/-! ## The main lemma -/


end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open =====
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

/-- Almost everywhere strong measurability of a function which is only known to be continuous
on the open quadrant `(0,∞) × (0,π/2)`, with respect to the product of Lebesgue measure
restricted to `(a,b]` and to `Iθ = [0,π/2]`.

Since `0 ≤ a` forces `(a,b] ⊆ (0,∞)`, the domain `(a,b] × Iθ` is covered by the open quadrant
`(0,∞) × (0,π/2)` together with the null set `(a,b] × {0,π/2}`.  Hence the hypothesis of
continuity on the open quadrant already gives almost everywhere strong measurability, and the
result for the larger set `Iz = [0,∞)` (proved in `Work.Spaces.aesm_of_continuousOn_Qd`) is
transferred by monotonicity of the restricted measure. -/
theorem aesm_uncurry_restrict_open (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) {a b : ℝ} (ha : 0 ≤ a) :
    MeasureTheory.AEStronglyMeasurable g
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- `0 ≤ a` makes the half-open interval `(a,b]` a subset of `Iz = [0,∞)`.
  have hA : Set.Ioc a b ⊆ Work.Spaces.Iz :=
    fun x hx => le_of_lt (lt_of_le_of_lt ha hx.1)
  have hmain := Work.Spaces.aesm_of_continuousOn_Qd g hg
  -- Write both product measures as restrictions of the planar Lebesgue measure.
  rw [MeasureTheory.Measure.prod_restrict (Set.Ioc a b) Work.Spaces.Iθ]
  rw [MeasureTheory.Measure.prod_restrict Work.Spaces.Iz Work.Spaces.Iθ] at hmain
  exact hmain.mono_measure
    (MeasureTheory.Measure.restrict_mono (Set.prod_mono hA (subset_refl _)) le_rfl)

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.bslOp_sub =====
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
set_option linter.unusedSimpArgs false

theorem bslOp_sub (α : ℝ) (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    Work.Elliptic.bslOp α (fun z θ => Ψ z θ - Φ z θ) z θ
      = Work.Elliptic.bslOp α Ψ z θ - Work.Elliptic.bslOp α Φ z θ := by
  have hsub : (fun z θ => Ψ z θ - Φ z θ) = fun z θ => Ψ z θ + (-Φ) z θ := by
    funext a b; simp [sub_eq_add_neg]
  rw [hsub, Work.Elliptic.bslOp_add α Ψ (-Φ) z θ hθ hΨ hΦ.neg]
  rw [congrFun (congrFun (bslOp_neg α Φ) z) θ]
  ring

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-- **Sharp Hardy on `[0,π/2]` with the shift `2`, correction against the *same* weight.**

For `0 ≤ η < 1` there is `C` with: for every `f : ℝ → ℝ` of class `C¹` on `[0,π/2]` with
`f 0 = 0`, `f (π/2) = 0`,

  `∫_0^{π/2} f² / sin(2θ)^{2+η} ≤ 1/(1+η)² ∫_0^{π/2} (f')² / sin(2θ)^η + C ∫_0^{π/2} f² / sin(2θ)^η`.

The constant `1/(1+η)²` is *sharp*: for the power weight it is the classical sharp value
`4/(1+η)²` on the half-line, and the substitution `sin(2θ) ≈ 2θ` (`sin(2θ) = 2θ` to first order)
contributes the factor `2^{-(2+η)}·2^{η} = 1/4`.  The correction term carries the *same* weight
`sin(2θ)^{-η}` as the derivative term (not the unweighted `H¹`-norm as in
`Work.Elliptic.sharp_hardy_sin_two`).

Derivation from what is already in the repository: apply the proved
`Work.Elliptic.half_sharp_hardy` (exactly this inequality integrated over `(0,π/4)`, with the
constant `1/(1+η)²` and the correction `C ∫ f² sin(2θ)^{-η}`) to `f`, and again to the reflected
function `f̃ θ = f (π/2 - θ)`; since `sin(2(π/2-θ)) = sin(2θ)`, `f̃ 0 = f (π/2) = 0` and
`f̃ (π/2) = f 0 = 0`, the two halves add up to the full interval `Iθ = Icc 0 (π/2)`. -/
theorem hardy_shift_two_same_weight (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, f θ ^ 2 / (Real.sin (2 * θ)) ^ (2 + η))
        ≤ 1 / (η + 1) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 / (Real.sin (2 * θ)) ^ η)
          + C * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 / (Real.sin (2 * θ)) ^ η) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.Elliptic.half_sharp_hardy hη0 hη1
  refine ⟨C0, hC0pos, fun f hf hf0 hfpi => ?_⟩
  have keyI : ∀ h : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, h θ) = ∫ θ in (0:ℝ)..(Real.pi/2), h θ := by
    intro h
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)]
  have hsin_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2*θ) := by
    intro θ hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hdiv : ∀ (a : ℝ → ℝ),
      (∫ θ in Work.Spaces.Iθ, a θ / (Real.sin (2*θ))^(2+η))
        = ∫ θ in Work.Spaces.Iθ, a θ * (Real.sin (2*θ))^(-(2+η)) := by
    intro a
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro θ hθ
    show a θ / (Real.sin (2*θ))^(2+η) = a θ * (Real.sin (2*θ))^(-(2+η))
    rw [div_eq_mul_inv, Real.rpow_neg (hsin_nn θ hθ) (2+η)]
  have hdiv2 : ∀ (a : ℝ → ℝ),
      (∫ θ in Work.Spaces.Iθ, a θ / (Real.sin (2*θ))^η)
        = ∫ θ in Work.Spaces.Iθ, a θ * (Real.sin (2*θ))^(-η) := by
    intro a
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro θ hθ
    show a θ / (Real.sin (2*θ))^η = a θ * (Real.sin (2*θ))^(-η)
    rw [div_eq_mul_inv, Real.rpow_neg (hsin_nn θ hθ) η]
  rw [hdiv (fun θ => f θ ^ 2), hdiv2 (fun θ => (deriv f θ) ^ 2), hdiv2 (fun θ => f θ ^ 2)]
  simp only [keyI]
  -- integrability of the five weighted integrands, and the two halves
  obtain ⟨hIL, hIN, hIP, hIM, hIQ⟩ := Work.Elliptic.sin_weight_integrable hη0 hη1 hf hf0 hfpi
  have hsub1 : Set.uIcc (0:ℝ) (Real.pi/4) ⊆ Set.uIcc 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/4),
        Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)]
    exact Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])
  have hsub2 : Set.uIcc (Real.pi/4) (Real.pi/2) ⊆ Set.uIcc 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : Real.pi/4 ≤ Real.pi/2),
        Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)]
    exact Set.Icc_subset_Icc (by positivity) le_rfl
  have hIL1 := hIL.mono_set hsub1
  have hIL2 := hIL.mono_set hsub2
  have hIN1 := hIN.mono_set hsub1
  have hIN2 := hIN.mono_set hsub2
  have hIP1 := hIP.mono_set hsub1
  have hIP2 := hIP.mono_set hsub2
  have hleft := hC0 f hf hf0 hfpi
  -- right half by reflection
  set g : ℝ → ℝ := fun φ => f (Real.pi/2 - φ) with hg_def
  have hg : ContDiffOn ℝ 1 g (Set.Icc 0 (Real.pi/2)) := by
    have h1 : ContDiffOn ℝ 1 (fun φ : ℝ => Real.pi/2 - φ) (Set.Icc 0 (Real.pi/2)) := by fun_prop
    have h2 : Set.MapsTo (fun φ : ℝ => Real.pi/2 - φ) (Set.Icc 0 (Real.pi/2)) (Set.Icc 0 (Real.pi/2)) := by
      intro x hx; simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.2, Real.pi_pos], by linarith [hx.1]⟩
    have := hf.comp h1 h2
    simpa only [hg_def, Function.comp_def] using this
  have hg0 : g 0 = 0 := by rw [hg_def]; simpa using hfpi
  have hgpi : g (Real.pi/2) = 0 := by rw [hg_def]; simpa using hf0
  have hright_raw := hC0 g hg hg0 hgpi
  have hr1 : (∫ φ in (0:ℝ)..(Real.pi/4), g φ ^ 2 * (Real.sin (2*φ)) ^ (-(2+η)))
      = ∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)) := by
    have hcomp := intervalIntegral.integral_comp_sub_left (fun θ => f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η))) (Real.pi/2)
        (a := (0:ℝ)) (b := Real.pi/4)
    rw [show Real.pi/2 - Real.pi/4 = Real.pi/4 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro φ hφ
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/4)] at hφ
    simp only [hg_def]
    rw [show 2*(Real.pi/2 - φ) = Real.pi - 2*φ by ring, Real.sin_pi_sub]
  have hr2 : (∫ φ in (0:ℝ)..(Real.pi/4), (deriv g φ) ^ 2 * (Real.sin (2*φ)) ^ (-η))
      = ∫ θ in (Real.pi/4)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η) := by
    have hcomp := intervalIntegral.integral_comp_sub_left (fun θ => (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η)) (Real.pi/2)
        (a := (0:ℝ)) (b := Real.pi/4)
    rw [show Real.pi/2 - Real.pi/4 = Real.pi/4 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro φ hφ
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/4)] at hφ
    show deriv g φ ^ 2 * (Real.sin (2*φ)) ^ (-η)
        = deriv f (Real.pi/2 - φ) ^ 2 * (Real.sin (2*(Real.pi/2 - φ))) ^ (-η)
    have hd : deriv g φ = - deriv f (Real.pi/2 - φ) := by
      rw [hg_def]; exact deriv_comp_const_sub f (Real.pi/2) φ
    rw [hd, show 2*(Real.pi/2 - φ) = Real.pi - 2*φ by ring, Real.sin_pi_sub]
    ring
  have hr3 : (∫ φ in (0:ℝ)..(Real.pi/4), g φ ^ 2 * (Real.sin (2*φ)) ^ (-η))
      = ∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η) := by
    have hcomp := intervalIntegral.integral_comp_sub_left (fun θ => f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) (Real.pi/2)
        (a := (0:ℝ)) (b := Real.pi/4)
    rw [show Real.pi/2 - Real.pi/4 = Real.pi/4 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro φ hφ
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/4)] at hφ
    simp only [hg_def]
    rw [show 2*(Real.pi/2 - φ) = Real.pi - 2*φ by ring, Real.sin_pi_sub]
  have hright : (∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
      ≤ 1/(1+η)^2 * (∫ θ in (Real.pi/4)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
        + C0 * (∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
    rw [← hr1, ← hr2, ← hr3]
    exact hright_raw
  have hsum : (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
        + (∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
      ≤ 1/(1+η)^2 * ((∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
          + (∫ θ in (Real.pi/4)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η)))
        + C0 * ((∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))
          + (∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))) := by
    linarith [hleft, hright]
  have e1 := intervalIntegral.integral_add_adjacent_intervals hIL1 hIL2
  have e2 := intervalIntegral.integral_add_adjacent_intervals hIN1 hIN2
  have e3 := intervalIntegral.integral_add_adjacent_intervals hIP1 hIP2
  have hkey : (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
      ≤ 1/(1+η)^2 * (∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
    rw [← e1, ← e2, ← e3]
    linarith [hsum]
  rw [show (1:ℝ) / (η + 1) ^ 2 = 1 / (1 + η) ^ 2 by ring]
  exact hkey

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Baux.DthIter_M_recursion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The recursion of `D_θ^k` applied to the operator `L`

The target `Work.FTS.EllipticEst.remov.Baux.DthIter_M_recursion` records that the angular
operator `D_θ = sin(2θ) ∂_θ` acts on the multiplier

`M Ψ = ∂_θ (tan θ · Ψ) - 6 Ψ - α(5+α) D_z Ψ`

through the twisted binomial expansion `D_θ^k (tan²θ · X) = tan²θ · (D_θ + 4)^k X + D_θ^k X`.

Everything is reduced to the one-dimensional operator `Work.Spaces.Lop u θ = sin(2θ) u'(θ)`
(the action of `D_θ` on `θ`-slices) and the *pointwise* finite-order calculus for it:
`LopLeibnizPoint` (the Leibniz rule at a point), the additivity `Lop_iter_add_at`, the
congruence `Lop_iter_congr_at` and the eigenvalue identity `Lop^k (tan²) = 4^k tan²`.
-/

namespace Work.FTS.EllipticEst.remov.Baux

open scoped Real Topology
open Filter Set

/-- `((N : ℕ) : ℕ∞ω)` for the finite order `N`. -/
abbrev DmrOrd (N : ℕ) : WithTop ℕ∞ := ((N : ℕ) : WithTop ℕ∞)

namespace Dmr

/-! ## Elementary facts about the angular operator `Lop` -/


/-- Iterates of `Lop` commute with multiplication by a constant. -/
theorem Lop_iter_const_mul (c : ℝ) (u : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.Lop^[i] (fun θ => c * u θ) = fun θ => c * Work.Spaces.Lop^[i] u θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      funext θ
      simp only [Work.Spaces.Lop]
      rw [deriv_const_mul_field (u := c) (v := Work.Spaces.Lop^[n] u) (x := θ)]
      ring

/-- `Lop`-iterates respect eventual equality: they only see the germ of the function. -/
theorem Lop_iter_eventuallyEq {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (i : ℕ) :
    Work.Spaces.Lop^[i] u =ᶠ[𝓝 θ] Work.Spaces.Lop^[i] v := by
  induction i with
  | zero => simpa using h
  | succ n ih =>
      change ∀ᶠ x in 𝓝 θ, Work.Spaces.Lop^[n] u x = Work.Spaces.Lop^[n] v x at ih
      rw [Filter.eventually_iff_exists_mem] at ih
      obtain ⟨s, hs, hsEq⟩ := ih
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change ∀ᶠ x in 𝓝 θ, Real.sin (2 * x) * deriv (Work.Spaces.Lop^[n] u) x
          = Real.sin (2 * x) * deriv (Work.Spaces.Lop^[n] v) x
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨interior s, interior_mem_nhds.mpr hs, fun x hx => ?_⟩
      have hg : Work.Spaces.Lop^[n] u =ᶠ[𝓝 x] Work.Spaces.Lop^[n] v :=
        Filter.eventually_iff_exists_mem.mpr
          ⟨interior s, isOpen_interior.mem_nhds hx, fun y hy => hsEq y (interior_subset hy)⟩
      congr 1
      exact Filter.EventuallyEq.deriv_eq hg

/-- `Lop`-iterates respect eventual equality, pointwise form. -/
theorem Lop_iter_congr_at {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (i : ℕ) :
    Work.Spaces.Lop^[i] u θ = Work.Spaces.Lop^[i] v θ :=
  (Lop_iter_eventuallyEq h i).eq_of_nhds



/-! ## A finite-sum reindexing

`∑_{a ≤ k} C(k,a) 4^a X(k-a) = ∑_{j ≤ k} C(k,j) 4^{k-j} X j`: the reflection of the index
range `range (k+1)`, using `Nat.choose_symm`. -/


/-- `DmrOrd` is monotone in the natural number. -/
theorem DmrOrd_le {a b : ℕ} (h : a ≤ b) : DmrOrd a ≤ DmrOrd b := by
  simp only [DmrOrd]; exact_mod_cast h


/-- A finite order is not the smooth order `∞`. -/
theorem DmrOrd_ne_infty (n : ℕ) : DmrOrd n ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ne_of_lt (Work.FTS.EllipticEst.RPFresh.DivSinOpen.LopOrd_lt_omega n)

/-- `Lop^[i]` is subtractive at a point where both arguments are `C^i`. -/
theorem Lop_iter_sub_at (i : ℕ) :
    ∀ {u v : ℝ → ℝ} {θ : ℝ}, ContDiffAt ℝ (DmrOrd i) u θ →
      ContDiffAt ℝ (DmrOrd i) v θ →
      Work.Spaces.Lop^[i] (u - v) θ = Work.Spaces.Lop^[i] u θ - Work.Spaces.Lop^[i] v θ := by
  induction i with
  | zero => intro u v θ hu hv; rfl
  | succ n ih =>
      intro u v θ hu hv
      have hle : DmrOrd n ≤ DmrOrd (n + 1) := DmrOrd_le (Nat.le_succ n)
      obtain ⟨s, hs, hscd⟩ := hu.contDiffOn (le_rfl : DmrOrd (n + 1) ≤ DmrOrd (n + 1))
        (fun h => absurd h (DmrOrd_ne_infty (n + 1)))
      obtain ⟨t, ht, htcd⟩ := hv.contDiffOn (le_rfl : DmrOrd (n + 1) ≤ DmrOrd (n + 1))
        (fun h => absurd h (DmrOrd_ne_infty (n + 1)))
      obtain ⟨W, hWst, hWopen, hθW⟩ := mem_nhds_iff.mp (Filter.inter_mem hs ht)
      have hev : Work.Spaces.Lop^[n] (u - v)
          =ᶠ[𝓝 θ] (Work.Spaces.Lop^[n] u - Work.Spaces.Lop^[n] v) := by
        change ∀ᶠ x in 𝓝 θ, Work.Spaces.Lop^[n] (u - v) x
          = (Work.Spaces.Lop^[n] u - Work.Spaces.Lop^[n] v) x
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨W, hWopen.mem_nhds hθW, fun x hx => ?_⟩
        have h1 : ContDiffAt ℝ (DmrOrd (n + 1)) u x :=
          (hscd.mono (fun y hy => (hWst hy).1)).contDiffAt (hWopen.mem_nhds hx)
        have h2 : ContDiffAt ℝ (DmrOrd (n + 1)) v x :=
          (htcd.mono (fun y hy => (hWst hy).2)).contDiffAt (hWopen.mem_nhds hx)
        exact ih (h1.of_le hle) (h2.of_le hle)
      have hdu : DifferentiableAt ℝ (Work.Spaces.Lop^[n] u) θ :=
        (Work.FTS.EllipticEst.RPFresh.DivSinOpen.Lop_iter_contDiffAt n (n + 1)
          (Nat.le_succ n) hu).differentiableAt (by simp [DmrOrd])
      have hdv : DifferentiableAt ℝ (Work.Spaces.Lop^[n] v) θ :=
        (Work.FTS.EllipticEst.RPFresh.DivSinOpen.Lop_iter_contDiffAt n (n + 1)
          (Nat.le_succ n) hv).differentiableAt (by simp [DmrOrd])
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply']
      show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[n] (u - v)) θ
          = Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[n] u) θ
            - Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[n] v) θ
      rw [Filter.EventuallyEq.deriv_eq hev, deriv_sub hdu hdv]
      ring






end Dmr


end Work.FTS.EllipticEst.remov.Baux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Step4.slice_step4_identity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.Step4

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ### The null set: `[0, π/2]` versus `(0, π/2)` -/

/-- `[0, π/2]` and `(0, π/2)` agree up to a null set. -/
private lemma ae_eq_Icc_Ioo :
    (Set.Icc 0 (Real.pi / 2) : Set ℝ) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · have hsub : Set.Icc 0 (Real.pi / 2) \ Set.Ioo 0 (Real.pi / 2) ⊆ ({0, Real.pi / 2} : Set ℝ) := by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx ⊢
      rcases eq_or_lt_of_le hx.1.1 with h | h
      · exact Or.inl h.symm
      · refine Or.inr ?_
        by_contra hne
        exact hx.2 ⟨h, lt_of_le_of_ne hx.1.2 hne⟩
    have hnull : volume ({0, Real.pi / 2} : Set ℝ) = 0 :=
      (Set.Finite.insert (0 : ℝ) (Set.finite_singleton (Real.pi / 2))).measure_zero _
    exact MeasureTheory.measure_mono_null hsub hnull
  · have h0 : Set.Ioo 0 (Real.pi / 2) \ Set.Icc 0 (Real.pi / 2) = ∅ :=
      Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self
    rw [h0, MeasureTheory.measure_empty]

/-- Consequently `volume.restrict Iθ = volume.restrict (0, π/2)`. -/
private lemma restrict_Iθ_eq_Ioo :
    (volume.restrict Work.Spaces.Iθ : Measure ℝ)
      = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
  simpa [Work.Spaces.Iθ] using MeasureTheory.Measure.restrict_congr_set ae_eq_Icc_Ioo

/-! ### The identity -/

theorem slice_step4_identity (γ : ℝ) (hγ : γ ≤ 2) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    (hA : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hD : MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hC1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
      = - (∫ θ in Work.Spaces.Iθ, deriv g θ * deriv (deriv (deriv u)) θ *
            Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + (∫ θ in Work.Spaces.Iθ, deriv (deriv (fun t => Real.tan t * u t)) θ *
            deriv (deriv (deriv u)) θ * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        - 6 * (∫ θ in Work.Spaces.Iθ, deriv u θ * deriv (deriv (deriv u)) θ *
            Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
  -- Work on the open interval, where all the functions involved are continuous.
  set s : Set ℝ := Set.Ioo 0 (Real.pi / 2) with hs_def
  have hsopen : IsOpen s := by rw [hs_def]; exact isOpen_Ioo
  have hsmeas : MeasurableSet s := hsopen.measurableSet
  have hset : (Work.Spaces.Iθ : Set ℝ) =ᵐ[volume] s := by
    rw [hs_def]; exact ae_eq_Icc_Ioo
  have hrestrict : (volume.restrict Work.Spaces.Iθ : Measure ℝ) = volume.restrict s := by
    rw [hs_def]; exact restrict_Iθ_eq_Ioo
  -- The weight `σ = sin(2θ)^{2-γ}` on the open interval.
  have hsinpos : ∀ θ ∈ s, 0 < Real.sin (2 * θ) := by
    intro θ hθ
    rw [hs_def] at hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hκ0 : ∀ θ ∈ s, 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    fun θ hθ => Real.rpow_nonneg (le_of_lt (hsinpos θ hθ)) _
  have hκ1 : ∀ θ ∈ s, Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 := by
    intro θ hθ
    exact Real.rpow_le_one (le_of_lt (hsinpos θ hθ)) (Real.sin_le_one _) (by linarith)
  have hmκ : AEStronglyMeasurable (fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (volume.restrict s) := by
    refine (ContinuousOn.rpow_const ?_ ?_).aestronglyMeasurable hsmeas
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro θ hθ
      exact Or.inl (ne_of_gt (hsinpos θ hθ))
  -- The three `u`-derivatives and `(tan θ·u)''` are continuous on the open interval.
  have hT : ContDiffOn ℝ 0 (fun θ => deriv (deriv (deriv u)) θ) s := by
    have h1 : ContDiffOn ℝ 2 (deriv u) s := hu.deriv_of_isOpen hsopen (by norm_num)
    have h2 : ContDiffOn ℝ 1 (deriv (deriv u)) s := h1.deriv_of_isOpen hsopen (by norm_num)
    exact h2.deriv_of_isOpen hsopen (by norm_num)
  have hmv : AEStronglyMeasurable (fun θ => deriv (deriv (deriv u)) θ)
      (volume.restrict s) := hT.continuousOn.aestronglyMeasurable hsmeas
  have hU : ContinuousOn (fun θ => deriv u θ) s :=
    hu.continuousOn_deriv_of_isOpen hsopen (by norm_num)
  have hmδ : AEStronglyMeasurable (fun θ => deriv u θ) (volume.restrict s) :=
    hU.aestronglyMeasurable hsmeas
  have htu : ContDiffOn ℝ 2 (fun t => Real.tan t * u t) s := by
    intro θ hθ
    rw [hs_def] at hθ
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩)
    exact (((Real.contDiffAt_tan.mpr hcos).mul
      ((hu.contDiffAt (hsopen.mem_nhds hθ)).of_le (by norm_num))).contDiffWithinAt)
  have hβ : ContDiffOn ℝ 0 (fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ) s := by
    have h1 : ContDiffOn ℝ 1 (deriv (fun t => Real.tan t * u t)) s :=
      htu.deriv_of_isOpen hsopen (by norm_num)
    exact h1.deriv_of_isOpen hsopen (by norm_num)
  have hmβ : AEStronglyMeasurable (fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ)
      (volume.restrict s) := hβ.continuousOn.aestronglyMeasurable hsmeas
  -- `g'` agrees on `s` with the continuous function `-u''' + (tan θ·u)'' - 6u'`.
  have hmα : AEStronglyMeasurable (fun θ => deriv g θ) (volume.restrict s) := by
    have hF : ContinuousOn (fun θ => -deriv (deriv (deriv u)) θ
        + deriv (deriv (fun t => Real.tan t * u t)) θ - 6 * deriv u θ) s :=
      ((hT.continuousOn.neg).add hβ.continuousOn).sub (hU.const_mul 6)
    refine (hF.aestronglyMeasurable hsmeas).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hsmeas] with θ hθ
    exact (slice_gprime_ident u g hu hode θ hθ).symm
  -- The pointwise relation on `s`, in the shape used by the integral lemma.
  have hrel : ∀ θ ∈ s, deriv (deriv (deriv u)) θ = -deriv g θ
      + deriv (deriv (fun t => Real.tan t * u t)) θ - 6 * deriv u θ := by
    intro θ hθ
    have h := slice_gprime_ident u g hu hode θ hθ
    linarith
  -- Integrability, transported from `Iθ` to the open interval.
  have hIv : IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) s := by
    show MeasureTheory.Integrable _ (volume.restrict s)
    rw [← hrestrict]
    exact hA
  have hIα : IntegrableOn (fun θ => (deriv g θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) s := by
    show MeasureTheory.Integrable _ (volume.restrict s)
    rw [← hrestrict]
    exact hD
  have hU2 : IntegrableOn (fun θ => (deriv u θ) ^ 2) s := by
    show MeasureTheory.Integrable _ (volume.restrict s)
    rw [← hrestrict]
    exact hC1
  have hIδ : IntegrableOn (fun θ => (deriv u θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) s := by
    show MeasureTheory.Integrable _ (volume.restrict s)
    refine MeasureTheory.Integrable.mono' (g := fun θ => (deriv u θ) ^ 2) hU2
      ((hmδ.pow 2).mul hmκ) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hsmeas] with θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hκ0 θ hθ), abs_of_nonneg (sq_nonneg _)]
    nlinarith [hκ1 θ hθ, sq_nonneg (deriv u θ)]
  -- The abstract integral identity, then back to `Iθ`.
  have hmain := integral_sq_eq_of_rel (s := s) (α := fun θ => deriv g θ)
    (β := fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ)
    (δ := fun θ => deriv u θ) (v := fun θ => deriv (deriv (deriv u)) θ)
    (κ := fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ))
    hsmeas hκ0 hκ1 hrel hmα hmv hmδ hmκ hIα hIv hIδ
  rw [MeasureTheory.setIntegral_congr_set hset, MeasureTheory.setIntegral_congr_set hset,
    MeasureTheory.setIntegral_congr_set hset, MeasureTheory.setIntegral_congr_set hset]
  exact hmain

end Work.FTS.EllipticEst.remov.Step4
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarHyp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The hypothesis bundle and the right-hand side of the far-region estimate

The far-region angular estimate `TopCoreB.slice_ang_far` of Elgindi's §"General ℋ^k case"
bounds the top angular derivative slot on `[3π/8, π/2]` by the *lower* slots, the source slot
and the three low-order quantities.  Everything the estimate needs is collected here, so that
the individual steps of the proof can be stated (and proved) independently of the target.

Vocabulary (all in `Work.FTS.EllipticEst.remov.TopCoreB`):

* `qW k γ θ = sin(2θ)^{2k-γ}` (the weight of the top slot; already in `FarDefs`),
* `vF u = u / cos θ` (already in `FarDefs`),
* `farSet = Icc (3π/8) (π/2)` (the far window),
* `FarR k γ u g` — the right-hand side of the target (without the constant),
* `FarHyp k γ u g` — the hypotheses of the target.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false

/-- The far window `[3π/8, π/2]` of the angular estimate. -/
def farSet : Set ℝ := Set.Icc (3 * Real.pi / 8) (Real.pi / 2)

/-- The right-hand side of the far-region estimate (the target's parenthesised factor). -/
def FarR (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) : ℝ :=
  (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
    + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
    + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
    + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
    + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)

/-- The hypotheses of the far-region estimate, bundled. -/
def FarHyp (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) : Prop :=
  1 ≤ γ ∧ γ ≤ 5 / 4 ∧
  ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) ∧
  ContinuousOn u (Set.Icc 0 (Real.pi / 2)) ∧
  u 0 = 0 ∧ u (Real.pi / 2) = 0 ∧
  (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) ∧
  MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ ∧
  MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ ∧
  (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
      (fun θ => (iteratedDeriv j u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ) ∧
  MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
  MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ ∧
  MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ

/-- The far window sits inside `Iθ`. -/
theorem farSet_subset_Iθ : farSet ⊆ Work.Spaces.Iθ := by
  intro x hx
  exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩

section Projections

variable {k : ℕ} {γ : ℝ} {u g : ℝ → ℝ}

theorem FarHyp.hγ1 (h : FarHyp k γ u g) : 1 ≤ γ := h.1
theorem FarHyp.hγ2 (h : FarHyp k γ u g) : γ ≤ 5 / 4 := h.2.1
theorem FarHyp.huC (h : FarHyp k γ u g) :
    ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) := h.2.2.1
theorem FarHyp.hucont (h : FarHyp k γ u g) :
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) := h.2.2.2.1
theorem FarHyp.hu0 (h : FarHyp k γ u g) : u 0 = 0 := h.2.2.2.2.1
theorem FarHyp.hupi (h : FarHyp k γ u g) : u (Real.pi / 2) = 0 := h.2.2.2.2.2.1
theorem FarHyp.hg (h : FarHyp k γ u g) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ :=
  h.2.2.2.2.2.2.1
theorem FarHyp.hH1 (h : FarHyp k γ u g) :
    MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ := h.2.2.2.2.2.2.2.1
theorem FarHyp.hH2 (h : FarHyp k γ u g) :
    MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ :=
  h.2.2.2.2.2.2.2.2.1
theorem FarHyp.hH3 (h : FarHyp k γ u g) :
    ∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
      (fun θ => (iteratedDeriv j u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ :=
  h.2.2.2.2.2.2.2.2.2.1
theorem FarHyp.hH4 (h : FarHyp k γ u g) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
  h.2.2.2.2.2.2.2.2.2.2.1
theorem FarHyp.hH5 (h : FarHyp k γ u g) :
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ :=
  h.2.2.2.2.2.2.2.2.2.2.2.1
theorem FarHyp.hH6 (h : FarHyp k γ u g) :
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
  h.2.2.2.2.2.2.2.2.2.2.2.2

end Projections





/-- Monotonicity: a nonnegative density integrated over the far window is at most its integral
over `Iθ`. -/
theorem farIntegral_le_Iθ {f : ℝ → ℝ} (hf : MeasureTheory.IntegrableOn f Work.Spaces.Iθ)
    (hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ f θ) :
    ∫ θ in farSet, f θ ≤ ∫ θ in Work.Spaces.Iθ, f θ := by
  refine MeasureTheory.setIntegral_mono_set hf ?_ ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with x hx
    exact hnn x hx
  · exact Filter.Eventually.of_forall (fun x hx => farSet_subset_Iθ hx)

end Work.FTS.EllipticEst.remov.TopCoreB
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.mid_pointwise_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise bound in the "middle" angular window `[π/8, 3π/8]`

This file proves `Work.FTS.EllipticEst.remov.mid_pointwise_bound`: for `u` of class `C^{k+2}`
on `(0, π/2)` and `g = Lzero1 u`, the top derivative `u^{(k+2)}` at a point `θ` of the closed
window `[π/8, 3π/8]` is controlled by the lower derivatives of `u` at `θ` together with
`g^{(k)}(θ)`.

The mechanism is the exact expansion of `Lzero1 u = g` after differentiating `k` times
(`Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq`),

`u^{(k+2)} = ∑_{i ≤ k+1} C(k+1,i) (tan)^{(i)} u^{(k+1-i)} - 6 u^{(k)} - g^{(k)}`,

read as a pointwise relation on `Ioo 0 (π/2)`.  Since `tan` is smooth on a neighbourhood of the
window, all its derivatives up to `k+1` are bounded there, so the right hand side is a fixed
(finite) real linear combination of `u^{(0)}, …, u^{(k+1)}` and `g^{(k)}`.  Squaring and using
`(∑ a_j)^2 ≤ (card)·∑ a_j^2`-free reasoning — here simply `|x| ≤ √S` for every summand and
`√S · √S = S` — yields the stated quadratic bound.
-/

open scoped Real Topology

namespace Work.FTS.EllipticEst.remov





end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.near_pointwise_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise near-axis bound for the top derivative of the slice ODE

The slice ODE `g = Lzero1 u` reads `u'' = ∂_θ(tan θ · u) - 6u - g`, and differentiating it `k`
times (`Lzero1_iteratedDeriv_eq`) gives, at every `θ ∈ (0, π/2)`,

  `u^{(k+2)}(θ) = ∑_{i≤k+1} C(k+1,i)(tan)^{(i)}(θ) u^{(k+1-i)}(θ) - 6u^{(k)}(θ) - g^{(k)}(θ)`.

The interval `[0, π/8]` is contained in `(-π/2, π/2)`, where `tan` is analytic, so the finitely
many coefficient functions `(tan)^{(i)}`, `i ≤ k+1`, are continuous on it and therefore bounded
by a single constant `M` depending only on `k`.  Combining the identity with the elementary
finite-sum Cauchy–Schwarz inequality yields the stated pointwise bound for `θ ∈ (0, π/8)`.
-/

open scoped Real Topology
open Set Filter

namespace Work.FTS.EllipticEst.remov







end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice5_eqn_deriv2 =====
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

/-- `Lzero1 u` is `-u'' + (tan θ · u)' - 6u`, written in terms of `iteratedDeriv`. -/
lemma Lzero1_eq_iteratedDeriv (u : ℝ → ℝ) :
    Work.FTS.EllipticEst.Lzero1 u
      = -(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)
        - (fun t => 6 * u t) := by
  funext t
  have hd2 : deriv (fun s => deriv u s) t = iteratedDeriv 2 u t := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hd1 : deriv (fun s => Real.tan s * u s) t
      = iteratedDeriv 1 (fun s => Real.tan s * u s) t := by rw [iteratedDeriv_one]
  unfold Work.FTS.EllipticEst.Lzero1
  rw [hd2, hd1]
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]

/-- The second iterated derivative of `Lzero1 u` at an interior point:
`(Lzero1 u)'' = -u'''' + (tan θ · u)''' - 6u''`. -/
lemma iteratedDeriv_two_Lzero1 (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      iteratedDeriv 2 (Work.FTS.EllipticEst.Lzero1 u) θ
        = -iteratedDeriv 4 u θ
          + iteratedDeriv 3 (fun t => Real.tan t * u t) θ
          - 6 * iteratedDeriv 2 u θ := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 := by
    intro t ht
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩)
  have hcosθ : Real.cos θ ≠ 0 := hcos_ne θ hθ
  have huAt : ContDiffAt ℝ 4 u θ := hu.contDiffAt hIoo
  have huC1 : ContDiffAt ℝ 1 u θ := huAt.of_le (by norm_num)
  have huC2 : ContDiffAt ℝ 2 u θ := huAt.of_le (by norm_num)
  have huC3 : ContDiffAt ℝ 3 u θ := huAt.of_le (by norm_num)
  have htanC3 : ContDiffAt ℝ 3 Real.tan θ := Real.contDiffAt_tan.mpr hcosθ
  have htuC3 : ContDiffAt ℝ 3 (fun s => Real.tan s * u s) θ := htanC3.mul huC3
  have hu2C2 : ContDiffAt ℝ 2 (iteratedDeriv 2 u) θ :=
    contDiffAt_iteratedDeriv (f := u) (n := 4) (k := 2) huAt (by norm_num)
  have htu1C2 : ContDiffAt ℝ 2 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
    contDiffAt_iteratedDeriv (f := fun s => Real.tan s * u s) (n := 3) (k := 1) htuC3
      (by norm_num)
  rw [Lzero1_eq_iteratedDeriv]
  have hA : ContDiffAt ℝ 2
      (-(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
    (ContDiffAt.neg hu2C2).add htu1C2
  have hB : ContDiffAt ℝ 2 (fun t => 6 * u t) θ := contDiffAt_const.mul huC2
  rw [iteratedDeriv_sub hA hB]
  have hA1 : ContDiffAt ℝ 2 (-(iteratedDeriv 2 u)) θ := ContDiffAt.neg hu2C2
  have hA2 : ContDiffAt ℝ 2 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ := htu1C2
  rw [iteratedDeriv_add hA1 hA2, iteratedDeriv_neg, iteratedDeriv_const_mul (6 : ℝ) huC2]
  rw [itd_comp_two_val 2 u θ, itd_comp_two_val 1 (fun s => Real.tan s * u s) θ]

theorem slice5_eqn_deriv2 (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (deriv (deriv u))) θ + deriv (deriv g) θ
        = deriv (deriv (deriv (fun t => Real.tan t * u t))) θ - 6 * deriv (deriv u) θ := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  -- `g` agrees with `Lzero1 u` near every interior point
  have hcong : Work.FTS.EllipticEst.Lzero1 u =ᶠ[𝓝 θ] g := by
    filter_upwards [hIoo] with t ht
    exact hode t ht
  -- hence `g'' = (Lzero1 u)''` there
  have hg2 : deriv (deriv g) θ
      = iteratedDeriv 2 (Work.FTS.EllipticEst.Lzero1 u) θ := by
    rw [← itd_two_val g θ, ← Filter.EventuallyEq.iteratedDeriv_eq 2 hcong]
  have hL2 := iteratedDeriv_two_Lzero1 u hu θ hθ
  -- rewrite every `deriv`-tower as an `iteratedDeriv`
  rw [hg2, hL2, ← itd_four_val u θ, ← itd_three_val (fun t => Real.tan t * u t) θ,
    ← itd_two_val u θ]
  ring

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice5_idents =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open Filter

namespace Work.FTS.EllipticEst.remov

theorem slice5_idents (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ
        = -Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
          + 3 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          - 4 * Real.cos θ * (u θ / Real.cos θ)) ∧
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv u) θ = Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        - 5 * Real.cos θ * (u θ / Real.cos θ) - g θ) ∧
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (deriv u)) θ
        = Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
          - 4 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          + 5 * Real.sin θ * (u θ / Real.cos θ) - deriv g θ) ∧
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (deriv (deriv u))) θ
        = Real.sin θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
          - 3 * Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
          + 9 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
          + 5 * Real.cos θ * (u θ / Real.cos θ) - deriv (deriv g) θ) := by
  -- `cosBarIdents` gives the same four identities with `Lzero1 u` in place of `g`;
  -- `g` agrees with `Lzero1 u` on the whole interval, hence to first and second order
  -- near each interior point.
  have hCBI := cosBarIdents hu
  have hcong : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u =ᶠ[𝓝 θ] g := by
    intro θ hθ
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact hode t ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ hθ
    exact (hCBI θ hθ).1
  · intro θ hθ
    rw [(hCBI θ hθ).2.1, hode θ hθ]
  · intro θ hθ
    have hd : deriv (Work.FTS.EllipticEst.Lzero1 u) θ = deriv g θ :=
      (hcong θ hθ).deriv_eq
    rw [(hCBI θ hθ).2.2.1, hd]
  · intro θ hθ
    have hd : deriv (deriv (Work.FTS.EllipticEst.Lzero1 u)) θ = deriv (deriv g) θ :=
      ((hcong θ hθ).deriv).deriv_eq
    rw [(hCBI θ hθ).2.2.2, hd]

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.sliceY2Uniform =====
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

/-! ### The two first-order identities for `v = u / cos θ` -/

/-- On the open interval, `v = u / cos θ` has the derivative `(u' + u tan θ)/cos θ`. -/
private lemma Y2U_psi_deriv (u : ℝ → ℝ) (hu : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => u t / Real.cos t) θ
      = (deriv u θ + u θ * Real.tan θ) / Real.cos θ := by
  have hp : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩)
  have hu_at : ContDiffAt ℝ 1 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hd1 : HasDerivAt u (deriv u θ) θ :=
    (hu_at.differentiableAt (by norm_num)).hasDerivAt
  have hd2 : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have hd := hd1.div hd2 hcos
  have hd' : deriv (fun t => u t / Real.cos t) θ
      = (deriv u θ * Real.cos θ - u θ * (-Real.sin θ)) / Real.cos θ ^ 2 := hd.deriv
  rw [hd', Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- The exact form of the equation `Lzero1 u = g` in terms of `v = u / cos θ`:
`sin θ · v' = u'' + 5u + g` on the open interval. -/
private lemma Y2U_psi_ident (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin θ * deriv (fun t => u t / Real.cos t) θ = deriv (deriv u) θ + 5 * u θ + g θ := by
  have hp : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩)
  have hu_at : ContDiffAt ℝ 3 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hd1 : HasDerivAt u (deriv u θ) θ :=
    (((hu_at.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).differentiableAt
      (by norm_num))).hasDerivAt
  have htan : deriv (fun t => Real.tan t * u t) θ
      = (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ :=
    ((Real.hasDerivAt_tan hcos).mul hd1).deriv
  have hL : -(deriv (fun t => deriv u t) θ) + deriv (fun t => Real.tan t * u t) θ
      - 6 * u θ = g θ := by
    have h := hode θ hθ
    simpa [Work.FTS.EllipticEst.Lzero1] using h
  have hpsi := Y2U_psi_deriv u (hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)) hθ
  rw [hpsi, ← hL, htan, Real.tan_eq_sin_div_cos]
  field_simp
  ring_nf
  rw [Real.sin_sq]
  ring

/-! ### The two halves of the pointwise bound -/

/-- On `(0, π/4]` the coefficients of `v' = (u' + u tan θ)/cos θ` are bounded by `√2` and by
`1`, and `σ = sin(2θ)^{2-γ} ≤ 1`; hence `(v')²σ ≤ 4 (u'² + u²)`. -/
private lemma Y2U_left_bound (γ : ℝ) (_hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioc 0 (Real.pi / 4),
      (deriv (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ 4 * ((deriv u θ) ^ 2 + (u θ) ^ 2) := by
  intro θ hθ
  have hp : (0 : ℝ) < Real.pi / 2 := by positivity
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2]⟩
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.1], hθ'.2⟩
  have hψ : deriv (fun t => u t / Real.cos t) θ
      = (deriv u θ + u θ * Real.tan θ) / Real.cos θ :=
    Y2U_psi_deriv u (hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)) hθ'
  -- the weight is at most `1`
  have hsin2 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hσ1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 :=
    Real.rpow_le_one hsin2 (Real.sin_le_one _) (by linarith)
  -- `tan θ ≤ 1`
  have htan0 : 0 ≤ Real.tan θ :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hθ.1.le (by linarith [hθ.2])
  have htan1 : Real.tan θ ≤ 1 := by
    rcases lt_or_eq_of_le hθ.2 with hlt | heq
    · have h := Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hθ.1.le (by linarith) hlt
      rw [Real.tan_pi_div_four] at h
      exact le_of_lt h
    · rw [heq, Real.tan_pi_div_four]
  have htan2 : Real.tan θ ^ 2 ≤ 1 := by nlinarith
  -- `1/cos² θ ≤ 2`
  have hcos2 : (1 : ℝ) / 2 ≤ Real.cos θ ^ 2 := by
    have hc : Real.cos θ ^ 2 = 1 / 2 + Real.cos (2 * θ) / 2 := Real.cos_sq θ
    have hc2 : 0 ≤ Real.cos (2 * θ) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    linarith
  -- numerator estimate
  have hnum : (deriv u θ + u θ * Real.tan θ) ^ 2
      ≤ 2 * ((deriv u θ) ^ 2 + (u θ) ^ 2) := by
    nlinarith [sq_nonneg (deriv u θ - u θ * Real.tan θ), sq_nonneg (u θ), htan2]
  -- putting the pieces together
  have hkey : (deriv (fun t => u t / Real.cos t) θ) ^ 2
      ≤ 4 * ((deriv u θ) ^ 2 + (u θ) ^ 2) := by
    rw [hψ, div_pow, div_le_iff₀ (pow_pos hcos 2)]
    have hA : (deriv u θ + u θ * Real.tan θ) ^ 2
        ≤ 2 * ((deriv u θ) ^ 2 + (u θ) ^ 2) := hnum
    have hB : 2 * ((deriv u θ) ^ 2 + (u θ) ^ 2)
        ≤ 4 * ((deriv u θ) ^ 2 + (u θ) ^ 2) * Real.cos θ ^ 2 := by
      nlinarith [sq_nonneg (deriv u θ), sq_nonneg (u θ), hcos2]
    linarith
  calc (deriv (fun t => u t / Real.cos t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ (deriv (fun t => u t / Real.cos t) θ) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hσ1 (sq_nonneg _)
    _ = (deriv (fun t => u t / Real.cos t) θ) ^ 2 := mul_one _
    _ ≤ 4 * ((deriv u θ) ^ 2 + (u θ) ^ 2) := hkey

/-- On `(π/4, π/2)` the exact identity `sin θ v' = u'' + 5u + g` together with `sin²θ ≥ 1/2`,
`σ ≤ 1` and `σ ≤ sEta` gives `(v')²σ ≤ 6 (g²σ + 25u² + (u'')²sEta)`. -/
private lemma Y2U_right_bound (γ : ℝ) (_hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ 6 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) + 25 * (u θ) ^ 2
            + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  intro θ hθ
  have hp : (0 : ℝ) < Real.pi / 2 := by positivity
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.1], hθ.2⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo ⟨hθ'.1, by linarith [hθ'.2]⟩
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hident := Y2U_psi_ident u g hu hode hθ'
  have hψ : deriv (fun t => u t / Real.cos t) θ
      = (deriv (deriv u) θ + 5 * u θ + g θ) / Real.sin θ := by
    rw [eq_div_iff hsin.ne']
    rw [mul_comm]
    exact hident
  -- `sin² θ ≥ 1/2`
  have hsin2half : (1 : ℝ) / 2 ≤ Real.sin θ ^ 2 := by
    have hc : Real.cos θ ^ 2 = 1 / 2 + Real.cos (2 * θ) / 2 := Real.cos_sq θ
    have hc2 : Real.cos (2 * θ) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [hθ.1]) (by linarith [hθ.2])
    have hs := Real.sin_sq θ
    linarith
  -- the Cauchy–Schwarz step
  have hnum : (deriv (deriv u) θ + 5 * u θ + g θ) ^ 2
      ≤ 3 * ((deriv (deriv u) θ) ^ 2 + 25 * (u θ) ^ 2 + (g θ) ^ 2) := by
    nlinarith [sq_nonneg (deriv (deriv u) θ - 5 * u θ),
      sq_nonneg (5 * u θ - g θ), sq_nonneg (deriv (deriv u) θ - g θ)]
  have hkey : (deriv (fun t => u t / Real.cos t) θ) ^ 2
      ≤ 6 * ((deriv (deriv u) θ) ^ 2 + 25 * (u θ) ^ 2 + (g θ) ^ 2) := by
    rw [hψ, div_pow, div_le_iff₀ (pow_pos hsin 2)]
    have hA : 0 ≤ (deriv (deriv u) θ) ^ 2 + 25 * (u θ) ^ 2 + (g θ) ^ 2 := by positivity
    nlinarith [hnum, hsin2half, hA]
  -- the weight comparisons
  have hσ1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 :=
    Real.rpow_le_one hsin2.le (Real.sin_le_one _) (by linarith)
  have hσsEta : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ Work.FTS.EllipticEst.sEta θ := by
    have heta : (0 : ℝ) < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    rw [Work.FTS.EllipticEst.sEta]
    exact Real.rpow_le_rpow_of_exponent_ge hsin2 (Real.sin_le_one _) (by linarith)
  have hσ0 : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := Real.rpow_nonneg hsin2.le _
  have hsEta0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
    rw [Work.FTS.EllipticEst.sEta]
    exact Real.rpow_nonneg hsin2.le _
  -- assembling
  have step1 : (deriv (fun t => u t / Real.cos t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ (6 * ((deriv (deriv u) θ) ^ 2 + 25 * (u θ) ^ 2 + (g θ) ^ 2))
        * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    mul_le_mul_of_nonneg_right hkey hσ0
  have step2 : (6 * ((deriv (deriv u) θ) ^ 2 + 25 * (u θ) ^ 2 + (g θ) ^ 2))
        * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ 6 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + 25 * (u θ) ^ 2
          + (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
    have h1 : (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      mul_le_mul_of_nonneg_left hσsEta (sq_nonneg _)
    have h2 : 25 * (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 25 * (u θ) ^ 2 := by
      have h := mul_le_of_le_one_right (a := 25 * (u θ) ^ 2)
        (b := Real.rpow (Real.sin (2 * θ)) (2 - γ)) (by positivity) hσ1
      simpa using h
    nlinarith [h1, h2]
  calc (deriv (fun t => u t / Real.cos t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ (6 * ((deriv (deriv u) θ) ^ 2 + 25 * (u θ) ^ 2 + (g θ) ^ 2))
        * Real.rpow (Real.sin (2 * θ)) (2 - γ) := step1
    _ ≤ 6 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + 25 * (u θ) ^ 2
          + (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) := step2
    _ = 6 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) + 25 * (u θ) ^ 2
          + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring

/-! ### The requested uniform bound -/

/-- **The uniform-in-`γ` `(v')²σ`-bound.**  There is a single constant `C > 0` such that for
every `γ ∈ [1, 3/2]` and every `u` of class `C³` on `(0, π/2)` solving `Lzero1 u = g`,

`∫_{Iθ} (v')²σ ≤ C (∫_{Iθ} g²σ + ∫_{Iθ} (u'')²sEta + ∫_{Iθ} (u')² + ∫_{Iθ} u²)`

with `v = u/cos θ` and `σ = sin(2θ)^{2-γ}`; the constant `160` works.  This is the same
proof as `slice_Y2_le`, where `160` is already produced for every `γ ∈ [1, 3/2]`. -/
theorem sliceY2Uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), 1 ≤ γ → γ ≤ 3 / 2 →
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 - γ))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
              + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))) := by
  refine ⟨160, by norm_num, ?_⟩
  intro γ u g hγ1 hγ2 hu _hcont _hu0 _hupi hode hgI hu2I hu1I hu0I
  set F : ℝ → ℝ := fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 - γ) with hF
  -- ### the pointwise bound on the open interval
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      F θ ≤ 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + (deriv u θ) ^ 2 + (u θ) ^ 2) := by
    intro θ hθ
    have hsin2 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hσ0 : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := Real.rpow_nonneg hsin2 _
    have hη0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
      rw [Work.FTS.EllipticEst.sEta]
      exact Real.rpow_nonneg
        (le_of_lt (Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)) _
    have hA : 0 ≤ (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
      mul_nonneg (sq_nonneg _) hσ0
    have hB : 0 ≤ (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      mul_nonneg (sq_nonneg _) hη0
    have hC : 0 ≤ (deriv u θ) ^ 2 := sq_nonneg _
    have hD : 0 ≤ (u θ) ^ 2 := sq_nonneg _
    simp only [hF]
    by_cases hle : θ ≤ Real.pi / 4
    · have h1 := Y2U_left_bound γ hγ1 hγ2 u hu θ ⟨hθ.1, hle⟩
      have h2 : 4 * ((deriv u θ) ^ 2 + (u θ) ^ 2)
          ≤ 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
              + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
              + (deriv u θ) ^ 2 + (u θ) ^ 2) := by
        nlinarith [hA, hB, hC, hD]
      linarith [h1, h2]
    · have hlt : Real.pi / 4 < θ := lt_of_not_ge hle
      have h1 := Y2U_right_bound γ hγ1 hγ2 u g hu hode θ ⟨hlt, hθ.2⟩
      have h2 : 6 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) + 25 * (u θ) ^ 2
              + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
              + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
              + (deriv u θ) ^ 2 + (u θ) ^ 2) := by
        nlinarith [hA, hB, hC, hD]
      linarith [h1, h2]
  -- ### almost-everywhere statement and measurability
  have hle_ae : F ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + (deriv u θ) ^ 2 + (u θ) ^ 2)) :=
    Work.FTS.EllipticEst.ae_restrict_Iθ_of_Ioo_memLp hpt
  have hF_aesm : MeasureTheory.AEStronglyMeasurable F
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [hF]
    have h1 : MeasureTheory.AEStronglyMeasurable (deriv (fun t => u t / Real.cos t))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := aestronglyMeasurable_deriv _ _
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).comp
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    exact h1.pow 2 |>.mul h2
  have hF_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] F := by
    have aux : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
        (0 : ℝ) ≤ F θ := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun θ hθ => ?_)
      simp only [hF]
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
          by linarith [hθ.2]⟩) _)
    exact aux
  -- ### integrability of the dominating function and of `F`
  have hA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ := hgI
  have hB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := hu2I
  have hC : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv u θ) ^ 2) Work.Spaces.Iθ := hu1I
  have hD : MeasureTheory.IntegrableOn (fun θ : ℝ => (u θ) ^ 2) Work.Spaces.Iθ := hu0I
  have hAB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := hA.add hB
  have hABC : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (deriv u θ) ^ 2)
      Work.Spaces.Iθ := hAB.add hC
  have hABCD : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (deriv u θ) ^ 2
        + (u θ) ^ 2) Work.Spaces.Iθ := hABC.add hD
  have hJ_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (deriv u θ) ^ 2
        + (u θ) ^ 2)) Work.Spaces.Iθ := hABCD.const_mul 160
  have hF_int : MeasureTheory.IntegrableOn F Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono_nonneg hJ_int hF_aesm hF_nonneg hle_ae
  -- ### the value of the dominating integral
  have hJ_eval : (∫ θ in Work.Spaces.Iθ, 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (deriv u θ) ^ 2
        + (u θ) ^ 2))
      = 160 * ((∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
    simp only [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hA hB,
      MeasureTheory.integral_add hAB hC, MeasureTheory.integral_add hABC hD]
  refine ⟨hF_int, ?_⟩
  calc ∫ θ in Work.Spaces.Iθ, F θ
      ≤ ∫ θ in Work.Spaces.Iθ, 160 * ((g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          + (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (deriv u θ) ^ 2
          + (u θ) ^ 2) := MeasureTheory.integral_mono_ae hF_int hJ_int hle_ae
    _ = 160 * ((∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := hJ_eval

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_Y2_le =====
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

/-! ### The two first-order identities for `v = u / cos θ` -/



/-! ### The two halves of the pointwise bound -/



/-! ### The requested bound -/


end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_v_identities =====
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

theorem slice_v_identities (u : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ
        = - Real.cos θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          + 3 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ
          - 4 * Real.cos θ * (u θ / Real.cos θ) ∧
      deriv (deriv (deriv u)) θ
        = Real.cos θ * deriv (fun t => deriv (fun s => deriv (fun r => u r / Real.cos r) s) t) θ
          - 3 * Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          - 3 * Real.cos θ * deriv (fun t => u t / Real.cos t) θ
          + Real.sin θ * (u θ / Real.cos θ) ∧
      deriv (fun t => deriv (fun s => Real.tan s * u s) t) θ
        = Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          + 2 * Real.cos θ * deriv (fun t => u t / Real.cos t) θ
          - Real.sin θ * (u θ / Real.cos θ) ∧
      deriv u θ = Real.cos θ * deriv (fun t => u t / Real.cos t) θ
          - Real.sin θ * (u θ / Real.cos θ) := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  set ψ : ℝ → ℝ := fun t => u t / Real.cos t with hψdef
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 := by
    intro t ht
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩)
  have hcosθ : Real.cos θ ≠ 0 := hcos_ne θ hθ
  have hψC : ContDiffOn ℝ 3 ψ (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hψAt : ContDiffAt ℝ 3 ψ θ := hψC.contDiffAt hIoo
  have hψ1 : ContDiffAt ℝ 1 ψ θ := hψAt.of_le (by norm_num)
  have hψ2 : ContDiffAt ℝ 2 ψ θ := hψAt.of_le (by norm_num)
  -- `u = cos θ · ψ` and `tan θ · u = sin θ · ψ` near `θ`
  have hu_eq : u =ᶠ[𝓝 θ] fun s => Real.cos s * ψ s := by
    filter_upwards [hIoo] with s hs
    have hc : Real.cos s ≠ 0 := hcos_ne s hs
    show u s = Real.cos s * ψ s
    rw [hψdef, ← mul_div_assoc, mul_div_cancel_left₀ (u s) hc]
  have htan_eq : (fun s => Real.tan s * u s) =ᶠ[𝓝 θ] fun s => Real.sin s * ψ s := by
    filter_upwards [hIoo] with s hs
    have hc : Real.cos s ≠ 0 := hcos_ne s hs
    show Real.tan s * u s = Real.sin s * ψ s
    rw [Real.tan_eq_sin_div_cos, hψdef, div_mul_eq_mul_div, mul_div_assoc]
  -- Leibniz expansions of the derivatives of `u` and of `tan θ · u`
  have hu1 : iteratedDeriv 1 u θ = -Real.sin θ * ψ θ + Real.cos θ * iteratedDeriv 1 ψ θ := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 1 hu_eq]
    exact itd_cos_one ψ θ hψ1
  have hu2 : iteratedDeriv 2 u θ = -Real.cos θ * ψ θ - 2 * Real.sin θ * iteratedDeriv 1 ψ θ
      + Real.cos θ * iteratedDeriv 2 ψ θ := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 hu_eq]
    exact itd_cos_two ψ θ hψ2
  have hu3 : iteratedDeriv 3 u θ = Real.sin θ * ψ θ - 3 * Real.cos θ * iteratedDeriv 1 ψ θ
      - 3 * Real.sin θ * iteratedDeriv 2 ψ θ + Real.cos θ * iteratedDeriv 3 ψ θ := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 3 hu_eq]
    exact itd_cos_three ψ θ hψAt
  have htu1 : iteratedDeriv 1 (fun s => Real.tan s * u s) θ
      = Real.cos θ * ψ θ + Real.sin θ * iteratedDeriv 1 ψ θ := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 1 htan_eq]
    exact itd_sin_one ψ θ hψ1
  have htu2 : iteratedDeriv 2 (fun s => Real.tan s * u s) θ
      = -Real.sin θ * ψ θ + 2 * Real.cos θ * iteratedDeriv 1 ψ θ
        + Real.sin θ * iteratedDeriv 2 ψ θ := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 htan_eq]
    exact itd_sin_two ψ θ hψ2
  -- conversions from `deriv` to `iteratedDeriv` on the left-hand sides
  have hd2u : deriv (fun s => deriv u s) θ = iteratedDeriv 2 u θ := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hd1tu : deriv (fun s => Real.tan s * u s) θ
      = iteratedDeriv 1 (fun s => Real.tan s * u s) θ := by rw [iteratedDeriv_one]
  have hval : u θ = Real.cos θ * ψ θ := hu_eq.self_of_nhds
  -- `Lzero1 u` in terms of `ψ`
  have keyL : Work.FTS.EllipticEst.Lzero1 u θ
      = -Real.cos θ * iteratedDeriv 2 ψ θ + 3 * Real.sin θ * iteratedDeriv 1 ψ θ
        - 4 * Real.cos θ * ψ θ := by
    unfold Work.FTS.EllipticEst.Lzero1
    rw [hd2u, hd1tu, hu2, htu1, hval]
    ring
  -- conversions of the goal's sub-terms to `ψ`-form
  have hP1 : deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ = iteratedDeriv 2 ψ θ := by
    rw [itd_two_val, hψdef]
  have hP2 : deriv (fun t => deriv (fun s => deriv (fun r => u r / Real.cos r) s) t) θ
      = iteratedDeriv 3 ψ θ := by
    rw [itd_three_val, hψdef]
  have hP0 : deriv (fun t => u t / Real.cos t) θ = iteratedDeriv 1 ψ θ := by
    rw [itd_one_val, hψdef]
  have hPtu : deriv (fun t => deriv (fun s => Real.tan s * u s) t) θ
      = iteratedDeriv 2 (fun s => Real.tan s * u s) θ := by
    rw [itd_two_val]
  have hPu : deriv u θ = iteratedDeriv 1 u θ := by rw [iteratedDeriv_one]
  have hPu3 : deriv (deriv (deriv u)) θ = iteratedDeriv 3 u θ := by
    rw [itd_three_val]
  have hV : u θ / Real.cos θ = ψ θ := by rw [hψdef]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [keyL, hP1, hP0, hV]
  · rw [hPu3, hu3, hP2, hP1, hP0, hV]
    ring
  · rw [hPtu, htu2, hP1, hP0, hV]
    ring
  · rw [hPu, hu1, hP0, hV]
    ring

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.sliceLimitLeftExists =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Set Filter
open scoped Topology

/-! ## Auxiliary estimates -/

/-- **`sEta ≥ 1` on `(0, π/2)`.**  There `0 < sin(2θ) ≤ 1` and the exponent `-η` of the weight
`sEta θ = sin(2θ)^{-η}` is nonpositive, so the weight is at least `1`. -/
lemma sliceLim_one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ sEta θ := by
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one (2 * θ)
  have hz : -(Work.Spaces.eta) ≤ 0 := by
    have het : (0 : ℝ) ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    linarith
  have h := Real.rpow_le_rpow_of_nonpos hpos hle hz
  simpa [sEta, Real.one_rpow] using h

/-- **First transfer of integrability.**  Since `sEta ≥ 1` on `(0, π/2)`, the weighted
square-integrability hypothesis for `u''` implies plain square-integrability of `u''`. -/
lemma sliceLim_integrableOn_sq_of_integrableOn_mul_sEta (u : ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2 * sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hint.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  refine MeasureTheory.Integrable.mono' hI ?_ ?_
  · exact ((measurable_deriv (fun t : ℝ => deriv u t)).pow_const 2).aestronglyMeasurable
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
      have hsq : 0 ≤ (deriv (fun t : ℝ => deriv u t) θ) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hsq]
      nlinarith [sliceLim_one_le_sEta hθ, hsq])

/-- **Second transfer of integrability.**  `|x| ≤ x² + 1` turns square-integrability of `u''`
into integrability of `|u''|` (the interval has finite measure). -/
lemma sliceLim_integrableOn_abs_of_integrableOn_sq (u : ℝ → ℝ)
    (h : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2 + 1)
      (Set.Ioo 0 (Real.pi / 2)) :=
    h.add (MeasureTheory.integrableOn_const (C := (1 : ℝ))
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (by simp))
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · simpa only [Real.norm_eq_abs] using
      (measurable_deriv (fun t : ℝ => deriv u t)).norm.aestronglyMeasurable
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ _ => by
      have hnn : 0 ≤ |deriv (fun t : ℝ => deriv u t) θ| := abs_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      by_cases h1 : |deriv (fun t : ℝ => deriv u t) θ| ≤ 1
      · nlinarith [sq_nonneg (deriv (fun t : ℝ => deriv u t) θ)]
      · push_neg at h1
        nlinarith [sq_abs (deriv (fun t : ℝ => deriv u t) θ), h1,
          abs_nonneg (deriv (fun t : ℝ => deriv u t) θ)])

/-- **Newton–Leibniz bound.**  If `f` has derivative `f'` on the whole closed interval
`[a, b]` and `f'` is integrable there, then for `a ≤ c ≤ b` the increment of `f` from `a` to `c`
is bounded by the mass of `|f'|` on `(a, c]`. -/
lemma sliceLim_abs_sub_le_setIntegral {f f' : ℝ → ℝ} {a b c : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hint : MeasureTheory.IntegrableOn f' (Set.Icc a b) volume) :
    |f c - f a| ≤ ∫ x in Set.Ioc a c, |f' x| := by
  have hsub : Set.Ioc a c ⊆ Set.Icc a b := fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 hcb⟩
  have hInt : IntervalIntegrable f' volume a c :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hac).mpr (hint.mono_set hsub)
  have hFTC : ∫ x in a..c, f' x = f c - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hderiv x (by
      rw [Set.uIcc_of_le hac] at hx
      exact ⟨hx.1, le_trans hx.2 hcb⟩)) hInt
  have hnorm : |∫ x in a..c, f' x| ≤ ∫ x in a..c, |f' x| := by
    simpa only [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_integral_norm (μ := volume) hac (f := f')
  rw [← hFTC]
  exact hnorm.trans (le_of_eq (intervalIntegral.integral_of_le hac))

/-- **Boundedness of `u'` on `(0, π/4)`.**  If `u''` (written out as
`deriv (fun t => deriv u t)`) is the derivative of `u'` on `(0, π/2)` and `|u''|` is integrable
there, then for `θ ∈ (0, π/4)` the value `|u' θ|` is bounded by `|u' (π/4)|` plus the total mass
of `|u''|` on `(0, π/2)`. -/
lemma sliceLim_abs_deriv_le_of_second_deriv_integrableOn {u : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4))
    (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x)
    (hg : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|)
      (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    |deriv u θ| ≤ |deriv u (Real.pi / 4)|
      + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t : ℝ => deriv u t) s| := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hq : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hle : θ ≤ Real.pi / 4 := le_of_lt hθ1
  have hsub : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨lt_of_lt_of_le hθ0 hx.1, lt_of_le_of_lt hx.2 hq⟩
  have hIcc : MeasureTheory.IntegrableOn
      (fun x : ℝ => |deriv (fun t : ℝ => deriv u t) x|) (Set.Icc θ (Real.pi / 4)) :=
    hg.mono_set hsub
  have hint : MeasureTheory.IntegrableOn (deriv (fun t : ℝ => deriv u t))
      (Set.Icc θ (Real.pi / 4)) :=
    MeasureTheory.Integrable.mono' hIcc (measurable_deriv (fun t : ℝ => deriv u t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs])
  have hmain := sliceLim_abs_sub_le_setIntegral (f := deriv u)
    (f' := deriv (fun t : ℝ => deriv u t))
    (a := θ) (b := Real.pi / 4) (c := Real.pi / 4) hle le_rfl
    (fun x hx => hderiv x (hsub hx)) hint
  have htri : |deriv u θ| ≤ |deriv u (Real.pi / 4)|
      + |deriv u (Real.pi / 4) - deriv u θ| := by
    have hid : deriv u θ = deriv u (Real.pi / 4) - (deriv u (Real.pi / 4) - deriv u θ) := by
      ring
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (deriv u (Real.pi / 4)),
        le_abs_self (deriv u (Real.pi / 4) - deriv u θ), hid]
    · linarith [le_abs_self (deriv u (Real.pi / 4)),
        neg_abs_le (deriv u (Real.pi / 4) - deriv u θ), hid]
  have hmono : ∫ x in Set.Ioc θ (Real.pi / 4), |deriv (fun t : ℝ => deriv u t) x|
      ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t : ℝ => deriv u t) s| :=
    MeasureTheory.setIntegral_mono_set hg
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Filter.Eventually.of_forall fun x hx =>
        ⟨lt_trans hθ0 hx.1, lt_of_le_of_lt hx.2 hq⟩)
  calc |deriv u θ|
      ≤ |deriv u (Real.pi / 4)| + |deriv u (Real.pi / 4) - deriv u θ| := htri
    _ ≤ |deriv u (Real.pi / 4)|
        + ∫ x in Set.Ioc θ (Real.pi / 4), |deriv (fun t : ℝ => deriv u t) x| := by
        linarith [hmain]
    _ ≤ |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t : ℝ => deriv u t) s| := by
        linarith [hmono]

theorem sliceLimitLeftExists : ∀ (u : ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    ∃ L : ℝ, Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds L) := by
  intro u hsm hint
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  -- `u` and `u'` are differentiable on the open interval
  have hderiv1 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (deriv u x) x := by
    intro x hx
    have h1 : ContDiffAt ℝ 1 u x := (hsm 1).contDiffAt (isOpen_Ioo.mem_nhds hx)
    exact (h1.differentiableAt (by norm_num)).hasDerivAt
  have hderiv2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 u x := (hsm 2).contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd1 : ContDiffAt ℝ 1 (deriv u) x := h2.derivWithin (by norm_num)
    exact (hd1.differentiableAt (by norm_num)).hasDerivAt
  -- integrability of `(u'')²` and of `|u''|` on `(0, π/2)`
  have hsq : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u hint
  have habs : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) :=
    sliceLim_integrableOn_abs_of_integrableOn_sq u hsq
  -- `u'` is bounded on `(0, π/4)`, hence integrable there
  have hderivu : MeasureTheory.IntegrableOn (deriv u) (Set.Ioo 0 (Real.pi / 4)) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ (measurable_deriv u).aestronglyMeasurable
      (|deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t : ℝ => deriv u t) s|) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
        rw [Real.norm_eq_abs]
        exact sliceLim_abs_deriv_le_of_second_deriv_integrableOn hθ hderiv2 habs)
  exact exists_tendsto_nhdsGT_zero_of_integrableOn_deriv hpi4
    (fun x hx => hderiv1 x ⟨hx.1, lt_of_lt_of_le hx.2 hpi4lt.le⟩) hderivu

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.H2.L12densSlice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set

namespace Work.FTS.H2

/-- The `L₁₂` density of the elliptic section is the fundamental-model density for the
angular weight `K = 3 sin θ cos²θ`: the two definitions differ only by `Ktheta_eq_K`, and
`Work.Spaces.Iθ` is definitionally `Icc 0 (π/2)`. -/
theorem L12dens_eq_FM_K (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.L12dens f z = Work.FM.L12dens Work.Spaces.K f z := by
  simp only [Work.Elliptic.L12dens, Work.FM.L12dens, Work.Elliptic.Ktheta_eq_K,
    Work.Spaces.Iθ]

/-- The angular slice `θ ↦ f z θ` of a `SmoothNbhd` function is continuous on the compact
`Iθ`, hence its square is integrable there. -/
theorem slice_sq_integrableOn {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  -- The slice map `θ ↦ (z,θ)` sends `Iθ` into the open neighbourhood `U` of `SmoothNbhd`.
  have ht : Set.MapsTo (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := by
    intro θ hθ
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    exact ⟨by simp only [Set.mem_Ioi]; linarith [hz], by
      simp only [Set.mem_Ioo]
      exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩
  have hcont : ContinuousOn (fun θ : ℝ => f z θ) Work.Spaces.Iθ :=
    hsm.continuousOn.comp (f := fun θ : ℝ => (z, θ)) (g := Function.uncurry f)
      ((continuous_const.prodMk continuous_id).continuousOn) ht
  have hsq : ContinuousOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := hcont.pow 2
  exact hsq.integrableOn_compact (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)

/-- Elementary square-root algebra: if `x² ≤ 3 X / z²` with `X ≥ 0` and `z > 0`, then
`|x| ≤ √3 · √X / z`. -/
theorem abs_le_sqrt_three_mul_sqrt_div {x X z : ℝ} (hz : 0 < z) (hX : 0 ≤ X)
    (h : x ^ 2 ≤ 3 * X / z ^ 2) : |x| ≤ Real.sqrt 3 * Real.sqrt X / z := by
  calc |x| = Real.sqrt (x ^ 2) := (Real.sqrt_sq_eq_abs x).symm
    _ ≤ Real.sqrt (3 * X / z ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt 3 * Real.sqrt X / z := by
        rw [Real.sqrt_div (by positivity) (z ^ 2), Real.sqrt_mul (by norm_num) X,
          Real.sqrt_sq hz.le]


end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.energyToDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.H2.ModalSolR

/-- On `Iθ = [0, π/2]` the integrand `(v θ / cos θ)² · cos θ` is nonnegative — `cos ≥ 0`
on `Iθ` and the square factor is a square — hence so is its integral. -/
private theorem integral_div_cos_sq_nonneg (v : ℝ → ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, (v θ / Real.cos θ) ^ 2 * Real.cos θ := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hrew : (∫ θ in Work.Spaces.Iθ, (v θ / Real.cos θ) ^ 2 * Real.cos θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), (v θ / Real.cos θ) ^ 2 * Real.cos θ := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle]
  rw [hrew]
  exact intervalIntegral.integral_nonneg hle fun θ hθ =>
    mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)

theorem energyToDeriv {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2)))
    (h0 : v 0 = 0) (h1 : v (Real.pi / 2) = 0)
    (hI1 : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ) Work.Spaces.Iθ)
    (hI2 : MeasureTheory.IntegrableOn (fun θ => (deriv v θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (hI3 : MeasureTheory.IntegrableOn
      (fun θ => (v θ / Real.cos θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (hI4 : MeasureTheory.IntegrableOn (fun θ => v θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ)
      ≤ 6 * (∫ θ in Work.Spaces.Iθ, v θ ^ 2 * Real.cos θ)
          + (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ) := by
  -- the `cos`-weighted energy identity for the angular operator `Lzero1`:
  -- `∫ (Lzero1 v)·v·cos = ∫ (v')²cos + ∫ (v/cos)²cos - 6∫ v²cos`
  have hE :=
    Work.EllipticEst.ModalSolution.Lzero1_energy_cos_correct v hv h0 h1 hI1 hI2 hI3 hI4
  -- the middle term is nonnegative, so it can be dropped from the identity
  have hB := integral_div_cos_sq_nonneg v
  linarith

end Work.FTS.H2.ModalSolR
end
-- ===== merged: Submission.Work.FTS.H2.MuEstimate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

/-- `1 ≤ α^c` for `c ≤ 0` when `0 < α ≤ 1`; equivalently `α^z ≤ α^y` for `y ≤ z`.  This is
`Work.Construction.rpow_le_of_le_one`, reproved here to avoid importing the whole
`Apriori` chapter. -/
private theorem rpow_le_of_le_one' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {y z : ℝ}
    (hyz : y ≤ z) : α ^ z ≤ α ^ y := by
  have h : α ^ z = α ^ y * α ^ (z - y) := by
    rw [← Real.rpow_add hα]
    ring_nf
  rw [h]
  calc α ^ y * α ^ (z - y) ≤ α ^ y * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hα.le y)
        exact Real.rpow_le_one hα.le hα1 (by linarith)
    _ = α ^ y := by ring

private theorem one_le_rpow_of_nonpos {α c : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hc : c ≤ 0) :
    1 ≤ α ^ c := by
  have h := rpow_le_of_le_one' hα hα1 (show c ≤ (0 : ℝ) from hc)
  rwa [Real.rpow_zero] at h



end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.H2.PhiStarE.Gbar_wiln =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.PhiStarE

set_option autoImplicit false

/-! ## Reduction of `Elliptic.Fstar (Construction.Fstar α)` -/

theorem EllFstar_Fstar (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Elliptic.Fstar (Work.Construction.Fstar α)
      = fun z => α * Work.FM.Fstar z / 3 := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  funext z
  rw [Work.Elliptic.Fstar]
  have hpoint : ∀ θ : ℝ,
      Work.Construction.Fstar α z θ * Work.Elliptic.sinCos2 θ
        = (α * Work.FM.Fstar z / (3 * Work.Spaces.c α))
            * (Work.Spaces.Gam α θ * Work.Spaces.K θ) := by
    intro θ
    simp only [Work.Construction.Fstar, Work.Elliptic.sinCos2, Work.Spaces.K]
    ring
  rw [setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
        (fun θ _ => hpoint θ)]
  rw [integral_const_mul]
  have hcint : (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ)
      = Work.Spaces.c α := rfl
  rw [hcint]
  field_simp

/-! ## Differentiation of the basic family -/

/-- The `x`-derivative of the integrand of `At`:
`d/dx [t^a/(1+xt)^m] = -m·t^{a+1}/(1+xt)^{m+1}`. -/
theorem hasDerivAt_div_pow_exp (a : ℝ) (m : ℕ) (hm : 1 ≤ m) {t x : ℝ} (ht : 0 ≤ t)
    (ha : 0 ≤ a) (hx : 0 < 1 + x * t) :
    HasDerivAt (fun x : ℝ => t ^ a / (1 + x * t) ^ m)
      (-(m : ℝ) * (t ^ (a + 1) / (1 + x * t) ^ (m + 1))) x := by
  have hD : (1 + x * t) ≠ 0 := ne_of_gt hx
  have hden : HasDerivAt (fun x : ℝ => (1 + x * t) ^ m)
      ((m : ℝ) * (1 + x * t) ^ (m - 1) * t) x := by
    have h1 : HasDerivAt (fun x : ℝ => 1 + x * t) t x := by
      simpa using ((hasDerivAt_id x).mul_const t).const_add 1
    convert h1.pow m using 1
  have hnum : HasDerivAt (fun _ : ℝ => t ^ a) 0 x := hasDerivAt_const x _
  have h := hnum.div hden (pow_ne_zero m hD)
  have htp : t ^ a * t = t ^ (a + 1) := by
    rcases lt_or_eq_of_le ht with h0 | h0
    · rw [Real.rpow_add h0, Real.rpow_one]
    · subst h0
      rcases lt_or_eq_of_le ha with ha0 | ha0
      · rw [Real.zero_rpow (ne_of_gt ha0), Real.zero_rpow (by linarith : (a + 1) ≠ 0)]
        ring
      · subst ha0
        simp only [Real.rpow_zero, zero_add, Real.rpow_one]
        ring
  have hgen : ∀ (D T : ℝ), D ≠ 0 →
      (0 * D ^ m - T * ((m : ℝ) * D ^ (m - 1) * t)) / (D ^ m) ^ 2
        = -((m : ℝ) * (T * t / D ^ (m + 1))) := by
    intro D T _
    have key : D * D ^ m * D ^ (m - 1) = D ^ (m * 2) := by
      nth_rewrite 1 [show D = D ^ 1 from (pow_one D).symm]
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    field_simp
    ring_nf
    rw [key]
  have hv := hgen (1 + x * t) (t ^ a) hD
  rw [htp] at hv
  rw [hv] at h
  convert h using 1
  · ring

/-- `At N j` is differentiable on `z ≥ 0`, with `(At N j)' = -(j+2)·At N (j+1)`
(differentiation under the integral sign; the factor `1 + zt ≥ 1` keeps the
denominator away from zero). -/
theorem At_hasDerivAt (N : ℝ) (hN : 0 ≤ N) (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (At N j) (-((j : ℝ) + 2) * At N (j + 1) z) z := by
  have hS : Set.Ioi (-1/2 : ℝ) ∈ 𝓝 z :=
    isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith)
  have hzS : z ∈ Set.Ioi (-1/2 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hpos : ∀ x ∈ Set.Ioi (-1/2 : ℝ), ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < 1 + x * t := by
    intro x hx t ht
    simp only [Set.mem_Ioi] at hx
    nlinarith [ht.1, ht.2]
  have hcont : ∀ x ∈ Set.Ioi (-1/2 : ℝ),
      ContinuousOn (fun t : ℝ => t ^ (N + (j:ℝ)) / (1 + x * t) ^ (j + 2)) (Set.uIcc 0 1) := by
    intro x hx
    have hden : Continuous (fun t : ℝ => (1 + x * t) ^ (j + 2)) :=
      (continuous_const.add (continuous_const.mul continuous_id)).pow _
    have hnum : Continuous (fun t : ℝ => t ^ (N + (j:ℝ))) :=
      continuous_iff_continuousAt.mpr fun t =>
        Real.continuousAt_rpow_const t _ (Or.inr (by positivity))
    refine ContinuousOn.div hnum.continuousOn hden.continuousOn ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have := hpos x hx t ⟨ht.1, ht.2⟩
    positivity
  have hcont' : ∀ x ∈ Set.Ioi (-1/2 : ℝ),
      ContinuousOn (fun t : ℝ => t ^ (N + (j:ℝ) + 1) / (1 + x * t) ^ (j + 3))
        (Set.uIcc 0 1) := by
    intro x hx
    have hden : Continuous (fun t : ℝ => (1 + x * t) ^ (j + 3)) :=
      (continuous_const.add (continuous_const.mul continuous_id)).pow _
    have hnum : Continuous (fun t : ℝ => t ^ (N + (j:ℝ) + 1)) :=
      continuous_iff_continuousAt.mpr fun t =>
        Real.continuousAt_rpow_const t _ (Or.inr (by positivity))
    refine ContinuousOn.div hnum.continuousOn hden.continuousOn ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have := hpos x hx t ⟨ht.1, ht.2⟩
    positivity
  have hdiff : ∀ t ∈ Set.uIoc (0:ℝ) 1, ∀ x ∈ Set.Ioi (-1/2 : ℝ),
      HasDerivAt (fun x : ℝ => t ^ (N + (j:ℝ)) / (1 + x * t) ^ (j + 2))
        (-((j:ℝ)+2) * (t ^ (N + (j:ℝ) + 1) / (1 + x * t) ^ (j + 3))) x := by
    intro t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have hx' : 0 < 1 + x * t := hpos x hx t ⟨le_of_lt ht.1, ht.2⟩
    convert hasDerivAt_div_pow_exp (N + (j:ℝ)) (j+2) (by omega) (le_of_lt ht.1)
      (by positivity) hx' using 1
    push_cast
    ring
  have hbd : ∀ t ∈ Set.uIoc (0:ℝ) 1, ∀ x ∈ Set.Ioi (-1/2 : ℝ),
      ‖-((j:ℝ)+2) * (t ^ (N + (j:ℝ) + 1) / (1 + x * t) ^ (j + 3))‖
        ≤ ((j:ℝ)+2) * (2:ℝ)^(j+3) := by
    intro t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    simp only [Set.mem_Ioi] at hx
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hx' : 0 < 1 + x * t := by nlinarith
    have h1 : t ^ (N + (j:ℝ) + 1) ≤ 1 :=
      Real.rpow_le_one (le_of_lt ht0) ht1 (by positivity)
    have h2 : (1 : ℝ) / (1 + x * t) ^ (j + 3) ≤ (2:ℝ)^(j+3) := by
      rw [div_le_iff₀ (by positivity), ← mul_pow]
      exact one_le_pow₀ (by nlinarith)
    rw [norm_mul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (j:ℝ)+2)]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht0) _),
      abs_of_pos (by positivity : (0:ℝ) < (1 + x * t)^(j+3))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc t ^ (N + (j:ℝ) + 1) / (1 + x * t) ^ (j + 3)
        = t ^ (N + (j:ℝ) + 1) * (1 / (1 + x * t) ^ (j + 3)) := by ring
      _ ≤ 1 * (2:ℝ)^(j+3) := mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ = (2:ℝ)^(j+3) := by ring
  have hAt : At N (j+1) z
      = ∫ t in (0:ℝ)..1, t ^ (N + (j:ℝ) + 1) / (1 + z * t) ^ (j + 3) := by
    rw [At_def]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have h1 : N + ((j+1 : ℕ) : ℝ) = N + (j:ℝ) + 1 := by push_cast; ring
    have h2 : (j+1) + 2 = j + 3 := by omega
    rw [h1, h2]
  have hval : (∫ t in (0:ℝ)..1,
        -((j:ℝ)+2) * (t ^ (N + (j:ℝ) + 1) / (1 + z * t) ^ (j + 3)))
      = -((j:ℝ)+2) * At N (j+1) z := by
    rw [intervalIntegral.integral_const_mul, ← hAt]
  have hFmeas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun t : ℝ => t ^ (N + (j:ℝ)) / (1 + x * t) ^ (j + 2))
        (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    filter_upwards [hS] with x hx
    exact ((hcont x hx).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hF'meas : AEStronglyMeasurable
      (fun t : ℝ => -((j:ℝ)+2) * (t ^ (N + (j:ℝ) + 1) / (1 + z * t) ^ (j + 3)))
        (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    (((hcont' z hzS).const_mul (-((j:ℝ)+2))).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  have key := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (𝕜 := ℝ)
    (F := fun x t => t ^ (N + (j:ℝ)) / (1 + x * t) ^ (j + 2))
    (F' := fun x t => -((j:ℝ)+2) * (t ^ (N + (j:ℝ) + 1) / (1 + x * t) ^ (j + 3)))
    (bound := fun _ : ℝ => ((j:ℝ)+2) * (2:ℝ)^(j+3))
    (x₀ := z) (a := 0) (b := 1) (s := Set.Ioi (-1/2 : ℝ))
    hS hFmeas ((hcont z hzS).intervalIntegrable) hF'meas
    (Filter.Eventually.of_forall hbd) intervalIntegrable_const
    (Filter.Eventually.of_forall hdiff)).2
  rw [hval] at key
  exact key

/-- `t ↦ t^a` is continuous for `a ≥ 0`. -/
theorem continuous_rpow_const_nonneg {a : ℝ} (ha : 0 ≤ a) :
    Continuous (fun t : ℝ => t ^ a) :=
  continuous_iff_continuousAt.mpr fun t => Real.continuousAt_rpow_const t a (Or.inr ha)

/-- The change of variables `s = z·t` in the basic integral:
`∫_0^z s^{N+j}(1+s)^{-(j+2)} ds = z^{N+j+1} · At N j z` for `z > 0`. -/
theorem At_subst (N : ℝ) (j : ℕ) {z : ℝ} (hz : 0 < z) :
    ∫ s in (0:ℝ)..z, s ^ (N + (j:ℝ)) / (1 + s) ^ (j + 2)
      = z ^ (N + (j:ℝ) + 1) * At N j z := by
  have hkey := intervalIntegral.mul_integral_comp_mul_left (a := (0:ℝ)) (b := (1:ℝ))
    (f := fun s : ℝ => s ^ (N + (j:ℝ)) / (1 + s) ^ (j + 2)) z
  simp only [mul_zero, mul_one] at hkey
  rw [← hkey]
  rw [At_def]
  have hpt : Set.EqOn (fun t : ℝ => (z * t) ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2))
      (fun t : ℝ => z ^ (N + (j:ℝ)) * (t ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2)))
      (Set.uIcc (0:ℝ) 1) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    dsimp only
    rw [Real.mul_rpow (le_of_lt hz) ht.1]
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
  have hzpow : z ^ (N + (j:ℝ) + 1) = z ^ (N + (j:ℝ)) * z := by
    rw [show N + (j:ℝ) + 1 = (N + (j:ℝ)) + 1 from rfl, Real.rpow_add hz, Real.rpow_one]
  rw [hzpow]
  ring

/-- The basic bound `|z^c · At N j z| ≤ 2/N` for `N ≥ 2` and `0 ≤ c ≤ j+1`.  The
exponent budget `c ≤ j+1` is exactly what the Leibniz expansion of `(1+z)^k Pi^{(k)} z`
produces. -/
theorem At_bound (N : ℝ) (hN : 2 ≤ N) (j c : ℕ) (hc : c ≤ j + 1) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ c * At N j z| ≤ 2 / N := by
  have hNpos : (0:ℝ) < N := by linarith
  have hNj : (0:ℝ) < N + (j:ℝ) := by linarith [show (0:ℝ) ≤ (j:ℝ) from Nat.cast_nonneg j]
  have hexp0 : (0:ℝ) ≤ N + (j:ℝ) := le_of_lt hNj
  have hzpow : (0:ℝ) ≤ z ^ c := pow_nonneg hz c
  have hA0 : 0 ≤ At N j z := by
    rw [At_def]
    refine intervalIntegral.integral_nonneg (by norm_num) fun t ht => ?_
    exact div_nonneg (Real.rpow_nonneg ht.1 _)
      (pow_nonneg (by linarith [mul_nonneg hz ht.1]) _)
  rw [abs_of_nonneg (mul_nonneg hzpow hA0)]
  have hcont1 : ContinuousOn (fun t : ℝ => t ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2))
      (Set.uIcc 0 1) :=
    ContinuousOn.div (continuous_rpow_const_nonneg hexp0).continuousOn
      ((continuous_const.add (continuous_const.mul continuous_id)).pow _).continuousOn
      (fun t ht => by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
        exact pow_ne_zero _ (ne_of_gt (by linarith [mul_nonneg hz ht.1])))
  have hintegrable1 : IntervalIntegrable
      (fun t : ℝ => t ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2)) volume 0 1 :=
    hcont1.intervalIntegrable
  have hintegrable2 : IntervalIntegrable (fun t : ℝ => t ^ (N + (j:ℝ))) volume 0 1 :=
    (continuous_rpow_const_nonneg hexp0).intervalIntegrable 0 1
  have hintegrable3 : IntervalIntegrable (fun t : ℝ => t ^ (N - 2)) volume 0 1 :=
    (continuous_rpow_const_nonneg (by linarith : (0:ℝ) ≤ N - 2)).intervalIntegrable 0 1
  have hfin : 1 / (N - 1) ≤ 2 / N := by
    have h1 : (0:ℝ) < N - 1 := by linarith
    rw [div_le_iff₀ h1, show (2:ℝ) / N * (N - 1) = 2 * (N - 1) / N from by ring,
      le_div_iff₀ hNpos]
    linarith
  rcases le_or_gt z 1 with hz1 | hz1
  · have h1 : z ^ c ≤ 1 := pow_le_one₀ hz hz1
    have h2 : At N j z ≤ 1 / N := by
      have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
          t ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2) ≤ t ^ (N + (j:ℝ)) := by
        intro t ht
        rw [div_le_iff₀ (pow_pos (by linarith [mul_nonneg hz ht.1]) _)]
        have h3 : (1:ℝ) ≤ (1 + z * t) ^ (j + 2) :=
          one_le_pow₀ (by linarith [mul_nonneg hz ht.1])
        nlinarith [Real.rpow_nonneg ht.1 (N + (j:ℝ))]
      rw [At_def]
      have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
        hintegrable1 hintegrable2 hpt
      have hval : (∫ t in (0:ℝ)..1, t ^ (N + (j:ℝ))) = 1 / (N + (j:ℝ) + 1) := by
        rw [integral_rpow (Or.inl (by linarith))]
        rw [Real.one_rpow,
          Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < N + (j:ℝ) + 1))]
        simp only [sub_zero]
      rw [hval] at hmono
      have hle : 1 / (N + (j:ℝ) + 1) ≤ 1 / N := by
        apply one_div_le_one_div_of_le hNpos
        linarith [show (0:ℝ) ≤ (j:ℝ) from Nat.cast_nonneg j]
      linarith
    calc z ^ c * At N j z ≤ 1 * At N j z := mul_le_mul_of_nonneg_right h1 hA0
      _ = At N j z := one_mul _
      _ ≤ 1 / N := h2
      _ ≤ 2 / N := div_le_div_of_nonneg_right (by norm_num) (le_of_lt hNpos)
  · have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
        z ^ c * (t ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2)) ≤ t ^ (N - 2) := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · subst h0
        rw [Real.zero_rpow (ne_of_gt hNj), zero_div, mul_zero]
        exact Real.rpow_nonneg le_rfl _
      · have hc2 : c ≤ j + 2 := by omega
        have hmain : z ^ c * t ^ (j + 2) ≤ (1 + z * t) ^ (j + 2) := by
          have h1 : z ^ c ≤ z ^ (j + 2) := pow_le_pow_right₀ (le_of_lt hz1) hc2
          have h2 : z ^ c * t ^ (j + 2) ≤ z ^ (j + 2) * t ^ (j + 2) :=
            mul_le_mul_of_nonneg_right h1 (pow_nonneg (le_of_lt h0) _)
          rw [← mul_pow] at h2
          exact h2.trans (pow_le_pow_left₀ (mul_nonneg hz (le_of_lt h0))
            (by linarith [mul_nonneg hz (le_of_lt h0)]) _)
        have hp : t ^ (N + (j:ℝ)) = t ^ (N - 2) * t ^ (j + 2) := by
          rw [show N + (j:ℝ) = (N - 2) + ((j + 2 : ℕ) : ℝ) from by push_cast; ring]
          rw [Real.rpow_add h0, Real.rpow_natCast]
        rw [hp]
        calc z ^ c * (t ^ (N - 2) * t ^ (j + 2) / (1 + z * t) ^ (j + 2))
            = t ^ (N - 2) * (z ^ c * t ^ (j + 2) / (1 + z * t) ^ (j + 2)) := by ring
          _ ≤ t ^ (N - 2) * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.rpow_pos_of_pos h0 _))
              rw [div_le_one (pow_pos (by linarith [mul_nonneg hz (le_of_lt h0)]) _)]
              exact hmain
          _ = t ^ (N - 2) := mul_one _
    have hIntLHS : IntervalIntegrable
        (fun t : ℝ => z ^ c * (t ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2))) volume 0 1 :=
      hintegrable1.const_mul _
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      hIntLHS hintegrable3 hpt
    have hval : (∫ t in (0:ℝ)..1, t ^ (N - 2)) = 1 / (N - 1) := by
      rw [integral_rpow (Or.inl (by linarith))]
      rw [Real.one_rpow,
        Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < N - 2 + 1))]
      simp only [sub_zero]
      congr 1
      ring
    rw [hval] at hmono
    rw [At_def, ← intervalIntegral.integral_const_mul]
    exact hmono.trans hfin

/-! ## The left branch `PhiL` and its derivatives -/


/-! ## The reduction of `Ḡ` to the one-variable model -/

/-- On `z ≥ 0` the singular piece `Ḡ` is `-(1/2)·Pi (5/α) z`, i.e.
`-(1/2) z^{-5/α}∫_0^z s^{5/α}(1+s)^{-2} ds` after the change of variables. -/
theorem Gbar_eq_of_nonneg (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    Work.Elliptic.Gbar α (Work.Construction.Fstar α) z = -(1 / 2) * Pi (5 / α) z := by
  have hαne : α ≠ 0 := ne_of_gt hα
  rw [Work.Elliptic.Gbar, EllFstar_Fstar α hα hα1]
  have hpt : ∀ s ∈ Set.uIcc (0:ℝ) z,
      s ^ ((5 - α) / α) * (α * Work.FM.Fstar s / 3)
        = (2 * α / 3) * (s ^ (5 / α) / (1 + s) ^ 2) := by
    intro s hs
    rw [Set.uIcc_of_le hz] at hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · subst h0
      rw [Real.zero_rpow (div_ne_zero (by linarith) hαne),
        Real.zero_rpow (div_ne_zero (by norm_num) hαne), zero_mul, zero_div, mul_zero]
    · rw [Work.FM.Fstar]
      have hrw : s ^ ((5 - α) / α) * s = s ^ (5 / α) := by
        rw [show (5:ℝ) / α = ((5 - α) / α) + 1 from by field_simp; ring,
          Real.rpow_add h0, Real.rpow_one]
      rw [show s ^ ((5 - α) / α) * (α * (2 * s / (1 + s) ^ 2) / 3)
          = (2 * α / 3) * (s ^ ((5 - α) / α) * s / (1 + s) ^ 2) from by ring, hrw]
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
  rcases eq_or_lt_of_le hz with hz0 | hz0
  · subst hz0
    rw [intervalIntegral.integral_same, Pi_def]
    ring
  · have hsub := At_subst (5 / α) 0 hz0
    simp only [Nat.cast_zero, add_zero, zero_add] at hsub
    rw [hsub, Pi_def]
    have hzp : z ^ (-(5 / α)) * z ^ (5 / α + 1) = z := by
      rw [← Real.rpow_add hz0]
      norm_num
    rw [show - (3 / (4 * α)) * z ^ (-(5 / α))
          * ((2 * α / 3) * (z ^ (5 / α + 1) * At (5 / α) 0 z))
        = (-(3 / (4 * α)) * (2 * α / 3) * (z ^ (-(5 / α)) * z ^ (5 / α + 1)))
          * At (5 / α) 0 z from by ring, hzp]
    field_simp
    norm_num

/-! ## The derivative chain for `ρ = -(1/2)·Pi N` -/

/-- The `k`-th derivative of `ρ = -(1/2)·Pi N` for `k ≤ 4` (computed from
`(At N j)' = -(j+2)At N (j+1)` and the Leibniz rule). -/
def Dk (N : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun z => -(1 / 2) * (z * At N 0 z)
  | 1 => fun z => -(1 / 2) * (At N 0 z - 2 * z * At N 1 z)
  | 2 => fun z => -(1 / 2) * (-4 * At N 1 z + 6 * z * At N 2 z)
  | 3 => fun z => -(1 / 2) * (18 * At N 2 z - 24 * z * At N 3 z)
  | _ => fun z => -(1 / 2) * (-96 * At N 3 z + 120 * z * At N 4 z)

@[simp] theorem Dk_zero (N : ℝ) : Dk N 0 = fun z => -(1 / 2) * (z * At N 0 z) := rfl
@[simp] theorem Dk_one (N : ℝ) : Dk N 1 = fun z => -(1 / 2) * (At N 0 z - 2 * z * At N 1 z) := rfl
@[simp] theorem Dk_two (N : ℝ) :
    Dk N 2 = fun z => -(1 / 2) * (-4 * At N 1 z + 6 * z * At N 2 z) := rfl
@[simp] theorem Dk_three (N : ℝ) :
    Dk N 3 = fun z => -(1 / 2) * (18 * At N 2 z - 24 * z * At N 3 z) := rfl
@[simp] theorem Dk_four (N : ℝ) :
    Dk N 4 = fun z => -(1 / 2) * (-96 * At N 3 z + 120 * z * At N 4 z) := rfl



/-- Weighted bound for the model integrals: `(1+z)^c z^e At N j z = O(1/N)` whenever the
total exponent budget `c + e ≤ j + 1` is respected. -/
theorem shift_bound (N : ℝ) (hN : 2 ≤ N) (c j e : ℕ) (hc : c + e ≤ j + 1) {z : ℝ}
    (hz : 0 ≤ z) :
    |(1 + z) ^ c * (z ^ e * At N j z)| ≤ 2 ^ (c + 1) / N := by
  have hNpos : (0:ℝ) < N := by linarith
  have h1z : (0:ℝ) ≤ 1 + z := by linarith
  have hsum : (1 + z) ^ c * (z ^ e * At N j z)
      = ∑ m ∈ Finset.range (c + 1),
          (c.choose m : ℝ) * (z ^ (c - m + e) * At N j z) := by
    rw [add_pow]
    simp only [one_pow, one_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    calc z ^ (c - m) * ↑(c.choose m) * (z ^ e * At N j z)
        = ↑(c.choose m) * (z ^ (c - m) * z ^ e * At N j z) := by ring
      _ = ↑(c.choose m) * (z ^ (c - m + e) * At N j z) := by rw [← pow_add]
  rw [hsum]
  have hterm : ∀ m ∈ Finset.range (c + 1),
      |(c.choose m : ℝ) * (z ^ (c - m + e) * At N j z)| ≤ (c.choose m : ℝ) * (2 / N) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hmc : c - m + e ≤ j + 1 := by omega
    have h := At_bound N hN j (c - m + e) hmc hz
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c.choose m : ℝ))]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsc : (∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ)) = (2:ℝ) ^ c := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  rw [hsc]
  have h2 : ((2:ℝ) ^ c) * (2 / N) = 2 ^ (c + 1) / N := by
    rw [pow_succ]; ring
  rw [h2]





/-- `pzIter k` of a radial function is the `k`-th `deriv`-iterate. -/
theorem pzIter_radial (g : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z θ => g z) z θ = (deriv^[k]) g z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      simp only [ih]
      rw [Function.iterate_succ_apply']


/-- `pzIter k` of the zero function is zero. -/
theorem pzIter_zero_fun (k : ℕ) :
    Work.Spaces.pzIter k (fun _ _ => (0:ℝ)) = fun _ _ => (0:ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Work.Spaces.pzIter_succ, ih]; funext z θ; simp [Work.Spaces.pz]





end Work.FTS.H2.PhiStarE
end
end
-- ===== merged: Submission.Work.FTS.H2.T2Aesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section






/-! ## Continuity of `H4PairInt`, `Hhard` and `Heasy` on the open square -/







/-! ## The a.e. strong measurability statements -/







end

end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `L₁₂`-density of the profile `F_*` is integrable on `(z,∞)`

`Work.Construction.L12dens (F_*) s` is the angular density `∫_0^{π/2} K(θ) F_*(s,θ)/s dθ` of
the integral operator `L₁₂` at the paper's profile.  By
`Work.Construction.L12dens_Fstar` it equals `α · (F_*(s)/s)` with `F_*(s) = 2s/(1+s)²`
(`Work.FM.Fstar`), so on `/ s ≠ 0` it is the elementary function `2α/(1+s)²`, whose
`z`-integral converges on `(z,∞)` for every `z ≥ 0` (the pole of `1/(1+s)²` sits at
`s = -1 < z`).  The integrability is `L₂`-integrability, not just convergence of the
improper integral, and is obtained from the FTC lemma
`MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'` applied to the primitive
`s ↦ -2/(1+s)` — exactly the computation of `Work.FM.integral_Ioi_Fstar_div`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.MeridianDyn.Bridge.Pieces

/-- The elementary integrand `s ↦ 2/(1+s)²` is integrable on `(z,∞)` for `z ≥ 0`: it has the
antiderivative `s ↦ -2/(1+s)`, which is nonnegative-derivative there and tends to `0` at
`+∞`. -/
theorem integrableOn_two_div_one_add_sq (z : ℝ) (hz : 0 ≤ z) :
    IntegrableOn (fun s : ℝ => 2 / (1 + s) ^ 2) (Ioi z) := by
  refine integrableOn_Ioi_deriv_of_nonneg'
    (g := fun t : ℝ => -2 / (1 + t)) (g' := fun t : ℝ => 2 / (1 + t) ^ 2)
    (a := z) (l := 0) ?_ ?_ ?_
  · intro x hx
    have hxz : z ≤ x := hx.out
    have hx1 : (1 : ℝ) + x ≠ 0 := by linarith
    simpa using Work.FM.hasDerivAt_div_add_const (-2) 1 x hx1
  · intro x hx
    have hx0 : (0 : ℝ) < 1 + x := by have := hx.out; linarith
    positivity
  · have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
      tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
    have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 := h2.const_mul (-2 : ℝ)
    simpa [div_eq_mul_inv] using h3

/-- The `L₁₂`-density of the profile `F_*` is integrable on `(z,∞)` for every `z ≥ 0`: it is
`α · 2/(1+s)²` off the null set `{0}`, and `2/(1+s)²` is integrable on `(z,∞)` by
`integrableOn_two_div_one_add_sq`. -/
theorem L12dens_Fstar_integrableOn {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ z : ℝ, 0 ≤ z → MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Construction.Fstar α)) (Set.Ioi z) := by
  intro z hz
  -- the elementary integrand, and its `α`-multiple
  have hbase : IntegrableOn (fun s : ℝ => 2 / (1 + s) ^ 2) (Ioi z) :=
    integrableOn_two_div_one_add_sq z hz
  have hmul : IntegrableOn (fun s : ℝ => α * (2 / (1 + s) ^ 2)) (Ioi z) :=
    hbase.integrable.const_mul α
  -- `2/(1+s)² = F_*(s)/s` on `(z,∞)` (`z ≥ 0`, so `s ≠ 0` there)
  have hcongr : EqOn (fun s : ℝ => α * (2 / (1 + s) ^ 2))
      (fun s : ℝ => α * (Work.FM.Fstar s / s)) (Ioi z) := by
    intro s hs
    have hs0 : s ≠ 0 := by have := hs.out; linarith
    have hs1 : (1 : ℝ) + s ≠ 0 := by have := hs.out; linarith
    have hkey : Work.FM.Fstar s / s = 2 / (1 + s) ^ 2 := by
      unfold Work.FM.Fstar
      field_simp
    show α * (2 / (1 + s) ^ 2) = α * (Work.FM.Fstar s / s)
    rw [hkey]
  have h1 : IntegrableOn (fun s : ℝ => α * (Work.FM.Fstar s / s)) (Ioi z) :=
    hmul.congr_fun hcongr measurableSet_Ioi
  -- identify the density of `L₁₂` with `α · (F_*/s)`
  refine h1.congr_fun (fun s _ => ?_) measurableSet_Ioi
  exact (Work.Construction.L12dens_Fstar hα hα1 s).symm

end Work.FTS.MeridianDyn.Bridge.Pieces
end
end
-- ===== merged: Submission.Work.FTS.MuFix.MufunS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L₁₂(F_*) = 2α/(1+z)` on the whole range `z > -1`

The profile identity `L₁₂(F_*)(z) = 2α/(1+z)` is proved in
`Submission/Work/Construction/L12_Fstar_eq.lean` (`Work.Construction.L12_Fstar_eq`) under the
hypothesis `0 ≤ z`, inherited from `Work.FM.integral_Ioi_Fstar_div`, whose proof uses the
FTC lemma `MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'` with the profile computed as
`F_*(s)/s = 2/(1+s)²`.

Both the identity and its proof are valid on the larger range `z > -1`: the only obstruction
of the radial profile `F_*(s) = 2s/(1+s)²` is the pole of `2/(1+s)²` at `s = -1`, and every
`z > -1` gives an integration domain `(z, ∞)` on which the integrand is bounded.  The single
point `s = 0`, where `F_*(s)/s` and `2/(1+s)²` differ (Lean's totalised division gives
`0/0 = 0`), is Lebesgue-null, so the two functions are a.e. equal on `(z, ∞)` and the same
computation applies once the pointwise rewrite is replaced by an a.e. one.

This generalised form is what downstream `FTS`/`Nonlinear` consumers of the profile identity
need, since they work on the open half line `z > -1` rather than on `z ≥ 0`.
-/

noncomputable section

open scoped Real Topology MeasureTheory Filter
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

/-- The improper integral of the radial profile, `∫_z^∞ F_*(s)/s ds = 2/(1+z)`, for every
`z > -1`.  This is `Work.FM.integral_Ioi_Fstar_div` with the hypothesis `0 ≤ z` relaxed to
`-1 < z`; the two only differ at the null set `{0}`, on which the pointwise identity
`F_*(s)/s = 2/(1+s)²` fails. -/
theorem integral_Ioi_Fstar_div_of_gt_neg_one (z : ℝ) (hz : -1 < z) :
    ∫ s in Ioi z, Work.FM.Fstar s / s = 2 / (1 + z) := by
  -- `F_*(s)/s = 2/(1+s)^2` off the null set `{0}`
  have hae : ∀ᵐ s ∂(volume : MeasureTheory.Measure ℝ),
      s ∈ Ioi z → Work.FM.Fstar s / s = 2 / (1 + s) ^ 2 := by
    rw [MeasureTheory.ae_iff]
    have hsub : {s : ℝ | ¬ (s ∈ Ioi z → Work.FM.Fstar s / s = 2 / (1 + s) ^ 2)}
        ⊆ ({0} : Set ℝ) := by
      intro s hs
      by_contra h0
      refine hs (fun hsz => ?_)
      have hs1 : (0 : ℝ) < 1 + s := by have hsz' : z < s := hsz; linarith
      have h1 : (1 : ℝ) + s ≠ 0 := ne_of_gt hs1
      have h2 : (1 + s) ^ 2 ≠ 0 := pow_ne_zero 2 h1
      have hsne : s ≠ 0 := by intro h; exact h0 (by simp [h])
      unfold Work.FM.Fstar
      field_simp
    refine MeasureTheory.measure_mono_null hsub ?_
    rw [Real.volume_singleton]
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioi hae]
  -- `∫_z^∞ 2/(1+s)^2 ds` by FTC-2, with primitive `-2/(1+s)` (a limit `0` at `+∞`)
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun t : ℝ => -2 / (1 + t)) (g' := fun t : ℝ => 2 / (1 + t) ^ 2) (a := z) (l := 0)
    ?_ ?_ ?_
  · rw [key]; ring
  · intro x hx
    have hx1 : (1 : ℝ) + x ≠ 0 := by have := hx.out; linarith
    simpa using Work.FM.hasDerivAt_div_add_const (-2) 1 x hx1
  · intro x hx
    have hx0 : (0 : ℝ) < 1 + x := by have := hx.out; linarith
    positivity
  · have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
      tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
    have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 := h2.const_mul (-2 : ℝ)
    simpa [div_eq_mul_inv] using h3

/-- `L₁₂(F_*)(z) = 2α/(1+z)` for every `z > -1`, the generalisation of
`Work.Construction.L12_Fstar_eq` (which assumes `0 ≤ z`) needed by the `FstarPkg` consumers.

The proof separates the angular integration (`Work.Construction.L12dens_Fstar`, valid for
every `s`) from the radial one, which is `integral_Ioi_Fstar_div_of_gt_neg_one` above. -/
theorem L12_Fstar_eq_of_gt_neg_one {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : -1 < z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) := by
  rw [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun (s := Ioi z) measurableSet_Ioi
        (fun s _ => show Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) s
            = α * (Work.FM.Fstar s / s) from Work.Construction.L12dens_Fstar hα hα1 s)]
  rw [MeasureTheory.integral_const_mul, integral_Ioi_Fstar_div_of_gt_neg_one z hz]
  ring

end Work.FTS.Nonlinear.FstarPkg
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.FstarPkg

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces

-- Intended full name: `Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial`
-- (declare it inside `namespace Work.FTS.Nonlinear.FstarPkg`).  This is the `Γ ⊗ H` version
-- of `Work.Spaces.Gamma_WlInf` (which is the special case `H = hKer`, `D = 1`); the proof
-- pattern is the same: `pzIter_decomp` / `DthIter_decomp` factor the iterated derivatives,
-- `Gam_bounds` gives `|Γ| ≤ 1`, `dthU_Gam_le` gives `|D_θ^j Γ| ≤ α (tBound (j-1) 0) Γ`,
-- `Gam_mul_weight_le` gives `α Γ sin(2θ)^{-α/5}/(α+sin 2θ) ≤ 1`, and `hB` bounds the
-- radial `(z+1)^k H^{(k)}`.

/-- Boundedness of a function on the domain (`Work.Spaces.SupFinite`) from a pointwise
bound on the domain; the analogue of `Work.Spaces.HkAux.supFinite_of_pointwise`. -/
lemma supFinite_of_pointwise_bound {g : ℝ → ℝ → ℝ} {C : ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |g z θ| ≤ C) :
    Work.Spaces.SupFinite g :=
  ⟨C, by rintro y ⟨z, hz, θ, hθ, rfl⟩; exact h z hz θ hθ⟩

theorem WlInf_Gamma_radial {l : ℕ} {H : ℝ → ℝ} {B : ℕ → ℝ} {D α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hB : ∀ k, k ≤ l → ∀ z, 0 ≤ z → |(z + 1) ^ k * deriv^[k] H z| ≤ B k) :
    Work.Spaces.WlInfMem α l (fun z θ => D * (Work.Spaces.Gam α θ * H z)) ∧
      Work.Spaces.WlInf α l (fun z θ => D * (Work.Spaces.Gam α θ * H z))
        ≤ |D| * ((∑ k ∈ Finset.range (l + 1), B k)
            + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
                (if 1 ≤ j ∧ k + j ≤ l then B k * Work.Spaces.tBound (j - 1) 0 else 0)) := by
  classical
  -- Reassociate the amplitude `D` onto the angular factor.
  have hf : (fun z θ => D * (Work.Spaces.Gam α θ * H z))
      = fun z θ => (D * Work.Spaces.Gam α θ) * H z := by
    funext z θ; ring
  -- Separation of variables for the angular derivatives.
  have hDthF : ∀ j : ℕ, Work.Spaces.DthIter j (fun z θ => (D * Work.Spaces.Gam α θ) * H z)
      = fun z θ => dthU^[j] (fun t => D * Work.Spaces.Gam α t) θ * H z := by
    intro j
    funext z θ
    exact Work.Spaces.DthIter_decomp j (fun t => D * Work.Spaces.Gam α t) H z θ
  have hdthD : ∀ j : ℕ, dthU^[j] (fun t => D * Work.Spaces.Gam α t)
      = fun t => D * dthU^[j] (fun t => Work.Spaces.Gam α t) t := by
    intro j
    exact Work.Spaces.dthU_iter_const_mul j D (fun t => Work.Spaces.Gam α t)
  have hBnn : ∀ k, k ≤ l → 0 ≤ B k := by
    intro k hk
    exact le_trans (abs_nonneg _) (hB k hk 0 (le_refl 0))
  -- The two pointwise estimates.
  have hpt1 : ∀ k, k ≤ l → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => (D * Work.Spaces.Gam α θ) * H z) z θ|
        ≤ |D| * B k := by
    intro k hk z hz θ hθ
    rw [Work.Spaces.pzIter_decomp k (fun θ => D * Work.Spaces.Gam α θ) H z θ]
    have hGam := Work.Spaces.Gam_bounds α θ hα hθ
    have hDz := hB k hk z hz
    rw [show (z + 1) ^ k * ((D * Work.Spaces.Gam α θ) * deriv^[k] H z)
          = (D * Work.Spaces.Gam α θ) * ((z + 1) ^ k * deriv^[k] H z) by ring]
    rw [abs_mul, abs_mul, abs_of_nonneg hGam.1]
    calc |D| * Work.Spaces.Gam α θ * |(z + 1) ^ k * deriv^[k] H z|
        ≤ |D| * 1 * B k := by
          refine mul_le_mul ?_ hDz (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hGam.2 (abs_nonneg D)
      _ = |D| * B k := by ring
  have hpt2 : ∀ j, 1 ≤ j → ∀ k, k + j ≤ l → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (fun z θ => (D * Work.Spaces.Gam α θ) * H z)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        ≤ |D| * B k * Work.Spaces.tBound (j - 1) 0 := by
    intro j hj1 k hkj z hz θ hθ
    have hkl : k ≤ l := by omega
    rw [hDthF j]
    rw [Work.Spaces.pzIter_decomp k (fun θ => dthU^[j] (fun t => D * Work.Spaces.Gam α t) θ) H]
    rw [hdthD j]
    have hsin : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc (by
      constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos])
    have hden : 0 < α + Real.sin (2 * θ) := by linarith
    have hw : 0 ≤ Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
      div_nonneg (Real.rpow_nonneg hsin _) (le_of_lt hden)
    rw [show (z + 1) ^ k * (D * dthU^[j] (fun t => Work.Spaces.Gam α t) θ * deriv^[k] H z)
          * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
        = (D * dthU^[j] (fun t => Work.Spaces.Gam α t) θ) * ((z + 1) ^ k * deriv^[k] H z)
          * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) by ring]
    rw [abs_mul, abs_mul, abs_of_nonneg hw]
    have hGam := Work.Spaces.Gam_bounds α θ hα hθ
    have hDz := hB k hkl z hz
    have hTBnn := Work.Spaces.tBound_nonneg (j - 1) 0
    have hDnn : 0 ≤ |D| := abs_nonneg D
    have hBknn : 0 ≤ B k := hBnn k hkl
    have hdth_le := Work.Spaces.dthU_Gam_le j hj1 α hα hα1 θ hθ
    calc |D * dthU^[j] (fun t => Work.Spaces.Gam α t) θ| * |(z + 1) ^ k * deriv^[k] H z|
          * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ (|D| * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ)) * B k
          * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
          apply mul_le_mul_of_nonneg_right _ hw
          refine mul_le_mul ?_ hDz (abs_nonneg _) ?_
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_left hdth_le hDnn
          · exact mul_nonneg hDnn (mul_nonneg (mul_nonneg (le_of_lt hα) hTBnn) hGam.1)
      _ = |D| * B k * Work.Spaces.tBound (j - 1) 0
          * (α * Work.Spaces.Gam α θ
            * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
      _ ≤ |D| * B k * Work.Spaces.tBound (j - 1) 0 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg hDnn hBknn) hTBnn)
          rw [← mul_div_assoc]
          exact Work.Spaces.Gam_mul_weight_le α θ hα hθ
      _ = |D| * B k * Work.Spaces.tBound (j - 1) 0 := by ring
  constructor
  · -- Membership in `𝒲^{l,∞}`.
    rw [Work.Spaces.WlInfMem, hf]
    refine ⟨?_, ?_⟩
    · intro k hk
      exact supFinite_of_pointwise_bound (fun z hz θ hθ => hpt1 k hk z hz θ hθ)
    · intro j hj k hk hj1 hjk
      exact supFinite_of_pointwise_bound (fun z hz θ hθ => hpt2 j hj1 k hjk z hz θ hθ)
  · -- The norm bound.
    rw [Work.Spaces.WlInf, hf]
    have hterm1 : ∀ k ∈ Finset.range (l + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (fun z θ => (D * Work.Spaces.Gam α θ) * H z) z θ)
          ≤ |D| * B k := by
      intro k hk
      exact Work.Spaces.supAbs_le (fun z hz θ hθ =>
        hpt1 k (by simpa using Finset.mem_range.mp hk) z hz θ hθ)
    have hterm2 : ∀ j ∈ Finset.range (l + 1), ∀ k ∈ Finset.range (l + 1),
        (if 1 ≤ j ∧ k + j ≤ l then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k
                (Work.Spaces.DthIter j (fun z θ => (D * Work.Spaces.Gam α θ) * H z)) z θ
            * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          else 0)
        ≤ (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Work.Spaces.tBound (j - 1) 0) else 0) := by
      intro j hj k hk
      split_ifs with hcond
      · exact le_trans (Work.Spaces.supAbs_le (fun z hz θ hθ =>
          hpt2 j hcond.1 k hcond.2 z hz θ hθ)) (le_of_eq (by ring))
      · exact le_refl 0
    have hsum1 : (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (fun z θ => (D * Work.Spaces.Gam α θ) * H z) z θ))
        ≤ ∑ k ∈ Finset.range (l + 1), |D| * B k := Finset.sum_le_sum hterm1
    have hsum2 : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
              * Work.Spaces.pzIter k
                  (Work.Spaces.DthIter j (fun z θ => (D * Work.Spaces.Gam α θ) * H z)) z θ
              * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            else 0))
        ≤ ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
            (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Work.Spaces.tBound (j - 1) 0) else 0) :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk => hterm2 j hj k hk))
    have hsum2eq : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Work.Spaces.tBound (j - 1) 0) else 0))
        = |D| * (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
            (if 1 ≤ j ∧ k + j ≤ l then B k * Work.Spaces.tBound (j - 1) 0 else 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      by_cases h : 1 ≤ j ∧ k + j ≤ l <;> simp [h]
    have hsum1eq : (∑ k ∈ Finset.range (l + 1), |D| * B k)
        = |D| * (∑ k ∈ Finset.range (l + 1), B k) :=
      (Finset.mul_sum (s := Finset.range (l + 1)) (f := B) (a := |D|)).symm
    calc (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (fun z θ => (D * Work.Spaces.Gam α θ) * H z) z θ))
          + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then
                Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
                  * Work.Spaces.pzIter k
                      (Work.Spaces.DthIter j (fun z θ => (D * Work.Spaces.Gam α θ) * H z)) z θ
                  * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
                else 0)
        ≤ (∑ k ∈ Finset.range (l + 1), |D| * B k)
          + (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Work.Spaces.tBound (j - 1) 0) else 0)) :=
          add_le_add hsum1 hsum2
      _ = |D| * ((∑ k ∈ Finset.range (l + 1), B k)
          + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then B k * Work.Spaces.tBound (j - 1) 0 else 0)) := by
          rw [hsum1eq, hsum2eq, mul_add]

end Work.FTS.Nonlinear.FstarPkg
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.c2mInv_points =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted `z`-derivative bound for `(z,θ) ↦ c2m θ · 2α/(1+z)`

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021).

The multiplier `c2m θ = cos(2θ) - sin² θ` (`Work.Construction.c2m`) of the transport term
is applied to the rational function `2α/(1+z)`.  This file proves the elementary weighted
estimate

`|(z+1)^k ∂_z^k (c2m θ · 2α/(1+z))(z)| ≤ 4 α k!`   for `z ≥ 0`, `0 < α ≤ 1`, `k ≤ 4`,

i.e. `Work.FTS.Nonlinear.FstarPkg.c2mInv_points`.  It is the `𝒲^{k,∞}`-input (the constant
of `Spaces.Jk`/`WlInf`) for the `c2m θ · 2α/(1+z)` factor appearing in the linearized
equations of §Modulation.

The proof is the same shape as `Work.Spaces.pzIter_hKer_bound` (which treats
`z/(1+z)²`): compute the `k`-th derivative in closed form.  Here the function is even
simpler; writing `B(z) = 2α/(1+z) = 2α·(1+z)⁻¹`, a direct induction gives

`deriv^[k] B z = (-1)^k k! · 2α · (1+z)^{-(k+1)}`  for `z > -1`,

whence

`(z+1)^k deriv^[k] B z = (-1)^k k! · 2α · (1+z)⁻¹`,

and `|c2m θ| ≤ 2`, `(1+z)⁻¹ ≤ 1` for `z ≥ 0` give the stated `4 α k!`.
-/

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

-- The fixed statement carries the hypotheses `α ≤ 1` and `k ≤ 4`, which the estimate
-- below does not need (it holds for all `α > 0` and all `k`).
set_option linter.unusedVariables false

/-! ## The closed form of the `k`-th derivative of `(1+z)⁻¹` -/

/-- The closed form of the `k`-th derivative of `z ↦ (1+z)⁻¹`:
`(-1)^k k! (1+z)^{-(k+1)}`, written with the powers of `(1+z)⁻¹`. -/
noncomputable def nInvClosed (k : ℕ) (z : ℝ) : ℝ :=
  ((-1) ^ k * (k.factorial : ℝ)) * (((1 + z)⁻¹) ^ (k + 1))

/-- The value of the derivative of the closed form: the derivative of `nInvClosed k` is
`nInvClosed (k+1)` (at every point where `1+z ≠ 0`). -/
lemma nInvClosed_step (k : ℕ) (z : ℝ) :
    ((-1) ^ k * (k.factorial : ℝ)) *
        ((↑(k + 1) : ℝ) * ((1 + z)⁻¹) ^ k * (-(((1 + z)⁻¹) ^ 2)))
      = nInvClosed (k + 1) z := by
  have hsign : (-1 : ℝ) ^ (k + 1) = -(-1) ^ k := by rw [pow_succ]; ring
  have hfact : (((k + 1).factorial : ℝ)) = (↑(k + 1) * ↑k.factorial) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hpow : (↑(k + 1) : ℝ) * ((1 + z)⁻¹) ^ k * (-(((1 + z)⁻¹) ^ 2))
      = -(↑(k + 1) * ((1 + z)⁻¹) ^ (k + 2)) := by
    rw [mul_neg, mul_assoc, ← pow_add]
  unfold nInvClosed
  rw [hsign, hfact, hpow]
  ring

/-- The closed form has the expected derivative. -/
lemma hasDerivAt_nInvClosed (k : ℕ) {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (nInvClosed k) (nInvClosed (k + 1) z) z := by
  have hz' : (1 + z) ≠ 0 := by intro h; exact hz (by linarith)
  have hv : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-((1 + z)⁻¹) ^ 2) z := by
    have hh : HasDerivAt (fun t : ℝ => 1 + t) 1 z := by
      simpa using (hasDerivAt_id z).const_add (1 : ℝ)
    have hv2 := hh.inv hz'
    have hval : -(1 : ℝ) / (1 + z) ^ 2 = -((1 + z)⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow]; ring
    rwa [hval] at hv2
  have hp := hv.pow (k + 1)
  have hc := hp.const_mul ((-1) ^ k * (k.factorial : ℝ))
  have hfun : (fun y : ℝ => ((-1) ^ k * (k.factorial : ℝ)) *
      ((fun t : ℝ => (1 + t)⁻¹) ^ (k + 1)) y) = nInvClosed k := by
    funext y; simp only [Pi.pow_apply, nInvClosed]
  have hv3 : ((-1) ^ k * (k.factorial : ℝ)) *
      ((↑(k + 1) : ℝ) * (1 + z)⁻¹ ^ (k + 1 - 1) * (-((1 + z)⁻¹) ^ 2))
      = nInvClosed (k + 1) z := by
    rw [show k + 1 - 1 = k by omega]
    exact nInvClosed_step k z
  rw [hfun, hv3] at hc
  exact hc

/-- The `k`-th derivative of `z ↦ (1+z)⁻¹` for `z > -1`. -/
theorem iter_deriv_nInvClosed : ∀ (k : ℕ) (z : ℝ),
    -1 < z → deriv^[k] (fun z : ℝ => (1 + z)⁻¹) z = nInvClosed k z := by
  intro k
  induction k with
  | zero =>
    intro z _
    simp [nInvClosed]
  | succ k ih =>
    intro z hz
    rw [Function.iterate_succ_apply']
    have hev : (deriv^[k] (fun z : ℝ => (1 + z)⁻¹)) =ᶠ[𝓝 z] nInvClosed k := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact ih y hy
    rw [hev.deriv_eq]
    exact (hasDerivAt_nInvClosed k (by linarith)).deriv

/-! ## Constants pass through iterated derivatives -/

/-- A constant factor passes through `deriv^[k]` (no differentiability needed). -/
lemma deriv_iter_const_mul (c : ℝ) (f : ℝ → ℝ) (k : ℕ) :
    deriv^[k] (fun z => c * f z) = fun z => c * deriv^[k] f z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    rw [Work.Spaces.deriv_const_mul', Function.iterate_succ_apply']

/-! ## The weighted bound -/

/-- `|(z+1)^k nInvClosed k z| ≤ k!` for `z ≥ 0`: the weight `(z+1)^k` cancels all but
one factor of `(1+z)⁻¹`. -/
lemma nInvClosed_weighted (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    |(z + 1) ^ k * nInvClosed k z| ≤ (k.factorial : ℝ) := by
  have hz' : (1 + z) ≠ 0 := by positivity
  have hknn : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hpos : (0 : ℝ) < (1 + z)⁻¹ := by positivity
  have hpow : (z + 1) ^ k * ((1 + z)⁻¹) ^ (k + 1) = (1 + z)⁻¹ := by
    rw [pow_add, ← mul_assoc, ← mul_pow, show (z + 1) = (1 + z) by ring,
      mul_inv_cancel₀ hz', one_pow, one_mul, pow_one]
  have hsplit : (z + 1) ^ k * nInvClosed k z
      = ((-1 : ℝ) ^ k * (k.factorial : ℝ)) * ((z + 1) ^ k * ((1 + z)⁻¹) ^ (k + 1)) := by
    unfold nInvClosed; ring
  rw [hsplit, abs_mul, hpow]
  have h1 : |((-1 : ℝ) ^ k * (k.factorial : ℝ))| = (k.factorial : ℝ) := by
    rw [abs_mul, abs_of_nonneg hknn]; simp
  rw [h1, abs_of_nonneg (le_of_lt hpos)]
  exact mul_le_of_le_one_right hknn (inv_le_one_of_one_le₀ (by linarith))

/-! ## The iterated `z`-derivative of `c2m θ · 2α/(1+z)` -/

/-- `∂_z^k` of `(z,θ) ↦ c2m θ · 2α/(1+z)` in closed form (for `z > -1`). -/
lemma pzIter_c2m_inv (α : ℝ) (k : ℕ) (z θ : ℝ) (hz : -1 < z) :
    Work.Spaces.pzIter k (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z))) z θ
      = Work.Construction.c2m θ * (2 * α * nInvClosed k z) := by
  rw [Work.Spaces.pzIter_decomp k Work.Construction.c2m (fun z => 2 * α / (1 + z)) z θ]
  have hB : deriv^[k] (fun z : ℝ => 2 * α / (1 + z)) z = 2 * α * nInvClosed k z := by
    have h1 : (fun z : ℝ => 2 * α / (1 + z)) = fun z : ℝ => (2 * α) * ((1 + z)⁻¹) := by
      funext z; rw [div_eq_mul_inv]
    rw [h1, congrFun (deriv_iter_const_mul (2 * α) (fun z : ℝ => (1 + z)⁻¹) k) z,
      iter_deriv_nInvClosed k z hz]
  rw [hB]

/-- `|c2m θ| ≤ 2`. -/
lemma abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq]
  have hstep : |Real.cos (2 * θ) - Real.sin θ ^ 2|
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by
    have h := abs_sub_le (Real.cos (2 * θ)) (0 : ℝ) (Real.sin θ ^ 2)
    rwa [sub_zero, zero_sub, abs_neg] at h
  have hsin : |Real.sin θ ^ 2| = Real.sin θ ^ 2 := abs_of_nonneg (sq_nonneg _)
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := hstep
    _ = |Real.cos (2 * θ)| + Real.sin θ ^ 2 := by rw [hsin]
    _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) (Real.sin_sq_le_one θ)
    _ = 2 := by norm_num

/-- The weighted bound `|(z+1)^k ∂_z^k (c2m θ · 2α/(1+z))(z)| ≤ 4 α k!`.  (The hypotheses
`hα1 : α ≤ 1` and `hk : k ≤ 4` are part of the fixed statement; the estimate is proved
here for all `α > 0` and all `k`.) -/
theorem c2mInv_points (α z θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (k : ℕ) (hk : k ≤ 4) :
    |(z + 1) ^ k * Work.Spaces.pzIter k
        (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z))) z θ|
      ≤ 4 * α * (k.factorial : ℝ) := by
  have hz1 : -1 < z := by linarith
  have hα2 : (0 : ℝ) ≤ 2 * α := by linarith
  have hc2m : |Work.Construction.c2m θ| ≤ 2 := abs_c2m_le_two θ
  rw [pzIter_c2m_inv α k z θ hz1]
  rw [show (z + 1) ^ k * (Work.Construction.c2m θ * (2 * α * nInvClosed k z))
        = Work.Construction.c2m θ * (2 * α * ((z + 1) ^ k * nInvClosed k z)) by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hα2]
  calc |Work.Construction.c2m θ| * (2 * α * |(z + 1) ^ k * nInvClosed k z|)
      ≤ 2 * (2 * α * (k.factorial : ℝ)) := by
        apply mul_le_mul hc2m (mul_le_mul_of_nonneg_left (nInvClosed_weighted k z hz) hα2)
          (mul_nonneg hα2 (abs_nonneg _)) (by norm_num)
    _ = 4 * α * (k.factorial : ℝ) := by ring

end Work.FTS.Nonlinear.FstarPkg
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.GamSeqDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular sequence controlling the `dthU`-iterates of `deriv Γ`

With `Γ(θ) = (sin θ cos²θ)^{α/3}` and `D_θ = sin(2θ) ∂_θ` one has (on `(0,π/2)`)

  `D_θ Γ = α · q(θ) · Γ`,   `q(θ) = cos 2θ - 1/3`,      (`Work.Spaces.dthU_Gam`)

so `deriv Γ = α·q/(sin 2θ)·Γ = α·Gseq α 0·Γ/(sin θ cos θ)` with `Gseq α 0 = q/2`.  The
denominator `sin θ cos θ` is *not* preserved by `D_θ` alone, but a short computation shows
that the whole quotient is, provided one puts

  `Gseq α (d+1) := D_θ (Gseq α d) + g · Gseq α d`,   `g(θ) = (α-2) q(θ) - 2/3`,

i.e. `D_θ^d (deriv Γ) = α · Gseq α d · Γ/(sin θ cos θ)` for every `d` (proved in
`Gam_deriv_bounds.lean`).

This file only sets up the definitions and the elementary pointwise bounds on the factor
`g`; the induction that bounds all `D_θ`-iterates of `Gseq α d` by constants is stated (and
proved) separately as `Gseq_iter_bounded`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

local notation "C∞" => (⊤ : ℕ∞)

/-! ## The angular factor `g` -/

/-- The factor of the recursion for `Gseq`:
`gfun α θ = (α-2)·q(θ) - 2/3 = α·q(θ) - 2 cos 2θ`. -/
noncomputable def gfun (α θ : ℝ) : ℝ := (α - 2) * Work.Spaces.qfun θ - 2 / 3


/-- `|q(θ)| ≤ 4/3` everywhere. -/
theorem abs_qfun_le (θ : ℝ) : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
  rw [Work.Spaces.qfun_apply]
  have h1 : |Real.cos (2 * θ) - 1 / 3| ≤ |Real.cos (2 * θ)| + 1 / 3 := by
    have h := abs_sub_le (Real.cos (2 * θ)) 0 (1 / 3 : ℝ)
    rw [sub_zero, zero_sub, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)] at h
    exact h
  have h2 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
  linarith

/-! ## `dthU` and subtraction -/





/-! ## The sequence `Gseq` -/

/-- The angular sequence with `D_θ^d (deriv (Gam α)) = α · Gseq α d · Gam α / (sin θ cos θ)`
on `(0,π/2)`.  Defined by `Gseq α 0 = q/2` and
`Gseq α (d+1) = D_θ (Gseq α d) + gfun α · Gseq α d`. -/
noncomputable def Gseq (α : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun θ => Work.Spaces.qfun θ / 2
  | (d + 1) => fun θ => Work.Spaces.dthU (Gseq α d) θ + gfun α θ * Gseq α d θ

@[simp] theorem Gseq_zero (α θ : ℝ) : Gseq α 0 θ = Work.Spaces.qfun θ / 2 := rfl

@[simp] theorem Gseq_succ_apply (α : ℝ) (d : ℕ) (θ : ℝ) :
    Gseq α (d + 1) θ = Work.Spaces.dthU (Gseq α d) θ + gfun α θ * Gseq α d θ := rfl



/-! ## The pointwise bounds for the iterates of `g` -/




end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.dthIter_Gam_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular iterates of `Γ` are dominated by `Γ` (for fixed `α`)

`Γ(θ) = (sin θ cos²θ)^{α/3}` is one of the two basic building blocks of the paper
(jointly with the radial profile `z/(1+z)²`).  On the angular interval `Iθ = [0,π/2]`
the operator `Lop u = sin(2θ)·u'` is the action of `D_θ` on functions of `θ` alone, and
the identity

`D_θ^{j+1} Γ = α · Tfun j α · Γ`  on `(0,π/2)`

(`Work.Spaces.dthU_iter_Gam`) shows that each iterate of `Γ` is `Γ` times a coefficient
built from the bounded sequence `Tfun j α`.  The sibling
`Work.Spaces.dthU_Gam_le` bounds `α · Tfun j α` uniformly in `α ∈ (0,1]`; for the row-19
estimate only a *fixed* `α` is needed, and then the constant may depend on `α`.  This is
the `α`-dependent version: `Work.Spaces.Tfun_iter_bounded` is reproved with the bound
`M` allowed to depend on `α` (the only place the sibling uses `α ≤ 1` is the step
`α·S ≤ S`, which is dropped here).

The main result is `dthIter_Gam_le`: for every `i ≤ 4` and `θ ∈ Iθ`,
`|Lop^[i] Γ θ| ≤ C·Γ(θ)`.
-/

noncomputable section

open scoped Real Topology
open Work.Spaces

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false

local notation "C∞" => (⊤ : ℕ∞)

/-- The `α`-dependent version of `Work.Spaces.Tfun_iter_bounded`: for every `j` the
iterated angular derivatives `D_θ^m (Tfun j α)` are bounded on `Iθ` by a constant
`M α m` which is allowed to depend on `α` (the sibling `Tfun_iter_bounded` gives a bound
uniform in `α ≤ 1`; here `α > 0` is arbitrary). -/
lemma Tfun_iter_bounded_alpha (j : ℕ) :
    ∃ M : ℝ → ℕ → ℝ, (∀ α : ℝ, 0 ≤ α → ∀ m : ℕ, 0 ≤ M α m) ∧
      ∀ α : ℝ, 0 < α → ∀ θ : ℝ, θ ∈ Iθ → ∀ m : ℕ,
        |dthU^[m] (Tfun j α) θ| ≤ M α m := by
  induction j with
  | zero =>
      refine ⟨fun _ m => qBound m, fun α hα m => qBound_nonneg m, ?_⟩
      intro α hα θ hθ m
      have hT0 : Tfun 0 α = qfun := by funext t; rfl
      rw [hT0]
      exact dthU_qfun_le_qBound m hθ
  | succ j ih =>
      obtain ⟨M, hM0, hMbound⟩ := ih
      refine ⟨fun α m => M α (m + 1) + α * ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * qBound i * M α (m - i), ?_, ?_⟩
      · intro α hα m
        exact add_nonneg (hM0 α hα (m + 1)) (mul_nonneg hα (Finset.sum_nonneg fun i _ =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (qBound_nonneg i)) (hM0 α hα _)))
      · intro α hα θ hθ m
        have hTeq : Tfun (j+1) α = dthU (Tfun j α) + (fun θ => α * qfun θ) * (Tfun j α) := by
          funext t; rw [Tfun_succ]; simp only [dthU_apply, Pi.add_apply, Pi.mul_apply]
        have hsm : (fun θ => α * qfun θ) * (Tfun j α)
            = fun θ => α * ((qfun * (Tfun j α)) θ) := by
          funext t; simp only [Pi.mul_apply]; ring
        have hdiff1 : ContDiff ℝ C∞ (dthU (Tfun j α)) := dthU_smooth (Tfun_smooth j α)
        have hdiff2 : ContDiff ℝ C∞ ((fun θ => α * qfun θ) * (Tfun j α)) :=
          (contDiff_const.mul qfun_smooth).mul (Tfun_smooth j α)
        have hdecomp : dthU^[m] (Tfun (j+1) α)
            = fun θ => dthU^[m+1] (Tfun j α) θ + α * (dthU^[m] (qfun * (Tfun j α))) θ := by
          rw [hTeq, dthU_iter_add m _ _ hdiff1 hdiff2, hsm, dthU_iter_const_mul,
            dthU_iter_comp]
          funext t; simp only [Pi.add_apply]
        have hleib : dthU^[m] (qfun * (Tfun j α))
            = ∑ i ∈ Finset.range (m+1), dthCoef m qfun (Tfun j α) i :=
          dthU_iter_mul m qfun (Tfun j α) qfun_smooth (Tfun_smooth j α)
        calc |dthU^[m] (Tfun (j+1) α) θ|
            = |dthU^[m+1] (Tfun j α) θ + α * (dthU^[m] (qfun * (Tfun j α))) θ| := by
                rw [hdecomp]
          _ ≤ |dthU^[m+1] (Tfun j α) θ| + |α * (dthU^[m] (qfun * (Tfun j α))) θ| :=
                abs_add_le _ _
          _ = |dthU^[m+1] (Tfun j α) θ| + α * |(dthU^[m] (qfun * (Tfun j α))) θ| := by
                rw [abs_mul, abs_of_pos hα]
          _ = |dthU^[m+1] (Tfun j α) θ|
                + α * |(∑ i ∈ Finset.range (m+1), dthCoef m qfun (Tfun j α) i) θ| := by
                rw [hleib]
          _ = |dthU^[m+1] (Tfun j α) θ|
                + α * |∑ i ∈ Finset.range (m+1), dthCoef m qfun (Tfun j α) i θ| := by
                rw [Finset.sum_apply]
          _ ≤ M α (m+1)
                + α * ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * qBound i * M α (m-i) := by
                apply add_le_add
                · exact hMbound α hα θ hθ (m+1)
                · apply mul_le_mul_of_nonneg_left _ (le_of_lt hα)
                  calc |∑ i ∈ Finset.range (m+1), dthCoef m qfun (Tfun j α) i θ|
                      ≤ ∑ i ∈ Finset.range (m+1), |dthCoef m qfun (Tfun j α) i θ| :=
                        Finset.abs_sum_le_sum_abs _ _
                    _ ≤ ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * qBound i * M α (m-i) := by
                        apply Finset.sum_le_sum
                        intro i hi
                        have habs : |dthCoef m qfun (Tfun j α) i θ|
                            = (m.choose i : ℝ) * |dthU^[i] qfun θ|
                              * |dthU^[m-i] (Tfun j α) θ| := by
                          rw [dthCoef_apply, abs_mul, abs_mul,
                            abs_of_nonneg (Nat.cast_nonneg (m.choose i))]
                          ring
                        rw [habs]
                        exact mul_le_mul
                          (mul_le_mul_of_nonneg_left (dthU_qfun_le_qBound i hθ)
                            (Nat.cast_nonneg _))
                          (hMbound α hα θ hθ (m-i)) (abs_nonneg _)
                          (mul_nonneg (Nat.cast_nonneg _) (qBound_nonneg i))

/-- **Row 19, `Γ`-slot.**  For every fixed `α > 0` the first five angular iterates
`Lop^[i] Γ` (`i ≤ 4`) of `Γ(θ) = (sin θ cos²θ)^{α/3}` are dominated by `Γ` itself on the
angular interval `Iθ`.  The constant is allowed to depend on `α` (it is built from the
bounds `M_j α 0` of the coefficient sequence `Tfun `). -/
theorem dthIter_Gam_le {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Lop^[i] (fun θ => Work.Spaces.Gam α θ) θ| ≤ C * Work.Spaces.Gam α θ := by
  obtain ⟨M0, hM0n, hM0⟩ := Tfun_iter_bounded_alpha 0
  obtain ⟨M1, hM1n, hM1⟩ := Tfun_iter_bounded_alpha 1
  obtain ⟨M2, hM2n, hM2⟩ := Tfun_iter_bounded_alpha 2
  obtain ⟨M3, hM3n, hM3⟩ := Tfun_iter_bounded_alpha 3
  have hα0 : (0 : ℝ) ≤ α := le_of_lt hα
  have h0 : 0 ≤ M0 α 0 := hM0n α hα0 0
  have h1 : 0 ≤ M1 α 0 := hM1n α hα0 0
  have h2 : 0 ≤ M2 α 0 := hM2n α hα0 0
  have h3 : 0 ≤ M3 α 0 := hM3n α hα0 0
  set B : ℝ := M0 α 0 + M1 α 0 + M2 α 0 + M3 α 0 with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; linarith
  -- every `|Tfun j α|`, `j ≤ 3`, is bounded by `B`
  have hTb : ∀ j : ℕ, j ≤ 3 → ∀ θ ∈ Iθ, |Tfun j α θ| ≤ B := by
    intro j hj θ hθ
    interval_cases j
    · exact le_trans (by simpa using hM0 α hα θ hθ 0) (by rw [hBdef]; linarith)
    · exact le_trans (by simpa using hM1 α hα θ hθ 0) (by rw [hBdef]; linarith)
    · exact le_trans (by simpa using hM2 α hα θ hθ 0) (by rw [hBdef]; linarith)
    · exact le_trans (by simpa using hM3 α hα θ hθ 0) (by rw [hBdef]; linarith)
  refine ⟨1 + α * B, ?_, ?_⟩
  · have : 0 ≤ α * B := mul_nonneg hα0 hB0
    linarith
  intro i hi4 θ hθ
  have hG := Gam_bounds α θ hα hθ
  have hLop : Lop = dthU := rfl
  rw [hLop]
  rcases eq_or_ne i 0 with hi0 | hi0
  · subst hi0
    simp only [Function.iterate_zero_apply]
    rw [abs_of_nonneg hG.1]
    exact le_mul_of_one_le_left hG.1 (by linarith [mul_nonneg hα0 hB0])
  · have hipos : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    have h := dthU_iter_Gam_abs_bound i hipos α hα B
      (hTb (i - 1) (by omega)) θ hθ
    refine le_trans h (mul_le_mul_of_nonneg_right ?_ hG.1)
    have hαB : 0 ≤ α * B := mul_nonneg hα0 hB0
    linarith

end Work.FTS.Nonlinear.Pieces.RNP.row19
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter

namespace Work.FTS.PhiStar.FlatWAux

/-- The angular coefficients `Asf a θ = D_θ^a (sin 2·) θ`, i.e. the `a`-fold iterate of `Lop`
applied to `θ ↦ sin(2θ)`. -/
def Asf (a : ℕ) : ℝ → ℝ := (Work.Spaces.Lop^[a]) (fun θ : ℝ => Real.sin (2 * θ))


theorem Asf_succ (a : ℕ) : Asf (a + 1) = Work.Spaces.Lop (Asf a) :=
  Function.iterate_succ_apply' Work.Spaces.Lop a (fun θ : ℝ => Real.sin (2 * θ))

theorem Asf_contDiff : ∀ a : ℕ, ∀ n : ℕ, ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) (Asf a) := by
  intro a
  induction a with
  | zero =>
      intro n
      show ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ))
      fun_prop
  | succ a ih =>
      intro n
      have h1 : ContDiff ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Asf a) := ih (n + 1)
      have hcast : (((n : ℕ)) : WithTop ℕ∞) + 1 = (((n + 1 : ℕ)) : WithTop ℕ∞) := by
        push_cast; ring
      rw [← hcast] at h1
      have hs : ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) := by
        fun_prop
      rw [Asf_succ]
      show ContDiff ℝ ((n : ℕ) : WithTop ℕ∞)
        (fun θ : ℝ => Real.sin (2 * θ) * deriv (Asf a) θ)
      exact hs.mul h1.deriv'

theorem Asf_deriv_continuous (k : ℕ) : Continuous (deriv (Asf k)) := by
  have h2 : ContDiff ℝ (((2 : ℕ)) : WithTop ℕ∞) (Asf k) := Asf_contDiff k 2
  have hc : (((1 : ℕ)) : WithTop ℕ∞) + 1 = (((2 : ℕ)) : WithTop ℕ∞) := by push_cast; norm_num
  rw [← hc] at h2
  exact h2.deriv'.continuous

/-- Uniform bound for the coefficient functions `Asf k` and their derivatives, `k ≤ n`, on a
compact interval. -/
theorem Asf_bound_le (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      (∀ k ≤ n, ∀ y ∈ Set.Icc a b, |Asf k y| ≤ C) ∧
      (∀ k ≤ n, ∀ y ∈ Set.Icc a b, |deriv (Asf k) y| ≤ D) := by
  have hex : ∀ k : ℕ, ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      (∀ y ∈ Set.Icc a b, |Asf k y| ≤ C) ∧ (∀ y ∈ Set.Icc a b, |deriv (Asf k) y| ≤ D) := by
    intro k
    have h1 : ContinuousOn (Asf k) (Set.Icc a b) := (Asf_contDiff k 0).continuous.continuousOn
    have h2 : ContinuousOn (deriv (Asf k)) (Set.Icc a b) :=
      (Asf_deriv_continuous k).continuousOn
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn h1
    obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn h2
    refine ⟨max C 0, max D 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
    · intro y hy
      exact le_trans (by simpa [Real.norm_eq_abs] using hC y hy) (le_max_left _ _)
    · intro y hy
      exact le_trans (by simpa [Real.norm_eq_abs] using hD y hy) (le_max_left _ _)
  choose C D hC0 hD0 hCb hDb using hex
  refine ⟨∑ k ∈ Finset.range (n + 1), C k, ∑ k ∈ Finset.range (n + 1), D k,
    Finset.sum_nonneg (fun k _ => hC0 k), Finset.sum_nonneg (fun k _ => hD0 k), ?_, ?_⟩
  · intro k hk y hy
    exact le_trans (hCb k y hy)
      (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
  · intro k hk y hy
    exact le_trans (hDb k y hy)
      (Finset.single_le_sum (fun j _ => hD0 j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))

/-- `Lop` costs exactly one order of `ContDiffOn` on an open set. -/
theorem contDiffOn_Lop {u : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {n : ℕ}
    (hu : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) u U) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Work.Spaces.Lop u) U := by
  have hcast : (((n : ℕ)) : WithTop ℕ∞) + 1 = (((n + 1 : ℕ)) : WithTop ℕ∞) := by
    push_cast; ring
  have hs : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) U := by
    fun_prop
  have hd : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (deriv u) U := by
    refine hu.deriv_of_isOpen hU ?_
    rw [hcast]
  have : Work.Spaces.Lop u = (fun θ : ℝ => Real.sin (2 * θ)) * deriv u := rfl
  rw [this]
  exact hs.mul hd

/-- Iterating `Lop` costs one order per application. -/
theorem contDiffOn_Lop_iter (k : ℕ) {u : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) :
    ∀ n : ℕ, ContDiffOn ℝ (((n + k : ℕ)) : WithTop ℕ∞) u U →
      ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) ((Work.Spaces.Lop^[k]) u) U := by
  induction k with
  | zero => intro n hu; simpa using hu
  | succ k ih =>
      intro n hu
      rw [Function.iterate_succ_apply']
      refine contDiffOn_Lop hU ?_
      refine ih (n + 1) ?_
      have hnat : n + 1 + k = n + (k + 1) := by omega
      rw [hnat]
      exact hu

/-- `iteratedDeriv` costs orders of `ContDiffOn` on an open set. -/
theorem contDiffOn_iteratedDeriv {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) :
    ∀ r : ℕ, ∀ n : ℕ, ContDiffOn ℝ (((n + r : ℕ)) : WithTop ℕ∞) g U →
      ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (iteratedDeriv r g) U := by
  intro r
  induction r with
  | zero =>
      intro n hg
      simpa using hg
  | succ r ih =>
      intro n hg
      rw [iteratedDeriv_succ]
      have hnat : (n + 1) + r = n + (r + 1) := by omega
      have hprev : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (iteratedDeriv r g) U :=
        ih (n + 1) (by rw [hnat]; exact hg)
      have hcast : (((n : ℕ)) : WithTop ℕ∞) + 1 = (((n + 1 : ℕ)) : WithTop ℕ∞) := by
        push_cast; ring
      refine hprev.deriv_of_isOpen hU ?_
      rw [hcast]

/-- **Recursion of the `Lop`-iterates.**  On an open set `U` on which `g` is of class
`C^{i+1}`,

`Lop^[i+1] g = ∑_{a ≤ i} C(i,a) · Asf a · Lop^[i-a] (deriv g)`. -/
theorem Lop_iter_succ_eq_sum (i : ℕ) {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hg : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) g U) :
    ∀ θ ∈ U, (Work.Spaces.Lop^[i + 1]) g θ
      = ∑ a ∈ Finset.range (i + 1),
          (i.choose a : ℝ) * (Asf a θ * (Work.Spaces.Lop^[i - a]) (deriv g) θ) := by
  intro θ hθ
  rw [Function.iterate_succ_apply]
  have hlop : Work.Spaces.Lop g = (fun θ' : ℝ => Real.sin (2 * θ')) * deriv g := rfl
  rw [hlop]
  have hs : ContDiffOn ℝ ((i : ℕ) : WithTop ℕ∞) (fun θ' : ℝ => Real.sin (2 * θ')) U := by
    fun_prop
  have hcast : (((i : ℕ)) : WithTop ℕ∞) + 1 = (((i + 1 : ℕ)) : WithTop ℕ∞) := by
    push_cast; ring
  have hdg : ContDiffOn ℝ ((i : ℕ) : WithTop ℕ∞) (deriv g) U := by
    refine hg.deriv_of_isOpen hU ?_
    rw [hcast]
  have h := Work.FTS.EllipticEst.RPFresh.DivSinOpen.Lop_iter_mul_eqOn_fin i i
    (fun θ' : ℝ => Real.sin (2 * θ')) (deriv g) U hU hs hdg le_rfl hθ
  rw [h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show (Work.Spaces.Lop^[a]) (fun θ' : ℝ => Real.sin (2 * θ')) = Asf a from rfl]

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_head_shaped =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- **Head piece, weighted by `z ^ (-r)`.**

For `r ≥ 1`, `z > 0` and `c` with `∫_0^∞ c² < ∞`, the near-origin Green integral weighted
by `z ^ (-r)` is bounded by the `L²` mass of `c`:

  `|z ^ (-r) ∫_0^z c t · t ^ (r-1) dt| ≤ √(∫_{Ioi 0} c²) · z ^ (-1/2) / √(2r-1)`.

This is `Work.EllipticEst.ModalSolution.radGreen_head_bound` (Cauchy–Schwarz for `√(c²)`
against `t ^ (r-1)` on `(0,z)` together with `∫_0^z t ^ (2r-2) = z ^ (2r-1)/(2r-1)`,
giving the unweighted bound `|∫_0^z c t ^ (r-1)| ≤ √(∫ c²) · z ^ (r - 1/2) / √(2r-1)`)
multiplied through by `z ^ (-r) > 0`, using `z ^ (-r) · z ^ (r - 1/2) = z ^ (-1/2)`. -/
theorem radGreen_head_shaped (c : ℝ → ℝ)
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    {r z : ℝ} (hr : 1 ≤ r) (hz : 0 < z) :
    |z ^ (-r) * (∫ t in (0 : ℝ)..z, c t * t ^ (r - 1))| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * r - 1) := by
  have hzr : 0 < z ^ (-r) := Real.rpow_pos_of_pos hz _
  -- the key exponent identity, valid because `z > 0`
  have hzA : z ^ (-r) * z ^ (r - 1 / 2) = z ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hhead : |∫ t in (0 : ℝ)..z, c t * t ^ (r - 1)| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (r - 1 / 2) / Real.sqrt (2 * r - 1) :=
    Work.EllipticEst.ModalSolution.radGreen_head_bound c hc hr hz
  rw [abs_mul, abs_of_pos hzr]
  calc z ^ (-r) * |∫ t in (0 : ℝ)..z, c t * t ^ (r - 1)|
      ≤ z ^ (-r) * (Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (r - 1 / 2)
          / Real.sqrt (2 * r - 1)) :=
        mul_le_mul_of_nonneg_left hhead (le_of_lt hzr)
    _ = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * r - 1) := by
        rw [← hzA]
        ring

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.dthU_iter_mul_Ioo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary

open scoped Real Topology
open Filter

set_option autoImplicit false

/-- Right-hand side of the `m`-fold Leibniz expansion of `dthU` (the angular derivation
`φ ↦ sin(2θ)·φ'`). -/
noncomputable def dthLf (m : ℕ) (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m - i] g θ)

lemma dthLf_apply (m : ℕ) (f g : ℝ → ℝ) (θ : ℝ) :
    dthLf m f g θ = ∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m - i] g θ) := rfl

/-- The defining relation of `dthU`: `sin (2θ) · (dthU^i φ)' = dthU^{i+1} φ`.  Note that this is
unconditional: it is a definitional unfolding of `dthU`. -/
lemma sin_mul_deriv_dthU (i : ℕ) (φ : ℝ → ℝ) (θ : ℝ) :
    Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[i] φ) θ = Work.Spaces.dthU^[i + 1] φ θ := by
  rw [← Work.Spaces.dthU_iter_succ_apply i φ]
  rfl

/-- The pointwise derivative of the Leibniz sum, assuming only that the individual iterates of
`f` and `g` (up to `m`) are differentiable at `θ`. -/
lemma deriv_dthLf (m : ℕ) (f g : ℝ → ℝ) (θ : ℝ)
    (hf : ∀ i ≤ m, DifferentiableAt ℝ (Work.Spaces.dthU^[i] f) θ)
    (hg : ∀ i ≤ m, DifferentiableAt ℝ (Work.Spaces.dthU^[i] g) θ) :
    deriv (dthLf m f g) θ =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (deriv (Work.Spaces.dthU^[i] f) θ * Work.Spaces.dthU^[m - i] g θ
          + Work.Spaces.dthU^[i] f θ * deriv (Work.Spaces.dthU^[m - i] g) θ) := by
  have hterm : ∀ i ∈ Finset.range (m + 1),
      DifferentiableAt ℝ (fun y => (m.choose i : ℝ) *
        (Work.Spaces.dthU^[i] f y * Work.Spaces.dthU^[m - i] g y)) θ := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact ((hf i (by omega)).mul (hg (m - i) (by omega))).const_mul _
  unfold dthLf
  rw [deriv_fun_sum hterm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have him : i ≤ m := by omega
  have hmi : m - i ≤ m := by omega
  rw [Work.Spaces.deriv_const_mul']
  rw [show deriv (fun y => Work.Spaces.dthU^[i] f y * Work.Spaces.dthU^[m - i] g y) θ
      = deriv (Work.Spaces.dthU^[i] f) θ * Work.Spaces.dthU^[m - i] g θ
        + Work.Spaces.dthU^[i] f θ * deriv (Work.Spaces.dthU^[m - i] g) θ
      from deriv_mul (hf i him) (hg (m - i) hmi)]

/-- The iterated Leibniz rule for `dthU` on the open interval, with only differentiability of the
individual iterates as hypothesis. -/
lemma dthU_iter_mul_Ioo_aux :
    ∀ (m : ℕ) (f g : ℝ → ℝ),
      (∀ i ≤ m, DifferentiableOn ℝ (Work.Spaces.dthU^[i] f) (Set.Ioo 0 (Real.pi / 2))) →
      (∀ i ≤ m, DifferentiableOn ℝ (Work.Spaces.dthU^[i] g) (Set.Ioo 0 (Real.pi / 2))) →
      Set.EqOn (Work.Spaces.dthU^[m] (f * g)) (dthLf m f g) (Set.Ioo 0 (Real.pi / 2)) := by
  intro m
  induction m with
  | zero =>
      intro f g hf hg θ hθ
      simp [dthLf]
  | succ m ih =>
      intro f g hf hg θ hθ
      have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := IsOpen.mem_nhds isOpen_Ioo hθ
      have hfm : ∀ i ≤ m,
          DifferentiableOn ℝ (Work.Spaces.dthU^[i] f) (Set.Ioo 0 (Real.pi / 2)) :=
        fun i hi => hf i (by omega)
      have hgm : ∀ i ≤ m,
          DifferentiableOn ℝ (Work.Spaces.dthU^[i] g) (Set.Ioo 0 (Real.pi / 2)) :=
        fun i hi => hg i (by omega)
      have hAt : ∀ i ≤ m, DifferentiableAt ℝ (Work.Spaces.dthU^[i] f) θ :=
        fun i hi => (hfm i hi).differentiableAt hmem
      have hAtg : ∀ i ≤ m, DifferentiableAt ℝ (Work.Spaces.dthU^[i] g) θ :=
        fun i hi => (hgm i hi).differentiableAt hmem
      have hev : Filter.EventuallyEq (𝓝 θ) (Work.Spaces.dthU^[m] (f * g)) (dthLf m f g) :=
        (ih f g hfm hgm).eventuallyEq_of_mem hmem
      rw [← Work.Spaces.dthU_iter_succ_apply m (f * g), Work.Spaces.dthU_apply, hev.deriv_eq,
        deriv_dthLf m f g θ hAt hAtg, Finset.mul_sum]
      have h1 : ∀ i ∈ Finset.range (m + 1),
          Real.sin (2 * θ) * ((m.choose i : ℝ) *
              (deriv (Work.Spaces.dthU^[i] f) θ * Work.Spaces.dthU^[m - i] g θ
                + Work.Spaces.dthU^[i] f θ * deriv (Work.Spaces.dthU^[m - i] g) θ))
            = (m.choose i : ℝ) *
                (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m + 1 - i] g θ)
              + (m.choose i : ℝ) *
                (Work.Spaces.dthU^[i + 1] f θ * Work.Spaces.dthU^[m - i] g θ) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have him : i ≤ m := by omega
        rw [show Real.sin (2 * θ) * ((m.choose i : ℝ) *
              (deriv (Work.Spaces.dthU^[i] f) θ * Work.Spaces.dthU^[m - i] g θ
                + Work.Spaces.dthU^[i] f θ * deriv (Work.Spaces.dthU^[m - i] g) θ))
            = (m.choose i : ℝ) *
                ((Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[i] f) θ)
                  * Work.Spaces.dthU^[m - i] g θ)
              + (m.choose i : ℝ) *
                (Work.Spaces.dthU^[i] f θ
                  * (Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[m - i] g) θ))
            from by ring]
        rw [sin_mul_deriv_dthU i f θ, sin_mul_deriv_dthU (m - i) g θ,
          show m - i + 1 = m + 1 - i from by omega]
        ring
      trans ∑ i ∈ Finset.range (m + 1),
          ((m.choose i : ℝ) * (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m + 1 - i] g θ)
            + (m.choose i : ℝ) *
                (Work.Spaces.dthU^[i + 1] f θ * Work.Spaces.dthU^[m - i] g θ))
      · exact Finset.sum_congr rfl h1
      · rw [Finset.sum_add_distrib, dthLf_apply]
        have hS : (∑ i ∈ Finset.range (m + 2),
              ((m + 1).choose i : ℝ) *
                (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m + 1 - i] g θ))
            = (∑ i ∈ Finset.range (m + 1),
                  (m.choose i : ℝ) *
                    (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m + 1 - i] g θ))
              + ∑ i ∈ Finset.range (m + 1),
                  (m.choose i : ℝ) *
                    (Work.Spaces.dthU^[i + 1] f θ * Work.Spaces.dthU^[m - i] g θ) := by
          rw [show (m + 1) + 1 = m + 2 from rfl]
          exact Finset.sum_choose_succ_mul
            (fun a b => Work.Spaces.dthU^[a] f θ * Work.Spaces.dthU^[b] g θ) m
        rw [hS]

theorem dthU_iter_mul_Ioo (m : ℕ) (f g : ℝ → ℝ)
    (hf : ∀ i ≤ m, DifferentiableOn ℝ (Work.Spaces.dthU^[i] f) (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ i ≤ m, DifferentiableOn ℝ (Work.Spaces.dthU^[i] g) (Set.Ioo 0 (Real.pi / 2))) :
    Set.EqOn (Work.Spaces.dthU^[m] (f * g))
      (fun θ => ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m - i] g θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have h := dthU_iter_mul_Ioo_aux m f g hf hg hθ
  simp only [dthLf] at h
  exact h

end Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.abs_DthIter_Gam_le =====
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

/-! ## Two structural facts about `DthIter` on `z`-independent data

`Work.Spaces.DthIter_decomp` separates the angular and the radial variable; for a function of
`θ` alone (multiplied by the constant radial factor `1`) it identifies the two-variable
iterate `DthIter a` with the one-variable iterate `dthU^[a]`, where
`dthU φ = sin(2·) · φ'`. -/

/-- `D_θ^a` of a function of `θ` alone is the one-variable iterate `dthU^[a]`. -/
theorem DthIter_z_indep (a : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter a (fun _ θ' => g θ') z θ = Work.Spaces.dthU^[a] g θ := by
  have h : (fun (_ : ℝ) (θ : ℝ) => g θ) = (fun (z : ℝ) (θ : ℝ) => g θ * (1 : ℝ)) := by
    funext z θ; ring
  rw [h, Work.Spaces.DthIter_decomp]
  ring

/-- **`Tfun j α` is bounded on the angular interval `Iθ`.**  This is continuity plus
compactness of `Iθ = [0, π/2]`; the bound depends on `j` and on `α`, which is all that the
chain rule identity `D_θ^{j+1}Γ = α·Tfun j α·Γ` needs.  (No restriction on `α > 0` is used:
`Tfun j α` is smooth for every real `α`.) -/
theorem exists_Tfun_bound (α : ℝ) (j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun j α θ| ≤ M := by
  have hcont : ContinuousOn (Work.Spaces.Tfun j α) Work.Spaces.Iθ :=
    (Work.Spaces.Tfun_smooth j α).continuous.continuousOn
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
  have h := hC θ hθ
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- **Every `D_θ`-iterate of the angular profile `Γ(θ) = (sin θ cos²θ)^{α/3}` is dominated by
`Γ` itself**, for `α > 0`.

Here `D_θ = sin(2θ)∂_θ` (`Work.Spaces.Dth`), so `D_θ^a Γ = Γ·q_a` with
`q_1 = (2α/3)(cos²θ - 2sin²θ) = (2α/3)(1 - 3sin²θ)`, and inductively `q_{a+1}` is again a
polynomial in `sin²θ` (the factor `sin(2θ)` in `D_θ` exactly absorbs the chain-rule factor);
hence `q_a` is continuous on `[0,π/2]` and bounded by some `C > 0` independent of `θ`.

This is the input of the *angular* boundary traces of the separated product
`(z,θ) ↦ Γ(θ)·r(z)`: the trace weighs the `a`-th iterate by `sin(2θ)^{1-γ}` and needs the
product to vanish at `θ = 0, π/2⁻`, where `sin(2θ)^{1-γ}Γ² ~ sin(2θ)^{1-γ+2α/3}` with
`1-γ+2α/3 = α(2/3 - 1/10) > 0` for `α > 0`. -/
theorem abs_DthIter_Gam_le {α : ℝ} (hα : 0 < α) (a : ℕ) (ha : a ≤ 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ C * Work.Spaces.Gam α θ := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · -- `a = 0`: the iterate is `Γ` itself, and `Γ ≤ 1` on `Iθ`.
    subst h0
    refine ⟨1, one_pos, ?_⟩
    intro θ hθ0 hθ1
    have hmem : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
    have hG := (Work.Spaces.Gam_bounds α θ hα hmem).1
    rw [Work.Spaces.DthIter_zero, abs_of_nonneg hG]
    linarith
  · -- `a ≥ 1`: `D_θ^a Γ = α·Tfun (a-1) α·Γ` on `(0,π/2)`, and `Tfun (a-1) α` is bounded.
    obtain ⟨M, hM0, hM⟩ := exists_Tfun_bound α (a - 1)
    refine ⟨α * M + 1, by positivity, ?_⟩
    intro θ hθ0 hθ1
    have hmem : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
    have hG := (Work.Spaces.Gam_bounds α θ hα hmem).1
    rw [DthIter_z_indep a (fun θ' => Work.Spaces.Gam α θ') 0 θ]
    have hb := Work.Spaces.dthU_iter_Gam_abs_bound a hpos α hα M hM θ hmem
    have hAM : 0 ≤ α * M := mul_nonneg hα.le hM0
    calc |Work.Spaces.dthU^[a] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * M * Work.Spaces.Gam α θ := hb
      _ ≤ (α * M + 1) * Work.Spaces.Gam α θ := by nlinarith [hG, hAM]

end Work.FTS.StrongEps.EpsE4Thr.TracesAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SupZ.sliceCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory

namespace Work.FTS.StrongPersist.SupZ

/-- Slicewise Cauchy–Schwarz on the angular interval `Iθ = [0, π/2]`: for a fixed `s > 0`,
if the slices `θ ↦ Φ s θ` and `θ ↦ Φ' s θ` are (a.e.) strongly measurable on `Iθ` — which
follows from continuity of the corresponding two-variable functions on the open quadrant
`(0,∞) × (0,π/2)` — and square-integrable there, then

`∫_{Iθ} |Φ s θ · Φ' s θ| ≤ √( (∫_{Iθ} Φ s θ²) · (∫_{Iθ} Φ' s θ²) )`.

The proof converts the two `IntegrableOn` square hypotheses into `MemLp … 2` statements via
`memLp_two_iff_integrable_sq`, applies the abstract Cauchy–Schwarz inequality in `L²`
(`Work.Spaces.cs_integral`) to the absolute values, and takes square roots with
`Real.le_sqrt_of_sq_le`.  Note `open scoped Real` above is what makes the bare `π` in the
statement below denote `Real.pi` (matching `Work.Spaces.Iθ`); the statement itself is
otherwise unchanged. -/
theorem sliceCS {Φ Φ' : ℝ → ℝ → ℝ} {s : ℝ} (hs : 0 < s)
    (hcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hcont' : ContinuousOn (Function.uncurry Φ') (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hFin : MeasureTheory.IntegrableOn (fun θ : ℝ => Φ s θ ^ 2) Work.Spaces.Iθ)
    (hGin : MeasureTheory.IntegrableOn (fun θ : ℝ => Φ' s θ ^ 2) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, |Φ s θ * Φ' s θ|)
      ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, Φ s θ ^ 2) * (∫ θ in Work.Spaces.Iθ, Φ' s θ ^ 2)) := by
  -- the two slices are a.e. strongly measurable on `Iθ`
  have hΦm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Φ s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry Φ) hcont hs
  have hΨm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Φ' s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry Φ') hcont' hs
  -- hence the slices are in `L²(Iθ)`
  have hΦ : MeasureTheory.MemLp (fun θ : ℝ => Φ s θ) 2
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hΦm).2 hFin
  have hΨ : MeasureTheory.MemLp (fun θ : ℝ => Φ' s θ) 2
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hΨm).2 hGin
  -- Cauchy–Schwarz for the absolute values
  have hcs := Work.Spaces.cs_integral hΦ.abs hΨ.abs
  have hcs' : (∫ x in Work.Spaces.Iθ, |Φ s x| * |Φ' s x|) ^ 2
      ≤ (∫ x in Work.Spaces.Iθ, |Φ s x| ^ 2) * (∫ x in Work.Spaces.Iθ, |Φ' s x| ^ 2) := hcs
  -- `|Φ·Φ'| = |Φ|·|Φ'|` and `|Φ|² = Φ²`
  have hsq : (∫ θ in Work.Spaces.Iθ, |Φ s θ * Φ' s θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Φ s θ ^ 2) * (∫ θ in Work.Spaces.Iθ, Φ' s θ ^ 2) := by
    simpa only [abs_mul, sq_abs] using hcs'
  exact Real.le_sqrt_of_sq_le hsq

end Work.FTS.StrongPersist.SupZ
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxReg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-! ## The definition -/

/-- The closed box `[a,b] × [0,π/2]` (with `0 < a ≤ b`, so it is contained in the closed right
half-plane and bounded away from the degenerate line `z = 0`). -/
def cbox (a b : ℝ) : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc 0 (π / 2)

@[simp] theorem mem_cbox {a b z θ : ℝ} :
    (z, θ) ∈ cbox a b ↔ z ∈ Set.Icc a b ∧ θ ∈ Set.Icc 0 (π / 2) := Iff.rfl

/-- **Closed-box regularity**: on every box `[a,b] × [0,π/2]` with `0 < a ≤ b` the function is
jointly `C²`.  This is the finite-order substitute for the tree's closed-quadrant smoothness
(`Work.Spaces.SmoothNbhd` / `SmoothStrip`); see the module docstring for why the uniqueness
obligation cannot be proved without it. -/
def BoxReg (Ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → ContDiffOn ℝ 2 (Function.uncurry Ψ) (cbox a b)

/-! ## The API -/

/-- **The slice at a fixed `z > 0` is `C²` on the closed interval `[0,π/2]`** — the hypothesis
consumed by `Work.FTS.EllipticEst.Lzero_self_form`, `Work.Elliptic.Lzero_orthogonal` and
`Work.FTS.EllipticEst.angQ_ge`. -/
theorem BoxReg.slice {Ψ : ℝ → ℝ → ℝ} (h : BoxReg Ψ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Icc 0 (π / 2)) := by
  have hbox := h z (z + 1) hz (by linarith)
  have hcont : ContDiffOn ℝ 2 (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) (Set.Icc 0 (π / 2)) := by
    fun_prop
  refine hbox.comp hcont ?_
  intro θ hθ
  exact ⟨⟨le_rfl, by linarith⟩, hθ⟩

/-- **`BoxReg` of the pointwise difference** (the difference of two jet-limits, the object of the
uniqueness obligation). -/
theorem BoxReg.sub {Ψ Φ : ℝ → ℝ → ℝ} (hΨ : BoxReg Ψ) (hΦ : BoxReg Φ) :
    BoxReg (fun z θ => Ψ z θ - Φ z θ) := by
  intro a b ha hab
  have h1 : Function.uncurry (fun z θ : ℝ => Ψ z θ - Φ z θ)
      = (Function.uncurry Ψ) - (Function.uncurry Φ) := by
    funext p
    simp [Function.uncurry]
  rw [h1]
  exact (hΨ a b ha hab).sub (hΦ a b ha hab)

/-- **`BoxReg` is joint `C²` at every interior point of the quadrant** (the local form used by
every differentiation under the `θ`-integral below). -/
theorem BoxReg.contDiffAt {Ψ : ℝ → ℝ → ℝ} (h : BoxReg Ψ) {p : ℝ × ℝ}
    (hp : p.1 ∈ Set.Ioi (0 : ℝ) ∧ p.2 ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ContDiffAt ℝ 2 (Function.uncurry Ψ) p := by
  set a : ℝ := p.1 / 2 with ha
  set b : ℝ := 2 * p.1 with hb
  have hp1 : 0 < p.1 := hp.1
  have ha0 : 0 < a := by rw [ha]; linarith
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have hbox := h a b ha0 hab
  have hmem : p ∈ Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
    refine ⟨⟨?_, ?_⟩, hp.2⟩
    · rw [ha]; linarith
    · rw [hb]; linarith
  have hopen : IsOpen (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := isOpen_Ioo.prod isOpen_Ioo
  refine hbox.contDiffAt (Filter.mem_of_superset (hopen.mem_nhds hmem) ?_)
  intro q hq
  exact ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩⟩

/-- **`BoxReg` implies joint `C²` on the open quadrant**. -/
theorem BoxReg.contDiffOn_Qd {Ψ : ℝ → ℝ → ℝ} (h : BoxReg Ψ) :
    ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd :=
  fun p hp => (h.contDiffAt ⟨hp.1, hp.2⟩).contDiffWithinAt

end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB2.BrMirFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB2

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-!
# `Work.FTS_StreamBdry.SB2.BrMirFacts`

The reflection `θ ↦ π - θ` acting on the angular variable of the self-similar strip:
if `P` is `C²` on the open quadrant `Qd = (0,∞) × (0,π/2)`, then the *mirrored*
function `Q(w,θ) = -P(w, π-θ)` is `C²` on the reflected strip
`(0,∞) × (π/2, π)`, and the plain partial derivatives `∂_z`, `∂_θ` — and all the
second-order combinations of them — transform by the expected signs:

* `∂_z` and `∂_z²` pick up a sign `-1` (the reflection swaps the orientation of the
  `z`-axis relative to the sign of the function);
* `∂_θ` picks up a sign `+1`, and `∂_θ(∂_z)`, `∂_z(∂_θ)` pick up `+1` as well, while
  `∂_θ²` picks up `-1` (each `θ`-derivative contributes `-1` from the chain rule,
  cancelling against the `-1` of the mirrored function).

The pointwise identities are the content of the second conjunct; the first is the
`C²`-statement on the mirrored strip.  Everything is proved from `hP` and the
elementary chain rule for the reflection; the second derivatives use that
`uncurry (∂_zP)` and `uncurry (∂_θP)` are `C¹` on `Qd` (a fact about the curried
partials of a `C²` function, `Work.Spaces.uncurry_partial_c1`).
-/

/-! ## §0 The elementary calculus of the reflection `t ↦ c - t` -/

/-- Chain rule for the reflection `t ↦ c - t`: for `F` differentiable at `c - x`,
the derivative of `F (c - ·)` at `x` is minus the derivative of `F` at `c - x`. -/
private lemma deriv_comp_reflect {F : ℝ → ℝ} {c x : ℝ}
    (hF : DifferentiableAt ℝ F (c - x)) :
    deriv (fun t => F (c - t)) x = - deriv F (c - x) := by
  have hlin : HasDerivAt (fun t : ℝ => c - t) (-1) x := (hasDerivAt_id x).const_sub c
  have h := (hF.hasDerivAt.comp x hlin).deriv
  rw [mul_neg_one] at h
  exact h

/-- `∂_z` of a mirrored function: the sign is `-1`, and no differentiability is
needed (both sides are totalised by `deriv`). -/
private lemma pz_neg_reflect (F : ℝ → ℝ → ℝ) (w θ : ℝ) :
    Work.Spaces.pz (fun w θ => -F w (π - θ)) w θ = -Work.Spaces.pz F w (π - θ) := by
  show deriv (fun x => -F x (π - θ)) w = -deriv (fun x => F x (π - θ)) w
  exact deriv.neg

/-- `∂_θ` of a mirrored function: the sign is `+1`, the two `-1`'s (one from the
negation of the function, one from the chain rule) cancelling. -/
private lemma pth_neg_reflect {F : ℝ → ℝ → ℝ} {w θ : ℝ}
    (hF : DifferentiableAt ℝ (fun s => F w s) (π - θ)) :
    Work.Spaces.pth (fun w θ => -F w (π - θ)) w θ = Work.Spaces.pth F w (π - θ) := by
  show deriv (fun t => -F w (π - t)) θ = deriv (fun s => F w s) (π - θ)
  rw [show (fun t => -F w (π - t)) = - (fun t => F w (π - t)) from rfl]
  rw [deriv.neg]
  rw [deriv_comp_reflect hF]
  ring

/-- The `z`-partials of a mirrored function, as a global function identity. -/
private lemma pz_neg_reflect_fun (F : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun w θ => -F w (π - θ))
      = fun a b => -Work.Spaces.pz F a (π - b) := by
  funext a b
  exact pz_neg_reflect F a b

/-! ## §1 The main statement -/

theorem BrMirFacts {P : ℝ → ℝ → ℝ}
    (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ 2 (Function.uncurry (fun w θ => -P w (Real.pi - θ)))
        (Set.Ioi 0 ×ˢ Set.Ioo (Real.pi / 2) Real.pi) ∧
    (∀ w θ, 0 < w → Real.pi / 2 < θ → θ < Real.pi →
      Work.Spaces.pz (fun w θ => -P w (Real.pi - θ)) w θ
          = -Work.Spaces.pz P w (Real.pi - θ) ∧
      Work.Spaces.pth (fun w θ => -P w (Real.pi - θ)) w θ
          = Work.Spaces.pth P w (Real.pi - θ) ∧
      Work.Spaces.pz (Work.Spaces.pz (fun w θ => -P w (Real.pi - θ))) w θ
        = -Work.Spaces.pz (Work.Spaces.pz P) w (Real.pi - θ) ∧
      Work.Spaces.pth (Work.Spaces.pz (fun w θ => -P w (Real.pi - θ))) w θ
        = Work.Spaces.pth (Work.Spaces.pz P) w (Real.pi - θ) ∧
      Work.Spaces.pz (Work.Spaces.pth (fun w θ => -P w (Real.pi - θ))) w θ
        = Work.Spaces.pz (Work.Spaces.pth P) w (Real.pi - θ) ∧
      Work.Spaces.pth (Work.Spaces.pth (fun w θ => -P w (Real.pi - θ))) w θ
        = -Work.Spaces.pth (Work.Spaces.pth P) w (Real.pi - θ)) := by
  have hQdopen : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  -- differentiability of `P` on the open quadrant, as a function of two variables
  have hPd : ∀ p ∈ Work.Construction.Qd, DifferentiableAt ℝ (Function.uncurry P) p :=
    fun p hp => (hP.differentiableOn (by norm_num)).differentiableAt (hQdopen.mem_nhds hp)
  -- the curried partials of `P` are `C¹` on the open quadrant
  have hpart := Work.Spaces.uncurry_partial_c1 hQdopen hP
  refine ⟨?_, ?_⟩
  · -- the mirrored function is `C²` on the reflected strip
    have hR : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (p.1, Real.pi - p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo (Real.pi / 2) Real.pi) :=
      contDiff_fst.contDiffOn.prodMk
        (contDiffOn_const.sub contDiff_snd.contDiffOn)
    have hmap : Set.MapsTo (fun p : ℝ × ℝ => (p.1, Real.pi - p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo (Real.pi / 2) Real.pi) Work.Construction.Qd := by
      rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb⟩ := hab
      rw [Set.mem_Ioi] at ha
      rw [Set.mem_Ioo] at hb
      show (a, Real.pi - b) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
      rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨ha, ⟨by linarith [hb.2, Real.pi_pos], by linarith [hb.1, Real.pi_pos]⟩⟩
    refine ((hP.neg).comp hR hmap).congr ?_
    rintro ⟨a, b⟩ _
    rfl
  · -- the six derivative identities
    intro w θ hw hθ1 hθ2
    have hmem : (w, Real.pi - θ) ∈ Work.Construction.Qd := by
      show (w, Real.pi - θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
      rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨hw, ⟨by linarith [hθ2, Real.pi_pos], by linarith [hθ1, Real.pi_pos]⟩⟩
    -- differentiability of the three slices of `P` at the reflected angle
    have hPslice : DifferentiableAt ℝ (fun s => P w s) (Real.pi - θ) :=
      Work.Spaces.differentiableAt_curry_right (hPd (w, Real.pi - θ) hmem)
    have hpzslice : DifferentiableAt ℝ (fun s => Work.Spaces.pz P w s) (Real.pi - θ) :=
      Work.Spaces.differentiableAt_curry_right
        ((hpart.1.differentiableOn (by norm_num)).differentiableAt (hQdopen.mem_nhds hmem))
    have hpthslice : DifferentiableAt ℝ (fun s => Work.Spaces.pth P w s) (Real.pi - θ) :=
      Work.Spaces.differentiableAt_curry_right
        ((hpart.2.differentiableOn (by norm_num)).differentiableAt (hQdopen.mem_nhds hmem))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- `∂_z`
      exact pz_neg_reflect P w θ
    · -- `∂_θ`
      exact pth_neg_reflect (F := P) (w := w) (θ := θ) hPslice
    · -- `∂_z²`
      rw [pz_neg_reflect_fun P]
      exact pz_neg_reflect (Work.Spaces.pz P) w θ
    · -- `∂_θ∂_z`
      rw [pz_neg_reflect_fun P]
      exact pth_neg_reflect (F := Work.Spaces.pz P) (w := w) (θ := θ) hpzslice
    · -- `∂_z∂_θ`
      show deriv (fun a => Work.Spaces.pth (fun w θ => -P w (Real.pi - θ)) a θ) w
          = deriv (fun a => Work.Spaces.pth P a (Real.pi - θ)) w
      refine Filter.EventuallyEq.deriv_eq ?_
      have hset : {a : ℝ | (a, Real.pi - θ) ∈ Work.Construction.Qd} ∈ 𝓝 w :=
        (hQdopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hmem
      filter_upwards [hset] with a ha
      exact pth_neg_reflect (F := P) (w := a) (θ := θ)
        (Work.Spaces.differentiableAt_curry_right (hPd (a, Real.pi - θ) ha))
    · -- `∂_θ²`
      show deriv (fun t => Work.Spaces.pth (fun w θ => -P w (Real.pi - θ)) w t) θ
          = -deriv (fun s => Work.Spaces.pth P w s) (Real.pi - θ)
      have hev : (fun t => Work.Spaces.pth (fun w θ => -P w (Real.pi - θ)) w t)
          =ᶠ[𝓝 θ] (fun t => Work.Spaces.pth P w (Real.pi - t)) := by
        have hset : {t : ℝ | (w, Real.pi - t) ∈ Work.Construction.Qd} ∈ 𝓝 θ :=
          (hQdopen.preimage
            (continuous_const.prodMk (continuous_const.sub continuous_id))).mem_nhds hmem
        filter_upwards [hset] with t ht
        exact pth_neg_reflect (F := P) (w := w) (θ := t)
          (Work.Spaces.differentiableAt_curry_right (hPd (w, Real.pi - t) ht))
      rw [hev.deriv_eq]
      exact deriv_comp_reflect (F := fun s => Work.Spaces.pth P w s) (c := Real.pi)
        (x := θ) hpthslice

end Work.FTS_StreamBdry.SB2
end
-- ===== merged: Submission.Work.Spaces.HPwH2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Elgindi, §H2: `H²` functions are pointwise bounded by `100/(γ-1)·|·|²_{H²}`.**
For `h` a smooth function on a neighbourhood of the closed quadrant, vanishing on the two
angular boundaries, decaying to `0` in `z` along each angle, and of class `H²`, every
pointwise value on the domain satisfies
`(h z θ)² ≤ (100/(γ-1)) · HkSq α 2 h`.

This is the pointwise form of the paper's Corollary *Linfty*: it combines the radial
Hardy inequality `HardyZ` with the angular Hardy inequality applied to `D_z h`
(`Dz_HardyTheta_HkIntegrand`), after which the surviving angular integral is a single
term of the `H²`-integrand. -/
theorem HPwH2 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd h) (hvt : Work.Spaces.VanishTheta h)
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => h z θ) Filter.atTop (nhds 0))
    (hmem : Work.Spaces.HkMem α 2 h) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (h z θ) ^ 2 ≤ 100 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 2 h := by
  have hgam1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hcoef : 0 ≤ 100 / (gam α - 1) := div_nonneg (by norm_num) hgam1.le
  have hPhi_int : IntegrableOn (fun z => ∫ σ in Iθ, HkIntegrand α 2 h z σ) Iz := hmem.2
  have hbnd : IntegrableOn
      (fun z => (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 h z σ) Iz :=
    hPhi_int.const_mul _
  intro z hz θ hθ
  have hAES : AEStronglyMeasurable
      (fun z' => (Dz h z' θ) ^ 2 * (w z') ^ 2) (volume.restrict Iz) := by
    have h1 : Measurable (fun z' => pz h z' θ) := by
      simpa [pz] using measurable_deriv (fun z'' => h z'' θ)
    have hD : Measurable (fun z' => Dz h z' θ) := measurable_id.mul h1
    have h2 : Measurable (fun z' => (Dz h z' θ) ^ 2) := by
      have : Measurable (fun z' => Dz h z' θ * Dz h z' θ) := hD.mul hD
      simpa [pow_two] using this
    have hw : Measurable w := by
      show Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
      have hnum : Measurable (fun z : ℝ => (1 + z) ^ 2) := by
        have hm : Measurable (fun z : ℝ => (1 + z) * (1 + z)) :=
          (measurable_const.add measurable_id).mul (measurable_const.add measurable_id)
        simpa [pow_two] using hm
      have hden : Measurable (fun z : ℝ => z ^ 2) := by
        have hm : Measurable (fun z : ℝ => z * z) := measurable_id.mul measurable_id
        simpa [pow_two] using hm
      exact hnum.div hden
    have hw2 : Measurable (fun z' => (w z') ^ 2) := by
      have : Measurable (fun z' => w z' * w z') := hw.mul hw
      simpa [pow_two] using this
    exact (h2.mul hw2).aestronglyMeasurable
  have hFint : IntegrableOn (fun z' => (Dz h z' θ) ^ 2 * (w z') ^ 2) Iz := by
    refine MeasureTheory.Integrable.mono' hbnd hAES ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z' hz' => by
      have hstep := Dz_HardyTheta_HkIntegrand α hα hα1 h hsm hvt hmem z' hz' θ hθ
      have hFnn : 0 ≤ (Dz h z' θ) ^ 2 * (w z') ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
      exact hstep)
  have hHZ : (h z θ) ^ 2 ≤ ∫ z' in Iz, (Dz h z' θ) ^ 2 * (w z') ^ 2 :=
    HardyZ h θ hsm hθ (hdec θ hθ) hFint z hz
  have hIntLe : ∫ z' in Iz, (Dz h z' θ) ^ 2 * (w z') ^ 2
      ≤ (100 / (gam α - 1)) * HkSq α 2 h := by
    calc ∫ z' in Iz, (Dz h z' θ) ^ 2 * (w z') ^ 2
        ≤ ∫ z' in Iz, (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 h z' σ :=
          MeasureTheory.setIntegral_mono_of_nonneg
            (fun z' _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (fun z' hz' => Dz_HardyTheta_HkIntegrand α hα hα1 h hsm hvt hmem z' hz' θ hθ)
            hbnd
      _ = (100 / (gam α - 1)) * ∫ z' in Iz, ∫ σ in Iθ, HkIntegrand α 2 h z' σ := by
          rw [MeasureTheory.integral_const_mul]
      _ = (100 / (gam α - 1)) * HkSq α 2 h := rfl
  exact le_trans hHZ hIntLe

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.Linf_H2_of_decay =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000


end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.bt_g_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

open MeasureTheory Set Filter
open scoped Real Topology


end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.bt_integral_weight_id =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces


end Work.Spaces
end
