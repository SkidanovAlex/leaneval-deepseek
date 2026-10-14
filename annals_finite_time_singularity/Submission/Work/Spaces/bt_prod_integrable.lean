import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.l_self_w_sq_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity


end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.slice_ibp =====
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

/-- The point of the closed quadrant `(z,θ)` with `z > 0` and `θ ∈ (0,π/2)` lies in the open
box on which `SmoothNbhd` requires smoothness; hence `v` is differentiable there, and so is the
angular slice `θ' ↦ v z θ'`. -/
theorem smoothNbhd_slice_differentiableAt (v : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd v)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' => v z θ') θ := by
  have hmem : (z, θ) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) := by
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_Ioi]; linarith [hz]
    · simp only [Set.mem_Ioo]; exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hopen : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hdiff : DifferentiableAt ℝ (Function.uncurry v) (z, θ) :=
    (hsm.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by norm_num)
  exact Work.Spaces.differentiableAt_curry_right hdiff

/-- The derivative of the angular boundary term
`ψ θ = sin(2θ)^{-(γ-1)} · v(z,θ)²` (`γ = gam α`) at an interior point of `(0,π/2)`, where
`sin(2θ) > 0` so that the power is genuinely differentiable.  The derivative is written in the
form `2·(sin(2θ)^{-γ} D_θ v · v) - 2(γ-1)·(cos(2θ) sin(2θ)^{-γ} v²)` adapted to the two
integrands of `slice_ibp`. -/
theorem slice_psi_hasDerivAt (α : ℝ) (v : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd v)
    (z θ : ℝ) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hsin : 0 < Real.sin (2 * θ)) :
    HasDerivAt (fun θ' => (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α - 1)) * (v z θ') ^ 2)
      (2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Work.Spaces.Dth v z θ * v z θ)
        - (2 * (Work.Spaces.gam α - 1)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (v z θ) ^ 2)) θ := by
  have hdiff : DifferentiableAt ℝ (fun θ' => v z θ') θ :=
    smoothNbhd_slice_differentiableAt v hsm hz hθ
  have hu : HasDerivAt (fun θ' => v z θ') (Work.Spaces.pth v z θ) θ := hdiff.hasDerivAt
  have hs2 : HasDerivAt (fun θ' => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    convert h using 1
    · ext θ'; simp [Function.comp]
    · ring
  have hsinne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsin
  have hφ : HasDerivAt (fun θ' => (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α - 1)))
      ((-(Work.Spaces.gam α - 1)) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1) - 1)
        * (2 * Real.cos (2 * θ))) θ := by
    have h := (Real.hasDerivAt_rpow_const (x := Real.sin (2 * θ))
      (p := -(Work.Spaces.gam α - 1)) (Or.inl hsinne)).comp θ hs2
    convert h using 1
    · ext θ'; simp [Function.comp]
  have hu2 : HasDerivAt (fun θ' => (v z θ') ^ 2) (2 * (v z θ) * Work.Spaces.pth v z θ) θ := by
    have h := (hasDerivAt_pow 2 (v z θ)).comp θ hu
    convert h using 1
    · ext θ'; simp [Function.comp]
    · simp only [Nat.reduceSub, pow_one]; ring
  have hψ := hφ.mul hu2
  have key : ( (-(Work.Spaces.gam α - 1)) * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α - 1) - 1)
          * (2 * Real.cos (2 * θ)) * (v z θ) ^ 2
        + Real.sin (2 * θ) ^ (-(Work.Spaces.gam α - 1)) * (2 * (v z θ) * Work.Spaces.pth v z θ) )
      = 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Work.Spaces.Dth v z θ * v z θ)
        - (2 * (Work.Spaces.gam α - 1)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (v z θ) ^ 2) := by
    have hA : Real.sin (2 * θ) ^ (-(Work.Spaces.gam α - 1))
        = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) * Real.sin (2 * θ) := by
      rw [show -(Work.Spaces.gam α - 1) = -(Work.Spaces.gam α) + 1 by ring,
        Real.rpow_add hsin, Real.rpow_one]
    have hB : Real.sin (2 * θ) ^ (-(Work.Spaces.gam α - 1) - 1)
        = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      rw [show -(Work.Spaces.gam α - 1) - 1 = -(Work.Spaces.gam α) by ring]
    rw [hA, hB, Work.Spaces.Dth]
    ring
  rw [key] at hψ
  exact hψ


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.wip_K_part_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.Coercivity

/-- The `K`-part of the `L₁₂` integration by parts, in the product-measure form used by
the `L²` coercivity chain: with `K(θ) = 3 sin θ cos²θ` and `L₁₂(f)(z) = ∫_z^∞ ∫_θ K f/s`,

`∫∫ 2 K(θ) f(z,θ) (w(z)/z · L₁₂(f)(z)) = -2 ∫_0^∞ (1+z)/z³ · L₁₂(f)(z)² dz`.

This is `L12_z_byparts` with the `θ`-integral performed first (Fubini) and the factor `2`
pulled out; the angular integral `∫_θ K(θ)f(z,θ)dθ = z · L₁₂-density(z)` is exactly the
density produced by differentiating `L₁₂(f)`. -/
theorem wip_K_part_eq (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => 2 * Spaces.K θ * f z θ * (Spaces.w z / z * L12f f z)))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    (∫ p : ℝ × ℝ, 2 * Spaces.K p.2 * f p.1 p.2 * (Spaces.w p.1 / p.1 * L12f f p.1)
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)))
      = -2 * ∫ z in Set.Ioi (0 : ℝ), (1 + z) / z ^ 3 * (L12f f z) ^ 2 := by
  -- The product of the two restricted measures is the restriction of the product measure
  -- to the quadrant; this is what lets Fubini consume `hint` directly.
  have hvol : MeasureTheory.volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)
      = (MeasureTheory.volume.restrict Spaces.Iz).prod
          (MeasureTheory.volume.restrict Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  set G : ℝ → ℝ → ℝ :=
    fun z θ => 2 * Spaces.K θ * f z θ * (Spaces.w z / z * L12f f z) with hGdef
  have hInt : Integrable (Function.uncurry G)
      ((MeasureTheory.volume.restrict Spaces.Iz).prod
        (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    rw [← hvol]
    exact hint
  change (∫ p : ℝ × ℝ, Function.uncurry G p
      ∂((MeasureTheory.volume.restrict Spaces.Iz).prod
        (MeasureTheory.volume.restrict Spaces.Iθ)))
    = -2 * ∫ z in Set.Ioi (0 : ℝ), (1 + z) / z ^ 3 * (L12f f z) ^ 2
  -- Step 1: Fubini
  have step1 : (∫ p : ℝ × ℝ, Function.uncurry G p
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod
          (MeasureTheory.volume.restrict Spaces.Iθ)))
      = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, G z θ := by
    rw [MeasureTheory.integral_prod (Function.uncurry G) hInt]
    simp only [Function.uncurry]
  -- Step 2: the `θ`-integral factors out the coefficient that is constant in `θ`
  have step2 : (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, G z θ)
      = ∫ z in Spaces.Iz,
          2 * (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) := by
    refine MeasureTheory.setIntegral_congr_fun ?_ ?_
    · rw [Spaces.Iz]; exact measurableSet_Ici
    · intro z _
      show (∫ θ in Spaces.Iθ, G z θ)
        = 2 * (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ)
      have hfun : G z
          = fun θ => (2 * (Spaces.w z / z * L12f f z)) * (Spaces.K θ * f z θ) := by
        funext θ
        simp only [hGdef]
        ring
      rw [hfun, MeasureTheory.integral_const_mul]
  -- Step 3: `Iz = [0,∞)` and `(0,∞)` differ by the null set `{0}`
  have hae : Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) := by
    rw [Spaces.Iz, MeasureTheory.ae_eq_set]
    constructor
    · have hset : Set.Ici (0 : ℝ) \ Set.Ioi (0 : ℝ) = {0} := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_Ioi, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩; linarith
        · rintro rfl; exact ⟨le_refl 0, lt_irrefl 0⟩
      rw [hset]; exact measure_singleton 0
    · have hset : Set.Ioi (0 : ℝ) \ Set.Ici (0 : ℝ) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨h1, h2⟩
        exact h2 (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp h1)))
      rw [hset]; simp
  have step3 : (∫ z in Spaces.Iz,
        2 * (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
      = ∫ z in Set.Ioi (0 : ℝ),
          2 * (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) :=
    MeasureTheory.setIntegral_congr_set hae
  -- Step 4: pull the factor `2` out of the integral
  have step4 : (∫ z in Set.Ioi (0 : ℝ),
        2 * (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
      = 2 * ∫ z in Set.Ioi (0 : ℝ),
          (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) := by
    rw [show (fun z => 2 * (Spaces.w z / z * L12f f z)
          * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
        = fun z => 2 * ((Spaces.w z / z * L12f f z)
          * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ)) from by funext z; ring]
    rw [MeasureTheory.integral_const_mul]
  -- Step 5: the radial integration by parts, from the same joint integrability
  have hint' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ)))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    have hmain : Integrable
        (Function.uncurry (fun z θ => 2 * Spaces.K θ * f z θ * (Spaces.w z / z * L12f f z)))
        (MeasureTheory.volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)) := hint
    refine (hmain.const_mul ((1 : ℝ) / 2)).congr ?_
    filter_upwards with p
    simp only [Function.uncurry]
    ring
  have hkey : (∫ z in Set.Ioi (0 : ℝ),
        (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
      = - ∫ z in Set.Ioi (0 : ℝ), (1 + z) / z ^ 3 * (L12f f z) ^ 2 :=
    L12_z_byparts f hfH hint'
  rw [step1, step2, step3, step4, hkey]
  ring

end Work.Coercivity
end
-- ===== merged: Submission.Work.Cyl.fderiv_R_theta_eZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The axial derivative of `x ↦ F(ρ(x)^α, θ(x))`: the `e₃` direction

For a two-variable function `F`, a real exponent `α` and a point `x` off the symmetry axis
(`0 < radial x`),

`fderiv ℝ (fun y ↦ F (rho y ^ α) (theta y)) x eZ
   = (sin θ / ρ) · (α ρ^α ∂_R F(ρ^α,θ)) + (cos θ / ρ) · ∂_θ F(ρ^α,θ)`,

with `(ρ, θ) = (rho x, theta x)`.

Geometrically: along the vertical line `x + t e₃` the point `(ρ, θ)` moves as
`(ρ(x₃), θ(x₃))` with `∂_{x₃}ρ = x₃/ρ = sin θ` and `∂_{x₃}θ = radial/ρ² = cos θ/ρ`, and
`e₃` is the coordinate direction `∂_{x₃}`.  The `(r, x₃)`-plane computation is
`Work.Cyl.pdZ_comp_polar`; the present lemma transports it to `ℝ³` along the line
`x + t e₃`, on which `radial` is constant and `axial` increases at unit speed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-! ## The dictionary between `(rho, theta)` on `ℝ³` and `(rhoP, thetaP)` on the half plane -/

private lemma rho_eq_rhoP (y : R3) : rho y = rhoP (radial y) (axial y) := by
  rw [rho, rhoP, radial_sq]

private lemma theta_eq_thetaP (y : R3) : theta y = thetaP (radial y) (axial y) := rfl



private lemma rhoP_radial_axial (x : R3) : rhoP (radial x) (axial x) = rho x :=
  (rho_eq_rhoP x).symm

private lemma thetaP_radial_axial (x : R3) : thetaP (radial x) (axial x) = theta x := rfl

/-! ## Differentiability of `ρ` and `θ` off the axis -/




/-! ## The chain rule along a vertical line in the `(r, x₃)` half plane -/

private lemma deriv_rhoP_thetaP_shift (F : ℝ → ℝ → ℝ) (α r z : ℝ) (hr : 0 < r)
    (hF : DiffAt2 F (rhoP r z ^ α) (thetaP r z)) :
    deriv (fun t : ℝ => F (rhoP r (z + t) ^ α) (thetaP r (z + t))) 0 =
      Real.sin (thetaP r z) / rhoP r z *
          (α * rhoP r z ^ α * pdR F (rhoP r z ^ α) (thetaP r z))
        + Real.cos (thetaP r z) / rhoP r z * pdZ F (rhoP r z ^ α) (thetaP r z) := by
  rw [deriv_comp_const_add (fun u : ℝ => F (rhoP r u ^ α) (thetaP r u)) z 0, add_zero]
  rw [show deriv (fun u : ℝ => F (rhoP r u ^ α) (thetaP r u)) z
      = pdZ (fun r' z' => F (rhoP r' z' ^ α) (thetaP r' z')) r z from rfl]
  exact pdZ_comp_polar F α r z hr hF


end Work.Cyl
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4AMGM =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-!
# The pointwise AM–GM of the honest `I₄` slice estimate

With `s = sin θ`, `c = cos θ`, `σ = sin(2θ)^{-99/100}` and
`Σ = (1-η) cos²θ + (3+η) sin²θ` (`η = 99/100`), the target inequality

`|s σ q Ψv| ≤ ½ Σ σ q² + 50 σ (Ψv / c)²`

is, after dividing by `σ > 0`, the statement that the quadratic form
`½ Σ q² - s q Ψv + 50 (Ψv/c)²` in `(q, Ψv)` is positive semidefinite, i.e. that

`s² ≤ 4 · (Σ/2) · (50/c²)`,  equivalently  `s² c² ≤ 100 Σ`,

which holds because `Σ ≥ 3 s²` and `c² ≤ 1`.

The elementary quadratic-AM–GM fact is proved first (`quad_amgm`); the target then follows by
multiplying by `σ > 0` and rewriting `(Ψv/c)² = Ψv²/c²`.
-/

/-- **Positive-semidefinite quadratic AM–GM.** If `A, C > 0` and `s ^ 2 ≤ 4*A*C`, then
`|s * x * y| ≤ A * x ^ 2 + C * y ^ 2` for all reals `x`, `y`.

Proof: multiply the completing-square identity
`4A (A x² - s x y + C y²) = (2 A x - s y)² + (4 A C - s²) y²` by `1/(4A) > 0`, and apply it
again with `x` replaced by `-x`. -/
theorem quad_amgm (A C s x y : ℝ) (hA : 0 < A) (hC : 0 < C) (hs : s ^ 2 ≤ 4 * A * C) :
    |s * x * y| ≤ A * x ^ 2 + C * y ^ 2 := by
  have key : ∀ u v : ℝ, s * u * v ≤ A * u ^ 2 + C * v ^ 2 := by
    intro u v
    have h4 : (0 : ℝ) < 4 * A := by linarith
    have hid : 4 * A * (A * u ^ 2 + C * v ^ 2 - s * u * v)
        = (2 * A * u - s * v) ^ 2 + (4 * A * C - s ^ 2) * v ^ 2 := by ring
    have hsq : 0 ≤ (2 * A * u - s * v) ^ 2 + (4 * A * C - s ^ 2) * v ^ 2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
    have h0 : 0 ≤ 4 * A * (A * u ^ 2 + C * v ^ 2 - s * u * v) := by rw [hid]; exact hsq
    have h1 : 0 ≤ A * u ^ 2 + C * v ^ 2 - s * u * v := (mul_nonneg_iff_of_pos_left h4).mp h0
    linarith
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h := key (-x) y
    nlinarith [h]
  · exact key x y

/-- The pointwise `I₄` AM–GM estimate. -/
theorem I4AMGM (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (q Ψv : ℝ) :
    |Real.sin θ * I4sig θ * q * Ψv|
      ≤ (1 / 2) * I4Sig θ * I4sig θ * q ^ 2
        + 50 * I4sig θ * (Ψv / Real.cos θ) ^ 2 := by
  have hσ : 0 < I4sig θ := I4sig_pos hθ
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsin : 0 ≤ Real.sin θ :=
    le_of_lt (Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
  -- `Sig ≥ 3 s²`
  have hSig : 3 * Real.sin θ ^ 2 ≤ I4Sig θ := by
    have hs := Real.sin_sq_add_cos_sq θ
    rw [I4Sig]
    nlinarith [sq_nonneg (Real.cos θ), sq_nonneg (Real.sin θ)]
  have hc2 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hApos : 0 < I4Sig θ / 2 := div_pos (I4Sig_pos θ) (by norm_num)
  have hCpos : 0 < 50 / Real.cos θ ^ 2 := div_pos (by norm_num) (pow_pos hcos 2)
  -- `s² ≤ 4 · (Σ/2) · (50/c²)`, i.e. `s² c² ≤ 100 Σ`
  have hsineq : Real.sin θ ^ 2 ≤ 4 * (I4Sig θ / 2) * (50 / Real.cos θ ^ 2) := by
    have hkeq : 4 * (I4Sig θ / 2) * (50 / Real.cos θ ^ 2)
        = 100 * I4Sig θ / Real.cos θ ^ 2 := by ring
    rw [hkeq, le_div_iff₀ (pow_pos hcos 2)]
    have h1 : Real.sin θ ^ 2 * Real.cos θ ^ 2 ≤ Real.sin θ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hc2 (sq_nonneg (Real.sin θ))
      simpa using this
    have h2 : Real.sin θ ^ 2 ≤ 100 * I4Sig θ := by nlinarith [hsin, hSig]
    linarith
  have hmain := quad_amgm (I4Sig θ / 2) (50 / Real.cos θ ^ 2) (Real.sin θ) q Ψv
    hApos hCpos hsineq
  have hmain' : |Real.sin θ * q * Ψv|
      ≤ (1 / 2) * I4Sig θ * q ^ 2 + 50 * (Ψv / Real.cos θ) ^ 2 := by
    have hrw : (I4Sig θ / 2) * q ^ 2 + (50 / Real.cos θ ^ 2) * Ψv ^ 2
        = (1 / 2) * I4Sig θ * q ^ 2 + 50 * (Ψv / Real.cos θ) ^ 2 := by
      rw [div_pow]; ring
    rw [hrw] at hmain
    exact hmain
  calc |Real.sin θ * I4sig θ * q * Ψv|
      = I4sig θ * |Real.sin θ * q * Ψv| := by
        rw [show Real.sin θ * I4sig θ * q * Ψv = I4sig θ * (Real.sin θ * q * Ψv) by ring,
          abs_mul, abs_of_pos hσ]
    _ ≤ I4sig θ * ((1 / 2) * I4Sig θ * q ^ 2 + 50 * (Ψv / Real.cos θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hmain' (le_of_lt hσ)
    _ = (1 / 2) * I4Sig θ * I4sig θ * q ^ 2
          + 50 * I4sig θ * (Ψv / Real.cos θ) ^ 2 := by ring

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4CSBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted Cauchy–Schwarz bound for the `I₄` slice estimate

`I4CSBound` bounds the (interval) integral of `cos θ · ψ θ · b θ · σ θ` (with `ψ = Φ/cos`,
`b = Φ''`, `σ = sin(2θ)^{-99/100}`) by the product of the two weighted `L²` norms appearing in
the `I₄` slice estimate.

The interest of the statement is that `Φ` is only assumed `L²` with respect to the weight `σ`
in the *squared* form `ψ²σ`, `b²σ` — in particular `ψ` and `b` themselves need not be a.e.
strongly measurable, so the classical Cauchy–Schwarz cannot be applied to the pair
`(cos·ψ, b)` directly.  The trick is to absorb the square root of the weight into each factor:
with `U = √((cos·ψ)²σ)` and `V = √(b²σ)` both are a.e. strongly measurable (they are
compositions of the a.e. strongly measurable functions `(cos·ψ)²σ`, `b²σ` with `Real.sqrt`),
their squares integrate to the two right hand sides, and `U·V = |cos·ψ·b·σ|` pointwise on
`Iθ`; `csIntegralSqrt` (weighted Cauchy–Schwarz for `U`, `V`) then gives the result.  The
interval integral is compared with the set integral over `Iθ` using
`MeasureTheory.norm_integral_le_integral_norm` (which needs no integrability hypothesis) and
`MeasureTheory.setIntegral_mono_set`.
-/

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory Set Filter
open scoped Real Topology

theorem I4CSBound (Φ : ℝ → ℝ)
    (hA : MeasureTheory.IntegrableOn (fun θ => I4psi Φ θ ^ 2 * I4sig θ) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn (fun θ => I4b Φ θ ^ 2 * I4sig θ) Work.Spaces.Iθ)
    {δ θ₁ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ₁) (hθ₁ : θ₁ < Real.pi / 2) :
    (∫ θ in δ..θ₁, Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ)
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, I4b Φ θ ^ 2 * I4sig θ) := by
  -- the two square-rooted factors
  let U : ℝ → ℝ := fun θ => Real.sqrt ((Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ)
  let V : ℝ → ℝ := fun θ => Real.sqrt (I4b Φ θ ^ 2 * I4sig θ)
  have hIθmeas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- integrability of `(cos θ · ψ θ)² σ θ`, dominated by `ψ θ² σ θ`
  have hcosψ_int : MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ) Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => Real.cos θ ^ 2 * (I4psi Φ θ ^ 2 * I4sig θ)) Work.Spaces.Iθ := by
      refine hA.mono' ?_ ?_
      · exact ((Real.continuous_cos.pow 2).measurable.aemeasurable.mul hA.aemeasurable).aestronglyMeasurable
      · rw [MeasureTheory.ae_restrict_iff' hIθmeas]
        refine Filter.Eventually.of_forall fun θ hθ => ?_
        have hσ : 0 ≤ I4sig θ := I4sig_nonneg hθ
        have hψσ : 0 ≤ I4psi Φ θ ^ 2 * I4sig θ := mul_nonneg (sq_nonneg _) hσ
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ)),
          abs_of_nonneg hψσ]
        exact mul_le_of_le_one_left hψσ (Real.cos_sq_le_one θ)
    rw [show (fun θ => (Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ)
        = fun θ => Real.cos θ ^ 2 * (I4psi Φ θ ^ 2 * I4sig θ) from funext fun θ => by ring]
    exact h1
  -- measurability, integrability and integral identities for `U` and `V`
  obtain ⟨hU_ae, hU2_int, -, hU2_eq⟩ :=
    sqrtWeightFacts (s := Work.Spaces.Iθ) (p := fun θ => Real.cos θ * I4psi Φ θ)
      (σ := I4sig) hIθmeas (fun θ hθ => I4sig_nonneg hθ) hcosψ_int
  obtain ⟨hV_ae, hV2_int, -, hV2_eq⟩ :=
    sqrtWeightFacts (s := Work.Spaces.Iθ) (p := I4b Φ) (σ := I4sig)
      hIθmeas (fun θ hθ => I4sig_nonneg hθ) hB
  have hU2_eq' : (∫ θ in Work.Spaces.Iθ, U θ ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ := hU2_eq
  have hV2_eq' : (∫ θ in Work.Spaces.Iθ, V θ ^ 2)
      = ∫ θ in Work.Spaces.Iθ, I4b Φ θ ^ 2 * I4sig θ := hV2_eq
  -- weighted Cauchy–Schwarz
  have hcs : (∫ θ in Work.Spaces.Iθ, U θ * V θ)
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, U θ ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, V θ ^ 2) :=
    csIntegralSqrt (μ := volume.restrict Work.Spaces.Iθ) (F := U) (G := V)
      hU_ae hV_ae hU2_int hV2_int
  -- `U · V = |cos θ · ψ θ · b θ · σ θ|` on `Iθ`
  have huv : ∀ θ ∈ Work.Spaces.Iθ,
      U θ * V θ = |Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ| := by
    intro θ hθ
    have hσ : 0 ≤ I4sig θ := I4sig_nonneg hθ
    change Real.sqrt ((Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ)
        * Real.sqrt (I4b Φ θ ^ 2 * I4sig θ)
      = |Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ|
    rw [← Real.sqrt_mul (mul_nonneg (sq_nonneg _) hσ)]
    rw [show ((Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ) * (I4b Φ θ ^ 2 * I4sig θ)
        = (Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ) ^ 2 by ring]
    exact Real.sqrt_sq_eq_abs _
  have huv_ae : (fun θ => |Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ|)
      =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => U θ * V θ) :=
    (MeasureTheory.ae_restrict_iff' hIθmeas).mpr
      (Filter.Eventually.of_forall fun θ hθ => (huv θ hθ).symm)
  have hhabs_int : MeasureTheory.IntegrableOn
      (fun θ => |Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ|) Work.Spaces.Iθ :=
    integrableOn_abs_mul_sigma (s := Work.Spaces.Iθ)
      (p := fun θ => Real.cos θ * I4psi Φ θ) (q := I4b Φ) (σ := I4sig)
      (fun θ hθ => I4sig_nonneg hθ) hcosψ_int hB
  -- the interval `[δ, θ₁]` sits inside `Iθ`
  have hIoc_sub : Set.Ioc δ θ₁ ⊆ Work.Spaces.Iθ := fun θ hθ =>
    ⟨le_of_lt (lt_trans hδ hθ.1), le_of_lt (lt_of_le_of_lt hθ.2 hθ₁)⟩
  have hst : Set.Ioc δ θ₁ ≤ᵐ[volume] Work.Spaces.Iθ :=
    MeasureTheory.ae_le_set.mpr
      (by rw [Set.sdiff_eq_empty.mpr hIoc_sub]; exact MeasureTheory.measure_empty)
  calc (∫ θ in δ..θ₁, Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ)
      = ∫ θ in Set.Ioc δ θ₁, Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ :=
        intervalIntegral.integral_of_le hδθ
    _ ≤ ∫ θ in Set.Ioc δ θ₁, |Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ| := by
        have h := MeasureTheory.norm_integral_le_integral_norm
          (μ := volume.restrict (Set.Ioc δ θ₁))
          (fun θ => Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ)
        rw [Real.norm_eq_abs] at h
        exact le_trans (le_abs_self (∫ θ in Set.Ioc δ θ₁,
          Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ)) h
    _ ≤ ∫ θ in Work.Spaces.Iθ, |Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ| :=
        MeasureTheory.setIntegral_mono_set hhabs_int
          (Filter.Eventually.of_forall fun θ => abs_nonneg _) hst
    _ = ∫ θ in Work.Spaces.Iθ, U θ * V θ := integral_congr_ae huv_ae
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, U θ ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, V θ ^ 2) := hcs
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, I4b Φ θ ^ 2 * I4sig θ) := by
        rw [hU2_eq', hV2_eq']

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4CosSqIntegralLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory Set

/-- On `Iθ = [0, π/2]` the factor `cos²θ` is at most `1` and the weight `I4sig` is
non-negative, so the weighted integral of `(cos θ · ψ)²` is dominated by that of `ψ²`. -/
theorem I4CosSqIntegralLe (Φ : ℝ → ℝ)
    (hA : MeasureTheory.IntegrableOn (fun θ => I4psi Φ θ ^ 2 * I4sig θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ)
      ≤ ∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ := by
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ ≤ I4psi Φ θ ^ 2 * I4sig θ := by
    intro θ hθ
    have hσ : 0 ≤ I4sig θ := I4sig_nonneg hθ
    have hψ : 0 ≤ I4psi Φ θ ^ 2 := sq_nonneg _
    have hc : (Real.cos θ) ^ 2 ≤ 1 := Real.cos_sq_le_one θ
    have h1 : (Real.cos θ) ^ 2 * (I4psi Φ θ ^ 2 * I4sig θ)
        ≤ 1 * (I4psi Φ θ ^ 2 * I4sig θ) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hψ hσ)
    nlinarith [h1]
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    simpa only [Work.Spaces.Iθ] using measurableSet_Icc
  have hbdd : MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ) ^ 2 * (I4psi Φ θ ^ 2 * I4sig θ)) Work.Spaces.Iθ :=
    hA.bdd_mul (c := 1) (Real.continuous_cos.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun θ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.cos θ))]
        exact Real.cos_sq_le_one θ))
  have hf : MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ) Work.Spaces.Iθ :=
    hbdd.congr_fun (fun θ _ => by ring) hIθ
  exact MeasureTheory.setIntegral_mono_on hf hA hIθ hpt

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4GHasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `I4G Φ` is differentiable (with derivative `deriv (I4G Φ)`) on `(0, π/2)`

The boundary primitive

`I4G Φ θ = ½ · (sin θ / cos³θ) · σ θ · (cos²θ · (Φ/cos)'θ)²`

of the honest `I₄` upper bound is a finite product of functions each of which is
differentiable at every `θ ∈ (0, π/2)`, provided `Φ` is of class `C²` on that interval:

* `½` and `sin θ / cos³θ` are smooth (and `cos θ ≠ 0` on the interval),
* `σ θ = sin(2θ)^{-99/100}` is differentiable because `sin(2θ) > 0` there,
* `cos²θ` is smooth and `(Φ/cos)'` is differentiable at `θ` because `Φ/cos` is `C²` there
  (`C²` at a point ⟹ `deriv` is `C¹` at that point ⟹ differentiable).

Since differentiability at `θ` already says `HasDerivAt (I4G Φ) (deriv (I4G Φ) θ) θ`, the
claim follows.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-- `Φ/cos` is `C²` at every interior point of `(0, π/2)`. -/
private lemma contDiffAt_I4psi (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : ContDiffAt ℝ 2 (I4psi Φ) θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hcd : ContDiffAt ℝ 2 Φ θ := hsm.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  change ContDiffAt ℝ 2 (fun θ : ℝ => Φ θ / Real.cos θ) θ
  exact hcd.div (by fun_prop) hcos

/-- The derivative of `Φ/cos`, i.e. the inner factor of `P`, is differentiable at every
interior point. -/
private lemma differentiableAt_deriv_I4psi (Φ : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : DifferentiableAt ℝ (deriv (I4psi Φ)) θ := by
  have hq : ContDiffAt ℝ 2 (I4psi Φ) θ := contDiffAt_I4psi Φ hsm hθ
  have h1 : ContDiffAt ℝ 1 (deriv (I4psi Φ)) θ := hq.derivWithin (m := 1) (by norm_num)
  exact h1.differentiableAt (by norm_num)

/-- `P = cos²θ · (Φ/cos)'` is differentiable at every interior point. -/
private lemma differentiableAt_I4P (Φ : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : DifferentiableAt ℝ (I4P Φ) θ := by
  have hcos2 : DifferentiableAt ℝ (fun θ : ℝ => (Real.cos θ) ^ 2) θ := by fun_prop
  have hd : DifferentiableAt ℝ (deriv (I4psi Φ)) θ := differentiableAt_deriv_I4psi Φ hsm hθ
  change DifferentiableAt ℝ (fun θ : ℝ => (Real.cos θ) ^ 2 * deriv (I4psi Φ) θ) θ
  exact hcos2.mul hd

/-- `σ θ = sin(2θ)^{-99/100}` is differentiable at every interior point. -/
private lemma differentiableAt_I4sig {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ I4sig θ := by
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : DifferentiableAt ℝ (fun θ : ℝ => Real.sin (2 * θ)) θ := by fun_prop
  exact h1.rpow_const (Or.inl (ne_of_gt hsin2))

/-- `sin θ / cos³θ` is differentiable at every interior point. -/
private lemma differentiableAt_sin_div_cos_cube {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ : ℝ => Real.sin θ / (Real.cos θ) ^ 3) θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hsin : DifferentiableAt ℝ Real.sin θ := by fun_prop
  have hcosd : DifferentiableAt ℝ Real.cos θ := by fun_prop
  exact hsin.div (hcosd.pow 3) (pow_ne_zero 3 hcos)

/-- `I4G Φ` is differentiable at every interior point. -/
private lemma differentiableAt_I4G (Φ : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : DifferentiableAt ℝ (I4G Φ) θ := by
  change DifferentiableAt ℝ (fun θ : ℝ => (1 / 2) * (Real.sin θ / (Real.cos θ) ^ 3)
    * I4sig θ * (I4P Φ θ) ^ 2) θ
  exact DifferentiableAt.mul (DifferentiableAt.mul
    (DifferentiableAt.mul (by fun_prop) (differentiableAt_sin_div_cos_cube hθ))
    (differentiableAt_I4sig hθ)) ((differentiableAt_I4P Φ hsm hθ).pow 2)

theorem I4GHasDerivAt (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (I4G Φ) (deriv (I4G Φ) θ) θ := by
  intro θ hθ
  exact (differentiableAt_I4G Φ hsm hθ).hasDerivAt

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4IntervalIdentity =====
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

/-- The derivative of the `I₄` boundary primitive `G`, written in the form that the
algebraic identities `hAlg` of `I4IntervalIdentity` produce: the factor
`deriv (I4P Φ) θ` of the fourth identity is eliminated with the third one. -/
def I4gfun (Φ : ℝ → ℝ) : ℝ → ℝ := fun θ =>
    (Real.sin θ / (Real.cos θ)^3) * I4sig θ * ((Real.cos θ)^2 * deriv (I4psi Φ) θ)
      * (Real.cos θ * (I4b Φ θ + Φ θ))
    + (1/2) * I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2

/-- On an *open* set, a `C^n` function has continuous honest iterated derivatives up to `n`. -/
lemma continuousOn_iteratedDeriv_of_contDiffOn_isOpen {f : ℝ → ℝ} {n : WithTop ℕ∞} {m : ℕ}
    {s : Set ℝ} (hs : IsOpen s) (h : ContDiffOn ℝ n f s) (hmn : (m : WithTop ℕ∞) ≤ n) :
    ContinuousOn (iteratedDeriv m f) s :=
  (h.continuousOn_iteratedDerivWithin hmn hs.uniqueDiffOn).congr
    (fun _ hx => (iteratedDerivWithin_of_isOpen hs hx).symm)

lemma I4II_cos_pos {θ : ℝ} (h : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1, Real.pi_pos], h.2⟩

lemma I4II_sin_two_pos {θ : ℝ} (h : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2, Real.pi_pos])

lemma contDiffOn_I4psi (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 2 (I4psi Φ) (Set.Ioo 0 (Real.pi / 2)) :=
  hsm.div (Real.contDiff_cos.contDiffOn.of_le le_top)
    (fun _ hx => ne_of_gt (I4II_cos_pos hx))

lemma continuousOn_deriv_I4psi (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    {s : Set ℝ} (hs : s ⊆ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousOn (fun θ => deriv (I4psi Φ) θ) s := by
  have h := continuousOn_iteratedDeriv_of_contDiffOn_isOpen (s := Set.Ioo 0 (Real.pi / 2))
    isOpen_Ioo (contDiffOn_I4psi Φ hsm) (m := 1) (by norm_num)
  rw [iteratedDeriv_one] at h
  exact h.mono hs

/-- **Renamed** to `I4II_continuousOn_deriv_deriv`: the name `continuousOn_deriv_deriv` is
already taken by `Work.FTS.EllipticEst.Honest.SliceMain` (with a different statement), and Lean
rejects any environment containing both declarations, so an unrenamed copy here made it
impossible to import `SliceMain` and `I4IntervalIdentity` into the same module. -/
lemma I4II_continuousOn_deriv_deriv (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    {s : Set ℝ} (hs : s ⊆ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousOn (fun θ => deriv (deriv Φ) θ) s := by
  have h2 : iteratedDeriv 2 Φ = fun θ => deriv (deriv Φ) θ := by
    funext θ
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h := continuousOn_iteratedDeriv_of_contDiffOn_isOpen (s := Set.Ioo 0 (Real.pi / 2))
    isOpen_Ioo hsm (m := 2) (by norm_num)
  rw [h2] at h
  exact h.mono hs

lemma continuousOn_I4sig {δ θ₁ : ℝ} (hδ : 0 < δ) (hθ₁ : θ₁ < Real.pi / 2) :
    ContinuousOn I4sig (Set.Icc δ θ₁) := by
  have hsub : Set.Icc δ θ₁ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hδ hx.1, lt_of_le_of_lt hx.2 hθ₁⟩
  have hs : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Icc δ θ₁) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  exact ContinuousOn.rpow_const (p := -(99 / 100 : ℝ)) hs
    (fun x hx => Or.inl (ne_of_gt (I4II_sin_two_pos (hsub hx))))

theorem I4IntervalIdentity (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    (hAlg : (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => Real.tan θ' * Φ θ') θ
          = Real.cos θ * (Φ θ / Real.cos θ)
            + Real.sin θ * deriv (fun θ' => Φ θ' / Real.cos θ') θ)
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (deriv Φ) θ
          = Real.cos θ * deriv (deriv (fun θ' => Φ θ' / Real.cos θ')) θ
            - 2 * Real.sin θ * deriv (fun θ' => Φ θ' / Real.cos θ') θ
            - Real.cos θ * (Φ θ / Real.cos θ))
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => (Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ') θ
          = Real.cos θ * (deriv (deriv Φ) θ + Φ θ))
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => (1/2) * (Real.sin θ' / (Real.cos θ')^3)
            * (Real.sin (2*θ'))^(-(99/100:ℝ))
            * ((Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ')^2) θ
          = (Real.sin θ / (Real.cos θ)^3) * (Real.sin (2*θ))^(-(99/100:ℝ))
              * ((Real.cos θ)^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ)
              * deriv (fun θ' => (Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ') θ
            + (1/2) * ((1 - 99/100) * (Real.cos θ)^2 + (3 + 99/100) * (Real.sin θ)^2)
              * (Real.sin (2*θ))^(-(99/100:ℝ))
              * (deriv (fun θ' => Φ θ' / Real.cos θ') θ)^2))
    (hGder : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (I4G Φ) (deriv (I4G Φ) θ) θ)
    {δ θ₁ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ₁) (hθ₁ : θ₁ < Real.pi / 2) :
    (∫ θ in δ..θ₁, I4u Φ θ * I4b Φ θ * I4sig θ)
      = (∫ θ in δ..θ₁, Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ)
        + I4G Φ θ₁ - I4G Φ δ
        - (1 / 2) * (∫ θ in δ..θ₁, I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
        - (∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ) := by
  obtain ⟨hA1, -, hA3, hA4⟩ := hAlg
  have hIcc : Set.Icc δ θ₁ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hδ hx.1, lt_of_le_of_lt hx.2 hθ₁⟩
  have hIoo : Set.Ioo δ θ₁ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_trans hδ hx.1, lt_trans hx.2 hθ₁⟩
  have hcosne : ∀ x ∈ Set.Icc δ θ₁, Real.cos x ≠ 0 := fun x hx =>
    ne_of_gt (I4II_cos_pos (hIcc hx))
  -- the derivative of `G`, in the algebraic form supplied by `hA3` and `hA4`
  have hg_eq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv (I4G Φ) θ = I4gfun Φ θ := by
    intro θ hθ
    have h3I : deriv (I4P Φ) θ = Real.cos θ * (I4b Φ θ + Φ θ) := hA3 θ hθ
    have h4I : deriv (I4G Φ) θ
        = (Real.sin θ / (Real.cos θ)^3) * I4sig θ * ((Real.cos θ)^2 * deriv (I4psi Φ) θ)
            * deriv (I4P Φ) θ
          + (1/2) * I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2 := hA4 θ hθ
    rw [h4I, h3I]
    simp only [I4gfun, I4b]
  -- the pointwise identity is pure algebra
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      I4u Φ θ * I4b Φ θ * I4sig θ
        = Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ + I4gfun Φ θ
          - (1/2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)
          - Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ := by
    intro θ hθ
    have h1I : I4u Φ θ = Real.cos θ * I4psi Φ θ + Real.sin θ * deriv (I4psi Φ) θ := hA1 θ hθ
    have h3I : deriv (I4P Φ) θ = Real.cos θ * (I4b Φ θ + Φ θ) := hA3 θ hθ
    have h4I : deriv (I4G Φ) θ
        = (Real.sin θ / (Real.cos θ)^3) * I4sig θ * ((Real.cos θ)^2 * deriv (I4psi Φ) θ)
            * deriv (I4P Φ) θ
          + (1/2) * I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2 := hA4 θ hθ
    have hc : Real.cos θ ≠ 0 := ne_of_gt (I4II_cos_pos hθ)
    rw [h1I, ← hg_eq θ hθ, h4I, h3I]
    simp only [I4b]
    field_simp
    ring
  -- continuity of the ingredients on the closed interval
  have hcos : ContinuousOn (fun θ : ℝ => Real.cos θ) (Set.Icc δ θ₁) :=
    Real.continuous_cos.continuousOn
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin θ) (Set.Icc δ θ₁) :=
    Real.continuous_sin.continuousOn
  have hdpsi : ContinuousOn (fun θ => deriv (I4psi Φ) θ) (Set.Icc δ θ₁) :=
    continuousOn_deriv_I4psi Φ hsm hIcc
  have hb : ContinuousOn (fun θ => deriv (deriv Φ) θ) (Set.Icc δ θ₁) :=
    I4II_continuousOn_deriv_deriv Φ hsm hIcc
  have hPhi : ContinuousOn Φ (Set.Icc δ θ₁) := hsm.continuousOn.mono hIcc
  have hσ : ContinuousOn I4sig (Set.Icc δ θ₁) := continuousOn_I4sig hδ hθ₁
  have hSig : ContinuousOn I4Sig (Set.Icc δ θ₁) := by
    change ContinuousOn
      (fun θ : ℝ => (1 - 99/100) * (Real.cos θ)^2 + (3 + 99/100) * (Real.sin θ)^2)
      (Set.Icc δ θ₁)
    exact (continuousOn_const.mul (hcos.pow 2)).add (continuousOn_const.mul (hsin.pow 2))
  have hdiv : ContinuousOn (fun θ : ℝ => Real.sin θ / (Real.cos θ)^3) (Set.Icc δ θ₁) :=
    hsin.div (hcos.pow 3) (fun x hx => pow_ne_zero 3 (hcosne x hx))
  have hFAc : ContinuousOn (fun θ => Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ)
      (Set.Icc δ θ₁) :=
    ((hcos.mul ((contDiffOn_I4psi Φ hsm).continuousOn.mono hIcc)).mul hb).mul hσ
  have hFBc : ContinuousOn (fun θ => I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)
      (Set.Icc δ θ₁) :=
    (hSig.mul hσ).mul (hdpsi.pow 2)
  have hFCc : ContinuousOn (fun θ => Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
      (Set.Icc δ θ₁) :=
    ((hsin.mul hσ).mul hdpsi).mul hPhi
  have hgc : ContinuousOn (I4gfun Φ) (Set.Icc δ θ₁) := by
    have h3 : ContinuousOn (fun θ => Real.cos θ * (I4b Φ θ + Φ θ)) (Set.Icc δ θ₁) :=
      hcos.mul (hb.add hPhi)
    have h2 : ContinuousOn (fun θ => (Real.cos θ)^2 * deriv (I4psi Φ) θ) (Set.Icc δ θ₁) :=
      (hcos.pow 2).mul hdpsi
    have hmain : ContinuousOn
        (fun θ => (Real.sin θ / (Real.cos θ)^3) * I4sig θ
            * ((Real.cos θ)^2 * deriv (I4psi Φ) θ) * (Real.cos θ * (I4b Φ θ + Φ θ)))
        (Set.Icc δ θ₁) :=
      ((hdiv.mul hσ).mul h2).mul h3
    have hsec : ContinuousOn
        (fun θ => (1/2) * I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2) (Set.Icc δ θ₁) :=
      ((continuousOn_const.mul hSig).mul hσ).mul (hdpsi.pow 2)
    exact hmain.add hsec
  have hGc : ContinuousOn (I4G Φ) (Set.Icc δ θ₁) := by
    have hP : ContinuousOn (fun θ => I4P Φ θ) (Set.Icc δ θ₁) := by
      simp only [I4P]
      exact (hcos.pow 2).mul hdpsi
    exact ((continuousOn_const.mul hdiv).mul hσ).mul (hP.pow 2)
  -- integrability on `δ..θ₁` from continuity on the closed interval
  have huIcc : Set.uIcc δ θ₁ = Set.Icc δ θ₁ := Set.uIcc_of_le hδθ
  have hintB : ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc δ θ₁) → IntervalIntegrable f volume δ θ₁ :=
    fun f hf => by rw [← huIcc] at hf; exact hf.intervalIntegrable
  have hFAi : IntervalIntegrable (fun θ => Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ)
      volume δ θ₁ := hintB _ hFAc
  have hFBi : IntervalIntegrable (fun θ => I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)
      volume δ θ₁ := hintB _ hFBc
  have hFCi : IntervalIntegrable (fun θ => Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
      volume δ θ₁ := hintB _ hFCc
  have hgi : IntervalIntegrable (I4gfun Φ) volume δ θ₁ := hintB _ hgc
  have h12Bi : IntervalIntegrable
      (fun θ => (1/2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)) volume δ θ₁ :=
    hintB _ (continuousOn_const.mul hFBc)
  -- fundamental theorem of calculus for the primitive `G`
  have hGderiv : ∀ x ∈ Set.Ioo δ θ₁, HasDerivAt (I4G Φ) (I4gfun Φ x) x := by
    intro x hx
    rw [← hg_eq x (hIoo hx)]
    exact hGder x (hIoo hx)
  have hintG : ∫ θ in δ..θ₁, I4gfun Φ θ = I4G Φ θ₁ - I4G Φ δ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδθ hGc hGderiv hgi
  have hcongr : (∫ θ in δ..θ₁, I4u Φ θ * I4b Φ θ * I4sig θ)
      = ∫ θ in δ..θ₁, (Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ + I4gfun Φ θ
          - (1/2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)
          - Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hδθ] at hθ
    exact hpt θ (hIcc hθ)
  have hsplit : (∫ θ in δ..θ₁, (Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ + I4gfun Φ θ
          - (1/2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)
          - Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ))
      = (∫ θ in δ..θ₁, Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ)
        + (∫ θ in δ..θ₁, I4gfun Φ θ)
        - (1/2) * (∫ θ in δ..θ₁, I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)
        - (∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ) := by
    have h1 : IntervalIntegrable
        (fun θ => Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ + I4gfun Φ θ
          - (1/2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)) volume δ θ₁ :=
      (hFAi.add hgi).sub h12Bi
    have h2 : IntervalIntegrable
        (fun θ => Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ + I4gfun Φ θ)
        volume δ θ₁ := hFAi.add hgi
    rw [intervalIntegral.integral_sub h1 hFCi, intervalIntegral.integral_sub h2 h12Bi,
      intervalIntegral.integral_add hFAi hgi, intervalIntegral.integral_const_mul]
  rw [hcongr, hsplit, hintG]
  ring

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4SubInterval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

theorem I4SubInterval (f : ℝ → ℝ) (hA : MeasureTheory.IntegrableOn f Work.Spaces.Iθ)
    (hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ f θ)
    {δ θ₁ : ℝ} (hδ : 0 ≤ δ) (hδθ : δ ≤ θ₁) (hθ₁ : θ₁ ≤ Real.pi / 2) :
    (∫ θ in δ..θ₁, f θ) ≤ (∫ θ in Work.Spaces.Iθ, f θ) := by
  -- `Iθ = [0, π/2]`, and `[δ, θ₁] ⊆ Iθ`; so the interval integral is a sub-integral of a
  -- nonnegative function over a larger set.
  have hsub : Set.Ioc δ θ₁ ⊆ Work.Spaces.Iθ := by
    intro θ hθ
    exact ⟨by linarith [hδ, hθ.1.le], by linarith [hθ.2, hθ₁]⟩
  rw [intervalIntegral.integral_of_le hδθ]
  refine MeasureTheory.setIntegral_mono_set hA ?_ ?_
  · filter_upwards
      [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc] with θ hθ
    exact hnn θ hθ
  · exact Filter.Eventually.of_forall hsub

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneAsm.eigE_orthonormal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

local notation "Iθ" => Work.Spaces.Iθ


end Work.FTS.EllipticEst.LevelOneAsm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LzeroSingODE =====
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
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.FSlotsTwoD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

set_option autoImplicit false

/-! ## Elementary facts about the angular weights -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem gam_pos_of_pos {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

theorem sig2_nonneg_of_mem_Iθ {γ θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sig2 γ θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

theorem sig4_nonneg_of_mem_Iθ {γ θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sig4 γ θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- The square of the angular weight `W = w·sin(2θ)^{-γ/2}` of `HkSq`. -/
theorem Wt_sq (α z θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hg : Work.Spaces.gam α ≠ 0 := ne_of_gt (gam_pos_of_pos hα)
  have hne : -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2) ≠ 0 := fun h => hg (by linarith)
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  congr 1
  rw [sq, ← Real.rpow_add' hs hne]
  congr 1
  ring

/-! ## The two pointwise slot bounds on `Iθ` -/

theorem sig2_slot_pointwise (α : ℝ) (hα : 0 < α) (γ : ℝ) (hγ2 : γ ≤ 3 / 2)
    (hγg : γ ≤ Work.Spaces.gam α) (F : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth F z θ) ^ 2 * sig2 γ θ)
      ≤ Work.Spaces.HkIntegrand α 2 F z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hkI : 0 ≤ Work.Spaces.HkIntegrand α 2 F z θ :=
    Work.Spaces.HkIntegrand_nonneg α 2 F z θ
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · have h2γ : (2 : ℝ) - γ ≠ 0 := by linarith
    have hz : sig2 γ θ = 0 := by rw [sig2, ← hs0]; exact Real.zero_rpow h2γ
    simp only [hz, mul_zero]
    linarith [hkI]
  · have hexp : sig2 γ θ ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
      show (Real.sin (2 * θ)) ^ (2 - γ) ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      exact Real.rpow_le_rpow_of_exponent_ge hspos hs1 (by linarith)
    have hstep : (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth F z θ) ^ 2 * sig2 γ θ)
        ≤ (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (sq_nonneg _)) (sq_nonneg _)
    have hsp : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      have h : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          = (Real.sin (2 * θ)) ^ (2 : ℝ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        have h2 := Real.rpow_add hspos (2 : ℝ) (-(Work.Spaces.gam α))
        rw [show (2 : ℝ) + -(Work.Spaces.gam α) = 2 - Work.Spaces.gam α by ring] at h2
        exact h2
      simpa using h
    have halg : (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        = (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [hsp, mul_pow, Wt_sq α z θ hα hθ]
      ring
    have hslot : (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 2 F z θ := by
      have h := Work.Spaces.sq_le_HkIntegrand_mixed α 2 F z θ 1 0 (by norm_num) (by norm_num)
      exact h
    calc (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth F z θ) ^ 2 * sig2 γ θ)
        ≤ (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := hstep
      _ = (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2 := halg
      _ ≤ Work.Spaces.HkIntegrand α 2 F z θ := hslot

theorem sig4_slot_pointwise (α : ℝ) (hα : 0 < α) (γ : ℝ) (hγ2 : γ ≤ 3 / 2)
    (hγg : γ ≤ Work.Spaces.gam α) (F : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z) ^ 2 *
        ((deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2 * sig4 γ θ)
      ≤ 10 * Work.Spaces.HkIntegrand α 2 F z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hkI : 0 ≤ Work.Spaces.HkIntegrand α 2 F z θ :=
    Work.Spaces.HkIntegrand_nonneg α 2 F z θ
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · have h4γ : (4 : ℝ) - γ ≠ 0 := by linarith
    have hz : sig4 γ θ = 0 := by rw [sig4, ← hs0]; exact Real.zero_rpow h4γ
    simp only [hz, mul_zero]
    linarith [hkI]
  · have hexp : sig4 γ θ ≤ (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by
      show (Real.sin (2 * θ)) ^ (4 - γ) ≤ (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)
      exact Real.rpow_le_rpow_of_exponent_ge hspos hs1 (by linarith)
    have hstep : (Work.Spaces.w z) ^ 2 *
          ((deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2 * sig4 γ θ)
        ≤ (Work.Spaces.w z) ^ 2 *
          ((deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (sq_nonneg _)) (sq_nonneg _)
    have hsp : (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)
        = (Real.sin (2 * θ)) ^ 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      have h : (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)
          = (Real.sin (2 * θ)) ^ (4 : ℝ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        have h2 := Real.rpow_add hspos (4 : ℝ) (-(Work.Spaces.gam α))
        rw [show (4 : ℝ) + -(Work.Spaces.gam α) = 4 - Work.Spaces.gam α by ring] at h2
        exact h2
      simpa using h
    have halg : (Work.Spaces.w z) ^ 2 *
          ((deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α))
        = (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            * (Work.Spaces.Wt α z θ) ^ 2 := by
      rw [hsp, Wt_sq α z θ hα hθ]
      ring
    have hslot1 : (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 2 F z θ := by
      have h := Work.Spaces.sq_le_HkIntegrand_mixed α 2 F z θ 1 0 (by norm_num) (by norm_num)
      exact h
    have hslot2 : (Work.Spaces.DthIter 2 F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 2 F z θ := by
      have h := Work.Spaces.sq_le_HkIntegrand_mixed α 2 F z θ 2 0 (by norm_num) (by norm_num)
      exact h
    have hmain : (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
          * (Work.Spaces.Wt α z θ) ^ 2
        ≤ 2 * (Work.Spaces.DthIter 2 F z θ * Work.Spaces.Wt α z θ) ^ 2
          + 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      by_cases hd : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pth F z t) θ
      · have hderiv : deriv (fun t : ℝ => Real.sin (2 * t) * Work.Spaces.pth F z t) θ
            = 2 * Real.cos (2 * θ) * Work.Spaces.pth F z θ
              + Real.sin (2 * θ) * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ := by
          have h1 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
            simpa [Function.comp_def, mul_comm] using
              (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
          have hd' : HasDerivAt (fun t : ℝ => Work.Spaces.pth F z t)
              (deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) θ := hd.hasDerivAt
          exact (h1.mul hd').deriv
        have hArec : Work.Spaces.DthIter 2 F z θ
            = 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pth F z θ
              + Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ := by
          have h0 : Work.Spaces.DthIter 2 F z θ
              = Real.sin (2 * θ)
                * deriv (fun t : ℝ => Real.sin (2 * t) * Work.Spaces.pth F z t) θ := rfl
          rw [h0, hderiv]
          ring
        have hs2p2 : Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ
            = Work.Spaces.DthIter 2 F z θ
              - 2 * Real.sin (2 * θ) * (Real.cos (2 * θ) * Work.Spaces.pth F z θ) := by
          rw [hArec]; ring
        have hkey : (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            ≤ 2 * (Work.Spaces.DthIter 2 F z θ) ^ 2
              + 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ) ^ 2 := by
          have hA2 : (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
              ≤ 2 * (Work.Spaces.DthIter 2 F z θ) ^ 2
                + 2 * (2 * Real.sin (2 * θ)
                    * (Real.cos (2 * θ) * Work.Spaces.pth F z θ)) ^ 2 := by
            rw [hs2p2]
            nlinarith [sq_nonneg (Work.Spaces.DthIter 2 F z θ
              + 2 * Real.sin (2 * θ) * (Real.cos (2 * θ) * Work.Spaces.pth F z θ))]
          have hB2 : 2 * (2 * Real.sin (2 * θ)
                * (Real.cos (2 * θ) * Work.Spaces.pth F z θ)) ^ 2
              ≤ 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ) ^ 2 := by
            have hc : (Real.cos (2 * θ)) ^ 2 ≤ 1 := Real.cos_sq_le_one (2 * θ)
            have hsp1 : 0 ≤ (Real.sin (2 * θ) * Work.Spaces.pth F z θ) ^ 2 := sq_nonneg _
            have hprod : (Real.cos (2 * θ)) ^ 2
                  * (Real.sin (2 * θ) * Work.Spaces.pth F z θ) ^ 2
                ≤ (Real.sin (2 * θ) * Work.Spaces.pth F z θ) ^ 2 := by
              simpa using mul_le_mul_of_nonneg_right hc hsp1
            nlinarith [hprod]
          linarith [hA2, hB2]
        calc (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
              * (Work.Spaces.Wt α z θ) ^ 2
            ≤ (2 * (Work.Spaces.DthIter 2 F z θ) ^ 2
                + 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ) ^ 2)
              * (Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hkey (sq_nonneg _)
          _ = 2 * (Work.Spaces.DthIter 2 F z θ * Work.Spaces.Wt α z θ) ^ 2
              + 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
              ring
      · have hp2 : deriv (fun t : ℝ => Work.Spaces.pth F z t) θ = 0 :=
          deriv_zero_of_not_differentiableAt hd
        have hzero : (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            * (Work.Spaces.Wt α z θ) ^ 2 = 0 := by rw [hp2]; ring
        rw [hzero]
        have hnn : (0 : ℝ) ≤ 2 * (Work.Spaces.DthIter 2 F z θ * Work.Spaces.Wt α z θ) ^ 2
            + 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          positivity
        linarith [hnn]
    calc (Work.Spaces.w z) ^ 2 *
          ((deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2 * sig4 γ θ)
        ≤ (Work.Spaces.w z) ^ 2 *
          ((deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) := hstep
      _ = (Real.sin (2 * θ) ^ 2 * deriv (fun t : ℝ => Work.Spaces.pth F z t) θ) ^ 2
            * (Work.Spaces.Wt α z θ) ^ 2 := halg
      _ ≤ 2 * (Work.Spaces.DthIter 2 F z θ * Work.Spaces.Wt α z θ) ^ 2
          + 8 * (Real.sin (2 * θ) * Work.Spaces.pth F z θ * Work.Spaces.Wt α z θ) ^ 2 := hmain
      _ ≤ 2 * Work.Spaces.HkIntegrand α 2 F z θ + 8 * Work.Spaces.HkIntegrand α 2 F z θ := by
          linarith [hslot1, hslot2]
      _ = 10 * Work.Spaces.HkIntegrand α 2 F z θ := by ring

/-! ## The two-dimensional statement -/


end Work.FTS.EllipticEst.Mine
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.OpenQAng =====
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

namespace FstarHkOpen

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## Elementary angular facts -/

/-- `sin(2θ) ≥ 0` on `Iθ = [0,π/2]`. -/
theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) ≤ 1`. -/
theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- The measure of `Iθ` is `π/2`. -/
theorem integral_Iθ_one : ∫ θ in Work.Spaces.Iθ, (1 : ℝ) = π / 2 := by
  rw [MeasureTheory.setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- A function on `Iθ` bounded by a constant is integrable there. -/
theorem integrableOn_Iθ_of_abs_le {f : ℝ → ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ)) {C : ℝ}
    (h : ∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ C) : IntegrableOn f Work.Spaces.Iθ := by
  refine Integrable.mono'
    (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := C)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) hm ?_
  rw [Work.Spaces.Iθ, ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun θ hθ => by simpa [Real.norm_eq_abs] using h θ hθ

/-- `sinθ cos²θ` vanishes wherever `sin 2θ` does. -/
theorem sinCos2_eq_zero_of_sin_two_eq_zero {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.Elliptic.sinCos2 θ = 0 := by
  have h2 : Real.sin θ * Real.cos θ = 0 := by
    have h3 : 2 * (Real.sin θ * Real.cos θ) = 0 := by
      rw [← h, Real.sin_two_mul]; ring
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  rcases mul_eq_zero.mp h2 with h3 | h3
  · simp [Work.Elliptic.sinCos2, h3]
  · simp [Work.Elliptic.sinCos2, h3]


/-- `sinProf i` vanishes wherever `sin 2θ` does. -/
theorem sinProf_eq_zero_of_sin_eq_zero (i : ℕ) {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    sinProf i θ = 0 := by
  induction i with
  | zero => simpa [sinProf] using h
  | succ n _ =>
      show Work.Spaces.DthIter (n + 1) (fun _ θ' => Real.sin (2 * θ')) 0 θ = 0
      rw [Work.Spaces.DthIter_succ]
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [h, zero_mul]

/-- `sinProf i` is a smooth function of the angle on a neighbourhood of `[0,π/2]`. -/
theorem smoothSlice_sinProf (i : ℕ) : Work.Elliptic.SmoothSlice (fun θ => sinProf i θ) := by
  have hbase : Work.Spaces.SmoothNbhd (fun z θ => Real.sin (2 * θ)) := by
    rw [Work.Spaces.SmoothNbhd]
    fun_prop
  have hsm := Work.Spaces.smoothNbhd_DthIter hbase i
  rw [Work.Elliptic.SmoothSlice]
  have hmap : Set.MapsTo (fun θ : ℝ => ((0 : ℝ), θ)) (Set.Ioo (-1) (π / 2 + 1))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun θ hθ => ⟨by norm_num, hθ⟩
  have hcomp := hsm.comp ((contDiffOn_const (c := (0 : ℝ))).prodMk contDiffOn_id) hmap
  simpa [sinProf, Function.uncurry, Function.comp_def] using hcomp

/-- **The angular bound.**  `(D_θ^i (sin 2θ))² sin(2θ)^{-γ}` is bounded on `Iθ` by a
constant depending only on `i`, uniformly in `γ ∈ [1,2]`. -/
theorem sinProf_sq_mul_rpow_le (i : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (γ : ℝ), 1 ≤ γ → γ ≤ 2 → ∀ θ ∈ Work.Spaces.Iθ,
      (sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) ≤ K := by
  obtain ⟨C, hCpos, hC, -, -, -⟩ :=
    Work.Elliptic.SinSliceBounds (fun θ => sinProf i θ) (smoothSlice_sinProf i)
      (sinProf_eq_zero_of_sin_eq_zero i (by norm_num))
      (sinProf_eq_zero_of_sin_eq_zero i (by rw [show 2 * (π / 2) = π by ring, Real.sin_pi]))
  refine ⟨max 1 (C ^ 2), lt_max_of_lt_left one_pos, ?_⟩
  intro γ hγ1 hγ2 θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one θ
  have h2γ : 0 ≤ 2 - γ := by linarith
  have hsle : Real.sin (2 * θ) ^ (2 - γ) ≤ 1 := Real.rpow_le_one hs0 hs1 h2γ
  have hpow : 0 ≤ (Real.sin (2 * θ)) ^ (-γ) := Real.rpow_nonneg hs0 _
  by_cases hzero : Real.sin (2 * θ) = 0
  · rw [sinProf_eq_zero_of_sin_eq_zero i hzero, hzero,
      Real.zero_rpow (by linarith : (-γ) ≠ 0)]
    rw [zero_pow (by norm_num : 2 ≠ 0), zero_mul]
    linarith [le_max_left (1 : ℝ) (C ^ 2)]
  · have hspos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hs0 (Ne.symm hzero)
    have hθ0 : 0 < θ := by
      rcases eq_or_lt_of_le hθ.1 with h | h
      · exact absurd (by rw [← h]; norm_num) hzero
      · exact h
    have hθπ : θ < π / 2 := by
      rcases lt_or_eq_of_le hθ.2 with h | h
      · exact h
      · exact absurd (by rw [h]; rw [show 2 * (π / 2) = π by ring, Real.sin_pi]) hzero
    have hb := hC θ ⟨hθ0, hθπ⟩
    have hsq : (sinProf i θ) ^ 2 ≤ (C * Real.sin (2 * θ)) ^ 2 := by
      have h1 : |sinProf i θ| ^ 2 ≤ (C * Real.sin (2 * θ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hb 2
      rwa [sq_abs] at h1
    have hstep : (sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)
        ≤ (C * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) :=
      mul_le_mul_of_nonneg_right hsq hpow
    have hmain : (C * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) ≤ C ^ 2 := by
      have hsplit : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)
          = (Real.sin (2 * θ)) ^ (2 - γ) := by
        have hcast : (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ 2 :=
          Real.rpow_natCast (Real.sin (2 * θ)) 2
        rw [← hcast, ← Real.rpow_add hspos (2 : ℝ) (-γ)]
        congr 1
      calc (C * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)
          = C ^ 2 * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) := by ring
        _ = C ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) := by rw [hsplit]
        _ ≤ C ^ 2 * 1 := mul_le_mul_of_nonneg_left hsle (sq_nonneg C)
        _ = C ^ 2 := by ring
    exact le_trans hstep (le_trans hmain (le_max_right 1 (C ^ 2)))

/-- The angular constant of the estimate: `angK i` bounds
`(D_θ^i (sin 2θ))² sin(2θ)^{-γ}` on `Iθ` for every `γ ∈ [1,2]`. -/
noncomputable def angK (i : ℕ) : ℝ := Classical.choose (sinProf_sq_mul_rpow_le i)

theorem angK_pos (i : ℕ) : 0 < angK i := (Classical.choose_spec (sinProf_sq_mul_rpow_le i)).1

theorem angK_bound (i : ℕ) (γ : ℝ) (h1 : 1 ≤ γ) (h2 : γ ≤ 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) ≤ angK i :=
  (Classical.choose_spec (sinProf_sq_mul_rpow_le i)).2 γ h1 h2 θ hθ

theorem abs_sinCos2_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
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


/-- The pure `D_z`-summand of the `H^k`-integrand of `F_*·sin 2θ`. -/
theorem zTerm_eq_on (Ψ : ℝ) (z : ℝ) : ∀ θ ∈ Work.Spaces.Iθ,
    (Ψ * Real.sin (2 * θ) * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = Ψ ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have he : Work.Spaces.eta / 2 ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  have he2 : 2 - Work.Spaces.eta ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [hs, Real.zero_rpow he, div_zero, Real.zero_rpow he2]
    ring
  · have hspos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hs0 (Ne.symm hs)
    have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
      rw [pow_two, ← Real.rpow_add hspos (Work.Spaces.eta / 2) (Work.Spaces.eta / 2)]
      congr 1
      ring
    have h2 : (Real.sin (2 * θ)) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta
        = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
      have hcast : (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ 2 :=
        Real.rpow_natCast (Real.sin (2 * θ)) 2
      rw [← hcast, ← Real.rpow_sub hspos (2 : ℝ) Work.Spaces.eta]
    calc (Ψ * Real.sin (2 * θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = Ψ ^ 2 * (Real.sin (2 * θ)) ^ 2
            * ((Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
      _ = Ψ ^ 2 * (Real.sin (2 * θ)) ^ 2
            * ((Work.Spaces.w z) ^ 2 / ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2) := by
          rw [div_pow]
      _ = Ψ ^ 2 * (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta) := by
          rw [h1]; ring
      _ = Ψ ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
          rw [h2]

/-- The mixed summand of the `H^k`-integrand of `F_*·sin 2θ`. -/
theorem mixedTerm_eq_on (α : ℝ) (Ψ z : ℝ) (u : ℝ → ℝ) : ∀ θ ∈ Work.Spaces.Iθ,
    (Ψ * u θ * Work.Spaces.Wt α z θ) ^ 2
      = Ψ ^ 2 * (Work.Spaces.w z) ^ 2
        * ((u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2,
      ← Real.rpow_mul hs0]
    congr 1
    ring
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [show (Ψ * u θ * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = Ψ ^ 2 * (u θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 from by ring,
    h1]
  ring

/-! ## The constants of the estimate -/

/-- The `j`-th pure `D_z`-summand of the `H^k`-integrand of `F`, integrated over the angle. -/
def Uj (F : ℝ → ℝ → ℝ) (z : ℝ) (j : ℕ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j F z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

theorem Uj_nonneg (F : ℝ → ℝ → ℝ) (z : ℝ) (j : ℕ) : 0 ≤ Uj F z j :=
  integral_nonneg fun θ => sq_nonneg _

/-- The sum of the angular constants `angK i`, `i ≤ k`. -/
noncomputable def angKsum (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), angK i

theorem angKsum_nonneg (k : ℕ) : 0 ≤ angKsum k :=
  Finset.sum_nonneg fun i _ => (angK_pos i).le

/-- The constant of the `H^k`-slice estimate. -/
noncomputable def hkConst (k : ℕ) : ℝ :=
  (π / 2) ^ 2 * (1 + (k + 1)) * (1 + angKsum k) + 1

theorem hkConst_pos (k : ℕ) : 0 < hkConst k := by
  have hK := angKsum_nonneg k
  have hk : (0 : ℝ) ≤ 1 + (k + 1) := by positivity
  have h1 : (0 : ℝ) ≤ 1 + angKsum k := by linarith
  have h2 : (0 : ℝ) ≤ (π / 2) ^ 2 * (1 + (k + 1)) :=
    mul_nonneg (sq_nonneg _) hk
  have h3 : (0 : ℝ) ≤ (π / 2) ^ 2 * (1 + (k + 1)) * (1 + angKsum k) :=
    mul_nonneg h2 h1
  rw [hkConst]
  linarith

end FstarHkOpen

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.l2etaL0Asm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option maxHeartbeats 1000000

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.L0

set_option autoImplicit false

/-- **The assembly of the level-`0` `η`-weighted estimate from the three analytic steps** of
Elgindi's `prop:L2` (Steps 1–3 of `prop:H2`).  See the module docstring. -/
theorem l2eta_weak_of_pieces
    (hPsi : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Work.Spaces.HkMem α 0 Ψ ∧
        Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
        Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
          ≤ C * Real.sqrt (Work.Spaces.HkSq α 0 F) ∧
        Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
          ≤ C * Real.sqrt (Work.Spaces.HkSq α 0 F))
    (hG : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
        α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
          ≤ C * Real.sqrt (Work.Spaces.HkSq α 0 F))
    (hB : ∀ (C₁ : ℝ), 0 < C₁ →
      (∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Work.Spaces.HkMem α 0 Ψ ∧
        Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
        Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
        Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
          + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
          ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F)) →
      ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
          ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
              + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))))
    (hu : ∀ (C₁ C_B : ℝ), 0 < C₁ → 0 < C_B →
      (∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Work.Spaces.HkMem α 0 Ψ ∧
        Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
        Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
        Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
          + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
          ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F)) →
      (∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
          ≤ C_B * (Real.sqrt (Work.Spaces.HkSq α 0 F)
              + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)))) →
      ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Work.Spaces.HkMem α 0 (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)) ∧
        Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)))
          ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
              + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))))
    : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 / 4 →
      (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) →
      (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
      (∀ z, 0 < z → Work.Elliptic.Fstar F z = 0) →
      (∀ z, 0 < z → Work.Elliptic.Fstar Ψ z = 0) →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α 0 F →
      Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ) →
      Work.Spaces.HkMem α 0
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) →
      α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
      ≤ C * Work.Spaces.HkSq α 0 F := by
  obtain ⟨C1, hC1, hpsi⟩ := hPsi
  obtain ⟨Cg, hCg, hgrad⟩ := hG
  -- ### the combined first-order constant and bound
  obtain ⟨Cf, hCf, hfirst⟩ : ∃ Cf : ℝ, 0 < Cf ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Work.Spaces.HkMem α 0 Ψ ∧
        Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
        Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
        Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
          + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
          ≤ Cf * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
    refine ⟨2 * C1 + Cg + 1, by linarith, ?_⟩
    intro α F Ψ hα hα4 hw
    obtain ⟨hmΨ, hmCos, hbΨ, hbCos⟩ := hpsi α F Ψ hα hα4 hw
    obtain ⟨hmG, hbG⟩ := hgrad α F Ψ hα hα4 hw
    refine ⟨hmΨ, hmG, hmCos, ?_⟩
    have hF0 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 F) := Real.sqrt_nonneg _
    nlinarith [hbΨ, hbCos, hbG, mul_nonneg (le_of_lt hCg) hF0,
      mul_nonneg (le_of_lt hC1) hF0, hF0]
  -- ### Step 2 and Step 3
  obtain ⟨CB, hCB, hBsq⟩ := hB Cf hCf hfirst
  obtain ⟨Cu, hCu, hulemma⟩ := hu Cf CB hCf hCB hfirst hBsq
  refine ⟨5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2)
      + ((1 + Cg) * CB) ^ 2 + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 heq h0 h1 horthF horthP hsm hmF hmA hmB hmC
  have hw : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ :=
    ⟨heq, h0, h1, horthF, horthP, hsm, hmF, hmA, hmB, hmC⟩
  obtain ⟨hmΨ, hmG, hmCos, hfirstle⟩ := hfirst α F Ψ hα hα4 hw
  have hBle : Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
      ≤ CB * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) :=
    hBsq α F Ψ hα hα4 hw
  obtain ⟨hmu, hule⟩ := hulemma α F Ψ hα hα4 hw
  -- ### abbreviations
  set gG : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Ψ z θ with hgG
  set gu : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ with hgu
  set gcG : ℝ → ℝ → ℝ := fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ) with hgcG
  set g6 : ℝ → ℝ → ℝ := fun z θ => 6 * Ψ z θ with hg6
  set fA : ℝ → ℝ → ℝ := fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) with hfA
  have hAeq : Work.Spaces.HkSq α 0 fA
      = α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
    rw [HkSq_zero_const_mul α (α ^ 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)]
    ring
  -- ### the pointwise identity on the open quadrant
  have hident : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      fA z θ = -F z θ - gcG z θ - Work.Spaces.pthIter 2 Ψ z θ + gu z θ - g6 z θ := by
    intro z θ hz hθ0 hθ1
    have h := heq z hz θ hθ0 hθ1
    rw [Work.Elliptic.bslOp_apply] at h
    simp only [Work.Elliptic.Lzero, hfA, hgcG, hgu, hg6] at h ⊢
    ring_nf at h ⊢
    linarith [h]
  -- ### the majorant bound on the whole domain
  have hmaj : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 fA z θ
        ≤ 5 * (Work.Spaces.HkIntegrand α 0 F z θ
            + Work.Spaces.HkIntegrand α 0 gcG z θ
            + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
            + Work.Spaces.HkIntegrand α 0 gu z θ
            + Work.Spaces.HkIntegrand α 0 g6 z θ) := by
    intro z hz θ hθ
    have hnn1 := Work.Spaces.HkIntegrand_nonneg α 0 F z θ
    have hnn2 := Work.Spaces.HkIntegrand_nonneg α 0 gcG z θ
    have hnn3 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.pthIter 2 Ψ) z θ
    have hnn4 := Work.Spaces.HkIntegrand_nonneg α 0 gu z θ
    have hnn5 := Work.Spaces.HkIntegrand_nonneg α 0 g6 z θ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [HkIntegrand_zero_boundary α _ (Or.inl hz0.symm)]
      have h0' : (0 : ℝ) ≤ Work.Spaces.HkIntegrand α 0 F z θ := hnn1
      nlinarith [hnn1, hnn2, hnn3, hnn4, hnn5]
    · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).1 with hθ0 | hθ0pos
      · rw [HkIntegrand_zero_boundary α _ (Or.inr (Or.inl hθ0.symm))]
        nlinarith [hnn1, hnn2, hnn3, hnn4, hnn5]
      · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).2 with hθπ | hθlt
        · rw [HkIntegrand_zero_boundary α _ (Or.inr (Or.inr hθπ))]
          nlinarith [hnn1, hnn2, hnn3, hnn4, hnn5]
        · rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq, HkIntegrand_zero_eq,
            HkIntegrand_zero_eq, HkIntegrand_zero_eq, HkIntegrand_zero_eq]
          set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hW
          have hid := hident z θ hzpos hθ0pos hθlt
          simp only [hfA, hgcG, hgu, hg6] at hid ⊢
          have hsplit : (α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) * W
              = -(F z θ * W) + -((α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)) * W)
                + -((Work.Spaces.pthIter 2 Ψ z θ) * W)
                + (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) * W
                + -((6 * Ψ z θ) * W) := by
            rw [hid]; ring
          rw [hsplit]
          have hkey := sum_five_sq_le (-(F z θ * W))
            (-((α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)) * W))
            (-((Work.Spaces.pthIter 2 Ψ z θ) * W))
            ((Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) * W)
            (-((6 * Ψ z θ) * W))
          linarith [hkey]
  -- ### the honesty of the majorant
  have hMd : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 F z θ
          + Work.Spaces.HkIntegrand α 0 gcG z θ
          + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 gu z θ
          + Work.Spaces.HkIntegrand α 0 g6 z θ) Work.Spaces.Iθ := by
    intro z hz
    exact ((((hmF.1 z hz).add ((HkMem_zero_const_mul α (α * (5 + α)) hmG).1 z hz)).add
      (hmB.1 z hz)).add (hmu.1 z hz)).add
      ((HkMem_zero_const_mul α 6 hmΨ).1 z hz)
  have hMθ : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn
        (fun θ => 5 * (Work.Spaces.HkIntegrand α 0 F z θ
            + Work.Spaces.HkIntegrand α 0 gcG z θ
            + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
            + Work.Spaces.HkIntegrand α 0 gu z θ
            + Work.Spaces.HkIntegrand α 0 g6 z θ)) Work.Spaces.Iθ :=
    fun z hz => (hMd z hz).const_mul 5
  -- ### the value of the majorant integral
  have hstep1 : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, 5 * (Work.Spaces.HkIntegrand α 0 F z θ
          + Work.Spaces.HkIntegrand α 0 gcG z θ
          + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 gu z θ
          + Work.Spaces.HkIntegrand α 0 g6 z θ))
        = 5 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 gcG z θ)
            + (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 gu z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g6 z θ)) := by
    intro z hz
    have h1 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 F z θ)
        Work.Spaces.Iθ := hmF.1 z hz
    have h2 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 gcG z θ)
        Work.Spaces.Iθ := (HkMem_zero_const_mul α (α * (5 + α)) hmG).1 z hz
    have h3 : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        Work.Spaces.Iθ := hmB.1 z hz
    have h4 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 gu z θ)
        Work.Spaces.Iθ := hmu.1 z hz
    have h5 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 g6 z θ)
        Work.Spaces.Iθ := (HkMem_zero_const_mul α 6 hmΨ).1 z hz
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact integral_five_eq h1 h2 h3 h4 h5
  have hsumInt : MeasureTheory.IntegrableOn
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 gcG z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 gu z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g6 z θ)) Work.Spaces.Iz :=
    (((hmF.2.add (HkMem_zero_const_mul α (α * (5 + α)) hmG).2).add hmB.2).add hmu.2).add
      (HkMem_zero_const_mul α 6 hmΨ).2
  have hMz : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ,
        5 * (Work.Spaces.HkIntegrand α 0 F z θ
            + Work.Spaces.HkIntegrand α 0 gcG z θ
            + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
            + Work.Spaces.HkIntegrand α 0 gu z θ
            + Work.Spaces.HkIntegrand α 0 g6 z θ)) Work.Spaces.Iz := by
    refine MeasureTheory.IntegrableOn.congr_fun (μ := volume)
      (hsumInt.const_mul 5) ?_ (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)
    intro z hz
    exact (hstep1 z hz).symm
  -- ### the value of the majorant integral
  have hval : (∫ z in Set.Ici (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
      5 * (Work.Spaces.HkIntegrand α 0 F z θ
          + Work.Spaces.HkIntegrand α 0 gcG z θ
          + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 gu z θ
          + Work.Spaces.HkIntegrand α 0 g6 z θ))
      = 5 * (Work.Spaces.HkSq α 0 F
          + ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
          + Work.Spaces.HkSq α 0 gu
          + 36 * Work.Spaces.HkSq α 0 Ψ) := by
    rw [MeasureTheory.setIntegral_congr_fun (μ := volume) measurableSet_Ici
      (fun x hx => hstep1 x hx)]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hz1 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
        Work.Spaces.Iz := hmF.2
    have hz2 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 gcG z θ)
        Work.Spaces.Iz := (HkMem_zero_const_mul α (α * (5 + α)) hmG).2
    have hz3 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ) Work.Spaces.Iz := hmB.2
    have hz4 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 gu z θ) Work.Spaces.Iz :=
      hmu.2
    have hz5 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g6 z θ)
        Work.Spaces.Iz := (HkMem_zero_const_mul α 6 hmΨ).2
    rw [integral_five_eq (s := Set.Ici (0 : ℝ)) hz1 hz2 hz3 hz4 hz5]
    have e1 : (∫ z in Set.Ici (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 F z θ) = Work.Spaces.HkSq α 0 F := rfl
    have e2 : (∫ z in Set.Ici (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 gcG z θ)
        = ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG := by
      rw [← HkSq_zero_const_mul α (α * (5 + α)) gG]
      rfl
    have e3 : (∫ z in Set.Ici (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ) := rfl
    have e4 : (∫ z in Set.Ici (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 gu z θ) = Work.Spaces.HkSq α 0 gu := rfl
    have e5 : (∫ z in Set.Ici (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 g6 z θ) = 36 * Work.Spaces.HkSq α 0 Ψ := by
      rw [show (36 : ℝ) = 6 ^ 2 by norm_num]
      rw [← HkSq_zero_const_mul α 6 Ψ]
      rfl
    rw [e1, e2, e3, e4, e5]
  -- ### the `A`-bound
  have hA : Work.Spaces.HkSq α 0 fA
      ≤ 5 * (Work.Spaces.HkSq α 0 F
          + ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
          + Work.Spaces.HkSq α 0 gu
          + 36 * Work.Spaces.HkSq α 0 Ψ) := by
    have hmemfA : Work.Spaces.HkMem α 0 fA :=
      HkMem_zero_const_mul α (α ^ 2)
        (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hmA
    exact (HkSq_zero_le_of_integrand_le α hmemfA hMθ hMz hmaj).trans hval.le
  -- ### the individual `HkSq` bounds
  have hF0 : 0 ≤ Work.Spaces.HkSq α 0 F := Work.Spaces.HkSq_nonneg α 0 F
  have hG0 : 0 ≤ Work.Spaces.HkSq α 0 gG := Work.Spaces.HkSq_nonneg α 0 gG
  have hB0 : 0 ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ) :=
    Work.Spaces.HkSq_nonneg α 0 _
  have hu0 : 0 ≤ Work.Spaces.HkSq α 0 gu := Work.Spaces.HkSq_nonneg α 0 gu
  have hP0 : 0 ≤ Work.Spaces.HkSq α 0 Ψ := Work.Spaces.HkSq_nonneg α 0 Ψ
  have hF0s : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 F) := Real.sqrt_nonneg _
  have hbG := (hgrad α F Ψ hα hα4 hw).2
  have hbPsi := (hpsi α F Ψ hα hα4 hw).2.2.1
  -- `((α(5+α))²)·HkSq gG ≤ 36 Cg² HkSq F`
  have hcGsq : ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG
      ≤ 36 * Cg ^ 2 * Work.Spaces.HkSq α 0 F := by
    have hs : (α * Real.sqrt (Work.Spaces.HkSq α 0 gG)) ^ 2
        ≤ (Cg * Real.sqrt (Work.Spaces.HkSq α 0 F)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hbG 2
    rw [mul_pow, Real.sq_sqrt hG0, mul_pow, Real.sq_sqrt hF0] at hs
    have h5 : (5 + α) ^ 2 ≤ 36 := by nlinarith [hα4]
    have hstep : ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG
        = ((5 + α) ^ 2) * (α ^ 2 * Work.Spaces.HkSq α 0 gG) := by ring
    rw [hstep]
    calc ((5 + α) ^ 2) * (α ^ 2 * Work.Spaces.HkSq α 0 gG)
        ≤ ((5 + α) ^ 2) * (Cg ^ 2 * Work.Spaces.HkSq α 0 F) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 36 * (Cg ^ 2 * Work.Spaces.HkSq α 0 F) :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = 36 * Cg ^ 2 * Work.Spaces.HkSq α 0 F := by ring
  -- `HkSq B ≤ ((1+Cg)CB)² HkSq F`
  have hBsq : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
      ≤ ((1 + Cg) * CB) ^ 2 * Work.Spaces.HkSq α 0 F := by
    have hαG : α * Real.sqrt (Work.Spaces.HkSq α 0 gG)
        ≤ Cg * Real.sqrt (Work.Spaces.HkSq α 0 F) := hbG
    have hcomb : Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
        ≤ (1 + Cg) * CB * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
      have h2 : CB * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 gG))
          ≤ CB * ((1 + Cg) * Real.sqrt (Work.Spaces.HkSq α 0 F)) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCB)
        nlinarith [hαG]
      nlinarith [hBle, h2, mul_nonneg (le_of_lt hCB) hF0s,
        mul_nonneg (mul_nonneg (le_of_lt hCB) (le_of_lt hCg)) hF0s]
    have hs : (Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))) ^ 2
        ≤ ((1 + Cg) * CB * Real.sqrt (Work.Spaces.HkSq α 0 F)) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hcomb 2
    rw [Real.sq_sqrt hB0, mul_pow, mul_pow, Real.sq_sqrt hF0] at hs
    have hgoal : ((1 + Cg) * CB) ^ 2 * Work.Spaces.HkSq α 0 F
        = (1 + Cg) ^ 2 * CB ^ 2 * Work.Spaces.HkSq α 0 F := by ring
    rw [hgoal]
    exact hs
  -- `HkSq u ≤ ((1+Cg)Cu)² HkSq F`
  have husq : Work.Spaces.HkSq α 0 gu ≤ ((1 + Cg) * Cu) ^ 2 * Work.Spaces.HkSq α 0 F := by
    have hαG : α * Real.sqrt (Work.Spaces.HkSq α 0 gG)
        ≤ Cg * Real.sqrt (Work.Spaces.HkSq α 0 F) := hbG
    have hcomb : Real.sqrt (Work.Spaces.HkSq α 0 gu)
        ≤ (1 + Cg) * Cu * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
      have h2 : Cu * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 gG))
          ≤ Cu * ((1 + Cg) * Real.sqrt (Work.Spaces.HkSq α 0 F)) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCu)
        nlinarith [hαG]
      nlinarith [hule, h2, mul_nonneg (le_of_lt hCu) hF0s,
        mul_nonneg (mul_nonneg (le_of_lt hCu) (le_of_lt hCg)) hF0s]
    have hs : (Real.sqrt (Work.Spaces.HkSq α 0 gu)) ^ 2
        ≤ ((1 + Cg) * Cu * Real.sqrt (Work.Spaces.HkSq α 0 F)) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hcomb 2
    rw [Real.sq_sqrt hu0, mul_pow, mul_pow, Real.sq_sqrt hF0] at hs
    have hgoal : ((1 + Cg) * Cu) ^ 2 * Work.Spaces.HkSq α 0 F
        = (1 + Cg) ^ 2 * Cu ^ 2 * Work.Spaces.HkSq α 0 F := by ring
    rw [hgoal]
    exact hs
  -- `36 HkSq Ψ ≤ 36 C1² HkSq F`
  have hPsisq : 36 * Work.Spaces.HkSq α 0 Ψ ≤ 36 * C1 ^ 2 * Work.Spaces.HkSq α 0 F := by
    have hs : (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)) ^ 2
        ≤ (C1 * Real.sqrt (Work.Spaces.HkSq α 0 F)) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hbPsi 2
    rw [Real.sq_sqrt hP0, mul_pow, Real.sq_sqrt hF0] at hs
    nlinarith [hs]
  -- ### the final square-root assembly
  have hAfin : α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      ≤ (5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2))
        * Work.Spaces.HkSq α 0 F := by
    have hA0 : 0 ≤ Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.Spaces.HkSq_nonneg α 0 _
    have hAeq : Work.Spaces.HkSq α 0 fA
        = α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
      rw [HkSq_zero_const_mul α (α ^ 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)]
      ring
    rw [← hAeq]
    have hc1 : 0 ≤ ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG := mul_nonneg (sq_nonneg _) hG0
    have hc2 : 0 ≤ 36 * Work.Spaces.HkSq α 0 Ψ := by linarith
    calc Work.Spaces.HkSq α 0 fA
        ≤ 5 * (Work.Spaces.HkSq α 0 F + ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ) + Work.Spaces.HkSq α 0 gu
            + 36 * Work.Spaces.HkSq α 0 Ψ) := hA
      _ ≤ 5 * ((1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2)
            * Work.Spaces.HkSq α 0 F) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          nlinarith [hcGsq, hBsq, husq, hPsisq, hF0]
      _ = (5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2))
            * Work.Spaces.HkSq α 0 F := by ring
  -- ### the target
  have hfinal : α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
      ≤ (5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2)
          + ((1 + Cg) * CB) ^ 2 + 1) * Work.Spaces.HkSq α 0 F := by
    have hmain : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
        ≤ ((1 + Cg) * CB) ^ 2 * Work.Spaces.HkSq α 0 F := hBsq
    have hK : (0 : ℝ) ≤ 5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2
        + 36 * C1 ^ 2) := by positivity
    calc α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
        ≤ (5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2))
            * Work.Spaces.HkSq α 0 F + ((1 + Cg) * CB) ^ 2 * Work.Spaces.HkSq α 0 F :=
          add_le_add hAfin hmain
      _ = (5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2)
            + ((1 + Cg) * CB) ^ 2) * Work.Spaces.HkSq α 0 F := by ring
      _ ≤ (5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2)
            + ((1 + Cg) * CB) ^ 2 + 1) * Work.Spaces.HkSq α 0 F := by
          refine mul_le_mul_of_nonneg_right ?_ hF0
          linarith
  exact hfinal

end Work.FTS.EllipticEst.Prop.L0
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.pzIter_integral_hasDerivAt =====
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

/-! ## Joint continuity of the integrand on `(-1,∞) × Iθ` -/

/-- The integrand `(s,θ) ↦ (∂_z^k u)(s,θ) · φ(θ)` is jointly continuous on
`(-1,∞) × Iθ`, because `(-1,∞) × Iθ` is contained in the open set `U` on which the
`SmoothNbhd` function `u` is smooth and `φ` is continuous on `Iθ`. -/
theorem continuousOn_uncurry_pzIter_mul (u : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hu : Work.Spaces.SmoothNbhd u) (hφ : ContinuousOn φ Work.Spaces.Iθ) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter k u p.1 p.2 * φ p.2)
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) := by
  have hsm : Work.Spaces.SmoothNbhd (Work.Spaces.pzIter k u) :=
    Work.Spaces.smoothNbhd_pzIter hu k
  have hsub : Set.Ioi (-1 : ℝ) ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.U :=
    Set.prod_mono subset_rfl fun θ hθ =>
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have h1 : ContinuousOn (Function.uncurry (Work.Spaces.pzIter k u))
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) := (hsm.mono hsub).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => φ p.2)
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) :=
    hφ.comp continuousOn_snd fun p hp => hp.2
  exact (h1.mul h2).congr fun p _ => rfl

/-! ## The main theorem -/

theorem pzIter_integral_hasDerivAt (u : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hu : Work.Spaces.SmoothNbhd u) (hφ : ContinuousOn φ Work.Spaces.Iθ) (k : ℕ) {s : ℝ}
    (hs : s ∈ Set.Ioi (-1)) :
    HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k u s θ * φ θ)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter (k + 1) u s θ * φ θ) s := by
  refine Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt
    (g := fun s θ => Work.Spaces.pzIter k u s θ * φ θ)
    (g' := fun s θ => Work.Spaces.pzIter (k + 1) u s θ * φ θ)
    isOpen_Ioi hs ?_ ?_ ?_
  · exact continuousOn_uncurry_pzIter_mul u φ hu hφ k
  · exact continuousOn_uncurry_pzIter_mul u φ hu hφ (k + 1)
  · intro θ hθ s' hs'
    have hsm : Work.Spaces.SmoothNbhd (Work.Spaces.pzIter k u) :=
      Work.Spaces.smoothNbhd_pzIter hu k
    have h := (Work.Spaces.hardyZ_hasDerivAt_slice (Work.Spaces.pzIter k u) hsm hθ hs').mul_const
      (φ θ)
    simpa [Work.Spaces.pzIter_succ] using h

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.rDz_HarOp_of_continuousAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

set_option linter.unusedVariables false

namespace Work.FTS.EllipticEst

/-- For `x > 0` the weighted integrand `s ↦ s ^ (β - 1) * u s` is continuous at `x` as soon as
`u` is continuous on `(0,∞)`: at a positive point the real power `s ↦ s ^ (β - 1)` is
differentiable, for any real exponent. -/
theorem continuousAt_rpow_sub_one_mul_of_continuousOn (β : ℝ) {u : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hu : ContinuousOn u (Set.Ioi 0)) :
    ContinuousAt (fun s : ℝ => s ^ (β - 1) * u s) x :=
  ((Real.hasDerivAt_rpow_const (p := β - 1) (Or.inl (ne_of_gt hx))).continuousAt).mul
    (hu.continuousAt (Ioi_mem_nhds hx))

/-- `HasDerivAt` form of the commutation of `rDz` with the Hardy operator: under the hypotheses
that `u` is continuous on `(0,∞)` and that `s ↦ s^{β-1} u s` is interval integrable on `[0,z]`,
`HarOp β u` has derivative `(-β) z^{-β-1} ∫_0^z s^{β-1} u s ds + z^{-β} (z^{β-1} u z)` at `z`. -/
theorem hasDerivAt_HarOp_of_continuousAt (β : ℝ) {u : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hu : ContinuousOn u (Set.Ioi 0))
    (hint : IntervalIntegrable (fun s : ℝ => s ^ (β - 1) * u s) volume 0 z) :
    HasDerivAt (HarOp β u)
      ((-β) * z ^ (-β - 1) * (∫ s in (0 : ℝ)..z, s ^ (β - 1) * u s)
        + z ^ (-β) * (z ^ (β - 1) * u z)) z := by
  have hcont : ∀ x ∈ Set.Ioi (0 : ℝ), ContinuousAt (fun s : ℝ => s ^ (β - 1) * u s) x :=
    fun x hx => continuousAt_rpow_sub_one_mul_of_continuousOn β hx hu
  have hsm : StronglyMeasurableAtFilter (fun s : ℝ => s ^ (β - 1) * u s) (𝓝 z) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioi (0 : ℝ)) (μ := volume)
      isOpen_Ioi hcont z hz
  -- the fundamental theorem of calculus at the upper endpoint `z > 0`
  have hJ : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, s ^ (β - 1) * u s)
      (z ^ (β - 1) * u z) z :=
    intervalIntegral.integral_hasDerivAt_right hint hsm (hcont z hz)
  have hA : HasDerivAt (fun y : ℝ => y ^ (-β)) ((-β) * z ^ (-β - 1)) z :=
    Real.hasDerivAt_rpow_const (p := -β) (Or.inl (ne_of_gt hz))
  have h := hA.mul hJ
  have hfun : HarOp β u
      = (fun y : ℝ => y ^ (-β))
        * (fun y : ℝ => ∫ s in (0 : ℝ)..y, s ^ (β - 1) * u s) := rfl
  rw [hfun]
  convert h using 1

/-- `rDz` of the Hardy operator: `z ∂_z (HarOp β u)(z) = -β · HarOp β u z + u z`, for `0 < β`,
`u` continuous on `(0,∞)` and `s ↦ s^{β-1} u s` interval integrable on `[0,z]`. -/
theorem rDz_HarOp_of_continuousAt (β : ℝ) (hβ : 0 < β) {u : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hu : ContinuousOn u (Set.Ioi 0))
    (hint : IntervalIntegrable (fun s : ℝ => s ^ (β - 1) * u s) MeasureTheory.volume 0 z) :
    Work.FTS.EllipticEst.rDz (Work.FTS.EllipticEst.HarOp β u) z
      = -β * Work.FTS.EllipticEst.HarOp β u z + u z := by
  have h := (hasDerivAt_HarOp_of_continuousAt (u := u) (z := z) β hz hu hint).deriv
  -- the three real-power identities at `z > 0`
  have h1 : z * z ^ (-β - 1) = z ^ (-β) := by
    have hsp : z ^ (-β) * z ^ (-1 : ℝ) = z ^ (-β - 1) := by
      rw [← Real.rpow_add hz, show -β + (-1 : ℝ) = -β - 1 by ring]
    have hz1 : z * z ^ (-1 : ℝ) = 1 := by
      have h' : z ^ (1 : ℝ) * z ^ (-1 : ℝ) = 1 := by
        rw [← Real.rpow_add hz, show (1 : ℝ) + (-1) = 0 by ring, Real.rpow_zero]
      rwa [Real.rpow_one] at h'
    calc z * z ^ (-β - 1) = z * (z ^ (-β) * z ^ (-1 : ℝ)) := by rw [← hsp]
      _ = z ^ (-β) * (z * z ^ (-1 : ℝ)) := by ring
      _ = z ^ (-β) := by rw [hz1, mul_one]
  have h2 : z * z ^ (-β) = z ^ (1 - β) := by
    have h' : z ^ (1 : ℝ) * z ^ (-β) = z ^ (1 - β) := by
      rw [← Real.rpow_add hz, show (1 : ℝ) + -β = 1 - β by ring]
    rwa [Real.rpow_one] at h'
  have h3 : z ^ (1 - β) * z ^ (β - 1) = 1 := by
    rw [← Real.rpow_add hz, show 1 - β + (β - 1) = 0 by ring, Real.rpow_zero]
  set J := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * u s with hJdef
  -- the pointwise algebra `z · (derivative) = -β · HarOp β u z + u z`
  have hmain : z * ((-β) * z ^ (-β - 1) * J + z ^ (-β) * (z ^ (β - 1) * u z))
      = -β * (z ^ (-β) * J) + u z := by
    have e1 : z * ((-β) * z ^ (-β - 1) * J) = -β * (z ^ (-β) * J) := by
      rw [show z * ((-β) * z ^ (-β - 1) * J) = (z * z ^ (-β - 1)) * (-β * J) by ring, h1]
      ring
    have e2 : z * (z ^ (-β) * (z ^ (β - 1) * u z)) = u z := by
      rw [show z * (z ^ (-β) * (z ^ (β - 1) * u z))
          = (z * z ^ (-β)) * (z ^ (β - 1) * u z) by ring, h2]
      rw [show z ^ (1 - β) * (z ^ (β - 1) * u z)
          = (z ^ (1 - β) * z ^ (β - 1)) * u z by ring, h3, one_mul]
    rw [mul_add, e1, e2]
  simp only [rDz, h, HarOp]
  exact hmain

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.TopCoreB.FEL.uSlot_Icc_le_FarR =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB.FEL

open Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false



end Work.FTS.EllipticEst.remov.TopCoreB.FEL
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarReflect =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The reflection `θ ↦ π/2 - θ` of the far window `[3π/8, π/2]`

For the far-window bound on `v = u/cos θ` one substitutes `x = π/2 - θ ∈ [0, π/8]`, so that
`v(π/2 - x) = u(π/2 - x)/sin x`.  This file collects the definitions (`xEnd`, `shiftU`,
`shiftV`, `secH`), the elementary reflection calculus for `iteratedDeriv`, the change of
variables for the far-window integral, and the smoothness/vanishing/integrability transfers
from the `θ`-side to the `x`-side.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false

/-- The right endpoint `π/8` of the reflected far window. -/
abbrev xEnd : ℝ := Real.pi / 8

theorem xEnd_pos : 0 < xEnd := by rw [xEnd]; positivity

theorem xEnd_le_one : xEnd ≤ 1 := by
  rw [xEnd]; linarith [Real.pi_pos, Real.pi_lt_four]

theorem xEnd_lt_pi_half : xEnd < Real.pi / 2 := by
  rw [xEnd]; linarith [Real.pi_pos]

theorem xEnd_lt_pi_four : xEnd < Real.pi / 4 := by
  rw [xEnd]; linarith [Real.pi_pos]


/-- The reflected slice `x ↦ u (π/2 - x)`. -/
abbrev shiftU (u : ℝ → ℝ) : ℝ → ℝ := fun x => u (Real.pi / 2 - x)

/-- The bounded quotient `x / sin x` on the far window. -/
abbrev secH : ℝ → ℝ := fun x => x / Real.sin x

/-- `v = u / cos θ` in the reflected variable: `x ↦ u (π/2 - x) / sin x`. -/
abbrev shiftV (u : ℝ → ℝ) : ℝ → ℝ := fun x => shiftU u x / Real.sin x

/-- The reflection `x ↦ π/2 - x`. -/
abbrev reflectC : ℝ → ℝ := fun x => Real.pi / 2 - x

theorem reflectC_eq (x : ℝ) : reflectC x = -(x - Real.pi / 2) := by rw [reflectC]; ring

/-- **Chain rule for the reflection** `θ ↦ c - θ`. -/
theorem iteratedDeriv_comp_const_sub (n : ℕ) (f : ℝ → ℝ) (c : ℝ) :
    iteratedDeriv n (fun x => f (c - x)) = fun x => (-1) ^ n * iteratedDeriv n f (c - x) := by
  have h := iteratedDerivWithin_comp_const_sub (𝕜 := ℝ) (f := f) (s := Set.univ) (n := n) c
  simpa using h

/-- `sin (2 (π/2 - x)) = sin (2x)`. -/
theorem sin_two_pi_half_sub (x : ℝ) : Real.sin (2 * (Real.pi / 2 - x)) = Real.sin (2 * x) := by
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]

/-- **Substitution `θ = π/2 - x` on the far window.** -/
theorem integral_farSet_eq (F : ℝ → ℝ) :
    (∫ θ in farSet, F θ) = ∫ x in (0 : ℝ)..xEnd, F (Real.pi / 2 - x) := by
  have hIcc : farSet = Set.Icc (3 * Real.pi / 8) (Real.pi / 2) := rfl
  have hle : (3 : ℝ) * Real.pi / 8 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [hIcc, setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := 3 * Real.pi / 8)
      (b := Real.pi / 2)).symm, ← intervalIntegral.integral_of_le hle]
  have h := intervalIntegral.integral_comp_sub_left (fun y : ℝ => F (Real.pi / 2 - y))
    (Real.pi / 2) (a := 3 * Real.pi / 8) (b := Real.pi / 2)
  simp only [sub_sub_cancel] at h
  rw [show Real.pi / 2 - 3 * Real.pi / 8 = xEnd by rw [xEnd]; ring,
    show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) by ring] at h
  exact h

/-- `vF u` is the reflected `v`. -/
theorem vF_eq_shiftV (u : ℝ → ℝ) :
    vF u = fun θ => shiftV u (Real.pi / 2 - θ) := by
  funext θ
  rw [vF, shiftV, shiftU, Real.sin_pi_div_two_sub]
  rw [show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring]

/-- The far-window integrand in the reflected variable. -/
theorem farSet_integrand_eq (k : ℕ) (γ : ℝ) (m : ℕ) (u : ℝ → ℝ) (x : ℝ) :
    (iteratedDeriv m (vF u) (Real.pi / 2 - x)) ^ 2 * qW k γ (Real.pi / 2 - x)
      = (iteratedDeriv m (shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) := by
  rw [vF_eq_shiftV, iteratedDeriv_comp_const_sub]
  have hx : Real.pi / 2 - (Real.pi / 2 - x) = x := by ring
  have hp : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, show m * 2 = 2 * m by ring, pow_mul]
    norm_num
  simp only [qW, hx, sin_two_pi_half_sub]
  rw [mul_pow, hp, one_mul]

/-- **The far-window left-hand side in the reflected variable.** -/
theorem farSet_LHS_eq (k : ℕ) (γ : ℝ) (m : ℕ) (u : ℝ → ℝ) :
    (∫ θ in farSet, (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ)
      = ∫ x in (0 : ℝ)..xEnd, (iteratedDeriv m (shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) := by
  rw [integral_farSet_eq]
  refine intervalIntegral.integral_congr fun x _ => ?_
  exact farSet_integrand_eq k γ m u x

/-- The reflected slot integrand. -/
theorem slot_integrand_reflect (j : ℕ) (p : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    (iteratedDeriv j u (Real.pi / 2 - x)) ^ 2
        * Real.rpow (Real.sin (2 * (Real.pi / 2 - x))) p
      = (iteratedDeriv j (shiftU u) x) ^ 2 * Real.rpow (Real.sin (2 * x)) p := by
  have h := congrFun (iteratedDeriv_comp_const_sub j u (Real.pi / 2)) x
  have h' : iteratedDeriv j (shiftU u) x = (-1) ^ j * iteratedDeriv j u (Real.pi / 2 - x) := h
  have hsq : (iteratedDeriv j u (Real.pi / 2 - x)) ^ 2 = (iteratedDeriv j (shiftU u) x) ^ 2 := by
    have hp : ((-1 : ℝ) ^ j) ^ 2 = 1 := by
      rw [← pow_mul, show j * 2 = 2 * j by ring, pow_mul]
      norm_num
    rw [h', mul_pow, hp, one_mul]
  rw [sin_two_pi_half_sub, hsq]

/-- **A far-window `u`-slot integral in the reflected variable.** -/
theorem integral_farSet_slot_eq (j : ℕ) (p : ℝ) (u : ℝ → ℝ) :
    (∫ θ in farSet, (iteratedDeriv j u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) p)
      = ∫ x in (0 : ℝ)..xEnd, (iteratedDeriv j (shiftU u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) p := by
  rw [integral_farSet_eq]
  refine intervalIntegral.integral_congr fun x _ => ?_
  exact slot_integrand_reflect j p u x

section Basic

variable {x θ : ℝ}

theorem sin_two_nonneg_Ioc (hx : x ∈ Set.Ioc 0 xEnd) : 0 ≤ Real.sin (2 * x) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by
    have := hx.2; rw [xEnd] at this; linarith [Real.pi_pos]⟩

theorem sin_two_pos_Ioc (hx : x ∈ Set.Ioc 0 xEnd) : 0 < Real.sin (2 * x) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by
    have := hx.2; rw [xEnd] at this; linarith [Real.pi_pos])


/-- On the reflected window, `x ≤ sin (2x)`. -/
theorem self_le_sin_two (hx : x ∈ Set.Ioc 0 xEnd) : x ≤ Real.sin (2 * x) := by
  have h0 : 0 ≤ 2 * x := by linarith [hx.1]
  have h1 : 2 * x ≤ Real.pi / 2 := by
    have := hx.2; rw [xEnd] at this; linarith [Real.pi_pos]
  have h2 := Real.mul_le_sin h0 h1
  have h3 : (4 / Real.pi) * x ≤ Real.sin (2 * x) := by
    calc (4 / Real.pi) * x = 2 / Real.pi * (2 * x) := by ring
      _ ≤ Real.sin (2 * x) := h2
  have h4 : (1 : ℝ) ≤ 4 / Real.pi := by
    rw [le_div_iff₀ (by linarith [Real.pi_pos])]; linarith [Real.pi_lt_four]
  calc x = 1 * x := (one_mul x).symm
    _ ≤ (4 / Real.pi) * x := mul_le_mul_of_nonneg_right h4 (by linarith [hx.1])
    _ ≤ Real.sin (2 * x) := h3

end Basic

/-- Reflected smoothness. -/
theorem contDiffOn_shiftU {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (shiftU u) (Set.Ioo 0 xEnd) := by
  have hmap : ContDiffOn ℝ n (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 xEnd) := by fun_prop
  have hmt : MapsTo (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 xEnd)
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro x hx
    exact ⟨by linarith [hx.2, xEnd_lt_pi_half], by linarith [hx.1]⟩
  exact hu.comp hmap hmt

/-- `shiftU u` is `C^N` on the half-open interval `(0, xEnd]`. -/
theorem contDiffOn_shiftU_Ioc {N : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ N u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ N (shiftU u) (Set.Ioc 0 xEnd) := by
  have hmap : ContDiffOn ℝ N (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 (Real.pi / 4)) := by
    fun_prop
  have hmt : MapsTo (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 (Real.pi / 4))
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro x hx
    exact ⟨by linarith [hx.2, Real.pi_pos], by linarith [hx.1]⟩
  have h1 : ContDiffOn ℝ N (shiftU u) (Set.Ioo 0 (Real.pi / 4)) := hu.comp hmap hmt
  refine h1.mono fun x hx => ?_
  exact ⟨hx.1, by linarith [hx.2, xEnd_lt_pi_four]⟩

/-- The reflected slice tends to `u (π/2) = 0` at `0⁺`. -/
theorem tendsto_shiftU {u : ℝ → ℝ} (hu : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hu1 : u (Real.pi / 2) = 0) :
    Tendsto (shiftU u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hmem : Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], le_rfl⟩
  have hcont : Tendsto u (nhdsWithin (Real.pi / 2) (Set.Icc 0 (Real.pi / 2)))
      (nhds (u (Real.pi / 2))) := hu.continuousWithinAt hmem
  rw [hu1] at hcont
  refine hcont.comp ?_
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hc : ContinuousAt (fun x : ℝ => Real.pi / 2 - x) 0 := by fun_prop
    have h1 : Tendsto (fun x : ℝ => Real.pi / 2 - x) (nhds (0 : ℝ))
        (nhds (Real.pi / 2 - 0)) := hc.tendsto
    simpa using h1.mono_left nhdsWithin_le_nhds
  · have hlt : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2))
    filter_upwards [self_mem_nhdsWithin, hlt] with x hxpos hxlt
    have h1 : (0 : ℝ) < x := hxpos
    have h2 : x < Real.pi / 2 := hxlt
    exact ⟨by linarith, by linarith⟩

theorem measurableEmbedding_reflectC : MeasurableEmbedding reflectC := by
  have h : MeasurableEmbedding (fun x : ℝ => -(x - Real.pi / 2)) :=
    measurableEmbedding_neg.comp (measurableEmbedding_subRight (Real.pi / 2))
  have hfun : reflectC = fun x : ℝ => -(x - Real.pi / 2) := by
    funext x; rw [reflectC_eq]
  rwa [hfun]

theorem measurePreserving_reflectC : MeasurePreserving reflectC volume volume := by
  have h : MeasurePreserving (fun x : ℝ => -(x - Real.pi / 2)) volume volume :=
    (Measure.measurePreserving_neg volume).comp
      (measurePreserving_sub_right volume (Real.pi / 2))
  have hfun : reflectC = fun x : ℝ => -(x - Real.pi / 2) := by
    funext x; rw [reflectC_eq]
  rwa [hfun]

theorem preimage_reflectC_farSet : reflectC ⁻¹' farSet = Set.Icc 0 xEnd := by
  ext x
  simp only [mem_preimage, reflectC, farSet, mem_Icc, xEnd]
  constructor
  · intro h
    exact ⟨by linarith [h.2, Real.pi_pos], by linarith [h.1]⟩
  · intro h
    exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- Integrability of a reflected slot, transferred from the angular interval. -/
theorem integrableOn_shift_slot (j : ℕ) (p : ℝ) (u : ℝ → ℝ)
    (h : IntegrableOn (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) p)
      Work.Spaces.Iθ) :
    IntegrableOn (fun x : ℝ => (iteratedDeriv j (shiftU u) x) ^ 2
      * Real.rpow (Real.sin (2 * x)) p) (Set.Icc 0 xEnd) := by
  have h1 : IntegrableOn (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) p)
      farSet := h.mono_set farSet_subset_Iθ
  have h2 := (MeasurePreserving.integrableOn_comp_preimage
    (measurePreserving_reflectC) measurableEmbedding_reflectC (s := farSet)).mpr h1
  rw [preimage_reflectC_farSet] at h2
  refine h2.congr_fun (fun x _ => ?_) measurableSet_Icc
  exact slot_integrand_reflect j p u x

/-- The same, on the half-open interval `(0, xEnd]`. -/
theorem integrableOn_shift_slot_Ioc (j : ℕ) (p : ℝ) (u : ℝ → ℝ)
    (h : IntegrableOn (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) p)
      Work.Spaces.Iθ) :
    IntegrableOn (fun x : ℝ => (iteratedDeriv j (shiftU u) x) ^ 2
      * Real.rpow (Real.sin (2 * x)) p) (Set.Ioc 0 xEnd) :=
  (integrableOn_shift_slot j p u h).mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)

end Work.FTS.EllipticEst.remov.TopCoreB
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice5_reduce =====
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

/-! ## Elementary facts about `Iθ` and the weight `σ₄` -/

lemma Iθ_eq_R : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl


lemma sin_two_nonneg_R {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Iθ_eq_R] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- Almost every point of `Iθ` is interior. -/
lemma ae_mem_Ioo_Iθ_R :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ))).symm
  rw [Iθ_eq_R, Measure.restrict_congr_set h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- `σ₄ = sin(2θ)^{4-γ}` is nonnegative on `Iθ`. -/
lemma sig4_nonneg_R (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
  Real.rpow_nonneg (sin_two_nonneg_R hθ) _

/-- `σ₄ ≤ sEta` on `Iθ` (for `1 ≤ γ ≤ 3/2`); indeed `σ₄ ≤ 1 ≤ sEta`. -/
lemma sig4_le_sEta_R (γ : ℝ) (_hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ Work.FTS.EllipticEst.sEta θ := by
  have hs := sin_two_nonneg_R hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h4 : (0 : ℝ) ≤ 4 - γ := by linarith
  have h4' : (4 : ℝ) - γ ≠ 0 := by linarith
  have heta : (-(Work.Spaces.eta)) ≠ 0 := by
    rw [Work.Spaces.eta]; norm_num
  rcases eq_or_lt_of_le hs with hz | hpos
  · have hz1 : Real.rpow (0 : ℝ) (4 - γ) = 0 := Real.zero_rpow h4'
    rw [← hz, hz1, Work.FTS.EllipticEst.sEta, ← hz, Real.zero_rpow heta]
  · have hle1 : Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ 1 :=
      Real.rpow_le_one hpos.le hs1 h4
    have hge1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := by
      rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg hpos.le]
      have h2 : Real.rpow (Real.sin (2 * θ)) Work.Spaces.eta ≤ 1 :=
        Real.rpow_le_one hpos.le hs1 Work.Spaces.eta_nonneg
      exact (one_le_inv₀ (Real.rpow_pos_of_pos hpos _)).mpr h2
    linarith

/-! ## Elementary algebraic inequalities -/


lemma add_sq_le_four (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-! ## Reduction 1: `L ≤ 3 (J + 36 A2' + B2)` -/


/-! ## Reduction 2: the expansion of `J` -/


/-! ## Integrability of the auxiliary integrands -/







/-! ## The final absorption step of the assembly

Writing `L = X^2` with `X = sqrt L`, the inequality produced by the room estimate and
Cauchy-Schwarz reads `L <= -Q + C1 (Bv2 + Bv1 + Bv0) + 6 sqrt (A2 * L) + sqrt (B2 * L)`, with
`Q >= 0`, `Bv2 + Bv1 + Bv0 <= C2 R`, `A2 <= R`, `B2 <= R`, `R >= 0`.  Dropping `-Q` and
solving the resulting quadratic inequality for `X` bounds `L` by `100 R`; then `Q` is bounded
as well. -/



end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_ang_reduce =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `slice_ang_gen`: reduction to the far region `[3π/8, π/2]`

This file reduces the target `Work.FTS.EllipticEst.remov.slice_ang_gen` to

* the **outer region** `Icc 0 (3π/8)`, which is *proved* in
  `Submission/Work/FTS/EllipticEst/remov/slice_ang_outer.lean` (via the two pointwise bounds
  `near_pointwise_bound` / `mid_pointwise_bound`), and
* the **far region** `Icc (3π/8) (π/2)`, which is the only remaining input
  (`SliceAngFar` below; see `NOTES_slice_ang_gen_REFINED.md` for its structure and the two
  remaining obstructions).

The reduction itself is the interval splitting `Iθ = Icc 0 (3π/8) ∪ Icc (3π/8) (π/2)` (the two
pieces overlap only in the null set `{3π/8}`), which is the proved lemma
`remov/slice_ang_split`.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- The right hand side `R` of the target estimate. -/
noncomputable def AngRHS (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) : ℝ :=
  (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
    + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
        (iteratedDeriv j u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
    + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
    + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
    + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)



end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.wsSliceLeft =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

/-- **Left-end pointwise vanishing from the angular moment condition.**

The integrand `θ ↦ Lzero1 u θ · sinθcos²θ` is an exact `θ`-derivative
(`Work.Elliptic.hasDerivAt_Lzero_antideriv`): with the antiderivative
`A(θ) = -u'(θ) sinθcos²θ + u(θ) cosθ cos 2θ`,

  `∫_{Iθ} Lzero1 u · sinθcos²θ = A(π/2) - lim_{0⁺} A = -lim_{0⁺} u`,

because `A(π/2) = 0` (`sinθcos²θ` and `cosθcos2θ` both vanish at `π/2`) and
`A(θ) → lim_{0⁺} u` as `θ → 0⁺` (`sinθcos²θ → 0`, `cosθcos2θ → 1`).  The weighted
square-integrability of `u''` supplies the needed boundedness of `u'` near `0`, hence the
existence of the limit `lim_{0⁺} u` (`SourceBound.auxLimitAtZero`), and the assumed vanishing
of the moment then forces that limit to be `0` (`SourceBound.auxMoment`). -/
theorem wsSliceLeft {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hL : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = 0) :
    Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨α, hα⟩ := SourceBound.auxLimitAtZero hsm h2
  have hm := SourceBound.auxMoment hsm h2 hL hα
  have hα0 : α = 0 := by
    have h1 : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = -α := hm
    rw [hmom] at h1
    linarith
  simpa [hα0] using hα

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.sinIter_weight_bound =====
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

set_option linter.unusedVariables false

/-! ## The polynomial describing `D_θ^i (sin 2θ) / sin 2θ` -/

/-- The sequence of polynomials `pᵢ` with
`D_θ^i (sin 2θ) = sin(2θ) · pᵢ (cos 2θ)`, defined by `p₀ = 1` and
`p_{i+1} = 2 X pᵢ - 2 (1 - X²) pᵢ'`. -/
def sinPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | (i+1) => 2 * Polynomial.X * sinPoly i - 2 * (1 - Polynomial.X^2) * (sinPoly i).derivative

/-- The evaluation of the defining recursion of `sinPoly`. -/
theorem sinPoly_eval_succ (i : ℕ) (t : ℝ) :
    (sinPoly (i+1)).eval t =
      2 * t * (sinPoly i).eval t - 2 * (1 - t^2) * (sinPoly i).derivative.eval t := by
  simp [sinPoly, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow]

/-- One step of the recursion `sinIter (i+1) θ = sin(2θ) · (sinIter i)' θ`. -/
theorem sinIter_succ (i : ℕ) (θ : ℝ) :
    sinIter (i+1) θ = Real.sin (2*θ) * deriv (fun t : ℝ => sinIter i t) θ := by
  simp [sinIter, Work.Spaces.DthIter, Work.Spaces.Dth, Work.Spaces.pth]

/-- The derivative of `θ ↦ sin(2θ) · p (cos 2θ)`, computed with the chain rule. -/
theorem deriv_sin_mul_eval (p : Polynomial ℝ) (θ : ℝ) :
    deriv (fun t : ℝ => Real.sin (2*t) * p.eval (Real.cos (2*t))) θ
      = 2 * Real.cos (2*θ) * p.eval (Real.cos (2*θ))
        - 2 * (Real.sin (2*θ))^2 * p.derivative.eval (Real.cos (2*θ)) := by
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2*t)) (2 * Real.cos (2*θ)) θ := by
    have h := (Real.hasDerivAt_sin (2*θ)).comp θ ((hasDerivAt_id θ).const_mul (2:ℝ))
    simpa [Function.comp_def, mul_comm] using h
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2*t)) (-2 * Real.sin (2*θ)) θ := by
    have h := (Real.hasDerivAt_cos (2*θ)).comp θ ((hasDerivAt_id θ).const_mul (2:ℝ))
    simpa [Function.comp_def, mul_comm] using h
  have hpc : HasDerivAt (fun t : ℝ => p.eval (Real.cos (2*t)))
      (p.derivative.eval (Real.cos (2*θ)) * (-2*Real.sin (2*θ))) θ := by
    have h := (Polynomial.hasDerivAt p (Real.cos (2*θ))).comp θ hcos
    simpa [Function.comp_def] using h
  have hmul := hsin.mul hpc
  change deriv ((fun t : ℝ => Real.sin (2*t)) * fun t : ℝ => p.eval (Real.cos (2*t))) θ
      = 2 * Real.cos (2*θ) * p.eval (Real.cos (2*θ))
        - 2 * (Real.sin (2*θ))^2 * p.derivative.eval (Real.cos (2*θ))
  rw [hmul.deriv]
  ring

/-- The fundamental factorisation `sinIter i θ = sin(2θ) · pᵢ (cos 2θ)`. -/
theorem sinIter_eq_sinPoly (i : ℕ) :
    ∀ θ, sinIter i θ = Real.sin (2*θ) * (sinPoly i).eval (Real.cos (2*θ)) := by
  induction i with
  | zero => intro θ; simp [sinIter, sinPoly]
  | succ i ih =>
    intro θ
    rw [sinIter_succ]
    have hfun : (fun t : ℝ => sinIter i t)
        = fun t => Real.sin (2*t) * (sinPoly i).eval (Real.cos (2*t)) := by
      funext t; exact ih t
    rw [hfun, deriv_sin_mul_eval]
    have hs : (Real.sin (2*θ))^2 = 1 - (Real.cos (2*θ))^2 := by
      have h := Real.sin_sq_add_cos_sq (2*θ); linarith
    rw [hs, sinPoly_eval_succ]

/-! ## Uniform bounds -/

/-- A polynomial is bounded on `[-1,1]` by the sum of the absolute values of its
coefficients. -/
theorem poly_eval_abs_le (p : Polynomial ℝ) (t : ℝ) (ht : |t| ≤ 1) :
    |p.eval t| ≤ ∑ n ∈ p.support, |p.coeff n| := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc |∑ n ∈ p.support, p.coeff n * t ^ n| ≤ ∑ n ∈ p.support, |p.coeff n * t ^ n| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ p.support, |p.coeff n| * |t| ^ n := by
        refine Finset.sum_congr rfl ?_
        intro n _; rw [abs_mul, abs_pow]
    _ ≤ ∑ n ∈ p.support, |p.coeff n| * 1 := by
        refine Finset.sum_le_sum ?_
        intro n _
        exact mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg t) ht) (abs_nonneg _)
    _ = ∑ n ∈ p.support, |p.coeff n| := by simp

/-- The universal constant bounding `pᵢ` on `[-1,1]`: the sum of the absolute values of
the coefficients of `sinPoly i`. -/
def sinBound (i : ℕ) : ℝ := ∑ n ∈ (sinPoly i).support, |(sinPoly i).coeff n|


/-- `|sinIter i θ| ≤ sin(2θ) · sinBound i` for `θ` with `sin 2θ ≥ 0`. -/
theorem sinIter_abs_le (i : ℕ) (θ : ℝ) (h : 0 ≤ Real.sin (2*θ)) :
    |sinIter i θ| ≤ Real.sin (2*θ) * sinBound i := by
  rw [sinIter_eq_sinPoly i θ, abs_mul, abs_of_nonneg h]
  exact mul_le_mul_of_nonneg_left (poly_eval_abs_le _ _ (Real.abs_cos_le_one _)) h

/-- The squared form of `sinIter_abs_le`. -/
theorem sinIter_sq_le (i : ℕ) (θ : ℝ) (h : 0 ≤ Real.sin (2*θ)) :
    (sinIter i θ)^2 ≤ (sinBound i)^2 * (Real.sin (2*θ))^2 := by
  have h1 := sinIter_abs_le i θ h
  have h2 : (sinIter i θ)^2 = |sinIter i θ|^2 := by rw [sq_abs]
  rw [h2]
  have h3 : (Real.sin (2*θ) * sinBound i)^2 = (sinBound i)^2 * (Real.sin (2*θ))^2 := by
    ring
  calc |sinIter i θ|^2 ≤ (Real.sin (2*θ) * sinBound i)^2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = (sinBound i)^2 * (Real.sin (2*θ))^2 := h3

/-- For `0 < s ≤ 1` and `1 ≤ γ ≤ 2`: `s² · s^{-γ} ≤ 1`. -/
theorem sq_mul_rpow_neg_le_one (s γ : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (h1 : 1 ≤ γ) (h2 : γ ≤ 2) : s ^ 2 * s ^ (-γ) ≤ 1 := by
  have hs0 : 0 ≤ s := le_of_lt hs
  calc s ^ 2 * s ^ (-γ) = s ^ (2:ℝ) * s ^ (-γ) := by rw [← Real.rpow_ofNat s 2]
    _ = s ^ ((2:ℝ) + -γ) := by rw [Real.rpow_add hs]
    _ ≤ 1 := Real.rpow_le_one hs0 hs1 (by linarith)

/-! ## The target bound -/

theorem sinIter_weight_bound (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.sinIter i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ C := by
  refine ⟨(sinBound i)^2, sq_nonneg _, ?_⟩
  intro α hα hα1 θ hθ
  have hsin_nonneg : 0 ≤ Real.sin (2*θ) := by
    have h1 : 0 ≤ θ := hθ.1
    have h2 : θ ≤ π/2 := hθ.2
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hgam1 : 1 ≤ Work.Spaces.gam α := by simp [Work.Spaces.gam]; linarith
  have hgam2 : Work.Spaces.gam α ≤ 2 := by simp [Work.Spaces.gam]; linarith
  rcases lt_or_eq_of_le hsin_nonneg with hpos | hzero
  · have hsq := sinIter_sq_le i θ hsin_nonneg
    have hpow_nonneg : 0 ≤ (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_nonneg hsin_nonneg _
    calc (sinIter i θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α))
        ≤ ((sinBound i)^2 * (Real.sin (2*θ))^2)
            * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hsq hpow_nonneg
      _ = (sinBound i)^2 * ((Real.sin (2*θ))^2
            * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α))) := by ring
      _ ≤ (sinBound i)^2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact sq_mul_rpow_neg_le_one _ _ hpos (Real.sin_le_one _) hgam1 hgam2
      _ = (sinBound i)^2 := mul_one _
  · have hz : Real.sin (2*θ) = 0 := hzero.symm
    rw [hz, Real.zero_rpow (by linarith : -(Work.Spaces.gam α) ≠ 0), mul_zero]
    exact sq_nonneg _

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.zAMGM_Hk_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-! ## The weight `ρ = w²` and its elementary properties -/

private def rho_prv (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2







/-! ## Young's inequality and the elementary square-root lemmas -/




private lemma sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have h1 := Real.sq_sqrt ha
    have h2 := Real.sq_sqrt hb
    have h3 : 0 ≤ Real.sqrt a * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [h1, h2, h3]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-! ## The core estimate -/


/-! ## The smoothness of the iterates `rDzIter k g` -/



/-! ## The boundary term `w² z h h₁`

The one input of the integration by parts in `zAMGM_core` that is not an elementary estimate: the
boundary term `w(z)² z h(z) h₁(z)` vanishes both at `z → 0⁺` and at `z → ∞`.

Route: the functions `u = w h`, `v = w h₁` are, in the logarithmic variable, the profiles
`P(t) = e^{t/2}w(e^t)h(e^t)`, `Q(t) = e^{t/2}w(e^t)h₁(e^t)`, and `w(z)² z h h₁ = P(log z) Q(log z)`.
The three finiteness hypotheses say exactly that `P, P', Q, Q'` are square-integrable, hence also
that `P ^ 2`, `Q ^ 2` have integrable derivatives; the Mathlib lemma
`tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi` (applied to `P ^ 2` and `Q ^ 2`, and its `Iic`
counterpart) then gives `P, Q → 0` at both ends of the logarithmic line, whence the product.
The substitution `z = e^t` in the integrals is `integrableOn_comp_log_Ioi_zero`. -/

private lemma hasDerivAt_w_prv (z : ℝ) (hz : 0 < z) :
    HasDerivAt Work.Spaces.w (-2 * Work.Spaces.w z / (z * (1 + z))) z := by
  have hnum : HasDerivAt (fun y : ℝ => (1 + y) ^ 2) (2 * (1 + z)) z := by
    have h : HasDerivAt (fun y : ℝ => 1 + y) (1 : ℝ) z := by
      simpa using (hasDerivAt_id z).const_add (1 : ℝ)
    have h2 := h.fun_pow 2
    simpa [pow_one, Nat.cast_ofNat] using h2
  have hden : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
    have h := (hasDerivAt_id z).fun_pow 2
    simpa [pow_one, Nat.cast_ofNat] using h
  have hdiv := hnum.div hden (by positivity)
  refine hdiv.congr_deriv ?_
  simp only [Work.Spaces.w]
  field_simp
  ring










private lemma c_abs_le (x : ℝ) (hx : 0 < x) : |(1 / 2 : ℝ) - 2 / (1 + x)| ≤ 3 / 2 := by
  have hp : 0 < 1 + x := by linarith
  have h2 : 2 / (1 + x) ≤ 2 := by
    rw [div_le_iff₀ hp]; linarith
  have h3 : 0 ≤ 2 / (1 + x) := by positivity
  rw [abs_le]
  constructor <;> linarith







end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.H2.HardSummandMixed =====
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


end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.HardSummandZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2


end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.H2.Hhard_slice_eq =====
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

/-! ## Auxiliary lemmas for `Hhard_slice_eq` -/


/-- If `φ` is integrable on `Iθ` and `ψ` is bounded there (and a.e. strongly measurable),
then `ψ · φ` is integrable on `Iθ`. -/
private theorem integrableOn_mul_of_bound {φ ψ : ℝ → ℝ}
    (hφ : IntegrableOn φ Work.Spaces.Iθ)
    (hψ : AEStronglyMeasurable ψ (volume.restrict Work.Spaces.Iθ)) {C : ℝ}
    (hC : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C) :
    IntegrableOn (fun θ => ψ θ * φ θ) Work.Spaces.Iθ := by
  have h0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_refl 0, by linarith [Real.pi_pos]⟩
  have hCnn : 0 ≤ C := le_trans (abs_nonneg (ψ 0)) (hC 0 h0)
  have hg : Integrable (fun θ => C * |φ θ|) (volume.restrict Work.Spaces.Iθ) :=
    hφ.abs.const_mul C
  refine hg.mono' (hψ.mul hφ.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    with θ hθ
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC θ hθ) (abs_nonneg (φ θ))








end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Bridge.dynEqF_transport_form =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge

/-- **The transport form of the profile equation.**  Writing `Φ = Φ̃ + Θ` with
`Θ = (1/(4α)) sin(2θ) L₁₂(F)` (hypotheses `h1`--`h3`, `h5`; `h4`/`h6` are definitional), the
quadratic form `UVR α F Φ = 2U(Φ)∂_θF + 2αV(Φ)D_zF - 2ℛ(Φ)F` can be put in the *transport
form* whose coefficients involve only `Φ̃ = Φ - Θ` and the two angular moments `L₁₂(F)`,
`(F,K)_{L²_θ}` of `F`:

`(1+μ)F + (1-μ)D_zF + UVR(F,Φ)`
` = ((1-μ) + L₁₂(F)·c2m(θ) + 2αV(Φ̃))·D_zF + 2U(Φ)·∂_θF`
`   + ((1+μ) - L₁₂(F)/α + sin²θ (F,K) - 2ℛ(Φ̃))·F`.

This is the pointwise algebraic core of `Work.FTS.Galerkin.IsDynEqOn` (the `∂_τF + …` display):
the `U`-slot keeps the *full* `Φ` — its `Θ`-part `2U(Θ) = -(3/(2α))sin(2θ)L₁₂(F) + (1/2)sin(2θ)(F,K)`
supplies exactly the two `∂_θF`-terms that `UVR_sub` produces — while the `V`- and `ℛ`-slots are
evaluated at the regular part `Φ̃`, with the corrections `L₁₂(F)c2m(θ)` resp.
`-L₁₂(F)/α + sin²θ(F,K)`.

Proof: `Construction.UVR_sub` (the substitution `Φ = Φ̃ + Θ`) plus the affineness of `U` in its
argument and the two evaluations of `U`/`V`/`ℛ` at `Θ`. -/
theorem dynEqF_transport_form {α μ : ℝ} (hα : 0 < α)
    {F Φ : ℝ → ℝ → ℝ} (z θ : ℝ) (hcos : Real.cos θ ≠ 0)
    (h1 : Φ z θ = Work.Construction.PhiTil α F Φ z θ + Work.Construction.Theta α F z θ)
    (h2 : Work.Spaces.pz Φ z θ = Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z θ
      + Work.Spaces.pz (Work.Construction.Theta α F) z θ)
    (h3 : Work.Spaces.pth Φ z θ = Work.Spaces.pth (Work.Construction.PhiTil α F Φ) z θ
      + Work.Spaces.pth (Work.Construction.Theta α F) z θ)
    (h5 : z * Work.Spaces.pz (Work.Construction.Theta α F) z θ
      = -(1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.FK F z) :
    (1 + μ) * F z θ + (1 - μ) * Work.Spaces.Dz F z θ + Work.Construction.UVR α F Φ z θ
      = ((1 - μ) + Work.Construction.L12 F z * Work.Construction.c2m θ
            + 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ)
          * Work.Spaces.Dz F z θ
        + (2 * Work.Construction.Uop α Φ z θ) * Work.Spaces.pth F z θ
        + ((1 + μ) - Work.Construction.L12 F z / α + Real.sin θ ^ 2 * Work.Construction.FK F z
            - 2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ) * F z θ := by
  -- `Θ z θ = (1/(4α)) sin(2θ) L₁₂(F)`: the definitional evaluation of the singular part.
  have h4 : Work.Construction.Theta α F z θ
      = (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z := rfl
  -- `∂_θ Θ = (1/(2α)) cos(2θ) L₁₂(F)`.
  have h6 := Work.Construction.pth_Theta_eq hα (F := F) z θ
  -- **The substitution** `Φ = Φ̃ + Θ`: both the `V`- and the `ℛ`-slot of the quadratic form
  -- pick up the explicit `L₁₂(F)`-corrections, while the `U`-slot is left as `U(Φ̃)`.
  have hsub := Work.Construction.UVR_sub α hα z θ hcos h1 h2 h3 h4 h5 h6
  -- `U` is affine in its argument, so `U(Φ) = U(Φ̃) + U(Θ)` along `Φ = Φ̃ + Θ`.
  have hU : Work.Construction.Uop α Φ z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
        + Work.Construction.Uop α (Work.Construction.Theta α F) z θ := by
    simp only [Work.Construction.Uop]
    rw [h1, h2]
    ring
  -- `2U(Θ) = -(3/(2α)) sin(2θ)L₁₂(F) + (1/2) sin(2θ)(F,K)`: the `U`-slot correction, whose two
  -- pieces are exactly the `∂_θF`-terms of `UVR_sub` (with opposite signs).
  have hUΘ : 2 * Work.Construction.Uop α (Work.Construction.Theta α F) z θ
      = -(3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z
        + (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z := by
    simp only [Work.Construction.Uop]
    rw [h4]
    rw [show α * z * Work.Spaces.pz (Work.Construction.Theta α F) z θ
        = α * (z * Work.Spaces.pz (Work.Construction.Theta α F) z θ) from by ring, h5]
    field_simp
    ring
  -- the `∂_θF`-slot of the target right-hand side: `2U(Φ)∂_θF` is `2U(Φ̃)∂_θF` up to exactly the
  -- two corrections produced by `UVR_sub`.
  have hpt : 2 * Work.Construction.Uop α Φ z θ * Work.Spaces.pth F z θ
      = 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
          * Work.Spaces.pth F z θ
        + (-(3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z
            + (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z)
          * Work.Spaces.pth F z θ := by
    have h2' : 2 * Work.Construction.Uop α Φ z θ
        = 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
          + (-(3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z
              + (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z) := by
      rw [hU]
      linear_combination hUΘ
    rw [h2']; ring
  rw [hsub]
  simp only [Work.Construction.UVR]
  rw [hpt]
  ring

end Work.FTS.MeridianDyn.Bridge
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.TsumLopDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open scoped Real Topology
open Filter


end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.EqcBasis =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP.Sobolev

set_option maxHeartbeats 1000000

set_option autoImplicit false


/-- A set integral over a product of closed intervals is an iterated interval integral. -/
lemma eqc_setIntegral_rect_eq {f : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (h : IntegrableOn (fun x : ℝ × ℝ => (f x) ^ 2) (Set.Icc a b ×ˢ Set.Icc c d)) :
    (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f x) ^ 2)
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (f (z, θ)) ^ 2 := by
  rw [Measure.volume_eq_prod ℝ ℝ] at h ⊢
  exact setIntegral_prod (fun x : ℝ × ℝ => (f x) ^ 2) h


end Work.FTS.StrongLWP.Sobolev
end
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.EqcProduct =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP.Sobolev

set_option maxHeartbeats 1000000

set_option autoImplicit false


/-- A product with a compactly supported cutoff has compact support. -/
lemma eqc_hasCompactSupport_mul {χ g : ℝ × ℝ → ℝ} (hχ : HasCompactSupport χ) :
    HasCompactSupport (fun x => χ x * g x) :=
  hχ.mono fun x hx => by
    simp only [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by rw [h0, zero_mul])

/-- **The second derivative of a product.**  If `χ` and `g` are twice differentiable on a
neighbourhood of `x`, then
`‖D²(χ·g)(x)‖ ≤ |χ x|·‖D²g(x)‖ + 2‖Dχ(x)‖‖Dg(x)‖ + ‖D²χ(x)‖·|g x|`.

The bound is proved by evaluating the second derivative at an arbitrary vector, which keeps the
scalar multiplications at the (single) level of `(ℝ × ℝ) →L[ℝ] ℝ`; going through the operator
norm of the second derivative directly runs into the missing `IsBoundedSMul`/`NormSMulClass`
instance on `(ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)` in this Mathlib pin. -/
lemma eqc_norm_fderiv_fderiv_mul_le {χ g : ℝ × ℝ → ℝ} {M0 M1 M2 : ℝ} {x : ℝ × ℝ}
    (hχ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ χ y ∧ DifferentiableAt ℝ (fderiv ℝ χ) y)
    (hg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ (fderiv ℝ g) y)
    (hM0 : |χ x| ≤ M0) (hM1 : ‖fderiv ℝ χ x‖ ≤ M1) (hM2 : ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ M2) :
    ‖fderiv ℝ (fderiv ℝ (fun y => χ y * g y)) x‖ ≤
      M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * |g x| := by
  have hχx := hχ.self_of_nhds
  have hgx := hg.self_of_nhds
  have hfg : fderiv ℝ (fun y => χ y * g y)
      =ᶠ[𝓝 x] (fun y => χ y • fderiv ℝ g y + g y • fderiv ℝ χ y) := by
    filter_upwards [hχ, hg] with y hy hgy
    exact fderiv_fun_mul hy.1 hgy.1
  have hd1 : DifferentiableAt ℝ (fun y => χ y • fderiv ℝ g y) x := hχx.1.smul hgx.2
  have hd2 : DifferentiableAt ℝ (fun y => g y • fderiv ℝ χ y) x := hgx.1.smul hχx.2
  have e1 : fderiv ℝ (fderiv ℝ (fun y => χ y * g y)) x
      = fderiv ℝ (fun y => χ y • fderiv ℝ g y) x
        + fderiv ℝ (fun y => g y • fderiv ℝ χ y) x := by
    rw [hfg.fderiv_eq]
    exact fderiv_add hd1 hd2
  have e2 : fderiv ℝ (fun y => χ y • fderiv ℝ g y) x
      = χ x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ χ x).smulRight (fderiv ℝ g x) :=
    fderiv_smul hχx.1 hgx.2
  have e3 : fderiv ℝ (fun y => g y • fderiv ℝ χ y) x
      = g x • fderiv ℝ (fderiv ℝ χ) x + (fderiv ℝ g x).smulRight (fderiv ℝ χ x) :=
    fderiv_smul hgx.1 hχx.2
  have hM0nn : 0 ≤ M0 := le_trans (abs_nonneg (χ x)) hM0
  have hM1nn : 0 ≤ M1 := le_trans (norm_nonneg (fderiv ℝ χ x)) hM1
  have hM2nn : 0 ≤ M2 := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ χ) x)) hM2
  have hbound : 0 ≤ M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * |g x| := by
    have h1 : 0 ≤ M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ :=
      mul_nonneg hM0nn (norm_nonneg (fderiv ℝ (fderiv ℝ g) x))
    have h2 : 0 ≤ 2 * M1 * ‖fderiv ℝ g x‖ := by positivity
    have h3 : 0 ≤ M2 * |g x| := mul_nonneg hM2nn (abs_nonneg (g x))
    linarith
  rw [ContinuousLinearMap.opNorm_le_iff hbound]
  intro h
  rw [e1, e2, e3]
  have hA : ‖χ x • ((fderiv ℝ (fderiv ℝ g) x) h)‖
      ≤ (M0 * ‖fderiv ℝ (fderiv ℝ g) x‖) * ‖h‖ := by
    calc ‖χ x • ((fderiv ℝ (fderiv ℝ g) x) h)‖
        ≤ ‖χ x‖ * ‖(fderiv ℝ (fderiv ℝ g) x) h‖ :=
          norm_smul_le (χ x) ((fderiv ℝ (fderiv ℝ g) x) h)
      _ ≤ ‖χ x‖ * (‖fderiv ℝ (fderiv ℝ g) x‖ * ‖h‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ h)
            (norm_nonneg (χ x))
      _ = (‖χ x‖ * ‖fderiv ℝ (fderiv ℝ g) x‖) * ‖h‖ := by ring
      _ ≤ (M0 * ‖fderiv ℝ (fderiv ℝ g) x‖) * ‖h‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg h)
          rw [Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right hM0 (norm_nonneg (fderiv ℝ (fderiv ℝ g) x))
  have hB : ‖(fderiv ℝ χ x h) • (fderiv ℝ g x)‖
      ≤ (M1 * ‖h‖) * ‖fderiv ℝ g x‖ := by
    calc ‖(fderiv ℝ χ x h) • (fderiv ℝ g x)‖
        ≤ ‖fderiv ℝ χ x h‖ * ‖fderiv ℝ g x‖ :=
          norm_smul_le (fderiv ℝ χ x h) (fderiv ℝ g x)
      _ ≤ (‖fderiv ℝ χ x‖ * ‖h‖) * ‖fderiv ℝ g x‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ h)
            (norm_nonneg (fderiv ℝ g x))
      _ ≤ (M1 * ‖h‖) * ‖fderiv ℝ g x‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM1 (norm_nonneg h))
            (norm_nonneg (fderiv ℝ g x))
  have hC : ‖g x • ((fderiv ℝ (fderiv ℝ χ) x) h)‖ ≤ (M2 * ‖h‖) * |g x| := by
    calc ‖g x • ((fderiv ℝ (fderiv ℝ χ) x) h)‖
        ≤ ‖g x‖ * ‖(fderiv ℝ (fderiv ℝ χ) x) h‖ :=
          norm_smul_le (g x) ((fderiv ℝ (fderiv ℝ χ) x) h)
      _ ≤ ‖g x‖ * (‖fderiv ℝ (fderiv ℝ χ) x‖ * ‖h‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ h) (norm_nonneg (g x))
      _ = ‖g x‖ * (‖h‖ * ‖fderiv ℝ (fderiv ℝ χ) x‖) := by ring
      _ ≤ |g x| * (‖h‖ * M2) := by
          refine mul_le_mul (by rw [Real.norm_eq_abs]) ?_ (by positivity)
            (abs_nonneg (g x))
          exact mul_le_mul_of_nonneg_left hM2 (norm_nonneg h)
      _ = (M2 * ‖h‖) * |g x| := by ring
  have hD : ‖(fderiv ℝ g x h) • (fderiv ℝ χ x)‖
      ≤ (M1 * ‖fderiv ℝ g x‖) * ‖h‖ := by
    calc ‖(fderiv ℝ g x h) • (fderiv ℝ χ x)‖
        ≤ ‖fderiv ℝ g x h‖ * ‖fderiv ℝ χ x‖ :=
          norm_smul_le (fderiv ℝ g x h) (fderiv ℝ χ x)
      _ ≤ (‖fderiv ℝ g x‖ * ‖h‖) * M1 :=
          mul_le_mul (ContinuousLinearMap.le_opNorm (fderiv ℝ g x) h) hM1
            (norm_nonneg (fderiv ℝ χ x))
            (mul_nonneg (norm_nonneg (fderiv ℝ g x)) (norm_nonneg h))
      _ = (M1 * ‖fderiv ℝ g x‖) * ‖h‖ := by ring
  calc ‖χ x • ((fderiv ℝ (fderiv ℝ g) x) h) + (fderiv ℝ χ x h) • (fderiv ℝ g x)
        + (g x • ((fderiv ℝ (fderiv ℝ χ) x) h) + (fderiv ℝ g x h) • (fderiv ℝ χ x))‖
      ≤ (‖χ x • ((fderiv ℝ (fderiv ℝ g) x) h)‖ + ‖(fderiv ℝ χ x h) • (fderiv ℝ g x)‖)
        + (‖g x • ((fderiv ℝ (fderiv ℝ χ) x) h)‖ + ‖(fderiv ℝ g x h) • (fderiv ℝ χ x)‖) := by
        refine le_trans (norm_add_le _ _)
          (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ ((M0 * ‖fderiv ℝ (fderiv ℝ g) x‖) * ‖h‖ + (M1 * ‖h‖) * ‖fderiv ℝ g x‖)
        + ((M2 * ‖h‖) * |g x| + (M1 * ‖fderiv ℝ g x‖) * ‖h‖) :=
        add_le_add (add_le_add hA hB) (add_le_add hC hD)
    _ = (M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * |g x|) * ‖h‖ := by
        ring

/-- On a set where `χ` vanishes (and outside which the integrand vanishes), the `L²`-norm of
`χ·g` is dominated by that of `g`. -/
lemma eqc_integral_mul_sq_le {χ g : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hχ0 : ∀ x ∉ s, χ x = 0) (hχle1 : ∀ x, χ x ≤ 1) (hχnn : ∀ x, 0 ≤ χ x)
    (hs : MeasurableSet s) (hgi : IntegrableOn (fun x => (g x) ^ 2) s) :
    ∫ x : ℝ × ℝ, (χ x * g x) ^ 2 ≤ ∫ x in s, (g x) ^ 2 := by
  have hzero : ∀ x ∉ s, (χ x * g x) ^ 2 = 0 := fun x hx => by rw [hχ0 x hx, zero_mul]; simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hgi ?_
  filter_upwards [ae_restrict_mem hs] with x hx
  have h1 : (χ x) ^ 2 ≤ 1 := by nlinarith [hχnn x, hχle1 x]
  calc (χ x * g x) ^ 2 = (χ x) ^ 2 * (g x) ^ 2 := by ring
    _ ≤ 1 * (g x) ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = (g x) ^ 2 := one_mul _

/-- The second-derivative product bound, integrated.  `χ` is a `C²` cutoff vanishing off the
closed set `s`; `g` is twice differentiable on the open set `U ⊇ s`; and `E` dominates
`‖fderiv (fderiv g)‖` on `s` and is square-integrable there (in the applications `E` is the sum
of the absolute values of the four basis entries of the second derivative, which keeps the
statement free of the `Norm`-instance diamonds of `E →L[ℝ] (E →L[ℝ] ℝ)`). -/
lemma eqc_integral_fderiv_fderiv_mul_sq_le {χ g : ℝ × ℝ → ℝ} {s U : Set (ℝ × ℝ)}
    {M0 M1 M2 : ℝ} {E : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (hsc : IsClosed s)
    (hχ0 : ∀ x ∉ s, χ x = 0)
    (hM0 : ∀ x, ‖χ x‖ ≤ M0) (hM1 : ∀ x, ‖fderiv ℝ χ x‖ ≤ M1)
    (hM2 : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ M2)
    (hU : IsOpen U) (hsU : s ⊆ U) (hgd : ∀ y ∈ U, DifferentiableAt ℝ g y)
    (hgd2 : ∀ y ∈ U, DifferentiableAt ℝ (fderiv ℝ g) y)
    (hE : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ E x)
    (hI0 : IntegrableOn (fun x => (g x) ^ 2) s)
    (hI1 : IntegrableOn (fun x => ‖fderiv ℝ g x‖ ^ 2) s)
    (hI2 : IntegrableOn (fun x => (E x) ^ 2) s) :
    ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun y => χ y * g y)) x‖ ^ 2
      ≤ 3 * (M0 ^ 2 * (∫ x in s, (E x) ^ 2)
        + (2 * M1) ^ 2 * (∫ x in s, ‖fderiv ℝ g x‖ ^ 2)
        + M2 ^ 2 * (∫ x in s, (g x) ^ 2)) := by
  have hχd : ∀ x, DifferentiableAt ℝ χ x :=
    fun x => (hχ.differentiable (by norm_num)).differentiableAt
  have hχd2 : ∀ x, DifferentiableAt ℝ (fderiv ℝ χ) x := fun x =>
    ((hχ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
  set v : ℝ × ℝ → ℝ := fun y => χ y * g y with hvdef
  have hpt : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2
      ≤ 3 * (M0 ^ 2 * (E x) ^ 2 + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + M2 ^ 2 * (g x) ^ 2) := by
    intro x hx
    have hχev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ χ y ∧ DifferentiableAt ℝ (fderiv ℝ χ) y :=
      Eventually.of_forall fun y => ⟨hχd y, hχd2 y⟩
    have hgev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ (fderiv ℝ g) y := by
      filter_upwards [hU.mem_nhds (hsU hx)] with y hy
      exact ⟨hgd y hy, hgd2 y hy⟩
    have hb := eqc_norm_fderiv_fderiv_mul_le (χ := χ) (g := g) (x := x) hχev hgev
      (hM0 x) (hM1 x) (hM2 x)
    have hb' : ‖fderiv ℝ (fderiv ℝ v) x‖
        ≤ M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * ‖g x‖ := hb
    have hM0nn : 0 ≤ M0 := le_trans (abs_nonneg (χ x)) (hM0 x)
    have hM1nn : 0 ≤ M1 := le_trans (norm_nonneg (fderiv ℝ χ x)) (hM1 x)
    have hM2nn : 0 ≤ M2 := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ χ) x)) (hM2 x)
    have hstep : M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * ‖g x‖
        ≤ M0 * E x + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * ‖g x‖ :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hE x hx) hM0nn) le_rfl) le_rfl
    have hnn1 : 0 ≤ M0 * ‖fderiv ℝ (fderiv ℝ g) x‖ + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * ‖g x‖ := by
      positivity
    have hsq := pow_le_pow_left₀ hnn1 hstep 2
    have hsq2 := pow_le_pow_left₀ (norm_nonneg (fderiv ℝ (fderiv ℝ v) x)) hb' 2
    refine (hsq2.trans hsq).trans ?_
    calc (M0 * E x + 2 * M1 * ‖fderiv ℝ g x‖ + M2 * ‖g x‖) ^ 2
        ≤ 3 * ((M0 * E x) ^ 2 + (2 * M1 * ‖fderiv ℝ g x‖) ^ 2 + (M2 * ‖g x‖) ^ 2) :=
          eqc_sq_add3_le _ _ _
      _ = 3 * (M0 ^ 2 * (E x) ^ 2 + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + M2 ^ 2 * (g x) ^ 2) := by
          simp only [mul_pow, Real.norm_eq_abs, sq_abs]
  have hvzero : ∀ x ∉ s, fderiv ℝ (fderiv ℝ v) x = 0 := fun x hx =>
    (eqc_fderiv_fderiv_eq_zero_of_open hsc.isOpen_compl (fun y hy => by
      simp only [hvdef]; rw [hχ0 y hy, zero_mul]) hx).2
  have hmain : ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2
      = ∫ x in s, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [hvzero x hx, ContinuousLinearMap.opNorm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)])).symm
  rw [hmain]
  have hFA : IntegrableOn (fun x => M0 ^ 2 * (E x) ^ 2) s := hI2.const_mul _
  have hFB : IntegrableOn (fun x => (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2) s := hI1.const_mul _
  have hFC : IntegrableOn (fun x => M2 ^ 2 * (g x) ^ 2) s := hI0.const_mul _
  have hIntBig : IntegrableOn (fun x => 3 * (M0 ^ 2 * (E x) ^ 2
      + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + M2 ^ 2 * (g x) ^ 2)) s :=
    (hFA.add hFB).add hFC |>.const_mul 3
  have h1 : (∫ x in s, M0 ^ 2 * (E x) ^ 2
        + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + M2 ^ 2 * (g x) ^ 2)
      = (∫ x in s, M0 ^ 2 * (E x) ^ 2 + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2)
        + (∫ x in s, M2 ^ 2 * (g x) ^ 2) :=
    integral_add (hFA.add hFB) hFC
  have h2 : (∫ x in s, M0 ^ 2 * (E x) ^ 2 + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2)
      = (∫ x in s, M0 ^ 2 * (E x) ^ 2)
        + (∫ x in s, (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2) :=
    integral_add hFA hFB
  have h3 : (∫ x in s, M0 ^ 2 * (E x) ^ 2) = M0 ^ 2 * (∫ x in s, (E x) ^ 2) :=
    integral_const_mul _ _
  have h4 : (∫ x in s, (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2)
      = (2 * M1) ^ 2 * (∫ x in s, ‖fderiv ℝ g x‖ ^ 2) := integral_const_mul _ _
  have h5 : (∫ x in s, M2 ^ 2 * (g x) ^ 2) = M2 ^ 2 * (∫ x in s, (g x) ^ 2) :=
    integral_const_mul _ _
  have hsplit : (∫ x in s, M0 ^ 2 * (E x) ^ 2
        + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + M2 ^ 2 * (g x) ^ 2)
      = M0 ^ 2 * (∫ x in s, (E x) ^ 2)
        + (2 * M1) ^ 2 * (∫ x in s, ‖fderiv ℝ g x‖ ^ 2)
        + M2 ^ 2 * (∫ x in s, (g x) ^ 2) := by
    rw [h1, h2, h3, h4, h5]
  calc ∫ x in s, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2
      ≤ ∫ x in s, 3 * (M0 ^ 2 * (E x) ^ 2
          + (2 * M1) ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + M2 ^ 2 * (g x) ^ 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hIntBig
          (ae_restrict_of_forall_mem hsc.measurableSet hpt)
    _ = 3 * (M0 ^ 2 * (∫ x in s, (E x) ^ 2)
          + (2 * M1) ^ 2 * (∫ x in s, ‖fderiv ℝ g x‖ ^ 2)
          + M2 ^ 2 * (∫ x in s, (g x) ^ 2)) := by
        rw [integral_const_mul, hsplit]

end Work.FTS.StrongLWP.Sobolev
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.AK6.hkSq_le_of_integrand_le6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `HkSq` from a pointwise bound on the `ℋ⁶`-integrand

If the `ℋ⁶`-integrand of `f` is dominated on the closed quadrant by the product of the radial
factor `1/(1+z)²` with the two angular profiles `A·sin(2θ)^{-η}` and
`B·(α+sin 2θ)²·sin(2θ)^{2α/5-γ(α)}`, then `|f|²_{ℋ⁶} ≤ 2(A·10⁴ + B·700)`.

This is the pointwise-to-`HkSq` bookkeeping: the two angular profiles have `θ`-integrals bounded
by `10⁴` resp. `700` uniformly in `α ∈ (0,1]` (`Work.Elliptic.WtoH_Angular`), while the radial
factor has `z`-integral `1 ≤ 2` over `Iz = [0,∞)` (`Work.Elliptic.WtoH_IntZ`).  The factors
multiply to `2(A·10⁴ + B·700)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.AK6

set_option autoImplicit false

theorem hkSq_le_of_integrand_le6 {α A B : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) {f : ℝ → ℝ → ℝ} (hpt : ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ), θ ∈ Work.Spaces.Iθ → Work.Spaces.HkIntegrand α 6 f z θ ≤ (1 / (1 + z) ^ 2) * (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + B * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) : Work.Spaces.HkSq α 6 f ≤ 2 * (A * 10 ^ 4 + B * 700) := by
  -- Integrability of the two angular profiles on `Iθ`.
  have hS1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)).1
  have hS2 : IntegrableOn (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    Work.Spaces.integrableOn_angular_weight' hα hα1
  -- The uniform angular integral bound.
  have hAng : (∫ θ in Work.Spaces.Iθ, (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + B * ((α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))))
      ≤ A * 10 ^ 4 + B * 700 :=
    Work.Elliptic.WtoH_Angular (α := α) hα hα1 hA hB
  -- The `θ`-slices of the `ℋ⁶`-integrand.
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
        ≤ (1 / (1 + z) ^ 2) * (A * 10 ^ 4 + B * 700) := by
    intro z hz
    have hmaj : Integrable (fun θ : ℝ => (1 / (1 + z) ^ 2)
        * (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + B * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))))
        (volume.restrict Work.Spaces.Iθ) :=
      ((hS1.const_mul A).add (hS2.const_mul B)).const_mul (1 / (1 + z) ^ 2)
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α 6 f z θ ≤ (1 / (1 + z) ^ 2)
          * (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + B * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
      ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (1 / (1 + z) ^ 2)
            * (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + B * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ) hmaj hae
      _ = (1 / (1 + z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + B * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ (1 / (1 + z) ^ 2) * (A * 10 ^ 4 + B * 700) :=
          mul_le_mul_of_nonneg_left hAng (by positivity)
  -- The radial integral.
  set K : ℝ := A * 10 ^ 4 + B * 700 with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; nlinarith [hA, hB]
  have hI : IntegrableOn (fun z : ℝ => (1 / (1 + z) ^ 2) * K) Work.Spaces.Iz :=
    Work.Elliptic.WtoH_IntZ.1.mul_const K
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 f z θ) ≤ 2 * K := by
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 f z θ)
        ≤ ∫ z in Work.Spaces.Iz, (1 / (1 + z) ^ 2) * K :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun z =>
              integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ)
            hI (ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => by
              simpa only [hKdef] using hinner z hz))
      _ = (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) * K := by
          rw [MeasureTheory.integral_mul_const]
      _ ≤ 2 * K := mul_le_mul_of_nonneg_right Work.Elliptic.WtoH_IntZ.2 hKnn
  change (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 f z θ) ≤ 2 * (A * 10 ^ 4 + B * 700)
  rw [← hKdef]
  exact houter

end Work.FTS.StrongPersist.AK6
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Phi_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology MeasureTheory
open Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-! ## The box analysis: slices, and continuity of the two `z`-derivatives -/

/-- **`C²` within a box gives the `z`-calculus up to the boundary angles.**

For `F` jointly `C²` on the closed box `[a,b] × [0,π/2]` (`a < b`) and every
radial point `z ∈ (a,b)` interior to the box:

* the `z`-slice `s ↦ F s θ` is differentiable at `z` with derivative the plain
  partial `∂_z F z θ`, for **every** angle `θ ∈ [0,π/2]` (including the two
  boundary angles, where only the one-sided information of `BoxReg` is
  available — the derivative still exists because the curve `s ↦ (s,θ)` stays
  inside the box for `s` near `z`);
* the same for the slice of `∂_z F`, with derivative `∂_z² F z θ`;
* `∂_z F` and `∂_z² F` are jointly continuous on `(a,b) × [0,π/2]`. -/
theorem boxReg_facts {F : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h : ContDiffOn ℝ 2 (Function.uncurry F) (Set.Icc a b ×ˢ Set.Icc 0 (π / 2))) :
    (∀ z ∈ Set.Ioo a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivAt (fun s => F s θ) (Work.Spaces.pz F z θ) z) ∧
    (∀ z ∈ Set.Ioo a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivAt (fun s => Work.Spaces.pz F s θ) (Work.Spaces.pzIter 2 F z θ) z) ∧
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2)
      (Set.Ioo a b ×ˢ Set.Icc 0 (π / 2)) ∧
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 F p.1 p.2)
      (Set.Ioo a b ×ˢ Set.Icc 0 (π / 2)) := by
  set S : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc 0 (π / 2) with hS
  have hSbox : UniqueDiffOn ℝ S := by
    rw [hS]
    exact (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc (by linarith [Real.pi_pos]))
  -- `G` is the partial `∂_z F`, as read off from the Fréchet derivative within the box
  set G : ℝ × ℝ → ℝ := fun p => (fderivWithin ℝ (Function.uncurry F) S p) (1, 0) with hG
  have hfd : ContDiffOn ℝ 1 (fderivWithin ℝ (Function.uncurry F) S) S :=
    h.fderivWithin hSbox (by norm_num)
  have hGC1 : ContDiffOn ℝ 1 G S := hfd.clm_apply contDiffOn_const
  have hcontG : ContinuousOn G S := hGC1.continuousOn
  have hsub : Set.Ioo a b ×ˢ Set.Icc 0 (π / 2) ⊆ S := by
    intro p hp
    rw [hS]
    exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, hp.2⟩
  have hmem_of : ∀ {z θ : ℝ}, z ∈ Set.Ioo a b → θ ∈ Set.Icc 0 (π / 2) →
      ∀ᶠ s in 𝓝 z, (s, θ) ∈ S := by
    intro z θ hz hθ
    exact Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hz) (fun s hs => hsub ⟨hs, hθ⟩)
  -- `∂_z² F` as the derivative of the first partial within the box
  have hcomp : ContinuousOn (fun p : ℝ × ℝ => (fderivWithin ℝ G S p) (1, 0)) S :=
    (hGC1.continuousOn_fderivWithin hSbox le_rfl).clm_apply continuousOn_const
  -- the pointwise identity `∂_z F = G` at every point of the box with interior radial coordinate
  have hpt : ∀ p ∈ Set.Ioo a b ×ˢ Set.Icc 0 (π / 2), Work.Spaces.pz F p.1 p.2 = G p := by
    intro p hp
    have hpS : p ∈ S := hsub hp
    have hd : HasFDerivWithinAt (Function.uncurry F)
        (fderivWithin ℝ (Function.uncurry F) S p) S p :=
      ((h p hpS).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    have h2 := hd.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)) (hmem_of hp.1 hp.2)
    have h3 : HasDerivAt (fun s => F s p.2)
        ((fderivWithin ℝ (Function.uncurry F) S p) (1, 0)) p.1 := by
      simpa [Function.comp_def, Function.uncurry] using h2
    rw [Work.Spaces.pz, hG]
    exact h3.deriv
  have hslice : ∀ z ∈ Set.Ioo a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivAt (fun s => F s θ) (Work.Spaces.pz F z θ) z := by
    intro z hz θ hθ
    rw [hpt (z, θ) ⟨hz, hθ⟩]
    have hzS : (z, θ) ∈ S := hsub ⟨hz, hθ⟩
    have hd : HasFDerivWithinAt (Function.uncurry F)
        (fderivWithin ℝ (Function.uncurry F) S (z, θ)) S (z, θ) :=
      ((h (z, θ) hzS).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    have h2 := hd.comp_hasDerivAt z
      ((hasDerivAt_id z).prodMk (hasDerivAt_const z θ)) (hmem_of hz hθ)
    simpa [Function.comp_def, Function.uncurry, hG] using h2
  have hslicepz : ∀ z ∈ Set.Ioo a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivAt (fun s => Work.Spaces.pz F s θ) ((fderivWithin ℝ G S (z, θ)) (1, 0)) z := by
    intro z hz θ hθ
    have hzS : (z, θ) ∈ S := hsub ⟨hz, hθ⟩
    have hd : HasFDerivWithinAt G (fderivWithin ℝ G S (z, θ)) S (z, θ) :=
      ((hGC1 (z, θ) hzS).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    have h2 := hd.comp_hasDerivAt z
      ((hasDerivAt_id z).prodMk (hasDerivAt_const z θ)) (hmem_of hz hθ)
    have heq : (fun s => Work.Spaces.pz F s θ) =ᶠ[𝓝 z] (fun s => G (s, θ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hz] with s hs
      exact hpt (s, θ) ⟨hs, hθ⟩
    simpa [Function.comp_def] using h2.congr_of_eventuallyEq heq
  have hslicepz' : ∀ z ∈ Set.Ioo a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivAt (fun s => Work.Spaces.pz F s θ) (Work.Spaces.pzIter 2 F z θ) z := by
    intro z hz θ hθ
    have hC : (fderivWithin ℝ G S (z, θ)) (1, 0) = Work.Spaces.pzIter 2 F z θ := by
      rw [← (hslicepz z hz θ hθ).deriv]; rfl
    exact hC ▸ hslicepz z hz θ hθ
  refine ⟨hslice, hslicepz', ?_, ?_⟩
  · exact (hcontG.mono hsub).congr (fun p hp => hpt p hp)
  · refine (hcomp.mono hsub).congr (fun p hp => ?_)
    exact (hslicepz p.1 hp.1 p.2 hp.2).deriv

/-! ## The two derivatives of `Φ` and `Ψ` -/

/-- **Differentiation of the energy functionals.**  For `δ` jointly `C²` on the closed box
`[a,b] × [0,π/2]` (`0 < a < b`) and every `z ∈ (a,b)`:

* `s ↦ ∫_θ (δ s θ)²` has derivative `2 ∫_θ δ z θ ∂_z δ z θ` at `z`;
* `s ↦ 2 ∫_θ δ s θ ∂_z δ s θ` has derivative
  `2 ∫_θ ((∂_z δ z θ)² + δ z θ ∂_z² δ z θ)` at `z`. -/
theorem hasDerivAt_PhiPsi_box {δ : ℝ → ℝ → ℝ} {a b z : ℝ} (hab : a < b)
    (hδ : ContDiffOn ℝ 2 (Function.uncurry δ) (Set.Icc a b ×ˢ Set.Icc 0 (π / 2)))
    (hz : z ∈ Set.Ioo a b) :
    HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, (δ s θ) ^ 2)
        (2 * ∫ θ in Work.Spaces.Iθ, δ z θ * Work.Spaces.pz δ z θ) z ∧
      HasDerivAt (fun s => 2 * ∫ θ in Work.Spaces.Iθ, δ s θ * Work.Spaces.pz δ s θ)
        (2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pz δ z θ) ^ 2 + δ z θ * Work.Spaces.pzIter 2 δ z θ) z := by
  obtain ⟨hsl, hslpz, hpc, hp2c⟩ := boxReg_facts hab hδ
  have hV : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have hsub : Set.Ioo a b ×ˢ Work.Spaces.Iθ ⊆ Set.Icc a b ×ˢ Set.Icc 0 (π / 2) := by
    intro p hp
    exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, hp.2⟩
  have hcδ : ContinuousOn (fun p : ℝ × ℝ => δ p.1 p.2) (Set.Ioo a b ×ˢ Work.Spaces.Iθ) :=
    hδ.continuousOn.mono hsub
  have hcpz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz δ p.1 p.2)
      (Set.Ioo a b ×ˢ Work.Spaces.Iθ) := hpc
  have hcp2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 δ p.1 p.2)
      (Set.Ioo a b ×ˢ Work.Spaces.Iθ) := hp2c
  -- the two `z`-derivative identities
  have hval1 : (∫ θ in Work.Spaces.Iθ, 2 * δ z θ * Work.Spaces.pz δ z θ)
      = 2 * ∫ θ in Work.Spaces.Iθ, δ z θ * Work.Spaces.pz δ z θ := by
    rw [show (fun θ => 2 * δ z θ * Work.Spaces.pz δ z θ)
        = (fun θ => 2 * (δ z θ * Work.Spaces.pz δ z θ)) from by funext θ; ring]
    exact MeasureTheory.integral_const_mul 2 _
  have hfun2 : (fun s => ∫ θ in Work.Spaces.Iθ, 2 * δ s θ * Work.Spaces.pz δ s θ)
      = fun s => 2 * ∫ θ in Work.Spaces.Iθ, δ s θ * Work.Spaces.pz δ s θ := by
    funext s
    rw [show (fun θ => 2 * δ s θ * Work.Spaces.pz δ s θ)
        = (fun θ => 2 * (δ s θ * Work.Spaces.pz δ s θ)) from by funext θ; ring]
    exact MeasureTheory.integral_const_mul 2 _
  have hval2 : (∫ θ in Work.Spaces.Iθ, 2 * (Work.Spaces.pz δ z θ ^ 2
      + δ z θ * Work.Spaces.pzIter 2 δ z θ))
      = 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz δ z θ ^ 2
          + δ z θ * Work.Spaces.pzIter 2 δ z θ) := MeasureTheory.integral_const_mul 2 _
  constructor
  · have h1 : ContinuousOn (Function.uncurry (fun s θ => (δ s θ) ^ 2))
        (Set.Ioo a b ×ˢ Work.Spaces.Iθ) := hcδ.pow 2
    have h2 : ContinuousOn (Function.uncurry (fun s θ => 2 * δ s θ * Work.Spaces.pz δ s θ))
        (Set.Ioo a b ×ˢ Work.Spaces.Iθ) :=
      (continuousOn_const.mul hcδ).mul hcpz
    have h3 : ∀ θ ∈ Work.Spaces.Iθ, ∀ s ∈ Set.Ioo a b,
        HasDerivAt (fun s => (δ s θ) ^ 2) (2 * δ s θ * Work.Spaces.pz δ s θ) s := by
      intro θ hθ s hs
      convert (hsl s hs θ hθ).pow 2 using 1
      ring
    have hkey := Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt
      (g := fun s θ => (δ s θ) ^ 2)
      (g' := fun s θ => 2 * δ s θ * Work.Spaces.pz δ s θ)
      (V := Set.Ioo a b) hV hz h1 h2 h3
    rw [hval1] at hkey
    exact hkey
  · have h1 : ContinuousOn (Function.uncurry (fun s θ => 2 * δ s θ * Work.Spaces.pz δ s θ))
        (Set.Ioo a b ×ˢ Work.Spaces.Iθ) :=
      (continuousOn_const.mul hcδ).mul hcpz
    have h2 : ContinuousOn (Function.uncurry (fun s θ => 2 * (Work.Spaces.pz δ s θ ^ 2
        + δ s θ * Work.Spaces.pzIter 2 δ s θ)))
        (Set.Ioo a b ×ˢ Work.Spaces.Iθ) :=
      continuousOn_const.mul ((hcpz.pow 2).add (hcδ.mul hcp2))
    have h3 : ∀ θ ∈ Work.Spaces.Iθ, ∀ s ∈ Set.Ioo a b,
        HasDerivAt (fun s => 2 * δ s θ * Work.Spaces.pz δ s θ)
          (2 * (Work.Spaces.pz δ s θ ^ 2 + δ s θ * Work.Spaces.pzIter 2 δ s θ)) s := by
      intro θ hθ s hs
      have h1' : HasDerivAt (fun s' => δ s' θ) (Work.Spaces.pz δ s θ) s := hsl s hs θ hθ
      have h2' : HasDerivAt (fun s' => Work.Spaces.pz δ s' θ) (Work.Spaces.pzIter 2 δ s θ) s :=
        hslpz s hs θ hθ
      have hmul := (h1'.const_mul 2).mul h2'
      convert hmul using 1
      ring
    have hkey := Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt
      (g := fun s θ => 2 * δ s θ * Work.Spaces.pz δ s θ)
      (g' := fun s θ => 2 * (Work.Spaces.pz δ s θ ^ 2 + δ s θ * Work.Spaces.pzIter 2 δ s θ))
      (V := Set.Ioo a b) hV hz h1 h2 h3
    rw [hfun2, hval2] at hkey
    exact hkey

/-- The derivative of the energy `Φ δ = ∫_θ δ²` and of the pairing `2 ∫_θ δ ∂_z δ`, for
box-regular data and radial points `z > 0`. -/
theorem Phi_deriv {δ : ℝ → ℝ → ℝ} (hbox : Work.FTS_EllLimOK.BoxReg δ) :
    (∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, (δ s θ) ^ 2)
      (2 * ∫ θ in Work.Spaces.Iθ, δ z θ * Work.Spaces.pz δ z θ) z) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s => 2 * ∫ θ in Work.Spaces.Iθ, δ s θ * Work.Spaces.pz δ s θ)
      (2 * ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pz δ z θ) ^ 2 + δ z θ * Work.Spaces.pzIter 2 δ z θ) z) := by
  constructor
  · intro z hz
    have hzpos : 0 < z := hz
    have hab : z / 2 < 2 * z := by linarith
    have hz' : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
    exact (hasDerivAt_PhiPsi_box hab (hbox (z / 2) (2 * z) (by linarith) (le_of_lt hab)) hz').1
  · intro z hz
    have hzpos : 0 < z := hz
    have hab : z / 2 < 2 * z := by linarith
    have hz' : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
    exact (hasDerivAt_PhiPsi_box hab (hbox (z / 2) (2 * z) (by linarith) (le_of_lt hab)) hz').2

end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.jet_fderiv_partial_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

set_option autoImplicit false

/-! ## The Fréchet derivative of a two-variable function

For `g : ℝ → ℝ → ℝ` with `F = Function.uncurry g` differentiable at `(a,b)`, the Fréchet
derivative of `F` at `(a,b)` is the continuous linear functional `(u,v) ↦ u ∂_z g + v ∂_θ g`,
i.e. `ellCop (pz g a b) (pth g a b)` of `BoxRegAux.Defs`.  This is the linear-algebraic
counterpart of `Work.Spaces.pz_eq_fderiv` / `pth_eq_fderiv` (which identify the two partials
with the evaluations of `fderiv` on `(1,0)` and `(0,1)`). -/

theorem fderiv_uncurry_eq_ellCop {g : ℝ → ℝ → ℝ} {a b : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry g) (a, b)) :
    fderiv ℝ (Function.uncurry g) (a, b)
      = Work.FTS_EllLimOK.ellCop (Work.Spaces.pz g a b) (Work.Spaces.pth g a b) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h1 : fderiv ℝ (Function.uncurry g) (a, b) ((1 : ℝ), (0 : ℝ)) = Work.Spaces.pz g a b :=
    (Work.Spaces.pz_eq_fderiv h).symm
  have h2 : fderiv ℝ (Function.uncurry g) (a, b) ((0 : ℝ), (1 : ℝ)) = Work.Spaces.pth g a b :=
    (Work.Spaces.pth_eq_fderiv h).symm
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  show fderiv ℝ (Function.uncurry g) (a, b) v = _
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, h1, h2, Work.FTS_EllLimOK.ellCop_apply]
  simp only [smul_eq_mul]

/-- **The operator norm of a first-order jet.**  If the Fréchet derivative of `F : ℝ × ℝ → ℝ`
at `x` is `ellCop A B`, then the norm of `iteratedFDeriv ℝ 1 F x` is at most `|A| + |B|`
(in fact it is equal, the norm on `ℝ × ℝ` being the sup norm). -/
theorem norm_iterDF1_le {F : ℝ × ℝ → ℝ} {x : ℝ × ℝ} {A B : ℝ}
    (hfd : fderiv ℝ F x = Work.FTS_EllLimOK.ellCop A B) :
    ‖iteratedFDeriv ℝ 1 F x‖ ≤ |A| + |B| := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  rw [iteratedFDeriv_one_apply, hfd, Real.norm_eq_abs, Fin.prod_univ_one]
  simp only [Work.FTS_EllLimOK.ellCop_apply]
  have h1 : |(m 0).1| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_fst_le (m 0)
  have h2 : |(m 0).2| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_snd_le (m 0)
  calc |(m 0).1 * A + (m 0).2 * B|
      ≤ |(m 0).1 * A| + |(m 0).2 * B| := abs_add_le _ _
    _ = |(m 0).1| * |A| + |(m 0).2| * |B| := by rw [abs_mul, abs_mul]
    _ ≤ ‖m 0‖ * |A| + ‖m 0‖ * |B| :=
        add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg A))
          (mul_le_mul_of_nonneg_right h2 (abs_nonneg B))
    _ = (|A| + |B|) * ‖m 0‖ := by ring

/-- **The operator norm of a second-order jet.**  If the second Fréchet derivative of
`F : ℝ × ℝ → ℝ` at `x` is the curried bilinear map with the four second partials `A2 B2 C2 D2`
(the `(∂_z∂_z, ∂_θ∂_z, ∂_z∂_θ, ∂_θ∂_θ)` entries), then the norm of `iteratedFDeriv ℝ 2 F x` is
at most the sum of their absolute values. -/
theorem norm_iterDF2_le {F : ℝ × ℝ → ℝ} {x : ℝ × ℝ} {A2 B2 C2 D2 : ℝ}
    (hfd2 : fderiv ℝ (fderiv ℝ F) x
      = Work.FTS_EllLimOK.copBilin.comp ((Work.FTS_EllLimOK.ellCop A2 B2).prod
          (Work.FTS_EllLimOK.ellCop C2 D2))) :
    ‖iteratedFDeriv ℝ 2 F x‖ ≤ |A2| + |B2| + |C2| + |D2| := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  rw [iteratedFDeriv_two_apply, hfd2, Real.norm_eq_abs, Fin.prod_univ_two]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    Work.FTS_EllLimOK.copBilin_apply, Work.FTS_EllLimOK.ellCop_apply]
  have hh1 : |(m 0).1| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_fst_le (m 0)
  have hh2 : |(m 0).2| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_snd_le (m 0)
  have hk1 : |(m 1).1| ≤ ‖m 1‖ := by simpa [Real.norm_eq_abs] using norm_fst_le (m 1)
  have hk2 : |(m 1).2| ≤ ‖m 1‖ := by simpa [Real.norm_eq_abs] using norm_snd_le (m 1)
  have hN1 : (0 : ℝ) ≤ ‖m 1‖ := norm_nonneg _
  have hX : |(m 0).1 * A2 + (m 0).2 * B2| ≤ ‖m 0‖ * (|A2| + |B2|) := by
    calc |(m 0).1 * A2 + (m 0).2 * B2|
        ≤ |(m 0).1 * A2| + |(m 0).2 * B2| := abs_add_le _ _
      _ = |(m 0).1| * |A2| + |(m 0).2| * |B2| := by rw [abs_mul, abs_mul]
      _ ≤ ‖m 0‖ * |A2| + ‖m 0‖ * |B2| :=
          add_le_add (mul_le_mul_of_nonneg_right hh1 (abs_nonneg A2))
            (mul_le_mul_of_nonneg_right hh2 (abs_nonneg B2))
      _ = ‖m 0‖ * (|A2| + |B2|) := by ring
  have hY : |(m 0).1 * C2 + (m 0).2 * D2| ≤ ‖m 0‖ * (|C2| + |D2|) := by
    calc |(m 0).1 * C2 + (m 0).2 * D2|
        ≤ |(m 0).1 * C2| + |(m 0).2 * D2| := abs_add_le _ _
      _ = |(m 0).1| * |C2| + |(m 0).2| * |D2| := by rw [abs_mul, abs_mul]
      _ ≤ ‖m 0‖ * |C2| + ‖m 0‖ * |D2| :=
          add_le_add (mul_le_mul_of_nonneg_right hh1 (abs_nonneg C2))
            (mul_le_mul_of_nonneg_right hh2 (abs_nonneg D2))
      _ = ‖m 0‖ * (|C2| + |D2|) := by ring
  have e1 : |(m 1).1 * ((m 0).1 * A2 + (m 0).2 * B2)|
      ≤ ‖m 1‖ * (‖m 0‖ * (|A2| + |B2|)) :=
    le_trans (le_of_eq (abs_mul _ _)) (mul_le_mul hk1 hX (abs_nonneg _) hN1)
  have e2 : |(m 1).2 * ((m 0).1 * C2 + (m 0).2 * D2)|
      ≤ ‖m 1‖ * (‖m 0‖ * (|C2| + |D2|)) :=
    le_trans (le_of_eq (abs_mul _ _)) (mul_le_mul hk2 hY (abs_nonneg _) hN1)
  calc |(m 1).1 * ((m 0).1 * A2 + (m 0).2 * B2)
        + (m 1).2 * ((m 0).1 * C2 + (m 0).2 * D2)|
      ≤ |(m 1).1 * ((m 0).1 * A2 + (m 0).2 * B2)|
        + |(m 1).2 * ((m 0).1 * C2 + (m 0).2 * D2)| := abs_add_le _ _
    _ ≤ ‖m 1‖ * (‖m 0‖ * (|A2| + |B2|)) + ‖m 1‖ * (‖m 0‖ * (|C2| + |D2|)) :=
        add_le_add e1 e2
    _ = (|A2| + |B2| + |C2| + |D2|) * (‖m 0‖ * ‖m 1‖) := by ring

/-- **The norm of the first two iterated Fréchet derivatives of a curried function is bounded
by the sums of the absolute values of its partial derivatives.**

For `f : ℝ → ℝ → ℝ` which is `C²` at `(z,θ)`, the operator norm of `iteratedFDeriv ℝ 1`
of `Function.uncurry f` at `(z,θ)` is at most `|∂_z f| + |∂_θ f|` (the norm on `ℝ × ℝ` is the
sup norm, so this is sharp), and the operator norm of `iteratedFDeriv ℝ 2` is at most the sum
of the absolute values of the four second-order partials `∂_z∂_z f`, `∂_θ∂_z f`,
`∂_z∂_θ f`, `∂_θ∂_θ f`. -/
theorem jet_fderiv_partial_bound {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hsm : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    ‖iteratedFDeriv ℝ 1 (Function.uncurry f) (z, θ)‖
        ≤ |Work.Spaces.pz f z θ| + |Work.Spaces.pth f z θ| ∧
      ‖iteratedFDeriv ℝ 2 (Function.uncurry f) (z, θ)‖
        ≤ |Work.Spaces.pz (Work.Spaces.pz f) z θ| + |Work.Spaces.pth (Work.Spaces.pz f) z θ|
          + |Work.Spaces.pz (Work.Spaces.pth f) z θ| + |Work.Spaces.pth (Work.Spaces.pth f) z θ| := by
  refine ⟨?_, ?_⟩
  · exact norm_iterDF1_le (fderiv_uncurry_eq_ellCop (g := f) (hsm.differentiableAt (by norm_num)))
  · -- an open neighbourhood of `(z,θ)` on which `Function.uncurry f` is `C²`
    have hsmU : ContDiffWithinAt ℝ 2 (Function.uncurry f) Set.univ (z, θ) := hsm
    obtain ⟨u, hu_open, hu_mem, hu_cd⟩ :=
      hsmU.contDiffOn' (le_refl (2 : WithTop ℕ∞)) (by intro h; simp at h)
    have hu_eq : insert (z, θ) Set.univ ∩ u = u := by ext x; simp
    rw [hu_eq] at hu_cd
    have hdiff_u : ∀ q ∈ u, DifferentiableAt ℝ (Function.uncurry f) q := fun q hq =>
      (hu_cd.contDiffAt (hu_open.mem_nhds hq)).differentiableAt (by norm_num)
    have h_ev_pz : Function.uncurry (Work.Spaces.pz f) =ᶠ[𝓝 (z, θ)]
        fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry f) q (1, 0) := by
      filter_upwards [hu_open.mem_nhds hu_mem] with q hq
      exact Work.Spaces.pz_eq_fderiv (hdiff_u q hq)
    have h_ev_pth : Function.uncurry (Work.Spaces.pth f) =ᶠ[𝓝 (z, θ)]
        fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry f) q (0, 1) := by
      filter_upwards [hu_open.mem_nhds hu_mem] with q hq
      exact Work.Spaces.pth_eq_fderiv (hdiff_u q hq)
    have hdF1 : ContDiffAt ℝ 1 (fderiv ℝ (Function.uncurry f)) (z, θ) :=
      hsm.fderiv_right (m := 1) (by norm_num)
    have hdiffF1 : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (z, θ) :=
      hdF1.differentiableAt (by norm_num)
    have hdA : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz f)) (z, θ) :=
      (hdiffF1.clm_apply (differentiableAt_const ((1 : ℝ), (0 : ℝ)))).congr_of_eventuallyEq
        h_ev_pz
    have hdB : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth f)) (z, θ) :=
      (hdiffF1.clm_apply (differentiableAt_const ((0 : ℝ), (1 : ℝ)))).congr_of_eventuallyEq
        h_ev_pth
    have hA : HasFDerivAt (fun q : ℝ × ℝ => Work.Spaces.pz f q.1 q.2)
        (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
          (Work.Spaces.pth (Work.Spaces.pz f) z θ)) (z, θ) :=
      hdA.hasFDerivAt.congr_fderiv (fderiv_uncurry_eq_ellCop (g := Work.Spaces.pz f) hdA)
    have hB : HasFDerivAt (fun q : ℝ × ℝ => Work.Spaces.pth f q.1 q.2)
        (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
          (Work.Spaces.pth (Work.Spaces.pth f) z θ)) (z, θ) :=
      hdB.hasFDerivAt.congr_fderiv (fderiv_uncurry_eq_ellCop (g := Work.Spaces.pth f) hdB)
    have hg_ev : fderiv ℝ (Function.uncurry f) =ᶠ[𝓝 (z, θ)]
        fun q : ℝ × ℝ => Work.FTS_EllLimOK.copBilin
          (Work.Spaces.pz f q.1 q.2, Work.Spaces.pth f q.1 q.2) := by
      filter_upwards [hu_open.mem_nhds hu_mem] with q hq
      rw [fderiv_uncurry_eq_ellCop (g := f) (hdiff_u q hq), Work.FTS_EllLimOK.copBilin_apply]
    have hpair : HasFDerivAt
        (fun q : ℝ × ℝ => (Work.Spaces.pz f q.1 q.2, Work.Spaces.pth f q.1 q.2))
        ((Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
            (Work.Spaces.pth (Work.Spaces.pz f) z θ)).prod
          (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
            (Work.Spaces.pth (Work.Spaces.pth f) z θ))) (z, θ) := hA.prodMk hB
    have hcomp : HasFDerivAt (fun q : ℝ × ℝ => Work.FTS_EllLimOK.copBilin
        (Work.Spaces.pz f q.1 q.2, Work.Spaces.pth f q.1 q.2))
        (Work.FTS_EllLimOK.copBilin.comp
          ((Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
              (Work.Spaces.pth (Work.Spaces.pz f) z θ)).prod
            (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
              (Work.Spaces.pth (Work.Spaces.pth f) z θ)))) (z, θ) :=
      (ContinuousLinearMap.hasFDerivAt Work.FTS_EllLimOK.copBilin).comp (z, θ) hpair
    have hfd2 : fderiv ℝ (fderiv ℝ (Function.uncurry f)) (z, θ)
        = Work.FTS_EllLimOK.copBilin.comp
          ((Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pz f) z θ)
              (Work.Spaces.pth (Work.Spaces.pz f) z θ)).prod
            (Work.FTS_EllLimOK.ellCop (Work.Spaces.pz (Work.Spaces.pth f) z θ)
              (Work.Spaces.pth (Work.Spaces.pth f) z θ))) :=
      hg_ev.fderiv_eq.trans hcomp.fderiv
    exact norm_iterDF2_le hfd2

end Work.FTS_EllLimOK.ProducerH.BoxAux
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.Support.jet2_sub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2.Support

open scoped Real

/-- **The order-2 jet is `1`-Lipschitz in the four second partials.**  If the second Fréchet
derivative of `F : ℝ × ℝ → ℝ` at `x` (resp. `y`) is the curried bilinear map with entries
`(A,B,C,D)` (resp. `(A',B',C',D')`), then the difference of the two iterated second derivatives is
bounded in operator norm by `|A-A'| + |B-B'| + |C-C'| + |D-D'|`. -/
theorem norm_iterDF2_sub_le {F : ℝ × ℝ → ℝ} {x y : ℝ × ℝ} {A B C D A' B' C' D' : ℝ}
    (hx : fderiv ℝ (fderiv ℝ F) x = Work.FTS_EllLimOK.copBilin.comp
      ((Work.FTS_EllLimOK.ellCop A B).prod (Work.FTS_EllLimOK.ellCop C D)))
    (hy : fderiv ℝ (fderiv ℝ F) y = Work.FTS_EllLimOK.copBilin.comp
      ((Work.FTS_EllLimOK.ellCop A' B').prod (Work.FTS_EllLimOK.ellCop C' D'))) :
    ‖iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 F y‖
      ≤ |A - A'| + |B - B'| + |C - C'| + |D - D'| := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  rw [sub_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, hx, hy]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    Work.FTS_EllLimOK.copBilin_apply, Work.FTS_EllLimOK.ellCop_apply]
  rw [Real.norm_eq_abs, Fin.prod_univ_two]
  have hh1 : |(m 0).1| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_fst_le (m 0)
  have hh2 : |(m 0).2| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_snd_le (m 0)
  have hk1 : |(m 1).1| ≤ ‖m 1‖ := by simpa [Real.norm_eq_abs] using norm_fst_le (m 1)
  have hk2 : |(m 1).2| ≤ ‖m 1‖ := by simpa [Real.norm_eq_abs] using norm_snd_le (m 1)
  have h1n : (0 : ℝ) ≤ ‖m 1‖ := norm_nonneg _
  have hkey : (m 1).1 * ((m 0).1 * A + (m 0).2 * B) + (m 1).2 * ((m 0).1 * C + (m 0).2 * D) -
        ((m 1).1 * ((m 0).1 * A' + (m 0).2 * B') + (m 1).2 * ((m 0).1 * C' + (m 0).2 * D'))
      = (m 1).1 * (m 0).1 * (A - A') + (m 1).1 * (m 0).2 * (B - B')
        + (m 1).2 * (m 0).1 * (C - C') + (m 1).2 * (m 0).2 * (D - D') := by ring
  rw [hkey]
  have e1 : |(m 1).1 * (m 0).1 * (A - A')| ≤ ‖m 1‖ * (‖m 0‖ * |A - A'|) := by
    rw [abs_mul, abs_mul]
    calc |(m 1).1| * |(m 0).1| * |A - A'| ≤ (‖m 1‖ * ‖m 0‖) * |A - A'| :=
          mul_le_mul_of_nonneg_right (mul_le_mul hk1 hh1 (abs_nonneg _) h1n) (abs_nonneg _)
      _ = ‖m 1‖ * (‖m 0‖ * |A - A'|) := by ring
  have e2 : |(m 1).1 * (m 0).2 * (B - B')| ≤ ‖m 1‖ * (‖m 0‖ * |B - B'|) := by
    rw [abs_mul, abs_mul]
    calc |(m 1).1| * |(m 0).2| * |B - B'| ≤ (‖m 1‖ * ‖m 0‖) * |B - B'| :=
          mul_le_mul_of_nonneg_right (mul_le_mul hk1 hh2 (abs_nonneg _) h1n) (abs_nonneg _)
      _ = ‖m 1‖ * (‖m 0‖ * |B - B'|) := by ring
  have e3 : |(m 1).2 * (m 0).1 * (C - C')| ≤ ‖m 1‖ * (‖m 0‖ * |C - C'|) := by
    rw [abs_mul, abs_mul]
    calc |(m 1).2| * |(m 0).1| * |C - C'| ≤ (‖m 1‖ * ‖m 0‖) * |C - C'| :=
          mul_le_mul_of_nonneg_right (mul_le_mul hk2 hh1 (abs_nonneg _) h1n) (abs_nonneg _)
      _ = ‖m 1‖ * (‖m 0‖ * |C - C'|) := by ring
  have e4 : |(m 1).2 * (m 0).2 * (D - D')| ≤ ‖m 1‖ * (‖m 0‖ * |D - D'|) := by
    rw [abs_mul, abs_mul]
    calc |(m 1).2| * |(m 0).2| * |D - D'| ≤ (‖m 1‖ * ‖m 0‖) * |D - D'| :=
          mul_le_mul_of_nonneg_right (mul_le_mul hk2 hh2 (abs_nonneg _) h1n) (abs_nonneg _)
      _ = ‖m 1‖ * (‖m 0‖ * |D - D'|) := by ring
  have hsplit : |(m 1).1 * (m 0).1 * (A - A') + (m 1).1 * (m 0).2 * (B - B')
        + (m 1).2 * (m 0).1 * (C - C') + (m 1).2 * (m 0).2 * (D - D')|
      ≤ |(m 1).1 * (m 0).1 * (A - A')| + |(m 1).1 * (m 0).2 * (B - B')|
        + |(m 1).2 * (m 0).1 * (C - C')| + |(m 1).2 * (m 0).2 * (D - D')| := by
    have h12 := abs_add_le ((m 1).1 * (m 0).1 * (A - A')) ((m 1).1 * (m 0).2 * (B - B'))
    have h123 := abs_add_le (((m 1).1 * (m 0).1 * (A - A')) + ((m 1).1 * (m 0).2 * (B - B')))
      ((m 1).2 * (m 0).1 * (C - C'))
    have h1234 := abs_add_le ((((m 1).1 * (m 0).1 * (A - A')) + ((m 1).1 * (m 0).2 * (B - B')))
      + ((m 1).2 * (m 0).1 * (C - C'))) ((m 1).2 * (m 0).2 * (D - D'))
    linarith
  refine le_trans hsplit ?_
  calc |(m 1).1 * (m 0).1 * (A - A')| + |(m 1).1 * (m 0).2 * (B - B')|
        + |(m 1).2 * (m 0).1 * (C - C')| + |(m 1).2 * (m 0).2 * (D - D')|
      ≤ ‖m 1‖ * (‖m 0‖ * |A - A'|) + ‖m 1‖ * (‖m 0‖ * |B - B'|)
        + ‖m 1‖ * (‖m 0‖ * |C - C'|) + ‖m 1‖ * (‖m 0‖ * |D - D'|) := by linarith
    _ = (|A - A'| + |B - B'| + |C - C'| + |D - D'|) * (‖m 0‖ * ‖m 1‖) := by ring


end Work.FTS_EllLimOK.ProducerH.H2.Support
end
-- ===== merged: Submission.Work.Spaces.AesmSqProdSmooth =====
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



/-- The open interval `(0,π/2)` and the closed interval `Iθ` carry the same restriction
of Lebesgue measure, since they differ by the two null points `0` and `π/2`. -/
private lemma restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Iθ :=
  Measure.restrict_congr_set (by rw [Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)


end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.HProductRule_Zsummand =====
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
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! Everything below (except the final theorem) is auxiliary and lives in its own
namespace so that it cannot clash with colleagues' names. -/

namespace HPRZ

/-! ## The auxiliary data of the `Z`-summand

For the Leibniz expansion `D_z^i (f·g) = ∑_b C(i,b) D_z^b f · D_z^{i-b} g` we keep,
for each `b ≤ i`, the factor with index `> 2` (in `L²`, with the light weight) and
bound the other factor pointwise.  The following definitions record the retained
factor (`zsFun`, `zsIdx`), its `L^∞`-square (`zsGam`), the product with the weight
(`zsFb`), the coefficient (`zsAA`) and the assembled majorant `zsV`. -/


























/-! ## Measurability and membership of the retained factors -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

lemma Qd_subset_nbhU : Qd ⊆ nbhU := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  exact mem_nbhU (Set.mem_Ici.mpr (le_of_lt hz))
    (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)

lemma sin_two_pos_Qd {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

lemma contOn_Hw_Qd :
    ContinuousOn (fun p : ℝ × ℝ => w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2)) Qd := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (eta / 2)) Qd :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (sin_two_pos_Qd hp.2)))
  have hw : ContinuousOn (fun p : ℝ × ℝ => w p.1) Qd := by
    simp only [w]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  exact hw.div hsin (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_Qd hp.2) _))

lemma contOn_DzIter_Qd (h : ℝ → ℝ → ℝ) (hsm : SmoothNbhd h) (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => DzIter m h p.1 p.2) Qd :=
  ((SmoothNbhd.DzIter hsm m).continuousOn).mono (fun p hp => Qd_subset_nbhU hp)

/-- A.e. strong measurability of the pure `D_z` summand of `HkIntegrand` on the
product measure. -/
theorem aesm_DzIter_H_weight_prod (h : ℝ → ℝ → ℝ) (hsm : SmoothNbhd h) (m : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => DzIter m h p.1 p.2 * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2)))
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
  aesm_of_continuousOn_Qd _ ((contOn_DzIter_Qd h hsm m).mul contOn_Hw_Qd)

/-- A.e. strong measurability of the angular slice of the pure `D_z` summand. -/
theorem aesm_DzIter_H_weight_slice (h : ℝ → ℝ → ℝ) (hsm : SmoothNbhd h)
    (m : ℕ) {z : ℝ} (hz : z ∈ Iz) :
    AEStronglyMeasurable
      (fun θ : ℝ => DzIter m h z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2)))
      (volume.restrict Iθ) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
  · subst h0
    have hz0 : (fun θ : ℝ => DzIter m h 0 θ * (w 0 / (Real.sin (2 * θ)) ^ (eta / 2)))
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      simp [w]
    rw [hz0]
    exact aestronglyMeasurable_const
  · exact aesm_slice_of_continuousOn_Qd _
      ((contOn_DzIter_Qd h hsm m).mul contOn_Hw_Qd) hpos


/-! ## Elementary closure properties of `L2Mem` -/

theorem aesm_abs_of {γ : Type*} [MeasurableSpace γ] {μ : Measure γ} {F : γ → ℝ}
    (h : AEStronglyMeasurable F μ) : AEStronglyMeasurable (fun x => |F x|) μ := by
  simpa only [Real.norm_eq_abs] using h.norm

/-- A finite sum of a.e. strongly measurable functions is a.e. strongly measurable
(in the pointwise presentation, not the `Pi`-sum one). -/
theorem aesm_finset_sum {ι γ : Type*} [MeasurableSpace γ] {μ : Measure γ} (s : Finset ι)
    {f : ι → γ → ℝ} (h : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x => ∑ i ∈ s, f i x) μ := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h : AEStronglyMeasurable (fun _ : γ => (0 : ℝ)) μ := aestronglyMeasurable_const
      simpa only [Finset.sum_empty] using h
  | insert a s ha ih =>
      have hfun : (fun x => ∑ i ∈ insert a s, f i x) = (fun x => f a x + ∑ i ∈ s, f i x) := by
        funext x; rw [Finset.sum_insert ha]
      rw [hfun]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem L2Mem_abs {F : ℝ → ℝ → ℝ} (hF : L2Mem F) : L2Mem (fun z θ => |F z θ|) := by
  constructor
  · intro z hz
    simpa only [sq_abs] using hF.1 z hz
  · simpa only [sq_abs] using hF.2

theorem L2Sq_abs (F : ℝ → ℝ → ℝ) : L2Sq (fun z θ => |F z θ|) = L2Sq F := by
  simp only [L2Sq, sq_abs]

/-- Domination of `F` by an `L2Mem` function `U` transfers `L2Mem`, provided the
squares of `F` are measurable in the two required senses. -/
theorem L2Mem_of_abs_le {F U : ℝ → ℝ → ℝ} (hU : L2Mem U)
    (hFs : ∀ z ∈ Iz, AEStronglyMeasurable (fun θ => (F z θ) ^ 2) (volume.restrict Iθ))
    (hFo : AEStronglyMeasurable
      (fun z => ∫ θ, (F z θ) ^ 2 ∂(volume.restrict Iθ)) (volume.restrict Iz))
    (h : ∀ z ∈ Iz, ∀ θ ∈ Iθ, |F z θ| ≤ |U z θ|) : L2Mem F := by
  have hsq : ∀ z ∈ Iz, ∀ θ ∈ Iθ, (F z θ) ^ 2 ≤ (U z θ) ^ 2 := fun z hz θ hθ => by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h z hz θ hθ) 2
  constructor
  · intro z hz
    refine Integrable.mono' (hU.1 z hz) (hFs z hz) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hsq z hz θ hθ
  · refine Integrable.mono' hU.2 hFo ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hU.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ hθ => hsq z hz θ hθ))

/-! ## Finite sums of `L2Mem` functions -/

/-- A finite linear combination of `L2Mem` functions is `L2Mem`, and its squared `L²`
norm obeys the Cauchy–Schwarz estimate.  The two measurability hypotheses are what
the slices and the outer partial integral need; they are available in the application
below from `aesm_DzIter_H_weight_slice`/`_prod`. -/
theorem L2Mem_L2Sq_finset_sum_le {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℝ) (C : ι → ℝ)
    (hF : ∀ b ∈ s, L2Mem (F b))
    (hAE1 : ∀ z ∈ Iz, AEStronglyMeasurable
      (fun θ : ℝ => (∑ b ∈ s, C b * F b z θ) ^ 2) (volume.restrict Iθ))
    (hAE2 : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ, (∑ b ∈ s, C b * F b z θ) ^ 2 ∂(volume.restrict Iθ))
      (volume.restrict Iz)) :
    L2Mem (fun z θ => ∑ b ∈ s, C b * F b z θ)
      ∧ L2Sq (fun z θ => ∑ b ∈ s, C b * F b z θ)
        ≤ (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * L2Sq (F b) := by
  have hpt : ∀ z θ : ℝ, (∑ b ∈ s, C b * F b z θ) ^ 2
      ≤ (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2 := by
    intro z θ
    refine le_trans (sq_sum_le_card_mul_sum_sq (s := s) (f := fun b => C b * F b z θ)) ?_
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun b hb => le_of_eq (by ring)) (Nat.cast_nonneg _)
  have hmaj_i : ∀ z ∈ Iz, Integrable
      (fun θ : ℝ => (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2)
      (volume.restrict Iθ) := by
    intro z hz
    exact (integrable_finsetSum s (fun b hb => (hF b hb).1 z hz |>.const_mul _)).const_mul _
  have hae_maj : (fun z : ℝ => (s.card : ℝ) * ∑ b ∈ s,
        (C b) ^ 2 * (∫ θ, (F b z θ) ^ 2 ∂(volume.restrict Iθ)))
      =ᵐ[volume.restrict Iz]
      (fun z : ℝ => ∫ θ, (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2
        ∂(volume.restrict Iθ)) := by
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    show (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (∫ θ, (F b z θ) ^ 2 ∂(volume.restrict Iθ))
      = ∫ θ, (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2 ∂(volume.restrict Iθ)
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum s
      (f := fun b θ => (C b) ^ 2 * (F b z θ) ^ 2) (fun b hb => (hF b hb).1 z hz |>.const_mul _)]
    exact Finset.sum_congr rfl fun b hb => (integral_const_mul _ _).symm
  have hmaj_z : Integrable
      (fun z : ℝ => ∫ θ, (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2
        ∂(volume.restrict Iθ)) (volume.restrict Iz) := by
    have hg : Integrable (fun z : ℝ => (s.card : ℝ) * ∑ b ∈ s,
        (C b) ^ 2 * (∫ θ, (F b z θ) ^ 2 ∂(volume.restrict Iθ))) (volume.restrict Iz) :=
      (integrable_finsetSum s (fun b hb => (hF b hb).2.const_mul _)).const_mul _
    exact hg.congr hae_maj
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    refine Integrable.mono' (hmaj_i z hz) (hAE1 z hz) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt z θ
  · refine Integrable.mono' hmaj_z hAE2 ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hmaj_i z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => hpt z θ))
  · rw [L2Sq]
    have hmain : ∫ z in Iz, ∫ θ in Iθ, (∑ b ∈ s, C b * F b z θ) ^ 2
        ≤ ∫ z in Iz, ∫ θ in Iθ, (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2 := by
      refine integral_mono_of_nonneg
        (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hmaj_z ?_
      filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
      refine integral_mono_of_nonneg
        (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
          (fun θ _ => sq_nonneg _))
        (hmaj_i z hz) ?_
      filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
      exact hpt z θ
    have hval : ∫ z in Iz, ∫ θ in Iθ, (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2
        = (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * L2Sq (F b) := by
      rw [← integral_congr_ae hae_maj]
      rw [integral_const_mul,
        integral_finsetSum s
          (f := fun b z => (C b) ^ 2 * (∫ θ, (F b z θ) ^ 2 ∂(volume.restrict Iθ)))
          (fun b hb => (hF b hb).2.const_mul _)]
      congr 1
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [integral_const_mul]
      simp only [L2Sq]
    exact le_trans hmain (le_of_eq hval)

/-! ## The coefficient estimate -/

theorem zs_coeff_bound (i : ℕ) (hi : i ≤ 4) :
    ((i : ℝ) + 1) * (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2) * 100 ≤ 10 ^ 12 := by
  have hterm : ∀ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2 ≤ 256 := by
    intro b hb
    have hb' : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
    have h2 : (2 : ℕ) ^ i ≤ 16 := by interval_cases i <;> norm_num
    have h3 : i.choose b ≤ 16 := le_trans h1 h2
    have h4 : ((i.choose b : ℕ) : ℝ) ≤ 16 := by exact_mod_cast h3
    nlinarith [h4, Nat.cast_nonneg (α := ℝ) (i.choose b)]
  have hsum : (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2) ≤ 1280 := by
    have h := Finset.sum_le_card_nsmul (Finset.range (i + 1))
      (fun b => (i.choose b : ℝ) ^ 2) 256 hterm
    simp only [nsmul_eq_mul] at h
    have hcard : ((Finset.range (i + 1)).card : ℝ) ≤ 5 := by
      simp only [Finset.card_range]
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_succ_of_le hi)
    nlinarith [h, hcard]
  have h0 : (0 : ℝ) ≤ ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hi5 : ((i : ℝ) + 1) ≤ 5 := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_succ_of_le hi)
  nlinarith [hsum, h0, hi5]

end HPRZ

open HPRZ

/-! ## The theorem -/


end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.SmoothCompact_HkInf =====
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

/-- Membership in `ℋ^k` of a smooth compactly supported function. -/
theorem HkSq_le_of_bound (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (R M : ℝ)
    (hR : 0 ≤ R) (hMnn : 0 ≤ M)
    (hf_gt : ∀ z θ : ℝ, R < z → f z θ = 0)
    (hbound : ∀ z ∈ Iz, ∀ θ ∈ Iθ, HkIntegrand α k f z θ ≤ M) :
    HkSq α k f ≤ M * (π / 2) * (R + 1) := by
  set g : ℝ → ℝ := (Set.Icc 0 R).indicator (fun _ => M * (π / 2)) with hg
  have hinner_le : ∀ z ∈ Iz, (∫ θ in Iθ, HkIntegrand α k f z θ) ≤ M * (π / 2) := by
    intro z hz
    have hz0le : (0 : ℝ) ≤ z := hz
    by_cases hzR : z ≤ R
    · calc (∫ θ in Iθ, HkIntegrand α k f z θ)
          ≤ |∫ θ in Iθ, HkIntegrand α k f z θ| := le_abs_self _
        _ = ‖∫ θ in Iθ, HkIntegrand α k f z θ‖ := (Real.norm_eq_abs _).symm
        _ ≤ M * (π / 2) := by
            rw [← volume_real_Iθ]
            refine norm_setIntegral_le_of_norm_le_const volume_Iθ_lt_top fun θ hθ => ?_
            rw [Real.norm_eq_abs]
            exact abs_le.mpr ⟨by linarith [HkIntegrand_nonneg α k f z θ, hMnn],
              hbound z hz θ hθ⟩
    · rw [show (fun θ => HkIntegrand α k f z θ) = fun _ => (0 : ℝ) from
        funext fun θ => HkIntegrand_eq_zero_of_gt α k f R z θ hf_gt (not_le.mp hzR)]
      simp only [integral_zero]
      exact mul_nonneg hMnn (by linarith [Real.pi_pos])
  have hgint : Integrable g (volume.restrict Iz) := by
    rw [hg]
    refine (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr ?_
    have hfin : (volume.restrict Iz) (Set.Icc 0 R) ≠ ⊤ := by
      rw [Measure.restrict_apply measurableSet_Icc]
      have h1 : volume (Set.Icc 0 R ∩ Iz) ≤ volume (Set.Icc 0 R) :=
        measure_mono Set.inter_subset_left
      have h2 : volume (Set.Icc 0 R) < ⊤ := by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
      exact ne_of_lt (lt_of_le_of_lt h1 h2)
    exact MeasureTheory.integrableOn_const hfin
  have hle : (fun z => ∫ θ in Iθ, HkIntegrand α k f z θ) ≤ᵐ[volume.restrict Iz] g := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    by_cases hzR : z ≤ R
    · rw [hg, Set.indicator_of_mem (show z ∈ Set.Icc 0 R from ⟨hz, hzR⟩)]
      exact hinner_le z hz
    · rw [hg, Set.indicator_of_notMem (by
        intro hmem
        exact absurd hmem.2 hzR)]
      rw [show (fun θ => HkIntegrand α k f z θ) = fun _ => (0 : ℝ) from
        funext fun θ => HkIntegrand_eq_zero_of_gt α k f R z θ hf_gt (not_le.mp hzR)]
      simp
  have hmain := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => HkIntegrand_nonneg α k f z θ) hgint hle
  have hgval : ∫ z, g z ∂(volume.restrict Iz) ≤ M * (π / 2) * (R + 1) := by
    rw [hg, MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const]
    rw [smul_eq_mul]
    have hmeas : (volume.restrict Iz).real (Set.Icc 0 R) ≤ R + 1 := by
      rw [MeasureTheory.measureReal_def, Measure.restrict_apply measurableSet_Icc]
      have hset : Set.Icc 0 R ∩ Iz = Set.Icc 0 R := by
        ext x
        constructor
        · intro hx; exact hx.1
        · intro hx; exact ⟨hx, hx.1⟩
      rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      linarith
    have hMpi : 0 ≤ M * (π / 2) := mul_nonneg hMnn (by linarith [Real.pi_pos])
    nlinarith [hmeas, hMpi]
  rw [HkSq]
  exact le_trans hmain hgval


end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.bt_prod_integrable =====
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

/-! ## Angular slices are integrable, by domination by `HkIntegrand α 4 g` -/

private theorem slice_integrable_aux (α : ℝ) (g : ℝ → ℝ → ℝ) (hmem : HkMem α 4 g)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (mixed j i g p.1 p.2 * Wt α p.1 p.2) ^ 2)
      ((volume.restrict Iz).prod (volume.restrict Iθ))) :
    ∀ᵐ z ∂(volume.restrict Iz),
      Integrable (fun θ => (mixed j i g z θ * Wt α z θ) ^ 2) (volume.restrict Iθ) := by
  -- The slice is a.e. strongly measurable because the joint function is, and for
  -- `z ∈ Iz` it is dominated by the (integrable) slice of the `H⁴`-integrand.
  filter_upwards [hAE.prodMk_left, ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)]
    with z hz_meas hz
  refine Integrable.mono' (hmem.1 z hz) hz_meas ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij

/-! ## The iterated integral is integrable, by domination by `hmem.2` -/

private theorem outer_integrable_aux (α : ℝ) (g : ℝ → ℝ → ℝ) (hmem : HkMem α 4 g)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (mixed j i g p.1 p.2 * Wt α p.1 p.2) ^ 2)
      ((volume.restrict Iz).prod (volume.restrict Iθ))) :
    Integrable (fun z => ∫ θ, (mixed j i g z θ * Wt α z θ) ^ 2 ∂(volume.restrict Iθ))
      (volume.restrict Iz) := by
  -- `z ↦ ∫_θ (…)²` is a.e. strongly measurable (partial integral of the joint function)
  -- and pointwise bounded by the integrable function `z ↦ ∫_θ HkIntegrand α 4 g`.
  refine Integrable.mono' hmem.2 hAE.integral_prod_right' ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
  exact integral_mono_of_nonneg
    (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
      (fun θ _ => sq_nonneg _))
    (hmem.1 z hz)
    (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
      (fun θ _ => sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij))

/-! ## Assembly -/

theorem bt_prod_integrable (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α 4 g)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.integral
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (fun p : ℝ × ℝ => (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ (mixed j i g z θ * Wt α z θ) ^ 2 := fun z θ => sq_nonneg _
  have hAE := aesm_mixed_Wt_sq_prod α g hsm j i
  have hslice := slice_integrable_aux α g hmem j i hi hij hAE
  have houter := outer_integrable_aux α g hmem j i hi hij hAE
  obtain ⟨hint, hval⟩ := integrable_prod_of_iterated hnn hAE hslice houter
  refine ⟨hint, ?_⟩
  rw [hval]
  simp only [L2Sq]

end Work.Spaces
end
end
