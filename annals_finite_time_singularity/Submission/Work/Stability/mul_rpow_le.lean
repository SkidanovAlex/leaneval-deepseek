import ChallengeDeps
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Have
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Uniformizable
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.SobolevCalc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FourierTransform TemperedDistribution MeasureTheory Laplacian LineDeriv
open scoped SchwartzMap BesselPotentialSpace ENNReal Real

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.EllipticEst.InteriorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `w s x = (1 + ‖x‖^2)^(s/2)` as a complex valued function: the symbol of the Bessel
potential of order `s`. -/
def w (s : ℝ) : E → ℂ := fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)

/-- The multiplier `x ↦ ‖x‖^2` (the symbol of `-Δ/(2π)^2`). -/
def tt : E → ℂ := fun x => ((‖x‖ ^ 2 : ℝ) : ℂ)

theorem w_temperate (s : ℝ) : (w (E := E) s).HasTemperateGrowth := by
  unfold w; fun_prop

theorem tt_temperate : (tt (E := E)).HasTemperateGrowth := by
  unfold tt; fun_prop

theorem w_mul_tt_temperate (s : ℝ) : (w (E := E) s * tt).HasTemperateGrowth := by
  unfold w tt; fun_prop

/-- The elementary decomposition `(1+t)^{(s+2)/2} = (1+t)^{s/2} + (1+t)^{s/2}·t`. -/
theorem w_add_two (s : ℝ) : w (E := E) (s+2) = w (E := E) s + w (E := E) s * tt := by
  funext x
  unfold w tt
  simp only [Pi.add_apply, Pi.mul_apply]
  have h1 : (0:ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  rw [show (s+2)/2 = s/2 + 1 by ring, Real.rpow_add h1, Real.rpow_one]
  push_cast
  ring

/-- The Fourier transform commutes with Fourier multipliers, on the Fourier side. -/
theorem fourier_mult (g : E → ℂ) (u : 𝓢'(E, ℂ)) :
    𝓕 (fourierMultiplierCLM ℂ g u) = smulLeftCLM ℂ g (𝓕 u) := by
  rw [fourierMultiplierCLM_apply, fourier_fourierInv_eq]


/-- The Fourier transform of the Laplacian as a multiplier. -/
theorem fourier_laplacian (u : 𝓢'(E, ℂ)) :
    𝓕 (Δ u) = (((-(2 * π : ℝ) ^ 2 : ℝ)) : ℂ) • smulLeftCLM ℂ (tt (E := E)) (𝓕 u) := by
  have hlap : Δ u = (((-(2 * π : ℝ) ^ 2 : ℝ)) : ℂ) • fourierMultiplierCLM ℂ (tt (E := E)) u := by
    rw [laplacian_eq_fourierMultiplierCLM, ← Complex.coe_smul]
    rfl
  rw [hlap, fourier_smul, fourier_mult]

/-- **Gain-two lemma for the Laplacian.**  If `u ∈ H^s` and `Δ u ∈ H^s` then `u ∈ H^{s+2}`.

This is the constant-coefficient elliptic estimate, in the Bessel-potential (Fourier)
formulation; it is proved by splitting the symbol of the Bessel potential of order `s+2`. -/
theorem gain_two (s : ℝ) (u : 𝓢'(E, ℂ))
    (hu : MemSobolev s 2 u) (hΔ : MemSobolev s 2 (Δ u)) :
    MemSobolev (s+2) 2 u := by
  obtain ⟨v, hv⟩ := (memSobolev_iff_exists_smulLeftCLM_fourier (F := ℂ)).mp hu
  obtain ⟨v', hv'⟩ := (memSobolev_iff_exists_smulLeftCLM_fourier (F := ℂ)).mp hΔ
  have hv2 : smulLeftCLM ℂ (w (E := E) s) (𝓕 u) = Lp.toTemperedDistribution v := hv
  have hv2' : smulLeftCLM ℂ (w (E := E) s) (𝓕 (Δ u)) = Lp.toTemperedDistribution v' := hv'
  set c : ℂ := (((-(2 * π : ℝ) ^ 2 : ℝ)) : ℂ) with hc
  have hcne : c ≠ 0 := by
    rw [hc]; push_cast; simp [Real.pi_ne_zero]
  have h3 : 𝓕 (Δ u) = c • smulLeftCLM ℂ (tt (E := E)) (𝓕 u) := fourier_laplacian u
  have h4 : smulLeftCLM ℂ (w (E := E) s * tt) (𝓕 u) = c⁻¹ • Lp.toTemperedDistribution v' := by
    have h2' := hv2'
    rw [h3, ContinuousLinearMap.map_smul,
      smulLeftCLM_smulLeftCLM_apply (tt_temperate) (w_temperate s)] at h2'
    rw [mul_comm (tt (E := E)) (w (E := E) s)] at h2'
    rw [← h2', smul_smul, inv_mul_cancel₀ hcne, one_smul]
  refine ⟨𝓕⁻ v + c⁻¹ • 𝓕⁻ v', ?_⟩
  show fourierMultiplierCLM ℂ (w (E := E) (s+2)) u = Lp.toTemperedDistribution _
  rw [fourierMultiplierCLM_apply, w_add_two s,
    smulLeftCLM_add (w_temperate s) (w_mul_tt_temperate s), add_apply, hv2, h4]
  rw [fourierInv_add, fourierInv_smul,
    MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq,
    MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq]
  rw [← MeasureTheory.Lp.toTemperedDistributionCLM_apply (f := 𝓕⁻ v + c⁻¹ • 𝓕⁻ v'),
    map_add, map_smul,
    MeasureTheory.Lp.toTemperedDistributionCLM_apply,
    MeasureTheory.Lp.toTemperedDistributionCLM_apply]

end Work.EllipticEst.InteriorRegularity
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Baux.SliceAngRoomDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

noncomputable section

set_option autoImplicit false

/-!
# Vocabulary for the angular slice "room" construction (`SLICE-ANG(k)`)

`u` is a θ-slice, `v = u/cos θ` the `cos`-divided profile, `σ = sin(2θ)`, `q = σ^{2k-γ}`,
`W = σ·q`, `P = cos²θ·q`, `B` the "room" coefficient and `D` the flux of the room identity:

* `slice_ang_room_ident` (proved) gives the two pointwise product-rule identities;
* adding them (with the weights `-(k+2)sin²θq` and `(k+1)`) and integrating over `[a,b]` gives the
  **room integral identity**
  `∫ ( sinθcosθ v^{(k+1)}v^{(k+2)} - (k+2)sin²θ (v^{(k+1)})² + (k+1)cos²θ v^{(k)}v^{(k+2)} ) q
      = - ∫ B (v^{(k+1)})² q + ((k+1)/2)∫ (cos²θq)'' (v^{(k)})² + D(b) - D(a)`,
  with `B = ((2k+1-γ)/2)cos2θ + (k+2)sin²θ + (k+1)cos²θ = ((4k+3-γ)/2)cos²θ + ((3+γ)/2)sin²θ`,
  i.e. `B ≥ (3+γ)/2 > 0` on `Iθ`, and the flux
  `D = ¼σq(v^{(k+1)})² + (k+1)cos²θq v^{(k)}v^{(k+1)} - ½(k+1)(cos²θq)'(v^{(k)})²`.
-/

/-- `v = u / cos θ`. -/
def sv (u : ℝ → ℝ) : ℝ → ℝ := fun t => u t / Real.cos t

/-- `q = sin(2θ)^{2k-γ}`. -/
def sq (k : ℕ) (γ : ℝ) : ℝ → ℝ :=
  fun θ => Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)

/-- `W = sin(2θ)·q = 2 sinθ cosθ · q`. -/
def sW (k : ℕ) (γ : ℝ) : ℝ → ℝ :=
  fun θ => Real.sin (2 * θ) * sq k γ θ

/-- `P = cos²θ · q`. -/
def sP (k : ℕ) (γ : ℝ) : ℝ → ℝ :=
  fun θ => Real.cos θ ^ 2 * sq k γ θ

/-- The room coefficient
`B = ((2k+1-γ)/2)·cos2θ + (k+2)·sin²θ + (k+1)·cos²θ`.  On `(0,π/2)` it equals
`((4k+3-γ)/2)cos²θ + ((3+γ)/2)sin²θ`, so

`B - (3+γ)/2 = (2k-γ)·cos²θ`,

and hence `B ≥ (3+γ)/2 > 0` on `(0,π/2)` **provided `γ ≤ 2k`** (which holds in the intended
application `k ≥ 2`, `γ ≤ 5/4`). -/
def sB (k : ℕ) (γ : ℝ) : ℝ → ℝ :=
  fun θ => ((2 * (k : ℝ) + 1 - γ) / 2) * Real.cos (2 * θ)
    + ((k : ℝ) + 2) * Real.sin θ ^ 2 + ((k : ℝ) + 1) * Real.cos θ ^ 2

/-- The flux `D` of the room identity. -/
def sD (k : ℕ) (γ : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (1 / 4) * sW k γ θ * (iteratedDeriv (k + 1) (sv u) θ) ^ 2
    + ((k : ℝ) + 1) * sP k γ θ * iteratedDeriv k (sv u) θ
        * iteratedDeriv (k + 1) (sv u) θ
    - (1 / 2) * ((k : ℝ) + 1) * deriv (sP k γ) θ * (iteratedDeriv k (sv u) θ) ^ 2

end

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgB_int_Ioi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-- AM–GM: `|a·b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * (|a| * |b|) ≤ |a| ^ 2 + |b| ^ 2 := by nlinarith [sq_nonneg (|a| - |b|)]
  rw [abs_mul]
  linarith [h, sq_abs a, sq_abs b]

/-- AM–GM in the form used below: `|y| ≤ (y² + 1)/2`. -/
private lemma abs_le_sq_add_one_div_two (y : ℝ) : |y| ≤ (y ^ 2 + 1) / 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1)]

/-- For `0 < δ ≤ x` the negative power `x^{-p-1}` is dominated by its value at `δ`, provided the
exponent is negative, i.e. `0 ≤ p`. -/
private lemma rpow_neg_sub_one_le {t x p : ℝ} (ht : 0 < t) (htx : t ≤ x) (hp : 0 ≤ p) :
    x ^ (-p - 1) ≤ t ^ (-p - 1) := by
  have hx : 0 < x := lt_of_lt_of_le ht htx
  rw [show -p - 1 = -(p + 1) from by ring]
  rw [Real.rpow_neg hx.le, Real.rpow_neg ht.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos ht _) (Real.rpow_le_rpow ht.le htx (by linarith))

theorem rgB_int_Ioi {c : ℝ → ℝ} {p δ : ℝ} (hp : 1 ≤ p) (hδ : 0 < δ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => |c t|)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => ‖c t * t ^ (-p - 1)‖) (Set.Ioi δ) := by
  have hp0 : 0 ≤ p := by linarith
  -- ### a.e. strong measurability of `|c t| * t^{-p-1}` on `Ioi δ`
  have hAesm : AEStronglyMeasurable (fun t : ℝ => |c t| * t ^ (-p - 1))
      (volume.restrict (Ioi δ)) := by
    have h1 : AEStronglyMeasurable (fun t : ℝ => |c t|) (volume.restrict (Ioi δ)) :=
      hmeas.mono_set (fun x hx => lt_trans hδ hx)
    have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (-p - 1))
        (volume.restrict (Ioi δ)) :=
      (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (ne_of_gt (lt_trans hδ hx)))).aestronglyMeasurable measurableSet_Ioi
    exact h1.mul h2
  -- ### The part `(δ, 1]`: bounded weight, `L²` control of `c` from `hnear`
  have hA : IntegrableOn (fun x : ℝ => |c x| * x ^ (-p - 1)) (Ioc δ 1) := by
    have hIoo : Integrable (fun x : ℝ => |c x| * x ^ (-p - 1))
        (volume.restrict (Ioo δ 1)) := by
      have hmaj : Integrable
          (fun x : ℝ => δ ^ (-p - 1) * (((c x) ^ 2 / x ^ 4 + 1) / 2))
          (volume.restrict (Ioo δ 1)) := by
        have h11 : Integrable (fun x : ℝ => (c x) ^ 2 / x ^ 4)
            (volume.restrict (Ioo δ 1)) :=
          hnear.mono_set (fun x hx => ⟨lt_trans hδ hx.1, hx.2⟩)
        have h12 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo δ 1)) :=
          integrable_const 1
        exact ((h11.add h12).div_const 2).const_mul _
      refine Integrable.mono' hmaj (hAesm.mono_set (fun x hx => hx.1)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hxδ : δ < x := hx.1
      have hx1 : x ≤ 1 := hx.2.le
      have hx0 : 0 < x := lt_trans hδ hxδ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abs_nonneg (c x)),
        abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      have hw : x ^ (-p - 1) ≤ δ ^ (-p - 1) := rpow_neg_sub_one_le hδ hxδ.le hp0
      -- `|c x| ≤ x²·|c x|/x² ≤ ((c x)²/x⁴ + 1)/2` on `(δ,1]`
      have hcA : |c x| ≤ ((c x) ^ 2 / x ^ 4 + 1) / 2 := by
        have h1 : |c x / x ^ 2| ≤ ((c x / x ^ 2) ^ 2 + 1) / 2 := abs_le_sq_add_one_div_two _
        have h2 : (c x / x ^ 2) ^ 2 = (c x) ^ 2 / x ^ 4 := by
          rw [div_pow, show (x ^ 2) ^ 2 = x ^ 4 from by ring]
        have h3 : |c x / x ^ 2| = |c x| / x ^ 2 := by
          rw [abs_div, abs_of_nonneg (sq_nonneg x)]
        have h4 : x ^ 2 * (|c x| / x ^ 2) = |c x| := by
          field_simp
        have h5 : x ^ 2 ≤ 1 := by nlinarith [hx1, hx0]
        rw [h2] at h1
        rw [h3] at h1
        calc |c x| = x ^ 2 * (|c x| / x ^ 2) := h4.symm
          _ ≤ 1 * (|c x| / x ^ 2) := mul_le_mul_of_nonneg_right h5 (by positivity)
          _ = |c x| / x ^ 2 := one_mul _
          _ ≤ ((c x) ^ 2 / x ^ 4 + 1) / 2 := h1
      calc |c x| * x ^ (-p - 1)
          ≤ |c x| * δ ^ (-p - 1) := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
        _ = δ ^ (-p - 1) * |c x| := by ring
        _ ≤ δ ^ (-p - 1) * (((c x) ^ 2 / x ^ 4 + 1) / 2) :=
            mul_le_mul_of_nonneg_left hcA (Real.rpow_nonneg hδ.le _)
    exact MeasureTheory.IntegrableOn.congr_set_ae hIoo
      (Ioo_ae_eq_Ioc (a := δ) (b := 1)).symm
  -- ### The part `(1, ∞)`: `c ∈ L²` against the `L²` weight `x^{-p-1}`
  have hB : IntegrableOn (fun x : ℝ => |c x| * x ^ (-p - 1)) (Ioi (max δ 1)) := by
    have hδ' : 0 < max δ 1 := lt_of_lt_of_le zero_lt_one (le_max_right δ 1)
    have hmaj : Integrable (fun x : ℝ => ((c x) ^ 2 + x ^ (-(2 * p) - 2)) / 2)
        (volume.restrict (Ioi (max δ 1))) := by
      have h1 : Integrable (fun x => (c x) ^ 2) (volume.restrict (Ioi (max δ 1))) :=
        hfar.mono_set (fun x hx => lt_of_le_of_lt (le_max_right δ 1) hx)
      have h2 : Integrable (fun x => x ^ (-(2 * p) - 2)) (volume.restrict (Ioi (max δ 1))) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) hδ'
      exact (h1.add h2).div_const 2
    refine Integrable.mono' hmaj (hAesm.mono_set (fun x hx => ?_)) ?_
    · exact lt_of_le_of_lt (le_max_left δ 1) hx
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := lt_trans zero_lt_one (lt_of_le_of_lt (le_max_right δ 1) hx)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abs_nonneg (c x)),
        abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      have hb : (x ^ (-p - 1)) ^ 2 = x ^ (-(2 * p) - 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        congr 1
        ring
      calc |c x| * x ^ (-p - 1)
          = |c x * x ^ (-p - 1)| := by
              rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
        _ ≤ ((c x) ^ 2 + (x ^ (-p - 1)) ^ 2) / 2 := abs_mul_le_half_sq_add_sq _ _
        _ = ((c x) ^ 2 + x ^ (-(2 * p) - 2)) / 2 := by rw [hb]
  -- ### Glue the two parts
  have hsub : Ioi δ ⊆ Ioc δ 1 ∪ Ioi (max δ 1) := by
    intro x hx
    by_cases h : x ≤ 1
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr (max_lt hx (lt_of_not_ge h))
  have hU : IntegrableOn (fun x : ℝ => |c x| * x ^ (-p - 1))
      (Ioc δ 1 ∪ Ioi (max δ 1)) := hA.union hB
  have hmain : IntegrableOn (fun x : ℝ => |c x| * x ^ (-p - 1)) (Ioi δ) :=
    hU.mono_set hsub
  -- ### Rewrite the absolutised integrand as the norm of the original one
  refine hmain.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans hδ hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.hasDerivAt_pairGreen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

theorem hasDerivAt_pairGreen {K sn sp : ℝ} {A B F1 F2 : ℝ → ℝ} {z : ℝ}
    (hA : HasDerivAt A (F1 z) z) (hB : HasDerivAt B (-(F2 z)) z) (hz : z ≠ 0) :
    HasDerivAt (fun y => K * ((sn * y ^ (sn - 1)) * A y + (sp * y ^ (sp - 1)) * B y))
      (K * (((sn * ((sn - 1) * z ^ (sn - 2))) * A z + (sn * z ^ (sn - 1)) * F1 z)
          + ((sp * ((sp - 1) * z ^ (sp - 2))) * B z + (sp * z ^ (sp - 1)) * (-(F2 z))))) z := by
  -- product rule: differentiate `y ↦ K * ((sn * y^(sn-1)) * A y + (sp * y^(sp-1)) * B y)`
  have hp1 : HasDerivAt (fun t : ℝ => sn * t ^ (sn - 1))
      (sn * ((sn - 1) * z ^ (sn - 2))) z := by
    have h := (Real.hasDerivAt_rpow_const (x := z) (p := sn - 1) (Or.inl hz)).const_mul sn
    rwa [show (sn - 1) - 1 = sn - 2 from by ring] at h
  have hp2 : HasDerivAt (fun t : ℝ => sp * t ^ (sp - 1))
      (sp * ((sp - 1) * z ^ (sp - 2))) z := by
    have h := (Real.hasDerivAt_rpow_const (x := z) (p := sp - 1) (Or.inl hz)).const_mul sp
    rwa [show (sp - 1) - 1 = sp - 2 from by ring] at h
  exact ((hp1.mul hA).add (hp2.mul hB)).const_mul K

end Work.FTS.PhiStar.Series.Deleg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.summableModeMajorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

theorem summableModeMajorant (K A : ℝ) :
    Summable (fun m : ℕ => (if m = 0 then K else 0) + A * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
  -- The `if m = 0` term has finite support, hence is summable ...
  have h1 : Summable (fun m : ℕ => if m = 0 then K else 0) :=
    summable_of_ne_finset_zero (s := {0}) (fun b hb => by
      simp only [Finset.mem_singleton] at hb
      simp [hb])
  -- ... and the `m^{-3/2}` tail is the convergent `p`-series with `p = 3/2 > 1`.
  have h2 : Summable (fun m : ℕ => A * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv (p := (3 / 2 : ℝ))).mpr (by norm_num) |>.mul_left A
  exact h1.add h2

end Work.FTS.PhiStar.Series.Deleg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.SmoothAux.SeriesAux.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.SmoothAux

set_option autoImplicit false

/-- The majorant `maj m = (m+1)^{-3/2}`. -/
def maj (m : ℕ) : ℝ := (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹

lemma maj_nonneg (m : ℕ) : 0 ≤ maj m := by
  have h : (0 : ℝ) < ((m : ℝ) + 1) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  simpa [maj] using inv_nonneg.mpr (le_of_lt h)

/-- The majorant is summable. -/
lemma summable_maj : Summable maj := by
  have h2 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
    have h : Summable (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
      (Real.summable_nat_rpow_inv (p := (3 / 2 : ℝ))).mpr (by norm_num)
    have h3 := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h3
  exact h2

/-- **Smoothing of `iteratedDeriv`.**  If `f` is `C^k` on `(0,∞)` for every `k`, then so is each
of its iterated derivatives. -/
lemma contDiffOn_iteratedDeriv {f : ℝ → ℝ} (hf : ∀ k : ℕ, ContDiffOn ℝ k f (Set.Ioi 0)) :
    ∀ (a n : ℕ), ContDiffOn ℝ n (iteratedDeriv a f) (Set.Ioi 0) := by
  intro a
  induction a with
  | zero => intro n; simpa only [iteratedDeriv_zero] using hf n
  | succ a ih =>
    intro n
    have h1 : ContDiffOn ℝ ((n : ℕ∞ω) + 1) (iteratedDeriv a f) (Set.Ioi 0) := by
      have := ih (n + 1)
      simpa only [Nat.cast_add, Nat.cast_one] using this
    have h2 := ((contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) isOpen_Ioi).1 h1).2.2
    rw [iteratedDeriv_succ]
    exact h2



end Work.FTS.PhiStar.Series.SmoothAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Weil.continuousOn_sq_integrableOn_Ioo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Weil

/-- The square of a function continuous on `[a, b]` is integrable on the open interval
`(a, b)`.  (The hypothesis `a ≤ b` is not needed for the argument: `[a, b]` is compact
in either case, and the empty interval case is trivial.) -/
theorem continuousOn_sq_integrableOn_Ioo {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => f θ ^ 2) (Set.Ioo a b) := by
  -- `f ^ 2` is continuous on the compact interval `[a, b]`, hence integrable there;
  -- restricting to the smaller set `(a, b) ⊆ [a, b]` preserves integrability.
  have _ : a ≤ b := hab
  exact (hf.pow 2).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self

end Work.FTS.PhiStar.Series.Weil
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.abs_deriv2_mul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series

lemma abs_deriv2_mul_le {f g : ℝ → ℝ} {θ : ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hf' : DifferentiableAt ℝ (deriv f) θ) (hg' : DifferentiableAt ℝ (deriv g) θ)
    {A B A' B' : ℝ} (hA : |deriv f θ| ≤ A) (hB : |deriv g θ| ≤ B)
    (hA' : |deriv (deriv f) θ| ≤ A') (hB' : |deriv (deriv g) θ| ≤ B')
    (hf0 : 0 ≤ f θ) (hf1 : f θ ≤ 1) (hg0 : 0 ≤ g θ) (hg1 : g θ ≤ 1) :
    |deriv (deriv (f * g)) θ| ≤ A' + 2 * A * B + B' := by
  -- Leibniz twice: `(f * g)'' = f'' * g + 2 * (f' * g') + f * g''`.
  have hderiv : deriv (deriv (f * g)) θ
      = deriv (deriv f) θ * g θ + 2 * (deriv f θ * deriv g θ) + f θ * deriv (deriv g) θ := by
    have h1 : deriv (f * g) = fun x => deriv f x * g x + f x * deriv g x := by
      funext x
      exact deriv_mul (hf x) (hg x)
    rw [h1]
    have hd1 : DifferentiableAt ℝ (fun x => deriv f x * g x) θ := hf'.mul hg.differentiableAt
    have hd2 : DifferentiableAt ℝ (fun x => f x * deriv g x) θ := hf.differentiableAt.mul hg'
    change deriv ((fun x => deriv f x * g x) + (fun x => f x * deriv g x)) θ = _
    rw [deriv_add hd1 hd2]
    change deriv ((deriv f) * g) θ + deriv (f * deriv g) θ = _
    rw [deriv_mul hf' hg.differentiableAt, deriv_mul hf.differentiableAt hg']
    ring
  rw [hderiv]
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) hA
  have hA'0 : 0 ≤ A' := le_trans (abs_nonneg _) hA'
  have hgn : |g θ| ≤ 1 := abs_le.2 ⟨by linarith [hg0], hg1⟩
  have hfn : |f θ| ≤ 1 := abs_le.2 ⟨by linarith [hf0], hf1⟩
  have h1 : |deriv (deriv f) θ * g θ| ≤ A' := by
    rw [abs_mul]
    calc |deriv (deriv f) θ| * |g θ| ≤ A' * 1 := mul_le_mul hA' hgn (abs_nonneg _) hA'0
      _ = A' := mul_one A'
  have h2 : |2 * (deriv f θ * deriv g θ)| ≤ 2 * A * B := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul]
    calc 2 * (|deriv f θ| * |deriv g θ|) ≤ 2 * (A * B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hA hB (abs_nonneg _) hA0) (by norm_num)
      _ = 2 * A * B := by ring
  have h3 : |f θ * deriv (deriv g) θ| ≤ B' := by
    rw [abs_mul]
    calc |f θ| * |deriv (deriv g) θ| ≤ 1 * B' :=
          mul_le_mul hfn hB' (abs_nonneg _) (by norm_num)
      _ = B' := one_mul B'
  calc |deriv (deriv f) θ * g θ + 2 * (deriv f θ * deriv g θ) + f θ * deriv (deriv g) θ|
      ≤ |deriv (deriv f) θ * g θ + 2 * (deriv f θ * deriv g θ)| + |f θ * deriv (deriv g) θ| :=
        abs_add_le _ _
    _ ≤ (|deriv (deriv f) θ * g θ| + |2 * (deriv f θ * deriv g θ)|)
          + |f θ * deriv (deriv g) θ| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ A' + 2 * A * B + B' := by linarith

end Work.FTS.PhiStar.Series
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.abs_deriv_mul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series

lemma abs_deriv_mul_le {f g : ℝ → ℝ} {θ : ℝ} (hf : DifferentiableAt ℝ f θ)
    (hg : DifferentiableAt ℝ g θ) {A B : ℝ} (hA : |deriv f θ| ≤ A) (hB : |deriv g θ| ≤ B)
    (hf0 : 0 ≤ f θ) (hf1 : f θ ≤ 1) (hg0 : 0 ≤ g θ) (hg1 : g θ ≤ 1) :
    |deriv (f * g) θ| ≤ A + B := by
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) hA
  have hgabs : |g θ| ≤ 1 := abs_le.2 ⟨by linarith, hg1⟩
  have hfabs : |f θ| ≤ 1 := abs_le.2 ⟨by linarith, hf1⟩
  have h1 : |deriv f θ * g θ| ≤ A := by
    rw [abs_mul]
    calc |deriv f θ| * |g θ| ≤ A * 1 :=
          mul_le_mul hA hgabs (abs_nonneg _) hA0
      _ = A := mul_one A
  have h2 : |f θ * deriv g θ| ≤ B := by
    rw [abs_mul]
    calc |f θ| * |deriv g θ| ≤ 1 * B :=
          mul_le_mul hfabs hB (abs_nonneg _) (by norm_num)
      _ = B := one_mul B
  rw [deriv_mul hf hg]
  calc |deriv f θ * g θ + f θ * deriv g θ|
      ≤ |deriv f θ * g θ| + |f θ * deriv g θ| := abs_add_le _ _
    _ ≤ A + B := add_le_add h1 h2

end Work.FTS.PhiStar.Series
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.exists_layer_small =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series

/-- If `f` is continuous on `[0, π/2]` and vanishes at both endpoints, then `f` is uniformly
small on a pair of boundary layers `[0, ρ] ∪ [π/2 - ρ, π/2]` of the interval.  This is just
the one-sided continuity of `f` at the two endpoints. -/
theorem exists_layer_small (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : ℝ,
      (θ ∈ Set.Icc 0 ρ ∨ θ ∈ Set.Icc (Real.pi / 2 - ρ) (Real.pi / 2)) → |f θ| < ε := by
  intro ε hε
  have hπ : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_refl 0, hπ.le⟩
  have hmem1 : Real.pi / 2 ∈ Set.Icc 0 (Real.pi / 2) := ⟨hπ.le, le_refl _⟩
  obtain ⟨δ₁, hδ₁, hb₁⟩ := (Metric.continuousWithinAt_iff.mp (hf.continuousWithinAt hmem0)) ε hε
  obtain ⟨δ₂, hδ₂, hb₂⟩ := (Metric.continuousWithinAt_iff.mp (hf.continuousWithinAt hmem1)) ε hε
  set ρ : ℝ := min (min (δ₁ / 2) (δ₂ / 2)) (Real.pi / 2) with hρdef
  have hρ1 : ρ ≤ δ₁ / 2 := hρdef ▸ le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ2 : ρ ≤ δ₂ / 2 := hρdef ▸ le_trans (min_le_left _ _) (min_le_right _ _)
  have hρπ : ρ ≤ Real.pi / 2 := hρdef ▸ min_le_right _ _
  have hρpos : 0 < ρ := hρdef ▸ lt_min (lt_min (by linarith) (by linarith)) hπ
  refine ⟨ρ, hρpos, ?_⟩
  intro θ hθ
  rcases hθ with ⟨hθ0, hθρ⟩ | ⟨hθa, hθb⟩
  · -- left layer: `θ` is close to `0`
    have hs : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨hθ0, le_trans hθρ hρπ⟩
    have hd : dist θ 0 < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hθ0]
      linarith [le_trans hθρ hρ1]
    have := hb₁ hs hd
    rw [h0, Real.dist_eq, sub_zero] at this
    exact this
  · -- right layer: `θ` is close to `π/2`
    have hs : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨by linarith [hθa, hρπ], hθb⟩
    have hd : dist θ (Real.pi / 2) < δ₂ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith : θ - Real.pi / 2 ≤ 0),
        show -(θ - Real.pi / 2) = Real.pi / 2 - θ from by ring]
      have : Real.pi / 2 - θ ≤ ρ := by linarith
      linarith [hρ2, hδ₂]
    have := hb₂ hs hd
    rw [h1, Real.dist_eq, sub_zero] at this
    exact this

end Work.FTS.PhiStar.Series
end
-- ===== merged: Submission.Work.FTS.PhiStar.sin_rpow_slack =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar

/-- For `0 < α ≤ 1` and `0 ≤ s ≤ 1` the quantity `s ^ (1 - α / 5) / (α + s)` is at most `2`.

In fact it is at most `1`: writing `δ = α/5 ∈ (0, 1/5]` and using the weighted AM–GM
inequality (concavity of `x ↦ x ^ δ`) in the form `y ^ δ ≤ δ * y + (1 - δ)` for `y ≥ 0`
with `y = 1/s` gives `s ^ (1 - δ) ≤ s + δ * (1 - s) ≤ s + α`, whence
`s ^ (1 - α/5) / (α + s) ≤ 1`. -/
theorem sin_rpow_slack {α s : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ (1 - α / 5) / (α + s) ≤ 2 := by
  have hδ0 : 0 ≤ α / 5 := by linarith
  rcases eq_or_lt_of_le hs0 with hs | hs
  · subst hs
    rw [Real.zero_rpow (by intro h; linarith), zero_div]
    norm_num
  · have hαs : 0 < α + s := by linarith
    -- weighted AM–GM with weights `α/5` and `1 - α/5` applied to `1/s` and `1`
    have hamgm : (1 / s) ^ (α / 5) * (1 : ℝ) ^ (1 - α / 5)
        ≤ (α / 5) * (1 / s) + (1 - α / 5) * 1 :=
      Real.geom_mean_le_arith_mean2_weighted hδ0 (by linarith) (by positivity) (by norm_num)
        (by ring)
    have hamgm' : (1 / s) ^ (α / 5) ≤ (α / 5) * (1 / s) + (1 - α / 5) := by
      simpa using hamgm
    -- `s ^ (1 - α/5) = s * (1/s) ^ (α/5)`
    have hsp : s ^ (1 - α / 5) = s * (1 / s) ^ (α / 5) := by
      rw [Real.rpow_sub hs, Real.rpow_one, one_div, Real.inv_rpow hs0, div_eq_mul_inv]
    have h1 : s * ((α / 5) * (1 / s)) = α / 5 := by
      field_simp
    have h2 : s * (1 - α / 5) ≤ s := by
      have hle : 1 - α / 5 ≤ 1 := by linarith
      simpa using mul_le_mul_of_nonneg_left hle hs0
    have hfin : s * ((α / 5) * (1 / s) + (1 - α / 5)) ≤ α + s := by
      rw [mul_add, h1]
      linarith
    -- the key estimate `s ^ (1 - α/5) ≤ α + s`
    have hkey : s ^ (1 - α / 5) ≤ α + s := by
      rw [hsp]
      exact le_trans (mul_le_mul_of_nonneg_left hamgm' hs0) hfin
    have hle1 : s ^ (1 - α / 5) / (α + s) ≤ 1 := by
      have := div_le_div_of_nonneg_right hkey hαs.le
      rwa [div_self (ne_of_gt hαs)] at this
    linarith

end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.Physical.Pressure.curlCompSelf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.Pressure




end Work.FTS.Physical.Pressure
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.fderiv_fderiv_comm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

theorem fderiv_fderiv_comm (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hW : ∀ n : ℕ, ContDiff ℝ n W) (x a b : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => fderiv ℝ W w a) x b
      = fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => fderiv ℝ W w b) x a := by
  -- The two sides are the two mixed second derivatives of `W` at `x`, evaluated on the
  -- constant vector fields `a` and `b`; their difference is the derivative of `W` along the
  -- Lie bracket `[a, b] = 0` of two constant vector fields.
  have h2 : ContDiffAt ℝ 2 W x := (hW 2).contDiffAt
  have hsymm : IsSymmSndFDerivAt ℝ W x := h2.isSymmSndFDerivAt (by simp)
  have h := VectorField.fderiv_apply_lieBracket_of_isSymmSndFDerivAt
    (𝕜 := ℝ) (f := W)
    (V := fun _ : EuclideanSpace ℝ (Fin 3) => b)
    (W := fun _ : EuclideanSpace ℝ (Fin 3) => a)
    h2 hsymm (differentiableAt_const a) (differentiableAt_const b)
  simp only [VectorField.lieBracket, map_sub] at h
  simp at h
  exact sub_eq_zero.mp h.symm

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.ihak_r_exp_gauss_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Gaussian decay comparison `r e^{-r²/4t} ≤ 2√t e^{-r²/8t}`

For `t > 0` the linear factor `r` is dominated by the *slower* Gaussian
`exp (r²/(8t))`, which together with `exp (-(r²/(4t))) = exp (-(r²/(8t))) · exp (-(r²/(8t)))`
yields the elementary estimate
`r * exp (-(r²/(4t))) ≤ 2 √t * exp (-(r²/(8t)))`.

The only analytic input is `Real.add_one_le_exp` (`1 + x ≤ exp x`); the rest is the
elementary quadratic inequality `r² - 4√t r + 8t = (r - 2√t)² + 4t ≥ 0`.
-/

set_option linter.unusedVariables false

namespace Work.FTS.PressureOn.Auxiliary

theorem ihak_r_exp_gauss_le (t r : ℝ) (ht : 0 < t) (hr : 0 ≤ r) :
    r * Real.exp (-(r ^ 2 / (4 * t))) ≤ 2 * Real.sqrt t * Real.exp (-(r ^ 2 / (8 * t))) := by
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt (le_of_lt ht)
  have h4s : (0 : ℝ) < 4 * Real.sqrt t := by positivity
  -- `r ≤ 2√t e^{r²/8t}`: it suffices to bound the exponential below by its first
  -- Taylor polynomial, `e^{u} ≥ 1 + u`, and compare quadratics.
  have hpoly : r - 2 * Real.sqrt t ≤ r ^ 2 / (4 * Real.sqrt t) := by
    rw [le_div_iff₀ h4s]
    nlinarith [sq_nonneg (r - 2 * Real.sqrt t), hs2, ht]
  have hexp : 1 + r ^ 2 / (8 * t) ≤ Real.exp (r ^ 2 / (8 * t)) := by
    have h := Real.add_one_le_exp (r ^ 2 / (8 * t))
    linarith
  have h2 : 2 * Real.sqrt t * (1 + r ^ 2 / (8 * t))
      = 2 * Real.sqrt t + r ^ 2 / (4 * Real.sqrt t) := by
    field_simp
    rw [hs2]
    ring
  have h1 : r ≤ 2 * Real.sqrt t * Real.exp (r ^ 2 / (8 * t)) := by
    calc r = (r - 2 * Real.sqrt t) + 2 * Real.sqrt t := by ring
      _ ≤ r ^ 2 / (4 * Real.sqrt t) + 2 * Real.sqrt t := by linarith [hpoly]
      _ = 2 * Real.sqrt t * (1 + r ^ 2 / (8 * t)) := by rw [h2]; ring
      _ ≤ 2 * Real.sqrt t * Real.exp (r ^ 2 / (8 * t)) := by
            exact mul_le_mul_of_nonneg_left hexp (by positivity)
  -- multiply `h1` by `exp (-(r²/4t)) = exp (-(r²/8t)) · exp (-(r²/8t))`
  have harg : r ^ 2 / (8 * t) + -(r ^ 2 / (4 * t)) = -(r ^ 2 / (8 * t)) := by
    field_simp
    ring
  calc r * Real.exp (-(r ^ 2 / (4 * t)))
      ≤ (2 * Real.sqrt t * Real.exp (r ^ 2 / (8 * t))) * Real.exp (-(r ^ 2 / (4 * t))) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = 2 * Real.sqrt t * (Real.exp (r ^ 2 / (8 * t)) * Real.exp (-(r ^ 2 / (4 * t)))) := by ring
    _ = 2 * Real.sqrt t * Real.exp (-(r ^ 2 / (8 * t))) := by
          rw [← Real.exp_add, harg]

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.integrable_uncurry_mul_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of `(x, t) ↦ ρ t * a x * b (x - t)`

The product `ρ t * a x * b (x - t)` is integrable for the product of Lebesgue measures on
`ℝ³ × ℝ³` as soon as `ρ` and `b` are continuous with compact support (and `a` is merely
continuous).  The point is that the integrand *vanishes outside the compact set*

`K := (tsupport ρ + tsupport b) ×ˢ tsupport ρ`

(indeed `ρ t * a x * b (x - t) ≠ 0` forces `t ∈ tsupport ρ` and `x - t ∈ tsupport b`, whence
`x = t + (x - t) ∈ tsupport ρ + tsupport b`), so the integrand is a continuous function with
compact support and Mathlib's `Continuous.integrable_of_hasCompactSupport` applies.  No
boundedness assumption on `a` is needed: its argument is confined to `tsupport ρ + tsupport b`.

This is the lemma consumed by the pressure reconstruction: after the change of variables that
turns a convolution against the Newtonian kernel into an integral over `(x, t)`, the resulting
double integral has this exact shape.
-/

open MeasureTheory Function
open scoped Pointwise

namespace Work.FTS.PressureOn.Auxiliary

theorem integrable_uncurry_mul_sub (a b ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hρ : Continuous ρ)
    (hbc : HasCompactSupport b) (hρc : HasCompactSupport ρ) :
    MeasureTheory.Integrable
      (Function.uncurry fun (x t : EuclideanSpace ℝ (Fin 3)) => ρ t * a x * b (x - t))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  -- the integrand, packaged as a function of the pair `(x, t)`
  set K : Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
    (tsupport ρ + tsupport b) ×ˢ tsupport ρ with hKdef
  -- it is continuous
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ρ p.2 * a p.1 * b (p.1 - p.2)) :=
    ((hρ.comp continuous_snd).mul (ha.comp continuous_fst)).mul
      (hb.comp (continuous_fst.sub continuous_snd))
  -- and its support is contained in the compact set `K`
  have hsupp : Function.support (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ρ p.2 * a p.1 * b (p.1 - p.2)) ⊆ K := by
    intro p hp
    rw [Function.mem_support] at hp
    have hρne : ρ p.2 ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).1
    have hbne : b (p.1 - p.2) ≠ 0 := (mul_ne_zero_iff.mp hp).2
    have h2 : p.2 ∈ tsupport ρ := subset_tsupport ρ (Function.mem_support.mpr hρne)
    have h1 : p.1 - p.2 ∈ tsupport b := subset_tsupport b (Function.mem_support.mpr hbne)
    rw [hKdef]
    refine Set.mem_prod.mpr ⟨?_, h2⟩
    rw [Set.mem_add]
    exact ⟨p.2, h2, p.1 - p.2, h1, by abel⟩
  have hK : IsCompact K := by rw [hKdef]; exact IsCompact.add hρc hbc |>.prod hρc
  have hcs : HasCompactSupport (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ρ p.2 * a p.1 * b (p.1 - p.2)) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal hsupp hK.isClosed)
  exact hcont.integrable_of_hasCompactSupport hcs

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.integrable_uncurry_mul_sub_left =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

theorem integrable_uncurry_mul_sub_left (a b ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hρ : Continuous ρ)
    (hac : HasCompactSupport a) (hρc : HasCompactSupport ρ) :
    MeasureTheory.Integrable
      (Function.uncurry fun (x t : EuclideanSpace ℝ (Fin 3)) => ρ t * a x * b (x - t))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  -- The integrand is continuous and supported in `tsupport a ×ˢ tsupport ρ`, a compact set.
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ρ p.2 * a p.1 * b (p.1 - p.2)) :=
    ((hρ.comp continuous_snd).mul (ha.comp continuous_fst)).mul
      (hb.comp (continuous_fst.sub continuous_snd))
  have hsupp : HasCompactSupport (fun p : EuclideanSpace ℝ (Fin 3) ×
      EuclideanSpace ℝ (Fin 3) => ρ p.2 * a p.1 * b (p.1 - p.2)) := by
    have hle : Function.support (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          a p.1 * ρ p.2) ⊆ Function.support a ×ˢ Function.support ρ := by
      intro p hp
      simp only [Function.mem_support, Set.mem_prod] at hp ⊢
      exact ⟨fun h => hp (by rw [h, zero_mul]), fun h => hp (by rw [h, mul_zero])⟩
    have hA : HasCompactSupport (fun p : EuclideanSpace ℝ (Fin 3) ×
        EuclideanSpace ℝ (Fin 3) => a p.1 * ρ p.2) := by
      refine (hac.isCompact.prod hρc.isCompact).of_isClosed_subset (isClosed_tsupport _) ?_
      calc tsupport (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
              a p.1 * ρ p.2)
          = closure (Function.support fun p : EuclideanSpace ℝ (Fin 3) ×
              EuclideanSpace ℝ (Fin 3) => a p.1 * ρ p.2) := rfl
        _ ⊆ closure (Function.support a ×ˢ Function.support ρ) := closure_mono hle
        _ = closure (Function.support a) ×ˢ closure (Function.support ρ) := closure_prod_eq
        _ = tsupport a ×ˢ tsupport ρ := rfl
    refine hA.mono (fun p hp => ?_)
    rw [Function.mem_support] at hp ⊢
    intro h
    exact hp (by rw [mul_comm (ρ p.2) (a p.1), h, zero_mul])
  exact hcont.integrable_of_hasCompactSupport hsupp

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.integral_inner_convolution_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PressureOn.Auxiliary

theorem integral_inner_convolution_eq
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hΦ : Continuous Φ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (heven : ∀ z, ρ (-z) = ρ z)
    (hα : MeasureTheory.Integrable (Function.uncurry fun (x t : EuclideanSpace ℝ (Fin 3)) =>
        ρ t * inner ℝ (Φ x) (f (x - t))) (MeasureTheory.volume.prod MeasureTheory.volume))
    (hβ : MeasureTheory.Integrable (Function.uncurry fun (x t : EuclideanSpace ℝ (Fin 3)) =>
        ρ t * inner ℝ (Φ (x - t)) (f x)) (MeasureTheory.volume.prod MeasureTheory.volume)) :
    ∫ x, inner ℝ (Φ x)
        (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = ∫ x, inner ℝ
          (MeasureTheory.convolution ρ Φ (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
          (f x) := by
  -- Step 1: unfold the convolution and pull the inner product inside the integral.
  have hpt1 : ∀ x, inner ℝ (Φ x)
      (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = ∫ t, ρ t * inner ℝ (Φ x) (f (x - t)) := by
    intro x
    have hint : Integrable (fun t : EuclideanSpace ℝ (Fin 3) => ρ t • f (x - t)) :=
      (hf.comp (continuous_const.sub continuous_id)).locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        hρ hρc
    have hkey : (innerSL ℝ (Φ x)) (∫ t, ρ t • f (x - t))
        = ∫ t, (innerSL ℝ (Φ x)) (ρ t • f (x - t)) :=
      (ContinuousLinearMap.integral_comp_comm (innerSL ℝ (Φ x)) hint).symm
    rw [MeasureTheory.convolution_lsmul]
    rw [← innerSL_apply_apply, hkey]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [innerSL_apply_apply, real_inner_smul_right]
  have hpt2 : ∀ x, inner ℝ
      (MeasureTheory.convolution ρ Φ (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      (f x) = ∫ t, ρ t * inner ℝ (Φ (x - t)) (f x) := by
    intro x
    have hint : Integrable (fun t : EuclideanSpace ℝ (Fin 3) => ρ t • Φ (x - t)) :=
      (hΦ.comp (continuous_const.sub continuous_id)).locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        hρ hρc
    have hkey : (innerSL ℝ (f x)) (∫ t, ρ t • Φ (x - t))
        = ∫ t, (innerSL ℝ (f x)) (ρ t • Φ (x - t)) :=
      (ContinuousLinearMap.integral_comp_comm (innerSL ℝ (f x)) hint).symm
    rw [MeasureTheory.convolution_lsmul, real_inner_comm]
    rw [← innerSL_apply_apply, hkey]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [innerSL_apply_apply, real_inner_smul_right, real_inner_comm]
  -- Now the chain of identities between iterated integrals.
  have key1 : ∫ x, inner ℝ (Φ x)
      (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = ∫ x, ∫ t, ρ t * inner ℝ (Φ x) (f (x - t)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    exact hpt1 x
  -- Fubini (from `hα`).
  have key2 : (∫ x, ∫ t, ρ t * inner ℝ (Φ x) (f (x - t)))
      = ∫ t, ∫ x, ρ t * inner ℝ (Φ x) (f (x - t)) :=
    MeasureTheory.integral_integral_swap hα
  -- Translate the inner variable: `x ↦ x + t`.
  have key3 : (∫ t, ∫ x, ρ t * inner ℝ (Φ x) (f (x - t)))
      = ∫ t, ∫ x, ρ t * inner ℝ (Φ (x + t)) (f x) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    simpa using (MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume)
      (fun y : EuclideanSpace ℝ (Fin 3) => ρ t * inner ℝ (Φ y) (f (y - t))) t).symm
  have h1 : ∀ t, (∫ x, ρ t * inner ℝ (Φ (x + t)) (f x))
      = ∫ x, ρ (-t) * inner ℝ (Φ (x - (-t))) (f x) := by
    intro t
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [← heven t, sub_neg_eq_add]
  -- `t ↦ -t` in the outer integral, using that `ρ` is even.
  have key4 : (∫ t, ∫ x, ρ t * inner ℝ (Φ (x + t)) (f x))
      = ∫ t, ∫ x, ρ t * inner ℝ (Φ (x - t)) (f x) := by
    calc ∫ t, ∫ x, ρ t * inner ℝ (Φ (x + t)) (f x)
        = ∫ t, ∫ x, ρ (-t) * inner ℝ (Φ (x - (-t))) (f x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          exact h1 t
      _ = ∫ t, (fun s => ∫ x, ρ s * inner ℝ (Φ (x - s)) (f x)) (-t) := rfl
      _ = ∫ t, (fun s => ∫ x, ρ s * inner ℝ (Φ (x - s)) (f x)) t :=
          MeasureTheory.integral_neg_eq_self
            (fun s => ∫ x, ρ s * inner ℝ (Φ (x - s)) (f x)) MeasureTheory.volume
      _ = ∫ t, ∫ x, ρ t * inner ℝ (Φ (x - t)) (f x) := rfl
  -- Fubini in the other direction (from `hβ`).
  have key45 : (∫ t, ∫ x, ρ t * inner ℝ (Φ (x - t)) (f x))
      = ∫ x, ∫ t, ρ t * inner ℝ (Φ (x - t)) (f x) :=
    (MeasureTheory.integral_integral_swap hβ).symm
  have key5 : (∫ x, ∫ t, ρ t * inner ℝ (Φ (x - t)) (f x))
      = ∫ x, inner ℝ
          (MeasureTheory.convolution ρ Φ (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
          (f x) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    exact (hpt2 x).symm
  exact key1.trans (key2.trans (key3.trans (key4.trans (key45.trans key5))))

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.integral_mul_convolution_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PressureOn.Auxiliary

/-- **Duality identity for a convolution against a multiplication.**

For scalar functions `q`, `b`, `ρ` on `ℝ³` with `ρ` even (and `b`, `ρ` compactly supported),
the pairing `∫ q · (ρ ⋆ b)` equals `∫ (ρ ⋆ q) · b`.

The proof is the standard one: unfold both convolutions with `convolution_lsmul`, distribute
the pointwise factor into the integral (`integral_const_mul` / `integral_mul_const`), apply
Fubini (`integral_integral_swap`, the two integrability hypotheses are exactly the Fubini
hypotheses), and then observe that the two double integrals agree after the change of
variables `t ↦ -t` in the outer variable (using `heven`) and `x ↦ x + t` in the inner one
(`integral_sub_right_eq_self`). -/
theorem integral_mul_convolution_eq
    (q b : EuclideanSpace ℝ (Fin 3) → ℝ)
    (ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hq : Continuous q) (hb : Continuous b) (hbc : HasCompactSupport b)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (heven : ∀ z, ρ (-z) = ρ z)
    (hγ : MeasureTheory.Integrable (Function.uncurry fun (x t : EuclideanSpace ℝ (Fin 3)) =>
        q x * (ρ t * b (x - t))) (MeasureTheory.volume.prod MeasureTheory.volume))
    (hδ : MeasureTheory.Integrable (Function.uncurry fun (x t : EuclideanSpace ℝ (Fin 3)) =>
        (ρ t * q (x - t)) * b x) (MeasureTheory.volume.prod MeasureTheory.volume)) :
    ∫ x, q x * (MeasureTheory.convolution ρ b (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = ∫ x, (MeasureTheory.convolution ρ q (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
          * b x := by
  have hconvb : ∀ x,
      MeasureTheory.convolution ρ b (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
        = ∫ t, ρ t * b (x - t) := by
    intro x
    rw [MeasureTheory.convolution_lsmul]
    simp
  have hconvq : ∀ x,
      MeasureTheory.convolution ρ q (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
        = ∫ t, ρ t * q (x - t) := by
    intro x
    rw [MeasureTheory.convolution_lsmul]
    simp
  have hL : ∫ x, q x *
        (MeasureTheory.convolution ρ b (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = ∫ t, ∫ x, q x * (ρ t * b (x - t)) := by
    have h1 : (fun x => q x * (∫ t, ρ t * b (x - t)))
        = fun x => ∫ t, q x * (ρ t * b (x - t)) := by
      funext x
      exact (MeasureTheory.integral_const_mul (q x) (fun t => ρ t * b (x - t))).symm
    simp only [hconvb, h1]
    exact MeasureTheory.integral_integral_swap hγ
  have hR : ∫ x,
        (MeasureTheory.convolution ρ q (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x) * b x
      = ∫ t, ∫ x, (ρ t * q (x - t)) * b x := by
    have h1 : (fun x => (∫ t, ρ t * q (x - t)) * b x)
        = fun x => ∫ t, (ρ t * q (x - t)) * b x := by
      funext x
      exact (MeasureTheory.integral_mul_const (b x) (fun t => ρ t * q (x - t))).symm
    simp only [hconvq, h1]
    exact MeasureTheory.integral_integral_swap hδ
  rw [hL, hR]
  -- The two double integrals agree: for every `t` the inner integral of the right-hand side
  -- is the inner integral of the left-hand side at `-t` (change of variables `x ↦ x + t` in
  -- the inner integral, plus evenness of `ρ`).
  have hGF : ∀ t, (∫ x, (ρ t * q (x - t)) * b x)
      = ∫ x, q x * (ρ (-t) * b (x - (-t))) := by
    intro t
    have hstep : ∫ x, (ρ t * q (x - t)) * b x
        = ∫ u, (ρ t * q u) * b (u + t) := by
      have h := MeasureTheory.integral_sub_right_eq_self (μ := volume)
        (fun u : EuclideanSpace ℝ (Fin 3) => (ρ t * q u) * b (u + t)) t
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    rw [hstep]
    have h2 : ∫ u, (ρ t * q u) * b (u + t) = ∫ u, q u * (ρ t * b (u + t)) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      ring
    rw [h2]
    have h3 : ∫ u, q u * (ρ t * b (u + t)) = ∫ u, q u * (ρ (-t) * b (u + t)) := by
      rw [heven t]
    rw [h3]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [sub_neg_eq_add]
  calc ∫ t, ∫ x, q x * (ρ t * b (x - t))
      = ∫ t, (fun s => ∫ x, q x * (ρ s * b (x - s))) t := rfl
    _ = ∫ t, (fun s => ∫ x, q x * (ρ s * b (x - s))) (-t) :=
        (MeasureTheory.integral_neg_eq_self (fun s => ∫ x, q x * (ρ s * b (x - s))) volume).symm
    _ = ∫ t, ∫ x, (ρ t * q (x - t)) * b x := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        exact (hGF t).symm

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.tendsto_cocompact_bound_scalar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

theorem tendsto_cocompact_bound_scalar {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : Continuous g)
    (hg0 : Filter.Tendsto g (Filter.cocompact (EuclideanSpace ℝ (Fin 3))) (nhds 0)) :
    (∃ C : ℝ, ∀ x, |g x| ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → |g x| ≤ ε) := by
  -- From `hg0` we extract, for every `ε > 0`, that the set `{x | |g x| < ε}` belongs to
  -- the cocompact filter, i.e. its complement is contained in a compact set.
  have hbdd : ∃ C : ℝ, ∀ x, |g x| ≤ C := by
    have hmem : {x : EuclideanSpace ℝ (Fin 3) | |g x| < 1} ∈ Filter.cocompact _ := by
      have h := hg0 (Metric.ball_mem_nhds (0 : ℝ) one_pos)
      rw [Filter.mem_map] at h
      rwa [show g ⁻¹' Metric.ball (0 : ℝ) 1 = {x : EuclideanSpace ℝ (Fin 3) | |g x| < 1} from by
        ext x; simp [Metric.mem_ball]] at h
    obtain ⟨K, hKc, hKsub⟩ := Filter.mem_cocompact.1 hmem
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
    refine ⟨max M 1, fun x => ?_⟩
    by_cases hx : x ∈ K
    · have h := hM x hx
      rw [Real.norm_eq_abs] at h
      exact h.trans (le_max_left _ _)
    · have h := hKsub (by simpa using hx)
      exact (le_of_lt h).trans (le_max_right _ _)
  refine ⟨hbdd, fun ε hε => ?_⟩
  have hmem : {x : EuclideanSpace ℝ (Fin 3) | |g x| < ε} ∈ Filter.cocompact _ := by
    have h := hg0 (Metric.ball_mem_nhds (0 : ℝ) hε)
    rw [Filter.mem_map] at h
    rwa [show g ⁻¹' Metric.ball (0 : ℝ) ε = {x : EuclideanSpace ℝ (Fin 3) | |g x| < ε} from by
      ext x; simp [Metric.mem_ball]] at h
  obtain ⟨K, hKc, hKsub⟩ := Filter.mem_cocompact.1 hmem
  obtain ⟨R, -, hR⟩ := hKc.isBounded.exists_pos_norm_lt
  refine ⟨R, fun x hx => ?_⟩
  have hxK : x ∉ K := fun h => absurd hx (not_le.2 (hR x h))
  exact le_of_lt (hKsub (by simpa using hxK))

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.tendsto_integral_of_compact_support =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

theorem tendsto_integral_of_compact_support {F : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ}
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {C : ℝ}
    (hK : IsCompact K) (hC : 0 ≤ C)
    (hFmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (F n) MeasureTheory.volume)
    (hFsupp : ∀ n, Function.support (F n) ⊆ K)
    (hfsupp : Function.support f ⊆ K)
    (hFbound : ∀ n x, ‖F n x‖ ≤ C)
    (hlim : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x))) :
    Filter.Tendsto (fun n => ∫ x, F n x) Filter.atTop (nhds (∫ x, f x)) := by
  have _ := hC
  have hKfin : MeasureTheory.volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hbound_int : MeasureTheory.Integrable (fun _ : EuclideanSpace ℝ (Fin 3) => C)
      (MeasureTheory.volume.restrict K) :=
    MeasureTheory.integrableOn_const hKfin
  have key : Filter.Tendsto (fun n => ∫ x, F n x ∂(MeasureTheory.volume.restrict K))
      Filter.atTop (nhds (∫ x, f x ∂(MeasureTheory.volume.restrict K))) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence (μ := MeasureTheory.volume.restrict K)
      (fun _ => C)
      (fun n => (hFmeas n).restrict)
      hbound_int
      (fun n => Filter.Eventually.of_forall (fun x => hFbound n x))
      (Filter.Eventually.of_forall (fun x => hlim x))
  have hFn : ∀ n, (∫ x in K, F n x) = ∫ x, F n x := fun n =>
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      by_contra h; exact hx (hFsupp n h))
  have hf : (∫ x in K, f x) = ∫ x, f x :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      by_contra h; exact hx (hfsupp h))
  rw [hf] at key
  exact key.congr' (Filter.Eventually.of_forall hFn)

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.BoundaryTime.deriv_zero_of_eq_zero_on_Icc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect.BoundaryTime

theorem deriv_zero_of_eq_zero_on_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} {S t : ℝ} (hS : 0 < S) (hg : ∀ s ∈ Set.Icc 0 S, g s = 0)
    (ht : t ∈ Set.Icc 0 S) : deriv g t = 0 := by
  -- On the interval `Icc 0 S` the function `g` agrees with the constant `0`, so it has the
  -- one-sided (within `Icc 0 S`) derivative `0` at every point of the interval.  Since
  -- `Icc 0 S` is a convex set with nonempty interior (as `0 < S`), it is a set of unique
  -- differentiability, so the two-sided derivative `deriv g t` must equal that one-sided
  -- derivative.  (This covers the endpoints `t = 0` and `t = S` as well: `deriv` is the
  -- two-sided derivative, and if it exists it agrees with the one within the interval.)
  exact HasDerivWithinAt.deriv_eq_zero
    ((hasDerivWithinAt_const (x := t) (s := Set.Icc 0 S) (c := (0 : E))).congr
      hg (hg t ht))
    ((uniqueDiffOn_Icc hS).uniqueDiffWithinAt ht)

end Work.FTS.PressureOn.Connect.BoundaryTime
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.BoundaryTime.norm_sub_fderiv_le_of_convex =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect.BoundaryTime

/-- Mean value inequality on a convex set, with the increment measured against the (fixed)
derivative `L x` at the base point `x` and the error controlled by the uniform bound `η` on
`‖L z - L x‖`, `z ∈ B`.  Immediate from Mathlib's
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`. -/
theorem norm_sub_fderiv_le_of_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : Set E} (hB : Convex ℝ B) {f : E → F} {L : E → E →L[ℝ] F} {x : E} {η : ℝ}
    (hx : x ∈ B) (hd : ∀ z ∈ B, HasFDerivAt f (L z) z)
    (hb : ∀ z ∈ B, ‖L z - L x‖ ≤ η) :
    ∀ w ∈ B, ‖f w - f x - L x (w - x)‖ ≤ η * ‖w - x‖ := by
  intro w hw
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (s := B) (f := f) (f' := L)
    (φ := L x) (C := η) (fun z hz => (hd z hz).hasFDerivWithinAt) (fun z hz => hb z hz) hB hx hw

end Work.FTS.PressureOn.Connect.BoundaryTime
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.BoundaryTime.rightDeriv_zero_of_hasDerivAt_Ioo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.PressureOn.Connect.BoundaryTime

theorem rightDeriv_zero_of_hasDerivAt_Ioo
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {g c : ℝ → F} {S : ℝ} (hS : 0 < S)
    (hg : ContinuousOn g (Set.Icc 0 S)) (hc : ContinuousOn c (Set.Icc 0 S))
    (h : ∀ t ∈ Set.Ioo 0 S, HasDerivAt g (c t) t) :
    HasDerivWithinAt g (c 0) (Set.Ici 0) 0 ∧
    (∀ C : ℝ, (∀ t ∈ Set.Ioo 0 S, ‖c t - c 0‖ ≤ C) →
      ∀ t ∈ Set.Icc 0 S, ‖g t - g 0 - t • c 0‖ ≤ C * t) := by
  -- `Ioo 0 S` is a right neighbourhood of `0`, and on it `deriv g` agrees with `c`; hence `c`
  -- has the limit `c 0` along `𝓝[>] 0`.
  have hmem : Set.Ioo (0 : ℝ) S ∈ 𝓝[>] (0 : ℝ) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hS]
    exact self_mem_nhdsWithin
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Set.Icc 0 S] (0 : ℝ) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hS]
    exact nhdsWithin_mono 0 Set.Ioo_subset_Icc_self
  have hct : Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 (c 0)) :=
    (hc.continuousWithinAt ⟨le_rfl, hS.le⟩).mono_left hle
  have hderiv_eq : (fun x => deriv g x) =ᶠ[𝓝[>] (0 : ℝ)] c := by
    filter_upwards [hmem] with x hx
    exact (h x hx).deriv
  -- First conjunct: right differentiability of `g` at `0`, with derivative the limit of `c`.
  have hdiff : DifferentiableOn ℝ g (Set.Ioo 0 S) :=
    fun x hx => (h x hx).differentiableAt.differentiableWithinAt
  have hcontW : ContinuousWithinAt g (Set.Ioo 0 S) (0 : ℝ) :=
    (hg.continuousWithinAt ⟨le_rfl, hS.le⟩).mono Set.Ioo_subset_Icc_self
  have hfirst : HasDerivWithinAt g (c 0) (Set.Ici 0) 0 :=
    hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo 0 S) (a := (0 : ℝ)) (e := c 0)
      (f := g) hdiff hcontW hmem (Filter.Tendsto.congr' hderiv_eq.symm hct)
  refine ⟨hfirst, ?_⟩
  -- Second conjunct: the mean value inequality for `φ t = g t - g 0 - t • c 0`.
  intro C hC
  have hC0 : 0 ≤ C := by
    have ht : S / 2 ∈ Set.Ioo (0 : ℝ) S := ⟨by linarith, by linarith⟩
    have := hC (S / 2) ht
    linarith [norm_nonneg (c (S / 2) - c 0)]
  have hφcont : ContinuousOn (fun x : ℝ => g x - g 0 - x • c 0) (Set.Icc 0 S) :=
    (hg.sub continuousOn_const).sub (continuousOn_id.smul continuousOn_const)
  have hfun : ((g - fun _ : ℝ => g 0) - fun y : ℝ => y • c 0)
      = (fun y : ℝ => g y - g 0 - y • c 0) := by
    funext y; simp [Pi.sub_apply]
  have hφderiv : ∀ x ∈ Set.Ico (0 : ℝ) S,
      HasDerivWithinAt (fun y : ℝ => g y - g 0 - y • c 0) (c x - c 0) (Set.Ici x) x := by
    intro x hx
    rcases lt_or_eq_of_le hx.1 with hxpos | hxeq
    · have h1 : HasDerivWithinAt g (c x) (Set.Ici x) x :=
        (h x ⟨hxpos, hx.2⟩).hasDerivWithinAt
      have h2 : HasDerivWithinAt (fun y : ℝ => y • c 0) (c 0) (Set.Ici x) x := by
        simpa using ((hasDerivAt_id x).smul_const (c 0)).hasDerivWithinAt
      have h3 := (h1.sub (hasDerivWithinAt_const x (Set.Ici x) (g 0))).sub h2
      rw [hfun] at h3
      simpa using h3
    · obtain rfl : x = 0 := hxeq.symm
      have h1 : HasDerivWithinAt (fun y : ℝ => y • c 0) (c 0) (Set.Ici (0 : ℝ)) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (c 0)).hasDerivWithinAt
      have h2 := (hfirst.sub (hasDerivWithinAt_const (0 : ℝ) (Set.Ici (0 : ℝ)) (g 0))).sub h1
      rw [hfun] at h2
      simpa using h2
  have hφbound : ∀ x ∈ Set.Ico (0 : ℝ) S, ‖c x - c 0‖ ≤ C := by
    intro x hx
    rcases lt_or_eq_of_le hx.1 with hxpos | hxeq
    · exact hC x ⟨hxpos, hx.2⟩
    · obtain rfl : x = 0 := hxeq.symm
      simpa using hC0
  intro t ht
  have hmain := norm_image_sub_le_of_norm_deriv_right_le_segment (a := (0 : ℝ)) (b := S)
    (f := fun y : ℝ => g y - g 0 - y • c 0) (f' := fun x => c x - c 0) (C := C)
    hφcont hφderiv hφbound t ht
  simpa using hmain

end Work.FTS.PressureOn.Connect.BoundaryTime
end
-- ===== merged: Submission.Work.FTS.PressureOn.Green.integral_quartic_exp_neg_mul_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Green



end Work.FTS.PressureOn.Green
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.deriv_deriv_comp_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.PoissonAux

theorem deriv_deriv_comp_sq (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (deriv (fun r : ℝ => F (r ^ 2))) ρ + 2 * deriv (fun r : ℝ => F (r ^ 2)) ρ / ρ
      = 6 * deriv F (ρ ^ 2) + 4 * ρ ^ 2 * deriv (deriv F) (ρ ^ 2) := by
  have hDiffF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hDiffdF : Differentiable ℝ (deriv F) := hF.differentiable_deriv_two
  -- First derivative: `deriv (fun r => F (r^2)) = fun r => 2 * r * deriv F (r^2)`.
  have hGfun : deriv (fun r : ℝ => F (r ^ 2)) = fun r => 2 * r * deriv F (r ^ 2) := by
    funext r
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have h2 : HasDerivAt F (deriv F (r ^ 2)) (r ^ 2) :=
      (hDiffF.differentiableAt (x := r ^ 2)).hasDerivAt
    have h3 : HasDerivAt (fun s : ℝ => F (s ^ 2)) (deriv F (r ^ 2) * (2 * r)) r :=
      h2.comp_of_eq r h1 rfl
    rw [h3.deriv]; ring
  -- Second derivative at `ρ`.
  have hH : deriv (deriv (fun r : ℝ => F (r ^ 2))) ρ
      = 2 * deriv F (ρ ^ 2) + 4 * ρ ^ 2 * deriv (deriv F) (ρ ^ 2) := by
    rw [hGfun]
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * ρ) ρ := by
      simpa using hasDerivAt_pow 2 ρ
    have h2 : HasDerivAt (deriv F) (deriv (deriv F) (ρ ^ 2)) (ρ ^ 2) :=
      (hDiffdF.differentiableAt (x := ρ ^ 2)).hasDerivAt
    have h3 : HasDerivAt (fun s : ℝ => deriv F (s ^ 2))
        (deriv (deriv F) (ρ ^ 2) * (2 * ρ)) ρ := h2.comp_of_eq ρ h1 rfl
    have h4 : HasDerivAt (fun s : ℝ => 2 * s) 2 ρ := by
      simpa using (hasDerivAt_id ρ).const_mul 2
    have h5 : HasDerivAt (fun s : ℝ => 2 * s * deriv F (s ^ 2))
        (2 * deriv F (ρ ^ 2) + (2 * ρ) * (deriv (deriv F) (ρ ^ 2) * (2 * ρ))) ρ :=
      h4.mul h3
    rw [h5.deriv]; ring
  rw [hH, hGfun]
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  field_simp
  ring

end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.oneDim_radial_laplace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The one-dimensional radial Laplace identity

For a `C²` function `h` and `ρ > 0` we compute, with `f(r) = h(r)/(4π r)`,

`f'(r) = h'(r)/(4π r) - h(r)/(4π r²)`,   `f''(r) = h''(r)/(4π r) - 2h'(r)/(4π r²) + 2h(r)/(4π r³)`,

so that `f''(ρ) + 2 f'(ρ)/ρ = h''(ρ)/(4π ρ)`.  This is the radial part of the Laplacian
applied to `h(|x|)/(4π|x|)`; it is the identity used to evaluate the Poisson kernel on
radially symmetric data.
-/

namespace Work.FTS.PressureOn.PoissonAux

/-- Derivative of `r ↦ f r / (c * r)` at a point `ρ ≠ 0` (with `c ≠ 0`). -/
private lemma hasDerivAt_div_mul_id {f : ℝ → ℝ} {f' c ρ : ℝ} (hc : c ≠ 0) (hρ : ρ ≠ 0)
    (hf : HasDerivAt f f' ρ) :
    HasDerivAt (fun r : ℝ => f r / (c * r)) (f' / (c * ρ) - f ρ / (c * ρ ^ 2)) ρ := by
  have hg : HasDerivAt (fun r : ℝ => c * r) c ρ := by
    simpa using (hasDerivAt_id ρ).const_mul c
  have h := hf.div hg (mul_ne_zero hc hρ)
  convert h using 1
  field_simp

/-- Derivative of `r ↦ f r / (c * r ^ 2)` at a point `ρ ≠ 0` (with `c ≠ 0`). -/
private lemma hasDerivAt_div_mul_sq {f : ℝ → ℝ} {f' c ρ : ℝ} (hc : c ≠ 0) (hρ : ρ ≠ 0)
    (hf : HasDerivAt f f' ρ) :
    HasDerivAt (fun r : ℝ => f r / (c * r ^ 2)) (f' / (c * ρ ^ 2) - 2 * f ρ / (c * ρ ^ 3)) ρ := by
  have hg : HasDerivAt (fun r : ℝ => c * r ^ 2) (c * (2 * ρ)) ρ := by
    simpa using (hasDerivAt_pow 2 ρ).const_mul c
  have h := hf.div hg (by positivity)
  convert h using 1
  field_simp

theorem oneDim_radial_laplace (h : ℝ → ℝ) (hh : ContDiff ℝ 2 h) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (deriv (fun r : ℝ => h r / (4 * Real.pi * r))) ρ
        + 2 * deriv (fun r : ℝ => h r / (4 * Real.pi * r)) ρ / ρ
      = deriv (deriv h) ρ / (4 * Real.pi * ρ) := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hc : (4 * Real.pi) ≠ 0 := by positivity
  have hd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (deriv h) := hh.differentiable_deriv_two
  -- first derivative of `r ↦ h r / (4 π r)`
  have hF1 : HasDerivAt (fun r : ℝ => h r / (4 * Real.pi * r))
      (deriv h ρ / (4 * Real.pi * ρ) - h ρ / (4 * Real.pi * ρ ^ 2)) ρ :=
    hasDerivAt_div_mul_id hc hρne (hd.differentiableAt.hasDerivAt)
  -- the two summands of the derivative function, differentiated at `ρ`
  have hG1 : HasDerivAt (fun r : ℝ => deriv h r / (4 * Real.pi * r))
      (deriv (deriv h) ρ / (4 * Real.pi * ρ) - deriv h ρ / (4 * Real.pi * ρ ^ 2)) ρ :=
    hasDerivAt_div_mul_id hc hρne (hd1.differentiableAt.hasDerivAt)
  have hG2 : HasDerivAt (fun r : ℝ => h r / (4 * Real.pi * r ^ 2))
      (deriv h ρ / (4 * Real.pi * ρ ^ 2) - 2 * h ρ / (4 * Real.pi * ρ ^ 3)) ρ :=
    hasDerivAt_div_mul_sq hc hρne (hd.differentiableAt.hasDerivAt)
  have hG : HasDerivAt (fun r : ℝ => deriv h r / (4 * Real.pi * r) - h r / (4 * Real.pi * r ^ 2))
      ((deriv (deriv h) ρ / (4 * Real.pi * ρ) - deriv h ρ / (4 * Real.pi * ρ ^ 2))
        - (deriv h ρ / (4 * Real.pi * ρ ^ 2) - 2 * h ρ / (4 * Real.pi * ρ ^ 3))) ρ :=
    hG1.sub hG2
  -- `deriv (fun r => h r / (4π r))` agrees near `ρ` with the explicit formula
  have hEv : (fun r : ℝ => deriv h r / (4 * Real.pi * r) - h r / (4 * Real.pi * r ^ 2))
      =ᶠ[nhds ρ] deriv (fun r : ℝ => h r / (4 * Real.pi * r)) := by
    filter_upwards [(isOpen_ne (x := (0 : ℝ))).mem_nhds hρne] with r hr
    exact (hasDerivAt_div_mul_id hc hr (hd.differentiableAt.hasDerivAt)).deriv.symm
  have h2 : deriv (deriv (fun r : ℝ => h r / (4 * Real.pi * r))) ρ
      = (deriv (deriv h) ρ / (4 * Real.pi * ρ) - deriv h ρ / (4 * Real.pi * ρ ^ 2))
        - (deriv h ρ / (4 * Real.pi * ρ ^ 2) - 2 * h ρ / (4 * Real.pi * ρ ^ 3)) := by
    rw [← hEv.deriv_eq, hG.deriv]
  have h1 : deriv (fun r : ℝ => h r / (4 * Real.pi * r)) ρ
      = deriv h ρ / (4 * Real.pi * ρ) - h ρ / (4 * Real.pi * ρ ^ 2) := hF1.deriv
  rw [h2, h1]
  field_simp
  ring

end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.box_divergence_identity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

set_option linter.unusedVariables false in
theorem box_divergence_identity {F : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {F' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)}
    (a b : Fin 3 → ℝ) (hle : a ≤ b) (hlt : ∀ i, a i < b i)
    (hgood : ∀ x ∈ Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)), x 0 ≠ 0 ∧ x 2 ≠ 0)
    (hcont : ContinuousOn F (Set.Icc a b))
    (hdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt F (F' x) x)
    (hint : MeasureTheory.IntegrableOn (fun x => ∑ i, F' x (Pi.single i 1) i) (Set.Icc a b)) :
    (∫ x in Set.Icc a b, ∑ i, F' x (Pi.single i 1) i) =
      ∑ i : Fin 3,
        ((∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (b i) x) i) -
          ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) x) i) := by
  -- This is Mathlib's Bochner divergence theorem on the box `[a, b]`, with `n = 2` and the
  -- empty exception set: `hgood` says that the *interior* of the box meets neither of the two
  -- planes `x 0 = 0`, `x 2 = 0` off which `hdiff` is available, so `F` is differentiable on the
  -- whole interior of `[a, b]`.
  exact MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable (n := 2) a b hle F F'
    (∅ : Set (Fin 3 → ℝ)) Set.countable_empty hcont
    (fun x hx => hdiff x (hgood x hx.1).1 (hgood x hx.1).2) hint

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.offPlanes.Ibp1D =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integration by parts on `ℝ` with one exceptional point

`Work.FTS.PressureOn.offPlanes.ibp_except_zero`: if `Ψ` is differentiable everywhere with derivative
`Ψp`, `G` is differentiable everywhere except at `0` with derivative `Gp` there, both are continuous,
the products `Ψ * Gp` and `G * Ψp` are integrable and `G * Ψ` vanishes at `±∞`, then

  `∫ t, Ψ t * Gp t = - ∫ t, Ψp t * G t`.

The proof splits `ℝ = (-∞,0] ∪ (0,∞)` and applies the half-line integration by parts
`MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul` and
`MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`; the two boundary terms at `0` cancel by
continuity.
-/

open MeasureTheory Filter Topology

namespace Work.FTS.PressureOn.offPlanes

theorem ibp_except_zero {G Gp Ψ Ψp : ℝ → ℝ}
    (hΨd : ∀ t, HasDerivAt Ψ (Ψp t) t)
    (hGd : ∀ t, t ≠ 0 → HasDerivAt G (Gp t) t)
    (hGc : Continuous G) (hΨc : Continuous Ψ)
    (hΨGp : Integrable (fun t => Ψ t * Gp t))
    (hΨpG : Integrable (fun t => Ψp t * G t))
    (hbot : Tendsto (fun t => Ψ t * G t) atBot (𝓝 0))
    (htop : Tendsto (fun t => Ψ t * G t) atTop (𝓝 0)) :
    ∫ t, Ψ t * Gp t = -∫ t, Ψp t * G t := by
  have hzeroR : Tendsto (fun t => Ψ t * G t) (𝓝[>] (0 : ℝ)) (𝓝 (Ψ 0 * G 0)) :=
    (hΨc.mul hGc).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzeroL : Tendsto (fun t => Ψ t * G t) (𝓝[<] (0 : ℝ)) (𝓝 (Ψ 0 * G 0)) :=
    (hΨc.mul hGc).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hR : ∫ t in Set.Ioi (0 : ℝ), Ψ t * Gp t = 0 - (Ψ 0 * G 0) - ∫ t in Set.Ioi (0:ℝ), Ψp t * G t := by
    apply integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := Ψ 0 * G 0) (b' := 0)
    · exact fun x _ => hΨd x
    · exact fun x hx => hGd x (ne_of_gt hx)
    · exact hΨGp.integrableOn
    · exact hΨpG.integrableOn
    · exact hzeroR
    · exact htop
  have hL : ∫ t in Set.Iic (0 : ℝ), Ψ t * Gp t = (Ψ 0 * G 0) - 0 - ∫ t in Set.Iic (0:ℝ), Ψp t * G t := by
    apply integral_Iic_mul_deriv_eq_deriv_mul (a := 0) (a' := Ψ 0 * G 0) (b' := 0)
    · exact fun x _ => hΨd x
    · exact fun x hx => hGd x (ne_of_lt hx)
    · exact hΨGp.integrableOn
    · exact hΨpG.integrableOn
    · exact hzeroL
    · exact hbot
  have hsplit : ∫ t, Ψ t * Gp t = (∫ t in Set.Iic 0, Ψ t * Gp t) + ∫ t in Set.Ioi 0, Ψ t * Gp t := by
    rw [← integral_add_compl measurableSet_Iic hΨGp, Set.compl_Iic]
  have hsplit2 : ∫ t, Ψp t * G t = (∫ t in Set.Iic 0, Ψp t * G t) + ∫ t in Set.Ioi 0, Ψp t * G t := by
    rw [← integral_add_compl measurableSet_Iic hΨpG, Set.compl_Iic]
  rw [hsplit, hL, hR, hsplit2]
  ring

end Work.FTS.PressureOn.offPlanes
end
-- ===== merged: Submission.Work.FTS.PressureOn.secondDerivTest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

open scoped Topology

theorem secondDerivTest {f : ℝ → ℝ} {x₀ : ℝ} (hmax : IsLocalMax f x₀)
    (h2 : ContDiffAt ℝ 2 f x₀) : deriv (deriv f) x₀ ≤ 0 := by
  by_contra h
  have hpos : 0 < deriv (deriv f) x₀ := not_le.mp h
  -- Fermat's theorem: the first derivative vanishes at a local maximum.
  have hd : deriv f x₀ = 0 := hmax.deriv_eq_zero
  -- `h2` is only used here, to supply continuity at `x₀`.
  have hc : ContinuousAt f x₀ := h2.continuousAt
  -- The second-derivative test upgrades the positive second derivative to a local minimum.
  have hmin : IsLocalMin f x₀ := isLocalMin_of_deriv_deriv_pos hpos hd hc
  -- Being both a local min and a local max, `f` is eventually constant near `x₀`.
  have hconst : f =ᶠ[𝓝 x₀] fun _ => f x₀ := by
    filter_upwards [hmax, hmin] with x hx1 hx2 using le_antisymm hx1 hx2
  -- Hence `deriv f` is eventually `0` near `x₀`, and so is its derivative.
  have hzero : deriv (deriv f) x₀ = 0 := by
    have h1 : deriv (deriv f) =ᶠ[𝓝 x₀] deriv (deriv (fun _ : ℝ => f x₀)) := hconst.deriv.deriv
    have := h1.eq_of_nhds
    simpa using this
  linarith

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.RegExportIface.RXT.LeafAux.landau_1d =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! # `Work.FTS.RegExportIface.RXT.landau_1d` — leaf port (module `LeafAux.landau_1d`)

The leaf statement of `Submission/Work/FTS/RegExportIface/RXT/Leaves.lean`, **proved**.
Proof ported verbatim from the `Work.FTS_RegExport` mirror area; this module deliberately
does **not** import `Leaves` (which imports it), so the cycle is broken.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.RegExportIface.RXT

set_option autoImplicit false


/-- `|p - q| ≤ |p| + |q|`, the form of the triangle inequality used below. -/
private theorem landau_abs_sub_le (p q : ℝ) : |p - q| ≤ |p| + |q| := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [le_abs_self p, neg_le_abs p, le_abs_self q, neg_le_abs q]

/-- **Second-order Taylor bound, upper sign.**  If `f` is differentiable with derivative `f'`
on `[a, b]`, `f'` is differentiable with derivative `f''` there, `a ≤ b` and `f'' ≤ A` on
`[a, b]`, then the Taylor remainder at the left endpoint is bounded above:
`f b - f a - f' a * (b - a) ≤ A * (b - a)^2 / 2`.

Only pointwise `HasDerivAt` hypotheses are used; no continuity of `f''` is needed. -/
theorem landau_taylor2_upper {f f' f'' : ℝ → ℝ} {a b A : ℝ} (hab : a ≤ b)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc a b, HasDerivAt f' (f'' y) y)
    (hA : ∀ y ∈ Set.Icc a b, f'' y ≤ A) :
    f b - f a - f' a * (b - a) ≤ A * (b - a) ^ 2 / 2 := by
  have haI : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hfc : ContinuousOn f (Set.Icc a b) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hf'c : ContinuousOn f' (Set.Icc a b) := fun t ht => (hf' t ht).continuousAt.continuousWithinAt
  -- the auxiliary function `G` is continuous on `[a,b]`
  have hGcont : ContinuousOn (fun s : ℝ => f b - f s - f' s * (b - s) - A / 2 * (b - s) ^ 2)
      (Set.Icc a b) := by
    have h1 : ContinuousOn (fun s : ℝ => f b - f s) (Set.Icc a b) :=
      (continuousOn_const (s := Set.Icc a b) (c := f b)).sub hfc
    have h2 : ContinuousOn (fun s : ℝ => f' s * (b - s)) (Set.Icc a b) :=
      hf'c.mul ((continuousOn_const (s := Set.Icc a b) (c := b)).sub continuousOn_id)
    have h3 : ContinuousOn (fun s : ℝ => A / 2 * (b - s) ^ 2) (Set.Icc a b) :=
      (continuousOn_const (s := Set.Icc a b) (c := A / 2)).mul
        (((continuousOn_const (s := Set.Icc a b) (c := b)).sub continuousOn_id).pow 2)
    exact (h1.sub h2).sub h3
  -- its derivative on the interior is `(b - t) * (A - f'' t)`
  have hderiv : ∀ t ∈ interior (Set.Icc a b),
      HasDerivWithinAt (fun s : ℝ => f b - f s - f' s * (b - s) - A / 2 * (b - s) ^ 2)
        ((b - t) * (A - f'' t)) (interior (Set.Icc a b)) t := by
    intro t ht
    rw [interior_Icc] at ht
    have htI : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hb : HasDerivAt (fun s : ℝ => b - s) (0 - 1) t :=
      (hasDerivAt_const t b).sub (hasDerivAt_id t)
    have h1 : HasDerivAt (fun s : ℝ => f b - f s) (0 - f' t) t :=
      (hasDerivAt_const t (f b)).sub (hf t htI)
    have h2 : HasDerivAt (fun s : ℝ => f' s * (b - s)) (f'' t * (b - t) + f' t * (0 - 1)) t :=
      (hf' t htI).mul hb
    have h3 : HasDerivAt (fun s : ℝ => A / 2 * (b - s) ^ 2)
        (A / 2 * (2 * (b - t) ^ (2 - 1) * (0 - 1))) t :=
      (hb.pow 2).const_mul (A / 2)
    have h4 : HasDerivAt (fun s : ℝ => f b - f s - f' s * (b - s) - A / 2 * (b - s) ^ 2)
        ((0 - f' t) - (f'' t * (b - t) + f' t * (0 - 1))
          - A / 2 * (2 * (b - t) ^ (2 - 1) * (0 - 1))) t :=
      (h1.sub h2).sub h3
    convert h4.hasDerivWithinAt using 1
    norm_num
    ring
  -- and that derivative is nonnegative on `(a,b)`
  have hnonneg : ∀ t ∈ interior (Set.Icc a b), 0 ≤ (b - t) * (A - f'' t) := by
    intro t ht
    rw [interior_Icc] at ht
    have htI : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h1 : 0 ≤ b - t := by linarith [ht.2]
    have h2 : 0 ≤ A - f'' t := by linarith [hA t htI]
    exact mul_nonneg h1 h2
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hGcont hderiv hnonneg
  have h := hmono haI hbI hab
  have hG0 : (fun s : ℝ => f b - f s - f' s * (b - s) - A / 2 * (b - s) ^ 2) b = 0 := by
    simp only [sub_self, mul_zero, zero_pow (show (2:ℕ) ≠ 0 by norm_num)]
  rw [hG0] at h
  linarith [h]

/-- **Second-order Taylor bound, lower sign.**  Same as `landau_taylor2_upper` with `f'' ≥ -A`:
the Taylor remainder at the left endpoint is bounded below by `-A * (b - a)^2 / 2`. -/
theorem landau_taylor2_lower {f f' f'' : ℝ → ℝ} {a b A : ℝ} (hab : a ≤ b)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc a b, HasDerivAt f' (f'' y) y)
    (hA : ∀ y ∈ Set.Icc a b, -A ≤ f'' y) :
    -(A * (b - a) ^ 2 / 2) ≤ f b - f a - f' a * (b - a) := by
  have h := landau_taylor2_upper (f := fun y => -f y) (f' := fun y => -f' y)
    (f'' := fun y => -f'' y) (a := a) (b := b) (A := A) hab
    (fun y hy => (hf y hy).neg) (fun y hy => (hf' y hy).neg)
    (fun y hy => by have := hA y hy; linarith)
  linarith [h]

/-- **Second-order Taylor bound with the Lagrange remainder** for a function whose first two
derivatives are only known to exist pointwise on `[a, b]`: if `|f''| ≤ A` there, then
`|f b - f a - f' a * (b - a)| ≤ A * (b - a)^2 / 2`. -/
theorem landau_taylor2_remainder {f f' f'' : ℝ → ℝ} {a b A : ℝ} (hab : a ≤ b)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc a b, HasDerivAt f' (f'' y) y)
    (hA : ∀ y ∈ Set.Icc a b, |f'' y| ≤ A) :
    |f b - f a - f' a * (b - a)| ≤ A * (b - a) ^ 2 / 2 := by
  have h1 := landau_taylor2_upper (f := f) (f' := f') (f'' := f'') (A := A) hab hf hf'
    (fun y hy => (abs_le.mp (hA y hy)).2)
  have h2 := landau_taylor2_lower (f := f) (f' := f') (f'' := f'') (A := A) hab hf hf'
    (fun y hy => (abs_le.mp (hA y hy)).1)
  rw [abs_le]
  exact ⟨h2, h1⟩

theorem landau_1d {h : ℝ → ℝ} {x δ M₀ M₂ : ℝ} (hδ : 0 < δ)
    (hd : ∀ y ∈ Set.Icc x (x + δ), HasDerivAt h (deriv h y) y)
    (hd2 : ∀ y ∈ Set.Icc x (x + δ), HasDerivAt (deriv h) (deriv (deriv h) y) y)
    (h0 : ∀ y ∈ Set.Icc x (x + δ), |h y| ≤ M₀)
    (h2 : ∀ y ∈ Set.Icc x (x + δ), |deriv (deriv h) y| ≤ M₂) :
    |deriv h x| ≤ 2 * M₀ / δ + M₂ * δ / 2 := by
  have hxδ : x ≤ x + δ := by linarith
  -- the Lagrange remainder of the second-order Taylor expansion at `x`, evaluated at `x + δ`
  have hrem := landau_taylor2_remainder (f := h) (f' := deriv h) (f'' := deriv (deriv h))
    (a := x) (b := x + δ) (A := M₂) hxδ hd hd2 h2
  have hsub : x + δ - x = δ := by ring
  rw [hsub] at hrem
  have hmemx : x ∈ Set.Icc x (x + δ) := ⟨le_rfl, hxδ⟩
  have hmemδ : x + δ ∈ Set.Icc x (x + δ) := ⟨hxδ, le_rfl⟩
  -- `|h (x+δ) - h x| ≤ 2 M₀`
  have hb : |h (x + δ) - h x| ≤ 2 * M₀ := by
    have h1 : |h (x + δ) - h x| ≤ |h (x + δ)| + |h x| := landau_abs_sub_le _ _
    have h2' : |h (x + δ)| + |h x| ≤ M₀ + M₀ := add_le_add (h0 (x + δ) hmemδ) (h0 x hmemx)
    linarith [h1, h2']
  have key : |deriv h x| * δ ≤ 2 * M₀ + M₂ * δ ^ 2 / 2 := by
    have h1 : |deriv h x| * δ = |deriv h x * δ| := by rw [abs_mul, abs_of_pos hδ]
    rw [h1]
    -- `deriv h x * δ = (h (x+δ) - h x) - R`
    have htri : |deriv h x * δ| ≤ |h (x + δ) - h x| + |h (x + δ) - h x - deriv h x * δ| := by
      have he : deriv h x * δ = (h (x + δ) - h x) - (h (x + δ) - h x - deriv h x * δ) := by ring
      calc |deriv h x * δ|
          = |(h (x + δ) - h x) - (h (x + δ) - h x - deriv h x * δ)| := congrArg abs he
        _ ≤ |h (x + δ) - h x| + |h (x + δ) - h x - deriv h x * δ| := landau_abs_sub_le _ _
    linarith [htri, hb, hrem]
  have hdone : |deriv h x| ≤ (2 * M₀ + M₂ * δ ^ 2 / 2) / δ := (le_div_iff₀ hδ).mpr key
  have harith : (2 * M₀ + M₂ * δ ^ 2 / 2) / δ = 2 * M₀ / δ + M₂ * δ / 2 := by
    field_simp
  rw [harith] at hdone
  exact hdone


end Work.FTS.RegExportIface.RXT
end
end
-- ===== merged: Submission.Work.FTS.RegExportIface.RXT.LeafAux.spatial_expand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! # `Work.FTS.RegExportIface.RXT.spatial_expand` — leaf port (module `LeafAux.spatial_expand`)

The leaf statement of `Submission/Work/FTS/RegExportIface/RXT/Leaves.lean`, **proved**.
Proof ported verbatim from the `Work.FTS_RegExport` mirror area; this module deliberately
does **not** import `Leaves` (which imports it), so the cycle is broken.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.RegExportIface.RXT

set_option autoImplicit false



/-! ## Elementary helpers -/







end Work.FTS.RegExportIface.RXT
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.Lib.holder_of_lipschitz_of_bounded =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der.Lib

theorem holder_of_lipschitz_of_bounded {f : ℝ → ℝ} {C M α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hlip : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |f z - f z'| ≤ C * |z - z'|)
    (hbdd : ∀ z : ℝ, 0 ≤ z → |f z| ≤ M) :
    ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |f z - f z'| ≤ max C (2 * M) * |z - z'| ^ α := by
  intro z z' hz hz'
  have hd0 : 0 ≤ |z - z'| := abs_nonneg _
  have hmax0 : 0 ≤ max C (2 * M) := le_trans hC (le_max_left _ _)
  have habs : |f z - f z'| ≤ |f z| + |f z'| := by
    simpa using abs_sub_le (f z) 0 (f z')
  -- the trivial bound: either Lipschitz or bounded
  have hmin : |f z - f z'| ≤ min (C * |z - z'|) (2 * M) := by
    refine le_min (hlip z z' hz hz') ?_
    calc |f z - f z'| ≤ |f z| + |f z'| := habs
      _ ≤ M + M := add_le_add (hbdd z hz) (hbdd z' hz')
      _ = 2 * M := by ring
  rcases le_or_gt |z - z'| 1 with hd1 | hd1
  · -- small distances: |z - z'| ≤ |z - z'| ^ α, so the Lipschitz bound wins
    have hle : |z - z'| ≤ |z - z'| ^ α := by
      rcases eq_or_lt_of_le hd0 with h0 | h0
      · simp [h0.symm, Real.zero_rpow (ne_of_gt hα)]
      · have h1 : |z - z'| ^ (1:ℝ) ≤ |z - z'| ^ α :=
          Real.rpow_le_rpow_of_exponent_ge h0 hd1 hα1
        rwa [Real.rpow_one] at h1
    calc |f z - f z'| ≤ C * |z - z'| := le_trans hmin (min_le_left _ _)
      _ ≤ max C (2 * M) * |z - z'| := mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
      _ ≤ max C (2 * M) * |z - z'| ^ α := mul_le_mul_of_nonneg_left hle hmax0
  · -- large distances: |z - z'| ^ α ≥ 1, so the boundedness bound wins
    have hle : (1:ℝ) ≤ |z - z'| ^ α := Real.one_le_rpow (le_of_lt hd1) (le_of_lt hα)
    calc |f z - f z'| ≤ 2 * M := le_trans hmin (min_le_right _ _)
      _ ≤ max C (2 * M) := le_max_right _ _
      _ ≤ max C (2 * M) * |z - z'| ^ α := le_mul_of_one_le_right hmax0 hle

end Work.FTS.RegPkgGal.Der.Lib
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.Lib.lip_of_bounded_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology

namespace Work.FTS.RegPkgGal.Der.Lib

/-- **Mean-value bound on the half line.**  If `f` is differentiable on `(0, ∞)` with
`|deriv f| ≤ M` there and is continuous at `0`, then `f` is `M`-Lipschitz on `[0, ∞)`.

The proof is the mean value theorem on `[a, b]` for `0 < a`, together with an
`ε → 0⁺` limit argument on `[ε, b]` in the case `a = 0`, where differentiability at the
endpoint `0` is replaced by continuity there. -/
theorem lip_of_bounded_deriv {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hdiff : ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ f x)
    (hbd : ∀ x ∈ Set.Ioi (0 : ℝ), |deriv f x| ≤ M)
    (hcont : ContinuousAt f 0) :
    ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |f z - f z'| ≤ M * |z - z'| := by
  have hderivAt : ∀ x : ℝ, 0 < x → HasDerivAt f (deriv f x) x :=
    fun x hx => (hdiff x hx).hasDerivAt
  have hbound : ∀ x : ℝ, 0 < x → ‖deriv f x‖ ≤ M :=
    fun x hx => by rw [Real.norm_eq_abs]; exact hbd x hx
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → |f a - f b| ≤ M * |a - b| := by
    intro a b ha hab
    rcases eq_or_lt_of_le hab with hab' | hlt
    · subst hab'; simp
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · -- `a = 0`: apply the mean value theorem on `[ε, b]` and let `ε → 0⁺`.
      subst ha0
      have hb : 0 < b := hlt
      have h1 : Filter.Tendsto (fun ε : ℝ => |f ε - f b|) (𝓝[Set.Ioi 0] 0)
          (𝓝 (|f 0 - f b|)) :=
        (((ContinuousAt.tendsto hcont).mono_left nhdsWithin_le_nhds).sub
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => f b) (𝓝[Set.Ioi 0] 0) (𝓝 (f b)))).abs
      have h2 : Filter.Tendsto (fun ε : ℝ => M * (b - ε)) (𝓝[Set.Ioi 0] 0) (𝓝 (M * b)) := by
        have hb' : Filter.Tendsto (fun ε : ℝ => b - ε) (𝓝[Set.Ioi 0] 0) (𝓝 (b - 0)) := by
          simpa using Filter.Tendsto.sub
            (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => b) (𝓝[Set.Ioi 0] 0) (𝓝 b))
            (Filter.tendsto_id.mono_left nhdsWithin_le_nhds :
              Filter.Tendsto (fun ε : ℝ => ε) (𝓝[Set.Ioi 0] 0) (𝓝 (0 : ℝ)))
        simpa using Filter.Tendsto.const_mul M hb'
      have h3 : ∀ᶠ ε in 𝓝[Set.Ioi 0] 0, |f ε - f b| ≤ M * (b - ε) := by
        filter_upwards [self_mem_nhdsWithin,
          (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
        have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := ε) (b := b)
          (f' := fun x => deriv f x) (C := M)
          (fun x hx => (hderivAt x (lt_of_lt_of_le hε hx.1)).hasDerivWithinAt)
          (fun x hx => hbound x (lt_of_lt_of_le hε hx.1))
          b (right_mem_Icc.mpr hεb.le)
        simpa [Real.norm_eq_abs, abs_sub_comm] using hmvt
      have h4 := le_of_tendsto_of_tendsto h1 h2 h3
      simpa [abs_of_pos hb] using h4
    · -- `0 < a`: the mean value theorem on `[a, b]`.
      have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := a) (b := b)
        (f' := fun x => deriv f x) (C := M)
        (fun x hx => (hderivAt x (lt_of_lt_of_le hapos hx.1)).hasDerivWithinAt)
        (fun x hx => hbound x (lt_of_lt_of_le hapos hx.1))
        b (right_mem_Icc.mpr hab)
      rw [Real.norm_eq_abs] at hmvt
      have hgoal : M * |a - b| = M * (b - a) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring
      rw [hgoal, abs_sub_comm (f a) (f b)]
      exact hmvt
  intro z z' hz hz'
  rcases le_total z z' with h | h
  · exact key z z' hz h
  · have hh := key z' z hz' h
    rw [abs_sub_comm (f z) (f z'), abs_sub_comm z z']
    exact hh

end Work.FTS.RegPkgGal.Der.Lib
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R1b.General =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R1b

open Set Filter Topology MeasureTheory
open scoped Topology Real

set_option autoImplicit false

/-! ## A general gluing lemma -/

/-- **Gluing of derivatives along two pieces covering a neighbourhood.**  If `f` agrees with `f₁`
on `s` and with `f₂` on `t`, if `s ∪ t` is a neighbourhood of `x`, and if `f₁`, `f₂` both have
derivative `L` at `x`, then so does `f`. -/
theorem hasFDerivAt_of_union {f f₁ f₂ : ℝ × ℝ → ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ} {x : ℝ × ℝ}
    {s t : Set (ℝ × ℝ)} (hst : s ∪ t ∈ 𝓝 x) (hxs : x ∈ s) (hxt : x ∈ t)
    (h1 : ∀ y ∈ s, f y = f₁ y) (h2 : ∀ y ∈ t, f y = f₂ y)
    (hf₁ : HasFDerivAt f₁ L x) (hf₂ : HasFDerivAt f₂ L x) : HasFDerivAt f L x :=
  ((hf₁.hasFDerivWithinAt.congr h1 (h1 x hxs)).union
    (hf₂.hasFDerivWithinAt.congr h2 (h2 x hxt))).hasFDerivAt hst

/-! ## General auxiliary facts -/

/-- The Fréchet derivative of `f : ℝ × ℝ → ℝ` is the sum of its two partial derivatives
(evaluated on the two basis vectors). -/
theorem fderiv_eq_partials {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x
      = (deriv (fun z => f (z, x.2)) x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (deriv (fun s => f (x.1, s)) x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  refine ContinuousLinearMap.ext fun v => ?_
  obtain ⟨u, w⟩ := v
  have h1 : (fderiv ℝ f x) (1, 0) = deriv (fun z => f (z, x.2)) x.1 := by
    have hc : HasDerivAt (fun z : ℝ => (z, x.2)) ((1, 0) : ℝ × ℝ) x.1 := by
      simpa using (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
    have hh := (hf.hasFDerivAt.comp_hasDerivAt (x.1) hc).deriv
    simpa [Function.comp_def] using hh.symm
  have h2 : (fderiv ℝ f x) (0, 1) = deriv (fun s => f (x.1, s)) x.2 := by
    have hc : HasDerivAt (fun s : ℝ => (x.1, s)) ((0, 1) : ℝ × ℝ) x.2 := by
      simpa using (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
    have hh := (hf.hasFDerivAt.comp_hasDerivAt (x.2) hc).deriv
    simpa [Function.comp_def] using hh.symm
  have hsplit : (u, w) = u • (1, 0) + w • (0, 1) := by ext <;> simp
  have hL : (fderiv ℝ f x) (u, w)
      = deriv (fun z => f (z, x.2)) x.1 * u + deriv (fun s => f (x.1, s)) x.2 * w := by
    rw [hsplit, map_add, map_smul, map_smul, h1, h2]
    simp only [smul_eq_mul]
    ring
  have hR : ((deriv (fun z => f (z, x.2)) x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (deriv (fun s => f (x.1, s)) x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, w)
      = deriv (fun z => f (z, x.2)) x.1 * u + deriv (fun s => f (x.1, s)) x.2 * w := by
    simp [smul_eq_mul]
  rw [hL, hR]

/-- The partial derivative of a `C¹` function in the first variable is continuous. -/
theorem continuousOn_deriv_z_slice {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) :
    ContinuousOn (fun q : ℝ × ℝ => deriv (fun z => f (z, q.2)) q.1) s := by
  have hf' : ContinuousOn (fderiv ℝ f) s := hf.continuousOn_fderiv_of_isOpen hs (by norm_num)
  have hc : ContinuousOn (fun q : ℝ × ℝ => (fderiv ℝ f q) (1, 0)) s :=
    hf'.clm_apply continuousOn_const
  refine hc.congr fun q hq => ?_
  have hd : DifferentiableAt ℝ f q :=
    (hf.differentiableOn one_ne_zero q hq).differentiableAt (hs.mem_nhds hq)
  have hcurve : HasDerivAt (fun z : ℝ => (z, q.2)) ((1, 0) : ℝ × ℝ) q.1 := by
    simpa using (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  have hh := (hd.hasFDerivAt.comp_hasDerivAt (q.1) hcurve).deriv
  simpa [Function.comp_def] using hh

/-- The partial derivative of a `C¹` function in the second variable is continuous. -/
theorem continuousOn_deriv_t_slice {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) :
    ContinuousOn (fun q : ℝ × ℝ => deriv (fun t => f (q.1, t)) q.2) s := by
  have hf' : ContinuousOn (fderiv ℝ f) s := hf.continuousOn_fderiv_of_isOpen hs (by norm_num)
  have hc : ContinuousOn (fun q : ℝ × ℝ => (fderiv ℝ f q) (0, 1)) s :=
    hf'.clm_apply continuousOn_const
  refine hc.congr fun q hq => ?_
  have hd : DifferentiableAt ℝ f q :=
    (hf.differentiableOn one_ne_zero q hq).differentiableAt (hs.mem_nhds hq)
  have hcurve : HasDerivAt (fun t : ℝ => (q.1, t)) ((0, 1) : ℝ × ℝ) q.2 := by
    simpa using (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have hh := (hd.hasFDerivAt.comp_hasDerivAt (q.2) hcurve).deriv
  simpa [Function.comp_def] using hh

/-- Extraction of a two-sided `ε`-`δ` statement (a box in `(z,τ)`) from a joint limit as
`(z,τ) → (0,τ₀)` within `z > 0`. -/
theorem tendsto_box {F : ℝ × ℝ → ℝ} {τ₀ c : ℝ}
    (h : Tendsto F (nhdsWithin (0, τ₀) (Ioi (0:ℝ) ×ˢ univ)) (nhds c)) :
    ∀ ε > 0, ∃ δ > 0, ∀ z τ : ℝ, 0 < z → z < δ → |τ - τ₀| < δ → |F (z, τ) - c| < ε := by
  intro ε hε
  have hmem : {p : ℝ × ℝ | |F p - c| < ε} ∈ nhdsWithin (0, τ₀) (Ioi (0:ℝ) ×ˢ univ) :=
    (Metric.tendsto_nhds.mp h) ε hε
  rcases mem_nhdsWithin.mp hmem with ⟨V, hVopen, hxV, hVsub⟩
  rcases Metric.mem_nhds_iff.mp (hVopen.mem_nhds hxV) with ⟨δ, hδ, hδV⟩
  refine ⟨δ, hδ, fun z τ hz hzδ hτδ => hVsub ⟨hδV ?_, ⟨hz, trivial⟩⟩⟩
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, abs_of_pos hz]
  exact max_lt hzδ hτδ


/-! ## More auxiliary lemmas for the corner analysis -/

/-- Near `(0,τ₀)`, any point with `0 < z` has `z < δ` and `|τ - τ₀| < δ`. -/
theorem eventually_box (τ₀ δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ y : ℝ × ℝ in 𝓝 (0, τ₀), 0 < y.1 → y.1 < δ ∧ |y.2 - τ₀| < δ := by
  have hbox : Ioo (-δ) δ ×ˢ Ioo (τ₀ - δ) (τ₀ + δ) ∈ 𝓝 ((0, τ₀) : ℝ × ℝ) := by
    apply (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
    show (0:ℝ) ∈ Ioo (-δ) δ ∧ τ₀ ∈ Ioo (τ₀ - δ) (τ₀ + δ)
    exact ⟨⟨by linarith, hδ⟩, ⟨by linarith, by linarith⟩⟩
  filter_upwards [hbox] with y hy _
  exact ⟨hy.1.2, abs_lt.mpr ⟨by linarith [hy.2.1], by linarith [hy.2.2]⟩⟩

/-- From `|z⁻¹ * v| < c` with `0 < z` deduce `|v| < c * z`. -/
theorem abs_lt_mul_of_abs_inv_mul_lt {z v c : ℝ} (hz : 0 < z) (h : |z⁻¹ * v| < c) :
    |v| < c * z := by
  have h' : z⁻¹ * |v| < c := by rwa [abs_mul, abs_inv, abs_of_pos hz] at h
  have h'' := mul_lt_mul_of_pos_left h' hz
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hz), one_mul, mul_comm z c] at h''

/-- From a joint limit as `(z,τ) → (0,τ₀)` within `z > 0` (to `0`) we get an eventual bound. -/
theorem eventually_of_tendsto_box {F : ℝ × ℝ → ℝ} {τ₀ c : ℝ} (hc : 0 < c)
    (h : Tendsto F (nhdsWithin (0, τ₀) (Ioi 0 ×ˢ univ)) (nhds 0)) :
    ∀ᶠ y : ℝ × ℝ in 𝓝 (0, τ₀), 0 < y.1 → |F y| < c := by
  rcases tendsto_box h c hc with ⟨δ, hδ, H⟩
  filter_upwards [eventually_box τ₀ δ hδ] with y hy hy1
  exact by simpa using H y.1 y.2 hy1 (hy hy1).1 (hy hy1).2

/-- The slice at `τ = τ₀` of a joint limit as `(z,τ) → (0,τ₀)`. -/
theorem slice_bound_of_tendsto {F : ℝ × ℝ → ℝ} {τ₀ c : ℝ} (hc : 0 < c)
    (h : Tendsto F (nhdsWithin (0, τ₀) (Ioi 0 ×ˢ univ)) (nhds 0)) :
    ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ → |F (z, τ₀)| < c := by
  rcases tendsto_box h c hc with ⟨δ, hδ, H⟩
  exact ⟨δ, hδ, fun z hz hzδ => by simpa using H z τ₀ hz hzδ (by simpa using hδ)⟩

/-- Norm bound for the combination `a • fst + b • snd`. -/
theorem norm_smul_fst_add_smul_snd_le (a b : ℝ) :
    ‖a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ |a| + |b| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  obtain ⟨u, w⟩ := v
  have hv : (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, w)
      = a * u + b * w := by simp
  have hmax : max |u| |w| = ‖(u, w)‖ := by rw [Prod.norm_def]; simp
  rw [hv]
  calc ‖a * u + b * w‖ ≤ ‖a * u‖ + ‖b * w‖ := norm_add_le _ _
    _ = |a| * |u| + |b| * |w| := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    _ ≤ (|a| + |b|) * max |u| |w| := by
        have h1 : |u| ≤ max |u| |w| := le_max_left _ _
        have h2 : |w| ≤ max |u| |w| := le_max_right _ _
        nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg u, abs_nonneg w]
    _ = (|a| + |b|) * ‖(u, w)‖ := by rw [hmax]

end Work.FTS.RegPkgGal.R1b
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R2.angIntegral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R2

/-- The pointwise bound `(sinθ cos²θ)^α/sin 2θ ≤ 2^{-α}(sin 2θ)^{α-1}` (valid on all of
`[0, π/2]`; at the endpoints both sides are `0`). -/
private lemma fA {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) (Real.pi / 2)) :
    (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ)
      ≤ 2 ^ (-α) * (Real.sin (2 * θ)) ^ (α - 1) := by
  have hsin2nn : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc (by constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos])
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [hs, div_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (le_refl 0) _)
  · have hs2 : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hsin2nn (Ne.symm hs)
    have hsinθ : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc (by constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos])
    have hcosθ : 0 ≤ Real.cos θ := by
      by_contra h
      push Not at h
      have h2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
      nlinarith [hs2]
    have hcosle : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hc2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith
    have hAB : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * Real.cos θ :=
      mul_le_mul_of_nonneg_left hc2 hsinθ
    have h0A : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by positivity
    have hpow : (Real.sin θ * Real.cos θ ^ 2) ^ α ≤ (Real.sin θ * Real.cos θ) ^ α :=
      Real.rpow_le_rpow h0A hAB hα.le
    have key : (Real.sin θ * Real.cos θ) ^ α = 2 ^ (-α) * (Real.sin (2 * θ)) ^ α := by
      have hs2' : Real.sin (2 * θ) = 2 * (Real.sin θ * Real.cos θ) := by
        rw [Real.sin_two_mul]; ring
      rw [hs2', Real.mul_rpow (by norm_num) (mul_nonneg hsinθ hcosθ),
        Real.rpow_neg (x := 2) (by norm_num) α]
      rw [inv_mul_cancel_left₀ (Real.rpow_pos_of_pos (x := 2) (by norm_num) α).ne']
    rw [key] at hpow
    calc (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ)
        ≤ 2 ^ (-α) * (Real.sin (2 * θ)) ^ α / Real.sin (2 * θ) :=
          div_le_div_of_nonneg_right hpow hsin2nn
      _ = 2 ^ (-α) * (Real.sin (2 * θ)) ^ (α - 1) := by
          rw [mul_div_assoc, Real.rpow_sub hs2 α 1, Real.rpow_one]

/-- `(sin 2θ)^{α-1} ≤ (4/π)^{α-1}·(θ^{α-1} + (π/2-θ)^{α-1})` on the open interval. -/
private lemma fB {α : ℝ} (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (α - 1)
      ≤ (4 / Real.pi) ^ (α - 1) * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1)) := by
  have hθ0 : 0 < θ := hθ.1
  have hδ : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hC : 0 < (4 / Real.pi) ^ (α - 1) := by positivity
  have hexp : α - 1 ≤ 0 := by linarith
  rcases le_or_gt θ (Real.pi / 4) with hle | hgt
  · have hs : 4 / Real.pi * θ ≤ Real.sin (2 * θ) := by
      have h2 : 0 ≤ 2 * θ := by linarith
      have h3 : 2 * θ ≤ Real.pi / 2 := by linarith
      have h := Real.mul_le_sin h2 h3
      have he : (2 : ℝ) / Real.pi * (2 * θ) = 4 / Real.pi * θ := by ring
      linarith [h, he]
    have hp : 0 < 4 / Real.pi * θ := by positivity
    have h1 : (Real.sin (2 * θ)) ^ (α - 1) ≤ (4 / Real.pi * θ) ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos hp hs hexp
    rw [Real.mul_rpow (by positivity) hθ0.le] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg hδ.le _)) hC.le)
  · have hsin : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
      have h2 : 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ := by ring
      rw [h2, Real.sin_pi_sub]
    have hs : 4 / Real.pi * (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
      rw [hsin]
      have hx0 : 0 ≤ 2 * (Real.pi / 2 - θ) := by linarith
      have hx1 : 2 * (Real.pi / 2 - θ) ≤ Real.pi / 2 := by linarith
      have h := Real.mul_le_sin hx0 hx1
      have he : (2 : ℝ) / Real.pi * (2 * (Real.pi / 2 - θ)) = 4 / Real.pi * (Real.pi / 2 - θ) := by
        ring
      linarith [h, he]
    have hp : 0 < 4 / Real.pi * (Real.pi / 2 - θ) := by positivity
    have h1 : (Real.sin (2 * θ)) ^ (α - 1) ≤ (4 / Real.pi * (Real.pi / 2 - θ)) ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos hp hs hexp
    rw [Real.mul_rpow (by positivity) hδ.le] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg hθ0.le _)) hC.le)

/-- The combined pointwise domination on `[0, π/2]`. -/
private lemma fpoint {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Icc (0:ℝ) (Real.pi / 2)) :
    (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ)
      ≤ 2 ^ (-α) * (4 / Real.pi) ^ (α - 1) * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1)) := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    have hL : (Real.sin 0 * Real.cos 0 ^ 2) ^ α / Real.sin (2 * 0) = 0 := by
      rw [show (2:ℝ) * 0 = 0 from by norm_num, Real.sin_zero, Real.cos_zero, one_pow,
        zero_mul, Real.zero_rpow (x := α) hα.ne', div_zero]
    rw [hL, sub_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (add_nonneg (by positivity) (by positivity))
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2
    · subst h2
      have hL : (Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) ^ 2) ^ α
          / Real.sin (2 * (Real.pi / 2)) = 0 := by
        rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi, Real.cos_pi_div_two,
          zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, Real.zero_rpow (x := α) hα.ne', div_zero]
      rw [hL, sub_self]
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (add_nonneg (by positivity) (Real.rpow_nonneg le_rfl _))
    · have hA := fA hα hθ
      have hB := fB hα1 (show θ ∈ Ioo (0:ℝ) (Real.pi / 2) from ⟨h0, h2⟩)
      calc (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ)
          ≤ 2 ^ (-α) * (Real.sin (2 * θ)) ^ (α - 1) := hA
        _ ≤ 2 ^ (-α) * ((4 / Real.pi) ^ (α - 1) * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1))) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
        _ = 2 ^ (-α) * (4 / Real.pi) ^ (α - 1) * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1)) := by
            ring

theorem angIntegral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      IntervalIntegrable
          (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
          MeasureTheory.volume a b ∧
        (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
          ≤ M * (b - a) ^ α := by
  refine ⟨2 * (2 ^ (-α) * (4 / Real.pi) ^ (α - 1)) / α, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (by norm_num) (le_of_lt (mul_pos (by positivity) (by positivity))))
      hα.le
  · intro a b ha hab hb
    have hC : 0 < 2 ^ (-α) * (4 / Real.pi) ^ (α - 1) := mul_pos (by positivity) (by positivity)
    have hr : (-1 : ℝ) < α - 1 := by linarith
    have h1i : IntervalIntegrable (fun θ : ℝ => θ ^ (α - 1)) volume a b :=
      intervalIntegral.intervalIntegrable_rpow' hr
    have h2i' : IntervalIntegrable (fun x : ℝ => x ^ (α - 1)) volume (Real.pi / 2 - a)
        (Real.pi / 2 - b) :=
      intervalIntegral.intervalIntegrable_rpow' hr
    have h2i : IntervalIntegrable (fun θ : ℝ => (Real.pi / 2 - θ) ^ (α - 1)) volume a b := by
      have h := h2i'.comp_sub_left (Real.pi / 2)
      simpa using h
    have hdom : IntervalIntegrable
        (fun θ : ℝ => 2 ^ (-α) * (4 / Real.pi) ^ (α - 1)
          * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1))) volume a b :=
      (h1i.add h2i).const_mul _
    have hf_meas : AEStronglyMeasurable
        (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
        (volume.restrict (uIoc a b)) := by
      refine Measurable.aestronglyMeasurable ?_
      have h1 : Measurable (fun x : ℝ => Real.sin x * Real.cos x ^ 2) :=
        Real.measurable_sin.mul (Real.measurable_cos.pow_const 2)
      have h2 : Measurable (fun x : ℝ => (Real.sin x * Real.cos x ^ 2) ^ α) :=
        h1.pow measurable_const
      have h3 : Measurable (fun x : ℝ => Real.sin (2 * x)) :=
        Real.measurable_sin.comp (measurable_id.const_mul 2)
      exact h2.div h3
    have hae : (fun x : ℝ => ‖(Real.sin x * Real.cos x ^ 2) ^ α / Real.sin (2 * x)‖)
        ≤ᵐ[volume.restrict (uIoc a b)]
        (fun θ : ℝ => 2 ^ (-α) * (4 / Real.pi) ^ (α - 1)
          * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1))) := by
      rw [uIoc_of_le hab]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : 0 ≤ x := le_trans ha hx.1.le
      have hx1 : x ≤ Real.pi / 2 := le_trans hx.2 hb
      have hsinx : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_mem_Icc (by constructor <;> linarith [Real.pi_pos, hx0, hx1])
      have hsin2x : 0 ≤ Real.sin (2 * x) :=
        Real.sin_nonneg_of_mem_Icc (by constructor <;> linarith [Real.pi_pos, hx0, hx1])
      have hfnn : 0 ≤ (Real.sin x * Real.cos x ^ 2) ^ α / Real.sin (2 * x) :=
        div_nonneg (Real.rpow_nonneg (mul_nonneg hsinx (by positivity)) _) hsin2x
      rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
      exact fpoint hα hα1 ⟨hx0, hx1⟩
    have hf_int : IntervalIntegrable
        (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ)) volume a b :=
      IntervalIntegrable.mono_fun' hdom hf_meas hae
    refine ⟨hf_int, ?_⟩
    have hmono : (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
        ≤ ∫ θ in a..b, 2 ^ (-α) * (4 / Real.pi) ^ (α - 1)
            * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1)) := by
      refine intervalIntegral.integral_mono_on hab hf_int hdom (fun x hx => ?_)
      exact fpoint hα hα1 ⟨le_trans ha hx.1, le_trans hx.2 hb⟩
    have hval1 : ∫ θ in a..b, θ ^ (α - 1) = (b ^ α - a ^ α) / α := by
      rw [integral_rpow (Or.inl hr), show (α - 1) + 1 = α by ring]
    have hval2 : ∫ θ in a..b, (Real.pi / 2 - θ) ^ (α - 1)
        = ((Real.pi / 2 - a) ^ α - (Real.pi / 2 - b) ^ α) / α := by
      rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (α - 1)) (Real.pi / 2),
        integral_rpow (Or.inl hr), show (α - 1) + 1 = α by ring]
    have hhint : ∫ θ in a..b, 2 ^ (-α) * (4 / Real.pi) ^ (α - 1)
          * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1))
        = 2 ^ (-α) * (4 / Real.pi) ^ (α - 1) *
          (((b ^ α - a ^ α) / α) + (((Real.pi / 2 - a) ^ α - (Real.pi / 2 - b) ^ α) / α)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1i h2i, hval1, hval2]
    have hb1 : b ^ α - a ^ α ≤ (b - a) ^ α := by
      have h := Real.rpow_add_le_add_rpow (p := α) (a := a) (b := b - a) ha (by linarith) hα.le hα1
      rw [show a + (b - a) = b from by ring] at h
      linarith
    have hb2 : (Real.pi / 2 - a) ^ α - (Real.pi / 2 - b) ^ α ≤ (b - a) ^ α := by
      have h := Real.rpow_add_le_add_rpow (p := α) (a := Real.pi / 2 - b) (b := b - a)
        (by linarith : (0:ℝ) ≤ Real.pi / 2 - b) (by linarith : (0:ℝ) ≤ b - a) hα.le hα1
      rw [show Real.pi / 2 - b + (b - a) = Real.pi / 2 - a from by ring] at h
      linarith
    have hsum : (b ^ α - a ^ α) + ((Real.pi / 2 - a) ^ α - (Real.pi / 2 - b) ^ α)
        ≤ 2 * (b - a) ^ α := by
      linarith
    have hdiv : ((b ^ α - a ^ α) / α) + (((Real.pi / 2 - a) ^ α - (Real.pi / 2 - b) ^ α) / α)
        ≤ 2 * (b - a) ^ α / α := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hsum hα.le
    calc (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
        ≤ ∫ θ in a..b, 2 ^ (-α) * (4 / Real.pi) ^ (α - 1)
            * (θ ^ (α - 1) + (Real.pi / 2 - θ) ^ (α - 1)) := hmono
      _ = 2 ^ (-α) * (4 / Real.pi) ^ (α - 1) *
            (((b ^ α - a ^ α) / α) + (((Real.pi / 2 - a) ^ α - (Real.pi / 2 - b) ^ α) / α)) :=
            hhint
      _ ≤ 2 ^ (-α) * (4 / Real.pi) ^ (α - 1) * (2 * (b - a) ^ α / α) :=
            mul_le_mul_of_nonneg_left hdiv hC.le
      _ = 2 * (2 ^ (-α) * (4 / Real.pi) ^ (α - 1)) / α * (b - a) ^ α := by ring

end Work.FTS.RegPkgGal.R2
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7d.Vth_edge_cont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7d

theorem Vth_edge_cont {Vz Vθ : ℝ → ℝ → ℝ → ℝ} {S : ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => (Vz p.1 p.2.1 p.2.2, Vθ p.1 p.2.1 p.2.2))
      (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)))
    {z τ : ℝ} (hz : 0 < z) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) :
    Filter.Tendsto (fun θ' : ℝ => Vθ z θ' τ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Vθ z 0 τ)) ∧
    Filter.Tendsto (fun θ' : ℝ => Vθ z θ' τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds (Vθ z (Real.pi / 2) τ)) := by
  -- We prove continuity of `θ' ↦ Vθ z θ' τ` within the (open) interval `(0, π/2)` and then
  -- transfer the (`nhdsWithin`-)filter to the two edge restrictions `Ioi 0` and `Iio (π/2)`.
  set A : Set ℝ := Set.Ioo (0:ℝ) (Real.pi / 2) with hAdef
  have hπ : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hG : ContinuousOn (fun p : ℝ × ℝ × ℝ => Vθ p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := hcont.snd
  have key : ∀ x : ℝ, x ∈ Set.Icc (0:ℝ) (Real.pi / 2) →
      ContinuousWithinAt (fun θ' : ℝ => Vθ z θ' τ) A x := by
    intro x hx
    have hmem : (z, x, τ) ∈
        (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) :=
      ⟨hz, hx, hτ0, hτS⟩
    have hGx := hG.continuousWithinAt hmem
    -- the curve `θ' ↦ (z, θ', τ)` maps `A` into the half-strip and is continuous
    have hfx : ContinuousWithinAt (fun θ' : ℝ => (z, θ', τ)) A x :=
      (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousAt.continuousWithinAt
    have hmap : Set.MapsTo (fun θ' : ℝ => (z, θ', τ)) A
        (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
      intro θ' hθ'
      exact ⟨hz, ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩, hτ0, hτS⟩
    have hcomp : ContinuousWithinAt
        ((fun p : ℝ × ℝ × ℝ => Vθ p.1 p.2.1 p.2.2) ∘ (fun θ' : ℝ => (z, θ', τ))) A x :=
      ContinuousWithinAt.comp (x := x) (f := fun θ' : ℝ => (z, θ', τ)) hGx hfx hmap
    exact hcomp
  have h0 : ContinuousWithinAt (fun θ' : ℝ => Vθ z θ' τ) A 0 := key 0 ⟨le_refl 0, hπ.le⟩
  have hpi : ContinuousWithinAt (fun θ' : ℝ => Vθ z θ' τ) A (Real.pi / 2) :=
    key (Real.pi / 2) ⟨hπ.le, le_refl _⟩
  constructor
  · -- the two filters `𝓝[Ioi 0] 0` and `𝓝[Ioo 0 (π/2)] 0` agree
    have hfil : nhdsWithin (0:ℝ) (Set.Ioi 0) = nhdsWithin (0:ℝ) A := by
      rw [hAdef]
      exact nhdsWithin_eq_nhdsWithin' (s := Set.Iio (Real.pi / 2)) (t := Set.Ioi (0:ℝ))
        (u := Set.Ioo (0:ℝ) (Real.pi / 2))
        (isOpen_Iio.mem_nhds (by positivity : (0:ℝ) < Real.pi / 2))
        (by ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]; tauto)
    rw [hfil]
    exact h0
  · -- and likewise `𝓝[Iio (π/2)] (π/2)` and `𝓝[Ioo 0 (π/2)] (π/2)`
    have hfil : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) = nhdsWithin (Real.pi / 2) A := by
      rw [hAdef]
      exact nhdsWithin_eq_nhdsWithin' (s := Set.Ioi (0:ℝ)) (t := Set.Iio (Real.pi / 2))
        (u := Set.Ioo (0:ℝ) (Real.pi / 2))
        (isOpen_Ioi.mem_nhds (by positivity : (0:ℝ) < Real.pi / 2))
        (by ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]; tauto)
    rw [hfil]
    exact hpi

end Work.FTS.RegPkgGal.R7d
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7d.Vth_lip_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7d


end Work.FTS.RegPkgGal.R7d
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7d.exp_ode_const =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7d

open MeasureTheory intervalIntegral

/-- Uniqueness for the linear ODE `G' = cs * G`: the integrating factor
`F t = G t * exp (-∫_0^t cs)` is constant on `[0,T]` because its derivative vanishes
on the open interval, whence `G 0 = F 0 = F T = G T * exp (-∫_0^T cs) = 0`. -/
theorem exp_ode_const {G cs : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hG : ∀ t ∈ Set.Ioo 0 T, HasDerivAt G (cs t * G t) t)
    (hGc : ContinuousOn G (Set.Icc 0 T)) (hcs : ContinuousOn cs (Set.Icc 0 T))
    (hzero : G T = 0) : G 0 = 0 := by
  let F : ℝ → ℝ := fun t => G t * Real.exp (-(∫ s in (0:ℝ)..t, cs s))
  -- the integrating factor has vanishing derivative on the open interval
  have hderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt F 0 t := by
    intro t ht
    have hcs_at : ContinuousAt cs t := hcs.continuousAt (Icc_mem_nhds ht.1 ht.2)
    have hcsI : IntervalIntegrable cs volume 0 t :=
      ContinuousOn.intervalIntegrable_of_Icc ht.1.le (hcs.mono (Set.Icc_subset_Icc le_rfl ht.2.le))
    have hmeas : StronglyMeasurableAtFilter cs (nhds t) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hcs.mono (by intro x hx; exact ⟨hx.1.le, hx.2.le⟩)) t ht
    have hPderiv : HasDerivAt (fun u => ∫ s in (0:ℝ)..u, cs s) (cs t) t :=
      intervalIntegral.integral_hasDerivAt_right hcsI hmeas hcs_at
    have hexp : HasDerivAt (fun u => Real.exp (-(∫ s in (0:ℝ)..u, cs s)))
        (Real.exp (-(∫ s in (0:ℝ)..t, cs s)) * (-(cs t))) t := hPderiv.neg.exp
    have hprod : HasDerivAt (fun u => G u * Real.exp (-(∫ s in (0:ℝ)..u, cs s)))
        (cs t * G t * Real.exp (-(∫ s in (0:ℝ)..t, cs s))
          + G t * (Real.exp (-(∫ s in (0:ℝ)..t, cs s)) * -(cs t))) t := (hG t ht).mul hexp
    have hz : cs t * G t * Real.exp (-(∫ s in (0:ℝ)..t, cs s))
          + G t * (Real.exp (-(∫ s in (0:ℝ)..t, cs s)) * -(cs t)) = 0 := by ring
    simpa only [F] using hprod.congr_deriv hz
  -- continuity of the integrating factor on the closed interval
  have hcontP : ContinuousOn (fun u => ∫ s in (0:ℝ)..u, cs s) (Set.Icc 0 T) := by
    have h_int : IntegrableOn cs (Set.uIcc 0 T) volume := by
      rw [Set.uIcc_of_le hT.le]
      exact hcs.integrableOn_Icc
    have h2 := intervalIntegral.continuousOn_primitive_interval (f := cs) (a := (0:ℝ)) (b := T)
      (μ := volume) h_int
    rwa [Set.uIcc_of_le hT.le] at h2
  have hFc : ContinuousOn F (Set.Icc 0 T) := by
    change ContinuousOn (fun t => G t * Real.exp (-(∫ s in (0:ℝ)..t, cs s))) (Set.Icc 0 T)
    exact hGc.mul (Real.continuous_exp.comp_continuousOn hcontP.neg)
  -- fundamental theorem of calculus: `F T = F 0`
  have hFT : F T = F 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hFc hderiv
      intervalIntegrable_const
    rw [intervalIntegral.integral_zero] at h
    linarith [h]
  have hF0 : F 0 = G 0 := by simp [F]
  have hFT0 : F T = 0 := by simp [F, hzero]
  rw [← hF0, ← hFT, hFT0]

end Work.FTS.RegPkgGal.R7d
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7d.quadrant_extend =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.RegPkgGal.R7d


end Work.FTS.RegPkgGal.R7d
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7d.thBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7d

open Set

/-- The integrating factor `φ ↦ φ · exp (K · ·)` used to turn the differential inequality
`φ' ≥ -K φ` into monotonicity. -/
noncomputable def scalExp (K : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun x => φ x * Real.exp (K * x)

/-- **Grönwall, lower bound.**  If `φ` is continuous on `[0,T]`, differentiable on `(0,T)` with
`φ' x ≥ -K φ x` there, then `φ x ≥ φ 0 · exp (-(K x))` on `[0,T]`.

Proof: `x ↦ φ x · exp (K x)` is monotone, since its derivative
`(φ' x + K φ x) · exp (K x)` is nonnegative. -/
lemma gronwall_lower_fts {φ φ' : ℝ → ℝ} {K T : ℝ}
    (hφc : ContinuousOn φ (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ioo 0 T, HasDerivAt φ (φ' x) x)
    (hineq : ∀ x ∈ Set.Ioo 0 T, -(K * φ x) ≤ φ' x) :
    ∀ x ∈ Set.Icc 0 T, φ 0 * Real.exp (-(K * x)) ≤ φ x := by
  have hfd : ∀ x ∈ Set.Ioo 0 T,
      HasDerivAt (scalExp K φ) ((φ' x + K * φ x) * Real.exp (K * x)) x := by
    intro x hx
    have he : HasDerivAt (fun y : ℝ => Real.exp (K * y)) (Real.exp (K * x) * K) x :=
      (hasDerivAt_const_mul (x := x) K).exp
    have hm : HasDerivAt (fun y : ℝ => φ y * Real.exp (K * y))
        (φ' x * Real.exp (K * x) + φ x * (Real.exp (K * x) * K)) x := (hd x hx).mul he
    have h1 : HasDerivAt (scalExp K φ)
        (φ' x * Real.exp (K * x) + φ x * (Real.exp (K * x) * K)) x := hm
    refine h1.congr_deriv ?_
    ring
  have hmono : MonotoneOn (scalExp K φ) (Set.Icc 0 T) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Icc 0 T)
      (f := scalExp K φ) (f' := fun x => (φ' x + K * φ x) * Real.exp (K * x))
      (convex_Icc 0 T) ?_ ?_ ?_
    · refine ContinuousOn.mul hφc ?_
      exact Continuous.continuousOn (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    · intro x hx
      rw [interior_Icc] at hx
      exact (hfd x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact mul_nonneg (by linarith [hineq x hx]) (Real.exp_pos _).le
  intro x hx
  have hx0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_refl 0, hx.1.trans hx.2⟩
  have hmon := hmono hx0 hx hx.1
  simp only [scalExp, mul_zero, Real.exp_zero, mul_one] at hmon
  have hxsimp : φ x * Real.exp (K * x) * Real.exp (-(K * x)) = φ x := by
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have h2 := mul_le_mul_of_nonneg_right hmon (Real.exp_pos (-(K * x))).le
  rwa [hxsimp] at h2

theorem thBounds {θ V : ℝ → ℝ} {K θ₀ T : ℝ} (hθc : ContinuousOn θ (Set.Icc 0 T)) (hθ0 : θ 0 = θ₀) (hderiv : ∀ x ∈ Set.Ioo 0 T, HasDerivAt θ (-(V x)) x) (hl : ∀ x ∈ Set.Ioo 0 T, |V x| ≤ K * θ x) (hu : ∀ x ∈ Set.Ioo 0 T, |V x| ≤ K * (Real.pi / 2 - θ x)) : ∀ x ∈ Set.Icc 0 T, θ₀ * Real.exp (-(K * x)) ≤ θ x ∧ θ x ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * x)) := by
  intro x hx
  constructor
  · -- lower bound: apply Grönwall to `θ` with `θ' = -V ≥ -K θ`
    have hineq : ∀ y ∈ Set.Ioo 0 T, -(K * θ y) ≤ -(V y) := by
      intro y hy
      have h := le_of_abs_le (hl y hy)
      linarith
    have key := gronwall_lower_fts (φ := θ) (φ' := fun y => -(V y)) (K := K) (T := T)
      hθc hderiv hineq x hx
    rwa [hθ0] at key
  · -- upper bound: apply Grönwall to `ψ = π/2 - θ` with `ψ' = V ≥ -K ψ`
    have hψc : ContinuousOn ((fun _ : ℝ => Real.pi / 2) - θ) (Set.Icc 0 T) :=
      continuousOn_const.sub hθc
    have hψd : ∀ y ∈ Set.Ioo 0 T, HasDerivAt ((fun _ : ℝ => Real.pi / 2) - θ) (V y) y := by
      intro y hy
      have h := (hasDerivAt_const y (Real.pi / 2)).sub (hderiv y hy)
      convert h using 1
      rw [zero_sub, neg_neg]
    have hψineq : ∀ y ∈ Set.Ioo 0 T, -(K * ((fun _ : ℝ => Real.pi / 2) - θ) y) ≤ V y := by
      intro y hy
      have h := neg_le_of_abs_le (hu y hy)
      simpa [Pi.sub_apply] using h
    have key := gronwall_lower_fts (φ := (fun _ : ℝ => Real.pi / 2) - θ) (φ' := V) (K := K) (T := T)
      hψc hψd hψineq x hx
    have key2 : (Real.pi / 2 - θ 0) * Real.exp (-(K * x)) ≤ Real.pi / 2 - θ x := by
      simpa [Pi.sub_apply] using key
    rw [hθ0] at key2
    linarith

end Work.FTS.RegPkgGal.R7d
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7d.zBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7d

/-- Two-sided bounds for the solution of the linear ODE `z' = -(z · V)` on `[0,T]`, where
`0 ≤ V ≤ a` and `z ≥ 0` on the open interval.

* the **upper** bound `z x ≤ z₀` is simply the antitonicity of `z`: `z' = -z·V ≤ 0`;
* the **lower** bound `z₀·exp (-(a·x)) ≤ z x` is the integrating-factor argument for
  `u x = z x · exp (a·x)`: `u' = z·(a - V)·exp (a·x) ≥ 0`, so `u` is monotone and
  `z₀ = u 0 ≤ u x = z x · exp (a·x)`.

The degenerate case `T ≤ 0` gives `Set.Icc 0 T = ∅` (or `{0}` when `T = 0`). -/
theorem zBounds {z V : ℝ → ℝ} {a z₀ T : ℝ} (hzc : ContinuousOn z (Set.Icc 0 T)) (hz0 : z 0 = z₀) (hderiv : ∀ x ∈ Set.Ioo 0 T, HasDerivAt z (-(z x * V x)) x) (hV0 : ∀ x ∈ Set.Ioo 0 T, 0 ≤ V x) (hVa : ∀ x ∈ Set.Ioo 0 T, V x ≤ a) (hzpos : ∀ x ∈ Set.Ioo 0 T, 0 ≤ z x) : ∀ x ∈ Set.Icc 0 T, z₀ * Real.exp (-(a * x)) ≤ z x ∧ z x ≤ z₀ := by
  rcases le_or_gt T 0 with hTle | hT
  · -- degenerate case: `x ∈ Set.Icc 0 T` forces `x = 0` and `T = 0`
    intro x hx
    have hx0 : x = 0 := le_antisymm (le_trans hx.2 hTle) hx.1
    rw [hx0, hz0]
    constructor <;> simp
  · have hD : Convex ℝ (Set.Icc 0 T) := convex_Icc 0 T
    have hIcc : interior (Set.Icc 0 T) = Set.Ioo 0 T := interior_Icc
    have h0D : (0:ℝ) ∈ Set.Icc 0 T := ⟨le_refl 0, hT.le⟩
    -- the integrating factor `u x = z x · exp (a·x)` and its derivative
    have hlin : ContinuousOn (fun x : ℝ => a * x) (Set.Icc 0 T) :=
      continuousOn_const.mul continuousOn_id
    have hexp_cont : ContinuousOn (fun x : ℝ => Real.exp (a * x)) (Set.Icc 0 T) :=
      Real.continuous_exp.comp_continuousOn hlin
    have hu_cont : ContinuousOn (fun x : ℝ => z x * Real.exp (a * x)) (Set.Icc 0 T) :=
      hzc.mul hexp_cont
    have hu_deriv : ∀ x ∈ interior (Set.Icc 0 T),
        HasDerivWithinAt (fun y : ℝ => z y * Real.exp (a * y))
          ((z x * (a - V x)) * Real.exp (a * x)) (interior (Set.Icc 0 T)) x := by
      intro x hx
      rw [hIcc] at hx ⊢
      have hz' : HasDerivAt z (-(z x * V x)) x := hderiv x hx
      have hlin' : HasDerivAt (fun y : ℝ => a * y) a x := by
        simpa using (hasDerivAt_id x).const_mul a
      have hexp' : HasDerivAt (fun y : ℝ => Real.exp (a * y)) (Real.exp (a * x) * a) x :=
        hlin'.exp
      have hprod := hz'.mul hexp'
      have hval : -(z x * V x) * Real.exp (a * x) + z x * (Real.exp (a * x) * a)
          = (z x * (a - V x)) * Real.exp (a * x) := by ring
      exact (hprod.congr_deriv hval).hasDerivWithinAt
    have hu_nn : ∀ x ∈ interior (Set.Icc 0 T), 0 ≤ (z x * (a - V x)) * Real.exp (a * x) := by
      intro x hx
      rw [hIcc] at hx
      exact mul_nonneg (mul_nonneg (hzpos x hx) (sub_nonneg.mpr (hVa x hx))) (Real.exp_pos _).le
    have hu_mono : MonotoneOn (fun y : ℝ => z y * Real.exp (a * y)) (Set.Icc 0 T) :=
      monotoneOn_of_hasDerivWithinAt_nonneg hD hu_cont hu_deriv hu_nn
    -- antitonicity of `z` itself
    have hz_deriv : ∀ x ∈ interior (Set.Icc 0 T),
        HasDerivWithinAt z (-(z x * V x)) (interior (Set.Icc 0 T)) x := by
      intro x hx
      rw [hIcc] at hx ⊢
      exact (hderiv x hx).hasDerivWithinAt
    have hz_np : ∀ x ∈ interior (Set.Icc 0 T), -(z x * V x) ≤ 0 := by
      intro x hx
      rw [hIcc] at hx
      have := mul_nonneg (hzpos x hx) (hV0 x hx)
      linarith
    have hz_anti : AntitoneOn z (Set.Icc 0 T) :=
      antitoneOn_of_hasDerivWithinAt_nonpos hD hzc hz_deriv hz_np
    intro x hx
    constructor
    · -- lower bound from the monotonicity of the integrating factor
      have hle := hu_mono h0D hx hx.1
      change z 0 * Real.exp (a * 0) ≤ z x * Real.exp (a * x) at hle
      rw [hz0, mul_zero, Real.exp_zero, mul_one] at hle
      have hgoal : z₀ * Real.exp (-(a * x)) = z₀ / Real.exp (a * x) := by
        rw [Real.exp_neg, div_eq_mul_inv]
      rw [hgoal]
      exact (div_le_iff₀ (Real.exp_pos _)).mpr hle
    · -- upper bound
      have hle := hz_anti h0D hx hx.1
      rw [hz0] at hle
      exact hle

end Work.FTS.RegPkgGal.R7d
end
-- ===== merged: Submission.Work.FTS.Regularity.Moduli.rpow_abs_sub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity.Moduli

/-- For `0 < p ≤ 1` the map `x ↦ x ^ p` is subadditive on `ℝ≥0`, hence `p`-Hölder
as a self-map of `ℝ≥0`. -/
lemma rpow_abs_sub_le {p s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hp0 : 0 < p) (hp1 : p ≤ 1) : |s ^ p - t ^ p| ≤ |s - t| ^ p := by
  rcases le_total t s with hts | hst
  · rw [abs_of_nonneg (sub_nonneg.2 hts),
      abs_of_nonneg (sub_nonneg.2 (Real.rpow_le_rpow ht hts hp0.le))]
    have h := Real.rpow_add_le_add_rpow ht (sub_nonneg.2 hts) hp0.le hp1
    rw [show t + (s - t) = s by ring] at h
    linarith
  · have h1 : s ^ p ≤ t ^ p := Real.rpow_le_rpow hs hst hp0.le
    have h := Real.rpow_add_le_add_rpow hs (sub_nonneg.2 hst) hp0.le hp1
    rw [show s + (t - s) = t by ring] at h
    rw [abs_of_nonpos (sub_nonpos.2 h1), abs_of_nonpos (sub_nonpos.2 hst)]
    simp only [neg_sub]
    linarith

end Work.FTS.Regularity.Moduli
end
-- ===== merged: Submission.Work.FTS.Regularity.Moduli.sinCosSqLip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity.Moduli

/-- `θ ↦ sin θ * cos θ ^ 2` is 3-Lipschitz on `ℝ` (its true Lipschitz constant is
`4√2/9 < 1`, but the crude bound `3` is what is needed). -/
lemma sinCosSqLip (θ θ' : ℝ) : |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ≤ 3 * |θ - θ'| := by
  have hsin : |Real.sin θ - Real.sin θ'| ≤ |θ - θ'| := Real.abs_sin_sub_sin_le θ θ'
  have hcos : |Real.cos θ - Real.cos θ'| ≤ |θ - θ'| := Real.abs_cos_sub_cos_le θ θ'
  have hD : 0 ≤ |θ - θ'| := abs_nonneg _
  have hcos2 : |Real.cos θ ^ 2 - Real.cos θ' ^ 2| ≤ 2 * |θ - θ'| := by
    have hfac : Real.cos θ ^ 2 - Real.cos θ' ^ 2
        = (Real.cos θ - Real.cos θ') * (Real.cos θ + Real.cos θ') := by ring
    rw [hfac, abs_mul]
    have h2 : |Real.cos θ + Real.cos θ'| ≤ 2 := by
      have := abs_add_le (Real.cos θ) (Real.cos θ')
      have a1 := Real.abs_cos_le_one θ
      have a2 := Real.abs_cos_le_one θ'
      linarith
    calc |Real.cos θ - Real.cos θ'| * |Real.cos θ + Real.cos θ'|
        ≤ |θ - θ'| * 2 := mul_le_mul hcos h2 (abs_nonneg _) hD
      _ = 2 * |θ - θ'| := by ring
  have hsq : |Real.cos θ' ^ 2| ≤ 1 := by
    rw [abs_pow]
    nlinarith [Real.abs_cos_le_one θ', abs_nonneg (Real.cos θ')]
  have h1 : |Real.sin θ| * |Real.cos θ ^ 2 - Real.cos θ' ^ 2| ≤ 1 * (2 * |θ - θ'|) :=
    mul_le_mul (Real.abs_sin_le_one θ) hcos2 (abs_nonneg _) (by norm_num)
  have h2 : |Real.sin θ - Real.sin θ'| * |Real.cos θ' ^ 2| ≤ |θ - θ'| * 1 :=
    mul_le_mul hsin hsq (abs_nonneg _) hD
  calc |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2|
      = |Real.sin θ * (Real.cos θ ^ 2 - Real.cos θ' ^ 2)
          + (Real.sin θ - Real.sin θ') * Real.cos θ' ^ 2| := by
        congr 1; ring
    _ ≤ |Real.sin θ * (Real.cos θ ^ 2 - Real.cos θ' ^ 2)|
          + |(Real.sin θ - Real.sin θ') * Real.cos θ' ^ 2| := abs_add_le _ _
    _ = |Real.sin θ| * |Real.cos θ ^ 2 - Real.cos θ' ^ 2|
          + |Real.sin θ - Real.sin θ'| * |Real.cos θ' ^ 2| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (2 * |θ - θ'|) + |θ - θ'| * 1 := add_le_add h1 h2
    _ = 3 * |θ - θ'| := by ring

end Work.FTS.Regularity.Moduli
end
-- ===== merged: Submission.Work.FTS.Regularity.deriv_eq_zero_of_const_on_Icc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity

open Filter Set
open scoped Topology

/-- If `f` is constant on the closed interval `[a, b]` (with `a < b`), then its derivative
vanishes at every point of `[a, b]`: at interior points `f` is locally constant, and at the
endpoints `f` is frequently equal to `f x` on the punctured neighbourhoods, so the derivative
is zero (either `f` is not differentiable there, or the derivative is forced to be `0`). -/
theorem deriv_eq_zero_of_const_on_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f x = f y) :
    ∀ x ∈ Set.Icc a b, deriv f x = 0 := by
  intro x hx
  -- It suffices that `f` frequently equals `f x` on the punctured neighbourhood of `x`.
  apply deriv_zero_of_frequently_const
  rw [Filter.frequently_iff]
  intro U hU
  -- A punctured neighbourhood contains `ball x ε \ {x}`.
  rw [Metric.mem_nhdsWithin_iff] at hU
  obtain ⟨ε, hε, hball⟩ := hU
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · -- `x < b`: step to the right into `(x, b) ⊆ [a, b]`.
    set d : ℝ := min (ε / 2) ((b - x) / 2) with hd
    have hdpos : 0 < d := by rw [hd]; exact lt_min (by linarith) (by linarith)
    refine ⟨x + d, hball ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq]
      have h1 : x + d - x = d := by ring
      rw [h1, abs_of_pos hdpos]
      have h2 : d ≤ ε / 2 := by rw [hd]; exact min_le_left _ _
      linarith
    · exact ne_of_gt (by linarith)
    · have hyb : x + d < b := by
        have h2 : d ≤ (b - x) / 2 := by rw [hd]; exact min_le_right _ _
        linarith
      exact hf _ ⟨hx.1.trans (by linarith), hyb.le⟩ x hx
  · -- `x = b`: step to the left into `(a, b) ⊆ [a, b]`.
    have hax : a < x := by rw [heq]; exact hab
    set d : ℝ := min (ε / 2) ((x - a) / 2) with hd
    have hdpos : 0 < d := by rw [hd]; exact lt_min (by linarith) (by linarith)
    refine ⟨x - d, hball ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq]
      have h1 : x - d - x = -d := by ring
      rw [h1, abs_neg, abs_of_pos hdpos]
      have h2 : d ≤ ε / 2 := by rw [hd]; exact min_le_left _ _
      linarith
    · exact ne_of_lt (by linarith)
    · have had : a < x - d := by
        have h2 : d ≤ (x - a) / 2 := by rw [hd]; exact min_le_right _ _
        linarith
      have hxb : x - d ≤ b := by rw [← heq]; linarith
      exact hf _ ⟨had.le, hxb⟩ x hx

end Work.FTS.Regularity
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.abs_sub_le_exp_sqrt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

/-- Two nonnegative reals that are comparable up to a factor `E ≥ 1` are within
`(E - 1)·√(a·b)` of each other.  Elementary: if `b ≤ a ≤ E·b` then
`a - b ≤ (E - 1)·b ≤ (E - 1)·√(a·b)` (as `b ≤ √(a·b)` when `b ≤ a`); the other case is
symmetric. -/
theorem abs_sub_le_exp_sqrt {a b E : ℝ} (hE : 1 ≤ E) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : a ≤ E * b) (h2 : b ≤ E * a) :
    |a - b| ≤ (E - 1) * Real.sqrt (a * b) := by
  have hE1 : 0 ≤ E - 1 := by linarith
  have step : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ E * x →
      y - x ≤ (E - 1) * Real.sqrt (x * y) := by
    intro x y hx hxy hyE
    have hs : Real.sqrt (x * x) ≤ Real.sqrt (x * y) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hxy hx)
    have hxs : x ≤ Real.sqrt (x * y) := by rwa [Real.sqrt_mul_self hx] at hs
    calc y - x ≤ (E - 1) * x := by nlinarith [hyE]
      _ ≤ (E - 1) * Real.sqrt (x * y) := mul_le_mul_of_nonneg_left hxs hE1
  rcases le_total b a with hba | hab
  · have h := step b a hb hba h1
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b)]
    simpa [mul_comm] using h
  · have h := step a b ha hab h2
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)]
    exact h

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_conv_pair =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Joint integrability of the two mollifier-convolution pairings

`integrable_conv_pair` is the measure-theoretic core of the `IP6`-transfer estimate for the
Friedrichs mollifier `J_ε` in the log coordinates: the mollifier is an even convolution over the
plane, so after the change of variables `(s,ζ) = (log z, log tan θ)` the level-`k` pairing is an
integral over `(y, p) ∈ (ℝ × ℝ)²` of

  `Q y * k p * G₁ (y - p) * G₂ y`   resp.   `Q y * k p * G₁ y * G₂ (y - p)`,

with `Q` the pulled-back weight (which is only *shift-bounded*,
`Q (y + p) ≤ exp (Cw * (|p.1| + |p.2|)) * Q y`, not bounded) and `k` the mollifier kernel, which is
nonnegative, integrable and supported in the box `|p.1| + |p.2| ≤ 2 ε`.

The proof is an AM–GM: `2 |G₁ (y - p)| |G₂ y| ≤ G₁ (y - p)² + G₂ y²`.  The two resulting pieces are

* `k p * (Q (y - p) * G₁ (y - p)²)` — integrable by the Mathlib convolution lemma
  `MeasureTheory.Integrable.convolution_integrand` (one factor shifted in the first variable),
* `k p * (Q y * G₂ y²)` — a product function, integrable by `Integrable.mul_prod` and `swap`.

The only point that needs the support of `k` is the comparison of the shift bound with a constant
factor: for `p` in the support, `exp (Cw * (|p.1| + |p.2|)) ≤ exp (2 * Cw * ε)`, which is what turns
`Q y ≤ exp (Cw * (|p.1| + |p.2|)) * Q (y - p)` into `Q y ≤ c * Q (y - p)` with `c` *independent*
of `p`; the pointwise bound `k p * f p ≤ c * k p ≤ …` is then a legitimate domination.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

open MeasureTheory

/-- **The AM–GM pair bound.**  If `k` is nonnegative and supported in the box
`|p.1| + |p.2| ≤ 2 ε`, and the weight `Q ≥ 0` is shift-bounded with constant `Cw ≥ 0`, then the
product `Q y * k p * G (y - p) * H y` is dominated by

`(c/2) * (k p * (Q (y - p) * G (y - p)²)) + (c/2) * (k p * (Q y * H y²))`  with  `c = e^{2 Cw ε}`,

where the two summands are joint *product* functions (one factor shifted, one unshifted). -/
theorem integrable_shifted_pair {k Q G H : ℝ × ℝ → ℝ} {Cw ε : ℝ} (hCw : 0 ≤ Cw)
    (hk : MeasureTheory.Integrable k) (hk0 : ∀ p : ℝ × ℝ, 0 ≤ k p)
    (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hGm : Measurable G) (hHm : Measurable H)
    (hGi : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G y ^ 2))
    (hHi : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * H y ^ 2)) :
    MeasureTheory.Integrable
      (Function.uncurry fun (y p : ℝ × ℝ) => Q y * k p * G (y - p) * H y) := by
  change MeasureTheory.Integrable
    (fun z : (ℝ × ℝ) × (ℝ × ℝ) => Q z.1 * k z.2 * G (z.1 - z.2) * H z.1) volume
  set c : ℝ := Real.exp (2 * Cw * ε) with hc
  -- the shift bound at `p` is at most the constant `c`, on the support of `k`
  have hc_le : ∀ p : ℝ × ℝ, k p ≠ 0 → Real.exp (Cw * (|p.1| + |p.2|)) ≤ c := by
    intro p hp
    rw [hc]
    apply Real.exp_le_exp.mpr
    have hle : |p.1| + |p.2| ≤ 2 * ε := hksupp p hp
    calc Cw * (|p.1| + |p.2|) ≤ Cw * (2 * ε) := mul_le_mul_of_nonneg_left hle hCw
      _ = 2 * Cw * ε := by ring
  -- on the support, the constant is `≥ 1` (so the unshifted summand is also dominated)
  have hc1 : ∀ p : ℝ × ℝ, k p ≠ 0 → 1 ≤ c := by
    intro p hp
    rw [hc, Real.one_le_exp_iff]
    have hle : |p.1| + |p.2| ≤ 2 * ε := hksupp p hp
    have hnn : (0 : ℝ) ≤ |p.1| + |p.2| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    calc (0 : ℝ) ≤ Cw * (2 * ε) := mul_nonneg hCw (le_trans hnn hle)
      _ = 2 * Cw * ε := by ring
  have hmeas : AEStronglyMeasurable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => Q z.1 * k z.2 * G (z.1 - z.2) * H z.1)
      (volume.prod volume) :=
    (((hQm.comp measurable_fst).aestronglyMeasurable.mul
        hk.aestronglyMeasurable.comp_snd).mul
      (hGm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable).mul
      (hHm.comp measurable_fst).aestronglyMeasurable
  -- the shifted product is integrable by the convolution lemma for the two factors `k` and `Q G²`
  have hshift : MeasureTheory.Integrable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (Q (z.1 - z.2) * G (z.1 - z.2) ^ 2))
      (volume.prod volume) :=
    MeasureTheory.Integrable.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ)
      (μ := volume) (ν := volume) (f := k) (g := fun y : ℝ × ℝ => Q y * G y ^ 2) hk hGi
  -- the unshifted product is integrable by `mul_prod` and commutation of the two variables
  have hprod : MeasureTheory.Integrable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (Q z.1 * H z.1 ^ 2)) (volume.prod volume) :=
    (MeasureTheory.Integrable.mul_prod (μ := volume) (ν := volume) (f := k)
      (g := fun y : ℝ × ℝ => Q y * H y ^ 2) hk hHi).swap
  refine MeasureTheory.Integrable.mono'
    (g := fun z : (ℝ × ℝ) × (ℝ × ℝ) => c / 2 * (k z.2 * (Q (z.1 - z.2) * G (z.1 - z.2) ^ 2))
      + c / 2 * (k z.2 * (Q z.1 * H z.1 ^ 2))) ?_ hmeas ?_
  · exact (hshift.const_mul (c / 2)).add (hprod.const_mul (c / 2))
  · filter_upwards with z
    by_cases hp : k z.2 = 0
    · simp [hp]
    · have hB : 0 < k z.2 := lt_of_le_of_ne (hk0 z.2) (Ne.symm hp)
      have hA : 0 ≤ Q z.1 := hQ0 z.1
      have hAB : 0 ≤ Q z.1 * k z.2 := mul_nonneg hA hB.le
      have hQp : 0 ≤ Q (z.1 - z.2) := hQ0 _
      have hG2 : 0 ≤ G (z.1 - z.2) ^ 2 := sq_nonneg _
      have hH2 : 0 ≤ H z.1 ^ 2 := sq_nonneg _
      have hQle : Q z.1 ≤ c * Q (z.1 - z.2) := by
        have h := hQsh (z.1 - z.2) z.2
        rw [sub_add_cancel] at h
        exact le_trans h (mul_le_mul_of_nonneg_right (hc_le z.2 hp) hQp)
      have hAM : |G (z.1 - z.2)| * |H z.1| ≤ (G (z.1 - z.2) ^ 2 + H z.1 ^ 2) / 2 := by
        nlinarith [sq_nonneg (|G (z.1 - z.2)| - |H z.1|), sq_abs (G (z.1 - z.2)),
          sq_abs (H z.1), abs_nonneg (G (z.1 - z.2)), abs_nonneg (H z.1)]
      have hstep1 : Q z.1 * k z.2 * |G (z.1 - z.2)| * |H z.1|
          ≤ (Q z.1 * k z.2 * G (z.1 - z.2) ^ 2 + Q z.1 * k z.2 * H z.1 ^ 2) / 2 := by
        calc Q z.1 * k z.2 * |G (z.1 - z.2)| * |H z.1|
            = (Q z.1 * k z.2) * (|G (z.1 - z.2)| * |H z.1|) := by ring
          _ ≤ (Q z.1 * k z.2) * ((G (z.1 - z.2) ^ 2 + H z.1 ^ 2) / 2) :=
              mul_le_mul_of_nonneg_left hAM hAB
          _ = (Q z.1 * k z.2 * G (z.1 - z.2) ^ 2 + Q z.1 * k z.2 * H z.1 ^ 2) / 2 := by ring
      have hstep2 : Q z.1 * k z.2 * G (z.1 - z.2) ^ 2
          ≤ c * k z.2 * (Q (z.1 - z.2) * G (z.1 - z.2) ^ 2) := by
        calc Q z.1 * k z.2 * G (z.1 - z.2) ^ 2
            = Q z.1 * (k z.2 * G (z.1 - z.2) ^ 2) := by ring
          _ ≤ (c * Q (z.1 - z.2)) * (k z.2 * G (z.1 - z.2) ^ 2) :=
              mul_le_mul_of_nonneg_right hQle (mul_nonneg hB.le hG2)
          _ = c * k z.2 * (Q (z.1 - z.2) * G (z.1 - z.2) ^ 2) := by ring
      have hstep3 : Q z.1 * k z.2 * H z.1 ^ 2 ≤ c * k z.2 * (Q z.1 * H z.1 ^ 2) := by
        calc Q z.1 * k z.2 * H z.1 ^ 2 = 1 * (Q z.1 * k z.2 * H z.1 ^ 2) := by ring
          _ ≤ c * (Q z.1 * k z.2 * H z.1 ^ 2) :=
              mul_le_mul_of_nonneg_right (hc1 z.2 hp) (mul_nonneg hAB hH2)
          _ = c * k z.2 * (Q z.1 * H z.1 ^ 2) := by ring
      have hnorm : ‖Q z.1 * k z.2 * G (z.1 - z.2) * H z.1‖
          = Q z.1 * k z.2 * |G (z.1 - z.2)| * |H z.1| := by
        rw [Real.norm_eq_abs]
        simp only [abs_mul, abs_of_nonneg hA, abs_of_nonneg hB.le]
      rw [hnorm]
      linarith [hstep1, hstep2, hstep3]


end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_mixed_pair =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

open MeasureTheory

/-- Weighted pointwise `2ab ≤ a² + b²` estimate: if the weight `Q` is bounded by `c₁` times the
weight `Q₁` carrying `f` and by `c₂` times the weight `Q₂` carrying `g` (all weights nonnegative),
then `Q f g` is dominated by `c₁ (Q₁ f²) + c₂ (Q₂ g²)`. -/
private lemma abs_weight_mul_le {Q Q₁ Q₂ f g : ℝ × ℝ → ℝ} {c₁ c₂ : ℝ}
    (hQ0 : ∀ y, 0 ≤ Q y) (hQ10 : ∀ y, 0 ≤ Q₁ y) (hQ20 : ∀ y, 0 ≤ Q₂ y)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h1 : ∀ y, Q y ≤ c₁ * Q₁ y) (h2 : ∀ y, Q y ≤ c₂ * Q₂ y) (y : ℝ × ℝ) :
    |Q y * f y * g y| ≤ c₁ * (Q₁ y * f y ^ 2) + c₂ * (Q₂ y * g y ^ 2) := by
  have hQ : 0 ≤ Q y := hQ0 y
  have h2xy : 2 * |f y| * |g y| ≤ f y ^ 2 + g y ^ 2 := by
    nlinarith [sq_nonneg (|f y| - |g y|), sq_abs (f y), sq_abs (g y)]
  have hmain : Q y * |f y| * |g y| ≤ (Q y * f y ^ 2 + Q y * g y ^ 2) / 2 := by
    have h := mul_le_mul_of_nonneg_left h2xy hQ
    linarith [h]
  have hQf : Q y * f y ^ 2 ≤ c₁ * (Q₁ y * f y ^ 2) := by
    calc Q y * f y ^ 2 ≤ (c₁ * Q₁ y) * f y ^ 2 :=
          mul_le_mul_of_nonneg_right (h1 y) (sq_nonneg (f y))
      _ = c₁ * (Q₁ y * f y ^ 2) := by ring
  have hQg : Q y * g y ^ 2 ≤ c₂ * (Q₂ y * g y ^ 2) := by
    calc Q y * g y ^ 2 ≤ (c₂ * Q₂ y) * g y ^ 2 :=
          mul_le_mul_of_nonneg_right (h2 y) (sq_nonneg (g y))
      _ = c₂ * (Q₂ y * g y ^ 2) := by ring
  have hA : 0 ≤ c₁ * (Q₁ y * f y ^ 2) := mul_nonneg hc₁ (mul_nonneg (hQ10 y) (sq_nonneg (f y)))
  have hB : 0 ≤ c₂ * (Q₂ y * g y ^ 2) := mul_nonneg hc₂ (mul_nonneg (hQ20 y) (sq_nonneg (g y)))
  rw [abs_mul, abs_mul, abs_of_nonneg hQ]
  linarith [hmain, hQf, hQg, hA, hB]

/-- Integrability of a mixed product from two weighted `L²` bounds, when the cross weight `Q` is
controlled by the weights `Q₁`, `Q₂` attached to the two factors. -/
private lemma integrable_weight_cross {Q Q₁ Q₂ : ℝ × ℝ → ℝ} {c₁ c₂ : ℝ} {f g : ℝ × ℝ → ℝ}
    (hQm : Measurable Q) (hQ0 : ∀ y, 0 ≤ Q y) (hQ10 : ∀ y, 0 ≤ Q₁ y) (hQ20 : ∀ y, 0 ≤ Q₂ y)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h1 : ∀ y, Q y ≤ c₁ * Q₁ y) (h2 : ∀ y, Q y ≤ c₂ * Q₂ y)
    (hfm : Measurable f) (hgm : Measurable g)
    (hI1 : Integrable (fun y => Q₁ y * f y ^ 2))
    (hI2 : Integrable (fun y => Q₂ y * g y ^ 2)) :
    Integrable (fun y => Q y * f y * g y) := by
  refine Integrable.mono' ((hI1.const_mul c₁).add (hI2.const_mul c₂))
    ((hQm.mul hfm).mul hgm).aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs]
  exact abs_weight_mul_le hQ0 hQ10 hQ20 hc₁ hc₂ h1 h2 y

theorem integrable_mixed_pair {Q G₁ G₂ : ℝ × ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hQsh' : ∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p))
    (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) (p : ℝ × ℝ) :
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ (y - p) * G₂ y) ∧
      MeasureTheory.Integrable (fun y : ℝ × ℝ => Q (y - p) * G₁ (y - p) * G₂ y) ∧
      MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y * G₂ (y + p)) ∧
      MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y * G₂ (y - p)) := by
  have hE : (0 : ℝ) ≤ Real.exp (Cw * (|p.1| + |p.2|)) := Real.exp_nonneg _
  have hmsub : Measurable (fun y : ℝ × ℝ => y - p) := measurable_id.sub measurable_const
  have hmadd : Measurable (fun y : ℝ × ℝ => y + p) := measurable_id.add measurable_const
  have hG1sub : Measurable (fun y : ℝ × ℝ => G₁ (y - p)) := hG1m.comp hmsub
  have hG2sub : Measurable (fun y : ℝ × ℝ => G₂ (y - p)) := hG2m.comp hmsub
  have hG2add : Measurable (fun y : ℝ × ℝ => G₂ (y + p)) := hG2m.comp hmadd
  -- shifted weighted `L²` bounds, from translation invariance of Lebesgue measure on `ℝ × ℝ`
  have hI1sub : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q (y - p) * G₁ (y - p) ^ 2) := by
    simpa only [] using hI1.comp_sub_right p
  have hI2sub : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q (y - p) * G₂ (y - p) ^ 2) := by
    simpa only [] using hI2.comp_sub_right p
  have hI2add : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q (y + p) * G₂ (y + p) ^ 2) := by
    simpa only [] using hI2.comp_add_right p
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `∫ Q y G₁(y-p) G₂ y` : use the weight `Q(y-p)` for `G₁`, bounding `Q y ≤ e Q (y-p)`
    exact integrable_weight_cross (Q := Q) (Q₁ := fun y => Q (y - p)) (Q₂ := Q)
      (c₁ := Real.exp (Cw * (|p.1| + |p.2|))) (c₂ := 1)
      hQm hQ0 (fun y => hQ0 (y - p)) hQ0 hE (by norm_num)
      (fun y => by simpa using hQsh (y - p) p) (fun y => by simp)
      hG1sub hG2m hI1sub hI2
  · -- `∫ Q(y-p) G₁(y-p) G₂ y` : use the weight `Q(y-p)` for `G₂`, bounding `Q (y-p) ≤ e Q y`
    exact integrable_weight_cross (Q := fun y => Q (y - p)) (Q₁ := fun y => Q (y - p)) (Q₂ := Q)
      (c₁ := 1) (c₂ := Real.exp (Cw * (|p.1| + |p.2|)))
      (hQm.comp hmsub) (fun y => hQ0 (y - p)) (fun y => hQ0 (y - p)) hQ0 (by norm_num) hE
      (fun y => by simp) (fun y => by simpa using hQsh' (y - p) p)
      hG1sub hG2m hI1sub hI2
  · -- `∫ Q y G₁ y G₂(y+p)` : use the weight `Q(y+p)` for `G₂`, bounding `Q y ≤ e Q (y+p)`
    exact integrable_weight_cross (Q := Q) (Q₁ := Q) (Q₂ := fun y => Q (y + p))
      (c₁ := 1) (c₂ := Real.exp (Cw * (|p.1| + |p.2|)))
      hQm hQ0 hQ0 (fun y => hQ0 (y + p)) (by norm_num) hE
      (fun y => by simp) (fun y => by simpa using hQsh' y p)
      hG1m hG2add hI1 hI2add
  · -- `∫ Q y G₁ y G₂(y-p)` : use the weight `Q(y-p)` for `G₂`, bounding `Q y ≤ e Q (y-p)`
    exact integrable_weight_cross (Q := Q) (Q₁ := Q) (Q₂ := fun y => Q (y - p))
      (c₁ := 1) (c₂ := Real.exp (Cw * (|p.1| + |p.2|)))
      hQm hQ0 hQ0 (fun y => hQ0 (y - p)) (by norm_num) hE
      (fun y => by simp) (fun y => by simpa using hQsh (y - p) p)
      hG1m hG2sub hI1 hI2sub

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_mul_of_sq_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

theorem integrable_mul_of_sq_integrable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g : α → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hfi : MeasureTheory.Integrable (fun y => f y ^ 2) μ)
    (hgi : MeasureTheory.Integrable (fun y => g y ^ 2) μ) :
    MeasureTheory.Integrable (fun y => f y * g y) μ := by
  -- Cauchy--Schwarz: `‖f y * g y‖ ≤ f y ^ 2 + g y ^ 2` pointwise, and the right-hand
  -- side is integrable by hypothesis.
  have hsum : MeasureTheory.Integrable (fun y => f y ^ 2 + g y ^ 2) μ := hfi.add hgi
  refine hsum.mono' ((hfm.mul hgm).aestronglyMeasurable) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_mul, ← sq_abs (f y), ← sq_abs (g y)]
  nlinarith [two_mul_le_add_sq (|f y|) (|g y|), abs_nonneg (f y), abs_nonneg (g y)]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integral_mul_le_sqrt_mul_sqrt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

/-- Cauchy–Schwarz (Hölder with conjugate exponents `p = q = 2`) for two nonnegative
real-valued functions whose squares are integrable:
`∫ f * g ≤ sqrt (∫ f²) * sqrt (∫ g²)`. -/
theorem integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g : α → ℝ} (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y)
    (hfm : Measurable f) (hgm : Measurable g)
    (hfi : MeasureTheory.Integrable (fun y => f y ^ 2) μ)
    (hgi : MeasureTheory.Integrable (fun y => g y ^ 2) μ) :
    ∫ y, f y * g y ∂μ ≤ Real.sqrt (∫ y, f y ^ 2 ∂μ) * Real.sqrt (∫ y, g y ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  -- `L²`-membership of `f` and `g` from square-integrability.
  have hf2 : MeasureTheory.MemLp f (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr hfi
  have hg2 : MeasureTheory.MemLp g (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr hgi
  have hmain := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (Filter.Eventually.of_forall hf) (Filter.Eventually.of_forall hg) hf2 hg2
  -- Rewrite the real powers `f ^ (2 : ℝ)` as squares and `x ^ (1/2)` as `sqrt x`.
  have h1 : ∫ y, f y ^ (2 : ℝ) ∂μ = ∫ y, f y ^ 2 ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only [Real.rpow_two]
  have h2 : ∫ y, g y ^ (2 : ℝ) ∂μ = ∫ y, g y ^ 2 ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only [Real.rpow_two]
  simpa [h1, h2, Real.sqrt_eq_rpow] using hmain

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.shiftNormLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

set_option linter.unusedVariables false in
theorem shiftNormLe {Q G : ℝ × ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hG : Measurable G) (hI : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G y ^ 2))
    (p : ℝ × ℝ) :
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G (y - p) ^ 2) ∧
      ∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2
        ≤ Real.exp (Cw * (|p.1| + |p.2|)) * ∫ y : ℝ × ℝ, Q y * G y ^ 2 := by
  set c : ℝ := Real.exp (Cw * (|p.1| + |p.2|)) with hc
  -- the backwards shift bound on the weight
  have hQshift : ∀ y : ℝ × ℝ, Q y ≤ c * Q (y - p) := by
    intro y
    rw [hc]
    simpa using hQsh (y - p) p
  have hsub : Measurable fun y : ℝ × ℝ => y - p := measurable_id.sub measurable_const
  -- the shifted integrand, which is integrable by translation invariance
  have hH : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q (y - p) * G (y - p) ^ 2) :=
    hI.comp_sub_right p
  have hcH : MeasureTheory.Integrable (fun y : ℝ × ℝ => c * (Q (y - p) * G (y - p) ^ 2)) :=
    hH.const_mul c
  have hFmeas : MeasureTheory.AEStronglyMeasurable (fun y : ℝ × ℝ => Q y * G (y - p) ^ 2) :=
    (hQm.mul ((hG.comp hsub).pow_const 2)).aestronglyMeasurable
  -- the pointwise comparison, both for the integral and (through `‖·‖`) for integrability
  have hle : ∀ y : ℝ × ℝ, Q y * G (y - p) ^ 2 ≤ c * (Q (y - p) * G (y - p) ^ 2) := by
    intro y
    have h := mul_le_mul_of_nonneg_right (hQshift y) (sq_nonneg (G (y - p)))
    calc Q y * G (y - p) ^ 2 ≤ (c * Q (y - p)) * G (y - p) ^ 2 := h
      _ = c * (Q (y - p) * G (y - p) ^ 2) := by ring
  have hnorm : ∀ y : ℝ × ℝ, ‖Q y * G (y - p) ^ 2‖ ≤ c * (Q (y - p) * G (y - p) ^ 2) := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hQ0 y) (sq_nonneg (G (y - p))))]
    exact hle y
  have hFint : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G (y - p) ^ 2) :=
    hcH.mono' hFmeas (Filter.Eventually.of_forall hnorm)
  refine ⟨hFint, ?_⟩
  calc ∫ y : ℝ × ℝ, Q y * G (y - p) ^ 2
      ≤ ∫ y : ℝ × ℝ, c * (Q (y - p) * G (y - p) ^ 2) :=
        MeasureTheory.integral_mono hFint hcH hle
    _ = c * ∫ y : ℝ × ℝ, Q (y - p) * G (y - p) ^ 2 :=
        MeasureTheory.integral_const_mul c (fun y : ℝ × ℝ => Q (y - p) * G (y - p) ^ 2)
    _ = c * ∫ y : ℝ × ℝ, Q y * G y ^ 2 := by
        congr 1
        exact MeasureTheory.integral_sub_right_eq_self (fun y : ℝ × ℝ => Q y * G y ^ 2) p
    _ = Real.exp (Cw * (|p.1| + |p.2|)) * ∫ y : ℝ × ℝ, Q y * G y ^ 2 := by rw [hc]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.exp_moment_pt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2

/-- Pointwise exponential moment bound.

For `0 ≤ Cw`, `0 ≤ ε ≤ 1` and `0 ≤ u ≤ 2·Cw·ε` one has
`2 (e^u - 1) e^u ≤ 4·Cw·ε·e^{4 Cw}`.

The proof uses the tangent-line bound `e^u - 1 ≤ u e^u` (equivalently
`1 - u ≤ e^{-u}`, i.e. the tangent line of `exp` at `0`), then
`e^u ≤ e^{2 Cw ε} ≤ e^{4 Cw}` (as `ε ≤ 1` and `Cw ≥ 0`). -/
theorem exp_moment_pt {Cw ε u : ℝ} (hCw : 0 ≤ Cw) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu : 0 ≤ u) (hu2 : u ≤ 2 * Cw * ε) :
    2 * (Real.exp u - 1) * Real.exp u ≤ 4 * Cw * ε * Real.exp (4 * Cw) := by
  have hCwε : 0 ≤ Cw * ε := mul_nonneg hCw hε0
  have hEpos : 0 < Real.exp u := Real.exp_pos u
  -- Tangent-line bound: `e^u - 1 ≤ u * e^u` for `u ≥ 0`.
  have h3 : Real.exp u - 1 ≤ u * Real.exp u := by
    have hlin : 1 - u ≤ Real.exp (-u) := by
      have h := Real.add_one_le_exp (-u); linarith
    have hmul : (1 - u) * Real.exp u ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hlin hEpos.le
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
      exact h
    nlinarith [hmul]
  have h4 : Real.exp u ≤ Real.exp (2 * Cw * ε) := Real.exp_le_exp.2 hu2
  have hsq : Real.exp (2 * Cw * ε) ^ 2 = Real.exp (4 * Cw * ε) := by
    rw [sq, ← Real.exp_add, Real.exp_eq_exp]; ring
  have h5 : Real.exp (4 * Cw * ε) ≤ Real.exp (4 * Cw) := by
    apply Real.exp_le_exp.2
    nlinarith [hCw, hε0, hε1]
  have hA : 2 * (Real.exp u - 1) * Real.exp u ≤ 2 * u * Real.exp u ^ 2 := by
    calc 2 * (Real.exp u - 1) * Real.exp u
        ≤ 2 * (u * Real.exp u) * Real.exp u := by
          have h2 : 2 * (Real.exp u - 1) ≤ 2 * (u * Real.exp u) := by linarith
          exact mul_le_mul_of_nonneg_right h2 hEpos.le
      _ = 2 * u * Real.exp u ^ 2 := by ring
  have hB : 2 * u * Real.exp u ^ 2 ≤
      2 * (2 * Cw * ε) * Real.exp (2 * Cw * ε) ^ 2 := by
    have h1 : 2 * u ≤ 2 * (2 * Cw * ε) := by linarith
    have h2 : Real.exp u ^ 2 ≤ Real.exp (2 * Cw * ε) ^ 2 :=
      pow_le_pow_left₀ hEpos.le h4 2
    exact mul_le_mul h1 h2 (by positivity) (by linarith)
  have hC : 4 * Cw * ε * Real.exp (4 * Cw * ε) ≤ 4 * Cw * ε * Real.exp (4 * Cw) :=
    mul_le_mul_of_nonneg_left h5 (by linarith)
  calc 2 * (Real.exp u - 1) * Real.exp u
      ≤ 2 * u * Real.exp u ^ 2 := hA
    _ ≤ 2 * (2 * Cw * ε) * Real.exp (2 * Cw * ε) ^ 2 := hB
    _ = 4 * Cw * ε * Real.exp (4 * Cw * ε) := by rw [hsq]; ring
    _ ≤ 4 * Cw * ε * Real.exp (4 * Cw) := hC

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.weight_diff_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2

open MeasureTheory

/-- Cauchy–Schwarz in the `L²` form used for Schur-type estimates:
`∫ |A| * |B| ≤ √(∫ A²) * √(∫ B²)`. -/
lemma abs_integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A B : α → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA2 : Integrable (fun a => A a ^ 2) μ) (hB2 : Integrable (fun a => B a ^ 2) μ) :
    ∫ a, |A a| * |B a| ∂μ ≤ Real.sqrt (∫ a, A a ^ 2 ∂μ) * Real.sqrt (∫ a, B a ^ 2 ∂μ) := by
  have hmA : MemLp (fun a => |A a|) 2 μ := by
    rw [memLp_two_iff_integrable_sq]
    · simpa [sq_abs] using hA2
    · exact hAm.abs.aestronglyMeasurable
  have hmB : MemLp (fun a => |B a|) 2 μ := by
    rw [memLp_two_iff_integrable_sq]
    · simpa [sq_abs] using hB2
    · exact hBm.abs.aestronglyMeasurable
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (Real.HolderConjugate.two_two)
      (ae_of_all _ fun a => abs_nonneg _) (ae_of_all _ fun a => abs_nonneg _)
      (by simpa using hmA) (by simpa using hmB)
  have e1 : (∫ a, |A a| ^ (2:ℝ) ∂μ) = ∫ a, A a ^ 2 ∂μ :=
    integral_congr_ae (ae_of_all _ fun a => by simp only [Real.rpow_two, sq_abs])
  have e2 : (∫ a, |B a| ^ (2:ℝ) ∂μ) = ∫ a, B a ^ 2 ∂μ :=
    integral_congr_ae (ae_of_all _ fun a => by simp only [Real.rpow_two, sq_abs])
  rw [e1, e2] at h
  simp only [← Real.sqrt_eq_rpow] at h
  exact h

theorem weight_diff_integral_le {Q G₁ G₂ : ℝ × ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hQsh' : ∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p))
    (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) (p : ℝ × ℝ) :
    |∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ 2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1) * Real.exp (Cw * (|p.1| + |p.2|))
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by
  set θ : ℝ := Cw * (|p.1| + |p.2|) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hexp1 : 0 ≤ Real.exp θ - 1 := by
    have := Real.one_le_exp hθ0; linarith
  have he2 : 1 ≤ 2 * Real.exp θ := by
    have := Real.one_le_exp hθ0; linarith
  have hs1 : 0 ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := Real.sqrt_nonneg _
  have hD : 0 ≤ (Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
      * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)) := mul_nonneg hexp1 (mul_nonneg hs1 hs2)
  -- the two-sided comparability of `Q` under the shift `p`
  have hle : ∀ y, Q (y - p) ≤ Real.exp θ * Q y := by
    intro y
    have h := hQsh y (-p)
    rw [sub_eq_add_neg]
    simpa [hθ] using h
  have hge : ∀ y, Q y ≤ Real.exp θ * Q (y - p) := by
    intro y
    have h := hQsh' y (-p)
    rw [sub_eq_add_neg]
    simpa [hθ] using h
  let A : ℝ × ℝ → ℝ := fun y => Real.sqrt (Q y) * G₂ y
  let B : ℝ × ℝ → ℝ := fun y => Real.sqrt (Q (y - p)) * G₁ (y - p)
  have hsub : Measurable (fun y : ℝ × ℝ => y - p) := measurable_id.sub measurable_const
  have hAm : Measurable A := hQm.sqrt.mul hG2m
  have hBm : Measurable B := (hQm.comp hsub).sqrt.mul (hG1m.comp hsub)
  -- pointwise bound on the weight difference
  have hpt : ∀ y : ℝ × ℝ,
      |Q y - Q (y - p)| ≤ (Real.exp θ - 1) * Real.sqrt (Q y * Q (y - p)) := by
    intro y
    have hX : 0 ≤ Q y := hQ0 y
    have hY : 0 ≤ Q (y - p) := hQ0 _
    have h1 : Q y ≤ Real.exp θ * Q (y - p) := hge y
    have h2 : Q (y - p) ≤ Real.exp θ * Q y := hle y
    have hmin : |Q y - Q (y - p)| ≤ (Real.exp θ - 1) * min (Q y) (Q (y - p)) := by
      rcases le_total (Q (y - p)) (Q y) with h | h
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]
        nlinarith [h1]
      · rw [min_eq_left h, abs_of_nonpos (by linarith), neg_sub]
        nlinarith [h2]
    have hmin2 : min (Q y) (Q (y - p)) ≤ Real.sqrt (Q y * Q (y - p)) := by
      rcases le_total (Q y) (Q (y - p)) with h | h
      · calc min (Q y) (Q (y - p)) = Q y := min_eq_left h
          _ = Real.sqrt (Q y * Q y) := (Real.sqrt_mul_self hX).symm
          _ ≤ Real.sqrt (Q y * Q (y - p)) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h hX)
      · calc min (Q y) (Q (y - p)) = Q (y - p) := min_eq_right h
          _ = Real.sqrt (Q (y - p) * Q (y - p)) := (Real.sqrt_mul_self hY).symm
          _ ≤ Real.sqrt (Q y * Q (y - p)) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h hY)
    calc |Q y - Q (y - p)| ≤ (Real.exp θ - 1) * min (Q y) (Q (y - p)) := hmin
      _ ≤ (Real.exp θ - 1) * Real.sqrt (Q y * Q (y - p)) := mul_le_mul_of_nonneg_left hmin2 hexp1
  -- pointwise bound on the full integrand
  have hfpt : ∀ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ (Real.exp θ - 1) * (|Real.sqrt (Q y) * G₂ y| * |Real.sqrt (Q (y - p)) * G₁ (y - p)|) := by
    intro y
    have h1 := hpt y
    have hs : Real.sqrt (Q y * Q (y - p)) = Real.sqrt (Q y) * Real.sqrt (Q (y - p)) :=
      Real.sqrt_mul (hQ0 y) (Q (y - p))
    have hg1 : 0 ≤ |G₁ (y - p)| := abs_nonneg _
    have hg2 : 0 ≤ |G₂ y| := abs_nonneg _
    have hstep : |Q y - Q (y - p)| * |G₁ (y - p)| * |G₂ y|
        ≤ (Real.exp θ - 1) * Real.sqrt (Q y * Q (y - p)) * |G₁ (y - p)| * |G₂ y| := by
      calc |Q y - Q (y - p)| * |G₁ (y - p)| * |G₂ y|
          = |Q y - Q (y - p)| * (|G₁ (y - p)| * |G₂ y|) := by ring
        _ ≤ ((Real.exp θ - 1) * Real.sqrt (Q y * Q (y - p))) * (|G₁ (y - p)| * |G₂ y|) :=
            mul_le_mul_of_nonneg_right h1 (mul_nonneg hg1 hg2)
        _ = (Real.exp θ - 1) * Real.sqrt (Q y * Q (y - p)) * |G₁ (y - p)| * |G₂ y| := by ring
    calc |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
        = |Q y - Q (y - p)| * |G₁ (y - p)| * |G₂ y| := by rw [abs_mul, abs_mul]
      _ ≤ (Real.exp θ - 1) * Real.sqrt (Q y * Q (y - p)) * |G₁ (y - p)| * |G₂ y| := hstep
      _ = (Real.exp θ - 1) *
            (|Real.sqrt (Q y) * G₂ y| * |Real.sqrt (Q (y - p)) * G₁ (y - p)|) := by
          rw [hs, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (Q y)),
            abs_of_nonneg (Real.sqrt_nonneg (Q (y - p)))]
          ring
  have hA2 : Integrable (fun y : ℝ × ℝ => A y ^ 2) := by
    refine hI2.congr ?_
    filter_upwards with y
    simp [A, mul_pow, Real.sq_sqrt (hQ0 y)]
  have hB2 : Integrable (fun y : ℝ × ℝ => B y ^ 2) := by
    refine (hI1.comp_sub_right p).congr ?_
    filter_upwards with y
    simp [B, mul_pow, Real.sq_sqrt (hQ0 (y - p))]
  have hABint : Integrable (fun y : ℝ × ℝ => |A y| * |B y|) := by
    refine Integrable.mono' ((hA2.add hB2).div_const 2)
      ((hAm.abs).mul (hBm.abs)).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (by positivity)]
    change |A y| * |B y| ≤ (A y ^ 2 + B y ^ 2) / 2
    have hsq : A y ^ 2 = |A y| ^ 2 := (sq_abs (A y)).symm
    have hsq2 : B y ^ 2 = |B y| ^ 2 := (sq_abs (B y)).symm
    rw [hsq, hsq2]
    nlinarith [sq_nonneg (|A y| - |B y|)]
  have hCS := abs_integral_mul_le_sqrt_mul_sqrt (volume : Measure (ℝ × ℝ)) hAm hBm hA2 hB2
  have eA : (∫ y : ℝ × ℝ, A y ^ 2) = ∫ y : ℝ × ℝ, Q y * G₂ y ^ 2 :=
    integral_congr_ae (by filter_upwards with y; simp [A, mul_pow, Real.sq_sqrt (hQ0 y)])
  have eB : (∫ y : ℝ × ℝ, B y ^ 2) = ∫ y : ℝ × ℝ, Q y * G₁ y ^ 2 := by
    have h1 : (∫ y : ℝ × ℝ, B y ^ 2) = ∫ y : ℝ × ℝ, Q (y - p) * G₁ (y - p) ^ 2 :=
      integral_congr_ae (by
        filter_upwards with y
        simp [B, mul_pow, Real.sq_sqrt (hQ0 (y - p))])
    rw [h1, integral_sub_right_eq_self (fun u : ℝ × ℝ => Q u * G₁ u ^ 2) p]
  have hmain : ∫ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ (Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)) := by
    calc ∫ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
        ≤ ∫ y : ℝ × ℝ, (Real.exp θ - 1) * (|A y| * |B y|) := by
          refine integral_mono_of_nonneg
            (f := fun y : ℝ × ℝ => |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|)
            (g := fun y : ℝ × ℝ => (Real.exp θ - 1) * (|A y| * |B y|)) ?_ ?_ ?_
          · exact Filter.Eventually.of_forall (fun y => abs_nonneg _)
          · exact hABint.const_mul (Real.exp θ - 1)
          · exact Filter.Eventually.of_forall (fun y => hfpt y)
      _ = (Real.exp θ - 1) * ∫ y : ℝ × ℝ, |A y| * |B y| := integral_const_mul _ _
      _ ≤ (Real.exp θ - 1) *
            (Real.sqrt (∫ y : ℝ × ℝ, A y ^ 2) * Real.sqrt (∫ y : ℝ × ℝ, B y ^ 2)) :=
          mul_le_mul_of_nonneg_left hCS hexp1
      _ = (Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)) := by
          rw [eA, eB]; ring
  have hfinal : (Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
        * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2))
      ≤ 2 * (Real.exp θ - 1) * Real.exp θ * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by
    calc (Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2))
        = 1 * ((Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2))) := by ring
      _ ≤ (2 * Real.exp θ) * ((Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2))) :=
            mul_le_mul_of_nonneg_right he2 hD
      _ = 2 * (Real.exp θ - 1) * Real.exp θ * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by ring
  calc |∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ ∫ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ (Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)) := hmain
    _ ≤ 2 * (Real.exp θ - 1) * Real.exp θ * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := hfinal
    _ = 2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1) * Real.exp (Cw * (|p.1| + |p.2|))
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by rw [hθ]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integrable_prod_of_lintegral_iterated =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

open MeasureTheory

/-- If the iterated (Tonelli) lintegral of `‖F z θ‖` over `z ∈ (0,∞)`, `θ ∈ (0,π/2)` is
finite and `F` is a.e. strongly measurable on the product region, then `F` is integrable
there.  The region integral `volume.restrict (Ioi 0 ×ˢ Ioo 0 (π/2))` is the product of the
two slice measures (`Measure.prod_restrict`), and the iterated integral equals the integral
over that product (`lintegral_lintegral`). -/
theorem integrable_prod_of_lintegral_iterated {F : ℝ → ℝ → ℝ}
    (hm : MeasureTheory.AEStronglyMeasurable (Function.uncurry F)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))))
    (hfin : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
        ENNReal.ofReal ‖F z θ‖) ≠ ⊤) :
    MeasureTheory.Integrable (Function.uncurry F)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) := by
  set s : Set ℝ := Set.Ioi 0
  set t : Set ℝ := Set.Ioo 0 (Real.pi / 2)
  -- the restricton of the product measure to the product set is the product of restrictions
  have hμeq : (volume : Measure (ℝ × ℝ)).restrict (s ×ˢ t)
      = (volume.restrict s).prod (volume.restrict t) := by
    show (volume.prod volume).restrict (s ×ˢ t)
      = (volume.restrict s).prod (volume.restrict t)
    rw [← Measure.prod_restrict s t]
  -- a.e. strong measurability of the `ENNReal`-valued integrand for Tonelli
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ‖F p.1 p.2‖)
      ((volume.restrict s).prod (volume.restrict t)) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
        ((volume.restrict s).prod (volume.restrict t)) := by
      rw [← hμeq]
      exact hm
    exact h1.norm.aemeasurable.ennreal_ofReal
  -- Tonelli: the product integral is the iterated integral
  have hprod : (∫⁻ p, ENNReal.ofReal ‖F p.1 p.2‖
        ∂((volume.restrict s).prod (volume.restrict t)))
      = (∫⁻ z, ∫⁻ θ, ENNReal.ofReal ‖F z θ‖
        ∂(volume.restrict t) ∂(volume.restrict s)) := by
    have := lintegral_lintegral (μ := volume.restrict s) (ν := volume.restrict t)
      (f := fun z θ => ENNReal.ofReal ‖F z θ‖) hmeas
    simpa only [Function.uncurry] using this.symm
  -- hence the product integral is finite
  have hne : (∫⁻ p, ENNReal.ofReal ‖F p.1 p.2‖
        ∂((volume.restrict s).prod (volume.restrict t))) ≠ ⊤ := by
    rw [hprod]
    exact hfin
  refine ⟨hm, ?_⟩
  rw [hasFiniteIntegral_iff_norm, lt_top_iff_ne_top, hμeq]
  simpa only [Function.uncurry] using hne

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.shift_diff_ftc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

theorem shift_diff_ftc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : E → ℝ}
    (hG : ContDiff ℝ 1 G) (y p : E) :
    G (y + p) - G (y - p) = ∫ t in (-1 : ℝ)..1, (fderiv ℝ G (y + t • p)) p := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => G (y + s • p)) ((fderiv ℝ G (y + t • p)) p) t := by
    intro t
    have hcurve : HasDerivAt (fun s : ℝ => y + s • p) p t := by
      simpa using ((hasDerivAt_id t).smul_const p).const_add y
    have hl : HasFDerivAt G (fderiv ℝ G (y + t • p)) (y + t • p) :=
      (hG.differentiable_one (y + t • p)).hasFDerivAt
    exact hl.comp_hasDerivAt (f := fun s : ℝ => y + s • p) (x := t) hcurve
  have hcont : Continuous fun t : ℝ => (fderiv ℝ G (y + t • p)) p := by
    have h := hG.continuous_fderiv_apply (𝕜 := ℝ) (n := 1) (by simp)
    have h2 : Continuous fun t : ℝ => (y + t • p, p) :=
      (continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const
    exact h.comp h2
  have hint : IntervalIntegrable (fun t : ℝ => (fderiv ℝ G (y + t • p)) p)
      MeasureTheory.volume (-1) 1 :=
    hcont.intervalIntegrable (-1) 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint]
  simp [sub_eq_add_neg]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.sq_intervalIntegral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

/-- *Cauchy–Schwarz for interval integrals.*
For `a ≤ b` and `f` interval-integrable together with `f ^ 2` on `[a,b]`,
`(∫_a^b f)² ≤ (b - a) · ∫_a^b f²`.

The proof does not use the Cauchy–Schwarz inequality itself: it is the classical
"discriminant" argument.  For every `c : ℝ`, the interval integral of the nonnegative
function `t ↦ (f t - c)²` is nonnegative, and expanding it gives the quadratic
`c² (b - a) - 2 c (∫f) + ∫f² ≥ 0`.  Evaluating at the minimiser `c = (∫f)/(b - a)`
(available because `b - a > 0` when `a < b`) yields the claim; the degenerate case
`a = b` is immediate since both sides vanish. -/
theorem sq_intervalIntegral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfi : IntervalIntegrable f volume a b)
    (hfsq : IntervalIntegrable (fun t => f t ^ 2) volume a b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, f t ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    simp [intervalIntegral.integral_same]
  · set A : ℝ := ∫ t in a..b, f t with hA
    set B : ℝ := ∫ t in a..b, f t ^ 2 with hB
    have hbd : (0 : ℝ) < b - a := sub_pos.mpr h
    -- the shifted square has nonnegative integral, for every shift
    have key : ∀ c : ℝ, 0 ≤ c ^ 2 * (b - a) - 2 * c * A + B := by
      intro c
      have h1 : (∫ t in a..b, (f t - c) ^ 2)
          = ∫ t in a..b, (f t ^ 2 - 2 * c * f t + c ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      have hE : (∫ t in a..b, (f t - c) ^ 2) = c ^ 2 * (b - a) - 2 * c * A + B := by
        rw [h1]
        rw [intervalIntegral.integral_add (hfsq.sub (hfi.const_mul (2 * c)))
          intervalIntegrable_const]
        rw [intervalIntegral.integral_sub hfsq (hfi.const_mul (2 * c))]
        rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        rw [← hA, ← hB]
        ring
      have hnn : 0 ≤ ∫ t in a..b, (f t - c) ^ 2 :=
        intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg (f u - c))
      rwa [hE] at hnn
    -- evaluate the quadratic at its vertex
    have hzA := key (A / (b - a))
    have hexp : (b - a) * ((A / (b - a)) ^ 2 * (b - a) - 2 * (A / (b - a)) * A + B)
        = B * (b - a) - A ^ 2 := by
      field_simp [ne_of_gt hbd]
      ring
    have hle : A ^ 2 ≤ B * (b - a) := by
      have hh : 0 ≤ B * (b - a) - A ^ 2 := by
        rw [← hexp]
        exact mul_nonneg hbd.le hzA
      linarith
    rw [mul_comm (b - a) B]
    exact hle

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.gronwall_absorb_proof =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/gronwall_absorb_proof` — Grönwall with an absorbed quadratic defect

A continuous `e : ℝ → ℝ` with
`e' ≤ Λ (1 + e) + ε C₁ (1 + e)²` on `(0,T)`, `e 0 ≤ E0` and the smallness condition
`ε C₁ · 2 (1 + E0) e^{2(Λ+1)T} ≤ Λ + 1` satisfies `1 + e τ ≤ (1 + E0) e^{2(Λ+1)T}` on `[0,T]`.

Write `u := 1 + e` and `M := (1+E0) e^{2(Λ+1)T}`, so that `u 0 ≤ 1 + E0 < M` and
`u' ≤ Λ u + ε C₁ u²`.  The proof is the standard barrier (first-crossing) argument, split into
three independent ingredients:

* `grAux_gronwall_le_exp` — one-sided linear Grönwall comparison (integrating factor):
  `u b ≤ u a e^{K (b-a)}` whenever `u' ≤ K u` on `(a,b)`.  No sign hypothesis on `u`.
* `grAux_no_cross_up` — a solution of `u' ≤ Λ u + ε C₁ u²` (`Λ, C₁, ε ≥ 0`) that is `≤ 0` at
  some time can never become positive later: on the region `u ≤ 0` the quadratic term works in
  the same direction, and the integrating factor traps the trajectory below `0`.
* the crossing analysis in `gronwall_absorb_proof`: if `u` exceeds `M` at some time, let `τ₀` be
  the first time at which the *initial segment* bound `u ≤ M` fails.  Then `u ≤ M` on `[0,τ₀]`
  with `u τ₀ = M`, so on `[0,τ₀]` the quadratic term is absorbed into the linear one using
  `ε C₁ M ≤ (Λ+1)/2 < Λ+1`; either `u` is positive on all of `[0,τ₀]` — then Grönwall from `0`
  gives `u τ₀ ≤ (1+E0) e^{(Λ+εC₁M)T} < M`, a contradiction — or `u` dips `≤ 0` at some point of
  `[0,τ₀]`, whence `u τ₀ ≤ 0` by `grAux_no_cross_up`, again a contradiction.
-/

noncomputable section

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

/-! ### Auxiliary real-analysis lemmas -/

/-- **One-sided Grönwall comparison.**  If `u` is continuous on `[a,b]` and satisfies the
one-sided differential inequality `u' ≤ K * u` at every interior point, then
`u b ≤ u a * exp (K * (b - a))`.  The point is that the integrating factor
`τ ↦ u τ * exp (-K (τ - a))` is antitone; no sign hypothesis on `u` is needed. -/
theorem grAux_gronwall_le_exp {u : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn u (Set.Icc a b))
    (hd : ∀ τ ∈ Set.Ioo a b, ∃ u' : ℝ, HasDerivAt u u' τ ∧ u' ≤ K * u τ) :
    u b ≤ u a * Real.exp (K * (b - a)) := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · set psi : ℝ → ℝ := fun τ => u τ * Real.exp (-K * (τ - a)) with hpsi
    have hcont_psi : ContinuousOn psi (Set.Icc a b) := by
      rw [hpsi]
      exact hcont.mul
        ((Real.continuous_exp.comp ((continuous_id.sub continuous_const).const_mul (-K))).continuousOn)
    have hderiv : ∀ x ∈ Set.Ioo a b,
        HasDerivAt psi ((deriv u x - K * u x) * Real.exp (-K * (x - a))) x := by
      intro x hx
      obtain ⟨u', hu', _⟩ := hd x hx
      have hu : HasDerivAt u (deriv u x) x := by rw [hu'.deriv]; exact hu'
      have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-K * (τ - a)))
          (Real.exp (-K * (x - a)) * (-K)) x := by
        have hlin : HasDerivAt (fun τ : ℝ => -K * (τ - a)) (-K * 1) x := by
          simpa using ((hasDerivAt_id x).sub_const a).const_mul (-K)
        simpa using hlin.exp
      have hmain := hu.mul hexp
      have hfun : psi = (fun τ : ℝ => u τ * Real.exp (-K * (τ - a))) := hpsi
      rw [hfun]
      convert hmain using 1
      ring
    have hnonpos : ∀ x ∈ interior (Set.Icc a b), deriv psi x ≤ 0 := by
      intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x hx).deriv]
      have h1 : deriv u x - K * u x ≤ 0 := by
        obtain ⟨u', hu', hle'⟩ := hd x hx
        rw [hu'.deriv]
        linarith
      exact mul_nonpos_of_nonpos_of_nonneg h1 (Real.exp_pos _).le
    have hdiff : DifferentiableOn ℝ psi (interior (Set.Icc a b)) := by
      intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    have hanti : AntitoneOn psi (Set.Icc a b) :=
      antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont_psi hdiff hnonpos
    have hba : psi b ≤ psi a :=
      hanti (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
    have hpsi_a : psi a = u a := by
      rw [hpsi]; simp
    have h1 : u b * Real.exp (-K * (b - a)) ≤ u a := by
      rw [← hpsi_a]; exact hba
    have h2 : Real.exp (-K * (b - a)) * Real.exp (K * (b - a)) = 1 := by
      rw [← Real.exp_add]
      have : -K * (b - a) + K * (b - a) = 0 := by ring
      rw [this, Real.exp_zero]
    have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (K * (b - a))).le
    rw [mul_assoc, h2, mul_one] at h3
    simpa using h3
  · subst heq; simp

/-- ε–δ form of continuity within the interval: at a point `τ` where `u` exceeds `c`, `u` stays
above `c` in a whole relative neighbourhood of `τ`. -/
theorem grAux_exists_pos_forall_gt {u : ℝ → ℝ} {T τ c : ℝ} (hcont : ContinuousOn u (Set.Icc 0 T))
    (hτ : τ ∈ Set.Icc 0 T) (hc : c < u τ) :
    ∃ δ > 0, ∀ z ∈ Set.Icc 0 T, |z - τ| < δ → c < u z := by
  have hcw : ContinuousWithinAt u (Set.Icc 0 T) τ := hcont.continuousWithinAt hτ
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp hcw (u τ - c) (by linarith)
  refine ⟨δ, hδpos, fun z hz hzd => ?_⟩
  have h1 := hδ hz (by rwa [Real.dist_eq])
  rw [Real.dist_eq] at h1
  have h2 : u τ - u z ≤ |u z - u τ| := by
    have h3 : u τ - u z = -(u z - u τ) := by ring
    rw [h3]
    exact neg_le_abs (u z - u τ)
  linarith

/-- ε–δ form of continuity within the interval, dual form. -/
theorem grAux_exists_lt_forall_lt {u : ℝ → ℝ} {T τ c : ℝ} (hcont : ContinuousOn u (Set.Icc 0 T))
    (hτ : τ ∈ Set.Icc 0 T) (hc : u τ < c) :
    ∃ δ > 0, ∀ z ∈ Set.Icc 0 T, |z - τ| < δ → u z < c := by
  have hcw : ContinuousWithinAt u (Set.Icc 0 T) τ := hcont.continuousWithinAt hτ
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp hcw (c - u τ) (by linarith)
  refine ⟨δ, hδpos, fun z hz hzd => ?_⟩
  have h1 := hδ hz (by rwa [Real.dist_eq])
  rw [Real.dist_eq] at h1
  have h2 : u z - u τ ≤ |u z - u τ| := le_abs_self _
  linarith

set_option linter.unusedVariables false in
/-- **A subsolution of `u' ≤ Λ u + ε C₁ u²` cannot cross up through `0`.**  If `u` is continuous
on `[0,T]`, satisfies the quadratic differential inequality on `(0,T)` with `Λ, C₁, ε ≥ 0`, and
`u x ≤ 0` at some `x ∈ [0,T]`, then `u` never exceeds `0` afterwards; in particular it cannot be
`> M` for `M > 0` at a later time. -/
theorem grAux_no_cross_up {u : ℝ → ℝ} {Λ C₁ ε M x y T : ℝ} (hΛ : 0 ≤ Λ) (hC₁ : 0 ≤ C₁)
    (hε : 0 ≤ ε) (hMpos : 0 < M) (hcont : ContinuousOn u (Set.Icc 0 T))
    (hd : ∀ τ ∈ Set.Ioo 0 T, ∃ u' : ℝ, HasDerivAt u u' τ ∧
      u' ≤ Λ * u τ + ε * C₁ * (u τ) ^ 2)
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hyT : y ≤ T) (hxle : u x ≤ 0) (hylt : M < u y) : False := by
  -- the set of times `≤ 0`, and its supremum
  have hxmem : x ∈ {q : ℝ | q ∈ Set.Icc x y ∧ u q ≤ 0} := ⟨Set.left_mem_Icc.mpr hxy, hxle⟩
  have hne : ({q : ℝ | q ∈ Set.Icc x y ∧ u q ≤ 0}).Nonempty := ⟨x, hxmem⟩
  have hbdd : BddAbove ({q : ℝ | q ∈ Set.Icc x y ∧ u q ≤ 0}) := ⟨y, fun q hq => hq.1.2⟩
  set ν : ℝ := sSup {q : ℝ | q ∈ Set.Icc x y ∧ u q ≤ 0} with hν
  have hxν : x ≤ ν := by rw [hν]; exact le_csSup hbdd hxmem
  have hνy : ν ≤ y := by rw [hν]; exact csSup_le hne (fun q hq => hq.1.2)
  have hνIcc : ν ∈ Set.Icc 0 T := ⟨le_trans hx0 hxν, le_trans hνy hyT⟩
  -- the supremum itself is a nonpositive point
  have hνle0 : u ν ≤ 0 := by
    by_contra hc
    have hc' : 0 < u ν := not_le.mp hc
    obtain ⟨δ, hδpos, hδ⟩ := grAux_exists_pos_forall_gt hcont hνIcc hc'
    have hlt : ν - δ < sSup {q : ℝ | q ∈ Set.Icc x y ∧ u q ≤ 0} := by rw [← hν]; linarith
    obtain ⟨q, hq, hqgt⟩ := (lt_csSup_iff hbdd hne).mp hlt
    have hqν : q ≤ ν := by rw [hν]; exact le_csSup hbdd hq
    have hqT : q ∈ Set.Icc 0 T := ⟨le_trans hx0 hq.1.1, le_trans hq.1.2 hyT⟩
    have habs : |q - ν| < δ := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have := hδ q hqT habs
    linarith [hq.2]
  -- `u` is positive on `(ν, y]`
  have hpos : ∀ z ∈ Set.Ioo ν y, 0 < u z := by
    intro z hz
    by_contra hc
    have hznonpos : u z ≤ 0 := not_lt.mp hc
    have hzmem : z ∈ {q : ℝ | q ∈ Set.Icc x y ∧ u q ≤ 0} :=
      ⟨⟨le_trans hxν hz.1.le, hz.2.le⟩, hznonpos⟩
    have hle : z ≤ ν := by rw [hν]; exact le_csSup hbdd hzmem
    linarith [hz.1]
  -- on `[ν,y]` the quadratic term is dominated by a constant, so Grönwall applies
  have hcont' : ContinuousOn u (Set.Icc ν y) :=
    hcont.mono (fun z hz => ⟨le_trans hνIcc.1 hz.1, le_trans hz.2 hyT⟩)
  obtain ⟨ζ, -, hζmax⟩ :=
    IsCompact.exists_isMaxOn isCompact_Icc
      (⟨ν, Set.left_mem_Icc.mpr hνy⟩ : (Set.Icc ν y).Nonempty) hcont'
  have hgr : u y ≤ u ν * Real.exp ((Λ + ε * C₁ * u ζ) * (y - ν)) := by
    refine grAux_gronwall_le_exp hνy hcont' ?_
    intro z hz
    have hzT : z ∈ Set.Ioo 0 T := ⟨lt_of_le_of_lt hνIcc.1 hz.1, lt_of_lt_of_le hz.2 hyT⟩
    obtain ⟨u', hu', hle⟩ := hd z hzT
    refine ⟨u', hu', ?_⟩
    have hzpos : 0 < u z := hpos z hz
    have hzle : u z ≤ u ζ := hζmax ⟨hz.1.le, hz.2.le⟩
    have huu : Λ + ε * C₁ * u z ≤ Λ + ε * C₁ * u ζ := by
      have := mul_le_mul_of_nonneg_left hzle (mul_nonneg hε hC₁)
      linarith
    calc u' ≤ Λ * u z + ε * C₁ * (u z) ^ 2 := hle
      _ = u z * (Λ + ε * C₁ * u z) := by ring
      _ ≤ u z * (Λ + ε * C₁ * u ζ) := mul_le_mul_of_nonneg_left huu hzpos.le
      _ = (Λ + ε * C₁ * u ζ) * u z := by ring
  have hy0 : u y ≤ 0 := by
    have h := mul_nonpos_of_nonpos_of_nonneg hνle0
      (Real.exp_pos ((Λ + ε * C₁ * u ζ) * (y - ν))).le
    linarith
  linarith

/-! ### The absorption estimate -/

theorem gronwall_absorb_proof {e : ℝ → ℝ} {T Λ C₁ ε E0 : ℝ} (hT : 0 < T) (hΛ : 0 ≤ Λ)
    (hC₁ : 0 ≤ C₁) (hε : 0 ≤ ε) (hE0 : 0 ≤ E0)
    (hcont : ContinuousOn e (Set.Icc 0 T))
    (hd : ∀ τ ∈ Set.Ioo 0 T, ∃ e' : ℝ, HasDerivAt e e' τ ∧
      e' ≤ Λ * (1 + e τ) + ε * C₁ * (1 + e τ) ^ 2)
    (he0 : e 0 ≤ E0)
    (hsmall : ε * C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T)) ≤ Λ + 1) :
    ∀ τ ∈ Set.Icc 0 T, 1 + e τ ≤ (1 + E0) * Real.exp (2 * (Λ + 1) * T) := by
  set u : ℝ → ℝ := fun τ => 1 + e τ with hu
  set M : ℝ := (1 + E0) * Real.exp (2 * (Λ + 1) * T) with hM
  have hu_cont : ContinuousOn u (Set.Icc 0 T) := by
    rw [hu]; exact continuousOn_const.add hcont
  have hd' : ∀ τ ∈ Set.Ioo 0 T, ∃ u' : ℝ, HasDerivAt u u' τ ∧
      u' ≤ Λ * u τ + ε * C₁ * (u τ) ^ 2 := by
    intro τ hτ
    obtain ⟨e', he', hle⟩ := hd τ hτ
    refine ⟨e', ?_, ?_⟩
    · rw [hu]; exact he'.const_add 1
    · rw [hu]; exact hle
  have h1E0pos : (0 : ℝ) < 1 + E0 := by linarith
  have hMpos : 0 < M := by
    rw [hM]; exact mul_pos h1E0pos (Real.exp_pos _)
  have hE0lt : 1 + E0 < M := by
    rw [hM]
    have hE : 1 < Real.exp (2 * (Λ + 1) * T) := by
      have hΛ1 : 0 < Λ + 1 := by linarith
      have hpos : (0 : ℝ) < 2 * (Λ + 1) * T := by positivity
      simpa using Real.exp_lt_exp.mpr hpos
    calc 1 + E0 = (1 + E0) * 1 := by ring
      _ < (1 + E0) * Real.exp (2 * (Λ + 1) * T) := mul_lt_mul_of_pos_left hE h1E0pos
  have hu0 : u 0 ≤ 1 + E0 := by rw [hu]; simpa using he0
  have hsmall' : ε * C₁ * M ≤ (Λ + 1) / 2 := by
    have h2 : 2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T) = 2 * M := by rw [hM]; ring
    rw [h2] at hsmall
    linarith
  have hKlt : Λ + ε * C₁ * M < 2 * (Λ + 1) := by linarith
  have hKnonneg : (0 : ℝ) ≤ Λ + ε * C₁ * M := by
    have : 0 ≤ ε * C₁ * M := mul_nonneg (mul_nonneg hε hC₁) hMpos.le
    linarith
  -- main claim
  have hmain : ∀ τ ∈ Set.Icc 0 T, u τ ≤ M := by
    intro τ hτ
    by_contra hcon
    have hgt : M < u τ := not_le.mp hcon
    -- first time the "initial segment bound" could fail
    have hBne : ({s : ℝ | s ∈ Set.Icc 0 T ∧ M < u s}).Nonempty := ⟨τ, hτ, hgt⟩
    have hBbdd : BddBelow ({s : ℝ | s ∈ Set.Icc 0 T ∧ M < u s}) := ⟨0, fun s hs => hs.1.1⟩
    set τ₀ : ℝ := sInf {s : ℝ | s ∈ Set.Icc 0 T ∧ M < u s} with hτ₀
    have hτ₀nonneg : 0 ≤ τ₀ := by
      rw [hτ₀]; exact le_csInf hBne (fun s hs => hs.1.1)
    have hτ₀leT : τ₀ ≤ T := by
      rw [hτ₀]
      obtain ⟨b, hb⟩ := hBne
      exact le_trans (csInf_le hBbdd hb) hb.1.2
    have hτ₀mem : τ₀ ∈ Set.Icc 0 T := ⟨hτ₀nonneg, hτ₀leT⟩
    have hP2 : ∀ s ∈ Set.Icc 0 τ₀, u s ≤ M := by
      intro s hs
      rcases lt_or_eq_of_le hs.2 with hlt | heq
      · -- `s < τ₀`: otherwise `τ₀` would not be a lower bound
        by_contra h
        have hMs : M < u s := not_le.mp h
        have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 hτ₀leT⟩
        have hle : τ₀ ≤ s := by rw [hτ₀]; exact csInf_le hBbdd ⟨hsT, hMs⟩
        linarith
      · -- `s = τ₀`: by continuity
        rw [heq]
        by_contra h
        have hMτ : M < u τ₀ := not_le.mp h
        rcases lt_or_eq_of_le hτ₀nonneg with hpos | hzero
        · obtain ⟨δ, hδpos, hδ⟩ := grAux_exists_pos_forall_gt hu_cont hτ₀mem hMτ
          have hmpos : 0 < min δ τ₀ := lt_min hδpos hpos
          have hzt : |(τ₀ - min δ τ₀ / 2) - τ₀| < δ := by
            have h1 : (τ₀ - min δ τ₀ / 2) - τ₀ = -(min δ τ₀ / 2) := by ring
            rw [h1, abs_neg, abs_of_pos (by linarith : 0 < min δ τ₀ / 2)]
            have h2 : min δ τ₀ ≤ δ := min_le_left δ τ₀
            linarith
          have hz0 : 0 ≤ τ₀ - min δ τ₀ / 2 := by
            have h2 : min δ τ₀ ≤ τ₀ := min_le_right δ τ₀
            linarith
          have hzT : τ₀ - min δ τ₀ / 2 ≤ T := by linarith
          have hzmem : τ₀ - min δ τ₀ / 2 ∈ {s : ℝ | s ∈ Set.Icc 0 T ∧ M < u s} :=
            ⟨⟨hz0, hzT⟩, hδ _ ⟨hz0, hzT⟩ hzt⟩
          have hle : τ₀ ≤ τ₀ - min δ τ₀ / 2 := by
            rw [hτ₀]; exact csInf_le hBbdd hzmem
          linarith
        · rw [← hzero] at hMτ
          linarith [hu0, hE0lt]
    -- take the crossing witness above `τ₀`
    obtain ⟨b, hb⟩ := hBne
    have hτ₀b : τ₀ ≤ b := by rw [hτ₀]; exact csInf_le hBbdd hb
    have hbT : b ≤ T := hb.1.2
    have hbM : M < u b := hb.2
    have hbgt : τ₀ < b := by
      rcases lt_or_eq_of_le hτ₀b with h | h
      · exact h
      · exfalso
        have hle := hP2 τ₀ ⟨hτ₀nonneg, le_rfl⟩
        rw [h] at hle
        linarith
    by_cases hcase : ∃ p ∈ Set.Icc 0 τ₀, u p ≤ 0
    · -- `u` was nonpositive somewhere before `τ₀`: it cannot come back up
      obtain ⟨p, hp, hp0⟩ := hcase
      exact grAux_no_cross_up hΛ hC₁ hε hMpos hu_cont hd' hp.1
        (le_trans hp.2 hbgt.le) hbT hp0 hbM
    · push Not at hcase
      -- first time at which `u` reaches `M`
      have hSne : ({p : ℝ | p ∈ Set.Icc 0 b ∧ M ≤ u p}).Nonempty :=
        ⟨b, ⟨⟨le_trans hτ₀nonneg hbgt.le, le_rfl⟩, hbM.le⟩⟩
      have hSbdd : BddBelow ({p : ℝ | p ∈ Set.Icc 0 b ∧ M ≤ u p}) := ⟨0, fun p hp => hp.1.1⟩
      set τ₁ : ℝ := sInf {p : ℝ | p ∈ Set.Icc 0 b ∧ M ≤ u p} with hτ₁
      have hτ₁nonneg : 0 ≤ τ₁ := by
        rw [hτ₁]; exact le_csInf hSne (fun p hp => hp.1.1)
      have hτ₁leb : τ₁ ≤ b := by
        rw [hτ₁]
        exact csInf_le hSbdd ⟨⟨le_trans hτ₀nonneg hbgt.le, le_rfl⟩, hbM.le⟩
      have hτ₁ge : M ≤ u τ₁ := by
        by_contra h
        have hlt : u τ₁ < M := not_le.mp h
        obtain ⟨δ, hδpos, hδ⟩ :=
          grAux_exists_lt_forall_lt hu_cont ⟨hτ₁nonneg, le_trans hτ₁leb hbT⟩ hlt
        have hlt2 : sInf {p : ℝ | p ∈ Set.Icc 0 b ∧ M ≤ u p} < τ₁ + δ := by
          rw [← hτ₁]; linarith
        obtain ⟨q, hq, hqlt⟩ := (csInf_lt_iff hSbdd hSne).mp hlt2
        have hqτ₁ : τ₁ ≤ q := by rw [hτ₁]; exact csInf_le hSbdd hq
        have hqT : q ∈ Set.Icc 0 T := ⟨hq.1.1, le_trans hq.1.2 hbT⟩
        have hqd : |q - τ₁| < δ := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        have hqq := hδ q hqT hqd
        linarith [hq.2]
      by_cases hcase2 : ∃ p ∈ Set.Icc 0 τ₁, u p ≤ 0
      · obtain ⟨p, hp, hp0⟩ := hcase2
        exact grAux_no_cross_up hΛ hC₁ hε hMpos hu_cont hd' hp.1
          (le_trans hp.2 hτ₁leb) hbT hp0 hbM
      · push Not at hcase2
        -- `u` is positive on `[0,τ₁]`, so the quadratic term is absorbed on `(0,τ₁)`
        have hgr : u τ₁ ≤ u 0 * Real.exp ((Λ + ε * C₁ * M) * (τ₁ - 0)) := by
          refine grAux_gronwall_le_exp hτ₁nonneg
            (hu_cont.mono (fun z hz => ⟨hz.1, le_trans hz.2 (le_trans hτ₁leb hbT)⟩)) ?_
          intro z hz
          obtain ⟨u', hu', hle⟩ :=
            hd' z ⟨hz.1, lt_of_lt_of_le hz.2 (le_trans hτ₁leb hbT)⟩
          refine ⟨u', hu', ?_⟩
          have hzpos : 0 < u z := hcase2 z ⟨hz.1.le, hz.2.le⟩
          have hzltM : u z < M := by
            by_contra h
            have hMz : M ≤ u z := not_lt.mp h
            have hzmem : z ∈ {p : ℝ | p ∈ Set.Icc 0 b ∧ M ≤ u p} :=
              ⟨⟨hz.1.le, le_trans hz.2.le hτ₁leb⟩, hMz⟩
            have hle2 : τ₁ ≤ z := by rw [hτ₁]; exact csInf_le hSbdd hzmem
            linarith [hz.2]
          calc u' ≤ Λ * u z + ε * C₁ * (u z) ^ 2 := hle
            _ = u z * (Λ + ε * C₁ * u z) := by ring
            _ ≤ u z * (Λ + ε * C₁ * M) := mul_le_mul_of_nonneg_left (by
                  have := mul_le_mul_of_nonneg_left hzltM.le (mul_nonneg hε hC₁)
                  linarith) hzpos.le
            _ = (Λ + ε * C₁ * M) * u z := by ring
        have h1 : u 0 * Real.exp ((Λ + ε * C₁ * M) * (τ₁ - 0)) ≤
            (1 + E0) * Real.exp ((Λ + ε * C₁ * M) * T) := by
          have hexp : Real.exp ((Λ + ε * C₁ * M) * (τ₁ - 0)) ≤
              Real.exp ((Λ + ε * C₁ * M) * T) := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_left (by linarith : τ₁ - 0 ≤ T) hKnonneg
          calc u 0 * Real.exp ((Λ + ε * C₁ * M) * (τ₁ - 0))
              ≤ (1 + E0) * Real.exp ((Λ + ε * C₁ * M) * (τ₁ - 0)) :=
                mul_le_mul_of_nonneg_right hu0 (Real.exp_pos _).le
            _ ≤ (1 + E0) * Real.exp ((Λ + ε * C₁ * M) * T) :=
                mul_le_mul_of_nonneg_left hexp h1E0pos.le
        have h2 : (1 + E0) * Real.exp ((Λ + ε * C₁ * M) * T) <
            (1 + E0) * Real.exp (2 * (Λ + 1) * T) := by
          apply mul_lt_mul_of_pos_left _ h1E0pos
          apply Real.exp_lt_exp.mpr
          have hh := mul_lt_mul_of_pos_right hKlt hT
          linarith
        have h3 : (1 + E0) * Real.exp (2 * (Λ + 1) * T) = M := by rw [hM]
        linarith [hτ₁ge, hgr, h1, h2]
  intro τ hτ
  have h := hmain τ hτ
  rw [hu] at h
  rw [hM] at h
  exact h

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.sInf_crossing =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

/-- If `f` is continuous on `[0,T]`, `f 0 < M` and `f τ > M` for some `τ ∈ [0,T]`, then the first
crossing time `sInf {τ ∈ [0,T] | M < f τ}` is strictly positive and at most `T`, the value of `f`
there is exactly `M`, and `f ≤ M` on `[0, sInf …]`. -/
theorem sInf_crossing {f : ℝ → ℝ} {M T : ℝ} (hT : 0 < T) (hf : ContinuousOn f (Set.Icc 0 T))
    (h0 : f 0 < M) (hU : ∃ τ ∈ Set.Icc 0 T, M < f τ) :
    0 < sInf {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ} ∧
      sInf {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ} ≤ T ∧
      f (sInf {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ}) = M ∧
      ∀ τ ∈ Set.Icc 0 (sInf {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ}), f τ ≤ M := by
  set S : Set ℝ := {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ} with hSdef
  have hmemS : ∀ τ, τ ∈ S ↔ τ ∈ Set.Icc 0 T ∧ M < f τ := by
    intro τ; rw [hSdef]; exact Iff.rfl
  have hne : S.Nonempty := by
    obtain ⟨τ, hτ⟩ := hU
    exact ⟨τ, (hmemS τ).mpr hτ⟩
  have hbdd : BddBelow S := ⟨0, fun x hx => ((hmemS x).mp hx).1.1⟩
  have hge0 : 0 ≤ sInf S := le_csInf hne (fun x hx => ((hmemS x).mp hx).1.1)
  have hleT : sInf S ≤ T := by
    obtain ⟨τ, hτ⟩ := hU
    have hτS : τ ∈ S := (hmemS τ).mpr hτ
    exact (csInf_le hbdd hτS).trans hτ.1.2
  have hmem_inf : sInf S ∈ Set.Icc 0 T := ⟨hge0, hleT⟩
  -- The crossing time is strictly positive: continuity at `0` forces `f < M` nearby.
  have hpos : 0 < sInf S := by
    rcases lt_or_eq_of_le hge0 with h | h
    · exact h
    · exfalso
      have hzero : sInf S = 0 := h.symm
      have hcont0 : ContinuousWithinAt f (Set.Icc 0 T) 0 := hf 0 ⟨le_refl 0, hT.le⟩
      obtain ⟨δ, hδpos, hδ⟩ :=
        (Metric.continuousWithinAt_iff.mp hcont0) (M - f 0) (by linarith)
      obtain ⟨s, hsS, hslt⟩ :=
        exists_lt_of_csInf_lt hne (show sInf S < δ by rw [hzero]; exact hδpos)
      have hs0 : 0 ≤ s := ((hmemS s).mp hsS).1.1
      have hsIcc : s ∈ Set.Icc 0 T := ((hmemS s).mp hsS).1
      have hsM : M < f s := ((hmemS s).mp hsS).2
      have hdist : dist s 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hs0]
        exact hslt
      have hb := hδ hsIcc hdist
      rw [Real.dist_eq, abs_lt] at hb
      linarith [hb.2, hsM]
  -- `f` at the crossing time is `≥ M`: otherwise a whole neighbourhood lies below `M`,
  -- contradicting the approximating points from `S`.
  have hf_ge : M ≤ f (sInf S) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.continuousWithinAt_iff.mp (hf (sInf S) hmem_inf)) (M - f (sInf S)) (by linarith)
    obtain ⟨s, hsS, hslt⟩ := exists_lt_of_csInf_lt hne (by linarith : sInf S < sInf S + δ)
    have hsIcc : s ∈ Set.Icc 0 T := ((hmemS s).mp hsS).1
    have hsM : M < f s := ((hmemS s).mp hsS).2
    have hdist : dist s (sInf S) < δ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [csInf_le hbdd hsS], by linarith⟩
    have hb := hδ hsIcc hdist
    rw [Real.dist_eq, abs_lt] at hb
    linarith [hb.2, hsM]
  -- `f` at the crossing time is `≤ M`: every point below it has `f ≤ M` (by minimality of the
  -- infimum), so continuity from the left gives the bound.
  have hf_le : f (sInf S) ≤ M := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.continuousWithinAt_iff.mp (hf (sInf S) hmem_inf)) (f (sInf S) - M) (by linarith)
    set τ : ℝ := max 0 (sInf S - δ / 3) with hτdef
    have hτ0 : 0 ≤ τ := by rw [hτdef]; exact le_max_left 0 (sInf S - δ / 3)
    have hτlt : τ < sInf S := by
      rw [hτdef]
      rcases le_or_gt 0 (sInf S - δ / 3) with hcase | hcase
      · rw [max_eq_right hcase]; linarith
      · rw [max_eq_left hcase.le]; exact hpos
    have hτT : τ ≤ T := hτlt.le.trans hleT
    have hτIcc : τ ∈ Set.Icc 0 T := ⟨hτ0, hτT⟩
    have hτdist : dist τ (sInf S) < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · rcases le_or_gt 0 (sInf S - δ / 3) with hcase | hcase
        · have hτeq : τ = sInf S - δ / 3 := by rw [hτdef]; exact max_eq_right hcase
          rw [hτeq]; linarith
        · have hτeq : τ = 0 := by rw [hτdef]; exact max_eq_left hcase.le
          rw [hτeq]; linarith
      · linarith [hτlt, hδpos]
    have hb := hδ hτIcc hτdist
    rw [Real.dist_eq, abs_lt] at hb
    have hτnot : τ ∉ S := notMem_of_lt_csInf hτlt hbdd
    have hfτ : f τ ≤ M := by
      by_contra hc
      push_neg at hc
      exact hτnot ((hmemS τ).mpr ⟨hτIcc, hc⟩)
    linarith [hb.1, hfτ]
  have hfM : f (sInf S) = M := le_antisymm hf_le hf_ge
  refine ⟨hpos, hleT, hfM, ?_⟩
  intro τ hτ
  rcases lt_or_eq_of_le hτ.2 with h | h
  · have hτT : τ ≤ T := h.le.trans hleT
    by_contra hc
    push_neg at hc
    exact notMem_of_lt_csInf h hbdd ((hmemS τ).mpr ⟨⟨hτ.1, hτT⟩, hc⟩)
  · rw [h]; exact hfM.le

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux.tvAverageLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux

/-- Pointwise total-variation bound: if `U` has derivative `U'` at every point of `[a,b]` and `U'`
is interval integrable on `[a,b]`, then for every `x ∈ [a,b]` the difference `U θ - U x` is
dominated, in absolute value, by the total variation `∫ y in a..b, |U' y|`.

This is the fundamental-theorem-of-calculus step behind `tvAverageLe`: restrict the FTC to the
subinterval between `x` and `θ` and use monotonicity of the integral of the nonnegative function
`|U'|`. -/
lemma abs_sub_le_intervalIntegral_abs_deriv {a b θ : ℝ} (haθ : a ≤ θ)
    (hθb : θ ≤ b) {U U' : ℝ → ℝ} (hU : ∀ x ∈ Set.Icc a b, HasDerivAt U (U' x) x)
    (hInt : IntervalIntegrable U' MeasureTheory.volume a b) :
    ∀ x ∈ Set.Icc a b, |U θ - U x| ≤ ∫ y in a..b, |U' y| := by
  intro x hx
  rcases le_total x θ with hxθ | hθx
  · have hsubI : Set.uIcc x θ ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le hxθ]
      exact Set.Icc_subset_Icc hx.1 hθb
    have hsub : Set.uIcc x θ ⊆ Set.uIcc a b := hsubI.trans Set.Icc_subset_uIcc
    have hFTC : ∫ y in x..θ, U' y = U θ - U x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y hy => hU y (hsubI hy)) (hInt.mono_set hsub)
    calc |U θ - U x| = |∫ y in x..θ, U' y| := by rw [hFTC]
      _ ≤ ∫ y in x..θ, |U' y| := intervalIntegral.abs_integral_le_integral_abs hxθ
      _ ≤ ∫ y in a..b, |U' y| :=
          intervalIntegral.integral_mono_interval hx.1 hxθ hθb
            (ae_of_all _ (fun y => abs_nonneg (U' y))) hInt.abs
  · have hsubI : Set.uIcc θ x ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le hθx]
      exact Set.Icc_subset_Icc haθ hx.2
    have hsub : Set.uIcc θ x ⊆ Set.uIcc a b := hsubI.trans Set.Icc_subset_uIcc
    have hFTC : ∫ y in θ..x, U' y = U x - U θ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y hy => hU y (hsubI hy)) (hInt.mono_set hsub)
    calc |U θ - U x| = |∫ y in θ..x, U' y| := by rw [hFTC, abs_sub_comm]
      _ ≤ ∫ y in θ..x, |U' y| := intervalIntegral.abs_integral_le_integral_abs hθx
      _ ≤ ∫ y in a..b, |U' y| :=
          intervalIntegral.integral_mono_interval haθ hθx hx.2
            (ae_of_all _ (fun y => abs_nonneg (U' y))) hInt.abs

/-- The value of a function at a point is bounded by its mean value over `[a,b]` plus its total
variation on `[a,b]`: if `U` has derivative `U'` at each point of `[a,b]` with `U'` interval
integrable, and `U` is interval integrable, then for `θ ∈ [a,b]`
`U θ ≤ (1/(b-a)) ∫_a^b U + ∫_a^b |U'|`.

Proof: by `abs_sub_le_intervalIntegral_abs_deriv`, `U θ - U x ≤ ∫_a^b |U'|` for every `x ∈ [a,b]`;
integrating this inequality over `[a,b]` gives `(b-a) U θ - ∫_a^b U ≤ (b-a) ∫_a^b |U'|`, and
division by `b - a > 0` yields the claim. -/
theorem tvAverageLe {a b θ : ℝ} (hab : a < b) (haθ : a ≤ θ) (hθb : θ ≤ b)
    {U U' : ℝ → ℝ} (hU : ∀ x ∈ Set.Icc a b, HasDerivAt U (U' x) x)
    (hInt : IntervalIntegrable U' MeasureTheory.volume a b)
    (hIntU : IntervalIntegrable U MeasureTheory.volume a b) :
    U θ ≤ (1 / (b - a)) * (∫ x in a..b, U x) + ∫ x in a..b, |U' x| := by
  have hab_le : a ≤ b := hab.le
  have hbda : (0 : ℝ) < b - a := sub_pos.mpr hab
  -- pointwise bound
  have hpt : ∀ x ∈ Set.Icc a b, U θ - U x ≤ ∫ y in a..b, |U' y| := fun x hx =>
    (le_abs_self (U θ - U x)).trans
      (abs_sub_le_intervalIntegral_abs_deriv haθ hθb hU hInt x hx)
  -- integrate the pointwise bound
  have hnonneg : 0 ≤ ∫ x in a..b, (U x + ((∫ y in a..b, |U' y|) - U θ)) :=
    intervalIntegral.integral_nonneg hab_le (fun u hu => by linarith [hpt u hu])
  have hval : ∫ x in a..b, (U x + ((∫ y in a..b, |U' y|) - U θ))
      = (∫ x in a..b, U x) + (b - a) * ((∫ y in a..b, |U' y|) - U θ) := by
    rw [intervalIntegral.integral_add hIntU intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  have hmain : (b - a) * U θ ≤ (∫ x in a..b, U x) + (b - a) * (∫ x in a..b, |U' x|) := by
    have h2 : 0 ≤ (∫ x in a..b, U x) + (b - a) * ((∫ x in a..b, |U' x|) - U θ) := by
      rw [← hval]; exact hnonneg
    nlinarith [h2]
  -- divide by the positive number `b - a`
  have hc : (0 : ℝ) ≤ 1 / (b - a) := by positivity
  have h1 : (1 / (b - a)) * ((b - a) * U θ) = U θ := by
    rw [← mul_assoc, one_div_mul_cancel (ne_of_gt hbda), one_mul]
  have h2 : (1 / (b - a)) * ((∫ x in a..b, U x) + (b - a) * (∫ x in a..b, |U' x|))
      = (1 / (b - a)) * (∫ x in a..b, U x) + ∫ x in a..b, |U' x| := by
    rw [mul_add, ← mul_assoc, one_div_mul_cancel (ne_of_gt hbda), one_mul]
  calc U θ = (1 / (b - a)) * ((b - a) * U θ) := h1.symm
    _ ≤ (1 / (b - a)) * ((∫ x in a..b, U x) + (b - a) * (∫ x in a..b, |U' x|)) :=
        mul_le_mul_of_nonneg_left hmain hc
    _ = (1 / (b - a)) * (∫ x in a..b, U x) + ∫ x in a..b, |U' x| := h2

end Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.abs_sub_sub_mul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false


end Work.FTS.StrongEps.E5Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux3.LimDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter Asymptotics

namespace Work.FTS.StrongEps.E5Aux3

set_option autoImplicit false
set_option maxHeartbeats 800000



end Work.FTS.StrongEps.E5Aux3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.continuousOn_of_pointwise_of_equiholder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

lemma continuousOn_of_pointwise_of_equiholder {f : ℕ → ℝ × ℝ → ℝ} {Φ : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hpt : ∀ q ∈ U, Filter.Tendsto (fun n => f n q) Filter.atTop (nhds (Φ q))) (hequi : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ U → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K, dist (f n p) (f n q) ≤ C * dist p q ^ (1 / 2 : ℝ)) : ContinuousOn Φ U := by
  -- It suffices to prove that `Φ` is continuous at every point of `U`; for such a point we
  -- apply the equi-Hölder bound on a closed ball around it, which is compact and contained in `U`.
  have hcont : ∀ x ∈ U, ContinuousAt Φ x := by
    intro x hx
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    have hKU : Metric.closedBall x (r/2) ⊆ U :=
      fun y hy => hrU (Metric.closedBall_subset_ball (by linarith) hy)
    obtain ⟨C, hC0, hC⟩ := hequi _ (isCompact_closedBall x (r/2)) hKU
    have hxK : x ∈ Metric.closedBall x (r/2) := by
      rw [Metric.mem_closedBall, dist_self]; linarith
    -- the Hölder bound passes to the limit `n → ∞` on the compact ball
    have hbound : ∀ y ∈ Metric.closedBall x (r/2),
        dist (Φ y) (Φ x) ≤ C * dist y x ^ (1/2 : ℝ) := by
      intro y hy
      exact le_of_tendsto ((hpt y (hKU hy)).dist (hpt x hx))
        (Filter.Eventually.of_forall (fun n => hC n y hy x hxK))
    rw [Metric.continuousAt_iff]
    intro ε hε
    -- a `≤ η` version of continuity, upgraded to `< ε` by taking `η = ε/2`
    have key : ∀ η > 0, ∃ δ > 0, ∀ y, dist y x < δ → dist (Φ y) (Φ x) ≤ η := by
      intro η hη
      have hC1 : (0:ℝ) < C + 1 := by linarith
      have hpos : 0 < η / (C + 1) := div_pos hη hC1
      refine ⟨min (r/2) ((η/(C+1))^2), lt_min (by linarith) (pow_pos hpos 2), ?_⟩
      intro y hy
      have hyK : y ∈ Metric.closedBall x (r/2) := by
        rw [Metric.mem_closedBall]
        exact le_of_lt (lt_of_lt_of_le hy (min_le_left _ _))
      have h1 := hbound y hyK
      have ht : dist y x < (η/(C+1))^2 := lt_of_lt_of_le hy (min_le_right _ _)
      have hs : Real.sqrt (dist y x) < η/(C+1) := (Real.sqrt_lt' hpos).mpr ht
      rw [show dist y x ^ (1/2:ℝ) = Real.sqrt (dist y x) from (Real.sqrt_eq_rpow _).symm] at h1
      calc dist (Φ y) (Φ x) ≤ C * Real.sqrt (dist y x) := h1
        _ ≤ C * (η/(C+1)) := mul_le_mul_of_nonneg_left hs.le hC0
        _ ≤ η := by
            rw [mul_div_assoc', div_le_iff₀ hC1]
            nlinarith [hη.le, hC0]
    obtain ⟨δ, hδ, hδb⟩ := key (ε/2) (by linarith)
    exact ⟨δ, hδ, fun y hy => lt_of_le_of_lt (hδb y hy) (by linarith)⟩
  exact fun x hx => (hcont x hx).continuousWithinAt

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.dist_setIntegral_mul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.StrongEps.E5G

open MeasureTheory

/-- Weighted-average Hölder estimate: if `ψ ≥ 0` is a probability density supported on `K`
(so that `∫_K ψ = 1`), `ψ` vanishes off a `δ`-neighbourhood of `q`, and `f` is `1/2`-Hölder
(with constant `C`) at `q` on `K`, then the `ψ`-average of `f` is within `C δ^{1/2}` of `f q`.

This is the "mollifier peak" step: `∫ f ψ - f q = ∫ (f - f q) ψ`, and `|f p - f q| ≤ C δ^{1/2}`
on the support of `ψ`. -/
lemma dist_setIntegral_mul_le {K : Set (ℝ × ℝ)} (hK : IsCompact K) {f ψ : ℝ × ℝ → ℝ} {q : ℝ × ℝ} {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hf : ContinuousOn f K) (hψ : ContinuousOn ψ K) (hψnn : ∀ p, 0 ≤ ψ p) (hψK : ∀ p, ψ p ≠ 0 → p ∈ K) (hψint : (∫ p in K, ψ p) = 1) (hb : ∀ p ∈ K, dist (f p) (f q) ≤ C * dist p q ^ (1 / 2 : ℝ)) (hδb : ∀ p, ψ p ≠ 0 → dist p q ≤ δ) : dist (∫ p in K, f p * ψ p) (f q) ≤ C * δ ^ (1 / 2 : ℝ) := by
  -- integrability on the compact set `K`
  have hintψ : IntegrableOn ψ K := hψ.integrableOn_compact hK
  have hintfψ : IntegrableOn (fun p => f p * ψ p) K := (hf.mul hψ).integrableOn_compact hK
  have hintcψ : IntegrableOn (fun p => f q * ψ p) K :=
    (continuousOn_const.mul hψ).integrableOn_compact hK
  have hintg : IntegrableOn (fun p => (C * δ ^ (1 / 2 : ℝ)) * ψ p) K :=
    (continuousOn_const.mul hψ).integrableOn_compact hK
  -- pointwise bound of the difference integrand
  have hpt : ∀ p, ‖f p * ψ p - f q * ψ p‖ ≤ (C * δ ^ (1 / 2 : ℝ)) * ψ p := by
    intro p
    rcases eq_or_ne (ψ p) 0 with h0 | hne
    · rw [h0]; simp
    · have hpK : p ∈ K := hψK p hne
      have hd : dist p q ≤ δ := hδb p hne
      have hsq : dist p q ^ (1 / 2 : ℝ) ≤ δ ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow dist_nonneg hd (by norm_num)
      have hle : dist (f p) (f q) ≤ C * δ ^ (1 / 2 : ℝ) :=
        le_trans (hb p hpK) (mul_le_mul_of_nonneg_left hsq hC)
      calc ‖f p * ψ p - f q * ψ p‖
          = ‖(f p - f q) * ψ p‖ := by
            rw [show f p * ψ p - f q * ψ p = (f p - f q) * ψ p from by ring]
        _ = dist (f p) (f q) * ψ p := by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hψnn p),
              ← Real.dist_eq]
        _ ≤ (C * δ ^ (1 / 2 : ℝ)) * ψ p := mul_le_mul_of_nonneg_right hle (hψnn p)
  -- replace the centre `f q` by its weighted average `∫ f q ψ = f q`
  have hmain : dist (∫ p in K, f p * ψ p) (f q) ≤ ∫ p in K, (C * δ ^ (1 / 2 : ℝ)) * ψ p := by
    rw [dist_eq_norm]
    have h1 : (∫ p in K, f p * ψ p) - f q = ∫ p in K, (f p * ψ p - f q * ψ p) := by
      rw [MeasureTheory.integral_sub hintfψ hintcψ, MeasureTheory.integral_const_mul,
        hψint, mul_one]
    rw [h1]
    calc ‖∫ p in K, (f p * ψ p - f q * ψ p)‖
        ≤ ∫ p in K, ‖f p * ψ p - f q * ψ p‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ p in K, (C * δ ^ (1 / 2 : ℝ)) * ψ p :=
          integral_mono_ae ((hintfψ.sub hintcψ).norm) hintg (Filter.Eventually.of_forall hpt)
  calc dist (∫ p in K, f p * ψ p) (f q)
      ≤ ∫ p in K, (C * δ ^ (1 / 2 : ℝ)) * ψ p := hmain
    _ = C * δ ^ (1 / 2 : ℝ) := by
        rw [MeasureTheory.integral_const_mul, hψint, mul_one]

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.equicont_of_holder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

lemma equicont_of_holder {K : Set (ℝ × ℝ)} {F : ℕ → ℝ × ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K, |F n p - F n q| ≤ C * dist p q ^ (1 / 2 : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
      dist p q < δ → |F n p - F n q| < ε := by
  intro ε hε
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  refine ⟨(ε / (C + 1)) ^ 2, by positivity, ?_⟩
  intro n p hp q hq hpq
  -- the half-power of the distance is bounded by ε/(C+1)
  have ha : (0 : ℝ) < ε / (C + 1) := by positivity
  have hsqrt : Real.sqrt (dist p q) < ε / (C + 1) := by
    have h1 := Real.sqrt_lt_sqrt (dist_nonneg) hpq
    rwa [Real.sqrt_sq (le_of_lt ha)] at h1
  have h2 := h n p hp q hq
  rw [← Real.sqrt_eq_rpow] at h2
  have h3 : C * (ε / (C + 1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ hC1]
    nlinarith [hε]
  have h4 : C * Real.sqrt (dist p q) ≤ C * (ε / (C + 1)) :=
    mul_le_mul_of_nonneg_left (le_of_lt hsqrt) hC
  linarith

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.exists_normed_bump_test =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A normalised smooth bump in `ℝ × ℝ` supported in a prescribed ball

Mathlib's `ContDiffBump` machinery provides a `C^∞` function `b` with

* `0 ≤ b x ≤ 1`,
* `b = 1` on `Metric.closedBall c b.rIn`,
* `support b = Metric.ball c b.rOut`,

and its normalisation `b.normed volume` has integral `1` and the same support.  Choosing the
centre `c = q` and the radii `rIn = δ/4`, `rOut = δ/2` produces the required bump: its support is
`Metric.ball q (δ/2)`, which is contained both in `Metric.ball q δ` and in
`Metric.ball q (ρ/2) ⊆ Metric.ball q ρ` because `δ ≤ ρ/2`.  Consequently the integral over
`Metric.closedBall q (ρ/2)` agrees with the total integral `1`.
-/

namespace Work.FTS.StrongEps.E5G

open MeasureTheory Metric

lemma exists_normed_bump_test (q : ℝ × ℝ) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hδρ : δ ≤ ρ / 2) :
    ∃ ψ : ℝ × ℝ → ℝ,
      (∀ n : ℕ, ContDiff ℝ n ψ) ∧ HasCompactSupport ψ ∧ (∀ p, 0 ≤ ψ p) ∧ (∫ p, ψ p) = 1 ∧
        (∀ p, ψ p ≠ 0 → dist p q < δ) ∧ (∀ p, δ ≤ dist p q → ψ p = 0) ∧
        (∫ p in Metric.closedBall q (ρ / 2), ψ p) = 1 ∧ (∀ p, ψ p ≠ 0 → p ∈ Metric.ball q ρ) := by
  -- The support radius `δ/2` stays below `ρ`.
  have hδ2ρ : δ / 2 < ρ := by
    have h1 : δ / 2 ≤ ρ / 4 := by linarith [hδρ]
    have h2 : ρ / 4 < ρ := div_lt_self hρ (by norm_num)
    linarith
  -- The bump with centre `q` and radii `δ/4 < δ/2`; its support is `ball q (δ/2)`.
  set b : ContDiffBump q := ⟨δ / 4, δ / 2, by linarith, by linarith⟩ with hb
  have hb_rOut : b.rOut = δ / 2 := rfl
  -- Everything is supported in `ball q (δ/2)`.
  have hsupp : ∀ p, b.normed volume p ≠ 0 → dist p q < δ / 2 := by
    intro p hp
    have h1 : p ∈ Function.support (b.normed volume) := Function.mem_support.mpr hp
    rw [b.support_normed_eq, mem_ball] at h1
    simpa [hb_rOut] using h1
  refine ⟨b.normed volume, fun n => b.contDiff_normed, b.hasCompactSupport_normed,
    fun p => b.nonneg_normed p, b.integral_normed, ?_, ?_, ?_, ?_⟩
  · -- support inside `ball q δ`
    intro p hp
    have h1 := hsupp p hp
    linarith
  · -- vanishing outside `ball q δ`
    intro p hp
    by_contra h
    have h1 := hsupp p h
    linarith
  · -- the integral over `closedBall q (ρ/2)` is the total integral, namely `1`
    have hset : ∫ p in Metric.closedBall q (ρ / 2), b.normed volume p
        = ∫ p, b.normed volume p := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => ?_)
      by_contra hne
      have h1 := hsupp p hne
      have h2 : ¬ dist p q ≤ ρ / 2 := by
        simpa [Metric.mem_closedBall] using hp
      linarith
    rw [hset, b.integral_normed]
  · -- support inside `ball q ρ`
    intro p hp
    have h1 := hsupp p hp
    rw [Metric.mem_ball]
    linarith [h1, hδ2ρ]

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.tendstoUniformlyOn_of_pointwise_of_holder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

lemma tendstoUniformlyOn_of_pointwise_of_holder {K : Set (ℝ × ℝ)} {F : ℕ → ℝ × ℝ → ℝ}
    {f : ℝ × ℝ → ℝ}
    (hK : IsCompact K)
    (hpt : ∀ p ∈ K, Filter.Tendsto (fun n : ℕ => F n p) Filter.atTop (nhds (f p)))
    (heqc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
      dist p q < δ → |F n p - F n q| < ε) :
    TendstoUniformlyOn F f Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := heqc (ε / 3) (by linarith)
  obtain ⟨t, htK, htfin, hcov⟩ := hK.finite_cover_balls hδpos
  have hev : ∀ᶠ n in Filter.atTop, ∀ y ∈ t, |F n y - f y| < ε / 3 := by
    rw [htfin.eventually_all]
    intro y hy
    have h1 : ∀ᶠ n in Filter.atTop, dist (F n y) (f y) < ε / 3 :=
      Metric.tendsto_nhds.mp (hpt y (htK hy)) (ε / 3) (by linarith)
    filter_upwards [h1] with n hn
    simpa [Real.dist_eq] using hn
  filter_upwards [hev] with n hn
  intro x hx
  rcases Set.mem_iUnion₂.mp (hcov hx) with ⟨y, hyt, hxy⟩
  have hyK : y ∈ K := htK hyt
  have hdxy : dist x y < δ := Metric.mem_ball.mp hxy
  have hlim : Filter.Tendsto (fun n => dist (F n y) (F n x)) Filter.atTop
      (nhds (dist (f y) (f x))) := (hpt y hyK).dist (hpt x hx)
  have hle : dist (f y) (f x) ≤ ε / 3 := by
    refine le_of_tendsto hlim ?_
    filter_upwards with m
    rw [Real.dist_eq, abs_sub_comm]
    exact le_of_lt (hδ m x hx y hyK hdxy)
  calc dist (f x) (F n x)
      ≤ dist (f x) (f y) + dist (f y) (F n y) + dist (F n y) (F n x) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h1 : dist (f x) (f y) ≤ ε / 3 := by
          rw [dist_comm]; exact hle
        have h2 : dist (f y) (F n y) < ε / 3 := by
          rw [Real.dist_eq, abs_sub_comm]; exact hn y hyt
        have h3 : dist (F n y) (F n x) < ε / 3 := by
          rw [Real.dist_eq, abs_sub_comm]; exact hδ n x hx y hyK hdxy
        linarith
    _ = ε := by ring

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.ExistsTestfunSecondDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ContDiff
open MeasureTheory

namespace Work.FTS.StrongEps.EComparison

/-- The interval integral of a function vanishing on `[[c, d]]` is zero. -/
private lemma intervalIntegral_eq_zero_of_forall_mem_uIcc {f : ℝ → ℝ} {c d : ℝ}
    (h : ∀ x ∈ Set.uIcc c d, f x = 0) : (∫ x in c..d, f x) = 0 := by
  rw [intervalIntegral.integral_congr h]
  exact intervalIntegral.integral_zero

/-- `[[c, d]] ⊆ (-∞, A]` as soon as both endpoints are `≤ A`. -/
private lemma uIcc_subset_Iic {c d A : ℝ} (hc : c ≤ A) (hd : d ≤ A) :
    Set.uIcc c d ⊆ Set.Iic A := by
  intro x hx
  rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact le_trans h2 hd
  · exact le_trans h2 hc

/-- `[[c, d]] ⊆ [B, ∞)` as soon as both endpoints are `≥ B`. -/
private lemma uIcc_subset_Ici {c d B : ℝ} (hc : B ≤ c) (hd : B ≤ d) :
    Set.uIcc c d ⊆ Set.Ici B := by
  intro x hx
  rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact le_trans hc h1
  · exact le_trans hd h1


/-- **Second antiderivative of a test function with two vanishing moments.**

Given `ψ` of class `C^∞` with compact support contained in the open interval `(a,b)` and with
vanishing zeroth and first moments against the interval `(a,b)`, there is a `C^∞` function `ρ`
with compact support contained in `(a,b)` whose second derivative is `ψ`. -/
theorem ExistsTestfunSecondDeriv {a b : ℝ} (hab : a < b) {ψ : ℝ → ℝ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n ψ) (hψc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ Set.Ioo a b)
    (h1 : (∫ t in a..b, ψ t) = 0) (h2 : (∫ t in a..b, t * ψ t) = 0) :
    ∃ ρ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ρ) ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ Set.Ioo a b ∧
      ∀ t : ℝ, deriv (deriv ρ) t = ψ t := by
  have hψcont : Continuous ψ := contDiff_zero.mp (hψ 0)
  have hsupp_sub : Function.support ψ ⊆ Set.Ioo a b :=
    fun x hx => hsupp (subset_tsupport ψ hx)
  have hzts : ∀ t : ℝ, t ∉ tsupport ψ → ψ t = 0 := by
    intro t ht
    by_contra hne
    exact ht (subset_tsupport ψ (Function.mem_support.mpr hne))
  -- `ψ` vanishes outside a slightly smaller closed interval `[A, B]`
  have ha_not : a ∉ tsupport ψ := fun h => absurd (hsupp h).1 (lt_irrefl a)
  have hnb_a : (tsupport ψ)ᶜ ∈ nhds a := (isClosed_tsupport ψ).isOpen_compl.mem_nhds ha_not
  obtain ⟨εa, hεa, hεasub⟩ := Metric.mem_nhds_iff.mp hnb_a
  have hb_not : b ∉ tsupport ψ := fun h => absurd (hsupp h).2 (lt_irrefl b)
  have hnb_b : (tsupport ψ)ᶜ ∈ nhds b := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hb_not
  obtain ⟨εb, hεb, hεbsub⟩ := Metric.mem_nhds_iff.mp hnb_b
  set A : ℝ := a + εa / 2 with hAdef
  set B : ℝ := b - εb / 2 with hBdef
  have hAle : a ≤ A := by rw [hAdef]; linarith
  have hA : a < A := by rw [hAdef]; linarith
  have hBle : B ≤ b := by rw [hBdef]; linarith
  have hB : B < b := by rw [hBdef]; linarith
  have hψzero_le_A : ∀ t : ℝ, t ≤ A → ψ t = 0 := by
    intro t ht
    rcases le_or_gt t a with h | h
    · by_contra hne
      exact absurd (hsupp_sub (Function.mem_support.mpr hne)).1 (not_lt.mpr h)
    · refine hzts t (hεasub ?_)
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr h)]
      have ht' : t ≤ a + εa / 2 := by rw [hAdef] at ht; exact ht
      linarith
  have hψzero_ge_B : ∀ t : ℝ, B ≤ t → ψ t = 0 := by
    intro t ht
    rcases le_or_gt b t with h | h
    · by_contra hne
      exact absurd (hsupp_sub (Function.mem_support.mpr hne)).2 (not_lt.mpr h)
    · refine hzts t (hεbsub ?_)
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr h)]
      have ht' : b - εb / 2 ≤ t := by rw [hBdef] at ht; exact ht
      linarith
  have hψzero : ∀ t : ℝ, t ≤ A ∨ B ≤ t → ψ t = 0 :=
    fun t ht => ht.elim (hψzero_le_A t) (hψzero_ge_B t)
  -- the first antiderivative `Ψ`
  let Ψ : ℝ → ℝ := fun t => ∫ s in a..t, ψ s
  have hΨderiv' : ∀ t : ℝ, HasDerivAt Ψ (ψ t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (f := ψ) (a := a) (b := t)
      (hψcont.intervalIntegrable a t)
      (hψcont.stronglyMeasurableAtFilter volume (nhds t)) hψcont.continuousAt
  have hΨderiv : deriv Ψ = ψ := funext fun t => (hΨderiv' t).deriv
  have hΨdiff : Differentiable ℝ Ψ := fun t => (hΨderiv' t).differentiableAt
  have hΨinf : ContDiff ℝ ∞ Ψ := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨hΨdiff, by rw [hΨderiv]; exact contDiff_infty.mpr hψ⟩
  have hΨcont : Continuous Ψ := (contDiff_infty.mp hΨinf 0).continuous
  have hΨzero_le_A : ∀ t : ℝ, t ≤ A → Ψ t = 0 := by
    intro t ht
    show (∫ s in a..t, ψ s) = 0
    exact intervalIntegral_eq_zero_of_forall_mem_uIcc
      (fun x hx => hψzero_le_A x (uIcc_subset_Iic hAle ht hx))
  have hΨzero_ge_B : ∀ t : ℝ, B ≤ t → Ψ t = 0 := by
    intro t ht
    have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := ψ)
      (a := a) (b := b) (c := t) (hψcont.intervalIntegrable a b) (hψcont.intervalIntegrable b t)
    show (∫ s in a..t, ψ s) = 0
    rw [← hadj, h1]
    have hb' : (∫ x in b..t, ψ x) = 0 :=
      intervalIntegral_eq_zero_of_forall_mem_uIcc
        (fun x hx => hψzero_ge_B x (uIcc_subset_Ici hBle ht hx))
    rw [hb', add_zero]
  have hΨzero : ∀ t : ℝ, t ≤ A ∨ B ≤ t → Ψ t = 0 :=
    fun t ht => ht.elim (hΨzero_le_A t) (hΨzero_ge_B t)
  have hΨa : Ψ a = 0 := hΨzero_le_A a hAle
  have hΨb : Ψ b = 0 := hΨzero_ge_B b hBle
  have hR : (∫ x in a..b, ψ x * x) = 0 := by
    rw [← h2]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  -- the two moment conditions give `∫ Ψ = 0` by integration by parts
  have hΨint : (∫ s in a..b, Ψ s) = 0 := by
    have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := Ψ)
      (v := fun x : ℝ => x) (u' := ψ) (v' := fun _ => (1 : ℝ)) (a := a) (b := b)
      (fun x _ => hΨderiv' x) (fun x _ => hasDerivAt_id x)
      (hψcont.intervalIntegrable a b) (continuous_const.intervalIntegrable a b)
    have hL : (∫ x in a..b, Ψ x * (fun _ => (1 : ℝ)) x) = ∫ x in a..b, Ψ x := by
      apply intervalIntegral.integral_congr
      intro x _
      simp
    rw [hL, hΨb, hΨa, hR] at hIBP
    simpa using hIBP
  -- the second antiderivative `ρ`
  let ρ : ℝ → ℝ := fun t => ∫ s in a..t, Ψ s
  have hρderiv' : ∀ t : ℝ, HasDerivAt ρ (Ψ t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (f := Ψ) (a := a) (b := t)
      (hΨcont.intervalIntegrable a t)
      (hΨcont.stronglyMeasurableAtFilter volume (nhds t)) hΨcont.continuousAt
  have hρderiv : deriv ρ = Ψ := funext fun t => (hρderiv' t).deriv
  have hρdiff : Differentiable ℝ ρ := fun t => (hρderiv' t).differentiableAt
  have hρinf : ContDiff ℝ ∞ ρ := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨hρdiff, by rw [hρderiv]; exact hΨinf⟩
  have hρzero_le_A : ∀ t : ℝ, t ≤ A → ρ t = 0 := by
    intro t ht
    show (∫ s in a..t, Ψ s) = 0
    exact intervalIntegral_eq_zero_of_forall_mem_uIcc
      (fun x hx => hΨzero_le_A x (uIcc_subset_Iic hAle ht hx))
  have hρzero_ge_B : ∀ t : ℝ, B ≤ t → ρ t = 0 := by
    intro t ht
    have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := Ψ)
      (a := a) (b := b) (c := t) (hΨcont.intervalIntegrable a b) (hΨcont.intervalIntegrable b t)
    show (∫ s in a..t, Ψ s) = 0
    rw [← hadj, hΨint]
    have hb' : (∫ x in b..t, Ψ x) = 0 :=
      intervalIntegral_eq_zero_of_forall_mem_uIcc
        (fun x hx => hΨzero_ge_B x (uIcc_subset_Ici hBle ht hx))
    rw [hb', add_zero]
  -- `ρ` is supported in `(A, B)`, hence in `(a, b)`
  have hsuppρ : Function.support ρ ⊆ Set.Ioo A B := by
    intro t ht
    have ht' : ρ t ≠ 0 := Function.mem_support.mp ht
    by_contra hcon
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hcon
    rcases hcon with h | h
    · exact ht' (hρzero_le_A t h)
    · exact ht' (hρzero_ge_B t h)
  have htsp : tsupport ρ ⊆ Set.Ioo a b := by
    intro x hx
    have hx' : x ∈ closure (Set.Ioo A B) := closure_mono hsuppρ hx
    have hx'' : x ∈ Set.Icc A B :=
      (closure_minimal (Set.Ioo_subset_Icc_self : Set.Ioo A B ⊆ Set.Icc A B) isClosed_Icc :
        closure (Set.Ioo A B) ⊆ Set.Icc A B) hx'
    exact ⟨lt_of_lt_of_le hA hx''.1, lt_of_le_of_lt hx''.2 hB⟩
  have hcomp : HasCompactSupport ρ :=
    (isCompact_Icc (a := a) (b := b)).of_isClosed_subset (isClosed_tsupport ρ)
      (fun x hx => Set.Ioo_subset_Icc_self (htsp hx))
  exact ⟨ρ, fun n => contDiff_infty.mp hρinf n, hcomp, htsp, fun t => by
    rw [hρderiv]
    exact congrFun hΨderiv t⟩

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.FubiniZWeight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory Set

/-- The point `b` belongs to the unordered interval `[a,b]` when `a ≤ b`. -/
private lemma fubiniZWeight_mem_uIcc {a b : ℝ} (hab : a ≤ b) : b ∈ Set.uIcc a b := by
  rw [Set.uIcc_of_le hab]
  exact ⟨hab, le_rfl⟩

/-- **Integration by parts for a triangular domain.**

For an interval integrable `g` and an absolutely continuous `φ` on `[a,b]` with `φ a = 0`,
```
∫_a^b φ'(t) (∫_t^b g(z) dz) dt = ∫_a^b g(z) φ(z) dz .
```
The primitive `t ↦ ∫_t^b g z dz` is absolutely continuous and, by the Lebesgue differentiation
theorem (`IntervalIntegrable.ae_hasDerivAt_integral`), has a.e. derivative `-g`; integration by
parts for absolutely continuous functions then gives the identity, the boundary term at `b`
vanishing because the integral over `[b,b]` is zero and the term at `a` vanishing because
`φ a = 0`. -/
private lemma fubiniZWeight_ibp_triangle {a b : ℝ} {g φ : ℝ → ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b)
    (hφ : AbsolutelyContinuousOnInterval φ a b) (hφa : φ a = 0) :
    ∫ t in a..b, deriv φ t * (∫ z in t..b, g z) = ∫ z in a..b, g z * φ z := by
  -- The two primitives `G t = ∫ z in b..t, g z` and its negative `F = -G`.
  let G : ℝ → ℝ := fun t => ∫ z in b..t, g z
  let F : ℝ → ℝ := -G
  have hF_eq : ∀ t, F t = ∫ z in t..b, g z := by
    intro t
    have hsym : ∫ z in b..t, g z = -∫ z in t..b, g z := intervalIntegral.integral_symm t b
    simp only [F, G, Pi.neg_apply]
    linarith
  have hGac : AbsolutelyContinuousOnInterval G a b :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral hg
      (fubiniZWeight_mem_uIcc hab)
  -- The a.e. derivative of `G`, from the Lebesgue differentiation theorem.
  have hGd : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt G (g x) x := by
    filter_upwards [IntervalIntegrable.ae_hasDerivAt_integral hg] with x hx hxab
    exact hx hxab b (fubiniZWeight_mem_uIcc hab)
  have hFd : ∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt F (-(g x)) x := by
    filter_upwards [hGd] with x hx hxab
    exact (hx hxab).neg
  have hFac : AbsolutelyContinuousOnInterval F a b := hGac.neg
  have hFb : F b = 0 := by rw [hF_eq b, intervalIntegral.integral_same]
  -- Replace `deriv F` by `-g` under the integral.
  have hderiv : ∫ x in a..b, deriv F x * φ x = -∫ x in a..b, g x * φ x := by
    have h1 : ∫ x in a..b, deriv F x * φ x = ∫ x in a..b, -(g x * φ x) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hFd] with x hx hxu
      rw [(hx (Set.uIoc_subset_uIcc hxu)).deriv, neg_mul]
    rw [h1, intervalIntegral.integral_neg]
  have hIBP := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hFac hφ
  have hmain : ∫ x in a..b, F x * deriv φ x = ∫ x in a..b, g x * φ x := by
    rw [hIBP, hFb, hφa, hderiv]
    ring
  rw [show (∫ t in a..b, deriv φ t * (∫ z in t..b, g z)) = ∫ t in a..b, deriv φ t * F t from
    intervalIntegral.integral_congr (fun t _ => by rw [hF_eq t])]
  rw [show (∫ t in a..b, deriv φ t * F t) = ∫ t in a..b, F t * deriv φ t from
    intervalIntegral.integral_congr (fun t _ => mul_comm _ _)]
  exact hmain

theorem FubiniZWeight {a b : ℝ} {W ρ : ℝ → ℝ}
    (hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0)) (ha : 0 < a) (hab : a < b)
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ) (hρc : HasCompactSupport ρ)
    (hsupp : tsupport ρ ⊆ Set.Ioo a b) :
    (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, W z * z))
      = ∫ z in a..b, W z * z * deriv ρ z := by
  -- `z ↦ W z * z` is locally integrable on `(0,∞)` (hence integrable on `[a,b]`, as `a > 0`).
  have hloc : MeasureTheory.LocallyIntegrableOn (fun z : ℝ => W z * z) (Set.Ioi 0) :=
    hW.mul_continuousOn continuous_id.continuousOn isOpen_Ioi.isLocallyClosed
  have hgIcc : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact hloc.integrableOn_compact_subset (fun z hz => lt_of_lt_of_le ha hz.1) isCompact_Icc
  have hg : IntervalIntegrable (fun z : ℝ => W z * z) volume a b :=
    intervalIntegrable_iff.mpr (hgIcc.mono_set Set.uIoc_subset_uIcc)
  -- `deriv ρ` is Lipschitz (hence absolutely continuous) on `[a,b]`: it is `C¹` there.
  have hφ : AbsolutelyContinuousOnInterval (deriv ρ) a b := by
    have hd : ContDiffOn ℝ 1 (deriv ρ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 2 ρ Set.univ := (hρ 2).contDiffOn
      exact (h2.deriv_of_isOpen isOpen_univ (by norm_num)).mono (Set.subset_univ _)
    obtain ⟨K, hK⟩ := hd.exists_lipschitzOnWith (by norm_num) (convex_uIcc a b) isCompact_uIcc
    exact hK.absolutelyContinuousOnInterval
  -- `deriv ρ` vanishes at `a`: `tsupport (deriv ρ) ⊆ tsupport ρ ⊆ (a,b)`.
  have hφa : deriv ρ a = 0 := by
    have ha_not : a ∉ tsupport ρ := fun h => (lt_irrefl a) (hsupp h).1
    exact image_eq_zero_of_notMem_tsupport (fun h => ha_not (tsupport_deriv_subset h))
  exact fubiniZWeight_ibp_triangle hab.le hg hφ hφa

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroRepr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

theorem SlotsZeroRepr {α : ℝ} (hα : 0 < α) {u : ℝ → ℝ → ℝ} {θ : ℝ}
    (hdiff : DifferentiableOn ℝ (fun z => u z θ) (Set.Ioi 0))
    (hode : ∀ z, 0 < z → z * deriv (fun z' => u z' θ) z = -(3 / α) * u z θ) :
    ∀ z, 0 < z → u z θ = u 1 θ * z ^ (-(3 / α)) := by
  -- The inhomogeneous problem `z f' = s f` with `s := -(3/α)` has the general solution
  -- `f z = C · z^s` on the connected open set `z > 0`: the function `z ↦ f z · z^{-s}` has
  -- vanishing derivative there, hence is constant.
  have _hαne : α ≠ 0 := ne_of_gt hα
  intro z hz
  let f : ℝ → ℝ := fun z => u z θ
  let h : ℝ → ℝ := f * fun z => z ^ (3 / α)
  -- the logarithmic derivative of `h` vanishes on `z > 0`
  have hder : ∀ w ∈ Set.Ioi (0 : ℝ), deriv h w = 0 := by
    intro w hw
    have hw0 : 0 < w := hw
    have hfd : DifferentiableAt ℝ f w := hdiff.differentiableAt (isOpen_Ioi.mem_nhds hw)
    have hgd : HasDerivAt (fun z : ℝ => z ^ (3 / α)) ((3 / α) * w ^ (3 / α - 1)) w :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hw0))
    have hmul : deriv h w = deriv f w * w ^ (3 / α) + f w * ((3 / α) * w ^ (3 / α - 1)) := by
      show deriv (f * fun z : ℝ => z ^ (3 / α)) w
          = deriv f w * w ^ (3 / α) + f w * ((3 / α) * w ^ (3 / α - 1))
      rw [deriv_mul hfd hgd.differentiableAt, hgd.deriv]
    -- `w · w^{(3/α)-1} = w^{3/α}`
    have hwp : w * w ^ (3 / α - 1) = w ^ (3 / α) := by
      calc w * w ^ (3 / α - 1) = w ^ (1 : ℝ) * w ^ (3 / α - 1) := by rw [Real.rpow_one]
        _ = w ^ ((1 : ℝ) + (3 / α - 1)) := by rw [Real.rpow_add hw0]
        _ = w ^ (3 / α) := by congr 1; ring
    have hode' : w * deriv f w = -(3 / α) * f w := by
      have hh := hode w hw0
      simpa only [f] using hh
    have hkey : deriv h w * w = 0 := by
      rw [hmul, ← hwp]
      have : (deriv f w * (w * w ^ (3 / α - 1)) + f w * ((3 / α) * w ^ (3 / α - 1))) * w
          = w ^ (3 / α - 1) * w * (w * deriv f w + (3 / α) * f w) := by ring
      rw [this, hode']
      ring
    rcases mul_eq_zero.mp hkey with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt hw0)
  have hdiffh : DifferentiableOn ℝ h (Set.Ioi 0) := by
    intro w hw
    have hw0 : 0 < w := hw
    have hfd : DifferentiableAt ℝ f w := hdiff.differentiableAt (isOpen_Ioi.mem_nhds hw)
    have hgd : DifferentiableAt ℝ (fun z : ℝ => z ^ (3 / α)) w :=
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hw0))).differentiableAt
    exact (hfd.mul hgd).differentiableWithinAt
  obtain ⟨a, ha⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi hdiffh
    (fun w hw => hder w hw)
  have hz1' : u z θ * z ^ (3 / α) = u 1 θ := by
    have hh : h z = h 1 := by rw [ha z hz, ha 1 (by norm_num)]
    simp only [h, Pi.mul_apply, f, Real.one_rpow, mul_one] at hh
    exact hh
  have hzc : z ^ (3 / α) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hz (3 / α))
  calc u z θ = u 1 θ * (z ^ (3 / α))⁻¹ := (eq_mul_inv_iff_mul_eq₀ hzc).mpr hz1'
    _ = u 1 θ * z ^ (-(3 / α)) := by rw [← Real.rpow_neg (le_of_lt hz) (3 / α)]

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.contDiffOn_one_integral_left =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

theorem contDiffOn_one_integral_left {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hf : ContinuousOn f (Set.Ioi 0)) :
    ContDiffOn ℝ 1 (fun t => ∫ z in t..b, f z) (Set.Ioi 0) ∧
      ∀ t ∈ Set.Ioi 0, deriv (fun t => ∫ z in t..b, f z) t = - f t := by
  -- `f` is continuous at every point of the open half-line `(0, ∞)`
  have hct : ∀ x ∈ Set.Ioi (0 : ℝ), ContinuousAt f x :=
    fun x hx => (hf.continuousWithinAt hx).continuousAt (Ioi_mem_nhds hx)
  -- the closed interval between `t > 0` and `b > 0` stays inside `(0, ∞)`
  have hsub : ∀ t ∈ Set.Ioi (0 : ℝ), Set.uIcc t b ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht x hx
    rw [Set.mem_Ioi] at ht
    rw [Set.mem_Ioi]
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩
    · linarith
    · linarith
  -- fundamental theorem of calculus: differentiation in the left endpoint
  have hhas : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun u => ∫ z in u..b, f z) (-f t) t := by
    intro t ht
    have hInt : IntervalIntegrable f (MeasureTheory.volume : MeasureTheory.Measure ℝ) t b :=
      (hf.mono (hsub t ht)).intervalIntegrable
    exact intervalIntegral.integral_hasDerivAt_left hInt
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hct t ht) (hct t ht)
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), deriv (fun u => ∫ z in u..b, f z) t = -f t :=
    fun t ht => (hhas t ht).deriv
  refine ⟨?_, hderiv⟩
  rw [contDiffOn_one_iff_derivWithin (𝕜 := ℝ) isOpen_Ioi.uniqueDiffOn]
  refine ⟨fun t ht => (hhas t ht).differentiableAt.differentiableWithinAt, ?_⟩
  refine (hf.neg).congr fun t ht => ?_
  rw [derivWithin_of_isOpen isOpen_Ioi ht, hderiv t ht]
  rfl

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.continuousOn_integral_left =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open MeasureTheory

namespace Work.FTS.StrongEps.EComparison

/-- The left primitive `t ↦ ∫ z in t..b, f z` of a function `f` that is locally integrable on
`(0, ∞)` is continuous on `(0, ∞)`, provided `b > 0` — so that the whole interval between the
variable point `t` and `b` stays inside the half-line on which `f` is controlled. -/
theorem continuousOn_integral_left {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hf : MeasureTheory.LocallyIntegrableOn f (Set.Ioi 0)) :
    ContinuousOn (fun t => ∫ z in t..b, f z) (Set.Ioi 0) := by
  intro t₀ ht₀
  have ht₀pos : (0 : ℝ) < t₀ := ht₀
  -- An interval `[b₁, b₂]` with `0 < b₁ < t₀ < b₂`.
  obtain ⟨b₁, b₂, hb₁pos, hb₁lt, ht₀lt⟩ : ∃ b₁ b₂ : ℝ, 0 < b₁ ∧ b₁ < t₀ ∧ t₀ < b₂ := by
    refine ⟨min (b / 2) (t₀ / 2), b + t₀ + 1, ?_, ?_, ?_⟩
    · exact lt_min (by linarith) (by linarith)
    · have hle : min (b / 2) (t₀ / 2) ≤ t₀ / 2 := min_le_right _ _
      linarith
    · linarith
  -- `f` is integrable on `[min b b₁, max b b₂]`, which lies inside `(0, ∞)`.
  have hsub : Set.uIcc (min b b₁) (max b b₂) ⊆ Set.Ioi 0 := by
    intro x hx
    have hx' := Set.mem_uIcc.mp hx
    have hpos : (0 : ℝ) < min b b₁ := lt_min hb hb₁pos
    rcases hx' with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact lt_of_lt_of_le hpos h1
    · exact lt_of_lt_of_le (lt_of_lt_of_le hb (le_max_left b b₂)) h1
  have hIntU : MeasureTheory.IntegrableOn f (Set.uIcc (min b b₁) (max b b₂)) :=
    hf.integrableOn_compact_subset hsub isCompact_uIcc
  have hInt : IntervalIntegrable f volume (min b b₁) (max b b₂) := hIntU.intervalIntegrable
  -- Fundamental theorem of calculus: the primitive of the upper limit is continuous.
  have key : ContinuousWithinAt (fun x => ∫ z in b..x, f z) (Set.Icc b₁ b₂) t₀ :=
    intervalIntegral.continuousWithinAt_primitive (MeasureTheory.measure_singleton t₀) hInt
  have hmem : Set.Icc b₁ b₂ ∈ 𝓝[Set.Ioi 0] t₀ :=
    mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hb₁lt ht₀lt)
  have key' : ContinuousWithinAt (fun x => ∫ z in b..x, f z) (Set.Ioi 0) t₀ :=
    key.mono_left (nhdsWithin_le_iff.mpr hmem)
  -- `∫ z in t..b, f z = -∫ z in b..t, f z`.
  have hF : (fun t => ∫ z in t..b, f z) = fun t => -∫ z in b..t, f z := by
    funext t
    rw [intervalIntegral.integral_symm]
  rw [hF]
  exact key'.neg

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.existsBumpMoments =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A `C^∞` bump with prescribed first moments

For `a < b` we construct a `C^∞` function `χ` with compact support in the open interval `(a,b)`,
whose integral over `(a,b)` equals `1` and whose first two moments against `deriv χ` are
`∫ χ' = 0` and `∫ t · χ'(t) = -1`.

Both derivative identities are automatic for *any* bump of total mass one supported in `(a,b)`:
`∫ χ' = χ b - χ a = 0` and `∫ t χ'(t) = b χ(b) - a χ(a) - ∫ χ = -1` (integration by parts).
So it suffices to exhibit a nonnegative `C^∞` bump of positive mass supported in a strictly
smaller closed interval `[lo, hi] ⊆ (a,b)` and normalise it.

The building block is the elementary bump `g x = smoothTransition x * smoothTransition (1 - x)`,
which is `C^∞`, nonnegative, positive exactly on `(0,1)` and vanishes off `(0,1)`; its integral
`M = ∫ g` is positive.  We then set
`χ t = ((hi - lo) * M)⁻¹ * g ((t - lo) / (hi - lo))`
with `lo = a + (b-a)/4` and `hi = b - (b-a)/4`, so that `a < lo < hi < b` and
`∫ χ = ((hi-lo)*M)⁻¹ * ((hi-lo) * M) = 1`.
-/

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory Set
open scoped Topology ContDiff Interval

/-- The elementary smooth bump `x ↦ smoothTransition x * smoothTransition (1 - x)`: it is `C^∞`,
nonnegative, and positive exactly on `(0,1)` (it vanishes on `(-∞,0] ∪ [1,∞)`). -/
private noncomputable def bumpG (x : ℝ) : ℝ :=
  Real.smoothTransition x * Real.smoothTransition (1 - x)

private lemma bumpG_contDiff : ContDiff ℝ ∞ bumpG := by
  have h1 : ContDiff ℝ ∞ fun x : ℝ => Real.smoothTransition x :=
    Real.smoothTransition.contDiff
  have h2 : ContDiff ℝ ∞ fun x : ℝ => Real.smoothTransition (1 - x) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)
  exact h1.mul h2

private lemma bumpG_nonneg (x : ℝ) : 0 ≤ bumpG x :=
  mul_nonneg (Real.smoothTransition.nonneg x) (Real.smoothTransition.nonneg (1 - x))

private lemma bumpG_pos_half : bumpG (1 / 2) ≠ 0 := by
  have h1 : 0 < Real.smoothTransition (1 / 2 : ℝ) := Real.smoothTransition.pos_of_pos (by norm_num)
  have h2 : 0 < Real.smoothTransition (1 - 1 / 2 : ℝ) :=
    Real.smoothTransition.pos_of_pos (by norm_num)
  exact ne_of_gt (by simpa [bumpG] using mul_pos h1 h2)

private lemma bumpG_support_subset : Function.support bumpG ⊆ Set.Ioo 0 1 := by
  intro x hx
  rw [Function.mem_support] at hx
  have hx1 : Real.smoothTransition x ≠ 0 := fun h => hx (by rw [bumpG, h, zero_mul])
  have hx2 : Real.smoothTransition (1 - x) ≠ 0 := fun h => hx (by rw [bumpG, h, mul_zero])
  exact ⟨lt_of_not_ge fun h => hx1 (Real.smoothTransition.zero_iff_nonpos.mpr h),
    lt_of_not_ge fun h => hx2 (Real.smoothTransition.zero_iff_nonpos.mpr (by linarith))⟩

private lemma bumpG_support_subset_Ioc : Function.support bumpG ⊆ Set.Ioc 0 1 :=
  fun _ hx => ⟨(bumpG_support_subset hx).1, (bumpG_support_subset hx).2.le⟩

private lemma bumpG_tsupport_subset : tsupport bumpG ⊆ Set.Icc 0 1 :=
  closure_minimal
    (fun _ hx => ⟨(bumpG_support_subset hx).1.le, (bumpG_support_subset hx).2.le⟩)
    isClosed_Icc

private lemma bumpG_hasCompactSupport : HasCompactSupport bumpG :=
  (isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset (isClosed_tsupport bumpG)
    bumpG_tsupport_subset

private lemma bumpG_continuous : Continuous bumpG := bumpG_contDiff.continuous

private lemma bumpG_integral_pos : 0 < ∫ x, bumpG x :=
  bumpG_continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    bumpG_hasCompactSupport bumpG_nonneg bumpG_pos_half

private lemma bumpG_integral_interval : (∫ u in (0 : ℝ)..1, bumpG u) = ∫ u, bumpG u :=
  intervalIntegral.integral_eq_integral_of_support_subset bumpG_support_subset_Ioc

/-- The affine change of variables for the elementary bump: translating its argument by `A` and
rescaling by `B - A` multiplies the integral by `B - A`. -/
private lemma bumpG_integral_affine {A B : ℝ} (hAB : A < B) :
    ∫ t : ℝ, bumpG ((t - A) / (B - A)) = (B - A) * ∫ u, bumpG u := by
  have hBA : (0 : ℝ) < B - A := sub_pos.mpr hAB
  have hBA' : B - A ≠ 0 := ne_of_gt hBA
  have hsupp : Function.support (fun t : ℝ => bumpG ((t - A) / (B - A))) ⊆ Set.Ioc A B := by
    intro t ht
    rw [Function.mem_support] at ht
    obtain ⟨h1, h2⟩ := bumpG_support_subset ht
    rw [div_pos_iff_of_pos_right hBA] at h1
    rw [div_lt_one hBA] at h2
    exact ⟨by linarith, by linarith⟩
  calc ∫ t : ℝ, bumpG ((t - A) / (B - A))
      = ∫ t in A..B, bumpG ((t - A) / (B - A)) :=
        (intervalIntegral.integral_eq_integral_of_support_subset hsupp).symm
    _ = ∫ s in (0 : ℝ)..(B - A), bumpG (s / (B - A)) := by
        rw [intervalIntegral.integral_comp_sub_right (f := fun s : ℝ => bumpG (s / (B - A)))
          (a := A) (b := B) (d := A)]
        simp only [sub_self]
    _ = (B - A) * ∫ u in (0 : ℝ)..1, bumpG u := by
        rw [intervalIntegral.integral_comp_div (f := bumpG) (a := (0 : ℝ)) (b := B - A) hBA']
        rw [zero_div, div_self hBA', smul_eq_mul]
    _ = (B - A) * ∫ u, bumpG u := by rw [bumpG_integral_interval]

/-- The mass of the elementary bump. -/
private noncomputable def bumpM : ℝ := ∫ u, bumpG u

private lemma bumpM_pos : 0 < bumpM := bumpG_integral_pos

/-- Left endpoint of the support interval: `a + (b-a)/4`. -/
private noncomputable def bumpLo (a b : ℝ) : ℝ := a + (b - a) / 4

/-- Right endpoint of the support interval: `b - (b-a)/4`. -/
private noncomputable def bumpHi (a b : ℝ) : ℝ := b - (b - a) / 4

/-- The width of the support interval. -/
private noncomputable def bumpW (a b : ℝ) : ℝ := bumpHi a b - bumpLo a b

private lemma bumpLo_lt_bumpHi {a b : ℝ} (hab : a < b) : bumpLo a b < bumpHi a b := by
  have h : 0 < b - a := sub_pos.mpr hab
  simp only [bumpLo, bumpHi]
  linarith

private lemma lt_bumpLo {a b : ℝ} (hab : a < b) : a < bumpLo a b := by
  have h : 0 < b - a := sub_pos.mpr hab
  simp only [bumpLo]
  linarith

private lemma bumpHi_lt {a b : ℝ} (hab : a < b) : bumpHi a b < b := by
  have h : 0 < b - a := sub_pos.mpr hab
  simp only [bumpHi]
  linarith

private lemma bumpW_pos {a b : ℝ} (hab : a < b) : 0 < bumpW a b := by
  have h : bumpLo a b < bumpHi a b := bumpLo_lt_bumpHi hab
  simp only [bumpW]
  linarith

private lemma bumpW_ne_zero {a b : ℝ} (hab : a < b) : bumpW a b ≠ 0 := ne_of_gt (bumpW_pos hab)

/-- The bump: a normalised, translated and rescaled copy of the elementary bump, whose support
lies in `(bumpLo a b, bumpHi a b) ⊂ (a,b)`. -/
private noncomputable def bumpChi (a b : ℝ) : ℝ → ℝ :=
  fun t => (bumpW a b * bumpM)⁻¹ * bumpG ((t - bumpLo a b) / bumpW a b)

private lemma bumpChi_contDiff (a b : ℝ) : ContDiff ℝ ∞ (bumpChi a b) := by
  have h : ContDiff ℝ ∞ fun t : ℝ => (t - bumpLo a b) / bumpW a b :=
    (contDiff_id.sub contDiff_const).div_const _
  exact contDiff_const.mul (bumpG_contDiff.comp h)

private lemma bumpChi_support_subset_lo_hi {a b : ℝ} (hab : a < b) :
    Function.support (bumpChi a b) ⊆ Set.Ioo (bumpLo a b) (bumpHi a b) := by
  intro t ht
  rw [Function.mem_support] at ht
  have hg : bumpG ((t - bumpLo a b) / bumpW a b) ≠ 0 := by
    intro h
    exact ht (by rw [bumpChi, h, mul_zero])
  obtain ⟨h1, h2⟩ := bumpG_support_subset hg
  have hw : 0 < bumpW a b := bumpW_pos hab
  rw [div_pos_iff_of_pos_right hw] at h1
  rw [div_lt_one hw] at h2
  simp only [bumpW] at h2
  exact ⟨by linarith, by linarith⟩

private lemma bumpChi_support_subset {a b : ℝ} (hab : a < b) :
    Function.support (bumpChi a b) ⊆ Set.Ioo a b := by
  intro t ht
  obtain ⟨h1, h2⟩ := bumpChi_support_subset_lo_hi hab ht
  exact ⟨lt_trans (lt_bumpLo hab) h1, lt_trans h2 (bumpHi_lt hab)⟩

private lemma bumpChi_tsupport_subset {a b : ℝ} (hab : a < b) :
    tsupport (bumpChi a b) ⊆ Set.Ioo a b := by
  have hcl : tsupport (bumpChi a b) ⊆ Set.Icc (bumpLo a b) (bumpHi a b) :=
    closure_minimal
      (fun x hx => ⟨(bumpChi_support_subset_lo_hi hab hx).1.le,
        (bumpChi_support_subset_lo_hi hab hx).2.le⟩)
      isClosed_Icc
  intro x hx
  obtain ⟨h1, h2⟩ := hcl hx
  exact ⟨lt_of_lt_of_le (lt_bumpLo hab) h1, lt_of_le_of_lt h2 (bumpHi_lt hab)⟩

private lemma bumpChi_hasCompactSupport {a b : ℝ} (hab : a < b) :
    HasCompactSupport (bumpChi a b) :=
  (isCompact_Icc (a := a) (b := b)).of_isClosed_subset (isClosed_tsupport _)
    (fun _ hx => Set.Ioo_subset_Icc_self (bumpChi_tsupport_subset hab hx))

private lemma bumpChi_support_subset_Ioc {a b : ℝ} (hab : a < b) :
    Function.support (bumpChi a b) ⊆ Set.Ioc a b :=
  fun _ hx => ⟨(bumpChi_support_subset hab hx).1, (bumpChi_support_subset hab hx).2.le⟩

private lemma bumpChi_zero_of_notMem_tsupport {a b : ℝ} {t : ℝ}
    (ht : t ∉ tsupport (bumpChi a b)) : bumpChi a b t = 0 := by
  by_contra h
  exact ht (subset_tsupport (bumpChi a b) (Function.mem_support.mpr h))

private lemma bumpChi_zero_at_left {a b : ℝ} (hab : a < b) : bumpChi a b a = 0 :=
  bumpChi_zero_of_notMem_tsupport fun h => absurd (bumpChi_tsupport_subset hab h).1 (lt_irrefl a)

private lemma bumpChi_zero_at_right {a b : ℝ} (hab : a < b) : bumpChi a b b = 0 :=
  bumpChi_zero_of_notMem_tsupport fun h => absurd (bumpChi_tsupport_subset hab h).2 (lt_irrefl b)

private lemma bumpChi_integral {a b : ℝ} (hab : a < b) : (∫ t in a..b, bumpChi a b t) = 1 := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset (bumpChi_support_subset_Ioc hab)]
  have haff := bumpG_integral_affine (A := bumpLo a b) (B := bumpHi a b) (bumpLo_lt_bumpHi hab)
  have hval : (∫ t : ℝ, bumpG ((t - bumpLo a b) / bumpW a b)) = bumpW a b * bumpM := by
    simpa [bumpW, bumpM] using haff
  have hmul : (bumpW a b * bumpM)⁻¹ * (bumpW a b * bumpM) = 1 :=
    inv_mul_cancel₀ (mul_ne_zero (bumpW_ne_zero hab) (ne_of_gt bumpM_pos))
  simp only [bumpChi]
  rw [integral_const_mul, hval, hmul]

private lemma bumpChi_differentiableAt {a b : ℝ} (x : ℝ) :
    DifferentiableAt ℝ (bumpChi a b) x := by
  have h : Differentiable ℝ (bumpChi a b) :=
    (contDiff_infty.mp (bumpChi_contDiff a b) 1).differentiable (by norm_num)
  exact h.differentiableAt

private lemma bumpChi_continuous_deriv {a b : ℝ} : Continuous (deriv (bumpChi a b)) :=
  (contDiff_infty.mp (bumpChi_contDiff a b) 1).continuous_deriv le_rfl

private lemma bumpChi_deriv_integral {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, deriv (bumpChi a b) t) = 0 := by
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun x _ => bumpChi_differentiableAt x) (bumpChi_continuous_deriv.intervalIntegrable a b),
    bumpChi_zero_at_right hab, bumpChi_zero_at_left hab, sub_zero]

private lemma bumpChi_moment {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, t * deriv (bumpChi a b) t) = -1 := by
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => t) (v := bumpChi a b) (u' := fun _ => (1 : ℝ))
    (v' := deriv (bumpChi a b)) (a := a) (b := b)
    (fun x _ => hasDerivAt_id x) (fun x _ => (bumpChi_differentiableAt x).hasDerivAt)
    intervalIntegrable_const (bumpChi_continuous_deriv.intervalIntegrable a b)
  have hint : (∫ x in a..b, (1 : ℝ) * bumpChi a b x) = 1 := by
    rw [intervalIntegral.integral_congr (fun x _ => one_mul (bumpChi a b x))]
    exact bumpChi_integral hab
  rw [bumpChi_zero_at_right hab, bumpChi_zero_at_left hab, hint] at hIBP
  simp only [mul_zero, sub_zero] at hIBP
  linarith [hIBP]

open MeasureTheory Set in
open scoped Topology ContDiff Interval in
theorem existsBumpMoments {a b : ℝ} (hab : a < b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Set.Ioo a b ∧
      (∫ t in a..b, χ t) = 1 ∧ (∫ t in a..b, deriv χ t) = 0 ∧
      (∫ t in a..b, t * deriv χ t) = -1 :=
  ⟨bumpChi a b, bumpChi_contDiff a b, bumpChi_hasCompactSupport hab, bumpChi_tsupport_subset hab,
    bumpChi_integral hab, bumpChi_deriv_integral hab, bumpChi_moment hab⟩

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.integrable_fubiniWeightZ_integrand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

/-- **Integrability of the `FubiniWeightZ` integrand on `[a,b] × [a,b]`.**

On the product `(volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))` the first coordinate
lies a.e. in the compact interval `[a,b]`, where `deriv (deriv ρ)` is bounded (it is continuous,
`ρ` being `C^∞`), and the second factor `(if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0)` is
dominated by `(b - a) * ‖W p.2‖` (the indicator only cuts the integrand down, and
`p.2 - p.1 ≤ b - a`).  Because `[a,b] ⊆ (0,∞)` (as `a > 0`), the local integrability of `W` on
`(0,∞)` gives `IntegrableOn W (Icc a b)`, hence `fun p => ‖W p.2‖` is integrable on the product
measure; multiplying by the two constants and applying `Integrable.mono'` gives the claim. -/
theorem integrable_fubiniWeightZ_integrand {a b : ℝ} {W ρ : ℝ → ℝ}
    (hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0)) (ha : 0 < a) (hab : a < b)
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => deriv (deriv ρ) p.1
        * (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0))
      ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc a b))) := by
  let ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc a b)
  change MeasureTheory.Integrable (fun p : ℝ × ℝ => deriv (deriv ρ) p.1 *
    (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0)) (ν.prod ν)
  -- `W` is integrable on `[a,b]`, which sits inside `(0,∞)`.
  have hWint : MeasureTheory.Integrable W ν :=
    hW.integrableOn_compact_subset (fun x hx => lt_of_lt_of_le ha hx.1) isCompact_Icc
  -- `deriv (deriv ρ)` is continuous, hence bounded on the compact interval `[a,b]`.
  have hcont : Continuous (deriv (deriv ρ)) := by
    have h2 := (hρ 2).continuous_iteratedDeriv 2 le_rfl
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using h2
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  -- The dominating function.
  have hdom : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => C * ((b - a) * ‖W p.2‖)) (ν.prod ν) :=
    ((hWint.norm.const_mul (b - a)).const_mul C).comp_snd ν
  -- A.e. the two coordinates lie in `[a,b]`.
  have hmem : ∀ᵐ p ∂(ν.prod ν), p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a b := by
    refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem (μ := ν) (ν := ν)
      (s := Set.Icc a b ×ˢ Set.Icc a b) (measurableSet_Icc.prod measurableSet_Icc)).mpr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Icc] with x hx
    filter_upwards
      [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Icc] with y hy
    exact ⟨hx, hy⟩
  -- A.e. strong measurability of the integrand.
  have hF_aesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => deriv (deriv ρ) p.1 *
        (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0)) (ν.prod ν) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => deriv (deriv ρ) p.1) (ν.prod ν) :=
      (hcont.comp continuous_fst).stronglyMeasurable.aestronglyMeasurable
    have hWsm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => W p.2) (ν.prod ν) :=
      ((hWint.aestronglyMeasurable).aemeasurable.comp_snd (μ := ν)).aestronglyMeasurable
    have hlin : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (p.2 - p.1)) (ν.prod ν) :=
      ((continuous_snd.sub continuous_fst).stronglyMeasurable.aestronglyMeasurable)
    have hind : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => if p.1 ≤ p.2 then (1 : ℝ) else 0) (ν.prod ν) :=
      (Measurable.ite (measurableSet_le measurable_fst measurable_snd) measurable_const
        measurable_const).stronglyMeasurable.aestronglyMeasurable
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0)) (ν.prod ν) := by
      rw [show (fun p : ℝ × ℝ => (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0))
          = (fun p : ℝ × ℝ => (if p.1 ≤ p.2 then (1 : ℝ) else 0) * ((p.2 - p.1) * W p.2)) from by
            funext p; by_cases h : p.1 ≤ p.2 <;> simp [h]]
      exact hind.mul (hlin.mul hWsm)
    exact h1.mul h2
  -- The a.e. pointwise domination.
  have hbound : ∀ᵐ p ∂(ν.prod ν), ‖deriv (deriv ρ) p.1 *
      (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0)‖ ≤ C * ((b - a) * ‖W p.2‖) := by
    filter_upwards [hmem] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hCb : ‖deriv (deriv ρ) p.1‖ ≤ C := hC p.1 hp1
    have hCnn : 0 ≤ C := le_trans (norm_nonneg _) hCb
    rw [norm_mul]
    refine mul_le_mul hCb ?_ (norm_nonneg _) hCnn
    by_cases h : p.1 ≤ p.2
    · rw [ite_eq_left h, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h)]
      have hle : p.2 - p.1 ≤ b - a := by linarith [hp1.1, hp2.2]
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    · rw [ite_eq_right h, norm_zero]
      positivity
  exact MeasureTheory.Integrable.mono' hdom hF_aesm hbound

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.intervalIntegral_eq_setIntegral_indicator =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

theorem intervalIntegral_eq_setIntegral_indicator {a b t : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (g : ℝ → ℝ) :
    (∫ z in t..b, g z) = ∫ z in Set.Icc a b, (if t ≤ z then g z else 0) := by
  -- the interval integral is the set integral over `Ioc t b`
  rw [intervalIntegral.integral_of_le htb,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc (x := t) (y := b)]
  -- convert both sides to integrals of indicators over `ℝ`
  rw [← MeasureTheory.integral_indicator (s := Set.Icc t b) (f := g) measurableSet_Icc,
    ← MeasureTheory.integral_indicator (s := Set.Icc a b)
      (f := fun z => if t ≤ z then g z else 0) measurableSet_Icc]
  -- the two indicators agree everywhere (both `a ≤ t` and `t ∈ Icc a b` are used)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Set.Icc t b
  · have hza : z ∈ Set.Icc a b := ⟨le_trans hat hz.1, hz.2⟩
    rw [Set.indicator_of_mem hz, Set.indicator_of_mem hza, ite_eq_left hz.1]
  · rw [Set.indicator_of_notMem hz]
    by_cases hzt : t ≤ z
    · have hza : z ∉ Set.Icc a b := fun h => hz ⟨hzt, h.2⟩
      rw [Set.indicator_of_notMem hza]
    · by_cases hza : z ∈ Set.Icc a b
      · rw [Set.indicator_of_mem hza, ite_eq_right hzt]
      · rw [Set.indicator_of_notMem hza]

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.intervalIntegral_secondDeriv_mul_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory

/-- **Second-order Taylor formula with a vanishing lower end.**

If `ρ` is `C³` on `ℝ` and vanishes in a neighbourhood of `a`, then the triangular weighted
second derivative of `ρ` integrates back to `ρ z`:
```
∫_a^z ρ''(t) (z - t) dt = ρ z .
```
This is the fundamental theorem of calculus applied to the primitive `F t = ρ'(t)(z-t) + ρ(t)`,
whose derivative is exactly `ρ''(t)(z-t)`: the two extra terms `-ρ'(t) + ρ'(t)` cancel.  The
boundary terms at `a` vanish because `ρ` is identically zero near `a`, hence so are `ρ a` and
`ρ' a`; the boundary term at `z` vanishes because of the factor `(z - t)`. -/
theorem intervalIntegral_secondDeriv_mul_sub {a z : ℝ} {ρ : ℝ → ℝ} (haz : a ≤ z)
    (hρ : ContDiff ℝ 3 ρ) (hρa : ρ =ᶠ[nhds a] 0) :
    (∫ t in a..z, deriv (deriv ρ) t * (z - t)) = ρ z := by
  -- The proof actually works for every `a`, `z` (`Set.uIcc` is symmetric); the hypothesis
  -- `haz` is kept only because the statement was requested in this form.
  have haz' : a ≤ z := haz
  -- `ρ` and its first derivative vanish at `a`.
  have hρa0 : ρ a = 0 := by simpa using hρa.eq_of_nhds
  have hdρa0 : deriv ρ a = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hρa]
    simp
  -- Smoothness of `ρ`, `ρ'` and `ρ''`.
  have hρ2 : ContDiff ℝ 2 ρ := hρ.of_le (by norm_num)
  have hdρ_diff : Differentiable ℝ (deriv ρ) := ContDiff.differentiable_deriv_two hρ2
  have hρ_diff : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv ρ) := hρ2.deriv'
  have h2d : Continuous (deriv (deriv ρ)) := hd1.continuous_deriv (by norm_num)
  -- The primitive `F t = ρ'(t)(z-t) + ρ(t)` has derivative `ρ''(t)(z-t)`.
  have hderiv : ∀ x ∈ Set.uIcc a z,
      HasDerivAt ((deriv ρ) * (fun t => z - t) + ρ) (deriv (deriv ρ) x * (z - x)) x := by
    intro x _
    have hx' := (((hdρ_diff x).hasDerivAt).mul ((hasDerivAt_id x).const_sub z)).add
      ((hρ_diff x).hasDerivAt)
    have hv : deriv (deriv ρ) x * (z - x) + deriv ρ x * (-1) + deriv ρ x
        = deriv (deriv ρ) x * (z - x) := by ring
    simpa [hv] using hx'
  -- The integrand is continuous, hence interval integrable.
  have hint : IntervalIntegrable (fun t => deriv (deriv ρ) t * (z - t)) volume a z :=
    (h2d.mul (continuous_const.sub continuous_id)).intervalIntegrable a z
  -- Fundamental theorem of calculus, then evaluate the boundary terms.
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc ∫ t in a..z, deriv (deriv ρ) t * (z - t)
      = ((deriv ρ) * (fun t => z - t) + ρ) z - ((deriv ρ) * (fun t => z - t) + ρ) a := hmain
    _ = ρ z := by simp only [Pi.add_apply, Pi.mul_apply]; rw [hρa0, hdρa0]; ring

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.locallyIntegrableOn_mul_id =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

/-- Multiplying a function that is locally integrable on the open half-line `(0,∞)` by the
continuous function `z ↦ z` preserves local integrability there.  This is the instance
`g = id` of `MeasureTheory.LocallyIntegrableOn.continuousOn_mul`, applicable because `Set.Ioi 0`
is open, hence locally closed. -/
theorem locallyIntegrableOn_mul_id {W : ℝ → ℝ}
    (hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0)) :
    MeasureTheory.LocallyIntegrableOn (fun z => z * W z) (Set.Ioi 0) := by
  exact hW.continuousOn_mul continuousOn_id isOpen_Ioi.isLocallyClosed

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.not_integrable_exp_trig =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory Filter
open scoped BigOperators Topology

/-- Auxiliary: a nonnegative integrable function whose integrals over the consecutive
windows `[a n, a (n+1)]` are bounded below by a positive constant is not integrable. -/
private lemma not_integrable_of_window_lower {f : ℝ → ℝ} {I : ℝ}
    (hint : Integrable f) (hnonneg : ∀ t, 0 ≤ f t) (hI : 0 < I)
    (a : ℕ → ℝ) (ha0 : a 0 = 0)
    (hwin : ∀ n : ℕ, I ≤ ∫ x in (a n)..(a (n + 1)), f x) : False := by
  have htel : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, ∫ x in (a n)..(a (n + 1)), f x)
        = ∫ x in (0 : ℝ)..(a N), f x := by
    intro N
    induction N with
    | zero => simp [ha0]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact intervalIntegral.integral_add_adjacent_intervals
        hint.intervalIntegrable hint.intervalIntegrable
  have hpartial : ∀ N : ℕ, (N : ℝ) * I ≤ ∫ x in (0 : ℝ)..(a N), f x := by
    intro N
    calc (N : ℝ) * I = ∑ _n ∈ Finset.range N, I := by simp
      _ ≤ ∑ n ∈ Finset.range N, ∫ x in (a n)..(a (n + 1)), f x :=
          Finset.sum_le_sum (fun n _ => hwin n)
      _ = ∫ x in (0 : ℝ)..(a N), f x := htel N
  obtain ⟨N, hN⟩ := exists_nat_gt ((∫ x : ℝ, f x) / I)
  have hN' : (∫ x : ℝ, f x) < (N : ℝ) * I := by
    have h := mul_lt_mul_of_pos_right hN hI
    rwa [div_mul_cancel₀ _ (ne_of_gt hI)] at h
  have hbound : (N : ℝ) * I ≤ ∫ x : ℝ, f x := by
    refine le_trans (hpartial N) ?_
    rcases le_or_gt 0 (a N) with h | h
    · rw [intervalIntegral.integral_of_le h]
      exact setIntegral_le_integral hint (Eventually.of_forall hnonneg)
    · rw [intervalIntegral.integral_of_ge h.le]
      have h1 : 0 ≤ ∫ x in Set.Ioc (a N) 0, f x := integral_nonneg hnonneg
      have h2 : 0 ≤ ∫ x : ℝ, f x := integral_nonneg hnonneg
      linarith
  linarith

/-- The `c ≥ 0` case: a function `exp (c t) * (A cos (ωt) + B sin (ωt))²` with a genuinely
oscillating trigonometric factor is never integrable. -/
private lemma exp_trig_nonneg {c : ℝ} (hc : 0 ≤ c) {ω A B : ℝ} (hω : ω ≠ 0)
    (hint : Integrable (fun t : ℝ => Real.exp (c * t) *
      (A * Real.cos (ω * t) + B * Real.sin (ω * t)) ^ 2)) :
    A = 0 ∧ B = 0 := by
  by_contra hne
  have hAB : A ≠ 0 ∨ B ≠ 0 := not_and_or.mp hne
  set T : ℝ := 2 * Real.pi / |ω| with hTdef
  set ψ : ℝ → ℝ := fun t => A * Real.cos (ω * t) + B * Real.sin (ω * t) with hψdef
  set g : ℝ → ℝ := fun t => Real.exp (c * t) * ψ t ^ 2 with hgdef
  have hT : 0 < T := by
    rw [hTdef]
    exact div_pos (by positivity) (abs_pos.mpr hω)
  have hcontψ : Continuous ψ := by rw [hψdef]; fun_prop
  have hcontg : Continuous g := by rw [hgdef]; fun_prop
  have homegaT : ω * T = 2 * Real.pi ∨ ω * T = -(2 * Real.pi) := by
    rcases lt_trichotomy ω 0 with h | h | h
    · right; rw [hTdef, abs_of_neg h]; field_simp
    · exact absurd h hω
    · left; rw [hTdef, abs_of_pos h]; field_simp
  have hhalf : ω * (T / 2) = Real.pi ∨ ω * (T / 2) = -Real.pi := by
    rcases homegaT with h | h
    · left; rw [show ω * (T / 2) = (ω * T) / 2 by ring, h]; ring
    · right; rw [show ω * (T / 2) = (ω * T) / 2 by ring, h]; ring
  have hquarter : ω * (T / 4) = Real.pi / 2 ∨ ω * (T / 4) = -(Real.pi / 2) := by
    rcases homegaT with h | h
    · left; rw [show ω * (T / 4) = (ω * T) / 4 by ring, h]; ring
    · right; rw [show ω * (T / 4) = (ω * T) / 4 by ring, h]; ring
  have hper : Function.Periodic ψ T := by
    intro t
    show A * Real.cos (ω * (t + T)) + B * Real.sin (ω * (t + T))
       = A * Real.cos (ω * t) + B * Real.sin (ω * t)
    rcases homegaT with h | h
    · have harg : ω * (t + T) = ω * t + 2 * Real.pi := by rw [mul_add, h]
      rw [harg, Real.cos_add_two_pi, Real.sin_add_two_pi]
    · have harg : ω * (t + T) = ω * t - 2 * Real.pi := by rw [mul_add, h]; ring
      rw [harg, Real.cos_sub_two_pi, Real.sin_sub_two_pi]
  have hpern : ∀ n : ℕ, Function.Periodic ψ ((n : ℝ) * T) := by
    intro n
    simpa [nsmul_eq_mul] using hper.nsmul n
  have hshift : ∀ (n : ℕ) (t : ℝ),
      g (t + (n : ℝ) * T) = Real.exp (c * ((n : ℝ) * T)) * g t := by
    intro n t
    show Real.exp (c * (t + (n : ℝ) * T)) * ψ (t + (n : ℝ) * T) ^ 2
       = Real.exp (c * ((n : ℝ) * T)) * (Real.exp (c * t) * ψ t ^ 2)
    rw [hpern n t,
      show c * (t + (n : ℝ) * T) = c * ((n : ℝ) * T) + c * t by ring, Real.exp_add]
    ring
  have hintg : Integrable g := by
    simpa [hgdef, hψdef] using hint
  have hpoint : ∃ x₀ ∈ Set.Ioo (0 : ℝ) T, ψ x₀ ≠ 0 := by
    rcases hAB with hA | hB
    · refine ⟨T / 2, ⟨by linarith, by linarith⟩, ?_⟩
      show A * Real.cos (ω * (T / 2)) + B * Real.sin (ω * (T / 2)) ≠ 0
      rcases hhalf with h | h
      · rw [h, Real.cos_pi, Real.sin_pi]
        simpa using neg_ne_zero.mpr hA
      · rw [h, Real.cos_neg, Real.cos_pi, Real.sin_neg, Real.sin_pi]
        simpa using neg_ne_zero.mpr hA
    · refine ⟨T / 4, ⟨by linarith, by linarith⟩, ?_⟩
      show A * Real.cos (ω * (T / 4)) + B * Real.sin (ω * (T / 4)) ≠ 0
      rcases hquarter with h | h
      · rw [h, Real.cos_pi_div_two, Real.sin_pi_div_two]
        simpa using hB
      · rw [h, Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]
        simpa using neg_ne_zero.mpr hB
  obtain ⟨x₀, hx₀I, hx₀ne⟩ := hpoint
  have hI : 0 < ∫ x in (0 : ℝ)..T, g x := by
    have hmem : {t : ℝ | ψ t ≠ 0} ∈ 𝓝 x₀ := hcontψ.continuousAt.eventually_ne hx₀ne
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hmem
    set ρ : ℝ := min ε (min (x₀ / 2) ((T - x₀) / 2)) with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact lt_min hεpos (lt_min (by linarith [hx₀I.1]) (by linarith [hx₀I.2]))
    have hball : Metric.ball x₀ ρ ⊆ Function.support g ∩ Set.Ioc 0 T := by
      intro t ht
      have htx : |t - x₀| < ρ := by
        simpa [Metric.mem_ball, Real.dist_eq] using ht
      refine ⟨?_, ?_⟩
      · change g t ≠ 0
        have hne : ψ t ≠ 0 := hεsub (Metric.ball_subset_ball (min_le_left _ _) ht)
        exact mul_ne_zero (Real.exp_ne_zero _) (pow_ne_zero 2 hne)
      · rw [Set.mem_Ioc]
        constructor
        · have h2 : |t - x₀| < x₀ / 2 :=
            lt_of_lt_of_le htx (le_trans (min_le_right _ _) (min_le_left _ _))
          have := (abs_lt.mp h2).1
          linarith [hx₀I.1]
        · have h2 : |t - x₀| < (T - x₀) / 2 :=
            lt_of_lt_of_le htx (le_trans (min_le_right _ _) (min_le_right _ _))
          have := (abs_lt.mp h2).2
          linarith [hx₀I.2]
    have hmeas : 0 < volume (Function.support g ∩ Set.Ioc 0 T) :=
      lt_of_lt_of_le (Metric.measure_ball_pos volume x₀ hρpos) (measure_mono hball)
    exact (intervalIntegral.integral_pos_iff_support_of_nonneg_ae (f := g) (a := (0 : ℝ))
      (b := T) (μ := volume)
      (Eventually.of_forall (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
      (hcontg.intervalIntegrable 0 T)).mpr ⟨hT, hmeas⟩
  have hwin : ∀ n : ℕ,
      (∫ x in (0 : ℝ)..T, g x) ≤ ∫ x in ((n : ℝ) * T)..((↑(n + 1) : ℝ) * T), g x := by
    intro n
    have hsub : ∫ x in ((n : ℝ) * T)..((↑(n + 1) : ℝ) * T), g x
        = ∫ x in (0 : ℝ)..T, g (x + (n : ℝ) * T) := by
      have key := intervalIntegral.integral_comp_add_right (f := g) (a := (0 : ℝ)) (b := T)
        ((n : ℝ) * T)
      rw [zero_add] at key
      rw [show T + (n : ℝ) * T = (↑(n + 1) : ℝ) * T by push_cast; ring] at key
      exact key.symm
    rw [hsub]
    simp only [hshift n]
    rw [intervalIntegral.integral_const_mul]
    exact le_mul_of_one_le_left hI.le (Real.one_le_exp (by positivity))
  exact not_integrable_of_window_lower hintg
    (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) hI
    (fun n : ℕ => (n : ℝ) * T) (by simp) hwin

theorem not_integrable_exp_trig {c ω A B : ℝ} (hω : ω ≠ 0)
    (hint : MeasureTheory.Integrable
      (fun t : ℝ => Real.exp (c * t) * (A * Real.cos (ω * t) + B * Real.sin (ω * t)) ^ 2)) :
    A = 0 ∧ B = 0 := by
  rcases le_or_gt 0 c with hc | hc
  · exact exp_trig_nonneg hc hω hint
  · have hcomp : MeasureTheory.Integrable (fun t : ℝ =>
        Real.exp (c * (-t)) * (A * Real.cos (ω * (-t)) + B * Real.sin (ω * (-t))) ^ 2) :=
      hint.comp_neg
    have hfun : (fun t : ℝ => Real.exp (c * (-t)) *
          (A * Real.cos (ω * (-t)) + B * Real.sin (ω * (-t))) ^ 2)
        = fun t : ℝ => Real.exp ((-c) * t) *
          (A * Real.cos (ω * t) + (-B) * Real.sin (ω * t)) ^ 2 := by
      funext t
      rw [show c * -t = (-c) * t by ring, show ω * -t = -(ω * t) by ring,
        Real.cos_neg, Real.sin_neg]
      ring
    have hint' : MeasureTheory.Integrable (fun t : ℝ => Real.exp ((-c) * t) *
        (A * Real.cos (ω * t) + (-B) * Real.sin (ω * t)) ^ 2) := by
      rw [← hfun]
      exact hcomp
    have hres := exp_trig_nonneg (by linarith : (0 : ℝ) ≤ -c) hω hint'
    exact ⟨hres.1, neg_eq_zero.mp hres.2⟩

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.not_integrable_poly_exp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory

/-- If a real function is bounded below by a positive constant `ε` on a half-line
`[a, ∞)`, it cannot be integrable: the set `{t | ε ≤ g t}` then contains `Ici a`,
which has infinite measure, contradicting `Integrable.measure_ge_lt_top`. -/
lemma not_integrable_of_forall_ge_atTop {g : ℝ → ℝ} {ε a : ℝ} (hε : 0 < ε)
    (h : ∀ t, a ≤ t → ε ≤ g t) : ¬ MeasureTheory.Integrable g := by
  intro hg
  have hfin : volume {t : ℝ | ε ≤ g t} < ⊤ := hg.measure_ge_lt_top hε
  have hle : volume (Set.Ici a) ≤ volume {t : ℝ | ε ≤ g t} :=
    MeasureTheory.measure_mono fun t ht => h t ht
  rw [Real.volume_Ici] at hle
  exact absurd hle (not_le.mpr hfin)

/-- Same statement on a half-line `(-∞, a]`, obtained by reflecting `t ↦ -t`
(Lebesgue measure on `ℝ` is invariant under negation). -/
lemma not_integrable_of_forall_ge_atBot {g : ℝ → ℝ} {ε a : ℝ} (hε : 0 < ε)
    (h : ∀ t, t ≤ a → ε ≤ g t) : ¬ MeasureTheory.Integrable g := by
  intro hg
  have hg' : MeasureTheory.Integrable (fun t : ℝ => g (-t)) := hg.comp_neg
  exact not_integrable_of_forall_ge_atTop (g := fun t : ℝ => g (-t)) (ε := ε) (a := -a) hε
    (fun t ht => by simpa using h (-t) (by linarith)) hg'

/-- For `c2 ≠ 0` the affine function `c1 + c2 * t` has absolute value at least `1`
as soon as `|t|` is large enough. -/
lemma exists_abs_ge_one_of_ne_zero {c1 c2 : ℝ} (hc2 : c2 ≠ 0) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ t : ℝ, a ≤ |t| → (1 : ℝ) ≤ |c1 + c2 * t| := by
  have hc2pos : 0 < |c2| := abs_pos.mpr hc2
  refine ⟨(|c1| + 1) / |c2|, by positivity, fun t ht => ?_⟩
  have ht' : |c1| + 1 ≤ |t| * |c2| := (div_le_iff₀ hc2pos).mp ht
  have h3 : |c1| + 1 ≤ |c2 * t| := by
    rw [abs_mul]
    calc |c1| + 1 ≤ |t| * |c2| := ht'
      _ = |c2| * |t| := mul_comm _ _
  have h4 := abs_sub_abs_le_abs_sub (c2 * t) (-c1)
  rw [abs_neg, sub_neg_eq_add] at h4
  have hcomm : |c1 + c2 * t| = |c2 * t + c1| := by rw [add_comm]
  rw [hcomm]
  linarith

theorem not_integrable_poly_exp {r c1 c2 : ℝ}
    (hint : MeasureTheory.Integrable (fun t : ℝ => ((c1 + c2 * t) * Real.exp (r * t)) ^ 2)) :
    c1 = 0 ∧ c2 = 0 := by
  by_contra hcon
  have hcon' : c1 ≠ 0 ∨ c2 ≠ 0 := not_and_or.mp hcon
  have hg : ¬ MeasureTheory.Integrable
      (fun t : ℝ => ((c1 + c2 * t) * Real.exp (r * t)) ^ 2) := by
    by_cases hr : 0 ≤ r
    · -- `r ≥ 0`: look at `t → +∞`
      rcases eq_or_ne c2 0 with hc2 | hc2
      · -- `c2 = 0`, `c1 ≠ 0`: `g t = c1^2 * exp (2 r t) ≥ c1^2` for `t ≥ 0`
        have hc1 : c1 ≠ 0 := by
          rcases hcon' with h | h
          · exact h
          · exact (h hc2).elim
        refine not_integrable_of_forall_ge_atTop
          (g := fun t : ℝ => ((c1 + c2 * t) * Real.exp (r * t)) ^ 2)
          (ε := c1 ^ 2) (a := 0) (sq_pos_of_ne_zero hc1) ?_
        intro t ht
        have hexp : 1 ≤ Real.exp (r * t) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonneg hr ht)
        have hrew : ((c1 + c2 * t) * Real.exp (r * t)) ^ 2
            = c1 ^ 2 * (Real.exp (r * t)) ^ 2 := by
          rw [hc2]; ring
        rw [hrew]
        have h2 : 1 ≤ (Real.exp (r * t)) ^ 2 := by
          nlinarith [hexp, Real.exp_pos (r * t)]
        nlinarith [sq_nonneg c1]
      · -- `c2 ≠ 0`, `r ≥ 0`
        obtain ⟨a, ha0, ha⟩ := exists_abs_ge_one_of_ne_zero hc2
        refine not_integrable_of_forall_ge_atTop
          (g := fun t : ℝ => ((c1 + c2 * t) * Real.exp (r * t)) ^ 2)
          (ε := 1) (a := a) one_pos ?_
        intro t ht
        have ht0 : 0 ≤ t := le_trans ha0 ht
        have habs : 1 ≤ |c1 + c2 * t| := ha t (by rw [abs_of_nonneg ht0]; exact ht)
        have hexp : 1 ≤ Real.exp (r * t) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonneg hr ht0)
        have hmul : 1 ≤ |(c1 + c2 * t) * Real.exp (r * t)| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos (r * t))]
          exact one_le_mul_of_one_le_of_one_le habs hexp
        calc (1 : ℝ) = 1 ^ 2 := by ring
          _ ≤ |(c1 + c2 * t) * Real.exp (r * t)| ^ 2 := by
              nlinarith [hmul, abs_nonneg ((c1 + c2 * t) * Real.exp (r * t))]
          _ = ((c1 + c2 * t) * Real.exp (r * t)) ^ 2 := by rw [sq_abs]
    · -- `r < 0`: look at `t → -∞`
      have hr' : r < 0 := not_le.mp hr
      rcases eq_or_ne c2 0 with hc2 | hc2
      · -- `c2 = 0`, `c1 ≠ 0`: `g t = c1^2 * exp (2 r t) ≥ c1^2` for `t ≤ 0`
        have hc1 : c1 ≠ 0 := by
          rcases hcon' with h | h
          · exact h
          · exact (h hc2).elim
        refine not_integrable_of_forall_ge_atBot
          (g := fun t : ℝ => ((c1 + c2 * t) * Real.exp (r * t)) ^ 2)
          (ε := c1 ^ 2) (a := 0) (sq_pos_of_ne_zero hc1) ?_
        intro t ht
        have hexp : 1 ≤ Real.exp (r * t) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonneg_of_nonpos_of_nonpos hr'.le ht)
        have hrew : ((c1 + c2 * t) * Real.exp (r * t)) ^ 2
            = c1 ^ 2 * (Real.exp (r * t)) ^ 2 := by
          rw [hc2]; ring
        rw [hrew]
        have h2 : 1 ≤ (Real.exp (r * t)) ^ 2 := by
          nlinarith [hexp, Real.exp_pos (r * t)]
        nlinarith [sq_nonneg c1]
      · -- `c2 ≠ 0`, `r < 0`
        obtain ⟨a, ha0, ha⟩ := exists_abs_ge_one_of_ne_zero hc2
        refine not_integrable_of_forall_ge_atBot
          (g := fun t : ℝ => ((c1 + c2 * t) * Real.exp (r * t)) ^ 2)
          (ε := 1) (a := -a) one_pos ?_
        intro t ht
        have ht0 : t ≤ 0 := by linarith
        have hleabs : a ≤ |t| := by rw [abs_of_nonpos ht0]; linarith
        have habs : 1 ≤ |c1 + c2 * t| := ha t hleabs
        have hexp : 1 ≤ Real.exp (r * t) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonneg_of_nonpos_of_nonpos hr'.le ht0)
        have hmul : 1 ≤ |(c1 + c2 * t) * Real.exp (r * t)| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos (r * t))]
          exact one_le_mul_of_one_le_of_one_le habs hexp
        calc (1 : ℝ) = 1 ^ 2 := by ring
          _ ≤ |(c1 + c2 * t) * Real.exp (r * t)| ^ 2 := by
              nlinarith [hmul, abs_nonneg ((c1 + c2 * t) * Real.exp (r * t))]
          _ = ((c1 + c2 * t) * Real.exp (r * t)) ^ 2 := by rw [sq_abs]
  exact hg hint

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.not_integrable_two_exp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

/-!
# An integrable (square of a) two-exponential combination must be identically zero

We prove

`not_integrable_two_exp` : if `r2 < r1` and `t ↦ (c1 * exp (r1 * t) + c2 * exp (r2 * t)) ^ 2`
is integrable on `ℝ`, then `c1 = 0` and `c2 = 0`.

The mathematical content is purely growth: a nonzero exponential coefficient forces a bound
`≥ c > 0` of the integrand on a half-line, and an integrable function cannot dominate a
positive constant on a set of infinite measure.  The two halves of `ℝ` are handled by the two
elementary "tail" lemmas `not_eventually_ge_const` and `not_eventually_ge_const_atBot`; the
asymptotic lower bounds at `±∞` are extracted from `exp ((r2 - r1) * t) → 0` (respectively
`exp ((r1 - r2) * t) → 0` at `-∞`).
-/

/-- An integrable function cannot dominate a positive constant on a half-line `[T, ∞)`. -/
lemma not_eventually_ge_const {G : ℝ → ℝ} (hint : MeasureTheory.Integrable G) :
    ¬ (∃ c : ℝ, 0 < c ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t → c ≤ G t) := by
  rintro ⟨c, hc, T, hT⟩
  have hG : MeasureTheory.Integrable G (MeasureTheory.volume.restrict (Set.Ioi T)) :=
    hint.integrableOn
  have hae : ∀ᵐ a ∂(MeasureTheory.volume.restrict (Set.Ioi T)), ‖(c : ℝ)‖ ≤ G a := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with a ha
    rw [Real.norm_eq_abs, abs_of_pos hc]
    exact hT a (le_of_lt ha)
  have hconst : MeasureTheory.Integrable (fun _ : ℝ => c)
      (MeasureTheory.volume.restrict (Set.Ioi T)) :=
    MeasureTheory.Integrable.mono' hG measurable_const.aestronglyMeasurable hae
  have hkey := (MeasureTheory.integrableOn_const_iff (C := c) (s := Set.Ioi T)
      (μ := MeasureTheory.volume)).mp hconst
  rcases hkey with h0 | hfin
  · exact hc.ne' (enorm_eq_zero.mp h0)
  · rw [Real.volume_Ioi] at hfin
    exact lt_irrefl _ hfin

/-- An integrable function cannot dominate a positive constant on a half-line `(-∞, S]`. -/
lemma not_eventually_ge_const_atBot {G : ℝ → ℝ} (hint : MeasureTheory.Integrable G) :
    ¬ (∃ c : ℝ, 0 < c ∧ ∃ S : ℝ, ∀ t : ℝ, t ≤ S → c ≤ G t) := by
  rintro ⟨c, hc, S, hS⟩
  have hG : MeasureTheory.Integrable G (MeasureTheory.volume.restrict (Set.Iic S)) :=
    hint.integrableOn
  have hae : ∀ᵐ a ∂(MeasureTheory.volume.restrict (Set.Iic S)), ‖(c : ℝ)‖ ≤ G a := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Iic]
    filter_upwards with a ha
    rw [Real.norm_eq_abs, abs_of_pos hc]
    exact hS a ha
  have hconst : MeasureTheory.Integrable (fun _ : ℝ => c)
      (MeasureTheory.volume.restrict (Set.Iic S)) :=
    MeasureTheory.Integrable.mono' hG measurable_const.aestronglyMeasurable hae
  have hkey := (MeasureTheory.integrableOn_const_iff (C := c) (s := Set.Iic S)
      (μ := MeasureTheory.volume)).mp hconst
  rcases hkey with h0 | hfin
  · exact hc.ne' (enorm_eq_zero.mp h0)
  · rw [Real.volume_Iic] at hfin
    exact lt_irrefl _ hfin

/-- The exact factorisation of the two-term exponential combination. -/
private lemma two_exp_sq_eq (r1 r2 c1 c2 t : ℝ) :
    (c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t)) ^ 2
      = Real.exp (2 * r1 * t) * (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2 := by
  have h1 : Real.exp ((r2 - r1) * t) * Real.exp (r1 * t) = Real.exp (r2 * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : c2 * Real.exp (r2 * t) = Real.exp (r1 * t) * (c2 * Real.exp ((r2 - r1) * t)) := by
    rw [← h1]; ring
  have h3 : Real.exp (2 * r1 * t) = Real.exp (r1 * t) ^ 2 := by
    rw [show (2 : ℝ) * r1 * t = r1 * t + r1 * t from by ring, Real.exp_add]; ring
  rw [h2, h3]; ring

/-- At `+∞` the top exponential of a two-term combination dominates: if its coefficient `c1`
is nonzero and its rate `r1` is nonnegative, the square is bounded below by a positive
constant on a half-line. -/
private lemma eventually_ge_of_exp_tendsto_zero {r1 r2 c1 c2 : ℝ} (h : r2 < r1)
    (hc1 : c1 ≠ 0) (hr1 : 0 ≤ r1) :
    ∃ c : ℝ, 0 < c ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      c ≤ (c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t)) ^ 2 := by
  have hsub : r2 - r1 < 0 := by linarith
  have htend : Filter.Tendsto (fun t : ℝ => (r2 - r1) * t) Filter.atTop Filter.atBot :=
    (Filter.tendsto_const_mul_atBot_of_neg hsub).2 Filter.tendsto_id
  have hexp : Filter.Tendsto (fun t : ℝ => Real.exp ((r2 - r1) * t)) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp htend
  have hlin : Filter.Tendsto (fun t : ℝ => c1 + c2 * Real.exp ((r2 - r1) * t))
      Filter.atTop (nhds c1) := by
    have := (hexp.const_mul c2).const_add c1
    simpa using this
  have hsq : Filter.Tendsto (fun t : ℝ => (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2)
      Filter.atTop (nhds (c1 ^ 2)) := hlin.pow 2
  have hc1sq : (0 : ℝ) < c1 ^ 2 := sq_pos_of_ne_zero hc1
  have hev1 : ∀ᶠ t : ℝ in Filter.atTop,
      c1 ^ 2 / 2 < (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2 :=
    (tendsto_order.1 hsq).1 (c1 ^ 2 / 2) (by linarith)
  have hev2 : ∀ᶠ t : ℝ in Filter.atTop, (0 : ℝ) ≤ t := Filter.eventually_ge_atTop 0
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (hev1.and hev2)
  refine ⟨c1 ^ 2 / 2, by linarith, T, ?_⟩
  intro t ht
  obtain ⟨hb1, hb2⟩ := hT t ht
  have hge1 : (1 : ℝ) ≤ Real.exp (2 * r1 * t) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith)
  rw [two_exp_sq_eq]
  have hsqnn : 0 ≤ (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2 := sq_nonneg _
  have h2 : (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2
      ≤ Real.exp (2 * r1 * t) * (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2 := by
    calc (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2
        = 1 * (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2 := by ring
      _ ≤ Real.exp (2 * r1 * t) * (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2 :=
          mul_le_mul_of_nonneg_right hge1 hsqnn
  linarith

/-- The `-∞` twin of `eventually_ge_of_exp_tendsto_zero`: if the *bottom* exponential
coefficient `c2` is nonzero and its rate `r2` is nonpositive, the square is bounded below by
a positive constant on a half-line at `-∞`. -/
private lemma eventually_ge_atBot_of_exp {r1 r2 c1 c2 : ℝ} (h : r2 < r1)
    (hc2 : c2 ≠ 0) (hr2 : r2 ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ S : ℝ, ∀ t : ℝ, t ≤ S →
      c ≤ (c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t)) ^ 2 := by
  obtain ⟨c, hc, T, hT⟩ := eventually_ge_of_exp_tendsto_zero (r1 := -r2) (r2 := -r1)
    (c1 := c2) (c2 := c1) (by linarith) hc2 (by linarith)
  refine ⟨c, hc, -T, ?_⟩
  intro t ht
  have ht' : T ≤ -t := by linarith
  have h := hT (-t) ht'
  have heq : (c2 * Real.exp ((-r2) * (-t)) + c1 * Real.exp ((-r1) * (-t))) ^ 2
      = (c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t)) ^ 2 := by
    rw [neg_mul_neg, neg_mul_neg]; ring
  rw [heq] at h
  exact h

/-- A single nonzero exponential term has a non-integrable square over `ℝ`. -/
lemma single_exp_not_integrable {c r : ℝ} (hc : c ≠ 0) :
    ¬ MeasureTheory.Integrable (fun t : ℝ => (c * Real.exp (r * t)) ^ 2) := by
  intro hint
  have hc2 : (0 : ℝ) < c ^ 2 := sq_pos_of_ne_zero hc
  rcases le_or_gt 0 r with hr | hr
  · refine not_eventually_ge_const hint ⟨c ^ 2, hc2, 0, ?_⟩
    intro t ht
    have he : (1 : ℝ) ≤ Real.exp (r * t) := Real.one_le_exp (by nlinarith)
    have hs : (1 : ℝ) ≤ (Real.exp (r * t)) ^ 2 := one_le_pow₀ he
    calc c ^ 2 = c ^ 2 * 1 := by ring
      _ ≤ c ^ 2 * (Real.exp (r * t)) ^ 2 := mul_le_mul_of_nonneg_left hs (sq_nonneg c)
      _ = (c * Real.exp (r * t)) ^ 2 := by ring
  · refine not_eventually_ge_const_atBot hint ⟨c ^ 2, hc2, 0, ?_⟩
    intro t ht
    have he : (1 : ℝ) ≤ Real.exp (r * t) := Real.one_le_exp (by nlinarith)
    have hs : (1 : ℝ) ≤ (Real.exp (r * t)) ^ 2 := one_le_pow₀ he
    calc c ^ 2 = c ^ 2 * 1 := by ring
      _ ≤ c ^ 2 * (Real.exp (r * t)) ^ 2 := mul_le_mul_of_nonneg_left hs (sq_nonneg c)
      _ = (c * Real.exp (r * t)) ^ 2 := by ring

theorem not_integrable_two_exp {r1 r2 c1 c2 : ℝ} (h : r2 < r1)
    (hint : MeasureTheory.Integrable (fun t : ℝ => (c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t)) ^ 2)) :
    c1 = 0 ∧ c2 = 0 := by
  by_cases hc1 : c1 = 0
  · -- a single (bottom) exponential remains
    have hc2 : c2 = 0 := by
      by_contra hc2ne
      exact single_exp_not_integrable hc2ne (by simpa [hc1] using hint)
    exact ⟨hc1, hc2⟩
  · exfalso
    -- `+∞` forces `r1 < 0`
    have hr1 : r1 < 0 := by
      by_contra hlt
      exact not_eventually_ge_const hint
        (eventually_ge_of_exp_tendsto_zero h hc1 (not_lt.mp hlt))
    -- then `c2 ≠ 0` would force `0 < r2`, contradicting `r2 < r1 < 0`
    have hc2 : c2 = 0 := by
      by_contra hc2ne
      have hpos : 0 < r2 := by
        by_contra hle
        exact not_eventually_ge_const_atBot hint
          (eventually_ge_atBot_of_exp h hc2ne (not_lt.mp hle))
      linarith
    exact single_exp_not_integrable hc1 (by simpa [hc2] using hint)

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.ode_rep_distinct =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.FTS.StrongEps.EComparison

/-- `deriv (fun s => exp (c * s)) t = c * exp (c * t)`. -/
private lemma hasDerivAt_exp_const_mul (c t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (c * s)) (c * Real.exp (c * t)) t := by
  have hlin : HasDerivAt (fun s : ℝ => c * s) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have h := hlin.exp
  rwa [show Real.exp (c * t) * c = c * Real.exp (c * t) by ring] at h

/-- A function satisfying `f' = c * f` is `t ↦ f 0 * exp (c * t)`. -/
private lemma eq_exp_const_mul_of_deriv_eq {c : ℝ} {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (h : ∀ t, deriv f t = c * f t) (t : ℝ) : f t = f 0 * Real.exp (c * t) := by
  have hgdiff : Differentiable ℝ (fun s : ℝ => f s * Real.exp ((-c) * s)) := by fun_prop
  have hg0 : ∀ s, deriv (fun x : ℝ => f x * Real.exp ((-c) * x)) s = 0 := by
    intro s
    have h1 : HasDerivAt (fun x : ℝ => Real.exp ((-c) * x)) ((-c) * Real.exp ((-c) * s)) s :=
      hasDerivAt_exp_const_mul (-c) s
    have h2 : HasDerivAt f (c * f s) s := by
      have hh := (hf.differentiableAt (x := s)).hasDerivAt
      rwa [h s] at hh
    have h3 : HasDerivAt (fun x : ℝ => f x * Real.exp ((-c) * x))
        (c * f s * Real.exp ((-c) * s) + f s * ((-c) * Real.exp ((-c) * s))) s := h2.mul h1
    rw [h3.deriv]
    ring
  have hgc := is_const_of_deriv_eq_zero hgdiff hg0 t 0
  simp only [mul_zero, Real.exp_zero, mul_one] at hgc
  have hexp : Real.exp ((-c) * t) * Real.exp (c * t) = 1 := by
    rw [← Real.exp_add, show (-c) * t + c * t = 0 by ring, Real.exp_zero]
  calc f t = f t * (Real.exp ((-c) * t) * Real.exp (c * t)) := by rw [hexp, mul_one]
    _ = (f t * Real.exp ((-c) * t)) * Real.exp (c * t) := by rw [mul_assoc]
    _ = f 0 * Real.exp (c * t) := by rw [hgc]

/-- Solutions of the second order equation `U'' + a U' + b U = 0` with characteristic
polynomial splitting into two *distinct* real roots `r1 ≠ r2`, `r1 + r2 = -a`, `r1 * r2 = b`,
are linear combinations of `exp (r1 * ·)` and `exp (r2 * ·)`.

Proof: `F := U * exp (-r1 * ·)` satisfies `F' = G` with
`G := exp (-r1 * ·) * (U' - r1 * U)`, and the equation gives `G' = (r2 - r1) * G`.  Hence
`G = G 0 * exp ((r2 - r1) * ·)` (by `eq_exp_const_mul_of_deriv_eq`), and then
`F - (G 0 / (r2 - r1)) * exp ((r2 - r1) * ·)` has vanishing derivative, i.e. is constant. -/
theorem ode_rep_distinct {a b r1 r2 : ℝ} (hs : r1 + r2 = -a) (hp : r1 * r2 = b) (hne : r1 ≠ r2)
    {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hode : ∀ t, deriv (deriv U) t + a * deriv U t + b * U t = 0) :
    ∃ c1 c2 : ℝ, ∀ t, U t = c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t) := by
  have hdU : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hdU' : Differentiable ℝ (deriv U) := hU.differentiable_deriv_two
  have ha : a = -(r1 + r2) := by linarith
  have hb : b = r1 * r2 := hp.symm
  have hne' : (r2 - r1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  -- `F' = G`
  have hFderiv : deriv (fun s : ℝ => U s * Real.exp ((-r1) * s))
      = fun s : ℝ => Real.exp ((-r1) * s) * (deriv U s - r1 * U s) := by
    funext t
    have h1 : HasDerivAt (fun x : ℝ => Real.exp ((-r1) * x)) ((-r1) * Real.exp ((-r1) * t)) t :=
      hasDerivAt_exp_const_mul (-r1) t
    have h2 : HasDerivAt U (deriv U t) t := (hdU.differentiableAt (x := t)).hasDerivAt
    have h3 : HasDerivAt (fun x : ℝ => U x * Real.exp ((-r1) * x))
        (deriv U t * Real.exp ((-r1) * t) + U t * ((-r1) * Real.exp ((-r1) * t))) t := h2.mul h1
    rw [h3.deriv]
    ring
  -- `G' = (r2 - r1) * G`
  have hGderiv : ∀ t, deriv (fun s : ℝ => Real.exp ((-r1) * s) * (deriv U s - r1 * U s)) t
      = (r2 - r1) * (Real.exp ((-r1) * t) * (deriv U t - r1 * U t)) := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ => Real.exp ((-r1) * x)) ((-r1) * Real.exp ((-r1) * t)) t :=
      hasDerivAt_exp_const_mul (-r1) t
    have h2 : HasDerivAt (fun x : ℝ => deriv U x - r1 * U x)
        (deriv (deriv U) t - r1 * deriv U t) t :=
      ((hdU'.differentiableAt (x := t)).hasDerivAt).sub
        (((hdU.differentiableAt (x := t)).hasDerivAt).const_mul r1)
    have h3 : HasDerivAt (fun x : ℝ => Real.exp ((-r1) * x) * (deriv U x - r1 * U x))
        (((-r1) * Real.exp ((-r1) * t)) * (deriv U t - r1 * U t)
          + Real.exp ((-r1) * t) * (deriv (deriv U) t - r1 * deriv U t)) t := h1.mul h2
    rw [h3.deriv]
    have hdd : deriv (deriv U) t = -(a * deriv U t + b * U t) := by
      have := hode t
      linarith
    rw [hdd, ha, hb]
    ring
  have hGdiff : Differentiable ℝ (fun s : ℝ => Real.exp ((-r1) * s) * (deriv U s - r1 * U s)) := by
    fun_prop
  have hGrep : ∀ t, Real.exp ((-r1) * t) * (deriv U t - r1 * U t)
      = (deriv U 0 - r1 * U 0) * Real.exp ((r2 - r1) * t) := by
    have h := eq_exp_const_mul_of_deriv_eq hGdiff hGderiv
    intro t
    have ht := h t
    simpa using ht
  set K : ℝ := (deriv U 0 - r1 * U 0) / (r2 - r1) with hK
  have hKmul : K * (r2 - r1) = deriv U 0 - r1 * U 0 := by
    rw [hK, div_mul_cancel₀ _ hne']
  have hFdiff : Differentiable ℝ (fun s : ℝ => U s * Real.exp ((-r1) * s)) := by fun_prop
  have hHdiff : Differentiable ℝ (fun s : ℝ => U s * Real.exp ((-r1) * s)
      - K * Real.exp ((r2 - r1) * s)) := by fun_prop
  have hHderiv : ∀ t, deriv (fun s : ℝ => U s * Real.exp ((-r1) * s)
      - K * Real.exp ((r2 - r1) * s)) t = 0 := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ => U x * Real.exp ((-r1) * x))
        (Real.exp ((-r1) * t) * (deriv U t - r1 * U t)) t := by
      have hh := (hFdiff.differentiableAt (x := t)).hasDerivAt
      rwa [hFderiv] at hh
    have h2 : HasDerivAt (fun x : ℝ => K * Real.exp ((r2 - r1) * x))
        (K * ((r2 - r1) * Real.exp ((r2 - r1) * t))) t :=
      (hasDerivAt_exp_const_mul (r2 - r1) t).const_mul K
    have h3 : HasDerivAt (fun x : ℝ => U x * Real.exp ((-r1) * x) - K * Real.exp ((r2 - r1) * x))
        (Real.exp ((-r1) * t) * (deriv U t - r1 * U t)
          - K * ((r2 - r1) * Real.exp ((r2 - r1) * t))) t := h1.sub h2
    rw [h3.deriv, hGrep t, ← mul_assoc, hKmul]
    ring
  have hHconst : ∀ t, U t * Real.exp ((-r1) * t) - K * Real.exp ((r2 - r1) * t) = U 0 - K := by
    intro t
    have h := is_const_of_deriv_eq_zero hHdiff hHderiv t 0
    simpa using h
  refine ⟨U 0 - K, K, ?_⟩
  intro t
  have h1 := hHconst t
  have hEt : Real.exp ((-r1) * t) * Real.exp (r1 * t) = 1 := by
    rw [← Real.exp_add, show (-r1) * t + r1 * t = 0 by ring, Real.exp_zero]
  have hEc : Real.exp ((r2 - r1) * t) * Real.exp (r1 * t) = Real.exp (r2 * t) := by
    rw [← Real.exp_add, show (r2 - r1) * t + r1 * t = r2 * t by ring]
  have h2 : U t * Real.exp ((-r1) * t) = (U 0 - K) + K * Real.exp ((r2 - r1) * t) := by linarith
  calc U t = U t * (Real.exp ((-r1) * t) * Real.exp (r1 * t)) := by rw [hEt, mul_one]
    _ = (U t * Real.exp ((-r1) * t)) * Real.exp (r1 * t) := by rw [mul_assoc]
    _ = ((U 0 - K) + K * Real.exp ((r2 - r1) * t)) * Real.exp (r1 * t) := by rw [h2]
    _ = (U 0 - K) * Real.exp (r1 * t) + K * Real.exp (r2 * t) := by
          rw [add_mul, mul_assoc, hEc]

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.ode_rep_double =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

/-- If `g` is `C²` on `ℝ` and has vanishing second derivative everywhere, then `g` is affine.

The proof is the two FTC steps `0 = ∫₀ᵗ g'' = g'(t) - g'(0)` (so `g'` is constant) and
`g(t) - g(0) = ∫₀ᵗ g' = t · g'(0)`. -/
lemma affine_of_deriv_deriv_eq_zero {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (h : ∀ t, deriv (deriv g) t = 0) :
    ∃ c1 c2 : ℝ, ∀ t, g t = c1 + c2 * t := by
  have hdg : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  have hg' : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hcont : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  -- First step: `deriv g` is constant, because `deriv (deriv g) ≡ 0`.
  have hstep1 : ∀ s, deriv g s = deriv g 0 := by
    intro s
    have hh : ∀ x ∈ Set.uIcc (0 : ℝ) s, HasDerivAt (deriv g) (deriv (deriv g) x) x :=
      fun x _ => (hdg x).hasDerivAt
    have hint : IntervalIntegrable (deriv (deriv g)) MeasureTheory.volume 0 s := by
      have hz : deriv (deriv g) = fun _ => (0 : ℝ) := funext h
      rw [hz]
      exact intervalIntegrable_const
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hh hint
    have hzero : (∫ x in (0 : ℝ)..s, deriv (deriv g) x) = 0 := by
      simp [h]
    linarith [hftc, hzero]
  refine ⟨g 0, deriv g 0, fun t => ?_⟩
  -- Second step: `g t - g 0 = ∫₀ᵗ g' = t · g'(0)`.
  have hstep2 : (∫ x in (0 : ℝ)..t, deriv g x) = g t - g 0 := by
    have hh : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt g (deriv g x) x :=
      fun x _ => (hg' x).hasDerivAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hh (hcont.intervalIntegrable 0 t)
  have hInt : (∫ x in (0 : ℝ)..t, deriv g x) = t * deriv g 0 := by
    calc (∫ x in (0 : ℝ)..t, deriv g x) = ∫ x in (0 : ℝ)..t, deriv g 0 := by
          apply intervalIntegral.integral_congr
          intro x _
          exact hstep1 x
      _ = t * deriv g 0 := by
          rw [intervalIntegral.integral_const]
          simp
  have h3 : g t = g 0 + t * deriv g 0 := by linarith [hstep2, hInt]
  rw [h3]
  ring

theorem ode_rep_double {a b r : ℝ} (ha : a = -2 * r) (hb : b = r ^ 2)
    {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hode : ∀ t, deriv (deriv U) t + a * deriv U t + b * U t = 0) :
    ∃ c1 c2 : ℝ, ∀ t, U t = (c1 + c2 * t) * Real.exp (r * t) := by
  -- The substitution `W t = U t · e^{-rt}` turns the double-root equation
  -- `U'' - 2r U' + r² U = 0` into `W'' = 0`.
  have hdU : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hdU' : Differentiable ℝ (deriv U) := hU.differentiable_deriv_two
  have hW : ContDiff ℝ 2 (fun t => U t * Real.exp (-(r * t))) := by fun_prop
  -- Explicit first derivative of `W`.
  have hderivW : deriv (fun t => U t * Real.exp (-(r * t)))
      = fun t => (deriv U t - r * U t) * Real.exp (-(r * t)) := by
    funext t
    show deriv (U * fun s => Real.exp (-(r * s))) t
        = (deriv U t - r * U t) * Real.exp (-(r * t))
    rw [deriv_mul (hdU t) (by fun_prop)]
    rw [deriv_exp (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => -(r * t)) t)]
    simp
    ring
  -- `W'' = e^{-rt} (U'' + a U' + b U) = 0`.
  have hW2 : ∀ t, deriv (deriv (fun t => U t * Real.exp (-(r * t)))) t = 0 := by
    intro t
    rw [hderivW]
    have hV : deriv (fun s => (deriv U s - r * U s) * Real.exp (-(r * s))) t
        = Real.exp (-(r * t))
          * (deriv (deriv U) t + (-2 * r) * deriv U t + r ^ 2 * U t) := by
      show deriv ((fun s => deriv U s - r * U s) * fun s => Real.exp (-(r * s))) t = _
      rw [deriv_mul (by fun_prop) (by fun_prop)]
      have hA : deriv (fun s => deriv U s - r * U s) t
          = deriv (deriv U) t - r * deriv U t := by
        show deriv ((deriv U) - fun s => r * U s) t = _
        rw [deriv_sub (hdU' t) (by fun_prop : DifferentiableAt ℝ (fun s => r * U s) t)]
        rw [deriv_const_mul r (hdU t)]
      rw [hA, deriv_exp (by fun_prop)]
      simp
      ring
    rw [hV]
    have hode' : deriv (deriv U) t + (-2 * r) * deriv U t + r ^ 2 * U t = 0 := by
      have ht := hode t
      rw [ha, hb] at ht
      exact ht
    rw [hode']
    ring
  obtain ⟨c1, c2, hc⟩ := affine_of_deriv_deriv_eq_zero hW hW2
  refine ⟨c1, c2, fun t => ?_⟩
  have hexp : Real.exp (-(r * t)) * Real.exp (r * t) = 1 := by
    rw [← Real.exp_add]
    have : -(r * t) + r * t = 0 := by ring
    rw [this, Real.exp_zero]
  have h2 : (c1 + c2 * t) * Real.exp (r * t) = U t := by
    rw [(hc t).symm, mul_assoc, hexp, mul_one]
  exact h2.symm

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.ode_rep_trig =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Solutions of `U'' + a U' + b U = 0` when the characteristic roots are complex

If `b - a²/4 = ω²` with `ω > 0`, the characteristic polynomial `X² + aX + b` of the ODE
`U'' + a U' + b U = 0` has the two conjugate complex roots `-a/2 ± iω`, so every `C²`
solution must have the form

`U t = exp (-(a t / 2)) (A cos (ω t) + B sin (ω t))`.

The proof here is elementary and avoids any ODE uniqueness theory: multiplying `U` by
`exp (a t / 2)` reduces the equation to the harmonic oscillator `V'' + ω² V = 0`, whose
"energy" `(V')² + ω² V²` is constant (its derivative is `2 V' (V'' + ω² V) = 0`).  Energy
zero then forces `V ≡ 0`, which gives uniqueness for two solutions with the same value and
derivative at `0`; a linear combination of `cos` and `sin` matching those two data is
constructed explicitly.

## Main result

* `Work.FTS.StrongEps.EComparison.ode_rep_trig`
-/

namespace Work.FTS.StrongEps.EComparison

/-- **Energy equality for the harmonic oscillator.**  If `Y'' + ω² Y = 0` on `ℝ` (with `Y`
twice differentiable in the sense that `deriv Y` is differentiable), then the energy
`(Y')² + ω² Y²` is constant. -/
lemma osc_energy_const {ω : ℝ} {Y : ℝ → ℝ} (hY1 : Differentiable ℝ Y)
    (hY2 : Differentiable ℝ (deriv Y)) (hode : ∀ t, deriv (deriv Y) t + ω ^ 2 * Y t = 0) :
    ∀ t, (deriv Y t) ^ 2 + ω ^ 2 * (Y t) ^ 2 = (deriv Y 0) ^ 2 + ω ^ 2 * (Y 0) ^ 2 := by
  have hdiff : Differentiable ℝ (fun t => (deriv Y t) ^ 2 + ω ^ 2 * (Y t) ^ 2) :=
    (hY2.pow 2).add ((hY1.pow 2).const_mul (ω ^ 2))
  have hzero : ∀ t, deriv (fun t => (deriv Y t) ^ 2 + ω ^ 2 * (Y t) ^ 2) t = 0 := by
    intro t
    have h1 : HasDerivAt (fun s => (deriv Y s) ^ 2) (2 * deriv Y t * deriv (deriv Y) t) t := by
      convert (hY2 t).hasDerivAt.pow 2 using 1
      ring
    have h2 : HasDerivAt (fun s => ω ^ 2 * (Y s) ^ 2) (ω ^ 2 * (2 * Y t * deriv Y t)) t := by
      convert ((hY1 t).hasDerivAt.pow 2).const_mul (ω ^ 2) using 1
      ring
    have h3 := h1.add h2
    convert h3.deriv using 1
    rw [show deriv (deriv Y) t = -(ω ^ 2 * Y t) by linarith [hode t]]
    ring
  intro t
  exact is_const_of_deriv_eq_zero hdiff hzero t 0

/-- **Vanishing from zero initial data.**  If `D'' + ω² D = 0` with `ω ≠ 0` and
`D 0 = D' 0 = 0`, then `D ≡ 0`.  (The two derivatives are supplied as functions `D1`, `D2`
realising `deriv D = D1` and `deriv D1 = D2`.) -/
lemma osc_eq_zero_of_ode {ω : ℝ} (hω : 0 < ω) {D D1 D2 : ℝ → ℝ}
    (h1 : ∀ t, HasDerivAt D (D1 t) t) (h2 : ∀ t, HasDerivAt D1 (D2 t) t)
    (hode : ∀ t, D2 t + ω ^ 2 * D t = 0) (h0 : D 0 = 0) (h0' : D1 0 = 0) :
    ∀ t, D t = 0 := by
  have hD1 : deriv D = D1 := funext fun t => (h1 t).deriv
  have h1' : deriv D1 = D2 := funext fun t => (h2 t).deriv
  have hDdiff : Differentiable ℝ D := fun t => (h1 t).differentiableAt
  have hD1diff : Differentiable ℝ (deriv D) := by
    rw [hD1]; exact fun t => (h2 t).differentiableAt
  have hD2 : deriv (deriv D) = D2 := by rw [hD1, h1']
  have henergy : ∀ t, (deriv D t) ^ 2 + ω ^ 2 * (D t) ^ 2 =
      (deriv D 0) ^ 2 + ω ^ 2 * (D 0) ^ 2 :=
    osc_energy_const hDdiff hD1diff (fun t => by rw [hD2]; exact hode t)
  have hzero0 : (deriv D 0) ^ 2 + ω ^ 2 * (D 0) ^ 2 = 0 := by
    have hz : deriv D 0 = 0 := by rw [hD1]; exact h0'
    rw [hz, h0]; norm_num
  intro t
  have h := henergy t
  rw [hzero0] at h
  have hz : ω ^ 2 * (D t) ^ 2 = 0 := by
    nlinarith [sq_nonneg (deriv D t), sq_nonneg (D t), sq_nonneg ω, hω]
  have hω2 : ω ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hω)
  have hDt2 : (D t) ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left hω2
  exact mul_self_eq_zero.mp (by simpa [pow_two] using hDt2)

/-- **Representation of a solution of `Y'' + ω² Y = 0`.**  The linear combination of `cos`
and `sin` that matches `Y` and `Y'` at `0` is `Y` itself. -/
lemma osc_eq_sin_cos_of_hasderiv {ω : ℝ} (hω : 0 < ω) {Y Y1 Y2 : ℝ → ℝ}
    (h1 : ∀ t, HasDerivAt Y (Y1 t) t) (h2 : ∀ t, HasDerivAt Y1 (Y2 t) t)
    (hode : ∀ t, Y2 t + ω ^ 2 * Y t = 0) :
    ∀ t, Y t = Y 0 * Real.cos (ω * t) + (Y1 0 / ω) * Real.sin (ω * t) := by
  let T : ℝ → ℝ := fun t => Y 0 * Real.cos (ω * t) + (Y1 0 / ω) * Real.sin (ω * t)
  let T1 : ℝ → ℝ := fun t => (Y 0 * (-ω)) * Real.sin (ω * t) + ((Y1 0 / ω) * ω) * Real.cos (ω * t)
  let T2 : ℝ → ℝ :=
    fun t => (Y 0 * (-ω)) * (Real.cos (ω * t) * ω) + ((Y1 0 / ω) * ω) * (-Real.sin (ω * t) * ω)
  have hT1 : ∀ t, HasDerivAt T (T1 t) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => ω * s) ω t := by simpa using (hasDerivAt_id t).const_mul ω
    have h := ((hlin.cos).const_mul (Y 0)).add ((hlin.sin).const_mul (Y1 0 / ω))
    convert h using 1
    ring
  have hT2 : ∀ t, HasDerivAt T1 (T2 t) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => ω * s) ω t := by simpa using (hasDerivAt_id t).const_mul ω
    exact ((hlin.sin).const_mul (Y 0 * (-ω))).add ((hlin.cos).const_mul ((Y1 0 / ω) * ω))
  have hTode : ∀ t, T2 t + ω ^ 2 * T t = 0 := by
    intro t; simp only [T, T2]; ring
  let D : ℝ → ℝ := fun t => Y t - T t
  let D1 : ℝ → ℝ := fun t => Y1 t - T1 t
  let D2 : ℝ → ℝ := fun t => Y2 t - T2 t
  have hD_has : ∀ t, HasDerivAt D (D1 t) t := fun t => (h1 t).sub (hT1 t)
  have hD1_has : ∀ t, HasDerivAt D1 (D2 t) t := fun t => (h2 t).sub (hT2 t)
  have hDode : ∀ t, D2 t + ω ^ 2 * D t = 0 := by
    intro t
    have hY := hode t
    have hT := hTode t
    simp only [D, D2]
    linarith
  have hD0 : D 0 = 0 := by
    simp only [D, T]
    norm_num
  have hD10 : D1 0 = 0 := by
    simp only [D1, T1, mul_zero, Real.sin_zero, Real.cos_zero, mul_one, mul_zero]
    rw [div_mul_cancel₀ _ (ne_of_gt hω)]
    ring
  have hzero := osc_eq_zero_of_ode hω hD_has hD1_has hDode hD0 hD10
  intro t
  have ht := hzero t
  simp only [D, T] at ht
  linarith

theorem ode_rep_trig {a b ω : ℝ} (hω : 0 < ω) (hb : b - a ^ 2 / 4 = ω ^ 2)
    {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hode : ∀ t, deriv (deriv U) t + a * deriv U t + b * U t = 0) :
    ∃ A B : ℝ, ∀ t, U t = Real.exp (-(a * t / 2)) * (A * Real.cos (ω * t) + B * Real.sin (ω * t)) := by
  have hU1 : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hU2 : Differentiable ℝ (deriv U) := hU.differentiable_deriv_two
  have hb' : a ^ 2 / 4 + ω ^ 2 = b := by linarith
  -- `V = exp (a·/2) · U` solves the harmonic oscillator equation with frequency `ω`
  let V : ℝ → ℝ := fun s => Real.exp (a * s / 2) * U s
  let V1 : ℝ → ℝ := fun s => Real.exp (a * s / 2) * (deriv U s + a / 2 * U s)
  let V2 : ℝ → ℝ :=
    fun s => Real.exp (a * s / 2) * (deriv (deriv U) s + a * deriv U s + a ^ 2 / 4 * U s)
  have hV1 : ∀ t, HasDerivAt V (V1 t) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => a * s / 2) (a / 2) t := by
      simpa using ((hasDerivAt_id t).const_mul a).div_const 2
    have h := (hlin.exp).mul (hU1 t).hasDerivAt
    convert h using 1
    ring
  have hV2 : ∀ t, HasDerivAt V1 (V2 t) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => a * s / 2) (a / 2) t := by
      simpa using ((hasDerivAt_id t).const_mul a).div_const 2
    have hW : HasDerivAt (fun s : ℝ => deriv U s + a / 2 * U s)
        (deriv (deriv U) t + a / 2 * deriv U t) t :=
      (hU2 t).hasDerivAt.add ((hU1 t).hasDerivAt.const_mul (a / 2))
    have h := (hlin.exp).mul hW
    convert h using 1
    ring
  have hVode : ∀ t, V2 t + ω ^ 2 * V t = 0 := by
    intro t
    have hb2 : deriv (deriv U) t + a * deriv U t + (a ^ 2 / 4 + ω ^ 2) * U t = 0 := by
      rw [hb']; exact hode t
    simp only [V, V2]
    rw [show Real.exp (a * t / 2) * (deriv (deriv U) t + a * deriv U t + a ^ 2 / 4 * U t)
        + ω ^ 2 * (Real.exp (a * t / 2) * U t)
        = Real.exp (a * t / 2) * (deriv (deriv U) t + a * deriv U t + (a ^ 2 / 4 + ω ^ 2) * U t)
        from by ring]
    rw [hb2, mul_zero]
  have htrig := osc_eq_sin_cos_of_hasderiv hω hV1 hV2 hVode
  -- read off the representation of `U` from the one of `V`
  refine ⟨Real.exp (a * 0 / 2) * U 0,
    (Real.exp (a * 0 / 2) * (deriv U 0 + a / 2 * U 0)) / ω, fun t => ?_⟩
  have ht : Real.exp (a * t / 2) * U t
      = (Real.exp (a * 0 / 2) * U 0) * Real.cos (ω * t)
        + ((Real.exp (a * 0 / 2) * (deriv U 0 + a / 2 * U 0)) / ω) * Real.sin (ω * t) :=
    htrig t
  have hexp : Real.exp (-(a * t / 2)) * Real.exp (a * t / 2) = 1 := by
    rw [← Real.exp_add, show -(a * t / 2) + a * t / 2 = 0 by ring, Real.exp_zero]
  rw [← ht, ← mul_assoc, hexp, one_mul]

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ConvDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

/-- The convolution `s' ↦ ∫ p, κ p * g (s' - p)` is differentiable at `s` with derivative
`∫ p, deriv κ p * g (s - p)`, for `κ` of class `C¹` with compact support and `g` merely locally
integrable: this is the one-variable case of `HasCompactSupport.hasDerivAt_convolution_left`
(the convolution with the bilinear operator `ContinuousLinearMap.mul ℝ ℝ`, whose defining
integral is exactly `∫ p, κ p * g (s' - p)`, since this is definitionally
`MeasureTheory.convolution_mul`). -/
theorem ConvDeriv {κ : ℝ → ℝ} (hκ : ContDiff ℝ 1 κ) (hκc : HasCompactSupport κ)
    {g : ℝ → ℝ} (hg : MeasureTheory.LocallyIntegrable g MeasureTheory.volume) (s : ℝ) :
    HasDerivAt (fun s' => ∫ p, κ p * g (s' - p))
      (∫ p, deriv κ p * g (s - p)) s := by
  have h : HasDerivAt (fun s' => ∫ p, κ p * g (s' - p)) (∫ p, deriv κ p * g (s - p)) s :=
    hκc.hasDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hκ hg s
  exact h

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ParamIntegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter
open scoped Topology

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

theorem ParamIntegral {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasure μ] {Φ : ℕ → ℝ → X → ℝ}
    (hmeas : ∀ k s, MeasureTheory.AEStronglyMeasurable (Φ k s) μ)
    (hderiv : ∀ k, ∀ᵐ x ∂μ, ∀ s : ℝ, HasDerivAt (fun s' => Φ k s' x) (Φ (k + 1) s x) s)
    (hbound : ∀ k s₀, ∃ B : X → ℝ, MeasureTheory.Integrable B μ ∧
      ∀ᵐ x ∂μ, ∀ s ∈ Set.Ioo (s₀ - 1) (s₀ + 1), |Φ k s x| ≤ B x)
    (m : ℕ) : ContDiff ℝ m (fun s => ∫ x, Φ 0 s x ∂μ) := by
  -- Each `Φ k s` is integrable, since it is dominated by the integrable `B` on a neighbourhood
  -- of `s` itself.
  have hInt : ∀ k s, MeasureTheory.Integrable (Φ k s) μ := by
    intro k s
    obtain ⟨B, hBint, hB⟩ := hbound k s
    refine hBint.mono' (hmeas k s) ?_
    filter_upwards [hB] with x hx
    simpa only [Real.norm_eq_abs] using hx s ⟨by linarith, by linarith⟩
  -- Differentiation under the integral sign: the derivative of `s ↦ ∫ x, Φ k s x ∂μ` is the
  -- integral of `Φ (k+1)`.
  have hd : ∀ k s, HasDerivAt (fun s => ∫ x, Φ k s x ∂μ) (∫ x, Φ (k + 1) s x ∂μ) s := by
    intro k s
    obtain ⟨B, hBint, hB⟩ := hbound (k + 1) s
    have hs : Set.Ioo (s - 1) (s + 1) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
    have hbnd : ∀ᵐ x ∂μ, ∀ y ∈ Set.Ioo (s - 1) (s + 1), ‖Φ (k + 1) y x‖ ≤ B x := by
      filter_upwards [hB] with x hx y hy
      simpa only [Real.norm_eq_abs] using hx y hy
    have hdiff : ∀ᵐ x ∂μ, ∀ y ∈ Set.Ioo (s - 1) (s + 1),
        HasDerivAt (fun y' => Φ k y' x) (Φ (k + 1) y x) y :=
      (hderiv k).mono fun x hx y _ => hx y
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (E := ℝ)
      hs (Filter.Eventually.of_forall fun y => hmeas k y) (hInt k s) (hmeas (k + 1) s)
      hbnd hBint hdiff).2
  -- Identification of all iterated derivatives of the integral.
  have hiter : ∀ k, iteratedDeriv k (fun s => ∫ x, Φ 0 s x ∂μ) = fun s => ∫ x, Φ k s x ∂μ := by
    intro k
    induction k with
    | zero => rw [iteratedDeriv_zero]
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      exact (hd n s).deriv
  rw [contDiff_nat_iff_iteratedDeriv]
  refine ⟨fun m' _ => ?_, fun m' _ => ?_⟩
  · rw [hiter m']
    exact Differentiable.continuous (f := fun s => ∫ x, Φ m' s x ∂μ)
      fun s => (hd m' s).differentiableAt
  · rw [hiter m']
    exact fun s => (hd m' s).differentiableAt

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.measurable_indicator_of_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

/-- The indicator of an open set, times a function which is continuous on that set, is Borel
measurable: on the open set `s` we may test measurability of `g` on open preimages (`s ∩ g ⁻¹' U`
is open by `ContinuousOn.isOpen_inter_preimage`), while off `s` the indicator is constantly `0`. -/
theorem measurable_indicator_of_continuousOn {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [BorelSpace α] {s : Set α} (hs : IsOpen s) {g : α → ℝ}
    (hg : ContinuousOn g s) : Measurable (Set.indicator s g) := by
  classical
  -- Borel measurability of a real-valued function may be checked on open preimages.
  refine measurable_of_isOpen fun U hU => ?_
  have hA : MeasurableSet (s ∩ g ⁻¹' U) := (hg.isOpen_inter_preimage hs hU).measurableSet
  by_cases h0 : (0 : ℝ) ∈ U
  · -- the fibre of `U` is `(s ∩ g ⁻¹' U) ∪ sᶜ`
    have hpre : (Set.indicator s g) ⁻¹' U = (s ∩ g ⁻¹' U) ∪ sᶜ := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx, h0]
    rw [hpre]
    exact hA.union hs.measurableSet.compl
  · -- the fibre of `U` is `s ∩ g ⁻¹' U`
    have hpre : (Set.indicator s g) ⁻¹' U = s ∩ g ⁻¹' U := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx, h0]
    rw [hpre]
    exact hA

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.aesm_of_integrable_mul_shift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux

open MeasureTheory Filter Set


end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.LeafD2.continuousOn_slab_of_lipschitz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.LeafD2

-- `hδ` and `hZ` are part of the requested statement but are not needed by the argument
-- (only the *local* data at the base point is used).
set_option linter.unusedVariables false

theorem continuousOn_slab_of_lipschitz {E : Type*} [NormedAddCommGroup E] {δ : ℝ} (hδ : 0 ≤ δ)
    {g : ℝ → ℝ × ℝ → E} {Z : Set (ℝ × ℝ)} (hZ : IsOpen Z)
    (hcont : ∀ τ ∈ Set.Icc 0 δ, ContinuousOn (g τ) Z)
    (hlip : ∀ q ∈ Z, ∃ K : ℝ, 0 ≤ K ∧ ∃ U : Set (ℝ × ℝ), IsOpen U ∧ q ∈ U ∧
      ∀ q' ∈ U, ∀ τ ∈ Set.Icc 0 δ, ∀ τ' ∈ Set.Icc 0 δ, ‖g τ q' - g τ' q'‖ ≤ K * |τ - τ'|) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => g p.2.2 (p.1, p.2.1))
      {p : ℝ × (ℝ × ℝ) | (p.1, p.2.1) ∈ Z ∧ p.2.2 ∈ Set.Icc 0 δ} := by
  -- The function is `p ↦ g p.2.2 (p.1, p.2.1)`.  At a base point `p` of the slab,
  -- it is continuous in the space variable `(p.1, p.2.1)` at the frozen time `p.2.2`
  -- (hypothesis `hcont`), and locally `τ`-Lipschitz with a constant valid on an open
  -- neighbourhood `U` of `(p.1, p.2.1)` (hypothesis `hlip`); an `ε/2`-argument closes
  -- the two pieces.
  intro p hp
  rw [Metric.continuousWithinAt_iff]
  intro e he
  obtain ⟨hZq, hτp⟩ := hp
  -- the local Lipschitz data at the space-time point `(p.1, p.2.1) ∈ Z`
  obtain ⟨K, hK0, U, hUopen, hqU, hlipU⟩ := hlip (p.1, p.2.1) hZq
  obtain ⟨r, hrpos, hrU⟩ := Metric.isOpen_iff.mp hUopen (p.1, p.2.1) hqU
  -- the per-slice continuity at the frozen time `p.2.2`
  have hcontq : ContinuousWithinAt (g p.2.2) Z (p.1, p.2.1) :=
    (hcont p.2.2 hτp) (p.1, p.2.1) hZq
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousWithinAt_iff.mp hcontq (e / 2) (by linarith)
  have hcpos : 0 < e / (2 * (K + 1)) := div_pos he (by linarith)
  refine ⟨min δ₁ (min r (e / (2 * (K + 1)))), lt_min hδ₁pos (lt_min hrpos hcpos), ?_⟩
  intro x hx hdist
  obtain ⟨hZx, hτx⟩ := hx
  -- the metric `dist` on `ℝ × (ℝ × ℝ)`, in coordinates
  have hxd : dist x p = max (dist x.1 p.1) (max (dist x.2.1 p.2.1) (dist x.2.2 p.2.2)) := by
    rw [Prod.dist_eq, Prod.dist_eq]
  have hle_inner : dist (x.1, x.2.1) (p.1, p.2.1) ≤ dist x p := by
    rw [hxd, Prod.dist_eq]
    exact max_le (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_right _ _))
  -- the time difference is small ...
  have hτsmall : dist x.2.2 p.2.2 < e / (2 * (K + 1)) := by
    have hle : dist x.2.2 p.2.2 ≤ dist x p := by
      rw [hxd]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact lt_of_le_of_lt hle
      (lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- ... the space difference is small ...
  have hspace : dist (x.1, x.2.1) (p.1, p.2.1) < δ₁ :=
    lt_of_le_of_lt hle_inner (lt_of_lt_of_le hdist (min_le_left _ _))
  -- ... and small enough that `(x.1, x.2.1)` lies in the Lipschitz neighbourhood
  have hUmem : (x.1, x.2.1) ∈ U := by
    refine hrU ?_
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hle_inner
      (lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_left _ _)))
  -- the frozen-slice continuity
  have hslice : dist (g p.2.2 (x.1, x.2.1)) (g p.2.2 (p.1, p.2.1)) < e / 2 :=
    hδ₁ hZx hspace
  -- the Lipschitz-in-`τ` piece
  have htime : dist (g x.2.2 (x.1, x.2.1)) (g p.2.2 (x.1, x.2.1)) < e / 2 := by
    rw [dist_eq_norm]
    have h1 : ‖g x.2.2 (x.1, x.2.1) - g p.2.2 (x.1, x.2.1)‖ ≤ K * |x.2.2 - p.2.2| :=
      hlipU (x.1, x.2.1) hUmem x.2.2 hτx p.2.2 hτp
    have h2 : |x.2.2 - p.2.2| < e / (2 * (K + 1)) := by
      rw [← Real.dist_eq]
      exact hτsmall
    refine lt_of_le_of_lt h1 ?_
    have h3 : K * |x.2.2 - p.2.2| ≤ K * (e / (2 * (K + 1))) :=
      mul_le_mul_of_nonneg_left h2.le hK0
    refine lt_of_le_of_lt h3 ?_
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (K + 1))]
    nlinarith [he]
  have htri := dist_triangle (g x.2.2 (x.1, x.2.1)) (g p.2.2 (x.1, x.2.1))
    (g p.2.2 (p.1, p.2.1))
  linarith

end Work.FTS.StrongEps.EpsE4Thr.LeafD2
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.RegSlab.continuousOn_intervalIntegral_slab_normed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.RegSlab

open Set MeasureTheory Filter
open scoped Topology

/-- The `σ`-slice of a function which is continuous on the slab `Z ×ˢ (Θ ×ˢ Icc 0 δ)` is
continuous on `Icc 0 δ`. -/
lemma continuousOn_slice_of_continuousOn_slab {E : Type*} [NormedAddCommGroup E]
    {Z Θ : Set ℝ} {δ : ℝ} {B : ℝ × ℝ × ℝ → E}
    (hB : ContinuousOn B (Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)))
    {z θ : ℝ} (hz : z ∈ Z) (hθ : θ ∈ Θ) :
    ContinuousOn (fun σ : ℝ => B (z, θ, σ)) (Icc (0 : ℝ) δ) := by
  refine hB.comp ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn)
    (fun σ hσ => ⟨hz, hθ, hσ⟩)

/-- `uIcc 0 τ₀ ⊆ Icc 0 δ` whenever `τ₀ ∈ Icc 0 δ`. -/
lemma uIcc_zero_subset_Icc {δ τ₀ : ℝ} (hτ₀ : τ₀ ∈ Icc (0 : ℝ) δ) :
    uIcc (0 : ℝ) τ₀ ⊆ Icc (0 : ℝ) δ :=
  uIcc_subset_Icc ⟨le_rfl, le_trans hτ₀.1 hτ₀.2⟩ hτ₀

/-- Replacing the last coordinate of `p` by a number closer to the last coordinate of `p₀` than
`p.2.2` cannot increase the distance to `p₀`. -/
lemma dist_replace_last_le {p p₀ : ℝ × ℝ × ℝ} {σ : ℝ}
    (h : dist σ p₀.2.2 ≤ dist p.2.2 p₀.2.2) :
    dist (p.1, (p.2.1, σ)) p₀ ≤ dist p p₀ := by
  simp only [Prod.dist_eq]
  exact max_le_max_left _ (max_le_max_left _ h)

/-- **Uniform control forced by continuity on the slab.**  If `B` is continuous on the slab
`Z ×ˢ (Θ ×ˢ Icc 0 δ)` then, near any point `(z₀, θ₀) ∈ Z × Θ`, the difference
`B (z, θ, σ) - B (z₀, θ₀, σ)` is small *uniformly* in `σ ∈ Icc 0 δ`.  (The compactness of the
last slice `Icc 0 δ` is what makes the bound uniform; the first two coordinates are arbitrary
subsets of `ℝ`.) -/
lemma slab_eventually_uniform {E : Type*} [NormedAddCommGroup E]
    {Z Θ : Set ℝ} {δ : ℝ} {B : ℝ × ℝ × ℝ → E}
    (hB : ContinuousOn B (Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)))
    {z₀ : ℝ} (hz₀ : z₀ ∈ Z) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Θ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℝ × ℝ in 𝓝[Z ×ˢ Θ] (z₀, θ₀),
      ∀ σ ∈ Icc (0 : ℝ) δ, dist (B (p.1, p.2, σ)) (B (z₀, θ₀, σ)) < ε := by
  haveI : CompactSpace ↥(Icc (0 : ℝ) δ) := isCompact_iff_compactSpace.mp isCompact_Icc
  let Φ : ↥(Z ×ˢ Θ) × ↥(Icc (0 : ℝ) δ) → E × E :=
    fun x => (B ((x.1 : ℝ × ℝ).1, ((x.1 : ℝ × ℝ).2, (x.2 : ℝ))), B (z₀, θ₀, (x.2 : ℝ)))
  have hΦcont : Continuous Φ := by
    have h1 : Continuous fun x : ↥(Z ×ˢ Θ) × ↥(Icc (0 : ℝ) δ) =>
        B ((x.1 : ℝ × ℝ).1, ((x.1 : ℝ × ℝ).2, (x.2 : ℝ))) :=
      hB.comp_continuous
        ((continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk
          ((continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).prodMk
            (continuous_subtype_val.comp continuous_snd)))
        (fun x => ⟨x.1.2.1, x.1.2.2, x.2.2⟩)
    have h2 : Continuous fun x : ↥(Z ×ˢ Θ) × ↥(Icc (0 : ℝ) δ) => B (z₀, θ₀, (x.2 : ℝ)) := by
      have hslice : ContinuousOn (fun σ : ℝ => B (z₀, θ₀, σ)) (Icc (0 : ℝ) δ) :=
        continuousOn_slice_of_continuousOn_slab hB hz₀ hθ₀
      exact hslice.comp_continuous (continuous_subtype_val.comp continuous_snd) (fun x => x.2.2)
    exact h1.prodMk h2
  have hTclosed : IsClosed {y : E × E | ε ≤ dist y.1 y.2} := by
    simpa using isClosed_le (continuous_const : Continuous fun _ : E × E => ε)
      (continuous_dist.comp continuous_id : Continuous fun y : E × E => dist y.1 y.2)
  have hT : IsClosed (Φ ⁻¹' {y : E × E | ε ≤ dist y.1 y.2}) := hTclosed.preimage hΦcont
  have hproj : IsClosed (Prod.fst '' (Φ ⁻¹' {y : E × E | ε ≤ dist y.1 y.2})) :=
    isClosedMap_fst_of_compactSpace (X := ↥(Z ×ˢ Θ)) (Y := ↥(Icc (0 : ℝ) δ)) _ hT
  have hnotmem : (⟨(z₀, θ₀), ⟨hz₀, hθ₀⟩⟩ : ↥(Z ×ˢ Θ)) ∉
      Prod.fst '' (Φ ⁻¹' {y : E × E | ε ≤ dist y.1 y.2}) := by
    rintro ⟨y, hy, hyfst⟩
    have h1 : (y.1 : ℝ × ℝ) = (z₀, θ₀) := by
      have := congrArg Subtype.val hyfst
      simpa using this
    have h2 : (Φ y).1 = (Φ y).2 := by
      dsimp only [Φ]
      rw [h1]
    have hy' : ε ≤ dist (Φ y).1 (Φ y).2 := hy
    rw [h2, dist_self] at hy'
    linarith
  have hcompl : (Prod.fst '' (Φ ⁻¹' {y : E × E | ε ≤ dist y.1 y.2}))ᶜ ∈
      𝓝 (⟨(z₀, θ₀), ⟨hz₀, hθ₀⟩⟩ : ↥(Z ×ˢ Θ)) :=
    hproj.isOpen_compl.mem_nhds hnotmem
  obtain ⟨u, hu, hsub⟩ :=
    (mem_nhds_subtype (Z ×ˢ Θ) ⟨(z₀, θ₀), ⟨hz₀, hθ₀⟩⟩
      ((Prod.fst '' (Φ ⁻¹' {y : E × E | ε ≤ dist y.1 y.2}))ᶜ)).mp hcompl
  filter_upwards [show u ∈ 𝓝[Z ×ˢ Θ] (z₀, θ₀) from nhdsWithin_le_nhds hu,
    self_mem_nhdsWithin] with p hp hpmem
  intro σ hσ
  have hq : (⟨p, hpmem⟩ : ↥(Z ×ˢ Θ)) ∉
      Prod.fst '' (Φ ⁻¹' {y : E × E | ε ≤ dist y.1 y.2}) := hsub hp
  have : ¬ (ε ≤ dist (B (p.1, p.2, σ)) (B (z₀, θ₀, σ))) := by
    intro hle
    apply hq
    exact ⟨(⟨p, hpmem⟩, ⟨σ, hσ⟩), hle, rfl⟩
  exact not_le.mp this

/-- Continuity of the interval integral in the first two variables only (fixed upper limit `τ₀`),
on the slab of parameters. -/
lemma continuousOn_intervalIntegral_fixed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Z Θ : Set ℝ} {δ τ₀ : ℝ} {B : ℝ × ℝ × ℝ → E}
    (hB : ContinuousOn B (Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ))) (hτ₀ : τ₀ ∈ Icc (0 : ℝ) δ) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ σ in (0 : ℝ)..τ₀, B (p.1, p.2, σ)) (Z ×ˢ Θ) := by
  intro p₀ hp₀
  obtain ⟨z₀, θ₀⟩ := p₀
  rcases hp₀ with ⟨hz₀, hθ₀⟩
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun p : ℝ × ℝ => fun σ : ℝ => B (p.1, p.2, σ))
    (bound := fun σ : ℝ => ‖B (z₀, θ₀, σ)‖ + 1) (a := 0) (b := τ₀) (s := Z ×ˢ Θ)
    ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact ((continuousOn_slice_of_continuousOn_slab hB hp.1 hp.2).mono
      (uIoc_subset_uIcc.trans (uIcc_zero_subset_Icc hτ₀))).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [slab_eventually_uniform hB hz₀ hθ₀ (ε := 1) one_pos] with p hp
    filter_upwards with σ hσ
    have h1 : σ ∈ Icc (0 : ℝ) δ := (uIoc_subset_uIcc.trans (uIcc_zero_subset_Icc hτ₀)) hσ
    have h2 : dist (B (p.1, p.2, σ)) (B (z₀, θ₀, σ)) < 1 := hp σ h1
    have h3 : ‖B (p.1, p.2, σ) - B (z₀, θ₀, σ)‖ < 1 := by
      rwa [dist_eq_norm] at h2
    calc ‖B (p.1, p.2, σ)‖
        ≤ ‖B (z₀, θ₀, σ)‖ + ‖B (p.1, p.2, σ) - B (z₀, θ₀, σ)‖ := by
          have := norm_add_le (B (z₀, θ₀, σ)) (B (p.1, p.2, σ) - B (z₀, θ₀, σ))
          simpa using this
      _ ≤ ‖B (z₀, θ₀, σ)‖ + 1 := by linarith
  · have hslice : ContinuousOn (fun σ : ℝ => ‖B (z₀, θ₀, σ)‖ + 1) (Icc (0 : ℝ) δ) :=
      (continuousOn_slice_of_continuousOn_slab hB hz₀ hθ₀).norm.add continuousOn_const
    exact (hslice.mono (uIcc_zero_subset_Icc hτ₀)).intervalIntegrable
  · filter_upwards with σ hσ
    have h1 : σ ∈ Icc (0 : ℝ) δ := (uIoc_subset_uIcc.trans (uIcc_zero_subset_Icc hτ₀)) hσ
    have hcont : ContinuousOn (fun x : ℝ × ℝ => B (x.1, x.2, σ)) (Z ×ˢ Θ) :=
      hB.comp
        ((continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn)
        (fun x hx => ⟨hx.1, hx.2, h1⟩)
    exact hcont.continuousWithinAt ⟨hz₀, hθ₀⟩

theorem continuousOn_intervalIntegral_slab_normed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Z Θ : Set ℝ} {δ : ℝ} {B : ℝ × ℝ × ℝ → E}
    (hB : ContinuousOn B (Z ×ˢ (Θ ×ˢ Set.Icc (0 : ℝ) δ))) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => ∫ σ in (0 : ℝ)..p.2.2, B (p.1, p.2.1, σ))
      (Z ×ˢ (Θ ×ˢ Set.Icc (0 : ℝ) δ)) := by
  intro p₀ hp₀
  obtain ⟨z₀, θ₀, τ₀⟩ := p₀
  rcases hp₀ with ⟨hz₀, hθ₀, hτ₀⟩
  -- the fixed part `(z,θ) ↦ ∫₀^{τ₀} B (z,θ,σ) dσ`
  have hfirst : ContinuousWithinAt
      (fun p : ℝ × ℝ × ℝ => ∫ σ in (0 : ℝ)..τ₀, B (p.1, p.2.1, σ))
      (Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)) (z₀, θ₀, τ₀) :=
    ((continuousOn_intervalIntegral_fixed hB hτ₀).comp
      ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn)
      (fun p hp => ⟨hp.1, hp.2.1⟩)).continuousWithinAt ⟨hz₀, hθ₀, hτ₀⟩
  -- the moving part `p ↦ ∫_{τ₀}^{p.2.2} B (p.1,p.2.1,σ) dσ` vanishes at `p₀`
  have hΨ : Tendsto (fun p : ℝ × ℝ × ℝ => ∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ))
      (𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀)) (𝓝 0) := by
    have hbound : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀),
        ‖∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ)‖ ≤ |p.2.2 - τ₀| * (‖B (z₀, θ₀, τ₀)‖ + 1) := by
      have hcont : ∀ᶠ x : ℝ × ℝ × ℝ in 𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀),
          ‖B x‖ ≤ ‖B (z₀, θ₀, τ₀)‖ + 1 := by
        have ht := (hB (z₀, θ₀, τ₀) ⟨hz₀, hθ₀, hτ₀⟩).tendsto.norm
        filter_upwards [ht.eventually_lt_const (lt_add_one _)] with x hx
        exact le_of_lt hx
      obtain ⟨u, hu, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hcont
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hu
      filter_upwards [show Metric.ball (z₀, θ₀, τ₀) (r / 2) ∈
          𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀) from
        nhdsWithin_le_nhds (Metric.ball_mem_nhds _ (by positivity)),
        self_mem_nhdsWithin] with p hpball hpS
      have hpdist : dist p (z₀, θ₀, τ₀) < r / 2 := by
        simpa [Metric.mem_ball] using hpball
      have hstep : ‖∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ)‖ ≤
          (‖B (z₀, θ₀, τ₀)‖ + 1) * |p.2.2 - τ₀| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun σ hσ => ?_)
        have hσIcc : σ ∈ Icc (0 : ℝ) δ := (uIoc_subset_uIcc.trans (uIcc_subset_Icc hτ₀ hpS.2.2)) hσ
        have hmemslab : (p.1, (p.2.1, σ)) ∈ Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ) :=
          ⟨hpS.1, hpS.2.1, hσIcc⟩
        have hσdist : dist σ τ₀ ≤ dist p.2.2 τ₀ := by
          rw [Real.dist_eq, Real.dist_eq]
          rcases (mem_uIcc.mp (uIoc_subset_uIcc hσ)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ - τ₀),
              abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.2.2 - τ₀)]
            linarith
          · rw [abs_of_nonpos (by linarith : σ - τ₀ ≤ 0),
              abs_of_nonpos (by linarith : p.2.2 - τ₀ ≤ 0)]
            linarith
        have hclose : dist (p.1, (p.2.1, σ)) (z₀, θ₀, τ₀) < r := by
          have := dist_replace_last_le (p := p) (p₀ := (z₀, θ₀, τ₀)) hσdist
          linarith
        exact hsub ⟨hball hclose, hmemslab⟩
      rw [mul_comm] at hstep
      exact hstep
    refine squeeze_zero_norm' hbound ?_
    have h2 : Tendsto (fun p : ℝ × ℝ × ℝ => p.2.2)
        (𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀)) (𝓝 τ₀) :=
      (continuous_snd.comp continuous_snd).tendsto (z₀, θ₀, τ₀) |>.mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun p : ℝ × ℝ × ℝ => |p.2.2 - τ₀| * (‖B (z₀, θ₀, τ₀)‖ + 1))
        (𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀)) (𝓝 0) := by
      have h5 : Tendsto (fun p : ℝ × ℝ × ℝ => p.2.2 - τ₀)
          (𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀)) (𝓝 0) := by
        simpa using h2.sub_const τ₀
      have h6 : Tendsto (fun p : ℝ × ℝ × ℝ => |p.2.2 - τ₀|)
          (𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀)) (𝓝 0) := by
        simpa using h5.abs
      simpa using h6.mul_const (‖B (z₀, θ₀, τ₀)‖ + 1)
    exact h3
  -- the value of the moving part at `p₀` is `0`
  have hΨc : ContinuousWithinAt (fun p : ℝ × ℝ × ℝ => ∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ))
      (Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)) (z₀, θ₀, τ₀) := by
    show Tendsto (fun p : ℝ × ℝ × ℝ => ∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ))
      (𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀))
      (𝓝 ((fun p : ℝ × ℝ × ℝ => ∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ)) (z₀, θ₀, τ₀)))
    rw [show (fun p : ℝ × ℝ × ℝ => ∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ)) (z₀, θ₀, τ₀) = 0
      from intervalIntegral.integral_same]
    exact hΨ
  -- split the integral at `τ₀`
  have hsplit : ∀ p ∈ Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ),
      (∫ σ in (0 : ℝ)..p.2.2, B (p.1, p.2.1, σ)) =
        (∫ σ in (0 : ℝ)..τ₀, B (p.1, p.2.1, σ)) + (∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ)) := by
    intro p hp
    have hslice : ContinuousOn (fun σ : ℝ => B (p.1, p.2.1, σ)) (Icc (0 : ℝ) δ) :=
      continuousOn_slice_of_continuousOn_slab hB hp.1 hp.2.1
    have h1 : IntervalIntegrable (fun σ : ℝ => B (p.1, p.2.1, σ)) volume 0 τ₀ :=
      (hslice.mono (uIcc_zero_subset_Icc hτ₀)).intervalIntegrable
    have h2 : IntervalIntegrable (fun σ : ℝ => B (p.1, p.2.1, σ)) volume τ₀ p.2.2 :=
      (hslice.mono (uIcc_subset_Icc hτ₀ hp.2.2)).intervalIntegrable
    exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
  have hgoal : ContinuousWithinAt
      (fun p : ℝ × ℝ × ℝ =>
        (∫ σ in (0 : ℝ)..τ₀, B (p.1, p.2.1, σ)) + (∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ)))
      (Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)) (z₀, θ₀, τ₀) := hfirst.add hΨc
  have heq : (fun p : ℝ × ℝ × ℝ => ∫ σ in (0 : ℝ)..p.2.2, B (p.1, p.2.1, σ)) =ᶠ[
      𝓝[Z ×ˢ (Θ ×ˢ Icc (0 : ℝ) δ)] (z₀, θ₀, τ₀)]
      (fun p : ℝ × ℝ × ℝ =>
        (∫ σ in (0 : ℝ)..τ₀, B (p.1, p.2.1, σ)) + (∫ σ in τ₀..p.2.2, B (p.1, p.2.1, σ))) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hsplit p hp
  have hval : (∫ σ in (0 : ℝ)..(z₀, θ₀, τ₀).2.2, B ((z₀, θ₀, τ₀).1, (z₀, θ₀, τ₀).2.1, σ)) =
      (∫ σ in (0 : ℝ)..τ₀, B (z₀, θ₀, σ)) + (∫ σ in τ₀..τ₀, B (z₀, θ₀, σ)) :=
    hsplit (z₀, θ₀, τ₀) ⟨hz₀, hθ₀, hτ₀⟩
  exact hgoal.congr_of_eventuallyEq heq hval

end Work.FTS.StrongEps.EpsE4Thr.RegSlab
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.aemeasurable_slice_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Work.FTS.StrongEps.EpsE4Thr


end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.cs_diag =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr



end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.energy_barrier =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr


end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.sq_integral_interval_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open MeasureTheory

/-- **Cauchy–Schwarz on an interval.** For `a ≤ b` and `f²` interval integrable on `a..b`,
the square of the integral of `f` is at most `(b - a)` times the integral of `f²`:
`(∫_a^b f)² ≤ (b - a) ∫_a^b f²`.

The proof splits on whether `f` is itself interval integrable. If it is not, the interval
integral of `f` is `0` (`intervalIntegral.integral_undef`) and the right-hand side is
nonnegative. If it is, integrate the nonnegative quadratic `(f - c)²` for the optimal
`c = (∫ f)/(b - a)`. -/
theorem sq_integral_interval_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hi : IntervalIntegrable (fun x : ℝ => (f x) ^ 2) MeasureTheory.volume a b) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, (f x) ^ 2 := by
  rcases eq_or_lt_of_le hab with hab' | hab'
  · -- degenerate interval
    rw [hab']
    simp [intervalIntegral.integral_same]
  · by_cases hf : IntervalIntegrable f volume a b
    · -- the integral of `f` is a genuine number: integrate the nonnegative quadratic `(f - c)²`
      set A : ℝ := ∫ t in a..b, f t with hA
      set B : ℝ := ∫ t in a..b, f t ^ 2 with hB
      have key : ∀ c : ℝ, 0 ≤ c ^ 2 * (b - a) - 2 * c * A + B := by
        intro c
        have hA1 : IntervalIntegrable (fun t : ℝ => f t ^ 2 - 2 * c * f t) volume a b :=
          hi.sub (hf.const_mul (2 * c))
        have hA2 : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume a b :=
          intervalIntegrable_const
        have hiden : (∫ t in a..b, (f t - c) ^ 2) = c ^ 2 * (b - a) - 2 * c * A + B := by
          have h1 : (∫ t in a..b, (f t - c) ^ 2)
              = ∫ t in a..b, (f t ^ 2 - 2 * c * f t + c ^ 2) := by
            apply intervalIntegral.integral_congr
            intro t _
            ring
          rw [h1, intervalIntegral.integral_add hA1 hA2,
            intervalIntegral.integral_sub hi (hf.const_mul (2 * c)),
            intervalIntegral.integral_const_mul (2 * c) f,
            intervalIntegral.integral_const]
          rw [← hA, ← hB]
          simp only [smul_eq_mul]
          ring
        have hnn : 0 ≤ ∫ t in a..b, (f t - c) ^ 2 :=
          intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg (f u - c))
        rw [hiden] at hnn
        exact hnn
      have hd : 0 < b - a := sub_pos.mpr hab'
      have hkey := key (A / (b - a))
      have hexp : (b - a) * ((A / (b - a)) ^ 2 * (b - a) - 2 * (A / (b - a)) * A + B)
          = B * (b - a) - A ^ 2 := by
        field_simp [ne_of_gt hd]
        ring
      have hle : A ^ 2 ≤ B * (b - a) := by
        have h : 0 ≤ B * (b - a) - A ^ 2 := by
          rw [← hexp]
          exact mul_nonneg hd.le hkey
        linarith
      rw [mul_comm (b - a) B]
      exact hle
    · -- `f` is not interval integrable: its interval integral vanishes and the right side is ≥ 0
      rw [intervalIntegral.integral_undef hf]
      have h2 : 0 ≤ (b - a) * ∫ x in a..b, f x ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hab)
          (intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg (f u)))
      have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0]
      exact h2

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.tendsto_slope_interval_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter Set
open scoped Topology

namespace Work.FTS.StrongEps.EpsE4Thr


end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.AbsLamShiftIntegrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open MeasureTheory Filter

/-- **The shifted absolute trace is integrable.**  If `u ↦ lam (exp u)` is integrable on the
line, then for every `z > 0` the function `x ↦ |lam (z * exp (-x))|` is integrable on the whole
line, hence on the interval `Icc (-ε) ε`.

The substitution `u = log z - x` is an affine (indeed, measure preserving) change of variable:
`z * exp (-x) = exp (log z - x)`, so the claim is the translation- and dilation-invariance of the
Lebesgue integral — no local structure of `lam` beyond the integrability of its log-trace is
needed.  (The sibling `mti_integrable_shift_abs` of `MarginalTransferIntegrable.lean` is the
ε-generalised form of the same computation, with `-(ε * x)` in place of `-x`; here the
`ε` only enters through the irrelevant interval `Icc (-ε) ε`.) -/
theorem AbsLamShiftIntegrableOn {lam : ℝ → ℝ}
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)))
    {ε z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun x : ℝ => |lam (z * Real.exp (-x))|) (Set.Icc (-ε) ε) := by
  -- (1) translate the log-trace by `log z`; the translation is measure preserving
  have h1 : MeasureTheory.Integrable (fun y : ℝ => |lam (Real.exp (y + Real.log z))|) volume := by
    have hmp : MeasureTheory.MeasurePreserving (fun y : ℝ => y + Real.log z) volume volume :=
      MeasureTheory.measurePreserving_add_right volume (Real.log z)
    have hemb : MeasurableEmbedding (fun y : ℝ => y + Real.log z) :=
      measurableEmbedding_addRight (Real.log z)
    exact ((hmp.integrable_comp_emb hemb).mpr hint).abs
  -- (2) reflect the line, `x ↦ -x`, which is the dilation by `-1` (a nonzero scalar)
  have h2 : MeasureTheory.Integrable
      (fun x : ℝ => |lam (Real.exp ((-1 : ℝ) * x + Real.log z))|) volume :=
    h1.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)
  -- (3) identify the two arguments: `exp ((-1) * x + log z) = z * exp (-x)`
  have hfun : ∀ x : ℝ, Real.exp ((-1 : ℝ) * x + Real.log z) = z * Real.exp (-x) := by
    intro x
    rw [show (-1 : ℝ) * x + Real.log z = Real.log z - x by ring, Real.exp_sub,
      Real.exp_log hz, div_eq_mul_inv, Real.exp_neg]
  have h3 : MeasureTheory.Integrable (fun x : ℝ => |lam (z * Real.exp (-x))|) volume :=
    h2.congr (Filter.Eventually.of_forall fun x => congrArg (fun t => |lam t|) (hfun x))
  exact h3.integrableOn

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.ConvInjective =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology FourierTransform ContDiff SchwartzMap
open MeasureTheory Set Filter



end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsSqIntegralAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- `ENNReal.ofReal` turns a square into the square of the absolute value. -/
lemma ofReal_sq_abs (y : ℝ) : ENNReal.ofReal (y ^ 2) = (ENNReal.ofReal |y|) ^ 2 := by
  rw [sq, ← abs_mul_abs_self y, ENNReal.ofReal_mul (abs_nonneg y), sq]

/-- The square of the half-power is the number itself. -/
lemma rpow_half_sq (x : ℝ≥0∞) : (x ^ ((1:ℝ)/2)) ^ (2:ℕ) = x := by
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num

/-- **Cauchy–Schwarz with a weight**, in the `ℝ≥0∞`-form used below:
`(∫⁻ |f|)² ≤ (∫⁻ f²/b) · (∫⁻ b)` for `b > 0`.  This is Hölder's inequality with exponents
`p = q = 2` applied to `|f|/√b` and `√b`. -/
lemma l2_cs {ν : Measure ℝ} [IsFiniteMeasure ν] {b : ℝ → ℝ} (hb_meas : AEMeasurable b ν)
    (hb_pos : ∀ s, 0 < b s) {f : ℝ → ℝ} (hf_meas : AEMeasurable f ν) :
    (∫⁻ s, ENNReal.ofReal |f s| ∂ν) ^ 2
      ≤ (∫⁻ s, ENNReal.ofReal (f s ^ 2 / b s) ∂ν) * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) := by
  have hpq : (2:ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hb_nn : ∀ s, 0 ≤ b s := fun s => (hb_pos s).le
  have hsq_meas : AEMeasurable (fun s => Real.sqrt (b s)) ν := hb_meas.sqrt
  have hf1 : AEMeasurable (fun s => ENNReal.ofReal (|f s| / Real.sqrt (b s))) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hf_meas.abs.div hsq_meas)
  have hg1 : AEMeasurable (fun s => ENNReal.ofReal (Real.sqrt (b s))) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable hsq_meas
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hf1 hg1
  have hconv : (∫⁻ a, ((fun s => ENNReal.ofReal (|f s| / Real.sqrt (b s)))
      * fun s => ENNReal.ofReal (Real.sqrt (b s))) a ∂ν) = ∫⁻ s, ENNReal.ofReal |f s| ∂ν := by
    refine lintegral_congr (fun s => ?_)
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)),
      div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.2 (hb_pos s)))]
  rw [hconv] at h
  have hf1sq : (fun s => (ENNReal.ofReal (|f s| / Real.sqrt (b s))) ^ (2:ℝ))
      = fun s => ENNReal.ofReal (f s ^ 2 / b s) := by
    funext s
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)),
      div_pow, sq_abs, Real.sq_sqrt (hb_nn s)]
  have hg1sq : (fun s => (ENNReal.ofReal (Real.sqrt (b s))) ^ (2:ℝ))
      = fun s => ENNReal.ofReal (b s) := by
    funext s
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hb_nn s)]
  rw [hf1sq, hg1sq] at h
  calc (∫⁻ s, ENNReal.ofReal |f s| ∂ν) ^ 2
      ≤ ((∫⁻ s, ENNReal.ofReal (f s ^ 2 / b s) ∂ν) ^ ((1:ℝ)/2)
          * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) ^ ((1:ℝ)/2)) ^ 2 :=
        pow_le_pow_left₀ bot_le h 2
    _ = (∫⁻ s, ENNReal.ofReal (f s ^ 2 / b s) ∂ν) * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) := by
        rw [mul_pow, rpow_half_sq, rpow_half_sq]

/-- **Minkowski's inequality for the `L²`-norm of a parameter integral.**  For a curve
`F : ℝ → P → ℝ` of functions on a measure space `(P, μ)` which is a.e. strongly measurable as a
function of the pair, whose `s`-slices are square-integrable in `p` for a.e. `s`, and for which
`s ↦ √(∫_p F s p²)` is integrable,

`∫_p (∫_s F s p ∂ν)² ∂μ ≤ (∫_s √(∫_p F s p² ∂μ) ∂ν)²`,

and the left-hand integrand is `μ`-integrable. -/
theorem l2_integral_le {P : Type*} [MeasurableSpace P] {μ : Measure P} {ν : Measure ℝ}
    [SFinite μ] [IsFiniteMeasure ν] {F : ℝ → P → ℝ}
    (hmeas : AEStronglyMeasurable (Function.uncurry F) (ν.prod μ))
    (hsq : ∀ᵐ s ∂ν, Integrable (fun p => (F s p) ^ 2) μ)
    (hint : Integrable (fun s => Real.sqrt (∫ p, (F s p) ^ 2 ∂μ)) ν) :
    Integrable (fun p => (∫ s, F s p ∂ν) ^ 2) μ ∧
      ∫ p, (∫ s, F s p ∂ν) ^ 2 ∂μ
        ≤ (∫ s, Real.sqrt (∫ p, (F s p) ^ 2 ∂μ) ∂ν) ^ 2 := by
  classical
  set a : ℝ → ℝ := fun s => Real.sqrt (∫ p, (F s p) ^ 2 ∂μ) with ha_def
  have ha_nn : ∀ s, 0 ≤ a s := fun s => Real.sqrt_nonneg _
  have ha_sq : ∀ s, a s ^ 2 = ∫ p, (F s p) ^ 2 ∂μ := fun s => by
    rw [ha_def]; exact Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _)
  have ha_meas : AEMeasurable a ν := hint.aemeasurable
  set A : ℝ := ∫ s, a s ∂ν with hA_def
  have hA_nn : 0 ≤ A := integral_nonneg ha_nn
  have hslice_p : ∀ᵐ p ∂μ, AEStronglyMeasurable (fun s => F s p) ν := hmeas.prodMk_right
  -- The main chain, with the weight `b = a + ε`.
  have key : ∀ ε : ℝ, 0 < ε →
      ∫⁻ p, ENNReal.ofReal ((∫ s, F s p ∂ν) ^ 2) ∂μ
        ≤ ENNReal.ofReal ((A + ε * (ν Set.univ).toReal) * A) := by
    intro ε hε
    set b : ℝ → ℝ := fun s => a s + ε with hb_def
    have hb_pos : ∀ s, 0 < b s := fun s => by rw [hb_def]; linarith [ha_nn s, hε]
    have hb_nn : ∀ s, 0 ≤ b s := fun s => (hb_pos s).le
    have hb_meas : AEMeasurable b ν := ha_meas.add aemeasurable_const
    have hb_int : Integrable b ν := hint.add (integrable_const ε)
    have hBval : ∫ s, b s ∂ν = A + ε * (ν Set.univ).toReal := by
      rw [hb_def, integral_add hint (integrable_const ε), hA_def, integral_const]
      simp only [Measure.real, smul_eq_mul]
      ring
    have hofB : ENNReal.ofReal (∫ s, b s ∂ν) = ∫⁻ s, ENNReal.ofReal (b s) ∂ν :=
      ofReal_integral_eq_lintegral_ofReal hb_int (ae_of_all _ hb_nn)
    -- the pointwise (a.e. in `p`) Cauchy–Schwarz inequality
    have hpt : ∀ᵐ p ∂μ, ENNReal.ofReal ((∫ s, F s p ∂ν) ^ 2)
        ≤ (∫⁻ s, ENNReal.ofReal (F s p ^ 2 / b s) ∂ν) * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) := by
      filter_upwards [hslice_p] with p hp
      calc ENNReal.ofReal ((∫ s, F s p ∂ν) ^ 2)
          = (ENNReal.ofReal |∫ s, F s p ∂ν|) ^ 2 := ofReal_sq_abs _
        _ ≤ (∫⁻ s, ENNReal.ofReal |F s p| ∂ν) ^ 2 := by
              refine pow_le_pow_left₀ bot_le ?_ 2
              have h := enorm_integral_le_lintegral_enorm (μ := ν) (fun s => F s p)
              simpa [Real.enorm_eq_ofReal_abs] using h
        _ ≤ _ := l2_cs hb_meas hb_pos hp.aemeasurable
    -- joint measurability for Tonelli
    have hmeasG : AEMeasurable (fun q : P × ℝ => ENNReal.ofReal (F q.2 q.1 ^ 2 / b q.2))
        (μ.prod ν) := by
      have h1 : AEMeasurable (fun q : P × ℝ => F q.2 q.1) (μ.prod ν) :=
        hmeas.prod_swap.aemeasurable
      have h2 : AEMeasurable (fun q : P × ℝ => b q.2) (μ.prod ν) := hb_meas.comp_snd
      exact ENNReal.measurable_ofReal.comp_aemeasurable ((h1.pow_const 2).div h2)
    -- the `s`-slices of `F ·²/b` are integrable for a.e. `s`
    have hGint : ∀ᵐ s ∂ν, Integrable (fun p => F s p ^ 2 / b s) μ :=
      hsq.mono fun s hs => hs.div_const (b s)
    -- the inner integral collapses to `ofReal (a s)`
    have hinner : ∀ᵐ s ∂ν, (∫⁻ p, ENNReal.ofReal (F s p ^ 2 / b s) ∂μ)
        ≤ ENNReal.ofReal (a s) := by
      filter_upwards [hGint] with s hs
      rw [← ofReal_integral_eq_lintegral_ofReal hs
        (ae_of_all _ (fun p => div_nonneg (sq_nonneg _) (hb_nn s))), integral_div, ← ha_sq s]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ (hb_pos s)]
      nlinarith [ha_nn s, hε]
    calc ∫⁻ p, ENNReal.ofReal ((∫ s, F s p ∂ν) ^ 2) ∂μ
        ≤ ∫⁻ p, (∫⁻ s, ENNReal.ofReal (F s p ^ 2 / b s) ∂ν)
            * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) ∂μ :=
          lintegral_mono_ae hpt
      _ = (∫⁻ p, ∫⁻ s, ENNReal.ofReal (F s p ^ 2 / b s) ∂ν ∂μ)
            * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) :=
          lintegral_mul_const' _ _ (by rw [← hofB]; exact ENNReal.ofReal_lt_top.ne)
      _ = (∫⁻ s, ∫⁻ p, ENNReal.ofReal (F s p ^ 2 / b s) ∂μ ∂ν)
            * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) := by
          rw [lintegral_lintegral_swap hmeasG]
      _ ≤ (∫⁻ s, ENNReal.ofReal (a s) ∂ν) * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) := by
          exact mul_le_mul_of_nonneg_right (lintegral_mono_ae hinner) bot_le
      _ = ENNReal.ofReal A * ENNReal.ofReal (∫ s, b s ∂ν) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ ha_nn), hofB]
      _ = ENNReal.ofReal (A * (A + ε * (ν Set.univ).toReal)) := by
          rw [← hBval, ← ENNReal.ofReal_mul hA_nn]
      _ = ENNReal.ofReal ((A + ε * (ν Set.univ).toReal) * A) := by
          rw [mul_comm]
  have hnorm : ENNReal.ofReal (∫ p, (∫ s, F s p ∂ν) ^ 2 ∂μ)
      ≤ ∫⁻ p, ENNReal.ofReal ((∫ s, F s p ∂ν) ^ 2) ∂μ := by
    have h := enorm_integral_le_lintegral_enorm (μ := μ) (fun p => (∫ s, F s p ∂ν) ^ 2)
    rw [Real.enorm_eq_ofReal (integral_nonneg (fun p => sq_nonneg _))] at h
    refine h.trans_eq (lintegral_congr (fun p => ?_))
    exact Real.enorm_eq_ofReal (sq_nonneg _)
  -- the integrand is a.e. strongly measurable
  have hmeas_int : AEStronglyMeasurable (fun p => (∫ s, F s p ∂ν) ^ 2) μ :=
    hmeas.prod_swap.integral_prod_right'.pow 2
  -- and has finite `lintegral` of its norm
  have hfin : ∫⁻ p, ‖(∫ s, F s p ∂ν) ^ 2‖ₑ ∂μ < ∞ := by
    rw [lintegral_congr (fun p => Real.enorm_eq_ofReal (sq_nonneg _))]
    exact lt_of_le_of_lt (key 1 one_pos) ENNReal.ofReal_lt_top
  refine ⟨⟨hmeas_int, hasFiniteIntegral_iff_enorm.mpr hfin⟩, ?_⟩
  -- the bound
  have hle : ∫ p, (∫ s, F s p ∂ν) ^ 2 ∂μ ≤ A * A := by
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    have hc_nn : 0 ≤ (ν Set.univ).toReal := ENNReal.toReal_nonneg
    have hden : 0 < (ν Set.univ).toReal * A + 1 := by nlinarith
    have h := hnorm.trans (key (δ / ((ν Set.univ).toReal * A + 1)) (by positivity))
    have hY : 0 ≤ (A + δ / ((ν Set.univ).toReal * A + 1) * (ν Set.univ).toReal) * A :=
      mul_nonneg (add_nonneg hA_nn (mul_nonneg (div_nonneg hδ.le hden.le) hc_nn)) hA_nn
    have h' : ∫ p, (∫ s, F s p ∂ν) ^ 2 ∂μ
        ≤ (A + δ / ((ν Set.univ).toReal * A + 1) * (ν Set.univ).toReal) * A :=
      (ENNReal.ofReal_le_ofReal_iff hY).mp h
    have h4 : δ * ((ν Set.univ).toReal * A) / ((ν Set.univ).toReal * A + 1) ≤ δ := by
      rw [div_le_iff₀ hden]
      exact mul_le_mul_of_nonneg_left (by linarith) hδ.le
    calc ∫ p, (∫ s, F s p ∂ν) ^ 2 ∂μ
        ≤ (A + δ / ((ν Set.univ).toReal * A + 1) * (ν Set.univ).toReal) * A := h'
      _ = A * A + δ * ((ν Set.univ).toReal * A) / ((ν Set.univ).toReal * A + 1) := by ring
      _ ≤ A * A + δ := by linarith
  calc ∫ p, (∫ s, F s p ∂ν) ^ 2 ∂μ ≤ A * A := hle
    _ = (∫ s, Real.sqrt (∫ p, (F s p) ^ 2 ∂μ) ∂ν) ^ 2 := by rw [hA_def, ha_def, sq]

end Work.FTS.StrongEps.EpsLocalPStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.ExpShiftIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open MeasureTheory Set

/-- The map `y ↦ z * exp (-y)` is a `C¹` diffeomorphism from `ℝ` onto `(0,∞)`; it carries
`Icc (-ε) ε` onto the compact positive interval `Icc (z * exp (-ε)) (z * exp ε)`.  Hence a
function which is integrable on every compact interval of positive reals has an integrable
pull-back under this exponential substitution. -/
theorem ExpShiftIntegrable {h : ℝ → ℝ} {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z)
    (hint : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn h (Set.Icc a b)) :
    MeasureTheory.IntegrableOn (fun x : ℝ => h (z * Real.exp (-x))) (Set.Icc (-ε) ε) := by
  have hz0 : z ≠ 0 := hz.ne'
  -- The positive interval which is the image of `Icc (-ε) ε`.
  set a : ℝ := z * Real.exp (-ε) with ha_def
  set b : ℝ := z * Real.exp ε with hb_def
  have ha : 0 < a := by rw [ha_def]; positivity
  have hb : 0 < b := by rw [hb_def]; positivity
  have hab : a ≤ b := by
    rw [ha_def, hb_def]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hz.le
  have hloga : Real.log a = Real.log z - ε := by
    rw [ha_def, Real.log_mul hz0 (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hlogb : Real.log b = Real.log z + ε := by
    rw [hb_def, Real.log_mul hz0 (Real.exp_ne_zero _), Real.log_exp]
  -- The inverse substitution `φ y = log z - log y`, which maps `Icc a b` onto `Icc (-ε) ε`.
  set φ : ℝ → ℝ := fun y => Real.log z - Real.log y with hφ
  have hderiv : ∀ y ∈ Set.Icc a b, HasDerivWithinAt φ (-(y⁻¹)) (Set.Icc a b) y := by
    intro y hy
    have hy0 : y ≠ 0 := (lt_of_lt_of_le ha hy.1).ne'
    have hd : HasDerivAt (fun t : ℝ => Real.log z - Real.log t) (0 - y⁻¹) y :=
      (hasDerivAt_const y (Real.log z)).sub (Real.hasDerivAt_log hy0)
    simpa [hφ] using hd.hasDerivWithinAt
  have hinj : Set.InjOn φ (Set.Icc a b) := by
    intro y hy y' hy' heq
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have hy0' : 0 < y' := lt_of_lt_of_le ha hy'.1
    have hlog : Real.log y = Real.log y' := by
      have h' := heq
      simp only [hφ] at h'
      linarith
    exact Real.log_injOn_pos hy0 hy0' hlog
  have himg : φ '' Set.Icc a b = Set.Icc (-ε) ε := by
    ext t
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_Icc] at hy
      have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
      have h1 : Real.log y ≤ Real.log z + ε := by
        rw [← hlogb]; exact Real.log_le_log hy0 hy.2
      have h2 : Real.log z - ε ≤ Real.log y := by
        rw [← hloga]; exact Real.log_le_log ha hy.1
      simp only [hφ, Set.mem_Icc]
      constructor <;> linarith
    · intro ht
      simp only [Set.mem_Icc] at ht
      refine ⟨z * Real.exp (-t), ?_, ?_⟩
      · simp only [ha_def, hb_def, Set.mem_Icc]
        constructor
        · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [ht.2])) hz.le
        · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [ht.1])) hz.le
      · simp only [hφ]
        rw [Real.log_mul hz0 (Real.exp_ne_zero _), Real.log_exp]
        ring
  -- Change of variables: integrability on `φ '' Icc a b` is equivalent to integrability of
  -- `|φ'| • (h ∘ φ)` on `Icc a b`.
  have key := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.Icc a b) (f := φ) (f' := fun y => -(y⁻¹)) measurableSet_Icc hderiv hinj
    (fun x => h (z * Real.exp (-x)))
  rw [himg] at key
  rw [key]
  -- On `Icc a b` the factor `|φ' y| = y⁻¹` is bounded, and `h ∘ φ = h` there.
  have hcont : ContinuousOn (fun y : ℝ => y⁻¹) (Set.Icc a b) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro y hy; exact (lt_of_lt_of_le ha hy.1).ne'
  have h2 : MeasureTheory.IntegrableOn (fun y : ℝ => y⁻¹ * h y) (Set.Icc a b) :=
    MeasureTheory.IntegrableOn.continuousOn_mul_of_subset hcont (hint a b ha hab)
      isCompact_Icc measurableSet_Icc Subset.rfl
  rw [MeasureTheory.integrableOn_congr_fun
    (f := fun y : ℝ => |(-(y⁻¹))| • h (z * Real.exp (-(Real.log z - Real.log y))))
    (g := fun y : ℝ => y⁻¹ * h y) _ measurableSet_Icc]
  · exact h2
  · intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have hexp : z * Real.exp (-(Real.log z - Real.log y)) = y := by
      rw [show -(Real.log z - Real.log y) = Real.log y - Real.log z by ring]
      rw [Real.exp_sub, Real.exp_log hy0, Real.exp_log hz]
      field_simp
    have habs : |(-(y⁻¹))| = y⁻¹ := by
      rw [abs_neg, abs_of_pos (inv_pos.mpr hy0)]
    show |(-(y⁻¹))| • h (z * Real.exp (-(Real.log z - Real.log y))) = y⁻¹ * h y
    rw [hexp, habs, smul_eq_mul]

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.FourierZeroNull =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Fourier transform of a compactly supported `L¹` function is a.e. nonzero

If `ρ : ℝ → ℂ` is integrable, vanishes off `[-1, 1]` and has nonzero total mass `∫ ρ ≠ 0`,
then its Fourier transform `𝓕 ρ` does not vanish on a set of positive measure.

The proof is the classical one.  Since `ρ` is supported in the compact set `[-1, 1]`, the
parametric integral
`F z = ∫ a, exp ((-2πi a) * z) * ρ a`
is an entire function of `z : ℂ` (differentiation under the integral sign; the domination is
supplied by the compact support and `Integrable ρ`).  On the real line `F` restricts to `𝓕 ρ`,
and `F 0 = ∫ ρ ≠ 0`, so `F` is not identically zero.  By the identity theorem the zero set of
an analytic function on `ℂ` (or `ℝ`) is *discrete* (`AnalyticOnNhd.preimage_zero_mem_codiscrete`),
hence countable (a discrete subset of a Lindelöf space is countable,
`IsLindelof.countable_of_isDiscrete`), and a countable subset of `ℝ` has measure zero. -/

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology FourierTransform
open MeasureTheory Set Filter

/-- The frequency factor of the plane wave `a ↦ exp (epsK a * z)`. -/
private noncomputable def epsK (a : ℝ) : ℂ := (↑(-2 * Real.pi * a) : ℂ) * Complex.I

/-- The entire extension of the Fourier transform of `ρ`:
`fourierCont ρ z = ∫ a, exp ((-2πi a) z) ρ a`. -/
noncomputable def fourierCont (ρ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ a : ℝ, Complex.exp (epsK a * z) * ρ a

private lemma continuous_epsK : Continuous epsK :=
  (Complex.continuous_ofReal.comp (by continuity)).mul continuous_const

private lemma continuous_exp_epsK (z : ℂ) : Continuous fun a : ℝ => Complex.exp (epsK a * z) :=
  Complex.continuous_exp.comp (continuous_epsK.mul continuous_const)

private lemma norm_epsK_mul_le (a : ℝ) (z : ℂ) : ‖epsK a * z‖ ≤ 2 * Real.pi * |a| * ‖z‖ := by
  refine (norm_mul_le _ _).trans ?_
  simp only [epsK, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_pos Real.pi_pos, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  ring_nf
  exact le_refl _

private lemma norm_epsK (a : ℝ) : ‖epsK a‖ = 2 * Real.pi * |a| := by
  simp only [epsK, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_pos Real.pi_pos, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

/-- Domination of the plane wave on the unit ball of frequencies, using `|a| ≤ 1` on the
support of `ρ`. -/
private lemma norm_exp_epsK_le (a : ℝ) (z z₀ : ℂ) (ha : |a| ≤ 1) (hz : ‖z‖ ≤ ‖z₀‖ + 1) :
    ‖Complex.exp (epsK a * z)‖ ≤ Real.exp (2 * Real.pi * (‖z₀‖ + 1)) := by
  refine (Complex.norm_exp_le_exp_norm _).trans ?_
  apply Real.exp_le_exp.mpr
  refine (norm_epsK_mul_le a z).trans ?_
  calc 2 * Real.pi * |a| * ‖z‖ ≤ (2 * Real.pi * 1) * (‖z₀‖ + 1) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left ha (by positivity)
        · exact hz
        · positivity
        · positivity
    _ = 2 * Real.pi * (‖z₀‖ + 1) := by ring

private lemma norm_le_of_mem_ball (z₀ z : ℂ) (hz : z ∈ Metric.ball z₀ 1) :
    ‖z‖ ≤ ‖z₀‖ + 1 := by
  have hd : dist z z₀ < 1 := Metric.mem_ball.mp hz
  calc ‖z‖ = dist z 0 := by rw [dist_zero_right]
    _ ≤ dist z z₀ + dist z₀ 0 := dist_triangle z z₀ 0
    _ ≤ 1 + ‖z₀‖ := by rw [dist_zero_right]; linarith
    _ = ‖z₀‖ + 1 := by ring

/-- On the real line, the entire extension restricts to the Fourier transform. -/
lemma fourierCont_ofReal (ρ : ℝ → ℂ) (ξ : ℝ) : fourierCont ρ (ξ : ℂ) = 𝓕 ρ ξ := by
  rw [Real.fourier_eq']
  simp only [fourierCont, smul_eq_mul]
  congr 1
  ext a
  congr 1
  rw [Real.inner_apply, epsK]
  push_cast
  ring

/-- The value at the origin is the total mass. -/
lemma fourierCont_zero (ρ : ℝ → ℂ) : fourierCont ρ 0 = ∫ a, ρ a := by
  simp [fourierCont]

/-- `fourierCont ρ` is entire. -/
lemma fourierCont_differentiable {ρ : ℝ → ℂ} (h : Integrable ρ)
    (hs : ∀ x ∉ Set.Icc (-1 : ℝ) 1, ρ x = 0) : Differentiable ℂ (fourierCont ρ) := by
  have hsupp : ∀ a : ℝ, ρ a ≠ 0 → |a| ≤ 1 := by
    intro a ha
    by_contra hcon
    exact ha (hs a fun hmem => hcon (abs_le.mpr hmem))
  intro z₀
  set C : ℝ := 2 * Real.pi * Real.exp (2 * Real.pi * (‖z₀‖ + 1)) with hC
  have h2π : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hbnd_int : Integrable (fun a : ℝ => C * ‖ρ a‖) volume := h.norm.const_mul C
  have hmeas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (fun a : ℝ => Complex.exp (epsK a * z) * ρ a) volume := by
    filter_upwards with z
    exact (continuous_exp_epsK z).aestronglyMeasurable.mul h.1
  have hint : Integrable (fun a : ℝ => Complex.exp (epsK a * z₀) * ρ a) volume := by
    apply Integrable.mono' hbnd_int
    · exact (continuous_exp_epsK z₀).aestronglyMeasurable.mul h.1
    · filter_upwards with a
      rcases eq_or_ne (ρ a) 0 with h0 | h0
      · simp [h0]
      · have he : ‖Complex.exp (epsK a * z₀)‖ ≤ Real.exp (2 * Real.pi * (‖z₀‖ + 1)) :=
          norm_exp_epsK_le a z₀ z₀ (hsupp a h0) (by linarith [norm_nonneg z₀])
        calc ‖Complex.exp (epsK a * z₀) * ρ a‖ = ‖Complex.exp (epsK a * z₀)‖ * ‖ρ a‖ :=
              norm_mul _ _
          _ ≤ Real.exp (2 * Real.pi * (‖z₀‖ + 1)) * ‖ρ a‖ := by gcongr
          _ ≤ C * ‖ρ a‖ := by
              rw [hC]
              gcongr
              exact le_mul_of_one_le_left (Real.exp_nonneg _) h2π
  have hF'meas : AEStronglyMeasurable
      (fun a : ℝ => (Complex.exp (epsK a * z₀) * epsK a) * ρ a) volume := by
    exact (((continuous_exp_epsK z₀).mul continuous_epsK).aestronglyMeasurable).mul h.1
  have hbnd : ∀ᵐ a ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      ‖(Complex.exp (epsK a * z) * epsK a) * ρ a‖ ≤ C * ‖ρ a‖ := by
    filter_upwards with a z hz
    rcases eq_or_ne (ρ a) 0 with h0 | h0
    · simp [h0]
    · have ha1 : |a| ≤ 1 := hsupp a h0
      have hz1 : ‖z‖ ≤ ‖z₀‖ + 1 := norm_le_of_mem_ball z₀ z hz
      have he : ‖Complex.exp (epsK a * z)‖ ≤ Real.exp (2 * Real.pi * (‖z₀‖ + 1)) :=
        norm_exp_epsK_le a z z₀ ha1 hz1
      have hK : ‖epsK a‖ ≤ 2 * Real.pi := by
        rw [norm_epsK]
        nlinarith [Real.pi_pos, abs_nonneg a, ha1]
      calc ‖(Complex.exp (epsK a * z) * epsK a) * ρ a‖
          = ‖Complex.exp (epsK a * z)‖ * ‖epsK a‖ * ‖ρ a‖ := by rw [norm_mul, norm_mul]
        _ ≤ Real.exp (2 * Real.pi * (‖z₀‖ + 1)) * (2 * Real.pi) * ‖ρ a‖ := by gcongr
        _ = C * ‖ρ a‖ := by rw [hC]; ring_nf
  have hdiff : ∀ᵐ a ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun x : ℂ => Complex.exp (epsK a * x) * ρ a)
        ((Complex.exp (epsK a * z) * epsK a) * ρ a) z := by
    filter_upwards with a z _
    exact ((hasDerivAt_const_mul (epsK a)).cexp).mul_const (ρ a)
  have key : Integrable (fun a : ℝ => (Complex.exp (epsK a * z₀) * epsK a) * ρ a) volume ∧
      HasDerivAt (fun z => ∫ a, Complex.exp (epsK a * z) * ρ a)
        (∫ a, (Complex.exp (epsK a * z₀) * epsK a) * ρ a) z₀ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball z₀ 1)
      (bound := fun a => C * ‖ρ a‖) (Metric.ball_mem_nhds z₀ one_pos)
      hmeas hint hF'meas hbnd hbnd_int hdiff
  change DifferentiableAt ℂ (fun z => ∫ a, Complex.exp (epsK a * z) * ρ a) z₀
  exact key.2.differentiableAt

theorem FourierZeroNull {ρ : ℝ → ℂ} (h : MeasureTheory.Integrable ρ)
    (hs : ∀ x ∉ Set.Icc (-1 : ℝ) 1, ρ x = 0) (h0 : (∫ x, ρ x) ≠ 0) :
    ∀ᵐ ξ ∂MeasureTheory.volume, 𝓕 ρ ξ ≠ 0 := by
  have hdiff : Differentiable ℂ (fourierCont ρ) := fourierCont_differentiable h hs
  have h0' : fourierCont ρ (0 : ℂ) ≠ 0 := by
    rw [fourierCont_zero]
    exact h0
  -- `ξ ↦ fourierCont ρ ↑ξ` is real analytic, being the restriction of an entire function
  have hanR : AnalyticOnNhd ℝ (fun ξ : ℝ => fourierCont ρ (ξ : ℂ)) Set.univ := by
    intro ξ _
    have h1 : AnalyticAt ℝ (fourierCont ρ) ((ξ : ℂ)) :=
      (hdiff.analyticAt (ξ : ℂ)).restrictScalars
    have h2 : AnalyticAt ℝ (fun y : ℝ => (y : ℂ)) ξ := Complex.ofRealCLM.analyticAt ξ
    simpa only [Function.comp_def] using h1.comp h2
  -- the zero set is closed and discrete, hence countable, hence null
  have hcod : (fun ξ : ℝ => fourierCont ρ (ξ : ℂ)) ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ :=
    hanR.preimage_zero_mem_codiscrete h0'
  have hcl : IsClosed ((fun ξ : ℝ => fourierCont ρ (ξ : ℂ)) ⁻¹' {0}) :=
    (compl_mem_codiscrete_iff.mp hcod).1
  have hdisc : IsDiscrete ((fun ξ : ℝ => fourierCont ρ (ξ : ℂ)) ⁻¹' {0}) :=
    (compl_mem_codiscrete_iff.mp hcod).2
  have hcnt : ((fun ξ : ℝ => fourierCont ρ (ξ : ℂ)) ⁻¹' {0}).Countable :=
    IsLindelof.countable_of_isDiscrete (isLindelof_univ.of_isClosed_subset hcl (subset_univ _))
      hdisc
  rw [MeasureTheory.ae_iff]
  have hset : {ξ : ℝ | ¬ (𝓕 ρ ξ ≠ 0)} = (fun ξ : ℝ => fourierCont ρ (ξ : ℂ)) ⁻¹' {0} := by
    ext ξ
    simp [fourierCont_ofReal]
  rw [hset]
  exact hcnt.measure_zero volume

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSrc.sq_le_of_forall_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSrc

/-- **Squaring the AM–GM bound.**  If `x ≤ K · (t/2 + M/(2t))` for every `t > 0` and `K ≠ ⊤`,
then `x² ≤ K² M` in `ℝ≥0∞`.  The bound is applied at `t = √M` (giving `t/2 + M/(2t) = √M`);
the degenerate cases `K = 0`, `M = ⊤` and `M = 0` are handled separately (for `M = 0` the bound
is applied at `t = 2ε/K` and the limit `ε → 0⁺` is taken via `ENNReal.le_of_forall_pos_le_add`). -/
theorem sq_le_of_forall_mul {x M K : ENNReal} (hK : K ≠ ⊤)
    (h : ∀ t : ℝ, 0 < t → x ≤ K * (ENNReal.ofReal (t / 2) + M * ENNReal.ofReal ((2 * t)⁻¹))) :
    x ^ 2 ≤ K ^ 2 * M := by
  rcases eq_or_ne K 0 with hK0 | hK0
  · subst hK0
    have hx0 : x = 0 := le_bot_iff.mp (by simpa using h 1 zero_lt_one)
    subst hx0
    simp
  · rcases eq_or_ne M ⊤ with hMtop | hMtop
    · rw [hMtop, ENNReal.mul_top (ENNReal.pow_ne_zero hK0 2)]
      exact le_top
    · set s : ℝ := Real.sqrt M.toReal with hs
      have hsnn : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg M.toReal
      have hs2 : s ^ 2 = M.toReal := by rw [hs]; exact Real.sq_sqrt ENNReal.toReal_nonneg
      have hMsq : ENNReal.ofReal s * ENNReal.ofReal s = M := by
        rw [← ENNReal.ofReal_mul hsnn, ← pow_two, hs2, ENNReal.ofReal_toReal hMtop]
      have hMsq' : ENNReal.ofReal s ^ 2 = M := by rw [pow_two, hMsq]
      have hxle : x ≤ K * ENNReal.ofReal s := by
        rcases eq_or_ne M.toReal 0 with hm0 | hm0
        · have hM0 : M = 0 := by
            rw [← ENNReal.ofReal_toReal hMtop, hm0, ENNReal.ofReal_zero]
          have hs0 : s = 0 := by rw [hs, hm0, Real.sqrt_zero]
          rw [hs0, ENNReal.ofReal_zero, mul_zero]
          refine ENNReal.le_of_forall_pos_le_add ?_
          intro ε hε _
          rw [zero_add]
          have hKpos : 0 < K.toReal := ENNReal.toReal_pos hK0 hK
          have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
          have ht : 0 < 2 * (ε : ℝ) / K.toReal := by positivity
          have hh := h (2 * (ε : ℝ) / K.toReal) ht
          rw [hM0, zero_mul, add_zero] at hh
          have hb : K * ENNReal.ofReal ((2 * (ε : ℝ) / K.toReal) / 2) ≠ ⊤ :=
            ne_of_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK) ENNReal.ofReal_lt_top)
          have hxtr : x.toReal ≤ (ε : ℝ) := by
            calc x.toReal
                ≤ (K * ENNReal.ofReal ((2 * (ε : ℝ) / K.toReal) / 2)).toReal :=
                  ENNReal.toReal_mono hb hh
              _ = K.toReal * ((2 * (ε : ℝ) / K.toReal) / 2) := by
                  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
              _ = (ε : ℝ) := by field_simp
          calc x = ENNReal.ofReal x.toReal :=
                (ENNReal.ofReal_toReal (ne_top_of_le_ne_top hb hh)).symm
            _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal hxtr
            _ = (ε : ENNReal) := ENNReal.ofReal_coe_nnreal
        · have hMpos : 0 < M.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hm0)
          have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hMpos
          have hsne : s ≠ 0 := ne_of_gt hspos
          refine le_trans (h s hspos) ?_
          have key : ENNReal.ofReal (s / 2) + M * ENNReal.ofReal ((2 * s)⁻¹)
              = ENNReal.ofReal s := by
            have h2 : M * ENNReal.ofReal ((2 * s)⁻¹) = ENNReal.ofReal (s / 2) := by
              rw [← hMsq, ← ENNReal.ofReal_mul hsnn,
                ← ENNReal.ofReal_mul (mul_nonneg hsnn hsnn)]
              congr 1
              field_simp
            rw [h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
          rw [key]
      calc x ^ 2 ≤ (K * ENNReal.ofReal s) ^ 2 := ENNReal.pow_le_pow_left hxle
        _ = K ^ 2 * M := by rw [mul_pow, hMsq']

end Work.FTS.StrongEps.EpsSrc
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.WlInfDthAux.sum_shift_identity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `sum_shift_identity` of the level-`5` `W^{l,∞}` bookkeeping

Both sides of the identity are the *triangular* sum
`∑_{j < l+1} ∑_{k < l+1-j} V (j+1) k`:

* the right-hand side is `∑_{1 ≤ j ≤ l+1} ∑_{k < l+2-j} V j k`, i.e. the same triangular
  sum, after dropping the `j = 0` term (which vanishes because of the `1 ≤ j` guard) and
  observing that the guard `k + j ≤ l + 1` cuts `k` down to `k < l + 2 - j`;
* the left-hand side is the `j = 0` layer `∑_{k < l+1} V 1 k = ∑_{k < l+1-0} V (0+1) k`
  together with the layers `j = i+1`, `i < l`, which again are `∑_{k < l+1-(i+1)} V (i+2) k`
  because the guard `k + (i+1) ≤ l` cuts `k` down to `k < l+1-(i+1)`.

The two elementary ingredients are `sum_shift_filter_range` (the guard `k + j ≤ M` selects
exactly `Finset.range (M+1-j)` inside `Finset.range N`, for `M + 1 ≤ N`) and the split
`Finset.sum_range_succ'`, which peels off the `j = 0` term of a `range (l+1)`-sum.
-/

namespace Work.FTS.StrongEps.H5.WlInfDthAux

/-- Inside `Finset.range N` (with `M + 1 ≤ N`), the indices `k` with `k + j ≤ M` are exactly
`Finset.range (M + 1 - j)`. -/
lemma sum_shift_filter_range (N M j : ℕ) (h : M + 1 ≤ N) :
    (Finset.range N).filter (fun k => k + j ≤ M) = Finset.range (M + 1 - j) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The inner `k`-sum of the left-hand side, evaluated at a fixed `j`: the guards
`1 ≤ j` and `k + j ≤ l` cut it down to `∑_{k < l+1-j} V (j+1) k` (and kill it when `j = 0`). -/
lemma sum_shift_inner_left (V : ℕ → ℕ → ℝ) (l j : ℕ) :
    (∑ k ∈ Finset.range (l + 1), (if 1 ≤ j ∧ k + j ≤ l then V (j + 1) k else 0))
      = (if 1 ≤ j then ∑ k ∈ Finset.range (l + 1 - j), V (j + 1) k else 0) := by
  by_cases hj : 1 ≤ j
  · rw [ite_eq_left hj]
    simp only [hj, true_and]
    rw [← Finset.sum_filter]
    congr 1
    exact sum_shift_filter_range (l + 1) l j le_rfl
  · rw [ite_eq_right hj]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [ite_eq_right]
    exact fun h => hj h.1

/-- The inner `k`-sum of the right-hand side at the shifted index `i + 1`: the guard
`k + (i+1) ≤ l + 1` cuts it down to `∑_{k < l+1-i} V (i+1) k`. -/
lemma sum_shift_inner_right (V : ℕ → ℕ → ℝ) (l i : ℕ) :
    (∑ k ∈ Finset.range (l + 2), (if 1 ≤ i + 1 ∧ k + (i + 1) ≤ l + 1 then V (i + 1) k else 0))
      = ∑ k ∈ Finset.range (l + 1 - i), V (i + 1) k := by
  have h1 : 1 ≤ i + 1 := by omega
  simp only [h1, true_and]
  rw [← Finset.sum_filter]
  congr 1
  rw [sum_shift_filter_range (l + 2) (l + 1) (i + 1) (by omega)]
  congr 1
  omega

theorem sum_shift_identity (V : ℕ → ℕ → ℝ) (l : ℕ) :
    (∑ k ∈ Finset.range (l + 1), V 1 k)
      + (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then V (j + 1) k else 0))
    = ∑ j ∈ Finset.range (l + 2), ∑ k ∈ Finset.range (l + 2),
        (if 1 ≤ j ∧ k + j ≤ l + 1 then V j k else 0) := by
  -- the common triangular form
  have hL : (∑ k ∈ Finset.range (l + 1), V 1 k)
      + (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then V (j + 1) k else 0))
      = ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1 - j), V (j + 1) k := by
    have hB : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then V (j + 1) k else 0))
        = ∑ j ∈ Finset.range (l + 1),
            (if 1 ≤ j then ∑ k ∈ Finset.range (l + 1 - j), V (j + 1) k else 0) :=
      Finset.sum_congr rfl (fun j _ => sum_shift_inner_left V l j)
    rw [hB]
    rw [Finset.sum_range_succ'
      (fun j => (if 1 ≤ j then ∑ k ∈ Finset.range (l + 1 - j), V (j + 1) k else 0)) l]
    rw [Finset.sum_range_succ' (fun j => ∑ k ∈ Finset.range (l + 1 - j), V (j + 1) k) l]
    have h10 : ¬ ((1 : ℕ) ≤ 0) := by omega
    rw [ite_eq_right h10]
    simp only [Nat.sub_zero, add_zero]
    exact add_comm _ _
  have hR : (∑ j ∈ Finset.range (l + 2), ∑ k ∈ Finset.range (l + 2),
        (if 1 ≤ j ∧ k + j ≤ l + 1 then V j k else 0))
      = ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1 - j), V (j + 1) k := by
    rw [Finset.sum_range_succ'
      (fun j => (∑ k ∈ Finset.range (l + 2),
        (if 1 ≤ j ∧ k + j ≤ l + 1 then V j k else 0))) (l + 1)]
    have hJ0 : (∑ k ∈ Finset.range (l + 2),
        (if 1 ≤ 0 ∧ k + 0 ≤ l + 1 then V 0 k else 0)) = 0 := by simp
    rw [hJ0, add_zero]
    exact Finset.sum_congr rfl (fun i _ => sum_shift_inner_right V l i)
  exact hL.trans hR.symm

end Work.FTS.StrongEps.H5.WlInfDthAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.lintegral_exp_subst_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

open MeasureTheory Set

/-- The `lintegral` change-of-variables formula for the substitution `z = exp s` on `(0, ∞)`,
stated for an arbitrary `ENNReal`-valued function `U` (so no integrability hypothesis is
needed): `∫⁻ z ∈ (0,∞), U z = ∫⁻ s, exp s * U (exp s)`.

This is the one-dimensional change-of-variables formula
`lintegral_image_eq_lintegral_abs_deriv_mul` applied to `Real.exp` on `Set.univ`, using
`Real.range_exp : range exp = Ioi 0`. -/
theorem lintegral_exp_subst_gen (U : ℝ → ENNReal) :
    (∫⁻ z in Set.Ioi 0, U z) = ∫⁻ s, ENNReal.ofReal (Real.exp s) * U (Real.exp s) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
    (s := Set.univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn U
  simpa [image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _)] using h

end Work.FTS.StrongEps.HkSqAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.lintegral_prod_shift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.StrongEps.HkSqAux

set_option autoImplicit false

/-- **Double translation invariance of the Lebesgue integral on `ℝ × ℝ`** (iterated form):
`∫⁻ s ∫⁻ ζ, F (s - p₁) (ζ - p₂) = ∫⁻ s ∫⁻ ζ, F s ζ` for an arbitrary `ENNReal`-valued `F`
(no measurability hypothesis is needed, the `lintegral` is defined for every function). -/
theorem lintegral_prod_shift (F : ℝ → ℝ → ENNReal) (p₁ p₂ : ℝ) :
    (∫⁻ s, ∫⁻ ζ, F (s - p₁) (ζ - p₂)) = ∫⁻ s, ∫⁻ ζ, F s ζ := by
  have h1 : (fun s : ℝ => ∫⁻ ζ, F (s - p₁) (ζ - p₂)) = fun s => ∫⁻ ζ, F (s - p₁) ζ :=
    funext fun s => MeasureTheory.lintegral_sub_right_eq_self (fun ζ => F (s - p₁) ζ) p₂
  rw [h1]
  exact MeasureTheory.lintegral_sub_right_eq_self (fun s => ∫⁻ ζ, F s ζ) p₁

/-- The two-factor form used in `integral_shift_le`: the shift can be moved from the second
factor onto the first. -/
theorem lintegral_prod_shift_mul (A B : ℝ → ℝ → ENNReal) (p₁ p₂ : ℝ) :
    (∫⁻ s, ∫⁻ ζ, A s ζ * B (s - p₁) (ζ - p₂)) = ∫⁻ s, ∫⁻ ζ, A (s + p₁) (ζ + p₂) * B s ζ := by
  have h := lintegral_prod_shift (fun s ζ => A (s + p₁) (ζ + p₂) * B s ζ) p₁ p₂
  simpa [sub_add_cancel] using h

end Work.FTS.StrongEps.HkSqAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.IsEpsSolPQ.eq_zero_of_le_mul_intervalIntegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.IsEpsSolPQ

theorem eq_zero_of_le_mul_intervalIntegral {φ : ℝ → ℝ} {c T M : ℝ} (hc : 0 ≤ c) (hT : 0 ≤ T)
    (hM : 0 ≤ M) (hint : MeasureTheory.IntegrableOn φ (Set.Icc 0 T))
    (hnn : ∀ τ ∈ Set.Icc 0 T, 0 ≤ φ τ) (hbd : ∀ τ ∈ Set.Icc 0 T, φ τ ≤ M)
    (h : ∀ τ ∈ Set.Icc 0 T, φ τ ≤ c * ∫ s in (0 : ℝ)..τ, φ s) :
    ∀ τ ∈ Set.Icc 0 T, φ τ = 0 := by
  -- We prove the stronger statement `φ τ ≤ M * (c * τ) ^ n / n !` for every `n`,
  -- by induction on `n`: the inductive hypothesis is integrated against `h` and the
  -- exact value `∫_0^τ (c s)^n ds = c^n τ^{n+1}/(n+1)` produces the next factorial.
  -- Letting `n → ∞` (the bounds tend to `0`) and using `φ ≥ 0` gives `φ τ = 0`.
  have key : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      φ τ ≤ M * (c * τ) ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero =>
      intro τ hτ
      simpa using hbd τ hτ
    | succ n ih =>
      intro τ hτ
      have hτ0 : (0 : ℝ) ≤ τ := hτ.1
      have hτT : τ ≤ T := hτ.2
      -- `φ` is interval-integrable on `[0,τ]`
      have hIntφ : IntervalIntegrable φ MeasureTheory.volume (0 : ℝ) τ :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le hτ0).2
          (hint.mono_set (Set.Icc_subset_Icc_right hτT))
      -- the comparison function is continuous, hence interval-integrable
      have hIntg : IntervalIntegrable
          (fun s : ℝ => M * (c * s) ^ n / (n.factorial : ℝ)) MeasureTheory.volume (0 : ℝ) τ :=
        ((by fun_prop : ContinuousOn
            (fun s : ℝ => M * (c * s) ^ n / (n.factorial : ℝ)) (Set.Icc (0 : ℝ) τ))).intervalIntegrable_of_Icc hτ0
      -- the inductive hypothesis on `[0,τ]`
      have hpt : ∀ s ∈ Set.Icc (0 : ℝ) τ, φ s ≤ M * (c * s) ^ n / (n.factorial : ℝ) := by
        intro s hs
        exact ih s ⟨hs.1, le_trans hs.2 hτT⟩
      have hmono : (∫ s in (0 : ℝ)..τ, φ s)
          ≤ ∫ s in (0 : ℝ)..τ, M * (c * s) ^ n / (n.factorial : ℝ) :=
        intervalIntegral.integral_mono_on hτ0 hIntφ hIntg hpt
      -- the exact value of the comparison integral
      have hInt : (∫ s in (0 : ℝ)..τ, M * (c * s) ^ n / (n.factorial : ℝ))
          = M * c ^ n * τ ^ (n + 1) / ((n + 1).factorial : ℝ) := by
        have h1 : (∫ s in (0 : ℝ)..τ, M * (c * s) ^ n / (n.factorial : ℝ))
            = (M / (n.factorial : ℝ)) * c ^ n * (∫ s in (0 : ℝ)..τ, s ^ n) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro s _
          show M * (c * s) ^ n / (n.factorial : ℝ) = M / (n.factorial : ℝ) * c ^ n * s ^ n
          rw [mul_pow]; ring
        rw [h1, integral_pow]
        have h0 : (0 : ℝ) ^ (n + 1) = 0 := by simp
        rw [h0, sub_zero]
        have hfac : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        rw [hfac]
        field_simp
      calc φ τ ≤ c * ∫ s in (0 : ℝ)..τ, φ s := h τ hτ
        _ ≤ c * ∫ s in (0 : ℝ)..τ, M * (c * s) ^ n / (n.factorial : ℝ) :=
              mul_le_mul_of_nonneg_left hmono hc
        _ = c * (M * c ^ n * τ ^ (n + 1) / ((n + 1).factorial : ℝ)) := by rw [hInt]
        _ = M * (c * τ) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
              rw [mul_pow, pow_succ]; ring
  intro τ hτ
  -- the bounds `M * (c * τ)^n / n!` tend to `0`
  have hlim : Filter.Tendsto (fun n : ℕ => M * (c * τ) ^ n / (n.factorial : ℝ))
      Filter.atTop (nhds 0) := by
    have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (c * τ)).const_mul M
    simpa [mul_div_assoc] using h
  have hle0 : φ τ ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall (fun n => key n τ hτ))
  exact le_antisymm hle0 (hnn τ hτ)

end Work.FTS.StrongEps.IsEpsSolPQ
end
-- ===== merged: Submission.Work.FTS.StrongEps.KernAux.contDiff_partFst_partSnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.KernAux

/-- The first partial derivative `p ↦ ∂₁F p` of a smooth `F : ℝ × ℝ → ℝ` is smooth,
at every finite order. -/
theorem contDiff_partFst (F : ℝ × ℝ → ℝ) (hF : ∀ n : ℕ, ContDiff ℝ n F) :
    ∀ n : ℕ, ContDiff ℝ n (fun p : ℝ × ℝ => deriv (fun s : ℝ => F (s, p.2)) p.1) := by
  intro n
  -- `f p` is the slice `s ↦ F (s, p.2)`, whose uncurried form is `F` composed with the
  -- linear map `((x,y),s) ↦ (s,y)`; `g p = p.1` is the point at which it is evaluated
  -- and `k = 1` picks out the scalar derivative.
  have hf : ContDiff ℝ (n + 1) (Function.uncurry (fun (p : ℝ × ℝ) (s : ℝ) => F (s, p.2))) := by
    have h : Function.uncurry (fun (p : ℝ × ℝ) (s : ℝ) => F (s, p.2))
        = F ∘ (fun w : (ℝ × ℝ) × ℝ => (w.2, w.1.2)) := rfl
    rw [h]
    exact (hF (n + 1)).comp (by fun_prop)
  have hg : ContDiff ℝ n (fun p : ℝ × ℝ => p.1) := contDiff_fst
  have hk : ContDiff ℝ n (fun _ : ℝ × ℝ => (1 : ℝ)) := contDiff_const
  have hmain := ContDiff.fderiv_apply (𝕜 := ℝ) hf hg hk (le_refl ((n : WithTop ℕ∞) + 1))
  simpa only [fderiv_apply_one_eq_deriv] using hmain

/-- The second partial derivative `p ↦ ∂₂F p` of a smooth `F : ℝ × ℝ → ℝ` is smooth,
at every finite order. -/
theorem contDiff_partSnd (F : ℝ × ℝ → ℝ) (hF : ∀ n : ℕ, ContDiff ℝ n F) :
    ∀ n : ℕ, ContDiff ℝ n (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (p.1, t)) p.2) := by
  intro n
  have hf : ContDiff ℝ (n + 1) (Function.uncurry (fun (p : ℝ × ℝ) (s : ℝ) => F (p.1, s))) := by
    have h : Function.uncurry (fun (p : ℝ × ℝ) (s : ℝ) => F (p.1, s))
        = F ∘ (fun w : (ℝ × ℝ) × ℝ => (w.1.1, w.2)) := rfl
    rw [h]
    exact (hF (n + 1)).comp (by fun_prop)
  have hg : ContDiff ℝ n (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have hk : ContDiff ℝ n (fun _ : ℝ × ℝ => (1 : ℝ)) := contDiff_const
  have hmain := ContDiff.fderiv_apply (𝕜 := ℝ) hf hg hk (le_refl ((n : WithTop ℕ∞) + 1))
  simpa only [fderiv_apply_one_eq_deriv] using hmain

theorem contDiff_partFst_partSnd (F : ℝ × ℝ → ℝ) (hF : ∀ n : ℕ, ContDiff ℝ n F) :
    (∀ n : ℕ, ContDiff ℝ n (fun p : ℝ × ℝ => deriv (fun s : ℝ => F (s, p.2)) p.1)) ∧
    (∀ n : ℕ, ContDiff ℝ n (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (p.1, t)) p.2)) :=
  ⟨contDiff_partFst F hF, contDiff_partSnd F hF⟩

end Work.FTS.StrongEps.KernAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.KernAux.hasCompactSupport_partFst_partSnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.KernAux

/-- The first partial derivative of a compactly supported function again has compact support.

Reason: if `p` is outside the (closed) topological support of `F`, then `F` vanishes on a whole
neighbourhood of `p`, hence so does the slice `s ↦ F (s, p.2)` near `p.1`, so its derivative at
`p.1` vanishes.  Thus the support of `∂₁F` is contained in `tsupport F`. -/
theorem hasCompactSupport_deriv_fst (F : ℝ × ℝ → ℝ) (hF : HasCompactSupport F) :
    HasCompactSupport (fun p : ℝ × ℝ => deriv (fun s : ℝ => F (s, p.2)) p.1) := by
  refine HasCompactSupport.of_support_subset_isCompact hF ?_
  intro p hp
  rw [Function.mem_support] at hp
  by_contra hcon
  refine hp ?_
  have h0 : F =ᶠ[nhds p] 0 := notMem_tsupport_iff_eventuallyEq.mp hcon
  have hcont : ContinuousAt (fun s : ℝ => (s, p.2)) p.1 :=
    continuousAt_id.prodMk continuousAt_const
  have hg : (fun s : ℝ => F (s, p.2)) =ᶠ[nhds p.1] (fun _ => 0) :=
    hcont.tendsto.eventually h0
  rw [hg.deriv_eq, deriv_const]

/-- The second partial derivative of a compactly supported function again has compact support. -/
theorem hasCompactSupport_deriv_snd (F : ℝ × ℝ → ℝ) (hF : HasCompactSupport F) :
    HasCompactSupport (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (p.1, t)) p.2) := by
  refine HasCompactSupport.of_support_subset_isCompact hF ?_
  intro p hp
  rw [Function.mem_support] at hp
  by_contra hcon
  refine hp ?_
  have h0 : F =ᶠ[nhds p] 0 := notMem_tsupport_iff_eventuallyEq.mp hcon
  have hcont : ContinuousAt (fun t : ℝ => (p.1, t)) p.2 :=
    continuousAt_const.prodMk continuousAt_id
  have hg : (fun t : ℝ => F (p.1, t)) =ᶠ[nhds p.2] (fun _ => 0) :=
    hcont.tendsto.eventually h0
  rw [hg.deriv_eq, deriv_const]

theorem hasCompactSupport_partFst_partSnd (F : ℝ × ℝ → ℝ) (hF : HasCompactSupport F) :
    HasCompactSupport (fun p : ℝ × ℝ => deriv (fun s : ℝ => F (s, p.2)) p.1) ∧
    HasCompactSupport (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (p.1, t)) p.2) :=
  ⟨hasCompactSupport_deriv_fst F hF, hasCompactSupport_deriv_snd F hF⟩

end Work.FTS.StrongEps.KernAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.KernAux.integral_mul_partFst_eq_neg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integration by parts in the first coordinate on `ℝ × ℝ`

`Work.FTS.StrongEps.KernAux.integral_mul_partFst_eq_neg` is the two-dimensional
integration-by-parts identity

`∫ p, u p * ∂₁v p = - ∫ p, ∂₁u p * v p`

for `u : ℝ × ℝ → ℝ` of class `C¹` with **compact support** and an arbitrary
`C¹` function `v` (no support condition on `v`; everything is localised by the
support of `u`).

The proof is by Fubini together with the one-dimensional integration by parts
`∫ x, f x * deriv g x = - ∫ x, deriv f x * g x` for `f` of class `C¹` with
compact support, applied to every fibre `x ↦ u (x, y)`, `x ↦ v (x, y)`.

The file also provides the small fibre calculus used on the way, in particular
* `deriv_slice_fst_eq` : the derivative of the fibre is the Fréchet derivative
  applied to the unit vector `(1, 0)`,
* `continuous_deriv_slice_fst` : that fibre-derivative is continuous in `p`,
* `hasCompactSupport_slice_fst` : the fibre of a compactly supported function
  still has compact support,
* `hasCompactSupport_deriv_slice_fst` : the derivative of the fibre of a
  compactly supported function has compact support,
* `oneDim_ibp_compact` : the one-dimensional integration by parts on `ℝ`.
-/

namespace Work.FTS.StrongEps.KernAux

open MeasureTheory

open scoped Topology

/-- The derivative of the first-coordinate slice of a function on `ℝ × ℝ`
is the Fréchet derivative at the point, evaluated at the unit vector `(1, 0)`. -/
lemma deriv_slice_fst_eq {f : ℝ × ℝ → ℝ} {x y : ℝ} (hf : DifferentiableAt ℝ f (x, y)) :
    deriv (fun s : ℝ => f (s, y)) x = fderiv ℝ f (x, y) (1, 0) := by
  have hγ : HasDerivAt (fun s : ℝ => (s, y)) (1, 0) x := by
    simpa using (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y).hasDerivAt
  have h := hf.hasFDerivAt.comp_hasDerivAt x hγ
  simpa [Function.comp_def] using h.deriv

/-- For a `C¹` function on `ℝ × ℝ`, the function sending a point to the
derivative of its first-coordinate slice is continuous. -/
lemma continuous_deriv_slice_fst {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s : ℝ => f (s, p.2)) p.1) := by
  have h1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ f p (1, 0)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact h1.congr (fun p => (deriv_slice_fst_eq (x := p.1) (y := p.2)
    hf.differentiable_one.differentiableAt).symm)

/-- The derivative of the first-coordinate slice of a compactly supported `C¹`
function again has compact support. -/
lemma hasCompactSupport_deriv_slice_fst {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) :
    HasCompactSupport (fun p : ℝ × ℝ => deriv (fun s : ℝ => f (s, p.2)) p.1) := by
  refine hfs.mono' ?_
  intro p hp
  rw [Function.mem_support] at hp
  by_contra hcon
  have h0 : f =ᶠ[𝓝 p] (0 : ℝ × ℝ → ℝ) := notMem_tsupport_iff_eventuallyEq.mp hcon
  have hfd : fderiv ℝ f p = 0 := by
    rw [h0.fderiv_eq]; simp
  exact hp (by rw [deriv_slice_fst_eq (hf.differentiable_one.differentiableAt), hfd]; rfl)

/-- Every first-coordinate slice of a compactly supported function has compact
support. -/
lemma hasCompactSupport_slice_fst {f : ℝ × ℝ → ℝ} (hfs : HasCompactSupport f) (y : ℝ) :
    HasCompactSupport (fun x : ℝ => f (x, y)) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Prod.fst '' tsupport f) ?_ ?_
  · exact IsCompact.image hfs continuous_fst
  · intro x hx
    rw [Function.mem_support] at hx
    by_contra hcon
    exact hx ((notMem_tsupport_iff_eventuallyEq.mp
      (fun hmem => hcon ⟨(x, y), hmem, rfl⟩)).eq_of_nhds)

/-- Every first-coordinate slice of a smooth function on `ℝ × ℝ` is smooth. -/
lemma contDiff_slice_fst {f : ℝ × ℝ → ℝ} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (y : ℝ) :
    ContDiff ℝ n (fun x : ℝ => f (x, y)) := by
  have hφ : ContDiff ℝ n (fun x : ℝ => (x, y)) := contDiff_id.prodMk (contDiff_const (c := y))
  exact hf.comp hφ

/-- One-dimensional integration by parts on `ℝ` for a `C¹` function with
compact support. -/
theorem oneDim_ibp_compact {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) :
    ∫ x : ℝ, f x * deriv g x = - ∫ x : ℝ, deriv f x * g x :=
  MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun _x _ => (hf.differentiable_one.differentiableAt).hasDerivAt)
    (fun _x _ => (hg.differentiable_one.differentiableAt).hasDerivAt)
    ((hf.continuous.mul hg.continuous_deriv_one).integrable_of_hasCompactSupport (hfs.mul_right))
    ((hf.continuous_deriv_one.mul hg.continuous).integrable_of_hasCompactSupport (hfs.deriv.mul_right))
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hfs.mul_right))

theorem integral_mul_partFst_eq_neg {u v : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (hus : HasCompactSupport u) (hv : ContDiff ℝ 1 v) :
    ∫ p : ℝ × ℝ, u p * deriv (fun s : ℝ => v (s, p.2)) p.1
      = - ∫ p : ℝ × ℝ, deriv (fun s : ℝ => u (s, p.2)) p.1 * v p := by
  -- Both integrands are continuous with compact support, hence integrable.
  have hFint : Integrable (fun p : ℝ × ℝ => u p * deriv (fun s : ℝ => v (s, p.2)) p.1) :=
    (hu.continuous.mul (continuous_deriv_slice_fst hv)).integrable_of_hasCompactSupport
      (hus.mul_right)
  have hGint : Integrable (fun p : ℝ × ℝ => deriv (fun s : ℝ => u (s, p.2)) p.1 * v p) :=
    ((continuous_deriv_slice_fst hu).mul hv.continuous).integrable_of_hasCompactSupport
      ((hasCompactSupport_deriv_slice_fst hu hus).mul_right)
  -- Fubini, written in the order `∫ y ∫ x`.
  have hL : (∫ p : ℝ × ℝ, u p * deriv (fun s : ℝ => v (s, p.2)) p.1)
      = ∫ y : ℝ, ∫ x : ℝ, u (x, y) * deriv (fun s : ℝ => v (s, y)) x :=
    MeasureTheory.integral_prod_symm _ hFint
  have hR : (∫ p : ℝ × ℝ, deriv (fun s : ℝ => u (s, p.2)) p.1 * v p)
      = ∫ y : ℝ, ∫ x : ℝ, deriv (fun s : ℝ => u (s, y)) x * v (x, y) :=
    MeasureTheory.integral_prod_symm _ hGint
  rw [hL, hR]
  -- Integration by parts in `x`, fibre by fibre.
  have hfiber : ∀ y : ℝ, ∫ x : ℝ, u (x, y) * deriv (fun s : ℝ => v (s, y)) x
      = - ∫ x : ℝ, deriv (fun s : ℝ => u (s, y)) x * v (x, y) := fun y =>
    oneDim_ibp_compact (contDiff_slice_fst hu y) (hasCompactSupport_slice_fst hus y)
      (contDiff_slice_fst hv y)
  simp only [hfiber]
  rw [MeasureTheory.integral_neg]

end Work.FTS.StrongEps.KernAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.KernAux.integral_mul_partSnd_eq_neg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.KernAux

open MeasureTheory Filter

/-- The derivative of the second-coordinate slice of a function of two variables is the
Fréchet derivative applied to the direction `(0,1)`. -/
private lemma deriv_slice_snd_eq_fderiv {F : ℝ × ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ F (z, θ)) :
    deriv (fun θ' : ℝ => F (z, θ')) θ = fderiv ℝ F (z, θ) (0, 1) := by
  have h2 : HasFDerivAt (fun t : ℝ => (z, t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
    hasFDerivAt_prodMk_right z θ
  have h3 : HasDerivAt (fun t : ℝ => F (z, t))
      ((fderiv ℝ F (z, θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) θ :=
    (h.hasFDerivAt.comp θ h2).hasDerivAt
  rw [h3.deriv]; simp

/-- The second-coordinate slice of a `C¹` function is `C¹`. -/
private lemma contDiff_slice_snd {w : ℝ × ℝ → ℝ} (hw : ContDiff ℝ 1 w) (x : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => w (x, t)) :=
  hw.comp (contDiff_const.prodMk contDiff_id)

/-- The second-coordinate slice of a compactly supported function is compactly supported. -/
private lemma hasCompactSupport_slice_snd {w : ℝ × ℝ → ℝ} (hw : HasCompactSupport w)
    (x : ℝ) : HasCompactSupport (fun y : ℝ => w (x, y)) := by
  refine IsCompact.of_isClosed_subset (hw.isCompact.image continuous_snd) (isClosed_tsupport _)
    ?_
  refine closure_minimal ?_ (hw.isCompact.image continuous_snd).isClosed
  intro y hy
  exact ⟨(x, y), subset_closure (by simpa [Function.mem_support] using hy), rfl⟩

/-- **Integration by parts on `ℝ`, compactly supported case.**  For `a` of class `C¹` with
compact support and `b` of class `C¹`, we have `∫ a · b' = - ∫ a' · b`. -/
private lemma integral_mul_deriv_eq_neg_of_hasCompactSupport {a b : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (hca : HasCompactSupport a) (hb : ContDiff ℝ 1 b) :
    ∫ y : ℝ, a y * deriv b y = - ∫ y : ℝ, deriv a y * b y := by
  have hDa : Continuous (deriv a) := ha.continuous_deriv le_rfl
  have hDb : Continuous (deriv b) := hb.continuous_deriv le_rfl
  have hda : ∀ y : ℝ, HasDerivAt a (deriv a y) y := fun y =>
    (ha.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hdb : ∀ y : ℝ, HasDerivAt b (deriv b y) y := fun y =>
    (hb.differentiable (by norm_num)).differentiableAt.hasDerivAt
  refine MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := a) (v := b) (u' := deriv a) (v' := deriv b)
    (fun y _ => hda y) (fun y _ => hdb y) ?_ ?_ ?_
  · exact (ha.continuous.mul hDb).integrable_of_hasCompactSupport (hca.mul_right (f' := deriv b))
  · exact (hDa.mul hb.continuous).integrable_of_hasCompactSupport (hca.deriv.mul_right (f' := b))
  · exact (ha.continuous.mul hb.continuous).integrable_of_hasCompactSupport (hca.mul_right (f' := b))

/-- **Integration by parts in the second variable on `ℝ × ℝ`.**  If `u` is `C¹` with compact
support and `v` is `C¹`, then `∫ u ∂₂v = - ∫ (∂₂u) v`, where `∂₂` is the derivative of the
second-coordinate slice. -/
theorem integral_mul_partSnd_eq_neg {u v : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (hus : HasCompactSupport u) (hv : ContDiff ℝ 1 v) :
    ∫ p : ℝ × ℝ, u p * deriv (fun t : ℝ => v (p.1, t)) p.2
      = - ∫ p : ℝ × ℝ, deriv (fun t : ℝ => u (p.1, t)) p.2 * v p := by
  have hdu : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdv : Differentiable ℝ v := hv.differentiable (by norm_num)
  -- Step 1: identify the slice derivatives with Fréchet derivatives
  have hstep1 : (∫ p : ℝ × ℝ, u p * deriv (fun t : ℝ => v (p.1, t)) p.2)
      = ∫ p : ℝ × ℝ, u p * fderiv ℝ v p (0, 1) :=
    integral_congr_ae (Eventually.of_forall fun p =>
      congrArg (fun c => u p * c) (deriv_slice_snd_eq_fderiv hdv.differentiableAt))
  have hstep2 : (∫ p : ℝ × ℝ, deriv (fun t : ℝ => u (p.1, t)) p.2 * v p)
      = ∫ p : ℝ × ℝ, fderiv ℝ u p (0, 1) * v p :=
    integral_congr_ae (Eventually.of_forall fun p =>
      congrArg (fun c => c * v p) (deriv_slice_snd_eq_fderiv hdu.differentiableAt))
  rw [hstep1, hstep2]
  -- Step 2: both integrands are continuous with compact support
  have hFint : Integrable (fun p : ℝ × ℝ => u p * fderiv ℝ v p (0, 1)) :=
    (hu.continuous.mul ((hv.continuous_fderiv (by norm_num)).clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport
        (hus.mul_right (f' := fun p : ℝ × ℝ => fderiv ℝ v p (0, 1)))
  have hGint : Integrable (fun p : ℝ × ℝ => fderiv ℝ u p (0, 1) * v p) :=
    (((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hv.continuous)
      |>.integrable_of_hasCompactSupport
        ((HasCompactSupport.fderiv_apply ℝ hus (0, 1)).mul_right (f' := v))
  -- Step 3: Fubini
  have hFub1 : (∫ p : ℝ × ℝ, u p * fderiv ℝ v p (0, 1))
      = ∫ x : ℝ, ∫ y : ℝ, u (x, y) * fderiv ℝ v (x, y) (0, 1) := by
    have h : Integrable (fun p : ℝ × ℝ => u p * fderiv ℝ v p (0, 1)) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]; exact hFint
    have h2 := MeasureTheory.integral_prod (fun p : ℝ × ℝ => u p * fderiv ℝ v p (0, 1)) h
    rw [← Measure.volume_eq_prod] at h2
    exact h2
  have hFub2 : (∫ p : ℝ × ℝ, fderiv ℝ u p (0, 1) * v p)
      = ∫ x : ℝ, ∫ y : ℝ, fderiv ℝ u (x, y) (0, 1) * v (x, y) := by
    have h : Integrable (fun p : ℝ × ℝ => fderiv ℝ u p (0, 1) * v p) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]; exact hGint
    have h2 := MeasureTheory.integral_prod (fun p : ℝ × ℝ => fderiv ℝ u p (0, 1) * v p) h
    rw [← Measure.volume_eq_prod] at h2
    exact h2
  rw [hFub1, hFub2]
  -- Step 4: the one-dimensional identity, slice by slice
  have hslice : ∀ x : ℝ, (∫ y : ℝ, u (x, y) * fderiv ℝ v (x, y) (0, 1))
      = - ∫ y : ℝ, fderiv ℝ u (x, y) (0, 1) * v (x, y) := by
    intro x
    have key := integral_mul_deriv_eq_neg_of_hasCompactSupport
      (contDiff_slice_snd hu x) (hasCompactSupport_slice_snd hus x) (contDiff_slice_snd hv x)
    have e1 : (∫ y : ℝ, u (x, y) * fderiv ℝ v (x, y) (0, 1))
        = ∫ y : ℝ, u (x, y) * deriv (fun t : ℝ => v (x, t)) y :=
      integral_congr_ae (Eventually.of_forall fun y =>
        congrArg (fun c => u (x, y) * c)
          (deriv_slice_snd_eq_fderiv hdv.differentiableAt).symm)
    have e2 : (∫ y : ℝ, deriv (fun t : ℝ => u (x, t)) y * v (x, y))
        = ∫ y : ℝ, fderiv ℝ u (x, y) (0, 1) * v (x, y) :=
      integral_congr_ae (Eventually.of_forall fun y =>
        congrArg (fun c => c * v (x, y))
          (deriv_slice_snd_eq_fderiv hdu.differentiableAt))
    rw [e1, key, e2]
  -- Step 5: integrate the slicewise identity
  rw [show (∫ x : ℝ, ∫ y : ℝ, u (x, y) * fderiv ℝ v (x, y) (0, 1))
      = ∫ x : ℝ, -(∫ y : ℝ, fderiv ℝ u (x, y) (0, 1) * v (x, y)) from
    integral_congr_ae (Eventually.of_forall hslice)]
  rw [integral_neg]

end Work.FTS.StrongEps.KernAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12Sub4.ConvAdjDiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12Sub4

open MeasureTheory Set
open scoped Real Topology

/-- The unshifted-weight translation identity on `ℝ × ℝ`: integrating
`x ↦ G x₂ · F (x₁-p₁) (x₂-p₂)` gives the same value as integrating `x ↦ G (x₂+p₂) · F x₁ x₂`.
Immediate from the translation invariance of Lebesgue measure
(`MeasureTheory.integral_add_right_eq_self`), applied in the reverse direction. -/
theorem integral_shift_weight (G : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ∫ x : ℝ × ℝ, G x.2 * F (x.1 - p.1) (x.2 - p.2)
      = ∫ x : ℝ × ℝ, G (x.2 + p.2) * F x.1 x.2 := by
  have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
    (fun y : ℝ × ℝ => G y.2 * F (y.1 - p.1) (y.2 - p.2)) p
  have h2 : (fun y : ℝ × ℝ => G (y + p).2 * F ((y + p).1 - p.1) ((y + p).2 - p.2))
      = fun y : ℝ × ℝ => G (y.2 + p.2) * F y.1 y.2 := by
    funext y; simp
  rw [← h, h2]

/-- Joint integrability of `(x,p) ↦ k p · G x₂ · F (x₁-p₁) (x₂-p₂)` for the product Lebesgue
measure.  Because `k` is supported in the strip `|p₂| ≤ 1`, the shift bound on `G` and the
translation invariance of Lebesgue measure give a dominating product function, and Tonelli
(`MeasureTheory.integrable_prod_iff'`) turns the two iterated integrals into joint integrability.
The joint measurability of `(x,p) ↦ F (x₁-p₁) (x₂-p₂)` uses that `(x,p) ↦ x - p` is
quasi-measure-preserving (`MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant`). -/
theorem integrable_mollinger_shift (k : ℝ × ℝ → ℝ) (G : ℝ → ℝ) (F : ℝ → ℝ → ℝ)
    (hknn : ∀ p, 0 ≤ k p) (hki : MeasureTheory.Integrable k)
    (hksupp : ∀ p, k p ≠ 0 → |p.2| ≤ 1)
    (hGcont : Continuous G) (hGnn : ∀ ζ, 0 ≤ G ζ)
    (hGshift : ∀ ζ q : ℝ, |q| ≤ 1 → G (ζ + q) ≤ Real.exp (8 * |q|) * G ζ)
    (hFmeas : MeasureTheory.AEStronglyMeasurable (Function.uncurry F))
    (hFint : MeasureTheory.Integrable (fun x : ℝ × ℝ => G x.2 * |F x.1 x.2|)) :
    MeasureTheory.Integrable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (G z.1.2 * F (z.1.1 - z.2.1) (z.1.2 - z.2.2)))
      (volume.prod volume) := by
  have hF' : MeasureTheory.AEStronglyMeasurable (fun x : ℝ × ℝ => F x.1 x.2) volume := hFmeas
  have hGle : ∀ ζ : ℝ, ∀ q : ℝ, |q| ≤ 1 → G (ζ + q) ≤ Real.exp 8 * G ζ := by
    intro ζ q hq
    refine le_trans (hGshift ζ q hq) ?_
    apply mul_le_mul_of_nonneg_right _ (hGnn ζ)
    apply Real.exp_le_exp.mpr
    linarith [abs_nonneg q, hq]
  have hshift : MeasureTheory.AEStronglyMeasurable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => F (z.1.1 - z.2.1) (z.1.2 - z.2.2))
      (volume.prod volume) :=
    hF'.comp_quasiMeasurePreserving
      (MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant
        (μ := (volume : Measure (ℝ × ℝ))) (ν := (volume : Measure (ℝ × ℝ))))
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (G z.1.2 * F (z.1.1 - z.2.1) (z.1.2 - z.2.2)))
      (volume.prod volume) :=
    (hki.aestronglyMeasurable.comp_snd).mul
      (((hGcont.comp (continuous_snd.comp continuous_fst)).aestronglyMeasurable).mul hshift)
  rw [MeasureTheory.integrable_prod_iff' hmeas]
  constructor
  · refine Filter.Eventually.of_forall (fun p => ?_)
    change MeasureTheory.Integrable
      (fun x : ℝ × ℝ => k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))) volume
    by_cases hp : k p = 0
    · rw [show (fun x : ℝ × ℝ => k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))) = fun _ => 0 from by
        funext x; rw [hp]; ring]
      exact integrable_zero _ _ _
    · have hp2 : |p.2| ≤ 1 := hksupp p hp
      have hbase : MeasureTheory.Integrable
          (fun x : ℝ × ℝ => G (x.2 - p.2) * |F (x.1 - p.1) (x.2 - p.2)|) volume :=
        hFint.comp_sub_right p
      refine MeasureTheory.Integrable.mono'
        ((hbase.const_mul (Real.exp 8)).const_mul |k p|) ?_ ?_
      · exact aestronglyMeasurable_const.mul
          (((hGcont.comp continuous_snd).aestronglyMeasurable).mul
            (hF'.comp_quasiMeasurePreserving
              (MeasureTheory.measurePreserving_sub_right (volume : Measure (ℝ × ℝ))
                p).quasiMeasurePreserving))
      · refine Filter.Eventually.of_forall (fun x => ?_)
        have hGx : G x.2 ≤ Real.exp 8 * G (x.2 - p.2) := by
          have h1 := hGle (x.2 - p.2) p.2 hp2
          rwa [show (x.2 - p.2) + p.2 = x.2 from by ring] at h1
        have hFnn : 0 ≤ |F (x.1 - p.1) (x.2 - p.2)| := abs_nonneg _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hknn p), abs_mul, abs_of_nonneg (hGnn x.2)]
        have h2 : G x.2 * |F (x.1 - p.1) (x.2 - p.2)|
            ≤ Real.exp 8 * (G (x.2 - p.2) * |F (x.1 - p.1) (x.2 - p.2)|) := by
          nlinarith [hGx, hFnn]
        exact mul_le_mul_of_nonneg_left h2 (hknn p)
  · refine MeasureTheory.Integrable.mono'
      ((hki.abs).mul_const (Real.exp 8 * ∫ x : ℝ × ℝ, G x.2 * |F x.1 x.2|)) ?_ ?_
    · exact hmeas.prod_swap.norm.integral_prod_right'
    · refine Filter.Eventually.of_forall (fun p => ?_)
      change ‖∫ x : ℝ × ℝ, ‖k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))‖‖
        ≤ |k p| * (Real.exp 8 * ∫ x : ℝ × ℝ, G x.2 * |F x.1 x.2|)
      by_cases hp : k p = 0
      · rw [show (fun x : ℝ × ℝ => ‖k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))‖)
            = fun _ => 0 from by
          funext x; rw [hp]; simp]
        simp [hp]
      · have hp2 : |p.2| ≤ 1 := hksupp p hp
        have hpoint : ∀ x : ℝ × ℝ, ‖k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))‖
            = |k p| * (G x.2 * |F (x.1 - p.1) (x.2 - p.2)|) := by
          intro x
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hknn p), abs_mul, abs_of_nonneg (hGnn x.2)]
        have hI : ∫ x : ℝ × ℝ, ‖k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))‖
            = |k p| * ∫ x : ℝ × ℝ, G x.2 * |F (x.1 - p.1) (x.2 - p.2)| := by
          simp only [hpoint]
          rw [MeasureTheory.integral_const_mul]
        have hIpos : 0 ≤ ∫ x : ℝ × ℝ, G x.2 * |F (x.1 - p.1) (x.2 - p.2)| :=
          MeasureTheory.integral_nonneg (fun x => mul_nonneg (hGnn x.2) (abs_nonneg _))
        have hshift2 : ∫ x : ℝ × ℝ, G x.2 * |F (x.1 - p.1) (x.2 - p.2)|
            = ∫ x : ℝ × ℝ, G (x.2 + p.2) * |F x.1 x.2| := by
          have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
            (fun y : ℝ × ℝ => G y.2 * |F (y.1 - p.1) (y.2 - p.2)|) p
          have h2 : (fun y : ℝ × ℝ => G (y + p).2 * |F ((y + p).1 - p.1) ((y + p).2 - p.2)|)
              = fun y : ℝ × ℝ => G (y.2 + p.2) * |F y.1 y.2| := by
            funext y; simp
          rw [← h, h2]
        have hInt : MeasureTheory.Integrable
            (fun x : ℝ × ℝ => G (x.2 + p.2) * |F x.1 x.2|) volume := by
          have hb : MeasureTheory.AEStronglyMeasurable
              (fun x : ℝ × ℝ => G (x.2 + p.2) * F x.1 x.2) volume :=
            ((hGcont.comp (continuous_snd.add continuous_const)).aestronglyMeasurable).mul hF'
          have hm : MeasureTheory.Integrable
              (fun x : ℝ × ℝ => G (x.2 + p.2) * F x.1 x.2) volume := by
            refine MeasureTheory.Integrable.mono' (hFint.const_mul (Real.exp 8)) hb ?_
            refine Filter.Eventually.of_forall (fun x => ?_)
            have hGx : G (x.2 + p.2) ≤ Real.exp 8 * G x.2 := hGle x.2 p.2 hp2
            have hFnn : 0 ≤ |F x.1 x.2| := abs_nonneg _
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hGnn (x.2 + p.2))]
            have h2 : G (x.2 + p.2) * |F x.1 x.2| ≤ Real.exp 8 * (G x.2 * |F x.1 x.2|) := by
              nlinarith [hGx, hFnn]
            exact h2
          refine hm.abs.congr ?_
          refine Filter.Eventually.of_forall (fun x => ?_)
          simp only [abs_mul, abs_of_nonneg (hGnn (x.2 + p.2))]
        have hmon : ∫ x : ℝ × ℝ, G (x.2 + p.2) * |F x.1 x.2|
            ≤ Real.exp 8 * ∫ x : ℝ × ℝ, G x.2 * |F x.1 x.2| := by
          rw [← MeasureTheory.integral_const_mul]
          apply MeasureTheory.integral_mono hInt (hFint.const_mul (Real.exp 8))
          intro x
          have hGx : G (x.2 + p.2) ≤ Real.exp 8 * G x.2 := hGle x.2 p.2 hp2
          have hFnn : 0 ≤ |F x.1 x.2| := abs_nonneg _
          have h2 : G (x.2 + p.2) * |F x.1 x.2| ≤ Real.exp 8 * (G x.2 * |F x.1 x.2|) := by
            nlinarith [hGx, hFnn]
          exact h2
        rw [hI, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hIpos), hshift2]
        exact mul_le_mul_of_nonneg_left hmon (abs_nonneg _)

/-- Joint integrability of `(x,p) ↦ (k p · (G (x₂+p₂) - G x₂)) · F x₁ x₂`.  This is the
factorised case: the weight difference is bounded by `(e^8+1) G x₂` (thanks to the strip support
of `k` and the shift bound) and the two factors `|k p|` and `(e^8+1) G x₂ |F x₁ x₂|` are both
integrable. -/
theorem integrable_mollinger_weight (k : ℝ × ℝ → ℝ) (G : ℝ → ℝ) (F : ℝ → ℝ → ℝ)
    (hknn : ∀ p, 0 ≤ k p) (hki : MeasureTheory.Integrable k)
    (hksupp : ∀ p, k p ≠ 0 → |p.2| ≤ 1)
    (hGcont : Continuous G) (hGnn : ∀ ζ, 0 ≤ G ζ)
    (hGshift : ∀ ζ q : ℝ, |q| ≤ 1 → G (ζ + q) ≤ Real.exp (8 * |q|) * G ζ)
    (hFmeas : MeasureTheory.AEStronglyMeasurable (Function.uncurry F))
    (hFint : MeasureTheory.Integrable (fun x : ℝ × ℝ => G x.2 * |F x.1 x.2|)) :
    MeasureTheory.Integrable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (k z.2 * (G (z.1.2 + z.2.2) - G z.1.2)) * F z.1.1 z.1.2)
      (volume.prod volume) := by
  have hF' : MeasureTheory.AEStronglyMeasurable (fun x : ℝ × ℝ => F x.1 x.2) volume := hFmeas
  have hGle : ∀ ζ : ℝ, ∀ q : ℝ, |q| ≤ 1 → G (ζ + q) ≤ Real.exp 8 * G ζ := by
    intro ζ q hq
    refine le_trans (hGshift ζ q hq) ?_
    apply mul_le_mul_of_nonneg_right _ (hGnn ζ)
    apply Real.exp_le_exp.mpr
    linarith [abs_nonneg q, hq]
  have hdom : MeasureTheory.Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      |k z.2| * ((Real.exp 8 + 1) * (G z.1.2 * |F z.1.1 z.1.2|))) (volume.prod volume) :=
    (hki.abs.mul_prod (hFint.const_mul (Real.exp 8 + 1))).swap
  have hc : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => G (z.1.2 + z.2.2) - G z.1.2) := by fun_prop
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · exact ((hki.aestronglyMeasurable.comp_snd).mul hc.aestronglyMeasurable).mul hF'.comp_fst
  · refine Filter.Eventually.of_forall (fun z => ?_)
    change ‖(k z.2 * (G (z.1.2 + z.2.2) - G z.1.2)) * F z.1.1 z.1.2‖
      ≤ |k z.2| * ((Real.exp 8 + 1) * (G z.1.2 * |F z.1.1 z.1.2|))
    by_cases hp : k z.2 = 0
    · rw [hp, zero_mul, zero_mul, norm_zero]
      exact mul_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg (hGnn _) (abs_nonneg _)))
    · have hz2 : |z.2.2| ≤ 1 := hksupp z.2 hp
      have hd : |G (z.1.2 + z.2.2) - G z.1.2| ≤ (Real.exp 8 + 1) * G z.1.2 := by
        have h1 : G (z.1.2 + z.2.2) ≤ Real.exp 8 * G z.1.2 := hGle z.1.2 z.2.2 hz2
        have h2 : |G (z.1.2 + z.2.2) - G z.1.2| ≤ G (z.1.2 + z.2.2) + G z.1.2 := by
          rw [abs_sub_le_iff]
          exact ⟨by linarith [hGnn (z.1.2 + z.2.2), hGnn z.1.2],
                 by linarith [hGnn (z.1.2 + z.2.2), hGnn z.1.2]⟩
        nlinarith [h1, h2]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hknn z.2)]
      have hFnn : 0 ≤ |F z.1.1 z.1.2| := abs_nonneg _
      have hstep : |G (z.1.2 + z.2.2) - G z.1.2| * |F z.1.1 z.1.2| ≤
          (Real.exp 8 + 1) * (G z.1.2 * |F z.1.1 z.1.2|) := by
        calc |G (z.1.2 + z.2.2) - G z.1.2| * |F z.1.1 z.1.2|
            ≤ ((Real.exp 8 + 1) * G z.1.2) * |F z.1.1 z.1.2| :=
              mul_le_mul_of_nonneg_right hd hFnn
          _ = (Real.exp 8 + 1) * (G z.1.2 * |F z.1.1 z.1.2|) := by ring
      calc (k z.2 * |G (z.1.2 + z.2.2) - G z.1.2|) * |F z.1.1 z.1.2|
          = k z.2 * (|G (z.1.2 + z.2.2) - G z.1.2| * |F z.1.1 z.1.2|) := by ring
        _ ≤ k z.2 * ((Real.exp 8 + 1) * (G z.1.2 * |F z.1.1 z.1.2|)) :=
            mul_le_mul_of_nonneg_left hstep (hknn z.2)

/-- **Adjointness of the mollifier against a `s`-independent weight, difference form** (generic
measure theory, Mathlib only).  For a nonnegative integrable kernel `k` of mass `1` supported in the
strip `|p₂| ≤ 1`, a continuous nonnegative weight `G` with `G (ζ+q) ≤ e^{8|q|} G ζ` for `|q| ≤ 1`,
and an a.e. strongly measurable `F` whose `G`-weighted absolute value is integrable,

  `∫_s ∫_ζ G(ζ) ((∫_p k p · F (s-p₁) (ζ-p₂)) - F(s,ζ))
     = ∫_s ∫_ζ (∫_p k p · (G (ζ+p₂) - G ζ)) F(s,ζ)`.

The subtraction of `F(s,ζ)` is performed *inside* the outer integral, so no measurability of the
weight-convolution `ζ ↦ ∫p, k p G(ζ+p₂)` is ever needed (the `p`-integrals stay at the outermost
level).

Hints: the LHS equals `∫∫ G(ζ)(∫p k p F(s-p₁,ζ-p₂)) - ∫∫ G·F` (`MeasureTheory.integral_sub`; both
terms are integrable — for the first, `(p,x) ↦ k p · G x.2 · |F (x.1-p.1) (x.2-p.2)|` is integrable
by Tonelli, since integrating it over `p` gives
`∫p k p ∫∫ G(ζ)|F(s-p₁,ζ-p₂)| ≤ e^8 ‖k‖₁ ∫∫ G|F| < ∞` by the shift bound).  Then write the first
term as `∫p k p ∫∫G(ζ)F(s-p₁,ζ-p₂)` and the second as `∫p k p ∫∫G(ζ)F(s,ζ)` (using `hk1` and
`MeasureTheory.integral_mul_const`), combine the two `p`-integrals with `MeasureTheory.integral_sub`,
use the translation invariance of Lebesgue measure
(`MeasureTheory.integral_sub_right_eq_self`, twice) on the first term, and finish with Fubini. -/
theorem ConvAdjDiff (k : ℝ × ℝ → ℝ) (G : ℝ → ℝ) (F : ℝ → ℝ → ℝ)
    (hknn : ∀ p, 0 ≤ k p) (hki : MeasureTheory.Integrable k) (hk1 : ∫ p : ℝ × ℝ, k p = 1)
    (hksupp : ∀ p, k p ≠ 0 → |p.2| ≤ 1)
    (hGcont : Continuous G) (hGnn : ∀ ζ, 0 ≤ G ζ)
    (hGshift : ∀ ζ q : ℝ, |q| ≤ 1 → G (ζ + q) ≤ Real.exp (8 * |q|) * G ζ)
    (hFmeas : MeasureTheory.AEStronglyMeasurable (Function.uncurry F))
    (hFint : MeasureTheory.Integrable (fun x : ℝ × ℝ => G x.2 * |F x.1 x.2|)) :
    ∫ s, ∫ ζ, G ζ * ((∫ p : ℝ × ℝ, k p * F (s - p.1) (ζ - p.2)) - F s ζ)
      = ∫ s, ∫ ζ, (∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)) * F s ζ := by
  have hF' : MeasureTheory.AEStronglyMeasurable (fun x : ℝ × ℝ => F x.1 x.2) volume := hFmeas
  have hGle : ∀ ζ : ℝ, ∀ q : ℝ, |q| ≤ 1 → G (ζ + q) ≤ Real.exp 8 * G ζ := by
    intro ζ q hq
    refine le_trans (hGshift ζ q hq) ?_
    apply mul_le_mul_of_nonneg_right _ (hGnn ζ)
    apply Real.exp_le_exp.mpr
    linarith [abs_nonneg q, hq]
  -- integrability of `x ↦ G x₂ F x₁ x₂` (without the absolute value)
  have hGFint : MeasureTheory.Integrable (fun x : ℝ × ℝ => G x.2 * F x.1 x.2) volume := by
    refine MeasureTheory.Integrable.mono' hFint ?_ ?_
    · exact ((hGcont.comp continuous_snd).aestronglyMeasurable).mul hF'
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hGnn x.2)]
  -- the three joint integrability facts
  have hfL := integrable_mollinger_shift k G F hknn hki hksupp hGcont hGnn hGshift hFmeas hFint
  have hfB : MeasureTheory.Integrable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (G z.1.2 * F z.1.1 z.1.2))
      (volume.prod volume) := (hki.mul_prod hGFint).swap
  have hfC := integrable_mollinger_weight k G F hknn hki hksupp hGcont hGnn hGshift hFmeas hFint
  -- the `p`-slices of the three integrands, integrated in `x`
  have hA : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => ∫ p : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))) volume :=
    MeasureTheory.Integrable.integral_prod_left
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        k z.2 * (G z.1.2 * F (z.1.1 - z.2.1) (z.1.2 - z.2.2))) hfL
  have hB : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => ∫ p : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)) volume :=
    MeasureTheory.Integrable.integral_prod_left
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (G z.1.2 * F z.1.1 z.1.2)) hfB
  have hC : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => ∫ p : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2) volume :=
    MeasureTheory.Integrable.integral_prod_left
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        (k z.2 * (G (z.1.2 + z.2.2) - G z.1.2)) * F z.1.1 z.1.2) hfC
  -- pointwise identities for the `p`-slices
  have hpL : ∀ x : ℝ × ℝ, (∫ p : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
      = G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)) := by
    intro x
    rw [show (fun p : ℝ × ℝ => k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
        = fun p : ℝ × ℝ => G x.2 * (k p * F (x.1 - p.1) (x.2 - p.2)) from by
      funext p; ring,
      MeasureTheory.integral_const_mul]
  have hpB : ∀ x : ℝ × ℝ, (∫ p : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)) = G x.2 * F x.1 x.2 := by
    intro x
    rw [MeasureTheory.integral_mul_const, hk1]
    ring
  have hpC : ∀ x : ℝ × ℝ,
      (∫ p : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2)
        = (∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 :=
    fun x => MeasureTheory.integral_mul_const _ _
  -- integrability of the `A`, `B`, `C` integrands
  have hA' : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2))) volume :=
    hA.congr (Filter.Eventually.of_forall hpL)
  have hC' : MeasureTheory.Integrable
      (fun x : ℝ × ℝ =>
        (∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2) volume :=
    hC.congr (Filter.Eventually.of_forall hpC)
  -- the two `p`-integrals of the slices
  have hAp : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ∫ x : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))) volume :=
    MeasureTheory.Integrable.integral_prod_right
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        k z.2 * (G z.1.2 * F (z.1.1 - z.2.1) (z.1.2 - z.2.2))) hfL
  have hBp : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ∫ x : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)) volume :=
    MeasureTheory.Integrable.integral_prod_right
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => k z.2 * (G z.1.2 * F z.1.1 z.1.2)) hfB
  -- the slice identity, for every `p`
  have hpFC : ∀ p : ℝ × ℝ,
      (∫ x : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2)
        = (∫ x : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
          - (∫ x : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)) := by
    intro p
    by_cases hp : k p = 0
    · rw [show (fun x : ℝ × ℝ => (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2) = fun _ => 0 from by
          funext x; rw [hp]; ring,
        show (fun x : ℝ × ℝ => k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))) = fun _ => 0 from by
          funext x; rw [hp]; ring,
        show (fun x : ℝ × ℝ => k p * (G x.2 * F x.1 x.2)) = fun _ => 0 from by
          funext x; rw [hp]; ring]
      simp
    · have hp2 : |p.2| ≤ 1 := hksupp p hp
      -- integrability of the shifted weight
      have hshiftInt : MeasureTheory.Integrable
          (fun x : ℝ × ℝ => G (x.2 + p.2) * F x.1 x.2) volume := by
        have hb : MeasureTheory.AEStronglyMeasurable
            (fun x : ℝ × ℝ => G (x.2 + p.2) * F x.1 x.2) volume :=
          ((hGcont.comp (continuous_snd.add continuous_const)).aestronglyMeasurable).mul hF'
        refine MeasureTheory.Integrable.mono' (hFint.const_mul (Real.exp 8)) hb ?_
        refine Filter.Eventually.of_forall (fun x => ?_)
        have hGx : G (x.2 + p.2) ≤ Real.exp 8 * G x.2 := hGle x.2 p.2 hp2
        have hFnn : 0 ≤ |F x.1 x.2| := abs_nonneg _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hGnn (x.2 + p.2))]
        nlinarith [hGx, hFnn]
      rw [show (fun x : ℝ × ℝ => (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2)
          = fun x : ℝ × ℝ => k p * ((G (x.2 + p.2) - G x.2) * F x.1 x.2) from by
        funext x; ring,
        MeasureTheory.integral_const_mul,
        show (fun x : ℝ × ℝ => (G (x.2 + p.2) - G x.2) * F x.1 x.2)
          = fun x : ℝ × ℝ => G (x.2 + p.2) * F x.1 x.2 - G x.2 * F x.1 x.2 from by
        funext x; ring,
        MeasureTheory.integral_sub hshiftInt hGFint]
      rw [show (∫ x : ℝ × ℝ, G (x.2 + p.2) * F x.1 x.2)
          = ∫ x : ℝ × ℝ, G x.2 * F (x.1 - p.1) (x.2 - p.2) from
        (integral_shift_weight G F p).symm,
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
      ring
  -- the main chain
  have hmain : (∫ x : ℝ × ℝ, G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)))
        - (∫ x : ℝ × ℝ, G x.2 * F x.1 x.2)
      = ∫ x : ℝ × ℝ, (∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 := by
    have hsL : (∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
        = ∫ p : ℝ × ℝ, ∫ x : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)) :=
      MeasureTheory.integral_integral_swap
        (f := fun x p : ℝ × ℝ => k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))) hfL
    have hsB : (∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * (G x.2 * F x.1 x.2))
        = ∫ p : ℝ × ℝ, ∫ x : ℝ × ℝ, k p * (G x.2 * F x.1 x.2) :=
      MeasureTheory.integral_integral_swap
        (f := fun x p : ℝ × ℝ => k p * (G x.2 * F x.1 x.2)) hfB
    have hsC : (∫ p : ℝ × ℝ, ∫ x : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2)
        = ∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 :=
      (MeasureTheory.integral_integral_swap
        (f := fun x p : ℝ × ℝ => (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2) hfC).symm
    calc (∫ x : ℝ × ℝ, G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)))
          - (∫ x : ℝ × ℝ, G x.2 * F x.1 x.2)
        = (∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
          - (∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)) := by
          rw [show (∫ x : ℝ × ℝ, G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)))
                = ∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2))
              from integral_congr_ae (Filter.Eventually.of_forall (fun x => (hpL x).symm)),
            show (∫ x : ℝ × ℝ, G x.2 * F x.1 x.2)
                = ∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)
              from integral_congr_ae (Filter.Eventually.of_forall (fun x => (hpB x).symm))]
      _ = (∫ p : ℝ × ℝ, ∫ x : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
          - (∫ p : ℝ × ℝ, ∫ x : ℝ × ℝ, k p * (G x.2 * F x.1 x.2)) := by rw [hsL, hsB]
      _ = ∫ p : ℝ × ℝ, ((∫ x : ℝ × ℝ, k p * (G x.2 * F (x.1 - p.1) (x.2 - p.2)))
            - (∫ x : ℝ × ℝ, k p * (G x.2 * F x.1 x.2))) :=
          (MeasureTheory.integral_sub hAp hBp).symm
      _ = ∫ p : ℝ × ℝ, ∫ x : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 :=
          integral_congr_ae (Filter.Eventually.of_forall (fun p => (hpFC p).symm))
      _ = ∫ x : ℝ × ℝ, ∫ p : ℝ × ℝ, (k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 := hsC
      _ = ∫ x : ℝ × ℝ, (∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 :=
          integral_congr_ae (Filter.Eventually.of_forall hpC)
  -- Fubini reductions of the two sides of the goal
  have hABint : MeasureTheory.Integrable
      (fun x : ℝ × ℝ =>
        G x.2 * ((∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)) - F x.1 x.2)) volume := by
    refine (hA'.sub hGFint).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Pi.sub_apply]
    ring
  have hLHS : (∫ s, ∫ ζ, G ζ * ((∫ p : ℝ × ℝ, k p * F (s - p.1) (ζ - p.2)) - F s ζ))
      = ∫ x : ℝ × ℝ,
          G x.2 * ((∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)) - F x.1 x.2) :=
    MeasureTheory.integral_integral (μ := volume) (ν := volume)
      (f := fun s ζ => G ζ * ((∫ p : ℝ × ℝ, k p * F (s - p.1) (ζ - p.2)) - F s ζ)) hABint
  have hRHS : (∫ s, ∫ ζ, (∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)) * F s ζ)
      = ∫ x : ℝ × ℝ,
          (∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2 :=
    MeasureTheory.integral_integral (μ := volume) (ν := volume)
      (f := fun s ζ => (∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)) * F s ζ) hC'
  rw [hLHS, hRHS]
  have hsub : (∫ x : ℝ × ℝ, G x.2 * ((∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2))
        - F x.1 x.2))
      = (∫ x : ℝ × ℝ, G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2)))
        - (∫ x : ℝ × ℝ, G x.2 * F x.1 x.2) := by
    rw [show (fun x : ℝ × ℝ => G x.2 * ((∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2))
          - F x.1 x.2))
        = fun x : ℝ × ℝ => G x.2 * (∫ p : ℝ × ℝ, k p * F (x.1 - p.1) (x.2 - p.2))
          - G x.2 * F x.1 x.2 from by funext x; ring,
      MeasureTheory.integral_sub hA' hGFint]
  rw [hsub, hmain]

end Work.FTS.StrongEps.L12Sub4
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12Sub4.KernelWeightSub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12Sub4

open MeasureTheory

/-- **The `ε`-error of a probability kernel on a smooth `ζ`-independent weight** (generic, Mathlib
only).  For a nonnegative integrable kernel `k` of mass `1`, supported in the strip `|p₂| ≤ ε ≤ 1`,
and a continuous weight `G` whose relative oscillation on the unit interval is bounded by `B`
(`|G (ζ+q) - G ζ| ≤ B|q| G ζ` for `|q| ≤ 1`),

  `|∫ p, k p · G (ζ + p.2) - G ζ| ≤ B ε G ζ`  for every `ζ`.

Hints: `∫ p, k p G(ζ+p.2) - G ζ = ∫ p, k p (G(ζ+p.2) - G ζ)` (using `∫ k = 1` and
`MeasureTheory.integral_sub`).  Integrability: on the strip `|p₂| ≤ ε` the factor `G(ζ+p₂)` is bounded
by its maximum `M` on the compact interval `[ζ-ε, ζ+ε]` (continuity), so `|k p · G(ζ+p₂)| ≤ M ‖k p‖`
which is integrable; and `p ↦ k p * G ζ` is a constant multiple of `k`.  Then `‖∫‖ ≤ ∫‖·‖` and the
pointwise bound `|G(ζ+p.2) - G ζ| ≤ B |p.2| G ζ ≤ B ε G ζ` valid wherever `k p ≠ 0`. -/
theorem KernelWeightSub (k : ℝ × ℝ → ℝ) (G : ℝ → ℝ) {ε B : ℝ}
    (hknn : ∀ p, 0 ≤ k p) (hki : MeasureTheory.Integrable k) (hk1 : ∫ p : ℝ × ℝ, k p = 1)
    (hksupp : ∀ p, k p ≠ 0 → |p.2| ≤ ε)
    (hGcont : Continuous G) (hB : 0 ≤ B)
    (hGdiff : ∀ ζ q : ℝ, |q| ≤ 1 → |G (ζ + q) - G ζ| ≤ B * |q| * G ζ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ ζ : ℝ, |(∫ p : ℝ × ℝ, k p * G (ζ + p.2)) - G ζ| ≤ B * ε * G ζ := by
  have hεnn : (0 : ℝ) ≤ ε := le_of_lt hε0
  intro ζ
  by_cases hB0 : B = 0
  · -- `B = 0`: `G` is constant on `[ζ-1, ζ+1]`, so on the support of `k` the factor `G (ζ+p.2)`
    -- equals `G ζ`; the two integrals coincide and the claim reads `0 ≤ 0`.
    have hconst : ∀ p : ℝ × ℝ, k p * G (ζ + p.2) = k p * G ζ := by
      intro p
      by_cases hp : k p = 0
      · rw [hp, zero_mul, zero_mul]
      · have hp2 : |p.2| ≤ 1 := le_trans (hksupp p hp) hε1
        have h2 : |G (ζ + p.2) - G ζ| ≤ 0 := by simpa [hB0] using hGdiff ζ p.2 hp2
        have hEq : G (ζ + p.2) = G ζ :=
          sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h2 (abs_nonneg _)))
        rw [hEq]
    have hI : (∫ p : ℝ × ℝ, k p * G (ζ + p.2)) = G ζ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hconst),
        MeasureTheory.integral_mul_const, hk1, one_mul]
    rw [hI, sub_self, abs_zero, hB0]
    simp
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    -- The oscillation hypothesis forces `G ζ ≥ 0` (evaluate at `q = 1/2`).
    have hGζ : 0 ≤ G ζ := by
      have h := hGdiff ζ (1 / 2) (by norm_num)
      have h1 : |(1 : ℝ) / 2| = (1 : ℝ) / 2 := by norm_num
      rw [h1] at h
      exact nonneg_of_mul_nonneg_right (le_trans (abs_nonneg _) h)
        (mul_pos hBpos (by norm_num))
    -- Pointwise domination of the difference integrand on the support of `k`.
    have hpt : ∀ p : ℝ × ℝ, k p * |G (ζ + p.2) - G ζ| ≤ (B * ε * G ζ) * k p := by
      intro p
      by_cases hp : k p = 0
      · rw [hp, zero_mul, mul_zero]
      · have hp2 : |p.2| ≤ ε := hksupp p hp
        have hp2' : |p.2| ≤ 1 := le_trans hp2 hε1
        have h1 : |G (ζ + p.2) - G ζ| ≤ B * |p.2| * G ζ := hGdiff ζ p.2 hp2'
        have h2 : B * |p.2| * G ζ ≤ B * ε * G ζ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hB) hGζ
        have h3 : |G (ζ + p.2) - G ζ| ≤ B * ε * G ζ := le_trans h1 h2
        calc k p * |G (ζ + p.2) - G ζ| ≤ k p * (B * ε * G ζ) :=
              mul_le_mul_of_nonneg_left h3 (hknn p)
          _ = (B * ε * G ζ) * k p := by ring
    have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => (B * ε * G ζ) * k p) :=
      hki.const_mul _
    have hInt2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * (G (ζ + p.2) - G ζ)) := by
      refine MeasureTheory.Integrable.mono' hInt ?_ ?_
      · have hc : Continuous (fun p : ℝ × ℝ => G (ζ + p.2) - G ζ) :=
          (hGcont.comp (continuous_const.add continuous_snd)).sub continuous_const
        exact hki.aestronglyMeasurable.mul hc.aestronglyMeasurable
      · filter_upwards with p
        have := hpt p
        rwa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hknn p)]
    have hInt3 : MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G (ζ + p.2)) := by
      have h := hInt2.add (hki.mul_const (G ζ))
      refine h.congr ?_
      filter_upwards with p
      simp only [Pi.add_apply]
      ring
    -- Subtract `G ζ = ∫ p, k p * G ζ` and rewrite the difference as a single integral.
    have hI : (∫ p : ℝ × ℝ, k p * G (ζ + p.2)) - G ζ
        = ∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ) := by
      have h2 : (∫ p : ℝ × ℝ, k p * G ζ) = G ζ := by
        rw [MeasureTheory.integral_mul_const, hk1, one_mul]
      calc (∫ p : ℝ × ℝ, k p * G (ζ + p.2)) - G ζ
          = (∫ p : ℝ × ℝ, k p * G (ζ + p.2)) - ∫ p : ℝ × ℝ, k p * G ζ := by rw [h2]
        _ = ∫ p : ℝ × ℝ, (k p * G (ζ + p.2) - k p * G ζ) := by
              rw [MeasureTheory.integral_sub hInt3 (hki.mul_const (G ζ))]
        _ = ∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with p
              ring
    rw [hI]
    have h1 : ‖∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)‖
        ≤ ∫ p : ℝ × ℝ, ‖k p * (G (ζ + p.2) - G ζ)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    have h2 : ∫ p : ℝ × ℝ, ‖k p * (G (ζ + p.2) - G ζ)‖
        ≤ ∫ p : ℝ × ℝ, (B * ε * G ζ) * k p := by
      refine MeasureTheory.integral_mono_ae hInt2.norm hInt ?_
      filter_upwards with p
      have := hpt p
      rwa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hknn p)]
    have h3 : ∫ p : ℝ × ℝ, (B * ε * G ζ) * k p = B * ε * G ζ := by
      rw [MeasureTheory.integral_const_mul, hk1, mul_one]
    rw [← Real.norm_eq_abs]
    exact le_trans h1 (le_trans h2 (le_of_eq h3))

end Work.FTS.StrongEps.L12Sub4
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.ae_integrableOn_slice_of_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A.e. integrability of the slices of `w`, from two lintegral bounds

`Work.FTS.StrongEps.LocUnif.D5.ae_integrableOn_slice_of_bounds`: if on the rectangle
`Icc a b ×ˢ Icc c d` the `ENNReal.ofReal`-lintegrals of `W ^ 2` and of `|W - w|` are bounded
(by `M` and by `ε` respectively), then for almost every `θ ∈ Icc c d` the `z`-slice
`z ↦ w z θ` is integrable on `Icc a b`.

The proof needs no regularity beyond a.e. measurability.  The pointwise bound `|x| ≤ 1 + x ^ 2`
turns the two hypotheses into the finiteness of the `L¹`-norms of `W` and of `W - w` for the
product `(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))` (the restricted measures
are finite, so the constant `1` is integrable), whence `w = W - (W - w)` is integrable for that
product measure.  Tonelli/Fubini in the form `Integrable.prod_left_ae` then yields integrability
of the left slices for a.e. right coordinate.  Finally
`Measure.prod_restrict` identifies `(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))`
with `volume.restrict (Icc a b ×ˢ Icc c d)`.
-/

set_option linter.unusedVariables false

open MeasureTheory

namespace Work.FTS.StrongEps.LocUnif.D5

/-- If the `ENNReal.ofReal`-lintegrals of `W ^ 2` and of `|W - w|` against a product of finite
measures are bounded, then `w`, viewed as a function on the product, is integrable; consequently
its left slices are a.e. integrable. -/
theorem integrable_uncurry_of_lintegral_bounds {μA μB : Measure ℝ} [SFinite μA] [SFinite μB]
    [IsFiniteMeasure μA] [IsFiniteMeasure μB]
    {W w : ℝ → ℝ → ℝ} {M ε : ℝ}
    (hWm : AEMeasurable (Function.uncurry W) (μA.prod μB))
    (hwm : AEMeasurable (Function.uncurry w) (μA.prod μB))
    (hW2 : ∫⁻ p, ENNReal.ofReal ((W p.1 p.2) ^ 2) ∂(μA.prod μB) ≤ ENNReal.ofReal M)
    (hdiff : ∫⁻ p, ENNReal.ofReal |W p.1 p.2 - w p.1 p.2| ∂(μA.prod μB)
      ≤ ENNReal.ofReal ε) :
    ∀ᵐ θ ∂μB, Integrable (fun z => w z θ) μA := by
  -- `W ^ 2` is integrable for the product measure
  have hsq_meas : AEMeasurable (fun p : ℝ × ℝ => (W p.1 p.2) ^ 2) (μA.prod μB) :=
    Measurable.comp_aemeasurable (g := fun x : ℝ => x ^ 2) (by fun_prop) hWm
  have hIntV2 : Integrable (fun p : ℝ × ℝ => (W p.1 p.2) ^ 2) (μA.prod μB) := by
    refine ⟨hsq_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => sq_nonneg _)]
    exact lt_of_le_of_lt hW2 ENNReal.ofReal_lt_top
  -- `|W - w|` is integrable for the product measure
  have hdiff_meas : AEMeasurable (fun p : ℝ × ℝ => |W p.1 p.2 - w p.1 p.2|) (μA.prod μB) :=
    Measurable.comp_aemeasurable (g := fun x : ℝ => |x|) (by fun_prop) (hWm.sub hwm)
  have hIntD : Integrable (fun p : ℝ × ℝ => |W p.1 p.2 - w p.1 p.2|) (μA.prod μB) := by
    refine ⟨hdiff_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => abs_nonneg _)]
    exact lt_of_le_of_lt hdiff ENNReal.ofReal_lt_top
  -- `W` is integrable for the product measure, by `|x| ≤ 1 + x ^ 2`
  have hIntW : Integrable (fun p : ℝ × ℝ => W p.1 p.2) (μA.prod μB) := by
    refine Integrable.mono (g := fun p : ℝ × ℝ => 1 + (W p.1 p.2) ^ 2)
      ((integrable_const 1).add hIntV2) hWm.aestronglyMeasurable ?_
    filter_upwards with p
    have h1 : 0 ≤ 1 + (W p.1 p.2) ^ 2 := by nlinarith [sq_nonneg (W p.1 p.2)]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1]
    nlinarith [abs_nonneg (W p.1 p.2), sq_nonneg (|W p.1 p.2| - 1 / 2), sq_abs (W p.1 p.2)]
  have hIntWdiff : Integrable (fun p : ℝ × ℝ => W p.1 p.2 - w p.1 p.2) (μA.prod μB) :=
    ⟨(hWm.sub hwm).aestronglyMeasurable,
      hIntD.hasFiniteIntegral.mono (Filter.Eventually.of_forall fun p => by
        simp [Real.norm_eq_abs])⟩
  -- `w = W - (W - w)`
  have hIntw : Integrable (fun p : ℝ × ℝ => w p.1 p.2) (μA.prod μB) := by
    refine (hIntW.sub hIntWdiff).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.sub_apply]
    ring
  exact hIntw.prod_left_ae

theorem ae_integrableOn_slice_of_bounds {a b c d M ε : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hM : 0 ≤ M) (hε : 0 ≤ ε) {W : ℝ → ℝ → ℝ} {w : ℝ → ℝ → ℝ}
    (hWm : AEMeasurable (Function.uncurry W)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hwm : AEMeasurable (Function.uncurry w)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hW2 : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
      ENNReal.ofReal ((W p.1 p.2) ^ 2) ≤ ENNReal.ofReal M)
    (hdiff : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
      ENNReal.ofReal |W p.1 p.2 - w p.1 p.2| ≤ ENNReal.ofReal ε) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc c d)),
      MeasureTheory.IntegrableOn (fun z => w z θ) (Set.Icc a b) MeasureTheory.volume := by
  -- the product of the restrictions is the restriction of the product measure
  have hμ : (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))
      = volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) := Measure.prod_restrict _ _
  have h := integrable_uncurry_of_lintegral_bounds
    (μA := volume.restrict (Set.Icc a b)) (μB := volume.restrict (Set.Icc c d))
    (by rw [hμ]; exact hWm) (by rw [hμ]; exact hwm)
    (by rw [hμ]; exact hW2) (by rw [hμ]; exact hdiff)
  simpa only [MeasureTheory.IntegrableOn] using h

end Work.FTS.StrongEps.LocUnif.D5
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.box_integral_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

theorem box_integral_eq {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc c d)) :
    ∫ p in Set.Icc a b ×ˢ Set.Icc c d, g p.1 p.2 = ∫ z in a..b, ∫ θ in c..d, g z θ := by
  -- The integrand is continuous on the (compact) rectangle, hence integrable there.
  have hf : MeasureTheory.IntegrableOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (IsCompact.prod isCompact_Icc isCompact_Icc) hg
  -- Fubini for set integrals over a product of sets.
  refine (MeasureTheory.setIntegral_prod (fun p : ℝ × ℝ => g p.1 p.2) hf).trans ?_
  -- Turn the iterated set integrals over `Icc` into interval integrals:
  -- `∫ in a..b = ∫ in Ioc a b` and `Ioc a b =ᵐ Icc a b`.
  simp only [intervalIntegral.integral_of_le, hab, hcd,
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (α := ℝ)
      (μ := MeasureTheory.volume))]

end Work.FTS.StrongEps.LocUnif.D5
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.continuousOn_intervalIntegral_shift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

/-- Continuity in `z` of the sliding interval integral `z ↦ ∫ u in z..(z+h), f u`, for `f`
continuous on `[a, b+h]` and `z ∈ [a,b]`.  We write the sliding integral as the difference of
the primitive `z ↦ ∫_a^z f` evaluated at `z+h` and at `z`, and use continuity of the primitive
(`intervalIntegral.continuousOn_primitive_interval'`). -/
theorem continuousOn_intervalIntegral_shift {a b h : ℝ} (hab : a ≤ b) (hh : 0 < h) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a (b + h))) :
    ContinuousOn (fun z => ∫ u in z..(z + h), f u) (Set.Icc a b) := by
  have hle : a ≤ b + h := by linarith
  have hf_int : IntervalIntegrable f MeasureTheory.volume a (b + h) :=
    hf.intervalIntegrable_of_Icc hle
  -- The primitive `y ↦ ∫_a^y f` is continuous on `[a, b+h]`.
  have hG' : ContinuousOn (fun y => ∫ t in a..y, f t) (Set.Icc a (b + h)) := by
    rw [← Set.uIcc_of_le hle]
    exact intervalIntegral.continuousOn_primitive_interval' hf_int Set.left_mem_uIcc
  have h1 : ContinuousOn (fun z => ∫ t in a..(z + h), f t) (Set.Icc a b) :=
    hG'.comp ((continuous_id.add continuous_const).continuousOn)
      (fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩)
  have h2 : ContinuousOn (fun z => ∫ t in a..z, f t) (Set.Icc a b) :=
    hG'.mono (fun z hz => ⟨hz.1, by linarith [hz.2]⟩)
  refine (h1.sub h2).congr fun z hz => ?_
  have hz1 : a ≤ z := hz.1
  have hz2 : z ≤ b := hz.2
  have haz : IntervalIntegrable f MeasureTheory.volume a z := by
    refine ContinuousOn.intervalIntegrable (u := f) (μ := MeasureTheory.volume) ?_
    rw [Set.uIcc_of_le hz1]
    exact hf.mono (fun t ht => ⟨ht.1, by linarith [ht.2, hz2]⟩)
  have hazh : IntervalIntegrable f MeasureTheory.volume a (z + h) := by
    refine ContinuousOn.intervalIntegrable (u := f) (μ := MeasureTheory.volume) ?_
    rw [Set.uIcc_of_le (by linarith : a ≤ z + h)]
    exact hf.mono (fun t ht => ⟨ht.1, by linarith [ht.2, hz2]⟩)
  simp only [Pi.sub_apply]
  rw [intervalIntegral.integral_interval_sub_left hazh haz]

end Work.FTS.StrongEps.LocUnif.D5
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.exists_diag_extract =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Abstract diagonal extraction along a.e.-convergent subsequences

`Work.FTS.StrongEps.LocUnif.D5.exists_diag_extract`: given a doubly-indexed family
`F : ℕ → ℕ → α → ℝ`, targets `G : ℕ → α → ℝ` and the hypothesis

* for every `k` and every strictly increasing `σ : ℕ → ℕ` there is a strictly increasing
  `ν : ℕ → ℕ` with `F k (σ (ν n)) p → G k p` for almost every `p`,

produce a **single** strictly increasing `Φ` with `F k (Φ n) p → G k p` for a.e. `p`, for every `k`.

The proof is the classical diagonal extraction.  Build the nested sequences
`S 0 = id`, `S (k+1) = S k ∘ ν k`, where `ν k` is the sequence supplied by the hypothesis at index
`k` for the sequence `S k`.  Each `S j` is strictly increasing, `range (S j) ⊆ range (S i)` for
`i ≤ j`, and for every `k` one has `F k (S (k+1) n) p → G k p` for a.e. `p`.  Then set
`Φ n := S n (m n)`, with `m n` chosen recursively so that `Φ` is strictly increasing — this makes
the tail `{n : n ≥ k+1}` of `Φ` a strictly increasing subsequence of `S (k+1)`, so it inherits the
a.e. convergence for the index `k`, and the countably many exceptional null sets are collected into
a single one.
-/

open Filter MeasureTheory

namespace Work.FTS.StrongEps.LocUnif.D5

/-- A strictly increasing sequence `ℕ → ℕ` is unbounded. -/
theorem strictMono_exists_gt (f : ℕ → ℕ) (hf : StrictMono f) (b : ℕ) : ∃ j, f j > b := by
  refine ⟨b + 1, ?_⟩
  have h1 : b + 1 ≤ f (b + 1) := hf.id_le (b + 1)
  omega

/-- If `u` and `σ` are strictly increasing and every value of `u` lies in the range of `σ`, then
`u` is a subsequence of `σ`; in particular a limit along `σ` is also a limit along `u`. -/
theorem tendsto_of_strictMono_range {β : Type*} [TopologicalSpace β] {a : ℕ → β} {L : β}
    {u σ : ℕ → ℕ} (hu : StrictMono u) (hσ : StrictMono σ)
    (hrange : ∀ n, u n ∈ Set.range σ)
    (ha : Tendsto (fun m => a (σ m)) atTop (nhds L)) :
    Tendsto (fun n => a (u n)) atTop (nhds L) := by
  classical
  have hr_spec : ∀ n, σ (Nat.find (hrange n)) = u n := fun n => Nat.find_spec (hrange n)
  have hr_mono : StrictMono (fun n => Nat.find (hrange n)) := by
    intro m n hmn
    by_contra hle
    have hle' : Nat.find (hrange n) ≤ Nat.find (hrange m) := le_of_not_gt hle
    have h1 : σ (Nat.find (hrange n)) ≤ σ (Nat.find (hrange m)) := hσ.monotone hle'
    rw [hr_spec n, hr_spec m] at h1
    exact absurd (hu hmn) (not_lt.mpr h1)
  have heq : (fun n => a (u n)) = (fun m => a (σ m)) ∘ (fun n => Nat.find (hrange n)) := by
    funext n
    rw [Function.comp_apply, hr_spec n]
  rw [heq]
  exact ha.comp hr_mono.tendsto_atTop

/-- Tail version of `tendsto_of_strictMono_range`: the range condition is needed only from `N` on. -/
theorem tendsto_of_strictMono_range' {β : Type*} [TopologicalSpace β] {a : ℕ → β} {L : β}
    {u σ : ℕ → ℕ} (hu : StrictMono u) (hσ : StrictMono σ) (N : ℕ)
    (hrange : ∀ n, N ≤ n → u n ∈ Set.range σ)
    (ha : Tendsto (fun m => a (σ m)) atTop (nhds L)) :
    Tendsto (fun n => a (u n)) atTop (nhds L) := by
  rw [← tendsto_add_atTop_iff_nat (f := fun n => a (u n)) N]
  refine tendsto_of_strictMono_range (hu.comp (fun a b h => Nat.add_lt_add_right h N)) hσ ?_ ha
  intro n
  exact hrange (n + N) (by omega)

/-- The nested strictly increasing sequences `S k` of the diagonal extraction, defined by
`S 0 = id` and `S (k+1) = S k ∘ ν k`, where `ν k` is the sequence furnished by the hypothesis at
index `k` applied to `S k`. -/
noncomputable def diagNestedSeq {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {F : ℕ → ℕ → α → ℝ} {G : ℕ → α → ℝ}
    (h : ∀ k : ℕ, ∀ σ : ℕ → ℕ, StrictMono σ → ∃ ν : ℕ → ℕ, StrictMono ν ∧
      ∀ᵐ p ∂μ, Filter.Tendsto (fun n => F k (σ (ν n)) p) Filter.atTop (nhds (G k p))) :
    ℕ → {f : ℕ → ℕ // StrictMono f} :=
  Nat.rec ⟨id, strictMono_id⟩
    (fun k prev => ⟨prev.1 ∘ (h k prev.1 prev.2).choose,
      prev.2.comp ((h k prev.1 prev.2).choose_spec).1⟩)

/-- **Diagonal extraction.**  If for every `k` and every strictly increasing `σ` the sequence
`F k (σ (ν n))` converges to `G k` a.e. along some further strictly increasing `ν`, then a single
strictly increasing `Φ` converges a.e. for *all* `k` at once. -/
theorem exists_diag_extract {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {F : ℕ → ℕ → α → ℝ} {G : ℕ → α → ℝ}
    (h : ∀ k : ℕ, ∀ σ : ℕ → ℕ, StrictMono σ → ∃ ν : ℕ → ℕ, StrictMono ν ∧
      ∀ᵐ p ∂μ, Filter.Tendsto (fun n => F k (σ (ν n)) p) Filter.atTop (nhds (G k p))) :
    ∃ Φ : ℕ → ℕ, StrictMono Φ ∧ ∀ k : ℕ,
      ∀ᵐ p ∂μ, Filter.Tendsto (fun n => F k (Φ n) p) Filter.atTop (nhds (G k p)) := by
  classical
  set S : ℕ → {f : ℕ → ℕ // StrictMono f} := diagNestedSeq h with hS
  -- unfolding lemma for the recursion
  have S_succ : ∀ k, (S (k+1)).1 = (S k).1 ∘ (h k (S k).1 (S k).2).choose := by
    intro k
    rw [hS]
    rfl
  have S_zero : (S 0).1 = id := by rw [hS]; rfl
  -- the a.e. convergence along `S (k+1)` for the index `k`
  have hconv : ∀ k : ℕ,
      ∀ᵐ p ∂μ, Filter.Tendsto (fun n => F k ((S (k+1)).1 n) p) Filter.atTop (nhds (G k p)) := by
    intro k
    have hk := (h k (S k).1 (S k).2).choose_spec.2
    rw [S_succ k]
    simpa only [Function.comp_apply] using hk
  -- the ranges are nested
  have hrange_step : ∀ k, Set.range (S (k+1)).1 ⊆ Set.range (S k).1 := by
    intro k x hx
    obtain ⟨j, hj⟩ := hx
    refine ⟨(h k (S k).1 (S k).2).choose j, ?_⟩
    rw [← hj, S_succ k]
    rfl
  have hrange_le : ∀ k n, k ≤ n → Set.range (S n).1 ⊆ Set.range (S k).1 := by
    intro k n hkn
    induction n, hkn using Nat.le_induction with
    | base => exact subset_rfl
    | succ m hm ih => exact (hrange_step m).trans ih
  -- the diagonal: `Φ n = S n (m n)` with `m` chosen so that `Φ` is strictly increasing
  set Φ : ℕ → ℕ := Nat.rec 0 (fun n prev =>
    (S (n+1)).1 (Nat.find (strictMono_exists_gt (S (n+1)).1 (S (n+1)).2 prev))) with hΦ
  have Φ_succ : ∀ n, Φ (n+1)
      = (S (n+1)).1 (Nat.find (strictMono_exists_gt (S (n+1)).1 (S (n+1)).2 (Φ n))) := by
    intro n
    rw [hΦ]
  have Φ_lt_succ : ∀ n, Φ n < Φ (n+1) := by
    intro n
    rw [Φ_succ n]
    exact Nat.find_spec (strictMono_exists_gt (S (n+1)).1 (S (n+1)).2 (Φ n))
  have Φ_mono : StrictMono Φ := strictMono_nat_of_lt_succ Φ_lt_succ
  -- `Φ n` lies in the range of `S n`
  have Φ_mem : ∀ n, Φ n ∈ Set.range (S n).1 := by
    intro n
    cases n with
    | zero =>
      refine ⟨0, ?_⟩
      rw [hΦ]
      rfl
    | succ n =>
      refine ⟨Nat.find (strictMono_exists_gt (S (n+1)).1 (S (n+1)).2 (Φ n)), ?_⟩
      rw [Φ_succ n]
  refine ⟨Φ, Φ_mono, fun k => ?_⟩
  refine (hconv k).mono (fun p hp => ?_)
  exact tendsto_of_strictMono_range' (a := fun m => F k m p) (L := G k p)
    Φ_mono (S (k+1)).2 (k+1) (fun n hn => hrange_le (k+1) n hn (Φ_mem n)) hp

end Work.FTS.StrongEps.LocUnif.D5
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.exists_strictMono_tendsto_ae_of_lintegral_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter

namespace Work.FTS.StrongEps.LocUnif.D5

/-- **Extraction step.**  If `∫⁻ x, L k x ∂μ → 0`, then there is a strictly increasing
`ψ : ℕ → ℕ` along which the integrals are summable, indeed bounded by the summable
geometric sequence `(1/2)^{k+1}`.

This is the "diagonal" selection: at stage `k` the hypothesis gives a threshold `N k`
beyond which `∫⁻ x, L m x ∂μ ≤ (1/2)^{k+1}`; the subsequence
`ψ k = (sup_{j ≤ k} N j) + k` is strictly increasing and stays beyond every threshold. -/
theorem exists_strictMono_lintegral_le_geometric {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α}
    {L : ℕ → α → ENNReal}
    (h : Filter.Tendsto (fun k => ∫⁻ x, L k x ∂μ) Filter.atTop (nhds 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ k, ∫⁻ x, L (ψ k) x ∂μ ≤ ENNReal.ofReal ((1/2 : ℝ) ^ (k + 1)) := by
  have hδpos : ∀ k, 0 < ENNReal.ofReal ((1/2 : ℝ) ^ (k + 1)) :=
    fun k => ENNReal.ofReal_pos.mpr (by positivity)
  have hex : ∀ k, ∃ N, ∀ m ≥ N, ∫⁻ x, L m x ∂μ ≤ ENNReal.ofReal ((1/2 : ℝ) ^ (k + 1)) :=
    fun k => (ENNReal.tendsto_atTop_zero.1 h) _ (hδpos k)
  choose N hN using hex
  refine ⟨fun k => (Finset.range (k + 1)).sup N + k, ?_, ?_⟩
  · intro a b hab
    have hsup : (Finset.range (a + 1)).sup N ≤ (Finset.range (b + 1)).sup N := by
      refine Finset.sup_le fun c hc => Finset.le_sup ?_
      simp only [Finset.mem_range] at hc ⊢
      omega
    simp only
    omega
  · intro k
    have hle : N k ≤ (Finset.range (k + 1)).sup N :=
      Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self k))
    exact hN k _ (le_trans hle (Nat.le_add_right _ _))

/-- **Limit step.**  If the series of integrals `∑' k, ∫⁻ x, L (ψ k) x ∂μ` is finite, then
`L (ψ k) x → 0` for almost every `x`: Tonelli's theorem turns the series of integrals into
the integral of the series, which is therefore finite a.e., and a finite `ℝ≥0∞`-series has
terms tending to `0`. -/
theorem ae_tendsto_of_tsum_lintegral_ne_top {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α}
    {L : ℕ → α → ENNReal} (hm : ∀ k, AEMeasurable (L k) μ) {ψ : ℕ → ℕ}
    (h : (∑' k, ∫⁻ x, L (ψ k) x ∂μ) ≠ ⊤) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun k => L (ψ k) x) Filter.atTop (nhds 0) := by
  have hInt : ∫⁻ x, (∑' k, L (ψ k) x) ∂μ = ∑' k, ∫⁻ x, L (ψ k) x ∂μ :=
    MeasureTheory.lintegral_tsum (fun k => hm (ψ k))
  have haefin : ∀ᵐ x ∂μ, (∑' k, L (ψ k) x) < ⊤ := by
    refine MeasureTheory.ae_lt_top' ?_ ?_
    · exact AEMeasurable.tsum (fun k => hm (ψ k))
    · rw [hInt]; exact h
  filter_upwards [haefin] with x hx
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne

theorem exists_strictMono_tendsto_ae_of_lintegral_tendsto {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {L : ℕ → α → ENNReal}
    (hm : ∀ k, AEMeasurable (L k) μ)
    (h : Filter.Tendsto (fun k => ∫⁻ x, L k x ∂μ) Filter.atTop (nhds 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ x ∂μ, Filter.Tendsto (fun k => L (ψ k) x) Filter.atTop (nhds 0) := by
  obtain ⟨ψ, hψ, hbound⟩ := exists_strictMono_lintegral_le_geometric h
  refine ⟨ψ, hψ, ae_tendsto_of_tsum_lintegral_ne_top hm ?_⟩
  have hS : Summable (fun k : ℕ => (1/2 : ℝ) ^ (k + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_left (1/2 : ℝ)
  exact ne_top_of_le_ne_top hS.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hbound)

end Work.FTS.StrongEps.LocUnif.D5
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.integrableOn_slice_integrals =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

theorem integrableOn_slice_integrals {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Icc a b ×ˢ Set.Icc c d)) :
    MeasureTheory.IntegrableOn (fun θ => ∫ z in a..b, f z θ) (Set.Ioc c d) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in c..d, f z θ) (Set.Ioc a b) := by
  -- `f` is integrable on the compact rectangle `[a,b] × [c,d]`
  have hK : MeasureTheory.Integrable (Function.uncurry f)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  -- turn the restricted product measure into a product of restricted measures
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict] at hK
  -- the interval integral over `[a,b]` is the set integral over `Icc a b`
  have hset : ∀ {a b : ℝ}, a ≤ b → ∀ g : ℝ → ℝ,
      (∫ x in Set.Icc a b, g x) = ∫ x in a..b, g x := by
    intro a b hab g
    rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]
  constructor
  · -- Fubini: the `z`-marginal is integrable in `θ`, then shrink `Icc c d` to `Ioc c d`
    refine MeasureTheory.IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
    refine (hK.integral_prod_right).congr (Filter.Eventually.of_forall fun θ => ?_)
    exact hset hab (fun z => f z θ)
  · -- Fubini: the `θ`-marginal is integrable in `z`, then shrink `Icc a b` to `Ioc a b`
    refine MeasureTheory.IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
    refine (hK.integral_prod_left).congr (Filter.Eventually.of_forall fun z => ?_)
    exact hset hcd (fun θ => f z θ)

end Work.FTS.StrongEps.LocUnif.D5
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.intervalIntegral_swap =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

theorem intervalIntegral_swap {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc c d)) :
    ∫ z in a..b, ∫ θ in c..d, g z θ = ∫ θ in c..d, ∫ z in a..b, g z θ := by
  refine MeasureTheory.intervalIntegral_intervalIntegral_swap (F := g) ?_
  rw [Set.uIoc_of_le hab, Set.uIoc_of_le hcd]
  exact (hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set (by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨⟨le_of_lt hx.1, hx.2⟩, ⟨le_of_lt hy.1, hy.2⟩⟩)

end Work.FTS.StrongEps.LocUnif.D5
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.slice_pointwise_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

open MeasureTheory Set Filter
open scoped Topology

theorem slice_pointwise_le {a b h δ : ℝ} (hab : a ≤ b) (hh : 0 < h) {P G G' : ℝ → ℝ}
    (hP : ∀ x ∈ Set.Icc a (b + h), |P x| ≤ δ)
    (hG : ∀ x ∈ Set.Icc a (b + h), HasDerivAt P (G x) x)
    (hG2 : ∀ x ∈ Set.Icc a (b + h), HasDerivAt G (G' x) x)
    (hG2c : ContinuousOn G' (Set.Icc a (b + h))) :
    ∀ z ∈ Set.Icc a b, |G z| ≤ 2 * δ / h + ∫ u in z..(z + h), |G' u| := by
  have _ := hab
  intro z hz
  have hz1 : a ≤ z := hz.1
  have hz2 : z ≤ b := hz.2
  have hzh : z < z + h := by linarith
  -- the window `[z, z+h]` lies inside `[a, b+h]`
  have hsub : Set.Icc z (z + h) ⊆ Set.Icc a (b + h) := by
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- mean value theorem on `[z, z+h]`: a point `c` where `G c` is the slope of `P`
  have hcont : ContinuousOn P (Set.Icc z (z + h)) :=
    fun x hx => (hG x (hsub hx)).continuousAt.continuousWithinAt
  obtain ⟨c, hcIoo, hcval⟩ := exists_hasDerivAt_eq_slope P G hzh hcont
    (fun x hx => hG x (hsub (Set.Ioo_subset_Icc_self hx)))
  have hcge : z ≤ c := hcIoo.1.le
  have hcle : c ≤ z + h := hcIoo.2.le
  have hsub' : Set.Icc z c ⊆ Set.Icc a (b + h) := by
    intro x hx; exact hsub ⟨hx.1, le_trans hx.2 hcle⟩
  have hc_eq : G c = (P (z + h) - P z) / h := by
    rw [hcval, add_sub_cancel_left]
  -- `|G c| ≤ 2 δ / h`
  have hP1 : |P z| ≤ δ := hP z ⟨hz1, by linarith⟩
  have hP2 : |P (z + h)| ≤ δ := hP (z + h) ⟨by linarith, by linarith⟩
  have hbound : |P (z + h) - P z| ≤ 2 * δ := by
    have hsplit : P (z + h) - P z = P (z + h) + -P z := by ring
    calc |P (z + h) - P z| = |P (z + h) + -P z| := congrArg abs hsplit
      _ ≤ |P (z + h)| + |-P z| := abs_add_le _ _
      _ = |P (z + h)| + |P z| := by rw [abs_neg]
      _ ≤ δ + δ := add_le_add hP2 hP1
      _ = 2 * δ := by ring
  have hGc : |G c| ≤ 2 * δ / h := by
    rw [hc_eq, abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right hbound hh.le
  -- fundamental theorem of calculus on `[z, c]`
  have hIntG' : IntervalIntegrable G' volume z c :=
    (hG2c.mono hsub').intervalIntegrable_of_Icc hcge
  have hFTC : ∫ u in z..c, G' u = G c - G z :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => by
        rw [Set.uIcc_of_le hcge] at hx
        exact hG2 x (hsub' hx)) hIntG'
  have hGz : G z - G c = -∫ u in z..c, G' u := by rw [hFTC]; ring
  have hIntAbs : IntervalIntegrable (fun u => |G' u|) volume z (z + h) :=
    ((continuous_abs.comp_continuousOn (hG2c.mono hsub))).intervalIntegrable_of_Icc
      (by linarith)
  have h2 : |G z - G c| ≤ ∫ u in z..(z + h), |G' u| := by
    have he : |G z - G c| = |∫ u in z..c, G' u| := by rw [hGz, abs_neg]
    rw [he]
    calc |∫ u in z..c, G' u| ≤ ∫ u in z..c, |G' u| :=
          intervalIntegral.abs_integral_le_integral_abs hcge
      _ ≤ ∫ u in z..(z + h), |G' u| :=
          intervalIntegral.integral_mono_interval le_rfl hcge hcle
            (Filter.Eventually.of_forall fun x => abs_nonneg (G' x)) hIntAbs
  have h1 : |G z| ≤ |G c| + |G z - G c| := by
    have hsplit : G z = G c + (G z - G c) := by ring
    calc |G z| = |G c + (G z - G c)| := congrArg abs hsplit
      _ ≤ |G c| + |G z - G c| := abs_add_le _ _
  linarith

end Work.FTS.StrongEps.LocUnif.D5
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.subseq_tendsto_ae_of_cauchy_L1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

open MeasureTheory Filter
open scoped ENNReal Topology

/-! ### Auxiliary measure-theoretic facts

These are the two general ingredients of the main theorem, proved here so that the file is
self-contained. -/

/-- If the successive differences of `u` are summable in the `L¹`-seminorm measured by `eLpNorm`,
then `u` converges almost everywhere. -/
theorem ae_tendsto_of_summable_eLpNorm_sub_aux {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {u : ℕ → α → ℝ}
    (hsum : (∑' n : ℕ, MeasureTheory.eLpNorm (fun x : α => u (n + 1) x - u n x) (1 : ENNReal) μ)
      ≠ ⊤) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => u n x) Filter.atTop (nhds L) := by
  have hnorm := MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top (μ := μ) (p := (1 : ENNReal))
    (f := fun n (x : α) => u (n + 1) x - u n x) le_rfl hsum
  filter_upwards [hnorm] with x hx
  have hs : Summable (fun n : ℕ => u (n + 1) x - u n x) := hx.of_norm
  have h1 : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (u (n + 1) x - u n x))
      Filter.atTop (nhds (∑' n : ℕ, (u (n + 1) x - u n x))) := hs.hasSum.tendsto_sum_nat
  have h2 : Filter.Tendsto (fun N : ℕ => u N x - u 0 x)
      Filter.atTop (nhds (∑' n : ℕ, (u (n + 1) x - u n x))) := by
    refine h1.congr' ?_
    filter_upwards with N
    exact Finset.sum_range_sub (fun n : ℕ => u n x) N
  refine ⟨u 0 x + ∑' n : ℕ, (u (n + 1) x - u n x), ?_⟩
  have h3 : Filter.Tendsto (fun N : ℕ => (u N x - u 0 x) + u 0 x) Filter.atTop
      (nhds ((∑' n : ℕ, (u (n + 1) x - u n x)) + u 0 x)) := h2.add tendsto_const_nhds
  have h4 : Filter.Tendsto (fun N : ℕ => u N x) Filter.atTop
      (nhds ((∑' n : ℕ, (u (n + 1) x - u n x)) + u 0 x)) := by
    refine h3.congr' ?_
    filter_upwards with N
    ring
  simpa [add_comm] using h4

/-- Fatou: an `L¹`-Cauchy sequence converging almost everywhere converges in `L¹` to its a.e.
limit (stated with `lintegral`s, so no integrability hypothesis is needed). -/
theorem lintegral_sub_le_of_tendsto_ae_of_cauchy_aux {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {u : ℕ → α → ℝ} {w : α → ℝ}
    (hu : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (u n) μ)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n : ℕ => u n x) Filter.atTop (nhds (w x)))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ x, ENNReal.ofReal |u n x - u m x| ∂μ ≤ ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∫⁻ x, ENNReal.ofReal |u k x - w x| ∂μ ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hcauchy ε hε
  refine ⟨N, fun k hk => ?_⟩
  have hFatou : ∫⁻ x, Filter.liminf (fun j : ℕ => ENNReal.ofReal |u k x - u j x|) Filter.atTop ∂μ
      ≤ Filter.liminf (fun j : ℕ => ∫⁻ x, ENNReal.ofReal |u k x - u j x| ∂μ) Filter.atTop :=
    MeasureTheory.lintegral_liminf_le' (μ := μ) (u := Filter.atTop)
      (f := fun (j : ℕ) (x : α) => ENNReal.ofReal |u k x - u j x|)
      (fun j => (((hu k).aemeasurable.sub (hu j).aemeasurable).abs).ennreal_ofReal)
  have hae : ∀ᵐ x ∂μ, Filter.liminf (fun j : ℕ => ENNReal.ofReal |u k x - u j x|) Filter.atTop
      = ENNReal.ofReal |u k x - w x| := by
    filter_upwards [hlim] with x hx
    have h1 : Filter.Tendsto (fun j : ℕ => u k x - u j x) Filter.atTop (nhds (u k x - w x)) :=
      tendsto_const_nhds.sub hx
    have h2 : Filter.Tendsto (fun j : ℕ => ENNReal.ofReal |u k x - u j x|) Filter.atTop
        (nhds (ENNReal.ofReal |u k x - w x|)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp h1.abs
    exact h2.liminf_eq
  have hstep1 : ∫⁻ x, ENNReal.ofReal |u k x - w x| ∂μ
      ≤ ∫⁻ x, Filter.liminf (fun j : ℕ => ENNReal.ofReal |u k x - u j x|) Filter.atTop ∂μ :=
    MeasureTheory.lintegral_mono_ae (hae.mono fun x hx => le_of_eq hx.symm)
  refine le_trans hstep1 ?_
  have hev : ∀ᶠ j : ℕ in Filter.atTop,
      (∫⁻ x, ENNReal.ofReal |u k x - u j x| ∂μ) ≤ ENNReal.ofReal ε := by
    filter_upwards [Filter.eventually_ge_atTop N] with j hj
    rw [MeasureTheory.lintegral_congr (fun x => by rw [abs_sub_comm])]
    exact hN j k hj hk
  exact le_trans hFatou (Filter.liminf_le_of_frequently_le' hev.frequently)

theorem subseq_tendsto_ae_of_cauchy_L1 {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ] {W : ℕ → α → ℝ}
    (hW : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (W n) μ)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ x, ENNReal.ofReal |W n x - W m x| ∂μ ≤ ENNReal.ofReal ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : α → ℝ, Measurable w ∧
      (∀ᵐ x ∂μ, Filter.Tendsto (fun k : ℕ => W (φ k) x) Filter.atTop (nhds (w x))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
        ∫⁻ x, ENNReal.ofReal |W (φ k) x - w x| ∂μ ≤ ENNReal.ofReal ε) := by
  -- Step 1: extract a strictly monotone subsequence whose successive differences are summable.
  have hεpos : ∀ k : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 2) := fun k => by positivity
  let Nk : ℕ → ℕ := fun k => Classical.choose (hcauchy ((1 / 2 : ℝ) ^ (k + 2)) (hεpos k))
  have hNk : ∀ k : ℕ, ∀ n m : ℕ, Nk k ≤ n → Nk k ≤ m →
      ∫⁻ x, ENNReal.ofReal |W n x - W m x| ∂μ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 2)) :=
    fun k => Classical.choose_spec (hcauchy ((1 / 2 : ℝ) ^ (k + 2)) (hεpos k))
  let φ : ℕ → ℕ := fun k => Nat.rec (Nk 0) (fun k ih => max (ih + 1) (Nk (k + 1))) k
  have hφ0 : φ 0 = Nk 0 := rfl
  have hφs : ∀ k : ℕ, φ (k + 1) = max (φ k + 1) (Nk (k + 1)) := fun k => rfl
  have hφlt : ∀ k : ℕ, φ k < φ (k + 1) := fun k => by
    rw [hφs]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hφge : ∀ k : ℕ, k ≤ φ k := by
    intro k
    induction k with
    | zero => simp [hφ0]
    | succ k ih => rw [hφs]; exact le_trans (Nat.succ_le_succ ih) (le_max_left _ _)
  have hφNk : ∀ k : ℕ, Nk k ≤ φ k := by
    intro k
    induction k with
    | zero => simp [hφ0]
    | succ k _ => rw [hφs]; exact le_max_right _ _
  have hstrict : StrictMono φ := strictMono_nat_of_lt_succ hφlt
  have hbnd : ∀ k : ℕ,
      ∫⁻ x, ENNReal.ofReal |W (φ (k + 1)) x - W (φ k) x| ∂μ
        ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 2)) := by
    intro k
    exact hNk k (φ (k + 1)) (φ k) (le_trans (hφNk k) (le_of_lt (hφlt k))) (hφNk k)
  -- Step 2: the `L¹`-norms of the successive differences are summable.
  have hLp : ∀ k : ℕ,
      MeasureTheory.eLpNorm (fun x : α => W (φ (k + 1)) x - W (φ k) x) (1 : ENNReal) μ
        ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 2)) := by
    intro k
    have h1 : MeasureTheory.eLpNorm (fun x : α => W (φ (k + 1)) x - W (φ k) x) (1 : ENNReal) μ
        = ∫⁻ x, ENNReal.ofReal |W (φ (k + 1)) x - W (φ k) x| ∂μ := by
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm
        (f := fun x : α => W (φ (k + 1)) x - W (φ k) x) ((hW (φ (k + 1))).sub (hW (φ k)))]
      exact MeasureTheory.lintegral_congr (fun x => Real.enorm_eq_ofReal_abs _)
    rw [h1]
    exact hbnd k
  have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have htsumgeom : (∑' k : ℕ, (1 / 2 : ℝ) ^ k) = 2 := by
    rw [tsum_geometric_of_norm_lt_one (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)]
    norm_num
  have hfingeom : (∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) = ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hgeom, htsumgeom]
  have hle : (∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 2))) ≤ ENNReal.ofReal 2 := by
    rw [← hfingeom]
    refine ENNReal.tsum_le_tsum (fun k => ?_)
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  have hsum_ne_top : (∑' k : ℕ,
      MeasureTheory.eLpNorm (fun x : α => W (φ (k + 1)) x - W (φ k) x) (1 : ENNReal) μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans (ENNReal.tsum_le_tsum hLp) hle)
  -- Step 3: a.e. convergence along the subsequence, and a measurable limit.
  have hu : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (fun x : α => W (φ n) x) μ :=
    fun n => hW (φ n)
  have hconv : ∀ᵐ x ∂μ, ∃ L : ℝ,
      Filter.Tendsto (fun k : ℕ => W (φ k) x) Filter.atTop (nhds L) :=
    ae_tendsto_of_summable_eLpNorm_sub_aux hsum_ne_top
  obtain ⟨w, hwsm, hwlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae hu hconv
  refine ⟨φ, hstrict, w, hwsm.measurable, hwlim, ?_⟩
  -- Step 4: the tail of the subsequence converges in `L¹` to its a.e. limit (Fatou).
  have hcau' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ x, ENNReal.ofReal |W (φ n) x - W (φ m) x| ∂μ ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    exact ⟨N, fun n m hn hm => hN (φ n) (φ m) (le_trans hn (hφge n)) (le_trans hm (hφge m))⟩
  exact lintegral_sub_le_of_tendsto_ae_of_cauchy_aux hu hwlim hcau'

end Work.FTS.StrongEps.LocUnif.D5
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.window_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

open MeasureTheory Set Filter

/-- **Window (sliding-interval) bound.**  For `f ≥ 0` continuous on the window `[a, b+h]`,
the average of the sliding-window integrals `∫_z^{z+h} f` over `z ∈ [a,b]` is at most `h`
times the total mass of `f` over `[a, b+h]`.

Proof: substitute `u = z + v` in the inner integral (`v ∈ [0,h]`), so that the left-hand
side becomes `∫_v (∫_z f (z+v))`; this is a genuine rectangle, so Tonelli applies.  For each
fixed `v ∈ [0,h]` the inner integral is `∫_u in (a+v)..(b+v), f u ≤ ∫_u in a..(b+h), f u`,
because `f ≥ 0` and `[a+v, b+v] ⊆ [a, b+h]`.  Finally `∫_v in 0..h, C = C * h` for a
constant `C`, and `∫ ≤ ‖∫‖` for free. -/
theorem window_bound {a b h : ℝ} (hab : a ≤ b) (hh : 0 < h) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a (b + h))) (hnn : ∀ x, 0 ≤ f x) :
    ∫ z in a..b, ∫ u in z..(z + h), f u ≤ h * ∫ u in a..(b + h), f u := by
  have hahb : a ≤ b + h := by linarith
  have h0h : (0 : ℝ) ≤ h := le_of_lt hh
  -- joint integrability of `(z,v) ↦ f (z+v)` on the rectangle `(a,b] × (0,h]`:
  -- it is continuous on the compact rectangle `[a,b] × [0,h]`.
  have hrect : Set.uIoc a b ×ˢ Set.uIoc (0 : ℝ) h ⊆ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) h := by
    rw [Set.uIoc_of_le hab, Set.uIoc_of_le h0h]
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨⟨hx.1.le, hx.2⟩, ⟨hy.1.le, hy.2⟩⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ => f (p.1 + p.2))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) h) := by
    refine hf.comp ?_ ?_
    · exact (continuous_fst.add continuous_snd).continuousOn
    · rintro ⟨x, y⟩ ⟨hx, hy⟩
      exact ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  have hint : IntegrableOn (fun p : ℝ × ℝ => f (p.1 + p.2))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) h) :=
    hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hint' : IntegrableOn (fun p : ℝ × ℝ => f (p.1 + p.2))
      (Set.uIoc a b ×ˢ Set.uIoc (0 : ℝ) h) := hint.mono_set hrect
  -- substitute `u = z + v` in the inner integral
  have hshift : ∀ z : ℝ, ∫ u in z..(z + h), f u = ∫ v in (0 : ℝ)..h, f (z + v) := by
    intro z
    have h := intervalIntegral.integral_comp_add_left (f := f) (a := (0 : ℝ)) (b := h) (d := z)
    rw [add_zero] at h
    exact h.symm
  -- the region is now a rectangle, so Tonelli applies
  have hswap : (∫ z in a..b, ∫ v in (0 : ℝ)..h, f (z + v))
      = ∫ v in (0 : ℝ)..h, ∫ z in a..b, f (z + v) :=
    MeasureTheory.intervalIntegral_intervalIntegral_swap hint'
  have hmain : (∫ z in a..b, ∫ u in z..(z + h), f u)
      = ∫ v in (0 : ℝ)..h, ∫ z in a..b, f (z + v) := by
    simp_rw [hshift]
    exact hswap
  -- for fixed `v ∈ [0,h]` the inner integral is at most the total mass
  have hbound : ‖∫ v in (0 : ℝ)..h, ∫ z in a..b, f (z + v)‖
      ≤ h * ∫ u in a..(b + h), f u := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun v => ∫ z in a..b, f (z + v)) (a := (0 : ℝ)) (b := h)
      (C := ∫ u in a..(b + h), f u) ?_
    · simpa [abs_of_pos hh, mul_comm] using h1
    · intro v hv
      rw [Set.uIoc_of_le h0h] at hv
      obtain ⟨hv0, hvh⟩ := hv
      have hshiftv : (∫ z in a..b, f (z + v)) = ∫ u in (a + v)..(b + v), f u :=
        intervalIntegral.integral_comp_add_right (f := f) (a := a) (b := b) (d := v)
      have hle : (∫ z in a..b, f (z + v)) ≤ ∫ u in a..(b + h), f u := by
        rw [hshiftv]
        exact intervalIntegral.integral_mono_interval (f := f) (a := a + v) (b := b + v)
          (c := a) (d := b + h) (by linarith) (by linarith) (by linarith)
          (Eventually.of_forall fun x => hnn x) (hf.intervalIntegrable_of_Icc hahb)
      have hnonneg : 0 ≤ ∫ z in a..b, f (z + v) :=
        intervalIntegral.integral_nonneg hab (fun w _ => hnn (w + v))
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hle
  calc ∫ z in a..b, ∫ u in z..(z + h), f u
      = ∫ v in (0 : ℝ)..h, ∫ z in a..b, f (z + v) := hmain
    _ ≤ ‖∫ v in (0 : ℝ)..h, ∫ z in a..b, f (z + v)‖ := by
          rw [Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ h * ∫ u in a..(b + h), f u := hbound

end Work.FTS.StrongEps.LocUnif.D5
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.DiffQuotFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Facts for `diffQuot_backward_lintegral_le`

Three elementary facts used by `Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le`:

* `ofReal_interval_integral_sq_le` — Cauchy–Schwarz with the constant weight `1`, in the
  unconditional `ℝ≥0∞`-valued form: `(∫_a^b f)² ≤ (b - a) · ∫⁻_a^b f²`.  (Adapted from
  `Work.FTS.EllipticEst.DzAmgm.OfRealIntervalIntegralSqLe`, which carries the weight `(b - t)`.)
* `setLIntegral_Icc_comp_sub` — translation invariance of a set integral over an interval
  (substituting `x ↦ x - c`).
* `integral_deriv_slice_sub` — the fundamental theorem of calculus for a `C¹` slice of `u`,
  in the backward form `∫_0^h ∂_zu(z - s, θ) ds = u z θ - u (z - h) θ`.
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Set

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-- **Cauchy–Schwarz with constant weight**, `ℝ≥0∞`-valued (no integrability needed):

`(∫_a^b f)² ≤ (b - a) · ∫⁻_{t ∈ (a,b]} f t ^ 2` for `a ≤ b` and `f` a.e. strongly measurable. -/
theorem ofReal_interval_integral_sq_le {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioc a b))) :
    ENNReal.ofReal ((∫ t in a..b, f t) ^ 2)
      ≤ ENNReal.ofReal (b - a) * ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((f t) ^ 2) := by
  rw [intervalIntegral.integral_of_le hab]
  set F : ℝ → ℝ≥0∞ := fun _ => 1 with hF
  set H : ℝ → ℝ≥0∞ := fun t => ‖f t‖ₑ with hH
  have hFmeas : AEMeasurable F (volume.restrict (Set.Ioc a b)) := aemeasurable_const
  have hHmeas : AEMeasurable H (volume.restrict (Set.Ioc a b)) := by
    rw [hH]; exact hf.enorm
  have hF2 : ∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ) = ENNReal.ofReal (b - a) := by
    have hpt : ∀ t : ℝ, (F t) ^ (2 : ℝ) = (1 : ℝ≥0∞) := by
      intro t; simp [hF]
    simp_rw [hpt]
    rw [MeasureTheory.setLIntegral_const, one_mul, Real.volume_Ioc]
  have hH2 : ∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)
      = ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((f t) ^ 2) := by
    refine lintegral_congr fun t => ?_
    simp only [hH]
    rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (abs_nonneg (f t)) 2, sq_abs]
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hCS : ∫⁻ t in Set.Ioc a b, F t * H t
      ≤ (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Ioc a b)) hpq hFmeas hHmeas
  have hrpow : ((∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ)
      = (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ)) * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / 2 by norm_num),
      ← ENNReal.rpow_mul,
      show (1 : ℝ) / 2 * 2 = 1 by norm_num, ENNReal.rpow_one]
  have hCSsq : (∫⁻ t in Set.Ioc a b, F t * H t) ^ (2 : ℝ)
      ≤ (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ))
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) := by
    have h2 := ENNReal.rpow_le_rpow hCS (show (0 : ℝ) ≤ 2 by norm_num)
    rwa [hrpow] at h2
  have hInt : ENNReal.ofReal |∫ t in Set.Ioc a b, f t|
      ≤ ∫⁻ t in Set.Ioc a b, F t * H t := by
    have h1 : ‖∫ t in Set.Ioc a b, f t‖ₑ ≤ ∫⁻ t in Set.Ioc a b, ‖f t‖ₑ :=
      enorm_integral_le_lintegral_enorm (fun t => f t)
    rw [Real.enorm_eq_ofReal_abs] at h1
    refine h1.trans (le_of_eq ?_)
    refine lintegral_congr fun t => ?_
    simp only [hF, hH, one_mul]
  have hleft : ENNReal.ofReal ((∫ t in Set.Ioc a b, f t) ^ 2)
      ≤ (∫⁻ t in Set.Ioc a b, F t * H t) ^ (2 : ℝ) := by
    have h1 : ENNReal.ofReal ((∫ t in Set.Ioc a b, f t) ^ 2)
        = (ENNReal.ofReal |∫ t in Set.Ioc a b, f t|) ^ 2 := by
      rw [← sq_abs (∫ t in Set.Ioc a b, f t)]
      exact ENNReal.ofReal_pow (abs_nonneg _) 2
    rw [h1, ← ENNReal.rpow_two]
    exact ENNReal.rpow_le_rpow hInt (show (0 : ℝ) ≤ 2 by norm_num)
  calc ENNReal.ofReal ((∫ t in Set.Ioc a b, f t) ^ 2)
      ≤ (∫⁻ t in Set.Ioc a b, F t * H t) ^ (2 : ℝ) := hleft
    _ ≤ (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ))
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) := hCSsq
    _ = ENNReal.ofReal (b - a) * ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((f t) ^ 2) := by
        rw [hF2, hH2]


/-- The fundamental theorem of calculus for a `C¹` slice of `u`, backward form. -/
theorem integral_deriv_slice_sub {a b : ℝ} {u : ℝ → ℝ → ℝ} {h z θ : ℝ} (hh : 0 ≤ h)
    (hsub : Set.Icc (z - h) z ⊆ Set.Ioo a b)
    (hu : ContDiffOn ℝ 1 (fun z' => u z' θ) (Set.Ioo a b)) :
    ∫ s in (0 : ℝ)..h, deriv (fun z' => u z' θ) (z - s) = u z θ - u (z - h) θ := by
  rw [intervalIntegral.integral_comp_sub_left (fun y => deriv (fun z' => u z' θ) y) z]
  simp only [sub_zero]
  have hIcc : Set.Icc (z - h) z ⊆ Set.Ioo a b := hsub
  have hcont : ContinuousOn (fun z' => u z' θ) (Set.Icc (z - h) z) :=
    hu.continuousOn.mono hIcc
  have hderiv : ∀ x ∈ Set.Ioo (z - h) z, HasDerivAt (fun z' => u z' θ)
      (deriv (fun z' => u z' θ) x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo a b := hIcc (Set.Ioo_subset_Icc_self hx)
    exact ((hu.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hx')).hasDerivAt
  have hcont_d : ContinuousOn (deriv (fun z' => u z' θ)) (Set.uIcc (z - h) z) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact (hu.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hIcc
  have hint : IntervalIntegrable (deriv (fun z' => u z' θ)) volume (z - h) z :=
    hcont_d.intervalIntegrable
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hcont hderiv hint

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.ae_shift_measure_null =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set

/-- Fubini + translation invariance: if a measurable set `B` meets the rectangle
`Icc a b ×ˢ Icc c d` in a null set, then for almost every `p` in the shifted
(and thinner) rectangle `Icc a' b' ×ˢ Icc c d`, the set of shifts `s ∈ (0, h]`
with `(p.1 - s, p.2) ∈ B` is null.  The hypotheses `h < a' - a` and `b' < b`
guarantee that for `p` in the small rectangle and `s ∈ (0, h]` the point
`(p.1 - s, p.2)` automatically lies in the *large* rectangle, so the null set
condition for `B ∩ (Icc a b ×ˢ Icc c d)` applies. -/
theorem ae_shift_measure_null {a b a' b' c d h : ℝ} (haa' : a < a') (hb'b : b' < b)
    (hh : 0 < h) (hah : h < a' - a) {B : Set (ℝ × ℝ)} (hB : MeasurableSet B)
    (hBnull : (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) B = 0) :
    ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d)),
      (MeasureTheory.volume.restrict (Set.Ioc 0 h)) {s : ℝ | (p.1 - s, p.2) ∈ B} = 0 := by
  -- Work with the piece of `B` inside the large rectangle: it is null.
  set W : Set (ℝ × ℝ) := B ∩ (Set.Icc a b ×ˢ Set.Icc c d) with hW
  have hWmeas : MeasurableSet W := hB.inter (measurableSet_Icc.prod measurableSet_Icc)
  have hWnull : (MeasureTheory.volume : Measure (ℝ × ℝ)) W = 0 := by
    rw [hW, ← Measure.restrict_apply hB]
    exact hBnull
  -- Fubini: almost every vertical slice of `W` is null.
  have hslice : ∀ᵐ y ∂(MeasureTheory.volume : Measure ℝ),
      (MeasureTheory.volume : Measure ℝ) {x : ℝ | (x, y) ∈ W} = 0 := by
    have h1 : ∫⁻ y, (MeasureTheory.volume : Measure ℝ) ((fun x : ℝ => (x, y)) ⁻¹' W)
        ∂(MeasureTheory.volume : Measure ℝ) = 0 := by
      rw [← Measure.prod_apply_symm hWmeas]
      rw [← Measure.volume_eq_prod]
      exact hWnull
    exact (MeasureTheory.lintegral_eq_zero_iff
      (measurable_measure_prodMk_right hWmeas)).mp h1
  -- Restrict the `y`-variable to `Icc c d` and pull back through the product measure.
  have hD : ∀ᵐ p ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc a' b')).prod
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc c d)),
      (MeasureTheory.volume : Measure ℝ) {x : ℝ | (x, p.2) ∈ W} = 0 := by
    have hTae : ∀ᵐ y ∂(MeasureTheory.volume : Measure ℝ).restrict (Set.Icc c d),
        (MeasureTheory.volume : Measure ℝ) {x : ℝ | (x, y) ∈ W} = 0 :=
      MeasureTheory.ae_restrict_of_ae hslice
    refine (Measure.ae_prod_iff_ae_ae ?_).mpr ?_
    · exact (measurableSet_singleton (0 : ENNReal)).preimage
        ((measurable_measure_prodMk_right hWmeas).comp measurable_snd)
    · exact Filter.Eventually.of_forall fun x => by simpa using hTae
  -- Rewrite the product of restricted measures as a restricted product measure.
  have hD' : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d)),
      (MeasureTheory.volume : Measure ℝ) {x : ℝ | (x, p.2) ∈ W} = 0 := by
    have h := hD
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
    exact h
  have hbox : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d)),
      p ∈ Set.Icc a' b' ×ˢ Set.Icc c d :=
    MeasureTheory.ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  filter_upwards [hD', hbox] with p hp hpmem
  rw [Set.mem_prod] at hpmem
  -- For `p` in the small rectangle and `s ∈ (0, h]`, the point `(p.1 - s, p.2)` lies
  -- in the large rectangle, so membership in `B` is membership in `W`.
  have hsub : {s : ℝ | (p.1 - s, p.2) ∈ B} ∩ Set.Ioc 0 h
      ⊆ {s : ℝ | p.1 - s ∈ {x : ℝ | (x, p.2) ∈ W}} := by
    intro s hs
    have h1 : a < p.1 - s := by
      have hh1 : a' ≤ p.1 := (Set.mem_Icc.mp hpmem.1).1
      linarith [hs.2.2]
    have h2 : p.1 - s < b := by
      have hh1 : p.1 ≤ b' := (Set.mem_Icc.mp hpmem.1).2
      linarith [hs.2.1]
    show (p.1 - s, p.2) ∈ W
    rw [hW]
    exact ⟨hs.1, ⟨le_of_lt h1, le_of_lt h2⟩, hpmem.2⟩
  -- Translation invariance of Lebesgue measure on `ℝ`.
  have htrans : (MeasureTheory.volume : Measure ℝ)
        {s : ℝ | p.1 - s ∈ {x : ℝ | (x, p.2) ∈ W}}
      = (MeasureTheory.volume : Measure ℝ) {x : ℝ | (x, p.2) ∈ W} := by
    have key : {s : ℝ | p.1 - s ∈ {x : ℝ | (x, p.2) ∈ W}}
        = (fun s : ℝ => -s) ⁻¹' ((fun t : ℝ => p.1 + t) ⁻¹' {x : ℝ | (x, p.2) ∈ W}) := by
      ext s; simp [sub_eq_add_neg]
    rw [key, MeasureTheory.Measure.measure_preimage_neg, MeasureTheory.measure_preimage_add]
  have hSp_meas : MeasurableSet {s : ℝ | (p.1 - s, p.2) ∈ B} :=
    hB.preimage ((measurable_const.sub measurable_id).prodMk measurable_const)
  rw [Measure.restrict_apply hSp_meas]
  refine le_antisymm ?_ zero_le
  calc (MeasureTheory.volume : Measure ℝ) ({s : ℝ | (p.1 - s, p.2) ∈ B} ∩ Set.Ioc 0 h)
      ≤ (MeasureTheory.volume : Measure ℝ) {s : ℝ | p.1 - s ∈ {x : ℝ | (x, p.2) ∈ W}} :=
        measure_mono hsub
    _ = (MeasureTheory.volume : Measure ℝ) {x : ℝ | (x, p.2) ∈ W} := htrans
    _ = 0 := hp

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.ae_shift_preimage_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongEps.LocUnif

/-- **Almost-everywhere statements transfer under a horizontal translation.**  If `Q` holds
almost everywhere on `A`, and the shift `q ↦ (q.1 - h, q.2)` maps `B` into `A`, then `Q` holds
almost everywhere on `B` after the shift.  Only the translation invariance of Lebesgue measure
on `ℝ × ℝ` is used. -/
theorem ae_shift_preimage_sub {A B : Set (ℝ × ℝ)} {h : ℝ} {Q : ℝ × ℝ → Prop}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hQ : ∀ᵐ q ∂(MeasureTheory.volume.restrict A), Q q)
    (hmap : ∀ q ∈ B, (q.1 - h, q.2) ∈ A) :
    ∀ᵐ q ∂(MeasureTheory.volume.restrict B), Q (q.1 - h, q.2) := by
  rw [MeasureTheory.ae_iff]
  have hA0 : (MeasureTheory.volume : Measure (ℝ × ℝ))
      ({q : ℝ × ℝ | ¬ Q q} ∩ A) = 0 := by
    rw [← MeasureTheory.Measure.restrict_apply' hAm]
    exact MeasureTheory.ae_iff.mp hQ
  rw [MeasureTheory.Measure.restrict_apply' hBm]
  have hpre : ((fun q : ℝ × ℝ => (q.1 - h, q.2)) ⁻¹' ({q : ℝ × ℝ | ¬ Q q} ∩ A))
      = ((fun q : ℝ × ℝ => (-h, 0) + q) ⁻¹' ({q : ℝ × ℝ | ¬ Q q} ∩ A)) := by
    rw [show (fun q : ℝ × ℝ => (q.1 - h, q.2)) = (fun q : ℝ × ℝ => (-h, 0) + q) from by
      funext q
      exact Prod.ext (by simp [sub_eq_add_neg, add_comm]) (by simp [Prod.snd_add])]
  refine MeasureTheory.measure_mono_null
    (t := ((fun q : ℝ × ℝ => (q.1 - h, q.2)) ⁻¹' ({q : ℝ × ℝ | ¬ Q q} ∩ A))) ?_ ?_
  · rintro q ⟨hq1, hq2⟩
    exact ⟨hq1, hmap q hq2⟩
  · rw [hpre, MeasureTheory.measure_preimage_add]
    exact hA0

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Filter Set Metric
open scoped Topology

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-! ## A dense sequence inside a nonempty subset of `ℝ²` -/

private theorem denseSeq_of_nonempty_aux {U : Set (ℝ × ℝ)} (hne : U.Nonempty) :
    ∃ e : ℕ → ℝ × ℝ, (∀ k : ℕ, e k ∈ U) ∧ ∀ p ∈ U, p ∈ closure (Set.range e) := by
  obtain ⟨t, htc, htsub, hUsub⟩ := TopologicalSpace.exists_countable_dense_subset U
  have htne : t.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    obtain ⟨p, hp⟩ := hne
    have hpt : p ∈ closure t := hUsub hp
    rw [h, closure_empty] at hpt
    exact hpt
  obtain ⟨e, he⟩ := htc.exists_eq_range htne
  exact ⟨e, fun k => htsub (he.symm ▸ Set.mem_range_self k), fun p hp => he ▸ hUsub hp⟩

/-! ## Diagonal extraction with per-column bounds -/

/-- A sequence of real sequences, bounded column by column, has a subsequence converging in every
column.  Proved by normalising the columns to `[-1,1]` and using the sequential compactness of the
compact product `∏ₖ [-1,1]` (Tychonoff). -/
private theorem diag_extract_aux {u : ℕ → ℕ → ℝ}
    (h : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, |u n k| ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ, ∃ L : ℝ,
      Filter.Tendsto (fun n => u (φ n) k) Filter.atTop (nhds L) := by
  choose C hC using h
  set D : ℕ → ℝ := fun k => |C k| + 1 with hD
  have hDpos : ∀ k, 0 < D k := by
    intro k; rw [hD]; positivity
  have hb : ∀ n k : ℕ, |u n k / D k| ≤ 1 := by
    intro n k
    have h1 : |u n k| ≤ D k := by
      have h2 := hC k n
      rw [hD]
      linarith [h2, le_abs_self (C k)]
    rw [abs_div, abs_of_pos (hDpos k), div_le_one (hDpos k)]
    exact h1
  have hcomp : IsCompact (Set.univ.pi fun _ : ℕ => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hx : ∀ n : ℕ, (fun k => u n k / D k) ∈
      Set.univ.pi (fun _ : ℕ => Set.Icc (-1 : ℝ) 1) := by
    intro n
    rw [Set.mem_univ_pi]
    intro k
    exact abs_le.mp (hb n k)
  obtain ⟨a, -, φ, hφ, htend⟩ := hcomp.tendsto_subseq hx
  refine ⟨φ, hφ, fun k => ⟨a k * D k, ?_⟩⟩
  have h1 : Filter.Tendsto (fun n => u (φ n) k / D k * D k) Filter.atTop
      (nhds (a k * D k)) :=
    ((tendsto_pi_nhds.mp htend) k).mul_const (D k)
  have h2 : (fun n => u (φ n) k / D k * D k) = fun n => u (φ n) k := by
    funext n; exact div_mul_cancel₀ _ (ne_of_gt (hDpos k))
  rwa [h2] at h1

/-- Vector version of `diag_extract_aux`: the columns are indexed by `m : ℕ` but the values live
in `Fin k → ℝ`; flattening `(m, j) ↦ Nat.pair m j` and reassembling with `tendsto_pi_nhds` gives
the result. -/
private theorem diag_extract_fin_aux {k : ℕ} {e : ℕ → ℝ × ℝ} {F : ℕ → ℝ × ℝ → (Fin k → ℝ)}
    (hbdd : ∀ m : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖F n (e m)‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m : ℕ, ∃ L : Fin k → ℝ,
      Filter.Tendsto (fun n => F (φ n) (e m)) Filter.atTop (nhds L) := by
  have hcoord : ∀ t : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      |(if h : t.unpair.2 < k then F n (e t.unpair.1) ⟨t.unpair.2, h⟩ else 0)| ≤ C := by
    intro t
    obtain ⟨C, hC⟩ := hbdd t.unpair.1
    refine ⟨max C 0, fun n => ?_⟩
    by_cases h : t.unpair.2 < k
    · rw [dif_pos h]
      refine le_trans ?_ (le_trans (hC n) (le_max_left _ _))
      simpa [Real.norm_eq_abs] using
        norm_le_pi_norm (F n (e t.unpair.1)) ⟨t.unpair.2, h⟩
    · rw [dif_neg h]
      exact le_trans (le_of_eq (abs_zero)) (le_max_right _ _)
  obtain ⟨φ, hφ, hlim⟩ := diag_extract_aux (u := fun n t =>
      if h : t.unpair.2 < k then F n (e t.unpair.1) ⟨t.unpair.2, h⟩ else 0) hcoord
  refine ⟨φ, hφ, fun m => ?_⟩
  have hL : ∀ j : Fin k, ∃ L : ℝ,
      Filter.Tendsto (fun n => F (φ n) (e m) j) Filter.atTop (nhds L) := by
    intro j
    obtain ⟨L, hL⟩ := hlim (Nat.pair m j.1)
    refine ⟨L, ?_⟩
    have hfun : (fun n => (if h : (Nat.pair m j.1).unpair.2 < k then
          F (φ n) (e (Nat.pair m j.1).unpair.1) ⟨(Nat.pair m j.1).unpair.2, h⟩ else 0))
        = fun n => F (φ n) (e m) j := by
      funext n
      rw [Nat.unpair_pair, dif_pos j.2]
    rwa [hfun] at hL
  choose L hLs using hL
  exact ⟨L, tendsto_pi_nhds.mpr hLs⟩

/-! ## From a dense set to pointwise convergence -/

/-- A uniformly equicontinuous sequence that converges at every point of a set whose closure meets
the compact `K` at `p` converges at `p`.  (Cauchy criterion in the complete space `Fin k → ℝ`.) -/
private theorem exists_tendsto_of_dense_equicont_fin_aux {k : ℕ} {e : ℕ → ℝ × ℝ}
    {G : ℕ → ℝ × ℝ → (Fin k → ℝ)} {K : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hp : p ∈ closure (Set.range e ∩ K))
    (hconv : ∀ m : ℕ, ∃ L : Fin k → ℝ,
      Filter.Tendsto (fun n => G n (e m)) Filter.atTop (nhds L))
    (heq : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ q ∈ K, dist q p ≤ δ →
      ‖G n q - G n p‖ ≤ ε) :
    ∃ L : Fin k → ℝ, Filter.Tendsto (fun n => G n p) Filter.atTop (nhds L) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := heq (ε / 4) (by linarith)
  obtain ⟨d, ⟨hdmem, hdK⟩, hdp⟩ := Metric.mem_closure_iff.mp hp δ hδpos
  obtain ⟨m, rfl⟩ := hdmem
  obtain ⟨L, hL⟩ := hconv m
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hL (ε / 4) (by linarith)
  refine ⟨N, fun n hn n' hn' => ?_⟩
  have hdpm : dist (e m) p ≤ δ := le_of_lt (by rwa [dist_comm] at hdp)
  have hδ' : ∀ n : ℕ, dist (G n (e m)) (G n p) ≤ ε / 4 := fun n => by
    rw [dist_eq_norm]; exact hδ n (e m) hdK hdpm
  have h1 : dist (G n p) (G n (e m)) ≤ ε / 4 := by rw [dist_comm]; exact hδ' n
  have h2 : dist (G n (e m)) (G n' (e m)) < ε / 2 := by
    have ha := hN n hn
    have hb := hN n' hn'
    calc dist (G n (e m)) (G n' (e m))
        ≤ dist (G n (e m)) L + dist L (G n' (e m)) := dist_triangle _ _ _
      _ = dist (G n (e m)) L + dist (G n' (e m)) L := by rw [dist_comm L (G n' (e m))]
      _ < ε / 4 + ε / 4 := by linarith
      _ = ε / 2 := by ring
  have h3 : dist (G n' (e m)) (G n' p) ≤ ε / 4 := hδ' n'
  have h4 : dist (G n p) (G n' p)
      ≤ dist (G n p) (G n (e m)) + dist (G n (e m)) (G n' (e m)) + dist (G n' (e m)) (G n' p) :=
    dist_triangle4 _ _ _ _
  linarith

/-! ## Uniform convergence on a compact set -/

/-- Pointwise convergence plus uniform equicontinuity on a compact set give uniform convergence:
cover the compact set by finitely many `δ/2`-balls and use the three-term split. -/
private theorem tendstoUniformlyOn_of_pointwise_of_equicont_aux {k : ℕ} {K : Set (ℝ × ℝ)}
    {F : ℕ → ℝ × ℝ → (Fin k → ℝ)} {f : ℝ × ℝ → (Fin k → ℝ)}
    (hK : IsCompact K)
    (hpt : ∀ p ∈ K, Filter.Tendsto (fun n => F n p) Filter.atTop (nhds (f p)))
    (heqc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
      dist p q < δ → ‖F n p - F n q‖ < ε) :
    TendstoUniformlyOn F f Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := heqc (ε / 3) (by linarith)
  obtain ⟨T, hTK, hTfin, hTcov⟩ :=
    Metric.finite_approx_of_totallyBounded hK.totallyBounded (δ / 2) (by linarith)
  haveI : Fintype {t : ℝ × ℝ // t ∈ T} := hTfin.fintype
  have hev : ∀ᶠ n in Filter.atTop, ∀ t : {t : ℝ × ℝ // t ∈ T}, dist (f t.1) (F n t.1) < ε / 3 := by
    rw [Filter.eventually_all]
    intro t
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hpt t.1 (hTK t.2)) (ε / 3) (by linarith)
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rwa [dist_comm] at h
  filter_upwards [hev] with n hn x hx
  obtain ⟨t, htT, hxt⟩ : ∃ t ∈ T, x ∈ ball t (δ / 2) := by
    rcases Set.mem_iUnion.mp (hTcov hx) with ⟨t, ht⟩
    rcases Set.mem_iUnion.mp ht with ⟨htT, hxt⟩
    exact ⟨t, htT, hxt⟩
  have hxtδ : dist x t < δ := by
    have h1 : dist x t < δ / 2 := mem_ball.mp hxt
    linarith
  have h1 : ‖F n x - F n t‖ < ε / 3 := hδ n x hx t (hTK htT) hxtδ
  have h2 : dist (f t) (F n t) < ε / 3 := hn ⟨t, htT⟩
  have h3 : dist (f x) (f t) ≤ ε / 3 := by
    have hxta : Filter.Tendsto (fun n' => F n' x) Filter.atTop (nhds (f x)) := hpt x hx
    have hta : Filter.Tendsto (fun n' => F n' t) Filter.atTop (nhds (f t)) := hpt t (hTK htT)
    have hnorm : Filter.Tendsto (fun n' => ‖F n' x - F n' t‖) Filter.atTop (nhds ‖f x - f t‖) :=
      (hxta.sub hta).norm
    have hle : ∀ n', ‖F n' x - F n' t‖ ≤ ε / 3 := fun n' =>
      le_of_lt (hδ n' x hx t (hTK htT) hxtδ)
    have h := le_of_tendsto_of_tendsto' hnorm tendsto_const_nhds hle
    rw [dist_eq_norm]
    exact h
  have h4 : dist (F n t) (F n x) = ‖F n x - F n t‖ := by
    rw [dist_eq_norm, norm_sub_rev]
  have h5 : dist (f x) (F n x)
      ≤ dist (f x) (f t) + dist (f t) (F n t) + dist (F n t) (F n x) :=
    dist_triangle4 _ _ _ _
  linarith

/-! ## The main extraction -/

theorem exists_subseq_tendstoLocallyUniformlyOn_fin {k : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F : ℕ → ℝ × ℝ → (Fin k → ℝ)}
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ n : ℕ, ∀ p ∈ K, ‖F n p‖ ≤ C)
    (heqc : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ U → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K, dist p q < δ → ‖F n p - F n q‖ < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℝ × ℝ → (Fin k → ℝ),
      TendstoLocallyUniformlyOn (fun n p => F (φ n) p) f Filter.atTop U := by
  classical
  rcases U.eq_empty_or_nonempty with hUe | hUne
  · rw [hUe]
    refine ⟨id, strictMono_id, fun _ => 0, ?_⟩
    intro u hu x hx
    exact absurd hx (by simp)
  · obtain ⟨e, heU, hedense⟩ := denseSeq_of_nonempty_aux hUne
    have hcol : ∀ m : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖F n (e m)‖ ≤ C := by
      intro m
      obtain ⟨C, hC⟩ := hbdd ({e m} : Set (ℝ × ℝ)) isCompact_singleton (by
        intro p hp
        rw [Set.mem_singleton_iff] at hp
        rw [hp]
        exact heU m)
      exact ⟨C, fun n => hC n (e m) rfl⟩
    obtain ⟨φ, hφ, hlim⟩ := diag_extract_fin_aux hcol
    have hpt : ∀ p ∈ U, ∃ L : Fin k → ℝ,
        Filter.Tendsto (fun n => F (φ n) p) Filter.atTop (nhds L) := by
      intro p hp
      obtain ⟨r, hrpos, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
      have hKsub : Metric.closedBall p (r / 2) ⊆ U := by
        intro q hq
        exact hrU (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hq) (by linarith)))
      refine exists_tendsto_of_dense_equicont_fin_aux (e := e) (G := fun n q => F (φ n) q)
        (K := Metric.closedBall p (r / 2)) (p := p) ?_ ?_ ?_
      · rw [Metric.mem_closure_iff]
        intro η hη
        have hηpos : 0 < min η (r / 2) := lt_min hη (by linarith)
        obtain ⟨d, hd, hdp⟩ := Metric.mem_closure_iff.mp (hedense p hp) (min η (r / 2)) hηpos
        refine ⟨d, ⟨hd, ?_⟩, lt_of_lt_of_le hdp (min_le_left _ _)⟩
        refine Metric.mem_closedBall.mpr (le_of_lt ?_)
        rw [dist_comm]
        exact lt_of_lt_of_le hdp (min_le_right _ _)
      · intro m
        exact hlim m
      · intro ε hε
        obtain ⟨δ, hδpos, hδ⟩ :=
          heqc (Metric.closedBall p (r / 2)) (isCompact_closedBall p (r / 2)) hKsub ε hε
        refine ⟨δ / 2, by linarith, fun n q hq hqp => ?_⟩
        exact le_of_lt (hδ (φ n) q hq p (Metric.mem_closedBall_self (by linarith))
          (lt_of_le_of_lt hqp (by linarith)))
    let f : ℝ × ℝ → (Fin k → ℝ) := fun p =>
      if hp : p ∈ U then Classical.choose (hpt p hp) else 0
    have hf : ∀ p : ℝ × ℝ, p ∈ U →
        Filter.Tendsto (fun n => F (φ n) p) Filter.atTop (nhds (f p)) := by
      intro p hp
      have hfp : f p = Classical.choose (hpt p hp) := by
        show (if hp : p ∈ U then Classical.choose (hpt p hp) else 0)
            = Classical.choose (hpt p hp)
        exact dif_pos hp
      rw [hfp]
      exact Classical.choose_spec (hpt p hp)
    refine ⟨φ, hφ, f, ?_⟩
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    refine tendstoUniformlyOn_of_pointwise_of_equicont_aux (F := fun n p => F (φ n) p) (f := f)
      hK (fun p hp => hf p (hKU hp)) ?_
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := heqc K hK hKU ε hε
    exact ⟨δ, hδpos, fun n p hp q hq hpq => hδ (φ n) p hp q hq hpq⟩

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.iUnion_subbox =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- One-dimensional exhaustion: the closed intervals with margins `(b-a)/(k+2)` around `[a,b]`
increase with `k` to the whole open interval `(a,b)`. -/
private lemma iUnion_Icc_div_eq_Ioo {a b : ℝ} (hab : a < b) :
    (⋃ k : ℕ, Set.Icc (a + (b - a) / ((k : ℝ) + 2)) (b - (b - a) / ((k : ℝ) + 2)))
      = Set.Ioo a b := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_Ioo]
  constructor
  · rintro ⟨k, h1, h2⟩
    have hpos : 0 < (b - a) / ((k : ℝ) + 2) := div_pos (by linarith) (by positivity)
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hx1, hx2⟩
    have hm : 0 < min (x - a) (b - x) := lt_min (by linarith) (by linarith)
    obtain ⟨k, hk⟩ := exists_nat_gt ((b - a) / min (x - a) (b - x))
    have hkey : b - a < (k : ℝ) * min (x - a) (b - x) := (div_lt_iff₀ hm).mp hk
    have hsmall : (b - a) / ((k : ℝ) + 2) ≤ min (x - a) (b - x) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 2)]
      nlinarith [hkey, hm]
    exact ⟨k, by linarith [min_le_left (x - a) (b - x), hsmall],
      by linarith [min_le_right (x - a) (b - x), hsmall]⟩

/-- The family of closed sub-boxes is increasing in `k`. -/
private lemma monotone_Icc_div {a b : ℝ} (hab : a < b) :
    Monotone
      (fun k : ℕ => Set.Icc (a + (b - a) / ((k : ℝ) + 2)) (b - (b - a) / ((k : ℝ) + 2))) := by
  intro k j hkj
  have hkj' : (k : ℝ) + 2 ≤ (j : ℝ) + 2 := by
    have : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj
    linarith
  have hle : (b - a) / ((j : ℝ) + 2) ≤ (b - a) / ((k : ℝ) + 2) := by
    gcongr
  exact Set.Icc_subset_Icc (by linarith) (by linarith)

theorem iUnion_subbox {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    (⋃ k : ℕ, (Set.Icc (a + (b - a) / ((k : ℝ) + 2)) (b - (b - a) / ((k : ℝ) + 2)) ×ˢ
      Set.Icc (c + (d - c) / ((k : ℝ) + 2)) (d - (d - c) / ((k : ℝ) + 2)) : Set (ℝ × ℝ)))
      = Set.Ioo a b ×ˢ Set.Ioo c d := by
  rw [Set.iUnion_prod_of_monotone (monotone_Icc_div hab) (monotone_Icc_div hcd),
    iUnion_Icc_div_eq_Ioo hab, iUnion_Icc_div_eq_Ioo hcd]

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.lintegral_lintegral_shift_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.LocUnif.lintegral_lintegral_shift_le`

A pure measure-theoretic shifting estimate used by the local-uniformity extraction of
`Submission/Work/FTS/StrongEps/exists_locUnif_subseq_of_uniform_H6.lean`.

**Statement.**  For `a < a'`, `b' < b`, `0 < h` and `h < a' - a`, and for a measurable
`G' : ℝ × ℝ → ℝ≥0∞`,

`∫⁻ p in [a',b'] × [c,d], ∫⁻ s in (0,h], G' (p.1 - s, p.2) ≤ h · ∫⁻ q in [a,b] × [c,d], G' q`.

**Why it is true.**  Tonelli swaps the two integrations; for a fixed `s ∈ (0,h]` the map
`p ↦ (p.1 - s, p.2)` translates the box `[a',b'] × [c,d]` *into* `[a,b] × [c,d]` (because
`a < a' - h ≤ a' - s` and `b' - s ≤ b' < b`), so the inner integral is at most the full
integral over `[a,b] × [c,d]`.  Integrating the resulting constant over `(0,h]` contributes
exactly `volume (Ioc 0 h) = ofReal h`.

The helper below isolates the per-`s` step: it is the image-measure form
`map (· - (s,0)) (volume.restrict A) ≤ volume.restrict C` of the shift, transported to
integrals with `lintegral_map`.
-/

open MeasureTheory Set

namespace Work.FTS.StrongEps.LocUnif

/-- **Per-`s` shift bound.**  If `a ≤ a' - s`, `b' ≤ b` and `0 ≤ s`, then translating the box
`[a',b'] × [c,d]` by `(s,0)` to the left does not increase the integral of a nonegative
measurable function against Lebesgue measure on `[a,b] × [c,d]`. -/
lemma setLIntegral_shift_le {a b a' b' c d s : ℝ} (ha : a ≤ a' - s) (hbb' : b' ≤ b)
    (hs0 : 0 ≤ s) {G' : ℝ × ℝ → ENNReal} (hG' : Measurable G') :
    ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, G' (p.1 - s, p.2)
      ≤ ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q := by
  have hCmeas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
    measurableSet_Icc.prod measurableSet_Icc
  -- the shift maps the source box into the target box
  have hsub : Set.Icc a' b' ×ˢ Set.Icc c d ⊆
      (fun p : ℝ × ℝ => (p.1 - s, p.2)) ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d) := by
    rintro p ⟨hp1, hp2⟩
    have h1 : a ≤ p.1 - s := by linarith [ha, hp1.1]
    have h2 : p.1 - s ≤ b := by linarith [hbb', hp1.2, hs0]
    exact ⟨⟨h1, h2⟩, hp2⟩
  have hTmeas : Measurable (fun p : ℝ × ℝ => (p.1 - s, p.2)) := by fun_prop
  -- the shift preserves Lebesgue measure on `ℝ × ℝ`
  have hmap : Measure.map (fun p : ℝ × ℝ => (p.1 - s, p.2)) volume = volume := by
    have heq : (fun p : ℝ × ℝ => (p.1 - s, p.2)) = fun p : ℝ × ℝ => p + (-s, 0) := by
      funext p; ext <;> simp [sub_eq_add_neg]
    rw [heq, Measure.IsAddRightInvariant.map_add_right_eq_self]
  have hmono : Measure.map (fun p : ℝ × ℝ => (p.1 - s, p.2))
        (volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d))
      ≤ volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) := by
    calc Measure.map (fun p : ℝ × ℝ => (p.1 - s, p.2))
          (volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d))
        ≤ Measure.map (fun p : ℝ × ℝ => (p.1 - s, p.2))
            (volume.restrict ((fun p : ℝ × ℝ => (p.1 - s, p.2)) ⁻¹'
              (Set.Icc a b ×ˢ Set.Icc c d))) :=
          Measure.map_mono (Measure.restrict_mono hsub le_rfl) hTmeas
      _ = (Measure.map (fun p : ℝ × ℝ => (p.1 - s, p.2)) volume).restrict
            (Set.Icc a b ×ˢ Set.Icc c d) :=
          (Measure.restrict_map hTmeas hCmeas).symm
      _ = volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) := by rw [hmap]
  calc ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, G' (p.1 - s, p.2)
      = ∫⁻ q, G' q ∂(Measure.map (fun p : ℝ × ℝ => (p.1 - s, p.2))
            (volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d))) :=
        (lintegral_map (μ := volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d))
          (f := G') (g := fun p : ℝ × ℝ => (p.1 - s, p.2)) hG' hTmeas).symm
    _ ≤ ∫⁻ q, G' q ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
        lintegral_mono' hmono le_rfl
    _ = ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q := rfl

set_option linter.unusedVariables false

/-- The assumption `a < a'` is not needed (only `h < a' - a` is), and neither is `0 < h`
(the bound is also valid, and trivial, for `h ≤ 0`); they are kept because they are part of the
requested statement. -/
theorem lintegral_lintegral_shift_le {a b a' b' c d h : ℝ} (haa' : a < a') (hb'b : b' < b)
    (hh : 0 < h) (hah : h < a' - a) {G' : ℝ × ℝ → ENNReal} (hG' : Measurable G') :
    ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2)
      ≤ ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q := by
  -- Tonelli: swap the order of integration.
  have hswap :
      ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2)
        = ∫⁻ s in Set.Ioc 0 h, ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, G' (p.1 - s, p.2) :=
    lintegral_lintegral_swap (μ := volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d))
      (ν := volume.restrict (Set.Ioc 0 h)) (f := fun p s => G' (p.1 - s, p.2)) (by fun_prop)
  rw [hswap]
  -- For every `s ∈ (0,h]` the inner integral is bounded by the full integral over the target box.
  have hpt : ∀ s ∈ Set.Ioc 0 h,
      ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, G' (p.1 - s, p.2)
        ≤ ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs.1
    have hsle : s ≤ h := hs.2
    have ha : a ≤ a' - s := by linarith [hah, haa', hh]
    exact setLIntegral_shift_le ha (le_of_lt hb'b) hs0 hG'
  calc ∫⁻ s in Set.Ioc 0 h,
        (fun s => ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d, G' (p.1 - s, p.2)) s
      ≤ ∫⁻ s in Set.Ioc 0 h,
        (fun _ => ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q) s :=
        setLIntegral_mono measurable_const hpt
    _ = (∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q) * volume (Set.Ioc 0 h) :=
        setLIntegral_const _ _
    _ = ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q := by
        rw [Real.volume_Ioc, sub_zero, mul_comm]

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.rho_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

theorem rho_bounds {a b c d : ℝ} (hab : a < b) (hcd : c < d) {ρ : ℝ → ℝ → ℝ}
    (hρc : ContinuousOn (Function.uncurry ρ) (Set.Icc a b ×ˢ Set.Icc c d))
    (hρp : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < ρ z θ) :
    (∃ m : ℝ, 0 < m ∧ ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, m ≤ ρ z θ) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ z ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |z - t| < δ → |ρ z θ - ρ t θ| < ε) := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) :=
    (isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := c) (b := d))
  constructor
  · obtain ⟨m, hm, hle⟩ :=
      hK.exists_forall_le' hρc (a := 0) (fun p hp => hρp p.1 hp.1 p.2 hp.2)
    exact ⟨m, hm, fun z hz θ hθ => hle (z, θ) ⟨hz, hθ⟩⟩
  · intro ε hε
    have hunif : UniformContinuousOn (Function.uncurry ρ) (Set.Icc a b ×ˢ Set.Icc c d) :=
      hK.uniformContinuousOn_of_continuous hρc
    obtain ⟨δ, hδ, hδ'⟩ := (Metric.uniformContinuousOn_iff.mp hunif) ε hε
    refine ⟨δ, hδ, fun z hz t ht θ hθ hzt => ?_⟩
    have hd : dist (z, θ) (t, θ) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq]
      exact hzt
    have hres := hδ' (z, θ) ⟨hz, hθ⟩ (t, θ) ⟨ht, hθ⟩ hd
    rwa [Real.dist_eq] at hres

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.sin_two_lower_bound_rect =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

theorem sin_two_lower_bound_rect {c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2) :
    ∃ m : ℝ, 0 < m ∧ ∀ θ ∈ Set.Icc c d, m ≤ Real.sin (2 * θ) := by
  rcases le_or_gt c d with hcd | hdc
  · -- nonempty rectangle: the minimum of `sin(2·)` on `[c,d]` is attained at an endpoint
    have hdpos : 0 < d := lt_of_lt_of_le hc hcd
    refine ⟨min (Real.sin (2 * c)) (Real.sin (2 * d)), lt_min ?_ ?_, ?_⟩
    · exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    · exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    · intro θ hθ
      rw [Set.mem_Icc] at hθ
      obtain ⟨hcθ, hθd⟩ := hθ
      rcases le_or_gt (2 * θ) (Real.pi / 2) with hcase | hcase
      · -- `2θ ≤ π/2`: `sin` is increasing on `[-(π/2), π/2]`
        have hmono : Real.sin (2 * c) ≤ Real.sin (2 * θ) :=
          Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 2 * c)
            hcase (by linarith)
        exact le_trans (min_le_left _ _) hmono
      · -- `π/2 ≤ 2θ`: `sin x = cos (x - π/2)` with `cos` decreasing on `[0, π]`
        have hmono : Real.cos (2 * d - Real.pi / 2) ≤ Real.cos (2 * θ - Real.pi / 2) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (x := 2 * θ - Real.pi / 2)
            (y := 2 * d - Real.pi / 2) (by linarith) (by linarith) (by linarith)
        have hsin : Real.sin (2 * d) ≤ Real.sin (2 * θ) := by
          rw [← Real.cos_sub_pi_div_two (2 * d), ← Real.cos_sub_pi_div_two (2 * θ)]
          exact hmono
        exact le_trans (min_le_right _ _) hsin
  · -- the rectangle is empty, so any positive constant works
    refine ⟨1, one_pos, ?_⟩
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    exact absurd (le_trans hθ.1 hθ.2) (not_le.mpr hdc)

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.sup_bound_of_holder_L2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set

/-- **Averaging lemma (one dimensional).** If `f` is integrable on `[u,v]` (`u < v`) and its
integral on `[u,v]` is at most `C`, then `f` takes a value at most `(C+1)/(v-u)` somewhere on
`[u,v]`.  (The constant `C+1` instead of `C` is what makes the argument work with a plain
pointwise comparison, no strictness or attainment of a minimum is needed.) -/
private lemma exists_le_of_setIntegral_le {u v C : ℝ} {f : ℝ → ℝ} (huv : u < v)
    (hfint : IntegrableOn f (Set.Icc u v)) (hC : ∫ x in Set.Icc u v, f x ≤ C) :
    ∃ x ∈ Set.Icc u v, f x ≤ (C + 1) / (v - u) := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have hle : ∀ x ∈ Set.Icc u v, (C + 1) / (v - u) ≤ f x := fun x hx => (h x hx).le
  have hμ : volume (Set.Icc u v) ≠ ⊤ := by simp
  have hge := setIntegral_ge_of_const_le (s := Set.Icc u v) (f := f)
    (c := (C + 1) / (v - u)) measurableSet_Icc hμ hle hfint
  rw [Real.volume_real_Icc_of_le huv.le, smul_eq_mul] at hge
  have hvu : v - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huv)
  have hone : (v - u) * ((C + 1) / (v - u)) = C + 1 := by field_simp
  rw [hone] at hge
  linarith

theorem sup_bound_of_holder_L2 {ι : Type*} {M : ι → ℝ → ℝ → ℝ} {a b c d C₁ C₂ : ℝ}
    (hab : a < b) (hcd : c < d) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hcont : ∀ n : ι, ContinuousOn (fun p : ℝ × ℝ => M n p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (hholder : ∀ n p q, p ∈ Set.Icc a b ×ˢ Set.Icc c d → q ∈ Set.Icc a b ×ˢ Set.Icc c d →
      |M n p.1 p.2 - M n q.1 q.2| ≤ C₁ * dist p q ^ (1 / 2 : ℝ))
    (hL2 : ∀ n, ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (M n z θ) ^ 2 ≤ C₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ n p, p ∈ Set.Icc a b ×ˢ Set.Icc c d → |M n p.1 p.2| ≤ C := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hdc : 0 < d - c := sub_pos.mpr hcd
  have hKpos : 0 < ((C₂ + 1) / (b - a) + 1) / (d - c) := by
    have h1 : 0 < (C₂ + 1) / (b - a) := div_pos (by linarith) hba
    exact div_pos (by linarith) hdc
  refine ⟨√(((C₂ + 1) / (b - a) + 1) / (d - c))
      + C₁ * ((b - a) + (d - c)) ^ (1 / 2 : ℝ) + 1, ?_, ?_⟩
  · have hs : 0 < √(((C₂ + 1) / (b - a) + 1) / (d - c)) := Real.sqrt_pos.mpr hKpos
    have hr : 0 ≤ ((b - a) + (d - c)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    have := mul_nonneg hC₁ hr
    linarith
  · intro n p hp
    -- ### Step 1: a point `z₀` whose `θ`-slice energy is small.
    --
    -- The (iterated) hypothesis `hL2` is a statement about the honest value of the outer
    -- integral, which requires the outer integrand to be integrable.  We obtain integrability
    -- from continuity, by clamping the two variables into the box: the clamped function is
    -- globally continuous and agrees with `M n` on the box.
    have hexists : ∃ z ∈ Set.Icc a b, (∫ θ in Set.Icc c d, (M n z θ) ^ 2) ≤ (C₂ + 1) / (b - a) := by
      have hcl1 : Continuous fun t : ℝ => max a (min b t) :=
        continuous_const.max (continuous_const.min continuous_id)
      have hcl2 : Continuous fun t : ℝ => max c (min d t) :=
        continuous_const.max (continuous_const.min continuous_id)
      have hm1 : ∀ t : ℝ, max a (min b t) ∈ Set.Icc a b := fun t =>
        ⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩
      have hm2 : ∀ t : ℝ, max c (min d t) ∈ Set.Icc c d := fun t =>
        ⟨le_max_left _ _, max_le hcd.le (min_le_left _ _)⟩
      have hid1 : ∀ t ∈ Set.Icc a b, max a (min b t) = t := fun t ht => by
        rw [min_eq_right ht.2, max_eq_right ht.1]
      have hid2 : ∀ t ∈ Set.Icc c d, max c (min d t) = t := fun t ht => by
        rw [min_eq_right ht.2, max_eq_right ht.1]
      set G : ℝ → ℝ → ℝ := fun z θ => (M n (max a (min b z)) (max c (min d θ))) ^ 2 with hG
      have hpair : Continuous fun q : ℝ × ℝ =>
          (max a (min b q.1), max c (min d q.2)) :=
        continuous_prodMk.mpr
          ⟨hcl1.comp continuous_fst, hcl2.comp continuous_snd⟩
      have hcomp : Continuous fun q : ℝ × ℝ =>
          M n (max a (min b q.1)) (max c (min d q.2)) :=
        (hcont n).comp_continuous hpair (fun q => ⟨hm1 q.1, hm2 q.2⟩)
      have hGc : Continuous (Function.uncurry G) := by
        change Continuous fun q : ℝ × ℝ =>
            (M n (max a (min b q.1)) (max c (min d q.2))) ^ 2
        exact hcomp.pow 2
      have hHc : Continuous fun z : ℝ => ∫ θ in c..d, G z θ :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := G) hGc c d
      have hHG : ∀ z ∈ Set.Icc a b,
          (∫ θ in c..d, G z θ) = ∫ θ in Set.Icc c d, (M n z θ) ^ 2 := by
        intro z hz
        rw [intervalIntegral.integral_of_le hcd.le,
          MeasureTheory.integral_Icc_eq_integral_Ioc]
        refine setIntegral_congr_fun measurableSet_Ioc (fun θ hθ => ?_)
        simp only [hG, hid1 z hz, hid2 θ ⟨hθ.1.le, hθ.2⟩]
      have hHint : IntegrableOn (fun z : ℝ => ∫ θ in c..d, G z θ) (Set.Icc a b) :=
        hHc.integrableOn_Icc
      have hhint : IntegrableOn (fun z : ℝ => ∫ θ in Set.Icc c d, (M n z θ) ^ 2)
          (Set.Icc a b) :=
        (integrableOn_congr_fun (fun z hz => hHG z hz) measurableSet_Icc).mp hHint
      exact exists_le_of_setIntegral_le hab hhint (hL2 n)
    obtain ⟨z₀, hz₀mem, hz₀le⟩ := hexists
    -- ### Step 2: a point `θ₀` whose value is small.
    have hslice : ContinuousOn (fun θ : ℝ => M n z₀ θ) (Set.Icc c d) :=
      (hcont n).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun θ hθ => ⟨hz₀mem, hθ⟩)
    have hslice2 : ContinuousOn (fun θ : ℝ => (M n z₀ θ) ^ 2) (Set.Icc c d) :=
      hslice.pow 2
    obtain ⟨θ₀, hθ₀mem, hθ₀le⟩ :=
      exists_le_of_setIntegral_le hcd hslice2.integrableOn_Icc hz₀le
    -- ### Step 3: Hölder continuity transfers the bound to every point of the box.
    have hq : (z₀, θ₀) ∈ Set.Icc a b ×ˢ Set.Icc c d := ⟨hz₀mem, hθ₀mem⟩
    have hA : |M n z₀ θ₀| ≤ √(((C₂ + 1) / (b - a) + 1) / (d - c)) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hθ₀le
    have hdist : dist p (z₀, θ₀) ≤ (b - a) + (d - c) := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
      constructor
      · rw [abs_le]; constructor <;> linarith [hp.1.1, hp.1.2, hz₀mem.1, hz₀mem.2]
      · rw [abs_le]; constructor <;> linarith [hp.2.1, hp.2.2, hθ₀mem.1, hθ₀mem.2]
    have hrpow : dist p (z₀, θ₀) ^ (1 / 2 : ℝ) ≤ ((b - a) + (d - c)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow dist_nonneg hdist (by norm_num)
    calc |M n p.1 p.2| ≤ |M n p.1 p.2 - M n z₀ θ₀| + |M n z₀ θ₀| := by
          have h := abs_add_le (M n p.1 p.2 - M n z₀ θ₀) (M n z₀ θ₀)
          rwa [sub_add_cancel] at h
      _ ≤ C₁ * dist p (z₀, θ₀) ^ (1 / 2 : ℝ) + √(((C₂ + 1) / (b - a) + 1) / (d - c)) :=
          add_le_add (hholder n p (z₀, θ₀) hp hq) hA
      _ ≤ C₁ * ((b - a) + (d - c)) ^ (1 / 2 : ℝ)
            + √(((C₂ + 1) / (b - a) + 1) / (d - c)) :=
          add_le_add (mul_le_mul_of_nonneg_left hrpow hC₁) le_rfl
      _ ≤ √(((C₂ + 1) / (b - a) + 1) / (d - c))
            + C₁ * ((b - a) + (d - c)) ^ (1 / 2 : ℝ) + 1 := by linarith

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.tendstoUniformlyOn_of_pointwise_of_equicont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif


end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.tendsto_backward_diffQuot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

theorem tendsto_backward_diffQuot {f : ℝ → ℝ} {x : ℝ} (hx : DifferentiableAt ℝ f x)
    {s : ℕ → ℝ} (hs : Filter.Tendsto s Filter.atTop (nhds 0)) (hspos : ∀ j, 0 < s j) :
    Filter.Tendsto (fun j => (f x - f (x - s j)) / s j) Filter.atTop (nhds (deriv f x)) := by
  -- `x - s j → x` and stays away from `x`, since `s j > 0`.
  have h1 : Filter.Tendsto (fun j => x - s j) Filter.atTop (nhdsWithin x {x}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds.sub hs)
    · filter_upwards with j
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      linarith [hspos j]
  -- Rewrite the backward difference quotient as the slope at `x - s j`.
  have h2 : Filter.Tendsto (fun j => slope f x (x - s j)) Filter.atTop (nhds (deriv f x)) :=
    (hx.hasDerivAt.tendsto_slope).comp h1
  have hfun : (fun j => slope f x (x - s j)) = fun j => (f x - f (x - s j)) / s j := by
    funext j
    rw [slope_def_field]
    ring_nf
  rwa [hfun] at h2

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.volume_box_sdiff_openBox =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- A point of `Icc a b` that is not in the open interval `Ioo a b` is one of the two
endpoints. -/
private lemma mem_pair_of_mem_Icc_not_mem_Ioo {a b x : ℝ} (hx : x ∈ Set.Icc a b)
    (hx' : x ∉ Set.Ioo a b) : x ∈ ({a, b} : Set ℝ) := by
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  obtain ⟨hax, hxb⟩ := hx
  rcases eq_or_lt_of_le hax with h | h
  · exact Or.inl h.symm
  · exact Or.inr (le_antisymm hxb (le_of_not_gt fun hlt => hx' ⟨h, hlt⟩))

/-- A pair of finite sets has measure zero in `ℝ × ℝ`. -/
private lemma volume_pair_prod_univ (a b : ℝ) :
    MeasureTheory.volume (({a, b} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
  have h0 : MeasureTheory.volume ({a, b} : Set ℝ) = 0 := by
    rw [Set.insert_eq, MeasureTheory.measure_union_null_iff]
    exact ⟨Real.volume_singleton, Real.volume_singleton⟩
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod, h0, zero_mul]

/-- A pair of finite sets has measure zero in `ℝ × ℝ`, vertical version. -/
private lemma volume_univ_prod_pair (c d : ℝ) :
    MeasureTheory.volume ((Set.univ : Set ℝ) ×ˢ ({c, d} : Set ℝ)) = 0 := by
  have h0 : MeasureTheory.volume ({c, d} : Set ℝ) = 0 := by
    rw [Set.insert_eq, MeasureTheory.measure_union_null_iff]
    exact ⟨Real.volume_singleton, Real.volume_singleton⟩
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod, h0, mul_zero]

theorem volume_box_sdiff_openBox (a b c d : ℝ) :
    MeasureTheory.volume ((Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)) \
      (Set.Ioo a b ×ˢ Set.Ioo c d : Set (ℝ × ℝ))) = 0 := by
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_union_null
    (volume_pair_prod_univ a b) (volume_univ_prod_pair c d))
  rintro ⟨x, y⟩ ⟨⟨hx, hy⟩, hnot⟩
  rw [Set.mem_union]
  by_cases hxy : x ∈ Set.Ioo a b
  · right
    exact ⟨Set.mem_univ x,
      mem_pair_of_mem_Icc_not_mem_Ioo hy fun hy' => hnot ⟨hxy, hy'⟩⟩
  · left
    exact ⟨mem_pair_of_mem_Icc_not_mem_Ioo hx hxy, Set.mem_univ y⟩

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.hasDerivWithinAt_of_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Set MeasureTheory
open scoped Topology

set_option linter.style.haveILetI false

namespace Work.FTS.StrongEps

/-!
# Derivative of a pointwise limit of `C¹` functions with uniformly bounded derivatives

If a sequence `g k` of functions on the interval `Icc 0 T` has derivatives `dk k` (within
`Icc 0 T`) which are continuous and uniformly bounded, and if `g k → G` and `dk k → D`
pointwise, then `G` has derivative `D` on `Icc 0 T`.

The proof goes through the integral representation: for each `k` the fundamental theorem of
calculus gives `∫ x in a..b, dk k x = g k b - g k a` on `Icc 0 T`; dominated convergence
(with the uniform bound `M` and the finite measure of `Icc 0 T`) lets `k → ∞`, producing
`G b - G a = ∫ x in a..b, D x`; the fundamental theorem of calculus for the continuous
integrand `D` then gives the one-sided derivative.
-/

/-- Fundamental theorem of calculus for each of the approximating functions. -/
private theorem ftc_each {T : ℝ} {g : ℕ → ℝ → ℝ} {dk : ℕ → ℝ → ℝ}
    (hderiv : ∀ k : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      HasDerivWithinAt (g k) (dk k τ) (Set.Icc 0 T) τ)
    (hcont : ∀ k : ℕ, ContinuousOn (dk k) (Set.Icc 0 T))
    (k : ℕ) {x y : ℝ} (hx : x ∈ Set.Icc 0 T) (hy : y ∈ Set.Icc 0 T) (hxy : x ≤ y) :
    ∫ s in x..y, dk k s = g k y - g k x := by
  have hsub : Set.Icc x y ⊆ Set.Icc 0 T := fun z hz =>
    ⟨le_trans hx.1 hz.1, le_trans hz.2 hy.2⟩
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy ?_ ?_ ?_
  · exact (HasDerivWithinAt.continuousOn (hderiv k)).mono hsub
  · intro z hz
    have hzT : z ∈ Set.Icc 0 T := ⟨le_trans hx.1 hz.1.le, le_trans hz.2.le hy.2⟩
    exact (hderiv k z hzT).hasDerivAt
      (Icc_mem_nhds (by linarith [hx.1, hz.1]) (by linarith [hy.2, hz.2]))
  · exact ((hcont k).mono (by rw [Set.uIcc_of_le hxy]; exact hsub)).intervalIntegrable

/-- Dominated convergence for the interval integrals of the derivatives. -/
private theorem tendsto_intervalIntegral {T : ℝ} {dk : ℕ → ℝ → ℝ} {D : ℝ → ℝ}
    (hcont : ∀ k : ℕ, ContinuousOn (dk k) (Set.Icc 0 T))
    (hbdd : ∃ M : ℝ, ∀ k : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 T → |dk k τ| ≤ M)
    (hd : ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      Filter.Tendsto (fun k : ℕ => dk k τ) Filter.atTop (nhds (D τ)))
    {x y : ℝ} (hx : x ∈ Set.Icc 0 T) (hy : y ∈ Set.Icc 0 T) (hxy : x ≤ y) :
    Filter.Tendsto (fun k : ℕ => ∫ s in x..y, dk k s) Filter.atTop
      (nhds (∫ s in x..y, D s)) := by
  obtain ⟨M, hM⟩ := hbdd
  have hsub : Set.Ioc x y ⊆ Set.Icc 0 T := fun z hz =>
    ⟨le_trans hx.1 hz.1.le, le_trans hz.2 hy.2⟩
  have hbound_int : Integrable (fun _ : ℝ => M) (volume.restrict (Set.Ioc x y)) := by
    rw [MeasureTheory.integrable_const_iff]
    right
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc x y)) (F := dk) (f := D) (fun _ : ℝ => M)
    (fun k => ((hcont k).mono hsub).aestronglyMeasurable measurableSet_Ioc)
    hbound_int
    (fun k => by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with a ha
      rw [Real.norm_eq_abs]
      exact hM k a (hsub ha))
    (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with a ha
      exact hd a (hsub ha))
  simpa only [intervalIntegral.integral_of_le hxy] using hmain

/-- The limit function `G` satisfies the integral identity `G b - G a = ∫ x in a..b, D x`. -/
private theorem G_sub_eq_integral {T : ℝ} {g : ℕ → ℝ → ℝ} {G D : ℝ → ℝ}
    {dk : ℕ → ℝ → ℝ}
    (hderiv : ∀ k : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      HasDerivWithinAt (g k) (dk k τ) (Set.Icc 0 T) τ)
    (hcont : ∀ k : ℕ, ContinuousOn (dk k) (Set.Icc 0 T))
    (hbdd : ∃ M : ℝ, ∀ k : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 T → |dk k τ| ≤ M)
    (hg : ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      Filter.Tendsto (fun k : ℕ => g k τ) Filter.atTop (nhds (G τ)))
    (hd : ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      Filter.Tendsto (fun k : ℕ => dk k τ) Filter.atTop (nhds (D τ)))
    {x y : ℝ} (hx : x ∈ Set.Icc 0 T) (hy : y ∈ Set.Icc 0 T) (hxy : x ≤ y) :
    G y - G x = ∫ s in x..y, D s := by
  have h1 : Filter.Tendsto (fun k : ℕ => g k y - g k x) Filter.atTop (nhds (G y - G x)) :=
    (hg y hy).sub (hg x hx)
  have h2 : Filter.Tendsto (fun k : ℕ => g k y - g k x) Filter.atTop
      (nhds (∫ s in x..y, D s)) := by
    have h3 := tendsto_intervalIntegral hcont hbdd hd hx hy hxy
    rw [show (fun k : ℕ => g k y - g k x) = fun k : ℕ => ∫ s in x..y, dk k s from
      funext fun k => (ftc_each hderiv hcont k hx hy hxy).symm]
    exact h3
  exact tendsto_nhds_unique h1 h2

/-- The fundamental theorem of calculus for the continuous limit derivative `D`: the map
`u ↦ ∫ s in 0..u, D s` has derivative `D τ` within `Icc 0 T` at `τ`. -/
private theorem hasDerivWithinAt_integral {T : ℝ} {D : ℝ → ℝ}
    (hDc : ContinuousOn D (Set.Icc 0 T)) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, D s) (D τ) (Set.Icc 0 T) τ := by
  haveI : Fact (τ ∈ Set.Icc 0 T) := ⟨hτ⟩
  have hsub : Set.uIcc 0 τ ⊆ Set.Icc 0 T := by
    rw [Set.uIcc_of_le hτ.1]
    exact fun z hz => ⟨hz.1, le_trans hz.2 hτ.2⟩
  refine intervalIntegral.integral_hasDerivWithinAt_right (f := D)
    (s := Set.Icc 0 T) (t := Set.Icc 0 T)
    ((hDc.mono hsub).intervalIntegrable) ?_ (hDc.continuousWithinAt hτ)
  exact ⟨Set.Icc 0 T, self_mem_nhdsWithin, hDc.aestronglyMeasurable measurableSet_Icc⟩

theorem hasDerivWithinAt_of_tendsto {T : ℝ} (hT : 0 ≤ T) {g : ℕ → ℝ → ℝ} {G D : ℝ → ℝ}
    {dk : ℕ → ℝ → ℝ}
    (hderiv : ∀ k : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      HasDerivWithinAt (g k) (dk k τ) (Set.Icc 0 T) τ)
    (hcont : ∀ k : ℕ, ContinuousOn (dk k) (Set.Icc 0 T))
    (hbdd : ∃ M : ℝ, ∀ k : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 T → |dk k τ| ≤ M)
    (hDc : ContinuousOn D (Set.Icc 0 T))
    (hg : ∀ τ : ℝ, τ ∈ Set.Icc 0 T → Filter.Tendsto (fun k : ℕ => g k τ) Filter.atTop (nhds (G τ)))
    (hd : ∀ τ : ℝ, τ ∈ Set.Icc 0 T → Filter.Tendsto (fun k : ℕ => dk k τ) Filter.atTop (nhds (D τ))) :
    ∀ τ : ℝ, τ ∈ Set.Icc 0 T → HasDerivWithinAt G (D τ) (Set.Icc 0 T) τ := by
  intro τ hτ
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hG : ∀ y ∈ Set.Icc 0 T, G y = G 0 + ∫ s in (0 : ℝ)..y, D s := by
    intro y hy
    have h := G_sub_eq_integral hderiv hcont hbdd hg hd h0 hy hy.1
    linarith
  have hF := (hasDerivWithinAt_integral hDc hτ).const_add (G 0)
  exact hF.congr (fun y hy => hG y hy) (hG τ hτ)

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.EqcAux.smoothIntervalCutoff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.EqcAux

/-- A smooth (C^∞) cutoff function which is `1` on `[a,b]` and `0` outside `[a',b']`,
whenever `a' < a` and `b < b'`.

It is built as a product of two translates of `Real.smoothTransition`:
`x ↦ st ((x - a')/(a - a')) * st ((b' - x)/(b' - b))`. -/
theorem smoothIntervalCutoff {a' a b b' : ℝ} (h1 : a' < a) (h3 : b < b') :
    ∃ g : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n g) ∧ HasCompactSupport g ∧
      (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ 1) ∧
      (∀ x ∈ Set.Icc a b, g x = 1) ∧ (∀ x ∉ Set.Icc a' b', g x = 0) := by
  set c1 : ℝ := (a - a')⁻¹ with hc1def
  set c2 : ℝ := (b' - b)⁻¹ with hc2def
  have hc1pos : 0 < c1 := by rw [hc1def]; exact inv_pos.mpr (by linarith)
  have hc2pos : 0 < c2 := by rw [hc2def]; exact inv_pos.mpr (by linarith)
  have h1ne : a - a' ≠ 0 := by linarith
  have h3ne : b' - b ≠ 0 := by linarith
  have hzero : ∀ x : ℝ, x ∉ Set.Icc a' b' →
      Real.smoothTransition (c1 * (x - a')) * Real.smoothTransition (c2 * (b' - x)) = 0 := by
    intro x hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [Real.smoothTransition.zero_of_nonpos
          (le_of_lt (mul_neg_of_pos_of_neg hc1pos (by linarith))), zero_mul]
    · rw [Real.smoothTransition.zero_of_nonpos
          (le_of_lt (mul_neg_of_pos_of_neg hc2pos (by linarith))), mul_zero]
  have hcs : HasCompactSupport
      (fun x : ℝ => Real.smoothTransition (c1 * (x - a')) *
        Real.smoothTransition (c2 * (b' - x))) :=
    HasCompactSupport.intro' (K := Set.Icc a' b') isCompact_Icc isClosed_Icc hzero
  have hsm : ∀ n : ℕ, ContDiff ℝ n
      (fun x : ℝ => Real.smoothTransition (c1 * (x - a')) *
        Real.smoothTransition (c2 * (b' - x))) := by
    intro n
    have h1n : ContDiff ℝ n (fun x : ℝ => Real.smoothTransition (c1 * (x - a'))) :=
      Real.smoothTransition.contDiff.comp
        (contDiff_const.mul (contDiff_id.sub contDiff_const))
    have h2n : ContDiff ℝ n (fun x : ℝ => Real.smoothTransition (c2 * (b' - x))) :=
      Real.smoothTransition.contDiff.comp
        (contDiff_const.mul (contDiff_const.sub contDiff_id))
    exact h1n.mul h2n
  have hnn : ∀ x : ℝ, 0 ≤ Real.smoothTransition (c1 * (x - a')) *
      Real.smoothTransition (c2 * (b' - x)) :=
    fun x => mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hle : ∀ x : ℝ, Real.smoothTransition (c1 * (x - a')) *
      Real.smoothTransition (c2 * (b' - x)) ≤ 1 := by
    intro x
    have hp2 : 0 ≤ Real.smoothTransition (c2 * (b' - x)) := Real.smoothTransition.nonneg _
    calc Real.smoothTransition (c1 * (x - a')) * Real.smoothTransition (c2 * (b' - x))
        ≤ 1 * Real.smoothTransition (c2 * (b' - x)) :=
          mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) hp2
      _ = Real.smoothTransition (c2 * (b' - x)) := one_mul _
      _ ≤ 1 := Real.smoothTransition.le_one _
  have hone : ∀ x ∈ Set.Icc a b, Real.smoothTransition (c1 * (x - a')) *
      Real.smoothTransition (c2 * (b' - x)) = 1 := by
    intro x hx
    have he1 : 1 ≤ c1 * (x - a') := by
      have h : c1 * (a - a') ≤ c1 * (x - a') :=
        mul_le_mul_of_nonneg_left (by linarith [hx.1]) (le_of_lt hc1pos)
      have h' : c1 * (a - a') = 1 := by rw [hc1def, inv_mul_cancel₀ h1ne]
      linarith
    have he2 : 1 ≤ c2 * (b' - x) := by
      have h : c2 * (b' - b) ≤ c2 * (b' - x) :=
        mul_le_mul_of_nonneg_left (by linarith [hx.2]) (le_of_lt hc2pos)
      have h' : c2 * (b' - b) = 1 := by rw [hc2def, inv_mul_cancel₀ h3ne]
      linarith
    rw [Real.smoothTransition.one_of_one_le he1, Real.smoothTransition.one_of_one_le he2,
      mul_one]
  exact ⟨fun x => Real.smoothTransition (c1 * (x - a')) *
      Real.smoothTransition (c2 * (b' - x)), hsm, hcs, hnn, hle, hone, hzero⟩

end Work.FTS.StrongLWP.Sobolev.EqcAux
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.abs_sub_le_mul_integral_norm_fderiv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

theorem abs_sub_le_mul_integral_norm_fderiv {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v)
    (hseg : ∀ p z : ℝ × ℝ, v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p))
    (w z : ℝ × ℝ) :
    |v z - v w| ≤ ‖z - w‖ * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v (w + t • (z - w))‖ := by
  -- `fderiv ℝ v` is continuous, since `v` is `C¹`
  have hfd := hv.continuous_fderiv (by norm_num)
  have hcont : Continuous fun t : ℝ => fderiv ℝ v (w + t • (z - w)) :=
    hfd.comp (continuous_const.add (continuous_id.smul continuous_const))
  -- rewrite the difference as the segment integral given by `hseg`
  rw [hseg w z, ← Real.norm_eq_abs]
  calc ‖∫ t in (0:ℝ)..1, (fderiv ℝ v (w + t • (z - w))) (z - w)‖
      ≤ ∫ t in (0:ℝ)..1, ‖z - w‖ * ‖fderiv ℝ v (w + t • (z - w))‖ := by
        -- the norm of the integral is at most the integral of the norms, and each
        -- integrand is bounded by `‖z - w‖` times the operator norm
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        · filter_upwards with t ht
          have h := ContinuousLinearMap.le_opNorm (fderiv ℝ v (w + t • (z - w))) (z - w)
          rw [mul_comm] at h
          exact h
        · exact (hcont.norm.const_mul _).intervalIntegrable _ _
    _ = ‖z - w‖ * ∫ t in (0:ℝ)..1, ‖fderiv ℝ v (w + t • (z - w))‖ :=
        intervalIntegral.integral_const_mul _ _

end Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.arith_final =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

/-- Auxiliary: `(4 a ^ 2) ^ (3/4) * sqrt a = 2 * sqrt 2 * a ^ 2` for `a > 0`. -/
private lemma rpow_four_sq_mul_sqrt {a : ℝ} (ha : 0 < a) :
    (4 * a ^ 2) ^ (3 / 4 : ℝ) * Real.sqrt a = 2 * Real.sqrt 2 * a ^ 2 := by
  have hsplit : (4 * a ^ 2) ^ (3 / 4 : ℝ) = 4 ^ ((3 : ℝ) / 4) * a ^ ((3 : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) ≤ a ^ 2)]
    congr 1
    rw [← Real.rpow_natCast a 2, ← Real.rpow_mul (le_of_lt ha)]
    norm_num
  have h4 : (4 : ℝ) ^ ((3 : ℝ) / 4) = 2 * Real.sqrt 2 := by
    have h2 : ((2 : ℝ) ^ (2 : ℝ)) = 4 := by norm_num [Real.rpow_natCast]
    calc (4 : ℝ) ^ ((3 : ℝ) / 4) = ((2 : ℝ) ^ (2 : ℝ)) ^ ((3 : ℝ) / 4) := by rw [h2]
      _ = (2 : ℝ) ^ ((2 : ℝ) * ((3 : ℝ) / 4)) := by
            rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ ((3 : ℝ) / 2) := by
            rw [show (2 : ℝ) * ((3 : ℝ) / 4) = (3 : ℝ) / 2 by norm_num]
      _ = (2 : ℝ) ^ ((1 : ℝ) + 1 / 2) := by
            rw [show (3 : ℝ) / 2 = (1 : ℝ) + 1 / 2 by norm_num]
      _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = 2 * Real.sqrt 2 := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  calc (4 * a ^ 2) ^ (3 / 4 : ℝ) * Real.sqrt a
      = (4 ^ ((3 : ℝ) / 4) * a ^ ((3 : ℝ) / 2)) * Real.sqrt a := by rw [hsplit]
    _ = (2 * Real.sqrt 2 * a ^ ((3 : ℝ) / 2)) * Real.sqrt a := by rw [h4]
    _ = 2 * Real.sqrt 2 * (a ^ ((3 : ℝ) / 2) * Real.sqrt a) := by ring
    _ = 2 * Real.sqrt 2 * (a ^ ((3 : ℝ) / 2) * a ^ ((1 : ℝ) / 2)) := by
          rw [Real.sqrt_eq_rpow a]
    _ = 2 * Real.sqrt 2 * a ^ ((3 : ℝ) / 2 + 1 / 2) := by rw [← Real.rpow_add ha]
    _ = 2 * Real.sqrt 2 * a ^ (2 : ℕ) := by
          rw [show (3 : ℝ) / 2 + 1 / 2 = 2 by norm_num]
          norm_num [Real.rpow_natCast]

theorem arith_final {a d I : ℝ} (ha : 0 < a) :
    (1 / (4 * a ^ 2)) * ((a + d) * (2 * (4 * a ^ 2) ^ (3 / 4 : ℝ) * I))
      = Real.sqrt 2 * I * ((a + d) / Real.sqrt a) := by
  have hXa : (4 * a ^ 2) ^ (3 / 4 : ℝ) = 2 * Real.sqrt 2 * a ^ 2 / Real.sqrt a := by
    rw [eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr ha))]
    exact rpow_four_sq_mul_sqrt ha
  rw [hXa]
  field_simp
  ring

end Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.integral_abs_le_L4_mul_vol =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

/-- **Hölder with exponents `p = 4`, `q = 4/3`.**  On a set of finite measure, the `L¹` norm of
`f` is controlled by the `L⁴` norm times `(volume s)^{3/4}`. -/
theorem integral_abs_le_L4_mul_vol {s : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hs : MeasureTheory.volume s < ⊤)
    (hf : MeasureTheory.MemLp f 4 (MeasureTheory.volume.restrict s)) :
    ∫ x in s, |f x| ≤ (MeasureTheory.volume s).toReal ^ (3 / 4 : ℝ)
      * (∫ x in s, |f x| ^ 4) ^ (1 / 4 : ℝ) := by
  have hpq : (4 : ℝ).HolderConjugate (4 / 3 : ℝ) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hf' : MemLp f (ENNReal.ofReal (4 : ℝ)) (MeasureTheory.volume.restrict s) := by
    simpa using hf
  -- `s` has finite measure, so the constant function `1` lies in `L^{4/3}` on it
  have hg : MemLp (fun _ : ℝ × ℝ => (1 : ℝ)) (ENNReal.ofReal (4 / 3))
      (MeasureTheory.volume.restrict s) := by
    rw [memLp_const_iff (p := ENNReal.ofReal (4 / 3)) (c := (1 : ℝ))
      (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)) ENNReal.ofReal_ne_top]
    right
    rw [Measure.restrict_apply_univ]
    exact hs
  have hmain := integral_mul_norm_le_Lp_mul_Lq (μ := MeasureTheory.volume.restrict s)
    (f := f) (g := fun _ : ℝ × ℝ => (1 : ℝ)) hpq hf' hg
  -- the two `L^p` factors simplify to the two quantities in the statement
  have hA : ∫ a, ‖f a‖ ^ (4 : ℝ) ∂(MeasureTheory.volume.restrict s)
      = ∫ x in s, |f x| ^ 4 := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.rpow_ofNat]
  have hB : ∫ a, ‖(1 : ℝ)‖ ^ ((4 : ℝ) / 3) ∂(MeasureTheory.volume.restrict s)
      = (MeasureTheory.volume s).toReal := by
    simp [Measure.real_def]
  rw [hA, hB] at hmain
  calc ∫ x in s, |f x|
      = ∫ a, ‖f a‖ * ‖(1 : ℝ)‖ ∂(MeasureTheory.volume.restrict s) := by
        simp [Real.norm_eq_abs]
    _ ≤ _ := hmain
    _ = (MeasureTheory.volume s).toReal ^ (3 / 4 : ℝ)
          * (∫ x in s, |f x| ^ 4) ^ (1 / 4 : ℝ) := by
        rw [show (1 : ℝ) / (4 / 3) = 3 / 4 by norm_num, mul_comm]

end Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.integral_ball_integral_swap =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

theorem integral_ball_integral_swap {F : (ℝ × ℝ) → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    {a : ℝ} (ha : 0 < a) :
    ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, (∫ t in (0 : ℝ)..1, F ζ t)
      = ∫ t in (0 : ℝ)..1, ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, F ζ t := by
  -- `F` is continuous, so it is integrable on any product of a compact slab and a compact ball;
  -- we then apply Fubini in the form `intervalIntegral_integral_swap`.
  have hcont : Continuous (fun p : ℝ × (ℝ × ℝ) => F p.2 p.1) :=
    hF.comp continuous_swap
  -- the compact set `[0,1] × closedBall 0 a`, which contains `uIoc 0 1 × ball 0 a`
  have hcpt : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℝ × ℝ) a) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hint : MeasureTheory.IntegrableOn (fun p : ℝ × (ℝ × ℝ) => F p.2 p.1)
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℝ × ℝ) a) MeasureTheory.volume :=
    ContinuousOn.integrableOn_compact hcpt hcont.continuousOn
  have hsub : Set.uIoc (0 : ℝ) 1 ×ˢ Metric.ball (0 : ℝ × ℝ) a ⊆
      Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℝ × ℝ) a := by
    intro p hp
    rw [Set.uIoc_of_le zero_le_one] at hp
    exact ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, Metric.ball_subset_closedBall hp.2⟩
  -- integrability of the uncurried integrand for the product measure
  have hInt : MeasureTheory.Integrable (fun p : ℝ × (ℝ × ℝ) => F p.2 p.1)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (MeasureTheory.volume.restrict (Metric.ball (0 : ℝ × ℝ) a))) := by
    rw [MeasureTheory.Measure.prod_restrict,
      ← MeasureTheory.Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    exact MeasureTheory.IntegrableOn.mono_set hint hsub
  have hInt' : MeasureTheory.Integrable (Function.uncurry (fun t ζ => F ζ t))
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (MeasureTheory.volume.restrict (Metric.ball (0 : ℝ × ℝ) a))) := hInt
  exact (MeasureTheory.intervalIntegral_integral_swap
    (μ := MeasureTheory.volume.restrict (Metric.ball (0 : ℝ × ℝ) a))
    (f := fun t ζ => F ζ t) hInt').symm

end Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.rpow_scale_identity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

theorem rpow_scale_identity {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (t ^ 2)⁻¹ * (4 * (t * a) ^ 2) ^ (3 / 4 : ℝ) = (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (-1 / 2 : ℝ) := by
  -- `(t ^ 2) ^ (3/4) = t ^ (3/2)` for `t > 0`
  have hA : (t ^ 2) ^ (3 / 4 : ℝ) = t ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast_mul (le_of_lt ht) 2 (3 / 4)]
    norm_num
  -- pull the factor `t ^ 2` out of the base `4 * (t * a) ^ 2 = (4 * a ^ 2) * t ^ 2`
  have hkey : (4 * (t * a) ^ 2) ^ (3 / 4 : ℝ) = (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (3 / 2 : ℝ) := by
    have hta : 4 * (t * a) ^ 2 = (4 * a ^ 2) * (t ^ 2) := by ring
    rw [hta, Real.mul_rpow (by positivity) (by positivity), hA]
  -- the remaining power bookkeeping: `(t ^ 2)⁻¹ * t ^ (3/2) = t ^ (-1/2)`
  have hc : (t ^ 2)⁻¹ * t ^ (3 / 2 : ℝ) = t ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_ofNat t 2, ← Real.rpow_neg (le_of_lt ht) 2, ← Real.rpow_add ht (-2) (3 / 2)]
    norm_num
  rw [hkey]
  calc (t ^ 2)⁻¹ * ((4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (3 / 2 : ℝ))
      = (4 * a ^ 2) ^ (3 / 4 : ℝ) * ((t ^ 2)⁻¹ * t ^ (3 / 2 : ℝ)) := by ring
    _ = (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (-1 / 2 : ℝ) := by rw [hc]

end Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D.setIntegral_comp_smul_add_ball =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Pointwise

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

/-- Change of variables for the Lebesgue integral over a ball of `ℝ × ℝ` (with the product,
i.e. sup, norm) under the affine map `y ↦ c + t • y` with `t > 0`: the ball of radius `a` centred
at `0` is transported to the ball of radius `t * a` centred at `c`, at the price of the Jacobian
factor `(t ^ 2)⁻¹` (the dimension being `2`). -/
theorem setIntegral_comp_smul_add_ball (f : ℝ × ℝ → ℝ) {a t : ℝ} (ht : 0 < t) (c : ℝ × ℝ) :
    ∫ y in Metric.ball (0 : ℝ × ℝ) a, f (c + t • y)
      = (t ^ 2)⁻¹ * ∫ w in Metric.ball c (t * a), f w := by
  have ht0 : t ≠ 0 := ht.ne'
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hsmulball : t • Metric.ball (0 : ℝ × ℝ) a = Metric.ball (0 : ℝ × ℝ) (t * a) := by
    rw [smul_ball ht0, smul_zero, Real.norm_of_nonneg ht.le]
  -- the image of a ball under the translation `x ↦ c + x`
  have himg : (fun x : ℝ × ℝ => c + x) '' Metric.ball (0 : ℝ × ℝ) (t * a)
      = Metric.ball c (t * a) := by
    rw [show (fun x : ℝ × ℝ => c + x) = (fun x : ℝ × ℝ => c +ᵥ x) from by
      funext x; rw [vadd_eq_add]]
    rw [Set.image_vadd, Metric.vadd_ball]
    simp [vadd_eq_add]
  -- translation invariance of the set integral
  have htrans : ∫ x in Metric.ball (0 : ℝ × ℝ) (t * a), f (c + x)
      = ∫ w in Metric.ball c (t * a), f w := by
    have h1 : MeasureTheory.MeasurePreserving (fun x : ℝ × ℝ => c + x) MeasureTheory.volume
        MeasureTheory.volume := MeasureTheory.measurePreserving_add_left _ c
    have h2 : MeasurableEmbedding (fun x : ℝ × ℝ => c + x) := by
      have := (Homeomorph.addLeft c).measurableEmbedding
      simpa using this
    have h3 := MeasureTheory.MeasurePreserving.setIntegral_image_emb h1 h2 f
      (Metric.ball (0 : ℝ × ℝ) (t * a))
    rw [himg] at h3
    exact h3.symm
  calc ∫ y in Metric.ball (0 : ℝ × ℝ) a, f (c + t • y)
      = ∫ y in Metric.ball (0 : ℝ × ℝ) a, (fun x => f (c + x)) (t • y) := rfl
    _ = (t ^ Module.finrank ℝ (ℝ × ℝ))⁻¹ • ∫ x in t • Metric.ball (0 : ℝ × ℝ) a, f (c + x) :=
        MeasureTheory.Measure.setIntegral_comp_smul_of_pos (μ := MeasureTheory.volume)
          (fun x => f (c + x)) (Metric.ball (0 : ℝ × ℝ) a) ht
    _ = (t ^ 2)⁻¹ * ∫ x in Metric.ball (0 : ℝ × ℝ) (t * a), f (c + x) := by
        rw [hsmulball, hfin, smul_eq_mul]
    _ = (t ^ 2)⁻¹ * ∫ w in Metric.ball c (t * a), f w := by rw [htrans]

end Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.NashData.integrable_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.NashData

open MeasureTheory

theorem integrable_facts {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (u p) ^ 2) ∧
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (u p) ^ 4) ∧
    MeasureTheory.Integrable (fun p : ℝ × ℝ => ‖fderiv ℝ u p‖ ^ 2) ∧
    MeasureTheory.Integrable (fun t : ℝ => ∫ s : ℝ, (u (s, t)) ^ 2) ∧
    MeasureTheory.Integrable (fun s : ℝ => ∫ t : ℝ, (u (s, t)) ^ 2) ∧
    MeasureTheory.Integrable (fun t : ℝ => ∫ s : ℝ, (fderiv ℝ u (s, t) (1, 0)) ^ 2) ∧
    MeasureTheory.Integrable (fun s : ℝ => ∫ t : ℝ, (fderiv ℝ u (s, t) (0, 1)) ^ 2) ∧
    (∫ t : ℝ, ∫ s : ℝ, (u (s, t)) ^ 2) = ∫ p : ℝ × ℝ, (u p) ^ 2 ∧
    (∫ s : ℝ, ∫ t : ℝ, (u (s, t)) ^ 2) = ∫ p : ℝ × ℝ, (u p) ^ 2 ∧
    (∫ t : ℝ, ∫ s : ℝ, (fderiv ℝ u (s, t) (1, 0)) ^ 2) ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 ∧
    (∫ s : ℝ, ∫ t : ℝ, (fderiv ℝ u (s, t) (0, 1)) ^ 2) ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := by
  have hcont : Continuous u := hu.continuous
  have hcontD : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  -- compact support of the powers
  have hcs2 : HasCompactSupport (fun p : ℝ × ℝ => (u p) ^ 2) :=
    hc.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hcs4 : HasCompactSupport (fun p : ℝ × ℝ => (u p) ^ 4) :=
    hc.comp_left (g := fun x : ℝ => x ^ 4) (by simp)
  have h2 : Integrable (fun p : ℝ × ℝ => (u p) ^ 2) :=
    (hcont.pow 2).integrable_of_hasCompactSupport hcs2
  have h4 : Integrable (fun p : ℝ × ℝ => (u p) ^ 4) :=
    (hcont.pow 4).integrable_of_hasCompactSupport hcs4
  -- the derivative
  have hcD : HasCompactSupport (fderiv ℝ u) := HasCompactSupport.fderiv ℝ hc
  have hcsD : HasCompactSupport (fun p : ℝ × ℝ => ‖fderiv ℝ u p‖ ^ 2) :=
    (hcD.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => ‖L‖) (by simp)).comp_left
      (g := fun x : ℝ => x ^ 2) (by simp)
  have hg2 : Integrable (fun p : ℝ × ℝ => ‖fderiv ℝ u p‖ ^ 2) :=
    (hcontD.norm.pow 2).integrable_of_hasCompactSupport hcsD
  -- directional derivatives
  have hDcont1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ u p (1, 0)) :=
    hcontD.clm_apply continuous_const
  have hDcont2 : Continuous (fun p : ℝ × ℝ => fderiv ℝ u p (0, 1)) :=
    hcontD.clm_apply continuous_const
  have hpw1 : ∀ p : ℝ × ℝ, (fderiv ℝ u p (1, 0)) ^ 2 ≤ ‖fderiv ℝ u p‖ ^ 2 := by
    intro p
    have h : ‖fderiv ℝ u p (1, 0)‖ ≤ ‖fderiv ℝ u p‖ := by
      have := ContinuousLinearMap.le_opNorm (fderiv ℝ u p) ((1, 0) : ℝ × ℝ)
      simpa using this
    calc (fderiv ℝ u p (1, 0)) ^ 2 = ‖fderiv ℝ u p (1, 0)‖ ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]
      _ ≤ ‖fderiv ℝ u p‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hpw2 : ∀ p : ℝ × ℝ, (fderiv ℝ u p (0, 1)) ^ 2 ≤ ‖fderiv ℝ u p‖ ^ 2 := by
    intro p
    have h : ‖fderiv ℝ u p (0, 1)‖ ≤ ‖fderiv ℝ u p‖ := by
      have := ContinuousLinearMap.le_opNorm (fderiv ℝ u p) ((0, 1) : ℝ × ℝ)
      simpa using this
    calc (fderiv ℝ u p (0, 1)) ^ 2 = ‖fderiv ℝ u p (0, 1)‖ ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]
      _ ≤ ‖fderiv ℝ u p‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hD1 : Integrable (fun p : ℝ × ℝ => (fderiv ℝ u p (1, 0)) ^ 2) :=
    hg2.mono' (hDcont1.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hpw1 p)
  have hD2 : Integrable (fun p : ℝ × ℝ => (fderiv ℝ u p (0, 1)) ^ 2) :=
    hg2.mono' (hDcont2.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hpw2 p)
  -- product measure form
  have h2p : Integrable (fun p : ℝ × ℝ => (u p) ^ 2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact h2
  have hD1p : Integrable (fun p : ℝ × ℝ => (fderiv ℝ u p (1, 0)) ^ 2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hD1
  have hD2p : Integrable (fun p : ℝ × ℝ => (fderiv ℝ u p (0, 1)) ^ 2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hD2
  -- marginal integrability
  have hIt2 : Integrable (fun t : ℝ => ∫ s : ℝ, (u (s, t)) ^ 2) := by
    simpa using h2p.integral_prod_right
  have hIs2 : Integrable (fun s : ℝ => ∫ t : ℝ, (u (s, t)) ^ 2) := by
    simpa using h2p.integral_prod_left
  have hIt1 : Integrable (fun t : ℝ => ∫ s : ℝ, (fderiv ℝ u (s, t) (1, 0)) ^ 2) := by
    simpa using hD1p.integral_prod_right
  have hIs1 : Integrable (fun s : ℝ => ∫ t : ℝ, (fderiv ℝ u (s, t) (0, 1)) ^ 2) := by
    simpa using hD2p.integral_prod_left
  -- Fubini equalities
  have heq8 : (∫ t : ℝ, ∫ s : ℝ, (u (s, t)) ^ 2) = ∫ p : ℝ × ℝ, (u p) ^ 2 := by
    have h := (MeasureTheory.integral_prod_symm (fun p : ℝ × ℝ => (u p) ^ 2) h2p).symm
    rw [← Measure.volume_eq_prod] at h
    exact h
  have heq9 : (∫ s : ℝ, ∫ t : ℝ, (u (s, t)) ^ 2) = ∫ p : ℝ × ℝ, (u p) ^ 2 := by
    have h := (MeasureTheory.integral_prod (fun p : ℝ × ℝ => (u p) ^ 2) h2p).symm
    rw [← Measure.volume_eq_prod] at h
    exact h
  -- the two inequalities
  have hineq1 : (∫ t : ℝ, ∫ s : ℝ, (fderiv ℝ u (s, t) (1, 0)) ^ 2) ≤
      ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := by
    calc (∫ t : ℝ, ∫ s : ℝ, (fderiv ℝ u (s, t) (1, 0)) ^ 2)
        = ∫ p : ℝ × ℝ, (fderiv ℝ u p (1, 0)) ^ 2 :=
          (MeasureTheory.integral_prod_symm (fun p : ℝ × ℝ => (fderiv ℝ u p (1, 0)) ^ 2)
            hD1p).symm
      _ ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := MeasureTheory.integral_mono hD1 hg2 hpw1
  have hineq2 : (∫ s : ℝ, ∫ t : ℝ, (fderiv ℝ u (s, t) (0, 1)) ^ 2) ≤
      ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := by
    calc (∫ s : ℝ, ∫ t : ℝ, (fderiv ℝ u (s, t) (0, 1)) ^ 2)
        = ∫ p : ℝ × ℝ, (fderiv ℝ u p (0, 1)) ^ 2 :=
          (MeasureTheory.integral_prod (fun p : ℝ × ℝ => (fderiv ℝ u p (0, 1)) ^ 2) hD2p).symm
      _ ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := MeasureTheory.integral_mono hD2 hg2 hpw2
  exact ⟨h2, h4, hg2, hIt2, hIs2, hIt1, hIs1, heq8, heq9, hineq1, hineq2⟩

end Work.FTS.StrongLWP.Sobolev.HolderHalf.NashData
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.NashData.slice_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.NashData

theorem slice_facts {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (∀ t : ℝ, ContDiff ℝ 1 fun s : ℝ => u (s, t)) ∧
    (∀ s : ℝ, ContDiff ℝ 1 fun t : ℝ => u (s, t)) ∧
    (∀ t : ℝ, HasCompactSupport fun s : ℝ => u (s, t)) ∧
    (∀ s : ℝ, HasCompactSupport fun t : ℝ => u (s, t)) ∧
    (∀ s t : ℝ, deriv (fun r : ℝ => u (r, t)) s = fderiv ℝ u (s, t) (1, 0)) ∧
    (∀ s t : ℝ, (deriv (fun r : ℝ => u (r, t)) s) ^ 2 ≤ ‖fderiv ℝ u (s, t)‖ ^ 2) ∧
    (∀ s t : ℝ, (deriv (fun r : ℝ => u (s, r)) t) ^ 2 ≤ ‖fderiv ℝ u (s, t)‖ ^ 2) := by
  -- `u` is differentiable on all of `ℝ × ℝ` (it is `C¹`), with derivative `fderiv ℝ u p` at `p`.
  have hdiff : ∀ p : ℝ × ℝ, HasFDerivAt (𝕜 := ℝ) u (fderiv ℝ u p) p :=
    fun p => (hu.differentiable (by norm_num) p).hasFDerivAt
  -- the derivative of a slice is the derivative of `u` applied to `(1,0)` resp. `(0,1)`
  have hslice₁ : ∀ s t : ℝ,
      deriv (fun r : ℝ => u (r, t)) s = fderiv ℝ u (s, t) (1, 0) := by
    intro s t
    have h1 : HasFDerivAt (𝕜 := ℝ) (fun r : ℝ => (r, t)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s :=
      hasFDerivAt_prodMk_left s t
    have h2 : HasFDerivAt (𝕜 := ℝ) (fun r : ℝ => u (r, t))
        ((fderiv ℝ u (s, t)) ∘SL (ContinuousLinearMap.inl ℝ ℝ ℝ)) s :=
      (hdiff (s, t)).comp s h1
    rw [← fderiv_apply_one_eq_deriv, h2.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply]
  have hslice₂ : ∀ s t : ℝ,
      deriv (fun r : ℝ => u (s, r)) t = fderiv ℝ u (s, t) (0, 1) := by
    intro s t
    have h1 : HasFDerivAt (𝕜 := ℝ) (fun r : ℝ => (s, r)) (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
      hasFDerivAt_prodMk_right s t
    have h2 : HasFDerivAt (𝕜 := ℝ) (fun r : ℝ => u (s, r))
        ((fderiv ℝ u (s, t)) ∘SL (ContinuousLinearMap.inr ℝ ℝ ℝ)) t :=
      (hdiff (s, t)).comp t h1
    rw [← fderiv_apply_one_eq_deriv, h2.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply]
  refine ⟨?_, ?_, ?_, ?_, hslice₁, ?_, ?_⟩
  · -- first coordinate slices of a `C¹` function are `C¹`
    intro t
    have h : ContDiff ℝ 1 (fun s : ℝ => (s, t)) :=
      (contDiff_id : ContDiff ℝ 1 (id : ℝ → ℝ)).prodMk (contDiff_const (c := t))
    simpa [Function.comp_def] using hu.comp h
  · -- second coordinate slices of a `C¹` function are `C¹`
    intro s
    have h : ContDiff ℝ 1 (fun t : ℝ => (s, t)) :=
      (contDiff_const (c := s)).prodMk (contDiff_id : ContDiff ℝ 1 (id : ℝ → ℝ))
    simpa [Function.comp_def] using hu.comp h
  · -- first coordinate slices of a compactly supported function are compactly supported
    intro t
    have hsub : Function.support (fun s : ℝ => u (s, t)) ⊆ Prod.fst '' tsupport u := by
      intro s hs
      exact ⟨(s, t), subset_tsupport u (by simpa [Function.mem_support] using hs), rfl⟩
    exact IsCompact.of_isClosed_subset (hc.image continuous_fst) (isClosed_tsupport _)
      (closure_minimal hsub (hc.image continuous_fst).isClosed)
  · -- second coordinate slices of a compactly supported function are compactly supported
    intro s
    have hsub : Function.support (fun t : ℝ => u (s, t)) ⊆ Prod.snd '' tsupport u := by
      intro t ht
      exact ⟨(s, t), subset_tsupport u (by simpa [Function.mem_support] using ht), rfl⟩
    exact IsCompact.of_isClosed_subset (hc.image continuous_snd) (isClosed_tsupport _)
      (closure_minimal hsub (hc.image continuous_snd).isClosed)
  · -- `(∂ₛ u)² ≤ ‖Du‖²` because `‖(1,0)‖ = 1`
    intro s t
    have hle : ‖fderiv ℝ u (s, t) (1, 0)‖ ≤ ‖fderiv ℝ u (s, t)‖ := by
      have h := ContinuousLinearMap.le_opNorm (fderiv ℝ u (s, t)) ((1 : ℝ), (0 : ℝ))
      simpa [Prod.norm_def] using h
    rw [hslice₁ s t]
    calc (fderiv ℝ u (s, t) (1, 0)) ^ 2 = ‖fderiv ℝ u (s, t) (1, 0)‖ ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]
      _ ≤ ‖fderiv ℝ u (s, t)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  · -- `(∂ₜ u)² ≤ ‖Du‖²` because `‖(0,1)‖ = 1`
    intro s t
    have hle : ‖fderiv ℝ u (s, t) (0, 1)‖ ≤ ‖fderiv ℝ u (s, t)‖ := by
      have h := ContinuousLinearMap.le_opNorm (fderiv ℝ u (s, t)) ((0 : ℝ), (1 : ℝ))
      simpa [Prod.norm_def] using h
    rw [hslice₂ s t]
    calc (fderiv ℝ u (s, t) (0, 1)) ^ 2 = ‖fderiv ℝ u (s, t) (0, 1)‖ ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]
      _ ≤ ‖fderiv ℝ u (s, t)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2

end Work.FTS.StrongLWP.Sobolev.HolderHalf.NashData
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.one_dim_agmon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

open MeasureTheory

/-- **One-dimensional Agmon inequality.**
For a `C¹` function `f : ℝ → ℝ` with compact support and every `y : ℝ`,
`(f y) ^ 2 ≤ 2 * √(∫ f²) * √(∫ (f')²)`.

Proof: since `f` is `C¹` with compact support, the fundamental theorem of calculus applied to
`f²` on `(-∞, y]` (this is `HasCompactSupport.integral_Iic_deriv_eq`) gives
`(f y) ^ 2 = ∫_{Iic y} 2 f f'`, and Cauchy–Schwarz for `L²` bounds the integral of `f f'` by
`√(∫_{Iic y} f²) √(∫_{Iic y} (f')²)`, which is at most `√(∫ f²) √(∫ (f')²)`. -/
theorem one_dim_agmon {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∀ y : ℝ, (f y) ^ 2 ≤ 2 * Real.sqrt (∫ x : ℝ, (f x) ^ 2) * Real.sqrt (∫ x : ℝ, (deriv f x) ^ 2) := by
  intro y
  -- `f ^ 2` and `(f') ^ 2` have compact support
  have hsq_supp : HasCompactSupport (fun x => f x ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hdsq_supp : HasCompactSupport (fun x => deriv f x ^ 2) :=
    hc.deriv.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  -- Fundamental theorem of calculus on `(-∞, y]`
  have hFTC : (f y) ^ 2 = ∫ x in Set.Iic y, 2 * f x * deriv f x := by
    have hF := HasCompactSupport.integral_Iic_deriv_eq (hf.pow 2) hsq_supp y
    rw [← hF]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hd : HasDerivAt (fun x => f x ^ 2) (2 * f x * deriv f x) x := by
      have h : HasDerivAt f (deriv f x) x := (hf.differentiable one_ne_zero x).hasDerivAt
      convert h.pow 2 using 1
      ring
    exact hd.deriv
  -- Cauchy–Schwarz on `(-∞, y]`
  have hCS : |∫ x in Set.Iic y, f x * deriv f x| ≤
      Real.sqrt (∫ x in Set.Iic y, (f x) ^ 2) *
        Real.sqrt (∫ x in Set.Iic y, (deriv f x) ^ 2) := by
    have hmem_f : MemLp f 2 (volume.restrict (Set.Iic y)) :=
      (hf.continuous.memLp_of_hasCompactSupport hc).restrict _
    have hmem_d : MemLp (deriv f) 2 (volume.restrict (Set.Iic y)) :=
      ((hf.continuous_deriv le_rfl).memLp_of_hasCompactSupport hc.deriv).restrict _
    have hCS := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict (Set.Iic y))
        (p := 2) (q := 2) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
        (by simpa using hmem_f) (by simpa using hmem_d)
    have h1 : |∫ x in Set.Iic y, f x * deriv f x| ≤
        ∫ x, ‖f x‖ * ‖deriv f x‖ ∂(volume.restrict (Set.Iic y)) := by
      have hEq : (∫ x, |f x * deriv f x| ∂(volume.restrict (Set.Iic y)))
          = ∫ x, ‖f x‖ * ‖deriv f x‖ ∂(volume.restrict (Set.Iic y)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          simp only [Real.norm_eq_abs, abs_mul])
      rw [← hEq]
      exact MeasureTheory.abs_integral_le_integral_abs
    have hpowf : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume.restrict (Set.Iic y))) =
        ∫ x in Set.Iic y, (f x) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs])
    have hpowd : (∫ x, ‖deriv f x‖ ^ (2 : ℝ) ∂(volume.restrict (Set.Iic y))) =
        ∫ x in Set.Iic y, (deriv f x) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs])
    calc |∫ x in Set.Iic y, f x * deriv f x|
        ≤ ∫ x, ‖f x‖ * ‖deriv f x‖ ∂(volume.restrict (Set.Iic y)) := h1
      _ ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume.restrict (Set.Iic y))) ^ (1 / 2) *
            (∫ x, ‖deriv f x‖ ^ (2 : ℝ) ∂(volume.restrict (Set.Iic y))) ^ (1 / 2) := hCS
      _ = Real.sqrt (∫ x in Set.Iic y, (f x) ^ 2) *
            Real.sqrt (∫ x in Set.Iic y, (deriv f x) ^ 2) := by
          rw [hpowf, hpowd, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  -- monotonicity of the set integrals (the integrands are nonnegative and integrable)
  have hmono_f : (∫ x in Set.Iic y, (f x) ^ 2) ≤ ∫ x : ℝ, (f x) ^ 2 := by
    refine MeasureTheory.setIntegral_le_integral ?_ ?_
    · exact (hf.continuous.pow 2).integrable_of_hasCompactSupport hsq_supp
    · filter_upwards with x
      positivity
  have hmono_d : (∫ x in Set.Iic y, (deriv f x) ^ 2) ≤ ∫ x : ℝ, (deriv f x) ^ 2 := by
    refine MeasureTheory.setIntegral_le_integral ?_ ?_
    · exact ((hf.continuous_deriv le_rfl).pow 2).integrable_of_hasCompactSupport hdsq_supp
    · filter_upwards with x
      positivity
  -- pull the constant `2` out of the integral
  have hfac : (∫ x in Set.Iic y, 2 * f x * deriv f x) =
      2 * ∫ x in Set.Iic y, f x * deriv f x := by
    have hfun : (fun x => 2 * f x * deriv f x) = fun x => 2 * (f x * deriv f x) := by
      funext x; ring
    rw [hfun, MeasureTheory.integral_const_mul]
  calc (f y) ^ 2 = ∫ x in Set.Iic y, 2 * f x * deriv f x := hFTC
    _ = 2 * ∫ x in Set.Iic y, f x * deriv f x := hfac
    _ ≤ |2 * ∫ x in Set.Iic y, f x * deriv f x| := le_abs_self _
    _ = 2 * |∫ x in Set.Iic y, f x * deriv f x| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * (Real.sqrt (∫ x in Set.Iic y, (f x) ^ 2) *
          Real.sqrt (∫ x in Set.Iic y, (deriv f x) ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS (by norm_num)
    _ ≤ 2 * (Real.sqrt (∫ x : ℝ, (f x) ^ 2) * Real.sqrt (∫ x : ℝ, (deriv f x) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt hmono_f)
          (Real.sqrt_le_sqrt hmono_d) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by norm_num)
    _ = 2 * Real.sqrt (∫ x : ℝ, (f x) ^ 2) * Real.sqrt (∫ x : ℝ, (deriv f x) ^ 2) := by ring

end Work.FTS.StrongLWP.Sobolev.HolderHalf
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.segment_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

/-- Fundamental theorem of calculus along the segment from `p` to `z` in `ℝ × ℝ`:
for a `C¹` function `v`, the total increment equals the integral of the directional
derivative along the segment. -/
theorem segment_integral {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (p z : ℝ × ℝ) :
    v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p) := by
  have hd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => v (p + t • (z - p)))
        ((fderiv ℝ v (p + t • (z - p))) (z - p)) t := by
    intro t _
    have hcur : HasDerivAt (fun t : ℝ => p + t • (z - p)) (z - p) t := by
      have h1 := (hasDerivAt_id t).smul_const (z - p)
      have h2 := h1.const_add p
      simpa using h2
    exact (hd.differentiableAt.hasFDerivAt).comp_hasDerivAt t hcur
  have hint : IntervalIntegrable (fun t : ℝ => (fderiv ℝ v (p + t • (z - p))) (z - p))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hcont := hv.continuous_fderiv_apply (by norm_num)
    exact hcont.comp
      ((continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  simp

end Work.FTS.StrongLWP.Sobolev.HolderHalf
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.vol_ball_prod =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

/-- The ball in `ℝ × ℝ` (with the product, i.e. sup, norm) is a square, so its Lebesgue volume
is `4 r ^ 2` (as an `ℝ≥0∞`). -/
theorem vol_ball_prod (x : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (4 * r ^ 2) := by
  -- In the product (sup) metric the ball is the square product of the two balls.
  have hball : Metric.ball x r = Metric.ball x.1 r ×ˢ Metric.ball x.2 r := by
    ext y
    simp only [Metric.mem_ball, Set.mem_prod, Prod.dist_eq, max_lt_iff]
  -- The volume on a product is the product of the volumes, and `volume (ball a r) = 2 r` on `ℝ`.
  rw [hball, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    Real.volume_ball, Real.volume_ball,
    ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 2 * r)]
  congr 1
  ring

end Work.FTS.StrongLWP.Sobolev.HolderHalf
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.contDiffOn_four_of_partial_tower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.StrongLWP.Sobolev

/-!
# `C⁴` from a continuous partial-derivative tower on an open subset of `ℝ²`

The main result below, `contDiffOn_four_of_partial_tower`, shows that a function
`F = Function.uncurry φ : ℝ × ℝ → ℝ` is `C⁴` on an open set `U` as soon as there is a
"partial derivative tower" `D : ℕ → ℕ → ℝ → ℝ → ℝ` with

* `D 0 0 = φ`,
* every `D a b` with `a + b ≤ 4` is continuous on `U`,
* the two one-variable slices of `D a b` have one-sided (in fact two-sided) derivatives
  `D (a+1) b` resp. `D a (b+1)` on `U`, for `a + b ≤ 3`.

The proof is an induction on the order `n ∈ {0,1,2,3,4}` of the statement
`main n` ("a continuous tower up to order `n` and slice derivatives up to order `n-1`
give `ContDiffOn ℝ n`").  The induction step needs the classical fact that a function on
an open subset of `ℝ × ℝ` whose two slice derivatives exist everywhere and are
continuous is (strictly) Fréchet differentiable with derivative given by the two slices —
Mathlib's `hasStrictFDerivAt_uncurry_coprod` — together with the observation that the
Fréchet derivative function `fderivWithin ℝ F U`, written in terms of the two slice
derivatives, is `Cⁿ` as soon as the two slice derivatives are (closure of `ContDiffOn`
under postcomposition with the continuous linear map `(x,y) ↦ x ⊗ fst + y ⊗ snd`).
-/

/-- The continuous linear map `ℝ × ℝ →L[ℝ] ℝ` which is the Fréchet derivative of a
function with slice derivatives `x` (in the first variable) and `y` (in the second). -/
private noncomputable def cop (x y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ x).coprod (ContinuousLinearMap.toSpanSingleton ℝ y)

/-- `p ↦ cop (a p) (b p)` is `Cⁿ` on `U` when `a` and `b` are.  This is the closure step
that makes the induction below possible: the Fréchet derivative function of a function with
continuous slice derivatives is built from those slice derivatives by a fixed continuous
linear operation. -/
private lemma cop_pair_eq {n : WithTop ℕ∞} {U : Set (ℝ × ℝ)} {a b : ℝ × ℝ → ℝ}
    (ha : ContDiffOn ℝ n a U) (hb : ContDiffOn ℝ n b U) :
    ContDiffOn ℝ n (fun p => cop (a p) (b p)) U := by
  have heq : (fun q : ℝ × ℝ => cop q.1 q.2)
      = fun q : ℝ × ℝ =>
        q.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + q.2 • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    funext q
    apply ContinuousLinearMap.ext
    intro v
    rw [show cop q.1 q.2 v = v.1 * q.1 + v.2 * q.2 from by
      simp [cop, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul]]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [show (ContinuousLinearMap.fst ℝ ℝ ℝ) v = v.1 from rfl,
        show (ContinuousLinearMap.snd ℝ ℝ ℝ) v = v.2 from rfl]
    ring
  have hc : ContDiff ℝ n (fun q : ℝ × ℝ => cop q.1 q.2) := by
    rw [heq]
    exact ((contDiff_fst (𝕜 := ℝ)).smul_const _).add ((contDiff_snd (𝕜 := ℝ)).smul_const _)
  have h := hc.comp_contDiffOn (ha.prodMk hb)
  simpa [Function.comp_def] using h

/-- The map `c ↦ x ↦ x • c` is continuous. -/
private lemma continuous_toSpanSingleton :
    Continuous (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c : ℝ → (ℝ →L[ℝ] ℝ)) := by
  have h : (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c : ℝ → (ℝ →L[ℝ] ℝ))
      = ⇑(ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)) := by
    funext c
    simp [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  rw [h]
  exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous

/-- **Slice derivatives give the Fréchet derivative.**  If the two one-variable slices of
`φ` have derivative `a z θ` resp. `b z θ` at every point of the open set `U`, and these slice
derivative functions are continuous on `U`, then `Function.uncurry φ` is differentiable on
`U`, with `fderivWithin ℝ (Function.uncurry φ) U p = cop (a p.1 p.2) (b p.1 p.2)`. -/
private lemma differentiableOn_uncurry_of_slices {φ : ℝ → ℝ → ℝ} {a b : ℝ → ℝ → ℝ}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (ha : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun z' => φ z' θ) (a z θ) z)
    (hb : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun θ' => φ z θ') (b z θ) θ)
    (hca : ContinuousOn (Function.uncurry a) U) (hcb : ContinuousOn (Function.uncurry b) U) :
    DifferentiableOn ℝ (Function.uncurry φ) U ∧
      Set.EqOn (fderivWithin ℝ (Function.uncurry φ) U)
        (fun p => cop (a p.1 p.2) (b p.1 p.2)) U := by
  have key : ∀ p ∈ U, HasFDerivAt (Function.uncurry φ) (cop (a p.1 p.2) (b p.1 p.2)) p := by
    intro p hp
    have hmem : U ∈ 𝓝 p := hU.mem_nhds hp
    have h1 : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun x => φ x v.2)
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (a z θ)) v) v.1 := by
      filter_upwards [hmem] with v hv
      exact (ha v.1 v.2 hv).hasFDerivAt
    have h2 : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun x => φ v.1 x)
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (b z θ)) v) v.2 := by
      filter_upwards [hmem] with v hv
      exact (hb v.1 v.2 hv).hasFDerivAt
    have c1 : ContinuousAt
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (a z θ))) p :=
      continuous_toSpanSingleton.continuousAt.comp (hca.continuousAt hmem)
    have c2 : ContinuousAt
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (b z θ))) p :=
      continuous_toSpanSingleton.continuousAt.comp (hcb.continuousAt hmem)
    have h := hasStrictFDerivAt_uncurry_coprod (u := p) (f := φ)
      (f₁ := fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (a z θ))
      (f₂ := fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (b z θ)) h1 h2 c1 c2
    exact h.hasFDerivAt
  constructor
  · intro p hp; exact (key p hp).differentiableAt.differentiableWithinAt
  · intro p hp
    exact ((key p hp).hasFDerivWithinAt).fderivWithin (hU.uniqueDiffOn p hp)

/-- **The induction.**  Given a partial-derivative tower continuous up to order `n` on the
open set `U`, whose slices are differentiable with the next tower entries as derivatives for
all `a + b < n`, the function `Function.uncurry φ` is `Cⁿ` on `U`. -/
private theorem main : ∀ n : ℕ, ∀ (φ : ℝ → ℝ → ℝ) (D : ℕ → ℕ → ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)),
    IsOpen U → (∀ z θ, φ z θ = D 0 0 z θ) →
    (∀ a b, a + b ≤ n → ContinuousOn (fun p : ℝ × ℝ => D a b p.1 p.2) U) →
    (∀ a b, a + b < n → ∀ z θ, (z, θ) ∈ U →
      HasDerivAt (fun z' => D a b z' θ) (D (a + 1) b z θ) z) →
    (∀ a b, a + b < n → ∀ z θ, (z, θ) ∈ U →
      HasDerivAt (fun θ' => D a b z θ') (D a (b + 1) z θ) θ) →
    ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry φ) U := by
  intro n
  induction n with
  | zero =>
      intro φ D U hU hφ hcont hsz hth
      have h : ContinuousOn (Function.uncurry φ) U :=
        (hcont 0 0 le_rfl).congr (fun p hp => hφ p.1 p.2)
      simpa [Nat.cast_zero] using (contDiffOn_zero (𝕜 := ℝ)).2 h
  | succ k ih =>
      intro φ D U hU hφ hcont hsz hth
      -- the two slice derivative functions `D 1 0` and `D 0 1` are `Cᵏ` by induction,
      -- applied to the shifted towers
      have hcontX : ContDiffOn ℝ k (Function.uncurry (D 1 0)) U :=
        ih (D 1 0) (fun i j => D (i + 1) j) U hU (fun z θ => rfl)
          (fun i j hij => hcont (i + 1) j (by omega))
          (fun i j hij z θ hz => hsz (i + 1) j (by omega) z θ hz)
          (fun i j hij z θ hz => hth (i + 1) j (by omega) z θ hz)
      have hcontY : ContDiffOn ℝ k (Function.uncurry (D 0 1)) U :=
        ih (D 0 1) (fun i j => D i (j + 1)) U hU (fun z θ => rfl)
          (fun i j hij => hcont i (j + 1) (by omega))
          (fun i j hij z θ hz => hsz i (j + 1) (by omega) z θ hz)
          (fun i j hij z θ hz => hth i (j + 1) (by omega) z θ hz)
      -- the slice derivatives of `φ` itself
      have hsz0 : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun z' => φ z' θ) (D 1 0 z θ) z := by
        intro z θ hz
        have hfs : (fun z' => φ z' θ) = fun z' => D 0 0 z' θ := funext fun z' => hφ z' θ
        rw [hfs]
        exact hsz 0 0 (by omega) z θ hz
      have hth0 : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun θ' => φ z θ') (D 0 1 z θ) θ := by
        intro z θ hz
        have hfs : (fun θ' => φ z θ') = fun θ' => D 0 0 z θ' := funext fun θ' => hφ z θ'
        rw [hfs]
        exact hth 0 0 (by omega) z θ hz
      have hP1 := differentiableOn_uncurry_of_slices hU hsz0 hth0
        (hcont 1 0 (by omega)) (hcont 0 1 (by omega))
      have hfderiv : ContDiffOn ℝ k (fderivWithin ℝ (Function.uncurry φ) U) U :=
        (cop_pair_eq (n := (k : WithTop ℕ∞))
          (a := Function.uncurry (D 1 0)) (b := Function.uncurry (D 0 1)) hcontX hcontY).congr
          (fun p hp => hP1.2 hp)
      have hsucc := contDiffOn_succ_of_fderivWithin hP1.1 (fun hω => absurd hω (by simp)) hfderiv
      simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hsucc

theorem contDiffOn_four_of_partial_tower {φ : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hφ : ∀ z θ, φ z θ = D 0 0 z θ)
    (hcont : ∀ a b : ℕ, a + b ≤ 4 → ContinuousOn (fun p : ℝ × ℝ => D a b p.1 p.2) U)
    (hsz : ∀ a b : ℕ, a + b ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ U →
      HasDerivAt (fun z' => D a b z' θ) (D (a + 1) b z θ) z)
    (hth : ∀ a b : ℕ, a + b ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ U →
      HasDerivAt (fun θ' => D a b z θ') (D a (b + 1) z θ) θ)
    : ContDiffOn ℝ 4 (Function.uncurry φ) U := by
  have h := main 4 φ D U hU hφ
    (fun a b hab => hcont a b hab)
    (fun a b hab => hsz a b (by omega))
    (fun a b hab => hth a b (by omega))
  simpa using h

end Work.FTS.StrongLWP.Sobolev
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.EndLimits.abs_sub_le_integral_abs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.EndLimits

theorem abs_sub_le_integral_abs {F F' : ℝ → ℝ} {a b θ₁ θ₂ : ℝ}
    (hderiv : ∀ θ ∈ Set.Ioo a b, HasDerivAt F (F' θ) θ)
    (hint : IntervalIntegrable F' MeasureTheory.volume a b)
    (ha : a < θ₁) (h₁ : θ₁ ≤ θ₂) (h₂ : θ₂ < b) :
    |F θ₂ - F θ₁| ≤ ∫ x in a..b, |F' x| := by
  have hab : a ≤ b := le_of_lt (lt_trans ha (lt_of_le_of_lt h₁ h₂))
  have hsub : Set.Icc θ₁ θ₂ ⊆ Set.Ioo a b := fun y hy =>
    ⟨lt_of_lt_of_le ha hy.1, lt_of_le_of_lt hy.2 h₂⟩
  have hcont : ContinuousOn F (Set.Icc θ₁ θ₂) := fun y hy =>
    (hderiv y (hsub hy)).continuousAt.continuousWithinAt
  have hInt : IntervalIntegrable F' MeasureTheory.volume θ₁ θ₂ :=
    hint.mono_set (by
      rw [Set.uIcc_of_le h₁, Set.uIcc_of_le hab]
      exact fun y hy => ⟨le_trans (le_of_lt ha) hy.1, le_trans hy.2 (le_of_lt h₂)⟩)
  have hftc : ∫ x in θ₁..θ₂, F' x = F θ₂ - F θ₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h₁ hcont
      (fun y hy => hderiv y (hsub ⟨le_of_lt hy.1, le_of_lt hy.2⟩)) hInt
  calc |F θ₂ - F θ₁| = |∫ x in θ₁..θ₂, F' x| := by rw [hftc]
    _ ≤ ∫ x in θ₁..θ₂, |F' x| := intervalIntegral.abs_integral_le_integral_abs h₁
    _ ≤ ∫ x in a..b, |F' x| :=
        intervalIntegral.integral_mono_interval (le_of_lt ha) h₁ (le_of_lt h₂)
          (Filter.Eventually.of_forall (fun x => abs_nonneg _)) hint.abs

end Work.FTS.StrongPersist.H6Aux.EndLimits
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.EndLimits.not_integrableOn_Ioo_div =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.EndLimits

open MeasureTheory Set

/-- For `c > 0` and `r > 0`, the function `θ ↦ c / θ` is not integrable on `(0, r)`:
the singularity at `θ = 0` is non-integrable (the primitive is `c · log θ → -∞`).
Equivalently, this is the borderline case `s = -1` of `integrableOn_Ioo_rpow_iff`: the
real power `θ ^ s` is integrable on `(0, r)` exactly for `-1 < s`. -/
theorem not_integrableOn_Ioo_div {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => c / θ) (Set.Ioo (0:ℝ) r) := by
  intro h
  -- multiplying by the nonzero constant `c⁻¹` reduces to the non-integrability of `θ⁻¹`
  have h2 : MeasureTheory.IntegrableOn (fun θ : ℝ => c⁻¹ * (c / θ)) (Set.Ioo (0:ℝ) r) :=
    h.const_mul c⁻¹
  have h3 : MeasureTheory.IntegrableOn (fun θ : ℝ => θ⁻¹) (Set.Ioo (0:ℝ) r) :=
    h2.congr_fun (fun θ _ => by
      show c⁻¹ * (c / θ) = θ⁻¹
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]) measurableSet_Ioo
  -- `θ⁻¹` is the real power `θ ^ (-1)`
  have h4 : MeasureTheory.IntegrableOn (fun θ : ℝ => θ ^ (-1 : ℝ)) (Set.Ioo (0:ℝ) r) :=
    h3.congr_fun (fun θ _ => by
      show θ⁻¹ = θ ^ (-1 : ℝ)
      rw [Real.rpow_neg_one]) measurableSet_Ioo
  -- whose integrability on `(0, r)` is equivalent to the false statement `-1 < -1`
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hr] at h4
  exact absurd h4 (lt_irrefl (-1))

end Work.FTS.StrongPersist.H6Aux.EndLimits
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.EndLimits.not_integrableOn_Ioo_div_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.EndLimits

theorem not_integrableOn_Ioo_div_sub {c L t : ℝ} (hc : 0 < c) (ht : t < L) :
    ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => c / (L - θ)) (Set.Ioo t L) := by
  intro h
  -- shrink the interval to `(m, L)` with `t < m < L` so that `L` is an interior endpoint
  obtain ⟨m, htm, hmL⟩ : ∃ m : ℝ, t < m ∧ m < L := ⟨(t + L) / 2, by linarith, by linarith⟩
  have h1 : MeasureTheory.IntegrableOn (fun θ : ℝ => c / (L - θ)) (Set.Ioo m L) :=
    h.mono_set (Set.Ioo_subset_Ioo_left htm.le)
  have hI : IntervalIntegrable (fun θ : ℝ => c / (L - θ)) MeasureTheory.volume m L :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hmL.le).mpr h1
  -- `c / (L - x) = -c * (x - L)⁻¹`, hence integrability of `(· - L)⁻¹` on `m..L`
  have hpt : ∀ x : ℝ, (-c⁻¹) * (c / (L - x)) = (x - L)⁻¹ := by
    intro x
    have hx : (x - L)⁻¹ = -((L - x)⁻¹) := by rw [← neg_sub x L, inv_neg, neg_neg]
    rw [hx, div_eq_mul_inv, neg_mul, inv_mul_cancel_left₀ (ne_of_gt hc)]
  have h2 : IntervalIntegrable (fun θ : ℝ => (θ - L)⁻¹) MeasureTheory.volume m L := by
    have h3 : IntervalIntegrable (fun θ : ℝ => (-c⁻¹) * (c / (L - θ))) MeasureTheory.volume m L :=
      hI.const_mul (-c⁻¹)
    exact h3.congr (fun x _ => hpt x)
  -- but `(· - L)⁻¹` is interval integrable on `m..L` only if `L ∉ [[m, L]]`
  rw [intervalIntegrable_sub_inv_iff] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 (ne_of_lt hmL)
  · exact h2 (by rw [Set.uIcc_of_le hmL.le]; exact ⟨hmL.le, le_rfl⟩)

end Work.FTS.StrongPersist.H6Aux.EndLimits
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.EndLimits.tendsto_intervalIntegral_abs_left =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.EndLimits

/-- The primitive `r ↦ ∫_0^r |f|` of an `L¹` function on `(0,L)` tends to `0` as `r → 0` from
the right.  This is the absolute continuity of the Lebesgue integral, in the form of the
continuity of the integral as a function of its upper endpoint together with the fact that
`Icc 0 L` is a neighbourhood of `0` inside `Ioi 0`. -/
theorem tendsto_intervalIntegral_abs_left {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioo (0:ℝ) L)) :
    Filter.Tendsto (fun r : ℝ => ∫ x in (0:ℝ)..r, |f x|)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  -- `|f|` is interval integrable on `0..L`, so its primitive is continuous there.
  have hInt : IntervalIntegrable (fun x : ℝ => |f x|) MeasureTheory.volume (0:ℝ) L :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt hL)).2 hf.abs
  have hprim : ContinuousWithinAt (fun r : ℝ => ∫ x in (0:ℝ)..r, |f x|)
      (Set.Icc (0:ℝ) L) (0:ℝ) :=
    intervalIntegral.continuousWithinAt_primitive (MeasureTheory.measure_singleton 0)
      (by simpa [max_eq_right (le_of_lt hL)] using hInt)
  -- `Icc 0 L` is a neighbourhood of `0` relative to `Ioi 0`.
  have hsub : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhdsWithin (0:ℝ) (Set.Icc (0:ℝ) L) := by
    rw [nhdsWithin_le_iff, mem_nhdsWithin]
    exact ⟨Set.Iio L, isOpen_Iio, hL, fun x hx => ⟨le_of_lt hx.2, le_of_lt hx.1⟩⟩
  simpa using hprim.mono_left hsub

end Work.FTS.StrongPersist.H6Aux.EndLimits
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.EndLimits.tendsto_intervalIntegral_abs_right =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.EndLimits

/-- The absolute continuity of the integral: as `t → L⁻` the integral of `|f|` over `(t, L)`
tends to zero, for `f` integrable on `(0, L)`. -/
theorem tendsto_intervalIntegral_abs_right {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioo (0:ℝ) L)) :
    Filter.Tendsto (fun t : ℝ => ∫ x in t..L, |f x|)
      (nhdsWithin L (Set.Iio L)) (nhds 0) := by
  -- extend `|f|` to a globally integrable function `F` by killing it off `(0, L)`
  set F : ℝ → ℝ := (Set.Ioo (0:ℝ) L).indicator (fun x => |f x|) with hFdef
  have hFint : MeasureTheory.Integrable F := by
    rw [hFdef]
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mpr hf.abs
  -- the measure of `(t, L)` tends to `0` as `t → L⁻`
  have hmeas : Filter.Tendsto (fun t : ℝ => MeasureTheory.volume (Set.Ioc t L))
      (nhdsWithin L (Set.Iio L)) (nhds 0) := by
    have hfun : (fun t : ℝ => MeasureTheory.volume (Set.Ioc t L)) =
        fun t : ℝ => ENNReal.ofReal (L - t) := by
      funext t
      rw [Real.volume_Ioc]
    rw [hfun]
    have hcont : Filter.Tendsto (fun t : ℝ => L - t) (nhdsWithin L (Set.Iio L))
        (nhds (L - L)) :=
      tendsto_nhdsWithin_of_tendsto_nhds
        (tendsto_const_nhds.sub Filter.tendsto_id)
    have h := ENNReal.tendsto_ofReal hcont
    simpa using h
  -- absolute continuity of the integral
  have hmain : Filter.Tendsto (fun t : ℝ => ∫ x in Set.Ioc t L, F x)
      (nhdsWithin L (Set.Iio L)) (nhds 0) :=
    hFint.tendsto_setIntegral_nhds_zero (s := fun t : ℝ => Set.Ioc t L) hmeas
  -- identify the two functions eventually (for `t` close to `L`, hence `t ∈ (0, L)`)
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds
      (Filter.eventually_iff.mpr (IsOpen.mem_nhds isOpen_Ioi hL))] with t ht hpos
  have h1 : (∫ x in t..L, |f x|) = ∫ x in Set.Ioo t L, |f x| := by
    rw [intervalIntegral.integral_of_le ht.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo, h1]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x hx => by
    simp only [hFdef,
      Set.indicator_of_mem (show x ∈ Set.Ioo (0:ℝ) L from ⟨lt_trans hpos hx.1, hx.2⟩)])

end Work.FTS.StrongPersist.H6Aux.EndLimits
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.IbpInnerDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.R

/-- On `(0, π/2)` one has `sin (2θ) · (sin (2θ)^{-q} · H(θ)²) = sin (2θ)^{1-q} · H(θ)²`, and the
θ-derivative of the latter is
`(1-q)·2cos(2θ)·sin(2θ)^{-q}·H² + 2·sin(2θ)^{1-q}·H·H'`
`= 2·sin(2θ)·H'·H·sin(2θ)^{-q} - 2(q-1)·cos(2θ)·sin(2θ)^{-q}·H²`.

This is the derivative of the integrand of the "inner" integration by parts
(`H6Aux.slice_ibp_base`). -/
theorem IbpInnerDeriv {q : ℝ} {H : ℝ → ℝ}
    (hH : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt H (deriv H θ) θ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' => Real.sin (2 * θ') * ((Real.sin (2 * θ')) ^ (-q) * (H θ') ^ 2))
        (2 * (Real.sin (2 * θ) * deriv H θ * H θ * (Real.sin (2 * θ)) ^ (-q))
          - 2 * (q - 1) * (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * (H θ) ^ 2)) θ := by
  intro θ hθ
  -- on the open interval, `sin (2θ) > 0`, so the `rpow`s behave algebraically
  have hs0 : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hθ.1]
    · linarith [hθ.2]
  -- the chain rule for `θ' ↦ sin (2θ')`
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := h2.sin
  -- and for its `(-q)`-th power
  have hpow : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ') ^ (-q))
      ((Real.cos (2 * θ) * 2) * (-q) * Real.sin (2 * θ) ^ (-q - 1)) θ := by
    have h := hsin.rpow_const (p := -q) (Or.inl (ne_of_gt hs0))
    simpa using h
  -- the second factor `H²`
  have hsq : HasDerivAt (H ^ 2) (2 * H θ * deriv H θ) θ := by
    have h := (hH θ hθ).pow 2
    simpa using h
  -- product rule
  have hprod := hsin.mul (hpow.mul hsq)
  -- put the pointwise product of functions into the product-rule shape
  have hfun : (fun θ' : ℝ => Real.sin (2 * θ') *
      (Real.sin (2 * θ') ^ (-q) * (H θ') ^ 2))
      = (fun θ' : ℝ => Real.sin (2 * θ')) *
        ((fun θ' : ℝ => Real.sin (2 * θ') ^ (-q)) * (H ^ 2)) := by
    funext θ'
    simp [Pi.mul_apply, Pi.pow_apply]
  rw [hfun]
  refine hprod.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply]
  -- abbreviate `s = sin (2θ) > 0`; the only `rpow` identity needed is `s * s^{-q-1} = s^{-q}`
  set s := Real.sin (2 * θ) with hsdef
  have hs : 0 < s := hs0
  have hrpow : s * s ^ (-1 - q) = s ^ (-q) := by
    rw [show (-1 - q : ℝ) = -q - 1 by ring, Real.rpow_sub hs (-q) 1, Real.rpow_one,
      ← mul_div_assoc]
    exact mul_div_cancel_left₀ _ (ne_of_gt hs)
  have hrpow_gen : ∀ a : ℝ, a * s * s ^ (-1 - q) = a * s ^ (-q) := by
    intro a
    rw [mul_assoc, hrpow]
  ring_nf
  rw [hrpow_gen]
  ring

end Work.FTS.StrongPersist.H6Aux.R
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.tendstoGT_of_hasDerivAt_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.StrongPersist.H6Aux.R

/-- **Right-hand limit of a primitive.**  If `F` has derivative `v'` on `(0, c)`, `v'` is
interval integrable on `(0, c)` and `F` is continuous at `c`, then `F` has a right limit at
`0⁺`, given by `F c - ∫_0^c v'`.

Indeed, for `x ∈ (0, c)` the fundamental theorem of calculus on `[x, c]` gives
`F x = F c - ∫_x^c v'`, and `x ↦ ∫_x^c v'` is continuous on `[0, c]` (continuity of the
primitive of an interval integrable function), so it tends to `∫_0^c v'` as `x → 0⁺`. -/
theorem tendstoGT_of_hasDerivAt_integrableOn {F v' : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) c, HasDerivAt F (v' x) x)
    (hcont : ContinuousAt F c)
    (hint : IntervalIntegrable v' MeasureTheory.volume (0 : ℝ) c) :
    Filter.Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (F c - ∫ x in (0 : ℝ)..c, v' x)) := by
  -- `v'` is integrable on the *closed* interval `[0, c]`, hence the primitive `∫_x^c v'`
  -- is continuous on `[0, c]`.
  have hintIcc : IntegrableOn v' (uIcc (0 : ℝ) c) volume :=
    (intervalIntegrable_iff' (f := v') (a := (0 : ℝ)) (b := c)).mp hint
  have hpri : ContinuousOn (fun x => ∫ t in x..c, v' t) (uIcc (0 : ℝ) c) :=
    intervalIntegral.continuousOn_primitive_interval_left hintIcc
  -- hence `∫_x^c v' → ∫_0^c v'` as `x → 0⁺`, because `[0, c]` is a neighbourhood of `0`
  -- within `Ioi 0`.
  have hprim : Tendsto (fun x => ∫ t in x..c, v' t) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ t in (0 : ℝ)..c, v' t)) := by
    have hmem : uIcc (0 : ℝ) c ∈ 𝓝[>] (0 : ℝ) := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Set.Iio c, Iio_mem_nhds hc, ?_⟩
      rintro x ⟨hxc, hx0⟩
      exact ⟨le_trans (min_le_left _ _) hx0.le, le_trans hxc.le (le_max_right _ _)⟩
    refine ((hpri.continuousWithinAt (left_mem_uIcc (a := (0 : ℝ)) (b := c))).tendsto).mono_left ?_
    exact nhdsWithin_le_iff.mpr hmem
  -- For `x ∈ (0, c)`, the FTC on `[x, c]` identifies `F x` with `F c - ∫_x^c v'`.
  have hF : (fun x => F c - ∫ t in x..c, v' t) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] F := by
    filter_upwards [Ioo_mem_nhdsGT hc] with x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hxc : x < c := hx.2
    have hint' : IntervalIntegrable v' volume x c := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxc.le]
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le).mp hint).mono_set
        (Ioc_subset_Ioc hx0.le le_rfl)
    have ha : Tendsto F (𝓝[>] x) (𝓝 (F x)) :=
      ((hderiv x ⟨hx0, hxc⟩).continuousAt.tendsto).mono_left inf_le_left
    have hb : Tendsto F (𝓝[<] c) (𝓝 (F c)) := hcont.tendsto.mono_left inf_le_left
    have hEq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hxc
      (fun z hz => hderiv z ⟨hx0.trans hz.1, hz.2⟩) hint' ha hb
    linarith
  exact Filter.Tendsto.congr' hF (tendsto_const_nhds.sub hprim)

end Work.FTS.StrongPersist.H6Aux.R
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.tendstoLT_of_hasDerivAt_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.R

open MeasureTheory Set Filter
open scoped Topology

/-- If `F` has derivative `v'` on the open interval `(a, b)`, is continuous at `a`, and `v'` is
interval integrable on `a..b`, then `F` has the left limit `F a + ∫ x in a..b, v' x` at `b`.

This is the "indefinite integral is continuous" form of the fundamental theorem of calculus: for
`x ∈ (a, b)` the (second) FTC gives `F x = F a + ∫ y in a..x, v' y`, and `x ↦ ∫ y in a..x, v' y`
is absolutely continuous (hence continuous) on `[a, b]`, so it tends at `b⁻` to
`∫ y in a..b, v' y`. -/
theorem tendstoLT_of_hasDerivAt_integrableOn {F v' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt F (v' x) x)
    (hcont : ContinuousAt F a)
    (hint : IntervalIntegrable v' MeasureTheory.volume a b) :
    Filter.Tendsto F (nhdsWithin b (Set.Iio b))
      (nhds (F a + ∫ x in a..b, v' x)) := by
  -- The second fundamental theorem of calculus on each closed subinterval `[a, x]`, `x < b`.
  have hFTC : ∀ x ∈ Ioo a b, F x = F a + ∫ y in a..x, v' y := by
    intro x hx
    have hcont' : ContinuousOn F (Icc a x) := by
      intro y hy
      rcases eq_or_lt_of_le hy.1 with hya | hya
      · subst hya; exact hcont.continuousWithinAt
      · exact ((hderiv y ⟨hya, lt_of_le_of_lt hy.2 hx.2⟩).continuousAt).continuousWithinAt
    have hderiv' : ∀ y ∈ Ioo a x, HasDerivAt F (v' y) y :=
      fun y hy => hderiv y ⟨hy.1, lt_trans hy.2 hx.2⟩
    have hint' : IntervalIntegrable v' volume a x :=
      hint.mono_set (by
        rw [uIcc_of_le hx.1.le, uIcc_of_le hab.le]
        exact Icc_subset_Icc_right hx.2.le)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1.le hcont' hderiv' hint']
    ring
  -- The indefinite integral `x ↦ ∫ y in a..x, v' y` is continuous at `b`.
  have hAC : AbsolutelyContinuousOnInterval (fun x => ∫ y in a..x, v' y) a b :=
    hint.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by
      rw [uIcc_of_le hab.le]; exact ⟨le_rfl, hab.le⟩)
  have hg : Tendsto (fun x => ∫ y in a..x, v' y) (𝓝[Iio b] b) (𝓝 (∫ y in a..b, v' y)) := by
    have hcw : ContinuousWithinAt (fun x => ∫ y in a..x, v' y) (Icc a b) b := by
      have h := hAC.continuousOn
      rw [uIcc_of_le hab.le] at h
      exact h b ⟨hab.le, le_rfl⟩
    refine hcw.mono_left ?_
    rw [nhdsWithin_le_iff]
    refine mem_of_superset (inter_mem_nhdsWithin (Iio b) (Ici_mem_nhds hab)) ?_
    intro x hx
    exact ⟨hx.2, hx.1.le⟩
  -- Replace `F a + ∫ y in a..x, v' y` by `F x` eventually (`x > a`).
  refine Tendsto.congr' ?_ (hg.const_add (F a))
  filter_upwards [show Ioo a b ∈ 𝓝[Iio b] b from
      mem_of_superset (inter_mem_nhdsWithin (Iio b) (Ioi_mem_nhds hab))
        (fun x hx => ⟨hx.2, hx.1⟩)] with x hx
  exact (hFTC x hx).symm

end Work.FTS.StrongPersist.H6Aux.R
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.hasDerivAt_ibpPrim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

theorem hasDerivAt_ibpPrim {q : ℝ} {H : ℝ → ℝ}
    (hH : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt H (deriv H θ) θ) :
    ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      HasDerivAt (fun θ' => Real.sin (2*θ') * ((Real.sin (2*θ'))^(-q) * (H θ')^2))
        (2 * (Real.sin (2*θ) * deriv H θ * H θ * (Real.sin (2*θ))^(-q))
          - 2*(q-1) * (Real.cos (2*θ) * (Real.sin (2*θ))^(-q) * (H θ)^2)) θ := by
  intro θ hθ
  -- on the open interval `sin (2θ) > 0`
  have hs0 : 0 < Real.sin (2*θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hθ.1]
    · linarith [hθ.2]
  -- the inner chain rule for `θ' ↦ sin (2θ')`
  have h2 : HasDerivAt (fun θ' : ℝ => 2*θ') (2:ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ')) (Real.cos (2*θ) * 2) θ := h2.sin
  -- and the real power of it
  have hpow : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ') ^ (-q))
      ((Real.cos (2*θ) * 2) * (-q) * Real.sin (2*θ) ^ (-q - 1)) θ := by
    have h := hsin.rpow_const (p := -q) (Or.inl (ne_of_gt hs0))
    simpa using h
  have hsq : HasDerivAt (H ^ 2) (2 * H θ * deriv H θ) θ := by
    have h := (hH θ hθ).pow 2
    simpa using h
  have hprod := hsin.mul (hpow.mul hsq)
  -- rewrite the pointwise product of functions into the product-rule shape
  have hfun : (fun θ' : ℝ => Real.sin (2*θ') *
      (Real.sin (2*θ') ^ (-q) * (H θ')^2))
      = (fun θ' : ℝ => Real.sin (2*θ')) * ((fun θ' : ℝ => Real.sin (2*θ') ^ (-q)) * (H ^ 2)) := by
    funext θ'; simp [Pi.mul_apply, Pi.pow_apply]
  rw [hfun]
  refine hprod.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply]
  -- abbreviate `s = sin (2θ) > 0`; the only `rpow` fact needed is `s * s^{-q-1} = s^{-q}`
  set s := Real.sin (2*θ) with hsdef
  have hs : 0 < s := hs0
  have hrpow : s * s ^ (-1 - q) = s ^ (-q) := by
    rw [show (-1 - q : ℝ) = -q - 1 by ring, Real.rpow_sub hs (-q) 1, Real.rpow_one,
      ← mul_div_assoc]
    exact mul_div_cancel_left₀ _ (ne_of_gt hs)
  have hrpow_gen : ∀ a : ℝ, a * s * s ^ (-1 - q) = a * s ^ (-q) := by
    intro a; rw [mul_assoc, hrpow]
  ring_nf
  rw [hrpow_gen]
  ring

end Work.FTS.StrongPersist.H6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.Rl0Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false

/-- The `ℋ⁴`-coefficient of the pointwise bound for `N₀`: it prices the terms of `N₀` which are
dominated slot by slot by the `ℋ⁴`-integrand of `g` (the two `L₁₂(g)`-terms and the
`L₁₂(F_*)`-term, together with the `(1/α)L₁₂(g)g`-term). -/
def A₀ (α X : ℝ) : ℝ := 9 * X ^ 2 / α ^ 2 + 81 * X ^ 2 / (4 * α ^ 2) + 36 * X ^ 2 + 16 * α ^ 2

/-- The radial coefficient of the pointwise bound for `N₀`: it prices the terms whose `z`-dependence
is exactly `z/(1+z)²` (the `F_*`-terms and the collapse `N₀₁ + N₀₂ = 8α²c2m z²Γ/(c(1+z)⁴)`), so
that after multiplication by the Hardy weight `w` they contribute the integrable profile
`(1/(1+r))²`. -/
def B₀ (α X : ℝ) : ℝ := (160 * α ^ 2) ^ 2 + (180 * α * X) ^ 2 + (240 * α * X) ^ 2

theorem A₀_nonneg (α X : ℝ) : 0 ≤ A₀ α X := by
  have h1 : (0 : ℝ) ≤ 9 * X ^ 2 / α ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg X)) (sq_nonneg α)
  have h2 : (0 : ℝ) ≤ 81 * X ^ 2 / (4 * α ^ 2) :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg X)) (by positivity)
  have h3 : (0 : ℝ) ≤ 36 * X ^ 2 := mul_nonneg (by norm_num) (sq_nonneg X)
  have h4 : (0 : ℝ) ≤ 16 * α ^ 2 := mul_nonneg (by norm_num) (sq_nonneg α)
  rw [A₀]
  linarith

theorem B₀_nonneg (α X : ℝ) : 0 ≤ B₀ α X := by
  rw [B₀]
  nlinarith [sq_nonneg (160 * α ^ 2), sq_nonneg (180 * α * X), sq_nonneg (240 * α * X)]

/-- The crude upper bound for `A₀` used in the final arithmetic: with `α ≤ 1` one has
`9 + 81/4 + 36 = 261/4 ≤ 90` after pushing the `36 X²` term into `X²/α²`. -/
theorem A₀_le {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    A₀ α X ≤ 90 * X ^ 2 / α ^ 2 + 16 * α ^ 2 := by
  have h4 : (0 : ℝ) < 4 * α ^ 2 := by positivity
  have hα2le : α ^ 2 ≤ 1 := by nlinarith
  have hprod : α ^ 2 * X ^ 2 ≤ X ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right hα2le (sq_nonneg X)
  have hcross : A₀ α X * (4 * α ^ 2) ≤ (90 * X ^ 2 / α ^ 2 + 16 * α ^ 2) * (4 * α ^ 2) := by
    have e1 : A₀ α X * (4 * α ^ 2) = 36 * X ^ 2 + 81 * X ^ 2 + 144 * α ^ 2 * X ^ 2
        + 64 * α ^ 4 := by
      rw [A₀]; field_simp; ring
    have e2 : (90 * X ^ 2 / α ^ 2 + 16 * α ^ 2) * (4 * α ^ 2) = 360 * X ^ 2 + 64 * α ^ 4 := by
      field_simp; ring
    rw [e1, e2]
    nlinarith [hprod]
  exact le_of_mul_le_mul_right hcross h4

/-- The exact value of the `B₀`-constants: `180² + 240² = 90000`. -/
theorem B₀_le (α X : ℝ) : B₀ α X ≤ 25600 * α ^ 4 + 90000 * α ^ 2 * X ^ 2 := by
  rw [B₀]
  have h1 : (160 * α ^ 2) ^ 2 = 25600 * α ^ 4 := by ring
  have h2 : (180 * α * X) ^ 2 + (240 * α * X) ^ 2 = 90000 * α ^ 2 * X ^ 2 := by ring
  linarith

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAssem =====
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
set_option linter.unusedVariables false

/-- `X ≤ (1+X)⁴` for `X ≥ 0`. -/
theorem pow_le_one_add_four {x : ℝ} (hx : 0 ≤ x) : x ≤ (1 + x) ^ 4 := by
  have hx1 : (1 : ℝ) ≤ 1 + x := by linarith
  calc x ≤ 1 + x := by linarith
    _ = (1 + x) ^ 1 := by ring
    _ ≤ (1 + x) ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)

/-- `X²Y ≤ (1+X)⁴(1+Y²)` for `X, Y ≥ 0`. -/
theorem sq_mul_le_one_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 2 * y ≤ (1 + x) ^ 4 * (1 + y ^ 2) := by
  have hx1 : (1 : ℝ) ≤ 1 + x := by linarith
  have h2 : x ^ 2 ≤ (1 + x) ^ 4 := by
    have h3 : x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
    exact le_trans h3 (pow_le_pow_right₀ hx1 (by norm_num))
  have hP : 0 ≤ (1 + x) ^ 4 := pow_nonneg (by linarith) 4
  have hP1 : (1 : ℝ) ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  by_cases hyl : y ≤ 1
  · have h5 : x ^ 2 * y ≤ x ^ 2 := by nlinarith [sq_nonneg x, hyl]
    calc x ^ 2 * y ≤ x ^ 2 := h5
      _ ≤ (1 + x) ^ 4 := h2
      _ ≤ (1 + x) ^ 4 * (1 + y ^ 2) := le_mul_of_one_le_right hP hP1
  · have hy1 : 1 ≤ y := by linarith
    have h5 : x ^ 2 * y ≤ x ^ 2 * (y * y) := by
      have hyy : y ≤ y * y := by nlinarith [hy, hy1]
      exact mul_le_mul_of_nonneg_left hyy (sq_nonneg x)
    calc x ^ 2 * y ≤ x ^ 2 * (y * y) := h5
      _ = x ^ 2 * y ^ 2 := by ring
      _ ≤ (1 + x) ^ 4 * y ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg y)
      _ ≤ (1 + x) ^ 4 * (1 + y ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hP

/-- `X·Y² ≤ (1+X)⁴(1+Y²)` for `X, Y ≥ 0`. -/
theorem mul_sq_le_one_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y ^ 2 ≤ (1 + x) ^ 4 * (1 + y ^ 2) := by
  have h1 := pow_le_one_add_four hx
  have hP : 0 ≤ (1 + x) ^ 4 := pow_nonneg (by linarith) 4
  calc x * y ^ 2 ≤ (1 + x) ^ 4 * y ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg y)
    _ ≤ (1 + x) ^ 4 * (1 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith [sq_nonneg y]) hP

/-- **The sum of the per-term bounds.** -/
theorem t5bSumBound {C0 Cc C4 C6 X Y : ℝ} (hC0 : 0 ≤ C0) (hCc : 0 ≤ Cc) (hC4 : 0 ≤ C4)
    (hC6 : 0 ≤ C6) (hX : 0 ≤ X) (hY : 0 ≤ Y) {a b : ℕ} (hab : a + b ≤ 6) :
    (∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
      (if k = 0 ∧ i = 0 then C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
       else 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)))))
      ≤ 49 * (C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
          + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)))) := by
  have hB : 0 ≤ Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)) := by positivity
  have hA : 0 ≤ C0 * (1 + X) ^ 4 * (1 + Y ^ 2) := by positivity
  have hM : (0 : ℝ) ≤ 4096 * 4096 := by norm_num
  have hstep : ∀ k ∈ Finset.range (b + 1), ∀ i ∈ Finset.range (a + 1),
      (if k = 0 ∧ i = 0 then C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
       else 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))))
      ≤ C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
        + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))) := by
    intro k hk i hi
    by_cases h00 : k = 0 ∧ i = 0
    · rw [if_pos h00]; linarith
    · rw [if_neg h00]; linarith
  refine le_trans (Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun i hi =>
    hstep k hk i hi) ?_
  have hconst : (∑ k ∈ Finset.range (b + 1), ∑ _i ∈ Finset.range (a + 1),
        (C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
          + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)))))
      = (((b + 1) * (a + 1) : ℕ) : ℝ)
        * (C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
          + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)))) := by
    rw [Finset.sum_const, Finset.sum_const]
    simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_mul]
    ring
  rw [hconst]
  have hcard : (((b + 1) * (a + 1) : ℕ) : ℝ) ≤ 49 := by
    have hb : b ≤ 6 := by omega
    have ha : a ≤ 6 := by omega
    have h1 : (b + 1) * (a + 1) ≤ 49 := by nlinarith
    exact_mod_cast h1
  have hnn : 0 ≤ C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
      + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))) := by
    linarith
  exact mul_le_mul_of_nonneg_right hcard hnn

/-- **The final arithmetic of the row.** -/
theorem t5bFinalArith {C0 Cc C4 C6 X Y α : ℝ} (hC0 : 0 ≤ C0) (hCc : 0 ≤ Cc) (hC4 : 0 ≤ C4)
    (hC6 : 0 ≤ C6) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hα : 0 < α) (hα1 : α ≤ 1) :
    49 * (C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
        + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))))
      ≤ (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1) * α ^ (-(3 : ℝ))
          * (1 + X) ^ 4 * (1 + Y ^ 2) := by
  set K : ℝ := (1 + X) ^ 4 * (1 + Y ^ 2) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]; positivity
  have hB : Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)) ≤ Cc * (2 * C4 + C6) * K := by
    have h1 : C4 * X * (X * Y + Y * Y) = C4 * (X ^ 2 * Y + X * (Y * Y)) := by ring
    have h2 : C6 * Y * (X * Y) = C6 * (X * (Y * Y)) := by ring
    rw [h1, h2]
    have h3 : C4 * (X ^ 2 * Y + X * Y ^ 2) ≤ C4 * (K + K) := by
      refine mul_le_mul_of_nonneg_left ?_ hC4
      rw [hK]
      exact add_le_add (sq_mul_le_one_add hX hY) (mul_sq_le_one_add hX hY)
    have h4 : C6 * (X * Y ^ 2) ≤ C6 * K := by
      refine mul_le_mul_of_nonneg_left ?_ hC6
      rw [hK]
      exact mul_sq_le_one_add hX hY
    have h5 : (0 : ℝ) ≤ C4 * (K + K) := by positivity
    have h6 : (0 : ℝ) ≤ C6 * K := by positivity
    calc Cc * (C4 * (X ^ 2 * Y + X * (Y * Y)) + C6 * (X * (Y * Y)))
        ≤ Cc * (C4 * (K + K) + C6 * K) := by
          refine mul_le_mul_of_nonneg_left ?_ hCc; linarith
      _ = Cc * (2 * C4 + C6) * K := by ring
  have hα3 : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
    have h1 : (α⁻¹) ^ (3 : ℝ) = α ^ (-(3 : ℝ)) := by
      rw [Real.inv_rpow hα.le, Real.rpow_neg hα.le]
    rw [← h1]
    exact Real.one_le_rpow ((one_le_inv₀ hα).mpr hα1) (by norm_num)
  have hM : (0 : ℝ) ≤ (4096 * 4096) * 49 * Cc * (2 * C4 + C6) * K := by
    have h3 : (0 : ℝ) ≤ 2 * C4 + C6 := by linarith
    positivity
  have hKM : 0 ≤ C0 * K := by positivity
  have h1 : 49 * (C0 * (1 + X) ^ 4 * (1 + Y ^ 2)) ≤ 49 * C0 * K := by
    rw [hK]
    exact le_of_eq (by ring)
  have h2 : 49 * (4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))))
      ≤ (4096 * 4096) * 49 * Cc * (2 * C4 + C6) * K := by
    have h3 : 49 * (4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))))
        = 49 * (4096 * 4096) * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))) := by
      ring
    rw [h3]
    calc 49 * (4096 * 4096) * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)))
        ≤ 49 * (4096 * 4096) * (Cc * (2 * C4 + C6) * K) := by
          refine mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = (4096 * 4096) * 49 * Cc * (2 * C4 + C6) * K := by ring
  have h4 : 49 * (C0 * (1 + X) ^ 4 * (1 + Y ^ 2)
        + 4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y))))
      = 49 * (C0 * (1 + X) ^ 4 * (1 + Y ^ 2))
        + 49 * (4096 * 4096 * (Cc * (C4 * X * (X * Y + Y * Y) + C6 * Y * (X * Y)))) := by
    ring
  rw [h4]
  refine le_trans (add_le_add h1 h2) ?_
  calc 49 * C0 * K + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) * K
      = (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6)) * K := by ring
    _ ≤ (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1) * K := by
        nlinarith [hKnn]
    _ = (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1)
          * ((1 + X) ^ 4 * (1 + Y ^ 2)) := by rw [hK]
    _ ≤ (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1)
          * (α ^ (-(3 : ℝ)) * ((1 + X) ^ 4 * (1 + Y ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (1 + X) ^ 4 * (1 + Y ^ 2) = 1 * ((1 + X) ^ 4 * (1 + Y ^ 2)) := by ring
          _ ≤ α ^ (-(3 : ℝ)) * ((1 + X) ^ 4 * (1 + Y ^ 2)) :=
              mul_le_mul_of_nonneg_right hα3 (by positivity)
    _ = (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1) * α ^ (-(3 : ℝ))
          * (1 + X) ^ 4 * (1 + Y ^ 2) := by ring

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.lintegral_Ioo_reflect =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open MeasureTheory

/-- Reflection of the Lebesgue integral on an open interval: substituting `θ = b - φ`
(the reflection `φ ↦ b - φ` maps `(0, b - a)` onto `(a, b)` and preserves Lebesgue measure)
gives `∫⁻_{θ ∈ (a,b)} F θ = ∫⁻_{φ ∈ (0,b-a)} F (b - φ)`. -/
theorem lintegral_Ioo_reflect (F : ℝ → ENNReal) (a b : ℝ) :
    (∫⁻ θ in Set.Ioo a b, F θ) = ∫⁻ φ in Set.Ioo (0 : ℝ) (b - a), F (b - φ) := by
  -- The reflection `φ ↦ b - φ` is a measurable embedding (it is an isometry of `ℝ`).
  have hemb : MeasurableEmbedding (fun φ : ℝ => b - φ) :=
    (MeasurableEquiv.subLeft b).measurableEmbedding
  -- It maps `(0, b - a)` onto `(a, b)`.
  have hpre : (fun φ : ℝ => b - φ) ⁻¹' Set.Ioo a b = Set.Ioo (0 : ℝ) (b - a) := by
    ext x; simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith
  -- It preserves Lebesgue measure.
  have hmap : Measure.map (fun φ : ℝ => b - φ) (volume : Measure ℝ) = volume := by
    have h1 : Measure.map (fun x : ℝ => -x) (volume : Measure ℝ) = volume :=
      Measure.map_neg_eq_self (volume : Measure ℝ)
    have h2 : Measure.map (fun y : ℝ => b + y) (volume : Measure ℝ) = volume :=
      Measure.IsAddLeftInvariant.map_add_left_eq_self b
    have hg : Measurable (fun y : ℝ => b + y) := measurable_const_add b
    have hf : Measurable (fun x : ℝ => -x) := measurable_neg
    rw [show (fun φ : ℝ => b - φ) = fun x : ℝ => b + -x from by funext x; rw [sub_eq_add_neg]]
    calc Measure.map (fun x : ℝ => b + -x) (volume : Measure ℝ)
        = Measure.map ((fun y : ℝ => b + y) ∘ (fun x : ℝ => -x)) volume := rfl
      _ = Measure.map (fun y : ℝ => b + y)
            (Measure.map (fun x : ℝ => -x) (volume : Measure ℝ)) :=
            (Measure.map_map hg hf).symm
      _ = volume := by rw [h1, h2]
  -- Hence the restricted measures correspond.
  have hres : (volume : Measure ℝ).restrict (Set.Ioo a b)
      = Measure.map (fun φ : ℝ => b - φ)
          ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (b - a))) := by
    have h := MeasurableEmbedding.restrict_map hemb (volume : Measure ℝ) (Set.Ioo a b)
    rw [hmap, hpre] at h
    exact h
  calc (∫⁻ θ in Set.Ioo a b, F θ)
      = ∫⁻ θ, F θ ∂((volume : Measure ℝ).restrict (Set.Ioo a b)) := rfl
    _ = ∫⁻ θ, F θ ∂(Measure.map (fun φ : ℝ => b - φ)
          ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (b - a)))) := by rw [hres]
    _ = ∫⁻ φ, F ((fun φ : ℝ => b - φ) φ)
          ∂((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (b - a))) :=
          MeasurableEmbedding.lintegral_map hemb F
    _ = ∫⁻ φ in Set.Ioo (0 : ℝ) (b - a), F (b - φ) := rfl

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.slotArith =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

theorem slotArith {α Cpw K0 K4 HkSq : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hCpw : 0 < Cpw)
    (hK0 : 0 ≤ K0) (hK4 : 0 ≤ K4) (hH : 0 ≤ HkSq) :
    Real.sqrt (K4 ^ 2 + 1)
        * Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
      ≤ (Real.sqrt (10 * Cpw + 1) + 1) * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + HkSq)) := by
  -- abbreviations: s := α⁻¹ ≥ 1, B := √(10 Cpw + 1), C := 1 + HkSq
  have hs1 : 1 ≤ α ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]
    exact (one_le_inv₀ hα0).2 hα1
  have hs0 : 0 ≤ α ^ (-(1 : ℝ)) := le_trans zero_le_one hs1
  -- α^{-3} = (α^{-1})³
  have hα3 : α ^ (-(3 : ℝ)) = (α ^ (-(1 : ℝ))) ^ 3 := by
    rw [show (-(3 : ℝ)) = (-(1 : ℝ)) + (-(1 : ℝ)) + (-(1 : ℝ)) by norm_num,
      Real.rpow_add hα0, Real.rpow_add hα0]
    ring
  rw [hα3]
  -- √(K4²+1) ≤ 1 + K4
  have hA : Real.sqrt (K4 ^ 2 + 1) ≤ 1 + K4 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith [hK4]⟩
  -- 10 Cpw s HkSq² + 1 ≤ (10 Cpw s + 1)(1 + HkSq)²
  have hXbound : Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1
      ≤ (10 * Cpw * α ^ (-(1 : ℝ)) + 1) * (1 + HkSq) ^ 2 := by
    have key : (10 * Cpw * α ^ (-(1 : ℝ)) + 1) * (1 + HkSq) ^ 2
        - (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
        = 10 * Cpw * α ^ (-(1 : ℝ)) * (2 * HkSq + 1) + (2 * HkSq + HkSq * HkSq) := by ring
    have h1 : 0 ≤ 10 * Cpw * α ^ (-(1 : ℝ)) * (2 * HkSq + 1) := by positivity
    have h2 : 0 ≤ 2 * HkSq + HkSq * HkSq := by nlinarith
    linarith
  -- √(10 Cpw s + 1) ≤ √(10 Cpw + 1) · s
  have hsq : Real.sqrt (10 * Cpw * α ^ (-(1 : ℝ)) + 1)
      ≤ Real.sqrt (10 * Cpw + 1) * α ^ (-(1 : ℝ)) := by
    have h2 : α ^ (-(1 : ℝ)) ≤ (α ^ (-(1 : ℝ))) ^ 2 := by nlinarith [hs1]
    have hp : 10 * Cpw * α ^ (-(1 : ℝ)) + 1 ≤ (10 * Cpw + 1) * (α ^ (-(1 : ℝ))) ^ 2 := by
      have h1 : 10 * Cpw * α ^ (-(1 : ℝ)) + 1 ≤ (10 * Cpw + 1) * α ^ (-(1 : ℝ)) := by
        nlinarith [hs1]
      nlinarith [h1, h2, hCpw]
    calc Real.sqrt (10 * Cpw * α ^ (-(1 : ℝ)) + 1)
        ≤ Real.sqrt ((10 * Cpw + 1) * (α ^ (-(1 : ℝ))) ^ 2) := Real.sqrt_le_sqrt hp
      _ = Real.sqrt (10 * Cpw + 1) * α ^ (-(1 : ℝ)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs0]
  -- √(Cpw · 10 · s · HkSq² + 1) ≤ √(10 Cpw + 1) · (1 + HkSq) · s
  have hB : Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
      ≤ Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ)) := by
    calc Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
        ≤ Real.sqrt ((10 * Cpw * α ^ (-(1 : ℝ)) + 1) * (1 + HkSq) ^ 2) :=
          Real.sqrt_le_sqrt hXbound
      _ = Real.sqrt (10 * Cpw * α ^ (-(1 : ℝ)) + 1) * (1 + HkSq) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]
      _ ≤ Real.sqrt (10 * Cpw + 1) * α ^ (-(1 : ℝ)) * (1 + HkSq) :=
          mul_le_mul_of_nonneg_right hsq (by linarith)
      _ = Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ)) := by ring
  -- the remaining purely algebraic step, with the three monotonicities
  -- 1 + K4 ≤ 1 + K0 + K4,  √(10Cpw+1) ≤ √(10Cpw+1) + 1,  s ≤ s³
  have hfinal : (1 + K4) * (Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ)))
      ≤ (Real.sqrt (10 * Cpw + 1) + 1) * (α ^ (-(1 : ℝ))) ^ 3
        * ((1 + K0 + K4) * (1 + HkSq)) := by
    have hs3 : α ^ (-(1 : ℝ)) ≤ (α ^ (-(1 : ℝ))) ^ 3 := by
      simpa using pow_le_pow_right₀ hs1 (show (1 : ℕ) ≤ 3 by norm_num)
    have hDnn : 0 ≤ 1 + K0 + K4 := by linarith
    have hBle : Real.sqrt (10 * Cpw + 1) ≤ Real.sqrt (10 * Cpw + 1) + 1 := by linarith
    have hK : 1 + K4 ≤ 1 + K0 + K4 := by linarith
    have hCnn : 0 ≤ 1 + HkSq := by linarith
    have hprod : 0 ≤ Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ)) := by positivity
    have hA' : (1 + K4) * (Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ)))
        ≤ (1 + K0 + K4) * (Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ))) :=
      mul_le_mul_of_nonneg_right hK hprod
    have hBC : Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ))
        ≤ (Real.sqrt (10 * Cpw + 1) + 1) * ((1 + HkSq) * α ^ (-(1 : ℝ))) := by
      have h1 : Real.sqrt (10 * Cpw + 1) * (1 + HkSq)
          ≤ (Real.sqrt (10 * Cpw + 1) + 1) * (1 + HkSq) :=
        mul_le_mul_of_nonneg_right hBle hCnn
      have h2 := mul_le_mul_of_nonneg_right h1 hs0
      nlinarith [h2]
    have hCs : (1 + HkSq) * α ^ (-(1 : ℝ)) ≤ (1 + HkSq) * (α ^ (-(1 : ℝ))) ^ 3 :=
      mul_le_mul_of_nonneg_left hs3 hCnn
    have hBCs : (Real.sqrt (10 * Cpw + 1) + 1) * ((1 + HkSq) * α ^ (-(1 : ℝ)))
        ≤ (Real.sqrt (10 * Cpw + 1) + 1) * ((1 + HkSq) * (α ^ (-(1 : ℝ))) ^ 3) :=
      mul_le_mul_of_nonneg_left hCs (by nlinarith [Real.sqrt_nonneg (10 * Cpw + 1)])
    calc (1 + K4) * (Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ)))
        ≤ (1 + K0 + K4) * (Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ))) := hA'
      _ ≤ (1 + K0 + K4)
            * ((Real.sqrt (10 * Cpw + 1) + 1) * ((1 + HkSq) * α ^ (-(1 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hBC hDnn
      _ ≤ (1 + K0 + K4)
            * ((Real.sqrt (10 * Cpw + 1) + 1) * ((1 + HkSq) * (α ^ (-(1 : ℝ))) ^ 3)) :=
          mul_le_mul_of_nonneg_left hBCs hDnn
      _ = (Real.sqrt (10 * Cpw + 1) + 1) * (α ^ (-(1 : ℝ))) ^ 3
            * ((1 + K0 + K4) * (1 + HkSq)) := by
          ring
  calc Real.sqrt (K4 ^ 2 + 1) * Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
      ≤ (1 + K4) * (Real.sqrt (10 * Cpw + 1) * (1 + HkSq) * α ^ (-(1 : ℝ))) :=
        mul_le_mul hA hB (Real.sqrt_nonneg _) (by linarith)
    _ ≤ (Real.sqrt (10 * Cpw + 1) + 1) * (α ^ (-(1 : ℝ))) ^ 3
          * ((1 + K0 + K4) * (1 + HkSq)) :=
        hfinal

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.aemeasurable_deriv_fst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter MeasureTheory
open scoped MeasureTheory Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- Auxiliary lemma: translating the first coordinate by a *positive* amount preserves
`AEMeasurable` with respect to `(volume.restrict (Ioi 0)).prod ν`.

The push-forward of `Λ := (volume.restrict (Ioi 0)).prod ν` under `T p = (p.1 + h, p.2)` is
`Λ.map T = (volume.restrict (Ioi h)).prod ν ≤ Λ` (`Measure.map_prod_map`, `Measure.restrict_map`,
`map_add_right_eq_self`, `Measure.prod_mono`, `Measure.restrict_mono`); hence
`AEMeasurable Φ (Λ.map T)` (`AEMeasurable.mono_measure`) and `AEMeasurable (Φ ∘ T) Λ`
(`AEMeasurable.comp_measurable`). -/
theorem aemeasurable_comp_add_fst' {ν : MeasureTheory.Measure ℝ} [MeasureTheory.SFinite ν]
    {h : ℝ} (hh : 0 < h) {Φ : ℝ × ℝ → ℝ}
    (hΦ : AEMeasurable Φ ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν)) :
    AEMeasurable (fun p : ℝ × ℝ => Φ (p.1 + h, p.2))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν) := by
  set μ : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν with hμ
  have hΦμ : AEMeasurable Φ μ := hΦ
  have hTmeas : Measurable (fun p : ℝ × ℝ => (p.1 + h, p.2)) :=
    (measurable_fst.add_const h).prodMk measurable_snd
  have hvol : MeasureTheory.Measure.map (fun z : ℝ => z + h)
        (MeasureTheory.volume.restrict (Set.Ioi 0))
      = MeasureTheory.volume.restrict (Set.Ioi h) := by
    have hpre : (fun z : ℝ => z + h) ⁻¹' (Set.Ioi h) = Set.Ioi 0 := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Ioi]
      constructor <;> intro hz <;> linarith
    have hf : Measurable (fun z : ℝ => z + h) := measurable_id.add_const h
    rw [← hpre,
      ← MeasureTheory.Measure.restrict_map (f := fun z : ℝ => z + h) hf measurableSet_Ioi,
      MeasureTheory.map_add_right_eq_self MeasureTheory.volume h]
  have hmap : MeasureTheory.Measure.map (fun p : ℝ × ℝ => (p.1 + h, p.2)) μ
      = (MeasureTheory.volume.restrict (Set.Ioi h)).prod ν := by
    have h1 := MeasureTheory.Measure.map_prod_map (MeasureTheory.volume.restrict (Set.Ioi 0)) ν
      (f := fun z : ℝ => z + h) (g := id) (measurable_id.add_const h) measurable_id
    have h2 : MeasureTheory.Measure.map (Prod.map (fun z : ℝ => z + h) id)
          ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν)
        = MeasureTheory.Measure.map (fun p : ℝ × ℝ => (p.1 + h, p.2))
          ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν) := rfl
    rw [hμ, ← h2, ← h1, hvol, MeasureTheory.Measure.map_id]
  have hle : MeasureTheory.Measure.map (fun p : ℝ × ℝ => (p.1 + h, p.2)) μ ≤ μ := by
    rw [hmap, hμ]
    exact MeasureTheory.Measure.prod_mono
      (MeasureTheory.Measure.restrict_mono (Set.Ioi_subset_Ioi hh.le) le_rfl) le_rfl
  have hfin := (hΦμ.mono_measure hle).comp_measurable hTmeas
  rw [show (Φ ∘ fun p : ℝ × ℝ => (p.1 + h, p.2)) = (fun p : ℝ × ℝ => Φ (p.1 + h, p.2))
      from rfl] at hfin
  exact hfin

/-- If `Φ : ℝ × ℝ → ℝ` is a.e.-measurable w.r.t. `(volume.restrict (Ioi 0)).prod ν` and each
`z`-slice `z ↦ Φ (z, θ)` is differentiable on `(0,∞)`, then the derivative `∂_z Φ` is again
a.e.-measurable w.r.t. the same measure.

Route: for `n ≥ 1` the difference quotients
`p ↦ n * (Φ (p.1 + 1/n, p.2) - Φ (p.1, p.2))`
are a.e.-measurable (translate the a.e.-measurability by the positive shift `1/n`: the
push-forward of the measure under `(z,θ) ↦ (z+1/n,θ)` is
`(volume.restrict (Ioi (1/n))).prod ν ≤ (volume.restrict (Ioi 0)).prod ν`, via
`Measure.map_prod_map`, `Measure.restrict_map`, `map_add_right_eq_self`, `Measure.prod_mono`,
`Measure.restrict_mono`; then `AEMeasurable.mono_measure` + `AEMeasurable.comp_measurable`),
and they converge a.e. (for `z > 0`) to `∂_zΦ` by `DifferentiableOn.hasDerivAt` +
`HasDerivAt.tendsto_slope` (+ `tendsto_one_div_atTop_nhds_zero_nat`).  An a.e. limit of
a.e.-measurable functions is a.e.-measurable (`AEMeasurable.limsup` + `Tendsto.limsup_eq`). -/
theorem aemeasurable_deriv_fst {ν : MeasureTheory.Measure ℝ} [MeasureTheory.SFinite ν]
    {Φ : ℝ × ℝ → ℝ}
    (hΦ : AEMeasurable Φ ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν))
    (hdiff : ∀ θ : ℝ, DifferentiableOn ℝ (fun z => Φ (z, θ)) (Set.Ioi 0)) :
    AEMeasurable (fun p : ℝ × ℝ => deriv (fun z => Φ (z, p.2)) p.1)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν) := by
  set μ : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict (Set.Ioi 0)).prod ν with hμ
  have hΦμ : AEMeasurable Φ μ := hΦ
  set F : ℕ → ℝ × ℝ → ℝ :=
    fun n p => (n : ℝ) * (Φ (p.1 + (n : ℝ)⁻¹, p.2) - Φ (p.1, p.2)) with hF
  -- the difference quotients are a.e.-measurable
  have hshift : ∀ n : ℕ, 0 < (n : ℝ)⁻¹ →
      AEMeasurable (fun p : ℝ × ℝ => Φ (p.1 + (n : ℝ)⁻¹, p.2)) μ :=
    fun n hn => aemeasurable_comp_add_fst' hn hΦμ
  have hFmeas : ∀ n : ℕ, AEMeasurable (F n) μ := by
    intro n
    cases n with
    | zero =>
      have hzero : F 0 = fun _ : ℝ × ℝ => (0 : ℝ) := by
        funext p
        simp only [hF, Nat.cast_zero, inv_zero, add_zero, zero_mul]
      rw [hzero]
      exact aemeasurable_const
    | succ k =>
      have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ)⁻¹ :=
        inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos k))
      have h1 : AEMeasurable (fun p : ℝ × ℝ => Φ (p.1 + ((k + 1 : ℕ) : ℝ)⁻¹, p.2)) μ :=
        hshift (k + 1) hpos
      have h2 : AEMeasurable (fun p : ℝ × ℝ => Φ (p.1, p.2)) μ := by simpa using hΦμ
      have h3 := h1.sub h2
      have h4 := h3.const_mul ((k + 1 : ℕ) : ℝ)
      simpa [hF] using h4
  -- the first coordinate is positive almost everywhere
  have hμ_eq : μ = ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod ν).restrict
      (Set.prod (Set.Ioi 0) Set.univ) := by
    have h := MeasureTheory.Measure.prod_restrict
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (ν := ν) (Set.Ioi 0) Set.univ
    rw [MeasureTheory.Measure.restrict_univ] at h
    rw [hμ]
    exact h
  have hae_mem : ∀ᵐ p ∂μ, p ∈ Set.prod (Set.Ioi 0) Set.univ := by
    rw [hμ_eq]
    exact MeasureTheory.ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)
  have hpos : ∀ᵐ p ∂μ, 0 < p.1 := hae_mem.mono (fun p hp => hp.1)
  -- pointwise (a.e.) convergence of the difference quotients to the derivative
  have hconv : ∀ᵐ p ∂μ, Filter.Tendsto (fun n : ℕ => F n p) Filter.atTop
      (nhds (deriv (fun z : ℝ => Φ (z, p.2)) p.1)) := by
    filter_upwards [hpos] with p hp
    have hH : HasDerivAt (fun z : ℝ => Φ (z, p.2))
        (deriv (fun z : ℝ => Φ (z, p.2)) p.1) p.1 :=
      DifferentiableOn.hasDerivAt (hdiff p.2) (isOpen_Ioi.mem_nhds hp)
    have hbase : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop (nhds (0 : ℝ)) := by
      simpa only [one_div] using tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hseq : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop
        (nhdsWithin (0 : ℝ) ({(0 : ℝ)}ᶜ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hbase, ?_⟩
      filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
      exact inv_ne_zero (Nat.cast_ne_zero.mpr (by omega))
    have hcomp := (hH.tendsto_slope_zero).comp hseq
    refine Filter.Tendsto.congr' ?_ hcomp
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    simp only [Function.comp_apply, hF, inv_inv, smul_eq_mul]
  -- an a.e. limit of a.e.-measurable functions is a.e.-measurable
  have hlimmeas : AEMeasurable
      (fun p : ℝ × ℝ => Filter.limsup (fun n : ℕ => F n p) Filter.atTop) μ :=
    AEMeasurable.limsup hFmeas
  refine hlimmeas.congr ?_
  filter_upwards [hconv] with p hp
  exact hp.limsup_eq

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkArith =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux


end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.arithNsumG3Dz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG

set_option maxHeartbeats 800000
set_option linter.all false

/-- Auxiliary: `1 + K₀ + K₄ + K₁` is bounded by the product of the three prices. -/
lemma nsumG3Dz_one_add {α M Ce k0 k4 k1 K0 K4 K1 : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hM : 0 ≤ M) (hk0 : 0 ≤ k0) (hk4 : 0 ≤ k4) (hk1 : 0 ≤ k1)
    (hp0 : K0 ≤ k0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
    (hp4 : K4 ≤ k4 * (1 + |Ce|) * M)
    (hp1 : K1 ≤ k1 * (1 + |Ce|) * (1 + M)) :
    1 + K0 + K4 + K1 ≤ (1 + k0 + k4 + k1) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
  have hAm0 : 0 ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
  have hAm1 : 1 ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
  have hαhalf : 1 ≤ α ^ (-(1 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show (-(1 / 2 : ℝ)) ≤ (0 : ℝ) by norm_num)
    simpa using h
  have hm0 : 0 ≤ 1 + M := by linarith
  have hm1 : 1 ≤ 1 + M := by linarith
  have hW1 : 1 ≤ α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hαhalf hAm1) hm1
  have hK0W : K0 ≤ k0 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
    rw [show k0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)
        = k0 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) from by ring] at hp0
    exact hp0
  have hK4W : K4 ≤ k4 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
    have hMM : M ≤ α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
      calc M ≤ 1 + M := by linarith
        _ ≤ α ^ (-(1 / 2 : ℝ)) * (1 + M) := le_mul_of_one_le_left hm0 hαhalf
    have h1 : k4 * (1 + |Ce|) * M ≤ k4 * (1 + |Ce|) * (α ^ (-(1 / 2 : ℝ)) * (1 + M)) :=
      mul_le_mul_of_nonneg_left hMM (mul_nonneg hk4 hAm0)
    have h2 : k4 * (1 + |Ce|) * (α ^ (-(1 / 2 : ℝ)) * (1 + M))
        = k4 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by ring
    linarith [hp4, h1, h2]
  have hK1W : K1 ≤ k1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
    have hk1' : k1 ≤ k1 * α ^ (-(1 / 2 : ℝ)) := le_mul_of_one_le_right hk1 hαhalf
    have h1 : k1 * (1 + |Ce|) ≤ (k1 * α ^ (-(1 / 2 : ℝ))) * (1 + |Ce|) :=
      mul_le_mul_of_nonneg_right hk1' hAm0
    have h2 : k1 * (1 + |Ce|) * (1 + M) ≤ ((k1 * α ^ (-(1 / 2 : ℝ))) * (1 + |Ce|)) * (1 + M) :=
      mul_le_mul_of_nonneg_right h1 hm0
    have h3 : ((k1 * α ^ (-(1 / 2 : ℝ))) * (1 + |Ce|)) * (1 + M)
        = k1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by ring
    linarith [hp1, h2, h3]
  have h1 : 1 + K0 + K4 + K1 ≤ 1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      + k0 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      + k4 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      + k1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by
    linarith [hW1, hK0W, hK4W, hK1W]
  have h2 : 1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      + k0 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      + k4 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      + k1 * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
      = (1 + k0 + k4 + k1) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) := by ring
  linarith [h1, h2]

/-- Auxiliary: `K₄ + K₆` is bounded by the product of the two prices. -/
lemma nsumG3Dz_K46 {M Ce H k4 k6 K4 K6 : ℝ} (hM : 0 ≤ M) (hH0 : 0 ≤ H)
    (hk4 : 0 ≤ k4) (hk6 : 0 ≤ k6)
    (hp4 : K4 ≤ k4 * (1 + |Ce|) * M)
    (hp6 : K6 ≤ k6 * (1 + |Ce|) * H) :
    K4 + K6 ≤ (k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H) := by
  have hAm0 : 0 ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
  have hm0 : 0 ≤ 1 + M := by linarith
  have hm1 : 1 ≤ 1 + M := by linarith
  have hh0 : 0 ≤ 1 + H := by linarith
  have hh1 : 1 ≤ 1 + H := by linarith
  have hB4 : K4 ≤ k4 * (1 + |Ce|) * (1 + M) * (1 + H) := by
    have s1 : k4 * (1 + |Ce|) * M ≤ k4 * (1 + |Ce|) * (1 + M) :=
      mul_le_mul_of_nonneg_left (by linarith : M ≤ 1 + M) (mul_nonneg hk4 hAm0)
    have s2 : k4 * (1 + |Ce|) * (1 + M) ≤ k4 * (1 + |Ce|) * (1 + M) * (1 + H) :=
      le_mul_of_one_le_right (mul_nonneg (mul_nonneg hk4 hAm0) hm0) hh1
    linarith [hp4, s1, s2]
  have hB6 : K6 ≤ k6 * (1 + |Ce|) * (1 + M) * (1 + H) := by
    have s1 : k6 * (1 + |Ce|) * H ≤ k6 * (1 + |Ce|) * (1 + M) * H :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg hk6 hAm0) hm1) hH0
    have s2 : k6 * (1 + |Ce|) * (1 + M) * H ≤ k6 * (1 + |Ce|) * (1 + M) * (1 + H) :=
      mul_le_mul_of_nonneg_left (by linarith : H ≤ 1 + H) (mul_nonneg (mul_nonneg hk6 hAm0) hm0)
    linarith [hp6, s1, s2]
  nlinarith [hB4, hB6]

/-- First half of the arithmetic: the `(1 + K₀ + K₄ + K₁)` bracket. -/
lemma nsumG3Dz_first {α M Ce Cs S C0 k0 k4 k6 k1 K0 K4 K1 : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hC0 : 0 ≤ C0) (hM : 0 ≤ M) (hS0 : 0 ≤ S)
    (hk0 : 0 ≤ k0) (hk4 : 0 ≤ k4) (hk6 : 0 ≤ k6) (hk1 : 0 ≤ k1)
    (hp0 : K0 ≤ k0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
    (hp4 : K4 ≤ k4 * (1 + |Ce|) * M)
    (hp1 : K1 ≤ k1 * (1 + |Ce|) * (1 + M)) :
    C0 * α ^ (-(4 : ℝ)) * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S))
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S) := by
  have hA : 1 + K0 + K4 + K1
      ≤ (1 + k0 + k4 + k1) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)) :=
    nsumG3Dz_one_add hα0 hα1 hM hk0 hk4 hk1 hp0 hp4 hp1
  have hm0 : 0 ≤ 1 + M := by linarith
  have hm1 : 1 ≤ 1 + M := by linarith
  have hs0 : 0 ≤ 1 + S := by linarith
  have hAm0 : 0 ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
  have hm24 : (1 + M) ^ 2 ≤ (1 + M) ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hm2nn : 0 ≤ (1 + M) ^ 2 := pow_nonneg hm0 2
  have hm4nn : 0 ≤ (1 + M) ^ 4 := pow_nonneg hm0 4
  have hABnn : 0 ≤ 1 + |Ce| + |Cs| := by linarith [abs_nonneg Ce, abs_nonneg Cs]
  have hAB1 : 1 ≤ 1 + |Ce| + |Cs| := by linarith [abs_nonneg Ce, abs_nonneg Cs]
  have hAB4nn : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := pow_nonneg hABnn 4
  have hAm_le : 1 + |Ce| ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    have h3 : 1 + |Ce| + |Cs| ≤ (1 + |Ce| + |Cs|) ^ 4 := le_self_pow₀ hAB1 (by norm_num)
    linarith [abs_nonneg Cs]
  have hα4nn : 0 ≤ α ^ (-(4 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hα10nn : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hαhalf0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hαcomb : α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(10 : ℝ)) := by
    rw [← Real.rpow_add hα0]
    rw [show -(4 : ℝ) + -(1 / 2 : ℝ) = -(9 / 2 : ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hαcomb0 : 0 ≤ α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hα4nn hαhalf0
  have hC0α4 : 0 ≤ C0 * α ^ (-(4 : ℝ)) := mul_nonneg hC0 hα4nn
  have hT0 : 0 ≤ 1 + k0 + k4 + k6 + k1 := by linarith
  have hT'T : 1 + k0 + k4 + k1 ≤ 1 + k0 + k4 + k6 + k1 := by linarith
  have hT1b : (1 + K0 + K4 + K1) * (1 + M) * (1 + S)
      ≤ ((1 + k0 + k4 + k1) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)))
          * (1 + M) * (1 + S) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hm0) hs0
  have hT1c : C0 * α ^ (-(4 : ℝ)) * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S))
      ≤ C0 * α ^ (-(4 : ℝ))
          * (((1 + k0 + k4 + k1) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)))
              * (1 + M) * (1 + S)) :=
    mul_le_mul_of_nonneg_left hT1b hC0α4
  have hT1d : C0 * α ^ (-(4 : ℝ))
          * (((1 + k0 + k4 + k1) * (α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M)))
              * (1 + M) * (1 + S))
      = (1 + k0 + k4 + k1) * C0 * (α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ)))
          * (1 + |Ce|) * (1 + M) ^ 2 * (1 + S) := by ring
  have e1 : (1 + k0 + k4 + k1) * C0 ≤ (1 + k0 + k4 + k6 + k1) * C0 :=
    mul_le_mul_of_nonneg_right hT'T hC0
  have e2 : (1 + k0 + k4 + k1) * C0 * (α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ)))
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) :=
    mul_le_mul e1 hαcomb hαcomb0 (mul_nonneg hT0 hC0)
  have e3 : (1 + k0 + k4 + k1) * C0 * (α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ))) * (1 + |Ce|)
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 :=
    mul_le_mul e2 hAm_le hAm0 (mul_nonneg (mul_nonneg hT0 hC0) hα10nn)
  have e4 : (1 + k0 + k4 + k1) * C0 * (α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ))) * (1 + |Ce|)
          * (1 + M) ^ 2
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 :=
    mul_le_mul e3 hm24 hm2nn (mul_nonneg (mul_nonneg (mul_nonneg hT0 hC0) hα10nn) hAB4nn)
  have hT1e : (1 + k0 + k4 + k1) * C0 * (α ^ (-(4 : ℝ)) * α ^ (-(1 / 2 : ℝ))) * (1 + |Ce|)
          * (1 + M) ^ 2 * (1 + S)
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S) :=
    mul_le_mul e4 (le_refl (1 + S)) hs0
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hT0 hC0) hα10nn) hAB4nn) hm4nn)
  exact le_trans hT1c (le_trans (le_of_eq hT1d) hT1e)

/-- Second half of the arithmetic: the `(K₄ + K₆)` bracket. -/
lemma nsumG3Dz_second {α M Ce Cs S H C0 k0 k4 k6 k1 K4 K6 : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hC0 : 0 ≤ C0) (hM : 0 ≤ M) (hH0 : 0 ≤ H) (hS0 : 0 ≤ S)
    (hSH : S = H ^ 2) (hk0 : 0 ≤ k0) (hk4 : 0 ≤ k4) (hk6 : 0 ≤ k6) (hk1 : 0 ≤ k1)
    (hp4 : K4 ≤ k4 * (1 + |Ce|) * M)
    (hp6 : K6 ≤ k6 * (1 + |Ce|) * H) :
    C0 * α ^ (-(4 : ℝ)) * ((K4 + K6) * (1 + M) * (1 + H))
      ≤ 4 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := by
  have hB : K4 + K6 ≤ (k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H) :=
    nsumG3Dz_K46 hM hH0 hk4 hk6 hp4 hp6
  have hm0 : 0 ≤ 1 + M := by linarith
  have hm1 : 1 ≤ 1 + M := by linarith
  have hh0 : 0 ≤ 1 + H := by linarith
  have hs0 : 0 ≤ 1 + S := by linarith
  have hAm0 : 0 ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
  have hm24 : (1 + M) ^ 2 ≤ (1 + M) ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hm2nn : 0 ≤ (1 + M) ^ 2 := pow_nonneg hm0 2
  have hm4nn : 0 ≤ (1 + M) ^ 4 := pow_nonneg hm0 4
  have hH2nn : 0 ≤ (1 + H) ^ 2 := pow_nonneg hh0 2
  have hH2S : (1 + H) ^ 2 ≤ 4 * (1 + S) := by nlinarith [hSH, sq_nonneg (H - 1 / 3)]
  have hABnn : 0 ≤ 1 + |Ce| + |Cs| := by linarith [abs_nonneg Ce, abs_nonneg Cs]
  have hAB1 : 1 ≤ 1 + |Ce| + |Cs| := by linarith [abs_nonneg Ce, abs_nonneg Cs]
  have hAB4nn : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := pow_nonneg hABnn 4
  have hAm_le : 1 + |Ce| ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    have h3 : 1 + |Ce| + |Cs| ≤ (1 + |Ce| + |Cs|) ^ 4 := le_self_pow₀ hAB1 (by norm_num)
    linarith [abs_nonneg Cs]
  have hα4nn : 0 ≤ α ^ (-(4 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hα10nn : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hα4_le_10 : α ^ (-(4 : ℝ)) ≤ α ^ (-(10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hC0α4 : 0 ≤ C0 * α ^ (-(4 : ℝ)) := mul_nonneg hC0 hα4nn
  have hT0 : 0 ≤ 1 + k0 + k4 + k6 + k1 := by linarith
  have hT2b : (K4 + K6) * (1 + M) * (1 + H)
      ≤ ((k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H)) * (1 + M) * (1 + H) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hm0) hh0
  have hT2c : C0 * α ^ (-(4 : ℝ)) * ((K4 + K6) * (1 + M) * (1 + H))
      ≤ C0 * α ^ (-(4 : ℝ))
          * (((k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H)) * (1 + M) * (1 + H)) :=
    mul_le_mul_of_nonneg_left hT2b hC0α4
  have hT2d : C0 * α ^ (-(4 : ℝ))
          * (((k4 + k6) * (1 + |Ce|) * (1 + M) * (1 + H)) * (1 + M) * (1 + H))
      = (k4 + k6) * C0 * α ^ (-(4 : ℝ)) * (1 + |Ce|) * (1 + M) ^ 2 * (1 + H) ^ 2 := by ring
  have e1 : k4 + k6 ≤ 1 + k0 + k4 + k6 + k1 := by linarith
  have e2 : (k4 + k6) * C0 ≤ (1 + k0 + k4 + k6 + k1) * C0 :=
    mul_le_mul_of_nonneg_right e1 hC0
  have e3 : (k4 + k6) * C0 * α ^ (-(4 : ℝ))
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) :=
    mul_le_mul e2 hα4_le_10 hα4nn (mul_nonneg hT0 hC0)
  have e4 : (k4 + k6) * C0 * α ^ (-(4 : ℝ)) * (1 + |Ce|)
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 :=
    mul_le_mul e3 hAm_le hAm0 (mul_nonneg (mul_nonneg hT0 hC0) hα10nn)
  have e5 : (k4 + k6) * C0 * α ^ (-(4 : ℝ)) * (1 + |Ce|) * (1 + M) ^ 2
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 :=
    mul_le_mul e4 hm24 hm2nn (mul_nonneg (mul_nonneg (mul_nonneg hT0 hC0) hα10nn) hAB4nn)
  have hT2e : (k4 + k6) * C0 * α ^ (-(4 : ℝ)) * (1 + |Ce|) * (1 + M) ^ 2 * (1 + H) ^ 2
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + H) ^ 2 :=
    mul_le_mul e5 (le_refl ((1 + H) ^ 2)) hH2nn
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hT0 hC0) hα10nn) hAB4nn) hm4nn)
  have hT2f : (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + H) ^ 2
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (4 * (1 + S)) :=
    mul_le_mul_of_nonneg_left hH2S
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hT0 hC0) hα10nn) hAB4nn) hm4nn)
  have hT2g : (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (4 * (1 + S))
      = 4 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := by ring
  exact le_trans hT2c (le_trans (le_of_eq hT2d) (le_trans hT2e (le_trans hT2f (le_of_eq hT2g))))

theorem arithNsumG3Dz {X α M Ce Cs S H C0 k0 k4 k6 k1 K0 K4 K6 K1 : ℝ}
    (hX : X ≤ C0 * α ^ (-(4 : ℝ)) * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S)
      + (K4 + K6) * (1 + M) * (1 + H)))
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hC0 : 0 ≤ C0)
    (hSH : S = H ^ 2) (hH0 : 0 ≤ H) (hS0 : 0 ≤ S)
    (hk0 : 0 ≤ k0) (hk4 : 0 ≤ k4) (hk6 : 0 ≤ k6) (hk1 : 0 ≤ k1)
    (hK0 : 0 ≤ K0) (hK4 : 0 ≤ K4) (hK6 : 0 ≤ K6) (hK1 : 0 ≤ K1) (hM : 0 ≤ M)
    (hp0 : K0 ≤ k0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
    (hp4 : K4 ≤ k4 * (1 + |Ce|) * M)
    (hp6 : K6 ≤ k6 * (1 + |Ce|) * H)
    (hp1 : K1 ≤ k1 * (1 + |Ce|) * (1 + M)) :
    X ≤ (16 * (1 + k0 + k4 + k6 + k1) * C0) * α ^ (-(10 : ℝ))
          * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + S) := by
  have hfin1 : C0 * α ^ (-(4 : ℝ)) * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S))
      ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S) :=
    nsumG3Dz_first (Cs := Cs) hα0 hα1 hC0 hM hS0 hk0 hk4 hk6 hk1 hp0 hp4 hp1
  have hfin2 : C0 * α ^ (-(4 : ℝ)) * ((K4 + K6) * (1 + M) * (1 + H))
      ≤ 4 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) :=
    nsumG3Dz_second (Cs := Cs) (S := S) hα0 hα1 hC0 hM hH0 hS0 hSH hk0 hk4 hk6 hk1 hp4 hp6
  have hsplit : C0 * α ^ (-(4 : ℝ))
        * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S) + (K4 + K6) * (1 + M) * (1 + H))
      = C0 * α ^ (-(4 : ℝ)) * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S))
        + C0 * α ^ (-(4 : ℝ)) * ((K4 + K6) * (1 + M) * (1 + H)) := by ring
  have hsum : C0 * α ^ (-(4 : ℝ))
        * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S) + (K4 + K6) * (1 + M) * (1 + H))
      ≤ 5 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := by
    rw [hsplit]
    linarith [hfin1, hfin2]
  have h16 : 5 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S))
      ≤ 16 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := by
    have hnn : 0 ≤ (1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
        * (1 + M) ^ 4 * (1 + S) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg (by linarith) hC0) (Real.rpow_nonneg hα0.le _))
          (pow_nonneg (by linarith [abs_nonneg Ce, abs_nonneg Cs]) 4))
            (pow_nonneg (by linarith) 4)) (by linarith)
    linarith
  calc X ≤ C0 * α ^ (-(4 : ℝ))
        * ((1 + K0 + K4 + K1) * (1 + M) * (1 + S) + (K4 + K6) * (1 + M) * (1 + H)) := hX
    _ ≤ 5 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := hsum
    _ ≤ 16 * ((1 + k0 + k4 + k6 + k1) * C0 * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
          * (1 + M) ^ 4 * (1 + S)) := h16
    _ = (16 * (1 + k0 + k4 + k6 + k1) * C0) * α ^ (-(10 : ℝ))
          * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + S) := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.AuxAgmon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## Elementary prerequisites -/

/-- The AM–GM (arithmetic–geometric mean) estimate `|ab| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
    rw [abs_mul, ← sq_abs a, ← sq_abs b]
    nlinarith [sq_nonneg (|a| - |b|)]
  linarith

/-- The `rpow` identity `x^(1/2) * x = x^(3/2)` for `x ≥ 0` (at `x = 0` both sides vanish). -/
private lemma rpow_half_mul_self (x : ℝ) (hx : 0 ≤ x) : x ^ (1 / 2 : ℝ) * x = x ^ (3 / 2 : ℝ) := by
  rcases hx.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    simp
  · have h1 : x ^ (1 / 2 : ℝ) * x ^ (1 : ℝ) = x ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add h, show (1 : ℝ) / 2 + 1 = 3 / 2 by norm_num]
    simpa using h1


/-! ## Cauchy–Schwarz on the half-line -/


/-! ## The pointwise Agmon bound -/


/-! ## The main lemma -/


end Work.FTS.StrongPersist.L3Rhs
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.sum_sq_binom_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs.VfsRadAux

theorem sum_sq_binom_le (q : ℕ) (hq : q ≤ 3) (X Y : ℕ → ℝ)
    (hY : ∀ j ≤ 3, |Y j| ≤ 24000) :
    ((∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (X b * Y (q - b))) ^ 2)
      ≤ 256 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2 := by
  -- Rewrite the summand so that Cauchy–Schwarz applies with the coefficient
  -- `f b = C(q,b)·Y(q-b)` against the factor `X b`.
  have hsum_eq : (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (X b * Y (q - b)))
      = ∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y (q - b)) * X b := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hsum_eq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (q + 1))
      (fun b => (q.choose b : ℝ) * Y (q - b)) X
  -- The squared coefficient sum is controlled by `4 · (8 · 24000)² = 256 · 24000²`.
  have hf2 : ∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y (q - b)) ^ 2
      ≤ 256 * 24000 ^ 2 := by
    have hterm : ∀ b ∈ Finset.range (q + 1),
        ((q.choose b : ℝ) * Y (q - b)) ^ 2 ≤ 64 * 24000 ^ 2 := by
      intro b hb
      have hc0 : (0 : ℝ) ≤ (q.choose b : ℝ) := by positivity
      have hc : (q.choose b : ℝ) ^ 2 ≤ 64 := by
        have h' : (q.choose b : ℝ) ≤ 8 := by
          have h1 : q.choose b ≤ 2 ^ q := Nat.choose_le_two_pow q b
          have h2 : 2 ^ q ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hq
          have h3 : q.choose b ≤ 8 := le_trans h1 (by simpa using h2)
          exact_mod_cast h3
        nlinarith [h', hc0]
      have hy : (Y (q - b)) ^ 2 ≤ 24000 ^ 2 := by
        have h := hY (q - b) (by omega)
        exact sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
      calc ((q.choose b : ℝ) * Y (q - b)) ^ 2
          = (q.choose b : ℝ) ^ 2 * (Y (q - b)) ^ 2 := by ring
        _ ≤ 64 * 24000 ^ 2 := mul_le_mul hc hy (sq_nonneg _) (by norm_num)
    calc ∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y (q - b)) ^ 2
        ≤ (Finset.range (q + 1)).card • (64 * 24000 ^ 2) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = ((q + 1 : ℕ) : ℝ) * (64 * 24000 ^ 2) := by
            simp [Finset.card_range, nsmul_eq_mul]
      _ ≤ 256 * 24000 ^ 2 := by
          have hq1 : ((q + 1 : ℕ) : ℝ) ≤ 4 := by
            have : q + 1 ≤ 4 := by omega
            exact_mod_cast this
          have hc0 : (0 : ℝ) ≤ 64 * 24000 ^ 2 := by norm_num
          have := mul_le_mul_of_nonneg_right hq1 hc0
          nlinarith [this]
  have hX2 : ∑ b ∈ Finset.range (q + 1), (X b) ^ 2 ≤ ∑ b ∈ Finset.range 4, (X b) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro b hb
      simp only [Finset.mem_range] at hb ⊢
      omega
    · intro b _ _
      exact sq_nonneg _
  calc (∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y (q - b)) * X b) ^ 2
      ≤ (∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y (q - b)) ^ 2)
          * ∑ b ∈ Finset.range (q + 1), (X b) ^ 2 := hcs
    _ ≤ (256 * 24000 ^ 2) * ∑ b ∈ Finset.range 4, (X b) ^ 2 :=
        mul_le_mul hf2 hX2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)

end Work.FTS.StrongPersist.L3Rhs.VfsRadAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.abs_le_quartic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

theorem abs_le_quartic (z s b c d e : ℝ) (hz : 0 ≤ z) :
    |s * z ^ 4 + b * z ^ 3 + c * z ^ 2 + d * z + e| ≤ (|s| + |b| + |c| + |d| + |e|) * (1 + z) ^ 4 := by
  have h1z : (1 : ℝ) ≤ 1 + z := by linarith
  have h4 : z ^ 4 ≤ (1 + z) ^ 4 := pow_le_pow_left₀ hz (by linarith) 4
  have h3 : z ^ 3 ≤ (1 + z) ^ 4 :=
    le_trans (pow_le_pow_left₀ hz (by linarith) 3)
      (pow_le_pow_right₀ h1z (show (3 : ℕ) ≤ 4 by norm_num))
  have h2 : z ^ 2 ≤ (1 + z) ^ 4 :=
    le_trans (pow_le_pow_left₀ hz (by linarith) 2)
      (pow_le_pow_right₀ h1z (show (2 : ℕ) ≤ 4 by norm_num))
  have h1 : z ≤ (1 + z) ^ 4 := by
    have hz1 : z ≤ 1 + z := by linarith
    have hh : (1 + z) ≤ (1 + z) ^ 4 := by
      simpa using pow_le_pow_right₀ h1z (show (1 : ℕ) ≤ 4 by norm_num)
    exact le_trans hz1 hh
  have h0 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ h1z
  have step1 : |s * z ^ 4 + b * z ^ 3 + c * z ^ 2 + d * z + e|
      ≤ |s * z ^ 4| + |b * z ^ 3| + |c * z ^ 2| + |d * z| + |e| := by
    have hA := abs_add_le (s * z ^ 4 + b * z ^ 3 + c * z ^ 2 + d * z) e
    have hB := abs_add_le (s * z ^ 4 + b * z ^ 3 + c * z ^ 2) (d * z)
    have hC := abs_add_le (s * z ^ 4 + b * z ^ 3) (c * z ^ 2)
    have hD := abs_add_le (s * z ^ 4) (b * z ^ 3)
    linarith
  have step2 : |s * z ^ 4| + |b * z ^ 3| + |c * z ^ 2| + |d * z| + |e|
      = |s| * z ^ 4 + |b| * z ^ 3 + |c| * z ^ 2 + |d| * z + |e| := by
    simp only [abs_mul]
    rw [abs_of_nonneg (pow_nonneg hz 4), abs_of_nonneg (pow_nonneg hz 3),
      abs_of_nonneg (pow_nonneg hz 2), abs_of_nonneg hz]
  have step3 : |s| * z ^ 4 + |b| * z ^ 3 + |c| * z ^ 2 + |d| * z + |e|
      ≤ (|s| + |b| + |c| + |d| + |e|) * (1 + z) ^ 4 := by
    have hs := abs_nonneg s
    have hb := abs_nonneg b
    have hc := abs_nonneg c
    have hd := abs_nonneg d
    have he := abs_nonneg e
    have m4 : |s| * z ^ 4 ≤ |s| * (1 + z) ^ 4 := mul_le_mul_of_nonneg_left h4 hs
    have m3 : |b| * z ^ 3 ≤ |b| * (1 + z) ^ 4 := mul_le_mul_of_nonneg_left h3 hb
    have m2 : |c| * z ^ 2 ≤ |c| * (1 + z) ^ 4 := mul_le_mul_of_nonneg_left h2 hc
    have m1 : |d| * z ≤ |d| * (1 + z) ^ 4 := mul_le_mul_of_nonneg_left h1 hd
    have m0 : |e| ≤ |e| * (1 + z) ^ 4 := le_mul_of_one_le_right he h0
    nlinarith [m4, m3, m2, m1, m0]
  linarith [step1, step2, step3]

end Work.FTS.StrongPersist.L6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.abs_le_quintic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A crude bound for a quintic polynomial by its coefficient `ℓ¹`-norm

For `z ≥ 0` and arbitrary real coefficients `s, b, c, d, e, f`,

`|s z⁵ + b z⁴ + c z³ + d z² + e z + f| ≤ (|s|+|b|+|c|+|d|+|e|+|f|) (1+z)⁵`.

The proof is the triangle inequality, termwise, together with the pointwise bounds
`z ^ k ≤ (1 + z) ^ 5` for `0 ≤ z` and `k ≤ 5` (both `z ≤ 1 + z` and `(1 + z) ^ k ≤ (1 + z) ^ 5`
follow from `1 ≤ 1 + z`).
-/

namespace Work.FTS.StrongPersist.L6Aux

/-- `z ^ k ≤ (1 + z) ^ 5` for `z ≥ 0` and `k ≤ 5`. -/
private lemma pow_le_one_add_pow_five {z : ℝ} (hz : 0 ≤ z) {k : ℕ} (hk : k ≤ 5) :
    z ^ k ≤ (1 + z) ^ 5 := by
  have h1z : (1 : ℝ) ≤ 1 + z := by linarith
  have hzle : z ≤ 1 + z := by linarith
  calc z ^ k ≤ (1 + z) ^ k := pow_le_pow_left₀ hz hzle k
    _ ≤ (1 + z) ^ 5 := pow_le_pow_right₀ h1z hk

theorem abs_le_quintic (z s b c d e f : ℝ) (hz : 0 ≤ z) :
    |s * z ^ 5 + b * z ^ 4 + c * z ^ 3 + d * z ^ 2 + e * z + f|
      ≤ (|s| + |b| + |c| + |d| + |e| + |f|) * (1 + z) ^ 5 := by
  have hzn : (0 : ℝ) ≤ z := hz
  have hP : (1 : ℝ) ≤ (1 + z) ^ 5 := by
    have := pow_le_one_add_pow_five hz (show (0 : ℕ) ≤ 5 by norm_num)
    simpa using this
  -- termwise bounds
  have hA : |s * z ^ 5| ≤ |s| * (1 + z) ^ 5 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hzn 5)]
    exact mul_le_mul_of_nonneg_left (pow_le_one_add_pow_five hz le_rfl) (abs_nonneg s)
  have hB : |b * z ^ 4| ≤ |b| * (1 + z) ^ 5 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hzn 4)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_one_add_pow_five hz (by norm_num)) (abs_nonneg b)
  have hC : |c * z ^ 3| ≤ |c| * (1 + z) ^ 5 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hzn 3)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_one_add_pow_five hz (by norm_num)) (abs_nonneg c)
  have hD : |d * z ^ 2| ≤ |d| * (1 + z) ^ 5 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hzn 2)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_one_add_pow_five hz (by norm_num)) (abs_nonneg d)
  have hE : |e * z| ≤ |e| * (1 + z) ^ 5 := by
    rw [abs_mul, abs_of_nonneg hzn]
    exact mul_le_mul_of_nonneg_left
      (by simpa using pow_le_one_add_pow_five hz (show (1 : ℕ) ≤ 5 by norm_num))
      (abs_nonneg e)
  have hF : |f| ≤ |f| * (1 + z) ^ 5 := le_mul_of_one_le_right (abs_nonneg f) hP
  -- triangle inequality, peeled off one term at a time
  have t1 : |s * z ^ 5 + b * z ^ 4 + c * z ^ 3 + d * z ^ 2 + e * z + f|
      ≤ |s * z ^ 5 + b * z ^ 4 + c * z ^ 3 + d * z ^ 2 + e * z| + |f| := abs_add_le _ _
  have t2 : |s * z ^ 5 + b * z ^ 4 + c * z ^ 3 + d * z ^ 2 + e * z|
      ≤ |s * z ^ 5 + b * z ^ 4 + c * z ^ 3 + d * z ^ 2| + |e * z| := abs_add_le _ _
  have t3 : |s * z ^ 5 + b * z ^ 4 + c * z ^ 3 + d * z ^ 2|
      ≤ |s * z ^ 5 + b * z ^ 4 + c * z ^ 3| + |d * z ^ 2| := abs_add_le _ _
  have t4 : |s * z ^ 5 + b * z ^ 4 + c * z ^ 3|
      ≤ |s * z ^ 5 + b * z ^ 4| + |c * z ^ 3| := abs_add_le _ _
  have t5 : |s * z ^ 5 + b * z ^ 4| ≤ |s * z ^ 5| + |b * z ^ 4| := abs_add_le _ _
  have hX : (|s| + |b| + |c| + |d| + |e| + |f|) * (1 + z) ^ 5
      = (|s| * (1 + z) ^ 5 + |b| * (1 + z) ^ 5 + |c| * (1 + z) ^ 5
          + |d| * (1 + z) ^ 5 + |e| * (1 + z) ^ 5) + |f| * (1 + z) ^ 5 := by ring
  linarith [t1, t2, t3, t4, t5, hA, hB, hC, hD, hE, hF, hX]

end Work.FTS.StrongPersist.L6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.abs_le_sextic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

theorem abs_le_sextic (z s b c d e f g : ℝ) (hz : 0 ≤ z) :
    |s * z ^ 6 + b * z ^ 5 + c * z ^ 4 + d * z ^ 3 + e * z ^ 2 + f * z + g|
      ≤ (|s| + |b| + |c| + |d| + |e| + |f| + |g|) * (1 + z) ^ 6 := by
  have h1z : 1 ≤ 1 + z := by linarith
  -- each power of z is dominated by (1+z)^6
  have hpow : ∀ k ≤ 6, z ^ k ≤ (1 + z) ^ 6 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simpa using one_le_pow₀ h1z (n := 6)
    · exact le_trans (pow_le_pow_left₀ hz (by linarith) k) (pow_le_pow_right₀ h1z hk)
  -- each summand is bounded by |coefficient| * (1+z)^6
  have key : ∀ a k, k ≤ 6 → |a * z ^ k| ≤ |a| * (1 + z) ^ 6 := by
    intro a k hk
    rw [abs_mul, abs_of_nonneg (pow_nonneg hz k)]
    exact mul_le_mul_of_nonneg_left (hpow k hk) (abs_nonneg a)
  have hs := key s 6 le_rfl
  have hb := key b 5 (by norm_num)
  have hc := key c 4 (by norm_num)
  have hd := key d 3 (by norm_num)
  have he := key e 2 (by norm_num)
  have hf := key f 1 (by norm_num)
  have hg : |g| ≤ |g| * (1 + z) ^ 6 :=
    le_mul_of_one_le_right (abs_nonneg g) (hpow 0 (by norm_num))
  rw [abs_le']
  constructor
  · have h1 := (abs_le.mp hs).2
    have h2 := (abs_le.mp hb).2
    have h3 := (abs_le.mp hc).2
    have h4 := (abs_le.mp hd).2
    have h5 := (abs_le.mp he).2
    have h6 := (abs_le.mp hf).2
    have h7 := (abs_le.mp hg).2
    linarith
  · have h1 := (abs_le.mp hs).1
    have h2 := (abs_le.mp hb).1
    have h3 := (abs_le.mp hc).1
    have h4 := (abs_le.mp hd).1
    have h5 := (abs_le.mp he).1
    have h6 := (abs_le.mp hf).1
    have h7 := (abs_le.mp hg).1
    linarith

end Work.FTS.StrongPersist.L6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.radZop_deriv4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

theorem radZop_deriv4 (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (-y ^ 3 + 18 * y ^ 2 - 33 * y + 8) / (1 + y) ^ 6)
      (2 * z * (z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16) / (1 + z) ^ 7) z := by
  have hz1 : (1 + z : ℝ) ≠ 0 := by intro h; exact hz (by linarith)
  -- ∂_z (z^2) = 2z, ∂_z (z^3) = 3z^2
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * z ^ 2) z := by simpa using hasDerivAt_pow 3 z
  -- the numerator polynomial  N y = -y^3 + 18 y^2 - 33 y + 8
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 3) (-(3 * z ^ 2)) z := h3.neg
  have h18 : HasDerivAt (fun y : ℝ => 18 * y ^ 2) (18 * (2 * z)) z := h2.const_mul 18
  have h33 : HasDerivAt (fun y : ℝ => 33 * y) (33 * 1) z := (hasDerivAt_id z).const_mul 33
  have h8 : HasDerivAt (fun y : ℝ => (8 : ℝ)) 0 z := hasDerivAt_const z 8
  have hN : HasDerivAt (fun y : ℝ => -y ^ 3 + 18 * y ^ 2 - 33 * y + 8)
      (-(3 * z ^ 2) + 18 * (2 * z) - 33 * 1 + 0) z :=
    ((h1.add h18).sub h33).add h8
  have h2N : HasDerivAt (fun y : ℝ => 2 * y ^ 2) (2 * (2 * z)) z := h2.const_mul 2
  have hnum : HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (-y ^ 3 + 18 * y ^ 2 - 33 * y + 8))
      (2 * (2 * z) * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8)
        + 2 * z ^ 2 * (-(3 * z ^ 2) + 18 * (2 * z) - 33 * 1 + 0)) z :=
    h2N.mul hN
  -- ∂_z ((1+z)^6) = 6 (1+z)^5
  have hshift : HasDerivAt (fun y : ℝ => 1 + y) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have hden := by simpa using hshift.pow 6
  have hz6 : (1 + z) ^ 6 ≠ 0 := pow_ne_zero 6 hz1
  refine (hnum.div hden hz6).congr_deriv ?_
  field_simp
  simp only [Pi.pow_apply]
  ring

end Work.FTS.StrongPersist.L6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.radZop_deriv5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

theorem radZop_deriv5 (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (y ^ 4 - 41 * y ^ 3 + 171 * y ^ 2 - 131 * y + 16) / (1 + y) ^ 7)
      (2 * z * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32) / (1 + z) ^ 8) z := by
  -- the polynomial is positive at no point of the proof; we only need the algebraic identity
  --   (2 y² P y)'(z) (1+z) - 7 · 2 z² P z = 2 z · Q z
  -- with `P y = y⁴ - 41y³ + 171y² - 131y + 16` and `Q z = -z⁵ + 88z⁴ - 718z³ + 1208z² - 473z + 32`,
  -- which `ring` checks once denominators are cleared.
  have hz1 : (1 : ℝ) + z ≠ 0 := fun h => hz (by linarith)
  -- derivative of the quartic factor
  have hP : HasDerivAt (fun y : ℝ => y ^ 4 - 41 * y ^ 3 + 171 * y ^ 2 - 131 * y + 16)
      (4 * z ^ 3 - 123 * z ^ 2 + 342 * z - 131) z := by
    have h := ((((hasDerivAt_pow 4 z).sub ((hasDerivAt_pow 3 z).const_mul (41:ℝ))).add
        ((hasDerivAt_pow 2 z).const_mul (171:ℝ))).sub ((hasDerivAt_id' z).const_mul (131:ℝ))).add_const (16:ℝ)
    convert h using 1
    ring
  -- derivative of the numerator `2 y² · P y`
  have hN : HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (y ^ 4 - 41 * y ^ 3 + 171 * y ^ 2 - 131 * y + 16))
      (2 * (2 * z * (z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16)
        + z ^ 2 * (4 * z ^ 3 - 123 * z ^ 2 + 342 * z - 131))) z := by
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
    have h := (h2.const_mul (2:ℝ)).mul hP
    convert h using 1
    ring
  -- derivative of the denominator `(1 + y) ^ 7`
  have hD : HasDerivAt (fun y : ℝ => (1 + y) ^ 7) (7 * (1 + z) ^ 6) z := by
    have h := ((hasDerivAt_const z (1:ℝ)).add (hasDerivAt_id' z)).pow 7
    convert h using 1
    simp only [Pi.add_apply]
    ring
  have hz7 : (1 + z) ^ 7 ≠ 0 := pow_ne_zero 7 hz1
  -- quotient rule
  have h := hN.div hD hz7
  convert h using 1
  rw [div_eq_div_iff (pow_ne_zero 8 hz1) (pow_ne_zero 2 hz7)]
  ring

end Work.FTS.StrongPersist.L6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.radZop_deriv6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

/-- The sixth iterate of the radial operator `Zop u z = z·u'(z)` applied to the profile
`2z²/(1+z)³` is the rational function `2z²Q(z)/(1+z)⁹` with
`Q(z) = z⁶ - 183z⁵ + 2682z⁴ - 8422z³ + 7197z² - 1611z + 64`; this is the derivative of the
previous iterate.  The claim is a purely algebraic identity: the numerator
`N(y) = 2y²(-y⁵+88y⁴-718y³+1208y²-473y+32)` and the denominator `(1+y)⁸` are differentiated
by the product/quotient rule and the result is normalised by `ring`. -/
theorem radZop_deriv6 (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (-y ^ 5 + 88 * y ^ 4 - 718 * y ^ 3 + 1208 * y ^ 2 - 473 * y + 32) / (1 + y) ^ 8)
      (2 * z * (z ^ 6 - 183 * z ^ 5 + 2682 * z ^ 4 - 8422 * z ^ 3 + 7197 * z ^ 2 - 1611 * z + 64) / (1 + z) ^ 9) z := by
  have hz1 : (1 + z) ≠ 0 := by intro h; exact hz (by linarith)
  -- The numerator `2y²·P(y)`.
  have hnum : HasDerivAt
      (fun y : ℝ => 2 * y ^ 2 * (-y ^ 5 + 88 * y ^ 4 - 718 * y ^ 3 + 1208 * y ^ 2 - 473 * y + 32))
      (4 * z * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32)
        + 2 * z ^ 2 * (-5 * z ^ 4 + 352 * z ^ 3 - 2154 * z ^ 2 + 2416 * z - 473)) z := by
    have h1 : HasDerivAt (fun y : ℝ => 2 * y ^ 2) (4 * z) z := by
      have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
      convert h using 1
      ring
    have hP : HasDerivAt
        (fun y : ℝ => -y ^ 5 + 88 * y ^ 4 - 718 * y ^ 3 + 1208 * y ^ 2 - 473 * y + 32)
        (-5 * z ^ 4 + 352 * z ^ 3 - 2154 * z ^ 2 + 2416 * z - 473) z := by
      have t5 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * z ^ 4) z := by
        have h := hasDerivAt_pow 5 z; simpa using h
      have t4 : HasDerivAt (fun y : ℝ => 88 * y ^ 4) (88 * (4 * z ^ 3)) z :=
        (hasDerivAt_pow 4 z).const_mul 88
      have t3 : HasDerivAt (fun y : ℝ => 718 * y ^ 3) (718 * (3 * z ^ 2)) z :=
        (hasDerivAt_pow 3 z).const_mul 718
      have t2 : HasDerivAt (fun y : ℝ => 1208 * y ^ 2) (1208 * (2 * z)) z := by
        have h := (hasDerivAt_pow 2 z).const_mul 1208
        convert h using 1
        ring
      have t1 : HasDerivAt (fun y : ℝ => 473 * y) (473 : ℝ) z := by
        simpa using (hasDerivAt_id z).const_mul (473 : ℝ)
      have hraw := ((((t5.neg.add t4).sub t3).add t2).sub t1).add_const 32
      convert hraw using 1
      ring
    exact h1.mul hP
  -- The denominator `(1+y)⁸`.
  have hden : HasDerivAt (fun y : ℝ => (1 + y) ^ 8) (8 * (1 + z) ^ 7) z := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) (1 : ℝ) z := (hasDerivAt_id z).const_add 1
    have h := (hasDerivAt_pow 8 (1 + z)).comp z h1
    simpa [Function.comp_def] using h
  have hdiv := hnum.div hden (pow_ne_zero 8 hz1)
  -- Normalise the quotient rule result.
  convert hdiv using 1
  rw [div_eq_div_iff (pow_ne_zero 9 hz1) (pow_ne_zero 2 (pow_ne_zero 8 hz1))]
  ring

end Work.FTS.StrongPersist.L6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.SlotArithHon =====
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

/-- The arithmetic of the final constant in the honest shape: the frozen `slot_arith` with the
honest `Smain` constant `Csm` (only `0 ≤ Csm` is used) in place of `2`. -/
theorem slot_arith_hon {r Xf Kf Xg Cs Cl Cg Cd Csm : ℝ}
    (hr1 : 1 ≤ r) (hr0 : 0 ≤ r) (hXf : 0 ≤ Xf) (hKf : 0 ≤ Kf) (hXg : 0 ≤ Xg)
    (hCs : 0 ≤ Cs) (hCl : 0 ≤ Cl) (hCg : 0 ≤ Cg) (hCd : 0 ≤ Cd) (hCsm : 0 ≤ Csm)
    (h10 : Real.sqrt 10 ≤ 10) :
    Csm * (Cs * (Real.sqrt 10 * r) * Xf) * Xg ^ 2
      + (6400 * ((Cs * (Real.sqrt 10 * r) * Xf + Cl * Kf) * Xg ^ 2
          + Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
        + (16 * ((Cs * (Real.sqrt 10 * r) * Xf + Cl * Kf) * Xg ^ 2
            + Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
          + Cd * r * (Xf + Kf) * Xg ^ 2))
      ≤ (11 * Csm + 10 ^ 8) * (Cs + Cl + Cg + Cd + 1) * r * (Xf + Kf) * Xg ^ 2 := by
  have hsq : (0 : ℝ) ≤ Xg ^ 2 := sq_nonneg Xg
  have hsq10 : (0 : ℝ) ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  set T : ℝ := r * (Xf + Kf) * Xg ^ 2 with hTdef
  have hT : 0 ≤ T := by rw [hTdef]; positivity
  have h1 : r * Xf * Xg ^ 2 ≤ T := by
    rw [hTdef]; nlinarith [mul_nonneg hr0 (mul_nonneg hKf hsq)]
  have h3 : Kf * Xg ^ 2 ≤ T := by
    rw [hTdef]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r - 1) (mul_nonneg hKf hsq),
      mul_nonneg hr0 (mul_nonneg hXf hsq), mul_nonneg hKf hsq]
  have H1 : Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2 ≤ 10 * Cs * T := by
    rw [show Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2
        = Cs * Real.sqrt 10 * (r * Xf * Xg ^ 2) by ring]
    calc Cs * Real.sqrt 10 * (r * Xf * Xg ^ 2)
        ≤ Cs * Real.sqrt 10 * T := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCs hsq10)
      _ ≤ 10 * Cs * T := by
          have hc : Cs * Real.sqrt 10 ≤ 10 * Cs := by nlinarith [hCs, h10]
          exact mul_le_mul_of_nonneg_right hc hT
  have H2 : Cl * Kf * Xg ^ 2 ≤ Cl * T := by
    rw [show Cl * Kf * Xg ^ 2 = Cl * (Kf * Xg ^ 2) by ring]
    exact mul_le_mul_of_nonneg_left h3 hCl
  have H3 : Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg) ≤ 10 * Cg * T := by
    rw [show Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg)
        = Cg * Real.sqrt 10 * (r * Xf * Xg ^ 2) by ring]
    calc Cg * Real.sqrt 10 * (r * Xf * Xg ^ 2)
        ≤ Cg * Real.sqrt 10 * T := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCg hsq10)
      _ ≤ 10 * Cg * T := by
          have hc : Cg * Real.sqrt 10 ≤ 10 * Cg := by nlinarith [hCg, h10]
          exact mul_le_mul_of_nonneg_right hc hT
  have H4 : Cd * r * (Xf + Kf) * Xg ^ 2 = Cd * T := by rw [hTdef]; ring
  have H0 : Csm * (Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2) ≤ 11 * Csm * (Cs * T) :=
    le_trans (mul_le_mul_of_nonneg_left H1 hCsm)
      (by nlinarith [mul_nonneg hCsm (mul_nonneg hCs hT)])
  have hLHS : Csm * (Cs * (Real.sqrt 10 * r) * Xf) * Xg ^ 2
      + (6400 * ((Cs * (Real.sqrt 10 * r) * Xf + Cl * Kf) * Xg ^ 2
          + Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
        + (16 * ((Cs * (Real.sqrt 10 * r) * Xf + Cl * Kf) * Xg ^ 2
            + Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
          + Cd * r * (Xf + Kf) * Xg ^ 2))
      = Csm * (Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2)
        + (6400 * (Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2)
          + (6400 * (Cl * Kf * Xg ^ 2)
            + (6400 * (Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
              + (16 * (Cs * (Real.sqrt 10 * r) * Xf * Xg ^ 2)
                + (16 * (Cl * Kf * Xg ^ 2)
                  + (16 * (Cg * (Real.sqrt 10 * r) * Xg * (Xf * Xg))
                    + Cd * r * (Xf + Kf) * Xg ^ 2)))))) := by ring
  rw [hLHS, H4]
  have hSum : (0 : ℝ) ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  have hSumT : 0 ≤ (Cs + Cl + Cg + Cd + 1) * T := mul_nonneg hSum hT
  have hCsSum : Cs ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  have hClSum : Cl ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  have hCgSum : Cg ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  have hCdSum : Cd ≤ Cs + Cl + Cg + Cd + 1 := by linarith
  nlinarith [H0, H1, H2, H3, hT, hSum, hSumT, hCsm, hCs, hCl, hCg, hCd, hXg,
    mul_le_mul_of_nonneg_left hCsSum hT, mul_le_mul_of_nonneg_left hClSum hT,
    mul_le_mul_of_nonneg_left hCgSum hT, mul_le_mul_of_nonneg_left hCdSum hT]

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SupZ.weightedAgmonAbstract =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongPersist.SupZ

set_option linter.unusedVariables false

/-- The elementary AM–GM inequality `2√(ab) ≤ a + b` for `a, b ≥ 0`. -/
private lemma two_mul_sqrt_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  have h4 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha b
  rw [h4]
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.mul_self_sqrt ha,
    Real.mul_self_sqrt hb]

/--
Abstract (weighted) Agmon inequality.

Assume `F, G ≥ 0` on `(0,∞)`, with `F z / z` and `G z * z` integrable there, and that for
every `x > z₀`
`F z₀ ≤ F x + 2 ∫_{z₀}^{x} √(F s · G s) ds`.
Then `F z₀ ≤ 2 ∫_0^∞ F z / z dz + ∫_0^∞ G z · z dz`.

The proof is the standard Agmon argument: AM–GM turns the integral term into
`∫_{z₀}^{x} (F s / s + G s · s) ds ≤ A + B` where `A = ∫ F/z`, `B = ∫ G·z`, so that
`F z₀ ≤ F x + A + B` for every `x > z₀`. If `A + B < F z₀` held, then `F s ≥ c := F z₀ - A - B >
0` on `(z₀,∞)`, whence `A ≥ ∫_{z₀}^{X} F s/s ds ≥ c log (X / z₀)` for every `X > z₀`, which is
absurd for `X = z₀ · exp (A/c + 1)`. Hence `F z₀ ≤ A + B ≤ 2A + B`. -/
theorem weightedAgmonAbstract {F G : ℝ → ℝ} {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hFm : MeasureTheory.AEStronglyMeasurable F (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hGm : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hFnn : ∀ z ∈ Set.Ioi 0, 0 ≤ F z)
    (hGnn : ∀ z ∈ Set.Ioi 0, 0 ≤ G z)
    (hFint : MeasureTheory.IntegrableOn (fun z : ℝ => F z / z) (Set.Ioi 0))
    (hGint : MeasureTheory.IntegrableOn (fun z : ℝ => G z * z) (Set.Ioi 0))
    (hkey : ∀ x ∈ Set.Ioi z₀, F z₀ ≤ F x + 2 * ∫ s in z₀..x, Real.sqrt (F s * G s)) :
    F z₀ ≤ 2 * (∫ z in Set.Ioi 0, F z / z) + (∫ z in Set.Ioi 0, G z * z) := by
  set A : ℝ := ∫ z in Set.Ioi 0, F z / z with hAdef
  set B : ℝ := ∫ z in Set.Ioi 0, G z * z with hBdef
  have hFnn_ae : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] fun z : ℝ => F z / z := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact div_nonneg (hFnn z hz) hz.le
  have hGnn_ae : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] fun z : ℝ => G z * z := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact mul_nonneg (hGnn z hz) hz.le
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg_of_ae hFnn_ae
  -- It suffices to prove the (stronger) bound `F z₀ ≤ A + B`.
  suffices hmain : F z₀ ≤ A + B by linarith
  by_contra hcon
  rw [not_le] at hcon
  -- AM–GM replaces `2√(F s G s)` by `F s / s + G s * s`.
  have hkeyb : ∀ x ∈ Set.Ioi z₀, 2 * ∫ s in z₀..x, Real.sqrt (F s * G s) ≤ A + B := by
    intro x hx
    have hxle : z₀ ≤ x := le_of_lt hx
    have hsub : Set.Ioc z₀ x ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_trans hz₀ hs.1
    have hsum_int : MeasureTheory.IntegrableOn (fun s : ℝ => F s / s + G s * s)
        (Set.Ioc z₀ x) := (hFint.mono_set hsub).add (hGint.mono_set hsub)
    have hsum_int0 : MeasureTheory.IntegrableOn (fun s : ℝ => F s / s + G s * s)
        (Set.Ioi 0) := hFint.add hGint
    have hsum_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
        fun s : ℝ => F s / s + G s * s := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
      exact add_nonneg (div_nonneg (hFnn s hs) hs.le) (mul_nonneg (hGnn s hs) hs.le)
    calc 2 * ∫ s in z₀..x, Real.sqrt (F s * G s)
        = ∫ s in z₀..x, 2 * Real.sqrt (F s * G s) :=
          (intervalIntegral.integral_const_mul 2
            (fun s : ℝ => Real.sqrt (F s * G s))).symm
      _ = ∫ s in Set.Ioc z₀ x, 2 * Real.sqrt (F s * G s) := by
          rw [intervalIntegral.integral_of_le hxle]
      _ ≤ ∫ s in Set.Ioc z₀ x, (F s / s + G s * s) := by
          refine setIntegral_mono_of_nonneg (fun s _ => ?_) (fun s hs => ?_) hsum_int
          · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
          · have hs0 : 0 < s := lt_trans hz₀ hs.1
            have ha : 0 ≤ F s / s := div_nonneg (hFnn s hs0) hs0.le
            have hb : 0 ≤ G s * s := mul_nonneg (hGnn s hs0) hs0.le
            have hprod : F s / s * (G s * s) = F s * G s := by field_simp
            have h := two_mul_sqrt_mul_le ha hb
            rwa [hprod] at h
      _ ≤ ∫ s in Set.Ioi (0 : ℝ), (F s / s + G s * s) := by
          refine setIntegral_mono_set hsum_int0 hsum_nn ?_
          exact Filter.Eventually.of_forall fun s hs => hsub hs
      _ = A + B := by rw [integral_add hFint hGint, ← hAdef, ← hBdef]
  -- Hence `F s ≥ c` on `(z₀,∞)`, where `c = F z₀ - (A + B) > 0`.
  set c : ℝ := F z₀ - (A + B) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hstep : ∀ x ∈ Set.Ioi z₀, c ≤ F x := by
    intro x hx
    have h1 := hkey x hx
    have h2 := hkeyb x hx
    rw [hcdef]; linarith
  -- Choose `X = z₀ · exp (A/c + 1)`, so that `∫_{z₀}^{X} c/s = A + c`.
  set X : ℝ := z₀ * Real.exp (A / c + 1) with hXdef
  have hXpos : 0 < X := by rw [hXdef]; exact mul_pos hz₀ (Real.exp_pos _)
  have hXgt : z₀ < X := by
    have h1 : 1 < Real.exp (A / c + 1) :=
      Real.one_lt_exp_iff.mpr (add_pos_of_nonneg_of_pos (div_nonneg hA_nonneg hcpos.le) one_pos)
    rw [hXdef]
    simpa using mul_lt_mul_of_pos_left h1 hz₀
  have hXdiv : X / z₀ = Real.exp (A / c + 1) := by rw [hXdef]; field_simp
  have hlog : Real.log (X / z₀) = A / c + 1 := by rw [hXdiv, Real.log_exp]
  have hsubX : Set.Ioc z₀ X ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_trans hz₀ hs.1
  have hFintX : IntervalIntegrable (fun s : ℝ => F s / s) volume z₀ X :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hXgt.le).mpr (hFint.mono_set hsubX)
  have hcintX : IntervalIntegrable (fun s : ℝ => c / s) volume z₀ X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hXgt.le]
    exact ContinuousOn.div continuousOn_const continuousOn_id
      (fun s hs => ne_of_gt (lt_of_lt_of_le hz₀ hs.1))
  have hval : c * (A / c + 1) = A + c := by
    have : c ≠ 0 := ne_of_gt hcpos
    field_simp
  -- Lower bound on `∫_{z₀}^{X} F s / s`.
  have hlow : c * (A / c + 1) ≤ ∫ s in z₀..X, F s / s := by
    have hcle : ∫ s in z₀..X, c / s ≤ ∫ s in z₀..X, F s / s := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hXgt.le hcintX hFintX ?_
      intro s hs
      have hs0 : 0 < s := lt_trans hz₀ hs.1
      exact div_le_div_of_nonneg_right (hstep s hs.1) hs0.le
    have heq : ∫ s in z₀..X, c / s = c * (A / c + 1) := by
      calc ∫ s in z₀..X, c / s
          = ∫ s in z₀..X, c * s⁻¹ := by simp only [div_eq_mul_inv]
        _ = c * ∫ s in z₀..X, s⁻¹ := intervalIntegral.integral_const_mul c _
        _ = c * Real.log (X / z₀) := by rw [integral_inv_of_pos hz₀ hXpos]
        _ = c * (A / c + 1) := by rw [hlog]
    linarith
  -- Upper bound on `∫_{z₀}^{X} F s / s`, coming from integrability on `(0,∞)`.
  have hup : ∫ s in z₀..X, F s / s ≤ A := by
    rw [intervalIntegral.integral_of_le hXgt.le]
    calc ∫ s in Set.Ioc z₀ X, F s / s
        ≤ ∫ s in Set.Ioi (0 : ℝ), F s / s := by
          refine setIntegral_mono_set hFint hFnn_ae ?_
          exact Filter.Eventually.of_forall fun s hs => hsubX hs
      _ = A := by rw [hAdef]
  linarith

end Work.FTS.StrongPersist.SupZ
end
-- ===== merged: Submission.Work.FTS.TransportS.T2Sup.absIntegralAddLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS.T2Sup

theorem absIntegralAddLe {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g : α → ℝ} (hf : MeasureTheory.Integrable f μ) :
    |∫ x, (f x + g x) ∂μ| ≤ |∫ x, f x ∂μ| + |∫ x, g x ∂μ| := by
  by_cases hg : MeasureTheory.Integrable g μ
  · rw [MeasureTheory.integral_add hf hg]
    exact abs_add_le _ _
  · have hfg : ¬ MeasureTheory.Integrable (fun x => f x + g x) μ := by
      intro h
      have h2 : ((fun x => f x + g x) - f) = g := by
        funext x
        simp [Pi.sub_apply]
      exact hg (h2 ▸ h.sub hf)
    rw [MeasureTheory.integral_undef hfg, MeasureTheory.integral_undef hg]
    simp

end Work.FTS.TransportS.T2Sup
end
-- ===== merged: Submission.Work.FTS.TransportS.TvUniform.csc_sqrt_specialise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS.TvUniform

theorem csc_sqrt_specialise {f g : ℝ → ℝ} {c θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hf : 0 ≤ f θ) (hg : 0 ≤ g θ) :
    2 * (Real.sin (2 * θ))⁻¹ * Real.sqrt (f θ * g θ)
      = 2 * Real.sqrt (f θ * (Real.sin (2 * θ)) ^ (-c))
          * Real.sqrt (g θ * (Real.sin (2 * θ)) ^ (c - 2)) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hs0 : 0 ≤ Real.sin (2 * θ) := le_of_lt hs
  have hA : 0 ≤ f θ * (Real.sin (2 * θ)) ^ (-c) :=
    mul_nonneg hf (Real.rpow_nonneg hs0 _)
  have hsq : Real.sqrt ((Real.sin (2 * θ)) ^ (-2 : ℝ)) = (Real.sin (2 * θ))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs0 (-2) (1/2),
      show (-2:ℝ) * (1/2) = -1 by norm_num, Real.rpow_neg_one]
  have hprod : (f θ * (Real.sin (2 * θ)) ^ (-c)) * (g θ * (Real.sin (2 * θ)) ^ (c - 2))
      = (f θ * g θ) * (Real.sin (2 * θ)) ^ (-2 : ℝ) := by
    have h1 : (f θ * (Real.sin (2 * θ)) ^ (-c)) * (g θ * (Real.sin (2 * θ)) ^ (c - 2))
        = (f θ * g θ) * ((Real.sin (2 * θ)) ^ (-c) * (Real.sin (2 * θ)) ^ (c - 2)) := by
      ring
    rw [h1, ← Real.rpow_add hs (-c) (c - 2),
      show -c + (c - 2) = (-2:ℝ) by ring]
  have hR : 2 * Real.sqrt (f θ * (Real.sin (2 * θ)) ^ (-c))
        * Real.sqrt (g θ * (Real.sin (2 * θ)) ^ (c - 2))
      = 2 * (Real.sqrt (f θ * g θ) * (Real.sin (2 * θ))⁻¹) := by
    calc 2 * Real.sqrt (f θ * (Real.sin (2 * θ)) ^ (-c))
            * Real.sqrt (g θ * (Real.sin (2 * θ)) ^ (c - 2))
        = 2 * (Real.sqrt (f θ * (Real.sin (2 * θ)) ^ (-c))
            * Real.sqrt (g θ * (Real.sin (2 * θ)) ^ (c - 2))) := by ring
      _ = 2 * Real.sqrt ((f θ * (Real.sin (2 * θ)) ^ (-c))
            * (g θ * (Real.sin (2 * θ)) ^ (c - 2))) := by
            rw [← Real.sqrt_mul hA (g θ * (Real.sin (2 * θ)) ^ (c - 2))]
      _ = 2 * Real.sqrt ((f θ * g θ) * (Real.sin (2 * θ)) ^ (-2 : ℝ)) := by rw [hprod]
      _ = 2 * (Real.sqrt (f θ * g θ) * Real.sqrt ((Real.sin (2 * θ)) ^ (-2 : ℝ))) := by
            rw [Real.sqrt_mul (mul_nonneg hf hg) ((Real.sin (2 * θ)) ^ (-2 : ℝ))]
      _ = 2 * (Real.sqrt (f θ * g θ) * (Real.sin (2 * θ))⁻¹) := by rw [hsq]
  rw [hR]
  ring

end Work.FTS.TransportS.TvUniform
end
-- ===== merged: Submission.Work.FTS.TransportS.TvUniform.exists_min_le_average =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS.TvUniform


end Work.FTS.TransportS.TvUniform
end
-- ===== merged: Submission.Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.TransportS.TvUniform

/-- Cauchy–Schwarz for the square roots of two nonnegative integrable functions. -/
theorem integral_sqrt_mul_sqrt_le {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {p q : α → ℝ} (hpnn : 0 ≤ᵐ[μ] p) (hqnn : 0 ≤ᵐ[μ] q)
    (hp : MeasureTheory.Integrable p μ) (hq : MeasureTheory.Integrable q μ) :
    ∫ x, Real.sqrt (p x) * Real.sqrt (q x) ∂μ
      ≤ Real.sqrt (∫ x, p x ∂μ) * Real.sqrt (∫ x, q x ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hfnn : 0 ≤ᵐ[μ] fun x => Real.sqrt (p x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have hgnn : 0 ≤ᵐ[μ] fun x => Real.sqrt (q x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have hfaesm : AEStronglyMeasurable (fun x => Real.sqrt (p x)) μ :=
    hp.aemeasurable.sqrt.aestronglyMeasurable
  have hgaesm : AEStronglyMeasurable (fun x => Real.sqrt (q x)) μ :=
    hq.aemeasurable.sqrt.aestronglyMeasurable
  have hfsq : Integrable (fun x => (Real.sqrt (p x)) ^ 2) μ :=
    hp.congr (hpnn.mono fun x hx => (Real.sq_sqrt hx).symm)
  have hgsq : Integrable (fun x => (Real.sqrt (q x)) ^ 2) μ :=
    hq.congr (hqnn.mono fun x hx => (Real.sq_sqrt hx).symm)
  have hfmem : MemLp (fun x => Real.sqrt (p x)) (ENNReal.ofReal (2 : ℝ)) μ := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hfaesm).mpr hfsq
  have hgmem : MemLp (fun x => Real.sqrt (q x)) (ENNReal.ofReal (2 : ℝ)) μ := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hgaesm).mpr hgsq
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq hfnn hgnn hfmem hgmem
  have h1 : ∫ x, (Real.sqrt (p x)) ^ (2 : ℝ) ∂μ = ∫ x, p x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hpnn] with x hx
    rw [Real.rpow_two, Real.sq_sqrt hx]
  have h2 : ∫ x, (Real.sqrt (q x)) ^ (2 : ℝ) ∂μ = ∫ x, q x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hqnn] with x hx
    rw [Real.rpow_two, Real.sq_sqrt hx]
  calc ∫ x, Real.sqrt (p x) * Real.sqrt (q x) ∂μ
      ≤ (∫ x, (Real.sqrt (p x)) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
          * (∫ x, (Real.sqrt (q x)) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hmain
    _ = (∫ x, p x ∂μ) ^ (1 / (2 : ℝ)) * (∫ x, q x ∂μ) ^ (1 / (2 : ℝ)) := by rw [h1, h2]
    _ = Real.sqrt (∫ x, p x ∂μ) * Real.sqrt (∫ x, q x ∂μ) := by
        rw [Real.sqrt_eq_rpow (∫ x, p x ∂μ), Real.sqrt_eq_rpow (∫ x, q x ∂μ)]

end Work.FTS.TransportS.TvUniform
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.DerivSliceEqFderiv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP.Levels

/-- For a two-variable function `F` differentiable at `(w, η)`, the derivative of the slice
`θ ↦ F w θ` at `η` is the Fréchet derivative at `(w, η)` applied to the direction `(0, 1)`. -/
theorem deriv_slice_eq_fderiv {F : ℝ → ℝ → ℝ} {w η : ℝ}
    (hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w, η)) :
    deriv (fun θ : ℝ => F w θ) η = fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w, η) (0, 1) := by
  -- The slice `θ ↦ F w θ` is the composite of `p ↦ F p.1 p.2` with the affine map
  -- `θ ↦ (w, θ)`, whose Fréchet derivative is `ContinuousLinearMap.inr ℝ ℝ ℝ`
  -- (the second-coordinate injection `1 ↦ (0, 1)`).
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w, η)) (w, η) := hd.hasFDerivAt
  have h2 : HasFDerivAt (fun θ : ℝ => (w, θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ) η :=
    hasFDerivAt_prodMk_right w η
  have h3 : HasFDerivAt (fun θ : ℝ => F w θ)
      ((fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w, η)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) η :=
    h1.comp η h2
  rw [(h3.hasDerivAt).deriv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

end Work.FTS.BSIdentP.Levels
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.HasDerivAtOddExtensionZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP.Levels

/-- If `g` is differentiable at `0` and `g 0 = 0`, then the odd extension
`θ ↦ if 0 ≤ θ then g θ else -g (-θ)` is differentiable at `0` with the same derivative. -/
theorem hasDerivAt_oddExtension_zero {g : ℝ → ℝ} {d : ℝ} (h0 : g 0 = 0)
    (hg : HasDerivAt g d 0) :
    HasDerivAt (fun θ : ℝ => if 0 ≤ θ then g θ else -g (-θ)) d 0 := by
  -- Write `F` for the odd extension and split `ℝ` into the two closed halves.
  set F : ℝ → ℝ := fun θ => if 0 ≤ θ then g θ else -g (-θ) with hF
  -- On `[0, ∞)` the odd extension agrees with `g`, hence has derivative `d` from the right.
  have hright : HasDerivWithinAt F d (Set.Ici 0) 0 := by
    refine (hg.hasDerivWithinAt).congr ?_ ?_
    · intro y hy
      exact ite_eq_left hy
    · simp [F]
  -- On `(-∞, 0]` it agrees with `θ ↦ -g (-θ)`, which has derivative `d` at `0`
  -- (chain rule with `θ ↦ -θ`, whose derivative is `-1`).
  have hleft : HasDerivWithinAt F d (Set.Iic 0) 0 := by
    have hg' : HasDerivAt g d (-(0 : ℝ)) := by simpa using hg
    have hgn : HasDerivAt (fun θ : ℝ => g (-θ)) (d * (-1)) 0 :=
      hg'.comp 0 (hasDerivAt_neg 0)
    have hG : HasDerivAt (fun θ : ℝ => -(g (-θ))) d 0 := by
      have h1 : HasDerivAt (fun θ : ℝ => -(g (-θ))) (-(d * (-1))) 0 := hgn.neg
      exact h1.congr_deriv (by ring)
    refine hG.hasDerivWithinAt.congr ?_ ?_
    · intro y hy
      have hy' : y ≤ 0 := hy
      rcases lt_or_eq_of_le hy' with hlt | heq
      · simp only [F]
        exact ite_eq_right (not_le.mpr hlt)
      · subst heq
        simp [F, h0]
    · simp [F, h0]
  -- Glue the two one-sided derivatives; they cover `ℝ`.
  have hunion : HasDerivWithinAt F d (Set.Ici (0 : ℝ) ∪ Set.Iic 0) 0 :=
    hright.union hleft
  have hU : Set.Ici (0 : ℝ) ∪ Set.Iic 0 = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_univ, iff_true]
    exact le_total 0 x
  rw [hU] at hunion
  exact hasDerivWithinAt_univ.mp hunion

end Work.FTS.BSIdentP.Levels
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.RhoMulRpowWeightLeTwo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP.Levels

/-- Elementary weighted decay bound: for `ρ ≥ 0`, `p, lam, b > 0` with `p * lam ≥ 2`,

`ρ * (1 + ρ^p / b)^(-lam) ≤ 2 * max 1 (b^lam) / (1 + ρ)`.

The two regimes are `ρ ≤ 1` (where the rpow factor is at most `1`) and `ρ ≥ 1`
(where `(1 + ρ^p/b)^(-lam) ≤ (ρ^p/b)^(-lam) = ρ^(-p*lam) * b^lam`, and
`ρ^(1 - p*lam) ≤ ρ^(-1)` because `p * lam ≥ 2`). -/
theorem rho_mul_rpow_weight_le_two {p lam b ρ : ℝ} (hp : 0 < p) (hlam : 0 < lam) (hb : 0 < b)
    (hρ : 0 ≤ ρ) (hpl : 2 ≤ p * lam) :
    ρ * (1 + ρ ^ p / b) ^ (-lam) ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
  have hM1 : (1 : ℝ) ≤ max 1 (b ^ lam) := le_max_left _ _
  have hMb : b ^ lam ≤ max 1 (b ^ lam) := le_max_right _ _
  have hMpos : (0 : ℝ) < max 1 (b ^ lam) := lt_of_lt_of_le one_pos hM1
  rcases lt_or_ge ρ 1 with hρ1 | hρ1
  · -- small `ρ`: the rpow factor is at most `1`
    have hbase : (1 : ℝ) ≤ 1 + ρ ^ p / b := by
      have : 0 ≤ ρ ^ p / b := div_nonneg (Real.rpow_nonneg hρ p) hb.le
      linarith
    have hpw : (1 + ρ ^ p / b) ^ (-lam) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_nonpos one_pos hbase (show -lam ≤ 0 by linarith)
      rwa [Real.one_rpow] at h
    have h1 : ρ * (1 + ρ ^ p / b) ^ (-lam) ≤ ρ := by
      simpa using mul_le_mul_of_nonneg_left hpw hρ
    have h2 : ρ ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 + ρ)]
      nlinarith [hρ, hρ1, hM1]
    linarith
  · -- large `ρ`: `(1 + ρ^p/b)^(-lam) ≤ (ρ^p/b)^(-lam) = ρ^(-p*lam) * b^lam`
    have hρpos : 0 < ρ := lt_of_lt_of_le one_pos hρ1
    have hspos : 0 < ρ ^ p / b := div_pos (Real.rpow_pos_of_pos hρpos p) hb
    have hbase2 : ρ ^ p / b ≤ 1 + ρ ^ p / b := by linarith
    have hpw : (1 + ρ ^ p / b) ^ (-lam) ≤ (ρ ^ p / b) ^ (-lam) :=
      Real.rpow_le_rpow_of_nonpos hspos hbase2 (show -lam ≤ 0 by linarith)
    have hA : (ρ ^ p / b) ^ (-lam) = ρ ^ (p * (-lam)) * b ^ lam := by
      rw [Real.div_rpow (Real.rpow_nonneg hρ p) hb.le, Real.rpow_neg hb.le,
          ← Real.rpow_mul hρ p (-lam)]
      rw [div_inv_eq_mul]
    have hcomb : ρ * ρ ^ (p * (-lam)) = ρ ^ (1 + p * (-lam)) := by
      rw [Real.rpow_add hρpos 1 (p * (-lam)), Real.rpow_one]
    have hexp : ρ ^ (1 + p * (-lam)) ≤ ρ ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hρ1 (by nlinarith [hpl])
    have hblam : 0 ≤ b ^ lam := (Real.rpow_pos_of_pos hb lam).le
    have hrhoinv : ρ ^ (-1 : ℝ) = ρ⁻¹ := by
      rw [Real.rpow_neg hρ 1, Real.rpow_one]
    have hfin : ρ * (1 + ρ ^ p / b) ^ (-lam) ≤ max 1 (b ^ lam) / ρ := by
      calc ρ * (1 + ρ ^ p / b) ^ (-lam)
          ≤ ρ * (ρ ^ p / b) ^ (-lam) := mul_le_mul_of_nonneg_left hpw hρ
        _ = ρ * ρ ^ (p * (-lam)) * b ^ lam := by rw [hA]; ring
        _ = ρ ^ (1 + p * (-lam)) * b ^ lam := by rw [hcomb]
        _ ≤ ρ ^ (-1 : ℝ) * max 1 (b ^ lam) :=
              mul_le_mul hexp hMb hblam (Real.rpow_nonneg hρ (-1))
        _ = max 1 (b ^ lam) / ρ := by rw [hrhoinv, div_eq_mul_inv]; ring
    have hlast : max 1 (b ^ lam) / ρ ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 + ρ)]
      rw [div_mul_eq_mul_div, div_le_iff₀ hρpos]
      nlinarith [hρ1, hMpos]
    linarith

end Work.FTS.BSIdentP.Levels
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxRegAux.abs_sub_mul_le_of_derivWithin_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.BoxRegAux

theorem abs_sub_mul_le_of_derivWithin_bound {u u' : ℝ → ℝ} {α β c C : ℝ}
    (hder : ∀ t ∈ Set.Icc α β, HasDerivWithinAt u (u' t) (Set.Icc α β) t)
    {x y : ℝ} (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β)
    (hb : ∀ t ∈ Set.uIcc x y, |u' t - c| ≤ C) :
    |u y - u x - (y - x) * c| ≤ C * |y - x| := by
  -- `uIcc x y ⊆ Icc α β`, so the derivative hypothesis restricts to the unordered interval
  have hsub : Set.uIcc x y ⊆ Set.Icc α β := Set.uIcc_subset_Icc hx hy
  -- apply the mean value theorem to `τ ↦ u τ - c * τ`, whose derivative is `u' t - c`
  have hf : ∀ t ∈ Set.uIcc x y,
      HasDerivWithinAt (fun τ : ℝ => u τ - τ * c) (u' t - c) (Set.uIcc x y) t := by
    intro t ht
    have h1 : HasDerivWithinAt u (u' t) (Set.uIcc x y) t := (hder t (hsub ht)).mono hsub
    have h2 : HasDerivWithinAt (fun τ : ℝ => τ * c) c (Set.uIcc x y) t := by
      simpa using ((hasDerivAt_id t).mul_const c).hasDerivWithinAt
    exact h1.sub h2
  have hbound : ∀ t ∈ Set.uIcc x y, ‖u' t - c‖ ≤ C := by
    intro t ht; rw [Real.norm_eq_abs]; exact hb t ht
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun τ : ℝ => u τ - τ * c) (f' := fun τ : ℝ => u' τ - c)
      (s := Set.uIcc x y) hf hbound (convex_uIcc x y) (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have hnorm : ‖(fun τ : ℝ => u τ - τ * c) y - (fun τ : ℝ => u τ - τ * c) x‖
      = |u y - u x - (y - x) * c| := by
    rw [Real.norm_eq_abs]; congr 1; ring
  rw [hnorm, Real.norm_eq_abs] at hmain
  exact hmain

end Work.FTS_EllLimOK.BoxRegAux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.FstarOde.not_integrableOn_of_rpow_lower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.FstarOde

theorem not_integrableOn_of_rpow_lower {f : ℝ → ℝ} {m b q : ℝ} (hm : 0 < m) (hb : 0 < b)
    (hq : q ≤ -1) (hlow : ∀ z ∈ Set.Ioo (0 : ℝ) b, m * z ^ q ≤ f z) :
    ¬ MeasureTheory.IntegrableOn f (Set.Ioo (0 : ℝ) b) := by
  -- `z ↦ z ^ q` is *not* integrable on `(0,b)` when `q ≤ -1`.
  intro hf
  have hmne : m ≠ 0 := ne_of_gt hm
  have hinv : 0 < (1 : ℝ) / m := by positivity
  have hnot : ¬ MeasureTheory.IntegrableOn (fun z : ℝ => z ^ q) (Set.Ioo (0 : ℝ) b) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hb]
    exact not_lt.mpr hq
  -- `f` dominates `m * z ^ q` on `(0,b)`, hence dominates `z ^ q` up to the positive
  -- constant `1/m`; a function dominated by an integrable one (and nonnegative) is integrable.
  apply hnot
  refine MeasureTheory.Integrable.mono' (g := fun z : ℝ => (1 / m) * f z) ?_ ?_ ?_
  · exact hf.const_mul (1 / m)
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    exact continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz.1))
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
    have hz0 : 0 < z := hz.1
    have hzq : 0 ≤ z ^ q := Real.rpow_nonneg (le_of_lt hz0) q
    rw [Real.norm_eq_abs, abs_of_nonneg hzq]
    calc z ^ q = (m⁻¹ * m) * z ^ q := by rw [inv_mul_cancel₀ hmne, one_mul]
      _ = (1 / m) * (m * z ^ q) := by ring
      _ ≤ (1 / m) * f z := mul_le_mul_of_nonneg_left (hlow z hz) (le_of_lt hinv)

end Work.FTS_EllLimOK.FstarOde
end
-- ===== merged: Submission.Work.FTS_EllLimOK.FstarOde.rigidity_form_of_ode =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.FstarOde

open scoped Real

/-- A function on `(0, ∞)` that is differentiable there with identically vanishing
derivative is constant.  (The open half-line `(0, ∞)` is open, connected and convex.) -/
private lemma exists_const_of_deriv_eq_zero {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hf' : ∀ z ∈ Set.Ioi (0 : ℝ), deriv f z = 0) :
    ∃ c : ℝ, ∀ z ∈ Set.Ioi (0 : ℝ), f z = c :=
  isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi hf hf'

theorem rigidity_form_of_ode (α : ℝ) (hα : 0 < α) {g : ℝ → ℝ}
    (hg1 : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt g (deriv g z) z)
    (hg2 : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (deriv g) (deriv (deriv g) z) z)
    (hode : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (deriv g) z + α * (5 + α) * z * deriv g z = 0) :
    ∃ A B : ℝ, ∀ z ∈ Set.Ioi (0 : ℝ), g z = A * z ^ (-(5 / α)) + B := by
  have hαne : α ≠ 0 := ne_of_gt hα
  set p : ℝ := (5 + α) / α with hp
  have hpα : α * p = 5 + α := by
    rw [hp]; field_simp
  -- ## Step 1: `z ↦ g'(z) z^p` is constant on `(0, ∞)`
  have hφdiff : DifferentiableOn ℝ (deriv g * fun z : ℝ => z ^ p) (Set.Ioi (0 : ℝ)) := by
    intro z hz
    have h2 : HasDerivAt (fun z : ℝ => z ^ p) (p * z ^ (p - 1)) z :=
      Real.hasDerivAt_rpow_const (x := z) (p := p) (Or.inl (ne_of_gt hz))
    exact ((hg2 z hz).differentiableAt.mul h2.differentiableAt).differentiableWithinAt
  have hφderiv : ∀ z ∈ Set.Ioi (0 : ℝ), deriv (deriv g * fun z : ℝ => z ^ p) z = 0 := by
    intro z hz
    have h2 : HasDerivAt (fun z : ℝ => z ^ p) (p * z ^ (p - 1)) z :=
      Real.hasDerivAt_rpow_const (x := z) (p := p) (Or.inl (ne_of_gt hz))
    have hd : HasDerivAt (deriv g * fun z : ℝ => z ^ p)
        (deriv (deriv g) z * z ^ p + deriv g z * (p * z ^ (p - 1))) z :=
      (hg2 z hz).mul h2
    rw [hd.deriv]
    -- the ODE, rewritten as `α z g'' + (5 + α) g' = 0`
    have hcore : α * z * deriv (deriv g) z + (5 + α) * deriv g z = 0 := by
      have h : (α * z) * (α * z * deriv (deriv g) z + (5 + α) * deriv g z) = 0 := by
        have heq : (α * z) * (α * z * deriv (deriv g) z + (5 + α) * deriv g z)
            = α ^ 2 * z ^ 2 * deriv (deriv g) z + α * (5 + α) * z * deriv g z := by
          ring
        rw [heq, hode z hz]
      exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (mul_pos hα hz))
    -- `z^p = z^(p-1) z`
    have hzp : z ^ p = z ^ (p - 1) * z := by
      have h := Real.rpow_add hz (p - 1) 1
      rw [Real.rpow_one] at h
      rwa [sub_add_cancel] at h
    have key1 : α * (deriv (deriv g) z * z ^ p + deriv g z * (p * z ^ (p - 1)))
        = z ^ (p - 1) * (α * z * deriv (deriv g) z + (α * p) * deriv g z) := by
      rw [hzp]; ring
    have key : α * (deriv (deriv g) z * z ^ p + deriv g z * (p * z ^ (p - 1)))
        = z ^ (p - 1) * (α * z * deriv (deriv g) z + (5 + α) * deriv g z) := by
      rw [key1, hpα]
    have hzero : α * (deriv (deriv g) z * z ^ p + deriv g z * (p * z ^ (p - 1))) = 0 := by
      rw [key, hcore, mul_zero]
    exact (mul_eq_zero.mp hzero).resolve_left hαne
  obtain ⟨c, hc⟩ := exists_const_of_deriv_eq_zero hφdiff hφderiv
  -- `c` is the value of `z ↦ g'(z) z^p`, whence `g'(z) = c z^{-p}`
  have hc' : ∀ z ∈ Set.Ioi (0 : ℝ), deriv g z * z ^ p = c := by
    intro z hz
    simpa only [Pi.mul_apply] using hc z hz
  -- ## Step 2: `z ↦ g z - A z^{-5/α}` is constant on `(0, ∞)`, with `A := -c α / 5`
  set A : ℝ := -(c * α) / 5 with hAdef
  have hAr : A * (-(5 / α)) = c := by
    rw [hAdef]; field_simp
  have hrp : -(5 / α) - 1 = -p := by
    rw [hp]; field_simp; ring
  have hHderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
      deriv (g - fun z : ℝ => A * z ^ (-(5 / α))) z = 0 := by
    intro z hz
    have h2 : HasDerivAt (fun z : ℝ => z ^ (-(5 / α))) ((-(5 / α)) * z ^ (-(5 / α) - 1)) z :=
      Real.hasDerivAt_rpow_const (x := z) (p := -(5 / α)) (Or.inl (ne_of_gt hz))
    have hd : HasDerivAt (g - fun z : ℝ => A * z ^ (-(5 / α)))
        (deriv g z - A * ((-(5 / α)) * z ^ (-(5 / α) - 1))) z :=
      (hg1 z hz).sub (h2.const_mul A)
    rw [hd.deriv]
    have hgz : deriv g z = c * z ^ (-p) := by
      have hzpow_ne : z ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hz p)
      have hcz : c * z ^ (-p) = c / z ^ p := by
        rw [Real.rpow_neg hz.le p, div_eq_mul_inv]
      rw [hcz, eq_div_iff hzpow_ne]
      exact hc' z hz
    rw [hgz, hrp]
    have : A * ((-(5 / α)) * z ^ (-p)) = (A * (-(5 / α))) * z ^ (-p) := by ring
    rw [this, hAr]
    ring
  have hHdiff : DifferentiableOn ℝ (g - fun z : ℝ => A * z ^ (-(5 / α))) (Set.Ioi (0 : ℝ)) := by
    intro z hz
    have h2 : HasDerivAt (fun z : ℝ => z ^ (-(5 / α))) ((-(5 / α)) * z ^ (-(5 / α) - 1)) z :=
      Real.hasDerivAt_rpow_const (x := z) (p := -(5 / α)) (Or.inl (ne_of_gt hz))
    have h1 : DifferentiableAt ℝ g z := (hg1 z hz).differentiableAt
    have h3 : DifferentiableAt ℝ (fun z : ℝ => A * z ^ (-(5 / α))) z :=
      (h2.const_mul A).differentiableAt
    exact (h1.sub h3).differentiableWithinAt
  obtain ⟨B, hB⟩ := exists_const_of_deriv_eq_zero hHdiff hHderiv
  refine ⟨A, B, fun z hz => ?_⟩
  have hBz : g z - A * z ^ (-(5 / α)) = B := by
    simpa only [Pi.sub_apply] using hB z hz
  linarith

end Work.FTS_EllLimOK.FstarOde
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Pinning.leftLimitOfBoundedDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.Pinning


end Work.FTS_EllLimOK.Pinning
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.CosTailDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real
open MeasureTheory Set

/-!
# Definitions for the second `cos`-weight tail estimate

The target estimate (`Work.FTS_EllLimOK.PkgJets.cosTailB`) is
`∫_0^T sin(2s)^{-η}/cos(s)^4 ds ≤ C (π/2 - T)^{-(3+η)}`, `η = 99/100`.

The proof splits at `π/4`; on `(0, π/4]` the integrand is dominated by a multiple of
`s^{-η}` (`ctA`), and in the reflected variable `w = π/2 - s` (also on `(0, π/4]`) by a
multiple of `w^{-(4+η)}` (`ctB`).
-/






/-! ### Elementary numeric facts -/


















end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.cosTailA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS_EllLimOK.PkgJets


end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.cos_inv_cube_mul_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

/-- Antiderivative computation: `∫_a^b sin t · cos²t dt = cos³a/3 - cos³b/3`. -/
theorem integral_sin_mul_cos_sq (a b : ℝ) (hab : a ≤ b) :
    ∫ t in a..b, Real.sin t * (Real.cos t) ^ 2
      = (Real.cos a) ^ 3 / 3 - (Real.cos b) ^ 3 / 3 := by
  have hcd : Continuous (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2) :=
    Real.continuous_sin.mul (Real.continuous_cos.pow 2)
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun s : ℝ => -((Real.cos s) ^ 3) / 3) (Real.sin x * (Real.cos x) ^ 2) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => (Real.cos s) ^ 3)
        (3 * (Real.cos x) ^ 2 * (-Real.sin x)) x := (Real.hasDerivAt_cos x).pow 3
    have h2 : HasDerivAt (fun s : ℝ => -((Real.cos s) ^ 3) / 3)
        (-(3 * (Real.cos x) ^ 2 * (-Real.sin x)) / 3) x := h1.neg.div_const 3
    convert h2 using 1
    ring
  have hint' : IntervalIntegrable (fun x : ℝ => Real.sin x * (Real.cos x) ^ 2)
      MeasureTheory.volume a b := hcd.intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint']
  ring

theorem cos_inv_cube_mul_integral_le {β θ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hθ : θ ∈ Set.Icc (Real.pi / 4) (Real.pi / 2)) :
    (Real.cos θ)⁻¹ ^ 3
        * ∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (Real.pi / 2 - t) ^ β
      ≤ 32 * (Real.pi / 2 - θ) ^ β := by
  have hle : θ ≤ Real.pi / 2 := hθ.2
  have hθpos : 0 ≤ θ := le_trans (by positivity) hθ.1
  have hcd : Continuous (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2) :=
    Real.continuous_sin.mul (Real.continuous_cos.pow 2)
  have hcont_pow : ContinuousOn (fun t : ℝ => (Real.pi / 2 - t) ^ β)
      (Set.uIcc θ (Real.pi / 2)) :=
    (continuous_const.sub continuous_id).continuousOn.rpow_const (fun _ _ => Or.inr hβ.le)
  have hint_f : IntervalIntegrable
      (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2 * (Real.pi / 2 - t) ^ β)
      MeasureTheory.volume θ (Real.pi / 2) :=
    ((hcd.continuousOn).mul hcont_pow).intervalIntegrable
  have hint_g : IntervalIntegrable
      (fun t : ℝ => (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2))
      MeasureTheory.volume θ (Real.pi / 2) :=
    (hcd.continuousOn.const_mul _).intervalIntegrable
  have hXnn : 0 ≤ (Real.pi / 2 - θ) ^ β := Real.rpow_nonneg (by linarith) β
  -- pointwise comparison of the integrands: `(π/2-t)^β ≤ (π/2-θ)^β` on `[θ, π/2]`
  have hpt : ∀ t ∈ Set.Icc θ (Real.pi / 2),
      Real.sin t * (Real.cos t) ^ 2 * (Real.pi / 2 - t) ^ β
        ≤ (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hθpos ht.1
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [ht.2, Real.pi_pos])
    have hb : 0 ≤ Real.sin t * (Real.cos t) ^ 2 := mul_nonneg hsin (sq_nonneg _)
    have hr : (Real.pi / 2 - t) ^ β ≤ (Real.pi / 2 - θ) ^ β :=
      Real.rpow_le_rpow (by linarith [ht.2]) (by linarith [ht.1]) hβ.le
    calc Real.sin t * (Real.cos t) ^ 2 * (Real.pi / 2 - t) ^ β
        ≤ (Real.sin t * (Real.cos t) ^ 2) * (Real.pi / 2 - θ) ^ β :=
          mul_le_mul_of_nonneg_left hr hb
      _ = (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2) := by ring
  have hmono := intervalIntegral.integral_mono_on hle hint_f hint_g hpt
  have hint_val : ∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2
      = (Real.cos θ) ^ 3 / 3 := by
    rw [integral_sin_mul_cos_sq θ (Real.pi / 2) hle, Real.cos_pi_div_two]
    ring
  have hI : ∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (Real.pi / 2 - t) ^ β
      ≤ (Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 / 3) := by
    rw [intervalIntegral.integral_const_mul, hint_val] at hmono
    exact hmono
  have hcosnn : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hle⟩
  have hcoef_nn : 0 ≤ (Real.cos θ)⁻¹ ^ 3 := pow_nonneg (inv_nonneg.mpr hcosnn) 3
  have hmain : (Real.cos θ)⁻¹ ^ 3 * ((Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 / 3))
      ≤ 32 * (Real.pi / 2 - θ) ^ β := by
    by_cases ha : Real.cos θ = 0
    · have h1 : (Real.cos θ)⁻¹ ^ 3 = 0 := by rw [ha, inv_zero]; norm_num
      rw [h1, zero_mul]
      exact mul_nonneg (by norm_num) hXnn
    · have h3 : (Real.cos θ)⁻¹ ^ 3 * ((Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 / 3))
          = (Real.pi / 2 - θ) ^ β / 3 := by
        rw [inv_pow]
        field_simp
      rw [h3]
      linarith [hXnn]
  exact (mul_le_mul_of_nonneg_left hI hcoef_nn).trans hmain

end Work.FTS_EllLimOK.ProducerH.BoxAux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.hasDerivWithinAt_of_tendsto_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.BoxAux


end Work.FTS_EllLimOK.ProducerH.BoxAux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.le_zero_of_hasDerivAt_nonneg_of_tendsto_nhdsLT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

/-- **A one-sided comparison principle.**

If `h` is differentiable on the open interval `(a,b)` with nonnegative derivative there, and
`h` tends to `c ≤ 0` as `x → b⁻`, then `h ≤ 0` on all of `(a,b)`.

Proof: `h` is monotone nondecreasing on `(a,b)` by the mean value theorem
(`monotoneOn_of_deriv_nonneg`, using `deriv h x = h' x ≥ 0`).  For a fixed `x < b` we may
therefore compare `h` with the constant `h x` along the filter `𝓝[Ioo x b] b` (nontrivial
because `x < b`), and pass to the limit `c`. -/
theorem le_zero_of_hasDerivAt_nonneg_of_tendsto_nhdsLT {a b c : ℝ} (hab : a < b)
    {h h' : ℝ → ℝ} (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt h (h' x) x)
    (hge : ∀ x ∈ Set.Ioo a b, 0 ≤ h' x)
    (hlim : Filter.Tendsto h (nhdsWithin b (Set.Iio b)) (nhds c)) (hc : c ≤ 0) :
    ∀ x ∈ Set.Ioo a b, h x ≤ 0 := by
  intro x hx
  have hxb : x < b := hx.2
  -- `h` is monotone nondecreasing on `(a,b)`.
  have hmono : MonotoneOn h (Set.Ioo a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo a b) ?_ ?_ ?_
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioo] at hy
      exact (hd y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ioo] at hy
      rw [(hd y hy).deriv]
      exact hge y hy
  -- the filter `𝓝[Ioo x b] b` is nontrivial, and `Ioo x b ⊆ Iio b`.
  have hne : Filter.NeBot (nhdsWithin b (Set.Ioo x b)) := right_nhdsWithin_Ioo_neBot hxb
  have htend : Filter.Tendsto h (nhdsWithin b (Set.Ioo x b)) (nhds c) :=
    hlim.mono_left (nhdsWithin_mono b Set.Ioo_subset_Iio_self)
  -- `h x ≤ h t` eventually as `t → b⁻`.
  have hle : ∀ᶠ t in nhdsWithin b (Set.Ioo x b), h x ≤ h t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hmono hx ⟨lt_trans hx.1 ht.1, ht.2⟩ (le_of_lt ht.1)
  have hxc : h x ≤ c :=
    le_of_tendsto_of_tendsto (b := nhdsWithin b (Set.Ioo x b)) (hb := hne)
      tendsto_const_nhds htend hle
  exact le_trans hxc hc

end Work.FTS_EllLimOK.ProducerH.BoxAux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.le_zero_of_hasDerivAt_nonpos_of_tendsto_nhdsGT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

/-- **One-sided maximum principle (left endpoint).**

If `h` is differentiable on the open interval `(a,b)` with derivative `h' ≤ 0` there, and if
`h` tends to some `c ≤ 0` at the left endpoint `a` (along `(a,b)`), then `h ≤ 0` on all of
`(a,b)`.  Indeed `h` is antitone on `(a,b)`, so `h x ≤ lim_{t→a⁺} h t = c` for every
`x ∈ (a,b)`.

The companion statement `le_zero_of_hasDerivAt_nonneg_of_tendsto_nhdsLT` is the mirrored
version at the right endpoint. -/
theorem le_zero_of_hasDerivAt_nonpos_of_tendsto_nhdsGT {a b c : ℝ} (hab : a < b)
    {h h' : ℝ → ℝ} (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt h (h' x) x)
    (hle : ∀ x ∈ Set.Ioo a b, h' x ≤ 0)
    (hlim : Filter.Tendsto h (nhdsWithin a (Set.Ioi a)) (nhds c)) (hc : c ≤ 0) :
    ∀ x ∈ Set.Ioo a b, h x ≤ 0 := by
  have _ : a < b := hab
  have hcont : ContinuousOn h (Set.Ioo a b) :=
    fun y hy => (hd y hy).continuousAt.continuousWithinAt
  -- `h` is antitone on `(a,b)`: its derivative there is `h' ≤ 0`.
  have hAnti : AntitoneOn h (Set.Ioo a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo a b) hcont ?_ ?_
    · intro y hy
      rw [interior_Ioo] at hy
      exact (hd y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ioo] at hy
      rw [(hd y hy).deriv]
      exact hle y hy
  intro x hx
  -- `h x` is a lower bound of `h` on a right-neighbourhood of `a`, hence `h x ≤ c`.
  have hxc : h x ≤ c := by
    refine ge_of_tendsto hlim ?_
    have h1 : Set.Iio x ∈ nhdsWithin a (Set.Ioi a) :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hx.1)
    filter_upwards [h1, self_mem_nhdsWithin] with t htx ht
    exact hAnti ⟨ht, lt_of_lt_of_le htx hx.2.le⟩ hx htx.le
  linarith

end Work.FTS_EllLimOK.ProducerH.BoxAux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2Ident =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK/ProducerH/BoxAux/th2Ident` — the closed form of `Φ = (S'' + 4S + G)`

For a function `S` of class `C²` on `(0, π/2)` whose second derivative solves the slice equation

`S'' = tan θ · S' + (cos θ)⁻² · S − 6 S − G`

one has, on `(0, π/2)`,

`(cos θ)^3 · (S''(θ) + 4 S(θ) + G(θ)) = ∫_θ^{π/2} sin t · (cos t)^2 · G(t) dt`.

## Proof

Write `Φ := S'' + 4S + G`.  The equation turns `Φ` into `Φ = tan θ · S' + ((cos θ)⁻² − 2)·S`, and the
elementary identity

`(cos^3 θ · (tan θ · S' + ((cos θ)⁻² − 2) · S))' = − sin θ · (cos θ)^2 · G θ`

holds on `(0, π/2)` (everything cancels except `− sin θ (cos θ)^2 G θ`, using the equation to eliminate
`S''`).  Since the whole expression is `O((cos θ)^3)` near `π/2` (here the hypothesis `|Φ| ≤ MW` is
used), the function `cos^3 θ · Φ(θ)` has the left limit `0` at `π/2`, and the fundamental theorem of
calculus (in the form `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto`) on `[θ, π/2]` gives
the claim.
-/

open scoped Topology
open MeasureTheory Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

theorem th2Ident {S G : ℝ → ℝ} {MG MW : ℝ}
    (hS : ContDiffOn ℝ 2 S (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hG : ContinuousOn G (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hGb : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |G t| ≤ MG)
    (hode : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (deriv S) θ
        = Real.tan θ * deriv S θ + ((Real.cos θ) ^ 2)⁻¹ * S θ - 6 * S θ - G θ)
    (hWb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv (deriv S) θ + 4 * S θ + G θ| ≤ MW) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Real.cos θ) ^ 3 * (deriv (deriv S) θ + 4 * S θ + G θ)
        = ∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t := by
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  -- ## Regularity of `S` and of `deriv S` on the open interval
  have hS1 : ContDiffOn ℝ 1 (deriv S) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h := hS.derivWithin (uniqueDiffOn_Ioo 0 (Real.pi / 2))
      (show (1 : WithTop ℕ∞) + 1 ≤ 2 from by norm_num)
    exact h.congr (fun x hx => (derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hx)).symm)
  have hdC : ContinuousOn (deriv S) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hS1.continuousOn
  have hSd : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt S (deriv S t) t := fun t ht =>
    (hS.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioo.mem_nhds ht)
  have hS2d : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv S) (deriv (deriv S) t) t := fun t ht =>
    (hS1.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioo.mem_nhds ht)
  -- ## The explicit primitive `F` of the integrand
  set F : ℝ → ℝ := fun u => Real.sin u * (Real.cos u)^2 * deriv S u
      + (Real.cos u - 2*(Real.cos u)^3) * S u with hF
  -- `F` agrees with `cos^3 θ · Φ(θ)` on the interval (this is the ODE)
  have hPF : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Real.cos t)^3 * (deriv (deriv S) t + 4*S t + G t) = F t := by
    intro t ht
    rw [hF]
    have hcos : Real.cos t ≠ 0 := by
      have h : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩
      exact ne_of_gt h
    rw [hode t ht, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  -- ## `F` has the desired derivative on the interval
  have hFderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt F (-(Real.sin t * (Real.cos t)^2 * G t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ => Real.sin u * (Real.cos u)^2 * deriv S u)
        ((Real.cos t ^ 3 - 2 * Real.sin t ^ 2 * Real.cos t) * deriv S t
          + Real.sin t * (Real.cos t)^2 * deriv (deriv S) t) t := by
      have ha : HasDerivAt (fun u : ℝ => Real.sin u) (Real.cos t) t := Real.hasDerivAt_sin t
      have hb : HasDerivAt (fun u : ℝ => Real.cos u ^ 2)
          (2 * Real.cos t^(2-1) * -Real.sin t) t := (Real.hasDerivAt_cos t).pow 2
      have hab : HasDerivAt (fun u : ℝ => Real.sin u * Real.cos u ^ 2)
          (Real.cos t ^ 3 - 2 * Real.sin t ^ 2 * Real.cos t) t := by
        have h := ha.mul hb
        convert h using 1
        simp only [Nat.reduceSub]
        ring
      exact hab.mul (hS2d t ht)
    have h2 : HasDerivAt (fun u : ℝ => (Real.cos u - 2 * Real.cos u ^ 3) * S u)
        ((-Real.sin t + 6 * Real.cos t ^ 2 * Real.sin t) * S t
          + (Real.cos t - 2 * Real.cos t ^ 3) * deriv S t) t := by
      have ha : HasDerivAt (fun u : ℝ => Real.cos u - 2 * Real.cos u ^ 3)
          (-Real.sin t + 6 * Real.cos t ^ 2 * Real.sin t) t := by
        have hc : HasDerivAt (fun u : ℝ => Real.cos u) (-Real.sin t) t := Real.hasDerivAt_cos t
        have hd : HasDerivAt (fun u : ℝ => Real.cos u ^ 3)
            (3 * Real.cos t^(3-1) * -Real.sin t) t := (Real.hasDerivAt_cos t).pow 3
        have h := hc.sub (hd.const_mul 2)
        convert h using 1
        simp only [Nat.reduceSub]
        ring
      exact ha.mul (hSd t ht)
    have hD : (Real.cos t ^ 3 - 2 * Real.sin t ^ 2 * Real.cos t) * deriv S t
          + Real.sin t * (Real.cos t)^2 * deriv (deriv S) t
          + ((-Real.sin t + 6 * Real.cos t ^ 2 * Real.sin t) * S t
              + (Real.cos t - 2 * Real.cos t ^ 3) * deriv S t)
        = -(Real.sin t * (Real.cos t)^2 * G t) := by
      have hcos : Real.cos t ≠ 0 := by
        have h : 0 < Real.cos t :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩
        exact ne_of_gt h
      have hsq : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
        linarith [Real.sin_sq_add_cos_sq t]
      rw [hode t ht, Real.tan_eq_sin_div_cos, hsq]
      field_simp
      ring_nf
      linear_combination (Real.cos t * deriv S t) * Real.sin_sq_add_cos_sq t
    have hsum := h1.add h2
    rw [hD] at hsum
    rw [hF]
    exact hsum
  -- ## Integrability of the integrand on `[θ, π/2]`
  have hint : IntervalIntegrable (fun t => -(Real.sin t * (Real.cos t)^2 * G t))
      volume θ (Real.pi/2) := by
    have hGae : AEMeasurable G (volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))) :=
      hG.aemeasurable measurableSet_Ioo
    have hmono : volume.restrict (Set.Ioo θ (Real.pi/2))
        ≤ volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      Measure.restrict_mono (s := Set.Ioo θ (Real.pi/2))
        (s' := Set.Ioo (0:ℝ) (Real.pi/2)) (μ := volume) (ν := volume)
        (fun x hx => ⟨lt_trans hθ0 hx.1, hx.2⟩) le_rfl
    have hGae' : AEMeasurable G (volume.restrict (Set.Ioo θ (Real.pi/2))) :=
      hGae.mono_measure hmono
    have hcae : AEMeasurable (fun t : ℝ => Real.sin t * (Real.cos t)^2)
        (volume.restrict (Set.Ioo θ (Real.pi/2))) :=
      (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).aemeasurable
    have hmeas : AEStronglyMeasurable (fun t : ℝ => -(Real.sin t * (Real.cos t)^2 * G t))
        (volume.restrict (Set.Ioo θ (Real.pi/2))) :=
      ((hcae.mul hGae').neg).aestronglyMeasurable
    have hbdd : ∀ᶠ t in ae (volume.restrict (Set.Ioo θ (Real.pi/2))),
        ‖-(Real.sin t * (Real.cos t)^2 * G t)‖ ≤ MG := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have hGt : |G t| ≤ MG := hGb t ⟨lt_trans hθ0 ht.1, ht.2⟩
      have hcos2 : |(Real.cos t)^2| ≤ 1 := by
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one t)
      rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul]
      calc |Real.sin t| * |(Real.cos t)^2| * |G t| ≤ 1 * 1 * |G t| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (Real.abs_sin_le_one t) hcos2 (abs_nonneg _) zero_le_one) (abs_nonneg _)
        _ = |G t| := by ring
        _ ≤ MG := hGt
    have hIoo : IntegrableOn (fun t : ℝ => -(Real.sin t * (Real.cos t)^2 * G t))
        (Set.Ioo θ (Real.pi/2)) volume :=
      MeasureTheory.IntegrableOn.of_bound (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
        hmeas MG hbdd
    refine ⟨?_, ?_⟩
    · exact IntegrableOn.congr_set_ae hIoo (MeasureTheory.Ioo_ae_eq_Ioc.symm)
    · rw [Set.Ioc_eq_empty_of_le (le_of_lt hθ1)]
      exact MeasureTheory.integrableOn_empty
  -- ## The left limit of `F` at `π/2` is `0`
  have hmem : Set.Ioo (0:ℝ) (Real.pi/2) ∈ 𝓝[<] (Real.pi/2) := by
    have h1 : Set.Ioi (0:ℝ) ∈ 𝓝[<] (Real.pi/2) :=
      nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds Real.pi_div_two_pos)
    have h2 : Set.Iio (Real.pi/2) ∈ 𝓝[<] (Real.pi/2) := self_mem_nhdsWithin
    have h3 : Set.Ioi (0:ℝ) ∩ Set.Iio (Real.pi/2) ∈ 𝓝[<] (Real.pi/2) := Filter.inter_mem h1 h2
    have hinter : Set.Ioi (0:ℝ) ∩ Set.Iio (Real.pi/2) = Set.Ioo (0:ℝ) (Real.pi/2) := by
      ext x; exact Iff.rfl
    rwa [hinter] at h3
  have hEvF : F =ᶠ[𝓝[<] (Real.pi/2)]
      (fun t => (Real.cos t)^3 * (deriv (deriv S) t + 4*S t + G t)) := by
    filter_upwards [hmem] with t ht
    rw [hF]
    exact (hPF t ht).symm
  have hzero : Tendsto (fun t : ℝ => (Real.cos t)^3 * MW) (𝓝[<] (Real.pi/2)) (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => Real.cos t) (𝓝[<] (Real.pi/2))
        (𝓝 (Real.cos (Real.pi/2))) :=
      Real.continuous_cos.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [Real.cos_pi_div_two] at hc
    have hc3 : Tendsto (fun t : ℝ => (Real.cos t)^3) (𝓝[<] (Real.pi/2)) (𝓝 0) := by
      simpa using hc.pow 3
    simpa using hc3.mul_const MW
  have hboundF : ∀ᶠ t in 𝓝[<] (Real.pi/2), ‖F t‖ ≤ (Real.cos t)^3 * MW := by
    filter_upwards [hmem] with t ht
    have hΦ : |deriv (deriv S) t + 4*S t + G t| ≤ MW := hWb t ht
    have hcos0 : 0 ≤ (Real.cos t)^3 := by
      have h : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩
      positivity
    rw [← hPF t ht, Real.norm_eq_abs, abs_mul, abs_of_nonneg hcos0]
    exact mul_le_mul_of_nonneg_left hΦ hcos0
  have htend_pi : Tendsto F (𝓝[<] (Real.pi/2)) (𝓝 0) := by
    have hnorm : Tendsto (fun t : ℝ => ‖F t‖) (𝓝[<] (Real.pi/2)) (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
        (by filter_upwards with t; exact norm_nonneg _) hboundF
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  -- ## The right limit of `F` at `θ` is `F θ` (continuity)
  have hcd : ContinuousAt (deriv S) θ := hdC.continuousAt (isOpen_Ioo.mem_nhds hθ)
  have hcs : ContinuousAt S θ := hS.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hθ)
  have hcontF : ContinuousAt F θ := by
    rw [hF]
    fun_prop
  have htend_θ : Tendsto F (𝓝[>] θ) (𝓝 (F θ)) :=
    hcontF.tendsto.mono_left nhdsWithin_le_nhds
  -- ## The fundamental theorem of calculus
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (f := F)
    (f' := fun t => -(Real.sin t * (Real.cos t)^2 * G t)) hθ1
    (fun t ht => hFderiv t ⟨lt_trans hθ0 ht.1, ht.2⟩) hint htend_θ htend_pi
  rw [intervalIntegral.integral_neg, zero_sub] at hFTC
  have hInt : (∫ t in θ..(Real.pi/2), Real.sin t * (Real.cos t)^2 * G t) = F θ := by
    linarith
  rw [hInt]
  rw [hF]
  exact hPF θ hθ

end Work.FTS_EllLimOK.ProducerH.BoxAux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.abs_sub_le_of_deriv_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

theorem abs_sub_le_of_deriv_abs_le {f : ℝ → ℝ} {L C : ℝ}
    (hC : ContDiffOn ℝ 1 f (Set.Ioo 0 L))
    (h : ∀ t ∈ Set.Ioo 0 L, |deriv f t| ≤ C) :
    ∀ s ∈ Set.Ioo 0 L, ∀ t ∈ Set.Ioo 0 L, |f s - f t| ≤ C * |s - t| := by
  intro s hs t ht
  -- `f` is differentiable on the open interval, with derivative `deriv f`.
  have hdiff : ∀ x ∈ Set.Ioo (0 : ℝ) L, DifferentiableAt ℝ f x := by
    intro x hx
    exact (hC.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hbound : ∀ x ∈ Set.Ioo (0 : ℝ) L, ‖deriv f x‖ ≤ C := by
    intro x hx
    simpa [Real.norm_eq_abs] using h x hx
  -- Mean value inequality on the convex set `Ioo 0 L`.
  have := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Ioo 0 L) ht hs
  simpa [Real.norm_eq_abs] using this

end Work.FTS_EllLimOK.ProducerH.H2
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.sinCosSqInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS_EllLimOK.ProducerH.H2

theorem sinCosSqInt {F : ℝ → ℝ} {x C : ℝ}
    (hc : ContinuousOn F (Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ t ∈ Set.Ioo 0 (Real.pi / 2), |F t| ≤ C)
    (hx : 0 < x) (hx2 : x ≤ Real.pi / 2) :
    IntervalIntegrable (fun t => Real.sin t * (Real.cos t) ^ 2 * F t) volume x (Real.pi / 2) := by
  -- The only singular point of the integrand would be the endpoint `π / 2`, where `cos` vanishes;
  -- the (global) factor `cos²` kills it, and the complement of the open interval is null.
  have hsub : Set.Ioo x (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    Set.Ioo_subset_Ioo_left (le_of_lt hx)
  have hcont : ContinuousOn (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2 * F t)
      (Set.Ioo x (Real.pi / 2)) :=
    ((Real.continuous_sin.continuousOn.mul (Real.continuous_cos.continuousOn.pow 2))).mul
      (hc.mono hsub)
  -- It suffices to prove integrability on the open interval `(x, π/2)`.
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hx2]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioo_lt_top ?_ C ?_
  · exact hcont.aestronglyMeasurable measurableSet_Ioo
  · -- Pointwise bound: `|sin t| ≤ 1`, `|cos t|² ≤ 1`, and `|F t| ≤ C` on the open interval.
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo ?_
    intro t ht
    have ht' : t ∈ Set.Ioo 0 (Real.pi / 2) := hsub ht
    have hFt : |F t| ≤ C := hb t ht'
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    calc |Real.sin t| * |Real.cos t| ^ 2 * |F t|
        ≤ 1 * 1 * |F t| := by
          gcongr
          · exact Real.abs_sin_le_one t
          · exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one t)
      _ = |F t| := by ring
      _ ≤ C := hFt

end Work.FTS_EllLimOK.ProducerH.H2
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.wRateArithAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

/-- For `0 < β ≤ 1` and `0 ≤ d ≤ δ`: `δ^(β-1) * d ≤ d^β`. -/
theorem rpow_sub_one_mul_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {δ d : ℝ} (hd0 : 0 ≤ d)
    (hdδ : d ≤ δ) : δ ^ (β - 1) * d ≤ d ^ β := by
  rcases lt_or_eq_of_le hd0 with hd | hd
  · have hδ : 0 < δ := lt_of_lt_of_le hd hdδ
    have h1 : 1 ≤ δ / d := (one_le_div hd).mpr hdδ
    have h2 : (δ / d) ^ (β - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have hd1 : d ^ β = d ^ (β - 1) * d := by
      have h := Real.rpow_add hd (β - 1) 1
      rw [show β - 1 + 1 = β by ring, Real.rpow_one] at h
      exact h
    have hdne : d ^ (β - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hd (β - 1))
    have hinner : (d ^ (β - 1))⁻¹ * (d ^ (β - 1) * d) = d := by
      rw [← mul_assoc, inv_mul_cancel₀ hdne, one_mul]
    have h3 : (δ / d) ^ (β - 1) * d ^ β = δ ^ (β - 1) * d := by
      calc (δ / d) ^ (β - 1) * d ^ β
          = (δ ^ (β - 1) * (d ^ (β - 1))⁻¹) * (d ^ (β - 1) * d) := by
            rw [Real.div_rpow (le_of_lt hδ) (le_of_lt hd), hd1, div_eq_mul_inv]
        _ = δ ^ (β - 1) * ((d ^ (β - 1))⁻¹ * (d ^ (β - 1) * d)) := by rw [mul_assoc]
        _ = δ ^ (β - 1) * d := by rw [hinner]
    rw [← h3]
    calc (δ / d) ^ (β - 1) * d ^ β ≤ 1 * d ^ β :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hd0 β)
      _ = d ^ β := one_mul _
  · rw [← hd, mul_zero, Real.zero_rpow (ne_of_gt hβ)]

/-- The purely arithmetic core of the modulus estimate. -/
theorem wRateArithAux {F F' c c' δ δ' d L β : ℝ} (hL : 0 ≤ L)
    (hc' : 0 < c') (hcc : c' ≤ c)
    (hδ' : 0 ≤ δ') (hδδ : δ' ≤ δ) (hδ : 0 < δ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hcos : 2 / Real.pi * δ ≤ c)
    (hsub : c - c' ≤ d) (hdδ : d ≤ δ)
    (hF : |F - F'| ≤ L * δ ^ β * (c ^ 3 - c' ^ 3) / 3)
    (hF' : |F'| ≤ L * δ' ^ β * c' ^ 3 / 3) :
    |(c ^ 3)⁻¹ * F - (c' ^ 3)⁻¹ * F'| ≤ 4 * L * d ^ β := by
  have hc : 0 < c := lt_of_lt_of_le hc' hcc
  have hcoef : 0 ≤ (c' ^ 3)⁻¹ - (c ^ 3)⁻¹ := by
    have hle : c' ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ (le_of_lt hc') hcc 3
    exact sub_nonneg.mpr (inv_anti₀ (by positivity) hle)
  have hdec : |(c ^ 3)⁻¹ * F - (c' ^ 3)⁻¹ * F'|
      ≤ (c ^ 3)⁻¹ * |F - F'| + ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * |F'| := by
    have h1 : (c ^ 3)⁻¹ * F - (c' ^ 3)⁻¹ * F'
        = (c ^ 3)⁻¹ * (F - F') + (-(((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F')) := by ring
    rw [h1]
    have h2 : |(c ^ 3)⁻¹ * (F - F')| ≤ (c ^ 3)⁻¹ * |F - F'| := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ c ^ 3))]
    have h3 : |((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F'| ≤ ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * |F'| := by
      rw [abs_mul, abs_of_nonneg hcoef]
    have hstep : |(c ^ 3)⁻¹ * (F - F') + (-(((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F'))|
        ≤ |(c ^ 3)⁻¹ * (F - F')| + |((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F'| := by
      have hh := abs_add_le ((c ^ 3)⁻¹ * (F - F')) (-(((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F'))
      rwa [abs_neg] at hh
    calc |(c ^ 3)⁻¹ * (F - F') + (-(((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F'))|
        ≤ |(c ^ 3)⁻¹ * (F - F')| + |((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * F'| := hstep
      _ ≤ (c ^ 3)⁻¹ * |F - F'| + ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * |F'| := add_le_add h2 h3
  have hb1 : (c ^ 3)⁻¹ * |F - F'| ≤ (c ^ 3)⁻¹ * (L * δ ^ β * (c ^ 3 - c' ^ 3) / 3) :=
    mul_le_mul_of_nonneg_left hF (by positivity)
  have hb2 : ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * |F'|
      ≤ ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * (L * δ' ^ β * c' ^ 3 / 3) :=
    mul_le_mul_of_nonneg_left hF' hcoef
  have hcomb : (c ^ 3)⁻¹ * (L * δ ^ β * (c ^ 3 - c' ^ 3) / 3)
      + ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * (L * δ' ^ β * c' ^ 3 / 3)
      = (L / 3) * (δ ^ β + δ' ^ β) * (1 - (c' / c) ^ 3) := by
    field_simp
  have hA1 : δ ^ β + δ' ^ β ≤ 2 * δ ^ β := by
    have := Real.rpow_le_rpow hδ' hδδ hβ.le
    linarith
  have hA2 : 0 ≤ 1 - (c' / c) ^ 3 := by
    have hr0 : 0 ≤ c' / c := div_nonneg (le_of_lt hc') (le_of_lt hc)
    have hr : c' / c ≤ 1 := (div_le_one hc).mpr hcc
    have h : (c' / c) ^ 3 ≤ 1 := pow_le_one₀ hr0 hr
    linarith
  have hA3 : 1 - (c' / c) ^ 3 ≤ 3 * (c - c') / c := by
    have h1 : 1 - (c' / c) ^ 3 = (c ^ 3 - c' ^ 3) / c ^ 3 := by
      rw [div_pow]
      field_simp
    rw [h1]
    have h2 : c ^ 3 - c' ^ 3 ≤ 3 * (c - c') * c ^ 2 := by
      nlinarith [hcc, hc.le, hc'.le, mul_nonneg (le_of_lt hc') (sq_nonneg (c - c')),
        pow_nonneg (sub_nonneg.mpr hcc) 3]
    calc (c ^ 3 - c' ^ 3) / c ^ 3 ≤ (3 * (c - c') * c ^ 2) / c ^ 3 :=
          div_le_div_of_nonneg_right h2 (by positivity)
      _ = 3 * (c - c') / c := by field_simp
  have hd0 : 0 ≤ d := le_trans (sub_nonneg.mpr hcc) hsub
  have h6 : δ ^ β / δ = δ ^ (β - 1) := by
    have h := Real.rpow_sub hδ β 1
    rw [Real.rpow_one] at h
    exact h.symm
  have hrp : δ ^ β / c ≤ (Real.pi / 2) * δ ^ (β - 1) := by
    have h1 : 1 / c ≤ Real.pi / (2 * δ) := by
      have h2 : 1 / c ≤ 1 / (2 / Real.pi * δ) := one_div_le_one_div_of_le (by positivity) hcos
      have h3 : 1 / (2 / Real.pi * δ) = Real.pi / (2 * δ) := by field_simp
      rwa [h3] at h2
    have h4 : δ ^ β / c ≤ δ ^ β * (Real.pi / (2 * δ)) := by
      have h4' := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (le_of_lt hδ) β)
      rwa [mul_one_div] at h4'
    have h5 : δ ^ β * (Real.pi / (2 * δ)) = (Real.pi / 2) * δ ^ (β - 1) := by
      rw [show δ ^ β * (Real.pi / (2 * δ)) = Real.pi / 2 * (δ ^ β / δ) by field_simp, h6]
    rwa [h5] at h4
  calc |(c ^ 3)⁻¹ * F - (c' ^ 3)⁻¹ * F'|
      ≤ (c ^ 3)⁻¹ * |F - F'| + ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * |F'| := hdec
    _ ≤ (c ^ 3)⁻¹ * (L * δ ^ β * (c ^ 3 - c' ^ 3) / 3)
        + ((c' ^ 3)⁻¹ - (c ^ 3)⁻¹) * (L * δ' ^ β * c' ^ 3 / 3) := add_le_add hb1 hb2
    _ = (L / 3) * (δ ^ β + δ' ^ β) * (1 - (c' / c) ^ 3) := hcomb
    _ ≤ (L / 3) * (2 * δ ^ β) * (1 - (c' / c) ^ 3) := by
        have hL3 : 0 ≤ L / 3 := by positivity
        have := mul_le_mul_of_nonneg_left hA1 hL3
        exact mul_le_mul_of_nonneg_right this hA2
    _ ≤ (L / 3) * (2 * δ ^ β) * (3 * d / c) := by
        have h1 : 1 - (c' / c) ^ 3 ≤ 3 * d / c := by
          refine hA3.trans ?_
          exact div_le_div_of_nonneg_right (by linarith [hsub]) (le_of_lt hc)
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * L * (δ ^ β / c) * d := by ring
    _ ≤ 2 * L * ((Real.pi / 2) * δ ^ (β - 1)) * d := by
        have h2 : (0 : ℝ) ≤ 2 * L := by linarith
        have := mul_le_mul_of_nonneg_left hrp h2
        exact mul_le_mul_of_nonneg_right this hd0
    _ = Real.pi * L * (δ ^ (β - 1) * d) := by ring
    _ ≤ Real.pi * L * d ^ β := mul_le_mul_of_nonneg_left
        (rpow_sub_one_mul_le hβ hβ1 hd0 hdδ) (by positivity)
    _ ≤ 4 * L * d ^ β := by
        have h3 : (0 : ℝ) ≤ L * d ^ β := mul_nonneg hL (Real.rpow_nonneg hd0 β)
        have hp := Real.pi_lt_four
        nlinarith

end Work.FTS_EllLimOK.ProducerH.H2
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.SliceBound.mode_contradiction_down =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

set_option linter.unusedVariables false

namespace Work.FTS_EllLimOK.ProducerH.SliceBound

theorem mode_contradiction_down {V : ℝ → ℝ} {M Z₀ θ₀ : ℝ}
    (hM : 0 ≤ M) (hθ₀ : θ₀ ∈ Set.Ioo 0 (π / 2)) (hZ₀ : Z₀ < 0)
    (hanti : ∀ θ ∈ Set.Ioo 0 (π / 2), θ₀ ≤ θ →
      3 * V θ * Real.cos θ + M * (Real.cos θ) ^ 3 ≤ Z₀)
    (hfl : ∀ θ ∈ Set.Ioo 0 (π / 2), -M - 2 * M * (Real.cos θ) ^ 2 ≤ V θ) :
    False := by
  have hlt : θ₀ < π / 2 := hθ₀.2
  -- Pointwise bound on the half-open interval `[θ₀, π/2) ∩ (0, π/2)`.
  have hbound : ∀ θ ∈ Set.Ioo 0 (π / 2), θ₀ ≤ θ →
      -3 * M * Real.cos θ - 5 * M * (Real.cos θ) ^ 3 ≤ Z₀ := by
    intro θ hθ hθ0
    have hcpos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    have h1 : 3 * (-M - 2 * M * (Real.cos θ) ^ 2) * Real.cos θ
        ≤ 3 * V θ * Real.cos θ := by
      have h3 : (0 : ℝ) ≤ 3 * Real.cos θ := by linarith
      have hmul := mul_le_mul_of_nonneg_right (hfl θ hθ) h3
      nlinarith [hmul]
    have h2 := hanti θ hθ hθ0
    nlinarith [h1, h2]
  -- The auxiliary function tends to `0` at the right endpoint.
  have hcont : Continuous fun θ : ℝ => -3 * M * Real.cos θ - 5 * M * (Real.cos θ) ^ 3 := by
    fun_prop
  have hne : (𝓝[Set.Ioo θ₀ (π / 2)] (π / 2)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (ne_of_lt hlt)]
    exact ⟨le_of_lt hlt, le_refl _⟩
  have hlim : Filter.Tendsto (fun θ : ℝ => -3 * M * Real.cos θ - 5 * M * (Real.cos θ) ^ 3)
      (𝓝[Set.Ioo θ₀ (π / 2)] (π / 2)) (𝓝 0) := by
    have h := (hcont.tendsto (π / 2)).mono_left
      (nhdsWithin_le_nhds (a := π / 2) (s := Set.Ioo θ₀ (π / 2)))
    simpa [Real.cos_pi_div_two] using h
  have hev : ∀ᶠ θ in 𝓝[Set.Ioo θ₀ (π / 2)] (π / 2),
      -3 * M * Real.cos θ - 5 * M * (Real.cos θ) ^ 3 ≤ Z₀ := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact hbound θ ⟨by linarith [hθ.1, hθ₀.1], hθ.2⟩ (le_of_lt hθ.1)
  have h0 : (0 : ℝ) ≤ Z₀ := le_of_tendsto (hx := hne) hlim hev
  linarith [hZ₀]

end Work.FTS_EllLimOK.ProducerH.SliceBound
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.SliceBound.mode_contradiction_up =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `π` is the scoped notation for `Real.pi`; without this line the identifier `π` is
-- unknown (the workspace sets `autoImplicit = false`), so the statement itself does
-- not elaborate.
open scoped Real

namespace Work.FTS_EllLimOK.ProducerH.SliceBound

/-- Upper mode contradiction: the two-sided pointwise bounds
`Z₀ ≤ 3 V θ cos θ - M cos³θ` (for `θ ≥ θ₀`) and `V θ ≤ M + 2M cos²θ` are incompatible
with `Z₀ > 0` when `θ₀ < π/2`, because letting `θ → π/2⁻` forces `Z₀ ≤ 0`.

Indeed, multiplying the second bound by `3 cos θ ≥ 0` and inserting it into the first
gives `Z₀ ≤ M cos θ (3 + 5 cos²θ)` for every `θ ∈ (θ₀, π/2)`; the right-hand side tends
to `0` as `θ → π/2` (continuity of `cos`), so `Z₀ ≤ 0`. -/
theorem mode_contradiction_up {V : ℝ → ℝ} {M Z₀ θ₀ : ℝ}
    (hM : 0 ≤ M) (hθ₀ : θ₀ ∈ Set.Ioo 0 (π / 2)) (hZ₀ : 0 < Z₀)
    (hmono : ∀ θ ∈ Set.Ioo 0 (π / 2), θ₀ ≤ θ →
      Z₀ ≤ 3 * V θ * Real.cos θ - M * (Real.cos θ) ^ 3)
    (hfu : ∀ θ ∈ Set.Ioo 0 (π / 2), V θ ≤ M + 2 * M * (Real.cos θ) ^ 2) :
    False := by
  -- Pointwise reduction to the single bound `Z₀ ≤ M cos θ (3 + 5 cos²θ)`.
  have key : ∀ θ ∈ Set.Ioo 0 (π / 2), θ₀ ≤ θ →
      Z₀ ≤ M * Real.cos θ * (3 + 5 * (Real.cos θ) ^ 2) := by
    intro θ hθ hge
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have h1 := hmono θ hθ hge
    have h2 := hfu θ hθ
    have h3 : 3 * V θ * Real.cos θ ≤ 3 * (M + 2 * M * (Real.cos θ) ^ 2) * Real.cos θ := by
      nlinarith [mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ 3 * Real.cos θ)]
    nlinarith [h1, h3]
  -- The right-hand side is continuous and vanishes at `π/2`.
  have hcont : Continuous (fun θ : ℝ => M * Real.cos θ * (3 + 5 * (Real.cos θ) ^ 2)) := by
    fun_prop
  have h0 : M * Real.cos (π / 2) * (3 + 5 * (Real.cos (π / 2)) ^ 2) = 0 := by
    rw [Real.cos_pi_div_two]; ring
  -- Hence it is `< Z₀` on a left-neighbourhood of `π/2`.
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuousAt_iff.mp (hcont.continuousAt (x := π / 2)) Z₀ hZ₀
  -- Pick `θ = π/2 - γ` in `(θ₀, π/2)` and inside that neighbourhood.
  set γ : ℝ := min (δ / 2) ((π / 2 - θ₀) / 2) with hγdef
  have hγpos : 0 < γ := lt_min (by linarith [hδpos]) (by linarith [hθ₀.2])
  have hγle : γ ≤ (π / 2 - θ₀) / 2 := min_le_right _ _
  have hγlt : γ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith [hδpos])
  set θ : ℝ := π / 2 - γ with hθdef
  have hθmem : θ ∈ Set.Ioo 0 (π / 2) := by
    refine ⟨?_, ?_⟩
    · rw [hθdef]; linarith [hγle, hθ₀.1]
    · rw [hθdef]; linarith [hγpos]
  have hθge : θ₀ ≤ θ := by rw [hθdef]; linarith [hγle]
  have hdist : dist θ (π / 2) < δ := by
    rw [Real.dist_eq, hθdef]
    have : π / 2 - γ - π / 2 = -γ := by ring
    rw [this, abs_neg, abs_of_pos hγpos]
    exact hγlt
  have hFlt : M * Real.cos θ * (3 + 5 * (Real.cos θ) ^ 2) < Z₀ := by
    have h := hδ (x := θ) hdist
    simp only [Real.dist_eq, h0, sub_zero] at h
    exact (abs_lt.mp h).2
  linarith [key θ hθmem hθge, hFlt]

end Work.FTS_EllLimOK.ProducerH.SliceBound
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.ThetaZero.tendsto_of_deriv_bounded =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology NNReal
open Filter Set Metric

namespace Work.FTS_EllLimOK.ProducerH.ThetaZero

/-- A function which is Lipschitz on the open interval `(a,b)` has a limit at `a` from the
right.  (This is the "cluster set at `a` is a single point" argument, phrased through Cauchy
filters and completeness of `ℝ`.) -/
private lemma exists_tendsto_nhdsGT_of_lipschitzOn {f : ℝ → ℝ} {a b : ℝ} {C : ℝ≥0}
    (hab : a < b) (hL : LipschitzOnWith C f (Ioo a b)) :
    ∃ L : ℝ, Tendsto f (𝓝[>] a) (𝓝 L) := by
  rw [← cauchy_map_iff_exists_tendsto]
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, ?_⟩
  intro ε hε
  set δ : ℝ := ε / (2 * ((C : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; exact div_pos hε (by positivity)
  have hCpos : (0 : ℝ) < (C : ℝ) + 1 := by positivity
  have hac : a < min b (a + δ) := lt_min hab (lt_add_of_pos_right a hδ)
  refine ⟨f '' Ioo a (min b (a + δ)), image_mem_map (Ioo_mem_nhdsGT hac), ?_⟩
  intro x hx y hy
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  have hpb : p ∈ Ioo a b := ⟨hp.1, lt_of_lt_of_le hp.2 (min_le_left _ _)⟩
  have hqb : q ∈ Ioo a b := ⟨hq.1, lt_of_lt_of_le hq.2 (min_le_left _ _)⟩
  have h1 : dist (f p) (f q) ≤ (C : ℝ) * dist p q := hL.dist_le_mul p hpb q hqb
  have h2 : dist p q ≤ δ := by
    rw [Real.dist_eq]
    have hlt : |p - q| < min b (a + δ) - a := by
      rw [abs_lt]
      constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
    have hle : min b (a + δ) - a ≤ δ := by linarith [min_le_right b (a + δ)]
    linarith
  have h3 : (C : ℝ) * dist p q ≤ (C : ℝ) * δ :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : (C : ℝ) * δ < ε := by
    have hδnn : 0 ≤ δ := le_of_lt hδ
    have h5 : (C : ℝ) * δ ≤ ((C : ℝ) + 1) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδnn
    have h6 : ((C : ℝ) + 1) * δ = ε / 2 := by
      rw [hδdef]; field_simp
    linarith
  linarith

/-- A function which is Lipschitz on the open interval `(a,b)` has a limit at `b` from the
left (the mirror image of the previous lemma). -/
private lemma exists_tendsto_nhdsLT_of_lipschitzOn {f : ℝ → ℝ} {a b : ℝ} {C : ℝ≥0}
    (hab : a < b) (hL : LipschitzOnWith C f (Ioo a b)) :
    ∃ R : ℝ, Tendsto f (𝓝[<] b) (𝓝 R) := by
  rw [← cauchy_map_iff_exists_tendsto]
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, ?_⟩
  intro ε hε
  set δ : ℝ := ε / (2 * ((C : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; exact div_pos hε (by positivity)
  have hCpos : (0 : ℝ) < (C : ℝ) + 1 := by positivity
  have hcb : max a (b - δ) < b := max_lt hab (by linarith)
  refine ⟨f '' Ioo (max a (b - δ)) b, image_mem_map (Ioo_mem_nhdsLT hcb), ?_⟩
  intro x hx y hy
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  have hpb : p ∈ Ioo a b := ⟨lt_of_le_of_lt (le_max_left _ _) hp.1, hp.2⟩
  have hqb : q ∈ Ioo a b := ⟨lt_of_le_of_lt (le_max_left _ _) hq.1, hq.2⟩
  have h1 : dist (f p) (f q) ≤ (C : ℝ) * dist p q := hL.dist_le_mul p hpb q hqb
  have h2 : dist p q ≤ δ := by
    rw [Real.dist_eq]
    have hlt : |p - q| < b - max a (b - δ) := by
      rw [abs_lt]
      constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
    have hle : b - max a (b - δ) ≤ δ := by linarith [le_max_right a (b - δ)]
    linarith
  have h3 : (C : ℝ) * dist p q ≤ (C : ℝ) * δ :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : (C : ℝ) * δ < ε := by
    have hδnn : 0 ≤ δ := le_of_lt hδ
    have h5 : (C : ℝ) * δ ≤ ((C : ℝ) + 1) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδnn
    have h6 : ((C : ℝ) + 1) * δ = ε / 2 := by
      rw [hδdef]; field_simp
    linarith
  linarith

theorem tendsto_of_deriv_bounded {f : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 1 f (Set.Ioo a b)) (hM : ∀ x ∈ Set.Ioo a b, |deriv f x| ≤ M) :
    (∃ L : ℝ, Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds L)) ∧
      (∃ R : ℝ, Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds R)) := by
  have hL : LipschitzOnWith (⟨max M 0, le_max_right M 0⟩ : ℝ≥0) f (Ioo a b) := by
    refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun x hx => ?_) (fun x hx => ?_)
      (convex_Ioo a b)
    · exact (hf.differentiableOn_one x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
    · have hm : |deriv f x| ≤ max M 0 := le_trans (hM x hx) (le_max_left M 0)
      exact_mod_cast hm
  exact ⟨exists_tendsto_nhdsGT_of_lipschitzOn hab hL,
    exists_tendsto_nhdsLT_of_lipschitzOn hab hL⟩

end Work.FTS_EllLimOK.ProducerH.ThetaZero
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.integral_rpow_zero_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

/-- `∫₀¹ v^β dv = 1/(β+1)` for `β > -1` (immediate from `integral_rpow`). -/
theorem integral_rpow_zero_one {β : ℝ} (hβ : -1 < β) :
    ∫ v in (0 : ℝ)..1, v ^ β = 1 / (β + 1) := by
  rw [integral_rpow (Or.inl hβ), Real.one_rpow, Real.zero_rpow (by linarith : (β + 1) ≠ 0)]
  ring

end Work.FTS_EllLimOK.ProducerH
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.not_integrableOn_cos_sq_mul_sin_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

open MeasureTheory Set
open scoped Real

/-!
## Non-integrability of `cos θ^{-2} · sin(2θ)^{-η}` at the right endpoint `θ = π/2`

This is the divergence input for `Work.FTS_EllLimOK.ProducerH.kappa_eq_zero`: near `θ = π/2`
the function `θ ↦ cos θ^{-2} · sin(2θ)^{-η}` behaves like
`(π/2 - θ)^{-2-η}`, whose integral over any right neighbourhood of `π/2` diverges because
`2 + η > 1`.

The three ingredients below are proved from scratch:

* `inv_sq_not_integrableOn_Ioo` — `u ↦ 1 / u ^ 2` is not integrable on `(0,t)`, `t > 0`
  (the case `s = -2` of `intervalIntegral.integrableOn_Ioo_rpow_iff`);
* `one_div_sq_le_sin_mul_sin` — the pointwise lower bound
  `1 / u ^ 2 ≤ sin u ^ (-2) · sin(2u) ^ (-η)` on `(0, π/2)` for `η ≥ 0`, from `Real.sin_le`
  and the antitonicity of `x ↦ x ^ (-η)` on `(0,1]`;
* `not_integrableOn_Ioo_sin_mul` — its consequence: `sin u ^ (-2) · sin(2u) ^ (-η)` is not
  integrable on `(0,t)`.

The theorem is then obtained by reflecting the right end `(a, π/2)` of the interval onto
`(0, π/2 - a)` with the substitution `u = π/2 - θ`, using
`IntervalIntegrable.comp_sub_left`; on that interval `cos θ = sin u` and `sin 2θ = sin 2u`.
-/

/-- `u ↦ 1 / u ^ 2` is not integrable on `(0, t)` for `t > 0`: this is the case `s = -2` of
`intervalIntegral.integrableOn_Ioo_rpow_iff`, together with `1 / u ^ 2 = u ^ (-2)`. -/
private theorem inv_sq_not_integrableOn_Ioo {t : ℝ} (ht : 0 < t) :
    ¬ MeasureTheory.IntegrableOn (fun u : ℝ => 1 / u ^ 2) (Set.Ioo 0 t) := by
  intro h
  have h' : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Set.Ioo 0 t) := by
    refine h.congr_fun (fun u hu => ?_) measurableSet_Ioo
    simp only []
    rw [one_div, Real.rpow_neg (le_of_lt hu.1) 2]
    norm_num
  have h2 := (intervalIntegral.integrableOn_Ioo_rpow_iff ht).mp h'
  linarith

/-- Pointwise lower bound: on `(0, π/2)`, `1 / u ^ 2 ≤ sin u ^ (-2) · sin(2u) ^ (-η)` for
`η ≥ 0`.  Indeed `sin u ≤ u` gives `u ^ (-2) ≤ (sin u) ^ (-2)` (the exponent `-2` is `≤ 0`),
while `0 < sin(2u) ≤ 1` and `-η ≤ 0` give `sin(2u) ^ (-η) ≥ 1`. -/
private theorem one_div_sq_le_sin_mul_sin {η u : ℝ} (hη : 0 ≤ η)
    (hu : u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 / u ^ 2 ≤ (Real.sin u) ^ (-2 : ℝ) * (Real.sin (2 * u)) ^ (-η) := by
  have hu0 : 0 < u := hu.1
  have hult : u < Real.pi / 2 := hu.2
  have hsin_pos : 0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [Real.pi_pos, hult])
  have hle : Real.sin u ≤ u := Real.sin_le hu0.le
  have h1 : u ^ (-2 : ℝ) ≤ (Real.sin u) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hsin_pos hle (by norm_num)
  have hu2 : 1 / u ^ 2 = u ^ (-2 : ℝ) := by
    rw [one_div, Real.rpow_neg hu0.le 2]; norm_num
  have h1' : 1 / u ^ 2 ≤ (Real.sin u) ^ (-2 : ℝ) := by rw [hu2]; exact h1
  have h2u0 : 0 < 2 * u := by linarith
  have h2ult : 2 * u < Real.pi := by linarith
  have hsin2_pos : 0 < Real.sin (2 * u) := Real.sin_pos_of_pos_of_lt_pi h2u0 h2ult
  have h2 : 1 ≤ (Real.sin (2 * u)) ^ (-η) := by
    have h := Real.rpow_le_rpow_of_nonpos hsin2_pos (Real.sin_le_one (2 * u))
      (by linarith : -η ≤ 0)
    rwa [Real.one_rpow] at h
  calc 1 / u ^ 2 = 1 / u ^ 2 * 1 := (mul_one _).symm
    _ ≤ (Real.sin u) ^ (-2 : ℝ) * (Real.sin (2 * u)) ^ (-η) :=
        mul_le_mul h1' h2 zero_le_one (le_of_lt (Real.rpow_pos_of_pos hsin_pos _))

/-- `u ↦ sin u ^ (-2) · sin(2u) ^ (-η)` is not integrable on `(0, t)`, `t > 0`, for `η ≥ 0`:
it dominates `1 / u ^ 2`, which is not integrable at `0`. -/
private theorem not_integrableOn_Ioo_sin_mul {η t : ℝ} (hη : 0 ≤ η) (ht : 0 < t) :
    ¬ MeasureTheory.IntegrableOn
        (fun u : ℝ => (Real.sin u) ^ (-2 : ℝ) * (Real.sin (2 * u)) ^ (-η))
        (Set.Ioo 0 t) := by
  intro h
  have hp : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have ht' : 0 < min t (Real.pi / 2) := lt_min ht hp
  have hmono : MeasureTheory.IntegrableOn
      (fun u : ℝ => (Real.sin u) ^ (-2 : ℝ) * (Real.sin (2 * u)) ^ (-η))
      (Set.Ioo 0 (min t (Real.pi / 2))) :=
    h.mono_set (Set.Ioo_subset_Ioo_right (min_le_left t (Real.pi / 2)))
  have hInt : MeasureTheory.IntegrableOn (fun u : ℝ => 1 / u ^ 2)
      (Set.Ioo 0 (min t (Real.pi / 2))) := by
    refine hmono.mono' (measurable_const.div (measurable_id.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_of_nonneg (div_nonneg zero_le_one (sq_nonneg u))]
    exact one_div_sq_le_sin_mul_sin hη ⟨hu.1, lt_of_lt_of_le hu.2 (min_le_right _ _)⟩
  exact inv_sq_not_integrableOn_Ioo ht' hInt

/-- **`cos θ^{-2}·sin(2θ)^{-η}` is not integrable near `θ = π/2`.**  For `0 < a < π/2` and
`0 ≤ η < 1`, the function `θ ↦ cos θ^{-2}·sin(2θ)^{-η}` is not integrable on `(a, π/2)`.
Route: substitute `u = π/2 - θ` (so `cos θ = sin u`, `sin 2θ = sin(2u)`), apply
`intervalIntegral.integral_comp_sub_left` (or the `IntervalIntegrable`-level version), and dominate
`sin u^{-2}·sin(2u)^{-η} ≥ π^{-η}·u^{-2}` for `u ∈ (0, π/2)` using `Real.sin_le` and the
antitonicity of `x ↦ x^{-η}` on `(0,∞)`; then use
`intervalIntegral.integrableOn_Ioo_rpow_iff` (`u^{-2}` is not integrable at `0`).
Consumed by `Work.FTS_EllLimOK.ProducerH.kappa_eq_zero`. -/
theorem not_integrableOn_cos_sq_mul_sin_rpow {a η : ℝ} (ha : 0 < a) (ha' : a < Real.pi / 2)
    (hη : 0 ≤ η) (hη1 : η < 1) :
    ¬ MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Real.cos θ) ^ (-2 : ℝ) * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo a (Real.pi / 2)) := by
  have _ha : 0 < a := ha
  have _hη1 : η < 1 := hη1
  intro h
  -- `h` is an integral over `a..π/2`; reflect the right end onto `0..π/2 - a`
  have hII : IntervalIntegrable
      (fun θ : ℝ => (Real.cos θ) ^ (-2 : ℝ) * (Real.sin (2 * θ)) ^ (-η))
      volume a (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt ha')).mpr h
  have hII' : IntervalIntegrable
      (fun u : ℝ =>
        (Real.cos (Real.pi / 2 - u)) ^ (-2 : ℝ) * (Real.sin (2 * (Real.pi / 2 - u))) ^ (-η))
      volume (Real.pi / 2 - a) (Real.pi / 2 - Real.pi / 2) :=
    hII.comp_sub_left (Real.pi / 2)
  have hIIs : IntervalIntegrable
      (fun u : ℝ =>
        (Real.cos (Real.pi / 2 - u)) ^ (-2 : ℝ) * (Real.sin (2 * (Real.pi / 2 - u))) ^ (-η))
      volume 0 (Real.pi / 2 - a) := by
    simpa [sub_self] using hII'.symm
  have ht0 : (0 : ℝ) ≤ Real.pi / 2 - a := by linarith [ha']
  have hIoo : MeasureTheory.IntegrableOn
      (fun u : ℝ =>
        (Real.cos (Real.pi / 2 - u)) ^ (-2 : ℝ) * (Real.sin (2 * (Real.pi / 2 - u))) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2 - a)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht0).mp hIIs
  -- substitute `cos (π/2 - u) = sin u`, `sin (2 (π/2 - u)) = sin (2u)`
  have hIoo' : MeasureTheory.IntegrableOn
      (fun u : ℝ => (Real.sin u) ^ (-2 : ℝ) * (Real.sin (2 * u)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2 - a)) := by
    refine hIoo.congr_fun (fun u _ => ?_) measurableSet_Ioo
    simp only []
    simp only [Real.cos_pi_div_two_sub]
    rw [show 2 * (Real.pi / 2 - u) = Real.pi - 2 * u by ring, Real.sin_pi_sub]
  exact not_integrableOn_Ioo_sin_mul hη (by linarith [ha']) hIoo'

end Work.FTS_EllLimOK.ProducerH
end
-- ===== merged: Submission.Work.FTS_EllLimOK.SliceTrace.abs_deriv_sub_le_intervalIntegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS_EllLimOK.SliceTrace


end Work.FTS_EllLimOK.SliceTrace
end
-- ===== merged: Submission.Work.FTS_EllLimOK.SliceTrace.abs_le_half_sq_mul_rpow_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.SliceTrace

/-- The arithmetic–geometric mean inequality in the form
`|h| ≤ (h² s^{-η} + s^η)/2` for `s > 0`: the two summands are nonnegative and their
product is `h²`, so `2|h| = 2√(A B) ≤ A + B`. -/
theorem abs_le_half_sq_mul_rpow_add {η s h : ℝ} (hs : 0 < s) :
    |h| ≤ (h ^ 2 * s ^ (-η) + s ^ η) / 2 := by
  set A := h ^ 2 * s ^ (-η) with hAdef
  set B := s ^ η with hBdef
  have hs0 : 0 ≤ s := le_of_lt hs
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by rw [hBdef]; exact Real.rpow_nonneg hs0 _
  -- the two summands multiply to `h ^ 2`
  have hAB : A * B = h ^ 2 := by
    rw [hAdef, hBdef, mul_assoc, ← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero, mul_one]
  -- `(A + B) ^ 2 - 4 h ^ 2 = (A - B) ^ 2 ≥ 0`
  have h4 : 4 * h ^ 2 ≤ (A + B) ^ 2 := by nlinarith [sq_nonneg (A - B)]
  have h2 : (2 * |h|) ^ 2 ≤ (A + B) ^ 2 := by nlinarith [abs_nonneg h, sq_abs h]
  have : 2 * |h| ≤ A + B := by nlinarith [abs_nonneg h, hA0, hB0, h2]
  linarith

end Work.FTS_EllLimOK.SliceTrace
end
-- ===== merged: Submission.Work.FTS_EllLimOK.SliceTrace.exists_abs_le_of_integrable_weighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology

namespace Work.FTS_EllLimOK.SliceTrace

/-- `sin (2 x) ≥ 0` for `x` in `(t, π/2)` with `t > 0`. -/
private lemma sin_two_nonneg_of_mem {t x : ℝ} (ht : 0 < t) (hx : x ∈ Set.Ioo t (Real.pi / 2)) :
    0 ≤ Real.sin (2 * x) := by
  apply Real.sin_nonneg_of_mem_Icc
  constructor <;> linarith [ht, hx.1, hx.2, Real.pi_pos]

/-- On `(π/2 - θ, π/2)` with `0 < θ < π/2`, the weight `sin (2x) ^ (-γ)` dominates the
constant `(2θ) ^ (-γ)` (for `γ > 0`). -/
private lemma rpow_sin_two_ge {γ θ x : ℝ} (hγ : 0 < γ) (hθπ : θ < Real.pi / 2)
    (hx1 : Real.pi / 2 - θ < x) (hx2 : x < Real.pi / 2) :
    (2 * θ) ^ (-γ) ≤ (Real.sin (2 * x)) ^ (-γ) := by
  have hsx_pos : 0 < Real.sin (2 * x) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have hs2 : Real.sin (2 * x) ≤ 2 * θ := by
    have he : Real.sin (2 * x) = Real.sin (Real.pi - 2 * x) :=
      (Real.sin_pi_sub (2 * x)).symm
    rw [he]
    calc Real.sin (Real.pi - 2 * x) ≤ Real.pi - 2 * x := Real.sin_le (by linarith)
      _ ≤ 2 * θ := by linarith
  exact Real.rpow_le_rpow_of_nonpos hsx_pos hs2 (by linarith)

/-- Near the endpoint `π / 2`, integrability of `f ^ 2 * sin (2θ) ^ (-γ)` with `γ > 1` forces
`|f| ≤ d` at some point. -/
theorem exists_abs_le_of_integrable_weighted {γ : ℝ} (hγ : 1 < γ) {f : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
      (Set.Ioo t (Real.pi / 2))) {d : ℝ} (hd : 0 < d) :
    ∃ τ ∈ Set.Ioo t (Real.pi / 2), |f τ| ≤ d := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hγpos : 0 < γ := by linarith
  set S : Set ℝ := Set.Ioo t (Real.pi / 2) with hS
  set h : ℝ → ℝ := fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) with hh
  have hint' : IntegrableOn h S := hint
  set D : ℝ := ∫ x in S, h x with hD
  have hsnonneg : 0 ≤ᵐ[volume.restrict S] h := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := S) measurableSet_Ioo] with x hx
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (sin_two_nonneg_of_mem ht.1 hx) _)
  -- The key lower bound: the integral over any interval `(π/2 - θ, π/2)` dominates
  -- `d ^ 2 * (2 * θ) ^ (-γ) * θ`.
  have hmain : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2 - t),
      d ^ 2 * (2 * θ) ^ (-γ) * θ ≤ D := by
    intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hθu : θ < Real.pi / 2 - t := hθ.2
    have ht1 : 0 < t := ht.1
    have hθπ : θ < Real.pi / 2 := by linarith
    have ha : t < Real.pi / 2 - θ := by linarith
    have hsub : Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2) ⊆ S := by
      rintro x ⟨hx1, hx2⟩
      exact ⟨lt_trans ha hx1, hx2⟩
    have hintf : IntegrableOn h (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2)) :=
      hint'.mono_set hsub
    have hconst : IntegrableOn (fun _ : ℝ => d ^ 2 * (2 * θ) ^ (-γ))
        (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2)) := by
      apply integrableOn_const
      · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
      · finiteness
    have hmono : ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), (d ^ 2 * (2 * θ) ^ (-γ) : ℝ)
        ≤ ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), h x := by
      refine setIntegral_mono_on hconst hintf measurableSet_Ioo ?_
      intro x hx
      have hx1 : Real.pi / 2 - θ < x := hx.1
      have hx2 : x < Real.pi / 2 := hx.2
      have hcx : d < |f x| := hcon x ⟨lt_trans ha hx1, hx2⟩
      have hcsq : d ^ 2 ≤ (f x) ^ 2 := by
        have h := pow_le_pow_left₀ hd.le hcx.le 2
        rwa [sq_abs] at h
      have hw := rpow_sin_two_ge hγpos hθπ hx1 hx2
      have h2θ0 : 0 ≤ (2 * θ) ^ (-γ) := Real.rpow_nonneg (by linarith) _
      calc d ^ 2 * (2 * θ) ^ (-γ) ≤ (f x) ^ 2 * (2 * θ) ^ (-γ) :=
            mul_le_mul_of_nonneg_right hcsq h2θ0
        _ ≤ (f x) ^ 2 * (Real.sin (2 * x)) ^ (-γ) :=
            mul_le_mul_of_nonneg_left hw (sq_nonneg _)
        _ = h x := by rw [hh]
    have hval : ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), (d ^ 2 * (2 * θ) ^ (-γ) : ℝ)
        = d ^ 2 * (2 * θ) ^ (-γ) * θ := by
      rw [setIntegral_const, Real.volume_real_Ioo,
        max_eq_left (show (0 : ℝ) ≤ Real.pi / 2 - (Real.pi / 2 - θ) by linarith),
        smul_eq_mul]
      ring
    have hb : ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), h x ≤ D := by
      rw [hD]
      refine setIntegral_mono_set hint' ?_ ?_
      · exact hsnonneg
      · exact ae_of_all _ fun x hx => hsub hx
    linarith [hval ▸ hmono]
  -- The lower bound diverges as `θ → 0⁺`.
  have hgtop : Tendsto (fun θ : ℝ => d ^ 2 * (2 * θ) ^ (-γ) * θ) (𝓝[>] (0 : ℝ)) atTop := by
    have hr : Tendsto (fun θ : ℝ => θ ^ (1 - γ)) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_rpow_neg_nhdsGT_zero (by linarith : (1 : ℝ) - γ < 0)
    have hpos : 0 < d ^ 2 * (2 : ℝ) ^ (-γ) := by
      have h2 : 0 < (2 : ℝ) ^ (-γ) := Real.rpow_pos_of_pos (by norm_num) _
      positivity
    refine (hr.const_mul_atTop hpos).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hθ0 : 0 < θ := hθ
    have h1 : θ ^ (-γ) * θ = θ ^ (1 - γ) := by
      have key : θ ^ (-γ) * θ ^ (1 : ℝ) = θ ^ (-γ + 1) := (Real.rpow_add hθ0 (-γ) 1).symm
      rw [Real.rpow_one θ] at key
      rw [key, show -γ + 1 = 1 - γ from by ring]
    have hgoal : d ^ 2 * (2 * θ) ^ (-γ) * θ = d ^ 2 * 2 ^ (-γ) * θ ^ (1 - γ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hθ0.le]
      calc d ^ 2 * (2 ^ (-γ) * θ ^ (-γ)) * θ
          = d ^ 2 * (2 ^ (-γ) * (θ ^ (-γ) * θ)) := by ring
        _ = d ^ 2 * (2 ^ (-γ) * θ ^ (1 - γ)) := by rw [h1]
        _ = d ^ 2 * 2 ^ (-γ) * θ ^ (1 - γ) := by ring
    exact hgoal.symm
  have hevA : ∀ᶠ θ in 𝓝[>] (0 : ℝ), D + 1 < d ^ 2 * (2 * θ) ^ (-γ) * θ :=
    hgtop.eventually_gt_atTop (D + 1)
  have hevB : ∀ᶠ θ in 𝓝[>] (0 : ℝ), d ^ 2 * (2 * θ) ^ (-γ) * θ ≤ D :=
    Filter.mem_of_superset
      (Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 2 - t by linarith [ht.2]))
      fun θ hθ => hmain θ hθ
  obtain ⟨θ, h1, h2⟩ := (hevA.and hevB).exists
  linarith

end Work.FTS_EllLimOK.SliceTrace
end
-- ===== merged: Submission.Work.FTS_EllLimOK.SliceTrace.tendsto_self_at_pi_div_two_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The trace `f` vanishes at `π/2`

If `f` is a function on `(0, π/2)` whose weighted square integral
`∫₀^{π/2} (f θ / cos θ)² dθ` is finite and which has a finite limit `J` at `π/2` from the
left, then necessarily `J = 0`, so `f → 0`.

The point is that `cos θ ≈ π/2 - θ` near `π/2`: the weight `1/cos²θ` is *not* integrable
there.  If `f → J ≠ 0`, then `|f| > d` for some `d > 0` on a whole tail `(t, π/2)`, and on the
sub-interval `(π/2 - θ, π/2)` of length `θ` we have `cos x ≤ θ`, whence

`(f x / cos x)² > d²/θ²`,  so  `∫_{π/2-θ}^{π/2} (f/cos)² > d²/θ`,

which is unbounded as `θ → 0⁺`, contradicting integrability.

The integrability of `f` at the endpoint is therefore strong enough to force the value of the
limit on its own; the `C¹`-hypothesis is not needed (it is part of the caller's context).
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS_EllLimOK.SliceTrace



end Work.FTS_EllLimOK.SliceTrace
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.integral_comp_mul_Ioi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_LocDatum3a

theorem integral_comp_mul_Ioi {c : ℝ} (hc : 0 < c) (R : ℝ → ℝ) :
    (∫ s in Set.Ioi 0, R (c * s) / s) = ∫ s in Set.Ioi 0, R s / s := by
  let g : ℝ → ℝ := fun t => R t / t
  have hR : (∫ s in Set.Ioi 0, R s / s) = ∫ s in Set.Ioi 0, g s := rfl
  rw [hR]
  have hpt : ∀ s : ℝ, R (c * s) / s = c • g (c * s) := by
    intro s
    show R (c * s) / s = c * (R (c * s) / (c * s))
    rw [← mul_div_assoc, mul_div_mul_left (R (c * s)) s hc.ne']
  simp_rw [hpt]
  rw [MeasureTheory.integral_smul]
  rw [MeasureTheory.integral_comp_mul_left_Ioi' g 0 hc]
  simp only [mul_zero]

end Work.FTS_LocDatum3a
end
-- ===== merged: Submission.Work.FTS_RXTPieces.noDecayPieces.false_of_log_divergence =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RXTPieces.noDecayPieces

-- the a.e. nonnegativity hypothesis is not needed: `hg` already gives pointwise positivity
-- on `(z,∞)`, so the proof below does not consume it
set_option linter.unusedVariables false in
theorem false_of_log_divergence {g : ℝ → ℝ} {z c : ℝ}
    (hz : 0 < z) (hc : 0 < c)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0))
    (hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)] g)
    (hg : ∀ x, z ≤ x → c / x ≤ g x) : False := by
  -- `g` is integrable on `(z,∞)`
  have hgz : MeasureTheory.IntegrableOn g (Set.Ioi z) :=
    hint.mono_set (Set.Ioi_subset_Ioi hz.le)
  -- hence so is the larger function `x ↦ c⁻¹ * g x`
  have h1 : MeasureTheory.IntegrableOn (fun x : ℝ => c⁻¹ * g x) (Set.Ioi z) :=
    MeasureTheory.Integrable.const_mul hgz c⁻¹
  -- comparing with `x ↦ x⁻¹ ≤ c⁻¹ * g x` on `(z,∞)` gives integrability of `x ↦ x⁻¹`
  have h2 : MeasureTheory.IntegrableOn (fun x : ℝ => x⁻¹) (Set.Ioi z) := by
    refine MeasureTheory.Integrable.mono' h1 measurable_inv.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hz.trans hx
    have hle : c / x ≤ g x := hg x hx.le
    have hcoef : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
    have hkey : c⁻¹ * (c / x) = x⁻¹ := by
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hx0, ← hkey]
    exact mul_le_mul_of_nonneg_left hle hcoef.le
  exact not_integrableOn_Ioi_inv h2

end Work.FTS_RXTPieces.noDecayPieces
end
-- ===== merged: Submission.Work.FTS_RXTPieces.noDecayPieces.le_sub_setIntegral_of_deriv_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RXTPieces.noDecayPieces

open MeasureTheory Set

theorem le_sub_setIntegral_of_deriv_le {F F' G : ℝ → ℝ}
    (hcont : ContinuousOn F (Set.Ioi (0 : ℝ)))
    (hmeas : MeasureTheory.AEStronglyMeasurable F' (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt F (F' x) x)
    (hbd : ∀ x ∈ Set.Ioi (0 : ℝ), |F' x| ≤ G x)
    (hGint : MeasureTheory.IntegrableOn G (Set.Ioi 0))
    (hGnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)] G)
    {z : ℝ} (hz : 0 < z) :
    ∀ x, z ≤ x → F z - (∫ t in Set.Ioi 0, G t) ≤ F x := by
  intro x hzx
  -- On `[z,x]` (with `z > 0`) the function `F'` is dominated by the integrable, a.e. nonnegative
  -- `G`; the fundamental theorem of calculus then writes `F z - F x` as the integral of `-F'`.
  have hsub : Set.Ioc z x ⊆ Set.Ioi (0 : ℝ) := fun y hy => lt_trans hz hy.1
  have hIntG : IntervalIntegrable G volume z x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hzx]
    exact hGint.mono_set hsub
  have hIntF' : IntervalIntegrable F' volume z x := by
    refine hIntG.mono_fun' (hmeas.mono_set ?_) ?_
    · rw [uIoc_of_le hzx]; exact hsub
    · rw [uIoc_of_le hzx]
      exact ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => by
        have h := hbd y (hsub hy)
        simpa [Real.norm_eq_abs] using h)
  have hFTC : ∫ y in z..x, F' y = F x - F z := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro y hy
      rw [uIcc_of_le hzx] at hy
      exact hderiv y (lt_of_lt_of_le hz hy.1)
    · exact hIntF'
  have hmono : ∫ y in z..x, -F' y ≤ ∫ y in z..x, G y := by
    apply intervalIntegral.integral_mono_on hzx hIntF'.neg hIntG
    intro y hy
    have h := hbd y (lt_of_lt_of_le hz hy.1)
    rw [abs_le] at h
    show -(F' y) ≤ G y
    linarith [h.1]
  have hmono2 : ∫ y in z..x, G y ≤ ∫ t in Set.Ioi 0, G t := by
    rw [intervalIntegral.integral_of_le hzx]
    exact setIntegral_mono_set hGint hGnn (Filter.Eventually.of_forall hsub)
  have h1 : F z - F x ≤ ∫ t in Set.Ioi 0, G t := by
    calc F z - F x = -(F x - F z) := by ring
      _ = -∫ y in z..x, F' y := by rw [← hFTC]
      _ = ∫ y in z..x, -F' y := intervalIntegral.integral_neg.symm
      _ ≤ ∫ y in z..x, G y := hmono
      _ ≤ ∫ t in Set.Ioi 0, G t := hmono2
  linarith

end Work.FTS_RXTPieces.noDecayPieces
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.HJ.derivBoundZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1.HJ

theorem derivBoundZero {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ x : ℝ, 0 < x → ∃ d : ℝ, HasDerivAt f d x ∧ |d| ≤ C)
    (htend : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ z : ℝ, 0 < z → |f z| ≤ C * z := by
  intro z hz
  -- Mean value inequality: for every `y > 0`, `|f z - f y| ≤ C * |z - y|`.
  have hdiff : ∀ y ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ f y :=
    fun y hy => (hderiv y hy).choose_spec.1.differentiableAt
  have hderivb : ∀ y ∈ Set.Ioi (0 : ℝ), ‖deriv f y‖ ≤ C := by
    intro y hy
    rw [Real.norm_eq_abs, (hderiv y hy).choose_spec.1.deriv]
    exact (hderiv y hy).choose_spec.2
  have hmvt : ∀ y ∈ Set.Ioi (0 : ℝ), |f z - f y| ≤ C * |z - y| := by
    intro y hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderivb (convex_Ioi 0) hz hy
    simpa [Real.norm_eq_abs, abs_sub_comm] using h
  -- Pass to the limit `y → 0⁺`, where `f y → 0`.
  have hlim : Filter.Tendsto (fun y : ℝ => |f z - f y|) (nhdsWithin 0 (Set.Ioi 0))
      (nhds |f z|) := by
    have hsub : Filter.Tendsto (fun y : ℝ => f z - f y) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (f z - 0)) := tendsto_const_nhds.sub htend
    have h2 : Filter.Tendsto (fun y : ℝ => ‖f z - f y‖) (nhdsWithin 0 (Set.Ioi 0))
        (nhds ‖f z - 0‖) := hsub.norm
    simpa [Real.norm_eq_abs] using h2
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (isOpen_Iio.mem_nhds (show (0 : ℝ) ∈ Set.Iio z from hz))] with y hy hyz
  have hy0 : 0 < y := hy
  have hyz' : y < z := hyz
  have h1 := hmvt y hy0
  have h2 : |z - y| ≤ z := by
    rw [abs_of_pos (show (0 : ℝ) < z - y by linarith)]
    linarith
  calc |f z - f y| ≤ C * |z - y| := h1
    _ ≤ C * z := by nlinarith [hC]

end Work.FTS_RegExport.RXR1.HJ
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.contDiffOn_one_of_equiC1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1

/-- Mean value bound for a difference quotient: if `φ` is `C¹` on `(0,∞)` and
`|deriv φ w - deriv φ u| ≤ ε` on the whole segment `[u, u+h]` (`h > 0`, `u > 0`), then the
difference quotient of `φ` at `u` with step `h` is within `ε` of `deriv φ u`. -/
theorem sub_deriv_slope_le {φ : ℝ → ℝ} {u h ε : ℝ} (hu : 0 < u) (hh : 0 < h)
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi (0:ℝ)))
    (hbound : ∀ w ∈ Set.Icc u (u + h), |deriv φ w - deriv φ u| ≤ ε) :
    |h⁻¹ • (φ (u + h) - φ u) - deriv φ u| ≤ ε := by
  have hsub : (u + h : ℝ) - u = h := by ring
  obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope φ (show u < u + h by linarith)
    (hφ.continuousOn.mono (fun x hx => lt_of_lt_of_le hu (Set.mem_Icc.mp hx).1))
    ((hφ.differentiableOn_one).mono (fun x hx => lt_trans hu hx.1))
  have hξmem : ξ ∈ Set.Icc u (u + h) := ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
  rw [hsub] at hξeq
  have hkey : h⁻¹ • (φ (u + h) - φ u) - deriv φ u = deriv φ ξ - deriv φ u := by
    rw [hξeq, smul_eq_mul, div_eq_inv_mul, mul_comm]
  rw [hkey]
  exact hbound ξ hξmem

/-- The limit of the family `f τ` as `τ → 0⁺` is `C¹` on `(0,∞)` whenever the family is
uniformly `C¹` with an equicontinuous derivative (modulus `E`, vanishing on the diagonal) and
the pointwise limit `R` is differentiable. -/
theorem contDiffOn_one_of_equiC1 {f : ℝ → ℝ → ℝ} {R : ℝ → ℝ} {N : ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hNcont : ContinuousOn N (Set.Ioi 0))
    (hC1 : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ContDiffOn ℝ 1 (fun z => f τ z) (Set.Ioi 0))
    (hN : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ∀ z ∈ Set.Ioi (0:ℝ), |deriv (fun z' => f τ z') z| ≤ N z)
    (hEcont : ContinuousOn (fun p : ℝ × ℝ => E p.1 p.2) (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)))
    (hEdiag : ∀ z ∈ Set.Ioi (0:ℝ), E z z = 0)
    (hE : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ∀ z ∈ Set.Ioi (0:ℝ), ∀ z' ∈ Set.Ioi (0:ℝ),
      |deriv (fun z'' => f τ z'') z - deriv (fun z'' => f τ z'') z'| ≤ E z z')
    (htend : ∀ z ∈ Set.Ioi (0:ℝ), Filter.Tendsto (fun τ => f τ z) (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (R z)))
    (hdiff : DifferentiableOn ℝ R (Set.Ioi (0:ℝ))) :
    ContDiffOn ℝ 1 R (Set.Ioi (0:ℝ)) := by
  -- Step 1: the derivative of `R` inherits the modulus of equicontinuity `E`.
  have hmod : ∀ z ∈ Set.Ioi (0:ℝ), ∀ z' ∈ Set.Ioi (0:ℝ), |deriv R z - deriv R z'| ≤ E z z' := by
    intro z hz z' hz'
    have hz0 : (0:ℝ) < z := hz
    have hz'0 : (0:ℝ) < z' := hz'
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε2 : 0 < ε / 2 := by linarith
    -- continuity of the modulus at the diagonal points `(z,z)` and `(z',z')`
    have hcont_z := Metric.continuousWithinAt_iff.mp
      (hEcont.continuousWithinAt (show (z, z) ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ) from ⟨hz, hz⟩))
    have hcont_z' := Metric.continuousWithinAt_iff.mp
      (hEcont.continuousWithinAt (show (z', z') ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ) from ⟨hz', hz'⟩))
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hcont_z (ε / 2) hε2
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hcont_z' (ε / 2) hε2
    have hEz : ∀ w ∈ Set.Ioi (0:ℝ), |w - z| < δ₁ → E w z < ε / 2 := by
      intro w hw hwδ
      have hd : dist (w, z) (z, z) < δ₁ := by simpa [Prod.dist_eq, Real.dist_eq] using hwδ
      have h := hδ₁ (x := (w, z)) ⟨hw, hz⟩ hd
      rw [Real.dist_eq, hEdiag z hz, sub_zero] at h
      exact lt_of_le_of_lt (le_abs_self _) h
    have hEz' : ∀ w ∈ Set.Ioi (0:ℝ), |w - z'| < δ₂ → E w z' < ε / 2 := by
      intro w hw hwδ
      have hd : dist (w, z') (z', z') < δ₂ := by simpa [Prod.dist_eq, Real.dist_eq] using hwδ
      have h := hδ₂ (x := (w, z')) ⟨hw, hz'⟩ hd
      rw [Real.dist_eq, hEdiag z' hz', sub_zero] at h
      exact lt_of_le_of_lt (le_abs_self _) h
    have hδpos : 0 < min δ₁ δ₂ := lt_min hδ₁pos hδ₂pos
    have hIoc : Set.Ioc (0:ℝ) 1 ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := by
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1:ℝ) 1, isOpen_Ioo, by norm_num, ?_⟩
      rintro x ⟨hx1, hx2⟩
      exact ⟨show (0:ℝ) < x from hx2, le_of_lt hx1.2⟩
    -- the bound for the difference quotients at a fixed step `h`
    have hkey : ∀ h : ℝ, 0 < h → h < min δ₁ δ₂ →
        |h⁻¹ • (R (z + h) - R z) - h⁻¹ • (R (z' + h) - R z')| ≤ E z z' + ε := by
      intro h hhpos hhδ
      have hzl : z + h ∈ Set.Ioi (0:ℝ) := by show (0:ℝ) < z + h; linarith
      have hz'l : z' + h ∈ Set.Ioi (0:ℝ) := by show (0:ℝ) < z' + h; linarith
      have hQb : ∀ τ ∈ Set.Ioc (0:ℝ) 1,
          |h⁻¹ • (f τ (z + h) - f τ z) - h⁻¹ • (f τ (z' + h) - f τ z')| ≤ E z z' + ε := by
        intro τ hτ
        have hpz : |h⁻¹ • (f τ (z + h) - f τ z) - deriv (fun z'' => f τ z'') z| ≤ ε / 2 := by
          refine sub_deriv_slope_le hz hhpos (hC1 τ hτ) ?_
          intro w hw
          have hw0 : w ∈ Set.Ioi (0:ℝ) := lt_of_lt_of_le hz (Set.mem_Icc.mp hw).1
          have hwδ : |w - z| < δ₁ := by
            have h1 : w - z ≤ h := by linarith [(Set.mem_Icc.mp hw).2]
            have h2 : 0 ≤ w - z := by linarith [(Set.mem_Icc.mp hw).1]
            rw [abs_of_nonneg h2]
            exact lt_of_le_of_lt h1 (lt_of_lt_of_le hhδ (min_le_left _ _))
          exact le_of_lt (lt_of_le_of_lt (hE τ hτ w hw0 z hz) (hEz w hw0 hwδ))
        have hpz' : |h⁻¹ • (f τ (z' + h) - f τ z') - deriv (fun z'' => f τ z'') z'| ≤ ε / 2 := by
          refine sub_deriv_slope_le hz' hhpos (hC1 τ hτ) ?_
          intro w hw
          have hw0 : w ∈ Set.Ioi (0:ℝ) := lt_of_lt_of_le hz' (Set.mem_Icc.mp hw).1
          have hwδ : |w - z'| < δ₂ := by
            have h1 : w - z' ≤ h := by linarith [(Set.mem_Icc.mp hw).2]
            have h2 : 0 ≤ w - z' := by linarith [(Set.mem_Icc.mp hw).1]
            rw [abs_of_nonneg h2]
            exact lt_of_le_of_lt h1 (lt_of_lt_of_le hhδ (min_le_right _ _))
          exact le_of_lt (lt_of_le_of_lt (hE τ hτ w hw0 z' hz') (hEz' w hw0 hwδ))
        have hdiffτ : |deriv (fun z'' => f τ z'') z - deriv (fun z'' => f τ z'') z'| ≤ E z z' :=
          hE τ hτ z hz z' hz'
        have htri : |h⁻¹ • (f τ (z + h) - f τ z) - deriv (fun z'' => f τ z'') z
              + (deriv (fun z'' => f τ z'') z - deriv (fun z'' => f τ z'') z')
              - (h⁻¹ • (f τ (z' + h) - f τ z') - deriv (fun z'' => f τ z'') z')|
            ≤ |h⁻¹ • (f τ (z + h) - f τ z) - deriv (fun z'' => f τ z'') z|
              + |deriv (fun z'' => f τ z'') z - deriv (fun z'' => f τ z'') z'|
              + |h⁻¹ • (f τ (z' + h) - f τ z') - deriv (fun z'' => f τ z'') z'| := by
          have ht := abs_add_three
            (h⁻¹ • (f τ (z + h) - f τ z) - deriv (fun z'' => f τ z'') z)
            (deriv (fun z'' => f τ z'') z - deriv (fun z'' => f τ z'') z')
            (-(h⁻¹ • (f τ (z' + h) - f τ z') - deriv (fun z'' => f τ z'') z'))
          rw [abs_neg] at ht
          exact ht
        have hsplit : h⁻¹ • (f τ (z + h) - f τ z) - h⁻¹ • (f τ (z' + h) - f τ z')
            = h⁻¹ • (f τ (z + h) - f τ z) - deriv (fun z'' => f τ z'') z
              + (deriv (fun z'' => f τ z'') z - deriv (fun z'' => f τ z'') z')
              - (h⁻¹ • (f τ (z' + h) - f τ z') - deriv (fun z'' => f τ z'') z') := by
          simp only [smul_eq_mul]; ring
        rw [hsplit]
        linarith [htri, hpz, hpz', hdiffτ]
      have htendQ : Filter.Tendsto
          (fun τ => h⁻¹ • (f τ (z + h) - f τ z) - h⁻¹ • (f τ (z' + h) - f τ z'))
          (nhdsWithin (0:ℝ) (Set.Ioi 0))
          (nhds (h⁻¹ • (R (z + h) - R z) - h⁻¹ • (R (z' + h) - R z'))) := by
        have h1 : Filter.Tendsto (fun τ => h⁻¹ • (f τ (z + h) - f τ z))
            (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (h⁻¹ • (R (z + h) - R z))) :=
          ((htend (z + h) hzl).sub (htend z hz)).const_smul (h⁻¹)
        have h2 : Filter.Tendsto (fun τ => h⁻¹ • (f τ (z' + h) - f τ z'))
            (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (h⁻¹ • (R (z' + h) - R z'))) :=
          ((htend (z' + h) hz'l).sub (htend z' hz')).const_smul (h⁻¹)
        exact h1.sub h2
      exact le_of_tendsto htendQ.abs (Filter.eventually_of_mem hIoc (fun τ hτ => hQb τ hτ))
    -- pass to the limit `h → 0⁺`
    have hLtend : Filter.Tendsto
        (fun h => h⁻¹ • (R (z + h) - R z) - h⁻¹ • (R (z' + h) - R z'))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (deriv R z - deriv R z')) :=
      (((hdiff.differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt.tendsto_slope_zero_right).sub
       ((hdiff.differentiableAt (isOpen_Ioi.mem_nhds hz')).hasDerivAt.tendsto_slope_zero_right))
    have hIoo : Set.Ioo (0:ℝ) (min δ₁ δ₂) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := by
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂), isOpen_Ioo,
        ⟨by linarith, hδpos⟩, ?_⟩
      rintro x ⟨hx1, hx2⟩
      exact ⟨show (0:ℝ) < x from hx2, hx1.2⟩
    exact le_of_tendsto hLtend.abs (Filter.eventually_of_mem hIoo (fun h hh => hkey h hh.1 hh.2))
  -- Step 2: the modulus bound makes `deriv R` continuous on `(0,∞)`.
  have hcont : ContinuousOn (fun z => deriv R z) (Set.Ioi (0:ℝ)) := by
    intro z hz
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hcont_z := Metric.continuousWithinAt_iff.mp
      (hEcont.continuousWithinAt (show (z, z) ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ) from ⟨hz, hz⟩))
    obtain ⟨δ, hδpos, hδ⟩ := hcont_z ε hε
    refine ⟨δ, hδpos, ?_⟩
    intro z' hz' hz'δ
    have hd : dist (z', z) (z, z) < δ := by simpa [Prod.dist_eq, Real.dist_eq] using hz'δ
    have h := hδ (x := (z', z)) ⟨hz', hz⟩ hd
    rw [Real.dist_eq, hEdiag z hz, sub_zero] at h
    calc dist (deriv R z') (deriv R z)
        = |deriv R z' - deriv R z| := Real.dist_eq _ _
      _ ≤ E z' z := hmod z' hz' z hz
      _ ≤ |E z' z| := le_abs_self _
      _ < ε := h
  -- Step 3: `R` is differentiable with continuous derivative, i.e. `C¹`.
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn]
  exact ⟨hdiff, hcont.congr fun x hx => derivWithin_of_isOpen isOpen_Ioi hx⟩

end Work.FTS_RegExport.RXR1
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.hasDerivAt_of_tendsto_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1

set_option linter.unusedVariables false

/-- **Pointwise convergence + a uniform Lipschitz bound on a compact set implies uniform
convergence there.**

This is the ("Arzelà–Ascoli"-style) step that promotes the pointwise convergence of the
`v n` to local uniform convergence, which is what `hasDerivAt_of_tendstoLocallyUniformlyOn`
consumes.  The proof is the usual finite-subcover argument: `K` is covered by finitely many
`δ`-balls with `δ = ε / (3 (L + 1))`; at the centres of this cover the sequence converges
pointwise and everywhere else the common Lipschitz bound `L` (also valid for the limit `f`,
by passing to the limit in `|F n x - F n y| ≤ L |x - y|`) controls the error. -/
theorem tendstoUniformlyOn_of_pointwise_of_lipschitzOn {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    {L : ℝ} (hL0 : 0 ≤ L)
    (hF : ∀ n, ∀ x ∈ K, ∀ y ∈ K, |F n x - F n y| ≤ L * |x - y|)
    (hf : ∀ x ∈ K, ∀ y ∈ K, |f x - f y| ≤ L * |x - y|)
    (hK : IsCompact K) (hpt : ∀ x ∈ K, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x))) :
    TendstoUniformlyOn F f Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hL1pos : 0 < L + 1 := by linarith
  have hδpos : 0 < ε / (3 * (L + 1)) := by positivity
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun p => Metric.ball p (ε / (3 * (L + 1))))
    (fun p _ => Metric.ball_mem_nhds p hδpos)
  -- the centres of the finite cover are eventually close to the limit
  have hcen : ∀ᶠ n in Filter.atTop, ∀ y ∈ t, |f y - F n y| < ε / 3 := by
    rw [Filter.eventually_all_finset]
    intro y hy
    have h0 : Filter.Tendsto (fun _ : ℕ => f y) Filter.atTop (nhds (f y)) := tendsto_const_nhds
    have h2 : Filter.Tendsto (fun n => |f y - F n y|) Filter.atTop (nhds (0 : ℝ)) := by
      simpa using (h0.sub (hpt y (htK y hy))).abs
    filter_upwards [Metric.tendsto_nhds.1 h2 (ε / 3) (by linarith)] with n hn
    simpa [Real.dist_eq, abs_abs] using hn
  filter_upwards [hcen] with n hn
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx)
  have hyK : y ∈ K := htK y hyt
  have hxyδ : |x - y| < ε / (3 * (L + 1)) := by
    have h := Metric.mem_ball.1 hxy
    rwa [Real.dist_eq] at h
  have hscale : ∀ a : ℝ, L * |a| ≤ (L + 1) * |a| := fun a =>
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg a)
  have hdelta : (L + 1) * (ε / (3 * (L + 1))) = ε / 3 := by field_simp
  have h1 : |F n x - F n y| < ε / 3 := by
    calc |F n x - F n y| ≤ (L + 1) * |x - y| := le_trans (hF n x hx y hyK) (hscale (x - y))
      _ < (L + 1) * (ε / (3 * (L + 1))) := mul_lt_mul_of_pos_left hxyδ hL1pos
      _ = ε / 3 := hdelta
  have h3 : |f y - f x| < ε / 3 := by
    calc |f y - f x| ≤ (L + 1) * |y - x| := le_trans (hf y hyK x hx) (hscale (y - x))
      _ = (L + 1) * |x - y| := by rw [abs_sub_comm]
      _ < (L + 1) * (ε / (3 * (L + 1))) := mul_lt_mul_of_pos_left hxyδ hL1pos
      _ = ε / 3 := hdelta
  have h2 : |f y - F n y| < ε / 3 := hn y hyt
  rw [Real.dist_eq]
  calc |f x - F n x| ≤ |f x - f y| + |f y - F n y| + |F n y - F n x| := by
        rw [show f x - F n x = (f x - f y) + (f y - F n y) + (F n y - F n x) from by ring]
        exact abs_add_three _ _ _
    _ < ε := by
        have h4 : |f x - f y| < ε / 3 := by rw [abs_sub_comm]; exact h3
        have h5 : |F n y - F n x| < ε / 3 := by rw [abs_sub_comm]; exact h1
        linarith

/-- **Derivative of a pointwise limit with bounded derivatives.**

Let `u n : ℝ → ℝ` be differentiable on the open interval `(a,b)` with derivative `v n`
(bounded on `(a,b)`), let `v n` be differentiable on `(a,b)` with `|deriv (v n)| ≤ L`
uniformly in `n`, and suppose `u n → φ` and `v n → γ` pointwise on `(a,b)`.  Then `φ` is
differentiable on `(a,b)` with `φ' = γ`.

The uniform bound on `deriv (v n)` makes the `v n` Lipschitz with a common constant, so by
`tendstoUniformlyOn_of_pointwise_of_lipschitzOn` the pointwise convergence `v n → γ` is
locally uniform on the open set `(a,b)` (and the limit `γ` is Lipschitz with the same
constant).  Mathlib's `hasDerivAt_of_tendstoLocallyUniformlyOn` then transfers the
derivatives to the limit.  (No use is made of `hab` or of the `L^∞` bound `hM` on `v n`.) -/
theorem hasDerivAt_of_tendsto_deriv {a b : ℝ} (hab : a < b)
    {u v : ℕ → ℝ → ℝ} {φ γ : ℝ → ℝ}
    (hder : ∀ n, ∀ x ∈ Set.Ioo a b, HasDerivAt (u n) (v n x) x)
    (hvdiff : ∀ n, DifferentiableOn ℝ (v n) (Set.Ioo a b))
    (hM : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ∀ x ∈ Set.Ioo a b, |v n x| ≤ M)
    (hL : ∃ L : ℝ, 0 ≤ L ∧ ∀ n, ∀ x ∈ Set.Ioo a b, |deriv (v n) x| ≤ L)
    (hu : ∀ x ∈ Set.Ioo a b, Filter.Tendsto (fun n => u n x) Filter.atTop (nhds (φ x)))
    (hv : ∀ x ∈ Set.Ioo a b, Filter.Tendsto (fun n => v n x) Filter.atTop (nhds (γ x))) :
    ∀ x ∈ Set.Ioo a b, HasDerivAt φ (γ x) x := by
  obtain ⟨L, hL0, hL⟩ := hL
  -- the `v n` are `L`-Lipschitz on `(a,b)`, uniformly in `n` (mean value theorem)
  have hv_lip : ∀ n, ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, |v n x - v n y| ≤ L * |x - y| := by
    intro n x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := v n) (s := Set.Ioo a b) (C := L)
      (fun z hz => (hvdiff n).differentiableAt (isOpen_Ioo.mem_nhds hz))
      (fun z hz => by rw [Real.norm_eq_abs]; exact hL n z hz)
      (convex_Ioo a b) hx hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    rwa [abs_sub_comm (v n x) (v n y), abs_sub_comm x y]
  -- the limit `γ` inherits the same Lipschitz bound
  have hγ_lip : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, |γ x - γ y| ≤ L * |x - y| := by
    intro x hx y hy
    have hlim : Filter.Tendsto (fun n => |v n x - v n y|) Filter.atTop (nhds |γ x - γ y|) := by
      simpa using ((hv x hx).sub (hv y hy)).abs
    exact le_of_tendsto' hlim (fun n => hv_lip n x hx y hy)
  -- hence `v n → γ` locally uniformly on the open interval
  have hlu : TendstoLocallyUniformlyOn (fun n => v n) γ Filter.atTop (Set.Ioo a b) := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioo]
    intro K hKsub hKc
    exact tendstoUniformlyOn_of_pointwise_of_lipschitzOn hL0
      (fun n x hx y hy => hv_lip n x (hKsub hx) y (hKsub hy))
      (fun x hx y hy => hγ_lip x (hKsub hx) y (hKsub hy)) hKc
      (fun x hx => hv x (hKsub hx))
  intro x hx
  exact hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioo hlu
    (Filter.Eventually.of_forall hder) hu hx

end Work.FTS_RegExport.RXR1
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1Aux.intervalIntegrable_of_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1Aux

theorem intervalIntegrable_of_tendsto {R : ℝ → ℝ → ℝ} {Nz τ : ℝ} (hNz : 0 ≤ Nz)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hlip : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ x ∈ Set.Ioi (0:ℝ), ∀ y ∈ Set.Ioi (0:ℝ),
      |R x s - R y s| ≤ Nz * |x - y|)
    {z' : ℝ} (hz' : 0 < z')
    {u : ℕ → ℝ} (htu : Filter.Tendsto u Filter.atTop (nhds z')) (hu : ∀ n, 0 < u n)
    (hgood : ∀ n, IntervalIntegrable (fun s => R (u n) s) MeasureTheory.volume (0:ℝ) τ) :
    IntervalIntegrable (fun s => R z' s) MeasureTheory.volume (0:ℝ) τ := by
  -- `R (u n) s - R z' s` is bounded by `Nz * |u n - z'|`, which tends to `0`.
  have hlim0 : Filter.Tendsto (fun n => Nz * |u n - z'|) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun n : ℕ => |u n - z'|) Filter.atTop (nhds 0) := by
      have h3 := (htu.sub (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => z') Filter.atTop (nhds z'))).abs
      simpa using h3
    simpa using h2.const_mul Nz
  -- pick one index for which the displacement is at most `1`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Nz * |u N - z'| < 1 :=
    (hlim0.eventually (Iio_mem_nhds zero_lt_one)).exists
  have hsubset : Set.Ioc (0:ℝ) τ ⊆ Set.Icc (0:ℝ) 1 :=
    fun s hs => ⟨le_of_lt hs.1, le_trans hs.2 hτ1⟩
  -- pointwise convergence on the integration interval
  have hconv : ∀ s ∈ Set.Ioc (0:ℝ) τ,
      Filter.Tendsto (fun n => R (u n) s) Filter.atTop (nhds (R z' s)) := by
    intro s hs
    have hs' : s ∈ Set.Icc (0:ℝ) 1 := hsubset hs
    have hb : ∀ n, |R (u n) s - R z' s| ≤ Nz * |u n - z'| :=
      fun n => hlip s hs' (u n) (hu n) z' hz'
    have habs : Filter.Tendsto (fun n => |R (u n) s - R z' s|) Filter.atTop (nhds 0) :=
      squeeze_zero (fun n => abs_nonneg _) hb hlim0
    have hsub : Filter.Tendsto (fun n => R (u n) s - R z' s) Filter.atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using habs)
    have h4 := hsub.add (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => R z' s) Filter.atTop (nhds (R z' s)))
    simpa using h4
  -- hence `R z'` is measurable, as an a.e. limit of the integrable `R (u n)`
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun s => R z' s)
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) τ)) :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun n => (hgood n).1.aestronglyMeasurable)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hconv)
  have hconst : MeasureTheory.Integrable (fun _ : ℝ => (1:ℝ))
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) τ)) :=
    (intervalIntegrable_const (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := τ)
      (c := (1:ℝ))).1
  have hdom : MeasureTheory.Integrable (fun s => ‖R (u N) s‖ + 1)
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) τ)) :=
    ((hgood N).1.norm).add hconst
  -- and it is dominated by the integrable function `|R (u N)| + 1`
  have hbdry : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) τ)),
      ‖R z' s‖ ≤ ‖R (u N) s‖ + 1 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => by
      have hs' : s ∈ Set.Icc (0:ℝ) 1 := hsubset hs
      have h1 : |R (u N) s - R z' s| ≤ Nz * |u N - z'| := hlip s hs' (u N) (hu N) z' hz'
      have h2 : |R z' s - R (u N) s| < 1 := by
        rw [abs_sub_comm]; exact lt_of_le_of_lt h1 hN
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      have h3 : |R z' s| ≤ |R z' s - R (u N) s| + |R (u N) s| :=
        calc |R z' s| = |(R z' s - R (u N) s) + R (u N) s| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      linarith)
  constructor
  · exact MeasureTheory.Integrable.mono' hdom hmeas hbdry
  · rw [Set.Ioc_eq_empty_iff.mpr (not_lt.mpr hτ0)]
    exact MeasureTheory.integrableOn_empty

end Work.FTS_RegExport.RXR1Aux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.Joint.CLM =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXR7

set_option autoImplicit false

/-! ## §1  Elementary continuous-linear-map helpers

`ℝ × ℝ × ℝ` is right-associated: `p = (p.1, p.2.1, p.2.2)`.  We record the three coordinate
functionals, the CLM whose coordinate vector is `(a,b,c)`, the CLM `(z,θ) ↦ a z + b θ`, and the
"boundary" CLM `(z,θ,τ) ↦ L (z,θ) + c τ`. -/

/-- `p ↦ p.1`. -/
def p1 : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

/-- `p ↦ p.2.1`. -/
def p2 : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- `p ↦ p.2.2`. -/
def p3 : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The CLM `(z,θ,τ) ↦ a z + b θ + c τ`. -/
def tripleCLM (a b c : ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := a • p1 + b • p2 + c • p3

/-- The CLM `(z,θ) ↦ a z + b θ`. -/
def pairCLM (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • (ContinuousLinearMap.fst ℝ ℝ ℝ) + b • (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The CLM `(z,θ,τ) ↦ L (z,θ) + c τ` of the boundary derivative. -/
def bdryCLM (L : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  L.comp ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
    + c • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

theorem tripleCLM_apply (a b c : ℝ) (v : ℝ × ℝ × ℝ) :
    tripleCLM a b c v = a * v.1 + b * v.2.1 + c * v.2.2 := by
  simp [tripleCLM, p1, p2, p3]

theorem pairCLM_apply (a b : ℝ) (v : ℝ × ℝ) : pairCLM a b v = a * v.1 + b * v.2 := by
  simp [pairCLM]

theorem bdryCLM_apply (L : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ) (v : ℝ × ℝ × ℝ) :
    bdryCLM L c v = L (v.1, v.2.1) + c * v.2.2 := by
  simp [bdryCLM]

theorem tripleCLM_add (a b c a' b' c' : ℝ) :
    tripleCLM a b c + tripleCLM a' b' c' = tripleCLM (a + a') (b + b') (c + c') := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [add_apply, tripleCLM_apply, tripleCLM_apply, tripleCLM_apply]
  ring

theorem pairCLM_add (a b a' b' : ℝ) :
    pairCLM a b + pairCLM a' b' = pairCLM (a + a') (b + b') := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [add_apply, pairCLM_apply, pairCLM_apply, pairCLM_apply]
  ring

theorem bdryCLM_pairCLM (a b c : ℝ) : bdryCLM (pairCLM a b) c = tripleCLM a b c := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [bdryCLM_apply, tripleCLM_apply, pairCLM_apply]

/-- A CLM `(ℝ×ℝ×ℝ) →L ℝ` is determined by its values on the three coordinate vectors. -/
theorem clm_ext_triple {L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ} {a b c : ℝ}
    (h1 : L (1, 0, 0) = a) (h2 : L (0, 1, 0) = b) (h3 : L (0, 0, 1) = c) :
    L = tripleCLM a b c := by
  refine ContinuousLinearMap.ext fun p => ?_
  have hp : p = p.1 • (1, 0, 0) + p.2.1 • ((0, 1, 0) : ℝ × ℝ × ℝ) + p.2.2 • (0, 0, 1) := by
    ext <;> simp
  conv_lhs => rw [hp]
  rw [map_add, map_add, map_smul, map_smul, map_smul, h1, h2, h3, tripleCLM_apply]
  simp only [smul_eq_mul]
  ring

/-- A CLM `(ℝ×ℝ) →L ℝ` is determined by its values on the two coordinate vectors. -/
theorem clm_ext_pair {L : (ℝ × ℝ) →L[ℝ] ℝ} {a b : ℝ}
    (h1 : L (1, 0) = a) (h2 : L (0, 1) = b) : L = pairCLM a b := by
  refine ContinuousLinearMap.ext fun q => ?_
  have hq : q = q.1 • (1, 0) + q.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  conv_lhs => rw [hq]
  rw [map_add, map_smul, map_smul, h1, h2, pairCLM_apply]
  simp only [smul_eq_mul]
  ring

/-- The first coordinate of a `HasFDerivAt` is the derivative of the corresponding slice. -/
theorem fderiv_apply_e1 {Φ : ℝ × ℝ × ℝ → ℝ} {L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ} {x : ℝ × ℝ × ℝ}
    (hL : HasFDerivAt Φ L x) : L (1, 0, 0) = deriv (fun z => Φ (z, x.2.1, x.2.2)) x.1 := by
  have hc : HasDerivAt (fun t : ℝ => (t, x.2.1, x.2.2)) (1, 0, 0) x.1 := by
    simpa using (hasDerivAt_id x.1).prodMk
      ((hasDerivAt_const x.1 x.2.1).prodMk (hasDerivAt_const x.1 x.2.2))
  have hd := (hL.comp_hasDerivAt x.1 hc).deriv
  simpa [Function.comp_def] using hd.symm

/-- The second coordinate of a `HasFDerivAt` is the derivative of the corresponding slice. -/
theorem fderiv_apply_e2 {Φ : ℝ × ℝ × ℝ → ℝ} {L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ} {x : ℝ × ℝ × ℝ}
    (hL : HasFDerivAt Φ L x) : L (0, 1, 0) = deriv (fun θ => Φ (x.1, θ, x.2.2)) x.2.1 := by
  have hc : HasDerivAt (fun t : ℝ => (x.1, t, x.2.2)) (0, 1, 0) x.2.1 := by
    simpa using (hasDerivAt_const x.2.1 x.1).prodMk
      ((hasDerivAt_id x.2.1).prodMk (hasDerivAt_const x.2.1 x.2.2))
  have hd := (hL.comp_hasDerivAt x.2.1 hc).deriv
  simpa [Function.comp_def] using hd.symm

/-- The third coordinate of a `HasFDerivAt` is the derivative of the corresponding slice. -/
theorem fderiv_apply_e3 {Φ : ℝ × ℝ × ℝ → ℝ} {L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ} {x : ℝ × ℝ × ℝ}
    (hL : HasFDerivAt Φ L x) : L (0, 0, 1) = deriv (fun τ => Φ (x.1, x.2.1, τ)) x.2.2 := by
  have hc : HasDerivAt (fun t : ℝ => (x.1, x.2.1, t)) (0, 0, 1) x.2.2 := by
    simpa using (hasDerivAt_const x.2.2 x.1).prodMk
      ((hasDerivAt_const x.2.2 x.2.1).prodMk (hasDerivAt_id x.2.2))
  have hd := (hL.comp_hasDerivAt x.2.2 hc).deriv
  simpa [Function.comp_def] using hd.symm

theorem fderiv_apply_2d_1 {Φ : ℝ × ℝ → ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ} {x : ℝ × ℝ}
    (hL : HasFDerivAt Φ L x) : L (1, 0) = deriv (fun z => Φ (z, x.2)) x.1 := by
  have hc : HasDerivAt (fun t : ℝ => (t, x.2)) (1, 0) x.1 := by
    simpa using (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
  have hd := (hL.comp_hasDerivAt x.1 hc).deriv
  simpa [Function.comp_def] using hd.symm

theorem fderiv_apply_2d_2 {Φ : ℝ × ℝ → ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ} {x : ℝ × ℝ}
    (hL : HasFDerivAt Φ L x) : L (0, 1) = deriv (fun θ => Φ (x.1, θ)) x.2 := by
  have hc : HasDerivAt (fun t : ℝ => (x.1, t)) (0, 1) x.2 := by
    simpa using (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
  have hd := (hL.comp_hasDerivAt x.2 hc).deriv
  simpa [Function.comp_def] using hd.symm

end Work.FTS_RegExport.RXR7
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.Support.hasFDerivWithinAt_of_ftc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR7.Support

open Set Filter MeasureTheory
open scoped Topology

/-- The parametric fundamental theorem of calculus at a degenerate interval: if the
uncurried `κ` is continuous on `A ×ˢ B ×ˢ Icc 0 S`, then
`p ↦ ∫ s in 0..p.2.2, κ p.1 p.2.1 s` has derivative `κ z θ 0` in the `τ`-direction at
`(z,θ,0)`, within `A ×ˢ B ×ˢ Icc 0 S`. -/
theorem hasFDerivWithinAt_intervalIntegral_of_continuousOn {A B : Set ℝ} {S : ℝ} (hS0 : 0 ≤ S)
    {κ : ℝ → ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ∈ A) (hθ : θ ∈ B)
    (hκ : ContinuousOn (fun p : ℝ × ℝ × ℝ => κ p.1 p.2.1 p.2.2) (A ×ˢ B ×ˢ Set.Icc (0:ℝ) S)) :
    HasFDerivWithinAt (fun p : ℝ × ℝ × ℝ => ∫ s in (0:ℝ)..p.2.2, κ p.1 p.2.1 s)
      ((κ z θ 0) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
      (A ×ˢ B ×ˢ Set.Icc (0:ℝ) S) (z, θ, 0) := by
  set s : Set (ℝ × ℝ × ℝ) := A ×ˢ B ×ˢ Set.Icc (0:ℝ) S with hs
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hp0 : (z, θ, 0) ∈ s := by
    rw [hs]; simp only [Set.mem_prod, Set.mem_Icc]
    exact ⟨hz, hθ, le_rfl, hS0⟩
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousWithinAt_iff.mp (hκ.continuousWithinAt hp0)) c hc
  have hmem : Metric.ball (z, θ, 0) (δ / 2) ∩ s ∈ 𝓝[s] (z, θ, 0) := by
    change _ ∈ _root_.nhds (z,θ,0) ⊓ Filter.principal s
    exact Filter.mem_inf_iff.mpr ⟨_, Metric.ball_mem_nhds (z,θ,0) (by linarith), _,
      Filter.mem_principal_self _, rfl⟩
  refine Filter.mem_of_superset hmem ?_
  intro p hp
  rw [Set.mem_inter_iff, Metric.mem_ball] at hp
  obtain ⟨hdp, hps⟩ := hp
  obtain ⟨hzp, hθp, hτp⟩ : p.1 ∈ A ∧ p.2.1 ∈ B ∧ p.2.2 ∈ Set.Icc (0:ℝ) S := by
    rw [hs] at hps; simpa only [Set.mem_prod] using hps
  have hτ0 : 0 ≤ p.2.2 := hτp.1
  have hτS : p.2.2 ≤ S := hτp.2
  have hmaps : Set.MapsTo (fun x : ℝ => ((p.1, p.2.1, x) : ℝ × ℝ × ℝ))
      (Set.uIcc 0 p.2.2) s := by
    intro x hx
    rw [Set.uIcc_of_le hτ0, Set.mem_Icc] at hx
    rw [hs]
    simp only [Set.mem_prod, Set.mem_Icc]
    exact ⟨hzp, hθp, hx.1, le_trans hx.2 hτS⟩
  have hcontSlice : ContinuousOn (fun x : ℝ => κ p.1 p.2.1 x) (Set.uIcc 0 p.2.2) := by
    have hh := hκ.comp
      ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn) hmaps
    simpa [Function.comp_def] using hh
  have hint : IntervalIntegrable (fun x : ℝ => κ p.1 p.2.1 x) volume 0 p.2.2 :=
    hcontSlice.intervalIntegrable
  show ‖(∫ s in (0:ℝ)..p.2.2, κ p.1 p.2.1 s) - (∫ s in (0:ℝ)..(0:ℝ), κ z θ s) -
      ((κ z θ 0) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
        (p - (z, θ, 0))‖ ≤ c * ‖p - (z, θ, 0)‖
  have hL : ((κ z θ 0) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
      (p - (z, θ, 0)) = (κ z θ 0) * p.2.2 := by
    rw [smul_apply]
    have hc2 : ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
        (p - (z, θ, 0)) = p.2.2 := by
      rw [ContinuousLinearMap.comp_apply]
      simp
    rw [hc2, smul_eq_mul]
  have hbound : ∀ x ∈ Set.uIoc (0:ℝ) p.2.2, ‖κ p.1 p.2.1 x - κ z θ 0‖ ≤ c := by
    intro x hx
    rw [Set.uIoc_of_le hτ0, Set.mem_Ioc] at hx
    obtain ⟨hx0, hxτ⟩ := hx
    have hxmem : ((p.1, p.2.1, x) : ℝ × ℝ × ℝ) ∈ s := by
      rw [hs]; simp only [Set.mem_prod, Set.mem_Icc]
      exact ⟨hzp, hθp, le_of_lt hx0, le_trans hxτ hτS⟩
    have hdistle : dist ((p.1, p.2.1, x) : ℝ × ℝ × ℝ) (z, θ, 0) ≤ dist p (z, θ, 0) := by
      rw [dist_eq_norm, dist_eq_norm]
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_zero, Real.norm_eq_abs]
      refine max_le_max le_rfl (max_le_max le_rfl ?_)
      rw [abs_of_pos hx0, abs_of_nonneg hτ0]
      exact hxτ
    have hlt : dist (κ p.1 p.2.1 x) (κ z θ 0) < c := by
      have hh := hδ hxmem (lt_of_le_of_lt hdistle (lt_of_lt_of_le hdp (by linarith)))
      simpa using hh
    rw [dist_eq_norm] at hlt
    exact le_of_lt hlt
  have heq : ((∫ s in (0:ℝ)..p.2.2, κ p.1 p.2.1 s) - (∫ s in (0:ℝ)..(0:ℝ), κ z θ s))
      - ((κ z θ 0) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
        (p - (z, θ, 0))
      = ∫ x in (0:ℝ)..p.2.2, (κ p.1 p.2.1 x - κ z θ 0) := by
    rw [hL]
    have hdeg : (∫ s in (0:ℝ)..(0:ℝ), κ z θ s) = 0 := by
      simp [intervalIntegral.integral_same]
    rw [hdeg, sub_zero]
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hple : p.2.2 ≤ ‖p - (z, θ, 0)‖ := by
    have h1 : ‖(p - (z, θ, 0)).2.2‖ ≤ ‖p - (z, θ, 0)‖ :=
      le_trans (norm_snd_le _) (norm_snd_le _)
    have h2 : (p - (z, θ, 0)).2.2 = p.2.2 := by simp
    rw [h2, Real.norm_of_nonneg hτ0] at h1
    exact h1
  rw [heq]
  calc ‖∫ x in (0:ℝ)..p.2.2, (κ p.1 p.2.1 x - κ z θ 0)‖
      ≤ c * |p.2.2 - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = c * p.2.2 := by rw [sub_zero, abs_of_nonneg hτ0]
    _ ≤ c * ‖p - (z, θ, 0)‖ := mul_le_mul_of_nonneg_left hple hc.le

theorem hasFDerivWithinAt_of_ftc {A B : Set ℝ} {S : ℝ} (hS0 : 0 ≤ S)
    {h : ℝ → ℝ → ℝ → ℝ} {h₀ : ℝ → ℝ → ℝ} {κ : ℝ → ℝ → ℝ → ℝ}
    {z θ : ℝ} (hz : z ∈ A) (hθ : θ ∈ B) {L₀ : (ℝ × ℝ) →L[ℝ] ℝ}
    (hderiv₀ : HasFDerivAt (fun q : ℝ × ℝ => h₀ q.1 q.2) L₀ (z, θ))
    (hftc : ∀ z' ∈ A, ∀ θ' ∈ B, ∀ τ ∈ Set.Icc (0:ℝ) S,
      h z' θ' τ - h₀ z' θ' = ∫ s in (0:ℝ)..τ, κ z' θ' s)
    (hκ : ContinuousOn (fun p : ℝ × ℝ × ℝ => κ p.1 p.2.1 p.2.2) (A ×ˢ B ×ˢ Set.Icc (0:ℝ) S)) :
    HasFDerivWithinAt (fun p : ℝ × ℝ × ℝ => h p.1 p.2.1 p.2.2)
      (L₀.comp ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
        + (κ z θ 0) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
            (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
      (A ×ˢ B ×ˢ Set.Icc (0:ℝ) S) (z, θ, 0) := by
  have hp0 : (z, θ, 0) ∈ A ×ˢ B ×ˢ Set.Icc (0:ℝ) S := by
    simp only [Set.mem_prod, Set.mem_Icc]
    exact ⟨hz, hθ, le_rfl, hS0⟩
  -- the `(z,θ)`-part: `h₀` composed with the linear projection `p ↦ (p.1, p.2.1)`
  have h1 : HasFDerivWithinAt (fun p : ℝ × ℝ × ℝ => h₀ p.1 p.2.1)
      (L₀.comp ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))))
      (A ×ˢ B ×ˢ Set.Icc (0:ℝ) S) (z, θ, 0) := by
    have hh := hderiv₀.comp_hasFDerivWithinAt (z, θ, 0)
      ((ContinuousLinearMap.hasFDerivAt ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))).hasFDerivWithinAt
            (s := A ×ˢ B ×ˢ Set.Icc (0:ℝ) S))
    simpa [Function.comp_def] using hh
  -- the `τ`-part: the parametric FTC at the degenerate interval
  have h2 := hasFDerivWithinAt_intervalIntegral_of_continuousOn hS0 hz hθ hκ
  have hsum := h1.add h2
  -- replace `h₀ + ∫` by `h` on the whole set
  have hEqOn : Set.EqOn (fun p : ℝ × ℝ × ℝ => h p.1 p.2.1 p.2.2)
      (fun p : ℝ × ℝ × ℝ => h₀ p.1 p.2.1 + ∫ s in (0:ℝ)..p.2.2, κ p.1 p.2.1 s)
      (A ×ˢ B ×ˢ Set.Icc (0:ℝ) S) := by
    intro p hp
    obtain ⟨hzp, hθp, hτp⟩ : p.1 ∈ A ∧ p.2.1 ∈ B ∧ p.2.2 ∈ Set.Icc (0:ℝ) S := by
      simpa only [Set.mem_prod] using hp
    have hh := hftc p.1 hzp p.2.1 hθp p.2.2 hτp
    linarith [hh]
  exact hsum.congr hEqOn (hEqOn hp0)

end Work.FTS_RegExport.RXR7.Support
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.majorant_tail =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `majorant_tail`: the tail bound for `s ↦ s^{1/2}/(1+s)²`

For every `z > 0` the function `maj s = s ^ (1/2) / (1 + s) ^ 2` is integrable on `(z, ∞)`
and its tail integral is at most `3`.

The tail integral is actually convergent as `z → 0⁺` with value `π/2 ≈ 1.571`, but only the
crude constant `3` is needed.  The proof splits the halfline at `1`:

* `maj s ≤ s ^ (-3/2)` for `s ≥ 1`, and `∫_1^∞ s^{-3/2} = 2`;
* `maj s ≤ s ^ (1/2)` for `0 < s ≤ 1`, and `∫_z^1 s^{1/2} = (2/3)(1 - z^{3/2}) ≤ 2/3`.

Hence `∫_z^∞ maj ≤ 2/3 + 2 = 8/3 ≤ 3`.  The two pieces are glued by
`intervalIntegral.integral_interval_add_Ioi'` (`∫_z^1 + ∫_1^∞ = ∫_z^∞`, valid for *every*
`z`, so no case distinction is needed in the glueing step), and the integrability on
`(z, ∞)` follows from `(z,∞) ⊆ (z,1] ∪ (1,∞)` together with `IntegrableOn.union`.
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

/-- The integrand `s^{1/2}/(1+s)²` of the tail majorant. -/
private noncomputable def maj (s : ℝ) : ℝ := s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2

/-- `maj` is continuous on the open halfline `(0,∞)`. -/
private lemma maj_cont : ContinuousOn maj (Ioi 0) := by
  have hfe : maj = fun s : ℝ => Real.sqrt s / (1 + s) ^ 2 := by
    funext s; simp only [maj, Real.sqrt_eq_rpow]
  rw [hfe]
  refine ContinuousOn.div Real.continuous_sqrt.continuousOn ?_ (fun x hx => ?_)
  · exact ((continuous_const.add continuous_id).pow 2).continuousOn
  · have hx0 : 0 < x := hx
    positivity

/-- `s ↦ s^{1/2}` is continuous on `(0,∞)`. -/
private lemma sqr_cont : ContinuousOn (fun s : ℝ => s ^ ((1 : ℝ) / 2)) (Ioi 0) := by
  have hfe : (fun s : ℝ => s ^ ((1 : ℝ) / 2)) = fun s : ℝ => Real.sqrt s := by
    funext s; rw [Real.sqrt_eq_rpow]
  rw [hfe]; exact Real.continuous_sqrt.continuousOn

private lemma maj_cont_uIcc {z : ℝ} (hz : 0 < z) : ContinuousOn maj (uIcc z 1) :=
  maj_cont.mono (by intro s hs; exact lt_of_lt_of_le (lt_min hz zero_lt_one) hs.1)

private lemma sqr_cont_uIcc {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun s : ℝ => s ^ ((1 : ℝ) / 2)) (uIcc z 1) :=
  sqr_cont.mono (by intro s hs; exact lt_of_lt_of_le (lt_min hz zero_lt_one) hs.1)

/-- Pointwise domination on `(1,∞)`: `maj s ≤ s ^ (-3/2)`. -/
private lemma maj_le_rpow_neg {a : ℝ} (ha : (1 : ℝ) < a) :
    maj a ≤ a ^ (-(3 : ℝ) / 2) := by
  have ha1 : 0 < a := by linarith
  have hle : a ^ 2 ≤ (1 + a) ^ 2 := by
    have h1 : (0 : ℝ) ≤ a := le_of_lt ha1
    have h2 : a ≤ 1 + a := by linarith
    exact pow_le_pow_left₀ h1 h2 2
  have h := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ a ^ ((1 : ℝ) / 2))
    (by positivity : (0 : ℝ) < a ^ 2) hle
  simp only [maj]
  refine le_trans h ?_
  rw [show (-(3 : ℝ) / 2) = (1 : ℝ) / 2 - 2 by norm_num, ← Real.rpow_natCast a 2]
  exact le_of_eq (Real.rpow_sub ha1 (1 / 2) 2).symm

/-- `maj` is integrable on `(1,∞)`. -/
private lemma maj_int_one : IntegrableOn maj (Ioi 1) := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hcont : ContinuousOn maj (Ioi 1) :=
    maj_cont.mono (by intro s hs; exact lt_trans zero_lt_one (mem_Ioi.mp hs))
  refine hbase.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  have ha1 : 0 < a := by linarith [mem_Ioi.mp ha]
  have hnn : (0 : ℝ) ≤ a ^ ((1 : ℝ) / 2) / (1 + a) ^ 2 :=
    div_nonneg (Real.rpow_nonneg ha1.le _) (sq_nonneg _)
  have hle := maj_le_rpow_neg (mem_Ioi.mp ha)
  simp only [maj]
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

/-- `∫_1^∞ maj ≤ 2`. -/
private lemma maj_val_one : ∫ s in Ioi (1 : ℝ), maj s ≤ 2 := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hb : ∫ t in Ioi (1 : ℝ), t ^ (-(3 : ℝ) / 2) = 2 := by
    rw [integral_Ioi_rpow_of_lt (a := -(3 : ℝ) / 2) (c := 1) (by norm_num) (by norm_num)]
    norm_num
  have hmono := setIntegral_mono_ae_restrict maj_int_one hbase (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact maj_le_rpow_neg (mem_Ioi.mp ha))
  rw [hb] at hmono
  exact hmono

/-- `∫_z^1 maj ≤ 2/3` for every `z > 0`. -/
private lemma maj_interval_le {z : ℝ} (hz : 0 < z) : ∫ s in z..1, maj s ≤ 2 / 3 := by
  by_cases h : z ≤ 1
  · have hmono := intervalIntegral.integral_mono_on h
      ((maj_cont_uIcc hz).intervalIntegrable (μ := volume))
      ((sqr_cont_uIcc hz).intervalIntegrable (μ := volume)) (fun x hx => by
        have hx0 : 0 < x := lt_of_lt_of_le hz hx.1
        have h1x : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith [hx0]
        simp only [maj]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + x) ^ 2)]
        exact le_mul_of_one_le_right (by positivity) h1x)
    have hval : ∫ x in z..1, x ^ ((1 : ℝ) / 2) = (1 - z ^ ((3 : ℝ) / 2)) / ((3 : ℝ) / 2) := by
      rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2)), Real.one_rpow]
      norm_num
    rw [hval] at hmono
    have hz32 : (0 : ℝ) ≤ z ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hz.le _
    linarith
  · push Not at h
    rw [intervalIntegral.integral_symm (a := 1) (b := z)]
    have hnn : 0 ≤ ∫ x in 1..z, maj x :=
      intervalIntegral.integral_nonneg h.le (fun u hu => by
        have hu0 : (0 : ℝ) < u := by linarith [hu.1]
        have hnum : (0 : ℝ) ≤ u ^ ((1 : ℝ) / 2) / (1 + u) ^ 2 :=
          div_nonneg (Real.rpow_nonneg hu0.le _) (sq_nonneg _)
        simpa only [maj] using hnum)
    linarith

/-- `maj` is integrable on `(z,∞)` for `z > 0`. -/
private lemma maj_int_Ioi {z : ℝ} (hz : 0 < z) : IntegrableOn maj (Ioi z) := by
  have hii : IntervalIntegrable maj volume z 1 := (maj_cont_uIcc hz).intervalIntegrable
  have hU : IntegrableOn maj (Ioc z 1 ∪ Ioi 1) := hii.1.union maj_int_one
  refine hU.mono_set ?_
  intro s hs
  by_cases hs1 : s ≤ 1
  · exact Or.inl ⟨mem_Ioi.mp hs, hs1⟩
  · exact Or.inr (lt_of_not_ge hs1)

theorem majorant_tail {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) (Set.Ioi z) ∧
      ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ 3 := by
  have hii : IntervalIntegrable maj volume z 1 := (maj_cont_uIcc hz).intervalIntegrable
  have hdec := intervalIntegral.integral_interval_add_Ioi' hii maj_int_one
  have hz1 : ∫ s in z..1, maj s ≤ 2 / 3 := maj_interval_le hz
  have hone : ∫ s in Ioi (1 : ℝ), maj s ≤ 2 := maj_val_one
  have hint : IntegrableOn maj (Ioi z) := maj_int_Ioi hz
  have hcalc : ∫ s in Ioi z, maj s ≤ 3 := by linarith
  exact ⟨hint, hcalc⟩

end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.MajorantPieces.sqrt_div_sq_Ioi_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS_RegExport.RXT.Sys.MajorantPieces

/-- The majorant weight `√s/(1+s)²` is integrable on `(z, ∞)` and its integral is `≤ 3`,
for every `z ≥ 0`.

The pointwise bound `s^{1/2}/(1+s)² ≤ (1+s)^{-3/2}` (valid since `s ≤ 1+s`) reduces both
statements to the elementary improper integral `∫_z^∞ (1+s)^{-3/2} ds = 2(1+z)^{-1/2} ≤ 2`,
computed by the fundamental theorem of calculus with the antiderivative
`s ↦ -2(1+s)^{-1/2}`. -/
theorem sqrt_div_sq_Ioi_integral_le {z : ℝ} (hz : 0 ≤ z) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) (Set.Ioi z) ∧
      (∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) ≤ 3 := by
  have hmeas : Measurable (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by measurability
  -- the dominating function `(1+s)^{-3/2}` is integrable on `(z,∞)`
  have hg : IntegrableOn (fun s : ℝ => (1 + s) ^ (-((3 : ℝ) / 2))) (Set.Ioi z) := by
    have h := integrableOn_add_rpow_Ioi_of_lt (a := -((3 : ℝ) / 2)) (c := z)
      (m := (1 : ℝ)) (by norm_num) (by linarith)
    simpa [add_comm] using h
  -- pointwise bound
  have hle : ∀ s ∈ Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ (1 + s) ^ (-((3 : ℝ) / 2)) := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := le_of_lt (lt_of_le_of_lt hz (Set.mem_Ioi.mp hs))
    have h1 : (0 : ℝ) < 1 + s := by linarith
    have hbase : s ^ ((1 : ℝ) / 2) ≤ (1 + s) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow hs0 (by linarith) (by norm_num)
    have hinv : (0 : ℝ) ≤ ((1 + s) ^ 2)⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_right hbase hinv
    have hpow : (1 + s) ^ ((1 : ℝ) / 2) * ((1 + s) ^ 2)⁻¹ = (1 + s) ^ (-((3 : ℝ) / 2)) := by
      rw [← Real.rpow_two, ← Real.rpow_neg (le_of_lt h1), ← Real.rpow_add h1]
      congr 1
      norm_num
    calc s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2
        = s ^ ((1 : ℝ) / 2) * ((1 + s) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (1 + s) ^ ((1 : ℝ) / 2) * ((1 + s) ^ 2)⁻¹ := hmul
      _ = (1 + s) ^ (-((3 : ℝ) / 2)) := hpow
  have hf_int : IntegrableOn (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) (Set.Ioi z) := by
    refine Integrable.mono' hg hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) ≤ s := le_of_lt (lt_of_le_of_lt hz (Set.mem_Ioi.mp hs))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle s hs
  -- the exact value of the dominating integral
  have hIntEq : ∫ s in Set.Ioi z, (1 + s) ^ (-((3 : ℝ) / 2)) = 2 * (1 + z) ^ (-((1 : ℝ) / 2)) := by
    have hderiv : ∀ x ∈ Set.Ici z,
        HasDerivAt (fun s : ℝ => -2 * (1 + s) ^ (-((1 : ℝ) / 2))) ((1 + x) ^ (-((3 : ℝ) / 2))) x := by
      intro x hx
      have hxz : z ≤ x := Set.mem_Ici.mp hx
      have hpos : (0 : ℝ) < 1 + x := by linarith
      have hd0 : HasDerivAt (fun s : ℝ => 1 + s) (1 : ℝ) x := by
        simpa using (hasDerivAt_id x).const_add (1 : ℝ)
      have hd1 : HasDerivAt (fun s : ℝ => (1 + s) ^ (-((1 : ℝ) / 2)))
          (1 * (-((1 : ℝ) / 2)) * (1 + x) ^ (-((1 : ℝ) / 2) - 1)) x :=
        hd0.rpow_const (p := -((1 : ℝ) / 2)) (Or.inl (ne_of_gt hpos))
      have hd2 := hd1.const_mul (-2)
      have hexp : -((1 : ℝ) / 2) - 1 = -((3 : ℝ) / 2) := by norm_num
      rw [hexp] at hd2
      convert hd2 using 1
      ring
    have htend : Tendsto (fun s : ℝ => -2 * (1 + s) ^ (-((1 : ℝ) / 2))) atTop (𝓝 0) := by
      have hq : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
      have h1 : Tendsto (fun s : ℝ => (1 + s) ^ (-((1 : ℝ) / 2))) atTop (𝓝 0) := by
        simpa only [Function.comp_def, id_eq] using (tendsto_rpow_neg_atTop hq).comp
          (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
      simpa using h1.const_mul (-2)
    have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hg htend
    simpa using hmain
  refine ⟨hf_int, ?_⟩
  have hmono : ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤
      ∫ s in Set.Ioi z, (1 + s) ^ (-((3 : ℝ) / 2)) :=
    setIntegral_mono_on hf_int hg measurableSet_Ioi hle
  have hfin : (1 + z) ^ (-((1 : ℝ) / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  linarith

end Work.FTS_RegExport.RXT.Sys.MajorantPieces
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.aestronglyMeasurable_restrict_of_ae_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

theorem aestronglyMeasurable_restrict_of_ae_eq {F G : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hG : Measurable G) (h : ∀ x ∈ s, F x = G x) :
    MeasureTheory.AEStronglyMeasurable F (MeasureTheory.volume.restrict s) := by
  have hG' : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict s) :=
    hG.stronglyMeasurable.aestronglyMeasurable
  refine hG'.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem hs] with x hx
  exact (h x hx).symm

end Work.FTS_RegExport.RXT.Sys
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.integrableOn_Ioc_of_abs_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS_RegExport.RXT.Sys

theorem integrableOn_Ioc_of_abs_bound {S C : ℝ} (hC : 0 ≤ C) {f : ℝ → ℝ}
    (hm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) S)))
    (hb : ∀ σ ∈ Set.Ioc (0 : ℝ) S, |f σ| ≤ C) :
    MeasureTheory.IntegrableOn f (Set.Ioc (0 : ℝ) S) MeasureTheory.volume := by
  -- `Ioc 0 S` has finite Lebesgue measure, and `f` is bounded on it by `C`, so
  -- the Bochner integral converges absolutely.
  refine MeasureTheory.IntegrableOn.of_bound ?_ hm C ?_
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    exact hb x hx

end Work.FTS_RegExport.RXT.Sys
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.intervalIntegrable_if_zero_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

theorem intervalIntegrable_if_zero_add {S : ℝ} (hS : 0 < S) {F A B : ℝ → ℝ}
    (hF : IntervalIntegrable F MeasureTheory.volume 0 S)
    (hA : ContinuousOn A (Set.Icc 0 S)) (hB : ContinuousOn B (Set.Icc 0 S)) :
    IntervalIntegrable (fun τ => (if τ = 0 then 0 else F τ) + A τ + B τ)
      MeasureTheory.volume 0 S := by
  have hSle : (0 : ℝ) ≤ S := le_of_lt hS
  -- The modified function agrees with `F` on the (open) interval of integration.
  have hF0 :
      IntervalIntegrable (fun τ => if τ = 0 then 0 else F τ) MeasureTheory.volume 0 S := by
    refine hF.congr_uIoo ?_
    intro τ hτ
    rw [Set.uIoo_of_le hSle] at hτ
    simp only
    rw [ite_eq_right (ne_of_gt hτ.1)]
  -- `A + B` is continuous on `[0, S]`, hence interval integrable.
  have hAB : IntervalIntegrable (A + B) MeasureTheory.volume 0 S :=
    (hA.add hB).intervalIntegrable_of_Icc hSle
  have h := hF0.add hAB
  simpa [Pi.add_apply, add_assoc] using h

end Work.FTS_RegExport.RXT.Sys
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.intervalIntegral_if_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

theorem intervalIntegral_if_zero {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) :
    (∫ σ in a..b, (if σ = 0 then 0 else f σ)) = ∫ σ in a..b, f σ := by
  -- The two integrands differ only on the null set `{0}`, so their interval
  -- integrals agree (the hypothesis `ha` is not needed).
  have _ : 0 ≤ a := ha
  apply intervalIntegral.integral_congr_ae
  filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume : MeasureTheory.Measure ℝ) 0]
    with x hx _
  simp [hx]

end Work.FTS_RegExport.RXT.Sys
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.dense_diffAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.SysAux.dense_diffAt` — the core of the `Corr`-lemma of S6

The key structural input for the decomposition of `bR = Vθ7/sin 2θ` in the leaf
`Work.FTS_RegExport.RXT.Sys.forcing_bound` (see `RXT/Sys/NOTES_forcing_bound.md` §3):
the stream function `Φ = ΦR α Φs E g` is `Φs + E(slice G)`, an *arbitrary* function of `(z,θ)`
as far as the hypotheses of S6 are concerned, so the additivity
`Uop β Φ = Uop β Φ̃ + Uop β (Θ β F)` — equivalently `deriv_sub` on the `z`-slices — is not
available.  This file proves the substitute: the non-differentiability set of a slice has empty
interior (because on an interval the definition of `bR` forces `Φ = -sin 2θ·b/6`), whence the
differentiable points are dense and, by continuity, the *correction*
`Corr = bR - 2W - 2·Uop β (Θ β F)/sin 2θ` vanishes identically.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

/-- **Density of the differentiability points.**  If a slice of `Φ` satisfies the pointwise
identity `b z θ = 2·(-3·Φ z θ - β·z·(∂_zΦ)(z,θ))/sin 2θ` with `b(·,θ)` differentiable on `(0,∞)`,
then every open interval of `(0,∞)` contains a point at which the slice `z ↦ Φ z θ` is
differentiable.  (Equivalently: the non-differentiability set of the slice has empty interior,
because on an interval the identity forces `Φ = -sin 2θ·b/6`.) -/
theorem exists_differentiableAt_of_slice_identity {β θ : ℝ} {b Φ : ℝ → ℝ → ℝ} (hβ : 0 < β)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hb : ∀ z : ℝ, 0 < z →
      b z θ = 2 * (-3 * Φ z θ - β * z * deriv (fun z' => Φ z' θ) z) / Real.sin (2 * θ))
    (hbd : DifferentiableOn ℝ (fun z : ℝ => b z θ) (Set.Ioi 0))
    {a c : ℝ} (ha : 0 < a) (hac : a < c) :
    ∃ z ∈ Set.Ioo a c, DifferentiableAt ℝ (fun z' : ℝ => Φ z' θ) z := by
  by_contra hcon
  push Not at hcon
  have hθπ : 2 * θ < Real.pi := by linarith
  have hsin : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) hθπ)
  -- on `(a,c)` the slice is nowhere differentiable, so `deriv` vanishes there
  have hzero : ∀ z ∈ Set.Ioo a c, deriv (fun z' : ℝ => Φ z' θ) z = 0 := fun z hz =>
    deriv_zero_of_not_differentiableAt (hcon z hz)
  -- hence `Φ(·,θ)` coincides on `(a,c)` with `-sin 2θ·b(·,θ)/6`
  have hEq : Set.EqOn (fun z => Φ z θ) (fun z => -(Real.sin (2 * θ) * b z θ) / 6)
      (Set.Ioo a c) := by
    intro z hz
    have hz0 : 0 < z := lt_trans ha hz.1
    have h := hb z hz0
    rw [hzero z hz] at h
    have h6 : 6 * Φ z θ = -(2 * (-3 * Φ z θ)) := by ring
    field_simp at h
    linarith [h]
  -- and the latter is differentiable on the interval
  have hd : DifferentiableOn ℝ (fun z => -(Real.sin (2 * θ) * b z θ) / 6) (Set.Ioo a c) := by
    have hsub : Set.Ioo a c ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_trans ha hz.1
    have h1 : DifferentiableOn ℝ (fun z : ℝ => Real.sin (2 * θ) * b z θ) (Set.Ioo a c) :=
      (hbd.mono hsub).const_mul _
    exact (h1.neg).div_const 6
  obtain ⟨z, hz⟩ : (Set.Ioo a c).Nonempty := Set.nonempty_Ioo.mpr hac
  refine hcon z hz ?_
  have hev : (fun z' => -(Real.sin (2 * θ) * b z' θ) / 6) =ᶠ[𝓝 z] (fun z' => Φ z' θ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with y hy
    exact (hEq hy).symm
  exact (hd.differentiableAt (isOpen_Ioo.mem_nhds hz)).congr_of_eventuallyEq hev.symm

end Work.FTS_RegExport.RXT.SysAux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.cone_max_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary real-analysis lemmas for `cone_max_principle`

Helpers for the cone maximum principle for a first-order transport equation with bounded
coefficients (`Work.FTS_RegExport.RXT.cone_max_principle`).
-/

namespace Work.FTS_RegExport.RXT

namespace ConeAux

/-- `(1-u) * exp (2u) ≥ 1` for `u ∈ [0, 1/2]`. -/
lemma one_le_one_sub_mul_exp {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    1 ≤ (1 - u) * Real.exp (2 * u) := by
  have hexp : 2 * u + 1 ≤ Real.exp (2 * u) := Real.add_one_le_exp (2 * u)
  have h1u : 0 ≤ 1 - u := by linarith
  have h2 : (1 - u) * (2 * u + 1) ≤ (1 - u) * Real.exp (2 * u) :=
    mul_le_mul_of_nonneg_left hexp h1u
  have h3 : 1 ≤ (1 - u) * (2 * u + 1) := by nlinarith
  linarith

/-- `1/(1-u) ≤ exp (2u)` for `u ∈ [0, 1/2]`. -/
lemma div_one_sub_le_exp {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    1 / (1 - u) ≤ Real.exp (2 * u) := by
  have h : (1:ℝ) ≤ (1 - u) * Real.exp (2 * u) := one_le_one_sub_mul_exp h0 h1
  have hpos : (0:ℝ) < 1 - u := by linarith
  rw [div_le_iff₀ hpos]
  linarith [mul_comm (Real.exp (2*u)) (1-u)]

/-- Arithmetic core of the recursion: from the one-step inequality
`B ≤ M + h·Fη + h·C·B` one gets the value of the discrete scheme at the next time. -/
lemma key_step {K₀ Fη C B h kh : ℝ} (hK₀ : 0 ≤ K₀) (hFη : 0 ≤ Fη) (hC : 0 ≤ C)
    (hkh : 0 ≤ kh) (hh : 0 ≤ h) (hCh : C * h ≤ 1 / 2)
    (haux : B ≤ Real.exp (2 * C * kh) * (K₀ + kh * Fη) + h * Fη + h * C * B) :
    B ≤ Real.exp (2 * C * (kh + h)) * (K₀ + (kh + h) * Fη) := by
  set X : ℝ := Real.exp (2 * C * kh) * (K₀ + kh * Fη) + h * Fη with hX
  have haux' : B ≤ X + h * C * B := by rw [hX]; exact haux
  have h1 : B * (1 - C * h) ≤ X := by nlinarith [haux']
  have hpos : (0:ℝ) < 1 - C * h := by linarith
  have hCh0 : 0 ≤ C * h := mul_nonneg hC hh
  have h3 : (1 - C * h)⁻¹ ≤ Real.exp (2 * (C * h)) := by
    simpa [one_div] using div_one_sub_le_exp hCh0 hCh
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have h4 : B ≤ X * (1 - C * h)⁻¹ := by
    have h4' : B ≤ X / (1 - C * h) := by rw [le_div_iff₀ hpos]; exact h1
    rwa [div_eq_mul_inv] at h4'
  have h5 : X * (1 - C * h)⁻¹ ≤ X * Real.exp (2 * (C * h)) :=
    mul_le_mul_of_nonneg_left h3 hX0
  have h6 : X * Real.exp (2 * (C * h))
      ≤ Real.exp (2 * C * kh) * Real.exp (2 * (C * h)) * (K₀ + (kh + h) * Fη) := by
    have hexp1 : (1:ℝ) ≤ Real.exp (2 * C * kh) := Real.one_le_exp (by nlinarith)
    have hFη' : 0 ≤ h * Fη := mul_nonneg hh hFη
    have hkey2 : h * Fη ≤ Real.exp (2 * C * kh) * (h * Fη) := by
      simpa using mul_le_mul_of_nonneg_right hexp1 hFη'
    have hsum : K₀ + (kh + h) * Fη = (K₀ + kh * Fη) + h * Fη := by ring
    rw [hX, hsum]
    nlinarith [mul_le_mul_of_nonneg_left hkey2 (le_of_lt (Real.exp_pos (2 * (C * h)))),
      Real.exp_pos (2 * (C * h)), Real.exp_pos (2 * C * kh), hK₀,
      mul_nonneg hkh hFη]
  have hexpEq : Real.exp (2 * C * (kh + h))
      = Real.exp (2 * C * kh) * Real.exp (2 * (C * h)) := by
    rw [show 2 * C * (kh + h) = 2 * C * kh + 2 * (C * h) by ring, Real.exp_add]
  rw [hexpEq]
  linarith [h4, h5, h6]







end ConeAux

end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.jc3_landau =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-- `|a - b| ≤ |a| + |b|`. -/
lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_sub_le a 0 b
  rwa [sub_zero, zero_sub, abs_neg] at h

/-- **The abstract Landau step.**  If `V` is Lipschitz in `τ` and has `x`-derivative `W`, and
`W` is Lipschitz in `x` at the base point `x₀`, then `W x₀ ·` is `1/2`-Hölder in `τ` on the
side `τ ≥ 0`, up to the size `δ²` of the space interval used in the argument. -/
theorem tau_lip_sqrt_of_primitive_self {V W : ℝ → ℝ → ℝ} {x₀ δ L K : ℝ}
    (hδ : 0 < δ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hV : ∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → ∀ x ∈ Set.Icc x₀ (x₀ + δ),
      |V x τ - V x τ'| ≤ L * |τ - τ'|)
    (hcont : ∀ τ : ℝ, 0 ≤ τ → ContinuousOn (fun x => W x τ) (Set.Icc x₀ (x₀ + δ)))
    (hW : ∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δ),
      |W x τ - W x₀ τ| ≤ K * |x - x₀|)
    (hderiv : ∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δ),
      HasDerivAt (fun x' => V x' τ) (W x τ) x) :
    ∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → |τ - τ'| ≤ δ ^ 2 →
      |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * Real.sqrt |τ - τ'| := by
  intro τ τ' hτ hτ' hdiff
  rcases eq_or_lt_of_le (abs_nonneg (τ - τ')) with hz | hpos
  · have hττ : τ = τ' := by
      have h1 : τ - τ' = 0 := abs_eq_zero.mp hz.symm
      exact sub_eq_zero.mp h1
    subst hττ
    simp [Real.sqrt_zero]
  · set h : ℝ := Real.sqrt |τ - τ'| with hh
    have hhpos : 0 < h := Real.sqrt_pos.mpr hpos
    have hh2 : h ^ 2 = |τ - τ'| := Real.sq_sqrt (abs_nonneg _)
    have hhle : h ≤ δ := by
      rw [hh, ← Real.sqrt_sq hδ.le]
      exact Real.sqrt_le_sqrt hdiff
    have hab : x₀ ≤ x₀ + h := by linarith
    have hx0 : x₀ ∈ Set.Icc x₀ (x₀ + δ) := ⟨le_rfl, by linarith⟩
    have hxh : x₀ + h ∈ Set.Icc x₀ (x₀ + δ) := ⟨by linarith, by linarith⟩
    have hderiv' : ∀ σ : ℝ, 0 ≤ σ → ∀ x ∈ Set.uIcc x₀ (x₀ + h),
        HasDerivAt (fun x' => V x' σ) (W x σ) x := by
      intro σ hσ x hx
      rw [Set.uIcc_of_le hab] at hx
      exact hderiv σ hσ x ⟨hx.1, by linarith [hx.2]⟩
    have hint : ∀ σ : ℝ, 0 ≤ σ → IntervalIntegrable (fun x => W x σ) volume x₀ (x₀ + h) := by
      intro σ hσ
      refine (ContinuousOn.intervalIntegrable ?_)
      rw [Set.uIcc_of_le hab]
      exact (hcont σ hσ).mono (Set.Icc_subset_Icc le_rfl (by linarith))
    have hFTC : ∀ σ : ℝ, 0 ≤ σ →
        ∫ x in x₀..(x₀ + h), W x σ = V (x₀ + h) σ - V x₀ σ := fun σ hσ =>
      intervalIntegral.integral_eq_sub_of_hasDerivAt (hderiv' σ hσ) (hint σ hσ)
    -- the first integral
    have hA : ∫ x in x₀..(x₀ + h), (W x τ - W x τ')
        = (V (x₀ + h) τ - V x₀ τ) - (V (x₀ + h) τ' - V x₀ τ') := by
      rw [intervalIntegral.integral_sub (hint τ hτ) (hint τ' hτ'), hFTC τ hτ, hFTC τ' hτ']
    have hb1 : |∫ x in x₀..(x₀ + h), (W x τ - W x τ')| ≤ 2 * L * |τ - τ'| := by
      rw [hA]
      have h1 := hV τ τ' hτ hτ' (x₀ + h) hxh
      have h2 := hV τ τ' hτ hτ' x₀ hx0
      have h3 : (V (x₀ + h) τ - V x₀ τ) - (V (x₀ + h) τ' - V x₀ τ')
          = (V (x₀ + h) τ - V (x₀ + h) τ') - (V x₀ τ - V x₀ τ') := by ring
      rw [h3]
      have h4 : |(V (x₀ + h) τ - V (x₀ + h) τ') - (V x₀ τ - V x₀ τ')|
          ≤ |V (x₀ + h) τ - V (x₀ + h) τ'| + |V x₀ τ - V x₀ τ'| := by
        exact abs_sub_le_abs_add _ _
      calc |(V (x₀ + h) τ - V (x₀ + h) τ') - (V x₀ τ - V x₀ τ')|
          ≤ |V (x₀ + h) τ - V (x₀ + h) τ'| + |V x₀ τ - V x₀ τ'| := h4
        _ ≤ L * |τ - τ'| + L * |τ - τ'| := add_le_add h1 h2
        _ = 2 * L * |τ - τ'| := by ring
    -- the second integral
    have hsub1 : IntervalIntegrable (fun x => W x τ - W x₀ τ) volume x₀ (x₀ + h) :=
      (hint τ hτ).sub intervalIntegrable_const
    have hsub2 : IntervalIntegrable (fun x => W x τ' - W x₀ τ') volume x₀ (x₀ + h) :=
      (hint τ' hτ').sub intervalIntegrable_const
    have hint2 : IntervalIntegrable
        (fun x => (W x τ - W x₀ τ) - (W x τ' - W x₀ τ')) volume x₀ (x₀ + h) :=
      hsub1.sub hsub2
    have hInt : ∫ x in x₀..(x₀ + h), (2 * K * (x - x₀)) = K * h ^ 2 := by
      have hsub : ∫ x in x₀..(x₀ + h), (x - x₀) = h ^ 2 / 2 := by
        have h1 : (fun x : ℝ => x - x₀) = fun x => (fun y : ℝ => y) (x - x₀) := by
          funext x; rfl
        rw [h1, intervalIntegral.integral_comp_sub_right (f := fun y : ℝ => y) x₀]
        simp only [sub_self, add_sub_cancel_left]
        simp
      rw [intervalIntegral.integral_const_mul, hsub]
      ring
    have hb2 : |∫ x in x₀..(x₀ + h), ((W x τ - W x₀ τ) - (W x τ' - W x₀ τ'))| ≤ K * h ^ 2 := by
      rw [← hInt, ← Real.norm_eq_abs]
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
      refine intervalIntegral.integral_mono_on hab hint2.norm
        ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _) ?_
      intro x hx
      rw [Real.norm_eq_abs]
      have hxIcc : x ∈ Set.Icc x₀ (x₀ + δ) := ⟨hx.1, by linarith [hx.2]⟩
      have h1 := hW τ hτ x hxIcc
      have h2 := hW τ' hτ' x hxIcc
      have hxnn : 0 ≤ x - x₀ := by linarith [hx.1]
      calc |(W x τ - W x₀ τ) - (W x τ' - W x₀ τ')|
          ≤ |W x τ - W x₀ τ| + |W x τ' - W x₀ τ'| := abs_sub_le_abs_add _ _
        _ ≤ K * |x - x₀| + K * |x - x₀| := add_le_add h1 h2
        _ = 2 * K * (x - x₀) := by rw [abs_of_nonneg hxnn]; ring
    -- combine
    have hsplit : ∫ x in x₀..(x₀ + h), (W x τ - W x τ')
        = h * (W x₀ τ - W x₀ τ')
          + ∫ x in x₀..(x₀ + h), ((W x τ - W x₀ τ) - (W x τ' - W x₀ τ')) := by
      have hfun : (fun x => W x τ - W x τ')
          = fun x => (W x₀ τ - W x₀ τ') + ((W x τ - W x₀ τ) - (W x τ' - W x₀ τ')) := by
        funext x; ring
      rw [hfun, intervalIntegral.integral_add intervalIntegrable_const hint2,
        intervalIntegral.integral_const]
      ring
    have hkey : h * |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * h ^ 2 := by
      have h1 : h * (W x₀ τ - W x₀ τ')
          = (∫ x in x₀..(x₀ + h), (W x τ - W x τ'))
            - ∫ x in x₀..(x₀ + h), ((W x τ - W x₀ τ) - (W x τ' - W x₀ τ')) := by
        rw [hsplit]; ring
      calc h * |W x₀ τ - W x₀ τ'| = |h * (W x₀ τ - W x₀ τ')| := by
            rw [abs_mul, abs_of_pos hhpos]
        _ = |(∫ x in x₀..(x₀ + h), (W x τ - W x τ'))
                - (∫ x in x₀..(x₀ + h), ((W x τ - W x₀ τ) - (W x τ' - W x₀ τ')))| := by
            rw [h1]
        _ ≤ |∫ x in x₀..(x₀ + h), (W x τ - W x τ')|
              + |∫ x in x₀..(x₀ + h), ((W x τ - W x₀ τ) - (W x τ' - W x₀ τ'))| := by
            exact abs_sub_le_abs_add _ _
        _ ≤ 2 * L * |τ - τ'| + K * h ^ 2 := add_le_add hb1 hb2
        _ = (2 * L + K) * h ^ 2 := by rw [← hh2]; ring
    have hfin : |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * h := by
      have h2 : h * |W x₀ τ - W x₀ τ'| ≤ h * ((2 * L + K) * h) := by
        rw [show h * ((2 * L + K) * h) = (2 * L + K) * h ^ 2 by ring]
        exact hkey
      exact le_of_mul_le_mul_left h2 hhpos
    exact hfin

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.SlabFlat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.slabC1Flat`

An abstract regularity export on the slab `(0,∞) × (0,π/2) × [0,S]`.

If `f z θ τ = f z θ 0 + ∫_σ A z θ σ` on the slab, if the `(z,θ)`-slices `(z,θ) ↦ f z θ τ` are
Fréchet differentiable with derivative `L (z,θ,τ)`, and if `A` and `L` are continuous on the slab,
then `(z,θ,τ) ↦ f z θ τ` is `C¹` on the slab and the `τ`-derivative of `s ↦ f z θ s` is
`A z θ τ`.

The proof decomposes `f z θ τ = φ(z,θ) + ∫_{τ₀}^{τ} A z θ σ` on the slab (with `φ` the `τ₀`-slice
of `f`, `τ₀` being the base point), differentiates the two summands and adds.  The `(z,θ)`-part is
exactly the hypothesis `hd`; the integral part is differentiable because it is `o` in the `(z,θ)`
directions and its `τ`-derivative is the (continuous) integrand.
-/

open scoped Real Topology ContDiff
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT0

/-- The slab `(0,∞) × (0,π/2) × [0,S]`. -/
def SlabF (S : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)

lemma mem_Slab {S : ℝ} {y : ℝ × ℝ × ℝ} :
    y ∈ SlabF S ↔
      0 < y.1 ∧ 0 < y.2.1 ∧ y.2.1 < Real.pi / 2 ∧ 0 ≤ y.2.2 ∧ y.2.2 ≤ S := by
  simp [SlabF, and_assoc]

/-- Projection `(z,θ,τ) ↦ (z,θ)`. -/
noncomputable def projZθ : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

/-- Projection `(z,θ,τ) ↦ τ`. -/
noncomputable def projT : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The candidate derivative of `(z,θ,τ) ↦ f z θ τ` at `p`: the `(z,θ)`-part is `L p` and the
`τ`-part is the integrand `A p`. -/
noncomputable def slabD (L : ℝ × ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (A : ℝ → ℝ → ℝ → ℝ)
    (p : ℝ × ℝ × ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (L p).comp projZθ + (A p.1 p.2.1 p.2.2) • projT

@[simp] lemma projZθ_apply (v : ℝ × ℝ × ℝ) : projZθ v = (v.1, v.2.1) := rfl
@[simp] lemma projT_apply (v : ℝ × ℝ × ℝ) : projT v = v.2.2 := rfl

lemma uIcc_subset_Icc_of_mem {a b S : ℝ} (ha : a ∈ Set.Icc (0:ℝ) S) (hb : b ∈ Set.Icc (0:ℝ) S) :
    Set.uIcc a b ⊆ Set.Icc (0:ℝ) S := by
  intro σ hσ
  rw [Set.mem_uIcc] at hσ
  rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨le_trans ha.1 h1, le_trans h2 hb.2⟩
  · exact ⟨le_trans hb.1 h1, le_trans h2 ha.2⟩

/-- For `y` in the slab and `t ⊆ [0,S]`, the `σ`-slice `σ ↦ A y.1 y.2.1 σ` is continuous on
`t`. -/
lemma slabA_continuousOn_of_subset {S : ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2) (SlabF S))
    {y : ℝ × ℝ × ℝ} (hy : y ∈ SlabF S) {t : Set ℝ} (ht : t ⊆ Set.Icc (0:ℝ) S) :
    ContinuousOn (fun σ : ℝ => A y.1 y.2.1 σ) t := by
  have hyy := mem_Slab.mp hy
  have hmap : MapsTo (fun σ : ℝ => (y.1, y.2.1, σ)) t (SlabF S) := by
    intro σ hσ
    exact mem_Slab.mpr ⟨hyy.1, hyy.2.1, hyy.2.2.1, (ht hσ).1, (ht hσ).2⟩
  have hcont' := hA.comp (g := fun q : ℝ × ℝ × ℝ => A q.1 q.2.1 q.2.2)
    ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn) hmap
  convert hcont' using 1
  ext σ
  rfl

lemma Ioo_subset_Icc {S : ℝ} : Set.Ioo (0:ℝ) S ⊆ Set.Icc (0:ℝ) S :=
  fun _ hσ => ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩

/-- **The integral part.**  For `A` continuous on the slab and `p` in the slab, the map
`y ↦ ∫_{p.2.2}^{y.2.2} A y.1 y.2.1 σ` has Fréchet derivative `A p • projT` at `p` within the slab:
it is `o` in the `(z,θ)`-directions, and its `τ`-derivative is the integrand. -/
lemma slabIntegral_hasFDerivWithinAt {S : ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2) (SlabF S))
    {p : ℝ × ℝ × ℝ} (hp : p ∈ SlabF S) :
    HasFDerivWithinAt (fun y : ℝ × ℝ × ℝ => ∫ σ in p.2.2..y.2.2, A y.1 y.2.1 σ)
      ((A p.1 p.2.1 p.2.2) • projT) (SlabF S) p := by
  rw [hasFDerivWithinAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hcont : ContinuousWithinAt (fun q : ℝ × ℝ × ℝ => A q.1 q.2.1 q.2.2) (SlabF S) p :=
    hA.continuousWithinAt hp
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ, hδ, H⟩ := hcont (c/2) (by linarith)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds p hδ)]
    with y hyT hyball
  rw [Metric.mem_ball] at hyball
  have hyp := mem_Slab.mp hyT
  have hyy := mem_Slab.mp hp
  simp only [Prod.dist_eq] at hyball
  have hd1 : dist y.1 p.1 < δ := (max_lt_iff.mp hyball).1
  have hd2 : max (dist y.2.1 p.2.1) (dist y.2.2 p.2.2) < δ := (max_lt_iff.mp hyball).2
  have hd21 : dist y.2.1 p.2.1 < δ := (max_lt_iff.mp hd2).1
  have hd22 : dist y.2.2 p.2.2 < δ := (max_lt_iff.mp hd2).2
  have hle : |y.2.2 - p.2.2| ≤ ‖y - p‖ := by
    have h1 : ‖(y - p).2.2‖ ≤ ‖y - p‖ :=
      le_trans (norm_snd_le (y - p).2) (norm_snd_le (y - p))
    simpa [Real.norm_eq_abs] using h1
  have hbdd : ∀ σ ∈ Set.uIoc p.2.2 y.2.2, ‖A y.1 y.2.1 σ - A p.1 p.2.1 p.2.2‖ ≤ c/2 := by
    intro σ hσ
    rw [Set.mem_uIoc] at hσ
    have h0σ : 0 ≤ σ := by
      rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact le_trans hyy.2.2.2.1 (le_of_lt h1)
      · exact le_trans hyp.2.2.2.1 (le_of_lt h1)
    have hσS : σ ≤ S := by
      rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact le_trans h2 hyp.2.2.2.2
      · exact le_trans h2 hyy.2.2.2.2
    have habs : |σ - p.2.2| ≤ |y.2.2 - p.2.2| := by
      rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    have hdistσ : dist (y.1, y.2.1, σ) p < δ := by
      simp only [Prod.dist_eq]
      rw [max_lt_iff]
      refine ⟨hd1, ?_⟩
      rw [max_lt_iff]
      refine ⟨hd21, ?_⟩
      rw [Real.dist_eq]
      exact lt_of_le_of_lt habs (by rwa [Real.dist_eq] at hd22)
    have hmem : (y.1, y.2.1, σ) ∈ SlabF S := mem_Slab.mpr ⟨hyp.1, hyp.2.1, hyp.2.2.1, h0σ, hσS⟩
    have hH := H hmem hdistσ
    rw [Real.dist_eq] at hH
    rw [Real.norm_eq_abs]
    linarith
  have hline : ContinuousOn (fun σ : ℝ => A y.1 y.2.1 σ) (Set.uIcc p.2.2 y.2.2) :=
    slabA_continuousOn_of_subset hA hyT
      (uIcc_subset_Icc_of_mem ⟨hyy.2.2.2.1, hyy.2.2.2.2⟩ ⟨hyp.2.2.2.1, hyp.2.2.2.2⟩)
  have hint1 : IntervalIntegrable (fun σ : ℝ => A y.1 y.2.1 σ) volume p.2.2 y.2.2 :=
    hline.intervalIntegrable
  have hint2 : IntervalIntegrable (fun _ : ℝ => A p.1 p.2.1 p.2.2) volume p.2.2 y.2.2 :=
    intervalIntegrable_const
  have heq : (∫ σ in p.2.2..y.2.2, (A y.1 y.2.1 σ - A p.1 p.2.1 p.2.2))
      = (∫ σ in p.2.2..y.2.2, A y.1 y.2.1 σ) - A p.1 p.2.1 p.2.2 * (y.2.2 - p.2.2) := by
    rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hgoal : ‖(∫ σ in p.2.2..y.2.2, A y.1 y.2.1 σ) - A p.1 p.2.1 p.2.2 * (y.2.2 - p.2.2)‖
      ≤ c * ‖y - p‖ := by
    rw [← heq]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbdd) ?_
    calc (c/2) * |y.2.2 - p.2.2| ≤ (c/2) * ‖y - p‖ :=
          mul_le_mul_of_nonneg_left hle (by linarith)
      _ ≤ c * ‖y - p‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hKp : (∫ σ in p.2.2..p.2.2, A p.1 p.2.1 σ) = 0 := intervalIntegral.integral_same
  have hf' : ((A p.1 p.2.1 p.2.2) • projT) (y - p) = A p.1 p.2.1 p.2.2 * (y.2.2 - p.2.2) := by
    simp [projT]
  simpa only [hKp, hf', sub_zero] using hgoal

/-- Splitting the integral identity at the base point `p`. -/
lemma slab_split {S : ℝ} (hS : 0 < S) {f : ℝ → ℝ → ℝ → ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2) (SlabF S))
    (hId : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
      f z θ τ = f z θ 0 + ∫ σ in (0:ℝ)..τ, A z θ σ)
    {p y : ℝ × ℝ × ℝ} (hp : p ∈ SlabF S) (hy : y ∈ SlabF S) :
    f y.1 y.2.1 y.2.2 = f y.1 y.2.1 p.2.2 + ∫ σ in p.2.2..y.2.2, A y.1 y.2.1 σ := by
  have hyy := mem_Slab.mp hy
  have hypp := mem_Slab.mp hp
  have h1 := hId y.1 y.2.1 y.2.2 hyy.1 hyy.2.1 hyy.2.2.1 hyy.2.2.2.1 hyy.2.2.2.2
  have h2 := hId y.1 y.2.1 p.2.2 hyy.1 hyy.2.1 hyy.2.2.1 hypp.2.2.2.1 hypp.2.2.2.2
  have hcontS : ContinuousOn (fun σ : ℝ => A y.1 y.2.1 σ) (Set.Icc (0:ℝ) S) :=
    slabA_continuousOn_of_subset hA hy (Subset.refl _)
  have h0I : (0:ℝ) ∈ Set.Icc (0:ℝ) S := ⟨le_refl 0, le_of_lt hS⟩
  have hpI : p.2.2 ∈ Set.Icc (0:ℝ) S := ⟨hypp.2.2.2.1, hypp.2.2.2.2⟩
  have hyI : y.2.2 ∈ Set.Icc (0:ℝ) S := ⟨hyy.2.2.2.1, hyy.2.2.2.2⟩
  have hI1 : IntervalIntegrable (fun σ : ℝ => A y.1 y.2.1 σ) volume (0:ℝ) p.2.2 :=
    (hcontS.mono (uIcc_subset_Icc_of_mem h0I hpI)).intervalIntegrable
  have hI2 : IntervalIntegrable (fun σ : ℝ => A y.1 y.2.1 σ) volume p.2.2 y.2.2 :=
    (hcontS.mono (uIcc_subset_Icc_of_mem hpI hyI)).intervalIntegrable
  have hadj := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  rw [h1, h2, ← hadj]
  ring

/-- The `(z,θ)`-part: the `τ₀`-slice of `f`, lifted to the slab. -/
lemma slab_slice_hasFDerivWithinAt {S : ℝ} {f : ℝ → ℝ → ℝ → ℝ}
    {L : ℝ × ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hd : ∀ p ∈ SlabF S, HasFDerivAt (fun q : ℝ × ℝ => f q.1 q.2 p.2.2) (L p) (p.1, p.2.1))
    {p : ℝ × ℝ × ℝ} (hp : p ∈ SlabF S) :
    HasFDerivWithinAt (fun y : ℝ × ℝ × ℝ => f y.1 y.2.1 p.2.2)
      ((L p).comp projZθ) (SlabF S) p := by
  refine ((hd p hp).comp p projZθ.hasFDerivAt).hasFDerivWithinAt.congr ?_ ?_
  · intro y hy
    rfl
  · rfl

/-- **Differentiability of `(z,θ,τ) ↦ f z θ τ` on the slab.** -/
lemma slab_hasFDerivWithinAt {S : ℝ} (hS : 0 < S) {f : ℝ → ℝ → ℝ → ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    {L : ℝ × ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2) (SlabF S))
    (hId : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
      f z θ τ = f z θ 0 + ∫ σ in (0:ℝ)..τ, A z θ σ)
    (hd : ∀ p ∈ SlabF S, HasFDerivAt (fun q : ℝ × ℝ => f q.1 q.2 p.2.2) (L p) (p.1, p.2.1))
    {p : ℝ × ℝ × ℝ} (hp : p ∈ SlabF S) :
    HasFDerivWithinAt (fun y : ℝ × ℝ × ℝ => f y.1 y.2.1 y.2.2) (slabD L A p) (SlabF S) p := by
  have hsum := (slab_slice_hasFDerivWithinAt hd hp).add (slabIntegral_hasFDerivWithinAt hA hp)
  exact hsum.congr (fun y hy => slab_split hS hA hId hp hy) (slab_split hS hA hId hp hp)

/-- **Continuity of the candidate derivative on the slab.** -/
lemma slabD_continuousOn {S : ℝ} {L : ℝ × ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    (hL : ContinuousOn L (SlabF S))
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2) (SlabF S)) :
    ContinuousOn (slabD L A) (SlabF S) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ × ℝ => (L p).comp projZθ) (SlabF S) :=
    hL.clm_comp (continuousOn_const (c := projZθ))
  have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => (A p.1 p.2.1 p.2.2) • projT) (SlabF S) :=
    hA.smul (continuousOn_const (c := projT))
  unfold slabD
  exact h1.add h2

/-- The `τ`-derivative, from the integral representation (fundamental theorem of calculus). -/
lemma slab_tau_hasDerivAt {S : ℝ} (hS : 0 < S) {f : ℝ → ℝ → ℝ → ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2) (SlabF S))
    (hId : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
      f z θ τ = f z θ 0 + ∫ σ in (0:ℝ)..τ, A z θ σ)
    {z θ τ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) (hτ : 0 < τ) (hτS : τ < S) :
    HasDerivAt (fun s => f z θ s) (A z θ τ) τ := by
  have hp : (z, θ, τ) ∈ SlabF S :=
    mem_Slab.mpr ⟨hz, hθ, hθ2, le_of_lt hτ, le_of_lt hτS⟩
  have hcIoo : ContinuousOn (fun σ : ℝ => A z θ σ) (Set.Ioo (0:ℝ) S) :=
    slabA_continuousOn_of_subset hA hp Ioo_subset_Icc
  have hcτ : ContinuousAt (fun σ : ℝ => A z θ σ) τ :=
    hcIoo.continuousAt (isOpen_Ioo.mem_nhds ⟨hτ, hτS⟩)
  have hsm : StronglyMeasurableAtFilter (fun σ : ℝ => A z θ σ) (𝓝 τ) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hcIoo τ ⟨hτ, hτS⟩
  have hII : IntervalIntegrable (fun σ : ℝ => A z θ σ) volume (0:ℝ) τ :=
    (slabA_continuousOn_of_subset hA hp (uIcc_subset_Icc_of_mem ⟨le_refl 0, le_of_lt hS⟩
      ⟨le_of_lt hτ, le_of_lt hτS⟩)).intervalIntegrable
  have hderiv : HasDerivAt (fun s : ℝ => ∫ σ in (0:ℝ)..s, A z θ σ) (A z θ τ) τ :=
    intervalIntegral.integral_hasDerivAt_right hII hsm hcτ
  have hfull : HasDerivAt (fun s : ℝ => f z θ 0 + ∫ σ in (0:ℝ)..s, A z θ σ) (A z θ τ) τ := by
    have h := (hasDerivAt_const τ (f z θ 0)).add hderiv
    rw [zero_add] at h
    exact h
  refine hfull.congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds isOpen_Ioo ⟨hτ, hτS⟩] with s hs
  exact hId z θ s hz hθ hθ2 (le_of_lt hs.1) (le_of_lt hs.2)

theorem slabC1Flat {S : ℝ} (hS : 0 < S) {f : ℝ → ℝ → ℝ → ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    {L : ℝ × ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)))
    (hId : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
      f z θ τ = f z θ 0 + ∫ σ in (0:ℝ)..τ, A z θ σ)
    (hd : ∀ p ∈ Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S),
      HasFDerivAt (fun q : ℝ × ℝ => f q.1 q.2 p.2.2) (L p) (p.1, p.2.1))
    (hL : ContinuousOn L (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) ∧
    ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ < S →
      HasDerivAt (fun s => f z θ s) (A z θ τ) τ := by
  constructor
  · rw [show (1 : ℕ∞ω) = (0 : ℕ∞ω) + 1 from (zero_add 1).symm]
    rw [contDiffOn_succ_iff_hasFDerivWithinAt (𝕜 := ℝ) (n := (0 : ℕ∞ω)) (by simp)]
    intro x hx
    refine ⟨SlabF S, ?_, ?_, slabD L A, ?_, ?_⟩
    · rw [insert_eq_of_mem hx]
      exact self_mem_nhdsWithin
    · intro h
      exact absurd h (by simp)
    · intro y hy
      exact slab_hasFDerivWithinAt hS hA hId hd hy
    · rw [contDiffOn_zero]
      exact slabD_continuousOn hL hA
  · intro z θ τ hz hθ hθ2 hτ hτS
    exact slab_tau_hasDerivAt hS hA hId hz hθ hθ2 hτ hτS

end Work.FTS_RegExport.RXT0
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.integral_sin_two_rpow_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.THL

open MeasureTheory

/-- Subadditivity of `x ↦ x ^ p` for `0 < p ≤ 1`: for `0 ≤ x ≤ y` we have
`y ^ p - x ^ p ≤ (y - x) ^ p`. -/
lemma rpow_sub_le_rpow_sub {p x y : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hx : 0 ≤ x) (hxy : x ≤ y) :
    y ^ p - x ^ p ≤ (y - x) ^ p := by
  have h := Real.rpow_add_le_add_rpow hx (sub_nonneg.mpr hxy) hp.le hp1
  have hx' : x + (y - x) = y := by ring
  rw [hx'] at h
  linarith

/-- `(4 / π) ^ (p - 1) = (π / 4) ^ (1 - p)`. -/
lemma four_div_pi_rpow (p : ℝ) : (4 / Real.pi) ^ (p - 1) = (Real.pi / 4) ^ (1 - p) := by
  have hc : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h1 : (Real.pi / 4)⁻¹ = 4 / Real.pi := inv_div _ _
  calc (4 / Real.pi) ^ (p - 1) = ((Real.pi / 4)⁻¹) ^ (p - 1) := by rw [h1]
    _ = ((Real.pi / 4) ^ (p - 1))⁻¹ := by rw [Real.inv_rpow hc]
    _ = (Real.pi / 4) ^ (-(p - 1)) := (Real.rpow_neg hc (p - 1)).symm
    _ = (Real.pi / 4) ^ (1 - p) := by rw [show -(p - 1) = 1 - p by ring]

theorem integral_sin_two_rpow_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {θ θ' : ℝ}
    (h0 : 0 < θ) (hle : θ ≤ θ') (h1 : θ' < Real.pi / 2) :
    ∫ σ in θ..θ', Real.sin (2 * σ) ^ (p - 1) ≤ 2 * (Real.pi / 4) ^ (1 - p) / p * (θ' - θ) ^ p := by
  have hpm1 : p - 1 ≤ 0 := by linarith
  have h4pi : (0 : ℝ) < 4 / Real.pi := by positivity
  have hc4 : (0 : ℝ) < Real.pi / 4 := by positivity
  -- `sin (2σ) > 0` on the whole interval
  have hsin_pos : ∀ σ ∈ Set.Icc θ θ', 0 < Real.sin (2 * σ) := by
    intro σ hσ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1, h0]) (by linarith [hσ.2, h1])
  -- the pointwise comparison
  have hpt : ∀ σ ∈ Set.Icc θ θ', Real.sin (2 * σ) ^ (p - 1) ≤
      (Real.pi / 4) ^ (1 - p) * (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)) := by
    intro σ hσ
    have hσ0 : 0 < σ := lt_of_lt_of_le h0 hσ.1
    have hσL : σ < Real.pi / 2 := lt_of_le_of_lt hσ.2 h1
    have hc_nn : 0 ≤ (Real.pi / 4) ^ (1 - p) := Real.rpow_nonneg hc4.le _
    rcases le_or_gt σ (Real.pi / 4) with hs | hs
    · -- `σ ≤ π/4`: use `sin (2σ) ≥ (4/π) σ`
      have hmul : 2 / Real.pi * (2 * σ) ≤ Real.sin (2 * σ) :=
        Real.mul_le_sin (by linarith) (by linarith)
      have hge : 4 / Real.pi * σ ≤ Real.sin (2 * σ) := by
        rw [show (4 : ℝ) / Real.pi * σ = 2 / Real.pi * (2 * σ) by ring]
        exact hmul
      have hbase : 0 < 4 / Real.pi * σ := mul_pos h4pi hσ0
      have hrw : (4 / Real.pi * σ) ^ (p - 1) = (Real.pi / 4) ^ (1 - p) * σ ^ (p - 1) := by
        rw [Real.mul_rpow h4pi.le hσ0.le, four_div_pi_rpow]
      calc Real.sin (2 * σ) ^ (p - 1) ≤ (4 / Real.pi * σ) ^ (p - 1) :=
            Real.rpow_le_rpow_of_nonpos hbase hge hpm1
        _ = (Real.pi / 4) ^ (1 - p) * σ ^ (p - 1) := hrw
        _ ≤ (Real.pi / 4) ^ (1 - p) * (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)) :=
            mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _)) hc_nn
    · -- `σ > π/4`: use `sin (2σ) = sin (π - 2σ) ≥ (4/π) (π/2 - σ)`
      have hmul : 2 / Real.pi * (Real.pi - 2 * σ) ≤ Real.sin (Real.pi - 2 * σ) :=
        Real.mul_le_sin (by linarith) (by linarith)
      rw [Real.sin_pi_sub] at hmul
      have hge : 4 / Real.pi * (Real.pi / 2 - σ) ≤ Real.sin (2 * σ) := by
        rw [show (4 : ℝ) / Real.pi * (Real.pi / 2 - σ)
              = 2 / Real.pi * (Real.pi - 2 * σ) by ring]
        exact hmul
      have hbase : 0 < 4 / Real.pi * (Real.pi / 2 - σ) := mul_pos h4pi (by linarith)
      have hrw : (4 / Real.pi * (Real.pi / 2 - σ)) ^ (p - 1)
          = (Real.pi / 4) ^ (1 - p) * (Real.pi / 2 - σ) ^ (p - 1) := by
        rw [Real.mul_rpow h4pi.le (by linarith), four_div_pi_rpow]
      calc Real.sin (2 * σ) ^ (p - 1) ≤ (4 / Real.pi * (Real.pi / 2 - σ)) ^ (p - 1) :=
            Real.rpow_le_rpow_of_nonpos hbase hge hpm1
        _ = (Real.pi / 4) ^ (1 - p) * (Real.pi / 2 - σ) ^ (p - 1) := hrw
        _ ≤ (Real.pi / 4) ^ (1 - p) * (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)) :=
            mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_left (Real.rpow_nonneg hσ0.le _)) hc_nn
  -- continuity of the two integrands
  have hui : Set.uIcc θ θ' = Set.Icc θ θ' := Set.uIcc_of_le hle
  have hid : ContinuousOn (fun σ : ℝ => σ ^ (p - 1)) (Set.uIcc θ θ') := by
    refine continuous_id.continuousOn.rpow_const ?_
    intro σ hσ
    left
    rw [hui] at hσ
    exact ne_of_gt (lt_of_lt_of_le h0 hσ.1)
  have hsub_c : ContinuousOn (fun σ : ℝ => Real.pi / 2 - σ) (Set.uIcc θ θ') :=
    continuous_const.continuousOn.sub continuous_id.continuousOn
  have h2c : ContinuousOn (fun σ : ℝ => (Real.pi / 2 - σ) ^ (p - 1)) (Set.uIcc θ θ') := by
    refine hsub_c.rpow_const ?_
    intro σ hσ
    left
    rw [hui] at hσ
    exact ne_of_gt (by linarith [hσ.2, h1])
  have hcontf : ContinuousOn (fun σ : ℝ => Real.sin (2 * σ) ^ (p - 1)) (Set.uIcc θ θ') := by
    have hsin : ContinuousOn (fun σ : ℝ => Real.sin (2 * σ)) (Set.uIcc θ θ') :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    refine hsin.rpow_const ?_
    intro σ hσ
    left
    rw [hui] at hσ
    exact ne_of_gt (hsin_pos σ hσ)
  have hcontg : ContinuousOn (fun σ : ℝ =>
      (Real.pi / 4) ^ (1 - p) * (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)))
      (Set.uIcc θ θ') :=
    continuousOn_const.mul (hid.add h2c)
  -- monotonicity of the interval integral
  have hmono : ∫ σ in θ..θ', Real.sin (2 * σ) ^ (p - 1) ≤
      ∫ σ in θ..θ', (Real.pi / 4) ^ (1 - p) * (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)) :=
    intervalIntegral.integral_mono_on hle (ContinuousOn.intervalIntegrable hcontf)
      (ContinuousOn.intervalIntegrable hcontg) hpt
  -- explicit evaluation of the comparison integral
  have hint1 : ∫ σ in θ..θ', σ ^ (p - 1) = (θ' ^ p - θ ^ p) / p := by
    rw [integral_rpow (Or.inl (show (-1 : ℝ) < p - 1 by linarith))]
    rw [show p - 1 + 1 = p by ring]
  have hint2 : ∫ σ in θ..θ', (Real.pi / 2 - σ) ^ (p - 1)
      = ((Real.pi / 2 - θ) ^ p - (Real.pi / 2 - θ') ^ p) / p := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (p - 1)) (Real.pi / 2)]
    rw [integral_rpow (Or.inl (show (-1 : ℝ) < p - 1 by linarith))]
    rw [show p - 1 + 1 = p by ring]
  have hint_add : ∫ σ in θ..θ', (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1))
      = (∫ σ in θ..θ', σ ^ (p - 1)) + ∫ σ in θ..θ', (Real.pi / 2 - σ) ^ (p - 1) :=
    intervalIntegral.integral_add (ContinuousOn.intervalIntegrable hid)
      (ContinuousOn.intervalIntegrable h2c)
  have hInt : ∫ σ in θ..θ', (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1))
      = (θ' ^ p - θ ^ p) / p + ((Real.pi / 2 - θ) ^ p - (Real.pi / 2 - θ') ^ p) / p := by
    rw [hint_add, hint1, hint2]
  have hb1 : θ' ^ p - θ ^ p ≤ (θ' - θ) ^ p := rpow_sub_le_rpow_sub hp hp1 h0.le hle
  have hb2 : (Real.pi / 2 - θ) ^ p - (Real.pi / 2 - θ') ^ p ≤ (θ' - θ) ^ p := by
    have h := rpow_sub_le_rpow_sub (p := p) hp hp1 (x := Real.pi / 2 - θ') (y := Real.pi / 2 - θ)
      (by linarith) (by linarith)
    rwa [show Real.pi / 2 - θ - (Real.pi / 2 - θ') = θ' - θ by ring] at h
  have hsum_bound : ∫ σ in θ..θ', (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1))
      ≤ 2 * (θ' - θ) ^ p / p := by
    rw [hInt]
    have hkey : θ' ^ p - θ ^ p + ((Real.pi / 2 - θ) ^ p - (Real.pi / 2 - θ') ^ p)
        ≤ 2 * (θ' - θ) ^ p := by linarith
    calc (θ' ^ p - θ ^ p) / p + ((Real.pi / 2 - θ) ^ p - (Real.pi / 2 - θ') ^ p) / p
        = (θ' ^ p - θ ^ p + ((Real.pi / 2 - θ) ^ p - (Real.pi / 2 - θ') ^ p)) / p := by ring
      _ ≤ (2 * (θ' - θ) ^ p) / p := div_le_div_of_nonneg_right hkey hp.le
      _ = 2 * (θ' - θ) ^ p / p := rfl
  have hc_nn : 0 ≤ (Real.pi / 4) ^ (1 - p) := Real.rpow_nonneg hc4.le _
  calc ∫ σ in θ..θ', Real.sin (2 * σ) ^ (p - 1)
      ≤ ∫ σ in θ..θ', (Real.pi / 4) ^ (1 - p) * (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)) :=
        hmono
    _ = (Real.pi / 4) ^ (1 - p)
          * ∫ σ in θ..θ', (σ ^ (p - 1) + (Real.pi / 2 - σ) ^ (p - 1)) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (Real.pi / 4) ^ (1 - p) * (2 * (θ' - θ) ^ p / p) :=
        mul_le_mul_of_nonneg_left hsum_bound hc_nn
    _ = 2 * (Real.pi / 4) ^ (1 - p) / p * (θ' - θ) ^ p := by ring

end Work.FTS_RegExport.THL
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB1.rpow_ode_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB1

open MeasureTheory Set Filter
open scoped Interval Topology

theorem rpow_ode_aux {k M z : ℝ} (hk : 0 < k) (hz : 0 < z) {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Ioo 0 (z + 1)))
    (hbdd : ∀ u ∈ Set.Ioo (0 : ℝ) (z + 1), |h u| ≤ M) :
    HasDerivAt (fun z' => ∫ v in (0 : ℝ)..1, v ^ (k - 1) * h (z' * v))
      ((h z - k * (∫ v in (0 : ℝ)..1, v ^ (k - 1) * h (z * v))) / z) z := by
  -- `M` is nonnegative: evaluate the bound at an interior point.
  have hM : 0 ≤ M := by
    have h1 : |h (z / 2)| ≤ M := hbdd (z / 2) ⟨by linarith, by linarith⟩
    have h2 : (0 : ℝ) ≤ |h (z / 2)| := abs_nonneg _
    linarith
  have hzmem : z ∈ Set.Ioo (0 : ℝ) (z + 1) := ⟨hz, by linarith⟩
  -- Basic continuity of the integrand on the open interval.
  have hcφ : ContinuousOn (fun u : ℝ => u ^ (k - 1) * h u) (Set.Ioo 0 (z + 1)) := by
    have h1 : ContinuousOn (fun x : ℝ => x ^ (k - 1)) (Set.Ioo 0 (z + 1)) :=
      continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))
    exact h1.mul hcont
  -- Interval integrability of `u ↦ u^(k-1) * h u` on `(0,z)`.
  have hφint : IntervalIntegrable (fun u : ℝ => u ^ (k - 1) * h u) volume 0 z := by
    have hcIoc : ContinuousOn (fun u : ℝ => u ^ (k - 1) * h u) (Set.Ioc 0 z) :=
      hcφ.mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)
    have hmeas : AEStronglyMeasurable (fun u : ℝ => u ^ (k - 1) * h u)
        (volume.restrict (Set.Ioc 0 z)) :=
      hcIoc.aestronglyMeasurable measurableSet_Ioc
    have hg : IntegrableOn (fun u : ℝ => M * u ^ (k - 1)) (Set.Ioc 0 z) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mp
        ((intervalIntegral.intervalIntegrable_rpow'
          (a := 0) (b := z) (by linarith : (-1 : ℝ) < k - 1)).const_mul M)
    have hle : ∀ᵐ u ∂volume.restrict (Set.Ioc 0 z),
        ‖u ^ (k - 1) * h u‖ ≤ M * u ^ (k - 1) := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      have hu' : u ∈ Set.Ioo (0 : ℝ) (z + 1) := ⟨hu.1, by linarith [hu.2]⟩
      have hbu : |h u| ≤ M := hbdd u hu'
      have hx : (0 : ℝ) ≤ u ^ (k - 1) := Real.rpow_nonneg hu.1.le _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
      nlinarith [hbu, hx, hM]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mpr (hg.mono' hmeas hle)
  have hφcontAt : ContinuousAt (fun u : ℝ => u ^ (k - 1) * h u) z :=
    hcφ.continuousAt (isOpen_Ioo.mem_nhds hzmem)
  have hsm : StronglyMeasurableAtFilter (fun u : ℝ => u ^ (k - 1) * h u) (𝓝 z) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
      (fun x hx => hcφ.continuousAt (isOpen_Ioo.mem_nhds hx)) z hzmem
  -- FTC: derivative of the primitive.
  have hderivG : HasDerivAt (fun t : ℝ => ∫ u in (0 : ℝ)..t, u ^ (k - 1) * h u)
      (z ^ (k - 1) * h z) z :=
    intervalIntegral.integral_hasDerivAt_right hφint hsm hφcontAt
  -- Product rule with `t^(-k)`.
  have hderiv : HasDerivAt
      (fun t : ℝ => t ^ (-k) * ∫ u in (0 : ℝ)..t, u ^ (k - 1) * h u)
      ((-k) * z ^ (-k - 1) * (∫ u in (0 : ℝ)..z, u ^ (k - 1) * h u)
        + z ^ (-k) * (z ^ (k - 1) * h z)) z := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ (-k)) ((-k) * z ^ (-k - 1)) z := by
      have hlt := Real.hasDerivAt_rpow_const (x := z) (p := -k) (Or.inl hz.ne')
      exact hlt
    exact h1.mul hderivG
  -- The substitution identity, for every `t > 0` (in fact, near `z`).
  have hid : ∀ t ∈ Set.Ioo (0 : ℝ) (z + 1),
      (∫ v in (0 : ℝ)..1, v ^ (k - 1) * h (t * v))
        = t ^ (-k) * ∫ u in (0 : ℝ)..t, u ^ (k - 1) * h u := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hstep1 : (∫ v in (0 : ℝ)..1, v ^ (k - 1) * h (t * v))
        = ∫ v in (0 : ℝ)..1, t ^ (1 - k) * ((t * v) ^ (k - 1) * h (t * v)) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
      have hv0 : (0 : ℝ) ≤ v := hv.1
      calc v ^ (k - 1) * h (t * v)
          = (t ^ (1 - k) * t ^ (k - 1)) * (v ^ (k - 1) * h (t * v)) := by
            rw [← Real.rpow_add ht0 (1 - k) (k - 1),
              show (1 - k) + (k - 1) = (0 : ℝ) by ring, Real.rpow_zero, one_mul]
        _ = t ^ (1 - k) * (t ^ (k - 1) * v ^ (k - 1) * h (t * v)) := by ring
        _ = t ^ (1 - k) * ((t * v) ^ (k - 1) * h (t * v)) := by
            rw [Real.mul_rpow ht0.le hv0]
    have hstep2 : (∫ v in (0 : ℝ)..1, t ^ (1 - k) * ((t * v) ^ (k - 1) * h (t * v)))
        = t ^ (1 - k) * ∫ v in (0 : ℝ)..1, (t * v) ^ (k - 1) * h (t * v) :=
      intervalIntegral.integral_const_mul _ _
    have hstep3 : (∫ v in (0 : ℝ)..1, (t * v) ^ (k - 1) * h (t * v))
        = t⁻¹ * ∫ u in (0 : ℝ)..t, u ^ (k - 1) * h u := by
      have h := intervalIntegral.integral_comp_mul_left
        (f := fun u : ℝ => u ^ (k - 1) * h u) (a := (0 : ℝ)) (b := 1) (c := t) ht0.ne'
      simpa [zero_mul, mul_one, smul_eq_mul] using h
    rw [hstep1, hstep2, hstep3, ← mul_assoc, ← Real.rpow_neg_one t,
      ← Real.rpow_add ht0 (1 - k) (-1), show (1 - k) + (-1) = -k by ring]
  -- The derivative value equals the stated one.
  have hD : ((-k) * z ^ (-k - 1) * (∫ u in (0 : ℝ)..z, u ^ (k - 1) * h u)
        + z ^ (-k) * (z ^ (k - 1) * h z))
      = (h z - k * (∫ v in (0 : ℝ)..1, v ^ (k - 1) * h (z * v))) / z := by
    rw [hid z hzmem]
    have hz1 : z ^ (-k - 1) = z ^ (-k) / z := by
      rw [show (-k - 1 : ℝ) = -k + (-1) by ring, Real.rpow_add hz, Real.rpow_neg_one]
      ring
    have hz2 : z ^ (-k) * z ^ (k - 1) = 1 / z := by
      rw [← Real.rpow_add hz (-k) (k - 1),
        show -k + (k - 1) = (-1 : ℝ) by ring, Real.rpow_neg_one]
      ring
    have hz3 : z ^ (-k) * (z ^ (k - 1) * h z) = h z / z := by
      rw [← mul_assoc, hz2]; ring
    rw [hz1, hz3, div_eq_mul_inv]
    ring
  -- Assemble.
  have hev : (fun t : ℝ => ∫ v in (0 : ℝ)..1, v ^ (k - 1) * h (t * v))
      =ᶠ[𝓝 z] (fun t : ℝ => t ^ (-k) * ∫ u in (0 : ℝ)..t, u ^ (k - 1) * h u) := by
    filter_upwards [isOpen_Ioo.mem_nhds hzmem] with t ht
    exact hid t ht
  rw [← hD]
  exact hderiv.congr_of_eventuallyEq hev

end Work.FTS_StreamBdry.SB1
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB2.OddReflectC2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB2

/-- **Odd reflection preserves `C²`.** If `h : ℝ → ℝ → ℝ` is odd in its second variable and its
uncurried form is `C²` on the upper half-strip `(0,∞) × (0,π)`, then it is `C²` on the lower
half-strip `(0,∞) × (-π,0)` as well.

On the lower half-strip `h w θ = -h w (-θ)`, and `(w,θ) ↦ (w,-θ)` is a smooth diffeomorphism
carrying `(0,∞) × (-π,0)` onto `(0,∞) × (0,π)`; the claim is therefore `ContDiffOn`-invariance
under composition with that reflection, followed by taking the negative. -/
theorem OddReflectC2 {h : ℝ → ℝ → ℝ} (hodd : ∀ w θ, h w (-θ) = -h w θ)
    (h2 : ContDiffOn ℝ 2 (Function.uncurry h) (Set.Ioi 0 ×ˢ Set.Ioo 0 Real.pi)) :
    ContDiffOn ℝ 2 (Function.uncurry h) (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) 0) := by
  set s : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) 0 with hs
  -- the reflection `(w,θ) ↦ (w,-θ)` maps the lower half-strip into the upper one
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => (p.1, -p.2)) s (Set.Ioi 0 ×ˢ Set.Ioo 0 Real.pi) := by
    rintro ⟨w, θ⟩ ⟨hw, hθ⟩
    exact ⟨hw, by linarith [hθ.2], by linarith [hθ.1]⟩
  -- the reflection is smooth on the lower half-strip
  have hσ : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (p.1, -p.2)) s :=
    contDiffOn_fst.prodMk contDiffOn_snd.neg
  -- hence so is the composition
  have hcomp : ContDiffOn ℝ 2 ((Function.uncurry h) ∘ (fun p : ℝ × ℝ => (p.1, -p.2))) s :=
    h2.comp hσ hmap
  -- and that composition is `-(uncurry h)` on the lower half-strip, by oddness
  refine (hcomp.neg).congr ?_
  rintro ⟨w, θ⟩ ⟨hw, hθ⟩
  simp only [Function.comp_apply, Function.uncurry]
  simpa using hodd w (-θ)

end Work.FTS_StreamBdry.SB2
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.cont_rate_left =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25

theorem cont_rate_left {f : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {a b K : ℝ} (hab : a < b) (hK : 0 ≤ K)
    (hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo a b))
    (hrate : ∀ z θ, 0 < z → θ ∈ Set.Ioo a b → |f z θ - g z| ≤ K * (θ - a)) :
    ContinuousOn g (Set.Ioi 0) := by
  rw [Metric.continuousOn_iff]
  intro z₀ hz₀ ε hε
  -- a small offset into the interval `(a, b)`, controlled by `ε / 4`
  set m : ℝ := min ((b - a) / 2) (ε / (4 * (K + 1))) with hm
  have hm_pos : 0 < m := by
    rw [hm]
    exact lt_min (by linarith) (div_pos hε (by linarith))
  set θ : ℝ := a + m with hθ
  have haθ : a < θ := by rw [hθ]; linarith
  have hθb : θ < b := by
    rw [hθ]
    have : m ≤ (b - a) / 2 := by rw [hm]; exact min_le_left _ _
    linarith
  have hθmem : θ ∈ Set.Ioo a b := ⟨haθ, hθb⟩
  have hKm_aux : K * (ε / (4 * (K + 1))) < ε / 4 := by
    rw [← mul_div_assoc]
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 4 * (K + 1))]
    nlinarith
  have hKm : K * m < ε / 4 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by rw [hm]; exact min_le_right _ _) hK) hKm_aux
  have hθa_eq : θ - a = m := by rw [hθ]; ring
  have hKmθ : K * (θ - a) < ε / 4 := by rw [hθa_eq]; exact hKm
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.continuousOn_iff.mp hcont) (z₀, θ) ⟨hz₀, hθmem⟩ (ε / 2) (by linarith)
  refine ⟨δ, hδpos, ?_⟩
  intro z hz hdz
  have hdist : dist (z, θ) (z₀, θ) < δ := by
    rw [Prod.dist_eq, dist_self]
    exact max_lt hdz hδpos
  have h2raw : dist (Function.uncurry f (z, θ)) (Function.uncurry f (z₀, θ)) < ε / 2 :=
    hδ (a := (z, θ)) ⟨hz, hθmem⟩ hdist
  have h2 : |f z θ - f z₀ θ| < ε / 2 := by
    simpa [Function.uncurry, Real.dist_eq] using h2raw
  have h1 : |g z - f z θ| ≤ K * (θ - a) := by
    rw [abs_sub_comm]; exact hrate z θ hz hθmem
  have h3 : |f z₀ θ - g z₀| ≤ K * (θ - a) := hrate z₀ θ hz₀ hθmem
  have htri : |g z - g z₀| ≤ |g z - f z θ| + |f z θ - f z₀ θ| + |f z₀ θ - g z₀| := by
    have heq : g z - g z₀ = (g z - f z θ) + (f z θ - f z₀ θ) + (f z₀ θ - g z₀) := by ring
    rw [heq]
    exact abs_add_three _ _ _
  rw [Real.dist_eq]
  linarith

end Work.FTS_StreamBdry.SB25
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.cont_rate_right =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25

theorem cont_rate_right {f : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {a b K : ℝ} (hab : a < b) (hK : 0 ≤ K)
    (hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo a b))
    (hrate : ∀ z θ, 0 < z → θ ∈ Set.Ioo a b → |f z θ - g z| ≤ K * (b - θ)) :
    ContinuousOn g (Set.Ioi 0) := by
  -- `g` is the uniform (in `z`) limit of the slices `θ ↦ f z θ` as `θ → b⁻`, by `hrate`;
  -- joint continuity of `f` turns that into continuity of `g`.
  intro z₀ hz₀
  have hz0 : (0:ℝ) < z₀ := hz₀
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff]
  intro ε hε
  -- pick `θ := b - δt` close enough to `b` that the rate estimate is `< ε/3`
  set δt : ℝ := min ((b - a) / 2) (ε / (3 * (K + 1))) with hδtdef
  have hδtpos : 0 < δt := by
    rw [hδtdef]
    exact lt_min (by linarith) (div_pos hε (by linarith))
  have hθa : a < b - δt := by
    have hle : δt ≤ (b - a) / 2 := by rw [hδtdef]; exact min_le_left _ _
    linarith
  have hθb : b - δt < b := by linarith
  have hθmem : b - δt ∈ Set.Ioo a b := ⟨hθa, hθb⟩
  have hKδ : K * δt < ε / 3 := by
    have hle : δt ≤ ε / (3 * (K + 1)) := by rw [hδtdef]; exact min_le_right _ _
    have h1 : K * δt ≤ K * (ε / (3 * (K + 1))) := mul_le_mul_of_nonneg_left hle hK
    have h2 : K * (ε / (3 * (K + 1))) < ε / 3 := by
      have h3 : (0:ℝ) < 3 * (K + 1) := by linarith
      rw [← mul_div_assoc, div_lt_div_iff₀ h3 (by norm_num : (0:ℝ) < 3)]
      ring_nf
      nlinarith
    linarith
  -- joint continuity of `f` at `(z₀, b - δt)`
  have hnhds : Set.Ioi (0:ℝ) ×ˢ Set.Ioo a b ∈ nhds (z₀, b - δt) :=
    (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz0, hθmem⟩
  have hcat : ContinuousAt (Function.uncurry f) (z₀, b - δt) := hcont.continuousAt hnhds
  rw [Metric.continuousAt_iff] at hcat
  obtain ⟨δ', hδ'pos, hδ'⟩ := hcat (ε / 3) (by linarith)
  refine ⟨min δ' (z₀ / 2), lt_min hδ'pos (by linarith), ?_⟩
  intro y hy
  have hyδ' : dist y z₀ < δ' := lt_of_lt_of_le hy (min_le_left _ _)
  have hyz : dist y z₀ < z₀ / 2 := lt_of_lt_of_le hy (min_le_right _ _)
  -- staying within `z₀/2` keeps `y > 0`, so that `hrate` applies at `y`
  have hypos : 0 < y := by
    rw [Real.dist_eq] at hyz
    have h1 : -(z₀ / 2) < y - z₀ := (abs_lt.mp hyz).1
    linarith
  have hmid : dist (f y (b - δt)) (f z₀ (b - δt)) < ε / 3 := by
    have h := hδ' (show dist (y, b - δt) (z₀, b - δt) < δ' from by
      rw [dist_prod_same_right]; exact hyδ')
    simpa using h
  have hy1 : |g y - f y (b - δt)| < ε / 3 := by
    rw [abs_sub_comm]
    exact lt_of_le_of_lt (show |f y (b - δt) - g y| ≤ K * (b - (b - δt)) from
      hrate y (b - δt) hypos hθmem) (by linarith)
  have hy2 : |f z₀ (b - δt) - g z₀| < ε / 3 := by
    exact lt_of_le_of_lt (hrate z₀ (b - δt) hz0 hθmem) (by linarith)
  rw [Real.dist_eq]
  calc |g y - g z₀|
      = |(g y - f y (b - δt)) + (f y (b - δt) - f z₀ (b - δt)) + (f z₀ (b - δt) - g z₀)| := by
        ring_nf
    _ ≤ |g y - f y (b - δt)| + |f y (b - δt) - f z₀ (b - δt)| + |f z₀ (b - δt) - g z₀| := by
        have h1 := abs_add_le ((g y - f y (b - δt)) + (f y (b - δt) - f z₀ (b - δt)))
          (f z₀ (b - δt) - g z₀)
        have h2 := abs_add_le (g y - f y (b - δt)) (f y (b - δt) - f z₀ (b - δt))
        linarith
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [Real.dist_eq] at hmid
        linarith
    _ = ε := by ring

end Work.FTS_StreamBdry.SB25
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux.abs_le_chord_left =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25Aux

open Set Filter

/-! Auxiliary facts: the derivative of the quadratic `(K/2)(y-a)(b-y)`, of its derivative,
and of the linear function `((y-a)/(b-a))*C`. -/

private lemma alcl_hasDerivAt_quad (K a b x : ℝ) :
    HasDerivAt (fun y : ℝ => (K/2)*(y - a)*(b - y)) ((K/2)*(a + b - 2*x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (K/2)*(y - a)) (K/2) x := by
    simpa using ((hasDerivAt_id x).sub_const a).const_mul (K/2)
  have h2 : HasDerivAt (fun y : ℝ => b - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub b
  refine (h1.mul h2).congr_deriv ?_
  ring

private lemma alcl_hasDerivAt_quad' (K a b x : ℝ) :
    HasDerivAt (fun y : ℝ => (K/2)*(a + b - 2*y)) (-K) x := by
  have h1 : HasDerivAt (fun y : ℝ => 2*y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2:ℝ)
  have h2 : HasDerivAt (fun y : ℝ => a + b - 2*y) (-2) x := by
    simpa using h1.const_sub (a + b)
  refine (h2.const_mul (K/2)).congr_deriv ?_
  ring

private lemma alcl_hasDerivAt_lin (C a b x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y - a)/(b - a)) * C) (C/(b - a)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y - a)/(b - a)) (1/(b - a)) x := by
    simpa using ((hasDerivAt_id x).sub_const a).div_const (b - a)
  refine (h1.mul_const C).congr_deriv ?_
  ring

/-- If `φ` tends to `0` at both endpoints of the open interval `(a,b)` and `φ'' ≥ 0` on
`(a,b)`, then `φ ≤ 0` on `(a,b)`.  (Two mean value theorems plus the monotonicity of `φ'`.) -/
private theorem alcl_chord_nonpos {φ φ' φ'' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hlima : Tendsto φ (nhdsWithin a (Ioi a)) (nhds 0))
    (hlimb : Tendsto φ (nhdsWithin b (Iio b)) (nhds 0))
    (hd1 : ∀ x ∈ Ioo a b, HasDerivAt φ (φ' x) x)
    (hd2 : ∀ x ∈ Ioo a b, HasDerivAt φ' (φ'' x) x)
    (h2 : ∀ x ∈ Ioo a b, 0 ≤ φ'' x) :
    ∀ θ ∈ Ioo a b, φ θ ≤ 0 := by
  intro θ hθ
  by_contra hcon
  rw [not_le] at hcon
  have hθa : a < θ := hθ.1
  have hθb : θ < b := hθ.2
  have hθt : Filter.Tendsto φ (nhdsWithin θ (Iio θ)) (nhds (φ θ)) :=
    ((hd1 θ hθ).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  -- Cauchy mean value theorem on `(a, θ)`: some `φ' c₁` is positive
  obtain ⟨c₁, hc₁, hc₁eq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope' φ φ' hθa id (fun _ => 1)
      (lfa := 0) (lga := a) (lfb := φ θ) (lgb := θ)
      (fun x hx => hd1 x ⟨hx.1, hx.2.trans hθb⟩)
      (fun x _ => hasDerivAt_id x)
      hlima
      ((continuousAt_id (x := a)).tendsto.mono_left nhdsWithin_le_nhds)
      hθt
      ((continuousAt_id (x := θ)).tendsto.mono_left nhdsWithin_le_nhds)
  simp only [sub_zero, mul_one] at hc₁eq
  have hc₁pos : 0 < φ' c₁ := by
    have : 0 < (θ - a) * φ' c₁ := by rw [hc₁eq]; exact hcon
    exact pos_of_mul_pos_left (by simpa [mul_comm] using this) (le_of_lt (sub_pos.mpr hθa))
  -- Cauchy mean value theorem on `(θ, b)`: some `φ' c₂` is negative
  obtain ⟨c₂, hc₂, hc₂eq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope' φ φ' hθb id (fun _ => 1)
      (lfa := φ θ) (lga := θ) (lfb := 0) (lgb := b)
      (fun x hx => hd1 x ⟨hθa.trans hx.1, hx.2⟩)
      (fun x _ => hasDerivAt_id x)
      ((hd1 θ hθ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((continuousAt_id (x := θ)).tendsto.mono_left nhdsWithin_le_nhds)
      hlimb
      ((continuousAt_id (x := b)).tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_sub, mul_one] at hc₂eq
  have hc₂neg : φ' c₂ < 0 := by
    have : (b - θ) * φ' c₂ < 0 := by rw [hc₂eq]; linarith
    exact neg_of_mul_neg_left (by simpa [mul_comm] using this) (le_of_lt (sub_pos.mpr hθb))
  have hc₁c₂ : c₁ < c₂ := hc₁.2.trans hc₂.1
  have hsub : Icc c₁ c₂ ⊆ Ioo a b := by
    intro x hx
    exact ⟨hc₁.1.trans_le hx.1, hx.2.trans_lt hc₂.2⟩
  -- `φ'` is monotone on `[c₁,c₂]` because `φ'' ≥ 0`
  have hmono : MonotoneOn φ' (Icc c₁ c₂) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc c₁ c₂) ?_ ?_ ?_
    · intro x hx
      exact ((hd2 x (hsub hx)).continuousAt).continuousWithinAt
    · rw [interior_Icc]
      intro x hx
      exact ((hd2 x (hsub ⟨hx.1.le, hx.2.le⟩)).differentiableAt).differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hx' : x ∈ Ioo a b := hsub ⟨hx.1.le, hx.2.le⟩
      rw [(hd2 x hx').deriv]
      exact h2 x hx'
  have := hmono ⟨le_refl c₁, hc₁c₂.le⟩ ⟨hc₁c₂.le, le_refl c₂⟩ hc₁c₂.le
  linarith

/-- If `e` tends to `0` at both endpoints of `(a,b)` and `|e''| ≤ K` on `(a,b)`, then
`|e θ| ≤ (K/2)(θ-a)(b-θ)`.  Both estimates follow from `alcl_chord_nonpos` applied to
`e - H` and `-e - H`, where `H` is the parabola `(K/2)(y-a)(b-y)`. -/
private theorem alcl_chord_abs {e e' e'' : ℝ → ℝ} {a b K : ℝ} (hab : a < b)
    (hlima : Tendsto e (nhdsWithin a (Ioi a)) (nhds 0))
    (hlimb : Tendsto e (nhdsWithin b (Iio b)) (nhds 0))
    (hd1 : ∀ x ∈ Ioo a b, HasDerivAt e (e' x) x)
    (hd2 : ∀ x ∈ Ioo a b, HasDerivAt e' (e'' x) x)
    (hb : ∀ x ∈ Ioo a b, |e'' x| ≤ K) :
    ∀ θ ∈ Ioo a b, |e θ| ≤ (K/2)*(θ - a)*(b - θ) := by
  intro θ hθ
  have hHcont : Continuous (fun y : ℝ => (K/2)*(y - a)*(b - y)) := by fun_prop
  have hHa : K / 2 * (a - a) * (b - a) = 0 := by ring
  have hHb : K / 2 * (b - a) * (b - b) = 0 := by ring
  have hHca : ContinuousAt (fun y : ℝ => (K/2)*(y - a)*(b - y)) a := hHcont.continuousAt
  have hHcb : ContinuousAt (fun y : ℝ => (K/2)*(y - a)*(b - y)) b := hHcont.continuousAt
  have hHatend : Tendsto (fun y : ℝ => (K/2)*(y - a)*(b - y)) (nhdsWithin a (Ioi a)) (nhds 0) := by
    have := hHca.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi a))
    rwa [hHa] at this
  have hHbtend : Tendsto (fun y : ℝ => (K/2)*(y - a)*(b - y)) (nhdsWithin b (Iio b)) (nhds 0) := by
    have := hHcb.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio b))
    rwa [hHb] at this
  have hfirst : e θ - (K/2)*(θ - a)*(b - θ) ≤ 0 := by
    refine alcl_chord_nonpos (φ := fun y : ℝ => e y - (K/2)*(y - a)*(b - y))
      (φ' := fun y : ℝ => e' y - (K/2)*(a + b - 2*y)) (φ'' := fun y : ℝ => e'' y + K)
      hab ?_ ?_ ?_ ?_ ?_ θ hθ
    · have := hlima.sub hHatend; simpa using this
    · have := hlimb.sub hHbtend; simpa using this
    · intro x hx
      exact (hd1 x hx).sub (alcl_hasDerivAt_quad K a b x)
    · intro x hx
      refine ((hd2 x hx).sub (alcl_hasDerivAt_quad' K a b x)).congr_deriv ?_
      ring
    · intro x hx
      have := (abs_le.mp (hb x hx)).1
      linarith
  have hsecond : -e θ - (K/2)*(θ - a)*(b - θ) ≤ 0 := by
    refine alcl_chord_nonpos (φ := fun y : ℝ => -e y - (K/2)*(y - a)*(b - y))
      (φ' := fun y : ℝ => -e' y - (K/2)*(a + b - 2*y)) (φ'' := fun y : ℝ => -e'' y + K)
      hab ?_ ?_ ?_ ?_ ?_ θ hθ
    · have := hlima.neg.sub hHatend; simpa using this
    · have := hlimb.neg.sub hHbtend; simpa using this
    · intro x hx
      exact (hd1 x hx).neg.sub (alcl_hasDerivAt_quad K a b x)
    · intro x hx
      refine ((hd2 x hx).neg.sub (alcl_hasDerivAt_quad' K a b x)).congr_deriv ?_
      ring
    · intro x hx
      have := (abs_le.mp (hb x hx)).2
      linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_le_chord_left {F : ℝ → ℝ} {K a b : ℝ} (hab : a < b)
    (hlim : Filter.Tendsto F (nhdsWithin a (Set.Ioi a)) (nhds 0))
    (hcont : Filter.Tendsto F (nhdsWithin b (Set.Iio b)) (nhds (F b)))
    (hd1 : ∀ θ ∈ Set.Ioo a b, DifferentiableAt ℝ F θ)
    (hd2 : ∀ θ ∈ Set.Ioo a b, DifferentiableAt ℝ (deriv F) θ)
    (hb1 : ∀ θ ∈ Set.Ioo a b, |deriv F θ| ≤ K)
    (hb2 : ∀ θ ∈ Set.Ioo a b, |deriv (deriv F) θ| ≤ K) :
    ∀ θ ∈ Set.Ioo a b, |F θ| ≤ ((θ - a) / (b - a)) * |F b| + (K / 2) * (θ - a) * (b - θ) := by
  intro θ hθ
  -- the chord `L` joining `(a,0)` to `(b,F b)`
  have hLcont : Continuous (fun x : ℝ => ((x - a) / (b - a)) * F b) := by fun_prop
  have hLa : (a - a) / (b - a) * F b = 0 := by ring
  have hLb : (b - a) / (b - a) * F b = F b := by
    rw [div_self (ne_of_gt (sub_pos.mpr hab)), one_mul]
  have hLca : ContinuousAt (fun x : ℝ => ((x - a) / (b - a)) * F b) a := hLcont.continuousAt
  have hLcb : ContinuousAt (fun x : ℝ => ((x - a) / (b - a)) * F b) b := hLcont.continuousAt
  have hLtenda : Tendsto (fun x : ℝ => ((x - a) / (b - a)) * F b) (nhdsWithin a (Ioi a)) (nhds 0) := by
    have := hLca.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi a))
    rwa [hLa] at this
  have hLtendb : Tendsto (fun x : ℝ => ((x - a) / (b - a)) * F b) (nhdsWithin b (Iio b)) (nhds (F b)) := by
    have := hLcb.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio b))
    rwa [hLb] at this
  -- `e = F - L` vanishes at both ends
  have hlima : Tendsto (fun x : ℝ => F x - ((x - a) / (b - a)) * F b) (nhdsWithin a (Ioi a)) (nhds 0) := by
    have := hlim.sub hLtenda
    simpa using this
  have hlimb : Tendsto (fun x : ℝ => F x - ((x - a) / (b - a)) * F b) (nhdsWithin b (Iio b)) (nhds 0) := by
    have := hcont.sub hLtendb
    simpa using this
  have hder1 : ∀ x ∈ Ioo a b, HasDerivAt (fun y : ℝ => F y - ((y - a) / (b - a)) * F b)
      ((fun y : ℝ => deriv F y - F b / (b - a)) x) x := by
    intro x hx
    exact (hd1 x hx).hasDerivAt.sub (alcl_hasDerivAt_lin (F b) a b x)
  have hder2 : ∀ x ∈ Ioo a b, HasDerivAt (fun y : ℝ => deriv F y - F b / (b - a))
      ((fun y : ℝ => deriv (deriv F) y) x) x := by
    intro x hx
    exact (hd2 x hx).hasDerivAt.sub_const (F b / (b - a))
  have hb : ∀ x ∈ Ioo a b, |(fun y : ℝ => deriv (deriv F) y) x| ≤ K := by
    intro x hx
    exact hb2 x hx
  have hmain : |(fun y : ℝ => F y - ((y - a) / (b - a)) * F b) θ| ≤ (K/2)*(θ - a)*(b - θ) :=
    alcl_chord_abs hab hlima hlimb hder1 hder2 hb θ hθ
  have hLabs : |((θ - a) / (b - a)) * F b| = ((θ - a) / (b - a)) * |F b| := by
    rw [abs_mul, abs_div, abs_of_pos (sub_pos.mpr hθ.1), abs_of_pos (sub_pos.mpr hab)]
  have h1 : |F θ| ≤ |F θ - ((θ - a) / (b - a)) * F b| + |((θ - a) / (b - a)) * F b| := by
    have := abs_add_le (F θ - ((θ - a) / (b - a)) * F b) (((θ - a) / (b - a)) * F b)
    rwa [sub_add_cancel] at this
  calc |F θ| ≤ |F θ - ((θ - a) / (b - a)) * F b| + |((θ - a) / (b - a)) * F b| := h1
    _ ≤ (K/2)*(θ - a)*(b - θ) + ((θ - a) / (b - a)) * |F b| := add_le_add hmain (le_of_eq hLabs)
    _ = ((θ - a) / (b - a)) * |F b| + (K / 2) * (θ - a) * (b - θ) := by ring

end Work.FTS_StreamBdry.SB25Aux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux.axisBterm_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25Aux

theorem axisBterm_le (θ0 Vv v0 ε : ℝ) (hθ0 : θ0 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hε : 0 ≤ ε) (hV : |Vv - v0| ≤ ε * (Real.pi / 2 - θ0)) :
    |Real.tan θ0 * (Vv - v0)| ≤ ε * (Real.pi / 2) := by
  have hδpos : 0 < Real.pi / 2 - θ0 := by linarith [hθ0.2]
  have hδlt : Real.pi / 2 - θ0 < Real.pi / 2 := by linarith [hθ0.1]
  have htanθ : 0 < Real.tan θ0 := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0.1 hθ0.2
  have htanδ : 0 < Real.tan (Real.pi / 2 - θ0) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hδpos hδlt
  -- `tan θ0 = 1 / tan (π/2 - θ0)` and `x ≤ tan x`, so `tan θ0 · (π/2 - θ0) ≤ 1 ≤ π/2`.
  have htan_eq : Real.tan θ0 = (Real.tan (Real.pi / 2 - θ0))⁻¹ := by
    have h := Real.tan_pi_div_two_sub (Real.pi / 2 - θ0)
    rwa [sub_sub_cancel] at h
  have hkey : Real.tan θ0 * (Real.pi / 2 - θ0) ≤ Real.pi / 2 := by
    rw [htan_eq, inv_mul_eq_div]
    have h1 : (Real.pi / 2 - θ0) / Real.tan (Real.pi / 2 - θ0) ≤ 1 := by
      rw [div_le_one htanδ]
      exact Real.le_tan hδpos.le hδlt
    linarith [Real.two_le_pi]
  calc |Real.tan θ0 * (Vv - v0)| = Real.tan θ0 * |Vv - v0| := by
        rw [abs_mul, abs_of_pos htanθ]
    _ ≤ Real.tan θ0 * (ε * (Real.pi / 2 - θ0)) := mul_le_mul_of_nonneg_left hV htanθ.le
    _ = ε * (Real.tan θ0 * (Real.pi / 2 - θ0)) := by ring
    _ ≤ ε * (Real.pi / 2) := mul_le_mul_of_nonneg_left hkey hε

end Work.FTS_StreamBdry.SB25Aux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux.axisD2_ident =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25Aux

theorem axisD2_ident (f : ℝ → ℝ) {θ0 : ℝ} (hθ0 : θ0 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (h1 : DifferentiableAt ℝ f θ0) (h2 : DifferentiableAt ℝ (deriv f) θ0) :
    deriv (deriv f) θ0
      = deriv (fun s => deriv f s - Real.tan s * f s) θ0
        + Real.tan θ0 * (deriv f θ0 - Real.tan θ0 * f θ0)
        + f θ0 * (1 + Real.sin θ0 ^ 2) / Real.cos θ0 ^ 2 := by
  have hcos_pos : 0 < Real.cos θ0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0.1], hθ0.2⟩
  have hcos : Real.cos θ0 ≠ 0 := ne_of_gt hcos_pos
  have htan_diff : DifferentiableAt ℝ Real.tan θ0 := Real.differentiableAt_tan.mpr hcos
  have hmul : DifferentiableAt ℝ (fun s => Real.tan s * f s) θ0 := htan_diff.mul h1
  -- the product rule for `tan · f`
  have hA : deriv (fun s => Real.tan s * f s) θ0
      = 1 / Real.cos θ0 ^ 2 * f θ0 + Real.tan θ0 * deriv f θ0 := by
    change deriv (Real.tan * f) θ0 = 1 / Real.cos θ0 ^ 2 * f θ0 + Real.tan θ0 * deriv f θ0
    rw [deriv_mul htan_diff h1, Real.deriv_tan]
  -- the derivative of the bracket `deriv f - tan · f`
  have hderiv_g : deriv (fun s => deriv f s - Real.tan s * f s) θ0
      = deriv (deriv f) θ0 - (1 / Real.cos θ0 ^ 2 * f θ0 + Real.tan θ0 * deriv f θ0) := by
    change deriv (deriv f - fun s => Real.tan s * f s) θ0
      = deriv (deriv f) θ0 - (1 / Real.cos θ0 ^ 2 * f θ0 + Real.tan θ0 * deriv f θ0)
    rw [deriv_sub h2 hmul, hA]
  rw [hderiv_g, Real.tan_eq_sin_div_cos]
  field_simp
  ring

end Work.FTS_StreamBdry.SB25Aux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux.axisDterm_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25Aux

theorem axisDterm_le (θ0 v0 : ℝ) (hθ0 : θ0 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |v0 * (1 - Real.sin θ0) ^ 2 / Real.cos θ0 ^ 3| ≤ |v0| * (Real.pi / 2 - θ0) := by
  have hcos : 0 < Real.cos θ0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0.1], hθ0.2⟩
  have hsin_nn : 0 ≤ Real.sin θ0 :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0.1.le (by linarith [hθ0.2, Real.pi_pos])
  have hsin_le1 : Real.sin θ0 ≤ 1 := Real.sin_le_one θ0
  have h1s : 0 ≤ 1 - Real.sin θ0 := by linarith
  have hY : 0 < Real.cos θ0 ^ 3 := pow_pos hcos 3
  -- `cos²θ = (1 - sin θ)(1 + sin θ)`
  have hcos2 : Real.cos θ0 ^ 2 = (1 - Real.sin θ0) * (1 + Real.sin θ0) := by
    have h := Real.sin_sq_add_cos_sq θ0
    nlinarith [h]
  -- `(1 - sin θ)² ≤ cos⁴θ`
  have hsq : (1 - Real.sin θ0) ^ 2 ≤ Real.cos θ0 ^ 4 := by
    have hle : 1 - Real.sin θ0 ≤ Real.cos θ0 ^ 2 := by
      rw [hcos2]; nlinarith
    have := pow_le_pow_left₀ h1s hle 2
    calc (1 - Real.sin θ0) ^ 2 ≤ (Real.cos θ0 ^ 2) ^ 2 := this
      _ = Real.cos θ0 ^ 4 := by ring
  -- hence `(1 - sin θ)² / cos³θ ≤ cos θ`
  have key1 : (1 - Real.sin θ0) ^ 2 / Real.cos θ0 ^ 3 ≤ Real.cos θ0 := by
    rw [div_le_iff₀ hY]
    nlinarith [hsq]
  -- and `cos θ = sin (π/2 - θ) ≤ π/2 - θ`
  have key2 : Real.cos θ0 ≤ Real.pi / 2 - θ0 := by
    rw [← Real.sin_pi_div_two_sub θ0]
    exact Real.sin_le (by linarith [hθ0.2])
  have key := le_trans key1 key2
  have hXY : 0 ≤ (1 - Real.sin θ0) ^ 2 / Real.cos θ0 ^ 3 := div_nonneg (sq_nonneg _) hY.le
  have habs : |v0 * (1 - Real.sin θ0) ^ 2 / Real.cos θ0 ^ 3|
      = |v0| * ((1 - Real.sin θ0) ^ 2 / Real.cos θ0 ^ 3) := by
    rw [mul_div_assoc, abs_mul, abs_of_nonneg hXY]
  rw [habs]
  exact mul_le_mul_of_nonneg_left key (abs_nonneg v0)

end Work.FTS_StreamBdry.SB25Aux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux.axisJterm_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25Aux

/-- The elementary inequality `sin t - t * cos t ≤ t ^ 3 / 3` for `t ≥ 0`.

(It is the statement that `t ↦ t ^ 3 / 3 - (sin t - t cos t)` is nondecreasing on `[0, ∞)`,
its derivative being `t * (t - sin t) ≥ 0`.) -/
theorem sin_sub_mul_cos_le_cube_div_three (t : ℝ) (ht : 0 ≤ t) :
    Real.sin t - t * Real.cos t ≤ t ^ 3 / 3 := by
  let f : ℝ → ℝ := fun x => x ^ 3 / 3 - (Real.sin x - x * Real.cos x)
  have hderiv (x : ℝ) : deriv f x = x ^ 2 - x * Real.sin x := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      rw [hderiv]
      have hx0 : 0 < x := by simpa using hx
      nlinarith [Real.sin_lt hx0]
  have h0 : f 0 = 0 := by simp [f]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp only [h0, f] at this
  linarith

/-- The numerical crux: for `0 < t < π/2`,
`(sin t - t cos t) (1 + cos²t) / sin³t ≤ π³ / 12`.

The proof is the sharp chain `sin t - t cos t ≤ t³/3` (previous lemma), `1 + cos²t ≤ 2`, and
Jordan's inequality `2t/π ≤ sin t` (so `sin³t ≥ (2t/π)³`), which combine to
`(t³/3)·2/(2t/π)³ = π³/12`. -/
theorem sin_sub_mul_cos_div_sin_cube_le (t : ℝ) (ht0 : 0 < t) (ht1 : t < Real.pi / 2) :
    (Real.sin t - t * Real.cos t) * (1 + Real.cos t ^ 2) / Real.sin t ^ 3
      ≤ Real.pi ^ 3 / 12 := by
  have hsin_pos : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos, ht1])
  have hS : Real.sin t - t * Real.cos t ≤ t ^ 3 / 3 :=
    sin_sub_mul_cos_le_cube_div_three t ht0.le
  have hc2 : 1 + Real.cos t ^ 2 ≤ 2 := by
    have := Real.cos_sq_le_one t
    linarith
  have hJ1 : (Real.sin t - t * Real.cos t) * (1 + Real.cos t ^ 2) ≤ 2 * t ^ 3 / 3 := by
    have h1 := mul_le_mul_of_nonneg_right hS (by positivity : (0 : ℝ) ≤ 1 + Real.cos t ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hc2 (by positivity : (0 : ℝ) ≤ t ^ 3 / 3)
    nlinarith [h1, h2]
  have hsin3 : (2 / Real.pi * t) ^ 3 ≤ Real.sin t ^ 3 := by
    have h := Real.mul_le_sin ht0.le (le_of_lt ht1)
    exact pow_le_pow_left₀ (by positivity) h 3
  have hR : 2 * t ^ 3 / 3 ≤ (Real.pi ^ 3 / 12) * Real.sin t ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hsin3 (by positivity : (0 : ℝ) ≤ Real.pi ^ 3 / 12)
    have heq : (Real.pi ^ 3 / 12) * (2 / Real.pi * t) ^ 3 = 2 * t ^ 3 / 3 := by
      field_simp
      ring
    linarith [h, heq]
  rw [div_le_iff₀ (pow_pos hsin_pos 3)]
  linarith [hJ1, hR]

theorem axisJterm_le (θ0 Jv ε : ℝ) (hθ0 : θ0 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hε : 0 ≤ ε)
    (hJ : |Jv| ≤ ε * (Real.sin (Real.pi / 2 - θ0) - (Real.pi / 2 - θ0) * Real.cos (Real.pi / 2 - θ0))) :
    |Jv * (1 + Real.sin θ0 ^ 2) / Real.cos θ0 ^ 3| ≤ ε * (Real.pi ^ 3 / 12) := by
  set t := Real.pi / 2 - θ0 with ht
  have ht0 : 0 < t := by rw [ht]; linarith [hθ0.2]
  have ht1 : t < Real.pi / 2 := by rw [ht]; linarith [hθ0.1]
  have hcos_pos : 0 < Real.cos θ0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0.1], hθ0.2⟩
  have hsin_eq : Real.sin θ0 = Real.cos t := by
    rw [ht]; exact (Real.cos_pi_div_two_sub θ0).symm
  have hcos_eq : Real.cos θ0 = Real.sin t := by
    rw [ht]; exact (Real.sin_pi_div_two_sub θ0).symm
  have hJ' : |Jv| ≤ ε * (Real.sin t - t * Real.cos t) := by
    have hthis : Real.sin (Real.pi / 2 - θ0) - (Real.pi / 2 - θ0) * Real.cos (Real.pi / 2 - θ0)
        = Real.sin t - t * Real.cos t := by
      rw [ht]
    rw [hthis] at hJ
    exact hJ
  have hA : 0 < 1 + Real.sin θ0 ^ 2 := by positivity
  have hB : 0 < Real.cos θ0 ^ 3 := pow_pos hcos_pos 3
  have hL : |Jv * (1 + Real.sin θ0 ^ 2) / Real.cos θ0 ^ 3|
      = |Jv| * (1 + Real.cos t ^ 2) / Real.sin t ^ 3 := by
    rw [abs_div, abs_mul, abs_of_pos hA, abs_of_pos hB, hsin_eq, hcos_eq]
  rw [hL]
  have hsin_pos : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos, ht1])
  have hF : 0 ≤ (1 + Real.cos t ^ 2) / Real.sin t ^ 3 :=
    div_nonneg (by positivity) (pow_nonneg hsin_pos.le 3)
  calc |Jv| * (1 + Real.cos t ^ 2) / Real.sin t ^ 3
      = |Jv| * ((1 + Real.cos t ^ 2) / Real.sin t ^ 3) := by ring
    _ ≤ ε * (Real.sin t - t * Real.cos t) * ((1 + Real.cos t ^ 2) / Real.sin t ^ 3) :=
        mul_le_mul_of_nonneg_right hJ' hF
    _ = ε * ((Real.sin t - t * Real.cos t) * (1 + Real.cos t ^ 2) / Real.sin t ^ 3) := by ring
    _ ≤ ε * (Real.pi ^ 3 / 12) :=
        mul_le_mul_of_nonneg_left (sin_sub_mul_cos_div_sin_cube_le t ht0 ht1) hε

end Work.FTS_StreamBdry.SB25Aux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux.eventually_uniform_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25Aux

/-- **Uniform smallness out of pointwise smallness plus an equi-Lipschitz bound.**

Given a family `F z θ` that is (i) pointwise in `θ` tending to `0` as `z → ∞` and
(ii) Lipschitz in `θ` with a constant `K` *independent of* `z`, on the compact
interval `[a,b]`, the convergence is uniform: eventually in `z` all values on
`[a,b]` are `≤ ε` in absolute value.

Proof: cover the compact interval `[a,b]` by finitely many balls of radius
`δ = ε / (2 (K+1))` (centred at points of `[a,b]`).  For each centre `θᵢ` the
pointwise convergence gives `|F z θᵢ| < ε/2` eventually, and there are finitely
many centres, so eventually this holds simultaneously for all of them.  For an
arbitrary `θ ∈ [a,b]` pick a centre `θᵢ` with `|θ - θᵢ| ≤ δ` and split
`|F z θ| ≤ |F z θ - F z θᵢ| + |F z θᵢ| ≤ K δ + ε/2 ≤ ε`, using
`K δ = K ε / (2(K+1)) ≤ ε/2` (valid since `K ≥ 0`).  (The hypothesis `hab` is
not needed: for `a > b` the interval is empty and the claim is vacuous.) -/
theorem eventually_uniform_abs_le {F : ℝ → ℝ → ℝ} {K a b ε : ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K)
    (hlip : ∀ z, ∀ θ ∈ Set.Icc a b, ∀ θ' ∈ Set.Icc a b, |F z θ - F z θ'| ≤ K * |θ - θ'|)
    (hpt : ∀ θ ∈ Set.Icc a b, Filter.Tendsto (fun z => F z θ) Filter.atTop (nhds 0)) (hε : 0 < ε) :
    ∀ᶠ z in Filter.atTop, ∀ θ ∈ Set.Icc a b, |F z θ| ≤ ε := by
  -- `a ∈ [a,b]` (this is the only use of `hab`; the argument also works for the empty interval).
  have hmem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  -- The mesh size of the finite cover, chosen so that `K δ ≤ ε/2`.
  set δ : ℝ := ε / (2 * (K + 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; positivity
  have hKδ : K * δ ≤ ε / 2 := by
    rw [hδdef]
    field_simp
    nlinarith
  -- Cover `[a,b]` by finitely many δ-balls centred at points of `[a,b]`.
  obtain ⟨t, ht_sub, ht_fin, ht_cov⟩ :=
    finite_cover_balls_of_compact (s := Set.Icc a b) isCompact_Icc hδpos
  -- Simultaneously, for all centres, `|F z θᵢ| < ε/2` eventually.
  have hcov : ∀ᶠ z in Filter.atTop, ∀ i ∈ t, |F z i| < ε / 2 := by
    rw [Set.Finite.eventually_all ht_fin]
    intro i hi
    have hp : ∀ᶠ y in nhds (0 : ℝ), |y| < ε / 2 :=
      IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) (by simp; positivity)
    exact (hpt i (ht_sub hi)).eventually hp
  filter_upwards [hcov] with z hz
  intro θ hθ
  -- Pick a centre `i` of the cover with `θ` in its ball.
  rcases Set.mem_iUnion₂.mp (ht_cov hθ) with ⟨i, hi, hiθ⟩
  have hdist : |θ - i| ≤ δ := by
    rw [Metric.mem_ball, Real.dist_eq] at hiθ
    linarith
  have h1 : |F z θ| ≤ |F z θ - F z i| + |F z i| := by
    have := dist_triangle (F z θ) (F z i) 0
    simpa [Real.dist_eq, sub_zero] using this
  calc |F z θ| ≤ |F z θ - F z i| + |F z i| := h1
    _ ≤ K * δ + ε / 2 := add_le_add
        ((hlip z θ hθ i (ht_sub hi)).trans (mul_le_mul_of_nonneg_left hdist hK))
        (le_of_lt (hz i hi))
    _ ≤ ε / 2 + ε / 2 := add_le_add hKδ le_rfl
    _ = ε := by ring

end Work.FTS_StreamBdry.SB25Aux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25Aux2.axisTail_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux2.axisTail_bound`

The 1-D tail bound used by leaf B4 (`axis_d2_bound`): for `W := f·cos`,

  `|W θ₀ + v₀(1 - sin θ₀)| ≤ ε (sin δ - δ cos δ)`,  `δ = π/2 - θ₀`,

under `|f| ≤ B` on `(0,π/2)`, `f` differentiable there, and
`|f' - tan·f - v₀| ≤ ε(π/2 - t)` on `[θ₀, π/2)`.

This is the `W`-half of the axis expansion: `J := W + v₀(1 - sin)` satisfies
`J' = cos·(f' - tan·f - v₀)`, so `|J'| ≤ ε cos t (π/2 - t)` on `[θ₀, π/2)`, and `J → 0` at
`π/2` because `f` is bounded there.  The fundamental theorem of calculus on the half-open
interval (`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto`, with the integrability
of `deriv J` from its a.e. bound `ε(π/2 - θ₀)` and `aestronglyMeasurable_deriv`) gives
`|J θ₀| ≤ ∫_{θ₀}^{π/2}|J'| ≤ ε ∫_{θ₀}^{π/2} cos t (π/2 - t) dt = ε(sin δ - δ cos δ)`,
the last integral being evaluated with the primitive `(π/2 - t) sin t - cos t`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux2

theorem axisTail_bound (f : ℝ → ℝ) (v0 B ε θ0 : ℝ) (hθ0 : θ0 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ f θ)
    (hb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ B)
    (hV : ∀ t ∈ Set.Ico θ0 (Real.pi / 2),
      |deriv f t - Real.tan t * f t - v0| ≤ ε * (Real.pi / 2 - t)) :
    |f θ0 * Real.cos θ0 + v0 * (1 - Real.sin θ0)| ≤
      ε * (Real.sin (Real.pi / 2 - θ0) - (Real.pi / 2 - θ0) * Real.cos (Real.pi / 2 - θ0)) := by
  set J : ℝ → ℝ := fun t => f t * Real.cos t + v0 * (1 - Real.sin t) with hJdef
  have hlt : θ0 < Real.pi / 2 := hθ0.2
  have hθ0pos : 0 < θ0 := hθ0.1
  -- the derivative of `J` on `(0, π/2)`
  have hJderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt J (Real.cos x * (deriv f x - Real.tan x * f x - v0)) x := by
    intro x hx
    have hcx : Real.cos x ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩)
    have h1 : HasDerivAt (fun t => f t * Real.cos t)
        (deriv f x * Real.cos x + f x * (-Real.sin x)) x :=
      (hf x hx).hasDerivAt.mul (Real.hasDerivAt_cos x)
    have h2 : HasDerivAt (fun t => v0 * (1 - Real.sin t)) (v0 * (-Real.cos x)) x := by
      have h1' : HasDerivAt (fun t => 1 - Real.sin t) (-Real.cos x) x :=
        (Real.hasDerivAt_sin x).const_sub 1
      exact h1'.const_mul v0
    have h3 : HasDerivAt (fun t => f t * Real.cos t + v0 * (1 - Real.sin t))
        (deriv f x * Real.cos x + f x * (-Real.sin x) + v0 * (-Real.cos x)) x := h1.add h2
    rw [hJdef]
    convert h3 using 1
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    ring
  -- `deriv J` is bounded on `(θ₀, π/2]`
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioc θ0 (Real.pi / 2))),
      ‖deriv J x‖ ≤ ε * (Real.pi / 2 - θ0) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (Real.volume_singleton (a := Real.pi / 2))
    intro x hx
    simp only [Set.mem_ofPred_eq, not_imp] at hx
    obtain ⟨hxIoc, hxlt⟩ := hx
    simp only [Set.mem_singleton_iff]
    by_contra hne
    have hxoo : x ∈ Set.Ioo θ0 (Real.pi / 2) := ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hne⟩
    have hx0 : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hθ0pos, hxoo.1], hxoo.2⟩
    have hd : deriv J x = Real.cos x * (deriv f x - Real.tan x * f x - v0) :=
      (hJderiv x hx0).deriv
    have hVx : |deriv f x - Real.tan x * f x - v0| ≤ ε * (Real.pi / 2 - x) :=
      hV x ⟨hxoo.1.le, hxoo.2⟩
    have hcosnn : 0 ≤ Real.cos x :=
      le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx0.1], hx0.2⟩)
    have hcle : Real.cos x ≤ 1 := Real.cos_le_one x
    have hdle : ε * (Real.pi / 2 - x) ≤ ε * (Real.pi / 2 - θ0) :=
      mul_le_mul_of_nonneg_left (by linarith [hxoo.1]) hε
    have hprod : Real.cos x * |deriv f x - Real.tan x * f x - v0| ≤
        1 * (ε * (Real.pi / 2 - θ0)) :=
      mul_le_mul hcle (le_trans hVx hdle) (abs_nonneg _) (by norm_num)
    rw [hd, Real.norm_eq_abs, abs_mul, abs_of_nonneg hcosnn] at hxlt
    linarith [hprod]
  have hJint : IntervalIntegrable (deriv J) volume θ0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le]
    exact MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
      (aestronglyMeasurable_deriv J _) _ hbound
  -- one-sided limits of `J`
  have hJleft : Filter.Tendsto J (nhdsWithin θ0 (Set.Ioi θ0)) (nhds (J θ0)) := by
    have hfcont : ContinuousAt f θ0 := (hf θ0 hθ0).continuousAt
    have hcont : ContinuousAt J θ0 := by
      rw [hJdef]
      exact (hfcont.mul Real.continuous_cos.continuousAt).add
        (continuousAt_const.mul (continuousAt_const.sub Real.continuous_sin.continuousAt))
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hJright : Filter.Tendsto J (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hev : ∀ᶠ t in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        |J t| ≤ B * Real.cos t + |v0| * (1 - Real.sin t) := by
      filter_upwards [Ioo_mem_nhdsLT hlt] with t ht
      have ht0 : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith [hθ0pos, ht.1], ht.2⟩
      have hft : |f t| ≤ B := hb t ht0
      have hcosnn : 0 ≤ Real.cos t :=
        le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, ht0.1], ht0.2⟩)
      have hsinnn : 0 ≤ 1 - Real.sin t := by have := Real.sin_le_one t; linarith
      rw [hJdef]
      calc |f t * Real.cos t + v0 * (1 - Real.sin t)|
          ≤ |f t * Real.cos t| + |v0 * (1 - Real.sin t)| := abs_add_le _ _
        _ = |f t| * Real.cos t + |v0| * (1 - Real.sin t) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hcosnn, abs_of_nonneg hsinnn]
        _ ≤ B * Real.cos t + |v0| * (1 - Real.sin t) := by
              have := mul_le_mul_of_nonneg_right hft hcosnn
              linarith
    have hmaj : Filter.Tendsto (fun t => B * Real.cos t + |v0| * (1 - Real.sin t))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have hcos : Filter.Tendsto (fun t => Real.cos t)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa using (Real.continuous_cos.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
          Filter.Tendsto (fun t => Real.cos t) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
            (nhds (Real.cos (Real.pi / 2))))
      have hsin : Filter.Tendsto (fun t => Real.sin t)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 1) := by
        simpa using (Real.continuous_sin.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
          Filter.Tendsto (fun t => Real.sin t) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
            (nhds (Real.sin (Real.pi / 2))))
      have h1 : Filter.Tendsto (fun t => B * Real.cos t)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa using (tendsto_const_nhds (x := B)).mul hcos
      have h2 : Filter.Tendsto (fun t => |v0| * (1 - Real.sin t))
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        have := (tendsto_const_nhds (x := |v0|)).mul
          ((tendsto_const_nhds (x := (1 : ℝ))).sub hsin)
        simpa using this
      simpa using h1.add h2
    have hsq := squeeze_zero' (Filter.Eventually.of_forall (fun t => abs_nonneg (J t))) hev hmaj
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using hsq
  -- fundamental theorem of calculus on `[θ₀, π/2]`
  have hFTC : ∫ y in θ0..(Real.pi / 2), deriv J y = 0 - J θ0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hlt
      (f := J) (f' := deriv J) (fa := J θ0) (fb := 0)
      (fun x hx => ((hJderiv x ⟨by linarith [hθ0pos, hx.1], hx.2⟩).differentiableAt).hasDerivAt)
      hJint hJleft hJright
  have h1 : |J θ0| ≤ ∫ y in θ0..(Real.pi / 2), |deriv J y| := by
    have := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
      (a := θ0) (b := Real.pi / 2) (f := fun y => deriv J y) hlt.le
    rw [hFTC] at this
    simpa using this
  have h2 : ∫ y in θ0..(Real.pi / 2), |deriv J y|
      ≤ ∫ y in θ0..(Real.pi / 2), ε * (Real.cos y * (Real.pi / 2 - y)) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hlt.le hJint.abs ?_ (fun x hx => ?_)
    · apply ContinuousOn.intervalIntegrable
      fun_prop
    · have hx0 : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith [hθ0pos, hx.1], hx.2⟩
      have hd : deriv J x = Real.cos x * (deriv f x - Real.tan x * f x - v0) :=
        (hJderiv x hx0).deriv
      have hVx : |deriv f x - Real.tan x * f x - v0| ≤ ε * (Real.pi / 2 - x) :=
        hV x ⟨hx.1.le, hx.2⟩
      have hcosnn : 0 ≤ Real.cos x :=
        le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx0.1], hx0.2⟩)
      rw [hd, abs_mul, abs_of_nonneg hcosnn]
      have hh := mul_le_mul_of_nonneg_left hVx hcosnn
      nlinarith [hh, hcosnn, hε]
  have h3 : ∫ y in θ0..(Real.pi / 2), ε * (Real.cos y * (Real.pi / 2 - y))
      = ε * (Real.sin (Real.pi / 2 - θ0)
          - (Real.pi / 2 - θ0) * Real.cos (Real.pi / 2 - θ0)) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hprim : ∀ y : ℝ, HasDerivAt (fun s : ℝ => (Real.pi / 2 - s) * Real.sin s - Real.cos s)
        (Real.cos y * (Real.pi / 2 - y)) y := by
      intro y
      have h1 : HasDerivAt (fun s : ℝ => Real.pi / 2 - s) (-1) y := by
        have h2 : HasDerivAt (fun s : ℝ => -s) (-1) y := (hasDerivAt_id y).neg
        have h3 : HasDerivAt (fun s : ℝ => (Real.pi / 2) + (-s)) (-1) y :=
          h2.const_add (Real.pi / 2)
        simpa [sub_eq_add_neg] using h3
      have h2 := h1.mul (Real.hasDerivAt_sin y)
      have h3 := h2.sub (Real.hasDerivAt_cos y)
      convert h3 using 1
      ring
    have hint : IntervalIntegrable (fun y : ℝ => Real.cos y * (Real.pi / 2 - y)) volume θ0
        (Real.pi / 2) := by
      apply ContinuousOn.intervalIntegrable
      fun_prop
    have h4 := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => (Real.pi / 2 - s) * Real.sin s - Real.cos s)
      (f' := fun y : ℝ => Real.cos y * (Real.pi / 2 - y)) (fun x _ => hprim x) hint
    rw [h4]
    have hP : (Real.pi / 2 - Real.pi / 2) * Real.sin (Real.pi / 2) - Real.cos (Real.pi / 2) = 0 := by
      simp
    rw [hP, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    ring
  rw [hJdef] at h1
  linarith [h1, h2, h3]

end Work.FTS_StreamBdry.SB25Aux2
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.P2Aux.FamOde.Weight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FamOde.Weight` — the integrating factor and the dominating function

Setting of `Work.FTS_StreamBdry.SB3.P2Aux.fam_ode_deriv_bound_proved`: the singular
first-order equation `w' + c(θ)w = H` with `c(θ) = 4 cos 2θ / sin 2θ - tan θ`.  We record the
integrating factor `m(θ) = sin²θ cos³θ` (`wfn`; `m' = m·c`), the dominating function
`Φ(θ) = (A/2) sin θ cos²θ + C sin²θ cos³θ` (`phfn`; `m·(A/sin 2θ + C) = Φ`) and the
elementary size bounds for both, in particular the endpoint behaviour
`m(θ) ≥ θ²/(2π²)` on `(0, π/4]` and `m(θ) ≥ 2(π/2-θ)³/π³` on `[π/4, π/2)`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB3.P2Aux.FamOde

/-- The coefficient `c(θ) = 4 cos(2θ)/sin(2θ) - tan θ` of the ODE. -/
def coco (θ : ℝ) : ℝ := 4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ

/-- The integrating factor `m(θ) = sin²θ cos³θ`; `m' = m·c`. -/
def wfn (θ : ℝ) : ℝ := Real.sin θ ^ 2 * Real.cos θ ^ 3











end Work.FTS_StreamBdry.SB3.P2Aux.FamOde
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.P2Aux.exists_anchor_left =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB3.P2Aux


end Work.FTS_StreamBdry.SB3.P2Aux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.P2Aux.exists_anchor_right =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB3.P2Aux


end Work.FTS_StreamBdry.SB3.P2Aux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SBpsiP.SelfBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SBpsiP.SelfBound` — the elementary scaled-integral bound

For `-1 < c` and `|φ| ≤ B` on `(0,1]`, the scaled integral `∫₀¹ v^c·φ v dv` is bounded by
`B/(c+1) = B·∫₀¹ v^c dv`.  The proof is `intervalIntegral.norm_integral_le_of_norm_le`
(whose domination hypothesis is only required on `Ioc 0 1`, so the (irrelevant) values of `φ`
at `v = 0` are never used) together with `integral_rpow`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SBpsiP

set_option autoImplicit false

/-- **The scaled-integral bound.**  If `-1 < c` and `|φ v| ≤ B` for `v ∈ (0,1]`, then
`|∫₀¹ v^c·φ v dv| ≤ B/(c+1)`. -/
theorem J_bound_self {c B : ℝ} (hc : -1 < c) (hB : 0 ≤ B) {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Ioc (0 : ℝ) 1))
    (hφ : ∀ v ∈ Set.Ioc (0 : ℝ) 1, |φ v| ≤ B) :
    |∫ v in (0 : ℝ)..1, v ^ c * φ v| ≤ B / (c + 1) := by
  have hint : IntervalIntegrable (fun v : ℝ => B * v ^ c) volume (0 : ℝ) 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hc).const_mul B
  have hpt : ∀ v ∈ Set.Ioc (0 : ℝ) 1, ‖v ^ c * φ v‖ ≤ B * v ^ c := by
    intro v hv
    have hv0 : 0 < v := hv.1
    have hvc : (0 : ℝ) ≤ v ^ c := Real.rpow_nonneg hv0.le c
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hvc]
    calc v ^ c * |φ v| ≤ v ^ c * B := mul_le_mul_of_nonneg_left (hφ v hv) hvc
      _ = B * v ^ c := by ring
  have hmain : ‖∫ v in (0 : ℝ)..1, v ^ c * φ v‖ ≤ ∫ v in (0 : ℝ)..1, B * v ^ c :=
    intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (Filter.Eventually.of_forall hpt) hint
  have hval : (∫ v in (0 : ℝ)..1, B * v ^ c) = B / (c + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hc), Real.one_rpow,
      Real.zero_rpow (by linarith : c + 1 ≠ 0)]
    ring
  rw [hval] at hmain
  rwa [Real.norm_eq_abs] at hmain

end Work.FTS_StreamBdry.SBpsiP
end
end
-- ===== merged: Submission.Work.H2.T1Q.SinRatioBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `π` must be the real number `Real.pi` (the file is built with `autoImplicit = false`,
-- so without this the notation is not even in scope).
open scoped Real

namespace Work.H2.T1Q

/-- In either singular window `θ ∈ (ζ/2, ζ)` or `θ ∈ (π/2 - ζ, π/2 - ζ/2)` (`ζ > 0`) one has
`|sin(2θ)| ≤ 2ζ`, hence `|sin(2θ)|·(2/ζ) ≤ 4`.

Both windows are images of `(ζ/2, ζ)` under `t ↦ t` resp. `t ↦ π/2 - t`, and on either the
argument `2θ` of the sine has modulus `≤ 2ζ`; the conclusion follows from `|sin x| ≤ |x|`. -/
theorem SinRatioBound {ζ θ : ℝ} (hζ : 0 < ζ)
    (h : (ζ / 2 < θ ∧ θ < ζ) ∨ (π / 2 - ζ < θ ∧ θ < π / 2 - ζ / 2)) :
    |Real.sin (2 * θ)| * (2 / ζ) ≤ 4 := by
  have hsin : |Real.sin (2 * θ)| ≤ 2 * ζ := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- First window: `0 < 2θ < 2ζ`.
      have habs : |2 * θ| ≤ 2 * ζ := by
        rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * θ)]
        linarith
      calc |Real.sin (2 * θ)| ≤ |2 * θ| := Real.abs_sin_le_abs
        _ ≤ 2 * ζ := habs
    · -- Second window: reflections of the first, `sin(π - x) = sin x`.
      have hkey : 2 * θ = π - 2 * (π / 2 - θ) := by ring
      have hsin2 : Real.sin (2 * θ) = Real.sin (2 * (π / 2 - θ)) := by
        rw [hkey, Real.sin_pi_sub]
      have habs : |2 * (π / 2 - θ)| ≤ 2 * ζ := by
        rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * (π / 2 - θ))]
        linarith
      calc |Real.sin (2 * θ)| = |Real.sin (2 * (π / 2 - θ))| := by rw [hsin2]
        _ ≤ |2 * (π / 2 - θ)| := Real.abs_sin_le_abs
        _ ≤ 2 * ζ := habs
  have hfac : 0 ≤ 2 / ζ := by positivity
  calc |Real.sin (2 * θ)| * (2 / ζ) ≤ (2 * ζ) * (2 / ζ) :=
        mul_le_mul_of_nonneg_right hsin hfac
    _ = 4 := by field_simp; norm_num

end Work.H2.T1Q
end
-- ===== merged: Submission.Work.H2.T1Q.SmoothTransitionDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open Filter

namespace Work.H2.T1Q

/-!
# The derivative of `Real.smoothTransition`

`Real.smoothTransition` is Mathlib's `C^∞` function which is `0` on `(-∞, 0]` and `1` on
`[1, ∞)` (defined as `expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))`).

This file records the elementary consequences for its derivative `deriv Real.smoothTransition`:

* it vanishes on `(-∞, 0]`;
* it vanishes on `[1, ∞)`;
* it is bounded.

The first two statements are proved pointwise: away from the two junction points `0` and `1`
the function is *locally constant*, so `Filter.EventuallyEq.deriv_eq` applies; at `0` (resp.
`1`) the function is constant on the half line `Iic 0` (resp. `Ici 1`), so the within-derivative
there is `0`, and since `smoothTransition` is differentiable at the point, the within-derivative
on a set with `UniqueDiffWithinAt` agrees with the ordinary derivative.

For the boundedness we use that `deriv Real.smoothTransition` is continuous (as
`smoothTransition` is `C^∞`), hence bounded on the compact interval `[0,1]`, while it vanishes
off `[0,1]`.
-/

/-- `deriv Real.smoothTransition` vanishes strictly to the left of `0`, where the function is
locally `0`. -/
private lemma deriv_smoothTransition_of_lt_zero {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have hmem : Set.Iio (0 : ℝ) ∈ 𝓝 x := Iio_mem_nhds hx
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hmem] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  rw [heq.deriv_eq, deriv_const]

/-- `deriv Real.smoothTransition 0 = 0`: the function is `0` on the half line `Iic 0`. -/
private lemma deriv_smoothTransition_at_zero : deriv Real.smoothTransition 0 = 0 := by
  have hdiff : DifferentiableAt ℝ Real.smoothTransition (0 : ℝ) := by fun_prop
  have h2 : HasDerivWithinAt Real.smoothTransition (deriv Real.smoothTransition 0)
      (Set.Iic 0) 0 := hdiff.hasDerivAt.hasDerivWithinAt
  have h1 : HasDerivWithinAt Real.smoothTransition 0 (Set.Iic 0) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Set.Iic 0) (0 : ℝ)).congr
      (fun y hy => Real.smoothTransition.zero_of_nonpos hy) (by simp)
  have hd1 := h1.derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))
  have hd2 := h2.derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))
  exact hd2.symm.trans hd1

/-- `deriv Real.smoothTransition` vanishes strictly to the right of `1`, where the function is
locally `1`. -/
private lemma deriv_smoothTransition_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have hmem : Set.Ioi (1 : ℝ) ∈ 𝓝 x := Ioi_mem_nhds hx
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [hmem] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
  rw [heq.deriv_eq, deriv_const]

/-- `deriv Real.smoothTransition 1 = 0`: the function is `1` on the half line `Ici 1`. -/
private lemma deriv_smoothTransition_at_one : deriv Real.smoothTransition 1 = 0 := by
  have hdiff : DifferentiableAt ℝ Real.smoothTransition (1 : ℝ) := by fun_prop
  have h2 : HasDerivWithinAt Real.smoothTransition (deriv Real.smoothTransition 1)
      (Set.Ici 1) 1 := hdiff.hasDerivAt.hasDerivWithinAt
  have h1 : HasDerivWithinAt Real.smoothTransition 0 (Set.Ici 1) 1 :=
    (hasDerivWithinAt_const (1 : ℝ) (Set.Ici 1) (1 : ℝ)).congr
      (fun y hy => Real.smoothTransition.one_of_one_le hy) (by simp)
  have hd1 := h1.derivWithin (uniqueDiffWithinAt_Ici (1 : ℝ))
  have hd2 := h2.derivWithin (uniqueDiffWithinAt_Ici (1 : ℝ))
  exact hd2.symm.trans hd1

theorem SmoothTransitionDeriv :
    (∀ x : ℝ, x ≤ 0 → deriv Real.smoothTransition x = 0) ∧
    (∀ x : ℝ, 1 ≤ x → deriv Real.smoothTransition x = 0) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ M) := by
  have hleft : ∀ x : ℝ, x ≤ 0 → deriv Real.smoothTransition x = 0 := by
    intro x hx
    rcases lt_or_eq_of_le hx with h | h
    · exact deriv_smoothTransition_of_lt_zero h
    · rw [h]; exact deriv_smoothTransition_at_zero
  have hright : ∀ x : ℝ, 1 ≤ x → deriv Real.smoothTransition x = 0 := by
    intro x hx
    rcases lt_or_eq_of_le hx with h | h
    · exact deriv_smoothTransition_of_one_lt h
    · rw [← h]; exact deriv_smoothTransition_at_one
  refine ⟨hleft, hright, ?_⟩
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (1 : ℕ∞))).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  rcases le_or_gt x 0 with hx | hx
  · rw [hleft x hx, abs_zero]
    exact le_max_right _ _
  · rcases le_or_gt 1 x with hx1 | hx1
    · rw [hright x hx1, abs_zero]
      exact le_max_right _ _
    · have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hx, le_of_lt hx1⟩
      have hb := hC x hxI
      rw [Real.norm_eq_abs] at hb
      exact le_trans hb (le_max_left _ _)

end Work.H2.T1Q
end
-- ===== merged: Submission.Work.LWP.BiotSavart.crossRecover =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LWP.BiotSavart

open Matrix

/-- The self dot product of a nonzero vector of `Fin 3 → ℝ` is nonzero: it is a sum of
squares of the coordinates. -/
lemma dotProduct_self_ne_zero_three {v : Fin 3 → ℝ} (hv : v ≠ 0) : v ⬝ᵥ v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ v j * v j :=
    fun j _ => mul_self_nonneg _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
  exact mul_self_eq_zero.mp (hz i (Finset.mem_univ i))

theorem crossRecover (x a d : Fin 3 → ℝ) (hd : d ≠ 0) (hda : crossProduct d a ≠ 0) :
    x = (d ⬝ᵥ d)⁻¹ • crossProduct d (crossProduct x d)
        + (((((crossProduct (crossProduct x a) d) ⬝ᵥ a) * (d ⬝ᵥ d) + (d ⬝ᵥ a) * ((crossProduct (crossProduct x d) a) ⬝ᵥ d))
            / ((d ⬝ᵥ d) * (a ⬝ᵥ a) - (d ⬝ᵥ a) * (d ⬝ᵥ a))) * (d ⬝ᵥ d)⁻¹) • d := by
  -- The self dot product of `d` is nonzero.
  have hdd : (d ⬝ᵥ d) ≠ 0 := dotProduct_self_ne_zero_three hd
  -- The Binet–Cauchy denominator is the square of `d ⨯₃ a`, hence nonzero.
  have hD : ((d ⬝ᵥ d) * (a ⬝ᵥ a) - (d ⬝ᵥ a) * (d ⬝ᵥ a)) ≠ 0 := by
    rw [show (d ⬝ᵥ d) * (a ⬝ᵥ a) - (d ⬝ᵥ a) * (d ⬝ᵥ a)
          = (crossProduct d a) ⬝ᵥ (crossProduct d a) by
        rw [cross_dot_cross, dotProduct_comm a d]]
    exact dotProduct_self_ne_zero_three hda
  -- The numerator equals `(x ⬝ᵥ d)` times the denominator.
  have hN : ((crossProduct (crossProduct x a) d) ⬝ᵥ a) * (d ⬝ᵥ d)
        + (d ⬝ᵥ a) * ((crossProduct (crossProduct x d) a) ⬝ᵥ d)
      = (x ⬝ᵥ d) * ((d ⬝ᵥ d) * (a ⬝ᵥ a) - (d ⬝ᵥ a) * (d ⬝ᵥ a)) := by
    simp_rw [cross_apply, vec3_dotProduct]
    dsimp only [Matrix.cons_val]
    ring
  -- Hence the scalar coefficient is `(x ⬝ᵥ d) * (d ⬝ᵥ d)⁻¹`.
  have hc : ((((crossProduct (crossProduct x a) d) ⬝ᵥ a) * (d ⬝ᵥ d)
        + (d ⬝ᵥ a) * ((crossProduct (crossProduct x d) a) ⬝ᵥ d))
        / ((d ⬝ᵥ d) * (a ⬝ᵥ a) - (d ⬝ᵥ a) * (d ⬝ᵥ a))) = (x ⬝ᵥ d) := by
    rw [hN]
    exact mul_div_cancel_right₀ (x ⬝ᵥ d) hD
  rw [hc, cross_cross_eq_smul_sub_smul']
  rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hdd, one_smul]
  rw [mul_comm (d ⬝ᵥ d)⁻¹ (x ⬝ᵥ d), sub_add_cancel]

end Work.LWP.BiotSavart
end
-- ===== merged: Submission.Work.LWP.BiotSavart.cube_inv_mul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LWP.BiotSavart

/-- For `0 ≤ X`, `0 ≤ a` and `X ≤ 2a`, one has `a^{-3}·a ≤ 4·X^{-2}`, i.e.
`1/a² ≤ 4/X²`. -/
theorem cube_inv_mul_le {a X : ℝ} (hX : 0 ≤ X) (ha : 0 ≤ a) (h1 : X ≤ 2 * a) (h2 : a ≤ 3 * X / 2) : (a ^ (3 : ℕ))⁻¹ * a ≤ 4 * (X ^ 2)⁻¹ := by
  rcases eq_or_lt_of_le ha with rfl | hapos
  · have hX0 : X = 0 := le_antisymm (by linarith) hX
    subst hX0
    norm_num
  · have hXpos : 0 < X := by nlinarith
    have hL : (a ^ 3)⁻¹ * a = (a ^ 2)⁻¹ := by
      rw [show a ^ 3 = a ^ 2 * a by ring, mul_inv]
      field_simp
    rw [hL]
    calc (a ^ 2)⁻¹ ≤ (X ^ 2 / 4)⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr (by nlinarith)
      _ = 4 * (X ^ 2)⁻¹ := by rw [div_eq_inv_mul, mul_inv, inv_inv]

end Work.LWP.BiotSavart
end
-- ===== merged: Submission.Work.LWP.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

/-! ## The ambient space -/

/-- `ℝ³`, i.e. `EuclideanSpace ℝ (Fin 3)`.  The challenge writes `local notation "ℝ³" => …`;
we expose it globally inside `Work.LWP` so that statements can be read without the notation. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## Initial data and the Lichtenstein–Gunther class -/

/-- The decay clause on the vorticity appearing in `theorem_1`: `‖ω x‖ ≤ C / (‖x‖^α + 1)`. -/
def VorticityDecay (α : ℝ≥0) (ω : R3 → R3) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖ω x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)

/-- **Lichtenstein–Gunther admissible initial data**: a divergence-free, odd vector field of class
`C^{1,α}(ℝ³)` whose vorticity decays as in the main theorem.  This is exactly the data class of
Elgindi's Theorem 1 (and of the classical Lichtenstein–Gunther local well-posedness theorem). -/
structure EulerData (α : ℝ≥0) (u₀ : R3 → R3) : Prop where
  /-- `u₀` is divergence-free. -/
  div_free : div u₀ = 0
  /-- `u₀` is odd in the sense of `FiniteTimeSingularity.IsOdd`. -/
  odd : IsOdd u₀
  /-- `u₀ ∈ C^{1,α}(ℝ³)`: `ContDiff 1`, bounded derivative, `α`-Hölder derivative. -/
  contDiffHolder : IsContDiffHolder ℝ α u₀
  /-- The vorticity decays like `‖x‖^{-α}` at infinity. -/
  vort_decay : VorticityDecay α (vorticity u₀)

/-- Joint `C^{1,α}` regularity in `(x,t)` of a spacetime field, on every strip `ℝ³ × [0,S]`
with `S < T` — the regularity clause of the main theorem. -/
def SpaceTimeHolder (α : ℝ≥0) (u : R3 → ℝ → R3) (T : ℝ) : Prop :=
  ∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 S)

/-- **The Lichtenstein–Gunther solution class** on `[0,T)`: a solution of the incompressible Euler
equation in the sense of `IsLocalEulerEquationSolution`, odd at every time, and jointly
`C^{1,α}` on compact time strips.  This is the class of solutions whose existence the classical
theory of Lichtenstein and Günther asserts, and the class in which the main theorem is stated. -/
structure LGClass (α : ℝ≥0) (u₀ : R3 → R3) (T : ℝ) (p : R3 → ℝ → ℝ)
    (u : R3 → ℝ → R3) : Prop where
  /-- `(p,u)` solves the incompressible Euler equation up to time `T` with data `u₀`. -/
  sol : IsLocalEulerEquationSolution p u₀ T u
  /-- The oddness of the data is propagated in time. -/
  odd : ∀ t ∈ Ico 0 T, IsOdd (u · t)
  /-- Joint `C^{1,α}` regularity on compact time strips. -/
  spacetime : SpaceTimeHolder α u T

/-- **Biot–Savart-compatible initial data**: the extra properties of the initial datum needed to
run the reconstruction `ω₀ ↦ u = biotSavart ω₀` of the Lichtenstein–Gunther argument on top of
the *analytically* given datum class `EulerData`.  They are: the vorticity is `L¹` (so that the
Newtonian-potential Biot–Savart integral converges), the vorticity is divergence-free (the
standing assumption the paper's Introduction makes when solving the vorticity equation), and the
velocity decays at infinity (so that it is recovered from its vorticity; both are automatic for
the compactly supported vorticity of the assembly's construction). -/
structure EulerDataBS (α : ℝ≥0) (u₀ : R3 → R3) : Prop where
  /-- the vorticity is integrable, so that `biotSavart (vorticity u₀)` converges -/
  vort_integrable : Integrable (vorticity u₀)
  /-- the vorticity is divergence-free -/
  vort_div_free : ∀ x : R3, div (vorticity u₀) x = 0
  /-- the vorticity is bounded -/
  vort_bounded : IsBoundedFun (vorticity u₀)
  /-- the vorticity is `α`-Hölder -/
  vort_holder : Holder α (vorticity u₀)
  /-- the velocity decays at infinity, so that the Biot–Savart law inverts `∇×` -/
  decay : ∃ C : ℝ, ∀ x : R3, ‖u₀ x‖ ≤ C / (1 + ‖x‖)

/-- `u'` extends `u` on `[0,T)`. -/
def ExtendsField (u u' : R3 → ℝ → R3) (T : ℝ) : Prop :=
  ∀ x t, t ∈ Ico 0 T → u' x t = u x t


/-! ## The Beale–Kato–Majda quantity -/

/-- The Beale–Kato–Majda quantity `∫₀ᵗ (⨆ₓ ‖ω(x,s)‖) ds` of the main theorem.  This is
*definitionally* the expression appearing in the challenge statement
`∫ s in 0..t, ⨆ x, ‖(∇×(u · s)) x‖`. -/
noncomputable def bkm (u : R3 → ℝ → R3) (t : ℝ) : ℝ :=
  ∫ s in 0..t, ⨆ x, ‖vorticity (u · s) x‖

/-- The `L∞`-in-space norm of the vorticity at time `t`, as a `sSup` (the integrand of `bkm`). -/
noncomputable def vortLInf (u : R3 → ℝ → R3) (t : ℝ) : ℝ := ⨆ x, ‖vorticity (u · t) x‖

/-! ## The vorticity formulation -/


/-- The 3D vorticity equation `∂ₜω + (u·∇)ω = (ω·∇)u`, written with the fixed definitions
`timeDeriv`, `directionalDeriv` of `ChallengeDeps`. -/
def VorticityEquation (u ω : R3 → ℝ → R3) : Prop :=
  ∀ x t, timeDeriv ω x t + directionalDeriv ω u x t = directionalDeriv u ω x t


/-! ## The reflection in the plane `x₃ = 0` -/

/-- The reflection of `ℝ³` in the plane `x₃ = 0`, i.e. `x ↦ (x₀, x₁, -x₃)`.  (This is
`Work.Cyl.reflZ`; it is repeated here so that `Work.LWP` is self-contained.) -/
def reflZ (x : R3) : R3 := WithLp.toLp 2 ![x 0, x 1, - x 2]

/-- The reflection of the *components* of a vector `v ↦ (v₀, v₁, -v₃)`.  (This is
`Work.Cyl.flipZ`.) -/
def flipZ (v : R3) : R3 := WithLp.toLp 2 ![v 0, v 1, - v 2]

/-- The parity class of the vorticity of an odd axisymmetric no-swirl velocity field: `ω` changes
sign under the reflection `reflZ` up to the component flip `flipZ`, i.e.
`ω (reflZ x) = - flipZ (ω x)`.  For `ω = ∇×u` this is equivalent to `u` being reflection-invariant
(hence, together with axisymmetry, `IsOdd`), by the identity
`curl (σ·v) = -σ·(curl v)` for a reflection `σ`. -/
def IsOddVorticity (ω : R3 → R3) : Prop := ∀ x, ω (reflZ x) = - flipZ (ω x)

/-! ## Biot–Savart -/

/-- The **Biot–Savart operator** on `ℝ³`, in the Newtonian-potential form obtained from
`u = ∇× (4π)^{-1}∫ ω(y)/‖x-y‖ dy`:

  `biotSavart ω x = (4π)^{-1} ∫ (ω y) ⨯₃ (x - y) / ‖x - y‖³ dy`.

Off the (measure-zero) diagonal the kernel is `(4π)^{-1} ω(y) × (x-y)/‖x-y‖³`, so that
`∇× (biotSavart ω) = ω` for divergence-free `ω` with sufficient decay — this is the Biot–Savart
law `u = (-Δ)^{-1}(∇×ω)` of the paper's Introduction. -/
noncomputable def biotSavart (ω : R3 → R3) (x : R3) : R3 :=
  (4 * Real.pi)⁻¹ • ∫ y : R3,
    WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ • ((ω y) ⨯₃ (x - y)))


/-! ## Flows -/





/-! ## Maximal solutions -/

/-- A **maximal Lichtenstein–Gunther solution** on `[0,T)`: a `C^{1,α}` solution on every
`[0,S]`, `S < T`, which cannot be extended past `T` as a solution of the same kind.  The
divergence of the BKM integral at `T` is *not* a field of this structure: it is a theorem
(`Work.LWP.bkm_divergence_of_maximal`) proved from the Beale–Kato–Majda continuation criterion.
This is the object the main theorem's conclusion is phrased in terms of (with `T = 1`). -/
structure MaximalSolution (α : ℝ≥0) (u₀ : R3 → R3) (T : ℝ) where
  /-- the maximal time is positive -/
  T_pos : 0 < T
  /-- the pressure -/
  p : R3 → ℝ → ℝ
  /-- the velocity -/
  u : R3 → ℝ → R3
  /-- the solution on `[0,T)`, in the challenge's predicate -/
  sol : IsLocalEulerEquationSolution p u₀ T u
  /-- the solution is odd at every time -/
  odd : ∀ t ∈ Ico 0 T, IsOdd (u · t)
  /-- joint `C^{1,α}` regularity on compact time strips -/
  spacetime : SpaceTimeHolder α u T
  /-- no solution of class `C^{1,α}` with the same data extends it past `T` -/
  maximal : ¬ ∃ T' : ℝ, T < T' ∧ ∃ p' : R3 → ℝ → ℝ, ∃ u' : R3 → ℝ → R3,
    IsLocalEulerEquationSolution p' u₀ T' u' ∧ ExtendsField u u' T

end Work.LWP
end
-- ===== merged: Submission.Work.RPFresh.integral_mul_sq_le_sq_mul_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped RealInnerProductSpace

namespace Work.RPFresh

/-- Cauchy–Schwarz (Bunyakovsky) inequality for the Lebesgue integral, exponent `2`:
for real functions `f`, `h` with `f²` and `h²` integrable,
`(∫ f h)² ≤ (∫ f²) * (∫ h²)`.

The proof passes to `Lp ℝ 2 μ`, an inner product space whose inner product is the integral
of the pointwise product, applies the abstract Cauchy–Schwarz
`real_inner_mul_inner_self_le`, and transports the four integrals back along the `MemLp.toLp`
a.e.-equalities.  The membership `MemLp f 2 μ` is obtained from the hypotheses through
`MeasureTheory.memLp_two_iff_integrable_sq`. -/
theorem integral_mul_sq_le_sq_mul_sq {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {f h : α → ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable f μ) (hhm : MeasureTheory.AEStronglyMeasurable h μ)
    (hfi : MeasureTheory.Integrable (fun x => f x ^ 2) μ)
    (hhi : MeasureTheory.Integrable (fun x => h x ^ 2) μ) :
    (∫ x, f x * h x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, h x ^ 2 ∂μ) := by
  have hf : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm).2 hfi
  have hh : MemLp h 2 μ := (memLp_two_iff_integrable_sq hhm).2 hhi
  have hB : (∫ x, f x * h x ∂μ) = ∫ x, (hf.toLp f) x * (hh.toLp h) x ∂μ :=
    integral_congr_ae (by
      filter_upwards [hf.coeFn_toLp, hh.coeFn_toLp] with x hx hy
      rw [hx, hy])
  have hA : (∫ x, f x ^ 2 ∂μ) = ∫ x, (hf.toLp f) x * (hf.toLp f) x ∂μ :=
    integral_congr_ae (by
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx, sq])
  have hC : (∫ x, h x ^ 2 ∂μ) = ∫ x, (hh.toLp h) x * (hh.toLp h) x ∂μ :=
    integral_congr_ae (by
      filter_upwards [hh.coeFn_toLp] with x hx
      rw [hx, sq])
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hh.toLp h)
  simp only [L2.inner_def, Real.inner_apply] at h
  rw [hB, hA, hC]
  simpa [sq] using h

end Work.RPFresh
end
-- ===== merged: Submission.Work.RemovLog.exists_lt_log_combination =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.RemovLog

/-- For `a < b` and `μ > 0`, taking `t` close enough to `b` from the left makes
`K + μ * log (b - t)` arbitrarily negative. -/
theorem exists_lt_log_combination {a b K μ M : ℝ} (hab : a < b) (hμ : 0 < μ) :
    ∃ t ∈ Set.Ioo a b, K + μ * Real.log (b - t) < M := by
  have hgap : 0 < b - a := by linarith
  have hexp : 0 < Real.exp ((M - K) / μ) := Real.exp_pos _
  have hle : min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2) < b - a :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hlt : min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2)
      < Real.exp ((M - K) / μ) :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hpos : 0 < min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2) :=
    lt_min (by linarith) (by linarith)
  refine ⟨b - min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2), ?_, ?_⟩
  · constructor
    · linarith
    · linarith
  · have hb : b - (b - min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2))
        = min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2) := by ring
    rw [hb]
    set δ := min ((b - a) / 2) (Real.exp ((M - K) / μ) / 2) with hδdef
    have hδpos : 0 < δ := hpos
    have hδexp : δ < Real.exp ((M - K) / μ) := hlt
    have hlog : Real.log δ < (M - K) / μ := by
      have h1 := Real.log_lt_log hδpos hδexp
      rwa [Real.log_exp] at h1
    have h4 : μ * ((M - K) / μ) = M - K := by field_simp
    have h3 := mul_lt_mul_of_pos_left hlog hμ
    linarith [h3, h4]

end Work.RemovLog
end
-- ===== merged: Submission.Work.RemovSign.exists_sign_mul_eq_abs_of_abs_lower_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.RemovSign

theorem exists_sign_mul_eq_abs_of_abs_lower_bound {T b θ μ : ℝ} (hTb : T < b)
    {Q : ℝ → ℝ} (hQ : ∀ x ∈ Set.Ioo T b, DifferentiableAt ℝ Q x)
    (hθ : θ ∈ Set.Ioo T b) (hμ : 0 < μ)
    (h : ∀ t ∈ Set.Ioo θ b, μ ≤ |Q t|) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ t ∈ Set.Ioo θ b, s * Q t = |Q t| := by
  -- `Q` is continuous on the open interval `(θ, b)` (indeed on `(T, b)`).
  have hcont : ContinuousOn Q (Set.Ioo θ b) := fun x hx =>
    (hQ x ⟨lt_trans hθ.1 hx.1, hx.2⟩).continuousAt.continuousWithinAt
  -- `Q` never vanishes on `(θ, b)`, since `|Q| ≥ μ > 0` there.
  have hne : ∀ t ∈ Set.Ioo θ b, Q t ≠ 0 := by
    intro t ht h0
    have ht' := h t ht
    rw [h0, abs_zero] at ht'
    linarith
  -- Pick a base point of `(θ, b)`.
  obtain ⟨θ', hθ'⟩ := Set.nonempty_Ioo.mpr hθ.2
  -- Intermediate value theorem on the closed interval spanned by two points of `(θ, b)`.
  have hwit : ∀ x ∈ Set.Ioo θ b, ∀ y ∈ Set.Ioo θ b,
      Set.uIcc (Q x) (Q y) ⊆ Q '' Set.uIcc x y := fun x hx y hy =>
    intermediate_value_uIcc
      (hcont.mono (Set.OrdConnected.uIcc_subset Set.ordConnected_Ioo hx hy))
  -- Consequently `0` is never between `Q x` and `Q y` for `x, y ∈ (θ, b)`.
  have hzero : ∀ x ∈ Set.Ioo θ b, ∀ y ∈ Set.Ioo θ b, 0 ∈ Set.uIcc (Q x) (Q y) → False := by
    intro x hx y hy h0
    obtain ⟨z, hz, hzQ⟩ := hwit x hx y hy h0
    have hzI : z ∈ Set.Ioo θ b :=
      Set.OrdConnected.uIcc_subset Set.ordConnected_Ioo hx hy hz
    have hz' := h z hzI
    rw [hzQ, abs_zero] at hz'
    linarith
  rcases lt_or_gt_of_ne (hne θ' hθ').symm with hpos | hneg
  · -- `Q θ' > 0`: then `Q > 0` on all of `(θ, b)`, so `s = 1` works.
    refine ⟨1, Or.inl rfl, ?_⟩
    intro t ht
    have h0 : 0 ≤ Q t := by
      by_contra hlt
      push Not at hlt
      exact hzero θ' hθ' t ht
        (by rw [Set.mem_uIcc]; exact Or.inr ⟨le_of_lt hlt, le_of_lt hpos⟩)
    rw [one_mul, abs_of_nonneg h0]
  · -- `Q θ' < 0`: then `Q < 0` on all of `(θ, b)`, so `s = -1` works.
    refine ⟨-1, Or.inr rfl, ?_⟩
    intro t ht
    have h0 : Q t ≤ 0 := by
      by_contra hlt
      push Not at hlt
      exact hzero θ' hθ' t ht
        (by rw [Set.mem_uIcc]; exact Or.inl ⟨le_of_lt hneg, le_of_lt hlt⟩)
    rw [neg_one_mul, abs_of_nonpos h0]

end Work.RemovSign
end
-- ===== merged: Submission.Work.SolutionDelivery.Scaling.rpow_scaling_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Scaling


end Work.SolutionDelivery.Scaling
end
-- ===== merged: Submission.Work.SolutionDelivery.Sup.bddAbove_range_ciSup_mem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Sup

theorem bddAbove_range_ciSup_mem {K : Set (EuclideanSpace ℝ (Fin 3))} (hKc : IsCompact K)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : ContinuousOn g K) :
    BddAbove (Set.range (fun x => ⨆ (_ : x ∈ K), g x)) := by
  refine BddAbove.mono (t := (g '' K) ∪ {sSup (∅ : Set ℝ)}) ?_ ?_
  · rintro y ⟨x, rfl⟩
    by_cases hx : x ∈ K
    · exact Or.inl ⟨x, hx, (ciSup_pos (f := fun _ : x ∈ K => g x) hx).symm⟩
    · refine Or.inr ?_
      rw [Set.mem_singleton_iff]
      exact ciSup_neg (f := fun _ : x ∈ K => g x) hx
  · exact BddAbove.union (hKc.bddAbove_image hg) bddAbove_singleton

end Work.SolutionDelivery.Sup
end
-- ===== merged: Submission.Work.SolutionDelivery.Sup.exists_notMem_closedBall_R3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Sup

/-- In a nontrivial normed space every closed ball is a proper subset: for any radius `R`
there is a vector whose distance from the origin exceeds `R`. -/
theorem exists_notMem_closedBall_R3 (R : ℝ) :
    ∃ x : EuclideanSpace ℝ (Fin 3), x ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R := by
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ (EuclideanSpace ℝ (Fin 3)) R
  refine ⟨x, ?_⟩
  intro h
  have hle : ‖x‖ ≤ R := by
    simpa using Metric.mem_closedBall.mp h
  exact absurd hle (not_le.mpr hx)

end Work.SolutionDelivery.Sup
end
-- ===== merged: Submission.Work.Spaces.abs_binom_double_sum_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

theorem abs_binom_double_sum_le (k j : ℕ) (x y : ℕ → ℕ → ℝ) :
    |∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (k + 1),
        (j.choose a : ℝ) * (k.choose c : ℝ) * (x a c * y a c)| ≤
      (1 + ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (k + 1),
        (j.choose a : ℝ) * (k.choose c : ℝ)) *
        ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1), |x a c| * |y a c| := by
  set sA : Finset ℕ := Finset.range (j + 1) with hsA
  set sC : Finset ℕ := Finset.range (k + 1) with hsC
  set S : ℝ := ∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) with hS
  set T : ℝ := ∑ c ∈ sC, ∑ a ∈ sA, |x a c| * |y a c| with hT
  have hBnn : ∀ a c, (0 : ℝ) ≤ (j.choose a : ℝ) * (k.choose c : ℝ) :=
    fun a c => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hznn : ∀ a c, (0 : ℝ) ≤ |x a c| * |y a c| :=
    fun a c => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  -- Step 1: triangle inequality, and `|B * (x*y)| = B * |x| * |y|` since `B ≥ 0`.
  have step1 :
      |∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (x a c * y a c)|
      ≤ ∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (|x a c| * |y a c|) := by
    calc
      |∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (x a c * y a c)|
          ≤ ∑ a ∈ sA, |∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (x a c * y a c)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ sA, ∑ c ∈ sC, |(j.choose a : ℝ) * (k.choose c : ℝ) * (x a c * y a c)| :=
            Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (|x a c| * |y a c|) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro c _
            rw [abs_mul, abs_of_nonneg (hBnn a c), abs_mul]
  -- Each `B a c` is bounded by the full double sum `S`.
  have hB_le : ∀ a ∈ sA, ∀ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) ≤ 1 + S := by
    intro a ha c hc
    have h2 : (j.choose a : ℝ) * (k.choose c : ℝ)
        ≤ ∑ c' ∈ sC, (j.choose a : ℝ) * (k.choose c' : ℝ) :=
      Finset.single_le_sum (fun c' _ => hBnn a c') hc
    have h1 : (∑ c' ∈ sC, (j.choose a : ℝ) * (k.choose c' : ℝ)) ≤ S := by
      rw [hS]
      exact Finset.single_le_sum (fun a' _ => Finset.sum_nonneg (fun c' _ => hBnn a' c')) ha
    have hBS : (j.choose a : ℝ) * (k.choose c : ℝ) ≤ S := h2.trans h1
    linarith
  -- Step 2: bound termwise by `(1+S) * z`, then factor `(1+S)` out.
  have step2 :
      (∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (|x a c| * |y a c|))
      ≤ (1 + S) * T := by
    have hstep : ∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (|x a c| * |y a c|)
        ≤ ∑ a ∈ sA, ∑ c ∈ sC, (1 + S) * (|x a c| * |y a c|) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_right (hB_le a ha c hc) (hznn a c)
    refine hstep.trans (le_of_eq ?_)
    have heq : (∑ a ∈ sA, ∑ c ∈ sC, (1 + S) * (|x a c| * |y a c|)) = (1 + S) * T := by
      rw [hT, Finset.sum_comm (s := sA) (t := sC)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
    exact heq
  exact step1.trans step2

end Work.Spaces
end
-- ===== merged: Submission.Work.Stability.min_mul_le_max_mul_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

theorem min_mul_le_max_mul_rpow {K M d : ℝ} {α : NNReal} (hK : 0 ≤ K) (hM : 0 ≤ M) (hd : 0 ≤ d) (hα : α ≤ 1) : min (K * d) (2 * M) ≤ max K (2 * M) * d ^ (α : ℝ) := by
  have hα0 : (0 : ℝ) ≤ (α : ℝ) := by positivity
  have hα1 : (α : ℝ) ≤ 1 := by exact_mod_cast hα
  have hmax : 0 ≤ max K (2 * M) := le_trans hK (le_max_left _ _)
  rcases eq_or_lt_of_le hd with hd0 | hdpos
  · -- d = 0
    rw [← hd0]
    have hnonneg : 0 ≤ max K (2 * M) * (0 : ℝ) ^ (α : ℝ) :=
      mul_nonneg (le_trans hK (le_max_left _ _)) (Real.rpow_nonneg (le_refl 0) _)
    calc min (K * 0) (2 * M) ≤ K * 0 := min_le_left _ _
      _ = 0 := by ring
      _ ≤ max K (2 * M) * (0 : ℝ) ^ (α : ℝ) := hnonneg
  · rcases lt_or_ge 1 d with hlt | hdle
    · -- 1 < d, use the `2 * M` branch
      have hd1 : 1 ≤ d := le_of_lt hlt
      have hpow : 1 ≤ d ^ (α : ℝ) := Real.one_le_rpow hd1 hα0
      calc min (K * d) (2 * M) ≤ 2 * M := min_le_right _ _
        _ = (2 * M) * 1 := by ring
        _ ≤ max K (2 * M) * d ^ (α : ℝ) :=
            mul_le_mul (le_max_right _ _) hpow (by norm_num) hmax
    · -- d ≤ 1, use the `K * d` branch and d ≤ d^α
      have hpow : d ≤ d ^ (α : ℝ) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hdpos hdle hα1
        simpa using h
      have hpow0 : 0 ≤ d ^ (α : ℝ) := Real.rpow_nonneg hd _
      calc min (K * d) (2 * M) ≤ K * d := min_le_left _ _
        _ ≤ K * d ^ (α : ℝ) := mul_le_mul_of_nonneg_left hpow hK
        _ ≤ max K (2 * M) * d ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0

end Work.Stability
end
-- ===== merged: Submission.Work.Stability.mul_rpow_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- Auxiliary comparison: if `0 ≤ p ≤ 2`, `0 ≤ t` and `p * t ≤ 2`, then `p * t ^ α ≤ 2`
whenever `0 < α ≤ 1`.

Proof: if `t ≤ 1` then `t ^ α ≤ 1` and hence `p * t ^ α ≤ p ≤ 2`; if `1 ≤ t` then
`t ^ α ≤ t` (since `α ≤ 1` and `t ^ 1 = t`), so `p * t ^ α ≤ p * t ≤ 2`. -/
theorem mul_rpow_le_aux_of_mul_le {p t α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hB : p ≤ 2) (hpt : p * t ≤ 2) : p * t ^ α ≤ 2 := by
  rcases le_total t 1 with ht1 | ht1
  · have h1 : t ^ α ≤ 1 := Real.rpow_le_one ht ht1 hα.le
    calc p * t ^ α ≤ p * 1 := mul_le_mul_of_nonneg_left h1 hp
      _ = p := mul_one p
      _ ≤ 2 := hB
  · have h1 : t ^ α ≤ t := by
      calc t ^ α ≤ t ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 hα1
        _ = t := Real.rpow_one t
    calc p * t ^ α ≤ p * t := mul_le_mul_of_nonneg_left h1 hp
      _ ≤ 2 := hpt

theorem mul_rpow_le {p ρ d α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 ≤ ρ) (hd : 0 ≤ d)
    (hp : 0 ≤ p) (hA : p * ρ ≤ 2 * d) (hB : p ≤ 2) : p * ρ ^ α ≤ 2 * d ^ α := by
  rcases eq_or_lt_of_le hd with hd0 | hdpos
  · -- `d = 0`: the constraint `p * ρ ≤ 0` forces `p = 0` or `ρ = 0`, so both sides vanish
    subst hd0
    rw [Real.zero_rpow hα.ne', mul_zero]
    have hpρ : p * ρ = 0 := le_antisymm (by linarith [hA]) (mul_nonneg hp hρ)
    rcases mul_eq_zero.mp hpρ with h | h
    · simp [h]
    · simp [h, Real.zero_rpow hα.ne']
  · -- `d > 0`: set `t = ρ / d`, so that `p * t ≤ 2` and `ρ = t * d`
    set t : ℝ := ρ / d with htdef
    have ht : 0 ≤ t := div_nonneg hρ hdpos.le
    have htd : t * d = ρ := by rw [htdef]; exact div_mul_cancel₀ ρ hdpos.ne'
    have hpt : p * t ≤ 2 := by
      have h1 : p * t = p * ρ / d := by rw [htdef]; exact (mul_div_assoc p ρ d).symm
      rw [h1, div_le_iff₀ hdpos]
      linarith [hA]
    have hkey : p * t ^ α ≤ 2 :=
      mul_rpow_le_aux_of_mul_le hα hα1 hp ht hB hpt
    calc p * ρ ^ α = p * (t * d) ^ α := by rw [htd]
      _ = p * (t ^ α * d ^ α) := by rw [Real.mul_rpow ht hd]
      _ = (p * t ^ α) * d ^ α := by ring
      _ ≤ 2 * d ^ α := mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hd α)

end Work.Stability
end
