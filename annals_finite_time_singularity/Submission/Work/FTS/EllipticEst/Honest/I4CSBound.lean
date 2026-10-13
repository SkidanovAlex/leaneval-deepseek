import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.Honest.I4SliceDefs
import Submission.Work.FTS.EllipticEst.AngSecond.slice_sq_integral_mul_le
import Submission.Work.FTS.EllipticEst.Honest.csIntegralSqrt
import Submission.Work.FTS.EllipticEst.Honest.sqrtWeightFacts
import Submission.Work.FTS.EllipticEst.Honest.integrableOn_abs_mul_sigma

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
