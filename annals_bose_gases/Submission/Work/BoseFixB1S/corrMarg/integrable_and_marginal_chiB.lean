import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.corrMarg.support_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `u`-marginal of `χ_{B(u)}² w²` (conjuncts 3 and 4 of `corrMarginal`)

`Work.BoseFixB1S.integrable_and_marginal_chiB` is the analytic content of the
`u`-marginal (in the `χ_{B(u)}²`-weighted sense) of the sliding localisation:

* `u ↦ ∫_z χ_{B(u)}(z)² w(z)²` is integrable, and
* `∫_u ∫_z χ_{B(u)}(z)² w(z)² = ∫_z χ_ℓ(z)² w(z)²`,

for `0 < ℓ`, `0 < d` and *continuous* `w`.  The per-`z` identity
`∫_u χ_{B(u)}(z)² du = χ_ℓ(z)²` is `Submission.BoseGases.chiB_partition_u`; the
`u`-marginal is finite because the joint integrand is supported in the fixed cube
`acube ℓ × acube ((1+d)/d)` (`corrMarg.support_u`) and bounded there.

The proof is the template of
`Submission/Work/SmallBoxSliding/boxMass_integral_u.lean`: a one-shot Tonelli
computation in `ℝ≥0∞` (`lintegral_lintegral_swap` + `lintegral_prod`) which
identifies the double `lintegral` with `ofReal (∫_z χ_ℓ(z)² w(z)²) < ⊤`; this
gives joint integrability of `(u,z) ↦ χ_{B(u)}(z)² w(z)²`, whence the `u`-marginal
integrability (`Integrable.integral_prod_left`) and the exchange of the two
Bochner integrals (`integral_integral_swap`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- Joint continuity of `(u,z) ↦ χ_{B(u)}(z) = χ(z/ℓ)·χ(z/(ℓd) − u)`. -/
lemma continuous_uncurry_chiB (ℓ d : ℝ) :
    Continuous (Function.uncurry (chiB ℓ d)) := by
  have h1 : Continuous (fun p : ℝ³ × ℝ³ => chiScale ℓ p.2) :=
    (chiScale_continuous ℓ).comp continuous_snd
  have h2 : Continuous (fun p : ℝ³ × ℝ³ => chiScale (ℓ * d) (p.2 - (ℓ * d) • p.1)) :=
    (chiScale_continuous (ℓ * d)).comp
      (continuous_snd.sub
        ((continuous_const : Continuous (fun _ : ℝ³ × ℝ³ => (ℓ * d))).smul continuous_fst))
  show Continuous (fun p : ℝ³ × ℝ³ => chiScale ℓ p.2 * chiScale (ℓ * d) (p.2 - (ℓ * d) • p.1))
  exact h1.mul h2

theorem integrable_and_marginal_chiB {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {w : ℝ³ → ℝ} (hw : Continuous w) :
    Integrable (fun u : ℝ³ => ∫ z : ℝ³, (chiB ℓ d u z) ^ 2 * (w z) ^ 2)
      ∧ (∫ u : ℝ³, ∫ z : ℝ³, (chiB ℓ d u z) ^ 2 * (w z) ^ 2)
          = ∫ z : ℝ³, (chiScale ℓ z) ^ 2 * (w z) ^ 2 := by
  -- ## The joint integrand, its continuity and its nonnegativity
  have hFcont : Continuous (fun p : ℝ³ × ℝ³ => chiB ℓ d p.1 p.2 ^ 2 * w p.2 ^ 2) :=
    ((continuous_uncurry_chiB ℓ d).pow 2).mul ((hw.comp continuous_snd).pow 2)
  have hFnn : ∀ p : ℝ³ × ℝ³, 0 ≤ chiB ℓ d p.1 p.2 ^ 2 * w p.2 ^ 2 := fun p =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- ## Integrability of the two `χ`-factors, and the per-`z` marginal identity
  have hInnerInt : ∀ z : ℝ³, Integrable (fun u : ℝ³ => chiB ℓ d u z ^ 2) := by
    intro z
    have hcont : Continuous (fun u : ℝ³ => chiB ℓ d u z ^ 2) :=
      (((continuous_uncurry_chiB ℓ d).comp
        (continuous_id.prodMk continuous_const)).pow 2)
    have hsub : Function.support (fun u : ℝ³ => chiB ℓ d u z ^ 2)
        ⊆ acube ((1 + d) / d) := by
      intro u hu
      by_contra hmem
      refine hu ?_
      show chiB ℓ d u z ^ 2 = 0
      rw [chiB_eq_zero_of_not_mem_acube_u hℓ hd hmem z]
      ring
    have h1d : 0 < (1 + d) / d := div_pos (by linarith) hd
    exact hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (acube_compact h1d) hsub)
  have hperz : ∀ z : ℝ³,
      (∫ u : ℝ³, chiB ℓ d u z ^ 2 * w z ^ 2) = (chiScale ℓ z) ^ 2 * (w z) ^ 2 := by
    intro z
    have hpt : (fun u : ℝ³ => chiB ℓ d u z ^ 2 * w z ^ 2)
        = fun u : ℝ³ => (w z) ^ 2 * (chiB ℓ d u z ^ 2) := by
      funext u; ring
    rw [hpt, integral_const_mul, chiB_partition_u hℓ hd z]
    ring
  -- ## Integrability of the `χ_ℓ²w²`-marginal
  have hOuterInt : Integrable (fun z : ℝ³ => (chiScale ℓ z) ^ 2 * (w z) ^ 2) := by
    have hsub : Function.support (fun z : ℝ³ => (chiScale ℓ z) ^ 2 * (w z) ^ 2) ⊆ acube ℓ := by
      intro z hz
      by_contra hmem
      refine hz ?_
      show chiScale ℓ z ^ 2 * w z ^ 2 = 0
      have hz0 : chiScale ℓ z = 0 := by
        by_contra h
        exact hmem (chiScale_mem_acube hℓ h)
      rw [hz0]
      ring
    exact (((chiScale_continuous ℓ).pow 2).mul (hw.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (acube_compact hℓ) hsub)
  -- ## The `ℝ≥0∞`-identity for the per-`z` marginal
  have hzlin : (∫⁻ z : ℝ³, ∫⁻ u : ℝ³,
        ENNReal.ofReal (chiB ℓ d u z ^ 2 * w z ^ 2))
      = ENNReal.ofReal (∫ z : ℝ³, (chiScale ℓ z) ^ 2 * (w z) ^ 2) := by
    have hper : ∀ z : ℝ³, (∫⁻ u : ℝ³, ENNReal.ofReal (chiB ℓ d u z ^ 2 * w z ^ 2))
        = ENNReal.ofReal ((chiScale ℓ z) ^ 2 * (w z) ^ 2) := by
      intro z
      have h1 : (∫⁻ u : ℝ³, ENNReal.ofReal (chiB ℓ d u z ^ 2 * w z ^ 2))
          = ENNReal.ofReal (w z ^ 2) * ∫⁻ u : ℝ³, ENNReal.ofReal (chiB ℓ d u z ^ 2) := by
        rw [show (fun u : ℝ³ => ENNReal.ofReal (chiB ℓ d u z ^ 2 * w z ^ 2))
              = fun u : ℝ³ => ENNReal.ofReal (w z ^ 2) * ENNReal.ofReal (chiB ℓ d u z ^ 2) from
            funext (fun u => by rw [ENNReal.ofReal_mul (sq_nonneg _), mul_comm])]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [h1,
        ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hInnerInt z)
          (Eventually.of_forall (fun u => sq_nonneg _)),
        chiB_partition_u hℓ hd z]
      rw [ENNReal.ofReal_mul (sq_nonneg (chiScale ℓ z)), mul_comm]
    rw [show (∫⁻ z : ℝ³, ∫⁻ u : ℝ³, ENNReal.ofReal (chiB ℓ d u z ^ 2 * w z ^ 2))
          = ∫⁻ z : ℝ³, ENNReal.ofReal ((chiScale ℓ z) ^ 2 * (w z) ^ 2) from
        lintegral_congr hper]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hOuterInt
      (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))).symm
  -- ## Joint integrability, by Tonelli
  have hjoint_int : Integrable
      (Function.uncurry (fun u z : ℝ³ => chiB ℓ d u z ^ 2 * w z ^ 2))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    refine ⟨hFcont.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hae : AEMeasurable (fun p : ℝ³ × ℝ³ =>
        ENNReal.ofReal (chiB ℓ d p.1 p.2 ^ 2 * w p.2 ^ 2))
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
      (ENNReal.continuous_ofReal.comp hFcont).aemeasurable
    have heq : (∫⁻ p : ℝ³ × ℝ³,
          ENNReal.ofReal ‖Function.uncurry (fun u z : ℝ³ => chiB ℓ d u z ^ 2 * w z ^ 2) p‖
          ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)))
        = (∫⁻ p : ℝ³ × ℝ³,
          ENNReal.ofReal (chiB ℓ d p.1 p.2 ^ 2 * w p.2 ^ 2)
          ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³))) := by
      refine lintegral_congr (fun p => ?_)
      have h1 : Function.uncurry (fun u z : ℝ³ => chiB ℓ d u z ^ 2 * w z ^ 2) p
          = chiB ℓ d p.1 p.2 ^ 2 * w p.2 ^ 2 := rfl
      rw [h1, Real.norm_eq_abs,
        abs_of_nonneg (show (0 : ℝ) ≤ chiB ℓ d p.1 p.2 ^ 2 * w p.2 ^ 2 from
          mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    have hprod : (∫⁻ p : ℝ³ × ℝ³,
          ENNReal.ofReal (chiB ℓ d p.1 p.2 ^ 2 * w p.2 ^ 2)
          ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)))
        = (∫⁻ u : ℝ³, ∫⁻ z : ℝ³,
            ENNReal.ofReal (chiB ℓ d u z ^ 2 * w z ^ 2)) :=
      lintegral_prod (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))
        (f := fun p : ℝ³ × ℝ³ => ENNReal.ofReal (chiB ℓ d p.1 p.2 ^ 2 * w p.2 ^ 2)) hae
    have hswap : (∫⁻ u : ℝ³, ∫⁻ z : ℝ³,
          ENNReal.ofReal (chiB ℓ d u z ^ 2 * w z ^ 2))
        = (∫⁻ z : ℝ³, ∫⁻ u : ℝ³,
            ENNReal.ofReal (chiB ℓ d u z ^ 2 * w z ^ 2)) :=
      lintegral_lintegral_swap (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))
        (f := fun u z : ℝ³ => ENNReal.ofReal (chiB ℓ d u z ^ 2 * w z ^ 2)) hae
    rw [heq, hprod, hswap, hzlin]
    exact ENNReal.ofReal_lt_top
  refine ⟨?_, ?_⟩
  · exact hjoint_int.integral_prod_left
  · rw [integral_integral_swap hjoint_int]
    exact integral_congr_ae (Eventually.of_forall hperz)

end Work.BoseFixB1S
