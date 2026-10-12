import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseRowsL.Row2.heatFubini
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Row2.heatB_integrable`

The **integrability of the heat row** `hB`.  For a function `f : ℝ³ → ℝ` whose
`p ↦ f p / (2‖p‖²)` is integrable (this is the hypothesis that makes the `B`-side of the
subordination bookkeeping finite), the heat marginal

    t ↦ ((2π)³)⁻¹ ∫ p, f p · e^{−t‖p‖²}

is integrable on `(0, ∞)`.

This is the well-posedness companion of `Work.BoseRowsL.Row2.heatFubini`, which identifies
`∫ p, f p/(2‖p‖²)` with `½ ∫_{t>0} ∫ p, f p e^{−t‖p‖²}`: the right-hand side there is an honest
Bochner integral only if the marginal is `L¹` in `t`, which is what this file supplies.

## Why the exact Tonelli computation, and not a domination

Note that **no separable majorant can work**: `∫_{t>0} e^{−t‖p‖²} dt = ‖p‖⁻²` is finite only
through the *cancellation* of the `p`- and `t`-integrals.  A majorant `‖f p‖ e^{−t‖p‖²} ≤
H(p)K(t)` would need `K(t) ≳ 1` for small `‖p‖` (where `e^{−t‖p‖²} ≈ 1`), whence
`∫_{t>0} K = ∞`; and the naive pointwise bound `‖∫ p, …‖ ≤ 2K/t` (splitting the `p`-integral at
`‖p‖ = t^{−1/2}` and using `e^{−x} ≤ x⁻¹` on the outer piece) is **not** integrable at `t = 0`
either — the marginal itself is not `O(1)` as `t → 0⁺`.  Hence the only route is the exact
computation of the joint integral, exactly as in `heatFubini_aux`:

* `integrable_heatB_joint` — the joint function `(p,t) ↦ f p · e^{−t‖p‖²}` is `L¹` on
  `volume.prod (volume.restrict (Ioi 0))` (Tonelli: the inner `t`-integral is `‖f p‖/‖p‖²` for
  `p ≠ 0`, and `{0}` is a null set);
* the marginal follows from the symmetry of the product measure (`Integrable.swap`) and
  `MeasureTheory.Integrable.integral_prod_left`.

All helper lemmas used below (`enorm_eq_ofReal_norm_real`, `lintegral_exp_neg_mul_Ioi`,
`two_mul_div_two`) are the proved ones of `heatFubini.lean`, in this same namespace.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace Work.BoseRowsL.Row2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Joint integrability of the heat kernel.**  If `p ↦ f p / (2‖p‖²) ∈ L¹`, then
`(p,t) ↦ f p · e^{−t‖p‖²}` is integrable for the product measure
`volume.prod (volume.restrict (Ioi 0))`.

This is the Tonelli finiteness underlying both the subordination identity `heatFubini` and the
`t`-integrability of the heat marginal: the inner `t`-integral equals `‖f p‖ / ‖p‖²` for
`p ≠ 0`, and `{p : ‖p‖ = 0}` is `volume`-null. -/
lemma integrable_heatB_joint {f : ℝ³ → ℝ}
    (hInt : Integrable (fun p : ℝ³ => f p / (2 * ‖p‖ ^ 2))) :
    Integrable (fun z : ℝ³ × ℝ => f z.1 * Real.exp (-(z.2 * ‖z.1‖ ^ 2)))
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  -- the set `{p : ‖p‖ = 0}` is null
  have hnull : volume {p : ℝ³ | (2 : ℝ) * ‖p‖ ^ 2 = 0} = 0 := by
    have hset : {p : ℝ³ | (2 : ℝ) * ‖p‖ ^ 2 = 0} = {0} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hp
        have h2 : ‖p‖ ^ 2 = 0 := by
          rcases mul_eq_zero.mp hp with h | h
          · exact absurd h (by norm_num)
          · exact h
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp h2)
      · rintro rfl
        simp
    rw [hset, measure_singleton]
  have hne : ∀ᵐ p ∂(volume : Measure ℝ³), (2 : ℝ) * ‖p‖ ^ 2 ≠ 0 := by
    have hcompl : {p : ℝ³ | ¬ ((2 : ℝ) * ‖p‖ ^ 2 ≠ 0)} = {p : ℝ³ | (2 : ℝ) * ‖p‖ ^ 2 = 0} := by
      ext p
      simp
    rw [ae_iff, hcompl]
    exact hnull
  have hne_norm : ∀ᵐ p ∂(volume : Measure ℝ³), ‖p‖ ≠ 0 := by
    filter_upwards [hne] with p hp h0
    exact hp (by rw [h0]; norm_num)
  -- strong measurability of `f`, from the integrability hypothesis
  have hf_aesm : AEStronglyMeasurable f volume := by
    have hae : f =ᵐ[volume] (fun p : ℝ³ => (f p / (2 * ‖p‖ ^ 2)) * (2 * ‖p‖ ^ 2)) := by
      filter_upwards [hne] with p hp
      exact (div_mul_cancel₀ (f p) hp).symm
    have hprod : AEStronglyMeasurable
        (fun p : ℝ³ => (f p / (2 * ‖p‖ ^ 2)) * (2 * ‖p‖ ^ 2)) volume :=
      hInt.aestronglyMeasurable.mul
        ((continuous_const.mul (continuous_norm.pow 2)).aestronglyMeasurable)
    exact hprod.congr hae.symm
  -- the joint integrand on `ℝ³ × (0,∞)`
  set F : ℝ³ × ℝ → ℝ := fun z => f z.1 * Real.exp (-(z.2 * ‖z.1‖ ^ 2)) with hFdef
  have hF_aesm : AEStronglyMeasurable F (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    rw [hFdef]
    have hcont : Continuous (fun z : ℝ³ × ℝ => Real.exp (-(z.2 * ‖z.1‖ ^ 2))) := by
      have h1 : Continuous (fun z : ℝ³ × ℝ => ‖z.1‖) := continuous_norm.comp continuous_fst
      have h2 : Continuous (fun z : ℝ³ × ℝ => ‖z.1‖ ^ 2) := h1.pow 2
      have h3 : Continuous (fun z : ℝ³ × ℝ => z.2 * ‖z.1‖ ^ 2) := continuous_snd.mul h2
      have h4 : Continuous (fun z : ℝ³ × ℝ => -(z.2 * ‖z.1‖ ^ 2)) := h3.neg
      exact Real.continuous_exp.comp h4
    exact hf_aesm.comp_fst.mul hcont.aestronglyMeasurable
  have hF_enorm : AEMeasurable (fun z : ℝ³ × ℝ => ‖F z‖ₑ)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := hF_aesm.enorm
  -- the inner `t`-integral, for a.e. `p`
  have hinner : ∀ᵐ p ∂(volume : Measure ℝ³),
      (∫⁻ t : ℝ, ‖F (p, t)‖ₑ ∂(volume.restrict (Set.Ioi (0 : ℝ))))
        = ENNReal.ofReal (‖f p‖ / ‖p‖ ^ 2) := by
    filter_upwards [hne_norm] with p hp
    have hc : (0 : ℝ) < ‖p‖ ^ 2 := sq_pos_of_ne_zero hp
    have hpt : ∀ t : ℝ, ‖F (p, t)‖ₑ
        = ENNReal.ofReal ‖f p‖ * ENNReal.ofReal (Real.exp (-(t * ‖p‖ ^ 2))) := by
      intro t
      change ‖f p * Real.exp (-(t * ‖p‖ ^ 2))‖ₑ = _
      rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal (Real.exp_pos _).le]
      congr 1
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_exp_neg_mul_Ioi _ hc, ← ENNReal.ofReal_mul (norm_nonneg (f p))]
    congr 1
  have hA_lt : (∫⁻ p : ℝ³, ENNReal.ofReal ‖f p / (2 * ‖p‖ ^ 2)‖) < ⊤ :=
    (hasFiniteIntegral_iff_norm (fun p : ℝ³ => f p / (2 * ‖p‖ ^ 2))).mp hInt.hasFiniteIntegral
  -- the joint `lintegral` is finite
  have hlin : (∫⁻ z : ℝ³ × ℝ, ‖F z‖ₑ ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
      = ENNReal.ofReal 2 * ∫⁻ p : ℝ³, ENNReal.ofReal ‖f p / (2 * ‖p‖ ^ 2)‖ := by
    rw [lintegral_prod _ hF_enorm, lintegral_congr_ae hinner,
      ← lintegral_const_mul' (ENNReal.ofReal 2) _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun p => ?_)
    have hden : ‖(2 : ℝ) * ‖p‖ ^ 2‖ = 2 * ‖p‖ ^ 2 := by
      rw [Real.norm_of_nonneg (by positivity)]
    have hnorm : ‖f p / (2 * ‖p‖ ^ 2)‖ = ‖f p‖ / (2 * ‖p‖ ^ 2) := by rw [norm_div, hden]
    rw [hnorm, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), two_mul_div_two]
  have hF_fin : HasFiniteIntegral F (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    rw [hasFiniteIntegral_iff_norm]
    have hlow : (∫⁻ z : ℝ³ × ℝ,
          ENNReal.ofReal ‖F z‖ ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
        = ∫⁻ z : ℝ³ × ℝ, ‖F z‖ₑ ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
      lintegral_congr (fun z => (enorm_eq_ofReal_norm_real (F z)).symm)
    rw [hlow, hlin]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA_lt
  exact ⟨hF_aesm, hF_fin⟩

/-- **The heat marginal is `L¹`.**  For `f/(2‖p‖²) ∈ L¹(ℝ³)`, the function
`t ↦ ∫ p, f p · e^{−t‖p‖²}` is integrable on `(0, ∞)`.

This is `integrable_heatB_joint` transported to the `(t,p)` orientation (the product measure is
symmetric) and then integrated out in `p` (`Integrable.integral_prod_left`). -/
lemma integrable_heatB_marginal {f : ℝ³ → ℝ}
    (hInt : Integrable (fun p : ℝ³ => f p / (2 * ‖p‖ ^ 2))) :
    Integrable (fun t : ℝ => ∫ p : ℝ³, f p * Real.exp (-(t * ‖p‖ ^ 2)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hjoint : Integrable (fun z : ℝ³ × ℝ => f z.1 * Real.exp (-(z.2 * ‖z.1‖ ^ 2)))
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := integrable_heatB_joint hInt
  have hswap := hjoint.swap
  simpa [Function.comp] using hswap.integral_prod_left

theorem heatB_integrable {h : ℝ³ → ℝ}
    (hInt : MeasureTheory.Integrable (fun p : ℝ³ => Work.BoseFixR.chat h p / (2 * ‖p‖ ^ 2))) :
    MeasureTheory.Integrable (fun t : ℝ => ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
        Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2)))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have h := integrable_heatB_marginal (f := Work.BoseFixR.chat h) hInt
  simpa using h.const_mul ((2 * Real.pi) ^ 3)⁻¹

end Work.BoseRowsL.Row2
