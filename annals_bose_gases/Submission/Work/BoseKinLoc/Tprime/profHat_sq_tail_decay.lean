import Mathlib.Tactic.Have
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Tprime.profHat_sq_tail_decay`

The squared bump profile `p ↦ profHat(p)²` has a polynomially decaying tail:

    `∃ K ≥ 0, ∀ r ≥ 1, ∫_{‖p‖ > r} profHat(p)² dp ≤ K / r^6`.

## Proof

`Work.OneBodyKin.ProfHatDecay` gives `|profHat p| ≤ C/(1+‖p‖)^6`, hence
`profHat(p)² ≤ C² (1+‖p‖)^{-12}`.  Multiplying by `(1+‖p‖)^6` makes this the *integrable*
weighted profile

    `g(p) := profHat(p)² (1+‖p‖)^6 ≤ C² (1+‖p‖)^{-6}`,

and `(1+‖p‖)^{-6}` is integrable on `ℝ³` (`6 > 3 = finrank`, `integrable_one_add_norm`).

On the tail region `{‖p‖ > r}` we have `1 ≤ (1+‖p‖)^6 / r^6` (because `r ≤ 1 + ‖p‖`), so
`profHat(p)² ≤ (r^6)^{-1} g(p)` pointwise there.  Integrating over the region and dominating by
the full integral of the nonnegative function `g` gives the claim with `K = ∫_p g(p) dp`. -/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Tprime

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

theorem profHat_sq_tail_decay : ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r →
    (∫ p in {p : EuclideanSpace ℝ (Fin 3) | r < ‖p‖}, (Work.OneBodyKin.profHat p) ^ 2) ≤ K / r ^ 6 := by
  obtain ⟨C, _hC, hd⟩ := Work.OneBodyKin.ProfHatDecay
  -- `(1 + ‖p‖)^{-6}` is integrable on `ℝ³` (`6 > 3 = finrank`)
  have hint6 : MeasureTheory.Integrable (fun p : ℝ³ => ((1 + ‖p‖ : ℝ) ^ 6)⁻¹) := by
    have h := integrable_one_add_norm (E := ℝ³) (μ := volume) (r := 6) (by
      rw [finrank_euclideanSpace]; norm_num)
    refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
    show (1 + ‖p‖) ^ (-(6 : ℝ)) = ((1 + ‖p‖ : ℝ) ^ 6)⁻¹
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖)]
    congr 1
    exact Real.rpow_natCast (1 + ‖p‖) 6
  -- the integrable weighted profile `g p = profHat(p)² (1+‖p‖)^6`
  set g : ℝ³ → ℝ := fun p => (Work.OneBodyKin.profHat p) ^ 2 * (1 + ‖p‖) ^ 6 with hg_def
  have hg_int : MeasureTheory.Integrable g := by
    rw [hg_def]
    refine (hint6.const_mul (C ^ 2)).mono' ?_ ?_
    · exact ((Work.OneBodyKin.continuous_profHat.pow 2).mul
        (((continuous_const : Continuous (fun _ : ℝ³ => (1 : ℝ))).add continuous_norm).pow 6)).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by positivity) 6))]
      have hpos : (0 : ℝ) < 1 + ‖p‖ := by positivity
      have hprof : (Work.OneBodyKin.profHat p) ^ 2 ≤ C ^ 2 / (1 + ‖p‖) ^ 12 := by
        have h1 : (Work.OneBodyKin.profHat p) ^ 2 ≤ (C / (1 + ‖p‖) ^ 6) ^ 2 := by
          rw [← sq_abs (Work.OneBodyKin.profHat p)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hd p) 2
        rw [div_pow, ← pow_mul] at h1
        norm_num at h1
        exact h1
      calc (Work.OneBodyKin.profHat p) ^ 2 * (1 + ‖p‖) ^ 6
          ≤ (C ^ 2 / (1 + ‖p‖) ^ 12) * (1 + ‖p‖) ^ 6 :=
            mul_le_mul_of_nonneg_right hprof (by positivity)
        _ = C ^ 2 * ((1 + ‖p‖ : ℝ) ^ 6)⁻¹ := by
            have h6 : (1 + ‖p‖ : ℝ) ^ 6 ≠ 0 := by positivity
            field_simp
  have hg_nonneg : 0 ≤ᵐ[volume] g := Filter.Eventually.of_forall (fun p => by
    rw [hg_def]; exact mul_nonneg (sq_nonneg _) (pow_nonneg (by positivity) 6))
  refine ⟨∫ p : ℝ³, g p, integral_nonneg (fun p => by
    rw [hg_def]; exact mul_nonneg (sq_nonneg _) (pow_nonneg (by positivity) 6)), ?_⟩
  intro r hr
  set s : Set (EuclideanSpace ℝ (Fin 3)) := {p | r < ‖p‖} with hs_def
  have hs : MeasurableSet s := by
    rw [hs_def]; exact measurableSet_lt measurable_const continuous_norm.measurable
  have hrpos : (0 : ℝ) < r := by linarith
  have hf_int : MeasureTheory.Integrable (fun p : ℝ³ => (Work.OneBodyKin.profHat p) ^ 2) := by
    have h := Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow 0 (by norm_num)
    simpa using h
  -- pointwise on the tail: `profHat(p)² ≤ (r^6)^{-1} g p`
  have hbound : ∀ p ∈ s, (Work.OneBodyKin.profHat p) ^ 2 ≤ (r ^ 6)⁻¹ * g p := by
    intro p hp
    rw [hs_def] at hp
    simp only [Set.mem_ofPred_eq] at hp
    have h6 : r ^ 6 ≤ (1 + ‖p‖) ^ 6 := by
      have : r ≤ 1 + ‖p‖ := by linarith [norm_nonneg p]
      exact pow_le_pow_left₀ (le_of_lt hrpos) this 6
    have hrel : (1 : ℝ) ≤ (1 + ‖p‖) ^ 6 / r ^ 6 := by
      rw [le_div_iff₀ (pow_pos hrpos 6)]
      simpa using h6
    calc (Work.OneBodyKin.profHat p) ^ 2
        = (Work.OneBodyKin.profHat p) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (Work.OneBodyKin.profHat p) ^ 2 * ((1 + ‖p‖) ^ 6 / r ^ 6) :=
            mul_le_mul_of_nonneg_left hrel (sq_nonneg _)
      _ = (r ^ 6)⁻¹ * g p := by
            rw [hg_def]
            have hr6 : (r : ℝ) ^ 6 ≠ 0 := by positivity
            field_simp
  have hA : ∫ p in s, (Work.OneBodyKin.profHat p) ^ 2 ≤ ∫ p in s, (r ^ 6)⁻¹ * g p := by
    have hs_ae : ∀ᵐ p ∂volume.restrict s, (Work.OneBodyKin.profHat p) ^ 2 ≤ (r ^ 6)⁻¹ * g p := by
      rw [MeasureTheory.ae_restrict_iff' hs]
      exact Filter.Eventually.of_forall (fun p hp => hbound p hp)
    exact MeasureTheory.integral_mono_ae hf_int.integrableOn
      ((hg_int.const_mul (r ^ 6)⁻¹).integrableOn) hs_ae
  calc ∫ p in s, (Work.OneBodyKin.profHat p) ^ 2
      ≤ ∫ p in s, (r ^ 6)⁻¹ * g p := hA
    _ = (r ^ 6)⁻¹ * ∫ p in s, g p := by rw [MeasureTheory.integral_const_mul]
    _ ≤ (r ^ 6)⁻¹ * ∫ p : ℝ³, g p :=
          mul_le_mul_of_nonneg_left (MeasureTheory.setIntegral_le_integral hg_int hg_nonneg)
            (by positivity)
    _ = (∫ p : ℝ³, g p) / r ^ 6 := by rw [inv_mul_eq_div]

end Work.BoseKinLoc.Tprime
