import Mathlib.Tactic.Have
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Tprime.symA_zero_decay` — polynomial decay of the origin value of the symbol

At scale `ℓ = 1` and momentum `q = 0` the unprojected family symbol is

    `symA 1 F 0 = (2π)⁻³ ∫_p F(‖p‖) · profHat(p)² dp`

(`Work.OneBodyKin.symA`, with `ℓ⁻¹ • p = p` and `q = 0`).  For the FS cut-off
`F = fsKinCoeff C = [· − C]₊² = (max (· − C) 0)²` the integrand therefore *vanishes* on the ball
`‖p‖ ≤ C` and equals `(‖p‖ − C)² profHat(p)²` outside it.  Since the bump profile decays faster
than any polynomial (`Work.OneBodyKin.ProfHatDecay`: `|profHat p| ≤ C₀ (1+‖p‖)^{-6}`), the
`C → ∞` behaviour is polynomial:

    `∃ K ≥ 0, ∀ C ≥ 1,  symA 1 (fsKinCoeff C) 0 ≤ K / C^5`.

This is the decay input that the *near-region* branch of the two-regime symbol bound
(`Tprime/tprime_two_regime.lean`, BS `lm:kinloc`) invokes: it is what controls the
`symA`-contribution `symA 1 (fsKinCoeff σ⁻¹) 0` of the near region, i.e. the value of the
unprojected symbol at the origin with the cut-off `σ⁻¹ → ∞`.

## The proof, in three elementary steps

Write `r := ‖p‖` and fix `C ≥ 1`.

1. **Pointwise domination.**  If `r ≤ C` the cut-off vanishes.  If `r > C` then `C > 0`, and

       `(r − C)² ≤ r²`,     `profHat(p)² ≤ C₀² (1+r)^{-12}`,

   hence

       `[r − C]₊² profHat(p)² ≤ C₀² r² (1+r)^{-12} ≤ 32 C₀² C^{-5} (1+r)^{-5}`;

   the last step is `r²(1+r)^{-12} ≤ r^{-10} = r^{-5}·r^{-5} ≤ C^{-5}·32(1+r)^{-5}`, using
   `r ≥ C` for `r^{-5} ≤ C^{-5}` and `1 + r ≤ 2r` (valid because `r ≥ C ≥ 1`) for
   `r^{-5} ≤ 32(1+r)^{-5}`.

2. **Integration.**  The dominating function `p ↦ 32 C₀² C^{-5} (1+‖p‖)^{-5}` is integrable
   in dimension `3` because `5 > 3` (`integrable_one_add_norm`), so `integral_mono_of_nonneg`
   bounds `∫_p [‖p‖ − C]₊² profHat(p)² dp` by `32 C₀² C^{-5} · I` with
   `I := ∫_p (1+‖p‖)^{-5} dp ≥ 0`.

3. **Reading off `K`.**  Multiplying by `(2π)^{-3}` gives the claim with the constant
   `K := (2π)^{-3} · 32 C₀² · I ≥ 0`.

No bookkeeping of the cut-off via set-integrals or scaling of Lebesgue measure is needed: the
`C^{-5}`-decay is produced *pointwise* by the factor `r ≥ C` inside the integrand.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real

namespace Work.BoseKinLoc.Tprime

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## 1. The pointwise domination -/

/-- **Pointwise domination of the cut-off integrand.**  For `C ≥ 1` and `C₀` the decay constant
of the bump profile, the FS-cut-off integrand is bounded by the integrable weight
`32 C₀² C^{-5} (1+‖p‖)^{-5}`.  This is the whole `C`-dependence of the estimate, produced
pointwise on the exterior region `‖p‖ > C`. -/
private lemma fsKinCoeff_mul_profHat_sq_le {C₀ C : ℝ} (hC : 1 ≤ C)
    (hdec : ∀ p : ℝ³, |Work.OneBodyKin.profHat p| ≤ C₀ / (1 + ‖p‖) ^ 6) (p : ℝ³) :
    fsKinCoeff C ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2
      ≤ 32 * C₀ ^ 2 * (C ^ 5)⁻¹ * ((1 + ‖p‖) ^ 5)⁻¹ := by
  by_cases hle : ‖p‖ ≤ C
  · -- the cut-off swallows `‖p‖`: the integrand vanishes
    rw [fsKinCoeff_of_le hle, zero_mul]
    positivity
  · -- `‖p‖ > C ≥ 1`: the cut-off is `(‖p‖ − C)²`
    have hle' : C < ‖p‖ := not_le.mp hle
    rw [fsKinCoeff_of_lt (by linarith) hle']
    have hCpos : 0 < C := by linarith
    -- the squared profile obeys the sixth-power decay
    have hp2 : (Work.OneBodyKin.profHat p) ^ 2 ≤ C₀ ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹ := by
      have h := pow_le_pow_left₀ (abs_nonneg (Work.OneBodyKin.profHat p)) (hdec p) 2
      rw [sq_abs, div_pow, ← pow_mul] at h
      norm_num at h
      rwa [div_eq_mul_inv] at h
    -- `(‖p‖ − C)² ≤ ‖p‖²`
    have hrC : (‖p‖ - C) ^ 2 ≤ ‖p‖ ^ 2 := by
      nlinarith [norm_nonneg p, hCpos]
    -- the weight inequality `‖p‖² (1+‖p‖)^{-12} ≤ 32 C^{-5} (1+‖p‖)^{-5}`
    have hkey : ‖p‖ ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹ ≤ 32 * (C ^ 5)⁻¹ * ((1 + ‖p‖) ^ 5)⁻¹ := by
      have hC5 : C ^ 5 ≤ ‖p‖ ^ 5 := pow_le_pow_left₀ hCpos.le (le_of_lt hle') 5
      have h1 : ‖p‖ ^ 2 * C ^ 5 ≤ ‖p‖ ^ 7 := by
        nlinarith [mul_le_mul_of_nonneg_left hC5 (sq_nonneg ‖p‖)]
      have h2 : ‖p‖ ^ 7 ≤ (1 + ‖p‖) ^ 7 := pow_le_pow_left₀ (by positivity) (by linarith) 7
      have h3 : 32 * ‖p‖ ^ 7 ≤ 32 * (1 + ‖p‖) ^ 7 := mul_le_mul_of_nonneg_left h2 (by norm_num)
      have h4 : ‖p‖ ^ 2 * C ^ 5 ≤ 32 * ‖p‖ ^ 7 := by
        have : (0 : ℝ) ≤ ‖p‖ ^ 7 := by positivity
        nlinarith [h1, this]
      have h5 : ‖p‖ ^ 2 * C ^ 5 ≤ 32 * (1 + ‖p‖) ^ 7 := le_trans h4 h3
      field_simp
      linarith
    calc (‖p‖ - C) ^ 2 * (Work.OneBodyKin.profHat p) ^ 2
        ≤ ‖p‖ ^ 2 * (C₀ ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹) :=
          mul_le_mul hrC hp2 (sq_nonneg _) (by positivity)
      _ = C₀ ^ 2 * (‖p‖ ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹) := by ring
      _ ≤ C₀ ^ 2 * (32 * (C ^ 5)⁻¹ * ((1 + ‖p‖) ^ 5)⁻¹) :=
          mul_le_mul_of_nonneg_left hkey (sq_nonneg C₀)
      _ = 32 * C₀ ^ 2 * (C ^ 5)⁻¹ * ((1 + ‖p‖) ^ 5)⁻¹ := by ring

/-! ## 2. The value of the symbol at the origin and scale `1` -/

/-- At the origin and at scale `ℓ = 1` the unprojected symbol is the plain `(2π)^{-3}`-multiple
of the integral of the symbol against the squared bump profile. -/
private lemma symA_one_zero (F : ℝ → ℝ) :
    Work.OneBodyKin.symA 1 F 0
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2 := by
  simp only [Work.OneBodyKin.symA, zero_add, inv_one, one_smul]

/-! ## 3. The decay theorem -/

theorem symA_zero_decay : ∃ K : ℝ, 0 ≤ K ∧ ∀ C : ℝ, 1 ≤ C →
    Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) 0 ≤ K / C ^ 5 := by
  obtain ⟨C₀, _hC₀nn, hdec⟩ := Work.OneBodyKin.ProfHatDecay
  -- the dominating weight `(1 + ‖p‖)^{-5}` is integrable in dimension `3`
  have hDint : MeasureTheory.Integrable (fun p : ℝ³ => ((1 + ‖p‖ : ℝ) ^ 5)⁻¹) := by
    have h := integrable_one_add_norm (E := ℝ³) (μ := MeasureTheory.volume) (r := 5)
      (by rw [finrank_euclideanSpace_fin]; norm_num)
    refine h.congr ?_
    filter_upwards with p
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖)]
    congr 1
    exact Real.rpow_natCast (1 + ‖p‖) 5
  have hInn : 0 ≤ ∫ p : ℝ³, ((1 + ‖p‖ : ℝ) ^ 5)⁻¹ :=
    MeasureTheory.integral_nonneg (fun p => by positivity)
  refine ⟨((2 * Real.pi) ^ 3)⁻¹ * (32 * C₀ ^ 2) *
      ∫ p : ℝ³, ((1 + ‖p‖ : ℝ) ^ 5)⁻¹, by positivity, fun C hC => ?_⟩
  -- the integral bound
  have key : ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff C ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2
      ≤ (32 * C₀ ^ 2 * (C ^ 5)⁻¹) * ∫ p : ℝ³, ((1 + ‖p‖ : ℝ) ^ 5)⁻¹ := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hDint.const_mul _) ?_
    · filter_upwards with p
      exact mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg C ‖p‖) (sq_nonneg _)
    · filter_upwards with p
      exact fsKinCoeff_mul_profHat_sq_le hC hdec p
  calc Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) 0
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
          Submission.BoseGases.fsKinCoeff C ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2 :=
        symA_one_zero _
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          ((32 * C₀ ^ 2 * (C ^ 5)⁻¹) * ∫ p : ℝ³, ((1 + ‖p‖ : ℝ) ^ 5)⁻¹) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (((2 * Real.pi) ^ 3)⁻¹ * (32 * C₀ ^ 2) *
          ∫ p : ℝ³, ((1 + ‖p‖ : ℝ) ^ 5)⁻¹) / C ^ 5 := by
        rw [div_eq_mul_inv]; ring

end Work.BoseKinLoc.Tprime
