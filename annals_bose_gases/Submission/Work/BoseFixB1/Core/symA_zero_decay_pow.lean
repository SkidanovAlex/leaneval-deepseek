import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Tprime.profHat_decay_twelve
import Submission.Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Core.symA_zero_decay_pow` — fast polynomial decay of the symbol at the origin

At scale `1` and momentum `q = 0` the unprojected family symbol is

    `symA 1 F 0 = (2π)⁻³ ∫_p F(‖p‖)·profHat(p)² dp`

(`Work.OneBodyKin.symA` with `ℓ = 1`, `q = 0`).  For the FS cut-off
`F = fsKinCoeff C = [· − C]₊²` the integrand is supported on `‖p‖ > C`, and since the bump
profile is Schwartz (`Work.BoseKinLoc.Tprime.profHat_decay_twelve`:
`|profHat p| ≤ K₁ (1+‖p‖)^{-12}`) we get, for `C ≥ 1` and `r = ‖p‖ > C`,

    `(r − C)² profHat(p)² ≤ r² K₁² (1+r)^{-24} ≤ K₁² C^{-16} (1+r)^{-6}`,

the two steps being `(1+r)^{-16} ≤ C^{-16}` (valid because `1 + r ≥ r ≥ C`) and
`r²(1+r)^{-8} ≤ (1+r)^{-6}`.  Since `(1+‖p‖)^{-6}` is integrable in dimension three, this gives

    `symA 1 (fsKinCoeff C) 0 ≤ K C^{-16}`       for all `C ≥ 1`,

with `K = (2π)⁻³ K₁² ∫_p (1+‖p‖)^{-6} dp`.

This is the decay input of the two-cut symbol comparison at FS's parameters, where
`C = c_sb·(dℓ) = 1/s` and the comparison's constant term is `β = K(2s)^{16}`; the coarser
`symA_zero_decay` of `BoseKinLoc/Tprime` (which buys only `C^{-5}`) is not enough there because the
resulting payment `β/(dℓ)²` must be dominated by the gap slack `(·)/(ℓ²)`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real Topology

namespace Work.BoseFixB1.Core

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- **Pointwise domination.**  With the twelve-fold decay of the bump profile and `C ≥ 1`, the
cut-off integrand is dominated by `K₁² C^{-16} (1+‖p‖)^{-6}`. -/
private lemma fsKinCoeff_mul_profHat_sq_le {K₁ C : ℝ} (hC : 1 ≤ C)
    (hdec : ∀ p : E3, |Work.OneBodyKin.profHat p| ≤ K₁ / (1 + ‖p‖) ^ 12) (p : E3) :
    Submission.BoseGases.fsKinCoeff C ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2
      ≤ K₁ ^ 2 * C ^ (-(16 : ℝ)) * (1 + ‖p‖) ^ (-(6 : ℝ)) := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hpos : (0 : ℝ) < 1 + ‖p‖ := by positivity
  have h6 : (1 + ‖p‖) ^ (-(6 : ℝ)) = ((1 + ‖p‖) ^ 6)⁻¹ := by
    rw [Real.rpow_neg hpos.le]; norm_num [Real.rpow_natCast]
  -- `C^{-16} = (C^16)^{-1}`
  have hCinv : C ^ (-(16 : ℝ)) = (C ^ 16)⁻¹ := by
    rw [Real.rpow_neg hC0.le]; norm_num [Real.rpow_natCast]
  by_cases hle : ‖p‖ ≤ C
  · rw [Submission.BoseGases.fsKinCoeff_of_le hle, zero_mul]
    have : 0 ≤ K₁ ^ 2 * C ^ (-(16 : ℝ)) * (1 + ‖p‖) ^ (-(6 : ℝ)) := by positivity
    linarith
  · have hlt : C < ‖p‖ := not_le.mp hle
    rw [Submission.BoseGases.fsKinCoeff_of_lt hC0.le hlt]
    -- `profHat² ≤ K₁² (1+‖p‖)^{-24}`
    have hp2 : (Work.OneBodyKin.profHat p) ^ 2 ≤ K₁ ^ 2 * ((1 + ‖p‖) ^ 24)⁻¹ := by
      have hh := pow_le_pow_left₀ (abs_nonneg (Work.OneBodyKin.profHat p)) (hdec p) 2
      rw [sq_abs, div_pow, ← pow_mul] at hh
      norm_num at hh
      rwa [div_eq_mul_inv] at hh
    -- `(‖p‖ − C)² ≤ ‖p‖²`
    have hr2 : (‖p‖ - C) ^ 2 ≤ ‖p‖ ^ 2 := by
      have h3 : 0 ≤ ‖p‖ - C := by linarith
      nlinarith [norm_nonneg p]
    -- `(1+‖p‖)^{-24} ≤ C^{-16}(1+‖p‖)^{-8}`, i.e. `(1+‖p‖)^{-16} ≤ C^{-16}`
    have hsplit : ((1 + ‖p‖) ^ 24)⁻¹ ≤ C ^ (-(16 : ℝ)) * ((1 + ‖p‖) ^ 8)⁻¹ := by
      have h16 : ((1 + ‖p‖) ^ 16)⁻¹ ≤ (C ^ 16)⁻¹ :=
        (inv_le_inv₀ (by positivity : (0:ℝ) < (1 + ‖p‖) ^ 16) (by positivity : (0:ℝ) < C ^ 16)).mpr
          (calc C ^ 16 ≤ ‖p‖ ^ 16 := pow_le_pow_left₀ hC0.le hlt.le 16
            _ ≤ (1 + ‖p‖) ^ 16 := by gcongr; linarith [norm_nonneg p])
      have hfac : ((1 + ‖p‖) ^ 24)⁻¹ = ((1 + ‖p‖) ^ 16)⁻¹ * ((1 + ‖p‖) ^ 8)⁻¹ := by
        rw [← mul_inv]; ring_nf
      rw [hfac, hCinv]
      exact mul_le_mul_of_nonneg_right h16 (by positivity)
    -- `‖p‖²(1+‖p‖)^{-8} ≤ (1+‖p‖)^{-6}`
    have hlast : ‖p‖ ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹ ≤ (1 + ‖p‖) ^ (-(6 : ℝ)) := by
      have hbase : ‖p‖ ^ 2 ≤ (1 + ‖p‖) ^ 2 := by nlinarith [norm_nonneg p]
      have h1 : ‖p‖ ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹ ≤ (1 + ‖p‖) ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹ :=
        mul_le_mul_of_nonneg_right hbase (by positivity)
      have h2 : (1 + ‖p‖) ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹ = ((1 + ‖p‖) ^ 6)⁻¹ := by field_simp
      rw [h6]
      exact le_trans h1 (le_of_eq h2)
    calc (‖p‖ - C) ^ 2 * (Work.OneBodyKin.profHat p) ^ 2
        ≤ ‖p‖ ^ 2 * (K₁ ^ 2 * ((1 + ‖p‖) ^ 24)⁻¹) :=
          mul_le_mul hr2 hp2 (sq_nonneg _) (by positivity)
      _ = K₁ ^ 2 * (‖p‖ ^ 2 * ((1 + ‖p‖) ^ 24)⁻¹) := by ring
      _ ≤ K₁ ^ 2 * (‖p‖ ^ 2 * (C ^ (-(16 : ℝ)) * ((1 + ‖p‖) ^ 8)⁻¹)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsplit (by positivity)) (by positivity)
      _ = K₁ ^ 2 * C ^ (-(16 : ℝ)) * (‖p‖ ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹) := by ring
      _ ≤ K₁ ^ 2 * C ^ (-(16 : ℝ)) * (1 + ‖p‖) ^ (-(6 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlast (by positivity)

/-! ## The decay theorem -/

/-- **Fast polynomial decay of the symbol at the origin.**  For the FS cut-off `fsKinCoeff C` and
every `C ≥ 1`, `symA 1 (fsKinCoeff C) 0 ≤ K C^{-16}`. -/
theorem symA_zero_decay_pow : ∃ K : ℝ, 0 ≤ K ∧ ∀ C : ℝ, 1 ≤ C →
    Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) 0 ≤ K * C ^ (-(16 : ℝ)) := by
  obtain ⟨K₁, hK₁, hdec⟩ := Work.BoseKinLoc.Tprime.profHat_decay_twelve
  refine ⟨((2 * Real.pi) ^ 3)⁻¹ * K₁ ^ 2 * ∫ p : E3, (1 + ‖p‖) ^ (-(6 : ℝ)), by positivity, ?_⟩
  intro C hC
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hfin : (Module.finrank ℝ E3 : ℝ) < 6 := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hInt : Integrable (fun p : E3 => K₁ ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ))) volume :=
    (integrable_one_add_norm (E := E3) (μ := volume) (r := 6) hfin).const_mul (K₁ ^ 2)
  have hdom : Integrable (fun p : E3 => K₁ ^ 2 * C ^ (-(16 : ℝ)) * (1 + ‖p‖) ^ (-(6 : ℝ))) volume :=
    (hInt.const_mul (C ^ (-(16 : ℝ)))).congr
      (Filter.Eventually.of_forall fun p => by ring)
  have hsymA : Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) 0
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          Submission.BoseGases.fsKinCoeff C ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2 := by
    simp only [Work.OneBodyKin.symA, zero_add, inv_one, one_smul]
  rw [hsymA]
  have hstep : (∫ p : E3, Submission.BoseGases.fsKinCoeff C ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2)
      ≤ K₁ ^ 2 * (∫ p : E3, (1 + ‖p‖) ^ (-(6 : ℝ))) * C ^ (-(16 : ℝ)) := by
    have hmono : (∫ p : E3, Submission.BoseGases.fsKinCoeff C ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2)
        ≤ ∫ p : E3, K₁ ^ 2 * C ^ (-(16 : ℝ)) * (1 + ‖p‖) ^ (-(6 : ℝ)) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ hdom ?_
      · filter_upwards with p
        exact mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg C ‖p‖) (sq_nonneg _)
      · filter_upwards with p
        exact fsKinCoeff_mul_profHat_sq_le hC hdec p
    refine le_trans hmono (le_of_eq ?_)
    rw [show (∫ p : E3, K₁ ^ 2 * C ^ (-(16 : ℝ)) * (1 + ‖p‖) ^ (-(6 : ℝ)))
          = C ^ (-(16 : ℝ)) * (∫ p : E3, K₁ ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ))) from by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)]
    rw [MeasureTheory.integral_const_mul]
    ring
  calc ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
        Submission.BoseGases.fsKinCoeff C ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (K₁ ^ 2 * (∫ p : E3, (1 + ‖p‖) ^ (-(6 : ℝ))) * C ^ (-(16 : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = ((2 * Real.pi) ^ 3)⁻¹ * K₁ ^ 2 * (∫ p : E3, (1 + ‖p‖) ^ (-(6 : ℝ))) * C ^ (-(16 : ℝ)) := by
        ring

end Work.BoseFixB1.Core
