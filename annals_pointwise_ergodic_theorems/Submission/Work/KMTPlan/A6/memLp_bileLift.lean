import Mathlib
import Submission.Work.KMTPlan.A6.BileLiftDefs
import Submission.Work.KMTPlan.A6.SchwartzLiftSummable
import Submission.Port.Aesm

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal

/-- A sequence on `ℤ` whose squares are summable belongs to `ℓ²(ℤ)` with respect to the counting
measure.  The `L²`-seminorm is the `ℓ²`-series by `lintegral_count`, and that series is finite
because `ofReal` never takes the value `⊤`. -/
theorem memLp_of_summable_sq {g : ℤ → ℂ} (h : Summable (fun n : ℤ => ‖g n‖ ^ 2)) :
    MeasureTheory.MemLp g 2 MeasureTheory.Measure.count := by
  rw [MeasureTheory.memLp_iff]
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (hf := by pw_aesm) (by norm_num) (by norm_num)]
  rw [lintegral_count]
  have hpt : ∀ a : ℤ, ‖g a‖ₑ ^ (2 : ℝ≥0∞).toReal = ENNReal.ofReal (‖g a‖ ^ 2) := by
    intro a
    rw [ENNReal.toReal_ofNat, ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simp_rw [hpt]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) h]
  exact ENNReal.ofReal_lt_top

/-- The lift `n ↦ R^{-1/2} ψ (n / R) u (n mod Q)` of a function on `ZMod Q` is square summable:
the Schwartz window `ψ (n / R)` is itself absolutely summable along the lattice
(`summable_norm_schwartzLift`), and the bounded factor `u` together with the constant
`R^{-1/2}` only produces a comparison constant. -/
theorem memLp_bileLift (ψ : SchwartzMap ℝ ℂ) (R : ℕ) {Q : ℕ} [NeZero Q] (u : ZMod Q → ℂ) :
    MeasureTheory.MemLp (Work.KMTPlan.A6.bileLift (ψ : ℝ → ℂ) R u) 2
      MeasureTheory.Measure.count := by
  by_cases hR : R = 0
  · -- at `R = 0` the prefactor `(√R)⁻¹` vanishes and the lift is the zero sequence
    have hzero : bileLift (ψ : ℝ → ℂ) 0 u = 0 := by
      funext n
      simp [bileLift]
    rw [hR, hzero]
    exact MemLp.zero
  · have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hR
    refine memLp_of_summable_sq ?_
    -- the Schwartz window sampled at step `R` is absolutely summable, hence square summable
    have hψsum : Summable (fun n : ℤ => ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖) :=
      summable_norm_schwartzLift ψ hRpos
    have hψ2 : Summable (fun n : ℤ => ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2) := by
      refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
        (hψsum.mul_left (SchwartzMap.seminorm ℝ 0 0 ψ))
      have hM : ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ≤ SchwartzMap.seminorm ℝ 0 0 ψ :=
        SchwartzMap.norm_le_seminorm ℝ ψ _
      calc ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2
          = ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ * ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ := by ring
        _ ≤ SchwartzMap.seminorm ℝ 0 0 ψ * ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ :=
            mul_le_mul_of_nonneg_right hM (norm_nonneg _)
    -- the comparison constant
    set c : ℝ := ‖((Real.sqrt (R : ℝ))⁻¹ : ℂ)‖ * (∑ i : ZMod Q, ‖u i‖) with hc
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      (hψ2.mul_left (c ^ 2))
    have hu : ‖u ((n : ZMod Q))‖ ≤ ∑ i : ZMod Q, ‖u i‖ :=
      Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ _)
    have hb : ‖bileLift (ψ : ℝ → ℂ) R u n‖
        ≤ c * ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ := by
      rw [hc]
      simp only [bileLift, norm_mul]
      calc ‖((Real.sqrt (R : ℝ))⁻¹ : ℂ)‖ * ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖
            * ‖u (n : ZMod Q)‖
          ≤ ‖((Real.sqrt (R : ℝ))⁻¹ : ℂ)‖ * ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖
              * (∑ i : ZMod Q, ‖u i‖) :=
            mul_le_mul_of_nonneg_left hu (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = (‖((Real.sqrt (R : ℝ))⁻¹ : ℂ)‖ * (∑ i : ZMod Q, ‖u i‖))
              * ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ := by ring
    calc ‖bileLift (ψ : ℝ → ℂ) R u n‖ ^ 2
        ≤ (c * ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = c ^ 2 * ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2 := by ring

end Work.KMTPlan.A6
