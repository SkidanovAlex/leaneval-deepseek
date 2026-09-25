import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.oscZ_model_of_block

/-!
# The block assembly of the model oscillation, along strictly increasing index families

`oscZ_model_of_block_mono` is the `StrictMono`-guarded version of
`Work.BourgainPlan.Oscillation.oscZ_model_of_block`: the per-block hypothesis is only assumed
along strictly increasing `k`, and only that case is concluded.  This is the shape in which the
circle-method input is actually available (the lacunary block oscillation
`oscZ_block_lacunary` is itself stated for strictly increasing `k`).

The proof is that of `oscZ_model_of_block` verbatim: the per-block hypothesis is used only at the
outer index family `k`, which in this statement is strictly increasing.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal
open Work.BourgainPlan.Maximal
open Commons.Analysis.ExponentialSums

noncomputable section

theorem oscZ_model_of_block_mono (P : Polynomial ℤ) (σ : ℝ) (hσ : 0 < σ) (N : ℕ → ℕ)
    (hm : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ),
      (∀ n, n ∉ s → g n = 0) →
        ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
          Work.BourgainPlan.Oscillation.oscZ
              (fun i x => Work.BourgainPlan.Oscillation.polyModelBlockOp P g s m (N i) x) J k
            ≤ ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2) ^ 2 *
                ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
        Work.BourgainPlan.Oscillation.oscZ
            (fun i x => Work.BourgainPlan.Oscillation.polyModelOp P g s (N i) x) J k
          ≤ ENNReal.ofReal (A^2) *
              ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hblk⟩ := hm
  set τ : ℝ := σ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτσ : τ < σ := by rw [hτdef]; linarith
  set W : ℝ≥0∞ := ∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)*τ))^(2:ℝ) with hW
  set D : ℝ≥0∞ := ∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
    ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2)^2) with hD
  have hWfin : W < ∞ := by rw [hW]; exact tsum_block_weight_sig_lt_top hτpos
  have hDfin : D < ∞ := by rw [hD]; exact tsum_scaled_K_sig_lt_top hCpos.le hτσ hτpos
  have hWD : W * D ≠ ∞ := ne_top_of_lt (ENNReal.mul_lt_top hWfin hDfin)
  refine ⟨Real.sqrt ((W * D).toReal) + 1, by positivity, ?_⟩
  have hA : W * D ≤ ENNReal.ofReal ((Real.sqrt ((W * D).toReal) + 1)^2) := by
    have h5 : (W * D).toReal ≤ (Real.sqrt ((W * D).toReal) + 1)^2 := by
      rw [add_sq, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (W * D).toReal)]
      linarith [Real.sqrt_nonneg ((W * D).toReal)]
    calc W * D = ENNReal.ofReal ((W * D).toReal) := (ENNReal.ofReal_toReal hWD).symm
      _ ≤ ENNReal.ofReal ((Real.sqrt ((W * D).toReal) + 1)^2) := ENNReal.ofReal_le_ofReal h5
  intro g s hgs J k hk
  have key : oscZ (fun i x => polyModelOp P g s (N i) x) J k
      ≤ W * D * (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) := by
    rw [oscZ]
    calc ∑ j ∈ Finset.range J, (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
          ‖polyModelOp P g s (N i) x - polyModelOp P g s (N (k j)) x‖ₑ) ^ (2:ℝ)
        ∂MeasureTheory.Measure.count)
        ≤ ∑ j ∈ Finset.range J, W * (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
            (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ) ^ (2:ℝ)
              ∂MeasureTheory.Measure.count)) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have h := oscZ_model_term_le P g s N k hτpos j
          rwa [← hW] at h
      _ = W * (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
            (∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ) ^ (2:ℝ)
              ∂MeasureTheory.Measure.count)) := by
          rw [← Finset.mul_sum, sum_tsum_ennreal]
          congr 1
          refine tsum_congr (fun m => ?_)
          rw [Finset.mul_sum]
      _ ≤ W * (D * (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count)) := by
          gcongr
          have h1 : (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
              (∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
                ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ) ^ (2:ℝ)
                ∂MeasureTheory.Measure.count))
              ≤ ∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
                  (ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2)^2 *
                    (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count))) := by
            refine ENNReal.tsum_le_tsum (fun m => ?_)
            gcongr
            have hZ : (∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
                  ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ) ^ (2:ℝ)
                  ∂MeasureTheory.Measure.count)
                = oscZ (fun i x => polyModelBlockOp P g s m (N i) x) J k := rfl
            rw [hZ]
            exact hblk m g s hgs J k hk
          have h2 : (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
                (ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2)^2 *
                  (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count))))
              = D * (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) := by
            rw [hD]
            rw [show (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
                  (ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2)^2 *
                    (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count))))
                = ∑' m : ℕ, ((((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
                  ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2)^2) *
                    (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count)) from
              tsum_congr (fun m => (mul_assoc _ _ _).symm)]
            rw [ENNReal.tsum_mul_right]
          exact le_trans h1 (le_of_eq h2)
      _ = W * D * (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) := by rw [mul_assoc]
  refine le_trans key ?_
  exact mul_le_mul_of_nonneg_right hA (by positivity)

end

end Work.BourgainPlan.Oscillation
