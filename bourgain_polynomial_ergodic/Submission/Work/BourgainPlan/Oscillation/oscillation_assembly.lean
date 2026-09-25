import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.oscillation_reduction
import Submission.Work.BourgainPlan.Oscillation.oscFunctional_le_oscZ_weyl
import Submission.Work.BourgainPlan.Oscillation.oscZ_block_lacunary_v2
import Submission.Work.BourgainPlan.Oscillation.oscZ_model_of_block_mono
import Submission.Work.BourgainPlan.Oscillation.oscZ_weyl_lacunary
import Submission.Work.BourgainPlan.Oscillation.oscZ_deg_le_one_v2
import Submission.Work.BourgainPlan.Maximal.kernel_l2
import Submission.Work.BourgainPlan.Maximal.z_transfer

/-!
# Assembly of the lacunary ℓ² oscillation inequality

This file assembles `SublinearOscillationStatement` (the analytic core of the oscillation area)
from the pieces proved in this directory:

* `oscZ_block_lacunary_v2` — the per-denominator-block oscillation bound for the model at the
  lacunary scales `⌊ρ^i⌋`, with the constant `C·2^{-m·polySig}(m+2)²`;
* `oscZ_model_of_block_mono` — the Cauchy–Schwarz assembly over the denominator blocks `m`;
* `oscZ_weyl_lacunary` — the passage from the major-arc model to the true Weyl kernel
  (using `Work.BourgainPlan.Maximal.model_pre`);
* `oscZ_deg_le_one_v2` — the same estimate for `natDegree P ≤ 1` (handled directly);
* `oscFunctional_le_oscZ_weyl` — the `ℕ → ℤ` transfer of the oscillation functional.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

open Work.BourgainPlan.Maximal (leadingCoeff_pos_of_nonnegOnNat polySig)

/-- The `ℤ`-integral of the lift of a function on `ℕ` is the `ℕ`-integral. -/
lemma lintegral_liftZC (g : ℕ → ℝ) :
    ∫⁻ x : ℤ, ‖liftZC g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count
      = ∫⁻ n : ℕ, ‖g n‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  rw [Work.BourgainPlan.Maximal.lintegral_count_nat_int (fun n : ℕ => ‖g n‖ₑ ^ (2 : ℝ))]
  refine lintegral_congr (fun m => ?_)
  by_cases h : 0 ≤ m
  · rw [liftZC_of_nonneg g h, if_pos h]
    congr 1
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    congr 1
    exact NNReal.eq (Complex.norm_real (g m.toNat))
  · rw [liftZC_of_neg g h, if_neg h]
    simp

/-- **The lacunary ℓ² oscillation bound for the Weyl kernel of every `P`** (all degrees). -/
theorem oscZ_weyl_lacunary_all (P : Polynomial ℤ)
    (hP : Submission.BourgainPlan.NonnegOnNat P) (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
        oscZ (fun i x => polyWeylOp P g s (lacScale ρ i) x) J k
          ≤ ENNReal.ofReal (C ^ 2) *
              ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  by_cases hd : P.natDegree ≤ 1
  · exact oscZ_deg_le_one_v2 P hP hd ρ hρ
  · have hd2 : 2 ≤ P.natDegree := by omega
    have hc : 0 < P.leadingCoeff := leadingCoeff_pos_of_nonnegOnNat P hP hd2
    obtain ⟨Cb, hCb, hblk⟩ := oscZ_block_lacunary_v2 P hc hd2 ρ hρ
    have hblockhyp : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ),
        (∀ n, n ∉ s → g n = 0) → ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
          oscZ (fun i x => polyModelBlockOp P g s m (lacScale ρ i) x) J k
            ≤ ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ) * polySig P) * ((m:ℝ)+2)^2) ^ 2 *
                ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count :=
      ⟨Cb, hCb, fun m g s hs J k hk => hblk m g s hs J k hk⟩
    have hσ : 0 < polySig P := by rw [polySig, Commons.Analysis.ExponentialSums.powSig]; positivity
    obtain ⟨A, hA, hmod⟩ :=
      oscZ_model_of_block_mono P (polySig P) hσ (lacScale ρ) hblockhyp
    exact oscZ_weyl_lacunary P hc hd2 ρ hρ ⟨A, hA, hmod⟩

/-- **The sublinear lacunary oscillation bound for the polynomial averages** (the analytic core of
the oscillation area).  Assembled here from the per-block estimate, the block assembly, the
model-to-kernel passage and the `ℕ → ℤ` transfer. -/
theorem lacunary_oscillation_core : SublinearOscillationStatement := by
  intro P hP ρ hρ
  obtain ⟨C, hCpos, hCb⟩ := oscZ_weyl_lacunary_all P hP ρ hρ
  refine ⟨C ^ 2, by positivity, 0, by norm_num, ?_⟩
  intro J k hk g hg
  obtain ⟨s, hs⟩ := hg
  calc oscFunctional P ρ J k g
      ≤ oscZ (fun i x => polyWeylOp P (liftZC g) (liftFinset s) (lacScale ρ i) x) J k :=
        oscFunctional_le_oscZ_weyl P hP ρ J k g s hs
    _ ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ x : ℤ, ‖liftZC g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count :=
        hCb (liftZC g) (liftFinset s) (liftZC_support g s hs) J k hk
    _ = ENNReal.ofReal (C ^ 2) *
          ∫⁻ n : ℕ, ‖g n‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
        rw [lintegral_liftZC g]
    _ = ENNReal.ofReal (C ^ 2 * (J : ℝ) ^ (0 : ℝ)) *
          ∫⁻ n : ℕ, ‖g n‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
        rw [Real.rpow_zero, mul_one]

end

end Work.BourgainPlan.Oscillation
