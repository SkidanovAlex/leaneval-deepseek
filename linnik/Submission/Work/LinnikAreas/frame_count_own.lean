import Mathlib
import Submission.Work.LinnikAreas.sumI_le_own
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.frame_step_defs
import Submission.Work.LinnikBurgess.frame_count_prov_defs
import Submission.Work.LinnikBurgess.frame_count_prov_aux.frameSum_eq_masterSum
import Submission.Work.LinnikBurgess.masterSum_le_sum_cases
import Submission.Work.LinnikBurgess.sumS_le
import Submission.Work.LinnikBurgess.sumT_le

open scoped BigOperators
open Classical

namespace Work.LinnikAreas

open Work.LinnikBurgess

/-- Theorem F (the frame count), assembled with my own sorry-free `sumI_le_own`. -/
theorem frame_count_own {H : ℕ} (i : Fin 6) {m d g : ℕ} (hm : Squarefree m)
    (hmd : Nat.Coprime m d) (hmg : Nat.Coprime m g) (hd : 0 < d) (hg : 0 < g) :
    ∑ fg ∈ (Finset.univ : Finset ((Fin 3 → Fin H) × (Fin 3 → Fin H))).filter
        (fun fg => ∀ i', i' ≠ i → shift6 fg i ≠ shift6 fg i'),
      sqrtGcdW m i (shift6 fg) * frameW d g fg
      ≤ 10 ^ 5 * (3 : ℝ) ^ d.primeFactors.card * ((m * d * g).divisors.card : ℝ) ^ 8
          * ((H : ℝ) ^ 6 / ((d : ℝ) * g) + (H : ℝ) ^ 5 / g) := by
  change frameSum H m d g i ≤ _
  rw [frameSum_eq_zero H m d g i,
    frame_count_prov_aux.frameSum_eq_masterSum H m d g]
  have hI := sumI_le_own (H := H) hm hmd hmg hd hg
  have hS := sumS_le (H := H) hm hmd hmg hd hg
  have hT := sumT_le (H := H) hm hmd hmg hd hg
  have hM := masterSum_le_sum_cases H m d g
  have hXnn : (0 : ℝ) ≤ ((m * d * g).divisors.card : ℝ) ^ 8
      * ((H : ℝ) ^ 6 / ((d : ℝ) * (g : ℝ)) + (H : ℝ) ^ 5 / (g : ℝ)) := by positivity
  have h1le : (1 : ℝ) ≤ (3 : ℝ) ^ d.primeFactors.card := one_le_pow₀ (by norm_num)
  have hcoef : (3 : ℝ) * 30000 ≤ 10 ^ 5 * (3 : ℝ) ^ d.primeFactors.card := by
    have h := mul_le_mul_of_nonneg_left h1le (by norm_num : (0:ℝ) ≤ 10^5)
    linarith
  have hrhs : (3 : ℝ) * rhsC 30000 H m d g
      ≤ 10 ^ 5 * (3 : ℝ) ^ d.primeFactors.card * ((m * d * g).divisors.card : ℝ) ^ 8
          * ((H : ℝ) ^ 6 / ((d : ℝ) * g) + (H : ℝ) ^ 5 / g) := by
    rw [rhsC]
    have h := mul_le_mul_of_nonneg_right hcoef hXnn
    calc (3 : ℝ) * (30000 * ((m * d * g).divisors.card : ℝ) ^ 8
            * ((H : ℝ) ^ 6 / ((d : ℝ) * (g : ℝ)) + (H : ℝ) ^ 5 / (g : ℝ)))
        = ((3 : ℝ) * 30000) * (((m * d * g).divisors.card : ℝ) ^ 8
            * ((H : ℝ) ^ 6 / ((d : ℝ) * (g : ℝ)) + (H : ℝ) ^ 5 / (g : ℝ))) := by ring
      _ ≤ (10 ^ 5 * (3 : ℝ) ^ d.primeFactors.card) * (((m * d * g).divisors.card : ℝ) ^ 8
            * ((H : ℝ) ^ 6 / ((d : ℝ) * (g : ℝ)) + (H : ℝ) ^ 5 / (g : ℝ))) := h
      _ = 10 ^ 5 * (3 : ℝ) ^ d.primeFactors.card * ((m * d * g).divisors.card : ℝ) ^ 8
            * ((H : ℝ) ^ 6 / ((d : ℝ) * g) + (H : ℝ) ^ 5 / g) := by ring
  linarith

end Work.LinnikAreas
