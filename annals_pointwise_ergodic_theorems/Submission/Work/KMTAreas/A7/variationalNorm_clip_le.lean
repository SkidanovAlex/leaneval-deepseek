import Mathlib
import Submission.Work.Analysis.CzShift.Main
import Submission.Work.Analysis.CzShift.exists_isCZSeed_of_fourierInv
import Submission.Work.BourgainPlan.Maximal.main_narrow_taoSetS
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7

open scoped ENNReal NNReal
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-- Pushing the index set backwards along `n ↦ n - m` does not increase the variation part of
the variational norm (the `varPart`-half of
`Submission.PointwiseErgodicTheorems.variationalNorm_shiftDown_le`). -/
lemma varPart_sub_le (r : NNReal) (m : ℕ) (b : ℕ → ℂ) :
    varPart r (fun n => b (n - m)) ≤ varPart r b := by
  unfold varPart
  refine iSup_le (fun J => iSup_le (fun N => iSup_le (fun hN => ?_)))
  refine le_iSup_of_le J (le_iSup_of_le (fun i => N i - m) (le_iSup_of_le ?_ le_rfl))
  exact monotone_nat_of_le_succ (fun i => Nat.sub_le_sub_right (hN (Nat.le_succ i)) m)

/-- The supremum part of the variational norm of a sequence with `m` zeros prepended is bounded by
that of the original sequence. -/
lemma iSup_enorm_prependZeros_le (m : ℕ) (b : ℕ → ℂ) :
    (⨆ n, ‖(fun n : ℕ => if n < m then (0 : ℂ) else b (n - m)) n‖ₑ) ≤ ⨆ n, ‖b n‖ₑ := by
  refine iSup_le (fun n => ?_)
  by_cases h : n < m
  · simp [h]
  · simp only [h, if_false]
    exact le_iSup (fun n => ‖b n‖ₑ) (n - m)

/-- Prepending `m` zeros to a sequence (and shifting the rest back by `m`) at most doubles the
variational norm, for `r ≥ 1`.  The only new increment is the single jump `0 → b 0` at the
boundary, which costs at most the supremum part `⨆ n, ‖b n‖ₑ`, while a second copy of the
variational norm pays for the increments of `b`. -/
lemma variationalNorm_prependZeros_le_two (r : NNReal) (hr : 1 ≤ r) (m : ℕ) (b : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if n < m then 0 else b (n - m))
      ≤ PointwiseErgodicTheorems.variationalNorm r b
        + PointwiseErgodicTheorems.variationalNorm r b := by
  have hsplit : (fun n : ℕ => if n < m then (0 : ℂ) else b (n - m))
      = (fun n : ℕ => b (n - m)) + (fun n : ℕ => if n < m then (-(b 0)) else 0) := by
    funext n
    by_cases h : n < m
    · have h0 : n - m = 0 := Nat.sub_eq_zero_of_le h.le
      simp [h, h0]
    · simp [h]
  calc PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if n < m then 0 else b (n - m))
      = (⨆ n, ‖(fun n : ℕ => if n < m then (0 : ℂ) else b (n - m)) n‖ₑ)
          + varPart r (fun n : ℕ => if n < m then 0 else b (n - m)) :=
        variationalNorm_eq_add r _
    _ ≤ (⨆ n, ‖b n‖ₑ)
          + varPart r (fun n : ℕ => if n < m then 0 else b (n - m)) :=
        add_le_add (iSup_enorm_prependZeros_le m b) le_rfl
    _ = (⨆ n, ‖b n‖ₑ)
          + varPart r ((fun n : ℕ => b (n - m))
              + (fun n : ℕ => if n < m then (-(b 0)) else 0)) := by
        rw [hsplit]
    _ ≤ (⨆ n, ‖b n‖ₑ)
          + (varPart r (fun n : ℕ => b (n - m))
              + varPart r (fun n : ℕ => if n < m then (-(b 0)) else 0)) :=
        add_le_add le_rfl (varPart_add_le hr _ _)
    _ ≤ (⨆ n, ‖b n‖ₑ) + (varPart r b + ‖b 0‖ₑ) := by
        refine add_le_add le_rfl (add_le_add (varPart_sub_le r m b) ?_)
        simpa using varPart_step_le hr m (-(b 0))
    _ ≤ (⨆ n, ‖b n‖ₑ) + (varPart r b + (⨆ n, ‖b n‖ₑ)) :=
        add_le_add le_rfl (add_le_add le_rfl (le_iSup (fun n => ‖b n‖ₑ) 0))
    _ = PointwiseErgodicTheorems.variationalNorm r b + (⨆ n, ‖b n‖ₑ) := by
        rw [variationalNorm_eq_add r b]
        ac_rfl
    _ ≤ PointwiseErgodicTheorems.variationalNorm r b
          + PointwiseErgodicTheorems.variationalNorm r b := by
        refine add_le_add le_rfl ?_
        rw [variationalNorm_eq_add r b]
        exact le_self_add

theorem variationalNorm_clip_le (r : NNReal) (hr : 1 ≤ r) (u : ℕ → ℂ) (n₀ : ℕ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if n₀ ≤ n then u n else 0)
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun j : ℕ => u (j + n₀))
        + PointwiseErgodicTheorems.variationalNorm r (fun j : ℕ => u (j + n₀)) := by
  have hfun : (fun n : ℕ => if n₀ ≤ n then u n else 0)
      = (fun n : ℕ => if n < n₀ then 0 else (fun j : ℕ => u (j + n₀)) (n - n₀)) := by
    funext n
    by_cases h : n < n₀
    · have h' : ¬ n₀ ≤ n := by omega
      simp [h, h']
    · have h' : n₀ ≤ n := by omega
      simp [h, h', Nat.sub_add_cancel h']
  rw [hfun]
  exact variationalNorm_prependZeros_le_two r hr n₀ (fun j : ℕ => u (j + n₀))

end Work.KMTAreas.A7
