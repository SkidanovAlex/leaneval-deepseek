/-
# Every chain sum is dominated by the variational norm

**Brick of step 2 of the `(lin-1)`/`(lin-2)` proof** (see
`NOTES_MdlWindowLift_CORRECTED_BAND.md` §6): the vector-valued sampling comparison needs the fact
that *each* finite chain of increments contributes at most the variational norm of the sequence.

The challenge's `variationalNorm` (`ChallengeDeps.lean`) is, by
`Work.KMTAreas.A7Hi.variationalNorm_eq_sup_add_varPart`,
`(⨆ n, ‖a n‖ₑ) + varPart r a`, where
`varPart r a = ⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N), ofReal ‖WithLp.toLp r (fun i : Fin J =>
a (N (i+1)) - a (N i))‖` — i.e. the supremum over *monotone `ℕ`-chains*.  The `VrLiftDataP` datum
of the §8 packets, on the other hand, quantifies over monotone chains `Fin (J+1) → ℕ`.  This file
bridges the two: every monotone `Fin (J+1)`-chain sum is `≤ variationalNorm r a`, by extending the
chain to an `ℕ`-chain (`N i := k (min i J)`), which reproduces all `J` jumps exactly.

`PiLp.norm_eq_sum` identifies the `WithLp` norm with `(∑ i, ‖v i‖ ^ r.toReal) ^ (1 / r.toReal)`,
which is the form in which the estimates are stated.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Hi.VarPartDefs
import Submission.Work.Analysis.Variation.variationalNorm_eq_iSup_VrFull

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTPlan.A6Clean

open MeasureTheory Finset
open scoped BigOperators ENNReal NNReal

/-- **Every monotone `Fin (J+1)`-chain sum is at most the variational norm.** -/
theorem ofReal_chain_sum_le_variationalNorm {r : NNReal} (hr : 1 ≤ r) {J : ℕ}
    (k : Fin (J + 1) → ℕ) (hk : Monotone k) (a : ℕ → ℂ) :
    ENNReal.ofReal ((∑ i : Fin J, ‖a (k i.succ) - a (k i.castSucc)‖ ^ (r : ℝ))
        ^ (1 / (r : ℝ)))
      ≤ PointwiseErgodicTheorems.variationalNorm r a := by
  classical
  -- the `ℕ`-chain extending `k`
  set N : ℕ → ℕ := fun i => k ⟨min i J, Nat.lt_succ_of_le (Nat.min_le_right i J)⟩ with hN
  have hNmono : Monotone N := by
    intro i j hij
    refine hk ?_
    rw [Fin.le_def]
    simp only [hN]
    omega
  -- the two index identifications
  have hidx₁ : ∀ i : Fin J, N (i : ℕ) = k i.castSucc := by
    intro i
    show k ⟨min (i : ℕ) J, _⟩ = k i.castSucc
    congr 1
    exact Fin.ext (by simp [Nat.min_eq_left i.isLt.le])
  have hidx₂ : ∀ i : Fin J, N ((i : ℕ) + 1) = k i.succ := by
    intro i
    show k ⟨min ((i : ℕ) + 1) J, _⟩ = k i.succ
    congr 1
    exact Fin.ext (by
      simp only [Fin.val_succ]
      exact Nat.min_eq_left (by omega))
  -- the `varPart` term of this chain
  have hle : ENNReal.ofReal ‖(WithLp.toLp r
      (fun i : Fin J => a (N ((i : ℕ) + 1)) - a (N (i : ℕ))) :
        WithLp r (Fin J → ℂ))‖ ≤ Work.KMTAreas.A7Hi.varPart r a :=
    le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hNmono le_rfl))
  -- identify the two norms
  have hfun : (fun i : Fin J => a (N ((i : ℕ) + 1)) - a (N (i : ℕ)))
      = fun i : Fin J => a (k i.succ) - a (k i.castSucc) := by
    funext i
    rw [hidx₁ i, hidx₂ i]
  rw [hfun] at hle
  -- the `WithLp` norm as a sum
  have hrpos : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hr)
  have hrp : (0 : ℝ) < (r : ℝ≥0∞).toReal := by
    simpa using hrpos
  have hnorm : ‖(WithLp.toLp r (fun i : Fin J => a (k i.succ) - a (k i.castSucc)) :
        WithLp r (Fin J → ℂ))‖
      = (∑ i : Fin J, ‖a (k i.succ) - a (k i.castSucc)‖ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
    rw [PiLp.norm_eq_sum hrp]
    rw [ENNReal.coe_toReal]
  rw [hnorm] at hle
  exact le_trans hle (Work.KMTAreas.A7Hi.varPart_le_variationalNorm r a)

/-- **The squared form**: every monotone `Fin (J+1)`-chain sum of squared increments is at most the
square of the variational norm.  This is the form used by the `ℓ²`-valued estimates. -/
theorem chain_sum_sq_le_variationalNorm {J : ℕ}
    (k : Fin (J + 1) → ℕ) (hk : Monotone k) (a : ℕ → ℂ) :
    (∑ i : Fin J, ‖a (k i.succ) - a (k i.castSucc)‖ₑ ^ (2 : ℕ))
      ≤ (PointwiseErgodicTheorems.variationalNorm (2 : NNReal) a) ^ (2 : ℕ) := by
  have h := ofReal_chain_sum_le_variationalNorm (r := 2) (by norm_num) k hk a
  have hnn : (0 : ℝ) ≤ (∑ i : Fin J, ‖a (k i.succ) - a (k i.castSucc)‖ ^ (2 : ℝ))
      ^ (1 / (2 : ℝ)) :=
    Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _
  have hsq : (ENNReal.ofReal ((∑ i : Fin J,
        ‖a (k i.succ) - a (k i.castSucc)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)))) ^ (2 : ℕ)
      ≤ (PointwiseErgodicTheorems.variationalNorm (2 : NNReal) a) ^ (2 : ℕ) := by
    calc (ENNReal.ofReal ((∑ i : Fin J,
          ‖a (k i.succ) - a (k i.castSucc)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)))) ^ (2 : ℕ)
        = ENNReal.ofReal ((∑ i : Fin J, ‖a (k i.succ) - a (k i.castSucc)‖ ^ (2 : ℝ))
            ^ (1 / (2 : ℝ))) * ENNReal.ofReal ((∑ i : Fin J,
              ‖a (k i.succ) - a (k i.castSucc)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) := by
          rw [pow_two]
      _ ≤ ENNReal.ofReal ((∑ i : Fin J, ‖a (k i.succ) - a (k i.castSucc)‖ ^ (2 : ℝ))
            ^ (1 / (2 : ℝ))) * PointwiseErgodicTheorems.variationalNorm (2 : NNReal) a :=
          mul_le_mul' le_rfl h
      _ ≤ PointwiseErgodicTheorems.variationalNorm (2 : NNReal) a
            * PointwiseErgodicTheorems.variationalNorm (2 : NNReal) a := mul_le_mul' h le_rfl
      _ = (PointwiseErgodicTheorems.variationalNorm (2 : NNReal) a) ^ (2 : ℕ) := by rw [pow_two]
  rw [← ENNReal.ofReal_pow hnn] at hsq
  -- the real identity `(S ^ (1/2)) ^ 2 = S`
  have hreal : ((∑ i : Fin J, ‖a (k i.succ) - a (k i.castSucc)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2
      = ∑ i : Fin J, ‖a (k i.succ) - a (k i.castSucc)‖ ^ (2 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _)]
    norm_num
  rw [hreal] at hsq
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)] at hsq
  have hconv : (∑ i : Fin J, ENNReal.ofReal (‖a (k i.succ) - a (k i.castSucc)‖ ^ (2 : ℝ)))
      = ∑ i : Fin J, ‖a (k i.succ) - a (k i.castSucc)‖ₑ ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc ENNReal.ofReal (‖a (k i.succ) - a (k i.castSucc)‖ ^ (2 : ℝ))
        = (ENNReal.ofReal ‖a (k i.succ) - a (k i.castSucc)‖) ^ (2 : ℝ) :=
          (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).symm
      _ = (‖a (k i.succ) - a (k i.castSucc)‖ₑ) ^ (2 : ℝ) := by
          rw [ofReal_norm _]
      _ = ‖a (k i.succ) - a (k i.castSucc)‖ₑ ^ (2 : ℕ) := ENNReal.rpow_natCast _ 2
  rw [hconv] at hsq
  exact hsq

end Work.KMTPlan.A6Clean
