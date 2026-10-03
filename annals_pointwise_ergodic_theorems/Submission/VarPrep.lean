import ChallengeDeps
import Mathlib.Tactic
import Submission.VarNorm
import Submission.Variational

/-!
# Shifting and zero-padding a sequence; the `ℓ¹` bound for the `L^r` norm

This file contains the two elementary estimates used to compare the variational norm of a
sequence with that of a rescaled (`N ↦ N / 2^k`) version of itself:

* `norm_toLp_le_sum_norm`: the `L^r` norm of a finite vector is at most its `ℓ¹` norm;
* `variationalNorm_shiftDown_le`: the variational norm is unchanged when the index set is
  pushed to the right by the monotone map `n ↦ n - m` (it can only decrease);
* `variationalNorm_prependZeros_le`: filling the first `m` entries with zeros multiplies the
  variational norm by at most `3`.

The "prepend zeros" estimate is what allows one to apply a variational estimate for
`Λ`-lacunary sequences with `a n ≥ 1` to the rescaled sequences `n ↦ a n / 2^k`, whose values
are `< 1` for small `n`.
-/

set_option maxHeartbeats 1600000

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

/-- The `L^r` norm (`r ≥ 1`) of a finite vector is at most its `ℓ¹` norm. -/
lemma norm_toLp_le_sum_norm {r : ℝ≥0} (hr : 1 ≤ r) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℂ) :
    ‖WithLp.toLp r v‖ ≤ ∑ i, ‖v i‖ := by
  have : Fact (1 ≤ (↑r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  have hbasis : v = ∑ i, Pi.single (M := fun _ : ι => ℂ) i (v i) := by
    funext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; rw [Pi.single_eq_of_ne (Ne.symm hij)]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have h1 : WithLp.toLp r v
      = ∑ i : ι, WithLp.toLp r (Pi.single (M := fun _ : ι => ℂ) i (v i)) := by
    conv_lhs => rw [hbasis]
    rw [WithLp.toLp_sum]
  rw [h1]
  calc ‖∑ i : ι, WithLp.toLp r (Pi.single (M := fun _ : ι => ℂ) i (v i))‖
      ≤ ∑ i : ι, ‖WithLp.toLp r (Pi.single (M := fun _ : ι => ℂ) i (v i))‖ := norm_sum_le _ _
    _ = ∑ i : ι, ‖v i‖ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact PiLp.norm_single (↑r) (fun _ : ι => ℂ) i (v i)

/-- The variation part of the variational norm of a "step" sequence `n ↦ if n < m then z else 0`
is at most `‖z‖`. -/
lemma varPart_step_le {r : ℝ≥0} (hr : 1 ≤ r) (m : ℕ) (z : ℂ) :
    varPart r (fun n => if n < m then z else 0) ≤ ‖z‖ₑ := by
  have : Fact (1 ≤ (↑r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  refine iSup_le (fun J => iSup_le (fun N => iSup_le (fun hN => ?_)))
  set w : Fin J → ℂ :=
    fun i => (if N ((i : ℕ) + 1) < m then z else 0) - (if N (i : ℕ) < m then z else 0)
    with hw
  have hspec : ∀ i, w i ≠ 0 → N (i : ℕ) < m ∧ m ≤ N ((i : ℕ) + 1) := by
    intro i hi
    by_cases h1 : N (i : ℕ) < m
    · by_cases h2 : N ((i : ℕ) + 1) < m
      · exact absurd (by simp [hw, h1, h2]) hi
      · exact ⟨h1, le_of_not_gt h2⟩
    · have h1' : m ≤ N (i : ℕ) := le_of_not_gt h1
      have h2' : ¬ (N ((i : ℕ) + 1) < m) :=
        Nat.not_lt.mpr (le_trans h1' (hN (Nat.le_succ (i : ℕ))))
      exact absurd (by simp [hw, h1, h2']) hi
  have hwle : ∀ i, ‖w i‖ ≤ ‖z‖ := by
    intro i
    rcases lt_or_ge (N (i : ℕ)) m with h | h
    · rcases lt_or_ge (N ((i : ℕ) + 1)) m with h2 | h2
      · have : w i = 0 := by simp [hw, h, h2]
        rw [this]; simp
      · have : w i = -z := by simp [hw, h, h2]
        rw [this, norm_neg]
    · have h2 : ¬ (N ((i : ℕ) + 1) < m) :=
        Nat.not_lt.mpr (le_trans h (hN (Nat.le_succ (i : ℕ))))
      have : w i = 0 := by simp [hw, h, h2]
      rw [this]; simp
  have hcard : (Finset.univ.filter (fun i : Fin J => w i ≠ 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨ha1, ha2⟩ := hspec a ha
    obtain ⟨hb1, hb2⟩ := hspec b hb
    rcases le_total (a : ℕ) (b : ℕ) with h | h
    · rcases eq_or_lt_of_le h with heq | hlt
      · exact Fin.ext heq
      · exfalso
        have : N ((a : ℕ) + 1) ≤ N (b : ℕ) := hN (by omega)
        omega
    · rcases eq_or_lt_of_le h with heq | hlt
      · exact Fin.ext heq.symm
      · exfalso
        have : N ((b : ℕ) + 1) ≤ N (a : ℕ) := hN (by omega)
        omega
  have hsum : ∑ i : Fin J, ‖w i‖ ≤ ‖z‖ := by
    have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin J => w i ≠ 0), ‖w i‖ = ∑ i : Fin J, ‖w i‖ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : w i ≠ 0
      · simp [h]
      · rw [if_neg h, not_not.mp h]; simp
    rw [← h1]
    calc ∑ i ∈ Finset.univ.filter (fun i : Fin J => w i ≠ 0), ‖w i‖
        ≤ ∑ _i ∈ Finset.univ.filter (fun i : Fin J => w i ≠ 0), ‖z‖ :=
          Finset.sum_le_sum (fun i _ => hwle i)
      _ = ((Finset.univ.filter (fun i : Fin J => w i ≠ 0)).card : ℝ) * ‖z‖ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * ‖z‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg z)
          exact_mod_cast hcard
      _ = ‖z‖ := one_mul _
  calc ENNReal.ofReal ‖WithLp.toLp r w‖
      ≤ ENNReal.ofReal (∑ i : Fin J, ‖w i‖) := ENNReal.ofReal_le_ofReal (norm_toLp_le_sum_norm hr w)
    _ ≤ ENNReal.ofReal ‖z‖ := ENNReal.ofReal_le_ofReal hsum
    _ = ‖z‖ₑ := ofReal_norm z

/-- The variational norm of a "step" sequence `n ↦ if n < m then z else 0` is at most `2‖z‖`. -/
lemma variationalNorm_step_le {r : ℝ≥0} (hr : 1 ≤ r) (m : ℕ) (z : ℂ) :
    variationalNorm r (fun n => if n < m then z else 0) ≤ 2 * ‖z‖ₑ := by
  rw [variationalNorm_eq_add]
  have hsup : (⨆ n, ‖(fun n => if n < m then z else 0) n‖ₑ) ≤ ‖z‖ₑ := by
    refine iSup_le (fun n => ?_)
    by_cases h : n < m <;> simp [h]
  rw [two_mul]
  exact add_le_add hsup (varPart_step_le hr m z)

/-- Pushing the index set to the right along `n ↦ n - m` does not increase the variational norm. -/
lemma variationalNorm_shiftDown_le {r : ℝ≥0} (m : ℕ) (b : ℕ → ℂ) :
    variationalNorm r (fun n => b (n - m)) ≤ variationalNorm r b := by
  rw [variationalNorm_eq_add, variationalNorm_eq_add]
  refine add_le_add ?_ ?_
  · refine iSup_le (fun n => le_iSup (fun n => ‖b n‖ₑ) (n - m))
  · refine iSup_le (fun J => iSup_le (fun N => iSup_le (fun hN => ?_)))
    refine le_iSup_of_le J (le_iSup_of_le (fun i => N i - m) (le_iSup_of_le ?_ le_rfl))
    exact monotone_nat_of_le_succ (fun i => Nat.sub_le_sub_right (hN (Nat.le_succ i)) m)

/-- Filling the first `m` entries of a sequence with zeros multiplies the variational norm by at
most `3`. -/
lemma variationalNorm_prependZeros_le {r : ℝ≥0} (hr : 1 ≤ r) (m : ℕ) (b : ℕ → ℂ) :
    variationalNorm r (fun n => if n < m then 0 else b (n - m)) ≤ 3 * variationalNorm r b := by
  have hdecomp : (fun n => if n < m then (0 : ℂ) else b (n - m))
      = (fun n => b (n - m)) - (fun n => if n < m then b 0 else 0) := by
    funext n
    rw [Pi.sub_apply]
    by_cases h : n < m
    · simp only [if_pos h]
      rw [Nat.sub_eq_zero_of_le h.le]
      simp
    · simp only [if_neg h]
      simp
  have hneg : variationalNorm r (-(fun n => if n < m then b 0 else 0))
      = variationalNorm r (fun n => if n < m then b 0 else 0) := by
    have h := variationalNorm_smul (r := r) hr (-1 : ℂ) (fun n => if n < m then b 0 else 0)
    rw [neg_one_smul] at h
    simpa using h
  calc variationalNorm r (fun n => if n < m then (0 : ℂ) else b (n - m))
      = variationalNorm r ((fun n => b (n - m)) + -(fun n => if n < m then b 0 else 0)) := by
        rw [hdecomp, sub_eq_add_neg]
    _ ≤ variationalNorm r (fun n => b (n - m))
          + variationalNorm r (-(fun n => if n < m then b 0 else 0)) :=
        variationalNorm_add_le hr _ _
    _ = variationalNorm r (fun n => b (n - m))
          + variationalNorm r (fun n => if n < m then b 0 else 0) := by rw [hneg]
    _ ≤ variationalNorm r b + 2 * ‖b 0‖ₑ :=
        add_le_add (variationalNorm_shiftDown_le m b) (variationalNorm_step_le hr m (b 0))
    _ ≤ variationalNorm r b + 2 * variationalNorm r b :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_variationalNorm r b 0)
          (show (0 : ℝ≥0∞) ≤ 2 by norm_num))
    _ = 3 * variationalNorm r b := by ring

end PointwiseErgodicTheorems
end Submission
