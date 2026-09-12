import Submission.SqueezeCore
import Submission.SqzTwoD
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-! # Child task: d-fold averages of the single-coordinate and pair sums.

Prove the four lemmas below (mirrors of `Submission.SqueezeCore`'s
`integrable_pairLog`, `integral_sum_coordLog`, `integral_pairLog_eq`,
`integral_totalLog_eq`, `integral_totalLog_ge`).  Add helper lemmas **in this
file**, namespace `Submission.SqzAvg`.  All definitions needed
(`pserre`, `coordLog`, `pairLog`, `totalLog`, `muSerre`, `energy`) live in
`Submission.SqueezeCore` / `Submission.EnergyHalf` (opened below).

Available machinery (in `Submission.SqueezeCore`):
* `pserre d = Measure.pi (fun _ : Fin d => muSerre)`, a probability measure;
* single-coordinate marginal & integrability:
  `integral_comp_eval_mu`, `integrable_comp_eval_mu`;
* pair marginal & integrability (from the pair-projection machinery):
  `integral_pair_marginal {i j : Fin d} (hij : i ≠ j) (hg : Integrable ...)`,
  `integrable_pair_marginal`;
* 1D facts: `integrable_log_abs_aeval R hR` (integrable `log|aeval · R|`),
  `integrable_const_mul_log_weight`, `integral_log_weight n`
  (`∫ n·log w = n·energy`),
  `integral_log_sub_eq_neg_potential` (pointwise, `∫_y log|x−y|dμ = −U(x)`);
* 2D kernel value (axiom-free, `Submission.SqzTwoD`): `integrable_prod_log_sub`,
  `integral_prod_log_sub_energy` (`∫∫ log|u−v| = −energy`).
-/

noncomputable section

open MeasureTheory Polynomial
open scoped Real BigOperators ENNReal Topology

namespace Submission.SqzAvg

open Submission.SqueezeCore
open Submission.Contracts
open Submission.SerreExample
open Submission.EnergyHalf

/-! ## 1D integrability / value of `coordLog` -/

/-- `coordLog n R` is integrable against `muSerre`. -/
lemma integrable_coordLog_1d {n : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0) :
    Integrable (fun x : ℝ => coordLog n R x) muSerre := by
  unfold coordLog
  exact (integrable_log_abs_aeval R hR).add (integrable_const_mul_log_weight n)

/-- integral of `coordLog` = integral of `log |R|` + `n · energy`. -/
lemma integral_coordLog {n : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0) :
    (∫ x : ℝ, coordLog n R x ∂muSerre) =
      (∫ x : ℝ, Real.log (|Polynomial.aeval x R|) ∂muSerre) + (n : ℝ) * energy := by
  unfold coordLog
  rw [MeasureTheory.integral_add]
  · rw [integral_log_weight n]
  · exact integrable_log_abs_aeval R hR
  · exact integrable_const_mul_log_weight n

/-! ## Pair terms: integrability on the product -/

/-- A single pair term `log |x_i − x_j|` is integrable over `pserre d`. -/
lemma integrable_pairLogTerm {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    Integrable (fun x : Fin d → ℝ => Real.log (|x i - x j|)) (pserre d) := by
  exact integrable_pair_marginal hij (g := fun u v : ℝ => Real.log (|u - v|))
    (Submission.SqzTwoD.integrable_prod_log_sub)

/-- its integral is `-energy`. -/
lemma integral_pairLogTerm {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    (∫ x : Fin d → ℝ, Real.log (|x i - x j|) ∂pserre d) = -energy := by
  calc
    (∫ x : Fin d → ℝ, Real.log (|x i - x j|) ∂pserre d)
        = ∫ p : ℝ × ℝ, Real.log (|p.1 - p.2|) ∂(muSerre.prod muSerre) := by
          exact integral_pair_marginal hij (g := fun u v : ℝ => Real.log (|u - v|))
            (Submission.SqzTwoD.integrable_prod_log_sub)
    _ = -energy := Submission.SqzTwoD.integral_prod_log_sub_energy

/-! ## Counting the pairs `i < j` in `Fin d` -/

/-- `Finset.Ioi i` is the filter of indices above `i`. -/
lemma filter_Ioi (d : ℕ) (i : Fin d) :
    (Finset.univ.filter (fun j : Fin d => i < j)) = Finset.Ioi i := by
  ext x
  simp

/-- `∑_{i : Fin d} i.val = d·(d−1)/2` (real-valued). -/
lemma sum_val_fin (d : ℕ) :
    (∑ i : Fin d, ((i : ℕ) : ℝ)) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Fin.sum_univ_castSucc]
      simp [Fin.val_castSucc, ih, Fin.val_last]
      ring

/-- the number of indices above `i` is `d − 1 − i.val` (cast to real). -/
lemma card_Ioi_cast_real {d : ℕ} (i : Fin d) :
    (((Finset.Ioi i).card : ℕ) : ℝ) = (d : ℝ) - 1 - ((i : ℕ) : ℝ) := by
  by_cases hd : d = 0
  · subst d
    exfalso
    exact (Nat.not_lt_zero i.val) i.isLt
  · have h1 : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd)
    have hi : (i : ℕ) ≤ d - 1 := Nat.le_sub_one_of_lt i.isLt
    have hdcast : (((d - 1 : ℕ) : ℝ)) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub h1]
      simp
    calc
      (((Finset.Ioi i).card : ℕ) : ℝ) = (((d - 1 - (i : ℕ)) : ℕ) : ℝ) := by
        congr 1
        exact Fin.card_Ioi i
      _ = ((d - 1 : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by
        rw [Nat.cast_sub hi]
      _ = (d : ℝ) - 1 - ((i : ℕ) : ℝ) := by
        rw [hdcast]

/-- `∑_i #{j | i < j} = d·(d−1)/2` (real). -/
lemma pairCard_sum_real (d : ℕ) :
    (∑ i : Fin d, (((Finset.Ioi i).card : ℕ) : ℝ)) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  calc
    (∑ i : Fin d, (((Finset.Ioi i).card : ℕ) : ℝ))
        = ∑ i : Fin d, ((d : ℝ) - 1 - ((i : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact card_Ioi_cast_real i
    _ = (∑ i : Fin d, ((d : ℝ) - 1)) - (∑ i : Fin d, ((i : ℕ) : ℝ)) := by
          rw [Finset.sum_sub_distrib]
    _ = (d : ℝ) * ((d : ℝ) - 1) - (∑ i : Fin d, ((i : ℕ) : ℝ)) := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul, Fintype.card_fin]
    _ = (d : ℝ) * ((d : ℝ) - 1) - (d : ℝ) * ((d : ℝ) - 1) / 2 := by
          rw [sum_val_fin d]
    _ = (d : ℝ) * ((d : ℝ) - 1) / 2 := by ring

/-- A constant summed over all strict pairs `i < j` of `Fin d`. -/
lemma pair_double_sum_const {d : ℕ} (c : ℝ) :
    (∑ i : Fin d, ∑ _j ∈ (Finset.univ.filter (fun j : Fin d => i < j)), c) =
      ((d : ℝ) * ((d : ℝ) - 1) / 2) * c := by
  calc
    (∑ i : Fin d, ∑ j ∈ (Finset.univ.filter (fun j : Fin d => i < j)), c)
        = ∑ i : Fin d, ((((Finset.univ.filter (fun j : Fin d => i < j)).card) : ℕ) : ℝ) * c := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
    _ = (∑ i : Fin d, ((((Finset.univ.filter (fun j : Fin d => i < j)).card) : ℕ) : ℝ)) * c := by
          rw [Finset.sum_mul]
    _ = (∑ i : Fin d, (((Finset.Ioi i).card : ℕ) : ℝ)) * c := by
          apply congrArg (fun t : ℝ => t * c)
          apply Finset.sum_congr rfl
          intro i _
          rw [filter_Ioi d i]
    _ = ((d : ℝ) * ((d : ℝ) - 1) / 2) * c := by
          rw [pairCard_sum_real d]

/-! ## Main five lemmas -/

lemma integrable_pairLog {d : ℕ} :
    Integrable (fun x : Fin d → ℝ => pairLog d x) (pserre d) := by
  classical
  unfold pairLog
  apply MeasureTheory.integrable_finsetSum
  intro i _
  apply MeasureTheory.integrable_finsetSum
  intro j hj
  exact integrable_pairLogTerm (ne_of_lt ((Finset.mem_filter.mp hj).2))

lemma integral_sum_coordLog {d n : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0) :
    (∫ x : Fin d → ℝ, (∑ k : Fin d, coordLog n R (x k)) ∂pserre d) =
      (d : ℝ) * (∫ x : ℝ, coordLog n R x ∂muSerre) := by
  classical
  calc
    (∫ x : Fin d → ℝ, (∑ k : Fin d, coordLog n R (x k)) ∂pserre d)
        = ∑ k : Fin d, (∫ x : Fin d → ℝ, coordLog n R (x k) ∂pserre d) := by
          rw [MeasureTheory.integral_finsetSum]
          intro k _
          exact integrable_comp_eval_mu k (coordLog n R) (integrable_coordLog_1d R hR)
    _ = ∑ k : Fin d, (∫ x : ℝ, coordLog n R x ∂muSerre) := by
          apply Finset.sum_congr rfl
          intro k _
          exact integral_comp_eval_mu k (coordLog n R) (integrable_coordLog_1d R hR)
    _ = (d : ℝ) * (∫ x : ℝ, coordLog n R x ∂muSerre) := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul, Fintype.card_fin]

lemma integral_pairLog_eq {d : ℕ} :
    (∫ x : Fin d → ℝ, pairLog d x ∂pserre d) =
      ((d : ℝ) * (d - 1) / 2) * (-energy) := by
  classical
  unfold pairLog
  calc
    (∫ x : Fin d → ℝ, (∑ i : Fin d,
          ∑ j ∈ (Finset.univ.filter (fun j : Fin d => i < j)), Real.log (|x i - x j|)) ∂pserre d)
        = ∑ i : Fin d, (∫ x : Fin d → ℝ,
              (∑ j ∈ (Finset.univ.filter (fun j : Fin d => i < j)), Real.log (|x i - x j|)) ∂pserre d) := by
          rw [MeasureTheory.integral_finsetSum]
          intro i _
          apply MeasureTheory.integrable_finsetSum
          intro j hj
          exact integrable_pairLogTerm (ne_of_lt ((Finset.mem_filter.mp hj).2))
    _ = ∑ i : Fin d, ∑ j ∈ (Finset.univ.filter (fun j : Fin d => i < j)),
          (∫ x : Fin d → ℝ, Real.log (|x i - x j|) ∂pserre d) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [MeasureTheory.integral_finsetSum]
          intro j hj
          exact integrable_pairLogTerm (ne_of_lt ((Finset.mem_filter.mp hj).2))
    _ = ∑ i : Fin d, ∑ j ∈ (Finset.univ.filter (fun j : Fin d => i < j)), (-energy) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j hj
          exact integral_pairLogTerm (ne_of_lt ((Finset.mem_filter.mp hj).2))
    _ = ((d : ℝ) * (d - 1) / 2) * (-energy) := by
          exact pair_double_sum_const (-energy)

lemma integral_totalLog_eq {d n : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0) :
    (∫ x : Fin d → ℝ, totalLog d n R x ∂pserre d) =
      (d : ℝ) * (∫ x : ℝ, coordLog n R x ∂muSerre) +
        ((d : ℝ) * (d - 1) / 2) * (-energy) := by
  calc
    (∫ x : Fin d → ℝ, totalLog d n R x ∂pserre d)
        = (∫ x : Fin d → ℝ,
            ((∑ k : Fin d, coordLog n R (x k)) + pairLog d x) ∂pserre d) := by
          rfl
    _ = (∫ x : Fin d → ℝ, (∑ k : Fin d, coordLog n R (x k)) ∂pserre d) +
        (∫ x : Fin d → ℝ, pairLog d x ∂pserre d) := by
          rw [MeasureTheory.integral_add]
          · apply MeasureTheory.integrable_finsetSum
            intro k _
            exact integrable_comp_eval_mu k (coordLog n R) (integrable_coordLog_1d R hR)
          · exact integrable_pairLog
    _ = (d : ℝ) * (∫ x : ℝ, coordLog n R x ∂muSerre) +
        ((d : ℝ) * (d - 1) / 2) * (-energy) := by
          rw [integral_sum_coordLog R hR]
          rw [integral_pairLog_eq]

lemma integral_totalLog_ge {d n : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0)
    (hRint : 0 ≤ ∫ x : ℝ, Real.log (|Polynomial.aeval x R|) ∂muSerre) :
    ((d : ℝ) * (n : ℝ) - (d : ℝ) * (d - 1) / 2) * energy ≤
      (∫ x : Fin d → ℝ, totalLog d n R x ∂pserre d) := by
  rw [integral_totalLog_eq (d := d) (n := n) R hR]
  rw [integral_coordLog (n := n) R hR]
  have hd0 : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hnonneg : 0 ≤ (d : ℝ) *
      (∫ x : ℝ, Real.log (|Polynomial.aeval x R|) ∂muSerre) :=
    mul_nonneg hd0 hRint
  nlinarith

end Submission.SqzAvg
