/-
Structural facts about Descartes quadruples in the Apollonian orbit of (-3,5,8,8):
  * every orbit quadruple has positive coordinate sum (and satisfies Descartes);
  * at most one coordinate of any Descartes quadruple with positive sum is negative.
-/
import Submission.Apollo.Descartes
import Submission.Apollo.Mod24
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped Pointwise
open LocalGlobalApollonianCirclePackings
namespace Apollo

/-- 4|x| < 3S from a Descartes-style bound 16x² ≤ 8S², S > 0. -/
lemma four_lt_three {x S : ℤ} (hS : 0 < S) (h : 16 * x ^ 2 ≤ 8 * S ^ 2) : 4 * x < 3 * S := by
  have h4 : (4 * x) ^ 2 < (3 * S) ^ 2 := by
    calc
      (4 * x) ^ 2 = 16 * x ^ 2 := by ring
      _ ≤ 8 * S ^ 2 := h
      _ < 9 * S ^ 2 := by nlinarith [hS]
      _ = (3 * S) ^ 2 := by ring
  have habs : |4 * x| < |3 * S| := sq_lt_sq.mp h4
  have h3pos : 0 < 3 * S := by nlinarith [hS]
  have hp := (abs_lt.mp habs).2
  simpa [abs_of_pos h3pos] using hp

/-- 8S² = 16Σ in a Descartes quadruple. -/
lemma desc_sq_sum (v : Fin 4 → ℤ)
    (hD : (∑ j : Fin 4, v j) ^ 2 = 2 * ∑ j : Fin 4, (v j) ^ 2) :
    8 * (∑ j : Fin 4, v j) ^ 2 = 16 * ∑ j : Fin 4, (v j) ^ 2 := by
  rw [hD]
  ring

/-- a single coordinate's square is at most the sum of squares. -/
lemma single_sq_le_sum (v : Fin 4 → ℤ) (i : Fin 4) :
    16 * (v i) ^ 2 ≤ 16 * (∑ j : Fin 4, (v j) ^ 2) := by
  rw [Fin.sum_univ_four]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]

/-- coordinate squared bound in a Descartes quadruple. -/
lemma coord_sq_le (v : Fin 4 → ℤ) (i : Fin 4)
    (hD : (∑ j : Fin 4, v j) ^ 2 = 2 * ∑ j : Fin 4, (v j) ^ 2) :
    16 * (v i) ^ 2 ≤ 8 * (∑ j : Fin 4, v j) ^ 2 := by
  rw [desc_sq_sum v hD]
  exact single_sq_le_sum v i

/-- S-move preserves the positivity of the sum in a Descartes quadruple. -/
lemma sum_gt_zero_of_descarates_and_possum (v : Fin 4 → ℤ)
    (hD : (∑ i : Fin 4, v i) ^ 2 = 2 * ∑ i : Fin 4, (v i) ^ 2)
    (hS : 0 < ∑ i : Fin 4, v i) (i : Fin 4) :
    0 < ∑ j : Fin 4, (gen i • v) j := by
  have hS' : (∑ j : Fin 4, (gen i • v) j) = 3 * (∑ j : Fin 4, v j) - 4 * (v i) := by
    rw [Fin.sum_univ_four] at hD ⊢
    fin_cases i <;> simp [gen, Matrix.mulVec_eq_sum, Fin.sum_univ_four] <;> ring
  rw [hS']
  have h4lt : 4 * v i < 3 * (∑ j : Fin 4, v j) :=
    four_lt_three hS (coord_sq_le v i hD)
  linarith

/-- S-move preserves the positivity of the sum (helper, Descartes in scope). -/
lemma pos_sum_of_pos_sum_move (v : Fin 4 → ℤ) (i : Fin 4)
    (hD : (∑ j : Fin 4, v j) ^ 2 = 2 * ∑ j : Fin 4, (v j) ^ 2)
    (hS : 0 < ∑ j : Fin 4, v j) : 0 < ∑ j : Fin 4, (gen i • v) j :=
  sum_gt_zero_of_descarates_and_possum v hD hS i

/-- Two-negative impossibility, part 1: three simultaneous negatives. -/
lemma not_three_neg {a b c d : ℤ} (hD : (a + b + c + d) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2))
    (hS : 0 < a + b + c + d) (ha : a < 0) (hb : b < 0) (hc : c < 0) : False := by
  have hd0 : 0 < d := by omega
  have hlt : (a + b + c + d) ^ 2 < 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    have hSd : a + b + c + d < d := by omega
    have hS2 : (a + b + c + d) ^ 2 < d ^ 2 := by
      have hnn : 0 ≤ a + b + c + d := le_of_lt hS
      exact sq_lt_sq.mpr (by simp [abs_of_nonneg hnn, abs_of_pos hd0]; linarith)
    nlinarith [hS2, sq_nonneg a, sq_nonneg b, sq_nonneg c]
  nlinarith

/-- Two-negative impossibility, part 2: exactly two negatives, others nonnegative. -/
lemma not_two_neg {a b c d : ℤ} (hD : (a + b + c + d) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2))
    (hS : 0 < a + b + c + d) (ha : a < 0) (hb : b < 0) (hc : 0 ≤ c) (hd : 0 ≤ d) : False := by
  let A : ℤ := -a
  let B : ℤ := -b
  have hA : 0 < A := by omega
  have hB : 0 < B := by omega
  have hDa : a = -A := by omega
  have hDb : b = -B := by omega
  have hcd : 0 < c + d := by omega
  have hsum : 0 < (c + d) * (A + B) := mul_pos hcd (by linarith)
  have hD2 : (c - d) ^ 2 + (A - B) ^ 2 + 2 * (c + d) * (A + B) = 0 := by
    rw [hDa, hDb] at hD
    ring_nf at hD
    nlinarith
  have hgt : 0 < (c - d) ^ 2 + (A - B) ^ 2 + 2 * (c + d) * (A + B) := by
    nlinarith [sq_nonneg (c - d), sq_nonneg (A - B), hsum]
  nlinarith

/-- Pair of negative coordinates at positions 0,1 is impossible. -/
lemma neg_pair_01 (v : Fin 4 → ℤ)
    (hD : (∑ i : Fin 4, v i) ^ 2 = 2 * ∑ i : Fin 4, (v i) ^ 2)
    (hS : 0 < ∑ i : Fin 4, v i) (h_0 : v 0 < 0) (h_1 : v 1 < 0) : False := by
  simp [Fin.sum_univ_four] at hD hS
  by_cases h2 : v 2 < 0
  · exfalso
    have hD_re : (v 0 + v 2 + v 1 + v 3) ^ 2 = 2 * ((v 0) ^ 2 + (v 2) ^ 2 + (v 1) ^ 2 + (v 3) ^ 2) := by
      simpa [add_assoc, add_comm, add_left_comm] using hD
    have hS_re : 0 < (v 0 + v 2 + v 1 + v 3) := by omega
    exact not_three_neg hD_re hS_re h_0 h2 h_1
  · have h20 : 0 ≤ v 2 := le_of_not_gt h2
    by_cases h3 : v 3 < 0
    · exfalso
      have hD_re : (v 0 + v 1 + v 3 + v 2) ^ 2 = 2 * ((v 0) ^ 2 + (v 1) ^ 2 + (v 3) ^ 2 + (v 2) ^ 2) := by
        simpa [add_assoc, add_comm, add_left_comm] using hD
      have hS_re : 0 < (v 0 + v 1 + v 3 + v 2) := by omega
      exact not_three_neg hD_re hS_re h_0 h_1 h3
    · have h30 : 0 ≤ v 3 := le_of_not_gt h3
      exfalso
      have hD_re : (v 0 + v 1 + v 2 + v 3) ^ 2 = 2 * ((v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) := by
        simpa [add_assoc, add_comm, add_left_comm] using hD
      have hS_re : 0 < (v 0 + v 1 + v 2 + v 3) := by omega
      exact not_two_neg hD_re hS_re h_0 h_1 h20 h30
/-- Pair of negative coordinates at positions 0,2 is impossible. -/
lemma neg_pair_02 (v : Fin 4 → ℤ)
    (hD : (∑ i : Fin 4, v i) ^ 2 = 2 * ∑ i : Fin 4, (v i) ^ 2)
    (hS : 0 < ∑ i : Fin 4, v i) (h_0 : v 0 < 0) (h_2 : v 2 < 0) : False := by
  simp [Fin.sum_univ_four] at hD hS
  by_cases h1 : v 1 < 0
  · exfalso
    have hD_re : (v 0 + v 1 + v 2 + v 3) ^ 2 = 2 * ((v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) := by
      simpa [add_assoc, add_comm, add_left_comm] using hD
    have hS_re : 0 < (v 0 + v 1 + v 2 + v 3) := by omega
    exact not_three_neg hD_re hS_re h_0 h1 h_2
  · have h10 : 0 ≤ v 1 := le_of_not_gt h1
    by_cases h3 : v 3 < 0
    · exfalso
      have hD_re : (v 0 + v 2 + v 3 + v 1) ^ 2 = 2 * ((v 0) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 + (v 1) ^ 2) := by
        simpa [add_assoc, add_comm, add_left_comm] using hD
      have hS_re : 0 < (v 0 + v 2 + v 3 + v 1) := by omega
      exact not_three_neg hD_re hS_re h_0 h_2 h3
    · have h30 : 0 ≤ v 3 := le_of_not_gt h3
      exfalso
      have hD_re : (v 0 + v 2 + v 1 + v 3) ^ 2 = 2 * ((v 0) ^ 2 + (v 2) ^ 2 + (v 1) ^ 2 + (v 3) ^ 2) := by
        simpa [add_assoc, add_comm, add_left_comm] using hD
      have hS_re : 0 < (v 0 + v 2 + v 1 + v 3) := by omega
      exact not_two_neg hD_re hS_re h_0 h_2 h10 h30
/-- Pair of negative coordinates at positions 0,3 is impossible. -/
lemma neg_pair_03 (v : Fin 4 → ℤ)
    (hD : (∑ i : Fin 4, v i) ^ 2 = 2 * ∑ i : Fin 4, (v i) ^ 2)
    (hS : 0 < ∑ i : Fin 4, v i) (h_0 : v 0 < 0) (h_3 : v 3 < 0) : False := by
  simp [Fin.sum_univ_four] at hD hS
  by_cases h1 : v 1 < 0
  · exfalso
    have hD_re : (v 0 + v 1 + v 3 + v 2) ^ 2 = 2 * ((v 0) ^ 2 + (v 1) ^ 2 + (v 3) ^ 2 + (v 2) ^ 2) := by
      simpa [add_assoc, add_comm, add_left_comm] using hD
    have hS_re : 0 < (v 0 + v 1 + v 3 + v 2) := by omega
    exact not_three_neg hD_re hS_re h_0 h1 h_3
  · have h10 : 0 ≤ v 1 := le_of_not_gt h1
    by_cases h2 : v 2 < 0
    · exfalso
      have hD_re : (v 0 + v 3 + v 2 + v 1) ^ 2 = 2 * ((v 0) ^ 2 + (v 3) ^ 2 + (v 2) ^ 2 + (v 1) ^ 2) := by
        simpa [add_assoc, add_comm, add_left_comm] using hD
      have hS_re : 0 < (v 0 + v 3 + v 2 + v 1) := by omega
      exact not_three_neg hD_re hS_re h_0 h_3 h2
    · have h20 : 0 ≤ v 2 := le_of_not_gt h2
      exfalso
      have hD_re : (v 0 + v 3 + v 1 + v 2) ^ 2 = 2 * ((v 0) ^ 2 + (v 3) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2) := by
        simpa [add_assoc, add_comm, add_left_comm] using hD
      have hS_re : 0 < (v 0 + v 3 + v 1 + v 2) := by omega
      exact not_two_neg hD_re hS_re h_0 h_3 h10 h20
/-- Pair of negative coordinates at positions 1,2 is impossible. -/
lemma neg_pair_12 (v : Fin 4 → ℤ)
    (hD : (∑ i : Fin 4, v i) ^ 2 = 2 * ∑ i : Fin 4, (v i) ^ 2)
    (hS : 0 < ∑ i : Fin 4, v i) (h_1 : v 1 < 0) (h_2 : v 2 < 0) : False := by
  simp [Fin.sum_univ_four] at hD hS
  by_cases h0 : v 0 < 0
  · exfalso
    have hD_re : (v 1 + v 0 + v 2 + v 3) ^ 2 = 2 * ((v 1) ^ 2 + (v 0) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) := by
      simpa [add_assoc, add_comm, add_left_comm] using hD
    have hS_re : 0 < (v 1 + v 0 + v 2 + v 3) := by omega
    exact not_three_neg hD_re hS_re h_1 h0 h_2
  · have h00 : 0 ≤ v 0 := le_of_not_gt h0
    by_cases h3 : v 3 < 0
    · exfalso
      have hD_re : (v 1 + v 2 + v 3 + v 0) ^ 2 = 2 * ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 + (v 0) ^ 2) := by
        simpa [add_assoc, add_comm, add_left_comm] using hD
      have hS_re : 0 < (v 1 + v 2 + v 3 + v 0) := by omega
      exact not_three_neg hD_re hS_re h_1 h_2 h3
    · have h30 : 0 ≤ v 3 := le_of_not_gt h3
      exfalso
      have hD_re : (v 1 + v 2 + v 0 + v 3) ^ 2 = 2 * ((v 1) ^ 2 + (v 2) ^ 2 + (v 0) ^ 2 + (v 3) ^ 2) := by
        simpa [add_assoc, add_comm, add_left_comm] using hD
      have hS_re : 0 < (v 1 + v 2 + v 0 + v 3) := by omega
      exact not_two_neg hD_re hS_re h_1 h_2 h00 h30
/-- Pair of negative coordinates at positions 1,3 is impossible. -/
lemma neg_pair_13 (v : Fin 4 → ℤ)
    (hD : (∑ i : Fin 4, v i) ^ 2 = 2 * ∑ i : Fin 4, (v i) ^ 2)
    (hS : 0 < ∑ i : Fin 4, v i) (h_1 : v 1 < 0) (h_3 : v 3 < 0) : False := by
  simp [Fin.sum_univ_four] at hD hS
  by_cases h0 : v 0 < 0
  · exfalso
    have hD_re : (v 1 + v 0 + v 3 + v 2) ^ 2 = 2 * ((v 1) ^ 2 + (v 0) ^ 2 + (v 3) ^ 2 + (v 2) ^ 2) := by
      simpa [add_assoc, add_comm, add_left_comm] using hD
    have hS_re : 0 < (v 1 + v 0 + v 3 + v 2) := by omega
    exact not_three_neg hD_re hS_re h_1 h0 h_3
  · have h00 : 0 ≤ v 0 := le_of_not_gt h0
    by_cases h2 : v 2 < 0
    · exfalso
      have hD_re : (v 1 + v 3 + v 2 + v 0) ^ 2 = 2 * ((v 1) ^ 2 + (v 3) ^ 2 + (v 2) ^ 2 + (v 0) ^ 2) := by
        simpa [add_assoc, add_comm, add_left_comm] using hD
      have hS_re : 0 < (v 1 + v 3 + v 2 + v 0) := by omega
      exact not_three_neg hD_re hS_re h_1 h_3 h2
    · have h20 : 0 ≤ v 2 := le_of_not_gt h2
      exfalso
      have hD_re : (v 1 + v 3 + v 0 + v 2) ^ 2 = 2 * ((v 1) ^ 2 + (v 3) ^ 2 + (v 0) ^ 2 + (v 2) ^ 2) := by
        simpa [add_assoc, add_comm, add_left_comm] using hD
      have hS_re : 0 < (v 1 + v 3 + v 0 + v 2) := by omega
      exact not_two_neg hD_re hS_re h_1 h_3 h00 h20
/-- Pair of negative coordinates at positions 2,3 is impossible. -/
lemma neg_pair_23 (v : Fin 4 → ℤ)
    (hD : (∑ i : Fin 4, v i) ^ 2 = 2 * ∑ i : Fin 4, (v i) ^ 2)
    (hS : 0 < ∑ i : Fin 4, v i) (h_2 : v 2 < 0) (h_3 : v 3 < 0) : False := by
  simp [Fin.sum_univ_four] at hD hS
  by_cases h0 : v 0 < 0
  · exfalso
    have hD_re : (v 2 + v 0 + v 3 + v 1) ^ 2 = 2 * ((v 2) ^ 2 + (v 0) ^ 2 + (v 3) ^ 2 + (v 1) ^ 2) := by
      simpa [add_assoc, add_comm, add_left_comm] using hD
    have hS_re : 0 < (v 2 + v 0 + v 3 + v 1) := by omega
    exact not_three_neg hD_re hS_re h_2 h0 h_3
  · have h00 : 0 ≤ v 0 := le_of_not_gt h0
    by_cases h1 : v 1 < 0
    · exfalso
      have hD_re : (v 2 + v 3 + v 1 + v 0) ^ 2 = 2 * ((v 2) ^ 2 + (v 3) ^ 2 + (v 1) ^ 2 + (v 0) ^ 2) := by
        simpa [add_assoc, add_comm, add_left_comm] using hD
      have hS_re : 0 < (v 2 + v 3 + v 1 + v 0) := by omega
      exact not_three_neg hD_re hS_re h_2 h_3 h1
    · have h10 : 0 ≤ v 1 := le_of_not_gt h1
      exfalso
      have hD_re : (v 2 + v 3 + v 0 + v 1) ^ 2 = 2 * ((v 2) ^ 2 + (v 3) ^ 2 + (v 0) ^ 2 + (v 1) ^ 2) := by
        simpa [add_assoc, add_comm, add_left_comm] using hD
      have hS_re : 0 < (v 2 + v 3 + v 0 + v 1) := by omega
      exact not_two_neg hD_re hS_re h_2 h_3 h00 h10

/-- At most one negative coordinate in any Descartes quadruple with positive sum. -/
lemma at_most_one_neg_coord (v : Fin 4 → ℤ)
    (hD : (∑ i : Fin 4, v i) ^ 2 = 2 * ∑ i : Fin 4, (v i) ^ 2)
    (hS : 0 < ∑ i : Fin 4, v i) :
    ¬ ∃ i j : Fin 4, i ≠ j ∧ v i < 0 ∧ v j < 0 := by
  rintro ⟨i, j, hij, hi, hj⟩
  fin_cases i <;> fin_cases j
  all_goals try (exfalso; exact hij rfl)
  all_goals
    first
    | exact neg_pair_01 v hD hS hi hj
    | exact neg_pair_01 v hD hS hj hi
    | exact neg_pair_02 v hD hS hi hj
    | exact neg_pair_02 v hD hS hj hi
    | exact neg_pair_03 v hD hS hi hj
    | exact neg_pair_03 v hD hS hj hi
    | exact neg_pair_12 v hD hS hi hj
    | exact neg_pair_12 v hD hS hj hi
    | exact neg_pair_13 v hD hS hi hj
    | exact neg_pair_13 v hD hS hj hi
    | exact neg_pair_23 v hD hS hi hj
    | exact neg_pair_23 v hD hS hj hi

/-- Orbit quadruples have positive coordinate sum and are Descartes. -/
theorem apOrbit_descarates_posSum (v : Fin 4 → ℤ) (hv : v ∈ apOrbit) :
    (∑ i : Fin 4, v i) ^ 2 = 2 * ∑ i : Fin 4, (v i) ^ 2 ∧ 0 < ∑ i : Fin 4, v i := by
  refine of_closure_apply
    (P := fun w => (∑ j : Fin 4, w j) ^ 2 = 2 * ∑ j : Fin 4, (w j) ^ 2 ∧ 0 < ∑ j : Fin 4, w j)
    ?hP ?hS v hv
  · constructor
    · exact q0v_descarates
    · decide
  · intro i w hw
    constructor
    · exact gen_smul_descarates i w hw.1
    · exact pos_sum_of_pos_sum_move w i hw.1 hw.2

/-- At most one negative coordinate in every orbit quadruple. -/
theorem apOrbit_at_most_one_neg (v : Fin 4 → ℤ) (hv : v ∈ apOrbit) :
    ¬ ∃ i j : Fin 4, i ≠ j ∧ v i < 0 ∧ v j < 0 := by
  have hD := apOrbit_descarates v hv
  exact at_most_one_neg_coord v hD (apOrbit_descarates_posSum v hv).2

end Apollo
