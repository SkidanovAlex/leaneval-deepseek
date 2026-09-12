import Mathlib
import ChallengeDeps
import Submission.RS

/-! Truncation of Littlewood polynomials: removing the top few monomials of a
Littlewood polynomial of degree `d` (all coefficients ±1) yields a Littlewood
polynomial of any degree `m ≤ d`, changing values on the unit circle by at
most `d − m`. -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

open FlatLittlewoodPoly

namespace Submission
namespace Trunc

/-- Truncate a polynomial to degree `m` (erase coefficients above `m`). -/
def trunc (P : ℂ[X]) (m : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range (m + 1), Polynomial.C (P.coeff j) * X ^ j

lemma coeff_trunc (P : ℂ[X]) (m j : ℕ) (hj : j ≤ m) :
    (trunc P m).coeff j = P.coeff j := by
  rw [trunc]
  simp only [finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    by_cases h : j = b
    · exfalso
      exact hbj h.symm
    · simp [h]
  · intro hmem
    exfalso
    exact hmem (by simpa using Nat.lt_succ_of_le hj)

lemma coeff_trunc_of_gt (P : ℂ[X]) (m j : ℕ) (hj : m < j) :
    (trunc P m).coeff j = 0 := by
  rw [trunc]
  simp only [finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro b hb
  have hb_lt : b < m + 1 := Finset.mem_range.mp hb
  have hbj : b ≠ j := by omega
  by_cases h : j = b
  · exfalso
    exact hbj h.symm
  · simp [h]

lemma trunc_littlewood_degree (Q : ℂ[X]) (d m : ℕ) (hQ : IsLittlewoodPolynomial Q)
    (hd : Q.natDegree = d) (hm : m ≤ d) :
    IsLittlewoodPolynomial (trunc Q m) ∧ (trunc Q m).natDegree = m := by
  have hcoeff_m_ne : (trunc Q m).coeff m ≠ 0 := by
    rw [coeff_trunc Q m m (le_rfl)]
    have hmdeg : m ≤ Q.natDegree := by omega
    rcases hQ m hmdeg with h1 | h1
    · rw [h1]; norm_num
    · rw [h1]; norm_num
  have hdeg_le : (trunc Q m).natDegree ≤ m := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact coeff_trunc_of_gt Q m N hN
  have hdeg : (trunc Q m).natDegree = m :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg_le hcoeff_m_ne
  constructor
  · intro i hi
    have hi_le_m : i ≤ m := by simpa [hdeg] using hi
    have hi_le_deg : i ≤ Q.natDegree := by omega
    rw [coeff_trunc Q m i hi_le_m]
    exact hQ i hi_le_deg
  · exact hdeg

lemma trunc_sub_le (Q : ℂ[X]) (d m : ℕ) (hQ : IsLittlewoodPolynomial Q)
    (hd : Q.natDegree = d) (hm : m ≤ d) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(trunc Q m).eval z - Q.eval z‖ ≤ (d - m : ℝ) := by
  have hdeg := (trunc_littlewood_degree Q d m hQ hd hm).2
  let f : ℕ → ℂ := fun j => Q.coeff j * z ^ j
  have h1 : Q.eval z = ∑ j ∈ Finset.range (d + 1), f j := by
    simpa [f, hd] using (Polynomial.eval_eq_sum_range (p := Q) z)
  have h2 : (trunc Q m).eval z = ∑ j ∈ Finset.range (m + 1), f j := by
    rw [Polynomial.eval_eq_sum_range (p := trunc Q m) z]
    rw [hdeg]
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < m + 1 := Finset.mem_range.mp hj
    dsimp [f]
    rw [coeff_trunc Q m j (by omega)]
  have hsub : Finset.range (m + 1) ⊆ Finset.range (d + 1) := by
    intro x hx
    have hx_lt : x < m + 1 := Finset.mem_range.mp hx
    exact Finset.mem_range.mpr (by omega)
  have hsum_eq :
      (∑ j ∈ (Finset.range (d + 1)) \ (Finset.range (m + 1)), f j) =
        Q.eval z - (trunc Q m).eval z := by
    rw [h1, h2]
    exact eq_sub_of_add_eq (Finset.sum_sdiff hsub)
  calc
    ‖(trunc Q m).eval z - Q.eval z‖
        = ‖Q.eval z - (trunc Q m).eval z‖ := by rw [norm_sub_rev]
    _ = ‖∑ j ∈ (Finset.range (d + 1)) \ (Finset.range (m + 1)), f j‖ := by rw [hsum_eq]
    _ ≤ ∑ j ∈ (Finset.range (d + 1)) \ (Finset.range (m + 1)), ‖f j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ (Finset.range (d + 1)) \ (Finset.range (m + 1)), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj_s : j ∈ Finset.range (d + 1) := (Finset.mem_sdiff.mp hj).1
        have hj_notm : j ∉ Finset.range (m + 1) := (Finset.mem_sdiff.mp hj).2
        have hterm : ‖f j‖ = 1 := by
          dsimp [f]
          calc
            ‖Q.coeff j * z ^ j‖ = ‖Q.coeff j‖ * ‖z ^ j‖ := by rw [norm_mul]
            _ = 1 := by
              have hj_le_deg : j ≤ Q.natDegree := by
                have : j < d + 1 := Finset.mem_range.mp hj_s
                omega
              have hc : ‖Q.coeff j‖ = 1 := by
                rcases hQ j hj_le_deg with h | h
                · rw [h]; norm_num
                · rw [h]; norm_num
              have hpow : ‖z ^ j‖ = 1 := by
                rw [norm_pow, hz]
                simp
              rw [hc, hpow]
              norm_num
        rw [hterm]
    _ = ((Finset.range (d + 1)) \ (Finset.range (m + 1))).card := by simp
    _ ≤ (d : ℝ) - (m : ℝ) := by
        have hcard : ((Finset.range (d + 1)) \ (Finset.range (m + 1))).card = d - m := by
          rw [Finset.card_sdiff]
          have hinter : Finset.range (m + 1) ∩ Finset.range (d + 1) = Finset.range (m + 1) := by
            exact Finset.inter_eq_left.mpr hsub
          rw [hinter, Finset.card_range, Finset.card_range]
          omega
        calc
          (((Finset.range (d + 1)) \ (Finset.range (m + 1))).card : ℝ)
              = ((d - m : ℕ) : ℝ) := by rw [hcard]
          _ ≤ (d : ℝ) - (m : ℝ) := le_of_eq (Nat.cast_sub hm)

lemma trunc_sub_le_three (Q : ℂ[X]) (d m : ℕ) (hQ : IsLittlewoodPolynomial Q)
    (hd : Q.natDegree = d) (hm3 : d - m ≤ 3) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(trunc Q m).eval z - Q.eval z‖ ≤ 3 := by
  by_cases hm : m ≤ d
  · calc
      ‖(trunc Q m).eval z - Q.eval z‖ ≤ (d : ℝ) - (m : ℝ) :=
        trunc_sub_le Q d m hQ hd hm z hz
      _ = ((d - m : ℕ) : ℝ) := (Nat.cast_sub hm).symm
      _ ≤ 3 := by exact_mod_cast hm3
  · have hmd : d < m := Nat.lt_of_not_ge hm
    have hR : trunc Q m = Q := by
      apply Polynomial.ext
      intro j
      by_cases hjm : j ≤ m
      · rw [coeff_trunc Q m j hjm]
      · have hmg : m < j := Nat.lt_of_not_ge hjm
        rw [coeff_trunc_of_gt Q m j hmg]
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    rw [hR]
    norm_num

end Trunc
end Submission
