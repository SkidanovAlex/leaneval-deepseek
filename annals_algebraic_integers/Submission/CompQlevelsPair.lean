import Submission.CompQNums
import Submission.Bclps

/-!
# Opposite signs of `Q0` at consecutive level points

Helper for `Submission/CompQRoots.lean`.  `Q0 = ∏_{j'<D} (T − C(c_{r,j'}))`,
`c_{r,j'} = (2j'+1)·u_r/2`, `u_r = levelStep r`.  At two consecutive level
points (`T(v) = m·u`, `T(w) = (m+1)·u`, `m+1 ≤ D`) exactly one factor (that
with `j' = m`) changes sign between `v` and `w`, hence
`Q0.eval v · Q0.eval w < 0`.
-/

noncomputable section

open scoped Real BigOperators
open Polynomial

namespace Submission.CompQlevelsPair

open Submission.SerreExample
open Submission.ChebSerre
open Submission.AdjustedCheb
open Submission.Bclps
open Submission.DivLinear
open Submission.CompQNums

/-- sign of a single factor `m·u − c_{r,j'}` at a level point: negative iff
`m ≤ j'`. -/
theorem level_factor_nonpos_iff (r m j' : ℕ) :
    (m : ℝ) * levelStep r - factorCenter r j' < 0 ↔ m ≤ j' := by
  unfold factorCenter
  have hu : 0 < levelStep r := levelStep_pos r
  have hfac : (m : ℝ) * levelStep r - ((2 * (j' : ℝ) + 1) * levelStep r) / 2 =
      levelStep r * ((m : ℝ) - ((2 * (j' : ℝ) + 1) / 2)) := by ring
  rw [hfac]
  have hmain : levelStep r * ((m : ℝ) - ((2 * (j' : ℝ) + 1) / 2)) < 0 ↔
      (m : ℝ) - ((2 * (j' : ℝ) + 1) / 2) < 0 := by
    constructor
    · intro h
      by_contra hX
      exact (not_lt_of_ge (mul_nonneg (le_of_lt hu) (le_of_not_gt hX))) h
    · intro h
      exact mul_neg_of_pos_of_neg hu h
  rw [hmain]
  constructor
  · intro h
    by_contra hnot
    have hmj : j' < m := Nat.lt_of_not_ge hnot
    have hmjR : (j' : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hmj)
    have hhalf : (2 * (j' : ℝ) + 1) / 2 = (j' : ℝ) + 1 / 2 := by ring
    rw [hhalf] at h
    linarith
  · intro hmj
    have hmjR : (m : ℝ) ≤ (j' : ℝ) := by exact_mod_cast hmj
    have hhalf : (2 * (j' : ℝ) + 1) / 2 = (j' : ℝ) + 1 / 2 := by ring
    rw [hhalf]
    linarith

/-- sign of a single factor `m·u − c_{r,j'}` at a level point: positive iff
`j' < m`. -/
theorem level_factor_pos_iff (r m j' : ℕ) :
    0 < (m : ℝ) * levelStep r - factorCenter r j' ↔ j' < m := by
  unfold factorCenter
  have hu : 0 < levelStep r := levelStep_pos r
  have hfac : (m : ℝ) * levelStep r - ((2 * (j' : ℝ) + 1) * levelStep r) / 2 =
      levelStep r * ((m : ℝ) - ((2 * (j' : ℝ) + 1) / 2)) := by ring
  rw [hfac]
  have hmain : 0 < levelStep r * ((m : ℝ) - ((2 * (j' : ℝ) + 1) / 2)) ↔
      0 < (m : ℝ) - ((2 * (j' : ℝ) + 1) / 2) := by
    exact mul_pos_iff_of_pos_left hu
  rw [hmain]
  constructor
  · intro h
    have hhalf : (2 * (j' : ℝ) + 1) / 2 = (j' : ℝ) + 1 / 2 := by ring
    rw [hhalf] at h
    by_contra hnot
    have hmjR : (m : ℝ) ≤ (j' : ℝ) := by exact_mod_cast (Nat.le_of_not_lt hnot)
    linarith
  · intro hmj
    have hmjR : (j' : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hmj)
    have hhalf : (2 * (j' : ℝ) + 1) / 2 = (j' : ℝ) + 1 / 2 := by ring
    rw [hhalf]
    linarith

/-- product of the pair factors over levels `m` and `m+1` is strictly
negative: exactly the factor with `j' = m` changes sign. -/
theorem level_prod_pair_neg (r m : ℕ) (hm : m + 1 ≤ D) :
    (∏ j' ∈ Finset.range D, ((m : ℝ) * levelStep r - factorCenter r j')) *
      (∏ j' ∈ Finset.range D, (((m + 1 : ℕ) : ℝ) * levelStep r - factorCenter r j')) < 0 := by
  let A : ℕ → ℝ := fun j' => ((m : ℝ) * levelStep r - factorCenter r j') *
      (((m + 1 : ℕ) : ℝ) * levelStep r - factorCenter r j')
  have hmem : m ∈ Finset.range D := Finset.mem_range.mpr (Nat.lt_of_succ_le hm)
  have hcomb : (∏ j' ∈ Finset.range D, ((m : ℝ) * levelStep r - factorCenter r j')) *
      (∏ j' ∈ Finset.range D, (((m + 1 : ℕ) : ℝ) * levelStep r - factorCenter r j')) =
      ∏ j' ∈ Finset.range D, A j' := by
    simp [A, Finset.prod_mul_distrib]
  rw [hcomb]
  rw [← Finset.mul_prod_erase (Finset.range D) A hmem]
  apply mul_neg_of_neg_of_pos
  · -- the sign-changing factor `j' = m` is negative
    unfold A
    apply mul_neg_of_neg_of_pos
    · exact (level_factor_nonpos_iff r m m).mpr le_rfl
    · exact (level_factor_pos_iff r (m + 1) m).mpr (Nat.lt_succ_self m)
  · -- every other factor keeps its sign, so the remaining product is positive
    apply Finset.prod_pos
    intro j' hj'
    have hj'm : j' ≠ m := (Finset.mem_erase.mp hj').1
    unfold A
    by_cases hmj : m ≤ j'
    · -- `j' ≥ m+1`: both factors negative
      apply mul_pos_of_neg_of_neg
      · exact (level_factor_nonpos_iff r m j').mpr hmj
      · have hsucc : m + 1 ≤ j' := Nat.succ_le_iff.mpr (Nat.lt_of_le_of_ne hmj (Ne.symm hj'm))
        exact (level_factor_nonpos_iff r (m + 1) j').mpr hsucc
    · -- `j' < m`: both factors positive
      have hjlm : j' < m := Nat.lt_of_not_ge hmj
      apply mul_pos
      · exact (level_factor_pos_iff r m j').mpr hjlm
      · have hjlm' : j' < m + 1 := lt_trans hjlm (Nat.lt_succ_self m)
        exact (level_factor_pos_iff r (m + 1) j').mpr hjlm'

/-- at consecutive level points (levels `m·u` and `(m+1)·u`, `m+1 ≤ D`) the
values of `Q0` have opposite signs. -/
theorem level_pair_neg (r : ℕ) {T Q0 : Polynomial ℝ}
    (hQ0 : Q0 = ∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')))
    {v w : ℝ} (m : ℕ) (hv : T.eval v = (m : ℝ) * levelStep r)
    (hw : T.eval w = ((m + 1 : ℕ) : ℝ) * levelStep r) (hm : m + 1 ≤ D) :
    Q0.eval v * Q0.eval w < 0 := by
  rw [hQ0]
  have heval_left :
      (∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j'))).eval v =
        ∏ j' ∈ Finset.range Bclps.Dconst, ((m : ℝ) * levelStep r - factorCenter r j') := by
    calc
      eval v (∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')))
          = ∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')).eval v := by
              exact map_prod (Polynomial.evalRingHom v)
                (fun j' => (T - Polynomial.C (factorCenter r j'))) (Finset.range Bclps.Dconst)
      _ = ∏ j' ∈ Finset.range Bclps.Dconst, ((m : ℝ) * levelStep r - factorCenter r j') := by
              refine Finset.prod_congr rfl ?_
              intro j' hj'
              simp [hv]
  have heval_right :
      (∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j'))).eval w =
        ∏ j' ∈ Finset.range Bclps.Dconst, (((m + 1 : ℕ) : ℝ) * levelStep r - factorCenter r j') := by
    calc
      eval w (∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')))
          = ∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')).eval w := by
              exact map_prod (Polynomial.evalRingHom w)
                (fun j' => (T - Polynomial.C (factorCenter r j'))) (Finset.range Bclps.Dconst)
      _ = ∏ j' ∈ Finset.range Bclps.Dconst, (((m + 1 : ℕ) : ℝ) * levelStep r - factorCenter r j') := by
              refine Finset.prod_congr rfl ?_
              intro j' hj'
              simp [hw]
  rw [heval_left, heval_right]
  exact level_prod_pair_neg r m hm

end Submission.CompQlevelsPair
