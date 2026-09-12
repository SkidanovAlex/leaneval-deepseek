import Submission.CompQNums
import Submission.Bclps

/-!
# Values of `Q0` at the level points

Helper for `Submission/CompQRoots.lean`.  `Q0 = ∏_{j'<D} (T − C(c_{r,j'}))`,
`c_{r,j'} = (2j'+1)·u_r/2` with `u_r = levelStep r`.  At a *level point* `v`
with `T(v) = m·u` every factor is at distance `≥ u/2` from `v`, so
`|Q0(v)| ≥ (u/2)^D = 8·C2val⁻¹·κ^{Dr}`; at two consecutive level points
(levels `m·u` and `(m+1)·u`) exactly one factor (that with `j' = m`) changes
sign, so the product `Q0(v)·Q0(w)` is strictly negative.
-/

noncomputable section

open scoped Real BigOperators
open Polynomial

namespace Submission.CompQlevels

open Submission.SerreExample
open Submission.ChebSerre
open Submission.AdjustedCheb
open Submission.Bclps
open Submission.DivLinear
open Submission.CompQNums

/-- `(u_r/2)^D = 8·C2val⁻¹·κ^{D·r}`: the level-power lower bound in terms of
`C2val`. -/
theorem level_pow_C2 (r : ℕ) :
    (levelStep r / 2) ^ D = 8 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt D_real_pos
  have hpow_ne : ((128 * (D : ℝ)) ^ D) ≠ 0 := by positivity
  calc
    (levelStep r / 2) ^ D = (kappaC ^ r / (128 * (D : ℝ))) ^ D := by
      congr 1
      unfold levelStep
      field_simp [hDne]
      ring
    _ = (kappaC ^ r) ^ D / (128 * (D : ℝ)) ^ D := by rw [div_pow]
    _ = kappaC ^ (r * D) / (128 * (D : ℝ)) ^ D := by rw [pow_mul]
    _ = kappaC ^ (Bclps.Dconst * r) / (128 * (D : ℝ)) ^ D := by
      have hExp : r * D = Bclps.Dconst * r := mul_comm r Bclps.Dconst
      rw [hExp]
    _ = 8 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
      unfold C2val
      field_simp [hpow_ne]

/-- at a level point `T(v) = m·u` the polynomial `Q0` is bounded below by
`8·C2val⁻¹·κ^{D·r}` in absolute value. -/
theorem level_mag (r : ℕ) {T Q0 : Polynomial ℝ}
    (hQ0 : Q0 = ∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')))
    {v : ℝ} (m : ℕ) (hv : T.eval v = (m : ℝ) * levelStep r) :
    8 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q0.eval v| := by
  have hprod : (∏ j' ∈ Finset.range D,
        |(m : ℝ) * levelStep r - factorCenter r j'|) = |Q0.eval v| := by
    rw [hQ0]
    rw [Polynomial.eval_prod]
    rw [Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro j' hj'
    simp [hv]
  calc
    8 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r)
        = (levelStep r / 2) ^ D := (level_pow_C2 r).symm
    _ ≤ ∏ j' ∈ Finset.range D, |(m : ℝ) * levelStep r - factorCenter r j'| :=
        prod_level_lower r m
    _ = |Q0.eval v| := hprod

/-- the factor indexed by `j = m` reverses sign between the consecutive levels
`m·u` and `(m+1)·u`, so its pair-product is negative. -/
private lemma pair_center_neg {r m : ℕ} :
    ((m : ℝ) * levelStep r - factorCenter r m) *
      (((m + 1 : ℕ) : ℝ) * levelStep r - factorCenter r m) < 0 := by
  have hu : 0 < levelStep r := levelStep_pos r
  unfold factorCenter
  have hc1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
  rw [hc1]
  have h1 : (m : ℝ) * levelStep r - ((2 * (m : ℝ) + 1) * levelStep r) / 2 = -(levelStep r / 2) := by ring
  have h2 : ((m : ℝ) + 1) * levelStep r - ((2 * (m : ℝ) + 1) * levelStep r) / 2 = levelStep r / 2 := by ring
  rw [h1, h2]
  exact mul_neg_of_neg_of_pos (by linarith) (by positivity)

/-- any other factor keeps its sign between the consecutive levels `m·u` and
`(m+1)·u`, so its pair-product is positive. -/
private lemma pair_center_pos {r m j : ℕ} (hj : j ≠ m) :
    0 < ((m : ℝ) * levelStep r - factorCenter r j) *
      (((m + 1 : ℕ) : ℝ) * levelStep r - factorCenter r j) := by
  have hu : 0 < levelStep r := levelStep_pos r
  unfold factorCenter
  have hc1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
  rw [hc1]
  by_cases hjm : j < m
  · have hpos1 : 0 < (m : ℝ) * levelStep r - ((2 * (j : ℝ) + 1) * levelStep r) / 2 := by
      have h : (m : ℝ) * levelStep r - ((2 * (j : ℝ) + 1) * levelStep r) / 2 =
          (levelStep r / 2) * (2 * (m : ℝ) - 2 * (j : ℝ) - 1) := by ring
      rw [h]
      have hlt : 0 < 2 * (m : ℝ) - 2 * (j : ℝ) - 1 := by
        have hjR : (j : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hjm)
        nlinarith
      exact mul_pos (by positivity) hlt
    have hpos2 : 0 < ((m : ℝ) + 1) * levelStep r - ((2 * (j : ℝ) + 1) * levelStep r) / 2 := by
      have h : ((m : ℝ) + 1) * levelStep r - ((2 * (j : ℝ) + 1) * levelStep r) / 2 =
          (levelStep r / 2) * (2 * (m : ℝ) + 2 - 2 * (j : ℝ) - 1) := by ring
      rw [h]
      have hlt : 0 < 2 * (m : ℝ) + 2 - 2 * (j : ℝ) - 1 := by
        have hjR : (j : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hjm)
        nlinarith
      exact mul_pos (by positivity) hlt
    exact mul_pos hpos1 hpos2
  · have hmle : m ≤ j := Nat.le_of_not_gt hjm
    have hmj : m < j := lt_of_le_of_ne hmle (by intro h; exact hj h.symm)
    have hneg1 : (m : ℝ) * levelStep r - ((2 * (j : ℝ) + 1) * levelStep r) / 2 < 0 := by
      have h : (m : ℝ) * levelStep r - ((2 * (j : ℝ) + 1) * levelStep r) / 2 =
          (levelStep r / 2) * (2 * (m : ℝ) - 2 * (j : ℝ) - 1) := by ring
      rw [h]
      have hlt : 2 * (m : ℝ) - 2 * (j : ℝ) - 1 < 0 := by
        have hjR : (m : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hmj)
        nlinarith
      exact mul_neg_of_pos_of_neg (by positivity) hlt
    have hneg2 : ((m : ℝ) + 1) * levelStep r - ((2 * (j : ℝ) + 1) * levelStep r) / 2 < 0 := by
      have h : ((m : ℝ) + 1) * levelStep r - ((2 * (j : ℝ) + 1) * levelStep r) / 2 =
          (levelStep r / 2) * (2 * (m : ℝ) + 2 - 2 * (j : ℝ) - 1) := by ring
      rw [h]
      have hlt : 2 * (m : ℝ) + 2 - 2 * (j : ℝ) - 1 < 0 := by
        have hjR : (m : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hmj)
        nlinarith
      exact mul_neg_of_pos_of_neg (by positivity) hlt
    have hmul : 0 < (-((m : ℝ) * levelStep r - ((2 * (j : ℝ) + 1) * levelStep r) / 2)) *
        (-(((m : ℝ) + 1) * levelStep r - ((2 * (j : ℝ) + 1) * levelStep r) / 2)) :=
        mul_pos (by linarith) (by linarith)
    nlinarith

/-- at consecutive level points (levels `m·u` and `(m+1)·u`, `m+1 ≤ D`) the
values of `Q0` have opposite signs. -/
theorem level_pair_neg (r : ℕ) {T Q0 : Polynomial ℝ}
    (hQ0 : Q0 = ∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')))
    {v w : ℝ} (m : ℕ) (hv : T.eval v = (m : ℝ) * levelStep r)
    (hw : T.eval w = ((m + 1 : ℕ) : ℝ) * levelStep r) (hm : m + 1 ≤ D) :
    Q0.eval v * Q0.eval w < 0 := by
  have hmain : Q0.eval v * Q0.eval w =
      (∏ j ∈ Finset.range D,
          ((m : ℝ) * levelStep r - factorCenter r j) *
            (((m + 1 : ℕ) : ℝ) * levelStep r - factorCenter r j)) := by
    rw [hQ0]
    have hevalv : (∏ j ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j))).eval v =
        (∏ j ∈ Finset.range D, ((m : ℝ) * levelStep r - factorCenter r j)) := by
      rw [Polynomial.eval_prod]
      apply Finset.prod_congr rfl
      intro j hj
      simp [hv]
    have hevalw : (∏ j ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j))).eval w =
        (∏ j ∈ Finset.range D, (((m + 1 : ℕ) : ℝ) * levelStep r - factorCenter r j)) := by
      rw [Polynomial.eval_prod]
      apply Finset.prod_congr rfl
      intro j hj
      simp [hw]
    rw [hevalv, hevalw]
    rw [← Finset.prod_mul_distrib]
  let f : ℕ → ℝ := fun j => ((m : ℝ) * levelStep r - factorCenter r j) *
      (((m + 1 : ℕ) : ℝ) * levelStep r - factorCenter r j)
  have hmem : m ∈ Finset.range D := by
    exact Finset.mem_range.mpr (Nat.lt_of_succ_le hm)
  have hneg : f m < 0 := by
    dsimp [f]
    exact pair_center_neg (r := r) (m := m)
  have hpos : ∀ j ∈ (Finset.range D).erase m, 0 < f j := by
    intro j hj
    have hjm : j ≠ m := (Finset.mem_erase.mp hj).1
    dsimp [f]
    exact pair_center_pos (r := r) (m := m) (j := j) hjm
  have hprodpos : 0 < (∏ j ∈ (Finset.range D).erase m, f j) := by
    exact Finset.prod_pos hpos
  have hsplit : (∏ j ∈ Finset.range D, f j) = f m * (∏ j ∈ (Finset.range D).erase m, f j) := by
    calc
      (∏ j ∈ Finset.range D, f j)
          = (∏ j ∈ (Finset.range D).erase m, f j) * f m :=
              (Finset.prod_erase_mul (s := Finset.range D) (f := f) (a := m) hmem).symm
      _ = f m * (∏ j ∈ (Finset.range D).erase m, f j) := by rw [mul_comm]
  have hlt : (∏ j ∈ Finset.range D, f j) < 0 := by
    rw [hsplit]
    exact mul_neg_of_neg_of_pos hneg hprodpos
  rw [hmain]
  simpa [f] using hlt

end Submission.CompQlevels
