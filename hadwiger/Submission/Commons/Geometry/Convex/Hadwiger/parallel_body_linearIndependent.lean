import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open scoped Classical Pointwise BigOperators
open Metric MeasureTheory Polynomial

namespace Commons.Geometry.Convex.Hadwiger

lemma linearIndependent_add_pow (n : ℕ) :
    LinearIndependent ℝ (fun i : Fin (n + 1) => fun j : Fin (n + 1) => ((i : ℝ) + (j : ℝ)) ^ n) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c h
  have hfun : ∀ j : Fin (n + 1), ∑ i : Fin (n + 1), c i * ((i : ℝ) + (j : ℝ)) ^ n = 0 := by
    intro j
    have hx := congr_fun h j
    simpa [Pi.smul_apply, smul_eq_mul] using hx
  let P : ℝ[X] := ∑ i : Fin (n + 1), Polynomial.C (c i) * (Polynomial.X + Polynomial.C (i : ℝ)) ^ n
  have hP_eval : ∀ j : Fin (n + 1), Polynomial.eval (j : ℝ) P = 0 := by
    intro j
    simp [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
    simpa [add_comm] using hfun j
  have hP_deg : P.natDegree ≤ n := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Nat.choose_eq_zero_of_lt hN]
    simp
  have hPzero : P = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (ι := Fin (n + 1)) (f := fun j : Fin (n + 1) => (j : ℝ))
    · intro a b hab
      exact Fin.ext (by exact_mod_cast (show (a:ℝ) = b from hab))
    · intro j
      simpa using hP_eval j
    · simpa [Fintype.card_fin] using lt_of_le_of_lt hP_deg (Nat.lt_succ_self n)
  have hmom : ∀ k : Fin (n + 1), ∑ i : Fin (n + 1), c i * (i : ℝ) ^ (k : ℕ) = 0 := by
    intro k
    let m : Fin (n + 1) := Fin.rev k
    have hcoeff := congrArg (fun p : ℝ[X] => p.coeff (m : ℕ)) hPzero
    have hcoeff' : (∑ i : Fin (n + 1), Polynomial.C (c i) * (Polynomial.X + Polynomial.C (i : ℝ)) ^ n).coeff (m : ℕ) = 0 := by
      simpa [P] using hcoeff
    rw [Polynomial.finsetSum_coeff] at hcoeff'
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow] at hcoeff'
    have hm : (m : ℕ) = n - (k : ℕ) := by
      simp [m, Fin.val_rev]
    have hk_le : (k : ℕ) ≤ n := Nat.le_of_lt_succ (Fin.isLt k)
    have hnm : n - (m : ℕ) = (k : ℕ) := by
      rw [hm]
      exact Nat.sub_sub_self hk_le
    have hchoose_symm : Nat.choose n (n - (k : ℕ)) = Nat.choose n (k : ℕ) := Nat.choose_symm hk_le
    have hcoeff_mom : (∑ i : Fin (n + 1), c i * (i : ℝ) ^ (k : ℕ) * (Nat.choose n (k : ℕ) : ℝ)) = 0 := by
      rw [hnm] at hcoeff'
      rw [hm] at hcoeff'
      simpa [hchoose_symm, mul_assoc, mul_comm, mul_left_comm] using hcoeff'
    have hC : (Nat.choose n (k : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk_le).ne'
    have hcoeff_sum : (Nat.choose n (k : ℕ) : ℝ) * ∑ i : Fin (n + 1), c i * (i : ℝ) ^ (k : ℕ) = 0 := by
      rw [Finset.mul_sum]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hcoeff_mom
    exact (mul_eq_zero.mp hcoeff_sum).resolve_left hC
  have hc0 : c = 0 := by
    refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (R := ℝ) (n := n + 1)
      (f := fun i : Fin (n + 1) => (i : ℝ)) (v := c) ?_ ?_
    · intro a b hab
      exact Fin.ext (by exact_mod_cast (show (a:ℝ) = b from hab))
    · intro k
      simpa [mul_comm] using hmom k
  intro i
  simpa using congr_fun hc0 i

lemma convexBody_add_smul_unitClosedBall_explicit
    (n : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (B : ConvexBody (EuclideanSpace ℝ (Fin n)))
    (hB : (B : Set (EuclideanSpace ℝ (Fin n))) = Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (((a • B) + b • B : ConvexBody (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (a + b) := by
  rw [ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_smul, hB]
  rw [smul_unitClosedBall_of_nonneg ha, smul_unitClosedBall_of_nonneg hb]
  simpa using (closedBall_add_closedBall (E := EuclideanSpace ℝ (Fin n)) ha hb (0 : EuclideanSpace ℝ (Fin n)) (0 : EuclideanSpace ℝ (Fin n)))

lemma parallelBody_ball_volume_explicit
    (n : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (B : ConvexBody (EuclideanSpace ℝ (Fin n)))
    (hB : (B : Set (EuclideanSpace ℝ (Fin n))) = Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (volume (((b • B) + a • B : ConvexBody (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)))).toReal =
      (a + b) ^ n * (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
  rw [add_comm]
  rw [convexBody_add_smul_unitClosedBall_explicit n a b ha hb B hB]
  have hvol := MeasureTheory.Measure.addHaar_real_closedBall' (μ := volume) (E := EuclideanSpace ℝ (Fin n)) (x := 0) (r := a + b) (by linarith)
  simp [MeasureTheory.measureReal_def] at hvol
  simpa [Fintype.card_fin, add_comm, mul_comm, mul_left_comm, mul_assoc] using hvol

theorem parallel_body_linearIndependent (n : ℕ) :
    let V := EuclideanSpace ℝ (Fin n)
    let B : ConvexBody V := ⟨Metric.closedBall (0 : V) 1, convex_closedBall (0 : V) 1, isCompact_closedBall (0 : V) 1, nonempty_closedBall.mpr zero_le_one⟩
    let F : ℝ → ConvexBody V → ℝ := fun t K => (volume ((K + t • B : ConvexBody V) : Set V)).toReal
    LinearIndependent ℝ (fun i : Fin (n + 1) => F (i : ℝ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c h
  let V := EuclideanSpace ℝ (Fin n)
  let B : ConvexBody V := ⟨Metric.closedBall (0 : V) 1, convex_closedBall (0 : V) 1, isCompact_closedBall (0 : V) 1, nonempty_closedBall.mpr zero_le_one⟩
  change (∑ i : Fin (n + 1), c i • (fun K : ConvexBody V => (volume ((K + (i : ℝ) • B : ConvexBody V) : Set V)).toReal)) = 0 at h
  have hB : (B : Set V) = Metric.closedBall (0 : V) 1 := rfl
  let C0 : ℝ := (volume (Metric.closedBall (0 : V) 1)).toReal
  have hC0 : C0 ≠ 0 := by
    have hpos_enn : 0 < volume (Metric.closedBall (0 : V) 1) := by
      exact Metric.measure_closedBall_pos (μ := volume) (x := (0 : V)) zero_lt_one
    have htop : volume (Metric.closedBall (0 : V) 1) < ⊤ := by
      exact measure_closedBall_lt_top
    have hpos_real : 0 < (volume (Metric.closedBall (0 : V) 1)).toReal := by
      exact ENNReal.toReal_pos (ne_of_gt hpos_enn) (ne_of_lt htop)
    exact ne_of_gt (by simpa [C0] using hpos_real)
  have hfun : ∀ j : Fin (n + 1), ∑ i : Fin (n + 1), c i * (((i : ℝ) + (j : ℝ)) ^ n * C0) = 0 := by
    intro j
    have hx := congr_fun h ((j : ℝ) • B)
    have hxj : ∑ i : Fin (n + 1), c i * (volume ((((j : ℝ) • B) + (i : ℝ) • B : ConvexBody V) : Set V)).toReal = 0 := by
      simpa [Pi.smul_apply, smul_eq_mul] using hx
    have hvol_i : ∀ i : Fin (n + 1),
        c i * (volume ((((j : ℝ) • B) + (i : ℝ) • B : ConvexBody V) : Set V)).toReal =
          c i * (((i : ℝ) + (j : ℝ)) ^ n * C0) := by
      intro i
      have hvol := parallelBody_ball_volume_explicit n (i : ℝ) (j : ℝ) (by positivity) (by positivity) B hB
      rw [hvol]
    have hsum' : (∑ i : Fin (n + 1), c i * (volume ((((j : ℝ) • B) + (i : ℝ) • B : ConvexBody V) : Set V)).toReal) =
        ∑ i : Fin (n + 1), c i * (((i : ℝ) + (j : ℝ)) ^ n * C0) := by
      exact Finset.sum_congr rfl (fun i hi => hvol_i i)
    exact hsum'.symm.trans hxj
  have hmom_add : ∀ j : Fin (n + 1), ∑ i : Fin (n + 1), c i * ((i : ℝ) + (j : ℝ)) ^ n = 0 := by
    intro j
    have hsum := hfun j
    have hsum' : C0 * (∑ i : Fin (n + 1), c i * ((i : ℝ) + (j : ℝ)) ^ n) = 0 := by
      rw [Finset.mul_sum]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hsum
    exact (mul_eq_zero.mp hsum').resolve_left hC0
  have hlin := linearIndependent_add_pow n
  rw [Fintype.linearIndependent_iff] at hlin
  apply hlin c
  ext j
  simpa [Pi.smul_apply, smul_eq_mul] using hmom_add j

end Commons.Geometry.Convex.Hadwiger