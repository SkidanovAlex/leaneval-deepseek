import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Matrix.Cartan
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Commons.Algebra.Lie.SerreConstruction

open Matrix

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

private def e8Inv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2;
     5, 8, 10, 15, 12, 9, 6, 3;
     7, 10, 14, 20, 16, 12, 8, 4;
     10, 15, 20, 30, 24, 18, 12, 6;
     8, 12, 16, 24, 20, 15, 10, 5;
     6, 9, 12, 18, 15, 12, 8, 4;
     4, 6, 8, 12, 10, 8, 6, 3;
     2, 3, 4, 6, 5, 4, 3, 2]

private def Mq : Matrix (Fin 8) (Fin 8) ℚ :=
  !![4, 5, 7, 10, 8, 6, 4, 2;
     5, 8, 10, 15, 12, 9, 6, 3;
     7, 10, 14, 20, 16, 12, 8, 4;
     10, 15, 20, 30, 24, 18, 12, 6;
     8, 12, 16, 24, 20, 15, 10, 5;
     6, 9, 12, 18, 15, 12, 8, 4;
     4, 6, 8, 12, 10, 8, 6, 3;
     2, 3, 4, 6, 5, 4, 3, 2]

private def E8q : Matrix (Fin 8) (Fin 8) ℚ :=
  !![2, 0, -1, 0, 0, 0, 0, 0;
     0, 2, 0, -1, 0, 0, 0, 0;
     -1, 0, 2, -1, 0, 0, 0, 0;
     0, -1, -1, 2, -1, 0, 0, 0;
     0, 0, 0, -1, 2, -1, 0, 0;
     0, 0, 0, 0, -1, 2, -1, 0;
     0, 0, 0, 0, 0, -1, 2, -1;
     0, 0, 0, 0, 0, 0, -1, 2]

private def Aq : Matrix (Fin 8) (Fin 8) ℚ := CartanMatrix.E₈.map (Int.castRingHom ℚ)

private lemma E8q_eq : E8q = Aq := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [E8q, Aq, CartanMatrix.E₈, CartanMatrix.E_eight_eq, Matrix.map_apply]

private lemma Mq_eq : Mq = e8Inv.map (Int.castRingHom ℚ) := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Mq, e8Inv, Matrix.map_apply]

private lemma e8Inv_mul : CartanMatrix.E₈ * e8Inv = 1 := by decide
private lemma mul_e8Inv : e8Inv * CartanMatrix.E₈ = 1 := by decide

private lemma Aq_mul_Mq : Aq * Mq = 1 := by
  rw [Mq_eq]
  change CartanMatrix.E₈.map (Int.castRingHom ℚ) * e8Inv.map (Int.castRingHom ℚ) = 1
  rw [← Matrix.map_mul, e8Inv_mul]
  ext i j; fin_cases i <;> fin_cases j <;> simp

private lemma Mq_mul_Aq : Mq * Aq = 1 := by
  rw [Mq_eq]
  change e8Inv.map (Int.castRingHom ℚ) * CartanMatrix.E₈.map (Int.castRingHom ℚ) = 1
  rw [← Matrix.map_mul, mul_e8Inv]
  ext i j; fin_cases i <;> fin_cases j <;> simp

private lemma Mq_eq_inv : Mq = Aq⁻¹ := (Matrix.inv_eq_right_inv Aq_mul_Mq).symm

private def Qalpha (a : Fin 8 → ℤ) : ℤ :=
  2*(a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2)
  - 2*(a 0 * a 2 + a 1 * a 3 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7)

private lemma Qalpha_cast (a : Fin 8 → ℤ) :
    (Qalpha a : ℚ) = ∑ i, ∑ j, (a i : ℚ) * E8q i j * (a j : ℚ) := by
  simp only [Qalpha, E8q, Fin.sum_univ_eight, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val]
  push_cast
  ring

private lemma sos_identity (a : Fin 8 → ℤ) :
    60 * Qalpha a =
      30*(2*a 0 - a 2)^2 + 30*(2*a 1 - a 3)^2 + 10*(3*a 2 - 2*a 3)^2 + 2*(5*a 3 - 6*a 4)^2
      + 3*(4*a 4 - 5*a 5)^2 + 5*(3*a 5 - 4*a 6)^2 + 10*(2*a 6 - 3*a 7)^2 + 30*(a 7)^2 := by
  simp only [Qalpha]; ring

private noncomputable def Qmu (m : Fin 8 → ℤ) : ℚ :=
  ∑ i, ∑ j, (m i : ℚ) * (Aq)⁻¹ i j * (m j : ℚ)

private lemma mulVec_cast (a : Fin 8 → ℤ) (i : Fin 8) :
    ((CartanMatrix.E₈ *ᵥ a) i : ℚ) = ∑ k, E8q i k * (a k : ℚ) := by
  simp only [Matrix.mulVec, E8q_eq, Aq, Matrix.map_apply, Int.coe_castRingHom]
  unfold dotProduct
  push_cast
  ring

private lemma Qmu_eq_qalpha (v : Fin 8 → ℚ) :
    (∑ i, ∑ j, (∑ k, E8q i k * v k) * Mq i j * (∑ l, E8q j l * v l))
      = ∑ i, ∑ j, v i * E8q i j * v j := by
  simp only [E8q, Mq, Fin.sum_univ_eight, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val]
  ring

private lemma Qmu_toMu (a : Fin 8 → ℤ) :
    Qmu (CartanMatrix.E₈ *ᵥ a) = (Qalpha a : ℚ) := by
  have h1 : Qmu (CartanMatrix.E₈ *ᵥ a)
      = ∑ i, ∑ j, (∑ k, E8q i k * (a k : ℚ)) * Mq i j * (∑ l, E8q j l * (a l : ℚ)) := by
    rw [Qmu, ← Mq_eq_inv]
    simp only [mulVec_cast]
  rw [h1, Qmu_eq_qalpha, ← Qalpha_cast]

private lemma int_le_of_sq_le {x C m : ℤ} (hm : 0 ≤ m) (h : x^2 ≤ C) (hC : C < (m+1)^2) :
    x ≤ m := by
  by_contra hx
  have h1 : m + 1 ≤ x := by omega
  have h3 : (m+1)*(m+1) ≤ x*x := mul_le_mul h1 h1 (by omega) (by omega)
  nlinarith [h, h3, hC]

private lemma neg_int_le_of_sq_le {x C m : ℤ} (hm : 0 ≤ m) (h : x^2 ≤ C) (hC : C < (m+1)^2) :
    -m ≤ x := by
  by_contra hx
  have h1 : m + 1 ≤ -x := by omega
  have h3 : (m+1)*(m+1) ≤ (-x)*(-x) := mul_le_mul h1 h1 (by omega) (by omega)
  have h4 : (-x)*(-x) = x*x := by ring
  nlinarith [h, h3, hC, h4]

private lemma sq_bounds (a : Fin 8 → ℤ) (h : Qalpha a = 2) :
    (2*a 0 - a 2)^2 ≤ 4 ∧ (2*a 1 - a 3)^2 ≤ 4 ∧ (3*a 2 - 2*a 3)^2 ≤ 12 ∧
    (5*a 3 - 6*a 4)^2 ≤ 60 ∧ (4*a 4 - 5*a 5)^2 ≤ 40 ∧ (3*a 5 - 4*a 6)^2 ≤ 24 ∧
    (2*a 6 - 3*a 7)^2 ≤ 12 ∧ (a 7)^2 ≤ 4 := by
  have hs := sos_identity a
  rw [h] at hs
  norm_num at hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith [hs, sq_nonneg (2*a 0 - a 2), sq_nonneg (2*a 1 - a 3), sq_nonneg (3*a 2 - 2*a 3),
      sq_nonneg (5*a 3 - 6*a 4), sq_nonneg (4*a 4 - 5*a 5), sq_nonneg (3*a 5 - 4*a 6),
      sq_nonneg (2*a 6 - 3*a 7), sq_nonneg (a 7)]

private lemma coord_bounds (a : Fin 8 → ℤ) (h : Qalpha a = 2) :
    (-2 ≤ a 7 ∧ a 7 ≤ 2) ∧ (-4 ≤ a 6 ∧ a 6 ≤ 4) ∧ (-6 ≤ a 5 ∧ a 5 ≤ 6) ∧
    (-9 ≤ a 4 ∧ a 4 ≤ 9) ∧ (-12 ≤ a 3 ∧ a 3 ≤ 12) ∧ (-9 ≤ a 2 ∧ a 2 ≤ 9) ∧
    (-5 ≤ a 0 ∧ a 0 ≤ 5) ∧ (-7 ≤ a 1 ∧ a 1 ≤ 7) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := sq_bounds a h
  have c7 := neg_int_le_of_sq_le (m:=2) (by norm_num) h7 (by norm_num)
  have d7 := int_le_of_sq_le (m:=2) (by norm_num) h7 (by norm_num)
  have c6 := neg_int_le_of_sq_le (m:=3) (by norm_num) h6 (by norm_num)
  have d6 := int_le_of_sq_le (m:=3) (by norm_num) h6 (by norm_num)
  have c5 := neg_int_le_of_sq_le (m:=4) (by norm_num) h5 (by norm_num)
  have d5 := int_le_of_sq_le (m:=4) (by norm_num) h5 (by norm_num)
  have c4 := neg_int_le_of_sq_le (m:=6) (by norm_num) h4 (by norm_num)
  have d4 := int_le_of_sq_le (m:=6) (by norm_num) h4 (by norm_num)
  have c3 := neg_int_le_of_sq_le (m:=7) (by norm_num) h3 (by norm_num)
  have d3 := int_le_of_sq_le (m:=7) (by norm_num) h3 (by norm_num)
  have c2 := neg_int_le_of_sq_le (m:=3) (by norm_num) h2 (by norm_num)
  have d2 := int_le_of_sq_le (m:=3) (by norm_num) h2 (by norm_num)
  have c0 := neg_int_le_of_sq_le (m:=2) (by norm_num) h0 (by norm_num)
  have d0 := int_le_of_sq_le (m:=2) (by norm_num) h0 (by norm_num)
  have c1 := neg_int_le_of_sq_le (m:=2) (by norm_num) h1 (by norm_num)
  have d1 := int_le_of_sq_le (m:=2) (by norm_num) h1 (by norm_num)
  refine ⟨⟨c7, d7⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

private def S7 (k7 : ℕ) : ℤ := 30*((k7:ℤ) - 2)^2
private def S6 (k7 k6 : ℕ) : ℤ := S7 k7 + 10*(2*((k6:ℤ) - 4) - 3*((k7:ℤ) - 2))^2
private def S5 (k7 k6 k5 : ℕ) : ℤ := S6 k7 k6 + 5*(3*((k5:ℤ) - 6) - 4*((k6:ℤ) - 4))^2
private def S4 (k7 k6 k5 k4 : ℕ) : ℤ := S5 k7 k6 k5 + 3*(4*((k4:ℤ) - 9) - 5*((k5:ℤ) - 6))^2
private def S3 (k7 k6 k5 k4 k3 : ℕ) : ℤ := S4 k7 k6 k5 k4 + 2*(5*((k3:ℤ) - 12) - 6*((k4:ℤ) - 9))^2
private def S2 (k7 k6 k5 k4 k3 k2 : ℕ) : ℤ := S3 k7 k6 k5 k4 k3 + 10*(3*((k2:ℤ) - 9) - 2*((k3:ℤ) - 12))^2
private def S0 (k7 k6 k5 k4 k3 k2 k0 : ℕ) : ℤ := S2 k7 k6 k5 k4 k3 k2 + 30*(2*((k0:ℤ) - 5) - ((k2:ℤ) - 9))^2
private def S1 (k7 k6 k5 k4 k3 k2 k0 k1 : ℕ) : ℤ := S0 k7 k6 k5 k4 k3 k2 k0 + 30*(2*((k1:ℤ) - 7) - ((k3:ℤ) - 12))^2

private def vecOf (k0 k1 k2 k3 k4 k5 k6 k7 : ℕ) : Fin 8 → ℤ :=
  ![(k0:ℤ) - 5, (k1:ℤ) - 7, (k2:ℤ) - 9, (k3:ℤ) - 12, (k4:ℤ) - 9, (k5:ℤ) - 6, (k6:ℤ) - 4, (k7:ℤ) - 2]

private def alphaCand : List (Fin 8 → ℤ) :=
  (List.range 5).flatMap fun (k7 : ℕ) =>
  ((List.range 9).filter fun (k6 : ℕ) => S6 k7 k6 ≤ 120).flatMap fun (k6 : ℕ) =>
  ((List.range 13).filter fun (k5 : ℕ) => S5 k7 k6 k5 ≤ 120).flatMap fun (k5 : ℕ) =>
  ((List.range 19).filter fun (k4 : ℕ) => S4 k7 k6 k5 k4 ≤ 120).flatMap fun (k4 : ℕ) =>
  ((List.range 25).filter fun (k3 : ℕ) => S3 k7 k6 k5 k4 k3 ≤ 120).flatMap fun (k3 : ℕ) =>
  ((List.range 19).filter fun (k2 : ℕ) => S2 k7 k6 k5 k4 k3 k2 ≤ 120).flatMap fun (k2 : ℕ) =>
  ((List.range 11).filter fun (k0 : ℕ) => S0 k7 k6 k5 k4 k3 k2 k0 ≤ 120).flatMap fun (k0 : ℕ) =>
  ((List.range 15).filter fun (k1 : ℕ) => S1 k7 k6 k5 k4 k3 k2 k0 k1 = 120).map fun (k1 : ℕ) =>
  vecOf k0 k1 k2 k3 k4 k5 k6 k7

private lemma sixty_Qalpha_vec (k0 k1 k2 k3 k4 k5 k6 k7 : ℕ) :
    60 * Qalpha (vecOf k0 k1 k2 k3 k4 k5 k6 k7) = S1 k7 k6 k5 k4 k3 k2 k0 k1 := by
  simp only [Qalpha, vecOf, S1, S0, S2, S3, S4, S5, S6, S7, Matrix.cons_val]
  ring

private lemma alphaCand_mem_iff (u : Fin 8 → ℤ) :
    u ∈ alphaCand ↔
      ∃ k0 k1 k2 k3 k4 k5 k6 k7 : ℕ, k7 < 5 ∧ (k6 < 9 ∧ S6 k7 k6 ≤ 120) ∧
        (k5 < 13 ∧ S5 k7 k6 k5 ≤ 120) ∧ (k4 < 19 ∧ S4 k7 k6 k5 k4 ≤ 120) ∧
        (k3 < 25 ∧ S3 k7 k6 k5 k4 k3 ≤ 120) ∧ (k2 < 19 ∧ S2 k7 k6 k5 k4 k3 k2 ≤ 120) ∧
        (k0 < 11 ∧ S0 k7 k6 k5 k4 k3 k2 k0 ≤ 120) ∧
        (k1 < 15 ∧ S1 k7 k6 k5 k4 k3 k2 k0 k1 = 120) ∧ vecOf k0 k1 k2 k3 k4 k5 k6 k7 = u := by
  simp only [alphaCand, List.mem_flatMap, List.mem_range, List.mem_filter, List.mem_map,
    decide_eq_true_eq]
  constructor
  · rintro ⟨k7, h7, k6, ⟨h6, c6⟩, k5, ⟨h5, c5⟩, k4, ⟨h4, c4⟩, k3, ⟨h3, c3⟩, k2, ⟨h2, c2⟩,
      k0, ⟨h0, c0⟩, k1, ⟨h1, c1⟩, he⟩
    exact ⟨k0, k1, k2, k3, k4, k5, k6, k7, h7, ⟨h6, c6⟩, ⟨h5, c5⟩, ⟨h4, c4⟩, ⟨h3, c3⟩,
      ⟨h2, c2⟩, ⟨h0, c0⟩, ⟨h1, c1⟩, he⟩
  · rintro ⟨k0, k1, k2, k3, k4, k5, k6, k7, h7, ⟨h6, c6⟩, ⟨h5, c5⟩, ⟨h4, c4⟩, ⟨h3, c3⟩,
      ⟨h2, c2⟩, ⟨h0, c0⟩, ⟨h1, c1⟩, he⟩
    exact ⟨k7, h7, k6, ⟨h6, c6⟩, k5, ⟨h5, c5⟩, k4, ⟨h4, c4⟩, k3, ⟨h3, c3⟩, k2, ⟨h2, c2⟩,
      k0, ⟨h0, c0⟩, k1, ⟨h1, c1⟩, he⟩

private lemma Qalpha_of_mem_alphaCand {u : Fin 8 → ℤ} (hu : u ∈ alphaCand) : Qalpha u = 2 := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, -, -, -, -, -, -, -, ⟨-, he1⟩, he⟩ :=
    (alphaCand_mem_iff u).mp hu
  subst he
  have h := sixty_Qalpha_vec k0 k1 k2 k3 k4 k5 k6 k7
  rw [he1] at h
  omega

private lemma mem_alphaCand {a : Fin 8 → ℤ} (h : Qalpha a = 2) : a ∈ alphaCand := by
  obtain ⟨⟨h7a, h7b⟩, ⟨h6a, h6b⟩, ⟨h5a, h5b⟩, ⟨h4a, h4b⟩, ⟨h3a, h3b⟩, ⟨h2a, h2b⟩,
    ⟨h0a, h0b⟩, ⟨h1a, h1b⟩⟩ := coord_bounds a h
  have hs := sos_identity a
  rw [h] at hs
  norm_num at hs
  have t0 : (((a 0 + 5).toNat : ℤ)) = a 0 + 5 := Int.toNat_of_nonneg (by omega)
  have t1 : (((a 1 + 7).toNat : ℤ)) = a 1 + 7 := Int.toNat_of_nonneg (by omega)
  have t2 : (((a 2 + 9).toNat : ℤ)) = a 2 + 9 := Int.toNat_of_nonneg (by omega)
  have t3 : (((a 3 + 12).toNat : ℤ)) = a 3 + 12 := Int.toNat_of_nonneg (by omega)
  have t4 : (((a 4 + 9).toNat : ℤ)) = a 4 + 9 := Int.toNat_of_nonneg (by omega)
  have t5 : (((a 5 + 6).toNat : ℤ)) = a 5 + 6 := Int.toNat_of_nonneg (by omega)
  have t6 : (((a 6 + 4).toNat : ℤ)) = a 6 + 4 := Int.toNat_of_nonneg (by omega)
  have t7 : (((a 7 + 2).toNat : ℤ)) = a 7 + 2 := Int.toNat_of_nonneg (by omega)
  have r0 : (a 0 + 5).toNat < 11 := by rw [Int.toNat_lt (by omega)]; omega
  have r1 : (a 1 + 7).toNat < 15 := by rw [Int.toNat_lt (by omega)]; omega
  have r2 : (a 2 + 9).toNat < 19 := by rw [Int.toNat_lt (by omega)]; omega
  have r3 : (a 3 + 12).toNat < 25 := by rw [Int.toNat_lt (by omega)]; omega
  have r4 : (a 4 + 9).toNat < 19 := by rw [Int.toNat_lt (by omega)]; omega
  have r5 : (a 5 + 6).toNat < 13 := by rw [Int.toNat_lt (by omega)]; omega
  have r6 : (a 6 + 4).toNat < 9 := by rw [Int.toNat_lt (by omega)]; omega
  have r7 : (a 7 + 2).toNat < 5 := by rw [Int.toNat_lt (by omega)]; omega
  rw [alphaCand_mem_iff]
  refine ⟨(a 0 + 5).toNat, (a 1 + 7).toNat, (a 2 + 9).toNat, (a 3 + 12).toNat,
    (a 4 + 9).toNat, (a 5 + 6).toNat, (a 6 + 4).toNat, (a 7 + 2).toNat,
    r7, ⟨r6, ?_⟩, ⟨r5, ?_⟩, ⟨r4, ?_⟩, ⟨r3, ?_⟩, ⟨r2, ?_⟩, ⟨r0, ?_⟩, ⟨r1, ?_⟩, ?_⟩
  · simp only [S6, S7, t7, t6]; nlinarith [hs, sq_nonneg (2*a 0 - a 2), sq_nonneg (2*a 1 - a 3),
      sq_nonneg (3*a 2 - 2*a 3), sq_nonneg (5*a 3 - 6*a 4), sq_nonneg (4*a 4 - 5*a 5),
      sq_nonneg (3*a 5 - 4*a 6), sq_nonneg (2*a 6 - 3*a 7), sq_nonneg (a 7)]
  · simp only [S5, S6, S7, t7, t6, t5]; nlinarith [hs, sq_nonneg (2*a 0 - a 2),
      sq_nonneg (2*a 1 - a 3), sq_nonneg (3*a 2 - 2*a 3), sq_nonneg (5*a 3 - 6*a 4),
      sq_nonneg (4*a 4 - 5*a 5), sq_nonneg (3*a 5 - 4*a 6), sq_nonneg (2*a 6 - 3*a 7),
      sq_nonneg (a 7)]
  · simp only [S4, S5, S6, S7, t7, t6, t5, t4]; nlinarith [hs, sq_nonneg (2*a 0 - a 2),
      sq_nonneg (2*a 1 - a 3), sq_nonneg (3*a 2 - 2*a 3), sq_nonneg (5*a 3 - 6*a 4),
      sq_nonneg (4*a 4 - 5*a 5), sq_nonneg (3*a 5 - 4*a 6), sq_nonneg (2*a 6 - 3*a 7),
      sq_nonneg (a 7)]
  · simp only [S3, S4, S5, S6, S7, t7, t6, t5, t4, t3]; nlinarith [hs, sq_nonneg (2*a 0 - a 2),
      sq_nonneg (2*a 1 - a 3), sq_nonneg (3*a 2 - 2*a 3), sq_nonneg (5*a 3 - 6*a 4),
      sq_nonneg (4*a 4 - 5*a 5), sq_nonneg (3*a 5 - 4*a 6), sq_nonneg (2*a 6 - 3*a 7),
      sq_nonneg (a 7)]
  · simp only [S2, S3, S4, S5, S6, S7, t7, t6, t5, t4, t3, t2]
    nlinarith [hs, sq_nonneg (2*a 0 - a 2), sq_nonneg (2*a 1 - a 3),
      sq_nonneg (3*a 2 - 2*a 3), sq_nonneg (5*a 3 - 6*a 4), sq_nonneg (4*a 4 - 5*a 5),
      sq_nonneg (3*a 5 - 4*a 6), sq_nonneg (2*a 6 - 3*a 7), sq_nonneg (a 7)]
  · simp only [S0, S2, S3, S4, S5, S6, S7, t7, t6, t5, t4, t3, t2, t0]
    nlinarith [hs, sq_nonneg (2*a 0 - a 2), sq_nonneg (2*a 1 - a 3),
      sq_nonneg (3*a 2 - 2*a 3), sq_nonneg (5*a 3 - 6*a 4), sq_nonneg (4*a 4 - 5*a 5),
      sq_nonneg (3*a 5 - 4*a 6), sq_nonneg (2*a 6 - 3*a 7), sq_nonneg (a 7)]
  · simp only [S1, S0, S2, S3, S4, S5, S6, S7, t7, t6, t5, t4, t3, t2, t0, t1]
    linarith
  · simp only [vecOf, t0, t1, t2, t3, t4, t5, t6, t7]
    funext i
    fin_cases i <;> simp

private def alphaGood : Finset (Fin 8 → ℤ) := alphaCand.toFinset

private lemma alphaGood_card : alphaGood.card = 240 := by decide

private lemma mem_alphaGood (a : Fin 8 → ℤ) : a ∈ alphaGood ↔ Qalpha a = 2 := by
  rw [alphaGood, List.mem_toFinset]
  exact ⟨Qalpha_of_mem_alphaCand, mem_alphaCand⟩
private lemma Qmu_zero : Qmu (0 : Fin 8 → ℤ) = 0 := by
  simp [Qmu]

private lemma toMu_toAl (m : Fin 8 → ℤ) : CartanMatrix.E₈ *ᵥ (e8Inv *ᵥ m) = m := by
  rw [Matrix.mulVec_mulVec, e8Inv_mul, Matrix.one_mulVec]

private lemma toAl_toMu (a : Fin 8 → ℤ) : e8Inv *ᵥ (CartanMatrix.E₈ *ᵥ a) = a := by
  rw [Matrix.mulVec_mulVec, mul_e8Inv, Matrix.one_mulVec]

private lemma Qmu_eq_Qalpha_toAl (m : Fin 8 → ℤ) :
    Qmu m = (Qalpha (e8Inv *ᵥ m) : ℚ) := by
  conv_lhs => rw [← toMu_toAl m]
  rw [Qmu_toMu]


/-- **The roots of `E₈` form a finite set of cardinality `240`.**

This is the `Finset` form of the root count: the roots are the nonzero `μ : Fin 8 → ℤ` with
`μᵀA⁻¹μ = 2` for the `E₈` Cartan matrix `A = CartanMatrix.E₈`. -/
theorem exists_finset_e8_roots :
    ∃ s : Finset (Fin 8 → ℤ), (∀ μ, μ ∈ s ↔ μ ≠ 0 ∧
      (∑ i, ∑ j, (μ i : ℚ) * ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹) i j * (μ j : ℚ) = 2))
      ∧ s.card = 240 := by
  have hinj : Function.Injective (fun a : Fin 8 → ℤ => CartanMatrix.E₈ *ᵥ a) := by
    intro a b hab
    have hab' : CartanMatrix.E₈ *ᵥ a = CartanMatrix.E₈ *ᵥ b := hab
    have h1 : e8Inv *ᵥ (CartanMatrix.E₈ *ᵥ a) = a := by
      rw [Matrix.mulVec_mulVec, mul_e8Inv, Matrix.one_mulVec]
    have h2 : e8Inv *ᵥ (CartanMatrix.E₈ *ᵥ b) = b := by
      rw [Matrix.mulVec_mulVec, mul_e8Inv, Matrix.one_mulVec]
    rw [← h1, ← h2, hab']
  refine ⟨alphaGood.image (fun a : Fin 8 → ℤ => CartanMatrix.E₈ *ᵥ a), ?_, ?_⟩
  · intro μ
    show μ ∈ alphaGood.image (fun a : Fin 8 → ℤ => CartanMatrix.E₈ *ᵥ a) ↔ μ ≠ 0 ∧ Qmu μ = 2
    rw [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hQ : Qmu (CartanMatrix.E₈ *ᵥ a) = 2 := by
        rw [Qmu_eq_Qalpha_toAl, toAl_toMu]
        exact_mod_cast (mem_alphaGood a).mp ha
      refine ⟨?_, hQ⟩
      intro hzero
      rw [hzero, Qmu_zero] at hQ
      exact absurd hQ (by norm_num)
    · rintro ⟨_, hQ⟩
      refine ⟨e8Inv *ᵥ μ, ?_, ?_⟩
      · rw [mem_alphaGood]
        have hq : (Qalpha (e8Inv *ᵥ μ) : ℚ) = 2 := by
          rw [← Qmu_eq_Qalpha_toAl]
          exact hQ
        exact_mod_cast hq
      · exact toMu_toAl μ
  · rw [Finset.card_image_of_injective alphaGood hinj, alphaGood_card]

end Commons.Algebra.Lie.SerreConstruction