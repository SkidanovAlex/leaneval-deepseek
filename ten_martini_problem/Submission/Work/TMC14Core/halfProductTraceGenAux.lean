import Mathlib
import Submission.Work.TMC14Core.zero_aux

open Polynomial Matrix

noncomputable section

namespace Work.TMC14Core

def szp : Matrix (Fin 2) (Fin 2) ℂ[X] := !![1, 0; 0, -1]

def Mpol (a ζ : ℂ) (t : ℕ) : Matrix (Fin 2) (Fin 2) ℂ[X] :=
  !![C (a / 2 * ζ ^ t) * X ^ 2 + C (a / 2 * (ζ ^ t)⁻¹), -X; X, 0]

def Pmat (a ζ : ℂ) (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ[X] :=
  (List.map (Mpol a ζ) (List.range N)).prod

def Tpoly (a ζ : ℂ) (N : ℕ) : ℂ[X] := ((Pmat a ζ N) * szp).trace

def Rpoly (a ζ : ℂ) (N : ℕ) : ℂ[X] :=
  ∏ t ∈ Finset.range N, (C (a / 2 * ζ ^ t) * X ^ 2 + C (a / 2 * (ζ ^ t)⁻¹))

def xt (a ζ : ℂ) (u : ℂ) (t : ℕ) : ℂ := (a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹)

theorem Mpol_00_eq (a ζ : ℂ) (t : ℕ) :
    (Mpol a ζ t) 0 0 = C (a / 2 * ζ ^ t) * X ^ 2 + C (a / 2 * (ζ ^ t)⁻¹) := rfl

theorem Mpol_01_eq (a ζ : ℂ) (t : ℕ) : (Mpol a ζ t) 0 1 = -X := rfl

theorem Mpol_10_eq (a ζ : ℂ) (t : ℕ) : (Mpol a ζ t) 1 0 = X := rfl

theorem Mpol_11_eq (a ζ : ℂ) (t : ℕ) : (Mpol a ζ t) 1 1 = 0 := rfl

theorem Mpol_natDegree (a ζ : ℂ) (t : ℕ) (i j : Fin 2) :
    ((Mpol a ζ t) i j).natDegree ≤ (if i = j then 2 else 1) := by
  fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one,
    Fin.reduceEq, reduceIte]
  · rw [Mpol_00_eq, Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    simp [show m ≠ 2 by omega, show m ≠ 0 by omega]
  · rw [Mpol_01_eq, Polynomial.natDegree_neg]
    exact Polynomial.natDegree_X_le
  · rw [Mpol_10_eq]
    exact Polynomial.natDegree_X_le
  · rw [Mpol_11_eq, Polynomial.natDegree_zero]
    norm_num

theorem Mpol_deg_le_two (a ζ : ℂ) (t : ℕ) (i j : Fin 2) :
    ((Mpol a ζ t) i j).natDegree ≤ 2 := by
  refine le_trans (Mpol_natDegree a ζ t i j) ?_
  split <;> omega

theorem matrix_one_apply_fin2Aux (i j : Fin 2) :
    (1 : Matrix (Fin 2) (Fin 2) ℂ[X]) i j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp

@[simp] theorem Pmat_zero (a ζ : ℂ) : Pmat a ζ 0 = 1 := by simp [Pmat]

theorem Pmat_succ (a ζ : ℂ) (n : ℕ) :
    Pmat a ζ (n + 1) = Pmat a ζ n * Mpol a ζ n := by
  simp [Pmat, List.prod_range_succ]

theorem Pmat_natDegree_le (a ζ : ℂ) (n : ℕ) (i j : Fin 2) :
    ((Pmat a ζ n) i j).natDegree ≤ 2 * n := by
  induction n generalizing i j with
  | zero =>
    rw [Pmat_zero, matrix_one_apply_fin2Aux]
    by_cases h : i = j
    · simp [h, Polynomial.natDegree_one]
    · simp [h, Polynomial.natDegree_zero]
  | succ n ih =>
    have hm : ∀ (k j : Fin 2), ((Mpol a ζ n) k j).natDegree ≤ 2 := Mpol_deg_le_two a ζ n
    rw [Pmat_succ, Matrix.mul_apply, Fin.sum_univ_two]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans Polynomial.natDegree_mul_le (by have := ih i 0; have := hm 0 j; omega)
    · exact le_trans Polynomial.natDegree_mul_le (by have := ih i 1; have := hm 1 j; omega)

theorem Pmat_01_natDegree_le (a ζ : ℂ) : ∀ n, 1 ≤ n → ((Pmat a ζ n) 0 1).natDegree ≤ 2 * n - 1 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn
    rw [Pmat_succ, Matrix.mul_apply, Fin.sum_univ_two, Mpol_11_eq, mul_zero, add_zero]
    have key : ((Pmat a ζ n) 0 0 * (-X : ℂ[X])).natDegree ≤ 2 * n + 1 := by
      calc ((Pmat a ζ n) 0 0 * (-X : ℂ[X])).natDegree
          ≤ ((Pmat a ζ n) 0 0).natDegree + ((-X : ℂ[X])).natDegree := Polynomial.natDegree_mul_le
        _ = ((Pmat a ζ n) 0 0).natDegree + 1 := by rw [Polynomial.natDegree_neg, Polynomial.natDegree_X]
        _ ≤ 2 * n + 1 := by have := Pmat_natDegree_le a ζ n 0 0; omega
    have h : 2 * n + 1 = 2 * (n + 1) - 1 := by omega
    rwa [h] at key

theorem Pmat_11_natDegree_le (a ζ : ℂ) : ∀ n, 1 ≤ n → ((Pmat a ζ n) 1 1).natDegree ≤ 2 * n - 1 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn
    rw [Pmat_succ, Matrix.mul_apply, Fin.sum_univ_two, Mpol_11_eq, mul_zero, add_zero]
    have key : ((Pmat a ζ n) 1 0 * (-X : ℂ[X])).natDegree ≤ 2 * n + 1 := by
      calc ((Pmat a ζ n) 1 0 * (-X : ℂ[X])).natDegree
          ≤ ((Pmat a ζ n) 1 0).natDegree + ((-X : ℂ[X])).natDegree := Polynomial.natDegree_mul_le
        _ = ((Pmat a ζ n) 1 0).natDegree + 1 := by rw [Polynomial.natDegree_neg, Polynomial.natDegree_X]
        _ ≤ 2 * n + 1 := by have := Pmat_natDegree_le a ζ n 1 0; omega
    have h : 2 * n + 1 = 2 * (n + 1) - 1 := by omega
    rwa [h] at key


/-! ## The extreme coefficients of `Pmat` -/

theorem coeff_C_X_pow_mulAux (c : ℂ) (k m : ℕ) (P : ℂ[X]) :
    ((C c * X ^ k) * P).coeff (m + k) = c * P.coeff m := by
  rw [mul_assoc, Polynomial.coeff_C_mul]
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show X ^ (k + 1) * P = X * (X ^ k * P) from by rw [pow_succ]; ring,
      show m + (k + 1) = m + k + 1 from by ring, Polynomial.coeff_X_mul, ih]

theorem coeff_mul_C_X_pow (c : ℂ) (k m : ℕ) (P : ℂ[X]) :
    (P * (C c * X ^ k)).coeff (m + k) = P.coeff m * c := by
  rw [mul_comm, coeff_C_X_pow_mulAux, mul_comm]

theorem Pmat_00_coeff_top (a ζ : ℂ) (n : ℕ) :
    ((Pmat a ζ n) 0 0).coeff (2 * n) = ∏ t ∈ Finset.range n, (a / 2 * ζ ^ t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Pmat_succ, Matrix.mul_apply, Fin.sum_univ_two, Polynomial.coeff_add]
    have h01 : ((Pmat a ζ n) 0 1 * (Mpol a ζ n) 1 0).coeff (2 * (n + 1)) = 0 := by
      have hb : ((Pmat a ζ n) 0 1 * (Mpol a ζ n) 1 0).natDegree < 2 * (n + 1) := by
        calc ((Pmat a ζ n) 0 1 * (Mpol a ζ n) 1 0).natDegree
            ≤ ((Pmat a ζ n) 0 1).natDegree + ((Mpol a ζ n) 1 0).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ 2 * n + 1 := by
              have h1 := Pmat_natDegree_le a ζ n 0 1
              have h2 : ((Mpol a ζ n) 1 0 : ℂ[X]).natDegree ≤ 1 := by
                rw [Mpol_10_eq]; exact Polynomial.natDegree_X_le
              omega
          _ < 2 * (n + 1) := by omega
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hb
    rw [h01, add_zero]
    rw [Mpol_00_eq, mul_add, Polynomial.coeff_add]
    have h2 : ((Pmat a ζ n) 0 0 * C (a / 2 * (ζ ^ n)⁻¹)).coeff (2 * (n + 1)) = 0 := by
      have hb : ((Pmat a ζ n) 0 0 * C (a / 2 * (ζ ^ n)⁻¹)).natDegree < 2 * (n + 1) := by
        calc ((Pmat a ζ n) 0 0 * C (a / 2 * (ζ ^ n)⁻¹)).natDegree
            ≤ ((Pmat a ζ n) 0 0).natDegree + (C (a / 2 * (ζ ^ n)⁻¹) : ℂ[X]).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ 2 * n + 0 := by
              have := Pmat_natDegree_le a ζ n 0 0
              rw [Polynomial.natDegree_C]; omega
          _ < 2 * (n + 1) := by omega
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hb
    rw [h2, add_zero]
    have h3 : ((Pmat a ζ n) 0 0 * (C (a / 2 * ζ ^ n) * X ^ 2)).coeff (2 * (n + 1))
        = ((Pmat a ζ n) 0 0).coeff (2 * n) * (a / 2 * ζ ^ n) := by
      have : 2 * (n + 1) = 2 * n + 2 := by ring
      rw [this]
      exact coeff_mul_C_X_pow (a / 2 * ζ ^ n) 2 (2 * n) _
    rw [h3, ih, Finset.prod_range_succ]

theorem Pmat_00_coeff_bot (a ζ : ℂ) (n : ℕ) :
    ((Pmat a ζ n) 0 0).coeff 0 = ∏ t ∈ Finset.range n, (a / 2 * (ζ ^ t)⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Pmat_succ, Matrix.mul_apply, Fin.sum_univ_two, Polynomial.coeff_add]
    have h01 : ((Pmat a ζ n) 0 1 * (Mpol a ζ n) 1 0).coeff 0 = 0 := by
      rw [Mpol_10_eq, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul, Polynomial.eval_X,
        mul_zero]
    rw [h01, add_zero]
    rw [Mpol_00_eq, mul_add, Polynomial.coeff_add]
    have h2 : ((Pmat a ζ n) 0 0 * (C (a / 2 * ζ ^ n) * X ^ 2)).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simp
    rw [h2, zero_add, Polynomial.coeff_mul_C, ih, Finset.prod_range_succ]

/-! ## `Tpoly` -/

theorem Tpoly_eq (a ζ : ℂ) (N : ℕ) :
    Tpoly a ζ N = (Pmat a ζ N) 0 0 - (Pmat a ζ N) 1 1 := by
  rw [Tpoly, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, szp]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

theorem Tpoly_natDegree_le (a ζ : ℂ) (N : ℕ) : (Tpoly a ζ N).natDegree ≤ 2 * N := by
  rw [Tpoly_eq]
  exact le_trans (Polynomial.natDegree_sub_le _ _)
    (max_le (Pmat_natDegree_le a ζ N 0 0) (Pmat_natDegree_le a ζ N 1 1))

theorem Pmat_11_coeff_zero (a ζ : ℂ) {N : ℕ} (hN : 1 ≤ N) : ((Pmat a ζ N) 1 1).coeff 0 = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  rw [Pmat_succ, Matrix.mul_apply, Fin.sum_univ_two, Mpol_11_eq, mul_zero, add_zero, Mpol_01_eq]
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_X,
    neg_zero, mul_zero]

theorem Tpoly_coeff_zero (a ζ : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (Tpoly a ζ N).coeff 0 = ∏ t ∈ Finset.range N, (a / 2 * (ζ ^ t)⁻¹) := by
  rw [Tpoly_eq, Polynomial.coeff_sub, Pmat_00_coeff_bot, Pmat_11_coeff_zero a ζ hN, sub_zero]

theorem Tpoly_coeff_top (a ζ : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (Tpoly a ζ N).coeff (2 * N) = ∏ t ∈ Finset.range N, (a / 2 * ζ ^ t) := by
  have hdeg : ((Pmat a ζ N) 1 1).natDegree ≤ 2 * N - 1 := Pmat_11_natDegree_le a ζ N hN
  have h11 : ((Pmat a ζ N) 1 1).coeff (2 * N) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [Tpoly_eq, Polynomial.coeff_sub, Pmat_00_coeff_top, h11, sub_zero]


/-! ## Plumbing: evaluation of polynomial matrices -/

theorem Matrix.eval_mul_eval (A B : Matrix (Fin 2) (Fin 2) ℂ[X]) (V : ℂ) :
    (A * B).map (Polynomial.eval V) = A.map (Polynomial.eval V) * B.map (Polynomial.eval V) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, Fin.sum_univ_two, Polynomial.eval_add,
    Polynomial.eval_mul]

theorem Matrix.eval_one_eval (V : ℂ) :
    (1 : Matrix (Fin 2) (Fin 2) ℂ[X]).map (Polynomial.eval V) = 1 := by
  ext i j
  simp only [Matrix.map_apply, matrix_one_apply_fin2Aux, Matrix.one_apply]
  split <;> simp

theorem Matrix_prod_map_eval (l : List (Matrix (Fin 2) (Fin 2) ℂ[X])) (V : ℂ) :
    (l.prod).map (Polynomial.eval V) = (l.map (fun M => M.map (Polynomial.eval V))).prod := by
  induction l with
  | nil => simpa using Matrix.eval_one_eval V
  | cons M t ih => simp only [List.prod_cons, List.map_cons, ih, Matrix.eval_mul_eval]

theorem Matrix_prod_smul (l : List (Matrix (Fin 2) (Fin 2) ℂ)) (c : ℂ) :
    (l.map (fun M => c • M)).prod = c ^ l.length • l.prod := by
  induction l with
  | nil => simp
  | cons M t ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.length_cons, pow_succ, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]

theorem list_prod_smul_map {α : Type*} (l : List α) (f : α → Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) :
    (l.map (fun t => c • f t)).prod = c ^ l.length • (l.map f).prod := by
  induction l with
  | nil => simp
  | cons M t ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.length_cons, pow_succ, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]

theorem trace_map_evalAux (M : Matrix (Fin 2) (Fin 2) ℂ[X]) (V : ℂ) :
    (M.trace).eval V = (M.map (Polynomial.eval V)).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, Matrix.map_apply, Matrix.map_apply,
    Polynomial.eval_add]

theorem szp_map_eval (V : ℂ) : szp.map (Polynomial.eval V) = sz := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [szp, sz, Matrix.map_apply]

theorem scalar_shift (a ζ V : ℂ) (hζ0 : ζ ≠ 0) (t : ℕ) :
    (a / 2 * ζ ^ t) * (ζ * V) ^ 2 + a / 2 * (ζ ^ t)⁻¹
      = ζ * ((a / 2 * ζ ^ (t + 1)) * V ^ 2 + a / 2 * (ζ ^ (t + 1))⁻¹) := by
  rw [show ζ ^ (t + 1) = ζ ^ t * ζ from by rw [pow_succ]]
  field_simp <;> ring_nf

theorem scalar_eval (a ζ V : ℂ) (hV : V ≠ 0) (t : ℕ) :
    (a / 2 * ζ ^ t) * V ^ 2 + a / 2 * (ζ ^ t)⁻¹
      = V * (a / 2 * (V * ζ ^ t + (V * ζ ^ t)⁻¹)) := by
  field_simp <;> ring_nf

theorem Mpol_map_eval_shift (a ζ V : ℂ) (hζ0 : ζ ≠ 0) (t : ℕ) :
    (Mpol a ζ t).map (Polynomial.eval (ζ * V))
      = ζ • (Mpol a ζ (t + 1)).map (Polynomial.eval V) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.map_apply, Matrix.smul_apply,
      Mpol, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val', Matrix.cons_val_fin_one,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_neg, Polynomial.eval_zero, smul_eq_mul]
  · exact scalar_shift a ζ V hζ0 t
  all_goals ring

theorem Mpol_map_eval (a ζ V : ℂ) (hV : V ≠ 0) (t : ℕ) :
    (Mpol a ζ t).map (Polynomial.eval V) = V • S2 (xt a ζ V t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.map_apply, Matrix.smul_apply,
      Mpol, S2, xt, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val', Matrix.cons_val_fin_one,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_neg, Polynomial.eval_zero, smul_eq_mul]
  · exact scalar_eval a ζ V hV t
  all_goals ring

/-! ## The shifted product -/

def Bmat (a ζ : ℂ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ[X] :=
  (List.map (fun t => Mpol a ζ (t + 1)) (List.range n)).prod

theorem Pmat_cons (a ζ : ℂ) (n : ℕ) :
    Pmat a ζ (n + 1) = Mpol a ζ 0 * Bmat a ζ n := by
  rw [Pmat, Bmat, List.range_succ_eq_map, List.map_cons, List.map_map, List.prod_cons]
  rfl

theorem Bmat_succ (a ζ : ℂ) (n : ℕ) :
    Bmat a ζ (n + 1) = Bmat a ζ n * Mpol a ζ (n + 1) := by
  simp [Bmat, List.prod_range_succ]

theorem xt_shift_N (a ζ V : ℂ) {N : ℕ} (hζN : ζ ^ N = -1) :
    xt a ζ V N = -xt a ζ V 0 := by
  simp only [xt, hζN, pow_zero, mul_one, mul_neg, inv_neg]
  ring

theorem xt_shift_one (a ζ V : ℂ) (t : ℕ) :
    xt a ζ (ζ * V) t = xt a ζ V (t + 1) := by
  have h1 : (ζ * V) * ζ ^ t = V * ζ ^ (t + 1) := by rw [pow_succ]; ring
  simp only [xt, h1]

/-! ## Evaluation of `Tpoly` -/

theorem Pmat_map_eval (a ζ : ℂ) (N : ℕ) (V : ℂ) :
    (Pmat a ζ N).map (Polynomial.eval V)
      = (List.map (fun t => (Mpol a ζ t).map (Polynomial.eval V)) (List.range N)).prod := by
  rw [Pmat, Matrix_prod_map_eval, List.map_map]
  rfl

theorem Tpoly_eval_eq (a ζ : ℂ) (N : ℕ) (V : ℂ) (hV : V ≠ 0) :
    (Tpoly a ζ N).eval V
      = V ^ N * (((List.map (fun t => S2 (xt a ζ V t)) (List.range N)).prod) * sz).trace := by
  rw [Tpoly, trace_map_evalAux, Matrix.eval_mul_eval, szp_map_eval, Pmat_map_eval]
  have hpt : ∀ t ∈ List.range N,
      (Mpol a ζ t).map (Polynomial.eval V) = V • S2 (xt a ζ V t) :=
    fun t _ => Mpol_map_eval a ζ V hV t
  rw [List.map_congr_left hpt, list_prod_smul_map, List.length_range, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]

theorem trace_shift (a ζ : ℂ) {N : ℕ} (hN : 1 ≤ N) (hζN : ζ ^ N = -1) (V : ℂ) (hV : V ≠ 0) :
    (((List.map (fun t => S2 (xt a ζ V (t + 1))) (List.range N)).prod) * sz).trace
      = -(((List.map (fun t => S2 (xt a ζ V t)) (List.range N)).prod) * sz).trace := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  set L := (List.map (fun t => S2 (xt a ζ V (t + 1))) (List.range n)).prod with hL
  set M := S2 (xt a ζ V 0) with hM
  have hsplit : (List.map (fun t => S2 (xt a ζ V (t + 1))) (List.range (n + 1))).prod
      = L * S2 (xt a ζ V (n + 1)) := by rw [List.prod_range_succ, ← hL]
  have hcons : (List.map (fun t => S2 (xt a ζ V t)) (List.range (n + 1))).prod = M * L := by
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons]
    have hmap : (List.map (fun t => S2 (xt a ζ V t)) (List.map Nat.succ (List.range n)))
        = List.map (fun t => S2 (xt a ζ V (t + 1))) (List.range n) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro t _
      simp [Function.comp_apply, Nat.succ_eq_add_one]
    rw [hmap, ← hM, ← hL]
  have hxN : S2 (xt a ζ V (n + 1)) = -(sz * M * sz) := by
    rw [show xt a ζ V (n + 1) = -xt a ζ V 0 from xt_shift_N a ζ V hζN, hM, S2_neg]
  have hLL : L * (-(sz * M * sz)) * sz = -(L * sz * M) := by
    have h1 : L * (-(sz * M * sz)) * sz = L * (sz * M * sz) * sz * (-1) := by noncomm_ring
    have h2 : L * (sz * M * sz) * sz = L * sz * M * (sz * sz) := by noncomm_ring
    rw [h1, h2, sz_mul_sz]
    noncomm_ring
  have hMM : (M * L * sz).trace = (L * sz * M).trace := by
    calc (M * L * sz).trace = (sz * (M * L)).trace := by rw [Matrix.trace_mul_comm]
      _ = (sz * M * L).trace := by rw [← Matrix.mul_assoc]
      _ = (L * (sz * M)).trace := by rw [Matrix.trace_mul_comm]
      _ = (L * sz * M).trace := by rw [Matrix.mul_assoc]
  rw [hsplit, hxN, hcons, hLL, hMM, Matrix.trace_neg]

theorem Tpoly_eval_shift (a ζ : ℂ) {N : ℕ} (hN : 1 ≤ N) (hζ0 : ζ ≠ 0) (hζN : ζ ^ N = -1) :
    ∀ V, (Tpoly a ζ N).eval (ζ * V) = (Tpoly a ζ N).eval V := by
  intro V
  rcases eq_or_ne V 0 with rfl | hV
  · simp
  · have hζV : ζ * V ≠ 0 := mul_ne_zero hζ0 hV
    rw [Tpoly_eval_eq a ζ N (ζ * V) hζV, Tpoly_eval_eq a ζ N V hV]
    rw [List.map_congr_left (fun t _ => by rw [xt_shift_one a ζ V t]),
      trace_shift a ζ hN hζN V hV, mul_pow, hζN]
    ring

/-! ## The primitive root: `ζ^N = -1` and the root-of-unity product -/

theorem zeta_pow_eq_neg_one {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * N)) (hN : 1 ≤ N) :
    ζ ^ N = -1 := by
  have h2 : (ζ ^ N) ^ 2 = 1 := by
    rw [← pow_mul, show N * 2 = 2 * N by ring, hζ.pow_eq_one]
  have h1 : (ζ : ℂ) ^ N ≠ 1 := by
    intro h
    have hd := (hζ.pow_eq_one_iff_dvd N).mp h
    have := Nat.le_of_dvd (by omega : 0 < N) hd
    omega
  have h3 : (ζ ^ N - 1) * (ζ ^ N + 1) = 0 := by
    have : (ζ ^ N - 1) * (ζ ^ N + 1) = (ζ ^ N) ^ 2 - 1 := by ring
    rw [this, h2, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · have := add_eq_zero_iff_eq_neg.mp h
    exact this

theorem zeta_sq_prim {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * N)) :
    IsPrimitiveRoot (ζ ^ 2) N := by
  refine ⟨?_, ?_⟩
  · rw [← pow_mul, hζ.pow_eq_one]
  · intro l hl
    rw [← pow_mul] at hl
    have hd : 2 * N ∣ 2 * l := hζ.dvd_of_pow_eq_one (2 * l) hl
    rw [mul_comm 2 N, mul_comm 2 l] at hd
    exact (Nat.mul_dvd_mul_iff_right (by norm_num : 0 < 2)).mp hd

theorem rootUnityProd (ω c : ℂ) (N : ℕ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N) :
    ∏ t ∈ Finset.range N, (1 - c * ω ^ t) = 1 - c ^ N := by
  have h := X_pow_sub_C_eq_prod (R := ℂ) hω hN (show c ^ N = c ^ N from rfl)
  have h2 : (1 : ℂ) - c ^ N = ∏ i ∈ Finset.range N, (1 - ω ^ i * c) := by
    have hh := congrArg (Polynomial.eval (1 : ℂ)) h
    rw [show Polynomial.eval (1 : ℂ) (∏ i ∈ Finset.range N, (Polynomial.X - Polynomial.C (ω ^ i * c)))
        = ∏ i ∈ Finset.range N,
            Polynomial.eval (1 : ℂ) (Polynomial.X - Polynomial.C (ω ^ i * c)) from
      map_prod (Polynomial.evalRingHom (1 : ℂ))
        (fun i => Polynomial.X - Polynomial.C (ω ^ i * c)) (Finset.range N)] at hh
    simpa using hh
  rw [h2]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  ring

/-! ## The form of `Tpoly` -/

theorem Tpoly_coeff_mul (a ζ : ℂ) {N : ℕ} (hN : 1 ≤ N) (hζ0 : ζ ≠ 0) (hζN : ζ ^ N = -1)
    (m : ℕ) (hm : m ≤ 2 * N) : (Tpoly a ζ N).coeff m * (ζ ^ m - 1) = 0 := by
  have hnd := Tpoly_natDegree_le a ζ N
  set R : ℂ[X] := ∑ m ∈ Finset.range (2 * N + 1),
      C ((Tpoly a ζ N).coeff m * (ζ ^ m - 1)) * X ^ m with hR
  have hroot : ∀ V : ℂ, R.IsRoot V := by
    intro V
    rw [Polynomial.IsRoot.def, hR, Polynomial.eval_finsetSum]
    have hsum : (∑ m ∈ Finset.range (2 * N + 1),
          Polynomial.eval V (C ((Tpoly a ζ N).coeff m * (ζ ^ m - 1)) * X ^ m))
        = (Tpoly a ζ N).eval (ζ * V) - (Tpoly a ζ N).eval V := by
      have e1 : (Tpoly a ζ N).eval (ζ * V)
          = ∑ m ∈ Finset.range (2 * N + 1), (Tpoly a ζ N).coeff m * (ζ * V) ^ m :=
        Polynomial.eval_eq_sum_range' (by omega) _
      have e2 : (Tpoly a ζ N).eval V
          = ∑ m ∈ Finset.range (2 * N + 1), (Tpoly a ζ N).coeff m * V ^ m :=
        Polynomial.eval_eq_sum_range' (by omega) _
      rw [e1, e2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        mul_pow]
      ring
    rw [hsum, Tpoly_eval_shift a ζ hN hζ0 hζN V, sub_self]
  have hR0 : R = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot R (Set.infinite_univ.mono (fun x _ => hroot x))
  have hcoeff : R.coeff m = (Tpoly a ζ N).coeff m * (ζ ^ m - 1) := by
    rw [hR, Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro b _ hne
      rw [Polynomial.coeff_C_mul_X_pow, if_neg (fun h => hne h.symm)]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [← hcoeff, hR0, Polynomial.coeff_zero]

theorem Tpoly_form (a ζ : ℂ) {N : ℕ} (hN : 1 ≤ N) (hζ0 : ζ ≠ 0) (hζN : ζ ^ N = -1)
    (hprim : ∀ m, ζ ^ m = 1 → 2 * N ∣ m) :
    Tpoly a ζ N = C ((Tpoly a ζ N).coeff 0) + C ((Tpoly a ζ N).coeff (2 * N)) * X ^ (2 * N) := by
  have hnd := Tpoly_natDegree_le a ζ N
  have key : ∀ m, (Tpoly a ζ N).coeff m = 0 ∨ m = 0 ∨ m = 2 * N := by
    intro m
    by_cases hm : m ≤ 2 * N
    · rcases eq_or_ne m 0 with rfl | h0
      · exact Or.inr (Or.inl rfl)
      · rcases eq_or_ne m (2 * N) with rfl | h2N
        · exact Or.inr (Or.inr rfl)
        · left
          have h := Tpoly_coeff_mul a ζ hN hζ0 hζN m hm
          rcases mul_eq_zero.mp h with h1 | h2
          · exact h1
          · exfalso
            have hz : ζ ^ m = 1 := sub_eq_zero.mp h2
            obtain ⟨k, hk⟩ := hprim m hz
            have h2Npos : 0 < 2 * N := by omega
            have hble : 2 * N * k ≤ 2 * N := by rw [← hk]; exact hm
            have hk1 : k ≤ 1 :=
              Nat.le_of_mul_le_mul_left (by simpa using hble) h2Npos
            have hk0 : k ≠ 0 := by intro hk0; rw [hk0, mul_zero] at hk; exact h0 hk
            have hk1' : k = 1 := by omega
            rw [hk1', mul_one] at hk
            exact h2N hk
    · left
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hnd (by omega))
  have hN0 : N ≠ 0 := by omega
  ext m
  rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X_pow]
  rcases key m with h | rfl | rfl
  · rw [h]
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0; simp [h, hN0]
    · rcases eq_or_ne m (2 * N) with hm2 | hm2
      · subst hm2; simp [h, hN0]
      · simp [hm0, hm2, hN0]
  · simp [hN0]
  · simp [hN0]

/-! ## The product of the `ζ^t` -/

def zetaK (ζ : ℂ) (N : ℕ) : ℂ := ζ ^ (N * (N - 1) / 2)

theorem prod_zeta_pow (ζ : ℂ) (N : ℕ) :
    (∏ t ∈ Finset.range N, ζ ^ t) = zetaK ζ N := by
  rw [zetaK, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

theorem prod_zeta_pow_inv (ζ : ℂ) (N : ℕ) :
    (∏ t ∈ Finset.range N, (ζ ^ t)⁻¹) = (zetaK ζ N)⁻¹ := by
  rw [Finset.prod_inv_distrib, prod_zeta_pow]

theorem zetaK_sq (ζ : ℂ) {N : ℕ} (hN : 1 ≤ N) (hζN : ζ ^ N = -1) :
    zetaK ζ N * zetaK ζ N = -(-1 : ℂ) ^ N := by
  have heven : 2 ∣ N * (N - 1) := (Nat.even_mul_pred_self N).two_dvd
  have hK : N * (N - 1) / 2 * 2 = N * (N - 1) := Nat.div_mul_cancel heven
  have hsign : -(-1 : ℂ) ^ N = (-1) ^ (N - 1) := by
    have h1 : (-1 : ℂ) ^ N = (-1) ^ (N - 1) * (-1) := by
      nth_rewrite 1 [show N = (N - 1) + 1 by omega]
      rw [pow_succ]
    rw [h1]; ring
  rw [zetaK, ← pow_add, show N * (N-1) / 2 + N * (N-1) / 2 = N * (N-1) by omega,
    pow_mul, hζN, hsign]

theorem Tpoly_coeff_zero' (a ζ : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (Tpoly a ζ N).coeff 0 = (a / 2) ^ N * (zetaK ζ N)⁻¹ := by
  rw [Tpoly_coeff_zero a ζ hN, ← prod_zeta_pow_inv]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

theorem Tpoly_coeff_top' (a ζ : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (Tpoly a ζ N).coeff (2 * N) = (a / 2) ^ N * zetaK ζ N := by
  rw [Tpoly_coeff_top a ζ hN, ← prod_zeta_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

theorem halfProductTraceGenAux (N : ℕ) (hN : 1 ≤ N) (a u ζ : ℂ) (hu : u ≠ 0)
    (hζ : IsPrimitiveRoot ζ (2 * N)) :
    (((List.range N).map (fun t => Work.TMC14Core.S2 ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹)))).prod
        * Work.TMC14Core.sz).trace
      = ∏ t ∈ Finset.range N, ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹)) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hζN : ζ ^ N = -1 := zeta_pow_eq_neg_one hζ hN
  have hprim : ∀ m, ζ ^ m = 1 → 2 * N ∣ m := fun m hm => (hζ.pow_eq_one_iff_dvd m).mp hm
  have h1 : (Tpoly a ζ N).eval u
      = u ^ N * (((List.range N).map (fun t => S2 (xt a ζ u t))).prod * sz).trace :=
    Tpoly_eval_eq a ζ N u hu
  have hform := Tpoly_form a ζ hN hζ0 hζN hprim
  have h2 : (Tpoly a ζ N).eval u
      = (a / 2) ^ N * (zetaK ζ N)⁻¹ + (a / 2) ^ N * zetaK ζ N * u ^ (2 * N) := by
    rw [hform, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Tpoly_coeff_zero' a ζ hN, Tpoly_coeff_top' a ζ hN]
  have hxt : ∀ t, u * xt a ζ u t = (a / 2) * (u ^ 2 * ζ ^ t + (ζ ^ t)⁻¹) := by
    intro t
    have huu : u * (u * ζ ^ t)⁻¹ = (ζ ^ t)⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    simp only [xt]
    rw [show u * ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹))
        = (a / 2) * (u * (u * ζ ^ t) + u * (u * ζ ^ t)⁻¹) by ring, huu]
    ring
  have hfac : ∀ t, (a / 2) * (u ^ 2 * ζ ^ t + (ζ ^ t)⁻¹)
      = (a / 2) * (ζ ^ t)⁻¹ * (u ^ 2 * ζ ^ (2 * t) + 1) := by
    intro t
    have hz0 : (ζ ^ t : ℂ) ≠ 0 := pow_ne_zero _ hζ0
    rw [show ζ ^ (2 * t) = ζ ^ t * ζ ^ t from by rw [two_mul, pow_add]]
    field_simp <;> ring
  have hru : ∏ t ∈ Finset.range N, (u ^ 2 * ζ ^ (2 * t) + 1) = 1 - (-1 : ℂ) ^ N * u ^ (2 * N) := by
    have h := rootUnityProd (ζ ^ 2) (-(u ^ 2)) N (by omega) (zeta_sq_prim hζ)
    have hpt : ∀ t ∈ Finset.range N, (1 - (-(u ^ 2)) * (ζ ^ 2) ^ t) = (u ^ 2 * ζ ^ (2 * t) + 1) := by
      intro t _
      rw [← pow_mul]
      ring
    rw [Finset.prod_congr rfl hpt] at h
    rw [h, neg_pow, ← pow_mul] <;> ring
  have h3 : u ^ N * (∏ t ∈ Finset.range N, xt a ζ u t)
      = (a / 2) ^ N * (zetaK ζ N)⁻¹ * (1 - (-1 : ℂ) ^ N * u ^ (2 * N)) := by
    have hprod : u ^ N = ∏ t ∈ Finset.range N, u := by
      rw [Finset.prod_const, Finset.card_range]
    rw [hprod, ← Finset.prod_mul_distrib]
    rw [Finset.prod_congr rfl (fun t _ => hxt t)]
    rw [Finset.prod_congr rfl (fun t _ => hfac t)]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      prod_zeta_pow_inv, hru]
  have h4 : (a / 2) ^ N * (zetaK ζ N)⁻¹ + (a / 2) ^ N * zetaK ζ N * u ^ (2 * N)
      = (a / 2) ^ N * (zetaK ζ N)⁻¹ * (1 - (-1 : ℂ) ^ N * u ^ (2 * N)) := by
    have hzK0 : zetaK ζ N ≠ 0 := pow_ne_zero _ hζ0
    have key : zetaK ζ N * u ^ (2 * N) = -((zetaK ζ N)⁻¹ * ((-1 : ℂ) ^ N * u ^ (2 * N))) := by
      have this : -((zetaK ζ N)⁻¹ * ((-1 : ℂ) ^ N * u ^ (2 * N)))
          = (zetaK ζ N)⁻¹ * (zetaK ζ N * zetaK ζ N) * u ^ (2 * N) := by
        rw [zetaK_sq ζ hN hζN]; ring
      rw [this]
      field_simp <;> ring
    rw [mul_sub, mul_one, mul_assoc, key]
    ring
  have key2 : u ^ N * (((List.range N).map (fun t => S2 (xt a ζ u t))).prod * sz).trace
      = u ^ N * (∏ t ∈ Finset.range N, xt a ζ u t) := by
    rw [← h1, h2, h4, h3]
  exact mul_left_cancel₀ (pow_ne_zero N hu) key2
