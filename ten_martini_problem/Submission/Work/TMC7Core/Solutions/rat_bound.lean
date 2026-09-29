import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Rat
import Submission.Work.TMC7Core.Trig
import Submission.Work.TMC7Core.Trig.iterPoly_eval
import Submission.Work.TMC7Core.Trig.iterPoly_natDegree
import Submission.Work.TMC7Core.Trig.iterZ_smul
import Submission.Work.TMC7Core.Solutions.lyap_periodic
import Submission.Work.TMC7Core.Solutions.floquet_trace_bound

/-!
# The Lyapunov exponent at a rational frequency

For `α = p/q` (in lowest terms) and `E ∈ Σ_{λ,p/q}`, `L(E) ≤ max 0 (log|λ|) + log 6 / q`.
-/

namespace Work.TMC7Core.Solutions

open Polynomial Matrix
open Work.TMC7Core

/-! ## 0. The root of unity `ω = e^{2πi p/q}` -/

theorem norm_omega (α : ℝ) : ‖omega α‖ = 1 := by
  rw [omega, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero]

theorem omega_isPrimitiveRoot (p : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime (Int.natAbs p) q) :
    IsPrimitiveRoot (omega ((p : ℝ) / (q : ℝ))) q := by
  have h0 : q ≠ 0 := by omega
  have hi : IsCoprime p (q : ℤ) := Int.isCoprime_iff_nat_coprime.mpr hcop
  have h := Complex.isPrimitiveRoot_exp_of_isCoprime p q h0 hi
  convert h using 2
  rw [omega]
  push_cast
  ring

/-! ## 1. The trace polynomial of the algebraic cocycle -/

/-- The trace of the polynomial transfer matrix `iterPoly α lam E n`. -/
noncomputable def trP (α lam : ℝ) (E : ℂ) (n : ℕ) : ℂ[X] := (iterPoly α lam E n).trace

lemma eval_trace_eq (A : Matrix (Fin 2) (Fin 2) ℂ[X]) (z : ℂ) :
    (A.trace).eval z = (A.map (Polynomial.eval z)).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, Polynomial.eval_add]
  simp [Matrix.map_apply]

theorem trP_eval (α lam : ℝ) (E : ℂ) (n : ℕ) (z : ℂ) :
    (trP α lam E n).eval z = (iterZ α lam E n z).trace := by
  rw [trP, eval_trace_eq, Trig.iterPoly_eval]

lemma trP_natDegree_le (α lam : ℝ) (E : ℂ) (n : ℕ) : (trP α lam E n).natDegree ≤ 2 * n := by
  rw [trP, Matrix.trace_fin_two]
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (Trig.iterPoly_natDegree α lam E n 0 0) (Trig.iterPoly_natDegree α lam E n 1 1))

/-! ## 2. `matProd` and cyclic shifts of the trace -/

lemma matProd_drop_last (B : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    matProd B (n + 1) = matProd (fun j => B (j + 1)) n * B 0 := by
  induction n with
  | zero => simp [matProd]
  | succ n ih =>
    rw [matProd_succ B (n + 1), ih, matProd_succ (fun j => B (j + 1)) n, mul_assoc]

lemma matProd_shift_trace {B : ℕ → Matrix (Fin 2) (Fin 2) ℂ} {q : ℕ} (hq : 1 ≤ q)
    (hB : B q = B 0) :
    (matProd (fun j => B (j + 1)) q).trace = (matProd B q).trace := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq).symm⟩
  have hC : matProd (fun j => B (j + 1)) (m + 1)
      = B (m + 1) * matProd (fun j => B (j + 1)) m := matProd_succ _ m
  have hD : matProd B (m + 1) = matProd (fun j => B (j + 1)) m * B 0 := matProd_drop_last B m
  rw [hC, hD, Matrix.trace_mul_comm, hB]

lemma trace_iterZ_omega (α lam : ℝ) (E : ℂ) (q : ℕ) (hq : 1 ≤ q) (hω : omega α ^ q = 1)
    (z : ℂ) :
    (iterZ α lam E q (omega α * z)).trace = (iterZ α lam E q z).trace := by
  set B : ℕ → Matrix (Fin 2) (Fin 2) ℂ := fun j => tmZ lam E (z * omega α ^ j) with hBdef
  have h1 : iterZ α lam E q (omega α * z) = matProd (fun j => B (j + 1)) q := by
    rw [Trig.iterZ_eq_matProd]
    apply congrArg (fun f => matProd f q)
    funext j
    rw [hBdef]
    congr 1
    rw [pow_succ]
    ring
  have h2 : iterZ α lam E q z = matProd B q := Trig.iterZ_eq_matProd α lam E q z
  have hBq : B q = B 0 := by rw [hBdef]; simp [hω]
  rw [h1, h2]
  exact matProd_shift_trace hq hBq

theorem trP_omega_shift (α lam : ℝ) (E : ℂ) (q : ℕ) (hq : 1 ≤ q) (hω : omega α ^ q = 1) :
    (trP α lam E q).comp (C (omega α) * X) = trP α lam E q := by
  apply Polynomial.funext
  intro z
  rw [Polynomial.eval_comp, show Polynomial.eval z (C (omega α) * X) = omega α * z by simp]
  change (trP α lam E q).eval (omega α * z) = (trP α lam E q).eval z
  rw [trP_eval, trP_eval, trace_iterZ_omega α lam E q hq hω z]

/-! ## 3. Coefficients of a product of polynomial matrices -/

/-- The matrix of `d`-th coefficients of the entries of a polynomial matrix. -/
def coeffMat (d : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ[X]) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (A i j).coeff d

lemma trace_coeffMat (d : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ[X]) :
    (A.trace).coeff d = (coeffMat d A).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, Polynomial.coeff_add]
  rfl

lemma coeff_mul_le {p q : ℂ[X]} {a b : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  rw [Polynomial.coeff_mul]
  rw [Finset.sum_eq_single (a, b)]
  · intro x hx hxne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rcases lt_trichotomy x.1 a with h | h | h
    · have h2 : b < x.2 := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq h2), mul_zero]
    · exact absurd (Prod.ext h (by omega)) hxne
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp h), zero_mul]
  · intro hx
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (show a + b = a + b from rfl)) hx

lemma coeffMat_mul {A B : Matrix (Fin 2) (Fin 2) ℂ[X]} {a b : ℕ}
    (hA : Trig.MatDegLe A a) (hB : Trig.MatDegLe B b) :
    coeffMat (a + b) (A * B) = coeffMat a A * coeffMat b B := by
  ext i j
  rw [coeffMat, Matrix.mul_apply, Polynomial.finsetSum_coeff, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact coeff_mul_le (hA i k) (hB k j)

lemma coeffMat_one : coeffMat 0 (1 : Matrix (Fin 2) (Fin 2) ℂ[X]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coeffMat]

lemma coeffMat_iterPoly (α lam : ℝ) (E : ℂ) (n : ℕ) :
    coeffMat (2 * n) (iterPoly α lam E n)
      = matProd (fun j => coeffMat 2 (tmPoly lam E (omega α ^ j))) n := by
  induction n with
  | zero =>
    rw [show iterPoly α lam E 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ[X]) from rfl,
        show 2 * 0 = 0 from rfl, matProd_zero, coeffMat_one]
  | succ n ih =>
    rw [show iterPoly α lam E (n + 1)
          = tmPoly lam E (omega α ^ n) * iterPoly α lam E n from rfl,
        show 2 * (n + 1) = 2 + 2 * n from by omega,
        coeffMat_mul (Trig.matDegLe_tmPoly lam E (omega α ^ n))
          (Trig.matDegLe_iterPoly α lam E n),
        ih, matProd_succ]

/-! ## 4. The two extreme coefficients of `trP` -/

lemma trace_diag (a : ℂ) : (!![a, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ).trace = a := by
  rw [Matrix.trace_fin_two]; simp

lemma coeffMat_tmPoly (lam : ℝ) (E w : ℂ) :
    coeffMat 2 (tmPoly lam E w) = !![(-(lam : ℂ)) * w ^ 2, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  · show (tmPoly lam E w 0 0).coeff 2 = (-(lam : ℂ)) * w ^ 2
    rw [show tmPoly lam E w 0 0
          = C (E : ℂ) * (C w * X) - C (lam : ℂ) * ((C w * X) ^ 2 + 1) from rfl]
    have hsq : (C w * X : ℂ[X]) ^ 2 = C (w ^ 2) * X ^ 2 := by
      rw [show (C w * X : ℂ[X]) = (monomial 1) w from Polynomial.C_mul_X_eq_monomial,
          show (C (w ^ 2) * X ^ 2 : ℂ[X]) = (monomial 2) (w ^ 2)
            from Polynomial.C_mul_X_pow_eq_monomial,
          sq, Polynomial.monomial_mul_monomial]
      congr 1
      ring
    rw [Polynomial.coeff_sub,
        show (C (E : ℂ) * (C w * X) : ℂ[X]).coeff 2 = 0 from by
          rw [Polynomial.coeff_C_mul]; simp,
        show (C (lam : ℂ) * ((C w * X) ^ 2 + 1) : ℂ[X]).coeff 2 = (lam : ℂ) * w ^ 2 from by
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_one, hsq,
              Polynomial.coeff_C_mul_X_pow]
          norm_num]
    ring
  · show (tmPoly lam E w 0 1).coeff 2 = 0
    rw [show tmPoly lam E w 0 1 = -(C w * X) from rfl, Polynomial.coeff_neg,
        Polynomial.coeff_C_mul, Polynomial.coeff_X]
    norm_num
  · show (tmPoly lam E w 1 0).coeff 2 = 0
    rw [show tmPoly lam E w 1 0 = C w * X from rfl,
        Polynomial.coeff_C_mul, Polynomial.coeff_X]
    norm_num
  · show (tmPoly lam E w 1 1).coeff 2 = 0
    rw [show tmPoly lam E w 1 1 = (0 : ℂ[X]) from rfl]
    simp

lemma matProd_diag (a : ℕ → ℂ) {q : ℕ} (hq : 1 ≤ q) :
    matProd (fun j => !![a j, 0; 0, 0]) q = !![∏ j ∈ Finset.range q, a j, 0; 0, 0] := by
  have hfun : (fun j => !![a j, 0; 0, 0])
      = fun j => a j • (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext j; ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.smul_apply]
  rw [hfun, Trig.matProd_smul]
  have hP : ∀ m, matProd (fun _ => (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) (m + 1)
      = !![1, 0; 0, 0] := by
    intro m
    induction m with
    | zero => rw [Nat.zero_add, matProd_succ, matProd_zero, mul_one]
    | succ m ih =>
      rw [matProd_succ, ih]
      ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq).symm⟩
  rw [hP m]
  ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.smul_apply]

lemma trP_coeff_top (α lam : ℝ) (E : ℂ) (q : ℕ) :
    (trP α lam E q).coeff (2 * q)
      = (matProd (fun j => coeffMat 2 (tmPoly lam E (omega α ^ j))) q).trace := by
  rw [trP, trace_coeffMat, coeffMat_iterPoly]

lemma trP_coeff_top_value (α lam : ℝ) (E : ℂ) (q : ℕ) (hq : 1 ≤ q) :
    (trP α lam E q).coeff (2 * q)
      = ∏ j ∈ Finset.range q, (-(lam : ℂ) * (omega α) ^ (2 * j)) := by
  rw [trP_coeff_top]
  conv_lhs => rw [show (fun j => coeffMat 2 (tmPoly lam E (omega α ^ j)))
      = (fun j => !![(-(lam : ℂ)) * (omega α ^ j) ^ 2, 0; 0, 0]) from by
        funext j; rw [coeffMat_tmPoly]]
  rw [matProd_diag (fun j => (-(lam : ℂ)) * (omega α ^ j) ^ 2) hq, trace_diag]
  apply Finset.prod_congr rfl
  intro j _
  rw [← pow_mul, Nat.mul_comm j 2]

lemma norm_trP_coeff_top (α lam : ℝ) (E : ℂ) (q : ℕ) (hq : 1 ≤ q) :
    ‖(trP α lam E q).coeff (2 * q)‖ = |lam| ^ q := by
  rw [trP_coeff_top_value α lam E q hq, norm_prod]
  have hterm : ∀ j : ℕ, ‖(-(lam : ℂ) * (omega α) ^ (2 * j))‖ = |lam| := by
    intro j
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pow, norm_omega α,
        one_pow, mul_one]
  simp_rw [hterm]
  rw [Finset.prod_const, Finset.card_range]

lemma tmZ_zero (lam : ℝ) (E : ℂ) : tmZ lam E 0 = !![(-(lam : ℂ)), 0; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tmZ]

lemma trP_coeff_zero (α lam : ℝ) (E : ℂ) (q : ℕ) (hq : 1 ≤ q) :
    (trP α lam E q).coeff 0 = (-(lam : ℂ)) ^ q := by
  rw [Polynomial.coeff_zero_eq_eval_zero, trP_eval, Trig.iterZ_eq_matProd]
  rw [show (fun j => tmZ lam E (0 * omega α ^ j)) = (fun _ => !![(-(lam : ℂ)), 0; 0, 0]) from by
    funext j; rw [zero_mul, tmZ_zero]]
  rw [matProd_diag (fun _ => (-(lam : ℂ))) hq, trace_diag, Finset.prod_const, Finset.card_range]

lemma norm_trP_coeff_zero (α lam : ℝ) (E : ℂ) (q : ℕ) (hq : 1 ≤ q) :
    ‖(trP α lam E q).coeff 0‖ = |lam| ^ q := by
  rw [trP_coeff_zero α lam E q hq, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs]

/-! ## 5. `trP` has only the frequencies `0, q, 2q` -/

lemma trP_coeff_eq_zero_of_not_dvd (α lam : ℝ) (E : ℂ) (q : ℕ) (hq : 1 ≤ q)
    (hζ : IsPrimitiveRoot (omega α) q) {k : ℕ} (hk : ¬ q ∣ k) :
    (trP α lam E q).coeff k = 0 := by
  have hcomp := trP_omega_shift α lam E q hq hζ.pow_eq_one
  have h := congrArg (fun p : ℂ[X] => p.coeff k) hcomp
  rw [Polynomial.comp_C_mul_X_coeff] at h
  have h2 : (trP α lam E q).coeff k * (omega α ^ k - 1) = 0 := by
    rw [mul_sub, mul_one]
    exact sub_eq_zero.mpr h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd ((hζ.pow_eq_one_iff_dvd k).mp (sub_eq_zero.mp h3)) hk

lemma trP_three_term (α lam : ℝ) (E : ℂ) (q : ℕ) (hq : 1 ≤ q)
    (hζ : IsPrimitiveRoot (omega α) q) :
    trP α lam E q
      = C ((trP α lam E q).coeff 0) + C ((trP α lam E q).coeff q) * X ^ q
        + C ((trP α lam E q).coeff (2 * q)) * X ^ (2 * q) := by
  ext k
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X_pow]
  by_cases hk0 : k = 0
  · rw [hk0, if_pos rfl, if_neg (by omega : ¬ (0 : ℕ) = q), if_neg (by omega : ¬ (0 : ℕ) = 2 * q)]
    ring
  by_cases hkq : k = q
  · rw [hkq, if_neg (by omega : ¬ q = 0), if_pos rfl, if_neg (by omega : ¬ q = 2 * q)]
    ring
  by_cases hk2 : k = 2 * q
  · rw [hk2, if_neg (by omega : ¬ 2 * q = 0), if_neg (by omega : ¬ 2 * q = q), if_pos rfl]
    ring
  · rw [if_neg hk0, if_neg hkq, if_neg hk2]
    simp only [add_zero]
    rcases lt_or_ge k (2 * q) with hlt | hge
    · exact trP_coeff_eq_zero_of_not_dvd α lam E q hq hζ (by
        intro hdvd
        obtain ⟨m, hm⟩ := hdvd
        have hmpos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h | h
          · subst h; simp at hm; omega
          · exact h
        have hmq : m * q < 2 * q := by rw [Nat.mul_comm m q, ← hm]; exact hlt
        have hm2 : m < 2 := (Nat.mul_lt_mul_right (by omega : 0 < q)).mp hmq
        have hm1 : m = 1 := by omega
        subst hm1
        simp at hm
        omega)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (trP_natDegree_le α lam E q) (lt_of_le_of_ne hge (Ne.symm hk2)))

lemma trP_eval_three (α lam : ℝ) (E : ℂ) (q : ℕ) (hq : 1 ≤ q)
    (hζ : IsPrimitiveRoot (omega α) q) (z : ℂ) :
    (trP α lam E q).eval z
      = (trP α lam E q).coeff 0 + (trP α lam E q).coeff q * z ^ q
        + (trP α lam E q).coeff (2 * q) * z ^ (2 * q) := by
  conv_lhs => rw [trP_three_term α lam E q hq hζ]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]

/-! ## 6. The trace oscillation bound -/

lemma trP_trace_relation (α lam : ℝ) (E : ℂ) (q : ℕ) (hq : 1 ≤ q)
    (hζ : IsPrimitiveRoot (omega α) q) (y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * y) ^ q * (omega α) ^ (q * (q - 1) / 2)
        * (iterC α lam E q y).trace
      = (trP α lam E q).coeff 0
        + (trP α lam E q).coeff q * Complex.exp (2 * Real.pi * Complex.I * y) ^ q
        + (trP α lam E q).coeff (2 * q) * Complex.exp (2 * Real.pi * Complex.I * y) ^ (2 * q) := by
  rw [← trP_eval_three α lam E q hq hζ (Complex.exp (2 * Real.pi * Complex.I * y))]
  rw [trP_eval, Trig.iterZ_smul, Matrix.trace_smul, smul_eq_mul]

theorem trace_oscillation (p : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime (Int.natAbs p) q) (lam E : ℝ) (x : ℝ) :
    ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace
        - (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace‖ ≤ 4 * |lam| ^ q := by
  set ω : ℂ := omega ((p : ℝ) / (q : ℝ)) with hωdef
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * x) with hzdef
  set w : ℂ := z ^ q with hwdef
  set T : ℂ := (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace with hTdef
  set T0 : ℂ := (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace with hT0def
  set c : ℕ := q * (q - 1) / 2 with hcdef
  set c0 : ℂ := (trP ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q).coeff 0 with hc0def
  set c1 : ℂ := (trP ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q).coeff q with hc1def
  set c2 : ℂ := (trP ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q).coeff (2 * q) with hc2def
  have hζ : IsPrimitiveRoot ω q := by
    rw [hωdef]; exact omega_isPrimitiveRoot p q hq hcop
  have hznorm : ‖z‖ = 1 := by
    rw [hzdef, Complex.norm_exp]
    have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [h, Real.exp_zero]
  have hwnorm : ‖w‖ = 1 := by rw [hwdef, norm_pow, hznorm]; simp
  have hωnorm : ‖ω‖ = 1 := by rw [hωdef]; exact norm_omega _
  have hωcnorm : ‖ω ^ c‖ = 1 := by rw [norm_pow, hωnorm]; simp
  have hc0norm : ‖c0‖ = |lam| ^ q := by
    rw [hc0def]; exact norm_trP_coeff_zero _ _ _ _ hq
  have hc2norm : ‖c2‖ = |lam| ^ q := by
    rw [hc2def]; exact norm_trP_coeff_top _ _ _ _ hq
  have hzw : z ^ (2 * q) = w ^ 2 := by
    rw [show 2 * q = q * 2 from by omega, pow_mul, ← hwdef]
  have hx : w * ω ^ c * T = c0 + c1 * w + c2 * w ^ 2 := by
    have h := trP_trace_relation ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q hq hζ x
    rw [← hzdef, hzw, ← hwdef, ← hTdef, ← hc0def, ← hc1def, ← hc2def, ← hcdef] at h
    simpa using h
  have h0 : ω ^ c * T0 = c0 + c1 + c2 := by
    have h := trP_trace_relation ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q hq hζ 0
    rw [← hT0def, ← hc0def, ← hc1def, ← hc2def, ← hcdef] at h
    simpa using h
  have hAlg : ω ^ c * w * (T - T0) = (1 - w) * (c0 - c2 * w) := by
    have e2 : w * ω ^ c * T0 = w * (c0 + c1 + c2) := by rw [mul_assoc, h0]
    linear_combination hx - e2
  have hstep1 : ‖ω ^ c * w * (T - T0)‖ = ‖T - T0‖ := by
    rw [norm_mul, norm_mul, hωcnorm, hwnorm, one_mul, one_mul]
  calc ‖T - T0‖ = ‖ω ^ c * w * (T - T0)‖ := hstep1.symm
    _ = ‖(1 - w) * (c0 - c2 * w)‖ := by rw [hAlg]
    _ = ‖1 - w‖ * ‖c0 - c2 * w‖ := norm_mul _ _
    _ ≤ 2 * (2 * |lam| ^ q) := by
        apply mul_le_mul
        · calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
            _ = 2 := by rw [norm_one, hwnorm]; norm_num
        · calc ‖c0 - c2 * w‖ ≤ ‖c0‖ + ‖c2 * w‖ := norm_sub_le _ _
            _ = |lam| ^ q + |lam| ^ q := by rw [norm_mul, hwnorm, mul_one, hc0norm, hc2norm]
            _ = 2 * |lam| ^ q := by ring
        · positivity
        · positivity
    _ = 4 * |lam| ^ q := by ring

/-! ## 7. The pointwise bound `log ρ(A_q(x)) ≤ q·log⁺|λ| + log 6` -/

lemma abs_re_trace_bound (p : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime (Int.natAbs p) q) (h1 : P_OpBasics) (h15 : P_Schnol)
    (lam E : ℝ) (hE : E ∈ amoSpec ((p : ℝ) / (q : ℝ)) lam) (x : ℝ) :
    |((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re| ≤ 2 + 4 * |lam| ^ q := by
  have himx := trace_iterC_im_zero ((p : ℝ) / (q : ℝ)) lam E q x
  have him0 := trace_iterC_im_zero ((p : ℝ) / (q : ℝ)) lam E q 0
  have hxeq := trace_eq_ofReal_re himx
  have h0eq := trace_eq_ofReal_re him0
  have hfl := floquet_trace_bound h1 h15 p q hq lam E hE
  have h0b : |((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace).re| ≤ 2 := by
    have h : ‖((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace)‖
        = |((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace).re| := by
      conv_lhs => rw [h0eq]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h] at hfl
    exact hfl
  have hosc : |((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re
      - ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace).re| ≤ 4 * |lam| ^ q := by
    have h := trace_oscillation p q hq hcop lam E x
    have hsub : (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace
        - (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace
        = ((((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re
            - ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace).re : ℝ) : ℂ) := by
      rw [hxeq, h0eq]
      simp only [Complex.ofReal_re]
      push_cast
      ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  calc |((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re|
      = |((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace).re
          + (((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re
              - ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace).re)| := by
          rw [show ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace).re
                + (((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re
                    - ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace).re)
              = ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re from by ring]
    _ ≤ |((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace).re|
          + |((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re
              - ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace).re| := abs_add_le _ _
    _ ≤ 2 + 4 * |lam| ^ q := add_le_add h0b hosc

lemma rhoSL_eq_max (τ : ℝ) : rhoSL τ = max 1 ((|τ| + Real.sqrt (τ ^ 2 - 4)) / 2) := by
  rw [rhoSL]
  split_ifs with h
  · rw [max_eq_right (by linarith [Real.sqrt_nonneg (τ ^ 2 - 4), abs_nonneg τ])]
  · push Not at h
    rw [max_eq_left (by
      rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith [sq_abs τ, abs_nonneg τ, h])]
      linarith)]

lemma rhoSL_log_bound (p : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime (Int.natAbs p) q) (h1 : P_OpBasics) (h15 : P_Schnol)
    (lam E : ℝ) (hE : E ∈ amoSpec ((p : ℝ) / (q : ℝ)) lam) (x : ℝ) :
    Real.log (rhoSL (((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re))
      ≤ (q : ℝ) * max 0 (Real.log |lam|) + Real.log 6 := by
  set τ : ℝ := ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re with hτdef
  have hτb : |τ| ≤ 2 + 4 * |lam| ^ q := abs_re_trace_bound p q hq hcop h1 h15 lam E hE x
  have hρ : rhoSL τ ≤ 2 + 4 * |lam| ^ q := by
    refine le_trans (rhoSL_le τ) ?_
    rw [max_le_iff]
    exact ⟨by have h := pow_nonneg (abs_nonneg lam) q; linarith, hτb⟩
  have hlog : Real.log (rhoSL τ) ≤ Real.log (2 + 4 * |lam| ^ q) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (rhoSL_one_le τ)) hρ
  refine le_trans hlog ?_
  rcases lt_or_ge (1 : ℝ) |lam| with ha | ha
  · have ha1 : 1 ≤ |lam| := le_of_lt ha
    have haq1 : 1 ≤ |lam| ^ q := one_le_pow₀ ha1
    have h6 : 2 + 4 * |lam| ^ q ≤ 6 * |lam| ^ q := by linarith
    have h1' := Real.log_le_log (by have h := pow_nonneg (abs_nonneg lam) q; linarith : (0 : ℝ) < 2 + 4 * |lam| ^ q) h6
    have hmul : Real.log (6 * |lam| ^ q) = Real.log 6 + (q : ℝ) * Real.log |lam| := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    rw [hmul] at h1'
    rw [max_eq_right (Real.log_nonneg ha1)]
    linarith
  · have haq : |lam| ^ q ≤ 1 := pow_le_one₀ (abs_nonneg lam) ha
    have h6 : 2 + 4 * |lam| ^ q ≤ 6 := by linarith
    have h1' := Real.log_le_log (by have h := pow_nonneg (abs_nonneg lam) q; linarith : (0 : ℝ) < 2 + 4 * |lam| ^ q) h6
    rw [max_eq_left (Real.log_nonpos (abs_nonneg lam) ha), mul_zero, zero_add]
    linarith

lemma continuous_log_rhoSL_trace (p : ℤ) (q : ℕ) (lam E : ℝ) :
    Continuous (fun x : ℝ =>
      Real.log (rhoSL (((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re))) := by
  have htr : Continuous (fun x : ℝ =>
      ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re) :=
    Complex.continuous_re.comp (continuous_iterC _ lam (E : ℂ) q).matrix_trace
  have hrho : Continuous (fun x : ℝ =>
      rhoSL (((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re)) := by
    simp only [rhoSL_eq_max]
    exact continuous_const.max (((continuous_abs.comp htr).add
      (Real.continuous_sqrt.comp (by fun_prop))).div_const 2)
  exact hrho.log (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (rhoSL_one_le _)))

/-! ## 8. The rational bound -/

theorem rat_bound (h1 : P_OpBasics) (h15 : P_Schnol) (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime (Int.natAbs p) q) (lam : ℝ) (E : ℝ) (hE : E ∈ amoSpec ((p : ℝ) / (q : ℝ)) lam) : lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ) ≤ max 0 (Real.log |lam|) + Real.log 6 / (q : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [lyap_periodic p q hq lam E]
  have hcont := continuous_log_rhoSL_trace p q lam E
  have hint := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (show (0 : ℝ) ≤ 1 by norm_num)
    (hcont.intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)
    (fun x _ => rhoSL_log_bound p q hq hcop h1 h15 lam E hE x)
  have hg : (∫ x in (0 : ℝ)..1, ((q : ℝ) * max 0 (Real.log |lam|) + Real.log 6))
      = (q : ℝ) * max 0 (Real.log |lam|) + Real.log 6 := by
    rw [intervalIntegral.integral_const]
    simp
  rw [hg] at hint
  calc (1 / (q : ℝ)) * (∫ x in (0 : ℝ)..1,
        Real.log (rhoSL (((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re)))
      ≤ (1 / (q : ℝ)) * ((q : ℝ) * max 0 (Real.log |lam|) + Real.log 6) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = max 0 (Real.log |lam|) + Real.log 6 / (q : ℝ) := by
        have h1 : (1 : ℝ) / (q : ℝ) * ((q : ℝ) * max 0 (Real.log |lam|))
            = max 0 (Real.log |lam|) := by
          rw [← mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hq0), one_mul]
        have h2 : (1 : ℝ) / (q : ℝ) * Real.log 6 = Real.log 6 / (q : ℝ) := by
          rw [one_div, inv_mul_eq_div]
        rw [mul_add, h1, h2]

end Work.TMC7Core.Solutions
