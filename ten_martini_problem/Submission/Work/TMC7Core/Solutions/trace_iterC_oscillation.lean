import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Trig
import Submission.Work.TMC7Core.Trig.iterPoly_eval
import Submission.Work.TMC7Core.Trig.iterPoly_natDegree
import Submission.Work.TMC7Core.Trig.iterZ_smul
import Submission.Work.TMC7Core.Trig.tmZ_smul

namespace Work.TMC7Core.Solutions

open Polynomial Matrix Finset
open Work.TMC7Core

noncomputable section

/-! ## `ω = e^{2πiα}` for `α = p/q` has order `q` -/

theorem omega_norm (α : ℝ) : ‖omega α‖ = 1 := by
  rw [omega, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [h, Real.exp_zero]

theorem omega_pow_eq_one_iff (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime (Int.natAbs p) q)
    (m : ℕ) : (omega ((p : ℝ) / (q : ℝ))) ^ m = 1 ↔ q ∣ m := by
  have hqC : (q : ℂ) ≠ 0 := by
    have : (q : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [omega, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hX : (2*(Real.pi:ℂ)*Complex.I) * ((↑m:ℂ)*((↑p:ℂ)/(↑q:ℂ)))
        = (2*(Real.pi:ℂ)*Complex.I) * (n:ℂ) := by
      have hn' := hn
      push_cast at hn'
      linear_combination hn'
    have h1 : (↑m : ℂ) * ((↑p:ℂ)/(↑q:ℂ)) = (n : ℂ) := mul_left_cancel₀ hI hX
    have h7 : (↑m : ℂ) * (↑p : ℂ) = (↑n : ℂ) * (↑q : ℂ) := by
      have h2 : (↑m : ℂ) * (↑p : ℂ) / (↑q : ℂ) = (↑n : ℂ) := by rw [mul_div_assoc]; exact h1
      rw [div_eq_iff hqC] at h2; exact h2
    have h6 : (m:ℤ) * p = n * (q:ℤ) := by
      rw [← Int.cast_inj (α := ℂ)]; push_cast; exact h7
    have h8 : (q:ℤ) ∣ (m:ℤ) * p := ⟨n, by rw [h6]; ring⟩
    have hcop' : IsCoprime (q:ℤ) p := by
      rw [Int.isCoprime_iff_nat_coprime]; simpa using hcop.symm
    have h9 : (q:ℤ) ∣ (m:ℤ) := hcop'.dvd_of_dvd_mul_left (by rwa [mul_comm] at h8)
    have h10 : q ∣ ((m:ℤ)).natAbs := Int.natCast_dvd.mp h9
    simpa using h10
  · intro hdvd
    obtain ⟨k, rfl⟩ := hdvd
    refine ⟨p * (k:ℤ), ?_⟩
    push_cast <;> field_simp <;> ring

/-! ## Polynomial coefficient lemmas -/

lemma poly_coeff_mul_top (p r : ℂ[X]) (m n : ℕ) (hp : p.natDegree ≤ m) (hr : r.natDegree ≤ n) :
    (p * r).coeff (m + n) = p.coeff m * r.coeff n := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_single (m, n) ?_ ?_
  · rintro ⟨i, j⟩ hmem hij
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmem
    rcases lt_trichotomy i m with h | h | h
    · have hj : n < j := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hr hj), mul_zero]
    · exact absurd (Prod.ext h (by omega)) hij
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp h), zero_mul]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by ring)) h

lemma poly_comp_coeff (P : ℂ[X]) (c : ℂ) (m : ℕ) :
    (P.comp (C c * X)).coeff m = P.coeff m * c ^ m := by
  induction P using Polynomial.induction_on' with
  | add p r hp hr =>
      rw [Polynomial.add_comp, Polynomial.coeff_add, Polynomial.coeff_add, hp, hr]
      ring
  | monomial k a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]
      rw [show (C c * X : ℂ[X]) ^ k = C (c ^ k) * X ^ k from by
        rw [mul_pow, ← Polynomial.C_pow]]
      rw [show (C a * (C (c ^ k) * X ^ k) : ℂ[X]) = C (a * c ^ k) * X ^ k from by
        rw [← mul_assoc, ← Polynomial.C_mul]]
      simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases h : m = k
      · subst h; ring
      · simp [h]

lemma trace_coeff (M : Matrix (Fin 2) (Fin 2) ℂ[X]) (n : ℕ) :
    M.trace.coeff n = (M.map (fun p => p.coeff n)).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, Polynomial.coeff_add]
  rfl

lemma trace_eval (M : Matrix (Fin 2) (Fin 2) ℂ[X]) (z : ℂ) :
    M.trace.eval z = (M.map (Polynomial.eval z)).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, Polynomial.eval_add]
  rfl

lemma map_coeff_mul (A B : Matrix (Fin 2) (Fin 2) ℂ[X]) (m n : ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ m) (hB : ∀ i j, (B i j).natDegree ≤ n) :
    (A * B).map (fun p => p.coeff (m + n))
      = (A.map (fun p => p.coeff m)) * (B.map (fun p => p.coeff n)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k _
  exact poly_coeff_mul_top (A i k) (B k j) m n (hA i k) (hB k j)

lemma tmPoly_eq' (lam : ℝ) (E : ℂ) (w : ℂ) :
    tmPoly lam E w =
      !![C E * (C w * X) - C (lam:ℂ) * (C (w^2) * X^2 + 1), -(C w * X); C w * X, 0] := by
  unfold tmPoly
  rw [show (C w * X : ℂ[X]) ^ 2 = C (w ^ 2) * X ^ 2 from by
    rw [show (C w * X : ℂ[X]) ^ 2 = (C w) ^ 2 * X ^ 2 from by ring, ← Polynomial.C_pow]]

lemma tmPoly_coeff_two (lam : ℝ) (E : ℂ) (w : ℂ) :
    (tmPoly lam E w).map (fun p => p.coeff 2)
      = Matrix.diagonal (fun i : Fin 2 => if i = 0 then (-(lam : ℂ)) * w ^ 2 else 0) := by
  rw [tmPoly_eq']
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.diagonal_apply]
  · show (C E * (C w * X) - C (lam:ℂ) * (C (w^2) * X^2 + 1) : ℂ[X]).coeff 2 = (-(lam:ℂ))*w^2
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_one]
    norm_num
  · show (-(C w * X) : ℂ[X]).coeff 2 = (0:ℂ); simp [Polynomial.coeff_C_mul, Polynomial.coeff_X]
  · show (C w * X : ℂ[X]).coeff 2 = (0:ℂ); simp [Polynomial.coeff_C_mul, Polynomial.coeff_X]
  · show (0 : ℂ[X]).coeff 2 = (0:ℂ); simp

lemma iterPoly_zero_coeff (α lam : ℝ) (E : ℂ) :
    (iterPoly α lam E 0).map (fun p => p.coeff 0) = 1 := by
  rw [show iterPoly α lam E 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ[X]) from by simp only [iterPoly]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, Matrix.one_apply]

lemma topMat_succ (α lam : ℝ) (E : ℂ) (n : ℕ) :
    (iterPoly α lam E (n+1)).map (fun p => p.coeff (2*(n+1)))
      = (tmPoly lam E (omega α ^ n)).map (fun p => p.coeff 2)
        * (iterPoly α lam E n).map (fun p => p.coeff (2*n)) := by
  rw [show (2*(n+1) : ℕ) = 2 + 2*n from by ring]
  rw [show iterPoly α lam E (n+1) = tmPoly lam E (omega α ^ n) * iterPoly α lam E n
      from by simp only [iterPoly]]
  exact map_coeff_mul _ _ 2 (2*n)
    (fun i j => Trig.matDegLe_tmPoly lam (E:ℂ) (omega α ^ n) i j)
    (fun i j => Trig.matDegLe_iterPoly α lam (E:ℂ) n i j)

lemma iterPoly_top (α lam : ℝ) (E : ℂ) (n : ℕ) :
    (iterPoly α lam E (n+1)).map (fun p => p.coeff (2*(n+1)))
      = Matrix.diagonal (fun i : Fin 2 =>
          if i = 0 then ∏ j ∈ range (n+1), (-(lam:ℂ)) * (omega α ^ j) ^ 2 else 0) := by
  induction n with
  | zero =>
      rw [topMat_succ, show (2*0:ℕ) = 0 from rfl, iterPoly_zero_coeff, mul_one, tmPoly_coeff_two,
        Finset.prod_range_one]
  | succ n ih =>
      rw [topMat_succ, ih, tmPoly_coeff_two,
        show (∏ j ∈ range (n+1+1), (-(lam:ℂ)) * (omega α ^ j) ^ 2)
            = (∏ j ∈ range (n+1), (-(lam:ℂ)) * (omega α ^ j) ^ 2)
              * ((-(lam:ℂ)) * (omega α ^ (n+1)) ^ 2) from Finset.prod_range_succ _ _,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp <;> ring

lemma iterPoly_trace_top (α lam : ℝ) (E : ℂ) (n : ℕ) :
    ((iterPoly α lam E (n+1)).trace).coeff (2*(n+1))
      = ∏ j ∈ range (n+1), (-(lam:ℂ)) * (omega α ^ j) ^ 2 := by
  rw [trace_coeff, iterPoly_top, Matrix.trace_diagonal]
  simp

lemma iterPoly_trace_top_norm (α lam : ℝ) (E : ℂ) (n : ℕ) :
    ‖((iterPoly α lam E (n+1)).trace).coeff (2*(n+1))‖ = |lam| ^ (n+1) := by
  rw [iterPoly_trace_top, Complex.norm_prod]
  have hfac : ∀ j : ℕ, ‖(-(lam:ℂ)) * (omega α ^ j) ^ 2‖ = |lam| := by
    intro j
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pow, omega_norm,
      one_pow, mul_one]
  simp only [hfac]
  rw [Finset.prod_const, Finset.card_range]

lemma matProd_trace_shift (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (q c : ℕ)
    (hper : ∀ j, A (j + q) = A j) (hc : c ≤ q) :
    (matProd A q).trace = (matProd (fun j => A (j + c)) q).trace := by
  have h1 : matProd A q = matProd (fun j => A (j + c)) (q - c) * matProd A c := by
    have h := matProd_add A c (q - c)
    rw [Nat.add_sub_of_le hc] at h
    rw [h]
    rw [show (fun j => A (c + j)) = (fun j => A (j + c)) from by funext j; rw [Nat.add_comm]]
  have h2 : matProd (fun j => A (j + c)) q = matProd A c * matProd (fun j => A (j + c)) (q - c) := by
    have h := matProd_add (fun j => A (j + c)) (q - c) c
    rw [Nat.sub_add_cancel hc] at h
    rw [h]
    congr 1
    apply congrArg (fun f => matProd f c)
    funext j
    rw [show q - c + j + c = j + q from by omega, hper]
  rw [h1, h2, Matrix.trace_mul_comm]

lemma matProd_const (M : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    matProd (fun _ => M) n = M ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [matProd_succ, ih, pow_succ']

/-! ## The main oscillation bound -/

theorem trace_iterC_oscillation (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime (Int.natAbs p) q) (lam E : ℝ) (x : ℝ) : ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace - (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace‖ ≤ 4 * |lam| ^ q := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  set ω : ℂ := omega ((p:ℝ)/((k+1:ℕ):ℝ)) with hω
  set P : ℂ[X] := (iterPoly ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1)).trace with hP
  have hωm : ∀ m : ℕ, ω ^ m = 1 ↔ (k+1) ∣ m := by
    intro m; rw [hω]; exact omega_pow_eq_one_iff p (k+1) (by omega) hcop m
  have hPeval : ∀ y : ℂ, P.eval y = (iterZ ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) y).trace := by
    intro y; rw [hP, trace_eval, Trig.iterPoly_eval]
  have hrot : ∀ y : ℂ, P.eval (ω * y) = P.eval y := by
    intro y
    rw [hPeval (ω * y), hPeval y, Trig.iterZ_eq_matProd, Trig.iterZ_eq_matProd]
    have hA : ∀ j : ℕ, (fun i => tmZ lam (E:ℂ) (y * ω ^ i)) (j + (k+1))
        = (fun i => tmZ lam (E:ℂ) (y * ω ^ i)) j := by
      intro j
      show tmZ lam (E:ℂ) (y * ω ^ (j + (k+1))) = tmZ lam (E:ℂ) (y * ω ^ j)
      rw [pow_add, (hωm (k+1)).mpr (dvd_refl (k+1)), mul_one]
    have hfun : (fun j => tmZ lam (E:ℂ) (ω * y * ω ^ j))
        = (fun j => (fun i => tmZ lam (E:ℂ) (y * ω ^ i)) (j + 1)) := by
      funext j
      rw [show ω * y * ω ^ j = y * ω ^ (j+1) from by rw [pow_succ]; ring]
    rw [hfun]
    exact (matProd_trace_shift (fun i => tmZ lam (E:ℂ) (y * ω ^ i)) (k+1) 1 hA (by omega)).symm
  have hcomp : P.comp (C ω * X) = P := by
    apply Polynomial.funext
    intro y
    rw [Polynomial.eval_comp, show Polynomial.eval y (C ω * X) = ω * y from by simp]
    exact hrot y
  have hcoeff : ∀ m : ℕ, P.coeff m * ω ^ m = P.coeff m := by
    intro m
    have h := congrArg (fun (Q : ℂ[X]) => Q.coeff m) hcomp
    rw [poly_comp_coeff] at h
    exact h
  have hdeg : P.natDegree ≤ 2*(k+1) := by
    rw [hP, Matrix.trace_fin_two]
    calc ((iterPoly ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1)) 0 0
            + (iterPoly ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1)) 1 1).natDegree
        ≤ max ((iterPoly ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1)) 0 0).natDegree
              ((iterPoly ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1)) 1 1).natDegree :=
          Polynomial.natDegree_add_le _ _
      _ ≤ 2*(k+1) := max_le
          (Trig.iterPoly_natDegree ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) 0 0)
          (Trig.iterPoly_natDegree ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) 1 1)
  have hvan : ∀ m : ℕ, P.coeff m ≠ 0 → m = 0 ∨ m = (k+1) ∨ m = 2*(k+1) := by
    intro m hm
    have hmω : ω ^ m = 1 := by
      have h := hcoeff m
      exact mul_left_cancel₀ hm (by rw [mul_one]; exact h)
    have hqd : (k+1) ∣ m := (hωm m).mp hmω
    have hmle : m ≤ 2*(k+1) := (Polynomial.le_natDegree_of_ne_zero hm).trans hdeg
    obtain ⟨j, rfl⟩ := hqd
    have hj : j ≤ 2 := by
      rw [mul_comm (k+1) j] at hmle
      exact Nat.le_of_mul_le_mul_right hmle (by omega)
    interval_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (by ring))
    · exact Or.inr (Or.inr (by ring))
  have hPpoly : P = C (P.coeff 0) + C (P.coeff (k+1)) * X ^ (k+1)
      + C (P.coeff (2*(k+1))) * X ^ (2*(k+1)) := by
    ext m
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hm0 : m = 0
    · subst hm0
      have h1 : ¬ ((k+1) = 0) := by omega
      have h2 : ¬ (2*(k+1) = 0) := by omega
      simp [h1, h2]
    by_cases hmq : m = (k+1)
    · subst hmq
      have h1 : ¬ (0 = (k+1)) := by omega
      have h2 : ¬ (2*(k+1) = (k+1)) := by omega
      simp [h1, h2]
    by_cases hm2q : m = 2*(k+1)
    · subst hm2q
      have h1 : ¬ (0 = 2*(k+1)) := by omega
      have h2 : ¬ ((k+1) = 2*(k+1)) := by omega
      simp [h1, h2]
    · have hy : P.coeff m = 0 := by
        by_contra hc
        rcases hvan m hc with h | h | h <;> tauto
      simp [hm0, hmq, hm2q, hy]
  have hPeval3 : ∀ y : ℂ, P.eval y = P.coeff 0 + P.coeff (k+1) * y ^ (k+1)
      + P.coeff (2*(k+1)) * y ^ (2*(k+1)) := by
    intro y
    conv_lhs => rw [hPpoly]
    rw [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_pow, Polynomial.eval_X]
  have hb0 : ‖P.coeff 0‖ = |lam|^(k+1) := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hPeval]
    show ‖(iterZ ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) 0).trace‖ = |lam|^(k+1)
    rw [Trig.iterZ_eq_matProd]
    have hm0 : (fun j => tmZ lam (E:ℂ) (0 * ω ^ j))
        = (fun _ => Matrix.diagonal (fun i : Fin 2 => if i = 0 then (-(lam:ℂ)) else 0)) := by
      funext j
      ext a b
      fin_cases a <;> fin_cases b <;> simp [tmZ, Matrix.diagonal_apply]
    rw [hm0, matProd_const, Matrix.diagonal_pow, Matrix.trace_diagonal, Fin.sum_univ_two]
    simp only [Pi.pow_apply]
    simp [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hb2q : ‖P.coeff (2*(k+1))‖ = |lam|^(k+1) := by
    rw [hP]
    exact iterPoly_trace_top_norm ((p:ℝ)/((k+1:ℕ):ℝ)) lam E k
  have hPevalx : P.eval (Complex.exp (2 * Real.pi * Complex.I * x))
      = Complex.exp (2 * Real.pi * Complex.I * x)^(k+1) * ω^((k+1)*((k+1)-1)/2)
        * (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) x).trace := by
    rw [hPeval]
    rw [Trig.iterZ_smul, Matrix.trace_smul, smul_eq_mul]
  have hPeval1 : P.eval 1 = ω^((k+1)*((k+1)-1)/2)
      * (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) 0).trace := by
    rw [hPeval 1]
    rw [show (1:ℂ) = Complex.exp (2 * Real.pi * Complex.I * (0:ℝ)) from by simp,
      Trig.iterZ_smul, Matrix.trace_smul, smul_eq_mul]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_pow, one_mul, ← hω]
  have hzq_norm : ‖Complex.exp (2 * Real.pi * Complex.I * x) ^ (k+1)‖ = 1 := by
    rw [norm_pow]
    have : ‖Complex.exp (2 * Real.pi * Complex.I * x)‖ = 1 := by
      rw [Complex.norm_exp]
      have h1 : (2 * (Real.pi:ℂ) * Complex.I * (x:ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      rw [h1, Real.exp_zero]
    rw [this, one_pow]
  have hωe_ne : ω ^ ((k+1)*((k+1)-1)/2) ≠ 0 := by
    intro h
    have h1 : ‖ω ^ ((k+1)*((k+1)-1)/2)‖ = 0 := by rw [h, norm_zero]
    rw [norm_pow, hω, omega_norm, one_pow] at h1
    exact one_ne_zero h1
  have hmain' : Complex.exp (2 * Real.pi * Complex.I * x)^(k+1) * ω^((k+1)*((k+1)-1)/2)
        * ((iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) x).trace
          - (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) 0).trace)
      = (1 - Complex.exp (2 * Real.pi * Complex.I * x)^(k+1))
        * (P.coeff 0 - P.coeff (2*(k+1)) * Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)) := by
    have e1 : Complex.exp (2 * Real.pi * Complex.I * x)^(k+1) * ω^((k+1)*((k+1)-1)/2)
        * (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) x).trace
        = P.eval (Complex.exp (2 * Real.pi * Complex.I * x)) := hPevalx.symm
    have e0 : Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)
        * (ω^((k+1)*((k+1)-1)/2) * (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) 0).trace)
        = Complex.exp (2 * Real.pi * Complex.I * x)^(k+1) * P.eval 1 := by rw [hPeval1]
    rw [mul_sub, e1]
    rw [show Complex.exp (2 * Real.pi * Complex.I * x)^(k+1) * ω^((k+1)*((k+1)-1)/2)
          * (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) 0).trace
        = Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)
          * (ω^((k+1)*((k+1)-1)/2) * (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) 0).trace)
        from by ring, e0]
    rw [hPeval3, hPeval3]
    ring
  have hmain : Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)
        * ((iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) x).trace
          - (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) 0).trace)
      = (ω^((k+1)*((k+1)-1)/2))⁻¹
        * ((1 - Complex.exp (2 * Real.pi * Complex.I * x)^(k+1))
          * (P.coeff 0 - P.coeff (2*(k+1)) * Complex.exp (2 * Real.pi * Complex.I * x)^(k+1))) := by
    rw [← hmain']
    rw [show Complex.exp (2 * Real.pi * Complex.I * x)^(k+1) * ω^((k+1)*((k+1)-1)/2)
          * ((iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) x).trace
            - (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) 0).trace)
        = ω^((k+1)*((k+1)-1)/2)
          * (Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)
            * ((iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) x).trace
              - (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) 0).trace)) from by ring]
    rw [inv_mul_cancel_left₀ hωe_ne]
  have hbnd : ‖(1 - Complex.exp (2 * Real.pi * Complex.I * x)^(k+1))
        * (P.coeff 0 - P.coeff (2*(k+1)) * Complex.exp (2 * Real.pi * Complex.I * x)^(k+1))‖
      ≤ 4 * |lam|^(k+1) := by
    rw [norm_mul]
    have h1 : ‖(1:ℂ) - Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)‖ ≤ 2 := by
      calc ‖(1:ℂ) - Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)‖
          ≤ ‖(1:ℂ)‖ + ‖Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_one, hzq_norm]; norm_num
    have h2 : ‖P.coeff 0 - P.coeff (2*(k+1)) * Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)‖
        ≤ 2 * |lam|^(k+1) := by
      calc ‖P.coeff 0 - P.coeff (2*(k+1)) * Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)‖
          ≤ ‖P.coeff 0‖ + ‖P.coeff (2*(k+1)) * Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)‖ :=
            norm_sub_le _ _
        _ = ‖P.coeff 0‖ + ‖P.coeff (2*(k+1))‖ := by rw [norm_mul, hzq_norm, mul_one]
        _ = 2 * |lam|^(k+1) := by rw [hb0, hb2q]; ring
    calc ‖(1 - Complex.exp (2 * Real.pi * Complex.I * x)^(k+1))‖
            * ‖P.coeff 0 - P.coeff (2*(k+1)) * Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)‖
        ≤ 2 * (2 * |lam|^(k+1)) := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ = 4 * |lam|^(k+1) := by ring
  have homega_inv : ‖(ω^((k+1)*((k+1)-1)/2))⁻¹‖ = 1 := by
    rw [norm_inv, norm_pow, hω, omega_norm, one_pow, inv_one]
  calc ‖(iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) x).trace
          - (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) 0).trace‖
      = ‖Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)
          * ((iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) x).trace
            - (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) 0).trace)‖ := by
        rw [norm_mul, hzq_norm, one_mul]
    _ = ‖(ω^((k+1)*((k+1)-1)/2))⁻¹
          * ((1 - Complex.exp (2 * Real.pi * Complex.I * x)^(k+1))
            * (P.coeff 0 - P.coeff (2*(k+1)) * Complex.exp (2 * Real.pi * Complex.I * x)^(k+1)))‖ := by
        rw [hmain]
    _ = ‖(1 - Complex.exp (2 * Real.pi * Complex.I * x)^(k+1))
          * (P.coeff 0 - P.coeff (2*(k+1)) * Complex.exp (2 * Real.pi * Complex.I * x)^(k+1))‖ := by
        rw [norm_mul, homega_inv, one_mul]
    _ ≤ 4 * |lam|^(k+1) := hbnd

end

end Work.TMC7Core.Solutions
