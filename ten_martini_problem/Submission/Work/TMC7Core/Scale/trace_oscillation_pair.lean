import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Solutions.rat_bound
import Submission.Work.TMC7Core.Solutions.trace_iterC_oscillation

/-!
# Oscillation of the `q`-step trace at a rational frequency

For `α = p/q` in lowest terms and `z = e^{2πix}`, the trace of the `q`-step transfer
matrix `A_q(x)` is, as a function of the phase, a two-mode Laurent polynomial

`Tr A_q(x) = (c₀ z^{-q} + c_q + c₂ z^{q}) / ω^{q(q-1)/2}`,

where the trace polynomial `P` of the algebraic cocycle `iterPoly α lam E q` satisfies
`P.eval y = c₀ + c_q y^q + c₂ y^{2q}` with `‖c₀‖ = ‖c₂‖ = |λ|^q`.  Consequently the
traces at two arbitrary phases differ by at most `2‖c₀‖ + 2‖c₂‖ = 4|λ|^q`.

The pure complex-algebra core of that final step is isolated in `norm_trace_pair_le`.
-/

namespace Work.TMC7Core.Scale

open Polynomial Matrix Finset
open Work.TMC7Core

/-- Pure algebra: if the `q`-step algebraic trace polynomial of the cocycle has the
three-term structure `c₀ + c_q y^q + c₂ y^{2q}`, then for two unimodular phases `z, w`
and a unimodular normalization `ω` the corresponding traces `A, B` differ by at most
`2‖c₀‖ + 2‖c₂‖`. -/
theorem norm_trace_pair_le (q : ℕ) (A B c₀ cq c₂ ω z w : ℂ)
    (hA : z ^ q * ω * A = c₀ + cq * z ^ q + c₂ * z ^ (2 * q))
    (hB : w ^ q * ω * B = c₀ + cq * w ^ q + c₂ * w ^ (2 * q))
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (hω : ‖ω‖ = 1) :
    ‖A - B‖ ≤ 2 * ‖c₀‖ + 2 * ‖c₂‖ := by
  have hz2 : z ^ (2 * q) = z ^ q * z ^ q := by
    rw [show 2 * q = q + q from by ring, pow_add]
  have hw2 : w ^ (2 * q) = w ^ q * w ^ q := by
    rw [show 2 * q = q + q from by ring, pow_add]
  rw [hz2] at hA
  rw [hw2] at hB
  have hkey : z ^ q * w ^ q * ω * (A - B)
      = (w ^ q - z ^ q) * (c₀ - c₂ * (z ^ q * w ^ q)) := by
    calc z ^ q * w ^ q * ω * (A - B)
        = w ^ q * (z ^ q * ω * A) - z ^ q * (w ^ q * ω * B) := by ring
      _ = w ^ q * (c₀ + cq * z ^ q + c₂ * (z ^ q * z ^ q))
            - z ^ q * (c₀ + cq * w ^ q + c₂ * (w ^ q * w ^ q)) := by rw [hA, hB]
      _ = (w ^ q - z ^ q) * (c₀ - c₂ * (z ^ q * w ^ q)) := by ring
  have hnorm : ‖z ^ q * w ^ q * ω‖ = 1 := by
    simp only [norm_mul, norm_pow, hz, hw, hω, one_pow, one_mul]
  have h1 : ‖w ^ q - z ^ q‖ ≤ 2 := by
    calc ‖w ^ q - z ^ q‖ ≤ ‖w ^ q‖ + ‖z ^ q‖ := norm_sub_le _ _
      _ = 2 := by simp only [norm_pow, hz, hw, one_pow]; norm_num
  have h2 : ‖c₀ - c₂ * (z ^ q * w ^ q)‖ ≤ ‖c₀‖ + ‖c₂‖ := by
    calc ‖c₀ - c₂ * (z ^ q * w ^ q)‖ ≤ ‖c₀‖ + ‖c₂ * (z ^ q * w ^ q)‖ := norm_sub_le _ _
      _ = ‖c₀‖ + ‖c₂‖ := by
          simp only [norm_mul, norm_pow, hz, hw, one_pow, one_mul, mul_one]
  calc ‖A - B‖ = ‖z ^ q * w ^ q * ω * (A - B)‖ := by simp only [norm_mul, hnorm, one_mul]
    _ = ‖(w ^ q - z ^ q) * (c₀ - c₂ * (z ^ q * w ^ q))‖ := by rw [hkey]
    _ ≤ 2 * ‖c₀‖ + 2 * ‖c₂‖ := by
        rw [norm_mul]
        calc ‖w ^ q - z ^ q‖ * ‖c₀ - c₂ * (z ^ q * w ^ q)‖
            ≤ 2 * (‖c₀‖ + ‖c₂‖) := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
          _ = 2 * ‖c₀‖ + 2 * ‖c₂‖ := by ring

/-- The trace of the `q`-step transfer matrix oscillates by at most `4|λ|^q`: for
`α = p/q` in lowest terms and any two phases `x, y`, `‖tr A_q(x) - tr A_q(y)‖ ≤ 4|λ|^q`. -/
theorem trace_oscillation_pair (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime (Int.natAbs p) q)
    (lam E : ℝ) (x y : ℝ) :
    ‖(Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace
      - (Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q y).trace‖ ≤ 4 * |lam| ^ q := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  set ω : ℂ := omega ((p:ℝ)/((k+1:ℕ):ℝ)) with hω
  set P : ℂ[X] := (iterPoly ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1)).trace with hP
  have hωm : ∀ m : ℕ, ω ^ m = 1 ↔ (k+1) ∣ m := by
    intro m; rw [hω]; exact Solutions.omega_pow_eq_one_iff p (k+1) (by omega) hcop m
  have hPeval : ∀ y : ℂ, P.eval y = (iterZ ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) y).trace := by
    intro y; rw [hP, Solutions.trace_eval, Trig.iterPoly_eval]
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
    exact (Solutions.matProd_trace_shift (fun i => tmZ lam (E:ℂ) (y * ω ^ i)) (k+1) 1 hA
      (by omega)).symm
  have hcomp : P.comp (C ω * X) = P := by
    apply Polynomial.funext
    intro y
    rw [Polynomial.eval_comp, show Polynomial.eval y (C ω * X) = ω * y from by simp]
    exact hrot y
  have hcoeff : ∀ m : ℕ, P.coeff m * ω ^ m = P.coeff m := by
    intro m
    have h := congrArg (fun (Q : ℂ[X]) => Q.coeff m) hcomp
    rw [Solutions.poly_comp_coeff] at h
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
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
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
    rw [hm0, Solutions.matProd_const, Matrix.diagonal_pow, Matrix.trace_diagonal,
      Fin.sum_univ_two]
    simp only [Pi.pow_apply]
    simp [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hb2q : ‖P.coeff (2*(k+1))‖ = |lam|^(k+1) := by
    rw [hP]
    exact Solutions.iterPoly_trace_top_norm ((p:ℝ)/((k+1:ℕ):ℝ)) lam E k
  have hPevalx : P.eval (Complex.exp (2 * Real.pi * Complex.I * x))
      = Complex.exp (2 * Real.pi * Complex.I * x)^(k+1) * ω^((k+1)*((k+1)-1)/2)
        * (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) x).trace := by
    rw [hPeval]
    rw [Trig.iterZ_smul, Matrix.trace_smul, smul_eq_mul]
  have hPevaly : P.eval (Complex.exp (2 * Real.pi * Complex.I * y))
      = Complex.exp (2 * Real.pi * Complex.I * y)^(k+1) * ω^((k+1)*((k+1)-1)/2)
        * (iterC ((p:ℝ)/((k+1:ℕ):ℝ)) lam (E:ℂ) (k+1) y).trace := by
    rw [hPeval]
    rw [Trig.iterZ_smul, Matrix.trace_smul, smul_eq_mul]
  have hA : Complex.exp (2 * Real.pi * Complex.I * x) ^ (k + 1)
        * ω ^ ((k + 1) * ((k + 1) - 1) / 2)
        * (iterC ((p : ℝ) / ((k + 1 : ℕ) : ℝ)) lam (E : ℂ) (k + 1) x).trace
      = P.coeff 0 + P.coeff (k+1) * Complex.exp (2 * Real.pi * Complex.I * x) ^ (k + 1)
        + P.coeff (2*(k+1)) * Complex.exp (2 * Real.pi * Complex.I * x) ^ (2 * (k + 1)) := by
    rw [← hPevalx, hPeval3]
  have hB : Complex.exp (2 * Real.pi * Complex.I * y) ^ (k + 1)
        * ω ^ ((k + 1) * ((k + 1) - 1) / 2)
        * (iterC ((p : ℝ) / ((k + 1 : ℕ) : ℝ)) lam (E : ℂ) (k + 1) y).trace
      = P.coeff 0 + P.coeff (k+1) * Complex.exp (2 * Real.pi * Complex.I * y) ^ (k + 1)
        + P.coeff (2*(k+1)) * Complex.exp (2 * Real.pi * Complex.I * y) ^ (2 * (k + 1)) := by
    rw [← hPevaly, hPeval3]
  have hzn : ‖Complex.exp (2 * Real.pi * Complex.I * x)‖ = 1 := by
    rw [Complex.norm_exp]
    have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [h, Real.exp_zero]
  have hwn : ‖Complex.exp (2 * Real.pi * Complex.I * y)‖ = 1 := by
    rw [Complex.norm_exp]
    have h : (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [h, Real.exp_zero]
  have hωn : ‖ω ^ ((k+1)*((k+1)-1)/2)‖ = 1 := by
    rw [norm_pow, hω, Solutions.omega_norm, one_pow]
  have key := norm_trace_pair_le (k + 1)
    (iterC ((p : ℝ) / ((k + 1 : ℕ) : ℝ)) lam (E : ℂ) (k + 1) x).trace
    (iterC ((p : ℝ) / ((k + 1 : ℕ) : ℝ)) lam (E : ℂ) (k + 1) y).trace
    (P.coeff 0) (P.coeff (k+1)) (P.coeff (2*(k+1)))
    (ω ^ ((k+1)*((k+1)-1)/2))
    (Complex.exp (2 * Real.pi * Complex.I * x)) (Complex.exp (2 * Real.pi * Complex.I * y))
    hA hB hzn hwn hωn
  rw [hb0, hb2q] at key
  have harith : (2 : ℝ) * |lam| ^ (k + 1) + 2 * |lam| ^ (k + 1) = 4 * |lam| ^ (k + 1) := by
    ring
  linarith [key, harith]

end Work.TMC7Core.Scale
