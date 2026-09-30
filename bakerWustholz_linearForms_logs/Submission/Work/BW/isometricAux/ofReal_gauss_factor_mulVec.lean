import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.isometricAux

private lemma sq_sum_eq_dotProduct {N : ℕ} (v : Fin N → ℝ) :
    (∑ i, (v i)^2) = v ⬝ᵥ v := by
  simp only [dotProduct, pow_two]

private lemma dotProduct_self_mulVec {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (hA : A.transpose * A = 1) (v : n → ℝ) :
    (A.mulVec v) ⬝ᵥ (A.mulVec v) = v ⬝ᵥ v := by
  have h := Matrix.dotProduct_transpose_mulVec (A := A) (x := v) (y := A.mulVec v)
  simp only [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec] at h
  exact h.symm

private lemma dotProduct_mulVec_eq_zero {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix m n ℝ) (B : Matrix m p ℝ) (h : A.transpose * B = 0) (x : n → ℝ) (y : p → ℝ) :
    (A.mulVec x) ⬝ᵥ (B.mulVec y) = 0 := by
  have h' : B.transpose * A = 0 := by
    have : B.transpose * A = (A.transpose * B).transpose := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [this, h, Matrix.transpose_zero]
  have h2 := Matrix.dotProduct_transpose_mulVec (A := B) (x := y) (y := A.mulVec x)
  rw [Matrix.mulVec_mulVec, h', Matrix.zero_mulVec] at h2
  have hzero : y ⬝ᵥ (0 : p → ℝ) = 0 := by simp [dotProduct]
  rw [hzero] at h2
  exact h2.symm

private lemma prod_ofReal_exp {N : ℕ} (a : Fin N → ℝ) :
    (∏ i : Fin N, ENNReal.ofReal (Real.exp (a i))) = ENNReal.ofReal (Real.exp (∑ i, a i)) := by
  rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ) (f := fun i => Real.exp (a i))
      (fun i _ => (Real.exp_pos _).le)]
  congr 1
  simpa using (Real.exp_sum Finset.univ a).symm

theorem ofReal_gauss_factor_mulVec {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (Bp : Matrix (Fin n) (Fin (n - k)) ℝ)
    (hB : B.transpose * B = 1) (hBp : Bp.transpose * Bp = 1) (hBBp : B.transpose * Bp = 0)
    (x : Fin k → ℝ) (y : Fin (n - k) → ℝ) :
    (∏ i : Fin n, ENNReal.ofReal (Real.exp (- Real.pi * ((B.mulVec x + Bp.mulVec y) i)^2)))
      = (∏ i : Fin k, ENNReal.ofReal (Real.exp (- Real.pi * (x i)^2)))
        * (∏ l : Fin (n-k), ENNReal.ofReal (Real.exp (- Real.pi * (y l)^2))) := by
  have hBBpT : Bp.transpose * B = 0 := by
    have : Bp.transpose * B = (B.transpose * Bp).transpose := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [this, hBBp, Matrix.transpose_zero]
  have hdot : (B.mulVec x + Bp.mulVec y) ⬝ᵥ (B.mulVec x + Bp.mulVec y)
      = x ⬝ᵥ x + y ⬝ᵥ y := by
    rw [add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_self_mulVec B hB x, dotProduct_self_mulVec Bp hBp y,
      dotProduct_mulVec_eq_zero B Bp hBBp x y,
      dotProduct_mulVec_eq_zero Bp B hBBpT y x]
    ring
  have hsum : (∑ i : Fin n, ((B.mulVec x + Bp.mulVec y) i)^2)
      = (∑ i : Fin k, (x i)^2) + (∑ l : Fin (n-k), (y l)^2) := by
    rw [sq_sum_eq_dotProduct, sq_sum_eq_dotProduct, sq_sum_eq_dotProduct, hdot]
  have hL : (∏ i : Fin n, ENNReal.ofReal (Real.exp (-Real.pi * ((B.mulVec x + Bp.mulVec y) i)^2)))
      = ENNReal.ofReal (Real.exp (-Real.pi * ((∑ i : Fin k, (x i)^2) + ∑ l : Fin (n-k), (y l)^2))) := by
    rw [prod_ofReal_exp (a := fun i => -Real.pi * ((B.mulVec x + Bp.mulVec y) i)^2)]
    congr 1
    congr 1
    rw [← hsum, Finset.mul_sum]
  have hR1 : (∏ i : Fin k, ENNReal.ofReal (Real.exp (-Real.pi * (x i)^2)))
      = ENNReal.ofReal (Real.exp (-Real.pi * ∑ i : Fin k, (x i)^2)) := by
    rw [prod_ofReal_exp (a := fun i : Fin k => -Real.pi * (x i)^2)]
    congr 1
    congr 1
    rw [Finset.mul_sum]
  have hR2 : (∏ l : Fin (n-k), ENNReal.ofReal (Real.exp (-Real.pi * (y l)^2)))
      = ENNReal.ofReal (Real.exp (-Real.pi * ∑ l : Fin (n-k), (y l)^2)) := by
    rw [prod_ofReal_exp (a := fun l : Fin (n-k) => -Real.pi * (y l)^2)]
    congr 1
    congr 1
    rw [Finset.mul_sum]
  rw [hL, hR1, hR2]
  rw [← ENNReal.ofReal_mul (p := Real.exp (-Real.pi * ∑ i : Fin k, (x i)^2))
      (le_of_lt (Real.exp_pos _))]
  congr 1
  rw [← Real.exp_add]
  congr 1
  ring

end Work.BW.isometricAux
