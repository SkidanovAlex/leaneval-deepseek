import Submission.MinkBox
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Roots

/-!
# `minkLower` — elementary cross-polytope/determinant lower bound

Prove `Submission.MinkLower.mink_lower : Submission.MinkBox.minkLower`.

The statement (with `d ≥ 2`, `α : Fin d → ℝ` injective, `v : Fin d → ℝ` all
positive): for every `ℚ`-linearly independent family `Q : Fin d → Polynomial ℤ`
of integer polynomials of degree `≤ d−1` and every `mu : Fin d → ℝ` with
`∀ i k, v k * |evalInt (Q i) (α k)| ≤ mu i`, we have
`Dval d α v ≤ (d:ℝ)^(C·d) · (∏ i, mu i)` (with `Dval d α v = (∏_k v k) · pairProd d α`).

Take `C := 1`; the proof splits into:

* **evaluation identity**: `evalInt (Q i) (α k) = ∑_j (Q i).coeff j · (α k)^j`
  (degrees `< d`), so the evaluation matrix factorizes as
  `(coefficient matrix) * (power matrix)` and `|det M| ≥ pairProd d α` because
  the integer coefficient matrix has ℚ-independent rows (hence nonzero integer
  determinant `≥ 1` in absolute value) and the power matrix has Vandermonde
  determinant with absolute value `pairProd d α`;
* **row/column scaling**: `det` of `M = (mu i)`-scaled rows and of
  `W i k = v k · Q i(α k) / mu i` give `(∏ v)·|det M| = (∏ mu)·|det W|`;
* **box bound**: `|W i k| ≤ 1` from the hypothesis, so
  `|det W| ≤ d!` by the permutation bound (`Matrix.det_le`);
* conclude `Dval ≤ d! · ∏ mu ≤ (d:ℝ)^(1·d) · ∏ mu` since `d! ≤ d^d`.
-/

noncomputable section
noncomputable section
open Polynomial
open scoped Real BigOperators

namespace Submission.MinkLower

open Submission.MinkBox
open Matrix

def evalMatrix (d : ℕ) (α : Fin d → ℝ) (Q : Fin d → Polynomial ℤ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i k => evalInt (Q i) (α k)

def coeffZ (d : ℕ) (Q : Fin d → Polynomial ℤ) : Matrix (Fin d) (Fin d) ℤ :=
  Matrix.of fun i j => (Q i).coeff j.val

def coeffR (d : ℕ) (Q : Fin d → Polynomial ℤ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ((Q i).coeff j.val : ℝ)

def zMat (d : ℕ) (α : Fin d → ℝ) (mu : Fin d → ℝ) (Q : Fin d → Polynomial ℤ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i k => evalInt (Q i) (α k) / mu i

def scalMat (d : ℕ) (α : Fin d → ℝ) (v mu : Fin d → ℝ) (Q : Fin d → Polynomial ℤ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i k => v k * (evalInt (Q i) (α k) / mu i)

def powMat (d : ℕ) (α : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun j k => (α k) ^ j.val

-- --------------------------------------------------------------------------
lemma det_ne_zero_of_linearIndependent {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]
    (c : n → n → K) (hc : LinearIndependent K c) : (Matrix.of c).det ≠ 0 := by
  intro hdet
  rcases Matrix.exists_vecMul_eq_zero_iff.mpr hdet with ⟨v, hv, hvc⟩
  apply hv
  apply _root_.funext
  intro j
  apply (Fintype.linearIndependent_iff.mp hc) v
  funext t
  calc
    (∑ i : n, v i • c i) t = ∑ i : n, v i * c i t := by simp
    _ = (v ᵥ* (Matrix.of c)) t := by rfl
    _ = 0 := congrFun hvc t

lemma det_coeffZ_ne_zero (d : ℕ) (Q : Fin d → Polynomial ℤ) (hQ : LinIndepInt d Q) :
    (coeffZ d Q).det ≠ 0 := by
  intro hz0
  have hrows : LinearIndependent ℚ (fun i : Fin d => coeffVec d (Q i)) := hQ
  have hmat : ((coeffZ d Q).map (fun x : ℤ => (x : ℚ))) =
      Matrix.of (fun i : Fin d => coeffVec d (Q i)) := by
    ext i j
    rfl
  have hdetQ : ((coeffZ d Q).map (fun x : ℤ => (x : ℚ))).det ≠ 0 := by
    have hd := det_ne_zero_of_linearIndependent (fun i : Fin d => coeffVec d (Q i)) hrows
    simpa [← hmat] using hd
  have hcast : ((coeffZ d Q).map (fun x : ℤ => (x : ℚ))).det = (((coeffZ d Q).det : ℤ) : ℚ) := by
    exact (Int.cast_det (R := ℚ) (M := coeffZ d Q)).symm
  rw [hcast, hz0] at hdetQ
  norm_num at hdetQ

lemma one_le_abs_intCast {z : ℤ} (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
  have hz' : (1 : ℤ) ≤ |z| := (Int.add_one_le_iff).mpr (abs_pos.mpr hz)
  exact_mod_cast hz'

lemma det_coeffR_abs_ge_one (d : ℕ) (Q : Fin d → Polynomial ℤ) (hQ : LinIndepInt d Q) :
    (1 : ℝ) ≤ |(coeffR d Q).det| := by
  have hz : (coeffZ d Q).det ≠ 0 := det_coeffZ_ne_zero d Q hQ
  have hmatR : coeffR d Q = (coeffZ d Q).map (fun x : ℤ => (x : ℝ)) := by
    ext i j
    rfl
  have hcast : (coeffR d Q).det = (((coeffZ d Q).det : ℤ) : ℝ) := by
    rw [hmatR]
    exact (Int.cast_det (R := ℝ) (M := coeffZ d Q)).symm
  rw [hcast]
  exact one_le_abs_intCast hz

-- --------------------------------------------------------------------------
lemma powMat_eq_vandermondeT (d : ℕ) (α : Fin d → ℝ) :
    powMat d α = (Matrix.vandermonde α)ᵀ := by
  ext j k
  rfl

lemma pairProd_eq_Ioi (d : ℕ) (α : Fin d → ℝ) :
    pairProd d α = ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, |α j - α i| := by
  unfold pairProd
  apply Finset.prod_congr rfl
  intro i hi
  rw [show (Finset.univ.filter (fun j : Fin d => i < j)) = Finset.Ioi i by ext j; simp]
  apply Finset.prod_congr rfl
  intro j hj
  exact abs_sub_comm (α i) (α j)

lemma abs_det_vandermonde_eq_pairProd (d : ℕ) (α : Fin d → ℝ) :
    |(Matrix.vandermonde α).det| = pairProd d α := by
  rw [pairProd_eq_Ioi, Matrix.det_vandermonde]
  simp [Finset.abs_prod]

lemma evalInt_eq_sum {d : ℕ} (Q : Polynomial ℤ) {x : ℝ} (hdeg : Q.natDegree < d) :
    evalInt Q x = ∑ j : Fin d, ((Q.coeff j.val : ℤ) : ℝ) * x ^ (j.val : ℕ) := by
  let p : Polynomial ℝ := Q.map (algebraMap ℤ ℝ)
  have hpdeg : p.natDegree < d := by
    rw [Polynomial.natDegree_map_eq_of_injective]
    · exact hdeg
    · intro a b h
      exact Int.cast_injective h
  calc
    evalInt Q x = p.eval x := by rfl
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
      rw [Polynomial.eval_eq_sum_range]
    _ = ∑ i ∈ Finset.range d, p.coeff i * x ^ i := by
      apply Finset.sum_subset
      · rw [Finset.range_subset]
        intro i hi
        exact Finset.mem_range.mpr (lt_of_lt_of_le hi (Nat.succ_le_of_lt hpdeg))
      · intro i hi hnot
        have hi' : p.natDegree < i := by
          have : ¬ i < p.natDegree + 1 := by
            intro h
            apply hnot
            exact Finset.mem_range.mpr h
          omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi']
        simp
    _ = ∑ j : Fin d, p.coeff j.val * x ^ (j.val : ℕ) := by
      rw [← Fin.sum_univ_eq_sum_range (fun n : ℕ => p.coeff n * x ^ n) d]
    _ = ∑ j : Fin d, ((Q.coeff j.val : ℤ) : ℝ) * x ^ (j.val : ℕ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hc : p.coeff j.val = ((Q.coeff j.val : ℤ) : ℝ) := by
        simp [p, Polynomial.coeff_map]
      rw [hc]

lemma evalMatrix_eq_coeffR_mul_pow (d : ℕ) (α : Fin d → ℝ) (Q : Fin d → Polynomial ℤ)
    (hdeg : ∀ i, (Q i).natDegree < d) :
    evalMatrix d α Q = coeffR d Q * powMat d α := by
  ext i k
  simp only [evalMatrix, Matrix.of_apply]
  rw [evalInt_eq_sum (Q := Q i) (hdeg := hdeg i)]
  simp [coeffR, powMat, Matrix.mul_apply]

lemma pairProd_le_abs_det_evalMatrix {d : ℕ} (α : Fin d → ℝ) (Q : Fin d → Polynomial ℤ)
    (hdeg : ∀ i, (Q i).natDegree < d) (hQ : LinIndepInt d Q) :
    pairProd d α ≤ |(evalMatrix d α Q).det| := by
  have hfac : evalMatrix d α Q = coeffR d Q * powMat d α :=
    evalMatrix_eq_coeffR_mul_pow d α Q hdeg
  have hV : (powMat d α).det = (Matrix.vandermonde α).det := by
    rw [powMat_eq_vandermondeT, Matrix.det_transpose]
  have hdet : (evalMatrix d α Q).det = (coeffR d Q).det * (powMat d α).det := by
    rw [hfac, Matrix.det_mul]
  calc
    pairProd d α = |(Matrix.vandermonde α).det| := (abs_det_vandermonde_eq_pairProd d α).symm
    _ = |(powMat d α).det| := by rw [hV]
    _ ≤ |(coeffR d Q).det| * |(powMat d α).det| := by
      nlinarith [det_coeffR_abs_ge_one d Q hQ, abs_nonneg ((powMat d α).det)]
    _ = |(evalMatrix d α Q).det| := by
      rw [hdet]
      rw [abs_mul]

-- --------------------------------------------------------------------------
lemma Q_ne_zero_of_LinIndepInt {d : ℕ} (Q : Fin d → Polynomial ℤ)
    (hQ : LinIndepInt d Q) (i : Fin d) : Q i ≠ 0 := by
  intro hzero
  have : coeffVec d (Q i) ≠ 0 := hQ.ne_zero i
  apply this
  ext j
  simp [coeffVec, hzero]

lemma exists_evalInt_ne_zero_of_LinIndepInt {d : ℕ} (α : Fin d → ℝ) (Q : Fin d → Polynomial ℤ)
    (hα : Function.Injective α) (hdeg : ∀ i, (Q i).natDegree < d) (hQ : LinIndepInt d Q) (i : Fin d) :
    ∃ k : Fin d, evalInt (Q i) (α k) ≠ 0 := by
  classical
  by_contra h
  have heval : ∀ k : Fin d, evalInt (Q i) (α k) = 0 := by
    intro k
    by_contra hk
    exact h ⟨k, hk⟩
  have hp0 : (Q i).map (algebraMap ℤ ℝ) = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero ((Q i).map (algebraMap ℤ ℝ)) hα
    · intro k
      simpa [evalInt] using heval k
    · rw [Polynomial.natDegree_map_eq_of_injective]
      · simpa using hdeg i
      · intro a b hab
        exact Int.cast_injective hab
  have hQi0 : Q i ≠ 0 := Q_ne_zero_of_LinIndepInt Q hQ i
  have hpmap : (Q i).map (algebraMap ℤ ℝ) ≠ 0 := by
    intro hz
    apply hQi0
    exact (Polynomial.map_injective (algebraMap ℤ ℝ) (by intro a b hab; exact Int.cast_injective hab))
      (by simpa using hz)
  exact hpmap hp0


-- --------------------------------------------------------------------------
-- Main estimate
-- --------------------------------------------------------------------------
lemma scalMat_bound (d : ℕ) (α : Fin d → ℝ) (v mu : Fin d → ℝ) (Q : Fin d → Polynomial ℤ)
    (hv : ∀ k, 0 < v k) (hmu_pos : ∀ i, 0 < mu i)
    (hmu : ∀ i k, v k * |evalInt (Q i) (α k)| ≤ mu i) :
    ∀ i k, |scalMat d α v mu Q i k| ≤ 1 := by
  intro i k
  have hmu0 : 0 < mu i := hmu_pos i
  have hvk0 : 0 < v k := hv k
  rw [show |scalMat d α v mu Q i k| = |v k * (evalInt (Q i) (α k) / mu i)| by rfl]
  rw [abs_mul, abs_of_pos hvk0, abs_div, abs_of_pos hmu0, ← mul_div_assoc, div_le_iff₀ hmu0]
  simpa using (hmu i k)

lemma abs_det_scalMat_le_factorial (d : ℕ) (α : Fin d → ℝ) (v mu : Fin d → ℝ) (Q : Fin d → Polynomial ℤ)
    (hv : ∀ k, 0 < v k) (hmu_pos : ∀ i, 0 < mu i)
    (hmu : ∀ i k, v k * |evalInt (Q i) (α k)| ≤ mu i) :
    |(scalMat d α v mu Q).det| ≤ (d.factorial : ℝ) := by
  have hsc := scalMat_bound d α v mu Q hv hmu_pos hmu
  have h := Matrix.det_le (A := scalMat d α v mu Q)
    (abv := (AbsoluteValue.abs : AbsoluteValue ℝ ℝ)) (x := (1 : ℝ))
    (by intro i k; exact hsc i k)
  simpa using h

lemma evalMatrix_eq_row_scaled (d : ℕ) (α : Fin d → ℝ) (Q : Fin d → Polynomial ℤ)
    (mu : Fin d → ℝ) (hmune : ∀ i, mu i ≠ 0) :
    evalMatrix d α Q = Matrix.of (fun i k : Fin d => mu i * zMat d α mu Q i k) := by
  ext i k
  simp only [evalMatrix, Matrix.of_apply]
  simp only [zMat, Matrix.of_apply]
  field_simp [hmune i]

lemma scalMat_eq_col_scaled (d : ℕ) (α : Fin d → ℝ) (v mu : Fin d → ℝ) (Q : Fin d → Polynomial ℤ) :
    scalMat d α v mu Q = Matrix.of (fun i k : Fin d => v k * zMat d α mu Q i k) := by
  ext i k
  simp [scalMat, zMat]

lemma main_estimate (d : ℕ) (hd : 2 ≤ d) (α : Fin d → ℝ) (hα : Function.Injective α)
    (v : Fin d → ℝ) (hv : ∀ k, 0 < v k)
    (Q : Fin d → Polynomial ℤ) (hQ : LinIndepInt d Q) (hdeg : ∀ i, (Q i).natDegree ≤ d - 1)
    (mu : Fin d → ℝ) (hmu : ∀ i k, v k * |evalInt (Q i) (α k)| ≤ mu i) :
    Dval d α v ≤ (d : ℝ) ^ (1 * (d : ℝ)) * (∏ i : Fin d, mu i) := by
  have hdpos : d ≥ 1 := by omega
  have hdeglt : ∀ i, (Q i).natDegree < d := by
    intro i
    have := hdeg i
    omega
  have hmu_pos : ∀ i : Fin d, 0 < mu i := by
    intro i
    rcases exists_evalInt_ne_zero_of_LinIndepInt α Q hα hdeglt hQ i with ⟨k, hkne⟩
    exact lt_of_lt_of_le (mul_pos (hv k) (abs_pos.mpr hkne)) (hmu i k)
  have hmune : ∀ i : Fin d, mu i ≠ 0 := fun i => ne_of_gt (hmu_pos i)
  have hprodv_pos : 0 < (∏ k : Fin d, v k) := Finset.prod_pos (fun k _ => hv k)
  have hprodmu_pos : 0 < (∏ i : Fin d, mu i) := Finset.prod_pos (fun i _ => hmu_pos i)
  have hpair : pairProd d α ≤ |(evalMatrix d α Q).det| :=
    pairProd_le_abs_det_evalMatrix α Q hdeglt hQ
  have hscal_det : |(scalMat d α v mu Q).det| ≤ (d.factorial : ℝ) :=
    abs_det_scalMat_le_factorial d α v mu Q hv hmu_pos hmu
  have hM := evalMatrix_eq_row_scaled d α Q mu hmune
  have hW := scalMat_eq_col_scaled d α v mu Q
  have hdetM : (evalMatrix d α Q).det = (∏ i : Fin d, mu i) * (zMat d α mu Q).det := by
    rw [hM, Matrix.det_mul_column]
  have hdetW : (scalMat d α v mu Q).det = (∏ k : Fin d, v k) * (zMat d α mu Q).det := by
    rw [hW, Matrix.det_mul_row]
  have hrel : (∏ k : Fin d, v k) * (evalMatrix d α Q).det =
      (∏ i : Fin d, mu i) * (scalMat d α v mu Q).det := by
    rw [hdetM, hdetW]
    ring
  have habsrel : (∏ k : Fin d, v k) * |(evalMatrix d α Q).det| =
      (∏ i : Fin d, mu i) * |(scalMat d α v mu Q).det| := by
    have h1 : |(∏ k : Fin d, v k) * (evalMatrix d α Q).det| =
        |(∏ i : Fin d, mu i) * (scalMat d α v mu Q).det| := by
      rw [hrel]
    have hL : |(∏ k : Fin d, v k) * (evalMatrix d α Q).det| =
        (∏ k : Fin d, v k) * |(evalMatrix d α Q).det| := by
      rw [abs_mul, abs_of_pos hprodv_pos]
    have hR : |(∏ i : Fin d, mu i) * (scalMat d α v mu Q).det| =
        (∏ i : Fin d, mu i) * |(scalMat d α v mu Q).det| := by
      rw [abs_mul, abs_of_pos hprodmu_pos]
    rw [hL, hR] at h1
    exact h1
  have hD : Dval d α v ≤ (∏ i : Fin d, mu i) * (d.factorial : ℝ) := by
    calc
      Dval d α v = (∏ k : Fin d, v k) * pairProd d α := rfl
      _ ≤ (∏ k : Fin d, v k) * |(evalMatrix d α Q).det| := by
        exact mul_le_mul_of_nonneg_left hpair (le_of_lt hprodv_pos)
      _ = (∏ i : Fin d, mu i) * |(scalMat d α v mu Q).det| := habsrel
      _ ≤ (∏ i : Fin d, mu i) * (d.factorial : ℝ) := by
        exact mul_le_mul_of_nonneg_left hscal_det (le_of_lt hprodmu_pos)
  have hfact : (d.factorial : ℝ) ≤ (d : ℝ) ^ (1 * (d : ℝ)) := by
    have hpow : (d : ℝ) ^ (1 * (d : ℝ)) = (d : ℝ) ^ d := by
      rw [one_mul]
      exact Real.rpow_natCast (d : ℝ) d
    calc
      (d.factorial : ℝ) ≤ (d : ℝ) ^ d := by exact_mod_cast (Nat.factorial_le_pow d)
      _ = (d : ℝ) ^ (1 * (d : ℝ)) := hpow.symm
  calc
    Dval d α v ≤ (∏ i : Fin d, mu i) * (d.factorial : ℝ) := hD
    _ ≤ (∏ i : Fin d, mu i) * ((d : ℝ) ^ (1 * (d : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hfact (le_of_lt hprodmu_pos)
    _ = (d : ℝ) ^ (1 * (d : ℝ)) * (∏ i : Fin d, mu i) := by ring

theorem mink_lower : minkLower := by
  refine ⟨(1 : ℝ), by norm_num, ?_⟩
  intro d hd α hα v hv Q hQ hdeg mu hmu
  exact main_estimate d hd α hα v hv Q hQ hdeg mu hmu

end Submission.MinkLower

