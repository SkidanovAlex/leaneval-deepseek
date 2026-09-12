import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Polynomial.Norm
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.Polynomial.Basic

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open scoped BigOperators
open Polynomial
open Matrix

noncomputable section

/-! # Determinant ("det facile") estimate for n+1 linearly independent integer polynomials -/

/-- Row bound constant: for `Q` of degree ≤ n and `1 ≤ k ≤ n`,
`|eval ξ (D^k Q)| ≤ rowBound n ξ * ‖Q‖`. -/
private def rowBound (n : ℕ) (ξ : ℝ) : ℝ :=
  (n + 1 : ℝ) * (max 1 |ξ|) ^ n * (n : ℝ) ^ n

/-- The `(n+1)×(n+1)` matrix with rows indexed by derivative orders and columns by polynomials:
entry `(k,j)` is `(D^k Q_j)(ξ)`. -/
private def taylorMat (n : ℕ) (ξ : ℝ) (Q : Fin (n + 1) → ℝ[X]) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun k j => Polynomial.eval ξ (Polynomial.derivative^[k.val] (Q j))

/-- Coefficient matrix: entry `(m,j)` is the coefficient of `X^m` in `Q_j`. -/
private def coeffMat (n : ℕ) (Q : Fin (n + 1) → ℝ[X]) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun m j => (Q j).coeff m.val

/-- The change-of-basis matrix from monomials to Taylor data at `ξ`:
entry `(k,m)` is `(D^k X^m)(ξ)`. -/
private def derivBasis (n : ℕ) (ξ : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun k m => Polynomial.eval ξ (Polynomial.derivative^[k.val] ((Polynomial.X : ℝ[X]) ^ m.val))

/-- The integer coefficient matrix of an integer polynomial family. -/
private def intCoeffMat (n : ℕ) (P : Fin (n + 1) → Polynomial ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun m i => (P i).coeff m.val

/-! ## Polynomial analysis: evaluation and derivative bounds -/

/-- For a real polynomial of degree ≤ n, `|Q(ξ)| ≤ (n+1) * max(1,|ξ|)^n * ‖Q‖`. -/
private lemma abs_eval_le (n : ℕ) (ξ : ℝ) {Q : ℝ[X]} (hdeg : Q.natDegree ≤ n) :
    |Polynomial.eval ξ Q| ≤ (n + 1 : ℝ) * (max 1 |ξ|) ^ n * Q.supNorm := by
  let B : ℝ := max 1 |ξ|
  have hB1 : 1 ≤ B := by dsimp [B]; exact le_max_left 1 |ξ|
  have hB0 : 0 ≤ B := by dsimp [B]; exact le_trans zero_le_one (le_max_left _ _)
  have hxiB : |ξ| ≤ B := by dsimp [B]; exact le_max_right 1 |ξ|
  have hnlt : Q.natDegree < n + 1 := Nat.lt_succ_of_le hdeg
  rw [Polynomial.eval_eq_sum_range' hnlt ξ]
  calc
    |∑ i ∈ Finset.range (n + 1), Q.coeff i * ξ ^ i|
        ≤ ∑ i ∈ Finset.range (n + 1), |Q.coeff i * ξ ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (n + 1), |Q.coeff i| * |ξ| ^ i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [abs_mul, abs_pow]
    _ ≤ ∑ i ∈ Finset.range (n + 1), Q.supNorm * B ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          |Q.coeff i| * |ξ| ^ i ≤ Q.supNorm * |ξ| ^ i := by
            exact mul_le_mul_of_nonneg_right (Polynomial.le_supNorm Q i) (pow_nonneg (abs_nonneg _) i)
          _ ≤ Q.supNorm * B ^ i := by
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hxiB i) (Polynomial.supNorm_nonneg Q)
    _ ≤ ∑ i ∈ Finset.range (n + 1), Q.supNorm * B ^ n := by
        apply Finset.sum_le_sum
        intro i hi
        have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 hi_le) (Polynomial.supNorm_nonneg Q)
    _ = ((n + 1 : ℕ) : ℝ) * (Q.supNorm * B ^ n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (n + 1 : ℝ) * (Q.supNorm * B ^ n) := by norm_cast
    _ = (n + 1 : ℝ) * B ^ n * Q.supNorm := by ring


/-- Coefficient bound for iterated derivatives: `|(D^k Q)_m| ≤ n^k ‖Q‖` when `natDegree Q ≤ n`. -/
private lemma coeff_iterate_derivative_abs_le (n k m : ℕ) {Q : ℝ[X]}
    (hdeg : Q.natDegree ≤ n) :
    |((Polynomial.derivative^[k]) Q).coeff m| ≤ (n : ℝ) ^ k * Q.supNorm := by
  by_cases hmk : m + k ≤ n
  · have hmkR : ((m + k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmk
    have hdesc : ((m + k).descFactorial k : ℝ) ≤ (n : ℝ) ^ k := by
      have hnat : (m + k).descFactorial k ≤ n ^ k := by
        calc
          (m + k).descFactorial k ≤ (m + k) ^ k := Nat.descFactorial_le_pow (m + k) k
          _ ≤ n ^ k := pow_le_pow_left₀ (Nat.zero_le _) hmk k
      exact_mod_cast hnat
    rw [Polynomial.coeff_iterate_derivative]
    calc
      |((m + k).descFactorial k • Q.coeff (m + k) : ℝ)| ≤
          ((m + k).descFactorial k : ℝ) * |Q.coeff (m + k)| := by
            rw [nsmul_eq_mul, abs_mul]
            rw [abs_of_nonneg (by exact_mod_cast (Nat.zero_le _) : 0 ≤ ((m + k).descFactorial k : ℝ))]
      _ ≤ (n : ℝ) ^ k * Q.supNorm := by
        exact mul_le_mul hdesc (Polynomial.le_supNorm Q (m + k)) (abs_nonneg _)
          (pow_nonneg (by positivity : 0 ≤ (n : ℝ)) k)
  · have hmn : n < m + k := by omega
    have hc : Q.coeff (m + k) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hmn)
    rw [Polynomial.coeff_iterate_derivative, hc]
    simp
    exact mul_nonneg (pow_nonneg (by positivity : 0 ≤ (n : ℝ)) k) (Polynomial.supNorm_nonneg Q)


/-- `supNorm (D^k Q) ≤ n^k ‖Q‖` when `natDegree Q ≤ n`. -/
private lemma supNorm_le_of_forall_coeff_le {Q : ℝ[X]} {B : ℝ}
    (h : ∀ m : ℕ, |Q.coeff m| ≤ B) : Q.supNorm ≤ B := by
  rcases Polynomial.exists_eq_supNorm Q with ⟨m, hm⟩
  rw [hm]
  exact h m

private lemma supNorm_iterate_derivative_le (n k : ℕ) {Q : ℝ[X]}
    (hdeg : Q.natDegree ≤ n) :
    ((Polynomial.derivative^[k]) Q).supNorm ≤ (n : ℝ) ^ k * Q.supNorm := by
  apply supNorm_le_of_forall_coeff_le
  intro m
  exact coeff_iterate_derivative_abs_le n k m hdeg


/-- `|(D^k Q)(ξ)| ≤ rowBound n ξ * ‖Q‖` for `1 ≤ k ≤ n`, `natDegree Q ≤ n`. -/
private lemma abs_eval_iterate_derivative_le (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ)
    {Q : ℝ[X]} (hdeg : Q.natDegree ≤ n) {k : ℕ} (hkn : k ≤ n) :
    |Polynomial.eval ξ ((Polynomial.derivative^[k]) Q)| ≤ rowBound n ξ * Q.supNorm := by
  let B : ℝ := max 1 |ξ|
  have hB1 : 1 ≤ B := by dsimp [B]; exact le_max_left 1 |ξ|
  have hB0 : 0 ≤ B := by dsimp [B]; exact le_trans zero_le_one (le_max_left _ _)
  have hdegk : ((Polynomial.derivative^[k]) Q).natDegree ≤ n := by
    calc
      ((Polynomial.derivative^[k]) Q).natDegree ≤ Q.natDegree - k :=
        Polynomial.natDegree_iterate_derivative Q k
      _ ≤ n - k := by omega
      _ ≤ n := Nat.sub_le _ _
  have h1 := abs_eval_le n ξ hdegk
  have h2 := supNorm_iterate_derivative_le n k hdeg
  have hnK : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hpk : (n : ℝ) ^ k ≤ (n : ℝ) ^ n := pow_le_pow_right₀ hnK hkn
  have hleft : 0 ≤ (n + 1 : ℝ) * B ^ n := mul_nonneg (by positivity) (pow_nonneg hB0 n)
  calc
    |Polynomial.eval ξ ((Polynomial.derivative^[k]) Q)| ≤ (n + 1 : ℝ) * B ^ n * ((Polynomial.derivative^[k]) Q).supNorm := h1
    _ ≤ (n + 1 : ℝ) * B ^ n * ((n : ℝ) ^ k * Q.supNorm) := by
      exact mul_le_mul_of_nonneg_left h2 hleft
    _ = ((n + 1 : ℝ) * B ^ n * (n : ℝ) ^ k) * Q.supNorm := by ring
    _ ≤ ((n + 1 : ℝ) * B ^ n * (n : ℝ) ^ n) * Q.supNorm := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpk hleft) (Polynomial.supNorm_nonneg Q)
    _ = rowBound n ξ * Q.supNorm := by rfl


/-! ## Lower bound: `|det Taylor| ≥ 1` from the integer determinant -/

/-- Membership of degree-≤n polynomials in `degreeLT (n+1)`. -/
private lemma mem_degreeLT_of_natDegree_le (n : ℕ) {Q : ℝ[X]} (hdeg : Q.natDegree ≤ n) :
    Q ∈ Polynomial.degreeLT ℝ (n + 1) := by
  rw [Polynomial.mem_degreeLT]
  have hd : Q.degree ≤ (n : WithBot ℕ) := (Polynomial.natDegree_le_iff_degree_le).mp hdeg
  exact lt_of_le_of_lt hd (by exact_mod_cast (Nat.lt_succ_self n))

private lemma linearIndependent_coeff_vectors (n : ℕ) {Q : Fin (n + 1) → ℝ[X]}
    (hdeg : ∀ i, (Q i).natDegree ≤ n)
    (hlin : LinearIndependent ℝ Q) :
    LinearIndependent ℝ (fun i : Fin (n + 1) => (fun m : Fin (n + 1) => (Q i).coeff m.val)) := by
  let S : Submodule ℝ ℝ[X] := Polynomial.degreeLT ℝ (n + 1)
  let v : Fin (n + 1) → S := fun i => ⟨Q i, mem_degreeLT_of_natDegree_le n (hdeg i)⟩
  have hS0 : LinearIndependent ℝ (fun i : Fin (n + 1) => S.subtype (v i)) := by
    simpa [v, S] using hlin
  have hS : LinearIndependent ℝ v := LinearIndependent.of_comp (S.subtype) hS0
  have hEv : LinearIndependent ℝ (fun i => (Polynomial.degreeLTEquiv ℝ (n + 1)) (v i)) := by
    exact LinearIndependent.map' hS ((Polynomial.degreeLTEquiv ℝ (n + 1)).toLinearMap)
      (LinearEquiv.ker (Polynomial.degreeLTEquiv ℝ (n + 1)))
  convert hEv using 1
  ext i m
  rfl

private lemma eval_iterate_derivative_sum_coeff (n : ℕ) (ξ : ℝ) {q : ℝ[X]}
    (hq : q ∈ Polynomial.degreeLT ℝ (n + 1)) (k : ℕ) :
    Polynomial.eval ξ (Polynomial.derivative^[k] q) =
      ∑ m : Fin (n + 1), (q.coeff m.val) *
        Polynomial.eval ξ (Polynomial.derivative^[k] ((Polynomial.X : ℝ[X]) ^ m.val)) := by
  have hqdeg : q.degree < ↑(n + 1) := Polynomial.mem_degreeLT.mp hq
  have hrep : q = ∑ m : Fin (n + 1),
      Polynomial.C (q.coeff m.val) * (Polynomial.X : ℝ[X]) ^ m.val := by
    rw [Polynomial.sum_fin (fun (i : ℕ) (c : ℝ) => Polynomial.C c * (Polynomial.X : ℝ[X]) ^ i)
      (by intro i; simp) hqdeg]
    simp [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.sum_monomial_eq]
  calc
    Polynomial.eval ξ (Polynomial.derivative^[k] q)
      = Polynomial.eval ξ (Polynomial.derivative^[k]
          (∑ m : Fin (n + 1), Polynomial.C (q.coeff m.val) * (Polynomial.X : ℝ[X]) ^ m.val)) := by
            exact congrArg (fun p => Polynomial.eval ξ (Polynomial.derivative^[k] p)) hrep
    _ = Polynomial.eval ξ (∑ m : Fin (n + 1),
          Polynomial.C (q.coeff m.val) * (Polynomial.derivative^[k] ((Polynomial.X : ℝ[X]) ^ m.val))) := by
        congr 1
        rw [Polynomial.iterate_derivative_sum k Finset.univ
          (fun m : Fin (n + 1) => Polynomial.C (q.coeff m.val) * (Polynomial.X : ℝ[X]) ^ m.val)]
        refine Finset.sum_congr rfl ?_
        intro m hm
        rw [Polynomial.iterate_derivative_C_mul]
    _ = ∑ m : Fin (n + 1),
        Polynomial.eval ξ (Polynomial.C (q.coeff m.val) *
          (Polynomial.derivative^[k] ((Polynomial.X : ℝ[X]) ^ m.val))) := by
        exact map_sum (Polynomial.evalRingHom ξ : ℝ[X] →+ ℝ)
          (fun m : Fin (n + 1) => Polynomial.C (q.coeff m.val) *
            (Polynomial.derivative^[k] ((Polynomial.X : ℝ[X]) ^ m.val))) Finset.univ
    _ = ∑ m : Fin (n + 1), (q.coeff m.val) *
        Polynomial.eval ξ (Polynomial.derivative^[k] ((Polynomial.X : ℝ[X]) ^ m.val)) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        rw [Polynomial.eval_mul, Polynomial.eval_C]

private lemma taylor_eq_basis_mul_coeff (n : ℕ) (ξ : ℝ) {Q : Fin (n + 1) → ℝ[X]}
    (hdeg : ∀ i, (Q i).natDegree ≤ n) :
    taylorMat n ξ Q = derivBasis n ξ * coeffMat n Q := by
  ext k j
  change Polynomial.eval ξ (Polynomial.derivative^[k.val] (Q j)) =
    ∑ m : Fin (n + 1),
      Polynomial.eval ξ (Polynomial.derivative^[k.val] ((Polynomial.X : ℝ[X]) ^ m.val)) *
        (Q j).coeff m.val
  rw [eval_iterate_derivative_sum_coeff n ξ (mem_degreeLT_of_natDegree_le n (hdeg j)) k.val]
  apply Finset.sum_congr rfl
  intro m hm
  rw [mul_comm]

private lemma derivBasis_diag (n : ℕ) (ξ : ℝ) (i : Fin (n + 1)) :
    derivBasis n ξ i i = ((i.val).factorial : ℝ) := by
  change Polynomial.eval ξ (Polynomial.derivative^[i.val] ((Polynomial.X : ℝ[X]) ^ i.val)) =
    ((i.val).factorial : ℝ)
  have hX : (Polynomial.X - Polynomial.C (0 : ℝ)) = (Polynomial.X : ℝ[X]) := by simp
  rw [← hX]
  have h := Polynomial.iterate_derivative_X_sub_pow_self (i.val) (0 : ℝ)
  rw [h]
  simp

private lemma derivBasis_offdiag (n : ℕ) (ξ : ℝ) {k m : Fin (n + 1)} (hkm : m < k) :
    derivBasis n ξ k m = 0 := by
  change Polynomial.eval ξ (Polynomial.derivative^[k.val] ((Polynomial.X : ℝ[X]) ^ m.val)) = 0
  have hmk : m.val < k.val := by simpa using hkm
  have hdeg : ((Polynomial.X : ℝ[X]) ^ m.val).degree < ↑(k.val) := by
    exact lt_of_le_of_lt (Polynomial.degree_X_pow_le m.val) (by exact_mod_cast hmk)
  have hz : Polynomial.derivative^[k.val] ((Polynomial.X : ℝ[X]) ^ m.val) = 0 :=
    Polynomial.iterate_derivative_eq_zero_of_degree_lt hdeg
  rw [hz]
  simp

private lemma det_derivBasis (n : ℕ) (ξ : ℝ) :
    (derivBasis n ξ).det = ∏ i : Fin (n + 1), ((i.val).factorial : ℝ) := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_congr rfl
    intro i hi
    exact derivBasis_diag n ξ i
  · intro k m hkm
    exact derivBasis_offdiag n ξ hkm

private lemma one_le_det_derivBasis (n : ℕ) (ξ : ℝ) : 1 ≤ (derivBasis n ξ).det := by
  rw [det_derivBasis]
  apply Finset.one_le_prod
  intro i hi
  have hf : 1 ≤ (i.val).factorial := by
    have hpos : 0 < (i.val).factorial := Nat.factorial_pos (i.val)
    omega
  exact_mod_cast hf

private lemma abs_int_ge_one_of_ne_zero (z : ℤ) (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
  by_cases hz0 : 0 ≤ z
  · have hz1 : (1 : ℤ) ≤ z := by omega
    rw [abs_of_nonneg (by exact_mod_cast hz0)]
    exact_mod_cast hz1
  · have hzneg : z < 0 := lt_of_not_ge hz0
    have hzm : z ≤ -1 := by omega
    have hzr : (z : ℝ) < 0 := by exact_mod_cast hzneg
    rw [abs_of_neg hzr]
    have hz1c : (z : ℝ) ≤ -(1 : ℝ) := by exact_mod_cast hzm
    linarith

private lemma intCoeffMat_det_ne_zero (n : ℕ) {P : Fin (n + 1) → Polynomial ℤ}
    (hdeg : ∀ i, (P i).natDegree ≤ n)
    (hlin : LinearIndependent ℝ (fun i => (P i).map (Int.castRingHom ℝ))) :
    (intCoeffMat n P).det ≠ 0 := by
  let Q : Fin (n + 1) → ℝ[X] := fun i => (P i).map (Int.castRingHom ℝ)
  let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := coeffMat n Q
  have hdegQ : ∀ i, (Q i).natDegree ≤ n := by
    intro i
    dsimp [Q]
    exact le_trans (Polynomial.natDegree_map_le) (hdeg i)
  have hcvec : LinearIndependent ℝ (fun i : Fin (n + 1) => (fun m : Fin (n + 1) => (Q i).coeff m.val)) :=
    linearIndependent_coeff_vectors n hdegQ hlin
  have hcols : C.col = (fun i : Fin (n + 1) => (fun m : Fin (n + 1) => (Q i).coeff m.val)) := by
    ext i m
    rfl
  have hc : LinearIndependent ℝ C.col := by simpa [hcols] using hcvec
  have hCunit : IsUnit C := (Matrix.linearIndependent_cols_iff_isUnit (A := C)).mp hc
  have hCdne : C.det ≠ 0 := (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det C).mp hCunit))
  have hcast : C.det = ((intCoeffMat n P).det : ℝ) := by
    have hCM : C = (Int.castRingHom ℝ).mapMatrix (intCoeffMat n P) := by
      ext m i
      simp [C, Q, coeffMat, intCoeffMat, Polynomial.coeff_map]
    calc
      C.det = ((Int.castRingHom ℝ).mapMatrix (intCoeffMat n P)).det := by rw [hCM]
      _ = ((intCoeffMat n P).det : ℝ) := by
        calc
          ((Int.castRingHom ℝ).mapMatrix (intCoeffMat n P)).det =
              (Int.castRingHom ℝ) ((intCoeffMat n P).det) := by
                rw [(Int.castRingHom ℝ).map_det (intCoeffMat n P)]
          _ = ((intCoeffMat n P).det : ℝ) := rfl
  intro hN
  apply hCdne
  rw [hcast, hN]
  norm_num

private lemma abs_det_coeffMat_ge_one (n : ℕ) {P : Fin (n + 1) → Polynomial ℤ}
    (hdeg : ∀ i, (P i).natDegree ≤ n)
    (hlin : LinearIndependent ℝ (fun i => (P i).map (Int.castRingHom ℝ))) :
    1 ≤ |(coeffMat n (fun i => (P i).map (Int.castRingHom ℝ))).det| := by
  let Q : Fin (n + 1) → ℝ[X] := fun i => (P i).map (Int.castRingHom ℝ)
  have hdegQ : ∀ i, (Q i).natDegree ≤ n := by
    intro i
    dsimp [Q]
    exact le_trans (Polynomial.natDegree_map_le) (hdeg i)
  have hNd : (intCoeffMat n P).det ≠ 0 := intCoeffMat_det_ne_zero n hdeg hlin
  have hcast : (coeffMat n Q).det = ((intCoeffMat n P).det : ℝ) := by
    have hCM : coeffMat n Q = (Int.castRingHom ℝ).mapMatrix (intCoeffMat n P) := by
      ext m i
      simp [Q, coeffMat, intCoeffMat, Polynomial.coeff_map]
    calc
      (coeffMat n Q).det = ((Int.castRingHom ℝ).mapMatrix (intCoeffMat n P)).det := by rw [hCM]
      _ = ((intCoeffMat n P).det : ℝ) := by
        calc
          ((Int.castRingHom ℝ).mapMatrix (intCoeffMat n P)).det =
              (Int.castRingHom ℝ) ((intCoeffMat n P).det) := by
                rw [(Int.castRingHom ℝ).map_det (intCoeffMat n P)]
          _ = ((intCoeffMat n P).det : ℝ) := rfl
  change 1 ≤ |(coeffMat n Q).det|
  rw [hcast]
  exact abs_int_ge_one_of_ne_zero ((intCoeffMat n P).det) hNd

private lemma taylor_det_abs_ge_one (n : ℕ) (ξ : ℝ) {P : Fin (n + 1) → Polynomial ℤ}
    (hdeg : ∀ i, (P i).natDegree ≤ n)
    (hlin : LinearIndependent ℝ (fun i => (P i).map (Int.castRingHom ℝ))) :
    1 ≤ |(taylorMat n ξ (fun i => (P i).map (Int.castRingHom ℝ))).det| := by
  let Q : Fin (n + 1) → ℝ[X] := fun i => (P i).map (Int.castRingHom ℝ)
  have hdegQ : ∀ i, (Q i).natDegree ≤ n := by
    intro i
    dsimp [Q]
    exact le_trans (Polynomial.natDegree_map_le) (hdeg i)
  have h1 : taylorMat n ξ Q = derivBasis n ξ * coeffMat n Q := taylor_eq_basis_mul_coeff n ξ hdegQ
  have hb : 1 ≤ (derivBasis n ξ).det := one_le_det_derivBasis n ξ
  have hc : 1 ≤ |(coeffMat n Q).det| := by
    simpa [Q] using abs_det_coeffMat_ge_one n hdeg hlin
  have hb0 : 0 ≤ (derivBasis n ξ).det := le_trans zero_le_one hb
  have hprod : 1 ≤ (derivBasis n ξ).det * |(coeffMat n Q).det| := by
    calc
      1 ≤ (derivBasis n ξ).det := hb
      _ ≤ (derivBasis n ξ).det * |(coeffMat n Q).det| := by
        simpa using (mul_le_mul_of_nonneg_left hc hb0)
  calc
    1 ≤ (derivBasis n ξ).det * |(coeffMat n Q).det| := hprod
    _ = |(derivBasis n ξ).det| * |(coeffMat n Q).det| := by
      rw [abs_of_nonneg hb0]
    _ = |((derivBasis n ξ).det * (coeffMat n Q).det)| := by
      rw [← abs_mul]
    _ = |((derivBasis n ξ) * (coeffMat n Q)).det| := by
      rw [Matrix.det_mul]
    _ = |(taylorMat n ξ Q).det| := by
      rw [← h1]

private lemma det_abs_le_sum_abs_prod (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    |M.det| ≤ ∑ σ : Equiv.Perm (Fin (n + 1)), ∏ j : Fin (n + 1), |M (σ j) j| := by
  rw [Matrix.det_apply']
  calc
    |∑ σ : Equiv.Perm (Fin (n + 1)), (↑↑(Equiv.Perm.sign σ) : ℝ) * (∏ j : Fin (n + 1), M (σ j) j)|
        ≤ ∑ σ : Equiv.Perm (Fin (n + 1)), |(↑↑(Equiv.Perm.sign σ) : ℝ) * (∏ j : Fin (n + 1), M (σ j) j)| :=
            Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)), ∏ j : Fin (n + 1), |M (σ j) j| := by
        apply Finset.sum_congr rfl
        intro σ hσ
        calc
          |(↑↑(Equiv.Perm.sign σ) : ℝ) * (∏ j : Fin (n + 1), M (σ j) j)|
              = |(↑↑(Equiv.Perm.sign σ) : ℝ)| * |∏ j : Fin (n + 1), M (σ j) j| := abs_mul _ _
          _ = |∏ j : Fin (n + 1), M (σ j) j| := by
              have hε : |(↑↑(Equiv.Perm.sign σ) : ℝ)| = 1 := by
                rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
                · simp [h]
                · simp [h]
              rw [hε, one_mul]
          _ = ∏ j : Fin (n + 1), |M (σ j) j| := by
              simpa using (Finset.abs_prod (Finset.univ : Finset (Fin (n + 1))) (fun j : Fin (n + 1) => M (σ j) j))


/-- Each permutation-product is bounded by `r^n (∏ H) (∑ x/H)` given the special entry bounds. -/
private lemma prod_entry_bound (n : ℕ) {x H : Fin (n + 1) → ℝ} {r : ℝ}
    (hH : ∀ j, 0 < H j) (hr : 0 ≤ r) (hx : ∀ j, 0 ≤ x j)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∏ j : Fin (n + 1), (if σ j = 0 then x j else r * H j)) ≤
      r ^ n * (∏ j : Fin (n + 1), H j) * (∑ j : Fin (n + 1), x j / H j) := by
  let j0 : Fin (n + 1) := σ.symm 0
  let P : Finset (Fin (n + 1)) := (Finset.univ : Finset (Fin (n + 1))).erase j0
  have hmem : j0 ∈ (Finset.univ : Finset (Fin (n + 1))) := Finset.mem_univ j0
  have hσ0 : σ j0 = 0 := by
    dsimp [j0]
    simp
  have hcard : P.card = n := by
    dsimp [P]
    rw [Finset.card_erase_of_mem hmem]
    simp
  have hσne : ∀ j : Fin (n + 1), j ∈ P → σ j ≠ 0 := by
    intro j hj hz
    apply (Finset.mem_erase.mp hj).1
    exact σ.injective (by simpa [hσ0] using hz)
  have hprod1 : (∏ j : Fin (n + 1), (if σ j = 0 then x j else r * H j)) =
      x j0 * (r ^ n * ∏ j ∈ P, H j) := by
    calc
      (∏ j : Fin (n + 1), (if σ j = 0 then x j else r * H j))
          = x j0 * ∏ j ∈ P, (if σ j = 0 then x j else r * H j) := by
              have hstep := Finset.mul_prod_erase (s := Finset.univ) (f := fun j : Fin (n + 1) =>
                (if σ j = 0 then x j else r * H j)) (a := j0) hmem
              simpa [P, hσ0] using hstep.symm
      _ = x j0 * (∏ j ∈ P, (r * H j)) := by
              congr 1
              refine Finset.prod_congr rfl ?_
              intro j hj
              have hne : σ j ≠ 0 := hσne j hj
              by_cases hjz : σ j = 0
              · exact False.elim (hne hjz)
              · simp [hjz]
      _ = x j0 * (r ^ n * ∏ j ∈ P, H j) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  calc
    (∏ j : Fin (n + 1), (if σ j = 0 then x j else r * H j)) ≤
        x j0 * (r ^ n * ∏ j ∈ P, H j) := by rw [hprod1]
    _ ≤ r ^ n * (∏ j : Fin (n + 1), H j) * (∑ j : Fin (n + 1), x j / H j) := by
        have hprodH : (∏ j ∈ P, H j) * H j0 = ∏ j : Fin (n + 1), H j := by
          have hstep := Finset.mul_prod_erase (s := Finset.univ) (f := fun j : Fin (n + 1) => H j) (a := j0) hmem
          simpa [P, mul_comm] using hstep
        have hsum_single : x j0 ≤ H j0 * (∑ j : Fin (n + 1), x j / H j) := by
          have hterm : x j0 / H j0 ≤ ∑ j : Fin (n + 1), x j / H j := by
            exact Finset.single_le_sum (fun j hj => div_nonneg (hx j) (le_of_lt (hH j))) (Finset.mem_univ j0)
          have hxeq : x j0 = H j0 * (x j0 / H j0) := by
            field_simp [ne_of_gt (hH j0)]
          rw [hxeq]
          exact mul_le_mul_of_nonneg_left hterm (le_of_lt (hH j0))
        have hnonneg : 0 ≤ r ^ n * ∏ j ∈ P, H j := by
          exact mul_nonneg (pow_nonneg hr n) (Finset.prod_nonneg (fun j hj => le_of_lt (hH j)))
        calc
          x j0 * (r ^ n * ∏ j ∈ P, H j) = (r ^ n * ∏ j ∈ P, H j) * x j0 := by ring
          _ ≤ (r ^ n * ∏ j ∈ P, H j) * (H j0 * (∑ j : Fin (n + 1), x j / H j)) := by
            exact mul_le_mul_of_nonneg_left hsum_single hnonneg
          _ = r ^ n * (∏ j ∈ P, H j) * (H j0 * (∑ j : Fin (n + 1), x j / H j)) := by ring
          _ = r ^ n * ((∏ j ∈ P, H j) * H j0) * (∑ j : Fin (n + 1), x j / H j) := by ring
          _ = r ^ n * (∏ j : Fin (n + 1), H j) * (∑ j : Fin (n + 1), x j / H j) := by rw [hprodH]


/-- Nonzero members of the family give `H_j > 0`. -/
private lemma supNorm_pos_of_ne_zero {Q : ℝ[X]} (hQ : Q ≠ 0) : 0 < Q.supNorm := by
  have h : Q.supNorm ≠ 0 := by
    intro hz
    apply hQ
    exact (Polynomial.supNorm_eq_zero_iff Q).mp hz
  exact lt_of_le_of_ne (Polynomial.supNorm_nonneg Q) (Ne.symm h)


/-- `(D^k Q_j)(ξ)` entrywise bounds against row 0 / `rowBound`. -/
private lemma taylor_entry_bound (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ)
    {Q : Fin (n + 1) → ℝ[X]} (hdeg : ∀ i, (Q i).natDegree ≤ n) (k j : Fin (n + 1)) :
    |(taylorMat n ξ Q) k j| ≤
      (if k = 0 then |Polynomial.eval ξ (Q j)| else rowBound n ξ * (Q j).supNorm) := by
  by_cases hk0 : k = 0
  · subst k
    simp [taylorMat]
  · have hk0' : k.val ≠ 0 := by
      intro hz
      apply hk0
      exact Fin.ext (by simpa using hz)
    have hk1 : 1 ≤ k.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0')
    have hkn : k.val ≤ n := Nat.le_of_lt_succ k.isLt
    have hb := abs_eval_iterate_derivative_le n hn ξ (hdeg j) hkn
    simpa [taylorMat, hk0] using hb


/-- The upper bound `|det (Taylor matrix)| ≤ (n+1)! rowBound^n (∏ H) (∑ |eval|/H)`. -/
private lemma taylor_det_abs_le (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ)
    {Q : Fin (n + 1) → ℝ[X]} (hdeg : ∀ i, (Q i).natDegree ≤ n)
    (hQ0 : ∀ i, Q i ≠ 0) :
    |(taylorMat n ξ Q).det| ≤
      ((n + 1).factorial : ℝ) * (rowBound n ξ) ^ n * (∏ j : Fin (n + 1), (Q j).supNorm) *
        (∑ j : Fin (n + 1), |Polynomial.eval ξ (Q j)| / (Q j).supNorm) := by
  let M := taylorMat n ξ Q
  let H : Fin (n + 1) → ℝ := fun j => (Q j).supNorm
  let x : Fin (n + 1) → ℝ := fun j => |Polynomial.eval ξ (Q j)|
  let r : ℝ := rowBound n ξ
  have hH : ∀ j, 0 < H j := by intro j; dsimp [H]; exact supNorm_pos_of_ne_zero (hQ0 j)
  have hr : 0 ≤ r := by
    dsimp [r, rowBound]
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (le_trans zero_le_one (le_max_left 1 |ξ|)) n)) (pow_nonneg (by positivity : 0 ≤ (n : ℝ)) n)
  have hx : ∀ j, 0 ≤ x j := by intro j; dsimp [x]; exact abs_nonneg _
  have hb : ∀ k j, |M k j| ≤ (if k = 0 then x j else r * H j) := by
    intro k j
    simpa [M, H, x, r] using taylor_entry_bound n hn ξ hdeg k j
  have hb2 : ∀ σ : Equiv.Perm (Fin (n + 1)),
      (∏ j : Fin (n + 1), |M (σ j) j|) ≤ (∏ j : Fin (n + 1), (if σ j = 0 then x j else r * H j)) := by
    intro σ
    refine Finset.prod_le_prod ?h0 ?h1
    · intro j hj
      exact abs_nonneg _
    · intro j hj
      exact hb (σ j) j
  have hb3 : ∀ σ : Equiv.Perm (Fin (n + 1)),
      (∏ j : Fin (n + 1), (if σ j = 0 then x j else r * H j)) ≤
        r ^ n * (∏ j : Fin (n + 1), H j) * (∑ j : Fin (n + 1), x j / H j) := by
    intro σ
    exact prod_entry_bound n hH hr hx σ
  have hdet : |M.det| ≤
      ((n + 1).factorial : ℝ) * r ^ n * (∏ j : Fin (n + 1), H j) * (∑ j : Fin (n + 1), x j / H j) := by
    calc
      |M.det| ≤ ∑ σ : Equiv.Perm (Fin (n + 1)), ∏ j : Fin (n + 1), |M (σ j) j| := det_abs_le_sum_abs_prod n M
      _ ≤ ∑ σ : Equiv.Perm (Fin (n + 1)), (∏ j : Fin (n + 1), (if σ j = 0 then x j else r * H j)) := by
        apply Finset.sum_le_sum
        intro σ hσ
        exact hb2 σ
      _ ≤ ∑ σ : Equiv.Perm (Fin (n + 1)), (r ^ n * (∏ j : Fin (n + 1), H j) * (∑ j : Fin (n + 1), x j / H j)) := by
        apply Finset.sum_le_sum
        intro σ hσ
        exact hb3 σ
      _ = ((n + 1).factorial : ℝ) * r ^ n * (∏ j : Fin (n + 1), H j) * (∑ j : Fin (n + 1), x j / H j) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        ring
  simpa [M, r, H, x] using hdet


/-! ## Main statement -/
theorem poly_det_facile (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : Fin (n + 1) → Polynomial ℤ,
      (∀ i : Fin (n + 1), (P i).natDegree ≤ n) →
      LinearIndependent ℝ (fun i : Fin (n + 1) => (P i).map (Int.castRingHom ℝ)) →
      1 ≤ c * (∏ i : Fin (n + 1), ((P i).map (Int.castRingHom ℝ)).supNorm) *
        (∑ i : Fin (n + 1),
          ‖Polynomial.eval ξ ((P i).map (Int.castRingHom ℝ))‖ /
            ((P i).map (Int.castRingHom ℝ)).supNorm) := by
  let c : ℝ := ((n + 1).factorial : ℝ) * (rowBound n ξ) ^ n
  refine ⟨c, ?cpos, ?cmain⟩
  · have hrow : 0 < rowBound n ξ := by
      dsimp [rowBound]
      exact mul_pos (mul_pos (by positivity : 0 < (n + 1 : ℝ))
        (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left 1 |ξ|)) n))
        (pow_pos (by exact_mod_cast hn : 0 < (n : ℝ)) n)
    dsimp [c]
    exact mul_pos (by exact_mod_cast (Nat.factorial_pos (n + 1))) (pow_pos hrow n)
  · intro P hdeg hlin
    let Q : Fin (n + 1) → ℝ[X] := fun i => (P i).map (Int.castRingHom ℝ)
    have hdegQ : ∀ i, (Q i).natDegree ≤ n := by
      intro i
      dsimp [Q]
      exact le_trans (Polynomial.natDegree_map_le) (hdeg i)
    have hQ0 : ∀ i, Q i ≠ 0 := by
      intro i hz
      have hdep : ¬ LinearIndependent ℝ Q := by
        rw [Fintype.not_linearIndependent_iffₛ]
        refine ⟨fun j => if j = i then (1 : ℝ) else 0, fun _ => 0, ?_⟩
        constructor
        · simp [hz]
        · refine ⟨i, ?_⟩
          norm_num
      exact False.elim (hdep (by simpa [Q] using hlin))
    have hlower : 1 ≤ |(taylorMat n ξ Q).det| := by
      simpa [Q] using taylor_det_abs_ge_one n ξ hdeg hlin
    have hupper : |(taylorMat n ξ Q).det| ≤
        ((n + 1).factorial : ℝ) * (rowBound n ξ) ^ n *
          (∏ i : Fin (n + 1), (Q i).supNorm) *
          (∑ i : Fin (n + 1), |Polynomial.eval ξ (Q i)| / (Q i).supNorm) := by
      simpa [Q] using (taylor_det_abs_le n hn ξ hdegQ hQ0)
    have hmain : 1 ≤ c * (∏ i : Fin (n + 1), (Q i).supNorm) *
        (∑ i : Fin (n + 1), |Polynomial.eval ξ (Q i)| / (Q i).supNorm) := by
      exact le_trans hlower (by simpa [c] using hupper)
    simpa [Q, Real.norm_eq_abs] using hmain

end