import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Submission.Commons.LinearAlgebra.Matrix.det_natDegree_le
import Submission.Commons.LinearAlgebra.Matrix.coeff_det_const_cols
import Submission.Commons.Data.Int.exists_int_avoid_roots
import Submission.Commons.LinearAlgebra.Basis.exists_linearIndependent_extend

set_option maxHeartbeats 0

noncomputable section
namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree
open Polynomial
open scoped BigOperators


/-! ## 1. Polynomials of degree ≤ n : coefficient vectors and linear independence -/

/-- A polynomial of natDegree ≤ n lies in `degreeLT ℝ (n + 1)`. -/
lemma degreeLT_of_natDegree_le {n : ℕ} {P : Polynomial ℝ} (h : P.natDegree ≤ n) :
    P ∈ Polynomial.degreeLT ℝ (n + 1) := by
  rw [Polynomial.mem_degreeLT]
  exact lt_of_le_of_lt (Polynomial.degree_le_natDegree) (by exact_mod_cast Nat.lt_succ_of_le h)

/-- Coefficient vector of a polynomial, on `X^0, ..., X^n`. -/
def coeffV (n : ℕ) (P : Polynomial ℝ) : Fin (n + 1) → ℝ := fun i => P.coeff i.val

/-- `coeffV` restricted to degree-≤n polynomials is the `degreeLTEquiv`. -/
lemma coeffV_eq_degreeLTEquiv {n : ℕ} {P : Polynomial ℝ} (h : P.natDegree ≤ n) :
    coeffV n P = (Polynomial.degreeLTEquiv ℝ (n + 1) ⟨P, degreeLT_of_natDegree_le h⟩) := by
  ext i
  rfl

/-- Polynomial linear independence implies coefficient-vector linear independence
(for degree-≤n families). -/
lemma linearIndependent_coeffV_of_poly {ι : Type*} {n : ℕ} (v : ι → Polynomial ℝ)
    (hdeg : ∀ i, (v i).natDegree ≤ n)
    (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ (fun i => coeffV n (v i)) := by
  let D : Submodule ℝ (Polynomial ℝ) := Polynomial.degreeLT ℝ (n + 1)
  let vD : ι → D := fun i => ⟨v i, degreeLT_of_natDegree_le (hdeg i)⟩
  have hD0 : LinearIndependent ℝ (fun i : ι => D.subtype (vD i)) := by
    simpa [vD] using hv
  have hD : LinearIndependent ℝ vD := LinearIndependent.of_comp D.subtype hD0
  have hmap : LinearIndependent ℝ (fun i : ι => (Polynomial.degreeLTEquiv ℝ (n + 1)) (vD i)) :=
    LinearIndependent.map' hD (Polynomial.degreeLTEquiv ℝ (n + 1)).toLinearMap (by simp)
  convert hmap using 1
  funext i
  exact coeffV_eq_degreeLTEquiv (hdeg i)

/-- Coefficient-vector linear independence implies polynomial linear independence
(for degree-≤n families). -/
lemma linearIndependent_poly_of_coeffV {ι : Type*} {n : ℕ} (v : ι → Polynomial ℝ)
    (hdeg : ∀ i, (v i).natDegree ≤ n)
    (hv : LinearIndependent ℝ (fun i => coeffV n (v i))) :
    LinearIndependent ℝ v := by
  let D : Submodule ℝ (Polynomial ℝ) := Polynomial.degreeLT ℝ (n + 1)
  let vD : ι → D := fun i => ⟨v i, degreeLT_of_natDegree_le (hdeg i)⟩
  have hmap : LinearIndependent ℝ (fun i : ι => (Polynomial.degreeLTEquiv ℝ (n + 1)) (vD i)) := by
    convert hv using 1
    funext i
    exact coeffV_eq_degreeLTEquiv (hdeg i)
  have hD : LinearIndependent ℝ vD :=
    LinearIndependent.of_comp (Polynomial.degreeLTEquiv ℝ (n + 1)).toLinearMap hmap
  change LinearIndependent ℝ (fun i : ι => D.subtype (vD i))
  exact LinearIndependent.map' hD D.subtype (by simp)

/-! ## 2. Binomial expansion and `lamEntry` -/

/-- `(X - C z)^e` expanded as a sum of monomials. -/
lemma X_sub_C_pow_eq_sum (e : ℕ) (z : ℝ) :
    (X - C z) ^ e = ∑ m ∈ Finset.range (e + 1),
      C (((e.choose m : ℝ) * (-z) ^ (e - m)) : ℝ) * X ^ m := by
  have h1 : (X - C z) = (X : Polynomial ℝ) + (-C z) := by ring
  rw [h1, add_pow]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hneg : (-C z) ^ (e - m) = C ((-z) ^ (e - m)) := by
    have h : (-C z : Polynomial ℝ) = C (-z) := by simp
    rw [h, map_pow]
  have hcast : ((e.choose m : ℕ) : Polynomial ℝ) = C ((e.choose m : ℝ)) := by norm_num
  calc
    X ^ m * (-C z) ^ (e - m) * ((e.choose m : ℕ) : Polynomial ℝ)
        = ((-C z) ^ (e - m)) * ((e.choose m : ℕ) : Polynomial ℝ) * X ^ m := by ring
    _ = C ((-z) ^ (e - m)) * C ((e.choose m : ℝ)) * X ^ m := by rw [hneg, hcast]
    _ = C (((e.choose m : ℝ) * (-z) ^ (e - m)) : ℝ) * X ^ m := by
        rw [← C_mul]; congr 1; ring

/-- The coefficient of `X^i` in `(X - C z)^e * A`, as a polynomial in `z`. -/
def lamEntry (e : ℕ) (A : Polynomial ℝ) (i : ℕ) : Polynomial ℝ :=
  ∑ r ∈ Finset.range (e + 1),
    Polynomial.C (((e.choose r : ℝ) * ((X ^ r * A).coeff i)) * (-1 : ℝ) ^ (e - r)) * X ^ (e - r)

/-- Evaluating `lamEntry` at `z` recovers the coefficient. -/
lemma lamEntry_eval (e : ℕ) (A : Polynomial ℝ) (i : ℕ) (z : ℝ) :
    (lamEntry e A i).eval z = ((X - C z) ^ e * A).coeff i := by
  let S : ℝ := ∑ m ∈ Finset.range (e + 1),
      ((e.choose m : ℝ) * ((X ^ m * A).coeff i)) * (-z) ^ (e - m)
  have hL : (∑ i_1 ∈ Finset.range (e + 1),
      eval z (C (((e.choose i_1 : ℝ) * ((X ^ i_1 * A).coeff i)) * (-1 : ℝ) ^ (e - i_1)) * X ^ (e - i_1))) = S := by
    dsimp [S]
    apply Finset.sum_congr rfl
    intro m hm
    rw [eval_C_mul, eval_pow, eval_X]
    rw [neg_pow]
    ring
  have hR : ((X - C z) ^ e * A).coeff i = S := by
    dsimp [S]
    rw [X_sub_C_pow_eq_sum e z]
    rw [Finset.sum_mul]
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro m hm
    calc
      (C (((e.choose m : ℝ) * (-z) ^ (e - m)) : ℝ) * X ^ m * A).coeff i
          = ((e.choose m : ℝ) * (-z) ^ (e - m)) * (X ^ m * A).coeff i := by
            rw [mul_assoc, coeff_C_mul]
      _ = ((e.choose m : ℝ) * ((X ^ m * A).coeff i)) * (-z) ^ (e - m) := by ring
  rw [lamEntry]
  rw [Polynomial.eval_finsetSum]
  exact hL.trans hR.symm

/-- `lamEntry` has degree at most `e`. -/
lemma natDegree_lamEntry_le (e : ℕ) (A : Polynomial ℝ) (i : ℕ) :
    (lamEntry e A i).natDegree ≤ e := by
  rw [lamEntry]
  refine le_trans (Polynomial.natDegree_sum_le (Finset.range (e + 1))
      (fun r => Polynomial.C (((e.choose r : ℝ) * ((X ^ r * A).coeff i)) * (-1 : ℝ) ^ (e - r)) * X ^ (e - r))) ?_
  rw [Finset.fold_max_le]
  constructor
  · simp
  · intro r hr
    calc
      (Polynomial.C (((e.choose r : ℝ) * ((X ^ r * A).coeff i)) * (-1 : ℝ) ^ (e - r)) * X ^ (e - r)).natDegree
          ≤ (Polynomial.C (((e.choose r : ℝ) * ((X ^ r * A).coeff i)) * (-1 : ℝ) ^ (e - r))).natDegree
            + (X ^ (e - r)).natDegree :=
            Polynomial.natDegree_mul_le
      _ = 0 + (e - r) := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
      _ ≤ e := by omega

/-- The top coefficient of `lamEntry` is `(-1)^e * A.coeff i`. -/
lemma coeff_e_lamEntry (e : ℕ) (A : Polynomial ℝ) (i : ℕ) :
    (lamEntry e A i).coeff e = (-1 : ℝ) ^ e * A.coeff i := by
  rw [lamEntry]
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (0 : ℕ)]
  · have h0 : (X ^ 0 * A).coeff i = A.coeff i := by simp
    rw [h0]
    have he0 : e - 0 = e := by omega
    rw [he0]
    have hc : (e.choose 0 : ℝ) = 1 := by norm_num [Nat.choose_zero_right]
    rw [hc, one_mul]
    simp only [Polynomial.coeff_C_mul_X_pow, if_pos]
    ring
  · intro r hr hrne
    rw [Polynomial.coeff_C_mul_X_pow]
    have hrlt : r < e + 1 := by simpa using hr
    have hr1 : 1 ≤ r := by omega
    have hrle : r ≤ e := by omega
    have he_pos : 0 < e := by omega
    have hne : e ≠ e - r := (ne_of_lt (Nat.sub_lt he_pos (by omega : 0 < r))).symm
    simp [hne]
  · intro h0
    exact False.elim (h0 (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le e))))

/-! ## 3. Square matrices built from the first two polynomials and a base matrix -/

/-- The real modified square matrix at parameters `(a,b)` (columns 0,1 replaced). -/
def modMatReal (n e0 : ℕ) (A0 : Polynomial ℝ) (e1 : ℕ) (A1 : Polynomial ℝ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (a b : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if j.val = 0 then ((X - C a) ^ e0 * A0).coeff i.val
             else if j.val = 1 then ((X - C b) ^ e1 * A1).coeff i.val
             else B i j

/-- λ-matrix over `ℝ[X]` (variable = first parameter) with column 0 of degree ≤ e0. -/
def lamMatReal (n e0 : ℕ) (A0 : Polynomial ℝ) (e1 : ℕ) (A1 : Polynomial ℝ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial ℝ) :=
  fun i j => if j.val = 0 then lamEntry e0 A0 i.val
             else if j.val = 1 then C (((X - C b) ^ e1 * A1).coeff i.val)
             else C (B i j)

/-- μ-matrix over `ℝ[X]` (variable = second parameter): column 1 has degree ≤ e1. -/
def muMat (n : ℕ) (e1 : ℕ) (A1 : Polynomial ℝ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial ℝ) :=
  fun i j => if j.val = 1 then lamEntry e1 A1 i.val else C (B i j)

/-- `eval a` of the λ-determinant equals the real determinant. -/
lemma lamMat_det_eval {n e0 : ℕ} (A0 : Polynomial ℝ) {e1 : ℕ} (A1 : Polynomial ℝ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (a b : ℝ) :
    (lamMatReal n e0 A0 e1 A1 B b).det.eval a = (modMatReal n e0 A0 e1 A1 B a b).det := by
  have hM : (Polynomial.evalRingHom a).mapMatrix (lamMatReal n e0 A0 e1 A1 B b) =
      modMatReal n e0 A0 e1 A1 B a b := by
    ext i j
    by_cases hj0 : j.val = 0
    · simp [lamMatReal, modMatReal, hj0, lamEntry_eval]
    · have hj0n : j.val ≠ 0 := hj0
      by_cases hj1 : j.val = 1
      · simp [lamMatReal, modMatReal, hj0, hj1]
      · simp [lamMatReal, modMatReal, hj0, hj1]
  calc
    (lamMatReal n e0 A0 e1 A1 B b).det.eval a
        = (Polynomial.evalRingHom a) ((lamMatReal n e0 A0 e1 A1 B b).det) := rfl
    _ = ((Polynomial.evalRingHom a).mapMatrix (lamMatReal n e0 A0 e1 A1 B b)).det := by
        rw [RingHom.map_det]
    _ = (modMatReal n e0 A0 e1 A1 B a b).det := by rw [hM]


/-- natDegree bound for the λ-determinant. -/
lemma lamMat_det_natDegree_le {n e0 : ℕ} (A0 : Polynomial ℝ) {e1 : ℕ} (A1 : Polynomial ℝ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : ℝ) :
    (lamMatReal n e0 A0 e1 A1 B b).det.natDegree ≤ e0 := by
  let D : Fin (n + 1) → ℕ := fun j => if j.val = 0 then e0 else 0
  have hD : ∀ (i j : Fin (n + 1)), ((lamMatReal n e0 A0 e1 A1 B b) i j).natDegree ≤ D j := by
    intro i j
    by_cases hj0 : j.val = 0
    · have h1 : (lamEntry e0 A0 i.val).natDegree ≤ e0 := natDegree_lamEntry_le e0 A0 i.val
      have hDj : D j = e0 := by
        dsimp [D]
        rw [hj0]
        simp
      rw [hDj]
      simp only [lamMatReal, hj0]
      exact h1
    · by_cases hj1 : j.val = 1
      · have h1 : (C (((X - C b) ^ e1 * A1).coeff i.val)).natDegree ≤ 0 := by simp
        have hDj : D j = 0 := by
          dsimp [D]
          simp [hj0, hj1]
        rw [hDj]
        simp only [lamMatReal, hj0, hj1]
        exact h1
      · have h1 : (C (B i j)).natDegree ≤ 0 := by simp
        have hDj : D j = 0 := by
          dsimp [D]
          simp [hj0, hj1]
        rw [hDj]
        simp only [lamMatReal, hj0, hj1]
        exact h1
  have hsum : (∑ j : Fin (n + 1), D j) = e0 := by
    let j0 : Fin (n + 1) := ⟨0, by omega⟩
    have hDj0 : D j0 = e0 := by
      simp [D, j0]
    have hDne : ∀ j : Fin (n + 1), j ≠ j0 → D j = 0 := by
      intro j hj
      have hz : j.val ≠ 0 := by
        intro hjv
        apply hj
        apply Fin.ext
        simpa [j0] using hjv
      dsimp [D]
      simp [hz]
    rw [Finset.sum_eq_single j0]
    · exact hDj0
    · intro b hb hbne
      exact hDne b hbne
    · intro hj0not
      exact False.elim (hj0not (Finset.mem_univ j0))
  exact le_trans (Commons.LinearAlgebra.Matrix.det_natDegree_le (lamMatReal n e0 A0 e1 A1 B b) D hD) (by rw [hsum])

/-- natDegree bound for the μ-determinant (topCoeffPoly). -/
lemma muMat_det_natDegree_le {n : ℕ} (hn : 1 ≤ n) {e1 : ℕ} (A1 : Polynomial ℝ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (muMat n e1 A1 B).det.natDegree ≤ e1 := by
  let D : Fin (n + 1) → ℕ := fun j => if j.val = 1 then e1 else 0
  have hD : ∀ (i j : Fin (n + 1)), ((muMat n e1 A1 B) i j).natDegree ≤ D j := by
    intro i j
    by_cases hj1 : j.val = 1
    · have h1 : (lamEntry e1 A1 i.val).natDegree ≤ e1 := natDegree_lamEntry_le e1 A1 i.val
      have hDj : D j = e1 := by
        dsimp [D]
        rw [hj1]
        simp
      rw [hDj]
      simp only [muMat, hj1]
      exact h1
    · have h1 : (C (B i j)).natDegree ≤ 0 := by simp
      have hDj : D j = 0 := by
        dsimp [D]
        simp [hj1]
      rw [hDj]
      simp only [muMat, hj1]
      exact h1
  have hsum : (∑ j : Fin (n + 1), D j) = e1 := by
    let j1 : Fin (n + 1) := ⟨1, by omega⟩
    have hDj1 : D j1 = e1 := by
      simp [D, j1]
    have hDne : ∀ j : Fin (n + 1), j ≠ j1 → D j = 0 := by
      intro j hj
      have hz : j.val ≠ 1 := by
        intro hjv
        apply hj
        apply Fin.ext
        simpa [j1] using hjv
      dsimp [D]
      simp [hz]
    rw [Finset.sum_eq_single j1]
    · exact hDj1
    · intro b hb hbne
      exact hDne b hbne
    · intro hj1not
      exact False.elim (hj1not (Finset.mem_univ j1))
  exact le_trans (Commons.LinearAlgebra.Matrix.det_natDegree_le (muMat n e1 A1 B) D hD) (by rw [hsum])

/-- Evaluating `C x` by a ring hom gives `x`. -/
lemma evalRingHom_C (b : ℝ) (x : ℝ) : (Polynomial.evalRingHom b) (C x) = x := by simp

/-- Top coefficient of the λ-determinant equals the μ-determinant evaluated at `b`
(up to the sign `(-1)^e0`).  Here `B` has `A0`'s coefficient vector in column 0. -/
lemma lamMat_det_coeff_e0 {n e0 : ℕ} (A0 : Polynomial ℝ) {e1 : ℕ} (A1 : Polynomial ℝ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : ℝ)
    (hB0 : ∀ i : Fin (n + 1), B i ⟨0, by omega⟩ = A0.coeff i.val) :
    ((lamMatReal n e0 A0 e1 A1 B b).det).coeff e0 =
      (-1 : ℝ) ^ e0 * ((muMat n e1 A1 B).det.eval b) := by
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial ℝ) := lamMatReal n e0 A0 e1 A1 B b
  let j0 : Fin (n + 1) := ⟨0, by omega⟩
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => if j = j0 then (-1 : ℝ) ^ e0 * A0.coeff i.val
               else (if j.val = 1 then ((X - C b) ^ e1 * A1).coeff i.val else B i j)
  have hN : ∀ (i j : Fin (n + 1)),
      N i j = (M i j).coeff (if j = j0 then e0 else 0) := by
    intro i j
    by_cases hj : j = j0
    · subst j
      have hMij : M i j0 = lamEntry e0 A0 i.val := by simp [M, lamMatReal, j0]
      calc
        N i j0 = (-1 : ℝ) ^ e0 * A0.coeff i.val := by simp [N, j0]
        _ = (lamEntry e0 A0 i.val).coeff e0 := (coeff_e_lamEntry e0 A0 i.val).symm
        _ = (M i j0).coeff (if j0 = j0 then e0 else 0) := by
              rw [hMij]
              simp
    · have hj0 : j.val ≠ 0 := by
        intro hz
        apply hj
        apply Fin.ext
        simpa [j0] using hz
      by_cases hj1 : j.val = 1
      · have hMij : M i j = C (((X - C b) ^ e1 * A1).coeff i.val) := by
          simp [M, lamMatReal, hj0, hj1]
        rw [hMij]
        simp [N, hj, hj1]
      · have hMij : M i j = C (B i j) := by
          simp [M, lamMatReal, hj0, hj1]
        rw [hMij]
        simp [N, hj, hj1]
  have hconst : ∀ (i j : Fin (n + 1)), j ≠ j0 → (M i j).natDegree = 0 := by
    intro i j hj
    have hj0 : j.val ≠ 0 := by
      intro hz
      apply hj
      apply Fin.ext
      simpa [j0] using hz
    dsimp [M, lamMatReal]
    by_cases hj1 : j.val = 1
    · rw [if_neg hj0, if_pos hj1]
      simp
    · rw [if_neg hj0, if_neg hj1]
      simp
  have hcoeff : (M.det).coeff e0 = N.det :=
    Commons.LinearAlgebra.Matrix.coeff_det_const_cols M N j0 e0 hN hconst
  let T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    (Polynomial.evalRingHom b).mapMatrix (muMat n e1 A1 B)
  have hN_eq : N = T.updateCol j0 (fun i => (-1 : ℝ) ^ e0 • (T i j0)) := by
    ext i j
    by_cases hj : j = j0
    · subst j
      have hTj0 : T i j0 = B i j0 := by simp [T, muMat, j0]
      calc
        N i j0 = (-1 : ℝ) ^ e0 * A0.coeff i.val := by simp [N, j0]
        _ = (-1 : ℝ) ^ e0 * (B i j0) := by rw [hB0 i]
        _ = (-1 : ℝ) ^ e0 * (T i j0) := by rw [hTj0]
        _ = (-1 : ℝ) ^ e0 • (T i j0) := by simp
        _ = (T.updateCol j0 (fun i => (-1 : ℝ) ^ e0 • (T i j0))) i j0 := by simp
    · have hj0 : j.val ≠ 0 := by
        intro hz
        apply hj
        apply Fin.ext
        simpa [j0] using hz
      by_cases hj1 : j.val = 1
      · have hTj : T i j = ((X - C b) ^ e1 * A1).coeff i.val := by
          simp [T, muMat, hj1, lamEntry_eval]
        calc
          N i j = ((X - C b) ^ e1 * A1).coeff i.val := by simp [N, hj, hj1]
          _ = T i j := by rw [hTj]
          _ = (T.updateCol j0 (fun i => (-1 : ℝ) ^ e0 • (T i j0))) i j := by simp [hj]
      · have hTj : T i j = B i j := by simp [T, muMat, hj1]
        calc
          N i j = B i j := by simp [N, hj, hj1]
          _ = T i j := by rw [hTj]
          _ = (T.updateCol j0 (fun i => (-1 : ℝ) ^ e0 • (T i j0))) i j := by simp [hj]
  have hself : T.updateCol j0 (fun i => T i j0) = T := by
    ext i j
    by_cases hj : j = j0
    · subst j
      simp
    · simp [hj]
  have hdetN : N.det = (-1 : ℝ) ^ e0 * T.det := by
    calc
      N.det = (T.updateCol j0 (fun i => (-1 : ℝ) ^ e0 • (T i j0))).det := by rw [hN_eq]
      _ = (-1 : ℝ) ^ e0 * (T.updateCol j0 (fun i => T i j0)).det := by
            change (T.updateCol j0 ((-1 : ℝ) ^ e0 • (fun i : Fin (n + 1) => T i j0))).det =
              (-1 : ℝ) ^ e0 * (T.updateCol j0 (fun i : Fin (n + 1) => T i j0)).det
            rw [Matrix.det_updateCol_smul (M := T) (j := j0) (s := (-1 : ℝ) ^ e0)
              (u := fun i : Fin (n + 1) => T i j0)]
      _ = (-1 : ℝ) ^ e0 * T.det := by rw [hself]
  have hTdet : T.det = (muMat n e1 A1 B).det.eval b := by
    dsimp [T]
    rw [← RingHom.map_det (f := Polynomial.evalRingHom b) (M := muMat n e1 A1 B)]
    simp [Polynomial.coe_evalRingHom]
  calc
    ((lamMatReal n e0 A0 e1 A1 B b).det).coeff e0
        = N.det := by simpa [M] using hcoeff
    _ = (-1 : ℝ) ^ e0 * T.det := hdetN
    _ = (-1 : ℝ) ^ e0 * ((muMat n e1 A1 B).det.eval b) := by rw [hTdet]

/-- The top-μ coefficient of the μ-determinant. -/
lemma muMat_det_coeff_e1 {n : ℕ} (hn : 1 ≤ n) {e1 : ℕ} (A1 : Polynomial ℝ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hB1 : ∀ i : Fin (n + 1), B i ⟨1, by omega⟩ = A1.coeff i.val) :
    (muMat n e1 A1 B).det.coeff e1 = (-1 : ℝ) ^ e1 * B.det := by
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial ℝ) := muMat n e1 A1 B
  let j1 : Fin (n + 1) := ⟨1, by omega⟩
  let N0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => if j = j1 then (-1 : ℝ) ^ e1 * A1.coeff i.val else B i j
  have hN0 : ∀ (i j : Fin (n + 1)),
      N0 i j = (M i j).coeff (if j = j1 then e1 else 0) := by
    intro i j
    by_cases hj : j = j1
    · subst j
      have hMij : M i j1 = lamEntry e1 A1 i.val := by simp [M, muMat, j1]
      calc
        N0 i j1 = (-1 : ℝ) ^ e1 * A1.coeff i.val := by simp [N0, j1]
        _ = (lamEntry e1 A1 i.val).coeff e1 := (coeff_e_lamEntry e1 A1 i.val).symm
        _ = (M i j1).coeff (if j1 = j1 then e1 else 0) := by
              rw [hMij]
              simp
    · have hj1n : j.val ≠ 1 := by
        intro hz
        apply hj
        apply Fin.ext
        simpa [j1] using hz
      have hMij : M i j = C (B i j) := by simp [M, muMat, hj1n]
      rw [hMij]
      simp [N0, hj, hj1n]
  have hconst : ∀ (i j : Fin (n + 1)), j ≠ j1 → (M i j).natDegree = 0 := by
    intro i j hj
    have hj1n : j.val ≠ 1 := by
      intro hz
      apply hj
      apply Fin.ext
      simpa [j1] using hz
    dsimp [M, muMat]
    rw [if_neg hj1n]
    simp
  have hcoeff : (M.det).coeff e1 = N0.det :=
    Commons.LinearAlgebra.Matrix.coeff_det_const_cols M N0 j1 e1 hN0 hconst
  have hN0B : N0 = B.updateCol j1 (fun i => (-1 : ℝ) ^ e1 • (B i j1)) := by
    ext i j
    by_cases hj : j = j1
    · subst j
      simp [N0, j1, hB1 i]
    · simp [N0, hj]
  have hdetN0 : N0.det = (-1 : ℝ) ^ e1 * B.det := by
    calc
      N0.det = (B.updateCol j1 (fun i => (-1 : ℝ) ^ e1 • (B i j1))).det := by rw [hN0B]
      _ = (-1 : ℝ) ^ e1 * (B.updateCol j1 (fun i => B i j1)).det := by
            change (B.updateCol j1 ((-1 : ℝ) ^ e1 • (fun i : Fin (n + 1) => B i j1))).det =
              (-1 : ℝ) ^ e1 * (B.updateCol j1 (fun i : Fin (n + 1) => B i j1)).det
            rw [Matrix.det_updateCol_smul (M := B) (j := j1) (s := (-1 : ℝ) ^ e1)
              (u := fun i : Fin (n + 1) => B i j1)]
      _ = (-1 : ℝ) ^ e1 * B.det := by
            have hself : B.updateCol j1 (fun i => B i j1) = B := by
              ext i j
              by_cases hj : j = j1
              · subst j; simp
              · simp [hj]
            rw [hself]
  calc
    (muMat n e1 A1 B).det.coeff e1 = N0.det := by simpa [M] using hcoeff
    _ = (-1 : ℝ) ^ e1 * B.det := hdetN0

/-- The μ-determinant is nonzero when the base matrix has nonzero determinant. -/
lemma muMat_det_ne_zero {n : ℕ} (hn : 1 ≤ n) {e1 : ℕ} (A1 : Polynomial ℝ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hB1 : ∀ i : Fin (n + 1), B i ⟨1, by omega⟩ = A1.coeff i.val)
    (hdetB : B.det ≠ 0) :
    (muMat n e1 A1 B).det ≠ 0 := by
  have hc := muMat_det_coeff_e1 (e1 := e1) hn A1 B hB1
  intro hz
  have hz0 : ((muMat n e1 A1 B).det).coeff e1 = 0 := by
    rw [hz]
    simp
  have : (-1 : ℝ) ^ e1 * B.det = 0 := by
    rwa [hc] at hz0
  exact hdetB (mul_eq_zero.mp this |>.resolve_left (pow_ne_zero e1 (by norm_num : (-1 : ℝ) ≠ 0)))


/-! ## 4. Main theorem -/

/-- Multiplying a real polynomial by `(X - C lam)^e` increases natDegree by at most `e`. -/
lemma natDegree_mul_X_sub_C_pow_le (e : ℕ) (P : Polynomial ℝ) (lam : ℝ) :
    ((X - C lam) ^ e * P).natDegree ≤ e + P.natDegree := by
  calc
    ((X - C lam) ^ e * P).natDegree ≤ ((X - C lam) ^ e).natDegree + P.natDegree :=
      Polynomial.natDegree_mul_le
    _ = e + P.natDegree := by
      have h1 : ((X - C lam) ^ e).natDegree = e * (X - C lam).natDegree :=
        Polynomial.natDegree_pow (X - C lam) e
      have h2 : (X - C lam).natDegree = 1 := Polynomial.natDegree_X_sub_C lam
      rw [h1, h2, mul_one]

theorem lift_shift_pair_independent_real (n k : ℕ) (hn : 1 ≤ n) (hk2 : 2 ≤ k)
    (hkn : k ≤ n + 1) :
    ∃ L : ℕ,
    ∀ (A : Fin k → Polynomial ℝ),
      (∀ i : Fin k, (A i).natDegree ≤ n) →
      (∀ i : Fin k, A i ≠ 0) →
      LinearIndependent ℝ A →
      IsCoprime (A ⟨0, by omega⟩) (A ⟨1, by omega⟩) →
      ∃ (lam0 lam1 : ℤ),
        |(lam0 : ℝ)| ≤ L ∧ |(lam1 : ℝ)| ≤ L ∧ lam0 ≠ lam1 ∧
        (A ⟨1, by omega⟩).eval (lam0 : ℝ) ≠ 0 ∧
        (A ⟨0, by omega⟩).eval (lam1 : ℝ) ≠ 0 ∧
        LinearIndependent ℝ
          (fun j : Fin k =>
            if j.val = 0 then
              (Polynomial.X - Polynomial.C (lam0 : ℝ)) ^ (n - (A ⟨0, by omega⟩).natDegree) *
                A ⟨0, by omega⟩
            else if j.val = 1 then
              (Polynomial.X - Polynomial.C (lam1 : ℝ)) ^ (n - (A ⟨1, by omega⟩).natDegree) *
                A ⟨1, by omega⟩
            else A j) := by
  let L : ℕ := n + 1
  refine ⟨L, ?_⟩
  intro A hdegA hAne0 hlinA hcop
  let A0 : Polynomial ℝ := A ⟨0, by omega⟩
  let A1 : Polynomial ℝ := A ⟨1, by omega⟩
  let e0 : ℕ := n - A0.natDegree
  let e1 : ℕ := n - A1.natDegree
  have hd0 : A0.natDegree ≤ n := by simpa [A0] using hdegA ⟨0, by omega⟩
  have hd1 : A1.natDegree ≤ n := by simpa [A1] using hdegA ⟨1, by omega⟩
  have h00 : A0 ≠ 0 := by simpa [A0] using hAne0 ⟨0, by omega⟩
  have h01 : A1 ≠ 0 := by simpa [A1] using hAne0 ⟨1, by omega⟩
  have he0n : e0 ≤ n := by dsimp [e0]; omega
  have he1n : e1 ≤ n := by dsimp [e1]; omega
  -- extend the coefficient vectors to a square basis
  have hw : LinearIndependent ℝ (fun j : Fin k => coeffV n (A j)) :=
    linearIndependent_coeffV_of_poly A hdegA hlinA
  obtain ⟨E, hElin, hEw⟩ := Commons.LinearAlgebra.Basis.exists_linearIndependent_extend n k hkn hw
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j => E j i
  have hBcol : LinearIndependent ℝ B.col := by
    change LinearIndependent ℝ (fun j : Fin (n + 1) => fun i : Fin (n + 1) => E j i)
    simpa [B] using hElin
  have hBu : IsUnit B := (Matrix.linearIndependent_cols_iff_isUnit (A := B)).mp hBcol
  have hdetB : B.det ≠ 0 := by
    exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det B).mp hBu))
  have hB0 : ∀ i : Fin (n + 1), B i ⟨0, by omega⟩ = A0.coeff i.val := by
    intro i
    have h1 := congrFun (hEw ⟨0, by omega⟩) i
    -- h1 : E ((Fin.castLE hkn) ⟨0,_⟩) i = (A ⟨0,_⟩).coeff i.val
    have hidx : (Fin.castLE hkn ⟨0, by omega⟩ : Fin (n + 1)) = ⟨0, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hidx] at h1
    change E ⟨0, by omega⟩ i = A0.coeff i.val
    simpa [A0, B, coeffV] using h1
  have hB1 : ∀ i : Fin (n + 1), B i ⟨1, by omega⟩ = A1.coeff i.val := by
    intro i
    have h1 := congrFun (hEw ⟨1, by omega⟩) i
    have hidx : (Fin.castLE hkn ⟨1, by omega⟩ : Fin (n + 1)) = ⟨1, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hidx] at h1
    change E ⟨1, by omega⟩ i = A1.coeff i.val
    simpa [A1, B, coeffV] using h1
  -- the μ-determinant (witness for bad λ1 values)
  let topC : Polynomial ℝ := (muMat n e1 A1 B).det
  have htop0 : topC ≠ 0 := muMat_det_ne_zero hn A1 B hB1 hdetB
  have htopdeg : topC.natDegree ≤ e1 := muMat_det_natDegree_le hn A1 B
  -- stage 1: choose λ1
  let ps1 : Fin 2 → Polynomial ℝ := ![A0, topC]
  have hps1 : ∀ i : Fin 2, ps1 i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [ps1] using h00
    · simpa [ps1] using htop0
  have hc1 : (∑ i : Fin 2, (ps1 i).natDegree) < 2 * L + 1 := by
    rw [Fin.sum_univ_two]
    dsimp [L]
    simp [ps1]
    have hsum : A0.natDegree + topC.natDegree ≤ n + e1 := Nat.add_le_add hd0 htopdeg
    exact le_trans hsum (by omega)
  obtain ⟨z1, hz1b, hz1e⟩ := Commons.Data.Int.exists_int_avoid_roots (m := 2) ps1 hps1 L hc1
  have hA0e1 : A0.eval (z1 : ℝ) ≠ 0 := by
    simpa [ps1] using hz1e (0 : Fin 2)
  have htopCe : topC.eval (z1 : ℝ) ≠ 0 := by
    simpa [ps1] using hz1e (1 : Fin 2)
  -- the λ-determinant at this λ1 (witness for bad λ0 values)
  let polyb : Polynomial ℝ := (lamMatReal n e0 A0 e1 A1 B (z1 : ℝ)).det
  have hpolyb0 : polyb ≠ 0 := by
    intro hp
    have hc0 : polyb.coeff e0 = 0 := by rw [hp]; simp
    have hlink := lamMat_det_coeff_e0 (e0 := e0) A0 (e1 := e1) A1 B (z1 : ℝ) hB0
    have hX : (lamMatReal n e0 A0 e1 A1 B (z1 : ℝ)).det.coeff e0 = 0 := by
      simpa [polyb] using hc0
    have hprod0 : (-1 : ℝ) ^ e0 * (muMat n e1 A1 B).det.eval (z1 : ℝ) = 0 :=
      hlink.symm.trans hX
    exact htopCe ((mul_eq_zero.mp hprod0).resolve_left (pow_ne_zero e0 (by norm_num)))
  have hpolybdeg : polyb.natDegree ≤ e0 := by
    simpa [polyb] using (lamMat_det_natDegree_le A0 (A1 := A1) B (z1 : ℝ))
  -- stage 2 : choose λ0
  let ps2 : Fin 3 → Polynomial ℝ := ![A1, polyb, X - C (z1 : ℝ)]
  have hXz1 : (X - C (z1 : ℝ) : Polynomial ℝ) ≠ 0 := Polynomial.X_sub_C_ne_zero (z1 : ℝ)
  have hps2 : ∀ i : Fin 3, ps2 i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [ps2] using h01
    · simpa [ps2] using hpolyb0
    · simpa [ps2] using hXz1
  have hc2 : (∑ i : Fin 3, (ps2 i).natDegree) < 2 * L + 1 := by
    rw [Fin.sum_univ_three]
    dsimp [L]
    simp [ps2]
    have h3 : (X - C (z1 : ℝ) : Polynomial ℝ).natDegree ≤ 1 := by
      rw [Polynomial.natDegree_X_sub_C]
    have hsum : A1.natDegree + polyb.natDegree + (X - C (z1 : ℝ) : Polynomial ℝ).natDegree
        ≤ n + e0 + 1 := by
      exact Nat.add_le_add (Nat.add_le_add hd1 hpolybdeg) h3
    exact le_trans hsum (by omega)
  obtain ⟨z0, hz0b, hz0e⟩ := Commons.Data.Int.exists_int_avoid_roots (m := 3) ps2 hps2 L hc2
  have hA1e0 : A1.eval (z0 : ℝ) ≠ 0 := by
    simpa [ps2] using hz0e (0 : Fin 3)
  have hpolye0 : polyb.eval (z0 : ℝ) ≠ 0 := by
    simpa [ps2] using hz0e (1 : Fin 3)
  have hne01 : z0 ≠ z1 := by
    intro h
    have hz := hz0e (2 : Fin 3)
    have : (ps2 (2 : Fin 3)).eval (z0 : ℝ) ≠ 0 := hz
    simpa [ps2, h] using this
  -- real determinant nonzero at (z0, z1)
  have hdet : (modMatReal n e0 A0 e1 A1 B (z0 : ℝ) (z1 : ℝ)).det ≠ 0 := by
    have hp : (lamMatReal n e0 A0 e1 A1 B (z1 : ℝ)).det.eval (z0 : ℝ) ≠ 0 := by
      simpa [polyb] using hpolye0
    intro hz
    have hev := lamMat_det_eval (e0 := e0) A0 (e1 := e1) A1 B (z0 : ℝ) (z1 : ℝ)
    rw [← hev] at hz
    exact hp hz
  -- linear independence of the columns of the modified matrix
  have hLIcol : LinearIndependent ℝ (fun j' : Fin (n + 1) => fun i : Fin (n + 1) =>
      (modMatReal n e0 A0 e1 A1 B (z0 : ℝ) (z1 : ℝ)) i j') := by
    have hLIc : LinearIndependent ℝ (modMatReal n e0 A0 e1 A1 B (z0 : ℝ) (z1 : ℝ)).col := by
      exact (Matrix.linearIndependent_cols_iff_isUnit
        (A := (modMatReal n e0 A0 e1 A1 B (z0 : ℝ) (z1 : ℝ)))).mpr
        ((Matrix.isUnit_iff_isUnit_det (modMatReal n e0 A0 e1 A1 B (z0 : ℝ) (z1 : ℝ))).mpr
          (isUnit_iff_ne_zero.mpr hdet))
    convert hLIc using 1
    funext j' i
    rfl
  -- restriction to the first k columns
  let fam : Fin k → (Fin (n + 1) → ℝ) := fun j => fun i =>
    (modMatReal n e0 A0 e1 A1 B (z0 : ℝ) (z1 : ℝ)) i ((Fin.castLE hkn) j)
  have hLIk : LinearIndependent ℝ fam := by
    change LinearIndependent ℝ (fun j : Fin k =>
      (fun j' : Fin (n + 1) => fun i : Fin (n + 1) =>
        (modMatReal n e0 A0 e1 A1 B (z0 : ℝ) (z1 : ℝ)) i j') ((Fin.castLE hkn) j))
    exact hLIcol.comp (Fin.castLE hkn) (Fin.castLE_injective hkn)
  -- identify the first k columns with coefficient vectors of the modified family
  let modj : Fin k → Polynomial ℝ := fun j =>
    if j.val = 0 then (X - C (z0 : ℝ)) ^ e0 * A0
    else if j.val = 1 then (X - C (z1 : ℝ)) ^ e1 * A1
    else A j
  have hcol_eq : ∀ j : Fin k, coeffV n (modj j) = fam j := by
    intro j
    by_cases hj0 : j.val = 0
    · have hj0' : ((Fin.castLE hkn) j).val = 0 := by
        simpa [hj0]
      ext i
      simp [fam, modj, hj0, hj0', modMatReal, coeffV]
    · by_cases hj1 : j.val = 1
      · have hj1' : ((Fin.castLE hkn) j).val = 1 := by
          simpa [hj1]
        ext i
        simp [fam, modj, hj0, hj1, hj1', modMatReal, coeffV]
      · have hj0n : ((Fin.castLE hkn) j).val ≠ 0 := by
          intro hz
          apply hj0
          simpa using hz
        have hj1n : ((Fin.castLE hkn) j).val ≠ 1 := by
          intro hz
          apply hj1
          simpa using hz
        ext i
        have hE := hEw j
        simp [fam, modj, hj0, hj1, hj0n, hj1n, modMatReal, B, coeffV, hE]
  have hLIvec : LinearIndependent ℝ (fun j : Fin k => coeffV n (modj j)) := by
    convert hLIk using 1
    funext j
    exact hcol_eq j
  have hdegmodj : ∀ j : Fin k, (modj j).natDegree ≤ n := by
    intro j
    by_cases hj0 : j.val = 0
    · have hb : ((X - C (z0 : ℝ)) ^ e0 * A0).natDegree ≤ n := by
        have h1 := natDegree_mul_X_sub_C_pow_le e0 A0 (z0 : ℝ)
        have h2 : e0 + A0.natDegree ≤ n := by
          dsimp [e0]
          rw [Nat.sub_add_cancel hd0]
        omega
      simpa [modj, hj0] using hb
    · by_cases hj1 : j.val = 1
      · have hb : ((X - C (z1 : ℝ)) ^ e1 * A1).natDegree ≤ n := by
          have h1 := natDegree_mul_X_sub_C_pow_le e1 A1 (z1 : ℝ)
          have h2 : e1 + A1.natDegree ≤ n := by
            dsimp [e1]
            rw [Nat.sub_add_cancel hd1]
          omega
        simpa [modj, hj0, hj1] using hb
      · simpa [modj, hj0, hj1] using hdegA j
  have hLImodj : LinearIndependent ℝ modj := linearIndependent_poly_of_coeffV modj hdegmodj hLIvec
  refine ⟨z0, z1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [L] using hz0b
  · simpa [L] using hz1b
  · exact_mod_cast hne01
  · simpa [A1] using hA1e0
  · simpa [A0] using hA0e1
  · simpa [modj] using hLImodj

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree