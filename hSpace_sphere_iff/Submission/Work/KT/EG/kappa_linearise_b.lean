import Mathlib
import Submission.Work.KT.EG.kappa_linearise_defs

/-!
# `Work.KT.EG.kappa_linearise_b` — the algebra of the block companion matrix

Contents:

* `shMat_pow` — the powers of the "next block" shift;
* `one_sub_smul_mul_sum` — the geometric series identity for a nilpotent matrix;
* `Rmat_apply` and its consequences (`Rmat_last`, `lastMat_mul_Rmat`);
* `poly_eval_sum` — evaluating a polynomial through a ring homomorphism;
* `Amat_mul_Rmat`, `Lmat_mul_Amat_Rmat` — the column and row operations.
-/

namespace Work.KT.EG

open Matrix

noncomputable section

/-! ## 1. The shift matrix and its powers -/

lemma shMat_nx (R : Type) [Zero R] [One R] (N m : ℕ) {x : BIdx N m} (h : BIdx.st x < N) :
    shMat R N m x (BIdx.nx x) = 1 := by
  show (if BIdx.st x < N then (if BIdx.nx x = BIdx.nx x then (1 : R) else 0) else 0) = 1
  rw [if_pos h, if_pos rfl]

lemma shMat_eq_zero (R : Type) [Zero R] [One R] (N m : ℕ) {x y : BIdx N m}
    (h : y ≠ BIdx.nx x) : shMat R N m x y = 0 := by
  show (if BIdx.st x < N then (if y = BIdx.nx x then (1 : R) else 0) else 0) = 0
  by_cases hx : BIdx.st x < N
  · rw [if_pos hx, if_neg h]
  · rw [if_neg hx]

lemma shMat_apply_of_not (R : Type) [Zero R] [One R] (N m : ℕ) {x : BIdx N m}
    (h : ¬ BIdx.st x < N) (y : BIdx N m) : shMat R N m x y = 0 := by
  show (if BIdx.st x < N then (if y = BIdx.nx x then (1 : R) else 0) else 0) = 0
  rw [if_neg h]

lemma BIdx.nx_iterate_succ {N m : ℕ} (k : ℕ) (x : BIdx N m) :
    BIdx.nx^[k] (BIdx.nx x) = BIdx.nx^[k+1] x :=
  (Function.iterate_succ_apply BIdx.nx k x).symm

theorem shMat_pow (R : Type) [Semiring R] (N m k : ℕ) (x y : BIdx N m) :
    (shMat R N m ^ k) x y
      = if BIdx.st x + k ≤ N then (if y = BIdx.nx^[k] x then (1 : R) else 0) else 0 := by
  induction k generalizing x with
  | zero =>
    rw [pow_zero, Matrix.one_apply, Function.iterate_zero]
    simp only [id_eq, Nat.add_zero]
    rw [if_pos (BIdx.st_le x)]
    by_cases h : y = x
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun hh => h hh.symm), if_neg h]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    by_cases hx : BIdx.st x < N
    · have hz : ∀ z : BIdx N m, shMat R N m x z * (shMat R N m ^ k) z y
          = if z = BIdx.nx x then (shMat R N m ^ k) z y else 0 := by
        intro z
        by_cases h : z = BIdx.nx x
        · rw [h, if_pos rfl, shMat_nx R N m hx, one_mul]
        · rw [shMat_eq_zero R N m h, zero_mul, if_neg h]
      rw [Finset.sum_congr rfl (fun z _ => hz z),
        Finset.sum_ite_eq' Finset.univ (BIdx.nx x) (fun z => (shMat R N m ^ k) z y)]
      simp only [Finset.mem_univ, if_true]
      rw [ih (BIdx.nx x), BIdx.st_nx hx, BIdx.nx_iterate_succ]
      by_cases h1 : BIdx.st x + 1 + k ≤ N
      · have h2 : BIdx.st x + (k + 1) ≤ N := by omega
        rw [if_pos h1, if_pos h2]
      · have h2 : ¬ (BIdx.st x + (k + 1) ≤ N) := by omega
        rw [if_neg h1, if_neg h2]
    · have hz : ∀ z : BIdx N m, shMat R N m x z * (shMat R N m ^ k) z y = 0 := by
        intro z; rw [shMat_apply_of_not R N m hx z, zero_mul]
      rw [Finset.sum_congr rfl (fun z _ => hz z)]
      have h2 : ¬ (BIdx.st x + (k + 1) ≤ N) := by have := BIdx.st_le x; omega
      simp [h2]

/-- The shift is nilpotent of index `N+1`. -/
lemma shMat_pow_succ_eq_zero (R : Type) [Semiring R] (N m : ℕ) :
    (shMat R N m) ^ (N + 1) = 0 := by
  ext x y
  rw [shMat_pow]
  have h : ¬ (BIdx.st x + (N + 1) ≤ N) := by have := BIdx.st_le x; omega
  rw [if_neg h]
  rfl

/-! ## 2. The geometric series identity -/

theorem one_sub_smul_mul_sum {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [CommRing A]
    (S : Matrix ι ι A) (x : A) (N : ℕ) (hS : S ^ (N + 1) = 0) :
    (1 - x • S) * (∑ k ∈ Finset.range (N + 1), x ^ k • S ^ k) = 1 ∧
    (∑ k ∈ Finset.range (N + 1), x ^ k • S ^ k) * (1 - x • S) = 1 := by
  have hmul : ∀ k : ℕ, (x • S) * (x ^ k • S ^ k) = x ^ (k + 1) • S ^ (k + 1) := by
    intro k
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ' x k, ← pow_succ' S k]
  have hmul' : ∀ k : ℕ, (x ^ k • S ^ k) * (x • S) = x ^ (k + 1) • S ^ (k + 1) := by
    intro k
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← pow_succ' x k, ← pow_succ S k]
  have hP : (∑ k ∈ Finset.range (N + 1), x ^ k • S ^ k)
      = (∑ k ∈ Finset.range N, x ^ (k + 1) • S ^ (k + 1)) + 1 := by
    rw [Finset.sum_range_succ']
    simp
  have hxS : (x • S) * (∑ k ∈ Finset.range (N + 1), x ^ k • S ^ k)
      = ∑ k ∈ Finset.range N, x ^ (k + 1) • S ^ (k + 1) := by
    rw [Matrix.mul_sum]
    simp only [hmul]
    rw [Finset.sum_range_succ, hS, smul_zero, add_zero]
  have hSx : (∑ k ∈ Finset.range (N + 1), x ^ k • S ^ k) * (x • S)
      = ∑ k ∈ Finset.range N, x ^ (k + 1) • S ^ (k + 1) := by
    rw [Matrix.sum_mul]
    simp only [hmul']
    rw [Finset.sum_range_succ, hS, smul_zero, add_zero]
  constructor
  · rw [sub_mul, one_mul, hxS, hP]
    abel
  · rw [mul_sub, mul_one, hSx, hP]
    abel

/-! ## 3. The entries of `Rmat` -/

lemma shC_pow_apply (X : Type) [TopologicalSpace X] (N m k : ℕ) (x y : BIdx N m) :
    (shC X N m ^ k) x y
      = if BIdx.st x + k ≤ N then (if y = BIdx.nx^[k] x then (1 : C(X × Sph ℂ, ℂ)) else 0)
        else 0 :=
  shMat_pow _ N m k x y

theorem Rmat_apply (X : Type) [TopologicalSpace X] (N : ℕ) {m : ℕ} (x y : BIdx N m) :
    Rmat X N x y =
      (if BIdx.st x ≤ BIdx.st y then
        (if y = BIdx.nx^[BIdx.st y - BIdx.st x] x then
          (zc X) ^ (BIdx.st y - BIdx.st x) else 0)
      else 0) := by
  have hterm : ∀ k : ℕ, ((zc X) ^ k • (shC X N m) ^ k) x y
      = (zc X) ^ k * (if BIdx.st x + k ≤ N then
          (if y = BIdx.nx^[k] x then (1 : C(X × Sph ℂ, ℂ)) else 0) else 0) := by
    intro k
    rw [show ((zc X) ^ k • (shC X N m) ^ k) x y
        = (zc X) ^ k * (((shC X N m) ^ k) x y) from rfl]
    rw [shC_pow_apply]
  rw [Rmat, Matrix.sum_apply]
  simp only [hterm]
  rw [Finset.sum_eq_single (BIdx.st y - BIdx.st x)]
  · by_cases h : BIdx.st x ≤ BIdx.st y
    · have h2 : BIdx.st x + (BIdx.st y - BIdx.st x) ≤ N := by
        have := BIdx.st_le y; omega
      rw [if_pos h, if_pos h2]
      by_cases h3 : y = BIdx.nx^[BIdx.st y - BIdx.st x] x
      · rw [if_pos h3, if_pos h3, mul_one]
      · rw [if_neg h3, if_neg h3, mul_zero]
    · have hne : y ≠ x := by intro hh; rw [hh] at h; exact h le_rfl
      have h1 : BIdx.st y - BIdx.st x = 0 := by omega
      have h2 : BIdx.st x + 0 ≤ N := by have := BIdx.st_le x; omega
      rw [if_neg h, h1, pow_zero, one_mul, if_pos h2, Function.iterate_zero]
      simp only [id_eq]
      rw [if_neg hne]
  · intro k _ hne
    by_cases hc : BIdx.st x + k ≤ N
    · rw [if_pos hc]
      by_cases hy : y = BIdx.nx^[k] x
      · exfalso
        have hst : BIdx.st y = BIdx.st x + k := by rw [hy, BIdx.st_nx_iterate k hc]
        exact hne (by omega)
      · rw [if_neg hy, mul_zero]
    · rw [if_neg hc, mul_zero]
  · intro hk
    exfalso
    apply hk
    simp only [Finset.mem_range]
    have := BIdx.st_le y
    omega

lemma Rmat_last (X : Type) [TopologicalSpace X] (N : ℕ) {m : ℕ} (x : BIdx N m)
    (hx : BIdx.st x = N) (y : BIdx N m) :
    Rmat X N x y = if y = x then (1 : C(X × Sph ℂ, ℂ)) else 0 := by
  rw [Rmat_apply]
  by_cases hy : BIdx.st y = N
  · have h1 : BIdx.st x ≤ BIdx.st y := by omega
    rw [if_pos h1, show BIdx.st y - BIdx.st x = 0 from by omega, pow_zero,
      Function.iterate_zero]
    simp only [id_eq]
  · have hlt : ¬ (BIdx.st x ≤ BIdx.st y) := by have := BIdx.st_le y; omega
    rw [if_neg hlt]
    have hne : ¬ (y = x) := by intro hh; exact hy (by rw [hh]; exact hx)
    rw [if_neg hne]

/-! ## 4. `idMat`, `lastMat` and the inverse of `Rmat` -/

lemma shMat_apply_eq (R : Type) [Zero R] [One R] (N m : ℕ) (x y : BIdx N m) :
    shMat R N m x y = if BIdx.st x < N then (if y = BIdx.nx x then 1 else 0) else 0 := rfl

lemma idMat_apply_eq (R : Type) [Zero R] [One R] (N m : ℕ) (x y : BIdx N m) :
    idMat R N m x y = if BIdx.st x < N then (if y = x then 1 else 0) else 0 := rfl

lemma lastMat_apply_eq (R : Type) [Zero R] [One R] (N m : ℕ) (x y : BIdx N m) :
    lastMat R N m x y = if BIdx.st x = N then (if y = x then 1 else 0) else 0 := rfl

lemma idMat_add_lastMat (R : Type) [AddZeroClass R] [One R] (N m : ℕ) :
    idMat R N m + lastMat R N m = 1 := by
  funext x y
  have hle := BIdx.st_le (m := m) x
  rw [Matrix.add_apply, Matrix.one_apply, idMat_apply_eq, lastMat_apply_eq]
  by_cases hx : BIdx.st x < N
  · have hN : ¬ (BIdx.st x = N) := by omega
    rw [if_pos hx, if_neg hN, add_zero]
    by_cases h : x = y
    · simp [h]
    · have h' : ¬ y = x := fun hh => h hh.symm
      simp [h, h']
  · have hN : BIdx.st x = N := by omega
    rw [if_neg hx, if_pos hN, zero_add]
    by_cases h : x = y
    · simp [h]
    · have h' : ¬ y = x := fun hh => h hh.symm
      simp [h, h']

lemma idMat_eq_one_sub_lastMat (R : Type) [Ring R] (N m : ℕ) :
    idMat R N m = 1 - lastMat R N m :=
  (eq_sub_iff_add_eq).mpr (idMat_add_lastMat R N m)

lemma idC_add_lastC (X : Type) [TopologicalSpace X] (N m : ℕ) :
    idC X N m + lastC X N m = 1 :=
  idMat_add_lastMat C(X × Sph ℂ, ℂ) N m

lemma idC_eq_one_sub (X : Type) [TopologicalSpace X] (N m : ℕ) :
    idC X N m = 1 - lastC X N m :=
  idMat_eq_one_sub_lastMat C(X × Sph ℂ, ℂ) N m

lemma one_sub_zc_shC_mul_Rmat (X : Type) [TopologicalSpace X] (N m : ℕ) :
    (1 - zc X • shC X N m) * Rmat X N = 1 :=
  (one_sub_smul_mul_sum (shC X N m) (zc X) N (shMat_pow_succ_eq_zero _ N m)).1

lemma Rmat_mul_one_sub_zc_shC (X : Type) [TopologicalSpace X] (N m : ℕ) :
    Rmat X N * (1 - zc X • shC X N m) = 1 :=
  (one_sub_smul_mul_sum (shC X N m) (zc X) N (shMat_pow_succ_eq_zero _ N m)).2

lemma lastMat_mul_Rmat (X : Type) [TopologicalSpace X] (N m : ℕ) :
    lastMat C(X × Sph ℂ, ℂ) N m * Rmat X N = lastMat C(X × Sph ℂ, ℂ) N m := by
  funext x y
  rw [Matrix.mul_apply]
  by_cases hx : BIdx.st x = N
  · have hz : ∀ z : BIdx N m, lastMat C(X × Sph ℂ, ℂ) N m x z * Rmat X N z y
        = if z = x then Rmat X N z y else 0 := by
      intro z
      by_cases h : z = x
      · rw [h, lastMat_apply_eq, if_pos hx, if_pos rfl, one_mul, if_pos rfl]
      · rw [lastMat_apply_eq, if_pos hx, if_neg h, zero_mul, if_neg h]
    rw [Finset.sum_congr rfl (fun z _ => hz z),
      Finset.sum_ite_eq' Finset.univ x (fun z => Rmat X N z y)]
    simp only [Finset.mem_univ, if_true]
    rw [Rmat_last X N x hx y, lastMat_apply_eq, if_pos hx]
  · have h1 : lastMat C(X × Sph ℂ, ℂ) N m x y = 0 := by
      rw [lastMat_apply_eq, if_neg hx]
    rw [h1]
    refine Finset.sum_eq_zero (fun z _ => ?_)
    have h2 : lastMat C(X × Sph ℂ, ℂ) N m x z = 0 := by
      rw [lastMat_apply_eq, if_neg hx]
    rw [h2, zero_mul]

lemma lastC_mul_Rmat (X : Type) [TopologicalSpace X] (N m : ℕ) :
    lastC X N m * Rmat X N = lastC X N m :=
  lastMat_mul_Rmat X N m

lemma idMat_sub_zc_shC_mul_Rmat (X : Type) [TopologicalSpace X] (N m : ℕ) :
    (idMat C(X × Sph ℂ, ℂ) N m - zc X • shC X N m) * Rmat X N
      = idMat C(X × Sph ℂ, ℂ) N m := by
  have h2 : (1 - zc X • shC X N m) * Rmat X N = 1 := one_sub_zc_shC_mul_Rmat X N m
  have h3 : lastMat C(X × Sph ℂ, ℂ) N m * Rmat X N = lastMat C(X × Sph ℂ, ℂ) N m :=
    lastMat_mul_Rmat X N m
  have hid := idMat_eq_one_sub_lastMat (R := C(X × Sph ℂ, ℂ)) N m
  calc (idMat C(X × Sph ℂ, ℂ) N m - zc X • shC X N m) * Rmat X N
      = ((1 - lastMat C(X × Sph ℂ, ℂ) N m) - zc X • shC X N m) * Rmat X N := by rw [hid]
    _ = (1 - zc X • shC X N m) * Rmat X N - lastMat C(X × Sph ℂ, ℂ) N m * Rmat X N := by
        have hh : ((1 - lastMat C(X × Sph ℂ, ℂ) N m) - zc X • shC X N m)
            = (1 - zc X • shC X N m) - lastMat C(X × Sph ℂ, ℂ) N m := by abel
        rw [hh, sub_mul]
    _ = 1 - lastMat C(X × Sph ℂ, ℂ) N m := by rw [h2, h3]
    _ = idMat C(X × Sph ℂ, ℂ) N m := by rw [hid]

lemma idC_sub_zc_shC_mul_Rmat (X : Type) [TopologicalSpace X] (N m : ℕ) :
    (idC X N m - zc X • shC X N m) * Rmat X N = idC X N m :=
  idMat_sub_zc_shC_mul_Rmat X N m

/-! ## 5. Polynomials -/

theorem poly_eval_sum {A B : Type} [CommSemiring A] [CommSemiring B]
    (φ : Polynomial A →+* B) (ψ : A →+* B) (w : B)
    (hC : ∀ a, φ (Polynomial.C a) = ψ a) (hX : φ Polynomial.X = w)
    (p : Polynomial A) (N : ℕ) (hN : p.natDegree ≤ N) :
    φ p = ∑ k ∈ Finset.range (N + 1), ψ (p.coeff k) * w ^ k := by
  have hφ : φ = Polynomial.eval₂RingHom ψ w := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change φ (Polynomial.C a) = Polynomial.eval₂ ψ w (Polynomial.C a)
      rw [hC, Polynomial.eval₂_C]
    · change φ Polynomial.X = Polynomial.eval₂ ψ w Polynomial.X
      rw [hX, Polynomial.eval₂_X]
  rw [hφ]
  change Polynomial.eval₂ ψ w p = ∑ k ∈ Finset.range (N + 1), ψ (p.coeff k) * w ^ k
  rw [Polynomial.eval₂_eq_sum_range' ψ (Nat.lt_succ_of_le hN) w]

end

end Work.KT.EG
