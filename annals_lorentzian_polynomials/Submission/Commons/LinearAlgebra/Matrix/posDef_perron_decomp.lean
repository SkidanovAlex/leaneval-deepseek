import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one

namespace Commons.LinearAlgebra.Matrix

open _root_.Matrix Polynomial Set
open scoped BigOperators

lemma dotProduct_mulVec_symm_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (x y : Fin n → ℝ) :
    x ⬝ᵥ A *ᵥ y = y ⬝ᵥ A *ᵥ x := by
  classical
  simp only [dotProduct, Matrix.mulVec_apply_eq_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [hA.apply i j]
  ring

lemma dotProduct_mulVec_eigen_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (u : Fin n → ℝ) (lam : ℝ)
    (hu_eigen : A.mulVec u = lam • u) (y : Fin n → ℝ) :
    u ⬝ᵥ A *ᵥ y = lam * (u ⬝ᵥ y) := by
  calc
    u ⬝ᵥ A *ᵥ y = y ⬝ᵥ A *ᵥ u := dotProduct_mulVec_symm_eq A hA u y
    _ = y ⬝ᵥ (lam • u) := by rw [hu_eigen]
    _ = lam * (y ⬝ᵥ u) := by simp [dotProduct_smul]
    _ = lam * (u ⬝ᵥ y) := by rw [dotProduct_comm]

lemma dotProduct_mulVec_eigen_right {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℝ) (lam : ℝ)
    (hu_eigen : A.mulVec u = lam • u) (y : Fin n → ℝ) :
    y ⬝ᵥ A *ᵥ u = lam * (y ⬝ᵥ u) := by
  rw [hu_eigen]
  simp [dotProduct_smul]

lemma dotProduct_mulVec_eigen_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℝ) (lam : ℝ)
    (hu_norm : (∑ i : Fin n, u i * u i) = 1)
    (hu_eigen : A.mulVec u = lam • u) :
    u ⬝ᵥ A *ᵥ u = lam := by
  rw [hu_eigen]
  rw [dotProduct_smul]
  have hu_self : u ⬝ᵥ u = 1 := by simpa [dotProduct] using hu_norm
  rw [hu_self]
  simp

lemma dotProduct_mulVec_eq_sum_mul_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) :
    x ⬝ᵥ A *ᵥ y = ∑ i : Fin n, ∑ j : Fin n, x i * A i j * y j := by
  classical
  simp only [dotProduct, Matrix.mulVec_apply_eq_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma norm_decomp {n : ℕ} (u x : Fin n → ℝ)
    (hu_norm : (∑ i : Fin n, u i * u i) = 1) :
    let α : ℝ := u ⬝ᵥ x
    let y : Fin n → ℝ := x - α • u
    x ⬝ᵥ x = y ⬝ᵥ y + α ^ 2 := by
  classical
  dsimp
  have hu_self : u ⬝ᵥ u = 1 := by simpa [dotProduct] using hu_norm
  have hyu : u ⬝ᵥ (x - (u ⬝ᵥ x) • u) = 0 := by
    rw [dotProduct_sub, dotProduct_smul]
    simp [hu_self]
  have hx : x = (x - (u ⬝ᵥ x) • u) + (u ⬝ᵥ x) • u := by
    ext i
    simp [sub_eq_add_neg, add_assoc]
  rw [hx]
  simp [dotProduct_smul, hu_self, dotProduct_comm, pow_two]

lemma quad_A_decomp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (u : Fin n → ℝ) (lam : ℝ)
    (hu_norm : (∑ i : Fin n, u i * u i) = 1)
    (hu_eigen : A.mulVec u = lam • u) (x : Fin n → ℝ) :
    let α : ℝ := u ⬝ᵥ x
    let y : Fin n → ℝ := x - α • u
    x ⬝ᵥ A *ᵥ x = y ⬝ᵥ A *ᵥ y + lam * α ^ 2 := by
  classical
  dsimp
  let α : ℝ := u ⬝ᵥ x
  let y : Fin n → ℝ := x - α • u
  have hu_self : u ⬝ᵥ u = 1 := by simpa [dotProduct] using hu_norm
  have hyu : u ⬝ᵥ y = 0 := by
    dsimp [y, α]
    rw [dotProduct_sub, dotProduct_smul]
    simp [hu_self]
  have hx : x = y + α • u := by
    dsimp [y, α]
    ext i
    simp [sub_eq_add_neg, add_assoc]
  calc
    x ⬝ᵥ A *ᵥ x = (y + α • u) ⬝ᵥ A *ᵥ (y + α • u) := by rw [hx]
    _ = y ⬝ᵥ A *ᵥ y + lam * α ^ 2 := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      simp [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul]
      rw [dotProduct_mulVec_eigen_left A hA u lam hu_eigen y,
          dotProduct_mulVec_eigen_right A u lam hu_eigen y,
          dotProduct_mulVec_eigen_self A u lam hu_norm hu_eigen]
      rw [dotProduct_comm y u, hyu]
      simp [pow_two]
      ring

lemma quad_vecMulVec_self {n : ℕ} (u x : Fin n → ℝ) :
    x ⬝ᵥ (Matrix.vecMulVec u u) *ᵥ x = (u ⬝ᵥ x) ^ 2 := by
  rw [Matrix.vecMulVec_mulVec]
  simp [dotProduct_smul, dotProduct_comm, pow_two]

lemma quad_B_basic {n : ℕ} (u x : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (lam ε : ℝ) :
    x ⬝ᵥ ((lam • Matrix.vecMulVec u u - A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x)
      = lam * (u ⬝ᵥ x) ^ 2 - x ⬝ᵥ A *ᵥ x + ε * (x ⬝ᵥ x) := by
  simp [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    quad_vecMulVec_self, dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]

lemma quad_B_decomp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (u : Fin n → ℝ) (lam ε : ℝ)
    (hu_norm : (∑ i : Fin n, u i * u i) = 1)
    (hu_eigen : A.mulVec u = lam • u) (x : Fin n → ℝ) :
    let α : ℝ := u ⬝ᵥ x
    let y : Fin n → ℝ := x - α • u
    x ⬝ᵥ ((lam • Matrix.vecMulVec u u - A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x)
      = - (y ⬝ᵥ A *ᵥ y) + ε * (y ⬝ᵥ y + α ^ 2) := by
  classical
  dsimp
  let α : ℝ := u ⬝ᵥ x
  let y : Fin n → ℝ := x - α • u
  have hB := quad_B_basic u x A lam ε
  have hAdecomp := quad_A_decomp A hA u lam hu_norm hu_eigen x
  have hnorm := norm_decomp u x hu_norm
  dsimp [α, y] at hAdecomp hnorm
  rw [hB, hAdecomp, hnorm]
  ring

lemma perron_decomp_hermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (u : Fin n → ℝ) (lam ε : ℝ) :
    ((lam • Matrix.vecMulVec u u - A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian) := by
  rw [Matrix.isHermitian_iff_isSymm]
  simp [Matrix.IsSymm, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_vecMulVec]
  exact hA

theorem posDef_perron_decomp
    {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (u : Fin n → ℝ) (lam ε : ℝ)
    (hlam : 0 < lam) (hu_norm : (∑ i : Fin n, u i * u i) = 1)
    (hu_eigen : A.mulVec u = lam • u)
    (hquad : ∀ x : Fin n → ℝ, (∑ i : Fin n, u i * x i) = 0 →
      (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j) ≤ 0)
    (hε : 0 < ε) :
    (lam • Matrix.vecMulVec u u - A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  classical
  have _ : 0 < n := hn
  have _ : 0 < lam := hlam
  let B : Matrix (Fin n) (Fin n) ℝ := lam • Matrix.vecMulVec u u - A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)
  have hB_herm : B.IsHermitian := by
    dsimp [B]
    exact perron_decomp_hermitian A hA u lam ε
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hB_herm
  intro x hx
  let α : ℝ := u ⬝ᵥ x
  let y : Fin n → ℝ := x - α • u
  have hyu : u ⬝ᵥ y = 0 := by
    dsimp [y, α]
    rw [dotProduct_sub, dotProduct_smul]
    have hu_self : u ⬝ᵥ u = 1 := by simpa [dotProduct] using hu_norm
    simp [hu_self]
  have hyu_sum : (∑ i : Fin n, u i * y i) = 0 := by
    simpa [dotProduct] using hyu
  have hA_y_nonpos_sum : (∑ i : Fin n, ∑ j : Fin n, y i * A i j * y j) ≤ 0 :=
    hquad y hyu_sum
  have hA_y_nonpos : y ⬝ᵥ A *ᵥ y ≤ 0 := by
    rw [dotProduct_mulVec_eq_sum_mul_left]
    exact hA_y_nonpos_sum
  have hneg_nonneg : 0 ≤ - (y ⬝ᵥ A *ᵥ y) := neg_nonneg.mpr hA_y_nonpos
  have hx_self_pos : 0 < x ⬝ᵥ x := by
    simpa using (dotProduct_self_star_pos_iff (v := x)).2 hx
  have hnorm_decomp := norm_decomp u x hu_norm
  dsimp [α, y] at hnorm_decomp
  have hnorm_pos : 0 < y ⬝ᵥ y + α ^ 2 := by
    rw [← hnorm_decomp]
    exact hx_self_pos
  have hpos_eps : 0 < ε * (y ⬝ᵥ y + α ^ 2) := mul_pos hε hnorm_pos
  have hsum_pos : 0 < - (y ⬝ᵥ A *ᵥ y) + ε * (y ⬝ᵥ y + α ^ 2) :=
    add_pos_of_nonneg_of_pos hneg_nonneg hpos_eps
  have hquad_B := quad_B_decomp A hA u lam ε hu_norm hu_eigen x
  dsimp [α, y] at hquad_B
  have hmain : 0 < x ⬝ᵥ B *ᵥ x := by
    rw [hquad_B]
    exact hsum_pos
  simpa using hmain

end Commons.LinearAlgebra.Matrix