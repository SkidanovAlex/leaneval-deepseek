import Submission.Perron
import Submission.RealizeAny
import Submission.LowerD

open EquiangularLinesFixedAngle
open Filter
open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option maxHeartbeats 1200000

/-! Perron--Frobenius extras: the kernel of a positive semidefinite matrix has no
"spurious" vectors with vanishing quadratic form; a nonnegative eigenvector for the
spectral radius of a nonnegative symmetric matrix exists. -/

/-- dot product is ℝ-linear in the first argument (addition). -/
lemma dotProduct_add_left {n : ℕ} (u v w : Fin n → ℝ) : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w := by
  simp [dotProduct, Finset.sum_add_distrib, add_mul]

/-- dot product is ℝ-linear in the first argument (scalars). -/
lemma dotProduct_smul_left {n : ℕ} (c : ℝ) (u v : Fin n → ℝ) : (c • u) ⬝ᵥ v = c * (u ⬝ᵥ v) := by
  simp [dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- real self-adjoint matrices have symmetric entries. -/
lemma hermitian_entries_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (i j : Fin n) : A i j = A j i := by
  have h := congrFun (congrFun hA.eq i) j
  simpa [Matrix.conjTranspose_apply] using h.symm

/-- dot products with a real symmetric matrix commute with the matrix. -/
lemma dotProduct_mulVec_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hAsym : ∀ i j : Fin n, A i j = A j i)
    (u v : Fin n → ℝ) : u ⬝ᵥ (A *ᵥ v) = (A *ᵥ u) ⬝ᵥ v := by
  classical
  rw [Matrix.dotProduct_mulVec]
  congr 1
  apply funext
  intro j
  simp [Matrix.vecMul, Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [hAsym i j]
  ring

/-- If `B ⪰ 0` and `x ⬝ Bx = 0`, then `Bx = 0`. -/
lemma psd_ker_of_quad_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ (B *ᵥ x) = 0) : B *ᵥ x = 0 := by
  classical
  have hBsym : ∀ i j : Fin n, B i j = B j i := hermitian_entries_symm B hB.isHermitian
  have hquad : ∀ y : Fin n → ℝ, 0 ≤ y ⬝ᵥ (B *ᵥ y) := by
    intro y
    have h := hB.dotProduct_mulVec_nonneg y
    have hy : star y = y := by
      ext a
      change star (y a) = y a
      simp
    rwa [hy] at h
  let n2 : ℝ := ((B *ᵥ x) ⬝ᵥ (B *ᵥ x))
  let g : ℝ := ((B *ᵥ x) ⬝ᵥ (B *ᵥ (B *ᵥ x)))
  have hn2ge : 0 ≤ n2 := by
    dsimp [n2]
    rw [dotProduct]
    apply Finset.sum_nonneg
    intro i hi
    rw [← sq]
    exact sq_nonneg ((B *ᵥ x) i)
  have hgge : 0 ≤ g := by
    dsimp [g]
    exact hquad (B *ᵥ x)
  have hfs (s : ℝ) : (x + s • (B *ᵥ x)) ⬝ᵥ (B *ᵥ (x + s • (B *ᵥ x)))
      = x ⬝ᵥ (B *ᵥ x) + 2 * s * ((B *ᵥ x) ⬝ᵥ (B *ᵥ x))
        + s ^ 2 * ((B *ᵥ x) ⬝ᵥ (B *ᵥ (B *ᵥ x))) := by
    have hxBBx : x ⬝ᵥ (B *ᵥ (B *ᵥ x)) = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) :=
      dotProduct_mulVec_symm B hBsym x (B *ᵥ x)
    calc
      (x + s • (B *ᵥ x)) ⬝ᵥ (B *ᵥ (x + s • (B *ᵥ x)))
          = (x + s • (B *ᵥ x)) ⬝ᵥ (B *ᵥ x + s • (B *ᵥ (B *ᵥ x))) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = x ⬝ᵥ (B *ᵥ x) + 2 * s * ((B *ᵥ x) ⬝ᵥ (B *ᵥ x))
          + s ^ 2 * ((B *ᵥ x) ⬝ᵥ (B *ᵥ (B *ᵥ x))) := by
            rw [dotProduct_add]
            rw [dotProduct_add_left]
            rw [dotProduct_add_left]
            rw [dotProduct_smul_right, dotProduct_smul_right, dotProduct_smul_left, dotProduct_smul_left]
            rw [hxBBx]
            ring
  have hnon : ∀ s : ℝ, 0 ≤ x ⬝ᵥ (B *ᵥ x) + 2 * s * n2 + s ^ 2 * g := by
    intro s
    have hs := hquad (x + s • (B *ᵥ x))
    have hfe' : (x + s • (B *ᵥ x)) ⬝ᵥ (B *ᵥ (x + s • (B *ᵥ x)))
        = x ⬝ᵥ (B *ᵥ x) + 2 * s * n2 + s ^ 2 * g := by
      rw [hfs s]
    rwa [hfe'] at hs
  by_contra hBx
  have hn2pos : 0 < n2 := by
    apply lt_of_le_of_ne hn2ge
    intro hn20
    have hzz : (B *ᵥ x) ⬝ᵥ (B *ᵥ x) = 0 := by simpa [n2] using hn20.symm
    have hz := dotProduct_self_eq_zero.mp hzz
    exact hBx hz
  have hbad : (x ⬝ᵥ (B *ᵥ x) + 2 * (-(n2) / (g + 1)) * n2 + (-(n2) / (g + 1)) ^ 2 * g) < 0 := by
    rw [hx]
    have hg1 : 0 < g + 1 := by linarith
    have hden : (g + 1) ≠ 0 := by linarith
    have hmain1 : 2 * (-(n2) / (g + 1)) * n2 = -2 * n2 ^ 2 / (g + 1) := by
      field_simp [hden]
    have hmain2 : (-(n2) / (g + 1)) ^ 2 * g = n2 ^ 2 * g / (g + 1) ^ 2 := by
      field_simp [hden]
    rw [hmain1, hmain2]
    field_simp [hden]
    nlinarith [hn2pos, hg1]

  have hgood := hnon (-(n2) / (g + 1))
  linarith

/-- `|x| ⬝ A|x| ≥ x ⬝ Ax` for entrywise nonnegative `A`. -/
lemma quad_abs_ge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hnonneg : ∀ i j : Fin n, 0 ≤ A i j) (x : Fin n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ (fun i => |x i|) ⬝ᵥ (A *ᵥ (fun i => |x i|)) := by
  classical
  have hdiff : ((fun i => |x i|) ⬝ᵥ (A *ᵥ (fun i => |x i|))) - (x ⬝ᵥ (A *ᵥ x)) ≥ 0 := by
    rw [quad_eq_double_sum A (fun i => |x i|), quad_eq_double_sum A x]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro a ha
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro b hb
    have hprod : |x a| * |x b| ≥ x a * x b := by
      have h1 : x a * x b ≤ |x a * x b| := le_abs_self (x a * x b)
      rw [abs_mul] at h1
      exact h1
    have hterm : 0 ≤ |x a| * (A a b * |x b|) - x a * (A a b * x b) := by
      calc
        0 ≤ A a b * (|x a| * |x b| - x a * x b) := mul_nonneg (hnonneg a b) (by linarith)
        _ = |x a| * (A a b * |x b|) - x a * (A a b * x b) := by ring
    simpa [mul_assoc, mul_comm, mul_left_comm] using hterm
  linarith

/-- dot product of absolute values: `|x| ⬝ |x| = x ⬝ x`. -/
lemma dotProduct_abs_self {n : ℕ} (x : Fin n → ℝ) :
    (fun i => |x i|) ⬝ᵥ (fun i => |x i|) = x ⬝ᵥ x := by
  classical
  calc
    (fun i => |x i|) ⬝ᵥ (fun i => |x i|) = ∑ i : Fin n, |x i| * |x i| := by simp [dotProduct]
    _ = ∑ i : Fin n, x i * x i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← pow_two, ← pow_two, sq_abs]
    _ = x ⬝ᵥ x := by simp [dotProduct]

/-- If `A ≥ 0` is symmetric with spectral radius `λ > 0`, then `λ` has a nonnegative
eigenvector with positive coordinate sum. -/
lemma nonneg_eigenvector_of_spectralRadius {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hnonneg : ∀ i j : Fin n, 0 ≤ A i j) {lam : ℝ} (hlam0 : 0 < lam)
    (hρ : spectralRadius ℝ A = ENNReal.ofReal lam) :
    ∃ u : Fin n → ℝ, (∀ i : Fin n, 0 ≤ u i) ∧ (0 < ∑ i : Fin n, u i)
      ∧ A *ᵥ u = lam • u := by
  classical
  rcases exists_eigenvalue_eq_of_spectralRadius hn A hA hnonneg hlam0 hρ with ⟨j0, hj0⟩
  let v : Fin n → ℝ := (hA.eigenvectorBasis j0).ofLp
  let u : Fin n → ℝ := fun i => |v i|
  refine ⟨u, ?_, ?_, ?_⟩
  · intro i
    dsimp [u]
    exact abs_nonneg (v i)
  · have hv0 : v ≠ 0 := by
      intro hv0
      have hv0' : (hA.eigenvectorBasis j0).ofLp = 0 := by simpa [v] using hv0
      have hd := eigenvector_dotProduct_self A hA j0
      rw [hv0'] at hd
      simp at hd
    have hpos_coord : ∃ i : Fin n, 0 < |v i| := by
      by_contra hnot
      have hall : ∀ i : Fin n, v i = 0 := by
        intro i
        by_contra hne0
        have hpos : 0 < |v i| := abs_pos.mpr hne0
        exact hnot ⟨i, hpos⟩
      apply hv0
      apply funext
      intro i
      exact hall i
    rcases hpos_coord with ⟨i, hi⟩
    have hle1 : |v i| ≤ ∑ j : Fin n, |v j| := by
      exact Finset.single_le_sum (fun j hj => abs_nonneg (v j)) (Finset.mem_univ i)
    have hle2 : 0 < ∑ j : Fin n, |v j| := lt_of_lt_of_le hi hle1
    simpa [u] using hle2
  · let B : Matrix (Fin n) (Fin n) ℝ := lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A
    have hBpsd : B.PosSemidef := sub_psd_of_spectralRadius A hA hlam0 hρ
    have hBv : B *ᵥ v = 0 := by
      dsimp [B, v]
      calc
        (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A) *ᵥ (hA.eigenvectorBasis j0).ofLp
            = (lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ (hA.eigenvectorBasis j0).ofLp
              - A *ᵥ (hA.eigenvectorBasis j0).ofLp := by rw [mulVec_sub]
        _ = lam • (hA.eigenvectorBasis j0).ofLp - A *ᵥ (hA.eigenvectorBasis j0).ofLp := by
              rw [mulVec_smul_one]
        _ = 0 := by
              rw [Matrix.IsHermitian.mulVec_eigenvectorBasis, hj0]
              simp
    have hmain (w : Fin n → ℝ) : w ⬝ᵥ (((lam • (1 : Matrix (Fin n) (Fin n) ℝ)) - A) *ᵥ w)
        = lam * (w ⬝ᵥ w) - w ⬝ᵥ (A *ᵥ w) := dotProduct_smul_sub_mulVec lam A w
    have huBu_le : u ⬝ᵥ (B *ᵥ u) ≤ 0 := by
      have hqa := quad_abs_ge A hnonneg v
      have hv2 : (fun i => |v i|) ⬝ᵥ (fun i => |v i|) = v ⬝ᵥ v := dotProduct_abs_self v
      calc
        u ⬝ᵥ (B *ᵥ u) = lam * (u ⬝ᵥ u) - u ⬝ᵥ (A *ᵥ u) := by
              dsimp [B]
              exact hmain u
        _ ≤ lam * (v ⬝ᵥ v) - v ⬝ᵥ (A *ᵥ v) := by
              dsimp [u] at hqa ⊢
              rw [hv2]
              linarith
        _ = 0 := by
              rw [← hmain v]
              rw [hBv]
              simp [B]
    have huBu_ge : 0 ≤ u ⬝ᵥ (B *ᵥ u) := by
      have h := hBpsd.dotProduct_mulVec_nonneg u
      have hu : star u = u := by
        ext a
        change star (u a) = u a
        simp
      rwa [hu] at h
    have huBu0 : u ⬝ᵥ (B *ᵥ u) = 0 := le_antisymm huBu_le huBu_ge
    have hBu0 : B *ᵥ u = 0 := psd_ker_of_quad_zero B hBpsd u huBu0
    dsimp [B] at hBu0
    have hsub : (lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u = lam • u := by
      rw [mulVec_smul_one]
    have hlin : lam • u - A *ᵥ u = 0 := by
      rw [mulVec_sub] at hBu0
      rw [hsub] at hBu0
      exact hBu0
    have hAul : A *ᵥ u = lam • u := by
      exact (sub_eq_zero.mp hlin).symm
    exact hAul

end Submission
