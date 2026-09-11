import Submission.NBridge

open EquiangularLinesFixedAngle
open Filter
open Matrix
open Unitary
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

/-! Spectral facts for real symmetric matrices and the Gram-matrix realization of
positive semidefinite matrices of bounded rank. -/

/-- Entrywise spectral decomposition of a real symmetric matrix. -/
lemma entrywise_spectral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (i j : Fin n) :
    A i j = ∑ k : Fin n, (hA.eigenvalues k) * (hA.eigenvectorBasis k) i
      * (hA.eigenvectorBasis k) j := by
  classical
  conv_lhs => rw [hA.spectral_theorem]
  rw [conjStarAlgAut_apply]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
    star_trivial]
  apply Finset.sum_congr rfl
  intro x hx
  ring


/-- The spectral radius dominates the absolute value of every eigenvalue. -/
lemma spectralRadius_ge_eigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (i : Fin n) : (ENNReal.ofReal |hA.eigenvalues i|) ≤ spectralRadius ℝ A := by
  classical
  have hm : hA.eigenvalues i ∈ spectrum ℝ A := hA.eigenvalues_mem_spectrum_real i
  have hval : ENNReal.ofReal |hA.eigenvalues i| = ((‖hA.eigenvalues i‖₊ : NNReal) : ENNReal) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
    rfl
  rw [hval]
  unfold spectralRadius
  exact le_trans
    (le_iSup (fun _ : hA.eigenvalues i ∈ spectrum ℝ A => ((‖hA.eigenvalues i‖₊ : NNReal) : ENNReal)) hm)
    (le_iSup (fun k : ℝ => ⨆ _ : k ∈ spectrum ℝ A, ((‖k‖₊ : NNReal) : ENNReal)) (hA.eigenvalues i))

/-- If `spectralRadius A = λ` for `λ > 0`, then every eigenvalue has absolute value at most
`λ` and in particular is at most `λ`. -/
lemma eigenvalues_le_of_spectralRadius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    {lam : ℝ} (hlam : 0 < lam) (hρ : spectralRadius ℝ A = ENNReal.ofReal lam) (i : Fin n) :
    hA.eigenvalues i ≤ lam := by
  have hge := spectralRadius_ge_eigenvalue A hA i
  have hle_abs : ENNReal.ofReal (|hA.eigenvalues i|) ≤ ENNReal.ofReal lam := by
    rwa [hρ] at hge
  have habs : |hA.eigenvalues i| ≤ lam := by
    exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt hlam)).mp hle_abs
  linarith [le_abs_self (hA.eigenvalues i)]


/-- The characteristic polynomial is invariant under conjugation by an invertible matrix. -/
lemma charpoly_conj_of_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hdet : IsUnit P.det) : ((P * A * P⁻¹).charpoly) = A.charpoly := by
  classical
  have hP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  calc
    (P * A * P⁻¹).charpoly = (P * (A * P⁻¹)).charpoly := by rw [mul_assoc]
    _ = ((A * P⁻¹) * P).charpoly := Matrix.charpoly_mul_comm P (A * P⁻¹)
    _ = A.charpoly := by
      rw [mul_assoc, hP']
      simp


/-- The characteristic polynomial of `λI − A` for Hermitian `A` with eigenvalues `σ`. -/
lemma charpoly_sub_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (lam : ℝ) :
    (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A).charpoly
      = ∏ j : Fin n, (Polynomial.X - Polynomial.C (lam - hA.eigenvalues j)) := by
  classical
  let U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  let D : Matrix (Fin n) (Fin n) ℝ := diagonal (fun j : Fin n => hA.eigenvalues j)
  have hspec : A = U * D * star U := by
    dsimp [U, D]
    simpa using hA.spectral_theorem
  have hUU : U * star U = 1 := by
    dsimp [U]
    simpa using (Unitary.mul_star_self (R := Matrix (Fin n) (Fin n) ℝ) hA.eigenvectorUnitary :
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) * star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1)
  have hstU : star U * U = 1 := by
    dsimp [U]
    simpa using (Unitary.star_mul_self (R := Matrix (Fin n) (Fin n) ℝ) hA.eigenvectorUnitary :
      star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) * (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1)
  have hlam : lam • (1 : Matrix (Fin n) (Fin n) ℝ) = lam • (U * star U) := by
    rw [hUU]
  have hdiag : lam • (1 : Matrix (Fin n) (Fin n) ℝ) - D = diagonal (fun j : Fin n => lam - hA.eigenvalues j) := by
    dsimp [D]
    ext i j
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  have hBformula : lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A = U * (diagonal (fun j => lam - hA.eigenvalues j)) * star U := by
    calc
      lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A
          = lam • (U * star U) - U * D * star U := by rw [hlam, hspec]
      _ = U * (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - D) * star U := by
          simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, smul_mul_assoc, mul_smul_comm]
      _ = U * (diagonal (fun j => lam - hA.eigenvalues j)) * star U := by rw [hdiag]
  calc
    (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A).charpoly
        = (U * (diagonal (fun j => lam - hA.eigenvalues j)) * star U).charpoly := by rw [hBformula]
    _ = ((diagonal (fun j => lam - hA.eigenvalues j)) * star U * U).charpoly := by
          rw [mul_assoc]
          exact Matrix.charpoly_mul_comm U (diagonal (fun j : Fin n => lam - hA.eigenvalues j) * star U)
    _ = (diagonal (fun j => lam - hA.eigenvalues j)).charpoly := by
          rw [mul_assoc, hstU]
          simp
    _ = ∏ j : Fin n, (Polynomial.X - Polynomial.C (lam - hA.eigenvalues j)) := by
          rw [Matrix.charpoly_diagonal]


/-- If all eigenvalues of a Hermitian matrix are at most `λ`, then `λI − A` is PSD. -/
lemma sub_psd_of_eigenvalues_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    {lam : ℝ} (hle : ∀ i : Fin n, hA.eigenvalues i ≤ lam) :
    (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := lam • 1 - A
  change B.PosSemidef
  have hB : B.IsHermitian := by
    dsimp [B]
    rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    have ha : A j i = A i j := by
      have h := congrFun (congrFun hA.eq i) j
      simpa [Matrix.conjTranspose_apply] using h
    have h1 : (1 : Matrix (Fin n) (Fin n) ℝ) j i = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
      by_cases h : j = i
      · subst j
        simp [Matrix.one_apply]
      · have hi : i ≠ j := by
          intro hij
          exact h hij.symm
        simp [Matrix.one_apply, h, hi]
    calc
      (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A) j i
          = lam * (1 : Matrix (Fin n) (Fin n) ℝ) j i - A j i := by
            simp [Matrix.sub_apply, Pi.smul_apply, smul_eq_mul]
      _ = lam * (1 : Matrix (Fin n) (Fin n) ℝ) i j - A i j := by rw [h1, ha]
      _ = (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A) i j := by
            simp [Matrix.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply (hB.posSemidef_iff_eigenvalues_nonneg).mpr
  intro i
  let mu : ℝ := hB.eigenvalues i
  have hrootB : B.charpoly.IsRoot mu := by
    dsimp [mu]
    rw [hB.charpoly_eq]
    have hroot_i : (Polynomial.X - Polynomial.C (hB.eigenvalues i)).IsRoot (hB.eigenvalues i) := by
      exact (Polynomial.root_X_sub_C (a := hB.eigenvalues i) (b := hB.eigenvalues i)).2 rfl
    exact (Polynomial.isRoot_prod (Finset.univ) (fun k : Fin n =>
      Polynomial.X - Polynomial.C (hB.eigenvalues k)) (hB.eigenvalues i)).2 ⟨i, Finset.mem_univ i, hroot_i⟩
  have hpoly : B.charpoly = ∏ j : Fin n, (Polynomial.X - Polynomial.C (lam - hA.eigenvalues j)) := by
    dsimp [B]
    exact charpoly_sub_self A hA lam
  have hroot' : (∏ j : Fin n, (Polynomial.X - Polynomial.C (lam - hA.eigenvalues j))).IsRoot mu := by
    exact hpoly ▸ hrootB
  have hex := (Polynomial.isRoot_prod (Finset.univ) (fun j : Fin n =>
    Polynomial.X - Polynomial.C (lam - hA.eigenvalues j)) mu).1 hroot'
  rcases hex with ⟨j, hj, hrootj⟩
  have hmu : lam - hA.eigenvalues j = mu := (Polynomial.root_X_sub_C).mp hrootj
  dsimp [mu] at hmu
  have hnonneg : 0 ≤ lam - hA.eigenvalues j := by linarith [hle j]
  rw [hmu] at hnonneg
  exact hnonneg


/-- If the spectral radius of a Hermitian matrix is `λ > 0`, then `λI − A` is PSD. -/
lemma sub_psd_of_spectralRadius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    {lam : ℝ} (hlam : 0 < lam) (hρ : spectralRadius ℝ A = ENNReal.ofReal lam) :
    (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef := by
  classical
  exact sub_psd_of_eigenvalues_le A hA (eigenvalues_le_of_spectralRadius A hA hlam hρ)

end Submission
