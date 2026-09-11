import Submission.PfExtra
import Submission.Correspondence

open EquiangularLinesFixedAngle
open Filter
open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option maxHeartbeats 1200000

/-! Foundational matrix lemmas for the upper-bound case analysis: rank subadditivity,
kernel structure of sums of PSD matrices, and the rank/full-rank dichotomy for
`λI − A` when `λ` is not an eigenvalue. -/

/-- rank is subadditive. -/
lemma rank_add_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  classical
  let f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := A.mulVecLin
  let g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := B.mulVecLin
  have hrg : ((A + B).mulVecLin).range ≤ f.range ⊔ g.range := by
    rw [Matrix.mulVecLin_add]
    exact LinearMap.range_add_le f g
  have h1 := Submodule.finrank_mono hrg
  have hsup : Module.finrank ℝ ↥(f.range ⊔ g.range)
      ≤ Module.finrank ℝ ↥f.range + Module.finrank ℝ ↥g.range := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq f.range g.range
    omega
  have rAB : (A + B).rank = Module.finrank ℝ ↥((A + B).mulVecLin).range := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.range_mulVecLin]
  have rA : A.rank = Module.finrank ℝ ↥f.range := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.range_mulVecLin]
  have rB : B.rank = Module.finrank ℝ ↥g.range := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.range_mulVecLin]
  rw [rAB, rA, rB]
  exact le_trans h1 hsup

/-- `x ⬝ Bx = 0` for PSD `B` and kernel facts: if `(A+B)x=0` with `A,B ⪰ 0` then
`Ax = 0` and `Bx = 0`. -/
lemma ker_of_sum_psd {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (x : Fin n → ℝ)
    (hx : (A + B) *ᵥ x = 0) : A *ᵥ x = 0 ∧ B *ᵥ x = 0 := by
  classical
  have h1 : x ⬝ᵥ ((A + B) *ᵥ x) = 0 := by rw [hx, dotProduct_zero]
  have hsplit : x ⬝ᵥ ((A + B) *ᵥ x) = x ⬝ᵥ (A *ᵥ x) + x ⬝ᵥ (B *ᵥ x) := by
    simp [Matrix.add_mulVec, dotProduct_add]
  have hsum0 : x ⬝ᵥ (A *ᵥ x) + x ⬝ᵥ (B *ᵥ x) = 0 := by
    rwa [hsplit] at h1
  have hA1 : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
    have h := hA.dotProduct_mulVec_nonneg x
    have hx' : star x = x := by
      ext a
      change star (x a) = x a
      simp
    rwa [hx'] at h
  have hB1 : 0 ≤ x ⬝ᵥ (B *ᵥ x) := by
    have h := hB.dotProduct_mulVec_nonneg x
    have hx' : star x = x := by
      ext a
      change star (x a) = x a
      simp
    rwa [hx'] at h
  have hAx0 : x ⬝ᵥ (A *ᵥ x) = 0 := by
    have hle0 : x ⬝ᵥ (A *ᵥ x) ≤ 0 := by
      have : x ⬝ᵥ (A *ᵥ x) = - (x ⬝ᵥ (B *ᵥ x)) := by linarith
      linarith
    exact le_antisymm hle0 hA1
  have hBx0 : x ⬝ᵥ (B *ᵥ x) = 0 := by linarith
  exact ⟨psd_ker_of_quad_zero A hA x hAx0, psd_ker_of_quad_zero B hB x hBx0⟩

/-- `λ` is an eigenvalue value iff it is in the spectrum. -/
lemma mem_spectrum_iff_eigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    {lam : ℝ} : lam ∈ spectrum ℝ A ↔ ∃ j : Fin n, hA.eigenvalues j = lam := by
  classical
  constructor
  · intro h
    exact exists_eigenvalue_of_mem_spectrum A hA h
  · rintro ⟨j, hj⟩
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hA.charpoly_eq]
    apply (Polynomial.isRoot_prod _ _ _).2
    exact ⟨j, Finset.mem_univ j, by
      rw [hj]
      exact (Polynomial.root_X_sub_C (a := lam) (b := lam)).2 rfl⟩

/-- determinant of `λI − A` is the product of `(λ − σ_j)`. -/
lemma det_sub_lam_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (lam : ℝ) : (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A).det
      = ∏ j : Fin n, (lam - hA.eigenvalues j) := by
  classical
  have hc : A.charpoly = ∏ j : Fin n, (Polynomial.X - Polynomial.C (hA.eigenvalues j)) := hA.charpoly_eq
  have hmain : (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A).det = A.charpoly.eval lam := by
    have hs : (Matrix.scalar (Fin n) lam) = (lam • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.scalar, h]
    have he := Matrix.eval_charpoly A lam
    rw [hs] at he
    exact he.symm
  rw [hmain, hc]
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  simp

/-- If `λ` is not an eigenvalue of `A`, then `λI − A` is invertible (full rank). -/
lemma full_rank_of_not_eigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) {lam : ℝ} (hlam : ∀ j : Fin n, hA.eigenvalues j ≠ lam) :
    (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A).rank = n := by
  classical
  have hρn : (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A).det ≠ 0 := by
    rw [det_sub_lam_eq A hA lam]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (hlam j).symm
  simpa using (rank_of_det_ne_zero hρn)

/-- If `λ` is an eigenvalue of `A`, then `λI − A` has rank at most `n-1`. -/
lemma nullity_ge_one_of_eigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) {lam : ℝ} (hlam : ∃ j : Fin n, hA.eigenvalues j = lam) :
    (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A).rank ≤ n - 1 := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A
  rcases hlam with ⟨j0, hj0⟩
  let w : Fin n → ℝ := (hA.eigenvectorBasis j0).ofLp
  let f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := B.mulVecLin
  have hw_ker : w ∈ LinearMap.ker f := by
    dsimp [f, w]
    apply LinearMap.mem_ker.mpr
    dsimp [B]
    rw [mulVec_sub, mulVec_smul_one, Matrix.IsHermitian.mulVec_eigenvectorBasis, hj0]
    simp
  have hwne : w ≠ 0 := by
    intro hw0
    have hw0' : (hA.eigenvectorBasis j0).ofLp = 0 := by simpa [w] using hw0
    have hd := eigenvector_dotProduct_self A hA j0
    rw [hw0'] at hd
    simp at hd
  have hker_ne_bot : LinearMap.ker f ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨w, hw_ker, hwne⟩
  have hker_pos : 0 < Module.finrank ℝ ↥(LinearMap.ker f) := by
    have hz : Module.finrank ℝ ↥(LinearMap.ker f) ≠ 0 := by
      intro h0
      exact hker_ne_bot (Submodule.finrank_eq_zero.mp h0)
    exact Nat.pos_of_ne_zero hz
  have hsp : (Submodule.span ℝ (Set.range B.col)) = LinearMap.range f := by
    exact (Matrix.range_mulVecLin B).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [Matrix.rank_eq_finrank_span_cols, hsp]
  have hsum : Module.finrank ℝ ↥(LinearMap.range f) + Module.finrank ℝ ↥(LinearMap.ker f) = n := by
    have hd2 : Module.finrank ℝ (Fin n → ℝ) = n := by
      simpa using Module.finrank_pi ℝ (Fin n)
    simpa [f] using (hrn.trans (by rw [hd2]))
  omega


/-- `(A - B).mulVecLin = A.mulVecLin - B.mulVecLin`. -/
lemma mulVecLin_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A - B).mulVecLin = A.mulVecLin - B.mulVecLin := by
  classical
  apply LinearMap.ext
  intro x
  ext i
  simp [Matrix.mulVecLin, Matrix.sub_apply]

/-- rank is subadditive for differences. -/
lemma rank_sub_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : (A - B).rank ≤ A.rank + B.rank := by
  classical
  let f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := A.mulVecLin
  let g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := B.mulVecLin
  have hlin : (A - B).mulVecLin = f - g := by
    dsimp [f, g]
    exact mulVecLin_sub A B
  have hrg : ((A - B).mulVecLin).range ≤ f.range ⊔ g.range := by
    intro y hy
    rcases LinearMap.mem_range.mp hy with ⟨x, hx⟩
    have hyfg : y = f x - g x := by
      rw [hlin] at hx
      simpa using hx.symm
    rw [hyfg]
    refine Submodule.mem_sup.mpr ?_
    refine ⟨f x, LinearMap.mem_range.mpr ⟨x, rfl⟩, -(g x), LinearMap.mem_range.mpr ⟨-x, ?_⟩, ?_⟩
    · simp
    · exact sub_eq_add_neg (f x) (g x)
  have h1 := Submodule.finrank_mono hrg
  have hsup : Module.finrank ℝ ↥(f.range ⊔ g.range)
      ≤ Module.finrank ℝ ↥f.range + Module.finrank ℝ ↥g.range := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq f.range g.range
    omega
  have rAB : (A - B).rank = Module.finrank ℝ ↥((A - B).mulVecLin).range := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.range_mulVecLin]
  have rA : A.rank = Module.finrank ℝ ↥f.range := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.range_mulVecLin]
  have rB : B.rank = Module.finrank ℝ ↥g.range := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.range_mulVecLin]
  rw [rAB, rA, rB]
  exact le_trans h1 hsup

end Submission
