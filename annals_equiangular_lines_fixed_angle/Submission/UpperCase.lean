import Submission.UpperConfig
import Submission.Components
import Submission.UpperRelabel
import Submission.GraphSpec
import Submission.KOrder
import Submission.ComponentsPF
import Mathlib.LinearAlgebra.Dimension.Constructions

open EquiangularLinesFixedAngle
open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section

variable {n : ℕ}

/-! Upper-bound case analysis (cases A / B1 / B2 of Jiang--Tidor--Yao--Zhang--Zhao).

Throughout: `v : Fin n → Euc d` is a family of unit vectors with pairwise `|⟪v i, v j⟫| = α`;
`G := assocGraph α v`, `A := G.adjMatrix ℝ`, `M := graphMatrix α G = λI − A + ½J ⪰ 0`,
`rank M ≤ d`, `λ := lam α = (1−α)/(2α) > 0`. -/

/-- quadratic form of the all-ones matrix: `x⬝Jx = (Σx)²`. -/
lemma dotProduct_ones (n : ℕ) (x : Fin n → ℝ) :
    x ⬝ᵥ (onesMatrix n *ᵥ x) = (∑ i : Fin n, x i) ^ 2 := by
  classical
  simp [dotProduct, Matrix.mulVec, onesMatrix]
  rw [← Finset.sum_mul]
  rw [← pow_two]

/-- `(1/2)J` is positive semidefinite. -/
lemma onesMatrix_posSemidef (n : ℕ) : (onesMatrix n).PosSemidef := by
  classical
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    simp [onesMatrix]
  · intro x
    have hx : star x = x := by ext a; simp
    rw [hx]
    rw [dotProduct_ones]
    exact sq_nonneg _

/-- `(1/2)J` is positive semidefinite. -/
lemma half_ones_posSemidef (n : ℕ) : (((1 / 2 : ℝ) • onesMatrix n).PosSemidef) := by
  classical
  exact (onesMatrix_posSemidef n).smul (by norm_num)

/-- a Perron vector of the associated graph (nonnegative, positive sum). -/
lemma b1_pf_vector {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n))
    (hα0 : 0 < α) (hα1 : α < 1) (hn : 0 < n)
    (hρ : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal (lam α)) :
    ∃ u : Fin n → ℝ, (∀ i, 0 ≤ u i) ∧ (0 < ∑ i : Fin n, u i)
      ∧ (G.adjMatrix ℝ) *ᵥ u = (lam α) • u := by
  classical
  exact nonneg_eigenvector_of_spectralRadius hn (G.adjMatrix ℝ) (adjMatrix_isHermitian G)
    (adjMatrix_nonneg G) (lam_pos hα0 hα1) hρ

/-- in case B1 (`ρ(A) = λ`), `graphMatrix x = 0` iff both `(λI−A)x = 0` and `Jx = 0`. -/
lemma mulVec_graphMatrix_eq_zero_iff {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n))
    (hα0 : 0 < α) (hα1 : α < 1)
    (hρ : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal (lam α))
    (x : Fin n → ℝ) :
    (graphMatrix α G) *ᵥ x = 0
      ↔ ((lam α • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ) *ᵥ x = 0
          ∧ (((1 / 2 : ℝ) • onesMatrix n) *ᵥ x = 0)) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := (lam α) • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
  let Jm : Matrix (Fin n) (Fin n) ℝ := (1 / 2 : ℝ) • onesMatrix n
  let M : Matrix (Fin n) (Fin n) ℝ := graphMatrix α G
  have hBpsd : B.PosSemidef := by
    dsimp [B]
    exact sub_psd_of_spectralRadius (G.adjMatrix ℝ) (adjMatrix_isHermitian G) (lam_pos hα0 hα1) hρ
  have hJpsd : Jm.PosSemidef := by
    dsimp [Jm]
    exact half_ones_posSemidef n
  have hdecomp : B + Jm = M := by
    dsimp [B, Jm, M]
    rw [graphMatrix_decomp]
  constructor
  · intro hx
    have hxM : M *ᵥ x = 0 := by simpa [M] using hx
    rcases ker_of_sum_psd B Jm hBpsd hJpsd x (by simpa [hdecomp] using hxM) with ⟨hBx, hJx⟩
    exact ⟨by simpa [B] using hBx, by simpa [Jm] using hJx⟩
  · rintro ⟨hBx, hJx⟩
    change M *ᵥ x = 0
    rw [← hdecomp]
    rw [add_mulVec, hBx, hJx]
    simp

/-- rank-nullity for square matrices: `rank + nullity = n`. -/
lemma rank_add_nullity_eq (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) :
    B.rank + Module.finrank ℝ ↥(LinearMap.ker B.mulVecLin) = n := by
  classical
  have h := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  have hr : Module.finrank ℝ (LinearMap.range B.mulVecLin) = B.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.range_mulVecLin]
  have hn : Module.finrank ℝ (Fin n → ℝ) = n := by
    simpa using Module.finrank_pi ℝ (fun _ : Fin n => ℝ)
  rw [hr, hn] at h
  exact h

/-- rank of `λI − A_G` is at most `d − 1` in case B1. -/
lemma b1_rank_le_d_sub_one {α : ℝ} {n d : ℕ} (v : Fin n → Euc d)
    (hα0 : 0 < α) (hα1 : α < 1) (hn : 0 < n)
    (hvnorm : ∀ i, ‖v i‖ = 1)
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α)
    (hρ : spectralRadius ℝ ((assocGraph α v).adjMatrix ℝ) = ENNReal.ofReal (lam α)) :
    ((lam α) • (1 : Matrix (Fin n) (Fin n) ℝ) - (assocGraph α v).adjMatrix ℝ).rank ≤ d - 1 := by
  classical
  let G : SimpleGraph (Fin n) := assocGraph α v
  let A : Matrix (Fin n) (Fin n) ℝ := G.adjMatrix ℝ
  let B : Matrix (Fin n) (Fin n) ℝ := (lam α) • (1 : Matrix (Fin n) (Fin n) ℝ) - A
  let M : Matrix (Fin n) (Fin n) ℝ := graphMatrix α G
  have hMrank : M.rank ≤ d := by
    dsimp [M, G]
    exact rank_graphMatrix_le v hα0 hvnorm hvangle
  rcases b1_pf_vector G hα0 hα1 hn (by simpa [A, G] using hρ) with ⟨u, _hu_nonneg, hu_sum, hu_eig⟩
  -- u ∈ ker B
  have huB : B *ᵥ u = 0 := by
    dsimp [B, A]
    rw [mulVec_sub_any]
    have hsc : ((lam α) • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u = lam α • u := by
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.one_apply, Finset.sum_ite_eq]
    rw [hsc, hu_eig]
    simp
  -- u ∉ ker Jm
  have huJ : ¬ (((1 / 2 : ℝ) • onesMatrix n) *ᵥ u) = 0 := by
    intro huj
    have h := congrFun huj ⟨0, hn⟩
    have hc : (((1 / 2 : ℝ) • onesMatrix n) *ᵥ u) ⟨0, hn⟩ = (1 / 2 : ℝ) * (∑ i : Fin n, u i) := by
      simp [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, onesMatrix]
      rw [Finset.mul_sum]
    have hc0 : (1 / 2 : ℝ) * (∑ i : Fin n, u i) = 0 := by
      rwa [hc] at h
    linarith
  -- ker M ⊆ ker B via the iff
  have hKM_le : (LinearMap.ker M.mulVecLin) ≤ LinearMap.ker B.mulVecLin := by
    intro x hx
    change x ∈ LinearMap.ker B.mulVecLin
    have hx' : (graphMatrix α G) *ᵥ x = 0 := by
      change M.mulVecLin x = 0
      dsimp [M] at hx ⊢
      exact hx
    rcases (mulVec_graphMatrix_eq_zero_iff G hα0 hα1 (by simpa [G] using hρ) x).1 hx' with ⟨hBx, hJx⟩
    change B *ᵥ x = 0
    simpa [B] using hBx
  have huM : u ∉ LinearMap.ker M.mulVecLin := by
    intro hM
    have hM' : (graphMatrix α G) *ᵥ u = 0 := by
      change M.mulVecLin u = 0
      dsimp [M] at hM ⊢
      exact hM
    rcases (mulVec_graphMatrix_eq_zero_iff G hα0 hα1 (by simpa [G] using hρ) u).1 hM' with ⟨hB, hJ⟩
    exact huJ hJ
  have hKM_strict : (LinearMap.ker M.mulVecLin) < LinearMap.ker B.mulVecLin := by
    refine lt_of_le_of_ne hKM_le ?_
    intro hEq
    have huM' : u ∈ LinearMap.ker M.mulVecLin := by
      rw [hEq]
      change u ∈ LinearMap.ker B.mulVecLin
      exact huB
    exact huM huM'
  have hdim_lt : Module.finrank ℝ ↥(LinearMap.ker M.mulVecLin)
      < Module.finrank ℝ ↥(LinearMap.ker B.mulVecLin) := by
    exact Submodule.finrank_lt_finrank_of_lt hKM_strict
  have hrn_B : B.rank + Module.finrank ℝ ↥(LinearMap.ker B.mulVecLin) = n := by
    exact rank_add_nullity_eq n B
  have hrn_M : M.rank + Module.finrank ℝ ↥(LinearMap.ker M.mulVecLin) = n := by
    exact rank_add_nullity_eq n M
  have hbrp1 : B.rank + 1 ≤ M.rank := by
    have hEq : B.rank + Module.finrank ℝ ↥(LinearMap.ker B.mulVecLin)
        = M.rank + Module.finrank ℝ ↥(LinearMap.ker M.mulVecLin) := by
      rw [hrn_B, hrn_M]
    omega
  have hbrd : B.rank + 1 ≤ d := le_trans hbrp1 hMrank
  have hb : B.rank ≤ d - 1 := by omega
  dsimp [B, A, G] at hb
  exact hb

end
end Submission
