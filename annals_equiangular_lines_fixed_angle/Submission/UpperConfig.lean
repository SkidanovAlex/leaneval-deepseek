import Submission.GraphSpec
import Submission.Correspondence
import Submission.MatrixFacts

open EquiangularLinesFixedAngle
open Filter
open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option maxHeartbeats 1200000

/-! Upper-bound case analysis for a family of `N` equiangular lines in `𝔼^d`.

Given unit vectors `v : Fin N → Euc d` with pairwise `|⟪v i,v j⟫| = α`, the associated
graph `G := assocGraph α v` gives the positive semidefinite matrix
`M := graphMatrix α G ⪰ 0` of rank `≤ d`.  Writing `λ := lam α`, we have
`M = λI − A_G + ½J`.  From this we extract the inequalities behind the paper's
case analysis. -/

/-- the all-ones matrix on `Fin n`. -/
def onesMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1

open Classical in
/-- `graphMatrix = λI − A + ½J`. -/
lemma graphMatrix_decomp {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphMatrix α G = (lam α) • (1 : Matrix (Fin n) (Fin n) ℝ) - (G.adjMatrix ℝ)
      + (1 / 2 : ℝ) • onesMatrix n := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    have hloop : ¬ G.Adj i i := G.loopless.irrefl i
    simp [graphMatrix, onesMatrix, Matrix.sub_apply, Pi.smul_apply, Matrix.one_apply,
      SimpleGraph.adjMatrix_apply, smul_eq_mul, hloop]
  · by_cases hadj : G.Adj i j
    · simp [graphMatrix, onesMatrix, Matrix.sub_apply, Pi.smul_apply, Matrix.one_apply,
        SimpleGraph.adjMatrix_apply, smul_eq_mul, hij, hadj]
      ring
    · simp [graphMatrix, onesMatrix, Matrix.sub_apply, Pi.smul_apply, Matrix.one_apply,
        SimpleGraph.adjMatrix_apply, smul_eq_mul, hij, hadj]

open Classical in
open Classical in
/-- `λI − A = graphMatrix − ½J`. -/
lemma lam_sub_adj_eq_graph_sub {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n)) :
    (lam α) • (1 : Matrix (Fin n) (Fin n) ℝ) - (G.adjMatrix ℝ)
      = graphMatrix α G - (1 / 2 : ℝ) • onesMatrix n := by
  classical
  rw [graphMatrix_decomp (G := G)]
  ext i j
  simp [onesMatrix, Pi.smul_apply, smul_eq_mul]

/-- the rank of the all-ones matrix is at most 1. -/
lemma rank_onesMatrix_le (n : ℕ) : (onesMatrix n).rank ≤ 1 := by
  classical
  have h : onesMatrix n = Matrix.vecMulVec (fun _ : Fin n => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ)) := by
    ext i j
    simp [onesMatrix, Matrix.vecMulVec]
  rw [h]
  exact Matrix.rank_vecMulVec_le _ _

open Classical in
/-- the rank of `½J` is at most 1. -/
lemma rank_half_ones_le (n : ℕ) : (((1 / 2 : ℝ) • onesMatrix n).rank) ≤ 1 := by
  classical
  exact le_trans (rank_smul_le (1 / 2) (onesMatrix n)) (rank_onesMatrix_le n)

/-- Setup for a family of `N` unit vectors with pairwise `|·| = α`. -/
structure ConfigBounds (α : ℝ) (d : ℕ) where
  N : ℕ
  v : Fin N → Euc d
  norm : ∀ i, ‖v i‖ = 1
  angle : ∀ ⦃i j : Fin N⦄, i ≠ j → |⟪v i, v j⟫| = α

namespace ConfigBounds

open Classical in
/-- the associated graph. -/
def G {α : ℝ} {d : ℕ} (C : ConfigBounds α d) : SimpleGraph (Fin C.N) := assocGraph α C.v

open Classical in
/-- adjacency matrix of the associated graph. -/
noncomputable def A {α : ℝ} {d : ℕ} (C : ConfigBounds α d) : Matrix (Fin C.N) (Fin C.N) ℝ :=
  (C.G.adjMatrix ℝ)

open Classical in
/-- the matrix `graphMatrix α G`. -/
noncomputable def M {α : ℝ} {d : ℕ} (C : ConfigBounds α d) : Matrix (Fin C.N) (Fin C.N) ℝ :=
  graphMatrix α C.G

open Classical in
/-- `M` is positive semidefinite. -/
lemma M_posSemidef {α : ℝ} {d : ℕ} (C : ConfigBounds α d) (hα0 : 0 < α) : (C.M).PosSemidef := by
  exact graphMatrix_posSemidef_of_config C.v hα0 C.norm C.angle

open Classical in
/-- `M` has rank at most `d`. -/
lemma M_rank_le {α : ℝ} {d : ℕ} (C : ConfigBounds α d) (hα0 : 0 < α) : (C.M).rank ≤ d := by
  exact rank_graphMatrix_le C.v hα0 C.norm C.angle

open Classical in
/-- the adjacency matrix is Hermitian. -/
lemma A_hermitian {α : ℝ} {d : ℕ} (C : ConfigBounds α d) : (C.A).IsHermitian := by
  exact adjMatrix_isHermitian C.G

open Classical in
/-- the matrix `D := λI − A = M − ½J` has rank at most `d+1`. -/
lemma D_rank_le {α : ℝ} {d : ℕ} (C : ConfigBounds α d) (hα0 : 0 < α) :
    ((lam α) • (1 : Matrix (Fin C.N) (Fin C.N) ℝ) - C.A).rank ≤ d + 1 := by
  classical
  have hD : (lam α) • (1 : Matrix (Fin C.N) (Fin C.N) ℝ) - C.A
      = C.M - (1 / 2 : ℝ) • onesMatrix C.N := by
    dsimp [M, A]
    exact lam_sub_adj_eq_graph_sub (α := α) (G := C.G)
  have h1 := rank_sub_le C.M ((1 / 2 : ℝ) • onesMatrix C.N)
  have hle : (C.M - (1 / 2 : ℝ) • onesMatrix C.N).rank ≤ d + 1 := by
    have hM := C.M_rank_le hα0
    have hJ := rank_half_ones_le C.N
    have hsum : C.M.rank + (((1 / 2 : ℝ) • onesMatrix C.N).rank) ≤ d + 1 := by omega
    exact le_trans h1 hsum
  have heq : ((lam α) • (1 : Matrix (Fin C.N) (Fin C.N) ℝ) - C.A).rank
      = (C.M - (1 / 2 : ℝ) • onesMatrix C.N).rank := congrArg Matrix.rank hD
  rwa [heq]

open Classical in
/-- Case A: if `λ` is not an eigenvalue of `A`, then `N ≤ d + 1`. -/
lemma upper_bound_caseA {α : ℝ} {d : ℕ} (C : ConfigBounds α d) (hα0 : 0 < α)
    (hnotEig : ∀ j : Fin C.N, (C.A_hermitian.eigenvalues j) ≠ lam α) :
    C.N ≤ d + 1 := by
  classical
  have hfull : ((lam α) • (1 : Matrix (Fin C.N) (Fin C.N) ℝ) - C.A).rank = C.N := by
    exact full_rank_of_not_eigenvalue C.A C.A_hermitian hnotEig
  have hle := C.D_rank_le hα0
  rwa [hfull] at hle

end ConfigBounds

end Submission
