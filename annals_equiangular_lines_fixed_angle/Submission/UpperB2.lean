import Submission.UpperB1
import Submission.Switch
import Submission.ComponentsPF
import Submission.Components
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open EquiangularLinesFixedAngle
open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section

/-! # Case B2 machinery (structural part)

Setup: `v : Fin n -> Euc d` (unit vectors, pairwise |inner| = α), `G := assocGraph α v`,
`A := G.adjMatrix ℝ`, `λ := lam α > 0`.  The matrix `M := graphMatrix α G` satisfies
`M ⪰ 0` and `M = λ•1 − A + ½J` (`graphMatrix_decomp`).

CASE B2 assumptions (provided by the caller):
  * λ is an eigenvalue of A
  * ρ0 : ℝ with λ < ρ0 and spectralRadius ℝ A = ENNReal.ofReal ρ0

Prove the structural facts below.  Proven helpers: UpperB1 (eigen_component_of,
spectrum_comp_subset, compRho_le, b1_rank_le_d_sub_one), ComponentsPF (generic PF:
nonneg_eigenvector_of_spectralRadius_any, eigenspace_eq_span_of_positive_any,
spectralRadius_ge_eigenvalue_any, exists_eigenvalue_of_mem_spectrum_any,
positive_eigenvector_of_connected_any), Components (compRest_ker, compRest_compExt,
adj_compExt_outside, compRest, compExt, compPreconnected, compReachable), UpperCase
(rank_add_nullity_eq, b1_pf_vector, half_ones_posSemidef, dotProduct_ones,
mulVec_graphMatrix_eq_zero_iff), UpperConfig (graphMatrix_decomp, rank_graphMatrix_le,
graphMatrix_posSemidef_of_config), Perron/PfExtra/GraphSpec (Fin versions).

Prove your own small helpers as needed, e.g.:
  * eigenvector -> spectrum membership (det route via Matrix.eval_charpoly and
    Matrix.nonsing_inv_mul + (A*B)*ᵥx = A *ᵥ (B*ᵥx)).
  * ofReal ν ≤ ρ(A) from an eigenvector with value ν.
  * eigenvector dot products with hA.eigenvectorBasis vectors (OrthonormalBasis.orthonormal,
    Matrix.IsHermitian.mulVec_eigenvectorBasis, eigenvector_dotProduct_self_any).
Good luck!
-/

/-- number of eigenvalues strictly above `t`. -/
noncomputable def countAbove {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (t : ℝ) : ℕ := Fintype.card {i : ι // t < hA.eigenvalues i}

/-- quadratic form of `graphMatrix` decomposed -/
lemma graphMatrix_quad {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ) :
    w ⬝ᵥ ((graphMatrix α G) *ᵥ w)
      = (lam α) * (w ⬝ᵥ w) - w ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ w) + (1 / 2 : ℝ) * (∑ i : Fin n, w i)^2 := by
  classical
  rw [graphMatrix_decomp (G := G)]
  have hsub : w ⬝ᵥ (((lam α) • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ) *ᵥ w)
      = (lam α) * (w ⬝ᵥ w) - w ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ w) := by
    exact dotProduct_smul_sub_mulVec (μ := lam α) (A := G.adjMatrix ℝ) (x := w)
  have hJ : w ⬝ᵥ (((1 / 2 : ℝ) • onesMatrix n) *ᵥ w) = (1 / 2 : ℝ) * (∑ i : Fin n, w i)^2 := by
    rw [Matrix.smul_mulVec]
    rw [dotProduct_smul_right]
    rw [dotProduct_ones]
  calc
    w ⬝ᵥ (((lam α) • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
        + (1 / 2 : ℝ) • onesMatrix n) *ᵥ w)
        = w ⬝ᵥ ((((lam α) • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ) *ᵥ w)
            + ((1 / 2 : ℝ) • onesMatrix n) *ᵥ w) := by
            rw [Matrix.add_mulVec]
    _ = w ⬝ᵥ (((lam α) • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ) *ᵥ w)
        + w ⬝ᵥ (((1 / 2 : ℝ) • onesMatrix n) *ᵥ w) := by
            rw [dotProduct_add]
    _ = ((lam α) * (w ⬝ᵥ w) - w ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ w))
        + (1 / 2 : ℝ) * (∑ i : Fin n, w i)^2 := by
            rw [hsub, hJ]

/-- PSD nonneg quad form -/
lemma graphMatrix_quad_nonneg {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n))
    (hMpsd : (graphMatrix α G).PosSemidef) (w : Fin n → ℝ) :
    0 ≤ w ⬝ᵥ ((graphMatrix α G) *ᵥ w) := by
  classical
  have h := hMpsd.dotProduct_mulVec_nonneg w
  have hstar : star w = w := by
    funext a
    change star (w a) = w a
    simp
  simpa [hstar] using h

/-- sum of a linear combination of two functions -/
lemma sum_add_smul {ι : Type*} [Fintype ι] (c d : ℝ) (x y : ι → ℝ) :
    (∑ k : ι, (c • x + d • y) k) = c * (∑ k : ι, x k) + d * (∑ k : ι, y k) := by
  classical
  calc
    (∑ k : ι, (c • x + d • y) k) = (∑ k : ι, (c * x k + d * y k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp [Pi.add_apply, Pi.smul_apply]
    _ = (∑ k : ι, c * x k) + (∑ k : ι, d * y k) := by
          rw [Finset.sum_add_distrib]
    _ = c * (∑ k : ι, x k) + d * (∑ k : ι, y k) := by
          congr 1
          · rw [← Finset.mul_sum]
          · rw [← Finset.mul_sum]

/-- dot product of two different orthonormal eigenvectors is zero -/
lemma eigenvector_dotProduct_other {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) {i j : ι} (hij : i ≠ j) :
    (hA.eigenvectorBasis i).ofLp ⬝ᵥ (hA.eigenvectorBasis j).ofLp = 0 := by
  classical
  have hob : ⟪hA.eigenvectorBasis i, hA.eigenvectorBasis j⟫ = 0 := hA.eigenvectorBasis.orthonormal.2 hij
  rw [← hob]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- norm-squared of a linear combination of two orthonormal eigenvectors -/
lemma normSq_lincomb_eigen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) {i j : ι} (hij : i ≠ j) (a b : ℝ) :
    (a • (hA.eigenvectorBasis i).ofLp + b • (hA.eigenvectorBasis j).ofLp) ⬝ᵥ
        (a • (hA.eigenvectorBasis i).ofLp + b • (hA.eigenvectorBasis j).ofLp)
      = a ^ 2 + b ^ 2 := by
  classical
  let v : ι → ℝ := (hA.eigenvectorBasis i).ofLp
  let w : ι → ℝ := (hA.eigenvectorBasis j).ofLp
  have hvv : v ⬝ᵥ v = 1 := by
    dsimp [v]
    exact eigenvector_dotProduct_self_any A hA i
  have hww : w ⬝ᵥ w = 1 := by
    dsimp [w]
    exact eigenvector_dotProduct_self_any A hA j
  have hvw : v ⬝ᵥ w = 0 := by
    dsimp [v, w]
    exact eigenvector_dotProduct_other (A := A) (hA := hA) hij
  have hwv : w ⬝ᵥ v = 0 := by
    dsimp [v, w]
    rw [dotProduct_comm]
    exact eigenvector_dotProduct_other (A := A) (hA := hA) hij
  have h1 : (a • v) ⬝ᵥ (a • v + b • w) + (b • w) ⬝ᵥ (a • v + b • w)
      = a * (a * (v ⬝ᵥ v) + b * (v ⬝ᵥ w)) + b * (a * (w ⬝ᵥ v) + b * (w ⬝ᵥ w)) := by
    rw [dotProduct_smul_left_pf, dotProduct_smul_left_pf]
    rw [dotProduct_add, dotProduct_add]
    rw [dotProduct_smul_right_pf, dotProduct_smul_right_pf, dotProduct_smul_right_pf, dotProduct_smul_right_pf]
  calc
    (a • v + b • w) ⬝ᵥ (a • v + b • w)
        = (a • v) ⬝ᵥ (a • v + b • w) + (b • w) ⬝ᵥ (a • v + b • w) := by
            rw [dotProduct_add_left_pf]
    _ = a * (a * (v ⬝ᵥ v) + b * (v ⬝ᵥ w)) + b * (a * (w ⬝ᵥ v) + b * (w ⬝ᵥ w)) := h1
    _ = a ^ 2 + b ^ 2 := by
            rw [hvv, hww, hvw, hwv]
            ring

/-- quadratic form of a linear combination of two orthonormal eigenvectors -/
lemma quad_lincomb_eigen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) {i j : ι} (hij : i ≠ j) (a b : ℝ) :
    (a • (hA.eigenvectorBasis i).ofLp + b • (hA.eigenvectorBasis j).ofLp) ⬝ᵥ
        (A *ᵥ (a • (hA.eigenvectorBasis i).ofLp + b • (hA.eigenvectorBasis j).ofLp))
      = a ^ 2 * hA.eigenvalues i + b ^ 2 * hA.eigenvalues j := by
  classical
  let v : ι → ℝ := (hA.eigenvectorBasis i).ofLp
  let w : ι → ℝ := (hA.eigenvectorBasis j).ofLp
  have hAv : A *ᵥ v = (hA.eigenvalues i) • v := by
    dsimp [v]
    exact hA.mulVec_eigenvectorBasis i
  have hAw : A *ᵥ w = (hA.eigenvalues j) • w := by
    dsimp [w]
    exact hA.mulVec_eigenvectorBasis j
  have hvv : v ⬝ᵥ v = 1 := by
    dsimp [v]
    exact eigenvector_dotProduct_self_any A hA i
  have hww : w ⬝ᵥ w = 1 := by
    dsimp [w]
    exact eigenvector_dotProduct_self_any A hA j
  have hvw : v ⬝ᵥ w = 0 := by
    dsimp [v, w]
    exact eigenvector_dotProduct_other (A := A) (hA := hA) hij
  have hwv : w ⬝ᵥ v = 0 := by
    dsimp [v, w]
    rw [dotProduct_comm]
    exact eigenvector_dotProduct_other (A := A) (hA := hA) hij
  let μi : ℝ := hA.eigenvalues i
  let μj : ℝ := hA.eigenvalues j
  have hlin : A *ᵥ (a • v + b • w) = (a * μi) • v + (b * μj) • w := by
    rw [Matrix.mulVec_add]
    rw [Matrix.mulVec_smul]
    rw [Matrix.mulVec_smul]
    rw [hAv, hAw]
    dsimp [μi, μj]
    funext k
    simp [Pi.smul_apply]
    ring
  calc
    (a • v + b • w) ⬝ᵥ (A *ᵥ (a • v + b • w))
        = (a • v + b • w) ⬝ᵥ ((a * μi) • v + (b * μj) • w) := by rw [hlin]
    _ = a * ((a * μi) * (v ⬝ᵥ v) + (b * μj) * (v ⬝ᵥ w))
        + b * ((a * μi) * (w ⬝ᵥ v) + (b * μj) * (w ⬝ᵥ w)) := by
            rw [dotProduct_add_left_pf]
            rw [dotProduct_smul_left_pf, dotProduct_smul_left_pf]
            rw [dotProduct_add, dotProduct_add]
            rw [dotProduct_smul_right_pf, dotProduct_smul_right_pf, dotProduct_smul_right_pf, dotProduct_smul_right_pf]
    _ = a ^ 2 * hA.eigenvalues i + b ^ 2 * hA.eigenvalues j := by
            rw [hvv, hww, hvw, hwv]
            ring

/-- in case B2, at most one eigenvalue of `A` lies strictly above `lam α`. -/
lemma b2_countAbove_le_one {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n))
    (hα0 : 0 < α) (hα1 : α < 1) (hMpsd : (graphMatrix α G).PosSemidef) :
    countAbove (G.adjMatrix ℝ) (adjMatrix_isHermitian G) (lam α) ≤ 1 := by
  classical
  by_contra hnot
  have hnot' : ¬ Fintype.card {i : Fin n // (lam α) < (adjMatrix_isHermitian G).eigenvalues i} ≤ 1 := by
    change ¬ countAbove (G.adjMatrix ℝ) (adjMatrix_isHermitian G) (lam α) ≤ 1
    exact hnot
  have hge : 2 ≤ Fintype.card {i : Fin n // (lam α) < (adjMatrix_isHermitian G).eigenvalues i} := by omega
  have hone : 1 < Fintype.card {i : Fin n // (lam α) < (adjMatrix_isHermitian G).eigenvalues i} := by omega
  rcases Fintype.exists_pair_of_one_lt_card (α := {i : Fin n // (lam α) < (adjMatrix_isHermitian G).eigenvalues i}) hone with ⟨a, b, hab⟩
  let i : Fin n := a.1
  let j : Fin n := b.1
  have hij : i ≠ j := by
    intro heq
    apply hab
    apply Subtype.ext
    simpa [i, j] using heq
  have hi : (lam α) < (adjMatrix_isHermitian G).eigenvalues i := by
    simpa [i] using a.2
  have hj : (lam α) < (adjMatrix_isHermitian G).eigenvalues j := by
    simpa [j] using b.2
  let v : Fin n → ℝ := (adjMatrix_isHermitian G).eigenvectorBasis i |>.ofLp
  let w : Fin n → ℝ := (adjMatrix_isHermitian G).eigenvectorBasis j |>.ofLp
  have hcontra : ∀ (p q : ℝ), (p ≠ 0 ∨ q ≠ 0) →
      (∑ k : Fin n, (p • v + q • w) k) = 0 → False := by
    intro p q hpq hsum
    let z : Fin n → ℝ := p • v + q • w
    have hnorm : z ⬝ᵥ z = p ^ 2 + q ^ 2 := by
      dsimp [z]
      exact normSq_lincomb_eigen (A := G.adjMatrix ℝ) (hA := adjMatrix_isHermitian G) (hij := hij) p q
    have hquad : z ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ z) = p ^ 2 * (adjMatrix_isHermitian G).eigenvalues i
        + q ^ 2 * (adjMatrix_isHermitian G).eigenvalues j := by
      dsimp [z]
      exact quad_lincomb_eigen (A := G.adjMatrix ℝ) (hA := adjMatrix_isHermitian G) (hij := hij) p q
    have hsum0 : (∑ k : Fin n, z k) = 0 := by
      simpa [z] using hsum
    have hzle : z ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ z) ≤ (lam α) * (z ⬝ᵥ z) := by
      have hq0 := graphMatrix_quad_nonneg G hMpsd z
      have hq := graphMatrix_quad (α := α) G z
      rw [hq] at hq0
      rw [hsum0] at hq0
      norm_num at hq0
      linarith
    have hgt : (lam α) * (z ⬝ᵥ z) < z ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ z) := by
      rw [hnorm, hquad]
      have hma : 0 < (adjMatrix_isHermitian G).eigenvalues i - lam α := by
        linarith
      have hmb : 0 < (adjMatrix_isHermitian G).eigenvalues j - lam α := by
        linarith
      have hmain : 0 < p ^ 2 * ((adjMatrix_isHermitian G).eigenvalues i - lam α)
          + q ^ 2 * ((adjMatrix_isHermitian G).eigenvalues j - lam α) := by
        rcases hpq with hpn | hqn
        · have h1 : 0 < p ^ 2 * ((adjMatrix_isHermitian G).eigenvalues i - lam α) :=
            mul_pos (sq_pos_of_ne_zero hpn) hma
          have h2 : 0 ≤ q ^ 2 * ((adjMatrix_isHermitian G).eigenvalues j - lam α) :=
            mul_nonneg (sq_nonneg q) (le_of_lt hmb)
          nlinarith
        · have h1 : 0 ≤ p ^ 2 * ((adjMatrix_isHermitian G).eigenvalues i - lam α) :=
            mul_nonneg (sq_nonneg p) (le_of_lt hma)
          have h2 : 0 < q ^ 2 * ((adjMatrix_isHermitian G).eigenvalues j - lam α) :=
            mul_pos (sq_pos_of_ne_zero hqn) hmb
          nlinarith
      nlinarith
    linarith
  by_cases hv0 : (∑ k : Fin n, v k) = 0
  · have hsum : (∑ k : Fin n, ((1 : ℝ) • v + (0 : ℝ) • w) k) = 0 := by
      simpa [hv0]
    exact hcontra 1 0 (Or.inl (by norm_num)) hsum
  · have hsum : (∑ k : Fin n, ((∑ t : Fin n, w t) • v + (-(∑ t : Fin n, v t)) • w) k) = 0 := by
      calc
        (∑ k : Fin n, ((∑ t : Fin n, w t) • v + (-(∑ t : Fin n, v t)) • w) k)
            = (∑ t : Fin n, w t) * (∑ k : Fin n, v k) + (-(∑ t : Fin n, v t)) * (∑ k : Fin n, w k) := by
                simpa using (sum_add_smul (ι := Fin n) (∑ t : Fin n, w t) (-(∑ t : Fin n, v t)) v w)
        _ = 0 := by ring
    exact hcontra (∑ t : Fin n, w t) (-(∑ t : Fin n, v t)) (Or.inr (neg_ne_zero.mpr hv0)) hsum

/-- an eigenvector of `A` with value `ν` makes `ν` a member of the spectrum. -/
lemma eigenvector_mem_spectrum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (ν : ℝ) (x : ι → ℝ) (hx0 : x ≠ 0)
    (hAx : A *ᵥ x = ν • x) : ν ∈ spectrum ℝ A := by
  classical
  exact eigen_mem_spectrum A hx0 hAx

/-- if `ν` is an eigenvalue value (has an eigenvector) then `ENNReal.ofReal ν` is at most
the spectral radius. -/
lemma ofReal_le_spectralRadius_of_eigenvector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (ν : ℝ) (x : ι → ℝ) (hx0 : x ≠ 0)
    (hAx : A *ᵥ x = ν • x) : ENNReal.ofReal ν ≤ spectralRadius ℝ A := by
  classical
  have hmem : ν ∈ spectrum ℝ A := eigenvector_mem_spectrum A ν x hx0 hAx
  have hval : ENNReal.ofReal |ν| = ((‖ν‖₊ : NNReal) : ENNReal) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg ν)]
    rfl
  have hb : ((‖ν‖₊ : NNReal) : ENNReal) ≤ spectralRadius ℝ A := by
    unfold spectralRadius
    exact le_trans
      (le_iSup (fun _ : ν ∈ spectrum ℝ A => ((‖ν‖₊ : NNReal) : ENNReal)) hmem)
      (le_iSup (fun k : ℝ => ⨆ _ : k ∈ spectrum ℝ A, ((‖k‖₊ : NNReal) : ENNReal)) ν)
  calc
    ENNReal.ofReal ν ≤ ENNReal.ofReal |ν| := ENNReal.ofReal_mono (le_abs_self ν)
    _ = ((‖ν‖₊ : NNReal) : ENNReal) := hval
    _ ≤ spectralRadius ℝ A := hb

/-- if `x ∈ ker(lam0I − A_G)` restricts nontrivially to component `c`, then
`ofReal lam0 ≤ ρ(A_c)`. -/
lemma compRest_nonzero_of {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent)
    {lam0 : ℝ} (x : Fin n → ℝ)
    (hx : ((lam0 • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ) *ᵥ x) = 0)
    (hx0 : compRest G c x ≠ 0) :
    ENNReal.ofReal lam0 ≤ spectralRadius ℝ (compAdj G c) := by
  classical
  let w : c → ℝ := compRest G c x
  have hwne : w ≠ 0 := by
    simpa [w] using hx0
  have hwk : ((lam0 • (1 : Matrix c c ℝ) - compAdj G c) *ᵥ w) = 0 := by
    have hk := compRest_ker_comp G c (lam0 := lam0) (x := x) hx
    simpa [w] using hk
  have hAw : (compAdj G c) *ᵥ w = lam0 • w := by
    have hlin : lam0 • w - (compAdj G c) *ᵥ w = 0 := by
      simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hwk
    exact (sub_eq_zero.mp hlin).symm
  exact ofReal_le_spectralRadius_of_eigenvector (compAdj G c) lam0 w hwne hAw

/-- A `ρ0`-eigenvector of `A_G` with ρ(A_G) = ofReal ρ0 restricts nontrivially to some
component of spectral radius ρ0. -/
lemma exists_component_spectralRadius_eq {n : ℕ} (G : SimpleGraph (Fin n))
    {ρ0 : ℝ} (hρ0 : 0 < ρ0)
    (hρG : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal ρ0)
    (x : Fin n → ℝ) (hx0 : x ≠ 0)
    (hAx : (G.adjMatrix ℝ) *ᵥ x = ρ0 • x) :
    ∃ c : G.ConnectedComponent,
      spectralRadius ℝ (compAdj G c) = ENNReal.ofReal ρ0 := by
  classical
  have hex : ∃ v : Fin n, x v ≠ 0 := by
    by_contra h
    apply hx0
    funext v
    by_contra hx
    exact h ⟨v, hx⟩
  rcases hex with ⟨v0, hx0v⟩
  let c0 : G.ConnectedComponent := G.connectedComponentMk v0
  have hv0mem : v0 ∈ c0.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  refine ⟨c0, ?_⟩
  apply le_antisymm
  · calc
      spectralRadius ℝ (compAdj G c0) ≤ spectralRadius ℝ (G.adjMatrix ℝ) := compRho_le G c0
      _ = ENNReal.ofReal ρ0 := hρG
  · have hxker : ((ρ0 • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ) *ᵥ x) = 0 := by
      rw [mulVec_sub_any]
      rw [sub_eq_zero]
      funext i
      have hsc : ((ρ0 • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x) i = ρ0 * x i := by
        simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.one_apply, Finset.sum_ite_eq]
      have hc := congrFun hAx i
      exact hsc.trans (by simpa [Pi.smul_apply] using hc.symm)
    have hres_ne : compRest G c0 x ≠ 0 := by
      intro h
      have hc : x v0 = 0 := by
        simpa [compRest] using congrFun h ⟨v0, hv0mem⟩
      exact hx0v hc
    exact compRest_nonzero_of G c0 (lam0 := ρ0) x hxker hres_ne

/-- sum of an extension over the whole graph equals the sum over the component -/
lemma sum_compExt {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) (u : c → ℝ) :
    (∑ k : Fin n, compExt G c u k) = ∑ i : c, u i := by
  classical
  let T : Finset (Fin n) := (Finset.univ : Finset c).image (fun w : c => w.1)
  have hzero : ∀ k : Fin n, k ∉ T → compExt G c u k = 0 := by
    intro k hkT
    have hks : k ∉ c.supp := by
      intro hks
      apply hkT
      exact Finset.mem_image.mpr ⟨⟨k, hks⟩, Finset.mem_univ _, rfl⟩
    exact compExt_apply_not_mem G c u hks
  have hsub := Finset.sum_subset (s₁ := T) (s₂ := Finset.univ) (f := fun k : Fin n => compExt G c u k)
    (by intro k hk; exact Finset.mem_univ k)
    (by intro k hk hkT; exact hzero k hkT)
  calc
    (∑ k : Fin n, compExt G c u k) = ∑ k ∈ T, compExt G c u k := hsub.symm
    _ = ∑ w : c, compExt G c u w.1 := by
          exact Finset.sum_image (f := fun k : Fin n => compExt G c u k) (s := Finset.univ)
            (g := fun w : c => w.1) (by
              intro x hx y hy hxy
              exact Subtype.ext hxy)
    _ = ∑ w : c, u w := by
          apply Finset.sum_congr rfl
          intro w hw
          exact compExt_apply_mem G c u w.2

/-- square-norm of an extension equals the sum of squares over the component -/
lemma normSq_compExt {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) (u : c → ℝ) :
    (compExt G c u) ⬝ᵥ (compExt G c u) = ∑ i : c, u i ^ 2 := by
  classical
  calc
    (compExt G c u) ⬝ᵥ (compExt G c u) = ∑ k : Fin n, (compExt G c u k) ^ 2 := by
          simp [dotProduct, pow_two]
    _ = ∑ k : Fin n, compExt G c (fun i : c => (u i) ^ 2) k := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases h : k ∈ c.supp
          · simp [compExt_apply_mem G c u h, compExt_apply_mem G c (fun i => (u i) ^ 2) h]
          · simp [compExt_apply_not_mem G c u h, compExt_apply_not_mem G c (fun i => (u i) ^ 2) h]
    _ = ∑ i : c, (u i) ^ 2 := by
          exact sum_compExt G c (fun i : c => (u i) ^ 2)

/-- extensions of two different components have disjoint support, so zero dot product -/
lemma compExt_dot_compExt_of_ne {n : ℕ} (G : SimpleGraph (Fin n)) (c d : G.ConnectedComponent)
    (hcd : c ≠ d) (u : c → ℝ) (v : d → ℝ) :
    (compExt G c u) ⬝ᵥ (compExt G d v) = 0 := by
  classical
  rw [dotProduct]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hc : k ∈ c.supp
  · have hdn : k ∉ d.supp := by
      intro hd
      apply hcd
      exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hc hd
    rw [compExt_apply_mem G c u hc, compExt_apply_not_mem G d v hdn]
    ring
  · rw [compExt_apply_not_mem G c u hc]
    ring

/-- an eigenvector of a component adjacency extends to an eigenvector of the whole graph -/
lemma compExt_eigenvector {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent)
    {μ : ℝ} {u : c → ℝ} (hu : (compAdj G c) *ᵥ u = μ • u) :
    (G.adjMatrix ℝ) *ᵥ (compExt G c u) = μ • (compExt G c u) := by
  classical
  funext w
  by_cases hw : w ∈ c.supp
  · have hres : compRest G c (compExt G c u) = u := by
      funext v
      simp [compRest, compExt_apply_mem G c u v.2]
    have hadj := adj_restrict_mem G c (compExt G c u) ⟨w, hw⟩
    calc
      ((G.adjMatrix ℝ) *ᵥ compExt G c u) w
          = ((cGraph G c).adjMatrix ℝ *ᵥ compRest G c (compExt G c u)) ⟨w, hw⟩ := hadj
      _ = ((cGraph G c).adjMatrix ℝ *ᵥ u) ⟨w, hw⟩ := by rw [hres]
      _ = (μ • u) ⟨w, hw⟩ := by
            have h := congrFun hu ⟨w, hw⟩
            simpa [compAdj] using h
      _ = (μ • compExt G c u) w := by
            simp [compExt_apply_mem G c u hw, Pi.smul_apply]
  · have hz : ((G.adjMatrix ℝ) *ᵥ compExt G c u) w = 0 := adj_compExt_outside G c u hw
    rw [hz]
    simp [compExt_apply_not_mem G c u hw, Pi.smul_apply]

/-- norm-squared of a linear combination of two orthogonal vectors -/
lemma normSq_two {ι : Type*} [Fintype ι] (x y : ι → ℝ) (hxy : x ⬝ᵥ y = 0) (a b : ℝ) :
    (a • x + b • y) ⬝ᵥ (a • x + b • y) = a ^ 2 * (x ⬝ᵥ x) + b ^ 2 * (y ⬝ᵥ y) := by
  classical
  have hyx : y ⬝ᵥ x = 0 := by
    rw [dotProduct_comm]
    exact hxy
  have h1 : (a • x) ⬝ᵥ (a • x + b • y) + (b • y) ⬝ᵥ (a • x + b • y)
      = a * (a * (x ⬝ᵥ x) + b * (x ⬝ᵥ y)) + b * (a * (y ⬝ᵥ x) + b * (y ⬝ᵥ y)) := by
    rw [dotProduct_smul_left_pf, dotProduct_smul_left_pf]
    rw [dotProduct_add, dotProduct_add]
    rw [dotProduct_smul_right_pf, dotProduct_smul_right_pf, dotProduct_smul_right_pf, dotProduct_smul_right_pf]
  calc
    (a • x + b • y) ⬝ᵥ (a • x + b • y)
        = (a • x) ⬝ᵥ (a • x + b • y) + (b • y) ⬝ᵥ (a • x + b • y) := by
            rw [dotProduct_add_left_pf]
    _ = a * (a * (x ⬝ᵥ x) + b * (x ⬝ᵥ y)) + b * (a * (y ⬝ᵥ x) + b * (y ⬝ᵥ y)) := h1
    _ = a ^ 2 * (x ⬝ᵥ x) + b ^ 2 * (y ⬝ᵥ y) := by
            rw [hxy, hyx]
            ring

/-- quadratic form of a linear combination of two eigenvectors (of any matrix A) -/
lemma quad_two {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x y : ι → ℝ) (p q : ℝ)
    (hAx : A *ᵥ x = p • x) (hAy : A *ᵥ y = q • y) (hxy : x ⬝ᵥ y = 0) (a b : ℝ) :
    (a • x + b • y) ⬝ᵥ (A *ᵥ (a • x + b • y)) = a ^ 2 * p * (x ⬝ᵥ x) + b ^ 2 * q * (y ⬝ᵥ y) := by
  classical
  have hyx : y ⬝ᵥ x = 0 := by
    rw [dotProduct_comm]
    exact hxy
  have hlin : A *ᵥ (a • x + b • y) = (a * p) • x + (b * q) • y := by
    rw [Matrix.mulVec_add]
    rw [Matrix.mulVec_smul]
    rw [Matrix.mulVec_smul]
    rw [hAx, hAy]
    funext k
    simp [Pi.smul_apply]
    ring
  have h1 : (a • x) ⬝ᵥ ((a * p) • x + (b * q) • y) + (b • y) ⬝ᵥ ((a * p) • x + (b * q) • y)
      = a * ((a * p) * (x ⬝ᵥ x) + (b * q) * (x ⬝ᵥ y))
        + b * ((a * p) * (y ⬝ᵥ x) + (b * q) * (y ⬝ᵥ y)) := by
    rw [dotProduct_smul_left_pf, dotProduct_smul_left_pf]
    rw [dotProduct_add, dotProduct_add]
    rw [dotProduct_smul_right_pf, dotProduct_smul_right_pf, dotProduct_smul_right_pf, dotProduct_smul_right_pf]
  calc
    (a • x + b • y) ⬝ᵥ (A *ᵥ (a • x + b • y))
        = (a • x + b • y) ⬝ᵥ ((a * p) • x + (b * q) • y) := by rw [hlin]
    _ = (a • x) ⬝ᵥ ((a * p) • x + (b * q) • y) + (b • y) ⬝ᵥ ((a * p) • x + (b * q) • y) := by
            rw [dotProduct_add_left_pf]
    _ = a * ((a * p) * (x ⬝ᵥ x) + (b * q) * (x ⬝ᵥ y))
        + b * ((a * p) * (y ⬝ᵥ x) + (b * q) * (y ⬝ᵥ y)) := h1
    _ = a ^ 2 * p * (x ⬝ᵥ x) + b ^ 2 * q * (y ⬝ᵥ y) := by
            rw [hxy, hyx]
            ring


/-- With `c0` a component of spectral radius ρ0 > λ, every other component has spectral
radius `< ofReal λ`.  (PF mixing via `M ⪰ 0`.) -/
lemma b2_other_components_rho_lt {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n))
    (hα0 : 0 < α) (hα1 : α < 1)
    (hMpsd : (graphMatrix α G).PosSemidef)
    {ρ0 : ℝ} (hlr0 : lam α < ρ0)
    (c0 : G.ConnectedComponent)
    (hc0 : spectralRadius ℝ (compAdj G c0) = ENNReal.ofReal ρ0)
    (c' : G.ConnectedComponent) (hc'ne : c' ≠ c0) :
    spectralRadius ℝ (compAdj G c') < ENNReal.ofReal (lam α) := by
  classical
  by_contra hnot
  have hlρ : ENNReal.ofReal (lam α) ≤ spectralRadius ℝ (compAdj G c') := le_of_not_gt hnot
  -- top eigenvalue of the component c'
  have hAc' : (compAdj G c').IsHermitian := compAdj_isHermitian G c'
  have hnn : ∀ i j : c', 0 ≤ (compAdj G c') i j := compAdj_nonneg G c'
  have hcard : 0 < Fintype.card c' := compCard_pos G c'
  rcases exists_top_eigenvalue_index_any (compAdj G c') hAc' hcard with ⟨i0, hi0⟩
  let μ : ℝ := hAc'.eigenvalues i0
  have hmu_ge_abs : ∀ j : c', |hAc'.eigenvalues j| ≤ μ := by
    intro j
    simpa [μ] using (top_eigenvalue_ge_abs_any (compAdj G c') hAc' hnn hcard i0 hi0 j)
  have hmu0 : 0 ≤ μ := by
    have hle : |μ| ≤ μ := by
      simpa [μ] using (hmu_ge_abs i0)
    have hme : μ ≤ |μ| := le_abs_self μ
    have habs : |μ| = μ := le_antisymm hle hme
    rw [← habs]
    exact abs_nonneg μ
  -- ρ(A_{c'}) ≤ ofReal μ  (each spectrum element has |·| ≤ μ)
  have hρle : spectralRadius ℝ (compAdj G c') ≤ ENNReal.ofReal μ := by
    unfold spectralRadius
    refine iSup_le (fun ν => ?_)
    refine iSup_le (fun hν => ?_)
    rcases exists_eigenvalue_of_mem_spectrum_any (compAdj G c') hAc' hν with ⟨j, hj⟩
    have hνμ : |ν| ≤ μ := by
      rw [← hj]
      exact hmu_ge_abs j
    have h1 : ENNReal.ofReal |ν| = ((‖ν‖₊ : NNReal) : ENNReal) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg ν)]
      rfl
    rw [← h1]
    exact (ENNReal.ofReal_le_ofReal_iff hmu0).mpr hνμ
  -- ofReal μ ≤ ρ(A_{c'})
  have hμρ : ENNReal.ofReal μ ≤ spectralRadius ℝ (compAdj G c') := by
    have h := spectralRadius_ge_eigenvalue_any (compAdj G c') hAc' i0
    have hmu0' : 0 ≤ hAc'.eigenvalues i0 := by simpa [μ] using hmu0
    have ha : |hAc'.eigenvalues i0| = hAc'.eigenvalues i0 := abs_of_nonneg hmu0'
    rwa [ha] at h
  have hρeq : spectralRadius ℝ (compAdj G c') = ENNReal.ofReal μ := le_antisymm hρle hμρ
  -- l ≤ μ
  have hle_l : lam α ≤ μ := by
    have h1 : ENNReal.ofReal (lam α) ≤ ENNReal.ofReal μ := by
      rwa [hρeq] at hlρ
    exact (ENNReal.ofReal_le_ofReal_iff hmu0).mp h1
  have hμpos : 0 < μ := lt_of_lt_of_le (lam_pos hα0 hα1) hle_l
  -- PF eigenvector of c' with eigenvalue μ
  rcases nonneg_eigenvector_of_spectralRadius_any (hn := compCard_pos G c') (compAdj G c') hAc' hnn
    hμpos hρeq with ⟨uc, hucnn, hucsum, huceig⟩
  -- PF eigenvector of c0 with eigenvalue ρ0
  have hρ0pos : 0 < ρ0 := lt_trans (lam_pos hα0 hα1) hlr0
  rcases nonneg_eigenvector_of_spectralRadius_any (hn := compCard_pos G c0) (compAdj G c0)
    (compAdj_isHermitian G c0) (compAdj_nonneg G c0) hρ0pos hc0 with ⟨u0, hu0nn, hu0sum, hu0eig⟩
  -- mixing data
  let U0 : Fin n → ℝ := compExt G c0 u0
  let U : Fin n → ℝ := compExt G c' uc
  let sv : ℝ := ∑ i : c0, u0 i
  let sw : ℝ := ∑ i : c', uc i
  have hsumU0 : (∑ k : Fin n, U0 k) = sv := by
    dsimp [U0, sv]
    exact sum_compExt G c0 u0
  have hsumU : (∑ k : Fin n, U k) = sw := by
    dsimp [U, sw]
    exact sum_compExt G c' uc
  have hsvpos : 0 < sv := by dsimp [sv]; exact hu0sum
  have hswpos : 0 < sw := by dsimp [sw]; exact hucsum
  have hA0 : (G.adjMatrix ℝ) *ᵥ U0 = ρ0 • U0 := by
    simpa [U0] using (compExt_eigenvector G c0 hu0eig)
  have hAc : (G.adjMatrix ℝ) *ᵥ U = μ • U := by
    simpa [U] using (compExt_eigenvector G c' huceig)
  have hN0 : U0 ⬝ᵥ U0 = ∑ i : c0, u0 i ^ 2 := by
    dsimp [U0]
    exact normSq_compExt G c0 u0
  have hN : U ⬝ᵥ U = ∑ i : c', uc i ^ 2 := by
    dsimp [U]
    exact normSq_compExt G c' uc
  have hcross : U0 ⬝ᵥ U = 0 := by
    simpa [U0, U] using (compExt_dot_compExt_of_ne G c0 c' (Ne.symm hc'ne) u0 uc)
  -- N0 > 0
  have hN0pos : 0 < U0 ⬝ᵥ U0 := by
    rw [hN0]
    have hpos_coord : ∃ i : c0, 0 < u0 i := by
      by_contra hnot2
      have hall : ∀ i : c0, u0 i = 0 := by
        intro i
        by_contra hne
        have hpos : 0 < u0 i := lt_of_le_of_ne (hu0nn i) (Ne.symm hne)
        exact hnot2 ⟨i, hpos⟩
      have hz : (∑ i : c0, u0 i) = 0 := by simp [hall]
      have hsumpos : 0 < (∑ i : c0, u0 i) := by simpa [sv] using hsvpos
      linarith
    rcases hpos_coord with ⟨i0c, hi0pos⟩
    refine Finset.sum_pos' ?_ ?_
    · intro i hi
      exact sq_nonneg (u0 i)
    · exact ⟨i0c, Finset.mem_univ i0c, sq_pos_of_ne_zero (ne_of_gt hi0pos)⟩
  -- w := sw • U0 + (-sv) • U
  let w : Fin n → ℝ := sw • U0 + (-sv) • U
  have hsumw : (∑ k : Fin n, w k) = 0 := by
    dsimp [w]
    calc
      (∑ k : Fin n, (sw • U0 + (-sv) • U) k)
          = sw * (∑ k : Fin n, U0 k) + (-sv) * (∑ k : Fin n, U k) := by
              simpa using (sum_add_smul (ι := Fin n) sw (-sv) U0 U)
      _ = sw * sv + (-sv) * sw := by rw [hsumU0, hsumU]
      _ = 0 := by ring
  have hnormw : w ⬝ᵥ w = sw ^ 2 * (U0 ⬝ᵥ U0) + sv ^ 2 * (U ⬝ᵥ U) := by
    dsimp [w]
    have h := normSq_two U0 U hcross sw (-sv)
    -- h: (sw•U0 + (-sv)•U)⬝(sw•U0 + (-sv)•U) = sw^2*(U0⬝U0) + (-sv)^2*(U⬝U)
    rw [h]
    ring
  have hquadw : w ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ w)
      = sw ^ 2 * ρ0 * (U0 ⬝ᵥ U0) + sv ^ 2 * μ * (U ⬝ᵥ U) := by
    dsimp [w]
    have h := quad_two (G.adjMatrix ℝ) U0 U ρ0 μ hA0 hAc hcross sw (-sv)
    rw [h]
    ring
  -- E(w) = w⬝Mw < 0
  have hEneg : w ⬝ᵥ (graphMatrix α G *ᵥ w) < 0 := by
    have hρ0ml : 0 < ρ0 - lam α := by linarith
    have hμml : 0 ≤ μ - lam α := by linarith
    -- bracket positivity
    have hbig : 0 < sw ^ 2 * (ρ0 - lam α) * (U0 ⬝ᵥ U0) := by
      have hsw2 : 0 < sw ^ 2 := sq_pos_of_ne_zero (ne_of_gt hswpos)
      have h1 : 0 < sw ^ 2 * (ρ0 - lam α) := mul_pos hsw2 hρ0ml
      exact mul_pos h1 hN0pos
    have hNge : 0 ≤ U ⬝ᵥ U := by
      rw [hN]
      exact Finset.sum_nonneg (fun i hi => sq_nonneg (uc i))
    have hrest : 0 ≤ sv ^ 2 * (μ - lam α) * (U ⬝ᵥ U) := by
      have hsv2 : 0 ≤ sv ^ 2 := sq_nonneg sv
      have h12 : 0 ≤ sv ^ 2 * (μ - lam α) := mul_nonneg hsv2 hμml
      exact mul_nonneg h12 hNge
    calc
      w ⬝ᵥ (graphMatrix α G *ᵥ w)
          = (lam α) * (w ⬝ᵥ w) - w ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ w) + (1 / 2 : ℝ) * (∑ k : Fin n, w k)^2 := by
              rw [graphMatrix_quad]
      _ = (lam α) * (sw ^ 2 * (U0 ⬝ᵥ U0) + sv ^ 2 * (U ⬝ᵥ U))
          - (sw ^ 2 * ρ0 * (U0 ⬝ᵥ U0) + sv ^ 2 * μ * (U ⬝ᵥ U)) := by
              rw [hnormw, hquadw, hsumw]
              norm_num
      _ < 0 := by
              have hrewrite : (lam α) * (sw ^ 2 * (U0 ⬝ᵥ U0) + sv ^ 2 * (U ⬝ᵥ U))
                  - (sw ^ 2 * ρ0 * (U0 ⬝ᵥ U0) + sv ^ 2 * μ * (U ⬝ᵥ U))
                  = -(sw ^ 2 * (ρ0 - lam α) * (U0 ⬝ᵥ U0) + sv ^ 2 * (μ - lam α) * (U ⬝ᵥ U)) := by
                    ring
              rw [hrewrite]
              linarith
  -- PSD gives ≥ 0; contradiction
  have hEge : 0 ≤ w ⬝ᵥ (graphMatrix α G *ᵥ w) := graphMatrix_quad_nonneg G hMpsd w
  linarith


/-- every `x ∈ ker(lam α I − A_G)` restricts to a kernel vector of `lam α I − A_{c0}`. -/
lemma b2_ker_restricts {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n))
    (hα0 : 0 < α) (hα1 : α < 1)
    (hMpsd : (graphMatrix α G).PosSemidef)
    {ρ0 : ℝ} (hlr0 : lam α < ρ0)
    (c0 : G.ConnectedComponent)
    (hc0 : spectralRadius ℝ (compAdj G c0) = ENNReal.ofReal ρ0)
    (x : Fin n → ℝ)
    (hx : ((lam α • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ) *ᵥ x) = 0) :
    ((lam α • (1 : Matrix c0 c0 ℝ) - compAdj G c0) *ᵥ compRest G c0 x) = 0 := by
  classical
  exact compRest_ker_comp G c0 (lam0 := lam α) (x := x) hx

/-- if a kernel vector restricts to a component whose spectral radius is below lam0,
the restriction is zero -/
lemma compRest_zero_of_rho_lt {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent)
    {lam0 : ℝ} (x : Fin n → ℝ)
    (hx : ((lam0 • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ) *ᵥ x) = 0)
    (hlt : spectralRadius ℝ (compAdj G c) < ENNReal.ofReal lam0) :
    compRest G c x = 0 := by
  classical
  by_contra hx0
  exact (not_lt_of_ge (compRest_nonzero_of G c x hx hx0)) hlt


/-- main dev: b2_nullity_le_component -/
lemma b2_nullity_le_component {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n))
    (hα0 : 0 < α) (hα1 : α < 1)
    (hMpsd : (graphMatrix α G).PosSemidef)
    {ρ0 : ℝ} (hlr0 : lam α < ρ0)
    (c0 : G.ConnectedComponent)
    (hc0 : spectralRadius ℝ (compAdj G c0) = ENNReal.ofReal ρ0) :
    Module.finrank ℝ (LinearMap.ker
        ((lam α • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ).mulVecLin))
      ≤ Module.finrank ℝ (LinearMap.ker
        ((lam α • (1 : Matrix c0 c0 ℝ) - compAdj G c0).mulVecLin)) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := (lam α) • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
  let B0 : Matrix c0 c0 ℝ := (lam α) • (1 : Matrix c0 c0 ℝ) - compAdj G c0
  let K : Submodule ℝ (Fin n → ℝ) := LinearMap.ker B.mulVecLin
  let K0 : Submodule ℝ (c0 → ℝ) := LinearMap.ker B0.mulVecLin
  let res : (Fin n → ℝ) →ₗ[ℝ] (c0 → ℝ) :=
    { toFun := compRest G c0
      map_add' := by intro x y; funext v; rfl
      map_smul' := by intro a x; funext v; rfl }
  let Gmap : K →ₗ[ℝ] (c0 → ℝ) := res.comp K.subtype
  have hker0G : ∀ w : K, Gmap w = 0 → w = 0 := by
    intro w hw
    apply Subtype.ext
    funext v
    let c := G.connectedComponentMk v
    have hv : v ∈ c.supp := by
      simp [c, SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hBw : B *ᵥ w.1 = 0 := w.2
    have hres0 : res w.1 = 0 := by
      simpa [Gmap] using hw
    by_cases hceq : c = c0
    · have hval := congrFun hres0 ⟨v, (by rw [hceq] at hv; exact hv)⟩
      simpa [res, compRest] using hval
    · have hltc : spectralRadius ℝ (compAdj G c) < ENNReal.ofReal (lam α) :=
        b2_other_components_rho_lt G hα0 hα1 hMpsd hlr0 c0 hc0 c hceq
      have hzc : compRest G c w.1 = 0 :=
        compRest_zero_of_rho_lt G c w.1 (by simpa [B] using hBw) hltc
      simpa [compRest] using congrFun hzc ⟨v, hv⟩
  have hGinj : Function.Injective Gmap := by
    intro x y hxy
    apply Subtype.ext
    let w : K := x - y
    have hGw : Gmap w = 0 := by
      change Gmap (x - y) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    have hw0 : w = 0 := hker0G w hGw
    have hd : x.1 - y.1 = 0 := by simpa [w] using congrArg (fun q : K => q.1) hw0
    exact sub_eq_zero.mp hd
  have hmem : ∀ w : K, Gmap w ∈ K0 := by
    intro w
    have hx : B *ᵥ w.1 = 0 := w.2
    have hk := b2_ker_restricts G hα0 hα1 hMpsd hlr0 c0 hc0 w.1 (by simpa [B] using hx)
    refine LinearMap.mem_ker.mpr ?_
    change B0 *ᵥ (compRest G c0 w.1) = 0
    simpa [B0] using hk
  let F : K →ₗ[ℝ] K0 := Gmap.codRestrict K0 hmem
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply hGinj
    have h' := congrArg (fun q : K0 => q.1) hxy
    simpa [F] using h'
  have hle := LinearMap.finrank_le_finrank_of_injective (f := F) hFinj
  simpa [K, K0, B, B0] using hle



end
end Submission
