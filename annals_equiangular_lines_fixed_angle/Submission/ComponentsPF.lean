import Submission.Perron
import Submission.PfExtra
import Submission.GraphSpec
import Submission.Eigen
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Finite.Basic

open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option autoImplicit false
set_option maxHeartbeats 1200000

attribute [local instance] Classical.propDecidable

noncomputable section

/-! # Generic (arbitrary finite index type) versions of the Perron--Frobenius lemmas

The lemmas in Perron.lean / PfExtra.lean / GraphSpec.lean / Eigen.lean are stated for
`Fin n`-indexed matrices and graphs.  This file restates the needed ones for an arbitrary
finite index type `ι : Type*` with `[Fintype ι]`.  (Mathlib's Hermitian spectral theory
`Matrix.IsHermitian.eigenvalues`, `eigenvectorBasis`, `spectral_theorem`,
`mem_spectrum_iff_isRoot_charpoly` is already generic in the index type, so transposing the
proofs is mechanical: replace every `(Fin n)` by `ι`, `n` by `Fintype.card ι` where relevant,
and sums `∑ j : Fin n` by `∑ j : ι`.)

PROVE ALL of the lemmas below with complete proofs (no placeholders).  You may add any auxiliary generic lemmas you
need.  READ the corresponding proofs in:
  - Submission/Perron.lean   (spectral radius facts, nonneg eigenvector of spectral radius)
  - Submission/PfExtra.lean  (psd_ker_of_quad_zero, quad_abs_ge, dotProduct_abs_self,
                              nonneg_eigenvector_of_spectralRadius)
  - Submission/GraphSpec.lean (Perron--Frobenius for connected graphs: eigenspace spanned by
                              a positive eigenvector)
  - Submission/Eigen.lean    (charpoly_sub_self, sub_psd_of_spectralRadius,
                              sub_psd_of_eigenvalues_le)
and transpose each proof to `ι`.  Dependencies: transpose in dependency order (e.g.
`charpoly_sub_self_any` before `sub_psd_of_eigenvalues_le_any`; `eigenvector_dotProduct_self_any`
needed by `nonneg_eigenvector_of_spectralRadius_any`, ...).  A convenient way: prove each
generic lemma BY TRANSPORT through `Fintype.equivFin` if transposition is painful, but direct
transposition is usually easier.  Note: `hA.eigenvalues : ι → ℝ` needs `[DecidableEq ι]`; add
`[DecidableEq ι]` as an explicit parameter where the eigenvalue statements are used.  Do not
change the statements below.  Good luck!
-/


/-- Generic: `(B - C) *ᵥ v = B *ᵥ v - C *ᵥ v` for any index type. -/
lemma mulVec_sub_pf {ι : Type*} [Fintype ι] (B C : Matrix ι ι ℝ) (v : ι → ℝ) :
    (B - C) *ᵥ v = B *ᵥ v - C *ᵥ v := by
  classical
  rw [Matrix.sub_mulVec]

/-- Generic: `(s • 1) *ᵥ v = s • v` for any index type. -/
lemma mulVec_smul_one_pf {ι : Type*} [Fintype ι] (s : ℝ) (v : ι → ℝ) :
    (s • (1 : Matrix ι ι ℝ)) *ᵥ v = s • v := by
  classical
  ext i
  simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.one_apply, Finset.sum_ite_eq]

/-- dot product is ℝ-linear in the second argument for scalars, generic index. -/
lemma dotProduct_smul_right_pf {ι : Type*} [Fintype ι] (c : ℝ) (u v : ι → ℝ) :
    u ⬝ᵥ (c • v) = c * (u ⬝ᵥ v) := by
  simp [dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

/-- dot product is ℝ-linear in the first argument for scalars, generic index. -/
lemma dotProduct_smul_left_pf {ι : Type*} [Fintype ι] (c : ℝ) (u v : ι → ℝ) :
    (c • u) ⬝ᵥ v = c * (u ⬝ᵥ v) := by
  classical
  simp [dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- dot product is ℝ-linear in the first argument for addition, generic index. -/
lemma dotProduct_add_left_pf {ι : Type*} [Fintype ι] (u v w : ι → ℝ) :
    (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w := by
  simp [dotProduct, Finset.sum_add_distrib, add_mul]

/-- real Hermitian matrices have symmetric entries, generic index. -/
lemma hermitian_entries_symm_pf {ι : Type*} (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (i j : ι) : A i j = A j i := by
  have h := congrFun (congrFun hA.eq i) j
  simpa [Matrix.conjTranspose_apply] using h.symm

/-- dot products with a real symmetric matrix commute with the matrix, generic index. -/
lemma dotProduct_mulVec_symm_pf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (hAsym : ∀ i j : ι, A i j = A j i)
    (u v : ι → ℝ) : u ⬝ᵥ (A *ᵥ v) = (A *ᵥ u) ⬝ᵥ v := by
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

/-- the quadratic form as a double sum, generic index. -/
lemma quad_eq_double_sum_pf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (A.mulVec x) = ∑ a : ι, ∑ b : ι, x a * (A a b * x b) := by
  classical
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum]

/-- `x ⬝ (μx − Ax) = μ(x⬝x) − x⬝Ax`, generic index. -/
lemma dotProduct_smul_sub_mulVec_pf {ι : Type*} [Fintype ι] (μ : ℝ) (A : Matrix ι ι ℝ)
    (x : ι → ℝ) :
    x ⬝ᵥ (((μ • (1 : Matrix ι ι ℝ)) - A) *ᵥ x) = μ * (x ⬝ᵥ x) - x ⬝ᵥ (A.mulVec x) := by
  classical
  calc
    x ⬝ᵥ (((μ • (1 : Matrix ι ι ℝ)) - A) *ᵥ x)
        = x ⬝ᵥ (((μ • (1 : Matrix ι ι ℝ)) *ᵥ x) - (A *ᵥ x)) := by rw [Matrix.sub_mulVec]
    _ = x ⬝ᵥ ((μ • (1 : Matrix ι ι ℝ)) *ᵥ x) - x ⬝ᵥ (A *ᵥ x) := by rw [dotProduct_sub]
    _ = x ⬝ᵥ (μ • x) - x ⬝ᵥ (A *ᵥ x) := by
          congr 1
          rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    _ = μ * (x ⬝ᵥ x) - x ⬝ᵥ (A *ᵥ x) := by rw [dotProduct_smul_right_pf]

/-- `A *ᵥ (v - w) = A *ᵥ v - A *ᵥ w`, generic index. -/
lemma mulVec_vector_sub_pf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v w : ι → ℝ) :
    A *ᵥ (v - w) = A *ᵥ v - A *ᵥ w := by
  classical
  exact Matrix.mulVec_sub A v w

/-- `|x| ⬝ A|x| ≥ − x⬝Ax` for entrywise nonnegative `A`, generic index. -/
lemma quad_neg_le_quad_abs_pf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (hnonneg : ∀ i j : ι, 0 ≤ A i j) (x : ι → ℝ) :
    -(x ⬝ᵥ (A.mulVec x)) ≤ (fun a : ι => |x a|) ⬝ᵥ (A.mulVec (fun a => |x a|)) := by
  classical
  have hnonneg_sum : 0 ≤ ((fun a : ι => |x a|) ⬝ᵥ (A.mulVec (fun a => |x a|)))
      + (x ⬝ᵥ (A.mulVec x)) := by
    rw [quad_eq_double_sum_pf A (fun a : ι => |x a|), quad_eq_double_sum_pf A x]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro a ha
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro b hb
    have hterm : 0 ≤ |x a| * (A a b * |x b|) + x a * (A a b * x b) := by
      calc
        0 ≤ A a b * (|x a| * |x b| + x a * x b) := mul_nonneg (hnonneg a b) (abs_mul_add_self_nonneg (x a) (x b))
        _ = |x a| * (A a b * |x b|) + x a * (A a b * x b) := by ring
    simpa [mul_assoc, mul_comm, mul_left_comm] using hterm
  linarith

/-- `x⬝Ax ≤ |x| ⬝ A|x|` for entrywise nonnegative `A`, generic index. -/
lemma quad_le_quad_abs_pf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (hnonneg : ∀ i j : ι, 0 ≤ A i j) (x : ι → ℝ) :
    x ⬝ᵥ (A.mulVec x) ≤ (fun i : ι => |x i|) ⬝ᵥ (A.mulVec (fun i => |x i|)) := by
  classical
  have hdiff : ((fun i : ι => |x i|) ⬝ᵥ (A *ᵥ (fun i => |x i|))) - (x ⬝ᵥ (A *ᵥ x)) ≥ 0 := by
    rw [quad_eq_double_sum_pf A (fun i => |x i|), quad_eq_double_sum_pf A x]
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

/-- if `u_i = 0` for a nonnegative eigenvector, then every neighbour also has value `0`,
generic index. -/
lemma neighbor_zero_of_eigen_pf {ι : Type*} [Fintype ι] {G : SimpleGraph ι}
    {u : ι → ℝ} {lam0 : ℝ} (hu : ∀ i : ι, 0 ≤ u i)
    (hAu : (G.adjMatrix ℝ) *ᵥ u = lam0 • u) {i j : ι} (h0 : u i = 0) (hij : G.Adj i j) :
    u j = 0 := by
  classical
  have hrow : ((G.adjMatrix ℝ) *ᵥ u) i = lam0 * u i := by
    have h := congrFun hAu i
    simpa [Pi.smul_apply] using h
  have hsum0 : (∑ k ∈ G.neighborFinset i, u k) = 0 := by
    rw [SimpleGraph.adjMatrix_mulVec_apply] at hrow
    rw [h0] at hrow
    linarith
  have hmem : j ∈ G.neighborFinset i := by
    simpa using hij
  exact (Finset.sum_eq_zero_iff_of_nonneg (s := G.neighborFinset i)
    (f := fun k : ι => u k) (fun x hx => hu x)) |>.mp hsum0 j hmem

/-- propagation along a walk: if `u_i = 0` then every reachable vertex has value `0`,
generic index. -/
lemma zero_propagates_walk_pf {ι : Type*} [Fintype ι] {G : SimpleGraph ι}
    {u : ι → ℝ} {lam0 : ℝ} (hu : ∀ i : ι, 0 ≤ u i)
    (hAu : (G.adjMatrix ℝ) *ᵥ u = lam0 • u)
    {i j : ι} (h0 : u i = 0) (p : G.Walk i j) : u j = 0 := by
  induction p with
  | nil => simpa using h0
  | cons h q ih =>
    exact ih (neighbor_zero_of_eigen_pf hu hAu h0 h)


/-- charpoly of `lam0I - A` as a product, generic index. -/
lemma charpoly_sub_self_any {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (lam0 : ℝ) :
    (lam0 • (1 : Matrix ι ι ℝ) - A).charpoly
      = ∏ j : ι, (Polynomial.X - Polynomial.C (lam0 - hA.eigenvalues j)) := by
  classical
  let U : Matrix ι ι ℝ := (hA.eigenvectorUnitary : Matrix ι ι ℝ)
  let D : Matrix ι ι ℝ := diagonal (fun j : ι => hA.eigenvalues j)
  have hspec : A = U * D * star U := by
    dsimp [U, D]
    simpa using hA.spectral_theorem
  have hUU : U * star U = 1 := by
    dsimp [U]
    simpa using (Unitary.mul_star_self (R := Matrix ι ι ℝ) hA.eigenvectorUnitary :
      (hA.eigenvectorUnitary : Matrix ι ι ℝ) * star (hA.eigenvectorUnitary : Matrix ι ι ℝ) = 1)
  have hstU : star U * U = 1 := by
    dsimp [U]
    simpa using (Unitary.star_mul_self (R := Matrix ι ι ℝ) hA.eigenvectorUnitary :
      star (hA.eigenvectorUnitary : Matrix ι ι ℝ) * (hA.eigenvectorUnitary : Matrix ι ι ℝ) = 1)
  have hlam : lam0 • (1 : Matrix ι ι ℝ) = lam0 • (U * star U) := by
    rw [hUU]
  have hdiag : lam0 • (1 : Matrix ι ι ℝ) - D = diagonal (fun j : ι => lam0 - hA.eigenvalues j) := by
    dsimp [D]
    ext i j
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  have hBformula : lam0 • (1 : Matrix ι ι ℝ) - A = U * (diagonal (fun j => lam0 - hA.eigenvalues j)) * star U := by
    calc
      lam0 • (1 : Matrix ι ι ℝ) - A
          = lam0 • (U * star U) - U * D * star U := by rw [hlam, hspec]
      _ = U * (lam0 • (1 : Matrix ι ι ℝ) - D) * star U := by
          simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, smul_mul_assoc, mul_smul_comm]
      _ = U * (diagonal (fun j => lam0 - hA.eigenvalues j)) * star U := by rw [hdiag]
  calc
    (lam0 • (1 : Matrix ι ι ℝ) - A).charpoly
        = (U * (diagonal (fun j => lam0 - hA.eigenvalues j)) * star U).charpoly := by rw [hBformula]
    _ = ((diagonal (fun j => lam0 - hA.eigenvalues j)) * star U * U).charpoly := by
          rw [mul_assoc]
          exact Matrix.charpoly_mul_comm U (diagonal (fun j : ι => lam0 - hA.eigenvalues j) * star U)
    _ = (diagonal (fun j => lam0 - hA.eigenvalues j)).charpoly := by
          rw [mul_assoc, hstU]
          simp
    _ = ∏ j : ι, (Polynomial.X - Polynomial.C (lam0 - hA.eigenvalues j)) := by
          rw [Matrix.charpoly_diagonal]

/-- If all eigenvalues are at most `lam0`, then `lam0I - A` is PSD, generic index. -/
lemma sub_psd_of_eigenvalues_le_any {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    {lam0 : ℝ} (hle : ∀ i : ι, hA.eigenvalues i ≤ lam0) :
    (lam0 • (1 : Matrix ι ι ℝ) - A).PosSemidef := by
  classical
  let B : Matrix ι ι ℝ := lam0 • 1 - A
  change B.PosSemidef
  have hB : B.IsHermitian := by
    dsimp [B]
    rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    have ha : A j i = A i j := by
      have h := congrFun (congrFun hA.eq i) j
      simpa [Matrix.conjTranspose_apply] using h
    have h1 : (1 : Matrix ι ι ℝ) j i = (1 : Matrix ι ι ℝ) i j := by
      by_cases h : j = i
      · subst j
        simp [Matrix.one_apply]
      · have hi : i ≠ j := by
          intro hij
          exact h hij.symm
        simp [Matrix.one_apply, h, hi]
    calc
      (lam0 • (1 : Matrix ι ι ℝ) - A) j i
          = lam0 * (1 : Matrix ι ι ℝ) j i - A j i := by
            simp [Matrix.sub_apply, Pi.smul_apply, smul_eq_mul]
      _ = lam0 * (1 : Matrix ι ι ℝ) i j - A i j := by rw [h1, ha]
      _ = (lam0 • (1 : Matrix ι ι ℝ) - A) i j := by
            simp [Matrix.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply (hB.posSemidef_iff_eigenvalues_nonneg).mpr
  intro i
  let mu : ℝ := hB.eigenvalues i
  have hrootB : B.charpoly.IsRoot mu := by
    dsimp [mu]
    rw [hB.charpoly_eq]
    have hroot_i : (Polynomial.X - Polynomial.C (hB.eigenvalues i)).IsRoot (hB.eigenvalues i) := by
      exact (Polynomial.root_X_sub_C (a := hB.eigenvalues i) (b := hB.eigenvalues i)).2 rfl
    exact (Polynomial.isRoot_prod (Finset.univ) (fun k : ι =>
      Polynomial.X - Polynomial.C (hB.eigenvalues k)) (hB.eigenvalues i)).2 ⟨i, Finset.mem_univ i, hroot_i⟩
  have hpoly : B.charpoly = ∏ j : ι, (Polynomial.X - Polynomial.C (lam0 - hA.eigenvalues j)) := by
    dsimp [B]
    exact charpoly_sub_self_any A hA lam0
  have hroot' : (∏ j : ι, (Polynomial.X - Polynomial.C (lam0 - hA.eigenvalues j))).IsRoot mu := by
    exact hpoly ▸ hrootB
  have hex := (Polynomial.isRoot_prod (Finset.univ) (fun j : ι =>
    Polynomial.X - Polynomial.C (lam0 - hA.eigenvalues j)) mu).1 hroot'
  rcases hex with ⟨j, hj, hrootj⟩
  have hmu : lam0 - hA.eigenvalues j = mu := (Polynomial.root_X_sub_C).mp hrootj
  dsimp [mu] at hmu
  have hnonneg : 0 ≤ lam0 - hA.eigenvalues j := by linarith [hle j]
  rw [hmu] at hnonneg
  exact hnonneg

/-- If the spectral radius is `lam0 > 0`, then `lam0I - A` is PSD, generic index. -/
lemma sub_psd_of_spectralRadius_any {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    {lam0 : ℝ} (hlam0 : 0 < lam0) (hρ : spectralRadius ℝ A = ENNReal.ofReal lam0) :
    (lam0 • (1 : Matrix ι ι ℝ) - A).PosSemidef := by
  classical
  apply sub_psd_of_eigenvalues_le_any A hA
  intro i
  have hge : ENNReal.ofReal |hA.eigenvalues i| ≤ spectralRadius ℝ A := by
    have hm : hA.eigenvalues i ∈ spectrum ℝ A := hA.eigenvalues_mem_spectrum_real i
    have hval : ENNReal.ofReal |hA.eigenvalues i| = ((‖hA.eigenvalues i‖₊ : NNReal) : ENNReal) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
      rfl
    rw [hval]
    unfold spectralRadius
    exact le_trans
      (le_iSup (fun _ : hA.eigenvalues i ∈ spectrum ℝ A => ((‖hA.eigenvalues i‖₊ : NNReal) : ENNReal)) hm)
      (le_iSup (fun k : ℝ => ⨆ _ : k ∈ spectrum ℝ A, ((‖k‖₊ : NNReal) : ENNReal)) (hA.eigenvalues i))
  have hle : ENNReal.ofReal (|hA.eigenvalues i|) ≤ ENNReal.ofReal lam0 := by
    rwa [hρ] at hge
  have habs : |hA.eigenvalues i| ≤ lam0 :=
    (ENNReal.ofReal_le_ofReal_iff (le_of_lt hlam0)).mp hle
  linarith [le_abs_self (hA.eigenvalues i)]

/-- every eigenvalue has absolute value at most the spectral radius, generic index. -/
lemma spectralRadius_ge_eigenvalue_any {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (i : ι) :
    (ENNReal.ofReal |hA.eigenvalues i|) ≤ spectralRadius ℝ A := by
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

/-- spectral radius `lam0 > 0` bounds every eigenvalue above, generic index. -/
lemma eigenvalues_le_of_spectralRadius_any {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    {lam0 : ℝ} (hlam0 : 0 < lam0) (hρ : spectralRadius ℝ A = ENNReal.ofReal lam0) (i : ι) :
    hA.eigenvalues i ≤ lam0 := by
  classical
  have hge := spectralRadius_ge_eigenvalue_any A hA i
  have hle_abs : ENNReal.ofReal (|hA.eigenvalues i|) ≤ ENNReal.ofReal lam0 := by
    rwa [hρ] at hge
  have habs : |hA.eigenvalues i| ≤ lam0 := by
    exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt hlam0)).mp hle_abs
  linarith [le_abs_self (hA.eigenvalues i)]

/-- every real spectrum element is an eigenvalue, generic index. -/
lemma exists_eigenvalue_of_mem_spectrum_any {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ A) : ∃ j : ι, hA.eigenvalues j = μ := by
  classical
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hμ
  rw [hA.charpoly_eq] at hμ
  have hex := (Polynomial.isRoot_prod (Finset.univ) (fun j : ι =>
    Polynomial.X - Polynomial.C (hA.eigenvalues j)) μ).1 hμ
  rcases hex with ⟨j, hj, hrootj⟩
  refine ⟨j, ?_⟩
  exact (Polynomial.root_X_sub_C (a := hA.eigenvalues j) (b := μ)).mp hrootj

/-- `μ` is in the spectrum iff it is an eigenvalue, generic index. -/
lemma mem_spectrum_iff_eigenvalue_any {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    {lam0 : ℝ} : lam0 ∈ spectrum ℝ A ↔ ∃ j : ι, hA.eigenvalues j = lam0 := by
  classical
  constructor
  · intro h
    exact exists_eigenvalue_of_mem_spectrum_any A hA h
  · rintro ⟨j, hj⟩
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hA.charpoly_eq]
    apply (Polynomial.isRoot_prod _ _ _).2
    exact ⟨j, Finset.mem_univ j, by
      rw [hj]
      exact (Polynomial.root_X_sub_C (a := lam0) (b := lam0)).2 rfl⟩

/-- eigenvectors have squared norm 1, generic index. -/
lemma eigenvector_dotProduct_self_any {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (j : ι) :
    (hA.eigenvectorBasis j).ofLp ⬝ᵥ (hA.eigenvectorBasis j).ofLp = 1 := by
  classical
  let b := hA.eigenvectorBasis
  have hb : ‖b j‖ = 1 := hA.eigenvectorBasis.orthonormal.1 j
  calc
    (b j).ofLp ⬝ᵥ (b j).ofLp = ⟪b j, b j⟫ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct (𝕜 := ℝ) (x := b j) (y := b j)]
      simp
    _ = ‖b j‖ ^ 2 := real_inner_self_eq_norm_sq (b j)
    _ = 1 := by
      rw [hb]
      norm_num

/-- quadratic form of an eigenvector equals its eigenvalue, generic index. -/
lemma quad_eigenvector_any {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (j : ι) :
    (hA.eigenvectorBasis j).ofLp ⬝ᵥ (A.mulVec (hA.eigenvectorBasis j).ofLp)
      = hA.eigenvalues j := by
  classical
  rw [Matrix.IsHermitian.mulVec_eigenvectorBasis]
  rw [dotProduct_smul_right_pf]
  rw [eigenvector_dotProduct_self_any A hA j]
  ring

/-- Rayleigh upper bound: `x⬝Ax ≤ μ x⬝x` when every eigenvalue is ≤ μ, generic index. -/
lemma quad_le_of_eigenvalues_le_any {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    {i : ι} (hi : ∀ j : ι, hA.eigenvalues j ≤ hA.eigenvalues i) (x : ι → ℝ) :
    x ⬝ᵥ (A.mulVec x) ≤ hA.eigenvalues i * (x ⬝ᵥ x) := by
  classical
  have hpsd : (hA.eigenvalues i • (1 : Matrix ι ι ℝ) - A).PosSemidef :=
    sub_psd_of_eigenvalues_le_any A hA hi
  have hq : 0 ≤ star x ⬝ᵥ ((hA.eigenvalues i • (1 : Matrix ι ι ℝ) - A) *ᵥ x) :=
    hpsd.dotProduct_mulVec_nonneg x
  have hstar : star x = x := by
    funext a
    change star (x a) = x a
    simp
  have hq' : 0 ≤ hA.eigenvalues i * (x ⬝ᵥ x) - x ⬝ᵥ (A.mulVec x) := by
    rw [hstar] at hq
    simpa [dotProduct_smul_sub_mulVec_pf] using hq
  linarith

/-- index of a maximal eigenvalue value, generic index. -/
lemma exists_top_eigenvalue_index_any {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (hn : 0 < Fintype.card ι) :
    ∃ i : ι, ∀ j : ι, hA.eigenvalues j ≤ hA.eigenvalues i := by
  classical
  let S : Finset ℝ := (Finset.univ : Finset ι).image hA.eigenvalues
  have hSne : S.Nonempty := by
    rcases (Fintype.card_pos_iff.mp hn) with ⟨i0⟩
    refine ⟨hA.eigenvalues i0, ?_⟩
    exact Finset.mem_image.mpr ⟨i0, Finset.mem_univ _, rfl⟩
  let m := S.max' hSne
  have hmS : m ∈ S := S.max'_mem hSne
  rcases Finset.mem_image.mp hmS with ⟨i, hi, hmi⟩
  refine ⟨i, ?_⟩
  intro j
  have hmem : hA.eigenvalues j ∈ S := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  calc
    hA.eigenvalues j ≤ m := Finset.le_max' S (hA.eigenvalues j) hmem
    _ = hA.eigenvalues i := hmi.symm

/-- the maximal eigenvalue value dominates |every eigenvalue| for nonnegative symmetric A,
generic index. -/
lemma top_eigenvalue_ge_abs_any {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (hnonneg : ∀ i j : ι, 0 ≤ A i j) (hn : 0 < Fintype.card ι)
    (i : ι) (hi : ∀ j : ι, hA.eigenvalues j ≤ hA.eigenvalues i) (j : ι) :
    |hA.eigenvalues j| ≤ hA.eigenvalues i := by
  classical
  have hle : hA.eigenvalues j ≤ hA.eigenvalues i := hi j
  have hneg : -(hA.eigenvalues j) ≤ hA.eigenvalues i := by
    let w : ι → ℝ := (hA.eigenvectorBasis j).ofLp
    have hqe : w ⬝ᵥ (A.mulVec w) = hA.eigenvalues j := by
      simpa [w] using quad_eigenvector_any A hA j
    have hqabs : (fun a => |w a|) ⬝ᵥ (A.mulVec (fun a => |w a|)) ≤ hA.eigenvalues i := by
      have hray := quad_le_of_eigenvalues_le_any A hA hi (fun a : ι => |w a|)
      have hw1 : w ⬝ᵥ w = 1 := by simpa [w] using eigenvector_dotProduct_self_any A hA j
      have hw2 : (fun a : ι => |w a|) ⬝ᵥ (fun a : ι => |w a|) = w ⬝ᵥ w := by
        unfold dotProduct
        refine Finset.sum_congr rfl ?_
        intro a ha
        rw [← pow_two, ← pow_two, sq_abs]
      calc
        (fun a : ι => |w a|) ⬝ᵥ (A.mulVec (fun a => |w a|))
            ≤ hA.eigenvalues i * ((fun a : ι => |w a|) ⬝ᵥ (fun a : ι => |w a|)) := hray
        _ ≤ hA.eigenvalues i * (w ⬝ᵥ w) := by rw [hw2]
        _ = hA.eigenvalues i := by rw [hw1, mul_one]
    have hql : -(w ⬝ᵥ (A.mulVec w)) ≤ (fun a => |w a|) ⬝ᵥ (A.mulVec (fun a => |w a|)) :=
      quad_neg_le_quad_abs_pf A hnonneg w
    linarith
  exact (abs_le (a := hA.eigenvalues j) (b := hA.eigenvalues i)).mpr ⟨by linarith, hle⟩


/-- index of a maximal eigenvalue value, with explicit decidability instance. -/
lemma exists_top_eigenvalue_index_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (hn : 0 < Fintype.card ι) :
    ∃ i : ι, ∀ j : ι, hA.eigenvalues j ≤ hA.eigenvalues i := by
  classical
  let S : Finset ℝ := (Finset.univ : Finset ι).image hA.eigenvalues
  have hSne : S.Nonempty := by
    rcases (Fintype.card_pos_iff.mp hn) with ⟨i0⟩
    refine ⟨hA.eigenvalues i0, ?_⟩
    exact Finset.mem_image.mpr ⟨i0, Finset.mem_univ _, rfl⟩
  let m := S.max' hSne
  have hmS : m ∈ S := S.max'_mem hSne
  rcases Finset.mem_image.mp hmS with ⟨i, hi, hmi⟩
  refine ⟨i, ?_⟩
  intro j
  have hmem : hA.eigenvalues j ∈ S := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  calc
    hA.eigenvalues j ≤ m := Finset.le_max' S (hA.eigenvalues j) hmem
    _ = hA.eigenvalues i := hmi.symm

/-- eigenvectors have squared norm 1, with explicit decidability instance. -/
lemma eigenvector_dotProduct_self_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (j : ι) :
    (hA.eigenvectorBasis j).ofLp ⬝ᵥ (hA.eigenvectorBasis j).ofLp = 1 := by
  classical
  let b := hA.eigenvectorBasis
  have hb : ‖b j‖ = 1 := hA.eigenvectorBasis.orthonormal.1 j
  calc
    (b j).ofLp ⬝ᵥ (b j).ofLp = ⟪b j, b j⟫ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct (𝕜 := ℝ) (x := b j) (y := b j)]
      simp
    _ = ‖b j‖ ^ 2 := real_inner_self_eq_norm_sq (b j)
    _ = 1 := by
      rw [hb]
      norm_num

/-- quadratic form of an eigenvector equals its eigenvalue, with explicit decidability
instance. -/
lemma quad_eigenvector_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (j : ι) :
    (hA.eigenvectorBasis j).ofLp ⬝ᵥ (A.mulVec (hA.eigenvectorBasis j).ofLp)
      = hA.eigenvalues j := by
  classical
  rw [Matrix.IsHermitian.mulVec_eigenvectorBasis]
  rw [dotProduct_smul_right_pf]
  rw [eigenvector_dotProduct_self_aux A hA j]
  ring

/-- Rayleigh upper bound, with explicit decidability instance. -/
lemma quad_le_of_eigenvalues_le_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    {i : ι} (hi : ∀ j : ι, hA.eigenvalues j ≤ hA.eigenvalues i) (x : ι → ℝ) :
    x ⬝ᵥ (A.mulVec x) ≤ hA.eigenvalues i * (x ⬝ᵥ x) := by
  classical
  have hpsd : (hA.eigenvalues i • (1 : Matrix ι ι ℝ) - A).PosSemidef :=
    sub_psd_of_eigenvalues_le_any A hA hi
  have hq : 0 ≤ star x ⬝ᵥ ((hA.eigenvalues i • (1 : Matrix ι ι ℝ) - A) *ᵥ x) :=
    hpsd.dotProduct_mulVec_nonneg x
  have hstar : star x = x := by
    funext a
    change star (x a) = x a
    simp
  have hq' : 0 ≤ hA.eigenvalues i * (x ⬝ᵥ x) - x ⬝ᵥ (A.mulVec x) := by
    rw [hstar] at hq
    simpa [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul_right_pf] using hq
  linarith

/-- the maximal eigenvalue value dominates |every eigenvalue| for nonnegative symmetric A,
with explicit decidability instance. -/
lemma top_eigenvalue_ge_abs_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (hnonneg : ∀ i j : ι, 0 ≤ A i j) (hn : 0 < Fintype.card ι)
    (i : ι) (hi : ∀ j : ι, hA.eigenvalues j ≤ hA.eigenvalues i) (j : ι) :
    |hA.eigenvalues j| ≤ hA.eigenvalues i := by
  classical
  have hle : hA.eigenvalues j ≤ hA.eigenvalues i := hi j
  have hneg : -(hA.eigenvalues j) ≤ hA.eigenvalues i := by
    let w : ι → ℝ := (hA.eigenvectorBasis j).ofLp
    have hqe : w ⬝ᵥ (A.mulVec w) = hA.eigenvalues j := by
      simpa [w] using quad_eigenvector_aux A hA j
    have hqabs : (fun a => |w a|) ⬝ᵥ (A.mulVec (fun a => |w a|)) ≤ hA.eigenvalues i := by
      have hray := quad_le_of_eigenvalues_le_aux A hA hi (fun a : ι => |w a|)
      have hw1 : w ⬝ᵥ w = 1 := by simpa [w] using eigenvector_dotProduct_self_aux A hA j
      have hw2 : (fun a : ι => |w a|) ⬝ᵥ (fun a : ι => |w a|) = w ⬝ᵥ w := by
        unfold dotProduct
        refine Finset.sum_congr rfl ?_
        intro a ha
        rw [← pow_two, ← pow_two, sq_abs]
      calc
        (fun a : ι => |w a|) ⬝ᵥ (A.mulVec (fun a => |w a|))
            ≤ hA.eigenvalues i * ((fun a : ι => |w a|) ⬝ᵥ (fun a : ι => |w a|)) := hray
        _ ≤ hA.eigenvalues i * (w ⬝ᵥ w) := by rw [hw2]
        _ = hA.eigenvalues i := by rw [hw1, mul_one]
    have hql : -(w ⬝ᵥ (A.mulVec w)) ≤ (fun a => |w a|) ⬝ᵥ (A.mulVec (fun a => |w a|)) :=
      quad_neg_le_quad_abs_pf A hnonneg w
    linarith
  exact (abs_le (a := hA.eigenvalues j) (b := hA.eigenvalues i)).mpr ⟨by linarith, hle⟩

/-- every real spectrum element is an eigenvalue, with explicit decidability instance. -/
lemma exists_eigenvalue_of_mem_spectrum_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ A) : ∃ j : ι, hA.eigenvalues j = μ := by
  classical
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hμ
  rw [hA.charpoly_eq] at hμ
  have hex := (Polynomial.isRoot_prod (Finset.univ) (fun j : ι =>
    Polynomial.X - Polynomial.C (hA.eigenvalues j)) μ).1 hμ
  rcases hex with ⟨j, hj, hrootj⟩
  refine ⟨j, ?_⟩
  exact (Polynomial.root_X_sub_C (a := hA.eigenvalues j) (b := μ)).mp hrootj

/-- the spectral radius dominates the absolute value of every eigenvalue, with explicit
decidability instance. -/
lemma spectralRadius_ge_eigenvalue_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (i : ι) :
    (ENNReal.ofReal |hA.eigenvalues i|) ≤ spectralRadius ℝ A := by
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

/-- spectral radius bounds every eigenvalue above, with explicit decidability instance. -/
lemma eigenvalues_le_of_spectralRadius_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    {lam0 : ℝ} (hlam0 : 0 < lam0) (hρ : spectralRadius ℝ A = ENNReal.ofReal lam0) (i : ι) :
    hA.eigenvalues i ≤ lam0 := by
  classical
  have hge := spectralRadius_ge_eigenvalue_aux A hA i
  have hle_abs : ENNReal.ofReal (|hA.eigenvalues i|) ≤ ENNReal.ofReal lam0 := by
    rwa [hρ] at hge
  have habs : |hA.eigenvalues i| ≤ lam0 := by
    exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt hlam0)).mp hle_abs
  linarith [le_abs_self (hA.eigenvalues i)]

/-- nonnegative symmetric with spectral radius `lam0 > 0`: `lam0` is an eigenvalue,
generic index. -/
lemma exists_eigenvalue_eq_of_spectralRadius_any {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : 0 < Fintype.card ι)
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (hnonneg : ∀ i j : ι, 0 ≤ A i j) {lam0 : ℝ} (hlam0 : 0 < lam0)
    (hρ : spectralRadius ℝ A = ENNReal.ofReal lam0) : ∃ j : ι, hA.eigenvalues j = lam0 := by
  classical
  rcases exists_top_eigenvalue_index_aux A hA hn with ⟨i, hi⟩
  have htop : ∀ j : ι, |hA.eigenvalues j| ≤ hA.eigenvalues i :=
    fun j => top_eigenvalue_ge_abs_aux A hA hnonneg hn i hi j
  have hσi_nonneg : 0 ≤ hA.eigenvalues i := by
    have habs : |hA.eigenvalues i| ≤ hA.eigenvalues i := htop i
    have h1 := (abs_le (a := hA.eigenvalues i) (b := hA.eigenvalues i)).mp habs
    linarith
  have hρ_le : spectralRadius ℝ A ≤ ENNReal.ofReal (hA.eigenvalues i) := by
    rw [spectralRadius]
    refine iSup_le (fun μ => ?_)
    refine iSup_le (fun hμ => ?_)
    rcases exists_eigenvalue_of_mem_spectrum_any A hA hμ with ⟨j, hj⟩
    have hjμ : |μ| = |hA.eigenvalues j| := by rw [hj]
    have hleabs : |μ| ≤ hA.eigenvalues i := by
      rw [hjμ]
      exact htop j
    have hnn : (‖μ‖₊ : NNReal) = ⟨|μ|, abs_nonneg μ⟩ := by
      apply Subtype.ext
      simp [Real.norm_eq_abs]
    have hco : ((‖μ‖₊ : NNReal) : ENNReal) = ENNReal.ofReal |μ| := by
      rw [hnn]
      exact (ENNReal.ofReal_eq_coe_nnreal (abs_nonneg μ)).symm
    rw [hco]
    exact (ENNReal.ofReal_le_ofReal_iff hσi_nonneg).mpr hleabs
  have hlam_le : lam0 ≤ hA.eigenvalues i := by
    have h1 : ENNReal.ofReal lam0 ≤ ENNReal.ofReal (hA.eigenvalues i) := by
      calc
        ENNReal.ofReal lam0 = spectralRadius ℝ A := hρ.symm
        _ ≤ ENNReal.ofReal (hA.eigenvalues i) := hρ_le
    exact (ENNReal.ofReal_le_ofReal_iff hσi_nonneg).mp h1
  have htop_le_lam : hA.eigenvalues i ≤ lam0 :=
    eigenvalues_le_of_spectralRadius_aux A hA hlam0 hρ i
  refine ⟨i, ?_⟩
  exact le_antisymm htop_le_lam hlam_le

/-- PSD kernel from zero quadratic form, generic index. -/
lemma psd_ker_of_quad_zero_any {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (x : ι → ℝ)
    (hx : x ⬝ᵥ (B *ᵥ x) = 0) : B *ᵥ x = 0 := by
  classical
  have hBsym : ∀ i j : ι, B i j = B j i := hermitian_entries_symm_pf B hB.isHermitian
  have hquad : ∀ y : ι → ℝ, 0 ≤ y ⬝ᵥ (B *ᵥ y) := by
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
      dotProduct_mulVec_symm_pf B hBsym x (B *ᵥ x)
    calc
      (x + s • (B *ᵥ x)) ⬝ᵥ (B *ᵥ (x + s • (B *ᵥ x)))
          = (x + s • (B *ᵥ x)) ⬝ᵥ (B *ᵥ x + s • (B *ᵥ (B *ᵥ x))) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = x ⬝ᵥ (B *ᵥ x) + 2 * s * ((B *ᵥ x) ⬝ᵥ (B *ᵥ x))
          + s ^ 2 * ((B *ᵥ x) ⬝ᵥ (B *ᵥ (B *ᵥ x))) := by
            rw [dotProduct_add]
            rw [dotProduct_add_left_pf]
            rw [dotProduct_add_left_pf]
            rw [dotProduct_smul_right_pf, dotProduct_smul_right_pf, dotProduct_smul_left_pf, dotProduct_smul_left_pf]
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

/-- `|x| ⬝ A|x| ≥ - x ⬝ A x` for nonnegative symmetric A, generic index. -/
lemma quad_abs_ge_any {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hnonneg : ∀ i j : ι, 0 ≤ A i j) (x : ι → ℝ) :
    - (x ⬝ᵥ (A *ᵥ x)) ≤ (fun a : ι => |x a|) ⬝ᵥ (A *ᵥ fun a : ι => |x a|) := by
  classical
  exact quad_neg_le_quad_abs_pf A hnonneg x

/-- `|x| ⬝ |x| = x ⬝ x`, generic index. -/
lemma dotProduct_abs_self_any {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (fun i : ι => |x i|) ⬝ᵥ (fun i : ι => |x i|) = x ⬝ᵥ x := by
  classical
  calc
    (fun i => |x i|) ⬝ᵥ (fun i => |x i|) = ∑ i : ι, |x i| * |x i| := by simp [dotProduct]
    _ = ∑ i : ι, x i * x i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← pow_two, ← pow_two, sq_abs]
    _ = x ⬝ᵥ x := by simp [dotProduct]

/-- nonnegative symmetric matrix with spectral radius `lam0 > 0` has a nonnegative
eigenvector with positive coordinate sum, generic index. -/
lemma nonneg_eigenvector_of_spectralRadius_any {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : 0 < Fintype.card ι)
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (hnonneg : ∀ i j : ι, 0 ≤ A i j) {lam0 : ℝ} (hlam0 : 0 < lam0)
    (hρ : spectralRadius ℝ A = ENNReal.ofReal lam0) :
    ∃ u : ι → ℝ, (∀ i : ι, 0 ≤ u i) ∧ (0 < ∑ i : ι, u i)
      ∧ A *ᵥ u = lam0 • u := by
  classical
  rcases exists_eigenvalue_eq_of_spectralRadius_any hn A hA hnonneg hlam0 hρ with ⟨j0, hj0⟩
  let v : ι → ℝ := (hA.eigenvectorBasis j0).ofLp
  let u : ι → ℝ := fun i => |v i|
  refine ⟨u, ?_, ?_, ?_⟩
  · intro i
    dsimp [u]
    exact abs_nonneg (v i)
  · have hv0 : v ≠ 0 := by
      intro hv0
      have hv0' : (hA.eigenvectorBasis j0).ofLp = 0 := by simpa [v] using hv0
      have hd := eigenvector_dotProduct_self_aux A hA j0
      rw [hv0'] at hd
      simp at hd
    have hpos_coord : ∃ i : ι, 0 < |v i| := by
      by_contra hnot
      have hall : ∀ i : ι, v i = 0 := by
        intro i
        by_contra hne0
        have hpos : 0 < |v i| := abs_pos.mpr hne0
        exact hnot ⟨i, hpos⟩
      apply hv0
      apply funext
      intro i
      exact hall i
    rcases hpos_coord with ⟨i, hi⟩
    have hle1 : |v i| ≤ ∑ j : ι, |v j| := by
      exact Finset.single_le_sum (fun j hj => abs_nonneg (v j)) (Finset.mem_univ i)
    have hle2 : 0 < ∑ j : ι, |v j| := lt_of_lt_of_le hi hle1
    simpa [u] using hle2
  · let B : Matrix ι ι ℝ := lam0 • (1 : Matrix ι ι ℝ) - A
    have hBpsd : B.PosSemidef := sub_psd_of_spectralRadius_any A hA hlam0 hρ
    have hBv : B *ᵥ v = 0 := by
      dsimp [B, v]
      calc
        (lam0 • (1 : Matrix ι ι ℝ) - A) *ᵥ (hA.eigenvectorBasis j0).ofLp
            = (lam0 • (1 : Matrix ι ι ℝ)) *ᵥ (hA.eigenvectorBasis j0).ofLp
              - A *ᵥ (hA.eigenvectorBasis j0).ofLp := by rw [Matrix.sub_mulVec]
        _ = lam0 • (hA.eigenvectorBasis j0).ofLp - A *ᵥ (hA.eigenvectorBasis j0).ofLp := by
              rw [Matrix.smul_mulVec, Matrix.one_mulVec]
        _ = 0 := by
              rw [Matrix.IsHermitian.mulVec_eigenvectorBasis, hj0]
              simp
    have hmain (w : ι → ℝ) : w ⬝ᵥ (((lam0 • (1 : Matrix ι ι ℝ)) - A) *ᵥ w)
        = lam0 * (w ⬝ᵥ w) - w ⬝ᵥ (A *ᵥ w) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [dotProduct_smul_right_pf]
    have huBu_le : u ⬝ᵥ (B *ᵥ u) ≤ 0 := by
      have hqa := quad_le_quad_abs_pf A hnonneg v
      have hv2 : (fun i => |v i|) ⬝ᵥ (fun i => |v i|) = v ⬝ᵥ v := dotProduct_abs_self_any v
      calc
        u ⬝ᵥ (B *ᵥ u) = lam0 * (u ⬝ᵥ u) - u ⬝ᵥ (A *ᵥ u) := by
              dsimp [B]
              exact hmain u
        _ ≤ lam0 * (v ⬝ᵥ v) - v ⬝ᵥ (A *ᵥ v) := by
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
    have hBu0 : B *ᵥ u = 0 := psd_ker_of_quad_zero_any B hBpsd u huBu0
    dsimp [B] at hBu0
    have hsub : (lam0 • (1 : Matrix ι ι ℝ)) *ᵥ u = lam0 • u := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have hlin : lam0 • u - A *ᵥ u = 0 := by
      rw [Matrix.sub_mulVec] at hBu0
      rw [hsub] at hBu0
      exact hBu0
    have hAul : A *ᵥ u = lam0 • u := by
      exact (sub_eq_zero.mp hlin).symm
    exact hAul

/-- if a nonnegative eigenvector is zero somewhere in a connected graph, it is zero,
generic index. -/
lemma zero_of_connected_eigen_any {ι : Type*} [Fintype ι] {G : SimpleGraph ι}
    {u : ι → ℝ} {lam0 : ℝ}
    (hu : ∀ i : ι, 0 ≤ u i) (hAu : (G.adjMatrix ℝ) *ᵥ u = lam0 • u)
    {i : ι} (h0 : u i = 0) (hconn : ∀ a b : ι, G.Reachable a b) : u = 0 := by
  classical
  apply funext
  intro j
  rcases hconn i j with ⟨p⟩
  exact zero_propagates_walk_pf hu hAu h0 p

/-- a nonzero nonnegative eigenvector of a connected graph is positive, generic index. -/
lemma positive_eigenvector_of_connected_any {ι : Type*} [Fintype ι] {G : SimpleGraph ι}
    (hconn : ∀ i j : ι, G.Reachable i j) {u : ι → ℝ} {lam0 : ℝ}
    (hu : ∀ i : ι, 0 ≤ u i) (hu0 : u ≠ 0) (hAu : (G.adjMatrix ℝ) *ᵥ u = lam0 • u) :
    ∀ i : ι, 0 < u i := by
  classical
  have hex : ∃ i : ι, 0 < u i := by
    by_contra hnot
    have hall : ∀ i : ι, u i = 0 := by
      intro i
      by_contra hne
      have hpos : 0 < u i := lt_of_le_of_ne (hu i) (Ne.symm hne)
      exact hnot ⟨i, hpos⟩
    apply hu0
    apply funext
    intro i
    exact hall i
  rcases hex with ⟨i₀, hi₀⟩
  intro i
  by_contra hnot
  have hle : u i ≤ 0 := le_of_not_gt hnot
  have hz : u i = 0 := le_antisymm hle (hu i)
  have hzero : u = 0 := zero_of_connected_eigen_any hu hAu hz hconn
  have hi₀' : u i₀ = 0 := congrFun hzero i₀
  linarith

/-- the eigenspace of a connected graph is spanned by any nonzero nonnegative eigenvector,
generic index. -/
lemma eigenspace_eq_span_of_positive_any {ι : Type*} [Fintype ι] {G : SimpleGraph ι}
    (hconn : ∀ i j : ι, G.Reachable i j) {u : ι → ℝ} {lam0 : ℝ}
    (hu : ∀ i : ι, 0 ≤ u i) (hu0 : u ≠ 0) (hAu : (G.adjMatrix ℝ) *ᵥ u = lam0 • u) :
    ∀ w : ι → ℝ, (G.adjMatrix ℝ) *ᵥ w = lam0 • w → ∃ t : ℝ, w = t • u := by
  classical
  have hu_pos : ∀ i : ι, 0 < u i := positive_eigenvector_of_connected_any hconn hu hu0 hAu
  intro w hw
  by_cases hw0 : w = 0
  · refine ⟨0, ?_⟩
    simp [hw0]
  · have hex : ∃ i : ι, 0 < u i := by
      by_contra hnot
      have hall : ∀ i : ι, u i = 0 := by
        intro i
        by_contra hne
        have hpos : 0 < u i := lt_of_le_of_ne (hu i) (Ne.symm hne)
        exact hnot ⟨i, hpos⟩
      apply hu0
      apply funext
      intro i
      exact hall i
    rcases hex with ⟨i₀, hi₀⟩
    let S : Finset ℝ := (Finset.univ : Finset ι).image (fun i : ι => w i / u i)
    have hS : S.Nonempty := by
      refine ⟨w i₀ / u i₀, ?_⟩
      exact Finset.mem_image.mpr ⟨i₀, Finset.mem_univ i₀, rfl⟩
    let t : ℝ := S.min' hS
    have hge : ∀ i : ι, t ≤ w i / u i := by
      intro i
      exact Finset.min'_le S (w i / u i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hnonneg : ∀ i : ι, 0 ≤ w i - t * u i := by
      intro i
      have hupos : 0 < u i := hu_pos i
      have hmul : t * u i ≤ w i := (le_div_iff₀ hupos).mp (hge i)
      exact sub_nonneg.mpr hmul
    have hmm : t ∈ S := S.min'_mem hS
    rcases Finset.mem_image.mp hmm with ⟨j₀, hj₀mem, hj₀t⟩
    have hz : (w - t • u) j₀ = 0 := by
      dsimp
      have hupos : 0 < u j₀ := hu_pos j₀
      rw [← hj₀t]
      field_simp [ne_of_gt hupos]
      ring
    have hz_eigen : (G.adjMatrix ℝ) *ᵥ (w - t • u) = lam0 • (w - t • u) := by
      calc
        (G.adjMatrix ℝ) *ᵥ (w - t • u)
            = (G.adjMatrix ℝ) *ᵥ w - (G.adjMatrix ℝ) *ᵥ (t • u) := by rw [mulVec_vector_sub_pf]
        _ = lam0 • w - t • (lam0 • u) := by
              rw [hw, Matrix.mulVec_smul, hAu]
        _ = lam0 • (w - t • u) := by
              funext a
              simp [Pi.smul_apply]
              ring
    have hzero : w - t • u = 0 := zero_of_connected_eigen_any hnonneg hz_eigen hz hconn
    refine ⟨t, ?_⟩
    exact sub_eq_zero.mp hzero

end
end Submission
