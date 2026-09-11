import Submission.GraphSpec
import Submission.Perron
import Submission.Components
import Submission.ComponentsPF
import Submission.Part5WalkB
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.LinearAlgebra.Matrix.Hermitian

open Matrix
open Filter
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section

namespace EigenMult


/-! # Eigenvalue multiplicity of bounded-degree connected graphs (case `j = 2`)

Development of the spectral-graph-theory estimate needed for `Submission.eigen_mult_eventual`
(the eventual `εn` bound on the multiplicity of the second-largest-style positive eigenvalue of a
connected bounded-degree graph).  The proof follows Jiang--Tidor--Yao--Zhang--Zhao, "Equiangular
lines with a fixed angle", Ann. of Math. 194 (2021), Section 4, via eigenvalue-above counting
(Rayleigh quotients), deletion of an `r`-net, and closed-walk (trace) identities. -/

/-- largest eigenvalue value of a Hermitian matrix over a finite type `W` (0 if `W` empty). -/
noncomputable def topVal {W : Type*} [Fintype W] [DecidableEq W]
    (A : Matrix W W ℝ) (hA : A.IsHermitian) : ℝ :=
  if h : (Finset.univ : Finset W).Nonempty then
    ((Finset.univ : Finset W).image hA.eigenvalues).max' (by
      rcases h with ⟨i⟩
      refine ⟨hA.eigenvalues i, ?_⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  else 0

/-- an index whose eigenvalue value is the top value (when nonempty). -/
lemma exists_topVal_index {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (hW : (Finset.univ : Finset W).Nonempty) :
    ∃ j : W, (∀ i : W, hA.eigenvalues i ≤ hA.eigenvalues j) ∧ hA.eigenvalues j = topVal A hA := by
  classical
  let S : Finset ℝ := (Finset.univ : Finset W).image hA.eigenvalues
  have hSne : S.Nonempty := by
    rcases hW with ⟨i⟩
    exact ⟨hA.eigenvalues i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let m := S.max' hSne
  have hmS : m ∈ S := S.max'_mem hSne
  rcases Finset.mem_image.mp hmS with ⟨j, hjmem, hjm⟩
  have htop : topVal A hA = m := by
    dsimp [topVal]
    rw [dif_pos hW]
  refine ⟨j, ?_, ?_⟩
  · intro i
    have hmem : hA.eigenvalues i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    calc
      hA.eigenvalues i ≤ m := Finset.le_max' S (hA.eigenvalues i) hmem
      _ = hA.eigenvalues j := hjm.symm
  · rw [htop, hjm]

/-- eigenvalue values are at most `topVal`. -/
lemma eigenvalues_le_topVal {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (i : W) : hA.eigenvalues i ≤ topVal A hA := by
  classical
  have hW : (Finset.univ : Finset W).Nonempty := ⟨i, Finset.mem_univ i⟩
  rcases exists_topVal_index A hA hW with ⟨j, hj, hjt⟩
  rw [← hjt]
  exact hj i

/-- `topVal` is an actual eigenvalue value when the type is nonempty. -/
lemma topVal_is_value {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (hW : (Finset.univ : Finset W).Nonempty) :
    ∃ j : W, hA.eigenvalues j = topVal A hA := by
  classical
  rcases exists_topVal_index A hA hW with ⟨j, hj, hjt⟩
  exact ⟨j, hjt⟩

/-- `0 ≤ topVal` for nonnegative-entry Hermitian matrices on a nonempty type. -/
lemma topVal_nonneg_of_nonneg {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (hnonneg : ∀ i j : W, 0 ≤ A i j)
    (hW : (Finset.univ : Finset W).Nonempty) : 0 ≤ topVal A hA := by
  classical
  let o : W → ℝ := fun _ => 1
  have hnW : Nonempty W := by
    rcases hW with ⟨w, _⟩
    exact ⟨w⟩
  have hn : 0 < o ⬝ᵥ o := by
    dsimp [o]
    rw [dotProduct, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hpos : 0 < (Fintype.card W : ℝ) := by exact_mod_cast (Fintype.card_pos_iff.mpr hnW)
    positivity
  have hle : o ⬝ᵥ (A *ᵥ o) ≤ topVal A hA * (o ⬝ᵥ o) := by
    rcases exists_topVal_index A hA hW with ⟨j, hj, hjt⟩
    rw [← hjt]
    exact quad_le_of_eigenvalues_le_any A hA hj o
  have hnum : 0 ≤ o ⬝ᵥ (A *ᵥ o) := by
    rw [quad_eq_double_sum_pf]
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro b hb
    exact mul_nonneg (by positivity) (mul_nonneg (hnonneg a b) (by positivity))
  have hdiv : 0 ≤ (o ⬝ᵥ (A *ᵥ o)) / (o ⬝ᵥ o) := div_nonneg hnum (le_of_lt hn)
  have hdivle : (o ⬝ᵥ (A *ᵥ o)) / (o ⬝ᵥ o) ≤ topVal A hA := (div_le_iff₀ hn).mpr hle
  linarith

/-! ## 2. Eigenvector-basis expansion identities (in the function space). -/

/-- an eigenvector function: `A b_j = μ_j b_j`. -/
lemma bfun_eigen {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ) (hA : A.IsHermitian)
    (j : W) : A *ᵥ (hA.eigenvectorBasis j).ofLp = (hA.eigenvalues j) • (hA.eigenvectorBasis j).ofLp := by
  classical
  simpa using (hA.mulVec_eigenvectorBasis j)

/-- eigenvectors with different indices are orthogonal. -/
lemma bfun_ortho {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ) (hA : A.IsHermitian)
    {i j : W} (h : i ≠ j) :
    (hA.eigenvectorBasis i).ofLp ⬝ᵥ (hA.eigenvectorBasis j).ofLp = 0 := by
  classical
  have hb : ⟪hA.eigenvectorBasis i, hA.eigenvectorBasis j⟫ = 0 :=
    hA.eigenvectorBasis.orthonormal.2 h
  rw [← hb]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- eigenvectors are unit vectors. -/
lemma bfun_unit {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ) (hA : A.IsHermitian)
    (j : W) : (hA.eigenvectorBasis j).ofLp ⬝ᵥ (hA.eigenvectorBasis j).ofLp = 1 := by
  classical
  have h1 : ⟪hA.eigenvectorBasis j, hA.eigenvectorBasis j⟫ = 1 := by
    have hb : ‖hA.eigenvectorBasis j‖ = 1 := hA.eigenvectorBasis.orthonormal.1 j
    rw [real_inner_self_eq_norm_sq]
    rw [hb]
    norm_num
  rw [← h1]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- eigenvector-unitary entries. -/
lemma eigenUnitary_entry {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (i j : W) :
    (hA.eigenvectorUnitary : Matrix W W ℝ) i j = (hA.eigenvectorBasis j).ofLp i := by
  classical
  simpa using (Matrix.IsHermitian.eigenvectorUnitary_apply hA i j)

/-- any vector expands in the eigenvector basis. -/
lemma expand {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ) (hA : A.IsHermitian)
    (x : W → ℝ) :
    x = fun i : W => ∑ j : W, (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) * ((hA.eigenvectorBasis j).ofLp i) := by
  classical
  have hUU : (hA.eigenvectorUnitary : Matrix W W ℝ) * star (hA.eigenvectorUnitary : Matrix W W ℝ) = 1 := by
    simpa using (Unitary.mul_star_self (R := Matrix W W ℝ) hA.eigenvectorUnitary :
      (hA.eigenvectorUnitary : Matrix W W ℝ) * star (hA.eigenvectorUnitary : Matrix W W ℝ) = 1)
  have hx : (((hA.eigenvectorUnitary : Matrix W W ℝ) * star (hA.eigenvectorUnitary : Matrix W W ℝ)) *ᵥ x) = x := by
    rw [hUU]
    simp
  funext i
  have hy (j : W) : ((star (hA.eigenvectorUnitary : Matrix W W ℝ)) *ᵥ x) j =
      (hA.eigenvectorBasis j).ofLp ⬝ᵥ x := by
    simp [Matrix.mulVec, dotProduct, star_trivial]
  calc
    x i = (((hA.eigenvectorUnitary : Matrix W W ℝ) * star (hA.eigenvectorUnitary : Matrix W W ℝ)) *ᵥ x) i := by rw [hx]
    _ = ((hA.eigenvectorUnitary : Matrix W W ℝ) *ᵥ ((star (hA.eigenvectorUnitary : Matrix W W ℝ)) *ᵥ x)) i := by
          rw [Matrix.mulVec_mulVec]
    _ = ∑ j : W, (hA.eigenvectorUnitary : Matrix W W ℝ) i j * ((star (hA.eigenvectorUnitary : Matrix W W ℝ)) *ᵥ x) j := by
          simp [Matrix.mulVec, dotProduct]
    _ = ∑ j : W, ((hA.eigenvectorBasis j).ofLp i) * ((hA.eigenvectorBasis j).ofLp ⬝ᵥ x) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [eigenUnitary_entry A hA i j, hy j]
    _ = ∑ j : W, (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) * ((hA.eigenvectorBasis j).ofLp i) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [dotProduct_comm]
          ring

/-- swap of double sum: `Σ_i x_i · Σ_j a_j · b_ji = Σ_j a_j · Σ_i x_i · b_ji`. -/
lemma sum_swap_aux {W : Type*} [Fintype W] (a x : W → ℝ) (b : W → W → ℝ) :
    (∑ i : W, x i * ∑ j : W, a j * b j i) = ∑ j : W, a j * ∑ i : W, x i * b j i := by
  classical
  calc
    (∑ i : W, x i * ∑ j : W, a j * b j i) = ∑ i : W, ∑ j : W, x i * a j * b j i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ j : W, ∑ i : W, x i * a j * b j i := by rw [Finset.sum_comm]
    _ = ∑ j : W, a j * ∑ i : W, x i * b j i := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
/-- `x⬝x = ∑ (x⬝b_j)^2`. -/
lemma norm_expand {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ) (hA : A.IsHermitian)
    (x : W → ℝ) : x ⬝ᵥ x = ∑ j : W, (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2 := by
  classical
  let b : W → (W → ℝ) := fun j => (hA.eigenvectorBasis j).ofLp
  have hx : x = fun i : W => ∑ j : W, (x ⬝ᵥ b j) * (b j i) := by
    simpa [b] using expand A hA x
  calc
    x ⬝ᵥ x = ∑ i : W, x i * x i := by simp [dotProduct]
    _ = ∑ i : W, x i * (∑ j : W, (x ⬝ᵥ b j) * (b j i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← congrFun hx i]
    _ = ∑ j : W, (x ⬝ᵥ b j) * (∑ i : W, x i * (b j i)) := by
          exact (sum_swap_aux (a := fun j => (x ⬝ᵥ b j)) (x := x) (b := fun j i => b j i))
    _ = ∑ j : W, (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [b, dotProduct, pow_two]
lemma mulVec_expand {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ) (hA : A.IsHermitian)
    (x : W → ℝ) :
    A *ᵥ x = fun i : W => ∑ j : W, (hA.eigenvalues j) * (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) * ((hA.eigenvectorBasis j).ofLp i) := by
  classical
  let b : W → (W → ℝ) := fun j => (hA.eigenvectorBasis j).ofLp
  have hx : x = fun i : W => ∑ j : W, (x ⬝ᵥ b j) * (b j i) := by
    simpa [b] using expand A hA x
  have hbA (i j : W) : (∑ k : W, A i k * (b j k)) = (A *ᵥ (b j)) i := by
    simp [Matrix.mulVec, dotProduct]
  funext i
  calc
    (A *ᵥ x) i = ∑ k : W, A i k * x k := by simp [Matrix.mulVec, dotProduct]
    _ = ∑ k : W, A i k * (∑ j : W, (x ⬝ᵥ b j) * (b j k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          congr 1
          exact congrFun hx k
    _ = ∑ j : W, (x ⬝ᵥ b j) * (∑ k : W, A i k * (b j k)) := by
          exact (sum_swap_aux (a := fun j => (x ⬝ᵥ b j)) (x := fun k => A i k) (b := fun j k => b j k))
    _ = ∑ j : W, (x ⬝ᵥ b j) * (((hA.eigenvalues j) • (b j)) i) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hbA i j, bfun_eigen A hA j]
    _ = ∑ j : W, (hA.eigenvalues j) * (x ⬝ᵥ b j) * (b j i) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [b, Pi.smul_apply, mul_assoc, mul_comm, mul_left_comm]
lemma quad_expand {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ) (hA : A.IsHermitian)
    (x : W → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ j : W, (hA.eigenvalues j) * (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2 := by
  classical
  let b : W → (W → ℝ) := fun j => (hA.eigenvectorBasis j).ofLp
  let c : W → ℝ := fun j => (x ⬝ᵥ b j)
  calc
    x ⬝ᵥ (A *ᵥ x) = ∑ i : W, x i * (∑ j : W, (hA.eigenvalues j) * (c j) * (b j i)) := by
          rw [mulVec_expand A hA x]
          simp [dotProduct, c]
          rfl
    _ = ∑ j : W, (hA.eigenvalues j) * (c j) * (∑ i : W, x i * (b j i)) := by
          exact (sum_swap_aux (a := fun j => (hA.eigenvalues j) * (c j)) (x := x)
            (b := fun j i => b j i))
    _ = ∑ j : W, (hA.eigenvalues j) * (c j) * (x ⬝ᵥ b j) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [dotProduct]
    _ = ∑ j : W, (hA.eigenvalues j) * (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [c, pow_two]
          ring

/-! ## 3. Perron--Frobenius-lite dominance, trace and power-sum identities. -/

/-- adjacency entries are nonnegative. -/
lemma adjMatrix_nonneg_any {W : Type*} (G : SimpleGraph W) (i j : W) :
    0 ≤ (G.adjMatrix ℝ) i j := by
  classical
  by_cases h : G.Adj i j <;> simp [SimpleGraph.adjMatrix_apply, h]

/-- `x⬝Ax ≤ |x|⬝A|x|` for a nonnegative-entry matrix `A`. -/
lemma quad_self_le_quad_abs {W : Type*} [Fintype W] (A : Matrix W W ℝ)
    (hnonneg : ∀ i j : W, 0 ≤ A i j) (x : W → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ (fun i : W => |x i|) ⬝ᵥ (A *ᵥ fun i : W => |x i|) := by
  classical
  rw [quad_eq_double_sum_pf]
  rw [quad_eq_double_sum_pf]
  calc
    (∑ a : W, ∑ b : W, x a * (A a b * x b))
        ≤ ∑ a : W, ∑ b : W, (|x a|) * (A a b * |x b|) := by
          apply Finset.sum_le_sum
          intro a ha
          apply Finset.sum_le_sum
          intro b hb
          have hle0 : x a * x b ≤ |x a| * |x b| := by
            rw [← abs_mul]
            exact le_abs_self (x a * x b)
          calc
            x a * (A a b * x b) = A a b * (x a * x b) := by ring
            _ ≤ A a b * (|x a| * |x b|) := mul_le_mul_of_nonneg_left hle0 (hnonneg a b)
            _ = |x a| * (A a b * |x b|) := by ring
    _ = ∑ a : W, ∑ b : W, |x a| * (A a b * |x b|) := rfl

/-- The largest eigenvalue value dominates every eigenvalue in absolute value for a
nonnegative-entry real symmetric matrix (Perron--Frobenius-lite). -/
lemma top_eigenvalue_dominates {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (hnonneg : ∀ i j : W, 0 ≤ A i j)
    (hW : (Finset.univ : Finset W).Nonempty) (j : W) :
    |hA.eigenvalues j| ≤ topVal A hA := by
  classical
  rcases exists_topVal_index A hA hW with ⟨i, hi, hit⟩
  have hcard : 0 < Fintype.card W := by
    rcases hW with ⟨w, _⟩
    exact Fintype.card_pos_iff.mpr ⟨w⟩
  have h1 := top_eigenvalue_ge_abs_any A hA hnonneg hcard i hi j
  rw [← hit]
  exact h1

/-- largest eigenvalue value is nonnegative for a graph adjacency (nonempty type). -/
lemma graphTop_nonneg {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    (hG : (G.adjMatrix ℝ).IsHermitian) (hW : (Finset.univ : Finset W).Nonempty) :
    0 ≤ topVal (G.adjMatrix ℝ) hG := by
  classical
  exact topVal_nonneg_of_nonneg (G.adjMatrix ℝ) hG (adjMatrix_nonneg_any G) hW

/-- `(A^k *ᵥ x) i = ∑_j (μ_j)^k (x⬝b_j) (b_j i)`, using the eigenbasis of `A`. -/
lemma mulVec_pow_expand {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (k : ℕ) (x : W → ℝ) :
    (A ^ k) *ᵥ x = fun i : W => ∑ j : W, (hA.eigenvalues j) ^ k * (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) * ((hA.eigenvectorBasis j).ofLp i) := by
  classical
  let b : W → (W → ℝ) := fun j => (hA.eigenvectorBasis j).ofLp
  have hx : x = fun i : W => ∑ j : W, (x ⬝ᵥ b j) * (b j i) := by
    simpa [b] using expand A hA x
  have hbk (j : W) : (A ^ k) *ᵥ (b j) = (hA.eigenvalues j) ^ k • (b j) := by
    classical
    induction k with
    | zero => simp [b]
    | succ k ih =>
        calc
          (A ^ (k + 1)) *ᵥ (b j) = (A ^ k) *ᵥ (A *ᵥ (b j)) := by
                rw [pow_succ, Matrix.mulVec_mulVec]
          _ = (A ^ k) *ᵥ ((hA.eigenvalues j) • (b j)) := by rw [bfun_eigen A hA j]
          _ = (hA.eigenvalues j) • ((A ^ k) *ᵥ (b j)) := by simp [Matrix.mulVec_smul]
          _ = (hA.eigenvalues j) • ((hA.eigenvalues j) ^ k • (b j)) := by rw [ih]
          _ = (hA.eigenvalues j) ^ (k + 1) • (b j) := by
                funext w
                simp [Pi.smul_apply, pow_succ]
                ring
  funext i
  calc
    ((A ^ k) *ᵥ x) i = ∑ k0 : W, (A ^ k) i k0 * x k0 := by simp [Matrix.mulVec, dotProduct]
    _ = ∑ k0 : W, (A ^ k) i k0 * (∑ j : W, (x ⬝ᵥ b j) * (b j k0)) := by
          apply Finset.sum_congr rfl
          intro k0 hk0
          congr 1
          exact congrFun hx k0
    _ = ∑ j : W, (x ⬝ᵥ b j) * (∑ k0 : W, (A ^ k) i k0 * (b j k0)) := by
          exact (sum_swap_aux (a := fun j => (x ⬝ᵥ b j)) (x := fun k0 => (A ^ k) i k0)
            (b := fun j k0 => b j k0))
    _ = ∑ j : W, (x ⬝ᵥ b j) * (((A ^ k) *ᵥ (b j)) i) := by
          apply Finset.sum_congr rfl
          intro j hj
          rfl
    _ = ∑ j : W, (x ⬝ᵥ b j) * ((hA.eigenvalues j) ^ k * (b j i)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hbk j]
          simp [Pi.smul_apply]
    _ = ∑ j : W, (hA.eigenvalues j) ^ k * (x ⬝ᵥ b j) * (b j i) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring

/-- `x⬝(A^k x) = ∑_j (μ_j)^k (x⬝b_j)^2`, using the eigenbasis of `A`. -/
lemma quad_pow_expand {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (k : ℕ) (x : W → ℝ) :
    x ⬝ᵥ ((A ^ k) *ᵥ x) = ∑ j : W, (hA.eigenvalues j) ^ k * (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2 := by
  classical
  let b : W → (W → ℝ) := fun j => (hA.eigenvectorBasis j).ofLp
  let c : W → ℝ := fun j => (x ⬝ᵥ b j)
  calc
    x ⬝ᵥ ((A ^ k) *ᵥ x) = ∑ i : W, x i * (((A ^ k) *ᵥ x) i) := by simp [dotProduct]
    _ = ∑ i : W, x i * (∑ j : W, (hA.eigenvalues j) ^ k * (c j) * (b j i)) := by
          rw [mulVec_pow_expand A hA k x]
    _ = ∑ j : W, (hA.eigenvalues j) ^ k * (c j) * (∑ i : W, x i * (b j i)) := by
          exact (sum_swap_aux (a := fun j => (hA.eigenvalues j) ^ k * (c j)) (x := x)
            (b := fun j i => b j i))
    _ = ∑ j : W, (hA.eigenvalues j) ^ k * (c j) * (x ⬝ᵥ b j) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [dotProduct]
    _ = ∑ j : W, (hA.eigenvalues j) ^ k * (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [c, pow_two]
          ring

/-- the `(v,v)`-entry of an even matrix power is at most `topVal^(2k)`. -/
lemma diag_pow_even_le_top {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (hnonneg : ∀ i j : W, 0 ≤ A i j) (k : ℕ) (v : W) :
    (A ^ (2 * k)) v v ≤ (topVal A hA) ^ (2 * k) := by
  classical
  have hW : (Finset.univ : Finset W).Nonempty := ⟨v, Finset.mem_univ v⟩
  let e : W → ℝ := fun w => if w = v then 1 else 0
  have hself : e ⬝ᵥ e = 1 := by
    simp [e, dotProduct]
  have hdeg : (A ^ (2 * k)) v v = e ⬝ᵥ ((A ^ (2 * k)) *ᵥ e) := by
    simp [e, dotProduct, Matrix.mulVec]
  rw [hdeg]
  rw [quad_pow_expand A hA (2 * k) e]
  calc
    (∑ j : W, (hA.eigenvalues j) ^ (2 * k) * (e ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2)
        ≤ (∑ j : W, (topVal A hA) ^ (2 * k) * (e ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2) := by
          apply Finset.sum_le_sum
          intro j hj
          have hterm : (hA.eigenvalues j) ^ (2 * k) ≤ (topVal A hA) ^ (2 * k) := by
            have hle : |hA.eigenvalues j| ≤ topVal A hA := top_eigenvalue_dominates A hA hnonneg hW j
            have heven : (hA.eigenvalues j) ^ (2 * k) = |hA.eigenvalues j| ^ (2 * k) := by
              have hp : 0 ≤ (hA.eigenvalues j) ^ (2 * k) := by
                rw [pow_mul]
                exact pow_nonneg (sq_nonneg (hA.eigenvalues j)) k
              rw [← abs_of_nonneg hp]
              rw [abs_pow]
            rw [heven]
            exact pow_le_pow_left₀ (abs_nonneg _) hle (2 * k)
          exact mul_le_mul_of_nonneg_right hterm (sq_nonneg _)
    _ = (topVal A hA) ^ (2 * k) * (∑ j : W, (e ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2) := by
          rw [Finset.mul_sum]
    _ = (topVal A hA) ^ (2 * k) * (e ⬝ᵥ e) := by
          congr 1
          exact (norm_expand A hA e).symm
    _ = (topVal A hA) ^ (2 * k) := by rw [hself, mul_one]

/-! ## 4. Eigenvalue-above counting via Rayleigh quotients. -/

/-- the number of eigenvalue values strictly above `t`. -/
noncomputable def cardAbove {W : Type*} [Fintype W] (A : Matrix W W ℝ) (hA : A.IsHermitian)
    (t : ℝ) : ℕ := Fintype.card {i : W // t < hA.eigenvalues i}

/-- the number of eigenvalue values at least `t`. -/
noncomputable def cardAtLeast {W : Type*} [Fintype W] (A : Matrix W W ℝ) (hA : A.IsHermitian)
    (t : ℝ) : ℕ := Fintype.card {i : W // t ≤ hA.eigenvalues i}

/-- If a vector is orthogonal to every eigenvector with value above `t`, then its
quadratic form is at most `t‖x‖²`. -/
lemma quad_le_of_above_coeff_zero {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (t : ℝ) (x : W → ℝ)
    (hx : ∀ j : W, t < hA.eigenvalues j → x ⬝ᵥ (hA.eigenvectorBasis j).ofLp = 0) :
    x ⬝ᵥ (A *ᵥ x) ≤ t * (x ⬝ᵥ x) := by
  classical
  have hq := quad_expand A hA x
  have hn := norm_expand A hA x
  calc
    x ⬝ᵥ (A *ᵥ x) = ∑ j : W, (hA.eigenvalues j) * (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2 := hq
    _ ≤ t * (∑ j : W, (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2) := by
          calc
            (∑ j : W, (hA.eigenvalues j) * (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2)
                ≤ ∑ j : W, t * (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2 := by
                  apply Finset.sum_le_sum
                  intro j hj
                  by_cases hjt : hA.eigenvalues j ≤ t
                  · exact mul_le_mul_of_nonneg_right hjt (sq_nonneg _)
                  · have hlt : t < hA.eigenvalues j := lt_of_not_ge hjt
                    have hc0 : x ⬝ᵥ (hA.eigenvectorBasis j).ofLp = 0 := hx j hlt
                    rw [hc0]
                    simp
            _ = t * (∑ j : W, (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2) := by
                  rw [Finset.mul_sum]
    _ = t * (x ⬝ᵥ x) := by rw [hn]

/-- linear-combination map `c ↦ Σ_u c_u • x_u`. -/
def combMap {W ι : Type*} [Fintype ι] (x : ι → (W → ℝ)) : (ι → ℝ) →ₗ[ℝ] (W → ℝ) where
  toFun c := ∑ u : ι, c u • x u
  map_add' c d := by
    ext w
    simp [Finset.sum_add_distrib, add_smul]
  map_smul' a c := by
    ext w
    simp [Finset.mul_sum, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

/-- dot product of a linear combination with `y` expands. -/
lemma comb_dot {W ι : Type*} [Fintype W] [Fintype ι] (x : ι → (W → ℝ)) (c : ι → ℝ)
    (y : W → ℝ) :
    (combMap x c) ⬝ᵥ y = ∑ u : ι, c u * (x u ⬝ᵥ y) := by
  classical
  unfold combMap
  simp [dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [Finset.sum_comm]

/-- `A` applied to a linear combination expands. -/
lemma mulVec_combMap {W ι : Type*} [Fintype W] [Fintype ι] (A : Matrix W W ℝ)
    (x : ι → (W → ℝ)) (c : ι → ℝ) :
    A *ᵥ (combMap x c) = combMap (fun v => A *ᵥ x v) c := by
  classical
  ext w
  simp [combMap, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- pairwise-orthogonal nonzero vectors are linearly independent. -/
lemma independent_of_pairwise_orth {W ι : Type*} [Fintype W] [Fintype ι] [DecidableEq ι]
    (x : ι → (W → ℝ)) (hx : ∀ u : ι, x u ≠ 0)
    (horth : ∀ ⦃u v : ι⦄, u ≠ v → x u ⬝ᵥ x v = 0) :
    Function.Injective (combMap x) := by
  classical
  intro c d hcd
  apply funext
  intro u
  have h1 : (combMap x c) ⬝ᵥ (x u) = c u * (x u ⬝ᵥ x u) := by
    rw [comb_dot]
    exact Finset.sum_eq_single u
      (by intro v hv hvu; have := horth (u := v) (v := u) hvu; simp [this])
      (by intro hu; exact False.elim (hu (Finset.mem_univ u)))
  have h2 : (combMap x d) ⬝ᵥ (x u) = d u * (x u ⬝ᵥ x u) := by
    rw [comb_dot]
    exact Finset.sum_eq_single u
      (by intro v hv hvu; have := horth (u := v) (v := u) hvu; simp [this])
      (by intro hu; exact False.elim (hu (Finset.mem_univ u)))
  have hdiff : (combMap x c) ⬝ᵥ (x u) = (combMap x d) ⬝ᵥ (x u) := by rw [hcd]
  have hcu : c u * (x u ⬝ᵥ x u) = d u * (x u ⬝ᵥ x u) := by
    rwa [h1, h2] at hdiff
  have hpos : 0 < x u ⬝ᵥ x u := by
    have hle : 0 ≤ x u ⬝ᵥ x u := by
      rw [dotProduct]
      exact Finset.sum_nonneg (fun i hi => by simpa [pow_two] using sq_nonneg (x u i))
    have hne : x u ⬝ᵥ x u ≠ 0 := by
      intro hz
      apply hx u
      funext i
      have hsqsum : (∑ j : W, (x u j) ^ 2) = 0 := by
        simpa [dotProduct, pow_two, mul_comm] using hz
      have hzsq : (x u i) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset W))
          (f := fun j => (x u j) ^ 2) (fun a ha => sq_nonneg (x u a))).mp hsqsum i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp hzsq
    exact lt_of_le_of_ne hle (Ne.symm hne)
  exact mul_right_cancel₀ (ne_of_gt hpos) hcu

/-- dot product of a scalar-multiple combination: `y⬝(Σ c_u • x_u) = Σ c_u (y⬝x_u)`. -/
lemma dot_comb {W ι : Type*} [Fintype W] [Fintype ι] (y : W → ℝ) (x : ι → (W → ℝ))
    (c : ι → ℝ) :
    y ⬝ᵥ (combMap x c) = ∑ u : ι, c u * (y ⬝ᵥ x u) := by
  classical
  unfold combMap
  simp [dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [Finset.sum_comm]

/-- norm squared of an orthogonal combination. -/
lemma orth_norm_sq {W ι : Type*} [Fintype W] [Fintype ι] [DecidableEq ι]
    (x : ι → (W → ℝ)) (c : ι → ℝ)
    (horth : ∀ ⦃u v : ι⦄, u ≠ v → x u ⬝ᵥ x v = 0) :
    (combMap x c) ⬝ᵥ (combMap x c) = ∑ u : ι, (c u) ^ 2 * (x u ⬝ᵥ x u) := by
  classical
  calc
    (combMap x c) ⬝ᵥ (combMap x c) = ∑ u : ι, c u * (x u ⬝ᵥ (combMap x c)) := by
          rw [comb_dot]
    _ = ∑ u : ι, c u * (∑ v : ι, c v * (x u ⬝ᵥ x v)) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [dot_comb]
    _ = ∑ u : ι, (c u) ^ 2 * (x u ⬝ᵥ x u) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_eq_single u]
          · ring
          · intro v hv hvu
            have := horth (u := v) (v := u) hvu
            rw [dotProduct_comm, this]
            simp
          · intro huniv
            exact False.elim (huniv (Finset.mem_univ u))

/-- quadratic form of an `A`-orthogonal combination. -/
lemma orth_quad {W ι : Type*} [Fintype W] [Fintype ι] [DecidableEq ι]
    (A : Matrix W W ℝ) (x : ι → (W → ℝ)) (c : ι → ℝ)
    (horthA : ∀ ⦃u v : ι⦄, u ≠ v → x u ⬝ᵥ (A *ᵥ x v) = 0) :
    (combMap x c) ⬝ᵥ (A *ᵥ (combMap x c)) = ∑ u : ι, (c u) ^ 2 * (x u ⬝ᵥ (A *ᵥ x u)) := by
  classical
  calc
    (combMap x c) ⬝ᵥ (A *ᵥ (combMap x c))
        = (combMap x c) ⬝ᵥ (combMap (fun v => A *ᵥ x v) c) := by rw [mulVec_combMap]
    _ = ∑ u : ι, c u * (x u ⬝ᵥ (combMap (fun v => A *ᵥ x v) c)) := by
          rw [comb_dot]
    _ = ∑ u : ι, c u * (∑ v : ι, c v * (x u ⬝ᵥ (A *ᵥ x v))) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [dot_comb (y := x u) (x := fun v : ι => A *ᵥ (x v))]
    _ = ∑ u : ι, (c u) ^ 2 * (x u ⬝ᵥ (A *ᵥ x u)) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_eq_single u]
          · ring
          · intro v hv hvu
            have h' : x u ⬝ᵥ (A *ᵥ x v) = 0 := horthA (u := u) (v := v) hvu.symm
            rw [h']
            simp
          · intro huniv
            exact False.elim (huniv (Finset.mem_univ u))

/-- if a nonzero combination has zero dot against every eigenvector above `t`, its Rayleigh
quotient would be both `> t` and `≤ t`. -/
lemma kernel_trivial {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]
    (A : Matrix W W ℝ) (hA : A.IsHermitian) (t : ℝ) (x : ι → (W → ℝ))
    (hx0 : ∀ u : ι, x u ≠ 0)
    (hray : ∀ u : ι, t * (x u ⬝ᵥ x u) < x u ⬝ᵥ (A *ᵥ x u))
    (horth : ∀ ⦃u v : ι⦄, u ≠ v → x u ⬝ᵥ x v = 0 ∧ x u ⬝ᵥ (A *ᵥ x v) = 0)
    (c : ι → ℝ)
    (hpi : ∀ j : W, t < hA.eigenvalues j → (combMap x c) ⬝ᵥ (hA.eigenvectorBasis j).ofLp = 0) :
    c = 0 := by
  classical
  by_contra hc0
  let q : W → ℝ := combMap x c
  have hpsi0 : q ≠ 0 := by
    intro hz
    apply hc0
    have hinj := independent_of_pairwise_orth x hx0 (fun ⦃u v⦄ hne => (horth hne).1)
    have : (combMap x c) = combMap x 0 := by
      simpa using hz
    have hc0' : c = 0 := by simpa using (hinj this)
    exact hc0'
  have hq_ray : t * (q ⬝ᵥ q) < q ⬝ᵥ (A *ᵥ q) := by
    have hnorm := orth_norm_sq x c (fun ⦃u v⦄ hne => (horth hne).1)
    have hquad := orth_quad A x c (fun ⦃u v⦄ hne => (horth hne).2)
    have hex_u : ∃ u : ι, c u ≠ 0 := by
      by_contra hall0
      apply hc0
      funext u
      by_contra hc
      exact hall0 ⟨u, hc⟩
    rcases hex_u with ⟨u0, hc0u⟩
    have hstrict : t * ((c u0) ^ 2 * (x u0 ⬝ᵥ x u0)) < (c u0) ^ 2 * (x u0 ⬝ᵥ (A *ᵥ x u0)) := by
      calc
        t * ((c u0) ^ 2 * (x u0 ⬝ᵥ x u0)) = (c u0) ^ 2 * (t * (x u0 ⬝ᵥ x u0)) := by ring
        _ < (c u0) ^ 2 * (x u0 ⬝ᵥ (A *ᵥ x u0)) :=
              mul_lt_mul_of_pos_left (hray u0) (sq_pos_of_ne_zero hc0u)
    have hterm (u : ι) : t * ((c u) ^ 2 * (x u ⬝ᵥ x u)) ≤ (c u) ^ 2 * (x u ⬝ᵥ (A *ᵥ x u)) := by
      calc
        t * ((c u) ^ 2 * (x u ⬝ᵥ x u)) = (c u) ^ 2 * (t * (x u ⬝ᵥ x u)) := by ring
        _ ≤ (c u) ^ 2 * (x u ⬝ᵥ (A *ᵥ x u)) :=
              mul_le_mul_of_nonneg_left (le_of_lt (hray u)) (sq_nonneg (c u))
    have hsum : t * (∑ u : ι, (c u) ^ 2 * (x u ⬝ᵥ x u))
        < ∑ u : ι, (c u) ^ 2 * (x u ⬝ᵥ (A *ᵥ x u)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_lt_sum (fun u hu => hterm u)
        ⟨u0, Finset.mem_univ u0, hstrict⟩
    change t * ((combMap x c) ⬝ᵥ (combMap x c)) < (combMap x c) ⬝ᵥ (A *ᵥ (combMap x c))
    rw [hnorm, hquad]
    exact hsum
  have hq_le : q ⬝ᵥ (A *ᵥ q) ≤ t * (q ⬝ᵥ q) := by
    exact quad_le_of_above_coeff_zero A hA t q hpi
  have hposnorm : 0 < q ⬝ᵥ q := by
    have hle : 0 ≤ q ⬝ᵥ q := by
      rw [dotProduct]
      exact Finset.sum_nonneg (fun i hi => by simpa [pow_two] using sq_nonneg (q i))
    have hne : q ⬝ᵥ q ≠ 0 := by
      intro hz
      apply hpsi0
      funext i
      have hsqsum : (∑ j : W, (q j) ^ 2) = 0 := by
        simpa [dotProduct, pow_two, mul_comm] using hz
      have hzsq : (q i) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset W))
          (f := fun j => (q j) ^ 2) (fun a ha => sq_nonneg (q a))).mp hsqsum i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp hzsq
    exact lt_of_le_of_ne hle (Ne.symm hne)
  linarith

/-- abstract counting: pairwise orthogonal and `A`-orthogonal family with Rayleigh `> t`
has size at most the number of eigenvalue values above `t`. -/
lemma card_above_ge_family {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]
    (A : Matrix W W ℝ) (hA : A.IsHermitian) (t : ℝ) (x : ι → (W → ℝ))
    (hx0 : ∀ u : ι, x u ≠ 0)
    (hray : ∀ u : ι, t * (x u ⬝ᵥ x u) < x u ⬝ᵥ (A *ᵥ x u))
    (horth : ∀ ⦃u v : ι⦄, u ≠ v → x u ⬝ᵥ x v = 0 ∧ x u ⬝ᵥ (A *ᵥ x v) = 0) :
    Fintype.card ι ≤ cardAbove A hA t := by
  classical
  let pi : (W → ℝ) →ₗ[ℝ] ({j : W // t < hA.eigenvalues j} → ℝ) :=
    { toFun := fun x => fun j => x ⬝ᵥ (hA.eigenvectorBasis j.1).ofLp
      map_add' := by
        intro x y
        funext j
        simp [dotProduct_add_left_pf]
      map_smul' := by
        intro a x
        funext j
        simp [dotProduct_smul_left_pf] }
  let psi := combMap x
  let phi : (ι → ℝ) →ₗ[ℝ] ({j : W // t < hA.eigenvalues j} → ℝ) := pi.comp psi
  have hphi_inj : Function.Injective phi := by
    intro c d hcd
    have hsub : c - d = 0 := by
      apply kernel_trivial A hA t x hx0 hray horth (c - d)
      intro j hjt
      have hz : phi (c - d) = 0 := by
        rw [map_sub, hcd, sub_self]
      have hpi0 : pi (psi (c - d)) = 0 := by
        simpa [phi, LinearMap.comp_apply] using hz
      have hjj : (pi (psi (c - d))) ⟨j, hjt⟩ = 0 := congrFun hpi0 ⟨j, hjt⟩
      simpa [psi, pi] using hjj
    exact sub_eq_zero.mp hsub
  have hdim : Module.finrank ℝ (ι → ℝ) ≤ Module.finrank ℝ ({j : W // t < hA.eigenvalues j} → ℝ) := by
    exact LinearMap.finrank_le_finrank_of_injective hphi_inj
  rw [Module.finrank_pi, Module.finrank_pi] at hdim
  change Fintype.card ι ≤ cardAbove A hA t
  exact hdim


/-! ## 6a. Multiplicity vs eigenvalue-value counting; deletion bounds via ranks. -/

/-- `μI − A` is Hermitian when `A` is. -/
lemma hermitian_smul_sub {W : Type*} [DecidableEq W] (A : Matrix W W ℝ) (hA : A.IsHermitian)
    (μ : ℝ) : ((μ • (1 : Matrix W W ℝ)) - A).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  have hs : A j i = A i j := by
    have h := congrFun (congrFun hA.eq i) j
    simpa [Matrix.conjTranspose_apply, star_trivial] using h
  by_cases hij : i = j
  · subst j
    simp [Matrix.sub_apply, Pi.smul_apply, Matrix.one_apply]
  · simp [Matrix.sub_apply, Pi.smul_apply, Matrix.one_apply, hs, hij, Ne.symm hij]

/-- eigenvectors with value `< μ` of a vector in the `μ`-kernel have zero coefficient. -/
lemma ker_coeff_lt_zero {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (μ : ℝ) {x : W → ℝ}
    (hx : ((μ • (1 : Matrix W W ℝ)) - A) *ᵥ x = 0)
    (j : W) (hj : hA.eigenvalues j < μ) : x ⬝ᵥ (hA.eigenvectorBasis j).ofLp = 0 := by
  classical
  have hb : ((μ • (1 : Matrix W W ℝ)) - A) *ᵥ (hA.eigenvectorBasis j).ofLp
      = (μ - hA.eigenvalues j) • (hA.eigenvectorBasis j).ofLp := by
    funext w
    rw [mulVec_sub_pf]
    rw [bfun_eigen A hA j]
    simp [Pi.smul_apply, Matrix.mulVec, Matrix.one_apply]
    have hsum : (∑ k : W, (if w = k then μ else 0) * (hA.eigenvectorBasis j).ofLp k)
        = (if w = w then μ else 0) * (hA.eigenvectorBasis j).ofLp w := by
      refine Finset.sum_eq_single (s := (Finset.univ : Finset W))
        (f := fun k => (if w = k then μ else 0) * (hA.eigenvectorBasis j).ofLp k) w ?_ ?_
      · intro k hk hkw
        rw [if_neg (Ne.symm hkw)]
        simp
      · intro hw
        exact False.elim (hw (Finset.mem_univ w))
    change (∑ k : W, (if w = k then μ else 0) * (hA.eigenvectorBasis j).ofLp k)
        - hA.eigenvalues j * (hA.eigenvectorBasis j).ofLp w
        = (μ - hA.eigenvalues j) * (hA.eigenvectorBasis j).ofLp w
    rw [hsum]
    simp
    ring
  have hz : x ⬝ᵥ (((μ • (1 : Matrix W W ℝ)) - A) *ᵥ (hA.eigenvectorBasis j).ofLp) = 0 := by
    calc
      x ⬝ᵥ (((μ • (1 : Matrix W W ℝ)) - A) *ᵥ (hA.eigenvectorBasis j).ofLp)
          = (((μ • (1 : Matrix W W ℝ)) - A) *ᵥ x) ⬝ᵥ (hA.eigenvectorBasis j).ofLp := by
            apply dotProduct_mulVec_symm_pf
            · intro a b
              exact hermitian_entries_symm_pf ((μ • (1 : Matrix W W ℝ)) - A)
                (hermitian_smul_sub A hA μ) a b
      _ = 0 := by rw [hx]; simp
  rw [hb] at hz
  have hz' : (μ - hA.eigenvalues j) * (x ⬝ᵥ (hA.eigenvectorBasis j).ofLp) = 0 := by
    simpa [Pi.smul_apply, mul_comm] using hz
  exact (mul_eq_zero.mp hz').resolve_left
    (sub_ne_zero.mpr (Ne.symm (ne_of_lt hj)))

/-- the kernel of `μI − A` injects into the coordinate space of eigenvalue values `≥ μ`. -/
lemma finrank_ker_le_cardAtLeast {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (((μ • (1 : Matrix W W ℝ)) - A).mulVecLin))
      ≤ cardAtLeast A hA μ := by
  classical
  let K : Submodule ℝ (W → ℝ) := LinearMap.ker (((μ • (1 : Matrix W W ℝ)) - A).mulVecLin)
  let pi : (W → ℝ) →ₗ[ℝ] ({j : W // μ ≤ hA.eigenvalues j} → ℝ) :=
    { toFun := fun x => fun j => x ⬝ᵥ (hA.eigenvectorBasis j.1).ofLp
      map_add' := by
        intro x y
        funext j
        simp [dotProduct_add_left_pf]
      map_smul' := by
        intro a x
        funext j
        simp [dotProduct_smul_left_pf] }
  let phi : K →ₗ[ℝ] ({j : W // μ ≤ hA.eigenvalues j} → ℝ) := pi.comp K.subtype
  have hphi_ker_triv : LinearMap.ker phi = ⊥ := by
    apply Submodule.ext
    intro x
    constructor
    · intro hx
      rw [Submodule.mem_bot]
      apply Subtype.ext
      -- x.1 = 0
      have hzker0 : ((μ • (1 : Matrix W W ℝ)) - A) *ᵥ x.1 = 0 := by
        change ((μ • (1 : Matrix W W ℝ)) - A).mulVecLin x.1 = 0
        exact x.2
      have hpi0 : pi x.1 = 0 := by
        simpa [phi, LinearMap.comp_apply, LinearMap.mem_ker] using hx
      have hcoeff (j : W) : x.1 ⬝ᵥ (hA.eigenvectorBasis j).ofLp = 0 := by
        by_cases hj : μ ≤ hA.eigenvalues j
        · have hjj : (pi x.1) ⟨j, hj⟩ = 0 := congrFun hpi0 ⟨j, hj⟩
          simpa [pi] using hjj
        · exact ker_coeff_lt_zero A hA μ hzker0 j (lt_of_not_ge hj)
      apply funext
      intro w
      have hexp := expand A hA x.1
      calc
        x.1 w = ∑ j0 : W, (x.1 ⬝ᵥ (hA.eigenvectorBasis j0).ofLp) * ((hA.eigenvectorBasis j0).ofLp w) := congrFun hexp w
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro j0 hj0
          rw [hcoeff j0]
          simp
    · intro hx
      rw [Submodule.mem_bot] at hx
      rw [LinearMap.mem_ker]
      rw [hx]
      simp
  have hinj : Function.Injective phi := by
    rw [← LinearMap.ker_eq_bot]
    exact hphi_ker_triv
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hcard : Module.finrank ℝ ({j : W // μ ≤ hA.eigenvalues j} → ℝ) = cardAtLeast A hA μ := by
    rw [Module.finrank_pi]
    rfl
  rw [hcard] at hle
  change Module.finrank ℝ K ≤ cardAtLeast A hA μ
  simpa [K, phi] using hle

/-- finrank-nullity for matrix linear maps: `dim ker = n - rank`. -/
lemma finrank_ker_eq_card_sub_rank {W : Type*} [Fintype W] [DecidableEq W]
    (M : Matrix W W ℝ) :
    Module.finrank ℝ (LinearMap.ker (M.mulVecLin)) = Fintype.card W - M.rank := by
  classical
  have h1 := LinearMap.finrank_range_add_finrank_ker (f := M.mulVecLin)
  have hrange : Module.finrank ℝ (LinearMap.range (M.mulVecLin)) = M.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.range_mulVecLin]
  have hdim : Module.finrank ℝ (W → ℝ) = Fintype.card W := by rw [Module.finrank_pi]
  rw [hdim, hrange] at h1
  omega

/-- rank of a principal submatrix is at most the rank of the whole matrix. -/
lemma rank_principal_submatrix_le {W : Type*} [Fintype W] [DecidableEq W]
    {W0 : Type*} [Fintype W0] [DecidableEq W0]
    (M : Matrix W W ℝ) (e : W0 → W) (he : Function.Injective e) :
    (Matrix.rank (fun i j : W0 => M (e i) (e j)) : ℕ) ≤ M.rank := by
  classical
  let rho : (W → ℝ) →ₗ[ℝ] (W0 → ℝ) :=
    { toFun := fun x => fun i => x (e i)
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  let A0 : Matrix W0 W0 ℝ := fun i j => M (e i) (e j)
  have hcol : Submodule.span ℝ (Set.range A0.col) ≤
      Submodule.map rho (Submodule.span ℝ (Set.range M.col)) := by
    rw [Submodule.span_le]
    intro y hy
    rcases Set.mem_range.mp hy with ⟨j, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨M.col (e j), ?_, ?_⟩
    · exact Submodule.subset_span ⟨e j, rfl⟩
    · funext i
      rfl
  have hdim1 : Module.finrank ℝ (Submodule.span ℝ (Set.range A0.col))
      ≤ Module.finrank ℝ (Submodule.map rho (Submodule.span ℝ (Set.range M.col))) :=
    Submodule.finrank_mono hcol
  have hdim2 : Module.finrank ℝ (Submodule.map rho (Submodule.span ℝ (Set.range M.col)))
      ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range M.col)) :=
    Submodule.finrank_map_le rho (Submodule.span ℝ (Set.range M.col))
  have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range A0.col))
      ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range M.col)) := le_trans hdim1 hdim2
  change (Matrix.rank A0 : ℕ) ≤ M.rank
  rw [Matrix.rank_eq_finrank_span_cols A0, Matrix.rank_eq_finrank_span_cols M]
  exact h1

/-- deleting vertices increases the geometric multiplicity of an eigenvalue value by at most
the number of deleted vertices. -/
lemma finrank_ker_le_of_submatrix {W W0 : Type*} [Fintype W] [Fintype W0]
    [DecidableEq W] [DecidableEq W0] (A : Matrix W W ℝ) (hA : A.IsHermitian)
    (B : Matrix W0 W0 ℝ) (hB : B.IsHermitian) (μ : ℝ)
    (hsub : ∃ e : W0 ↪ W, ∀ i j : W0, B i j = A (e i) (e j)) :
    Module.finrank ℝ (LinearMap.ker (((μ • (1 : Matrix W W ℝ)) - A).mulVecLin)) ≤
      Module.finrank ℝ (LinearMap.ker (((μ • (1 : Matrix W0 W0 ℝ)) - B).mulVecLin))
        + (Fintype.card W - Fintype.card W0) := by
  classical
  rcases hsub with ⟨e, he⟩
  let M : Matrix W W ℝ := (μ • (1 : Matrix W W ℝ)) - A
  let B0 : Matrix W0 W0 ℝ := (μ • (1 : Matrix W0 W0 ℝ)) - B
  have hB0_sub : (Matrix.rank B0 : ℕ) ≤ M.rank := by
    have hr := rank_principal_submatrix_le M e e.2
    have heq : (fun i j : W0 => M (e i) (e j)) = B0 := by
      funext i j
      have hij : B i j = A (e i) (e j) := he i j
      dsimp [M, B0]
      -- M (e i)(e j) = μ δ_{ei,ej} - A(ei)(ej) = μ δ_{ij} - B i j
      by_cases h : i = j
      · subst j
        simp [he i i, Matrix.one_apply, Matrix.sub_apply, Pi.smul_apply, hij]
      · have hne : e i ≠ e j := fun h2 => h (e.injective h2)
        simp [he i j, Matrix.one_apply, Matrix.sub_apply, Pi.smul_apply, h, hne, hij]
    rwa [heq] at hr
  have hkerM := finrank_ker_eq_card_sub_rank M
  have hkerB := finrank_ker_eq_card_sub_rank B0
  have hgoal : Fintype.card W - M.rank ≤ (Fintype.card W0 - B0.rank) + (Fintype.card W - Fintype.card W0) := by
    omega
  have hfinM : Module.finrank ℝ (LinearMap.ker (M.mulVecLin))
      ≤ Module.finrank ℝ (LinearMap.ker (B0.mulVecLin)) + (Fintype.card W - Fintype.card W0) := by
    rw [hkerM, hkerB]
    exact hgoal
  simpa [M, B0] using hfinM

/-! ## 6b. Zero-extension between a vertex set and its ambient index type. -/

/-- zero-extension of a function on `s` to all of `W`. -/
def extendZero {W : Type*} [DecidableEq W] (s : Set W) (z : s → ℝ) : W → ℝ :=
  fun w => if hw : w ∈ s then z ⟨w, hw⟩ else 0

lemma extendZero_apply_mem {W : Type*} [DecidableEq W] (s : Set W) (z : s → ℝ) {w : W}
    (hw : w ∈ s) : extendZero s z w = z ⟨w, hw⟩ := by
  classical
  simp [extendZero, hw]

lemma extendZero_apply_not_mem {W : Type*} [DecidableEq W] (s : Set W) (z : s → ℝ) {w : W}
    (hw : w ∉ s) : extendZero s z w = 0 := by
  classical
  simp [extendZero, hw]

/-- the norm of the extension equals the norm of the original function. -/
lemma extendZero_dot_self {W : Type*} [Fintype W] [DecidableEq W] (s : Set W) (z : s → ℝ) :
    extendZero s z ⬝ᵥ extendZero s z = z ⬝ᵥ z := by
  classical
  let g : W → ℝ := fun w => extendZero s z w * extendZero s z w
  have hz (w : W) (hw : w ∉ s) : g w = 0 := by
    simp [g, extendZero, hw]
  have hsplit : (∑ w : W, g w) = ∑ x : {w : W // w ∈ s}, g x.1 := by
    have hc := (Fintype.sum_subtype_add_sum_subtype (ι := W) (p := fun w : W => w ∈ s) (f := g)).symm
    have h0 : (∑ x : {w : W // w ∉ s}, g x.1) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact hz x.1 x.2
    rw [h0, add_zero] at hc
    exact hc
  calc
    extendZero s z ⬝ᵥ extendZero s z = ∑ w : W, g w := by simp [dotProduct, g, extendZero]
    _ = ∑ x : {w : W // w ∈ s}, g x.1 := hsplit
    _ = ∑ x : s, z x * z x := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [g, extendZero]
    _ = z ⬝ᵥ z := by simp [dotProduct]

/-- the quadratic form of the extension equals that of the original function on the
induced matrix. -/
lemma extendZero_quad {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ) (s : Set W)
    (z : s → ℝ) :
    extendZero s z ⬝ᵥ (A *ᵥ extendZero s z) =
      z ⬝ᵥ ((fun i j : s => A i.1 j.1) *ᵥ z) := by
  classical
  let Asub : Matrix s s ℝ := fun i j => A i.1 j.1
  calc
    extendZero s z ⬝ᵥ (A *ᵥ extendZero s z)
        = ∑ w : W, extendZero s z w * ((A *ᵥ extendZero s z) w) := by simp [dotProduct]
    _ = ∑ w : s, z w * ((A *ᵥ extendZero s z) w.1) := by
          have hz0 (w : W) (hw : w ∉ s) : extendZero s z w * ((A *ᵥ extendZero s z) w) = 0 := by
            simp [extendZero, hw]
          have hc := (Fintype.sum_subtype_add_sum_subtype (ι := W) (p := fun w : W => w ∈ s)
            (f := fun w => extendZero s z w * ((A *ᵥ extendZero s z) w)))
          have h0 : (∑ x : {w : W // w ∉ s}, extendZero s z x.1 * ((A *ᵥ extendZero s z) x.1)) = 0 := by
            apply Finset.sum_eq_zero
            intro x hx
            exact hz0 x.1 x.2
          rw [h0, add_zero] at hc
          rw [← hc]
          apply Finset.sum_congr rfl
          intro w hw
          congr 1
          simp [extendZero]
    _ = ∑ w : s, z w * ((Asub *ᵥ z) w) := by
          apply Finset.sum_congr rfl
          intro w hw
          congr 1
          change (∑ u : W, A w.1 u * extendZero s z u) = (Asub *ᵥ z) w
          have hz0 (u : W) (hu : u ∉ s) : A w.1 u * extendZero s z u = 0 := by
            simp [extendZero, hu]
          have hc := (Fintype.sum_subtype_add_sum_subtype (ι := W) (p := fun u : W => u ∈ s)
            (f := fun u => A w.1 u * extendZero s z u))
          have h0 : (∑ x : {u : W // u ∉ s}, A w.1 x.1 * extendZero s z x.1) = 0 := by
            apply Finset.sum_eq_zero
            intro x hx
            exact hz0 x.1 x.2
          rw [h0, add_zero] at hc
          rw [← hc]
          simp [Asub, Matrix.mulVec, dotProduct]
          apply Finset.sum_congr rfl
          intro u hu
          congr 1
          simp [extendZero]
    _ = z ⬝ᵥ (Asub *ᵥ z) := by simp [dotProduct]


/-- the largest eigenvalue value of the adjacency of a ball. -/
noncomputable def ballTop {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (c : V) (r : ℕ) : ℝ :=
  topVal ((ballGraph G c r).adjMatrix ℝ) (adj_isHerm_any (ballGraph G c r))

/-! ## 6c. Eigenvalue power sums, trace identities and the eigen-bound. -/

/-- `tr(A^k) = ∑_i μ_i^k` for a Hermitian matrix. -/
lemma trace_pow_eq_sum_eigs {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i : W, (hA.eigenvalues i) ^ k := by
  classical
  let e : W → (W → ℝ) := fun w => fun u => if u = w then 1 else 0
  have hdiag (w : W) : (A ^ k) w w = e w ⬝ᵥ ((A ^ k) *ᵥ (e w)) := by
    simp [e, dotProduct, Matrix.mulVec]
  calc
    (A ^ k).trace = ∑ w : W, (A ^ k) w w := by simp [Matrix.trace]
    _ = ∑ w : W, e w ⬝ᵥ ((A ^ k) *ᵥ (e w)) := by
          apply Finset.sum_congr rfl
          intro w hw
          exact hdiag w
    _ = ∑ w : W, ∑ j : W, (hA.eigenvalues j) ^ k * (e w ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2 := by
          apply Finset.sum_congr rfl
          intro w hw
          exact quad_pow_expand A hA k (e w)
    _ = ∑ j : W, (hA.eigenvalues j) ^ k * (∑ w : W, (e w ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
    _ = ∑ j : W, (hA.eigenvalues j) ^ k := by
          apply Finset.sum_congr rfl
          intro j hj
          have hunit : (∑ w : W, (e w ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2) = 1 := by
            calc
              (∑ w : W, (e w ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2)
                  = (∑ w : W, ((hA.eigenvectorBasis j).ofLp w) ^ 2) := by
                    apply Finset.sum_congr rfl
                    intro w hw
                    congr 1
                    simp [e, dotProduct, Finset.sum_ite_eq']
              _ = (hA.eigenvectorBasis j).ofLp ⬝ᵥ (hA.eigenvectorBasis j).ofLp := by
                    simp [dotProduct, pow_two]
              _ = 1 := bfun_unit A hA j
          rw [hunit]
          ring
/-- the sum of even powers of the eigenvalues of `H` is bounded by the sum over vertices of
the corresponding powers of the local spectral radii (the `r`-ball spectral tops). -/
lemma eigen_bound_sum {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) (r : ℕ) :
    (∑ i : W, ((adj_isHerm_any H).eigenvalues i) ^ (2 * r))
      ≤ ∑ w : W, (ballTop H w r) ^ (2 * r) := by
  classical
  have htr := trace_pow_eq_sum_eigs (H.adjMatrix ℝ) (adj_isHerm_any H) (2 * r)
  calc
    (∑ i : W, ((adj_isHerm_any H).eigenvalues i) ^ (2 * r))
        = (H.adjMatrix ℝ ^ (2 * r)).trace := by rw [← htr]
    _ = ∑ w : W, (H.adjMatrix ℝ ^ (2 * r)) w w := by simp [Matrix.trace]
    _ ≤ ∑ w : W, ((ballGraph H w r).adjMatrix ℝ ^ (2 * r)) (ballCenter H w r) (ballCenter H w r) := by
          apply Finset.sum_le_sum
          intro w hw
          exact diag_pow_le_ball H w r
    _ ≤ ∑ w : W, (ballTop H w r) ^ (2 * r) := by
          apply Finset.sum_le_sum
          intro w hw
          have hbw : ((ballGraph H w r).adjMatrix ℝ).IsHermitian := adj_isHerm_any (ballGraph H w r)
          have hle := diag_pow_even_le_top ((ballGraph H w r).adjMatrix ℝ) hbw
            (adjMatrix_nonneg_any (ballGraph H w r)) r (ballCenter H w r)
          simpa [ballTop, ballCenter] using hle

/-! ## 6d. Vertex-indexed restricted (zeroed) adjacency matrices. -/

/-- zero a matrix outside of a set of indices (restriction with padding). -/
def restrictedMatrix {V : Type*} [DecidableEq V] (A : Matrix V V ℝ) (s : Set V) :
    Matrix V V ℝ := fun u v => if u ∈ s ∧ v ∈ s then A u v else 0

/-- restricted matrices of Hermitian matrices are Hermitian. -/
lemma restrictedMatrix_isHermitian {V : Type*} [DecidableEq V] (A : Matrix V V ℝ)
    (hA : A.IsHermitian) (s : Set V) : (restrictedMatrix A s).IsHermitian := by
  classical
  rw [Matrix.isHermitian_iff_isSymm]
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  by_cases hij : i ∈ s ∧ j ∈ s
  · have hs : A j i = A i j := by
      have h := congrFun (congrFun hA.eq i) j
      simpa [Matrix.conjTranspose_apply, star_trivial] using h
    simp [restrictedMatrix, hij, hs]
  · have hji : ¬ (j ∈ s ∧ i ∈ s) := by
      intro hji
      exact hij ⟨hji.2, hji.1⟩
    simp [restrictedMatrix, hij, hji]

/-- restricted adjacency matrices have nonnegative entries. -/
lemma restrictedMatrix_nonneg {V : Type*} (A : Matrix V V ℝ) (hnonneg : ∀ i j : V, 0 ≤ A i j)
    (s : Set V) : ∀ i j : V, 0 ≤ restrictedMatrix A s i j := by
  classical
  intro i j
  by_cases h : i ∈ s ∧ j ∈ s <;> simp [restrictedMatrix, h, hnonneg i j]

/-- the vertex-local spectral top of `A` on a vertex set `s`. -/
noncomputable def localTop {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ)
    (hA : A.IsHermitian) (s : Set V) : ℝ :=
  topVal (restrictedMatrix A s) (restrictedMatrix_isHermitian A hA s)

/-- the `(w,w)`-entry of a `2r`-power of the restricted matrix is at most the top power. -/
lemma restricted_pow_diag_le_localTop {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hnonneg : ∀ i j : V, 0 ≤ A i j) (s : Set V) (w : V) (r : ℕ) :
    (restrictedMatrix A s ^ (2 * r)) w w ≤ (localTop A hA s) ^ (2 * r) := by
  classical
  have hle := diag_pow_even_le_top (restrictedMatrix A s)
    (restrictedMatrix_isHermitian A hA s) (restrictedMatrix_nonneg A hnonneg s) r w
  simpa [localTop] using hle

/-! ## 6e. The set of vertices with large local spectral radius is small. -/

/-- if two vertices are far apart, their reach-balls are disjoint and non-adjacent. -/
lemma ballSet_disjoint_of_dist {V : Type*} (G : SimpleGraph V) {u v : V} {r : ℕ}
    (h : 2 * r + 1 < G.dist u v) (huv : G.Reachable u v) :
    Disjoint (ballSet G u r) (ballSet G v r) ∧
    ∀ a ∈ ballSet G u r, ∀ b ∈ ballSet G v r, ¬ G.Adj a b := by
  classical
  constructor
  · rw [Set.disjoint_left]
    intro a ha hb
    rcases ha with ⟨pu, hpu⟩
    rcases hb with ⟨pv, hpv⟩
    let q : G.Walk u v := pu.append pv.reverse
    have hq : q.length ≤ 2 * r := by
      simp [q]
      linarith
    have hneed : G.dist u v ≤ 2 * r := le_trans (G.dist_le q) hq
    nlinarith
  · intro a ha b hb hadj
    rcases ha with ⟨pu, hpu⟩
    rcases hb with ⟨pv, hpv⟩
    let q : G.Walk u v := pu.append (hadj.toWalk.append pv.reverse)
    have hq : q.length ≤ 2 * r + 1 := by
      simp [q]
      linarith
    have hneed : G.dist u v ≤ 2 * r + 1 := le_trans (G.dist_le q) hq
    exact (not_lt_of_ge hneed) h

/-- the set of vertices whose `r`-ball has spectral top above `lam`. -/
noncomputable def Uset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (r : ℕ) (lam : ℝ) : Finset V :=
  Finset.univ.filter (fun v : V => lam < ballTop G v r)

/-- for `u` with `lam < ballTop G u r`, the zero-extension of a top eigenvector of the
`r`-ball is a nonzero vector with Rayleigh quotient `> lam`. -/
lemma ball_eigen_ext_exists {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {lam : ℝ} {u : V} {r : ℕ} (hu : lam < ballTop G u r) :
    ∃ x : V → ℝ, x ≠ 0 ∧ lam * (x ⬝ᵥ x) < x ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ x) := by
  classical
  let hBall := adj_isHerm_any (ballGraph G u r)
  have htop : ∃ j : ballSet G u r, hBall.eigenvalues j = ballTop G u r := by
    change ∃ j : ballSet G u r,
      (adj_isHerm_any (ballGraph G u r)).eigenvalues j = ballTop G u r
    exact topVal_is_value ((ballGraph G u r).adjMatrix ℝ) (adj_isHerm_any (ballGraph G u r))
      (ballFinset_nonempty G u r)
  let j := Classical.choose htop
  have hj : hBall.eigenvalues j = ballTop G u r := Classical.choose_spec htop
  let f : ballSet G u r → ℝ := (hBall.eigenvectorBasis j).ofLp
  let x : V → ℝ := extendZero (ballSet G u r) f
  have hf0 : f ≠ 0 := by
    intro hf0
    have hd := bfun_unit ((ballGraph G u r).adjMatrix ℝ) hBall j
    have hd' : f ⬝ᵥ f = 1 := by
      dsimp [f]
      exact hd
    rw [hf0] at hd'
    have hz : (0 : ballSet G u r → ℝ) ⬝ᵥ (0 : ballSet G u r → ℝ) = 0 := by simp [dotProduct]
    rw [hz] at hd'
    norm_num at hd'
  have hfe : ((ballGraph G u r).adjMatrix ℝ) *ᵥ f = (hBall.eigenvalues j) • f := by
    dsimp [f]
    exact bfun_eigen ((ballGraph G u r).adjMatrix ℝ) hBall j
  refine ⟨x, ?_, ?_⟩
  · intro hx0
    apply hf0
    funext v
    have hx0v := congrFun hx0 v
    have hvv : (v : V) ∈ ballSet G u r := v.2
    have hxv : x (v : V) = f v := by
      dsimp [x]
      exact extendZero_apply_mem (ballSet G u r) f hvv
    rw [← hxv]
    exact hx0v
  · have hquad := extendZero_quad ((G.adjMatrix ℝ)) (ballSet G u r) f
    have heq : (fun i j : ballSet G u r => (G.adjMatrix ℝ) i.1 j.1)
        = (ballGraph G u r).adjMatrix ℝ := by
      ext i j
      by_cases hadj : G.Adj i.1 j.1
      · simp [SimpleGraph.adjMatrix_apply, hadj, ball_adj_iff]
      · simp [SimpleGraph.adjMatrix_apply, hadj, ball_adj_iff]
    have hquadx : x ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ x)
        = f ⬝ᵥ (((ballGraph G u r).adjMatrix ℝ) *ᵥ f) := by
      dsimp [x]
      rw [heq] at hquad
      exact hquad
    have hquadf : f ⬝ᵥ (((ballGraph G u r).adjMatrix ℝ) *ᵥ f)
        = (hBall.eigenvalues j) * (f ⬝ᵥ f) := by
      rw [hfe]
      simp [Pi.smul_apply, mul_comm, mul_assoc]
    have hnorm : x ⬝ᵥ x = f ⬝ᵥ f := by
      dsimp [x]
      exact extendZero_dot_self (ballSet G u r) f
    have hgt : lam * (f ⬝ᵥ f) < (hBall.eigenvalues j) * (f ⬝ᵥ f) := by
      have hfpos : 0 < f ⬝ᵥ f := by
        have hle : 0 ≤ f ⬝ᵥ f := by
          rw [dotProduct]
          exact Finset.sum_nonneg (fun i hi => by simpa [pow_two] using sq_nonneg (f i))
        have hne : f ⬝ᵥ f ≠ 0 := by
          intro hz
          apply hf0
          funext i
          have hsqsum : (∑ j0 : ballSet G u r, (f j0) ^ 2) = 0 := by
            simpa [dotProduct, pow_two, mul_comm] using hz
          have hzsq : (f i) ^ 2 = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset (ballSet G u r)))
              (f := fun j0 => (f j0) ^ 2) (fun a ha => sq_nonneg (f a))).mp hsqsum i (Finset.mem_univ i)
          exact sq_eq_zero_iff.mp hzsq
        exact lt_of_le_of_ne hle (Ne.symm hne)
      have hjlt : lam < hBall.eigenvalues j := by
        rw [hj]
        exact hu
      exact mul_lt_mul_of_pos_right hjlt hfpos
    calc
      lam * (x ⬝ᵥ x) = lam * (f ⬝ᵥ f) := by rw [hnorm]
      _ < (hBall.eigenvalues j) * (f ⬝ᵥ f) := hgt
      _ = f ⬝ᵥ (((ballGraph G u r).adjMatrix ℝ) *ᵥ f) := hquadf.symm
      _ = x ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ x) := hquadx.symm
/-- the zero-extension is supported on `s`. -/
lemma extendZero_mem_support {W : Type*} [DecidableEq W] (s : Set W) (z : s → ℝ) :
    ∀ w : W, w ∉ s → extendZero s z w = 0 := by
  classical
  intro w hw
  exact extendZero_apply_not_mem s z hw

/-- the zero-extension of a function on `s` vanishes on a disjoint set. -/
lemma extendZero_disjoint_dot {W : Type*} [Fintype W] [DecidableEq W] (s t : Set W)
    (z : s → ℝ) (y : t → ℝ) (hdisj : Disjoint s t) :
    extendZero s z ⬝ᵥ extendZero t y = 0 := by
  classical
  rw [Set.disjoint_left] at hdisj
  calc
    extendZero s z ⬝ᵥ extendZero t y
        = ∑ w : W, (if hw : w ∈ s then z ⟨w, hw⟩ else 0) * (if hw : w ∈ t then y ⟨w, hw⟩ else 0) := by
          simp [extendZero, dotProduct]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro w hw
          by_cases hws : w ∈ s
          · have hwt : w ∉ t := hdisj hws
            simp [hws, hwt]
          · simp [hws]

/-- if two sets are disjoint and non-adjacent, functions supported on them are
`A`-orthogonal. -/
lemma extendZero_disjoint_quad {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s t : Set V) (z : s → ℝ) (y : t → ℝ)
    (hdisj : Disjoint s t)
    (hnadj : ∀ a ∈ s, ∀ b ∈ t, ¬ G.Adj a b) :
    extendZero s z ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ extendZero t y) = 0 := by
  classical
  calc
    extendZero s z ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ extendZero t y)
        = ∑ a : V, extendZero s z a * ((G.adjMatrix ℝ) *ᵥ extendZero t y) a := by simp [dotProduct]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro a ha
          by_cases has : a ∈ s
          · have hsum : ((G.adjMatrix ℝ) *ᵥ extendZero t y) a = 0 := by
              simp [Matrix.mulVec, dotProduct]
              apply Finset.sum_eq_zero
              intro b hb
              by_cases hbt : b ∈ t
              · have hn : ¬ G.Adj a b := hnadj a has b hbt
                simp [SimpleGraph.adjMatrix_apply, hbt, hn]
              · have : extendZero t y b = 0 := extendZero_mem_support t y b hbt
                simp [this, hbt]
            simp [hsum]
          · have : extendZero s z a = 0 := extendZero_mem_support s z a has
            simp [this]

/-! ## 6f. Walk counts for zeroed adjacency matrices.

A zeroed (restricted) adjacency matrix is the adjacency of the graph `subGraphOn G s`
(edges touching the complement of `s` deleted).  Powers of restricted matrices count
walks of that graph (mathlib's `adjMatrix_pow_apply_eq_card_walk`), which gives clean
walk-count comparisons: monotonicity (`restricted_pow_apply_self_le`), the deficit
lemma (`restricted_diag_deficit`), and confinement of closed walks. -/

/-- `G` with every edge touching the complement of `s` removed (so `sᶜ` becomes isolated). -/
def subGraphOn {V : Type*} (G : SimpleGraph V) (s : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ s ∧ v ∈ s
  symm := ⟨by intro u v h; exact ⟨G.adj_symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro u h; exact (G.loopless.irrefl u) h.1⟩

/-- the zeroed matrix is the adjacency of `subGraphOn`. -/
lemma restrictedMatrix_eq_subGraphOn_adj {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (s : Set V) :
    restrictedMatrix (G.adjMatrix ℝ) s = (subGraphOn G s).adjMatrix ℝ := by
  classical
  ext u v
  have hL : restrictedMatrix (G.adjMatrix ℝ) s u v =
      if (G.Adj u v ∧ u ∈ s ∧ v ∈ s) then 1 else 0 := by
    by_cases hadj : G.Adj u v <;> by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;>
      simp [restrictedMatrix, hadj, hu, hv, SimpleGraph.adjMatrix_apply]
  have hR : (subGraphOn G s).adjMatrix ℝ u v =
      if (G.Adj u v ∧ u ∈ s ∧ v ∈ s) then 1 else 0 := by
    rw [SimpleGraph.adjMatrix_apply]
    by_cases hadj : G.Adj u v <;> by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;>
      simp [hadj, hu, hv, subGraphOn]
  exact hL.trans hR.symm

/-- smaller sets give smaller subgraphs. -/
lemma subGraphOn_mono {V : Type*} (G : SimpleGraph V) {s t : Set V} (h : s ⊆ t) :
    subGraphOn G s ≤ subGraphOn G t := by
  intro u v h'
  exact ⟨h'.1, h h'.2.1, h h'.2.2⟩

/-- the vertices visited by a walk of `subGraphOn` starting inside the set stay in it. -/
lemma subGraphOn_support_mem {V : Type*} (G : SimpleGraph V) (s : Set V)
    {a b : V} (ha : a ∈ s) (p : (subGraphOn G s).Walk a b) :
    ∀ x ∈ p.support, x ∈ s := by
  classical
  induction p with
  | nil => intro x hx; simp at hx; rw [hx]; exact ha
  | cons h q ih =>
      intro x hx
      simp at hx
      rcases hx with rfl | hx
      · exact h.2.1
      · exact ih h.2.2 x hx

/-- lift a walk of `G` whose vertices lie in `t` to a walk of `subGraphOn G t`. -/
def liftWalk {V : Type*} (G : SimpleGraph V) (t : Set V) :
    ∀ {a b : V} (p : G.Walk a b), (∀ x ∈ p.support, x ∈ t) → (subGraphOn G t).Walk a b
  | _, _, SimpleGraph.Walk.nil, hw => (SimpleGraph.Walk.nil : (subGraphOn G t).Walk _ _)
  | _, _, SimpleGraph.Walk.cons' a0 v w h p, hw => by
      have hv : v ∈ t := hw v (by simp)
      have hpv : ∀ x ∈ p.support, x ∈ t := fun x hx => hw x (by simp [hx])
      exact SimpleGraph.Walk.cons ⟨h, hw a0 (by simp), hv⟩ (liftWalk G t p hpv)

/-- forget the membership conditions of a `subGraphOn` walk. -/
def unliftWalk {V : Type*} (G : SimpleGraph V) (t : Set V) :
    ∀ {a b : V} (p : (subGraphOn G t).Walk a b), G.Walk a b
  | _, _, SimpleGraph.Walk.nil => (SimpleGraph.Walk.nil : G.Walk _ _)
  | _, _, SimpleGraph.Walk.cons' a0 v w h p => SimpleGraph.Walk.cons h.1 (unliftWalk G t p)

/-- lifting preserves length. -/
lemma length_liftWalk {V : Type*} (G : SimpleGraph V) (t : Set V)
    {a b : V} (p : G.Walk a b) (hw : ∀ x ∈ p.support, x ∈ t) :
    (liftWalk G t p hw).length = p.length := by
  induction p with
  | nil => rfl
  | cons h q ih =>
      have hpv : ∀ x ∈ q.support, x ∈ t := fun x hx => hw x (by simp [hx])
      rw [SimpleGraph.Walk.length_cons]
      change (liftWalk G t q hpv).length + 1 = q.length + 1
      rw [ih hpv]

/-- unlifting preserves length. -/
lemma length_unliftWalk {V : Type*} (G : SimpleGraph V) (t : Set V)
    {a b : V} (p : (subGraphOn G t).Walk a b) :
    (unliftWalk G t p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h q ih =>
      rw [SimpleGraph.Walk.length_cons]
      change (unliftWalk G t q).length + 1 = q.length + 1
      rw [ih]

/-- lifting then unlifting is the identity. -/
lemma unlift_liftWalk {V : Type*} (G : SimpleGraph V) (t : Set V)
    {a b : V} (p : G.Walk a b) (hw : ∀ x ∈ p.support, x ∈ t) :
    unliftWalk G t (liftWalk G t p hw) = p := by
  induction p with
  | nil => rfl
  | cons h q ih =>
      have hpv : ∀ x ∈ q.support, x ∈ t := fun x hx => hw x (by simp [hx])
      simp [liftWalk, unliftWalk, ih hpv]

/-- the support of an unlifted walk is the support of the original walk. -/
lemma support_unliftWalk {V : Type*} (G : SimpleGraph V) (t : Set V)
    {a b : V} (p : (subGraphOn G t).Walk a b) :
    (unliftWalk G t p).support = p.support := by
  induction p with
  | nil => rfl
  | cons h q ih => simp [unliftWalk, ih]

/-- repeat a closed two-step walk `m` times. -/
def bounceWalk {V : Type*} {G : SimpleGraph V} {a : V} (two : G.Walk a a) : ℕ → G.Walk a a
  | 0 => SimpleGraph.Walk.nil
  | m + 1 => two.append (bounceWalk two m)

/-- length of a bounce walk. -/
lemma length_bounceWalk {V : Type*} {G : SimpleGraph V} {a : V}
    (two : G.Walk a a) (m : ℕ) :
    (bounceWalk two m).length = m * two.length := by
  induction m with
  | zero => simp [bounceWalk]
  | succ m ih =>
      rw [bounceWalk, SimpleGraph.Walk.length_append, ih]
      ring

/-- vertices of a bounce walk lie in any set containing the two-step walk's vertices. -/
lemma support_bounceWalk {V : Type*} {G : SimpleGraph V} {a : V}
    (s : Set V) (two : G.Walk a a) (m : ℕ) (hs : ∀ x ∈ two.support, x ∈ s) :
    ∀ x ∈ (bounceWalk two m).support, x ∈ s := by
  classical
  induction m with
  | zero =>
      intro x hx
      simp [bounceWalk] at hx
      rw [hx]
      exact hs a (SimpleGraph.Walk.start_mem_support two)
  | succ m ih =>
      intro x hx
      rw [bounceWalk] at hx
      rw [SimpleGraph.Walk.mem_support_append_iff] at hx
      rcases hx with hx | hx
      · exact hs x hx
      · exact ih x hx

/-- entries of powers of the restricted matrix count walks of the restricted graph. -/
lemma restricted_pow_apply_eq_card_walk {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : Set V) (a b : V) (k : ℕ) :
    (restrictedMatrix (G.adjMatrix ℝ) s ^ k) a b =
      (Fintype.card {p : (subGraphOn G s).Walk a b // p.length = k} : ℝ) := by
  classical
  rw [restrictedMatrix_eq_subGraphOn_adj]
  exact (SimpleGraph.adjMatrix_pow_apply_eq_card_walk (α := ℝ) (n := k) (u := a) (v := b)
    (G := subGraphOn G s))

/-- powers of entrywise-nonnegative matrices stay nonnegative. -/
lemma pow_nonneg_of_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : ∀ i j : V, 0 ≤ M i j) (k : ℕ) :
    ∀ i j : V, 0 ≤ (M ^ k) i j := by
  classical
  induction k with
  | zero => intro i j; by_cases hab : i = j <;> simp [hab]
  | succ k ih =>
      intro i j
      simp only [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun c hc => mul_nonneg (ih i c) (hM c j))

/-- entrywise monotonicity of powers of entrywise-nonnegative matrices. -/
lemma pow_entry_le_pow_entry_of_le {V : Type*} [Fintype V] [DecidableEq V]
    (M N : Matrix V V ℝ) (hMN : ∀ i j : V, M i j ≤ N i j)
    (hM : ∀ i j : V, 0 ≤ M i j) (hN : ∀ i j : V, 0 ≤ N i j) (k : ℕ) :
    ∀ i j : V, (M ^ k) i j ≤ (N ^ k) i j := by
  classical
  induction k with
  | zero =>
      intro i j
      by_cases h : i = j <;> simp [h]
  | succ k ih =>
      intro i j
      simp only [pow_succ, Matrix.mul_apply]
      apply Finset.sum_le_sum
      intro c hc
      have h1 := ih i c
      have h2 := hMN c j
      have h3 : 0 ≤ M c j := hM c j
      have h4 : 0 ≤ (N ^ k) i c := pow_nonneg_of_nonneg N hN k i c
      have h5 : 0 ≤ (N ^ k) i c - (M ^ k) i c := sub_nonneg.mpr h1
      have h6 : 0 ≤ N c j - M c j := sub_nonneg.mpr h2
      nlinarith

/-- walks of the smaller restriction inject into those of the larger one. -/
lemma restricted_pow_apply_self_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {s t : Set V} (hs : s ⊆ t) (k : ℕ) (a b : V) :
    (restrictedMatrix (G.adjMatrix ℝ) s ^ k) a b ≤
      (restrictedMatrix (G.adjMatrix ℝ) t ^ k) a b := by
  classical
  have hMN : ∀ i j : V, restrictedMatrix (G.adjMatrix ℝ) s i j ≤
      restrictedMatrix (G.adjMatrix ℝ) t i j := by
    intro i j
    by_cases h : i ∈ s ∧ j ∈ s
    · have hi : i ∈ t := hs h.1
      have hj : j ∈ t := hs h.2
      by_cases hadj : G.Adj i j <;> simp [restrictedMatrix, h, hi, hj, hadj]
    · have hle : 0 ≤ restrictedMatrix (G.adjMatrix ℝ) t i j :=
        restrictedMatrix_nonneg (G.adjMatrix ℝ) (adjMatrix_nonneg_any G) t i j
      simp [restrictedMatrix, h]
      exact hle
  exact pow_entry_le_pow_entry_of_le (restrictedMatrix (G.adjMatrix ℝ) s)
    (restrictedMatrix (G.adjMatrix ℝ) t) hMN
    (restrictedMatrix_nonneg (G.adjMatrix ℝ) (adjMatrix_nonneg_any G) s)
    (restrictedMatrix_nonneg (G.adjMatrix ℝ) (adjMatrix_nonneg_any G) t) k a b

/-- an extra closed walk through a deleted vertex. -/
lemma exists_extra_closed_walk {V : Type*} (G : SimpleGraph V) {s t : Set V}
    (hs : s ⊆ t) (a : V) (ha : a ∈ s) (r : ℕ)
    (hdel : ∃ z : V, z ∉ s ∧ z ∈ t ∧
      ∃ p : G.Walk a z, p.length ≤ r ∧ ∀ x ∈ p.support, x ∈ t)
    (hpad : ∃ y : V, G.Adj y a ∧ y ∈ t) :
    ∃ w : G.Walk a a,
      w.length = 2 * r ∧
      (∃ z : V, z ∈ w.support ∧ z ∉ s) ∧
      ∀ x ∈ w.support, x ∈ t := by
  classical
  rcases hdel with ⟨z, hzs, hzt, p, hplen, hpt⟩
  rcases hpad with ⟨y, hyadj, hyt⟩
  let ℓ := p.length
  let two : G.Walk a a := SimpleGraph.Walk.cons hyadj.symm
    (SimpleGraph.Walk.cons hyadj (SimpleGraph.Walk.nil : G.Walk a a))
  have htwo_len : two.length = 2 := by simp [two]
  have htwo_sup : ∀ x ∈ two.support, x ∈ t := by
    intro x hx
    have hmem : x = a ∨ (x = y ∨ x = a) := by
      simpa [two] using hx
    rcases hmem with hxa | hrest
    · rw [hxa]
      exact hs ha
    · rcases hrest with hxy | hxa2
      · rw [hxy]
        exact hyt
      · rw [hxa2]
        exact hs ha
  have hb_len : ∀ m : ℕ, (bounceWalk two m).length = 2 * m := by
    intro m
    rw [length_bounceWalk, htwo_len]
    ring
  have hb_sup_t : ∀ m : ℕ, ∀ x ∈ (bounceWalk two m).support, x ∈ t :=
    fun m => support_bounceWalk t two m htwo_sup
  let w : G.Walk a a := (p.append p.reverse).append (bounceWalk two (r - ℓ))
  refine ⟨w, ?_, ⟨z, ?_, hzs⟩, ?_⟩
  · dsimp [w]
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse, hb_len]
    have hpl : p.length = ℓ := rfl
    omega
  · dsimp [w]
    rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    exact SimpleGraph.Walk.end_mem_support p
  · intro x hx
    rw [SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hx
      rcases hx with hx | hx
      · exact hpt x hx
      · have : x ∈ p.support := by
          simpa [SimpleGraph.Walk.support_reverse] using hx
        exact hpt x this
    · exact hb_sup_t (r - ℓ) x hx

/-- the diagonal of a `2r`-power of a restricted matrix is at least `1` larger on a
superset, provided there is an extra closed walk through a deleted vertex. -/
lemma restricted_diag_deficit {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {s t : Set V} (hs : s ⊆ t) (r : ℕ) (a : V) (ha : a ∈ s)
    (hdel : ∃ z : V, z ∉ s ∧ z ∈ t ∧
      ∃ p : G.Walk a z, p.length ≤ r ∧ ∀ x ∈ p.support, x ∈ t)
    (hpad : ∃ y : V, G.Adj y a ∧ y ∈ t) :
    (restrictedMatrix (G.adjMatrix ℝ) s ^ (2 * r)) a a + 1 ≤
      (restrictedMatrix (G.adjMatrix ℝ) t ^ (2 * r)) a a := by
  classical
  let As := {p : (subGraphOn G s).Walk a a // p.length = 2 * r}
  let Bt := {p : (subGraphOn G t).Walk a a // p.length = 2 * r}
  let f : As → Bt := fun p => ⟨p.1.mapLe (subGraphOn_mono G hs), by
    simpa [SimpleGraph.Walk.length_mapLe] using p.2⟩
  have hinj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact (SimpleGraph.Walk.map_injective_of_injective
      (f := SimpleGraph.Hom.ofLE (subGraphOn_mono G hs)) (by intro u v huv; simpa using huv) a a)
      (Subtype.ext_iff.mp hpq)
  rcases exists_extra_closed_walk G hs a ha r hdel hpad with ⟨w, hwlen, hmid, hwt⟩
  rcases hmid with ⟨z, hzw, hzs⟩
  let wl := liftWalk G t w hwt
  have hwl_len : wl.length = 2 * r := by
    dsimp [wl]
    rw [length_liftWalk]
    exact hwlen
  let b : Bt := ⟨wl, hwl_len⟩
  have hb_not_range : b ∉ Set.range f := by
    intro hb
    rw [Set.mem_range] at hb
    rcases hb with ⟨x, hx⟩
    have hxs : ∀ y ∈ (f x).1.support, y ∈ s := by
      intro y hy
      have hy' : y ∈ x.1.support := by
        simpa [f] using hy
      exact subGraphOn_support_mem G s ha x.1 y hy'
    have hz_fx : z ∈ (f x).1.support := by
      have heq : (f x).1.support = b.1.support := by
        exact congrArg (fun q : Bt => q.1.support) hx
      rw [heq]
      dsimp [b, wl]
      have hun : unliftWalk G t (liftWalk G t w hwt) = w := unlift_liftWalk G t w hwt
      have hs' : (liftWalk G t w hwt).support = w.support := by
        calc
          (liftWalk G t w hwt).support =
              (unliftWalk G t (liftWalk G t w hwt)).support := by
            exact (support_unliftWalk G t (liftWalk G t w hwt)).symm
          _ = w.support := by rw [hun]
      rw [hs']
      exact hzw
    exact hzs (hxs z hz_fx)
  let g : Option As → Bt := fun o => match o with | some p => f p | none => b
  have hginj : Function.Injective g := by
    intro o o' ho
    cases o with
    | none =>
        cases o' with
        | none => rfl
        | some q =>
            exfalso
            exact hb_not_range ⟨q, by simpa [g] using ho.symm⟩
    | some p =>
        cases o' with
        | none =>
            exfalso
            exact hb_not_range ⟨p, by simpa [g] using ho⟩
        | some q =>
            have hpq : f p = f q := by simpa [g] using ho
            exact congrArg some (hinj hpq)
  have hcard : Fintype.card As + 1 ≤ Fintype.card Bt := by
    have hc1 : Fintype.card (Option As) = Fintype.card As + 1 := by simp
    rw [← hc1]
    exact Fintype.card_le_of_injective g hginj
  rw [restricted_pow_apply_eq_card_walk, restricted_pow_apply_eq_card_walk]
  norm_num
  exact_mod_cast hcard


/-- the Rayleigh bound: `x ⬝ A x ≤ topVal A * (x⬝x)` for Hermitian `A`. -/
lemma quad_le_topVal_pf {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (hW : (Finset.univ : Finset W).Nonempty) (x : W → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ topVal A hA * (x ⬝ᵥ x) := by
  classical
  rcases exists_topVal_index A hA hW with ⟨j, hj, hjt⟩
  rw [← hjt]
  exact quad_le_of_eigenvalues_le_any A hA hj x

/-- powers of an eigenvector are eigenvectors of the power. -/
lemma mulVec_pow_eigen_pf {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (k : ℕ) (j : W) :
    (A ^ k) *ᵥ (hA.eigenvectorBasis j).ofLp =
      ((hA.eigenvalues j) ^ k) • (hA.eigenvectorBasis j).ofLp := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (A ^ (k + 1)) *ᵥ (hA.eigenvectorBasis j).ofLp
            = (A ^ k) *ᵥ (A *ᵥ (hA.eigenvectorBasis j).ofLp) := by
              rw [pow_succ, Matrix.mulVec_mulVec]
        _ = (A ^ k) *ᵥ (((hA.eigenvalues j)) • (hA.eigenvectorBasis j).ofLp) := by
              rw [bfun_eigen A hA j]
        _ = ((hA.eigenvalues j)) • ((A ^ k) *ᵥ (hA.eigenvectorBasis j).ofLp) := by
              rw [Matrix.mulVec_smul]
        _ = ((hA.eigenvalues j)) • (((hA.eigenvalues j) ^ k) • (hA.eigenvectorBasis j).ofLp) := by
              rw [ih]
        _ = ((hA.eigenvalues j) ^ (k + 1)) • (hA.eigenvectorBasis j).ofLp := by
              funext w
              simp [Pi.smul_apply, pow_succ]
              ring

/-- the largest eigenvalue of an even power is the even power of the largest eigenvalue. -/
lemma topVal_even_pow_pf {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (hnonneg : ∀ i j : W, 0 ≤ A i j)
    (hW : (Finset.univ : Finset W).Nonempty) (k : ℕ) :
    topVal (A ^ (2 * k)) (hA.pow (2 * k)) = (topVal A hA) ^ (2 * k) := by
  classical
  let P := A ^ (2 * k)
  let hP : P.IsHermitian := hA.pow (2 * k)
  have htop : 0 ≤ topVal A hA := topVal_nonneg_of_nonneg A hA hnonneg hW
  apply le_antisymm
  · -- topVal(P) ≤ topVal(A)^{2k}
    rcases exists_topVal_index P hP hW with ⟨i0, hi0, hi0v⟩
    let u : W → ℝ := (hP.eigenvectorBasis i0).ofLp
    have hu1 : u ⬝ᵥ u = 1 := by simpa [u] using bfun_unit P hP i0
    have heig : P *ᵥ u = (hP.eigenvalues i0) • u := by simpa [u] using bfun_eigen P hP i0
    have hquad : u ⬝ᵥ (P *ᵥ u) = hP.eigenvalues i0 := by
      rw [heig]
      simp [Pi.smul_apply, hu1]
    have hle : u ⬝ᵥ (P *ᵥ u) ≤ (topVal A hA) ^ (2 * k) * (u ⬝ᵥ u) := by
      rw [quad_pow_expand A hA (2 * k) u]
      calc
        (∑ j : W, (hA.eigenvalues j) ^ (2 * k) * (u ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2)
            ≤ (∑ j : W, (topVal A hA) ^ (2 * k) * (u ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2) := by
              apply Finset.sum_le_sum
              intro j hj
              have hterm : (hA.eigenvalues j) ^ (2 * k) ≤ (topVal A hA) ^ (2 * k) := by
                have hd : |hA.eigenvalues j| ≤ topVal A hA := top_eigenvalue_dominates A hA hnonneg hW j
                have heven : (hA.eigenvalues j) ^ (2 * k) = |hA.eigenvalues j| ^ (2 * k) := by
                  have hp : 0 ≤ (hA.eigenvalues j) ^ (2 * k) := by
                    rw [pow_mul]
                    exact pow_nonneg (sq_nonneg (hA.eigenvalues j)) k
                  rw [← abs_of_nonneg hp]
                  rw [abs_pow]
                rw [heven]
                exact pow_le_pow_left₀ (abs_nonneg _) hd (2 * k)
              exact mul_le_mul_of_nonneg_right hterm (sq_nonneg _)
        _ = (topVal A hA) ^ (2 * k) * (u ⬝ᵥ u) := by
              calc
                (∑ j : W, (topVal A hA) ^ (2 * k) * (u ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2)
                    = (∑ j : W, (u ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2 * (topVal A hA) ^ (2 * k)) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
                _ = (∑ j : W, (u ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2) * (topVal A hA) ^ (2 * k) := by
                      exact (Finset.sum_mul (s := (Finset.univ : Finset W))
                        (f := fun j : W => (u ⬝ᵥ (hA.eigenvectorBasis j).ofLp) ^ 2)
                        (a := (topVal A hA) ^ (2 * k))).symm
                _ = (u ⬝ᵥ u) * (topVal A hA) ^ (2 * k) := by
                      rw [norm_expand A hA u]
                _ = (topVal A hA) ^ (2 * k) * (u ⬝ᵥ u) := by ring
    have htopP_le : topVal P hP ≤ (topVal A hA) ^ (2 * k) := by
      calc
        topVal P hP = hP.eigenvalues i0 := by
              rw [← hi0v]
        _ = u ⬝ᵥ (P *ᵥ u) := by
              rw [← hquad]
        _ ≤ (topVal A hA) ^ (2 * k) * (u ⬝ᵥ u) := hle
        _ = (topVal A hA) ^ (2 * k) := by rw [hu1, mul_one]
    simpa [P] using htopP_le
  · -- topVal(A)^{2k} ≤ topVal(P)
    rcases exists_topVal_index A hA hW with ⟨j, hj, hjt⟩
    let v : W → ℝ := (hA.eigenvectorBasis j).ofLp
    have hv1 : v ⬝ᵥ v = 1 := by simpa [v] using bfun_unit A hA j
    have hpowv : (A ^ (2 * k)) *ᵥ v = ((hA.eigenvalues j) ^ (2 * k)) • v := by
      simpa [v] using mulVec_pow_eigen_pf A hA (2 * k) j
    have hquadv : v ⬝ᵥ ((A ^ (2 * k)) *ᵥ v) = (hA.eigenvalues j) ^ (2 * k) := by
      rw [hpowv]
      simp [Pi.smul_apply, hv1]
    have hray : v ⬝ᵥ ((A ^ (2 * k)) *ᵥ v) ≤ topVal (A ^ (2 * k)) (hA.pow (2 * k)) * (v ⬝ᵥ v) := by
      exact quad_le_topVal_pf (A ^ (2 * k)) (hA.pow (2 * k)) hW v
    have hle2 : (topVal A hA) ^ (2 * k) ≤ topVal (A ^ (2 * k)) (hA.pow (2 * k)) := by
      calc
        (topVal A hA) ^ (2 * k) = (hA.eigenvalues j) ^ (2 * k) := by rw [hjt]
        _ = v ⬝ᵥ ((A ^ (2 * k)) *ᵥ v) := hquadv.symm
        _ ≤ topVal (A ^ (2 * k)) (hA.pow (2 * k)) * (v ⬝ᵥ v) := hray
        _ = topVal (A ^ (2 * k)) (hA.pow (2 * k)) := by rw [hv1, mul_one]
    simpa [P] using hle2

/-- restricted powers are entrywise nonnegative. -/
lemma restricted_pow_nonneg_pf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : Set V) (k : ℕ) :
    ∀ a b : V, 0 ≤ (restrictedMatrix (G.adjMatrix ℝ) s ^ k) a b := by
  classical
  exact pow_nonneg_of_nonneg (restrictedMatrix (G.adjMatrix ℝ) s)
    (restrictedMatrix_nonneg (G.adjMatrix ℝ) (adjMatrix_nonneg_any G) s) k



/-- |x| has the same norm as x and does not decrease `xᵀAx` for nonnegative `A`. -/
lemma quad_abs_le_quad_abs {W : Type*} [Fintype W] (A : Matrix W W ℝ)
    (hnonneg : ∀ i j : W, 0 ≤ A i j) (x : W → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ (fun i : W => |x i|) ⬝ᵥ (A *ᵥ fun i : W => |x i|) := by
  classical
  exact quad_self_le_quad_abs A hnonneg x

/-- `Σ_a w_a² E_aa ≤ w⬝Ew` for nonnegative `w` and entrywise-nonnegative `E`. -/
lemma quad_diag_le_pf {W : Type*} [Fintype W] (E : Matrix W W ℝ)
    (hE : ∀ a b : W, 0 ≤ E a b) (w : W → ℝ) (hw : ∀ a : W, 0 ≤ w a) :
    (∑ a : W, (w a) ^ 2 * E a a) ≤ w ⬝ᵥ (E *ᵥ w) := by
  classical
  calc
    (∑ a : W, (w a) ^ 2 * E a a) ≤ ∑ a : W, w a * (∑ b : W, E a b * w b) := by
      apply Finset.sum_le_sum
      intro a ha
      have hwpos : 0 ≤ w a := hw a
      calc
        (w a) ^ 2 * E a a = w a * (E a a * w a) := by ring
        _ ≤ w a * (∑ b : W, E a b * w b) := by
          apply mul_le_mul_of_nonneg_left _ hwpos
          have hb0 : E a a * w a ≤ ∑ b : W, E a b * w b := by
            exact Finset.single_le_sum (s := (Finset.univ : Finset W))
              (f := fun b : W => E a b * w b)
              (fun b hb => mul_nonneg (hE a b) (hw b)) (a := a) (Finset.mem_univ a)
          exact hb0
    _ = w ⬝ᵥ (E *ᵥ w) := by
          simp [dotProduct, Matrix.mulVec]


/-- dot product is right-additive. -/
lemma dot_add_right_pf {ι : Type*} [Fintype ι] (x y z : ι → ℝ) :
    x ⬝ᵥ (y + z) = x ⬝ᵥ y + x ⬝ᵥ z := by
  classical
  rw [dotProduct, dotProduct, dotProduct]
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- dot product is right-subtractive. -/
lemma dot_sub_right_pf {ι : Type*} [Fintype ι] (x y z : ι → ℝ) :
    x ⬝ᵥ (y - z) = x ⬝ᵥ y - x ⬝ᵥ z := by
  classical
  rw [dotProduct, dotProduct, dotProduct]
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma quad_e_a_pf {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ) (a : W) :
    ((fun w : W => if w = a then (1 : ℝ) else 0) ⬝ᵥ (A *ᵥ (fun w : W => if w = a then (1 : ℝ) else 0))) = A a a := by
  classical
  simp [Matrix.mulVec, dotProduct, Finset.sum_ite_eq']

/-- `e_a⬝e_a = 1`. -/
lemma norm_e_a_pf {W : Type*} [Fintype W] [DecidableEq W] (a : W) :
    ((fun w : W => if w = a then (1 : ℝ) else 0) ⬝ᵥ (fun w : W => if w = a then (1 : ℝ) else 0)) = 1 := by
  classical
  simp [dotProduct, Finset.sum_ite_eq']

/-- rows of a restricted matrix power vanish outside the set (positive powers). -/
lemma restricted_pow_row_zero_pf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : Set V) (k : ℕ) (hk : 1 ≤ k) (a b : V) (ha : a ∉ s) :
    (restrictedMatrix (G.adjMatrix ℝ) s ^ k) a b = 0 := by
  classical
  cases k with
  | zero => omega
  | succ k =>
      rw [pow_succ']
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro c hc
      rw [restrictedMatrix]
      simp [ha]

/-- if a restriction's even power has one extra closed walk per vertex on the diagonal,
then its top eigenvalue is at least one larger. -/
lemma top_eigen_gap_t {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : (G.adjMatrix ℝ).IsHermitian) {s t : Set V} (hs : s ⊆ t) (k : ℕ) (hk : 1 ≤ k)
    (hV : (Finset.univ : Finset V).Nonempty) (hsne : ∃ a : V, a ∈ s)
    (hdiag : ∀ a : V, a ∈ s → (restrictedMatrix (G.adjMatrix ℝ) s ^ (2 * k)) a a + 1 ≤
      (restrictedMatrix (G.adjMatrix ℝ) t ^ (2 * k)) a a) :
    topVal (restrictedMatrix (G.adjMatrix ℝ) t ^ (2 * k))
        ((restrictedMatrix_isHermitian (G.adjMatrix ℝ) hG t).pow (2 * k))
      ≥ topVal (restrictedMatrix (G.adjMatrix ℝ) s ^ (2 * k))
          ((restrictedMatrix_isHermitian (G.adjMatrix ℝ) hG s).pow (2 * k)) + 1 := by
  classical
  let Rs := restrictedMatrix (G.adjMatrix ℝ) s
  let Rt := restrictedMatrix (G.adjMatrix ℝ) t
  let M := Rs ^ (2 * k)
  let N := Rt ^ (2 * k)
  let hM : M.IsHermitian := (restrictedMatrix_isHermitian (G.adjMatrix ℝ) hG s).pow (2 * k)
  let hN : N.IsHermitian := (restrictedMatrix_isHermitian (G.adjMatrix ℝ) hG t).pow (2 * k)
  have hMN : ∀ i j : V, M i j ≤ N i j := by
    intro i j
    simpa [M, N] using restricted_pow_apply_self_le G hs (2 * k) i j
  have hMnonneg : ∀ i j : V, 0 ≤ M i j := by
    intro i j
    simpa [M] using restricted_pow_nonneg_pf G s (2 * k) i j
  have hNnonneg : ∀ i j : V, 0 ≤ N i j := by
    intro i j
    simpa [N] using restricted_pow_nonneg_pf G t (2 * k) i j
  by_cases hμ0 : topVal M hM = 0
  · -- trivial case: M has top 0
    rcases hsne with ⟨a, has⟩
    let e : V → ℝ := fun w => if w = a then 1 else 0
    have hdiagTop : ∀ (P : Matrix V V ℝ) (hP : P.IsHermitian), P a a ≤ topVal P hP := by
      intro P hP
      have h := quad_le_topVal_pf P hP hV e
      have hA : e ⬝ᵥ (P *ᵥ e) = P a a := by simpa [e] using quad_e_a_pf P a
      have hB : e ⬝ᵥ e = 1 := by simpa [e] using norm_e_a_pf a
      have h2 : P a a ≤ topVal P hP * (e ⬝ᵥ e) := by
        rw [hA] at h
        simpa using h
      have h2' : P a a ≤ topVal P hP := by
        rw [hB] at h2
        simpa using h2
      exact h2'
    have hMaa0 : M a a = 0 := by
      have hle : M a a ≤ topVal M hM := hdiagTop M hM
      have hge0 : 0 ≤ M a a := hMnonneg a a
      have hle0 : M a a ≤ 0 := by simpa [hμ0] using hle
      linarith
    have hNaa : 1 ≤ N a a := by
      have hd := hdiag a has
      change M a a + 1 ≤ N a a at hd
      simpa [hMaa0] using hd
    calc
      topVal M hM + 1 = 1 := by rw [hμ0]; norm_num
      _ ≤ N a a := hNaa
      _ ≤ topVal N hN := hdiagTop N hN
  · -- main case
    rcases exists_topVal_index M hM hV with ⟨i0, hi0, hi0v⟩
    let u : V → ℝ := (hM.eigenvectorBasis i0).ofLp
    have hu1 : u ⬝ᵥ u = 1 := by simpa [u] using bfun_unit M hM i0
    have hμ : hM.eigenvalues i0 = topVal M hM := hi0v
    have hμpos : 0 < topVal M hM := by
      rcases hsne with ⟨a, has⟩
      let e : V → ℝ := fun w => if w = a then 1 else 0
      have h := quad_le_topVal_pf M hM hV e
      have hA : e ⬝ᵥ (M *ᵥ e) = M a a := by simpa [e] using quad_e_a_pf M a
      have hB : e ⬝ᵥ e = 1 := by simpa [e] using norm_e_a_pf a
      have h2 : M a a ≤ topVal M hM * (e ⬝ᵥ e) := by
        rw [hA] at h
        simpa using h
      have h2' : M a a ≤ topVal M hM := by
        rw [hB] at h2
        simpa using h2
      have hge : 0 ≤ topVal M hM := by
        have hle : 0 ≤ M a a := hMnonneg a a
        exact le_trans hle h2'
      exact lt_of_le_of_ne hge (Ne.symm hμ0)
    have heig : M *ᵥ u = (hM.eigenvalues i0) • u := by simpa [u] using bfun_eigen M hM i0
    have hsupport : ∀ a : V, a ∉ s → u a = 0 := by
      intro a has
      have hrow : (M *ᵥ u) a = 0 := by
        rw [Matrix.mulVec]
        apply Finset.sum_eq_zero
        intro b hb
        have hMab : M a b = 0 := by
          simpa [M] using restricted_pow_row_zero_pf G s (2 * k) (by omega) a b has
        simp [hMab]
      have hmu : (M *ᵥ u) a = (hM.eigenvalues i0) * u a := by
        rw [heig]
        simp [Pi.smul_apply]
      rw [hmu] at hrow
      exact (mul_eq_zero.mp hrow).resolve_left (ne_of_gt (by rw [hμ]; exact hμpos))
    let w : V → ℝ := fun a => |u a|
    have hw1 : w ⬝ᵥ w = 1 := by
      calc
        w ⬝ᵥ w = ∑ a : V, (u a) ^ 2 := by
              simp [w, dotProduct, pow_two]
        _ = u ⬝ᵥ u := by simp [dotProduct, pow_two]
        _ = 1 := hu1
    have hwM : u ⬝ᵥ (M *ᵥ u) ≤ w ⬝ᵥ (M *ᵥ w) := by
      exact quad_self_le_quad_abs M hMnonneg u
    have hdiagE : ∀ a : V, a ∈ s → 1 ≤ N a a - M a a := by
      intro a has
      have hd := hdiag a has
      change M a a + 1 ≤ N a a at hd
      linarith
    have hEw : (∑ a : V, (w a) ^ 2) ≤ w ⬝ᵥ ((N - M) *ᵥ w) := by
      have hEN : ∀ a b : V, 0 ≤ (N - M) a b := by
        intro a b
        dsimp [N, M]
        exact sub_nonneg.mpr (hMN a b)
      have hquad := quad_diag_le_pf (N - M) hEN w (fun a => abs_nonneg (u a))
      have hpart : (∑ a : V, (w a) ^ 2) ≤ ∑ a : V, (w a) ^ 2 * (N - M) a a := by
        calc
          (∑ a : V, (w a) ^ 2) = ∑ a : V, (w a) ^ 2 * 1 := by simp
          _ ≤ ∑ a : V, (w a) ^ 2 * (N - M) a a := by
                apply Finset.sum_le_sum
                intro a ha
                have hw2 : 0 ≤ (w a) ^ 2 := sq_nonneg (w a)
                by_cases has : a ∈ s
                · have h1 : 1 ≤ (N - M) a a := hdiagE a has
                  exact mul_le_mul_of_nonneg_left h1 hw2
                · have hu0 : u a = 0 := hsupport a has
                  have hw0 : w a = 0 := by simp [w, hu0]
                  simp [hw0]
      exact le_trans hpart hquad
    have hwM_eq : w ⬝ᵥ (M *ᵥ w) = topVal M hM := by
      have hle_wM : w ⬝ᵥ (M *ᵥ w) ≤ topVal M hM * (w ⬝ᵥ w) := quad_le_topVal_pf M hM hV w
      have h_uM : u ⬝ᵥ (M *ᵥ u) = topVal M hM := by
        calc
          u ⬝ᵥ (M *ᵥ u) = (hM.eigenvalues i0) * (u ⬝ᵥ u) := by
                rw [heig]
                simp [Pi.smul_apply]
          _ = topVal M hM := by rw [hμ, hu1, mul_one]
      apply le_antisymm
      · rw [hw1] at hle_wM
        simpa using hle_wM
      · calc
          topVal M hM = u ⬝ᵥ (M *ᵥ u) := h_uM.symm
          _ ≤ w ⬝ᵥ (M *ᵥ w) := hwM
    have hgoal : topVal M hM + 1 ≤ w ⬝ᵥ (N *ᵥ w) := by
      have hEw1 : (1 : ℝ) ≤ w ⬝ᵥ ((N - M) *ᵥ w) := by
        calc
          (1 : ℝ) = w ⬝ᵥ w := hw1.symm
          _ = ∑ a : V, (w a) ^ 2 := by simp [dotProduct, pow_two]
          _ ≤ w ⬝ᵥ ((N - M) *ᵥ w) := hEw
      have hsplit : w ⬝ᵥ (M *ᵥ w) + w ⬝ᵥ ((N - M) *ᵥ w) = w ⬝ᵥ (N *ᵥ w) := by
        calc
          w ⬝ᵥ (M *ᵥ w) + w ⬝ᵥ ((N - M) *ᵥ w)
              = w ⬝ᵥ (M *ᵥ w) + (w ⬝ᵥ (N *ᵥ w) - w ⬝ᵥ (M *ᵥ w)) := by
                  rw [Matrix.sub_mulVec]
                  rw [dot_sub_right_pf w (N *ᵥ w) (M *ᵥ w)]
          _ = w ⬝ᵥ (N *ᵥ w) := by ring
      calc
        topVal M hM + 1 ≤ w ⬝ᵥ (M *ᵥ w) + w ⬝ᵥ ((N - M) *ᵥ w) := by
              rw [hwM_eq]
              linarith
        _ = w ⬝ᵥ (N *ᵥ w) := hsplit
    have hrayN : w ⬝ᵥ (N *ᵥ w) ≤ topVal N hN := by
      have h := quad_le_topVal_pf N hN hV w
      rw [hw1] at h
      simpa using h
    calc
      topVal M hM + 1 ≤ topVal N hN := by linarith

/-- per-vertex reduction of the largest eigenvalue of a restricted even power. -/
lemma reduce_eigen_t {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {s t : Set V} (hs : s ⊆ t) (k : ℕ) (hk : 1 ≤ k) (hV : (Finset.univ : Finset V).Nonempty)
    (hsne : ∃ a : V, a ∈ s)
    (hdiag : ∀ a : V, a ∈ s → (restrictedMatrix (G.adjMatrix ℝ) s ^ (2 * k)) a a + 1 ≤
      (restrictedMatrix (G.adjMatrix ℝ) t ^ (2 * k)) a a) :
    (localTop (G.adjMatrix ℝ) (adj_isHerm_any G) s) ^ (2 * k) + 1 ≤
      (localTop (G.adjMatrix ℝ) (adj_isHerm_any G) t) ^ (2 * k) := by
  classical
  have hg := top_eigen_gap_t G (adj_isHerm_any G) hs k hk hV hsne hdiag
  have hconvS : topVal (restrictedMatrix (G.adjMatrix ℝ) s ^ (2 * k))
      ((restrictedMatrix_isHermitian (G.adjMatrix ℝ) (adj_isHerm_any G) s).pow (2 * k))
      = (localTop (G.adjMatrix ℝ) (adj_isHerm_any G) s) ^ (2 * k) := by
    rw [localTop]
    exact topVal_even_pow_pf (restrictedMatrix (G.adjMatrix ℝ) s)
      (restrictedMatrix_isHermitian (G.adjMatrix ℝ) (adj_isHerm_any G) s)
      (restrictedMatrix_nonneg (G.adjMatrix ℝ) (adjMatrix_nonneg_any G) s) hV k
  have hconvT : topVal (restrictedMatrix (G.adjMatrix ℝ) t ^ (2 * k))
      ((restrictedMatrix_isHermitian (G.adjMatrix ℝ) (adj_isHerm_any G) t).pow (2 * k))
      = (localTop (G.adjMatrix ℝ) (adj_isHerm_any G) t) ^ (2 * k) := by
    rw [localTop]
    exact topVal_even_pow_pf (restrictedMatrix (G.adjMatrix ℝ) t)
      (restrictedMatrix_isHermitian (G.adjMatrix ℝ) (adj_isHerm_any G) t)
      (restrictedMatrix_nonneg (G.adjMatrix ℝ) (adjMatrix_nonneg_any G) t) hV k
  rw [← hconvS, ← hconvT]
  exact hg

/-- for `u` with `lam < ballTop G u r`, the zero-extension of a top eigenvector of the
`r`-ball is a vector supported inside the ball with Rayleigh quotient `> lam`. -/
lemma ball_eigen_ext_support {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {lam : ℝ} {u : V} {r : ℕ} (hu : lam < ballTop G u r) :
    ∃ x : V → ℝ, (∀ w : V, w ∉ ballSet G u r → x w = 0) ∧ x ≠ 0 ∧
      lam * (x ⬝ᵥ x) < x ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ x) := by
  classical
  let hBall := adj_isHerm_any (ballGraph G u r)
  have htop : ∃ j : ballSet G u r, hBall.eigenvalues j = ballTop G u r := by
    change ∃ j : ballSet G u r,
      (adj_isHerm_any (ballGraph G u r)).eigenvalues j = ballTop G u r
    exact topVal_is_value ((ballGraph G u r).adjMatrix ℝ) (adj_isHerm_any (ballGraph G u r))
      (ballFinset_nonempty G u r)
  let j := Classical.choose htop
  have hj : hBall.eigenvalues j = ballTop G u r := Classical.choose_spec htop
  let f : ballSet G u r → ℝ := (hBall.eigenvectorBasis j).ofLp
  let x : V → ℝ := extendZero (ballSet G u r) f
  have hf0 : f ≠ 0 := by
    intro hf0
    have hd := bfun_unit ((ballGraph G u r).adjMatrix ℝ) hBall j
    have hd' : f ⬝ᵥ f = 1 := by
      dsimp [f]
      exact hd
    rw [hf0] at hd'
    have hz : (0 : ballSet G u r → ℝ) ⬝ᵥ (0 : ballSet G u r → ℝ) = 0 := by simp [dotProduct]
    rw [hz] at hd'
    norm_num at hd'
  have hfe : ((ballGraph G u r).adjMatrix ℝ) *ᵥ f = (hBall.eigenvalues j) • f := by
    dsimp [f]
    exact bfun_eigen ((ballGraph G u r).adjMatrix ℝ) hBall j
  refine ⟨x, ?_, ?_, ?_⟩
  · intro w hw
    exact extendZero_apply_not_mem (ballSet G u r) f hw
  · intro hx0
    apply hf0
    funext v
    have hx0v := congrFun hx0 v
    have hvv : (v : V) ∈ ballSet G u r := v.2
    have hxv : x (v : V) = f v := by
      dsimp [x]
      exact extendZero_apply_mem (ballSet G u r) f hvv
    rw [← hxv]
    exact hx0v
  · have hquad := extendZero_quad ((G.adjMatrix ℝ)) (ballSet G u r) f
    have heq : (fun i j : ballSet G u r => (G.adjMatrix ℝ) i.1 j.1)
        = (ballGraph G u r).adjMatrix ℝ := by
      ext i j
      by_cases hadj : G.Adj i.1 j.1
      · simp [SimpleGraph.adjMatrix_apply, hadj, ball_adj_iff]
      · simp [SimpleGraph.adjMatrix_apply, hadj, ball_adj_iff]
    have hquadx : x ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ x)
        = f ⬝ᵥ (((ballGraph G u r).adjMatrix ℝ) *ᵥ f) := by
      dsimp [x]
      rw [heq] at hquad
      exact hquad
    have hquadf : f ⬝ᵥ (((ballGraph G u r).adjMatrix ℝ) *ᵥ f)
        = (hBall.eigenvalues j) * (f ⬝ᵥ f) := by
      rw [hfe]
      simp [Pi.smul_apply, mul_comm, mul_assoc]
    have hnorm : x ⬝ᵥ x = f ⬝ᵥ f := by
      dsimp [x]
      exact extendZero_dot_self (ballSet G u r) f
    have hgt : lam * (f ⬝ᵥ f) < (hBall.eigenvalues j) * (f ⬝ᵥ f) := by
      have hfpos : 0 < f ⬝ᵥ f := by
        have hle : 0 ≤ f ⬝ᵥ f := by
          rw [dotProduct]
          exact Finset.sum_nonneg (fun i hi => by simpa [pow_two] using sq_nonneg (f i))
        have hne : f ⬝ᵥ f ≠ 0 := by
          intro hz
          apply hf0
          funext i
          have hsqsum : (∑ j0 : ballSet G u r, (f j0) ^ 2) = 0 := by
            simpa [dotProduct, pow_two, mul_comm] using hz
          have hzsq : (f i) ^ 2 = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset (ballSet G u r)))
              (f := fun j0 => (f j0) ^ 2) (fun a ha => sq_nonneg (f a))).mp hsqsum i (Finset.mem_univ i)
          exact sq_eq_zero_iff.mp hzsq
        exact lt_of_le_of_ne hle (Ne.symm hne)
      have hjlt : lam < hBall.eigenvalues j := by
        rw [hj]
        exact hu
      exact mul_lt_mul_of_pos_right hjlt hfpos
    calc
      lam * (x ⬝ᵥ x) = lam * (f ⬝ᵥ f) := by rw [hnorm]
      _ < (hBall.eigenvalues j) * (f ⬝ᵥ f) := hgt
      _ = f ⬝ᵥ (((ballGraph G u r).adjMatrix ℝ) *ᵥ f) := hquadf.symm
      _ = x ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ x) := hquadx.symm

/-- functions with disjoint supports are orthogonal. -/
lemma dot_eq_zero_of_disjoint_support {W : Type*} [Fintype W] (s t : Set W) {x y : W → ℝ}
    (hx : ∀ w : W, w ∉ s → x w = 0) (hy : ∀ w : W, w ∉ t → y w = 0)
    (hdisj : Disjoint s t) : x ⬝ᵥ y = 0 := by
  classical
  rw [Set.disjoint_left] at hdisj
  rw [dotProduct]
  apply Finset.sum_eq_zero
  intro w hw
  by_cases hws : w ∈ s
  · have hwt : w ∉ t := hdisj hws
    rw [hy w hwt]
    ring
  · rw [hx w hws]
    ring

/-- functions supported on disjoint, pairwise-non-adjacent sets are `A`-orthogonal. -/
lemma quad_eq_zero_of_disjoint_nonadj_support {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s t : Set V) {x y : V → ℝ}
    (hx : ∀ w : V, w ∉ s → x w = 0) (hy : ∀ w : V, w ∉ t → y w = 0)
    (hdisj : Disjoint s t) (hnadj : ∀ a ∈ s, ∀ b ∈ t, ¬ G.Adj a b) :
    x ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ y) = 0 := by
  classical
  calc
    x ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ y) = ∑ a : V, x a * ((G.adjMatrix ℝ) *ᵥ y) a := by simp [dotProduct]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      by_cases has : a ∈ s
      · have hsum : ((G.adjMatrix ℝ) *ᵥ y) a = 0 := by
          simp [Matrix.mulVec, dotProduct]
          apply Finset.sum_eq_zero
          intro b hb
          by_cases hbt : b ∈ t
          · have hn : ¬ G.Adj a b := hnadj a has b hbt
            simp [SimpleGraph.adjMatrix_apply, hbt, hn]
          · have : y b = 0 := hy b hbt
            simp [this]
        simp [hsum]
      · have : x a = 0 := hx a has
        simp [this]

/-- pairwise-orthogonal `A`-orthogonal family with Rayleigh quotients `> t` forces at least
`card ι` eigenvalue values of `A` strictly above `t` (direct count). -/
lemma card_ge_family_count {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]
    (A : Matrix W W ℝ) (hA : A.IsHermitian) (t : ℝ) (x : ι → (W → ℝ))
    (hx0 : ∀ u : ι, x u ≠ 0)
    (hray : ∀ u : ι, t * (x u ⬝ᵥ x u) < x u ⬝ᵥ (A *ᵥ x u))
    (horth : ∀ ⦃u v : ι⦄, u ≠ v → x u ⬝ᵥ x v = 0 ∧ x u ⬝ᵥ (A *ᵥ x v) = 0) :
    Fintype.card ι ≤ Fintype.card {i : W // t < hA.eigenvalues i} := by
  classical
  let pi : (W → ℝ) →ₗ[ℝ] ({j : W // t < hA.eigenvalues j} → ℝ) :=
    { toFun := fun x => fun j => x ⬝ᵥ (hA.eigenvectorBasis j.1).ofLp
      map_add' := by
        intro x y
        funext j
        simp [dotProduct_add_left_pf]
      map_smul' := by
        intro a x
        funext j
        simp [dotProduct_smul_left_pf] }
  let psi := combMap x
  let phi : (ι → ℝ) →ₗ[ℝ] ({j : W // t < hA.eigenvalues j} → ℝ) := pi.comp psi
  have hphi_inj : Function.Injective phi := by
    intro c d hcd
    have hsub : c - d = 0 := by
      apply kernel_trivial A hA t x hx0 hray horth (c - d)
      intro j hjt
      have hz : phi (c - d) = 0 := by
        rw [map_sub, hcd, sub_self]
      have hpi0 : pi (psi (c - d)) = 0 := by
        simpa [phi, LinearMap.comp_apply] using hz
      have hjj : (pi (psi (c - d))) ⟨j, hjt⟩ = 0 := congrFun hpi0 ⟨j, hjt⟩
      simpa [psi, pi] using hjj
    exact sub_eq_zero.mp hsub
  have hdim : Module.finrank ℝ (ι → ℝ) ≤ Module.finrank ℝ ({j : W // t < hA.eigenvalues j} → ℝ) := by
    exact LinearMap.finrank_le_finrank_of_injective hphi_inj
  rw [Module.finrank_pi, Module.finrank_pi] at hdim
  exact hdim

/-- the number of vertices whose `r`-ball has spectral top `> lam` is bounded in terms of
`Δ`, `r` and the fact that at most one eigenvalue value of `G` lies above `lam`. -/
lemma U_card_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : ∀ i j : V, G.Reachable i j) {Δ : ℕ} (hdeg : ∀ v : V, G.degree v ≤ Δ)
    (r : ℕ) {lam : ℝ}
    (hcnt : Fintype.card {i : V // lam < (adj_isHerm_any G).eigenvalues i} ≤ 1) :
    ((Finset.univ.filter (fun v : V => lam < ballTop G v r)).card : ℕ)
      ≤ (Δ + 1) ^ (2 * (r + 1) + 1) := by
  classical
  let U : Finset V := Finset.univ.filter (fun v : V => lam < ballTop G v r)
  by_cases hU : U = ∅
  · change U.card ≤ (Δ + 1) ^ (2 * (r + 1) + 1)
    rw [hU]
    simp
  · have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
    rcases hUne with ⟨u0, hu0mem⟩
    have hu0 : lam < ballTop G u0 r := (Finset.mem_filter.mp hu0mem).2
    have hsub : U ⊆ ballFinset G u0 (2 * r + 1) := by
      intro u humem
      have hu : lam < ballTop G u r := (Finset.mem_filter.mp humem).2
      rw [mem_ballFinset]
      -- u ∈ ballSet G u0 (2r+1)
      have hd_le : G.dist u0 u ≤ 2 * r + 1 := by
        by_contra hnot
        have hlt : 2 * r + 1 < G.dist u0 u := lt_of_not_ge hnot
        have hdisj := ballSet_disjoint_of_dist G hlt (hconn u0 u)
        rcases ball_eigen_ext_support G hu0 with ⟨x0, hsup0, hx00, hray0⟩
        rcases ball_eigen_ext_support G hu with ⟨x1, hsup1, hx01, hray1⟩
        let xf : Fin 2 → (V → ℝ) := fun i => if i = 0 then x0 else x1
        have hx0f : ∀ i : Fin 2, xf i ≠ 0 := by
          intro i
          fin_cases i <;> simp [xf, hx00, hx01]
        have hrayf : ∀ i : Fin 2,
            lam * (xf i ⬝ᵥ xf i) < xf i ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ xf i) := by
          intro i
          fin_cases i <;> simp [xf, hray0, hray1]
        have hAsym : ∀ a b : V, (G.adjMatrix ℝ) a b = (G.adjMatrix ℝ) b a :=
          fun a b => hermitian_entries_symm_pf (G.adjMatrix ℝ) (adj_isHerm_any G) a b
        have horthf : ∀ ⦃i j : Fin 2⦄, i ≠ j →
            xf i ⬝ᵥ xf j = 0 ∧ xf i ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ xf j) = 0 := by
          intro i j hij
          fin_cases i <;> fin_cases j
          · exact False.elim (hij rfl)
          · constructor
            · simpa [xf] using dot_eq_zero_of_disjoint_support (s := ballSet G u0 r)
                (t := ballSet G u r) hsup0 hsup1 hdisj.1
            · simpa [xf] using quad_eq_zero_of_disjoint_nonadj_support G (ballSet G u0 r)
                (ballSet G u r) hsup0 hsup1 hdisj.1 hdisj.2
          · constructor
            · rw [dotProduct_comm]
              simpa [xf] using dot_eq_zero_of_disjoint_support (s := ballSet G u0 r)
                (t := ballSet G u r) hsup0 hsup1 hdisj.1
            · have hA10 : x1 ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ x0) = 0 := by
                calc
                  x1 ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ x0) = ((G.adjMatrix ℝ) *ᵥ x1) ⬝ᵥ x0 := by
                    exact dotProduct_mulVec_symm_pf (G.adjMatrix ℝ) hAsym x1 x0
                  _ = x0 ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ x1) := by rw [dotProduct_comm]
                  _ = 0 := by
                    exact quad_eq_zero_of_disjoint_nonadj_support G (ballSet G u0 r)
                      (ballSet G u r) hsup0 hsup1 hdisj.1 hdisj.2
              simpa [xf] using hA10
          · exact False.elim (hij rfl)
        have hge := card_ge_family_count (A := G.adjMatrix ℝ) (adj_isHerm_any G) lam xf
          hx0f hrayf horthf
        norm_num at hge
        omega
      rcases walk_of_dist G hconn u0 u with ⟨p, hp⟩
      exact ⟨p, by rw [hp]; exact hd_le⟩
    have hUcard : U.card ≤ (ballFinset G u0 (2 * r + 1)).card := Finset.card_le_card hsub
    have hball : (ballFinset G u0 (2 * r + 1)).card ≤ (Δ + 1) ^ ((2 * r + 1) + 1) :=
      ballFinset_card_le G hdeg u0 (2 * r + 1)
    have hmono : (Δ + 1) ^ ((2 * r + 1) + 1) ≤ (Δ + 1) ^ (2 * (r + 1) + 1) := by
      have hbase : 1 ≤ Δ + 1 := by omega
      exact Nat.pow_le_pow_right hbase (by omega)
    calc
      U.card ≤ (ballFinset G u0 (2 * r + 1)).card := hUcard
      _ ≤ (Δ + 1) ^ ((2 * r + 1) + 1) := hball
      _ ≤ (Δ + 1) ^ (2 * (r + 1) + 1) := hmono

/-- vertices reachable from `w` within `r` steps by walks of `G` whose vertices stay in `Kf`. -/
def keptReach {V : Type*} (G : SimpleGraph V) (Kf : Set V) (w : V) (r : ℕ) : Set V :=
  {v : V | ∃ p : G.Walk w v, p.length ≤ r ∧ ∀ x ∈ p.support, x ∈ Kf}

/-- every vertex visited by a closed walk of length `≤ 2r` starting and ending at `w`
whose vertices lie in `Kf` is in `keptReach G Kf w r`. -/
lemma keptReach_of_closed_walk {V : Type*} (G : SimpleGraph V) (Kf : Set V) {w : V} {r : ℕ}
    {p : G.Walk w w} (hp : p.length ≤ 2 * r) (hpK : ∀ x ∈ p.support, x ∈ Kf) :
    ∀ x ∈ p.support, x ∈ keptReach G Kf w r := by
  classical
  intro x hx
  let t := p.takeUntil x hx
  let d := p.dropUntil x hx
  have hsum : t.length + d.length = p.length := by
    rw [show t.length = p.support.idxOf x from by
      simpa [t] using (SimpleGraph.Walk.length_takeUntil (p := p) (w := x) hx),
      show d.length = p.length - p.support.idxOf x from by
      simpa [d] using (SimpleGraph.Walk.length_dropUntil (p := p) (w := x) hx)]
    have hidx_lt : p.support.idxOf x < p.support.length := List.idxOf_lt_length_of_mem hx
    have hlen_supp : p.support.length = p.length + 1 := by simp
    have hidx_le : p.support.idxOf x ≤ p.length := by omega
    exact Nat.add_sub_of_le hidx_le
  have htK : ∀ y ∈ t.support, y ∈ Kf := by
    intro y hy
    exact hpK y ((SimpleGraph.Walk.support_takeUntil_subset_support p hx) hy)
  have hdK : ∀ y ∈ d.support, y ∈ Kf := by
    intro y hy
    exact hpK y ((SimpleGraph.Walk.support_dropUntil_subset_support p hx) hy)
  by_cases ht_le : t.length ≤ r
  · exact ⟨t, ht_le, htK⟩
  · have hd_le : d.length ≤ r := by
      have hle : t.length + d.length ≤ 2 * r := by simpa [hsum] using hp
      omega
    exact ⟨d.reverse, by simpa [SimpleGraph.Walk.length_reverse] using hd_le, by
      intro y hy
      have hy' : y ∈ d.support := by
        simpa [SimpleGraph.Walk.support_reverse] using hy
      exact hdK y hy'⟩

/-- `unliftWalk` is injective: it merely erases membership proofs. -/
lemma unliftWalk_injective {V : Type*} (G : SimpleGraph V) (t : Set V) {a b : V} :
    Function.Injective (unliftWalk (G := G) (t := t) (a := a) (b := b)) := by
  intro p q h
  apply SimpleGraph.Walk.ext_support
  calc
    p.support = (unliftWalk G t p).support := (support_unliftWalk G t p).symm
    _ = (unliftWalk G t q).support := by rw [h]
    _ = q.support := support_unliftWalk G t q

/-- closed `Kf`-walks of length `2 r₂` from `w` inject into closed walks of the same length
in the kept reach set: every vertex of such a walk lies inside `keptReach G Kf w r₂`. -/
def keptWalkInj {V : Type*} [DecidableEq V] (G : SimpleGraph V) (Kf : Set V) {w : V}
    (hw : w ∈ Kf) (r₂ : ℕ) :
    {p : (subGraphOn G Kf).Walk w w // p.length = 2 * r₂} →
    {p : (subGraphOn G (keptReach G Kf w r₂)).Walk w w // p.length = 2 * r₂} := by
  intro x
  let R : Set V := keptReach G Kf w r₂
  let p := x.1
  let q := unliftWalk G Kf p
  have hqK : ∀ y ∈ q.support, y ∈ Kf := by
    intro y hy
    rw [support_unliftWalk G Kf p] at hy
    exact subGraphOn_support_mem G Kf hw p y hy
  have hqlen : q.length = p.length := by simpa [q] using length_unliftWalk G Kf p
  have hq2 : q.length = 2 * r₂ := hqlen.trans x.2
  have hqR : ∀ y ∈ q.support, y ∈ R := by
    intro y hy
    exact keptReach_of_closed_walk (G := G) (Kf := Kf) (w := w) (r := r₂) (p := q)
      (le_of_eq hq2) (fun z hz => hqK z hz) y hy
  refine ⟨liftWalk G R q hqR, ?_⟩
  rw [length_liftWalk, hqlen]
  exact x.2

lemma keptWalkInj_injective {V : Type*} [DecidableEq V] (G : SimpleGraph V) (Kf : Set V)
    {w : V} (hw : w ∈ Kf) (r₂ : ℕ) :
    Function.Injective (keptWalkInj G Kf hw r₂) := by
  intro x y hxy
  apply Subtype.ext
  have hval : (keptWalkInj G Kf hw r₂ x).1 = (keptWalkInj G Kf hw r₂ y).1 :=
    congrArg Subtype.val hxy
  have hunl : unliftWalk G (keptReach G Kf w r₂) (keptWalkInj G Kf hw r₂ x).1 =
      unliftWalk G (keptReach G Kf w r₂) (keptWalkInj G Kf hw r₂ y).1 :=
    congrArg (unliftWalk G (keptReach G Kf w r₂)) hval
  have hqeq : unliftWalk G Kf x.1 = unliftWalk G Kf y.1 := by
    simpa [keptWalkInj, unlift_liftWalk] using hunl
  exact unliftWalk_injective G Kf hqeq

/-- For a kept vertex `w`, the `(w,w)`-entry of the `(2 r₂)`-th power of the zeroed
(kept-only) adjacency is bounded by `localTop` over the kept `r₂`-reach ball. -/
lemma kept_diag_le_local {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (Kf : Set V) (w : V) (hw : w ∈ Kf) (r₂ : ℕ) :
    (restrictedMatrix (G.adjMatrix ℝ) Kf ^ (2 * r₂)) w w ≤
      (localTop (G.adjMatrix ℝ) (adj_isHerm_any G) (keptReach G Kf w r₂)) ^ (2 * r₂) := by
  classical
  let R : Set V := keptReach G Kf w r₂
  have hle : (restrictedMatrix (G.adjMatrix ℝ) Kf ^ (2 * r₂)) w w ≤
      (restrictedMatrix (G.adjMatrix ℝ) R ^ (2 * r₂)) w w := by
    rw [restricted_pow_apply_eq_card_walk G Kf w w (2 * r₂),
        restricted_pow_apply_eq_card_walk G R w w (2 * r₂)]
    exact_mod_cast Fintype.card_le_of_injective (keptWalkInj G Kf hw r₂)
      (keptWalkInj_injective G Kf hw r₂)
  calc
    (restrictedMatrix (G.adjMatrix ℝ) Kf ^ (2 * r₂)) w w ≤
        (restrictedMatrix (G.adjMatrix ℝ) R ^ (2 * r₂)) w w := hle
    _ ≤ (localTop (G.adjMatrix ℝ) (adj_isHerm_any G) R) ^ (2 * r₂) :=
        restricted_pow_diag_le_localTop (G.adjMatrix ℝ) (adj_isHerm_any G)
          (adjMatrix_nonneg_any G) R w r₂

/-! # Trace bound on the geometric multiplicity of an eigenvalue value

The core linear-algebra estimate used in the multiplicity bound: for a real Hermitian
matrix `P` whose eigenvalue *values* (with multiplicity) are `hP.eigenvalues`, the geometric
multiplicity of the eigenvalue value `t` is `finrank ker ((t • 1) - P)`, and every eigenvalue
value `μ` satisfies `0 ≤ μ^(2r)`, so that

`mult · t^(2r) ≤ Σ_j (hP.eigenvalues j)^(2r) = tr(P^(2r))`.

The only structural input needed is the "geometric ≤ algebraic multiplicity" inequality
`finrank_ker_le_card_eigen_eq` (an eigenvector-basis argument), the trace identity
`trace_pow_eq_sum_eigs`, and nonnegativity of even powers. -/

/-- eigenvector at index `j` of Hermitian `P` is a `(t - μ_j)`-eigenvector of `t•1 - P`. -/
lemma traceMult_mulVec_sub_eigen_basis {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : P.IsHermitian) (t : ℝ) (j : V) :
    ((t • (1 : Matrix V V ℝ) - P) *ᵥ (hP.eigenvectorBasis j).ofLp)
      = (t - hP.eigenvalues j) • (hP.eigenvectorBasis j).ofLp := by
  classical
  calc
    ((t • (1 : Matrix V V ℝ) - P) *ᵥ (hP.eigenvectorBasis j).ofLp)
        = ((t • (1 : Matrix V V ℝ)) *ᵥ (hP.eigenvectorBasis j).ofLp)
          - P *ᵥ (hP.eigenvectorBasis j).ofLp := by rw [Matrix.sub_mulVec]
    _ = t • (hP.eigenvectorBasis j).ofLp - P *ᵥ (hP.eigenvectorBasis j).ofLp := by
          simp [Matrix.smul_mulVec, Matrix.one_mulVec]
    _ = t • (hP.eigenvectorBasis j).ofLp - (hP.eigenvalues j) • (hP.eigenvectorBasis j).ofLp := by
          rw [bfun_eigen P hP j]
    _ = (t - hP.eigenvalues j) • (hP.eigenvectorBasis j).ofLp := by
          ext w
          simp [Pi.sub_apply, Pi.smul_apply]
          ring

/-- a vector in the kernel of `(t•1-P).mulVecLin` has zero `b_k`-coefficient when
`hP.eigenvalues k ≠ t`. -/
lemma traceMult_ker_coeff_zero_of_ne {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : P.IsHermitian) (t : ℝ) {x : V → ℝ}
    (hx : ((t • (1 : Matrix V V ℝ)) - P) *ᵥ x = 0) (k : V)
    (hk : hP.eigenvalues k ≠ t) : x ⬝ᵥ (hP.eigenvectorBasis k).ofLp = 0 := by
  classical
  let b : V → ℝ := (hP.eigenvectorBasis k).ofLp
  let B : Matrix V V ℝ := (t • (1 : Matrix V V ℝ)) - P
  have hBx : B *ᵥ x = t • x - P *ᵥ x := by
    dsimp [B]
    rw [Matrix.sub_mulVec]
    simp [Matrix.smul_mulVec, Matrix.one_mulVec]
  have hz : (B *ᵥ x) ⬝ᵥ b = 0 := by
    rw [hx]
    simp
  have hz' : (t • x - P *ᵥ x) ⬝ᵥ b = 0 := by
    rwa [hBx] at hz
  have hz2 : (t • x) ⬝ᵥ b - (P *ᵥ x) ⬝ᵥ b = 0 := by
    simpa [sub_dotProduct] using hz'
  have hz3 : t * (x ⬝ᵥ b) - (P *ᵥ x) ⬝ᵥ b = 0 := by
    have hsmul : (t • x) ⬝ᵥ b = t * (x ⬝ᵥ b) := by
      simpa using (smul_dotProduct (R := ℝ) (m := V) (x := t) x b)
    rw [hsmul] at hz2
    simpa using hz2
  have hsym : ∀ i j : V, P i j = P j i := fun i j => hermitian_entries_symm_pf P hP i j
  have hPxb : (P *ᵥ x) ⬝ᵥ b = x ⬝ᵥ (P *ᵥ b) := by
    calc
      (P *ᵥ x) ⬝ᵥ b = b ⬝ᵥ (P *ᵥ x) := dotProduct_comm (P *ᵥ x) b
      _ = (P *ᵥ b) ⬝ᵥ x := dotProduct_mulVec_symm_pf P hsym b x
      _ = x ⬝ᵥ (P *ᵥ b) := dotProduct_comm (P *ᵥ b) x
  have hz4 : t * (x ⬝ᵥ b) - x ⬝ᵥ (P *ᵥ b) = 0 := by
    rwa [hPxb] at hz3
  have hz5 : x ⬝ᵥ (P *ᵥ b) = (hP.eigenvalues k) * (x ⬝ᵥ b) := by
    calc
      x ⬝ᵥ (P *ᵥ b) = x ⬝ᵥ (P *ᵥ (hP.eigenvectorBasis k).ofLp) := rfl
      _ = x ⬝ᵥ ((hP.eigenvalues k) • (hP.eigenvectorBasis k).ofLp) := by
            rw [bfun_eigen P hP k]
      _ = (hP.eigenvalues k) * (x ⬝ᵥ (hP.eigenvectorBasis k).ofLp) := by
            simpa using (dotProduct_smul_right_pf (hP.eigenvalues k) x (hP.eigenvectorBasis k).ofLp)
      _ = (hP.eigenvalues k) * (x ⬝ᵥ b) := rfl
  have hz6 : t * (x ⬝ᵥ b) - (hP.eigenvalues k) * (x ⬝ᵥ b) = 0 := by
    rwa [hz5] at hz4
  have hz7 : (t - hP.eigenvalues k) * (x ⬝ᵥ b) = 0 := by
    nlinarith
  have htne : t - hP.eigenvalues k ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
  exact (mul_eq_zero.mp hz7).resolve_left htne

/-- the geometric multiplicity of an eigenvalue value `t` of a Hermitian matrix `P` is at most
the number of eigenvalue values equal to `t`. -/
lemma traceMult_finrank_ker_le_card_eigen_eq {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : P.IsHermitian) (t : ℝ) :
    Module.finrank ℝ (LinearMap.ker (((t • (1 : Matrix V V ℝ)) - P).mulVecLin))
      ≤ Fintype.card {j : V // hP.eigenvalues j = t} := by
  classical
  let S := {j : V // hP.eigenvalues j = t}
  let phi : (LinearMap.ker (((t • (1 : Matrix V V ℝ)) - P).mulVecLin)) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun x => fun j : S => x.1 ⬝ᵥ (hP.eigenvectorBasis j.1).ofLp
      map_add' := by
        intro x y
        funext j
        exact dotProduct_add_left_pf x.1 y.1 (hP.eigenvectorBasis j.1).ofLp
      map_smul' := by
        intro a x
        funext j
        exact dotProduct_smul_left_pf a x.1 (hP.eigenvectorBasis j.1).ofLp }
  have hker_below : ∀ {x : LinearMap.ker (((t • (1 : Matrix V V ℝ)) - P).mulVecLin)},
      (∀ j : S, (phi x) j = 0) → x = 0 := by
    intro x hxcoeff
    apply Subtype.ext
    funext w
    have hzker : ((t • (1 : Matrix V V ℝ) - P) *ᵥ x.1 = 0) := by
      change ((t • (1 : Matrix V V ℝ) - P).mulVecLin) x.1 = 0
      exact x.2
    have hcoeff (k : V) : x.1 ⬝ᵥ (hP.eigenvectorBasis k).ofLp = 0 := by
      by_cases h : hP.eigenvalues k = t
      · have hk := hxcoeff ⟨k, h⟩
        simpa [phi] using hk
      · exact traceMult_ker_coeff_zero_of_ne P hP t hzker k h
    calc
      x.1 w = (∑ k : V, (x.1 ⬝ᵥ (hP.eigenvectorBasis k).ofLp) * ((hP.eigenvectorBasis k).ofLp w)) :=
            congrFun (expand P hP x.1) w
      _ = 0 := by
            apply Finset.sum_eq_zero
            intro k hk
            rw [hcoeff k]
            simp
  have hphi_ker : LinearMap.ker phi = ⊥ := by
    apply Submodule.ext
    intro x
    constructor
    · intro hx
      rw [Submodule.mem_bot]
      exact hker_below (fun j => by
        have hxj := congrFun hx j
        simpa using hxj)
    · intro hx
      rw [Submodule.mem_bot] at hx
      rw [LinearMap.mem_ker]
      rw [hx]
      simp
  have hinj : Function.Injective phi := by
    rw [← LinearMap.ker_eq_bot]
    exact hphi_ker
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hfinS : Module.finrank ℝ (S → ℝ) = Fintype.card S := by
    rw [Module.finrank_pi]
  simpa [S] using (le_trans hle (by rw [hfinS]))

/-- `0 ≤ μ^(2r)` for real `μ`. -/
lemma traceMult_even_pow_nonneg (μ : ℝ) (r : ℕ) : 0 ≤ μ ^ (2 * r) := by
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg μ) r

/-- the geometric multiplicity of the eigenvalue value `t` (t > 0) of a Hermitian matrix
`P` satisfies `mult · t^(2r) ≤ tr(P^(2r))`. -/
lemma mult_le_trace_even {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ)
    (hP : P.IsHermitian) (t : ℝ) (ht : 0 < t) (r : ℕ) :
    (Module.finrank ℝ (LinearMap.ker (((t • (1 : Matrix V V ℝ)) - P).mulVecLin)) : ℝ) *
        t ^ (2 * r) ≤ (P ^ (2 * r)).trace := by
  classical
  let Sfin : Finset V := Finset.univ.filter (fun j : V => hP.eigenvalues j = t)
  have hfin_nat : Module.finrank ℝ (LinearMap.ker (((t • (1 : Matrix V V ℝ)) - P).mulVecLin))
      ≤ Fintype.card {j : V // hP.eigenvalues j = t} := traceMult_finrank_ker_le_card_eigen_eq P hP t
  have htp : 0 ≤ t ^ (2 * r) := traceMult_even_pow_nonneg t r
  have htr : (P ^ (2 * r)).trace = ∑ j : V, (hP.eigenvalues j) ^ (2 * r) :=
    trace_pow_eq_sum_eigs P hP (2 * r)
  have hsubset : Sfin ⊆ (Finset.univ : Finset V) := Finset.filter_subset _ _
  have hnonneg : ∀ j ∈ (Finset.univ : Finset V), j ∉ Sfin → 0 ≤ (hP.eigenvalues j) ^ (2 * r) := by
    intro j hj hnot
    exact traceMult_even_pow_nonneg (hP.eigenvalues j) r
  have hle_subset : (∑ j ∈ Sfin, (hP.eigenvalues j) ^ (2 * r))
      ≤ ∑ j : V, (hP.eigenvalues j) ^ (2 * r) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have hSsum : (∑ j ∈ Sfin, (hP.eigenvalues j) ^ (2 * r))
      = (Sfin.card : ℝ) * t ^ (2 * r) := by
    calc
      (∑ j ∈ Sfin, (hP.eigenvalues j) ^ (2 * r))
          = ∑ j ∈ Sfin, t ^ (2 * r) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hμ : hP.eigenvalues j = t := (Finset.mem_filter.mp hj).2
            rw [hμ]
      _ = (Sfin.card : ℝ) * t ^ (2 * r) := by
            simp
  have hcardS_nat : Fintype.card {j : V // hP.eigenvalues j = t} = Sfin.card := by
    dsimp [Sfin]
    exact Fintype.card_subtype (fun j : V => hP.eigenvalues j = t)
  have hcardS : (Fintype.card {j : V // hP.eigenvalues j = t} : ℝ) = (Sfin.card : ℝ) := by
    exact_mod_cast hcardS_nat
  calc
    (Module.finrank ℝ (LinearMap.ker (((t • (1 : Matrix V V ℝ)) - P).mulVecLin)) : ℝ)
        * t ^ (2 * r)
        ≤ (Fintype.card {j : V // hP.eigenvalues j = t} : ℝ) * t ^ (2 * r) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfin_nat) htp
    _ = ∑ j ∈ Sfin, (hP.eigenvalues j) ^ (2 * r) := by
          rw [hcardS]
          exact hSsum.symm
    _ ≤ ∑ j : V, (hP.eigenvalues j) ^ (2 * r) := hle_subset
    _ = (P ^ (2 * r)).trace := htr.symm

/-- an `r`-ball (r ≥ 1) around a vertex with a neighbour has spectral top at least 1. -/
lemma ballTop_ge_one_of_adj {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {v : V} {r : ℕ} (hr : 1 ≤ r) : (∃ y : V, G.Adj v y) → 1 ≤ ballTop G v r := by
  classical
  intro h
  rcases h with ⟨y, hy⟩
  let W := ballSet G v r
  let c : W := ballCenter G v r
  let w : W := ⟨y, ⟨hy.toWalk, by simpa [SimpleGraph.Adj.length_toWalk] using hr⟩⟩
  have hcw : c ≠ w := by
    intro hc
    apply hy.ne
    exact congrArg Subtype.val hc
  let B := ballGraph G v r
  let A : Matrix W W ℝ := B.adjMatrix ℝ
  let hA : A.IsHermitian := by
    dsimp [A]
    exact adj_isHerm_any B
  have hBcw : B.Adj c w := by
    rw [ball_adj_iff]
    exact hy
  have hBwc : B.Adj w c := by
    rw [ball_adj_iff]
    exact (G.adj_comm y v).mpr hy
  have hAcw : A c w = 1 := by
    simp [A, hBcw]
  have hAwc : A w c = 1 := by
    simp [A, hBwc]
  have hterm : ∀ t : W, t ∈ (Finset.univ : Finset W) → 0 ≤ A c t * A t c := fun t ht =>
    mul_nonneg (adjMatrix_nonneg_any B c t) (adjMatrix_nonneg_any B t c)
  have hsq : (A ^ 2) c c = ∑ t : W, A c t * A t c := by
    rw [pow_two, Matrix.mul_apply]
  have hsingle : A c w * A w c ≤ ∑ t : W, A c t * A t c := by
    have hs := Finset.single_le_sum (s := (Finset.univ : Finset W)) hterm (Finset.mem_univ w)
    simpa using hs
  have hcc : 1 ≤ (A ^ 2) c c := by
    rw [hsq]
    calc
      1 = A c w * A w c := by rw [hAcw, hAwc]; norm_num
      _ ≤ ∑ t : W, A c t * A t c := hsingle
  have hupper : (A ^ 2) c c ≤ (topVal A hA) ^ 2 := by
    simpa using (diag_pow_even_le_top A hA (adjMatrix_nonneg_any B) 1 c)
  have hWne : (Finset.univ : Finset W).Nonempty := ballFinset_nonempty G v r
  have htv : 0 ≤ topVal A hA := topVal_nonneg_of_nonneg A hA (adjMatrix_nonneg_any B) hWne
  have hle2 : 1 ≤ (topVal A hA) ^ 2 := le_trans hcc hupper
  have hfinal : 1 ≤ topVal A hA := by
    have hsq' : (1 : ℝ) ^ 2 ≤ (topVal A hA) ^ 2 := by simpa using hle2
    have habs : |(1 : ℝ)| ≤ |topVal A hA| := (sq_le_sq).mp hsq'
    simpa [abs_of_nonneg htv] using habs
  simpa [ballTop, A, hA] using hfinal

/-- a zeroed matrix applied to `x` is the zero-extension of its action on the restriction of
`x` to the set. -/
lemma restricted_mulVec_eq_extendZero {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (s : Set V) (x : V → ℝ) :
    restrictedMatrix A s *ᵥ x =
      extendZero s ((fun i j : s => A i.1 j.1) *ᵥ (fun i : s => x i.1)) := by
  classical
  funext u
  by_cases hu : u ∈ s
  · rw [extendZero_apply_mem s _ hu]
    simp only [Matrix.mulVec, dotProduct, restrictedMatrix, hu, true_and]
    have hsplit := (Fintype.sum_subtype_add_sum_subtype (ι := V) (p := fun v : V => v ∈ s)
      (f := fun v : V => (if v ∈ s then A u v else 0) * x v))
    have h0 : (∑ v : {v : V // v ∉ s}, (if v.1 ∈ s then A u v.1 else 0) * x v.1) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp [v.2]
    rw [← hsplit, h0, add_zero]
    apply Finset.sum_congr rfl
    intro v hv
    simp [v.2]
  · rw [extendZero_apply_not_mem s _ hu]
    simp [Matrix.mulVec, dotProduct, restrictedMatrix, hu]

/-- dotting with the zero-extension of `g` only sees the restriction of `x` to the set. -/
lemma dot_extendZero_left {V : Type*} [Fintype V] [DecidableEq V] (s : Set V)
    (x : V → ℝ) (g : s → ℝ) :
    x ⬝ᵥ (extendZero s g) = (fun i : s => x i.1) ⬝ᵥ g := by
  classical
  rw [dotProduct, dotProduct]
  have hsplit := (Fintype.sum_subtype_add_sum_subtype (ι := V) (p := fun v : V => v ∈ s)
    (f := fun v : V => x v * extendZero s g v))
  have h0 : (∑ v : {v : V // v ∉ s}, x v.1 * extendZero s g v.1) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    simp [extendZero, v.2]
  rw [← hsplit, h0, add_zero]
  apply Finset.sum_congr rfl
  intro v hv
  simp [extendZero, v.2]

/-- the norm of the restriction of `x` to a set is at most the norm of `x`. -/
lemma norm_restrict_le {V : Type*} [Fintype V] [DecidableEq V] (s : Set V) (x : V → ℝ) :
    (fun i : s => x i.1) ⬝ᵥ (fun i : s => x i.1) ≤ x ⬝ᵥ x := by
  classical
  rw [dotProduct, dotProduct]
  have hsplit := (Fintype.sum_subtype_add_sum_subtype (ι := V) (p := fun v : V => v ∈ s)
    (f := fun v : V => x v * x v))
  have h0 : 0 ≤ (∑ v : {v : V // v ∉ s}, x v.1 * x v.1) := by
    apply Finset.sum_nonneg
    intro v hv
    exact mul_self_nonneg (x v.1)
  calc
    (∑ i : s, x i.1 * x i.1) = (∑ v : {v : V // v ∈ s}, x v.1 * x v.1) := by
          apply Finset.sum_congr rfl
          intro v hv
          rfl
    _ ≤ (∑ v : {v : V // v ∈ s}, x v.1 * x v.1) + (∑ v : {v : V // v ∉ s}, x v.1 * x v.1) := by linarith
    _ = ∑ v : V, x v * x v := by
          rw [hsplit]

/-- the spectral top of the zeroed matrix on the ball `ballSet G w R` is at most the
spectral top `ballTop G w R` of the ball graph. -/
lemma localTop_ballSet_le_ballTop {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : V) (R : ℕ) :
    localTop (G.adjMatrix ℝ) (adj_isHerm_any G) (ballSet G w R) ≤ ballTop G w R := by
  classical
  let M : Matrix V V ℝ := restrictedMatrix (G.adjMatrix ℝ) (ballSet G w R)
  let hM : M.IsHermitian := restrictedMatrix_isHermitian (G.adjMatrix ℝ) (adj_isHerm_any G)
    (ballSet G w R)
  let hB : ((ballGraph G w R).adjMatrix ℝ).IsHermitian := adj_isHerm_any (ballGraph G w R)
  have hV : (Finset.univ : Finset V).Nonempty := ⟨w, Finset.mem_univ w⟩
  have hWs : (Finset.univ : Finset (ballSet G w R)).Nonempty := ballFinset_nonempty G w R
  rcases exists_topVal_index M hM hV with ⟨j, _hj, hjt⟩
  let b : V → ℝ := (hM.eigenvectorBasis j).ofLp
  have hb_unit : b ⬝ᵥ b = 1 := by simpa [b] using bfun_unit M hM j
  have hb_eig : M *ᵥ b = (hM.eigenvalues j) • b := by simpa [b] using bfun_eigen M hM j
  have hBnonneg : 0 ≤ topVal ((ballGraph G w R).adjMatrix ℝ) hB := by
    exact topVal_nonneg_of_nonneg ((ballGraph G w R).adjMatrix ℝ) hB
      (adjMatrix_nonneg_any (ballGraph G w R)) hWs
  have hC : (fun i j : ballSet G w R => (G.adjMatrix ℝ) i.1 j.1)
      = ((ballGraph G w R).adjMatrix ℝ) := by
    ext i j
    by_cases hadj : G.Adj i.1 j.1 <;> simp [SimpleGraph.adjMatrix_apply, hadj, ball_adj_iff]
  have hmain : hM.eigenvalues j ≤ topVal ((ballGraph G w R).adjMatrix ℝ) hB := by
    calc
      hM.eigenvalues j = b ⬝ᵥ (M *ᵥ b) := by
            calc
              hM.eigenvalues j = (hM.eigenvalues j) * (b ⬝ᵥ b) := by rw [hb_unit, mul_one]
              _ = b ⬝ᵥ ((hM.eigenvalues j) • b) := by rw [dotProduct_smul_right_pf]
              _ = b ⬝ᵥ (M *ᵥ b) := by rw [hb_eig]
      _ = (fun i : ballSet G w R => b i.1) ⬝ᵥ
          (((ballGraph G w R).adjMatrix ℝ) *ᵥ (fun i : ballSet G w R => b i.1)) := by
            calc
              b ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ (extendZero (ballSet G w R)
                  (((fun i j : ballSet G w R => (G.adjMatrix ℝ) i.1 j.1)) *ᵥ
                    (fun i : ballSet G w R => b i.1))) := by
                    rw [restricted_mulVec_eq_extendZero (G.adjMatrix ℝ) (ballSet G w R) b]
              _ = (fun i : ballSet G w R => b i.1) ⬝ᵥ
                  (((fun i j : ballSet G w R => (G.adjMatrix ℝ) i.1 j.1)) *ᵥ
                    (fun i : ballSet G w R => b i.1)) := by
                    exact dot_extendZero_left (ballSet G w R) b
                      (((fun i j : ballSet G w R => (G.adjMatrix ℝ) i.1 j.1)) *ᵥ
                        (fun i : ballSet G w R => b i.1))
              _ = (fun i : ballSet G w R => b i.1) ⬝ᵥ
                  (((ballGraph G w R).adjMatrix ℝ) *ᵥ (fun i : ballSet G w R => b i.1)) := by
                    rw [hC]
      _ ≤ topVal ((ballGraph G w R).adjMatrix ℝ) hB *
          ((fun i : ballSet G w R => b i.1) ⬝ᵥ (fun i : ballSet G w R => b i.1)) := by
            exact quad_le_topVal_pf ((ballGraph G w R).adjMatrix ℝ) hB hWs
              (fun i : ballSet G w R => b i.1)
      _ ≤ topVal ((ballGraph G w R).adjMatrix ℝ) hB := by
            have hz1 : (fun i : ballSet G w R => b i.1) ⬝ᵥ
                (fun i : ballSet G w R => b i.1) ≤ 1 := by
              calc
                (fun i : ballSet G w R => b i.1) ⬝ᵥ (fun i : ballSet G w R => b i.1)
                    ≤ b ⬝ᵥ b := norm_restrict_le (ballSet G w R) b
                _ = 1 := hb_unit
            have hmul : topVal ((ballGraph G w R).adjMatrix ℝ) hB *
                ((fun i : ballSet G w R => b i.1) ⬝ᵥ (fun i : ballSet G w R => b i.1))
                ≤ topVal ((ballGraph G w R).adjMatrix ℝ) hB * 1 :=
              mul_le_mul_of_nonneg_left hz1 hBnonneg
            simpa using hmul
  have hfin : topVal M hM ≤ topVal ((ballGraph G w R).adjMatrix ℝ) hB := by
    rw [← hjt]
    exact hmain
  simpa [localTop, ballTop, M, hM, hB] using hfin

lemma eig_abs_le_maxDeg {V : Type*} [Fintype V] (G : SimpleGraph V) (x : V → ℝ)
    (hx0 : x ≠ 0) {lam : ℝ} (hx : (G.adjMatrix ℝ) *ᵥ x = lam • x) {Δ : ℕ}
    (hdeg : ∀ v : V, G.degree v ≤ Δ) : |lam| ≤ (Δ : ℝ) := by
  classical
  -- `x` is nonzero, so pick a vertex `w` with `x w ≠ 0`.
  have hwnz : ∃ w : V, x w ≠ 0 := by
    by_contra h
    apply hx0
    funext v
    by_contra hv
    exact h ⟨v, hv⟩
  rcases hwnz with ⟨w, hw0⟩
  -- choose a vertex `v` where `|x|` attains its maximum
  let S : Finset ℝ := (Finset.univ : Finset V).image (fun v : V => |x v|)
  have hSne : S.Nonempty := ⟨|x w|, Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩⟩
  let m := S.max' hSne
  have hmem : m ∈ S := S.max'_mem hSne
  rcases Finset.mem_image.mp hmem with ⟨v, hvuniv, hvm⟩
  have hmax : ∀ u : V, |x u| ≤ |x v| := by
    intro u
    rw [hvm]
    exact Finset.le_max' S (|x u|) (Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩)
  have hxvpos : 0 < |x v| := by
    have hwpos : 0 < |x w| := abs_pos.mpr hw0
    exact lt_of_lt_of_le hwpos (hmax w)
  have hcv : (G.adjMatrix ℝ *ᵥ x) v = lam * x v := by
    have := congrFun hx v
    simpa using this
  have hle1 : |(G.adjMatrix ℝ *ᵥ x) v| ≤ (G.degree v : ℝ) * |x v| := by
    calc
      |(G.adjMatrix ℝ *ᵥ x) v|
          = |∑ u ∈ G.neighborFinset v, x u| := by rw [SimpleGraph.adjMatrix_mulVec_apply]
      _ ≤ ∑ u ∈ G.neighborFinset v, |x u| := by
            exact Finset.abs_sum_le_sum_abs (fun u : V => x u) (G.neighborFinset v)
      _ ≤ ∑ u ∈ G.neighborFinset v, |x v| := by
            exact Finset.sum_le_sum (fun u hu => hmax u)
      _ = (G.degree v : ℝ) * |x v| := by
            simp [SimpleGraph.card_neighborFinset_eq_degree]
  have hle2 : |(G.adjMatrix ℝ *ᵥ x) v| ≤ (Δ : ℝ) * |x v| := by
    calc
      |(G.adjMatrix ℝ *ᵥ x) v| ≤ (G.degree v : ℝ) * |x v| := hle1
      _ ≤ (Δ : ℝ) * |x v| := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg v) (abs_nonneg (x v))
  have hle3 : |lam| * |x v| ≤ (Δ : ℝ) * |x v| := by
    calc
      |lam| * |x v| = |lam * x v| := by rw [abs_mul]
      _ = |(G.adjMatrix ℝ *ᵥ x) v| := by rw [hcv]
      _ ≤ (Δ : ℝ) * |x v| := hle2
  -- divide by the positive number `|x v|`
  exact le_of_mul_le_mul_right hle3 hxvpos


lemma eigenvalues_eq_of_same_matrix {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (h1 h2 : A.IsHermitian) : h1.eigenvalues = h2.eigenvalues := by
  classical
  exact (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff (𝕜 := ℝ) h1 h2).mpr rfl



lemma has_neighbor_of_connected {V : Type*} (G : SimpleGraph V)
    (hconn : ∀ i j : V, G.Reachable i j) {i j : V} (hij : G.Adj i j) (v : V) :
    ∃ u : V, G.Adj v u := by
  classical
  by_cases hv : v = i
  · subst v
    exact ⟨j, hij⟩
  · rcases (hconn v i).exists_walk_length_eq_dist with ⟨p, hp⟩
    have hlen : 0 < p.length := by
      by_contra h
      have h0 : p.length = 0 := by omega
      exact hv (SimpleGraph.Walk.eq_of_length_eq_zero h0)
    have hnn : ¬ p.Nil := (SimpleGraph.Walk.not_nil_iff_lt_length).mpr hlen
    rcases (SimpleGraph.Walk.not_nil_iff.mp hnn) with ⟨u, hu, q, hpq⟩
    exact ⟨u, hu⟩


lemma support_subset_ball_self {V : Type*} (G : SimpleGraph V) {a z : V}
    (p : G.Walk a z) : ∀ x ∈ p.support, x ∈ ballSet G a p.length := by
  classical
  intro x hx
  let t := p.takeUntil x hx
  have hlen : t.length ≤ p.length := by
    have h1 := SimpleGraph.Walk.length_takeUntil (p := p) (w := x) hx
    dsimp [t]
    rw [h1]
    have hpos : p.support.idxOf x < p.support.length := List.idxOf_lt_length_of_mem hx
    have hlen_supp : p.support.length = p.length + 1 := by simp
    omega
  exact ⟨t, hlen⟩

/-- a short walk from a vertex in an `r₂`-ball stays inside the `(r₁ + r₂)`-ball. -/
lemma walk_vertices_in_ball_add {V : Type*} (G : SimpleGraph V) {a z w : V} {r₁ r₂ : ℕ}
    (p : G.Walk a z) (hp : p.length ≤ r₁) (haw : ∃ q : G.Walk w a, q.length ≤ r₂) :
    ∀ x ∈ p.support, x ∈ ballSet G w (r₁ + r₂) := by
  classical
  rcases haw with ⟨q, hq⟩
  intro x hx
  have hxr : x ∈ ballSet G a r₁ := (ballSet_mono G a hp) (support_subset_ball_self G p x hx)
  rcases hxr with ⟨px, hpx⟩
  refine ⟨q.append px, ?_⟩
  rw [SimpleGraph.Walk.length_append]
  omega

/-- per-vertex spectral reduction for a kept vertex (net + not-in-U hypotheses). -/
lemma kept_local_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : ∀ i j : V, G.Reachable i j)
    {Kf : Set V} (r₁ M : ℕ) (lam : ℝ) (w : V) (hw : w ∈ Kf)
    (hr₁ : 1 ≤ r₁)
    (hV : (Finset.univ : Finset V).Nonempty)
    (hnb : ∀ a : V, ∃ u : V, G.Adj a u)
    (V₀ : Finset V) (hV₀net : ∀ a : V, ∃ z ∈ V₀, G.dist z a ≤ r₁)
    (hV₀del : ∀ z : V, z ∈ V₀ → z ∉ Kf)
    (hball : localTop (G.adjMatrix ℝ) (adj_isHerm_any G) (ballSet G w (r₁ + r₁ * M)) ≤
        ballTop G w (r₁ + r₁ * M))
    (hnotU : ballTop G w (r₁ + r₁ * M) ≤ lam)
    (hlamge : 1 ≤ lam) :
    (localTop (G.adjMatrix ℝ) (adj_isHerm_any G) (keptReach G Kf w (r₁ * M))) ^ (2 * r₁) ≤
      lam ^ (2 * r₁) - 1 := by
  classical
  let s : Set V := keptReach G Kf w (r₁ * M)
  let t : Set V := ballSet G w (r₁ + r₁ * M)
  have hs : s ⊆ t := by
    intro a ha
    rcases ha with ⟨p, hp, hvert⟩
    have haB : a ∈ ballSet G w (r₁ * M) := ⟨p, hp⟩
    exact (ballSet_mono G w (by omega : r₁ * M ≤ r₁ + r₁ * M)) haB
  have hsne : ∃ a : V, a ∈ s := by
    refine ⟨w, ?_⟩
    dsimp [s]
    refine ⟨SimpleGraph.Walk.nil, ?_, ?_⟩
    · simp
    · intro x hx
      rw [SimpleGraph.Walk.support_nil] at hx
      rw [List.mem_singleton] at hx
      rw [hx]
      exact hw
  have hdiag : ∀ a : V, a ∈ s → (restrictedMatrix (G.adjMatrix ℝ) s ^ (2 * r₁)) a a + 1 ≤
      (restrictedMatrix (G.adjMatrix ℝ) t ^ (2 * r₁)) a a := by
    intro a has
    have has' : a ∈ s := has
    rcases has with ⟨pa, hpa, hvert⟩
    have haw : ∃ q : G.Walk w a, q.length ≤ r₁ * M := ⟨pa, hpa⟩
    rcases hnb a with ⟨y, hyadj⟩
    have hy_t : y ∈ t := by
      dsimp [t]
      refine ⟨pa.append hyadj.toWalk, ?_⟩
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Adj.length_toWalk]
      omega
    rcases hV₀net a with ⟨z, hzmem, hzdist⟩
    have hz_del : z ∉ s := by
      intro hzs
      rcases hzs with ⟨pz, hpz, hzvert⟩
      have hz_in : z ∈ pz.support := SimpleGraph.Walk.end_mem_support pz
      exact hV₀del z hzmem (hzvert z hz_in)
    rcases (hconn a z).exists_walk_length_eq_dist with ⟨p, hpdist⟩
    have hp_le : p.length ≤ r₁ := by
      rw [hpdist]
      rw [G.dist_comm]
      exact hzdist
    have hp_t : ∀ x ∈ p.support, x ∈ t := by
      intro x hx
      exact walk_vertices_in_ball_add G p hp_le haw x hx
    have hz_t : z ∈ t := hp_t z (SimpleGraph.Walk.end_mem_support p)
    have hdel : ∃ z : V, z ∉ s ∧ z ∈ t ∧
        ∃ p : G.Walk a z, p.length ≤ r₁ ∧ ∀ x ∈ p.support, x ∈ t :=
      ⟨z, hz_del, hz_t, p, hp_le, hp_t⟩
    have hpad : ∃ y : V, G.Adj y a ∧ y ∈ t := ⟨y, G.adj_symm hyadj, hy_t⟩
    exact restricted_diag_deficit G hs r₁ a has' hdel hpad
  have hred := reduce_eigen_t G hs r₁ hr₁ hV hsne hdiag
  have hlt_nonneg : 0 ≤ localTop (G.adjMatrix ℝ) (adj_isHerm_any G) t := by
    apply topVal_nonneg_of_nonneg (restrictedMatrix (G.adjMatrix ℝ) t)
      (restrictedMatrix_isHermitian (G.adjMatrix ℝ) (adj_isHerm_any G) t)
      (restrictedMatrix_nonneg (G.adjMatrix ℝ) (adjMatrix_nonneg_any G) t) hV
  have hball_nonneg : 0 ≤ ballTop G w (r₁ + r₁ * M) := by
    apply topVal_nonneg_of_nonneg ((ballGraph G w (r₁ + r₁ * M)).adjMatrix ℝ)
      (adj_isHerm_any (ballGraph G w (r₁ + r₁ * M)))
      (adjMatrix_nonneg_any (ballGraph G w (r₁ + r₁ * M)))
      (ballFinset_nonempty G w (r₁ + r₁ * M))
  have hbt : (localTop (G.adjMatrix ℝ) (adj_isHerm_any G) t) ^ (2 * r₁) ≤
      (ballTop G w (r₁ + r₁ * M)) ^ (2 * r₁) := by
    exact pow_le_pow_left₀ hlt_nonneg hball (2 * r₁)
  have hlam : (ballTop G w (r₁ + r₁ * M)) ^ (2 * r₁) ≤ lam ^ (2 * r₁) := by
    exact pow_le_pow_left₀ hball_nonneg hnotU (2 * r₁)
  have hbnd : (localTop (G.adjMatrix ℝ) (adj_isHerm_any G) s) ^ (2 * r₁) + 1 ≤ lam ^ (2 * r₁) := by
    exact le_trans hred (le_trans hbt hlam)
  dsimp [s] at hbnd ⊢
  linarith

/-- `(s • 1) *ᵥ v = s • v` (self-contained instance-consistent version). -/
lemma smul_one_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℝ) (v : ι → ℝ) :
    (s • (1 : Matrix ι ι ℝ)) *ᵥ v = s • v := by
  classical
  ext i
  simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.one_apply, Finset.sum_ite_eq]

/-- linear zero-extension map from functions on `s` to functions on `V`. -/
def extLin {V : Type*} [DecidableEq V] (s : Set V) : (s → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := extendZero s
  map_add' := by
    intro f g
    funext v
    by_cases hv : v ∈ s <;> simp [extendZero, hv]
  map_smul' := by
    intro a f
    funext v
    by_cases hv : v ∈ s <;> simp [extendZero, hv]

/-- restricted-matrix times an extension equals the extension of the submatrix product. -/
lemma restrictedMatrix_mulVec_extendZero {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (s : Set V) [Fintype s] (B : Matrix s s ℝ) (f : s → ℝ)
    (hB : ∀ i j : s, B i j = A i.1 j.1) :
    (restrictedMatrix A s) *ᵥ extendZero s f = extendZero s (B *ᵥ f) := by
  classical
  funext v
  by_cases hv : v ∈ s
  · simp only [Matrix.mulVec, dotProduct]
    simp only [extendZero_apply_mem s (B *ᵥ f) hv]
    have hz0 (i : V) (hi : i ∉ s) : restrictedMatrix A s v i * extendZero s f i = 0 := by
      simp [restrictedMatrix, extendZero, hi, hv]
    have hc := (Fintype.sum_subtype_add_sum_subtype (ι := V) (p := fun i : V => i ∈ s)
      (f := fun i => restrictedMatrix A s v i * extendZero s f i)).symm
    have h0 : (∑ x : {i : V // i ∉ s}, restrictedMatrix A s v x.1 * extendZero s f x.1) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact hz0 x.1 x.2
    rw [h0, add_zero] at hc
    rw [hc]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rw [hB ⟨v, hv⟩ x]
      simp [restrictedMatrix, extendZero, hv, x.2]
  · simp only [Matrix.mulVec, dotProduct]
    simp [extendZero, restrictedMatrix, hv]

/-- the deleted full operator applied to an extension equals the extension of the sub-operator. -/
lemma mulVec_sub_extendZero {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (s : Set V) [Fintype s] (B : Matrix s s ℝ) (μ : ℝ) (f : s → ℝ)
    (hB : ∀ i j : s, B i j = A i.1 j.1) :
    ((μ • (1 : Matrix V V ℝ)) - restrictedMatrix A s) *ᵥ extendZero s f =
      extendZero s ((μ • (1 : Matrix s s ℝ) - B) *ᵥ f) := by
  classical
  calc
    ((μ • (1 : Matrix V V ℝ)) - restrictedMatrix A s) *ᵥ extendZero s f
        = (μ • (1 : Matrix V V ℝ)) *ᵥ extendZero s f
            - (restrictedMatrix A s) *ᵥ extendZero s f := by
              rw [mulVec_sub_any]
    _ = extLin s (μ • f) - extLin s (B *ᵥ f) := by
              rw [smul_one_mulVec]
              rw [restrictedMatrix_mulVec_extendZero A s B f hB]
              congr 1
              · change μ • (extLin s) f = (extLin s) (μ • f)
                rw [(extLin s).map_smul]
    _ = extLin s ((μ • f) - (B *ᵥ f)) := by
              rw [← (extLin s).map_sub]
    _ = extendZero s ((μ • (1 : Matrix s s ℝ) - B) *ᵥ f) := by
              rw [mulVec_sub_any]
              rw [smul_one_mulVec]
              rfl

/-- kernel of the sub-operator extends into the kernel of the deleted operator. -/
lemma extendZero_ker {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (s : Set V) [Fintype s] (B : Matrix s s ℝ) (μ : ℝ) (f : s → ℝ)
    (hB : ∀ i j : s, B i j = A i.1 j.1)
    (hf : (((μ • (1 : Matrix s s ℝ)) - B).mulVecLin) f = 0) :
    (((μ • (1 : Matrix V V ℝ)) - restrictedMatrix A s).mulVecLin) (extendZero s f) = 0 := by
  classical
  rw [Matrix.mulVecLin_apply]
  rw [mulVec_sub_extendZero A s B μ f hB]
  rw [← Matrix.mulVecLin_apply, hf]
  funext v
  simp [extendZero]

/-- deleting vertices: multiplicity of the sub-operator is at most the deleted operator's. -/
lemma sub_ker_le_ker_deleted {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (s : Set V) [Fintype s] (B : Matrix s s ℝ) (μ : ℝ)
    (hB : ∀ i j : s, B i j = A i.1 j.1) :
    Module.finrank ℝ (LinearMap.ker (((μ • (1 : Matrix s s ℝ)) - B).mulVecLin)) ≤
    Module.finrank ℝ (LinearMap.ker (((μ • (1 : Matrix V V ℝ)) - restrictedMatrix A s).mulVecLin)) := by
  classical
  let Ks : Submodule ℝ (s → ℝ) := LinearMap.ker (((μ • (1 : Matrix s s ℝ)) - B).mulVecLin)
  let KC : Submodule ℝ (V → ℝ) := LinearMap.ker (((μ • (1 : Matrix V V ℝ)) - restrictedMatrix A s).mulVecLin)
  let psi : Ks →ₗ[ℝ] (V → ℝ) := (extLin s).comp Ks.subtype
  have h_cont (f : Ks) : psi f ∈ KC := by
    rw [LinearMap.mem_ker]
    dsimp [KC, psi]
    exact extendZero_ker A s B μ f.1 hB f.2
  let phi : Ks →ₗ[ℝ] KC := psi.codRestrict KC h_cont
  have hinj : Function.Injective phi := by
    intro f g hfg
    apply Subtype.ext
    funext u
    have hval := congrArg Subtype.val hfg
    have hps : (extLin s) f.1 = (extLin s) g.1 := by
      simpa [phi, psi] using hval
    have hfu := congrFun hps u.1
    change extendZero s f.1 u.1 = extendZero s g.1 u.1 at hfu
    simpa [extendZero, u.2] using hfu
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- deleting the vertices of `D` (zeroing their rows/columns) increases the geometric
multiplicity of an eigenvalue value by at most `D.card`. -/
lemma del_mult_bound {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ)
    (hA : A.IsHermitian) (D : Finset V) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (((μ • (1 : Matrix V V ℝ)) - A).mulVecLin)) ≤
      Module.finrank ℝ (LinearMap.ker (((μ • (1 : Matrix V V ℝ)) -
        (restrictedMatrix A {v : V | v ∉ (D : Set V)})).mulVecLin)) + D.card := by
  classical
  let S : Set V := {v : V | v ∉ (D : Set V)}
  letI : Fintype S := by classical infer_instance
  letI : DecidableEq S := by classical infer_instance
  let B : Matrix S S ℝ := fun i j => A i.1 j.1
  have hB : B.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
    intro i j
    dsimp [B]
    exact (hermitian_entries_symm_pf A hA i.1 j.1).symm
  have hB_entries : ∀ i j : S, B i j = A i.1 j.1 := by
    intro i j
    rfl
  have hsub : ∃ e : S ↪ V, ∀ i j : S, B i j = A (e i) (e j) := by
    refine ⟨Function.Embedding.subtype (fun v : V => v ∈ S), ?_⟩
    intro i j
    rfl
  have h1 := finrank_ker_le_of_submatrix (W := V) (W0 := S) A hA B hB μ hsub
  have h2 := sub_ker_le_ker_deleted A S B μ hB_entries
  have hcardD : Fintype.card {v : V // v ∈ (D : Set V)} = D.card := by
    rw [Fintype.card_subtype]
    simp
  have hleD : D.card ≤ Fintype.card V := by
    simpa using (Finset.card_le_card (Finset.subset_univ D) : D.card ≤ (Finset.univ : Finset V).card)
  have hcardS' : Fintype.card S = Fintype.card V - Fintype.card {v : V // v ∈ (D : Set V)} := by
    calc
      Fintype.card S = Fintype.card {v : V // v ∉ (D : Set V)} := rfl
      _ = Fintype.card V - Fintype.card {v : V // v ∈ (D : Set V)} :=
            Fintype.card_subtype_compl (α := V) (p := fun v : V => v ∈ (D : Set V))
  have hcard : Fintype.card V - Fintype.card S = D.card := by
    rw [hcardS', hcardD]
    omega
  have hfin :
      Module.finrank ℝ (LinearMap.ker (((μ • (1 : Matrix V V ℝ)) - A).mulVecLin)) ≤
        Module.finrank ℝ (LinearMap.ker (((μ • (1 : Matrix V V ℝ)) - restrictedMatrix A S).mulVecLin)) + D.card := by
    rw [← hcard]
    exact le_trans h1 (Nat.add_le_add_right h2 (Fintype.card V - Fintype.card S))
  simpa [S] using hfin
end EigenMult

/-- The eventual bound on the multiplicity of the `≥ second-largest` eigenvalue `λ > 0` of a
connected graph of maximum degree `≤ Δ`. -/
theorem eigen_mult_eventual (Δ : ℕ) :
    ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V], n₀ ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (hA : (G.adjMatrix ℝ).IsHermitian),
      (∀ i j : V, G.Reachable i j) →
      (∀ v : V, G.degree v ≤ Δ) →
      ∀ {lam : ℝ}, 0 < lam →
      (∃ x : V → ℝ, x ≠ 0 ∧ (G.adjMatrix ℝ) *ᵥ x = lam • x) →
      (∃ mu : ℝ, lam < mu ∧ ∃ y : V → ℝ, y ≠ 0 ∧ (G.adjMatrix ℝ) *ᵥ y = mu • y) →
      (Fintype.card {i : V // lam < hA.eigenvalues i} ≤ 1) →
      (Module.finrank ℝ (LinearMap.ker (((lam • (1 : Matrix V V ℝ)) - (G.adjMatrix ℝ)).mulVecLin)) : ℝ)
        ≤ ε * (Fintype.card V : ℝ) := by
  classical
  intro ε hε
  by_cases hεge : 1 ≤ ε
  · -- trivial case
    refine ⟨1, ?_⟩
    intro V hfin hdec hVcard G hA hconn hdeg lam hlampos hx hm hcnt
    -- multiplicity ≤ card V
    have h1 : (Module.finrank ℝ (LinearMap.ker (((lam • (1 : Matrix V V ℝ)) - (G.adjMatrix ℝ)).mulVecLin)) : ℝ)
        ≤ (Fintype.card V : ℝ) := by
      have hfin : Module.finrank ℝ (LinearMap.ker (((lam • (1 : Matrix V V ℝ)) - (G.adjMatrix ℝ)).mulVecLin))
          ≤ Fintype.card V := by
        rw [EigenMult.finrank_ker_eq_card_sub_rank]
        omega
      exact_mod_cast hfin
    have h2 : (Fintype.card V : ℝ) ≤ ε * (Fintype.card V : ℝ) := by
      have hc : 0 ≤ (Fintype.card V : ℝ) := by positivity
      nlinarith
    exact le_trans h1 h2
  · -- 0 < ε < 1
    have hεpos : 0 < ε := hε
    have hεlt : ε < 1 := lt_of_not_ge hεge
    have hε4 : 0 < 8 / ε := by positivity
    -- choose r₁ with 1 ≤ r₁ and ε(r₁+1) ≥ 8
    rcases (exists_nat_ge ((8 / ε) - 1 : ℝ)) with ⟨r₁, hr₁0⟩
    have hr₁ : (8 / ε) - 1 ≤ (r₁ : ℝ) := hr₁0
    have hεr₁ : (8 : ℝ) ≤ (r₁ + 1 : ℝ) * ε := by
      have h : ((8 / ε) - 1 + 1) ≤ (r₁ : ℝ) + 1 := by linarith
      have h' : (8 / ε : ℝ) ≤ (r₁ : ℝ) + 1 := by linarith
      have hpos : 0 < ε := hε
      calc
        (8 : ℝ) = (8 / ε) * ε := by field_simp
        _ ≤ ((r₁ : ℝ) + 1) * ε := by exact mul_le_mul_of_nonneg_right h' (le_of_lt hpos)
    have hεinv : 1 < (1 / ε : ℝ) := by
      simpa [one_div] using (one_lt_inv₀ hε).mpr hεlt
    have h8 : (8 : ℝ) < 8 / ε := by
      calc
        (8 : ℝ) = 8 * 1 := by ring
        _ < 8 * (1 / ε) := mul_lt_mul_of_pos_left hεinv (by norm_num)
        _ = 8 / ε := by ring
    have hr₁ge : 1 ≤ r₁ := by
      have h7 : 7 < (r₁ : ℝ) := by linarith
      have h7' : 7 ≤ (r₁ : ℝ) := le_of_lt h7
      have hn7 : 7 ≤ r₁ := by exact_mod_cast h7'
      omega
    -- choose M
    rcases (exists_nat_ge (max (1 : ℝ) ((Δ : ℝ) ^ (2 * r₁) * Real.log (8 / ε)))) with ⟨M, hM0⟩
    have hM_ge_1 : 1 ≤ M := by
      have hM : (1 : ℝ) ≤ (M : ℝ) := by
        have hb : (1 : ℝ) ≤ max (1 : ℝ) ((Δ : ℝ) ^ (2 * r₁) * Real.log (8 / ε)) := by simp
        exact le_trans hb hM0
      exact_mod_cast hM
    have hM : ((Δ : ℝ) ^ (2 * r₁) * Real.log (8 / ε)) ≤ (M : ℝ) := by
      exact le_trans (le_max_right _ _) hM0
    let r₂ : ℕ := r₁ * M
    let r : ℕ := r₁ + r₂
    let C : ℕ := (Δ + 1) ^ (2 * (r + 1) + 1)
    -- choose n₀
    rcases (exists_nat_ge (max (8 / ε : ℝ) (max (8 * (C : ℝ) / ε) ((C : ℝ) + 1)))) with ⟨n₀, hn₀⟩
    refine ⟨n₀, ?_⟩
    intro V hfin hdec hVcard G hA hconn hdeg lam hlampos hx hm hcnt
    have hn0ge : (n₀ : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hVcard
    have hn_8 : (8 / ε : ℝ) ≤ (Fintype.card V : ℝ) := le_trans (le_trans (le_max_left _ _) hn₀) hn0ge
    have hn_C : (8 * (C : ℝ) / ε) ≤ (Fintype.card V : ℝ) := by
      have h1 := le_trans (le_max_right _ _) hn₀
      exact le_trans (le_trans (le_max_left _ _) h1) hn0ge
    have hn_C1 : ((C : ℝ) + 1) ≤ (Fintype.card V : ℝ) := by
      have h1 := le_trans (le_max_right _ _) hn₀
      exact le_trans (le_trans (le_max_right _ _) h1) hn0ge
    have hεn : 8 ≤ ε * (Fintype.card V : ℝ) := by
      have hεnz : ε ≠ 0 := ne_of_gt hε
      have h := mul_le_mul_of_nonneg_right hn_8 (le_of_lt hε)
      field_simp [hεnz] at h
      nlinarith
    have heq : hA.eigenvalues = (EigenMult.adj_isHerm_any G).eigenvalues :=
      EigenMult.eigenvalues_eq_of_same_matrix (G.adjMatrix ℝ) hA (EigenMult.adj_isHerm_any G)
    have hcardeq : Fintype.card {i : V // lam < hA.eigenvalues i} =
        Fintype.card {i : V // lam < (EigenMult.adj_isHerm_any G).eigenvalues i} := by
      apply Fintype.card_congr
      refine ⟨fun i => ⟨i.1, ?_⟩, fun j => ⟨j.1, ?_⟩, ?_, ?_⟩
      · have hi := i.2
        simpa [heq] using hi
      · have hj := j.2
        simpa [heq] using hj
      · intro i; rfl
      · intro j; rfl
    have hcnt' : Fintype.card {i : V // lam < (EigenMult.adj_isHerm_any G).eigenvalues i} ≤ 1 := by
      rwa [hcardeq] at hcnt
    by_cases hlam1 : lam < 1
    · -- lam < 1 : U = V forces n ≤ C contradicting n ≥ C+1
      exfalso
      -- edge exists
      rcases hx with ⟨x, hx0, hAx⟩
      have hedge : ∃ i j : V, G.Adj i j := by
        have hwnz : ∃ w : V, x w ≠ 0 := by
          by_contra h
          apply hx0
          funext v
          by_contra hv
          exact h ⟨v, hv⟩
        rcases hwnz with ⟨w, hw0⟩
        have hAxw : ((G.adjMatrix ℝ) *ᵥ x) w = lam * x w := by
          have := congrFun hAx w
          simpa using this
        by_contra hn
        push_neg at hn
        have hzero : ((G.adjMatrix ℝ) *ᵥ x) w = 0 := by
          simp [Matrix.mulVec, SimpleGraph.adjMatrix_apply]
          apply Finset.sum_eq_zero
          intro u hu
          have hnu : ¬ G.Adj w u := hn w u
          simp [hnu]
        have hlamx : lam * x w = 0 := by
          rw [← hAxw, hzero]
        have hlam0 : lam ≠ 0 := ne_of_gt hlampos
        have hxw0 : x w = 0 := by
          exact (mul_eq_zero.mp hlamx).resolve_left hlam0
        exact hw0 hxw0
      rcases hedge with ⟨i0, j0, hAdj0⟩
      have hnb : ∀ v : V, ∃ u : V, G.Adj v u := fun v => EigenMult.has_neighbor_of_connected G hconn hAdj0 v
      have hr_ge : 1 ≤ r := by
        dsimp [r, r₂]
        have h1 : 1 ≤ r₁ := hr₁ge
        omega
      have hballv : ∀ v : V, 1 ≤ EigenMult.ballTop G v r := by
        intro v
        rcases hnb v with ⟨u, hu⟩
        exact EigenMult.ballTop_ge_one_of_adj G hr_ge ⟨u, hu⟩
      -- every vertex is in U
      have hU : (Finset.univ.filter (fun v : V => lam < EigenMult.ballTop G v r)) = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro v
        simp
        exact lt_of_lt_of_le hlam1 (hballv v)
      have hUcard : (Fintype.card V : ℕ) ≤ C := by
        have hc : (Finset.univ.filter (fun v : V => lam < EigenMult.ballTop G v r)).card = Fintype.card V := by
          rw [hU]
          simp
        have hb := EigenMult.U_card_le G hconn hdeg r (lam := lam) hcnt'
        rw [← hc]
        simpa [C, r] using hb
      have hC1 : C + 1 ≤ Fintype.card V := by
        have h1 : (C : ℝ) + 1 ≤ (Fintype.card V : ℝ) := hn_C1
        exact_mod_cast h1
      omega

    · -- 1 ≤ lam : main case
      have hlamge : 1 ≤ lam := le_of_not_gt hlam1
      -- λ ≤ Δ and Δ ≥ 1
      have hlam_le_D : lam ≤ (Δ : ℝ) := by
        rcases hx with ⟨x, hx0, hAx⟩
        have hle := EigenMult.eig_abs_le_maxDeg G x hx0 hAx hdeg
        have hlamnonneg : 0 ≤ lam := le_of_lt hlampos
        rwa [abs_of_nonneg hlamnonneg] at hle
      have hDge1 : 1 ≤ (Δ : ℝ) := by linarith
      have hDpowpos : 0 < (Δ : ℝ) ^ (2 * r₁) := by
        have hD1 : 1 ≤ (Δ : ℝ) ^ (2 * r₁) := by
          have h0 : 0 ≤ (1 : ℝ) := by norm_num
          simpa using (pow_le_pow_left₀ h0 hDge1 (2 * r₁))
        nlinarith
      -- every vertex has a neighbour
      have hnb : ∀ a : V, ∃ u : V, G.Adj a u := by
        rcases hx with ⟨x, hx0, hAx⟩
        have hedge : ∃ i j : V, G.Adj i j := by
          have hwnz : ∃ w : V, x w ≠ 0 := by
            by_contra h
            apply hx0
            funext v
            by_contra hv
            exact h ⟨v, hv⟩
          rcases hwnz with ⟨w, hw0⟩
          have hAxw : ((G.adjMatrix ℝ) *ᵥ x) w = lam * x w := by
            have := congrFun hAx w
            simpa using this
          by_contra hn
          push_neg at hn
          have hzero : ((G.adjMatrix ℝ) *ᵥ x) w = 0 := by
            simp [Matrix.mulVec, SimpleGraph.adjMatrix_apply]
            apply Finset.sum_eq_zero
            intro u hu
            have hnu : ¬ G.Adj w u := hn w u
            simp [hnu]
          have hlamx : lam * x w = 0 := by rw [← hAxw, hzero]
          have hxw0 : x w = 0 := (mul_eq_zero.mp hlamx).resolve_left (ne_of_gt hlampos)
          exact hw0 hxw0
        rcases hedge with ⟨i0, j0, hAdj0⟩
        exact fun a => EigenMult.has_neighbor_of_connected G hconn hAdj0 a
      -- net
      rcases EigenMult.net_exists G hconn r₁ with ⟨V₀, hV₀card, hV₀net⟩
      -- U-set
      let U : Finset V := EigenMult.Uset G r lam
      have hUcard : U.card ≤ C := by
        have hb := EigenMult.U_card_le G hconn hdeg r (lam := lam) hcnt'
        dsimp [U, EigenMult.Uset]
        simpa [C, r] using hb
      let D : Finset V := V₀ ∪ U
      have hDcard : D.card ≤ Fintype.card V / (r₁ + 1) + 1 + C := by
        have h1 : D.card ≤ V₀.card + U.card := by
          dsimp [D]
          exact Finset.card_union_le V₀ U
        have h2 : V₀.card + U.card ≤ (Fintype.card V / (r₁ + 1) + 1) + C := by
          exact Nat.add_le_add hV₀card hUcard
        omega
      let Kf : Set V := {v : V | v ∉ (D : Set V)}
      let R : Matrix V V ℝ := EigenMult.restrictedMatrix (G.adjMatrix ℝ) Kf
      let hR : R.IsHermitian := EigenMult.restrictedMatrix_isHermitian (G.adjMatrix ℝ) hA Kf
      let mG : ℕ := Module.finrank ℝ (LinearMap.ker (((lam • (1 : Matrix V V ℝ)) - (G.adjMatrix ℝ)).mulVecLin))
      let mH : ℕ := Module.finrank ℝ (LinearMap.ker (((lam • (1 : Matrix V V ℝ)) - R).mulVecLin))
      have hcardpos : 0 < Fintype.card V := by
        have h1ε : (1 : ℝ) ≤ 8 / ε := by
          exact (le_div_iff₀ hε).mpr (by nlinarith)
        have h1n : 1 ≤ (n₀ : ℝ) := by
          exact le_trans h1ε (le_trans (le_max_left _ _) hn₀)
        have h1n' : 1 ≤ n₀ := by exact_mod_cast h1n
        omega
      have hVne : Nonempty V := Fintype.card_pos_iff.mp hcardpos
      have hV : (Finset.univ : Finset V).Nonempty := ⟨Classical.choice hVne, Finset.mem_univ _⟩
      -- deleted vertices are outside Kf
      have hV₀del : ∀ z : V, z ∈ V₀ → z ∉ Kf := by
        intro z hz
        dsimp [Kf]
        intro hzKf
        exact hzKf (Finset.mem_union.mpr (Or.inl hz))
      -- net hypothesis for the reduction (dist form)
      have hnetd : ∀ a : V, ∃ z ∈ V₀, G.dist z a ≤ r₁ := hV₀net
      -- local-top vs ball-top and not-in-U bounds per kept vertex
      have hnotUw : ∀ w : V, w ∈ Kf → EigenMult.ballTop G w r ≤ lam := by
        intro w hw
        have hwU : w ∉ U := by
          intro hwu
          have hwD : w ∈ (D : Set V) := by
            dsimp [D]
            exact Finset.mem_union.mpr (Or.inr hwu)
          exact hw hwD
        have hwball : ¬ lam < EigenMult.ballTop G w r := by
          intro hlamtop
          have hwu : w ∈ U := by
            dsimp [U, EigenMult.Uset]
            simp
            exact hlamtop
          exact hwU hwu
        exact le_of_not_gt hwball
      -- per-vertex diagonal bound
      have hbval : (lam ^ (2 * r₁) - 1) ≥ 0 := by
        have h1 : (1 : ℝ) ≤ lam ^ (2 * r₁) := by
          have h0 : 0 ≤ (1 : ℝ) := by norm_num
          simpa using (pow_le_pow_left₀ h0 hlamge (2 * r₁))
        linarith
      have hr2ge : 1 ≤ r₂ := by
        dsimp [r₂]
        exact Nat.mul_le_mul hr₁ge hM_ge_1
      have hdiagR : ∀ w : V, (R ^ (2 * r₂)) w w ≤ (lam ^ (2 * r₁) - 1) ^ M := by
        intro w
        by_cases hw : w ∈ Kf
        · -- kept vertex
          have hk1 := EigenMult.kept_diag_le_local G Kf w hw r₂
          have hnotU_r : EigenMult.ballTop G w (r₁ + r₁ * M) ≤ lam := by
            have := hnotUw w hw
            dsimp [r, r₂] at this
            exact this
          have hk2 := EigenMult.kept_local_bound G hconn (Kf := Kf) r₁ M lam w hw hr₁ge hV hnb V₀
            hnetd hV₀del (EigenMult.localTop_ballSet_le_ballTop G w (r₁ + r₁ * M))
            hnotU_r hlamge
          -- hk1 : (R^{2 r₂}) w w ≤ localTop(keptReach G Kf w r₂)^{2 r₂}
          -- hk2 : localTop(keptReach G Kf w (r₁*M))^{2 r₁} ≤ lam^{2 r₁} − 1
          have hnonneg : 0 ≤ (EigenMult.localTop (G.adjMatrix ℝ) (EigenMult.adj_isHerm_any G)
              (EigenMult.keptReach G Kf w r₂)) ^ (2 * r₁) := by
            have hs : 0 ≤ (EigenMult.localTop (G.adjMatrix ℝ) (EigenMult.adj_isHerm_any G)
                (EigenMult.keptReach G Kf w r₂)) ^ 2 := sq_nonneg _
            simpa [pow_mul] using pow_nonneg hs r₁
          have hpow : (EigenMult.localTop (G.adjMatrix ℝ) (EigenMult.adj_isHerm_any G)
              (EigenMult.keptReach G Kf w r₂)) ^ (2 * r₂)
              ≤ (lam ^ (2 * r₁) - 1) ^ M := by
            have hmul : (2 * r₂) = (2 * r₁) * M := by
              dsimp [r₂]
              ring
            have hstep : (EigenMult.localTop (G.adjMatrix ℝ) (EigenMult.adj_isHerm_any G)
                (EigenMult.keptReach G Kf w r₂)) ^ (2 * r₁) ≤ (lam ^ (2 * r₁) - 1) := by
              simpa [r₂] using hk2
            calc
              (EigenMult.localTop (G.adjMatrix ℝ) (EigenMult.adj_isHerm_any G)
                  (EigenMult.keptReach G Kf w r₂)) ^ (2 * r₂)
                  = ((EigenMult.localTop (G.adjMatrix ℝ) (EigenMult.adj_isHerm_any G)
                      (EigenMult.keptReach G Kf w r₂)) ^ (2 * r₁)) ^ M := by
                        rw [hmul, pow_mul]
              _ ≤ (lam ^ (2 * r₁) - 1) ^ M := by
                        exact pow_le_pow_left₀ hnonneg hstep M
          exact le_trans hk1 hpow
        · -- deleted vertex: diagonal is 0
          have hzero : (R ^ (2 * r₂)) w w = 0 := by
            dsimp [R]
            have hk2r : 1 ≤ 2 * r₂ := by omega
            exact EigenMult.restricted_pow_row_zero_pf G Kf (2 * r₂) hk2r w w hw
          have hnonneg : 0 ≤ (lam ^ (2 * r₁) - 1) ^ M := pow_nonneg hbval M
          rw [hzero]
          exact hnonneg
      have hsum : (R ^ (2 * r₂)).trace ≤ (Fintype.card V : ℝ) * (lam ^ (2 * r₁) - 1) ^ M := by
        calc
          (R ^ (2 * r₂)).trace = ∑ w : V, (R ^ (2 * r₂)) w w := by simp [Matrix.trace]
          _ ≤ ∑ w : V, (lam ^ (2 * r₁) - 1) ^ M := by
                apply Finset.sum_le_sum
                intro w hw
                exact hdiagR w
          _ = (Fintype.card V : ℝ) * (lam ^ (2 * r₁) - 1) ^ M := by
                simp [Finset.sum_const, nsmul_eq_mul]
      have hmt := EigenMult.mult_le_trace_even R hR lam hlampos r₂
      have hmH : (mH : ℝ) * lam ^ (2 * r₂) ≤ (Fintype.card V : ℝ) * (lam ^ (2 * r₁) - 1) ^ M := by
        calc
          (mH : ℝ) * lam ^ (2 * r₂) ≤ (R ^ (2 * r₂)).trace := by
                simpa [mH] using hmt
          _ ≤ (Fintype.card V : ℝ) * (lam ^ (2 * r₁) - 1) ^ M := hsum
      -- divide and use exponential decay
      let x : ℝ := (lam ^ (2 * r₁))⁻¹
      have hx0 : 0 ≤ x := inv_nonneg.mpr (pow_nonneg (le_of_lt hlampos) (2 * r₁))
      have hlam2pos : 0 < lam ^ (2 * r₁) := pow_pos hlampos (2 * r₁)

      have hlam2pow : 1 ≤ lam ^ (2 * r₁) := by
        have h0 : 0 ≤ (1 : ℝ) := by norm_num
        simpa using (pow_le_pow_left₀ h0 hlamge (2 * r₁))
      have hxle1 : x ≤ 1 := by
        dsimp [x]
        exact inv_le_one_of_one_le₀ hlam2pow
      have hone_sub : 0 ≤ 1 - x := sub_nonneg.mpr hxle1
      have hpos2r2 : 0 < lam ^ (2 * r₂) := pow_pos hlampos (2 * r₂)
      have hpow_eq : lam ^ (2 * r₂) = (lam ^ (2 * r₁)) ^ M := by
        rw [show 2 * r₂ = (2 * r₁) * M by dsimp [r₂]; ring]
        rw [pow_mul]
      have hdiv1 : (mH : ℝ) ≤ (Fintype.card V : ℝ) * (lam ^ (2 * r₁) - 1) ^ M / lam ^ (2 * r₂) := by
        exact (le_div_iff₀ hpos2r2).mpr hmH
      have hdiv2 : (Fintype.card V : ℝ) * (lam ^ (2 * r₁) - 1) ^ M / lam ^ (2 * r₂)
          = (Fintype.card V : ℝ) * (((lam ^ (2 * r₁) - 1) / lam ^ (2 * r₁)) ^ M) := by
        rw [hpow_eq]
        rw [div_pow]
        ring_nf
      have hdiv3 : (((lam ^ (2 * r₁) - 1) / lam ^ (2 * r₁)) ^ M) = (1 - x) ^ M := by
        have hinside : (lam ^ (2 * r₁) - 1) / lam ^ (2 * r₁) = 1 - (lam ^ (2 * r₁))⁻¹ := by
          field_simp [ne_of_gt hlam2pos]
        calc
          (((lam ^ (2 * r₁) - 1) / lam ^ (2 * r₁)) ^ M) = (1 - (lam ^ (2 * r₁))⁻¹) ^ M := by rw [hinside]
          _ = (1 - x) ^ M := by rfl
      have hmH3 : (mH : ℝ) ≤ (Fintype.card V : ℝ) * (1 - x) ^ M := by
        calc
          (mH : ℝ) ≤ (Fintype.card V : ℝ) * (lam ^ (2 * r₁) - 1) ^ M / lam ^ (2 * r₂) := hdiv1
          _ = (Fintype.card V : ℝ) * (((lam ^ (2 * r₁) - 1) / lam ^ (2 * r₁)) ^ M) := hdiv2
          _ = (Fintype.card V : ℝ) * (1 - x) ^ M := by rw [hdiv3]
      have hstep : 1 - x ≤ Real.exp (-x) := by
        have h := Real.add_one_le_exp (-x)
        linarith
      have hmm1 : (1 - x) ^ M ≤ Real.exp (-((M : ℝ) * x)) := by
        have hpow := pow_le_pow_left₀ hone_sub hstep M
        calc
          (1 - x) ^ M ≤ (Real.exp (-x)) ^ M := hpow
          _ = Real.exp ((M : ℝ) * (-x)) := (Real.exp_nat_mul (-x) M).symm
          _ = Real.exp (-((M : ℝ) * x)) := by congr 1; ring
      have hxge : x ≥ ((Δ : ℝ) ^ (2 * r₁))⁻¹ := by
        dsimp [x]
        have hlepow : lam ^ (2 * r₁) ≤ (Δ : ℝ) ^ (2 * r₁) := by
          exact pow_le_pow_left₀ (le_of_lt hlampos) hlam_le_D (2 * r₁)
        exact (inv_le_inv₀ hDpowpos hlam2pos).mpr hlepow
      have hMx : ((M : ℝ) * x) ≥ Real.log (8 / ε) := by
        have h1 : (M : ℝ) * x ≥ (M : ℝ) * (((Δ : ℝ) ^ (2 * r₁))⁻¹) := by
          exact mul_le_mul_of_nonneg_left hxge (by positivity : 0 ≤ (M : ℝ))
        have h2 : (M : ℝ) * ((Δ : ℝ) ^ (2 * r₁))⁻¹ ≥ Real.log (8 / ε) := by
          have hM2 : (Δ : ℝ) ^ (2 * r₁) * Real.log (8 / ε) ≤ (M : ℝ) := hM
          have hΔi : 0 ≤ ((Δ : ℝ) ^ (2 * r₁))⁻¹ := by positivity
          have h3 : (Δ : ℝ) ^ (2 * r₁) * Real.log (8 / ε) * ((Δ : ℝ) ^ (2 * r₁))⁻¹
              ≤ (M : ℝ) * ((Δ : ℝ) ^ (2 * r₁))⁻¹ := by
            exact mul_le_mul_of_nonneg_right hM2 hΔi
          have h4 : (Δ : ℝ) ^ (2 * r₁) * Real.log (8 / ε) * ((Δ : ℝ) ^ (2 * r₁))⁻¹
              = Real.log (8 / ε) := by
            field_simp [hDpowpos.ne']
          linarith
        linarith
      have hmm2 : Real.exp (-((M : ℝ) * x)) ≤ ε / 8 := by
        have hmono : Real.exp (-((M : ℝ) * x)) ≤ Real.exp (-Real.log (8 / ε)) := by
          exact Real.exp_le_exp.mpr (by linarith)
        have hlog : Real.exp (-Real.log (8 / ε)) = ε / 8 := by
          calc
            Real.exp (-Real.log (8 / ε)) = (Real.exp (Real.log (8 / ε)))⁻¹ := by rw [Real.exp_neg]
            _ = (8 / ε)⁻¹ := by rw [Real.exp_log (by positivity : 0 < 8 / ε)]
            _ = ε / 8 := by field_simp [ne_of_gt hε]
        exact le_trans hmono (le_of_eq hlog)
      have hmH4 : (mH : ℝ) ≤ (ε / 8) * (Fintype.card V : ℝ) := by
        have hn0 : 0 ≤ (Fintype.card V : ℝ) := by positivity
        calc
          (mH : ℝ) ≤ (Fintype.card V : ℝ) * (1 - x) ^ M := hmH3
          _ ≤ (Fintype.card V : ℝ) * Real.exp (-((M : ℝ) * x)) := by
                exact mul_le_mul_of_nonneg_left hmm1 hn0
          _ ≤ (Fintype.card V : ℝ) * (ε / 8) := by
                exact mul_le_mul_of_nonneg_left hmm2 hn0
          _ = (ε / 8) * (Fintype.card V : ℝ) := by ring
      have hdel_m : mG ≤ mH + D.card := by
        have h := EigenMult.del_mult_bound (G.adjMatrix ℝ) hA D lam
        simpa [mG, mH, R, Kf] using h
      have hnpos : 0 ≤ (Fintype.card V : ℝ) := by positivity
      have hsmall : (1 : ℝ) / ((r₁ + 1 : ℕ) : ℝ) ≤ ε / 8 := by
        have hposr : 0 < ((r₁ + 1 : ℕ) : ℝ) := by positivity
        have h8p : 0 < (8 : ℝ) := by norm_num
        have hc : (1 : ℝ) * 8 ≤ ε * (((r₁ + 1 : ℕ) : ℝ)) := by
          calc
            (1 : ℝ) * 8 = 8 := by norm_num
            _ ≤ (((r₁ + 1 : ℕ) : ℝ)) * ε := by simpa using hεr₁
            _ = ε * (((r₁ + 1 : ℕ) : ℝ)) := by ring
        exact (div_le_div_iff₀ hposr h8p).mpr hc
      have hdivcast : ((Fintype.card V / (r₁ + 1) : ℕ) : ℝ)
          ≤ (Fintype.card V : ℝ) / ((r₁ + 1 : ℕ) : ℝ) := by
        have hposr : 0 < ((r₁ + 1 : ℕ) : ℝ) := by positivity
        rw [le_div_iff₀ hposr]
        have hN : (Fintype.card V / (r₁ + 1) : ℕ) * (r₁ + 1) ≤ Fintype.card V :=
          Nat.div_mul_le_self (Fintype.card V) (r₁ + 1)
        exact_mod_cast hN
      have hpiece1 : ((Fintype.card V / (r₁ + 1) : ℕ) : ℝ) ≤ (ε / 8) * (Fintype.card V : ℝ) := by
        calc
          ((Fintype.card V / (r₁ + 1) : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) / ((r₁ + 1 : ℕ) : ℝ) := hdivcast
          _ = (Fintype.card V : ℝ) * (1 / ((r₁ + 1 : ℕ) : ℝ)) := by ring
          _ ≤ (Fintype.card V : ℝ) * (ε / 8) := by
                exact mul_le_mul_of_nonneg_left hsmall hnpos
          _ = (ε / 8) * (Fintype.card V : ℝ) := by ring
      have hεn8 : (ε * (Fintype.card V : ℝ)) / 8 ≥ 1 := by
        exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr (by simpa using hεn)
      have hpiece2 : (1 : ℝ) ≤ (ε / 8) * (Fintype.card V : ℝ) := by
        rw [show (ε / 8) * (Fintype.card V : ℝ) = (ε * (Fintype.card V : ℝ)) / 8 by ring]
        exact hεn8
      have hpiece3 : (C : ℝ) ≤ (ε / 8) * (Fintype.card V : ℝ) := by
        have h1 : 8 * (C : ℝ) / ε ≤ (Fintype.card V : ℝ) := hn_C
        have h2 : (8 * (C : ℝ) / ε) * ε ≤ (Fintype.card V : ℝ) * ε :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hε)
        have h2' : 8 * (C : ℝ) ≤ ε * (Fintype.card V : ℝ) := by
          field_simp [ne_of_gt hε] at h2
          nlinarith only [h2]
        have hC : (C : ℝ) ≤ (ε * (Fintype.card V : ℝ)) / 8 := by
          exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr (by nlinarith only [h2'])
        rw [show (ε / 8) * (Fintype.card V : ℝ) = (ε * (Fintype.card V : ℝ)) / 8 by ring]
        exact hC
      have hDb : (D.card : ℝ) ≤ ((Fintype.card V / (r₁ + 1) : ℕ) : ℝ) + 1 + (C : ℝ) := by
        have hD := hDcard
        exact_mod_cast hD
      have hmGf : (mG : ℝ) ≤ ε * (Fintype.card V : ℝ) := by
        have h1 : (mG : ℝ) ≤ (mH : ℝ) + (D.card : ℝ) := by
          have h := hdel_m
          exact_mod_cast h
        have h2 : (mH : ℝ) + (D.card : ℝ)
            ≤ (ε / 8) * (Fintype.card V : ℝ) + (((Fintype.card V / (r₁ + 1) : ℕ) : ℝ) + 1 + (C : ℝ)) := by
          exact add_le_add hmH4 hDb
        -- assemble: mH ≤ (ε/8)n ; D ≤ n/(r₁+1) + 1 + C ≤ (ε/8)n + (ε/8)n + (ε/8)n
        have h3a : (((Fintype.card V / (r₁ + 1) : ℕ) : ℝ) + 1 + (C : ℝ))
            ≤ (ε / 8) * (Fintype.card V : ℝ) + (ε / 8) * (Fintype.card V : ℝ) + (ε / 8) * (Fintype.card V : ℝ) := by
          have hq1 := hpiece1
          have hq2 := hpiece2
          have hq3 := hpiece3
          linarith only [hq1, hq2, hq3]
        have h3b : (ε / 8) * (Fintype.card V : ℝ) + ((ε / 8) * (Fintype.card V : ℝ) + (ε / 8) * (Fintype.card V : ℝ) + (ε / 8) * (Fintype.card V : ℝ))
            ≤ ε * (Fintype.card V : ℝ) := by
          ring_nf
          have hεn0 : 0 ≤ ε * (Fintype.card V : ℝ) := by positivity
          nlinarith only [hεn0]
        have h2b : (mH : ℝ) + (D.card : ℝ)
            ≤ (ε / 8) * (Fintype.card V : ℝ) + ((ε / 8) * (Fintype.card V : ℝ) + (ε / 8) * (Fintype.card V : ℝ) + (ε / 8) * (Fintype.card V : ℝ)) := by
          have hA := hmH4
          have hB := hDb
          -- D ≤ n/(r₁+1) + 1 + C ≤ (ε/8)n + (ε/8)n + (ε/8)n
          have hB' : (D.card : ℝ) ≤ ((ε / 8) * (Fintype.card V : ℝ) + (ε / 8) * (Fintype.card V : ℝ) + (ε / 8) * (Fintype.card V : ℝ)) := by
            exact le_trans hDb h3a
          linarith only [hA, hB']
        exact le_trans h1 (le_trans h2b h3b)
      exact hmGf

end

end Submission
