import Submission.Eigen
import Submission.RealizeAny
import Submission.KOrder

open EquiangularLinesFixedAngle
open Filter
open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option maxHeartbeats 1200000

/-! Basic Perron--Frobenius facts for adjacency matrices of graphs (and more generally
for symmetric matrices with non-negative entries).

Key content:
- the spectral radius of a non-negative symmetric matrix is attained as an eigenvalue;
- adjacency matrices of graphs on at most one vertex have spectral radius `0`, so the
  spectral radius order is at least `2` for positive reals;
- Rayleigh-type bounds for symmetric matrices. -/

open Classical in
/-- The adjacency matrix of a graph is Hermitian (self-adjoint over `ℝ`). -/
lemma adjMatrix_isHermitian {n : ℕ} (G : SimpleGraph (Fin n)) :
    (G.adjMatrix ℝ).IsHermitian := by
  classical
  rw [Matrix.isHermitian_iff_isSymm]
  exact SimpleGraph.isSymm_adjMatrix G

open Classical in
/-- Entries of an adjacency matrix are non-negative. -/
lemma adjMatrix_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    0 ≤ (G.adjMatrix ℝ) i j := by
  classical
  by_cases h : G.Adj i j <;> simp [SimpleGraph.adjMatrix_apply, h]

open Classical in
/-- Graphs on at most one vertex have zero adjacency matrix. -/
lemma adjMatrix_eq_zero_of_card_le_one {n : ℕ} (hn : n ≤ 1) (G : SimpleGraph (Fin n)) :
    G.adjMatrix ℝ = 0 := by
  classical
  ext i j
  have hij : i = j := by
    apply Fin.ext
    have hi : i.val < n := i.isLt
    have hj : j.val < n := j.isLt
    omega
  subst j
  by_cases h : G.Adj i i
  · exfalso
    exact G.loopless.irrefl i h
  · simp [SimpleGraph.adjMatrix_apply, h]

open Classical in
/-- Graphs on at most one vertex have spectral radius `0`. -/
lemma spectralRadius_eq_zero_of_card_le_one {n : ℕ} (hn : n ≤ 1) (G : SimpleGraph (Fin n)) :
    spectralRadius ℝ (G.adjMatrix ℝ) = 0 := by
  classical
  rw [adjMatrix_eq_zero_of_card_le_one hn G]
  exact spectrum.spectralRadius_zero

/-- The spectral radius order of a positive real, when finite, is at least `2`. -/
lemma spectralRadiusOrder_toNat_ge_two {lam : ℝ} (hlam : 0 < lam)
    (hk : spectralRadiusOrder lam < (⊤ : ℕ∞)) : 2 ≤ (spectralRadiusOrder lam).toNat := by
  classical
  have hw := spectralRadiusOrder_lt_top_witness (lam := lam) hk
  rcases hw with ⟨G, hG⟩
  by_contra h2
  have hle : (spectralRadiusOrder lam).toNat ≤ 1 := by omega
  have hz : spectralRadius ℝ (G.adjMatrix ℝ) = 0 :=
    spectralRadius_eq_zero_of_card_le_one hle G
  have hz' : ENNReal.ofReal lam = 0 := by
    calc
      ENNReal.ofReal lam = spectralRadius ℝ (G.adjMatrix ℝ) := hG.symm
      _ = 0 := hz
  have hlamle : lam ≤ 0 := ENNReal.ofReal_eq_zero.mp hz'
  linarith

/-- dot-product equals the coordinate inner product under `eucOfFun`. -/
lemma dotProduct_eq_inner {n : ℕ} (u v : Fin n → ℝ) :
    u ⬝ᵥ v = ⟪eucOfFun u, eucOfFun v⟫ := by
  rw [euclidean_inner_apply]
  simp [dotProduct, eucOfFun_apply]

/-- Dot product is ℝ-linear in the second argument for scalar multiplication. -/
lemma dotProduct_smul_right {n : ℕ} (c : ℝ) (u v : Fin n → ℝ) : u ⬝ᵥ (c • v) = c * (u ⬝ᵥ v) := by
  simp [dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

/-- The dot-product square of an eigenvector of an orthonormal basis is `1`. -/
lemma eigenvector_dotProduct_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (j : Fin n) : (hA.eigenvectorBasis j).ofLp ⬝ᵥ (hA.eigenvectorBasis j).ofLp = 1 := by
  classical
  let b := hA.eigenvectorBasis
  have hb : ‖b j‖ = 1 := hA.eigenvectorBasis.orthonormal.1 j
  calc
    (b j).ofLp ⬝ᵥ (b j).ofLp = ⟪eucOfFun ((b j).ofLp), eucOfFun ((b j).ofLp)⟫ :=
          dotProduct_eq_inner ((b j).ofLp) ((b j).ofLp)
    _ = ⟪b j, b j⟫ := by
          have h1 : eucOfFun ((b j).ofLp) = b j := by simp [eucOfFun]
          rw [h1]
    _ = ‖b j‖ ^ 2 := real_inner_self_eq_norm_sq (b j)
    _ = 1 := by rw [hb]; norm_num

/-- Quadratic form on an eigenvector. -/
lemma quad_eigenvector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (j : Fin n) : (hA.eigenvectorBasis j).ofLp ⬝ᵥ (A.mulVec ((hA.eigenvectorBasis j).ofLp))
      = hA.eigenvalues j := by
  classical
  rw [Matrix.IsHermitian.mulVec_eigenvectorBasis]
  rw [dotProduct_smul_right]
  rw [eigenvector_dotProduct_self A hA j]
  ring

/-- Dot product distributes over subtraction on the right. -/
lemma dotProduct_sub_right {n : ℕ} (u v w : Fin n → ℝ) : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w := by
  simp [dotProduct, Finset.sum_sub_distrib, mul_sub]

/-- The quadratic form as a double sum. -/
lemma quad_eq_double_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (A.mulVec x) = ∑ a : Fin n, ∑ b : Fin n, x a * (A a b * x b) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum]

/-- `x ⬝ (μx − Ax) = μ(x⬝x) − x⬝Ax`. -/
lemma dotProduct_smul_sub_mulVec {n : ℕ} (μ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    x ⬝ᵥ (((μ • (1 : Matrix (Fin n) (Fin n) ℝ)) - A) *ᵥ x) = μ * (x ⬝ᵥ x) - x ⬝ᵥ (A.mulVec x) := by
  classical
  have h1 : (∑ a : Fin n, ∑ b : Fin n, x a * ((if a = b then μ else 0) * x b))
      = μ * (x ⬝ᵥ x) := by
    simp [dotProduct, Finset.sum_ite_eq', Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  calc
    x ⬝ᵥ (((μ • (1 : Matrix (Fin n) (Fin n) ℝ)) - A) *ᵥ x)
        = ∑ a : Fin n, ∑ b : Fin n, x a * ((((μ • (1 : Matrix (Fin n) (Fin n) ℝ)) - A)) a b * x b) := by
          simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ = (∑ a : Fin n, ∑ b : Fin n, x a * ((if a = b then μ else 0) * x b))
        - (∑ a : Fin n, ∑ b : Fin n, x a * (A a b * x b)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro b hb
          have he : ((μ • (1 : Matrix (Fin n) (Fin n) ℝ)) - A) a b = (if a = b then μ else 0) - A a b := by
            by_cases h : a = b
            · subst b
              simp [Matrix.sub_apply, Pi.smul_apply, Matrix.one_apply, smul_eq_mul]
            · simp [Matrix.sub_apply, Pi.smul_apply, Matrix.one_apply, smul_eq_mul, h]
          rw [he]
          ring
    _ = μ * (x ⬝ᵥ x) - x ⬝ᵥ (A.mulVec x) := by
          rw [h1]
          simp [quad_eq_double_sum A x]

/-- If all eigenvalues are at most `μ`, then the quadratic form is bounded by `μ ‖x‖²`. -/
lemma quad_le_of_eigenvalues_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    {μ : ℝ} (hle : ∀ i : Fin n, hA.eigenvalues i ≤ μ) (x : Fin n → ℝ) :
    x ⬝ᵥ (A.mulVec x) ≤ μ * (x ⬝ᵥ x) := by
  classical
  have hpsd : (μ • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef :=
    sub_psd_of_eigenvalues_le A hA hle
  have hq : 0 ≤ star x ⬝ᵥ ((μ • (1 : Matrix (Fin n) (Fin n) ℝ) - A) *ᵥ x) :=
    hpsd.dotProduct_mulVec_nonneg x
  have hstar : star x = x := by
    funext a
    change star (x a) = x a
    simp
  have hq' : 0 ≤ μ * (x ⬝ᵥ x) - x ⬝ᵥ (A.mulVec x) := by
    rw [hstar] at hq
    simpa [dotProduct_smul_sub_mulVec] using hq
  linarith

/-- `|a||b| + a·b ≥ 0`. -/
lemma abs_mul_add_self_nonneg (a b : ℝ) : 0 ≤ |a| * |b| + a * b := by
  have hz : 0 ≤ |a * b| + a * b := by
    have h : -(a * b) ≤ |a * b| := by simpa using (le_abs_self (-(a * b)))
    linarith
  rwa [abs_mul] at hz

/-- For a matrix with non-negative entries, `−Q(x) ≤ Q(|x|)`. -/
lemma quad_neg_le_quad_abs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hnonneg : ∀ i j : Fin n, 0 ≤ A i j) (x : Fin n → ℝ) :
    -(x ⬝ᵥ (A.mulVec x)) ≤ (fun a => |x a|) ⬝ᵥ (A.mulVec (fun a => |x a|)) := by
  classical
  have hnonneg_sum : 0 ≤ ((fun a : Fin n => |x a|) ⬝ᵥ (A.mulVec (fun a => |x a|)))
      + (x ⬝ᵥ (A.mulVec x)) := by
    rw [quad_eq_double_sum A (fun a : Fin n => |x a|), quad_eq_double_sum A x]
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

/-- Every element of the real spectrum of a Hermitian matrix is one of its eigenvalues. -/
lemma exists_eigenvalue_of_mem_spectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) {μ : ℝ} (hμ : μ ∈ spectrum ℝ A) : ∃ j : Fin n, hA.eigenvalues j = μ := by
  classical
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hμ
  rw [hA.charpoly_eq] at hμ
  have hex := (Polynomial.isRoot_prod (Finset.univ) (fun j : Fin n =>
    Polynomial.X - Polynomial.C (hA.eigenvalues j)) μ).1 hμ
  rcases hex with ⟨j, hj, hrootj⟩
  refine ⟨j, ?_⟩
  exact (Polynomial.root_X_sub_C (a := hA.eigenvalues j) (b := μ)).mp hrootj

/-- Absolute values of eigenvalues are bounded by the spectral radius. -/
lemma eigenvalue_abs_le_of_spectralRadius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) {lam : ℝ} (hlam : 0 ≤ lam) (hρ : spectralRadius ℝ A = ENNReal.ofReal lam)
    (i : Fin n) : |hA.eigenvalues i| ≤ lam := by
  have hge := spectralRadius_ge_eigenvalue A hA i
  have hle : ENNReal.ofReal (|hA.eigenvalues i|) ≤ ENNReal.ofReal lam := by
    rwa [hρ] at hge
  exact (ENNReal.ofReal_le_ofReal_iff hlam).mp hle

/-- An index where the eigenvalue value is maximal. -/
lemma exists_top_eigenvalue_index {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hn : 0 < n) : ∃ i : Fin n, ∀ j : Fin n, hA.eigenvalues j ≤ hA.eigenvalues i := by
  classical
  let S : Finset ℝ := (Finset.univ : Finset (Fin n)).image hA.eigenvalues
  have hSne : S.Nonempty := by
    refine ⟨hA.eigenvalues ⟨0, hn⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩
  let m := S.max' hSne
  have hmS : m ∈ S := S.max'_mem hSne
  rcases Finset.mem_image.mp hmS with ⟨i, hi, hmi⟩
  refine ⟨i, ?_⟩
  intro j
  have hmem : hA.eigenvalues j ∈ S := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  calc
    hA.eigenvalues j ≤ m := Finset.le_max' S (hA.eigenvalues j) hmem
    _ = hA.eigenvalues i := hmi.symm

/-- The maximal eigenvalue value dominates all absolute eigenvalue values of a
non-negative symmetric matrix. -/
lemma top_eigenvalue_ge_abs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hnonneg : ∀ i j : Fin n, 0 ≤ A i j) (hn : 0 < n)
    (i : Fin n) (hi : ∀ j : Fin n, hA.eigenvalues j ≤ hA.eigenvalues i) (j : Fin n) :
    |hA.eigenvalues j| ≤ hA.eigenvalues i := by
  classical
  have hle : hA.eigenvalues j ≤ hA.eigenvalues i := hi j
  have hneg : -(hA.eigenvalues j) ≤ hA.eigenvalues i := by
    let w : Fin n → ℝ := (hA.eigenvectorBasis j).ofLp
    have hqe : w ⬝ᵥ (A.mulVec w) = hA.eigenvalues j := by
      simpa [w] using quad_eigenvector A hA j
    have hqabs : (fun a => |w a|) ⬝ᵥ (A.mulVec (fun a => |w a|)) ≤ hA.eigenvalues i := by
      have hray := quad_le_of_eigenvalues_le A hA hi (fun a : Fin n => |w a|)
      have hw1 : w ⬝ᵥ w = 1 := by simpa [w] using eigenvector_dotProduct_self A hA j
      have hw2 : (fun a : Fin n => |w a|) ⬝ᵥ (fun a : Fin n => |w a|) = w ⬝ᵥ w := by
        unfold dotProduct
        refine Finset.sum_congr rfl ?_
        intro a ha
        rw [← pow_two, ← pow_two, sq_abs]
      calc
        (fun a : Fin n => |w a|) ⬝ᵥ (A.mulVec (fun a => |w a|))
            ≤ hA.eigenvalues i * ((fun a : Fin n => |w a|) ⬝ᵥ (fun a : Fin n => |w a|)) := hray
        _ ≤ hA.eigenvalues i * (w ⬝ᵥ w) := by rw [hw2]
        _ = hA.eigenvalues i := by rw [hw1, mul_one]
    have hql : -(w ⬝ᵥ (A.mulVec w)) ≤ (fun a => |w a|) ⬝ᵥ (A.mulVec (fun a => |w a|)) :=
      quad_neg_le_quad_abs A hnonneg w
    linarith
  exact (abs_le (a := hA.eigenvalues j) (b := hA.eigenvalues i)).mpr ⟨by linarith, hle⟩

/-- If the spectral radius is a positive value, then that value is attained as an
eigenvalue of a non-negative symmetric matrix. -/
lemma exists_eigenvalue_eq_of_spectralRadius {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hnonneg : ∀ i j : Fin n, 0 ≤ A i j) {lam : ℝ} (hlam0 : 0 < lam)
    (hρ : spectralRadius ℝ A = ENNReal.ofReal lam) : ∃ j : Fin n, hA.eigenvalues j = lam := by
  classical
  rcases exists_top_eigenvalue_index A hA hn with ⟨i, hi⟩
  have htop : ∀ j : Fin n, |hA.eigenvalues j| ≤ hA.eigenvalues i :=
    fun j => top_eigenvalue_ge_abs A hA hnonneg hn i hi j
  have hσi_nonneg : 0 ≤ hA.eigenvalues i := by
    have habs : |hA.eigenvalues i| ≤ hA.eigenvalues i := htop i
    have h1 := (abs_le (a := hA.eigenvalues i) (b := hA.eigenvalues i)).mp habs
    linarith
  have hρ_le : spectralRadius ℝ A ≤ ENNReal.ofReal (hA.eigenvalues i) := by
    rw [spectralRadius]
    refine iSup_le (fun μ => ?_)
    refine iSup_le (fun hμ => ?_)
    rcases exists_eigenvalue_of_mem_spectrum A hA hμ with ⟨j, hj⟩
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
  have hlam_le : lam ≤ hA.eigenvalues i := by
    have h1 : ENNReal.ofReal lam ≤ ENNReal.ofReal (hA.eigenvalues i) := by
      calc
        ENNReal.ofReal lam = spectralRadius ℝ A := hρ.symm
        _ ≤ ENNReal.ofReal (hA.eigenvalues i) := hρ_le
    exact (ENNReal.ofReal_le_ofReal_iff hσi_nonneg).mp h1
  have htop_le_lam : hA.eigenvalues i ≤ lam :=
    eigenvalues_le_of_spectralRadius A hA hlam0 hρ i
  refine ⟨i, ?_⟩
  exact le_antisymm htop_le_lam hlam_le

end Submission
