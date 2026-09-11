import Submission.Perron
import Submission.RealizeAny

open EquiangularLinesFixedAngle
open Filter
open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option maxHeartbeats 1200000

/-! The disjoint-union lower bound (Proposition 2.2 of the paper).

If `k = spectralRadiusOrder λ < ∞` with `λ = (1-α)/(2α) > 0`, let `H` be a `k0`-vertex
graph with spectral radius `λ` (`k0 := k.toNat ≥ 2`).  For `d ≥ 1` write
`d-1 = c(k0-1) + t` with `0 ≤ t < k0-1`.  We construct `n = c·k0 + t` lines in `𝔼^d`.

Construction (direct coordinates): in `𝔼^d ≅ ⊕_{c} 𝔼^{k0-1} ⊕ 𝔼^t ⊕ 𝔼` take unit vectors
`v = √(1-α)·y ⊕ √α·e_w` for the `c` copies (where `y_i` realize the Gram matrix
`(λI - A_H)/λ`, so `⟨y_i,y_j⟩ ∈ {0, -1/λ}`), and `√α·e_w ⊕ √(1-α)·e_u` for the `t`
isolated vertices. -/

/-- Multiplication by a scalar matrix: `(c•1) *ᵥ v = c • v`. -/
lemma mulVec_smul_one {n : ℕ} (c : ℝ) (v : Fin n → ℝ) :
    ((c • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ v) = c • v := by
  classical
  funext i
  simp [Matrix.mulVec, dotProduct, smul_eq_mul, Matrix.one_apply, Finset.sum_ite_eq']

/-- `(B - C) *ᵥ v = B *ᵥ v - C *ᵥ v`. -/
lemma mulVec_sub {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ((B - C).mulVec v) = B.mulVec v - C.mulVec v := by
  classical
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, mul_sub, sub_mul]

/-- If a Hermitian matrix has spectral radius `λ > 0` (attained by an eigenvalue of a
nonnegative matrix), then `λI − A` has rank at most `n-1`. -/
lemma rank_lam_sub_le_pred {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hnonneg : ∀ i j : Fin n, 0 ≤ A i j) {lam : ℝ}
    (hlam0 : 0 < lam) (hρ : spectralRadius ℝ A = ENNReal.ofReal lam) :
    (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A).rank ≤ n - 1 := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A
  let f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := B.mulVecLin
  rcases exists_eigenvalue_eq_of_spectralRadius hn A hA hnonneg hlam0 hρ with ⟨j, hj⟩
  let w : Fin n → ℝ := (hA.eigenvectorBasis j).ofLp
  have hw_ker : w ∈ LinearMap.ker f := by
    dsimp [f, w]
    apply LinearMap.mem_ker.mpr
    dsimp [B]
    rw [mulVec_sub, mulVec_smul_one, Matrix.IsHermitian.mulVec_eigenvectorBasis, hj]
    simp
  have hwne : w ≠ 0 := by
    intro hw0
    have hw0' : (hA.eigenvectorBasis j).ofLp = 0 := by simpa [w] using hw0
    have hd := eigenvector_dotProduct_self A hA j
    rw [hw0'] at hd
    simp at hd
  have hker_ne_bot : LinearMap.ker f ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨w, hw_ker, hwne⟩
  have hker_pos : 0 < Module.finrank ℝ (LinearMap.ker f) := by
    have hz : Module.finrank ℝ (LinearMap.ker f) ≠ 0 := by
      intro h0
      exact hker_ne_bot (Submodule.finrank_eq_zero.mp h0)
    exact Nat.pos_of_ne_zero hz
  have hsp : (Submodule.span ℝ (Set.range B.col)) = LinearMap.range f := by
    exact (Matrix.range_mulVecLin B).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hdom : Module.finrank ℝ (Fin n → ℝ) = n := by
    simpa using Module.finrank_pi ℝ (Fin n)
  rw [Matrix.rank_eq_finrank_span_cols, hsp]
  omega

open Classical in
/-- The per-copy Gram matrix: `(λI − A_H)/λ`. -/
noncomputable def perCopyGram (lam : ℝ) {k0 : ℕ} (H : SimpleGraph (Fin k0)) :
    Matrix (Fin k0) (Fin k0) ℝ :=
  (1 / lam) • ((lam • (1 : Matrix (Fin k0) (Fin k0) ℝ)) - (H.adjMatrix ℝ))

open Classical in
/-- Realize the per-copy vectors `y` in `𝔼^{k0-1}`. -/
lemma perCopyRealize (lam : ℝ) {k0 : ℕ} (H : SimpleGraph (Fin k0))
    (hk0 : 2 ≤ k0) (hlam0 : 0 < lam)
    (hρ : spectralRadius ℝ (H.adjMatrix ℝ) = ENNReal.ofReal lam) :
    ∃ y : Fin k0 → Euc (k0 - 1), Matrix.gram ℝ y = perCopyGram lam H := by
  classical
  have hA : (H.adjMatrix ℝ).IsHermitian := adjMatrix_isHermitian H
  have hnonneg : ∀ i j : Fin k0, 0 ≤ (H.adjMatrix ℝ) i j := adjMatrix_nonneg H
  have hn : 0 < k0 := by omega
  have hZ : (lam • (1 : Matrix (Fin k0) (Fin k0) ℝ) - (H.adjMatrix ℝ)).PosSemidef :=
    sub_psd_of_spectralRadius (H.adjMatrix ℝ) hA hlam0 hρ
  have hC : (perCopyGram lam H).PosSemidef := by
    dsimp [perCopyGram]
    exact hZ.smul (a := (1 / lam)) (by positivity)
  have hr : (perCopyGram lam H).rank ≤ k0 - 1 := by
    dsimp [perCopyGram]
    have hne : (1 / lam) ≠ 0 := by positivity
    have hz : (1 / lam) ∈ nonZeroDivisors ℝ := mem_nonZeroDivisors_of_ne_zero hne
    have hs := rank_smul_of_mem_nonZeroDivisors
      ((lam • (1 : Matrix (Fin k0) (Fin k0) ℝ)) - (H.adjMatrix ℝ)) hz
    rw [hs]
    exact rank_lam_sub_le_pred hn (H.adjMatrix ℝ) hA hnonneg hlam0 hρ
  exact gram_realize_any (ι := Fin k0) (d := k0 - 1) (perCopyGram lam H) hC hr

/-- dimension: `c*(k0-1) + t + 1` is the ambient dimension, where
`c = (d-1)/(k0-1)` and `t = (d-1)%(k0-1)`, equals `d` for `d ≥ 1`. -/
lemma dim_eq_of_div_mod {k0 d : ℕ} (hk0 : 2 ≤ k0) (hd : 1 ≤ d) :
    ((d - 1) / (k0 - 1)) * (k0 - 1) + ((d - 1) % (k0 - 1)) + 1 = d := by
  have hm : ((d - 1) / (k0 - 1)) * (k0 - 1) + ((d - 1) % (k0 - 1)) = d - 1 := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod (d - 1) (k0 - 1)
  omega

/-- The count `c*k0 + t` where `c = (d-1)/(k0-1)`, `t = (d-1)%(k0-1)` equals
`⌊k0(d-1)/(k0-1)⌋₊` (in nat-cast form). -/
lemma floor_count_cast {k0 d : ℕ} (hk0 : 2 ≤ k0) (hd : 1 ≤ d) :
    ⌊(((k0 * (d - 1) : ℕ) : ℝ) / (((k0 - 1 : ℕ)) : ℝ))⌋₊
      = ((d - 1) / (k0 - 1)) * k0 + ((d - 1) % (k0 - 1)) := by
  classical
  let c : ℕ := (d - 1) / (k0 - 1)
  let t : ℕ := (d - 1) % (k0 - 1)
  have hk : 0 < (k0 - 1 : ℕ) := by omega
  have hnonneg : 0 ≤ (((k0 * (d - 1) : ℕ) : ℝ) / (((k0 - 1 : ℕ)) : ℝ)) := by positivity
  have hm : (d - 1) = c * (k0 - 1) + t := by
    dsimp [c, t]
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod (d - 1) (k0 - 1)).symm
  have htl : t < k0 - 1 := by
    dsimp [t]
    exact Nat.mod_lt (d - 1) hk
  have hmR : ((d - 1 : ℕ) : ℝ) = (c * (k0 - 1) + t : ℕ) := by exact_mod_cast hm
  have hkR : (k0 : ℝ) = ((k0 - 1 : ℕ) : ℝ) + 1 := by
    have h : ((k0 - 1 : ℕ) : ℝ) + 1 = (k0 : ℝ) := by
      rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num]
      rw [← Nat.cast_add]
      congr 1
      omega
    exact h.symm
  have hfrac_ge : (0 : ℝ) ≤ (t : ℝ) / ((k0 - 1 : ℕ) : ℝ) := by positivity
  have hfrac_lt : (t : ℝ) / ((k0 - 1 : ℕ) : ℝ) < 1 := by
    rw [div_lt_one]
    · exact_mod_cast htl
    · positivity
  have hval : (((k0 * (d - 1) : ℕ) : ℝ) / (((k0 - 1 : ℕ)) : ℝ))
      = ((c * k0 + t : ℕ) : ℝ) + (t : ℝ) / ((k0 - 1 : ℕ) : ℝ) := by
    have hn2 : (((k0 * (d - 1) : ℕ) : ℝ)) = ((k0 : ℝ) * ((d - 1 : ℕ) : ℝ)) := by norm_num
    rw [hn2]
    have hnum : ((k0 : ℝ) * ((d - 1 : ℕ) : ℝ))
        = (((c * k0 + t : ℕ) : ℝ) * ((k0 - 1 : ℕ) : ℝ) + (t : ℝ)) := by
      rw [hmR]
      push_cast
      rw [hkR]
      ring
    rw [hnum]
    field_simp [show ((k0 - 1 : ℕ) : ℝ) ≠ 0 by positivity]
  have hfl : ⌊(((k0 * (d - 1) : ℕ) : ℝ) / (((k0 - 1 : ℕ)) : ℝ))⌋₊ = (c * k0 + t : ℕ) := by
    rw [Nat.floor_eq_iff hnonneg]
    constructor
    · rw [hval]
      linarith
    · rw [hval]
      linarith
  dsimp [c, t] at hfl
  rw [hfl]

/-- the real-subtraction version of the floor formula used in the theorem. -/
lemma floor_count_real_sub {k0 d : ℕ} (hk0 : 2 ≤ k0) (hd : 1 ≤ d) :
    ⌊((k0 * (d - 1) : ℝ) / (k0 - 1 : ℝ))⌋₊
      = ((d - 1) / (k0 - 1)) * k0 + ((d - 1) % (k0 - 1)) := by
  have hdd : ((k0 * (d - 1) : ℝ) / (k0 - 1 : ℝ))
      = (((k0 * (d - 1) : ℕ) : ℝ) / (((k0 - 1 : ℕ)) : ℝ)) := by
    have hkd : ((d - 1 : ℕ) : ℝ) = (d - 1 : ℝ) := by
      rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ d)]
      norm_num
    have hkk : ((k0 - 1 : ℕ) : ℝ) = (k0 - 1 : ℝ) := by
      rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ k0)]
      norm_num
    congr 1
    · rw [← hkd]
      norm_num
    · exact hkk.symm
  rw [hdd]
  exact floor_count_cast hk0 hd

end Submission
