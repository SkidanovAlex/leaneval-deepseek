import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore
import Submission.Work.ORVonNeumann.Rep.vnBlockDiagDefs

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace
open scoped InnerProduct

namespace Work.ORVonNeumann.Rep

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-! ### Coordinate formulas for the block inclusions and retractions -/

theorem vnBd_hcoord_incL_inl (a b : ℕ) (j : Fin a) (x : HSum (G := G) a) :
    hcoord (G := G) (a + b) (finSumFinEquiv (Sum.inl j)) (incL (G := G) a b x)
      = hcoord (G := G) a j x := by
  simp only [incL, sum_apply, ContinuousLinearMap.comp_apply]
  rw [map_sum, Finset.sum_eq_single j]
  · rw [hcoord_hinclude, if_pos rfl]
  · intro j' _ hj'
    rw [hcoord_hinclude, if_neg]
    intro h
    exact hj' (Sum.inl.inj (finSumFinEquiv.injective h)).symm
  · intro h; exact absurd (Finset.mem_univ j) h

theorem vnBd_hcoord_incL_inr (a b : ℕ) (k : Fin b) (x : HSum (G := G) a) :
    hcoord (G := G) (a + b) (finSumFinEquiv (Sum.inr k)) (incL (G := G) a b x) = 0 := by
  simp only [incL, sum_apply, ContinuousLinearMap.comp_apply]
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hcoord_hinclude, if_neg]
  intro h
  exact Sum.inr_ne_inl (finSumFinEquiv.injective h)

theorem vnBd_hcoord_incR_inl (a b : ℕ) (j : Fin a) (y : HSum (G := G) b) :
    hcoord (G := G) (a + b) (finSumFinEquiv (Sum.inl j)) (incR (G := G) a b y) = 0 := by
  simp only [incR, sum_apply, ContinuousLinearMap.comp_apply]
  rw [map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [hcoord_hinclude, if_neg]
  intro h
  exact Sum.inl_ne_inr (finSumFinEquiv.injective h)

theorem vnBd_hcoord_incR_inr (a b : ℕ) (k : Fin b) (y : HSum (G := G) b) :
    hcoord (G := G) (a + b) (finSumFinEquiv (Sum.inr k)) (incR (G := G) a b y)
      = hcoord (G := G) b k y := by
  simp only [incR, sum_apply, ContinuousLinearMap.comp_apply]
  rw [map_sum, Finset.sum_eq_single k]
  · rw [hcoord_hinclude, if_pos rfl]
  · intro k' _ hk'
    rw [hcoord_hinclude, if_neg]
    intro h
    exact hk' (Sum.inr.inj (finSumFinEquiv.injective h)).symm
  · intro h; exact absurd (Finset.mem_univ k) h

theorem vnBd_hcoord_retL (a b : ℕ) (j : Fin a) (x : HSum (G := G) (a + b)) :
    hcoord (G := G) a j (retL (G := G) a b x)
      = hcoord (G := G) (a + b) (finSumFinEquiv (Sum.inl j)) x := by
  simp only [retL, sum_apply, ContinuousLinearMap.comp_apply]
  rw [map_sum, Finset.sum_eq_single j]
  · rw [hcoord_hinclude, if_pos rfl]
  · intro j' _ hj'
    rw [hcoord_hinclude, if_neg]
    intro h
    exact hj' h.symm
  · intro h; exact absurd (Finset.mem_univ j) h

theorem vnBd_hcoord_retR (a b : ℕ) (k : Fin b) (x : HSum (G := G) (a + b)) :
    hcoord (G := G) b k (retR (G := G) a b x)
      = hcoord (G := G) (a + b) (finSumFinEquiv (Sum.inr k)) x := by
  simp only [retR, sum_apply, ContinuousLinearMap.comp_apply]
  rw [map_sum, Finset.sum_eq_single k]
  · rw [hcoord_hinclude, if_pos rfl]
  · intro k' _ hk'
    rw [hcoord_hinclude, if_neg]
    intro h
    exact hk' h.symm
  · intro h; exact absurd (Finset.mem_univ k) h

/-! ### The retraction identities -/

theorem vnBd_retL_incL (a b : ℕ) (x : HSum (G := G) a) :
    retL (G := G) a b (incL (G := G) a b x) = x := by
  apply hsum_ext
  intro j
  rw [vnBd_hcoord_retL, vnBd_hcoord_incL_inl]

theorem vnBd_retR_incL (a b : ℕ) (x : HSum (G := G) a) :
    retR (G := G) a b (incL (G := G) a b x) = 0 := by
  apply hsum_ext
  intro k
  rw [vnBd_hcoord_retR, vnBd_hcoord_incL_inr]
  simp

theorem vnBd_retL_incR (a b : ℕ) (y : HSum (G := G) b) :
    retL (G := G) a b (incR (G := G) a b y) = 0 := by
  apply hsum_ext
  intro j
  rw [vnBd_hcoord_retL, vnBd_hcoord_incR_inl]
  simp

theorem vnBd_retR_incR (a b : ℕ) (y : HSum (G := G) b) :
    retR (G := G) a b (incR (G := G) a b y) = y := by
  apply hsum_ext
  intro k
  rw [vnBd_hcoord_retR, vnBd_hcoord_incR_inr]

theorem vnBd_incL_retL_add_incR_retR (a b : ℕ) (x : HSum (G := G) (a + b)) :
    incL (G := G) a b (retL (G := G) a b x) + incR (G := G) a b (retR (G := G) a b x) = x := by
  apply hsum_ext
  intro i
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  rcases s with j | k
  · rw [map_add, vnBd_hcoord_incL_inl, vnBd_hcoord_incR_inl, vnBd_hcoord_retL]
    simp
  · rw [map_add, vnBd_hcoord_incL_inr, vnBd_hcoord_incR_inr, vnBd_hcoord_retR]
    simp

/-! ### The `δ` vectors of the blocks -/

theorem vnBd_hdelta_incL (a b : ℕ) (j : Fin a) :
    incL (G := G) a b (hdelta (G := G) a j)
      = hdelta (G := G) (a + b) (finSumFinEquiv (Sum.inl j)) := by
  simp only [incL, sum_apply, ContinuousLinearMap.comp_apply]
  rw [Finset.sum_eq_single j]
  · rw [hcoord_hdelta, if_pos rfl]
    rfl
  · intro j' _ hj'
    rw [hcoord_hdelta, if_neg hj', map_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem vnBd_hdelta_incR (a b : ℕ) (k : Fin b) :
    incR (G := G) a b (hdelta (G := G) b k)
      = hdelta (G := G) (a + b) (finSumFinEquiv (Sum.inr k)) := by
  simp only [incR, sum_apply, ContinuousLinearMap.comp_apply]
  rw [Finset.sum_eq_single k]
  · rw [hcoord_hdelta, if_pos rfl]
    rfl
  · intro k' _ hk'
    rw [hcoord_hdelta, if_neg hk', map_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-! ### Adjoints, inner products and norms -/

theorem vnBd_adjoint_incL (a b : ℕ) :
    ContinuousLinearMap.adjoint (incL (G := G) a b) = retL (G := G) a b := by
  simp only [incL, retL]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, hinclude_adjoint, hcoord_adjoint]

theorem vnBd_adjoint_incR (a b : ℕ) :
    ContinuousLinearMap.adjoint (incR (G := G) a b) = retR (G := G) a b := by
  simp only [incR, retR]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, hinclude_adjoint, hcoord_adjoint]

theorem vnBd_inner_incL_incL (a b : ℕ) (x y : HSum (G := G) a) :
    inner ℂ (incL (G := G) a b x) (incL (G := G) a b y) = inner ℂ x y := by
  rw [← ContinuousLinearMap.adjoint_inner_right (A := incL (G := G) a b) (x := x)
    (y := incL (G := G) a b y), vnBd_adjoint_incL, vnBd_retL_incL]

theorem vnBd_inner_incL_incR (a b : ℕ) (x : HSum (G := G) a) (y : HSum (G := G) b) :
    inner ℂ (incL (G := G) a b x) (incR (G := G) a b y) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right (A := incL (G := G) a b) (x := x)
    (y := incR (G := G) a b y), vnBd_adjoint_incL, vnBd_retL_incR, inner_zero_right]

theorem vnBd_inner_incR_incR (a b : ℕ) (x y : HSum (G := G) b) :
    inner ℂ (incR (G := G) a b x) (incR (G := G) a b y) = inner ℂ x y := by
  rw [← ContinuousLinearMap.adjoint_inner_right (A := incR (G := G) a b) (x := x)
    (y := incR (G := G) a b y), vnBd_adjoint_incR, vnBd_retR_incR]

theorem vnBd_inner_incR_incL (a b : ℕ) (x : HSum (G := G) b) (y : HSum (G := G) a) :
    inner ℂ (incR (G := G) a b x) (incL (G := G) a b y) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right (A := incR (G := G) a b) (x := x)
    (y := incL (G := G) a b y), vnBd_adjoint_incR, vnBd_retR_incL, inner_zero_right]

theorem vnBd_norm_incL (a b : ℕ) (x : HSum (G := G) a) : ‖incL (G := G) a b x‖ = ‖x‖ := by
  have h := vnBd_inner_incL_incL (G := G) a b x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ((‖incL (G := G) a b x‖ : ℝ) : ℂ) ^ 2 = ((‖x‖ : ℝ) : ℂ) ^ 2 := h
  have h3 : ((‖incL (G := G) a b x‖ ^ 2 : ℝ) : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow, Complex.ofReal_pow]; exact h2
  have h4 : ‖incL (G := G) a b x‖ ^ 2 = ‖x‖ ^ 2 := Complex.ofReal_inj.mp h3
  nlinarith [norm_nonneg (incL (G := G) a b x), norm_nonneg x]

theorem vnBd_norm_incR (a b : ℕ) (y : HSum (G := G) b) : ‖incR (G := G) a b y‖ = ‖y‖ := by
  have h := vnBd_inner_incR_incR (G := G) a b y y
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ((‖incR (G := G) a b y‖ : ℝ) : ℂ) ^ 2 = ((‖y‖ : ℝ) : ℂ) ^ 2 := h
  have h3 : ((‖incR (G := G) a b y‖ ^ 2 : ℝ) : ℂ) = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow, Complex.ofReal_pow]; exact h2
  have h4 : ‖incR (G := G) a b y‖ ^ 2 = ‖y‖ ^ 2 := Complex.ofReal_inj.mp h3
  nlinarith [norm_nonneg (incR (G := G) a b y), norm_nonneg y]

/-! ### The block structure of `blockDiag` -/

theorem vnBd_blockDiag_apply_inl_inl {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (j : Fin n) (j' : Fin m) :
    (Work.ORVonNeumann.blockDiag A B) (finSumFinEquiv (Sum.inl j))
      (finSumFinEquiv (Sum.inl j')) = A j j' := by
  simp only [Work.ORVonNeumann.blockDiag, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem vnBd_blockDiag_apply_inl_inr {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (j : Fin n) (k' : Fin q) :
    (Work.ORVonNeumann.blockDiag A B) (finSumFinEquiv (Sum.inl j))
      (finSumFinEquiv (Sum.inr k')) = 0 := by
  simp only [Work.ORVonNeumann.blockDiag, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

theorem vnBd_blockDiag_apply_inr_inl {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (k : Fin p) (j' : Fin m) :
    (Work.ORVonNeumann.blockDiag A B) (finSumFinEquiv (Sum.inr k))
      (finSumFinEquiv (Sum.inl j')) = 0 := by
  simp only [Work.ORVonNeumann.blockDiag, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem vnBd_blockDiag_apply_inr_inr {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (k : Fin p) (k' : Fin q) :
    (Work.ORVonNeumann.blockDiag A B) (finSumFinEquiv (Sum.inr k))
      (finSumFinEquiv (Sum.inr k')) = B k k' := by
  simp only [Work.ORVonNeumann.blockDiag, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

theorem vnBd_retL_matOp_blockDiag {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (w : HSum (G := G) (m + q)) :
    retL (G := G) n p (matOp (G := G) (Work.ORVonNeumann.blockDiag A B) w)
      = matOp (G := G) A (retL (G := G) m q w) := by
  apply hsum_ext
  intro j
  rw [vnBd_hcoord_retL, hcoord_matOp_apply, hcoord_matOp_apply]
  simp_rw [vnBd_hcoord_retL (G := G)]
  have hzero : (∑ k' : Fin q,
        ((Work.ORVonNeumann.blockDiag A B) (finSumFinEquiv (Sum.inl j))
          (finSumFinEquiv (Sum.inr k')) : boundedEnd G)
            (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inr k')) w)) = 0 := by
    refine Finset.sum_eq_zero fun k' _ => ?_
    rw [vnBd_blockDiag_apply_inl_inr]
    simp
  have hleft : (∑ j' : Fin m,
        ((Work.ORVonNeumann.blockDiag A B) (finSumFinEquiv (Sum.inl j))
          (finSumFinEquiv (Sum.inl j')) : boundedEnd G)
            (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inl j')) w))
      = ∑ j' : Fin m, ((A j j' : ↥(groupVonNeumann G)) : boundedEnd G)
            (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inl j')) w) := by
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [vnBd_blockDiag_apply_inl_inl]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type, hleft, hzero, add_zero]

theorem vnBd_retR_matOp_blockDiag {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (w : HSum (G := G) (m + q)) :
    retR (G := G) n p (matOp (G := G) (Work.ORVonNeumann.blockDiag A B) w)
      = matOp (G := G) B (retR (G := G) m q w) := by
  apply hsum_ext
  intro k
  rw [vnBd_hcoord_retR, hcoord_matOp_apply, hcoord_matOp_apply]
  simp_rw [vnBd_hcoord_retR (G := G)]
  have hzero : (∑ j' : Fin m,
        ((Work.ORVonNeumann.blockDiag A B) (finSumFinEquiv (Sum.inr k))
          (finSumFinEquiv (Sum.inl j')) : boundedEnd G)
            (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inl j')) w)) = 0 := by
    refine Finset.sum_eq_zero fun j' _ => ?_
    rw [vnBd_blockDiag_apply_inr_inl]
    simp
  have hright : (∑ k' : Fin q,
        ((Work.ORVonNeumann.blockDiag A B) (finSumFinEquiv (Sum.inr k))
          (finSumFinEquiv (Sum.inr k')) : boundedEnd G)
            (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inr k')) w))
      = ∑ k' : Fin q, ((B k k' : ↥(groupVonNeumann G)) : boundedEnd G)
            (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inr k')) w) := by
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [vnBd_blockDiag_apply_inr_inr]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type, hzero, zero_add, hright]

/-! ### Membership in the kernel of the block-diagonal matrix operator -/

theorem vnBd_mem_ker_blockDiag {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (w : HSum (G := G) (m + q)) :
    w ∈ (matOp (G := G) (Work.ORVonNeumann.blockDiag A B)).ker ↔
      retL (G := G) m q w ∈ (matOp (G := G) A).ker ∧
        retR (G := G) m q w ∈ (matOp (G := G) B).ker := by
  have key : ∀ v : HSum (G := G) (m + q),
      matOp (G := G) (Work.ORVonNeumann.blockDiag A B) v = 0 ↔
        retL (G := G) n p (matOp (G := G) (Work.ORVonNeumann.blockDiag A B) v) = 0 ∧
          retR (G := G) n p (matOp (G := G) (Work.ORVonNeumann.blockDiag A B) v) = 0 := by
    intro v
    constructor
    · intro h; rw [h]; simp
    · rintro ⟨h1, h2⟩
      have h := vnBd_incL_retL_add_incR_retR (G := G) (x :=
        matOp (G := G) (Work.ORVonNeumann.blockDiag A B) v)
      rw [h1, h2] at h
      rw [← h, map_zero, map_zero, add_zero]
  simp only [LinearMap.mem_ker]
  change matOp (G := G) (Work.ORVonNeumann.blockDiag A B) w = 0 ↔
    matOp (G := G) A (retL (G := G) m q w) = 0 ∧
      matOp (G := G) B (retR (G := G) m q w) = 0
  rw [key w, vnBd_retL_matOp_blockDiag, vnBd_retR_matOp_blockDiag]

/-! ### The orthogonal projections onto the two halves of the kernel -/

theorem vnBd_starProjection_left {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (j : Fin m) :
    (matOp (G := G) (Work.ORVonNeumann.blockDiag A B)).ker.starProjection
        (hdelta (G := G) (m + q) (finSumFinEquiv (Sum.inl j)))
      = incL (G := G) m q ((matOp (G := G) A).ker.starProjection (hdelta (G := G) m j)) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · rw [vnBd_mem_ker_blockDiag]
    constructor
    · rw [vnBd_retL_incL]
      exact Submodule.starProjection_apply_mem _ _
    · rw [vnBd_retR_incL]
      exact Submodule.zero_mem _
  · rw [Submodule.mem_orthogonal']
    intro z hz
    rw [vnBd_mem_ker_blockDiag] at hz
    rw [← vnBd_hdelta_incL, ← map_sub, ← vnBd_incL_retL_add_incR_retR (G := G) (x := z),
      inner_add_right, vnBd_inner_incL_incL, vnBd_inner_incL_incR]
    have hw : hdelta (G := G) m j
        - (matOp (G := G) A).ker.starProjection (hdelta (G := G) m j)
        ∈ ((matOp (G := G) A).ker)ᗮ := Submodule.sub_starProjection_mem_orthogonal _
    rw [Submodule.mem_orthogonal'] at hw
    rw [hw _ hz.1, add_zero]

theorem vnBd_starProjection_right {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (k : Fin q) :
    (matOp (G := G) (Work.ORVonNeumann.blockDiag A B)).ker.starProjection
        (hdelta (G := G) (m + q) (finSumFinEquiv (Sum.inr k)))
      = incR (G := G) m q ((matOp (G := G) B).ker.starProjection (hdelta (G := G) q k)) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · rw [vnBd_mem_ker_blockDiag]
    constructor
    · rw [vnBd_retL_incR]
      exact Submodule.zero_mem _
    · rw [vnBd_retR_incR]
      exact Submodule.starProjection_apply_mem _ _
  · rw [Submodule.mem_orthogonal']
    intro z hz
    rw [vnBd_mem_ker_blockDiag] at hz
    rw [← vnBd_hdelta_incR, ← map_sub, ← vnBd_incL_retL_add_incR_retR (G := G) (x := z),
      inner_add_right, vnBd_inner_incR_incL, vnBd_inner_incR_incR]
    have hw : hdelta (G := G) q k
        - (matOp (G := G) B).ker.starProjection (hdelta (G := G) q k)
        ∈ ((matOp (G := G) B).ker)ᗮ := Submodule.sub_starProjection_mem_orthogonal _
    rw [Submodule.mem_orthogonal'] at hw
    rw [hw _ hz.2, zero_add]

theorem vnBlockDiagKernel {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(Work.ORVonNeumann.groupVonNeumann G))) (B : Matrix (Fin p) (Fin q) (↥(Work.ORVonNeumann.groupVonNeumann G))) : Work.ORVonNeumann.Rep.hdim ((Work.ORVonNeumann.Rep.matOp (G := G) (Work.ORVonNeumann.blockDiag A B)).ker) = Work.ORVonNeumann.Rep.hdim ((Work.ORVonNeumann.Rep.matOp (G := G) A).ker) + Work.ORVonNeumann.Rep.hdim ((Work.ORVonNeumann.Rep.matOp (G := G) B).ker) := by
  simp only [hdim]
  have hL : (∑ j : Fin m,
        ‖(matOp (G := G) (Work.ORVonNeumann.blockDiag A B)).ker.starProjection
          (hdelta (G := G) (m + q) (finSumFinEquiv (Sum.inl j)))‖ ^ 2)
      = ∑ j : Fin m, ‖(matOp (G := G) A).ker.starProjection (hdelta (G := G) m j)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [vnBd_starProjection_left, vnBd_norm_incL]
  have hR : (∑ k : Fin q,
        ‖(matOp (G := G) (Work.ORVonNeumann.blockDiag A B)).ker.starProjection
          (hdelta (G := G) (m + q) (finSumFinEquiv (Sum.inr k)))‖ ^ 2)
      = ∑ k : Fin q, ‖(matOp (G := G) B).ker.starProjection (hdelta (G := G) q k)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [vnBd_starProjection_right, vnBd_norm_incR]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type, hL, hR]

end Work.ORVonNeumann.Rep
