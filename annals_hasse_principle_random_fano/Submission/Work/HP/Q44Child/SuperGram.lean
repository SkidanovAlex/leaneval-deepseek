import Mathlib
import Submission.Work.HP.Q44Child.SuperDefs

/-!
# The Gram determinant under orthogonal projection

For a real inner product space `E`, a `ℝ`-linearly independent family `b : Fin k → E` and any
family `v : Fin m → E`:
`det (gram (b ++ v)) = det (gram b) * det (gram (π ∘ v))`,
where `π` is the orthogonal projection onto the orthogonal complement of `span (range b)`.
-/

namespace Work.HP.Q44Child

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped RealInnerProductSpace
open Module

/-- The Gram matrix of a family of linear combinations: `gram (M · w) = M * gram w * Mᵀ`. -/
lemma gram_linearCombination {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] (w : ι → E) (M : Matrix ι' ι ℝ) :
    Matrix.gram ℝ (fun i : ι' => ∑ j, M i j • w j) =
      M * Matrix.gram ℝ w * M.transpose := by
  ext i i'
  rw [Matrix.mul_apply]
  simp only [Matrix.gram_apply, Matrix.transpose_apply, Matrix.mul_apply]
  rw [sum_inner]
  conv_lhs => enter [2, j]; rw [inner_sum]
  simp only [real_inner_smul_left, real_inner_smul_right, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The Gram determinant of `b` extended by `v`, in terms of the projections of `v` onto the
orthogonal complement of `span (range b)`. -/
theorem gram_proj_det' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {k m : ℕ} (b : Fin k → E) (v : Fin m → E)
    (hb : LinearIndependent ℝ b) :
    (Matrix.gram ℝ (fun i : Sum (Fin k) (Fin m) => Sum.elim b v i)).det =
      (Matrix.gram ℝ b).det *
        (Matrix.gram ℝ (fun j : Fin m =>
          (Submodule.span ℝ (Set.range b))ᗮ.starProjection (v j))).det := by
  classical
  have hcoord : ∀ j : Fin m, ∃ c : Fin k → ℝ,
      ∑ i, c i • b i = (Submodule.span ℝ (Set.range b)).starProjection (v j) := by
    intro j
    exact (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := b)).mp
      (Submodule.starProjection_apply_mem (Submodule.span ℝ (Set.range b)) (v j))
  choose c hc using hcoord
  have hv : ∀ j : Fin m, v j = (∑ i, c j i • b i) +
      (Submodule.span ℝ (Set.range b))ᗮ.starProjection (v j) := by
    intro j
    rw [hc j]
    exact (Submodule.starProjection_add_starProjection_orthogonal (v j)).symm
  let w : Sum (Fin k) (Fin m) → E :=
    Sum.elim b (fun j => (Submodule.span ℝ (Set.range b))ᗮ.starProjection (v j))
  have hw1 : ∀ a : Fin k, w (Sum.inl a) = b a := fun a => rfl
  have hw2 : ∀ j : Fin m, w (Sum.inr j) =
      (Submodule.span ℝ (Set.range b))ᗮ.starProjection (v j) := fun j => rfl
  let M : Matrix (Sum (Fin k) (Fin m)) (Sum (Fin k) (Fin m)) ℝ :=
    Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 (Matrix.of fun j a => c j a) 1
  have hM : M.det = 1 := by
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one, mul_one]
  have hrow1 : ∀ (i a : Fin k), M (Sum.inl i) (Sum.inl a) = (if i = a then 1 else 0 : ℝ) := by
    intro i a
    simp [M, Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
  have hrow2 : ∀ (i : Fin k) (jj : Fin m), M (Sum.inl i) (Sum.inr jj) = 0 := by
    intro i jj
    simp [M, Matrix.fromBlocks_apply₁₂]
  have hrow3 : ∀ (j : Fin m) (a : Fin k), M (Sum.inr j) (Sum.inl a) = c j a := by
    intro j a
    simp [M, Matrix.fromBlocks_apply₂₁]
  have hrow4 : ∀ (j jj : Fin m), M (Sum.inr j) (Sum.inr jj) = (if j = jj then 1 else 0 : ℝ) := by
    intro j jj
    simp [M, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
  have hfam : (fun i : Sum (Fin k) (Fin m) => Sum.elim b v i) =
      fun i => ∑ j, M i j • w j := by
    funext i
    rw [Fintype.sum_sum_type]
    rcases i with i | j
    · have h₁ : (∑ a : Fin k, M (Sum.inl i) (Sum.inl a) • w (Sum.inl a)) = b i := by
        rw [Finset.sum_eq_single i
          (fun a _ ha => by rw [hrow1 i a, if_neg (Ne.symm ha), zero_smul])
          (fun h => absurd (Finset.mem_univ i) h)]
        rw [hrow1 i i, if_pos rfl, one_smul, hw1]
      have h₂ : (∑ jj : Fin m, M (Sum.inl i) (Sum.inr jj) • w (Sum.inr jj)) = 0 := by
        refine Finset.sum_eq_zero fun jj _ => by rw [hrow2 i jj, zero_smul]
      rw [h₁, h₂, add_zero]
      rfl
    · have h₁ : (∑ a : Fin k, M (Sum.inr j) (Sum.inl a) • w (Sum.inl a)) =
          ∑ a, c j a • b a := by
        refine Finset.sum_congr rfl fun a _ => by rw [hrow3 j a, hw1]
      have h₂ : (∑ jj : Fin m, M (Sum.inr j) (Sum.inr jj) • w (Sum.inr jj)) =
          (Submodule.span ℝ (Set.range b))ᗮ.starProjection (v j) := by
        rw [Finset.sum_eq_single j
          (fun jj _ hj => by rw [hrow4 j jj, if_neg (Ne.symm hj), zero_smul])
          (fun h => absurd (Finset.mem_univ j) h)]
        rw [hrow4 j j, if_pos rfl, one_smul, hw2]
      rw [h₁, h₂]
      exact hv j
  have hoff1 : ∀ (i : Fin k) (j : Fin m),
      ⟪b i, (Submodule.span ℝ (Set.range b))ᗮ.starProjection (v j)⟫ = 0 := fun i j =>
    (Submodule.mem_orthogonal (Submodule.span ℝ (Set.range b)) _).mp
      (Submodule.starProjection_apply_mem _ (v j)) (b i) (Submodule.subset_span ⟨i, rfl⟩)
  have hoff2 : ∀ (i : Fin m) (j : Fin k),
      ⟪(Submodule.span ℝ (Set.range b))ᗮ.starProjection (v i), b j⟫ = 0 := fun i j => by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal (Submodule.span ℝ (Set.range b)) _).mp
      (Submodule.starProjection_apply_mem _ (v i)) (b j) (Submodule.subset_span ⟨j, rfl⟩)
  have hblock : Matrix.gram ℝ w =
      Matrix.fromBlocks (Matrix.gram ℝ b) 0 0
        (Matrix.gram ℝ (fun j : Fin m =>
          (Submodule.span ℝ (Set.range b))ᗮ.starProjection (v j))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.gram_apply, Matrix.fromBlocks_apply₁₁, hw1]
    · simp only [Matrix.gram_apply, Matrix.fromBlocks_apply₁₂, hw1, hw2, hoff1 i j,
        Matrix.zero_apply]
    · simp only [Matrix.gram_apply, Matrix.fromBlocks_apply₂₁, hw1, hw2, hoff2 i j,
        Matrix.zero_apply]
    · simp only [Matrix.gram_apply, Matrix.fromBlocks_apply₂₂, hw2]
  rw [show (fun i : Sum (Fin k) (Fin m) => Sum.elim b v i) = _ from hfam,
    gram_linearCombination _ M, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hM,
    hblock, Matrix.det_fromBlocks_zero₁₂]
  ring

end

end Work.HP.Q44Child
