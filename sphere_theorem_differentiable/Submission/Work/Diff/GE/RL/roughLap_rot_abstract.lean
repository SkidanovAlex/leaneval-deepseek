import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace Work.Diff.GE.RL

/-- Reindexing of a five-fold sum: the outermost summation variable is moved to the
innermost position.  (A `Finset.sum_comm` applied four times.) -/
lemma sum_comm_five {α : Type*} [Fintype α] (f : α → α → α → α → α → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_comm]

/-- The rotation invariance (in the *first two* slots) of the `roughLap` tensor: if `A` is
orthogonal, contracting the first two indices of the `6`-tensor `F` with `Aᵀ` and rotating the
remaining four indices with `A` is the same as taking the trace of `F` in its first two slots and
rotating the remaining four indices with `A`.

This is the abstract index computation behind `roughLap_rot`: the `Aᵀ * A` appearing on the first
two slots is the identity because `A` is orthogonal. -/
theorem roughLap_rot_abstract {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hAO : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) (i j k l : Fin n) :
    (∑ m, ∑ p, ∑ q, ∑ r, ∑ s, ∑ t, ∑ u,
        A m p * A m q * A i r * A j s * A k t * A l u * F p q r s t u)
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * (∑ m, F m m a b c d) := by
  -- Orthogonality gives `Aᵀ * A = 1`, i.e. the columns of `A` are orthonormal: the contraction
  -- `∑ m, A m p * A m q` is the Kronecker delta.
  have hAA : ∀ p q : Fin n, ∑ m, A m p * A m q = if p = q then 1 else 0 := by
    intro p q
    have hAtA : Aᵀ * A = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hAO
    have h := congrFun (congrFun hAtA p) q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    exact h
  -- (1) Factor out the contraction over `m`, `p`, `q` from the remaining four sums.
  have hL : (∑ m, ∑ p, ∑ q, ∑ r, ∑ s, ∑ t, ∑ u,
        A m p * A m q * A i r * A j s * A k t * A l u * F p q r s t u)
      = ∑ m, ∑ p, ∑ q, (A m p * A m q) *
          (∑ r, ∑ s, ∑ t, ∑ u, A i r * A j s * A k t * A l u * F p q r s t u) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Finset.sum_congr rfl fun t _ => ?_
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  -- (2) Perform the contraction using the orthonormality of the columns of `A`.
  have hC : (∑ m, ∑ p, ∑ q, (A m p * A m q) *
          (∑ r, ∑ s, ∑ t, ∑ u, A i r * A j s * A k t * A l u * F p q r s t u))
      = ∑ p, (∑ r, ∑ s, ∑ t, ∑ u, A i r * A j s * A k t * A l u * F p p r s t u) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    simp only [hAA]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  -- (3) Push the trace sum `∑ m, F m m a b c d` inside the four rotations and reindex.
  have hR : (∑ p, (∑ r, ∑ s, ∑ t, ∑ u, A i r * A j s * A k t * A l u * F p p r s t u))
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * (∑ m, F m m a b c d) := by
    simp only [Finset.mul_sum]
    conv_lhs =>
      rw [sum_comm_five (fun p r s t u => A i r * A j s * A k t * A l u * F p p r s t u)]
  exact hL.trans (hC.trans hR)

end Work.Diff.GE.RL
