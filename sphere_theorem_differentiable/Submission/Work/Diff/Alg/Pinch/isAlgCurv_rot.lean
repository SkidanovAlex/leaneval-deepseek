import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `rot A` preserves algebraic curvature tensors (for *any* matrix `A`)

`Submission.Diff.Alg.rot A R i j k l = ∑ a b c d, A i a * A j b * A k c * A l d * R a b c d`
is the action of a change of frame `A` on a curvature array.  The three defining conditions of an
algebraic curvature tensor (`Submission.Diff.Alg.IsAlgCurv`)

* antisymmetry in the first pair, `R j i k l = - R i j k l`,
* pair symmetry, `R k l i j = R i j k l`,
* the first Bianchi identity, `R i j k l + R j k i l + R k i j l = 0`,

are *linear* conditions on `R` in which each index is contracted against the corresponding column
of `A`.  Consequently they are preserved by `rot A` for an arbitrary matrix `A`; **no
orthogonality of `A` is used** (this is the point of the lemma: e.g. the `O(n)`-change-of-frame
machinery never has to worry about this part).

## Route

Each condition is checked indexwise.  After unfolding `rot` the three claims become statements
about fourfold sums `∑ a, ∑ b, ∑ c, ∑ d`, whose summands are reindexed by a permutation of the
index tuple:

* antisymmetry: swap the first two summation variables (`sum4_swap12`, i.e. `Finset.sum_comm`),
  then use `R a b c d = - R b a c d`;
* pair symmetry: reindex by `(a,b,c,d) ↦ (c,d,a,b)` (`sum4_pairs`), then use
  `R c d a b = R a b c d`;
* Bianchi: reindex the two cyclically shifted terms by `(a,b,c,d) ↦ (b,c,a,d)` (`sum4_cyc`) and
  `(a,b,c,d) ↦ (c,a,b,d)` (`sum4_cyc'`), merge the three sums (`Finset.sum_add_distrib`) and use
  `R a b c d + R b c a d + R c a b d = 0`.

The reindexings are realised as permutations of the index set `Fin n × Fin n × Fin n × Fin n`
handled by `Equiv.sum_comp`, exactly as in `Work.Diff.GE.rmFrame_eq_rot`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Reindexing lemmas for fourfold sums -/

/-- A fourfold nested sum equals the single sum over the fourfold product of its indices. -/
private lemma split4 (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2)
      = ∑ a, ∑ b, ∑ c, ∑ d, f a b c d := by
  simp only [Fintype.sum_prod_type]

/-- The `(a,b,c,d) ↦ (c,d,a,b)`-reindexing as a single sum over the fourfold product. -/
private lemma split4_pairs (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.2.1 x.2.2.2 x.1 x.2.1)
      = ∑ a, ∑ b, ∑ c, ∑ d, f c d a b := by
  simp only [Fintype.sum_prod_type]

/-- The `(a,b,c,d) ↦ (b,c,a,d)`-reindexing as a single sum over the fourfold product. -/
private lemma split4_cyc (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.1 x.2.2.1 x.1 x.2.2.2)
      = ∑ a, ∑ b, ∑ c, ∑ d, f b c a d := by
  simp only [Fintype.sum_prod_type]

/-- The `(a,b,c,d) ↦ (c,a,b,d)`-reindexing as a single sum over the fourfold product. -/
private lemma split4_cyc' (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.2.1 x.1 x.2.1 x.2.2.2)
      = ∑ a, ∑ b, ∑ c, ∑ d, f c a b d := by
  simp only [Fintype.sum_prod_type]

/-- The permutation `(a,b,c,d) ↦ (c,d,a,b)` of a fourfold index. -/
private def pPairs4 (n : ℕ) : (Fin n × Fin n × Fin n × Fin n) ≃ (Fin n × Fin n × Fin n × Fin n) where
  toFun x := (x.2.2.1, (x.2.2.2, (x.1, x.2.1)))
  invFun x := (x.2.2.1, (x.2.2.2, (x.1, x.2.1)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl

/-- The permutation `(a,b,c,d) ↦ (b,c,a,d)` of a fourfold index. -/
private def pCyc4 (n : ℕ) : (Fin n × Fin n × Fin n × Fin n) ≃ (Fin n × Fin n × Fin n × Fin n) where
  toFun x := (x.2.1, (x.2.2.1, (x.1, x.2.2.2)))
  invFun x := (x.2.2.1, (x.1, (x.2.1, x.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl

/-- The permutation `(a,b,c,d) ↦ (c,a,b,d)` of a fourfold index. -/
private def pCyc4' (n : ℕ) : (Fin n × Fin n × Fin n × Fin n) ≃ (Fin n × Fin n × Fin n × Fin n) where
  toFun x := (x.2.2.1, (x.1, (x.2.1, x.2.2.2)))
  invFun x := (x.2.1, (x.2.2.1, (x.1, x.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl

/-- Reindex a fourfold sum by the permutation `(a,b,c,d) ↦ (c,d,a,b)`. -/
private lemma sum4_pairs (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ b, ∑ c, ∑ d, f c d a b := by
  have hM : (∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.2.1 x.2.2.2 x.1 x.2.1)
      = ∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    simpa only [pPairs4, Equiv.coe_fn_mk] using
      (Equiv.sum_comp (pPairs4 n)
        (fun x : Fin n × Fin n × Fin n × Fin n => f x.1 x.2.1 x.2.2.1 x.2.2.2))
  exact (split4 f).symm.trans (hM.symm.trans (split4_pairs f))

/-- Reindex a fourfold sum by the permutation `(a,b,c,d) ↦ (b,c,a,d)`. -/
private lemma sum4_cyc (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ b, ∑ c, ∑ d, f b c a d := by
  have hM : (∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.1 x.2.2.1 x.1 x.2.2.2)
      = ∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    simpa only [pCyc4, Equiv.coe_fn_mk] using
      (Equiv.sum_comp (pCyc4 n)
        (fun x : Fin n × Fin n × Fin n × Fin n => f x.1 x.2.1 x.2.2.1 x.2.2.2))
  exact (split4 f).symm.trans (hM.symm.trans (split4_cyc f))

/-- Reindex a fourfold sum by the permutation `(a,b,c,d) ↦ (c,a,b,d)`. -/
private lemma sum4_cyc' (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ b, ∑ c, ∑ d, f c a b d := by
  have hM : (∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.2.1 x.1 x.2.1 x.2.2.2)
      = ∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    simpa only [pCyc4', Equiv.coe_fn_mk] using
      (Equiv.sum_comp (pCyc4' n)
        (fun x : Fin n × Fin n × Fin n × Fin n => f x.1 x.2.1 x.2.2.1 x.2.2.2))
  exact (split4 f).symm.trans (hM.symm.trans (split4_cyc' f))

/-- Swapping the first two index sums of a fourfold sum. -/
private lemma sum4_swap12 (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ a, ∑ c, ∑ d, f a b c d :=
  Finset.sum_comm

/-! ## The theorem -/

theorem isAlgCurv_rot (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) {R : Submission.Diff.Alg.Curv4 n}
    (hR : Submission.Diff.Alg.IsAlgCurv R) :
    Submission.Diff.Alg.IsAlgCurv (Submission.Diff.Alg.rot A R) := by
  obtain ⟨h1, h2, h3⟩ := hR
  refine ⟨?_, ?_, ?_⟩
  · -- antisymmetry in the first pair
    intro i j k l
    simp only [rot]
    have key : (∑ a, ∑ b, ∑ c, ∑ d, A j a * A i b * A k c * A l d * R a b c d)
        = ∑ a, ∑ b, ∑ c, ∑ d, -(A i a * A j b * A k c * A l d * R a b c d) := by
      rw [sum4_swap12 (fun a b c d => A j a * A i b * A k c * A l d * R a b c d)]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ =>
        Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun w _ => ?_))))
      rw [h1 y x]; ring
    rw [key]
    simp only [Finset.sum_neg_distrib]
  · -- pair symmetry
    intro i j k l
    simp only [rot]
    rw [sum4_pairs (fun a b c d => A k a * A l b * A i c * A j d * R a b c d)]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ =>
      Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun w _ => ?_))))
    rw [h2 x y z w]; ring
  · -- first Bianchi identity
    intro i j k l
    simp only [rot]
    have hT2 : (∑ a, ∑ b, ∑ c, ∑ d, A j a * A k b * A i c * A l d * R a b c d)
        = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R b c a d := by
      rw [sum4_cyc (fun a b c d => A j a * A k b * A i c * A l d * R a b c d)]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ =>
        Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun w _ => ?_))))
      ring
    have hT3 : (∑ a, ∑ b, ∑ c, ∑ d, A k a * A i b * A j c * A l d * R a b c d)
        = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R c a b d := by
      rw [sum4_cyc' (fun a b c d => A k a * A i b * A j c * A l d * R a b c d)]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ =>
        Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun w _ => ?_))))
      ring
    rw [hT2, hT3]
    have hmerge : (∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R a b c d)
        + (∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R b c a d)
        + (∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R c a b d)
        = ∑ a, ∑ b, ∑ c, ∑ d, (A i a * A j b * A k c * A l d * R a b c d
            + A i a * A j b * A k c * A l d * R b c a d
            + A i a * A j b * A k c * A l d * R c a b d) := by
      simp only [Finset.sum_add_distrib]
    rw [hmerge]
    apply Finset.sum_eq_zero; intro a _
    apply Finset.sum_eq_zero; intro b _
    apply Finset.sum_eq_zero; intro c _
    apply Finset.sum_eq_zero; intro d _
    rw [show A i a * A j b * A k c * A l d * R a b c d
          + A i a * A j b * A k c * A l d * R b c a d
          + A i a * A j b * A k c * A l d * R c a b d
          = (A i a * A j b * A k c * A l d) * (R a b c d + R b c a d + R c a b d) from by ring,
      h3 a b c d, mul_zero]

end Work.Diff.Alg.Pinch
