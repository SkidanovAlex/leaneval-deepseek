import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic

/-!
# `Work.KT.sumMvN` — the block sum `p ⊕ q` up to Murray–von Neumann equivalence

`Mat.MvN` is the Murray–von Neumann relation modelling the class of a projective module, and
`Mat.sum` models the direct sum of bundles.  This file proves that `Mat.MvN` is a congruence for
`Mat.sum`, and that `Mat.sum` is commutative, associative and unital (`Mat.one R 0` being the
empty, hence neutral, matrix).

The strategy is completely explicit.  A block sum is a block matrix reindexed along
`finSumFinEquiv`, so:
* preservation of `Mat.MvN` under `Mat.sum` is the multiplicativity of the rectangular block sum
  `fromBlocksSum` applied to the witnesses;
* commutativity/associativity/unitality reduce to reindexing identities for block matrices, whose
  index equivalences are `finAddFlip`, `sumAssocFinEquiv`, `sumZeroFinEquiv`, `sumZeroLeftFinEquiv`;
* each such identity is a finite case analysis on the block index.
-/

namespace Work.KT

open Matrix

noncomputable section

variable {R : Type} [Ring R]

/-! ## Rectangular block sums -/

/-- Block sum of rectangular matrices: `[[a, 0], [0, b]]`, reindexed to a square `Fin`-type. -/
def fromBlocksSum {n n' m m' : ℕ} (a : Matrix (Fin n) (Fin n') R)
    (b : Matrix (Fin m) (Fin m') R) : Matrix (Fin (n + m)) (Fin (n' + m')) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a 0 0 b)

/-- The second component of a block sum is a rectangular block sum. -/
lemma Mat.sum_snd_eq (p q : Mat R) : (p.sum q).2 = fromBlocksSum p.2 q.2 := rfl

/-- The rectangular block sum is multiplicative. -/
lemma fromBlocksSum_mul {n n' n'' m m' m'' : ℕ}
    (a : Matrix (Fin n) (Fin n') R) (b : Matrix (Fin n') (Fin n'') R)
    (c : Matrix (Fin m) (Fin m') R) (d : Matrix (Fin m') (Fin m'') R) :
    fromBlocksSum a c * fromBlocksSum b d = fromBlocksSum (a * b) (c * d) := by
  unfold fromBlocksSum
  rw [reindexMul, Matrix.fromBlocks_multiply]
  simp

/-! ## Preservation of `Mat.MvN` under the block sum -/

/-- `Mat.MvN` is a congruence for the block sum: the block sum of the witnesses. -/
lemma mvN_sum {p q p' q' : Mat R} (hp : p.MvN p') (hq : q.MvN q') :
    (p.sum q).MvN (p'.sum q') := by
  obtain ⟨n, P⟩ := p
  obtain ⟨m, Q⟩ := q
  obtain ⟨n', P'⟩ := p'
  obtain ⟨m', Q'⟩ := q'
  obtain ⟨a₁, b₁, h₁, h₁'⟩ := hp
  obtain ⟨a₂, b₂, h₂, h₂'⟩ := hq
  change Mat.MvN (⟨n + m, fromBlocksSum P Q⟩ : Mat R) ⟨n' + m', fromBlocksSum P' Q'⟩
  refine ⟨fromBlocksSum a₁ a₂, fromBlocksSum b₁ b₂, ?_, ?_⟩
  · show fromBlocksSum b₁ b₂ * fromBlocksSum a₁ a₂ = fromBlocksSum P Q
    rw [fromBlocksSum_mul, h₁, h₂]
  · show fromBlocksSum a₁ a₂ * fromBlocksSum b₁ b₂ = fromBlocksSum P' Q'
    rw [fromBlocksSum_mul, h₁', h₂']

/-! ## Commutativity of the block sum -/

/-- The inverse of `finAddFlip` on the `Fin.castAdd` part. -/
lemma finAddFlip_symm_castAdd (m n : ℕ) (k : Fin n) :
    (finAddFlip (m := m) (n := n)).symm (Fin.castAdd m k) = Fin.natAdd m k := by
  rw [Equiv.symm_apply_eq]
  exact (finAddFlip_apply_natAdd k m).symm

/-- The inverse of `finAddFlip` on the `Fin.natAdd` part. -/
lemma finAddFlip_symm_natAdd (m n : ℕ) (k : Fin m) :
    (finAddFlip (m := m) (n := n)).symm (Fin.natAdd n k) = Fin.castAdd n k := by
  rw [Equiv.symm_apply_eq]
  exact (finAddFlip_apply_castAdd k n).symm

/-- A block sum is invariant under the flip of the two summands of its index set. -/
lemma reindex_sumComm_sum (p q : Mat R) :
    Matrix.reindex (finAddFlip (m := p.1) (n := q.1)) (finAddFlip (m := p.1) (n := q.1))
      (fromBlocksSum p.2 q.2) = fromBlocksSum q.2 p.2 := by
  ext i j
  obtain ⟨u, rfl⟩ := Equiv.surjective finSumFinEquiv i
  obtain ⟨v, rfl⟩ := Equiv.surjective finSumFinEquiv j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases u with a | a <;> rcases v with b | b <;>
    simp only [fromBlocksSum, Matrix.reindex_apply, Matrix.submatrix_apply,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      finAddFlip_symm_castAdd, finAddFlip_symm_natAdd,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]

/-- The block sum is commutative up to `Mat.MvN`. -/
lemma mvN_sum_comm (p q : Mat R) : Mat.MvN (p.sum q) (q.sum p) := by
  have h := Mat.mvN_reindex (finAddFlip (m := p.1) (n := q.1)) (fromBlocksSum p.2 q.2)
  rw [reindex_sumComm_sum p q] at h
  exact h

/-! ## Associativity of the block sum -/

/-- The index equivalence `Fin ((n+m)+k) ≃ Fin (n+(m+k))` reassociating a nested block sum. -/
def sumAssocFinEquiv (n m k : ℕ) : Fin ((n + m) + k) ≃ Fin (n + (m + k)) :=
  (finSumFinEquiv : Fin (n + m) ⊕ Fin k ≃ Fin ((n + m) + k)).symm.trans
    ((Equiv.sumCongr (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm
        (Equiv.refl (Fin k))).trans
      ((Equiv.sumAssoc (Fin n) (Fin m) (Fin k)).trans
        ((Equiv.sumCongr (Equiv.refl (Fin n))
            (finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m + k))).trans
          (finSumFinEquiv : Fin n ⊕ Fin (m + k) ≃ Fin (n + (m + k))))))

/-- Reindexing a doubly nested block sum along `sumAssocFinEquiv` reassociates it. -/
lemma reindex_sumAssoc_sum (p q r : Mat R) :
    Matrix.reindex (sumAssocFinEquiv p.1 q.1 r.1) (sumAssocFinEquiv p.1 q.1 r.1)
      (fromBlocksSum (fromBlocksSum p.2 q.2) r.2) = fromBlocksSum p.2 (fromBlocksSum q.2 r.2) := by
  ext i j
  obtain ⟨u, rfl⟩ := Equiv.surjective finSumFinEquiv i
  obtain ⟨v, rfl⟩ := Equiv.surjective finSumFinEquiv j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases u with a | b <;> rcases v with c | d
  · simp [sumAssocFinEquiv, fromBlocksSum]
  · obtain ⟨d', rfl⟩ := Equiv.surjective finSumFinEquiv d
    rcases d' with d₁ | d₂ <;> simp [sumAssocFinEquiv, fromBlocksSum]
  · obtain ⟨b', rfl⟩ := Equiv.surjective finSumFinEquiv b
    rcases b' with b₁ | b₂ <;> simp [sumAssocFinEquiv, fromBlocksSum]
  · obtain ⟨b', rfl⟩ := Equiv.surjective finSumFinEquiv b
    rcases b' with b₁ | b₂
    · obtain ⟨d', rfl⟩ := Equiv.surjective finSumFinEquiv d
      rcases d' with d₁ | d₂ <;> simp [sumAssocFinEquiv, fromBlocksSum]
    · obtain ⟨d', rfl⟩ := Equiv.surjective finSumFinEquiv d
      rcases d' with d₁ | d₂ <;> simp [sumAssocFinEquiv, fromBlocksSum]

/-- The block sum is associative up to `Mat.MvN`. -/
lemma mvN_sum_assoc (p q r : Mat R) : Mat.MvN ((p.sum q).sum r) (p.sum (q.sum r)) := by
  have h := Mat.mvN_reindex (sumAssocFinEquiv p.1 q.1 r.1)
    (fromBlocksSum (fromBlocksSum p.2 q.2) r.2)
  rw [reindex_sumAssoc_sum p q r] at h
  exact h

/-! ## The empty matrix as a unit of the block sum -/

/-- `Fin (n + 0) ≃ Fin n` coming from the vanishing of the second summand. -/
def sumZeroFinEquiv (n : ℕ) : Fin (n + 0) ≃ Fin n :=
  (finSumFinEquiv : Fin n ⊕ Fin 0 ≃ Fin (n + 0)).symm.trans (Equiv.sumEmpty (Fin n) (Fin 0))

/-- `Fin (0 + n) ≃ Fin n` coming from the vanishing of the first summand. -/
def sumZeroLeftFinEquiv (n : ℕ) : Fin (0 + n) ≃ Fin n :=
  (finSumFinEquiv : Fin 0 ⊕ Fin n ≃ Fin (0 + n)).symm.trans (Equiv.emptySum (Fin 0) (Fin n))

lemma sumZeroFinEquiv_apply_inl (n : ℕ) (i : Fin n) :
    sumZeroFinEquiv n (finSumFinEquiv (Sum.inl i)) = i := by
  simp [sumZeroFinEquiv]

lemma sumZeroFinEquiv_symm (n : ℕ) (i : Fin n) :
    (sumZeroFinEquiv n).symm i = finSumFinEquiv (Sum.inl i) := by
  rw [Equiv.symm_apply_eq]
  exact (sumZeroFinEquiv_apply_inl n i).symm

lemma sumZeroLeftFinEquiv_apply_inr (n : ℕ) (i : Fin n) :
    sumZeroLeftFinEquiv n (finSumFinEquiv (Sum.inr i)) = i := by
  simp only [sumZeroLeftFinEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.emptySum_apply_inr]

lemma sumZeroLeftFinEquiv_symm (n : ℕ) (i : Fin n) :
    (sumZeroLeftFinEquiv n).symm i = finSumFinEquiv (Sum.inr i) := by
  rw [Equiv.symm_apply_eq]
  exact (sumZeroLeftFinEquiv_apply_inr n i).symm

/-- Adding an empty matrix on the right does not change the block matrix. -/
lemma reindex_sumZero_sum (p : Mat R) :
    Matrix.reindex (sumZeroFinEquiv p.1) (sumZeroFinEquiv p.1)
      (fromBlocksSum p.2 (Mat.one R 0).2) = p.2 := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, sumZeroFinEquiv_symm, sumZeroFinEquiv_symm]
  simp only [fromBlocksSum, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  exact Matrix.fromBlocks_apply₁₁ p.2 0 0 (Mat.one R 0).2 i j

/-- Adding an empty matrix on the left does not change the block matrix. -/
lemma reindex_sumZeroLeft (p : Mat R) :
    Matrix.reindex (sumZeroLeftFinEquiv p.1) (sumZeroLeftFinEquiv p.1)
      (fromBlocksSum (Mat.one R 0).2 p.2) = p.2 := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, sumZeroLeftFinEquiv_symm,
    sumZeroLeftFinEquiv_symm]
  simp only [fromBlocksSum, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  exact Matrix.fromBlocks_apply₂₂ (Mat.one R 0).2 0 0 p.2 i j

/-- `p ⊕ 0 ~ p`. -/
lemma mvN_sum_one_zero (p : Mat R) : Mat.MvN (p.sum (Mat.one R 0)) p := by
  have h := Mat.mvN_reindex (sumZeroFinEquiv p.1) (fromBlocksSum p.2 (Mat.one R 0).2)
  rw [reindex_sumZero_sum p] at h
  exact h

/-- `0 ⊕ p ~ p`. -/
lemma mvN_one_zero_sum (p : Mat R) : Mat.MvN ((Mat.one R 0).sum p) p := by
  have h := Mat.mvN_reindex (sumZeroLeftFinEquiv p.1) (fromBlocksSum (Mat.one R 0).2 p.2)
  rw [reindex_sumZeroLeft p] at h
  exact h

/-! ## The theorem -/

theorem sumMvN :
    (∀ (R : Type) [Ring R] (p q p' q' : Mat R), Mat.MvN p p' → Mat.MvN q q' →
      Mat.MvN (p.sum q) (p'.sum q')) ∧
    (∀ (R : Type) [Ring R] (p q : Mat R), Mat.MvN (p.sum q) (q.sum p)) ∧
    (∀ (R : Type) [Ring R] (p q r : Mat R), Mat.MvN ((p.sum q).sum r) (p.sum (q.sum r))) ∧
    (∀ (R : Type) [Ring R] (p : Mat R), Mat.MvN (p.sum (Mat.one R 0)) p) ∧
    (∀ (R : Type) [Ring R] (p : Mat R), Mat.MvN ((Mat.one R 0).sum p) p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro R _ p q p' q' hp hq
    exact mvN_sum hp hq
  · intro R _ p q
    exact mvN_sum_comm p q
  · intro R _ p q r
    exact mvN_sum_assoc p q r
  · intro R _ p
    exact mvN_sum_one_zero p
  · intro R _ p
    exact mvN_one_zero_sum p

end

end Work.KT
