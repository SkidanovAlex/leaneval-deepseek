import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.sum_mvN_congr
import Submission.Work.KT.sum_mvN_assoc

/-!
# `Work.KT.rel_cancel` — cancellation of a common block in stable Murray–von Neumann calculus

Two facts about `Mat.MvN` (`Submission/Work/KT/Defs.lean`) that let one cancel a common summand
after stabilising by a free block.

* `mvN_sum_compl` (first conjunct of `rel_cancel`): for an idempotent square matrix `p` of size `n`
  the "complementary" block matrix `[[p, 0], [0, 1 - p]]` is Murray–von Neumann equivalent to the
  identity `1ₙ`.  In module language `im p ⊕ im (1 - p) ≅ Rⁿ`, which is the tautology that an
  idempotent splits the free module into its image and kernel.

* second conjunct: if `p ⊕ c ⊕ 1ₖ ∼ q ⊕ c ⊕ 1ₖ` then `p ⊕ 1ₘ ∼ q ⊕ 1ₘ`.  The point is that
  stabilising by the single block `e = c ⊕ 1ₖ` and *then* adding the complement `1 - e` turns `e`
  into a free block, so that cancellation is legitimate in this restricted stable sense.
-/

namespace Work.KT

open Matrix

noncomputable section

/-- For an idempotent `e : Matrix (Fin n) (Fin n) R`, the block matrix `[[e,0],[0,1-e]]`
(after reindexing by `finSumFinEquiv`) is Murray–von Neumann equivalent to `1ₙ`.

Witnesses: `a = [e | 1-e]` (a row of blocks) and `b = [[e],[1-e]]` (a column of blocks).  Then
`b a = [[e², e(1-e)],[(1-e)e, (1-e)²]] = [[e,0],[0,1-e]]` and `a b = e² + (1-e)² = e + (1-e) = 1`. -/
theorem mvN_sum_compl_mat (R : Type) [Ring R] (n : ℕ) (e : Matrix (Fin n) (Fin n) R)
    (he : e * e = e) :
    Mat.MvN ⟨n + n, Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks e 0 0 (1 - e))⟩
      ⟨n, 1⟩ := by
  have hp0 : e * (1 - e) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, he, sub_self]
  have h0p : (1 - e) * e = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, he, sub_self]
  have h11 : (1 - e) * (1 - e) = 1 - e := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, he, sub_self, sub_zero]
  have hreid : ∀ {m k : Type} [Fintype m] [Fintype k] (X : Matrix m k R),
      Matrix.reindex (Equiv.refl m) (Equiv.refl k) X = X := by
    intro m k _ _ X; simp [Matrix.reindex_apply]
  refine ⟨Matrix.reindex (Equiv.refl (Fin n)) finSumFinEquiv (Matrix.fromCols e (1 - e)),
    Matrix.reindex finSumFinEquiv (Equiv.refl (Fin n)) (Matrix.fromRows e (1 - e)), ?_, ?_⟩
  · rw [reindexMul, Matrix.fromRows_mul_fromCols, he, hp0, h0p, h11]
  · rw [reindexMul, Matrix.fromCols_mul_fromRows, he, h11, hreid]
    abel

/-- **First conjunct of `rel_cancel`**: for an idempotent `p`, the complementary block sum
`p ⊕ (1 - p)` is stably the identity `1_{p.1}`. -/
theorem mvN_sum_compl (R : Type) [Ring R] (p : Mat R) (hp : p.IsIdem) :
    Mat.MvN (p.sum ⟨p.1, 1 - p.2⟩) (Mat.one R p.1) :=
  mvN_sum_compl_mat R p.1 p.2 hp

/-- The complementary matrix `1 - p` is idempotent when `p` is. -/
theorem Mat.isIdem_one_sub {R : Type} [Ring R] {p : Mat R} (hp : p.IsIdem) :
    Mat.IsIdem ⟨p.1, 1 - p.2⟩ := by
  show (1 - p.2) * (1 - p.2) = 1 - p.2
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hp, sub_self, sub_zero]

/-- The identity matrix is idempotent. -/
theorem Mat.one_isIdem (R : Type) [Ring R] (n : ℕ) : (Mat.one R n).IsIdem := by
  rw [Mat.IsIdem, Mat.one]; simp

/-- **Cancellation of a common idempotent block up to free stabilisation.**  If `p ⊕ e ∼ q ⊕ e`
with `e` idempotent, then `p ⊕ 1_{e.1} ∼ q ⊕ 1_{e.1}`.

Indeed, adding the complement `e' = 1 - e` to both sides and using `mvN_sum_compl` on `e` and on
`p ⊕ e` (resp. `q ⊕ e`) makes the common block free. -/
theorem mvN_cancel_sum_one (R : Type) [Ring R] (p q e : Mat R) (hp : p.IsIdem) (hq : q.IsIdem)
    (he : e.IsIdem) (hk : Mat.MvN (p.sum e) (q.sum e)) :
    Mat.MvN (p.sum (Mat.one R e.1)) (q.sum (Mat.one R e.1)) := by
  have he' : Mat.IsIdem (⟨e.1, 1 - e.2⟩ : Mat R) := Mat.isIdem_one_sub he
  -- `e ⊕ (1 - e) ∼ 1`
  have h2 : Mat.MvN (e.sum ⟨e.1, 1 - e.2⟩) (Mat.one R e.1) := mvN_sum_compl R e he
  -- reassociate `(p ⊕ e) ⊕ (1 - e) ∼ p ⊕ (e ⊕ (1 - e)) ∼ p ⊕ 1`
  have h1 : Mat.MvN ((p.sum e).sum ⟨e.1, 1 - e.2⟩) (p.sum (e.sum ⟨e.1, 1 - e.2⟩)) :=
    sum_mvN_assoc R p e ⟨e.1, 1 - e.2⟩
  have h3 : Mat.MvN (p.sum (e.sum ⟨e.1, 1 - e.2⟩)) (p.sum (Mat.one R e.1)) :=
    sum_mvN_congr R p p (e.sum ⟨e.1, 1 - e.2⟩) (Mat.one R e.1) (Mat.mvN_refl hp) h2
  have h4 : Mat.MvN ((p.sum e).sum ⟨e.1, 1 - e.2⟩) (p.sum (Mat.one R e.1)) :=
    Mat.mvN_trans (Mat.sum_idem (Mat.sum_idem hp he) he')
      (Mat.sum_idem hp (Mat.sum_idem he he')) (Mat.sum_idem hp (Mat.one_isIdem R e.1)) h1 h3
  have h1q : Mat.MvN ((q.sum e).sum ⟨e.1, 1 - e.2⟩) (q.sum (e.sum ⟨e.1, 1 - e.2⟩)) :=
    sum_mvN_assoc R q e ⟨e.1, 1 - e.2⟩
  have h3q : Mat.MvN (q.sum (e.sum ⟨e.1, 1 - e.2⟩)) (q.sum (Mat.one R e.1)) :=
    sum_mvN_congr R q q (e.sum ⟨e.1, 1 - e.2⟩) (Mat.one R e.1) (Mat.mvN_refl hq) h2
  have h4q : Mat.MvN ((q.sum e).sum ⟨e.1, 1 - e.2⟩) (q.sum (Mat.one R e.1)) :=
    Mat.mvN_trans (Mat.sum_idem (Mat.sum_idem hq he) he')
      (Mat.sum_idem hq (Mat.sum_idem he he')) (Mat.sum_idem hq (Mat.one_isIdem R e.1)) h1q h3q
  have h5 : Mat.MvN ((p.sum e).sum ⟨e.1, 1 - e.2⟩) ((q.sum e).sum ⟨e.1, 1 - e.2⟩) :=
    sum_mvN_congr R (p.sum e) (q.sum e) ⟨e.1, 1 - e.2⟩ ⟨e.1, 1 - e.2⟩ hk (Mat.mvN_refl he')
  have t : Mat.MvN (p.sum (Mat.one R e.1)) ((q.sum e).sum ⟨e.1, 1 - e.2⟩) :=
    Mat.mvN_trans (Mat.sum_idem hp (Mat.one_isIdem R e.1))
      (Mat.sum_idem (Mat.sum_idem hp he) he') (Mat.sum_idem (Mat.sum_idem hq he) he')
      (Mat.mvN_symm h4) h5
  exact Mat.mvN_trans (Mat.sum_idem hp (Mat.one_isIdem R e.1))
    (Mat.sum_idem (Mat.sum_idem hq he) he') (Mat.sum_idem hq (Mat.one_isIdem R e.1)) t h4q

theorem rel_cancel :
    (∀ (R : Type) [Ring R] (p : Mat R), p.IsIdem →
      Mat.MvN (p.sum ⟨p.1, 1 - p.2⟩) (Mat.one R p.1)) ∧
    (∀ (R : Type) [Ring R] (p q c : Mat R) (hp : p.IsIdem) (hq : q.IsIdem) (hc : c.IsIdem),
      (∃ k : ℕ, Mat.MvN ((p.sum c).sum (Mat.one R k)) ((q.sum c).sum (Mat.one R k))) →
      ∃ k : ℕ, Mat.MvN (p.sum (Mat.one R k)) (q.sum (Mat.one R k))) := by
  constructor
  · intro R _ p hp
    exact mvN_sum_compl R p hp
  · intro R _ p q c hp hq hc h
    obtain ⟨k, hk0⟩ := h
    -- let `e = c ⊕ 1ₖ`; the hypothesis is `p ⊕ c ⊕ 1ₖ ∼ q ⊕ c ⊕ 1ₖ`, i.e. `p ⊕ e ∼ q ⊕ e` up to
    -- reassociation of the block sums.
    let e : Mat R := c.sum (Mat.one R k)
    have he : e.IsIdem := Mat.sum_idem hc (Mat.one_isIdem R k)
    have hX : Mat.MvN ((p.sum c).sum (Mat.one R k)) (p.sum e) := sum_mvN_assoc R p c (Mat.one R k)
    have hY : Mat.MvN ((q.sum c).sum (Mat.one R k)) (q.sum e) := sum_mvN_assoc R q c (Mat.one R k)
    have hpe : Mat.MvN (p.sum e) (q.sum e) := by
      have t1 : Mat.MvN (p.sum e) ((q.sum c).sum (Mat.one R k)) :=
        Mat.mvN_trans (Mat.sum_idem hp he)
          (Mat.sum_idem (Mat.sum_idem hp hc) (Mat.one_isIdem R k))
          (Mat.sum_idem (Mat.sum_idem hq hc) (Mat.one_isIdem R k)) (Mat.mvN_symm hX) hk0
      exact Mat.mvN_trans (Mat.sum_idem hp he)
        (Mat.sum_idem (Mat.sum_idem hq hc) (Mat.one_isIdem R k)) (Mat.sum_idem hq he) t1 hY
    exact ⟨e.1, mvN_cancel_sum_one R p q e hp hq he hpe⟩

end

end Work.KT
