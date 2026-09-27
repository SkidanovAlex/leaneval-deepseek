import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.sumMvN
import Submission.Work.KT.mvN_sum_middle

/-!
# `Work.KT.stabMvN` — stability of the Murray–von Neumann relation under block sums

`Mat.MvN p q` is Murray–von Neumann equivalence of the bundles modelled by `p` and `q`.  The
theorem proved here is that the relation

  `p ~ q  :⟺  Mat.MvN (p ⊕ 1_k) (q ⊕ 1_k)`

(equivalence after stabilising by identity blocks) is transitive, and additive in the two
variables simultaneously.  Both statements are consequences of the fact that `Mat.sum` is, up to
`Mat.MvN`, a commutative monoid with the identities `Mat.one R k` as a graded family
(`1_k ⊕ 1_l = 1_{k+l}`), together with the middle-four exchange for the block sum.

* `Mat.one_sum_one` — `1_k ⊕ 1_l = 1_{k+l}`.
* `mvN_sum_one_shift` — `(p ⊕ 1_k) ⊕ 1_l ~ p ⊕ 1_{k+l}`.
* `mvN_sum_one_eq` — `(p ⊕ q) ⊕ 1_{k+l} ~ (p ⊕ 1_k) ⊕ (q ⊕ 1_l)`.
* `mvN_sum_shift_mono` — more stabilisation preserves `Mat.MvN`.
-/

namespace Work.KT

open Matrix

noncomputable section

/-- The identity matrices add up: `1_k ⊕ 1_l = 1_{k+l}`. -/
lemma Mat.one_sum_one {R : Type} [Ring R] (k l : ℕ) :
    (Mat.one R k).sum (Mat.one R l) = Mat.one R (k + l) := by
  show (⟨k + l, Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) R) 0 0
        (1 : Matrix (Fin l) (Fin l) R))⟩ : Mat R) = ⟨k + l, 1⟩
  congr 1
  rw [Matrix.fromBlocks_one, Matrix.reindex_apply]
  exact Matrix.submatrix_one_equiv finSumFinEquiv.symm

/-- The identity matrix of any size is idempotent. -/
lemma Mat.one_isIdem {R : Type} [Ring R] (n : ℕ) : (Mat.one R n).IsIdem := by
  unfold Mat.IsIdem Mat.one
  simp

/-- Stabilising an idempotent by identity blocks: `(p ⊕ 1_k) ⊕ 1_l ~ p ⊕ 1_{k+l}`. -/
lemma mvN_sum_one_shift {R : Type} [Ring R] (p : Mat R) (k l : ℕ) :
    Mat.MvN ((p.sum (Mat.one R k)).sum (Mat.one R l)) (p.sum (Mat.one R (k + l))) := by
  have h := mvN_sum_assoc p (Mat.one R k) (Mat.one R l)
  rw [Mat.one_sum_one (R := R) k l] at h
  exact h

/-- Splitting an identity block: `(p ⊕ q) ⊕ 1_{k+l} ~ (p ⊕ 1_k) ⊕ (q ⊕ 1_l)`. -/
lemma mvN_sum_one_eq {R : Type} [Ring R] (p q : Mat R) (hp : p.IsIdem) (hq : q.IsIdem)
    (k l : ℕ) :
    Mat.MvN ((p.sum q).sum (Mat.one R (k + l)))
      ((p.sum (Mat.one R k)).sum (q.sum (Mat.one R l))) := by
  rw [← Mat.one_sum_one (R := R) k l]
  exact mvN_sum_middle R p q (Mat.one R k) (Mat.one R l) hp hq
    (Mat.one_isIdem (R := R) k) (Mat.one_isIdem (R := R) l)

/-- Murray–von Neumann equivalence after stabilisation is stable under further stabilisation. -/
lemma mvN_sum_shift_mono {R : Type} [Ring R] {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem)
    (k l : ℕ) (h : Mat.MvN (p.sum (Mat.one R k)) (q.sum (Mat.one R k))) :
    Mat.MvN (p.sum (Mat.one R (k + l))) (q.sum (Mat.one R (k + l))) := by
  have h1 : Mat.MvN (p.sum (Mat.one R (k + l))) ((p.sum (Mat.one R k)).sum (Mat.one R l)) :=
    Mat.mvN_symm (mvN_sum_one_shift p k l)
  have h2 : Mat.MvN ((p.sum (Mat.one R k)).sum (Mat.one R l))
      ((q.sum (Mat.one R k)).sum (Mat.one R l)) :=
    mvN_sum h (Mat.mvN_refl (Mat.one_isIdem (R := R) l))
  have h3 : Mat.MvN ((q.sum (Mat.one R k)).sum (Mat.one R l)) (q.sum (Mat.one R (k + l))) :=
    mvN_sum_one_shift q k l
  have e1 : ((p.sum (Mat.one R k)).sum (Mat.one R l)).IsIdem :=
    Mat.sum_idem (Mat.sum_idem hp (Mat.one_isIdem (R := R) k)) (Mat.one_isIdem (R := R) l)
  have e2 : ((q.sum (Mat.one R k)).sum (Mat.one R l)).IsIdem :=
    Mat.sum_idem (Mat.sum_idem hq (Mat.one_isIdem (R := R) k)) (Mat.one_isIdem (R := R) l)
  exact Mat.mvN_trans (Mat.sum_idem hp (Mat.one_isIdem (R := R) (k + l))) e1
    (Mat.sum_idem hq (Mat.one_isIdem (R := R) (k + l))) h1
    (Mat.mvN_trans e1 e2 (Mat.sum_idem hq (Mat.one_isIdem (R := R) (k + l))) h2 h3)

theorem stabMvN :
    (∀ (R : Type) [Ring R] (a b c : Mat R), a.IsIdem → b.IsIdem → c.IsIdem → ∀ k l : ℕ,
      Mat.MvN (a.sum (Mat.one R k)) (b.sum (Mat.one R k)) →
      Mat.MvN (b.sum (Mat.one R l)) (c.sum (Mat.one R l)) →
      Mat.MvN (a.sum (Mat.one R (k + l))) (c.sum (Mat.one R (k + l)))) ∧
    (∀ (R : Type) [Ring R] (a b c d : Mat R), a.IsIdem → b.IsIdem → c.IsIdem → d.IsIdem →
      ∀ k l : ℕ,
      Mat.MvN (a.sum (Mat.one R k)) (b.sum (Mat.one R k)) →
      Mat.MvN (c.sum (Mat.one R l)) (d.sum (Mat.one R l)) →
      Mat.MvN ((a.sum c).sum (Mat.one R (k + l))) ((b.sum d).sum (Mat.one R (k + l)))) := by
  refine ⟨?_, ?_⟩
  · intro R _ a b c ha hb hc k l hab hbc
    have h1 := mvN_sum_shift_mono ha hb k l hab
    have h2 := mvN_sum_shift_mono hb hc l k hbc
    rw [Nat.add_comm l k] at h2
    exact Mat.mvN_trans (Mat.sum_idem ha (Mat.one_isIdem (R := R) (k + l)))
      (Mat.sum_idem hb (Mat.one_isIdem (R := R) (k + l)))
      (Mat.sum_idem hc (Mat.one_isIdem (R := R) (k + l))) h1 h2
  · intro R _ a b c d ha hb hc hd k l hab hcd
    have h1 : Mat.MvN ((a.sum c).sum (Mat.one R (k + l)))
        ((a.sum (Mat.one R k)).sum (c.sum (Mat.one R l))) :=
      mvN_sum_one_eq a c ha hc k l
    have h2 : Mat.MvN ((a.sum (Mat.one R k)).sum (c.sum (Mat.one R l)))
        ((b.sum (Mat.one R k)).sum (d.sum (Mat.one R l))) := mvN_sum hab hcd
    have h3 : Mat.MvN ((b.sum (Mat.one R k)).sum (d.sum (Mat.one R l)))
        ((b.sum d).sum (Mat.one R (k + l))) :=
      Mat.mvN_symm (mvN_sum_one_eq b d hb hd k l)
    have iM : ((a.sum (Mat.one R k)).sum (c.sum (Mat.one R l))).IsIdem :=
      Mat.sum_idem (Mat.sum_idem ha (Mat.one_isIdem (R := R) k))
        (Mat.sum_idem hc (Mat.one_isIdem (R := R) l))
    have iM' : ((b.sum (Mat.one R k)).sum (d.sum (Mat.one R l))).IsIdem :=
      Mat.sum_idem (Mat.sum_idem hb (Mat.one_isIdem (R := R) k))
        (Mat.sum_idem hd (Mat.one_isIdem (R := R) l))
    exact Mat.mvN_trans (Mat.sum_idem (Mat.sum_idem ha hc) (Mat.one_isIdem (R := R) (k + l)))
      iM (Mat.sum_idem (Mat.sum_idem hb hd) (Mat.one_isIdem (R := R) (k + l)))
      h1 (Mat.mvN_trans iM iM'
        (Mat.sum_idem (Mat.sum_idem hb hd) (Mat.one_isIdem (R := R) (k + l))) h2 h3)

end

end Work.KT
