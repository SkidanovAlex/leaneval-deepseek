import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs

namespace Work.ORHughesFree.NaturalExtension

set_option linter.style.haveILetI false

/-- The `(q, p)`-entry of `lacZB d n` vanishes unless `q` lies in the top block and `p` is the
inner index of `q`; consequently the product `lacWiB d n * lacZB d n` selects, in each column `q`,
the unique index with `divNat = 0` and `modNat = q`. -/
theorem lacWiB_mul_ZB {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (d n : ℕ)
    (r : Fin (d * n)) (q : Fin n) :
    (lacWiB (R := R) d n * lacZB (R := R) d n) r q
      = if r.modNat = q then -(skewLaurentT ^ ((r.divNat : ℕ) + 1)) else 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Fin.elim0 q
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    haveI : IsEmpty (Fin (0 * n)) := by rw [Nat.zero_mul]; exact Fin.isEmpty
    exact isEmptyElim r
  haveI : NeZero d := ⟨Nat.pos_iff_ne_zero.mp hd⟩
  rw [Matrix.mul_apply]
  simp only [lacWiB, lacZB, lacTmat, Matrix.diagonal_apply]
  -- The unique index carrying the `t` of the `0`-block.
  set j0 : Fin (d * n) := finProdFinEquiv ((0 : Fin d), q) with hj0def
  have hj0d : j0.divNat = (0 : Fin d) := by
    rw [hj0def]; exact Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_fst _ _
  have hj0m : j0.modNat = q := by
    rw [hj0def]; exact Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_snd _ _
  -- Every index is determined by its `divNat`/`modNat` pair.
  have hb_eq : ∀ b : Fin (d * n), b = finProdFinEquiv (b.divNat, b.modNat) := by
    intro b
    have h := Equiv.apply_symm_apply finProdFinEquiv b
    rw [finProdFinEquiv_symm_apply] at h
    exact h.symm
  have hb_eq_j0 : ∀ b : Fin (d * n), (b.divNat : ℕ) = 0 → b.modNat = q → b = j0 := by
    intro b hb0 hbm
    rw [hb_eq b]
    have hbd : b.divNat = (0 : Fin d) := Fin.ext (by simpa using hb0)
    rw [hbd, hbm, hj0def]
  rw [Finset.sum_eq_single j0]
  · rw [hj0d, hj0m]
    by_cases h : r.modNat = q <;> simp [h, neg_mul, pow_succ]
  · intro b _ hne
    by_cases hb0 : (b.divNat : ℕ) = 0
    · rw [if_pos hb0]
      by_cases hbm : b.modNat = q
      · exact absurd (hb_eq_j0 b hb0 hbm) hne
      · rw [if_neg hbm, mul_zero]
    · rw [if_neg hb0, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j0) h

end Work.ORHughesFree.NaturalExtension
