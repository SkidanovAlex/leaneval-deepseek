import Mathlib
import Submission.Work.KT.Psi.QBlkSetup
import Submission.Work.KT.Psi.sum_eq_sum_jQ
import Submission.Work.KT.Psi.clsI_submatrix_of_support

/-!
# `Work.KT.Psi.clsM_sumBlkQ_cubePart`

The `q`-block of the triple tensor power of `p ⊕ q`, cut down by the spectral projector `Cp` of
the cyclic permutation of the three tensor factors, has the class of `cubePart λ q`:

`clsM (SQ (Fin p.1 ⊕ Fin q.1)) (kron3g (sumBlkQ p q) * Cp (Fin p.1 ⊕ Fin q.1) λ)
  = cls (cubePart λ q)`.

Here `sumBlkQ p q` is the block matrix with `q.2` in the `q`-block and `0` elsewhere, so
`kron3g (sumBlkQ p q)` is supported on the single word of `SQ (Fin p.1 ⊕ Fin q.1)` all of whose
entries lie in the `q`-block (the word `(1,1,1)` in `Work.KT.Psi.QBlkSetup`), and the cyclic
permutation preserves that word.  Consequently:

* `kron3g (sumBlkQ p q) * Cp` vanishes unless *both* indices lie in the `q`-word
  (`clsM_sumBlkQ_cubePart_supp`), so by the general block-restriction lemma
  `clsI_submatrix_of_support` its class equals the class of its compression to the word;
* on the word, the entries of `kron3g (sumBlkQ p q) * Cp` are the entries of
  `kron3g q.2 * Cp (Fin q.1) λ` (`clsM_sumBlkQ_cubePart_block`, using the entry computations for
  `kron3g (sumBlkQ p q)` and for `Cp` on the word), and the sum over the full index type collapses
  to the sum over the word (`sum_eq_sum_jQ`);
* finally `kron3g q.2 * Cp (Fin q.1) λ = cubePartP λ q` and
  `clsM (SQ (Fin q.1)) (cubePartP λ q) = cls (cubePart λ q)`.

All the entry computations are entrywise and therefore require no commutativity of `A`; the class
computation is unconditional (no idempotency hypothesis): if `q` is not idempotent, both sides
vanish.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

/-- `clsM` is invariant under reindexing a square matrix along an equivalence. -/
theorem clsM_reindex {R : Type} [Ring R] {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : Matrix ι ι R) :
    clsM κ (Matrix.reindex e e M) = clsM ι M :=
  clsI_reindex e M

/-- `kron3g (sumBlkQ p q) * Cp` vanishes off the `q`-word: if *one* of the two indices is not in
the word, the entry is `0`. -/
theorem clsM_sumBlkQ_cubePart_supp {A : Type} [Ring A] [Algebra ℂ A] (p q : Mat A) (lam : ℂ) :
    ∀ i j : SQ (Fin p.1 ⊕ Fin q.1),
      ¬ (isQ i ∧ isQ j) →
        (kron3g (sumBlkQ p q) * Cp (A := A) (Fin p.1 ⊕ Fin q.1) lam) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  by_cases hi : isQ i
  · have hj : ¬ isQ j := fun hj => hij ⟨hi, hj⟩
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : isQ z
    · rw [Cp_eq_zero_of_isQ_not_isQ lam z j hz hj, mul_zero]
    · rw [kron3g_sumBlkQ_eq_zero_of_not_isQ_right p q i z hz, zero_mul]
  · refine Finset.sum_eq_zero fun z _ => ?_
    rw [kron3g_sumBlkQ_eq_zero_of_not_isQ_left p q i z hi, zero_mul]

/-- On the `q`-word, the entries of `kron3g (sumBlkQ p q) * Cp` are those of
`kron3g q.2 * Cp (Fin q.1) λ`. -/
theorem clsM_sumBlkQ_cubePart_block {A : Type} [Ring A] [Algebra ℂ A] (p q : Mat A) (lam : ℂ)
    (a b : SQ (Fin q.1)) :
    (kron3g (sumBlkQ p q) * Cp (A := A) (Fin p.1 ⊕ Fin q.1) lam) (jQ (n := p.1) a)
        (jQ (n := p.1) b)
      = (kron3g q.2 * Cp (A := A) (Fin q.1) lam) a b := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [sum_eq_sum_jQ (n := p.1) (m := q.1)
    (f := fun z => kron3g (sumBlkQ p q) (jQ (n := p.1) a) z *
      Cp (A := A) (Fin p.1 ⊕ Fin q.1) lam z (jQ (n := p.1) b))
    (fun z hz => by rw [kron3g_sumBlkQ_eq_zero_of_not_isQ_right p q (jQ (n := p.1) a) z hz,
      zero_mul])]
  exact Finset.sum_congr rfl (fun c _ => by rw [kron3g_sumBlkQ_jQ, Cp_jQ])

/-- The compression of `kron3g (sumBlkQ p q) * Cp` to the `q`-word is the reindexed
`kron3g q.2 * Cp (Fin q.1) λ`. -/
theorem clsM_sumBlkQ_cubePart_submatrix {A : Type} [Ring A] [Algebra ℂ A] (p q : Mat A)
    (lam : ℂ) :
    (kron3g (sumBlkQ p q) * Cp (A := A) (Fin p.1 ⊕ Fin q.1) lam).submatrix
        Subtype.val Subtype.val =
      Matrix.reindex (blkE p.1 q.1) (blkE p.1 q.1)
        (kron3g q.2 * Cp (A := A) (Fin q.1) lam) := by
  ext i j
  rw [Matrix.submatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hi : i.1 = jQ (n := p.1) ((blkE p.1 q.1).symm i) := by
    conv_lhs => rw [← Equiv.apply_symm_apply (blkE p.1 q.1) i]
    rw [blkE_apply]
  have hj : j.1 = jQ (n := p.1) ((blkE p.1 q.1).symm j) := by
    conv_lhs => rw [← Equiv.apply_symm_apply (blkE p.1 q.1) j]
    rw [blkE_apply]
  rw [hi, hj, clsM_sumBlkQ_cubePart_block]

theorem clsM_sumBlkQ_cubePart {A : Type} [Ring A] [Algebra ℂ A] (p q : Work.KT.Mat A) (lam : ℂ) :
    Work.KT.Psi.clsM (Work.KT.Psi.SQ (Fin p.1 ⊕ Fin q.1))
      (Work.KT.Psi.kron3g (Work.KT.Psi.sumBlkQ p q) * Work.KT.Psi.Cp (Fin p.1 ⊕ Fin q.1) lam)
      = Work.KT.cls (Work.KT.cubePart lam q) := by
  classical
  have hNP : kron3g q.2 * Cp (A := A) (Fin q.1) lam = cubePartP lam q := by
    simp only [Cp, kron3g, cubePartP, kron3m, cyc3_eq_cycPermP]
  calc clsM (SQ (Fin p.1 ⊕ Fin q.1))
        (kron3g (sumBlkQ p q) * Cp (A := A) (Fin p.1 ⊕ Fin q.1) lam)
      = clsM {x : SQ (Fin p.1 ⊕ Fin q.1) // isQ x}
          ((kron3g (sumBlkQ p q) * Cp (A := A) (Fin p.1 ⊕ Fin q.1) lam).submatrix
            Subtype.val Subtype.val) :=
        clsI_submatrix_of_support _ (clsM_sumBlkQ_cubePart_supp p q lam)
    _ = clsM {x : SQ (Fin p.1 ⊕ Fin q.1) // isQ x}
          (Matrix.reindex (blkE p.1 q.1) (blkE p.1 q.1)
            (kron3g q.2 * Cp (A := A) (Fin q.1) lam)) := by
        rw [clsM_sumBlkQ_cubePart_submatrix]
    _ = clsM (SQ (Fin q.1)) (kron3g q.2 * Cp (A := A) (Fin q.1) lam) :=
        clsM_reindex (blkE p.1 q.1) _
    _ = clsM (SQ (Fin q.1)) (cubePartP lam q) := by rw [hNP]
    _ = cls (cubePart lam q) := clsM_I3_cubePartP lam q

end

end Work.KT.Psi
