import Mathlib
import Submission.Work.EKLComp.EntPowDefs

/-!
# `Hfam` of the `M`-fold join of a `(m+1)`-fold join

`Work.EKLComp.joinPart hT P n` is the partition `⋁_{j<n} T^{-j} P` of `EntPowDefs.lean`,
indexed by `Fin (P.n ^ n)` through `finFunctionFinEquiv`.  The lemma proved here
identifies the entropy of the `M`-fold join of the `(m+1)`-fold join along `T^[m+1]`
with the entropy of the single `(M*(m+1))`-fold join along `T`:

`Hfam μ (joinSets (T^[m+1]) (joinPart hT P (m+1)) M) = Hfam μ (joinSets T P (M*(m+1)))`.

The two sides are indexed respectively by `Fin M → Fin (P.n^(m+1))` and
`Fin (M*(m+1)) → Fin P.n`; the reindexing equivalence `jEquiv` matches a word `w` of
`M` blocks of length `m+1` with the flattened word of length `M*(m+1)` (using
`finProdFinEquiv (i,j) = j + (m+1)*i`).  The atoms are genuinely equal as sets, because
`(T^[m+1])^[i] = T^[(m+1)*i]` and preimages compose.
-/

open MeasureTheory
open Work.EKLContract

namespace Work.EKLComp

/-- Reindexing equivalence between an `M`-tuple of words of length `m+1` and a single word
of length `M*(m+1)`: it is the composition
`(Fin M → (Fin (m+1) → Fin N)) ≃ ((Fin M × Fin (m+1)) → Fin N) ≃ (Fin (M*(m+1)) → Fin N)`,
the last step being precomposition with `finProdFinEquiv`. -/
def jEquiv (m M N : ℕ) : (Fin M → Fin (N^(m+1))) ≃ (Fin (M*(m+1)) → Fin N) :=
  (Equiv.piCongrRight (fun _ : Fin M => finFunctionFinEquiv.symm)).trans
    ((Equiv.curry (Fin M) (Fin (m+1)) (Fin N)).symm.trans
      (Equiv.arrowCongr finProdFinEquiv (Equiv.refl (Fin N))))

@[simp] theorem jEquiv_apply (m M N : ℕ) (w : Fin M → Fin (N^(m+1)))
    (l : Fin (M*(m+1))) :
    jEquiv m M N w l =
      (finFunctionFinEquiv.symm (w ((finProdFinEquiv (m:=M) (n:=m+1)).symm l).1))
        ((finProdFinEquiv (m:=M) (n:=m+1)).symm l).2 := rfl

/-- The atom of the `M`-fold join of the `(m+1)`-fold join along `T^[m+1]` coincides with the
atom of the flattened `(M*(m+1))`-fold join along `T`, under the reindexing `jEquiv`. -/
theorem joinSets_iterate_joinPart {X : Type} [MeasurableSpace X] {T : X → X}
    (hT : Measurable T) (P : FinPart X) (m M : ℕ) (w : Fin M → Fin (P.n^(m+1))) :
    joinSets (T^[m+1]) (joinPart hT P (m+1)) M w
      = joinSets T P (M*(m+1)) (jEquiv m M P.n w) := by
  ext x
  simp only [joinSets, joinPart_parts, Set.mem_iInter, Set.mem_preimage]
  have hiff : ∀ (i : Fin M) (j : Fin (m+1)),
      (T^[↑j] ((T^[m+1])^[↑i] x) ∈ P.parts (finFunctionFinEquiv.symm (w i) j)) ↔
      (T^[↑(finProdFinEquiv (m:=M) (n:=m+1) (i,j))] x ∈
        P.parts (jEquiv m M P.n w (finProdFinEquiv (m:=M) (n:=m+1) (i,j)))) := by
    intro i j
    have h1 : jEquiv m M P.n w (finProdFinEquiv (m:=M) (n:=m+1) (i,j))
        = (finFunctionFinEquiv.symm (w i)) j := by
      rw [jEquiv_apply, Equiv.symm_apply_apply]
    have h2 : T^[↑(finProdFinEquiv (m:=M) (n:=m+1) (i,j))] x
        = T^[↑j] ((T^[m+1])^[↑i] x) := by
      rw [show (finProdFinEquiv (m:=M) (n:=m+1) (i,j) : ℕ) = ↑j + (m+1) * ↑i from rfl]
      rw [show (↑j : ℕ) + (m+1) * ↑i = (m+1) * ↑i + ↑j from by ring]
      rw [← Work.EKLComp.Core.iterate_comm_apply T ((m+1) * ↑i) ↑j x]
      rw [← Function.iterate_mul T (m+1) ↑i]
    rw [h1, h2]
  constructor
  · intro h l
    have := (hiff (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2).mp (h _ _)
    rwa [Equiv.apply_symm_apply] at this
  · intro h i j
    exact (hiff i j).mpr (h (finProdFinEquiv (m:=M) (n:=m+1) (i,j)))

theorem Hfam_joinSets_joinPart {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {T : X → X} (hT : Measurable T)
    (P : Work.EKLContract.FinPart X) (m M : ℕ) :
    Work.EKLContract.Hfam μ
        (Work.EKLContract.joinSets (T^[m+1]) (Work.EKLComp.joinPart hT P (m+1)) M)
      = Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P (M * (m+1))) := by
  rw [Hfam, Hfam]
  have h := Equiv.sum_comp (jEquiv m M P.n)
    (fun u => Real.negMulLog (μ (joinSets T P (M*(m+1)) u)).toReal)
  rw [← h]
  exact Finset.sum_congr rfl (fun w _ => by rw [joinSets_iterate_joinPart hT P m M w])

end Work.EKLComp
