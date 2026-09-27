import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.rel_cancel

/-!
# `Work.KT.EG.KLG.cls_one_sum` — the class of the identity splits along an idempotent

For an idempotent square matrix `E` over `C(X, ℂ)`, the two matrices `E` and `1 - E` are
idempotent and complementary: in module language an idempotent splits the free module into its
image and its kernel.  Consequently

`[1ₙ] = [1 - E] + [E]`   in `K₀(C(X, ℂ))`.

The proof is the elementary one: `[1-E] + [E] = [(1-E) ⊕ E]` by `cls_sum`, and the block matrix
`[[1-E, 0], [0, 1-(1-E)]] = [[1-E,0],[0,E]]` is Murray–von Neumann equivalent to `1ₙ` by the
complement-splitting lemma `Work.KT.mvN_sum_compl_mat` (applied to the idempotent `1 - E`).
-/

namespace Work.KT.EG.KLG

open Matrix

noncomputable section

/-- **The identity class splits along an idempotent.**  For an idempotent `E : Matrix (Fin n)
(Fin n) C(X, ℂ)`: `[1ₙ] = [1 - E] + [E]` in `K₀(C(X, ℂ))`. -/
theorem cls_one_sum (X : Type) [TopologicalSpace X] (n : ℕ)
    (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E) :
    Work.KT.cls (Work.KT.Mat.one C(X, ℂ) n)
      = Work.KT.cls (⟨n, 1 - E⟩ : Work.KT.Mat C(X, ℂ))
        + Work.KT.cls (⟨n, E⟩ : Work.KT.Mat C(X, ℂ)) := by
  let p : Work.KT.Mat C(X, ℂ) := ⟨n, 1 - E⟩
  let q : Work.KT.Mat C(X, ℂ) := ⟨n, E⟩
  have hA : p.IsIdem := Work.KT.Mat.isIdem_one_sub (p := q) hE
  have hB : q.IsIdem := hE
  have hEE : (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) - (1 - E) = E := by abel
  -- `p ⊕ q` is the block matrix `[[1-E, 0],[0, 1-(1-E)]]`, so `mvN_sum_compl_mat` applies.
  have hsum : p.sum q
      = ⟨n + n, Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (1 - E) 0 0 (1 - (1 - E)))⟩ := by
    simp only [Work.KT.Mat.sum, p, q]
    rw [hEE]
  have hmvn : Work.KT.Mat.MvN (p.sum q) (Work.KT.Mat.one C(X, ℂ) n) := by
    rw [hsum]
    exact Work.KT.mvN_sum_compl_mat C(X, ℂ) n (1 - E) hA
  -- `cls (p ⊕ q) = cls 1` by Murray–von Neumann equivalence, and `cls (p ⊕ q) = cls p + cls q`.
  have key : Work.KT.cls (p.sum q) = Work.KT.cls (Work.KT.Mat.one C(X, ℂ) n) :=
    Work.KT.cls_eq_of_mvN (Work.KT.Mat.sum_idem hA hB) (Work.KT.Mat.one_isIdem C(X, ℂ) n) hmvn
  rw [← Work.KT.cls_sum hA hB]
  exact key.symm

end

end Work.KT.EG.KLG
