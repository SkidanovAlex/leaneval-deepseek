import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT.Fund

open Matrix

variable {R : Type} [Ring R] {N : ℕ}

/-- The "inclusion" `R^N → R^{N+N}` used to identify the idempotent `e + f` with the block
diagonal `diag(e, f)`: on the first summand it is `e`, on the second `f`. -/
private def inc (e f : Matrix (Fin N) (Fin N) R) : Matrix (Fin (N + N)) (Fin N) R :=
  fun i j => match finSumFinEquiv.symm i with
    | Sum.inl i' => e i' j
    | Sum.inr i' => f i' j

/-- The "projection" `R^{N+N} → R^N` left inverse to `inc`: it is `e` on the first block,
`f` on the second. -/
private def prj (e f : Matrix (Fin N) (Fin N) R) : Matrix (Fin N) (Fin (N + N)) R :=
  fun i k => match finSumFinEquiv.symm k with
    | Sum.inl j' => e i j'
    | Sum.inr j' => f i j'

private lemma prj_mul_inc (e f : Matrix (Fin N) (Fin N) R)
    (he : e * e = e) (hf : f * f = f) :
    prj e f * inc e f = e + f := by
  ext i j
  rw [Matrix.mul_apply, Matrix.add_apply]
  rw [← Equiv.sum_comp finSumFinEquiv (fun k => prj e f i k * inc e f k j)]
  rw [Fintype.sum_sum_type]
  simp only [inc, prj, Equiv.symm_apply_apply]
  rw [← Matrix.mul_apply, ← Matrix.mul_apply, he, hf]

private lemma inc_mul_prj (e f : Matrix (Fin N) (Fin N) R)
    (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0) :
    inc e f * prj e f
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks e 0 0 f) := by
  ext i l
  rw [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [inc, prj]
  set si := finSumFinEquiv.symm i with hsi
  set sl := finSumFinEquiv.symm l with hsl
  rcases si with a1 | a1 <;> rcases sl with b1 | b1
  · simp only [Matrix.fromBlocks_apply₁₁]
    rw [← Matrix.mul_apply, he]
  · simp only [Matrix.fromBlocks_apply₁₂]
    rw [← Matrix.mul_apply, hef]
  · simp only [Matrix.fromBlocks_apply₂₁]
    rw [← Matrix.mul_apply, hfe]
  · simp only [Matrix.fromBlocks_apply₂₂]
    rw [← Matrix.mul_apply, hf]

/-- Orthogonal idempotents `e, f` satisfy `e ⊕ f ∼ e + f` in `K₀`. -/
theorem kbi_or_sum {R : Type} [Ring R] (N : ℕ) (e f : Matrix (Fin N) (Fin N) R)
    (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0) :
    Work.KT.Mat.MvN (⟨N, e + f⟩ : Work.KT.Mat R)
      (Work.KT.Mat.sum (⟨N, e⟩ : Work.KT.Mat R) ⟨N, f⟩) := by
  refine ⟨inc e f, prj e f, prj_mul_inc e f he hf, ?_⟩
  exact inc_mul_prj e f he hf hef hfe

end Work.KT.Fund
