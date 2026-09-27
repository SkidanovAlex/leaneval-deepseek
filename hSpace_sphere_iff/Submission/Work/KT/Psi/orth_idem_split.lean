import Mathlib
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Basic

/-!
# `Work.KT.Psi.orth_idem_split` — orthogonal idempotents split their sum

If `e`, `f` are idempotent matrices with `e * f = 0` and `f * e = 0`, and `u = e + f` (which is then
automatically idempotent; the hypothesis `hu` is kept only for compatibility), then
`u` and the block sum `e ⊕ f` are Murray–von Neumann equivalent, so they have the same class in
`K₀`:

`cls u = cls e + cls f`  (the right-hand side being `cls (e ⊕ f)` by `cls_sum`).

The mathematical content is the module isomorphism `im u ≅ im e ⊕ im f` given by
`x ↦ (e x, f x)` with inverse `(y, z) ↦ y + z`: on `im u` the two maps are inverse to each other
because `e z = e f z' = 0` for `z = f z'`, and `e y = y`, `f z = z`; the two maps are realised by
the rectangular block matrices `[e  f]` (`rowEF`) and `[e; f]` (`colEF`), and the identity
`[e; f] · [e  f] = diag(e, f)` uses the orthogonality `e f = f e = 0`.

No commutativity of `R` is needed.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {R : Type} [Ring R]

/-! ## The two block matrices `[e f]` and `[e; f]` -/

/-- The column matrix `[e; f]` of size `2n × n`, indexed through `finSumFinEquiv`. -/
def colEF {n : ℕ} (e f : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + n)) (Fin n) R :=
  fun k j => Sum.elim (fun i => e i j) (fun i => f i j) (finSumFinEquiv.symm k)

/-- The row matrix `[e  f]` of size `n × 2n`, indexed through `finSumFinEquiv`. -/
def rowEF {n : ℕ} (e f : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin (n + n)) R :=
  fun i k => Sum.elim (fun j => e i j) (fun j => f i j) (finSumFinEquiv.symm k)

omit [Ring R] in
@[simp] lemma colEF_inl {n : ℕ} (e f : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    colEF e f (finSumFinEquiv (Sum.inl i)) j = e i j := by
  simp only [colEF, Equiv.symm_apply_apply, Sum.elim_inl]

omit [Ring R] in
@[simp] lemma colEF_inr {n : ℕ} (e f : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    colEF e f (finSumFinEquiv (Sum.inr i)) j = f i j := by
  simp only [colEF, Equiv.symm_apply_apply, Sum.elim_inr]

omit [Ring R] in
@[simp] lemma rowEF_inl {n : ℕ} (e f : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    rowEF e f i (finSumFinEquiv (Sum.inl j)) = e i j := by
  simp only [rowEF, Equiv.symm_apply_apply, Sum.elim_inl]

omit [Ring R] in
@[simp] lemma rowEF_inr {n : ℕ} (e f : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    rowEF e f i (finSumFinEquiv (Sum.inr j)) = f i j := by
  simp only [rowEF, Equiv.symm_apply_apply, Sum.elim_inr]

/-! ## The two products -/

/-- `[e  f] · [e; f] = e + f` for idempotents `e`, `f`. -/
lemma rowEF_mul_colEF {n : ℕ} (e f : Matrix (Fin n) (Fin n) R) (he : e * e = e)
    (hf : f * f = f) : rowEF e f * colEF e f = e + f := by
  ext i j
  rw [Matrix.mul_apply, Matrix.add_apply]
  rw [(Equiv.sum_comp finSumFinEquiv
      (fun k => rowEF e f i k * colEF e f k j)).symm, Fintype.sum_sum_type]
  simp only [colEF_inl, colEF_inr, rowEF_inl, rowEF_inr]
  rw [← Matrix.mul_apply, ← Matrix.mul_apply, he, hf]

/-- `[e; f] · [e  f] = diag(e, f)` for orthogonal idempotents `e`, `f`. -/
lemma colEF_mul_rowEF {n : ℕ} (e f : Matrix (Fin n) (Fin n) R)
    (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0) :
    colEF e f * rowEF e f =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks e 0 0 f) := by
  ext k k'
  obtain ⟨s, rfl⟩ := Equiv.surjective finSumFinEquiv k
  obtain ⟨t, rfl⟩ := Equiv.surjective finSumFinEquiv k'
  rcases s with i | i <;> rcases t with j | j <;>
    simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, colEF_inl, colEF_inr, rowEF_inl, rowEF_inr,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
  · rw [← Matrix.mul_apply, he]
  · rw [← Matrix.mul_apply, hef]; rfl
  · rw [← Matrix.mul_apply, hfe]; rfl
  · rw [← Matrix.mul_apply, hf]

/-! ## Splitting -/

/-- **Orthogonal idempotents split their sum**: if `e`, `f` are idempotent with `e f = f e = 0`
and `u = e + f`, then `u` is Murray–von Neumann equivalent to the block sum `e ⊕ f`. -/
theorem mvN_sum_orth {n : ℕ} {u e f : Matrix (Fin n) (Fin n) R}
    (he : e * e = e) (hf : f * f = f) (huef : u = e + f)
    (hef : e * f = 0) (hfe : f * e = 0) :
    Mat.MvN (Mat.sum (⟨n, e⟩ : Mat R) (⟨n, f⟩ : Mat R)) (⟨n, u⟩ : Mat R) := by
  refine ⟨rowEF e f, colEF e f, ?_, ?_⟩
  · exact colEF_mul_rowEF e f he hf hef hfe
  · show rowEF e f * colEF e f = u
    rw [rowEF_mul_colEF e f he hf, huef]

theorem orth_idem_split {R : Type} [Ring R] {n : ℕ}
    {u e f : Matrix (Fin n) (Fin n) R} (hu : u * u = u) (he : e * e = e) (hf : f * f = f)
    (huef : u = e + f) (hef : e * f = 0) (hfe : f * e = 0) :
    cls (⟨n, u⟩ : Mat R) = cls (⟨n, e⟩ : Mat R) + cls (⟨n, f⟩ : Mat R) := by
  have hmv := mvN_sum_orth (R := R) he hf huef hef hfe
  have hp : Mat.IsIdem (Mat.sum (⟨n, e⟩ : Mat R) (⟨n, f⟩ : Mat R)) :=
    Mat.sum_idem (p := (⟨n, e⟩ : Mat R)) (q := (⟨n, f⟩ : Mat R)) he hf
  have hq : Mat.IsIdem (⟨n, u⟩ : Mat R) := hu
  rw [← cls_sum (p := (⟨n, e⟩ : Mat R)) (q := (⟨n, f⟩ : Mat R)) he hf]
  exact (cls_eq_of_MvN hp hq hmv).symm

end

end Work.KT.Psi
