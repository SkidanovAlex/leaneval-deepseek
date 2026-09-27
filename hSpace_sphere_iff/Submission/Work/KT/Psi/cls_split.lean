import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.sumMvN

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/KT/DESIGN.md 'Addendum: psi'. SHARED helper needed by psi_exists (H8) and psi_comm (H6). CONVENTION: [Ring A] + explicit commutativity, never [CommRing A].

# `Work.KT.Psi.cls_split`

If `P` and `E` are idempotent commuting square matrices, then in `K₀`
`[P] = [P·E] + [P·(1-E)]`.

The mathematical content is that `PE` and `P(1-E)` are idempotent, orthogonal, sum to `P`, and
that an idempotent which is the orthogonal sum of two idempotents is Murray–von Neumann equivalent
to their block sum (whence `cls` is additive).  The MvN witnesses are the block matrices
`b = [PE, P(1-E)]` and `a = [[PE],[P(1-E)]]`, for which `b·a = PE + P(1-E) = P` and
`a·b = [[PE,0],[0,P(1-E)]]`.

The only fiddly point is bookkeeping: `Mat.sum` is a block matrix indexed by `Fin (N+N)` obtained
from the block matrices over `Fin N ⊕ Fin N` by `finSumFinEquiv`, while the "column block"
`[[PE],[P(1-E)]]` lives over `Fin N ⊕ Fin 0`; the equivalence `Fin n ⊕ Fin 0 ≃ Fin n` and the
reindexing lemmas below bridge the two.

Everything here is used only through `Work.KT.Psi.cls_split`; the helpers live in the nested
namespace `Work.KT.Psi.ClsSplit` so they cannot clash with other files.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

namespace ClsSplit

variable {A : Type} [Ring A]

/-- The canonical equivalence `Fin n ⊕ Fin 0 ≃ Fin n` (the empty summand is dropped). -/
def szc (n : ℕ) : Fin n ⊕ Fin 0 ≃ Fin n where
  toFun x := x.elim id (fun j => j.elim0)
  invFun i := Sum.inl i
  left_inv x := by
    cases x with
    | inl i => rfl
    | inr j => exact Fin.elim0 j
  right_inv i := rfl

@[simp] lemma szc_symm_apply (n : ℕ) (i : Fin n) : (szc n).symm i = Sum.inl i := rfl

/-- Reindexing a block matrix whose second block is empty (in both dimensions) recovers the
first block. -/
lemma reindex_diag (n : ℕ) (P : Matrix (Fin n) (Fin n) A) :
    Matrix.reindex (szc n) (szc n) (Matrix.fromBlocks P 0 0 0) = P := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, szc_symm_apply, szc_symm_apply]
  exact Matrix.fromBlocks_apply₁₁ P 0 0 0 i j

/-- **Block splitting.**  If `u = e + f` with `e, f` idempotent and orthogonal, then the
idempotent `u` is Murray–von Neumann equivalent to the block sum `e ⊕ f`. -/
lemma mvN_orth {N : ℕ} {u e f : Matrix (Fin N) (Fin N) A}
    (he : e * e = e) (hf : f * f = f) (huef : u = e + f)
    (hef : e * f = 0) (hfe : f * e = 0) :
    Mat.MvN (⟨N, u⟩ : Mat A) (Mat.sum (⟨N, e⟩ : Mat A) ⟨N, f⟩) := by
  set A₀ : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin 0) A := Matrix.fromBlocks e 0 f 0 with hA₀
  set B₀ : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin N) A := Matrix.fromBlocks e f 0 0 with hB₀
  have hBA : B₀ * A₀ = Matrix.fromBlocks u 0 0 0 := by
    rw [hA₀, hB₀, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, he, hf, ← huef]
  have hAB : A₀ * B₀ = Matrix.fromBlocks e 0 0 f := by
    rw [hA₀, hB₀, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, he, hf, hef, hfe]
  refine ⟨Matrix.reindex finSumFinEquiv (szc N) A₀,
    Matrix.reindex (szc N) finSumFinEquiv B₀, ?_, ?_⟩
  · show Matrix.reindex (szc N) finSumFinEquiv B₀ *
      Matrix.reindex finSumFinEquiv (szc N) A₀ = u
    rw [reindexMul (szc N) finSumFinEquiv (szc N) B₀ A₀, hBA, reindex_diag]
  · show Matrix.reindex finSumFinEquiv (szc N) A₀ *
      Matrix.reindex (szc N) finSumFinEquiv B₀ = (Mat.sum (⟨N, e⟩ : Mat A) ⟨N, f⟩).2
    rw [reindexMul finSumFinEquiv (szc N) finSumFinEquiv A₀ B₀, hAB]
    rfl

/-- `K₀`-version of `mvN_orth`: the class of an idempotent is the sum of the classes of two
orthogonal idempotent summands. -/
lemma cls_orth {N : ℕ} {u e f : Matrix (Fin N) (Fin N) A}
    (hu : u * u = u) (he : e * e = e) (hf : f * f = f) (huef : u = e + f)
    (hef : e * f = 0) (hfe : f * e = 0) :
    cls (⟨N, u⟩ : Mat A) = cls (⟨N, e⟩ : Mat A) + cls (⟨N, f⟩ : Mat A) := by
  have hsum : (Mat.sum (⟨N, e⟩ : Mat A) ⟨N, f⟩).IsIdem :=
    Mat.sum_idem (p := (⟨N, e⟩ : Mat A)) (q := (⟨N, f⟩ : Mat A)) he hf
  have hmvN : Mat.MvN (⟨N, u⟩ : Mat A) (Mat.sum (⟨N, e⟩ : Mat A) ⟨N, f⟩) :=
    mvN_orth he hf huef hef hfe
  rw [cls_eq_of_mvN (p := (⟨N, u⟩ : Mat A)) (q := Mat.sum (⟨N, e⟩ : Mat A) ⟨N, f⟩) hu hsum hmvN,
    cls_sum (p := (⟨N, e⟩ : Mat A)) (q := (⟨N, f⟩ : Mat A)) he hf]

end ClsSplit

/-- Splitting an idempotent by a commuting idempotent. -/
theorem cls_split (A : Type) [Ring A] (N : ℕ) (P E : Matrix (Fin N) (Fin N) A)
    (hP : P * P = P) (hE : E * E = E) (hPE : P * E = E * P) :
    cls (⟨N, P⟩ : Mat A) = cls ⟨N, P * E⟩ + cls ⟨N, P * (1 - E)⟩ := by
  -- the complementary idempotent `1 - E` and its commutation with `P`
  have hF : (1 - E) * (1 - E) = 1 - E := by
    have h : (1 - E) * (1 - E) = 1 - E - E + E * E := by noncomm_ring
    rw [h, hE]
    abel
  have hPF : P * (1 - E) = (1 - E) * P := by
    have h1 : P * (1 - E) = P - P * E := by noncomm_ring
    have h2 : (1 - E) * P = P - E * P := by noncomm_ring
    rw [h1, h2, hPE]
  -- `P = PE + P(1-E)`
  have hE1 : E + (1 - E) = 1 := by abel
  have hPQR : P = P * E + P * (1 - E) := by
    rw [← Matrix.mul_add, hE1, Matrix.mul_one]
  -- idempotency of the summands
  have hQ : (P * E) * (P * E) = P * E := by
    calc (P * E) * (P * E) = P * (E * P) * E := by noncomm_ring
      _ = P * (P * E) * E := by rw [← hPE]
      _ = (P * P) * (E * E) := by noncomm_ring
      _ = P * E := by rw [hP, hE]
  have hR : (P * (1 - E)) * (P * (1 - E)) = P * (1 - E) := by
    calc (P * (1 - E)) * (P * (1 - E)) = P * ((1 - E) * P) * (1 - E) := by noncomm_ring
      _ = P * (P * (1 - E)) * (1 - E) := by rw [← hPF]
      _ = (P * P) * ((1 - E) * (1 - E)) := by noncomm_ring
      _ = P * (1 - E) := by rw [hP, hF]
  -- orthogonality of the summands
  have hEF : E * (1 - E) = 0 := by
    have h : E * (1 - E) = E - E * E := by noncomm_ring
    rw [h, hE, sub_self]
  have hFE : (1 - E) * E = 0 := by
    have h : (1 - E) * E = E - E * E := by noncomm_ring
    rw [h, hE, sub_self]
  have hQR : (P * E) * (P * (1 - E)) = 0 := by
    calc (P * E) * (P * (1 - E)) = P * (E * P) * (1 - E) := by noncomm_ring
      _ = P * (P * E) * (1 - E) := by rw [← hPE]
      _ = (P * P) * (E * (1 - E)) := by noncomm_ring
      _ = 0 := by rw [hP, hEF, Matrix.mul_zero]
  have hRQ : (P * (1 - E)) * (P * E) = 0 := by
    calc (P * (1 - E)) * (P * E) = P * ((1 - E) * P) * E := by noncomm_ring
      _ = P * (P * (1 - E)) * E := by rw [← hPF]
      _ = (P * P) * ((1 - E) * E) := by noncomm_ring
      _ = 0 := by rw [hP, hFE, Matrix.mul_zero]
  exact ClsSplit.cls_orth (u := P) (e := P * E) (f := P * (1 - E)) hP hQ hR hPQR hQR hRQ

end

end Work.KT.Psi
