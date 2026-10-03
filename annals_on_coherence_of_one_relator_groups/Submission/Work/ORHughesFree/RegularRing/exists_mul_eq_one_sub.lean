import Mathlib

namespace Work.ORHughesFree.RegularRing

/-- **The complement of a projection onto the kernel of `M` factors through `M`.**

Let `M : Matrix (Fin n) (Fin m) R` and let `E : Matrix (Fin m) (Fin m) R` be a matrix which fixes
every vector of the kernel of `M` (hypothesis `hker`), and let `G : Matrix (Fin n) (Fin n) R`
satisfy `G * M = M` and `M * U = G` for some `U` (so the column space of `G` equals the column
space of `M`).  Then `1 - E` factors as `S * M` — the formal content of "the complement of a
projection onto the kernel of `M` factors through `M`".

No von Neumann regularity is needed, and `E` need not be idempotent: the proof is the explicit
choice `S := (1 - E) * U`, checked with `Matrix.ext_iff_mulVec`.  For a vector `v`, put
`w := U.mulVec (M.mulVec v) - v`; then `M.mulVec w = (M*U).mulVec (M.mulVec v) - M.mulVec v =
G.mulVec (M.mulVec v) - M.mulVec v = (G*M).mulVec v - M.mulVec v = 0`, so `E.mulVec w = w` by
`hker`, hence `(1 - E).mulVec w = 0`; and
`((1-E)*U*M).mulVec v = (1-E).mulVec (U.mulVec (M.mulVec v)) = (1-E).mulVec (v + w) =
(1-E).mulVec v`. -/
theorem exists_mul_eq_one_sub {R : Type*} [Ring R] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) R) (E : Matrix (Fin m) (Fin m) R) (G : Matrix (Fin n) (Fin n) R)
    (hGM : G * M = M) (hMU : ∃ U : Matrix (Fin m) (Fin n) R, M * U = G)
    (hker : ∀ v : Fin m → R, M.mulVec v = 0 → E.mulVec v = v) :
    ∃ S : Matrix (Fin m) (Fin n) R, S * M = 1 - E := by
  obtain ⟨U, hMU⟩ := hMU
  refine ⟨(1 - E) * U, ?_⟩
  rw [Matrix.ext_iff_mulVec]
  intro v
  have hMw : M.mulVec (U.mulVec (M.mulVec v) - v) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hMU, Matrix.mulVec_mulVec, hGM, sub_self]
  have hEw : E.mulVec (U.mulVec (M.mulVec v) - v) = U.mulVec (M.mulVec v) - v := hker _ hMw
  have h1E : (1 - E).mulVec (U.mulVec (M.mulVec v) - v) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hEw, sub_self]
  have hsplit : U.mulVec (M.mulVec v) = v + (U.mulVec (M.mulVec v) - v) := by abel
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hsplit, Matrix.mulVec_add, h1E, add_zero]

end Work.ORHughesFree.RegularRing
