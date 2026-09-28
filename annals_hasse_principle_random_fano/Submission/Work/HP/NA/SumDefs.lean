import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Definitions for the second-moment bound on `σ_Q`

The non-Archimedean factor `σ(a;Q)` (see `Setup.lean`) counts primitive vectors
`b ∈ (ZMod Q)^{n+1}` with `f_a(b) = 0`, normalised by `Q^n`.  To bound
`∑_{a primitive} σ(a;Q)^2` we expand the square and count pairs `(b₁,b₂)` of
primitive vectors.

* `irep` is the canonical integer representative (coordinates in `[0,Q)`) of a vector
  over `ZMod Q`; it is used to feed `b` to the `ℤ`-valued `gcdMinors2` machinery.
* `Bprim` is the finite set of primitive vectors `(ZMod Q)^{n+1}`.
-/

noncomputable section
set_option autoImplicit false

namespace Work.HP.NA

/-- The primitive vectors of `(ZMod q)^{n+1}`: those whose coordinates generate the unit ideal. -/
def Bprim (n q : ℕ) [NeZero q] : Finset (Fin (n + 1) → ZMod q) := by
  classical
  exact Finset.univ.filter (fun b => IsPrimGen q b)

/-- The canonical integer representative of a vector over `ZMod q` (coordinates in `[0,q)`). -/
def irep {n q : ℕ} (b : Fin (n + 1) → ZMod q) : Fin (n + 1) → ℤ := fun i => ((b i).val : ℤ)

@[simp] theorem irep_apply {n q : ℕ} (b : Fin (n + 1) → ZMod q) (i : Fin (n + 1)) :
    irep b i = ((b i).val : ℤ) := rfl

/-- The integer representative reduces back to the original vector. -/
theorem irep_cast {n q : ℕ} [NeZero q] (b : Fin (n + 1) → ZMod q) (i : Fin (n + 1)) :
    ((irep b i : ℤ) : ZMod q) = b i := by
  simp only [irep, Int.cast_natCast]
  exact ZMod.natCast_zmod_val (b i)

theorem mem_Bprim {n q : ℕ} [NeZero q] {b : Fin (n + 1) → ZMod q} :
    b ∈ Bprim n q ↔ IsPrimGen q b := by
  classical
  simp [Bprim]

end Work.HP.NA
