import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup

/-!
# Vocabulary for the proof of `Work.RatHurewicz.excisionRelPiVanishing`

The crux of the Puppe proof of homotopy excision (tom Dieck, *Algebraic Topology*, (6.9.1)--(6.9.3))
is a statement about the pair `(F, F_B)` of the *based* homotopy fibres of the triad
`(X; B, C)`: writing `F = homotopyFibre (setIncl C) y₀` and `F_B = homotopyFibre (interInclLeft B C) x₀`,
the comparison map is `excisionComparison B C x₀ : F_B → F` (`ExcisionSetup.lean`), and one has to
show that every map of pairs `(I^d, ∂I^d) → (F, range ι)` is homotopic relative to `∂I^d` into
`range ι`, for `d ≤ p + q + 1`.

The hypotheses of the theorem are stated at the single base point `x₀`: `π_k(F_B) = 0` for `k ≤ p`
and `π_k(F_C) = 0` for `k ≤ q`.  By the compression criterion (tom Dieck (6.7.3), (6.7.5)) these
give compression properties of the pairs `(B, B∩C)` and `(C, B∩C)` — but only for maps whose
*base points* are joined to `x₀` inside the relevant piece: the vanishing is not available at the
other base points (this is the substance of the reduction of tom Dieck's Problem 1 after (6.4.1),
and it is genuinely needed, see the counterexample recorded in `EXCISION_NOTES.md`).  This file
therefore fixes the small variation of the compression property in which the allowed boundary
values are restricted to a subset `Bd` of the subspace.

* `Work.RatHurewicz.CompressRelBd A Bd d` — compression of the pair `(Y, A)`: every map of pairs
  `(I^d, ∂I^d) → (Y, A)` whose boundary lands in `Bd ⊆ A` is homotopic relative to `∂I^d` into `A`.
  With `Bd = A` this is the compression property `Work.RatHurewicz.CompressRel` of the interface.
-/

set_option linter.unusedVariables false

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- **Compression of a pair with restricted boundary values.**  For a topological space `Y`, a
subspace `A ⊆ Y` and a subset `Bd ⊆ A`, this is the statement: every continuous map of pairs
`(I^d, ∂I^d) → (Y, A)` whose restriction to `∂I^d` lands in `Bd` is homotopic to a map into `A`,
relative to `∂I^d`.

For `Bd = A` this is the compression property of tom Dieck (6.7.5)(1); the restriction to `Bd` is
what is available in the single-basepoint situation of `excisionRelPiVanishing`. -/
def CompressRelBd {Y : Type} [TopologicalSpace Y] (A Bd : Set Y) (d : ℕ) : Prop :=
  ∀ f : C(ICube d, Y), (∀ x, x ∈ Cube.boundary (Fin d) → f x ∈ Bd) →
    ∃ G : C(ICube d × I, Y),
      (∀ x, G (x, 0) = f x) ∧
      (∀ x (hx : x ∈ Cube.boundary (Fin d)) t, G (x, t) = f x) ∧
      (∀ x, G (x, 1) ∈ A)

end

end Work.RatHurewicz
