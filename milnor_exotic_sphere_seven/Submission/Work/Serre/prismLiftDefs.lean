import Mathlib
import Submission.Work.StemsB.Fibrations

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the prism-lifting lemma (`serreC3FiniteOne`)

The transfer argument for `Work.Serre.serreC3FiniteOne` (see `C3ONE_SESSION9.md`) needs, for each
simplex `σ` of `X` and each face `∂_iσ`, a *fibrewise* homotopy (a "prism") over `∂_iσ` whose two
ends are prescribed lifts and whose sides are prescribed by the corresponding prisms of the faces
of `∂_iσ`.

This file fixes the indexing convention: `cof n i` is the `i`-th *face inclusion*
`Δ_{n-1} → Δ_n`, i.e. `stdSimplex.map (Fin.succAbove i)` with `i : Fin (n + 1)`.  Writing it this
way avoids any `n - 1` in the statements (the source is `stdSimplex ℝ (Fin n)`, which *is*
`Δ_{n-1}`), which is what makes the arithmetics of the statements below work for a variable `n`.
-/

open scoped Topology unitInterval

namespace Work.Serre

/-- The `i`-th face inclusion `Δ_{n-1} → Δ_n`: `stdSimplex.map (Fin.succAbove i)`, where
`i : Fin (n + 1)` indexes the vertices of `Δ_n`. -/
noncomputable def cof (n : ℕ) (i : Fin (n + 1)) :
    C(↥(stdSimplex ℝ (Fin n)), ↥(stdSimplex ℝ (Fin (n + 1)))) :=
  ⟨stdSimplex.map (Fin.succAbove i), stdSimplex.continuous_map _⟩

@[simp]
theorem cof_apply (n : ℕ) (i : Fin (n + 1)) (z : ↥(stdSimplex ℝ (Fin n))) :
    cof n i z = stdSimplex.map (Fin.succAbove i) z := rfl

end Work.Serre
