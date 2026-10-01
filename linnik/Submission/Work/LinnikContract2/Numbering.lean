/-
# LinnikContract2 — Numbering.lean  (ROUND 2, CORRECTED)

**`Area0 = WideMinExists` is a theorem, not an input.**

Round 2's numbered zero is the *wide minimiser*: `IsMin1 χ₁ ρ₁` says that `ρ₁` is a non-principal
zero with `|Im ρ₁| ≤ 10` whose `λ` is minimal among all such zeros.  There is no requirement that
`ρ₁` lie in the working region `|Im| ≤ 1`.

The existence of such a zero is *provable*: for each non-principal `χ` the set of zeros of the
completed L-function in the critical strip with `|Im| ≤ 10` is finite
(`Commons…lFunction_zeroSet_box_finite`, `Commons…completedL_zero_strip`), so the union over the
finitely many characters is finite, and `λ` attains its minimum there.  This is
`Work.LinnikContract2.exists_wideMin` (`NumZero/exists_wideMin.lean`, delegated and proved), and
`area0` below is its `Area0` form.

Consequently round 2 carries **no** extra hypothesis: `Area7` instantiates its §§14–15 argument at
this minimiser, and `linnik_of_areas` takes the seven paper areas only.

Historical note: an earlier draft of round 2 carried the input "the wide minimiser may be taken in
the working region" (`WideMinNarrow`, since deleted).  That requirement is *not* part of HB's §6
convention and is not provable from Theorems 1–3 (which are stated for `|t| ≤ 1`); it was a defect
of the draft, reported by the project lead, and the corrected definition (`Defs.IsMin1H`) no longer
mentions the working region.
-/
import Submission.Work.LinnikContract2.Defs
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract2.Areas
import Submission.Work.LinnikContract2.NumZero.exists_wideMin

open DirichletCharacter Complex
open Work.LinnikContract2.NumZero
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2

/-- **`Area0`, proved.**  HB's §6 numbered zero exists: whenever a non-principal zero of height
`≤ 10` exists, `λ` attains its minimum over that (finite) set. -/
theorem area0 : Area0 := fun _ _ hwide => exists_wideMin hwide

/-- The same, in the `IsMin1H` form at an arbitrary height `H ≥ 1`: the wide minimiser exists, and
it may be taken at any height for which the region is inhabited. -/
theorem isMin1H_exists {q : ℕ} [NeZero q] {H : ℝ}
    (h : ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZH H χ ρ) :
    ∃ (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ), IsMin1H H χ₁ ρ₁ :=
  exists_wideMin h

end Work.LinnikContract2
