import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseWire/Basic` — the wire's single input predicate

This is the root module of the `Work.BoseWire` area: the *wire* that reduces
the challenge statement (`Submission.lean`'s Theorem 1.2) to **one** named
statement about the box, namely

> FS `thm:LHY-Box` on the box `Λ = ∂(L)` at the FS parameters, for *some*
> admissible error exponent `η₀ > 1/2000` and *some* coefficient `C ≥ 0`,
> together with a scattering solution `h` of `v`.

The box statement itself is `Work.BoseBoxFix.LHYBoxB v h η₀ C` (the
`BoseKinLoc` box form over the symmetric `BoxState`s, `n` free); the wire
bundles it with its numerical side conditions into the single `Prop`
`LHYBoxBInput v`.

Nothing here says anything *new* about the box: the area's job is the wiring,
i.e. producing from `LHYBoxBInput v` (under the challenge's hypotheses on `v`)

* the pressure-level target `Work.BoseTop.HBoxGpTarget v`
  (`Work.BoseWire.HBoxGpTarget_of_LHYBoxBInput`), and
* the challenge statement shaped exactly as `Submission.BoseGases.theorem_1_2`
  (`Work.BoseWire.theorem_1_2_of_LHYBoxBInput` and the check file
  `Submission/Work/BoseWire/Patch.lean`).

The consumers of this area are documented in
`Submission/Work/BoseWire/README.md`.

## Conventions

* `ScatSol v` is `Work.UBB.ScatSol v = ∃ w, IsRadial w ∧ IsScatteringSolution w v`,
  the corpus's `h`-hypothesis (the scattering solution of `v`).
* `LHYBoxB v h η₀ C` is `Work.BoseBoxFix.LHYBoxB` (`BOSE_BOXNODES_LEAD.md`), the
  corrected box-restricted form of FS `thm:LHY-Box`.
* the error window `1/2000 < η₀ ≤ 1/2` is exactly the one of
  `Work.BoseTop.HBoxGTarget`/`HBoxGpTarget` (FS's window with the challenge's
  error exponent `η = 1/2000` strictly below `η₀`).
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseWire

open _root_.BoseGases Submission.BoseGases
open Work.UBB Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The input predicate -/

/-- **The single remaining box input**, bundled: `v` admits a scattering
solution `h` and FS `thm:LHY-Box` (`Work.BoseBoxFix.LHYBoxB`) holds for it at
some error exponent `η₀` in the window `1/2000 < η₀ ≤ 1/2` and some coefficient
`C ≥ 0`.

This is *the* hypothesis left of the wire.  The existential over `h` is
essential: `LHYBoxB v h η₀ C` genuinely depends on the scattering solution `h`
(it enters the box form through `g₀ v h`), and the workspace does not produce a
witness `ScatSol v` from the challenge's hypotheses on `v` — so the wire takes it
as part of its input rather than fixing a canonical one.  Evidence: the only
witness theorem in the workspace is `Work.SmallBoxA0.VZero.hZero` (for the zero
potential), and the corpus's `Submission.ScatChosen.w0_spec` only *chooses* a
scattering solution from a supplied witness `ScatSol v`.  If a witness theorem
ever lands, the bundle can be restated with `h` fixed by a one-line change; the
API below (`of_LHYBoxB`, `exists_scatSol`) is exactly what such a restatement
needs. -/
def LHYBoxBInput (v : ℝ³ → ℝ) : Prop :=
  ∃ (h : ScatSol v) (η₀ C : ℝ), 1 / 2000 < η₀ ∧ η₀ ≤ 1 / 2 ∧ 0 ≤ C ∧ LHYBoxB v h η₀ C

/-- Introduction form of `LHYBoxBInput`, for a caller who already holds the box
theorem as `LHYBoxB v h η₀ C` together with its numerical side conditions. -/
lemma LHYBoxBInput.of_LHYBoxB {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ}
    (hη₀ : 1 / 2000 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hC : 0 ≤ C)
    (hL : LHYBoxB v h η₀ C) : LHYBoxBInput v :=
  ⟨h, η₀, C, hη₀, hη₀le, hC, hL⟩

/-- Destructuring form of `LHYBoxBInput`. -/
lemma LHYBoxBInput.exists_box {v : ℝ³ → ℝ} (h : LHYBoxBInput v) :
    ∃ (h : ScatSol v) (η₀ C : ℝ), 1 / 2000 < η₀ ∧ η₀ ≤ 1 / 2 ∧ 0 ≤ C ∧ LHYBoxB v h η₀ C :=
  h

/-- The wire's input supplies a scattering solution of `v`. -/
lemma LHYBoxBInput.exists_scatSol {v : ℝ³ → ℝ} (h : LHYBoxBInput v) : ScatSol v := by
  obtain ⟨h', _⟩ := h
  exact h'

/-- Monotonicity in the potential: if `v = v'` pointwise then the input
transfers (recorded for convenience of callers who rewrite `v`).  Stated for
propositional equality, which is all the wire ever needs. -/
lemma LHYBoxBInput.congr {v v' : ℝ³ → ℝ} (hvv : v = v') (h : LHYBoxBInput v) :
    LHYBoxBInput v' :=
  hvv ▸ h

end Work.BoseWire
