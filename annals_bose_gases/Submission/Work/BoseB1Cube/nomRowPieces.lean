import ChallengeDeps
import Submission.Work.BoseB1Cube.NomRowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.nomRowPieces` — the two named pieces of `nominalPerBoxRow`

Holder: `Submission/Work/BoseB1Cube/nominalPerBoxRow.lean` (the node
`Work.BoseB1Cube.nominalPerBoxRow`).  This module contains **definitions only** (hence `sorry`-free,
and importing it cannot create a cycle with the node's file or with the two pieces' files).

The target `Work.BoseB1Cube.PerBoxFNomSlots v h R` is FS `thm:smallbox` at the sliding box in the
nominal spelling, at the slots `μ` and `4μ`, for **all** `BoxState`s.  Its proof is assembled in
`nominalPerBoxRow.lean` from two genuinely different statements:

* `NomRowSqWindowRow` — **piece A**: FS's `n''`-group bound (`final_v2.tex` l.4020–4040), the
  count-windowed `Sq`-row for in-box `ContDiff` states.  This is FS `lm:appinteractionestimate` +
  the refined Bogoliubov `eq:refinedaprioribog` at the *relative* (instance-level) constant — the
  chapter's single missing analytic instrument.  It is the hypothesis `hREM` of the PROVED descent
  `Work.BoseB1Cube.nomRow_all_of_windowRows` / `perBoxFNom_inBox_of_windowRows`, and it is the
  `Sq`-form (`c₁ ψ(1,μ,t) ≤ ¼(t−μ)²` for `c₁ ≤ 1/4`) of the statement of
  `Submission/Work/BoseB1Cube/sbWordCube_ge_nomRowWindow.lean`.
* `NomRowArbState` — **piece B**: the *extension*, from a.e.-box-supported states to all
  `BoxState`s (the passage whose absence is recorded as "the least-mapped residual" in
  `FINDING_perBoxFNom_session5.md` §5/§10 and as the failure mode of
  `FINDING_sectorPassageB1_REFUTED.md`).  Its conclusion may use *fresh* constants `(c₁', C')` —
  which it must, since the two-component in-box/off-box mixture of
  `FINDING_sectorPassageB1_REFUTED.md` §1 is *tight* at the flat in-box component and forces
  `c₁ ≤ 1/2 + o(1)`; FS's own theorem carries the same restriction `0 < c < 1/2`, and
  `c₁' := min c₁ (1/4)` is admissible.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseKinLoc

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

/-- **Piece A** — FS's `n''`-group bound (the `Sq`-row, `final_v2.tex` l.4020–4040) at the sliding
box of the parameter block of `μ`, in the nominal spelling, for `ContDiff` states that are a.e.
supported in the sliding box and lie in the count window `n ≤ Cn·μ·|B(u)|`:

    ((1/4)(n/|B| − μ)² − (1/2)μ²)·∬w_{1,B}·∫Ψ² − E·∫Ψ² ≤ sbWordCube v h μ u Ψ .

This is exactly the hypothesis `hREM` of the PROVED descent
`Work.BoseB1Cube.nomRow_all_of_windowRows` (and of `perBoxFNom_inBox_of_windowRows`), i.e. the
`n''`-group row of FS's proof; it is the statement of the (unproved)
`Submission/Work/BoseB1Cube/sbWordCube_ge_nomRowWindow.lean` in its `Sq`-form (the two are
equivalent by `psiWeight ≤ (t − μ)²`, i.e. `c₁ ψ(1,μ,t) ≤ ¼(t−μ)²` for `c₁ ≤ 1/4`).  Its content is
FS `lm:appinteractionestimate` + the refined Bogoliubov `eq:refinedaprioribog` at the *relative*
(instance-level) constant — the single missing analytic instrument of the chapter
(`FINDING_sbWordCube_ge_nomRowWindow.md` §8, `FINDING_perBoxFNom_session5.md` §1, §12).

It is *not* equivalent to the target: it is count-windowed, in-box, and stated for `ContDiff`
rather than `BoxState`. -/
def NomRowSqWindowRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 3 ≤ Cn → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : X n → ℝ) (u : E3),
        u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox n (sideAt μ (a v)))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) →
        (n : ℝ) ≤ Cn * μ * nomV v μ u →
        ((1 / 4) * (((n : ℝ) / nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2) * nomW v h μ u
            * (∫ x in abox n (sideAt μ (a v)), (Ψ x) ^ 2)
          - nomE v R C μ u * (∫ x in abox n (sideAt μ (a v)), (Ψ x) ^ 2)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **Piece B** — the *extension*: from the in-box row (for all `n`, at the slot `μ`) to the row
for **every** `BoxState` at the slot `μ`.  The conclusion is allowed to use fresh constants
`(c₁', C')` (see the module docstring for why lowering `c₁` is necessary and harmless). -/
def NomRowArbState (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ (ε₀ c₁ C : ℝ), 0 < ε₀ → 0 < c₁ → 0 ≤ C →
    (∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox n (sideAt μ (a v)))),
          (Φ : X n → ℝ) x ≠ 0 →
            ∀ i : Fin n, x i ∈ dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) →
        PerBoxFNom v h R c₁ C μ μ n Φ u) →
    ∃ ε₀' c₁' C' : ℝ, 0 < ε₀' ∧ 0 < c₁' ∧ 0 ≤ C' ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀' μ →
        ∀ (n : ℕ) (Φ : BoxState n (sideAt μ (a v))) (u : E3),
          u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
          PerBoxFNom v h R c₁' C' μ μ n Φ u

/-- **Piece C** — FS's `n'`-group bound: the **linear** windowed row
(`final_v2.tex` l.4019–4026), for in-box `ContDiff` states with the *two-sided* window
`Cn·μ|B| ≤ n' ≤ 2·Cn·μ|B|`:

    (1/18)·μ·(n'/|B|)·∬w_{1,B}·∫Ψ² ≤ sbWordCube v h μ u Ψ .

This is exactly the hypothesis `hGRP` of the PROVED descent
`Work.BoseB1Cube.nomRow_all_of_windowRows` (`nomRow_descentStep` / `nomBracket_le_groupBracket`),
i.e. the supply FS use for the `m` full blocks of the `n = m n' + n''` decomposition.  Its
distinguishing feature — and the reason it is a separate piece from `NomRowSqWindowRow` — is that it
carries **no error row** (`nomE`), so that summing it over the `m` blocks does not multiply the
error constant; this is what makes the descent's arithmetic close.

⚠ **The workspace's `Work.BoseB1Cube.sbWordCube_ge_nomLinRowWindow` is NOT a clean proof of this
statement**: its file is `sorry`-free but `#print axioms Work.BoseB1Cube.sbWordCube_ge_nomLinRowWindow`
reports `sorryAx`, through the node `Work.BoseB1Cube.boxQSum_ge_boxQ0_windowCount`
(`Submission/Work/BoseB1Cube/boxQSum_ge_boxQ0_windowCount.lean`, a one-line `sorry`), whose
*predecessor* `boxQSum_ge_boxQ0_window` was declared FALSE in
`FINDING_boxQSum_ge_boxQ0_window_FALSE.md`.  A clean proof of this piece must therefore replace
that input (the honest instrument is the sharp row `boxQSum ≥ boxQ0 − (1/8)(M₂/V²)·Pc −
C·a·(μ + n/V)·n₊` in a *true* form, or the `w₁`-mass comparison FS use at `l.4019`,
`∬w_{1,B} ≥ (1−C(R/λ₁)²)(1−C(R/(ℓd))²)·∫gω·∫χ_B²`, which the corpus's own cutoff does **not**
satisfy on every box — see `FINDING_w1MassB_lowerB1_FALSE.md`). -/
def NomRowLinWindowRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n' : ℕ) (Ψ : X n' → ℝ) (u : E3),
        u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox n' (sideAt μ (a v)))),
          Ψ x ≠ 0 → ∀ i : Fin n', x i ∈ dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) →
        Cn * μ * nomV v μ u ≤ (n' : ℝ) →
        (n' : ℝ) ≤ 2 * Cn * μ * nomV v μ u →
        (1 / 18) * μ * ((n' : ℝ) / nomV v μ u) * nomW v h μ u
            * (∫ x in abox n' (sideAt μ (a v)), (Ψ x) ^ 2)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

end Work.BoseB1Cube
