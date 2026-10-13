/-
# `Submission/Work/FTS/NonlinRows/Goals.lean` — the remaining row goals, as named `def`s

The deliverable is `Work.FTS.OpenPkg.N4Rows' IP α₂ Ci Ct Ce Cs`; `Assembly.lean` already reduces
it to five obligations, each a `Prop`.  The `def`s below name those obligations (and the
per-row obligations) in the compact `Ctx` vocabulary of `Defs.lean`, so that each remaining
piece of work can be delegated with a one-line statement.

Nothing here is a proof obligation by itself; the lemmas proving these `def`s are the rows of
this directory (`NRow8.lean`, `NRow9.lean`, …).  See `NOTES_Rows.md` and `NOTES_Handoff.md`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The three group obligations (the `rowsN0`/`rowsN`/`rowsAux` fields of `N4Rows'`) -/

def N0Data (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.FTS.Nonlinear.Pieces.N0Rows IP α K g Φs Φg

def NData (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.FTS.Nonlinear.Pieces.NRows IP α K g Φs Φg

def AuxData (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.FTS.Nonlinear.Pieces.AuxRows IP α K g Φs Φg

def SplitsAll (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg → SplitsData α g Φs Φg

def HkAll (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.FTS.OpenPkg.PiecesHk α g Φs Φg

/-! ## The individual `NRows` goals still to be proved -/

def R10 (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1sg α Φs g) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g)
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)

def R11 (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1ss α Φs) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ K * α ^ 2

def R14 (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2sg α Φs g) ∧
      |IP α (Work.FTS.Nonlin.N2sg α Φs g) g|
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)

def R15 (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2ss α Φs) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs) ≤ K * α ^ 2

def R16 (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3gg α g Φg) ∧
      |IP α (Work.FTS.Nonlin.N3gg α g Φg) g|
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 3)

def R17 (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3gs α g Φg) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3gs α g Φg)
        ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)

def R18 (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3sg α Φs g) ∧
      |IP α (Work.FTS.Nonlin.N3sg α Φs g) g|
        ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2)

def R19 (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3ss α Φs) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ K * α ^ 3

def R20 (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4gg α g) ∧
      |IP α (Work.FTS.Nonlin.N4gg α g) g|
        ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)

def R21 (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4gs α g) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4gs α g)
        ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)

def R22 (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4sg α g) ∧
      |IP α (Work.FTS.Nonlin.N4sg α g) g|
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)

def R23 (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4ss α) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4ss α) ≤ K * α ^ 3

def R24 (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5gg g) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gg g) ≤ K * Work.FTS.Nonlin.Xn α g ^ 2

def R25 (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5gs α g) ∧
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5sg α g) ∧
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gs α g)
        + Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5sg α g)
      ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)

def R26 (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5ss α) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5ss α) ≤ K * α ^ 2

def Rrl1 (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn}, Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
    |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) 0|
      ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)

/-! ## The two remaining obligations in the upgraded (`StarPkgo2`) context -/

/-- **The `NRows2` obligation**: rows 8--26 with one uniform constant in the upgraded context. -/
def NData2 (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
    Work.FTS.VocabO2.Ctx2 α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.FTS.VocabO2.NRows2 IP α K g Φs Φg

/-- **The `PiecesHk` obligation** in the upgraded context: the `ℋ⁴`-honesty of every piece. -/
def HkAll2 (α₂ Ci Ct Ce Cs : ℝ) : Prop :=
  ∀ {α : ℝ} {g Φs Φg : Fn}, Work.FTS.VocabO2.Ctx2 α₂ Ci Ct Ce Cs α g Φs Φg →
    Work.FTS.OpenPkg.PiecesHk α g Φs Φg

end Work.FTS.NonlinRows
