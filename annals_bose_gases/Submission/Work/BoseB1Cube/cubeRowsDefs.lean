import ChallengeDeps
import Submission.Work.BoseB1Cube.cubeSmallNArb12
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.cubeRowsDefs` — the **lower** definition layer of the node

The five definitions `Work.BoseB1Cube.CubeCoreSet`, `CubeRowsOn`, `CubeRowsCore`,
`CubeRowsNonCore` and (the `Prop`-layer they rest on) are moved here, *below* the holder file
`Submission/Work/BoseB1Cube/cubeSmallNArb12ExHolds.lean`, with their bodies **verbatim** (same
names, same namespace, same statements).

**Why this matters (a hard Lean fact the chapter's architecture depended on).**  The holder file
declares the *target* `Work.BoseB1Cube.cubeSmallNArb12ExHolds`, whose body is a `sorry` that must be
filled by a proof *inside the holder's import cone* — and Lean forbids import cycles, so no module
that (transitively) imports the holder can be used for that fill.  42 files in this area import the
holder, including almost every auxiliary lemma written for this node in sessions 1–9
(`cubeRowsOnCore`, `cubeRowsWindowVanish`, `cubeRowsThinBox`, the `rowsOf*` shell nodes,
`cubeRowsThickShell`, `cubeSmallNArb12ExGlue2`, the sessions-9 assembly …).  Those files import the
holder only for these five definitions (or for `sbWordCube`-level spellings that live lower).

So: the definitions live here, the holder imports this module, and every consumer keeps seeing
exactly the same names — and a consumer that *only* needed the definitions can be re-pointed at
this module (one import line) and thereby become usable **inside** the holder's cone.  That is the
precondition for ever filling the holder's `sorry` with the assembled argument; the alternative
(copying the definitions under new names in a lower module) would force an `Iff.rfl`-style
conversion at every interface.

`cubeSmallNArb12Ex_of_rows_split` (the split of the target into the two regions) stays in the
holder file — it is *about* `CubeSmallNArb12Ex`, which lives in `cubeSmallNArb12` (lower), and it is
the only assembling statement the holder's own cone still needs.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **The core condition** `∀ j, |((ℓd)•u)_j| ≤ ℓ/16` — the region on which the corpus's box
data (`w1MassB ≥ (1/4)(a v)χ_B`, the sharp `lm:w2>w1` with the *state-dependent* coefficient, the
mass upper bounds) are PROVED; its complement is the residual of the node (see
`FINDING_cubeSmallNArb12ExHolds_session2.md` §4/§7). -/
def CubeCoreSet (v : E3 → ℝ) (μ : ℝ) (u : E3) : Prop :=
  ∀ j : Fin 3, |((Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ) • u).ofLp j|
      ≤ Work.BoseFixB1B.PBℓ v μ / 16

/-- **The two per-size rows of the target, restricted to a region `P` of `goodSet`** (with `P`
allowed to depend on `(μ,u)`).  This is the two items of `CubeSmallNArb12` verbatim. -/
def CubeRowsOn (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (Cn C ε₀ : ℝ) (P : ℝ → E3 → Prop) : Prop :=
  ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ u : E3, u ∈ goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ → P μ u →
      (∀ {n' : ℕ}, Cn * μ * Work.BoseFixB1B.PBBV v μ u ≤ (n' : ℝ) →
          (n' : ℝ) < (Cn + 1) * μ * Work.BoseFixB1B.PBBV v μ u →
          ∀ (Ψ : Submission.BoseGases.X n' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
            Work.BoseFixB1B.InBox v μ u Ψ →
            (1 / 18) * μ * ((n' : ℝ) / Work.BoseFixB1B.PBBV v μ u) * Work.BoseFixB1B.PBW h μ u
                * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
              ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)
      ∧ (∀ {n'' : ℕ}, (n'' : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1B.PBBV v μ u →
          ∀ (Ψ : Submission.BoseGases.X n'' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
            Work.BoseFixB1B.InBox v μ u Ψ →
            ((1 / 4) * (((n'' : ℝ) / Work.BoseFixB1B.PBBV v μ u) - μ) ^ 2 * Work.BoseFixB1B.PBW h μ u
                - (1 / 2) * μ ^ 2 * Work.BoseFixB1B.PBW h μ u
                - C * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ
                      * Work.BoseFixB1B.PBW h μ u + μ * (_root_.BoseGases.a v)))
                * (∫ x in Submission.BoseGases.abox n'' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
              ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)

/-- The two target rows **on the core** — `CubeRowsOn` at the core predicate. -/
def CubeRowsCore (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (Cn C ε₀ : ℝ) : Prop :=
  CubeRowsOn v h Cn C ε₀ (CubeCoreSet v)

/-- The two target rows **off the core** — the residual (RES) of
`FINDING_cubeSmallNArb12ExHolds_session2.md` §4. -/
def CubeRowsNonCore (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (Cn C ε₀ : ℝ) : Prop :=
  CubeRowsOn v h Cn C ε₀ (fun μ u => ¬ CubeCoreSet v μ u)

/-- **The split of the target into the two regions.**  The constants `(Cn, C, ε₀)` are shared:
item (1)'s window `[CnμV, (Cn+1)μV)` is *not* monotone in `Cn`, so the two halves cannot be taken
at different `Cn`. -/
theorem cubeSmallNArb12Ex_of_rows_split {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {Cn C ε₀ : ℝ}
    (hCn : 4 ≤ Cn) (hC : 0 ≤ C) (hε : 0 < ε₀)
    (hcore : CubeRowsCore v h Cn C ε₀) (hnc : CubeRowsNonCore v h Cn C ε₀) :
    CubeSmallNArb12Ex v h :=
  ⟨Cn, C, by linarith, hC, ε₀, hε, fun μ hAdm u hu => by
    by_cases hcase : CubeCoreSet v μ u
    · exact hcore μ hAdm u hu hcase
    · exact hnc μ hAdm u hu hcase⟩

end Work.BoseB1Cube
