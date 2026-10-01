/-
# ZeroFreeTables — HBTable7_proof

**Target.**  `Work.ZeroFreeTables.HBTable7`: Heath-Brown's Table 7 (1992) — for a real character
`χ₁` with real exceptional zero `ρ₁` (`IsMin1WideAt 10`, `χ₁² = 1`, `ρ₁.im = 0`, `λ₁ < 0.696`),
every zero `ρ` of a character `χ ∉ {χ₁, χ₁⁻¹}` in the working region (`IsZ χ ρ`, i.e.
`|ρ.im| ≤ 1`) satisfies `λ(ρ) ≥ p.2` for every row `p` of `tableR hbTable7` with `λ₁ ≤ p.1`.

**The proof is complete and axiom-clean** (`#print axioms` = `propext`, `Classical.choice`,
`Quot.sound`):

```
theorem HBTable7_proof : Work.ZeroFreeTables.HBTable7 :=
  HBTable7_of_count Work.ZeroDensity.LogFree.otherLamCountBounded
    Lam0Table7_of_wide HBTable7_rowData
```

## The three ingredients

1. **`Work.ZeroFreeTables.HBTable7_of_count`** (`HBTable7_of_count.lean`) — the assembly of HB's
   §6 + §8 argument: given

   * a *constant* bound `OtherLamCountBounded` for the zeros of the characters
     `χ ∉ {1, χ₁, χ₁⁻¹}` with `λ ≤ Λ ≤ 3` and `|Im| ≤ H ≤ 10 log q` (HB's Lemma 6.1, the counting
     content of Jutila's log-free family zero-density estimate); and
   * the `λ₀`-rows `Lam0Table7` for `χ₁` (HB's Tables 2, 3, 4) and the per-row certificates
     (`HBTable7_rowData`: `CertRow` for the third method, `CertRow85` for the five-term method),

   it produces the second number `(χ₂,ρ₂)` by the doubling pigeonhole (`second_pair_wide`), splits
   on `χ₂⁴ = 1` (HB Lemma 8.5, `ψ ≤ 3/8`) versus the generic case (HB Lemma 8.7, third method),
   and concludes with the row cores `row_contra_general_weak` / `row_contra_degenerate_weak`.

2. **`Work.ZeroDensity.LogFree.otherLamCountBounded`** (`LogFree/logFreeNPInstances.lean`) — the
   near-line count of ingredient 1, **unconditional**: it is obtained from
   `logFreeNP (3979/5000) 4`, i.e. `Σ'_{χ ≠ 1} N(σ,T,χ) ≤ C (qT)^{4(1-σ)}` on `σ ≥ 3979/5000`,
   which the `LogFree` chapter proves through the Halász duality count
   `dualityCountOfParamsCF` (the eight axiom-clean interfaces of `LogFree/GramProps.lean`:
   detector `L1`, Graham mean values `L2`, Gram kernel `L3`, damped pole large sieve `L4`) and the
   box upgrade `boxUpgradeOfParams`, followed by
   `Work.ZeroFreeTables.OtherLamCountBounded_of_logFreeNP` (which converts any log-free
   `(c+ε)`-form non-principal estimate into a *constant* λ-count, using the *non-principal*
   counting lemma `otherLamCount_le_zeroCountSumNP` — no principal-character input anywhere).

3. **`Work.ZeroFreeTables.Lam0Table7_of_wide`** — the `χ₁`-rows, unconditional.

## Notes for whoever continues

* This file used to run through `FamilyZeroDensityJutilaNP` (= the `sorry` node
  `Work.ZeroDensity.Jutila.jutilaNonPrincipal`).  That is no longer necessary: the `LogFree`
  chapter's Halász route is complete, so the present route is shorter and self-contained.
* A workspace hazard had to be worked around: `Density4/SsmSetup.lean` and
  `Density4/ShiftedDefs.lean` both declare `Work.LinnikAreas.Density4.Phi`, so no module can
  import the detector chain (needed by `GramCross`, `DetectorBound`, `DetectorTruncation`,
  `GramSame`) together with the Selberg-`theta` chain (needed by the old proofs of `MassBound` and
  `PoleResidueBound`).  The two latter props were therefore re-derived in `ShiftedDefs`-free mirror
  trees, `Submission/Work/HB7CF2/` (`massBoundCF`) and `Submission/Work/HB7CF/`
  (`poleResidueBoundCF`); the chapter's own assembly `dualityCountOfParamsCF` consumes those.  Full
  write-up: `Submission/Work/ZeroFreeTables/STATUS_HBTable7_NAME_CLASH.md`.
* Independent unconditional partial results, kept for reference:
  `Work.ZeroFreeTables.HBTable7_ord4` (every bad zero with `χ⁴ = 1` has `λ ≥ 79/100`),
  `HBTable7_row745`, `HBTable7_row79`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.EngineRoadmap
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.HB4_1
import Submission.Work.ZeroFreeTables.HBTable7_of_count
import Submission.Work.ZeroFreeTables.HBTable7_rowData
import Submission.Work.ZeroFreeTables.Lam0Table7_of_wide
import Submission.Work.ZeroDensity.LogFree.logFreeNPInstances

namespace Work.ZeroFreeTables

/-- **Heath-Brown's Table 7** (`Work.ZeroFreeTables.HBTable7`), from the chapter's unconditional
near-line count `Work.ZeroDensity.LogFree.otherLamCountBounded`, the `χ₁`-rows
`Lam0Table7_of_wide` and the per-row certificates `HBTable7_rowData`. -/
theorem HBTable7_proof : Work.ZeroFreeTables.HBTable7 :=
  HBTable7_of_count Work.ZeroDensity.LogFree.otherLamCountBounded
    Lam0Table7_of_wide HBTable7_rowData

end Work.ZeroFreeTables
