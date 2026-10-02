import Mathlib
import Submission.Work.LinnikContract.Areas
import Submission.Work.SiegelAbsorb.area6Siegel

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option linter.unusedVariables false

/-- **AREA 6** of the frozen Linnik contract: the Siegel-zero case of Linnik's theorem.

**The state of the proof (session 3, see `NOTES_area6_route.md` §8).**  Everything below the
*one* deep input is proved, in this workspace, and the reduction is machine-checked by
`Work.LinnikAreas.area6_of_BGTZ` (`Submission/Work/LinnikAreas/area6BGTZ.lean`):

`area6_of_BGTZ : FamDensityEpsRange (4/5) 1 2 → FamDensityEpsRange 0 (4/5) (12/5) →
                  RepulsionWith (7/16) → Siegel.RepulsionBGTZ → Work.LinnikContract.Area6`

where the first two hypotheses are Jutila's and Huxley's log-free family zero-density estimates
(the fleet's `ZeroDensity/Jutila`, `ZeroDensity/Huxley` cores), `RepulsionWith (7/16)` is the
working-region Deuring--Heilbronn repulsion (the fleet's `DhRepel`/`OtherCharRepel`), and the
single deep input is `Siegel.RepulsionBGTZ` (`Submission/Work/LinnikAreas/BGTZ.lean`): the
Deuring--Heilbronn repulsion **at all heights**,

`λ(ρ) ≥ (log(1/λ₁) - log(24(c₁ + c₂·log(5+|Im ρ|)/𝓛))) / (c₁ + c₂·log(5+|Im ρ|)/𝓛)`,
`c₁ = 4/3+ε`, `c₂ = 2/3+ε`,

a true, explicit, published theorem (Benli--Goel--Twiss--Zaman, *Explicit Deuring--Heilbronn
phenomenon for Dirichlet L-functions*, arXiv:2410.06082, Cor. 1.2; see §8.1 for the effective
choice `ε = 1/2`).

The pieces of the reduction that are *proved* in the workspace:

| input of the assembly | proved as |
|---|---|
| `SimpleInput` (Landau simplicity) | `siegelSimpleInput` |
| summability of the kernel-weighted zero sum | `siegelZeroWeightSummable` |
| `PairDensityInput` (working region `\|Im ρ\| ≤ 1`) | `Work.ZeroDensity.pairDensityInput_of_cores` (Jutila + Huxley + repulsion) |
| `restLowZeroSum ≤ Cλ₁^{1+δ}` | `siegelRestLow` |
| `restHighZeroSum ≤ C𝓛^{-3/2}` (`λ₁`-free) | `Work.LinnikAreas.RestHighFree` |
| `restHighZeroSum ≤ Cλ₁𝓛^{-3/2}` for `λ₁ ≤ 1/10` | `Work.LinnikAreas.RestHighBGTZ` (from `RepulsionBGTZ`) |
| the `hHigh` split at `λ₁ = 1/10` | `Work.LinnikAreas.RestHighCombine` |
| `LogFreeFamHeight (5/2) (3/2)` | `Work.ZeroDensity.Assembly.logFreeFamHeight_of_cores` |
| `ExpansionInput R` for all `R ≥ 1` (HB §13) | `siegelExpansion` |
| the box part, the far splitting, the closing arithmetic, the prime extraction | `boxSum_eq_exceptional`, `signedBoxSumAll_le_exceptional`, `farZeroSum_le_restLow_add_restHigh`, `siegel_close_arith`, `prime_of_classSum_pos`, `lamOf_lower_bound` |

**What is *not* used any more.**  The earlier route fed the two rest-bounds through the
`λ₁`-saving estimates `PairDensityInput`/`PairDensityHeightInput` (`Siegel.DHLogFreeHeightCoupled`),
and in particular through `siegelRestHighCoupled`.  The height-direction estimate in its
unrestricted form is **not a theorem** (and is false at extreme heights); see §8 of the notes.
The only zero-density inputs of the new route are the *λ₁-free* Jutila/Huxley cores.  The
remaining gap is therefore exactly the formalization of `Siegel.RepulsionBGTZ`.

**UPDATE (session 9).**  That gap is *closed*: `Siegel.RepulsionBGTZ`'s role is played by the
corrected BGTZ detector assembly, which is complete (no incomplete cases) and axiom-clean —

* `Work.LinnikAreas.BGTZ.E.BGTZRepulsionGen_E :
   ∃ cZ > 0, BGTZ.ZFRInputL cZ ∧ BGTZ.RepulsionGenC (11/5) (11/10) (max (1000/cZ) 1000)`
  (the Deuring--Heilbronn repulsion at all heights, `Submission/Work/LinnikAreas/BGTZ/E/`).

AREA 6 is accordingly machine-checked, with `#print axioms = [propext, Classical.choice,
Quot.sound]`, as

* `Work.LinnikAreas.area6_of_cores_E` (`LinnikAreas/area6Cores.lean`):
  `FamDensityEpsRange (4/5) 1 2 → FamDensityEpsRange 0 (4/5) (12/5) → ZeroFreeCert → Area6`;
* `Work.LinnikAreas.area6_of_cores_E_np` (`LinnikAreas/area6CoresNp.lean`): the *sharper*
  interface, with the Jutila input replaced by its non-principal form
  (`LinnikAreas/logFreeFamHeightOfNonPrincipal`, `LinnikAreas/logFreeFamHalfOfNonPrincipal`).
  This matters because `famCount` sums over *all* characters mod `q` (the principal one
  included), so `FamDensityEpsRange (4/5) 1 2` implies the density hypothesis for `ζ` on
  `σ ≥ 4/5` and is *stronger* than Jutila's theorem; see
  `Submission/Work/LinnikAreas/NOTE_jutilaInput_principalChar.md`.

**UPDATE (session 10): AREA 3 is eliminated.**  The route above consumes the frozen AREA 3
certificate `Work.LinnikContract.ZeroFreeCert` in exactly one place: the *uncapped* repulsion
`Work.ZeroDensity.RepulsionWith (7/16)` produced by `repulsionWith_7_16`
(`RepulsionWith_of_ZeroFreeCert`), which needs the zero-free tables of AREA 3 precisely for the
range `λ₁ ∈ [lamS, 1/2]`.  AREA 6 never needs that range:

* `LinnikAreas/RepulsionCapDefs.lean` defines the *capped* repulsion `RepulsionWithCap ε₀ c`
  (`λ(β₁) ≤ ε₀` instead of `≤ 1/2`);
* `LinnikAreas/RepulsionCap.lean` proves `∃ ε₀ > 0, RepulsionWithCap ε₀ (7/16)` from the proved
  BGTZ repulsion `BGTZRepulsionGen`, the proved unconditional zero-free region
  `BGTZ.ZFRInput` (`BGTZ/ZFRInput_exists.lean`) and Siegel's uniform lower bound `lamOfEps200`
  — this is the step that replaces AREA 3 (the capped datum is automatically the *minimal* pair,
  which is all the BGTZ repulsion needs);
* `LinnikAreas/PairDensityCap.lean` derives the *uncapped* `Siegel.PairDensityInput` from the
  capped repulsion and the log-free family count `LogFreeFamHalf (5/2)` (for `λ₁ ≥ ε₀` the
  repulsion is not needed at all: the family count alone suffices);
* `LinnikAreas/siegelRestLowCap.lean` and `LinnikAreas/boxSumBoundCap.lean` are the two
  `λ₁`-capped consumers (`siegelRestLow`, `boxSumBound_of_inputs` with the repulsion hypothesis
  capped at `ε₀`; `BoxSumBound` already has an internal threshold `lamS ≤ 1/100`, which is only
  shrunk by `min · ε₀`).

The resulting interface, `LinnikAreas/area6CapChain.lean`,

* `Work.LinnikAreas.area6_of_cores_cap : BGTZRepulsionGen → JutilaNonPrincipal →
   FamDensityEpsRange 0 (4/5) (12/5) → Area6`

is complete (no incomplete cases) with `#print axioms = [propext, Classical.choice, Quot.sound]`,
and since `Work.LinnikAreas.BGTZ.E.BGTZRepulsionGen_E` is *proved*, the frozen target below
reduces to exactly **two** fleet cores:

| input | fleet module |
|---|---|
| Jutila, non-principal form (`Work.ZeroDensity.Jutila.jutilaNonPrincipal`) | `ZeroDensity/Jutila` |
| Huxley `12/5` (`FamDensityEpsRange 0 (4/5) (12/5)`) | `ZeroDensity/Huxley` |

**Wiring the target.**  `area6CapChain` imports *this* file if it is built on `area6.lean`, so the
wiring has been split into cycle-free modules (none of which imports `area6`), and this file
imports them:

* `LinnikAreas/area6Box.lean` — the box part of HB §§13--14 (`norm_char_apply_eq_one` …
  `siegel_close_arith`), extracted from this file;
* `LinnikAreas/area6Top.lean` — the top-level argument (`vmClassSum_eq_prime_add_nonPrime`,
  `prime_of_classSum_pos`, `Siegel.area6_of`), extracted from this file;
* `LinnikAreas/RepulsionCap.lean` + `…/RepulsionCapDefs.lean` — the capped repulsion
  `RepulsionWithCap ε₀ (7/16)` and its proof from the local statement `BGTZRepulsionGenE`;
* `LinnikAreas/PairDensityCap.lean` — `Siegel.PairDensityInput` from the capped repulsion;
* `LinnikAreas/siegelRestLowCap.lean`, `…/boxSumCap.lean` — the two capped consumers;
* `LinnikAreas/BGTZRepE.lean` — `BGTZRepulsionGenE_proved` (the BGTZ repulsion at all heights,
  in the local statement, so that no import of `area6Chain` is needed);
* `LinnikAreas/area6CapChain.lean` — the assembly
  `area6_of_cores_cap : BGTZRepulsionGenE → Jutila → Huxley → Area6`.

The frozen target below is therefore **one line from closure**: its body is
`area6_of_capped_cores Work.ZeroDensity.Jutila.jutilaNonPrincipal
Work.ZeroDensity.Huxley.huxleyTwelveFifths`, with `area6_of_capped_cores` (`area6_of_cores_cap BGTZRepulsionGenE_proved ·  ·`, proved in this
file, axiom-clean) as above.  See `Submission/Work/LinnikAreas/NOTE_area3_elimination.md`.

(Historical note for whoever wires the remaining two cores up: `ZeroDensity/Huxley/
huxleyTwelveFifths.lean` is *stale-by-content* in the workspace — its `lake build` requires
rebuilding `ZeroDensity/Montgomery/montgomerySharp`, blocked by the never-compiled
`ZeroDensity/Ingham/hiCaseF4BoundFile.lean` and friends — see
`Submission/Work/LinnikAreas/BGTZ/NOTES_workspace_blockers.md`.)

**UPDATE (session 11): the two cores are replaced by one, and alternatively by a different pair.**

*The exponent analysis.*  Everything downstream of the two family counts in AREA 6 consumes them
at the *fixed* exponent `5/2` (`Work.ZeroDensity.LogFreeFamHalf (5/2)`,
`Work.ZeroDensity.LogFreeFamHeight (5/2) (3/2)`):

* `PairDensityCap`'s Deuring--Heilbronn matching needs `c₃ + 1/c_r < 49/10` with the repulsion
  constant `c_r = 7/16`, i.e. `c₃ < 49/10 - 16/7 = 2.614…`, and `5/2 + 16/7 = 67/14 = 4.785…`;
* `RestHighFree`/`RestHighBGTZGenC` need `c₃ < 49/10` and `c₃' < 2`.

Consequently **any** non-principal log-free estimate with q-coefficient `≤ 5/2` on a range
`[σ₀,1]` with `σ₀ < 4/5` — glued with Huxley's all-character `12/5` on `σ ≤ 4/5` (coefficient
`12/5 + 1/10 = 5/2` at `ε = 1/10`, *exactly* the requirement) — closes AREA 6 verbatim; and so
does any pair of inputs that supplies the coefficient `5/2` on the whole range `σ ∈ [0,1]`.

*Route A (the lead's unified route, `Submission/Work/ZeroDensity/JUTILA_UNIFIED_LEAD.md`).*
`LinnikAreas/logFreeFamOfTwelveFifths.lean` derives `LogFreeFamHalf (5/2)` and
`LogFreeFamHeight (5/2) (3/2)` from

* `Work.ZeroDensity.LogFree.NonPrincipalTwelveFifths` — `Σ'_{χ≠1} N(σ,T,χ) ≤ C(qT)^{(12/5+ε)(1-σ)}`
  on `σ ≥ 3979/5000 = 0.7958`, the node `logFreeNP (93/100) (12/5)` glued with Huxley's
  non-principal bound widened to `σ ≤ 93/100` — at `ε = 1/10` (exponent `5/2`, and `3979/5000 < 4/5`
  so the whole near-line range is covered); **plus**
* Huxley's `Work.ZeroDensity.FamDensityEpsRange 0 (4/5) (12/5)` (unchanged; `ε = 1/10`).

`LinnikAreas/area6OfTwelveFifths.lean` then assembles

```
Work.LinnikAreas.area6_of_nonPrincipalTwelveFifths :
  NonPrincipalTwelveFifths → FamDensityEpsRange 0 (4/5) (12/5) → Area6
```

(reusing `PairDensityCap`, `RestHighFree`, `RestHighBGTZGenC`, `siegelRestLowCap`, `boxSumCap`
verbatim), so the frozen target closes from those two Propositions by
`area6_of_nonPrincipalTwelveFifths Work.ZeroDensity.LogFree.nonPrincipalTwelveFifths
Work.ZeroDensity.Huxley.huxleyTwelveFifths`.

*Route B (no Huxley).*  `LinnikAreas/logFreeFamOfMontgomery.lean` observes that if the *target*
exponent is raised from `5/2` to `261/100 = 2.61` — which is still admissible in both consumers,
since `261/100 < 49/10` and `261/100 + 16/7 = 3427/700 < 49/10` — then **Montgomery's sharp
large-sieve estimate replaces Huxley**: `3(1-σ)/(2-σ) ≤ 5/2` with equality only at `σ = 4/5`, so
at `σ = 4/5` Montgomery's `ε = 1/100` costs `0.01` of the `0.11·(1/5) = 0.022` of available
exponent budget, leaving room for its logarithmic power; Jutila's range `σ ≥ 4/5` is covered by
the near-line node `logFreeNP (93/100) (12/5)` at `σ ≥ 93/100` *and* by Montgomery (with the
`2.61` budget, i.e. `ε ≤ (1-σ)(2.61 - 3/(2-σ)) ≥ 0.11(1-σ)`) on `4/5 ≤ σ ≤ 0.93`.  The resulting
interface is

```
Work.LinnikAreas.area6_of_cores_v2 :
  BGTZRepulsionGenE → JutilaNP → MontgomerySharp (1/1000) → Area6
Work.LinnikAreas.area6_of_cores_v2_huxley :
  BGTZRepulsionGenE → JutilaNP → FamDensityEpsRange 0 (4/5) (12/5) → Area6
```

(`LinnikAreas/area6OfCores2.lean`), together with the `∀ B > 0` form
`area6_of_cores_v2_allB`, i.e. AREA 6 closes from the chapter target
`Work.ZeroDensity.Montgomery.montgomerySharp` **and nothing else** besides the non-principal
input.  Route B needs the two far-height lemmas at the exponent `261/100`
(`LinnikAreas/RestHighFreeGen`, `LinnikAreas/BGTZ/RestHighBGTZGenCGen`), which is where the
`5/2`-hardcoding of `RestHighFree`/`RestHighBGTZGenC` is lifted mechanically: every constraint in
those files is `c₃ < 49/10` (used only as `exp(c₃ - 49/10) < 1`) resp. `c₃' < 2`, and the numeric
certificates `exp(5/2) ≤ 27`, `1 - exp(-12/5) ≥ 1/2` remain true with `261/100` and `229/100`.

**UPDATE (session 12) — AREA 6 is CLOSED, and none of the routes above is used.**  The frozen
target below is now the *proved* theorem `Work.SiegelAbsorb.area6_siegelRoute`, i.e. **Siegel
absorption** (`LinnikAreas/AREA6_ROUTE_LEAD.md`, `Submission/Work/SiegelAbsorb/`): the exceptional
zero's own lower bound `λ₁ ≫ q^{-1/200}` (Siegel, already used by the proved BGTZ repulsion)
replaces every sharp density estimate on `σ < 93/100`, so neither Jutila's non-principal theorem
nor Huxley's `12/5` nor Montgomery's sharp large-sieve estimate is needed — in particular the
frozen target no longer depends on any statement of the `ZeroDensity` chapters that still contains
an incomplete case.  The inputs, all theorems of this workspace with
`#print axioms = [propext, Classical.choice, Quot.sound]`:

* the capped Deuring--Heilbronn repulsion `repulsionWithCap_7_16`, fed by the proved BGTZ
  repulsion at all heights (`BGTZRepulsionGenE_proved`);
* the log-free non-principal estimate `logFreeNP (3/4) (9/2)` (`SiegelAbsorb/logFreeNP34.lean`),
  the near-line count at coefficient `5/2` on `σ ≥ 93/100` (`SiegelAbsorb/famCount_nearLine.lean`)
  and the crude count at coefficient `9/2` on all of `[0,1]`
  (`SiegelAbsorb/famCount_crude.lean`);
* Siegel's lower bound in exponential form (`SiegelAbsorb/lamOf_ge_exp_neg.lean`), used twice: with
  `a = 21/1000` to kill the crude count on `λ > (7/100)𝓛`, and with `a = 7/250` in the far-zero
  branch;
* the truncated two-exponential matching (`SiegelAbsorb/dhCapTrunc.lean`, exponent
  `67/14 < 24/5`), the `λ₁`-saving count `Siegel.PairDensityInput` with `c = 24/5`
  (`SiegelAbsorb/pairDensityInput_siegel.lean`), the two-regime per-window mass
  (`SiegelAbsorb/highMassRep2.lean`) and its conversion into `RestHighBGTZSpec (-3/2)`
  (`SiegelAbsorb/RestHighBGTZSiegel_of_window.lean`, `SiegelAbsorb/area6Siegel.lean`);
* the unchanged AREA 6 assembly `siegelRestLowCap` → `boxSumCap` → `Siegel.area6_of`
  (`SiegelAbsorb/area6SiegelOfInputs.lean`). -/
theorem area6 : Work.LinnikContract.Area6 :=
  Work.SiegelAbsorb.area6_siegelRoute


end
end Work.LinnikAreas
