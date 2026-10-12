import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.PerBoxNames
import Submission.Work.BoseFixB1B.chiCubeBump
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.chiCubeSlots` — the **bumped vocabulary slots** for queue item (2)

Holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.  Decision (B) of the lead; the bump is
`chiCubeBump.lean` (rc=0, `sorry`-free), item (1) of the queue was the kernel
(`wSmall1PairCube`).

## What this module is for

Queue item (2) is: re-derive the PROVED port `Work.BoseFixB1B.SlidingBogPort`
(`slidingBogPortProved.lean`, 715 lines) with the bump swapped from `chiSmallB` to `chiCubeB`.
Counted occurrences in that file (`grep -o … | sort | uniq -c`):

    chiSmallB       20
    bSpectralCube    6
    chiMass          7
    wSmall1Pair      2

The 20 `chiSmallB` occurrences are *inside lemmas about the window itself* (support, smoothness,
`L²`-mass, decay) — and those are exactly what `chiCubeBump.lean` now provides in bumped form
(`chiCubeB_contDiff`, `chiCubeB_le_one`, `chiCubeB_eq_zero_of_*`, …).  The three remaining
occurrences are *vocabulary* sites, and this module supplies the two that are not already done:

| site | status |
|---|---|
| `wSmall1Pair` (2×) | **DONE** — `Work.BoseFixB1B.wSmall1PairCube` + `…_kernel` (`chiCubeBump.lean`, item (1)) |
| `bSpectralCube` (6×) | **here** — `Work.BoseFixB1B.bSpectralCubeB`, the definitional `chiSmallB ↦ chiCubeB` swap of `Work.BoseFixB1S.bSpectralCube` |
| `chiMass` (7×) | **here** — `Work.SmallBoxSliding.chiMass M ℓ d u = ∫ x, (chiSmallB M ℓ d u x)²` (`Sliding.lean:60`, a *plain* `∫χ²`; the identity `chiMass_eq_scaled` is a derived change-of-variables *lemma*, not the definition), so its twin `chiCubeMassB` is likewise a definitional name swap |

So queue item (2) is now: swap the three vocabulary sites, and re-issue the 20 window lemmas against
`chiCubeBump.lean`'s bumped versions.  Nothing else in the port's 715 lines refers to the bump.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The bumped spectral slot**: `Work.BoseFixB1S.bSpectralCube` with its window `chiSmallB M ℓ d u`
replaced by `chiCubeB M ℓ d u` and nothing else changed (the `M` is carried through
`Work.BoseFixB1.bM v μ`, exactly as in `bSpectralCube`, so the swap is a name substitution at each
of the 6 use sites). -/
noncomputable def bSpectralCubeB (v : E3 → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  Work.UBBInputs8.tBwordKinInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
    (Work.BoseFixB1.bV v μ u)
    (chiCubeB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
    (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ


/-- **The bumped χ-mass**: `Work.SmallBoxSliding.chiMass` with `chiSmallB ↦ chiCubeB` — a
definitional name swap (both are *literally* `∫ x, (χ x)²`; cf. `Sliding.lean:60` and the `rfl`
lemma `chiMass_def` there).  This is the third and last vocabulary site of the port's bump swap. -/
noncomputable def chiCubeMassB (M : ℕ) (ℓ d : ℝ) (u : E3) : ℝ :=
  ∫ x : E3, (chiCubeB M ℓ d u x) ^ 2

@[simp] lemma chiCubeMassB_def (M : ℕ) (ℓ d : ℝ) (u : E3) :
    chiCubeMassB M ℓ d u = ∫ x : E3, (chiCubeB M ℓ d u x) ^ 2 := rfl

lemma chiCubeMassB_nonneg (M : ℕ) (ℓ d : ℝ) (u : E3) : 0 ≤ chiCubeMassB M ℓ d u :=
  integral_nonneg (fun x => sq_nonneg _)


/-- **The bumped pairing word**: `Work.BoseFixB1.bA2` with its kernel `wSmall1Pair` replaced by the
matched-window twin `wSmall1PairCube` — a definitional name swap (`bA2` is literally
`boxA2 (bSide v μ) (bV v μ u) (bA v μ u) (wSmall1Pair h (bM v μ) … u) Φ`, `PerBoxNames.lean`). -/
noncomputable def bA2B {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  Work.BoseFixB1.boxA2 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bV v μ u)
    (Work.BoseFixB1.bA v μ u) (wSmall1PairCube h (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u) Φ

/-- **FS `lm:appbogolubov` at the sliding box, matched-window (smooth cube bump) rendering**:
`Work.BoseFixB1B.SlidingBogPort` (`perBoxFTotalInterfaces.lean:83`, PROVED as
`slidingBogPort_proved`) with its three vocabulary sites swapped to the bumped twins
(`chiMass ↦ chiCubeMassB`, `bSpectralCube ↦ bSpectralCubeB`, `bA2 ↦ bA2B`) and nothing else changed.

Statement only (`def : Prop`), so this module stays `sorry`-free.  It is written **before** the
715-line copy precisely because it fixes what that rewrite must prove. -/
def SlidingBogPortB (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ η C : ℝ, 0 < ε₀ ∧ 0 ≤ η ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        0 ≤ (1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
              * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
              * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
              * chiCubeMassB (Work.BoseFixB1.bM v μ)
                  (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
            + bSpectralCubeB v μ (Φ : Submission.BoseGases.X n → ℝ) u
            + bA2B h μ (Φ : Submission.BoseGases.X n → ℝ) u
            + C * (_root_.BoseGases.a v)
                * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u
            + C * (_root_.BoseGases.a v) * μ
                * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)

end Work.BoseFixB1B
