import ChallengeDeps
import Submission.Work.BoseFixB1.AprioriPieces
import Submission.Work.BoseFixB1S.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.lowProviderDefs` — the *correct* residual vocabulary of
# `Work.BoseFixB1B.lowCountBound`

Written by the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

## Why these definitions exist

The frozen node `Work.BoseFixB1B.lowCountBound` is proved in
`Submission/Work/BoseFixB1B/lowCountBound.lean` from `Work.BoseFixB1.AprioriHLambdaIneq`
(FS `eq:aprioriRn+`), which in turn is produced there from FS's *collected* per-box bound
`Work.BoseFixB1.smallBoxCollectedC_holds`.  That chain is **vacuous**: the per-box provider it
consumes is `Work.BoseFixB1.PerBoxF` *without* the low-state restriction, and that statement is
**FALSE** (three independent refutations of its flat branch, with the Jastrow/correlation-hole
family; see `Submission/Work/BoseFixB1B/FINDING_perBoxF_refuted_lowB_survives.md`, written by the
holder of `Submission/Work/BoseFixB1B/PerBoxSmoothHolds.lean`, together with
`FINDING_flatBranch_refuted_ledger.md` and `FINDING_flatBranchAlt.md`).

The *true* statement — the one FS actually use (`thm:smallbox` is applied only to low states
`eq:aprioriPsi`) — is the **low-state restricted** provider, and it is precisely what the corpus's
branch assembly `Work.BoseFixB1B.perBoxF_of_branches` produces from the thin, gap and flat arms.
The present module fixes the vocabulary of the corrected chain:

* `PerBoxFLow` — FS `thm:smallbox` at the sliding box on the good set, for **low** states, with a
  single triple of constants serving every threshold `J ≤ K_B³` (the shape produced by
  `perBoxF_of_branches` once the flat arm lands);
* `OffGoodCrudeLow` — FS `eq:badset`'s crude per-box bound on the complement of the good set, for
  low states (the shape of `Work.BoseFixB1S.BandPerBoxCrudeB1` on the band);
* `CollectedLow` — the corrected FS `thm:smallbox`-collected bound: the mean-field background
  `4πμ²(a v)ℓ³` is kept, and the bound is required only for states with **positive** box norm
  (`0 < normB`), which is exactly the class the counting consequence needs (FS's small-box states
  carry mass on the box; the `normB = 0` degeneracy of `Work.BoseKinLoc.BoxState` — smooth states
  whose mass sits *off* the box — is *not* covered, and does not need to be, because
  `Work.BoseFixB1.WindowBridge`, the consumer of this bound, is itself stated for `0 < normB`);
* `AprioriHLambdaIneqLow` — FS `eq:aprioriRn+` for the same restricted class.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **FS `thm:smallbox` at the sliding box `B(u)`, `F`-weighted, for low states, uniformly in
`J`.**  This is `Work.BoseFixB1.PerBoxF` on `goodSet` for the states admitted by FS's a-priori
hypothesis `eq:aprioriPsi`; it is the conclusion of
`Work.BoseFixB1B.perBoxF_of_branches` (thin + gap + flat arms) once the flat arm lands. -/
def PerBoxFLow (v : E3 → ℝ) (h : ScatSol v) (R J : ℝ) (c₁ C : ℝ) (ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε₀ μ →
    J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      0 < normB v μ n (Φ : X n → ℝ) →
      IsLowB v h J μ n Φ →
      ∀ u : E3,
        u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        PerBoxF v h R c₁ C μ n Φ u

/-- **FS `eq:badset`, the crude per-box bound off the good set, for low states.**  The shape of
`Work.BoseFixB1S.BandPerBoxCrudeB1`'s target (there stated on `bandSet`; here on all of
`goodSetᶜ`, where the far set is trivial since `sbWord = sbKin ≥ 0` there). -/
def OffGoodCrudeLow (v : E3 → ℝ) (h : ScatSol v) (J : ℝ) (C : ℝ) (ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε₀ μ →
    J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      0 < normB v μ n (Φ : X n → ℝ) →
      IsLowB v h J μ n Φ →
      ∀ u : E3,
        u ∉ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        -(C * (μ ^ 2 * (a v)
                * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
              + μ * (a v)))
            * normB v μ n (Φ : X n → ℝ)
          ≤ sbWord h μ u (Φ : X n → ℝ)

/-- **FS's collected per-box bound (`thm:smallbox` summed over the sliding boxes), restricted to
states with positive box norm and uniform in `J`.**  The conclusion is character-for-character the
one consumed by the a-priori chapter's arithmetic (with `0 < normB` made explicit and the
`J`-quantifier brought inside the existential, so that one triple of constants serves all `J`). -/
def CollectedLow (v : E3 → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ ε₀ C c : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < c ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        0 < normB v μ n (Φ : X n → ℝ) →
        IsLowB v h J μ n Φ →
          0 ≤ RPsi v h μ (Φ : X n → ℝ) ∧
          c * RPsi v h μ (Φ : X n → ℝ)
            ≤ (∫ u : E3, sbWord h μ u (Φ : X n → ℝ))
              + 4 * Real.pi * μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
                  * (1 + C * (paramsAt μ (a v)).KB ^ 3
                      * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                  * normB v μ n (Φ : X n → ℝ)

/-- **FS `eq:aprioriRn+` for the low-state class**: the a-priori bounds on `R_Ψ` and on the
excited count `n₊`, uniformly in the threshold `J ≤ K_B³`, for box states of positive norm. -/
def AprioriHLambdaIneqLow (v : E3 → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ C ε₀ : ℝ, 1 ≤ C ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      0 < normB v μ n (Φ : X n → ℝ) →
      IsLowB v h J μ n Φ →
        0 ≤ RPsi v h μ (Φ : X n → ℝ) ∧
        RPsi v h μ (Φ : X n → ℝ) ≤ C * μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
              * normB v μ n (Φ : X n → ℝ) ∧
        ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
              * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          ≤ C * μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
              * normB v μ n (Φ : X n → ℝ)

end Work.BoseFixB1B
