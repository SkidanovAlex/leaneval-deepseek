import ChallengeDeps
import Submission.Work.BoseFixB1.perBoxMF_cases
import Submission.Work.BoseFixB1S.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.lowMaxDefs` — the `J`-FREE low-state restriction

Written by the holder of `Submission/Work/BoseFixB1B/lowState_count_leAlt.lean`.

## Why this file exists

The count cap (my target) needs the a-priori interface `Work.BoseFixB1S.AprioriUnif v h`, which is
`J`-**uniform** (`∀ J ≤ K_B³` with ONE triple of constants).  The corpus's `J`-uniform chain

    `CollectedUnif`  ⟸  `Work.BoseFixB1.PerBoxF` on the good set (for **all** states) + `hW` + `hT`

(`Work.BoseFixB1S.collectedUnifOfPerBox`, PROVED) is **unsound**: its per-box provider
`PerBoxF` *without* the low-state restriction is **FALSE** (the Jastrow/correlation-hole family;
see `Submission/Work/BoseFixB1B/FINDING_perBoxF_refuted_lowB_survives.md`).  The *sound*
restricted chains on disk (`lowProviderDefs`/`lowProviderChain`/`lowProviderFinal`) are
`J`-**indexed**: their residual `Work.BoseFixB1B.FlatBranchLow v h R J` is stated for a *fixed*
threshold `J`, and the constants it returns may depend on `J`, so they cannot be composed into the
`∀ J` form (which is exactly what the `J`-uniform count cap needs).

## The fix: a `J`-free restriction

`IsLowB` is *monotone* in the threshold (`Work.BoseFixB1S.isLowB_mono`: raising `J` enlarges the
low class), so the class of states that are low at *some* `J ≤ K_B³(μ)` is exactly the class

    `LowMax v h μ n Φ  :=  IsLowB v h (K_B³(μ)) μ n Φ`      (the threshold at `J = K_B³(μ)`),

and this predicate contains **no free `J`**.  Hence every statement restricted by `LowMax` is
`J`-free, the whole chain can be run without ever mentioning a threshold, and the `J`-uniform
conclusion comes for free.

`LowMax` is the *weakest* adequate restriction: any restriction whose class must contain all
`IsLowB J` classes (`J ≤ K_B³`) contains the `K_B³` class, and `LowMax` is exactly that class.
So the residual obtained this way is *no harder* than the existing `J`-indexed residuals (its
proof is FS's own, which never mentions `J`; the only place `J` enters the corpus's per-box
proofs is through `J√(μ(a v)³) ≤ (μ(a v)³)^{287/646} ≤ 1`).

## Contents

* `LowMax` — the predicate;
* `LowMax_of_isLowB` — `IsLowB J` + `J ≤ K_B³` ⟹ `LowMax` (the monotonicity step used by every
  consumer);
* `LowMax_of_isLowB_lhyC` — the same with `lhyC ≤ J ≤ K_B³` and the `Adm`-free diluteness
  side conditions, in the exact form the chain needs;
* the two `J`-free restricted per-box interfaces (`PerBoxFLowMax`, `FlatBranchLowMax`) used by the
  ported chain modules.
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

/-- **The `J`-free low-state restriction**: `IsLowB` at the maximal threshold `K_B³(μ)` of the
count window.  A state is low at *some* `J ≤ K_B³(μ)` iff it is `LowMax`
(`LowMax_of_isLowB`). -/
def LowMax (v : E3 → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) : Prop :=
  IsLowB v h ((paramsAt μ (a v)).KB ^ 3) μ n Φ

/-- **The monotonicity step**: a state low at a threshold `J ≤ K_B³(μ)` is `LowMax`. -/
theorem LowMax_of_isLowB {v : E3 → ℝ} {h : ScatSol v} {J μ : ℝ} {n : ℕ} {Φ : X n → ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hℓ : 0 ≤ sideAt μ (_root_.BoseGases.a v))
    (hJJ : J ≤ (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3)
    (hlow : IsLowB v h J μ n Φ) : LowMax v h μ n Φ :=
  Work.BoseFixB1S.isLowB_mono hav hℓ hJJ hlow

/-- The `Adm`-form of the monotonicity step: for `μ` admissible at a diluteness threshold `ε₀`,
`J ≤ K_B³(μ)` gives `LowMax` from `IsLowB J`. -/
theorem LowMax_of_adm {v : E3 → ℝ} {h : ScatSol v} {ε₀ J μ : ℝ} {n : ℕ} {Φ : X n → ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hAdm : Adm v ε₀ μ)
    (hJJ : J ≤ (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3)
    (hlow : IsLowB v h J μ n Φ) : LowMax v h μ n Φ :=
  LowMax_of_isLowB hav (le_of_lt (adm_ell_pos hAdm)) hJJ hlow

/-- **The `J`-free restricted per-box interface** (FS `thm:smallbox` at the sliding box on the
good set, for `LowMax` states of positive box norm): the *sound* replacement of the (false)
`PerBoxF`-for-all-states hypothesis of `Work.BoseFixB1S.collectedUnifOfPerBox`. -/
def PerBoxFLowMax (v : E3 → ℝ) (h : ScatSol v) (R c₁ C ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (_root_.BoseGases.a v))),
      0 < normB v μ n (Φ : X n → ℝ) →
      LowMax v h μ n (Φ : X n → ℝ) →
      ∀ u : E3,
        u ∈ goodSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ →
        PerBoxF v h R c₁ C μ n Φ u

/-- **The `J`-free flat-branch residual**: the flat arm of FS `thm:smallbox` for `LowMax` states
(verbatim `Work.BoseFixB1B.FlatBranchLow v h R J` with `IsLowB v h J` replaced by `LowMax`, and
the threshold `J` deleted).  This is the single analytic obligation of the `J`-uniform low-state
chain; its content is FS `thm:smallbox`'s flat branch at the sliding box. -/
def FlatBranchLowMax (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ γ₀ ε₀ C : ℝ, 0 < γ₀ ∧ 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ → 0 < μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (_root_.BoseGases.a v))),
        0 < normB v μ n (Φ : X n → ℝ) →
        LowMax v h μ n (Φ : X n → ℝ) →
        ∀ u ∈ goodSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ,
        ¬ IsThinBox v h μ u →
        UBBInputs8.cnPlusBoxInd (sideAt μ (_root_.BoseGases.a v))
            (dlBox (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u)
            (boxMass (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u)
            (Φ : X n → ℝ)
          < γ₀ * (n : ℝ) * normB v μ n (Φ : X n → ℝ) →
        PerBoxF v h R (1 / 4) C μ n Φ u

/-- **The `J`-free restricted *integrated* per-box node** — verbatim the conclusion of
`Work.BoseFixB1B.integratedPerBoxLow` (resp. `Work.BoseFixB1S.perBoxIntegratedUnif`) with the
threshold `J` deleted and the per-box provider restricted by `LowMax`.  It is obtained from the
restricted per-box provider by the (mechanical) port of `integratedPerBoxLow`, whose proof never
uses `J`: the threshold and the lowness hypothesis are used exactly once, to feed the provider. -/
def IntegratedLowMax (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ c₁ ≤ 1 ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (_root_.BoseGases.a v))),
        0 < normB v μ n (Φ : X n → ℝ) →
        LowMax v h μ n (Φ : X n → ℝ) →
        c₁ * RPsi v h μ (Φ : X n → ℝ)
          ≤ (∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d μ,
                sbWord h μ u (Φ : X n → ℝ))
            + (1 / 2) * μ ^ 2
                * (∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
                    (paramsAt μ (_root_.BoseGases.a v)).d μ,
                    w1MassB h (paramsAt μ (_root_.BoseGases.a v)).M (sideAt μ (_root_.BoseGases.a v))
                      (paramsAt μ (_root_.BoseGases.a v)).d u)
                * normB v μ n (Φ : X n → ℝ)
            + C * (μ ^ 2 * (_root_.BoseGases.a v)
                      * ((R / (sideAt μ (_root_.BoseGases.a v)
                                * (paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                          + (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                      * (∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
                          (paramsAt μ (_root_.BoseGases.a v)).d μ,
                          chiMass (paramsAt μ (_root_.BoseGases.a v)).M
                            (sideAt μ (_root_.BoseGases.a v))
                            (paramsAt μ (_root_.BoseGases.a v)).d u)
                    + μ * (_root_.BoseGases.a v)
                      * (MeasureTheory.volume (interiorSet (sideAt μ (_root_.BoseGases.a v))
                          (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
                * normB v μ n (Φ : X n → ℝ)

/-- **The `J`-free restricted *collected* integrated per-box node** — verbatim the conclusion of
`Work.BoseFixB1B.perBoxIntegratedLow` (the constant-collection form) with the threshold `J` deleted
and the state class restricted by `LowMax`.  This is the node the collection arithmetic of
`Work.BoseFixB1B.collectedUnifOfLowMax` consumes. -/
def IntegratedCollectedLowMax (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ c₁ ≤ 1 ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (_root_.BoseGases.a v))),
        0 < normB v μ n (Φ : X n → ℝ) →
        LowMax v h μ n (Φ : X n → ℝ) →
        c₁ * RPsi v h μ (Φ : X n → ℝ)
          ≤ (∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d μ,
                sbWord h μ u (Φ : X n → ℝ))
            + (1 / 2) * μ ^ 2
                * (∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
                    (paramsAt μ (_root_.BoseGases.a v)).d μ,
                    w1MassB h (paramsAt μ (_root_.BoseGases.a v)).M (sideAt μ (_root_.BoseGases.a v))
                      (paramsAt μ (_root_.BoseGases.a v)).d u)
                * normB v μ n (Φ : X n → ℝ)
            + C * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
                    * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                    * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n (Φ : X n → ℝ)

/-- **The `J`-free restricted interior trim** — verbatim the conclusion of
`Work.BoseFixB1B.trimInteriorOfPerBoxFLow` with the threshold deleted and the state class
restricted by `LowMax`: the `∫_{I₋} → ∫_{ℝ³}` step of FS `eq:badset`. -/
def TrimLowMax (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₃ C₃ : ℝ, 0 < ε₃ ∧ 0 ≤ C₃ ∧
    ∀ μ : ℝ, Adm v ε₃ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (_root_.BoseGases.a v))),
        0 < normB v μ n (Φ : X n → ℝ) →
        LowMax v h μ n (Φ : X n → ℝ) →
        (∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ,
              sbWord h μ u (Φ : X n → ℝ))
          ≤ (∫ u : E3, sbWord h μ u (Φ : X n → ℝ))
            + C₃ * (μ ^ 2 * (_root_.BoseGases.a v)
                    * (sideAt μ (_root_.BoseGases.a v)) ^ 3
                    * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                    * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
              * normB v μ n (Φ : X n → ℝ)

end Work.BoseFixB1B
