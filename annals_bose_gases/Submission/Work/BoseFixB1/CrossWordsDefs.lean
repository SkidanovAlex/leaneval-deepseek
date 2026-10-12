import ChallengeDeps
import Submission.Work.BoseFixB1B.PerBoxSectorResidual
import Submission.Work.BoseFixB1S.BoxQWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.CrossWordsBound` — the cross-word residual of the condensed per-sector bound

`Work.BoseFixB1S.boxQSum = boxQ0 + boxQ1 + boxQ2 + boxQ3 + boxQ4` at the sliding box
`B(u) = dlBox ℓ d u`.  `boxQ0` has the exact value `½(M₂/V²)boxPairCount − μ(M₁/V)boxFlatCount`
(`Work.BoseFixB1.boxQ0_value`), so the entire *positive* mean-field content of
`qLHSwordB = boxQSum` sits in `boxQ0`, and the four cross words are the residual.

`CrossWordsBound v h ε₀ lb K` is the residual in the regime that the condensed per-sector target
needs: a **sector piece** (`Ψ` supported where the box occupancy `n_{B(u)}` equals the constant
`k`) in the **condensed** regime (`boxQCount ≤ boxFlatCount`), with the credit

    lb·(M₂/V²)·boxPairCount + K·a(v)·[μ·n₊ + μ·√(n₊·S) + (k/V)·n₊] ,   S = boxFlatCount,

i.e. a share `lb` of the mean-field pair term, plus an FS-shaped credit (`μ`- and `S/V`-slots)
augmented by the Cauchy–Schwarz cross term `μ√(n₊S)` coming from the `μ`-line of `boxQ1`.

The two structural restrictions are what make the bound elementary (see the module docstring of
`Submission/Work/BoseFixB1/boxCrossWordsBound.lean`): on a sector piece `n₀ = Σ_iP_{B,i} ≤ n_B ≤ k`
gives `Σ_{i≠j}‖P_{B,i}Q_{B,j}Ψ‖² ≤ k·n₊`, and `boxQCount ≤ boxFlatCount` with the count identity
`S + n₊ = k·∫Ψ²` gives `k ≤ 2S/∫Ψ²`, so the credit's `k/V`-slot is the local count slot.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge
open Work.BoseFixB1B

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The cross-word residual (sector + condensed form).** -/
def CrossWordsBound (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (ε₀ lb K : ℝ) : Prop :=
  0 < ε₀ ∧ 0 ≤ lb ∧ lb ≤ 1 / 4 ∧ 0 ≤ K ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n k : ℕ) (Ψ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)),
        0 < Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u →
        (∀ x : Submission.BoseGases.X n,
          Work.FockBridge.boxCount (PBB v μ u) x ≠ k → Ψ x = 0) →
        Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
            (PBℓ v μ) (PBB v μ u) Ψ
          ≤ Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
              (PBℓ v μ) (PBB v μ u) Ψ →
        - lb * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                (PBB v μ u)
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
                  (Submission.BoseGases.g2 v h))
              / (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u) ^ 2)
            * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                (PBℓ v μ) (PBB v μ u) Ψ
          - K * (_root_.BoseGases.a v)
            * (μ * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                  (PBℓ v μ) (PBB v μ u) Ψ
                + μ * Real.sqrt
                    (Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                        (PBℓ v μ) (PBB v μ u) Ψ
                      * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                          (PBℓ v μ) (PBB v μ u) Ψ)
                + ((k : ℝ) / Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                  * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                      (PBℓ v μ) (PBB v μ u) Ψ)
          ≤ Work.BoseFixB1S.boxQ1 (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                (PBℓ v μ) μ (PBB v μ u)
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
                  (Submission.BoseGases.g2 v h)) Ψ
            + Work.BoseFixB1S.boxQ2 (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                (PBℓ v μ) μ (PBB v μ u)
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
                  (Submission.BoseGases.g2 v h)) Ψ
            + Work.BoseFixB1S.boxQ3 (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                (PBℓ v μ) (PBB v μ u)
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) Ψ
            + Work.BoseFixB1S.boxQ4 (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                (PBℓ v μ) (PBB v μ u)
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
                (Submission.BoseGases.omC (Classical.choose h)) Ψ

/-- **The cross-word residual, read at the occupancy-sector piece** (the form the assembly of
`Work.BoseFixB1.perSectorBoundG_condensed` consumes).

⚠️ The *unrestricted* form (`CrossWordsBound`, quantifying over an arbitrary `Ψ`) is **false**: `Ψ`
carries no integrability hypothesis, so Lean's Bochner convention `∫ = 0` on non-integrable
functions makes every credit slot vanish (`boxQCount = 0`) while the `μ`-line of `boxQ1` stays
nonzero — see `FINDING_boxCrossWordsBound_FALSE.md`.  Quantifying over `sectorPiece (PBB v μ u) k Φ`
with `Φ : BoxState n (PBℓ v μ)` — i.e. the actual use — restores boundedness and measurability, and
makes the sector-support hypothesis automatic. -/
def CrossSectorBound (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (lb ε₀ K : ℝ) : Prop :=
  0 < ε₀ ∧ 0 ≤ lb ∧ lb ≤ 1 / 4 ∧ 0 ≤ K ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n k : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : EuclideanSpace ℝ (Fin 3)),
        0 < Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u →
        Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
            (PBℓ v μ) (PBB v μ u) (sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
          ≤ Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
              (PBℓ v μ) (PBB v μ u) (sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ)) →
        - lb * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                (PBB v μ u)
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
                  (Submission.BoseGases.g2 v h))
              / (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u) ^ 2)
            * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                (PBℓ v μ) (PBB v μ u) (sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
          - K * (_root_.BoseGases.a v)
            * (μ * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                  (PBℓ v μ) (PBB v μ u) (sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
                + μ * Real.sqrt
                    (Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                        (PBℓ v μ) (PBB v μ u) (sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
                      * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                          (PBℓ v μ) (PBB v μ u) (sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ)))
                + ((k : ℝ) / Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                  * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                      (PBℓ v μ) (PBB v μ u) (sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ)))
          ≤ Work.BoseFixB1S.boxQ1 (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                (PBℓ v μ) μ (PBB v μ u)
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
                  (Submission.BoseGases.g2 v h)) (sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
            + Work.BoseFixB1S.boxQ2 (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                (PBℓ v μ) μ (PBB v μ u)
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
                  (Submission.BoseGases.g2 v h)) (sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
            + Work.BoseFixB1S.boxQ3 (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                (PBℓ v μ) (PBB v μ u)
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) (sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
            + Work.BoseFixB1S.boxQ4 (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                (PBℓ v μ) (PBB v μ u)
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
                (Submission.BoseGases.omC (Classical.choose h)) (sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))


end Work.BoseFixB1

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge
open Work.BoseFixB1B

/-- **The localised pair-mass excess of the sliding box** — the second analytic input of the
condensed per-sector bound, and the payer of the target's `(½ − c)μ²` background.

For some `ε₀ > 0` and some `γ₀ > 0`, at every admissible `μ` and every sliding position `u` with
nonempty box,

    (1 + γ₀)·boxM1 ℓ A w₁ ≤ boxM2 V A w₂ ,

i.e. `M₂ ≥ (1+γ₀)M₁` with `M₁ = boxM1 ℓ A w₁ = ∬w_{1,B(u)}` and `M₂ = boxM2 V A w₂ = ∬w_{2,B(u)}`
(the FS `lm:w2>w1` quantity `(M₂−M₁)/M₁ = ∫ω w₁/∫w₁`).  This is **proved** in the corpus
(modulo the wrapper): `Work.BoseFixB1S.mfM2M1_key` gives
`(a v)/(2R)·boxM1 ℓ A w₁ ≤ boxM2 V A w₂ − boxM1 ℓ A w₁` for *every* `ℓ > 0`, `d > 0`, `u` and
every `M ≥ 1`, with **no** small-range hypothesis.  See `Work.BoseFixB1.pairMassData`.

⚠️ The *lower* bound `χ₁·a(v)·V ≤ M₁` is **false** as stated (`Work.BoseFixB1S/w1MassB_lowerB1.lean`
refutes exactly that, with the same hypothesis list) and is deliberately *not* part of this
predicate; the assembly must (and does) avoid dividing by `M₁`
(see `FINDING_perSectorBoundG_condensed.md` §2). -/
def PairMassData (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (ε₀ γ₀ : ℝ) : Prop :=
  0 < ε₀ ∧ 0 < γ₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        0 < Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u →
          (1 + γ₀) * Work.BoseFixB1S.boxM1 (PBℓ v μ) (PBB v μ u)
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
            ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                (PBB v μ u)
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
                  (Submission.BoseGases.g2 v h))

end Work.BoseFixB1

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge
open Work.BoseFixB1B

/-- **The sector-piece structure bundle** for the sliding box at FS's parameters.

At every admissible `μ`, every `n`, `k`, every smooth symmetric box state `Φ` and every sliding
position `u` with nonempty box, the **occupancy-sector piece** `ψ := sectorPiece (PBB v μ u) k Φ`
(= `1_{n_{B(u)} = k}·Φ`, a *measurable but not continuous* function) satisfies the four
structure statements that the corpus proves for *continuous* states:

* **(S1) potsplit** — `qLHSwordB` at the localised kernels equals the five-word box sum
  (`Work.BoseFixB1.bqPotsplit` for continuous states);
* **(S2) `boxQ0`'s exact value** — `Work.BoseFixB1.boxQ0_value`;
* **(S3) Jensen** — `Work.BoseFixB1S.boxFlatSqJensen`;
* **(S4) the count identity** — `boxFlatCount + boxQCount = k·∫ψ²`, from
  `Work.BoseFixB1S.boxPInd_sq_add_boxQInd_sq` summed over the slots and the sector support
  (`boxCount (PBB) x = k` wherever `ψ x ≠ 0`).

The *only* new content relative to the corpus is the replacement of the `Continuous Φ` hypothesis
by measurability+boundedness of the piece (every one of the corpus proofs uses continuity only to
get the integrability of the Finitely many integrands; the sector piece of a smooth `Φ` is bounded
on the compact box).  Needed by `Work.BoseFixB1.perSectorBoundG_condensed`. -/
def SectorPieceStructure (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ (n k : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : EuclideanSpace ℝ (Fin 3)),
      0 < Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u →
        let V : ℝ := Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u
        let A : Set (EuclideanSpace ℝ (Fin 3)) := PBB v μ u
        let ψ : Submission.BoseGases.X n → ℝ :=
          sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ)
        let w₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
          Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u
        let w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
          Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u
            (Submission.BoseGases.g2 v h)
        (Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u ψ
            = Work.BoseFixB1S.boxQSum V (PBℓ v μ) μ A
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v) w₁ w₂
                (Submission.BoseGases.omC (Classical.choose h)) ψ)
          ∧ (Work.BoseFixB1S.boxQ0 V (PBℓ v μ) μ A w₁ w₂ ψ
              = (1 / 2) * (Work.BoseFixB1S.boxM2 V A w₂ / V ^ 2)
                  * Work.BoseFixB1S.boxPairCount V (PBℓ v μ) A ψ
                - μ * (Work.BoseFixB1S.boxM1 (PBℓ v μ) A w₁ / V)
                    * Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A ψ)
          ∧ (Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A ψ
                * Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A ψ
              - Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A ψ
                  * (∫ x in Submission.BoseGases.abox n (PBℓ v μ), (ψ x) ^ 2)
              ≤ (∫ x in Submission.BoseGases.abox n (PBℓ v μ), (ψ x) ^ 2)
                  * Work.BoseFixB1S.boxPairCount V (PBℓ v μ) A ψ)
          ∧ (Work.BoseFixB1S.boxFlatCount V (PBℓ v μ) A ψ
                + Work.BoseFixB1S.boxQCount V (PBℓ v μ) A ψ
              = (k : ℝ) * (∫ x in Submission.BoseGases.abox n (PBℓ v μ), (ψ x) ^ 2))

end Work.BoseFixB1
