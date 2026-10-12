import ChallengeDeps
import Submission.Work.BoseFixB1B.sectorPieces
import Submission.Work.SlotWord.fibreAmpDecay
import Submission.Work.SlotWord.integrable_fibre_tBdiagFormInd_of_decay
import Submission.Work.SlotWord.integrable_tBdiagFibreJoint_of_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.twoArmFAltDefs` — the group (slot-set) word

Vocabulary for the regrouping step `Work.BoseFixB1B.twoArmF_of_piecesAlt`: the **group word**
`groupWord v h μ N u S Ψ` is the part of the sliding word `fibreWord h M N L d ε c μ u Ψ` carried
by the slots of a slot set `S : Finset (Fin N)`:

* the gap half restricted to the slots of `S` (`Σ_{i ∈ S}‖Q_{B,i}Ψ‖²`),
* the spectral half restricted to the slots of `S`,
* the **within-`S`** part of the potential density: the chemical terms of the slots of `S`, and the
  pair terms of the ordered distinct pairs *both* of whose entries lie in `S`.

It is an abbreviation of the sums of the definitions `Work.UBBInputs8.cnPlusBoxInd`,
`Work.UBBInputs8.tBdiagFormInd` and `Submission.BoseGases.qLHSden` restricted to `S`; the two
structure theorems about it are

* `groupWord_fibre` (the fibre factorisation, `Submission.Work.BoseFixB1B.groupWordFibreAlt`):
  `groupWord … S Ψ = ∫_y fibreWord … (fibre of Ψ at S, y)`,
* `fibreWord_ge_sum_groupWord` (`Submission.Work.BoseFixB1B.groupSplitAlt`): for a partition of
  `Fin N` into the slot sets `S g` and a remainder `S₀`,
  `fibreWord … N Ψ ≥ Σ_g groupWord … (S g) Ψ + groupWord … S₀ Ψ`,
  the cross pairs being dropped (`wSmallPair v ≥ 0`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The within-`S` part of the `qLHSword` density** `qLHSden` (the potential density of
`Submission.BoseGases.qLHSword`): the chemical terms of the slots of `S` and the pair terms of the
ordered distinct pairs with both entries in `S`. -/
noncomputable def qLHSdenS {N : ℕ} (L μ : ℝ) (w w1 : E3 → E3 → ℝ) (S : Finset (Fin N))
    (x : Submission.BoseGases.X N) : ℝ :=
  - μ * (∑ i ∈ S, Submission.BoseGases.w1Fibre L w1 (x i))
    + (1 / 2) * (∑ p ∈ (Submission.BoseGases.pairSet N).filter
        (fun p : Fin N × Fin N => p.1 ∈ S ∧ p.2 ∈ S), w (x p.1) (x p.2))

/-- **The part of the sliding word carried by the slot set `S`.**  The sums of the three pieces of
`fibreWord` restricted to `S` (see the module docstring). -/
noncomputable def groupWord (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (N : ℕ) (u : E3)
    (S : Finset (Fin N)) (Ψ : Submission.BoseGases.X N → ℝ) : ℝ :=
  Work.SmallBoxTBWord.tbGapCoeff (PBℓ v μ * PBd v μ) (PBeT v μ)
      * (∑ i ∈ S, ∫ x in Submission.BoseGases.abox N (PBℓ v μ),
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
            (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) i Ψ x) ^ 2)
  + (∑ i ∈ S, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
        Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖
          * (((PBℓ v μ) ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N (PBℓ v μ),
              ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB (PBℓ v μ) (PBd v μ) u) p
                  (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
                    (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) i Ψ) i x‖ ^ 2))
  + ∫ x in Submission.BoseGases.abox N (PBℓ v μ), (Ψ x) ^ 2
      * qLHSdenS (PBℓ v μ) μ
          (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
          (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) S x

/-- **The admissible-state word bound**: every in-box normalised `k`-particle state of the sliding
box satisfies `R ≤ fWord`.  This is the shape in which the two pieces `WindowFAt` and
`GroupSquareZero` deliver their bound (both are of this form, at the counts at which the count
density `k/PBV` lies in their respective windows), and it is the hypothesis consumed by the
conditional step (`fibreWord_integral_ge_of_adm`): the mass-weighted average of the fibre words is
at least `R` as soon as the bound holds at every admissible state. -/
def GroupAdmWord (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (k : ℕ) (u : E3) (R : ℝ) : Prop :=
  ∀ (Φ : Work.BoseKinLoc.BoxState k (PBℓ v μ)),
    (∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox k (PBℓ v μ))),
      (Φ : Submission.BoseGases.X k → ℝ) x ≠ 0 → ∀ i : Fin k, x i ∈ PBB v μ u) →
    (∫ x in Submission.BoseGases.abox k (PBℓ v μ),
        ((Φ : Submission.BoseGases.X k → ℝ) x) ^ 2) = 1 →
    R ≤ fWord v h μ k u (Φ : Submission.BoseGases.X k → ℝ)

end Work.BoseFixB1B
