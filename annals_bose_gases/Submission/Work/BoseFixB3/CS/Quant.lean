import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.qcross_bar_om_pair_weighted
import Submission.Work.BoseFixB3.CS.Reduce
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB3.CS.Quant` — the scalar quantities of the CS step

The CS step (`Steps.lean`, `B3CSRoot`) is proved by the following accounting, in which every
state-dependent quantity is one of the scalar sums defined here (see
`CS/SESSION4_HANDOFF.md` for the full plan):

* `ppMass` — the condensate pair mass `(ℓ³)⁻²·Σ_p∫_{Λ}(P_iP_jΦ)²` (`S₂` in the notes);
* `yMass` — the mass of the `4Q`-bracket remainder `Y = q4B − ω·P_iP_jΦ`, with a free weight;
* `fMass` — the `Q̄_L`-amplitude mass `Σ_p∫(highSlot_j(aP_i(aQ_jΦ)))²·|wgt|`;
* `sMass` — the three-operator pair mass `Σ_p∫(P_jQ_i + Q_jP_i)²·|wgt|`;
* `omegaSqCoupl` — the *fixed* coupling `∫_{Λ²}ω(x−y)²·wgt(x,y)`;
* `leakCoupl` — the *fixed* leakage coupling `∫_{Λ²}leak(y)·ω(x−y)·wgt(x,y)`.

The two fixed couplings multiply `ppMass` after the Fubini factorisation of a slot-constant
weight (`CS/Pieces/pp_sq_factor`); that is the mechanism by which the leakage term
`2·leakCoupl·ppMass` is paid by the condensate content `omegaSqCoupl·ppMass` of the `4Q`-square.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Metric Filter

namespace Work.BoseFixB3.CS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false

/-- The condensate pair mass `S₂ := (ℓ³)⁻²·Σ_{p∈pairSet n}∫_{Λⁿ}(P_{p.1}P_{p.2}Φ)²`. -/
def ppMass (ℓ : ℝ) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ *
    ∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
      (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2

/-- The `4Q`-remainder mass `Σ_p∫(q4B − ω·P_iP_jΦ)²·wgt(x_i,x_j)`. -/
def yMass (ℓ : ℝ) (om wgt : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
    (Submission.BoseGases.q4B ℓ om Φ p x
        - om (x p.1) (x p.2)
          * Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2
      * wgt (x p.1) (x p.2)

/-- The `Q̄_L`-amplitude mass `Σ_p∫(highSlot_j(aP_i(aQ_jΦ)))²·|wgt(x_i,x_j)|`. -/
def fMass (fc : LowCut) (κ ℓ : ℝ)
    (wgt : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
    (Work.BoseFixB3.highSlot fc κ ℓ p.2
        (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x) ^ 2
      * |wgt (x p.1) (x p.2)|

/-- The three-operator pair mass `Σ_p∫(P_jQ_iΦ + Q_jP_iΦ)²·|wgt(x_i,x_j)|`. -/
def sMass (ℓ : ℝ) (wgt : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
    (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
        + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) ^ 2
      * |wgt (x p.1) (x p.2)|

/-- The fixed coupling `∫_{Λ×Λ} ω(x−y)²·wgt(x,y)`. -/
def omegaSqCoupl (ℓ : ℝ) (om wgt : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) :
    ℝ :=
  ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
    (om a b) ^ 2 * wgt a b

/-- The fixed leakage coupling `∫_{Λ×Λ} leak(y)·ω(x−y)·wgt(x,y)`. -/
def leakCoupl (fc : LowCut) (κ ℓ : ℝ)
    (om wgt : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ :=
  ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
    leakFn fc κ ℓ b * om a b * wgt a b

end Work.BoseFixB3.CS
