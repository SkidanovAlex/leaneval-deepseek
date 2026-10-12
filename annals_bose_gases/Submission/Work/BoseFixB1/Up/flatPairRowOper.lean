import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Up.PairRowOper
import Submission.Work.BoseFixB1S.SbPotHalvesB1Fix
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Up.flatPairRowOper` — the exactly-flat pair identity with its integrability
# hypothesis discharged

`Work.BoseFixB1B.flatPairMeanFieldCorrectedB1BF` (proved, and re-exported in the `BoxPotOper`
branch as `Work.BoseFixB1.Up.PairRowOper`) gives, on the box-constant states,

    `flatPairSum = ½·W₂·(∫Φ²(nCountB/κ)² − κ⁻²·∫Φ²Σχ⁴)`,

with an explicit hypothesis `IntegrableOn (wSmallPair M ℓ d u v) (acube ℓ ×ˢ acube ℓ)`.  Here the
integrability is discharged from the standing data (`MemLp v 1`, support in `ball 0 R`, and the
localisation regime `R ≤ ℓd/16`, `R ≤ ℓ·chiR0`) via
`Work.BoseFixB1.integrableOn_wSmallPair_cube`, and the right-hand side is reshaped into the *pair
condensate count*

    `Xp = κ⁻¹² · Σᵢ Σ_{j≠i} ∫ Φ²·χ(xᵢ)²·χ(xⱼ)²`

which is exactly the quantity bounded below by `Work.BoseFixB1Up.flatPairJensen`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1.Up

open Submission.BoseGases Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The exactly-flat pair row**, with the integrability discharged and the right-hand side in
pair-condensate-count form. -/
theorem flatPairRowOper {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) {R0 : ℝ} (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hflat : Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) Φ = 0) :
    Work.BoseFixB1.flatPairSum v M ℓ d u Φ
      = (1 / 2) * Work.BoseFixB1.flatPairMass v M ℓ d u
          * ((Work.SmallBoxSliding.chiMass M ℓ d u)⁻¹ ^ 2
            * ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
                ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2
                  * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
                  * (Submission.BoseGases.chiSmallB M ℓ d u (x j)) ^ 2) := by
  classical
  -- the discharged integrability hypothesis
  have hvint : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hvsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ → v z = 0 :=
    fun z hz => Work.SmallBoxSliding.eq_zero_of_tsupport_subset_ball hv_supp hz
  have hInt : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) :=
    Work.BoseFixB1.integrableOn_wSmallPair_cube hvint hvsupp hM hℓ hd hR16 hRχ u
  have h1 := Work.BoseFixB1B.flatPairMeanFieldCorrectedB1BF (v := v) h hM hℓ hd u hΦc hflat hInt
  rw [Work.BoseFixB1B.nCountB_div_sq_integral_eqB1BF (M := M) ℓ d u,
    Work.BoseFixB1B.nCountB_sq_integral_eqB1BF (M := M) hM hℓ u hΦc] at h1
  rw [h1]
  rw [Work.BoseFixB1B.sum_erase_eq_pairSetB1BF]
  ring

end Work.BoseFixB1.Up
