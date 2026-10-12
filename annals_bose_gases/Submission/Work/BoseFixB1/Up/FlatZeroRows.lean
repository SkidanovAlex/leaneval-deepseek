import ChallengeDeps
import Submission.Work.BoseFixB1.Up.Core
import Submission.Work.BoseFixB1.Up.FrowSharp
import Submission.Work.BoseFixB1.Up.flatPairRowOper
import Submission.Work.BoseFixB1.Up.flatZeroOmega
import Submission.Work.BoseFixB1S.boxFlatSqJensen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Up.FlatZeroRows` — the two state-level rows of the exactly-flat branch

At FS's parameters (`ℓ = pL v μ`, `d = pD v μ`, `M = pM v μ`, `κ = chiMass M ℓ d u`), define

* `flatXp` — the **pair-condensate count** `κ⁻² Σᵢ Σ_{j≠i} ∫Φ²χ(xᵢ)²χ(xⱼ)²`;
* `flatD`  — the **diagonal correction** `κ⁻² ∫Φ² Σᵢ χ(xᵢ)⁴`.

This module proves

* `flatPairSum_eq_flatXp` — the exactly-flat pair identity `flatPairSum = ½ W₂ flatXp`
  (the integrability discharged, from `Work.BoseFixB1.Up.flatPairRowOper`);
* `flatVar_eq` — the split `flatVar = flatD + flatXp − τ²‖Φ‖²` of the smooth-density variance
  (i.e. `flatT2 = flatD + flatXp`), from `nCountB_sq_integral_eqB1BF` /
  `nCountB_div_sq_integral_eqB1BF`;
* `flatD_div_le` — the diagonal bound `flatD/‖Φ‖² ≤ Cχ²τ/κ` with `Cχ` a bound for the cutoff,
  from the pointwise `χ⁴ ≤ Cχ²χ²`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1.Up

open Submission.BoseGases Work.SmallBoxSliding Work.BoseBoxFix

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- The **diagonal correction** `κ⁻²∫Φ²Σᵢχ(xᵢ)⁴`. -/
noncomputable def flatD (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u)⁻¹ ^ 2 *
    ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2 *
      ∑ i : Fin n,
        (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (x i)) ^ 4

/-- The **pair-condensate count** `κ⁻²ΣᵢΣ_{j≠i}∫Φ²χ(xᵢ)²χ(xⱼ)²`. -/
noncomputable def flatXp (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u)⁻¹ ^ 2 *
    ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
      ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2 *
        (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (x i)) ^ 2 *
        (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (x j)) ^ 2

/-- **The exactly-flat pair identity in pair-condensate form.** -/
theorem flatPairSum_eq_flatXp {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R0 : ℝ} (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hflat : Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) Φ = 0) :
    Work.BoseFixB1.flatPairSum v M ℓ d u Φ
      = (1 / 2) * Work.BoseFixB1.flatPairMass v M ℓ d u
          * ((Work.SmallBoxSliding.chiMass M ℓ d u)⁻¹ ^ 2 *
            ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
              ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2
                * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
                * (Submission.BoseGases.chiSmallB M ℓ d u (x j)) ^ 2) := by
  exact Work.BoseFixB1.Up.flatPairRowOper (v := v) h hv hv1 hR0 hv_supp hM hℓ hd hR16 hRχ u hΦc hflat

/-- **The variance split** `flatT2 = flatD + flatXp` (equivalently
`flatVar = flatD + flatXp − τ²‖Φ‖²`). -/
theorem flatT2_eq_flatD_add_flatXp {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hℓ : 0 < Work.BoseFixB1.pL v μ) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1.Up.flatT2 v μ Φ u
      = Work.BoseFixB1.Up.flatD v μ Φ u + Work.BoseFixB1.Up.flatXp v μ Φ u := by
  have hM1 : 1 ≤ Work.BoseFixB1.pM v μ := by
    rw [Work.BoseFixB1.pM, Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have h1 := Work.BoseFixB1B.nCountB_div_sq_integral_eqB1BF
    (M := Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u (Φ := Φ)
  have h2 := Work.BoseFixB1B.nCountB_sq_integral_eqB1BF
    (M := Work.BoseFixB1.pM v μ) (d := Work.BoseFixB1.pD v μ) hM1 hℓ u hΦc
  have hsum : (∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
      ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2 *
        (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (x i)) ^ 2 *
        (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (x j)) ^ 2)
      = ∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2 *
            (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (x p.1)) ^ 2 *
            (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (x p.2)) ^ 2 :=
    Work.BoseFixB1B.sum_erase_eq_pairSetB1BF (f := fun i j =>
      ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2 *
        (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (x i)) ^ 2 *
        (Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (x j)) ^ 2)
  rw [Work.BoseFixB1.Up.flatT2, Work.BoseFixB1.Up.flatD, Work.BoseFixB1.Up.flatXp, h1, h2, hsum]
  ring

/-! ## The remaining row (statement only, not proved in this file)

**The diagonal bound** `flatD/‖Φ‖² ≤ Cχ²τ/κ` for any pointwise bound `Cχ` of the cutoff:

    theorem flatD_div_le {v} (h : ScatUBB.ScatSol v) {μ Cχ : ℝ} {n : ℕ} {Φ : X n → ℝ}
        (hΦc : Continuous Φ) (hℓ : 0 < Work.BoseFixB1.pL v μ) (u : E3)
        (hCχ : ∀ z, |chiSmallB (pM v μ) (pL v μ) (pD v μ) u z| ≤ Cχ) :
        flatD v μ Φ u / Work.BoseBoxFix.normB v μ n Φ
          ≤ Cχ ^ 2 * Work.BoseFixB1.flatTau (pM v μ) (pL v μ) (pD v μ) u Φ
            / chiMass (pM v μ) (pL v μ) (pD v μ) u

The proof is the pointwise bound `χ⁴ ≤ Cχ²χ²` and `integral_mono_of_nonneg` (the only
integrability input is a constant bound for the dominating continuous integrand on the compact
box, `IntegrableOn.of_bound` + `abox_lt_top`), followed by the field identity
`κ⁻¹²(Cχ²S)/N = Cχ²·(S/(κN))/κ` (`Work.BoseFixB1.flatTau`'s definition, `ring_nf`).  A draft of
the whole proof is in `Submission/Work/BoseFixB1/Up/FINDING_flatZeroHolds_session2.md` §4.
-/

end Work.BoseFixB1.Up
