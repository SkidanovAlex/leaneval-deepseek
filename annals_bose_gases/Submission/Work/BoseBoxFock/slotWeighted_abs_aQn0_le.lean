import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotSum_abs_aQn0_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotWeighted_abs_aQn0_le` — the slot-weighted `L²` slot bound

Let `Φ : X n → ℝ` be continuous on the `n`-particle centred box `abox n ℓ`, let `Pᵢ = aP ℓ i` be the
slot mean operator (`(PᵢΦ)(x) = ℓ⁻³ ∫_{acube ℓ} Φ(x[i ↦ y]) dy`), `Qᵢ = 1 − Pᵢ` its complement, and
let `Ψ := ∑ⱼ PⱼΦ`.  For a function `B` which is bounded by `K` on the cube `acube ℓ`,

    ∑ᵢ ∫_{abox n ℓ} |PᵢΦ| · |B(xᵢ)| · |QᵢΨ|  ≤  K · n² · ∫_{abox n ℓ} Φ² .

## Proof

Everything is a one-line consequence of the unweighted slot-sum bound
`Work.BoseBoxFock.slotSum_abs_aQn0_le` (weighted AM–GM with weight `n` per slot, followed by the two
`L²`-contractions `aP_sq_le`, `aQn0_aQ_sq_le_box`, and `aQn0_sum_sq_le`):

* **Pointwise on the box**, `x ∈ abox n ℓ` gives `xᵢ ∈ acube ℓ` for every slot `i` (by definition of
  `abox`), hence `|B (xᵢ)| ≤ K` *everywhere* on the box — no a.e. statement, and in particular no use
  of the a.e. strong measurability hypothesis `hBm`, is needed;
* consequently `∫_{abox} |PᵢΦ| |B(xᵢ)| |QᵢΨ| ≤ ∫_{abox} K·(|PᵢΦ| |QᵢΨ|) = K ∫_{abox} |PᵢΦ| |QᵢΨ|`
  (`MeasureTheory.integral_mono_of_nonneg`, whose only integrability input is the *majorant*, which
  is continuous and hence integrable on the box by `integrableOn_abox_of_continuous`);
* summing in `i` and pulling `K` out of the finite sum (`Finset.mul_sum`) reduces the claim to
  `slotSum_abs_aQn0_le`, and `K ≥ 0`.

The constant `K·n²` is exactly the product of the box bound `K` and the sharp constant of
`slotSum_abs_aQn0_le`; no slack is dropped.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

open Submission.BoseGases

set_option autoImplicit false

theorem slotWeighted_abs_aQn0_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) {B : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hBm : MeasureTheory.AEStronglyMeasurable B
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {K : ℝ} (hK : 0 ≤ K) (hB : ∀ z ∈ Submission.BoseGases.acube ℓ, |B z| ≤ K) :
    ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        |Submission.BoseGases.aP ℓ i Φ x| * |B (x i)|
          * |Submission.BoseGases.aQ ℓ i (fun y : Submission.BoseGases.X n =>
              ∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ y) x|
      ≤ K * ((n : ℝ) ^ 2 * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  let Ψ : X n → ℝ := fun y : X n => ∑ j : Fin n, aP ℓ j Φ y
  have hΨc : Continuous Ψ := continuous_finsetSum _ (fun j _ => aP_continuous hℓ j hΦc)
  have hQc : ∀ i : Fin n, Continuous (aQ ℓ i Ψ) := fun i => hΨc.sub (aP_continuous hℓ i hΨc)
  have key : ∀ i : Fin n,
      (∫ x in abox n ℓ, |aP ℓ i Φ x| * |B (x i)| * |aQ ℓ i Ψ x|)
        ≤ K * ∫ x in abox n ℓ, |aP ℓ i Φ x| * |aQ ℓ i Ψ x| := by
    intro i
    have hgi : Integrable (fun x : X n => K * (|aP ℓ i Φ x| * |aQ ℓ i Ψ x|))
        (volume.restrict (abox n ℓ)) :=
      integrableOn_abox_of_continuous hℓ
        (continuous_const.mul (((aP_continuous hℓ i hΦc).abs).mul ((hQc i).abs)))
    have hpoint : ∀ᵐ x ∂(volume.restrict (abox n ℓ)),
        |aP ℓ i Φ x| * |B (x i)| * |aQ ℓ i Ψ x|
          ≤ K * (|aP ℓ i Φ x| * |aQ ℓ i Ψ x|) := by
      rw [MeasureTheory.ae_restrict_iff' (abox_measurable n ℓ)]
      filter_upwards with x hx
      have hBx : |B (x i)| ≤ K := hB (x i) ((mem_abox_iff n ℓ x).mp hx i)
      have h1 : |aP ℓ i Φ x| * |B (x i)| ≤ |aP ℓ i Φ x| * K :=
        mul_le_mul_of_nonneg_left hBx (abs_nonneg _)
      have h2 : |aP ℓ i Φ x| * |B (x i)| * |aQ ℓ i Ψ x| ≤ |aP ℓ i Φ x| * K * |aQ ℓ i Ψ x| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      have h3 : |aP ℓ i Φ x| * K * |aQ ℓ i Ψ x| = K * (|aP ℓ i Φ x| * |aQ ℓ i Ψ x|) := by ring
      linarith [h2, le_of_eq h3]
    calc (∫ x in abox n ℓ, |aP ℓ i Φ x| * |B (x i)| * |aQ ℓ i Ψ x|)
        ≤ ∫ x in abox n ℓ, K * (|aP ℓ i Φ x| * |aQ ℓ i Ψ x|) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun x => by positivity)) hgi hpoint
      _ = K * ∫ x in abox n ℓ, |aP ℓ i Φ x| * |aQ ℓ i Ψ x| := by
          rw [MeasureTheory.integral_const_mul]
  calc ∑ i : Fin n, ∫ x in abox n ℓ, |aP ℓ i Φ x| * |B (x i)| * |aQ ℓ i Ψ x|
      ≤ ∑ i : Fin n, K * ∫ x in abox n ℓ, |aP ℓ i Φ x| * |aQ ℓ i Ψ x| :=
        Finset.sum_le_sum (fun i _ => key i)
    _ = K * ∑ i : Fin n, ∫ x in abox n ℓ, |aP ℓ i Φ x| * |aQ ℓ i Ψ x| := by
        rw [Finset.mul_sum]
    _ ≤ K * ((n : ℝ) ^ 2 * ∫ x in abox n ℓ, (Φ x) ^ 2) :=
        mul_le_mul_of_nonneg_left (slotSum_abs_aQn0_le hℓ hΦc) hK

end Work.BoseBoxFock
