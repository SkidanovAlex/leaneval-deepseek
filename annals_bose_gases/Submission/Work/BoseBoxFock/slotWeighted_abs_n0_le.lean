import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotSum_abs_n0_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotWeighted_abs_n0_le`

The *weighted* slot-sum bound: if `B` is bounded by `K` on the one-particle cube `acube ℓ`, then

    ∑_i ∫_{abox n ℓ} |PᵢΦ| · |B(xᵢ)| · |∑_j PⱼΦ|  ≤  K · n² · ∫_{abox n ℓ} Φ² .

Proof.  On the configuration box `abox n ℓ` every coordinate `xᵢ` lies in `acube ℓ`
(`abox N ℓ = {x | ∀ i, x i ∈ acube ℓ}`), so the hypothesis `hB` gives the **pointwise** bound
`|B (x i)| ≤ K` there.  Hence, for each `i`, the integrand is pointwise dominated by
`K · |PᵢΦ| · |∑_j PⱼΦ|`, and the latter is continuous, hence integrable on the compact box
(`integrableOn_abox_of_continuous`).  Since the dominated integrand is nonnegative, the
comparison of integrals needs no measurability of `B` at all
(`MeasureTheory.integral_mono_of_nonneg`); the hypothesis `hBm` is thus redundant for the bound
(it is kept because the statement is frozen).  Pulling out the constant `K` and summing over
`i` reduces the claim to the unweighted slot-sum bound `slotSum_abs_n0_le`.
-/

namespace Work.BoseBoxFock

-- the frozen statement carries the (unused) measurability hypothesis `hBm`:
set_option linter.unusedVariables false

open MeasureTheory Filter
open scoped BigOperators

open Submission.BoseGases

theorem slotWeighted_abs_n0_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) {B : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hBm : MeasureTheory.AEStronglyMeasurable B
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {K : ℝ} (hK : 0 ≤ K) (hB : ∀ z ∈ Submission.BoseGases.acube ℓ, |B z| ≤ K) :
    ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        |Submission.BoseGases.aP ℓ i Φ x| * |B (x i)|
          * |(∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ x)|
      ≤ K * ((n : ℝ) ^ 2 * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  have hPc : ∀ j : Fin n, Continuous (fun x : X n => aP ℓ j Φ x) :=
    fun j => aP_continuous hℓ j hΦc
  have hScont : Continuous (fun x : X n => |∑ j : Fin n, aP ℓ j Φ x|) :=
    (continuous_finsetSum _ (fun j _ => hPc j)).abs
  -- Termwise domination by the unweighted integrand, times `K`.
  have hterm : ∀ i : Fin n,
      (∫ x in abox n ℓ, |aP ℓ i Φ x| * |B (x i)| * |∑ j : Fin n, aP ℓ j Φ x|)
      ≤ K * ∫ x in abox n ℓ, |aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x| := by
    intro i
    have hcont : Continuous (fun x : X n => K * (|aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x|)) :=
      continuous_const.mul ((hPc i).abs.mul hScont)
    have hgint : Integrable
        (fun x : X n => K * (|aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x|))
        ((volume : Measure (X n)).restrict (abox n ℓ)) :=
      integrableOn_abox_of_continuous hℓ hcont
    have hnn : 0 ≤ᵐ[((volume : Measure (X n))).restrict (abox n ℓ)]
        (fun x : X n => |aP ℓ i Φ x| * |B (x i)| * |∑ j : Fin n, aP ℓ j Φ x|) :=
      Filter.Eventually.of_forall
        (fun x => mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
    have hle : (fun x : X n => |aP ℓ i Φ x| * |B (x i)| * |∑ j : Fin n, aP ℓ j Φ x|)
        ≤ᵐ[((volume : Measure (X n))).restrict (abox n ℓ)]
        (fun x : X n => K * (|aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x|)) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict (abox_measurable n ℓ)] with x hx
      have hb : |B (x i)| ≤ K := hB (x i) (hx i)
      calc |aP ℓ i Φ x| * |B (x i)| * |∑ j : Fin n, aP ℓ j Φ x|
          ≤ |aP ℓ i Φ x| * K * |∑ j : Fin n, aP ℓ j Φ x| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) (abs_nonneg _)
        _ = K * (|aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x|) := by ring
    calc (∫ x in abox n ℓ, |aP ℓ i Φ x| * |B (x i)| * |∑ j : Fin n, aP ℓ j Φ x|)
        ≤ ∫ x in abox n ℓ, K * (|aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x|) :=
          integral_mono_of_nonneg hnn hgint hle
      _ = K * ∫ x in abox n ℓ, |aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x| := by
          rw [MeasureTheory.integral_const_mul]
  calc ∑ i : Fin n, (∫ x in abox n ℓ,
          |aP ℓ i Φ x| * |B (x i)| * |∑ j : Fin n, aP ℓ j Φ x|)
      ≤ ∑ i : Fin n, K * (∫ x in abox n ℓ,
          |aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x|) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = K * ∑ i : Fin n, (∫ x in abox n ℓ,
          |aP ℓ i Φ x| * |∑ j : Fin n, aP ℓ j Φ x|) := by
        rw [Finset.mul_sum]
    _ ≤ K * ((n : ℝ) ^ 2 * ∫ x in abox n ℓ, (Φ x) ^ 2) :=
        mul_le_mul_of_nonneg_left (slotSum_abs_n0_le hℓ hΦc) hK

end Work.BoseBoxFock
