/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FlatP/DomAQ`: the `L²` mass of the flat-priced product slot `A · Q`

The engine behind the flat-price star row `rowStarP`.  Given

* the pointwise Leibniz bound `|D_z^b D_θ^a (A·Q)| ≤ KA·KQ·p·q·(flat angular factor)`
  (`p z = z/(1+z)`, `q z = z/(1+z)²`), and
* a dominating angular profile `E` with `∫_{Iθ} E ≤ B`,

we prove that the weighted slot square of `A·Q` is integrable against the leaf weight `ρ`
and bounded by `(KA·KQ)²·B`:

`∫∫ ρ · (D_z^b D_θ^a (A·Q))² ≤ (KA·KQ)² · B`.

The mechanism is the **min-split**: the two decay factors `p` and `q` of the two
coefficient slots combine into `p²q² = (z²/(1+z)³)²`, and the identity
`(w z)²·(z²/(1+z)³)² = (1+z)^{-2}` (away from the null set `{z = 0}`) makes the radial
factor integrable with integral `1` (see `FlatP/Basic` and `FlatP/zWeight_flat`).  The
angular profile `E` then carries all the singular `θ`-weight; for the two cases of the row
it is `8192²·σ^{-1+3α/10}` (`a ≥ 1`) resp. `8192²·σ^{-η}` (`a = 0`), both integrable with
the stated bounds.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open Work.FTS.StrongPersist.H6Rows.Npair6BWork (PM)

/-- The product measure `PM` is the restriction of Lebesgue measure to the closed quadrant. -/
theorem PM_eq_restrict :
    PM = MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [PM, MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]

/-- **The `L²` mass of the product slot.**  If the pointwise Leibniz bound of `D_z^bD_θ^a(A·Q)`
is available in the flat-priced shape, and the angular profile `E` of the dominating function
has `∫_{Iθ} E ≤ B`, then the leaf-weighted square of the slot is integrable with mass at most
`(KA·KQ)²·B`. -/
theorem domAQ {α : ℝ} {A Q : ℝ → ℝ → ℝ} {KA KQ : ℝ} {a b : ℕ}
    {ρ : ℝ → ℝ → ℝ} {E : ℝ → ℝ} {B : ℝ}
    (hKA0 : 0 ≤ KA) (hKQ0 : 0 ≤ KQ)
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hQ : Work.FTS.EllipticEst.SmoothOpen Q)
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hDg : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * E p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) PM ∧
      (∫ p, (Work.Spaces.w p.1) ^ 2 * E p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2 ∂PM) ≤ B)
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) z θ) ^ 2
        ≤ (KA * KQ) ^ 2 * ((Work.Spaces.w z) ^ 2 * E θ * (z ^ 2 / (1 + z) ^ 3) ^ 2)) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        ρ p.1 p.2 * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2) PM ∧
    (∫ p, ρ p.1 p.2
        * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2 ∂PM)
        ≤ (KA * KQ) ^ 2 * B := by
  have hc0 : 0 ≤ (KA * KQ) ^ 2 := sq_nonneg _
  have hDgc : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (KA * KQ) ^ 2 * ((Work.Spaces.w p.1) ^ 2 * E p.2
        * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2)) PM := hDg.1.const_mul _
  have hvalDg : (∫ p, (KA * KQ) ^ 2 * ((Work.Spaces.w p.1) ^ 2 * E p.2
        * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) ∂PM) ≤ (KA * KQ) ^ 2 * B := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hDg.2 hc0
  have hptae : ∀ᵐ p ∂PM, ρ p.1 p.2
      * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2
      ≤ (KA * KQ) ^ 2 * ((Work.Spaces.w p.1) ^ 2 * E p.2
        * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) := by
    exact Work.FTS.StrongPersist.H6Rows.Npair6BWork.ae_of_forall_Qd
      (fun z θ hz hθ0 hθ1 => hpt z θ hz hθ0 hθ1)
  have hnn : ∀ᵐ p ∂PM, 0 ≤ ρ p.1 p.2
      * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2 :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.ae_of_forall_Qd
      (fun z θ hz hθ0 hθ1 =>
        mul_nonneg (Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafW_nonneg hρ z θ hz hθ0 hθ1)
          (sq_nonneg _))
  have hptn : ∀ᵐ p ∂PM, ‖ρ p.1 p.2
      * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2‖
      ≤ (KA * KQ) ^ 2 * ((Work.Spaces.w p.1) ^ 2 * E p.2
        * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) := by
    filter_upwards [hptae, hnn] with p hp hn
    rw [Real.norm_of_nonneg hn]
    exact hp
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ρ p.1 p.2 * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2) PM :=
    (Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_leafW hρ).mul
      ((Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_mixed (smoothOpen_mul hA hQ) b a).pow 2)
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ρ p.1 p.2 * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2) PM :=
    hDgc.mono' hmeas hptn
  refine ⟨hint, ?_⟩
  calc (∫ p, ρ p.1 p.2
        * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2 ∂PM)
      ≤ ∫ p, (KA * KQ) ^ 2 * ((Work.Spaces.w p.1) ^ 2 * E p.2
          * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) ∂PM :=
        MeasureTheory.integral_mono_ae hint hDgc hptae
    _ ≤ (KA * KQ) ^ 2 * B := hvalDg

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP
