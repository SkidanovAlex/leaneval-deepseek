import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.Conv.Q3omPairDefs
import Submission.Work.BoseFixB3.Eps.q3convWord_abs_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Conv/hresPairInt_abs_le`

The **one-body residual bound** for the ordered-pair integral
`hresPairInt fc κ ℓ i j Φ = ∫_{abox n ℓ} PᵢΦ · (PⱼPᵢΦ · hRes(x j))`
of `Work.BoseFixB3.Conv.Q3omPairDefs`:

    |hresPairInt fc κ ℓ i j Φ| ≤ B · ∫_{abox n ℓ} Φ²

whenever `|hRes fc κ ℓ| ≤ B` pointwise and `0 ≤ B`.

This is the estimate FS's `lem:Convolution` needs after the fibre collapse
`Q̄_{L,j}(χ_Λ²P_jΦ) = P_jΦ · hRes(x j)` (the same collapse as in
`Eps/highSlot_chiSq_aP_eq`): the residual one-body profile is bounded by `B`,
so the pairing is dominated by `B ∫|PᵢΦ · PⱼPᵢΦ|`, and Cauchy–Schwarz on the box
together with the contraction `‖PᵢΨ‖² ≤ ‖Ψ‖²` (`Submission.BoseGases.aP_sq_le`)
gives `∫|PᵢΦ · PⱼPᵢΦ| ≤ ∫Φ²` — the contraction being applied twice, since
`PⱼPᵢΦ` is itself a projection of `PᵢΦ`.

The proof is the ordered-pair shadow of the pairwise estimate in
`Eps/q3convWord_abs_le` (there the second factor is `PⱼΦ` rather than `PⱼPᵢΦ`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Conv

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false

/-- Cauchy–Schwarz plus the contraction of the two box projections:
`∫_{abox} |PᵢΦ · PⱼPᵢΦ| ≤ ∫_{abox} Φ²`. -/
lemma aP_pair_aP_abs_integral_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) (i j : Fin n) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        |Submission.BoseGases.aP ℓ i Φ x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x|)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  have hAc : Continuous (Submission.BoseGases.aP ℓ i Φ) :=
    Submission.BoseGases.aP_continuous hℓ i hΦ
  have hCc : Continuous (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ)) :=
    Submission.BoseGases.aP_continuous hℓ j hAc
  have hcs := Submission.BoseGases.cs_box_product hℓ
    (f := fun x => |Submission.BoseGases.aP ℓ i Φ x|)
    (g := fun x => |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x|)
    hAc.abs hCc.abs
  have h1 : (∫ x in Submission.BoseGases.abox n ℓ,
          |Submission.BoseGases.aP ℓ i Φ x|
            * |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x|) ^ 2
      ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
        * (∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x) ^ 2) := by
    simpa only [sq_abs] using hcs
  have h2 : (∫ x in Submission.BoseGases.abox n ℓ,
        |Submission.BoseGases.aP ℓ i Φ x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x|)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          |Submission.BoseGases.aP ℓ i Φ x|
            * |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x| := by
    apply integral_congr_ae
    filter_upwards with x
    rw [abs_mul]
  have h3 : (∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 :=
    Submission.BoseGases.aP_sq_le hℓ i hΦ
  have h4 : (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 :=
    (Submission.BoseGases.aP_sq_le hℓ j hAc).trans (Submission.BoseGases.aP_sq_le hℓ i hΦ)
  have h5 : 0 ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  have h6 : 0 ≤ ∫ x in Submission.BoseGases.abox n ℓ,
      (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  have hsq : (∫ x in Submission.BoseGases.abox n ℓ,
        |Submission.BoseGases.aP ℓ i Φ x|
          * |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x|) ^ 2
      ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) ^ 2 := by
    calc (∫ x in Submission.BoseGases.abox n ℓ,
            |Submission.BoseGases.aP ℓ i Φ x|
              * |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x|) ^ 2
        ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
          * (∫ x in Submission.BoseGases.abox n ℓ,
              (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x) ^ 2) := h1
      _ ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
          * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :=
          mul_le_mul h3 h4 h6 h5
      _ = (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) ^ 2 := by ring
  rw [h2]
  exact le_of_sq_le_sq hsq h5

/-- The residual pairing `∫ PᵢΦ·(PⱼPᵢΦ·hRes(x j))` is bounded by `B · ∫Φ²`
whenever `|hRes| ≤ B` pointwise. -/
theorem hresPairInt_abs_le {fc : Work.BoseBoxFix.LowCut} {κ ℓ B : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ}
    (hℓ : 0 < ℓ) (hB0 : 0 ≤ B) (hΦ : Continuous Φ)
    (hresb : ∀ z : EuclideanSpace ℝ (Fin 3), |Work.BoseFixB3.Eps.hRes fc κ ℓ z| ≤ B)
    (i j : Fin n) :
    |hresPairInt fc κ ℓ i j Φ| ≤ B * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  have hpair := aP_pair_aP_abs_integral_le (ℓ := ℓ) hℓ hΦ i j
  have hcont : Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Φ x
        * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x) :=
    (Submission.BoseGases.aP_continuous hℓ i hΦ).mul
      (Submission.BoseGases.aP_continuous hℓ j (Submission.BoseGases.aP_continuous hℓ i hΦ))
  have hint : Integrable (fun x : Submission.BoseGases.X n =>
      B * |Submission.BoseGases.aP ℓ i Φ x
            * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x|)
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hcont.abs.const_mul B)
  have hub : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)),
      ‖Submission.BoseGases.aP ℓ i Φ x
          * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
              * Work.BoseFixB3.Eps.hRes fc κ ℓ (x j))‖
        ≤ B * |Submission.BoseGases.aP ℓ i Φ x
              * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x| := by
    filter_upwards with x
    rw [Real.norm_eq_abs]
    have hb := hresb (x j)
    calc |Submission.BoseGases.aP ℓ i Φ x
            * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
                * Work.BoseFixB3.Eps.hRes fc κ ℓ (x j))|
        = |Submission.BoseGases.aP ℓ i Φ x|
            * |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x|
            * |Work.BoseFixB3.Eps.hRes fc κ ℓ (x j)| := by rw [abs_mul, abs_mul]; ring
      _ ≤ |Submission.BoseGases.aP ℓ i Φ x|
            * |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x| * B :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = B * |Submission.BoseGases.aP ℓ i Φ x
              * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x| := by
          rw [abs_mul]; ring
  have h1 : |∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x
          * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
              * Work.BoseFixB3.Eps.hRes fc κ ℓ (x j))|
      ≤ ∫ x in Submission.BoseGases.abox n ℓ,
          B * |Submission.BoseGases.aP ℓ i Φ x
                * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x| := by
    have := norm_integral_le_of_norm_le
      (μ := (volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) hint hub
    simpa [Real.norm_eq_abs] using this
  rw [show (∫ x in Submission.BoseGases.abox n ℓ,
          B * |Submission.BoseGases.aP ℓ i Φ x
                * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x|)
      = B * (∫ x in Submission.BoseGases.abox n ℓ,
          |Submission.BoseGases.aP ℓ i Φ x
            * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x|) from
    integral_const_mul B _] at h1
  rw [hresPairInt]
  exact h1.trans (mul_le_mul_of_nonneg_left hpair hB0)

end Work.BoseFixB3.Conv
