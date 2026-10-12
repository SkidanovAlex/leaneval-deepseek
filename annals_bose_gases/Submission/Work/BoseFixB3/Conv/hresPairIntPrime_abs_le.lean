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
# `Submission/Work/BoseFixB3/Conv/hresPairIntPrime_abs_le`

The one-body residual estimate for `hresPairInt'`, the residual pairing of
`q3convWord` (`Work.BoseFixB3.Conv.Q3omPairDefs`):

  `|hresPairInt' fc κ ℓ i j Φ| ≤ B * ∫_{abox n ℓ} Φ²`

whenever `|hRes fc κ ℓ| ≤ B` pointwise on `ℝ³`.

This is exactly the per-pair bound (`hpair`) of
`Work.BoseFixB3.Eps.q3convWord_abs_le`, the `ε₂`-size bound for the whole convolution
word: the `hRes` factor is pulled out pointwise, and the remaining pairing
`PᵢΦ · PⱼΦ` is controlled by `Work.BoseFixB3.Eps.aP_pair_abs_integral_le`
(Cauchy–Schwarz on the box plus the contraction `aP_sq_le`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Conv

set_option autoImplicit false

theorem hresPairIntPrime_abs_le {fc : Work.BoseBoxFix.LowCut} {κ ℓ B : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ}
    (hℓ : 0 < ℓ) (hB0 : 0 ≤ B) (hΦ : Continuous Φ)
    (hresb : ∀ z : EuclideanSpace ℝ (Fin 3), |Work.BoseFixB3.Eps.hRes fc κ ℓ z| ≤ B)
    (i j : Fin n) :
    |hresPairInt' fc κ ℓ i j Φ| ≤ B * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  classical
  unfold hresPairInt'
  have hcont : Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x) :=
    (Submission.BoseGases.aP_continuous hℓ i hΦ).mul
      (Submission.BoseGases.aP_continuous hℓ j hΦ)
  have hint : Integrable (fun x : Submission.BoseGases.X n =>
      B * |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x|)
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hcont.abs.const_mul B)
  have hub : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)),
      ‖Submission.BoseGases.aP ℓ i Φ x
          * (Submission.BoseGases.aP ℓ j Φ x * Work.BoseFixB3.Eps.hRes fc κ ℓ (x j))‖
        ≤ B * |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x| := by
    filter_upwards with x
    rw [Real.norm_eq_abs]
    have hb := hresb (x j)
    calc |Submission.BoseGases.aP ℓ i Φ x
            * (Submission.BoseGases.aP ℓ j Φ x * Work.BoseFixB3.Eps.hRes fc κ ℓ (x j))|
        = |Submission.BoseGases.aP ℓ i Φ x| * |Submission.BoseGases.aP ℓ j Φ x|
            * |Work.BoseFixB3.Eps.hRes fc κ ℓ (x j)| := by rw [abs_mul, abs_mul]; ring
      _ ≤ |Submission.BoseGases.aP ℓ i Φ x| * |Submission.BoseGases.aP ℓ j Φ x| * B :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = B * |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x| := by
          rw [abs_mul]; ring
  have h1 : |∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x
          * (Submission.BoseGases.aP ℓ j Φ x * Work.BoseFixB3.Eps.hRes fc κ ℓ (x j))|
      ≤ ∫ x in Submission.BoseGases.abox n ℓ,
          B * |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x| := by
    have h := norm_integral_le_of_norm_le
      (μ := (volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) hint hub
    simpa [Real.norm_eq_abs] using h
  rw [show (∫ x in Submission.BoseGases.abox n ℓ,
          B * |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x|)
      = B * (∫ x in Submission.BoseGases.abox n ℓ,
          |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x|) from
    integral_const_mul B _] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left
    (Work.BoseFixB3.Eps.aP_pair_abs_integral_le hℓ hΦ i j) hB0)

end Work.BoseFixB3.Conv
