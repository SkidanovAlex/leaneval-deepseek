import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.amgmSlotSum
import Submission.Work.BoseFixB1.boxPairBlockIntegrable
import Submission.Work.BoseFixB1S.Clean.Fragments
import Submission.Work.BoseFixB1S.Clean.Target
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.amgmSlotSumMeas`

The AM–GM ("slot sum") inequality of `Work.BoseFixB1.amgmSlotSum`, with the
continuity hypotheses on the slots `P i`, `Q i` replaced by the genuinely
weaker pair

* a.e. strong measurability of `P i`, `Q i` on the box `abox N ℓ`, and
* the *pointwise* bounds `|P i x| ≤ CP`, `|Q i x| ≤ CQ` on the box.

The pointwise AM–GM identity is unchanged: for `c ≥ 0`,

`A·(2t·qpc + (t²/A)·p²c + A·q²c) = c·(tp + Aq)² ≥ 0`,

so on the box each slot-integrand is nonnegative, and integrating over
`abox N ℓ` and summing over `i : Fin N` gives

`2t·∑ᵢ∫(QᵢPᵢf) + (t²/A)·∑ᵢ∫(Pᵢ²f) + A·∑ᵢ∫(Qᵢ²f) ≥ 0`,

after which the mass hypothesis `∑ᵢ∫(Pᵢ²f) = (A/4)W` turns the middle term
into `(1/4)t²W`.

The only difference from `amgmSlotSum` is the source of integrability: instead
of `Submission.BoseGases.integrableOn_slot_fibre` (which needs a *continuous*
slot), we use that on a finite-measure set an a.e. strongly measurable function
with an a.e. bound is integrable (`MeasureTheory.IntegrableOn.of_bound`), the
fibre factor `x ↦ f (x i)` being a.e. strongly measurable on the box by
`Submission.BoseGases.aem_comp_coord'`.
-/

open MeasureTheory Metric Filter
open scoped BigOperators

namespace Work.BoseFixB1

set_option linter.unusedVariables false

/-- On the finite-measure box, an a.e. strongly measurable function with an
a.e. bound is integrable. -/
lemma integrableOn_of_aem_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : Submission.BoseGases.X N → ℝ}
    (hgm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)))
    (C : ℝ)
    (hgb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      ‖g x‖ ≤ C) :
    MeasureTheory.IntegrableOn g (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
  MeasureTheory.IntegrableOn.of_bound
    (Submission.BoseGases.abox_lt_top N ℓ hℓ.le) hgm C hgb

theorem amgmSlotSumMeas {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {P Q : Fin N → Submission.BoseGases.X N → ℝ}
    (hPm : ∀ i, MeasureTheory.AEStronglyMeasurable (P i)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)))
    (hQm : ∀ i, MeasureTheory.AEStronglyMeasurable (Q i)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)))
    {CP CQ : ℝ} (hPb : ∀ i, ∀ x ∈ Submission.BoseGases.abox N ℓ, |P i x| ≤ CP)
    (hQb : ∀ i, ∀ x ∈ Submission.BoseGases.abox N ℓ, |Q i x| ≤ CQ)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hfnn : ∀ z, 0 ≤ f z)
    (hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hfb : ∀ z ∈ Submission.BoseGases.acube ℓ, |f z| ≤ B)
    {A t W : ℝ} (hA : 0 < A) (hW : 0 ≤ W)
    (hmass : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (P i x) ^ 2 * f (x i))
      = (A / 4) * W) :
    2 * t * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Q i x) * (P i x) * f (x i))
      ≥ - (1 / 4) * t ^ 2 * W
        - A * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Q i x) ^ 2 * f (x i)) := by
  classical
  -- Scalar AM–GM: `A·(2t·qpc + (t²/A)p²c + A·q²c) = c·(tp + Aq)² ≥ 0`, divided by `A > 0`.
  have hamgm : ∀ c p q : ℝ, 0 ≤ c →
      0 ≤ 2 * t * (q * p * c) + (t ^ 2 / A) * (p ^ 2 * c) + A * (q ^ 2 * c) := by
    intro c p q hc
    have hsq : 0 ≤ c * (t * p + A * q) ^ 2 := mul_nonneg hc (sq_nonneg _)
    have hkey : A * (2 * t * (q * p * c) + (t ^ 2 / A) * (p ^ 2 * c) + A * (q ^ 2 * c))
        = c * (t * p + A * q) ^ 2 := by
      field_simp
      ring
    have h0 : 0 ≤ A * (2 * t * (q * p * c) + (t ^ 2 / A) * (p ^ 2 * c) + A * (q ^ 2 * c)) := by
      rw [hkey]; exact hsq
    exact nonneg_of_mul_nonneg_right h0 hA
  -- The pointwise AM–GM on the box.
  have hpt : ∀ (i : Fin N) (x : Submission.BoseGases.X N), x ∈ Submission.BoseGases.abox N ℓ →
      0 ≤ 2 * t * ((Q i x) * (P i x) * f (x i)) + (t ^ 2 / A) * ((P i x) ^ 2 * f (x i))
        + A * ((Q i x) ^ 2 * f (x i)) := by
    intro i x hx
    exact hamgm (f (x i)) (P i x) (Q i x) (hfnn (x i))
  -- The fibre factor `x ↦ f (x i)` is a.e. strongly measurable on the box.
  have hfaem : ∀ i : Fin N, AEStronglyMeasurable (fun x : Submission.BoseGases.X N => f (x i))
      (volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    fun i => Submission.BoseGases.aem_comp_coord' (N := N) (ℓ := ℓ) i hfm
  -- Integrability of the three integrands on the box, from finite measure and bounds.
  have hI1 : ∀ i : Fin N, IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Q i x) * (P i x) * f (x i)) (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    refine integrableOn_of_aem_bound hℓ (((hQm i).mul (hPm i)).mul (hfaem i))
      (|CQ| * |CP| * |B|) ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    apply ae_of_all
    intro x hx
    have h1 : |Q i x| ≤ |CQ| := le_trans (hQb i x hx) (le_abs_self CQ)
    have h2 : |P i x| ≤ |CP| := le_trans (hPb i x hx) (le_abs_self CP)
    have h3 : |f (x i)| ≤ |B| := le_trans (hfb (x i) (hx i)) (le_abs_self B)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)) h3 (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hI2 : ∀ i : Fin N, IntegrableOn (fun x : Submission.BoseGases.X N =>
      (P i x) ^ 2 * f (x i)) (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    refine integrableOn_of_aem_bound hℓ ?_ (|CP| ^ 2 * |B|) ?_
    · have h1 : AEStronglyMeasurable (fun x : Submission.BoseGases.X N => P i x * P i x)
        (volume.restrict (Submission.BoseGases.abox N ℓ)) := (hPm i).mul (hPm i)
      have h2 : AEStronglyMeasurable (fun x : Submission.BoseGases.X N => P i x * P i x * f (x i))
        (volume.restrict (Submission.BoseGases.abox N ℓ)) := h1.mul (hfaem i)
      simpa [pow_two] using h2
    · rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
      apply ae_of_all
      intro x hx
      have h1 : |P i x| ≤ |CP| := le_trans (hPb i x hx) (le_abs_self CP)
      have h3 : |f (x i)| ≤ |B| := le_trans (hfb (x i) (hx i)) (le_abs_self B)
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 2) h3 (abs_nonneg _)
        (pow_nonneg (abs_nonneg _) 2)
  have hI3 : ∀ i : Fin N, IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Q i x) ^ 2 * f (x i)) (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    refine integrableOn_of_aem_bound hℓ ?_ (|CQ| ^ 2 * |B|) ?_
    · have h1 : AEStronglyMeasurable (fun x : Submission.BoseGases.X N => Q i x * Q i x)
        (volume.restrict (Submission.BoseGases.abox N ℓ)) := (hQm i).mul (hQm i)
      have h2 : AEStronglyMeasurable (fun x : Submission.BoseGases.X N => Q i x * Q i x * f (x i))
        (volume.restrict (Submission.BoseGases.abox N ℓ)) := h1.mul (hfaem i)
      simpa [pow_two] using h2
    · rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
      apply ae_of_all
      intro x hx
      have h1 : |Q i x| ≤ |CQ| := le_trans (hQb i x hx) (le_abs_self CQ)
      have h3 : |f (x i)| ≤ |B| := le_trans (hfb (x i) (hx i)) (le_abs_self B)
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 2) h3 (abs_nonneg _)
        (pow_nonneg (abs_nonneg _) 2)
  -- Splitting the integral of the summand.
  have hper : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (2 * t * ((Q i x) * (P i x) * f (x i)) + (t ^ 2 / A) * ((P i x) ^ 2 * f (x i))
            + A * ((Q i x) ^ 2 * f (x i))))
        = 2 * t * (∫ x in Submission.BoseGases.abox N ℓ, (Q i x) * (P i x) * f (x i))
          + (t ^ 2 / A) * (∫ x in Submission.BoseGases.abox N ℓ, (P i x) ^ 2 * f (x i))
          + A * (∫ x in Submission.BoseGases.abox N ℓ, (Q i x) ^ 2 * f (x i)) := by
    intro i
    have h1 : Integrable (fun x : Submission.BoseGases.X N => (Q i x) * (P i x) * f (x i))
        (volume.restrict (Submission.BoseGases.abox N ℓ)) := hI1 i
    have h2 : Integrable (fun x : Submission.BoseGases.X N => (P i x) ^ 2 * f (x i))
        (volume.restrict (Submission.BoseGases.abox N ℓ)) := hI2 i
    have h3 : Integrable (fun x : Submission.BoseGases.X N => (Q i x) ^ 2 * f (x i))
        (volume.restrict (Submission.BoseGases.abox N ℓ)) := hI3 i
    have h12 : Integrable (fun x : Submission.BoseGases.X N =>
        2 * t * ((Q i x) * (P i x) * f (x i)) + (t ^ 2 / A) * ((P i x) ^ 2 * f (x i)))
        (volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      (h1.const_mul (2 * t)).add (h2.const_mul (t ^ 2 / A))
    rw [integral_add h12 (h3.const_mul A)]
    rw [integral_add (h1.const_mul (2 * t)) (h2.const_mul (t ^ 2 / A))]
    rw [integral_const_mul, integral_const_mul, integral_const_mul]
  -- The integral of the (pointwise nonnegative) summand, summed over slots.
  have hsum_nonneg : 0 ≤ ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (2 * t * ((Q i x) * (P i x) * f (x i)) + (t ^ 2 / A) * ((P i x) ^ 2 * f (x i))
        + A * ((Q i x) ^ 2 * f (x i))) := by
    apply Finset.sum_nonneg
    intro i _
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem (Submission.BoseGases.abox_measurable N ℓ)] with x hx
    exact hpt i x hx
  -- Distribute the sum over the slots.
  have hsplit : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (2 * t * ((Q i x) * (P i x) * f (x i)) + (t ^ 2 / A) * ((P i x) ^ 2 * f (x i))
          + A * ((Q i x) ^ 2 * f (x i))))
      = 2 * t * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Q i x) * (P i x) * f (x i))
        + (t ^ 2 / A) * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (P i x) ^ 2 * f (x i))
        + A * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Q i x) ^ 2 * f (x i)) := by
    trans ∑ i : Fin N, (2 * t * (∫ x in Submission.BoseGases.abox N ℓ, (Q i x) * (P i x) * f (x i))
        + (t ^ 2 / A) * (∫ x in Submission.BoseGases.abox N ℓ, (P i x) ^ 2 * f (x i))
        + A * (∫ x in Submission.BoseGases.abox N ℓ, (Q i x) ^ 2 * f (x i)))
    · exact Finset.sum_congr rfl (fun i _ => hper i)
    · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum]
  have hfinal : 0 ≤ 2 * t * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Q i x) * (P i x) * f (x i))
        + (t ^ 2 / A) * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (P i x) ^ 2 * f (x i))
        + A * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Q i x) ^ 2 * f (x i)) := by
    rw [← hsplit]
    exact hsum_nonneg
  -- Replace the `P²`-mass sum by `(A/4)W`.
  have hWterm : (t ^ 2 / A) *
        (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (P i x) ^ 2 * f (x i))
      = t ^ 2 * W / 4 := by
    rw [hmass]
    field_simp
  have hlin : 0 ≤ 2 * t * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Q i x) * (P i x) * f (x i))
        + t ^ 2 * W / 4
        + A * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Q i x) ^ 2 * f (x i)) := by
    rw [hWterm] at hfinal
    exact hfinal
  linarith

end Work.BoseFixB1
