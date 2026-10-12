import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.amgmSlotSum`

The elementary AM–GM ("slot sum") inequality behind the pairing
`2t⟨QᵢPᵢf⟩ + (t²/A)⟨Pᵢ²f⟩ ≥ −A⟨Qᵢ²f⟩` used throughout the dilute-Bose-gas
estimates: writing `Pᵢ = P i`, `Qᵢ = Q i`, `c = f(xᵢ) ≥ 0`,

`A·(2t QᵢPᵢc + (t²/A)Pᵢ²c + A Qᵢ²c) = c·(t Pᵢ + A Qᵢ)² ≥ 0`

pointwise on the box, and one integrates this over `abox N ℓ` and sums over the
slots `i : Fin N`.  The mass hypothesis `∑ᵢ∫(Pᵢ²f) = (A/4)W` converts the
middle term into `(1/4)t²W`, giving the stated bound.

The only analytic input is that the three integrands are integrable on the box,
which is the corpus lemma `Submission.BoseGases.integrableOn_slot_fibre`
(continuity of the slot, `L¹`-measurability of `f` on the cube, and the cube
bound `|f| ≤ B`).
-/

open MeasureTheory Metric Filter
open scoped BigOperators

namespace Work.BoseFixB1

set_option linter.unusedVariables false

/-- Scalar AM–GM: for `A > 0` and `c ≥ 0`,
`2t(qpc) + (t²/A)(p²c) + A(q²c) ≥ 0`.  This is
`A·(2tqpc + (t²/A)p²c + A q²c) = c·(tp + Aq)² ≥ 0` divided by `A > 0`. -/
private lemma amgm_scalar {A t c p q : ℝ} (hA : 0 < A) (hc : 0 ≤ c) :
    0 ≤ 2 * t * (q * p * c) + (t ^ 2 / A) * (p ^ 2 * c) + A * (q ^ 2 * c) := by
  have hsq : 0 ≤ c * (t * p + A * q) ^ 2 := mul_nonneg hc (sq_nonneg _)
  have hkey : A * (2 * t * (q * p * c) + (t ^ 2 / A) * (p ^ 2 * c) + A * (q ^ 2 * c))
      = c * (t * p + A * q) ^ 2 := by
    field_simp
    ring
  have h0 : 0 ≤ A * (2 * t * (q * p * c) + (t ^ 2 / A) * (p ^ 2 * c) + A * (q ^ 2 * c)) := by
    rw [hkey]; exact hsq
  exact nonneg_of_mul_nonneg_right h0 hA

theorem amgmSlotSum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {P Q : Fin N → Submission.BoseGases.X N → ℝ}
    (hPc : ∀ i, Continuous (P i)) (hQc : ∀ i, Continuous (Q i))
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hfnn : ∀ z, 0 ≤ f z)
    (hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hfb : ∀ z ∈ Submission.BoseGases.acube ℓ, |f z| ≤ B)
    {A t W : ℝ} (hA : 0 < A) (hW : 0 ≤ W)
    (hmass : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (P i x) ^ 2 * f (x i))
      = (A / 4) * W) :
    2 * t * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Q i x) * (P i x) * f (x i))
      ≥ - (1 / 4) * t ^ 2 * W
        - A * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Q i x) ^ 2 * f (x i)) := by
  classical
  -- The pointwise AM–GM on the box.
  have hpt : ∀ (i : Fin N) (x : Submission.BoseGases.X N), x ∈ Submission.BoseGases.abox N ℓ →
      0 ≤ 2 * t * ((Q i x) * (P i x) * f (x i)) + (t ^ 2 / A) * ((P i x) ^ 2 * f (x i))
        + A * ((Q i x) ^ 2 * f (x i)) := by
    intro i x hx
    exact amgm_scalar hA (hfnn (x i))
  -- Integrability of the three integrands on the box.
  have hI1 : ∀ i : Fin N, IntegrableOn (fun x => (Q i x) * (P i x) * f (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    exact Submission.BoseGases.integrableOn_slot_fibre hℓ i hfm hfb ((hQc i).mul (hPc i))
  have hI2 : ∀ i : Fin N, IntegrableOn (fun x => (P i x) ^ 2 * f (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    have h := Submission.BoseGases.integrableOn_slot_fibre (N := N) (ℓ := ℓ) hℓ i hfm hfb
      (S := fun x : Submission.BoseGases.XN N => P i x * P i x) ((hPc i).mul (hPc i))
    simpa [pow_two] using h
  have hI3 : ∀ i : Fin N, IntegrableOn (fun x => (Q i x) ^ 2 * f (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    have h := Submission.BoseGases.integrableOn_slot_fibre (N := N) (ℓ := ℓ) hℓ i hfm hfb
      (S := fun x : Submission.BoseGases.XN N => Q i x * Q i x) ((hQc i).mul (hQc i))
    simpa [pow_two] using h
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
