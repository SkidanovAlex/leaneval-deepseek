import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiLinearAux
import Submission.Work.BoseBoxFock.chiRowDefs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.doubleSlot_lin` — ℝ-linearity of the double slot sum in the weight

The double slot sum `DS(w) := Σ_i Σ_j ∫_{abox}(PᵢΦ)·w(xᵢ)·(PⱼΦ)` is `ℝ`-linear in the weight
`w`:

    DS(a·w + b·w') = a·DS(w) + b·DS(w') .

This is used to push linear operations (of the χ-row assembly, where the weights are bounded
measurable but **not** continuous) through the position-space slot sums.  The point is that the
integrand is pointwise linear in `w`, and each of the pieces is integrable on the box: the two
slot means `PᵢΦ`, `PⱼΦ` are continuous, and the weight is bounded and measurable, which is
exactly the hypothesis of `integrableOn_cont_slot_bounded` of
`Submission/Work/BoseBoxFock/chiLinearAux.lean`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option maxHeartbeats 800000

theorem doubleSlot_lin {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) {w w' : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hwm : Measurable w) (hw'm : Measurable w') {K K' : ℝ}
    (hw : ∀ x, |w x| ≤ K) (hw' : ∀ x, |w' x| ≤ K') (a b : ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x *
          ((a * w (x i) + b * w' (x i)) * Submission.BoseGases.aP ℓ j Φ x))
      = a * (∑ i : Fin n, ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x * (w (x i) * Submission.BoseGases.aP ℓ j Φ x))
        + b * (∑ i : Fin n, ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x * (w' (x i) * Submission.BoseGases.aP ℓ j Φ x)) := by
  -- Linearity of each double-slot integral, from the pointwise linearity of its integrand.
  have hterm : ∀ i j : Fin n,
      (∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x *
            ((a * w (x i) + b * w' (x i)) * Submission.BoseGases.aP ℓ j Φ x))
        = a * (∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x * (w (x i) * Submission.BoseGases.aP ℓ j Φ x))
          + b * (∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x * (w' (x i) * Submission.BoseGases.aP ℓ j Φ x)) := by
    intro i j
    have hic : Continuous (aP ℓ i Φ) := aP_continuous hℓ i hΦc
    have hjc : Continuous (aP ℓ j Φ) := aP_continuous hℓ j hΦc
    have hI1 : IntegrableOn (fun x : X n => aP ℓ i Φ x * w (x i) * aP ℓ j Φ x)
        (abox n ℓ) volume := integrableOn_cont_slot_bounded hℓ i hic hjc hwm hw
    have hI2 : IntegrableOn (fun x : X n => aP ℓ i Φ x * w' (x i) * aP ℓ j Φ x)
        (abox n ℓ) volume := integrableOn_cont_slot_bounded hℓ i hic hjc hw'm hw'
    have h1 : Integrable (fun x : X n => a * (aP ℓ i Φ x * (w (x i) * aP ℓ j Φ x)))
        ((volume : Measure (X n)).restrict (abox n ℓ)) :=
      (hI1.integrable.const_mul a).congr
        (Filter.EventuallyEq.of_eq (funext (fun x => by ring)))
    have h2 : Integrable (fun x : X n => b * (aP ℓ i Φ x * (w' (x i) * aP ℓ j Φ x)))
        ((volume : Measure (X n)).restrict (abox n ℓ)) :=
      (hI2.integrable.const_mul b).congr
        (Filter.EventuallyEq.of_eq (funext (fun x => by ring)))
    rw [show (∫ x in abox n ℓ,
            aP ℓ i Φ x * ((a * w (x i) + b * w' (x i)) * aP ℓ j Φ x))
        = ∫ x in abox n ℓ, (a * (aP ℓ i Φ x * (w (x i) * aP ℓ j Φ x))
            + b * (aP ℓ i Φ x * (w' (x i) * aP ℓ j Φ x))) from by
      apply integral_congr_ae
      filter_upwards with x
      ring]
    rw [integral_add h1 h2, integral_const_mul, integral_const_mul]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))]
  -- Distribute the two constants over the double sums.
  have hX : (∑ i : Fin n, ∑ j : Fin n, a * (∫ x in abox n ℓ,
        aP ℓ i Φ x * (w (x i) * aP ℓ j Φ x)))
      = a * (∑ i : Fin n, ∑ j : Fin n, ∫ x in abox n ℓ,
        aP ℓ i Φ x * (w (x i) * aP ℓ j Φ x)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ =>
      (Finset.mul_sum Finset.univ (fun j : Fin n => ∫ x in abox n ℓ,
        aP ℓ i Φ x * (w (x i) * aP ℓ j Φ x)) a).symm)
  have hY : (∑ i : Fin n, ∑ j : Fin n, b * (∫ x in abox n ℓ,
        aP ℓ i Φ x * (w' (x i) * aP ℓ j Φ x)))
      = b * (∑ i : Fin n, ∑ j : Fin n, ∫ x in abox n ℓ,
        aP ℓ i Φ x * (w' (x i) * aP ℓ j Φ x)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ =>
      (Finset.mul_sum Finset.univ (fun j : Fin n => ∫ x in abox n ℓ,
        aP ℓ i Φ x * (w' (x i) * aP ℓ j Φ x)) b).symm)
  simp only [Finset.sum_add_distrib]
  rw [hX, hY]

end Work.BoseBoxFock
