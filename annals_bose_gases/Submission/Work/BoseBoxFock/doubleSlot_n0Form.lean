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
# `Work.BoseBoxFock.doubleSlot_n0Form`

The **double slot sum** of the `n₀`-orientation of the χ-row equals the single slot sum with
the slot weight `w(x_i)` multiplied *inside*:

`∑_i ∑_j ∫_{abox} (P_iΦ)·w(x_i)·(P_jΦ) = ∑_i ∫_{abox} (P_iΦ)·(w(x_i)·∑_j P_jΦ)`.

This is a purely formal rearrangement (distributivity + exchange of the finite slot sum with
the integral), the point being that the exchange is legitimate here: every summand
`x ↦ P_iΦ x · w(x_i) · P_jΦ x` is integrable over the centred box, because `P_iΦ` and `P_jΦ`
are continuous (`aP_continuous`, `Φ` being continuous) and `w` is a bounded measurable slot
weight.  Integrability is supplied by `integrableOn_cont_slot_bounded`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem doubleSlot_n0Form {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hwm : Measurable w) {K : ℝ}
    (hw : ∀ x, |w x| ≤ K) :
    (∑ i : Fin n, ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x * w (x i) * Submission.BoseGases.aP ℓ j Φ x)
      = ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x * (w (x i) * (∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ x)) := by
  have hPc : ∀ i : Fin n, Continuous (Submission.BoseGases.aP ℓ i Φ) :=
    fun i => Submission.BoseGases.aP_continuous hℓ i hΦc
  -- integrability of every summand of the double slot sum over the centred box
  have hInt : ∀ i j : Fin n, Integrable (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Φ x * w (x i) * Submission.BoseGases.aP ℓ j Φ x)
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    fun i j => integrableOn_cont_slot_bounded hℓ i (hPc i) (hPc j) hwm hw
  -- the pointwise distributivity
  have hpoint : ∀ (i : Fin n) (x : Submission.BoseGases.X n),
      Submission.BoseGases.aP ℓ i Φ x * (w (x i) * (∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ x))
        = ∑ j : Fin n, Submission.BoseGases.aP ℓ i Φ x * w (x i) * Submission.BoseGases.aP ℓ j Φ x := by
    intro i x
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- exchange the (finite) slot sum with the integral, then use `hpoint`
  refine (MeasureTheory.integral_finsetSum
    (μ := (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))
    Finset.univ (f := fun j : Fin n => fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Φ x * w (x i) * Submission.BoseGases.aP ℓ j Φ x)
    (fun j _ => hInt i j)).symm.trans ?_
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  exact (hpoint i x).symm

end Work.BoseBoxFock
