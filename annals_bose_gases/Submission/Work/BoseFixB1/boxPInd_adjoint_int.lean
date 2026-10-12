import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxPInd_enorm_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.boxPInd_adjoint_int`

Self-adjointness of the FS box projection `Pᵢ = Work.UBBInputs8.boxPInd V A i` on the ambient
box `abox N ℓ`, **at `L¹` regularity in the second argument**:

  `∫_{abox N ℓ} (Pᵢf)·h = ∫_{abox N ℓ} f·(Pᵢh)`

for `f` measurable and bounded on the box and `h` merely measurable and `IntegrableOn` the box.
This is the `IntegrableOn`-regularity companion of `Work.BoseFixB1S.boxPIndSelfAdjoint`, which
assumes both arguments bounded: the two differ in that here `Pᵢh` is *a priori* neither bounded
nor known to be integrable, so the proof must supply

* `Pᵢ` maps `L¹(abox N ℓ)` into itself — `Work.BoseFixB1.boxPInd_enorm_le`, the `enorm`
  contraction `∫⁻‖PᵢΨ‖ₑ ≤ ∫⁻‖Ψ‖ₑ` (the box indicator in `Pᵢ` returns exactly the factor
  `|A| = V` that cancels the normalisation `1/V`); and
* the *unconditional* fibre identity `boxPInd_fibre_eq` below, which needs no integrability at
  all: peeling the `i`-th slot of the box, both fibre integrals reduce to
  `(1/V)·(∫_A f)·(∫_A h)`, symmetrically.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open Submission.BoseGases

set_option maxHeartbeats 1000000

/-- **The fibre identity behind the self-adjointness of `Pᵢ`.**  After peeling the `i`-th slot
of the box (`abox (n+1) ℓ ≃ acube ℓ × abox n ℓ` via `kcInsN n i`), the integrand at a
configuration `kcInsN n i (y,r)` is `1_A(y)` times a quantity which is *independent of `y`*;
the inner integral over `y ∈ acube ℓ` therefore collapses (`setIntegral_indicator_one_mul`), and
both sides reduce to `(1/V)·(∫_A f)·(∫_A h)`.  No measurability or integrability is used. -/
theorem boxPInd_fibre_eq {n : ℕ} {ℓ V : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (i : Fin (n + 1)) (f h : X (n + 1) → ℝ) (r : X n) :
    (∫ y in acube ℓ,
        Work.UBBInputs8.boxPInd V A i f (kcInsN n i (y, r)) * h (kcInsN n i (y, r)))
      = ∫ y in acube ℓ,
          f (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd V A i h (kcInsN n i (y, r)) := by
  have hL : (∫ y in acube ℓ,
        Work.UBBInputs8.boxPInd V A i f (kcInsN n i (y, r)) * h (kcInsN n i (y, r)))
      = ((1 / V) * ∫ z in A, f (kcInsN n i (z, r))) * (∫ z in A, h (kcInsN n i (z, r))) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
          Work.UBBInputs8.boxPInd V A i f (kcInsN n i (y, r)) * h (kcInsN n i (y, r)))
        = fun y => ((1 / V) * ∫ z in A, f (kcInsN n i (z, r)))
            * (A.indicator (fun _ => (1 : ℝ)) y * h (kcInsN n i (y, r))) from by
      funext y
      rw [Work.BoseFixB1S.boxPInd_kcInsN]
      ring]
    rw [MeasureTheory.integral_const_mul]
    rw [Work.BoseFixB1S.setIntegral_indicator_one_mul hA hAc]
  have hR : (∫ y in acube ℓ,
        f (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd V A i h (kcInsN n i (y, r)))
      = ((1 / V) * ∫ z in A, h (kcInsN n i (z, r))) * (∫ z in A, f (kcInsN n i (z, r))) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
          f (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd V A i h (kcInsN n i (y, r)))
        = fun y => ((1 / V) * ∫ z in A, h (kcInsN n i (z, r)))
            * (A.indicator (fun _ => (1 : ℝ)) y * f (kcInsN n i (y, r))) from by
      funext y
      rw [Work.BoseFixB1S.boxPInd_kcInsN]
      ring]
    rw [MeasureTheory.integral_const_mul]
    rw [Work.BoseFixB1S.setIntegral_indicator_one_mul hA hAc]
  rw [hL, hR]
  ring

theorem boxPInd_adjoint_int {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin N) {f h : Submission.BoseGases.X N → ℝ} (hfm : Measurable f) {Cf : ℝ}
    (hCf : 0 ≤ Cf) (hfb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |f x| ≤ Cf)
    (hhm : Measurable h)
    (hhi : MeasureTheory.IntegrableOn h (Submission.BoseGases.abox N ℓ)) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd V A i f x * h x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          f x * Work.UBBInputs8.boxPInd V A i h x := by
  have hPfm : Measurable (Work.UBBInputs8.boxPInd V A i f) :=
    Work.BoseFixB1S.measurable_boxPInd V A hA i hfm
  have hPhm : Measurable (Work.UBBInputs8.boxPInd V A i h) :=
    Work.BoseFixB1S.measurable_boxPInd V A hA i hhm
  have hPfb : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd V A i f x| ≤ Cf :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hfb
  -- `Pᵢ` maps `L¹(abox N ℓ)` into itself, via the `enorm` contraction
  have hPh_int : IntegrableOn (Work.UBBInputs8.boxPInd V A i h) (abox N ℓ) :=
    ⟨hPhm.aestronglyMeasurable,
      lt_of_le_of_lt (boxPInd_enorm_le hℓ hV hA hVeq hAc i hhm) hhi.hasFiniteIntegral⟩
  -- the two pairings are integrable: a bounded measurable factor times an `L¹` factor
  have hPf_int : IntegrableOn (fun x : X N => Work.UBBInputs8.boxPInd V A i f x * h x)
      (abox N ℓ) := by
    refine ((hhi.norm).const_mul Cf).mono' (hPfm.mul hhm).aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hPfb x hx) (abs_nonneg _)
  have hfPh_int : IntegrableOn (fun x : X N => f x * Work.UBBInputs8.boxPInd V A i h x)
      (abox N ℓ) := by
    refine ((hPh_int.norm).const_mul Cf).mono' (hfm.mul hPhm).aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hfb x hx) (abs_nonneg _)
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    rw [abox_integral_peel (i := i)
          (F := fun x : X (n + 1) => Work.UBBInputs8.boxPInd V A i f x * h x) hPf_int,
        abox_integral_peel (i := i)
          (F := fun x : X (n + 1) => f x * Work.UBBInputs8.boxPInd V A i h x) hfPh_int]
    apply integral_congr_ae
    filter_upwards with r
    exact boxPInd_fibre_eq hA hAc i f h r

end Work.BoseFixB1
