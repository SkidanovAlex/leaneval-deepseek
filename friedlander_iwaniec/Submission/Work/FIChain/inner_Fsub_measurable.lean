import Mathlib
import Submission.Work.FIChain.s3RemPlus_maj_le_defs

namespace Work.FIChain

open MeasureTheory
open scoped BigOperators Interval

/-- The `v`-inner integral of the rectangle integrand `Fsub` is a measurable function of `v`.

`Fsub x Cm B ℓ` is jointly measurable in `(v,w)` (`measurable_Fsub`), and the integration is over the
fixed set `Ioc 1 (x/Cm)`, so the result is measurable in `v`.  Concretely, the integrand is the
indicator of the measurable set `univ ×ˢ Ioc 1 (x/Cm)` applied to the jointly measurable function
`(v,w) ↦ Fsub x Cm B ℓ v w / (v·w)`, and the Bochner integral of a jointly measurable function along
one variable is (strongly) measurable (`StronglyMeasurable.integral_prod_right'`). -/
theorem inner_Fsub_measurable (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) :
    Measurable (fun v : ℝ => ∫ w in Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)),
      Work.FIChain.Fsub x Cm B ℓ v w / (v * w)) := by
  set S : Set ℝ := Set.Ioc (1 : ℝ) ((x : ℝ) / (Cm : ℝ)) with hS
  have hSmeas : MeasurableSet S := measurableSet_Ioc
  have hHm : Measurable (fun p : ℝ × ℝ => Work.FIChain.Fsub x Cm B ℓ p.1 p.2 / (p.1 * p.2)) :=
    (measurable_Fsub x Cm B ℓ).div (measurable_fst.mul measurable_snd)
  have hF : StronglyMeasurable (fun p : ℝ × ℝ =>
      S.indicator (fun w => Work.FIChain.Fsub x Cm B ℓ p.1 w / (p.1 * w)) p.2) := by
    have heq : (fun p : ℝ × ℝ =>
          S.indicator (fun w => Work.FIChain.Fsub x Cm B ℓ p.1 w / (p.1 * w)) p.2)
        = (fun p : ℝ × ℝ => ({q : ℝ × ℝ | q.2 ∈ S}.indicator
            (fun q => Work.FIChain.Fsub x Cm B ℓ q.1 q.2 / (q.1 * q.2))) p) := by
      funext p
      simp [Set.indicator_apply]
    rw [heq]
    exact (hHm.indicator (hSmeas.preimage measurable_snd)).stronglyMeasurable
  have hint : StronglyMeasurable (fun v : ℝ => ∫ w, S.indicator
      (fun w => Work.FIChain.Fsub x Cm B ℓ v w / (v * w)) w) :=
    hF.integral_prod_right' (ν := volume)
  rw [show (fun v : ℝ => ∫ w in S, Work.FIChain.Fsub x Cm B ℓ v w / (v * w))
      = (fun v : ℝ => ∫ w, S.indicator
          (fun w => Work.FIChain.Fsub x Cm B ℓ v w / (v * w)) w) from by
      funext v
      exact (integral_indicator hSmeas).symm]
  exact hint.measurable

end Work.FIChain
