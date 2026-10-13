import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllExist.Honesty.G1Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open MeasureTheory Set

/-- `G1 α m c` is the product `z ↦ z^{s⁻} · G1A α m c z` (definitional). -/
theorem G1_as_product (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    G1 α m c = fun z => z ^ (G1s α m) * G1A α m c z :=
  funext fun _ => rfl

/-- **`G1A` is continuous on `(0,∞)`.**  It is in fact differentiable there, with derivative
`G1f α m c = t ↦ c t · t^{a-1}` (`G1A_hasDerivAt`), which needs only the continuity of `c` on
`(0,∞)` and the integrability of `G1f` on `(0,1)` (a consequence of `h0`). -/
theorem G1A_continuousOn {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ContinuousOn (G1A α m c) (Set.Ioi 0) := by
  have hInt : IntegrableOn (G1f α m c) (Set.Ioo 0 1) := G1f_integrableOn hα m hc h0
  exact fun z hz => (G1A_hasDerivAt hc hInt z hz).continuousAt.continuousWithinAt

theorem G1_continuousOn {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ContinuousOn (Work.FTS.EllExist.Honesty.G1 α m c) (Set.Ioo 0 1) := by
  have hA : ContinuousOn (G1A α m c) (Set.Ioi 0) := G1A_continuousOn hα m hc h0
  have hpow : ContinuousOn (fun z : ℝ => z ^ (G1s α m)) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
  have hprod : ContinuousOn (fun z : ℝ => z ^ (G1s α m) * G1A α m c z) (Set.Ioo 0 1) :=
    (hpow.mul hA).mono Ioo_subset_Ioi_self
  rw [G1_as_product]
  exact hprod

end Work.FTS.EllExist.Honesty
