import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert.GbarSin

theorem Gbar_congr_of_fstar_eq (α : ℝ) {F G : ℝ → ℝ → ℝ}
    (h : ∀ s, 0 < s → Work.Elliptic.Fstar F s = Work.Elliptic.Fstar G s) :
    ∀ z, 0 < z → Work.Elliptic.Gbar α F z = Work.Elliptic.Gbar α G z := by
  intro z hz
  have hint : (∫ s in (0 : ℝ)..z, s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
      = ∫ s in (0 : ℝ)..z, s ^ ((5 - α) / α) * Work.Elliptic.Fstar G s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [Set.uIoc_of_le hz.le] at hs
    rw [h s hs.1]
  simp only [Work.Elliptic.Gbar]
  rw [hint]

end Work.FTS.EllipticEst.Cert.GbarSin
