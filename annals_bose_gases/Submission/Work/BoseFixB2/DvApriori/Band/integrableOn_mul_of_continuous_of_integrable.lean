import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.DvApriori.Band

theorem integrableOn_mul_of_continuous_of_integrable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f g : Submission.BoseGases.X n → ℝ} (hf : Continuous f) (hg : Continuous g)
    {W : Submission.BoseGases.X n → ℝ}
    (hWi : MeasureTheory.IntegrableOn W (Submission.BoseGases.abox n ℓ)) :
    MeasureTheory.IntegrableOn (fun x => f x * W x * g x) (Submission.BoseGases.abox n ℓ) := by
  -- The box is compact, so the two continuous factors are bounded on it; each can be
  -- absorbed into `W` one at a time (`IntegrableOn.continuousOn_mul` / `mul_continuousOn`).
  have hK : IsCompact (Submission.BoseGases.abox n ℓ) := Submission.BoseGases.abox_compact n hℓ
  have h1 : MeasureTheory.IntegrableOn (fun x => f x * W x) (Submission.BoseGases.abox n ℓ) :=
    hWi.continuousOn_mul hf.continuousOn hK
  exact h1.mul_continuousOn hg.continuousOn hK

end Work.BoseFixB2.DvApriori.Band
