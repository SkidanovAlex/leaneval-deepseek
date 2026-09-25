import Mathlib
import Submission.Work.NN.Seeley.Glob

namespace Work.NN.Seeley

open scoped ENNReal
open Work.NN.Final

/-- Sup-norm form of the Leibniz bound for a bounded bilinear map applied to two `C^i` maps,
for the global-derivative norms `gDN`.  Same proof as `Work.CR.Flat.Holder.iDN_bilinear_le`
(`Submission/Work/CR/Flat/Holder/Bilinear.lean`) with `iteratedFDerivWithin` replaced by
`iteratedFDeriv` (use `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear`). -/
theorem gDN_bilinear_le {Y E F G : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (i : ℕ) {f : Y → E} {g : Y → F} {Ω : Set Y}
    (hf : ContDiff ℝ i f) (hg : ContDiff ℝ i g) :
    Work.NN.Final.gDN i (fun x => B (f x) (g x)) Ω
      ≤ ENNReal.ofReal ‖B‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ENNReal) *
          (Work.NN.Final.gDN j f Ω * Work.NN.Final.gDN (i - j) g Ω) := by
  refine iSup₂_le fun x hx => ?_
  have hb := B.norm_iteratedFDeriv_le_of_bilinear hf hg x (le_rfl : i ≤ (i : WithTop ℕ∞))
  have hsum : (0:ℝ) ≤ ∑ j ∈ Finset.range (i + 1),
      (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j f x‖ *
        ‖iteratedFDeriv ℝ (i - j) g x‖ := by positivity
  calc ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun x => (B (f x)) (g x)) x‖
      ≤ ENNReal.ofReal (‖B‖ * ∑ j ∈ Finset.range (i + 1),
          (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j f x‖ *
            ‖iteratedFDeriv ℝ (i - j) g x‖) :=
        ENNReal.ofReal_le_ofReal hb
    _ = ENNReal.ofReal ‖B‖ * ENNReal.ofReal (∑ j ∈ Finset.range (i + 1),
          (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j f x‖ *
            ‖iteratedFDeriv ℝ (i - j) g x‖) :=
        ENNReal.ofReal_mul (norm_nonneg B)
    _ = ENNReal.ofReal ‖B‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (ENNReal.ofReal ‖iteratedFDeriv ℝ j f x‖ *
            ENNReal.ofReal ‖iteratedFDeriv ℝ (i - j) g x‖) := by
        congr 1
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
        apply Finset.sum_congr rfl
        intro j hj
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ ENNReal.ofReal ‖B‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (Work.NN.Final.gDN j f Ω * Work.NN.Final.gDN (i - j) g Ω) := by
        gcongr with j hj
        · exact le_gDN j hx
        · exact le_gDN (i - j) hx

end Work.NN.Seeley
