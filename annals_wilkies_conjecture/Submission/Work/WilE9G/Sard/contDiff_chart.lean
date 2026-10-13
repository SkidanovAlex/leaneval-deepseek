import Mathlib
import Submission.Work.WilE9G.Sard.rankDefs

namespace Work.WilE9G.Sard

theorem contDiff_chart {d m k : ℕ} (f : (Fin (d + 1) → ℝ) → (Fin (m + 1) → ℝ))
    (i : Fin (m + 1)) (j : Fin (d + 1)) (hf : ContDiff ℝ k f) : ContDiff ℝ k (chart f i j) :=
  (kdrj j).contDiff.prodMk
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) i).contDiff.comp hf)

end Work.WilE9G.Sard
