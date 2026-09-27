import Mathlib
import Submission.Work.EKLC6Core.C6Aux

namespace Work.EKLC6Core

open MeasureTheory Filter
open scoped ENNReal MeasureTheory

theorem tendsto_neg_log_toReal_iInf {u : ℕ → ENNReal} (hanti : Antitone u)
    (htop : ∀ n, u n ≠ ⊤) (hne : (⨅ n, u n) ≠ 0) :
    Filter.Tendsto (fun n => -Real.log ((u n).toReal)) Filter.atTop
      (nhds (-Real.log ((⨅ n, u n).toReal))) ∧
    Monotone (fun n => -Real.log ((u n).toReal)) := by
  have hLtop : (⨅ n, u n) ≠ ⊤ := ne_top_of_le_ne_top (htop 0) (iInf_le u 0)
  have hlim : Filter.Tendsto u Filter.atTop (nhds (⨅ n, u n)) := tendsto_atTop_iInf hanti
  have hlim2 : Filter.Tendsto (fun n => (u n).toReal) Filter.atTop (nhds ((⨅ n, u n).toReal)) :=
    (ENNReal.tendsto_toReal_iff htop hLtop).mpr hlim
  constructor
  · have hcont : ContinuousAt (fun x : ℝ => - Real.log x) ((⨅ n, u n).toReal) :=
      (Real.continuousAt_log (ENNReal.toReal_pos hne hLtop).ne').neg
    exact hcont.tendsto.comp hlim2
  · intro m n hmn
    have h1 : u n ≤ u m := hanti hmn
    have h2 : (u n).toReal ≤ (u m).toReal := ENNReal.toReal_mono (htop m) h1
    have hn0 : 0 < (u n).toReal :=
      ENNReal.toReal_pos (fun h => hne (by
        have : (⨅ i, u i) ≤ (0 : ENNReal) := by simpa [h] using iInf_le u n
        exact le_antisymm this bot_le)) (htop n)
    exact neg_le_neg (Real.log_le_log hn0 h2)

end Work.EKLC6Core
