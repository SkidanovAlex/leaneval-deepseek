import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Linv23Aux.Defs
import Submission.Work.FTS.PhiStar.Linv23Aux.Fallback
import Submission.Work.FTS.PhiStar.Linv23Aux.linvI_smooth
import Submission.Work.FTS.PhiStar.Linv23Aux.linv_smooth_of_phi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar

theorem linv23_smooth {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 t, |h θ| ≤ M) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Work.FTS.PhiStar.Linv h)
        (Set.Ioo 0 (Real.pi / 2)) ∧
      ContDiffOn ℝ Work.Stability.smoothOrder (Work.FTS.PhiStar.LinvI h)
        (Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ t : ℝ, 0 < t → t < Real.pi / 2 →
        ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 t, |Work.FTS.PhiStar.Linv h θ| ≤ M) ∧
      (∀ t : ℝ, 0 < t → t < Real.pi / 2 →
        ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 t, |Work.FTS.PhiStar.LinvI h θ| ≤ M) := by
  have hPhi : ContDiffOn ℝ Work.Stability.smoothOrder (LinvPhi h)
      (Set.Ioo 0 (Real.pi / 2)) := Linv23Aux.Fallback.linvPhi_smooth hsm hbdd
  have hLinv : ContDiffOn ℝ Work.Stability.smoothOrder (Linv h)
      (Set.Ioo 0 (Real.pi / 2)) := Linv23Aux.linv_contDiffOn_of_phi hPhi
  have hLinvBd : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 t, |Linv h θ| ≤ M := Linv23Aux.Fallback.linv_bounded hbdd
  exact ⟨hLinv, Linv23Aux.linvI_smooth hLinv hLinvBd, hLinvBd,
    Linv23Aux.Fallback.linvI_bounded hLinvBd⟩

end Work.FTS.PhiStar
