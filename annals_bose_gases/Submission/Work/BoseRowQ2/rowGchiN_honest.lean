import ChallengeDeps
import Submission.Work.BoseRowQ2.rowGchiN_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowQ2

theorem rowGchiN_honest {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hav : 0 < _root_.BoseGases.a v) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∃ Ng : ℝ → ℕ, ∀ (εg : ℝ) (ε : ℝ → ℝ), (∀ μ, 0 < μ → 0 < ε μ) →
      Work.BoseRowQ2.RowGchiN (h := h) (fc := fc) (fu := fu) R εg Ng C₁
        (Work.BoseRowQ2.RowGchiMaskRowAux.honCutRad v) ε := by
  refine ⟨Work.BoseRowQ2.RowGchiNAux.rowC fc, Work.BoseRowQ2.RowGchiNAux.rowC_nonneg fc,
    Work.BoseRowQ2.RowGchiNAux.Ng0 v, ?_⟩
  intro εg ε hε
  unfold Work.BoseRowQ2.RowGchiN
  intro hεg HM hN μ hμ ht ρ _
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans ht hεg
  exact Work.BoseRowQ2.RowGchiNAux.gchiAtN_of_matLe (Work.BoseRowQ2.RowGchiNAux.rowC fc)
    (Work.BoseRowQ2.RowGchiMaskRowAux.honCutRad v μ) (ε μ) HM μ (hε μ hμ)
    (fun u => Work.BoseRowQ2.RowGchiNAux.oneBodyRow HM μ hμ hav ht1 (hN μ) (ε μ) (hε μ hμ) u)

end Work.BoseRowQ2
