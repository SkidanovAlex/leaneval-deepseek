import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.K1dirBDefs
import Submission.Work.BoseBoxFock.L1Tails.chiBasicFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.K1dirB

theorem fderiv_chiG_eq_zero_of_notMem_boxL {ℓ : ℝ} (hℓ : 0 < ℓ)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) {w : EuclideanSpace ℝ (Fin 3)}
    (hw : w ∉ Work.BoseK15.corpusBox.boxL ℓ) (y : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun w' => Work.BoseBoxFock.K1dirB.chiB ℓ w' * G w' y) w = 0 := by
  -- (No smoothness of `G` is needed: the product vanishes identically near `w`.)
  have _hG' := hG
  -- The window `χ_ℓ` is supported in the *closed* box `boxL ℓ = ℓ • cell`.
  have hclosed : IsClosed (Work.BoseK15.corpusBox.boxL ℓ) :=
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).isClosed
  -- Since `w` is outside it, the complement is a neighbourhood of `w`.
  have hnhds : (Work.BoseK15.corpusBox.boxL ℓ)ᶜ ∈ nhds w :=
    hclosed.isOpen_compl.mem_nhds hw
  -- Hence the whole integrand vanishes on a neighbourhood of `w`,
  have hev : (fun w' => Work.BoseBoxFock.K1dirB.chiB ℓ w' * G w' y)
      =ᶠ[nhds w] (fun _ => (0 : ℂ)) := by
    filter_upwards [hnhds] with w' hw'
    rw [Work.BoseBoxFock.K1dirB.chiB_eq_zero_of_notMem_boxL hℓ hw', zero_mul]
  -- so its derivative there is the derivative of the constant zero function.
  rw [hev.fderiv_eq]
  simp

end Work.BoseBoxFock.K1dirB
