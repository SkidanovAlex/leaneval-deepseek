import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.BoxSideDefs
import Submission.Work.CNum.BoxSide
import Submission.Work.CNum.SerDnSpec
import Submission.Work.CNum.PtC1Spec
import Submission.Work.CNum.PtC2Spec
import Submission.Work.CNum.PtC1bSpec
import Submission.Work.CNum.CuspPoints

namespace Work.CNum

open Work.ANum

/-- `svDn` unfolded. -/
theorem svDn_eq (p : Cpx) : svDn p = serDn (toPB p).x (toPB p).y (toPB p).e := rfl

/-- The point `ψ_C (e^{i·2πk/1024})` lies in the box `ptOf k`. -/
theorem ptOf_mem (k : ℕ) (hk : k ≤ 1024) :
    (ptOf k).Mem (Submission.CDTPlan.psiC
      (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (k : ℂ) / 1024)))) := by
  by_cases h1 : k ≤ 244
  · rw [ptOf, if_pos h1]
    exact PtC1Spec h1
  · rw [ptOf, if_neg h1]
    by_cases h2 : 780 ≤ k
    · rw [if_pos h2]
      exact PtC1bSpec h2 hk
    · rw [if_neg h2]
      exact PtC2Spec (by omega) (by omega)

/-- **Grid lower bound**: `svDn (ptOf k)` bounds `circleLog phiC (k/1024)` from below. -/
theorem gridDn (k : ℕ) (hk : k ≤ 1024) :
    m2r (svDn (ptOf k)) ≤ Submission.CDTPlan.circleLog Submission.CDTPlan.phiC
      ((k : ℝ) / 1024) := by
  obtain ⟨hbox, hOKf, -, -⟩ := BoxSide
  have hOK : BoxOK (ptOf k) := hOKf k hk
  have hmem := ptOf_mem k hk
  have hball : ‖Submission.CDTPlan.psiC
        (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (k : ℂ) / 1024))) -
      bpt (toPB (ptOf k))‖ ≤ m2r (toPB (ptOf k)).e := hbox _ _ hmem
  have hspec := SerDnSpec (x := (toPB (ptOf k)).x) (y := (toPB (ptOf k)).y)
    (e := (toPB (ptOf k)).e)
    (w := Submission.CDTPlan.psiC
      (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (k : ℂ) / 1024))))
    (BoxOK.e_nonneg hOK) (BoxOK.e_le_real hOK) (BoxOK.natAbs_x hOK) (BoxOK.natAbs_y hOK)
    (BoxOK.sigma_le_real hOK) (BoxOK.e_lt_real hOK) (by simpa only [bpt] using hball)
  rw [svDn_eq]
  refine le_trans hspec ?_
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((k : ℝ) / 1024 : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (k : ℂ) / 1024)) := by
    congr 1
    push_cast
    ring
  rw [Submission.CDTPlan.circleLog, Submission.CDTPlan.phiC, hexp]

/-- `svDn ptCuspA` bounds `log ‖h (ψ_C (e^{i α}))‖` from below. -/
theorem cuspADn : m2r (svDn ptCuspA) ≤ Real.log ‖Submission.CDTPlan.hauptH
    (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (alpR : ℂ))))‖ := by
  obtain ⟨hbox, -, hOK, -⟩ := BoxSide
  have hmem := CuspPoints.1
  have hball : ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (alpR : ℂ))) -
      bpt (toPB ptCuspA)‖ ≤ m2r (toPB ptCuspA).e := hbox _ _ hmem
  have hspec := SerDnSpec (x := (toPB ptCuspA).x) (y := (toPB ptCuspA).y)
    (e := (toPB ptCuspA).e)
    (w := Submission.CDTPlan.psiC (Complex.exp (Complex.I * (alpR : ℂ))))
    (BoxOK.e_nonneg hOK) (BoxOK.e_le_real hOK) (BoxOK.natAbs_x hOK) (BoxOK.natAbs_y hOK)
    (BoxOK.sigma_le_real hOK) (BoxOK.e_lt_real hOK) (by simpa only [bpt] using hball)
  rw [svDn_eq]
  exact hspec

/-- `svDn ptCuspB` bounds `log ‖h (ψ_C (e^{i (2π-α)}))‖` from below. -/
theorem cuspBDn : m2r (svDn ptCuspB) ≤ Real.log ‖Submission.CDTPlan.hauptH
    (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) - (alpR : ℂ)))))‖ := by
  obtain ⟨hbox, -, -, hOK⟩ := BoxSide
  have hmem := CuspPoints.2
  have hball : ‖Submission.CDTPlan.psiC
        (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) - (alpR : ℂ)))) -
      bpt (toPB ptCuspB)‖ ≤ m2r (toPB ptCuspB).e := hbox _ _ hmem
  have hspec := SerDnSpec (x := (toPB ptCuspB).x) (y := (toPB ptCuspB).y)
    (e := (toPB ptCuspB).e)
    (w := Submission.CDTPlan.psiC
      (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) - (alpR : ℂ)))))
    (BoxOK.e_nonneg hOK) (BoxOK.e_le_real hOK) (BoxOK.natAbs_x hOK) (BoxOK.natAbs_y hOK)
    (BoxOK.sigma_le_real hOK) (BoxOK.e_lt_real hOK) (by simpa only [bpt] using hball)
  rw [svDn_eq]
  exact hspec

end Work.CNum
