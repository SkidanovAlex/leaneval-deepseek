import Mathlib
import Submission.Work.ANum3.CrudeDefs
import Submission.Work.ANum3.ZcertDefs
import Submission.Work.ANum2.slit_second_deriv_bound
import Submission.Work.ANum3.crude_mono

namespace Work.ANum3

open Work.ANum Submission.CDTPlan Complex

/-- The second-derivative bound of `Work.ANum2.slit_second_deriv_bound` re-indexed into the ten
argument slots of `Work.ANum3.crude`: the local (let-bound) quantities of that theorem, evaluated
at the centre `c` and the radius `ρ`, are substituted for the arguments of `crude`. -/
theorem slit_second_deriv_crude {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {c w : ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hw : ‖w - c‖ ≤ ρ) (hdisc : ‖c‖ + ρ < 1) (hwlo : ρ < ‖c‖)
    (hQlo : ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2)) <
      ‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖) :
    ‖deriv (deriv (slit r)) w‖ ≤
      crude r ((1 + r) ^ 2) (2 * (r - 1) ^ 2) (1 + r) (‖c‖ + ρ) (‖c - 1‖ + ρ) (‖c‖ - ρ)
        (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2))
        (‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
          + ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2)))
        (Real.sqrt (‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
          - ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2))))
        (Real.sqrt (‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
          + ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2)))) := by
  have hb := Work.ANum2.slit_second_deriv_bound r hr0 hr1 c w ρ hρ hw hdisc hwlo hQlo
  simp only [crude]
  convert hb using 2 <;> ring

/-- Crude second-derivative bound for the slit map on a disc.  Apply
`Work.ANum2.slit_second_deriv_bound` (real-valued, already proved) at the centre `c` and radius `ρ`,
then push every real quantity monotonically to the supplied bounds `Ab, Bh, Eh, Cb, W, wm1, Qp,
Qhi, Slo, Shi, Wlo`.  (Relevant imports: `Mathlib`, `Submission.Work.ANum3.ZcertDefs`,
`Submission.Work.ANum2.slit_second_deriv_bound`; namespace `Work.ANum3`, open
`Work.ANum Submission.CDTPlan Complex`.) -/
theorem slit_crude_bound {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {c w : ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hw : ‖w - c‖ ≤ ρ) (hdisc : ‖c‖ + ρ < 1) (hwloρ : ρ < ‖c‖)
    (hQlo : ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2)) <
      ‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖)
    {Ab Bh Eh Cb W wm1 Wlo Qp Qhi Slo Shi : ℝ}
    (hAb : (1 + r) ^ 2 ≤ Ab) (hBh : |2 * (1 - 6 * r + r ^ 2)| ≤ Bh) (hEh : 2 * (r - 1) ^ 2 ≤ Eh)
    (hCb : 1 + r ≤ Cb) (hW : ‖c‖ + ρ ≤ W) (hwm1 : ‖c - 1‖ + ρ ≤ wm1)
    (hWlo : Wlo ≤ ‖c‖ - ρ) (hWlo_pos : 0 < Wlo)
    (hQp : ‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2) ≤ Qp)
    (hQhi : ‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖ + ρ * Qp ≤ Qhi)
    (hSlo : 0 < Slo)
    (hSlo_le : Slo ≤ Real.sqrt (‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖ - ρ * Qp))
    (hShi : Real.sqrt Qhi ≤ Shi) :
    ‖deriv (deriv (Submission.CDTPlan.slit r)) w‖ ≤
      ((2 * Ab + Cb * Qp / Slo + Cb * wm1 * (4 * Ab * Qhi + Qp ^ 2) / (4 * Slo ^ 3)) * W ^ 2
        + 2 * (Eh + 2 * Ab * W + Cb * Shi + Cb * wm1 * Qp / (2 * Slo)) * W
        + 2 * (Ab + Eh * W + Ab * W ^ 2 + Cb * wm1 * Shi)) / (8 * r * Wlo ^ 3) := by
  refine (slit_second_deriv_crude hr0 hr1 hρ hw hdisc hwloρ hQlo).trans ?_
  have hQpL0 : 0 ≤ ‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2) := by
    positivity
  have hQhiL0 : 0 ≤ ‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
      + ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2)) := by
    positivity
  have hQhiL : ‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
      + ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2)) ≤ Qhi := by
    refine le_trans ?_ hQhi
    have := mul_le_mul_of_nonneg_left hQp hρ
    linarith
  have hSloL0 : 0 < Real.sqrt (‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
      - ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2))) := by
    apply Real.sqrt_pos.mpr
    linarith [hQlo]
  have hSlo_le' : Slo ≤ Real.sqrt (‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
      - ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2))) := by
    refine le_trans hSlo_le (Real.sqrt_le_sqrt ?_)
    have := mul_le_mul_of_nonneg_left hQp hρ
    linarith
  have hShiL0 : 0 ≤ Real.sqrt (‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
      + ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2))) :=
    Real.sqrt_nonneg _
  have hShiL : Real.sqrt (‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
      + ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2))) ≤ Shi :=
    le_trans (Real.sqrt_le_sqrt hQhiL) hShi
  have hWloL0 : 0 < ‖c‖ - ρ := by linarith [hWlo_pos, hWlo]
  have hmono := crude_mono (r := r) (A := (1 + r) ^ 2) (A' := Ab)
    (E := 2 * (r - 1) ^ 2) (E' := Eh) (C1 := 1 + r) (C1' := Cb)
    (w := ‖c‖ + ρ) (W := W) (wm1b := ‖c - 1‖ + ρ) (wm1 := wm1)
    (wloL := ‖c‖ - ρ) (Wlo := Wlo)
    (QpL := ‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2)) (Qp := Qp)
    (QhiL := ‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
      + ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2))) (Qhi := Qhi)
    (SloL := Real.sqrt (‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
      - ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2)))) (Slo := Slo)
    (ShiL := Real.sqrt (‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
      + ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2)))) (Shi := Shi)
    hr0 (by positivity) hAb (by positivity) hEh (by linarith) hCb (by positivity) hW
    (by positivity) hwm1 hQpL0 hQp hQhiL0 hQhiL hSlo hSloL0 hSlo_le'
    hShiL0 hShiL hWlo_pos hWloL0 hWlo
  exact hmono

end Work.ANum3
