import Mathlib
import Submission.Work.Pert.AsmDefs
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.pert2v2.TendstoFloorRep.tendsto_upperEnd_of_floor_rep

namespace Work.Pert.pert2v2.HlimRow

theorem tendsto_upperEnd_of_floor_rep_no_posB {Ef Φm Φp : ℂ → ℂ} {Q Qp : Set ℂ} {cm cp : ℂ}
    {y B : ℝ}
    (hrep : ∀ w : ℂ, y ≤ Complex.im w →
      w - (((Int.floor (Complex.re w) : ℤ)) : ℂ) ∈ Set.image Φm Q ∧
      Ef w = Φp (Work.Pert.invOn Φm Q (w - (((Int.floor (Complex.re w) : ℤ)) : ℂ)))
        + (((Int.floor (Complex.re w) : ℤ)) : ℂ))
    (hIm : Filter.Tendsto
      (fun w : ℂ => Complex.im (Work.Pert.invOn Φm Q (w - (((Int.floor (Complex.re w) : ℤ)) : ℂ))))
      MandelDim.upperEnd Filter.atTop)
    (hRe : ∀ w : ℂ, y ≤ Complex.im w →
      |Complex.re (Work.Pert.invOn Φm Q (w - (((Int.floor (Complex.re w) : ℤ)) : ℂ)))| ≤ B)
    (hQp : ∀ w : ℂ, y ≤ Complex.im w →
      Work.Pert.invOn Φm Q (w - (((Int.floor (Complex.re w) : ℤ)) : ℂ)) ∈ Qp)
    (hEndm : ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Q, Y' < Complex.im z → |Complex.re z| ≤ B →
      ‖Φm z - z - cm‖ < ε)
    (hEndp : ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Qp, Y' < Complex.im z → |Complex.re z| ≤ B →
      ‖Φp z - z - cp‖ < ε) :
    Filter.Tendsto (fun w : ℂ => Ef w - w) MandelDim.upperEnd (nhds (cp - cm)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨Ym, hYm⟩ := hEndm (ε / 2) (by linarith)
  obtain ⟨Yp, hYp⟩ := hEndp (ε / 2) (by linarith)
  have hyle : ∀ᶠ w in MandelDim.upperEnd, y ≤ Complex.im w := by
    rw [MandelDim.upperEnd, Filter.eventually_comap]
    filter_upwards [Filter.eventually_ge_atTop y] with b hb a ha
    rwa [ha]
  have hgt : ∀ᶠ w in MandelDim.upperEnd,
      Ym < Complex.im (Work.Pert.invOn Φm Q (w - (((Int.floor (Complex.re w) : ℤ)) : ℂ))) ∧
      Yp < Complex.im (Work.Pert.invOn Φm Q (w - (((Int.floor (Complex.re w) : ℤ)) : ℂ))) :=
    (hIm.eventually (Filter.eventually_gt_atTop Ym)).and
      (hIm.eventually (Filter.eventually_gt_atTop Yp))
  filter_upwards [hyle, hgt] with w hyl himw
  obtain ⟨himm, himp⟩ := himw
  set k : ℂ := (((Int.floor (Complex.re w) : ℤ)) : ℂ) with hk
  set Z : ℂ := Work.Pert.invOn Φm Q (w - k) with hZ
  obtain ⟨hmem, hEf⟩ := hrep w hyl
  rw [← hk] at hmem hEf
  rw [← hZ] at hEf
  have hzQ : Z ∈ Q := by
    rw [hZ]; exact Work.Pert.invOn_mem hmem
  have hzspec : Φm Z = w - k := by
    rw [hZ]; exact Work.Pert.invOn_spec hmem
  have hQpZ : Z ∈ Qp := by rw [hZ, hk]; exact hQp w hyl
  have hReZ : |Complex.re Z| ≤ B := by rw [hZ, hk]; exact hRe w hyl
  have hm := hYm Z hzQ himm hReZ
  have hp := hYp Z hQpZ himp hReZ
  rw [dist_eq_norm]
  have halg : Ef w - w - (cp - cm) = (Φp Z - Z - cp) - (Φm Z - Z - cm) := by
    have hw : w = Φm Z + k := by rw [hzspec]; ring
    rw [hEf, hw]
    ring
  rw [halg]
  calc ‖(Φp Z - Z - cp) - (Φm Z - Z - cm)‖
      ≤ ‖Φp Z - Z - cp‖ + ‖Φm Z - Z - cm‖ := norm_sub_le _ _
    _ < ε := by linarith

end Work.Pert.pert2v2.HlimRow
