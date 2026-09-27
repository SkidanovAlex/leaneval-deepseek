import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.planeWrapData
import Submission.Work.Drive.chordStrictWideDescent
import Submission.Work.Drive.bandData
import Submission.Work.Drive.planeProfiles
import Submission.Work.Drive.Neutral.stripTauData
import Submission.Work.Drive.Neutral.dataChord_spec
import Submission.Work.Drive.Neutral.stripDiskChordNe
import Submission.Work.Drive.capLift_reflect
import Submission.Work.Drive.capSideLift
import Submission.Work.Drive.exists_planeChartData

namespace Work.Drive

theorem exists_capDatum_of_data (γ : Circle → ℝ × ℝ)
    (hU : Submission.Drive.UmlaufProp)
    (hWrap : Work.Drive.WrapData γ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    (M W : ℂ × ℝ → ℂ) (c a : ℝ)
    (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hc : 0 < c) (ha : 0 < a) (ha2 : a < 1 / 2)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
      M (x, τ) = Work.Drive.Neutral.dataMid γ x (Real.sqrt τ))
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
      W (x, τ) = Work.Drive.Neutral.dchW γ (x, Real.sqrt τ))
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    (hW0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0)
    (hτc : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → -c ≤ Work.Drive.bandTau a z) :
    ∃ r : ℂ → ℝ, ∃ V : ℂ → Eucl 3,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧
      (∀ z : ℂ, 0 < r z) ∧ (∀ z : ℂ, V z ≠ 0) ∧
      (∀ z : ℂ, 1 / 2 < ‖z‖ → ‖z‖ ≤ 1 →
        r z = Real.sqrt (‖M (Work.Drive.wCollapse z, Work.Drive.bandTau a z)‖ ^ 2
              + Work.Drive.bandTau a z * ‖W (Work.Drive.wCollapse z, Work.Drive.bandTau a z)‖ ^ 2) ∧
        V z = Work.Drive.confProjVecOf
          (W (Work.Drive.wCollapse z, Work.Drive.bandTau a z)
            / ((‖W (Work.Drive.wCollapse z, Work.Drive.bandTau a z)‖ : ℝ) : ℂ))
          (M (Work.Drive.wCollapse z, Work.Drive.bandTau a z)
            / ((Real.sqrt (‖M (Work.Drive.wCollapse z, Work.Drive.bandTau a z)‖ ^ 2
                  + Work.Drive.bandTau a z
                    * ‖W (Work.Drive.wCollapse z, Work.Drive.bandTau a z)‖ ^ 2) : ℝ) : ℂ))) ∧
      (∀ z : ℂ, ‖z‖ < 1 / 2 →
        ∃ w dc : ℂ, w ≠ 0 ∧ ‖dc‖ ≤ 1 ∧ V z = Work.Drive.capProjVecOf w dc) := by
  have hxw : ∀ z : ℂ, ‖z‖ ≤ 1 / 8 → Work.Drive.wCollapse z = 0 := by
    intro z hz
    unfold Work.Drive.wCollapse Work.Drive.wProf
    rw [Work.Drive.profCut_eq_zero (a := 1 / 4) (by norm_num) (by nlinarith [norm_nonneg z]),
      zero_div, Complex.ofReal_zero, zero_mul]
  obtain ⟨r, V, hr, hV, hpos, hne, hpinned, hcap⟩ :=
    Work.Drive.exists_planeChartData hU γ hγ hγne hWrap M W c hMsm hWsm hc hMval hWval hband
      hWne hM0 hW0 (x := Work.Drive.wCollapse) (τ := fun z => Work.Drive.bandTau a z)
      contDiff_wCollapse (bandTau_contDiff ha ha2)
      (fun z hz => wCollapse_eq hz) (fun z => norm_wCollapse_le_one z) hxw
      (fun z hz => bandTau_eq ha2 hz)
      (fun z hz => hτc z hz)
      (fun z hz => bandTau_nonpos (a := a) hz)
  exact ⟨r, V, hr, hV, hpos, hne, fun z hz1 hz2 => hpinned z hz1 hz2, hcap⟩


end Work.Drive
