import Mathlib
import Submission.Work.Drive.chordStrictWideDescent
import Submission.Work.Drive.chordWideAnnulusDescent
import Submission.Work.Drive.bandData
import Submission.Work.Drive.planeProfiles
import Submission.Work.Drive.capLift_reflect
import Submission.Work.Drive.capSide_capPiece
import Submission.Work.Drive.Neutral.dataChord_spec
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.planeWrapData
import Submission.Work.Drive.capAngleOfSmooth
import Submission.Work.Drive.planeChartDataAux
import Submission.Work.Drive.bandLoop_periodic_argument
import Submission.Work.Drive.Neutral.stripDiskChordNe
import Submission.Work.Drive.Neutral.dataR_dataD_spec
import Submission.Work.Drive.exists_collar_of_norm_eq
import Submission.Work.Drive.periodicArgument_annulus_transport
import Submission.Work.Drive.smoothUnit_eqOn_annulus_of_periodicArgument

namespace Work.Drive

set_option maxHeartbeats 4000000 in
theorem exists_planeChartData (hU : Submission.Drive.UmlaufProp) (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hWrap : Work.Drive.WrapData γ)
    (M W : ℂ × ℝ → ℂ) (c : ℝ)
    (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hc : 0 < c)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
      M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ))
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
      W (x, τ) = Neutral.dchW γ (x, Real.sqrt τ))
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    (hW0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0)
    (x : ℂ → ℂ) (τ : ℂ → ℝ)
    (hxsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x)
    (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ)
    (hx1 : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → x z = z / (‖z‖ : ℂ))
    (hxn : ∀ z : ℂ, ‖x z‖ ≤ 1)
    (hxw : ∀ z : ℂ, ‖z‖ ≤ 1 / 8 → x z = 0)
    (hτ1 : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → τ z = Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2))
    (hτ2 : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → -c ≤ τ z)
    (hτ3 : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → τ z ≤ 0) :
    ∃ r : ℂ → ℝ, ∃ V : ℂ → Eucl 3,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧
      (∀ z : ℂ, 0 < r z) ∧
      (∀ z : ℂ, V z ≠ 0) ∧
      (∀ z : ℂ, 1 / 2 < ‖z‖ → ‖z‖ ≤ 1 →
        let A := ‖M (x z, τ z)‖ ^ 2 + τ z * ‖W (x z, τ z)‖ ^ 2
        r z = Real.sqrt A ∧
        V z = confProjVecOf (W (x z, τ z) / ((‖W (x z, τ z)‖ : ℝ) : ℂ))
          (M (x z, τ z) / ((Real.sqrt A : ℝ) : ℂ))) ∧
      (∀ z : ℂ, ‖z‖ < 1 / 2 →
        ∃ w dc : ℂ, w ≠ 0 ∧ ‖dc‖ ≤ 1 ∧ V z = capProjVecOf w dc) := by
  classical
  -- ### 0. the collar radius where the profile is good
  have hxnorm : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖x z‖ = 1 := by
    intro z hz
    have hzpos : 0 < ‖z‖ := by linarith
    rw [hx1 z hz, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z),
      div_self (ne_of_gt hzpos)]
  have hout : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → (1 / 4 : ℝ) ≤ ‖x z‖ := fun z hz => by
    rw [hxnorm z hz]; norm_num
  have hin : ∀ z : ℂ, ‖z‖ = 1 / 2 → (1 / 4 : ℝ) < ‖x z‖ := fun z hz => by
    rw [hxnorm z (le_of_eq hz.symm)]; norm_num
  obtain ⟨ρ, hρ0, hρhalf, hρgood⟩ := exists_collar_of_norm_eq x hxsm.continuous hout hin
  -- ### 1. the four radii
  set δ : ℝ := 1 / 2 - ρ with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set ρA : ℝ := ρ + δ / 5 with hρA
  set ρB : ℝ := ρ + 2 * δ / 5 with hρB
  set ρC : ℝ := ρ + 3 * δ / 5 with hρC
  have hρ_lt_ρA : ρ < ρA := by rw [hρA]; linarith
  have hρA_lt_ρB : ρA < ρB := by rw [hρA, hρB]; linarith
  have hρB_lt_ρC : ρB < ρC := by rw [hρB, hρC]; linarith
  have hρC_lt_half : ρC < 1 / 2 := by rw [hρC, hδ]; linarith
  have hρA_pos : 0 < ρA := by linarith
  have hρB_pos : 0 < ρB := by linarith
  have hρB_lt_half : ρB < 1 / 2 := by linarith
  have hsq0A : ρ ^ 2 < ρA ^ 2 := by nlinarith
  have hsqAB : ρA ^ 2 < ρB ^ 2 := by nlinarith
  have hsqBC : ρB ^ 2 < ρC ^ 2 := by nlinarith
  -- ### 2. the cut-offs
  set χ : ℂ → ℝ := fun z => pcCut (ρA ^ 2) (ρB ^ 2) z with hχ
  set χd : ℂ → ℝ := fun z => pcCut (ρ ^ 2) (ρA ^ 2) z * pcCutDown (ρB ^ 2) (ρC ^ 2) z with hχd
  have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := contDiff_pcCut _ _
  have hχdsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χd :=
    (contDiff_pcCut _ _).mul (contDiff_pcCutDown _ _)
  have hχ_nonneg : ∀ z : ℂ, 0 ≤ χ z := fun z => pcCut_nonneg _ _ z
  have hχ_le : ∀ z : ℂ, χ z ≤ 1 := fun z => pcCut_le_one _ _ z
  have hχ_eq_zero : ∀ z : ℂ, ‖z‖ < ρA → χ z = 0 := by
    intro z hz
    rw [hχ]
    exact pcCut_eq_zero hsqAB (le_of_lt (normSq_lt_of_lt_norm hρA_pos.le hz))
  have hχ_eq_one : ∀ z : ℂ, ρB ≤ ‖z‖ → χ z = 1 := by
    intro z hz
    rw [hχ]
    exact pcCut_eq_one hsqAB (le_trans (by nlinarith : ρB ^ 2 ≤ ‖z‖ ^ 2)
      (by rw [← Complex.normSq_eq_norm_sq]))
  have hχ_ne_zero : ∀ z : ℂ, χ z ≠ 0 → ρA < ‖z‖ := by
    intro z hz
    rw [hχ] at hz
    exact lt_norm_of_normSq_lt hρA_pos.le ((pcCut_pos_iff hsqAB z).mp (lt_of_le_of_ne
      (pcCut_nonneg _ _ z) (Ne.symm hz)))
  have hχ_ne_one : ∀ z : ℂ, χ z ≠ 1 → ‖z‖ < ρB := by
    intro z hz
    by_contra h
    exact hz (hχ_eq_one z (le_of_not_gt h))
  have hχd_nonneg : ∀ z : ℂ, 0 ≤ χd z := fun z =>
    mul_nonneg (pcCut_nonneg _ _ z) (pcCutDown_nonneg _ _ z)
  have hχd_le : ∀ z : ℂ, χd z ≤ 1 := by
    intro z
    have h1 := pcCut_le_one (ρ ^ 2) (ρA ^ 2) z
    have h2 := pcCutDown_le_one (ρB ^ 2) (ρC ^ 2) z
    have h3 := pcCut_nonneg (ρ ^ 2) (ρA ^ 2) z
    have h4 := pcCutDown_nonneg (ρB ^ 2) (ρC ^ 2) z
    simp only [hχd]
    nlinarith
  have hχd_eq_zero_lt : ∀ z : ℂ, ‖z‖ < ρ → χd z = 0 := by
    intro z hz
    simp only [hχd]
    rw [pcCut_eq_zero hsq0A (le_of_lt (normSq_lt_of_lt_norm hρ0.le hz)), zero_mul]
  have hχd_eq_zero_gt : ∀ z : ℂ, ρC < ‖z‖ → χd z = 0 := by
    intro z hz
    simp only [hχd]
    rw [pcCutDown_eq_zero hsqBC (le_trans (by nlinarith : ρC ^ 2 ≤ ‖z‖ ^ 2)
      (by rw [← Complex.normSq_eq_norm_sq])), mul_zero]
  have hχd_eq_one : ∀ z : ℂ, ρA ≤ ‖z‖ → ‖z‖ ≤ ρB → χd z = 1 := by
    intro z h1 h2
    simp only [hχd]
    rw [pcCut_eq_one hsq0A (by rw [Complex.normSq_eq_norm_sq]; nlinarith),
      pcCutDown_eq_one hsqBC (by rw [Complex.normSq_eq_norm_sq]; nlinarith), one_mul]
  -- ### 3. the region data
  have hDisc : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → PcDisc M W x τ z := fun z h1 h2 =>
    PcDisc.of_disc hband hWne hM0 hW0 (hρgood z h1) (hxn z) (hτ2 z h2) (hτ3 z h2)
  have hHon : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → PcHon M W x τ z := by
    intro z hz
    have hτ0 : 0 ≤ τ z := by
      rw [hτ1 z hz]
      have : 0 ≤ ‖z‖ - 1 / 2 := by linarith
      positivity
    exact PcHon.of_honest hγ hγne hMval hWval (hxnorm z hz) hτ0
  have hGood : ∀ z : ℂ, ρ ≤ ‖z‖ →
      (0 < pcA M W x τ z ∧ W (x z, τ z) ≠ 0 ∧ Complex.normSq (pcD M W x τ z) < 2) := by
    intro z hz
    by_cases h : (1 / 2 : ℝ) ≤ ‖z‖
    · exact ⟨(hHon z h).pos, (hHon z h).Wne, (hHon z h).Dlt⟩
    · exact ⟨(hDisc z hz (le_of_lt (not_le.mp h))).pos,
        (hDisc z hz (le_of_lt (not_le.mp h))).Wne,
        (hDisc z hz (le_of_lt (not_le.mp h))).Dlt⟩
  have hWsm' : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (pcW M W x τ) z := fun z h1 h2 => (hDisc z h1 h2).dW hMsm hWsm hxsm hτsm
  have hWunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → ‖pcW M W x τ z‖ = 1 :=
    fun z h1 h2 => (hDisc z h1 h2).normW'
  -- ### 4. the argument of the seam loop
  have hMval0 : ∀ y : ℂ, ‖y‖ = 1 → M (y, 0) = Neutral.dataMid γ y 0 := fun y hy => by
    simpa using hMval y 0 le_rfl hy
  have hWval0 : ∀ y : ℂ, ‖y‖ = 1 → W (y, 0) = Neutral.dchW γ (y, 0) := fun y hy => by
    simpa using hWval y 0 le_rfl hy
  have hMne0 : ∀ y : ℂ, ‖y‖ = 1 → M (y, 0) ≠ 0 := fun y hy =>
    hM0 y (by norm_num [hy]) (by norm_num [hy])
  have hWne0 : ∀ y : ℂ, ‖y‖ = 1 → W (y, 0) ≠ 0 := fun y hy =>
    hW0 y (by norm_num [hy]) (by norm_num [hy])
  obtain ⟨θs, hθsc, hθsper, hθs⟩ :=
    seam_periodic_argument γ hγ hγne hU hWrap hMsm hWsm hMval0 hWval0 hMne0 hWne0
      (c := 1) (hc := by norm_num)
  have hθs' : ∀ σ : ℝ, Complex.exp (((θs σ : ℝ) : ℂ) * Complex.I)
      = star (dirDatum M W (Complex.exp (((σ : ℂ) * Complex.I)), 0)) := fun σ => by
    simpa using hθs σ
  have hθseam : ∀ σ : ℝ, Complex.exp (((-(θs σ) : ℝ) : ℂ) * Complex.I)
      = pcW M W x τ (((1 / 2 : ℝ) : ℂ) * Complex.exp (((σ : ℂ) * Complex.I))) := by
    intro σ
    rw [← star_exp_mul_I (θs σ), hθs' σ, star_star]
    exact (pcW_at_seam hx1 hτ1 hM0 hW0 σ).symm
  -- ### 5. transport the argument to the inner circle
  have hθper : Function.Periodic (fun σ : ℝ => -(θs σ)) (2 * Real.pi) := fun σ =>
    by simp only [hθsper σ]
  obtain ⟨θρ, hθρc, hθρper, hθρ⟩ :=
    periodicArgument_annulus_transport (ρ := ρ) (ρ₂ := 1 / 2) hρ0 hρhalf hWsm' hWunit
      hθsc.neg hθper hθseam
  -- ### 6. the global smooth unit field
  obtain ⟨Ω, hΩsm, hΩunit, hΩeq⟩ :=
    smoothUnit_eqOn_annulus_of_periodicArgument (ρ₀ := ρ) (ρ₁ := ρA) (ρ₂ := ρB) (ρ₃ := 1 / 2)
      hρ0 hρ_lt_ρA hρA_lt_ρB hρB_lt_half hWsm' hWunit hθρc hθρper hθρ

  -- ### 7. the descended cap coordinate
  set dc : ℂ → ℂ := fun z => (χd z : ℂ) * pcDc M W x τ z with hdc
  have hdc_le_one : ∀ z : ℂ, ‖dc z‖ ≤ 1 := by
    intro z
    by_cases h : ‖z‖ < 1 / 2
    · by_cases h2 : ‖z‖ < ρ
      · simp only [hdc, hχd_eq_zero_lt z h2, Complex.ofReal_zero, zero_mul]
        norm_num
      · rw [hdc]; simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hχd_nonneg z)]
        have h1 := (hDisc z (le_of_not_gt h2) (le_of_lt h)).dc_le
        have h3 := hχd_le z
        nlinarith [norm_nonneg (pcDc M W x τ z)]
    · simp only [hdc, hχd_eq_zero_gt z (lt_of_lt_of_le hρC_lt_half (le_of_not_gt h)),
        Complex.ofReal_zero, zero_mul]
      norm_num
  have hdc_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dc := by
    rw [contDiff_iff_contDiffAt]
    intro z
    simp only [hdc]
    by_cases h1 : ‖z‖ < ρ
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds z (show (0 : ℝ) < ρ - ‖z‖ by linarith)] with y hy
      have hy' : ‖y - z‖ < ρ - ‖z‖ := by
        have := Metric.mem_ball.mp hy
        rwa [dist_eq_norm] at this
      have hyρ : ‖y‖ < ρ := by
        have h3 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
          conv_lhs => rw [← sub_add_cancel y z]
          exact norm_add_le _ _
        linarith
      rw [hχd_eq_zero_lt y hyρ, Complex.ofReal_zero, zero_mul]
    · by_cases h2 : ‖z‖ < 1 / 2
      · exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp z (hχdsm.contDiffAt)).mul
          ((hDisc z (le_of_not_gt h1) (le_of_lt h2)).dDc hMsm hWsm hxsm hτsm)
      · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [Metric.ball_mem_nhds z
          (show (0 : ℝ) < ‖z‖ - ρC by linarith [not_lt.mp h2, hρC_lt_half])] with y hy
        have hy' : ‖z - y‖ < ‖z‖ - ρC := by
          have := Metric.mem_ball.mp hy
          rwa [dist_comm, dist_eq_norm] at this
        have hyρ : ρC < ‖y‖ := by
          have h3 : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
            conv_lhs => rw [← sub_add_cancel z y]
            exact norm_add_le _ _
          linarith
        rw [hχd_eq_zero_gt y hyρ, Complex.ofReal_zero, zero_mul]
  have hdc_ne_two : ∀ z : ℂ, Complex.normSq (dc z) ≠ 2 := by
    intro z h
    have h1 := hdc_le_one z
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (dc z)]
  -- ### 8. the two halves of the lift
  have hcap_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => capProjVecOf (Ω z) (dc z)) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact pc_contDiffAt_capProjVecOf hΩsm.contDiffAt hdc_sm.contDiffAt (hdc_ne_two z)
  have hconfOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => confProjVecOf (pcU W x τ z) (pcD M W x τ z)) {z : ℂ | ρ < ‖z‖} := by
    intro z hz
    refine (pc_contDiffAt_confProjVecOf ?_ ?_ ?_).contDiffWithinAt
    · exact contDiffAt_pcU hWsm hxsm hτsm (hGood z (le_of_lt hz)).2.1
    · exact contDiffAt_pcD hMsm hWsm hxsm hτsm (hGood z (le_of_lt hz)).1
    · exact ne_of_lt (hGood z (le_of_lt hz)).2.2
  have hV1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => χ z • confProjVecOf (pcU W x τ z) (pcD M W x τ z)) := by
    refine contDiff_of_contDiffOn_union_of_isOpen (𝕜 := ℝ) (E := ℂ) (F := Eucl 3)
      (n := (⊤ : ℕ∞))
      (f := fun z : ℂ => χ z • confProjVecOf (pcU W x τ z) (pcD M W x τ z))
      (s := {z : ℂ | ρ < ‖z‖}) (t := {z : ℂ | ‖z‖ < ρA}) ?_ ?_ ?_ ?_ ?_
    · exact hχsm.contDiffOn.smul hconfOn
    · intro z hz
      refine (contDiffWithinAt_const (c := (0 : Eucl 3))).congr_of_mem ?_ hz
      intro y hy
      rw [hχ_eq_zero y hy, zero_smul]
    · refine Set.eq_univ_of_forall fun z => ?_
      rcases lt_or_ge ‖z‖ ρA with h | h
      · exact Or.inr h
      · exact Or.inl (lt_of_lt_of_le hρ_lt_ρA h)
    · exact isOpen_lt continuous_const continuous_norm
    · exact isOpen_lt continuous_norm continuous_const
  have hV2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => (1 - χ z) • capProjVecOf (Ω z) (dc z)) :=
    (contDiff_const.sub hχsm).smul hcap_sm
  set V : ℂ → Eucl 3 := fun z => χ z • confProjVecOf (pcU W x τ z) (pcD M W x τ z)
      + (1 - χ z) • capProjVecOf (Ω z) (dc z) with hV
  have hV_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V := by
    simp only [hV]
    exact hV1.add hV2
  -- ### 9. the radius
  set r : ℂ → ℝ := fun z => χ z * Real.sqrt (pcA M W x τ z) + (1 - χ z) * 1 with hr
  have hr_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := by
    simp only [hr]
    refine contDiff_of_contDiffOn_union_of_isOpen (𝕜 := ℝ) (E := ℂ) (F := ℝ)
      (n := (⊤ : ℕ∞))
      (f := fun z : ℂ => χ z * Real.sqrt (pcA M W x τ z) + (1 - χ z) * 1)
      (s := {z : ℂ | ρ < ‖z‖}) (t := {z : ℂ | ‖z‖ < ρA}) ?_ ?_ ?_ ?_ ?_
    · refine ((hχsm.contDiffOn).mul ?_).add
        (((contDiff_const.sub hχsm).contDiffOn).mul contDiffOn_const)
      intro z hz
      exact (((Real.contDiffAt_sqrt (ne_of_gt (hGood z (le_of_lt hz)).1)).comp z
        (contDiffAt_pcA hMsm hWsm hxsm hτsm z))).contDiffWithinAt
    · intro z hz
      refine (contDiffWithinAt_const (c := (1 : ℝ))).congr_of_mem ?_ hz
      intro y hy
      simp only [hχ_eq_zero y hy, zero_mul, sub_zero, one_mul, zero_add]
    · refine Set.eq_univ_of_forall fun z => ?_
      rcases lt_or_ge ‖z‖ ρA with h | h
      · exact Or.inr h
      · exact Or.inl (lt_of_lt_of_le hρ_lt_ρA h)
    · exact isOpen_lt continuous_const continuous_norm
    · exact isOpen_lt continuous_norm continuous_const
  -- ### 10. positivity and non-vanishing
  have hrpos : ∀ z : ℂ, 0 < r z := by
    intro z
    by_cases h1 : χ z = 1
    · have hB : ρB ≤ ‖z‖ := le_norm_of_normSq_le hρB_pos.le
        ((pcCut_eq_one_iff hsqAB z).mp (by rw [hχ] at h1; exact h1))
      simp only [hr, h1, one_mul, sub_self, zero_mul, add_zero]
      exact Real.sqrt_pos.mpr (hGood z (le_trans hρ_lt_ρA.le (le_trans (le_of_lt hρA_lt_ρB) hB))).1
    · have hlt : χ z < 1 := lt_of_le_of_ne (hχ_le z) h1
      have hsq := Real.sqrt_nonneg (pcA M W x τ z)
      have hmul : 0 ≤ χ z * Real.sqrt (pcA M W x τ z) := mul_nonneg (hχ_nonneg z) hsq
      simp only [hr]
      nlinarith
  have hVne : ∀ z : ℂ, V z ≠ 0 := by
    intro z
    by_cases h0 : χ z = 0
    · simp only [hV, h0, zero_smul, zero_add, sub_zero, one_smul]
      exact capProjVecOf_ne_zero (hΩunit z) (hdc_le_one z)
    · by_cases h1 : χ z = 1
      · simp only [hV, h1, one_smul, sub_self, zero_smul, add_zero]
        exact confProjVecOf_ne_zero_of_ne
          (pcU_ne_zero (hGood z (le_trans hρ_lt_ρA.le
            (le_of_lt (hχ_ne_zero z h0)))).2.1)
      · have hzA : ρA ≤ ‖z‖ := le_of_lt (hχ_ne_zero z h0)
        have hzB : ‖z‖ ≤ ρB := (hχ_ne_one z h1).le
        have hdi : PcDisc M W x τ z := hDisc z (le_trans hρ_lt_ρA.le hzA)
          (le_trans hzB hρB_lt_half.le)
        have hdcz : dc z = pcDc M W x τ z := by
          simp only [hdc, hχd_eq_one z hzA hzB, Complex.ofReal_one, one_mul]
        have hcap_eq : capProjVecOf (Ω z) (dc z)
            = confProjVecOf (pcU W x τ z) (pcD M W x τ z) := by
          rw [hΩeq z hzA hzB, hdcz]
          exact hdi.reflect
        have hVz : V z = confProjVecOf (pcU W x τ z) (pcD M W x τ z) := by
          simp only [hV, hcap_eq, ← add_smul, add_sub_cancel, one_smul]
        rw [hVz]
        exact confProjVecOf_ne_zero_of_ne (pcU_ne_zero (hGood z (le_trans hρ_lt_ρA.le hzA)).2.1)
  -- ### 11. the pinned values on the annulus
  have hpinned : ∀ z : ℂ, 1 / 2 < ‖z‖ → ‖z‖ ≤ 1 →
      (let A := ‖M (x z, τ z)‖ ^ 2 + τ z * ‖W (x z, τ z)‖ ^ 2
       r z = Real.sqrt A ∧
       V z = confProjVecOf (W (x z, τ z) / ((‖W (x z, τ z)‖ : ℝ) : ℂ))
          (M (x z, τ z) / ((Real.sqrt A : ℝ) : ℂ))) := by
    intro z hz1 hz2
    have hχ1 : χ z = 1 := hχ_eq_one z (le_trans hρB_lt_half.le (le_of_lt hz1))
    have hAeq : pcA M W x τ z = ‖M (x z, τ z)‖ ^ 2 + τ z * ‖W (x z, τ z)‖ ^ 2 := by
      rw [pcA, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    rw [← hAeq]
    refine ⟨?_, ?_⟩
    · simp only [hr, hχ1, one_mul, sub_self, zero_mul, add_zero]
    · simp only [hV, hχ1, one_smul, sub_self, zero_smul, add_zero, pcU_apply, pcD_apply]
  -- ### 12. the cap form on the inner disk
  have hcapform : ∀ z : ℂ, ‖z‖ < 1 / 2 →
      ∃ w dc0 : ℂ, w ≠ 0 ∧ ‖dc0‖ ≤ 1 ∧ V z = capProjVecOf w dc0 := by
    intro z hz
    have hΩne : Ω z ≠ 0 := by
      intro h
      have h1 := hΩunit z
      rw [h, norm_zero] at h1
      norm_num at h1
    by_cases h0 : χ z = 0
    · exact ⟨Ω z, dc z, hΩne, hdc_le_one z, by
        simp only [hV, h0, zero_smul, zero_add, sub_zero, one_smul]⟩
    · have hzA : ρA ≤ ‖z‖ := le_of_lt (hχ_ne_zero z h0)
      have hdi : PcDisc M W x τ z := hDisc z (le_trans hρ_lt_ρA.le hzA) (le_of_lt hz)
      by_cases h1 : χ z = 1
      · refine ⟨pcW M W x τ z, pcDc M W x τ z, hdi.Wne', hdi.dc_le, ?_⟩
        simp only [hV, h1, one_smul, sub_self, zero_smul, add_zero]
        exact hdi.reflect.symm
      · have hzB : ‖z‖ ≤ ρB := (hχ_ne_one z h1).le
        have hdcz : dc z = pcDc M W x τ z := by
          simp only [hdc, hχd_eq_one z hzA hzB, Complex.ofReal_one, one_mul]
        have hcap_eq : capProjVecOf (Ω z) (dc z)
            = confProjVecOf (pcU W x τ z) (pcD M W x τ z) := by
          rw [hΩeq z hzA hzB, hdcz]
          exact hdi.reflect
        refine ⟨Ω z, dc z, hΩne, hdc_le_one z, ?_⟩
        simp only [hV, ← hcap_eq, ← add_smul, add_sub_cancel, one_smul]
  exact ⟨r, V, hr_sm, hV_sm, hrpos, hVne, hpinned, hcapform⟩

end Work.Drive
