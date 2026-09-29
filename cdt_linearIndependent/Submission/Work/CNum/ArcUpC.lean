import Mathlib
import Submission.Work.CNum.ArcSetupC

namespace Work.CNum

open Work.ANum
open Complex Filter
open scoped BigOperators ComplexConjugate Topology

/-- The cusp arc `k = 244`. -/
lemma arc_cuspAC (t : ℝ) (ht : t ∈ Set.Icc ((244 : ℝ) / 1024) (((244 : ℝ) + 1) / 1024)) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t ≤ m2r (Gv 244) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hWA, -, hVA, -⟩ := GridFacts
  have hGv : m2r (Gv 244)
      = max (max (m2r (svUp (ptOf 244))) (m2r (svUp ptCuspA)))
          (max (m2r (svUp (ptOf 245))) (m2r (svUp ptCuspA)))
        + max (m2r (chord1 (dWup (ptOf 244) ptCuspA)))
            (m2r (chord2 (dVup (ptOf 245) ptCuspA))) := by
    rw [Gv244_eq, m2r_add]
    repeat rw [m2r_maxZ]
  rw [hGv]
  set θ : ℝ := 2 * Real.pi * t with hθdef
  have hθlo : arcθ 244 ≤ θ := by
    rw [hθdef]
    exact arcθ_le_of_div (k := 244) (by linarith [ht.1])
  have hθhi : θ ≤ arcθ 245 := by
    rw [hθdef]
    exact le_arcθ_of_div (k := 244) (by linarith [ht.2])
  have harc244_0 : 0 ≤ arcθ 244 := by rw [arcθ]; positivity
  have hIoo : arcθ 244 ∈ Set.Ioo (-alpR) alpR := arcθ_mem_Ioo (le_refl 244)
  rcases lt_or_ge θ alpR with hθα | hθα
  · -- `θ < α`: the `C₁`-side bound
    have hθIoo : θ ∈ Set.Ioo (-alpR) alpR :=
      ⟨by linarith [hθlo, harc244_0, alpR_pos], hθα⟩
    have hlog : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t = Hfun (phiR θ) := by
      rw [circleLog_phiC_eq hθdef, log_h_eq_Hfun hθIoo]
    have hlim : phiR θ ≤ alpR / 2 + 3 * Real.pi / 2 := phiR_le_lim hθα.le
    have haa : phiR (arcθ 244) ≤ phiR θ := phiR_mono hIoo hθIoo hθlo
    have hch := Hfun_chord (le_trans haa hlim) (phiR θ) ⟨haa, hlim⟩
    have hva : Hfun (phiR (arcθ 244)) ≤ m2r (svUp (ptOf 244)) := by
      rw [← log_h_eq_Hfun hIoo]; exact log_h_grid_le 244 (by norm_num)
    have hvb : Hfun (alpR / 2 + 3 * Real.pi / 2) ≤ m2r (svUp ptCuspA) := by
      rw [Hfun_cuspA]; exact log_h_cuspA_le
    have hstep := cuspA_delta_le (d := dWup (ptOf 244) ptCuspA) hWA dist_cuspA
    have h400 : 400 * (alpR / 2 + 3 * Real.pi / 2 - phiR (arcθ 244)) ^ 2
        ≤ m2r (chord1 (dWup (ptOf 244) ptCuspA)) := by
      have hc := chord1_sound (dWup (ptOf 244) ptCuspA) nonneg_dWup244
      have hnn2 : 0 ≤ alpR / 2 + 3 * Real.pi / 2 - phiR (arcθ 244) :=
        sub_nonneg.mpr (phiR_le_lim (le_of_lt arcθ_244_lt_alpR))
      have hsq := pow_le_pow_left₀ hnn2 hstep 2
      exact le_trans (mul_le_mul_of_nonneg_left hsq (by norm_num)) hc
    have hm : max (Hfun (phiR (arcθ 244))) (Hfun (alpR / 2 + 3 * Real.pi / 2))
        ≤ max (m2r (svUp (ptOf 244))) (m2r (svUp ptCuspA)) :=
      max_le (le_trans hva (le_max_left _ _)) (le_trans hvb (le_max_right _ _))
    refine le_trans hlog.le (le_trans (le_trans hch (add_le_add hm h400)) ?_)
    exact add_le_add (le_max_left _ _) (le_max_left _ _)
  · -- `α ≤ θ`
    by_cases hθeq : θ = alpR
    · -- the cusp point itself
      have hval : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t
          = Real.log ‖Submission.CDTPlan.hauptH (zCuspA * ((3 / 4 : ℝ) : ℂ))‖ := by
        have harg : 2 * (Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ)
            = Complex.I * ((alpR : ℝ) : ℂ) := by
          have h' : 2 * Real.pi * t = alpR := by rw [← hθdef]; exact hθeq
          have h2 : t = alpR / (2 * Real.pi) := by
            have h3 : (2 * Real.pi * t) / (2 * Real.pi) = t := by field_simp
            rw [← h3, h']
          rw [h2]
          push_cast
          field_simp
        simp only [Submission.CDTPlan.circleLog, Submission.CDTPlan.phiC, harg, psiC_cuspA]
      refine le_trans hval.le ?_
      refine le_trans log_h_cuspA_le ?_
      exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
        (le_add_of_nonneg_right (le_max_of_le_left nonneg_ch1cuspA))
    · -- `α < θ`: the `C₂`-side bound
      have hθlt : alpR < θ := lt_of_le_of_ne hθα (Ne.symm hθeq)
      have harc245lt : arcθ 245 < 2 * Real.pi - alpR := by
        have h' : arcθ 245 ≤ arcθ 779 := arcθ_mono (by norm_num)
        rw [show arcθ 779 = 2 * Real.pi - arcθ 245 by rw [arcθ, arcθ]; ring] at h'
        linarith [arcθ_245_gt_alpR]
      have hθβlt : θ < 2 * Real.pi - alpR := lt_of_le_of_lt hθhi harc245lt
      have hα245 : alpR < arcθ 245 := arcθ_245_gt_alpR
      have hα245le : alpR ≤ arcθ 245 := hα245.le
      have hα779 : alpR ≤ arcθ 779 := le_of_lt (lt_of_lt_of_le arcθ_245_gt_alpR (arcθ_mono (by norm_num)))
      have hθIoo : θ / 2 ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2) :=
        ⟨by linarith [hθlt], by linarith [hθβlt]⟩
      have h245Ioo : arcθ 245 / 2 ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2) :=
        ⟨by linarith [hα245], by linarith [harc245lt]⟩
      have hψhi : C2Psi (θ / 2) ≤ C2Psi (alpR / 2) := C2Psi_le_left hθIoo.1 hθIoo.2
      have hψhi' : C2Psi (arcθ 245 / 2) ≤ C2Psi (alpR / 2) :=
        C2Psi_le_left h245Ioo.1 h245Ioo.2
      have hlog : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t
          = Jfun (C2Psi (θ / 2) - Real.pi) := by
        rw [circleLog_phiC_eq hθdef]
        rw [show Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ)))
            = wf (C2Psi (θ / 2) - Real.pi) from (wf_Vof_eq hθα hθβlt.le).symm]
        exact (Jfun_eq_log_h (wf_norm_lt_one_of_range (PsiRange hθα hθβlt.le))).symm
      have hra := PsiRange (le_trans hα245le (arcθ_mono (by norm_num))) harc245lt.le
      have hrb := PsiRange (le_refl alpR) (by linarith [hα245, harc245lt])
      have hab : C2Psi (arcθ 245 / 2) - Real.pi ≤ C2Psi (alpR / 2) - Real.pi :=
        sub_le_sub_right hψhi' _
      have hψmem : C2Psi (θ / 2) - Real.pi ∈ Set.Icc (C2Psi (arcθ 245 / 2) - Real.pi)
          (C2Psi (alpR / 2) - Real.pi) := by
        refine ⟨?_, sub_le_sub_right hψhi _⟩
        rcases eq_or_lt_of_le hθhi with h2 | h2
        · rw [h2]
        · exact sub_le_sub_right (le_of_lt (C2_Psi_antitone hθIoo h245Ioo (by linarith))) _
      have hva : Jfun (C2Psi (arcθ 245 / 2) - Real.pi) ≤ m2r (svUp (ptOf 245)) := by
        rw [Jfun_eq_log_h (wf_norm_lt_one_of_range hra),
          wf_Vof_eq (le_trans hα245le (arcθ_mono (by norm_num))) harc245lt.le]
        exact log_h_grid_le 245 (by norm_num)
      have hvb : Jfun (C2Psi (alpR / 2) - Real.pi) ≤ m2r (svUp ptCuspA) := by
        rw [Jfun_eq_log_h (wf_norm_lt_one_of_range hrb),
          wf_Vof_eq (le_refl alpR) (by linarith [hα245, harc245lt]), psiC_cuspA]
        exact log_h_cuspA_le
      have hD2 : (143 / 115) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 245 : ℝ) : ℂ)))
          - Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((alpR : ℝ) : ℂ)))‖
          ≤ m2r (dVup (ptOf 245) ptCuspA) := by
        rw [psiC_cuspA]
        exact dist_cuspA2
      have hstep := psiChord_le (le_refl alpR) (by linarith [hα245, harc245lt])
        hα245le hD2 hVA
      have h1000 : 1000 * (C2Psi (alpR / 2) - Real.pi - (C2Psi (arcθ 245 / 2) - Real.pi)) ^ 2
          ≤ m2r (chord2 (dVup (ptOf 245) ptCuspA)) := by
        have h0 : C2Psi (alpR / 2) - Real.pi - (C2Psi (arcθ 245 / 2) - Real.pi)
            = C2Psi (alpR / 2) - C2Psi (arcθ 245 / 2) := by ring
        rw [h0]
        have hc := chord2_sound (dVup (ptOf 245) ptCuspA) nonneg_dVup245
        have hnn2 : 0 ≤ C2Psi (alpR / 2) - C2Psi (arcθ 245 / 2) := sub_nonneg.mpr hψhi'
        have hsq := pow_le_pow_left₀ hnn2 hstep 2
        exact le_trans (mul_le_mul_of_nonneg_left hsq (by norm_num)) hc
      have hm : max (Jfun (C2Psi (arcθ 245 / 2) - Real.pi))
          (Jfun (C2Psi (alpR / 2) - Real.pi))
          ≤ max (m2r (svUp (ptOf 245))) (m2r (svUp ptCuspA)) :=
        max_le (le_trans hva (le_max_left _ _)) (le_trans hvb (le_max_right _ _))
      refine le_trans hlog.le (le_trans (le_trans (Jfun_chord hab hra.1 hrb.2 _ hψmem)
        (add_le_add hm h1000)) ?_)
      exact add_le_add (le_max_right _ _) (le_max_right _ _)

/-- The cusp arc `k = 779`. -/
lemma arc_cuspBC (t : ℝ) (ht : t ∈ Set.Icc ((779 : ℝ) / 1024) (((779 : ℝ) + 1) / 1024)) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t ≤ m2r (Gv 779) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hWB, -, hVB⟩ := GridFacts
  have hGv : m2r (Gv 779)
      = max (max (m2r (svUp (ptOf 779))) (m2r (svUp ptCuspB)))
          (max (m2r (svUp (ptOf 780))) (m2r (svUp ptCuspB)))
        + max (m2r (chord2 (dVup (ptOf 779) ptCuspB)))
            (m2r (chord1 (dWup (ptOf 780) ptCuspB))) := by
    rw [Gv779_eq, m2r_add]
    repeat rw [m2r_maxZ]
  rw [hGv]
  set θ : ℝ := 2 * Real.pi * t with hθdef
  have hθlo : arcθ 779 ≤ θ := by
    rw [hθdef]
    exact arcθ_le_of_div (k := 779) (by linarith [ht.1])
  have hθhi : θ ≤ arcθ 780 := by
    rw [hθdef]
    exact le_arcθ_of_div (k := 779) (by linarith [ht.2])
  have hα779 : alpR < arcθ 779 := by
    have h' : arcθ 779 = 2 * Real.pi - arcθ 245 := by rw [arcθ, arcθ]; ring
    have hπ : arcθ 245 < Real.pi := by rw [arcθ]; nlinarith [Real.pi_pos]
    rw [h']
    linarith [arcθ_245_gt_alpR, alpR_lt_pi]
  have harc779lt : arcθ 779 < 2 * Real.pi - alpR := by
    have h' : arcθ 779 = 2 * Real.pi - arcθ 245 := by rw [arcθ, arcθ]; ring
    rw [h']
    linarith [arcθ_245_gt_alpR]
  have h779Ioo : arcθ 779 / 2 ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2) :=
    ⟨by linarith [hα779], by linarith [harc779lt]⟩
  have hα779le : alpR ≤ arcθ 779 := hα779.le
  by_cases hθβ : θ ≤ 2 * Real.pi - alpR
  · by_cases hθβeq : θ = 2 * Real.pi - alpR
    · -- the cusp point itself
      have hval : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t
          = Real.log ‖Submission.CDTPlan.hauptH (zCuspB * ((3 / 4 : ℝ) : ℂ))‖ := by
        have harg : 2 * (Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ)
            = Complex.I * (((2 * Real.pi - alpR : ℝ)) : ℂ) := by
          have h' : 2 * Real.pi * t = 2 * Real.pi - alpR := by rw [← hθdef]; exact hθβeq
          have h2 : t = (2 * Real.pi - alpR) / (2 * Real.pi) := by
            have h3 : (2 * Real.pi * t) / (2 * Real.pi) = t := by field_simp
            rw [← h3, h']
          rw [h2]
          push_cast
          field_simp
        simp only [Submission.CDTPlan.circleLog, Submission.CDTPlan.phiC, harg, psiC_cuspB_real]
      refine le_trans hval.le ?_
      refine le_trans log_h_cuspB_le ?_
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_add_of_nonneg_right (le_max_of_le_left nonneg_ch2cuspB))
    · -- `θ < 2π - α`
      have hθβlt : θ < 2 * Real.pi - alpR := lt_of_le_of_ne hθβ hθβeq
      have hθIoo : θ / 2 ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2) :=
        ⟨by linarith [hα779le, hθlo], by linarith [hθβlt]⟩
      have hlog : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t
          = Jfun (C2Psi (θ / 2) - Real.pi) := by
        rw [circleLog_phiC_eq hθdef]
        rw [show Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ)))
            = wf (C2Psi (θ / 2) - Real.pi) from
          (wf_Vof_eq (θ := θ) (lt_of_lt_of_le hα779 hθlo).le hθβlt.le).symm]
        exact (Jfun_eq_log_h (wf_norm_lt_one_of_range
          (PsiRange (lt_of_lt_of_le hα779 hθlo).le hθβlt.le))).symm
      have hra : (-3.9 : ℝ) ≤ C2Psi (Real.pi - alpR / 2) - Real.pi := by
        have h := (PsiRange (by linarith [alpR_lt_pi]) (le_refl (2 * Real.pi - alpR))).1
        rwa [show (2 * Real.pi - alpR) / 2 = Real.pi - alpR / 2 by ring] at h
      have hra779 : (-3.9 : ℝ) ≤ C2Psi (arcθ 779 / 2) - Real.pi :=
        (PsiRange (le_trans hα779le (arcθ_mono (by norm_num))) harc779lt.le).1
      have hrb : C2Psi (arcθ 779 / 2) - Real.pi ≤ -2.39 :=
        (PsiRange (le_trans hα779le (arcθ_mono (by norm_num))) harc779lt.le).2
      have hπc : C2Psi (Real.pi - alpR / 2) ≤ C2Psi (arcθ 779 / 2) :=
        C2Psi_le_right h779Ioo.1 h779Ioo.2
      have hab : C2Psi (Real.pi - alpR / 2) - Real.pi ≤ C2Psi (arcθ 779 / 2) - Real.pi :=
        sub_le_sub_right hπc _
      have hψmem : C2Psi (θ / 2) - Real.pi ∈ Set.Icc (C2Psi (Real.pi - alpR / 2) - Real.pi)
          (C2Psi (arcθ 779 / 2) - Real.pi) := by
        refine ⟨sub_le_sub_right (C2Psi_le_right hθIoo.1 hθIoo.2) _, ?_⟩
        rcases eq_or_lt_of_le hθlo with h2 | h2
        · rw [h2]
        · exact sub_le_sub_right
            (le_of_lt (C2_Psi_antitone h779Ioo hθIoo (by linarith))) _
      have hva : Jfun (C2Psi (Real.pi - alpR / 2) - Real.pi) ≤ m2r (svUp ptCuspB) := by
        have heq : C2Psi (Real.pi - alpR / 2) - Real.pi
            = C2Psi ((2 * Real.pi - alpR) / 2) - Real.pi := by
          rw [show (2 * Real.pi - alpR) / 2 = Real.pi - alpR / 2 by ring]
        rw [heq, Jfun_eq_log_h (wf_norm_lt_one_of_range
            (PsiRange (by linarith [alpR_lt_pi]) (le_refl (2 * Real.pi - alpR)))),
          wf_Vof_eq (by linarith [alpR_lt_pi]) (le_refl _), psiC_cuspB_real]
        exact log_h_cuspB_le
      have hvb : Jfun (C2Psi (arcθ 779 / 2) - Real.pi) ≤ m2r (svUp (ptOf 779)) := by
        rw [Jfun_eq_log_h (wf_norm_lt_one_of_range ⟨hra779, hrb⟩),
          wf_Vof_eq (le_trans hα779le (arcθ_mono (by norm_num))) harc779lt.le]
        exact log_h_grid_le 779 (by norm_num)
      have hDb : (143 / 115) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (((2 * Real.pi - alpR : ℝ)) : ℂ)))
          - Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 779 : ℝ) : ℂ)))‖
          ≤ m2r (dVup (ptOf 779) ptCuspB) := by
        rw [psiC_cuspB_real]
        simpa only [norm_sub_rev] using dist_cuspB
      have hstep : C2Psi (arcθ 779 / 2) - C2Psi (Real.pi - alpR / 2)
          ≤ m2r (dVup (ptOf 779) ptCuspB) + (m2r (dVup (ptOf 779) ptCuspB)) ^ 3 / 12
            + 4096 / (SC : ℝ) := by
        have h := psiChord_le hα779le (by linarith [alpR_lt_pi]) harc779lt.le hDb hVB
        rwa [show (2 * Real.pi - alpR) / 2 = Real.pi - alpR / 2 by ring] at h
      have h1000 : 1000 * (C2Psi (arcθ 779 / 2) - Real.pi - (C2Psi (Real.pi - alpR / 2) - Real.pi)) ^ 2
          ≤ m2r (chord2 (dVup (ptOf 779) ptCuspB)) := by
        have h0 : C2Psi (arcθ 779 / 2) - Real.pi - (C2Psi (Real.pi - alpR / 2) - Real.pi)
            = C2Psi (arcθ 779 / 2) - C2Psi (Real.pi - alpR / 2) := by ring
        rw [h0]
        have hc := chord2_sound (dVup (ptOf 779) ptCuspB) nonneg_dVup779
        have hnn2 : 0 ≤ C2Psi (arcθ 779 / 2) - C2Psi (Real.pi - alpR / 2) := sub_nonneg.mpr hπc
        have hsq := pow_le_pow_left₀ hnn2 hstep 2
        exact le_trans (mul_le_mul_of_nonneg_left hsq (by norm_num)) hc
      have hm : max (Jfun (C2Psi (Real.pi - alpR / 2) - Real.pi))
          (Jfun (C2Psi (arcθ 779 / 2) - Real.pi))
          ≤ max (m2r (svUp (ptOf 779))) (m2r (svUp ptCuspB)) :=
        max_le (le_trans hva (le_max_right _ _)) (le_trans hvb (le_max_left _ _))
      refine le_trans hlog.le (le_trans (le_trans (Jfun_chord hab hra hrb _ hψmem)
        (add_le_add hm h1000)) ?_)
      exact add_le_add (le_max_left _ _) (le_max_left _ _)
  · -- `2π - α < θ`: reflect onto the first arc
    have hθβ' : 2 * Real.pi - alpR < θ := lt_of_not_ge hθβ
    set θ' : ℝ := 2 * Real.pi - θ with hθ'def
    have hθ'lo : arcθ 244 ≤ θ' := by
      have h1 : arcθ 244 = 2 * Real.pi - arcθ 780 := by
        rw [show (244 : ℕ) = 1024 - 780 by norm_num, arcθ_sub 780 (by norm_num)]
      rw [hθ'def, h1]
      linarith [hθhi]
    have hθ'lt : θ' < alpR := by rw [hθ'def]; linarith
    have hθoc : θ ∈ Set.Ioc (2 * Real.pi - alpR) (2 * Real.pi) := by
      refine ⟨hθβ', ?_⟩
      have h : θ ≤ arcθ 1024 := le_trans hθhi (arcθ_mono (by omega))
      rwa [arcθ_1024] at h
    have hIoo : arcθ 244 ∈ Set.Ioo (-alpR) alpR := arcθ_mem_Ioo (le_refl 244)
    have hlim : phiR θ' ≤ alpR / 2 + 3 * Real.pi / 2 := phiR_le_lim hθ'lt.le
    have hθIoo' : θ' ∈ Set.Ioo (-alpR) alpR := ⟨by linarith [hθ'lo, hIoo.1], hθ'lt⟩
    have haa : phiR (arcθ 244) ≤ phiR θ' := phiR_mono hIoo hθIoo' hθ'lo
    have hch := Hfun_chord (le_trans haa hlim) (phiR θ') ⟨haa, hlim⟩
    have hθ244eq : arcθ 244 = 2 * Real.pi - arcθ 780 := by
      rw [show (244 : ℕ) = 1024 - 780 by norm_num, arcθ_sub 780 (by norm_num)]
    have hθoc780 : arcθ 780 ∈ Set.Ioc (2 * Real.pi - alpR) (2 * Real.pi) := by
      refine ⟨?_, ?_⟩
      · have h' : arcθ 780 = 2 * Real.pi - arcθ 244 := arcθ_sub 244 (by norm_num)
        rw [h']; linarith [arcθ_244_lt_alpR]
      · have h : arcθ 780 ≤ arcθ 1024 := arcθ_mono (by norm_num)
        rwa [arcθ_1024] at h
    have hconj780 : Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 244 : ℝ) : ℂ)))
        = conj (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 780 : ℝ) : ℂ)))) := by
      rw [hθ244eq]; exact (psiC_conj_eq hθoc780).symm
    have hva : Hfun (phiR (arcθ 244)) ≤ m2r (svUp (ptOf 780)) := by
      rw [← log_h_eq_Hfun hIoo]
      rw [hconj780, log_h_conj (norm_psiC_lt_one (arcθ 780))]
      exact log_h_grid_le 780 (by norm_num)
    have hvb : Hfun (alpR / 2 + 3 * Real.pi / 2) ≤ m2r (svUp ptCuspB) := by
      rw [Hfun_cuspA, cuspA_eq_conj_cuspB, log_h_conj norm_cuspB_lt_one]
      exact log_h_cuspB_le
    have hconj780' : Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 780 : ℝ) : ℂ)))
        = conj (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 244 : ℝ) : ℂ)))) := by
      have hh := congrArg conj hconj780
      simpa using hh.symm
    have hD : (4 / 3) * ‖zCuspA * ((3 / 4 : ℝ) : ℂ)
        - Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 244 : ℝ) : ℂ)))‖
        ≤ m2r (dWup (ptOf 780) ptCuspB) := by
      have h := dist_cuspB2
      rw [hconj780', ← conj_cuspA, ← map_sub, Complex.norm_conj] at h
      simpa only [norm_sub_rev] using h
    have hstep := cuspA_delta_le (d := dWup (ptOf 780) ptCuspB) hWB hD
    have h400 : 400 * (alpR / 2 + 3 * Real.pi / 2 - phiR (arcθ 244)) ^ 2
        ≤ m2r (chord1 (dWup (ptOf 780) ptCuspB)) := by
      have hc := chord1_sound (dWup (ptOf 780) ptCuspB) nonneg_dWup780
      have hnn2 : 0 ≤ alpR / 2 + 3 * Real.pi / 2 - phiR (arcθ 244) :=
        sub_nonneg.mpr (phiR_le_lim (le_of_lt arcθ_244_lt_alpR))
      have hsq := pow_le_pow_left₀ hnn2 hstep 2
      exact le_trans (mul_le_mul_of_nonneg_left hsq (by norm_num)) hc
    have hm : max (Hfun (phiR (arcθ 244))) (Hfun (alpR / 2 + 3 * Real.pi / 2))
        ≤ max (m2r (svUp (ptOf 780))) (m2r (svUp ptCuspB)) :=
      max_le (le_trans hva (le_max_left _ _)) (le_trans hvb (le_max_right _ _))
    have hcusp : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t = Hfun (phiR θ') := by
      rw [circleLog_phiC_eq hθdef]
      rw [show Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ)))
          = conj (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ' : ℂ)))) from by
        rw [hθ'def]; exact psiC_arc4_conj hθoc]
      rw [log_h_conj (norm_psiC_lt_one θ')]
      exact log_h_eq_Hfun hθIoo'
    refine le_trans hcusp.le (le_trans (le_trans hch (add_le_add hm h400)) ?_)
    exact add_le_add (le_max_right _ _) (le_max_right _ _)

/-- **The assignment.** `circleLog phiC ≤ Gv k` on the `k`-th arc of the certified subdivision. -/
theorem ArcUpC (k : ℕ) (hk : k < 1024) :
    ∀ t ∈ Set.Icc ((k : ℝ) / 1024) (((k : ℝ) + 1) / 1024),
      Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t ≤ Work.ANum.m2r (Work.CNum.Gv k) := by
  intro t ht
  by_cases h1 : k ≤ 243
  · exact arc_bound_C1 k h1 t ht
  · by_cases h2 : k = 244
    · subst h2
      exact arc_cuspAC t (by simpa using ht)
    · have h2' : 245 ≤ k := by omega
      by_cases h3 : k ≤ 778
      · exact arc_bound_C2 k h2' h3 t ht
      · by_cases h4 : k = 779
        · subst h4
          exact arc_cuspBC t (by simpa using ht)
        · exact arc_bound_C1b k (by omega) (by omega) t ht

end Work.CNum
