import Mathlib
import Submission.Work.WilC4.ProfileDefs
import Submission.Work.WilC4.base_est

namespace Work.WilC4

open Set

theorem cand_base (P : ℕ) (ρ τ β : ℝ) (hρ : 0 < ρ) (hτ0 : 0 ≤ τ) (hτρ : 2 * τ ≤ ρ)
    (hβ : 2 ^ (P + 1) ≤ β)
    (G : ℝ → ℝ) (hcont : ContinuousOn G (Set.Icc 1 β))
    (hpos : ∀ s ∈ Set.Icc 1 β, 0 < G s) (hmono : Work.WilC4.PieceMonoOn G P β)
    (hdoub : ∀ s ∈ Set.Icc 1 (β / 2), |G (2 * s) / G s - ρ| ≤ τ) :
    ∀ t ∈ Set.Icc 1 2,
      G t ≤ 2 ^ (2 * P + 1) * max ρ ρ⁻¹ * G 1 ∧
      G 1 ≤ 2 ^ (2 * P + 1) * max ρ ρ⁻¹ * G t := by
  have hρτ : 0 < ρ - τ := by linarith
  have hτρ' : τ ≤ ρ := by linarith
  have hratio_ge1 : 1 ≤ (ρ + τ) / (ρ - τ) := by
    rw [le_div_iff₀ hρτ]; linarith
  have hratio_pos : 0 < (ρ + τ) / (ρ - τ) := lt_of_lt_of_le one_pos hratio_ge1
  have hratio_nonneg : 0 ≤ (ρ + τ) / (ρ - τ) := le_of_lt hratio_pos
  -- decay-factor bound `(ρ+τ)/(ρ-τ) ≤ 4`
  have hR4 : ((ρ + τ) / (ρ - τ)) ^ P ≤ (4 : ℝ) ^ P := by
    have h4 : (ρ + τ) / (ρ - τ) ≤ 4 := by rw [div_le_iff₀ hρτ]; linarith
    exact pow_le_pow_left₀ hratio_nonneg h4 P
  -- constant bound `max ((ρ-τ)⁻¹) (ρ+τ) ≤ 2 max ρ ρ⁻¹`
  have hK : max ((ρ - τ)⁻¹) (ρ + τ) ≤ 2 * max ρ ρ⁻¹ := by
    apply max_le
    · have h2 : (ρ - τ)⁻¹ ≤ 2 * ρ⁻¹ := by
        have h2' : (ρ - τ)⁻¹ ≤ (ρ / 2)⁻¹ :=
          (inv_le_inv₀ hρτ (by positivity)).mpr (by linarith)
        rw [show (ρ / 2)⁻¹ = 2 * ρ⁻¹ by rw [inv_div, div_eq_mul_inv]] at h2'
        exact h2'
      have h3 : ρ⁻¹ ≤ max ρ ρ⁻¹ := le_max_right _ _
      linarith
    · have h1 : ρ ≤ max ρ ρ⁻¹ := le_max_left _ _
      linarith
  have hKnonneg : 0 ≤ max ((ρ - τ)⁻¹) (ρ + τ) := by
    have : (0 : ℝ) < ρ + τ := by linarith
    exact le_trans this.le (le_max_right _ _)
  have hCbound : max ((ρ - τ)⁻¹) (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ P
      ≤ 2 ^ (2 * P + 1) * max ρ ρ⁻¹ := by
    have hmnn : 0 ≤ max ρ ρ⁻¹ := le_trans hρ.le (le_max_left _ _)
    have h4P : (4 : ℝ) ^ P = 2 ^ (2 * P) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    have h2P : (2 : ℝ) * 2 ^ (2 * P) = 2 ^ (2 * P + 1) := by
      rw [mul_comm, ← pow_succ]
    calc max ((ρ - τ)⁻¹) (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ P
        ≤ (2 * max ρ ρ⁻¹) * (4 : ℝ) ^ P :=
          mul_le_mul hK hR4 (pow_nonneg hratio_nonneg P)
            (mul_nonneg (by norm_num) hmnn)
      _ = 2 ^ (2 * P + 1) * max ρ ρ⁻¹ := by
          rw [h4P, ← h2P]; ring
  have h1β : (1 : ℝ) ≤ β := le_trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hβ
  have h2β : (2 : ℝ) ≤ β := by
    have h : (2 : ℝ) ^ (1 : ℕ) ≤ (2 : ℝ) ^ (P + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    simpa using le_trans h hβ
  have key : ∀ t ∈ Set.Icc 1 2,
      G t ≤ (max ((ρ - τ)⁻¹) (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ P) * G 1 ∧
      G 1 ≤ (max ((ρ - τ)⁻¹) (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ P) * G t := by
    intro t ht
    obtain ⟨B, hBcard, hBanti⟩ := hmono
    obtain ⟨j, hjmem, hfree⟩ := base_est_slot_free B P hBcard
    have hjle : j ≤ P := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have h1le2j : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have h2j_lt : (2 : ℝ) ^ j < (2 : ℝ) ^ (j + 1) := by
      rw [pow_succ]; nlinarith [h2pos]
    have h2j1_le : (2 : ℝ) ^ (j + 1) ≤ β := by
      calc (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (P + 1) :=
            pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
        _ ≤ β := hβ
    have h2j_le : (2 : ℝ) ^ j ≤ β := le_trans h2j_lt.le h2j1_le
    have ht_le : (2 : ℝ) ^ j * t ≤ (2 : ℝ) ^ (j + 1) := by
      rw [pow_succ]; exact mul_le_mul_of_nonneg_left ht.2 h2pos.le
    have ht_ge : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ j * t := by
      simpa using mul_le_mul_of_nonneg_left ht.1 h2pos.le
    have h2jt_le_β : (2 : ℝ) ^ j * t ≤ β := le_trans ht_le h2j1_le
    have hfree' : ∀ x ∈ Ioo ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)), x ∉ B :=
      fun x hx hxB => hfree x hxB ⟨hx.1, hx.2⟩
    have hmono0 := hBanti ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)) h1le2j h2j1_le h2j_lt hfree'
    have hcontIcc : ContinuousOn G (Icc ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1))) :=
      hcont.mono (fun x hx => ⟨le_trans h1le2j hx.1, le_trans hx.2 h2j1_le⟩)
    have hmonoIcc := base_est_monoOrAnti_Icc h2j_lt hmono0 hcontIcc
    have hG1pos : 0 < G 1 := hpos 1 ⟨le_refl 1, h1β⟩
    have hGtpos : 0 < G t := hpos t ⟨ht.1, le_trans ht.2 h2β⟩
    have hpj : 0 < (ρ - τ) ^ j := pow_pos hρτ j
    have hlo_t : (ρ - τ) ^ j * G t ≤ G ((2 : ℝ) ^ j * t) :=
      (chain_bound G ρ τ β hτ0 hτρ' hpos hdoub j t ht.1 h2jt_le_β).1
    have hhi_t : G ((2 : ℝ) ^ j * t) ≤ (ρ + τ) ^ j * G t :=
      (chain_bound G ρ τ β hτ0 hτρ' hpos hdoub j t ht.1 h2jt_le_β).2
    have hlo_1 : (ρ - τ) ^ j * G 1 ≤ G ((2 : ℝ) ^ j) := by
      simpa using
        (chain_bound G ρ τ β hτ0 hτρ' hpos hdoub j 1 le_rfl (by simpa using h2j_le)).1
    have hhi_1 : G ((2 : ℝ) ^ j) ≤ (ρ + τ) ^ j * G 1 := by
      simpa using
        (chain_bound G ρ τ β hτ0 hτρ' hpos hdoub j 1 le_rfl (by simpa using h2j_le)).2
    have hlo_1' : (ρ - τ) ^ (j + 1) * G 1 ≤ G ((2 : ℝ) ^ (j + 1)) := by
      simpa using
        (chain_bound G ρ τ β hτ0 hτρ' hpos hdoub (j + 1) 1 le_rfl
          (by simpa using h2j1_le)).1
    have hhi_1' : G ((2 : ℝ) ^ (j + 1)) ≤ (ρ + τ) ^ (j + 1) * G 1 := by
      simpa using
        (chain_bound G ρ τ β hτ0 hτρ' hpos hdoub (j + 1) 1 le_rfl
          (by simpa using h2j1_le)).2
    have hKge1 : 1 ≤ max ((ρ - τ)⁻¹) (ρ + τ) := by
      rcases le_or_gt 1 (ρ + τ) with h | h
      · exact le_trans h (le_max_right _ _)
      · refine le_trans (le_of_lt ?_) (le_max_left _ _)
        rw [one_lt_inv₀ hρτ]; linarith
    rcases hmonoIcc with hinc | hdec
    · -- increasing on the free window
      have hstep1 : G ((2 : ℝ) ^ j * t) ≤ G ((2 : ℝ) ^ (j + 1)) :=
        hinc ⟨ht_ge, ht_le⟩ (right_mem_Icc.mpr h2j_lt.le) ht_le
      have hstep2 : G ((2 : ℝ) ^ j) ≤ G ((2 : ℝ) ^ j * t) :=
        hinc (left_mem_Icc.mpr h2j_lt.le) ⟨ht_ge, ht_le⟩ ht_ge
      constructor
      · have hGt : G t ≤ (ρ + τ) ^ (j + 1) * G 1 / (ρ - τ) ^ j := by
          rw [le_div_iff₀' hpj]
          calc (ρ - τ) ^ j * G t ≤ G ((2 : ℝ) ^ j * t) := hlo_t
            _ ≤ G ((2 : ℝ) ^ (j + 1)) := hstep1
            _ ≤ (ρ + τ) ^ (j + 1) * G 1 := hhi_1'
        have hkey : (ρ + τ) ^ (j + 1) * G 1 / (ρ - τ) ^ j
            = (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ j * G 1 := by
          rw [pow_succ, div_pow]; ring
        refine le_trans (le_trans hGt (le_of_eq hkey)) ?_
        have hfac : (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ j
            ≤ max ((ρ - τ)⁻¹) (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ P :=
          mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hratio_ge1 hjle)
            (pow_nonneg hratio_nonneg j) hKnonneg
        exact mul_le_mul_of_nonneg_right hfac hG1pos.le
      · have hG1 : G 1 ≤ (ρ + τ) ^ j * G t / (ρ - τ) ^ j := by
          rw [le_div_iff₀' hpj]
          calc (ρ - τ) ^ j * G 1 ≤ G ((2 : ℝ) ^ j) := hlo_1
            _ ≤ G ((2 : ℝ) ^ j * t) := hstep2
            _ ≤ (ρ + τ) ^ j * G t := hhi_t
        have hkey : (ρ + τ) ^ j * G t / (ρ - τ) ^ j
            = ((ρ + τ) / (ρ - τ)) ^ j * G t := by
          rw [div_pow, div_mul_eq_mul_div]
        refine le_trans (le_trans hG1 (le_of_eq hkey)) ?_
        have hfac : ((ρ + τ) / (ρ - τ)) ^ j
            ≤ max ((ρ - τ)⁻¹) (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ P :=
          le_trans (pow_le_pow_right₀ hratio_ge1 hjle)
            (le_mul_of_one_le_left (pow_nonneg hratio_nonneg P) hKge1)
        exact mul_le_mul_of_nonneg_right hfac hGtpos.le
    · -- decreasing on the free window
      constructor
      · have hstep : G ((2 : ℝ) ^ j * t) ≤ G ((2 : ℝ) ^ j) :=
          hdec (left_mem_Icc.mpr h2j_lt.le) ⟨ht_ge, ht_le⟩ ht_ge
        have hGt : G t ≤ (ρ + τ) ^ j * G 1 / (ρ - τ) ^ j := by
          rw [le_div_iff₀' hpj]
          calc (ρ - τ) ^ j * G t ≤ G ((2 : ℝ) ^ j * t) := hlo_t
            _ ≤ G ((2 : ℝ) ^ j) := hstep
            _ ≤ (ρ + τ) ^ j * G 1 := hhi_1
        have hkey : (ρ + τ) ^ j * G 1 / (ρ - τ) ^ j
            = ((ρ + τ) / (ρ - τ)) ^ j * G 1 := by
          rw [div_pow, div_mul_eq_mul_div]
        refine le_trans (le_trans hGt (le_of_eq hkey)) ?_
        have hfac : ((ρ + τ) / (ρ - τ)) ^ j
            ≤ max ((ρ - τ)⁻¹) (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ P :=
          le_trans (pow_le_pow_right₀ hratio_ge1 hjle)
            (le_mul_of_one_le_left (pow_nonneg hratio_nonneg P) hKge1)
        exact mul_le_mul_of_nonneg_right hfac hG1pos.le
      · have hstep : G ((2 : ℝ) ^ (j + 1)) ≤ G ((2 : ℝ) ^ j * t) :=
          hdec ⟨ht_ge, ht_le⟩ (right_mem_Icc.mpr h2j_lt.le) ht_le
        have hcore : (ρ - τ) ^ (j + 1) * G 1 ≤ (ρ + τ) ^ j * G t := by
          calc (ρ - τ) ^ (j + 1) * G 1 ≤ G ((2 : ℝ) ^ (j + 1)) := hlo_1'
            _ ≤ G ((2 : ℝ) ^ j * t) := hstep
            _ ≤ (ρ + τ) ^ j * G t := hhi_t
        have hG1 : G 1 ≤ (((ρ + τ) / (ρ - τ)) ^ j * (ρ - τ)⁻¹) * G t := by
          have ha : 0 < (ρ - τ) ^ (j + 1) := pow_pos hρτ (j + 1)
          have hgoal : ((ρ + τ) / (ρ - τ)) ^ j * (ρ - τ)⁻¹
              = (ρ + τ) ^ j / (ρ - τ) ^ (j + 1) := by
            rw [pow_succ, div_pow]; field_simp
          rw [hgoal, div_mul_eq_mul_div, le_div_iff₀' ha]
          exact hcore
        have hfac0 : ((ρ + τ) / (ρ - τ)) ^ j * (ρ - τ)⁻¹
            ≤ ((ρ + τ) / (ρ - τ)) ^ P * max ((ρ - τ)⁻¹) (ρ + τ) :=
          mul_le_mul (pow_le_pow_right₀ hratio_ge1 hjle) (le_max_left _ _)
            (inv_nonneg.mpr hρτ.le) (pow_nonneg hratio_nonneg P)
        have hfac : ((ρ + τ) / (ρ - τ)) ^ j * (ρ - τ)⁻¹
            ≤ max ((ρ - τ)⁻¹) (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ P :=
          hfac0.trans (le_of_eq (mul_comm _ _))
        exact le_trans hG1 (mul_le_mul_of_nonneg_right hfac hGtpos.le)
  intro t ht
  obtain ⟨h1, h2⟩ := key t ht
  have hG1pos : 0 < G 1 := hpos 1 ⟨le_refl 1, h1β⟩
  have hGtpos : 0 < G t := hpos t ⟨ht.1, le_trans ht.2 h2β⟩
  refine ⟨?_, ?_⟩
  · calc G t ≤ (max ((ρ - τ)⁻¹) (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ P) * G 1 := h1
      _ ≤ (2 ^ (2 * P + 1) * max ρ ρ⁻¹) * G 1 :=
          mul_le_mul_of_nonneg_right hCbound hG1pos.le
  · calc G 1 ≤ (max ((ρ - τ)⁻¹) (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ P) * G t := h2
      _ ≤ (2 ^ (2 * P + 1) * max ρ ρ⁻¹) * G t :=
          mul_le_mul_of_nonneg_right hCbound hGtpos.le

end Work.WilC4
