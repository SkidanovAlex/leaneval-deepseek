import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDesign
import Submission.Work.Drive.EpsForm.waypoint_levels

namespace Work.Drive.EpsForm

open Set

noncomputable section

/-! ## Elementary trigonometric inputs

The waypoint profile meets the unit circle of the tube coordinates exactly at the two chord
waypoints `W₂, W₃`; the analysis reduces to two trigonometric inequalities, one for the chord
range (`|t/2| ≤ π/3`, so `cos (t/2) ≥ 1/2`) and one outside it (`|t| ≥ 2π/3`, so `cos t ≤ -1/2`). -/

lemma cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]

lemma half_le_cos_of_abs_le {x : ℝ} (h : |x| ≤ Real.pi / 3) : (1 : ℝ) / 2 ≤ Real.cos x := by
  have h1 := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) (by linarith [Real.pi_pos]) h
  rwa [Real.cos_pi_div_three, Real.cos_abs] at h1

lemma cos_le_neg_half_of_ge {t : ℝ} (h : 2 * Real.pi / 3 ≤ t) (h' : t ≤ Real.pi) :
    Real.cos t ≤ -(1 / 2) := by
  have h1 := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) h' h
  rwa [cos_two_pi_div_three] at h1

lemma cos_le_neg_half_of_le {t : ℝ} (h : -Real.pi ≤ t) (h' : t ≤ -2 * Real.pi / 3) :
    Real.cos t ≤ -(1 / 2) := by
  rw [← Real.cos_neg]
  exact cos_le_neg_half_of_ge (by linarith) (by linarith)

lemma phLift_eq (t : ℝ) : phLift t = -(t / 2) - Real.pi := by
  unfold phLift u0 v0; field_simp; ring

lemma cos_phLift (t : ℝ) : Real.cos (phLift t) = -Real.cos (t / 2) := by
  rw [phLift_eq, show -(t / 2) - Real.pi = -(Real.pi + t / 2) by ring, Real.cos_neg,
    show Real.pi + t / 2 = t / 2 + Real.pi by ring, Real.cos_add_pi]

lemma sin_phLift (t : ℝ) : Real.sin (phLift t) = Real.sin (t / 2) := by
  rw [phLift_eq, show -(t / 2) - Real.pi = -(Real.pi + t / 2) by ring, Real.sin_neg,
    show Real.pi + t / 2 = t / 2 + Real.pi by ring, Real.sin_add_pi]
  ring

lemma cos_eq_zero_mem_Icc {y : ℝ} (h1 : -(Real.pi / 2) ≤ y) (h2 : y ≤ Real.pi / 2)
    (h : Real.cos y = 0) : y = Real.pi / 2 ∨ y = -(Real.pi / 2) := by
  by_contra hc
  have hc1 : y ≠ Real.pi / 2 := fun h => hc (Or.inl h)
  have hc2 : y ≠ -(Real.pi / 2) := fun h => hc (Or.inr h)
  have : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨lt_of_le_of_ne h1 (Ne.symm hc2), lt_of_le_of_ne h2 hc1⟩
  linarith

/-! ## Facts about the design functions -/

lemma bump_nonneg_of_inRange {t : ℝ} (hin : inRange t) : 0 ≤ bump t := by
  rw [bump_eq_cos]
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · have := hin.1; unfold u0 at this; linarith [Real.pi_pos]
  · have := hin.2; unfold v0 at this; linarith [Real.pi_pos]

lemma bump_eq_zero_iff {t : ℝ} (hin : inRange t) : bump t = 0 ↔ t = u0 ∨ t = v0 := by
  rw [bump_eq_cos]
  constructor
  · intro h
    have h1 : -(Real.pi / 2) ≤ 3 * t / 4 := by
      have := hin.1; unfold u0 at this; linarith [Real.pi_pos]
    have h2 : 3 * t / 4 ≤ Real.pi / 2 := by
      have := hin.2; unfold v0 at this; linarith [Real.pi_pos]
    rcases cos_eq_zero_mem_Icc h1 h2 h with h' | h'
    · right; unfold v0; linarith
    · left; unfold u0; linarith
  · rintro (rfl | rfl)
    · rw [show 3 * u0 / 4 = -(Real.pi / 2) by unfold u0; ring, Real.cos_neg,
        Real.cos_pi_div_two]
    · rw [show 3 * v0 / 4 = Real.pi / 2 by unfold v0; ring, Real.cos_pi_div_two]

lemma bump_pos_iff {t : ℝ} (hin : inRange t) : 0 < bump t ↔ u0 < t ∧ t < v0 := by
  constructor
  · intro h
    have hnz : bump t ≠ 0 := ne_of_gt h
    have hnez : ¬(t = u0 ∨ t = v0) := fun hc => hnz ((bump_eq_zero_iff hin).2 hc)
    obtain ⟨h1, h2⟩ := not_or.mp hnez
    exact ⟨lt_of_le_of_ne hin.1 (Ne.symm h1), lt_of_le_of_ne hin.2 h2⟩
  · intro ⟨h1, h2⟩
    rw [bump_eq_cos]
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · show -(Real.pi / 2) < 3 * t / 4
      unfold u0 at h1; linarith [Real.pi_pos]
    · show 3 * t / 4 < Real.pi / 2
      unfold v0 at h2; linarith [Real.pi_pos]

lemma sig1_pos (t : ℝ) : 0 < sig1 t := by
  unfold sig1 bump
  have := Real.sin_le_one (Real.pi * (t - u0) / (v0 - u0))
  linarith

lemma sig1c_pos (t : ℝ) : 0 < sig1c t := by
  by_cases h : inRange t
  · simp only [sig1c, if_pos h]; exact sig1_pos t
  · simp only [sig1c, if_neg h]; norm_num

lemma sig1c_le_one (t : ℝ) : sig1c t ≤ 1 := by
  by_cases h : inRange t
  · simp only [sig1c, if_pos h, sig1]
    have := bump_nonneg_of_inRange h
    linarith
  · simp only [sig1c, if_neg h]; exact le_refl 1

lemma sig2c_le_one (t : ℝ) : sig2c t ≤ 1 := by
  by_cases h : inRange t
  · simp only [sig2c, if_pos h, sig2]
    have := bump_nonneg_of_inRange h
    linarith
  · simp only [sig2c, if_neg h]; exact le_refl 1

lemma tauc_le_one (t : ℝ) : tauc t ≤ 1 := by
  by_cases h : inRange t
  · simp only [tauc, if_pos h, tauP, sig2]
    have := bump_nonneg_of_inRange h
    linarith
  · simp only [tauc, if_neg h]; exact le_refl 1

lemma cos_phLift_le_of_inRange {t : ℝ} (hin : inRange t) :
    Real.cos (phLift t) ≤ -(1 / 2) := by
  rw [cos_phLift]
  have h1 : |t / 2| ≤ Real.pi / 3 := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have := hin.1; unfold u0 at this; linarith [Real.pi_pos]
    · have := hin.2; unfold v0 at this; linarith [Real.pi_pos]
  have := half_le_cos_of_abs_le h1
  linarith

/-! ## The waypoints -/

lemma W2c_eq_of_not_inRange {t : ℝ} (h : ¬inRange t) : W2c t = W5c t := by
  simp only [W2c, if_neg h]

lemma W2c_u0 : W2c u0 = W5c u0 := by
  have hin : inRange u0 := ⟨le_refl u0, by unfold u0 v0; linarith [Real.pi_pos]⟩
  simp only [W2c, if_pos hin, W5c, phLift_u0]

lemma W2c_v0 : W2c v0 = W5c v0 := by
  have hin : inRange v0 := ⟨by unfold u0 v0; linarith [Real.pi_pos], le_refl v0⟩
  simp only [W2c, if_pos hin, W5c, phLift_v0, Real.cos_sub_two_pi, Real.sin_sub_two_pi]

lemma seg_right {P Q : ℝ × ℝ} {a b : ℝ} (h : b - a ≠ 0) : seg P Q a b b = Q := by
  simp only [seg]
  rw [div_self h]
  simp

/-! ## Reducing `profW` to its four branches -/

lemma profW_br1 {t s : ℝ} (h : s ≤ sig1c t) : profW t s = seg W1 (W2c t) 0 (sig1c t) s := by
  unfold profW; rw [if_pos h]

lemma profW_br2 {t s : ℝ} (h1 : ¬s ≤ sig1c t) (h2 : s ≤ sig2c t) :
    profW t s = seg (W2c t) (W3c t) (sig1c t) (sig2c t) s := by
  unfold profW; rw [if_neg h1, if_pos h2]

lemma profW_br3 {t s : ℝ} (h1 : ¬s ≤ sig1c t) (h2 : ¬s ≤ sig2c t) (h3 : s ≤ tauc t) :
    profW t s = seg (W3c t) W4 (sig2c t) (tauc t) s := by
  unfold profW; rw [if_neg h1, if_neg h2, if_pos h3]

lemma profW_br4 {t s : ℝ} (h1 : ¬s ≤ sig1c t) (h2 : ¬s ≤ sig2c t) (h3 : ¬s ≤ tauc t) :
    profW t s = seg W4 (W5c t) (tauc t) 1 s := by
  unfold profW; rw [if_neg h1, if_neg h2, if_neg h3]

/-! ## The squared norm of `seg` on each branch -/

lemma norm_br1 {t s : ℝ} (hin : inRange t) :
    (seg W1 (W2c t) 0 (sig1c t) s).1 ^ 2 + (seg W1 (W2c t) 0 (sig1c t) s).2 ^ 2
      = 1 + (s / sig1c t - 1) * ((5 + 4 * Real.cos (phLift t)) * (s / sig1c t) - 3) := by
  simp only [seg, W1, W2c, sig1c, if_pos hin, sub_zero]
  have hcs : Real.sin (phLift t) ^ 2 + Real.cos (phLift t) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  linear_combination (s / sig1 t) ^ 2 * hcs

lemma norm_br2 {t s : ℝ} (hin : inRange t) :
    (seg (W2c t) (W3c t) (sig1c t) (sig2c t) s).1 ^ 2
      + (seg (W2c t) (W3c t) (sig1c t) (sig2c t) s).2 ^ 2
      = 1 - 2 * ((s - sig1c t) / (sig2c t - sig1c t)) * (1 - (s - sig1c t) / (sig2c t - sig1c t))
              * (1 - Real.cos (dlt t)) := by
  simp only [seg, W2c, W3c, sig1c, sig2c, if_pos hin]
  have h1 : Real.sin (phLift t) ^ 2 + Real.cos (phLift t) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have h2 : Real.sin (phLift t + dlt t) ^ 2 + Real.cos (phLift t + dlt t) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have h3 : Real.cos (phLift t) * Real.cos (phLift t + dlt t)
      + Real.sin (phLift t) * Real.sin (phLift t + dlt t) = Real.cos (dlt t) := by
    have hh := Real.cos_sub (phLift t + dlt t) (phLift t)
    rw [show (phLift t + dlt t) - phLift t = dlt t by ring] at hh
    nlinarith [hh]
  linear_combination (1 - (s - sig1 t) / (sig2 t - sig1 t)) ^ 2 * h1
    + ((s - sig1 t) / (sig2 t - sig1 t)) ^ 2 * h2
    + (2 * ((s - sig1 t) / (sig2 t - sig1 t)) * (1 - (s - sig1 t) / (sig2 t - sig1 t))) * h3

lemma norm_br3 {t s : ℝ} (hin : inRange t) :
    (seg (W3c t) W4 (sig2c t) (tauc t) s).1 ^ 2 + (seg (W3c t) W4 (sig2c t) (tauc t) s).2 ^ 2
      = (1 - (s - sig2c t) / (tauc t - sig2c t)) ^ 2 := by
  simp only [seg, W3c, W4, sig2c, tauc, if_pos hin]
  have h2 : Real.sin (phLift t + dlt t) ^ 2 + Real.cos (phLift t + dlt t) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  nlinarith [h2]

lemma norm_br4 {t s : ℝ} (hin : inRange t) :
    (seg W4 (W5c t) (tauc t) 1 s).1 ^ 2 + (seg W4 (W5c t) (tauc t) 1 s).2 ^ 2
      = ((s - tauc t) / (1 - tauc t)) ^ 2 := by
  simp only [seg, W4, W5c, tauc, if_pos hin]
  have h2 : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  nlinarith [h2]

lemma norm_out {t s : ℝ} :
    (seg W1 (W5c t) 0 1 s).1 ^ 2 + (seg W1 (W5c t) 0 1 s).2 ^ 2
      = 1 + (s - 1) * ((5 + 4 * Real.cos t) * s - 3) := by
  simp only [seg, W1, W5c, sub_zero]
  have hcs : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  linear_combination s ^ 2 * hcs

/-! ## The endpoint level `s = 1` -/

lemma profW_one (t : ℝ) : profW t 1 = W5c t := by
  by_cases hin : inRange t
  · by_cases h1 : (1 : ℝ) ≤ sig1c t
    · have hs1 : sig1c t = 1 := le_antisymm (sig1c_le_one t) h1
      have hsig1 : sig1 t = 1 := by
        rw [← hs1]; simp only [sig1c, if_pos hin]
      have hbump : bump t = 0 := by unfold sig1 at hsig1; linarith
      have hW : W2c t = W5c t := by
        rcases (bump_eq_zero_iff hin).1 hbump with h | h
        · rw [h]; exact W2c_u0
        · rw [h]; exact W2c_v0
      rw [profW_br1 h1, hs1, seg_right (by norm_num : (1 : ℝ) - 0 ≠ 0), hW]
    · have hsig1 : sig1 t < 1 := by
        have hs1c : sig1c t = sig1 t := by simp only [sig1c, if_pos hin]
        rw [← hs1c]; exact lt_of_not_ge h1
      have hbump : 0 < bump t := by unfold sig1 at hsig1; linarith
      have hopen := (bump_pos_iff hin).1 hbump
      have hs2c : sig2c t = sig2 t := by simp only [sig2c, if_pos hin]
      have htc : tauc t = tauP t := by simp only [tauc, if_pos hin]
      have h2 : ¬(1 : ℝ) ≤ sig2c t := by
        rw [hs2c]; intro hh
        linarith [sig2_lt_tauP hopen.1 hopen.2, tauP_lt_one hopen.1 hopen.2]
      have h3 : ¬(1 : ℝ) ≤ tauc t := by
        rw [htc]; intro hh
        linarith [tauP_lt_one hopen.1 hopen.2]
      rw [profW_br4 h1 h2 h3, htc,
        seg_right (by linarith [tauP_lt_one hopen.1 hopen.2] : (1 : ℝ) - tauP t ≠ 0)]
  · have hs1c : sig1c t = 1 := by simp only [sig1c, if_neg hin]
    have hW : W2c t = W5c t := W2c_eq_of_not_inRange hin
    have h1 : (1 : ℝ) ≤ sig1c t := by rw [hs1c]
    rw [profW_br1 h1, hs1c, hW, seg_right (by norm_num : (1 : ℝ) - 0 ≠ 0)]

/-! ## The level statement -/

theorem profW_levels {t s : ℝ} (ht : -Real.pi < t) (ht' : t ≤ Real.pi) :
    profW t 1 = W5c t ∧ (0 < s → s < 1 →
      (((profW t s).1 ^ 2 + (profW t s).2 ^ 2 = 1) ↔
        (inRange t ∧ (s = sig1 t ∨ s = sig2 t)))) := by
  refine ⟨profW_one t, fun hs0 hs1 => ⟨?_, ?_⟩⟩
  · intro hnorm
    by_cases hin : inRange t
    · have hs1c : sig1c t = sig1 t := by simp only [sig1c, if_pos hin]
      have hs2c : sig2c t = sig2 t := by simp only [sig2c, if_pos hin]
      have htc : tauc t = tauP t := by simp only [tauc, if_pos hin]
      by_cases hb1 : s ≤ sig1c t
      · rw [profW_br1 hb1, norm_br1 hin] at hnorm
        have hfac : (s / sig1c t - 1) * ((5 + 4 * Real.cos (phLift t)) * (s / sig1c t) - 3)
            = 0 := by linarith
        have hcos : Real.cos (phLift t) ≤ -(1 / 2) := cos_phLift_le_of_inRange hin
        have hcpos : 0 < 5 + 4 * Real.cos (phLift t) := by
          have := Real.neg_one_le_cos (phLift t); linarith
        have hcle : 5 + 4 * Real.cos (phLift t) ≤ 3 := by linarith
        have hratio_ge : 1 ≤ 3 / (5 + 4 * Real.cos (phLift t)) :=
          (one_le_div₀ hcpos).2 hcle
        have hsigpos : 0 < sig1c t := sig1c_pos t
        have hlam_le : s / sig1c t ≤ 1 := (div_le_one hsigpos).2 hb1
        have hratio : s / sig1c t = 1 := by
          rcases mul_eq_zero.mp hfac with h | h
          · linarith
          · have h2 : s / sig1c t = 3 / (5 + 4 * Real.cos (phLift t)) := by
              rw [eq_div_iff (ne_of_gt hcpos)]; linarith
            exact le_antisymm hlam_le (le_trans hratio_ge (le_of_eq h2.symm))
        have hse : s = sig1 t := by
          have := (div_eq_one_iff_eq (ne_of_gt hsigpos)).mp hratio
          rw [this, hs1c]
        exact ⟨hin, Or.inl hse⟩
      · by_cases hb2 : s ≤ sig2c t
        · rw [profW_br2 hb1 hb2, norm_br2 hin] at hnorm
          have hlt : sig1c t < s := lt_of_not_ge hb1
          have hbump : 0 < bump t := by
            have : sig1 t < 1 := by rw [← hs1c]; linarith
            unfold sig1 at this; linarith
          have hopen := (bump_pos_iff hin).1 hbump
          have hss : sig1 t < sig2 t := sig1_lt_sig2 hopen.1 hopen.2
          have hdiff : 0 < sig2c t - sig1c t := by rw [hs1c, hs2c]; linarith
          have hlam_pos : 0 < (s - sig1c t) / (sig2c t - sig1c t) :=
            div_pos (by rw [hs1c]; linarith) hdiff
          have hcosd : Real.cos (dlt t) ≠ 1 := by
            have hd0 : 0 < dlt t := by unfold dlt; linarith
            have hd2 : dlt t < 2 * Real.pi := by
              have hb1' : bump t ≤ 1 := Real.sin_le_one _
              have hπ : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
              unfold dlt; linarith
            have := Real.cos_eq_one_iff_of_lt_of_lt (by linarith) hd2
            intro hh; exact hd0.ne' (this.mp hh)
          have hfac : 2 * ((s - sig1c t) / (sig2c t - sig1c t))
              * (1 - (s - sig1c t) / (sig2c t - sig1c t)) * (1 - Real.cos (dlt t)) = 0 := by
            linarith
          have hlam : (s - sig1c t) / (sig2c t - sig1c t) = 1 := by
            rcases mul_eq_zero.mp hfac with h | h
            · rcases mul_eq_zero.mp h with h' | h'
              · exact absurd h' (by intro hh; linarith [hlam_pos])
              · linarith
            · exact absurd h (by intro hh; exact hcosd (by linarith))
          have hse : s = sig2 t := by
            have := (div_eq_one_iff_eq (ne_of_gt hdiff)).mp hlam
            rw [hs1c, hs2c] at this; linarith
          exact ⟨hin, Or.inr hse⟩
        · by_cases hb3 : s ≤ tauc t
          · rw [profW_br3 hb1 hb2 hb3, norm_br3 hin] at hnorm
            exfalso
            have hlt : sig1c t < s := lt_of_not_ge hb1
            have hbump : 0 < bump t := by
              have : sig1 t < 1 := by rw [← hs1c]; linarith
              unfold sig1 at this; linarith
            have hopen := (bump_pos_iff hin).1 hbump
            have hdiff : 0 < tauc t - sig2c t := by
              rw [htc, hs2c]; exact sub_pos.mpr (sig2_lt_tauP hopen.1 hopen.2)
            have hpos : 0 < (s - sig2c t) / (tauc t - sig2c t) :=
              div_pos (by linarith [lt_of_not_ge hb2]) hdiff
            have hle : (s - sig2c t) / (tauc t - sig2c t) ≤ 1 :=
              (div_le_one hdiff).2 (by linarith)
            have hcases : (1 - (s - sig2c t) / (tauc t - sig2c t)) = 1
                ∨ (1 - (s - sig2c t) / (tauc t - sig2c t)) = -1 := by
              rwa [sq_eq_one_iff] at hnorm
            rcases hcases with h | h <;> linarith
          · rw [profW_br4 hb1 hb2 hb3, norm_br4 hin] at hnorm
            exfalso
            have hbump : 0 < bump t := by
              have : sig1 t < 1 := by rw [← hs1c]; linarith
              unfold sig1 at this; linarith
            have hopen := (bump_pos_iff hin).1 hbump
            have htau : tauc t < 1 := by rw [htc]; exact tauP_lt_one hopen.1 hopen.2
            have hden : 0 < 1 - tauc t := by linarith
            have hpos : 0 < (s - tauc t) / (1 - tauc t) :=
              div_pos (by linarith [lt_of_not_ge hb3]) hden
            have hlt : (s - tauc t) / (1 - tauc t) < 1 := (div_lt_one hden).2 (by linarith)
            have hcases : (s - tauc t) / (1 - tauc t) = 1
                ∨ (s - tauc t) / (1 - tauc t) = -1 := by
              rwa [sq_eq_one_iff] at hnorm
            rcases hcases with h | h <;> linarith
    · have hs1c : sig1c t = 1 := by simp only [sig1c, if_neg hin]
      have hW : W2c t = W5c t := W2c_eq_of_not_inRange hin
      have hb1 : s ≤ sig1c t := by rw [hs1c]; exact le_of_lt hs1
      rw [profW_br1 hb1, hs1c, hW, norm_out] at hnorm
      exfalso
      have hfac : (s - 1) * ((5 + 4 * Real.cos t) * s - 3) = 0 := by linarith
      have hcos : Real.cos t ≤ -(1 / 2) := by
        rcases lt_or_ge t u0 with h | h
        · have h' : t ≤ -2 * Real.pi / 3 := by unfold u0 at h; linarith
          exact cos_le_neg_half_of_le (le_of_lt ht) h'
        · have hv : v0 < t := by
            by_contra hc
            exact hin ⟨h, le_of_not_gt hc⟩
          have h' : 2 * Real.pi / 3 ≤ t := by unfold v0 at hv; linarith
          exact cos_le_neg_half_of_ge h' ht'
      have hcpos : 0 < 5 + 4 * Real.cos t := by
        have := Real.neg_one_le_cos t; linarith
      have hcle : 5 + 4 * Real.cos t ≤ 3 := by linarith
      have hsge : 1 ≤ 3 / (5 + 4 * Real.cos t) := (one_le_div₀ hcpos).2 hcle
      have h3 : (5 + 4 * Real.cos t) * s - 3 = 0 := by
        rcases mul_eq_zero.mp hfac with h | h
        · exact absurd h (by intro hh; linarith [hs1])
        · exact h
      have hse : s = 3 / (5 + 4 * Real.cos t) := by
        rw [eq_div_iff (ne_of_gt hcpos)]; linarith
      linarith [hse, hsge, hs1]
  · rintro ⟨hin, hsig | hsig⟩
    · have hs1c : sig1c t = sig1 t := by simp only [sig1c, if_pos hin]
      have hb1 : s ≤ sig1c t := by rw [hs1c, hsig]
      rw [profW_br1 hb1, norm_br1 hin, hsig, hs1c, div_self (ne_of_gt (sig1_pos t))]
      ring
    · have hs1c : sig1c t = sig1 t := by simp only [sig1c, if_pos hin]
      have hs2c : sig2c t = sig2 t := by simp only [sig2c, if_pos hin]
      have hbump : 0 < bump t := by
        have : sig2 t < 1 := by rw [← hsig]; exact hs1
        unfold sig2 at this; linarith
      have hopen := (bump_pos_iff hin).1 hbump
      have hss : sig1 t < sig2 t := sig1_lt_sig2 hopen.1 hopen.2
      have hb1 : ¬s ≤ sig1c t := by rw [hs1c, hsig]; exact not_le.mpr hss
      have hb2 : s ≤ sig2c t := by rw [hs2c, hsig]
      have hne : sig2 t - sig1 t ≠ 0 := ne_of_gt (sub_pos.mpr hss)
      rw [profW_br2 hb1 hb2, norm_br2 hin, hsig, hs1c, hs2c, div_self hne]
      ring

end

end Work.Drive.EpsForm
