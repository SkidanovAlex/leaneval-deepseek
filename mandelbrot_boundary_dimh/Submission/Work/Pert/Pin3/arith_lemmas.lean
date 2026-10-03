import Mathlib
import Submission.Work.Pert.Ksub2.exists_log_le_half

set_option linter.unusedVariables false

namespace Work.Pert.Pin3

/-- The linear term eventually dominates `a (1 + log M)`: for every `a > 0` and `k > 0`
there is `R > 0` such that `a * (1 + log M) ≤ M / k` for all `M ≥ R`. -/
theorem exists_mul_one_add_log_le_div (a k : ℝ) (ha : 0 < a) (hk : 0 < k) :
    ∃ R : ℝ, 0 < R ∧ ∀ M : ℝ, R ≤ M → a * (1 + Real.log M) ≤ M / k := by
  obtain ⟨R₀, hR₀⟩ := Work.Pert.Ksub2.exists_log_le_half (a * k)
  refine ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun M hM => ?_⟩
  have hR0 : R₀ ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : (1 : ℝ) ≤ M := le_trans (le_max_right _ _) hM
  have h := hR₀ M hR0
  have hlog : 1 + Real.log M ≤ M / (2 * (a * k)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [h]
  have h1 : a * (1 + Real.log M) ≤ a * (M / (2 * (a * k))) :=
    mul_le_mul_of_nonneg_left hlog ha.le
  have heq : a * (M / (2 * (a * k))) = M / (2 * k) := by field_simp
  rw [heq] at h1
  have h2 : M / (2 * k) ≤ M / k :=
    div_le_div_of_nonneg_left (le_of_lt (lt_of_lt_of_le one_pos hM1)) hk
      (by linarith : k ≤ 2 * k)
  linarith

/-- The linear term eventually dominates `a log M`: for every `a > 0` and `k > 0` there is
`R > 0` such that `a * log M ≤ M / k` for all `M ≥ R`. -/
theorem exists_mul_log_le_div (a k : ℝ) (ha : 0 < a) (hk : 0 < k) :
    ∃ R : ℝ, 0 < R ∧ ∀ M : ℝ, R ≤ M → a * Real.log M ≤ M / k := by
  obtain ⟨R, hRpos, hR⟩ := exists_mul_one_add_log_le_div a k ha hk
  refine ⟨R, hRpos, fun M hM => ?_⟩
  have h := hR M hM
  have h' : a * Real.log M ≤ a * (1 + Real.log M) :=
    mul_le_mul_of_nonneg_left (by linarith) ha.le
  linarith

/-- All the elementary estimates needed at the end of the perturbation construction hold for
`M` larger than a single explicit threshold. -/
theorem arith_lemmas {Ξ y₁ Cdev Cseed Camp Csh Chigh R C₂ R₁ : ℝ}
    (hΞ : 0 < Ξ) (hCdev : 0 < Cdev) (hCseed : 1 ≤ Cseed) (hCamp : 1 ≤ Camp)
    (hCsh : 0 < Csh) (hChigh : 0 < Chigh) (hR : 0 < R) :
    ∃ Ms : ℝ, 0 < Ms ∧ ∀ M : ℝ, Ms ≤ M →
      (8 * Ξ + 8 ≤ M) ∧
      (max (Chigh * Real.log M) y₁ ≤ M / 160) ∧
      (0 ≤ max (Chigh * Real.log M) y₁) ∧
      (Csh * (1 + Real.log M) ≤ M / 320) ∧
      (0 ≤ Csh * (1 + Real.log M)) ∧
      (2 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁ < M / 40) ∧
      (2 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁
        + Csh * (1 + Real.log M) < M / 80) ∧
      (Csh * (1 + Real.log M) + (1 + max (Chigh * Real.log M) y₁)
        + Csh * (1 + Real.log M) ≤ M / 8) ∧
      (Camp * (1 + max (Chigh * Real.log M) y₁) ≤ M) ∧
      (Cdev ≤ M / 80) ∧ (64 * C₂ ≤ M) ∧ (R₁ ≤ M / 8) ∧
      ((3 / 2) * (Csh * (1 + Real.log M))
        + (Cdev * 80 / M + 4 * (1 / M))
          * (3 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁)
        < M / 32) ∧
      (Cseed * ((Cdev * 80 / M + 4 * (1 / M))
          * (3 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁))
        / (M * M) ≤ R / (32 * Camp * M * M)) ∧
      (y₁ ≤ max (Chigh * Real.log M) y₁) := by
  have hCamppos : 0 < Camp := lt_of_lt_of_le one_pos hCamp
  set K : ℝ := max 1000 (max (2 * Camp) (160 * Camp * Cseed * (Cdev * 80 + 4) / R))
    with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1000) (le_max_left _ _)
  have hK1000 : (1000 : ℝ) ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hK2Camp : 2 * Camp ≤ K := by
    rw [hKdef]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hKX : 160 * Camp * Cseed * (Cdev * 80 + 4) / R ≤ K := by
    rw [hKdef]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨RA, _hRApos, hRA⟩ := exists_mul_one_add_log_le_div Csh K hCsh hKpos
  obtain ⟨RL, _hRLpos, hRL⟩ := exists_mul_log_le_div Chigh K hChigh hKpos
  have hAev : ∀ᶠ M : ℝ in Filter.atTop, Csh * (1 + Real.log M) ≤ M / K :=
    Filter.eventually_atTop.mpr ⟨RA, hRA⟩
  have hLlog : ∀ᶠ M : ℝ in Filter.atTop, Chigh * Real.log M ≤ M / K :=
    Filter.eventually_atTop.mpr ⟨RL, hRL⟩
  have hy₁ev : ∀ᶠ M : ℝ in Filter.atTop, y₁ ≤ M / K := by
    filter_upwards [Filter.eventually_ge_atTop (y₁ * K)] with M hM
    rw [le_div_iff₀ hKpos]
    linarith
  have hLev : ∀ᶠ M : ℝ in Filter.atTop, max (Chigh * Real.log M) y₁ ≤ M / K := by
    filter_upwards [hLlog, hy₁ev] with M h1 h2
    exact max_le h1 h2
  have h1Kev : ∀ᶠ M : ℝ in Filter.atTop, (1 : ℝ) ≤ M / K := by
    filter_upwards [Filter.eventually_ge_atTop K] with M hM
    rw [le_div_iff₀ hKpos]
    linarith
  have h1ev : ∀ᶠ M : ℝ in Filter.atTop, (1 : ℝ) ≤ M := Filter.eventually_ge_atTop 1
  have hCe : ∀ᶠ M : ℝ in Filter.atTop, (8 * Ξ + 8 ≤ M) ∧ (80 * Cdev ≤ M) ∧
      (64 * C₂ ≤ M) ∧ (8 * R₁ ≤ M) ∧ (20 * (Cdev * 80 + 4) ≤ M) := by
    filter_upwards [Filter.eventually_ge_atTop (8 * Ξ + 8),
      Filter.eventually_ge_atTop (80 * Cdev), Filter.eventually_ge_atTop (64 * C₂),
      Filter.eventually_ge_atTop (8 * R₁), Filter.eventually_ge_atTop (20 * (Cdev * 80 + 4))]
      with M h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have H : ∃ a : ℝ, ∀ M : ℝ, a ≤ M →
      (8 * Ξ + 8 ≤ M) ∧
      (max (Chigh * Real.log M) y₁ ≤ M / 160) ∧
      (0 ≤ max (Chigh * Real.log M) y₁) ∧
      (Csh * (1 + Real.log M) ≤ M / 320) ∧
      (0 ≤ Csh * (1 + Real.log M)) ∧
      (2 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁ < M / 40) ∧
      (2 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁
        + Csh * (1 + Real.log M) < M / 80) ∧
      (Csh * (1 + Real.log M) + (1 + max (Chigh * Real.log M) y₁)
        + Csh * (1 + Real.log M) ≤ M / 8) ∧
      (Camp * (1 + max (Chigh * Real.log M) y₁) ≤ M) ∧
      (Cdev ≤ M / 80) ∧ (64 * C₂ ≤ M) ∧ (R₁ ≤ M / 8) ∧
      ((3 / 2) * (Csh * (1 + Real.log M))
        + (Cdev * 80 / M + 4 * (1 / M))
          * (3 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁)
        < M / 32) ∧
      (Cseed * ((Cdev * 80 / M + 4 * (1 / M))
          * (3 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁))
        / (M * M) ≤ R / (32 * Camp * M * M)) ∧
      (y₁ ≤ max (Chigh * Real.log M) y₁) := by
    rw [← Filter.eventually_atTop]
    filter_upwards [hAev, hLev, h1Kev, h1ev, hCe] with M hA hL h1K h1 hCe'
    obtain ⟨h8Ξ, hCdev80, h64C₂, h8R₁, h13c⟩ := hCe'
    have hMpos : 0 < M := lt_of_lt_of_le one_pos h1
    have hMnn : 0 ≤ M := hMpos.le
    have hlog : 0 ≤ Real.log M := Real.log_nonneg h1
    have hMK160 : M / K ≤ M / 160 :=
      div_le_div_of_nonneg_left hMnn (by norm_num) (by linarith : (160 : ℝ) ≤ K)
    have hMK320 : M / K ≤ M / 320 :=
      div_le_div_of_nonneg_left hMnn (by norm_num) (by linarith : (320 : ℝ) ≤ K)
    have hMK1000 : M / K ≤ M / 1000 :=
      div_le_div_of_nonneg_left hMnn (by norm_num) (by linarith : (1000 : ℝ) ≤ K)
    have hP : Cdev * 80 / M + 4 * (1 / M) = (Cdev * 80 + 4) / M := by ring
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact h8Ξ
    · exact le_trans hL hMK160
    · exact le_trans (mul_nonneg hChigh.le hlog) (le_max_left _ _)
    · exact le_trans hA hMK320
    · exact mul_nonneg hCsh.le (by linarith)
    · have hb : 2 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁
          ≤ 4 * (M / 1000) := by linarith [hA, h1K, hL, hMK1000]
      have hb2 : 4 * (M / 1000) < M / 40 := by linarith [hMpos]
      linarith
    · have hb : 2 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁
            + Csh * (1 + Real.log M) ≤ 5 * (M / 1000) := by
        linarith [hA, h1K, hL, hMK1000]
      have hb2 : 5 * (M / 1000) < M / 80 := by linarith [hMpos]
      linarith
    · have hb : Csh * (1 + Real.log M) + (1 + max (Chigh * Real.log M) y₁)
            + Csh * (1 + Real.log M) ≤ 4 * (M / 1000) := by
        linarith [hA, h1K, hL, hMK1000]
      have hb2 : 4 * (M / 1000) ≤ M / 8 := by linarith [hMnn]
      linarith
    · have h1L : 1 + max (Chigh * Real.log M) y₁ ≤ 2 * (M / K) := by linarith [h1K, hL]
      have h2CK : 2 * Camp / K ≤ 1 := by rw [div_le_one hKpos]; linarith [hK2Camp]
      have hb : Camp * (1 + max (Chigh * Real.log M) y₁) ≤ M * (2 * Camp / K) := by
        calc Camp * (1 + max (Chigh * Real.log M) y₁) ≤ Camp * (2 * (M / K)) :=
              mul_le_mul_of_nonneg_left h1L hCamppos.le
          _ = M * (2 * Camp / K) := by ring
      have hb2 : M * (2 * Camp / K) ≤ M * 1 := mul_le_mul_of_nonneg_left h2CK hMnn
      linarith
    · rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 80)]
      linarith [hCdev80]
    · exact h64C₂
    · rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      linarith [h8R₁]
    · rw [hP]
      have hQ : 3 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁
          ≤ 5 * (M / K) := by linarith [hA, h1K, hL]
      have hPnn : 0 ≤ (Cdev * 80 + 4) / M :=
        div_nonneg (by linarith [hCdev]) hMnn
      have hPQ : (Cdev * 80 + 4) / M
            * (3 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁)
          ≤ (Cdev * 80 + 4) / M * (5 * (M / K)) := mul_le_mul_of_nonneg_left hQ hPnn
      have hPQ' : (Cdev * 80 + 4) / M * (5 * (M / K)) = 5 * (Cdev * 80 + 4) / K := by
        field_simp
      have h13a : (3 / 2) * (Csh * (1 + Real.log M)) ≤ (3 / 2) * (M / K) := by linarith [hA]
      have h5K : 5 / K ≤ 1 / 200 := by rw [div_le_iff₀ hKpos]; linarith [hK1000]
      have h5a : 5 * (Cdev * 80 + 4) / K ≤ (Cdev * 80 + 4) / 200 := by
        rw [show 5 * (Cdev * 80 + 4) / K = (5 / K) * (Cdev * 80 + 4) by ring,
          show (Cdev * 80 + 4) / 200 = (1 / 200) * (Cdev * 80 + 4) by ring]
        exact mul_le_mul_of_nonneg_right h5K (by linarith [hCdev])
      have hc' : Cdev * 80 + 4 ≤ M / 20 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 20)]
        linarith [h13c]
      have hce : (Cdev * 80 + 4) / 200 ≤ M / 4000 := by
        calc (Cdev * 80 + 4) / 200 = (Cdev * 80 + 4) * (1 / 200) := by ring
          _ ≤ (M / 20) * (1 / 200) := mul_le_mul_of_nonneg_right hc' (by norm_num)
          _ = M / 4000 := by ring
      have hfinal : (3 / 2) * (M / K) + 5 * (Cdev * 80 + 4) / K < M / 32 := by
        have h1' : (3 / 2) * (M / K) ≤ (3 / 2) * (M / 1000) := by linarith [hMK1000]
        have h2' : 5 * (Cdev * 80 + 4) / K ≤ M / 4000 := le_trans h5a hce
        nlinarith [h1', h2', hMpos]
      calc (3 / 2) * (Csh * (1 + Real.log M))
              + (Cdev * 80 + 4) / M
                * (3 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁)
            ≤ (3 / 2) * (M / K) + (Cdev * 80 + 4) / M * (5 * (M / K)) := by
              linarith [h13a, hPQ]
        _ = (3 / 2) * (M / K) + 5 * (Cdev * 80 + 4) / K := by rw [hPQ']
        _ < M / 32 := hfinal
    · rw [hP]
      have hQ : 3 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁
          ≤ 5 * (M / K) := by linarith [hA, h1K, hL]
      have hPnn : 0 ≤ (Cdev * 80 + 4) / M :=
        div_nonneg (by linarith [hCdev]) hMnn
      have hPQ : (Cdev * 80 + 4) / M
            * (3 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁)
          ≤ (Cdev * 80 + 4) / M * (5 * (M / K)) := mul_le_mul_of_nonneg_left hQ hPnn
      have hPQ' : (Cdev * 80 + 4) / M * (5 * (M / K)) = 5 * (Cdev * 80 + 4) / K := by
        field_simp
      have hCseednn : 0 ≤ Cseed := le_trans zero_le_one hCseed
      have hCPQ : Cseed * ((Cdev * 80 + 4) / M
            * (3 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁))
          ≤ Cseed * (5 * (Cdev * 80 + 4) / K) := by
        calc Cseed * ((Cdev * 80 + 4) / M
                * (3 * (Csh * (1 + Real.log M)) + 1 + max (Chigh * Real.log M) y₁))
            ≤ Cseed * ((Cdev * 80 + 4) / M * (5 * (M / K))) :=
              mul_le_mul_of_nonneg_left hPQ hCseednn
          _ = Cseed * (5 * (Cdev * 80 + 4) / K) := by rw [hPQ']
      have hRK : 5 * Cseed * (Cdev * 80 + 4) * 32 * Camp ≤ R * K := by
        have hRK1 : R * (160 * Camp * Cseed * (Cdev * 80 + 4) / R) ≤ R * K :=
          mul_le_mul_of_nonneg_left hKX hR.le
        have heq : R * (160 * Camp * Cseed * (Cdev * 80 + 4) / R)
            = 160 * Camp * Cseed * (Cdev * 80 + 4) := by field_simp
        rw [heq] at hRK1
        have heq2 : 5 * Cseed * (Cdev * 80 + 4) * 32 * Camp
            = 160 * Camp * Cseed * (Cdev * 80 + 4) := by ring
        rw [heq2]
        exact hRK1
      have hRdiv : 5 * Cseed * (Cdev * 80 + 4) / K ≤ R / (32 * Camp) := by
        rw [div_le_iff₀ hKpos, div_mul_eq_mul_div,
          le_div_iff₀ (by positivity : (0 : ℝ) < 32 * Camp)]
        linarith [hRK]
      have hCPQ' : Cseed * (5 * (Cdev * 80 + 4) / K)
          = 5 * Cseed * (Cdev * 80 + 4) / K := by ring
      have hMM : 0 ≤ M * M := by positivity
      have hRHS : R / (32 * Camp * M * M) = R / (32 * Camp) / (M * M) := by ring
      rw [hRHS]
      exact div_le_div_of_nonneg_right (le_trans hCPQ (by rw [hCPQ']; exact hRdiv)) hMM
    · exact le_max_right _ _
  obtain ⟨a, ha⟩ := H
  exact ⟨max a 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun M hM => ha M (le_trans (le_max_left _ _) hM)⟩

end Work.Pert.Pin3
