import Mathlib
import Submission.Work.Holonomy3.model_deps
import Submission.Work.Holonomy3.sum_Lge_aux
import Submission.Work.Holonomy3.modelFun_monotone
import Submission.Work.Holonomy3.sum_mul_le_integral_of_monotone
import Submission.Work.Holonomy3.log_Lge_eq_theta_sub_of_le
import Submission.Work.Holonomy3.lcmBound_le_modelFun
import Submission.Work.Holonomy3.integratedLcm_eq_integral_modelFun
import Submission.Work.Holonomy3.exists_theta_sub_id_le

namespace Work.Holonomy3

set_option maxHeartbeats 4000000

open scoped BigOperators

theorem sum_Lge_le_integral {m : ℕ} (hm : 0 < m) {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξm : ξ ≤ m)
    (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ d : ℕ, 0 < d →
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ n : Fin d → ℕ, Monotone n →
      (∀ j : Fin d, (n j : ℝ) ≤ (m : ℝ) * D * ((j : ℝ) / d) + 3 * m * ε * D) →
      (∑ s : Fin d, Real.log ((Submission.CDT.LcmGe.Lge ⌊ξ * D⌋₊ (n s) D : ℕ) : ℝ))
        ≤ ((d : ℝ) * D / m) * (Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ + η) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := le_of_lt hmR
  -- ============================== constants ==============================
  set Smax : ℝ := Submission.CDT.Lcm2Bound.H m + ((m : ℝ) + 1) with hSmax
  have hSmaxnn : 0 ≤ Smax := by
    rw [hSmax]
    exact add_nonneg (Finset.sum_nonneg (fun a _ => by positivity)) (by positivity)
  have hSmaxpos : 0 < Smax := by
    rw [hSmax]
    have : (0 : ℝ) ≤ Submission.CDT.Lcm2Bound.H m :=
      Finset.sum_nonneg (fun a _ => by positivity)
    linarith
  set εp : ℝ := η / (128 * ((m : ℝ) + 1) ^ 2) with hεp
  have hεp_pos : 0 < εp := by rw [hεp]; positivity
  have hεp_small : εp ≤ η / (64 * (m : ℝ) ^ 2) := by
    rw [hεp, div_le_div_iff_of_pos_left hη (by positivity) (by positivity)]
    nlinarith [hm0, sq_nonneg ((m : ℝ) + 1)]
  have hεp_le : 32 * (m : ℝ) * εp ≤ η := by
    rw [hεp, ← mul_div_assoc,
      div_le_iff₀ (by positivity : (0 : ℝ) < 128 * ((m : ℝ) + 1) ^ 2)]
    nlinarith [hη, hm0, sq_nonneg ((m : ℝ) + 1)]
  obtain ⟨Cθ, hCθnn, hCθ⟩ := exists_theta_sub_id_le εp hεp_pos
  set ε₀ : ℝ := min (min (min (1 / (3 * (m : ℝ))) (η / (64 * (m : ℝ) ^ 2)))
      (η / (12 * (m : ℝ) * Smax))) (η / (16 * (m : ℝ))) with hε₀
  have hε₀_pos : 0 < ε₀ := by
    rw [hε₀]
    exact lt_min (lt_min (lt_min (by positivity) (by positivity)) (by positivity)) (by positivity)
  have hε₀_le1 : ε₀ ≤ 1 / (3 * (m : ℝ)) := by
    rw [hε₀]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε₀_le2 : ε₀ ≤ η / (64 * (m : ℝ) ^ 2) := by
    rw [hε₀]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε₀_le3 : ε₀ ≤ η / (12 * (m : ℝ) * Smax) := by
    rw [hε₀]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hε₀_le4 : ε₀ ≤ η / (16 * (m : ℝ)) := by
    rw [hε₀]; exact min_le_right _ _
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.mp (Submission.CDT.Lcm2Bound.log_Lge_le_uniform εp hεp_pos)
  refine ⟨ε₀, hε₀_pos,
    max (max N₀ 1) (max (Nat.ceil (16 * (m : ℝ) / η))
      (Nat.ceil (16 * (m : ℝ) * (2 * Cθ + 3) / η))), ?_⟩
  intro D hD d hd ε hεpos hεlt n hnmono hnbound
  -- ============================== D facts ==============================
  have hDN0 : N₀ ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hD
  have hD1 : 1 ≤ D := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hD
  have hDceil1 : Nat.ceil (16 * (m : ℝ) / η) ≤ D :=
    le_trans (le_trans (le_max_left _ _)
      (le_max_right (max N₀ 1) (max (Nat.ceil (16 * (m : ℝ) / η))
        (Nat.ceil (16 * (m : ℝ) * (2 * Cθ + 3) / η))))) hD
  have hDceil2 : Nat.ceil (16 * (m : ℝ) * (2 * Cθ + 3) / η) ≤ D :=
    le_trans (le_trans (le_max_right _ _)
      (le_max_right (max N₀ 1) (max (Nat.ceil (16 * (m : ℝ) / η))
        (Nat.ceil (16 * (m : ℝ) * (2 * Cθ + 3) / η))))) hD
  have hDR : (0 : ℝ) < (D : ℝ) := by
    have : (0 : ℝ) < 1 := one_pos
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hD1)
  have hDR0 : (0 : ℝ) ≤ (D : ℝ) := le_of_lt hDR
  have hDM : 16 * (m : ℝ) / η ≤ (D : ℝ) := by
    have h1 : 16 * (m : ℝ) / η ≤ (Nat.ceil (16 * (m : ℝ) / η) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (16 * (m : ℝ) / η) : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDceil1
    linarith
  have hDC : 16 * (m : ℝ) * (2 * Cθ + 3) / η ≤ (D : ℝ) := by
    have h1 : 16 * (m : ℝ) * (2 * Cθ + 3) / η
        ≤ (Nat.ceil (16 * (m : ℝ) * (2 * Cθ + 3) / η) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (16 * (m : ℝ) * (2 * Cθ + 3) / η) : ℕ) : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast hDceil2
    linarith
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  -- ============================== grid ==============================
  have hl_le : ((⌊ξ * (D : ℝ)⌋₊ : ℕ) : ℝ) ≤ ξ * (D : ℝ) :=
    Nat.floor_le (by positivity)
  have hl_lt : ξ * (D : ℝ) < ((⌊ξ * (D : ℝ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  -- ============================== per-position bound ==============================
  set l : ℕ := ⌊ξ * (D : ℝ)⌋₊ with hl
  have htper : ∀ s : Fin d,
      Real.log ((Submission.CDT.LcmGe.Lge l (n s) D : ℕ) : ℝ)
        ≤ (D : ℝ) * Submission.CDT.IntegratedLcm.modelFun ξ ((n s : ℝ) / D)
          + (ε + εp) * (n s) + (2 + 2 * εp * D + 2 * Cθ + 1) := by
    intro s
    by_cases hnl : l < n s
    · by_cases hDn : D ≤ n s
      · have h1 := hN₀ (n s) (le_trans hDN0 hDn) D l hDn (le_of_lt hnl)
        have h2 := lcmBound_le_modelFun D hD1 ξ hξ0 hDn
        have hs0 : (0 : ℝ) ≤ (n s : ℝ) := by positivity
        nlinarith [h1, h2, hs0]
      · have hnD : n s ≤ D := le_of_lt (lt_of_not_ge hDn)
        have hnsl : l < n s := hnl
        have heq := log_Lge_eq_theta_sub_of_le (le_of_lt hnsl) hnD
        have hs0 : (0 : ℝ) ≤ (n s : ℝ) := by positivity
        have hl0 : (0 : ℝ) ≤ (l : ℝ) := by positivity
        have hat := (abs_le.mp (hCθ (n s) hs0)).2
        have hbt := (abs_le.mp (hCθ (l) hl0)).1
        have hθ : Chebyshev.theta (n s : ℝ) - Chebyshev.theta (l : ℝ)
            ≤ ((n s : ℝ) - l) + εp * ((n s : ℝ) + l) + 2 * Cθ := by linarith
        have hnsD : (n s : ℝ) < (D : ℝ) := by exact_mod_cast lt_of_not_ge hDn
        have hfrac : (n s : ℝ) / D < 1 := by
          rw [div_lt_one hDR]; exact hnsD
        have hfeq : Submission.CDT.IntegratedLcm.modelFun ξ ((n s : ℝ) / D)
            = max ((n s : ℝ) / D - ξ) 0 :=
          Submission.CDT.IntegratedLcm.modelFun_of_le_one ξ _ (le_of_lt hfrac)
        have hlge : ξ * (D : ℝ) - 1 ≤ (l : ℝ) := by linarith [hl_lt]
        have hDn : (D : ℝ) * ((n s : ℝ) / D - ξ) = (n s : ℝ) - ξ * (D : ℝ) := by
          rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hDR)]
          ring
        have hDmul : (D : ℝ) * max ((n s : ℝ) / D - ξ) 0
            = max ((n s : ℝ) - ξ * (D : ℝ)) 0 := by
          have hmm : ∀ x : ℝ, (D : ℝ) * max x 0 = max ((D : ℝ) * x) 0 := by
            intro x
            rcases le_total x 0 with hx | hx
            · rw [max_eq_right hx, max_eq_right (by nlinarith [hx, hDR]), mul_zero]
            · rw [max_eq_left hx, max_eq_left (by nlinarith [hx, hDR])]
          rw [hmm, hDn]
        have hkey : (n s : ℝ) - (l : ℝ) ≤ (D : ℝ) * max ((n s : ℝ) / D - ξ) 0 + 1 := by
          rw [hDmul]
          rcases le_total ((n s : ℝ) - ξ * (D : ℝ)) 0 with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
        have hn2D : (n s : ℝ) + (l : ℝ) ≤ 2 * (D : ℝ) := by
          have h1 : (n s : ℝ) ≤ (D : ℝ) := le_of_lt hnsD
          have h2 : (l : ℝ) ≤ (n s : ℝ) := by exact_mod_cast le_of_lt hnsl
          linarith
        have hεpn : εp * ((n s : ℝ) + (l : ℝ)) ≤ 2 * εp * D := by
          have h3 : εp * ((n s : ℝ) + (l : ℝ)) ≤ εp * (2 * (D : ℝ)) :=
            mul_le_mul_of_nonneg_left hn2D (le_of_lt hεp_pos)
          linarith
        have hchain : Chebyshev.theta (n s : ℝ) - Chebyshev.theta (l : ℝ)
            ≤ (D : ℝ) * max ((n s : ℝ) / D - ξ) 0 + 2 * εp * D + 2 * Cθ + 1 := by
          linarith [hθ, hkey, hεpn]
        rw [heq, hfeq]
        have hfin : (D : ℝ) * max ((n s : ℝ) / D - ξ) 0 + 2 * εp * D + 2 * Cθ + 1
            ≤ (D : ℝ) * max ((n s : ℝ) / D - ξ) 0 + (ε + εp) * (n s)
              + (2 + 2 * εp * D + 2 * Cθ + 1) := by
          nlinarith [hs0, hεpos, hεp_pos]
        linarith [hchain, hfin]
    · have hnsl : n s ≤ l := le_of_not_gt hnl
      rw [Lge_eq_one_of_le hnsl, Nat.cast_one, Real.log_one]
      have h1 : 0 ≤ (D : ℝ) * Submission.CDT.IntegratedLcm.modelFun ξ ((n s : ℝ) / D) :=
        mul_nonneg hDR0 (Submission.CDT.IntegratedLcm.modelFun_nonneg ξ _)
      have h2 : 0 ≤ (ε + εp) * ((n s : ℝ)) := by positivity
      have h3 : 0 ≤ 2 + 2 * εp * D + 2 * Cθ + 1 := by positivity
      linarith
  -- ============================== summation ==============================
  have hstep1 : (∑ s : Fin d, Real.log ((Submission.CDT.LcmGe.Lge ⌊ξ * (D : ℝ)⌋₊ (n s) D : ℕ) : ℝ))
      ≤ ∑ s : Fin d, ((D : ℝ) * Submission.CDT.IntegratedLcm.modelFun ξ ((n s : ℝ) / D)
          + (ε + εp) * (n s) + (2 + 2 * εp * D + 2 * Cθ + 1)) := by
    refine Finset.sum_le_sum (fun s _ => ?_)
    have := htper s
    rw [hl] at this
    exact this
  have hstep2 : (∑ s : Fin d, ((D : ℝ) * Submission.CDT.IntegratedLcm.modelFun ξ ((n s : ℝ) / D)
        + (ε + εp) * (n s) + (2 + 2 * εp * D + 2 * Cθ + 1)))
      = (D : ℝ) * (∑ s : Fin d, Submission.CDT.IntegratedLcm.modelFun ξ ((n s : ℝ) / D))
        + (ε + εp) * (∑ s : Fin d, (n s : ℝ))
        + (d : ℝ) * (2 + 2 * εp * D + 2 * Cθ + 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  -- the grid points
  set t : ℕ → ℝ := fun j => (m : ℝ) * (j : ℝ) / (d : ℝ) + 3 * (m : ℝ) * ε with ht
  set j₁ : ℕ := ⌈(ξ - 3 * (m : ℝ) * ε) * (d : ℝ) / (m : ℝ)⌉₊ with hj₁
  have ht_mono : Monotone t := by
    intro a b hab
    simp only [ht]
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have h1 : (m : ℝ) * (a : ℝ) / (d : ℝ) ≤ (m : ℝ) * (b : ℝ) / (d : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left habR hm0) hdR.le
    linarith
  have ht_id : ∀ j : ℕ, t j = (m : ℝ) * (j : ℝ) / (d : ℝ) + 3 * (m : ℝ) * ε := fun j => rfl
  have ht_lt_j₁ : ∀ j : ℕ, j < j₁ → t j ≤ ξ := by
    intro j hj
    rw [hj₁] at hj
    have hlt : (j : ℝ) < (ξ - 3 * (m : ℝ) * ε) * (d : ℝ) / (m : ℝ) := (Nat.lt_ceil).mp hj
    have h2 : (j : ℝ) * (m : ℝ) < (ξ - 3 * (m : ℝ) * ε) * (d : ℝ) := by
      have := (lt_div_iff₀ hmR).mp hlt
      linarith [this]
    have h3 : (m : ℝ) * (j : ℝ) / (d : ℝ) < ξ - 3 * (m : ℝ) * ε := by
      rw [div_lt_iff₀ hdR]
      linarith [mul_comm (j : ℝ) (m : ℝ)]
    simp only [ht]
    linarith
  have hj₁_le : j₁ ≤ d := by
    rw [hj₁, Nat.ceil_le, div_le_iff₀ hmR]
    have h : (ξ - 3 * (m : ℝ) * ε) * (d : ℝ) ≤ (m : ℝ) * (d : ℝ) := by
      have h1 : ξ ≤ (m : ℝ) := hξm
      have h2 : 0 < 3 * (m : ℝ) * ε := by positivity
      nlinarith [hdR, hmR]
    linarith [h]
  have hfs : ∀ s : Fin d, Submission.CDT.IntegratedLcm.modelFun ξ ((n s : ℝ) / D)
      ≤ Submission.CDT.IntegratedLcm.modelFun ξ (t (s : ℕ)) := by
    intro s
    apply modelFun_monotone hξ0
    have hb := hnbound s
    have hb' : (n s : ℝ) ≤ (m : ℝ) * (s : ℝ) * (D : ℝ) / (d : ℝ) + 3 * (m : ℝ) * ε * (D : ℝ) := by
      have h1 : (m : ℝ) * (D : ℝ) * ((s : ℝ) / d) = (m : ℝ) * (s : ℝ) * (D : ℝ) / (d : ℝ) := by ring
      have h2 : (3 : ℝ) * m * ε * D = 3 * (m : ℝ) * ε * (D : ℝ) := by push_cast; ring
      linarith [hb]
    rw [div_le_iff₀ hDR]
    have hDt : (D : ℝ) * t (s : ℕ) = (m : ℝ) * (s : ℝ) * (D : ℝ) / (d : ℝ)
        + 3 * (m : ℝ) * ε * (D : ℝ) := by
      simp only [ht]; ring
    linarith [hb', hDt]
  have hzero : ∀ j : ℕ, j < j₁ → Submission.CDT.IntegratedLcm.modelFun ξ (t j) = 0 :=
    fun j hj => modelFun_eq_zero_of_le hξ0 (ht_lt_j₁ j hj)
  have hstep3 : (∑ s : Fin d, Submission.CDT.IntegratedLcm.modelFun ξ ((n s : ℝ) / D))
      ≤ ∑ j ∈ Finset.Icc j₁ (d - 1), Submission.CDT.IntegratedLcm.modelFun ξ (t j) := by
    calc (∑ s : Fin d, Submission.CDT.IntegratedLcm.modelFun ξ ((n s : ℝ) / D))
        ≤ ∑ s : Fin d, Submission.CDT.IntegratedLcm.modelFun ξ (t (s : ℕ)) :=
          Finset.sum_le_sum (fun s _ => hfs s)
      _ = ∑ j ∈ Finset.Icc j₁ (d - 1), Submission.CDT.IntegratedLcm.modelFun ξ (t j) :=
          sum_fin_eq_sum_Icc_of_zero hd hzero
  have htile : ∑ j ∈ Finset.Icc j₁ (d - 1), Submission.CDT.IntegratedLcm.modelFun ξ (t j)
      ≤ ((d : ℝ) / (m : ℝ)) * ∫ u in (t j₁)..(t d), Submission.CDT.IntegratedLcm.modelFun ξ u := by
    have h := sum_mul_le_integral_of_monotone hd (modelFun_monotone hξ0) (a := 3 * (m : ℝ) * ε)
      (h := (m : ℝ) / (d : ℝ)) (div_nonneg hm0 hdR.le) hj₁_le
    have hL : (∑ j ∈ Finset.Icc j₁ (d - 1),
          ((m : ℝ) / (d : ℝ)) * Submission.CDT.IntegratedLcm.modelFun ξ (3 * (m : ℝ) * ε + (j : ℝ) * ((m : ℝ) / (d : ℝ))))
        = ((m : ℝ) / (d : ℝ)) * ∑ j ∈ Finset.Icc j₁ (d - 1), Submission.CDT.IntegratedLcm.modelFun ξ (t j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      simp only [ht]
      ring_nf
    have hR : 3 * (m : ℝ) * ε + (j₁ : ℝ) * ((m : ℝ) / (d : ℝ)) = t j₁ := by
      simp only [ht]; ring_nf
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
    have hR2 : 3 * (m : ℝ) * ε + (d : ℝ) * ((m : ℝ) / (d : ℝ)) = t d := by
      simp only [ht]
      field_simp
      ring
    rw [hL, hR, hR2] at h
    have hmd : (0 : ℝ) < (d : ℝ) / (m : ℝ) := div_pos hdR hmR
    have h' := mul_le_mul_of_nonneg_left h hmd.le
    have hsimp : (d : ℝ) / (m : ℝ)
        * (((m : ℝ) / (d : ℝ)) * ∑ j ∈ Finset.Icc j₁ (d - 1), Submission.CDT.IntegratedLcm.modelFun ξ (t j))
        = ∑ j ∈ Finset.Icc j₁ (d - 1), Submission.CDT.IntegratedLcm.modelFun ξ (t j) := by
      rw [← mul_assoc]
      have h1 : (d : ℝ) / (m : ℝ) * ((m : ℝ) / (d : ℝ)) = 1 := by field_simp
      rw [h1, one_mul]
    rwa [hsimp] at h'
  have htj : ξ ≤ t j₁ := by
    have hceil : (ξ - 3 * (m : ℝ) * ε) * (d : ℝ) / (m : ℝ) ≤ (j₁ : ℝ) := by
      rw [hj₁]; exact Nat.le_ceil _
    have hmul : (m : ℝ) * ((ξ - 3 * (m : ℝ) * ε) * (d : ℝ) / (m : ℝ)) / (d : ℝ) = ξ - 3 * (m : ℝ) * ε := by
      field_simp
    have hstep : (m : ℝ) * ((ξ - 3 * (m : ℝ) * ε) * (d : ℝ) / (m : ℝ)) / (d : ℝ)
        ≤ (m : ℝ) * (j₁ : ℝ) / (d : ℝ) := by
      apply div_le_div_of_nonneg_right _ hdR.le
      exact mul_le_mul_of_nonneg_left hceil hm0
    simp only [ht]
    linarith [hstep, hmul]
  have hint : ∫ u in (t j₁)..(t d), Submission.CDT.IntegratedLcm.modelFun ξ u
      ≤ ∫ u in ξ..((m : ℝ) + 3 * (m : ℝ) * ε), Submission.CDT.IntegratedLcm.modelFun ξ u := by
    have htd : t d = (m : ℝ) + 3 * (m : ℝ) * ε := by
      simp only [ht]
      field_simp
    have hii : IntervalIntegrable (Submission.CDT.IntegratedLcm.modelFun ξ) MeasureTheory.volume ξ (t j₁) :=
      (modelFun_monotone hξ0).intervalIntegrable
    have hii2 : IntervalIntegrable (Submission.CDT.IntegratedLcm.modelFun ξ) MeasureTheory.volume (t j₁) (t d) :=
      (modelFun_monotone hξ0).intervalIntegrable
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hii hii2
    have hnn : 0 ≤ ∫ u in ξ..(t j₁), Submission.CDT.IntegratedLcm.modelFun ξ u :=
      intervalIntegral.integral_nonneg htj (fun u _ => Submission.CDT.IntegratedLcm.modelFun_nonneg ξ u)
    rw [htd] at hsplit ⊢
    linarith [hsplit, hnn]
  -- final bound: the integral over [ξ, m+3mε]
  have hmain : (∑ j ∈ Finset.Icc j₁ (d - 1), Submission.CDT.IntegratedLcm.modelFun ξ (t j)) * D
      ≤ (d : ℝ) * D / (m : ℝ) * (Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ + η / 2) := by
    have hI := integratedLcm_eq_integral_modelFun hm hξ0 hξm
    have hsplit2 : ∫ u in ξ..((m : ℝ) + 3 * (m : ℝ) * ε), Submission.CDT.IntegratedLcm.modelFun ξ u
        = (∫ u in ξ..(m : ℝ), Submission.CDT.IntegratedLcm.modelFun ξ u)
          + ∫ u in (m : ℝ)..((m : ℝ) + 3 * (m : ℝ) * ε), Submission.CDT.IntegratedLcm.modelFun ξ u := by
      have h3 : (ξ : ℝ) ≤ (m : ℝ) := hξm
      have h4 : (m : ℝ) ≤ (m : ℝ) + 3 * (m : ℝ) * ε := by
        have : 0 ≤ 3 * (m : ℝ) * ε := by positivity
        linarith
      have hii1 : IntervalIntegrable (Submission.CDT.IntegratedLcm.modelFun ξ) MeasureTheory.volume
          ξ (m : ℝ) := (modelFun_monotone hξ0).intervalIntegrable
      have hii2 : IntervalIntegrable (Submission.CDT.IntegratedLcm.modelFun ξ) MeasureTheory.volume
          (m : ℝ) ((m : ℝ) + 3 * (m : ℝ) * ε) := (modelFun_monotone hξ0).intervalIntegrable
      exact (intervalIntegral.integral_add_adjacent_intervals hii1 hii2).symm
    have hbound_int : ∫ u in (m : ℝ)..((m : ℝ) + 3 * (m : ℝ) * ε), Submission.CDT.IntegratedLcm.modelFun ξ u
        ≤ 3 * (m : ℝ) * ε * Smax := by
      have hle : (m : ℝ) ≤ (m : ℝ) + 3 * (m : ℝ) * ε := by
        have : 0 ≤ 3 * (m : ℝ) * ε := by positivity
        linarith
      have hmono : ∀ u ∈ Set.Icc (m : ℝ) ((m : ℝ) + 3 * (m : ℝ) * ε),
          Submission.CDT.IntegratedLcm.modelFun ξ u ≤ Smax := by
        intro u hu
        have hu1 : u ≤ (m : ℝ) + 1 := by
          have hε₀_small : 3 * (m : ℝ) * ε₀ ≤ 1 := by
            have h := hε₀_le1
            rw [le_div_iff₀ (by positivity : (0:ℝ) < 3 * (m:ℝ))] at h
            linarith
          nlinarith [hu.2, hεlt.le, hε₀_small, hm0, hεpos]
        exact modelFun_le_sup hξ0 hξm (le_trans hm0 hu.1) hu1
      have hii : IntervalIntegrable (Submission.CDT.IntegratedLcm.modelFun ξ) MeasureTheory.volume
          (m : ℝ) ((m : ℝ) + 3 * (m : ℝ) * ε) := (modelFun_monotone hξ0).intervalIntegrable
      have h2 := intervalIntegral.integral_mono_on hle hii intervalIntegrable_const hmono
      have h3 : ∫ u in (m : ℝ)..((m : ℝ) + 3 * (m : ℝ) * ε), Smax
          = 3 * (m : ℝ) * ε * Smax := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      linarith [h2, h3]
    have hshift : 3 * (m : ℝ) * ε * Smax ≤ η / 4 := by
      have h1 : 3 * (m : ℝ) * ε ≤ 3 * (m : ℝ) * ε₀ := by nlinarith [hεlt.le, hm0]
      have h2 : 3 * (m : ℝ) * ε₀ * Smax ≤ η / 4 := by
        have h := hε₀_le3
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 12 * (m:ℝ) * Smax)] at h
        nlinarith [h, hSmaxpos, hmR]
      nlinarith [h1, h2, hSmaxpos]
    have hfin : ((d : ℝ) / (m : ℝ)) * (Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ + η / 2) * D
        = (d : ℝ) * D / (m : ℝ) * (Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ + η / 2) := by
      ring
    calc (∑ j ∈ Finset.Icc j₁ (d - 1), Submission.CDT.IntegratedLcm.modelFun ξ (t j)) * D
        ≤ (((d : ℝ) / (m : ℝ)) * ∫ u in (t j₁)..(t d), Submission.CDT.IntegratedLcm.modelFun ξ u) * D := by
          exact mul_le_mul_of_nonneg_right htile hDR0
      _ ≤ (((d : ℝ) / (m : ℝ))
            * ((Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ) + η / 2)) * D := by
          have h1 : ∫ u in (t j₁)..(t d), Submission.CDT.IntegratedLcm.modelFun ξ u
              ≤ (∫ u in ξ..(m : ℝ), Submission.CDT.IntegratedLcm.modelFun ξ u) + η / 2 := by
            have h0 := hint
            rw [hsplit2, ← hI] at h0
            rw [← hI]
            linarith [h0, hbound_int, hshift]
          have h2 : 0 ≤ (d : ℝ) / (m : ℝ) := by positivity
          have h3 : (∫ u in (t j₁)..(t d), Submission.CDT.IntegratedLcm.modelFun ξ u) * ((d:ℝ)/(m:ℝ))
              ≤ ((∫ u in ξ..(m : ℝ), Submission.CDT.IntegratedLcm.modelFun ξ u) + η/2) * ((d:ℝ)/(m:ℝ)) :=
            mul_le_mul_of_nonneg_right h1 h2
          have h4 : (∫ u in ξ..(m : ℝ), Submission.CDT.IntegratedLcm.modelFun ξ u)
              = Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ := hI.symm
          rw [h4] at h3
          nlinarith [h3]
      _ = (d : ℝ) * D / (m : ℝ) * (Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ + η / 2) := hfin
  -- error terms
  have herr : (ε + εp) * (∑ s : Fin d, (n s : ℝ)) + (d : ℝ) * (2 + 2 * εp * D + 2 * Cθ + 1)
      ≤ (d : ℝ) * D / (m : ℝ) * (η / 2) := by
    have hsum_n : (∑ s : Fin d, (n s : ℝ))
        ≤ (d : ℝ) * ((m : ℝ) * D + 3 * (m : ℝ) * ε * D) := by
      calc (∑ s : Fin d, (n s : ℝ))
          ≤ ∑ _s : Fin d, ((m : ℝ) * D + 3 * (m : ℝ) * ε * D) := by
            refine Finset.sum_le_sum (fun s _ => ?_)
            have hb := hnbound s
            have hsd : (s : ℝ) / d ≤ 1 := by
              rw [div_le_one hdR]
              exact_mod_cast (le_of_lt s.isLt)
            have hmD : (0 : ℝ) < (m : ℝ) * D := by positivity
            have h1 : (m : ℝ) * D * ((s : ℝ) / d) ≤ (m : ℝ) * D := by
              nlinarith [hsd, hmD]
            have h2 : (3 : ℝ) * m * ε * D = 3 * (m : ℝ) * ε * D := by push_cast; ring
            linarith [hb, h1]
        _ = (d : ℝ) * ((m : ℝ) * D + 3 * (m : ℝ) * ε * D) := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hεsum : (ε + εp) * (∑ s : Fin d, (n s : ℝ))
        ≤ (d : ℝ) * D / (m : ℝ) * (η / 4) := by
      have hsum2 : ε + εp ≤ η / (32 * (m : ℝ) ^ 2) := by
        have ha : ε ≤ η / (64 * (m : ℝ) ^ 2) := le_trans hεlt.le hε₀_le2
        have h2 : η / (64 * (m : ℝ) ^ 2) + η / (64 * (m : ℝ) ^ 2) = η / (32 * (m : ℝ) ^ 2) := by
          ring
        calc ε + εp ≤ η / (64 * (m : ℝ) ^ 2) + η / (64 * (m : ℝ) ^ 2) := add_le_add ha hεp_small
          _ = η / (32 * (m : ℝ) ^ 2) := h2
      have hε3 : 1 + 3 * ε ≤ 2 := by
        have h := hε₀_le1
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 3 * (m : ℝ))] at h
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have h4 : 3 * ε ≤ 3 * (m : ℝ) * ε₀ := by nlinarith [hεlt.le, hm1, hε₀_pos]
        have h5 : 3 * ε ≤ 1 := by nlinarith [h, h4]
        linarith [h5]
      have hkey : (m : ℝ) ^ 2 * (ε + εp) * (1 + 3 * ε) ≤ η / 4 := by
        have h1 : (m : ℝ) ^ 2 * (ε + εp) ≤ (m : ℝ) ^ 2 * (η / (32 * (m : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum2 (by positivity)
        have h2 : (m : ℝ) ^ 2 * (η / (32 * (m : ℝ) ^ 2)) = η / 32 := by
          field_simp
        nlinarith [h1, h2, hε3, hη]
      have h3 : (ε + εp) * ((d : ℝ) * ((m : ℝ) * D + 3 * (m : ℝ) * ε * D))
          = (d : ℝ) * D * ((m : ℝ) * (ε + εp) * (1 + 3 * ε)) := by ring
      have h4 : (d : ℝ) * D * ((m : ℝ) * (ε + εp) * (1 + 3 * ε))
          = (d : ℝ) * D / (m : ℝ) * ((m : ℝ) ^ 2 * (ε + εp) * (1 + 3 * ε)) := by
        field_simp
      have h5 : (d : ℝ) * D / (m : ℝ) * ((m : ℝ) ^ 2 * (ε + εp) * (1 + 3 * ε))
          ≤ (d : ℝ) * D / (m : ℝ) * (η / 4) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
      have h6 : (ε + εp) * (∑ s : Fin d, (n s : ℝ))
          ≤ (ε + εp) * ((d : ℝ) * ((m : ℝ) * D + 3 * (m : ℝ) * ε * D)) :=
        mul_le_mul_of_nonneg_left hsum_n (by positivity)
      linarith [h6, h3, h4, h5]
    have hK : (d : ℝ) * (2 + 2 * εp * D + 2 * Cθ + 1)
        ≤ (d : ℝ) * D / (m : ℝ) * (η / 4) := by
      have h1 : (d : ℝ) * (2 * Cθ + 3) ≤ (d : ℝ) * D / (m : ℝ) * (η / 8) := by
        have h2 : 8 * (m : ℝ) * (2 * Cθ + 3) ≤ D * η := by
          have h3 := mul_le_mul_of_nonneg_right hDC hη.le
          have h4 : 16 * (m : ℝ) * (2 * Cθ + 3) / η * η = 16 * (m : ℝ) * (2 * Cθ + 3) := by
            field_simp
          rw [h4] at h3
          have h5 : 8 * (m : ℝ) * (2 * Cθ + 3) ≤ 16 * (m : ℝ) * (2 * Cθ + 3) := by
            nlinarith [hCθnn, hm0]
          linarith [h3, h5]
        have h4 : (d : ℝ) * D / (m : ℝ) * (η / 8) = d * D * η / (8 * m) := by ring
        have h5 : d * (2 * Cθ + 3) ≤ d * D * η / (8 * m) := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (m : ℝ))]
          have h7 : 8 * (m : ℝ) * (2 * Cθ + 3) * d ≤ D * η * d :=
            mul_le_mul_of_nonneg_right h2 (le_of_lt hdR)
          have h6 : (d : ℝ) * (2 * Cθ + 3) * (8 * (m : ℝ))
              = 8 * (m : ℝ) * (2 * Cθ + 3) * d := by ring
          have h8 : D * η * d = d * D * η := by ring
          linarith [h7, h6, h8]
        linarith [h4, h5]
      have h2 : (d : ℝ) * (2 * εp * D) ≤ (d : ℝ) * D / (m : ℝ) * (η / 8) := by
        have h3 : 16 * (m : ℝ) * εp ≤ η := by linarith [hεp_le]
        have h4 : (d : ℝ) * D / (m : ℝ) * (η / 8) = d * D * η / (8 * m) := by ring
        have h5 : d * (2 * εp * D) ≤ d * D * η / (8 * m) := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (m : ℝ))]
          have h7 : 16 * (m : ℝ) * εp * (d * D) ≤ η * (d * D) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
          have h6 : (d : ℝ) * (2 * εp * D) * (8 * (m : ℝ))
              = 16 * (m : ℝ) * εp * (d * D) := by ring
          have h8 : η * (d * D) = d * D * η := by ring
          linarith [h7, h6, h8]
        linarith [h4, h5]
      have h4 : (d : ℝ) * (2 + 2 * εp * D + 2 * Cθ + 1)
          = (d : ℝ) * (2 * Cθ + 3) + (d : ℝ) * (2 * εp * D) := by ring
      have h5 : (d : ℝ) * D / (m : ℝ) * (η / 8) + (d : ℝ) * D / (m : ℝ) * (η / 8)
          = (d : ℝ) * D / (m : ℝ) * (η / 4) := by ring
      linarith [h1, h2, h4, h5]
    linarith [hεsum, hK]
  -- assembly
  have htot := le_trans hstep1 (le_of_eq hstep2)
  have hmain2 : (D : ℝ) * (∑ s : Fin d, Submission.CDT.IntegratedLcm.modelFun ξ ((n s : ℝ) / D))
      ≤ (d : ℝ) * D / (m : ℝ) * (Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ + η / 2) := by
    have h1 : (D : ℝ) * (∑ s : Fin d, Submission.CDT.IntegratedLcm.modelFun ξ ((n s : ℝ) / D))
        ≤ (D : ℝ) * ∑ j ∈ Finset.Icc j₁ (d - 1), Submission.CDT.IntegratedLcm.modelFun ξ (t j) :=
      mul_le_mul_of_nonneg_left hstep3 hDR0
    have h2 : (D : ℝ) * (∑ j ∈ Finset.Icc j₁ (d - 1), Submission.CDT.IntegratedLcm.modelFun ξ (t j))
        = (∑ j ∈ Finset.Icc j₁ (d - 1), Submission.CDT.IntegratedLcm.modelFun ξ (t j)) * D := by
      ring
    linarith [h1, h2, hmain]
  have hfinal : (d : ℝ) * D / (m : ℝ) * (Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ + η / 2)
      + (d : ℝ) * D / (m : ℝ) * (η / 2)
      = (d : ℝ) * D / (m : ℝ) * (Submission.CDTPlan.integratedLcm ξ (m : ℝ) ξ + η) := by ring
  linarith [htot, hmain2, herr, hfinal]

end Work.Holonomy3
