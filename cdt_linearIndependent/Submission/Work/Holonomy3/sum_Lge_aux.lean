import Mathlib
import Submission.Work.Holonomy3.model_deps

/-!
# Elementary helpers for the `τ♯` window-sum estimate
-/

namespace Work.Holonomy3

open scoped BigOperators

/-- For `n ≤ l` the window product `L^{≥l}_{n,D}` is empty (so it equals `1`). -/
theorem Lge_eq_one_of_le {l D n : ℕ} (h : n ≤ l) : Submission.CDT.LcmGe.Lge l n D = 1 := by
  unfold Submission.CDT.LcmGe.Lge
  rw [Finset.prod_eq_one]
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp
  omega

/-- An explicit bound for the model function on `[0, m+1]` when `0 ≤ ξ ≤ m`:
`modelFun ξ t ≤ H m + (m+1)`, where `H m = Σ_{a ≤ m} 1/a`. -/
theorem modelFun_le_sup {ξ : ℝ} (hξ0 : 0 ≤ ξ) {m : ℕ} (hξm : ξ ≤ (m : ℝ)) {t : ℝ}
    (ht0 : 0 ≤ t) (htm : t ≤ (m : ℝ) + 1) :
    Submission.CDT.IntegratedLcm.modelFun ξ t
      ≤ Submission.CDT.Lcm2Bound.H m + ((m : ℝ) + 1) := by
  have hHnn : 0 ≤ Submission.CDT.Lcm2Bound.H m :=
    Finset.sum_nonneg (fun a _ => by positivity)
  have hB : (0 : ℝ) < max 1 ξ := lt_of_lt_of_le one_pos (le_max_left _ _)
  rcases le_or_gt t 1 with ht | ht
  · rw [Submission.CDT.IntegratedLcm.modelFun_of_le_one ξ t ht]
    have h1 : max (t - ξ) 0 ≤ (m : ℝ) + 1 := by
      rcases le_total ξ t with hle | hle
      · rw [max_eq_left (by linarith)]
        linarith
      · rw [max_eq_right (by linarith)]
        linarith
    linarith
  · have hq1 : 1 ≤ ⌊(t + max 0 (ξ - 1)) / max 1 ξ⌋₊ := by
      refine Nat.le_floor ?_
      push_cast
      rw [le_div_iff₀ hB]
      have hle : max 1 ξ ≤ t + max 0 (ξ - 1) := by
        rcases le_total 1 ξ with hle | hle
        · rw [max_eq_right hle, max_eq_right (by linarith)]
          linarith
        · rw [max_eq_left hle, max_eq_left (by linarith)]
          linarith
      linarith
    have hcorr : Submission.CDT.IntegratedLcm.correctionFun ξ t ≤ (m : ℝ) + 1 := by
      unfold Submission.CDT.IntegratedLcm.correctionFun
      refine max_le ?_ (by positivity)
      have hcast : (1 : ℝ) ≤ ((⌊(t + max 0 (ξ - 1)) / max 1 ξ⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hq1
      have hle : t / ((⌊(t + max 0 (ξ - 1)) / max 1 ξ⌋₊ : ℕ) : ℝ) ≤ t := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    have hharm : Submission.CDT.IntegratedLcm.harmonicFun ξ t ≤ Submission.CDT.Lcm2Bound.H m := by
      have hk : ⌊(t - 1) / max 1 ξ⌋₊ ≤ m := by
        have h0 : 0 ≤ (t - 1) / max 1 ξ := div_nonneg (by linarith) hB.le
        have h1 : ((⌊(t - 1) / max 1 ξ⌋₊ : ℕ) : ℝ) ≤ (t - 1) / max 1 ξ := Nat.floor_le h0
        have h2 : (t - 1) / max 1 ξ ≤ (m : ℝ) := by
          rw [div_le_iff₀ hB]
          nlinarith [le_max_left (1 : ℝ) ξ, htm]
        exact_mod_cast le_trans h1 h2
      have hEq : Submission.CDT.IntegratedLcm.harmonicFun ξ t
          = ∑ a ∈ Finset.Icc 1 ⌊(t - 1) / max 1 ξ⌋₊, ((a : ℝ))⁻¹ := by
        rw [Submission.CDT.IntegratedLcm.harmonicFun]
        exact Finset.sum_congr rfl (fun a _ => one_div (a : ℝ))
      rw [hEq, Submission.CDT.Lcm2Bound.H]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun a ha => by
          simp only [Finset.mem_Icc] at ha ⊢
          exact ⟨ha.1, le_trans ha.2 hk⟩)
        (fun a _ _ => by positivity)
    rw [Submission.CDT.IntegratedLcm.modelFun_of_lt ξ t ht]
    linarith

/-- `modelFun ξ` vanishes on `(-∞, ξ]` when `0 ≤ ξ`: it is continuous and nondecreasing with
`modelFun ξ ξ = 0`. -/
theorem modelFun_eq_zero_of_le {ξ t : ℝ} (hξ0 : 0 ≤ ξ) (h : t ≤ ξ) :
    Submission.CDT.IntegratedLcm.modelFun ξ t = 0 := by
  have hB : (0 : ℝ) < max 1 ξ := lt_of_lt_of_le one_pos (le_max_left _ _)
  rcases le_or_gt t 1 with ht | ht
  · rw [Submission.CDT.IntegratedLcm.modelFun_of_le_one ξ t ht, max_eq_right (by linarith)]
  · have ht1 : (1 : ℝ) < t := ht
    have hq1 : 1 ≤ ⌊(t + max 0 (ξ - 1)) / max 1 ξ⌋₊ := by
      refine Nat.le_floor ?_
      push_cast
      rw [le_div_iff₀ hB]
      rcases le_total 1 ξ with hle | hle
      · rw [max_eq_right hle, max_eq_right (by linarith)]
        linarith
      · rw [max_eq_left hle, max_eq_left (by linarith)]
        linarith
    rw [Submission.CDT.IntegratedLcm.modelFun_of_lt ξ t ht1]
    have hharm : Submission.CDT.IntegratedLcm.harmonicFun ξ t = 0 := by
      unfold Submission.CDT.IntegratedLcm.harmonicFun
      rw [Finset.sum_eq_zero]
      intro a ha
      simp only [Finset.mem_Icc] at ha
      exfalso
      have hlt : (t - 1) / max 1 ξ < 1 := by
        rw [div_lt_one hB]
        rcases le_total 1 ξ with hle | hle
        · rw [max_eq_right hle]; linarith
        · rw [max_eq_left hle]; linarith
      have hz : ⌊(t - 1) / max 1 ξ⌋₊ = 0 := by
        rw [Nat.floor_eq_zero]
        linarith
      omega
    have hcorr : Submission.CDT.IntegratedLcm.correctionFun ξ t = 0 := by
      unfold Submission.CDT.IntegratedLcm.correctionFun
      rw [max_eq_right]
      have hq : (1 : ℝ) ≤ ((⌊(t + max 0 (ξ - 1)) / max 1 ξ⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hq1
      have hle : t / ((⌊(t + max 0 (ξ - 1)) / max 1 ξ⌋₊ : ℕ) : ℝ) ≤ t := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    rw [hharm, hcorr, add_zero]

/-- `Σ_{s : Fin d} g s = Σ_{j ∈ Icc j₁ (d-1)} g j` for a function `g` vanishing below `j₁`. -/
theorem sum_fin_eq_sum_Icc_of_zero {d j₁ : ℕ} (hd : 1 ≤ d) {g : ℕ → ℝ}
    (hzero : ∀ j, j < j₁ → g j = 0) :
    (∑ s : Fin d, g (s : ℕ)) = ∑ j ∈ Finset.Icc j₁ (d - 1), g j := by
  rw [Fin.sum_univ_eq_sum_range]
  have hset : Finset.Icc j₁ (d - 1) = (Finset.range d).filter (fun j => j₁ ≤ j) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by omega⟩
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : j₁ ≤ j
  · rw [if_pos h]
  · rw [if_neg h, hzero j (Nat.lt_of_not_le h)]

end Work.Holonomy3
