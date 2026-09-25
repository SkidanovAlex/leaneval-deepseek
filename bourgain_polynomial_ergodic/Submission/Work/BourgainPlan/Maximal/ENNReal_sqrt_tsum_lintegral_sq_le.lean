import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSymbolDefs

namespace Work.BourgainPlan.Maximal

open MeasureTheory ENNReal

/-- Cauchy–Schwarz for finite sums in `ℝ≥0∞` (obtained from Hölder with the counting measure). -/
lemma ennreal_finset_sum_mul_le_sqrt_mul_sqrt (s : Finset ℤ) (a b : ℤ → ℝ≥0∞) :
    ∑ n ∈ s, a n * b n
      ≤ (∑ n ∈ s, a n ^ (2:ℝ)) ^ ((1:ℝ)/2) * (∑ n ∈ s, b n ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
  have hc : Real.HolderConjugate (2:ℝ) (2:ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ↥s) hc
    (f := fun n : ↥s => a n) (g := fun n : ↥s => b n) (by measurability) (by measurability)
  rw [lintegral_count, lintegral_count, lintegral_count] at h
  simp only [Pi.mul_apply] at h
  rw [tsum_fintype] at h
  rw [tsum_fintype] at h
  rw [tsum_fintype] at h
  rwa [Finset.sum_coe_sort s (fun n => a n * b n),
    Finset.sum_coe_sort s (fun n => a n ^ (2:ℝ)),
    Finset.sum_coe_sort s (fun n => b n ^ (2:ℝ))] at h

lemma ennreal_rpow_half_sq (x : ℝ≥0∞) : (x ^ ((1:ℝ)/2)) ^ (2:ℝ) = x := by
  rw [← ENNReal.rpow_mul, show ((1:ℝ)/2) * 2 = 1 by norm_num, ENNReal.rpow_one]

lemma ennreal_rpow_sq_half (x : ℝ≥0∞) : (x ^ (2:ℝ)) ^ ((1:ℝ)/2) = x := by
  rw [← ENNReal.rpow_mul, show (2:ℝ) * ((1:ℝ)/2) = 1 by norm_num, ENNReal.rpow_one]

lemma ennreal_rpow_two_eq_mul (x : ℝ≥0∞) : x ^ (2:ℝ) = x * x := by
  rw [ENNReal.rpow_two, pow_two]

lemma ennreal_rpow_half_ne_top {x : ℝ≥0∞} (h : x ≠ ∞) : x ^ ((1:ℝ)/2) ≠ ∞ := by
  intro hh
  rw [ENNReal.rpow_eq_top_iff] at hh
  rcases hh with ⟨-, hlt⟩ | ⟨htop, -⟩
  · exact absurd hlt (by norm_num)
  · exact h htop

lemma ennreal_rpow_two_ne_top {x : ℝ≥0∞} (h : x ≠ ∞) : x ^ (2:ℝ) ≠ ∞ := by
  intro hh
  rw [ENNReal.rpow_eq_top_iff] at hh
  rcases hh with ⟨-, hlt⟩ | ⟨htop, -⟩
  · exact absurd hlt (by norm_num)
  · exact h htop

/-- Minkowski's integral inequality, finite index set version, for measurable `f`. -/
lemma finite_minkowski (f : ℤ → ℝ → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) (s : Finset ℤ)
    (ha : ∀ n, ∫⁻ y, f n y ≠ ∞) :
    (∑ n ∈ s, (∫⁻ y, f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2)
      ≤ ∫⁻ y, (∑' n, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
  set A := ∑ n ∈ s, (∫⁻ y, f n y) ^ (2:ℝ) with hA
  set L := ∫⁻ y, (∑' n, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) with hL
  have hAne : A ≠ ∞ := by
    rw [hA]
    exact ne_of_lt (ENNReal.sum_lt_top.mpr
      (fun n _ => lt_top_iff_ne_top.mpr (ennreal_rpow_two_ne_top (ha n))))
  have h1 : A = ∫⁻ y, ∑ n ∈ s, (∫⁻ y, f n y) * f n y := by
    rw [hA, lintegral_finsetSum s (fun n _ => (hf n).const_mul (∫⁻ y, f n y))]
    apply Finset.sum_congr rfl
    intro n _
    rw [ennreal_rpow_two_eq_mul, ← lintegral_const_mul' (∫⁻ y, f n y) (f n) (ha n)]
  have h2 : ∀ y, ∑ n ∈ s, (∫⁻ y, f n y) * f n y
      ≤ A ^ ((1:ℝ)/2) * (∑' n, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
    intro y
    calc ∑ n ∈ s, (∫⁻ y, f n y) * f n y
        ≤ (∑ n ∈ s, (∫⁻ y, f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2)
            * (∑ n ∈ s, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) :=
          ennreal_finset_sum_mul_le_sqrt_mul_sqrt s _ _
      _ = A ^ ((1:ℝ)/2) * (∑ n ∈ s, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) := by rw [hA]
      _ ≤ A ^ ((1:ℝ)/2) * (∑' n, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) :=
          mul_le_mul_right (ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by norm_num : (0:ℝ) ≤ 1/2)) _
  have h3 : A ≤ A ^ ((1:ℝ)/2) * L := by
    have h35 : A ≤ ∫⁻ y, A ^ ((1:ℝ)/2) * (∑' n, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
      nth_rewrite 1 [h1]
      exact lintegral_mono h2
    rw [lintegral_const_mul' _ _ (ennreal_rpow_half_ne_top hAne)] at h35
    rwa [← hL] at h35
  by_cases hA0 : A = 0
  · rw [hA0, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)]
    exact zero_le
  · have hApos : A ^ ((1:ℝ)/2) ≠ 0 := by
      intro hh
      apply hA0
      have hh2 := ennreal_rpow_half_sq A
      rw [hh, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)] at hh2
      exact hh2.symm
    have hmul : A ^ ((1:ℝ)/2) * A ^ ((1:ℝ)/2) ≤ A ^ ((1:ℝ)/2) * L := by
      rw [← ennreal_rpow_two_eq_mul (A ^ ((1:ℝ)/2)), ennreal_rpow_half_sq]
      exact h3
    exact (ENNReal.mul_le_mul_iff_right hApos (ennreal_rpow_half_ne_top hAne)).mp hmul

/-- Minkowski's integral inequality for measurable `f` with finite integrals. -/
lemma measurable_case (f : ℤ → ℝ → ℝ≥0∞) (hf : ∀ n, Measurable (f n))
    (ha : ∀ n, ∫⁻ y, f n y ≠ ∞) :
    (∑' n : ℤ, (∫⁻ y : ℝ, f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2)
      ≤ ∫⁻ y : ℝ, (∑' n : ℤ, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
  set L := ∫⁻ y : ℝ, (∑' n : ℤ, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) with hL
  have key2 : ∀ s : Finset ℤ,
      (∑ n ∈ s, (∫⁻ y : ℝ, f n y) ^ (2:ℝ)) ≤ L ^ (2:ℝ) := by
    intro s
    exact (le_of_eq (ennreal_rpow_half_sq _).symm).trans
      (ENNReal.rpow_le_rpow (finite_minkowski f hf s ha) (by norm_num : (0:ℝ) ≤ 2))
  have key3 : (∑' n : ℤ, (∫⁻ y : ℝ, f n y) ^ (2:ℝ)) ≤ L ^ (2:ℝ) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le key2
  calc (∑' n : ℤ, (∫⁻ y : ℝ, f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2)
      ≤ (L ^ (2:ℝ)) ^ ((1:ℝ)/2) := ENNReal.rpow_le_rpow key3 (by norm_num : (0:ℝ) ≤ 1/2)
    _ = L := ennreal_rpow_sq_half L

theorem ENNReal_sqrt_tsum_lintegral_sq_le (f : ℤ → ℝ → ENNReal) :
    (∑' n : ℤ, (∫⁻ y : ℝ, f n y) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ ∫⁻ y : ℝ, (∑' n : ℤ, (f n y) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  by_cases hex : ∃ n, ∫⁻ y : ℝ, f n y = ∞
  · obtain ⟨n0, hn0⟩ := hex
    have hLHS : (∑' n : ℤ, (∫⁻ y : ℝ, f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) = ∞ := by
      have hge : (∫⁻ y : ℝ, f n0 y) ^ (2:ℝ)
          ≤ (∑' n : ℤ, (∫⁻ y : ℝ, f n y) ^ (2:ℝ)) :=
            ENNReal.le_tsum (f := fun n => (∫⁻ y : ℝ, f n y) ^ (2:ℝ)) n0
      rw [hn0, ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 2)] at hge
      rw [top_le_iff.mp hge, ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)]
    have hRHS : ∫⁻ y : ℝ, (∑' n : ℤ, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) = ∞ := by
      have hle : (fun y => f n0 y)
          ≤ (fun y => (∑' n : ℤ, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2)) := by
        intro y
        calc f n0 y = ((f n0 y) ^ (2:ℝ)) ^ ((1:ℝ)/2) := (ennreal_rpow_sq_half _).symm
          _ ≤ (∑' n : ℤ, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) :=
              ENNReal.rpow_le_rpow (ENNReal.le_tsum (f := fun n => (f n y) ^ (2:ℝ)) n0) (by norm_num : (0:ℝ) ≤ 1/2)
      have hmono := lintegral_mono (μ := volume) hle
      rw [hn0] at hmono
      exact top_le_iff.mp hmono
    exact hLHS.le.trans (le_of_eq hRHS.symm)
  · push Not at hex
    choose g hgm hgf hgint using fun n =>
      exists_measurable_le_lintegral_eq (volume : Measure ℝ) (fun y => f n y)
    have hgfinite : ∀ n, ∫⁻ y : ℝ, g n y ≠ ∞ := by intro n; rw [← hgint n]; exact hex n
    have hmain := measurable_case g hgm hgfinite
    have hLHS_eq : (∑' n : ℤ, (∫⁻ y : ℝ, f n y) ^ (2:ℝ))
        = (∑' n : ℤ, (∫⁻ y : ℝ, g n y) ^ (2:ℝ)) := by
      apply tsum_congr
      intro n
      rw [hgint n]
    have hRHS_le : ∫⁻ y : ℝ, (∑' n : ℤ, (g n y) ^ (2:ℝ)) ^ ((1:ℝ)/2)
        ≤ ∫⁻ y : ℝ, (∑' n : ℤ, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
      apply lintegral_mono
      intro y
      exact ENNReal.rpow_le_rpow
        (ENNReal.tsum_le_tsum (fun n => ENNReal.rpow_le_rpow (hgf n y) (by norm_num : (0:ℝ) ≤ 2)))
        (by norm_num : (0:ℝ) ≤ 1/2)
    calc (∑' n : ℤ, (∫⁻ y : ℝ, f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2)
        = (∑' n : ℤ, (∫⁻ y : ℝ, g n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) := by rw [hLHS_eq]
      _ ≤ ∫⁻ y : ℝ, (∑' n : ℤ, (g n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) := hmain
      _ ≤ ∫⁻ y : ℝ, (∑' n : ℤ, (f n y) ^ (2:ℝ)) ^ ((1:ℝ)/2) := hRHS_le

end Work.BourgainPlan.Maximal
