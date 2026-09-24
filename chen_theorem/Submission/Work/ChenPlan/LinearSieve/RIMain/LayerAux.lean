import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.ErrProfile
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_le_decay

/-!
# Bookkeeping lemmas for the layer-to-main-term glue

Reindexing of the layer index `n` (`Σ_{n odd, n<N}` ↦ `Σ_{j<N/2}`), summability of the profiles
`j ↦ profC (2j) σ` and `j ↦ profC (2j+1) σ` (from `profC_le_decay`), the bound
`errH σ ≤ e^{-2}` for `σ ≥ 1`, and the geometric bound
`Σ_{n odd, n < N} (n+3)(98/100)^{n-1} ≤ 11000`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.RI

noncomputable section

/-- The odd members of `range N` are `2j+1` for `j < N/2`. -/
theorem filter_odd_range_eq (N : ℕ) :
    (Finset.range N).filter (fun n : ℕ => Odd n)
      = (Finset.range (N / 2)).image (fun j => 2 * j + 1) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hn, hodd⟩
    obtain ⟨j, rfl⟩ := hodd
    refine ⟨j, ?_, by ring⟩
    rw [Nat.lt_div_iff_mul_lt (by norm_num : (0:ℕ) < 2)]
    omega
  · rintro ⟨j, hj, rfl⟩
    refine ⟨?_, ⟨j, rfl⟩⟩
    rw [Nat.lt_div_iff_mul_lt (by norm_num : (0:ℕ) < 2)] at hj
    omega

/-- The nonzero even members of `range N` are `2j` for `0 < j < (N+1)/2`. -/
theorem filter_even_range_eq (N : ℕ) :
    (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0)
      = ((Finset.range ((N + 1) / 2)).erase 0).image (fun j => 2 * j) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨hn, hev, hne⟩
    obtain ⟨j, rfl⟩ := hev
    have hj : j ≠ 0 := by rintro rfl; exact hne (by norm_num)
    refine ⟨j, ⟨hj, ?_⟩, by ring⟩
    rw [Nat.lt_div_iff_mul_lt (by norm_num : (0:ℕ) < 2)]
    omega
  · rintro ⟨j, ⟨hj, hjN⟩, rfl⟩
    refine ⟨?_, ⟨j, by ring⟩, by omega⟩
    rw [Nat.lt_div_iff_mul_lt (by norm_num : (0:ℕ) < 2)] at hjN
    omega

/-- `Σ_j (j+1) x^j = (1-x)^{-2}` for `‖x‖ < 1`. -/
theorem tsum_succ_mul_pow (x : ℝ) (hx : ‖x‖ < 1) :
    ∑' j : ℕ, ((j : ℝ) + 1) * x ^ j = (1 - x)⁻¹ ^ 2 := by
  have hS1 : Summable (fun j : ℕ => (j : ℝ) * x ^ j) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hS2 : Summable (fun j : ℕ => x ^ j) := summable_geometric_of_norm_lt_one hx
  have h := Summable.tsum_add hS1 hS2
  rw [tsum_coe_mul_geometric_of_norm_lt_one hx, tsum_geometric_of_norm_lt_one hx] at h
  rw [show (∑' j : ℕ, ((j : ℝ) + 1) * x ^ j) = ∑' j : ℕ, ((j : ℝ) * x ^ j + x ^ j) from
    tsum_congr (fun j => by ring), h]
  field_simp
  ring

/-- `profC (2j) σ` is summable for `σ ≥ 1` (dominated by the sharp decay). -/
theorem summable_profC_two_mul (s : ℝ) (hs : 1 ≤ s) :
    Summable (fun j : ℕ => Work.NumberTheory.Chen.APSwitchUpper.profC (2 * j) s) := by
  have hg : ‖(((97:ℝ)/100))^2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; norm_num
  refine Summable.of_nonneg_of_le (fun j => Work.NumberTheory.Chen.APSwitchUpper.profC_nonneg _ _)
    (fun j => ?_)
    (Summable.mul_left (20 * Work.NumberTheory.Chen.APSwitchUpper.errH s)
      (summable_geometric_of_norm_lt_one hg))
  have h := Work.NumberTheory.Chen.APSwitchUpper.profC_le_decay (2 * j) s hs
  calc Work.NumberTheory.Chen.APSwitchUpper.profC (2 * j) s
      ≤ 20 * ((97:ℝ)/100) ^ (2 * j) * Work.NumberTheory.Chen.APSwitchUpper.errH s := h
    _ = (20 * Work.NumberTheory.Chen.APSwitchUpper.errH s) * ((((97:ℝ)/100))^2) ^ j := by
        rw [← pow_mul]; ring

/-- `profC (2j+1) σ` is summable for `σ ≥ 1`. -/
theorem summable_profC_two_mul_add_one (s : ℝ) (hs : 1 ≤ s) :
    Summable (fun j : ℕ => Work.NumberTheory.Chen.APSwitchUpper.profC (2 * j + 1) s) := by
  have hg : ‖(((97:ℝ)/100))^2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; norm_num
  refine Summable.of_nonneg_of_le (fun j => Work.NumberTheory.Chen.APSwitchUpper.profC_nonneg _ _)
    (fun j => ?_)
    (Summable.mul_left (20 * ((97:ℝ)/100) * Work.NumberTheory.Chen.APSwitchUpper.errH s)
      (summable_geometric_of_norm_lt_one hg))
  have h := Work.NumberTheory.Chen.APSwitchUpper.profC_le_decay (2 * j + 1) s hs
  calc Work.NumberTheory.Chen.APSwitchUpper.profC (2 * j + 1) s
      ≤ 20 * ((97:ℝ)/100) ^ (2 * j + 1) * Work.NumberTheory.Chen.APSwitchUpper.errH s := h
    _ = (20 * ((97:ℝ)/100) * Work.NumberTheory.Chen.APSwitchUpper.errH s) * ((((97:ℝ)/100))^2) ^ j := by
        rw [pow_succ, ← pow_mul]; ring

/-- `errH σ ≤ e^{-2}` for `σ ≥ 1`. -/
theorem errH_le_exp_neg_two (s : ℝ) (hs : 1 ≤ s) :
    Work.NumberTheory.Chen.APSwitchUpper.errH s ≤ Real.exp (-2) := by
  by_cases h3 : s ≤ 3
  · by_cases h2 : s ≤ 2
    · rw [Work.NumberTheory.Chen.APSwitchUpper.errH_of_le_two h2]
    · rw [Work.NumberTheory.Chen.APSwitchUpper.errH_of_between (lt_of_not_ge h2) h3]
      exact Real.exp_le_exp.mpr (by linarith)
  · have h3' : 3 < s := lt_of_not_ge h3
    rw [Work.NumberTheory.Chen.APSwitchUpper.errH_of_three_lt h3',
      div_le_iff₀ (by linarith : (0:ℝ) < s)]
    have key : 3 * Real.exp (2 - s) < s := by
      have h1 : Real.exp (2 - s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      nlinarith [Real.exp_pos (2 - s)]
    have he : Real.exp (-2) * Real.exp (2 - s) = Real.exp (-s) := by
      rw [← Real.exp_add]; congr 1; ring
    calc 3 * Real.exp (-s) = Real.exp (-2) * (3 * Real.exp (2 - s)) := by
          rw [← he]; ring
      _ ≤ Real.exp (-2) * s :=
          mul_le_mul_of_nonneg_left (le_of_lt key) (Real.exp_pos _).le

/-- `Σ_{n odd < N} (n+3)(98/100)^{n-1} ≤ 11000`. -/
theorem sum_odd_geom_le (N : ℕ) :
    ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Odd n),
        ((n : ℝ) + 3) * ((98/100 : ℝ)) ^ (n - 1) ≤ 11000 := by
  rw [filter_odd_range_eq]
  rw [Finset.sum_image]
  swap
  · intro a _ b _ h
    have h' : 2 * a + 1 = 2 * b + 1 := h
    omega
  have hρ : ‖(((98:ℝ)/100))^2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; norm_num
  have htsum := tsum_succ_mul_pow ((((98:ℝ)/100))^2) hρ
  have hsumm : Summable (fun j : ℕ => ((j:ℝ)+1) * ((((98:ℝ)/100))^2)^j) := by
    have h := (hasSum_coe_mul_geometric_of_norm_lt_one hρ).summable.add
      (summable_geometric_of_norm_lt_one hρ)
    refine h.congr (fun j => ?_)
    ring
  calc ∑ j ∈ Finset.range (N / 2),
        ((↑(2 * j + 1) : ℝ) + 3) * ((98/100 : ℝ)) ^ (2 * j + 1 - 1)
      ≤ ∑ j ∈ Finset.range (N / 2), 4 * (((j:ℝ)+1) * ((((98:ℝ)/100))^2)^j) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have h1 : (2 * j + 1 - 1 : ℕ) = 2 * j := by omega
        have hpow : ((98/100 : ℝ)) ^ (2 * j) = (((98/100 : ℝ))^2) ^ j := by rw [pow_mul]
        rw [h1, hpow]
        have hpos : (0:ℝ) ≤ ((((98:ℝ)/100))^2)^j := by positivity
        have hc : ((↑(2 * j + 1) : ℝ) + 3) ≤ 4 * ((j:ℝ)+1) := by push_cast; linarith
        calc ((↑(2 * j + 1) : ℝ) + 3) * ((((98:ℝ)/100))^2)^j
            ≤ 4 * ((j:ℝ)+1) * ((((98:ℝ)/100))^2)^j :=
              mul_le_mul_of_nonneg_right hc hpos
          _ = 4 * (((j:ℝ)+1) * ((((98:ℝ)/100))^2)^j) := by ring
    _ = 4 * ∑ j ∈ Finset.range (N / 2), ((j:ℝ)+1) * ((((98:ℝ)/100))^2)^j := by
        rw [Finset.mul_sum]
    _ ≤ 4 * (1 - ((98:ℝ)/100)^2)⁻¹ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [← htsum]
        exact hsumm.sum_le_tsum _ (fun j _ => by positivity)
    _ ≤ 11000 := by norm_num


/-- `Σ_{n even, 0<n<N} (n+3)(98/100)^{n-1} ≤ 11000`. -/
theorem sum_even_geom_le (N : ℕ) :
    ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0),
        ((n : ℝ) + 3) * ((98/100 : ℝ)) ^ (n - 1) ≤ 11000 := by
  rw [filter_even_range_eq]
  rw [Finset.sum_image]
  swap
  · intro a _ b _ h
    have h' : 2 * a = 2 * b := h
    omega
  have hρ : ‖(((98:ℝ)/100))^2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; norm_num
  have htsum := tsum_succ_mul_pow ((((98:ℝ)/100))^2) hρ
  have hsumm : Summable (fun j : ℕ => ((j:ℝ)+1) * ((((98:ℝ)/100))^2)^j) := by
    have h := (hasSum_coe_mul_geometric_of_norm_lt_one hρ).summable.add
      (summable_geometric_of_norm_lt_one hρ)
    refine h.congr (fun j => ?_)
    ring
  calc ∑ j ∈ (Finset.range ((N + 1) / 2)).erase 0,
        ((↑(2 * j) : ℝ) + 3) * ((98/100 : ℝ)) ^ (2 * j - 1)
      ≤ ∑ j ∈ Finset.range ((N + 1) / 2),
        ((↑(2 * j) : ℝ) + 3) * ((98/100 : ℝ)) ^ (2 * j - 1) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
        intro j _ _
        positivity
    _ ≤ ∑ j ∈ Finset.range ((N + 1) / 2),
        5 * ((98/100 : ℝ))⁻¹ * (((j:ℝ)+1) * ((((98:ℝ)/100))^2)^j) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hle : ((98/100 : ℝ)) ^ (2 * j - 1) ≤
            ((98/100 : ℝ))⁻¹ * ((((98:ℝ)/100))^2)^j := by
          rcases Nat.eq_zero_or_pos j with hj | hj
          · subst hj; norm_num
          · have hρne : (98/100 : ℝ) ≠ 0 := by norm_num
            have hpow : ((98/100 : ℝ)) ^ (2 * j) = (((98/100 : ℝ))^2) ^ j := by rw [pow_mul]
            rw [pow_sub₀ ((98/100 : ℝ)) hρne (by omega : 1 ≤ 2*j), pow_one, hpow]
            exact le_of_eq (by ring)
        have hc : ((↑(2 * j) : ℝ) + 3) ≤ 5 * ((j:ℝ)+1) := by push_cast; linarith
        have hcpos : (0:ℝ) ≤ ((↑(2 * j) : ℝ) + 3) := by positivity
        have hρinv : (0:ℝ) ≤ ((98/100 : ℝ))⁻¹ := by norm_num
        have hpos : (0:ℝ) ≤ ((((98:ℝ)/100))^2)^j := by positivity
        calc ((↑(2 * j) : ℝ) + 3) * ((98/100 : ℝ)) ^ (2 * j - 1)
            ≤ ((↑(2 * j) : ℝ) + 3) * (((98/100 : ℝ))⁻¹ * ((((98:ℝ)/100))^2)^j) :=
              mul_le_mul_of_nonneg_left hle hcpos
          _ ≤ (5 * ((j:ℝ)+1)) * (((98/100 : ℝ))⁻¹ * ((((98:ℝ)/100))^2)^j) :=
              mul_le_mul_of_nonneg_right hc (mul_nonneg hρinv hpos)
          _ = 5 * ((98/100 : ℝ))⁻¹ * (((j:ℝ)+1) * ((((98:ℝ)/100))^2)^j) := by ring
    _ = 5 * ((98/100 : ℝ))⁻¹ *
        ∑ j ∈ Finset.range ((N + 1) / 2), ((j:ℝ)+1) * ((((98:ℝ)/100))^2)^j := by
        rw [Finset.mul_sum]
    _ ≤ 5 * ((98/100 : ℝ))⁻¹ * (1 - ((98:ℝ)/100)^2)⁻¹ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [← htsum]
        exact hsumm.sum_le_tsum _ (fun j _ => by positivity)
    _ ≤ 11000 := by norm_num


end
end Work.ChenPlan.LinearSieve.RI
