import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecificLimits.Basic

namespace Commons.Analysis.ExponentialSums

open scoped BigOperators

/-- The numerical core of Bourgain (1989), (3.14): for every `a > 0`,
`∑_{k≥0} min(a·2^{-k}, (a·2^{-k})⁻¹)² ≤ 8/3`.  This is the pointwise `ℓ²`-bound on the dyadic
scales of a symbol with `|K̂(u)| ≤ c·min(|u|,|u|⁻¹)`. -/
theorem tsum_min_inv_sq_le (a : ℝ) (ha : 0 < a) :
    (∑' k : ℕ, (min (a / (2:ℝ)^k) (a / (2:ℝ)^k)⁻¹) ^ 2) ≤ 8 / 3 := by
  let F : ℕ → ℝ := fun k => (min (a / (2:ℝ)^k) (a / (2:ℝ)^k)⁻¹) ^ 2
  change (∑' k : ℕ, F k) ≤ 8 / 3
  have hpow2pos : ∀ k : ℕ, (0:ℝ) < (2:ℝ)^k := fun k => pow_pos (by norm_num) k
  have hx_pos : ∀ k : ℕ, (0:ℝ) < a / (2:ℝ)^k := fun k => div_pos ha (hpow2pos k)
  have hF_nonneg : ∀ k, 0 ≤ F k := fun k => sq_nonneg _
  have h2k_sq : ∀ k : ℕ, ((2:ℝ)^k)^2 = (4:ℝ)^k := by
    intro k
    rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul, ← pow_mul]
    ring_nf
  -- `S`-bound: `F k ≤ a^2 / 4^k`
  have hS : ∀ k, F k ≤ a^2 / (4:ℝ)^k := by
    intro k
    have hx := hx_pos k
    have hmin_nonneg : 0 ≤ min (a / (2:ℝ)^k) (a / (2:ℝ)^k)⁻¹ :=
      le_min hx.le (inv_pos.mpr hx).le
    have h1 : (min (a / (2:ℝ)^k) (a / (2:ℝ)^k)⁻¹)^2 ≤ (a / (2:ℝ)^k)^2 :=
      pow_le_pow_left₀ hmin_nonneg (min_le_left _ _) 2
    have h2 : (a / (2:ℝ)^k)^2 = a^2 / (4:ℝ)^k := by
      rw [div_pow, h2k_sq]
    rw [h2] at h1; exact h1
  -- `R`-bound: `F k ≤ 4^k / a^2`
  have hR : ∀ k, F k ≤ (4:ℝ)^k / a^2 := by
    intro k
    have hx := hx_pos k
    have hmin_nonneg : 0 ≤ min (a / (2:ℝ)^k) (a / (2:ℝ)^k)⁻¹ :=
      le_min hx.le (inv_pos.mpr hx).le
    have h1 : (min (a / (2:ℝ)^k) (a / (2:ℝ)^k)⁻¹)^2 ≤ ((a / (2:ℝ)^k)⁻¹)^2 :=
      pow_le_pow_left₀ hmin_nonneg (min_le_right _ _) 2
    have h2 : ((a / (2:ℝ)^k)⁻¹)^2 = (4:ℝ)^k / a^2 := by
      rw [inv_div, div_pow, h2k_sq]
    rw [h2] at h1; exact h1
  have hSummS : Summable (fun k : ℕ => a^2 / (4:ℝ)^k) := by
    have hgeo : Summable (fun k : ℕ => ((4:ℝ)⁻¹) ^ k) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have h := hgeo.mul_left (a^2)
    simpa only [div_eq_mul_inv, inv_pow] using h
  have hFsumm : Summable F := Summable.of_nonneg_of_le hF_nonneg hS hSummS
  have hvalS : (∑' k : ℕ, a^2 / (4:ℝ)^k) = a^2 * (4/3) := by
    have h1 : ∀ k : ℕ, a^2 / (4:ℝ)^k = a^2 * ((4:ℝ)⁻¹)^k := by
      intro k; rw [div_eq_mul_inv, inv_pow]
    rw [tsum_congr h1, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num : (4:ℝ)⁻¹ < 1)]
    norm_num
  rcases le_or_gt 1 a with ha1 | ha1
  · -- main case `1 ≤ a`
    have hex : ∃ k : ℕ, a < (2:ℝ)^(k+1) := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt a (by norm_num : (1:ℝ) < 2)
      exact ⟨n, lt_of_lt_of_le hn (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_succ n))⟩
    set m := Nat.find hex with hmdef
    have hm_spec : a < (2:ℝ)^(m+1) := Nat.find_spec hex
    have hm_le : (2:ℝ)^m ≤ a := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [hm0]; simpa using ha1
      · by_contra hcon
        rw [not_le] at hcon
        have hsucc : m - 1 + 1 = m := Nat.sub_add_cancel (by omega : 1 ≤ m)
        have hP : a < (2:ℝ)^((m-1)+1) := by rw [hsucc]; exact hcon
        have hle := Nat.find_min' hex hP
        rw [← hmdef] at hle
        omega
    have ha2pos : (0:ℝ) < a^2 := pow_pos ha 2
    have key := hFsumm.sum_add_tsum_nat_add (m+1)
    have h4m : (4:ℝ)^m ≤ a^2 := by
      rw [← h2k_sq m]
      exact pow_le_pow_left₀ (le_of_lt (hpow2pos m)) hm_le 2
    have hA : ∑ i ∈ Finset.range (m+1), F i ≤ 4/3 := by
      have h1 : ∑ i ∈ Finset.range (m+1), F i ≤ ∑ i ∈ Finset.range (m+1), (4:ℝ)^i / a^2 :=
        Finset.sum_le_sum (fun i _ => hR i)
      have hgeom : ∑ i ∈ Finset.range (m+1), (4:ℝ)^i = ((4:ℝ)^(m+1) - 1) / 3 := by
        rw [geom_sum_eq (by norm_num : (4:ℝ) ≠ 1)]; norm_num
      have hbound : (4:ℝ)^(m+1) ≤ 4 * a^2 := by
        rw [pow_succ]; nlinarith [h4m]
      have h2 : ∑ i ∈ Finset.range (m+1), (4:ℝ)^i / a^2 ≤ 4/3 := by
        rw [← Finset.sum_div, hgeom, div_div]
        have hnum : (4:ℝ)^(m+1) - 1 ≤ 4 * a^2 := by linarith [hbound]
        calc ((4:ℝ)^(m+1) - 1) / (3 * a^2) ≤ (4 * a^2) / (3 * a^2) :=
              div_le_div_of_nonneg_right hnum (by positivity)
          _ = 4/3 := by rw [mul_div_mul_right 4 3 (c := a^2) ha2pos.ne']
      linarith
    have hB : ∑' i : ℕ, F (i + (m+1)) ≤ 4/3 := by
      have htail_summ : Summable (fun i : ℕ => F (i + (m+1))) :=
        (summable_nat_add_iff (m+1)).mpr hFsumm
      have hc : ∀ i : ℕ,
          a^2 / (4:ℝ)^(i + (m+1)) = (a^2 / (4:ℝ)^(m+1)) * ((4:ℝ)⁻¹)^i := by
        intro i
        rw [pow_add, inv_pow]
        field_simp
      have hmaj : Summable (fun i : ℕ => a^2 / (4:ℝ)^(i + (m+1))) := by
        have hgeo : Summable (fun i : ℕ => ((4:ℝ)⁻¹)^i) :=
          summable_geometric_of_lt_one (by norm_num) (by norm_num)
        have h := hgeo.mul_left (a^2 / (4:ℝ)^(m+1))
        simpa only [hc] using h
      have hval : (∑' i : ℕ, a^2 / (4:ℝ)^(i + (m+1))) = (a^2 / (4:ℝ)^(m+1)) * (4/3) := by
        rw [tsum_congr hc, tsum_mul_left,
          tsum_geometric_of_lt_one (by norm_num) (by norm_num : (4:ℝ)⁻¹ < 1)]
        norm_num
      have hb := Summable.tsum_le_tsum (fun i => hS (i + (m+1))) htail_summ hmaj
      rw [hval] at hb
      have ha2_le : a^2 ≤ (4:ℝ)^(m+1) := by
        have h := pow_le_pow_left₀ (le_of_lt ha) hm_spec.le 2
        rwa [h2k_sq (m+1)] at h
      have h1 : a^2 / (4:ℝ)^(m+1) ≤ 1 :=
        (div_le_one (pow_pos (by norm_num) (m+1))).mpr ha2_le
      nlinarith [hb, h1]
    rw [← key]
    linarith [hA, hB]
  · -- case `a < 1`
    have h1 : (∑' k : ℕ, F k) ≤ ∑' k : ℕ, a^2 / (4:ℝ)^k :=
      Summable.tsum_le_tsum hS hFsumm hSummS
    rw [hvalS] at h1
    have ha2le : a^2 ≤ 1 := by nlinarith [mul_pos ha (sub_pos.mpr ha1)]
    linarith

end Commons.Analysis.ExponentialSums