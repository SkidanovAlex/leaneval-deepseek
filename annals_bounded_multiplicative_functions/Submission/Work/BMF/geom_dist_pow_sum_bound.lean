import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset

/-- Any finite sum of distinct powers `ρ ^ i` (`i ∈ ℕ`) is bounded by the full
geometric series `(1 - ρ)⁻¹`, for `0 ≤ ρ < 1`. -/
private lemma geom_finset_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (I : Finset ℕ) :
    (∑ i ∈ I, ρ ^ i) ≤ (1 - ρ)⁻¹ := by
  have hsumm : Summable (fun n : ℕ => ρ ^ n) := summable_geometric_of_lt_one hρ0 hρ1
  have htsum : ∑' n : ℕ, ρ ^ n = (1 - ρ)⁻¹ := tsum_geometric_of_lt_one hρ0 hρ1
  rw [← htsum]
  exact hsumm.sum_le_tsum I (fun i _ => pow_nonneg hρ0 i)

/-- For a fixed `j`, the weights `ρ ^ (Nat.dist j k)` over a finite set `S ⊆ ℕ`
are bounded by twice the geometric series: the points on the left of `j` and
those on the right contribute at most `(1 - ρ)⁻¹` each. -/
theorem geom_dist_pow_sum_bound (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (j : ℕ) (S : Finset ℕ) :
    (∑ k ∈ S, ρ ^ (Nat.dist j k)) ≤ 2 * (1 - ρ)⁻¹ := by
  -- the part of `S` on the left of `j`: `k ≤ j`, contributions `ρ ^ (j - k)`,
  -- reindexed by `k ↦ j - k` (injective there) into a set of exponents.
  have hleft : (∑ k ∈ S.filter (fun k => k ≤ j), ρ ^ (Nat.dist j k)) ≤ (1 - ρ)⁻¹ := by
    have hcongr : (∑ k ∈ S.filter (fun k => k ≤ j), ρ ^ (Nat.dist j k))
        = (∑ k ∈ S.filter (fun k => k ≤ j), ρ ^ (j - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [Nat.dist_eq_sub_of_le_right hk.2]
    rw [hcongr]
    have hinj : Set.InjOn (fun k => j - k) ↑(S.filter (fun k => k ≤ j)) := by
      intro a ha b hb hab
      change j - a = j - b at hab
      simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
      have h1 : j - (j - a) = a := Nat.sub_sub_self ha.2
      have h2 : j - (j - b) = b := Nat.sub_sub_self hb.2
      rw [← h1, hab, h2]
    rw [← Finset.sum_image (f := fun i => ρ ^ i) hinj]
    exact geom_finset_le ρ hρ0 hρ1 _
  -- the part of `S` on the right of `j`: `j < k`, contributions `ρ ^ (k - j)`,
  -- reindexed by `k ↦ k - j` (injective there) into a set of exponents.
  have hright : (∑ k ∈ S.filter (fun k => ¬ k ≤ j), ρ ^ (Nat.dist j k)) ≤ (1 - ρ)⁻¹ := by
    have hcongr : (∑ k ∈ S.filter (fun k => ¬ k ≤ j), ρ ^ (Nat.dist j k))
        = (∑ k ∈ S.filter (fun k => ¬ k ≤ j), ρ ^ (k - j)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [Nat.dist_eq_sub_of_le (le_of_lt (Nat.lt_of_not_le hk.2))]
    rw [hcongr]
    have hinj : Set.InjOn (fun k => k - j) ↑(S.filter (fun k => ¬ k ≤ j)) := by
      intro a ha b hb hab
      change a - j = b - j at hab
      simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
      have h1 : a - j + j = a := Nat.sub_add_cancel (le_of_lt (Nat.lt_of_not_le ha.2))
      have h2 : b - j + j = b := Nat.sub_add_cancel (le_of_lt (Nat.lt_of_not_le hb.2))
      rw [← h1, hab, h2]
    rw [← Finset.sum_image (f := fun i => ρ ^ i) hinj]
    exact geom_finset_le ρ hρ0 hρ1 _
  -- split `S` into the left and right parts and add the two bounds.
  rw [← Finset.sum_filter_add_sum_filter_not S (fun k => k ≤ j) (fun k => ρ ^ (Nat.dist j k))]
  calc (∑ k ∈ S.filter (fun k => k ≤ j), ρ ^ (Nat.dist j k))
        + (∑ k ∈ S.filter (fun k => ¬ k ≤ j), ρ ^ (Nat.dist j k))
      ≤ (1 - ρ)⁻¹ + (1 - ρ)⁻¹ := add_le_add hleft hright
    _ = 2 * (1 - ρ)⁻¹ := by ring

end Work.BMF
