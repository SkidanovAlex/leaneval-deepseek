import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Conjugating involutions with an odd product

Let `s` and `t` be involutions of a group `G` such that `s * t` has odd order `n`.
Then `s` and `t` generate a dihedral group of order `2 * n` (a "generalized dihedral"
group), in which `s` and `t` are two of the reflections.  Concretely, with `r = s * t`
(the rotation of order `n`) we have `t = s * r`, and `s * r * s = r⁻¹`, so

* `u := s * r ^ j`, where `j = (n + 1) / 2`, is an involution (`2 * j = n + 1` gives
  `r ^ (2 * j) = r`) lying in `⟨s, t⟩`, and
* `u⁻¹ * s * u = t` (the reflection `s * r ^ j` is exactly the reflection that carries
  `s` to `t`).

This is the unique (up to the choice of the group generated) "reflection conjugation"
used when a strongly embedded subgroup meets two distinct even-order centralizers.
-/

namespace Work.DoubleTransitivity.Alg

theorem exists_involution_conjugating {G : Type} [Group G] {s t : G}
    (hs : orderOf s = 2) (ht : orderOf t = 2) (hodd : Odd (orderOf (s * t))) :
    ∃ u : G, orderOf u = 2 ∧ u⁻¹ * s * u = t ∧ u ∈ Subgroup.closure ({s, t} : Set G) := by
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs, pow_two] at h
    exact h
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set r : G := s * t with hr
  set n : ℕ := orderOf r with hn
  have hnodd : Odd n := by rw [hn, hr]; exact hodd
  set j : ℕ := (n + 1) / 2 with hj
  have h2j : 2 * j = n + 1 := by
    obtain ⟨k, hk⟩ := hnodd
    rw [hj, hk]
    have hkk : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
    rw [hkk, Nat.mul_div_right (k + 1) (by norm_num)]
  have hrn : r ^ n = 1 := by rw [hn]; exact pow_orderOf_eq_one r
  have hr2j : r ^ (2 * j) = r := by
    rw [h2j, pow_succ, hrn, one_mul]
  -- `s` conjugates the rotation `r = s * t` to its inverse
  have hrs : s * r * s⁻¹ = r⁻¹ := by
    rw [hr, hsinv, mul_inv_rev, hsinv, htinv]
    rw [← mul_assoc, hs2, one_mul]
  -- hence `s * r ^ j * s = (r ^ j)⁻¹`
  have hc : s * r^j * s = (r^j)⁻¹ := by
    have hconj : s * r^j * s⁻¹ = (r^j)⁻¹ := by
      rw [← conj_pow (a := s) (b := r) (i := j), hrs, inv_pow]
    rw [← hconj, hsinv]
  refine ⟨s * r^j, ?_, ?_, ?_⟩
  · -- `s * r ^ j` is an involution
    have hu2 : (s * r^j) ^ 2 = 1 := by
      rw [pow_two]
      calc (s * r^j) * (s * r^j) = (s * r^j * s) * r^j := by rw [← mul_assoc]
        _ = (r^j)⁻¹ * r^j := by rw [hc]
        _ = 1 := inv_mul_cancel _
    have hu_ne : s * r^j ≠ 1 := by
      intro h
      have hsj : s = (r^j)⁻¹ := eq_inv_of_mul_eq_one_left h
      have hord : orderOf (r^j) = 2 := by
        rw [← orderOf_inv (r^j), ← hsj]
        exact hs
      have hdvd : orderOf (r^j) ∣ n := by
        have := orderOf_pow_dvd (x := r) j
        rwa [← hn] at this
      have h2dvd : 2 ∣ n := by rw [← hord]; exact hdvd
      exact (fun hc2 => (Nat.not_even_iff_odd.mpr hnodd) (even_iff_two_dvd.mpr hc2)) h2dvd
    exact orderOf_eq_prime hu2 hu_ne
  · -- `s * r ^ j` conjugates `s` to `t`
    have h1 : (s * r^j)⁻¹ = (r^j)⁻¹ * s := by rw [mul_inv_rev, hsinv]
    rw [h1]
    have hBB : r^j * r^j = r := by
      rw [← pow_two, ← pow_mul, Nat.mul_comm j 2]
      exact hr2j
    calc ((r^j)⁻¹ * s) * s * (s * r^j)
        = (r^j)⁻¹ * s * (r^j) := by simp only [mul_assoc, hs2, one_mul]
      _ = (s * r^j * s) * s * (r^j) := by rw [← hc]
      _ = s * r^j * r^j := by simp only [mul_assoc, hs2, one_mul]
      _ = s * r := by rw [mul_assoc s (r^j) (r^j), hBB]
      _ = t := by rw [hr, ← mul_assoc, hs2, one_mul]
  · -- `s * r ^ j` lies in `⟨s, t⟩`
    have hs_mem : s ∈ Subgroup.closure ({s, t} : Set G) := Subgroup.subset_closure (by simp)
    have ht_mem : t ∈ Subgroup.closure ({s, t} : Set G) := Subgroup.subset_closure (by simp)
    have hr_mem : r ∈ Subgroup.closure ({s, t} : Set G) := by
      rw [hr]; exact mul_mem hs_mem ht_mem
    exact mul_mem hs_mem (pow_mem hr_mem j)

end Work.DoubleTransitivity.Alg
