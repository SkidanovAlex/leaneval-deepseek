import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.H8

/-- If two sums of two powers of two agree, and each pair is sorted, then the pairs agree. -/
lemma two_pow_add_inj {p q r t : ℕ} (hpq : p ≤ q) (hrt : r ≤ t)
    (h : 2 ^ p + 2 ^ q = 2 ^ r + 2 ^ t) : p = r ∧ q = t := by
  -- Basic bounds: with `p ≤ q`, the sum `2^p + 2^q` lies in `[2^q, 2^(q+1)]`.
  have hq_up : 2 ^ p + 2 ^ q ≤ 2 ^ (q + 1) := by
    have hp : 2 ^ p ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hpq
    calc 2 ^ p + 2 ^ q ≤ 2 ^ q + 2 ^ q := by omega
      _ = 2 ^ (q + 1) := by rw [pow_succ]; ring
  have ht_up : 2 ^ r + 2 ^ t ≤ 2 ^ (t + 1) := by
    have hr : 2 ^ r ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hrt
    calc 2 ^ r + 2 ^ t ≤ 2 ^ t + 2 ^ t := by omega
      _ = 2 ^ (t + 1) := by rw [pow_succ]; ring
  -- Hence the larger exponents `q` and `t` differ by at most one.
  have ht_le : t ≤ q + 1 := by
    have h2 : 2 ^ t ≤ 2 ^ (q + 1) := by
      calc 2 ^ t ≤ 2 ^ r + 2 ^ t := Nat.le_add_left _ _
        _ = 2 ^ p + 2 ^ q := h.symm
        _ ≤ 2 ^ (q + 1) := hq_up
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have hq_le : q ≤ t + 1 := by
    have h2 : 2 ^ q ≤ 2 ^ (t + 1) := by
      calc 2 ^ q ≤ 2 ^ p + 2 ^ q := Nat.le_add_left _ _
        _ = 2 ^ r + 2 ^ t := h
        _ ≤ 2 ^ (t + 1) := ht_up
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  -- `q = t`: if `q < t` then `t = q + 1`, making the right side exceed `2^(q+1)`
  -- which bounds the left side; the case `t < q` is symmetric.
  have hqt : q = t := by
    rcases lt_trichotomy q t with hlt | heq | hgt
    · exfalso
      have ht_eq : t = q + 1 := by omega
      have hle : 2 ^ r + 2 ^ t ≤ 2 ^ (q + 1) := by rw [← h]; exact hq_up
      have hlt' : 2 ^ (q + 1) < 2 ^ r + 2 ^ t := by
        rw [ht_eq]
        exact Nat.lt_add_of_pos_left (pow_pos (by norm_num : (0:ℕ) < 2) r)
      exact absurd hle (not_le.mpr hlt')
    · exact heq
    · exfalso
      have hq_eq : q = t + 1 := by omega
      have hle : 2 ^ p + 2 ^ q ≤ 2 ^ (t + 1) := by rw [h]; exact ht_up
      have hlt' : 2 ^ (t + 1) < 2 ^ p + 2 ^ q := by
        rw [hq_eq]
        exact Nat.lt_add_of_pos_left (pow_pos (by norm_num : (0:ℕ) < 2) p)
      exact absurd hle (not_le.mpr hlt')
  -- With equal second exponents, `2^p = 2^r` and hence `p = r`.
  have hp_eq : 2 ^ p = 2 ^ r := by
    have h' := h
    rw [hqt] at h'
    exact Nat.add_right_cancel h'
  exact ⟨Nat.pow_right_injective (by norm_num : 2 ≤ 2) hp_eq, hqt⟩

end Work.Higman.H8
