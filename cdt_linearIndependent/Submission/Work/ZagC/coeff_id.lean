import Mathlib

namespace Work.ZagC

theorem coeff_id (n j : ℕ) (hj : j ≤ n + 1) :
    (((n : ℚ) + 1) ^ 2 * ((n + 1).choose j : ℚ)
      - (10 * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 3) * (n.choose j : ℚ)
      + 9 * (n : ℚ) ^ 2 * ((n - 1).choose j : ℚ))
    = (j : ℚ) ^ 2 * (n.choose (j - 1) : ℚ)
      - (7 * (j : ℚ) ^ 2 + 7 * (j : ℚ) + 2) * (n.choose j : ℚ)
      - 8 * ((j : ℚ) + 1) ^ 2 * (n.choose (j + 1) : ℚ) := by
  rcases eq_or_lt_of_le hj with h | h
  · -- case j = n + 1
    subst h
    have e1 : (n+1).choose (n+1) = 1 := Nat.choose_self (n+1)
    have e2 : n.choose (n+1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)
    have e3 : (n-1).choose (n+1) = 0 := Nat.choose_eq_zero_of_lt (by omega : n - 1 < n + 1)
    have e4 : n.choose ((n + 1) - 1) = 1 := by rw [Nat.add_sub_cancel]; exact Nat.choose_self n
    have e5 : n.choose (n+1+1) = 0 := Nat.choose_eq_zero_of_lt (by omega : n < n+1+1)
    rw [e1, e2, e3, e4, e5]
    push_cast
    ring
  · -- case j ≤ n
    have hjn : j ≤ n := by omega
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · -- case j = 0
      subst hj0
      have e1 : (n + 1).choose 0 = 1 := Nat.choose_zero_right (n+1)
      have e2 : n.choose 0 = 1 := Nat.choose_zero_right n
      have e3 : (n - 1).choose 0 = 1 := Nat.choose_zero_right (n-1)
      have e5 : n.choose (0 + 1) = n := by rw [Nat.zero_add]; exact Nat.choose_one_right n
      rw [e1, e2, e3, e5]
      push_cast
      ring
    · -- case 1 ≤ j, j ≤ n
      have hjle : (j:ℚ) ≤ (n:ℚ) := by exact_mod_cast hjn
      have hnpos : (0:ℚ) < (n:ℚ) := by exact_mod_cast (by omega : 0 < n)
      -- binomial ratio relations in ℚ
      have hA : (((n:ℚ)+1) - (j:ℚ)) * ((n+1).choose j : ℚ) = ((n:ℚ)+1) * (n.choose j : ℚ) := by
        have h'' : ((n.choose j : ℕ) : ℚ) * ((n:ℚ)+1) =
            (((n+1).choose j : ℕ) : ℚ) * (((n+1)-j : ℕ) : ℚ) := by
          exact_mod_cast (Nat.choose_mul_succ_eq n j)
        have hc : (((n+1) - j : ℕ) : ℚ) = ((n:ℚ)+1) - (j:ℚ) := by
          rw [Nat.cast_sub (by omega : j ≤ n+1), Nat.cast_add, Nat.cast_one]
        rw [hc] at h''
        linarith [h'']
      have hB : (n:ℚ) * ((n-1).choose j : ℚ) = ((n:ℚ) - (j:ℚ)) * (n.choose j : ℚ) := by
        have h' : ((n-1).choose j : ℚ) * (n:ℚ) = (n.choose j : ℚ) * ((n - j : ℕ) : ℚ) := by
          have hh := Nat.choose_mul_succ_eq (n-1) j
          rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hh
          exact_mod_cast hh
        rw [Nat.cast_sub hjn] at h'
        linarith [h']
      have hC : (((n:ℚ) - (j:ℚ)) + 1) * (n.choose (j-1) : ℚ) = (j:ℚ) * (n.choose j : ℚ) := by
        have h' : (n.choose j : ℚ) * (j:ℚ) = (n.choose (j-1) : ℚ) * ((n - (j-1) : ℕ) : ℚ) := by
          have hh := Nat.choose_succ_right_eq n (j-1)
          rw [Nat.sub_add_cancel hjpos] at hh
          exact_mod_cast hh
        have hsub : n - (j-1) = n - j + 1 := by omega
        rw [hsub] at h'
        have hc : (((n - j + 1 : ℕ)) : ℚ) = (n:ℚ) - (j:ℚ) + 1 := by
          rw [Nat.cast_add, Nat.cast_sub hjn, Nat.cast_one]
        rw [hc] at h'
        linarith [h']
      have hD : ((j:ℚ)+1) * (n.choose (j+1) : ℚ) = ((n:ℚ) - (j:ℚ)) * (n.choose j : ℚ) := by
        have h' : (n.choose (j+1) : ℚ) * ((j:ℚ)+1) = (n.choose j : ℚ) * ((n - j : ℕ) : ℚ) := by
          exact_mod_cast (Nat.choose_succ_right_eq n j)
        rw [Nat.cast_sub hjn] at h'
        linarith [h']
      -- nonzero facts
      have hM : (n.choose j : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_ne_zero hjn)
      have h1 : ((n:ℚ)+1) - (j:ℚ) ≠ 0 := by
        have : (0:ℚ) < (n:ℚ)+1 - (j:ℚ) := by linarith
        exact ne_of_gt this
      have h2 : (n:ℚ) ≠ 0 := ne_of_gt hnpos
      have h3 : (n:ℚ) - (j:ℚ) + 1 ≠ 0 := by
        have : (0:ℚ) < (n:ℚ) - (j:ℚ) + 1 := by linarith
        exact ne_of_gt this
      have h4 : (j:ℚ) + 1 ≠ 0 := by positivity
      -- division forms
      have hAeq : ((n+1).choose j : ℚ) = (((n:ℚ)+1) * (n.choose j : ℚ)) / (((n:ℚ)+1) - (j:ℚ)) := by
        rw [eq_div_iff h1]; linarith [hA]
      have hBeq : ((n-1).choose j : ℚ) = (((n:ℚ) - (j:ℚ)) * (n.choose j : ℚ)) / (n:ℚ) := by
        rw [eq_div_iff h2]; linarith [hB]
      have hCeq : (n.choose (j-1) : ℚ) = ((j:ℚ) * (n.choose j : ℚ)) / (((n:ℚ)-(j:ℚ)) + 1) := by
        rw [eq_div_iff h3]; linarith [hC]
      have hDeq : (n.choose (j+1) : ℚ) = (((n:ℚ)-(j:ℚ)) * (n.choose j : ℚ)) / ((j:ℚ)+1) := by
        rw [eq_div_iff h4]; linarith [hD]
      rw [hAeq, hBeq, hCeq, hDeq]
      field_simp
      ring

end Work.ZagC
