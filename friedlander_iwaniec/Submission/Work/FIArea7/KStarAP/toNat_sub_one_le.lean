import Mathlib

namespace Work.FIArea7.KStarAP

/-- Integer division by a positive divisor, cast to `ℝ`, is bounded by the real
division. -/
private lemma cast_ediv_le_div (a D : ℤ) (hD : 0 < D) :
    (((a / D : ℤ) : ℝ)) ≤ (a : ℝ) / (D : ℝ) := by
  have hDR : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  rw [le_div_iff₀ hDR]
  have h := Int.ediv_mul_le a (ne_of_gt hD)
  exact_mod_cast h

/-- `(Q + 1).toNat - 1`, read as a real number, is `max Q 0`. -/
private lemma toNat_sub_one_eq_max (Q : ℤ) :
    ((((Q + 1).toNat - 1 : ℕ) : ℝ)) = max (Q : ℝ) 0 := by
  rcases lt_or_ge Q 0 with hQ | hQ
  · have hneg : Q + 1 ≤ 0 := by omega
    have hzero : (Q + 1).toNat = 0 := Int.toNat_of_nonpos hneg
    have key : ((Q + 1).toNat - 1 : ℕ) = 0 := by rw [hzero]
    have hQle : (Q:ℝ) ≤ 0 := by exact_mod_cast (by omega : Q ≤ 0)
    rw [key, max_eq_right hQle]
    norm_num
  · have hnat : (Q + 1).toNat = Q.toNat + 1 := by
      rw [Int.toNat_add hQ (by norm_num : (0:ℤ) ≤ 1)]; norm_num
    have key : ((Q + 1).toNat - 1 : ℕ) = Q.toNat := by
      rw [hnat, Nat.add_sub_cancel]
    have hQnn : (0:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
    have hQcast : ((Q.toNat : ℕ) : ℝ) = (Q:ℝ) := by
      have := Int.toNat_of_nonneg hQ
      exact_mod_cast this
    rw [key, hQcast, max_eq_left hQnn]

/-- The general integer inequality: for `D > 0`,
`(((n - a) / D + 1 + a / D).toNat - 1 : ℕ)` is at most `n.toNat / D`. -/
private lemma toNat_add_one_ediv_le (D n a : ℤ) (hD : 0 < D) :
    ((((n - a) / D + 1 + a / D).toNat - 1 : ℕ) : ℝ) ≤ (n.toNat : ℝ) / (D : ℝ) := by
  have hAB : (n - a) / D + a / D ≤ n / D := by
    have h := Int.ediv_add_ediv_le_add_ediv (x := n - a) (y := a) (z := D) hD
    have hring : (n - a) + a = n := by ring
    rwa [hring] at h
  have hDR : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  have hcastAB : (((n - a) / D + a / D : ℤ) : ℝ) ≤ (n:ℝ)/(D:ℝ) := by
    have h1 : (((n - a) / D + a / D : ℤ) : ℝ) ≤ ((n / D : ℤ) : ℝ) := by exact_mod_cast hAB
    exact le_trans h1 (cast_ediv_le_div n D hD)
  have hQ1 : (n - a) / D + 1 + a / D = ((n - a) / D + a / D) + 1 := by ring
  rw [hQ1, toNat_sub_one_eq_max]
  rcases lt_or_ge n 0 with hn | hn
  · have hn0 : n.toNat = 0 := Int.toNat_of_nonpos (by omega)
    have hnR : (n:ℝ) ≤ 0 := by exact_mod_cast (by omega : n ≤ 0)
    rw [hn0]
    simp only [Nat.cast_zero, zero_div]
    have hnd : (n:ℝ)/(D:ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnR hDR.le
    exact max_le (le_trans hcastAB hnd) le_rfl
  · have hnt : (n.toNat : ℝ) = (n:ℝ) := by
      have := Int.toNat_of_nonneg hn; exact_mod_cast this
    rw [hnt]
    exact max_le hcastAB (div_nonneg (by exact_mod_cast hn : (0:ℝ) ≤ (n:ℝ)) hDR.le)

lemma toNat_sub_one_le (M c S T : ℤ) (hM : 1 ≤ M) :
    (((((T - c) / (4 * M)) + 1 + ((c - S) / (4 * M))).toNat - 1 : ℕ) : ℝ)
      ≤ ((T - S).toNat : ℝ) / (4 * (M : ℝ)) := by
  have hD : 0 < (4*M : ℤ) := by omega
  have h := toNat_add_one_ediv_le (4*M) (T-S) (c-S) hD
  have e1 : T - S - (c - S) = T - c := by ring
  have e2 : (((4*M : ℤ) : ℝ)) = 4 * (M : ℝ) := by push_cast; ring
  rw [e1, e2] at h
  exact h

end Work.FIArea7.KStarAP
