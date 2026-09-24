import Mathlib

namespace Work.GM.S3

/-- The final numeric step of GM (7.1): if `N ≥ 1`, `T = N^{6/5}`, `0 < L ≤ T`, `δ(j-1) ≥ 28` and
`Kc ≤ N`, then any `X ≤ Kc·N³·T³·L⁵·T^{-δ(j-1)}` satisfies `X ≤ (N:ℝ)^{-20}`.
(Indeed `L⁵ ≤ T⁵`, so the bound is `≤ Kc·N³·T⁸·T^{-δ(j-1)} = Kc·N^{3+48/5-(6/5)δ(j-1)} ≤ Kc·N^{-21} ≤ N^{-20}`.) -/
theorem final_rpow_bound (N : ℕ) (Kc T L δ : ℝ) (j : ℕ) (X : ℝ)
    (hN : 1 ≤ N) (hKc : Kc ≤ (N : ℝ)) (hT : T = (N : ℝ) ^ (6 / 5 : ℝ)) (hLpos : 0 < L)
    (hLT : L ≤ T) (hjge : 28 ≤ δ * ((j : ℝ) - 1))
    (hX : X ≤ Kc * (N : ℝ) ^ 3 * T ^ 3 * L ^ 5 * T ^ (-(δ * ((j : ℝ) - 1)))) :
    X ≤ (N : ℝ) ^ (-20 : ℤ) := by
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  set n : ℝ := (N:ℝ) with hn
  set c : ℝ := δ * ((j:ℝ) - 1) with hc_def
  have hnpos : 0 < n := by rw [hn]; exact hNpos
  have hn1 : 1 ≤ n := by rw [hn]; exact hNR
  have hcge : 28 ≤ c := by rw [hc_def]; exact hjge
  have hTpos : 0 < T := by rw [hT]; exact Real.rpow_pos_of_pos hnpos _
  have hT1 : 1 ≤ T := by rw [hT]; exact Real.one_le_rpow hn1 (by norm_num)
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hL5 : L^5 ≤ T^5 := pow_le_pow_left₀ hLnn hLT 5
  -- `Kc * L^5 ≤ n * T^5`
  have h1 : Kc * L^5 ≤ n * T^5 := mul_le_mul hKc hL5 (pow_nonneg hLnn 5) hnpos.le
  have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ n^3 * T^3 * T^(-c))
  have hstep1 : Kc * n^3 * T^3 * L^5 * T^(-c) ≤ n * n^3 * T^3 * T^5 * T^(-c) := by
    calc Kc * n^3 * T^3 * L^5 * T^(-c)
        = (Kc * L^5) * (n^3 * T^3 * T^(-c)) := by ring
      _ ≤ (n * T^5) * (n^3 * T^3 * T^(-c)) := h2
      _ = n * n^3 * T^3 * T^5 * T^(-c) := by ring
  -- `T^(-c) ≤ T^(-28)`
  have hTc : T^(-c) ≤ T^(-28:ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have h3 := mul_le_mul_of_nonneg_right hTc (by positivity : (0:ℝ) ≤ n * n^3 * T^3 * T^5)
  have hstep2 : n * n^3 * T^3 * T^5 * T^(-c) ≤ n * n^3 * T^3 * T^5 * T^(-28:ℝ) := by
    calc n * n^3 * T^3 * T^5 * T^(-c) = T^(-c) * (n * n^3 * T^3 * T^5) := by ring
      _ ≤ T^(-28:ℝ) * (n * n^3 * T^3 * T^5) := h3
      _ = n * n^3 * T^3 * T^5 * T^(-28:ℝ) := by ring
  -- collapse the `T` powers
  have hcomb : n * n^3 * T^3 * T^5 * T^(-28:ℝ) = n^4 * T^(-20:ℤ) := by
    have hnn : n * n^3 = n^4 := by ring
    have hTT : T^3 * T^5 * T^(-28:ℝ) = T^(-20:ℤ) := by
      have e1 : T^3 * T^5 = T^8 := (pow_add T 3 5).symm
      rw [e1]
      have e3' : T^8 * T^(-28:ℝ) = T^(-20:ℝ) := by
        rw [← Real.rpow_natCast T 8, ← Real.rpow_add hTpos]
        push_cast
        norm_num
      rw [e3', ← Real.rpow_intCast T (-20)]
      push_cast
      ring
    calc n * n^3 * T^3 * T^5 * T^(-28:ℝ)
        = (n * n^3) * (T^3 * T^5 * T^(-28:ℝ)) := by ring
      _ = n^4 * T^(-20:ℤ) := by rw [hnn, hTT]
  -- `n^4 * T^(-20) = n^(-20)` using `T = n^(6/5)`
  have hfinal : n^4 * T^(-20:ℤ) = n^(-20:ℤ) := by
    have hT24 : T^(-20:ℤ) = n^(-24:ℝ) := by
      rw [← Real.rpow_intCast T (-20), hT, ← Real.rpow_mul hnpos.le]
      congr 1
      norm_num
    rw [hT24]
    have hkey : n^4 * n^(-24:ℝ) = n^(-20:ℝ) := by
      rw [← Real.rpow_natCast n 4, ← Real.rpow_add hnpos]
      congr 1
      push_cast
      norm_num
    rw [hkey, ← Real.rpow_intCast n (-20)]
    push_cast
    ring
  exact hX.trans (hstep1.trans (hstep2.trans (hcomb.trans hfinal).le))

end Work.GM.S3
