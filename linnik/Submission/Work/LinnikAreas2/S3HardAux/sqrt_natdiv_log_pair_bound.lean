import Mathlib

namespace Work.LinnikAreas2.S3HardAux

/-- Auxiliary real-arithmetic assembly step. -/
lemma mul_three_le {a b c S L M : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hS : 0 ≤ S) (hL : 0 ≤ L) (_hM : 0 ≤ M) (h1 : a ≤ S) (h2 : b ≤ 4 * L) (h3 : c ≤ 4 * M) :
    a * b * c ≤ 16 * S * L * M := by
  have hbc : b * c ≤ 4 * L * (4 * M) := mul_le_mul h2 h3 hc (by linarith only [hL])
  calc a * b * c = a * (b * c) := by ring
    _ ≤ S * (4 * L * (4 * M)) := mul_le_mul h1 hbc (mul_nonneg hb hc) hS
    _ = 16 * S * L * M := by ring

/-- Monotonicity of `Real.sqrt` under natural-number division: the square root of a
floor-quotient is at most the quotient of the square roots. -/
lemma sqrt_natdiv_le_div (N q r t : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
      ≤ Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ) / Real.sqrt (r : ℝ) / Real.sqrt (t : ℝ) := by
  have hle : (((N / (q * r * t) : ℕ) : ℝ)) ≤ (N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)) := by
    have h := Nat.cast_div_le (α := ℝ) (m := N) (n := q * r * t)
    push_cast at h
    exact h
  have hsq : Real.sqrt ((q : ℝ) * (r : ℝ) * (t : ℝ))
      = Real.sqrt (q : ℝ) * Real.sqrt (r : ℝ) * Real.sqrt (t : ℝ) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  calc Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
      ≤ Real.sqrt ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (N : ℝ) / Real.sqrt ((q : ℝ) * (r : ℝ) * (t : ℝ)) := by
        rw [Real.sqrt_div' (N : ℝ) (y := (q : ℝ) * (r : ℝ) * (t : ℝ)) (by positivity)]
    _ = Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ) / Real.sqrt (r : ℝ) / Real.sqrt (t : ℝ) := by
        rw [hsq, div_div, div_div, mul_assoc]

/-- The logarithmic factor bound: the extra `log`-factor coming from a nice
divisor pair is controlled by `4 (1 + log (A / v))` where `A = ⌊N/(qz)⌋`. -/
lemma log_factor_bound (z N q u v : ℕ)
    (hz : 2 ≤ z) (_hzN : z ≤ N) (hNz : N < z * z) (hq : 1 ≤ q)
    (hu : 1 ≤ u) (huT : u ≤ N / (q * z)) (hv : 1 ≤ v) (hvT : v ≤ N / (q * z)) :
    1 + |Real.log (2 * (((N / (q * u * v) : ℕ) : ℝ)) * (u : ℝ) / (z : ℝ))|
      ≤ 4 * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (v : ℝ))) := by
  have hqz : 0 < q * z := by positivity
  have hquv : 0 < q * u * v := by positivity
  have hA1 : 1 ≤ N / (q * z) := le_trans hu huT
  -- `v ≤ z`
  have hvz : v ≤ z := by
    by_contra hcon
    push_neg at hcon
    have h2 : v * (q * z) ≤ N := (Nat.le_div_iff_mul_le hqz).mp hvT
    have h3 : v * (q * z) < z * z := lt_of_le_of_lt h2 hNz
    have h4 : (v * q) * z < z * z := by
      rwa [show v * (q * z) = (v * q) * z by ring] at h3
    have h5 : v * q < z := lt_of_mul_lt_mul_right h4 (Nat.zero_le z)
    have h6 : v ≤ v * q := by
      calc v = v * 1 := (mul_one v).symm
        _ ≤ v * q := Nat.mul_le_mul_left v hq
    omega
  have hquvN : q * u * v ≤ N := by
    have h1 : u * (q * z) ≤ N := (Nat.le_div_iff_mul_le hqz).mp huT
    have h2 : q * u * v ≤ q * u * z := Nat.mul_le_mul_left (q * u) hvz
    have h3 : q * u * z = u * (q * z) := by ring
    omega
  have hvqzN : v * (q * z) ≤ N := (Nat.le_div_iff_mul_le hqz).mp hvT
  have hB1 : 1 ≤ N / (q * u * v) := (Nat.one_le_div_iff hquv).mpr hquvN
  have hfloorB : N < (N / (q * u * v) + 1) * (q * u * v) :=
    (Nat.div_lt_iff_lt_mul hquv).mp (Nat.lt_succ_self _)
  have hN2 : N ≤ 2 * (N / (q * u * v)) * (q * u * v) := by
    have hle : (N / (q * u * v) + 1) * (q * u * v)
        ≤ 2 * (N / (q * u * v)) * (q * u * v) :=
      Nat.mul_le_mul_right (q * u * v) (by omega)
    omega
  have hfloorA : N < (N / (q * z) + 1) * (q * z) :=
    (Nat.div_lt_iff_lt_mul hqz).mp (Nat.lt_succ_self _)
  have hNA : N ≤ 2 * (N / (q * z)) * (q * z) := by
    have hle : (N / (q * z) + 1) * (q * z) ≤ 2 * (N / (q * z)) * (q * z) :=
      Nat.mul_le_mul_right (q * z) (by omega)
    omega
  have hBquvN : N / (q * u * v) * (q * u * v) ≤ N := by
    have h := Nat.mul_div_le N (q * u * v)
    simpa [mul_comm] using h
  -- pass to the reals
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (by omega : 0 < v)
  have hqvR : (0 : ℝ) < (q : ℝ) * (v : ℝ) := mul_pos hqR hvR
  have hN2R : (N : ℝ) ≤ 2 * (((N / (q * u * v) : ℕ) : ℝ)) * (u : ℝ) * ((q : ℝ) * (v : ℝ)) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hN2
    push_cast at h
    linarith only [h]
  have hvqzR : (z : ℝ) * ((q : ℝ) * (v : ℝ)) ≤ (N : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hvqzN
    push_cast at h
    linarith only [h]
  have hx1 : 1 ≤ 2 * (((N / (q * u * v) : ℕ) : ℝ)) * (u : ℝ) / (z : ℝ) := by
    rw [le_div_iff₀ hzR]
    simp only [one_mul]
    by_contra hcon
    push_neg at hcon
    have h1 : 2 * (((N / (q * u * v) : ℕ) : ℝ)) * (u : ℝ) * ((q : ℝ) * (v : ℝ))
        < (z : ℝ) * ((q : ℝ) * (v : ℝ)) := mul_lt_mul_of_pos_right hcon hqvR
    linarith only [hN2R, hvqzR, h1]
  have hx2 : 2 * (((N / (q * u * v) : ℕ) : ℝ)) * (u : ℝ) / (z : ℝ)
      ≤ 4 * (((N / (q * z) : ℕ) : ℝ)) / (v : ℝ) := by
    rw [div_le_div_iff₀ hzR hvR]
    have hfloorAR : (N : ℝ) < (((N / (q * z) : ℕ) : ℝ) + 1) * ((q : ℝ) * (z : ℝ)) := by
      have h := (Nat.cast_lt (α := ℝ)).mpr hfloorA
      push_cast at h
      linarith only [h]
    have h2N : (2 : ℝ) * (((N / (q * u * v) : ℕ) : ℝ)) * ((q : ℝ) * (u : ℝ) * (v : ℝ))
        ≤ 2 * (N : ℝ) := by
      have h := (Nat.cast_le (α := ℝ)).mpr (Nat.mul_le_mul_left 2 hBquvN)
      push_cast at h
      linarith only [h]
    have hAz2 : 2 * ((((N / (q * z) : ℕ) : ℝ)) + 1) * ((q : ℝ) * (z : ℝ))
        ≤ 4 * (((N / (q * z) : ℕ) : ℝ)) * ((q : ℝ) * (z : ℝ)) := by
      have hA1R : (1 : ℝ) ≤ (((N / (q * z) : ℕ) : ℝ)) := by exact_mod_cast hA1
      have h' : (2 : ℝ) * ((((N / (q * z) : ℕ) : ℝ)) + 1) ≤ 4 * (((N / (q * z) : ℕ) : ℝ)) := by
        linarith only [hA1R]
      exact mul_le_mul_of_nonneg_right h' (by positivity)
    have hcross : 2 * (((N / (q * u * v) : ℕ) : ℝ)) * (u : ℝ) * (v : ℝ) * (q : ℝ)
        ≤ 4 * (((N / (q * z) : ℕ) : ℝ)) * (z : ℝ) * (q : ℝ) := by linarith only [hfloorAR, h2N, hAz2]
    exact le_of_mul_le_mul_right hcross hqR
  -- the log chain
  have hxpos : 0 < 2 * (((N / (q * u * v) : ℕ) : ℝ)) * (u : ℝ) / (z : ℝ) :=
    lt_of_lt_of_le zero_lt_one hx1
  have hAR : (0 : ℝ) < ((N / (q * z) : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < N / (q * z))
  have habs : |Real.log (2 * (((N / (q * u * v) : ℕ) : ℝ)) * (u : ℝ) / (z : ℝ))|
      = Real.log (2 * (((N / (q * u * v) : ℕ) : ℝ)) * (u : ℝ) / (z : ℝ)) :=
    abs_of_nonneg (Real.log_nonneg hx1)
  have hAv : (1 : ℝ) ≤ ((N / (q * z) : ℕ) : ℝ) / (v : ℝ) := by
    rw [le_div_iff₀ hvR]
    simp only [one_mul]
    exact_mod_cast hvT
  have hlogAv : 0 ≤ Real.log (((N / (q * z) : ℕ) : ℝ) / (v : ℝ)) := Real.log_nonneg hAv
  have hlog4le : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith only [h]
  have hlog' : Real.log (2 * (((N / (q * u * v) : ℕ) : ℝ)) * (u : ℝ) / (z : ℝ))
      ≤ Real.log 4 + Real.log (((N / (q * z) : ℕ) : ℝ) / (v : ℝ)) := by
    have h := Real.log_le_log hxpos hx2
    rw [show (4 : ℝ) * (((N / (q * z) : ℕ) : ℝ)) / (v : ℝ)
        = 4 * ((((N / (q * z) : ℕ) : ℝ)) / (v : ℝ)) by ring] at h
    rwa [Real.log_mul (by norm_num) (by positivity)] at h
  rw [habs]
  linarith only [hlogAv, hlog4le, hlog']

/-- Bound for the product of the two square-root/log factors attached to a pair
`r, t` of divisors of `N`, in terms of `√N/√q` and the two `log (A/r)`, `log (A/t)`
factors. -/
theorem sqrt_natdiv_log_pair_bound (z N q r t : ℕ)
    (hz : 2 ≤ z) (hzN : z ≤ N) (hNz : N < z * z) (hq : 1 ≤ q)
    (hr : 1 ≤ r) (hrT : r ≤ N / (q * z)) (ht : 1 ≤ t) (htT : t ≤ N / (q * z)) :
    Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
        * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
        * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|)
      ≤ 16 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ))
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (r : ℝ))))
          * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (t : ℝ)))) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hsq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqR
  have hsr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrR
  have hst : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htR
  have hSnn : 0 ≤ Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ) / Real.sqrt (r : ℝ) / Real.sqrt (t : ℝ) :=
    div_nonneg (div_nonneg (div_nonneg (Real.sqrt_nonneg (N : ℝ)) (le_of_lt hsq)) (le_of_lt hsr))
      (le_of_lt hst)
  have hsqrt : Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
      ≤ Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ) / Real.sqrt (r : ℝ) / Real.sqrt (t : ℝ) :=
    sqrt_natdiv_le_div N q r t hq hr ht
  have hlog1 : 1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|
      ≤ 4 * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (r : ℝ))) := by
    have h := log_factor_bound z N q t r hz hzN hNz hq ht htT hr hrT
    simpa only [show q * t * r = q * r * t by ring] using h
  have hlog2 : 1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|
      ≤ 4 * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (t : ℝ))) :=
    log_factor_bound z N q r t hz hzN hNz hq hr hrT ht htT
  have hAr : (1 : ℝ) ≤ ((N / (q * z) : ℕ) : ℝ) / (r : ℝ) := by
    rw [le_div_iff₀ hrR]
    simp only [one_mul]
    exact_mod_cast hrT
  have hAt : (1 : ℝ) ≤ ((N / (q * z) : ℕ) : ℝ) / (t : ℝ) := by
    rw [le_div_iff₀ htR]
    simp only [one_mul]
    exact_mod_cast htT
  have hL1 : 0 ≤ 1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (r : ℝ)) := by
    have h := Real.log_nonneg hAr
    linarith only [h]
  have hL2 : 0 ≤ 1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (t : ℝ)) := by
    have h := Real.log_nonneg hAt
    linarith only [h]
  have hF1 : 0 ≤ 1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))| := by
    have h := abs_nonneg (Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ)))
    linarith only [h]
  have hF2 : 0 ≤ 1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))| := by
    have h := abs_nonneg (Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ)))
    linarith only [h]
  have hsqrtnn : 0 ≤ Real.sqrt (((N / (q * r * t) : ℕ) : ℝ)) := Real.sqrt_nonneg _
  have key : Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
        * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
        * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|)
      ≤ 16 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ) / Real.sqrt (r : ℝ) / Real.sqrt (t : ℝ))
          * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (r : ℝ)))
          * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (t : ℝ))) :=
    mul_three_le hsqrtnn hF1 hF2 hSnn hL1 hL2 hsqrt hlog1 hlog2
  calc Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
        * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
        * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|)
      ≤ 16 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ) / Real.sqrt (r : ℝ) / Real.sqrt (t : ℝ))
          * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (r : ℝ)))
          * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (t : ℝ))) := key
    _ = 16 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ))
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (r : ℝ))))
          * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (t : ℝ)))) := by
        ring

end Work.LinnikAreas2.S3HardAux
