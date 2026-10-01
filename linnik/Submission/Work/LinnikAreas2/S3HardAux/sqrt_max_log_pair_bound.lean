import Mathlib

set_option linter.unusedVariables false

namespace Work.LinnikAreas2.S3HardAux

/-- Auxiliary numeric fact: for `1 ≤ r ≤ z` and `r ≤ t`,
`1 ≤ 2 * (z / r) * t / z`. -/
private lemma np_pair_ge (z r t : ℕ) (hr : 1 ≤ r) (hrz : r ≤ z) (hrt : r ≤ t) :
    (1 : ℝ) ≤ 2 * ((z / r : ℕ) : ℝ) * (t : ℝ) / (z : ℝ) := by
  have hz0 : 0 < z := lt_of_lt_of_le Nat.zero_lt_one (le_trans hr hrz)
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz0
  have key : z + 1 ≤ 2 * (z / r) * t := by
    have hrpos : 0 < r := hr
    have hmod' : z % r + 1 ≤ r := Nat.succ_le_of_lt (Nat.mod_lt z hrpos)
    have hdiv : z = z / r * r + z % r := by
      have := Nat.div_add_mod z r; rw [mul_comm] at this; omega
    rcases lt_or_ge (z / r) 2 with hM | hM
    · have hM1 : z / r = 1 := by
        have h1 : 1 ≤ z / r := (Nat.le_div_iff_mul_le hrpos).mpr (by simpa using hrz)
        omega
      have hlt : z < 2 * r := (Nat.div_lt_iff_lt_mul hrpos).mp hM
      nlinarith [hM1, hlt, hrt]
    · have h2r : 2 * r ≤ z := (Nat.le_div_iff_mul_le hrpos).mp hM
      nlinarith [hmod', hdiv, h2r, hrt]
  have hcast : (z : ℝ) + 1 ≤ 2 * ((z / r : ℕ) : ℝ) * (t : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr key
    push_cast at h
    linarith
  rw [le_div_iff₀ hzpos]
  linarith

/-- Auxiliary numeric fact: for `1 ≤ r ≤ z`,
`|log (2 * (z / r) * r / z)| ≤ log 2`. -/
private lemma np_self_abs_log_le (z r : ℕ) (hr : 1 ≤ r) (hrz : r ≤ z) :
    |Real.log (2 * ((z / r : ℕ) : ℝ) * (r : ℝ) / (z : ℝ))| ≤ Real.log 2 := by
  have hz0 : 0 < z := lt_of_lt_of_le Nat.zero_lt_one (le_trans hr hrz)
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz0
  have hy1 : (1 : ℝ) ≤ 2 * ((z / r : ℕ) : ℝ) * (r : ℝ) / (z : ℝ) :=
    np_pair_ge z r r hr hrz le_rfl
  have hMr : (z / r) * r ≤ z := Nat.div_mul_le_self z r
  have hy2 : 2 * ((z / r : ℕ) : ℝ) * (r : ℝ) / (z : ℝ) ≤ 2 := by
    have h : ((z / r : ℕ) : ℝ) * (r : ℝ) ≤ (z : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hMr
      push_cast at this
      linarith
    rw [div_le_iff₀ hzpos]
    linarith
  rw [abs_of_nonneg (Real.log_nonneg hy1)]
  exact Real.log_le_log (lt_of_lt_of_le zero_lt_one hy1) hy2

/-- Auxiliary numeric fact: for `1 ≤ r ≤ z`,
`√r ≤ √z / √(z / r)`. -/
private lemma np_sqrt (z r : ℕ) (hr : 1 ≤ r) (hrz : r ≤ z) :
    Real.sqrt (r : ℝ) ≤ Real.sqrt (z : ℝ) / Real.sqrt (((z / r : ℕ) : ℝ)) := by
  have hrpos : 0 < r := hr
  have hMpos : (0 : ℝ) < ((z / r : ℕ) : ℝ) := by
    have : 0 < z / r := (Nat.le_div_iff_mul_le hrpos).mpr (by simpa using hrz)
    exact_mod_cast this
  have hMrR : ((z / r : ℕ) : ℝ) * (r : ℝ) ≤ (z : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr (Nat.div_mul_le_self z r)
    push_cast at this
    linarith
  have h1 : Real.sqrt (r : ℝ) * Real.sqrt (((z / r : ℕ) : ℝ)) ≤ Real.sqrt (z : ℝ) := by
    rw [mul_comm, ← Real.sqrt_mul (le_of_lt hMpos)]
    exact Real.sqrt_le_sqrt hMrR
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hMpos)]
  exact h1

/-- The `r ≤ t` case of the main inequality. -/
private lemma aux_le (z N q r t : ℕ) (hz : 2 ≤ z) (hNz : N < z * z)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hrT : r ≤ N / (q * z)) (ht : 1 ≤ t)
    (htT : t ≤ N / (q * z)) (hrt : r ≤ t) :
    Real.sqrt (((max (z / t) (z / r) : ℕ) : ℝ))
        * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
        * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|)
      ≤ 4 * Real.sqrt (z : ℝ)
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (r : ℝ)))
             + (1 / Real.sqrt (t : ℝ)) * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (t : ℝ)))) := by
  have hrpos : 0 < r := hr
  have hz0 : 0 < z := by omega
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz0
  have hqz0 : 0 < q * z := Nat.mul_pos (by omega) (by omega)
  have hA_lt_z : N / (q * z) < z := by
    rw [Nat.div_lt_iff_lt_mul hqz0]
    calc N < z * z := hNz
      _ ≤ z * (q * z) := Nat.mul_le_mul_left z (Nat.le_mul_of_pos_left z (by omega))
  have hrz : r ≤ z := le_trans hrT (le_of_lt hA_lt_z)
  have hmax : max (z / t) (z / r) = z / r := max_eq_right (Nat.div_le_div_left hrt hrpos)
  rw [hmax]
  set M : ℝ := ((z / r : ℕ) : ℝ) with hM
  set A : ℝ := ((N / (q * z) : ℕ) : ℝ) with hA
  set X : ℝ := 1 + |Real.log (2 * M * (t : ℝ) / (z : ℝ))| with hX
  set Y : ℝ := 1 + |Real.log (2 * M * (r : ℝ) / (z : ℝ))| with hY
  set P : ℝ := (1 / Real.sqrt (r : ℝ)) * (1 + Real.log (A / (r : ℝ))) with hP
  set Q : ℝ := (1 / Real.sqrt (t : ℝ)) * (1 + Real.log (A / (t : ℝ))) with hQ
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hrtR : (r : ℝ) ≤ (t : ℝ) := by exact_mod_cast hrt
  have hAr : (r : ℝ) ≤ A := by rw [hA]; exact_mod_cast hrT
  have hAt : (t : ℝ) ≤ A := by rw [hA]; exact_mod_cast htT
  have hAAr : (1 : ℝ) ≤ A / (r : ℝ) := by rw [le_div_iff₀ hrR]; linarith
  have hAAt : (1 : ℝ) ≤ A / (t : ℝ) := by rw [le_div_iff₀ htR]; linarith
  have hy1t : (1 : ℝ) ≤ 2 * M * (t : ℝ) / (z : ℝ) := by
    rw [hM]; exact np_pair_ge z r t hr hrz hrt
  have hy1r : (1 : ℝ) ≤ 2 * M * (r : ℝ) / (z : ℝ) := by
    rw [hM]; exact np_pair_ge z r r hr hrz le_rfl
  have hMrR : M * (r : ℝ) ≤ (z : ℝ) := by
    rw [hM]
    have := (Nat.cast_le (α := ℝ)).mpr (Nat.div_mul_le_self z r)
    push_cast at this
    linarith
  have hy2t : 2 * M * (t : ℝ) / (z : ℝ) ≤ 2 * (t : ℝ) / (r : ℝ) := by
    rw [div_le_div_iff₀ hzpos hrR]
    nlinarith [hMrR, htR]
  have hv : |Real.log (2 * M * (r : ℝ) / (z : ℝ))| ≤ Real.log 2 := by
    rw [hM]; exact np_self_abs_log_le z r hr hrz
  have hlog2le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hLnn : 0 ≤ Real.log ((t : ℝ) / (r : ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hrR]; linarith
  have hlog2tr : Real.log (2 * (t : ℝ) / (r : ℝ))
      = Real.log 2 + Real.log ((t : ℝ) / (r : ℝ)) := by
    rw [show 2 * (t : ℝ) / (r : ℝ) = 2 * ((t : ℝ) / (r : ℝ)) by ring,
        Real.log_mul (by norm_num) (ne_of_gt (div_pos htR hrR))]
  have hu : Real.log (2 * M * (t : ℝ) / (z : ℝ))
      ≤ Real.log 2 + Real.log ((t : ℝ) / (r : ℝ)) := by
    have hpos : 0 < 2 * M * (t : ℝ) / (z : ℝ) := lt_of_lt_of_le zero_lt_one hy1t
    have hle := Real.log_le_log hpos hy2t
    rwa [hlog2tr] at hle
  have hXt : X ≤ 1 + Real.log 2 + Real.log ((t : ℝ) / (r : ℝ)) := by
    have hnn : 0 ≤ Real.log (2 * M * (t : ℝ) / (z : ℝ)) := Real.log_nonneg hy1t
    rw [hX, abs_of_nonneg hnn]; linarith
  have hYr : Y ≤ 1 + Real.log 2 := by rw [hY]; linarith [hv]
  have hXY4 : X * Y ≤ 4 * (1 + Real.log ((t : ℝ) / (r : ℝ))) := by
    have h1 : X * Y ≤ (1 + Real.log 2 + Real.log ((t : ℝ) / (r : ℝ))) * (1 + Real.log 2) :=
      mul_le_mul hXt hYr (by positivity) (by linarith [hlog2nn, hLnn])
    nlinarith [h1, hlog2le1, hlog2nn, hLnn]
  have hlogA : Real.log ((t : ℝ) / (r : ℝ)) ≤ Real.log (A / (r : ℝ)) := by
    apply Real.log_le_log (div_pos htR hrR)
    rw [div_le_div_iff₀ hrR hrR]
    exact mul_le_mul_of_nonneg_right hAt (le_of_lt hrR)
  have hPnn : 0 ≤ P := by
    rw [hP]; exact mul_nonneg (by positivity) (by linarith [Real.log_nonneg hAAr])
  have hQnn : 0 ≤ Q := by
    rw [hQ]; exact mul_nonneg (by positivity) (by linarith [Real.log_nonneg hAAt])
  have hPQnn : 0 ≤ P + Q := add_nonneg hPnn hQnn
  have hsqr_ne : Real.sqrt (r : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hrR)
  have hsqr : Real.sqrt (r : ℝ) * (1 / Real.sqrt (r : ℝ)) = 1 := by
    rw [one_div, mul_inv_cancel₀ hsqr_ne]
  have hPQ1 : Real.sqrt (r : ℝ) * P = 1 + Real.log (A / (r : ℝ)) := by
    rw [hP, ← mul_assoc, hsqr, one_mul]
  have hQpos : 0 ≤ Real.sqrt (r : ℝ) * Q := by
    rw [hQ]; exact mul_nonneg (le_of_lt (Real.sqrt_pos.mpr hrR))
      (mul_nonneg (by positivity) (by linarith [Real.log_nonneg hAAt]))
  have hR1 : 4 * (1 + Real.log ((t : ℝ) / (r : ℝ))) ≤ 4 * (Real.sqrt (r : ℝ) * (P + Q)) := by
    have hsplit : Real.sqrt (r : ℝ) * (P + Q)
        = (1 + Real.log (A / (r : ℝ))) + Real.sqrt (r : ℝ) * Q := by
      rw [mul_add, hPQ1]
    have hle : 1 + Real.log ((t : ℝ) / (r : ℝ)) ≤ Real.sqrt (r : ℝ) * (P + Q) := by
      rw [hsplit]; linarith [hQpos, hlogA]
    linarith
  have hM1 : 1 ≤ z / r := (Nat.le_div_iff_mul_le hrpos).mpr (by simpa using hrz)
  have hMpos : (0 : ℝ) < M := by
    rw [hM]
    have : (1 : ℝ) ≤ ((z / r : ℕ) : ℝ) := by exact_mod_cast hM1
    linarith
  have hMposR : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have hsqMr : Real.sqrt M * Real.sqrt (r : ℝ) ≤ Real.sqrt (z : ℝ) := by
    have hs : Real.sqrt (r : ℝ) ≤ Real.sqrt (z : ℝ) / Real.sqrt M := by
      rw [hM]; exact np_sqrt z r hr hrz
    have h := mul_le_mul_of_nonneg_left hs (le_of_lt hMposR)
    rwa [mul_div_cancel₀ _ (ne_of_gt hMposR)] at h
  have hbound : X * Y ≤ 4 * (Real.sqrt (r : ℝ) * (P + Q)) := le_trans hXY4 hR1
  calc Real.sqrt M * X * Y
      = Real.sqrt M * (X * Y) := by ring
    _ ≤ Real.sqrt M * (4 * (Real.sqrt (r : ℝ) * (P + Q))) :=
        mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg M)
    _ = 4 * (Real.sqrt M * Real.sqrt (r : ℝ)) * (P + Q) := by ring
    _ ≤ 4 * Real.sqrt (z : ℝ) * (P + Q) := by
        have := mul_le_mul_of_nonneg_right hsqMr hPQnn
        linarith

theorem sqrt_max_log_pair_bound (z N q r t : ℕ)
    (hz : 2 ≤ z) (hzN : z ≤ N) (hNz : N < z * z) (hq : 1 ≤ q)
    (hr : 1 ≤ r) (hrT : r ≤ N / (q * z)) (ht : 1 ≤ t) (htT : t ≤ N / (q * z)) :
    Real.sqrt (((max (z / t) (z / r) : ℕ) : ℝ))
        * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
        * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|)
      ≤ 4 * Real.sqrt (z : ℝ)
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (r : ℝ)))
             + (1 / Real.sqrt (t : ℝ)) * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (t : ℝ)))) := by
  clear hzN
  rcases le_total r t with h | h
  · exact aux_le z N q r t hz hNz hq hr hrT ht htT h
  · have h' := aux_le z N q t r hz hNz hq ht htT hr hrT h
    rw [max_comm (z / r) (z / t)] at h'
    have e1 : (Real.sqrt (((max (z / t) (z / r) : ℕ) : ℝ))
          * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
          * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|))
        = (Real.sqrt (((max (z / t) (z / r) : ℕ) : ℝ))
          * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|)
          * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)) := by ring
    have e2 : (4 * Real.sqrt (z : ℝ)
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (r : ℝ)))
             + (1 / Real.sqrt (t : ℝ)) * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (t : ℝ)))))
        = (4 * Real.sqrt (z : ℝ)
          * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (t : ℝ)))
             + (1 / Real.sqrt (r : ℝ)) * (1 + Real.log (((N / (q * z) : ℕ) : ℝ) / (r : ℝ))))) := by ring
    rw [e1, e2]
    exact h'

end Work.LinnikAreas2.S3HardAux
