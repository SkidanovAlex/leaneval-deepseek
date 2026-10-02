import Submission.Work.ConeSwitch.MathlibNoHG

namespace Work.Deep.Kahn

/-!
# A Lovász-local-lemma-type numerical bound

For `1 ≤ C ≤ D` and `D ≥ 2^80`,

`exp 1 * exp (-(D^(1/4))) * (10^6 * C^10 * D^10 + 1) ≤ 1`.

This is the numerical estimate used to apply the Lovász Local Lemma in Kahn's
asymptotic edge-colouring argument: it says that the "bad event" probability
`exp(-D^(1/4))` beats the polynomial number `10^6 * C^10 * D^10 + 1` of events
each bad event depends on.

The proof is a chain of elementary estimates.  Writing `y = D^(1/4)` and
`u = D^(1/16)`:

* `D ≥ 2^80` gives `u ≥ 2^5`, hence `y = u^4 ≥ 2^20` and `640*u ≤ y`;
* `log (2 * 10^6 * D^20) = log 2 + 6 * log 10 + 20 * log D ≤ 55 + 20 * log D`,
  using `log t ≤ t - 1` on `2` and `10`;
* `log D = 16 * log u ≤ 16*u` (again `log t ≤ t - 1`), so `20 * log D ≤ 320*u`;
* `10^6 * C^10 * D^10 + 1 ≤ 2 * 10^6 * D^20` because `C ≤ D` and `D ≥ 1`.

Since `320*u + 56 ≤ y` (from `640*u ≤ y` and `112 ≤ y`), the logarithm of the
left-hand side is `1 - y + log(10^6*C^10*D^10+1) ≤ 1 - y + 55 + 320*u ≤ 0`,
and the conclusion follows from `Real.log_le_iff_le_exp`. -/

theorem lllPolyBound {C D : ℕ} (hC : 1 ≤ C) (hCD : C ≤ D) (hD : (2:ℝ)^80 ≤ (D:ℝ)) :
    Real.exp 1 * Real.exp (-(D:ℝ)^((1:ℝ)/4)) * (((10^6 * C^10 * D^10 : ℕ) : ℝ) + 1) ≤ 1 := by
  have h1D : 1 ≤ D := le_trans hC hCD
  have hx1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast h1D
  have hxpos : (0:ℝ) < (D:ℝ) := lt_of_lt_of_le (by norm_num) hx1
  set y : ℝ := (D:ℝ) ^ ((1:ℝ)/4) with hydef
  set u : ℝ := (D:ℝ) ^ ((1:ℝ)/16) with hudef
  -- `u ≥ 32 = 2^5`
  have hu5 : (32:ℝ) ≤ u := by
    have hD' : (2:ℝ)^((80:ℝ)) ≤ (D:ℝ) := by simpa using hD
    have hmono : ((2:ℝ)^((80:ℝ)))^((1:ℝ)/16) ≤ (D:ℝ)^((1:ℝ)/16) :=
      Real.rpow_le_rpow (by positivity) hD' (by norm_num)
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      show ((80:ℝ) * ((1:ℝ)/16)) = 5 by norm_num] at hmono
    have h32 : ((2:ℝ)^((5:ℝ))) = 32 := by norm_num
    rw [h32] at hmono
    rw [hudef]
    exact hmono
  have hupos : (0:ℝ) < u := lt_of_lt_of_le (by norm_num) hu5
  have hu0 : (0:ℝ) ≤ u := le_of_lt hupos
  -- `y = u^4`
  have hyu : y = u^4 := by
    rw [hydef, hudef]
    rw [← Real.rpow_natCast ((D:ℝ)^((1:ℝ)/16)) 4, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (D:ℝ))]
    norm_num
  -- `32768 * u ≤ y`
  have hu3 : (32768:ℝ) ≤ u^3 := by
    have h : (32:ℝ)^3 ≤ u^3 := pow_le_pow_left₀ (by norm_num) hu5 3
    norm_num at h
    exact h
  have h32768 : (32768:ℝ) * u ≤ y := by
    calc (32768:ℝ) * u ≤ u^3 * u := mul_le_mul hu3 le_rfl hu0 (by positivity)
      _ = u^4 := by ring
      _ = y := hyu.symm
  have h640 : (640:ℝ) * u ≤ y := by
    have h : (640:ℝ) * u ≤ (32768:ℝ) * u := mul_le_mul_of_nonneg_right (by norm_num) hu0
    linarith
  -- `y ≥ 2^20`
  have hybig : (1048576:ℝ) ≤ y := by
    have h : (32768:ℝ) * 32 ≤ (32768:ℝ) * u := mul_le_mul_of_nonneg_left hu5 (by norm_num)
    norm_num at h
    linarith
  have hy112 : (112:ℝ) ≤ y := le_trans (by norm_num) hybig
  -- logarithmic bounds
  have hlogu : Real.log u = ((1:ℝ)/16) * Real.log (D:ℝ) := by
    rw [hudef]; exact Real.log_rpow hxpos _
  have hlogD : Real.log (D:ℝ) ≤ 16 * u := by
    have h1 : Real.log (D:ℝ) = 16 * Real.log u := by rw [hlogu]; ring
    rw [h1]
    have h2 : Real.log u ≤ u := by
      have := Real.log_le_sub_one_of_pos hupos
      linarith
    exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  have h20logD : 20 * Real.log (D:ℝ) ≤ 320 * u := by
    have h := mul_le_mul_of_nonneg_left hlogD (by norm_num : (0:ℝ) ≤ 20)
    linarith
  -- the polynomial number of events
  have hCDR : (C:ℝ) ≤ (D:ℝ) := by exact_mod_cast hCD
  have hC10 : (C:ℝ)^10 ≤ (D:ℝ)^10 := pow_le_pow_left₀ (by positivity) hCDR 10
  have h1 : (C:ℝ)^10 * (D:ℝ)^10 ≤ (D:ℝ)^10 * (D:ℝ)^10 :=
    mul_le_mul hC10 le_rfl (by positivity) (by positivity)
  have h2 : (D:ℝ)^10 * (D:ℝ)^10 = (D:ℝ)^20 := by ring
  have h3 : ((10:ℝ)^6) * ((C:ℝ)^10 * (D:ℝ)^10) ≤ ((10:ℝ)^6) * ((D:ℝ)^10 * (D:ℝ)^10) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hN : ((10^6 * C^10 * D^10 : ℕ) : ℝ) ≤ ((10:ℝ)^6) * (D:ℝ)^20 := by
    push_cast
    rw [← h2]
    linarith [h3]
  have hx20 : (1:ℝ) ≤ (D:ℝ)^20 := one_le_pow₀ hx1
  have hB : (1:ℝ) ≤ ((10:ℝ)^6) * (D:ℝ)^20 := by
    have h106 : (1:ℝ) ≤ (10:ℝ)^6 := by norm_num
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ ((10:ℝ)^6) * (D:ℝ)^20 := mul_le_mul h106 hx20 (by norm_num) (by positivity)
  have hK : (((10^6 * C^10 * D^10 : ℕ) : ℝ) + 1) ≤ (2:ℝ) * ((10:ℝ)^6) * (D:ℝ)^20 := by
    linarith [hN, hB]
  have hKpos : (0:ℝ) < (((10^6 * C^10 * D^10 : ℕ) : ℝ) + 1) := by positivity
  have hlogK : Real.log (((10^6 * C^10 * D^10 : ℕ) : ℝ) + 1) ≤ 55 + 20 * Real.log (D:ℝ) := by
    have hlogeq : Real.log ((2:ℝ) * ((10:ℝ)^6) * (D:ℝ)^20)
        = Real.log 2 + 6 * Real.log 10 + 20 * Real.log (D:ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow, Real.log_pow]
      push_cast
      ring
    have hstep := Real.log_le_log hKpos hK
    rw [hlogeq] at hstep
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    have hl10 : Real.log 10 ≤ 9 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 10)
      linarith
    linarith
  -- take logarithms
  have hmain : Real.log (Real.exp 1 * Real.exp (-y) * (((10^6 * C^10 * D^10 : ℕ) : ℝ) + 1)) ≤ 0 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_exp]
    linarith [hlogK, h20logD, h640, hy112]
  have hLHSpos : (0:ℝ) < Real.exp 1 * Real.exp (-y) * (((10^6 * C^10 * D^10 : ℕ) : ℝ) + 1) := by
    positivity
  have := (Real.log_le_iff_le_exp hLHSpos).mp hmain
  simpa using this

end Work.Deep.Kahn
