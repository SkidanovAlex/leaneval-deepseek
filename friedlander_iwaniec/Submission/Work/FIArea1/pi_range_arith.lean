import Mathlib
import Submission.Work.FIArea1.L51Defs

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace Work.FIArea1

open Real

/-! ## Helper estimates for the final numerical comparison of *FI* (5.22) -/

/-- `|KR x| ≤ 3√x` for `x ≥ 1`. -/
private lemma KRCast (x : ℝ) (hx : 1 ≤ x) :
    ((KR x).natAbs : ℝ) ≤ 3 * Real.sqrt x := by
  have hK : ((KR x : ℤ) : ℝ) = ((⌈Real.sqrt (4 * x)⌉₊ : ℕ) : ℝ) := by
    simp [KR]
  rw [show ((KR x).natAbs : ℝ) = ((KR x : ℤ) : ℝ) by
        simp [KR], hK]
  have h1 : ((⌈Real.sqrt (4 * x)⌉₊ : ℕ) : ℝ) < Real.sqrt (4 * x) + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have h2 : Real.sqrt (4 * x) = 2 * Real.sqrt x := by
    rw [show (4:ℝ)*x = 2^2 * x by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h3 : 2 * Real.sqrt x + 1 ≤ 3 * Real.sqrt x := by
    have : (1:ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
    linarith
  linarith

/-- `√(Mq)·(N/q)^{3/2} = M^{1/2}N^{3/2}/q`. -/
private lemma sqrtMulRpowDiv (M q N : ℝ) (hM : 0 < M) (hq : 0 < q) (hN : 0 < N) :
    Real.sqrt (M*q) * (N/q)^((3:ℝ)/2) = M^((1:ℝ)/2) * N^((3:ℝ)/2) / q := by
  rw [Real.sqrt_eq_rpow (M*q), Real.mul_rpow hM.le hq.le, Real.div_rpow hN.le hq.le]
  have key : q ^ ((1:ℝ)/2) / q ^ ((3:ℝ)/2) = q⁻¹ := by
    rw [← Real.rpow_sub hq (1/2) ((3:ℝ)/2)]
    norm_num
    rw [Real.rpow_neg hq.le 1, Real.rpow_one]
  rw [show (M ^ ((1:ℝ)/2) * q ^ ((1:ℝ)/2) * (N ^ ((3:ℝ)/2) / q ^ ((3:ℝ)/2)))
      = M^((1:ℝ)/2) * N^((3:ℝ)/2) * (q^((1:ℝ)/2)/q^((3:ℝ)/2)) by ring, key]
  ring

/-- `16^{3/2} = 64`. -/
private lemma rpow16 : (16:ℝ)^((3:ℝ)/2) = 64 := by
  rw [show ((3:ℝ)/2) = (1/2)*3 by norm_num, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 16),
    show (16:ℝ)^((1:ℝ)/2) = 4 by rw [← Real.sqrt_eq_rpow]; norm_num]
  norm_num

/-- `√(Mq)·2^{3/2} ≤ 2^{3/2}·64·M^{1/2}N^{3/2}/q` for `q ≤ 16N`. -/
private lemma sqrtMulTwoRpow (M q N : ℝ) (hM : 0 < M) (hq : 0 < q) (hN : 0 < N)
    (hq16 : q ≤ 16*N) :
    Real.sqrt (M*q) * (2:ℝ)^((3:ℝ)/2)
      ≤ (2:ℝ)^((3:ℝ)/2) * 64 * (M^((1:ℝ)/2) * N^((3:ℝ)/2) / q) := by
  have hqq3 : q ^ ((3:ℝ)/2) ≤ 64 * N ^ ((3:ℝ)/2) := by
    have h1 : q ^ ((3:ℝ)/2) ≤ (16*N) ^ ((3:ℝ)/2) := Real.rpow_le_rpow hq.le hq16 (by norm_num)
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 16) hN.le, rpow16] at h1
    linarith [h1]
  have hqeq : q ^ ((3:ℝ)/2) = q ^ ((1:ℝ)/2) * q := by
    rw [show ((3:ℝ)/2) = (1:ℝ)/2 + 1 by norm_num, Real.rpow_add hq, Real.rpow_one]
  rw [hqeq] at hqq3
  have hqq : q ^ ((1:ℝ)/2) ≤ 64 * N ^ ((3:ℝ)/2) / q := (le_div_iff₀ hq).mpr hqq3
  rw [Real.sqrt_eq_rpow (M*q), Real.mul_rpow hM.le hq.le]
  calc M ^ ((1:ℝ)/2) * q ^ ((1:ℝ)/2) * (2:ℝ)^((3:ℝ)/2)
      ≤ M ^ ((1:ℝ)/2) * (64 * N ^ ((3:ℝ)/2) / q) * (2:ℝ)^((3:ℝ)/2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqq (Real.rpow_nonneg hM.le _))
          (Real.rpow_nonneg (by norm_num) _)
    _ = (2:ℝ)^((3:ℝ)/2) * 64 * (M^((1:ℝ)/2) * N^((3:ℝ)/2) / q) := by ring

/-- `(max a b)^{3/2} ≤ a^{3/2} + b^{3/2}` for `a,b ≥ 0`. -/
private lemma maxRpow (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (max a b)^((3:ℝ)/2) ≤ a^((3:ℝ)/2) + b^((3:ℝ)/2) := by
  rcases max_cases a b with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; exact le_add_of_nonneg_right (Real.rpow_nonneg hb _)
  · rw [h]; exact le_add_of_nonneg_left (Real.rpow_nonneg ha _)

/-- `1 ≤ log x` for `x ≥ 4`. -/
private lemma one_le_log_of_four_le (x : ℝ) (hx : 4 ≤ x) : 1 ≤ Real.log x := by
  have h0 : 0 < x := by linarith
  rw [Real.le_log_iff_exp_le h0]
  linarith [Real.exp_one_lt_d9]

/-- `log (2(A+B+2)) ≤ 4 log (x+2)` for `x ≥ 4`, `0 ≤ A ≤ 48x`, `0 ≤ B ≤ x`. -/
private lemma logTwoMul (x A B : ℝ) (hx4 : 4 ≤ x) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : A ≤ 48*x) (hB : B ≤ x) :
    Real.log (2*(A+B+2)) ≤ 4 * Real.log (x+2) := by
  have hx0 : 0 < x := by linarith
  have hstep : 2*(A+B+2) ≤ 100*(x+2) := by nlinarith
  have hpos : 0 < 2*(A+B+2) := by linarith
  have h1 : Real.log (2*(A+B+2)) ≤ Real.log (100*(x+2)) := Real.log_le_log hpos hstep
  rw [Real.log_mul (by norm_num : (100:ℝ) ≠ 0) (by linarith : x+2 ≠ 0)] at h1
  have h100 : Real.log 100 ≤ 3 * Real.log 6 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 100) (by norm_num : (100:ℝ) ≤ 6^3)
    rw [Real.log_pow] at h
    exact h
  have h6x : Real.log 6 ≤ Real.log (x+2) := Real.log_le_log (by norm_num) (by linarith)
  have : 3 * Real.log 6 ≤ 3 * Real.log (x+2) := by linarith
  linarith

/-- Final assembly of the two factors. -/
private lemma assemble (A B L T Q0 : ℝ)
    (hU : A * B^((3:ℝ)/2) ≤ 8192 * Q0)
    (hV : L^514 * T ≤ (4:ℝ)^514 * T^516)
    (hVnn : 0 ≤ L^514 * T) (hUnn : 0 ≤ 8192*Q0) :
    A * B^((3:ℝ)/2) * L^514 * T ≤ 8192 * (4:ℝ)^514 * Q0 * T^516 := by
  calc A * B^((3:ℝ)/2) * L^514 * T
      = (A * B^((3:ℝ)/2)) * (L^514 * T) := by rw [mul_assoc]
    _ ≤ (8192 * Q0) * ((4:ℝ)^514 * T^516) := mul_le_mul hU hV hVnn hUnn
    _ = 8192 * (4:ℝ)^514 * Q0 * T^516 := by ac_rfl

/-- **Final numerical comparison for the per-dyadic-range bound of *FI* (5.22).**

With `R' = KR (16Mq) = ⌈√(64Mq)⌉` and `X̃ = max (N/q) 2`, the quantity
`|R'| · X̃^{3/2} · log(2(|R'| + X̃ + 2))^{514} · log(MN+2)` produced by the two lattice counts and the
divisor bound is at most `C · M^{1/2}N^{3/2}q^{-1} · log(MN+2)^{516}`.

Route: `|R'| ≤ 9√(Mq)` for `Mq ≥ 1`; `X̃^{3/2} ≤ (N/q)^{3/2} + 2^{3/2}`, and
`√(Mq)·(N/q)^{3/2} = M^{1/2}N^{3/2}q^{-1}` while `√(Mq)·2^{3/2} ≤ 2^{3/2}·64·M^{1/2}N^{3/2}q^{-1}`
because `q ≤ 16N` gives `(q/N)^{3/2} ≤ 64`; finally `2(|R'| + X̃ + 2) ≤ C'(MN+2)`, so
`log(2(|R'|+X̃+2))^{514} ≤ C'^{514}log(MN+2)^{514}` and `log(MN+2) ≥ log 6 > 1`.  The constant `C`
is allowed to be astronomically large. -/
theorem pi_range_arith :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M N : ℝ), 1 ≤ q → 2 ≤ N → N ≤ M → q ≤ 16 * N →
      ((Work.FIArea1.KR (16 * M * q)).natAbs : ℝ)
        * (max (N / q) 2) ^ ((3 : ℝ) / 2)
        * (Real.log (2 * (((Work.FIArea1.KR (16 * M * q)).natAbs : ℝ) + max (N / q) 2 + 2)))
            ^ (514 : ℕ)
        * Real.log (M * N + 2)
      ≤ C * (M ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) / q)
          * (Real.log (M * N + 2)) ^ (516 : ℕ) := by
  refine ⟨8192 * (4:ℝ)^514, by positivity, ?_⟩
  intro q M N hq hN hNM hq16
  have hq0 : 0 < q := by linarith
  have hN0 : 0 < N := by linarith
  have hM0 : 0 < M := by linarith
  have hM2 : 2 ≤ M := by linarith
  have hMN4 : (4:ℝ) ≤ M*N := by nlinarith
  have hMq1 : (1:ℝ) ≤ 16*M*q := by nlinarith
  set A : ℝ := ((KR (16*M*q)).natAbs : ℝ) with hAdef
  set B : ℝ := max (N/q) 2 with hBdef
  set Q0 : ℝ := M^((1:ℝ)/2) * N^((3:ℝ)/2) / q with hQdef
  set T : ℝ := Real.log (M*N+2) with hTdef
  set L : ℝ := Real.log (2*(A+B+2)) with hLdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hQ0nn : 0 ≤ Q0 := by rw [hQdef]; positivity
  have hB2 : 2 ≤ B := by rw [hBdef]; exact le_max_right _ _
  have hBnn : 0 ≤ B := by linarith
  have hT1 : 1 ≤ T := by rw [hTdef]; exact one_le_log_of_four_le (M*N+2) (by linarith)
  have hT0 : 0 < T := by linarith
  have hA_le : A ≤ 12 * Real.sqrt (M*q) := by
    rw [hAdef]
    have h := KRCast (16*M*q) hMq1
    have hsqrt : Real.sqrt (16*M*q) = 4 * Real.sqrt (M*q) := by
      rw [show (16:ℝ)*M*q = 16*(M*q) by ring, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16),
        show Real.sqrt (16:ℝ) = 4 by norm_num]
    rw [hsqrt] at h
    linarith
  have hB_le : B^((3:ℝ)/2) ≤ (N/q)^((3:ℝ)/2) + (2:ℝ)^((3:ℝ)/2) := by
    rw [hBdef]
    rcases max_cases (N/q) 2 with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _)
    · rw [h]; exact le_add_of_nonneg_left
        (Real.rpow_nonneg (le_of_lt (div_pos hN0 hq0)) _)
  have hB32nn : 0 ≤ B^((3:ℝ)/2) := Real.rpow_nonneg hBnn _
  have hU2 : Real.sqrt (M*q) * B^((3:ℝ)/2) ≤ 512 * Q0 := by
    have h1 : Real.sqrt (M*q) * B^((3:ℝ)/2)
        ≤ Real.sqrt (M*q) * ((N/q)^((3:ℝ)/2) + (2:ℝ)^((3:ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hB_le (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (M*q) * ((N/q)^((3:ℝ)/2) + (2:ℝ)^((3:ℝ)/2))
        = Real.sqrt (M*q) * (N/q)^((3:ℝ)/2) + Real.sqrt (M*q) * (2:ℝ)^((3:ℝ)/2) := by ring
    rw [h2, sqrtMulRpowDiv M q N hM0 hq0 hN0, ← hQdef] at h1
    have h4 : Real.sqrt (M*q) * (2:ℝ)^((3:ℝ)/2) ≤ (2:ℝ)^((3:ℝ)/2) * 64 * Q0 := by
      rw [hQdef]; exact sqrtMulTwoRpow M q N hM0 hq0 hN0 hq16
    have h23 : (2:ℝ)^((3:ℝ)/2) ≤ 4 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : ((3:ℝ)/2) ≤ 2)
      have h4' : (2:ℝ)^(2:ℝ) = 4 := by norm_num
      linarith [h, h4']
    have h5 : Q0 + Real.sqrt (M*q)*(2:ℝ)^((3:ℝ)/2) ≤ Q0 + (2:ℝ)^((3:ℝ)/2)*64*Q0 := by
      linarith [h1, h4]
    have h6 : Q0 + (2:ℝ)^((3:ℝ)/2)*64*Q0 ≤ 512*Q0 := by nlinarith [h23, hQ0nn]
    linarith [h1, h5, h6]
  have hU : A * B^((3:ℝ)/2) ≤ 8192 * Q0 := by
    have h1 : A * B^((3:ℝ)/2) ≤ 12 * Real.sqrt (M*q) * B^((3:ℝ)/2) :=
      mul_le_mul_of_nonneg_right hA_le hB32nn
    have h2 : 12 * Real.sqrt (M*q) * B^((3:ℝ)/2) = 12 * (Real.sqrt (M*q) * B^((3:ℝ)/2)) := by ring
    rw [h2] at h1
    have h3 : 12 * (Real.sqrt (M*q) * B^((3:ℝ)/2)) ≤ 12 * (512 * Q0) :=
      mul_le_mul_of_nonneg_left hU2 (by norm_num)
    have h4 : (12:ℝ) * (512 * Q0) ≤ 8192 * Q0 := by nlinarith [hQ0nn]
    linarith
  have hA_le_MN : A ≤ 48*(M*N) := by
    have hmq : M*q ≤ 16*(M*N) := by
      nlinarith [mul_le_mul_of_nonneg_left hq16 (le_of_lt hM0)]
    have h3 : Real.sqrt (M*q) ≤ 4 * Real.sqrt (M*N) := by
      have h := Real.sqrt_le_sqrt hmq
      rwa [show Real.sqrt (16*(M*N)) = 4 * Real.sqrt (M*N) by
            rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16),
              show Real.sqrt (16:ℝ) = 4 by norm_num]] at h
    have h4 : Real.sqrt (M*N) ≤ M*N := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ M*N by positivity),
        Real.sqrt_nonneg (M*N), sq_nonneg (Real.sqrt (M*N)-1)]
    calc A ≤ 12 * Real.sqrt (M*q) := hA_le
      _ ≤ 12 * (4 * Real.sqrt (M*N)) := by linarith [h3]
      _ = 48 * Real.sqrt (M*N) := by ring
      _ ≤ 48 * (M*N) := by linarith [h4]
  have hB_le_MN : B ≤ M*N := by
    rw [hBdef]
    apply max_le
    · rw [div_le_iff₀ hq0]; nlinarith
    · nlinarith
  have hL_le : L ≤ 4*T := by
    rw [hLdef, hTdef]
    exact logTwoMul (M*N) A B hMN4 hA0 hBnn hA_le_MN hB_le_MN
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    apply Real.log_nonneg
    linarith
  have hV : L^514 * T ≤ (4:ℝ)^514 * T^516 := by
    have h1 : L^514 ≤ (4*T)^514 := pow_le_pow_left₀ hL0 hL_le 514
    rw [mul_pow] at h1
    have h2 : T^514 * T ≤ T^516 := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hT1 (by norm_num)
    have h4nn : (0:ℝ) ≤ (4:ℝ)^514 := by positivity
    calc L^514 * T ≤ ((4:ℝ)^514 * T^514) * T := mul_le_mul_of_nonneg_right h1 (le_of_lt hT0)
      _ = (4:ℝ)^514 * (T^514 * T) := by rw [mul_assoc]
      _ ≤ (4:ℝ)^514 * T^516 := mul_le_mul_of_nonneg_left h2 h4nn
  have hVnn : 0 ≤ L^514 * T := by positivity
  have hUnn : 0 ≤ 8192 * Q0 := by positivity
  refine assemble A B L T Q0 ?_ ?_ ?_ ?_
  · exact hU
  · exact hV
  · exact hVnn
  · exact hUnn

end Work.FIArea1
