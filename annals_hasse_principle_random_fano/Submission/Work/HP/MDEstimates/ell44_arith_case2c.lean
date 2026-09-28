import Mathlib

namespace Work.HP.MDEstimates

/-- `(a*b*c)^r = a^r * b^r * c^r` for nonnegative `a,b,c`. -/
private lemma case2c_rpow_three_mul (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (r : ℝ) :
    (a * b * c) ^ r = a ^ r * b ^ r * c ^ r := by
  rw [Real.mul_rpow (mul_nonneg ha hb) hc, Real.mul_rpow ha hb]

/-- `(x^n)^r = x^(n*r)` for `x ≥ 0`. -/
private lemma case2c_rpow_pow_nat (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (r : ℝ) :
    (x ^ n) ^ r = x ^ (n * r) := by
  rw [← Real.rpow_natCast x n]
  exact (Real.rpow_mul hx (n:ℝ) r).symm

theorem ell44_arith_case2c :
    ∀ Z Δ M : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ M → 1000 * M^53 < Δ → 1000^2 * M^106 * Δ < Z^3 →
      M ^ 70 * (Z ^ 4 * Δ ^ ((11:ℝ)/3) + Z ^ 4 * Δ ^ ((7:ℝ)/2) + Z ^ 6 * Δ ^ ((3:ℝ)/2))
        + M ^ 40 * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2)
      ≤ 1000 * Z ^ ((9:ℝ)/2) * Δ^2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * M^53 := by
  intro Z Δ M hZ hΔ hM h1 h2
  -- Pass all natural-number powers appearing in the goal to real (rpow) exponents.
  simp only [← Real.rpow_natCast]
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hΔ0 : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hZnn : 0 ≤ Z := le_of_lt hZ0
  have hΔnn : 0 ≤ Δ := le_of_lt hΔ0
  have hMnn : 0 ≤ M := le_of_lt hM0
  -- Key consequence of the second hypothesis: `10 * M^(53/3) * Δ^(1/6) < Z^(1/2)`.
  have key : 10 * M ^ ((53:ℝ)/3) * Δ ^ ((1:ℝ)/6) < Z ^ ((1:ℝ)/2) := by
    have hLnn : 0 ≤ (1000:ℝ)^2 * M^106 * Δ := by positivity
    have hlt := Real.rpow_lt_rpow hLnn h2 (by norm_num : (0:ℝ) < 1/6)
    rw [case2c_rpow_three_mul ((1000:ℝ)^2) (M^106) Δ (by positivity) (by positivity) hΔnn (1/6),
        case2c_rpow_pow_nat (1000:ℝ) (by norm_num) 2 (1/6),
        case2c_rpow_pow_nat M hMnn 106 (1/6),
        case2c_rpow_pow_nat Z hZnn 3 (1/6)] at hlt
    norm_num at hlt
    exact hlt
  have hΔadd : Δ ^ ((1:ℝ)/6) * Δ ^ ((7:ℝ)/2) = Δ ^ ((11:ℝ)/3) := by
    rw [← Real.rpow_add hΔ0]; norm_num
  have hZadd : Z ^ ((1:ℝ)/2) * Z ^ ((4:ℕ):ℝ) = Z ^ ((9:ℝ)/2) := by
    rw [← Real.rpow_add hZ0]; norm_num
  have hMadd : M ^ ((53:ℕ):ℝ) * M ^ ((17:ℕ):ℝ) = M ^ ((70:ℕ):ℝ) := by
    rw [← Real.rpow_add hM0]; norm_num
  have hM17le : M ^ ((17:ℕ):ℝ) ≤ M ^ ((53:ℝ)/3) := by
    apply Real.rpow_le_rpow_of_exponent_le hM; norm_num
  -- Bound for the term `M^70 * Z^4 * Δ^(11/3)`.
  have hstep1 : 10 * M ^ ((17:ℕ):ℝ) * Δ ^ ((1:ℝ)/6) < Z ^ ((1:ℝ)/2) := by
    have hle : 10 * M ^ ((17:ℕ):ℝ) * Δ ^ ((1:ℝ)/6) ≤ 10 * M ^ ((53:ℝ)/3) * Δ ^ ((1:ℝ)/6) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hM17le (by norm_num)
    exact lt_of_le_of_lt hle key
  have b1 : M ^ ((70:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((11:ℝ)/3)
      ≤ (1:ℝ)/10 * (M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2)) := by
    have b1core : M ^ ((17:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((11:ℝ)/3)
        ≤ (1:ℝ)/10 * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) := by
      have hcpos : 0 < (1:ℝ)/10 * Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2) := by positivity
      have h2' := mul_lt_mul_of_pos_right hstep1 hcpos
      have eL : (10 * M ^ ((17:ℕ):ℝ) * Δ ^ ((1:ℝ)/6)) * ((1:ℝ)/10 * Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2))
          = M ^ ((17:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((11:ℝ)/3) := by
        calc _ = M ^ ((17:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * (Δ ^ ((1:ℝ)/6) * Δ ^ ((7:ℝ)/2)) := by ring
          _ = M ^ ((17:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((11:ℝ)/3) := by rw [hΔadd]
      have eR : Z ^ ((1:ℝ)/2) * ((1:ℝ)/10 * Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2))
          = (1:ℝ)/10 * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) := by
        calc _ = (1:ℝ)/10 * (Z ^ ((1:ℝ)/2) * Z ^ ((4:ℕ):ℝ)) * Δ ^ ((7:ℝ)/2) := by ring
          _ = (1:ℝ)/10 * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) := by rw [hZadd]
      rw [eL, eR] at h2'
      exact le_of_lt h2'
    have step3 := mul_le_mul_of_nonneg_left b1core (by positivity : (0:ℝ) ≤ M ^ ((53:ℕ):ℝ))
    have e3 : M ^ ((53:ℕ):ℝ) * (M ^ ((17:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((11:ℝ)/3))
        = M ^ ((70:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((11:ℝ)/3) := by
      calc _ = (M ^ ((53:ℕ):ℝ) * M ^ ((17:ℕ):ℝ)) * (Z ^ ((4:ℕ):ℝ) * Δ ^ ((11:ℝ)/3)) := by ring
        _ = M ^ ((70:ℕ):ℝ) * (Z ^ ((4:ℕ):ℝ) * Δ ^ ((11:ℝ)/3)) := by rw [hMadd]
        _ = M ^ ((70:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((11:ℝ)/3) := by ring
    have e4 : M ^ ((53:ℕ):ℝ) * ((1:ℝ)/10 * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2))
        = (1:ℝ)/10 * (M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2)) := by ring
    rw [e3, e4] at step3
    exact step3
  -- Bound for the term `M^70 * Z^4 * Δ^(7/2)`.
  have hstep2 : 10 * M ^ ((17:ℕ):ℝ) < Z ^ ((1:ℝ)/2) := by
    have hΔ16ge1 : 1 ≤ Δ ^ ((1:ℝ)/6) := Real.one_le_rpow hΔ (by norm_num)
    have h1' : 10 * M ^ ((17:ℕ):ℝ) ≤ 10 * M ^ ((53:ℝ)/3) := mul_le_mul_of_nonneg_left hM17le (by norm_num)
    have h2' : 10 * M ^ ((53:ℝ)/3) ≤ 10 * M ^ ((53:ℝ)/3) * Δ ^ ((1:ℝ)/6) := by
      calc 10 * M ^ ((53:ℝ)/3) = 10 * M ^ ((53:ℝ)/3) * 1 := by ring
        _ ≤ 10 * M ^ ((53:ℝ)/3) * Δ ^ ((1:ℝ)/6) := mul_le_mul_of_nonneg_left hΔ16ge1 (by positivity)
    exact lt_of_le_of_lt (le_trans h1' h2') key
  have b2 : M ^ ((70:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2)
      ≤ (1:ℝ)/10 * (M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2)) := by
    have b2core : M ^ ((17:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2)
        ≤ (1:ℝ)/10 * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) := by
      have hcpos : 0 < (1:ℝ)/10 * Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2) := by positivity
      have h2'' := mul_lt_mul_of_pos_right hstep2 hcpos
      have eL : (10 * M ^ ((17:ℕ):ℝ)) * ((1:ℝ)/10 * Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2))
          = M ^ ((17:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2) := by ring
      have eR : Z ^ ((1:ℝ)/2) * ((1:ℝ)/10 * Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2))
          = (1:ℝ)/10 * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) := by
        calc _ = (1:ℝ)/10 * (Z ^ ((1:ℝ)/2) * Z ^ ((4:ℕ):ℝ)) * Δ ^ ((7:ℝ)/2) := by ring
          _ = (1:ℝ)/10 * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) := by rw [hZadd]
      rw [eL, eR] at h2''
      exact le_of_lt h2''
    have step3 := mul_le_mul_of_nonneg_left b2core (by positivity : (0:ℝ) ≤ M ^ ((53:ℕ):ℝ))
    have e3 : M ^ ((53:ℕ):ℝ) * (M ^ ((17:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2))
        = M ^ ((70:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2) := by
      calc _ = (M ^ ((53:ℕ):ℝ) * M ^ ((17:ℕ):ℝ)) * (Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2)) := by ring
        _ = M ^ ((70:ℕ):ℝ) * (Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2)) := by rw [hMadd]
        _ = M ^ ((70:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2) := by ring
    have e4 : M ^ ((53:ℕ):ℝ) * ((1:ℝ)/10 * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2))
        = (1:ℝ)/10 * (M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2)) := by ring
    rw [e3, e4] at step3
    exact step3
  -- From the first hypothesis: `M^53 < Δ`, hence `M^17 ≤ Δ^(1/2)`.
  have hM53lt : M ^ ((53:ℕ):ℝ) < Δ := by
    have hM53pos : 0 ≤ M ^ ((53:ℕ):ℝ) := by positivity
    have hh : M ^ ((53:ℕ):ℝ) ≤ 1000 * M ^ ((53:ℕ):ℝ) := by
      calc M ^ ((53:ℕ):ℝ) = 1 * M ^ ((53:ℕ):ℝ) := by ring
        _ ≤ 1000 * M ^ ((53:ℕ):ℝ) := mul_le_mul_of_nonneg_right (by norm_num) hM53pos
    have h1r : 1000 * M ^ ((53:ℕ):ℝ) < Δ := by
      rw [← Real.rpow_natCast M 53] at h1; exact h1
    exact lt_of_le_of_lt hh h1r
  have hM17leΔ : M ^ ((17:ℕ):ℝ) ≤ Δ ^ ((1:ℝ)/2) := by
    have step1 : (M ^ ((53:ℕ):ℝ)) ^ ((17:ℝ)/53) ≤ Δ ^ ((17:ℝ)/53) :=
      Real.rpow_le_rpow (by positivity) (le_of_lt hM53lt) (by norm_num)
    have e : (M ^ ((53:ℕ):ℝ)) ^ ((17:ℝ)/53) = M ^ ((17:ℕ):ℝ) := by
      rw [← Real.rpow_mul hMnn]; norm_num
    rw [e] at step1
    exact le_trans step1 (Real.rpow_le_rpow_of_exponent_le hΔ (by norm_num))
  -- Bound for the term `M^70 * Z^6 * Δ^(3/2)`.
  have b3 : M ^ ((70:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((3:ℝ)/2) ≤ M ^ ((53:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ) := by
    have hd32 : Δ ^ ((1:ℝ)/2) * Δ ^ ((3:ℝ)/2) = Δ ^ ((2:ℕ):ℝ) := by rw [← Real.rpow_add hΔ0]; norm_num
    have b3core : M ^ ((17:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((3:ℝ)/2) ≤ Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ) := by
      have step := mul_le_mul_of_nonneg_right hM17leΔ (by positivity : (0:ℝ) ≤ Z ^ ((6:ℕ):ℝ) * Δ ^ ((3:ℝ)/2))
      have eL : M ^ ((17:ℕ):ℝ) * (Z ^ ((6:ℕ):ℝ) * Δ ^ ((3:ℝ)/2)) = M ^ ((17:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((3:ℝ)/2) := by ring
      have eR : Δ ^ ((1:ℝ)/2) * (Z ^ ((6:ℕ):ℝ) * Δ ^ ((3:ℝ)/2)) = Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ) := by
        calc _ = (Δ ^ ((1:ℝ)/2) * Δ ^ ((3:ℝ)/2)) * Z ^ ((6:ℕ):ℝ) := by ring
          _ = Δ ^ ((2:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) := by rw [hd32]
          _ = Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ) := by ring
      rw [eL, eR] at step
      exact step
    have step := mul_le_mul_of_nonneg_left b3core (by positivity : (0:ℝ) ≤ M ^ ((53:ℕ):ℝ))
    have e3 : M ^ ((53:ℕ):ℝ) * (M ^ ((17:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((3:ℝ)/2)) = M ^ ((70:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((3:ℝ)/2) := by
      calc _ = (M ^ ((53:ℕ):ℝ) * M ^ ((17:ℕ):ℝ)) * (Z ^ ((6:ℕ):ℝ) * Δ ^ ((3:ℝ)/2)) := by ring
        _ = M ^ ((70:ℕ):ℝ) * (Z ^ ((6:ℕ):ℝ) * Δ ^ ((3:ℝ)/2)) := by rw [hMadd]
        _ = M ^ ((70:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((3:ℝ)/2) := by ring
    have e4 : M ^ ((53:ℕ):ℝ) * (Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ)) = M ^ ((53:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ) := by ring
    rw [e3, e4] at step
    exact step
  -- Bounds for the terms with the `M^40` prefactor.
  have h40le : M ^ ((40:ℕ):ℝ) ≤ M ^ ((53:ℕ):ℝ) := Real.rpow_le_rpow_of_exponent_le hM (by norm_num)
  have hZ4le : Z ^ ((4:ℕ):ℝ) ≤ Z ^ ((9:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  have hΔ3le : Δ ^ ((3:ℕ):ℝ) ≤ Δ ^ ((7:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le hΔ (by norm_num)
  have b4 : M ^ ((40:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((3:ℕ):ℝ) ≤ M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) := by
    have hmz : M ^ ((40:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) ≤ M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) :=
      mul_le_mul h40le hZ4le (by positivity) (by positivity)
    calc M ^ ((40:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((3:ℕ):ℝ)
        ≤ (M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2)) * Δ ^ ((3:ℕ):ℝ) := mul_le_mul_of_nonneg_right hmz (by positivity)
      _ ≤ (M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2)) * Δ ^ ((7:ℝ)/2) := mul_le_mul_of_nonneg_left hΔ3le (by positivity)
      _ = M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) := by ring
  have b5 : M ^ ((40:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ) ≤ M ^ ((53:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ) := by
    calc M ^ ((40:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ)
        = M ^ ((40:ℕ):ℝ) * (Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ)) := by ring
      _ ≤ M ^ ((53:ℕ):ℝ) * (Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ)) := mul_le_mul_of_nonneg_right h40le (by positivity)
      _ = M ^ ((53:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ) := by ring
  have hPnn : 0 ≤ M ^ ((53:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ) := by positivity
  have hQnn : 0 ≤ M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) := by positivity
  -- Expand the right-hand side into the two monomials.
  have hRHS : 1000 * Z ^ ((9:ℝ)/2) * Δ ^ ((2:ℕ):ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * M ^ ((53:ℕ):ℝ)
      = 1000 * (M ^ ((53:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ)
          + M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2)) := by
    rw [show Z ^ ((6:ℕ):ℝ) = Z ^ ((9:ℝ)/2) * Z ^ ((3:ℝ)/2) from by rw [← Real.rpow_add hZ0]; norm_num,
        show Δ ^ ((7:ℝ)/2) = Δ ^ ((3:ℝ)/2) * Δ ^ ((2:ℕ):ℝ) from by rw [← Real.rpow_add hΔ0]; norm_num]
    ring
  have e1 : M ^ ((70:ℕ):ℝ) * (Z ^ ((4:ℕ):ℝ) * Δ ^ ((11:ℝ)/3) + Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2) + Z ^ ((6:ℕ):ℝ) * Δ ^ ((3:ℝ)/2))
      = M ^ ((70:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((11:ℝ)/3) + M ^ ((70:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((7:ℝ)/2)
        + M ^ ((70:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((3:ℝ)/2) := by ring
  have e2 : M ^ ((40:ℕ):ℝ) * (Z ^ ((4:ℕ):ℝ) * Δ ^ ((3:ℕ):ℝ) + Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ))
      = M ^ ((40:ℕ):ℝ) * Z ^ ((4:ℕ):ℝ) * Δ ^ ((3:ℕ):ℝ) + M ^ ((40:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ) := by ring
  rw [e1, e2, hRHS]
  refine le_trans (add_le_add (add_le_add (add_le_add b1 b2) b3) (add_le_add b4 b5)) ?_
  calc (((1:ℝ)/10 * (M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2))
          + (1:ℝ)/10 * (M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2)))
        + (M ^ ((53:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ)))
      + ((M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2))
          + (M ^ ((53:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ)))
      = (2:ℝ)*(M ^ ((53:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ))
          + (6:ℝ)/5*(M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2)) := by ring
    _ ≤ 1000*(M ^ ((53:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ))
          + 1000*(M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2)) :=
        add_le_add (mul_le_mul_of_nonneg_right (by norm_num) hPnn)
          (mul_le_mul_of_nonneg_right (by norm_num) hQnn)
    _ = 1000 * (M ^ ((53:ℕ):ℝ) * Z ^ ((6:ℕ):ℝ) * Δ ^ ((2:ℕ):ℝ)
          + M ^ ((53:ℕ):ℝ) * Z ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2)) := by ring

end Work.HP.MDEstimates
