import Mathlib.Algebra.Order.Star.Real

set_option maxHeartbeats 1000000

namespace Commons.Analysis.Real

/-- Square root is subadditive on nonnegative reals. -/
theorem bterm_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hsq : (Real.sqrt x + Real.sqrt y) ^ 2 = x + y + 2 * (Real.sqrt x * Real.sqrt y) := by
    rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]; ring
  have hxy : 0 ≤ Real.sqrt x * Real.sqrt y :=
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
  nlinarith [hsq, hxy]

theorem bterm_arith {AvgB AvgLow CntDbl PGlt PGgt P ρ Rg η₁ η₂ C₁ C₂ KK L₂ ηB CB : ℝ} {N : ℕ}
    (hRg : 1 ≤ Rg) (hρ : 0 ≤ ρ) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hAvgB0 : 0 ≤ AvgB) (hAvgLow0 : 0 ≤ AvgLow) (hCntDbl0 : 0 ≤ CntDbl)
    (hPGlt0 : 0 ≤ PGlt) (hPGgt0 : 0 ≤ PGgt) (hP0 : 0 ≤ P)
    (hPGlt1 : PGlt ≤ 1) (hPGgt1 : PGgt ≤ 1)
    (hH3 : AvgB ≤ (1 / Rg) * AvgLow)
    (hIHLow : AvgLow ≤ (1 + η₁) * PGlt + C₁ * ρ)
    (hIHDbl : CntDbl ≤ (1 + η₂) * (PGlt * PGgt ^ 2) + C₂ * ρ)
    (hprod : PGlt * PGgt ≤ KK * P)
    (hP : (1 / L₂) ^ N ≤ P)
    (hηB0 : 0 ≤ ηB)
    (hkey1 : Real.sqrt (1 + η₁) * Real.sqrt (1 + η₂) * KK ≤ ηB / 2)
    (hkey2 : Real.sqrt ρ * (Real.sqrt (1 + η₁) * Real.sqrt C₂ + Real.sqrt (1 + η₂) * Real.sqrt C₁)
        ≤ (ηB / 2) * (1 / L₂) ^ N)
    (hkey3 : Real.sqrt (C₁ * C₂) ≤ CB / 2) :
    Real.sqrt AvgB * Real.sqrt CntDbl ≤ ηB * P + CB * ρ := by
  have h1η : (0 : ℝ) ≤ 1 + η₁ := by linarith
  have h2η : (0 : ℝ) ≤ 1 + η₂ := by linarith
  have hm1 : (0 : ℝ) ≤ Real.sqrt (1 + η₁) := Real.sqrt_nonneg _
  have hm2 : (0 : ℝ) ≤ Real.sqrt (1 + η₂) := Real.sqrt_nonneg _
  have hRgpos : (0 : ℝ) < Rg := by linarith
  have hCB0 : (0 : ℝ) ≤ CB := by
    have := Real.sqrt_nonneg (C₁ * C₂)
    linarith [hkey3]
  have hCB2 : (0 : ℝ) ≤ CB / 2 := by linarith
  have hηB2 : (0 : ℝ) ≤ ηB / 2 := by linarith
  -- Step 1: `AvgB ≤ AvgLow`
  have hAvgB_le : AvgB ≤ AvgLow := by
    have hinv : (1 : ℝ) / Rg ≤ 1 := (div_le_one hRgpos).mpr hRg
    calc AvgB ≤ (1 / Rg) * AvgLow := hH3
      _ ≤ 1 * AvgLow := mul_le_mul_of_nonneg_right hinv hAvgLow0
      _ = AvgLow := one_mul _
  -- Step 2: nonnegativity of the two upper bounds
  have hu : (0 : ℝ) ≤ (1 + η₁) * PGlt := mul_nonneg h1η hPGlt0
  have hv : (0 : ℝ) ≤ C₁ * ρ := mul_nonneg hC₁ hρ
  have hw : (0 : ℝ) ≤ (1 + η₂) * (PGlt * PGgt ^ 2) :=
    mul_nonneg h2η (mul_nonneg hPGlt0 (sq_nonneg _))
  have ht : (0 : ℝ) ≤ C₂ * ρ := mul_nonneg hC₂ hρ
  have hA' : (0 : ℝ) ≤ (1 + η₁) * PGlt + C₁ * ρ := add_nonneg hu hv
  have hC' : (0 : ℝ) ≤ (1 + η₂) * (PGlt * PGgt ^ 2) + C₂ * ρ := add_nonneg hw ht
  -- Step 3: sqrt bounds and multiplication
  have hsA : Real.sqrt AvgB ≤ Real.sqrt ((1 + η₁) * PGlt + C₁ * ρ) :=
    Real.sqrt_le_sqrt (le_trans hAvgB_le hIHLow)
  have hsC : Real.sqrt CntDbl ≤ Real.sqrt ((1 + η₂) * (PGlt * PGgt ^ 2) + C₂ * ρ) :=
    Real.sqrt_le_sqrt hIHDbl
  have hmul : Real.sqrt AvgB * Real.sqrt CntDbl
      ≤ Real.sqrt ((1 + η₁) * PGlt + C₁ * ρ)
        * Real.sqrt ((1 + η₂) * (PGlt * PGgt ^ 2) + C₂ * ρ) :=
    mul_le_mul hsA hsC (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmul_eq : Real.sqrt ((1 + η₁) * PGlt + C₁ * ρ)
        * Real.sqrt ((1 + η₂) * (PGlt * PGgt ^ 2) + C₂ * ρ)
      = Real.sqrt (((1 + η₁) * PGlt + C₁ * ρ)
          * ((1 + η₂) * (PGlt * PGgt ^ 2) + C₂ * ρ)) :=
    (Real.sqrt_mul hA' ((1 + η₂) * (PGlt * PGgt ^ 2) + C₂ * ρ)).symm
  -- Step 4: expand the product and split the square root
  have hx1 : (0 : ℝ) ≤ ((1 + η₁) * PGlt) * ((1 + η₂) * (PGlt * PGgt ^ 2)) := mul_nonneg hu hw
  have hx2 : (0 : ℝ) ≤ ((1 + η₁) * PGlt) * (C₂ * ρ) := mul_nonneg hu ht
  have hx3 : (0 : ℝ) ≤ (C₁ * ρ) * ((1 + η₂) * (PGlt * PGgt ^ 2)) := mul_nonneg hv hw
  have hx4 : (0 : ℝ) ≤ (C₁ * ρ) * (C₂ * ρ) := mul_nonneg hv ht
  have hdecomp : Real.sqrt (((1 + η₁) * PGlt + C₁ * ρ)
        * ((1 + η₂) * (PGlt * PGgt ^ 2) + C₂ * ρ))
      ≤ Real.sqrt (((1 + η₁) * PGlt) * ((1 + η₂) * (PGlt * PGgt ^ 2)))
        + Real.sqrt (((1 + η₁) * PGlt) * (C₂ * ρ))
        + Real.sqrt ((C₁ * ρ) * ((1 + η₂) * (PGlt * PGgt ^ 2)))
        + Real.sqrt ((C₁ * ρ) * (C₂ * ρ)) := by
    have heq : ((1 + η₁) * PGlt + C₁ * ρ) * ((1 + η₂) * (PGlt * PGgt ^ 2) + C₂ * ρ)
        = (((1 + η₁) * PGlt) * ((1 + η₂) * (PGlt * PGgt ^ 2)) + ((1 + η₁) * PGlt) * (C₂ * ρ))
          + ((C₁ * ρ) * ((1 + η₂) * (PGlt * PGgt ^ 2)) + (C₁ * ρ) * (C₂ * ρ)) := by ring
    rw [heq]
    have s1 := bterm_sqrt_add_le (x := ((1 + η₁) * PGlt) * ((1 + η₂) * (PGlt * PGgt ^ 2))
          + ((1 + η₁) * PGlt) * (C₂ * ρ))
        (y := (C₁ * ρ) * ((1 + η₂) * (PGlt * PGgt ^ 2)) + (C₁ * ρ) * (C₂ * ρ))
        (add_nonneg hx1 hx2) (add_nonneg hx3 hx4)
    have s2 := bterm_sqrt_add_le (x := ((1 + η₁) * PGlt) * ((1 + η₂) * (PGlt * PGgt ^ 2)))
        (y := ((1 + η₁) * PGlt) * (C₂ * ρ)) hx1 hx2
    have s3 := bterm_sqrt_add_le (x := (C₁ * ρ) * ((1 + η₂) * (PGlt * PGgt ^ 2)))
        (y := (C₁ * ρ) * (C₂ * ρ)) hx3 hx4
    linarith
  -- Step 5: bound the four terms
  have hT1le : Real.sqrt (((1 + η₁) * PGlt) * ((1 + η₂) * (PGlt * PGgt ^ 2)))
      ≤ (ηB / 2) * P := by
    have hval : Real.sqrt (((1 + η₁) * PGlt) * ((1 + η₂) * (PGlt * PGgt ^ 2)))
        = Real.sqrt (1 + η₁) * Real.sqrt (1 + η₂) * (PGlt * PGgt) := by
      have he : ((1 + η₁) * PGlt) * ((1 + η₂) * (PGlt * PGgt ^ 2))
          = ((1 + η₁) * (1 + η₂)) * (PGlt * PGgt) ^ 2 := by ring
      calc Real.sqrt (((1 + η₁) * PGlt) * ((1 + η₂) * (PGlt * PGgt ^ 2)))
          = Real.sqrt (((1 + η₁) * (1 + η₂)) * (PGlt * PGgt) ^ 2) := by rw [he]
        _ = Real.sqrt ((1 + η₁) * (1 + η₂)) * Real.sqrt ((PGlt * PGgt) ^ 2) := by
              rw [Real.sqrt_mul (mul_nonneg h1η h2η)]
        _ = Real.sqrt ((1 + η₁) * (1 + η₂)) * (PGlt * PGgt) := by
              rw [Real.sqrt_sq (mul_nonneg hPGlt0 hPGgt0)]
        _ = (Real.sqrt (1 + η₁) * Real.sqrt (1 + η₂)) * (PGlt * PGgt) := by
              rw [Real.sqrt_mul h1η]
        _ = Real.sqrt (1 + η₁) * Real.sqrt (1 + η₂) * (PGlt * PGgt) := by ring
    rw [hval]
    have hstep : Real.sqrt (1 + η₁) * Real.sqrt (1 + η₂) * (PGlt * PGgt)
        ≤ Real.sqrt (1 + η₁) * Real.sqrt (1 + η₂) * (KK * P) :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg hm1 hm2)
    have hstep2 : Real.sqrt (1 + η₁) * Real.sqrt (1 + η₂) * (KK * P)
        = (Real.sqrt (1 + η₁) * Real.sqrt (1 + η₂) * KK) * P := by ring
    have hstep3 : (Real.sqrt (1 + η₁) * Real.sqrt (1 + η₂) * KK) * P ≤ (ηB / 2) * P :=
      mul_le_mul_of_nonneg_right hkey1 hP0
    linarith
  have hT2le : Real.sqrt (((1 + η₁) * PGlt) * (C₂ * ρ))
      ≤ Real.sqrt (1 + η₁) * Real.sqrt C₂ * Real.sqrt ρ := by
    have hRHS : (0 : ℝ) ≤ Real.sqrt (1 + η₁) * Real.sqrt C₂ * Real.sqrt ρ :=
      mul_nonneg (mul_nonneg hm1 (Real.sqrt_nonneg C₂)) (Real.sqrt_nonneg ρ)
    rw [Real.sqrt_le_iff]
    refine ⟨hRHS, ?_⟩
    have hsq : (Real.sqrt (1 + η₁) * Real.sqrt C₂ * Real.sqrt ρ) ^ 2 = (1 + η₁) * C₂ * ρ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt h1η, Real.sq_sqrt hC₂, Real.sq_sqrt hρ]
    rw [hsq]
    have hk : (0 : ℝ) ≤ (1 + η₁) * C₂ * ρ := mul_nonneg (mul_nonneg h1η hC₂) hρ
    have hm : (1 + η₁) * C₂ * ρ * PGlt ≤ (1 + η₁) * C₂ * ρ * 1 :=
      mul_le_mul_of_nonneg_left hPGlt1 hk
    nlinarith [hm]
  have hT3le : Real.sqrt ((C₁ * ρ) * ((1 + η₂) * (PGlt * PGgt ^ 2)))
      ≤ Real.sqrt (1 + η₂) * Real.sqrt C₁ * Real.sqrt ρ := by
    have hRHS : (0 : ℝ) ≤ Real.sqrt (1 + η₂) * Real.sqrt C₁ * Real.sqrt ρ :=
      mul_nonneg (mul_nonneg hm2 (Real.sqrt_nonneg C₁)) (Real.sqrt_nonneg ρ)
    rw [Real.sqrt_le_iff]
    refine ⟨hRHS, ?_⟩
    have hsq : (Real.sqrt (1 + η₂) * Real.sqrt C₁ * Real.sqrt ρ) ^ 2 = (1 + η₂) * C₁ * ρ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt h2η, Real.sq_sqrt hC₁, Real.sq_sqrt hρ]
    rw [hsq]
    have hPg : PGlt * PGgt ^ 2 ≤ 1 := by
      have h1 : PGgt ^ 2 ≤ 1 := pow_le_one₀ hPGgt0 hPGgt1
      have h2 : PGlt * PGgt ^ 2 ≤ PGlt * 1 := mul_le_mul_of_nonneg_left h1 hPGlt0
      linarith
    have hk : (0 : ℝ) ≤ (1 + η₂) * C₁ * ρ := mul_nonneg (mul_nonneg h2η hC₁) hρ
    have hm : (1 + η₂) * C₁ * ρ * (PGlt * PGgt ^ 2) ≤ (1 + η₂) * C₁ * ρ * 1 :=
      mul_le_mul_of_nonneg_left hPg hk
    nlinarith [hm]
  have hT4le : Real.sqrt ((C₁ * ρ) * (C₂ * ρ)) ≤ (CB / 2) * ρ := by
    have hRHS : (0 : ℝ) ≤ (CB / 2) * ρ := mul_nonneg hCB2 hρ
    rw [Real.sqrt_le_iff]
    refine ⟨hRHS, ?_⟩
    have hsq : ((CB / 2) * ρ) ^ 2 = (CB / 2) ^ 2 * ρ ^ 2 := by ring
    rw [hsq]
    have hle : C₁ * C₂ ≤ (CB / 2) ^ 2 := (Real.sqrt_le_iff.mp hkey3).2
    nlinarith [hle, hρ]
  -- Step 6: the two middle terms
  have hmid : Real.sqrt (1 + η₁) * Real.sqrt C₂ * Real.sqrt ρ
        + Real.sqrt (1 + η₂) * Real.sqrt C₁ * Real.sqrt ρ ≤ (ηB / 2) * P := by
    have hfac : Real.sqrt (1 + η₁) * Real.sqrt C₂ * Real.sqrt ρ
          + Real.sqrt (1 + η₂) * Real.sqrt C₁ * Real.sqrt ρ
        = Real.sqrt ρ
          * (Real.sqrt (1 + η₁) * Real.sqrt C₂ + Real.sqrt (1 + η₂) * Real.sqrt C₁) := by ring
    calc Real.sqrt (1 + η₁) * Real.sqrt C₂ * Real.sqrt ρ
          + Real.sqrt (1 + η₂) * Real.sqrt C₁ * Real.sqrt ρ
        = Real.sqrt ρ
          * (Real.sqrt (1 + η₁) * Real.sqrt C₂ + Real.sqrt (1 + η₂) * Real.sqrt C₁) := hfac
      _ ≤ (ηB / 2) * (1 / L₂) ^ N := hkey2
      _ ≤ (ηB / 2) * P := mul_le_mul_of_nonneg_left hP hηB2
  -- Step 7: assemble
  calc Real.sqrt AvgB * Real.sqrt CntDbl
      ≤ Real.sqrt ((1 + η₁) * PGlt + C₁ * ρ)
        * Real.sqrt ((1 + η₂) * (PGlt * PGgt ^ 2) + C₂ * ρ) := hmul
    _ = Real.sqrt (((1 + η₁) * PGlt + C₁ * ρ)
          * ((1 + η₂) * (PGlt * PGgt ^ 2) + C₂ * ρ)) := hmul_eq
    _ ≤ Real.sqrt (((1 + η₁) * PGlt) * ((1 + η₂) * (PGlt * PGgt ^ 2)))
        + Real.sqrt (((1 + η₁) * PGlt) * (C₂ * ρ))
        + Real.sqrt ((C₁ * ρ) * ((1 + η₂) * (PGlt * PGgt ^ 2)))
        + Real.sqrt ((C₁ * ρ) * (C₂ * ρ)) := hdecomp
    _ ≤ (ηB / 2) * P + (Real.sqrt (1 + η₁) * Real.sqrt C₂ * Real.sqrt ρ
          + Real.sqrt (1 + η₂) * Real.sqrt C₁ * Real.sqrt ρ) + (CB / 2) * ρ := by
        linarith [hT1le, hT2le, hT3le, hT4le, hmid]
    _ ≤ ηB * P + CB * ρ := by
        have hCBle : (CB / 2) * ρ ≤ CB * ρ := by nlinarith [hCB0, hρ]
        nlinarith [hmid, hCBle]

end Commons.Analysis.Real