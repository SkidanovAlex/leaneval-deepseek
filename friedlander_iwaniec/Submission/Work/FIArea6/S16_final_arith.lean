import Mathlib

namespace Work.FIArea6

/-- Elementary arithmetic core of §16: the two weighted "main-term" contributions
`8·Wk·X²·(cε·A·4X·N·t⁶)²` and `8·W2·M²·X²` are bounded by
`(4096·cε² + 360·Cm²)·A·X⁵·N²·u¹³`, using `Wk ≤ 16u`, `W2 ≤ 5X³/E`, `M² ≤ 9Cm²N²u¹⁸`
and `u⁵ ≤ AE`, together with `A ≤ 2`, `t ≤ u`, `1 ≤ X`. -/
theorem S16_final_arith (cε Cm c1 t u X N A M Wk W2 E : ℝ)
    (hA0 : 0 ≤ A) (hA2 : A ≤ 2)
    (hAexp : Real.exp (-(c1 * t ^ ((1 : ℝ) / 4))) ≤ A)
    (hAE : u ^ (5 : ℕ) ≤ A * E)
    (ht0 : 0 ≤ t) (htu : t ≤ u) (hu1 : 1 ≤ u) (hX : 1 ≤ X) (hE : 0 < E)
    (hWk : Wk ≤ 16 * u) (hW2 : W2 ≤ 5 * X ^ (3 : ℕ) / E)
    (hM : 0 ≤ M) (hM2 : M ^ (2 : ℕ) ≤ 9 * Cm ^ (2 : ℕ) * N ^ (2 : ℕ) * u ^ (18 : ℕ)) :
    8 * Wk * X ^ (2 : ℕ) * (cε * A * (4 * X) * N * t ^ (6 : ℕ)) ^ (2 : ℕ)
        + 8 * W2 * M ^ (2 : ℕ) * X ^ (2 : ℕ)
      ≤ (4096 * cε ^ (2 : ℕ) + 360 * Cm ^ (2 : ℕ)) * (A * X ^ (5 : ℕ) * N ^ (2 : ℕ) * u ^ (13 : ℕ)) := by
  -- the remaining hypotheses of the statement are not needed for the arithmetic
  have _hM0 : (0 : ℝ) ≤ M := hM
  have _hAexp0 : Real.exp (-(c1 * t ^ ((1 : ℝ) / 4))) ≤ A := hAexp
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hu0 : (0 : ℝ) ≤ u := by linarith
  -- `A t¹² ≤ 2 X u¹²` from `A ≤ 2`, `t ≤ u`, `1 ≤ X`
  have htu12 : t ^ (12 : ℕ) ≤ u ^ (12 : ℕ) := pow_le_pow_left₀ ht0 htu 12
  have hu12 : (0 : ℝ) ≤ u ^ (12 : ℕ) := pow_nonneg hu0 12
  have ht12 : (0 : ℝ) ≤ t ^ (12 : ℕ) := pow_nonneg ht0 12
  have hA3 : A * t ^ (12 : ℕ) ≤ 2 * X * u ^ (12 : ℕ) := by
    nlinarith [htu12, hu12, ht12, hX, hA2, hA0]
  -- `A² t¹² u ≤ 2 A X u¹³`
  have hA4 : A ^ (2 : ℕ) * t ^ (12 : ℕ) * u ≤ 2 * A * X * u ^ (13 : ℕ) := by
    have h4a : A * (A * t ^ (12 : ℕ)) ≤ A * (2 * X * u ^ (12 : ℕ)) :=
      mul_le_mul_of_nonneg_left hA3 hA0
    have h4b : A * (A * t ^ (12 : ℕ)) * u ≤ A * (2 * X * u ^ (12 : ℕ)) * u :=
      mul_le_mul_of_nonneg_right h4a hu0
    have h := h4b
    ring_nf at h ⊢
    linarith [h]
  -- First term.
  have t1 : 8 * Wk * X ^ (2 : ℕ) * (cε * A * (4 * X) * N * t ^ (6 : ℕ)) ^ (2 : ℕ)
      ≤ 4096 * cε ^ (2 : ℕ) * (A * X ^ (5 : ℕ) * N ^ (2 : ℕ) * u ^ (13 : ℕ)) := by
    have h8F : (0 : ℝ) ≤ 8 * (X ^ (2 : ℕ) * (cε * A * (4 * X) * N * t ^ (6 : ℕ)) ^ (2 : ℕ)) := by
      positivity
    have s1 : 8 * Wk * X ^ (2 : ℕ) * (cε * A * (4 * X) * N * t ^ (6 : ℕ)) ^ (2 : ℕ)
        ≤ 8 * (16 * u) * X ^ (2 : ℕ) * (cε * A * (4 * X) * N * t ^ (6 : ℕ)) ^ (2 : ℕ) := by
      have h := mul_le_mul_of_nonneg_left hWk h8F
      have hh := h
      ring_nf at hh ⊢
      linarith [hh]
    have hK : (0 : ℝ) ≤ 2048 * cε ^ (2 : ℕ) * X ^ (4 : ℕ) * N ^ (2 : ℕ) := by positivity
    have s2 : 2048 * cε ^ (2 : ℕ) * X ^ (4 : ℕ) * N ^ (2 : ℕ)
          * (A ^ (2 : ℕ) * t ^ (12 : ℕ) * u)
        ≤ 2048 * cε ^ (2 : ℕ) * X ^ (4 : ℕ) * N ^ (2 : ℕ) * (2 * A * X * u ^ (13 : ℕ)) :=
      mul_le_mul_of_nonneg_left hA4 hK
    calc 8 * Wk * X ^ (2 : ℕ) * (cε * A * (4 * X) * N * t ^ (6 : ℕ)) ^ (2 : ℕ)
        ≤ 8 * (16 * u) * X ^ (2 : ℕ) * (cε * A * (4 * X) * N * t ^ (6 : ℕ)) ^ (2 : ℕ) := s1
      _ = 2048 * cε ^ (2 : ℕ) * X ^ (4 : ℕ) * N ^ (2 : ℕ)
            * (A ^ (2 : ℕ) * t ^ (12 : ℕ) * u) := by ring
      _ ≤ 2048 * cε ^ (2 : ℕ) * X ^ (4 : ℕ) * N ^ (2 : ℕ) * (2 * A * X * u ^ (13 : ℕ)) := s2
      _ = 4096 * cε ^ (2 : ℕ) * (A * X ^ (5 : ℕ) * N ^ (2 : ℕ) * u ^ (13 : ℕ)) := by ring
  -- `u¹⁸ / E ≤ A u¹³` from `u⁵ ≤ A E`
  have hu18E : u ^ (18 : ℕ) / E ≤ A * u ^ (13 : ℕ) := by
    have hdiv : u ^ (5 : ℕ) / E ≤ A := (div_le_iff₀ hE).mpr hAE
    have h := mul_le_mul_of_nonneg_left hdiv (pow_nonneg hu0 13)
    have hh := h
    ring_nf at hh ⊢
    linarith [hh]
  -- Second term.
  have t2 : 8 * W2 * M ^ (2 : ℕ) * X ^ (2 : ℕ)
      ≤ 360 * Cm ^ (2 : ℕ) * (A * X ^ (5 : ℕ) * N ^ (2 : ℕ) * u ^ (13 : ℕ)) := by
    have h8M : (0 : ℝ) ≤ 8 * (M ^ (2 : ℕ) * X ^ (2 : ℕ)) := by positivity
    have s1 : 8 * W2 * M ^ (2 : ℕ) * X ^ (2 : ℕ)
        ≤ 8 * (5 * X ^ (3 : ℕ) / E) * M ^ (2 : ℕ) * X ^ (2 : ℕ) := by
      have h := mul_le_mul_of_nonneg_left hW2 h8M
      have hh := h
      ring_nf at hh ⊢
      linarith [hh]
    have hK2 : (0 : ℝ) ≤ 40 * X ^ (5 : ℕ) / E := by positivity
    have s2 : 40 * X ^ (5 : ℕ) / E * M ^ (2 : ℕ)
        ≤ 40 * X ^ (5 : ℕ) / E * (9 * Cm ^ (2 : ℕ) * N ^ (2 : ℕ) * u ^ (18 : ℕ)) :=
      mul_le_mul_of_nonneg_left hM2 hK2
    have hK3 : (0 : ℝ) ≤ 360 * Cm ^ (2 : ℕ) * N ^ (2 : ℕ) * X ^ (5 : ℕ) := by positivity
    have s3 : 360 * Cm ^ (2 : ℕ) * N ^ (2 : ℕ) * X ^ (5 : ℕ) * (u ^ (18 : ℕ) / E)
        ≤ 360 * Cm ^ (2 : ℕ) * N ^ (2 : ℕ) * X ^ (5 : ℕ) * (A * u ^ (13 : ℕ)) :=
      mul_le_mul_of_nonneg_left hu18E hK3
    calc 8 * W2 * M ^ (2 : ℕ) * X ^ (2 : ℕ)
        ≤ 8 * (5 * X ^ (3 : ℕ) / E) * M ^ (2 : ℕ) * X ^ (2 : ℕ) := s1
      _ = 40 * X ^ (5 : ℕ) / E * M ^ (2 : ℕ) := by ring
      _ ≤ 40 * X ^ (5 : ℕ) / E * (9 * Cm ^ (2 : ℕ) * N ^ (2 : ℕ) * u ^ (18 : ℕ)) := s2
      _ = 360 * Cm ^ (2 : ℕ) * N ^ (2 : ℕ) * X ^ (5 : ℕ) * (u ^ (18 : ℕ) / E) := by ring
      _ ≤ 360 * Cm ^ (2 : ℕ) * N ^ (2 : ℕ) * X ^ (5 : ℕ) * (A * u ^ (13 : ℕ)) := s3
      _ = 360 * Cm ^ (2 : ℕ) * (A * X ^ (5 : ℕ) * N ^ (2 : ℕ) * u ^ (13 : ℕ)) := by ring
  have h := add_le_add t1 t2
  have hh := h
  ring_nf at hh ⊢
  linarith [hh]

end Work.FIArea6
