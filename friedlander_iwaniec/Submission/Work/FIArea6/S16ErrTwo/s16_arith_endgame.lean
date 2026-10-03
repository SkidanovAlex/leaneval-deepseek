import Mathlib

set_option maxHeartbeats 1000000

namespace Work.FIArea6.S16ErrTwo

/-- **The arithmetic endgame of the §16 error bound.**  Pure real arithmetic (no number theory):
given the numerical restrictions

* `1 ≤ N`, `1 ≤ L`, `1 ≤ X`, `1 ≤ U`, `U ≤ 3L`, `U = 1 + log(2+N)`, `1 + log(2+X) ≤ U`;
* `0 ≤ th` (the smoothing parameter `θ`) with `θ·L³ ≤ 1`; `0 ≤ Sq` (the square mass) with
  `Sq ≤ 1000·(θN + √N + 1)·U³`;
* `1 ≤ Pz`, `X²U¹⁵ ≤ Pz` (the §16 cut);
* the monomials `L^{2ν+4} ≤ √N`, `L^{ν+4} ≤ √N`, `L³ ≤ √N`, `L³ ≤ N` for `0 ≤ ν`;
* the 12-term polar-box bound
  `L⁴·X·(X² + θ√N·X + √N + θN/X)·(θN + √N + 1) ≤ 12N²`;
* `0 ≤ Cd, Cn, Cc, Cf` and the four constant comparisons,

the four terms of the §16 error bundle up to `C·(Pz⁻¹ + X⁻¹)·N²·L`. -/
theorem s16_arith_endgame (Cd Cn Cc Cf N L X U th Pz Sq ν : ℝ)
    (hCd0 : 0 ≤ Cd) (hCn0 : 0 ≤ Cn) (hCc0 : 0 ≤ Cc) (hCf0 : 0 ≤ Cf)
    (hth0 : 0 ≤ th) (hSq0 : 0 ≤ Sq)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hX : 1 ≤ X) (hU : 1 ≤ U) (hUL : U ≤ 3 * L)
    (hUdef : U = 1 + Real.log (2 + N))
    (hthL : th * L^(3:ℕ) ≤ 1)
    (hSq : Sq ≤ 1000 * (th * N + Real.sqrt N + 1) * U^(3:ℕ))
    (hPz1 : 1 ≤ Pz) (hPz0 : 0 < Pz) (hPzU : X^(2:ℕ) * U^(15:ℕ) ≤ Pz)
    (hlogX : 1 + Real.log (2 + X) ≤ U)
    (hν : 0 ≤ ν)
    (hm1 : L^(2 * ν + 4) ≤ Real.sqrt N)
    (hm2 : L^(1 * ν + 4) ≤ Real.sqrt N)
    (hm3 : L^3 ≤ Real.sqrt N) (hm4 : L^3 ≤ N)
    (hW : L^(4:ℕ) * (X * (X^(2:ℕ) + th * Real.sqrt N * X + Real.sqrt N + th * N / X))
        * (th * N + Real.sqrt N + 1) ≤ 12 * N^(2:ℕ))
    (hCd : 124416000 * Cd ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ))
    (hCn : 186624000 * Cn ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ))
    (hCc : 8192 * Cc ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ))
    (hCf : 124416000 * Cf ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ)) :
    2 * (16 * U * (X * Cd * Sq)
        + 16 * U * (Cn * Sq * (1 + Real.log (2 + X))
            * (X^(2:ℕ) + th * Real.sqrt N * X + Real.sqrt N + th * N / X))
        + 16 * U * (Cc * N^(2:ℕ) * (1 + Real.log (2 + N))^(14:ℕ) * X / Pz)
        + Cf * Sq * N * (1 + Real.log (2 + N)) / X^(2:ℕ))
      ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ) * (Pz⁻¹ + X⁻¹) * N^(2:ℕ) * L := by
  have hNpos : 0 < N := by linarith
  have hLpos : 0 < L := by linarith
  have hXpos : 0 < X := by linarith
  have hUpos : 0 < U := by linarith
  have hN0 : 0 ≤ N := le_of_lt hNpos
  have hX0 : 0 ≤ X := le_of_lt hXpos
  have hL0 : 0 ≤ L := le_of_lt hLpos
  have hsN0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hsN2 : Real.sqrt N * Real.sqrt N = N := by
    rw [← pow_two]; exact Real.sq_sqrt hN0
  set B : ℝ := th * N + Real.sqrt N + 1 with hBdef
  set Wt : ℝ := X^(2:ℕ) + th * Real.sqrt N * X + Real.sqrt N + th * N / X with hWdef
  set C0 : ℝ := (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ) with hC0def
  have hC0nn : 0 ≤ C0 := by rw [hC0def]; positivity
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hWtnn : 0 ≤ Wt := by rw [hWdef]; positivity
  have hWtge : X^(2:ℕ) ≤ Wt := by
    have h1 : 0 ≤ th * Real.sqrt N * X := by positivity
    have h2 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
    have h3 : 0 ≤ th * N / X := by positivity
    rw [hWdef]; linarith only [h1, h2, h3]
  have hSqB : Sq ≤ 1000 * B * U^(3:ℕ) := by rw [hBdef]; exact hSq
  -- the two main bounds in `B`/`Wt` form
  have hWB : B * Wt * L^(4:ℕ) * X ≤ 12 * N^(2:ℕ) := by
    rw [show B * Wt * L^(4:ℕ) * X = L^(4:ℕ) * (X * Wt) * B by ring]
    exact hW
  have hCdC0 : 124416000 * Cd ≤ C0 := by rw [hC0def]; exact hCd
  have hCnC0 : 186624000 * Cn ≤ C0 := by rw [hC0def]; exact hCn
  have hCcC0 : 8192 * Cc ≤ C0 := by rw [hC0def]; exact hCc
  have hCfC0 : 124416000 * Cf ≤ C0 := by rw [hC0def]; exact hCf
  -- powers of `U` against `L`
  have hU3 : U^(3:ℕ) ≤ 27 * L^(3:ℕ) := by
    have h := pow_le_pow_left₀ (le_of_lt hUpos) hUL 3
    have he : (3 * L)^(3:ℕ) = 27 * L^(3:ℕ) := by ring
    rwa [he] at h
  have hU4 : U^(4:ℕ) ≤ 81 * L^(4:ℕ) := by
    have h := pow_le_pow_left₀ (le_of_lt hUpos) hUL 4
    have he : (3 * L)^(4:ℕ) = 81 * L^(4:ℕ) := by ring
    rwa [he] at h
  have hU5 : U^(5:ℕ) ≤ 243 * L^(5:ℕ) := by
    have h := pow_le_pow_left₀ (le_of_lt hUpos) hUL 5
    have he : (3 * L)^(5:ℕ) = 243 * L^(5:ℕ) := by ring
    rwa [he] at h
  -- the polar-box bound in the form used below
  have hB3 : B * L^(4:ℕ) * X^(3:ℕ) ≤ 12 * N^(2:ℕ) := by
    have h1 : X * X^(2:ℕ) ≤ X * Wt := mul_le_mul_of_nonneg_left hWtge hX0
    have h2 : B * L^(4:ℕ) * (X * X^(2:ℕ)) ≤ B * L^(4:ℕ) * (X * Wt) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    calc B * L^(4:ℕ) * X^(3:ℕ) = B * L^(4:ℕ) * (X * X^(2:ℕ)) := by ring
      _ ≤ B * L^(4:ℕ) * (X * Wt) := h2
      _ = B * Wt * L^(4:ℕ) * X := by ring
      _ ≤ 12 * N^(2:ℕ) := hWB
  -- `Sq ≤ 81000 N`
  have hSq81 : Sq ≤ 81000 * N := by
    have h3 : th * N * L^3 ≤ N := by
      have h := mul_le_mul_of_nonneg_left hthL hN0
      nlinarith only [h]
    have h4 : Real.sqrt N * L^3 ≤ N := by
      have h := mul_le_mul_of_nonneg_left hm3 hsN0
      rw [hsN2] at h; exact h
    have h6 : B * L^3 ≤ 3 * N := by
      rw [hBdef]; nlinarith only [h3, h4, hm4]
    calc Sq ≤ 1000 * B * U^(3:ℕ) := hSqB
      _ ≤ 1000 * B * (27 * L^(3:ℕ)) := mul_le_mul_of_nonneg_left hU3 (by positivity)
      _ = 27000 * (B * L^(3:ℕ)) := by ring
      _ ≤ 27000 * (3 * N) := mul_le_mul_of_nonneg_left h6 (by norm_num)
      _ = 81000 * N := by ring
  -- the four summands, abstracted
  set T1 : ℝ := 16 * U * (X * Cd * Sq) with hT1def
  set T2 : ℝ := 16 * U * (Cn * Sq * (1 + Real.log (2 + X)) * Wt) with hT2def
  set T3 : ℝ := 16 * U * (Cc * N^(2:ℕ) * (1 + Real.log (2 + N))^(14:ℕ) * X / Pz) with hT3def
  set T4 : ℝ := Cf * Sq * N * (1 + Real.log (2 + N)) / X^(2:ℕ) with hT4def
  set Z : ℝ := (Pz⁻¹ + X⁻¹) * N^(2:ℕ) * L with hZdef
  have hZnn : 0 ≤ Z := by rw [hZdef]; positivity
  -- ===== term 1 =====
  have hA : 2 * T1 ≤ (C0/4) * Z := by
    have hA1' : 2 * T1 * X^(2:ℕ) ≤ 31104000 * Cd * N^(2:ℕ) := by
      rw [hT1def]
      have he : 2 * (16 * U * (X * Cd * Sq)) * X^(2:ℕ) = Sq * (32 * Cd * U * X^(3:ℕ)) := by ring
      rw [he]
      calc Sq * (32 * Cd * U * X^(3:ℕ))
          ≤ (1000 * B * U^(3:ℕ)) * (32 * Cd * U * X^(3:ℕ)) :=
            mul_le_mul_of_nonneg_right hSqB (by positivity)
        _ = 32000 * Cd * B * U^(4:ℕ) * X^(3:ℕ) := by ring
        _ ≤ 32000 * Cd * B * (81 * L^(4:ℕ)) * X^(3:ℕ) := by
            have hh := mul_le_mul_of_nonneg_left hU4 (by positivity : (0:ℝ) ≤ 32000 * Cd * B * X^(3:ℕ))
            nlinarith only [hh]
        _ = 2592000 * Cd * (B * L^(4:ℕ) * X^(3:ℕ)) := by ring
        _ ≤ 2592000 * Cd * (12 * N^(2:ℕ)) := mul_le_mul_of_nonneg_left hB3 (by positivity)
        _ = 31104000 * Cd * N^(2:ℕ) := by ring
    have hA1 : 2 * T1 ≤ 31104000 * Cd * N^(2:ℕ) / X^(2:ℕ) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < X^(2:ℕ))]
      exact hA1'
    have hA2 : 31104000 * Cd * N^(2:ℕ) / X^(2:ℕ) ≤ (C0/4) * Z := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < X^(2:ℕ))]
      have ht : (1:ℝ) ≤ (Pz⁻¹ + X⁻¹) * L * X^(2:ℕ) := by
        have h1 : (Pz⁻¹ + X⁻¹) * L * X^(2:ℕ) = Pz⁻¹ * L * X^(2:ℕ) + L * X := by field_simp
        have h2 : 0 ≤ Pz⁻¹ * L * X^(2:ℕ) := by positivity
        have h3 : 1 ≤ L * X := by nlinarith only [hL, hX]
        linarith only [h1.le, h1.ge, h2, h3]
      have hCd' : 124416000 * Cd ≤ C0 * ((Pz⁻¹ + X⁻¹) * L * X^(2:ℕ)) := by
        calc 124416000 * Cd ≤ C0 := hCdC0
          _ = C0 * 1 := by ring
          _ ≤ C0 * ((Pz⁻¹ + X⁻¹) * L * X^(2:ℕ)) := mul_le_mul_of_nonneg_left ht hC0nn
      rw [hZdef]
      calc 31104000 * Cd * N^(2:ℕ)
          = (124416000 * Cd) * (N^(2:ℕ) / 4) := by ring
        _ ≤ (C0 * ((Pz⁻¹ + X⁻¹) * L * X^(2:ℕ))) * (N^(2:ℕ) / 4) :=
            mul_le_mul_of_nonneg_right hCd' (by positivity)
        _ = (C0/4) * ((Pz⁻¹ + X⁻¹) * N^(2:ℕ) * L) * X^(2:ℕ) := by ring
    linarith only [hA1, hA2]
  -- ===== term 2 =====
  have hB : 2 * T2 ≤ (C0/2) * Z := by
    have hB1' : 2 * T2 * X ≤ 93312000 * Cn * N^(2:ℕ) * L := by
      rw [hT2def]
      have hlogXnn : 0 ≤ 1 + Real.log (2 + X) := by
        have := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 + X); linarith
      have hprod : Sq * (1 + Real.log (2 + X)) ≤ 1000 * B * U^(4:ℕ) := by
        calc Sq * (1 + Real.log (2 + X)) ≤ (1000 * B * U^(3:ℕ)) * U :=
              mul_le_mul hSqB hlogX hlogXnn (by positivity)
          _ = 1000 * B * U^(4:ℕ) := by ring
      calc 2 * (16 * U * (Cn * Sq * (1 + Real.log (2 + X)) * Wt)) * X
          = (Sq * (1 + Real.log (2 + X))) * (32 * U * Cn * Wt * X) := by ring
        _ ≤ (1000 * B * U^(4:ℕ)) * (32 * U * Cn * Wt * X) :=
            mul_le_mul_of_nonneg_right hprod (by positivity)
        _ = U^(5:ℕ) * (32000 * Cn * B * Wt * X) := by ring
        _ ≤ (243 * L^(5:ℕ)) * (32000 * Cn * B * Wt * X) :=
            mul_le_mul_of_nonneg_right hU5 (by positivity)
        _ = (7776000 * Cn * L) * (B * Wt * L^(4:ℕ) * X) := by ring
        _ ≤ (7776000 * Cn * L) * (12 * N^(2:ℕ)) :=
            mul_le_mul_of_nonneg_left hWB (by positivity)
        _ = 93312000 * Cn * N^(2:ℕ) * L := by ring
    have hB1 : 2 * T2 ≤ 93312000 * Cn * N^(2:ℕ) * L / X := by
      rw [le_div_iff₀ hXpos]
      exact hB1'
    have hB2 : 93312000 * Cn * N^(2:ℕ) * L / X ≤ (C0/2) * Z := by
      rw [div_le_iff₀ hXpos]
      have ht : (1:ℝ) ≤ (Pz⁻¹ + X⁻¹) * X := by
        have h1 : (Pz⁻¹ + X⁻¹) * X = Pz⁻¹ * X + 1 := by field_simp
        have h2 : 0 ≤ Pz⁻¹ * X := by positivity
        linarith only [h1.le, h1.ge, h2]
      have hCn' : 186624000 * Cn ≤ C0 * ((Pz⁻¹ + X⁻¹) * X) := by
        calc 186624000 * Cn ≤ C0 := hCnC0
          _ = C0 * 1 := by ring
          _ ≤ C0 * ((Pz⁻¹ + X⁻¹) * X) := mul_le_mul_of_nonneg_left ht hC0nn
      rw [hZdef]
      calc 93312000 * Cn * N^(2:ℕ) * L
          = (186624000 * Cn) * (N^(2:ℕ) * L / 2) := by ring
        _ ≤ (C0 * ((Pz⁻¹ + X⁻¹) * X)) * (N^(2:ℕ) * L / 2) :=
            mul_le_mul_of_nonneg_right hCn' (by positivity)
        _ = (C0/2) * ((Pz⁻¹ + X⁻¹) * N^(2:ℕ) * L) * X := by ring
    linarith only [hB1, hB2]
  -- ===== term 3 =====
  have hC : 2 * T3 ≤ (C0/256) * Z := by
    have hC1 : 2 * T3 ≤ 32 * Cc * N^(2:ℕ) / X := by
      rw [hT3def, ← hUdef]
      have hU15 : U^(15:ℕ) * X / Pz ≤ 1 / X := by
        rw [div_le_iff₀ hPz0]
        rw [show (1/X) * Pz = Pz/X by ring]
        rw [le_div_iff₀ hXpos]
        nlinarith only [hPzU]
      calc 2 * (16 * U * (Cc * N^(2:ℕ) * U^(14:ℕ) * X / Pz))
          = (U^(15:ℕ) * X / Pz) * (32 * Cc * N^(2:ℕ)) := by ring
        _ ≤ (1/X) * (32 * Cc * N^(2:ℕ)) := mul_le_mul_of_nonneg_right hU15 (by positivity)
        _ = 32 * Cc * N^(2:ℕ) / X := by ring
    have hC2 : 32 * Cc * N^(2:ℕ) / X ≤ (C0/256) * Z := by
      rw [div_le_iff₀ hXpos]
      have ht : (1:ℝ) ≤ (Pz⁻¹ + X⁻¹) * L * X := by
        have h1 : (Pz⁻¹ + X⁻¹) * L * X = Pz⁻¹ * L * X + L := by field_simp
        have h2 : 0 ≤ Pz⁻¹ * L * X := by positivity
        linarith only [h1.le, h1.ge, h2, hL]
      have hCc' : 8192 * Cc ≤ C0 * ((Pz⁻¹ + X⁻¹) * L * X) := by
        calc 8192 * Cc ≤ C0 := hCcC0
          _ = C0 * 1 := by ring
          _ ≤ C0 * ((Pz⁻¹ + X⁻¹) * L * X) := mul_le_mul_of_nonneg_left ht hC0nn
      rw [hZdef]
      calc 32 * Cc * N^(2:ℕ)
          = (8192 * Cc) * (N^(2:ℕ) / 256) := by ring
        _ ≤ (C0 * ((Pz⁻¹ + X⁻¹) * L * X)) * (N^(2:ℕ) / 256) :=
            mul_le_mul_of_nonneg_right hCc' (by positivity)
        _ = (C0/256) * ((Pz⁻¹ + X⁻¹) * N^(2:ℕ) * L) * X := by ring
    linarith only [hC1, hC2]
  -- ===== term 4 =====
  have hD : 2 * T4 ≤ (C0/256) * Z := by
    have hD1 : 2 * T4 ≤ 486000 * Cf * N^(2:ℕ) * L / X^(2:ℕ) := by
      rw [hT4def, ← hUdef]
      calc 2 * (Cf * Sq * N * U / X^(2:ℕ))
          = Sq * ((2 * Cf * N * U) / X^(2:ℕ)) := by ring
        _ ≤ (81000 * N) * ((2 * Cf * N * U) / X^(2:ℕ)) :=
            mul_le_mul_of_nonneg_right hSq81 (by positivity)
        _ = U * ((162000 * Cf * N^(2:ℕ)) / X^(2:ℕ)) := by ring
        _ ≤ (3 * L) * ((162000 * Cf * N^(2:ℕ)) / X^(2:ℕ)) :=
            mul_le_mul_of_nonneg_right hUL (by positivity)
        _ = 486000 * Cf * N^(2:ℕ) * L / X^(2:ℕ) := by ring
    have hD2 : 486000 * Cf * N^(2:ℕ) * L / X^(2:ℕ) ≤ (C0/256) * Z := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < X^(2:ℕ))]
      have ht : (1:ℝ) ≤ (Pz⁻¹ + X⁻¹) * X^(2:ℕ) := by
        have h1 : (Pz⁻¹ + X⁻¹) * X^(2:ℕ) = Pz⁻¹ * X^(2:ℕ) + X := by field_simp
        have h2 : 0 ≤ Pz⁻¹ * X^(2:ℕ) := by positivity
        linarith only [h1.le, h1.ge, h2, hX]
      have hCf' : 124416000 * Cf ≤ C0 * ((Pz⁻¹ + X⁻¹) * X^(2:ℕ)) := by
        calc 124416000 * Cf ≤ C0 := hCfC0
          _ = C0 * 1 := by ring
          _ ≤ C0 * ((Pz⁻¹ + X⁻¹) * X^(2:ℕ)) := mul_le_mul_of_nonneg_left ht hC0nn
      rw [hZdef]
      calc 486000 * Cf * N^(2:ℕ) * L
          = (124416000 * Cf) * (N^(2:ℕ) * L / 256) := by ring
        _ ≤ (C0 * ((Pz⁻¹ + X⁻¹) * X^(2:ℕ))) * (N^(2:ℕ) * L / 256) :=
            mul_le_mul_of_nonneg_right hCf' (by positivity)
        _ = (C0/256) * ((Pz⁻¹ + X⁻¹) * N^(2:ℕ) * L) * X^(2:ℕ) := by ring
    linarith only [hD1, hD2]
  -- ===== assembly =====
  have hsum : 2 * T1 + 2 * T2 + 2 * T3 + 2 * T4 ≤ (C0/4 + C0/2 + C0/256 + C0/256) * Z := by
    linarith only [hA, hB, hC, hD]
  have hstep : (C0/4 + C0/2 + C0/256 + C0/256) * Z ≤ C0 * Z := by
    have h1 : (C0/4 + C0/2 + C0/256 + C0/256) = (97/128:ℝ) * C0 := by ring
    rw [h1, mul_assoc]
    exact mul_le_of_le_one_left (mul_nonneg hC0nn hZnn) (by norm_num)
  have hfin : 2 * T1 + 2 * T2 + 2 * T3 + 2 * T4 ≤ C0 * Z := le_trans hsum hstep
  have heq1 : 2 * (T1 + T2 + T3 + T4) = 2 * T1 + 2 * T2 + 2 * T3 + 2 * T4 := by ring
  have heq2 : C0 * (Pz⁻¹ + X⁻¹) * N^(2:ℕ) * L = C0 * Z := by rw [hZdef]; ring
  rw [heq1, heq2]
  exact hfin

end Work.FIArea6.S16ErrTwo
