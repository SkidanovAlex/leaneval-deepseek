import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.mr_core.badPartAux

/-- `log x ≤ 576 * x^(1/576)` for `x ≥ 0`. -/
theorem lv_log_le_576 (x : ℝ) (hx : 0 ≤ x) :
    Real.log x ≤ 576 * x ^ ((1 : ℝ) / 576) := by
  have h := Real.log_le_rpow_div hx (show (0 : ℝ) < 1 / 576 by norm_num)
  rwa [show x ^ ((1 : ℝ) / 576) / ((1 : ℝ) / 576) = 576 * x ^ ((1 : ℝ) / 576)
        by ring] at h

/-- `l ^ (1/48) * l ^ (1/576) = l ^ (13/576)` for `l > 0`. -/
theorem lv_rpow_mul (l : ℝ) (hl : 0 < l) :
    l ^ ((1 : ℝ) / 48) * l ^ ((1 : ℝ) / 576) = l ^ ((13 : ℝ) / 576) := by
  rw [← Real.rpow_add hl]; norm_num

/-- `l / l ^ (47/48) = l ^ (1/48)` for `l > 0`. -/
theorem lv_div_rpow (l : ℝ) (hl : 0 < l) :
    l / l ^ ((47 : ℝ) / 48) = l ^ ((1 : ℝ) / 48) := by
  have h : (1 : ℝ) - 47 / 48 = 1 / 48 := by norm_num
  rw [← h, Real.rpow_sub hl 1 ((47 : ℝ) / 48), Real.rpow_one]

/-- Analytic core: the exponent appearing in the large-values count bound is
bounded by a constant times `l ^ (13/576)`. -/
theorem largeValue_expBound (l L T : ℝ) (hl : 1 ≤ l) (hL : l ^ ((47 : ℝ) / 48) ≤ 2 * L)
    (hT : 3 ≤ T) (hlogT : Real.log T ≤ 2 * l) :
    200 * Real.log l * Real.log T / L + 200 * Real.log l
      + 2 * (Real.log T / L) * Real.log (Real.log T)
    ≤ 585216 * l ^ ((13 : ℝ) / 576) := by
  have hlpos : 0 < l := lt_of_lt_of_le one_pos hl
  have hl0 : 0 ≤ Real.log l := Real.log_nonneg hl
  have hT1 : 1 ≤ T := by linarith
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith : 1 < T)
  have hhalf : l ^ ((47 : ℝ) / 48) / 2 ≤ L := by linarith
  have hhalfpos : 0 < l ^ ((47 : ℝ) / 48) / 2 := by positivity
  have hLpos : 0 < L := lt_of_lt_of_le hhalfpos hhalf
  have hinvL : 1 / L ≤ 2 / l ^ ((47 : ℝ) / 48) := by
    have h := one_div_le_one_div_of_le hhalfpos hhalf
    rwa [one_div_div] at h
  have hlA : l / l ^ ((47 : ℝ) / 48) = l ^ ((1 : ℝ) / 48) := lv_div_rpow l hlpos
  have hLT : Real.log T / L ≤ 4 * l ^ ((1 : ℝ) / 48) := by
    have h1 : Real.log T / L ≤ 2 * l / L := by
      rw [div_le_div_iff_of_pos_right hLpos]; exact hlogT
    have h3 : l / L ≤ 2 * l ^ ((1 : ℝ) / 48) := by
      calc l / L = l * (1 / L) := by ring
        _ ≤ l * (2 / l ^ ((47 : ℝ) / 48)) := mul_le_mul_of_nonneg_left hinvL hlpos.le
        _ = 2 * (l / l ^ ((47 : ℝ) / 48)) := by ring
        _ = 2 * l ^ ((1 : ℝ) / 48) := by rw [hlA]
    calc Real.log T / L ≤ 2 * l / L := h1
      _ = 2 * (l / L) := by ring
      _ ≤ 2 * (2 * l ^ ((1 : ℝ) / 48)) := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = 4 * l ^ ((1 : ℝ) / 48) := by ring
  have h2l1 : 1 ≤ 2 * l := by linarith
  have h2lpos : 0 < 2 * l := by linarith
  have hloglog : Real.log (Real.log T) ≤ Real.log (2 * l) := Real.log_le_log hlogTpos hlogT
  have hlog2l0 : 0 ≤ Real.log (2 * l) := Real.log_nonneg h2l1
  have hLT0 : 0 ≤ Real.log T / L := div_nonneg hlogT0 hLpos.le
  have ht1 : 200 * Real.log l * Real.log T / L ≤ 800 * l ^ ((1 : ℝ) / 48) * Real.log l := by
    calc 200 * Real.log l * Real.log T / L = 200 * Real.log l * (Real.log T / L) := by ring
      _ ≤ 200 * Real.log l * (4 * l ^ ((1 : ℝ) / 48)) :=
            mul_le_mul_of_nonneg_left hLT (by linarith [hl0] : (0 : ℝ) ≤ 200 * Real.log l)
      _ = 800 * l ^ ((1 : ℝ) / 48) * Real.log l := by ring
  have ht2 : 2 * (Real.log T / L) * Real.log (Real.log T)
      ≤ 8 * l ^ ((1 : ℝ) / 48) * Real.log (2 * l) := by
    have hs1 : 2 * (Real.log T / L) * Real.log (Real.log T)
        ≤ 2 * (Real.log T / L) * Real.log (2 * l) :=
      mul_le_mul_of_nonneg_left hloglog (by linarith [hLT0] : (0 : ℝ) ≤ 2 * (Real.log T / L))
    have hs2 : 2 * (Real.log T / L) * Real.log (2 * l)
        ≤ 2 * (4 * l ^ ((1 : ℝ) / 48)) * Real.log (2 * l) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLT (by norm_num : (0:ℝ) ≤ 2)) hlog2l0
    calc 2 * (Real.log T / L) * Real.log (Real.log T)
          ≤ 2 * (Real.log T / L) * Real.log (2 * l) := hs1
      _ ≤ 2 * (4 * l ^ ((1 : ℝ) / 48)) * Real.log (2 * l) := hs2
      _ = 8 * l ^ ((1 : ℝ) / 48) * Real.log (2 * l) := by ring
  have hlogl : Real.log l ≤ 576 * l ^ ((1 : ℝ) / 576) := lv_log_le_576 l hlpos.le
  have hlog2l : Real.log (2 * l) ≤ 576 * (2 * l) ^ ((1 : ℝ) / 576) :=
    lv_log_le_576 (2 * l) h2lpos.le
  have h2lp : (2 * l) ^ ((1 : ℝ) / 576) ≤ 2 * l ^ ((1 : ℝ) / 576) := by
    have hsplit : (2 * l) ^ ((1 : ℝ) / 576)
        = 2 ^ ((1 : ℝ) / 576) * l ^ ((1 : ℝ) / 576) :=
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hlpos.le
    rw [hsplit]
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / 576) ≤ 2 := by
      have hh := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (y := (1 : ℝ) / 576)
        (z := (1 : ℝ)) (show (1 : ℝ) ≤ 2 by norm_num)
        (show (1 : ℝ) / 576 ≤ 1 by norm_num)
      rw [Real.rpow_one] at hh
      exact hh
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hlpos.le ((1:ℝ)/576))
  have hb1 : 800 * l ^ ((1 : ℝ) / 48) * Real.log l ≤ 460800 * l ^ ((13 : ℝ) / 576) := by
    have h := mul_le_mul_of_nonneg_left hlogl
      (show (0 : ℝ) ≤ 800 * l ^ ((1 : ℝ) / 48) by positivity)
    calc 800 * l ^ ((1 : ℝ) / 48) * Real.log l
        ≤ 800 * l ^ ((1 : ℝ) / 48) * (576 * l ^ ((1 : ℝ) / 576)) := h
      _ = 460800 * (l ^ ((1 : ℝ) / 48) * l ^ ((1 : ℝ) / 576)) := by ring
      _ = 460800 * l ^ ((13 : ℝ) / 576) := by rw [lv_rpow_mul l hlpos]
  have hb2 : 8 * l ^ ((1 : ℝ) / 48) * Real.log (2 * l) ≤ 9216 * l ^ ((13 : ℝ) / 576) := by
    have h := mul_le_mul_of_nonneg_left hlog2l
      (show (0 : ℝ) ≤ 8 * l ^ ((1 : ℝ) / 48) by positivity)
    have h2 := mul_le_mul_of_nonneg_left h2lp (show (0 : ℝ) ≤ 576 by norm_num)
    calc 8 * l ^ ((1 : ℝ) / 48) * Real.log (2 * l)
        ≤ 8 * l ^ ((1 : ℝ) / 48) * (576 * (2 * l) ^ ((1 : ℝ) / 576)) := h
      _ ≤ 8 * l ^ ((1 : ℝ) / 48) * (576 * (2 * l ^ ((1 : ℝ) / 576))) :=
            mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 8 * l ^ ((1 : ℝ) / 48) by positivity)
      _ = 9216 * (l ^ ((1 : ℝ) / 48) * l ^ ((1 : ℝ) / 576)) := by ring
      _ = 9216 * l ^ ((13 : ℝ) / 576) := by rw [lv_rpow_mul l hlpos]
  have hb3 : 200 * Real.log l ≤ 115200 * l ^ ((13 : ℝ) / 576) := by
    have h := mul_le_mul_of_nonneg_left hlogl (show (0 : ℝ) ≤ 200 by norm_num)
    have h13 : l ^ ((1 : ℝ) / 576) ≤ l ^ ((13 : ℝ) / 576) :=
      Real.rpow_le_rpow_of_exponent_le hl (by norm_num)
    nlinarith [h, h13, Real.rpow_nonneg hlpos.le ((13 : ℝ) / 576)]
  have hG : 200 * Real.log l * Real.log T / L + 200 * Real.log l
      + 2 * (Real.log T / L) * Real.log (Real.log T)
      ≤ 800 * l ^ ((1 : ℝ) / 48) * Real.log l + 200 * Real.log l
        + 8 * l ^ ((1 : ℝ) / 48) * Real.log (2 * l) := by
    linarith [ht1, ht2]
  linarith [hG, hb1, hb2, hb3]

/-- Bound for the `T`-power times `V^2` factor. -/
theorem rpowV_exp_bound (l L T V : ℝ) (hl : 1 ≤ l) (hL : 0 < L) (hT : 3 ≤ T)
    (hV1 : 1 ≤ V) (hV : V ≤ l ^ (100 : ℝ)) :
    T ^ (2 * Real.log V / L) * V ^ 2
      ≤ Real.exp (200 * Real.log l * Real.log T / L + 200 * Real.log l) := by
  have hlpos : 0 < l := lt_of_lt_of_le one_pos hl
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hVpos : 0 < V := lt_of_lt_of_le one_pos hV1
  have hlogV : Real.log V ≤ 100 * Real.log l := by
    have h := Real.log_le_log hVpos hV
    rwa [Real.log_rpow hlpos 100] at h
  have hstep1 : 2 * Real.log V / L ≤ 200 * Real.log l / L := by
    rw [div_le_div_iff_of_pos_right hL]
    linarith
  have hTV : T ^ (2 * Real.log V / L) ≤ Real.exp (200 * Real.log l / L * Real.log T) := by
    rw [Real.rpow_def_of_pos hTpos, mul_comm (Real.log T)]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hstep1 hlogT0
  have hV2 : V ^ 2 ≤ Real.exp (200 * Real.log l) := by
    have heq : V ^ 2 = Real.exp (2 * Real.log V) := by
      rw [show (2 : ℝ) * Real.log V = Real.log V + Real.log V by ring, Real.exp_add,
        Real.exp_log hVpos, pow_two]
    rw [heq]
    apply Real.exp_le_exp.mpr
    linarith [hlogV]
  calc T ^ (2 * Real.log V / L) * V ^ 2
      ≤ Real.exp (200 * Real.log l / L * Real.log T) * Real.exp (200 * Real.log l) :=
        mul_le_mul hTV hV2 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (200 * Real.log l * Real.log T / L + 200 * Real.log l) := by
        rw [← Real.exp_add]
        try (congr 1; ring)

/-- Reduction: for `c, C > 0` and all large enough `l` (uniformly in `L`, `T`),
the exponent `G - c L^(1/12)` is at most `- log C`. -/
theorem largeValue_kill (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ l₀ : ℝ, 0 < l₀ ∧
      ∀ l L T : ℝ, l₀ ≤ l → l ^ ((47 : ℝ) / 48) ≤ 2 * L → 3 ≤ T → Real.log T ≤ 2 * l →
        200 * Real.log l * Real.log T / L + 200 * Real.log l
          + 2 * (Real.log T / L) * Real.log (Real.log T) - c * L ^ ((1 : ℝ) / 12)
        ≤ -Real.log C := by
  set cp : ℝ := c * 2 ^ (-(1 / 12 : ℝ)) with hcpdef
  have hcp : 0 < cp := by rw [hcpdef]; positivity
  set D : ℝ := max (Real.log C) 0 with hDdef
  have hD0 : 0 ≤ D := le_max_right _ _
  have hCD : Real.log C ≤ D := le_max_left _ _
  set X : ℝ := (2 * 585216 / cp) ^ ((288 : ℝ) / 17) with hXdef
  set Y : ℝ := (2 * D / cp) ^ ((576 : ℝ) / 47) with hYdef
  have hX0 : 0 ≤ X := by rw [hXdef]; exact Real.rpow_nonneg (div_nonneg (by norm_num) hcp.le) _
  have hY0 : 0 ≤ Y := by rw [hYdef]; exact Real.rpow_nonneg (div_nonneg (mul_nonneg (by norm_num) hD0) hcp.le) _
  have hcp2 : 0 ≤ cp / 2 := div_nonneg hcp.le (by norm_num : (0:ℝ) ≤ 2)
  refine ⟨max 1 (max X Y), lt_of_lt_of_le one_pos (le_max_left 1 (max X Y)), ?_⟩
  intro l L T hl hL hT hlogT
  have hl1 : 1 ≤ l := le_trans (le_max_left 1 (max X Y)) hl
  have hXl : X ≤ l := le_trans (le_max_left X Y) (le_trans (le_max_right 1 (max X Y)) hl)
  have hYl : Y ≤ l := le_trans (le_max_right X Y) (le_trans (le_max_right 1 (max X Y)) hl)
  have hlpos : 0 < l := lt_of_lt_of_le one_pos hl1
  have hb : 0 ≤ 2 * 585216 / cp := div_nonneg (by norm_num) hcp.le
  have hXpow : 2 * 585216 / cp ≤ l ^ ((17 : ℝ) / 288) := by
    have h := Real.rpow_le_rpow hX0 hXl (show (0 : ℝ) ≤ 17 / 288 by norm_num)
    have heq : X ^ ((17 : ℝ) / 288) = 2 * 585216 / cp := by
      rw [hXdef, ← Real.rpow_mul hb ((288 : ℝ) / 17) ((17 : ℝ) / 288)]
      rw [show (288 : ℝ) / 17 * (17 / 288) = 1 by norm_num, Real.rpow_one]
    rwa [heq] at h
  have hkey1 : 585216 ≤ (cp / 2) * l ^ ((17 : ℝ) / 288) := by
    have h := mul_le_mul_of_nonneg_left hXpow hcp2
    have heq : (cp / 2) * (2 * 585216 / cp) = 585216 := by field_simp
    linarith [h, heq]
  have hbD : 0 ≤ 2 * D / cp := div_nonneg (mul_nonneg (by norm_num) hD0) hcp.le
  have hYpow : 2 * D / cp ≤ l ^ ((47 : ℝ) / 576) := by
    have h := Real.rpow_le_rpow hY0 hYl (show (0 : ℝ) ≤ 47 / 576 by norm_num)
    have heq : Y ^ ((47 : ℝ) / 576) = 2 * D / cp := by
      rw [hYdef, ← Real.rpow_mul hbD ((576 : ℝ) / 47) ((47 : ℝ) / 576)]
      rw [show (576 : ℝ) / 47 * (47 / 576) = 1 by norm_num, Real.rpow_one]
    rwa [heq] at h
  have hkey2 : Real.log C ≤ (cp / 2) * l ^ ((47 : ℝ) / 576) := by
    have h := mul_le_mul_of_nonneg_left hYpow hcp2
    have heq : (cp / 2) * (2 * D / cp) = D := by field_simp
    calc Real.log C ≤ D := hCD
      _ = (cp / 2) * (2 * D / cp) := heq.symm
      _ ≤ (cp / 2) * l ^ ((47 : ℝ) / 576) := h
  have hLpos : 0 < L := by
    have h1 : 1 ≤ l ^ ((47 : ℝ) / 48) := Real.one_le_rpow hl1 (by norm_num)
    linarith
  have hhalf : l ^ ((47 : ℝ) / 48) / 2 ≤ L := by linarith
  have hpow : (l ^ ((47 : ℝ) / 48) / 2) ^ ((1 : ℝ) / 12)
      = l ^ ((47 : ℝ) / 576) / 2 ^ ((1 : ℝ) / 12) := by
    rw [Real.div_rpow (Real.rpow_nonneg hlpos.le ((47:ℝ)/48)) (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_mul hlpos.le ((47 : ℝ) / 48) ((1 : ℝ) / 12)]
    norm_num
  have hL12 : l ^ ((47 : ℝ) / 576) / 2 ^ ((1 : ℝ) / 12) ≤ L ^ ((1 : ℝ) / 12) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ l ^ ((47 : ℝ) / 48) / 2) hhalf
      (show (0 : ℝ) ≤ 1 / 12 by norm_num)
    rwa [hpow] at h
  have hkey3 : cp * l ^ ((47 : ℝ) / 576) ≤ c * L ^ ((1 : ℝ) / 12) := by
    have h := mul_le_mul_of_nonneg_left hL12 hc.le
    calc cp * l ^ ((47 : ℝ) / 576)
        = c * (l ^ ((47 : ℝ) / 576) / 2 ^ ((1 : ℝ) / 12)) := by
          rw [hcpdef, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          ring
      _ ≤ c * L ^ ((1 : ℝ) / 12) := h
  have hG := largeValue_expBound l L T hl1 hL hT hlogT
  have hsplit : l ^ ((47 : ℝ) / 576)
      = l ^ ((13 : ℝ) / 576) * l ^ ((17 : ℝ) / 288) := by
    rw [← Real.rpow_add hlpos]; norm_num
  have hK : 585216 * l ^ ((13 : ℝ) / 576) ≤ (cp / 2) * l ^ ((47 : ℝ) / 576) := by
    rw [hsplit]
    have h13n : 0 ≤ l ^ ((13 : ℝ) / 576) := Real.rpow_nonneg hlpos.le _
    nlinarith [hkey1, h13n]
  have hG2 : 200 * Real.log l * Real.log T / L + 200 * Real.log l
      + 2 * (Real.log T / L) * Real.log (Real.log T) ≤ (cp / 2) * l ^ ((47 : ℝ) / 576) :=
    le_trans hG hK
  calc 200 * Real.log l * Real.log T / L + 200 * Real.log l
        + 2 * (Real.log T / L) * Real.log (Real.log T) - c * L ^ ((1 : ℝ) / 12)
      ≤ (cp / 2) * l ^ ((47 : ℝ) / 576) - cp * l ^ ((47 : ℝ) / 576) := by
        linarith [hG2, hkey3]
    _ = -((cp / 2) * l ^ ((47 : ℝ) / 576)) := by ring
    _ ≤ -Real.log C := neg_le_neg hkey2

theorem largeValues_count_bound :
    ∀ (c C : ℝ), 0 < c → 0 < C → ∃ l₀ : ℝ, 0 < l₀ ∧
      ∀ (l T L V : ℝ), 1 ≤ V → V ≤ l ^ (100 : ℝ) → l₀ ≤ l →
        l ^ ((47 : ℝ) / 48) ≤ 2 * L → 3 ≤ T → Real.log T ≤ 2 * l →
        C * T ^ (2 * Real.log V / L) * V ^ 2
            * Real.exp (2 * (Real.log T / L) * Real.log (Real.log T))
            * Real.exp (-c * L ^ ((1 : ℝ) / 12)) ≤ 1 := by
  intro c C hc hC
  obtain ⟨l₀, hl₀pos, hl₀⟩ := largeValue_kill c C hc hC
  refine ⟨max l₀ 1, lt_of_lt_of_le hl₀pos (le_max_left l₀ 1), ?_⟩
  intro l T L V hV1 hV hll hL2 hT hlogT
  have hll' : l₀ ≤ l := le_trans (le_max_left l₀ 1) hll
  have hl1 : 1 ≤ l := le_trans (le_max_right l₀ 1) hll
  have hlpos : 0 < l := lt_of_lt_of_le one_pos hl1
  have hLpos : 0 < L := by
    have h1 : 1 ≤ l ^ ((47 : ℝ) / 48) := Real.one_le_rpow hl1 (by norm_num)
    linarith
  have hBV := rpowV_exp_bound l L T V hl1 hLpos hT hV1 hV
  have hmain : C * (T ^ (2 * Real.log V / L) * V ^ 2)
        * Real.exp (2 * (Real.log T / L) * Real.log (Real.log T))
        * Real.exp (-c * L ^ ((1 : ℝ) / 12))
      ≤ C * Real.exp (200 * Real.log l * Real.log T / L + 200 * Real.log l)
        * Real.exp (2 * (Real.log T / L) * Real.log (Real.log T))
        * Real.exp (-c * L ^ ((1 : ℝ) / 12)) := by
    have h1 : C * (T ^ (2 * Real.log V / L) * V ^ 2)
        ≤ C * Real.exp (200 * Real.log l * Real.log T / L + 200 * Real.log l) :=
      mul_le_mul_of_nonneg_left hBV hC.le
    have h2 := mul_le_mul_of_nonneg_right h1
      (Real.exp_pos (2 * (Real.log T / L) * Real.log (Real.log T))).le
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-c * L ^ ((1 : ℝ) / 12))).le
  have hsum : C * Real.exp (200 * Real.log l * Real.log T / L + 200 * Real.log l)
        * Real.exp (2 * (Real.log T / L) * Real.log (Real.log T))
        * Real.exp (-c * L ^ ((1 : ℝ) / 12))
      = Real.exp (Real.log C + (200 * Real.log l * Real.log T / L + 200 * Real.log l)
          + 2 * (Real.log T / L) * Real.log (Real.log T) + (-c * L ^ ((1 : ℝ) / 12))) := by
    calc C * Real.exp (200 * Real.log l * Real.log T / L + 200 * Real.log l)
          * Real.exp (2 * (Real.log T / L) * Real.log (Real.log T))
          * Real.exp (-c * L ^ ((1 : ℝ) / 12))
        = Real.exp (Real.log C) * Real.exp (200 * Real.log l * Real.log T / L + 200 * Real.log l)
          * Real.exp (2 * (Real.log T / L) * Real.log (Real.log T))
          * Real.exp (-c * L ^ ((1 : ℝ) / 12)) := by rw [Real.exp_log hC]
      _ = Real.exp (Real.log C + (200 * Real.log l * Real.log T / L + 200 * Real.log l)
          + 2 * (Real.log T / L) * Real.log (Real.log T) + (-c * L ^ ((1 : ℝ) / 12))) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          try (congr 1; ring)
  have hle : Real.exp (Real.log C + (200 * Real.log l * Real.log T / L + 200 * Real.log l)
          + 2 * (Real.log T / L) * Real.log (Real.log T) + (-c * L ^ ((1 : ℝ) / 12))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hk := hl₀ l L T hll' hL2 hT hlogT
    linarith [hk]
  calc C * T ^ (2 * Real.log V / L) * V ^ 2
          * Real.exp (2 * (Real.log T / L) * Real.log (Real.log T))
          * Real.exp (-c * L ^ ((1 : ℝ) / 12))
      = C * (T ^ (2 * Real.log V / L) * V ^ 2)
          * Real.exp (2 * (Real.log T / L) * Real.log (Real.log T))
          * Real.exp (-c * L ^ ((1 : ℝ) / 12)) := by ring
    _ ≤ C * Real.exp (200 * Real.log l * Real.log T / L + 200 * Real.log l)
          * Real.exp (2 * (Real.log T / L) * Real.log (Real.log T))
          * Real.exp (-c * L ^ ((1 : ℝ) / 12)) := hmain
    _ = Real.exp (Real.log C + (200 * Real.log l * Real.log T / L + 200 * Real.log l)
          + 2 * (Real.log T / L) * Real.log (Real.log T) + (-c * L ^ ((1 : ℝ) / 12))) := hsum
    _ ≤ 1 := hle

end Work.mr_core.badPartAux
