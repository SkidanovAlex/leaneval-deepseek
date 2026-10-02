import Mathlib
import Submission.Work.PARIMPL2.Direct.oidDefs
import Submission.Work.PARIMPL2.Direct.oidCg_sum
import Submission.Work.PARIMPL2.Direct.orbitCrossBound
import Submission.Work.PARIMPL2.Direct.oidArcNegCotOneStep
import Submission.Work.PARIMPL2.Direct.oidArcNegCotTail

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 12000000

namespace Work.PARIMPL2.Direct

open Real

/-! ## Elementary auxiliary estimates -/

/-- For `0 < y ≤ x`, `x * (exp (b y) - 1) ≤ y * (exp (b x) - 1)`: the function
`x ↦ (exp (b x) - 1)/x` is non-decreasing.  Proved from convexity of `exp`. -/
theorem oidArcNeg_exp_ratio {b x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) :
    x * (Real.exp (b * y) - 1) ≤ y * (Real.exp (b * x) - 1) := by
  have hx : 0 < x := lt_of_lt_of_le hy hxy
  set t : ℝ := y / x with ht
  have ht0 : 0 < t := div_pos hy hx
  have ht1 : t ≤ 1 := (div_le_one hx).mpr hxy
  have htx : t * x = y := by rw [ht]; field_simp
  have hexp : Real.exp (b * y) ≤ 1 - t + t * Real.exp (b * x) := by
    have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (b * x))
      (by linarith : (0:ℝ) ≤ 1 - t) (le_of_lt ht0) (by ring : (1 - t) + t = 1)
    simpa [smul_eq_mul, htx, mul_comm, mul_left_comm, mul_assoc] using h
  have h1 : Real.exp (b * y) - 1 ≤ t * (Real.exp (b * x) - 1) := by linarith
  calc x * (Real.exp (b * y) - 1) ≤ x * (t * (Real.exp (b * x) - 1)) :=
        mul_le_mul_of_nonneg_left h1 hx.le
    _ = y * (Real.exp (b * x) - 1) := by rw [← htx]; ring

/-- `Real.log R ≤ R/128 + 4` for `R ≥ 128`. -/
theorem oidArcNeg_log_le (R : ℝ) (hR : 128 ≤ R) : Real.log R ≤ R / 128 + 4 := by
  have h1 : 0 < R / 128 := by positivity
  have h2 : Real.log (R / 128) ≤ R / 128 - 1 := Real.log_le_sub_one_of_pos h1
  have h3 : Real.log R = Real.log 128 + Real.log (R / 128) := by
    rw [← Real.log_mul (by norm_num : (128:ℝ) ≠ 0) (by positivity : R / 128 ≠ 0)]
    congr 1; ring
  have h4 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128:ℝ) = 2^7 by norm_num, Real.log_pow]; norm_num
  have h5 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  rw [h3, h4]; linarith

/-- For `3 ≤ a` and `a ≤ s`, `log s / s ≤ log a / a`. -/
theorem oidArcNeg_log_div_mono {a s : ℝ} (ha : 3 ≤ a) (hs : a ≤ s) :
    Real.log s / s ≤ Real.log a / a := by
  have hapos : 0 < a := by linarith
  have hspos : 0 < s := lt_of_lt_of_le hapos hs
  have hsp : 0 < s / a := div_pos hspos hapos
  have hsplit : Real.log s = Real.log a + Real.log (s / a) := by
    rw [← Real.log_mul (ne_of_gt hapos) (ne_of_gt hsp)]; congr 1; field_simp
  have hle : Real.log (s / a) ≤ s / a - 1 := Real.log_le_sub_one_of_pos hsp
  have hlog : 1 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le hapos]; linarith [Real.exp_one_lt_three]
  have key : Real.log s / s - Real.log a / a ≤ 0 := by
    have h1 : Real.log s / s ≤ (Real.log a + (s / a - 1)) / s := by
      rw [hsplit]; exact div_le_div_of_nonneg_right (by linarith) hspos.le
    have h2 : (Real.log a + (s / a - 1)) / s ≤ Real.log a / a := by
      rw [div_le_div_iff₀ hspos hapos]
      have h3 : (Real.log a + (s / a - 1)) * a = Real.log a * a + s - a := by field_simp; ring
      rw [h3]
      have hprod : (Real.log a - 1) * (a - s) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      nlinarith [hprod]
    linarith
  linarith

/-- For `0 < lam ≤ 1/R²` with `R ≥ 128`: `lam * log (1/lam) ≤ log (R^2)/R^2`. -/
theorem oidArcNeg_lam_log (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) :
    lam * Real.log (1 / lam) ≤ Real.log (R ^ 2) / R ^ 2 := by
  have hRpos : (0:ℝ) < R := by linarith
  have hR2pos : (0:ℝ) < R ^ 2 := by positivity
  have hR2gt : (3:ℝ) ≤ R ^ 2 := by nlinarith
  have hs : R ^ 2 ≤ 1 / lam := by
    rw [le_div_iff₀ hlam]; linarith [hlamR]
  have h := oidArcNeg_log_div_mono hR2gt hs
  have he : lam * Real.log (1 / lam) = Real.log (1 / lam) / (1 / lam) := by
    field_simp
  rw [he]; exact h

/-- `exp (3/8) ≤ 3/2`. -/
theorem oidArcNeg_exp_three_eighths : Real.exp (3/8) ≤ 3/2 := by
  have hhalf : Real.exp (1/2) = Real.sqrt (Real.exp 1) := Real.exp_half 1
  have he1 : Real.exp 1 ≤ 2.7225 := by linarith [Real.exp_one_lt_d9]
  have hsqrt3 : Real.sqrt (Real.exp 1) ≤ 1.65 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith
  have heighth : (1:ℝ) + 1/8 ≤ Real.exp (1/8) := by
    have := Real.add_one_le_exp (1/8 : ℝ); linarith
  have hsplit : Real.exp (3/8) = Real.exp (1/2) / Real.exp (1/8) := by
    rw [← Real.exp_sub]; norm_num
  rw [hsplit, div_le_iff₀ (Real.exp_pos _)]
  nlinarith [hsqrt3, heighth]

/-- For `0 ≤ x`, `6 * (exp (2x) - 1) ≤ exp (12x) - 1`. -/
theorem oidArcNeg_six_mul_le (x : ℝ) (hx : 0 ≤ x) :
    6 * (Real.exp (2*x) - 1) ≤ Real.exp (12*x) - 1 := by
  have h1 : (1:ℝ) ≤ Real.exp (2*x) := Real.one_le_exp (by linarith)
  have he : Real.exp (12*x) = (Real.exp (2*x))^6 := by
    have h : Real.exp (12*x) = Real.exp (2*x) ^ 6 := by
      have := Real.exp_nat_mul (2*x) 6
      rw [show ((6:ℕ):ℝ) * (2*x) = 12*x by ring] at this
      exact this
    exact h
  have hgeom : (∑ k ∈ Finset.range 6, (Real.exp (2*x))^k) * (Real.exp (2*x) - 1)
      = (Real.exp (2*x))^6 - 1 := geom_sum_mul _ _
  have hsum : (6:ℝ) ≤ ∑ k ∈ Finset.range 6, (Real.exp (2*x))^k := by
    have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range 6) => one_le_pow₀ h1 (n := k))
    simpa using h
  have h2 : 0 ≤ Real.exp (2*x) - 1 := by linarith
  have := mul_le_mul_of_nonneg_right hsum h2
  rw [hgeom] at this
  linarith [this]

/-- Final arithmetic: `(60/14) * (exp (14x) - 1) ≤ 8 * (exp (12x) - 1)` for `0 ≤ x ≤ 3/16`. -/
theorem oidArcNeg_arith (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 3/16) :
    (60/14) * (Real.exp (14*x) - 1) ≤ 8 * (Real.exp (12*x) - 1) := by
  have h2x : Real.exp (2*x) ≤ 3/2 := by
    have h : 2*x ≤ 3/8 := by linarith
    exact le_trans (Real.exp_le_exp.mpr h) oidArcNeg_exp_three_eighths
  have h6 := oidArcNeg_six_mul_le x hx0
  have h12 : 0 ≤ Real.exp (12*x) - 1 := by
    have : (0:ℝ) ≤ 12*x := by linarith
    linarith [Real.one_le_exp this]
  have h2n : 0 ≤ Real.exp (2*x) - 1 := by
    have : (0:ℝ) ≤ 2*x := by linarith
    linarith [Real.one_le_exp this]
  have h14 : Real.exp (14*x) - 1
      = Real.exp (2*x) * (Real.exp (12*x) - 1) + (Real.exp (2*x) - 1) := by
    have : Real.exp (2*x) * Real.exp (12*x) = Real.exp (14*x) := by
      rw [← Real.exp_add]; ring_nf
    rw [← this]; ring
  have hstep : Real.exp (14*x) - 1
      ≤ (3/2)*(Real.exp (12*x) - 1) + (Real.exp (12*x) - 1)/6 := by
    rw [h14]
    have h1 : Real.exp (2*x)*(Real.exp (12*x) - 1) ≤ (3/2)*(Real.exp (12*x) - 1) :=
      mul_le_mul_of_nonneg_right h2x h12
    have h2 : Real.exp (2*x) - 1 ≤ (Real.exp (12*x) - 1)/6 := by
      rw [le_div_iff₀ (by norm_num)]; linarith [h6]
    linarith
  have h30 : (60:ℝ)/14 = 30/7 := by norm_num
  rw [h30]
  have hmain : (30/7)*(Real.exp (14*x) - 1) ≤ (50/7)*(Real.exp (12*x) - 1) := by
    have h := mul_le_mul_of_nonneg_left hstep (by norm_num : (0:ℝ) ≤ 30/7)
    have heq : (30/7)*((3/2)*(Real.exp (12*x) - 1) + (Real.exp (12*x) - 1)/6)
        = (50/7)*(Real.exp (12*x) - 1) := by ring
    linarith [h, heq.le, heq.ge]
  have hfin : (50/7)*(Real.exp (12*x) - 1) ≤ 8*(Real.exp (12*x) - 1) := by
    have h : (50:ℝ)/7 ≤ 8 := by norm_num
    exact mul_le_mul_of_nonneg_right h h12
  linarith [hmain, hfin]


/-! ## The two quantitative bounds for the negative arc -/

/-- Basic consequences of the window/decay hypotheses. -/
theorem oidArcNeg_setup (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (n j0 : ℕ) (x : ℕ → ℝ) (hj0 : j0 ≤ n)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3) :
    (∀ j ≤ n, 0 < Real.sin (lam * x j)) ∧
    (∀ j ≤ n, lam * x j < Real.pi) ∧
    (∀ j ≤ n, lam * R / 4 ≤ Real.pi - lam * x j) ∧
    (∀ j < n, lam * R / 4 ≤ Real.pi - lam * x (j + 1)) ∧
    (∀ j < n, (Real.pi - lam * x j) + lam / 3 ≤ Real.pi - lam * x (j + 1)) := by
  have hRpos : (0:ℝ) < R := by linarith
  have hxpos : ∀ j ≤ n, 0 < x j := fun j hj => by have := hx1 j hj; linarith
  have hlam_div : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by
    field_simp
  have hltpi : ∀ j ≤ n, lam * x j < Real.pi := fun j hj => by
    have h2 : lam * x j ≤ lam * (Real.pi / lam - R / 4) :=
      mul_le_mul_of_nonneg_left (hx2 j hj) hlam.le
    rw [hlam_div] at h2
    have : 0 < lam * R / 4 := by positivity
    linarith
  have hge : ∀ j ≤ n, lam * R / 4 ≤ Real.pi - lam * x j := fun j hj => by
    have h2 : lam * x j ≤ lam * (Real.pi / lam - R / 4) :=
      mul_le_mul_of_nonneg_left (hx2 j hj) hlam.le
    rw [hlam_div] at h2
    linarith
  refine ⟨?_, hltpi, hge, ?_, ?_⟩
  · intro j hj
    exact Real.sin_pos_of_pos_of_lt_pi (mul_pos hlam (hxpos j hj)) (hltpi j hj)
  · intro j hj
    have h2 : lam * x (j + 1) ≤ lam * (Real.pi / lam - R / 4) :=
      mul_le_mul_of_nonneg_left (hx2 (j+1) (by omega)) hlam.le
    rw [hlam_div] at h2
    linarith
  · intro j hj
    have h2 : lam * x (j + 1) ≤ lam * (x j - 1 / 3) :=
      mul_le_mul_of_nonneg_left (hdec j hj) hlam.le
    have h3 : lam * (x j - 1 / 3) = lam * x j - lam / 3 := by ring
    linarith [h2, h3.le, h3.ge]

/-- Uniform bound on `lam^2 / sin^2 (lam x_j)` inside the window. -/
theorem oidArcNeg_lam_sin_sq_le (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (n : ℕ) (x : ℕ → ℝ) (j : ℕ) (hj : j ≤ n)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4) :
    lam ^ 2 / (Real.sin (lam * x j)) ^ 2 ≤ 4 * Real.pi ^ 2 / R ^ 2 := by
  have hRpos : (0:ℝ) < R := by linarith
  have hR2pos : (0:ℝ) < R ^ 2 := by positivity
  have hxpos : 0 < x j := by have := hx1 j hj; linarith
  have ht0 : 0 < lam * x j := mul_pos hlam hxpos
  have hpi4 : 0 < lam * R / 4 := by positivity
  have hlam_div : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by field_simp
  have htpi : lam * x j < Real.pi := by
    have h2 : lam * x j ≤ lam * (Real.pi / lam - R / 4) :=
      mul_le_mul_of_nonneg_left (hx2 j hj) hlam.le
    rw [hlam_div] at h2
    linarith
  have htge : lam * R / 4 ≤ lam * x j := by
    have h := hx1 j hj
    have : lam * (R / 4 + 2) ≤ lam * x j := mul_le_mul_of_nonneg_left (by linarith) hlam.le
    nlinarith [this]
  have htle : lam * x j ≤ Real.pi - lam * R / 4 := by
    have h2 : lam * x j ≤ lam * (Real.pi / lam - R / 4) :=
      mul_le_mul_of_nonneg_left (hx2 j hj) hlam.le
    rw [hlam_div] at h2
    exact h2
  have hR4le : lam * R / 4 ≤ Real.pi / 2 := by
    have hlR : lam * R ≤ 1 / R := by
      rw [le_div_iff₀ hRpos]; nlinarith [hlamR]
    nlinarith [hlR, hR, Real.pi_gt_three]
  have hsin_ge : Real.sin (lam * R / 4) ≤ Real.sin (lam * x j) := by
    rcases le_total (lam * x j) (Real.pi / 2) with h | h
    · exact Real.monotoneOn_sin ⟨by linarith [Real.pi_pos], by linarith [hpi4, Real.pi_pos]⟩
        ⟨by linarith [Real.pi_pos], h⟩ htge
    · have hpt_le : Real.pi - lam * x j ≤ Real.pi / 2 := by linarith
      have hpt_ge : lam * R / 4 ≤ Real.pi - lam * x j := by linarith [htle]
      have h2 : Real.sin (lam * R / 4) ≤ Real.sin (Real.pi - lam * x j) :=
        Real.monotoneOn_sin ⟨by linarith [Real.pi_pos], by linarith [hpi4, Real.pi_pos]⟩
          ⟨by linarith [Real.pi_pos, hpi4], hpt_le⟩ hpt_ge
      rwa [Real.sin_pi_sub] at h2
  have hsinR4 : (2 / Real.pi) * (lam * R / 4) ≤ Real.sin (lam * R / 4) :=
    Real.mul_le_sin (le_of_lt hpi4) hR4le
  have hsinpos : 0 < Real.sin (lam * x j) := Real.sin_pos_of_pos_of_lt_pi ht0 htpi
  have hbase : lam * R / (2 * Real.pi) = (2 / Real.pi) * (lam * R / 4) := by ring
  have h1 : lam * R / (2 * Real.pi) ≤ Real.sin (lam * x j) := by
    rw [hbase]; exact le_trans hsinR4 hsin_ge
  have hbpos : 0 < lam * R / (2 * Real.pi) := by positivity
  have hkey : (lam * R / (2 * Real.pi)) ^ 2 ≤ (Real.sin (lam * x j)) ^ 2 :=
    pow_le_pow_left₀ hbpos.le h1 2
  have heq : lam ^ 2 * R ^ 2 ≤ 4 * Real.pi ^ 2 * (Real.sin (lam * x j)) ^ 2 := by
    have : 4 * Real.pi ^ 2 * (lam * R / (2 * Real.pi)) ^ 2 = lam ^ 2 * R ^ 2 := by
      field_simp; ring
    nlinarith [hkey, this]
  rw [div_le_div_iff₀ (pow_pos hsinpos 2) hR2pos]
  linarith [heq]


/-- Telescoping bound for `∑ 1/sin²` over the negative arc, with the endpoint term
`1/sin²(u j0)` kept only when the arc overshoots `π/2`. -/
theorem oidArcNeg_sin_sq_tel (lam : ℝ) (hlam : 0 < lam) (j0 : ℕ) (u : ℕ → ℝ)
    (hu_pos : ∀ j < j0, 0 < u j)
    (hu_le : ∀ j < j0, u j ≤ Real.pi / 2)
    (hu_step : ∀ j < j0, u j + lam / 3 ≤ u (j + 1))
    (hu0 : 0 < u j0) :
    ∀ j < j0, ∑ i ∈ Finset.Ico (j + 1) (j0 + 1), 1 / (Real.sin (u i)) ^ 2
      ≤ (3 / lam) * (Real.cos (u j) / Real.sin (u j))
        + (if u j0 ≤ Real.pi / 2 then 0 else 1 / (Real.sin (u j0)) ^ 2) := by
  have hpos' : ∀ j ≤ j0, 0 < u j := by
    intro j hj
    rcases lt_or_eq_of_le hj with h | h
    · exact hu_pos j h
    · rw [h]; exact hu0
  -- telescoping over an `Ico` interval, requiring `u ≤ π/2` up to `b`
  have tel : ∀ a b, a ≤ b → b ≤ j0 → (∀ k ≤ b, u k ≤ Real.pi / 2) →
      ∑ i ∈ Finset.Ico (a + 1) (b + 1), 1 / (Real.sin (u i)) ^ 2
        ≤ (3 / lam) * (Real.cos (u a) / Real.sin (u a) - Real.cos (u b) / Real.sin (u b)) := by
    intro a b hab hb hle'
    have key : ∀ i ∈ Finset.Ico a b,
        1 / (Real.sin (u (i + 1))) ^ 2
          ≤ (3 / lam) * (Real.cos (u i) / Real.sin (u i) - Real.cos (u (i+1)) / Real.sin (u (i+1))) := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
      have hiN : i < j0 := lt_of_lt_of_le hi2 hb
      have := one_div_sin_sq_le_cot_diff (u i) (u (i + 1)) (lam / 3) (by positivity)
        (hpos' i (le_trans (le_of_lt hi2) hb)) (hu_step i hiN) (hle' (i + 1) (by omega))
      rwa [show (1:ℝ) / (lam / 3) = 3 / lam by field_simp] at this
    have hshift : ∑ i ∈ Finset.Ico a b, 1 / Real.sin (u (i + 1)) ^ 2
        = ∑ i ∈ Finset.Ico (a + 1) (b + 1), 1 / Real.sin (u i) ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      have h1 : b - a = (b + 1) - (a + 1) := by omega
      rw [← h1]
      apply Finset.sum_congr rfl
      intro k _
      have h : (a + k) + 1 = a + 1 + k := by omega
      rw [h]
    rw [← hshift]
    calc ∑ i ∈ Finset.Ico a b, 1 / (Real.sin (u (i + 1))) ^ 2
        ≤ ∑ i ∈ Finset.Ico a b, (3 / lam) * (Real.cos (u i) / Real.sin (u i) - Real.cos (u (i+1)) / Real.sin (u (i+1))) :=
          Finset.sum_le_sum key
      _ = (3 / lam) * ∑ i ∈ Finset.Ico a b, (Real.cos (u i) / Real.sin (u i) - Real.cos (u (i+1)) / Real.sin (u (i+1))) := by
          rw [Finset.mul_sum]
      _ = (3 / lam) * (Real.cos (u a) / Real.sin (u a) - Real.cos (u b) / Real.sin (u b)) := by
          congr 1
          rw [Finset.sum_sub_distrib]
          have h := Finset.sum_Ico_sub (fun i => Real.cos (u i) / Real.sin (u i)) hab
          rw [Finset.sum_sub_distrib] at h
          linarith [h]
  intro j hj
  have hj0pos : 1 ≤ j0 := by omega
  by_cases hcase : u j0 ≤ Real.pi / 2
  · rw [if_pos hcase]
    have hle' : ∀ k ≤ j0, u k ≤ Real.pi / 2 := by
      intro k hk
      rcases lt_or_eq_of_le hk with h | h
      · exact hu_le k h
      · rw [h]; exact hcase
    have h := tel j j0 (le_of_lt hj) le_rfl hle'
    have hcm : 0 ≤ Real.cos (u j0) / Real.sin (u j0) := by
      apply div_nonneg
      · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hu0, Real.pi_pos], hcase⟩
      · exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [hcase, Real.pi_pos]))
    have h3 : (0:ℝ) < 3 / lam := by positivity
    nlinarith [h, hcm, h3]
  · rw [if_neg hcase]
    have hsplit : ∑ i ∈ Finset.Ico (j + 1) (j0 + 1), 1 / (Real.sin (u i)) ^ 2
        = (∑ i ∈ Finset.Ico (j + 1) j0, 1 / (Real.sin (u i)) ^ 2)
          + 1 / (Real.sin (u j0)) ^ 2 := by
      rw [Finset.sum_Ico_succ_top (by omega : j + 1 ≤ j0)]
    rw [hsplit]
    have hsub : j0 - 1 + 1 = j0 := Nat.sub_add_cancel hj0pos
    have hle' : ∀ k ≤ j0 - 1, u k ≤ Real.pi / 2 := by
      intro k hk; exact hu_le k (by omega)
    have h := tel j (j0 - 1) (by omega) (by omega) hle'
    rw [hsub] at h
    have hcm : 0 ≤ Real.cos (u (j0 - 1)) / Real.sin (u (j0 - 1)) := by
      apply div_nonneg
      · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hu_pos (j0-1) (by omega), Real.pi_pos],
          hu_le (j0-1) (by omega)⟩
      · exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi (hu_pos (j0-1) (by omega))
          (by linarith [hu_le (j0-1) (by omega), Real.pi_pos]))
    have h3 : (0:ℝ) < 3 / lam := by positivity
    have hnn : 0 ≤ 1 / (Real.sin (u j0)) ^ 2 := by positivity
    nlinarith [h, hcm, h3, hnn]


/-- Bound for `∑_{i=1}^{j0} (lam^2 + lam^2/ocDen i)`. -/
theorem oidArcNeg_T0_bound (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (n j0 : ℕ) (x y : ℕ → ℝ) (hj0 : j0 ≤ n) (hj0pos : 1 ≤ j0)
    (hneg : ∀ j < j0, Real.pi / 2 < lam * x j)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hDpos : ∀ j ≤ n, 0 < ocDen lam x y j) :
    ∑ i ∈ Finset.Ico 1 (j0 + 1), (lam ^ 2 + lam ^ 2 / ocDen lam x y i) ≤ 14 / R := by
  obtain ⟨hsinpos, hltpi, hge, hge1, hstep⟩ :=
    oidArcNeg_setup lam R hlam hR hlamR n j0 x hj0 hx1 hx2 hdec
  have hRpos : (0:ℝ) < R := by linarith
  have hR2pos : (0:ℝ) < R ^ 2 := by positivity
  have hnlam2 : (n:ℝ) * lam ^ 2 ≤ 1/R := oidCg_n_lam2_le lam R hlam hR hlamR n x hx1 hx2 hdec
  have hj0lam2 : (j0:ℝ) * lam ^ 2 ≤ 1/R := by
    have hle : (j0:ℝ) ≤ (n:ℝ) := Nat.cast_le.mpr hj0
    nlinarith [hnlam2]
  set u : ℕ → ℝ := fun j => Real.pi - lam * x j with hu
  have hsinu : ∀ j, Real.sin (u j) = Real.sin (lam * x j) := fun j => by
    simp only [hu]; exact Real.sin_pi_sub (lam * x j)
  have hu_pos : ∀ j < j0, 0 < u j := fun j hj => by
    simp only [hu]; have := hltpi j (le_trans (le_of_lt hj) hj0); linarith
  have hu_le : ∀ j < j0, u j ≤ Real.pi / 2 := fun j hj => by
    simp only [hu]; have := hneg j hj; linarith
  have hu_step : ∀ j < j0, u j + lam/3 ≤ u (j+1) := fun j hj => by
    have := hstep j (lt_of_lt_of_le hj hj0); simpa only [hu] using this
  have hu0 : 0 < u j0 := by simp only [hu]; have := hltpi j0 hj0; linarith
  have hge0 : lam * R / 4 ≤ u 0 := by simpa only [hu] using hge 0 (Nat.zero_le n)
  have htel := oidArcNeg_sin_sq_tel lam hlam j0 u hu_pos hu_le hu_step hu0 0 hj0pos
  -- `lam * cot (u 0) ≤ 4/R`
  have hu0pos : 0 < u 0 := hu_pos 0 hj0pos
  have hsin0pos : 0 < Real.sin (u 0) := Real.sin_pos_of_pos_of_lt_pi hu0pos
    (by linarith [hu_le 0 hj0pos, Real.pi_pos])
  have hcot0_le : Real.cos (u 0) / Real.sin (u 0) ≤ 1 / u 0 := by
    rw [div_le_div_iff₀ hsin0pos hu0pos]
    have h := mul_cos_le_sin_of_le (u 0) hu0pos.le (hu_le 0 hj0pos)
    linarith [h]
  have hlamcot : 3 * (lam * (Real.cos (u 0) / Real.sin (u 0))) ≤ 12 / R := by
    have hlamcot' : lam * (Real.cos (u 0) / Real.sin (u 0)) ≤ 4 / R := by
      have h2 : lam * (1/u 0) ≤ 4/R := by
        have he : lam * (1/u 0) = lam / u 0 := by ring
        rw [he, div_le_div_iff₀ hu0pos hRpos]
        nlinarith [hge0]
      nlinarith [hcot0_le, hlam.le, h2]
    have h3 : 3 * (4/R) = 12/R := by ring
    linarith [hlamcot', h3]
  -- `0 < u i` and `0 < sin (u i)` for `1 ≤ i ≤ j0`
  have hu_pos' : ∀ i ≤ j0, 0 < u i := by
    intro i hi
    rcases lt_or_eq_of_le hi with h | h
    · exact hu_pos i h
    · rw [h]; exact hu0
  have husin_pos : ∀ i ≤ j0, 0 < Real.sin (u i) := by
    intro i hi
    refine Real.sin_pos_of_pos_of_lt_pi (hu_pos' i hi) ?_
    simp only [hu]
    have h1 : 0 < lam * x i := mul_pos hlam (by have := hx1 i (le_trans hi hj0); linarith)
    linarith
  have hden : ∑ i ∈ Finset.Ico 1 (j0+1), lam^2/ocDen lam x y i
      ≤ lam^2 * ∑ i ∈ Finset.Ico 1 (j0+1), 1/(Real.sin (u i))^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
    have hi0 : i ≤ j0 := by omega
    have hsinp : 0 < Real.sin (u i) := husin_pos i hi0
    have hocs : (Real.sin (u i))^2 ≤ ocDen lam x y i := by
      rw [ocDen, ← hsinu i]
      nlinarith [sq_nonneg (Real.sinh (lam * y i))]
    have hDi : 0 < ocDen lam x y i := hDpos i (le_trans hi0 hj0)
    rw [mul_one_div, div_le_div_iff₀ hDi (pow_pos hsinp 2)]
    nlinarith [hocs, sq_nonneg lam]
  -- `lam^2 * (if …) ≤ 4π²/R²`
  have hKb : lam^2 * (if u j0 ≤ Real.pi/2 then 0 else 1/(Real.sin (u j0))^2) ≤ 4*Real.pi^2/R^2 := by
    by_cases hc : u j0 ≤ Real.pi/2
    · rw [if_pos hc]; simp only [mul_zero]; positivity
    · rw [if_neg hc, hsinu j0, mul_one_div]
      exact oidArcNeg_lam_sin_sq_le lam R hlam hR hlamR n x j0 hj0 hx1 hx2
  have hmain : ∑ i ∈ Finset.Ico 1 (j0+1), lam^2/ocDen lam x y i
      ≤ 3 * (lam * (Real.cos (u 0)/Real.sin (u 0)))
        + lam^2 * (if u j0 ≤ Real.pi/2 then 0 else 1/(Real.sin (u j0))^2) := by
    have h2 : lam^2 * ∑ i ∈ Finset.Ico 1 (j0+1), 1/(Real.sin (u i))^2
        ≤ lam^2 * ((3/lam)*(Real.cos (u 0)/Real.sin (u 0))
            + (if u j0 ≤ Real.pi/2 then 0 else 1/(Real.sin (u j0))^2)) :=
      mul_le_mul_of_nonneg_left htel (by positivity)
    have h3 : lam^2 * ((3/lam)*(Real.cos (u 0)/Real.sin (u 0))
            + (if u j0 ≤ Real.pi/2 then 0 else 1/(Real.sin (u j0))^2))
        = 3 * (lam * (Real.cos (u 0)/Real.sin (u 0)))
          + lam^2 * (if u j0 ≤ Real.pi/2 then 0 else 1/(Real.sin (u j0))^2) := by
      field_simp; try ring
    linarith [hden, h2, h3.le, h3.ge]
  have hsplit : ∑ i ∈ Finset.Ico 1 (j0 + 1), (lam ^ 2 + lam ^ 2 / ocDen lam x y i)
      = (j0:ℝ)*lam^2 + ∑ i ∈ Finset.Ico 1 (j0 + 1), lam ^ 2 / ocDen lam x y i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico]
    have hc : j0 + 1 - 1 = j0 := by omega
    rw [hc, nsmul_eq_mul]
  have hpi2 : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hfin : 4*Real.pi^2/R^2 ≤ 1/R := by
    rw [div_le_div_iff₀ hR2pos hRpos]
    nlinarith [hR, hpi2]
  have hB : lam^2 * (if u j0 ≤ Real.pi/2 then 0 else 1/(Real.sin (u j0))^2) ≤ 1/R :=
    le_trans hKb hfin
  rw [hsplit]
  have hchain : (∑ i ∈ Finset.Ico 1 (j0+1), lam^2/ocDen lam x y i) ≤ 13/R := by
    have h1 : 3 * (lam * (Real.cos (u 0)/Real.sin (u 0)))
        + lam^2 * (if u j0 ≤ Real.pi/2 then 0 else 1/(Real.sin (u j0))^2) ≤ 13/R := by
      have h3 : (12:ℝ)/R + 1/R = 13/R := by ring
      linarith [hlamcot, hB, h3]
    linarith [hmain, h1]
  calc (j0:ℝ) * lam^2 + ∑ i ∈ Finset.Ico 1 (j0+1), lam^2/ocDen lam x y i
      ≤ 1/R + 13/R := add_le_add hj0lam2 hchain
    _ = 14/R := by ring


/-- The main weighted-sum estimate on the negative arc. -/
theorem oidArcNeg_sum_bound (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (n j0 : ℕ) (x y : ℕ → ℝ) (hj0 : j0 ≤ n) (hj0pos : 1 ≤ j0)
    (hneg : ∀ j < j0, Real.pi / 2 < lam * x j)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hDpos : ∀ j ≤ n, 0 < ocDen lam x y j)
    (hSn : |∑ j ∈ Finset.range n, ocA lam x y j| ≤ 8 * (1 + Real.log R)) :
    ∑ j ∈ Finset.range j0, |ocA lam x y j| *
        (∑ i ∈ Finset.Ico (j + 1) (j0 + 1), (lam ^ 2 + lam ^ 2 / ocDen lam x y i))
      ≤ 60 / R := by
  obtain ⟨hsinpos, hltpi, hge, hge1, hstep⟩ :=
    oidArcNeg_setup lam R hlam hR hlamR n j0 x hj0 hx1 hx2 hdec
  have hRpos : (0:ℝ) < R := by linarith
  have hR2pos : (0:ℝ) < R ^ 2 := by positivity
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hlam_le1 : lam ≤ 1 := by nlinarith [hlamR, hlam, hR]
  have hlam_leR2 : lam ≤ 1/R^2 := by rw [le_div_iff₀ hR2pos]; linarith [hlamR]
  have hlogR : Real.log R ≤ R/128 + 4 := oidArcNeg_log_le R hR
  have hLnn : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  set u : ℕ → ℝ := fun j => Real.pi - lam * x j with hu
  have hsinu : ∀ j, Real.sin (u j) = Real.sin (lam * x j) := fun j => by
    simp only [hu]; exact Real.sin_pi_sub (lam * x j)
  have hu_pos : ∀ j < j0, 0 < u j := fun j hj => by
    simp only [hu]; have := hltpi j (le_trans (le_of_lt hj) hj0); linarith
  have hu_le : ∀ j < j0, u j ≤ Real.pi/2 := fun j hj => by
    simp only [hu]; have := hneg j hj; linarith
  have hu_lt : ∀ j < j0, u j < Real.pi/2 := fun j hj => by
    simp only [hu]; have := hneg j hj; linarith
  have hu_step : ∀ j < j0, u j + lam/3 ≤ u (j+1) := fun j hj => by
    have := hstep j (lt_of_lt_of_le hj hj0); simpa only [hu] using this
  have hu0 : 0 < u j0 := by simp only [hu]; have := hltpi j0 hj0; linarith
  have hu0lt : u j0 < Real.pi := by simp only [hu]; have := hx1 j0 hj0; nlinarith [hlam]
  have hge0 : lam * R / 4 ≤ u 0 := by simpa only [hu] using hge 0 (Nat.zero_le n)
  have hsinU : ∀ j ≤ j0, 0 < Real.sin (u j) := by
    intro j hj
    rcases lt_or_eq_of_le hj with h | h
    · exact Real.sin_pos_of_pos_of_lt_pi (hu_pos j h) (by linarith [hu_lt j h, Real.pi_pos])
    · rw [h]; exact Real.sin_pos_of_pos_of_lt_pi hu0 hu0lt
  have hcosU : ∀ j < j0, 0 < Real.cos (u j) := fun j hj =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hu_pos j hj, Real.pi_pos], hu_lt j hj⟩
  have hcotnn : ∀ j < j0, 0 ≤ Real.cos (u j)/Real.sin (u j) := fun j hj =>
    div_nonneg (le_of_lt (hcosU j hj)) (le_of_lt (hsinU j (le_of_lt hj)))
  -- ### (A) pointwise bound
  have habs : ∀ j < j0, |ocA lam x y j| ≤ lam * (Real.cos (u j)/Real.sin (u j)) := by
    intro j hj
    have hsinp : 0 < Real.sin (u j) := hsinU j (le_of_lt hj)
    have hcosp : 0 < Real.cos (u j) := hcosU j hj
    have hD : 0 < ocDen lam x y j := hDpos j (le_trans (le_of_lt hj) hj0)
    have hocs : (Real.sin (u j))^2 ≤ ocDen lam x y j := by
      rw [ocDen, ← hsinu j]; nlinarith [sq_nonneg (Real.sinh (lam * y j))]
    have hsin : Real.sin (lam * x j) = Real.sin (u j) := (hsinu j).symm
    have hcos : Real.cos (lam * x j) = -Real.cos (u j) := by
      have h : Real.cos (u j) = -Real.cos (lam * x j) := by simp only [hu, Real.cos_pi_sub]
      linarith
    have hval : |ocA lam x y j| = lam * Real.sin (u j) * Real.cos (u j)/ocDen lam x y j := by
      rw [ocA, abs_div, abs_of_pos hD, hsin, hcos,
        show lam * Real.sin (u j) * (-Real.cos (u j)) = -(lam * Real.sin (u j) * Real.cos (u j)) by ring,
        abs_neg, abs_mul, abs_mul, abs_of_pos hlam, abs_of_pos hsinp, abs_of_pos hcosp]
    rw [hval, show lam * (Real.cos (u j)/Real.sin (u j)) = (lam * Real.cos (u j))/Real.sin (u j) by ring,
      div_le_div_iff₀ hD hsinp]
    have hkey : (lam * Real.cos (u j)) * (Real.sin (u j))^2 ≤ (lam * Real.cos (u j)) * ocDen lam x y j :=
      mul_le_mul_of_nonneg_left hocs (by positivity)
    nlinarith [hkey]
  -- ### (B) the `T` bound
  have hT : ∀ j < j0, (∑ i ∈ Finset.Ico (j+1) (j0+1), (lam^2 + lam^2/ocDen lam x y i))
      ≤ lam^2*(((j0-j:ℕ)):ℝ) + 3*lam*(Real.cos (u j)/Real.sin (u j))
        + lam^2 * (if u j0 ≤ Real.pi/2 then 0 else 1/(Real.sin (u j0))^2) := by
    intro j hj
    have hsplit2 : ∑ i ∈ Finset.Ico (j+1) (j0+1), (lam^2 + lam^2/ocDen lam x y i)
        = lam^2*(((j0-j:ℕ)):ℝ) + ∑ i ∈ Finset.Ico (j+1) (j0+1), lam^2/ocDen lam x y i := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico]
      have hc : j0 + 1 - (j+1) = j0 - j := by omega
      rw [hc, nsmul_eq_mul]; ring
    have hden : ∑ i ∈ Finset.Ico (j+1) (j0+1), lam^2/ocDen lam x y i
        ≤ lam^2 * (∑ i ∈ Finset.Ico (j+1) (j0+1), 1/(Real.sin (u i))^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
      have hi0 : i ≤ j0 := by omega
      have hsinp : 0 < Real.sin (u i) := hsinU i hi0
      have hD : 0 < ocDen lam x y i := hDpos i (le_trans hi0 hj0)
      have hocs : (Real.sin (u i))^2 ≤ ocDen lam x y i := by
        rw [ocDen, ← hsinu i]; nlinarith [sq_nonneg (Real.sinh (lam * y i))]
      have hinv : (ocDen lam x y i)⁻¹ ≤ ((Real.sin (u i))^2)⁻¹ :=
        (inv_le_inv₀ hD (pow_pos hsinp 2)).mpr hocs
      rw [show lam^2/ocDen lam x y i = lam^2 * (ocDen lam x y i)⁻¹ by ring,
        show lam^2 * (1/(Real.sin (u i))^2) = lam^2 * ((Real.sin (u i))^2)⁻¹ by ring]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    have htelj := oidArcNeg_sin_sq_tel lam hlam j0 u hu_pos hu_le hu_step hu0 j hj
    have hsub : lam^2 * (∑ i ∈ Finset.Ico (j+1) (j0+1), 1/(Real.sin (u i))^2)
        ≤ 3*lam*(Real.cos (u j)/Real.sin (u j))
          + lam^2*(if u j0 ≤ Real.pi/2 then 0 else 1/(Real.sin (u j0))^2) := by
      have h1 := mul_le_mul_of_nonneg_left htelj (by positivity : (0:ℝ) ≤ lam^2)
      have h2 : lam^2 * ((3/lam)*(Real.cos (u j)/Real.sin (u j))
            + (if u j0 ≤ Real.pi/2 then 0 else 1/(Real.sin (u j0))^2))
          = 3*lam*(Real.cos (u j)/Real.sin (u j))
            + lam^2*(if u j0 ≤ Real.pi/2 then 0 else 1/(Real.sin (u j0))^2) := by
        field_simp
      linarith [h1, h2.le, h2.ge]
    rw [hsplit2]; linarith [hden, hsub]
  -- ### (C) outer assembly
  set Asum : ℝ := ∑ j ∈ Finset.range j0, |ocA lam x y j| with hAdef
  set Bsum : ℝ := ∑ j ∈ Finset.range j0, |ocA lam x y j| * (Real.cos (u j)/Real.sin (u j)) with hBdef
  set Csum : ℝ := ∑ j ∈ Finset.range j0, |ocA lam x y j| * (((j0-j:ℕ)):ℝ) with hCdef
  set Kb : ℝ := lam^2 * (if u j0 ≤ Real.pi/2 then 0 else 1/(Real.sin (u j0))^2) with hKbdef
  have hAsum_nn : 0 ≤ Asum := by rw [hAdef]; positivity
  have hBsum_nn : 0 ≤ Bsum := by
    rw [hBdef]; apply Finset.sum_nonneg; intro j hj
    exact mul_nonneg (abs_nonneg _) (hcotnn j (Finset.mem_range.mp hj))
  have hPSum : ∑ j ∈ Finset.range j0, |ocA lam x y j| *
        (∑ i ∈ Finset.Ico (j+1) (j0+1), (lam^2 + lam^2/ocDen lam x y i))
      ≤ lam^2*Csum + 3*lam*Bsum + Kb*Asum := by
    have h1 : ∑ j ∈ Finset.range j0, |ocA lam x y j| *
          (∑ i ∈ Finset.Ico (j+1) (j0+1), (lam^2 + lam^2/ocDen lam x y i))
        ≤ ∑ j ∈ Finset.range j0, (lam^2*(|ocA lam x y j| * (((j0-j:ℕ)):ℝ))
            + 3*lam*(|ocA lam x y j| * (Real.cos (u j)/Real.sin (u j)))
            + Kb * |ocA lam x y j|) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjlt : j < j0 := Finset.mem_range.mp hj
      have h := hT j hjlt
      have h2 := mul_le_mul_of_nonneg_left h (abs_nonneg (ocA lam x y j))
      have h3 : |ocA lam x y j| * (lam^2*(((j0-j:ℕ)):ℝ) + 3*lam*(Real.cos (u j)/Real.sin (u j)) + Kb)
          = lam^2*(|ocA lam x y j| * (((j0-j:ℕ)):ℝ))
            + 3*lam*(|ocA lam x y j| * (Real.cos (u j)/Real.sin (u j))) + Kb * |ocA lam x y j| := by
        rw [hKbdef]; ring
      linarith [h2, h3.le, h3.ge]
    have h2 : ∑ j ∈ Finset.range j0, (lam^2*(|ocA lam x y j| * (((j0-j:ℕ)):ℝ))
            + 3*lam*(|ocA lam x y j| * (Real.cos (u j)/Real.sin (u j)))
            + Kb * |ocA lam x y j|)
        = lam^2*Csum + 3*lam*Bsum + Kb*Asum := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hCdef, ← hBdef, ← hAdef]
    linarith [h1, h2.le, h2.ge]
  -- ### (D)
  have hTermA : lam^2 * Csum ≤ 2*Real.pi*lam*Asum := by
    have h1 : Csum ≤ (j0:ℝ) * Asum := by
      rw [hCdef, hAdef, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hle : (((j0-j:ℕ)):ℝ) ≤ (j0:ℝ) := by rw [Nat.cast_le]; omega
      have h2 := mul_le_mul_of_nonneg_right hle (abs_nonneg (ocA lam x y j))
      have h3 : |ocA lam x y j| * (((j0-j:ℕ)):ℝ) = (((j0-j:ℕ)):ℝ) * |ocA lam x y j| := by ring
      linarith [h2, h3.le, h3.ge]
    have hjad : (j0:ℝ) * lam ≤ 2*Real.pi := by
      have htelesc : x (j0-1) ≤ x 0 - (((j0-1:ℕ)):ℝ)/3 := oidCg_telescope x n hdec (j0-1) (by omega)
      have h1' : Real.pi/2 < lam * x (j0-1) := hneg (j0-1) (by omega)
      have h2' : lam * x 0 ≤ Real.pi - lam*R/4 := by
        have h := hx2 0 (Nat.zero_le n)
        have h2'' : lam * x 0 ≤ lam * (Real.pi/lam - R/4) := mul_le_mul_of_nonneg_left h hlam.le
        have h3' : lam * (Real.pi/lam - R/4) = Real.pi - lam*R/4 := by field_simp
        linarith [h2'', h3'.le, h3'.ge]
      have h3 : lam * x (j0-1) ≤ lam * x 0 - lam * (((j0-1:ℕ)):ℝ)/3 := by
        have := mul_le_mul_of_nonneg_left htelesc hlam.le
        have he : lam * (x 0 - (((j0-1:ℕ)):ℝ)/3) = lam * x 0 - lam*(((j0-1:ℕ)):ℝ)/3 := by ring
        linarith [this, he.le, he.ge]
      have h4 : lam * (((j0-1:ℕ)):ℝ)/3 < Real.pi/2 := by nlinarith [h1', h2', h3]
      have h5 : lam * (((j0-1:ℕ)):ℝ) < 3*Real.pi/2 := by linarith
      have h6 : (j0:ℝ) = (((j0-1:ℕ)):ℝ) + 1 := by
        have hj : j0 = (j0-1) + 1 := (Nat.sub_add_cancel hj0pos).symm
        rw [hj]; push_cast; ring
      nlinarith [h5, h6, hlam_le1, Real.pi_gt_three]
    calc lam^2 * Csum ≤ lam^2 * ((j0:ℝ)*Asum) := mul_le_mul_of_nonneg_left h1 (sq_nonneg lam)
      _ = lam * (lam * ((j0:ℝ)*Asum)) := by ring
      _ ≤ lam * (2*Real.pi*Asum) := by
          apply mul_le_mul_of_nonneg_left _ hlam.le
          nlinarith [hjad, hAsum_nn]
      _ = 2*Real.pi*lam*Asum := by ring
  -- ### (E) `Bsum` bound
  have hTermB : 3*lam*Bsum ≤ 36/R + 48/R^2 := by
    have h1 : Bsum ≤ lam * ∑ j ∈ Finset.range j0, (Real.cos (u j)/Real.sin (u j))^2 := by
      rw [hBdef, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hjlt : j < j0 := Finset.mem_range.mp hj
      have h := habs j hjlt
      have hnn := hcotnn j hjlt
      have hsq : Real.cos (u j)/Real.sin (u j) * (Real.cos (u j)/Real.sin (u j))
          = (Real.cos (u j)/Real.sin (u j))^2 := by ring
      nlinarith [h, hnn, hsq]
    have hcotsq : ∑ j ∈ Finset.range j0, (Real.cos (u j)/Real.sin (u j))^2
        ≤ (Real.cos (u 0)/Real.sin (u 0))^2 + (3/lam)*(Real.cos (u 0)/Real.sin (u 0)) := by
      have h1' : ∑ j ∈ Finset.range j0, (Real.cos (u j)/Real.sin (u j))^2
          = (∑ j ∈ Finset.Ico 1 j0, (Real.cos (u j)/Real.sin (u j))^2)
            + (Real.cos (u 0)/Real.sin (u 0))^2 := by
        rw [show j0 = (j0-1)+1 by omega, Finset.sum_range_succ']
        congr 1
        rw [Finset.sum_Ico_eq_sum_range]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.add_comm 1 k]
      have h2' : ∑ j ∈ Finset.Ico 1 j0, (Real.cos (u j)/Real.sin (u j))^2
          ≤ ∑ j ∈ Finset.Ico 1 j0, 1/(Real.sin (u j))^2 := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
        have hjlt : j < j0 := hj2
        have hsinp : 0 < Real.sin (u j) := hsinU j (le_of_lt hjlt)
        have hcos2 : (Real.cos (u j))^2 ≤ 1 := by
          nlinarith [Real.sin_sq_add_cos_sq (u j), sq_nonneg (Real.sin (u j))]
        rw [show (Real.cos (u j)/Real.sin (u j))^2 = (Real.cos (u j))^2/(Real.sin (u j))^2 by ring,
          show 1/(Real.sin (u j))^2 = (1:ℝ)/(Real.sin (u j))^2 by ring,
          div_le_div_iff₀ (pow_pos hsinp 2) (pow_pos hsinp 2)]
        nlinarith [hcos2]
      have h3' : ∑ j ∈ Finset.Ico 1 j0, 1/(Real.sin (u j))^2 ≤ (3/lam)*(Real.cos (u 0)/Real.sin (u 0)) := by
        have hh := oidArcNeg_sin_sq_tel lam hlam j0 u hu_pos hu_le hu_step hu0 0 hj0pos
        have hsplit : ∑ i ∈ Finset.Ico 1 j0, 1/(Real.sin (u i))^2
            = (∑ i ∈ Finset.Ico 1 (j0+1), 1/(Real.sin (u i))^2) - 1/(Real.sin (u j0))^2 := by
          rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ j0)]
          ring
        rw [hsplit]
        have hcm : 0 ≤ Real.cos (u (j0-1))/Real.sin (u (j0-1)) := hcotnn (j0-1) (by omega)
        have hKbnd : (if u j0 ≤ Real.pi/2 then 0 else 1/(Real.sin (u j0))^2) ≤ 1/(Real.sin (u j0))^2 := by
          by_cases hc : u j0 ≤ Real.pi/2
          · rw [if_pos hc]; positivity
          · rw [if_neg hc]
        have h3p : (0:ℝ) < 3/lam := by positivity
        nlinarith [hh, hcm, h3p, hKbnd]
      linarith [h1', h2', h3']
    have h2 : lam * (∑ j ∈ Finset.range j0, (Real.cos (u j)/Real.sin (u j))^2)
        ≤ lam * ((Real.cos (u 0)/Real.sin (u 0))^2 + (3/lam)*(Real.cos (u 0)/Real.sin (u 0))) :=
      mul_le_mul_of_nonneg_left hcotsq hlam.le
    have hc0le : Real.cos (u 0)/Real.sin (u 0) ≤ 1/u 0 := by
      rw [div_le_div_iff₀ (hsinU 0 (by omega)) (hu_pos 0 hj0pos)]
      have h := mul_cos_le_sin_of_le (u 0) (hu_pos 0 hj0pos).le (hu_le 0 hj0pos)
      linarith [h]
    have hlamcot0 : lam * (Real.cos (u 0)/Real.sin (u 0)) ≤ 4/R := by
      have h2' : lam * (1/u 0) ≤ 4/R := by
        have he : lam * (1/u 0) = lam/u 0 := by ring
        rw [he, div_le_div_iff₀ (hu_pos 0 hj0pos) hRpos]
        nlinarith [hge0]
      nlinarith [hc0le, hlam.le, h2']
    have hcotsq0 : lam^2*(Real.cos (u 0)/Real.sin (u 0))^2 ≤ 16/R^2 := by
      have h1' : (Real.cos (u 0)/Real.sin (u 0))^2 ≤ 1/(u 0)^2 := by
        rw [show (Real.cos (u 0)/Real.sin (u 0))^2 = (Real.cos (u 0))^2/(Real.sin (u 0))^2 by ring,
          show 1/(u 0)^2 = (1:ℝ)/(u 0)^2 by ring,
          div_le_div_iff₀ (pow_pos (hsinU 0 (by omega)) 2) (pow_pos (hu_pos 0 hj0pos) 2)]
        have h := mul_cos_le_sin_of_le (u 0) (hu_pos 0 hj0pos).le (hu_le 0 hj0pos)
        have h1'' : (u 0 * Real.cos (u 0))^2 ≤ (Real.sin (u 0))^2 :=
          pow_le_pow_left₀ (mul_nonneg (hu_pos 0 hj0pos).le (hcosU 0 hj0pos).le) h 2
        nlinarith [h1'']
      have h2' : lam^2 * (1/(u 0)^2) ≤ 16/R^2 := by
        rw [show lam^2 * (1/(u 0)^2) = lam^2/(u 0)^2 by ring,
          div_le_div_iff₀ (pow_pos (hu_pos 0 hj0pos) 2) hR2pos]
        have h1'' : (lam*R/4)^2 ≤ (u 0)^2 := pow_le_pow_left₀ (by positivity) hge0 2
        nlinarith [h1'']
      nlinarith [h1', h2', sq_nonneg lam]
    have h3 : Bsum ≤ lam*((Real.cos (u 0)/Real.sin (u 0))^2 + (3/lam)*(Real.cos (u 0)/Real.sin (u 0))) :=
      le_trans h1 h2
    have h4 : 3*lam*Bsum ≤ 3*(lam*(lam*((Real.cos (u 0)/Real.sin (u 0))^2
          + (3/lam)*(Real.cos (u 0)/Real.sin (u 0))))) := by
      nlinarith [h3, hlam]
    have h5 : 3*(lam*(lam*((Real.cos (u 0)/Real.sin (u 0))^2 + (3/lam)*(Real.cos (u 0)/Real.sin (u 0)))))
        = 3*(lam^2*(Real.cos (u 0)/Real.sin (u 0))^2) + 9*(lam*(Real.cos (u 0)/Real.sin (u 0))) := by
      field_simp; ring
    have h6 : 3*(lam^2*(Real.cos (u 0)/Real.sin (u 0))^2)
        + 9*(lam*(Real.cos (u 0)/Real.sin (u 0))) ≤ 48/R^2 + 36/R := by
      have hA2 : 3*(lam^2*(Real.cos (u 0)/Real.sin (u 0))^2) ≤ 48/R^2 := by
        have h := mul_le_mul_of_nonneg_left hcotsq0 (by norm_num : (0:ℝ) ≤ 3)
        have he : (3:ℝ)*(16/R^2) = 48/R^2 := by ring
        linarith [h, he.le, he.ge]
      have hA1 : 9*(lam*(Real.cos (u 0)/Real.sin (u 0))) ≤ 36/R := by
        have h := mul_le_mul_of_nonneg_left hlamcot0 (by norm_num : (0:ℝ) ≤ 9)
        have he : (9:ℝ)*(4/R) = 36/R := by ring
        linarith [h, he.le, he.ge]
      linarith [hA2, hA1]
    linarith [h4, h5.le, h5.ge, h6]
  -- ### (F) tail bound for `P1`
  set v : ℕ → ℝ := fun k => min (lam * x (j0+k)) (Real.pi/2) with hv
  have hP1tail : ∑ j ∈ Finset.Ico j0 n, ocA lam x y j
      ≤ (3*Real.pi/2)*(Real.log (Real.sin (v 0)) - Real.log (Real.sin (v (n-j0)))) := by
    have hvp : ∀ k ≤ n-j0, 0 < v k := by
      intro k hk
      have hk2 : j0 + k ≤ n := by omega
      have hx : R/4+2 ≤ x (j0+k) := hx1 (j0+k) hk2
      rw [hv]
      exact lt_min (mul_pos hlam (by linarith)) (by linarith [Real.pi_pos])
    have hvl : ∀ k ≤ n-j0, v k ≤ Real.pi/2 := by
      intro k hk; rw [hv]; exact min_le_right _ _
    have hvm : ∀ k < n-j0, v (k+1) ≤ v k := by
      intro k hk
      have hklt : j0 + k < n := by omega
      have hd : lam * x (j0+k+1) ≤ lam * (x (j0+k) - 1/3) :=
        mul_le_mul_of_nonneg_left (hdec (j0+k) hklt) hlam.le
      have hd2 : lam * x (j0+k+1) ≤ lam * x (j0+k) := by nlinarith [hd, hlam]
      rw [hv]; exact min_le_min hd2 le_rfl
    have hvc : ∀ k < n-j0, v k = Real.pi/2 ∨ v (k+1) + lam/3 ≤ v k := by
      intro k hk
      by_cases hc : Real.pi/2 ≤ lam * x (j0+k)
      · left; rw [hv]; exact min_eq_right hc
      · right
        have hlt : lam * x (j0+k) < Real.pi/2 := lt_of_not_ge hc
        have hklt : j0 + k < n := by omega
        have hd := hdec (j0+k) hklt
        have hd2 : lam * x (j0+k+1) ≤ lam * x (j0+k) - lam/3 := by
          have := mul_le_mul_of_nonneg_left hd hlam.le; nlinarith [this]
        have h1 : v (k+1) ≤ lam * x (j0 + (k+1)) := by rw [hv]; exact min_le_left _ _
        have h2 : v k = lam * x (j0+k) := by rw [hv]; exact min_eq_left hlt.le
        have h3 : lam * x (j0 + (k+1)) = lam * x (j0+k+1) := by congr 1
        linarith [h1, h2, h3, hd2]
    have htail := oidArcNegCotTail (lam/3) (by positivity) (n-j0) v hvp hvl hvm hvc
    have hP1v : ∑ j ∈ Finset.Ico j0 n, ocA lam x y j
        ≤ lam * ∑ k ∈ Finset.range (n-j0), Real.cos (v k)/Real.sin (v k) := by
      rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hk2 : j0 + k ≤ n := by have := Finset.mem_range.mp hk; omega
      have hsinp : 0 < Real.sin (lam * x (j0+k)) := hsinpos (j0+k) hk2
      have hlt := hltpi (j0+k) hk2
      have hD : 0 < ocDen lam x y (j0+k) := hDpos (j0+k) hk2
      have hocs : (Real.sin (lam * x (j0+k)))^2 ≤ ocDen lam x y (j0+k) := by
        rw [ocDen]; nlinarith [sq_nonneg (Real.sinh (lam * y (j0+k)))]
      have hvk : v k = min (lam * x (j0+k)) (Real.pi/2) := by simp only [hv]
      have hcot : ocA lam x y (j0+k) ≤ lam * (Real.cos (v k)/Real.sin (v k)) := by
        by_cases hc : lam * x (j0+k) ≤ Real.pi/2
        · rw [hvk, min_eq_left hc,
            show lam * (Real.cos (lam * x (j0+k))/Real.sin (lam * x (j0+k)))
              = lam * Real.cos (lam * x (j0+k))/Real.sin (lam * x (j0+k)) by ring,
            ocA, div_le_div_iff₀ hD hsinp]
          have hxpk : 0 < lam * x (j0+k) := mul_pos hlam (by have := hx1 (j0+k) hk2; linarith)
          have hcosnn : 0 ≤ Real.cos (lam * x (j0+k)) :=
            Real.cos_nonneg_of_mem_Icc ⟨by linarith [hxpk, Real.pi_pos], hc⟩
          have hkey : (lam * Real.cos (lam * x (j0+k))) * (Real.sin (lam * x (j0+k)))^2
              ≤ (lam * Real.cos (lam * x (j0+k))) * ocDen lam x y (j0+k) :=
            mul_le_mul_of_nonneg_left hocs (by positivity)
          nlinarith [hkey]
        · rw [hvk, min_eq_right (le_of_lt (lt_of_not_ge hc)), Real.cos_pi_div_two, zero_div]
          have hcosn : Real.cos (lam * x (j0+k)) < 0 :=
            Real.cos_neg_of_pi_div_two_lt_of_lt (lt_of_not_ge hc) (by linarith [hlt, Real.pi_pos])
          rw [ocA, mul_zero]
          refine div_nonpos_of_nonpos_of_nonneg ?_ hD.le
          exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hlam.le hsinp.le) hcosn.le
      linarith [hcot, hlam.le]
    have h1 : lam * ∑ k ∈ Finset.range (n-j0), Real.cos (v k)/Real.sin (v k)
        ≤ lam * ((3/lam) * ((Real.pi/2) * (Real.log (Real.sin (v 0)) - Real.log (Real.sin (v (n-j0)))))) := by
      apply mul_le_mul_of_nonneg_left _ hlam.le
      have h3c : (3/lam) * ((Real.pi/2) * (Real.log (Real.sin (v 0)) - Real.log (Real.sin (v (n-j0)))))
          = ((Real.pi/2) * (Real.log (Real.sin (v 0)) - Real.log (Real.sin (v (n-j0)))))/(lam/3) := by
        field_simp
      rw [h3c, le_div_iff₀ (by positivity : (0:ℝ) < lam/3)]
      rw [mul_comm]
      exact htail
    have h2 : lam * ((3/lam) * ((Real.pi/2) * (Real.log (Real.sin (v 0)) - Real.log (Real.sin (v (n-j0))))))
        = (3*Real.pi/2)*(Real.log (Real.sin (v 0)) - Real.log (Real.sin (v (n-j0)))) := by
      field_simp
    linarith [hP1v, h1, h2.le, h2.ge]
  have hsinvm : (2/Real.pi)*(lam*(R/4+2)) ≤ Real.sin (v (n-j0)) := by
    have hvm_eq : v (n-j0) = min (lam * x n) (Real.pi/2) := by
      have h : j0 + (n - j0) = n := by omega
      simp only [hv, h]
    rw [hvm_eq]
    rcases le_total (lam * x n) (Real.pi/2) with hc | hc
    · rw [min_eq_left hc]
      have hx : R/4+2 ≤ x n := hx1 n le_rfl
      have h1 : lam * (R/4+2) ≤ lam * x n := mul_le_mul_of_nonneg_left hx hlam.le
      have hsin1 : (2/Real.pi)*(lam*x n) ≤ Real.sin (lam*x n) :=
        Real.mul_le_sin (le_of_lt (mul_pos hlam (by linarith))) hc
      have hsin2 : (2/Real.pi)*(lam*(R/4+2)) ≤ (2/Real.pi)*(lam*x n) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith [hsin1, hsin2]
    · rw [min_eq_right hc, Real.sin_pi_div_two]
      have hR3 : lam * (R/4+2) ≤ Real.pi/2 := by
        have h1 : R/4+2 ≤ R := by linarith
        have h2 : lam*(R/4+2) ≤ lam*R := mul_le_mul_of_nonneg_left h1 hlam.le
        have h3 : lam*R ≤ 1/R := by rw [le_div_iff₀ hRpos]; nlinarith [hlamR]
        have h4 : (1:ℝ)/R ≤ Real.pi/2 := by rw [div_le_iff₀ hRpos]; nlinarith [hR, Real.pi_gt_three]
        linarith [h2, h3, h4]
      have hsin1 : (2/Real.pi)*(lam*(R/4+2)) ≤ Real.sin (lam*(R/4+2)) :=
        Real.mul_le_sin (by positivity) hR3
      linarith [hsin1, Real.sin_le_one (lam*(R/4+2))]
  -- ### (G) log bound for the tail
  have hlogvm : - Real.log (Real.sin (v (n-j0))) ≤ Real.log (Real.pi/(2*lam*(R/4+2))) := by
    have hbase : 0 < (2/Real.pi)*(lam*(R/4+2)) := by positivity
    have hlog := Real.log_le_log hbase hsinvm
    have h1 : - Real.log (Real.sin (v (n-j0))) ≤ - Real.log ((2/Real.pi)*(lam*(R/4+2))) := by linarith [hlog]
    have h2 : - Real.log ((2/Real.pi)*(lam*(R/4+2))) = Real.log (Real.pi/(2*lam*(R/4+2))) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    linarith [h1, h2.le, h2.ge]
  have hlamP1 : lam * (∑ j ∈ Finset.Ico j0 n, ocA lam x y j) ≤ 3*Real.pi*Real.log R/R^2 := by
    have h1 : lam * (∑ j ∈ Finset.Ico j0 n, ocA lam x y j)
        ≤ lam * ((3*Real.pi/2)*(Real.log (Real.sin (v 0)) - Real.log (Real.sin (v (n-j0))))) :=
      mul_le_mul_of_nonneg_left hP1tail hlam.le
    have hlogv0 : Real.log (Real.sin (v 0)) ≤ 0 := by
      have hv0pos : 0 < v 0 := by
        have h : j0 + 0 = j0 := by omega
        simp only [hv, h]
        exact lt_min (mul_pos hlam (by have := hx1 j0 hj0; linarith)) (by linarith [Real.pi_pos])
      have hv0le : v 0 ≤ Real.pi/2 := by rw [hv]; exact min_le_right _ _
      have hsinpos : 0 < Real.sin (v 0) := Real.sin_pos_of_pos_of_lt_pi hv0pos (by linarith [Real.pi_pos])
      exact Real.log_nonpos hsinpos.le (Real.sin_le_one _)
    have hlamC : lam * Real.log (Real.pi/(2*lam*(R/4+2))) ≤ Real.log (R^2)/R^2 := by
      have heq : Real.pi/(2*lam*(R/4+2)) = (Real.pi/(2*(R/4+2))) * (1/lam) := by field_simp
      rw [heq, Real.log_mul (by positivity) (by positivity)]
      have hC1 : Real.pi/(2*(R/4+2)) < 1 := by
        rw [div_lt_one (by positivity)]; linarith [Real.pi_lt_four, hR]
      have hC0 : 0 < Real.pi/(2*(R/4+2)) := by positivity
      have hlogC : Real.log (Real.pi/(2*(R/4+2))) ≤ 0 := Real.log_nonpos hC0.le hC1.le
      have h1' : lam * Real.log (Real.pi/(2*(R/4+2))) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam.le hlogC
      have h2' : lam * Real.log (1/lam) ≤ Real.log (R^2)/R^2 := oidArcNeg_lam_log lam R hlam hR hlamR
      nlinarith [h1', h2']
    have h3 : lam * ((3*Real.pi/2)*(Real.log (Real.sin (v 0)) - Real.log (Real.sin (v (n-j0)))))
        ≤ lam * ((3*Real.pi/2)*(0 + Real.log (Real.pi/(2*lam*(R/4+2))))) := by
      apply mul_le_mul_of_nonneg_left _ hlam.le
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 3*Real.pi/2)
      linarith [hlogv0, hlogvm]
    have h4 : lam * ((3*Real.pi/2)*(0 + Real.log (Real.pi/(2*lam*(R/4+2)))))
        = (3*Real.pi/2)*(lam * Real.log (Real.pi/(2*lam*(R/4+2)))) := by ring
    have h5 : lam * ((3*Real.pi/2)*(Real.log (R^2)/R^2)) ≤ 3*Real.pi*Real.log R/R^2 := by
      have hlog2 : Real.log (R^2) = 2*Real.log R := by
        rw [show (R^2:ℝ) = R*R by ring, Real.log_mul hRne hRne]; ring
      have h3 : lam*Real.log R ≤ Real.log R := mul_le_of_le_one_left hLnn hlam_le1
      calc lam * ((3*Real.pi/2)*(Real.log (R^2)/R^2))
          = (3*Real.pi*(lam*Real.log R))/R^2 := by rw [hlog2]; ring
        _ ≤ (3*Real.pi*Real.log R)/R^2 := by
            rw [div_le_div_iff₀ hR2pos hR2pos]
            have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 3*Real.pi)
            nlinarith [h4, hR2pos]
        _ = 3*Real.pi*Real.log R/R^2 := by ring
    have hlog2 : Real.log (R^2) = 2*Real.log R := by
      rw [show (R^2:ℝ) = R*R by ring, Real.log_mul hRne hRne]; ring
    calc lam * (∑ j ∈ Finset.Ico j0 n, ocA lam x y j)
        ≤ lam * ((3*Real.pi/2)*(Real.log (Real.sin (v 0)) - Real.log (Real.sin (v (n-j0))))) := h1
      _ ≤ lam * ((3*Real.pi/2)*(0 + Real.log (Real.pi/(2*lam*(R/4+2))))) := h3
      _ = (3*Real.pi/2)*(lam * Real.log (Real.pi/(2*lam*(R/4+2)))) := h4
      _ ≤ (3*Real.pi/2)*(Real.log (R^2)/R^2) := mul_le_mul_of_nonneg_left hlamC (by positivity)
      _ = 3*Real.pi*Real.log R/R^2 := by rw [hlog2]; ring
  -- ### (H) `Kb` bounds
  have hKb_le : Kb ≤ (Real.pi/2)^2 / (R/4+2)^2 := by
    by_cases hc : u j0 ≤ Real.pi/2
    · rw [hKbdef, if_pos hc]; simp only [mul_zero]
      exact div_nonneg (by positivity) (by positivity)
    · rw [hKbdef, if_neg hc, hsinu j0]
      have hth : lam * x j0 < Real.pi/2 := by simp only [hu] at hc; linarith [hge j0 hj0]
      have hx : R/4+2 ≤ x j0 := hx1 j0 hj0
      have hxpos : 0 < lam * x j0 := mul_pos hlam (by linarith)
      have hsinlb : (2/Real.pi)*(lam*x j0) ≤ Real.sin (lam*x j0) := Real.mul_le_sin hxpos.le hth.le
      have hsinpos : 0 < Real.sin (lam*x j0) := Real.sin_pos_of_pos_of_lt_pi hxpos (by linarith [hltpi j0 hj0])
      rw [show lam^2 * (1 / (Real.sin (lam*x j0))^2) = lam^2/(Real.sin (lam*x j0))^2 by ring,
        div_le_div_iff₀ (pow_pos hsinpos 2) (pow_pos (by linarith : (0:ℝ) < R/4+2) 2)]
      have h2b : (Real.pi/2)*((2/Real.pi)*(lam*x j0)) = lam*x j0 := by field_simp
      have h3b : ((Real.pi/2)*((2/Real.pi)*(lam*x j0)))^2
          ≤ ((Real.pi/2)*(Real.sin (lam*x j0)))^2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hsinlb (by positivity : (0:ℝ) ≤ Real.pi/2)) 2
      rw [h2b, show ((Real.pi/2)*(Real.sin (lam*x j0)))^2
            = (Real.pi/2)^2*(Real.sin (lam*x j0))^2 by ring] at h3b
      have h4b : lam^2*(R/4+2)^2 ≤ (lam*x j0)^2 := by
        have h1b : lam*(R/4+2) ≤ lam*x j0 := mul_le_mul_of_nonneg_left hx hlam.le
        have h2c : (0:ℝ) ≤ lam*(R/4+2) := by positivity
        have h3c := pow_le_pow_left₀ h2c h1b 2
        have he : (lam*(R/4+2))^2 = lam^2*(R/4+2)^2 := by ring
        rwa [he] at h3c
      linarith [h3b, h4b]
  have hKbP1 : Kb * (∑ j ∈ Finset.Ico j0 n, ocA lam x y j) ≤ 3*Real.pi^4/16/(R/4+2)^2 := by
    by_cases hc : u j0 ≤ Real.pi/2
    · rw [hKbdef, if_pos hc]; simp only [mul_zero, zero_mul]
      exact div_nonneg (by positivity) (by positivity)
    · have hth : lam * x j0 < Real.pi/2 := by simp only [hu] at hc; linarith [hge j0 hj0]
      have hx : R/4+2 ≤ x j0 := hx1 j0 hj0
      have hxpos : 0 < x j0 := by linarith
      have hKbv : Kb ≤ (Real.pi/2)^2 / (x j0)^2 := by
        rw [hKbdef, if_neg hc, hsinu j0]
        have hxpos' : 0 < lam * x j0 := mul_pos hlam hxpos
        have hsinlb : (2/Real.pi)*(lam*x j0) ≤ Real.sin (lam*x j0) := Real.mul_le_sin hxpos'.le hth.le
        have hsinpos : 0 < Real.sin (lam*x j0) := Real.sin_pos_of_pos_of_lt_pi hxpos' (by linarith [hltpi j0 hj0])
        rw [show lam^2 * (1/(Real.sin (lam*x j0))^2) = lam^2/(Real.sin (lam*x j0))^2 by ring,
          div_le_div_iff₀ (pow_pos hsinpos 2) (pow_pos hxpos 2)]
        have h2b : (Real.pi/2)*((2/Real.pi)*(lam*x j0)) = lam*x j0 := by field_simp
        have h3b : ((Real.pi/2)*((2/Real.pi)*(lam*x j0)))^2
            ≤ ((Real.pi/2)*(Real.sin (lam*x j0)))^2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hsinlb (by positivity : (0:ℝ) ≤ Real.pi/2)) 2
        rw [h2b, show ((Real.pi/2)*(Real.sin (lam*x j0)))^2
              = (Real.pi/2)^2*(Real.sin (lam*x j0))^2 by ring] at h3b
        have h4b : lam^2*(x j0)^2 = (lam*x j0)^2 := by ring
        linarith [h3b, h4b.le, h4b.ge]
      have hv0' : v 0 = lam * x j0 := by
        have h : j0 + 0 = j0 := by omega
        simp only [hv, h, min_eq_left hth.le]
      have hlogv0' : Real.log (Real.sin (v 0)) ≤ Real.log (lam * x j0) := by
        rw [hv0']
        exact Real.log_le_log (Real.sin_pos_of_pos_of_lt_pi (mul_pos hlam hxpos) (by linarith [hltpi j0 hj0]))
          (Real.sin_le (le_of_lt (mul_pos hlam hxpos)))
      have hlogsum : Real.log (Real.sin (v 0)) - Real.log (Real.sin (v (n-j0)))
          ≤ Real.log (lam * x j0) + Real.log (Real.pi/(2*lam*(R/4+2))) := by linarith [hlogv0', hlogvm]
      have hlogsum2 : Real.log (lam * x j0) + Real.log (Real.pi/(2*lam*(R/4+2)))
          = Real.log (Real.pi * x j0/(2*(R/4+2))) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1; field_simp
      have hP1log : (∑ j ∈ Finset.Ico j0 n, ocA lam x y j)
          ≤ (3*Real.pi/2)*(Real.log (Real.pi * x j0/(2*(R/4+2)))) := by
        have h3p : (0:ℝ) < 3*Real.pi/2 := by positivity
        have h5 := mul_le_mul_of_nonneg_left hlogsum h3p.le
        have h4 := mul_le_mul_of_nonneg_left (le_of_eq hlogsum2) h3p.le
        linarith [hP1tail, h5, h4]
      have hy1 : (1:ℝ) ≤ Real.pi * x j0/(2*(R/4+2)) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith [hx, Real.pi_gt_three]
      have hKbnn : 0 ≤ Kb := by
        rw [hKbdef]
        by_cases hcc : u j0 ≤ Real.pi/2
        · rw [if_pos hcc]; simp
        · rw [if_neg hcc]; positivity
      have hKbP1' : Kb * (∑ j ∈ Finset.Ico j0 n, ocA lam x y j)
          ≤ (Real.pi/2)^2/(x j0)^2 * ((3*Real.pi/2)*(Real.log (Real.pi * x j0/(2*(R/4+2))))) := by
        rcases le_total 0 (∑ j ∈ Finset.Ico j0 n, ocA lam x y j) with hnn | hn
        · exact mul_le_mul hKbv hP1log hnn (by positivity)
        · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hKbnn hn)
            (mul_nonneg (by positivity) (mul_nonneg (by positivity) (Real.log_nonneg hy1)))
      have hlogy : Real.log (Real.pi * x j0/(2*(R/4+2))) ≤ Real.pi * x j0/(2*(R/4+2)) := by
        have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < Real.pi * x j0/(2*(R/4+2)) by positivity)
        linarith
      have hfin1 : (Real.pi/2)^2/(x j0)^2 * ((3*Real.pi/2)*(Real.log (Real.pi * x j0/(2*(R/4+2)))))
          ≤ (Real.pi/2)^2/(x j0)^2 * ((3*Real.pi/2)*(Real.pi * x j0/(2*(R/4+2)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hlogy (by positivity)
      have hfin2 : (Real.pi/2)^2/(x j0)^2 * ((3*Real.pi/2)*(Real.pi * x j0/(2*(R/4+2))))
          = 3*Real.pi^4/16/(x j0 * (R/4+2)) := by field_simp; ring
      rw [hfin2] at hfin1
      have hfin3 : 3*Real.pi^4/16/(x j0 * (R/4+2)) ≤ 3*Real.pi^4/16/(R/4+2)^2 := by
        apply div_le_div_of_nonneg_left (by positivity)
        · positivity
        · nlinarith [hx]
      linarith [hKbP1', hfin1, hfin3]
  have hKb8 : Kb * (8*(1+Real.log R)) ≤ 8*(1+Real.log R)*(Real.pi/2)^2/(R/4+2)^2 := by
    have h1 : Kb * (8*(1+Real.log R)) ≤ ((Real.pi/2)^2/(R/4+2)^2) * (8*(1+Real.log R)) :=
      mul_le_mul_of_nonneg_right hKb_le (by positivity)
    have h2 : ((Real.pi/2)^2/(R/4+2)^2) * (8*(1+Real.log R))
        = 8*(1+Real.log R)*(Real.pi/2)^2/(R/4+2)^2 := by ring
    linarith [h1, h2.le, h2.ge]
  -- ### (I) `Asum ≤ P1 + 8(1+log R)`
  have hAsumP : Asum ≤ (∑ j ∈ Finset.Ico j0 n, ocA lam x y j) + 8*(1+Real.log R) := by
    have hnegs : ∑ j ∈ Finset.range j0, ocA lam x y j = -Asum := by
      rw [hAdef, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < j0 := Finset.mem_range.mp hj
      have hsinp : 0 < Real.sin (u j) := hsinU j (le_of_lt hjlt)
      have hcosp : 0 < Real.cos (u j) := hcosU j hjlt
      have hD : 0 < ocDen lam x y j := hDpos j (le_trans (le_of_lt hjlt) hj0)
      have hsin : Real.sin (lam * x j) = Real.sin (u j) := (hsinu j).symm
      have hcos : Real.cos (lam * x j) = -Real.cos (u j) := by
        have h : Real.cos (u j) = -Real.cos (lam * x j) := by simp only [hu, Real.cos_pi_sub]
        linarith
      have hval : |ocA lam x y j| = lam * Real.sin (u j) * Real.cos (u j)/ocDen lam x y j := by
        rw [ocA, abs_div, abs_of_pos hD, hsin, hcos,
          show lam * Real.sin (u j) * (-Real.cos (u j)) = -(lam * Real.sin (u j) * Real.cos (u j)) by ring,
          abs_neg, abs_mul, abs_mul, abs_of_pos hlam, abs_of_pos hsinp, abs_of_pos hcosp]
      rw [hval, ocA, hsin, hcos,
        show lam * Real.sin (u j) * (-Real.cos (u j)) / ocDen lam x y j
          = -(lam * Real.sin (u j) * Real.cos (u j)/ocDen lam x y j) by ring]
    have hsplit3 : ∑ j ∈ Finset.range n, ocA lam x y j
        = (∑ j ∈ Finset.range j0, ocA lam x y j) + (∑ j ∈ Finset.range (n-j0), ocA lam x y (j0+j)) := by
      rw [← Finset.sum_range_add]
      rw [show j0 + (n - j0) = n by omega]
    have hP1eq2 : (∑ j ∈ Finset.Ico j0 n, ocA lam x y j)
        = ∑ j ∈ Finset.range (n-j0), ocA lam x y (j0+j) :=
      Finset.sum_Ico_eq_sum_range (fun j => ocA lam x y j) j0 n
    have hS := hSn
    rw [hsplit3, hnegs] at hS
    have h2 := (abs_le.mp hS).1
    rw [← hP1eq2] at h2
    linarith
  -- ### (J) final assembly
  have hTermD : 2*Real.pi*lam*Asum
      ≤ 2*Real.pi*(lam*(∑ j ∈ Finset.Ico j0 n, ocA lam x y j) + lam*(8*(1+Real.log R))) := by
    have h1 : lam * Asum ≤ lam * ((∑ j ∈ Finset.Ico j0 n, ocA lam x y j) + 8*(1+Real.log R)) :=
      mul_le_mul_of_nonneg_left hAsumP hlam.le
    have h2 : lam * ((∑ j ∈ Finset.Ico j0 n, ocA lam x y j) + 8*(1+Real.log R))
        = lam*(∑ j ∈ Finset.Ico j0 n, ocA lam x y j) + lam*(8*(1+Real.log R)) := by ring
    nlinarith [h1, h2.le, h2.ge, Real.pi_pos]
  have hl8 : lam * (8*(1+Real.log R)) ≤ 8*(1+Real.log R)/R^2 := by
    have h1 : lam * (8*(1+Real.log R)) ≤ (1/R^2)*(8*(1+Real.log R)) :=
      mul_le_mul_of_nonneg_right hlam_leR2 (mul_nonneg (by norm_num) (by linarith [hLnn]))
    have h2 : (1/R^2)*(8*(1+Real.log R)) = 8*(1+Real.log R)/R^2 := by ring
    linarith [h1, h2.le, h2.ge]
  have hKb_nn : 0 ≤ Kb := by
    rw [hKbdef]
    by_cases hc : u j0 ≤ Real.pi/2
    · rw [if_pos hc]; simp
    · rw [if_neg hc]; positivity
  have h2' : Kb*(∑ j ∈ Finset.Ico j0 n, ocA lam x y j) + Kb*(8*(1+Real.log R))
      ≤ 3*Real.pi^4/16/(R/4+2)^2 + 8*(1+Real.log R)*(Real.pi/2)^2/(R/4+2)^2 := by
    linarith [hKbP1, hKb8]
  have hFin : 2*Real.pi*lam*Asum + Kb*Asum ≤ 24/R - 48/R^2 := by
    have h1 : 2*Real.pi*lam*Asum
        ≤ 2*Real.pi*(3*Real.pi*Real.log R/R^2 + 8*(1+Real.log R)/R^2) := by
      have h2 := mul_le_mul_of_nonneg_left (show lam*(∑ j ∈ Finset.Ico j0 n, ocA lam x y j)
            + lam*(8*(1+Real.log R))
          ≤ 3*Real.pi*Real.log R/R^2 + 8*(1+Real.log R)/R^2 from by linarith [hlamP1, hl8])
        (by positivity : (0:ℝ) ≤ 2*Real.pi)
      linarith [hTermD, h2]
    have h2 : Kb*Asum ≤ 3*Real.pi^4/16/(R/4+2)^2 + 8*(1+Real.log R)*(Real.pi/2)^2/(R/4+2)^2 := by
      have h3 : Asum ≤ (∑ j ∈ Finset.Ico j0 n, ocA lam x y j) + 8*(1+Real.log R) := hAsumP
      have h4 := mul_le_mul_of_nonneg_left h3 hKb_nn
      have h5 : Kb*((∑ j ∈ Finset.Ico j0 n, ocA lam x y j) + 8*(1+Real.log R))
          = Kb*(∑ j ∈ Finset.Ico j0 n, ocA lam x y j) + Kb*(8*(1+Real.log R)) := by ring
      linarith [h4, h5.le, h5.ge, h2']
    have h3 : 2*Real.pi*(3*Real.pi*Real.log R/R^2 + 8*(1+Real.log R)/R^2)
        + (3*Real.pi^4/16/(R/4+2)^2 + 8*(1+Real.log R)*(Real.pi/2)^2/(R/4+2)^2)
        ≤ 24/R - 48/R^2 := by
      have hb1 : 2*Real.pi*(3*Real.pi*Real.log R/R^2) ≤ 6*Real.pi^2*(R/128+4)/R^2 := by
        have he : 2*Real.pi*(3*Real.pi*Real.log R/R^2) = 6*Real.pi^2*Real.log R/R^2 := by ring
        rw [he]; apply div_le_div_of_nonneg_right _ hR2pos.le; nlinarith [hlogR]
      have hb2 : 2*Real.pi*(8*(1+Real.log R)/R^2) ≤ 16*Real.pi*(R/128+5)/R^2 := by
        have he : 2*Real.pi*(8*(1+Real.log R)/R^2) = 16*Real.pi*(1+Real.log R)/R^2 := by ring
        rw [he]; apply div_le_div_of_nonneg_right _ hR2pos.le; nlinarith [hlogR]
      have hb4 : 8*(1+Real.log R)*(Real.pi/2)^2/(R/4+2)^2
          ≤ 8*(R/128+5)*(Real.pi/2)^2/(R/4+2)^2 := by
        apply div_le_div_of_nonneg_right _ (by positivity); nlinarith [hlogR, Real.pi_pos]
      have hR4ge : R^2/16 ≤ (R/4+2)^2 := by nlinarith
      have hb3 : 3*Real.pi^4/16/(R/4+2)^2 ≤ 3*Real.pi^4/R^2 := by
        rw [div_le_div_iff₀ (by positivity) hR2pos]
        have h1 : 3*Real.pi^4/16 * R^2 = 3*Real.pi^4 * (R^2/16) := by ring
        have h2 : 3*Real.pi^4 * (R^2/16) ≤ 3*Real.pi^4 * (R/4+2)^2 :=
          mul_le_mul_of_nonneg_left hR4ge (by positivity)
        linarith [h1.le, h1.ge, h2]
      have hb5 : 8*(R/128+5)*(Real.pi/2)^2/(R/4+2)^2 ≤ (R+640)*(Real.pi/2)^2/R^2 := by
        have he : 8*(R/128+5) = (R+640)/16 := by ring
        rw [he, div_le_div_iff₀ (by positivity) hR2pos]
        nlinarith [hR4ge, Real.pi_pos, hR]
      have hsum : 6*Real.pi^2*(R/128+4)/R^2 + 16*Real.pi*(R/128+5)/R^2
          + 3*Real.pi^4/R^2 + (R+640)*(Real.pi/2)^2/R^2 ≤ 24/R - 48/R^2 := by
        rw [div_sub_div _ _ hRne hR2pos.ne']
        rw [show (24*R^2 - R*48)/(R*R^2) = (24*R - 48)/R^2 by field_simp]
        rw [show 6*Real.pi^2*(R/128+4)/R^2 + 16*Real.pi*(R/128+5)/R^2
              + 3*Real.pi^4/R^2 + (R+640)*(Real.pi/2)^2/R^2
            = (6*Real.pi^2*(R/128+4) + 16*Real.pi*(R/128+5) + 3*Real.pi^4
                + (R+640)*(Real.pi/2)^2)/R^2 by ring]
        rw [div_le_div_iff₀ hR2pos hR2pos]
        have hpi1 : Real.pi < 3.15 := by linarith [Real.pi_lt_d20]
        have hpi2 : Real.pi^2 < 10 := by nlinarith [Real.pi_lt_d20, Real.pi_pos]
        have hpi4 : Real.pi^4 < 100 := by nlinarith [hpi2, Real.pi_pos]
        have hA1 : 6*Real.pi^2*(R/128+4) ≤ (0.47*R + 240:ℝ) := by nlinarith [hpi2, hR, Real.pi_pos]
        have hA2 : 16*Real.pi*(R/128+5) ≤ (0.4*R + 252:ℝ) := by nlinarith [hpi1, hR, Real.pi_pos]
        have hA3 : 3*Real.pi^4 ≤ (300:ℝ) := by nlinarith [hpi4]
        have hA4 : (R+640)*(Real.pi/2)^2 ≤ (2.5*R + 1600:ℝ) := by nlinarith [hpi2, hR, Real.pi_pos]
        have hA : 6*Real.pi^2*(R/128+4) + 16*Real.pi*(R/128+5) + 3*Real.pi^4
            + (R+640)*(Real.pi/2)^2 ≤ 4*R + 2400 := by linarith [hA1, hA2, hA3, hA4]
        have hB : (4*R+2400)*R^2 ≤ (24*R-48)*R^2 := by nlinarith [hR]
        nlinarith [hA, hB, sq_nonneg R, hR2pos]
      linarith [hb1, hb2, hb3, hb5, hsum]
    linarith [h1, h2, h3]
  have hfinal : lam^2*Csum + 3*lam*Bsum + Kb*Asum ≤ 60/R := by
    calc lam^2*Csum + 3*lam*Bsum + Kb*Asum
        ≤ 2*Real.pi*lam*Asum + (36/R + 48/R^2) + Kb*Asum := by linarith [hTermA, hTermB]
      _ = (2*Real.pi*lam*Asum + Kb*Asum) + (36/R + 48/R^2) := by ring
      _ ≤ (24/R - 48/R^2) + (36/R + 48/R^2) := by linarith [hFin]
      _ = 60/R := by ring
  linarith [hPSum, hfinal]


/-- **Mandelbar, negative arc.**  Weighted sum of `|ocA|` against the exponential of the
partial sums of `oidCg` on the negative arc `j < j0`. -/
theorem oidArcNeg (lam R cp : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (hcp : 0 ≤ cp) (hcpR : cp ≤ 3 * R / 16)
    (n j0 : ℕ) (x y : ℕ → ℝ) (hj0 : j0 ≤ n)
    (hneg : ∀ j < j0, Real.pi / 2 < lam * x j)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hDpos : ∀ j ≤ n, 0 < Work.PARIMPL2.Direct.ocDen lam x y j)
    (hSn : |∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j| ≤ 8 * (1 + Real.log R)) :
    ∑ j ∈ Finset.range j0, |Work.PARIMPL2.Direct.ocA lam x y j| *
      (Real.exp (∑ i ∈ Finset.Ico (j + 1) (j0 + 1), Work.PARIMPL2.Direct.oidCg lam cp x y i) - 1)
      ≤ 8 * (Real.exp (12 * cp / R) - 1) := by
  have hRpos : (0:ℝ) < R := by linarith
  have hcpnn : 0 ≤ cp := hcp
  rcases Nat.eq_zero_or_pos j0 with h0 | hpos
  · subst h0
    rw [Finset.range_zero, Finset.sum_empty]
    have h1 : (1:ℝ) ≤ Real.exp (12*cp/R) := Real.one_le_exp (by positivity)
    linarith
  · set T : ℕ → ℝ := fun j => ∑ i ∈ Finset.Ico (j+1) (j0+1), (lam^2 + lam^2/ocDen lam x y i) with hTdef
    have hEeq : ∀ j, (∑ i ∈ Finset.Ico (j+1) (j0+1), oidCg lam cp x y i) = cp * T j := by
      intro j
      rw [hTdef, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [oidCg]
    have hTjnn : ∀ j, 0 ≤ T j := by
      intro j
      rw [hTdef]
      apply Finset.sum_nonneg
      intro i hi
      have hD := hDpos i (by have := (Finset.mem_Ico.mp hi).2; omega)
      positivity
    have hT0pos : 0 < T 0 := by
      rw [hTdef]
      apply Finset.sum_pos'
      · intro i hi
        have hD := hDpos i (by have := (Finset.mem_Ico.mp hi).2; omega)
        positivity
      · refine ⟨1, Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩, ?_⟩
        have hD := hDpos 1 (by omega)
        positivity
    have hT0le : T 0 ≤ 14/R := by
      rw [hTdef]
      exact oidArcNeg_T0_bound lam R hlam hR hlamR n j0 x y hj0 hpos hneg hx1 hx2 hdec hDpos
    have hS := oidArcNeg_sum_bound lam R hlam hR hlamR n j0 x y hj0 hpos hneg hx1 hx2 hdec hDpos hSn
    -- monotone comparison of the exponential weights
    have hstep : T 0 * (∑ j ∈ Finset.range j0, |ocA lam x y j| * (Real.exp (cp*T j) - 1))
        ≤ (Real.exp (cp*T 0) - 1) * (∑ j ∈ Finset.range j0, |ocA lam x y j| * T j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hjlt : j < j0 := Finset.mem_range.mp hj
      have hTjle : T j ≤ T 0 := by
        rw [hTdef]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
          exact Finset.mem_Ico.mpr ⟨by omega, hi2⟩
        · intro i hi1 hi2
          have hD := hDpos i (by have := (Finset.mem_Ico.mp hi1).2; omega)
          positivity
      have hnn := hTjnn j
      rcases eq_or_lt_of_le hnn with h | h
      · rw [← h]; simp
      · have hcmp := oidArcNeg_exp_ratio (b := cp) (x := T 0) (y := T j) h hTjle
        have hkey := mul_le_mul_of_nonneg_left hcmp (abs_nonneg (ocA lam x y j))
        nlinarith [hkey]
    have h1 : T 0 * (∑ j ∈ Finset.range j0, |ocA lam x y j| * (Real.exp (cp*T j) - 1))
        ≤ (Real.exp (cp*T 0) - 1) * (60/R) := by
      have h2 := mul_le_mul_of_nonneg_left hS
        (sub_nonneg.mpr (Real.one_le_exp (by positivity : (0:ℝ) ≤ cp*T 0)))
      linarith [hstep, h2]
    -- bound `exp(cp T 0)` by `exp(14 cp / R)`
    have hratio : Real.exp (cp*T 0) - 1 ≤ T 0 * ((Real.exp (14*cp/R) - 1)/(14/R)) := by
      have h := oidArcNeg_exp_ratio (b := cp) (x := 14/R) (y := T 0) hT0pos hT0le
      rw [show cp*(14/R) = 14*cp/R by ring] at h
      have he : T 0 * ((Real.exp (14*cp/R) - 1)/(14/R))
          = T 0 * (Real.exp (14*cp/R) - 1) / (14/R) := by ring
      rw [he, le_div_iff₀ (by positivity : (0:ℝ) < 14/R), mul_comm]
      exact h
    have hfin : T 0 * (∑ j ∈ Finset.range j0, |ocA lam x y j| * (Real.exp (cp*T j) - 1))
        ≤ T 0 * ((60/14)*(Real.exp (14*cp/R) - 1)) := by
      have h2 : (Real.exp (cp*T 0) - 1) * (60/R)
          ≤ T 0 * ((Real.exp (14*cp/R) - 1)/(14/R)) * (60/R) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      have he : T 0 * ((Real.exp (14*cp/R) - 1)/(14/R)) * (60/R)
          = T 0 * ((60/14)*(Real.exp (14*cp/R) - 1)) := by
        field_simp
      linarith [h1, h2, he.le, he.ge]
    have hmain : (∑ j ∈ Finset.range j0, |ocA lam x y j| * (Real.exp (cp*T j) - 1))
        ≤ (60/14)*(Real.exp (14*cp/R) - 1) :=
      le_of_mul_le_mul_left hfin hT0pos
    have harith : (60/14)*(Real.exp (14*cp/R) - 1) ≤ 8*(Real.exp (12*cp/R) - 1) := by
      have h := oidArcNeg_arith (cp/R) (by positivity) (by rw [div_le_iff₀ hRpos]; linarith [hcpR])
      rw [show 14*(cp/R) = 14*cp/R by ring, show 12*(cp/R) = 12*cp/R by ring] at h
      exact h
    have hgoal_eq : ∑ j ∈ Finset.range j0, |ocA lam x y j| *
        (Real.exp (∑ i ∈ Finset.Ico (j+1) (j0+1), oidCg lam cp x y i) - 1)
        = ∑ j ∈ Finset.range j0, |ocA lam x y j| * (Real.exp (cp*T j) - 1) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hEeq j]
    rw [hgoal_eq]
    linarith [hmain, harith]

end Work.PARIMPL2.Direct
