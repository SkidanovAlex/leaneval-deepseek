import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-! ## Elementary facts about the horospherical coordinates at `ξ ∈ Sph n` -/

/-- A point of the boundary sphere has norm one. -/
lemma dirFar_norm_Sph {ξ : E n} (hξ : ξ ∈ Sph n) : ‖ξ‖ = 1 := by
  simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ

/-- The normalised flat coordinate at `ξ` is orthogonal to `ξ`. -/
lemma dirFar_yc_inner_xi {ξ u : E n} (hξ : ξ ∈ Sph n) : inner ℝ (yc ξ u) ξ = 0 := by
  have h1 : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, dirFar_norm_Sph hξ]; norm_num
  simp only [yc, wc, real_inner_smul_left, inner_sub_left, real_inner_smul_left, h1]
  ring

/-- The `ξ^⊥`-coordinate is the level times the normalised flat coordinate. -/
lemma dirFar_wc_eq_lev_smul_yc {ξ u : E n} (hξ : ξ ∈ Sph n) :
    wc ξ u = lev ξ u • yc ξ u := by
  have hL : lev ξ u ≠ 0 := ne_of_gt (lev_pos ξ hξ u)
  rw [yc, smul_smul, mul_inv_cancel₀ hL, one_smul]

/-- The norm of `u` is the square sum of its `ξ`-coordinate and its (rescaled) flat coordinate:
`‖u‖² = ⟪u,ξ⟫² + (lev ξ u · ‖yc ξ u‖)²`. -/
lemma dirFar_lev_yc_sq {ξ u : E n} (hξ : ξ ∈ Sph n) :
    ‖u‖^2 = (inner ℝ u ξ)^2 + (lev ξ u * ‖yc ξ u‖)^2 := by
  have h := inner_wc hξ u u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have hwn : ‖wc ξ u‖ = lev ξ u * ‖yc ξ u‖ := by
    rw [dirFar_wc_eq_lev_smul_yc hξ, norm_smul, Real.norm_eq_abs, abs_of_pos (lev_pos ξ hξ u)]
  rw [← sq, hwn] at h
  linarith

/-- The reviewer-verified level/flat-coordinate identity
`2 · lev ξ u · ⟪u,ξ⟫ = 1 + (lev ξ u)² (‖yc ξ u‖² - 1)`. -/
lemma dirFar_lev_yc_level {ξ u : E n} (hξ : ξ ∈ Sph n) :
    2 * lev ξ u * inner ℝ u ξ = 1 + (lev ξ u)^2 * (‖yc ξ u‖^2 - 1) := by
  have h := one_add_norm_wc_sq hξ u
  have hwn : ‖wc ξ u‖ = lev ξ u * ‖yc ξ u‖ := by
    rw [dirFar_wc_eq_lev_smul_yc hξ, norm_smul, Real.norm_eq_abs, abs_of_pos (lev_pos ξ hξ u)]
  have ht : tpart u = lev ξ u + inner ℝ u ξ := by rw [lev]; ring
  rw [hwn, ht] at h
  nlinarith [h]

/-! ## The one-variable inequality -/

/-- **The real-variable core.**  For `1 < C`, if `L ≥ 2`, `0 ≤ r ≤ C`, `N > 0` and
`N² = a² + (L r)²`, `2 L a = 1 + L²(r² - 1)`, then `a / N` is bounded away from `1`, uniformly
in `L`, `r`, `a`, `N`.  Taking `q = (C - C⁻¹)/2 + 1` (so that `q > 1`), the witness is
`ε = 1/(4 q²)`.

The two ingredients are `a ≤ q L r` (from the second identity: `1 ≤ L²(2qr - r² + 1)`, which
follows from `r ≤ C` and `2q - C = 2 - C⁻¹ > 0`) and the arithmetic inequality
`q² ≤ (1 - ε)² (q² + 1)`, i.e. `0 ≤ 8 q⁴ - 7 q² + 1`, which holds because `q ≥ 1`. -/
lemma dirFar_arith (C : ℝ) (hC : 1 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (L a r N : ℝ), 2 ≤ L → 0 ≤ r → r ≤ C →
      (N ^ 2 = a ^ 2 + (L * r) ^ 2) → 0 < N →
      (2 * L * a = 1 + L ^ 2 * (r ^ 2 - 1)) → a / N ≤ 1 - ε := by
  have hε0 : 0 < 1 / (4 * ((C - C⁻¹) / 2 + 1) ^ 2) := by
    have h : (0:ℝ) < (C - C⁻¹) / 2 + 1 := by
      have h2 : C⁻¹ < 1 := inv_lt_one_of_one_lt₀ hC; linarith
    positivity
  refine ⟨1 / (4 * ((C - C⁻¹) / 2 + 1) ^ 2), hε0, ?_⟩
  intro L a r N hL hr hrC hN hNpos hkey
  set q : ℝ := (C - C⁻¹) / 2 + 1 with hqdef
  set ε : ℝ := 1 / (4 * q ^ 2) with hεdef
  have hq1 : 1 < q := by
    have h : C⁻¹ < 1 := inv_lt_one_of_one_lt₀ hC
    simp only [hqdef]; linarith
  have hqpos : 0 < q := by linarith
  have hεlt1 : ε < 1 := by
    rw [hεdef, div_lt_one (by positivity)]
    nlinarith [hq1]
  have hqC : 2 * q - C = 2 - C⁻¹ := by simp only [hqdef]; field_simp; ring
  have h2qC : 0 < 2 * q - C := by
    rw [hqC]; have h : C⁻¹ < 1 := inv_lt_one_of_one_lt₀ hC; linarith
  -- Step 1: `a ≤ q (L r)`.
  have hstep1 : a ≤ q * (L * r) := by
    rcases le_or_gt a 0 with ha | ha
    · nlinarith [mul_nonneg hqpos.le (mul_nonneg (by linarith : (0:ℝ) ≤ L) hr)]
    · have hbase : 1 ≤ 2 * q * r - r ^ 2 + 1 := by
        nlinarith [mul_nonneg hr h2qC.le, mul_nonneg hr (by linarith : (0:ℝ) ≤ C - r),
          mul_le_mul_of_nonneg_right hrC hr]
      have hquad : 1 ≤ L ^ 2 * (2 * q * r - r ^ 2 + 1) := by
        have hL2 : 4 ≤ L ^ 2 := by nlinarith
        have h := mul_le_mul hL2 hbase (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ L^2)
        linarith
      nlinarith [hkey, hquad, hL]
  rcases le_or_gt a 0 with ha | ha
  · have h1 : a / N ≤ 0 := div_nonpos_of_nonpos_of_nonneg ha hNpos.le
    linarith
  · have hq2 : (0:ℝ) < q ^ 2 := by positivity
    have hLr3 : a ^ 2 ≤ q ^ 2 * (L * r) ^ 2 := by
      have h1 : 0 ≤ q * (L * r) := mul_nonneg hqpos.le (mul_nonneg (by linarith) hr)
      nlinarith [hstep1, ha.le, h1]
    have hkeyε2 : q ^ 2 ≤ (1 - ε) ^ 2 * (q ^ 2 + 1) := by
      have hq2' : (1:ℝ) ≤ q ^ 2 := by nlinarith [hq1]
      have h8 : 0 ≤ 8 * q ^ 4 - 7 * q ^ 2 + 1 := by nlinarith [sq_nonneg (q^2 - 1), hq2']
      rw [hεdef]
      field_simp
      nlinarith [h8]
    have hsq' : a ^ 2 * q ^ 2 ≤ ((1 - ε) * N) ^ 2 * q ^ 2 := by
      rw [mul_pow, hN]
      nlinarith [hLr3, hkeyε2, ha.le, hq2, sq_nonneg (1 - ε), sq_nonneg (L * r)]
    have hsq : a ^ 2 ≤ ((1 - ε) * N) ^ 2 := (mul_le_mul_iff_of_pos_right hq2).mp hsq'
    have hnn : 0 ≤ (1 - ε) * N := mul_nonneg (by linarith) hNpos.le
    have haN : a ≤ (1 - ε) * N := by
      have h := (sq_le_sq.mp hsq)
      rw [abs_of_nonneg ha.le, abs_of_nonneg hnn] at h
      exact h
    rwa [div_le_iff₀ hNpos]

/-- **A point at a large horospherical level with flat coordinate in a bounded set does not point
towards the cusp.**  If `lev ξ u ≥ L₀` for `L₀` large (in terms of `C`) and `‖yc ξ u‖ ≤ C` with
`1 < C`, then the direction `(‖u‖)⁻¹ • u` is bounded away from `ξ ∈ Sph n`, uniformly in `u`.

Reviewer-verified computation: write `L = lev ξ u`, `y = yc ξ u` (so `y ⊥ ξ`), then
`u = ⟪u,ξ⟫ • ξ + L • y`, `⟪u,ξ⟫ = tpart u - L = (1 + L²(‖y‖² - 1)) / (2L)` and
`‖u‖² = ⟪u,ξ⟫² + L²‖y‖²` (`inner_wc`, `one_add_norm_wc_sq` in `levYcFormula`).  With
`ρ = L ‖y‖ / |⟪u,ξ⟫|` one has `⟪(‖u‖)⁻¹ • u, ξ⟫ = sign(⟪u,ξ⟫) / √(1 + ρ²)`.  If `⟪u,ξ⟫ ≤ 0` this
is `≤ 0`.  If `⟪u,ξ⟫ > 0` then `ρ = 2 L² ‖y‖ / (1 + L²(‖y‖² - 1))`, which for `‖y‖ ≤ C` and
`L ≥ L₀` is bounded below by a positive constant depending only on `C` (split `‖y‖ ≤ 1`, where
`⟪u,ξ⟫ ≤ 1/(2L)` and `ρ ≥ 2L²` for `‖y‖ = 1` while `⟪u,ξ⟫ < 0` for `‖y‖ < 1` and `L > 1`, and
`1 < ‖y‖ ≤ C`, where `1/ρ ≤ (C - 1/C)/2 + 1/(2L₀²C)`).  Hence some `ε > 0` works. -/
theorem dirFarOfLargeLev (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (C : ℝ) (hC : 1 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ L₀ : ℝ, ∀ u : Submission.Mostow.E n, L₀ ≤ Work.Mostow.lev ξ u →
      ‖Work.Mostow.yc ξ u‖ ≤ C →
      inner ℝ ((‖u‖)⁻¹ • u) ξ ≤ 1 - ε := by
  obtain ⟨ε, hεpos, harith⟩ := dirFar_arith C hC
  refine ⟨ε, hεpos, 2, ?_⟩
  intro u hL hrC
  have hN : ‖u‖^2 = (inner ℝ u ξ)^2 + (lev ξ u * ‖yc ξ u‖)^2 := dirFar_lev_yc_sq hξ
  have hkey : 2 * lev ξ u * inner ℝ u ξ = 1 + (lev ξ u)^2 * (‖yc ξ u‖^2 - 1) :=
    dirFar_lev_yc_level hξ
  have hunit : 0 < ‖u‖ := by
    rw [norm_pos_iff]
    intro hu
    have h1 : lev ξ (0 : E n) = 1 := by simp [lev, tpart]
    rw [hu, h1] at hL
    norm_num at hL
  have h := harith (lev ξ u) (inner ℝ u ξ) (‖yc ξ u‖) ‖u‖
    hL (norm_nonneg _) hrC hN hunit hkey
  rw [real_inner_smul_left]
  have h2 : (‖u‖)⁻¹ * inner ℝ u ξ = inner ℝ u ξ / ‖u‖ := by rw [div_eq_mul_inv, mul_comm]
  rw [h2]
  exact h

end Work.Mostow
