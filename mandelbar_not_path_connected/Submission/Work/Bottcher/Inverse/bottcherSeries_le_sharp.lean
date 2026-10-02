import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Core.norm_iterate_pMap_ge
import Submission.Work.Bottcher.Contraction.norm_log_normFactor_le
import Submission.Work.Bottcher.Series.summable_bottcherTerm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Sharp `1/‖z‖²` bound for the Böttcher series of the tricorn

`bottcherSeries c z = Σ_n 4^{-(n+1)} log (normFactor c ((pMap c)^[n] z))`, where
`normFactor c w = pMap c w / w^4` and `pMap c w = (w² + c̄)² + c` is the holomorphic
second iterate `T_c ∘ T_c` of the tricorn map.

Because `normFactor c w = 1 + 2c̄/w² + (c̄²+c)/w⁴`, the first order term of the
series is `4^{-1} log (1 + 2c̄/w² + …) = c̄/(2w²) + O(1/w⁴)`; the higher iterates
`p_c^n w` grow at least like `w^{4^n}`, so they contribute `O(1/w⁴)` as well.
Hence for `‖z‖` large

`‖bottcherSeries c z‖ ≤ (‖c‖/2 + 1/4)/‖z‖²`,

the constant `‖c‖/2` being *exact* (it is the modulus of the coefficient `c̄/2` of
the leading term `1/z²`).

The proof splits the series at `n = 0`, estimates the first term by the explicit
expansion of `log (normFactor c z)` and the tail by the geometric majorant
`Σ_{n≥1} 4^{-(n+1)} = 1/12` together with the crude bound
`‖log (normFactor c w)‖ ≤ K/‖w‖²` valid for `‖w‖ ≥ 1` (`K = 2‖c‖ + (‖c‖²+‖c‖)
+ 2(2‖c‖ + ‖c‖²+‖c‖)²`).
-/

open Function Filter
open scoped ComplexConjugate

namespace Work.Bottcher.Inverse

/-! ## The far radius `r = 32 (1 + ‖c‖)^4 + 32` -/

/-- The radius beyond which the sharp bound holds, and beyond which the orbit of
`pMap c` is monotone in norm. -/
noncomputable def sharpRadius (c : ℂ) : ℝ := 32 * (1 + ‖c‖) ^ 4 + 32

theorem sharpRadius_pos (c : ℂ) : 0 < sharpRadius c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [sharpRadius]
  positivity

theorem two_add_le_sharpRadius (c : ℂ) : 2 + ‖c‖ ≤ sharpRadius c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [sharpRadius]
  nlinarith [h, sq_nonneg ‖c‖, pow_nonneg h 2, pow_nonneg h 3, pow_nonneg h 4]

theorem one_le_sharpRadius (c : ℂ) : (1 : ℝ) ≤ sharpRadius c := by
  have h := two_add_le_sharpRadius c
  have h2 : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  linarith

/-! ## Growth of the `pMap c`-orbit outside `sharpRadius c` -/

/-- Outside `sharpRadius c` the quartic `pMap c` at least raises the fourth power
of the norm, and both the norm and `sharpRadius c` itself are non-decreasing. -/
theorem sharpRadius_le_norm_pMap (c w : ℂ) (hw : sharpRadius c ≤ ‖w‖) :
    sharpRadius c ≤ ‖pMap c w‖ ∧ ‖w‖ ≤ ‖pMap c w‖ ∧ ‖w‖ ^ 4 / 2 ≤ ‖pMap c w‖ := by
  have h2 : 2 + ‖c‖ ≤ ‖w‖ := le_trans (two_add_le_sharpRadius c) hw
  obtain ⟨h1, h2', _⟩ := Work.Bottcher.Core.pMap_norm_step c w h2
  have hc : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hw2 : (2 : ℝ) ≤ ‖w‖ := by linarith
  have h4 : ‖w‖ ≤ ‖w‖ ^ 4 / 2 := Work.Bottcher.Core.le_pow_four_div_two hw2
  exact ⟨le_trans (le_trans hw h4) h2', h1, h2'⟩

theorem norm_iterate_pMap_ge_sharp (c z : ℂ) (hz : sharpRadius c ≤ ‖z‖) (n : ℕ) :
    sharpRadius c ≤ ‖(pMap c)^[n] z‖ ∧ ‖z‖ ≤ ‖(pMap c)^[n] z‖ :=
  Work.Bottcher.Core.norm_iterate_pMap_ge c (sharpRadius c)
    (fun w hw => ⟨(sharpRadius_le_norm_pMap c w hw).1,
      (sharpRadius_le_norm_pMap c w hw).2.1⟩) z hz n

/-- For `n ≥ 1` the `n`-th `pMap c`-iterate at least raises the fourth power:
`‖z_n‖ ≥ ‖z‖⁴/2`. -/
theorem pow_four_div_two_le_norm_iterate (c z : ℂ) (hz : sharpRadius c ≤ ‖z‖) {n : ℕ}
    (hn : 1 ≤ n) : ‖z‖ ^ 4 / 2 ≤ ‖(pMap c)^[n] z‖ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Function.iterate_succ_apply]
  exact le_trans (sharpRadius_le_norm_pMap c z hz).2.2
    (norm_iterate_pMap_ge_sharp c (pMap c z) (sharpRadius_le_norm_pMap c z hz).1 m).2

/-! ## The pointwise logarithmic bound and its numerical constant -/

/-- `t(v) = 2‖c‖/v² + (‖c‖²+‖c‖)/v⁴`, the pointwise majorant of
`‖log (normFactor c w)‖` for `‖w‖ = v ≥ sharpRadius c`. -/
noncomputable def sharpT (c : ℂ) (v : ℝ) : ℝ :=
  2 * ‖c‖ / v ^ 2 + (‖c‖ ^ 2 + ‖c‖) / v ^ 4

/-- `K = 2‖c‖ + (‖c‖²+‖c‖) + 2(2‖c‖ + ‖c‖²+‖c‖)²`, the constant with
`t(v) + 2 t(v)² ≤ K/v²` for `v ≥ 1`. -/
noncomputable def sharpK (c : ℂ) : ℝ :=
  2 * ‖c‖ + (‖c‖ ^ 2 + ‖c‖) + 2 * (2 * ‖c‖ + (‖c‖ ^ 2 + ‖c‖)) ^ 2

theorem sharpK_nonneg (c : ℂ) : 0 ≤ sharpK c := by
  rw [sharpK]
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  nlinarith [h, sq_nonneg ‖c‖, sq_nonneg (2 * ‖c‖ + (‖c‖ ^ 2 + ‖c‖))]

theorem norm_log_normFactor_le_sharp (c w : ℂ) (hw : sharpRadius c ≤ ‖w‖) :
    ‖Complex.log (normFactor c w)‖ ≤ sharpT c ‖w‖ + 2 * sharpT c ‖w‖ ^ 2 := by
  have h := Work.Bottcher.Contraction.norm_log_normFactor_le c w (by simpa only [sharpRadius] using hw)
  simpa only [sharpT] using h

theorem sharpT_add_sq_le (A v : ℝ) (hA : 0 ≤ A) (hv : 1 ≤ v) :
    2 * A / v ^ 2 + (A ^ 2 + A) / v ^ 4
        + 2 * (2 * A / v ^ 2 + (A ^ 2 + A) / v ^ 4) ^ 2
      ≤ (2 * A + (A ^ 2 + A) + 2 * (2 * A + (A ^ 2 + A)) ^ 2) / v ^ 2 := by
  have hv2 : 0 < v ^ 2 := by positivity
  have hv2' : (1 : ℝ) ≤ v ^ 2 := by nlinarith
  have hB : 0 ≤ A ^ 2 + A := by nlinarith
  have hu0 : 0 ≤ 2 * A + (A ^ 2 + A) / v ^ 2 := by positivity
  have hu_le : 2 * A + (A ^ 2 + A) / v ^ 2 ≤ 2 * A + (A ^ 2 + A) := by
    have : (A ^ 2 + A) / v ^ 2 ≤ A ^ 2 + A := by
      rw [div_le_iff₀ hv2]; nlinarith [hB, hv2']
    linarith
  have ht : 2 * A / v ^ 2 + (A ^ 2 + A) / v ^ 4
      = (2 * A + (A ^ 2 + A) / v ^ 2) / v ^ 2 := by
    field_simp
  rw [ht]
  have h1 : (2 * A + (A ^ 2 + A) / v ^ 2) / v ^ 2 ≤ (2 * A + (A ^ 2 + A)) / v ^ 2 :=
    div_le_div_of_nonneg_right hu_le hv2.le
  have h2 : ((2 * A + (A ^ 2 + A) / v ^ 2) / v ^ 2) ^ 2
      ≤ ((2 * A + (A ^ 2 + A)) / v ^ 2) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hu0 hv2.le) h1 2
  have h3 : ((2 * A + (A ^ 2 + A)) / v ^ 2) ^ 2 = (2 * A + (A ^ 2 + A)) ^ 2 / v ^ 4 := by
    rw [div_pow]; ring_nf
  have h4 : (2 * A + (A ^ 2 + A)) ^ 2 / v ^ 4 ≤ (2 * A + (A ^ 2 + A)) ^ 2 / v ^ 2 := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) hv2
    nlinarith [hv2']
  have h5 : (2 * A + (A ^ 2 + A) + 2 * (2 * A + (A ^ 2 + A)) ^ 2) / v ^ 2
      = (2 * A + (A ^ 2 + A)) / v ^ 2 + 2 * ((2 * A + (A ^ 2 + A)) ^ 2 / v ^ 2) := by
    ring
  rw [h3] at h2
  rw [h5]
  linarith [h1, h2, h4]

theorem sharpT_add_sq_le' (c : ℂ) {v : ℝ} (hv : 1 ≤ v) :
    sharpT c v + 2 * sharpT c v ^ 2 ≤ sharpK c / v ^ 2 := by
  have h := sharpT_add_sq_le ‖c‖ v (norm_nonneg c) hv
  simpa only [sharpT, sharpK] using h

/-! ## The first term of the series -/

/-- Elementary bound on the remainder of the first term: with `A = ‖c‖` and
`w ≥ 32(1+A)^4+32`,
`(1/4)(t(w) + 2t(w)²) ≤ A/(2w²) + (1/8)/w²`. -/
theorem quarter_sharpT_le (A w : ℝ) (hA : 0 ≤ A) (hw : 32 * (1 + A) ^ 4 + 32 ≤ w) :
    (1 / 4) * (2 * A / w ^ 2 + (A ^ 2 + A) / w ^ 4
        + 2 * (2 * A / w ^ 2 + (A ^ 2 + A) / w ^ 4) ^ 2)
      ≤ A / 2 / w ^ 2 + (1 / 8) / w ^ 2 := by
  set B := A ^ 2 + A with hBdef
  have hB : 0 ≤ B := by rw [hBdef]; nlinarith
  have hA1 : (1 : ℝ) ≤ 1 + A := by linarith
  have hA0 : (0 : ℝ) ≤ 1 + A := by linarith
  have hp8 : (1 : ℝ) ≤ (1 + A) ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hA1 8
    simpa using this
  have hp4 : (1 : ℝ) ≤ (1 + A) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hA1 4
    simpa using this
  have hwpos : 0 < w := by
    have : (0 : ℝ) ≤ (1 + A) ^ 4 := by positivity
    linarith
  have hw2 : 0 < w ^ 2 := by positivity
  have hw2big : 1024 * (1 + A) ^ 8 ≤ w ^ 2 := by
    have h0 : (0 : ℝ) ≤ 32 * (1 + A) ^ 4 := by positivity
    have hw32 : 32 * (1 + A) ^ 4 ≤ w := by linarith
    calc 1024 * (1 + A) ^ 8 = (32 * (1 + A) ^ 4) ^ 2 := by ring
      _ ≤ w ^ 2 := pow_le_pow_left₀ h0 hw32 2
  have hw2one : (1 : ℝ) ≤ w ^ 2 := by linarith [hp8, hw2big]
  set u := 2 * A + B / w ^ 2 with hudef
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  have hu_le : u ≤ 2 * A + B := by
    rw [hudef]
    have hle : B / w ^ 2 ≤ B := by
      rw [div_le_iff₀ hw2]
      nlinarith [hB, hw2one]
    linarith
  have ht : 2 * A / w ^ 2 + B / w ^ 4 = u / w ^ 2 := by
    rw [hudef]; field_simp
  have hBAB : B / 4 + (2 * A + B) ^ 2 / 2 ≤ w ^ 2 / 8 := by
    have h1 : B / 4 + (2 * A + B) ^ 2 / 2 ≤ 9 * (1 + A) ^ 4 := by
      rw [hBdef]
      nlinarith [hA, sq_nonneg A, pow_nonneg hA0 2,
        sq_nonneg (1 + A), pow_nonneg hA0 3, pow_nonneg hA0 4]
    have h2 : 9 * (1 + A) ^ 4 ≤ w ^ 2 / 8 := by
      nlinarith [hw2big, hp4]
    linarith
  have hmain : (1 / 4) * (u / w ^ 2 + 2 * (u / w ^ 2) ^ 2) ≤ A / 2 / w ^ 2 + (1 / 8) / w ^ 2 := by
    have hexp : (1 / 4) * (u / w ^ 2 + 2 * (u / w ^ 2) ^ 2)
        = A / 2 / w ^ 2 + (B / (4 * w ^ 4) + (1 / 2) * (u / w ^ 2) ^ 2) := by
      rw [hudef]; field_simp; ring
    rw [hexp]
    have hR : B / (4 * w ^ 4) + (1 / 2) * (u / w ^ 2) ^ 2 ≤ (1 / 8) / w ^ 2 := by
      rw [le_div_iff₀ hw2]
      have hL : (B / (4 * w ^ 4) + (1 / 2) * (u / w ^ 2) ^ 2) * w ^ 2
          = (B / 4 + u ^ 2 / 2) / w ^ 2 := by
        field_simp
      rw [hL]
      have hnum : B / 4 + u ^ 2 / 2 ≤ B / 4 + (2 * A + B) ^ 2 / 2 := by
        have := pow_le_pow_left₀ hu0 hu_le 2
        linarith
      calc (B / 4 + u ^ 2 / 2) / w ^ 2 ≤ (B / 4 + (2 * A + B) ^ 2 / 2) / w ^ 2 :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ (w ^ 2 / 8) / w ^ 2 := div_le_div_of_nonneg_right hBAB (by positivity)
        _ = 1 / 8 := by field_simp
    linarith
  rw [ht]
  exact hmain

/-- Elementary bound on the tail constant: with `A = ‖c‖` and `w ≥ 32(1+A)^4+32`,
`K/(3w⁶) ≤ 1/8`. -/
theorem sharpK_div_le (A w : ℝ) (hA : 0 ≤ A) (hw : 32 * (1 + A) ^ 4 + 32 ≤ w) :
    (2 * A + (A ^ 2 + A) + 2 * (2 * A + (A ^ 2 + A)) ^ 2) / 3 / w ^ 6 ≤ 1 / 8 := by
  set B := A ^ 2 + A with hBdef
  have hApos : (0 : ℝ) < 1 + A := by linarith
  have hA0 : (0 : ℝ) ≤ 1 + A := by linarith
  have hA1 : (1 : ℝ) ≤ 1 + A := by linarith
  have hp4 : (1 : ℝ) ≤ (1 + A) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hA1 4
    simpa using this
  have h4pos : (0 : ℝ) < (1 + A) ^ 4 := pow_pos hApos 4
  have hp12 : (1 : ℝ) ≤ (1 + A) ^ 12 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hA1 12
    simpa using this
  have hwpos : 0 < w := by
    have : (0 : ℝ) ≤ (1 + A) ^ 4 := by positivity
    linarith
  have hw6pos : 0 < w ^ 6 := by positivity
  have hw2big : 1024 * (1 + A) ^ 8 ≤ w ^ 2 := by
    have h0 : (0 : ℝ) ≤ 32 * (1 + A) ^ 4 := by positivity
    have hw32 : 32 * (1 + A) ^ 4 ≤ w := by linarith
    calc 1024 * (1 + A) ^ 8 = (32 * (1 + A) ^ 4) ^ 2 := by ring
      _ ≤ w ^ 2 := pow_le_pow_left₀ h0 hw32 2
  have hw6big : (2 : ℝ) ^ 30 * (1 + A) ^ 4 ≤ w ^ 6 := by
    have h8 : 1024 * (1 + A) ^ 4 ≤ w ^ 2 := by
      have h48 : (1 + A) ^ 4 ≤ (1 + A) ^ 8 := pow_le_pow_right₀ hA1 (by norm_num)
      linarith [hw2big, h48]
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1024 * (1 + A) ^ 4 by positivity) h8 3
    have hcube : (1024 * (1 + A) ^ 4) ^ 3 = (2 : ℝ) ^ 30 * (1 + A) ^ 12 := by ring
    have hw6 : (w ^ 2) ^ 3 = w ^ 6 := by ring
    rw [hcube, hw6] at h
    have h124 : (1 + A) ^ 4 ≤ (1 + A) ^ 12 := pow_le_pow_right₀ hA1 (by norm_num)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ 30 := by positivity
    nlinarith [h, h124, hpos]
  have hK : 2 * A + B + 2 * (2 * A + B) ^ 2 ≤ 36 * (1 + A) ^ 4 := by
    rw [hBdef]
    nlinarith [hA, sq_nonneg A, pow_nonneg hA0 2,
      sq_nonneg (1 + A), pow_nonneg hA0 3, pow_nonneg hA0 4]
  have hden : (2 : ℝ) ^ 30 * (1 + A) ^ 4 ≤ w ^ 6 := hw6big
  calc (2 * A + B + 2 * (2 * A + B) ^ 2) / 3 / w ^ 6
      = (2 * A + B + 2 * (2 * A + B) ^ 2) / (3 * w ^ 6) := by rw [div_div]
    _ ≤ (36 * (1 + A) ^ 4) / (3 * w ^ 6) :=
        div_le_div_of_nonneg_right hK (by positivity)
    _ = 12 * (1 + A) ^ 4 / w ^ 6 := by ring
    _ ≤ 12 * (1 + A) ^ 4 / ((2 : ℝ) ^ 30 * (1 + A) ^ 4) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ 1 / 8 := by
        rw [div_le_iff₀ (by have h := h4pos; positivity)]
        nlinarith [hp4]

/-! ## Geometric series -/

private lemma summable_quarter_pow_succ : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) := by
  have h0 : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  simpa [pow_succ] using h0.mul_right (1 / 4 : ℝ)

private lemma summable_quarter_pow_add_two : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 2)) := by
  have h1 : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1) * (1 / 4 : ℝ)) :=
    summable_quarter_pow_succ.mul_right _
  exact h1.congr (fun n => by rw [pow_add]; ring)

private lemma tsum_quarter_pow_add_two : (∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 2)) = 1 / 12 := by
  have h0 : HasSum (fun n : ℕ => (1 / 4 : ℝ) ^ n) ((1 : ℝ) - 1 / 4)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (by norm_num)
  have h1 : HasSum (fun n : ℕ => (1 / 4 : ℝ) * ((1 / 4 : ℝ) * (1 / 4 : ℝ) ^ n))
      ((1 / 4 : ℝ) * ((1 / 4 : ℝ) * ((1 : ℝ) - 1 / 4)⁻¹)) :=
    (h0.mul_left (1 / 4 : ℝ)).mul_left (1 / 4 : ℝ)
  have h2 : (∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 2)) =
      (1 / 4 : ℝ) * ((1 / 4 : ℝ) * ((1 : ℝ) - 1 / 4)⁻¹) := by
    rw [← h1.tsum_eq]
    exact tsum_congr (fun n => by rw [pow_add]; ring)
  rw [h2]; norm_num

/-! ## Norm of the Böttcher terms -/

theorem norm_bottcherTerm (c z : ℂ) (n : ℕ) :
    ‖bottcherTerm c n z‖
      = (1 / 4 : ℝ) ^ (n + 1) * ‖Complex.log (normFactor c ((pMap c)^[n] z))‖ := by
  rw [bottcherTerm, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]

/-- Termwise bound with the crude constant `K`: for `‖w‖ ≥ 1`,
`‖log (normFactor c w)‖ ≤ K/‖w‖²`, and the orbit of `z` stays outside `‖z‖`. -/
theorem norm_bottcherTerm_le_sharp (c z : ℂ) (hz : sharpRadius c ≤ ‖z‖) (n : ℕ) :
    ‖bottcherTerm c n z‖ ≤ (1 / 4 : ℝ) ^ (n + 1) * sharpK c / ‖z‖ ^ 2 := by
  rw [norm_bottcherTerm]
  have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (sharpRadius_pos c) hz
  have hfar := (norm_iterate_pMap_ge_sharp c z hz n).1
  have hmono := (norm_iterate_pMap_ge_sharp c z hz n).2
  have h1 := norm_log_normFactor_le_sharp c ((pMap c)^[n] z) hfar
  have h2 := sharpT_add_sq_le' c (v := ‖(pMap c)^[n] z‖) (le_trans (one_le_sharpRadius c) hfar)
  have h3 : sharpK c / ‖(pMap c)^[n] z‖ ^ 2 ≤ sharpK c / ‖z‖ ^ 2 :=
    div_le_div_of_nonneg_left (sharpK_nonneg c) (pow_pos hzpos 2)
      (by nlinarith [hmono, norm_nonneg z, norm_nonneg ((pMap c)^[n] z)])
  calc (1 / 4 : ℝ) ^ (n + 1) * ‖Complex.log (normFactor c ((pMap c)^[n] z))‖
      ≤ (1 / 4 : ℝ) ^ (n + 1) * (sharpK c / ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) (by positivity)
    _ = (1 / 4 : ℝ) ^ (n + 1) * sharpK c / ‖z‖ ^ 2 := by ring

/-- Sharper termwise bound for the tail `n ≥ 1`, using `‖z_n‖ ≥ ‖z‖⁴/2`. -/
theorem norm_bottcherTerm_succ_le (c z : ℂ) (hz : sharpRadius c ≤ ‖z‖) (n : ℕ) :
    ‖bottcherTerm c (n + 1) z‖ ≤ (1 / 4 : ℝ) ^ (n + 2) * (4 * sharpK c / ‖z‖ ^ 8) := by
  rw [norm_bottcherTerm]
  have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (sharpRadius_pos c) hz
  have hfar := (norm_iterate_pMap_ge_sharp c z hz (n + 1)).1
  have h1 := norm_log_normFactor_le_sharp c ((pMap c)^[n + 1] z) hfar
  have h2 := sharpT_add_sq_le' c (v := ‖(pMap c)^[n + 1] z‖)
    (le_trans (one_le_sharpRadius c) hfar)
  have hbig := pow_four_div_two_le_norm_iterate c z hz (n := n + 1) (by omega)
  have h3 : sharpK c / ‖(pMap c)^[n + 1] z‖ ^ 2 ≤ 4 * sharpK c / ‖z‖ ^ 8 := by
    have hz4 : (0 : ℝ) < ‖z‖ ^ 4 / 2 := by positivity
    have hs : (‖z‖ ^ 4 / 2) ^ 2 ≤ ‖(pMap c)^[n + 1] z‖ ^ 2 := by
      have := pow_le_pow_left₀ (le_of_lt hz4) hbig 2
      simpa [pow_mul] using this
    have h4 : sharpK c / ‖(pMap c)^[n + 1] z‖ ^ 2 ≤ sharpK c / (‖z‖ ^ 4 / 2) ^ 2 :=
      div_le_div_of_nonneg_left (sharpK_nonneg c) (pow_pos hz4 2) hs
    have h5 : sharpK c / (‖z‖ ^ 4 / 2) ^ 2 = 4 * sharpK c / ‖z‖ ^ 8 := by
      field_simp
      ring
    rw [h5] at h4
    exact h4
  calc (1 / 4 : ℝ) ^ (n + 2) * ‖Complex.log (normFactor c ((pMap c)^[n + 1] z))‖
      ≤ (1 / 4 : ℝ) ^ (n + 2) * (4 * sharpK c / ‖z‖ ^ 8) :=
        mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) (by positivity)

/-! ## The main theorem -/

/-- **Sharp `1/‖z‖²` bound for the Böttcher series of the tricorn.**

There is `r > 0` (depending on `c`) such that for every `‖z‖ ≥ r`,
`‖bottcherSeries c z‖ ≤ (‖c‖/2 + 1/4)/‖z‖²`.

The leading term of the series is `(1/4) * log (normFactor c z) = c̄/(2z²) + O(1/‖z‖⁴)`, so the
constant `‖c‖/2` is the *exact* leading constant; the `+1/4` absorbs the remainder for `‖z‖`
large.  This is the quantitative input that makes `z ↦ w · exp (-(bottcherSeries c z))` a
contraction on a ball of radius `(1+‖c‖)/‖w‖` with the *sharp* displacement bound
`(1+‖c‖)/‖w‖` (the crude `Core.norm_bottcherSeries_le`, with constant `(3/2)(‖c‖²+3‖c‖)`,
cannot produce that).

Suggested route (the two analytic/arithmetic ingredients are already proved in the workspace):

* Take `r := 32 * (1 + ‖c‖)^4 + 32`.  Then `2*(1+‖c‖) ≤ r`, and for `‖w‖ ≥ r` the quartic
  satisfies `‖w‖^4/2 ≤ ‖pMap c w‖` (indeed `max 1 ‖c‖ ≤ ‖w‖` and
  `Work.Bottcher.Core.norm_pMap_ge` give it), so the `pMap c`-orbit of `z` with `r ≤ ‖z‖` is
  monotone (`Work.Bottcher.Core.norm_iterate_pMap_ge`): `‖z‖ ≤ ‖(pMap c)^[n] z‖` for all `n`,
  and `r ≤ ‖(pMap c)^[n] z‖`.
* Write `A := ‖c‖` and `t(w) := 2*A/‖w‖² + (A²+A)/‖w‖⁴`.  By
  `Work.Bottcher.Contraction.norm_log_normFactor_le c w` (hypothesis `32*(1+‖c‖)^4+32 ≤ ‖w‖`,
  which holds for the whole orbit),
  `‖log (normFactor c w)‖ ≤ t(w) + 2*t(w)²`.
* Split `bottcherSeries c z = bottcherTerm c 0 z + ∑' n, bottcherTerm c (n+1) z`
  (`Summable.tsum_eq_zero_add`, with summability of `bottcherTerm c · z` from
  `Work.Bottcher.Series.summable_bottcherTerm`, or directly from the geometric majorant), and
  bound the `n ≥ 1` terms by `4^{-(n+1)} * (t(z_n) + 2*t(z_n)²)` with `z_n := (pMap c)^[n] z`,
  replacing `‖z_n‖` by `‖z‖` (monotonicity, and `r ≤ ‖z‖ ≤ ‖z_n‖`).
* Sum the geometric series: `∑_{n≥1} 4^{-(n+1)} = 1/12`.

(Implementation: rather than the lossy uniform estimate on the tail, the `n ≥ 1` terms are
summed against `‖z_n‖ ≥ ‖z‖⁴/2` (valid for `n ≥ 1`), which gives
`∑_{n≥1} 4^{-(n+1)}‖log (normFactor c z_n)‖ ≤ K/(3‖z‖⁸)` with
`K = 2‖c‖ + (‖c‖²+‖c‖) + 2(2‖c‖ + ‖c‖²+‖c‖)²`; together with the sharp first term
`≤ ‖c‖/(2‖z‖²) + 1/(8‖z‖²)` this gives the claim because both remainders are `≤ 1/(8‖z‖²)`.) -/
theorem bottcherSeries_le_sharp (c : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, r ≤ ‖z‖ →
      ‖Work.Bottcher.bottcherSeries c z‖ ≤ (‖c‖ / 2 + 1 / 4) / ‖z‖ ^ 2 := by
  refine ⟨sharpRadius c, sharpRadius_pos c, fun z hz => ?_⟩
  have hsumm : Summable (fun n : ℕ => ‖bottcherTerm c n z‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_bottcherTerm_le_sharp c z hz n) ?_
    have h0 : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1) * (sharpK c / ‖z‖ ^ 2)) :=
      summable_quarter_pow_succ.mul_right _
    exact h0.congr (fun n => by ring)
  have hsplit := Summable.tsum_eq_zero_add hsumm
  have h0bound : ‖bottcherTerm c 0 z‖ ≤ ‖c‖ / 2 / ‖z‖ ^ 2 + (1 / 8) / ‖z‖ ^ 2 := by
    rw [norm_bottcherTerm]
    have hlog := norm_log_normFactor_le_sharp c z hz
    have hq := quarter_sharpT_le ‖c‖ ‖z‖ (norm_nonneg c) (by simpa only [sharpRadius] using hz)
    calc (1 / 4 : ℝ) ^ (0 + 1) * ‖Complex.log (normFactor c ((pMap c)^[0] z))‖
        = (1 / 4) * ‖Complex.log (normFactor c z)‖ := by simp
      _ ≤ (1 / 4) * (sharpT c ‖z‖ + 2 * sharpT c ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          simpa only [Function.iterate_zero_apply] using hlog
      _ ≤ ‖c‖ / 2 / ‖z‖ ^ 2 + (1 / 8) / ‖z‖ ^ 2 := by
          simpa only [sharpT] using hq
  have htail : ∑' n : ℕ, ‖bottcherTerm c (n + 1) z‖ ≤ (1 / 8) / ‖z‖ ^ 2 := by
    have hmaj : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 2) * (4 * sharpK c / ‖z‖ ^ 8)) :=
      summable_quarter_pow_add_two.mul_right _
    have hle : ∀ n : ℕ, ‖bottcherTerm c (n + 1) z‖
        ≤ (1 / 4 : ℝ) ^ (n + 2) * (4 * sharpK c / ‖z‖ ^ 8) :=
      fun n => norm_bottcherTerm_succ_le c z hz n
    have hsum : Summable (fun n : ℕ => ‖bottcherTerm c (n + 1) z‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hmaj
    have h1 := hsum.tsum_le_tsum hle hmaj
    have h2 : (∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 2) * (4 * sharpK c / ‖z‖ ^ 8))
        = (1 / 12) * (4 * sharpK c / ‖z‖ ^ 8) := by
      rw [tsum_mul_right, tsum_quarter_pow_add_two]
    rw [h2] at h1
    have h3 : (1 / 12) * (4 * sharpK c / ‖z‖ ^ 8) ≤ (1 / 8) / ‖z‖ ^ 2 := by
      have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (sharpRadius_pos c) hz
      have hw2pos : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos hzpos 2
      have hK := sharpK_div_le ‖c‖ ‖z‖ (norm_nonneg c) (by simpa only [sharpRadius] using hz)
      have heq : (1 / 12) * (4 * sharpK c / ‖z‖ ^ 8) = sharpK c / 3 / ‖z‖ ^ 8 := by ring
      have heq2 : sharpK c / 3 / ‖z‖ ^ 8 * ‖z‖ ^ 2 = sharpK c / 3 / ‖z‖ ^ 6 := by
        field_simp
      rw [heq, le_div_iff₀ hw2pos, heq2]
      simpa only [sharpK] using hK
    linarith [h1, h3]
  calc ‖bottcherSeries c z‖ = ‖∑' n : ℕ, bottcherTerm c n z‖ := rfl
    _ ≤ ∑' n : ℕ, ‖bottcherTerm c n z‖ := norm_tsum_le_tsum_norm hsumm
    _ = ‖bottcherTerm c 0 z‖ + ∑' n : ℕ, ‖bottcherTerm c (n + 1) z‖ := hsplit
    _ ≤ (‖c‖ / 2 / ‖z‖ ^ 2 + (1 / 8) / ‖z‖ ^ 2) + (1 / 8) / ‖z‖ ^ 2 :=
        add_le_add h0bound htail
    _ = (‖c‖ / 2 + 1 / 4) / ‖z‖ ^ 2 := by ring

end Work.Bottcher.Inverse
