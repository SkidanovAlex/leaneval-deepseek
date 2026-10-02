import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Flower.GermDefs
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ
import Submission.Work.SatFree.gU_sgauge_loss

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SatFree

open Work.FatouCoord.Flower
open Metric

/-! ## Elementary estimates for the wide gauge and for the local inverse

These are the small lemmas the main argument of `backward_step` is built from; they are kept
private because they concern only the algebra of the chart `W = -1/u`. -/

/-- `sgauge (W - 1) = sgauge W - 1`. -/
private lemma sgauge_sub_one (W : ℂ) : sgauge (W - 1) = sgauge W - 1 := by
  rw [sgauge, sgauge]
  simp [Complex.sub_re, Complex.sub_im]
  ring

/-- The chart offset identity: if `u = v + v² h` then `-1/v - (-1/u - 1) = (u - v h)/u`. -/
private lemma chart_offset (u v hv : ℂ) (hu : u ≠ 0) (hv0 : v ≠ 0)
    (hrel : u = v + v ^ 2 * hv) :
    -1 / v - (-1 / u - 1) = (u - v * hv) / u := by
  field_simp
  rw [hrel]
  ring

/-- The germ value `v` recovered from `u` satisfies `‖v‖ ≤ 2 ‖u‖` as soon as `‖v‖ ≤ 1/4`. -/
private lemma norm_v_le_two_norm_u {u v hv : ℂ} (hrel : u = v + v ^ 2 * hv)
    (hbv : ‖hv‖ ≤ 2) (hq : ‖v‖ ≤ 1 / 4) : ‖v‖ ≤ 2 * ‖u‖ := by
  have hsub : u - v = v ^ 2 * hv := by rw [hrel]; ring
  have h1 : ‖u - v‖ ≤ ‖v‖ ^ 2 * 2 := by
    rw [hsub, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left hbv (by positivity)
  have h2 : ‖v‖ ^ 2 * 2 ≤ (1 / 4) * ‖v‖ * 2 := by
    have hvnn : 0 ≤ ‖v‖ := norm_nonneg v
    nlinarith [hq, hvnn]
  have h4 : ‖v‖ ≤ ‖u‖ + ‖u - v‖ := by
    calc ‖v‖ = ‖u - (u - v)‖ := by congr 1; ring
      _ ≤ ‖u‖ + ‖u - v‖ := norm_sub_le _ _
  linarith

/-- The quadratic offset `u - v h v` is bounded by a constant times `‖u‖`. -/
private lemma norm_offset_le {u v hv : ℂ} {a : ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hrel : u = v + v ^ 2 * hv) (herr : ‖hv - 1 - a * v‖ ≤ A * ‖v‖ ^ 2)
    (hq : ‖v‖ ≤ 1 / 4) (hvu : ‖v‖ ≤ 2 * ‖u‖) :
    ‖u - v * hv‖ ≤ (1 + 5 * ‖a‖ / 4 + 5 * A / 16) * ‖u‖ := by
  have hfac : u - v * hv = v * (1 + (v - 1) * hv) := by rw [hrel]; ring
  have hdec : 1 + (v - 1) * hv
      = v + a * v * (v - 1) + (hv - 1 - a * v) * (v - 1) := by ring
  have hvnn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hunn : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hv1 : ‖v - 1‖ ≤ 5 / 4 := by
    have h : ‖v - 1‖ ≤ ‖v‖ + ‖(1 : ℂ)‖ := norm_sub_le v 1
    simp only [norm_one] at h
    linarith
  have hA2 : (0 : ℝ) ≤ A * ‖v‖ ^ 2 := mul_nonneg hA (sq_nonneg _)
  have hQ : 0 ≤ 1 + 5 * ‖a‖ / 4 + 5 * A / 16 := by
    have : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
    linarith
  have hsq : ‖v‖ ^ 2 ≤ ‖v‖ * (1 / 4) := by nlinarith [hq, hvnn]
  have hnorm : ‖1 + (v - 1) * hv‖ ≤ ‖v‖ * (1 + 5 * ‖a‖ / 4 + 5 * A / 16) := by
    have h1 : ‖v + a * v * (v - 1) + (hv - 1 - a * v) * (v - 1)‖
        ≤ ‖v‖ + ‖a * v * (v - 1)‖ + ‖(hv - 1 - a * v) * (v - 1)‖ := by
      have hA1 : ‖v + a * v * (v - 1)‖ ≤ ‖v‖ + ‖a * v * (v - 1)‖ := norm_add_le v _
      have hB1 : ‖v + a * v * (v - 1) + (hv - 1 - a * v) * (v - 1)‖
          ≤ ‖v + a * v * (v - 1)‖ + ‖(hv - 1 - a * v) * (v - 1)‖ :=
        norm_add_le (v + a * v * (v - 1)) _
      linarith
    rw [norm_mul, norm_mul] at h1
    rw [norm_mul] at h1
    have h2 : ‖a‖ * ‖v‖ * ‖v - 1‖ ≤ ‖a‖ * ‖v‖ * (5 / 4) := by
      have h0 : (0 : ℝ) ≤ ‖a‖ * ‖v‖ := by positivity
      exact mul_le_mul_of_nonneg_left hv1 h0
    have h3 : ‖hv - 1 - a * v‖ * ‖v - 1‖ ≤ A * ‖v‖ ^ 2 * (5 / 4) := by
      have h0 : (0 : ℝ) ≤ ‖v - 1‖ := norm_nonneg _
      calc ‖hv - 1 - a * v‖ * ‖v - 1‖ ≤ (A * ‖v‖ ^ 2) * ‖v - 1‖ :=
            mul_le_mul_of_nonneg_right herr h0
        _ ≤ (A * ‖v‖ ^ 2) * (5 / 4) := mul_le_mul_of_nonneg_left hv1 hA2
    have hKey : A * ‖v‖ ^ 2 * (5 / 4) ≤ A * (‖v‖ * (1 / 4)) * (5 / 4) := by
      have := mul_le_mul_of_nonneg_left hsq hA
      linarith
    rw [hdec]
    linarith
  rw [hfac, norm_mul]
  calc ‖v‖ * ‖1 + (v - 1) * hv‖
      ≤ ‖v‖ * (‖v‖ * (1 + 5 * ‖a‖ / 4 + 5 * A / 16)) :=
        mul_le_mul_of_nonneg_left hnorm hvnn
    _ = ‖v‖ ^ 2 * (1 + 5 * ‖a‖ / 4 + 5 * A / 16) := by ring
    _ ≤ (1 / 4) * ‖v‖ * (1 + 5 * ‖a‖ / 4 + 5 * A / 16) := by
        have := mul_le_mul_of_nonneg_right hsq hQ
        linarith
    _ ≤ (1 / 4) * (2 * ‖u‖) * (1 + 5 * ‖a‖ / 4 + 5 * A / 16) := by
        have h0 : (0 : ℝ) ≤ (1 / 4) * (1 + 5 * ‖a‖ / 4 + 5 * A / 16) := by linarith
        have := mul_le_mul_of_nonneg_right hvu h0
        linarith
    _ = (1 + 5 * ‖a‖ / 4 + 5 * A / 16) * ‖u‖ / 2 := by ring
    _ ≤ (1 + 5 * ‖a‖ / 4 + 5 * A / 16) * ‖u‖ := by nlinarith [hQ, hunn]

/-- **One step of the backward orbit in the wide chart sector.**

For a parabolic germ `f z = z + z ^ 2 * h z` with the quantitative bounds `ParabolicBounds`
(`h 0 = 1`, `h z = 1 + a z + O(z^2)`, `‖h‖ ≤ 2`, `‖h'‖ ≤ A'` on `ball 0 r`), there are constants
`M₀ > 0`, `C₀ ≥ 0` such that every `W` with `sgauge W = W.re + |W.im| ≥ M₀` has a preimage `W'`
under the chart dynamics, i.e. `f (-1/W') = -1/W` (equivalently `wMap f W' = W`), and this
preimage loses at most the constant `C₀` of the gauge: `sgauge W' ≥ sgauge W - C₀`.

Suggested route: let `G` be the local inverse of `f` at `0`
(`Petal.exists_local_inverse_of_parabolicBounds` gives `G` analytic at `0`, `G 0 = 0`, and both
`f (G u) = u`, `G (f z) = z` near `0`); choose `δ > 0` so that `f (G u) = u` and
`‖G u‖ < min r (1/4)` for `‖u‖ < δ`.  For `u = -1/W` put `v = G u` and `W' = -1/v`; then
`f (-1/W') = f v = u = -1/W`.  The estimate is algebraic: `u = v + v ^ 2 * h v` gives
`W' - (W - 1) = (u - v * h v) / u`, and with `‖v‖ ≤ 1/4` one gets `‖v‖ ≤ 2 ‖u‖` and
`‖u - v * h v‖ ≤ 4 (A/4 + ‖a‖ + 2) ‖u‖ ^ 2`, hence `‖W' - (W - 1)‖ ≤ (A + 4 ‖a‖ + 8) ‖u‖`.
Finally `sgauge (W - 1) = sgauge W - 1` and `sgauge` is `2`-Lipschitz in `‖·‖`. -/
theorem backward_step {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ M₀ C₀ : ℝ, 0 < M₀ ∧ 0 ≤ C₀ ∧ ∀ W : ℂ,
      M₀ ≤ Work.FatouCoord.Flower.sgauge W →
      ∃ W' : ℂ, f (-1 / W') = -1 / W ∧
        Work.FatouCoord.Flower.sgauge W' ≥ Work.FatouCoord.Flower.sgauge W - C₀ := by
  -- The local inverse of the germ at the origin.
  obtain ⟨G, hGan, hG0, _hGd, _hG2, _hG3, _hGleft, hGright⟩ :=
    Work.FatouCoord.Petal.exists_local_inverse_of_parabolicBounds hb
  -- A radius on which `G` really is a right inverse of `f`.
  have hδ₁ : ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → f (G u) = u := by
    rw [Metric.eventually_nhds_iff] at hGright
    obtain ⟨ε, hεpos, hε⟩ := hGright
    exact ⟨ε, hεpos, fun u hu => hε (by simpa using hu)⟩
  -- A radius on which `G` lands in the disc where the quantitative bounds hold.
  have hδ₂ : ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → ‖G u‖ < min r (1 / 4) := by
    have hpos : (0 : ℝ) < min r (1 / 4) := lt_min hb.hr (by norm_num)
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.continuousAt_iff.mp hGan.continuousAt) (min r (1 / 4)) hpos
    exact ⟨δ, hδpos, fun u hu => by
      have h := hδ (show dist u 0 < δ by simpa using hu)
      simpa [hG0, dist_eq_norm] using h⟩
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hδ₁
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hδ₂
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos hδ₂pos
  have hδle₁ : δ ≤ δ₁ := min_le_left _ _
  have hδle₂ : δ ≤ δ₂ := min_le_right _ _
  refine ⟨max 1 (4 / δ), 3 + 5 * ‖a‖ / 2 + 5 * A / 8, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · have ha : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
    linarith [hb.hA]
  · intro W hW
    -- `sgauge W ≥ M₀ > 0` forces `W ≠ 0` and `‖W‖ ≥ 2/δ`.
    have hWne : W ≠ 0 := by
      intro h0
      rw [h0] at hW
      simp [sgauge] at hW
      linarith
    have h4δ : 4 / δ ≤ 2 * ‖W‖ :=
      le_trans (le_max_right 1 (4 / δ)) (le_trans hW (Work.SatFree.sgauge_le_two_mul_norm W))
    have h2δ : 2 / δ ≤ ‖W‖ := by
      have h : 2 ≤ ‖W‖ * δ := by
        have h' := mul_le_mul_of_nonneg_right h4δ hδpos.le
        rw [div_mul_cancel₀ 4 (ne_of_gt hδpos)] at h'
        linarith
      rw [div_le_iff₀ hδpos]
      linarith
    have hWpos : (0 : ℝ) < ‖W‖ := by
      have : (0 : ℝ) < 2 / δ := div_pos two_pos hδpos
      linarith
    set u : ℂ := -1 / W with hudef
    have hunorm : ‖u‖ = 1 / ‖W‖ := by
      rw [hudef, norm_div, norm_neg, norm_one]
    have hu_ne : u ≠ 0 := by
      rw [hudef]
      exact div_ne_zero (by norm_num) hWne
    have hu_lt : ‖u‖ < δ := by
      have h2δ' : (0 : ℝ) < 2 / δ := div_pos two_pos hδpos
      have hle : (1 : ℝ) / ‖W‖ ≤ 1 / (2 / δ) := one_div_le_one_div_of_le h2δ' h2δ
      rw [one_div_div] at hle
      rw [hunorm]
      linarith
    -- The preimage `v = G u` of `u` under `f`.
    set v : ℂ := G u with hvdef
    have hfu : f v = u := by rw [hvdef]; exact hδ₁ u (lt_of_lt_of_le hu_lt hδle₁)
    have hGsmall : ‖G u‖ < min r (1 / 4) := hδ₂ u (lt_of_lt_of_le hu_lt hδle₂)
    have hv_quarter : ‖v‖ ≤ 1 / 4 := by
      rw [hvdef]
      exact le_of_lt (lt_of_lt_of_le hGsmall (min_le_right _ _))
    have hv_mem : v ∈ ball 0 r := by
      rw [mem_ball_zero_iff, hvdef]
      exact lt_of_lt_of_le hGsmall (min_le_left _ _)
    have hu_eq : u = v + v ^ 2 * h v := hfu.symm.trans (hb.f_eq v hv_mem)
    have hv_ne : v ≠ 0 := by
      intro hv0
      have hf0 : f 0 = 0 := by
        have h := hb.f_eq 0 (by rw [mem_ball_zero_iff]; simpa using hb.hr)
        simpa using h
      exact hu_ne (by rw [← hfu, hv0, hf0])
    -- The preimage in the chart.
    refine ⟨-1 / v, ?_, ?_⟩
    · have hneg : -1 / (-1 / v) = v := by
        field_simp
      rw [hneg, hfu, hudef]
    · have hW_eq : W = -1 / u := by
        rw [hudef]
        field_simp
      -- The gauge of `-1/v` is close to that of `W - 1`, and `W - 1` loses exactly `1`.
      have hsub1 : sgauge (W - 1) = sgauge W - 1 := sgauge_sub_one W
      have hoff : ‖u - v * h v‖ ≤ (1 + 5 * ‖a‖ / 4 + 5 * A / 16) * ‖u‖ :=
        norm_offset_le hb.hA hu_eq (hb.h_close v hv_mem) hv_quarter
          (norm_v_le_two_norm_u hu_eq (hb.h_bound v hv_mem) hv_quarter)
      have hnormid : ‖-1 / v - (W - 1)‖ ≤ 1 + 5 * ‖a‖ / 4 + 5 * A / 16 := by
        have h' : -1 / v - (W - 1) = -1 / v - (-1 / u - 1) := by rw [hW_eq]
        rw [h', chart_offset u v (h v) hu_ne hv_ne hu_eq, norm_div,
          div_le_iff₀ (norm_pos_iff.mpr hu_ne)]
        exact hoff
      have hkey : sgauge (W - 1) - sgauge (-1 / v)
          ≤ 2 * ‖-1 / v - (W - 1)‖ := by
        have h := Work.SatFree.sgauge_sub_le (W - 1) ((-1 / v) - (W - 1))
        simpa [show (W - 1) + ((-1 / v) - (W - 1)) = -1 / v by ring] using h
      linarith

end Work.SatFree
