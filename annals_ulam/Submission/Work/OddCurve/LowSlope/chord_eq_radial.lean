import Mathlib
import Submission.Work.OddEnvelope.Main

/-!
# The chord endpoints are the radial points (`Work.OddCurve.LowSlope`)

The paper's Step 3 describes the body both by its *chord curve* `(x, y)` — the intersections of the
line `x_d = s x_1 + h(s)` with the profile — and by its *radial functions* `R(α), r(α)`.  On the
range where the cutting line passes through the origin (`h(s) = 0`) the two descriptions coincide:
the chord of slope `s` is the segment between the two radial points

    `X s = ρ(-c)·c`,   `Y s = ρ(c)·c`,   `c = (√(1+s²))⁻¹`,

where `ρ(u) = R(arccos u)` for `u > 0` and `ρ(-u) = r(arccos u)` is the radial function of the
profile in the `u = cos α` variable.

This is the hypothesis *"`ρ (√(1+s²))⁻¹ · (√(1+s²))⁻¹ = y s`"* of the crux
`Work.OddRadon.radonProfile_inv`-based identity
`Work.OddCurve.LowSlope.anchorRadonData` (Prop. `workHARD1`), so it is what lets one compare the
Radon data of the anchor body with its section integrals.

## The two uniqueness lemmas

For a strictly concave profile `f` with `f 0 = 1`, `f 1 = 0`, the line `t ↦ s t` (`s > 0`) meets
the graph in at most one point of `(0,1)`; for `t ↦ -s t` in at most one point of `(-1,0)`.  Both
follow from strict concavity applied at the endpoint `0`, where the profile is `1`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- A non-horizontal line meets a strictly concave profile at most once on the right. -/
lemma eq_linear_unique_pos {f : ℝ → ℝ}
    (hconc : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (h0 : f 0 = 1) {s : ℝ} {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hfa : f a = s * a) :
    ∀ b ∈ Set.Ioo (0 : ℝ) 1, f b = s * b → b = a := by
  intro b hb hfb
  rcases lt_trichotomy a b with hab | heq | hba
  · -- `a = (1 - a/b)·0 + (a/b)·b`
    have hb0 : (0 : ℝ) < b := hb.1
    have hb1 : b < 1 := hb.2
    have hca : (0 : ℝ) < 1 - a / b := by
      rw [sub_pos, div_lt_one hb0]; exact hab
    have hcb : (0 : ℝ) < a / b := div_pos ha.1 hb0
    have hsum : (1 - a / b) + a / b = 1 := by ring
    have hx : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hy : b ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, le_of_lt hb1⟩
    have hne : (0 : ℝ) ≠ b := ne_of_lt hb0
    have hkey := hconc.2 hx hy hne hca hcb hsum
    have hpt : (1 - a / b) • (0 : ℝ) + (a / b) • b = a := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
      field_simp
    rw [hpt] at hkey
    simp only [smul_eq_mul, h0, hfb, hfa, mul_one] at hkey
    have hsab : a / b * (s * b) = s * a := by field_simp
    rw [hsab] at hkey
    linarith [hkey, hca]
  · exact heq.symm
  · -- `b = (1 - b/a)·0 + (b/a)·a`
    have ha0 : (0 : ℝ) < a := ha.1
    have ha1 : a < 1 := ha.2
    have hca : (0 : ℝ) < 1 - b / a := by
      rw [sub_pos, div_lt_one ha0]; exact hba
    have hcb : (0 : ℝ) < b / a := div_pos hb.1 ha0
    have hsum : (1 - b / a) + b / a = 1 := by ring
    have hx : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hy : a ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, le_of_lt ha1⟩
    have hne : (0 : ℝ) ≠ a := ne_of_lt ha0
    have hkey := hconc.2 hx hy hne hca hcb hsum
    have hpt : (1 - b / a) • (0 : ℝ) + (b / a) • a = b := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
      field_simp
    rw [hpt] at hkey
    simp only [smul_eq_mul, h0, hfa, hfb, mul_one] at hkey
    have hsab : b / a * (s * a) = s * b := by field_simp
    rw [hsab] at hkey
    linarith [hkey, hca]

/-- A non-horizontal line meets a strictly concave profile at most once on the left. -/
lemma eq_linear_unique_neg {f : ℝ → ℝ}
    (hconc : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (h0 : f 0 = 1) {s : ℝ} {a : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 0)
    (hfa : f a = -(s * a)) :
    ∀ b ∈ Set.Ioo (-1 : ℝ) 0, f b = -(s * b) → b = a := by
  intro b hb hfb
  rcases lt_trichotomy a b with hab | heq | hba
  · -- `b = (1 - b/a)·a + (b/a)·0`
    have ha0 : a < 0 := ha.2
    have ha1 : (-1 : ℝ) < a := ha.1
    have hb0 : b < 0 := hb.2
    have hcb : (0 : ℝ) < b / a := div_pos_of_neg_of_neg hb0 ha0
    have hca : (0 : ℝ) < 1 - b / a := by
      rw [sub_pos]
      rw [div_lt_one_of_neg ha0]; exact hab
    have hsum : (b / a) + (1 - b / a) = 1 := by ring
    have hx : a ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt ha1, le_trans (le_of_lt ha0) (by norm_num)⟩
    have hy : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hne : a ≠ (0 : ℝ) := ne_of_lt ha0
    have hkey := hconc.2 hx hy hne hcb hca hsum
    have hpt : (b / a) • a + (1 - b / a) • (0 : ℝ) = b := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
      field_simp
    rw [hpt] at hkey
    simp only [smul_eq_mul, h0, hfa, hfb, mul_one] at hkey
    have hsab : b / a * (s * a) = s * b := by field_simp
    rw [mul_neg, hsab] at hkey
    linarith [hkey, hca]
  · exact heq.symm
  · -- `a = (1 - a/b)·b + (a/b)·0`
    have hb0 : b < 0 := hb.2
    have hb1 : (-1 : ℝ) < b := hb.1
    have hcb : (0 : ℝ) < a / b := div_pos_of_neg_of_neg ha.2 hb0
    have hca : (0 : ℝ) < 1 - a / b := by
      rw [sub_pos]
      rw [div_lt_one_of_neg hb0]; exact hba
    have hsum : (a / b) + (1 - a / b) = 1 := by ring
    have hx : b ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hb1, le_trans (le_of_lt hb0) (by norm_num)⟩
    have hy : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hne : b ≠ (0 : ℝ) := ne_of_lt hb0
    have hkey := hconc.2 hx hy hne hcb hca hsum
    have hpt : (a / b) • b + (1 - a / b) • (0 : ℝ) = a := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
      field_simp
    rw [hpt] at hkey
    simp only [smul_eq_mul, h0, hfb, hfa, mul_one] at hkey
    have hsab : a / b * (s * b) = s * a := by field_simp
    rw [mul_neg, hsab] at hkey
    linarith [hkey, hca]

/-- **The chord of a vanishing crop is the radial chord.**  On a slope `s` where the cutting line
passes through the origin (`h s = 0`), the chord endpoints of the envelope curve are the radial
points of the profile. -/
theorem envelope_chord_eq_radial {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y) {s : ℝ} (hs : 0 < s) (hz : h s = 0)
    (hpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) =
        Work.OddEnvelope.envelopeProfile h X Y (ρ u * u)) :
    Y s = ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹) ∧
      X s = ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * ((Real.sqrt (1 + s ^ 2))⁻¹) := by
  set f : ℝ → ℝ := Work.OddEnvelope.envelopeProfile h X Y with hf
  have hconc : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f :=
    Work.OddEnvelope.strictConcaveOn_envelopeProfile H
  have hf0 : f 0 = 1 := Work.OddEnvelope.envelopeProfile_zero
  have hf1 : f 1 = 0 := Work.OddEnvelope.envelopeProfile_right_end
  have hfm1 : f (-1) = 0 := Work.OddEnvelope.envelopeProfile_left_end
  set c : ℝ := (Real.sqrt (1 + s ^ 2))⁻¹ with hc
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hcpos : 0 < c := inv_pos.mpr hspos
  have hclt1 : c < 1 := by
    rw [hc]
    refine inv_lt_one_of_one_lt₀ ?_
    have h : (1 : ℝ) < 1 + s ^ 2 := by nlinarith [sq_nonneg s]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + s ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h
  have hmemc : c ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hclt1⟩
  have hmemc' : -c ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hcsq : c ^ 2 = (1 + s ^ 2)⁻¹ := by
    rw [hc, inv_pow, Real.sq_sqrt (by positivity)]
  have h1mc : 1 - c ^ 2 = (s * c) ^ 2 := by
    have h1 : c ^ 2 * (1 + s ^ 2) = 1 := by rw [hcsq]; field_simp
    nlinarith [h1]
  have hsqrt : Real.sqrt (1 - c ^ 2) = s * c := by
    rw [h1mc, Real.sqrt_sq (by positivity)]
  set t1 : ℝ := ρ c * c with ht1
  set t2 : ℝ := ρ (-c) * (-c) with ht2
  have ht1pos : 0 < t1 := mul_pos (hpos c hmemc) hcpos
  have ht2neg : t2 < 0 := by
    rw [ht2]
    nlinarith [hpos (-c) hmemc', hcpos]
  have hft1 : f t1 = s * t1 := by
    rw [ht1, ← hgraph c hmemc, hsqrt]; ring
  have hft2 : f t2 = -(s * t2) := by
    rw [ht2]
    have hsqq : (-c) ^ 2 = c ^ 2 := by ring
    have hg := hgraph (-c) hmemc'
    rw [hsqq, hsqrt] at hg
    rw [← hg]; ring
  -- both are supported in `(-1,1)`
  have hsupp := Work.OddEnvelope.envelopeProfile_support (h := h) (x := X) (y := Y)
  have hft1ne : f t1 ≠ 0 := by rw [hft1]; exact ne_of_gt (mul_pos hs ht1pos)
  have ht1Icc : t1 ∈ Set.Icc (-1 : ℝ) 1 := hsupp (Function.mem_support.mpr hft1ne)
  have ht1lt1 : t1 < 1 := by
    rcases lt_or_eq_of_le ht1Icc.2 with h | h
    · exact h
    · exfalso; rw [h, hf1] at hft1; nlinarith [hs, ht1pos, hft1]
  have ht1Ioo : t1 ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht1pos, ht1lt1⟩
  have hft2ne : f t2 ≠ 0 := by rw [hft2]; exact ne_of_gt (by linarith [mul_pos hs (neg_pos.mpr ht2neg)])
  have ht2Icc : t2 ∈ Set.Icc (-1 : ℝ) 1 := hsupp (Function.mem_support.mpr hft2ne)
  have ht2gtm1 : -1 < t2 := by
    rcases lt_or_eq_of_le ht2Icc.1 with h | h
    · exact h
    · exfalso; rw [← h, hfm1] at hft2; nlinarith [hs, hft2]
  have ht2Ioo : t2 ∈ Set.Ioo (-1 : ℝ) 0 := ⟨ht2gtm1, ht2neg⟩
  -- the anchor chord endpoints
  have hYf : f (Y s) = s * Y s := by
    rw [hf, Work.OddEnvelope.envelopeProfile_root_right H hs, hz]; ring
  have hYpos : 0 < Y s := H.toChordCurve_y.pos hs
  have hYlt : Y s < 1 := H.toChordCurve_y.lt_one hs
  have hmXf : f (-(X s)) = -(s * (-(X s))) := by
    rw [hf, Work.OddEnvelope.envelopeProfile_root_left H hs, hz]; ring
  have hXpos : 0 < X s := H.toChordCurve_x.pos hs
  have hXlt : X s < 1 := H.toChordCurve_x.lt_one hs
  have hmXIoo : -(X s) ∈ Set.Ioo (-1 : ℝ) 0 := ⟨by linarith, by linarith⟩
  have h1 : t1 = Y s :=
    (eq_linear_unique_pos hconc hf0 ht1Ioo hft1 (Y s) ⟨hYpos, hYlt⟩ hYf).symm
  have h2 : t2 = -(X s) :=
    (eq_linear_unique_neg hconc hf0 ht2Ioo hft2 (-(X s)) hmXIoo hmXf).symm
  refine ⟨by rw [← h1, ht1], ?_⟩
  have hX : X s = -t2 := by linarith [h2]
  rw [hX, ht2]; ring

end

end Work.OddCurve.LowSlope
