import Mathlib
import Submission.Work.Drive.sweepFamWideTolDefs
import Submission.Work.Drive.chordSweepDefs

/-!
# The matched phase of the wide end is `2`-Lipschitz in the loop parameter

The wide-end estimate (`Work.Drive.sweepFam_wideEnd_estimate_tol`) matches the loop parameter `τ`
of the (chamfered, smeared) chord sweep to the knot parameter `Work.Drive.wideSig D lam σ τ`
through the piecewise affine phase `Work.Drive.wideSigma`.  Every estimate that compares the loop
with the knot `r` at the matched parameter has to know that this matching *does not move faster
than the loop parameter itself* — otherwise a `C¹`-closeness of the loop to the reparametrised
knot says nothing about the parametrisation.

This file proves the sharp statement, with the constant `2` (which is attained: on the two
chamfers and, when the retained arc is short, on the chord, the phase advances exactly twice as
fast as the loop parameter):

    |wideSig D lam σ τ₁ - wideSig D lam σ τ₂| ≤ 2 * |τ₁ - τ₂|      (0 < lam ≤ 1/4).

## The shape of the proof

`wideSigma ta w d lam τ = τ + (wideSfrac ta w d lam (sweepParam τ) - sweepParam τ * period)`,
i.e. the phase is the loop parameter plus the *periodic* correction
`F (sweepParam τ) - sweepParam τ * period` with `F = wideSfrac ta w d lam`.  Everything rests on
two properties of the piecewise affine profile `F` on the profile interval `[0,1]`:

* `|F a - F b| ≤ 2 * period * |a - b|` (the slopes of the four affine pieces are
  `(1-2λ)·2w`, `2·period`, `(1-2λ)d/(1/2-λ) = 2d` and `2·period`, all in `[0, 2·period]` because
  `0 ≤ w ≤ period`, `d = period - w` and `0 < λ ≤ 1/4`), and
* `F 1 = F 0 + period` (`Work.Drive.wideSfrac_periodicity`), which makes the phase continue
  across the discontinuities of the sawtooth `sweepParam`.

With these, the estimate is elementary and is proved in the abstract form
`Work.Drive.wideAbs_lipschitz`: on an interval of length `< period` the sawtooth advances by
either `h/period` or `h/period - 1` (`h` = the increase of `τ`), and the two cases are exactly
what the two properties of `F` control; a whole number of periods is handled by the exact
`period`-shift `wideAbs_shift_nat`.

## Contents

* `Work.Drive.wideSig_sweepW'_bounds` — `0 ≤ sweepW' D σ ≤ period`;
* `Work.Drive.wideSfrac_lipschitz` — the Lipschitz bound for the affine profile, via the
  closed-form values `wideSfrac_chamfer₁_closed`, `wideSfrac_chord_closed`,
  `wideSfrac_chamfer₂_closed` on the three zones (the junctions are the only delicate point);
* `Work.Drive.wideAbs`, `Work.Drive.wideAbs_lipschitz` — the abstract estimate;
* `Work.Drive.wideSig_tau_lipschitz` — the statement.
-/

set_option linter.unusedVariables false

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## The width of the retained arc -/

/-- The width `sweepW' D σ` of the retained arc lies in `[0, period]` for *every* real sweep
parameter (the clamped lift is a knot point, where `Work.Drive.sweepW_pos_lt` applies, or one of
the two ends). -/
lemma wideSig_sweepW'_bounds {d : BandArcData} (D : SweepData d) (σ : ℝ) :
    0 ≤ sweepW' D σ ∧ sweepW' D σ ≤ period := by
  have hcoe : sweepW' D σ = sweepW D (clampI σ) := rfl
  rw [hcoe]
  rcases eq_or_lt_of_le (clampI σ).2.1 with h0 | h0
  · have h0' : clampI σ = 0 := Subtype.ext h0.symm
    rw [h0', sweepW_zero]
    exact ⟨le_rfl, period_pos.le⟩
  rcases eq_or_lt_of_le (clampI σ).2.2 with h1 | h1
  · have h1' : clampI σ = 1 := Subtype.ext h1
    rw [h1', sweepW_one]
    exact ⟨period_pos.le, le_rfl⟩
  · obtain ⟨h2, h3⟩ := sweepW_pos_lt D (clampI σ) ⟨h0, h1⟩
    exact ⟨h2.le, h3.le⟩

/-! ## The affine profile on its four zones, and its Lipschitz bound -/

/-- The first chamfer formula, valid on the *closed* zone `[1/2, 1/2 + λ/2]`: at the left end `u =
1/2` the profile takes the arc branch, whose value at `1/2` is the same. -/
lemma wideSfrac_chamfer₁_closed {ta w d lam u : ℝ} (hd : d = period - w)
    (hu1 : 1 / 2 ≤ u) (hu2 : u ≤ 1 / 2 + lam / 2) :
    wideSfrac ta w d lam u = ta + (1 - lam) * w + (2 * u - 1) * period := by
  rcases eq_or_lt_of_le hu1 with h | h
  · subst h
    rw [wideSfrac_arc le_rfl]
    ring
  · exact wideSfrac_chamfer₁ (not_le.mpr h) hu2

/-- The chord formula, valid on the *closed* zone `[1/2 + λ/2, 1 - λ/2]` (at the left end the
chamfer value agrees, using `d = period - w`). -/
lemma wideSfrac_chord_closed {ta w d lam u : ℝ} (h0 : 0 < lam) (hd : d = period - w)
    (hu1 : 1 / 2 + lam / 2 ≤ u) (hu2 : u ≤ 1 - lam / 2) :
    wideSfrac ta w d lam u
      = ta + w + lam * d + ((1 - 2 * lam) * d) * ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) := by
  have hlt : (1 : ℝ) / 2 < 1 / 2 + lam / 2 := by linarith
  have hA : ¬ u ≤ 1 / 2 := not_le.mpr (lt_of_lt_of_le hlt hu1)
  rcases eq_or_lt_of_le hu1 with h | h
  · subst h
    rw [wideSfrac_chamfer₁ hA le_rfl, hd, sub_self, zero_div, mul_zero, add_zero]
    ring
  · exact wideSfrac_chord hA (not_le.mpr h) hu2

/-- The second chamfer formula, valid on the *closed* zone `[1 - λ/2, 1]` (the chord value at
`1 - λ/2` agrees). -/
lemma wideSfrac_chamfer₂_closed {ta w d lam u : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 4)
    (hd : d = period - w) (hu1 : 1 - lam / 2 ≤ u) :
    wideSfrac ta w d lam u = ta + w + (1 - lam) * d + (2 * u - 2 + lam) * period := by
  have hA : ¬ u ≤ 1 / 2 := by linarith
  have hB : ¬ u ≤ 1 / 2 + lam / 2 := by linarith
  rcases eq_or_lt_of_le hu1 with h | h
  · subst h
    have hden : (1 : ℝ) / 2 - lam ≠ 0 := by linarith
    rw [wideSfrac_chord hA hB le_rfl,
      show (1 - lam / 2 - (1 / 2 + lam / 2) : ℝ) = 1 / 2 - lam by ring,
      div_self hden]
    ring
  · exact wideSfrac_chamfer₂ hA hB (not_le.mpr h)

/-- The slope of the chord piece: `((1 - 2λ)d)·(x-z)/(1/2-λ) = 2d(x-z)` (the factor
`1 - 2λ = 2(1/2 - λ)` cancels). -/
lemma wideSfrac_chord_slope {d lam x z : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 4) :
    ((1 - 2 * lam) * d) * ((x - z) / (1 / 2 - lam)) = 2 * d * (x - z) := by
  have hden : (1 : ℝ) / 2 - lam ≠ 0 := by linarith
  have h2 : (1 - 2 * lam) * (1 / 2 - lam)⁻¹ = 2 := by
    rw [← div_eq_mul_inv, div_eq_iff hden]
    ring
  rw [div_eq_mul_inv]
  rw [show ((1 - 2 * lam) * d) * ((x - z) * (1 / 2 - lam)⁻¹)
      = ((1 - 2 * lam) * (1 / 2 - lam)⁻¹) * (d * (x - z)) by ring]
  rw [h2]
  ring

/-- **Arc zone**: the profile is affine with slope `(1 - 2λ)·2w ∈ [0, 2·period]`. -/
lemma wideSfrac_lip_arc {ta w d lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 4) (hw0 : 0 ≤ w)
    (hwP : w ≤ period) {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    |wideSfrac ta w d lam b - wideSfrac ta w d lam a| ≤ 2 * period * (b - a) := by
  rw [wideSfrac_arc hb, wideSfrac_arc (le_trans hab hb)]
  have hdiff : (ta + (lam + (1 - 2 * lam) * (2 * b)) * w)
      - (ta + (lam + (1 - 2 * lam) * (2 * a)) * w)
      = (1 - 2 * lam) * (2 * w) * (b - a) := by ring
  rw [hdiff, abs_mul]
  have hs : |(1 - 2 * lam) * (2 * w)| ≤ 2 * period := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * w)]
    have h1' : |1 - 2 * lam| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    calc |1 - 2 * lam| * (2 * w) ≤ 1 * (2 * period) :=
          mul_le_mul h1' (by linarith) (by linarith) (by norm_num)
      _ = 2 * period := by ring
  calc |(1 - 2 * lam) * (2 * w)| * |b - a| ≤ (2 * period) * |b - a| :=
        mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    _ = 2 * period * (b - a) := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]

/-- **First chamfer**: the profile advances exactly at rate `2·period`. -/
lemma wideSfrac_lip_chamfer₁ {ta w d lam : ℝ} (h0 : 0 < lam) (hd : d = period - w)
    {a b : ℝ} (ha : 1 / 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2 + lam / 2) :
    |wideSfrac ta w d lam b - wideSfrac ta w d lam a| ≤ 2 * period * (b - a) := by
  rw [wideSfrac_chamfer₁_closed (u := b) hd (le_trans ha hab) hb,
      wideSfrac_chamfer₁_closed (u := a) hd ha (le_trans hab hb)]
  have hdiff : (ta + (1 - lam) * w + (2 * b - 1) * period)
      - (ta + (1 - lam) * w + (2 * a - 1) * period) = 2 * period * (b - a) := by ring
  rw [hdiff,
    abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) period_pos.le) (sub_nonneg.mpr hab))]

/-- **Chord zone**: the profile is affine with slope `2d ∈ [0, 2·period]`. -/
lemma wideSfrac_lip_chord {ta w d lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 4) (hw0 : 0 ≤ w)
    (hwP : w ≤ period) (hd : d = period - w) {a b : ℝ} (ha : 1 / 2 + lam / 2 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1 - lam / 2) :
    |wideSfrac ta w d lam b - wideSfrac ta w d lam a| ≤ 2 * period * (b - a) := by
  rw [wideSfrac_chord_closed (u := b) h0 hd (le_trans ha hab) hb,
      wideSfrac_chord_closed (u := a) h0 hd ha (le_trans hab hb)]
  have hdiff : (ta + w + lam * d + ((1 - 2 * lam) * d) * ((b - (1 / 2 + lam / 2)) / (1 / 2 - lam)))
      - (ta + w + lam * d + ((1 - 2 * lam) * d) * ((a - (1 / 2 + lam / 2)) / (1 / 2 - lam)))
      = (2 * d) * (b - a) := by
    rw [wideSfrac_chord_slope (d := d) (lam := lam) (x := b) (z := 1 / 2 + lam / 2) h0 h1,
        wideSfrac_chord_slope (d := d) (lam := lam) (x := a) (z := 1 / 2 + lam / 2) h0 h1]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg (by rw [hd]; linarith : (0 : ℝ) ≤ 2 * d)]
  have hdP : d ≤ period := by rw [hd]; linarith
  calc 2 * d * |b - a| ≤ (2 * period) * |b - a| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ = 2 * period * (b - a) := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]

/-- **Second chamfer**: the profile advances exactly at rate `2·period`. -/
lemma wideSfrac_lip_chamfer₂ {ta w d lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 4)
    (hd : d = period - w) {a b : ℝ} (ha : 1 - lam / 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |wideSfrac ta w d lam b - wideSfrac ta w d lam a| ≤ 2 * period * (b - a) := by
  rw [wideSfrac_chamfer₂_closed (u := b) h0 h1 hd (le_trans ha hab),
      wideSfrac_chamfer₂_closed (u := a) h0 h1 hd ha]
  have hdiff : (ta + w + (1 - lam) * d + (2 * b - 2 + lam) * period)
      - (ta + w + (1 - lam) * d + (2 * a - 2 + lam) * period) = 2 * period * (b - a) := by ring
  rw [hdiff,
    abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) period_pos.le) (sub_nonneg.mpr hab))]

/-- **Gluing two Lipschitz estimates across a common point.** -/
lemma abs_sub_le_of_chain {f : ℝ → ℝ} {C l m r : ℝ}
    (h1 : ∀ a b, l ≤ a → a ≤ b → b ≤ m → |f b - f a| ≤ C * (b - a))
    (h2 : ∀ a b, m ≤ a → a ≤ b → b ≤ r → |f b - f a| ≤ C * (b - a)) :
    ∀ a b, l ≤ a → a ≤ b → b ≤ r → |f b - f a| ≤ C * (b - a) := by
  intro a b ha hab hb
  rcases le_total b m with hbm | hmb
  · exact h1 a b ha hab hbm
  rcases le_total a m with ham | hma
  · have hA := h1 a m ha ham le_rfl
    have hB := h2 m b le_rfl hmb hb
    calc |f b - f a| = |(f b - f m) + (f m - f a)| := by ring_nf
      _ ≤ |f b - f m| + |f m - f a| := abs_add_le _ _
      _ ≤ C * (b - m) + C * (m - a) := add_le_add hB hA
      _ = C * (b - a) := by ring
  · exact h2 a b hma hab hb

/-- **The affine profile is `2·period`-Lipschitz on the profile interval.** -/
lemma wideSfrac_lipschitz {ta w d lam : ℝ} (hw0 : 0 ≤ w) (hwP : w ≤ period)
    (hd : d = period - w) (h0 : 0 < lam) (h1 : lam ≤ 1 / 4) :
    ∀ a b : ℝ, a ∈ Set.Icc 0 1 → b ∈ Set.Icc 0 1 →
      |wideSfrac ta w d lam a - wideSfrac ta w d lam b| ≤ 2 * period * |a - b| := by
  have hright : ∀ a b : ℝ, 1 / 2 ≤ a → a ≤ b → b ≤ 1 →
      |wideSfrac ta w d lam b - wideSfrac ta w d lam a| ≤ 2 * period * (b - a) :=
    abs_sub_le_of_chain
      (f := wideSfrac ta w d lam) (C := 2 * period) (l := 1 / 2) (m := 1 / 2 + lam / 2) (r := 1)
      (fun a b ha hab hb => wideSfrac_lip_chamfer₁ h0 hd ha hab hb)
      (abs_sub_le_of_chain (f := wideSfrac ta w d lam) (C := 2 * period)
        (l := 1 / 2 + lam / 2) (m := 1 - lam / 2) (r := 1)
        (fun a b ha hab hb => wideSfrac_lip_chord h0 h1 hw0 hwP hd ha hab hb)
        (fun a b ha hab hb => wideSfrac_lip_chamfer₂ h0 h1 hd ha hab hb))
  have hall : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      |wideSfrac ta w d lam b - wideSfrac ta w d lam a| ≤ 2 * period * (b - a) :=
    abs_sub_le_of_chain (f := wideSfrac ta w d lam) (C := 2 * period) (l := 0) (m := 1 / 2)
      (r := 1)
      (fun a b _ hab hb => wideSfrac_lip_arc h0 h1 hw0 hwP hab hb)
      hright
  intro a b ha hb
  rcases le_total a b with hab | hba
  · have h := hall a b ha.1 hab hb.2
    rw [abs_sub_comm (wideSfrac ta w d lam a) (wideSfrac ta w d lam b), abs_sub_comm a b,
      abs_of_nonneg (sub_nonneg.mpr hab)]
    exact h
  · have h := hall b a hb.1 hba ha.2
    rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    exact h

/-! ## The abstract estimate for the matched phase -/

/-- The matched phase written as `τ ↦ τ + (F (sweepParam τ) - sweepParam τ * period)`: the loop
parameter plus a correction which is `F` evaluated at the sawtooth. -/
def wideAbs (F : ℝ → ℝ) (τ : ℝ) : ℝ := τ + (F (sweepParam τ) - sweepParam τ * period)

/-- The phase shifts by exactly one period when the loop parameter does. -/
lemma wideAbs_add_period (F : ℝ → ℝ) (τ : ℝ) :
    wideAbs F (τ + period) = wideAbs F τ + period := by
  simp only [wideAbs, sweepParam_add_period]
  ring

/-- The phase shifts by exactly `m` periods. -/
lemma wideAbs_shift_nat (F : ℝ → ℝ) (m : ℕ) (τ : ℝ) :
    wideAbs F (τ + m * period) = wideAbs F τ + m * period := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      have h : τ + ((m : ℝ) + 1) * period = (τ + m * period) + period := by ring
      rw [hcast, h, wideAbs_add_period, ih]
      ring

/-- **The local estimate.**  If `0 ≤ r < period`, the sawtooth `sweepParam` advances by either
`r/period` or `r/period - 1`; the two Lipschitz hypotheses on `F` (`2·period`-Lipschitz on `[0,1]`
and `F 1 = F 0 + period`) control both cases, and the phase advances by at most `2r`. -/
lemma wideAbs_lip_local {F : ℝ → ℝ}
    (hF : ∀ a b : ℝ, a ∈ Set.Icc 0 1 → b ∈ Set.Icc 0 1 →
      |F a - F b| ≤ 2 * period * |a - b|)
    (hF01 : F 1 = F 0 + period)
    {τ r : ℝ} (hr0 : 0 ≤ r) (hrp : r < period) :
    |wideAbs F (τ + r) - wideAbs F τ| ≤ 2 * r := by
  have hp : 0 < period := period_pos
  set k : ℤ := ⌊(τ + r) / period⌋ - ⌊τ / period⌋ with hkdef
  have hk0 : 0 ≤ k := by
    rw [hkdef]
    exact Int.sub_nonneg.mpr (Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hp.le))
  have hk1 : k ≤ 1 := by
    rw [hkdef]
    have hlt : (τ + r) / period < (((⌊τ / period⌋ + 2 : ℤ)) : ℝ) := by
      have h1 : τ / period < ((⌊τ / period⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
      have h2 : r / period < 1 := (div_lt_one hp).mpr hrp
      have h3 : (τ + r) / period = τ / period + r / period := by ring
      rw [h3]; push_cast; linarith
    have h4 : ⌊(τ + r) / period⌋ < ⌊τ / period⌋ + 2 := Int.floor_lt.mpr hlt
    omega
  have hk01 : k = 0 ∨ k = 1 := by omega
  have hu : sweepParam (τ + r) - sweepParam τ = r / period - (k : ℝ) := by
    rw [hkdef, sweepParam, sweepParam]
    push_cast
    ring
  have hW : wideAbs F (τ + r) - wideAbs F τ
      = (F (sweepParam (τ + r)) - F (sweepParam τ)) + (k : ℝ) * period := by
    have hb : (sweepParam (τ + r) - sweepParam τ) * period = r - (k : ℝ) * period := by
      rw [hu]; field_simp
    calc wideAbs F (τ + r) - wideAbs F τ
        = r + (F (sweepParam (τ + r)) - F (sweepParam τ))
            - (sweepParam (τ + r) - sweepParam τ) * period := by
          simp only [wideAbs]; ring
      _ = (F (sweepParam (τ + r)) - F (sweepParam τ)) + (k : ℝ) * period := by
          rw [hb]; ring
  have hu1 : sweepParam τ ∈ Set.Icc 0 1 := ⟨(sweepParam_mem τ).1, (sweepParam_mem τ).2.le⟩
  have hu2 : sweepParam (τ + r) ∈ Set.Icc 0 1 :=
    ⟨(sweepParam_mem (τ + r)).1, (sweepParam_mem (τ + r)).2.le⟩
  have h01 : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, by norm_num⟩
  have h11 : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, le_rfl⟩
  rcases hk01 with hk0' | hk1'
  · have hu' : sweepParam (τ + r) - sweepParam τ = r / period := by rw [hu, hk0']; ring
    have habs : |sweepParam (τ + r) - sweepParam τ| = r / period := by
      rw [hu']; exact abs_of_nonneg (div_nonneg hr0 hp.le)
    rw [hW, hk0', Int.cast_zero, zero_mul, add_zero]
    calc |F (sweepParam (τ + r)) - F (sweepParam τ)|
        ≤ 2 * period * |sweepParam (τ + r) - sweepParam τ| := hF _ _ hu2 hu1
      _ = 2 * period * (r / period) := by rw [habs]
      _ = 2 * r := by field_simp
  · have hsum : sweepParam (τ + r) + 1 - sweepParam τ = r / period := by
      rw [show sweepParam (τ + r) + 1 - sweepParam τ
            = (sweepParam (τ + r) - sweepParam τ) + 1 by ring, hu, hk1']
      ring
    rw [hW, hk1', Int.cast_one, one_mul]
    have hsplit : F (sweepParam (τ + r)) - F (sweepParam τ) + period
        = (F (sweepParam (τ + r)) - F 0) + (F 1 - F (sweepParam τ)) := by
      rw [hF01]; ring
    rw [hsplit]
    calc |(F (sweepParam (τ + r)) - F 0) + (F 1 - F (sweepParam τ))|
        ≤ |F (sweepParam (τ + r)) - F 0| + |F 1 - F (sweepParam τ)| := abs_add_le _ _
      _ ≤ 2 * period * |sweepParam (τ + r) - 0| + 2 * period * |1 - sweepParam τ| :=
            add_le_add (hF _ _ hu2 h01) (hF _ _ h11 hu1)
      _ = 2 * period * (sweepParam (τ + r)) + 2 * period * (1 - sweepParam τ) := by
            rw [sub_zero, abs_of_nonneg hu2.1, abs_of_nonneg (by linarith [hu1.2])]
      _ = 2 * period * (r / period) := by rw [← hsum]; ring
      _ = 2 * r := by field_simp

/-- **The abstract Lipschitz estimate for the matched phase.** -/
lemma wideAbs_lipschitz {F : ℝ → ℝ}
    (hF : ∀ a b : ℝ, a ∈ Set.Icc 0 1 → b ∈ Set.Icc 0 1 →
      |F a - F b| ≤ 2 * period * |a - b|)
    (hF01 : F 1 = F 0 + period) :
    ∀ τ₁ τ₂ : ℝ, |wideAbs F τ₁ - wideAbs F τ₂| ≤ 2 * |τ₁ - τ₂| := by
  have hp : 0 < period := period_pos
  have hmain : ∀ τ₁ τ₂ : ℝ, τ₁ ≤ τ₂ → |wideAbs F τ₁ - wideAbs F τ₂| ≤ 2 * |τ₁ - τ₂| := by
    intro τ₁ τ₂ hle
    have hd0 : 0 ≤ τ₂ - τ₁ := sub_nonneg.mpr hle
    set m : ℕ := ⌊(τ₂ - τ₁) / period⌋.toNat with hmdef
    set s : ℝ := (τ₂ - τ₁) - m * period with hsdef
    have hfloor0 : 0 ≤ ⌊(τ₂ - τ₁) / period⌋ :=
      Int.le_floor.mpr (by push_cast; exact div_nonneg hd0 hp.le)
    have hmcastZ : (m : ℤ) = ⌊(τ₂ - τ₁) / period⌋ := by
      rw [hmdef]; exact Int.toNat_of_nonneg hfloor0
    have hmcast : (m : ℝ) = ((⌊(τ₂ - τ₁) / period⌋ : ℤ) : ℝ) := by
      rw [← hmcastZ]; push_cast; ring
    have hms : (m : ℝ) * period ≤ τ₂ - τ₁ := by
      have h := Int.floor_le ((τ₂ - τ₁) / period)
      calc (m : ℝ) * period = ((⌊(τ₂ - τ₁) / period⌋ : ℤ) : ℝ) * period := by rw [hmcast]
        _ ≤ ((τ₂ - τ₁) / period) * period := mul_le_mul_of_nonneg_right h hp.le
        _ = τ₂ - τ₁ := by field_simp
    have hsp : s < period := by
      have h := Int.lt_floor_add_one ((τ₂ - τ₁) / period)
      have h2 : τ₂ - τ₁ < ((m : ℝ) + 1) * period := by
        have h3 : ((⌊(τ₂ - τ₁) / period⌋ : ℤ) : ℝ) + 1 ≤ (m : ℝ) + 1 := by
          linarith [hmcast]
        calc τ₂ - τ₁ = ((τ₂ - τ₁) / period) * period := by field_simp
          _ < (((⌊(τ₂ - τ₁) / period⌋ : ℤ) : ℝ) + 1) * period :=
                mul_lt_mul_of_pos_right h hp
          _ ≤ ((m : ℝ) + 1) * period := mul_le_mul_of_nonneg_right h3 hp.le
      rw [hsdef]; linarith
    have hs0 : 0 ≤ s := by rw [hsdef]; linarith
    have hsplit : τ₂ = (τ₁ + m * period) + s := by rw [hsdef]; ring
    have hloc := wideAbs_lip_local hF hF01 (τ := τ₁ + m * period) (r := s) hs0 hsp
    have hshift := wideAbs_shift_nat F m τ₁
    have hshift' : wideAbs F ((τ₁ + m * period) + s) - wideAbs F τ₁
        = (wideAbs F ((τ₁ + m * period) + s) - wideAbs F (τ₁ + m * period)) + m * period := by
      rw [hshift]; ring
    have hmp : 0 ≤ (m : ℝ) * period := mul_nonneg (Nat.cast_nonneg m) hp.le
    calc |wideAbs F τ₁ - wideAbs F τ₂| = |wideAbs F ((τ₁ + m * period) + s) - wideAbs F τ₁| := by
          rw [hsplit, abs_sub_comm]
      _ = |(wideAbs F ((τ₁ + m * period) + s) - wideAbs F (τ₁ + m * period)) + m * period| := by
          rw [hshift']
      _ ≤ |wideAbs F ((τ₁ + m * period) + s) - wideAbs F (τ₁ + m * period)| + |(m : ℝ) * period| :=
          abs_add_le _ _
      _ ≤ 2 * s + m * period := by rw [abs_of_nonneg hmp]; linarith [hloc]
      _ ≤ 2 * (τ₂ - τ₁) := by rw [hsdef] at *; linarith
      _ = 2 * |τ₁ - τ₂| := by rw [abs_of_nonpos (sub_nonpos.mpr hle)]; ring
  intro τ₁ τ₂
  rcases le_total τ₁ τ₂ with hle | hle
  · exact hmain τ₁ τ₂ hle
  · have h := hmain τ₂ τ₁ hle
    rw [abs_sub_comm (wideAbs F τ₁) (wideAbs F τ₂), abs_sub_comm τ₁ τ₂]
    exact h

/-! ## The matched phase of the wide end -/

/-- The phase `wideSigma` of `sweepFamWideTolDefs` is the abstract phase `wideAbs` of the affine
profile `wideSfrac`. -/
lemma wideSigma_eq_wideAbs (ta w d lam : ℝ) :
    wideSigma ta w d lam = wideAbs (wideSfrac ta w d lam) := rfl

theorem wideSig_tau_lipschitz {d : LeanEval.KnotTheory.Quadrisecant.BandArcData}
    (D : Work.Drive.SweepData d) :
    ∀ (lam σ τ₁ τ₂ : ℝ), 0 < lam → lam ≤ 1 / 4 →
      |Work.Drive.wideSig D lam σ τ₁ - Work.Drive.wideSig D lam σ τ₂| ≤ 2 * |τ₁ - τ₂| := by
  intro lam σ τ₁ τ₂ h0 h1
  have hw : 0 ≤ sweepW' D σ ∧ sweepW' D σ ≤ period := wideSig_sweepW'_bounds D σ
  have hF : ∀ a b : ℝ, a ∈ Set.Icc 0 1 → b ∈ Set.Icc 0 1 →
      |wideSfrac (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam a
        - wideSfrac (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam b|
        ≤ 2 * period * |a - b| :=
    wideSfrac_lipschitz hw.1 hw.2 rfl h0 h1
  have hF01 : wideSfrac (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam 1
      = wideSfrac (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam 0 + period :=
    wideSfrac_periodicity h0 (by linarith)
  have h := wideAbs_lipschitz hF hF01 τ₁ τ₂
  have hconv : ∀ τ : ℝ, wideSig D lam σ τ
      = wideAbs (wideSfrac (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam) τ :=
    fun τ => rfl
  rw [hconv τ₁, hconv τ₂]
  exact h

end Work.Drive
