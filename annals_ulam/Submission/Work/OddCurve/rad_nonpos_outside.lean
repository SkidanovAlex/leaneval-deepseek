import Mathlib
import Submission.Work.OddCurve.Defs

/-!
# `rad ≤ 0` outside the cut section

For an envelope curve `H : IsEnvelopeCurve h x y` and a slope `s > 0` the radicand

  `rad h (envelopeProfile h x y) s t = f t ^ 2 - (s * t + h s) ^ 2`

of the two moment equations is non-positive for every `t` outside the cut section
`[-(x s), y s]`.

Only three ingredients are used:

* the two root conditions `f (y s) = s * y s + h s` and
  `f (-(x s)) = -(s * (-(x s)) + h s)` (so that the two endpoints of the section sit exactly on
  the cutting line);
* the vanishing of the profile at `±1` (so that `f t = 0` beyond the body);
* the fact that each branch of the envelope is the inverse of the strictly increasing curve
  `σ ↦ σ c σ + p σ` and hence *strictly decreasing* on `(0,1)`
  (`IsEnvelopeBranch.envelopeRight_strictAntiOn` below).

The last point replaces the (false) claim that `f` itself is monotone on `(-1,1)`: the profile
increases on `(-1,0)` and decreases on `(0,1)`, and the two cases of the disjunction `t ≤ -(x s)`
resp. `y s ≤ t` are exactly the two sides of this maximum at `0`.
-/

namespace Work.OddEnvelope

noncomputable section

open Set Filter
open scoped Topology

variable {p c : ℝ → ℝ}

/-- **The right branch of an envelope is strictly decreasing on `(0,1)`.**

`envelopeRight p c` is the composite `(σ ↦ σ * c σ + p σ) ∘ slopeRight c`: the outer map is
strictly increasing on `(0,∞)` (`IsEnvelopeBranch.strictMonoOn_curve`) and `slopeRight c` is
strictly decreasing (`IsChordCurve.slopeRight_strictAntiOn`), so the composite is strictly
decreasing. -/
lemma IsEnvelopeBranch.envelopeRight_strictAntiOn (hb : IsEnvelopeBranch p c) :
    StrictAntiOn (envelopeRight p c) (Set.Ioo (0 : ℝ) 1) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  have hσ₁ : 0 < slopeRight c t₁ := hb.toIsChordCurve.slopeRight_pos ht₁
  have hσ₂ : 0 < slopeRight c t₂ := hb.toIsChordCurve.slopeRight_pos ht₂
  have hlt' : slopeRight c t₂ < slopeRight c t₁ :=
    hb.toIsChordCurve.slopeRight_strictAntiOn ht₁ ht₂ hlt
  have hmono := hb.strictMonoOn_curve hσ₂ hσ₁ hlt'
  have e₁ : envelopeRight p c t₁
      = slopeRight c t₁ * c (slopeRight c t₁) + p (slopeRight c t₁) := by
    rw [envelopeRight, hb.toIsChordCurve.slopeRight_eq ht₁]
  have e₂ : envelopeRight p c t₂
      = slopeRight c t₂ * c (slopeRight c t₂) + p (slopeRight c t₂) := by
    rw [envelopeRight, hb.toIsChordCurve.slopeRight_eq ht₂]
  rw [e₁, e₂]
  exact hmono

end

end Work.OddEnvelope

namespace Work.OddCurve

noncomputable section

open Set Filter
open scoped Topology

theorem rad_nonpos_outside {h x y : ℝ → ℝ} (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    {s : ℝ} (hs : 0 < s) {t : ℝ} (ht : t ≤ -(x s) ∨ y s ≤ t) :
    Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t ≤ 0 := by
  have hx0 : 0 < x s := H.toChordCurve_x.pos hs
  have hx1 : x s < 1 := H.toChordCurve_x.lt_one hs
  have hy0 : 0 < y s := H.toChordCurve_y.pos hs
  have hy1 : y s < 1 := H.toChordCurve_y.lt_one hs
  have hxmem : x s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have hymem : y s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hy0, hy1⟩
  -- the two endpoints of the section lie on the cutting line
  have hrootL : Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (x s)
      = s * x s - h s := by
    have hsr : s = Work.OddEnvelope.slopeRight x (x s) :=
      H.toChordCurve_x.slopeRight_eq_of hxmem hs rfl
    rw [Work.OddEnvelope.envelopeRight, ← hsr, Work.OddEnvelope.negH]
    ring
  have hrootR : Work.OddEnvelope.envelopeRight h y (y s) = s * y s + h s := by
    have hsr : s = Work.OddEnvelope.slopeRight y (y s) :=
      H.toChordCurve_y.slopeRight_eq_of hymem hs rfl
    rw [Work.OddEnvelope.envelopeRight, ← hsr]
  have key : (Work.OddEnvelope.envelopeProfile h x y t) ^ 2 ≤ (s * t + h s) ^ 2 := by
    rcases ht with ht | ht
    · -- `t ≤ -(x s)`: the left branch is increasing along `t`, the line is decreasing
      rcases le_or_gt t (-1) with ht1 | ht1
      · -- `t ≤ -1`: the profile vanishes
        have hft : Work.OddEnvelope.envelopeProfile h x y t = 0 :=
          Work.OddEnvelope.envelopeProfile_eq_zero (by intro hc; linarith [hc.1])
            (by intro hc; linarith [hc.1]) (by linarith)
        rw [hft, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        exact sq_nonneg _
      · have htmem0 : t ∈ Set.Ioo (-1 : ℝ) 0 := ⟨ht1, by linarith⟩
        have hft : Work.OddEnvelope.envelopeProfile h x y t
            = Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (-t) := by
          rw [Work.OddEnvelope.envelopeProfile_of_neg htmem0,
            Work.OddEnvelope.envelopeLeft_eq_negH]
        have humem : -t ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        have hle_u : x s ≤ -t := by linarith
        have hmono := (H.isEnvelopeBranch_left).envelopeRight_strictAntiOn.antitoneOn
          hxmem humem hle_u
        have hft_nonneg : 0 ≤ Work.OddEnvelope.envelopeProfile h x y t :=
          le_of_lt (Work.OddEnvelope.envelopeProfile_pos H ⟨ht1, by linarith⟩)
        have hle1 : Work.OddEnvelope.envelopeProfile h x y t ≤ -(s * t + h s) := by
          rw [hft]
          calc Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (-t)
              ≤ Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (x s) := hmono
            _ = s * x s - h s := hrootL
            _ ≤ -(s * t + h s) := by
                nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.le (by linarith : t + x s ≤ 0)]
        have h1 : (Work.OddEnvelope.envelopeProfile h x y t) ^ 2
            ≤ (-(s * t + h s)) ^ 2 := by
          rw [pow_two, pow_two]
          exact mul_self_le_mul_self hft_nonneg hle1
        linarith [h1, neg_sq (s * t + h s)]
    · -- `y s ≤ t`: the right branch is decreasing along `t`, the line is increasing
      rcases le_or_gt 1 t with ht1 | ht1
      · -- `1 ≤ t`: the profile vanishes
        have hft : Work.OddEnvelope.envelopeProfile h x y t = 0 :=
          Work.OddEnvelope.envelopeProfile_eq_zero (by intro hc; linarith [hc.2])
            (by intro hc; linarith [hc.2]) (by linarith)
        rw [hft, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        exact sq_nonneg _
      · have htmem0 : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, ht1⟩
        have hft : Work.OddEnvelope.envelopeProfile h x y t
            = Work.OddEnvelope.envelopeRight h y t :=
          Work.OddEnvelope.envelopeProfile_of_pos htmem0
        have hmono := (H.isEnvelopeBranch_right).envelopeRight_strictAntiOn.antitoneOn
          hymem htmem0 ht
        have hft_nonneg : 0 ≤ Work.OddEnvelope.envelopeProfile h x y t :=
          le_of_lt (Work.OddEnvelope.envelopeProfile_pos H ⟨by linarith, ht1⟩)
        have hle1 : Work.OddEnvelope.envelopeProfile h x y t ≤ s * t + h s := by
          rw [hft]
          calc Work.OddEnvelope.envelopeRight h y t
              ≤ Work.OddEnvelope.envelopeRight h y (y s) := hmono
            _ = s * y s + h s := hrootR
            _ ≤ s * t + h s := by nlinarith [mul_nonneg hs.le (by linarith : (0 : ℝ) ≤ t - y s)]
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self hft_nonneg hle1
  rw [Work.OddCurve.rad_def]
  linarith

end

end Work.OddCurve
