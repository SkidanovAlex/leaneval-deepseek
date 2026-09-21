import Mathlib
import Submission.Work.OddEnvelope.Main
import Submission.Work.OddEnvelope.NonDegenerate
import Submission.Work.OddVolterra.RowIdentity.momentF_eq_AA_add_WW

/-!
# Positivity of the frozen endpoint factors of an envelope curve

For the chord-endpoint curve `(x,y)` of the odd-dimensional Ulam construction and the perturbation
`h` — i.e. the data of `Work.OddEnvelope.IsEnvelopeCurve h x y` — the two endpoint factors

`Qy h y u σ = (y σ + H(u,σ)) * (L(σ,y σ) + L(u,y σ))`,
`Qx h x u σ = (-x σ + H(u,σ)) * (L(σ,-x σ) + L(u,-x σ))`

(`H(u,σ) = hquot h u σ` the divided difference of `h`, `L(s,t) = s t + h s` the cutting line) are
strictly positive for `0 < u ≤ σ ≤ 1`.  These are the two factors whose positivity makes the Abel
denominator `Kden h u σ (y σ) = √ (Qy h y u σ)`, `Kden h u σ (-x σ) = √ (Qx h x u σ)` strictly
positive, hence the manifest kernels smooth on the transition window.

## Proof

* **The factorisation.**  The divided-difference identity `h σ - h u = (σ - u) · H(u,σ)`
  (`Work.OddVolterra.sub_mul_hquot`) splits the frozen radicand
  `ψ u f (y σ) = f (y σ)² - L(u,y σ)²` as the product of `(σ - u) · Qy h y u σ` — because the
  root condition says `f (y σ) = L(σ,y σ)`, so the difference of the two squares factors as
  `(L(σ,y σ) - L(u,y σ)) · (L(σ,y σ) + L(u,y σ))` and the first factor is
  `(σ - u) · (y σ + H(u,σ))`.  The same computation with `t = -x σ` and the root condition
  `f (-x σ) = -L(σ,-x σ)` gives `(σ - u) · Qx h x u σ = L(σ,-x σ)² - L(u,-x σ)²`.
* **Non-degeneracy.**  For `u < σ` the points `y σ` and `-x σ` lie strictly inside the section
  `(-(x u), y u)` of slope `u` (the curves `x`, `y` are strictly decreasing and positive), and the
  envelope profile is strictly above the cutting line there
  (`Work.OddEnvelope.envelopeProfile_sub_sq_pos`).  Hence the two radicands are positive and
  `σ - u > 0` transfers this to `Qy` and `Qx`.
* **The diagonal `σ = u`.**  There the divided difference degenerates to `h' u`
  (`Work.OddVolterra.hquot_self`), the line at slope `u` contributes twice
  (`2 * (u * y u + h u) > 0` resp. `2 * (u * (-(x u)) + h u) < 0` — positivity of the profile at
  the two intersection points), and the second factor `y u + h' u > 0` resp.
  `-(x u) + h' u < 0` comes from the monotonicity hypotheses `mono_y`, `mono_x` together with
  `deriv y u < 0`, `deriv x u < 0`.
-/

namespace Work.OddVolterra.Smooth

open Set Filter
open scoped Topology ContDiff
open Work.OddVolterra (line hquot)
open Work.OddVolterra.RowIdentity (Qy Qx)

noncomputable section

/-! ### The perturbation is globally `C¹` -/

/-- The perturbation `h` of an envelope curve vanishes identically below the transition window
`[1 - 2τ, 1 - τ]` (its support is contained there), while the hypothesis `smooth_h` gives
smoothness on `(0,∞)`.  Those two open sets cover the line, so `h` is `C¹` on all of `ℝ` — the
form in which `Work.OddVolterra.sub_mul_hquot` consumes it. -/
lemma contDiff_one_of_isEnvelopeCurve {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) : ContDiff ℝ 1 h := by
  have hzero : ∀ z : ℝ, z < 1 - 2 * Work.OddEnvelope.tau → h z = 0 := by
    intro z hz
    by_contra hne
    have hmem := H.h_support hne
    have h1 : (1 : ℝ) - 2 * Work.OddEnvelope.tau ≤ z := hmem.1
    have h2 : (1 : ℝ) - 2 * Work.OddEnvelope.tau = 4 / 5 := by
      norm_num [Work.OddEnvelope.tau]
    linarith
  rw [contDiff_iff_contDiffAt]
  intro a
  by_cases ha : 0 < a
  · exact (H.smooth_h.contDiffAt (isOpen_Ioi.mem_nhds ha)).of_le (by norm_num)
  · have ha' : a ≤ 0 := le_of_not_gt ha
    have h1 : (0 : ℝ) < 1 - 2 * Work.OddEnvelope.tau := by
      norm_num [Work.OddEnvelope.tau]
    have hamem : a ∈ Set.Iio (1 - 2 * Work.OddEnvelope.tau) := lt_of_le_of_lt ha' h1
    exact contDiffAt_const.congr_of_eventuallyEq
      (eventuallyEq_of_mem (isOpen_Iio.mem_nhds hamem) (fun z hz => hzero z hz))

/-! ### The two factorisations of the frozen radicand -/

/-- The `y`-endpoint factorisation: `(σ - u) · Qy h y u σ` is the difference of the two squares
`L(σ,y σ)² - L(u,y σ)²`. -/
lemma sub_mul_Qy {h y : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (u σ : ℝ) :
    (σ - u) * Qy h y u σ = (σ * y σ + h σ) ^ 2 - (u * y σ + h u) ^ 2 := by
  have hsub := Work.OddVolterra.sub_mul_hquot hh u σ
  have hA : (σ - u) * (y σ + hquot h u σ) = (σ * y σ + h σ) - (u * y σ + h u) := by
    rw [mul_add, ← hsub]
    ring
  have hexp : line h σ (y σ) + line h u (y σ) =
      (σ * y σ + h σ) + (u * y σ + h u) := by
    unfold line
    ring
  unfold Qy
  rw [hexp, ← mul_assoc, hA]
  ring

/-- The `-x`-endpoint factorisation: `(σ - u) · Qx h x u σ` is the difference of the two squares
`L(σ,-x σ)² - L(u,-x σ)²`. -/
lemma sub_mul_Qx {h x : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (u σ : ℝ) :
    (σ - u) * Qx h x u σ =
      (σ * (-(x σ)) + h σ) ^ 2 - (u * (-(x σ)) + h u) ^ 2 := by
  have hsub := Work.OddVolterra.sub_mul_hquot hh u σ
  have hA : (σ - u) * (-(x σ) + hquot h u σ) =
      (σ * (-(x σ)) + h σ) - (u * (-(x σ)) + h u) := by
    rw [mul_add, ← hsub]
    ring
  have hexp : line h σ (-(x σ)) + line h u (-(x σ)) =
      (σ * (-(x σ)) + h σ) + (u * (-(x σ)) + h u) := by
    unfold line
    ring
  unfold Qx
  rw [hexp, ← mul_assoc, hA]
  ring

/-! ### The main statement -/

/-- **Strict positivity of the two frozen endpoint factors** for the chord-endpoint curve of an
envelope curve: `Qy h y u σ > 0` and `Qx h x u σ > 0` for all `0 < u ≤ σ ≤ 1`. -/
theorem Qy_pos_of_isEnvelopeCurve {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) :
    ∀ u σ : ℝ, 0 < u → u ≤ σ → σ ≤ 1 →
      0 < Work.OddVolterra.RowIdentity.Qy h y u σ ∧
      0 < Work.OddVolterra.RowIdentity.Qx h x u σ := by
  have hh := contDiff_one_of_isEnvelopeCurve H
  intro u σ hu huσ _
  rcases lt_or_eq_of_le huσ with hlt | heq
  · -- off the diagonal: both endpoint points lie strictly inside the section of slope `u`
    have hσpos : 0 < σ := lt_trans hu hlt
    have hyσ : y σ < y u := H.toChordCurve_y.strictAntiOn hu hσpos hlt
    have hxσ : x σ < x u := H.toChordCurve_x.strictAntiOn hu hσpos hlt
    have hxσpos : 0 < x σ := H.toChordCurve_x.pos hσpos
    have hyσpos : 0 < y σ := H.toChordCurve_y.pos hσpos
    have hyupos : 0 < y u := H.toChordCurve_y.pos hu
    have hsub : 0 < σ - u := by linarith
    have hnd := Work.OddEnvelope.concaveOn_envelopeProfile H
    have hme_y : y σ ∈ Set.Ioo (-(x u)) (y u) := ⟨by linarith, hyσ⟩
    have hndy := Work.OddEnvelope.envelopeProfile_sub_sq_pos H hnd hu (y σ) hme_y
    rw [Work.OddEnvelope.envelopeProfile_root_right H hσpos] at hndy
    have hme_x : -(x σ) ∈ Set.Ioo (-(x u)) (y u) := ⟨by linarith, by linarith⟩
    have hndx := Work.OddEnvelope.envelopeProfile_sub_sq_pos H hnd hu (-(x σ)) hme_x
    rw [Work.OddEnvelope.envelopeProfile_root_left H hσpos] at hndx
    refine ⟨?_, ?_⟩
    · have hmul : 0 < (σ - u) * Qy h y u σ := by
        rw [sub_mul_Qy hh u σ]
        exact hndy
      exact pos_of_mul_pos_right hmul hsub.le
    · have hmul : 0 < (σ - u) * Qx h x u σ := by
        rw [sub_mul_Qx hh u σ]
        rw [show (σ * (-(x σ)) + h σ) ^ 2 = (-(σ * (-(x σ)) + h σ)) ^ 2 from
          (neg_sq _).symm]
        exact hndx
      exact pos_of_mul_pos_right hmul hsub.le
  · -- the diagonal `σ = u`: the divided difference degenerates to `h' u`
    have hσu : σ = u := heq.symm
    rw [hσu]
    have hquot_s : hquot h u u = deriv h u := Work.OddVolterra.hquot_self h u
    have hmem := Work.OddEnvelope.envelopeProfile_mem_Ioo H hu
    have hA : 0 < y u + deriv h u := by
      have h1 := H.mono_y u hu
      have h2 : u * deriv y u < 0 := mul_neg_of_pos_of_neg hu (H.y_deriv_neg u hu)
      linarith
    have hB : 0 < u * y u + h u := by
      have h1 := Work.OddEnvelope.envelopeProfile_root_right H hu
      have h2 := Work.OddEnvelope.envelopeProfile_pos H hmem.2
      linarith
    have hC : -(x u) + deriv h u < 0 := by
      have h1 := H.mono_x u hu
      have h2 : u * deriv x u < 0 := mul_neg_of_pos_of_neg hu (H.x_deriv_neg u hu)
      linarith
    have hD : u * (-(x u)) + h u < 0 := by
      have h1 := Work.OddEnvelope.envelopeProfile_root_left H hu
      have h2 := Work.OddEnvelope.envelopeProfile_pos H hmem.1
      linarith
    have hly : line h u (y u) + line h u (y u) = 2 * (u * y u + h u) := by
      unfold line
      ring
    have hlx : line h u (-(x u)) + line h u (-(x u)) = 2 * (u * (-(x u)) + h u) := by
      unfold line
      ring
    refine ⟨?_, ?_⟩
    · unfold Qy
      rw [hquot_s, hly]
      exact mul_pos hA (by linarith)
    · unfold Qx
      rw [hquot_s, hlx]
      exact mul_pos_of_neg_of_neg hC (by linarith)

end

end Work.OddVolterra.Smooth
