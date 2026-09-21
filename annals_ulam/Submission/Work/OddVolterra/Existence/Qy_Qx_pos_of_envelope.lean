import Mathlib
import Submission.Work.OddVolterra.RowIdentity.Basic
import Submission.Work.OddVolterra.RowIdentity.momentF_eq_AA_add_WW
import Submission.Work.OddEnvelope.Main

namespace Work.OddVolterra.Existence

open Work.OddVolterra.RowIdentity

/-!
# Positivity of the frozen endpoint factors `Qy`, `Qx` for an envelope curve

The two functions

`Qy h y u σ = (y σ + H(u,σ)) * (L(σ,y σ) + L(u,y σ))`,
`Qx h x u σ = (-x σ + H(u,σ)) * (L(σ,-x σ) + L(u,-x σ))`

are the two endpoint factors of the frozen radicand `ψ u (·)`:  if `f` is the envelope profile
of `(h,x,y)` then

`ψ u f (y σ)     = (σ - u) * Qy h y u σ`,
`ψ u f (-x σ)    = (σ - u) * Qx h x u σ`.

(Indeed the root condition gives `f (y σ) = L(σ,y σ)`, so `ψ u f (y σ)` is the difference of
two squares, and the first factor of that difference is `(σ-u) y σ + h σ - h u`,
which is `(σ-u) * (y σ + H(u,σ))` by the divided-difference identity.)

The lemma below evaluates both sides at the section of slope `s`: for `s < σ` the points
`y σ` and `-x σ` both lie strictly inside the section `(-x s, y s)` of slope `s` (because `x`
and `y` are strictly decreasing), so the *non-degeneracy* of that section — a formal consequence
of the concavity of the envelope profile, `envelopeProfile_sub_sq_pos` — makes both radicands
positive, and `σ - s > 0` transfers this to `Qy`, `Qx`.  At the diagonal `σ = s` the
divided differences degenerate to `h' s` and one uses the monotonicity conditions `mono_y`,
`mono_x` instead.
-/

/-- The `y`-endpoint factorisation of the frozen radicand: `(σ - u) * Qy h y u σ` is the
difference of the two squares `L(σ,y σ)² - L(u,y σ)²`. -/
lemma sub_mul_Qy {h y : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (s σ : ℝ) :
    (σ - s) * Qy h y s σ = (σ * y σ + h σ) ^ 2 - (s * y σ + h s) ^ 2 := by
  have hsub := sub_mul_hquot hh s σ
  have hA : (σ - s) * (y σ + hquot h s σ) =
      (σ * y σ + h σ) - (s * y σ + h s) := by
    rw [mul_add, ← hsub]
    ring
  have hexp : line h σ (y σ) + line h s (y σ) =
      (σ * y σ + h σ) + (s * y σ + h s) := by
    unfold line
    ring
  unfold Qy
  rw [hexp, ← mul_assoc, hA]
  ring

/-- The `-x`-endpoint factorisation of the frozen radicand: `(σ - u) * Qx h x u σ` is the
difference of the two squares `L(σ,-x σ)² - L(u,-x σ)²`. -/
lemma sub_mul_Qx {h x : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (s σ : ℝ) :
    (σ - s) * Qx h x s σ =
      (σ * (-(x σ)) + h σ) ^ 2 - (s * (-(x σ)) + h s) ^ 2 := by
  have hsub := sub_mul_hquot hh s σ
  have hA : (σ - s) * (-(x σ) + hquot h s σ) =
      (σ * (-(x σ)) + h σ) - (s * (-(x σ)) + h s) := by
    rw [mul_add, ← hsub]
    ring
  have hexp : line h σ (-(x σ)) + line h s (-(x σ)) =
      (σ * (-(x σ)) + h σ) + (s * (-(x σ)) + h s) := by
    unfold line
    ring
  unfold Qx
  rw [hexp, ← mul_assoc, hA]
  ring

theorem Qy_Qx_pos_of_envelope {h x y : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) :
    ∀ s σ : ℝ, 0 < s → s ≤ σ →
      0 < Work.OddVolterra.RowIdentity.Qy h y s σ ∧
      0 < Work.OddVolterra.RowIdentity.Qx h x s σ := by
  intro s σ hs hsle
  have hσpos : 0 < σ := lt_of_lt_of_le hs hsle
  have hmem := Work.OddEnvelope.envelopeProfile_mem_Ioo H hs
  rcases lt_or_eq_of_le hsle with hlt | heq
  · -- off the diagonal: the two endpoint points lie inside the section of slope `s`
    have hyσ : y σ < y s := H.toChordCurve_y.strictAntiOn hs hσpos hlt
    have hxσ : x σ < x s := H.toChordCurve_x.strictAntiOn hs hσpos hlt
    have hxpos : 0 < x s := H.toChordCurve_x.pos hs
    have hyσpos : 0 < y σ := H.toChordCurve_y.pos hσpos
    have hxσpos : 0 < x σ := H.toChordCurve_x.pos hσpos
    have hsub : 0 < σ - s := by linarith
    have hnd := Work.OddEnvelope.concaveOn_envelopeProfile H
    have hme_y : y σ ∈ Set.Ioo (-(x s)) (y s) :=
      ⟨by linarith, hyσ⟩
    have hndy := Work.OddEnvelope.envelopeProfile_sub_sq_pos H hnd hs (y σ) hme_y
    rw [Work.OddEnvelope.envelopeProfile_root_right H hσpos] at hndy
    have hme_x : -(x σ) ∈ Set.Ioo (-(x s)) (y s) :=
      ⟨by linarith, by linarith⟩
    have hndx := Work.OddEnvelope.envelopeProfile_sub_sq_pos H hnd hs (-(x σ)) hme_x
    rw [Work.OddEnvelope.envelopeProfile_root_left H hσpos] at hndx
    refine ⟨?_, ?_⟩
    · have hmul : 0 < (σ - s) * Qy h y s σ := by
        rw [sub_mul_Qy (y := y) hh s σ]
        exact hndy
      exact pos_of_mul_pos_right hmul hsub.le
    · have hmul : 0 < (σ - s) * Qx h x s σ := by
        rw [sub_mul_Qx (x := x) hh s σ]
        rw [show (σ * (-(x σ)) + h σ) ^ 2 = (-(σ * (-(x σ)) + h σ)) ^ 2 from (neg_sq _).symm]
        exact hndx
      exact pos_of_mul_pos_right hmul hsub.le
  · -- the diagonal `σ = s`
    have hσs : σ = s := heq.symm
    rw [hσs]
    have hquot_s : hquot h s s = deriv h s := hquot_self h s
    have hA : 0 < y s + deriv h s := by
      have h1 := H.mono_y s hs
      have h2 : s * deriv y s < 0 := mul_neg_of_pos_of_neg hs (H.y_deriv_neg s hs)
      linarith
    have hB : 0 < s * y s + h s := by
      have h1 := Work.OddEnvelope.envelopeProfile_root_right H hs
      have h2 := Work.OddEnvelope.envelopeProfile_pos H hmem.2
      linarith
    have hC : -(x s) + deriv h s < 0 := by
      have h1 := H.mono_x s hs
      have h2 : s * deriv x s < 0 := mul_neg_of_pos_of_neg hs (H.x_deriv_neg s hs)
      linarith
    have hD : s * (-(x s)) + h s < 0 := by
      have h1 := Work.OddEnvelope.envelopeProfile_root_left H hs
      have h2 := Work.OddEnvelope.envelopeProfile_pos H hmem.1
      linarith
    have hly : line h s (y s) + line h s (y s) = 2 * (s * y s + h s) := by
      unfold line; ring
    have hlx : line h s (-(x s)) + line h s (-(x s)) = 2 * (s * (-(x s)) + h s) := by
      unfold line; ring
    refine ⟨?_, ?_⟩
    · unfold Qy
      rw [hquot_s, hly]
      exact mul_pos hA (by linarith)
    · unfold Qx
      rw [hquot_s, hlx]
      exact mul_pos_of_neg_of_neg hC (by linarith)

end Work.OddVolterra.Existence
