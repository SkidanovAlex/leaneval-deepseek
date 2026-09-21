import Mathlib
import Submission.Work.OddVolterra.Free.Defs

namespace Work.OddVolterra.Free

open Set Filter
open scoped Topology ContDiff

/-- **The chord equalities for the untruncated (free-tip) envelope profile.**

If `x` and `y` are smooth on `(0,∞)`, strictly decreasing and positive there, then the two
branches of `envProfileFree h x y` evaluate on the cutting section exactly on the chord:
`envProfileFree h x y (y s) = s * y s + h s` and
`envProfileFree h x y (-(x s)) = -(s * (-(x s)) + h s)` for every slope `s > 0`.

The only content is that `y` (resp. `x`) is injective on `(0,∞)`, so that the chosen preimage
`slopeRight y (y s)` (resp. `slopeLeft x (-(x s))`) is `s` again; monotonicity follows from the
sign of the derivative.  Unlike the tip-normalised `IsEnvelopeCurve` version this uses no
information about the size of the tips, only positivity. -/
theorem envProfileFree_chord (h x y : ℝ → ℝ)
    (hx : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) x (Set.Ioi 0))
    (hy : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) y (Set.Ioi 0))
    (hdecx : ∀ s : ℝ, 0 < s → deriv x s < 0) (hdecy : ∀ s : ℝ, 0 < s → deriv y s < 0)
    (hposx : ∀ s : ℝ, 0 < s → 0 < x s) (hposy : ∀ s : ℝ, 0 < s → 0 < y s) :
    (∀ s : ℝ, 0 < s → Work.OddVolterra.Free.envProfileFree h x y (y s) = s * y s + h s) ∧
    (∀ s : ℝ, 0 < s →
      Work.OddVolterra.Free.envProfileFree h x y (-(x s)) = -(s * (-(x s)) + h s)) := by
  -- `x` and `y` are strictly antitone on `(0,∞)`, hence injective there.
  have hInjy : Set.InjOn y (Set.Ioi 0) :=
    (strictAntiOn_of_deriv_neg (convex_Ioi 0) hy.continuousOn (by
      intro t ht
      rw [interior_Ioi] at ht
      exact hdecy t ht)).injOn
  have hInjx : Set.InjOn x (Set.Ioi 0) :=
    (strictAntiOn_of_deriv_neg (convex_Ioi 0) hx.continuousOn (by
      intro t ht
      rw [interior_Ioi] at ht
      exact hdecx t ht)).injOn
  refine ⟨?_, ?_⟩
  · intro s hs
    have hypos : 0 < y s := hposy s hs
    have hσ : Work.OddEnvelope.slopeRight y (y s) = s := by
      rw [Work.OddEnvelope.slopeRight]
      exact hInjy.leftInvOn_invFunOn hs
    rw [Work.OddVolterra.Free.envProfileFree, if_pos hypos,
      Work.OddEnvelope.envelopeRight, hσ]
  · intro s hs
    have hxpos : 0 < x s := hposx s hs
    have hneg : ¬ (0 < -(x s)) := by linarith
    have hneg2 : -(x s) < 0 := by linarith
    have hσ : Work.OddEnvelope.slopeLeft x (-(x s)) = s := by
      rw [Work.OddEnvelope.slopeLeft, neg_neg]
      exact hInjx.leftInvOn_invFunOn hs
    rw [Work.OddVolterra.Free.envProfileFree, if_neg hneg, if_pos hneg2,
      Work.OddEnvelope.envelopeLeft, hσ]

end Work.OddVolterra.Free
