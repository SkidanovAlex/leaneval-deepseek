import Submission.Work.OddEnvelope.Smooth
import Submission.Work.OddEnvelope.Concave
import Submission.Work.OddEnvelope.NonDegenerate
import Submission.Work.OddEnvelope.NonEven
import Submission.Work.OddEnvelope.Basic.continuousOn_envelopeProfile

/-!
# The envelope profile of the odd case

This is the interface file of the `Work.OddEnvelope` chapter.  From a *chord-endpoint curve*
`(x, y)` and a perturbation `h` (the data of `IsEnvelopeCurve`, produced e.g. by the Volterra
construction of `Work.OddVolterra`) we build the profile `envelopeProfile h x y` and prove all the
regularity, concavity, endpoint, root and non-degeneracy properties needed by the odd case of
Ryabogin's theorem.

The consumers are
`Commons.Geometry.Ulam.odd_profile_cap_volume_half`,
`Commons.Geometry.Ulam.odd_profile_cap_centroid_span`,
`Commons.Geometry.Ulam.odd_floating_of_family` and
`Commons.Geometry.Ulam.not_centrally_symmetric_body_of_revolution_of_not_even_v4`.

**Note on the smoothness order.**  Everything here is `C^∞` (`ContDiffOn ℝ ∞`, i.e.
`(↑(⊤ : ENat) : WithTop ENat)`), *not* analytic: the perturbation `h` is a bump function, so the
profile cannot be analytic.  Consumers that (in this Mathlib revision) ask for
`ContDiffOn ℝ (⊤ : WithTop ENat) f s` — which is `ω`/analyticity, see
`ContDiff/Defs.lean:90` — cannot be instantiated from this profile and should have that hypothesis
weakened to `∞`.
-/

namespace Work.OddEnvelope

noncomputable section

open Set Filter
open scoped Topology ContDiff

variable {h x y : ℝ → ℝ}

theorem strictAntiOn_deriv_envelopeProfile_interior (H : IsEnvelopeCurve h x y) :
    StrictAntiOn (deriv (envelopeProfile h x y)) (interior (Set.Icc (-1 : ℝ) 1)) := by
  rw [interior_Icc]
  exact strictAntiOn_deriv_envelopeProfile H

/-- The profile is continuous on the closed interval. -/
theorem continuousOn_envelopeProfile' (H : IsEnvelopeCurve h x y) :
    ContinuousOn (envelopeProfile h x y) (Set.Icc (-1 : ℝ) 1) :=
  Work.OddEnvelope.Basic.continuousOn_envelopeProfile H (envelopeProfile_contDiffOn H)

/-- **Strict concavity of the envelope profile on `[-1,1]`.** -/
theorem strictConcaveOn_envelopeProfile (H : IsEnvelopeCurve h x y) :
    StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) (envelopeProfile h x y) :=
  StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc _ _) (continuousOn_envelopeProfile' H)
    (strictAntiOn_deriv_envelopeProfile_interior H)

/-- **Concavity of the envelope profile on `[-1,1]`** (the form used by the cap lemmas). -/
theorem concaveOn_envelopeProfile (H : IsEnvelopeCurve h x y) :
    ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) (envelopeProfile h x y) :=
  (strictConcaveOn_envelopeProfile H).concaveOn

/-- **The complete specification of the envelope profile.**  Every property of the profile needed
by the odd case of Ryabogin's theorem, for the concrete function `envelopeProfile h x y`. -/
theorem envelopeProfile_spec (H : IsEnvelopeCurve h x y) :
    Function.support (envelopeProfile h x y) ⊆ Set.Icc (-1 : ℝ) 1 ∧
    envelopeProfile h x y (-1) = 0 ∧ envelopeProfile h x y 1 = 0 ∧
    (∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < envelopeProfile h x y t) ∧
    ContDiffOn ℝ ∞ (envelopeProfile h x y) (Set.Ioo (-1 : ℝ) 1) ∧
    StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) (envelopeProfile h x y) ∧
    ContinuousOn (envelopeProfile h x y) (Set.Icc (-1 : ℝ) 1) ∧
    (∀ s, 0 < s → envelopeProfile h x y (y s) = s * y s + h s) ∧
    (∀ s, 0 < s → envelopeProfile h x y (-(x s)) = -(s * (-(x s)) + h s)) ∧
    (∀ s, 0 < s → -(x s) ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1) ∧
    (∀ s, 0 < s → ∀ t ∈ Set.Ioo (-(x s)) (y s),
      0 < envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) ∧
    ((∀ t : ℝ, envelopeProfile h x y (-t) = envelopeProfile h x y t) ↔
      ∀ u : ℝ, 0 < u →
        y u * (slopeRight x (y u) - u) - h (slopeRight x (y u)) - h u = 0) ∧
    ((∀ s : ℝ, h s = 0) →
      ((∀ s, 0 < s → x s = y s) ↔
        (∀ t : ℝ, envelopeProfile h x y (-t) = envelopeProfile h x y t))) :=
  ⟨envelopeProfile_support, envelopeProfile_left_end, envelopeProfile_right_end,
   fun t ht => envelopeProfile_pos H ht,
   envelopeProfile_contDiffOn H,
   strictConcaveOn_envelopeProfile H,
   continuousOn_envelopeProfile' H,
   fun s hs => envelopeProfile_root_right H hs,
   fun s hs => envelopeProfile_root_left H hs,
   fun s hs => envelopeProfile_mem_Ioo H hs,
   fun s hs t ht => envelopeProfile_sub_sq_pos H (concaveOn_envelopeProfile H) hs t ht,
   envelopeProfile_even_iff H,
   fun hh => (envelopeProfile_even_iff_eq_of_h_eq_zero H hh).symm⟩

/-- **The deliverable of `Work.OddEnvelope`.**  From a chord-endpoint curve `(x,y)` satisfying
`IsEnvelopeCurve` there is a profile `f` with all the properties (support `[-1,1]`, `C^∞`,
strictly concave, positive, the two root conditions, the intersection points inside `(-1,1)`,
non-degeneracy of the cutting sections, and the sharp evenness criterion). -/
theorem odd_envelope_profile (H : IsEnvelopeCurve h x y) :
    ∃ f : ℝ → ℝ,
      Function.support f ⊆ Set.Icc (-1 : ℝ) 1 ∧ f (-1) = 0 ∧ f 1 = 0 ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t) ∧
      ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1) ∧
      StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f ∧
      ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
      (∀ s, 0 < s → f (y s) = s * y s + h s) ∧
      (∀ s, 0 < s → f (-(x s)) = -(s * (-(x s)) + h s)) ∧
      (∀ s, 0 < s → -(x s) ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1) ∧
      (∀ s, 0 < s → ∀ t ∈ Set.Ioo (-(x s)) (y s), 0 < f t ^ 2 - (s * t + h s) ^ 2) ∧
      ((∀ t : ℝ, f (-t) = f t) ↔
        ∀ u : ℝ, 0 < u →
          y u * (slopeRight x (y u) - u) - h (slopeRight x (y u)) - h u = 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _h13⟩ := envelopeProfile_spec H
  exact ⟨envelopeProfile h x y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- **The deliverable, with the non-evenness conclusion.**  The extra hypothesis is the *sharp*
criterion for non-evenness: the tuning relation of `envelopeProfile_even_iff` fails at some slope.
(It is *not* enough to know that `x ≠ y` somewhere — see the warning in `NonEven.lean`.) -/
theorem odd_envelope_profile_not_even (H : IsEnvelopeCurve h x y)
    (hbad : ∃ u : ℝ, 0 < u ∧
      y u * (slopeRight x (y u) - u) - h (slopeRight x (y u)) - h u ≠ 0) :
    ∃ f : ℝ → ℝ,
      Function.support f ⊆ Set.Icc (-1 : ℝ) 1 ∧ f (-1) = 0 ∧ f 1 = 0 ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t) ∧
      ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1) ∧
      StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f ∧
      ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
      (∀ s, 0 < s → f (y s) = s * y s + h s) ∧
      (∀ s, 0 < s → f (-(x s)) = -(s * (-(x s)) + h s)) ∧
      (∀ s, 0 < s → -(x s) ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1) ∧
      (∀ s, 0 < s → ∀ t ∈ Set.Ioo (-(x s)) (y s), 0 < f t ^ 2 - (s * t + h s) ^ 2) ∧
      ¬ (∀ t : ℝ, f (-t) = f t) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _h12, _h13⟩ := envelopeProfile_spec H
  exact ⟨envelopeProfile h x y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    not_even_of_tuning_fails H hbad⟩

end

end Work.OddEnvelope
