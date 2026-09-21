import Submission.Work.OddCurve.Free.SpecFree
import Submission.Work.OddCurve.CapsGen.Defs
import Submission.Work.OddCurve.CapsGen.centroid_span_general_smooth
import Submission.Work.Geometry.Ulam.odd_profile_cap_volume_half_general_smooth
import Submission.Work.Odd.not_centrally_symmetric_of_h_ne_zero
import Submission.Work.Odd.sub_singleton_eq_neg_iff
import Submission.Commons.Geometry.Ulam.interior_nonempty_body_of_revolution

/-!
# The endgame of the odd case on a general interval `[-R₁, R₂]`

`Submission.Odd.Assembly.family_data_of_moment_equations` turns the two moment equations on all
slopes `s > 0`, together with the profile data **on `[-1,1]`**, into
`Submission.Odd.OddFamilyData d`.  The normalisation to `[-1,1]` is exactly what the paper's odd
construction does *not* produce: the tips of the reconstructed body are at `±ρ(±1)`
(`Submission/Work/OddCurve/NOTES_SESSION5.md`).  `Submission.Odd.OddFamilyData` itself is stated
for a general `[-R₁, R₂]`; this file supplies the endgame at that generality.

The pieces used here are all already in the workspace:

* `Work.OddCurve.CapsGen.VolumeHalfGeneral` / `CentroidSpanGeneral` — the two family conditions on
  `[-R₁, R₂]`, as `Prop`s (`Work/OddCurve/CapsGen/Defs.lean`);
* `Commons.Geometry.Ulam.odd_profile_cap_volume_half_general_smooth` — the **smooth** (not
  analytic) general-interval volume-half cap lemma: the volume condition follows from the second
  moment equation;
* `Work.Odd.not_centrally_symmetric_of_h_ne_zero` — non-central symmetry from `h ≠ 0` and the
  volume-half property, already stated for an arbitrary convex body;
* the bookkeeping of `Submission.Odd.OddFamilyData`.

**The one missing input at this level** is the *smooth* general-interval version of the centroid
cap lemma: the seed's `odd_profile_cap_centroid_span_general` is proved for an **analytic**
profile (`ContDiffOn ℝ (⊤ : WithTop ℕ∞) f`, i.e. `ω`, not `∞`) and its `_smooth` restatement
carries a `sorry`.  Its proof uses no analyticity-specific fact (no `AnalyticOn` occurrence), so
weakening the hypothesis to `ContDiffOn ℝ ∞` is a mechanical copy; it is delegated as
`Submission/Work/OddCurve/CapsGen/centroid_span_general_smooth`.  Until it lands, the two theorems
below take the centroid condition (`hcent`) as an explicit hypothesis, so that the endgame is a
proved composition.
-/


/-!
## Caveat: the truncated profile

`Work.OddEnvelope.envelopeProfile` is defined to be `0` outside `[-1, 1]`; for a *free-tip* curve
(whose body has tips at `±ρ(±1)`, `ρ(±1) ≠ 1`) the profile of the body is the **untruncated**
profile `Work.OddVolterra.Free.envProfileFree` (`Submission/Work/OddVolterra/Free/Defs.lean`) —
the two agree on `|t| < 1` (`envProfileFree_eq_envelopeProfile`).  Statements in this file that
mention `envelopeProfile` are therefore the *tip-normalised* ones (correct only when the tips are
`±1`, i.e. `R₁ = R₂ = 1`); the free-tip statements in terms of `envProfileFree` are the sibling's
(`Submission/Work/OddCurveB/FreeTip.lean`, `Submission/Work/OddVolterra/Free/Defs.lean`, which
records `LowSlopeThreeFree`).  The general-interval endgame of this chapter
(`Submission/Work/OddCurve/Free/Endgame.lean`) takes the profile as an explicit hypothesis, so it
is agnostic to this distinction.
-/

namespace Work.OddCurve
namespace Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise Interval BigOperators RealInnerProductSpace

/-- The body of revolution with profile `f` on `[-R₁, R₂]` (the `K` of `OddFamilyData`). -/
abbrev bodySet (d : ℕ) [NeZero d] (R₁ R₂ : ℝ) (f : ℝ → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧
    ∑ i ∈ Finset.Ioi (0 : Fin d), (x i) ^ 2 ≤ f (x 0) ^ 2}

/-- **The odd endgame on a general interval, from the two family conditions.**  Profile data on
`[-R₁, R₂]`, a bump with `h 0 = 0` and `h ≠ 0` supported in the transition window, and the two
family conditions (volume half and centroid in span) give `Submission.Odd.OddFamilyData d`. -/
theorem oddFamilyData_of_familyConditions {d : ℕ} [NeZero d] (hd : 3 ≤ d) (hdodd : Odd d)
    (n : ℕ) (hdn : d = 2 * n + 1) (hn : 1 ≤ n)
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) {f h : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-R₁) R₂)
    (hf_cont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-R₁) R₂))
    (hf_strict : StrictConcaveOn ℝ (Set.Icc (-R₁) R₂) f)
    (hf_contIcc : ContinuousOn f (Set.Icc (-R₁) R₂))
    (hf_left : f (-R₁) = 0) (hf_right : f R₂ = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-R₁) R₂, 0 < f t)
    (hh_cont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (h0 : h 0 = 0)
    (hhne : ∃ s : ℝ, 0 < s ∧ h s ≠ 0)
    (hh_supp : Function.support h ⊆
      Set.Icc (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)))
    (hvol : CapsGen.VolumeHalfGeneral d R₁ R₂ f h)
    (hcent : CapsGen.CentroidSpanGeneral d R₁ R₂ f h) :
    Submission.Odd.OddFamilyData d := by
  classical
  have hRlt : -R₁ < R₂ := by linarith
  have hK_meas : MeasurableSet (bodySet d R₁ R₂ f) :=
    Commons.Geometry.Ulam.body_of_revolution_measurable (R₁ := R₁) (R₂ := R₂) (f := f)
      hf_support hf_cont hf_left hf_right
  have hK_conv : Convex ℝ (bodySet d R₁ R₂ f) :=
    Commons.Geometry.Ulam.body_of_revolution_convex (R₁ := R₁) (R₂ := R₂) (f := f)
      hf_strict.concaveOn hf_left hf_right
  have hK_bdd : Bornology.IsBounded (bodySet d R₁ R₂ f) :=
    Commons.Geometry.Ulam.body_of_revolution_bounded (R₁ := R₁) (R₂ := R₂) (f := f)
      hf_strict.concaveOn hf_left hf_right
  have hK_fin : MeasureTheory.volume (bodySet d R₁ R₂ f) < ⊤ := hK_bdd.measure_lt_top
  have hK_int : (interior (bodySet d R₁ R₂ f)).Nonempty :=
    Commons.Geometry.Ulam.interior_nonempty_body_of_revolution (R₁ := R₁) (R₂ := R₂) (f := f)
      hRlt hf_cont.continuousOn hf_pos
  have hrefl : ¬ ∃ p : EuclideanSpace ℝ (Fin d), ∀ x : EuclideanSpace ℝ (Fin d),
      (x ∈ bodySet d R₁ R₂ f ↔ (2 : ℝ) • p - x ∈ bodySet d R₁ R₂ f) :=
    Work.Odd.not_centrally_symmetric_of_h_ne_zero (K := bodySet d R₁ R₂ f) (h := h)
      hK_meas hK_conv hK_int hK_fin hvol hh_supp hhne
  have hnonc : ¬ ∃ p : EuclideanSpace ℝ (Fin d),
      bodySet d R₁ R₂ f - {p} = -(bodySet d R₁ R₂ f - {p}) := by
    rintro ⟨p, hp⟩
    have hconv : ∀ s : Set (EuclideanSpace ℝ (Fin d)), -s = (fun x => -x) '' s := by
      intro s
      ext a
      rw [Set.mem_neg, Set.mem_image]
      constructor
      · intro h; exact ⟨-a, h, by simp⟩
      · rintro ⟨x, hx, hxa⟩
        have : -a = x := by rw [← hxa]; simp
        rwa [this]
    have hkey : Set.image2 (fun a b : EuclideanSpace ℝ (Fin d) => a - b)
          (bodySet d R₁ R₂ f) ({p} : Set _) =
        (fun x : EuclideanSpace ℝ (Fin d) => -x) '' Set.image2 (fun a b => a - b)
          (bodySet d R₁ R₂ f) ({p} : Set _) := by
      calc Set.image2 (fun a b : EuclideanSpace ℝ (Fin d) => a - b)
              (bodySet d R₁ R₂ f) ({p} : Set _)
          = (bodySet d R₁ R₂ f - {p}) := rfl
        _ = -(bodySet d R₁ R₂ f - {p}) := hp
        _ = (fun x : EuclideanSpace ℝ (Fin d) => -x) '' (bodySet d R₁ R₂ f - {p}) := hconv _
        _ = (fun x : EuclideanSpace ℝ (Fin d) => -x) '' Set.image2 (fun a b => a - b)
              (bodySet d R₁ R₂ f) ({p} : Set _) := rfl
    exact hrefl ⟨p, (Work.Odd.sub_singleton_eq_neg_iff
      (K := bodySet d R₁ R₂ f) (p := p)).mp hkey⟩
  -- the centroid condition, with the direction vector in the form used by `OddFamilyData`
  have hcent' : ∀ s : ℝ, 0 < s →
      (⨍ x in bodySet d R₁ R₂ f, x) -
          (⨍ x in (bodySet d R₁ R₂ f ∩
            {x : EuclideanSpace ℝ (Fin d) | x ⟨d - 1, by omega⟩ ≤ s * x 0 + h s}), x) ∈
        ℝ ∙ (EuclideanSpace.single (0 : Fin d) (-s) +
          EuclideanSpace.single (⟨d - 1, by omega⟩ : Fin d) (1 : ℝ)) := by
    intro s hs
    have h := hcent s hs
    have hsingle : (-s) • (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) +
        EuclideanSpace.single (⟨d - 1, by omega⟩ : Fin d) (1 : ℝ) =
        EuclideanSpace.single (0 : Fin d) (-s) +
          EuclideanSpace.single (⟨d - 1, by omega⟩ : Fin d) (1 : ℝ) := by
      ext i
      by_cases hi : i = 0
      · subst hi; simp
      · by_cases hj : i = (⟨d - 1, by omega⟩ : Fin d)
        · subst hj; simp [hi]
        · simp [EuclideanSpace.single, hi, hj]
    rw [hsingle] at h
    simpa [CapsGen.CentroidSpanGeneral, bodySet] using h
  refine ⟨R₁, R₂, f, h, hRlt, hf_support, hf_cont, hf_strict, hf_contIcc, hf_left, hf_right,
    hf_pos, hh_cont, h0, hhne, ?_, ?_, ?_⟩
  · simpa [CapsGen.VolumeHalfGeneral, bodySet] using hvol
  · simpa [bodySet] using hcent'
  · simpa [bodySet] using hnonc

/-- **The volume-half family condition on a general interval follows from the second moment
equation** (the smooth general-interval cap lemma
`Commons.Geometry.Ulam.odd_profile_cap_volume_half_general_smooth`). -/
theorem volumeHalfGeneral_of_momentEquations {d : ℕ} [NeZero d] (n : ℕ) (hdn : d = 2 * n + 1)
    (hn : 1 ≤ n) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-R₁) R₂)
    (hf_cont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-R₁) R₂))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-R₁) R₂) f)
    (hf_left : f (-R₁) = 0) (hf_right : f R₂ = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-R₁) R₂, 0 < f t)
    (hh_cont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo (-R₁) R₂ ∧ y s ∈ Set.Ioo (-R₁) R₂)
    (h_center : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0) :
    CapsGen.VolumeHalfGeneral d R₁ R₂ f h := by
  have hRlt : -R₁ < R₂ := by linarith
  have h := Commons.Geometry.Ulam.odd_profile_cap_volume_half_general_smooth (d := d)
    (a := -R₁) (b := R₂) n hdn hn hRlt hf_support hf_cont hf_conc hf_left hf_right hf_pos
    (hh_cont.contDiffOn) h0 hxy hxy_inside h_center
  simpa [CapsGen.VolumeHalfGeneral, bodySet] using h

/-- **The odd endgame on a general interval, from the moment equations** (with the centroid
condition still supplied separately — see the module docstring). -/
theorem oddFamilyData_of_momentEquationsGeneral {d : ℕ} [NeZero d] (hd : 3 ≤ d) (hdodd : Odd d)
    (n : ℕ) (hdn : d = 2 * n + 1) (hn : 1 ≤ n)
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) {f h x y : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-R₁) R₂)
    (hf_cont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-R₁) R₂))
    (hf_strict : StrictConcaveOn ℝ (Set.Icc (-R₁) R₂) f)
    (hf_contIcc : ContinuousOn f (Set.Icc (-R₁) R₂))
    (hf_left : f (-R₁) = 0) (hf_right : f R₂ = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-R₁) R₂, 0 < f t)
    (hh_cont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (h0 : h 0 = 0)
    (hhne : ∃ s : ℝ, 0 < s ∧ h s ≠ 0)
    (hh_supp : Function.support h ⊆
      Set.Icc (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)))
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo (-R₁) R₂ ∧ y s ∈ Set.Ioo (-R₁) R₂)
    (hB : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0)
    (hcent : CapsGen.CentroidSpanGeneral d R₁ R₂ f h) :
    Submission.Odd.OddFamilyData d :=
  oddFamilyData_of_familyConditions hd hdodd n hdn hn hR₁ hR₂ hf_support hf_cont hf_strict
    hf_contIcc hf_left hf_right hf_pos hh_cont h0 hhne hh_supp
    (volumeHalfGeneral_of_momentEquations n hdn hn hR₁ hR₂ hf_support hf_cont
      hf_strict.concaveOn hf_left hf_right hf_pos hh_cont h0 hxy hxy_inside hB)
    hcent

/-- **The centroid family condition on a general interval follows from the two moment equations**
(using the smooth general-interval cap lemma
`Work.OddCurve.CapsGen.centroid_span_general_smooth`, proved in this chapter). -/
theorem centroidSpanGeneral_of_momentEquations {d : ℕ} [NeZero d] (n : ℕ)
    (hdn : d = 2 * n + 1) (hn : 1 ≤ n) {R₁ R₂ C : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-R₁) R₂)
    (hf_cont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-R₁) R₂))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-R₁) R₂) f)
    (hf_left : f (-R₁) = 0) (hf_right : f R₂ = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-R₁) R₂, 0 < f t)
    (hh_cont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo (-R₁) R₂ ∧ y s ∈ Set.Ioo (-R₁) R₂)
    (h_moment : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
        C / Real.sqrt (1 + s ^ 2))
    (h_center : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0)
    (hvol : ∀ s : ℝ, 0 < s →
      MeasureTheory.volume.real (bodySet d R₁ R₂ f ∩
        {z : EuclideanSpace ℝ (Fin d) | z ⟨d - 1, by omega⟩ ≤ s * z 0 + h s}) =
      MeasureTheory.volume.real (bodySet d R₁ R₂ f) / 2) :
    CapsGen.CentroidSpanGeneral d R₁ R₂ f h := by
  have hRlt : -R₁ < R₂ := by linarith
  have h := CapsGen.centroid_span_general_smooth (d := d) (A := -R₁) (B := R₂) (C := C) n hdn hn
    hRlt hf_support hf_cont hf_conc hf_left hf_right hf_pos (hh_cont.contDiffOn) h0 hxy hxy_inside
    h_moment h_center (by simpa [bodySet] using hvol)
  simpa [CapsGen.CentroidSpanGeneral, CapsGen.CentroidSpanGeneral', bodySet] using h

/-- **The odd endgame on a general interval, unconditionally.**  Profile data on `[-R₁, R₂]`, a
bump with `h 0 = 0`, `h ≠ 0` supported in the transition window, the chord-endpoint data, and the
two (odd, `sqrt`-weighted) moment equations for **all** slopes `s > 0` give
`Submission.Odd.OddFamilyData d` — with no normalisation of the tips and no analyticity
hypothesis. -/
theorem oddFamilyData_of_momentEquationsGeneralFull {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    (hdodd : Odd d) (n : ℕ) (hdn : d = 2 * n + 1) (hn : 1 ≤ n)
    {R₁ R₂ C : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) {f h x y : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-R₁) R₂)
    (hf_cont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-R₁) R₂))
    (hf_strict : StrictConcaveOn ℝ (Set.Icc (-R₁) R₂) f)
    (hf_contIcc : ContinuousOn f (Set.Icc (-R₁) R₂))
    (hf_left : f (-R₁) = 0) (hf_right : f R₂ = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-R₁) R₂, 0 < f t)
    (hh_cont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (h0 : h 0 = 0)
    (hhne : ∃ s : ℝ, 0 < s ∧ h s ≠ 0)
    (hh_supp : Function.support h ⊆
      Set.Icc (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)))
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo (-R₁) R₂ ∧ y s ∈ Set.Ioo (-R₁) R₂)
    (hA : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
        C / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0) :
    Submission.Odd.OddFamilyData d := by
  have hvol := volumeHalfGeneral_of_momentEquations n hdn hn hR₁ hR₂ hf_support hf_cont
    hf_strict.concaveOn hf_left hf_right hf_pos hh_cont h0 hxy hxy_inside hB
  exact oddFamilyData_of_familyConditions hd hdodd n hdn hn hR₁ hR₂ hf_support hf_cont
    hf_strict hf_contIcc hf_left hf_right hf_pos hh_cont h0 hhne hh_supp hvol
    (centroidSpanGeneral_of_momentEquations n hdn hn hR₁ hR₂ hf_support hf_cont
      hf_strict.concaveOn hf_left hf_right hf_pos hh_cont h0 hxy hxy_inside hA hB
      (by intro s hs; simpa [CapsGen.VolumeHalfGeneral, bodySet] using hvol s hs))

end

end Free
end Work.OddCurve
