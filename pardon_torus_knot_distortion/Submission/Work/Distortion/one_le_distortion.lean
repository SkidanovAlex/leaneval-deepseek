import Mathlib
import Submission.Work.Core.Torus
import Submission.Work.Distortion.length_ge_twice_diam

/-!
# The distortion of a smooth knot is at least `1`

The intrinsic (arclength) distance between two points of a closed curve is the
length of the shorter of the two arcs joining them.  Every such arc is at least
as long as the Euclidean chord between its endpoints, so the intrinsic distance
is at least the chord.  Consequently *every* distortion ratio of a knot is at
least `1`, hence so is the distortion, which is the supremum of the ratios.

The two ingredients, both elementary, are

* `dist_le_parameterArcLength`: the chord is at most the arclength of the
  parameter interval `[s, t]`.  This is the fundamental theorem of calculus
  (`γ t - γ s = ∫ deriv γ`) together with the triangle inequality for the
  interval integral (`‖∫ f‖ ≤ ∫ ‖f‖`);
* `dist_le_totalArcLength_sub`: for `s ≤ t` inside the fundamental interval, the
  chord is also at most the length `T - parameterArcLength K s t` of the
  *complementary* arc, obtained from the same estimate applied to the interval
  `[t, s + 2π]` and the `2π`-periodicity of the curve.

Both bounds hold simultaneously for `s, t` in the fundamental interval, and
`intrinsicDistance K s t` is by definition the smaller of the two arclengths.
-/

namespace Work.Distortion

open LeanEval.KnotTheory.PardonDistortion
open Set MeasureTheory
open scoped ENNReal

namespace OneLe

/-- The arclength between two parameters does not depend on their order. -/
lemma parameterArcLength_comm (K : Knot) (s t : ℝ) :
    parameterArcLength K s t = parameterArcLength K t s := by
  rw [parameterArcLength, parameterArcLength,
    intervalIntegral.integral_symm s t, abs_neg]

/-- **Chord is at most arc length.**  The Euclidean distance of the points with
parameters `s` and `t` is at most the arclength of the parametrized arc between
them (for any order of `s` and `t`). -/
lemma dist_le_parameterArcLength (K : Knot) (s t : ℝ) :
    dist (K.curve s) (K.curve t) ≤ parameterArcLength K s t := by
  have hmono : ∀ {a b : ℝ}, a ≤ b →
      dist (K.curve a) (K.curve b) ≤ ∫ u in a..b, speed K u :=
    fun h => LengthGeTwiceDiam.dist_le_integral_speed K h
  have hnonneg : ∀ {a b : ℝ}, a ≤ b →
      0 ≤ ∫ u in a..b, speed K u :=
    fun h => intervalIntegral.integral_nonneg (μ := volume) h
      (fun u _ => norm_nonneg (deriv K.curve u))
  rcases le_total s t with h | h
  · rw [parameterArcLength, abs_of_nonneg (hnonneg h)]
    exact hmono h
  · have hcomm : dist (K.curve s) (K.curve t) = dist (K.curve t) (K.curve s) :=
      dist_comm _ _
    rw [hcomm, parameterArcLength_comm K s t, parameterArcLength, abs_of_nonneg (hnonneg h)]
    exact hmono h

/-- The complemented arclength `totalArcLength K - parameterArcLength K s t` is
nonnegative for parameters in the fundamental interval. -/
lemma totalArcLength_sub_parameterArcLength_nonneg (K : Knot) {s t : ℝ}
    (hs : s ∈ Set.Ico 0 (2 * Real.pi)) (ht : t ∈ Set.Ico 0 (2 * Real.pi)) :
    0 ≤ totalArcLength K - parameterArcLength K s t := by
  have hcont : Continuous (speed K) := LengthGeTwiceDiam.continuous_speed K
  have hnonneg : ∀ {a b : ℝ}, a ≤ b →
      0 ≤ ∫ u in a..b, speed K u :=
    fun h => intervalIntegral.integral_nonneg (μ := volume) h
      (fun u _ => norm_nonneg (deriv K.curve u))
  rcases le_total s t with h | h
  · have hle : t ≤ s + 2 * Real.pi := by linarith [ht.2, hs.1]
    have h1 : parameterArcLength K s t = ∫ u in s..t, speed K u := by
      rw [parameterArcLength, abs_of_nonneg (hnonneg h)]
    have h2 : (∫ u in s..t, speed K u) + ∫ u in t..(s + 2 * Real.pi), speed K u
        = ∫ u in s..(s + 2 * Real.pi), speed K u :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (μ := volume) _ _)
        (hcont.intervalIntegrable (μ := volume) _ _)
    have h3 : (∫ u in s..(s + 2 * Real.pi), speed K u) = totalArcLength K :=
      LengthGeTwiceDiam.integral_speed_period K s
    linarith [hnonneg hle]
  · have hle : s ≤ t + 2 * Real.pi := by linarith [hs.2, ht.1]
    have h1 : parameterArcLength K t s = ∫ u in t..s, speed K u := by
      rw [parameterArcLength, abs_of_nonneg (hnonneg h)]
    have h2 : (∫ u in t..s, speed K u) + ∫ u in s..(t + 2 * Real.pi), speed K u
        = ∫ u in t..(t + 2 * Real.pi), speed K u :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (μ := volume) _ _)
        (hcont.intervalIntegrable (μ := volume) _ _)
    have h3 : (∫ u in t..(t + 2 * Real.pi), speed K u) = totalArcLength K :=
      LengthGeTwiceDiam.integral_speed_period K t
    rw [parameterArcLength_comm K s t]
    linarith [hnonneg hle]

/-- **Chord is at most the complementary arc.**  For `s ≤ t` inside the
fundamental interval, the chord between the two points is at most the arclength
of the *other* arc joining them, namely `totalArcLength K - parameterArcLength K s t`. -/
lemma dist_le_totalArcLength_sub (K : Knot) {s t : ℝ}
    (hs : s ∈ Set.Ico 0 (2 * Real.pi)) (ht : t ∈ Set.Ico 0 (2 * Real.pi)) (hst : s ≤ t) :
    dist (K.curve s) (K.curve t) ≤ totalArcLength K - parameterArcLength K s t := by
  have hcont : Continuous (speed K) := LengthGeTwiceDiam.continuous_speed K
  have hnonneg : ∀ {a b : ℝ}, a ≤ b →
      0 ≤ ∫ u in a..b, speed K u :=
    fun h => intervalIntegral.integral_nonneg (μ := volume) h
      (fun u _ => norm_nonneg (deriv K.curve u))
  have hle : t ≤ s + 2 * Real.pi := by linarith [ht.2, hs.1]
  -- the chord is at most the arclength of the complementary arc
  have hcomp : dist (K.curve s) (K.curve t) ≤ ∫ u in t..(s + 2 * Real.pi), speed K u := by
    have h := LengthGeTwiceDiam.dist_le_integral_speed K hle
    have hper : K.curve (s + 2 * Real.pi) = K.curve s := by simpa using K.periodic s
    rw [hper, dist_comm] at h
    exact h
  have h1 : parameterArcLength K s t = ∫ u in s..t, speed K u := by
    rw [parameterArcLength, abs_of_nonneg (hnonneg hst)]
  have h2 : (∫ u in s..t, speed K u) + ∫ u in t..(s + 2 * Real.pi), speed K u
      = ∫ u in s..(s + 2 * Real.pi), speed K u :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (μ := volume) _ _)
      (hcont.intervalIntegrable (μ := volume) _ _)
  have h3 : (∫ u in s..(s + 2 * Real.pi), speed K u) = totalArcLength K :=
    LengthGeTwiceDiam.integral_speed_period K s
  linarith

/-- **The intrinsic distance dominates the chord.**  For parameters in the
fundamental interval, the shorter of the two arcs joining the two points of the
curve is at least as long as their Euclidean distance. -/
theorem dist_le_intrinsicDistance (K : Knot) {s t : ℝ}
    (hs : s ∈ Set.Ico 0 (2 * Real.pi)) (ht : t ∈ Set.Ico 0 (2 * Real.pi)) :
    dist (K.curve s) (K.curve t) ≤ intrinsicDistance K s t := by
  rw [intrinsicDistance]
  refine le_min (dist_le_parameterArcLength K s t) ?_
  rcases le_total s t with h | h
  · exact dist_le_totalArcLength_sub K hs ht h
  · have h' := dist_le_totalArcLength_sub K ht hs h
    rwa [dist_comm, parameterArcLength_comm] at h'

/-- Every distortion ratio of a knot is at least `1`: the intrinsic distance of
two distinct points dominates their chord, and the chord is nonzero because the
parametrisation is injective on the fundamental interval. -/
theorem one_le_distortionRatio (K : Knot) {s t : ℝ}
    (hs : s ∈ Set.Ico 0 (2 * Real.pi)) (ht : t ∈ Set.Ico 0 (2 * Real.pi)) (hst : s ≠ t) :
    (1 : ℝ) ≤ distortionRatio K s t := by
  have hchord : 0 < dist (K.curve s) (K.curve t) := by
    rw [dist_pos]
    intro h
    exact hst (K.injOn hs ht h)
  rw [distortionRatio, one_le_div hchord]
  exact dist_le_intrinsicDistance K hs ht

end OneLe

open OneLe

/-- The distortion of every smooth knot is at least `1`. -/
theorem one_le_distortion (K : LeanEval.KnotTheory.PardonDistortion.Knot) :
    (1 : ENNReal) ≤ LeanEval.KnotTheory.PardonDistortion.distortion K := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨le_refl _, by linarith⟩
  have hπ : Real.pi ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨hpi.le, by linarith⟩
  have hne : (0 : ℝ) ≠ Real.pi := ne_of_lt hpi
  calc (1 : ENNReal)
      = ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_one.symm
    _ ≤ ENNReal.ofReal (distortionRatio K 0 Real.pi) :=
        ENNReal.ofReal_le_ofReal (one_le_distortionRatio K h0 hπ hne)
    _ ≤ distortion K := le_sSup ⟨0, h0, Real.pi, hπ, hne, rfl⟩

end Work.Distortion
