import Mathlib
import ChallengeDeps

/-!
# The distortion of a closed curve is at least half the ratio length/diameter

For a closed rectifiable curve `γ` with total length `L` and diameter `D`,
its distortion — the supremum of `(arclength distance) / (chord length)` over
pairs of points — is at least `L / (2 * D)`.

The classical proof is the "antipodal point" argument: walk along the curve
starting from a fixed point `γ(0)` and stop at the first time `t` at which the
arclength travelled equals `L / 2` (the intermediate value theorem applied to
the arclength function, whose derivative is the speed).  At that parameter the
two complementary arcs have equal length `L / 2`, so the intrinsic distance
between `γ(0)` and `γ(t)` is exactly `L / 2`, while the chord length is at most
the diameter `D`.  Hence the distortion ratio at this pair is at least
`(L/2) / D = L / (2 * D)`.

Note that the two parameters are distinct: `t ≠ 0` because the arclength
travelled at `t` is `L/2 > 0`, and this is also where the hypothesis that the
parametrisation is injective on `[0, 2π)` (a genuine embedded curve rather than
a multiply-traversed one) is used, to know that the chord length at the pair is
non-zero.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.Distortion

/-- For any smooth knot `K`, the ratio of its total arclength to twice the
diameter of its image is a lower bound for its distortion. -/
theorem length_diameter (K : LeanEval.KnotTheory.PardonDistortion.Knot) :
    ENNReal.ofReal (LeanEval.KnotTheory.PardonDistortion.totalArcLength K / (2 * Metric.diam (Set.range K.curve))) ≤ LeanEval.KnotTheory.PardonDistortion.distortion K := by
  have hspeed : Continuous (speed K) := by
    have h : Continuous (deriv K.curve) :=
      K.smooth.continuous_deriv (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
    exact h.norm
  have hpipos : (0 : ℝ) < 2 * Real.pi := by positivity
  -- The arclength function measured from `0`.
  set G : ℝ → ℝ := fun T => ∫ u in (0 : ℝ)..T, speed K u with hGdef
  have hGcont : Continuous G := by
    rw [hGdef]
    exact continuous_iff_continuousAt.mpr fun b =>
      ((hspeed.integral_hasStrictDerivAt (0 : ℝ) b).hasDerivAt).continuousAt
  have hG0 : G 0 = 0 := by
    show (∫ u in (0 : ℝ)..(0 : ℝ), speed K u) = 0
    exact intervalIntegral.integral_same
  set L : ℝ := totalArcLength K with hLdef
  set D : ℝ := Metric.diam (Set.range K.curve) with hDdef
  have hLnonneg : 0 ≤ L := by
    rw [hLdef, totalArcLength, parameterArcLength]
    exact abs_nonneg _
  by_cases hbd : Bornology.IsBounded (Set.range K.curve)
  · rcases eq_or_lt_of_le hLnonneg with hL0 | hLpos
    · -- Degenerate case: the curve has zero length.
      rw [← hL0]
      simp
    · -- `G (2π) = L`, so `L/2` is an intermediate value of `G` on `[0, 2π]`.
      have hInt_nonneg : 0 ≤ ∫ u in (0 : ℝ)..(2 * Real.pi), speed K u :=
        intervalIntegral.integral_nonneg hpipos.le (fun u _ => norm_nonneg (deriv K.curve u))
      have hG2pi : G (2 * Real.pi) = L := by
        show (∫ u in (0 : ℝ)..(2 * Real.pi), speed K u) = L
        rw [hLdef, totalArcLength, parameterArcLength]
        exact (abs_of_nonneg hInt_nonneg).symm
      have h0mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨le_refl _, hpipos⟩
      have hmem : L / 2 ∈ Set.Icc (G 0) (G (2 * Real.pi)) := by
        rw [hG0, hG2pi]
        exact ⟨by linarith, by linarith⟩
      obtain ⟨t, ht, hGt⟩ :=
        (isPreconnected_Icc.intermediate_value ⟨le_refl _, hpipos.le⟩ ⟨hpipos.le, le_refl _⟩
          hGcont.continuousOn) hmem
      have htne : t ≠ 0 := by
        intro h
        rw [h, hG0] at hGt
        linarith
      have htlt : t < 2 * Real.pi := by
        rcases lt_or_eq_of_le ht.2 with h | h
        · exact h
        · exfalso
          rw [h, hG2pi] at hGt
          linarith
      have htIco : t ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨ht.1, htlt⟩
      -- At `t` the two complementary arcs both have length `L/2`.
      have hparam : parameterArcLength K 0 t = L / 2 := by
        rw [parameterArcLength]
        show |G t| = L / 2
        rw [hGt, abs_of_nonneg (by linarith)]
      have hintr : intrinsicDistance K 0 t = L / 2 := by
        rw [intrinsicDistance, hparam, min_eq_left (by linarith)]
      -- The chord length is non-zero (injectivity of the parametrisation) and
      -- at most the diameter.
      have hne_pt : K.curve 0 ≠ K.curve t := by
        intro h
        exact htne (K.injOn h0mem htIco h).symm
      have hdpos : 0 < dist (K.curve 0) (K.curve t) := dist_pos.mpr hne_pt
      have hdle : dist (K.curve 0) (K.curve t) ≤ D := by
        rw [hDdef]
        exact Metric.dist_le_diam_of_mem hbd ⟨0, rfl⟩ ⟨t, rfl⟩
      -- Hence the distortion ratio at `(0, t)` is at least `L / (2 * D)`.
      have hkey : L / (2 * D) ≤ distortionRatio K 0 t := by
        rw [distortionRatio, hintr, div_div]
        exact div_le_div_of_nonneg_left hLpos.le (by linarith) (by linarith)
      refine le_trans (ENNReal.ofReal_le_ofReal hkey) (le_sSup ?_)
      exact ⟨0, h0mem, t, htIco, Ne.symm htne, rfl⟩
  · -- If the image were unbounded, `Metric.diam` would be zero.
    have hD0 : D = 0 := by
      rw [hDdef]
      exact Metric.diam_eq_zero_of_unbounded hbd
    rw [hD0]
    simp

end Work.Distortion
