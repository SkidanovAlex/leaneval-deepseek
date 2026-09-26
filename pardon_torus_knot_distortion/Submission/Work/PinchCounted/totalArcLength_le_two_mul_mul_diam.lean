import Mathlib
import Submission.Work.Sweep.Defs
import Submission.Work.Distortion.length_diameter

/-!
# Total arclength versus a distortion bound and the diameter

If `d` is a distortion bound for the knot `K` (`Work.Sweep.IsDistortionBound K d`),
then the total arclength of `K` is at most `2 * d` times the diameter of its
image.

The proof is the antipodal-"midpoint" argument: walking along the curve from
`0`, there is a parameter `t ∈ [0, 2π)` at which the arclength travelled is
exactly half of the total length `L`.  The intrinsic distance between the two
points `K 0` and `K t` is then `L / 2` (both complementary arcs have length
`L / 2`).  The distortion bound gives `L / 2 = intrinsicDistance K 0 t ≤
d * dist (K 0) (K t)`, and the chord length is at most the diameter `D` of the
image, whence `L ≤ 2 * d * D`.
-/

noncomputable section

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

theorem totalArcLength_le_two_mul_mul_diam {K : LeanEval.KnotTheory.PardonDistortion.Knot} {d : ℝ} (hd : 0 < d) (h : Work.Sweep.IsDistortionBound K d) : LeanEval.KnotTheory.PardonDistortion.totalArcLength K ≤ 2 * d * Metric.diam (Set.range K.curve) := by
  have hspeed : Continuous (speed K) := by
    have h1 : Continuous (deriv K.curve) :=
      K.smooth.continuous_deriv (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
    exact h1.norm
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
  have hDnn : 0 ≤ D := by
    rw [hDdef]
    exact Metric.diam_nonneg
  -- The image is bounded: it is the image of `[0, 2π]` under a continuous map.
  have hbdd : Bornology.IsBounded (Set.range K.curve) := by
    have hper : Function.Periodic K.curve (2 * Real.pi) := K.periodic
    have himg : K.curve '' Set.Icc (0 : ℝ) (0 + 2 * Real.pi) = Set.range K.curve :=
      hper.image_Icc hpipos 0
    rw [← himg]
    exact ((isCompact_Icc (a := (0 : ℝ)) (b := 0 + 2 * Real.pi)).image
      K.smooth.continuous).isBounded
  rcases eq_or_lt_of_le hLnonneg with hL0 | hLpos
  · -- Degenerate case: the curve has zero length.
    rw [← hL0]
    exact mul_nonneg (by linarith) hDnn
  · -- `G (2π) = L`, so `L/2` is an intermediate value of `G` on `[0, 2π]`.
    have hInt_nonneg : 0 ≤ ∫ u in (0 : ℝ)..(2 * Real.pi), speed K u :=
      intervalIntegral.integral_nonneg hpipos.le (fun u _ => norm_nonneg (deriv K.curve u))
    have hG2pi : G (2 * Real.pi) = L := by
      show (∫ u in (0 : ℝ)..(2 * Real.pi), speed K u) = L
      rw [hLdef, totalArcLength, parameterArcLength]
      exact (abs_of_nonneg hInt_nonneg).symm
    have hmem : L / 2 ∈ Set.Icc (G 0) (G (2 * Real.pi)) := by
      rw [hG0, hG2pi]
      exact ⟨by linarith, by linarith⟩
    obtain ⟨t, ht, hGt⟩ :=
      (isPreconnected_Icc.intermediate_value ⟨le_refl _, hpipos.le⟩ ⟨hpipos.le, le_refl _⟩
        hGcont.continuousOn) hmem
    have htlt : t < 2 * Real.pi := by
      rcases lt_or_eq_of_le ht.2 with hh | hh
      · exact hh
      · exfalso
        rw [hh, hG2pi] at hGt
        linarith
    have htIco : t ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨ht.1, htlt⟩
    have h0Ico : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨le_refl _, hpipos⟩
    -- At `t` the two complementary arcs both have length `L/2`.
    have hparam : parameterArcLength K 0 t = L / 2 := by
      rw [parameterArcLength]
      show |G t| = L / 2
      rw [hGt, abs_of_nonneg (by linarith)]
    have hintr : intrinsicDistance K 0 t = L / 2 := by
      rw [intrinsicDistance, hparam, min_eq_left (by linarith)]
    have hdist : intrinsicDistance K 0 t ≤ d * dist (K.curve 0) (K.curve t) :=
      h 0 h0Ico t htIco
    have hDle : dist (K.curve 0) (K.curve t) ≤ D := by
      rw [hDdef]
      exact Metric.dist_le_diam_of_mem hbdd ⟨0, rfl⟩ ⟨t, rfl⟩
    have hkey : L / 2 ≤ d * D := by
      calc L / 2 = intrinsicDistance K 0 t := hintr.symm
        _ ≤ d * dist (K.curve 0) (K.curve t) := hdist
        _ ≤ d * D := mul_le_mul_of_nonneg_left hDle hd.le
    linarith

end Work.PinchCounted
