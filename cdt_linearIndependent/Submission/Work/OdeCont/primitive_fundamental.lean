import Mathlib

/-!
# The fundamental theorem of calculus for the straight segment

If `g` is a primitive of `G` on a convex set `U` (i.e. `HasDerivAt g (G w) w` for `w ∈ U`)
and `G` is continuous on `U`, then for `z₀, z ∈ U`

`g z - g z₀ = ∫ t in 0..1, (z - z₀) • G (z₀ + t • (z - z₀))`.

This is the (elementary) complex fundamental theorem of calculus along the segment
from `z₀` to `z`, and is the key analytic input of the Picard iteration for
`Work.OdeCont.local_existence`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.OdeCont

theorem primitive_fundamental {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V]
    (g G : ℂ → V) (z₀ z : ℂ) (U : Set ℂ)
    (hU : Convex ℝ U) (hz₀ : z₀ ∈ U) (hz : z ∈ U)
    (hg : ∀ w ∈ U, HasDerivAt g (G w) w) (hG : ContinuousOn G U) :
    g z - g z₀ = ∫ t in (0:ℝ)..1, (z - z₀) • G (z₀ + t • (z - z₀)) := by
  set φ : ℝ → V := fun t => g (z₀ + t • (z - z₀)) with hφ
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, z₀ + t • (z - z₀) ∈ U := by
    intro t ht
    have h1 : (AffineMap.lineMap z₀ z) t ∈ U :=
      hU.segment_subset hz₀ hz (lineMap_mem_segment ℝ z₀ z ht)
    simpa [AffineMap.lineMap_apply, add_comm] using h1
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt φ ((z - z₀) • G (z₀ + t • (z - z₀))) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one] at ht
    have hw : z₀ + t • (z - z₀) ∈ U := hmem t ht'
    have h1 : HasDerivAt (fun s : ℝ => z₀ + s • (z - z₀)) (z - z₀) t := by
      have h2 : HasDerivAt (fun s : ℝ => s • (z - z₀)) (z - z₀) t := by
        simpa using (hasDerivAt_id t).smul_const (z - z₀)
      simpa using h2.const_add z₀
    exact (hg _ hw).scomp t h1
  have hcont : ContinuousOn (fun t : ℝ => (z - z₀) • G (z₀ + t • (z - z₀)))
      (Set.uIcc (0:ℝ) 1) := by
    apply ContinuousOn.const_smul
    apply hG.comp _ _
    · exact (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
    · intro t ht
      have ht' : t ∈ Set.Icc (0:ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one] at ht
      exact hmem t ht'
  have hint : IntervalIntegrable (fun t : ℝ => (z - z₀) • G (z₀ + t • (z - z₀)))
      volume (0:ℝ) 1 := hcont.intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1) (f := φ)
      (f' := fun t => (z - z₀) • G (z₀ + t • (z - z₀))) hderiv hint
  rw [h]
  simp [hφ]

end Work.OdeCont
