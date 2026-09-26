import Mathlib
import Submission.Work.Sweep.Defs

/-!
# Almost every concentric sphere meets the curve transversally

For a smooth knot `K` and a centre `x`, the set of radii `r` for which the sphere
of centre `x` and radius `r` is *not* transverse to `K` has measure zero.

## Strategy

Write `g t = dist (K.curve t) x` for the distance from the centre to the curve.
A radius `r` is bad when some parameter `t ∈ [0, 2π]` with `K.curve t ∈ sphere x r`
also satisfies `deriv g t = 0`, and then `r = g t` is the image of a critical point
of `g`.  So the bad radii form a subset of `g '' S`, where

`S = {t ∈ [0, 2π] | deriv g t = 0}`

is the critical set of `g` inside the fundamental interval.

Splitting `S` into the (at most two) parameters at which `K.curve t = x` — those
map to the single radius `0` — and the rest, on which `g` is differentiable, the
image of the critical set is a null set by Sard's lemma in dimension one
(`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`).

Nothing here uses the specifics of the curve: the result holds for any smooth
`2π`-periodic immersion and centre.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Work.Sweep.AeTransverseSphere

theorem ae_transverse_sphere (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (x : LeanEval.KnotTheory.PardonDistortion.R3) :
    ∀ᵐ r ∂MeasureTheory.volume, Work.Sweep.IsTransverseSphere K x r := by
  classical
  -- the distance to the centre, as a function of the curve parameter
  let g : ℝ → ℝ := fun t => dist (K.curve t) x
  -- the critical set of `g` inside the fundamental interval
  let S : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧ deriv g t = 0}
  -- the parameters at which the curve passes through the centre
  let B : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧ K.curve t = x}
  -- `g` is differentiable off the centre
  have hgdiff : ∀ t, K.curve t ≠ x → DifferentiableAt ℝ g t := by
    intro t ht
    exact DifferentiableAt.norm ℝ
      (((K.smooth.differentiable (by simp)).differentiableAt).sub_const x) (sub_ne_zero.mpr ht)
  -- the image of the critical set is null
  have hSnull : MeasureTheory.volume (g '' S) = 0 := by
    have hsub : g '' S ⊆ g '' B ∪ g '' (S \ B) := by
      rintro y ⟨t, ht, rfl⟩
      by_cases hB : t ∈ B
      · exact Or.inl ⟨t, hB, rfl⟩
      · exact Or.inr ⟨t, ⟨ht, hB⟩, rfl⟩
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · -- everything in `B` is mapped to the single value `0`
      refine measure_mono_null ?_ (measure_singleton (0 : ℝ))
      rintro y ⟨t, ht, rfl⟩
      simp only [B] at ht
      simp [g, ht.2]
    · -- off `B`, Sard's lemma applies to the set `S \ B`
      have hder : ∀ t ∈ S \ B,
          HasFDerivWithinAt g (ContinuousLinearMap.toSpanSingleton ℝ (deriv g t))
            (S \ B) t := by
        intro t ht
        have htx : K.curve t ≠ x := by
          intro h
          exact ht.2 (by simp only [B]; exact ⟨ht.1.1, h⟩)
        exact ((hgdiff t htx).hasDerivAt.hasFDerivAt).hasFDerivWithinAt
      have hdet : ∀ t ∈ S \ B,
          (ContinuousLinearMap.toSpanSingleton ℝ (deriv g t)).det = 0 := by
        intro t ht
        rw [ContinuousLinearMap.det_toSpanSingleton]
        exact ht.1.2
      exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero MeasureTheory.volume hder hdet
  -- a bad radius is the image of a critical point
  rw [ae_iff]
  refine measure_mono_null ?_ hSnull
  intro r hr
  simp only [Set.mem_ofPred_eq] at hr
  rw [Work.Sweep.IsTransverseSphere] at hr
  push Not at hr
  obtain ⟨t, ht, hd⟩ := hr
  exact ⟨t, ⟨ht.2, hd⟩, Metric.mem_sphere.mp ht.1⟩

end Work.Sweep.AeTransverseSphere
