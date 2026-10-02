import Mathlib
import Submission.Work.Bottcher.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Rays

open Work.Bottcher

/-- The point of the unit circle at angle `θ`, squared, is the point at angle
`2θ`.  (Consequence of the addition formula for `Complex.exp`.) -/
private lemma rayDirection_sq (θ : ℝ) : (rayDirection θ) ^ 2 = rayDirection (2 * θ) := by
  rw [rayDirection, rayDirection, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Complex conjugation sends the point of the unit circle at angle `θ` to the
one at angle `-θ`. -/
private lemma conj_rayDirection (θ : ℝ) :
    (starRingEnd ℂ) (rayDirection θ) = rayDirection (-θ) := by
  rw [rayDirection, rayDirection, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The tricorn map `T_c` acts on dynamic rays of an arbitrary Böttcher coordinate
`φ` (satisfying `φ ∘ T_c = conj ∘ φ^2`) by the angle-doubling map `θ ↦ -2θ`:
the `T_c`-image of the angle-`θ` ray is contained in the angle-`(-2θ)` ray.

Indeed, if `φ z = r · e^{2πiθ}` with `r > 1`, then
`φ (T_c z) = conj(φ z)^2 = conj(r e^{2πiθ})² = r² e^{-4πiθ}
= r² · e^{2πi(-2θ)}`, with `r² > 1`. -/
theorem Tantibar_maps_dynamicRayOf (c : ℂ) (φ : ℂ → ℂ)
    (hφ : ∀ z : ℂ, φ (LeanEval.ComplexAnalysis.Tantibar c z) = (starRingEnd ℂ) (φ z) ^ 2) (θ : ℝ) :
    LeanEval.ComplexAnalysis.Tantibar c '' Work.Bottcher.dynamicRayOf φ θ
      ⊆ Work.Bottcher.dynamicRayOf φ (-2 * θ) := by
  rintro w ⟨z, ⟨r, hr, hrz⟩, rfl⟩
  refine ⟨r ^ 2, by nlinarith, ?_⟩
  rw [hφ z, hrz, map_mul, Complex.conj_ofReal, conj_rayDirection, mul_pow,
    ← Complex.ofReal_pow, rayDirection_sq]
  norm_num

end Work.Bottcher.Rays
