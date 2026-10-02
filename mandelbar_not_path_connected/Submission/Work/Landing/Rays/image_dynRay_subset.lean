/-
# The image of a dynamic ray under `T_c`

For the antiholomorphic quadratic family `T_c(z) = z̄² + c` with a Böttcher coordinate `φ`, the
Böttcher equation `φ (T_c z) = conj (φ z)²` shows that `T_c` maps the dynamic ray at angle `θ`
into the dynamic ray at the angle

`angDouble θ = Int.fract (-2 θ) = -2 θ  (mod 1)`.

Indeed `φ z = r · e^{2πiθ}` with `r > 1` gives
`φ (T_c z) = conj (φ z)² = conj (r · e^{2πiθ})² = r² · e^{-4πiθ} = r² · e^{2πi (angDouble θ)}`,
and `r² > 1` again; the escaping set is preserved because `T_c z` is the first point of the orbit
of `z`, which escapes along with `z`.

The only angle arithmetic used is `rayDirection (angDouble θ) = conj (rayDirection θ)²`, where
`rayDirection θ = e^{2πiθ}` (`rayDirection_angDouble` below).
-/
import Mathlib
import Submission.Work.Landing.Rays

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Classical Function
open scoped ComplexConjugate
open LeanEval.ComplexAnalysis (Tantibar)
open Work.ParamRays (IsDynBottcher Escaping orbit orbit_succ)
open Work.Landing (rayDirection radialRay dynRay angDouble)

namespace Work.Landing.Rays

namespace ImageDynRay

/-! ## Angle arithmetic of the ray direction

`rayDirection θ = exp (2πiθ)` is invariant under `θ ↦ θ + m` for integers `m`, hence under
reduction of `θ` modulo `1`; conjugation negates the angle and squaring doubles it.  Together
these give `rayDirection (angDouble θ) = conj (rayDirection θ)²`. -/

theorem rayDirection_add_int (θ : ℝ) (m : ℤ) : rayDirection (θ + m) = rayDirection θ := by
  have h : ((2 * Real.pi * (θ + (m : ℝ)) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I + (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  simp only [rayDirection, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `rayDirection` only depends on the angle modulo `1`. -/
theorem rayDirection_fract (a : ℝ) : rayDirection (Int.fract a) = rayDirection a := by
  have h : Int.fract a = a + ((-⌊a⌋ : ℤ) : ℝ) := by
    rw [← Int.self_sub_floor a]
    push_cast
    ring
  rw [h, rayDirection_add_int]

/-- Conjugation inverts the angle: `conj (e^{2πiθ}) = e^{-2πiθ}`. -/
theorem rayDirection_neg (θ : ℝ) : rayDirection (-θ) = star (rayDirection θ) := by
  rw [rayDirection, rayDirection, ← starRingEnd_apply, ← Complex.exp_conj, starRingEnd_apply]
  congr 1
  rw [← starRingEnd_apply, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Squaring the direction doubles the angle. -/
theorem rayDirection_two (a : ℝ) : rayDirection (2 * a) = rayDirection a ^ 2 := by
  rw [rayDirection, rayDirection, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The effect of `T_c` on rays: `rayDirection (angDouble θ) = conj (rayDirection θ)²`. -/
theorem rayDirection_angDouble (θ : ℝ) :
    rayDirection (angDouble θ) = star (rayDirection θ) ^ 2 := by
  have h1 : angDouble θ = Int.fract (-2 * θ) := rfl
  rw [h1, rayDirection_fract]
  have h2 : -2 * θ = -(2 * θ) := by ring
  rw [h2]
  have h3 : rayDirection (-(2 * θ)) = star (rayDirection (2 * θ)) := rayDirection_neg (2 * θ)
  rw [h3, rayDirection_two, star_pow]

/-- The Böttcher coordinate of the image point: `conj (r · e^{2πiθ})² = r² · e^{2πi (angDouble θ)}`
with `r² > 1` again. -/
theorem star_mul_rayDirection_sq (r θ : ℝ) :
    star ((r : ℂ) * rayDirection θ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) * rayDirection (angDouble θ) := by
  rw [star_mul, mul_pow, rayDirection_angDouble]
  rw [show star (↑r : ℂ) = ↑r from by simp]
  push_cast
  ring

end ImageDynRay

/-- The image of the ray at angle `θ` under `T_c` is contained in the ray at angle
`angDouble θ`. -/
theorem image_dynRay_subset {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsDynBottcher c φ)
    (θ : ℝ) :
    LeanEval.ComplexAnalysis.Tantibar c '' Work.Landing.dynRay c φ θ ⊆
      Work.Landing.dynRay c φ ((Work.Landing.angDouble) θ) := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨r, hr, hφz⟩ := hz.2
  refine ⟨?_, r ^ 2, ?_, ?_⟩
  · -- `T_c z` is the first point of the escaping orbit of `z`
    have h1 : orbit c z 1 = Tantibar c z := by simp [orbit]
    rw [← h1]
    exact hz.1.iterate 1
  · -- `1 < r` gives `1 < r²`
    nlinarith
  · rw [h.2.1 z hz.1, hφz]
    exact ImageDynRay.star_mul_rayDirection_sq r θ

end Work.Landing.Rays
