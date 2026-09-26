import ChallengeDeps

/-!
# The standard torus of revolution: parametrisation, meridians and longitudes

`ChallengeDeps` defines the standard `(p,q)`-torus curve by an explicit formula.
Here we introduce the underlying parametrisation of the torus of revolution with
major radius `2` and minor radius `1`, so that the standard curve is the image of
the straight line of slope `(p,q)` in the parameter torus `ℝ²/2πℤ²`.

These definitions are the vocabulary in which the geometric and topological
lemmas about the standard torus are stated.

Terminology: the *meridian circle* at parameter `θ` is the level set
`{θ = const}` of the parametrisation (a "small" circle, the boundary of a
meridian disk of the inner solid torus); the *longitude circle* at parameter `φ`
is the level set `{φ = const}` (a "big" circle going around the axis).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.Core

/-- The parametrisation of the torus of revolution with major radius `2` and
minor radius `1`: `θ` is the angle around the axis, `φ` the angle around a
meridian. -/
noncomputable def torusMap (θ φ : ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then
      (2 + Real.cos φ) * Real.cos θ
    else if i.val = 1 then
      (2 + Real.cos φ) * Real.sin θ
    else
      Real.sin φ)

/-- The standard `(p,q)`-torus curve is the image of the straight line
`t ↦ (p t, q t)` in the parameter torus. -/
theorem standardTorusCurve_eq_torusMap (p q : ℕ) (t : ℝ) :
    standardTorusCurve p q t = torusMap ((p : ℝ) * t) ((q : ℝ) * t) := rfl

/-- The parametrisation is `2π`-periodic in the first (longitude) variable. -/
theorem torusMap_add_two_pi_left (θ φ : ℝ) :
    torusMap (θ + 2 * Real.pi) φ = torusMap θ φ := by
  unfold torusMap
  simp [Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The parametrisation is `2π`-periodic in the second (meridian) variable. -/
theorem torusMap_add_two_pi_right (θ φ : ℝ) :
    torusMap θ (φ + 2 * Real.pi) = torusMap θ φ := by
  unfold torusMap
  simp [Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The **meridian circle** at parameter `θ`: the level set `{θ = const}` of the
parametrisation.  It is a circle of radius `1` around the tube, i.e. the boundary
of a meridian disk of the solid torus bounded by the standard torus. -/
noncomputable def meridianCircle (θ : ℝ) : ℝ → R3 := fun φ => torusMap θ φ

/-- The meridian circle is `2π`-periodic. -/
theorem meridianCircle_periodic (θ φ : ℝ) :
    meridianCircle θ (φ + 2 * Real.pi) = meridianCircle θ φ :=
  torusMap_add_two_pi_right θ φ

/-- The **longitude circle** at parameter `φ`: the level set `{φ = const}` of the
parametrisation.  It is a circle around the axis of the torus. -/
noncomputable def longitudeCircle (φ : ℝ) : ℝ → R3 := fun θ => torusMap θ φ

/-- The longitude circle is `2π`-periodic. -/
theorem longitudeCircle_periodic (φ θ : ℝ) :
    longitudeCircle φ (θ + 2 * Real.pi) = longitudeCircle φ θ :=
  torusMap_add_two_pi_left θ φ

/-- The standard torus of revolution, as a subset of `ℝ³`. -/
noncomputable def standardTorus : Set R3 := Set.range (fun p : ℝ × ℝ => torusMap p.1 p.2)

/-- The curve `t ↦ torusMap (θ₀ + t) φ₀` traces the longitude circle at `φ₀`. -/
theorem longitudeCircle_eq (θ₀ φ₀ t : ℝ) :
    longitudeCircle φ₀ (θ₀ + t) = torusMap (θ₀ + t) φ₀ := rfl

end Work.Core
