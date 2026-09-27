import Mathlib
import Submission.Work.Drive.Interfaces

/-!
# The capping of the configuration Möbius strip: shared definitions

Hugelmeyer's proof of Theorem 1 caps the configuration Möbius strip `M` of a smooth plane curve by
gluing the boundary torus of the configuration space to a solid torus of "caps".  In coordinates, the
gluing is (proof of Theorem 1 in the paper)

`f (r, e^{iθ}, e^{iφ}) = (r cos φ, r sin φ, e^{i(2φ + θ)}, 0)`:

`(r, θ, φ)` are coordinates on the boundary torus of the cap solid torus `(0,∞) × S¹ × D²` (`θ` the
`S¹`-coordinate, `φ` the disk angle) and `(ψ, η)` on the boundary torus `(ℝ² ∖ {0}) × S¹ × {0}` of the
configuration space (`ψ` the position angle, `η` the doubled direction).  The gluing is therefore, at
the level of the two torus boundaries, the map `(θ, φ) ↦ (ψ, η) = (φ, θ + 2φ)`.

This file contains that map (`glueTorus`), its basic properties (proven here), and the polar
parametrisation of the punctured plane (`polarLift`) which identifies the position-angle coordinate
of the configuration boundary torus with the circle `ℝ/ℤ`.  The two facts are the two halves of the
capping's *identification* step: they are what turns the `(2,1)`-torus knot `∂M` (the doubled tangent
direction winds twice over a period — `Work.Drive.doubledTangent_winding`) into a *meridian* of the
cap, i.e. a curve bounding a disk there.  That is the input the chain-level representative of
Hugelmeyer's class `ω_P` needs (`Work.Drive.chainParity`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- The polar parametrisation of the punctured plane with `ℝ/ℤ`-valued angle, before descending to the
circle: `(r, ψ) ↦ (r cos (2πψ), r sin (2πψ))`.  It is `ℤ`-periodic in `ψ`, and it induces the
homeomorphism/diffeomorphism `(0,∞) × (ℝ/ℤ) ≅ ℝ² ∖ {0}` that identifies the position-angle coordinate
of the configuration boundary torus. -/
noncomputable def polarLift (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * Real.cos (2 * Real.pi * p.2), p.1 * Real.sin (2 * Real.pi * p.2))

/-- The torus-level gluing of the capping: `(θ, φ) ↦ (φ, θ + 2φ)`.  It carries the boundary torus of
the cap solid torus onto the boundary torus of `(ℝ² ∖ {0}) × S¹ × {0}`. -/
def glueTorus (p : UnitAddCircle × UnitAddCircle) : UnitAddCircle × UnitAddCircle :=
  (p.2, p.1 + 2 • p.2)

/-- The meridian circles of the cap solid torus: the boundary of the disk `{r} × {θ₀} × D²`. -/
def meridian (θ₀ : UnitAddCircle) : Set (UnitAddCircle × UnitAddCircle) := {p | p.1 = θ₀}

/-- The `(2,1)`-torus-knot family of the configuration boundary torus: the curves of class `T(2,1)`,
i.e. the curves along which the position angle winds once while the doubled direction winds twice. -/
def t21 (θ₀ : UnitAddCircle) : Set (UnitAddCircle × UnitAddCircle) :=
  {q | q.2 = 2 • q.1 + θ₀}


/-- The radial parametrisation of `ℝ³` minus the origin: `v ↦ (‖v‖, v / ‖v‖)`.  Hugelmeyer's proof of
Lemma 5 uses it to identify `ℝ² × [0,∞) ∖ {(0,0)}` with `(0,∞) × D²`, where `D²` is the half of the
unit sphere of `ℝ³` consisting of the points with non-negative third coordinate; the product of that
disk-bundle structure with `S¹` gives the fibration of the configuration space minus its axis by solid
tori, which is the first step of the capping. -/
noncomputable def radialMap (p : EuclideanSpace ℝ (Fin 3)) : ℝ × EuclideanSpace ℝ (Fin 3) :=
  (‖p‖, (‖p‖)⁻¹ • p)


/-- The gluing of the capping on the level of the boundary torus of the configuration space, in the
universal cover coordinates `(r, θ, φ) ∈ ℝ³` (`r > 0` the radius, `θ` the `S¹`-coordinate of the cap
solid torus, `φ` the disk angle): position `polarLift (r, φ)` and doubled direction `2φ + θ`.  This is
Hugelmeyer's `f (r, e^{iθ}, e^{iφ}) = (r cos φ, r sin φ, e^{i(2φ + θ)}, 0)`; it is `ℤ`-periodic in both
`θ` and `φ`, hence descends to the map `(0,∞) × (ℝ/ℤ)² → (ℝ² ∖ {0}) × ℝ/ℤ` of the gluing. -/
noncomputable def glueSpace (p : ℝ × ℝ × ℝ) : (ℝ × ℝ) × UnitAddCircle :=
  (polarLift (p.1, p.2.2), ((2 * p.2.2 + p.2.1 : ℝ) : UnitAddCircle))

lemma glueTorus_apply (p : UnitAddCircle × UnitAddCircle) :
    glueTorus p = (p.2, p.1 + 2 • p.2) := rfl

/-- The gluing is additive on the torus group: it is the linear map with matrix `[[0,1],[1,2]]`. -/
lemma glueTorus_add (p q : UnitAddCircle × UnitAddCircle) :
    glueTorus (p + q) = glueTorus p + glueTorus q := by
  ext <;> simp [glueTorus, add_assoc, add_comm, add_left_comm, nsmul_add]

/-- The gluing is a bijection of the torus: its matrix `[[0,1],[1,2]]` has determinant `-1`.  The
inverse is `(ψ, η) ↦ (η - 2ψ, ψ)`. -/
lemma glueTorus_bijective : Function.Bijective glueTorus := by
  refine ⟨?_, ?_⟩
  · rintro ⟨θ, φ⟩ ⟨θ', φ'⟩ h
    have h1 : φ = φ' := congrArg Prod.fst h
    have h2 : θ + 2 • φ = θ' + 2 • φ' := congrArg Prod.snd h
    refine Prod.ext ?_ ?_
    · rw [h1] at h2
      exact add_right_cancel h2
    · exact h1
  · rintro ⟨ψ, η⟩
    refine ⟨(η - 2 • ψ, ψ), ?_⟩
    ext <;> simp [glueTorus]

/-- **The gluing carries the `(2,1)`-torus knots to meridians.**  A point of the configuration boundary
torus lies on the `(2,1)`-curve `t21 θ₀` if and only if its preimage under the gluing is a point of the
meridian `meridian θ₀` of the cap.  Consequently the curve of class `T(2,1)` — in particular the
boundary `∂M` of the configuration Möbius strip, whose doubled tangent direction winds twice — becomes,
after the gluing, the boundary of a disk of the cap. -/
lemma glueTorus_preimage_t21 (θ₀ : UnitAddCircle) : glueTorus ⁻¹' t21 θ₀ = meridian θ₀ := by
  ext p
  simp only [Set.mem_preimage, t21, Set.mem_ofPred_eq, meridian, glueTorus]
  constructor
  · intro h
    exact add_left_cancel (by rw [add_comm]; exact h)
  · intro h
    rw [h, add_comm]

/-- Image form of `glueTorus_preimage_t21`. -/
lemma glueTorus_image_meridian (θ₀ : UnitAddCircle) : glueTorus '' meridian θ₀ = t21 θ₀ := by
  rw [← glueTorus_preimage_t21 θ₀]
  exact Set.image_preimage_eq _ glueTorus_bijective.surjective

end Work.Drive
