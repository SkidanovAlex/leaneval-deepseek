import Mathlib

/-!
# Torus data: the angle of a plane rotation

Helper vocabulary for `Work.Mostow.torusData`.  For an ordered pair of vectors `u, v` spanning an
oriented plane and a linear isometry `c` of an inner product space, `rotZ u v c` is the complex
number `⟪c u, u⟫ + ⟪c u, v⟫ * I`.  If `(u,v)` is an orthonormal basis of a `c`-invariant plane on
which `c` acts as a rotation (rather than a reflection), then `rotZ u v c` is that rotation,
viewed as a unit complex number.
-/

namespace Work.Mostow

noncomputable section

/-- The complex number encoding the first column of `c` with respect to the ordered pair `(u,v)`:
`rotZ u v c = ⟪c u, u⟫ + ⟪c u, v⟫ * I`. -/
def rotZ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (u v : V)
    (c : V ≃ₗᵢ[ℝ] V) : ℂ :=
  (inner ℝ (c u) u : ℂ) + (inner ℝ (c u) v : ℂ) * Complex.I

/-- `c` acts on the oriented plane spanned by the ordered pair `(u,v)` as a rotation. -/
def IsRot {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (u v : V)
    (c : V ≃ₗᵢ[ℝ] V) : Prop :=
  ∃ t : ℝ, c u = Real.cos t • u + Real.sin t • v ∧
    c v = -Real.sin t • u + Real.cos t • v

end

end Work.Mostow
