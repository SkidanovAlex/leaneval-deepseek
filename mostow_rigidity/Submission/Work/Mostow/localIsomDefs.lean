import Mathlib
import Submission.Mostow.Interfaces

/-!
# Area L — localIsom : basic vocabulary

The hyperbolic "cosh" kernel `cdist` (which is `Hyper.cc`), the explicit unit-speed geodesic
segment `segfun p q` from `p` to `q`, and the lift `liftTan` of a chart tangent vector to the
ambient Minkowski space.  The Minkowski form itself is `Work.Mostow.mink_localIsomDefs` (from `Hyper`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}


/-- The Minkowski bilinear form `x₁y₁+…+xₙyₙ − x_{n+1}y_{n+1}` on `ℝ^{Fin n ⊕ Fin 1}`. -/
noncomputable def mink_localIsomDefs (x y : Fin n ⊕ Fin 1 → ℝ) : ℝ :=
  (∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i)) - x (Sum.inr 0) * y (Sum.inr 0)

theorem tpart_pos (u : E n) : 0 < tpart u := Real.sqrt_pos.2 (by positivity)

theorem tpart_sq (u : E n) : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := Real.sq_sqrt (by positivity)

theorem one_le_tpart_localIsomDefs (u : E n) : 1 ≤ tpart u := by
  rw [tpart, Real.le_sqrt (by norm_num) (by positivity)]
  simp

theorem hdist_comm' (u v : E n) : hdist u v = hdist v u := by
  simp [hdist, mul_comm, real_inner_comm]

/-- `cosh` of the hyperbolic distance, as an explicit function of the chart points. -/
noncomputable def cdist (p q : E n) : ℝ := tpart p * tpart q - inner ℝ p q

/-- The unit-speed geodesic segment from `p` to `q`, parametrised by arclength on `[0, hdist p q]`. -/
noncomputable def segfun (p q : E n) (s : ℝ) : E n :=
  (Real.sinh (hdist p q - s) / Real.sinh (hdist p q)) • p +
    (Real.sinh s / Real.sinh (hdist p q)) • q

/-- The tangent vector of the hyperboloid at `hlift u` whose chart part is `v`. -/
noncomputable def liftTan (u v : E n) : Fin n ⊕ Fin 1 → ℝ :=
  Sum.elim (fun i => v i) (fun _ => inner ℝ u v / tpart u)

/-- The chart (spatial) coordinates of a vector of the ambient Minkowski space. -/
noncomputable def spatial (W : Fin n ⊕ Fin 1 → ℝ) : E n :=
  WithLp.toLp 2 (fun i => W (Sum.inl i))

/-- The time coordinate of a vector of the ambient Minkowski space. -/
def tcoord (W : Fin n ⊕ Fin 1 → ℝ) : ℝ := W (Sum.inr 0)

@[simp] theorem spatial_hlift (u : E n) : spatial (hlift u) = u := by
  simp [spatial, hlift]

@[simp] theorem tcoord_hlift (u : E n) : tcoord (hlift u) = tpart u := rfl

@[simp] theorem spatial_smul (c : ℝ) (W : Fin n ⊕ Fin 1 → ℝ) :
    spatial (c • W) = c • spatial W := rfl

@[simp] theorem spatial_add (V W : Fin n ⊕ Fin 1 → ℝ) : spatial (V + W) = spatial V + spatial W := rfl

@[simp] theorem tcoord_smul (c : ℝ) (W : Fin n ⊕ Fin 1 → ℝ) : tcoord (c • W) = c * tcoord W := rfl

@[simp] theorem tcoord_add (V W : Fin n ⊕ Fin 1 → ℝ) : tcoord (V + W) = tcoord V + tcoord W := rfl

end Work.Mostow
