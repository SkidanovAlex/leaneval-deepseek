import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.Frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the Kato identity `Δ|∇Rm|² = 2|∇∇Rm|² + 2⟨∇Rm, Δ∇Rm⟩`

This module fixes the objects used in the computation of the Laplacian of the squared norm of `∇Rm`
in a frame `W` at a point `x`:

* `Sof g W α` is the component `(α 0), …, (α 4)` of `∇Rm` in the frame `W`, as a function on `M`;
* `Avec g W x m γ = ∇_{W m x}(∇_{W m} W γ)` is the second derivative of the frame at `x`;
* `slot x e A α j` is the family of frame vectors with slot `j` replaced by the vector `A`;
* `P5 g x v` is `covRm g x` evaluated on a family of five vectors;
* `D1`, `D2` are the components of `∇∇Rm` and `∇∇∇Rm` in the frame `onFrame g x`;
* `Left g W x α m` is the second-order frame correction (the "leftover") in the computation of the
  second derivative of `Sof g W α` in the direction `W m x`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The component `(α 0), …, (α 4)` of `∇Rm` in the frame `W`, as a function on `M`. -/
noncomputable abbrev Sof (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (α : Fin 5 → Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun y => covRm g y (W (α 0) y) (W (α 1) y) (W (α 2) y) (W (α 3) y) (W (α 4) y)

/-- `∇_{W m x}(∇_{W m} W γ)`: the second derivative of the frame at `x`. -/
noncomputable abbrev Avec (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (m γ : Fin (Module.finrank ℝ E)) : TangentSpace I x :=
  lcOf g (fun p : M ↦ lcOf g (W γ) p (W m p)) x (W m x)

/-- The family of five vectors with slot `j` replaced by `A`. -/
abbrev slot {n : ℕ} (x : M) (e : Fin n → TangentSpace I x) (A : TangentSpace I x)
    (α : Fin 5 → Fin n) (j : Fin 5) : Fin 5 → TangentSpace I x :=
  fun s => if s = j then A else e (α s)

/-- `covRm g x` evaluated on a family of five vectors. -/
noncomputable abbrev P5 (g : SMet I M) (x : M) (v : Fin 5 → TangentSpace I x) : ℝ :=
  covRm g x (v 0) (v 1) (v 2) (v 3) (v 4)

/-- The second-order frame correction in the second derivative of the component `Sof g W α` in the
direction `W m x`. -/
noncomputable abbrev Left (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (α : Fin 5 → Fin (Module.finrank ℝ E)) (m : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ j : Fin 5, P5 g x (slot x (fun i => onFrame g x i) (Avec g W x m (α j)) α j)

/-- The components of `∇∇Rm` in the frame `onFrame g x`. -/
noncomputable abbrev D1 (g : SMet I M) (x : M) (α : Fin 5 → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) : ℝ :=
  cov2Rm g x (onFrame g x m) (onFrame g x (α 0)) (onFrame g x (α 1)) (onFrame g x (α 2))
    (onFrame g x (α 3)) (onFrame g x (α 4))

/-- The components of `∇∇∇Rm` in the frame `onFrame g x`. -/
noncomputable abbrev D2 (g : SMet I M) (x : M) (α : Fin 5 → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) : ℝ :=
  cov3Rm g x (onFrame g x m) (onFrame g x m) (onFrame g x (α 0)) (onFrame g x (α 1))
    (onFrame g x (α 2)) (onFrame g x (α 3)) (onFrame g x (α 4))

end Work.Diff.GE
