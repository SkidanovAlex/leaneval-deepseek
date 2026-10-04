import Mathlib
import Submission.Diff.Interfaces
import Submission.Geodesic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the restart/splice step of the continuation theorem (area `EXT`)

This file sets up the *coordinate* language in which the smoothness of the spliced family
`t ↦ (if t ≤ T then G t else H (t - T))` is proved.

Fix a chart centre `x₀ : M` and the canonical basis `bB` of the model space `E` (indices
`Fin (Module.finrank ℝ E)`).  The **chart matrix** of a smooth metric `g` is the matrix of `g` in
the coordinate frame `σ_i = frameVector I x₀ · (bB i)` of the chart at `x₀`:

`chartMatFun g x₀ y i j = g.inner p (σ_i) (σ_j)`,  `p = (extChartAt I x₀).symm y`,

a function `E → Matrix _ _ ℝ` of the *chart coordinate* `y`; the same formula with `g = G t` gives
the time-dependent `chartMat G x₀ : ℝ → E → Matrix _ _ ℝ`, and replacing `g.inner` by the Ricci
form of the Levi-Civita connection of `g` gives `chartRicMat g x₀`.

The point of using the matrix (rather than the bilinear form on the tangent space) is that all
derivatives in the sequel are ordinary Fréchet derivatives on the model space `E` of a
finite-dimensional normed space.

The **spatial `2`-jet** `jet2 u` of `u : ℝ × E → F` records `u`, its first and its second spatial
derivative:

`jet2 u p = (u p, fderiv ℝ (fun y => u (p.1, y)) p.2, fderiv ℝ (fun y => fderiv ℝ (fun y' => u (p.1, y')) y) p.2)`.

The main geometric input for the splice step (a separate, delegated lemma) is that the chart Ricci
matrix is a smooth function of the spatial `2`-jet of the chart matrix:

`∃ Φ, ContDiff ℝ ⊤ Φ ∧ ∀ g x₀ y, chartRicMat g x₀ y = Φ (y, jet2 (chartMatFun g x₀) (0, y))`.

Once this is available the Ricci-flow equation `∂ₜ g = -2 Ric(g)` becomes, in the chart, the
quasilinear parabolic system `∂ₜ u = -2 • Φ (·, jet2 u)` for `u = chartMat (G ·) x₀`, and the
spliced family is smooth because the time-jets of a solution of such a system at a time are
determined by its *spatial* jets at that time, and the two sides of the splice have equal spatial
jets at `T` (both are the chart matrix of the metric `G T = H 0`).
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]

/-- The canonical basis of the model space used for all matrix indices. -/
noncomputable abbrev bB : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E

/-- The finite-dimensional space in which the chart matrix of a metric takes its values. -/
abbrev MatE : Type _ := Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ

/-- **The chart matrix of a metric**: the matrix of `g` in the coordinate frame of the chart at
`x₀`, as a function of the chart coordinate `y`. -/
noncomputable def chartMatFun (g : Submission.Diff.SMet I M) (x₀ : M) : E → MatE (E := E) :=
  fun y i j =>
    g.inner ((extChartAt I x₀).symm y)
      (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) (bB i))
      (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) (bB j))

/-- **The chart matrix of a family of metrics**, as a function of time and of the chart
coordinate. -/
noncomputable def chartMat (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) :
    ℝ → E → MatE (E := E) :=
  fun t => chartMatFun (G t) x₀

/-- **The chart Ricci matrix**: the Ricci tensor of the Levi-Civita connection of `g`, in the
coordinate frame of the chart at `x₀`, as a function of the chart coordinate `y`. -/
noncomputable def chartRicMat (g : Submission.Diff.SMet I M) (x₀ : M) : E → MatE (E := E) :=
  fun y i j =>
    Submission.Diff.ricAt (Submission.Diff.lcOf g) ((extChartAt I x₀).symm y)
      (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) (bB i))
      (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) (bB j))

/-- The **spatial `2`-jet** of `u : ℝ × E → F`: the value, the first and the second spatial Fréchet
derivative at a point. -/
noncomputable def jet2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (u : ℝ × E → F) :
    ℝ × E → (F × (E →L[ℝ] F) × (E →L[ℝ] (E →L[ℝ] F))) :=
  fun p =>
    (u p,
     fderiv ℝ (fun y : E => u (p.1, y)) p.2,
     fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => u (p.1, y')) y) p.2)

theorem jet2_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℝ × E → F) (p : ℝ × E) :
    jet2 (E := E) u p =
      (u p, fderiv ℝ (fun y : E => u (p.1, y)) p.2,
       fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => u (p.1, y')) y) p.2) := rfl

/-- The partial derivative of a `MatE`-valued function in the direction of the `k`-th basis vector
of the model space.  Note that `MatE` is a type of scalar arrays, so this is again `MatE`-valued
(and, in particular, no space of continuous linear maps appears). -/
noncomputable def dPart (u : ℝ × E → MatE (E := E)) (k : Fin (Module.finrank ℝ E)) :
    ℝ × E → MatE (E := E) :=
  fun p => fderiv ℝ (fun y : E => u (p.1, y)) p.2 (bB (E := E) k)

/-- The **scalar (partial derivative) `2`-jet** of a `MatE`-valued function `u`: the value of `u`,
its first coordinate partial derivatives and its second coordinate partial derivatives. -/
noncomputable def sJetData (u : ℝ × E → MatE (E := E)) :
    ℝ × E → (MatE (E := E) × (Fin (Module.finrank ℝ E) → MatE (E := E)) ×
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → MatE (E := E))) :=
  fun p => (u p, fun k => dPart u k p, fun k l => dPart (dPart u l) k p)

theorem sJetData_apply (u : ℝ × E → MatE (E := E)) (p : ℝ × E) :
    sJetData u p = (u p, fun k => dPart u k p, fun k l => dPart (dPart u l) k p) := rfl

end Work.Diff.EXT
