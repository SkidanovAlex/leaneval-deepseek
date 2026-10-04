import Mathlib
import Submission.Diff.Grad
import Submission.CurvatureVec
import Submission.ChartCurv
import Submission.ChartBounds
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The scalar curvature in local coordinates

This file sets up the *explicit* local-coordinate expressions for the Levi-Civita connection, the
curvature, the Ricci tensor, the scalar curvature and the Laplace operator of a smooth metric
`g : SMet I M`, in the chart at a point `x₀`.

The point of the file is that every object is an **explicit function of the metric coefficients**
and their derivatives (in particular `∂ₜ`-differentiable along a Ricci flow), so that the classical
computation `∂ₜ scal = Δ scal + 2|Ric|²` becomes an algebraic identity.

All definitions are stated with the explicit bilinear form `g.inner` so that they can be used for a
*time-dependent* family of metrics; the bridge to the library's `chartGram`-based API is the
(rfl-level) lemma `cGram_eq_chartGram`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Curvature
open Submission.CurvatureVec
open Submission.Geodesic
open Submission.ChartCurv
open Submission.ChartConnection
open Submission.ChartBounds

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The coordinate basis of `E` used for all index expansions. -/
local notation "bb" => Module.finBasis ℝ E

/-- The Riemannian bundle structure induced by a smooth metric. -/
@[reducible] noncomputable def gInst (g : SMet I M) : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
  ⟨g.toRiemannianMetric⟩

/-- **The metric coefficients in the chart at `x₀`**, expressed with the explicit metric `g`. -/
noncomputable def cGram (g : SMet I M) (x₀ p : M) (a b : E) : ℝ :=
  g.inner p (frameVector x₀ p a) (frameVector x₀ p b)

/-- The matrix of metric coefficients at `p` in the chart at `x₀`. -/
noncomputable def cGramM (g : SMet I M) (x₀ p : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j => cGram g x₀ p (bb i) (bb j)

/-- The inverse metric coefficients at `p` in the chart at `x₀`. -/
noncomputable def cGramInv (g : SMet I M) (x₀ p : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (cGramM g x₀ p)⁻¹

/-- The Christoffel symbols `Γ^k_{ij} = (∇_{∂ᵢ}∂ⱼ)^k` in the chart at `x₀`. -/
noncomputable def cGam (g : SMet I M) (x₀ p : M)
    (k i j : Fin (Module.finrank ℝ E)) : ℝ :=
  ((bb).coord k) (chrB (lcOf g) x₀ p (bb j) (bb i))

/-- The coordinate derivative `∂ᵢu` of a function, in the chart at `x₀`. -/
noncomputable def cDiff (g : SMet I M) (x₀ : M) (u : M → ℝ) (p : M)
    (i : Fin (Module.finrank ℝ E)) : ℝ :=
  mvfderiv I u p (frameVector x₀ p (bb i))

/-- The coordinate second derivative `∂ᵢ∂ⱼu`. -/
noncomputable def cDiff2 (g : SMet I M) (x₀ : M) (u : M → ℝ) (p : M)
    (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  mvfderiv I (fun q => cDiff g x₀ u q j) p (frameVector x₀ p (bb i))

/-- The coordinate Hessian `∂ᵢ∂ⱼu − Γ^k_{ij}∂_k u`. -/
noncomputable def cHess (g : SMet I M) (x₀ : M) (u : M → ℝ) (p : M)
    (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  cDiff2 g x₀ u p i j - ∑ k, cGam g x₀ p k i j * cDiff g x₀ u p k

/-- **The Laplace operator in coordinates**: `Δu = γ^{ij}(∂ᵢ∂ⱼu − Γ^k_{ij}∂_k u)`. -/
noncomputable def cLapl (g : SMet I M) (x₀ : M) (u : M → ℝ) (p : M) : ℝ :=
  ∑ i, ∑ j, cGramInv g x₀ p i j * cHess g x₀ u p i j

/-- The coordinate vector of `R(σ_a, σ_b)σ_d` in the chart at `x₀`, from `curvVec_eq_chart`. -/
noncomputable def cCurv (g : SMet I M) (x₀ p : M) (a b d : E) : E :=
  dB (lcOf g) x₀ p a d b - dB (lcOf g) x₀ p b d a
    + chrB (lcOf g) x₀ p (chrB (lcOf g) x₀ p d b) a
    - chrB (lcOf g) x₀ p (chrB (lcOf g) x₀ p d a) b

/-- The curvature components `R_{abcd} = ⟪R(σ_a,σ_b)σ_d, σ_c⟫` in the chart at `x₀`. -/
noncomputable def cRm (g : SMet I M) (x₀ p : M) (a b c d : E) : ℝ :=
  cGram g x₀ p (cCurv g x₀ p a b d) c

/-- The chart Ricci tensor `Ric_{ij} = γ^{kl}R_{kilj}` at `p`, where in the `cRm` convention
`R_{kilj} = cRm (bb k) (bb i) (bb l) (bb j)` (the vector slot is the last one of `cCurv`). -/
noncomputable def cRic (g : SMet I M) (x₀ p : M)
    (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ k, ∑ l, cGramInv g x₀ p k l * cRm g x₀ p (bb k) (bb i) (bb l) (bb j)

/-- The chart scalar curvature `scal = γ^{ij}Ric_{ij}` at `p`. -/
noncomputable def cScal (g : SMet I M) (x₀ p : M) : ℝ :=
  ∑ i, ∑ j, cGramInv g x₀ p i j * cRic g x₀ p i j

/-- The chart squared Ricci norm `|Ric|² = γ^{ia}γ^{jb}Ric_{ij}Ric_{ab}` at `p`. -/
noncomputable def cRicSq (g : SMet I M) (x₀ p : M) : ℝ :=
  ∑ i, ∑ j, ∑ a, ∑ b, cGramInv g x₀ p i a * cGramInv g x₀ p j b *
    cRic g x₀ p i j * cRic g x₀ p a b


end Work.Diff.GE
