import Mathlib
import Submission.Diff.Grad
import Submission.Geodesic
import Submission.CurvatureVec
import Submission.ChartBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Chart data for the geometric norms along a Ricci flow (REG)

Definitions only.  Fix a chart centre `x₀ : M` and the canonical basis `bb` of the model space `E`.
The *coordinate frame* is `cFrame x₀ i y = frameVector I x₀ y (bb i)`; it is a basis of the tangent
space at every point of the chart.  For a time-dependent family of smooth metrics `G`, all the
quantities entering `rmNormSq`, `scalAt` and `dRmNormSq` are expressed below in this frame:
the metric components `mComp`, the derivative operator `dOp` in a coordinate direction, the Gram
matrix `GramM` and its inverse, the Christoffel pairings `fPair`, the curvature components `rmC4`
and the `∇Rm` components `covRmC5`, and finally the frame-independent contractions
`N4`, `N2`, `N5` (which are the sums of squares / traces in an orthonormal frame).
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic

namespace Work.Diff.GE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section

/-- The canonical basis of `E`. -/
abbrev cBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E

/-- The coordinate frame of the chart at `x₀`. -/
def cFrame (x₀ : M) (i : Fin (Module.finrank ℝ E)) : Π y : M, TangentSpace I y :=
  frameSection (I := I) x₀ (cBasis (E := E) i)

lemma cFrame_apply (x₀ : M) (i : Fin (Module.finrank ℝ E)) (y : M) :
    cFrame (I := I) x₀ i y = frameVector (I := I) x₀ y (cBasis (E := E) i) := rfl

/-- Metric components in the coordinate frame. -/
def mComp (G : ℝ → SMet I M) (x₀ : M) (i j : Fin (Module.finrank ℝ E)) (t : ℝ) (y : M) : ℝ :=
  (G t).inner y (cFrame (I := I) x₀ i y) (cFrame (I := I) x₀ j y)

/-- The derivative of a scalar function of `(t, y)` in the coordinate direction `k`. -/
def dOp (x₀ : M) (k : Fin (Module.finrank ℝ E)) (u : ℝ → M → ℝ) : ℝ → M → ℝ :=
  fun t y => mvfderiv I (u t) y (cFrame (I := I) x₀ k y)

/-- The Gram matrix of the coordinate frame for the metric `G t`. -/
def GramM (G : ℝ → SMet I M) (x₀ : M) (t : ℝ) (y : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun i j => mComp (I := I) G x₀ i j t y

/-- The inverse Gram matrix of the coordinate frame. -/
def GramInv (G : ℝ → SMet I M) (x₀ : M) (t : ℝ) (y : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (GramM (I := I) G x₀ t y)⁻¹

/-- Christoffel pairings `⟨∇_{σ_a} σ_b, σ_c⟩` in the coordinate frame. -/
def fPair (G : ℝ → SMet I M) (x₀ : M) (a b c : Fin (Module.finrank ℝ E)) (t : ℝ) (y : M) : ℝ :=
  (G t).inner y ((lcOf (G t)) (cFrame (I := I) x₀ b) y (cFrame (I := I) x₀ a y))
    (cFrame (I := I) x₀ c y)

/-- The curvature components `Rm(σᵢ,σⱼ,σₖ,σₗ)` in the coordinate frame. -/
def rmC4 (G : ℝ → SMet I M) (x₀ : M) (t : ℝ) (y : M) : Curv4 (Module.finrank ℝ E) :=
  fun i j k l => rmP (G t) y (cFrame (I := I) x₀ i y) (cFrame (I := I) x₀ j y)
    (cFrame (I := I) x₀ k y) (cFrame (I := I) x₀ l y)

/-- The `∇Rm` components in the coordinate frame, first index the derivative slot. -/
def covRmC5 (G : ℝ → SMet I M) (x₀ : M) (t : ℝ) (y : M) :
    Fin (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E) :=
  fun m i j k l => covRm (G t) y (cFrame (I := I) x₀ m y) (cFrame (I := I) x₀ i y)
    (cFrame (I := I) x₀ j y) (cFrame (I := I) x₀ k y) (cFrame (I := I) x₀ l y)

/-- The Koszul expression for the Christoffel pairing `⟨∇_{σ_a}σ_b, σ_c⟩` in the coordinate frame:
`½(∂_a G_{bc} + ∂_b G_{ac} - ∂_c G_{ab})`.  By `Work.Diff.GE.fPair_eq` this is `fPair` on the
chart. -/
def koszulPair (G : ℝ → SMet I M) (x₀ : M) (a b c : Fin (Module.finrank ℝ E)) : ℝ → M → ℝ :=
  fun t y => (1 / 2) * (mvfderiv I (fun y' : M ↦ (G t).inner y'
          (cFrame (I := I) x₀ b y') (cFrame (I := I) x₀ c y')) y (cFrame (I := I) x₀ a y)
      + mvfderiv I (fun y' : M ↦ (G t).inner y'
          (cFrame (I := I) x₀ c y') (cFrame (I := I) x₀ a y')) y (cFrame (I := I) x₀ b y)
      - mvfderiv I (fun y' : M ↦ (G t).inner y'
          (cFrame (I := I) x₀ a y') (cFrame (I := I) x₀ b y')) y (cFrame (I := I) x₀ c y))

/-- The explicit coordinate expression for the curvature components `Rm(σᵢ,σⱼ,σₖ,σₗ)` of `G t`:
`∂_i Γ_{jlk} - Γ_{jlm}Γ_{ikn}Γinv^{mn} - ∂_j Γ_{ilk} + Γ_{ilm}Γ_{jkn}Γinv^{mn}`, where `Γ` is the
Koszul pairing `koszulPair`.  `Work.Diff.GE.rmChartExpr_eq` identifies it with `rmC4`. -/
def rmChartExpr (G : ℝ → SMet I M) (x₀ : M) (i j k l : Fin (Module.finrank ℝ E)) : ℝ → M → ℝ :=
  fun t y =>
    dOp (I := I) x₀ i (koszulPair (I := I) G x₀ j l k) t y
      - ∑ m, ∑ n, GramInv (I := I) G x₀ t y m n *
          koszulPair (I := I) G x₀ j l m t y * koszulPair (I := I) G x₀ i k n t y
      - dOp (I := I) x₀ j (koszulPair (I := I) G x₀ i l k) t y
      + ∑ m, ∑ n, GramInv (I := I) G x₀ t y m n *
          koszulPair (I := I) G x₀ i l m t y * koszulPair (I := I) G x₀ j k n t y

/-- The Christoffel symbols in the coordinate frame: `∇_{σ_a}σ_b = ∑_n Γ^n_{ab} σ_n` with
`Γ^n_{ab} = ∑_p (G⁻¹)_{np} ⟨∇_{σ_a}σ_b, σ_p⟩`. -/
def chrCoord (G : ℝ → SMet I M) (x₀ : M) (n a b : Fin (Module.finrank ℝ E)) : ℝ → M → ℝ :=
  fun t y => ∑ p, GramInv (I := I) G x₀ t y n p * koszulPair (I := I) G x₀ a b p t y

/-- The explicit coordinate expression for the `∇Rm` components `(∇_{σ_m}Rm)(σᵢ,σⱼ,σₖ,σₗ)`: the
derivative of `rmChartExpr` in the direction `m`, corrected by the four Christoffel contractions.
`Work.Diff.GE.covRmChartExpr_eq` identifies it with `covRmC5`. -/
def covRmChartExpr (G : ℝ → SMet I M) (x₀ : M) (m i j k l : Fin (Module.finrank ℝ E)) :
    ℝ → M → ℝ :=
  fun t y =>
    dOp (I := I) x₀ m (rmChartExpr (I := I) G x₀ i j k l) t y
      - ∑ n, chrCoord (I := I) G x₀ n m i t y * rmChartExpr (I := I) G x₀ n j k l t y
      - ∑ n, chrCoord (I := I) G x₀ n m j t y * rmChartExpr (I := I) G x₀ i n k l t y
      - ∑ n, chrCoord (I := I) G x₀ n m k t y * rmChartExpr (I := I) G x₀ i j n l t y
      - ∑ n, chrCoord (I := I) G x₀ n m l t y * rmChartExpr (I := I) G x₀ i j k n t y

/-! ## Frame-independent contractions

For a positive definite matrix `Γ` (the Gram matrix of a basis) and a tensor `R`, `N4`, `N2` and
`N5` are the full contractions with `Γ⁻¹`; for `Γ = 1` (an orthonormal basis) they reduce to the
sums of squares / the trace used in `frobSq`, `scalAlg` and `dRmNormSq`. -/

/-- `|R|²` in a general basis. -/
def N4 {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ b, ∑ c, ∑ d,
    Γ⁻¹ i a * Γ⁻¹ j b * Γ⁻¹ k c * Γ⁻¹ l d * R i j k l * R a b c d

/-- The scalar curvature in a general basis. -/
def N2 {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) : ℝ :=
  ∑ i, ∑ a, ∑ j, ∑ b, Γ⁻¹ i a * Γ⁻¹ j b * R i j a b

/-- `|S|²` for a `(0,5)`-tensor array. -/
def frobSq5 {n : ℕ} (S : Fin n → Curv4 n) : ℝ :=
  ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, S m i j k l ^ 2

/-- Change of frame for a `(0,5)`-tensor array: `S'_{mijkl} = ∑ A_mA_iA_jA_kA_l S`. -/
def rot5 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Fin n → Curv4 n) :
    Fin n → Curv4 n :=
  fun m i j k l => ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    A m a * A i b * A j c * A k d * A l e * S a b c d e

/-- `|∇Rm|²` in a general basis. -/
def N5 {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (S : Fin n → Curv4 n) : ℝ :=
  ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    Γ⁻¹ m a * Γ⁻¹ i b * Γ⁻¹ j c * Γ⁻¹ k d * Γ⁻¹ l e *
      S m i j k l * S a b c d e

end

end Work.Diff.GE
