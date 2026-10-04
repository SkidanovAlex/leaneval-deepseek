/-
# Layer D, step 3: the Galerkin vector field in coefficient space

The Galerkin ODE of Layer D is

  `c' = ψ(c)`,   `ψ(c)_z = (1/2) · jFamilyCoeff D ρ ε (P (genMap D ε c)) z`,

where `P = deTurckSec hLC g₀` is the DeTurck operator and `genMap D ε c = Σ_z c z • jSym D ε z` is
the coefficient-to-section map of `Work.Diff.STE.D.Galerkin`.  The factor `1/2` is exactly the
symmetrisation factor: for a *symmetric* section `h`,
`Σ_z c_z • jSym D ε z = (1/2)(J ρ ε h + (J ρ ε h)^T) = J ρ ε h` whenever
`c_z = jFamilyCoeff D ρ ε h z` (`J_eq_sum_index` + symmetry of `J ρ ε h`, which follows from
`Rstar_symm`).  Consequently

  `genMap D ε (ψ(c)) = J ρ ε (P (genMap D ε c))`,

i.e. the coefficient ODE is exactly the Galerkin approximation of the DeTurck equation — this is
`Work.Diff.STE.D.genMap_galVF` (delegated).

The vector field is defined only where `genMap D ε c` is a *metric*: symmetric (automatic,
`isSymm_genMap`), positive definite (an open condition on `c`, carried here as the hypothesis
`hpos`), and with smooth chart data (carried as `hsmooth`; for the Galerkin family it holds by
`ChartData_genMap`).
-/
import Mathlib
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.Galerkin
import Submission.Work.Diff.STE.D.isSymm_genMap
import Submission.Work.Diff.STE.D.J_mem_span

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

noncomputable section

/-- **The Galerkin vector field**, in coefficient space: the coefficient vector of the DeTurck
operator applied to `genMap D ε c`, halved (the symmetrisation factor). -/
def galVF [T2Space M] [I.Boundaryless] (hLC : LCSmooth I M) (g₀ : SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hsmooth : ChartData (I := I) (M := M) (genMap (I := I) (M := M) D ε c))
    (hpos : ∀ x v, v ≠ 0 → 0 < genMap (I := I) (M := M) D ε c x v v) :
    Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ :=
  fun z => (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
    (deTurckSec hLC g₀ (genMap (I := I) (M := M) D ε c)
      (isSymm_genMap (I := I) (M := M) D ε c) hpos hsmooth) z

/-- **The section `g + h`** of the metric `g` and the bilinear form `h`. -/
def addSec (g : SMet I M) (h : Work.Diff.STE.Bil (I := I) (M := M)) :
    Work.Diff.STE.Bil (I := I) (M := M) :=
  fun x => g.inner x + h x

@[simp] lemma addSec_apply (g : SMet I M) (h : Work.Diff.STE.Bil (I := I) (M := M)) (x : M)
    (u v : TangentSpace I x) : addSec (I := I) g h x u v = g.inner x u v + h x u v := rfl

/-- **The affine Galerkin vector field**: the unknown metric is `g₀ + genMap D ε c`
(the initial datum `c = 0` corresponds to the metric `g₀`). -/
def galVFaff [T2Space M] [I.Boundaryless] (hLC : LCSmooth I M) (g₀ : SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hsym : IsSymm (I := I) (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)))
    (hsmooth : ChartData (I := I) (M := M)
      (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)))
    (hpos : ∀ x v, v ≠ 0 →
      0 < addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c) x v v) :
    Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ :=
  fun z => (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
    (deTurckSec hLC g₀ (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c))
      hsym hpos hsmooth) z

end

end Work.Diff.STE.D
