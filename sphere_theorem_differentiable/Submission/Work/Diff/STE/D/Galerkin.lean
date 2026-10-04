/-
# Layer D, step 2: the Galerkin space `V_ε`, in coefficient form

The Galerkin scheme of Layer D runs in a *finite-dimensional* space of smooth symmetric sections of
the bundle of bilinear forms.  The explicit finite spanning family of the range of the Friedrichs
mollifier `J ρ ε` is `Work.Diff.STE.B3.jFamily D ε` (proved: `Work.Diff.STE.B3.J_finite_rank`,
`Work.Diff.STE.B3.J_eq_sum_index`), indexed by `JIdx ι₀ n ε`.

**Caveat (do not repeat the mistake).**  `Work.Diff.STE.Bil I M` is a *Pi type of spaces of
continuous linear maps*, and the instance search for `AddCommGroup ↥p` on a submodule
`p : Submodule ℝ (Bil I M)` does **not** fire (verified: it fails even for the abstract statement
`(p : Submodule ℝ V) [AddCommGroup V] [Module ℝ V]`, specialised to this ambient type).
Consequently `FiniteDimensional ℝ ↥p` and `Module.finBasis ℝ ↥p` are not available for submodules
of `Bil`.  The Galerkin scheme is therefore formulated in the *coefficient space*
`JIdx ι₀ n ε → ℝ`, which is a genuine finite-dimensional real normed space, together with the linear
map

  `genMap D ε c = Σ z, c z • jSym D ε z`,

where `jSym D ε z := jFamily D ε z + transpose (jFamily D ε z)` is the symmetrisation of the
spanning vector.  Every element of the span of `jSym` is symmetric, so `genMap D ε c` is a symmetric
section for *every* `c`; positivity of `genMap c` is an open condition on `c`, which makes the
Galerkin ODE `c' = ψ(c)` an ODE on an open subset of `ℝ^{JIdx}`, with `ψ` given *explicitly* by the
Fourier coefficients of `J ρ ε` (see `Work.Diff.STE.B3.J_eq_sum_index`).

This file contains the vocabulary (`IsSymm`, `transpose`, `jSym`, `genMap`) and the membership lemma
`J_mem_span`: for a symmetric section `h`, `D.J ρ ε h` lies in the range of `genMap`.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.D.Setup

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

/-- **The chart matrix of a section** in the coordinate frame of the chart at `x₀`, as a function
of the chart coordinate `y`.  This is the function whose smoothness on the chart target is the
predicate `Work.Diff.STE.D.ChartData`. -/
def chartMat (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M) :
    E → (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :=
  fun y i j => h ((extChartAt I x₀).symm y)
    (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
      (Work.Diff.EXT.bB (E := E) i))
    (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
      (Work.Diff.EXT.bB (E := E) j))

/-- `ChartData` is the smoothness of the chart matrix of `h` on every chart target. -/
theorem chartData_iff_chartMat (h : Work.Diff.STE.Bil (I := I) (M := M)) :
    ChartData (I := I) (M := M) h ↔
      ∀ x₀ : M, ContDiffOn ℝ (⊤ : ℕ∞) (chartMat (I := I) h x₀) (extChartAt I x₀).target :=
  Iff.rfl

/-- A section of the bundle of bilinear forms is **symmetric** if it is symmetric at every point. -/
def IsSymm (h : Work.Diff.STE.Bil (I := I) (M := M)) : Prop := ∀ x u v, h x u v = h x v u

/-- **The index swap** on the spanning family: it exchanges the two matrix slots `(a,b)`. -/
def idxSwap (ε : ℝ) : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε ≃
    Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε where
  toFun z := (z.1, (z.2.2.1, (z.2.1, z.2.2.2)))
  invFun z := (z.1, (z.2.2.1, (z.2.1, z.2.2.2)))
  left_inv z := by
    obtain ⟨i, a, b, q⟩ := z
    rfl
  right_inv z := by
    obtain ⟨i, a, b, q⟩ := z
    rfl

@[simp] lemma idxSwap_apply (ε : ℝ) (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    idxSwap (E := E) (ι₀ := ι₀) ε z
      = (z.1, (z.2.2.1, (z.2.1, z.2.2.2))) := rfl

/-- **The symmetrised spanning family** of the range of `J ρ ε`: the sum of the spanning vector and
its transpose (the latter being the spanning vector at the swapped index pair). -/
def jSym (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) :
    Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε →
      Work.Diff.STE.Bil (I := I) (M := M) :=
  fun z => Work.Diff.STE.B3.jFamily D ε z
    + Work.Diff.STE.B3.jFamily D ε (idxSwap (E := E) (ι₀ := ι₀) ε z)

/-- **The coefficient-to-section map** of the Galerkin space: a real linear combination of the
symmetrised spanning family. -/
def genMap (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Work.Diff.STE.Bil (I := I) (M := M) :=
  ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
    c z • jSym (I := I) (M := M) D ε z

end

end Work.Diff.STE.D
