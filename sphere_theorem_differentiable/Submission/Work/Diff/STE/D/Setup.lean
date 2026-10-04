/-
# Layer D, step 1: the DeTurck operator on sections, and the metric attached to a positive
definite smooth bilinear form

The Galerkin scheme of Layer D runs in the finite-dimensional space
`V_ε = LinearMap.range (J ρ ε)`.  Its elements are explicit smooth sections of the bundle of
bilinear forms on `M`, so each positive definite element `h` of `V_ε` is the metric tensor of a
*unique* global smooth metric.  This file makes that passage a definition (not a choice):

* `Work.Diff.STE.D.smetOf h hsym hpos hsmooth : SMet I M` — the global smooth metric with
  `inner = h`, assembled from the proved pieces of `Work.Diff.STE.Man.exists_sMet_of_chartData`
  (`isVonNBounded_of_posDef` and `section_contMDiffAt_of_frameMat`);
* `Work.Diff.STE.D.deTurckSec g₀ h ... : Bil I M` — the DeTurck operator
  `P(h) = -2 Ric(h) + L_{W(h)} h` (with background metric `g₀`) as a section of the bundle of
  bilinear forms, i.e. the right-hand side of the DeTurck equation `∂ₜ ℊ = P(ℊ)`.

Both definitions only depend on `h` through the *data* of the metric tensor (the proof arguments
are propositional), so the passages `h ↦ smetOf h …` and `h ↦ deTurckSec g₀ h …` are functions of
`h` alone; `smetOf_inner` and `deTurckSec_eq` record the defining equations.
-/
import Mathlib
import Submission.Work.Diff.STE.Man.Sect
import Submission.Work.Diff.STE.Man.exists_sMet_of_chartData
import Submission.Work.Diff.STE.LieMet
import Submission.Work.Diff.STE.D.deTurckCLM

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

noncomputable section

/-- **The chart matrix of a section, written as in `Work.Diff.STE.Man.exists_sMet_of_chartData`**:
this is the smoothness hypothesis which lets a positive definite section be packaged into a global
smooth metric. -/
def ChartData (h : Work.Diff.STE.Bil (I := I) (M := M)) : Prop :=
  ∀ x₀ : M, ContDiffOn ℝ (⊤ : ℕ∞)
    (fun y : E => fun i j : Fin (Module.finrank ℝ E) =>
      h ((extChartAt I x₀).symm y)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
          (Work.Diff.EXT.bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
          (Work.Diff.EXT.bB (E := E) j)))
    (extChartAt I x₀).target

section Build

variable [I.Boundaryless] [T2Space M]

/-- **The global smooth metric attached to a positive definite section with smooth chart data.**
This is the construction of `Work.Diff.STE.Man.exists_sMet_of_chartData` turned into a definition:
the `inner` field is `h` itself, positivity gives `isVonNBounded`, and the smoothness of the chart
data gives `contMDiff`. -/
def smetOf (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ x u v, h x u v = h x v u)
    (hpos : ∀ x v, v ≠ 0 → 0 < h x v v)
    (hsmooth : ChartData (I := I) (M := M) h) : SMet I M :=
  { inner := h
    symm := hsym
    pos := hpos
    isVonNBounded := fun x =>
      Work.Diff.STE.Man.isVonNBounded_of_posDef (I := I) h hpos x
    contMDiff := fun x₀ => by
      -- smoothness of the frame matrix at the chart centre `x₀` ...
      have hframe : ContMDiffAt I (𝓘(ℝ, Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
          (fun x : M => Work.Diff.EXT.frameMat (I := I) x₀ x (h x)) x₀ := by
        have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
            (fun y : E => Work.Diff.EXT.frameMat (I := I) x₀ ((extChartAt I x₀).symm y)
              (h ((extChartAt I x₀).symm y))) ((extChartAt I x₀) x₀) :=
          (hsmooth x₀).contDiffAt (extChartAt_target_mem_nhds x₀)
        have h2 : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
            (fun y : E => Work.Diff.EXT.frameMat (I := I) x₀ ((extChartAt I x₀).symm y)
              (h ((extChartAt I x₀).symm y))) ((extChartAt I x₀) x₀) := h1.contMDiffAt
        have h3 := h2.comp x₀ (contMDiffAt_extChartAt (I := I) (x := x₀))
        refine h3.congr_of_eventuallyEq ?_
        filter_upwards [IsOpen.mem_nhds (chartAt H x₀).open_source (mem_chart_source H x₀)]
          with x hx
        have hx' : x ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
        simp only [Function.comp_apply]
        rw [show (extChartAt I x₀).symm ((extChartAt I x₀) x) = x
          from (extChartAt I x₀).left_inv hx']
      -- ... hence smoothness of the section of the bundle of bilinear forms.
      exact Work.Diff.STE.Man.section_contMDiffAt_of_frameMat (I := I) (x₀ := x₀)
        (γ := h) hframe }

@[simp] lemma smetOf_inner (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ x u v, h x u v = h x v u)
    (hpos : ∀ x v, v ≠ 0 → 0 < h x v v)
    (hsmooth : ChartData (I := I) (M := M) h) (x : M) (u v : TangentSpace I x) :
    (smetOf h hsym hpos hsmooth).inner x u v = h x u v := rfl

/-- **The DeTurck operator along a positive definite smooth section, as a plain function on
vectors**: `x ↦ (u v ↦ P(h)(x)(u,v))`.  This is the value assignment of the right-hand side of the
DeTurck equation `∂ₜℊ = P(ℊ)`; the packaging of each value into a continuous bilinear form (so that
`P(h)` is an element of `Bil I M`, and the Galerkin mollifier `J` can be applied to it) is
`Work.Diff.STE.D.deTurckCLM`, which is delegated. -/
def deTurckFun (g₀ : SMet I M) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ x u v, h x u v = h x v u)
    (hpos : ∀ x v, v ≠ 0 → 0 < h x v v)
    (hsmooth : ChartData (I := I) (M := M) h) :
    (x : M) → TangentSpace I x → TangentSpace I x → ℝ :=
  fun x => Work.Diff.STE.DeTurck.deTurckOp (smetOf h hsym hpos hsmooth) g₀ x

@[simp] lemma deTurckFun_apply (g₀ : SMet I M) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ x u v, h x u v = h x v u)
    (hpos : ∀ x v, v ≠ 0 → 0 < h x v v)
    (hsmooth : ChartData (I := I) (M := M) h) (x : M) (u v : TangentSpace I x) :
    deTurckFun g₀ h hsym hpos hsmooth x u v
      = Work.Diff.STE.DeTurck.deTurckOp (smetOf h hsym hpos hsmooth) g₀ x u v := rfl

/-- **The DeTurck operator on sections** `P(h) = -2 Ric(h) + L_{W(h)} h`, as a section of the
bundle of bilinear forms (i.e. an element of `Bil I M`): each pointwise value is packaged into a
continuous bilinear form by `Work.Diff.STE.D.deTurckCLM`.  This is the right-hand side of the
DeTurck equation `∂ₜ ℊ = P(ℊ)`, and the input of the Galerkin mollifier `J ρ ε`. -/
def deTurckSec (hLC : LCSmooth I M) (g₀ : SMet I M) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ x u v, h x u v = h x v u)
    (hpos : ∀ x v, v ≠ 0 → 0 < h x v v)
    (hsmooth : ChartData (I := I) (M := M) h) : Work.Diff.STE.Bil (I := I) (M := M) :=
  fun x => Classical.choose (deTurckCLM hLC (smetOf h hsym hpos hsmooth) g₀ x)

lemma deTurckSec_apply (hLC : LCSmooth I M) (g₀ : SMet I M)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ x u v, h x u v = h x v u)
    (hpos : ∀ x v, v ≠ 0 → 0 < h x v v)
    (hsmooth : ChartData (I := I) (M := M) h) (x : M) (u v : TangentSpace I x) :
    deTurckSec hLC g₀ h hsym hpos hsmooth x u v
      = Work.Diff.STE.DeTurck.deTurckOp (smetOf h hsym hpos hsmooth) g₀ x u v :=
  Classical.choose_spec (deTurckCLM hLC (smetOf h hsym hpos hsmooth) g₀ x) u v

end Build

end

end Work.Diff.STE.D
