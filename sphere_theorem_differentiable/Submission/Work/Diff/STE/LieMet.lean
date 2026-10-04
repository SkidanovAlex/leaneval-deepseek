/-
# The DeTurck operator `P(g) = -2 Ric(g) + L_{W(g)} g` as a geometric object

This file fixes the *geometric* vocabulary of C1 (the DeTurck layer of the short-time existence
proof), matching the jet-level vocabulary of `Submission/Work/Diff/STE/DeTurckJet.lean` and the
frame-free DeTurck field of `Submission/Work/Diff/STE/DeTurckField.lean`.

* `lieMet g W x u v = g(∇_u W, v) + g(u, ∇_v W)`: the Lie derivative of the metric `g` along the
  global field `W`, realised through the Levi-Civita connection.  For the torsion-free,
  metric-compatible `∇ = ∇^g` this is the classical Lie derivative `L_W g`.
* `deTurckOp g gbar x u v = -2 Ric(g)(u,v) + (L_{W(g)}g)(u,v)`: the DeTurck operator, whose
  short-time parabolicity is the content of the jet-level cancellation
  `Work.Diff.STE.DeTurck.pPhi_decomp` (`pPhi = secOp + pN`).
* `chartLieMat`/`chartDeTurckMat`: their matrices in the coordinate frame of a chart (the same
  frame in which `Submission.Work.Diff.EXT.chartRicMat` is written), and
  `chartDeTurckMat = -2 • chartRicMat + chartLieMat` by definition.
* `chartJet g x₀ y`: the spatial `2`-jet of `chartMatFun g x₀` at the chart coordinate `y`
  (value, `∂_a g_{ij}`, `∂_a∂_b g_{ij}`), and `lieJet`/`pPhiJet`: the jet-level expressions
  `jLW`/`pPhi` of `DeTurckJet.lean` evaluated on those jets.

The remaining obligation (delegated) is the **bridge**

`chartLieMat g gbar x₀ y = lieJet g gbar x₀ y`   (`y ∈ (extChartAt I x₀).target`),

i.e. that the chart matrix of the Lie derivative is the jet formula `jLW` (for which the dictionary
`GramInv ↔ jInv`, `chrCoord ↔ jGamU`, `deTurckVec ↔ jWU` — the latter is the proved
`deTurckVec_chartComp` — is needed).  Together with the EXT identity
`chartRicMat g x₀ y = ricPhi (jets)` this identifies the chart matrix of `deTurckOp` with `pPhiJet`,
which is what makes a solution of the flat PDE `∂ₜu = pPhiJet(jet u)` a solution of the geometric
DeTurck equation `∂ₜĝ = deTurckOp ĝ g₀` in the chart.
-/
import Mathlib
import Submission.Work.Diff.STE.DeTurckField
import Submission.Work.Diff.STE.DeTurckJet
import Submission.Work.Diff.EXT.splice_defs
import Submission.ChartConnection
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.GE.norms_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.DeTurck

open Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section

/-! ## The Lie derivative of the metric along a field -/

/-- **The Lie derivative of the metric `g` along a global tangent field `W`**, realised through the
Levi-Civita connection: `(L_W g)(u,v) = g(∇_u W, v) + g(u, ∇_v W)`.  For the torsion-free
metric-compatible `∇ = ∇^g` this is the classical Lie derivative, and it is the second term of the
DeTurck modification `P(g) = -2 Ric(g) + L_{W(g)} g` of the Ricci flow. -/
noncomputable def lieMet (g : SMet I M) (W : Π x : M, TangentSpace I x)
    (x : M) (u v : TangentSpace I x) : ℝ :=
  g.inner x ((lcOf g) W x u) v + g.inner x u ((lcOf g) W x v)

/-- **The DeTurck operator** `P(g) = -2 Ric(g) + L_{W(g)} g` with the background metric `gbar`
determining the DeTurck field `W(g) = tr_g(∇^g - ∇^gbar)`, as a bilinear form at each point. -/
noncomputable def deTurckOp (g gbar : SMet I M) (x : M) (u v : TangentSpace I x) : ℝ :=
  -2 * ricAt (lcOf g) x u v + lieMet g (deTurckVec g gbar) x u v

lemma lieMet_comm (g : SMet I M) (W : Π x : M, TangentSpace I x) (x : M)
    (u v : TangentSpace I x) : lieMet g W x u v = lieMet g W x v u := by
  simp only [lieMet]
  rw [g.symm x u ((lcOf g) W x v), g.symm x ((lcOf g) W x u) v]
  ring

@[simp] lemma deTurckOp_apply (g gbar : SMet I M) (x : M) (u v : TangentSpace I x) :
    deTurckOp g gbar x u v
      = -2 * ricAt (lcOf g) x u v + lieMet g (deTurckVec g gbar) x u v := rfl

/-! ## The chart matrices -/

/-- The chart matrix of the Lie derivative `L_{W(g)} g` in the coordinate frame of the chart
at `x₀` (the frame of `Work.Diff.GE.cFrame`, in which `Work.Diff.EXT.chartRicMat` is written). -/
noncomputable def chartLieMat (g gbar : SMet I M) (x₀ : M) : E → MatE (E := E) :=
  fun y i j => lieMet g (deTurckVec g gbar) ((extChartAt I x₀).symm y)
    (Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y))
    (Work.Diff.GE.cFrame (I := I) x₀ j ((extChartAt I x₀).symm y))

/-- The chart matrix of the DeTurck operator `P(g) = -2 Ric(g) + L_{W(g)}g` in the coordinate frame
of the chart at `x₀`. -/
noncomputable def chartDeTurckMat (g gbar : SMet I M) (x₀ : M) : E → MatE (E := E) :=
  fun y i j => deTurckOp g gbar ((extChartAt I x₀).symm y)
    (Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y))
    (Work.Diff.GE.cFrame (I := I) x₀ j ((extChartAt I x₀).symm y))

@[simp] lemma chartLieMat_apply (g gbar : SMet I M) (x₀ : M) (y : E) (i j : Idx E) :
    chartLieMat g gbar x₀ y i j
      = lieMet g (deTurckVec g gbar) ((extChartAt I x₀).symm y)
          (Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y))
          (Work.Diff.GE.cFrame (I := I) x₀ j ((extChartAt I x₀).symm y)) := rfl

@[simp] lemma chartDeTurckMat_apply (g gbar : SMet I M) (x₀ : M) (y : E) (i j : Idx E) :
    chartDeTurckMat g gbar x₀ y i j
      = deTurckOp g gbar ((extChartAt I x₀).symm y)
          (Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y))
          (Work.Diff.GE.cFrame (I := I) x₀ j ((extChartAt I x₀).symm y)) := rfl

/-- The DeTurck matrix is `-2` times the Ricci matrix plus the Lie-derivative matrix: this is the
definitional decomposition of `P(g) = -2 Ric(g) + L_{W(g)}g`. -/
lemma chartDeTurckMat_eq (g gbar : SMet I M) (x₀ : M) (y : E) (i j : Idx E) :
    chartDeTurckMat g gbar x₀ y i j
      = -2 * Work.Diff.EXT.chartRicMat g x₀ y i j + chartLieMat g gbar x₀ y i j := rfl

/-! ## The jet-level expressions -/

/-- The spatial `2`-jet of the chart matrix `chartMatFun g x₀` at the chart coordinate `y`:
`(A, L, B)` with `A i j = g_{ij}(y)`, `L (bB a) i j = ∂_a g_{ij}(y)` and
`B (bB a) (bB b) i j = ∂_a∂_b g_{ij}(y)`. -/
noncomputable def chartJet (g : SMet I M) (x₀ : M) (y : E) : MatE (E := E) × LinMat E × BilMat E :=
  jet2 (E := E) (fun p : ℝ × E => chartMatFun g x₀ p.2) (0, y)

/-- The jet-level Lie derivative: `jLW` of `DeTurckJet.lean` evaluated on the `2`-jets of the chart
matrices of `g` (the metric) and `gbar` (the background). -/
noncomputable def lieJet (g gbar : SMet I M) (x₀ : M) (y : E) : MatE (E := E) :=
  fun i j => jLW (chartJet g x₀ y).1 (chartJet g x₀ y).2.1 (chartJet g x₀ y).2.2
    (chartJet gbar x₀ y).1 (chartJet gbar x₀ y).2.1 (chartJet gbar x₀ y).2.2 i j

/-- The jet-level DeTurck operator: `pPhi` of `DeTurckJet.lean` evaluated on the `2`-jets of the
chart matrices of `g` and of the background `gbar`. -/
noncomputable def pPhiJet (g gbar : SMet I M) (x₀ : M) (y : E) : MatE (E := E) :=
  fun i j => pPhi (chartJet gbar x₀ y).1 (chartJet gbar x₀ y).2.1 (chartJet gbar x₀ y).2.2
    (chartJet g x₀ y).1 (chartJet g x₀ y).2.1 (chartJet g x₀ y).2.2 i j

@[simp] lemma lieJet_apply (g gbar : SMet I M) (x₀ : M) (y : E) (i j : Idx E) :
    lieJet g gbar x₀ y i j
      = jLW (chartJet g x₀ y).1 (chartJet g x₀ y).2.1 (chartJet g x₀ y).2.2
          (chartJet gbar x₀ y).1 (chartJet gbar x₀ y).2.1 (chartJet gbar x₀ y).2.2 i j := rfl

@[simp] lemma pPhiJet_apply (g gbar : SMet I M) (x₀ : M) (y : E) (i j : Idx E) :
    pPhiJet g gbar x₀ y i j
      = pPhi (chartJet gbar x₀ y).1 (chartJet gbar x₀ y).2.1 (chartJet gbar x₀ y).2.2
          (chartJet g x₀ y).1 (chartJet g x₀ y).2.1 (chartJet g x₀ y).2.2 i j := rfl

end

end Work.Diff.STE.DeTurck
