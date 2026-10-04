/-
# Layer D: the concrete chart expression of the Galerkin vector field `psi`

The Galerkin vector field of Layer D is

  `psi hLC D ρ ε c hg = if (g₀ + genMap D ε c) is positive definite then
      (fun z => (1/2) · jFamilyCoeff D ρ ε (P (g₀ + genMap D ε c)) z) else 0`

where `P` is the DeTurck operator.  The file `Diff/STE/D/contDiffAt_psi_zero.lean` proves that
`psi` is `C¹` at `0`.  This module fixes the *concrete chart expression* by which the smoothness is
proved: on the positivity set the section `P(g₀ + genMap D ε c)` agrees with

  `secChart c x₀ x u v = Σ_{j,k} ⟨u, θ_j(x)⟩ ⟨v, θ_k(x)⟩ · pPhi (jet g₀ y) (jet (g₀ + genMap c) y) j k`,

where `y = extChartAt I x₀ x` is the chart coordinate, `θ_j(x)` are the coordinates of a tangent
vector in the trivialisation of the tangent bundle at `x₀`, and `pPhi` is the *jet-level* DeTurck
operator of `Diff/STE/DeTurckJet.lean` (whose smoothness on the positive definite locus is
`contDiffOn_pPhi`).

The whole point of this file is that the right-hand side is an *explicit* function of the
coefficients `c` (affine in `c`, since `genMap D ε c = Σ_z c_z • jSym z`), so that the smoothness
of `psi` can be reduced to

* the smoothness of `pPhi` on the positive definite locus (`contDiffOn_pPhi`),
* the affinity of the chart jets in the coefficients `c`,
* the differentiability of the Fourier coefficient (an integral over the cube).
-/
import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Galerkin
import Submission.Work.Diff.STE.D.GalODE
import Submission.Work.Diff.STE.deTurck.contDiffOn_pPhi
import Submission.Work.Diff.STE.deTurck.ChartCompBridge
import Submission.Work.Diff.STE.deTurck.chartLieMat_eq_lieJet
import Submission.Work.Diff.EXT.chartRic_mat_smooth_of_jet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

/-! ## 1. The chart matrix, the chart jets and the jet-level DeTurck operator of a section -/

/-- **The chart matrix of a section** `h : Bil I M` in the chart at `x₀`: the same formula as
`Work.Diff.EXT.chartMatFun`, but for a section rather than for a metric.  For `h = g.inner` it is
`chartMatFun g x₀` definitionally, and for `h = (smetOf h …).inner` it is `chartMatFun (smetOf h …) x₀`. -/
noncomputable def chartMatOf (h : Bil (I := I) (M := M)) (x₀ : M) : E → Work.Diff.EXT.MatE (E := E) :=
  fun y i j => h ((extChartAt I x₀).symm y)
    (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
      (Work.Diff.EXT.bB (E := E) i))
    (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
      (Work.Diff.EXT.bB (E := E) j))

@[simp] lemma chartMatOf_apply (h : Bil (I := I) (M := M)) (x₀ : M) (y : E) (i j : Fin (Module.finrank ℝ E)) :
    chartMatOf (I := I) (M := M) h x₀ y i j =
      h ((extChartAt I x₀).symm y)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
          (Work.Diff.EXT.bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
          (Work.Diff.EXT.bB (E := E) j)) := rfl

/-- The chart matrix of a metric is the chart matrix of its inner product. -/
lemma chartMatOf_inner (g : Submission.Diff.SMet I M) :
    chartMatOf (I := I) (M := M) g.inner = Work.Diff.EXT.chartMatFun (I := I) g := rfl

/-- **The spatial `2`-jet of the chart matrix of a section.** -/
noncomputable def chartJetOf (h : Bil (I := I) (M := M)) (x₀ : M) (y : E) :
    Work.Diff.EXT.MatE (E := E) × (E →L[ℝ] Work.Diff.EXT.MatE (E := E)) ×
      (E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E)) :=
  Work.Diff.EXT.jet2 (E := E) (fun p : ℝ × E => chartMatOf (I := I) (M := M) h x₀ p.2) (0, y)

@[simp] lemma chartJetOf_eq (h : Bil (I := I) (M := M)) (x₀ : M) (y : E) :
    chartJetOf (I := I) (M := M) h x₀ y =
      Work.Diff.EXT.jet2 (E := E) (fun p : ℝ × E => chartMatOf (I := I) (M := M) h x₀ p.2) (0, y) := rfl

/-- The spatial `2`-jet of the chart matrix of a metric, in the notation of this file. -/
lemma chartJetOf_inner (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) :
    chartJetOf (I := I) (M := M) g.inner x₀ y = Work.Diff.STE.DeTurck.chartJet (I := I) g x₀ y := rfl

/-- **The jet-level DeTurck operator of a section**, with background `g₀`:
`pPhi` evaluated at the `2`-jets of the chart matrices of the background `g₀` and of `h`. -/
noncomputable def pPhiJetOf (g₀ : Submission.Diff.SMet I M)
    (h : Bil (I := I) (M := M)) (x₀ : M) (y : E) :
    Work.Diff.EXT.MatE (E := E) :=
  fun i j =>
    Work.Diff.STE.DeTurck.pPhi (chartJetOf (I := I) (M := M) g₀.inner x₀ y).1
      (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.1
      (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.2
      (chartJetOf (I := I) (M := M) h x₀ y).1
      (chartJetOf (I := I) (M := M) h x₀ y).2.1
      (chartJetOf (I := I) (M := M) h x₀ y).2.2 i j

@[simp] lemma pPhiJetOf_apply (g₀ : Submission.Diff.SMet I M)
    (h : Bil (I := I) (M := M)) (x₀ : M) (y : E) (i j : Fin (Module.finrank ℝ E)) :
    pPhiJetOf (I := I) (M := M) g₀ h x₀ y i j =
      Work.Diff.STE.DeTurck.pPhi (chartJetOf (I := I) (M := M) g₀.inner x₀ y).1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.1
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.2
        (chartJetOf (I := I) (M := M) h x₀ y).1
        (chartJetOf (I := I) (M := M) h x₀ y).2.1
        (chartJetOf (I := I) (M := M) h x₀ y).2.2 i j := rfl

/-- The jet-level DeTurck operator of a metric is the `DeTurck.pPhiJet` of `LieMet.lean`. -/
lemma pPhiJetOf_inner (g g₀ : Submission.Diff.SMet I M) (x₀ : M) (y : E) :
    pPhiJetOf (I := I) (M := M) g₀ g.inner x₀ y =
      Work.Diff.STE.DeTurck.pPhiJet (I := I) g g₀ x₀ y := rfl

/-! ## 2. The coordinates of a tangent vector in the trivialisation at a point -/

/-- **The coordinates of a tangent vector in the trivialisation of the tangent bundle at `x₀`.** -/
noncomputable def chartCoordOf (x₀ : M) (p : M) (u : TangentSpace I p) : E :=
  (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p u

/-- The `j`-th coordinate functional of the trivialisation at `x₀`, as a continuous linear
functional on the tangent space at `p`. -/
noncomputable def coordCLM (x₀ : M) (p : M) (j : Fin (Module.finrank ℝ E)) : TangentSpace I p →L[ℝ] ℝ :=
  ((Work.Diff.EXT.bB (E := E)).coord j).toContinuousLinearMap.comp
    ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p)

@[simp] lemma coordCLM_apply (x₀ : M) (p : M) (j : Fin (Module.finrank ℝ E))
    (u : TangentSpace I p) :
    coordCLM (I := I) (M := M) x₀ p j u =
      (Work.Diff.EXT.bB (E := E)).coord j (chartCoordOf (I := I) (M := M) x₀ p u) := rfl

/-! ## 3. The chart expression of the DeTurck operator on a section -/

/-- **The chart expression of the DeTurck operator of a section** at the point `x` of the chart at
`x₀`, evaluated on the tangent vectors `u v` (whose coordinates in the trivialisation at `x₀` are
used).  This is the explicit expression whose smoothness in a coefficient family is proved in the
sibling modules; it is the chart matrix of `P(smetOf h)` in the frame of the trivialisation. -/
noncomputable def secChartVal (g₀ : Submission.Diff.SMet I M)
    (h : Bil (I := I) (M := M)) (x₀ : M) (x : M)
    (u v : TangentSpace I x) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    pPhiJetOf (I := I) (M := M) g₀ h x₀ (extChartAt I x₀ x) j k
      * (coordCLM (I := I) (M := M) x₀ x j u * coordCLM (I := I) (M := M) x₀ x k v)

/-- **The chart expression of the DeTurck operator as a section**: the pointwise value assignment
of `secChartVal`, packaged as a continuous bilinear form at each point (it is a finite sum of
products of continuous linear functionals). -/
noncomputable def secChart (g₀ : Submission.Diff.SMet I M)
    (h : Bil (I := I) (M := M)) (x₀ : M) : Bil (I := I) (M := M) :=
  fun x => ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    (pPhiJetOf (I := I) (M := M) g₀ h x₀ (extChartAt I x₀ x) j k) •
      (coordCLM (I := I) (M := M) x₀ x j).smulRight (coordCLM (I := I) (M := M) x₀ x k)

@[simp] lemma secChart_apply (g₀ : Submission.Diff.SMet I M)
    (h : Bil (I := I) (M := M)) (x₀ : M) (x : M)
    (u v : TangentSpace I x) :
    secChart (I := I) (M := M) g₀ h x₀ x u v = secChartVal (I := I) (M := M) g₀ h x₀ x u v := by
  simp only [secChart, secChartVal, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    coordCLM_apply]

/-! ## 4. The concrete total function whose `C¹`-smoothness at `0` gives `psi` -/

/-- **The concrete Galerkin vector field** attached to the data: for every coefficient family `c`,

  `psiConc c z = (1/2) · jFamilyCoeff D ρ ε (secChart (g₀ + genMap D ε c) (x₀ z.1)) z`.

This is a *total* function of `c` (no proof arguments, no `if`), it agrees with `psi` on the
positivity set (by the chart expression of the DeTurck operator), and it is manifestly built from
the affine map `c ↦ g₀ + genMap D ε c` and the smooth jet-level operator `pPhi`. -/
noncomputable def psiConc (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ :=
  fun z => (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
    (secChart (I := I) (M := M) g₀
      (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) (D.x₀ z.1)) z

lemma psiConc_apply (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    psiConc (I := I) (M := M) g₀ D ρ ε c z =
      (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
        (secChart (I := I) (M := M) g₀
          (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) (D.x₀ z.1)) z := rfl

end

end Work.Diff.STE.D
