/-
# Layer D: `psi` agrees with its concrete chart expression on the positivity set

The Galerkin vector field `Work.Diff.STE.D.psi` is `galVFaff` on the positivity set and `0`
elsewhere; the concrete function `Work.Diff.STE.D.psiConc` replaces the DeTurck section by its
chart expression.  The two agree on the positivity set, because on the (topological) support of the
localised weight `ψ i` the chart at `x₀ i` is genuine, so the chart expression of the DeTurck
operator computes its value (`Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp`).

Together with the fact that the positivity set is a neighbourhood of `0`
(`Work.Diff.STE.D.eventually_posDef`) this gives `psi =ᶠ[𝓝 0] psiConc`, which reduces the
smoothness of `psi` at `0` to the smoothness of the explicit function `psiConc`.
-/
import Mathlib
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.STE.D.psi.Positivity
import Submission.Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp

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

/-- **On the positivity set, `psi` is the concrete chart expression.** -/
theorem psi_eq_psiConc (hLC : Submission.Diff.LCSmooth I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (hg : ChartData (I := I) (M := M) (g₀.inner))
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hc : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c) x v v) :
    psi (I := I) hLC D ρ ε c hg = psiConc (I := I) (M := M) g₀ D ρ ε c := by
  -- the two sections agree at all the points of the localised components
  have hbridge : ∀ (i : ι₀) (z' : Fin (Module.finrank ℝ E) → ℝ)
      (a b : Fin (Module.finrank ℝ E)), D.psi i z' ≠ 0 →
      D.mat i (deTurckSec hLC g₀ (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c))
          (isSymm_addSec_genMap D ε c) hc (chartData_addSec_genMap D ε c hg)) a b z'
        = D.mat i (secChart (I := I) (M := M) g₀
          (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) (D.x₀ i)) a b z' := by
    intro i z' a b hz
    have hζ : D.ζ i (D.pt i z') ≠ 0 :=
      fun h0 => hz (by simp only [Work.Diff.STE.B3Data.psi, h0, mul_zero])
    have hsrc' : D.pt i z' ∈ (extChartAt I (D.x₀ i)).source := (D.hζsupp i _ hζ).1
    have hsrc : D.pt i z' ∈ (chartAt H (D.x₀ i)).source := by
      rwa [extChartAt_source] at hsrc'
    rw [Work.Diff.STE.B3Data.mat, Work.Diff.STE.B3Data.mat, secChart_apply]
    rw [deTurckSec_apply hLC g₀ (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c))
      (isSymm_addSec_genMap D ε c) hc (chartData_addSec_genMap D ε c hg) (D.pt i z')
      (D.e i a (D.pt i z')) (D.e i b (D.pt i z'))]
    exact (Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp (I := I) (M := M) hLC
      (smetOf (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c))
        (isSymm_addSec_genMap D ε c) hc (chartData_addSec_genMap D ε c hg))
      g₀ (D.x₀ i) (x := D.pt i z') hsrc
      (D.e i a (D.pt i z')) (D.e i b (D.pt i z'))).symm
  have hRQ : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      D.R i (deTurckSec hLC g₀ (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c))
          (isSymm_addSec_genMap D ε c) hc (chartData_addSec_genMap D ε c hg)) a b
        = D.R i (secChart (I := I) (M := M) g₀
          (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) (D.x₀ i)) a b := by
    intro i a b
    funext z'
    by_cases hz : D.psi i z' = 0
    · simp only [Work.Diff.STE.B3Data.R, hz, zero_mul]
    · simp only [Work.Diff.STE.B3Data.R]
      rw [hbridge i z' a b hz]
  -- conclude
  funext z
  rw [Work.Diff.STE.D.psi, dif_pos hc]
  show (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
      (deTurckSec hLC g₀ (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c))
        (isSymm_addSec_genMap D ε c) hc (chartData_addSec_genMap D ε c hg)) z
    = (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
      (secChart (I := I) (M := M) g₀
        (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) (D.x₀ z.1)) z
  congr 1
  simp only [Work.Diff.STE.B3.jFamilyCoeff]
  rw [hRQ z.1 z.2.1 z.2.2.1]

/-- **`psi` agrees with its concrete chart expression near `0`.** -/
theorem psi_eventuallyEq_psiConc (hLC : Submission.Diff.LCSmooth I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (hg : ChartData (I := I) (M := M) (g₀.inner)) :
    (fun c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
        psi (I := I) hLC D ρ ε c hg)
      =ᶠ[𝓝 0] (psiConc (I := I) (M := M) g₀ D ρ ε) := by
  filter_upwards [eventually_posDef (I := I) (M := M) D ε] with c hc
  exact psi_eq_psiConc (I := I) (M := M) hLC D ρ ε hg c hc

end

end Work.Diff.STE.D
