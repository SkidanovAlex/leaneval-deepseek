/-
# Layer D: the concrete objects of the smoothness proof of `psiConc`

`Work.Diff.STE.D.psiConc g₀ D ρ ε c z = (1/2) · jFamilyCoeff D ρ ε (secChart g₀ (g₀ + genMap c) (x₀ z.1)) z`,
and the localised component entering the coefficient is

  `Fz c y = ψ i y · √(dens i y) · (secChart g₀ (g₀ + genMap c) (x₀ i)) (pt i y) (eᵢa) (eᵢb)`.

The chart expression of the DeTurck section is `pPhi` evaluated at the pair of `2`-jets

  `jetPairOf c y = (jet (g₀) y, jet (g₀ + genMap D ε c) y)`

of the background metric and of the unknown; `pPhi` is `C^∞` on the set `pPhiDom` where the two
Gram matrices are invertible (`Work.Diff.STE.deTurck.contDiffOn_pPhi`).  Hence the whole analytic
content of the smoothness of `psiConc` is:

* the *affinity* of `c ↦ jetPairOf c y` (a finite sum, `Work.Diff.STE.D.psi.chartJetOf_genMap_affine`),
* the *Taylor estimate* for `pPhiFun` around the compact set of base points
  (`Work.Diff.STE.D.psi.abs_Fz_sub_le`), and
* the ℝ-linearity of the Fourier coefficient `scoeff` on the supported functions
  (`Work.Diff.STE.B3.scoeff_add_of_support`, `Work.Diff.STE.B3.scoeff_smul_of_support`) plus its
  sup-norm bound (`Work.Diff.STE.B3.abs_scoeff_le`).

This module fixes the objects (`pPhiFun`, `jetPairOf`, `jetDir`, `Fz`, `Ufun`) in terms of which
those statements are made.
-/
import Mathlib
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.STE.deTurck.contDiffOn_pPhi

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
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

/-- **The jet-level DeTurck operator as a function of the pair of jets** (background and
foreground).  Its smoothness on the set where both Gram matrices are invertible is
`Work.Diff.STE.deTurck.contDiffOn_pPhi`. -/
noncomputable def pPhiFun : Work.Diff.STE.deTurck.JetPair (E := E) →
    Work.Diff.EXT.MatE (E := E) :=
  fun w i j => Work.Diff.STE.DeTurck.pPhi w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2.1 w.2.2.2 i j

@[simp] lemma pPhiFun_apply (w : Work.Diff.STE.deTurck.JetPair (E := E))
    (i j : Fin (Module.finrank ℝ E)) :
    pPhiFun (E := E) w i j =
      Work.Diff.STE.DeTurck.pPhi w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2.1 w.2.2.2 i j := rfl

/-- **The positivity condition** on the coefficients: the perturbed section `g₀ + genMap D ε c` is a
positive definite bilinear form.  This is the first branch of `Work.Diff.STE.D.psi`, and it holds on
a neighbourhood of `0` (`Work.Diff.STE.D.eventually_posDef`). -/
def IsPos (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
    0 < addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c) x v v

/-- **The derivative of the jet-level DeTurck operator.**  The instance argument `Module ℝ` for the
pair of jets has to be supplied locally: a bare `fderiv ℝ pPhiFun w` gets stuck in the instance
search for the product type. -/
noncomputable def pPhiFunD (w : Work.Diff.STE.deTurck.JetPair (E := E)) :
    Work.Diff.STE.deTurck.JetPair (E := E) →L[ℝ] Work.Diff.EXT.MatE (E := E) := by
  letI : Module ℝ (Work.Diff.STE.deTurck.JetPair (E := E)) := inferInstance
  exact fderiv ℝ (pPhiFun (E := E)) w

/-- **The pair of spatial `2`-jets of the metric family** at the chart coordinate `y`: the jets of
the background `g₀` and of the section `g₀ + genMap D ε c`. -/
noncomputable def jetPairOf (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (y : E) :
    Work.Diff.STE.deTurck.JetPair (E := E) :=
  (chartJetOf (I := I) (M := M) g₀.inner x₀ y,
   chartJetOf (I := I) (M := M)
     (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) x₀ y)

/-- The *direction* of the affine family in the coordinate of the index `z`: the jet pair whose
background component vanishes and whose foreground component is the jet of the spanning vector
`jSym D ε z`. -/
noncomputable def jetDir (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) (y : E) :
    Work.Diff.STE.deTurck.JetPair (E := E) :=
  (0, chartJetOf (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀ y)

/-- **The localised component of the chart section** in the frame of the chart at `x₀ z.1`. -/
noncomputable def Fz (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun c y => D.R z.1 (secChart (I := I) (M := M) g₀
      (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) (D.x₀ z.1))
    z.2.1 z.2.2.1 y

/-- **The directional derivative integrand** of the localised component: the derivative of the
chart DeTurck expression in the direction of the `z'`-th coefficient, multiplied by the same
weights as `Fz`. -/
noncomputable def Ufun (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun c₀ y => D.psi z.1 y * Real.sqrt (D.dens z.1 y) *
    ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
      coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j (D.e z.1 z.2.1 (D.pt z.1 y))
        * coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k (D.e z.1 z.2.2.1 (D.pt z.1 y))
        * (pPhiFunD (E := E)
              (jetPairOf (I := I) (M := M) g₀ D ε (D.x₀ z.1) c₀
                (Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y))
              (jetDir (I := I) (M := M) g₀ D ε (D.x₀ z.1) z'
                (Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y))) j k

end

end Work.Diff.STE.D
