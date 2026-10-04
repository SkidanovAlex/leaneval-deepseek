/-
# Layer D, step 4: the total Galerkin vector field `psi` on the coefficient space

The Galerkin scheme of Layer D needs a *total* vector field on the coefficient space
`JIdx ι₀ n ε → ℝ`, so that Picard–Lindelöf can be applied:

  `psi hLC D ρ ε c := if (g₀ + genMap D ε c is positive definite) then galVFaff … else 0`.

The positivity of the perturbed metric `g₀ + genMap D ε c` is an *open* condition in `c` (it holds
at `c = 0` since `g₀` is a metric), so on a neighbourhood of `0` the `if` takes the first branch and
`psi` agrees with the affine Galerkin vector field `galVFaff`.  The key identity

  `genMap D ε (psi … c) = J ρ ε (P (g₀ + genMap D ε c))`

on the positivity set is `Work.Diff.STE.D.genMap_psi`, a direct consequence of
`Work.Diff.STE.D.genMap_galVFaff`.  The remaining input for the ODE is that `psi` is `C¹` at `0`
(the DeTurck nonlinearity is smooth on the positive definite locus — the `deTurck/` files), after
which `Mathlib.Analysis.ODE.PicardLindelof` produces a local solution `c` of `c' = psi c`,
`c 0 = 0`, hence a Galerkin metric `u = g₀ + genMap D ε c` with `u' = J ρ ε (P u)`.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.Galerkin
import Submission.Work.Diff.STE.D.ODE
import Submission.Work.Diff.STE.D.isSymm_genMap
import Submission.Work.Diff.STE.D.isSymm_addSec
import Submission.Work.Diff.STE.D.ChartData_genMap
import Submission.Work.Diff.STE.D.genMap_galVFaff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
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

/-- The section `g₀ + genMap D ε c` is symmetric. -/
theorem isSymm_addSec_genMap [T2Space M] [I.Boundaryless]
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    IsSymm (I := I) (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) :=
  isSymm_addSec (I := I) (M := M) (ι₀ := ι₀) (g₀ := g₀) (genMap (I := I) (M := M) D ε c)
    (isSymm_genMap (I := I) (M := M) D ε c)

/-- The section `g₀ + genMap D ε c` has smooth chart data. -/
theorem chartData_addSec_genMap [T2Space M] [I.Boundaryless]
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hg : ChartData (I := I) (M := M) (g₀.inner)) :
    ChartData (I := I) (M := M)
      (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) :=
  GenMap.chartData_add (I := I) hg
    (ChartData_genMap (I := I) (M := M) D ε c)

/-- **The total Galerkin vector field** on the coefficient space: the affine vector field where the
perturbed metric is positive definite, and zero elsewhere. -/
def psi [T2Space M] [I.Boundaryless] (hLC : LCSmooth I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hg : ChartData (I := I) (M := M) (g₀.inner)) :
    Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ :=
  if hpos : (∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c) x v v) then
    galVFaff hLC g₀ D ρ ε c (isSymm_addSec_genMap D ε c)
      (chartData_addSec_genMap D ε c hg) hpos
  else 0

/-- **The value of the Galerkin vector field on the positivity set**: on the region where the
perturbed metric `g₀ + genMap D ε c` is positive definite, `psi` realises `J ρ ε (P (g₀ + genMap c))`
as a linear combination of the symmetrised spanning family. -/
theorem genMap_psi [T2Space M] [I.Boundaryless] (hLC : LCSmooth I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hg : ChartData (I := I) (M := M) (g₀.inner))
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c) x v v) :
    genMap (I := I) (M := M) D ε (psi (I := I) hLC D ρ ε c hg)
      = D.J ρ ε (deTurckSec hLC g₀
          (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c))
          (isSymm_addSec_genMap D ε c) hpos (chartData_addSec_genMap D ε c hg)) := by
  unfold psi
  rw [dif_pos hpos]
  exact genMap_galVFaff hLC D ρ ε hε hρ0 c (isSymm_addSec_genMap D ε c)
    (chartData_addSec_genMap D ε c hg) hpos

/-- **The Galerkin metric along a solution of the coefficient ODE**, pointwise form.  If `c` solves
`c' = psi c` on `Icc a b`, then for every point `x` and every pair of tangent vectors `u, v` the
real-valued function `s ↦ (g₀ + genMap D ε (c s)) x u v` has derivative
`(genMap D ε (psi … (c t))) x u v`; by `Work.Diff.STE.D.genMap_psi` this is
`J ρ ε (P (g₀ + genMap D ε (c t))) x u v` wherever `c t` lies in the positivity set, i.e. the
Galerkin approximant satisfies the DeTurck equation `u' = J ρ ε (P u)`.

The statement is deliberately *pointwise*: `Bil I M` is a `Π`-type of spaces of continuous linear
maps, and the instance `Module ℝ (Bil I M)` is not synthesizable in every elaboration context, so a
`Bil`-valued `HasDerivWithinAt` cannot be stated robustly.  The pointwise form is also exactly what
the energy argument uses (every estimate of Layer B3 is componentwise). -/
theorem hasDerivWithinAt_addSec_genMap [T2Space M] [I.Boundaryless]
    (hLC : LCSmooth I M) (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (hg : ChartData (I := I) (M := M) (g₀.inner)) (a b : ℝ)
    (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ))
    (hc : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt c (psi (I := I) hLC D ρ ε (c t) hg) (Set.Icc a b) t) :
    ∀ t ∈ Set.Icc a b, ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt
        (fun s => addSec (I := I) g₀ (genMap (I := I) (M := M) D ε (c s)) x u v)
        (genMap (I := I) (M := M) D ε (psi (I := I) hLC D ρ ε (c t) hg) x u v)
        (Set.Icc a b) t := by
  intro t ht x u v
  have h1 : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      HasDerivWithinAt (fun s => (c s) z • jSym (I := I) (M := M) D ε z x u v)
        ((psi (I := I) hLC D ρ ε (c t) hg) z • jSym (I := I) (M := M) D ε z x u v)
        (Set.Icc a b) t :=
    fun z => (((ContinuousLinearMap.proj z).hasFDerivAt).comp_hasDerivWithinAt t (hc t ht))
      |>.smul_const (jSym (I := I) (M := M) D ε z x u v)
  have h2 := HasDerivWithinAt.sum (u := Finset.univ) (fun z _ => h1 z)
  have h3 := h2.const_add (g₀.inner x u v)
  simpa only [addSec_apply, genMap, Finset.sum_apply, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, sum_apply] using h3

end

end Work.Diff.STE.D
