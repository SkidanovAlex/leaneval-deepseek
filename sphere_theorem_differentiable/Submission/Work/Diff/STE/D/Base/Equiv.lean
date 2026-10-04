/-
# Layer D: the base-generalised concrete field agrees with the DeTurck field

The concrete base-generalised field `psiConcB a₀ D ρ ε c` is defined through the *chart expression*
`secChart g₀ (fore a₀ D ε c)` of the DeTurck tensor, while the vector field of the Galerkin ODE is
defined through the geometric tensor `deTurckSec hLC g₀ (fore a₀ D ε c)`.  On the positivity set the
two agree: on the support of the localised weight the chart at the chart centre is genuine, so the
chart expression computes the DeTurck tensor (`Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp`).

Together with the symmetrisation identity
`D.J ρ ε h = genMap D ε (fun z => jFamilyCoeff D ρ ε h z / 2)` (valid for symmetric `h`, extracted
from `Work.Diff.STE.D.J_mem_span`), this gives the two identities the ODE argument needs:

* `deTurckSec … = J ρ ε (genMap (psiTrueB …))` — the DeTurck tensor of the foreground is the
  mollifier applied to the Galerkin section whose coefficients are the field, and
* `psiConcB … = psiTrueB …` pointwise on the positivity set.
-/
import Mathlib
import Submission.Work.Diff.STE.D.Base.Defs
import Submission.Work.Diff.STE.D.Base.Jet
import Submission.Work.Diff.STE.D.psi.Equiv
import Submission.Work.Diff.STE.D.genMap_galVFaff
import Submission.Work.Diff.STE.D.J_mem_span

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D.Base

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M} {ε : ℝ}

noncomputable section

/-! ## 1. The symmetrisation identity for the mollifier -/

/-- **The mollifier of a symmetric section is the Galerkin section with half the coefficients.** -/
theorem J_eq_genMap_div_two
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (h : Bil (I := I) (M := M)) (hsym : IsSymm (I := I) h) :
    D.J ρ ε h = Work.Diff.STE.D.genMap (I := I) (M := M) D ε
      (fun z => Work.Diff.STE.B3.jFamilyCoeff D ρ ε h z / 2) := by
  rw [Work.Diff.STE.B3.J_eq_sum_index D ρ ε hε hρ0 h]
  exact (Work.Diff.STE.D.genMap_div_two_eq_sum D ε
    (Work.Diff.STE.B3.jFamilyCoeff D ρ ε h)
    (fun z => Work.Diff.STE.D.jFamilyCoeff_idxSwap D ρ ε h hsym z)).symm

/-! ## 2. The "true" base-generalised field -/

/-- **The true base-generalised Galerkin vector field**: the Galerkin coefficients of the DeTurck
tensor of the affine foreground. -/
noncomputable def psiTrueB (hLC : LCSmooth I M) (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hsym : IsSymm (I := I) (fore (I := I) (M := M) a₀ D ε c))
    (hpos : IsPosF (I := I) (M := M) a₀ D ε c)
    (hsm : ChartData (I := I) (M := M) (fore (I := I) (M := M) a₀ D ε c)) :
    Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ :=
  fun z => (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
    (deTurckSec hLC g₀ (fore (I := I) (M := M) a₀ D ε c) hsym hpos hsm) z

/-- **On the positivity set the concrete field is the true field.** -/
theorem psiConcB_eq_psiTrueB (hLC : LCSmooth I M)
    (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hsym : IsSymm (I := I) (fore (I := I) (M := M) a₀ D ε c))
    (hpos : IsPosF (I := I) (M := M) a₀ D ε c)
    (hsm : ChartData (I := I) (M := M) (fore (I := I) (M := M) a₀ D ε c)) :
    psiConcB (I := I) (M := M) a₀ D ρ ε c =
      psiTrueB (I := I) (M := M) hLC a₀ D ρ ε c hsym hpos hsm := by
  -- the localised components agree wherever the localised weight does not vanish
  have hbridge : ∀ (i : ι₀) (z' : Fin (Module.finrank ℝ E) → ℝ)
      (a b : Fin (Module.finrank ℝ E)), D.psi i z' ≠ 0 →
      D.mat i (deTurckSec hLC g₀ (fore (I := I) (M := M) a₀ D ε c) hsym hpos hsm) a b z'
        = D.mat i (secChart (I := I) (M := M) g₀ (fore (I := I) (M := M) a₀ D ε c)
            (D.x₀ i)) a b z' := by
    intro i z' a b hz
    have hζ : D.ζ i (D.pt i z') ≠ 0 :=
      fun h0 => hz (by simp only [Work.Diff.STE.B3Data.psi, h0, mul_zero])
    have hsrc' : D.pt i z' ∈ (extChartAt I (D.x₀ i)).source := (D.hζsupp i _ hζ).1
    have hsrc : D.pt i z' ∈ (chartAt H (D.x₀ i)).source := by
      rwa [extChartAt_source] at hsrc'
    rw [Work.Diff.STE.B3Data.mat, Work.Diff.STE.B3Data.mat, Work.Diff.STE.D.secChart_apply]
    rw [deTurckSec_apply hLC g₀ (fore (I := I) (M := M) a₀ D ε c) hsym hpos hsm
      (D.pt i z') (D.e i a (D.pt i z')) (D.e i b (D.pt i z'))]
    exact (Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp (I := I) (M := M) hLC
      (smetOf (fore (I := I) (M := M) a₀ D ε c) hsym hpos hsm)
      g₀ (D.x₀ i) (x := D.pt i z') hsrc
      (D.e i a (D.pt i z')) (D.e i b (D.pt i z'))).symm
  have hRQ : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      D.R i (deTurckSec hLC g₀ (fore (I := I) (M := M) a₀ D ε c) hsym hpos hsm) a b
        = D.R i (secChart (I := I) (M := M) g₀ (fore (I := I) (M := M) a₀ D ε c)
            (D.x₀ i)) a b := by
    intro i a b
    funext z'
    by_cases hz : D.psi i z' = 0
    · simp only [Work.Diff.STE.B3Data.R, hz, zero_mul]
    · simp only [Work.Diff.STE.B3Data.R]
      rw [hbridge i z' a b hz]
  funext z
  show (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
      (secChart (I := I) (M := M) g₀ (fore (I := I) (M := M) a₀ D ε c) (D.x₀ z.1)) z
    = (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
      (deTurckSec hLC g₀ (fore (I := I) (M := M) a₀ D ε c) hsym hpos hsm) z
  congr 1
  simp only [Work.Diff.STE.B3.jFamilyCoeff]
  rw [hRQ z.1 z.2.1 z.2.2.1]

/-- **The DeTurck tensor of the foreground is the mollifier of the Galerkin section of the field.** -/
theorem J_psiTrueB (hLC : LCSmooth I M) (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hsym : IsSymm (I := I) (fore (I := I) (M := M) a₀ D ε c))
    (hpos : IsPosF (I := I) (M := M) a₀ D ε c)
    (hsm : ChartData (I := I) (M := M) (fore (I := I) (M := M) a₀ D ε c)) :
    D.J ρ ε (deTurckSec hLC g₀ (fore (I := I) (M := M) a₀ D ε c) hsym hpos hsm)
      = Work.Diff.STE.D.genMap (I := I) (M := M) D ε
          (psiTrueB (I := I) (M := M) hLC a₀ D ρ ε c hsym hpos hsm) := by
  have hss : IsSymm (I := I)
      (deTurckSec hLC g₀ (fore (I := I) (M := M) a₀ D ε c) hsym hpos hsm) :=
    deTurckSec_symm hLC (fore (I := I) (M := M) a₀ D ε c) hsym hpos hsm
  have h := J_eq_genMap_div_two (I := I) (M := M) D ρ ε hε hρ0
    (deTurckSec hLC g₀ (fore (I := I) (M := M) a₀ D ε c) hsym hpos hsm) hss
  rw [h]
  congr 1
  funext z
  simp only [psiTrueB]
  ring

end

end Work.Diff.STE.D.Base
