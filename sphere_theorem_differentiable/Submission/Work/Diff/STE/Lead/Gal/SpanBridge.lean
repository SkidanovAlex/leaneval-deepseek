import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.SpanLin
import Submission.Work.Diff.STE.D.Base.Equiv
import Submission.Work.Diff.STE.D.Base.Assemble
import Submission.Work.Diff.STE.D.BasePos.exists_isPosF_ball

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The span-form field `galVF2` as the base-generalised concrete field `psiConcB`

The foreground of the span-form Galerkin scheme is the *span element*
`u~(c) = J ρ ε (galState D ε c) = genMap D ε (Fcoef c)`.  With the base
`a₀ = genMap D ε e₀`, `e₀ = Fcoef c₀`, the base-generalised field `psiConcB a₀ D ρ ε` of
`Work.Diff.STE.D.Base` therefore computes exactly the chart expression of the span-form scheme:

  `galVF2 c = psiConcB a₀ D ρ ε (Fcoef c - e₀)`

on the positivity region of `u~(c)`.  This module reduces `galVF2` to that field, so that the
`C¹`/Lipschitz machinery of the base-generalised development applies.
-/

namespace Work.Diff.STE.Lead.Gal

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## Linearity of `genMap` in the coefficients -/

/-- `genMap` is additive in the coefficient vector. -/
theorem genMap_add (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c c' : Coef ι₀ (Module.finrank ℝ E) ε) :
    Work.Diff.STE.D.genMap (I := I) (M := M) D ε (c + c')
      = Work.Diff.STE.D.genMap (I := I) (M := M) D ε c
        + Work.Diff.STE.D.genMap (I := I) (M := M) D ε c' := by
  ext x u v
  show (∑ z, (c + c') z • Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x u v
      = ((∑ z, c z • Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
        + (∑ z, c' z • Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)) x u v
  simp only [Finset.sum_apply, Pi.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    add_mul]
  rw [Finset.sum_add_distrib]

/-- `genMap` is subtractive in the coefficient vector. -/
theorem genMap_sub (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c c' : Coef ι₀ (Module.finrank ℝ E) ε) :
    Work.Diff.STE.D.genMap (I := I) (M := M) D ε (c - c')
      = Work.Diff.STE.D.genMap (I := I) (M := M) D ε c
        - Work.Diff.STE.D.genMap (I := I) (M := M) D ε c' := by
  ext x u v
  show (∑ z, (c - c') z • Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x u v
      = ((∑ z, c z • Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
        - (∑ z, c' z • Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)) x u v
  simp only [Finset.sum_apply, Pi.sub_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.sub_apply, Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    sub_mul]
  rw [Finset.sum_sub_distrib]

/-- **The affine foreground with base `genMap D ε e` at `c - e` is the span element `genMap D ε c`.** -/
theorem fore_genMap_sub (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (e c : Coef ι₀ (Module.finrank ℝ E) ε) :
    Work.Diff.STE.D.Base.fore (I := I) (M := M)
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε e) D ε (c - e)
      = Work.Diff.STE.D.genMap (I := I) (M := M) D ε c := by
  rw [Work.Diff.STE.D.Base.fore_eq_add, genMap_sub]
  abel

/-- **The DeTurck tensor of the foreground of the span-form scheme is the DeTurck tensor of the span
element** `genMap D ε (Fcoef c)`. -/
theorem galVF2_fore_eq (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (e : Coef ι₀ (Module.finrank ℝ E) ε) (c : Coef ι₀ (Module.finrank ℝ E) ε) :
    Work.Diff.STE.D.Base.fore (I := I) (M := M)
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε e) D ε (Fcoef D ρ ε c - e)
      = D.J ρ ε (Submission.Diff.STEGal.galState D ε c) := by
  rw [fore_genMap_sub]
  exact (Work.Diff.STE.Lead.J_eq_genMap_galCoeff D ρ ε hε hρ0
    (Submission.Diff.STEGal.galState D ε c)
    (Work.Diff.STE.Lead.isSymm_galState D ε c)).symm

/-! ## The positivity predicates agree -/

/-- **The base-generalised positivity of the shifted coefficients is the positivity of the
foreground.** -/
theorem isPosF_iff_spanPos (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (e c : Coef ι₀ (Module.finrank ℝ E) ε) :
    Work.Diff.STE.D.Base.IsPosF (I := I) (M := M)
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε e) D ε (Fcoef D ρ ε c - e)
      ↔ ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
          0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x v v := by
  constructor
  · intro h x v hv
    have h1 : 0 < Work.Diff.STE.D.Base.fore (I := I) (M := M)
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε e) D ε (Fcoef D ρ ε c - e) x v v :=
      h x v hv
    rwa [galVF2_fore_eq D ρ ε hε hρ0 e c] at h1
  · intro h x v hv
    have h1 : 0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x v v := h x v hv
    rwa [← galVF2_fore_eq D ρ ε hε hρ0 e c] at h1

/-! ## The bridge between the chart expression and the DeTurck tensor -/

/-- **The Galerkin coefficient of the chart expression of the DeTurck tensor of a positive definite
smooth section is the Galerkin coefficient of the tensor itself.** -/
theorem jFamilyCoeff_secChart_eq_deTurckSec
    (hLC : Submission.Diff.LCSmooth I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (ε : ℝ) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : Work.Diff.STE.D.IsSymm (I := I) h)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    Work.Diff.STE.B3.jFamilyCoeff D ρ ε
        (Work.Diff.STE.D.secChart (I := I) (M := M) g₀ h (D.x₀ z.1)) z
      = Work.Diff.STE.B3.jFamilyCoeff D ρ ε
          (Work.Diff.STE.D.deTurckSec hLC g₀ h hsym hpos hsm) z := by
  have hbridge : ∀ (i : ι₀) (z' : Fin (Module.finrank ℝ E) → ℝ)
      (a b : Fin (Module.finrank ℝ E)), D.psi i z' ≠ 0 →
      D.mat i (Work.Diff.STE.D.deTurckSec hLC g₀ h hsym hpos hsm) a b z'
        = D.mat i (Work.Diff.STE.D.secChart (I := I) (M := M) g₀ h (D.x₀ i)) a b z' := by
    intro i z' a b hz
    have hζ : D.ζ i (D.pt i z') ≠ 0 :=
      fun h0 => hz (by simp only [Work.Diff.STE.B3Data.psi, h0, mul_zero])
    have hsrc' : D.pt i z' ∈ (extChartAt I (D.x₀ i)).source := (D.hζsupp i _ hζ).1
    have hsrc : D.pt i z' ∈ (chartAt H (D.x₀ i)).source := by
      rwa [extChartAt_source] at hsrc'
    rw [Work.Diff.STE.B3Data.mat, Work.Diff.STE.B3Data.mat, Work.Diff.STE.D.secChart_apply]
    rw [Work.Diff.STE.D.deTurckSec_apply hLC g₀ h hsym hpos hsm
      (D.pt i z') (D.e i a (D.pt i z')) (D.e i b (D.pt i z'))]
    exact (Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp (I := I) (M := M) hLC
      (Work.Diff.STE.D.smetOf h hsym hpos hsm) g₀ (D.x₀ i) (x := D.pt i z') hsrc
      (D.e i a (D.pt i z')) (D.e i b (D.pt i z'))).symm
  have hRQ : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      D.R i (Work.Diff.STE.D.deTurckSec hLC g₀ h hsym hpos hsm) a b
        = D.R i (Work.Diff.STE.D.secChart (I := I) (M := M) g₀ h (D.x₀ i)) a b := by
    intro i a b
    funext z'
    by_cases hz : D.psi i z' = 0
    · simp only [Work.Diff.STE.B3Data.R, hz, zero_mul]
    · simp only [Work.Diff.STE.B3Data.R]
      rw [hbridge i z' a b hz]
  simp only [Work.Diff.STE.B3.jFamilyCoeff]
  rw [hRQ z.1 z.2.1 z.2.2.1]

/-- **The span-form field is the base-generalised concrete field at the shifted coefficients.** -/
theorem galVF2_eq_psiConcB (hLC : Submission.Diff.LCSmooth I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (e : Coef ι₀ (Module.finrank ℝ E) ε) (c : Coef ι₀ (Module.finrank ℝ E) ε)
    (hposc : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x v v) :
    Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 c
      = Work.Diff.STE.D.Base.psiConcB (I := I) (M := M)
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε e) D ρ ε
          (Fcoef D ρ ε c - e) := by
  haveI : CompleteSpace E := ‹CompleteSpace E›
  funext z
  rw [Work.Diff.STE.Lead.galVF2_of_pos hLC D ρ ε hε hρ0 c hposc]
  rw [Work.Diff.STE.D.Base.psiConcB_apply]
  rw [galVF2_fore_eq D ρ ε hε hρ0 e c]
  show (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
      (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀
        (D.J ρ ε (Submission.Diff.STEGal.galState D ε c))
        (Work.Diff.STE.Lead.isSymm_J D ρ ε hε hρ0 (Submission.Diff.STEGal.galState D ε c)
          (Work.Diff.STE.Lead.isSymm_galState D ε c)) hposc
        (Work.Diff.STE.Lead.chartData_J D ρ ε hε hρ0 (Submission.Diff.STEGal.galState D ε c)
          (Work.Diff.STE.Lead.isSymm_galState D ε c))) z
    = (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
        (Work.Diff.STE.D.secChart (I := I) (M := M) g₀
          (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) (D.x₀ z.1)) z
  exact congrArg (fun w => (1 / 2 : ℝ) * w)
    (jFamilyCoeff_secChart_eq_deTurckSec (I := I) (M := M) hLC D ρ ε
      (D.J ρ ε (Submission.Diff.STEGal.galState D ε c))
      (Work.Diff.STE.Lead.isSymm_J D ρ ε hε hρ0 (Submission.Diff.STEGal.galState D ε c)
        (Work.Diff.STE.Lead.isSymm_galState D ε c)) hposc
      (Work.Diff.STE.Lead.chartData_J D ρ ε hε hρ0 (Submission.Diff.STEGal.galState D ε c)
        (Work.Diff.STE.Lead.isSymm_galState D ε c)) z).symm

end

end Work.Diff.STE.Lead.Gal
