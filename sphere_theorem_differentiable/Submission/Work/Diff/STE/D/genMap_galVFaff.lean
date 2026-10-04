import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.D.Galerkin
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.ODE
import Submission.Work.Diff.STE.D.isSymm_genMap
import Submission.Work.Diff.STE.D.J_mem_span
import Submission.Work.Diff.STE.D.genMap_galVF

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.D

theorem genMap_galVFaff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (hLC : Submission.Diff.LCSmooth I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hsym : Work.Diff.STE.D.IsSymm (I := I)
      (Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M)
      (Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)))
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < Work.Diff.STE.D.addSec (I := I) g₀
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c) x v v) :
    Work.Diff.STE.D.genMap (I := I) (M := M) D ε
        (Work.Diff.STE.D.galVFaff hLC g₀ D ρ ε c hsym hsmooth hpos)
      = D.J ρ ε (Work.Diff.STE.D.deTurckSec hLC g₀
          (Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c))
          hsym hpos hsmooth) := by
  -- the DeTurck tensor `P(g₀ + genMap D ε c)` of the symmetric section `addSec g₀ (genMap D ε c)`
  -- is symmetric (Ric is symmetric and the Lie derivative of a symmetric metric is symmetric)
  have hss : IsSymm (I := I)
      (deTurckSec hLC g₀ (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c))
        hsym hpos hsmooth) :=
    deTurckSec_symm hLC (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c))
      hsym hpos hsmooth
  -- hence its coefficients in the raw family are swap invariant
  have hC : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      Work.Diff.STE.B3.jFamilyCoeff D ρ ε
          (deTurckSec hLC g₀ (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c))
            hsym hpos hsmooth)
          (idxSwap (E := E) (ι₀ := ι₀) ε z)
        = Work.Diff.STE.B3.jFamilyCoeff D ρ ε
          (deTurckSec hLC g₀ (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c))
            hsym hpos hsmooth) z :=
    fun z => jFamilyCoeff_idxSwap D ρ ε _ hss z
  -- `galVFaff` is half these coefficients, so `genMap` of it is the sum over the raw family ...
  have hgal : galVFaff hLC g₀ D ρ ε c hsym hsmooth hpos
      = fun z => Work.Diff.STE.B3.jFamilyCoeff D ρ ε
          (deTurckSec hLC g₀ (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c))
            hsym hpos hsmooth) z / 2 := by
    funext z
    simp only [galVFaff]
    ring
  -- ... which is exactly the expansion of `J ρ ε` of that DeTurck tensor
  rw [hgal, genMap_div_two_eq_sum D ε _ hC]
  exact (Work.Diff.STE.B3.J_eq_sum_index D ρ ε hε hρ0 _).symm

end Work.Diff.STE.D
