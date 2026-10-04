/-
# Layer D, step 3: the Galerkin vector field is the Galerkin approximation of the DeTurck equation

The Galerkin ODE of Layer D is  `c' = ψ(c)`,  `ψ(c)_z = (1/2) · jFamilyCoeff D ρ ε (P (genMap D ε c)) z`,
where `P = deTurckSec hLC g₀` is the DeTurck operator and `genMap D ε c = Σ_z c z • jSym D ε z` is
the coefficient-to-section map of `Work.Diff.STE.D.Galerkin`.  This file records the *defining
property* of that vector field:

  `genMap D ε (galVF …) = J ρ ε (P (genMap D ε c))`,

i.e. the Galerkin vector field applied in coefficient space is exactly the Friedrichs mollifier of
the DeTurck operator evaluated at the section `genMap D ε c`.  In other words, the Galerkin
projection of the DeTurck equation is *closed* in the Galerkin space `range (J ρ ε)`.

The whole content is the symmetrisation factor `1/2`: `genMap` uses the *symmetrised* family
`jSym z = jFamily z + jFamily (idxSwap z)`, so `genMap D ε (C / 2) = Σ_z C z • jFamily z` whenever
the coefficient family `C` is invariant under the slot swap (`Work.Diff.STE.D.genMap_div_two_eq_sum`),
and the expansion of `J ρ ε h` in the raw family (`Work.Diff.STE.B3.J_eq_sum_index`) identifies the
right-hand side with `J ρ ε h`.  The swap invariance of the coefficients of `J ρ ε (P (genMap D ε c))`
is the symmetry of `P (genMap D ε c)`, i.e. the classical fact that the DeTurck tensor
`P(g) = -2 Ric(g) + L_{W(g)} g` of a metric is a symmetric 2-tensor:
`Ric` is symmetric (`Work.Diff.EXT.ricAt_symm_L`) and the Lie derivative of a symmetric metric is
symmetric (`Work.Diff.STE.DeTurck.lieMet_comm`).

The two ingredients are isolated as the lemmas `deTurckSec_symm` and `jFamilyCoeff_idxSwap` above the
target.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.D.Galerkin
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.ODE
import Submission.Work.Diff.STE.D.isSymm_genMap
import Submission.Work.Diff.STE.D.J_mem_span

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
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

/-- **The DeTurck tensor of a metric is symmetric.**  With `g = smetOf h …` the DeTurck operator is
`P(g) = -2 Ric(g) + L_{W(g)} g`: `Ric` is symmetric because the curvature of a Levi-Civita
connection has the pair-exchange symmetry (`Work.Diff.EXT.ricAt_symm_L`), and the Lie derivative
`L_W g(u,v) = g(∇_u W, v) + g(u, ∇_v W)` is symmetric because `g` is (`lieMet_comm`).  This is the
symmetry of `deTurckSec`, which makes the coefficients of `J ρ ε (P(genMap D ε c))` swap invariant. -/
lemma deTurckSec_symm [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ x u v, h x u v = h x v u)
    (hpos : ∀ x v, v ≠ 0 → 0 < h x v v)
    (hsmooth : ChartData (I := I) (M := M) h) :
    ∀ x u v, deTurckSec hLC g₀ h hsym hpos hsmooth x u v
      = deTurckSec hLC g₀ h hsym hpos hsmooth x v u := by
  intro x u v
  rw [deTurckSec_apply, deTurckSec_apply,
      Work.Diff.STE.DeTurck.deTurckOp_apply, Work.Diff.STE.DeTurck.deTurckOp_apply]
  have hcov := (hLC (smetOf h hsym hpos hsmooth)).1.some
  rw [Work.Diff.EXT.ricAt_symm_L hLC (smetOf h hsym hpos hsmooth) hcov x u v,
      Work.Diff.STE.DeTurck.lieMet_comm (smetOf h hsym hpos hsmooth) _ x u v]

/-- **Swap invariance of the coefficients of `J ρ ε h` for symmetric `h`.**  The coefficients of the
finite expansion of `J ρ ε h` are the Fourier coefficients of the chart components
`D.R i h a b`, which are symmetric in the two frame slots exactly when `h` is a symmetric section.
Since the swap `idxSwap` of the product index exchanges those two slots, the coefficient family is
invariant under it.  This is the hypothesis of `genMap_div_two_eq_sum`, i.e. the reason why the
symmetrisation factor `1/2` in `galVF` is the correct one. -/
lemma jFamilyCoeff_idxSwap
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (hsym : IsSymm (I := I) h)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    Work.Diff.STE.B3.jFamilyCoeff D ρ ε h (idxSwap (E := E) (ι₀ := ι₀) ε z)
      = Work.Diff.STE.B3.jFamilyCoeff D ρ ε h z := by
  have hR : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      D.R i h a b = D.R i h b a := by
    intro i a b
    funext z
    simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat]
    rw [hsym (D.pt i z) (D.e i a (D.pt i z)) (D.e i b (D.pt i z))]
  obtain ⟨i, a, b, q⟩ := z
  simp only [Work.Diff.STE.B3.jFamilyCoeff, Work.Diff.STE.D.idxSwap_apply]
  rw [← hR i a b]

/-- **The Galerkin vector field is the Galerkin approximation of the DeTurck equation**: applying
`genMap D ε` to the coefficient vector field `galVF` of the Galerkin ODE gives the Friedrichs
mollifier `J ρ ε` of the DeTurck tensor `P(genMap D ε c)` of the section `genMap D ε c`. -/
theorem genMap_galVF
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
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M)
      (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c))
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < Work.Diff.STE.D.genMap (I := I) (M := M) D ε c x v v) :
    Work.Diff.STE.D.genMap (I := I) (M := M) D ε
        (Work.Diff.STE.D.galVF hLC g₀ D ρ ε c hsmooth hpos)
      = D.J ρ ε (Work.Diff.STE.D.deTurckSec hLC g₀
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)
          (Work.Diff.STE.D.isSymm_genMap (I := I) (M := M) D ε c) hpos hsmooth) := by
  -- the DeTurck tensor of the section `genMap D ε c` is symmetric
  have hss : IsSymm (I := I) (deTurckSec hLC g₀ (genMap D ε c)
      (isSymm_genMap D ε c) hpos hsmooth) :=
    deTurckSec_symm hLC (genMap D ε c) (isSymm_genMap D ε c) hpos hsmooth
  -- hence its coefficients in the raw family are swap invariant
  have hC : ∀ z, Work.Diff.STE.B3.jFamilyCoeff D ρ ε
        (deTurckSec hLC g₀ (genMap D ε c) (isSymm_genMap D ε c) hpos hsmooth)
        (idxSwap (E := E) (ι₀ := ι₀) ε z)
      = Work.Diff.STE.B3.jFamilyCoeff D ρ ε
        (deTurckSec hLC g₀ (genMap D ε c) (isSymm_genMap D ε c) hpos hsmooth) z :=
    fun z => jFamilyCoeff_idxSwap D ρ ε _ hss z
  -- `galVF` is half these coefficients, so `genMap` of it is the sum over the raw family ...
  have hgal : galVF hLC g₀ D ρ ε c hsmooth hpos
      = fun z => Work.Diff.STE.B3.jFamilyCoeff D ρ ε
          (deTurckSec hLC g₀ (genMap D ε c) (isSymm_genMap D ε c) hpos hsmooth) z / 2 := by
    funext z
    simp only [galVF]
    ring
  -- ... which is exactly the expansion of `J ρ ε` of that DeTurck tensor
  rw [hgal, genMap_div_two_eq_sum D ε _ hC]
  exact (Work.Diff.STE.B3.J_eq_sum_index D ρ ε hε hρ0 _).symm

end

end Work.Diff.STE.D
