/-
# Layer D/STE: the Galerkin state, and its Friedrichs mollification, are symmetric sections
with smooth chart data

The Galerkin state of Layer D at a coefficient vector `c` is the section

  `galState D ε c = g₀ + Σ_z c z • jSym D ε z = g₀ + genMap D ε c`

(`Work.Diff.STE.D.addSec`, `Work.Diff.STE.D.genMap`), and the Galerkin ODE runs the *Friedrichs
mollifier* `J ρ ε` (`Work.Diff.STE.B3Data.J`) on it.  The two structural facts about a section which
the Layer-D machinery needs (positivity being the third, and an open condition) are:

* `Work.Diff.STE.D.IsSymm h` — pointwise symmetry of the bilinear form; and
* `Work.Diff.STE.D.ChartData h` — smoothness of the chart matrix of `h` on every chart target, the
  analytic input which turns a positive definite section into a global smooth metric
  (`Work.Diff.STE.D.smetOf`).

This file proves that **both are preserved along the Galerkin state and along its mollification**:

  `IsSymm (g₀ + genMap D ε c)`, `ChartData (g₀ + genMap D ε c)`,
  `IsSymm (J ρ ε (g₀ + genMap D ε c))`, `ChartData (J ρ ε (g₀ + genMap D ε c))`.

The first two are the proved Layer-D facts `isSymm_addSec_genMap` / `chartData_addSec_genMap`; the
last two are reduced here to the *pointwise* structure of the mollifier, which is the content of the
two helper lemmas below:

* `Work.Diff.STE.B3Data.J ρ ε h = Σ_i R_i*(S_ε (R_i h))` is a sum of reconstructions `Rstar i u`
  (`Work.Diff.STE.B3Data.J`, `Work.Diff.STE.B3Data.Rstar`);
* `Rstar i u` is symmetric as soon as the coefficient family `u` is symmetric in the two matrix
  slots (`Work.Diff.STE.D.Rstar_symm`), and the truncated components of a symmetric section are
  symmetric because the *same* frame field `D.e i a` is used for both slots
  (`B3Data.R_swap_of_isSymm`);
* `Rstar i u` has smooth chart data as soon as every component `u a b` is `C^∞` on the flat space
  (`Work.Diff.STE.D.ChartData_Rstar`), and `STruncR ρ ε f` is `C^∞` whenever `f` is a smooth
  function supported in the open unit cube (`contDiff_STruncR_of_support`), which holds for the
  components `R_i h` of a section with smooth chart data
  (`Work.Diff.STE.B3.R_contDiff_of_chartData`, `Work.Diff.STE.B3.R_support_cube`).
-/
import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.B3.STruncC_contDiff_periodic
import Submission.Work.Diff.STE.B3.BNorm_J_sub_le
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.Galerkin
import Submission.Work.Diff.STE.D.ChartData_genMap
import Submission.Work.Diff.STE.D.ChartData_Rstar
import Submission.Work.Diff.STE.D.isSymm_genMap
import Submission.Work.Diff.STE.D.isSymm_addSec
import Submission.Work.Diff.STE.D.Rstar_symm
import Submission.Work.Diff.STE.D.GalODE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **The chart components of a symmetric section are symmetric in the two frame slots.**  `D.mat`
evaluates the section on the *same* point of `M` in both slots (in the `g₀`-orthonormal frame
`D.e i`), so exchanging the two face indices is exactly the pointwise symmetry of the section. -/
lemma B3Data.R_swap_of_isSymm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.IsSymm (I := I) h)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    D.R i h a b = D.R i h b a := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat]
  rw [hh (D.pt i z) (D.e i a (D.pt i z)) (D.e i b (D.pt i z))]

/-- **The Friedrichs truncation of a smooth function supported in the open unit cube is smooth.**
`Work.Diff.STE.B3Data.STruncR ρ ε f` is the real part of the complex truncation `STruncC ρ ε f`
(`Work.Diff.STE.B3.STruncC_contDiff_periodic`), and taking the real part preserves smoothness. -/
lemma contDiff_STruncR_of_support
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfsupp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => Work.Diff.STE.B3Data.STruncR ρ ε f z) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (⇑Complex.reCLM ∘ (Work.Diff.STE.STruncC ρ ε f : (Fin (Module.finrank ℝ E) → ℝ) → ℂ)) :=
    (Complex.reCLM.contDiff).comp
      ((Work.Diff.STE.B3.STruncC_contDiff_periodic ρ hρ ε f hf hfsupp).1)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z => (Work.Diff.STE.STruncC ρ ε f z).re) := by
    convert h1 using 1
    funext z
    rfl
  simpa only [Work.Diff.STE.B3Data.STruncR, Work.Diff.STE.STruncC, Complex.ofReal_re] using h2

/-- **The Friedrichs mollifier of a symmetric section is symmetric.**  `J ρ ε h` is the sum of the
reconstructions `R_i*(S_ε (R_i h))`; a reconstruction is symmetric as soon as its coefficient
family is symmetric in the two slots (`Work.Diff.STE.D.Rstar_symm`), and the truncated components
of a symmetric section are symmetric (`B3Data.R_swap_of_isSymm`). -/
lemma isSymm_J_props
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.IsSymm (I := I) h) :
    Work.Diff.STE.D.IsSymm (I := I) (D.J ρ ε h) := by
  have hswap : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)), D.R i h a b = D.R i h b a :=
    fun i a b => B3Data.R_swap_of_isSymm D h hh i a b
  have hJ : D.J ρ ε h = ∑ i : ι₀, D.Rstar i (fun a b z =>
      Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z) := rfl
  rw [hJ]
  intro p X Y
  simp only [Finset.sum_apply, sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Work.Diff.STE.D.Rstar_symm (I := I) (M := M) D i _
    (fun a b z => by rw [hswap i a b]) p X Y

/-- **The Friedrichs mollifier of a section with smooth chart data has smooth chart data.**
`J ρ ε h = Σ_i R_i*(S_ε (R_i h))`; the reconstruction `R_i* u` has smooth chart data as soon as
every component `u a b` is `C^∞` (`Work.Diff.STE.D.ChartData_Rstar`), and here
`u a b = STruncR ρ ε (R_i h a b)` is smooth by `contDiff_STruncR_of_support`, the components
`R_i h a b` being smooth (`Work.Diff.STE.B3.R_contDiff_of_chartData`) and supported in the open cube
(`Work.Diff.STE.B3.R_support_cube`). -/
lemma chartData_J_props
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) :
    Work.Diff.STE.D.ChartData (I := I) (M := M) (D.J ρ ε h) := by
  refine Work.Diff.STE.D.GenMap.chartData_finset_sum (I := I) (M := M) Finset.univ
    (fun i : ι₀ => D.Rstar i (fun a b z =>
      Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z)) (fun i _ => ?_)
  refine Work.Diff.STE.D.ChartData_Rstar (I := I) (M := M) D i _ (fun a b => ?_)
  exact contDiff_STruncR_of_support ρ hρ ε (D.R i h a b)
    (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hh i a b)
    (Work.Diff.STE.B3.R_support_cube (I := I) (M := M) D h i a b)

theorem galState_J_props
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (hρ : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Work.Diff.STE.D.IsSymm (I := I)
        (Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c))
      ∧ Work.Diff.STE.D.ChartData (I := I) (M := M)
        (Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c))
      ∧ Work.Diff.STE.D.IsSymm (I := I)
        (D.J ρ ε (Work.Diff.STE.D.addSec (I := I) g₀
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)))
      ∧ Work.Diff.STE.D.ChartData (I := I) (M := M)
        (D.J ρ ε (Work.Diff.STE.D.addSec (I := I) g₀
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c))) := by
  have hZsym : Work.Diff.STE.D.IsSymm (I := I) (Work.Diff.STE.D.addSec (I := I) g₀
      (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)) :=
    Work.Diff.STE.D.isSymm_addSec_genMap (I := I) (M := M) (ι₀ := ι₀) (g₀ := g₀) D ε c
  have hZsm : Work.Diff.STE.D.ChartData (I := I) (M := M) (Work.Diff.STE.D.addSec (I := I) g₀
      (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)) :=
    Work.Diff.STE.D.chartData_addSec_genMap (I := I) (M := M) (ι₀ := ι₀) (g₀ := g₀) D ε c hg
  exact ⟨hZsym, hZsm,
    isSymm_J_props (I := I) (M := M) D ρ ε _ hZsym,
    chartData_J_props (I := I) (M := M) D ρ hρ ε _ hZsm⟩

end Work.Diff.STE.Lead
