import Mathlib
import Submission.Diff.STEGal
import Submission.Work.Diff.STE.D.ODE
import Submission.Work.Diff.STE.D.ChartData_genMap
import Submission.Work.Diff.STE.D.genMap_galVF
import Submission.Work.Diff.STE.D.GalODE
import Submission.Work.Diff.STE.D.Galerkin
import Submission.Work.Diff.STE.D.isSymm_genMap
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The span-form Galerkin scheme of the uniform-existence lemma `GalUniform`

`GalUniform` (`Submission/Diff/STEGal.lean`) asks, for every sufficiently small `ε`, for a solution
`c` of the **span Galerkin ODE**

  `u' = J ρ ε (P (J ρ ε u))`,   `u(t) = g₀.inner + genMap D ε (c t)`,

on a common interval `[0, τ₀]`, with `ε`-uniform `BNorm` bounds at every level and a uniform
positivity margin.  This module fixes the vocabulary of the *reduction* used by the target file
`Work.Diff.STE.Lead.gal_uniform_v2`.

The key structural facts (all elementary, and independent of `ε`):

* `galCoeff D ρ ε h = (1/2) • jFamilyCoeff ρ ε h` is the Galerkin coefficient family of the
  mollifier: for a **symmetric** section `h`, `D.J ρ ε h = genMap D ε (galCoeff D ρ ε h)`
  (`J_eq_genMap_galCoeff`, from `J_eq_sum_index` + `genMap_div_two_eq_sum`).  In particular the
  mollifier of a symmetric section is symmetric and has smooth chart data (`isSymm_J`,
  `chartData_J`), which is what makes the *foreground* section
  `u~(c) := J ρ ε (galState D ε c)` of the `u' = J P (J u)` scheme a legitimate metric argument for
  the DeTurck operator.
* `galVF2 hLC D ρ ε c` is the **span-form Galerkin vector field**: a *total* function on the
  coefficient space, equal on the positivity region of `u~(c)` to `galCoeff` of the DeTurck tensor
  `P (u~(c))`, and `0` outside.  Its defining property is
  `genMap D ε (galVF2 c) = D.J ρ ε (P (u~(c)))` (`genMap_galVF2`), i.e. the coefficient ODE
  `c' = galVF2 c` *is* the Galerkin approximant `u' = J ρ ε (P (J ρ ε u))`.
* `galE D k ε c = ENormB k (galState D ε c) + ENormB 0 (galState D ε c)` is the **energy** on which
  the Layer D2 a priori estimate is run.
-/

namespace Work.Diff.STE.Lead

open Classical LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

/-! ## The Galerkin coefficients and the mollifier as `genMap` of them -/

/-- **The Galerkin coefficient family** of the Friedrichs mollifier: half of the Fourier-coefficient
family of `h` in the family `jFamily D ε`.  For symmetric `h` the identity
`D.J ρ ε h = genMap D ε (galCoeff D ρ ε h)` holds (`J_eq_genMap_galCoeff`): the factor `1/2` is the
symmetrisation factor of `genMap` (whose spanning family is `jSym = jFamily + transpose`). -/
def galCoeff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) :
    Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ :=
  fun z => (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε h z

/-- **The mollifier of a symmetric section is `genMap` of its Galerkin coefficients.** -/
lemma J_eq_genMap_galCoeff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : Work.Diff.STE.D.IsSymm (I := I) h) :
    D.J ρ ε h = Work.Diff.STE.D.genMap (I := I) (M := M) D ε (galCoeff D ρ ε h) := by
  have hC : ∀ z, Work.Diff.STE.B3.jFamilyCoeff D ρ ε h
        (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z)
      = Work.Diff.STE.B3.jFamilyCoeff D ρ ε h z :=
    fun z => Work.Diff.STE.D.jFamilyCoeff_idxSwap D ρ ε h hsym z
  have hhalf : galCoeff D ρ ε h
      = (fun z => Work.Diff.STE.B3.jFamilyCoeff D ρ ε h z / 2) := by
    funext z; simp only [galCoeff]; ring
  rw [hhalf, Work.Diff.STE.D.genMap_div_two_eq_sum D ε _ hC]
  exact Work.Diff.STE.B3.J_eq_sum_index D ρ ε hε hρ0 h

/-- The mollifier of a symmetric section is symmetric. -/
lemma isSymm_J (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : Work.Diff.STE.D.IsSymm (I := I) h) :
    Work.Diff.STE.D.IsSymm (I := I) (D.J ρ ε h) := by
  rw [J_eq_genMap_galCoeff D ρ ε hε hρ0 h hsym]
  exact Work.Diff.STE.D.isSymm_genMap (I := I) (M := M) D ε (galCoeff D ρ ε h)

/-- The mollifier of a symmetric section has smooth chart data. -/
lemma chartData_J (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : Work.Diff.STE.D.IsSymm (I := I) h) :
    Work.Diff.STE.D.ChartData (I := I) (M := M) (D.J ρ ε h) := by
  rw [J_eq_genMap_galCoeff D ρ ε hε hρ0 h hsym]
  exact Work.Diff.STE.D.ChartData_genMap (I := I) (M := M) D ε (galCoeff D ρ ε h)

/-- The `galState` of a coefficient vector is symmetric. -/
lemma isSymm_galState (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Work.Diff.STE.D.IsSymm (I := I) (galState D ε c) :=
  Work.Diff.STE.D.isSymm_addSec_genMap (I := I) (M := M) D ε c

/-- The `galState` of a coefficient vector has smooth chart data. -/
lemma chartData_galState (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner))
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Work.Diff.STE.D.ChartData (I := I) (M := M) (galState D ε c) :=
  Work.Diff.STE.D.chartData_addSec_genMap (I := I) (M := M) D ε c hg

/-! ## The span-form Galerkin vector field -/

/-- **The span-form Galerkin vector field** of the scheme `u' = J ρ ε (P (J ρ ε u))`: a *total*
function on the coefficient space, equal on the positivity region of the foreground
`u~(c) = J ρ ε (galState D ε c)` to the Galerkin coefficients of the DeTurck tensor `P (u~(c))`, and
`0` outside.  (`Work.Diff.STE.D.psi` is the corresponding field of the *affine* scheme
`u' = J ρ ε (P u)`.) -/
def galVF2 (hLC : LCSmooth I M) (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ :=
  if hpos : (∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (D.J ρ ε (galState D ε c)) x v v) then
    galCoeff D ρ ε (Work.Diff.STE.D.deTurckSec hLC g₀ (D.J ρ ε (galState D ε c))
      (isSymm_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c))
      hpos
      (chartData_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)))
  else 0

/-- On the positivity region, `galVF2` is the honest Galerkin coefficient field of the DeTurck
tensor of the foreground. -/
lemma galVF2_of_pos (hLC : LCSmooth I M) (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (D.J ρ ε (galState D ε c)) x v v) :
    galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 c =
      galCoeff D ρ ε (Work.Diff.STE.D.deTurckSec hLC g₀ (D.J ρ ε (galState D ε c))
        (isSymm_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c))
        hpos
        (chartData_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c))) :=
  dite_eq_left hpos

/-- **The defining property of the span-form field**: applying `genMap D ε` to `galVF2 c` gives the
Friedrichs mollifier of the DeTurck tensor of the foreground `J ρ ε (galState D ε c)`. -/
lemma genMap_galVF2 (hLC : LCSmooth I M) (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (D.J ρ ε (galState D ε c)) x v v) :
    Work.Diff.STE.D.genMap (I := I) (M := M) D ε (galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 c)
      = D.J ρ ε (Work.Diff.STE.D.deTurckSec hLC g₀ (D.J ρ ε (galState D ε c))
          (isSymm_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)) hpos
          (chartData_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c))) := by
  rw [galVF2_of_pos (I := I) (M := M) hLC D ρ ε hε hρ0 c hpos]
  exact (J_eq_genMap_galCoeff D ρ ε hε hρ0 _ (Work.Diff.STE.D.deTurckSec_symm (g₀ := g₀) hLC
    (D.J ρ ε (galState D ε c)) (isSymm_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c))
    hpos (chartData_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)))).symm

/-- **The pointwise chain rule for `galState`**: a differentiable family of coefficient vectors
gives a differentiable family of sections, with derivative transported by `genMap` (linearity of
`genMap D ε` in the coefficients, with `g₀` constant). -/
lemma hasDerivAt_galState (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    {c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)}
    {c' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ} {t : ℝ}
    (h : HasDerivAt c c' t) :
    ∀ (x : M) (u v : TangentSpace I x),
      HasDerivAt (fun s => galState D ε (c s) x u v)
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c' x u v) t := by
  intro x u v
  have h1 : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      HasDerivAt
        (fun s => (c s) z * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v))
        ((c' z) * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v)) t :=
    fun z => (((ContinuousLinearMap.proj z).hasFDerivAt).comp_hasDerivAt t h)
      |>.mul_const (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v)
  have h2 := HasDerivAt.sum (u := Finset.univ) (fun z _ => h1 z)
  have h3 : HasDerivAt
      (fun s => ∑ z, (c s) z * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v))
      (∑ z, (c' z) * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v)) t :=
    h2.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by rw [Finset.sum_apply])
  have h4 : HasDerivAt
      (fun s => g₀.inner x u v + ∑ z, (c s) z * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v))
      (∑ z, (c' z) * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v)) t :=
    h3.const_add (g₀.inner x u v)
  simpa only [galState, Work.Diff.STE.D.addSec_apply, Work.Diff.STE.D.genMap,
    Finset.sum_apply, sum_apply, Pi.smul_apply, smul_apply, smul_eq_mul] using h4

/-! ## The energy of the span-form scheme -/

/-- **The energy of the scheme `u' = J ρ ε (P (J ρ ε u))`**: the physical `Hᵏ` energy of the metric
`galState D ε c = g₀.inner + genMap D ε c`, together with its `L²` part (the `ENormSq` seminorms are
homogeneous, so the `0`-level term is needed for the positivity/margin persistence). -/
def galE (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) : ℝ :=
  D.ENormB k (galState D ε c) + D.ENormB 0 (galState D ε c)

end

end Work.Diff.STE.Lead
