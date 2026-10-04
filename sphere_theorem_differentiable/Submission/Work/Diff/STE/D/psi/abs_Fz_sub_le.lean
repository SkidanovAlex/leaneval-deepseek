/-
# Layer D: the second order Taylor estimate for the localised component `Fz`

The localised component of the Galerkin chart section is

  `Fz z c y = ψ z.1 y · √(dens z.1 y) · secChart g₀ (g₀ + genMap D ε c) (x₀ z.1) z.2.1 z.2.2.1 y`,

and the target of this file is the *second order* Taylor estimate

  `|Fz z c y - Fz z c₀ y - Σ_{z'} (c z' - c₀ z') · Ufun z z' c₀ y| ≤ C · ‖c - c₀‖^2`

uniformly in `y`, with `C` depending only on the data.

## The proof

`Fz` is the weight `ψ z.1 y · √(dens z.1 y)` times the weight functional `LamFun D ε z y` (the
contraction of the matrix of the chart DeTurck operator with the coordinates of the two frame
vectors `e z.1 z.2.1`, `e z.1 z.2.2.1`) applied to the pair of `2`-jets of the metric.  The pair of
jets is *affine* in the coefficients `c`, so the second order Taylor estimate for `Fz` in `c` is the
second order Taylor estimate for the composite

  `FzPhi (c, y) = pPhiFun (jetPairOf g₀ D ε x₀ c (flatToE x₀ y))`

of the chart DeTurck operator with the affine jet pair, on the product of the coefficient space and
the flat coordinate space, in the direction `h = (c - c₀, 0)`.

`FzPhi` is `C^∞` on the open set `FzDom` (the coefficient smallness being exactly the positivity of
the perturbed section, so that the pair of jets lies in the smoothness locus `pPhiDom` of `pPhi`),
so the Taylor theorem on a compact set (`Work.Diff.Calc.taylor_bound_on_compact`, applied to
`closedBall 0 (δp/2) ×ˢ closedBall 0 (σ z.1)`) produces `δ`, `M` with

  `‖FzPhi x h - FzPhi x - fderiv FzPhi x h‖ ≤ M ‖h‖^2`,

and it remains to

* identify the derivative `fderiv FzPhi (c₀,y) (c - c₀, 0)` with the sum of linearisations
  `Σ_z' (c z' - c₀ z') · pPhiFunD (jetPairOf … c₀ (flatToE y)) (jetDir z' (flatToE y))`
  (`Fz_fderiv_Phi`, `FzJetLin_apply`),
* bound the weight `ψ·√dens` by `abs_pref_le` and the coordinate factors — on the compact region
  `FzKreg D z.1` where the weight can be nonzero — by `Fz_coord_factor_le`,
* and handle the (trivial) case in which the weight `ψ z.1` vanishes identically.
-/
import Mathlib
import Submission.Work.Diff.STE.D.psi.Core
import Submission.Work.Diff.STE.D.psi.Positivity
import Submission.Work.Diff.STE.D.psi.chartJetOf_genMap_affine
import Submission.Work.Diff.STE.D.psi.chartJetOf_jSym_bound
import Submission.Work.Diff.STE.D.psi.contDiffOn_secChartVal_chart
import Submission.Work.Diff.STE.D.psi.chartMatOf_pd_det_pos
import Submission.Work.Diff.STE.D.psi.abs_pref_le
import Submission.Work.Diff.Calc.taylor_bound_on_compact
import Submission.Work.Diff.STE.deTurck.posDef_gmat
import Submission.Work.Diff.STE.B3.CompSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D.psi

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M} {ε : ℝ}

noncomputable section

/-! ## 0. Vocabulary and instance support -/

/-- The coefficient space of the Galerkin scheme. -/
abbrev FzCoef (ι₀ : Type*) [Fintype ι₀] (n : ℕ) (ε : ℝ) : Type _ :=
  Work.Diff.STE.B3.JIdx ι₀ n ε → ℝ

/-- The flat coordinate space. -/
abbrev FzFlat (n : ℕ) : Type _ := Fin n → ℝ

/-- The "twice nested" continuous linear map space. -/
abbrev FzBil (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Type _ :=
  E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E)

/-- The triple of `2`-jet components. -/
abbrev FzTri (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Type _ :=
  Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E × FzBil (E := E)

/-- `ℝ` acts boundedly on the space of *twice* nested continuous linear maps; this instance is not
found by type class search on its own.  It is `local` so as not to perturb the instance space of
the rest of the development. -/
local instance fzBilSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E)) :=
  IsBoundedSMul.of_norm_smul_le fun r L => ContinuousLinearMap.opNorm_smul_le r L

/-- Addition is continuous on the space of twice nested continuous linear maps. -/
local instance fzBilCAdd : ContinuousAdd (E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E)) :=
  ⟨(inferInstance : IsTopologicalAddGroup
    (E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E))).continuous_add⟩

/-- The jet space carries its canonical module and normed space structures. -/
local instance fzModuleJetPair : Module ℝ (Work.Diff.STE.deTurck.JetPair (E := E)) :=
  inferInstance

local instance fzNormAddJetPair : NormedAddCommGroup (Work.Diff.STE.deTurck.JetPair (E := E)) :=
  inferInstance

local instance fzNormSpaceJetPair : NormedSpace ℝ (Work.Diff.STE.deTurck.JetPair (E := E)) :=
  inferInstance

/-! ## 1. The components of the chart `2`-jet and the affine family -/

/-- The `MatE` component of the chart `2`-jet of a section. -/
noncomputable def FzA0 (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M) (y : E) :
    Work.Diff.EXT.MatE (E := E) :=
  (chartJetOf (I := I) (M := M) h x₀ y).1

/-- The first jet component of the chart `2`-jet of a section. -/
noncomputable def FzL0 (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M) (y : E) :
    Work.Diff.STE.DeTurck.LinMat E :=
  (chartJetOf (I := I) (M := M) h x₀ y).2.1

/-- The second jet component of the chart `2`-jet of a section. -/
noncomputable def FzB0 (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M) (y : E) :
    FzBil (E := E) :=
  (chartJetOf (I := I) (M := M) h x₀ y).2.2

/-- The chart `2`-jet of a section is the triple of its components. -/
lemma Fz_chartJetOf_eta (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M) (y : E) :
    chartJetOf (I := I) (M := M) h x₀ y =
      (FzA0 (I := I) (M := M) h x₀ y,
        (FzL0 (I := I) (M := M) h x₀ y, FzB0 (I := I) (M := M) h x₀ y)) := rfl

/-- Scalar multiples of the zero twice-nested linear map vanish. -/
lemma fz_smul_zero_bil (c : ℝ) : c • (0 : FzBil (E := E)) = 0 := by
  ext v w i j
  simp

/-- Scalar multiples of the zero jet triple vanish. -/
lemma fz_smul_zero_tri (c : ℝ) : c • (0 : FzTri (E := E)) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show c • (0 : Work.Diff.EXT.MatE (E := E)) = 0
    exact smul_zero c
  · show c • (0 : Work.Diff.STE.DeTurck.LinMat E) = 0
    exact smul_zero c
  · simpa only [Prod.snd_zero, Prod.smul_snd] using fz_smul_zero_bil (E := E) c

/-- The `MatE` component of the chart `2`-jet of the affine family. -/
noncomputable def FzAffA (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) (y : E) : Work.Diff.EXT.MatE (E := E) :=
  FzA0 (I := I) (M := M) g₀.inner x₀ y
    + ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        c z • FzA0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀ y

/-- The first jet component of the chart `2`-jet of the affine family. -/
noncomputable def FzAffL (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) (y : E) : Work.Diff.STE.DeTurck.LinMat E :=
  FzL0 (I := I) (M := M) g₀.inner x₀ y
    + ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        c z • FzL0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀ y

/-- The second jet component of the chart `2`-jet of the affine family. -/
noncomputable def FzAffB (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) (y : E) : FzBil (E := E) :=
  FzB0 (I := I) (M := M) g₀.inner x₀ y
    + ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        c z • FzB0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀ y

/-- The second component of the pair of `2`-jets of the affine family. -/
noncomputable def FzAff3 (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) (y : E) : FzTri (E := E) :=
  (FzAffA (I := I) (M := M) g₀ D ε x₀ c y,
   (FzAffL (I := I) (M := M) g₀ D ε x₀ c y,
    FzAffB (I := I) (M := M) g₀ D ε x₀ c y))

/-- **The pair of `2`-jets of the affine family**, in explicit component form. -/
noncomputable def FzJetAff (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) (y : E) :
    Work.Diff.STE.deTurck.JetPair (E := E) :=
  ((FzA0 (I := I) (M := M) g₀.inner x₀ y,
   (FzL0 (I := I) (M := M) g₀.inner x₀ y, FzB0 (I := I) (M := M) g₀.inner x₀ y)),
   FzAff3 (I := I) (M := M) g₀ D ε x₀ c y)

/-- The `MatE` component of the affine family's jet is the first component of the chart jet. -/
lemma FzAffA_eq {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    FzAffA (I := I) (M := M) g₀ D ε x₀ c y =
      (chartJetOf (I := I) (M := M)
        (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) x₀ y).1 := by
  have h := chartJetOf_genMap_affine (I := I) (M := M) hg D ε x₀ c hy
  rw [FzAffA, h]
  simp only [FzA0, Prod.fst_add, Prod.fst_sum, Prod.smul_fst]

/-- The first jet component of the affine family's jet is the first jet component of the chart
jet. -/
lemma FzAffL_eq {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    FzAffL (I := I) (M := M) g₀ D ε x₀ c y =
      (chartJetOf (I := I) (M := M)
        (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) x₀ y).2.1 := by
  have h := chartJetOf_genMap_affine (I := I) (M := M) hg D ε x₀ c hy
  rw [FzAffL, h]
  simp only [FzL0, Prod.fst_add, Prod.fst_sum, Prod.smul_fst, Prod.snd_add, Prod.snd_sum,
    Prod.smul_snd]

/-- The second jet component of the affine family's jet is the second jet component of the chart
jet. -/
lemma FzAffB_eq {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    FzAffB (I := I) (M := M) g₀ D ε x₀ c y =
      (chartJetOf (I := I) (M := M)
        (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) x₀ y).2.2 := by
  have h := chartJetOf_genMap_affine (I := I) (M := M) hg D ε x₀ c hy
  rw [FzAffB, h]
  simp only [FzB0, Prod.fst_add, Prod.fst_sum, Prod.smul_fst, Prod.snd_add, Prod.snd_sum,
    Prod.smul_snd]

/-- **The affine form is the jet pair of the affine family.** -/
lemma FzJetAff_eq {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    FzJetAff (I := I) (M := M) g₀ D ε x₀ c y =
      jetPairOf (I := I) (M := M) g₀ D ε x₀ c y := by
  rw [Work.Diff.STE.D.jetPairOf, FzJetAff, Fz_chartJetOf_eta (I := I) (M := M)
    (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) x₀ y]
  refine Prod.ext (Prod.ext rfl (Prod.ext rfl rfl)) ?_
  refine Prod.ext ?_ ?_
  · exact FzAffA_eq (I := I) (M := M) hg D ε x₀ c hy
  · refine Prod.ext ?_ ?_
    · exact FzAffL_eq (I := I) (M := M) hg D ε x₀ c hy
    · exact FzAffB_eq (I := I) (M := M) hg D ε x₀ c hy

/-! ## 2. Smoothness of the affine jet pair -/

/-- **The affine jet pair is `C^∞`** on the set of coefficient vectors and flat coordinates whose
chart image lies in the target of the chart at `x₀`. -/
lemma contDiffOn_FzJetAff {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) =>
        FzJetAff (I := I) (M := M) g₀ D ε x₀ q.1 (flatToE (I := I) x₀ q.2))
      {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
        flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} := by
  classical
  have hflat : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) =>
        flatToE (I := I) x₀ q.2)
      {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
        flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    (Work.Diff.STE.contDiff_flatToE (I := I) x₀).comp_contDiffOn contDiffOn_snd
  have hA0 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) =>
        FzA0 (I := I) (M := M) g₀.inner x₀ (flatToE (I := I) x₀ q.2))
      {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
        flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    (contDiffOn_chartJetOf (I := I) (M := M) g₀.inner x₀ (hg x₀)).fst.comp hflat (fun _ hq => hq)
  have hL0 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) =>
        FzL0 (I := I) (M := M) g₀.inner x₀ (flatToE (I := I) x₀ q.2))
      {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
        flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    (contDiffOn_chartJetOf (I := I) (M := M) g₀.inner x₀ (hg x₀)).snd.fst.comp hflat
      (fun _ hq => hq)
  have hB0 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) =>
        FzB0 (I := I) (M := M) g₀.inner x₀ (flatToE (I := I) x₀ q.2))
      {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
        flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    (contDiffOn_chartJetOf (I := I) (M := M) g₀.inner x₀ (hg x₀)).snd.snd.comp hflat
      (fun _ hq => hq)
  have hAz : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) =>
          FzA0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀
            (flatToE (I := I) x₀ q.2))
        {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
          flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    fun z => (contDiffOn_chartJetOf (I := I) (M := M)
      (jSym (I := I) (M := M) D ε z) x₀ (jSym_chartData (I := I) (M := M) D ε z x₀)).fst.comp
        hflat (fun _ hq => hq)
  have hLz : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) =>
          FzL0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀
            (flatToE (I := I) x₀ q.2))
        {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
          flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    fun z => (contDiffOn_chartJetOf (I := I) (M := M)
      (jSym (I := I) (M := M) D ε z) x₀ (jSym_chartData (I := I) (M := M) D ε z x₀)).snd.fst.comp
        hflat (fun _ hq => hq)
  have hBz : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) =>
          FzB0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀
            (flatToE (I := I) x₀ q.2))
        {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
          flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    fun z => (contDiffOn_chartJetOf (I := I) (M := M)
      (jSym (I := I) (M := M) D ε z) x₀ (jSym_chartData (I := I) (M := M) D ε z x₀)).snd.snd.comp
        hflat (fun _ hq => hq)
  have hcz : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) => q.1 z)
        {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
          flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    fun z => ((ContinuousLinearMap.proj (R := ℝ) z).comp
      (ContinuousLinearMap.fst ℝ (FzCoef ι₀ (Module.finrank ℝ E) ε)
        (FzFlat (Module.finrank ℝ E)))).contDiff.contDiffOn
  have hsumA : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) =>
        ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          q.1 z • FzA0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀
            (flatToE (I := I) x₀ q.2))
      {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
        flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} := by
    have h := ContDiffOn.sum (s := Finset.univ)
      (t := {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
        flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target})
      (f := fun z q => q.1 z • FzA0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀
        (flatToE (I := I) x₀ q.2))
      (fun z _ => (hcz z).smul (hAz z))
    simpa using h
  have hsumL : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) =>
        ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          q.1 z • FzL0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀
            (flatToE (I := I) x₀ q.2))
      {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
        flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} := by
    have h := ContDiffOn.sum (s := Finset.univ)
      (t := {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
        flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target})
      (f := fun z q => q.1 z • FzL0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀
        (flatToE (I := I) x₀ q.2))
      (fun z _ => (hcz z).smul (hLz z))
    simpa using h
  have hsumB : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) =>
        ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          q.1 z • FzB0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀
            (flatToE (I := I) x₀ q.2))
      {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
        flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} := by
    have h := ContDiffOn.sum (s := Finset.univ)
      (t := {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
        flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target})
      (f := fun z q => q.1 z • FzB0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀
        (flatToE (I := I) x₀ q.2))
      (fun z _ => (hcz z).smul (hBz z))
    simpa using h
  refine ContDiffOn.congr ?_ (fun q _ => rfl)
  refine ContDiffOn.prodMk (ContDiffOn.prodMk hA0 (ContDiffOn.prodMk hL0 hB0)) ?_
  exact ContDiffOn.prodMk (hA0.add hsumA) (ContDiffOn.prodMk (hL0.add hsumL) (hB0.add hsumB))

/-- **The joint jet pair of the Galerkin family is `C^∞`** on the set of coefficient vectors and
flat coordinates for which the flat point stays inside the target of the chart at `x₀`. -/
lemma contDiffOn_joint_jetPairOf_Fz {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) =>
        jetPairOf (I := I) (M := M) g₀ D ε x₀ q.1 (flatToE (I := I) x₀ q.2))
      {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
        flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
  (contDiffOn_FzJetAff (I := I) (M := M) hg D ε x₀).congr
    (fun q hq => (FzJetAff_eq (I := I) (M := M) hg D ε x₀ q.1 hq).symm)

/-! ## 3. The compact region of the localised weight and the coordinate bounds -/

/-- **The region in which the localised weight `ψ i` can be nonzero**: the closed flat ball of
radius `σ i` intersected with the topological support of the cut-off `χ i`. -/
def FzKreg (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    Set (FzFlat (Module.finrank ℝ E)) :=
  Metric.closedBall 0 (D.σ i) ∩ tsupport (D.χ i)

/-- The region `FzKreg D i` is compact. -/
lemma isCompact_FzKreg (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    IsCompact (FzKreg (I := I) (M := M) D i) :=
  (isCompact_closedBall (0 : FzFlat (Module.finrank ℝ E)) (D.σ i)).of_isClosed_subset
    (isClosed_closedBall.inter (isClosed_tsupport (D.χ i))) Set.inter_subset_left

/-- Membership in `FzKreg` from the nonvanishing of the localised weight. -/
lemma mem_FzKreg_of_psi_ne_zero (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) {i : ι₀}
    {y : FzFlat (Module.finrank ℝ E)} (h : D.psi i y ≠ 0) :
    y ∈ FzKreg (I := I) (M := M) D i := by
  refine ⟨?_, subset_closure (fun h0 => h (by simp only [Work.Diff.STE.B3Data.psi, h0, zero_mul]))⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_lt (Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero (I := I) (M := M) D h)

/-- The flat coordinate of the members of `FzKreg` is bounded by `σ i`. -/
lemma norm_le_sigma_of_mem_FzKreg (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) {i : ι₀}
    {y : FzFlat (Module.finrank ℝ E)} (h : y ∈ FzKreg (I := I) (M := M) D i) :
    ‖y‖ ≤ D.σ i := by
  rw [← dist_zero_right, ← Metric.mem_closedBall]
  exact h.1

/-- On `FzKreg D i` the chart is genuine. -/
lemma flatToE_mem_target_of_mem_FzKreg (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    {i : ι₀} {y : FzFlat (Module.finrank ℝ E)} (h : y ∈ FzKreg (I := I) (M := M) D i) :
    flatToE (I := I) (D.x₀ i) y ∈ (extChartAt I (D.x₀ i)).target :=
  D.hχtsup i y h.2

/-- **The coordinates of the frame vectors are bounded on the compact region of the weight.** -/
theorem Fz_coord_factor_le (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (a : Fin (Module.finrank ℝ E)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ FzKreg (I := I) (M := M) D i,
      ∀ j : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
          (D.e i a (D.pt i y))| ≤ B := by
  classical
  have hZ : Work.Diff.GE.SmoothField M (D.e i a) := D.hesm i a
  have hcd : ∀ j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun Y : E =>
        Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i)
          ((extChartAt I (D.x₀ i)).symm Y) j (D.e i a ((extChartAt I (D.x₀ i)).symm Y)))
        (extChartAt I (D.x₀ i)).target :=
    fun j => (contDiffOn_coordCLM_symm (I := I) (M := M) (D.x₀ i) hZ j).continuousOn
  have hK : IsCompact (FzKreg (I := I) (M := M) D i) := isCompact_FzKreg (I := I) (M := M) D i
  have hflat : Continuous (flatToE (I := I) (D.x₀ i)) :=
    (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ i)).continuous
  have hcomp : ContinuousOn (fun y : FzFlat (Module.finrank ℝ E) =>
      fun j : Fin (Module.finrank ℝ E) =>
        Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
          (D.e i a (D.pt i y)))
      (FzKreg (I := I) (M := M) D i) :=
    continuousOn_pi.2 fun j =>
      (hcd j).comp hflat.continuousOn
        (fun y hy => flatToE_mem_target_of_mem_FzKreg (I := I) (M := M) D hy)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcomp
  refine ⟨max 0 C, le_max_left 0 C, fun y hy j => ?_⟩
  have h1 : ‖(fun j : Fin (Module.finrank ℝ E) =>
      Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
        (D.e i a (D.pt i y)))‖ ≤ C := hC y hy
  calc |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
          (D.e i a (D.pt i y))|
      = ‖Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
          (D.e i a (D.pt i y))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖(fun j : Fin (Module.finrank ℝ E) =>
          Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
            (D.e i a (D.pt i y)))‖ :=
        norm_le_pi_norm (fun j : Fin (Module.finrank ℝ E) =>
          Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
            (D.e i a (D.pt i y))) j
    _ ≤ C := h1
    _ ≤ max 0 C := le_max_right 0 C

/-! ## 4. The positivity ball, the smoothness locus of `pPhi`, and the joint expression -/

/-- **The positivity set of the Galerkin perturbation contains a ball around zero.** -/
lemma exists_isPos_ball (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : FzCoef ι₀ (Module.finrank ℝ E) ε,
      ‖c‖ < δ → Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c := by
  have h : {c : FzCoef ι₀ (Module.finrank ℝ E) ε |
      Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c} ∈
      𝓝 (0 : FzCoef ι₀ (Module.finrank ℝ E) ε) :=
    Work.Diff.STE.D.eventually_posDef (I := I) (M := M) D ε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨δ, hδ, fun c hc => hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  exact hc

/-- The smoothness locus of the chart DeTurck operator is open. -/
lemma isOpen_pPhiDom_Fz : IsOpen (Work.Diff.STE.deTurck.pPhiDom (E := E)) := by
  have h1 : Continuous fun w : Work.Diff.STE.deTurck.JetPair (E := E) =>
      (Matrix.of w.1.1).det :=
    Continuous.matrix_det (by fun_prop)
  have h2 : Continuous fun w : Work.Diff.STE.deTurck.JetPair (E := E) =>
      (Matrix.of w.2.1).det :=
    Continuous.matrix_det (by fun_prop)
  exact (isOpen_ne.preimage h1).inter (isOpen_ne.preimage h2)

/-- **The chart DeTurck operator is differentiable on its smoothness locus**, with derivative the
explicit linearisation `pPhiFunD`. -/
lemma hasFDerivAt_pPhiFun_Fz (w : Work.Diff.STE.deTurck.JetPair (E := E))
    (hw : w ∈ Work.Diff.STE.deTurck.pPhiDom (E := E)) :
    HasFDerivAt (Work.Diff.STE.D.pPhiFun (E := E))
      (Work.Diff.STE.D.pPhiFunD (E := E) w) w := by
  have h : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.pPhiFun (E := E)) w :=
    (Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E)).contDiffAt
      (isOpen_pPhiDom_Fz.mem_nhds hw)
  exact (h.differentiableAt (by simp)).hasFDerivAt

/-- The joint chart DeTurck expression: `pPhiFun` composed with the pair of jets. -/
noncomputable def FzPhi (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) →
      Work.Diff.EXT.MatE (E := E) :=
  fun q => Work.Diff.STE.D.pPhiFun (E := E)
    (jetPairOf (I := I) (M := M) g₀ D ε x₀ q.1 (flatToE (I := I) x₀ q.2))

/-- The domain of the joint chart DeTurck expression. -/
def FzDom (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    Set (FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E)) :=
  {q | flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} ∩
    (fun q => jetPairOf (I := I) (M := M) g₀ D ε x₀ q.1 (flatToE (I := I) x₀ q.2)) ⁻¹'
      Work.Diff.STE.deTurck.pPhiDom (E := E)

/-- The background component of the jet pair. -/
lemma Fz_jetPairOf_fst (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) (y : E) :
    (Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c y).1 =
      Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y := rfl

/-- The foreground component of the jet pair. -/
lemma Fz_jetPairOf_snd (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) (y : E) :
    (Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c y).2 =
      Work.Diff.STE.D.chartJetOf (I := I) (M := M)
        (Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c))
        x₀ y := rfl

/-- **On the positivity set the pair of jets lies in the smoothness locus of `pPhi`.** -/
lemma Fz_jet_mem_pPhiDom {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) {y : FzFlat (Module.finrank ℝ E)}
    (hpos : Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c)
    (hy : flatToE (I := I) x₀ y ∈ (extChartAt I x₀).target) :
    jetPairOf (I := I) (M := M) g₀ D ε x₀ c (flatToE (I := I) x₀ y)
      ∈ Work.Diff.STE.deTurck.pPhiDom (E := E) := by
  constructor
  · have hsrc : (extChartAt I x₀).symm (flatToE (I := I) x₀ y) ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I) x₀]
      exact PartialEquiv.map_target (extChartAt I x₀) hy
    have hpd : (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ x₀
        ((extChartAt I x₀).symm (flatToE (I := I) x₀ y)))).PosDef :=
      Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ x₀ hsrc
    rw [Fz_jetPairOf_fst (I := I) (M := M) g₀ D ε x₀ c (flatToE (I := I) x₀ y),
      Work.Diff.STE.D.psi.chartJetOf_fst_inner (I := I) (M := M)]
    exact ne_of_gt (Matrix.PosDef.det_pos hpd)
  · have hsymm : Work.Diff.STE.D.IsSymm (I := I)
        (Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)) :=
      Work.Diff.STE.D.isSymm_addSec (I := I) (ι₀ := ι₀) _
        (Work.Diff.STE.D.isSymm_genMap (I := I) (M := M) D ε c)
    have hpos' : ∀ (p : M) (v : TangentSpace I p), v ≠ 0 →
        0 < Work.Diff.STE.D.addSec (I := I) g₀
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c) p v v := hpos
    rw [Fz_jetPairOf_snd (I := I) (M := M) g₀ D ε x₀ c (flatToE (I := I) x₀ y),
      Work.Diff.STE.D.psi.chartJetOf_fst (I := I) (M := M)]
    exact ne_of_gt (Work.Diff.STE.D.psi.chartMatOf_det_pos_of_posDef (I := I) (M := M) _ x₀
      hsymm hpos' hy)

/-- **The joint chart DeTurck expression is smooth on its domain.** -/
lemma contDiffOn_FzPhi {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    ContDiffOn ℝ 2 (FzPhi (I := I) (M := M) g₀ D ε x₀) (FzDom (I := I) (M := M) g₀ D ε x₀) := by
  have hjet : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) =>
        jetPairOf (I := I) (M := M) g₀ D ε x₀ q.1 (flatToE (I := I) x₀ q.2))
      (FzDom (I := I) (M := M) g₀ D ε x₀) :=
    (contDiffOn_joint_jetPairOf_Fz (I := I) (M := M) hg D ε x₀).mono Set.inter_subset_left
  have hcomp := (Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E)).comp hjet
    (fun q hq => by
      rw [FzDom] at hq
      exact hq.2)
  exact hcomp.of_le (by simp)

/-- **The domain of the joint chart DeTurck expression is open.** -/
lemma isOpen_FzDom {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    IsOpen (FzDom (I := I) (M := M) g₀ D ε x₀) := by
  have hU : IsOpen {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
      flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    (isOpen_extChartAt_target (I := I) x₀).preimage
      (((Work.Diff.STE.contDiff_flatToE (I := I) x₀).comp contDiff_snd).continuous)
  rw [isOpen_iff_mem_nhds]
  intro q hq
  have hqU : q ∈ {q : FzCoef ι₀ (Module.finrank ℝ E) ε × FzFlat (Module.finrank ℝ E) |
      flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} := hq.1
  have hcont := contDiffOn_joint_jetPairOf_Fz (I := I) (M := M) hg D ε x₀
  have hc : ContinuousAt (fun q : FzCoef ι₀ (Module.finrank ℝ E) ε ×
      FzFlat (Module.finrank ℝ E) =>
      jetPairOf (I := I) (M := M) g₀ D ε x₀ q.1 (flatToE (I := I) x₀ q.2)) q :=
    hcont.continuousOn.continuousAt (hU.mem_nhds hqU)
  exact Filter.inter_mem (hU.mem_nhds hqU)
    (hc.preimage_mem_nhds ((isOpen_pPhiDom_Fz (E := E)).mem_nhds hq.2))

/-! ## 5. The derivative of the joint expression -/

/-- The `MatE`-component of the linear part of the jet pair map. -/
noncomputable def FzLinA (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) (y : E) :
    FzCoef ι₀ (Module.finrank ℝ E) ε →L[ℝ] Work.Diff.EXT.MatE (E := E) :=
  ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
    (ContinuousLinearMap.proj (R := ℝ) z :
      FzCoef ι₀ (Module.finrank ℝ E) ε →L[ℝ] ℝ).smulRight
      (FzA0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀ y)

/-- The first jet component of the linear part of the jet pair map. -/
noncomputable def FzLinL (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) (y : E) :
    FzCoef ι₀ (Module.finrank ℝ E) ε →L[ℝ] Work.Diff.STE.DeTurck.LinMat E :=
  ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
    (ContinuousLinearMap.proj (R := ℝ) z :
      FzCoef ι₀ (Module.finrank ℝ E) ε →L[ℝ] ℝ).smulRight
      (FzL0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀ y)

/-- The second jet component of the linear part of the jet pair map. -/
noncomputable def FzLinB (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) (y : E) :
    FzCoef ι₀ (Module.finrank ℝ E) ε →L[ℝ] FzBil (E := E) :=
  ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
    (ContinuousLinearMap.proj (R := ℝ) z :
      FzCoef ι₀ (Module.finrank ℝ E) ε →L[ℝ] ℝ).smulRight
      (FzB0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀ y)

lemma FzLinA_apply (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) (y : E)
    (δ : FzCoef ι₀ (Module.finrank ℝ E) ε) :
    FzLinA (I := I) (M := M) g₀ D ε x₀ y δ
      = ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          δ z • FzA0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀ y := by
  simp only [FzLinA, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

lemma FzLinL_apply (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) (y : E)
    (δ : FzCoef ι₀ (Module.finrank ℝ E) ε) :
    FzLinL (I := I) (M := M) g₀ D ε x₀ y δ
      = ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          δ z • FzL0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀ y := by
  simp only [FzLinL, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

lemma FzLinB_apply (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) (y : E)
    (δ : FzCoef ι₀ (Module.finrank ℝ E) ε) :
    FzLinB (I := I) (M := M) g₀ D ε x₀ y δ
      = ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          δ z • FzB0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀ y := by
  simp only [FzLinB, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

/-- **The linear part of the jet pair map**: the sum of the direction vectors weighted by the
coefficients, assembled componentwise (so that only the "leaf" instances of the jet space are
needed). -/
noncomputable def FzJetLin (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) (y : E) :
    FzCoef ι₀ (Module.finrank ℝ E) ε →L[ℝ] Work.Diff.STE.deTurck.JetPair (E := E) :=
  (0 : FzCoef ι₀ (Module.finrank ℝ E) ε →L[ℝ] FzTri (E := E)).prod
    ((FzLinA (I := I) (M := M) g₀ D ε x₀ y).prod
      ((FzLinL (I := I) (M := M) g₀ D ε x₀ y).prod
        (FzLinB (I := I) (M := M) g₀ D ε x₀ y)))

/-- The linear part computes the sum of the direction vectors. -/
lemma FzJetLin_apply (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) (y : E)
    (δ : FzCoef ι₀ (Module.finrank ℝ E) ε) :
    FzJetLin (I := I) (M := M) g₀ D ε x₀ y δ
      = ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          δ z • jetDir (I := I) (M := M) g₀ D ε x₀ z y := by
  have hdef : FzJetLin (I := I) (M := M) g₀ D ε x₀ y =
      (0 : FzCoef ι₀ (Module.finrank ℝ E) ε →L[ℝ] FzTri (E := E)).prod
        ((FzLinA (I := I) (M := M) g₀ D ε x₀ y).prod
          ((FzLinL (I := I) (M := M) g₀ D ε x₀ y).prod
            (FzLinB (I := I) (M := M) g₀ D ε x₀ y))) := rfl
  have hR1 : (∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      δ z • jetDir (I := I) (M := M) g₀ D ε x₀ z y).1 = 0 := by
    rw [Prod.fst_sum]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [Work.Diff.STE.D.jetDir, Prod.smul_fst]
    exact fz_smul_zero_tri (E := E) (δ z)
  have hR2 : (∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      δ z • jetDir (I := I) (M := M) g₀ D ε x₀ z y).2.1
      = ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          δ z • FzA0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀ y := by
    rw [Prod.snd_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Work.Diff.STE.D.jetDir, Prod.smul_snd, Prod.smul_fst, FzA0]
  have hR3 : (∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      δ z • jetDir (I := I) (M := M) g₀ D ε x₀ z y).2.2.1
      = ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          δ z • FzL0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀ y := by
    rw [Prod.snd_sum, Prod.snd_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Work.Diff.STE.D.jetDir, Prod.smul_snd, Prod.smul_snd, Prod.smul_fst, FzL0]
  have hR4 : (∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      δ z • jetDir (I := I) (M := M) g₀ D ε x₀ z y).2.2.2
      = ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          δ z • FzB0 (I := I) (M := M) (jSym (I := I) (M := M) D ε z) x₀ y := by
    rw [Prod.snd_sum, Prod.snd_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Work.Diff.STE.D.jetDir, Prod.smul_snd, Prod.smul_snd, Prod.smul_snd, FzB0]
  rw [hdef, ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_apply, FzLinA_apply,
    FzLinL_apply, FzLinB_apply]
  refine Prod.ext ?_ ?_
  · rw [hR1]
  · refine Prod.ext ?_ ?_
    · rw [hR2]
    · refine Prod.ext ?_ ?_
      · rw [hR3]
      · rw [hR4]

/-- The background jet triple: the one not depending on the coefficients. -/
noncomputable def FzJ0 (g₀ : Submission.Diff.SMet I M) (x₀ : M) (y : E) : FzTri (E := E) :=
  (FzA0 (I := I) (M := M) g₀.inner x₀ y,
    (FzL0 (I := I) (M := M) g₀.inner x₀ y, FzB0 (I := I) (M := M) g₀.inner x₀ y))

/-- The `MatE` component of the affine triple is the background value plus the linear part. -/
lemma FzAffA_eq_add (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) (y : E) :
    FzAffA (I := I) (M := M) g₀ D ε x₀ c y =
      FzA0 (I := I) (M := M) g₀.inner x₀ y
        + FzLinA (I := I) (M := M) g₀ D ε x₀ y c := by
  rw [FzAffA, FzLinA_apply]

/-- The first jet component of the affine triple is the background value plus the linear part. -/
lemma FzAffL_eq_add (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) (y : E) :
    FzAffL (I := I) (M := M) g₀ D ε x₀ c y =
      FzL0 (I := I) (M := M) g₀.inner x₀ y
        + FzLinL (I := I) (M := M) g₀ D ε x₀ y c := by
  rw [FzAffL, FzLinL_apply]

/-- The second jet component of the affine triple is the background value plus the linear part. -/
lemma FzAffB_eq_add (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) (y : E) :
    FzAffB (I := I) (M := M) g₀ D ε x₀ c y =
      FzB0 (I := I) (M := M) g₀.inner x₀ y
        + FzLinB (I := I) (M := M) g₀ D ε x₀ y c := by
  rw [FzAffB, FzLinB_apply]

/-- **The affine jet triple is the background triple plus the linear part.** -/
lemma FzAff3_eq_add (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) (y : E) :
    FzAff3 (I := I) (M := M) g₀ D ε x₀ c y
      = FzJ0 (I := I) g₀ x₀ y
        + (FzLinA (I := I) (M := M) g₀ D ε x₀ y c,
            (FzLinL (I := I) (M := M) g₀ D ε x₀ y c,
             FzLinB (I := I) (M := M) g₀ D ε x₀ y c)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact FzAffA_eq_add (I := I) (M := M) g₀ D ε x₀ c y
  · exact FzAffL_eq_add (I := I) (M := M) g₀ D ε x₀ c y
  · exact FzAffB_eq_add (I := I) (M := M) g₀ D ε x₀ c y

/-- **The jet pair is affine in the coefficients**: its Fréchet derivative is the constant linear
part `FzJetLin`. -/
lemma Fz_hasFDerivAt_jetPair {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c₀ : FzCoef ι₀ (Module.finrank ℝ E) ε) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    HasFDerivAt (fun c : FzCoef ι₀ (Module.finrank ℝ E) ε =>
        jetPairOf (I := I) (M := M) g₀ D ε x₀ c y)
      (FzJetLin (I := I) (M := M) g₀ D ε x₀ y) c₀ := by
  have haff : ∀ c' : FzCoef ι₀ (Module.finrank ℝ E) ε,
      FzJetAff (I := I) (M := M) g₀ D ε x₀ c' y
        = (FzJ0 (I := I) g₀ x₀ y, FzJ0 (I := I) g₀ x₀ y)
          + FzJetLin (I := I) (M := M) g₀ D ε x₀ y c' := by
    intro c'
    have hL : FzJetLin (I := I) (M := M) g₀ D ε x₀ y c'
        = ((0 : FzTri (E := E)),
            (FzLinA (I := I) (M := M) g₀ D ε x₀ y c',
             (FzLinL (I := I) (M := M) g₀ D ε x₀ y c',
              FzLinB (I := I) (M := M) g₀ D ε x₀ y c'))) := rfl
    rw [hL]
    refine Prod.ext ?_ ?_
    · show FzJ0 (I := I) g₀ x₀ y = FzJ0 (I := I) g₀ x₀ y + 0
      exact (add_zero (FzJ0 (I := I) g₀ x₀ y)).symm
    · change FzAff3 (I := I) (M := M) g₀ D ε x₀ c' y
          = FzJ0 (I := I) g₀ x₀ y
            + (FzLinA (I := I) (M := M) g₀ D ε x₀ y c',
                (FzLinL (I := I) (M := M) g₀ D ε x₀ y c',
                 FzLinB (I := I) (M := M) g₀ D ε x₀ y c'))
      rw [FzAff3_eq_add (I := I) (M := M) g₀ D ε x₀ c' y]
  have hfun : (fun c : FzCoef ι₀ (Module.finrank ℝ E) ε =>
        jetPairOf (I := I) (M := M) g₀ D ε x₀ c y)
      = fun c => (FzJ0 (I := I) g₀ x₀ y, FzJ0 (I := I) g₀ x₀ y)
          + FzJetLin (I := I) (M := M) g₀ D ε x₀ y c := by
    funext c'
    rw [← FzJetAff_eq (I := I) (M := M) hg D ε x₀ c' hy]
    exact haff c'
  rw [hfun]
  exact (ContinuousLinearMap.hasFDerivAt (FzJetLin (I := I) (M := M) g₀ D ε x₀ y)
    (x := c₀)).const_add (FzJ0 (I := I) g₀ x₀ y, FzJ0 (I := I) g₀ x₀ y)

/-- **The derivative of the joint chart DeTurck expression in a direction `δ` of the coefficient
space** is the linearisation `pPhiFunD` evaluated at the corresponding linear combination of the
direction vectors. -/
lemma Fz_fderiv_Phi {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) {y : FzFlat (Module.finrank ℝ E)}
    (hy : flatToE (I := I) x₀ y ∈ (extChartAt I x₀).target)
    (hdom : jetPairOf (I := I) (M := M) g₀ D ε x₀ c (flatToE (I := I) x₀ y)
      ∈ Work.Diff.STE.deTurck.pPhiDom (E := E))
    (δ : FzCoef ι₀ (Module.finrank ℝ E) ε) :
    (fderiv ℝ (FzPhi (I := I) (M := M) g₀ D ε x₀) (c, y))
        (δ, (0 : FzFlat (Module.finrank ℝ E)))
      = Work.Diff.STE.D.pPhiFunD (E := E)
          (jetPairOf (I := I) (M := M) g₀ D ε x₀ c (flatToE (I := I) x₀ y))
          (FzJetLin (I := I) (M := M) g₀ D ε x₀ (flatToE (I := I) x₀ y) δ) := by
  have hmem : (c, y) ∈ FzDom (I := I) (M := M) g₀ D ε x₀ := ⟨hy, hdom⟩
  have hF : HasFDerivAt (FzPhi (I := I) (M := M) g₀ D ε x₀)
      (fderiv ℝ (FzPhi (I := I) (M := M) g₀ D ε x₀) (c, y)) (c, y) :=
    (((contDiffOn_FzPhi (I := I) (M := M) hg D ε x₀).contDiffAt
      ((isOpen_FzDom (I := I) (M := M) hg D ε x₀).mem_nhds hmem)).differentiableAt
        (by norm_num)).hasFDerivAt
  have hd : HasFDerivAt (fun c' : FzCoef ι₀ (Module.finrank ℝ E) ε =>
      FzPhi (I := I) (M := M) g₀ D ε x₀ (c', y))
      (Work.Diff.STE.D.pPhiFunD (E := E)
          (jetPairOf (I := I) (M := M) g₀ D ε x₀ c (flatToE (I := I) x₀ y))
        ∘SL FzJetLin (I := I) (M := M) g₀ D ε x₀ (flatToE (I := I) x₀ y)) c :=
    ((hasFDerivAt_pPhiFun_Fz (E := E) _ hdom).comp c
      (Fz_hasFDerivAt_jetPair (I := I) (M := M) hg D ε x₀ c hy)).congr_of_eventuallyEq
        (Filter.EventuallyEq.of_eq rfl)
  have h2 : HasFDerivAt (fun c' : FzCoef ι₀ (Module.finrank ℝ E) ε =>
      FzPhi (I := I) (M := M) g₀ D ε x₀ (c', y))
      ((fderiv ℝ (FzPhi (I := I) (M := M) g₀ D ε x₀) (c, y)) ∘SL
        (ContinuousLinearMap.inl ℝ (FzCoef ι₀ (Module.finrank ℝ E) ε)
          (FzFlat (Module.finrank ℝ E)))) c :=
    (HasFDerivAt.comp c hF (hasFDerivAt_prodMk_left (𝕜 := ℝ) c y)).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq rfl)
  have hfd : (fderiv ℝ (FzPhi (I := I) (M := M) g₀ D ε x₀) (c, y)) ∘SL
        (ContinuousLinearMap.inl ℝ (FzCoef ι₀ (Module.finrank ℝ E) ε)
          (FzFlat (Module.finrank ℝ E)))
      = Work.Diff.STE.D.pPhiFunD (E := E)
          (jetPairOf (I := I) (M := M) g₀ D ε x₀ c (flatToE (I := I) x₀ y))
        ∘SL FzJetLin (I := I) (M := M) g₀ D ε x₀ (flatToE (I := I) x₀ y) := by
    rw [← hd.fderiv, h2.fderiv]
  calc (fderiv ℝ (FzPhi (I := I) (M := M) g₀ D ε x₀) (c, y))
        (δ, (0 : FzFlat (Module.finrank ℝ E)))
      = ((fderiv ℝ (FzPhi (I := I) (M := M) g₀ D ε x₀) (c, y)) ∘SL
          (ContinuousLinearMap.inl ℝ (FzCoef ι₀ (Module.finrank ℝ E) ε)
            (FzFlat (Module.finrank ℝ E)))) δ := rfl
    _ = (Work.Diff.STE.D.pPhiFunD (E := E)
          (jetPairOf (I := I) (M := M) g₀ D ε x₀ c (flatToE (I := I) x₀ y))
        ∘SL FzJetLin (I := I) (M := M) g₀ D ε x₀ (flatToE (I := I) x₀ y)) δ :=
      congrArg (fun L => L δ) hfd
    _ = Work.Diff.STE.D.pPhiFunD (E := E)
          (jetPairOf (I := I) (M := M) g₀ D ε x₀ c (flatToE (I := I) x₀ y))
          (FzJetLin (I := I) (M := M) g₀ D ε x₀ (flatToE (I := I) x₀ y) δ) := rfl

/-! ## 6. The weight functional -/

/-- **The weight functional of the localised component `z`.**  It contracts a chart matrix with
the coordinates of the two frame vectors `e z.1 z.2.1` and `e z.1 z.2.2.1` at `pt z.1 y`. -/
noncomputable def LamFun (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ε : ℝ) (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (y : FzFlat (Module.finrank ℝ E)) : Work.Diff.EXT.MatE (E := E) →L[ℝ] ℝ :=
  ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    (Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
        (D.e z.1 z.2.1 (D.pt z.1 y))
      * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
        (D.e z.1 z.2.2.1 (D.pt z.1 y))) •
      ((ContinuousLinearMap.proj (R := ℝ) k :
          (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj (R := ℝ) j :
          Work.Diff.EXT.MatE (E := E) →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)))

@[simp] lemma LamFun_apply (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (y : FzFlat (Module.finrank ℝ E)) (X : Work.Diff.EXT.MatE (E := E)) :
    LamFun (I := I) (M := M) D ε z y X =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        (Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
            (D.e z.1 z.2.1 (D.pt z.1 y))
          * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
            (D.e z.1 z.2.2.1 (D.pt z.1 y)))
          * X j k := by
  simp only [LamFun, sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- **The weight functional is bounded by the number of entries times the bounds on the coordinate
factors.** -/
lemma abs_LamFun_le (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) (y : FzFlat (Module.finrank ℝ E))
    {Ba Bb : ℝ} (hBa0 : 0 ≤ Ba) (hBb0 : 0 ≤ Bb)
    (hBa : ∀ j : Fin (Module.finrank ℝ E),
      |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
        (D.e z.1 z.2.1 (D.pt z.1 y))| ≤ Ba)
    (hBb : ∀ k : Fin (Module.finrank ℝ E),
      |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
        (D.e z.1 z.2.2.1 (D.pt z.1 y))| ≤ Bb)
    (X : Work.Diff.EXT.MatE (E := E)) :
    |LamFun (I := I) (M := M) D ε z y X|
      ≤ ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * ‖X‖ := by
  rw [LamFun_apply]
  calc |∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        (Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
            (D.e z.1 z.2.1 (D.pt z.1 y))
          * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
            (D.e z.1 z.2.2.1 (D.pt z.1 y)))
          * X j k|
      ≤ ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          |(Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
              (D.e z.1 z.2.1 (D.pt z.1 y))
            * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
              (D.e z.1 z.2.2.1 (D.pt z.1 y)))
            * X j k| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (Module.finrank ℝ E), ∑ _k : Fin (Module.finrank ℝ E),
          Ba * Bb * ‖X‖ := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul (hBa j) (hBb k) (abs_nonneg _) hBa0)
          (le_trans (norm_le_pi_norm (X j) k) (norm_le_pi_norm X j)) (abs_nonneg _)
          (mul_nonneg hBa0 hBb0)
    _ = ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * ‖X‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## 7. `Fz` and `Ufun` through the weight functional -/

/-- **The localised component `Fz` as weight times weight functional.** -/
lemma Fz_eq_LamFun (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) {y : FzFlat (Module.finrank ℝ E)}
    (hy : flatToE (I := I) (D.x₀ z.1) y ∈ (extChartAt I (D.x₀ z.1)).target) :
    Work.Diff.STE.D.Fz (I := I) (M := M) g₀ D ε z c y =
      (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
        LamFun (I := I) (M := M) D ε z y
          (FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1) (c, y)) := by
  have hpt : (extChartAt I (D.x₀ z.1)) (D.pt z.1 y)
      = flatToE (I := I) (D.x₀ z.1) y := (extChartAt I (D.x₀ z.1)).right_inv hy
  simp only [Work.Diff.STE.D.Fz, Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat,
    Work.Diff.STE.D.secChart_apply, Work.Diff.STE.D.secChartVal, hpt,
    Work.Diff.STE.D.pPhiJetOf_apply, FzPhi, Work.Diff.STE.D.jetPairOf,
    Work.Diff.STE.D.pPhiFun, LamFun_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The directional derivative integrand `Ufun` as weight times weight functional.** -/
lemma Ufun_eq_LamFun (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : FzCoef ι₀ (Module.finrank ℝ E) ε) (y : FzFlat (Module.finrank ℝ E)) :
    Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c y =
      (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
        LamFun (I := I) (M := M) D ε z y
          (Work.Diff.STE.D.pPhiFunD (E := E)
            (jetPairOf (I := I) (M := M) g₀ D ε (D.x₀ z.1) c
              (flatToE (I := I) (D.x₀ z.1) y))
            (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ z.1) z'
              (flatToE (I := I) (D.x₀ z.1) y))) := by
  rw [Work.Diff.STE.D.Ufun, LamFun_apply]

/-! ## 8. The second order Taylor estimate -/

theorem abs_Fz_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    ∃ (δ C : ℝ), 0 < δ ∧ 0 ≤ C ∧
      ∀ (c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
        ‖c₀‖ < δ → Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c₀ →
        ∀ (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
          ‖c - c₀‖ < δ → Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c →
          ∀ y : Fin (Module.finrank ℝ E) → ℝ,
            |Work.Diff.STE.D.Fz (I := I) (M := M) g₀ D ε z c y
              - Work.Diff.STE.D.Fz (I := I) (M := M) g₀ D ε z c₀ y
              - ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
                  (c z' - c₀ z') * Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c₀ y|
              ≤ C * ‖c - c₀‖ ^ 2 := by
  classical
  obtain ⟨δp, hδp, hIsPos⟩ := exists_isPos_ball (I := I) (M := M) D ε
  obtain ⟨Bpref, hBpref0, hBpref⟩ := abs_pref_le (I := I) (M := M) D z.1
  obtain ⟨Ba, hBa0, hBa⟩ := Fz_coord_factor_le (I := I) (M := M) D z.1 z.2.1
  obtain ⟨Bb, hBb0, hBb⟩ := Fz_coord_factor_le (I := I) (M := M) D z.1 z.2.2.1
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hPhi := contDiffOn_FzPhi (I := I) (M := M) hg D ε (D.x₀ z.1)
  have hDom := isOpen_FzDom (I := I) (M := M) hg D ε (D.x₀ z.1)
  have hK : IsCompact (Metric.closedBall (0 : FzCoef ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
      Metric.closedBall (0 : FzFlat (Module.finrank ℝ E)) (D.σ z.1)) :=
    (isCompact_closedBall (0 : FzCoef ι₀ (Module.finrank ℝ E) ε) (δp / 2)).prod
      (isCompact_closedBall (0 : FzFlat (Module.finrank ℝ E)) (D.σ z.1))
  have hKs : (Metric.closedBall (0 : FzCoef ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
      Metric.closedBall (0 : FzFlat (Module.finrank ℝ E)) (D.σ z.1))
      ⊆ FzDom (I := I) (M := M) g₀ D ε (D.x₀ z.1) := by
    rintro q hq
    obtain ⟨hq1, hq2⟩ := hq
    have hq1' : ‖q.1‖ ≤ δp / 2 := by
      rwa [Metric.mem_closedBall, dist_zero_right] at hq1
    have hq2' : ‖q.2‖ ≤ D.σ z.1 := by
      rwa [Metric.mem_closedBall, dist_zero_right] at hq2
    have htarget : flatToE (I := I) (D.x₀ z.1) q.2 ∈ (extChartAt I (D.x₀ z.1)).target :=
      D.htarget z.1 q.2 (by linarith [D.hσ z.1, hq2'])
    exact ⟨htarget, Fz_jet_mem_pPhiDom (I := I) (M := M) hg D (D.x₀ z.1) q.1
      (hIsPos q.1 (by linarith)) htarget⟩
  obtain ⟨δt, Mt, hδt, hMt0, hMt⟩ :=
    Work.Diff.Calc.taylor_bound_on_compact (FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1))
      (FzDom (I := I) (M := M) g₀ D ε (D.x₀ z.1))
      (Metric.closedBall (0 : FzCoef ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
        Metric.closedBall (0 : FzFlat (Module.finrank ℝ E)) (D.σ z.1))
      hDom hK hKs hPhi
  have hC0 : 0 ≤ Bpref * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * Mt :=
    mul_nonneg (mul_nonneg hBpref0
      (mul_nonneg (mul_nonneg (mul_nonneg hn0 hn0) hBa0) hBb0)) hMt0
  refine ⟨min (δp / 2) δt,
    Bpref * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * Mt,
    lt_min (by linarith) hδt, hC0, ?_⟩
  intro c₀ hc₀ hp₀ c hc hp y
  by_cases hψ : D.psi z.1 y = 0
  · -- the localised weight vanishes, so do all three terms
    have hFz : ∀ c' : FzCoef ι₀ (Module.finrank ℝ E) ε,
        Work.Diff.STE.D.Fz (I := I) (M := M) g₀ D ε z c' y = 0 := by
      intro c'
      rw [Work.Diff.STE.D.Fz, Work.Diff.STE.B3Data.R, hψ, zero_mul, zero_mul]
    have hU : (∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        (c z' - c₀ z') * Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c₀ y) = 0 := by
      refine Finset.sum_eq_zero fun z' _ => ?_
      rw [Work.Diff.STE.D.Ufun, hψ, zero_mul, zero_mul, mul_zero]
    rw [hFz c, hFz c₀, hU]
    simp only [sub_zero, abs_zero]
    exact mul_nonneg hC0 (sq_nonneg _)
  · -- the localised weight can be nonzero: the compact Taylor region applies
    have hyT : flatToE (I := I) (D.x₀ z.1) y ∈ (extChartAt I (D.x₀ z.1)).target :=
      Work.Diff.STE.B3.target_of_psi_ne_zero (I := I) (M := M) (D := D) hψ
    have hyσ : ‖y‖ ≤ D.σ z.1 :=
      le_of_lt (Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero (I := I) (M := M) (D := D) hψ)
    have hyK : y ∈ FzKreg (I := I) (M := M) D z.1 :=
      mem_FzKreg_of_psi_ne_zero (I := I) (M := M) D hψ
    have hc₀' : ‖c₀‖ ≤ δp / 2 := le_of_lt (lt_of_lt_of_le hc₀ (min_le_left _ _))
    have hxK : (c₀, y) ∈ Metric.closedBall (0 : FzCoef ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
        Metric.closedBall (0 : FzFlat (Module.finrank ℝ E)) (D.σ z.1) := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hc₀'
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hyσ
    have hc' : ‖c - c₀‖ ≤ δt := le_of_lt (lt_of_lt_of_le hc (min_le_right _ _))
    have hstep : ‖FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1) (c, y)
        - FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1) (c₀, y)
        - (fderiv ℝ (FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y))
            (c - c₀, (0 : FzFlat (Module.finrank ℝ E)))‖ ≤ Mt * ‖c - c₀‖ ^ 2 := by
      have h := hMt (c₀, y) hxK (c - c₀, (0 : FzFlat (Module.finrank ℝ E))) (by
        rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
        exact hc')
      have hpt : (c₀, y) + (c - c₀, (0 : FzFlat (Module.finrank ℝ E))) = (c, y) := by
        rw [Prod.mk_add_mk, add_sub_cancel, add_zero]
      have hnorm : ‖(c - c₀, (0 : FzFlat (Module.finrank ℝ E)))‖ = ‖c - c₀‖ := by
        rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
      rw [hpt, hnorm] at h
      exact h
    have hdom₀ : jetPairOf (I := I) (M := M) g₀ D ε (D.x₀ z.1) c₀
        (flatToE (I := I) (D.x₀ z.1) y) ∈ Work.Diff.STE.deTurck.pPhiDom (E := E) :=
      Fz_jet_mem_pPhiDom (I := I) (M := M) hg D (D.x₀ z.1) c₀ hp₀ hyT
    -- the identification of the sum of `Ufun` with the derivative
    have hsum : (∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          (c z' - c₀ z') * Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c₀ y)
        = (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
            LamFun (I := I) (M := M) D ε z y
              ((fderiv ℝ (FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y))
                (c - c₀, (0 : FzFlat (Module.finrank ℝ E)))) := by
      have hper : ∀ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c₀ y
            = (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
              LamFun (I := I) (M := M) D ε z y
                (Work.Diff.STE.D.pPhiFunD (E := E)
                  (jetPairOf (I := I) (M := M) g₀ D ε (D.x₀ z.1) c₀
                    (flatToE (I := I) (D.x₀ z.1) y))
                  (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ z.1) z'
                    (flatToE (I := I) (D.x₀ z.1) y))) :=
        fun z' => Ufun_eq_LamFun (I := I) (M := M) D ε z z' c₀ y
      calc (∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
            (c z' - c₀ z') * Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c₀ y)
          = ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
              (c z' - c₀ z') *
                ((D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
                  LamFun (I := I) (M := M) D ε z y
                    (Work.Diff.STE.D.pPhiFunD (E := E)
                      (jetPairOf (I := I) (M := M) g₀ D ε (D.x₀ z.1) c₀
                        (flatToE (I := I) (D.x₀ z.1) y))
                      (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ z.1) z'
                        (flatToE (I := I) (D.x₀ z.1) y)))) := by
            refine Finset.sum_congr rfl fun z' _ => ?_
            rw [hper z']
        _ = (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
              (∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
                (c z' - c₀ z') *
                  LamFun (I := I) (M := M) D ε z y
                    (Work.Diff.STE.D.pPhiFunD (E := E)
                      (jetPairOf (I := I) (M := M) g₀ D ε (D.x₀ z.1) c₀
                        (flatToE (I := I) (D.x₀ z.1) y))
                      (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ z.1) z'
                        (flatToE (I := I) (D.x₀ z.1) y)))) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun z' _ => by ring
        _ = (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
              LamFun (I := I) (M := M) D ε z y
                ((fderiv ℝ (FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y))
                  (c - c₀, (0 : FzFlat (Module.finrank ℝ E)))) := by
            congr 1
            rw [Fz_fderiv_Phi (I := I) (M := M) hg D ε (D.x₀ z.1) c₀ hyT hdom₀ (c - c₀),
              FzJetLin_apply]
            rw [map_sum, map_sum]
            refine Finset.sum_congr rfl fun z' _ => ?_
            rw [map_smul, map_smul, smul_eq_mul, Pi.sub_apply]
    -- the identification of the left hand side
    have hLHS : Work.Diff.STE.D.Fz (I := I) (M := M) g₀ D ε z c y
        - Work.Diff.STE.D.Fz (I := I) (M := M) g₀ D ε z c₀ y
        - ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
            (c z' - c₀ z') * Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c₀ y
        = (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
            LamFun (I := I) (M := M) D ε z y
              (FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1) (c, y)
                - FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1) (c₀, y)
                - (fderiv ℝ (FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y))
                    (c - c₀, (0 : FzFlat (Module.finrank ℝ E)))) := by
      rw [show Work.Diff.STE.D.Fz (I := I) (M := M) g₀ D ε z c y = _
          from Fz_eq_LamFun (I := I) (M := M) hg D ε z c hyT,
        show Work.Diff.STE.D.Fz (I := I) (M := M) g₀ D ε z c₀ y = _
          from Fz_eq_LamFun (I := I) (M := M) hg D ε z c₀ hyT,
        hsum, map_sub, map_sub]
      ring
    rw [hLHS, abs_mul]
    have hWtb := hBpref y
    have hLamb := abs_LamFun_le (I := I) (M := M) D ε z y hBa0 hBb0
      (fun j => hBa y hyK j) (fun k => hBb y hyK k)
      (FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1) (c, y)
        - FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1) (c₀, y)
        - (fderiv ℝ (FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y))
            (c - c₀, (0 : FzFlat (Module.finrank ℝ E))))
    calc |D.psi z.1 y * Real.sqrt (D.dens z.1 y)|
          * |LamFun (I := I) (M := M) D ε z y
              (FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1) (c, y)
                - FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1) (c₀, y)
                - (fderiv ℝ (FzPhi (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y))
                    (c - c₀, (0 : FzFlat (Module.finrank ℝ E))))|
        ≤ Bpref * (((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb)
            * (Mt * ‖c - c₀‖ ^ 2)) :=
          mul_le_mul hWtb (le_trans hLamb (mul_le_mul_of_nonneg_left hstep
            (mul_nonneg (mul_nonneg (mul_nonneg hn0 hn0) hBa0) hBb0))) (abs_nonneg _) hBpref0
      _ = (Bpref * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * Mt)
            * ‖c - c₀‖ ^ 2 := by ring

end

end Work.Diff.STE.D.psi
