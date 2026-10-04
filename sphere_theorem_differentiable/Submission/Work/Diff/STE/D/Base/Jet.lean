/-
# Layer D: the base-generalised jet machinery (affinity, smoothness, derivatives)

This module is the second half of the structural set-up of `Work.Diff.STE.D.Base.Defs`: the
explicit affine form of the chart `2`-jet of the affine foreground
(`FzAffAB`, `FzAffLB`, `FzAffBB`, `FzAff3B`, `FzJetAffB`), its smoothness as a function of the pair
`(coefficients, chart coordinate)` (`contDiffOn_FzJetAffB`, `contDiffOn_jetPB`), the smoothness of
the joint chart DeTurck expression on its domain (`contDiffOn_PhiB`, `isOpen_DomB`), and the two
derivative computations that the analytic estimates use: the derivative of the joint expression in
a coefficient direction (`Fz_fderiv_PhiB`, `fderiv_PhiB_apply_single`) and the resulting expression
for the directional integrand (`UfunB_eq_fderiv`).
-/
import Mathlib
import Submission.Work.Diff.STE.D.Base.Defs
import Submission.Work.Diff.STE.D.psi.abs_Ufun_sub_le
import Submission.Work.Diff.STE.B3.scoeff_finset_sum_smul

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

/-! ## 0. Instance support for the nested continuous linear map spaces -/

/-- `ℝ` acts boundedly on the space of *twice* nested continuous linear maps. -/
local instance baseBilSMul :
    IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E)) :=
  IsBoundedSMul.of_norm_smul_le fun r L => ContinuousLinearMap.opNorm_smul_le r L

/-- Addition is continuous on the space of twice nested continuous linear maps. -/
local instance baseBilCAdd :
    ContinuousAdd (E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E)) :=
  ⟨(inferInstance : IsTopologicalAddGroup
    (E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E))).continuous_add⟩

/-! ## 1. The affine form of the chart jet of the foreground -/

/-- **The `MatE` component of the chart `2`-jet of the affine foreground.** -/
noncomputable def FzAffAB (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (y : E) :
    Work.Diff.EXT.MatE (E := E) :=
  Work.Diff.STE.D.psi.FzA0 (I := I) (M := M) a₀ x₀ y
    + ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        c z • Work.Diff.STE.D.psi.FzA0 (I := I) (M := M)
          (jSym (I := I) (M := M) D ε z) x₀ y

/-- **The first jet component of the chart `2`-jet of the affine foreground.** -/
noncomputable def FzAffLB (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (y : E) :
    Work.Diff.STE.DeTurck.LinMat E :=
  Work.Diff.STE.D.psi.FzL0 (I := I) (M := M) a₀ x₀ y
    + ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        c z • Work.Diff.STE.D.psi.FzL0 (I := I) (M := M)
          (jSym (I := I) (M := M) D ε z) x₀ y

/-- **The second jet component of the chart `2`-jet of the affine foreground.** -/
noncomputable def FzAffBB (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (y : E) :
    Work.Diff.STE.D.psi.FzBil (E := E) :=
  Work.Diff.STE.D.psi.FzB0 (I := I) (M := M) a₀ x₀ y
    + ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        c z • Work.Diff.STE.D.psi.FzB0 (I := I) (M := M)
          (jSym (I := I) (M := M) D ε z) x₀ y

/-- **The foreground triple of the affine jet pair.** -/
noncomputable def FzAff3B (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (y : E) :
    Work.Diff.STE.D.psi.FzTri (E := E) :=
  (FzAffAB (I := I) (M := M) a₀ D ε x₀ c y,
   (FzAffLB (I := I) (M := M) a₀ D ε x₀ c y,
    FzAffBB (I := I) (M := M) a₀ D ε x₀ c y))

/-- **The pair of `2`-jets of the affine family**, in explicit component form. -/
noncomputable def FzJetAffB (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (y : E) :
    Work.Diff.STE.deTurck.JetPair (E := E) :=
  ((Work.Diff.STE.D.psi.FzA0 (I := I) (M := M) g₀.inner x₀ y,
   (Work.Diff.STE.D.psi.FzL0 (I := I) (M := M) g₀.inner x₀ y,
    Work.Diff.STE.D.psi.FzB0 (I := I) (M := M) g₀.inner x₀ y)),
   FzAff3B (I := I) (M := M) a₀ D ε x₀ c y)

/-- The `MatE` component of the affine form is the first component of the chart jet. -/
lemma FzAffAB_eq (a₀ : Bil (I := I) (M := M))
    (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    FzAffAB (I := I) (M := M) a₀ D ε x₀ c y =
      (chartJetOf (I := I) (M := M)
        (fore (I := I) (M := M) a₀ D ε c) x₀ y).1 := by
  have h := chartJetOf_fore_affine (I := I) (M := M) a₀ ha₀ D ε x₀ c hy
  rw [FzAffAB, h]
  simp only [Work.Diff.STE.D.psi.FzA0, Prod.fst_add, Prod.fst_sum, Prod.smul_fst]

/-- The first jet component of the affine form is the first jet component of the chart jet. -/
lemma FzAffLB_eq (a₀ : Bil (I := I) (M := M))
    (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    FzAffLB (I := I) (M := M) a₀ D ε x₀ c y =
      (chartJetOf (I := I) (M := M)
        (fore (I := I) (M := M) a₀ D ε c) x₀ y).2.1 := by
  have h := chartJetOf_fore_affine (I := I) (M := M) a₀ ha₀ D ε x₀ c hy
  rw [FzAffLB, h]
  simp only [Work.Diff.STE.D.psi.FzL0, Prod.fst_add, Prod.fst_sum, Prod.smul_fst, Prod.snd_add,
    Prod.snd_sum, Prod.smul_snd]

/-- The second jet component of the affine form is the second jet component of the chart jet. -/
lemma FzAffBB_eq (a₀ : Bil (I := I) (M := M))
    (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    FzAffBB (I := I) (M := M) a₀ D ε x₀ c y =
      (chartJetOf (I := I) (M := M)
        (fore (I := I) (M := M) a₀ D ε c) x₀ y).2.2 := by
  have h := chartJetOf_fore_affine (I := I) (M := M) a₀ ha₀ D ε x₀ c hy
  rw [FzAffBB, h]
  simp only [Work.Diff.STE.D.psi.FzB0, Prod.fst_add, Prod.fst_sum, Prod.smul_fst, Prod.snd_add,
    Prod.snd_sum, Prod.smul_snd]

/-- **The affine form is the jet pair of the affine foreground.** -/
lemma FzJetAffB_eq (a₀ : Bil (I := I) (M := M))
    (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    FzJetAffB (I := I) (M := M) a₀ D ε x₀ c y =
      jetPB (I := I) (M := M) a₀ D ε x₀ c y := by
  rw [jetPB, FzJetAffB, Work.Diff.STE.D.psi.Fz_chartJetOf_eta (I := I) (M := M)
    (fore (I := I) (M := M) a₀ D ε c) x₀ y]
  refine Prod.ext (Prod.ext rfl (Prod.ext rfl rfl)) ?_
  refine Prod.ext ?_ ?_
  · exact FzAffAB_eq (I := I) (M := M) a₀ ha₀ D ε x₀ c hy
  · refine Prod.ext ?_ ?_
    · exact FzAffLB_eq (I := I) (M := M) a₀ ha₀ D ε x₀ c hy
    · exact FzAffBB_eq (I := I) (M := M) a₀ ha₀ D ε x₀ c hy

/-! ## 2. Smoothness of the affine jet pair -/

/-- **The affine jet pair is `C^∞`** on the set of coefficient vectors and flat coordinates whose
chart image lies in the target of the chart at `x₀`. -/
lemma contDiffOn_FzJetAffB (hg : ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Bil (I := I) (M := M)) (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        FzJetAffB (I := I) (M := M) a₀ D ε x₀ q.1 (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} := by
  classical
  have hflat : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.flatToE (I := I) x₀ q.2)
      {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    (Work.Diff.STE.contDiff_flatToE (I := I) x₀).comp_contDiffOn contDiffOn_snd
  -- the components of the background chart jet
  have hA0 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.D.psi.FzA0 (I := I) (M := M) g₀.inner x₀
          (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    ((Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M) g₀.inner x₀
      (hg x₀)).fst).comp hflat (fun _ hq => hq)
  have hL0 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.D.psi.FzL0 (I := I) (M := M) g₀.inner x₀
          (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    ((Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M) g₀.inner x₀
      (hg x₀)).snd.fst).comp hflat (fun _ hq => hq)
  have hB0 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.D.psi.FzB0 (I := I) (M := M) g₀.inner x₀
          (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    ((Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M) g₀.inner x₀
      (hg x₀)).snd.snd).comp hflat (fun _ hq => hq)
  -- the components of the base section of the foreground
  have hA0a : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.D.psi.FzA0 (I := I) (M := M) a₀ x₀
          (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    ((Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M) a₀ x₀
      (ha₀ x₀)).fst).comp hflat (fun _ hq => hq)
  have hL0a : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.D.psi.FzL0 (I := I) (M := M) a₀ x₀
          (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    ((Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M) a₀ x₀
      (ha₀ x₀)).snd.fst).comp hflat (fun _ hq => hq)
  have hB0a : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.D.psi.FzB0 (I := I) (M := M) a₀ x₀
          (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    ((Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M) a₀ x₀
      (ha₀ x₀)).snd.snd).comp hflat (fun _ hq => hq)
  -- the components of the spanning family
  have hAz : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
            (Fin (Module.finrank ℝ E) → ℝ) =>
          Work.Diff.STE.D.psi.FzA0 (I := I) (M := M)
            (jSym (I := I) (M := M) D ε z) x₀ (Work.Diff.STE.flatToE (I := I) x₀ q.2))
        {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
            (Fin (Module.finrank ℝ E) → ℝ) |
          Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    fun z => ((Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M)
      (jSym (I := I) (M := M) D ε z) x₀
      (Work.Diff.STE.D.psi.jSym_chartData (I := I) (M := M) D ε z x₀)).fst).comp
        hflat (fun _ hq => hq)
  have hLz : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
            (Fin (Module.finrank ℝ E) → ℝ) =>
          Work.Diff.STE.D.psi.FzL0 (I := I) (M := M)
            (jSym (I := I) (M := M) D ε z) x₀ (Work.Diff.STE.flatToE (I := I) x₀ q.2))
        {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
            (Fin (Module.finrank ℝ E) → ℝ) |
          Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    fun z => ((Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M)
      (jSym (I := I) (M := M) D ε z) x₀
      (Work.Diff.STE.D.psi.jSym_chartData (I := I) (M := M) D ε z x₀)).snd.fst).comp
        hflat (fun _ hq => hq)
  have hBz : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
            (Fin (Module.finrank ℝ E) → ℝ) =>
          Work.Diff.STE.D.psi.FzB0 (I := I) (M := M)
            (jSym (I := I) (M := M) D ε z) x₀ (Work.Diff.STE.flatToE (I := I) x₀ q.2))
        {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
            (Fin (Module.finrank ℝ E) → ℝ) |
          Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    fun z => ((Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M)
      (jSym (I := I) (M := M) D ε z) x₀
      (Work.Diff.STE.D.psi.jSym_chartData (I := I) (M := M) D ε z x₀)).snd.snd).comp
        hflat (fun _ hq => hq)
  have hcz : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
            (Fin (Module.finrank ℝ E) → ℝ) => q.1 z)
        {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
            (Fin (Module.finrank ℝ E) → ℝ) |
          Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    fun z => ((ContinuousLinearMap.proj (R := ℝ) z).comp
      (ContinuousLinearMap.fst ℝ (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
        (Fin (Module.finrank ℝ E) → ℝ))).contDiff.contDiffOn
  have hsumA : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          q.1 z • Work.Diff.STE.D.psi.FzA0 (I := I) (M := M)
            (jSym (I := I) (M := M) D ε z) x₀ (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} := by
    have h := ContDiffOn.sum (s := Finset.univ)
      (t := {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target})
      (f := fun z q => q.1 z • Work.Diff.STE.D.psi.FzA0 (I := I) (M := M)
        (jSym (I := I) (M := M) D ε z) x₀ (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      (fun z _ => (hcz z).smul (hAz z))
    simpa using h
  have hsumL : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          q.1 z • Work.Diff.STE.D.psi.FzL0 (I := I) (M := M)
            (jSym (I := I) (M := M) D ε z) x₀ (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} := by
    have h := ContDiffOn.sum (s := Finset.univ)
      (t := {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target})
      (f := fun z q => q.1 z • Work.Diff.STE.D.psi.FzL0 (I := I) (M := M)
        (jSym (I := I) (M := M) D ε z) x₀ (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      (fun z _ => (hcz z).smul (hLz z))
    simpa using h
  have hsumB : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          q.1 z • Work.Diff.STE.D.psi.FzB0 (I := I) (M := M)
            (jSym (I := I) (M := M) D ε z) x₀ (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} := by
    have h := ContDiffOn.sum (s := Finset.univ)
      (t := {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target})
      (f := fun z q => q.1 z • Work.Diff.STE.D.psi.FzB0 (I := I) (M := M)
        (jSym (I := I) (M := M) D ε z) x₀ (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      (fun z _ => (hcz z).smul (hBz z))
    simpa using h
  refine ContDiffOn.congr ?_ (fun q _ => rfl)
  refine ContDiffOn.prodMk (ContDiffOn.prodMk hA0 (ContDiffOn.prodMk hL0 hB0)) ?_
  exact ContDiffOn.prodMk (hA0a.add hsumA) (ContDiffOn.prodMk (hL0a.add hsumL)
    (hB0a.add hsumB))

/-- **The joint jet pair is `C^∞`** on the set of coefficient vectors and flat coordinates for which
the flat point stays inside the target of the chart at `x₀`. -/
lemma contDiffOn_jetPB (hg : ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Bil (I := I) (M := M)) (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        jetPB (I := I) (M := M) a₀ D ε x₀ q.1 (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
  (contDiffOn_FzJetAffB (I := I) (M := M) hg a₀ ha₀ D ε x₀).congr
    (fun q hq => (FzJetAffB_eq (I := I) (M := M) a₀ ha₀ D ε x₀ q.1 hq).symm)

/-! ## 3. Smoothness of the joint chart DeTurck expression -/

/-- **The joint chart DeTurck expression is smooth on its domain.** -/
lemma contDiffOn_PhiB (hg : ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Bil (I := I) (M := M)) (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    ContDiffOn ℝ 2 (PhiB (I := I) (M := M) a₀ D ε x₀)
      (DomB (I := I) (M := M) a₀ D ε x₀) := by
  have hjet : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        jetPB (I := I) (M := M) a₀ D ε x₀ q.1 (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      (DomB (I := I) (M := M) a₀ D ε x₀) :=
    (contDiffOn_jetPB (I := I) (M := M) hg a₀ ha₀ D ε x₀).mono Set.inter_subset_left
  have hcomp := (Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E)).comp hjet
    (fun q hq => by
      rw [DomB] at hq
      exact hq.2)
  exact hcomp.of_le (by simp)

/-- **The domain of the joint chart DeTurck expression is open.** -/
lemma isOpen_DomB (hg : ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Bil (I := I) (M := M)) (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    IsOpen (DomB (I := I) (M := M) a₀ D ε x₀) := by
  have hU : IsOpen {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
      (Fin (Module.finrank ℝ E) → ℝ) |
      Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    (Work.Diff.STE.D.psi.isOpen_flatToE_preimage_target (I := I) x₀).preimage
      (continuous_snd : Continuous fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
        (Fin (Module.finrank ℝ E) → ℝ) => q.2)
  have hcont := contDiffOn_jetPB (I := I) (M := M) hg a₀ ha₀ D ε x₀
  rw [isOpen_iff_mem_nhds]
  intro q hq
  have hqU : q ∈ {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
      (Fin (Module.finrank ℝ E) → ℝ) |
      Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} := hq.1
  have hc : ContinuousAt (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
      (Fin (Module.finrank ℝ E) → ℝ) =>
      jetPB (I := I) (M := M) a₀ D ε x₀ q.1 (Work.Diff.STE.flatToE (I := I) x₀ q.2)) q :=
    (hcont.continuousOn.continuousWithinAt hqU).continuousAt (hU.mem_nhds hqU)
  exact Filter.inter_mem (hU.mem_nhds hqU)
    (hc.preimage_mem_nhds ((Work.Diff.STE.D.psi.isOpen_pPhiDom (E := E)).mem_nhds hq.2))

/-! ## 4. The derivative of the joint chart DeTurck expression -/

/-- The background jet triple of the affine family. -/
noncomputable def FzJ0B (a₀ : Bil (I := I) (M := M)) (x₀ : M) (y : E) :
    Work.Diff.STE.D.psi.FzTri (E := E) :=
  (Work.Diff.STE.D.psi.FzA0 (I := I) (M := M) a₀ x₀ y,
    (Work.Diff.STE.D.psi.FzL0 (I := I) (M := M) a₀ x₀ y,
     Work.Diff.STE.D.psi.FzB0 (I := I) (M := M) a₀ x₀ y))

/-- The second jet component of the affine triple is the background value plus the linear part. -/
lemma FzAff3B_eq_add (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (y : E) :
    FzAff3B (I := I) (M := M) a₀ D ε x₀ c y
      = FzJ0B (I := I) (M := M) a₀ x₀ y
        + (Work.Diff.STE.D.psi.FzLinA (I := I) (M := M) g₀ D ε x₀ y c,
            (Work.Diff.STE.D.psi.FzLinL (I := I) (M := M) g₀ D ε x₀ y c,
             Work.Diff.STE.D.psi.FzLinB (I := I) (M := M) g₀ D ε x₀ y c)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show FzAffAB (I := I) (M := M) a₀ D ε x₀ c y
      = Work.Diff.STE.D.psi.FzA0 (I := I) (M := M) a₀ x₀ y
        + Work.Diff.STE.D.psi.FzLinA (I := I) (M := M) g₀ D ε x₀ y c
    rw [FzAffAB, Work.Diff.STE.D.psi.FzLinA_apply]
  · show FzAffLB (I := I) (M := M) a₀ D ε x₀ c y
      = Work.Diff.STE.D.psi.FzL0 (I := I) (M := M) a₀ x₀ y
        + Work.Diff.STE.D.psi.FzLinL (I := I) (M := M) g₀ D ε x₀ y c
    rw [FzAffLB, Work.Diff.STE.D.psi.FzLinL_apply]
  · show FzAffBB (I := I) (M := M) a₀ D ε x₀ c y
      = Work.Diff.STE.D.psi.FzB0 (I := I) (M := M) a₀ x₀ y
        + Work.Diff.STE.D.psi.FzLinB (I := I) (M := M) g₀ D ε x₀ y c
    rw [FzAffBB, Work.Diff.STE.D.psi.FzLinB_apply]

/-- The two linear parts of the jet-pair map agree. -/
lemma FzJetLin_eq_jetDirLin (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (x₀ : M) (y : E) :
    Work.Diff.STE.D.psi.FzJetLin (I := I) (M := M) g₀ D ε x₀ y
      = Work.Diff.STE.D.psi.jetDirLin (I := I) (M := M) g₀ D ε x₀ y := by
  refine ContinuousLinearMap.ext fun δ => ?_
  rw [Work.Diff.STE.D.psi.FzJetLin_apply, Work.Diff.STE.D.psi.jetDirLin_apply]

/-- **The affine jet pair is differentiable in the coefficients**, with derivative `FzJetLin`. -/
lemma hasFDerivAt_jetPB_FzJetLin (a₀ : Bil (I := I) (M := M))
    (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    HasFDerivAt (fun c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
        jetPB (I := I) (M := M) a₀ D ε x₀ c y)
      (Work.Diff.STE.D.psi.FzJetLin (I := I) (M := M) g₀ D ε x₀ y) c₀ := by
  rw [FzJetLin_eq_jetDirLin (I := I) (M := M) D ε x₀ y]
  exact hasFDerivAt_jetPB (I := I) (M := M) a₀ ha₀ D ε x₀ c₀ hy

/-- **The derivative of the joint chart DeTurck expression in a direction `δ` of the coefficient
space** is the linearisation `pPhiFunD` evaluated at the corresponding linear combination of the
direction vectors. -/
lemma Fz_fderiv_PhiB (hg : ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Bil (I := I) (M := M)) (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    {y : Fin (Module.finrank ℝ E) → ℝ}
    (hy : Work.Diff.STE.flatToE (I := I) x₀ y ∈ (extChartAt I x₀).target)
    (hdom : jetPB (I := I) (M := M) a₀ D ε x₀ c (Work.Diff.STE.flatToE (I := I) x₀ y)
      ∈ Work.Diff.STE.deTurck.pPhiDom (E := E))
    (δ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    (fderiv ℝ (PhiB (I := I) (M := M) a₀ D ε x₀) (c, y))
        (δ, (0 : Fin (Module.finrank ℝ E) → ℝ))
      = Work.Diff.STE.D.pPhiFunD (E := E)
          (jetPB (I := I) (M := M) a₀ D ε x₀ c (Work.Diff.STE.flatToE (I := I) x₀ y))
          (Work.Diff.STE.D.psi.FzJetLin (I := I) (M := M) g₀ D ε x₀
            (Work.Diff.STE.flatToE (I := I) x₀ y) δ) := by
  have hmem : (c, y) ∈ DomB (I := I) (M := M) a₀ D ε x₀ := ⟨hy, hdom⟩
  have hF : HasFDerivAt (PhiB (I := I) (M := M) a₀ D ε x₀)
      (fderiv ℝ (PhiB (I := I) (M := M) a₀ D ε x₀) (c, y)) (c, y) :=
    (((contDiffOn_PhiB (I := I) (M := M) hg a₀ ha₀ D ε x₀).contDiffAt
      ((isOpen_DomB (I := I) (M := M) hg a₀ ha₀ D ε x₀).mem_nhds hmem)).differentiableAt
        (by norm_num)).hasFDerivAt
  have hd : HasFDerivAt (fun c' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
      PhiB (I := I) (M := M) a₀ D ε x₀ (c', y))
      (Work.Diff.STE.D.pPhiFunD (E := E)
          (jetPB (I := I) (M := M) a₀ D ε x₀ c (Work.Diff.STE.flatToE (I := I) x₀ y))
        ∘SL Work.Diff.STE.D.psi.FzJetLin (I := I) (M := M) g₀ D ε x₀
            (Work.Diff.STE.flatToE (I := I) x₀ y)) c :=
    ((Work.Diff.STE.D.psi.hasFDerivAt_pPhiFun (E := E) _ hdom).comp c
      (hasFDerivAt_jetPB_FzJetLin (I := I) (M := M) a₀ ha₀ D ε x₀ c hy)).congr_of_eventuallyEq
        (Filter.EventuallyEq.of_eq rfl)
  have h2 : HasFDerivAt (fun c' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
      PhiB (I := I) (M := M) a₀ D ε x₀ (c', y))
      ((fderiv ℝ (PhiB (I := I) (M := M) a₀ D ε x₀) (c, y)) ∘SL
        (ContinuousLinearMap.inl ℝ
          (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
          (Fin (Module.finrank ℝ E) → ℝ))) c :=
    (HasFDerivAt.comp c hF (hasFDerivAt_prodMk_left (𝕜 := ℝ) c y)).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq rfl)
  have hfd : (fderiv ℝ (PhiB (I := I) (M := M) a₀ D ε x₀) (c, y)) ∘SL
        (ContinuousLinearMap.inl ℝ
          (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
          (Fin (Module.finrank ℝ E) → ℝ))
      = Work.Diff.STE.D.pPhiFunD (E := E)
          (jetPB (I := I) (M := M) a₀ D ε x₀ c (Work.Diff.STE.flatToE (I := I) x₀ y))
        ∘SL Work.Diff.STE.D.psi.FzJetLin (I := I) (M := M) g₀ D ε x₀
            (Work.Diff.STE.flatToE (I := I) x₀ y) := by
    rw [← hd.fderiv, h2.fderiv]
  calc (fderiv ℝ (PhiB (I := I) (M := M) a₀ D ε x₀) (c, y))
        (δ, (0 : Fin (Module.finrank ℝ E) → ℝ))
      = ((fderiv ℝ (PhiB (I := I) (M := M) a₀ D ε x₀) (c, y)) ∘SL
          (ContinuousLinearMap.inl ℝ
            (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
            (Fin (Module.finrank ℝ E) → ℝ))) δ := rfl
    _ = (Work.Diff.STE.D.pPhiFunD (E := E)
          (jetPB (I := I) (M := M) a₀ D ε x₀ c (Work.Diff.STE.flatToE (I := I) x₀ y))
        ∘SL Work.Diff.STE.D.psi.FzJetLin (I := I) (M := M) g₀ D ε x₀
            (Work.Diff.STE.flatToE (I := I) x₀ y)) δ := by rw [hfd]
    _ = Work.Diff.STE.D.pPhiFunD (E := E)
          (jetPB (I := I) (M := M) a₀ D ε x₀ c (Work.Diff.STE.flatToE (I := I) x₀ y))
          (Work.Diff.STE.D.psi.FzJetLin (I := I) (M := M) g₀ D ε x₀
            (Work.Diff.STE.flatToE (I := I) x₀ y) δ) := rfl

/-- **The chain rule identity in the form needed by the Lipschitz estimate**: the derivative of
the joint chart DeTurck expression in the direction of a basis vector of the coefficient space is
the linearisation `pPhiFunD` evaluated on the corresponding direction vector. -/
lemma fderiv_PhiB_apply_single (hg : ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Bil (I := I) (M := M)) (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    {y : Fin (Module.finrank ℝ E) → ℝ}
    (hy : Work.Diff.STE.flatToE (I := I) x₀ y ∈ (extChartAt I x₀).target)
    (hdom : jetPB (I := I) (M := M) a₀ D ε x₀ c (Work.Diff.STE.flatToE (I := I) x₀ y)
      ∈ Work.Diff.STE.deTurck.pPhiDom (E := E)) :
    (fderiv ℝ (PhiB (I := I) (M := M) a₀ D ε x₀) (c, y))
        ((Pi.single z' (1 : ℝ) :
            Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
          (0 : Fin (Module.finrank ℝ E) → ℝ))
      = Work.Diff.STE.D.pPhiFunD (E := E)
          (jetPB (I := I) (M := M) a₀ D ε x₀ c (Work.Diff.STE.flatToE (I := I) x₀ y))
          (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε x₀ z'
            (Work.Diff.STE.flatToE (I := I) x₀ y)) :=
  (Fz_fderiv_PhiB (I := I) (M := M) hg a₀ ha₀ D ε x₀ c hy hdom
    (Pi.single z' (1 : ℝ))).trans (by
      rw [Work.Diff.STE.D.psi.FzJetLin_apply, Work.Diff.STE.D.psi.sum_single_smul])

/-- **The representation of the directional integrand through the derivative of the joint
expression.** -/
lemma UfunB_eq_fderiv (hg : ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Bil (I := I) (M := M)) (ha₀ : ChartData (I := I) (M := M) a₀)
    (hs : IsSymm (I := I) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    {y : Fin (Module.finrank ℝ E) → ℝ}
    (hy : Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y ∈ (extChartAt I (D.x₀ z.1)).target)
    (hpos : IsPosF (I := I) (M := M) a₀ D ε c) :
    UfunB (I := I) (M := M) a₀ D ε z z' c y =
      D.psi z.1 y * Real.sqrt (D.dens z.1 y) *
        ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
              (D.e z.1 z.2.1 (D.pt z.1 y))
            * coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
              (D.e z.1 z.2.2.1 (D.pt z.1 y))
            * ((fderiv ℝ (PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c, y))
                ((Pi.single z' (1 : ℝ) :
                    Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
                  (0 : Fin (Module.finrank ℝ E) → ℝ))) j k := by
  rw [UfunB, fderiv_PhiB_apply_single (I := I) (M := M) hg a₀ ha₀ D ε (D.x₀ z.1) z' c hy
    (jetPB_mem_pPhiDom (I := I) (M := M) hg D (D.x₀ z.1) a₀ hs c hpos hy)]

end

end Work.Diff.STE.D.Base
