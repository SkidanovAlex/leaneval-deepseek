/-
# Layer D: the chart `2`-jet of the Galerkin family is affine in the coefficients

`Work.Diff.STE.D.genMap D ε c = Σ_z c z • jSym D ε z` is a *real linear* combination of the
symmetrised spanning family, so its chart matrix is the corresponding linear combination of the
chart matrices of the summands (plus the background metric `g₀`).  The present file proves that
this survives the passage to the spatial `2`-jet of the chart matrix:

`chartJetOf (g₀ + genMap D ε c) x₀ y = chartJetOf g₀.inner x₀ y + Σ_z c z • chartJetOf (jSym D ε z) x₀ y`.

The mathematical content is entirely formal: `chartJetOf h x₀ y` is the `jet2` of the chart matrix
of `h` at the chart point `y`, `jet2` is built from `fderiv`, and `fderiv` is additive/homogeneous —
the only care needed is that the *pieces* involved are smooth on the (open) chart target, so that
the identities `fderiv (u + v) = fderiv u + fderiv v` (and the same one level up) hold on a
neighbourhood of `y`.  That smoothness is `Work.Diff.STE.D.ChartData`, supplied by the caller
(`hg` for the background metric, `ChartData_genMap` for the Galerkin family).

The helper lemmas `jet2_slice_add`, `jet2_slice_smul` and `jet2_slice_const` are the general
linearity statements for the spatial `2`-jet of `y ↦ u y`; `chartJetOf_add_of_chartData`,
`chartJetOf_smul_of_chartData` and `chartJetOf_zero` are their section-level counterparts.
-/
import Mathlib
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.STE.D.ChartData_genMap
import Submission.Work.Diff.STE.D.ChartData_jVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter Set

namespace Work.Diff.STE.D.psi

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-! ## 1. Linearity of the spatial `2`-jet on the model space -/

section Jet2Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The spatial `2`-jet is additive** on an open set on which both functions are smooth. -/
lemma jet2_slice_add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u v : E → F} {s : Set E} (hs : IsOpen s) {y : E} (hy : y ∈ s)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u s) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v s) :
    Work.Diff.EXT.jet2 (E := E) (fun p : ℝ × E => u p.2 + v p.2) (0, y) =
      Work.Diff.EXT.jet2 (E := E) (fun p : ℝ × E => u p.2) (0, y)
        + Work.Diff.EXT.jet2 (E := E) (fun p : ℝ × E => v p.2) (0, y) := by
  have htop : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hya : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ u y' := by
    filter_upwards [hs.mem_nhds hy] with y' hy'
    exact (hu.differentiableOn htop).differentiableAt (hs.mem_nhds hy')
  have hyb : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ v y' := by
    filter_upwards [hs.mem_nhds hy] with y' hy'
    exact (hv.differentiableOn htop).differentiableAt (hs.mem_nhds hy')
  have hdu : DifferentiableAt ℝ u y := (hu.differentiableOn htop).differentiableAt (hs.mem_nhds hy)
  have hdv : DifferentiableAt ℝ v y := (hv.differentiableOn htop).differentiableAt (hs.mem_nhds hy)
  have hdu' : DifferentiableAt ℝ (fderiv ℝ u) y :=
    ((ContDiffOn.fderiv_of_isOpen hu hs (m := (⊤ : ℕ∞)) (by simp)).differentiableOn htop).differentiableAt
      (hs.mem_nhds hy)
  have hdv' : DifferentiableAt ℝ (fderiv ℝ v) y :=
    ((ContDiffOn.fderiv_of_isOpen hv hs (m := (⊤ : ℕ∞)) (by simp)).differentiableOn htop).differentiableAt
      (hs.mem_nhds hy)
  have hderiv : (fun y' => fderiv ℝ (fun y'' => u y'' + v y'') y')
      =ᶠ[𝓝 y] (fderiv ℝ u + fderiv ℝ v) := by
    filter_upwards [hya, hyb] with y' h1 h2
    exact fderiv_add h1 h2
  simp only [Work.Diff.EXT.jet2, Prod.mk_add_mk]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · exact fderiv_add hdu hdv
  · rw [Filter.EventuallyEq.fderiv_eq hderiv, fderiv_add hdu' hdv']

/-- **The spatial `2`-jet is homogeneous** on an open set on which the function is smooth. -/
lemma jet2_slice_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (r : ℝ)
    {u : E → F} {s : Set E} (hs : IsOpen s) {y : E} (hy : y ∈ s)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u s) :
    Work.Diff.EXT.jet2 (E := E) (fun p : ℝ × E => r • u p.2) (0, y) =
      r • Work.Diff.EXT.jet2 (E := E) (fun p : ℝ × E => u p.2) (0, y) := by
  have htop : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hyu : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ u y' := by
    filter_upwards [hs.mem_nhds hy] with y' hy'
    exact (hu.differentiableOn htop).differentiableAt (hs.mem_nhds hy')
  have hdu : DifferentiableAt ℝ u y := (hu.differentiableOn htop).differentiableAt (hs.mem_nhds hy)
  have hdu' : DifferentiableAt ℝ (fderiv ℝ u) y :=
    ((ContDiffOn.fderiv_of_isOpen hu hs (m := (⊤ : ℕ∞)) (by simp)).differentiableOn htop).differentiableAt
      (hs.mem_nhds hy)
  have hderiv : (fun y' => fderiv ℝ (fun y'' => r • u y'') y')
      =ᶠ[𝓝 y] (fun y' => r • fderiv ℝ u y') := by
    filter_upwards [hyu] with y' h1
    exact fderiv_fun_const_smul h1 r
  simp only [Work.Diff.EXT.jet2, Prod.smul_mk, Prod.mk.injEq]
  refine ⟨trivial, ?_, ?_⟩
  · exact fderiv_fun_const_smul hdu r
  · rw [Filter.EventuallyEq.fderiv_eq hderiv, fderiv_fun_const_smul hdu' r]

/-- **The spatial `2`-jet of a constant function.** -/
lemma jet2_slice_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : F)
    (p : ℝ × E) :
    Work.Diff.EXT.jet2 (E := E) (fun _ : ℝ × E => c) p = (c, 0, 0) := by
  simp only [Work.Diff.EXT.jet2, fderiv_fun_const, fderiv_zero]
  exact Prod.ext rfl (Prod.ext rfl rfl)

end Jet2Linear

/-! ## 2. Linearity of the chart jet on the manifold -/

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]

/-- The chart matrix of a pointwise sum of sections is the pointwise sum of the chart matrices. -/
lemma chartMatOf_add (h k : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M) :
    Work.Diff.STE.D.chartMatOf (I := I) (M := M) (h + k) x₀ =
      fun y' => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y'
        + Work.Diff.STE.D.chartMatOf (I := I) (M := M) k x₀ y' := by
  funext y' i j
  simp only [Work.Diff.STE.D.chartMatOf_apply, Pi.add_apply, add_apply]

/-- The chart matrix of a scalar multiple of a section is the scalar multiple of the chart
matrix. -/
lemma chartMatOf_smul (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M) (r : ℝ) :
    Work.Diff.STE.D.chartMatOf (I := I) (M := M) (r • h) x₀ =
      fun y' => r • Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y' := by
  funext y' i j
  simp only [Work.Diff.STE.D.chartMatOf_apply, Pi.smul_apply, smul_apply]

/-- The chart matrix of the zero section vanishes. -/
lemma chartMatOf_zero (x₀ : M) :
    Work.Diff.STE.D.chartMatOf (I := I) (M := M) (0 : Work.Diff.STE.Bil (I := I) (M := M)) x₀ =
      fun _ : E => (0 : Work.Diff.EXT.MatE (E := E)) := by
  funext y' i j
  simp only [Work.Diff.STE.D.chartMatOf_apply, Pi.zero_apply, zero_apply]

/-- **The chart jet is additive** for sections whose chart matrices are smooth on the chart
target. -/
lemma chartJetOf_add_of_chartData (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (h k : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (hk : Work.Diff.STE.D.ChartData (I := I) (M := M) k) :
    Work.Diff.STE.D.chartJetOf (I := I) (M := M) (h + k) x₀ y =
      Work.Diff.STE.D.chartJetOf (I := I) (M := M) h x₀ y
        + Work.Diff.STE.D.chartJetOf (I := I) (M := M) k x₀ y := by
  have hs : IsOpen (extChartAt I x₀).target := isOpen_extChartAt_target x₀
  rw [Work.Diff.STE.D.chartJetOf_eq, Work.Diff.STE.D.chartJetOf_eq,
    Work.Diff.STE.D.chartJetOf_eq]
  rw [chartMatOf_add]
  exact jet2_slice_add (F := Work.Diff.EXT.MatE (E := E)) hs hy (hh x₀) (hk x₀)

/-- **The chart jet is homogeneous** for sections whose chart matrix is smooth on the chart
target. -/
lemma chartJetOf_smul_of_chartData (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (r : ℝ) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) :
    Work.Diff.STE.D.chartJetOf (I := I) (M := M) (r • h) x₀ y =
      r • Work.Diff.STE.D.chartJetOf (I := I) (M := M) h x₀ y := by
  have hs : IsOpen (extChartAt I x₀).target := isOpen_extChartAt_target x₀
  rw [Work.Diff.STE.D.chartJetOf_eq, Work.Diff.STE.D.chartJetOf_eq]
  rw [chartMatOf_smul]
  exact jet2_slice_smul (F := Work.Diff.EXT.MatE (E := E)) r hs hy (hh x₀)

/-- **The chart jet of the zero section vanishes.** -/
lemma chartJetOf_zero (x₀ : M) (y : E) :
    Work.Diff.STE.D.chartJetOf (I := I) (M := M)
      (0 : Work.Diff.STE.Bil (I := I) (M := M)) x₀ y = 0 := by
  rw [Work.Diff.STE.D.chartJetOf_eq]
  rw [chartMatOf_zero]
  show Work.Diff.EXT.jet2 (E := E) (fun _ : ℝ × E => (0 : Work.Diff.EXT.MatE (E := E)))
    (0, y) = 0
  rw [jet2_slice_const]
  rfl

end Chart

/-! ## 3. The chart jet of the Galerkin family -/

theorem chartJetOf_genMap_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    Work.Diff.STE.D.chartJetOf (I := I) (M := M)
        (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) x₀ y
      = Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y
        + ∑ z, c z • Work.Diff.STE.D.chartJetOf (I := I) (M := M)
            (jSym (I := I) (M := M) D ε z) x₀ y := by
  classical
  -- the spanning vectors of the Galerkin family have smooth chart data
  have hjFamily : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      Work.Diff.STE.D.ChartData (I := I) (M := M)
        (Work.Diff.STE.B3.jFamily (I := I) (M := M) D ε z) := by
    intro z
    simpa only [Work.Diff.STE.B3.jFamily] using
      GenMap.jVec_chartData (I := I) (M := M) D ε z.1 z.2.1 z.2.2.1 z.2.2.2
  have hjSym : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      Work.Diff.STE.D.ChartData (I := I) (M := M) (jSym (I := I) (M := M) D ε z) := by
    intro z
    rw [jSym]
    exact GenMap.chartData_add (I := I) (M := M) (hjFamily z)
      (hjFamily (idxSwap (E := E) (ι₀ := ι₀) ε z))
  have hsummand : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      Work.Diff.STE.D.ChartData (I := I) (M := M)
        (c z • jSym (I := I) (M := M) D ε z) :=
    fun z => GenMap.chartData_smul (I := I) (M := M) (c z) (hjSym z)
  -- the jet of a finite sum of the summands
  have hsum : ∀ t : Finset (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε),
      Work.Diff.STE.D.chartJetOf (I := I) (M := M)
          (∑ z ∈ t, c z • jSym (I := I) (M := M) D ε z) x₀ y
        = ∑ z ∈ t, c z • Work.Diff.STE.D.chartJetOf (I := I) (M := M)
            (jSym (I := I) (M := M) D ε z) x₀ y := by
    intro t
    induction t using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        exact chartJetOf_zero (I := I) (M := M) x₀ y
    | insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [chartJetOf_add_of_chartData (I := I) (M := M) x₀ hy
          (c a • jSym (I := I) (M := M) D ε a)
          (∑ z ∈ t, c z • jSym (I := I) (M := M) D ε z)
          (hsummand a)
          (GenMap.chartData_finset_sum (I := I) (M := M) t
            (fun z => c z • jSym (I := I) (M := M) D ε z) (fun z _ => hsummand z))]
        rw [chartJetOf_smul_of_chartData (I := I) (M := M) x₀ hy (c a)
          (jSym (I := I) (M := M) D ε a) (hjSym a), ih]
  -- assembly
  rw [show addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)
      = g₀.inner + genMap (I := I) (M := M) D ε c from rfl]
  rw [chartJetOf_add_of_chartData (I := I) (M := M) x₀ hy (g₀.inner)
    (genMap (I := I) (M := M) D ε c) hg (ChartData_genMap D ε c)]
  rw [show genMap (I := I) (M := M) D ε c
      = ∑ z ∈ Finset.univ, c z • jSym (I := I) (M := M) D ε z from rfl]
  rw [hsum Finset.univ]

end Work.Diff.STE.D.psi
