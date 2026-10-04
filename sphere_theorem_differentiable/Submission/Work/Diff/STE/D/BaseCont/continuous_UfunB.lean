/-
# Continuity of the base-generalised directional integrand `UfunB`

`Work.Diff.STE.D.Base.UfunB a₀ D ε z z' c₀ y` is the derivative of the chart DeTurck expression
`pPhiFun (jetPB a₀ D ε (x₀ z.1) c₀ (flatToE (x₀ z.1) y))` in the direction of the `z'`-th
coefficient, weighted by `ψ (z.1) · √dens (z.1)` and read in the frame of the chart at `x₀ z.1`.

This module is the base-generalised analogue of `Work.Diff.STE.D.psi.continuous_Ufun`: the same
argument, with the background `g₀` replaced by an arbitrary symmetric base section `a₀` (the
foreground being `fore a₀ D ε c₀ = a₀ + genMap D ε c₀`).

The proof has three parts:

* the *weight* `y ↦ D.psi i y * Real.sqrt (D.dens i y)` (which does not involve `a₀` at all) is
  continuous: away from `tsupport (D.χ i)` it vanishes, and on the chart target it is a product of
  continuous functions (`D.hχsm`, `D.hζsm`, `dens_continuousAt_of_mem_target`),
* the *sum* `Σ_{j,k} coordCLM … · coordCLM … · pPhiFunD (jet pair) (direction) j k` is continuous on
  the chart target: the first jet component is smooth (`contDiffOn_chartJetOf` for `g₀`), the second
  is smooth because `a₀` has smooth chart data (`ha₀`, then `chartData_fore`), the direction is
  continuous (`continuousOn_chartJetOf_jSym`), and the evaluated Fréchet derivative of the `C^∞`
  function `pPhiFun` is continuous at the jet pair, which lies in `pPhiDom` by `jetPB_mem_pPhiDom`
  (this is where positivity `hc₀` and symmetry `hs` of `a₀` are used),
* the two are multiplied, using that the support of the weight lies in the chart target.
-/
import Mathlib
import Submission.Work.Diff.STE.D.Base.Defs
import Submission.Work.Diff.STE.D.Base.Jet
import Submission.Work.Diff.STE.D.psi.continuousOn_chartJetOf_jSym
import Submission.Work.Diff.STE.B3.dens_bound_sigma

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D.BaseCont

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

/-- The chart target of the chart at `x₀ i`, read in the flat coordinates. -/
private def chartDom (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  Work.Diff.STE.flatToE (I := I) (D.x₀ i) ⁻¹' (extChartAt I (D.x₀ i)).target

private lemma isOpen_chartDom (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    IsOpen (chartDom (I := I) (M := M) (E := E) D i) :=
  (isOpen_extChartAt_target (I := I) (D.x₀ i)).preimage
    ((Work.Diff.STE.B3.flatToE_contDiff (I := I) (M := M) (D.x₀ i)).continuous)

private lemma tsupport_chi_subset_chartDom (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i : ι₀) : tsupport (D.χ i) ⊆ chartDom D i := D.hχtsup i

/-- A continuous function whose topological support lies in an open set on which `g` is continuous
is globally continuous. -/
private lemma continuous_mul_of_tsupport_subset {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    {U : Set (Fin n → ℝ)} (hf : Continuous f) (hU : IsOpen U) (hfs : tsupport f ⊆ U)
    (hg : ContinuousOn g U) : Continuous (fun y => f y * g y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ tsupport f
  · exact (hf.continuousAt).mul (hg.continuousAt (hU.mem_nhds (hfs hy)))
  · refine ContinuousAt.congr (continuousAt_const (y := (0 : ℝ))) ?_
    have hnb : (tsupport f)ᶜ ∈ 𝓝 y := (isClosed_tsupport f).isOpen_compl.mem_nhds hy
    filter_upwards [hnb] with z hz
    have hzero : f z = 0 := by
      by_contra hne
      exact hz (subset_closure hne)
    simp only [hzero, zero_mul]

/-! ## Continuity of the weight `ψ i · √dens i` -/

private lemma continuous_psi (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    Continuous (D.psi i) := by
  have hU : IsOpen (chartDom (I := I) (M := M) (E := E) D i) := isOpen_chartDom D i
  have hsymm : ContinuousOn (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      (extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y))
      (chartDom D i) :=
    ContinuousOn.comp (f := Work.Diff.STE.flatToE (I := I) (D.x₀ i))
      (g := fun y' : E => (extChartAt I (D.x₀ i)).symm y')
      (s := chartDom D i) (t := (extChartAt I (D.x₀ i)).target)
      (contMDiffOn_extChartAt_symm (I := I) (n := ∞) (D.x₀ i)).continuousOn
      ((Work.Diff.STE.B3.flatToE_contDiff (I := I) (M := M) (D.x₀ i)).continuous.continuousOn)
      (fun y hy => hy)
  have hz : ContinuousOn (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      D.ζ i ((extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y)))
      (chartDom D i) :=
    Continuous.comp_continuousOn (D.hζsm i).continuous hsymm
  have hmain := continuous_mul_of_tsupport_subset (D.hχsm i).continuous hU
    (tsupport_chi_subset_chartDom D i) hz
  change Continuous (fun y : Fin (Module.finrank ℝ E) → ℝ =>
    D.χ i y * D.ζ i ((extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y)))
  exact hmain

private lemma tsupport_psi_subset (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    tsupport (D.psi i) ⊆ chartDom D i := by
  have h1 : Function.support (D.psi i) ⊆ tsupport (D.χ i) := by
    intro y hy
    refine subset_closure (fun h => hy ?_)
    simp only [Work.Diff.STE.B3Data.psi, h, zero_mul]
  calc tsupport (D.psi i) = closure (Function.support (D.psi i)) := rfl
    _ ⊆ closure (tsupport (D.χ i)) := closure_mono h1
    _ = tsupport (D.χ i) := (isClosed_tsupport (D.χ i)).closure_eq
    _ ⊆ chartDom D i := tsupport_chi_subset_chartDom D i

private lemma continuous_psi_dens (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    Continuous (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      D.psi i y * Real.sqrt (D.dens i y)) := by
  have hU : IsOpen (chartDom (I := I) (M := M) (E := E) D i) := isOpen_chartDom D i
  have hdens : ContinuousOn (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Real.sqrt (D.dens i y)) (chartDom D i) := by
    intro y hy
    exact ((Real.continuous_sqrt.continuousAt).comp
      (Work.Diff.STE.B3.dens_continuousAt_of_mem_target D i hy)).continuousWithinAt
  exact continuous_mul_of_tsupport_subset (continuous_psi D i) hU
    (tsupport_psi_subset D i) hdens

/-! ## Continuity of the partial derivative term -/

/-- **The evaluated Fréchet derivative of a `C^1` function is continuous.**  This is stated in the
*evaluated* form (a `MatE`-valued function) rather than for the operator-norm-valued map, which is
what makes it applicable to the jet space of `pPhi`. -/
private lemma continuousAt_fderiv_apply_gen
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Y : Type*} [TopologicalSpace Y]
    {Φ : G → F} {W V : Y → G} {y₀ : Y} (hW : ContinuousAt W y₀) (hV : ContinuousAt V y₀)
    {n : WithTop ENat} (hn : n ≠ 0) (hΦ : ContDiffAt ℝ n Φ (W y₀)) :
    ContinuousAt (fun y => (fderiv ℝ Φ (W y)) (V y)) y₀ :=
  ((hΦ.continuousAt_fderiv hn).comp hW).clm_apply hV

/-- The two coordinate factors, the direction and the evaluated derivative of `pPhiFun`, as
functions of the flat coordinate `y`, are jointly continuous at every point of the chart target.

(All the pieces are proved separately in the body: the jet pair is continuous because `a₀` has
smooth chart data, the direction because the spanning family does, and the evaluated derivative
because `pPhiFun` is `C^∞` on the open set `pPhiDom` to which the jet pair belongs.) -/
private lemma pPhiFunD_continuousAt (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Work.Diff.STE.Bil (I := I) (M := M))
    (ha₀ : Work.Diff.STE.D.ChartData (I := I) (M := M) a₀)
    (hs : Work.Diff.STE.D.IsSymm (I := I) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (i : ι₀)
    (c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hc₀ : Work.Diff.STE.D.Base.IsPosF (I := I) (M := M) a₀ D ε c₀)
    (z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    {u : Fin (Module.finrank ℝ E) → ℝ} (hu : u ∈ chartDom D i)
    (j k : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.D.pPhiFunD (E := E)
        (Work.Diff.STE.D.Base.jetPB (I := I) (M := M) a₀ D ε (D.x₀ i) c₀
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y))
        (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ i) z'
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y)) j k) u := by
  have hO : IsOpen ((extChartAt I (D.x₀ i)).target) := isOpen_extChartAt_target (I := I) (D.x₀ i)
  have hu' : Work.Diff.STE.flatToE (I := I) (D.x₀ i) u ∈ (extChartAt I (D.x₀ i)).target := hu
  have hflat : Continuous (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.flatToE (I := I) (D.x₀ i) y) :=
    (Work.Diff.STE.B3.flatToE_contDiff (I := I) (M := M) (D.x₀ i)).continuous
  have hfrac : ContinuousAt (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.flatToE (I := I) (D.x₀ i) y) u := hflat.continuousAt
  -- the first component of the jet pair
  have hjet1 : ContinuousAt (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y)) u :=
    (((Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i) (hg (D.x₀ i))).continuousOn).continuousAt
      (hO.mem_nhds hu')).comp hfrac
  -- the second component of the jet pair: smooth chart data of the base-generalised foreground
  have hCD : Work.Diff.STE.D.ChartData (I := I) (M := M)
      (Work.Diff.STE.D.Base.fore (I := I) (M := M) a₀ D ε c₀) :=
    Work.Diff.STE.D.Base.chartData_fore (I := I) (M := M) a₀ D ε c₀ ha₀
  have hjet2 : ContinuousAt (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.D.chartJetOf (I := I) (M := M)
        (Work.Diff.STE.D.Base.fore (I := I) (M := M) a₀ D ε c₀)
        (D.x₀ i) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y)) u :=
    (((Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M)
        (Work.Diff.STE.D.Base.fore (I := I) (M := M) a₀ D ε c₀)
        (D.x₀ i) (hCD (D.x₀ i))).continuousOn).continuousAt (hO.mem_nhds hu')).comp hfrac
  have hW : ContinuousAt (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.D.Base.jetPB (I := I) (M := M) a₀ D ε (D.x₀ i) c₀
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y)) u := hjet1.prodMk hjet2
  -- the direction
  have hjet3 : ContinuousAt (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.D.chartJetOf (I := I) (M := M)
        (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z') (D.x₀ i)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y)) u :=
    ((Work.Diff.STE.D.psi.continuousOn_chartJetOf_jSym (I := I) (M := M) D ε (D.x₀ i) z').continuousAt
      (hO.mem_nhds hu')).comp hfrac
  have hV : ContinuousAt (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ i) z'
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y)) u := by
    have h := (continuousAt_const (y := (0 : Work.Diff.EXT.MatE (E := E) ×
      Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E))).prodMk hjet3
    simpa only [Work.Diff.STE.D.jetDir] using h
  -- the derivative of `pPhi` is continuous at the jet pair
  have hmem : Work.Diff.STE.D.Base.jetPB (I := I) (M := M) a₀ D ε (D.x₀ i) c₀
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) u) ∈ Work.Diff.STE.deTurck.pPhiDom E :=
    Work.Diff.STE.D.Base.jetPB_mem_pPhiDom (I := I) (M := M) hg D (D.x₀ i) a₀ hs c₀ hc₀ hu'
  have hcd : ContDiffAt ℝ (∞ : WithTop ENat) (Work.Diff.STE.D.pPhiFun (E := E))
      (Work.Diff.STE.D.Base.jetPB (I := I) (M := M) a₀ D ε (D.x₀ i) c₀
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) u)) :=
    (Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E)).contDiffAt
      ((Work.Diff.STE.D.psi.isOpen_pPhiDom (E := E)).mem_nhds hmem)
  have hgen := continuousAt_fderiv_apply_gen (G := Work.Diff.STE.deTurck.JetPair E)
    (F := Work.Diff.EXT.MatE (E := E)) (Y := Fin (Module.finrank ℝ E) → ℝ)
    (Φ := Work.Diff.STE.D.pPhiFun (E := E))
    (W := fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.D.Base.jetPB (I := I) (M := M) a₀ D ε (D.x₀ i) c₀
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y))
    (V := fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ i) z'
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y))
    (y₀ := u) hW hV (n := ∞) (by simp) hcd
  exact ((continuous_apply k).continuousAt).comp (((continuous_apply j).continuousAt).comp hgen)

/-! ## Continuity of the coordinate terms -/

private lemma coordCLM_continuousOn (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (a : Fin (Module.finrank ℝ E)) (j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
        (D.e i a (D.pt i y))) (chartDom D i) := by
  have h := (Work.Diff.STE.D.psi.contDiffOn_coordCLM_symm (I := I) (M := M) (D.x₀ i) (D.hesm i a) j).continuousOn
  have hcomp := h.comp
    ((Work.Diff.STE.B3.flatToE_contDiff (I := I) (M := M) (D.x₀ i)).continuous.continuousOn)
    (fun y hy => hy)
  refine hcomp.congr (fun y hy => ?_)
  rfl

/-! ## Continuity of the sum -/

private theorem ufun_sum_aux (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Work.Diff.STE.Bil (I := I) (M := M))
    (ha₀ : Work.Diff.STE.D.ChartData (I := I) (M := M) a₀)
    (hs : Work.Diff.STE.D.IsSymm (I := I) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hc₀ : Work.Diff.STE.D.Base.IsPosF (I := I) (M := M) a₀ D ε c₀) :
    ContinuousOn (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
            (D.e z.1 z.2.1 (D.pt z.1 y))
          * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
            (D.e z.1 z.2.2.1 (D.pt z.1 y))
          * (Work.Diff.STE.D.pPhiFunD (E := E)
                (Work.Diff.STE.D.Base.jetPB (I := I) (M := M) a₀ D ε (D.x₀ z.1) c₀
                  (Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y))
                (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ z.1) z'
                  (Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y))) j k)
      (chartDom D z.1) := by
  refine continuousOn_finsetSum _ (fun j _ => ?_)
  refine continuousOn_finsetSum _ (fun k _ => ?_)
  exact ((coordCLM_continuousOn D z.1 z.2.1 j).mul (coordCLM_continuousOn D z.1 z.2.2.1 k)).mul
    (fun y hy => (pPhiFunD_continuousAt hg a₀ ha₀ hs D ε z.1 c₀ hc₀ z' hy j k).continuousWithinAt)

/-! ## The target -/

theorem continuous_UfunB
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Work.Diff.STE.Bil (I := I) (M := M))
    (ha₀ : Work.Diff.STE.D.ChartData (I := I) (M := M) a₀)
    (hs : Work.Diff.STE.D.IsSymm (I := I) a₀)
    (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hc₀ : Work.Diff.STE.D.Base.IsPosF (I := I) (M := M) a₀ D ε c₀) :
    Continuous (Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c₀) := by
  have hW := continuous_psi_dens D z.1
  have hT := ufun_sum_aux hg a₀ ha₀ hs D ε z z' c₀ hc₀
  have hU : IsOpen (chartDom (I := I) (M := M) (E := E) D z.1) := isOpen_chartDom D z.1
  have hsub : tsupport (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      D.psi z.1 y * Real.sqrt (D.dens z.1 y)) ⊆ chartDom D z.1 := by
    have h1 : Function.support (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        D.psi z.1 y * Real.sqrt (D.dens z.1 y)) ⊆ tsupport (D.χ z.1) := by
      intro y hy
      refine subset_closure (fun h => hy ?_)
      simp only [Work.Diff.STE.B3Data.psi, h, zero_mul]
    calc tsupport (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          D.psi z.1 y * Real.sqrt (D.dens z.1 y))
        = closure (Function.support (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          D.psi z.1 y * Real.sqrt (D.dens z.1 y))) := rfl
      _ ⊆ closure (tsupport (D.χ z.1)) := closure_mono h1
      _ = tsupport (D.χ z.1) := (isClosed_tsupport (D.χ z.1)).closure_eq
      _ ⊆ chartDom D z.1 := tsupport_chi_subset_chartDom D z.1
  have hmain := continuous_mul_of_tsupport_subset hW hU hsub hT
  exact hmain

end

end Work.Diff.STE.D.BaseCont
