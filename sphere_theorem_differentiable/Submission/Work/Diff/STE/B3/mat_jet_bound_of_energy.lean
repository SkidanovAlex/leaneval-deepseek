import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.dens_lower_bound
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.B3.Rstar_R_eq_zeta_sq_free
import Submission.Work.Diff.STE.B3.BPairSmooth
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.flat.jetP_iteratedFDeriv_bound
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.STE.D.transMap_contDiffAt
import Submission.Work.Diff.STE.B3.pdList_le_sqrt_CSq
import Submission.Work.Diff.STE.B3.CSq_le_ENormSq_of_periodization
import Submission.Work.Diff.STE.B3.mat_eq_inv_zeta_sum
import Submission.Work.Diff.STE.B3.pdVec_mul_comp_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The jet bound for the B3 chart matrices in terms of the physical energy

For the Layer B3 data `D` (`Work.Diff.STE.B3Data`, `B3/Data.lean`) and `2 m + n < 2 k₀` (where
`n = finrank ℝ E`), the `m`-th flat jet of the chart matrix `D.mat i h c d` of a section `h` with
smooth chart data is bounded by `C (1 + √(D.ENormB k₀ h))`, uniformly in the section `h` and in the
point `z` of the `2σ i`-ball.

The proof is the *covering* refinement of `Work.Diff.STE.Lead.mat_jet_bound` (which controls the jets
on the region where the localised weight `D.psi i` is bounded below).  Since `Σ_i ζ_i² = 1`, at
every point `p = D.pt i z` there is a chart `j` with `ζ_j p ≥ 1/√(card ι₀)`; the pointwise identity
`Work.Diff.STE.B3.mat_eq_inv_zeta_sum` expresses `mat_i` in terms of the localised component `R_j`
and a *smooth* coefficient (the frames `e i`, `e j` are both `g₀`-orthonormal there), and the
Sobolev bound `Work.Diff.STE.B3.pdList_le_sqrt_CSq` +
`Work.Diff.STE.B3.CSq_le_ENormSq_of_periodization` control the jets of `R_j` by `√(ENormB k₀ h)`.

Note that no `T2Space M` is assumed (unlike in the `Lead/` development), which is why the density
and component smoothness lemmas below are reproved in the `T2`-free setting.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. The density of the B3 charts is positive and smooth (`T2`-free) -/

/-- The chart matrix `chartMatFun g x₀` of a smooth metric is `C^∞` at every chart coordinate `y` in
the target of the extended chart at `x₀`, without the `T2Space M` hypothesis of
`Work.Diff.EXT.kz_contDiffAt_chartMatFun`. -/
private theorem chartMatFun_contDiffAt_free (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.EXT.chartMatFun (I := I) g x₀) y := by
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm y :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy)
  have hpair : ∀ i j : Fin (Module.finrank ℝ E), ContMDiffAt I (𝓘(ℝ, ℝ)) (⊤ : ℕ∞)
      (fun z : M => g.inner z
        (Submission.Geodesic.frameVector (I := I) x₀ z (Work.Diff.EXT.bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ z (Work.Diff.EXT.bB (E := E) j)))
      ((extChartAt I x₀).symm y) :=
    fun i j => contMDiffAt_gmat_coeff' (I := I) (M := M) g x₀ hp i j
  refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => ?_))
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun y : E => g.inner ((extChartAt I x₀).symm y)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
          (Work.Diff.EXT.bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
          (Work.Diff.EXT.bB (E := E) j))) y :=
    (hpair i j).comp y hsymm
  exact hcomp.contDiffAt

/-- `D.DensGood i`, without the `T2Space M` hypothesis of `Work.Diff.STE.B3.densGood`. -/
private theorem densGood_free (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) : D.DensGood i := by
  intro z hz
  have hsymm : (extChartAt I (D.x₀ i)).symm (flatToE (I := I) (D.x₀ i) z)
      ∈ (chartAt H (D.x₀ i)).source := by
    rw [← extChartAt_source (I := I) (D.x₀ i)]
    exact PartialEquiv.map_target (extChartAt I (D.x₀ i)) hz
  have hpd : (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i)
      ((extChartAt I (D.x₀ i)).symm (flatToE (I := I) (D.x₀ i) z)))).PosDef :=
    Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ (D.x₀ i) hsymm
  have hdetpos : 0 < (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
      (flatToE (I := I) (D.x₀ i) z))).det := by
    have := hpd.det_pos
    rwa [show Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i)
          ((extChartAt I (D.x₀ i)).symm (flatToE (I := I) (D.x₀ i) z))
        = Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (flatToE (I := I) (D.x₀ i) z) from rfl] at this
  refine ⟨?_, ?_⟩
  · simpa only [Work.Diff.STE.B3Data.dens] using Real.sqrt_pos.mpr hdetpos
  · have hflat : ContDiffAt ℝ (⊤ : ℕ∞) (flatToE (I := I) (D.x₀ i)) z :=
      (contDiff_flatToE (I := I) (x₀ := D.x₀ i)).contDiffAt
    have hchart : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i))
        (flatToE (I := I) (D.x₀ i) z) :=
      chartMatFun_contDiffAt_free (I := I) (M := M) g₀ (D.x₀ i) hz
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (flatToE (I := I) (D.x₀ i) z)) z :=
      hchart.comp z hflat
    have hdet : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (flatToE (I := I) (D.x₀ i) z))).det) z :=
      (Work.Diff.STE.B3.contDiff_det_of (n := Module.finrank ℝ E)).contDiffAt.comp z hcomp
    have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => Real.sqrt ((Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (flatToE (I := I) (D.x₀ i) z))).det)) z :=
      (Real.contDiffAt_sqrt (ne_of_gt hdetpos)).comp z hdet
    exact hsqrt

/-! ## 2. Smoothness of the chart matrix of a section with smooth chart data (`T2`-free) -/

/-- Smoothness of the frame matrix of a section with `ChartData`, without `T2Space M`. -/
private theorem frameMat_contMDiffAt_of_chartData_free {h : Bil (I := I) (M := M)}
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (x₀ : M) :
    ContMDiffAt I (𝓘(ℝ, Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun x : M => Work.Diff.EXT.frameMat (I := I) x₀ x (h x)) x₀ := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.EXT.frameMat (I := I) x₀ ((extChartAt I x₀).symm y)
        (h ((extChartAt I x₀).symm y))) ((extChartAt I x₀) x₀) :=
    (hh x₀).contDiffAt (extChartAt_target_mem_nhds x₀)
  have h2 : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun y : E => Work.Diff.EXT.frameMat (I := I) x₀ ((extChartAt I x₀).symm y)
        (h ((extChartAt I x₀).symm y))) ((extChartAt I x₀) x₀) := h1.contMDiffAt
  have h3 := h2.comp x₀ (contMDiffAt_extChartAt (I := I) (x := x₀))
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds (chartAt H x₀).open_source (mem_chart_source H x₀)]
    with x hx
  have hx' : x ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  simp only [Function.comp_apply]
  rw [show (extChartAt I x₀).symm ((extChartAt I x₀) x) = x
    from (extChartAt I x₀).left_inv hx']

/-- Smoothness of the section of the bundle of bilinear forms, without `T2Space M`. -/
private theorem section_contMDiffAt_of_chartData_free {h : Bil (I := I) (M := M)}
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (x₀ : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (h x)) x₀ :=
  Work.Diff.STE.Man.section_contMDiffAt_of_frameMat (I := I) (x₀ := x₀) (γ := h)
    (frameMat_contMDiffAt_of_chartData_free hh x₀)

/-- The chart matrix in the coordinate frame is smooth on the chart target, without `T2Space M`. -/
private theorem chartMat_contDiffOn_of_chartData (D : B3Data (I := I) (M := M) ι₀ g₀)
    (h : Bil (I := I) (M := M)) (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart i h a b) (extChartAt I (D.x₀ i)).target := by
  have hsec : ∀ x : M, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (h x)) x :=
    fun x => section_contMDiffAt_of_chartData_free (I := I) (M := M) hh x
  have hmat : ContMDiffOn I 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun x : M => h x (D.e i a x) (D.e i b x)) univ := by
    intro x _
    have hψ := (hsec x).contMDiffWithinAt (s := univ)
    have hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i a)) univ x :=
      (D.hesm i a).contMDiffAt.contMDiffWithinAt
    have hw : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i b)) univ x :=
      (D.hesm i b).contMDiffAt.contMDiffWithinAt
    have hres := hψ.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hv hw
    simp only [contMDiffWithinAt_totalSpace] at hres
    exact hres.2
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun y : E => h ((extChartAt I (D.x₀ i)).symm y)
        (D.e i a ((extChartAt I (D.x₀ i)).symm y))
        (D.e i b ((extChartAt I (D.x₀ i)).symm y))) (extChartAt I (D.x₀ i)).target :=
    hmat.comp (contMDiffOn_extChartAt_symm (I := I) (x := D.x₀ i) (n := (⊤ : ℕ∞)))
      (fun y _ => mem_univ _)
  exact hcomp.contDiffOn

/-- Smoothness of the localised component `D.R i h a b` from `ChartData h`, without `T2Space M`. -/
private theorem R_contDiff_of_chartData' (D : B3Data (I := I) (M := M) ι₀ g₀)
    (h : Bil (I := I) (M := M)) (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) : ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) :=
  D.R_contDiff i h a b (densGood_free (I := I) (M := M) D i)
    (chartMat_contDiffOn_of_chartData D h hh i a b)

/-- The periodised localised component is smooth and periodic, without `T2Space M`. -/
private theorem Rper_contDiff_periodic_of_chartData (D : B3Data (I := I) (M := M) ι₀ g₀)
    (h : Bil (I := I) (M := M)) (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (D.Rper i h a b) ∧ Periodic1 (D.Rper i h a b) :=
  D.Rper_contDiff_periodic i h a b (densGood_free (I := I) (M := M) D i)
    (chartMat_contDiffOn_of_chartData D h hh i a b)

/-! ## 3. Congruence lemmas for iterated partial derivatives -/

/-- Iterated complex partial derivatives of eventually equal functions agree. -/
private lemma pdList_eventuallyEq_of_eventuallyEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : (ι → ℝ) → ℂ} {z : ι → ℝ} (h : f =ᶠ[𝓝 z] g) :
    ∀ l : List ι, pdList l f =ᶠ[𝓝 z] pdList l g := by
  intro l
  induction l with
  | nil => exact h
  | cons i l ih =>
    have hfd : fderiv ℝ (pdList l f) =ᶠ[𝓝 z] fderiv ℝ (pdList l g) := ih.fderiv
    filter_upwards [hfd] with y hy
    exact congrArg (fun (L : (ι → ℝ) →L[ℝ] ℂ) => L (Pi.single i 1)) hy

/-- Iterated complex partial derivatives of eventually equal functions agree at the point. -/
private lemma pdList_congr_of_eventuallyEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : (ι → ℝ) → ℂ} {z : ι → ℝ} (h : f =ᶠ[𝓝 z] g) (l : List ι) :
    pdList l f z = pdList l g z :=
  (pdList_eventuallyEq_of_eventuallyEq h l).eq_of_nhds

/-- Iterated real partial derivatives of eventually equal functions agree. -/
private lemma pdRList_eventuallyEq_of_eventuallyEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : (ι → ℝ) → ℝ} {z : ι → ℝ} (h : f =ᶠ[𝓝 z] g) :
    ∀ l : List ι, pdRList l f =ᶠ[𝓝 z] pdRList l g := by
  intro l
  induction l with
  | nil => exact h
  | cons i l ih =>
    have hfd : fderiv ℝ (pdRList l f) =ᶠ[𝓝 z] fderiv ℝ (pdRList l g) := ih.fderiv
    filter_upwards [hfd] with y hy
    exact congrArg (fun (L : (ι → ℝ) →L[ℝ] ℝ) => L (Pi.single i 1)) hy

/-- Iterated real partial derivatives of eventually equal functions agree at the point. -/
private lemma pdRList_congr_of_eventuallyEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : (ι → ℝ) → ℝ} {z : ι → ℝ} (h : f =ᶠ[𝓝 z] g) (l : List ι) :
    pdRList l f z = pdRList l g z :=
  (pdRList_eventuallyEq_of_eventuallyEq h l).eq_of_nhds

/-! ## 4. Multiplication by a bump supported in an open set -/

/-- If `f` is `C^∞` on an open set `U` and the closed support of `g` lies in `U`, then `f * g` is
`C^∞` everywhere. -/
private lemma contDiff_mul_of_tsupport_subset {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {f g : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hsupp : tsupport g ⊆ U) : ContDiff ℝ (⊤ : ℕ∞) (fun z => f z * g z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · exact ((hf.contDiffAt (hU.mem_nhds hz)).mul hg.contDiffAt)
  · have hg0 : g =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      have hz' : z ∉ tsupport g := fun h => hz (hsupp h)
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hz'] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hfg : (fun y => f y * g y) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hg0] with y hy
      rw [hy, mul_zero]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hfg

/-- If `φ` is `C^∞` on an open set `U` and the closed support of `g` lies in `U`, then `g • φ` is
`C^∞` everywhere. -/
private lemma contDiff_smul_of_tsupport_subset {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {φ : (Fin n → ℝ) → (Fin n → ℝ)} {g : (Fin n → ℝ) → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsupp : tsupport g ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => g z • φ z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · exact (hg.contDiffAt.smul (hφ.contDiffAt (hU.mem_nhds hz)))
  · have hg0 : g =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      have hz' : z ∉ tsupport g := fun h => hz (hsupp h)
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hz'] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hfg : (fun y => g y • φ y) =ᶠ[𝓝 z] fun _ => (0 : Fin n → ℝ) := by
      filter_upwards [hg0] with y hy
      rw [hy, zero_smul]
    exact (contDiffAt_const (c := (0 : Fin n → ℝ))).congr_of_eventuallyEq hfg

/-! ## 5. Derivative bounds on a compact set -/

/-- The iterated derivatives of a `C^∞` function are uniformly bounded on a compact set. -/
private lemma exists_bound_iteratedFDeriv_compact {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (Fin n → ℝ) → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : ℕ), i ≤ m → ∀ z ∈ K, ‖iteratedFDeriv ℝ i f z‖ ≤ C := by
  intro m
  have hcont : ∀ i : ℕ, Continuous fun z : Fin n → ℝ => ‖iteratedFDeriv ℝ i f z‖ := fun i =>
    (hf.continuous_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top : ((i : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).norm
  choose B hB using fun i : ℕ => hK.exists_bound_of_continuousOn (hcont i).continuousOn
  refine ⟨∑ i ∈ Finset.range (m + 1), |B i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro i hi z hz
  have hb : ‖iteratedFDeriv ℝ i f z‖ ≤ B i := by
    have h := hB i z hz
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
  have h1 : ‖iteratedFDeriv ℝ i f z‖ ≤ |B i| := hb.trans (le_abs_self (B i))
  exact h1.trans (Finset.single_le_sum (f := fun i => |B i|) (fun j _ => abs_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))

/-- The values of the iterated derivatives of a `C^∞` function, evaluated on the standard basis
tuples, are uniformly bounded on a compact set. -/
private lemma exists_bound_pdVec_compact {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (l : Fin i → Fin n) (z : Fin n → ℝ), z ∈ K → ‖pdVec i l f z‖ ≤ C := by
  intro i
  have hcont : ∀ l : Fin i → Fin n, Continuous (fun z : Fin n → ℝ => ‖pdVec i l f z‖) :=
    fun l => (continuous_pdVec i l f (hf.of_le
      (WithTop.coe_le_coe.mpr le_top : ((i : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞)))).norm
  choose B hB using fun l : Fin i → Fin n => hK.exists_bound_of_continuousOn (hcont l).continuousOn
  refine ⟨∑ l : Fin i → Fin n, |B l|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun l z hz => ?_⟩
  have hb : ‖pdVec i l f z‖ ≤ B l := by
    have h := hB l z hz
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
  have h1 : ‖pdVec i l f z‖ ≤ |B l| := hb.trans (le_abs_self (B l))
  exact h1.trans (Finset.single_le_sum (f := fun l => |B l|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ l))

/-! ## 6. The jet bound for the localised components in terms of the energy -/

/-- **The iterated jets of the localised component `D.R j h a b` are controlled by the physical
energy.**  On the `σ j`-ball (so that the flat coordinate lies in the open unit cube, where the
periodisation agrees with the component), the Sobolev bound `pdList_le_sqrt_CSq` and the
coefficient/energy comparison `CSq_le_ENormSq_of_periodization` give the bound in terms of
`√(D.ENormB k₀ h)`. -/
private theorem R_jet_bound (D : B3Data (I := I) (M := M) ι₀ g₀) (k₀ m : ℕ)
    (hm : 2 * m + Module.finrank ℝ E < 2 * k₀) (hk : 1 ≤ k₀)
    (hn : 1 ≤ Module.finrank ℝ E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Bil (I := I) (M := M))
      (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (j : ι₀) (a b : Fin (Module.finrank ℝ E)) (l : List (Fin (Module.finrank ℝ E)))
      (hl : l.length ≤ m) (w : Fin (Module.finrank ℝ E) → ℝ), ‖w‖ ≤ D.σ j →
      |pdRList l (D.R j h a b) w| ≤ C * Real.sqrt (D.ENormB k₀ h) := by
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    pdList_le_sqrt_CSq (ι := Fin (Module.finrank ℝ E)) k₀ m
      (by rw [Fintype.card_fin]; omega)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, hn⟩⟩
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    CSq_le_ENormSq_of_periodization (ι := Fin (Module.finrank ℝ E)) k₀ hk
  refine ⟨C₁ * Real.sqrt C₂, mul_nonneg hC₁_nn (Real.sqrt_nonneg _), ?_⟩
  intro h hh j a b l hl w hw
  have hsmR : ContDiff ℝ (⊤ : ℕ∞) (D.R j h a b) := R_contDiff_of_chartData' D h hh j a b
  obtain ⟨hsmP, hperP⟩ := Rper_contDiff_periodic_of_chartData D h hh j a b
  set Fc : (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun y => ((D.R j h a b y : ℝ) : ℂ) with hFc
  have hsmC : ContDiff ℝ (⊤ : ℕ∞) Fc := by
    rw [hFc]; exact Complex.ofRealCLM.contDiff.comp hsmR
  have hsuppC : Function.support Fc ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    refine D.R_support j h a b ?_
    rw [Function.mem_support] at hz ⊢
    intro hz0
    exact hz (by rw [hFc]; simp only; rw [hz0]; norm_num)
  have hperPeq : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      D.Rper j h a b z = ∑' m : Fin (Module.finrank ℝ E) → ℤ, Fc (z + iVec m) :=
    fun z => rfl
  have hw8 : ∀ k : Fin (Module.finrank ℝ E), |w k| ≤ 1 / 8 := by
    intro k
    have h1 : |w k| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w k
    have h2 : D.σ j ≤ 1 / 8 := by have := D.hσ2 j; linarith
    linarith
  have hev : Fc =ᶠ[𝓝 w] D.Rper j h a b := by
    refine Filter.eventually_iff_exists_mem.mpr
      ⟨Metric.ball w (1 / 4), Metric.ball_mem_nhds w (by norm_num), fun y hy => ?_⟩
    have hyc : ∀ k : Fin (Module.finrank ℝ E), y k ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      intro k
      have h1 : |y k - w k| ≤ ‖y - w‖ := by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (y - w) k
      have h2 : ‖y - w‖ < 1 / 4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
      have h4 := abs_lt.mp (lt_of_le_of_lt h1 h2)
      have h5 := abs_le.mp (hw8 k)
      rw [Set.mem_Ioo]
      constructor <;> linarith [h4.1, h4.2, h5.1, h5.2]
    exact (D.Rper_eq_R j h a b hyc).symm
  have hcongr : pdList l Fc w = pdList l (D.Rper j h a b) w :=
    pdList_congr_of_eventuallyEq hev l
  have hcsq : CSq k₀ (fourierCoeff (D.Rper j h a b)) ≤ C₂ * ENormSq k₀ (D.Rper j h a b) :=
    hC₂ Fc (D.Rper j h a b) hsmC hsuppC hsmP hperP hperPeq
  have hE : ENormSq k₀ (D.Rper j h a b) ≤ D.ENormB k₀ h := by
    have hnn : ∀ (i : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
        0 ≤ ENormSq k₀ (D.Rper i h a' b') := fun i a' b' =>
      Work.Diff.STE.flat.ENormSq_nonneg k₀ _
    simp only [B3Data.ENormB]
    exact (Finset.single_le_sum (f := fun b' => ENormSq k₀ (D.Rper j h a b'))
            (fun b' _ => hnn j a b') (Finset.mem_univ b)).trans
          ((Finset.single_le_sum (f := fun a' => ∑ b', ENormSq k₀ (D.Rper j h a' b'))
            (fun a' _ => Finset.sum_nonneg fun b' _ => hnn j a' b')
            (Finset.mem_univ a)).trans
          (Finset.single_le_sum (f := fun i => ∑ a', ∑ b', ENormSq k₀ (D.Rper i h a' b'))
            (fun i _ => Finset.sum_nonneg fun a' _ =>
              Finset.sum_nonneg fun b' _ => hnn i a' b')
            (Finset.mem_univ j)))
  have hsq : Real.sqrt (CSq k₀ (fourierCoeff (D.Rper j h a b)))
      ≤ Real.sqrt C₂ * Real.sqrt (D.ENormB k₀ h) := by
    calc Real.sqrt (CSq k₀ (fourierCoeff (D.Rper j h a b)))
        ≤ Real.sqrt (C₂ * ENormSq k₀ (D.Rper j h a b)) := Real.sqrt_le_sqrt hcsq
      _ = Real.sqrt C₂ * Real.sqrt (ENormSq k₀ (D.Rper j h a b)) := Real.sqrt_mul hC₂_nn _
      _ ≤ Real.sqrt C₂ * Real.sqrt (D.ENormB k₀ h) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (Real.sqrt_nonneg _)
  calc |pdRList l (D.R j h a b) w|
      = ‖((pdRList l (D.R j h a b) w : ℝ) : ℂ)‖ := by
          simp only [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖pdList l Fc w‖ := by rw [hFc]; rw [cm_pdList_ofReal_smooth l (D.R j h a b) hsmR]
    _ = ‖pdList l (D.Rper j h a b) w‖ := by rw [hcongr]
    _ ≤ C₁ * Real.sqrt (CSq k₀ (fourierCoeff (D.Rper j h a b))) := hC₁ _ hsmP hperP l hl w
    _ ≤ C₁ * (Real.sqrt C₂ * Real.sqrt (D.ENormB k₀ h)) :=
          mul_le_mul_of_nonneg_left hsq hC₁_nn
    _ = C₁ * Real.sqrt C₂ * Real.sqrt (D.ENormB k₀ h) := by ring


/-! ## 7. Preparatory smoothness lemmas -/

/-- `z ↦ ζ_j (pt i z)` is continuous at every point at which the chart inverse is genuine. -/
private theorem zeta_pt_continuousAt (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target) :
    ContinuousAt (fun w => D.ζ j (D.pt i w)) z := by
  have hsymm : ContinuousAt (extChartAt I (D.x₀ i)).symm (flatToE (I := I) (D.x₀ i) z) :=
    (contMDiffOn_extChartAt_symm (I := I) (x := D.x₀ i) (n := (⊤ : ℕ∞))).continuousOn.continuousAt
      ((isOpen_extChartAt_target (I := I) (D.x₀ i)).mem_nhds hz)
  have hpt : ContinuousAt (fun w => D.pt i w) z :=
    hsymm.comp ((contDiff_flatToE (I := I) (x₀ := D.x₀ i)).continuous.continuousAt)
  exact ((D.hζsm j).continuous.continuousAt).comp hpt

/-- `z ↦ pt i z` is `C^∞` at every point at which the chart inverse is genuine. -/
private theorem pt_contMDiffAt (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target) :
    ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) I (⊤ : ℕ∞) (fun w => D.pt i w) z :=
  ((contMDiffOn_extChartAt_symm (I := I) (x := D.x₀ i) (n := (⊤ : ℕ∞))).contMDiffAt
      ((isOpen_extChartAt_target (I := I) (D.x₀ i)).mem_nhds hz)).comp z
    ((contDiff_flatToE (I := I) (x₀ := D.x₀ i)).contMDiff.contMDiffAt)

/-- `z ↦ pt i z` is `C^∞` on the region where the chart inverse is genuine. -/
private theorem pt_contMDiffOn (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    ContMDiffOn 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) I (⊤ : ℕ∞) (fun z => D.pt i z)
      {z : Fin (Module.finrank ℝ E) → ℝ |
        flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target} :=
  fun z hz => (pt_contMDiffAt D i hz).contMDiffWithinAt

/-- The metric pairing of two smooth frame fields is `C^∞`. -/
private theorem pairing_contMDiffAt (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (c d : Fin (Module.finrank ℝ E)) (p : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun q : M => g₀.inner q (D.e i c q) (D.e j d q)) p := by
  have hY : Work.Diff.EXT.SmoothFieldAt I M (D.e i c) p := (D.hesm i c).contMDiffAt
  have hZ : Work.Diff.EXT.SmoothFieldAt I M (D.e j d) p := (D.hesm j d).contMDiffAt
  have hres := contMDiffAt_metric_pairing' (I := I) (G := fun _ : ℝ => g₀) (J := Set.univ)
    isOpen_univ (jointSmooth_const' g₀) (Set.mem_univ (0 : ℝ)) hY hZ
  have hc : ContMDiffAt I ((modelWithCornersSelf ℝ ℝ).prod I) (⊤ : ℕ∞)
      (fun q : M => ((0 : ℝ), q)) p :=
    (contMDiffAt_const : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) _
      (fun _ : M => (0 : ℝ)) p).prodMk contMDiffAt_id
  simpa only [Function.comp_def] using hres.comp p hc

/-- The metric pairing of the frame fields, composed with `pt i`. -/
private theorem pairing_pt_contDiffAt (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (c d : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt i w) (D.e i c (D.pt i w)) (D.e j d (D.pt i w))) z :=
  ((pairing_contMDiffAt D i j c d (D.pt i z)).comp z (pt_contMDiffAt D i hz)).contDiffAt

/-- The volume density of chart `j` at the flat coordinate of `pt i`, smooth where `ζ_j > 0`. -/
private theorem dens_comp_contDiffAt (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target)
    (hζ : 0 < D.ζ j (D.pt i z)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.dens j (coord (I := I) (D.x₀ j) (D.pt i w))) z := by
  obtain ⟨hsrc, hlt⟩ := D.hζsupp j (D.pt i z) (ne_of_gt hζ)
  have hlt2 : ‖coord (I := I) (D.x₀ j) (D.pt i z)‖ ≤ 2 * D.σ j := by
    have hσ := D.hσ j; linarith
  have htgt : flatToE (I := I) (D.x₀ j) (coord (I := I) (D.x₀ j) (D.pt i z))
      ∈ (extChartAt I (D.x₀ j)).target := D.htarget j _ hlt2
  have hdens : ContDiffAt ℝ (⊤ : ℕ∞) (D.dens j) (coord (I := I) (D.x₀ j) (D.pt i z)) :=
    (densGood_free D j _ htgt).2
  have htrans : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => coord (I := I) (D.x₀ j) (D.pt i w)) z :=
    Work.Diff.STE.D.transMap_contDiffAt D j i z hz hsrc
  have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
      ((D.dens j) ∘ fun w => coord (I := I) (D.x₀ j) (D.pt i w)) z :=
    ContDiffAt.comp z hdens htrans
  exact hcomp

/-- A finite product of real numbers in `[0,1]` is `≤ 1`. -/
private lemma prod_le_one_real {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h0a : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
    have h1a : f a ≤ 1 := h1 a (Finset.mem_insert_self a s)
    have h0s : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1s : ∏ i ∈ s, f i ≤ 1 :=
      ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    calc f a * ∏ i ∈ s, f i ≤ 1 * 1 := mul_le_mul h1a h1s h0s (by norm_num)
      _ = 1 := by ring

/-- **The bump of the covering argument.**  There is a `C^∞` function `θ`, `0 ≤ θ ≤ 1`, which

* vanishes on a neighbourhood of every point of the chart-`i` target at which `ζ_j (pt i ·) ≤ 0`,
* vanishes on a neighbourhood of every point outside the chart-`i` target (hence has support in a
  fixed ball inside the target),
* equals `1` on a neighbourhood of every point of the `2σ i`-ball with `ζ_j (pt i ·) ≥ 1/√(card ι₀)`.
-/
private theorem bump_data (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    ∃ θ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) θ ∧ (∀ z, 0 ≤ θ z) ∧ (∀ z, θ z ≤ 1) ∧
      (∀ z, flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target →
        D.ζ j (D.pt i z) ≤ 0 → θ =ᶠ[𝓝 z] fun _ => 0) ∧
      (∀ z, flatToE (I := I) (D.x₀ i) z ∉ (extChartAt I (D.x₀ i)).target →
        θ =ᶠ[𝓝 z] fun _ => 0) ∧
      (∀ z, ‖z‖ ≤ 2 * D.σ i → 1 / Real.sqrt (Fintype.card ι₀) ≤ D.ζ j (D.pt i z) →
        θ =ᶠ[𝓝 z] fun _ => 1) := by
  classical
  -- the flat-coordinate region on which the chart inverse is defined
  have hUtgt : IsOpen {z : Fin (Module.finrank ℝ E) → ℝ |
      flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target} :=
    (isOpen_extChartAt_target (I := I) (D.x₀ i)).preimage
      (contDiff_flatToE (I := I) (x₀ := D.x₀ i)).continuous
  have hsub : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ i) ⊆
      {z | flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target} := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact D.htarget i z hz
  obtain ⟨ρ, hρpos, hρ⟩ :=
    (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ i)).exists_thickening_subset_open
      hUtgt hsub
  -- the thresholds on `ζ_j`
  set τ : ℝ := 1 / Real.sqrt (Fintype.card ι₀) with hτ
  have hcardpos : 0 < Fintype.card ι₀ := Fintype.card_pos_iff.mpr ⟨i⟩
  have hτpos : 0 < τ := by
    rw [hτ]
    exact one_div_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hcardpos))
  set δ₀ : ℝ := τ / 4 with hδ₀
  set δ₁ : ℝ := τ / 2 with hδ₁
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀]; linarith
  have hδlt : δ₀ < δ₁ := by rw [hδ₀, hδ₁]; linarith
  -- the two radial radii
  set a : ℝ := 2 * D.σ i + ρ / 4 with ha
  set b : ℝ := 2 * D.σ i + ρ / 2 with hb
  have hab : a < b := by rw [ha, hb]; linarith [hρpos]
  have hbpos : 0 < b - a := by linarith
  have hb_nonneg : 0 ≤ b := by rw [hb]; linarith [D.hσ i, hρpos]
  have hball : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) b ⊆
      {z | flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target} := by
    intro z hz
    apply hρ
    rw [Metric.mem_thickening_iff]
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [hb] at hz
    by_cases hz' : ‖z‖ ≤ 2 * D.σ i
    · exact ⟨z, by simpa [Metric.mem_closedBall, dist_eq_norm] using hz',
        by simpa [dist_self] using hρpos⟩
    · push_neg at hz'
      have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by linarith [D.hσ i]) hz'.le
      refine ⟨((2 * D.σ i) / ‖z‖) • z, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (by linarith [D.hσ i]) (norm_nonneg _))]
        rw [div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt hzpos)]
        simp only [mul_one]
        linarith [D.hσ i]
      · rw [dist_eq_norm]
        have h1 : z - ((2 * D.σ i) / ‖z‖) • z = (1 - (2 * D.σ i) / ‖z‖) • z := by
          rw [sub_smul, one_smul]
        rw [h1, norm_smul, Real.norm_eq_abs]
        have hsub : 1 - (2 * D.σ i) / ‖z‖ > 0 := by
          have hlt : (2 * D.σ i) / ‖z‖ < 1 := by
            rw [div_lt_one hzpos]
            linarith [hz', D.hσ i]
          linarith
        rw [abs_of_pos hsub]
        have h2 : (1 - 2 * D.σ i / ‖z‖) * ‖z‖ = ‖z‖ - 2 * D.σ i := by
          field_simp
        rw [h2]
        linarith [hz]
  -- the one-dimensional cut-off
  set φ : ℝ → ℝ := fun x =>
    Real.smoothTransition ((x + b) / (b - a)) * Real.smoothTransition ((b - x) / (b - a)) with hφ
  have hφsm : ContDiff ℝ (⊤ : ℕ∞) φ := by
    rw [hφ]
    refine ContDiff.mul ?_ ?_
    · exact Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)
    · exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
  have hφnn : ∀ x, 0 ≤ φ x := by
    intro x
    rw [hφ]
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hφle : ∀ x, φ x ≤ 1 := by
    intro x
    rw [hφ]
    exact mul_le_one₀ (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
  have hφone : ∀ x ∈ Set.Icc (-a) a, φ x = 1 := by
    intro x hx
    rw [Set.mem_Icc] at hx
    rw [hφ]
    dsimp only
    have h1 : 1 ≤ (x + b) / (b - a) := by
      rw [le_div_iff₀ hbpos]; linarith [hx.1]
    have h2 : 1 ≤ (b - x) / (b - a) := by
      rw [le_div_iff₀ hbpos]; linarith [hx.2]
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, mul_one]
  have hφzero : ∀ x, b ≤ x → φ x = 0 := by
    intro x hx
    rw [hφ]
    dsimp only
    have h1 : (b - x) / (b - a) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hbpos.le
    rw [Real.smoothTransition.zero_of_nonpos h1, mul_zero]
  have hφzero' : ∀ x, x ≤ -b → φ x = 0 := by
    intro x hx
    rw [hφ]
    dsimp only
    have h1 : (x + b) / (b - a) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hbpos.le
    rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]
  -- the flat cut-off and the `ζ` cut-off
  set g₂ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun z => ∏ k, φ (z k) with hg₂
  have hcoord : ∀ k : Fin (Module.finrank ℝ E),
      ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ => z k) := by
    intro k
    fun_prop
  have hg₂sm : ContDiff ℝ (⊤ : ℕ∞) g₂ := by
    rw [hg₂]
    exact contDiff_prod fun k _ => hφsm.comp (hcoord k)
  have hg₂nn : ∀ z, 0 ≤ g₂ z := by
    intro z; rw [hg₂]; exact Finset.prod_nonneg fun k _ => hφnn _
  have hg₂le : ∀ z, g₂ z ≤ 1 := by
    intro z; rw [hg₂]
    exact prod_le_one_real _ (fun k _ => hφnn _) (fun k _ => hφle _)
  have hg₂supp : Function.support g₂ ⊆ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) b := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    push_neg at hlt
    obtain ⟨k, hk⟩ : ∃ k, b < |z k| := by
      by_contra hc
      push_neg at hc
      refine absurd hlt (not_lt.mpr ?_)
      refine (pi_norm_le_iff_of_nonneg hb_nonneg).mpr fun k => ?_
      simpa only [Real.norm_eq_abs] using hc k
    have hzero : φ (z k) = 0 := by
      rcases lt_abs.mp hk with h | h
      · exact hφzero _ h.le
      · exact hφzero' (z k) (by linarith)
    exact (Function.mem_support.mp hz) (by
      rw [hg₂]
      exact Finset.prod_eq_zero (Finset.mem_univ k) hzero)
  set g₁ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
    fun z => Real.smoothTransition ((D.ζ j (D.pt i z) - δ₀) / (δ₁ - δ₀)) with hg₁
  have hg₁per : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => D.ζ j (D.pt i z))
      {z | flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target} :=
    ((D.hζsm j).contMDiffOn.comp (f := fun z : Fin (Module.finrank ℝ E) → ℝ => D.pt i z)
      (t := Set.univ) (pt_contMDiffOn D i) (fun z hz => Set.mem_univ _)).contDiffOn
  have hg₁sm : ContDiffOn ℝ (⊤ : ℕ∞) g₁
      {z | flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target} := by
    rw [hg₁]
    exact Real.smoothTransition.contDiff.comp_contDiffOn
      ((hg₁per.sub contDiffOn_const).div_const _)
  have hg₁nn : ∀ z, 0 ≤ g₁ z := by
    intro z; rw [hg₁]; exact Real.smoothTransition.nonneg _
  have hg₁le : ∀ z, g₁ z ≤ 1 := by
    intro z; rw [hg₁]; exact Real.smoothTransition.le_one _
  have hg₁zero : ∀ z, flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target →
      D.ζ j (D.pt i z) ≤ 0 → g₁ =ᶠ[𝓝 z] fun _ => 0 := by
    intro z hzt hζ
    have hcont : ContinuousAt (fun w => D.ζ j (D.pt i w)) z := zeta_pt_continuousAt D i j hzt
    have hlt : D.ζ j (D.pt i z) < δ₀ := lt_of_le_of_lt hζ (by linarith)
    have hev : ∀ᶠ w in 𝓝 z, D.ζ j (D.pt i w) < δ₀ :=
      hcont.eventually (IsOpen.mem_nhds isOpen_Iio hlt)
    filter_upwards [hev] with w hw
    rw [hg₁]
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  have hg₁one : ∀ z, flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target →
      τ ≤ D.ζ j (D.pt i z) → g₁ =ᶠ[𝓝 z] fun _ => 1 := by
    intro z hzt hz
    rw [hg₁]
    have hcont : ContinuousAt (fun w => D.ζ j (D.pt i w)) z := zeta_pt_continuousAt D i j hzt
    have hlt2 : δ₁ < D.ζ j (D.pt i z) := by
      rw [hδ₁]
      linarith
    have hev : ∀ᶠ w in 𝓝 z, δ₁ < D.ζ j (D.pt i w) :=
      hcont.eventually (IsOpen.mem_nhds isOpen_Ioi hlt2)
    filter_upwards [hev] with w hw
    exact Real.smoothTransition.one_of_one_le (by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < δ₁ - δ₀)]; linarith)
  -- the bump itself
  refine ⟨fun z => g₁ z * g₂ z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hzt : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target
    · exact ((hg₁sm.contDiffAt (hUtgt.mem_nhds hzt)).mul hg₂sm.contDiffAt)
    · have htsup : tsupport g₂ ⊆ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) b :=
        closure_minimal hg₂supp Metric.isClosed_closedBall
      have hzero : g₂ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        refine Filter.eventually_iff_exists_mem.mpr ⟨(Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) b)ᶜ,
          IsOpen.mem_nhds Metric.isClosed_closedBall.isOpen_compl (fun h => hzt (hball h)), ?_⟩
        intro w hw
        exact image_eq_zero_of_notMem_tsupport (fun h => hw (htsup h))
      have hev0 : (fun y => g₁ y * g₂ y) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        filter_upwards [hzero] with w hw
        rw [hw, mul_zero]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev0
  · intro z; exact mul_nonneg (hg₁nn z) (hg₂nn z)
  · intro z
    exact mul_le_one₀ (hg₁le z) (hg₂nn z) (hg₂le z)
  · intro z hzt hζ
    have h1 := hg₁zero z hzt hζ
    filter_upwards [h1] with w hw
    rw [hw, zero_mul]
  · intro z hzt
    have hzb : z ∉ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) b :=
      fun h => hzt (hball h)
    have htsup : tsupport g₂ ⊆ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) b :=
      closure_minimal hg₂supp Metric.isClosed_closedBall
    have hzero : g₂ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      refine Filter.eventually_iff_exists_mem.mpr ⟨(Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) b)ᶜ,
        IsOpen.mem_nhds Metric.isClosed_closedBall.isOpen_compl hzb, ?_⟩
      intro w hw
      exact image_eq_zero_of_notMem_tsupport (fun h => hw (htsup h))
    filter_upwards [hzero] with w hw
    rw [hw, mul_zero]
  · intro z hz hζ
    have hzt : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target := D.htarget i z hz
    have h1 : g₁ =ᶠ[𝓝 z] fun _ => 1 := hg₁one z hzt (by linarith)
    have h2 : g₂ =ᶠ[𝓝 z] fun _ => 1 := by
      have hk : ∀ᶠ w in 𝓝 z, ∀ k, |w k| ≤ a := by
        have hlt : ‖z‖ < a := lt_of_le_of_lt hz (by linarith [hρpos])
        filter_upwards [Metric.ball_mem_nhds z (sub_pos.mpr hlt)] with w hw
        intro k
        have h1 : |w k - z k| ≤ ‖w - z‖ := by
          simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (w - z) k
        have h2 : ‖w - z‖ < a - ‖z‖ := by
          rw [Metric.mem_ball, dist_eq_norm] at hw
          linarith
        have h3 : |z k| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z k
        have h4 := abs_lt.mp (lt_of_le_of_lt h1 h2)
        have h5 := abs_le.mp h3
        rw [abs_le]
        constructor <;> linarith [h4.1, h4.2, h5.1, h5.2]
      filter_upwards [hk] with w hw
      exact Finset.prod_eq_one fun k _ =>
        hφone (w k) ⟨(abs_le.mp (hw k)).1, (abs_le.mp (hw k)).2⟩
    filter_upwards [h1, h2] with w h1w h2w
    rw [h1w, h2w, one_mul]

/-! ## 8. Pointwise reconstruction without the ball hypothesis -/

/-- The chart-`i` target region is open (in the flat coordinates). -/
private theorem target_region_open (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    IsOpen {z : Fin (Module.finrank ℝ E) → ℝ |
      flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target} :=
  (isOpen_extChartAt_target (I := I) (D.x₀ i)).preimage
    (contDiff_flatToE (I := I) (x₀ := D.x₀ i)).continuous

/-- `z ↦ ζ_j (pt i z)` is `C^∞` on the chart-`i` target region. -/
private theorem zeta_pt_contDiffOn (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => D.ζ j (D.pt i z))
      {z : Fin (Module.finrank ℝ E) → ℝ |
        flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target} :=
  ((D.hζsm j).contMDiffOn.comp (f := fun z : Fin (Module.finrank ℝ E) → ℝ => D.pt i z)
    (t := Set.univ) (pt_contMDiffOn D i) (fun z hz => Set.mem_univ _)).contDiffOn

/-- Cancellation of the weight `A` and the square root of the density `B`. -/
private lemma cancel_weight_dens {A B S M : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (h : (A * B⁻¹) * S = A ^ 2 * M) : A⁻¹ * B⁻¹ * S = M := by
  have h1 : S = A * B * M := by
    have h2 : (A * B⁻¹) * S = (A * B⁻¹) * (A * B * M) := by
      rw [h]
      field_simp
    exact mul_left_cancel₀ (mul_ne_zero hA (inv_ne_zero hB)) h2
  rw [h1]
  field_simp

/-- **Pointwise reconstruction, without the ball hypothesis.**  At a point `z` where `ζ_j (pt i z)`
does not vanish, the chart-`i` matrix of `h` is the weighted double sum of the localised components
of chart `j`. -/
private theorem mat_eq_inv_zeta_sum_pt (D : B3Data (I := I) (M := M) ι₀ g₀)
    (h : Bil (I := I) (M := M)) (i j : ι₀) (c d : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) (hζ : D.ζ j (D.pt i z) ≠ 0) :
    D.mat i h c d z
      = (D.ζ j (D.pt i z))⁻¹
        * (Real.sqrt (D.dens j (coord (I := I) (D.x₀ j) (D.pt i z))))⁻¹
        * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            g₀.inner (D.pt i z) (D.e i c (D.pt i z)) (D.e j a (D.pt i z)) *
            g₀.inner (D.pt i z) (D.e i d (D.pt i z)) (D.e j b (D.pt i z)) *
            D.R j h a b (coord (I := I) (D.x₀ j) (D.pt i z)) := by
  obtain ⟨hsrc, hlt⟩ := D.hζsupp j (D.pt i z) hζ
  have h2 : ‖coord (I := I) (D.x₀ j) (D.pt i z)‖ ≤ 2 * D.σ j := by
    have hσ := D.hσ j; linarith
  have hON : IsONFrame g₀ (D.pt i z) (fun a => D.e j a (D.pt i z)) := by
    have h0 := D.heON j (coord (I := I) (D.x₀ j) (D.pt i z)) h2
    rwa [D.symm_flatToE_coord j hsrc] at h0
  have htgt : flatToE (I := I) (D.x₀ j) (coord (I := I) (D.x₀ j) (D.pt i z))
      ∈ (extChartAt I (D.x₀ j)).target := D.htarget j _ h2
  have hdens : 0 < D.dens j (coord (I := I) (D.x₀ j) (D.pt i z)) :=
    dens_pos_of_mem_target D j htgt
  have hB : Real.sqrt (D.dens j (coord (I := I) (D.x₀ j) (D.pt i z))) ≠ 0 :=
    (Real.sqrt_pos.mpr hdens).ne'
  have hchi : D.χ j (coord (I := I) (D.x₀ j) (D.pt i z)) = 1 :=
    D.hχ1 j _ (le_of_lt hlt)
  have hR := Rstar_R_eq_zeta_sq_free D h j (D.pt i z) (D.e i c (D.pt i z)) (D.e i d (D.pt i z))
  have hRa : ((D.Rstar j (fun (a b : Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ) => D.R j h a b z) (D.pt i z))
        (D.e i c (D.pt i z))) (D.e i d (D.pt i z))
      = (D.ζ j (D.pt i z) * D.χ j (coord (I := I) (D.x₀ j) (D.pt i z))
          * (Real.sqrt (D.dens j (coord (I := I) (D.x₀ j) (D.pt i z))))⁻¹)
        * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            D.R j h a b (coord (I := I) (D.x₀ j) (D.pt i z))
              * ((g₀.inner (D.pt i z)) (D.e i c (D.pt i z))) (D.e j a (D.pt i z))
              * ((g₀.inner (D.pt i z)) (D.e i d (D.pt i z))) (D.e j b (D.pt i z)) := by
    simpa only using Rstar_apply D j (fun a b z => D.R j h a b z) (D.pt i z)
      (D.e i c (D.pt i z)) (D.e i d (D.pt i z))
  have hcomb := hRa.symm.trans hR
  simp only [hchi, mul_one] at hcomb
  have hkey := cancel_weight_dens (A := D.ζ j (D.pt i z)) (B := Real.sqrt (D.dens j
      (coord (I := I) (D.x₀ j) (D.pt i z)))) (S := ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          D.R j h a b (coord (I := I) (D.x₀ j) (D.pt i z))
            * ((g₀.inner (D.pt i z)) (D.e i c (D.pt i z))) (D.e j a (D.pt i z))
            * ((g₀.inner (D.pt i z)) (D.e i d (D.pt i z))) (D.e j b (D.pt i z)))
      (M := D.mat i h c d z) hζ hB hcomb
  rw [← hkey]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring


/-- **A bound for the `pdVec` of a finite sum.** -/
private lemma pdVec_finset_sum_le {n m : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → (Fin n → ℝ) → ℂ) (hF : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (F k))
    (β : Fin m → Fin n) (z : Fin n → ℝ) :
    ‖pdVec m β (fun y => ∑ k, F k y) z‖ ≤ ∑ k, ‖pdVec m β (F k) z‖ := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ k, F k y) := ContDiff.sum fun k _ => hF k
  rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m _ hG z β]
  rw [iteratedFDeriv_sum (𝕜 := ℝ) (u := Finset.univ) (fun k _ => (hF k).of_le
      (WithTop.coe_le_coe.mpr le_top : ((m : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞)))]
  rw [Finset.sum_apply z Finset.univ (fun j => iteratedFDeriv ℝ m (F j))]
  rw [ContinuousMultilinearMap.sum_apply Finset.univ
    (fun c => (iteratedFDeriv ℝ m (F c)) z) (fun j => Pi.single (β j) 1)]
  exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => by
    rw [← Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m (F k) (hF k) z β]))

/-- **The local jet bound for one pair of charts.**  For the pair `(i, j)` (and the section entries
`c`, `d`), every `m`-jet of the chart matrix `D.mat i h c d` at a point `z` of the `2σ i`-ball with
`ζ_j (pt i z) ≥ 1/√(card ι₀)` is bounded by `C √(D.ENormB k₀ h)`. -/
private theorem local_jet_bound (D : B3Data (I := I) (M := M) ι₀ g₀) (k₀ m : ℕ)
    (hm : 2 * m + Module.finrank ℝ E < 2 * k₀) (hk : 1 ≤ k₀)
    (hn : 1 ≤ Module.finrank ℝ E) (i j : ι₀) (c d : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Bil (I := I) (M := M))
      (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → 1 / Real.sqrt (Fintype.card ι₀) ≤ D.ζ j (D.pt i z) →
      ‖pdVec m β (fun y => ((D.mat i h c d y : ℝ) : ℂ)) z‖
        ≤ C * Real.sqrt (D.ENormB k₀ h) := by
  classical
  obtain ⟨θ, hθsm, hθnn, hθle, hθzero1, hθzero2, hθone⟩ := bump_data D i j
  obtain ⟨C_R, hC_R_nn, hC_R⟩ := R_jet_bound D k₀ m hm hk hn
  obtain ⟨C₄, hC₄_nn, hC₄⟩ := pdVec_mul_comp_le (n := Module.finrank ℝ E) (m := m)
  -- the coefficient function
  set cf : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
    fun a b w => (D.ζ j (D.pt i w))⁻¹ *
      (Real.sqrt (D.dens j (coord (I := I) (D.x₀ j) (D.pt i w))))⁻¹ *
      (g₀.inner (D.pt i w) (D.e i c (D.pt i w)) (D.e j a (D.pt i w)) *
       g₀.inner (D.pt i w) (D.e i d (D.pt i w)) (D.e j b (D.pt i w))) with hcf
  have hcf_sm : ∀ (a b : Fin (Module.finrank ℝ E)) {w : Fin (Module.finrank ℝ E) → ℝ},
      flatToE (I := I) (D.x₀ i) w ∈ (extChartAt I (D.x₀ i)).target →
      0 < D.ζ j (D.pt i w) → ContDiffAt ℝ (⊤ : ℕ∞) (cf a b) w := by
    intro a b w hwt hwζ
    rw [hcf]
    have hζat : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => D.ζ j (D.pt i y)) w :=
      (zeta_pt_contDiffOn D i j).contDiffAt ((target_region_open D i).mem_nhds hwt)
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (D.ζ j (D.pt i y))⁻¹) w :=
      hζat.inv (ne_of_gt hwζ)
    have hd := dens_comp_contDiffAt D i j hwt hwζ
    have hpos : 0 < D.dens j (coord (I := I) (D.x₀ j) (D.pt i w)) := by
      obtain ⟨hsrc, hlt⟩ := D.hζsupp j (D.pt i w) (ne_of_gt hwζ)
      have hlt2 : ‖coord (I := I) (D.x₀ j) (D.pt i w)‖ ≤ 2 * D.σ j := by
        have hσ := D.hσ j; linarith
      exact (densGood_free D j _ (D.htarget j _ hlt2)).1
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y => (Real.sqrt (D.dens j (coord (I := I) (D.x₀ j) (D.pt i y))))⁻¹) w :=
      (hd.sqrt (ne_of_gt hpos)).inv (Real.sqrt_pos.mpr hpos).ne'
    have h3 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y => g₀.inner (D.pt i y) (D.e i c (D.pt i y)) (D.e j a (D.pt i y))) w :=
      pairing_pt_contDiffAt D i j c a hwt
    have h4 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y => g₀.inner (D.pt i y) (D.e i d (D.pt i y)) (D.e j b (D.pt i y))) w :=
      pairing_pt_contDiffAt D i j d b hwt
    exact (h1.mul h2).mul (h3.mul h4)
  have hA_sm : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiff ℝ (⊤ : ℕ∞) (fun y => ((cf a b y * θ y : ℝ) : ℂ)) := by
    intro a b
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hwt : flatToE (I := I) (D.x₀ i) w ∈ (extChartAt I (D.x₀ i)).target
    · by_cases hwζ : 0 < D.ζ j (D.pt i w)
      · exact Complex.ofRealCLM.contDiff.contDiffAt.comp w
          ((hcf_sm a b hwt hwζ).mul hθsm.contDiffAt)
      · have hev : θ =ᶠ[𝓝 w] fun _ => 0 := hθzero1 w hwt (le_of_not_gt hwζ)
        have hev2 : (fun y => ((cf a b y * θ y : ℝ) : ℂ)) =ᶠ[𝓝 w] fun _ => 0 := by
          filter_upwards [hev] with y hy
          rw [hy, mul_zero]; norm_num
        exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev2
    · have hev : θ =ᶠ[𝓝 w] fun _ => 0 := hθzero2 w hwt
      have hev2 : (fun y => ((cf a b y * θ y : ℝ) : ℂ)) =ᶠ[𝓝 w] fun _ => 0 := by
        filter_upwards [hev] with y hy
        rw [hy, mul_zero]; norm_num
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev2
  set φq : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ) :=
    fun y => θ y • coord (I := I) (D.x₀ j) (D.pt i y) with hφq
  have hφq_sm : ContDiff ℝ (⊤ : ℕ∞) φq := by
    rw [hφq, contDiff_iff_contDiffAt]
    intro w
    by_cases hwt : flatToE (I := I) (D.x₀ i) w ∈ (extChartAt I (D.x₀ i)).target
    · by_cases hwζ : 0 < D.ζ j (D.pt i w)
      · obtain ⟨hsrc, hlt⟩ := D.hζsupp j (D.pt i w) (ne_of_gt hwζ)
        exact hθsm.contDiffAt.smul (Work.Diff.STE.D.transMap_contDiffAt D j i w hwt hsrc)
      · have hev : θ =ᶠ[𝓝 w] fun _ => 0 := hθzero1 w hwt (le_of_not_gt hwζ)
        have hev2 : (fun y => θ y • coord (I := I) (D.x₀ j) (D.pt i y))
            =ᶠ[𝓝 w] fun _ => 0 := by
          filter_upwards [hev] with y hy
          rw [hy, zero_smul]
        exact (contDiffAt_const (c := (0 : Fin (Module.finrank ℝ E) → ℝ))).congr_of_eventuallyEq
          hev2
    · have hev : θ =ᶠ[𝓝 w] fun _ => 0 := hθzero2 w hwt
      have hev2 : (fun y => θ y • coord (I := I) (D.x₀ j) (D.pt i y))
          =ᶠ[𝓝 w] fun _ => 0 := by
        filter_upwards [hev] with y hy
        rw [hy, zero_smul]
      exact (contDiffAt_const (c := (0 : Fin (Module.finrank ℝ E) → ℝ))).congr_of_eventuallyEq
        hev2
  have hK : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ i)) :=
    isCompact_closedBall _ _
  have hKmem : ∀ {w : Fin (Module.finrank ℝ E) → ℝ}, ‖w‖ ≤ 2 * D.σ i →
      w ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ i) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hw
  choose MA hMA_nn hMA using fun a b : Fin (Module.finrank ℝ E) =>
    exists_bound_iteratedFDeriv_compact (hA_sm a b) hK m
  obtain ⟨Cφ, -, hCφ⟩ := exists_bound_iteratedFDeriv_compact hφq_sm hK m
  set MD : ℝ := max 1 Cφ with hMD
  have hMD_nn : 0 ≤ MD := le_trans zero_le_one (le_max_left _ _)
  have hMD1 : 1 ≤ MD := le_max_left _ _
  set Card : ℝ := ∑ i' ∈ Finset.range (m + 1),
    (Fintype.card (Fin i' → Fin (Module.finrank ℝ E)) : ℝ) with hCard
  refine ⟨C₄ * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), MA a b)
    * (1 + MD) ^ m * Card * C_R, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E), MA a b :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hMA_nn a b
    have h2 : (0 : ℝ) ≤ (1 + MD) ^ m := pow_nonneg (by linarith) m
    have h3 : (0 : ℝ) ≤ Card := Finset.sum_nonneg fun i _ => by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₄_nn h1) h2) h3) hC_R_nn
  · intro h hh β z hz hζ
    have hzt : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target := D.htarget i z hz
    have hcardpos : 0 < Fintype.card ι₀ := Fintype.card_pos_iff.mpr ⟨i⟩
    have hτpos : 0 < 1 / Real.sqrt (Fintype.card ι₀) :=
      one_div_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hcardpos))
    have hζpos : 0 < D.ζ j (D.pt i z) := lt_of_lt_of_le hτpos hζ
    have hζne : D.ζ j (D.pt i z) ≠ 0 := ne_of_gt hζpos
    have hθz : θ z = 1 := (hθone z hz hζ).eq_of_nhds
    have hφqz : φq z = coord (I := I) (D.x₀ j) (D.pt i z) := by
      rw [hφq]; simp only [hθz, one_smul]
    have hcoordlt : ‖coord (I := I) (D.x₀ j) (D.pt i z)‖ < D.σ j :=
      (D.hζsupp j (D.pt i z) hζne).2
    have hζev : ∀ᶠ y in 𝓝 z, 0 < D.ζ j (D.pt i y) :=
      (zeta_pt_continuousAt D i j hzt).eventually (IsOpen.mem_nhds isOpen_Ioi hζpos)
    -- the eventual identity
    have hident : (fun y => ((D.mat i h c d y : ℝ) : ℂ)) =ᶠ[𝓝 z]
        (fun y => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (fun w => ((cf a b w * θ w : ℝ) : ℂ)) y *
          (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq y)) := by
      filter_upwards [hθone z hz hζ, hζev] with y hyθ hyζ
      have hmat := mat_eq_inv_zeta_sum_pt D h i j c d y (ne_of_gt hyζ)
      have hsum : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          cf a b y * D.R j h a b (coord (I := I) (D.x₀ j) (D.pt i y))) = D.mat i h c d y := by
        rw [hmat, hcf]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro b _
        ring
      have hφqy : φq y = coord (I := I) (D.x₀ j) (D.pt i y) := by
        rw [hφq]; simp only [hyθ, one_smul]
      rw [hyθ, hφqy]
      simp only [mul_one]
      rw [← hsum]
      push_cast
      rfl
    -- the energy factor
    set MRh : ℝ := Card * C_R * Real.sqrt (D.ENormB k₀ h) with hMRh
    have hMRb : ∀ (a b : Fin (Module.finrank ℝ E)) (i₀ : ℕ), i₀ ≤ m →
        ‖iteratedFDeriv ℝ i₀ (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq z)‖ ≤ MRh := by
      intro a b i₀ hi₀
      have hFc_sm : ContDiff ℝ (⊤ : ℕ∞) (fun w => ((D.R j h a b w : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (R_contDiff_of_chartData' D h hh j a b)
      have h1 : ‖iteratedFDeriv ℝ i₀ (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq z)‖
          ≤ ∑ l : Fin i₀ → Fin (Module.finrank ℝ E),
              ‖pdVec i₀ l (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq z)‖ :=
        Work.Diff.STE.flat.norm_iteratedFDeriv_le_sum_pdVec i₀ _ hFc_sm (φq z)
      have h2 : ∀ l : Fin i₀ → Fin (Module.finrank ℝ E),
          ‖pdVec i₀ l (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq z)‖
            ≤ C_R * Real.sqrt (D.ENormB k₀ h) := by
        intro l
        have hpv : pdVec i₀ l (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq z)
            = ((pdRList (List.ofFn l) (D.R j h a b) (φq z) : ℝ) : ℂ) := by
          show pdList (List.ofFn l) (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq z) = _
          rw [cm_pdList_ofReal_smooth (List.ofFn l) (D.R j h a b)
            (R_contDiff_of_chartData' D h hh j a b)]
        rw [hpv, Complex.norm_real, Real.norm_eq_abs]
        refine hC_R h hh j a b (List.ofFn l) (by simpa using hi₀) (φq z) ?_
        rw [hφqz]
        exact le_of_lt hcoordlt
      calc ‖iteratedFDeriv ℝ i₀ (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq z)‖
          ≤ ∑ l : Fin i₀ → Fin (Module.finrank ℝ E),
              ‖pdVec i₀ l (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq z)‖ := h1
        _ ≤ ∑ _l : Fin i₀ → Fin (Module.finrank ℝ E), (C_R * Real.sqrt (D.ENormB k₀ h)) :=
            Finset.sum_le_sum fun l _ => h2 l
        _ = (Fintype.card (Fin i₀ → Fin (Module.finrank ℝ E)) : ℝ)
              * (C_R * Real.sqrt (D.ENormB k₀ h)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ Card * (C_R * Real.sqrt (D.ENormB k₀ h)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [hCard]
            exact Finset.single_le_sum
              (f := fun i' => (Fintype.card (Fin i' → Fin (Module.finrank ℝ E)) : ℝ))
              (fun i' _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi₀))
        _ = MRh := by rw [hMRh]; ring
    -- the per-pair bound
    have hterm : ∀ a b : Fin (Module.finrank ℝ E),
        ‖pdVec m β (fun y => (fun w => ((cf a b w * θ w : ℝ) : ℂ)) y *
          (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq y)) z‖
          ≤ C₄ * MA a b * (1 + MD) ^ m * MRh := by
      intro a b
      have hFc_sm : ContDiff ℝ (⊤ : ℕ∞) (fun w => ((D.R j h a b w : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (R_contDiff_of_chartData' D h hh j a b)
      refine hC₄ _ φq _ z β (MA a b) MD MRh (hA_sm a b) hφq_sm hFc_sm ?_ ?_ ?_
      · intro i₀ hi₀
        exact hMA a b i₀ hi₀ z (hKmem hz)
      · intro i₀ hi₀₁ hi₀m
        have h1 : ‖iteratedFDeriv ℝ i₀ φq z‖ ≤ Cφ := hCφ i₀ hi₀m z (hKmem hz)
        have h2 : Cφ ≤ MD ^ i₀ := by
          have h3 : Cφ ≤ MD := by rw [hMD]; exact le_max_right _ _
          have h4 : MD ^ 1 ≤ MD ^ i₀ := pow_le_pow_right₀ hMD1 hi₀₁
          calc Cφ ≤ MD := h3
            _ = MD ^ 1 := (pow_one MD).symm
            _ ≤ MD ^ i₀ := h4
        exact h1.trans h2
      · intro i₀ hi₀
        exact hMRb a b i₀ hi₀
    -- the sum
    have hsum1 : ‖pdVec m β (fun y => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
          (fun w => ((cf a b w * θ w : ℝ) : ℂ)) y *
          (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq y)) z‖
        ≤ ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          ‖pdVec m β (fun y => (fun w => ((cf a b w * θ w : ℝ) : ℂ)) y *
            (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq y)) z‖ := by
      refine (pdVec_finset_sum_le _ ?_ β z).trans ?_
      · intro a
        refine ContDiff.sum fun b _ => ?_
        exact (hA_sm a b).mul ((Complex.ofRealCLM.contDiff.comp
          (R_contDiff_of_chartData' D h hh j a b)).comp hφq_sm)
      · refine Finset.sum_le_sum fun a _ => ?_
        refine pdVec_finset_sum_le _ (fun b => ?_) β z
        exact (hA_sm a b).mul ((Complex.ofRealCLM.contDiff.comp
          (R_contDiff_of_chartData' D h hh j a b)).comp hφq_sm)
    calc ‖pdVec m β (fun y => ((D.mat i h c d y : ℝ) : ℂ)) z‖
        = ‖pdVec m β (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
            (fun w => ((cf a b w * θ w : ℝ) : ℂ)) y *
            (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq y)) z‖ := by
          congr 1
          exact pdList_congr_of_eventuallyEq hident (List.ofFn β)
      _ ≤ ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            ‖pdVec m β (fun y => (fun w => ((cf a b w * θ w : ℝ) : ℂ)) y *
              (fun w => ((D.R j h a b w : ℝ) : ℂ)) (φq y)) z‖ := hsum1
      _ ≤ ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            C₄ * MA a b * (1 + MD) ^ m * MRh :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
      _ = (C₄ * (1 + MD) ^ m * MRh) * (∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E), MA a b) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _
          ring
      _ = (C₄ * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), MA a b)
            * (1 + MD) ^ m * Card * C_R) * Real.sqrt (D.ENormB k₀ h) := by
          rw [hMRh]; ring

theorem mat_jet_bound_of_energy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k₀ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h →
        ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ)
          (hm : 2 * m + Module.finrank ℝ E < 2 * k₀)
          (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
          ‖z‖ ≤ 2 * D.σ i →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat i h c d y : ℝ) : ℂ)) z‖
            ≤ C * (1 + Real.sqrt (D.ENormB k₀ h)) := by
  classical
  by_cases hn0 : Module.finrank ℝ E = 0
  · refine ⟨0, le_refl 0, ?_⟩
    intro h hh i c d m hm β z hz
    have hlt : c.val < 0 := by rw [← hn0]; exact c.isLt
    exact absurd hlt (by simp)
  · have hn : 1 ≤ Module.finrank ℝ E := Nat.pos_of_ne_zero hn0
    by_cases hk0 : k₀ = 0
    · refine ⟨0, le_refl 0, ?_⟩
      intro h hh i c d m hm β z hz
      exact absurd hm (by omega)
    · have hk : 1 ≤ k₀ := Nat.pos_of_ne_zero hk0
      have hloc : ∀ (i j : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ),
          ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Bil (I := I) (M := M))
            (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
            (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ)
            (hm : 2 * m + Module.finrank ℝ E < 2 * k₀),
            ‖z‖ ≤ 2 * D.σ i → 1 / Real.sqrt (Fintype.card ι₀) ≤ D.ζ j (D.pt i z) →
            ‖pdVec m β (fun y => ((D.mat i h c d y : ℝ) : ℂ)) z‖
              ≤ C * Real.sqrt (D.ENormB k₀ h) := by
        intro i j c d m
        by_cases hm : 2 * m + Module.finrank ℝ E < 2 * k₀
        · obtain ⟨C, hC, hCb⟩ := local_jet_bound D k₀ m hm hk hn i j c d
          exact ⟨C, hC, fun h hh β z hm' hz hζ => hCb h hh β z hz hζ⟩
        · exact ⟨0, le_refl 0, fun h hh β z hm' hz hζ => absurd hm' hm⟩
      choose Cf hCf_nn hCf using hloc
      have hCtot_def : ∀ (i : ι₀) (j : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ)
          (_hm : 2 * m + Module.finrank ℝ E < 2 * k₀),
          Cf i j c d m ≤ ∑ i' : ι₀, ∑ j' : ι₀, ∑ c' : Fin (Module.finrank ℝ E),
            ∑ d' : Fin (Module.finrank ℝ E),
            ∑ m' ∈ Finset.range (k₀ + 1), |Cf i' j' c' d' m'| := by
        intro i j c d m _hm
        have hm_r : m ∈ Finset.range (k₀ + 1) := Finset.mem_range.mpr (by omega)
        have L1 : |Cf i j c d m| ≤ ∑ m' ∈ Finset.range (k₀ + 1), |Cf i j c d m'| :=
          Finset.single_le_sum (f := fun m' => |Cf i j c d m'|) (fun m' _ => abs_nonneg _) hm_r
        have L2 : (∑ m' ∈ Finset.range (k₀ + 1), |Cf i j c d m'|) ≤
            ∑ d' : Fin (Module.finrank ℝ E),
              ∑ m' ∈ Finset.range (k₀ + 1), |Cf i j c d' m'| :=
          Finset.single_le_sum
            (f := fun d' => ∑ m' ∈ Finset.range (k₀ + 1), |Cf i j c d' m'|)
            (fun d' _ => Finset.sum_nonneg fun m' _ => abs_nonneg _) (Finset.mem_univ d)
        have L3 : (∑ d' : Fin (Module.finrank ℝ E),
              ∑ m' ∈ Finset.range (k₀ + 1), |Cf i j c d' m'|) ≤
            ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
              ∑ m' ∈ Finset.range (k₀ + 1), |Cf i j c' d' m'| :=
          Finset.single_le_sum
            (f := fun c' => ∑ d' : Fin (Module.finrank ℝ E),
              ∑ m' ∈ Finset.range (k₀ + 1), |Cf i j c' d' m'|)
            (fun c' _ => Finset.sum_nonneg fun d' _ =>
              Finset.sum_nonneg fun m' _ => abs_nonneg _) (Finset.mem_univ c)
        have L4 : (∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
              ∑ m' ∈ Finset.range (k₀ + 1), |Cf i j c' d' m'|) ≤
            ∑ j' : ι₀, ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
              ∑ m' ∈ Finset.range (k₀ + 1), |Cf i j' c' d' m'| :=
          Finset.single_le_sum
            (f := fun j' => ∑ c' : Fin (Module.finrank ℝ E),
              ∑ d' : Fin (Module.finrank ℝ E),
              ∑ m' ∈ Finset.range (k₀ + 1), |Cf i j' c' d' m'|)
            (fun j' _ => Finset.sum_nonneg fun c' _ =>
              Finset.sum_nonneg fun d' _ => Finset.sum_nonneg fun m' _ => abs_nonneg _)
            (Finset.mem_univ j)
        have L5 : (∑ j' : ι₀, ∑ c' : Fin (Module.finrank ℝ E),
              ∑ d' : Fin (Module.finrank ℝ E),
              ∑ m' ∈ Finset.range (k₀ + 1), |Cf i j' c' d' m'|) ≤
            ∑ i' : ι₀, ∑ j' : ι₀, ∑ c' : Fin (Module.finrank ℝ E),
              ∑ d' : Fin (Module.finrank ℝ E),
              ∑ m' ∈ Finset.range (k₀ + 1), |Cf i' j' c' d' m'| :=
          Finset.single_le_sum
            (f := fun i' => ∑ j' : ι₀, ∑ c' : Fin (Module.finrank ℝ E),
              ∑ d' : Fin (Module.finrank ℝ E),
              ∑ m' ∈ Finset.range (k₀ + 1), |Cf i' j' c' d' m'|)
            (fun i' _ => Finset.sum_nonneg fun j' _ =>
              Finset.sum_nonneg fun c' _ => Finset.sum_nonneg fun d' _ =>
              Finset.sum_nonneg fun m' _ => abs_nonneg _) (Finset.mem_univ i)
        exact le_trans (le_abs_self _) (L1.trans (L2.trans (L3.trans (L4.trans L5))))
      set Ctot : ℝ := ∑ i : ι₀, ∑ j : ι₀, ∑ c : Fin (Module.finrank ℝ E),
        ∑ d : Fin (Module.finrank ℝ E),
        ∑ m ∈ Finset.range (k₀ + 1), |Cf i j c d m| with hCtot
      have hCtot_nn : 0 ≤ Ctot := by
        rw [hCtot]
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ =>
          Finset.sum_nonneg fun m _ => abs_nonneg _
      refine ⟨Ctot, hCtot_nn, ?_⟩
      intro h hh i c d m hm β z hz
      obtain ⟨j, hj⟩ : ∃ j : ι₀, 1 / Real.sqrt (Fintype.card ι₀) ≤ D.ζ j (D.pt i z) := by
        by_contra hcon
        push_neg at hcon
        have hcardpos : (0 : ℝ) < Fintype.card ι₀ := by
          exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
        have hNpos : 0 < Real.sqrt (Fintype.card ι₀) := Real.sqrt_pos.mpr hcardpos
        have hlt : (∑ j : ι₀, (D.ζ j (D.pt i z)) ^ 2) < 1 := by
          calc (∑ j : ι₀, (D.ζ j (D.pt i z)) ^ 2)
              < ∑ _j : ι₀, (1 / Real.sqrt (Fintype.card ι₀)) ^ 2 := by
                refine Finset.sum_lt_sum (fun j _ => le_of_lt ?_) ⟨i, Finset.mem_univ i, ?_⟩
                · exact pow_lt_pow_left₀ (hcon j) (D.hζnn j _) (by norm_num)
                · exact pow_lt_pow_left₀ (hcon i) (D.hζnn i _) (by norm_num)
            _ = (Fintype.card ι₀ : ℝ) * (1 / Real.sqrt (Fintype.card ι₀)) ^ 2 := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            _ = 1 := by
                have hNne : (Fintype.card ι₀ : ℝ) ≠ 0 := by positivity
                rw [div_pow, one_pow, Real.sq_sqrt hcardpos.le]
                field_simp
        rw [D.hζsq (D.pt i z)] at hlt
        exact lt_irrefl 1 hlt
      have h1 := hCf i j c d m h hh β z hm hz hj
      have h2 : Cf i j c d m ≤ Ctot := by
        rw [hCtot]
        exact hCtot_def i j c d m hm
      calc ‖pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat i h c d y : ℝ) : ℂ)) z‖
          ≤ Cf i j c d m * Real.sqrt (D.ENormB k₀ h) := h1
        _ ≤ Ctot * Real.sqrt (D.ENormB k₀ h) :=
            mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
        _ ≤ Ctot * (1 + Real.sqrt (D.ENormB k₀ h)) := by
            refine mul_le_mul_of_nonneg_left ?_ hCtot_nn
            linarith [Real.sqrt_nonneg (D.ENormB k₀ h)]


end Work.Diff.STE.B3
