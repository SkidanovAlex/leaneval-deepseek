import Submission.Work.RiemLib.IndexCorner
import Submission.Work.RiemLib.GlobalBM
import Submission.Work.RiemLib.Commons.Analysis.Calculus.exists_pos_four_mul_sub_sq_mul_neg
import Submission.Work.RiemLib.Commons.Analysis.Calculus.sq_sqrt_mul_add_sqrt_mul_le
import Submission.Work.RiemLib.FlowJacobi
import Submission.Work.RiemLib.Commons.Topology.Compact.exists_pos_forall_mem_of_isCompact
import Submission.Work.RiemLib.Commons.Analysis.Calculus.exists_lt_of_hasDerivAt_deriv_neg
import Submission.Work.RiemLib.Commons.Analysis.ODE.exists_linearODE_solution_Icc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartCurv
open Submission.ChartConnection
open Submission.Rauch
open Submission.Gauss
open Submission.Curvature
open Submission.SecondVariation
open Submission.ChartBounds
open Submission.BonnetMyers
open Submission.IndexForm
open Submission.IndexForm2
open Submission.SecondVar2
open Submission.JacobiTensor
open Submission.FlowJacobi
open Submission.GlobalBM

namespace Submission.IndexCorner2

open Submission.IndexCorner

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Uniqueness for the Jacobi system.**  If `(y,z)` and `(0,0)` solve the linear system
`y' = z - Γ(w)y`, `z' = -Γ(w)z - R(y,w)w` on `[0,t₀]` and agree at `t₀`, then `(y,z) ≡ (0,0)`. -/
theorem eqOn_zero_of_jacobiSys {x₀ : M} {u w : ℝ → E} {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hGc : ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) (Icc 0 t₀))
    (hRc : ContinuousOn (fun t : ℝ => curvOp (cov := cov) x₀ u w t) (Icc 0 t₀))
    {y z : ℝ → E}
    (hy : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt y (z t - gammaOp (cov := cov) x₀ u w t (y t)) t)
    (hz : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt z (-gammaOp (cov := cov) x₀ u w t (z t)
      - curvOp (cov := cov) x₀ u w t (y t)) t)
    (hy0 : y t₀ = 0) (hz0 : z t₀ = 0) :
    ∀ t ∈ Icc (0:ℝ) t₀, y t = 0 ∧ z t = 0 := by
  classical
  obtain ⟨CG, hCG⟩ := isCompact_Icc.exists_bound_of_continuousOn hGc
  obtain ⟨CR, hCR⟩ := isCompact_Icc.exists_bound_of_continuousOn hRc
  set C : ℝ := 1 + 2 * CG + CR with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ CG := le_trans (norm_nonneg _) (hCG 0 ⟨le_refl 0, ht₀⟩)
    have h2 : 0 ≤ CR := le_trans (norm_nonneg _) (hCR 0 ⟨le_refl 0, ht₀⟩)
    linarith
  set M : ℝ≥0 := ⟨C, hCnn⟩ with hMdef
  have hAbound : ∀ t ∈ Icc (0:ℝ) t₀, ‖jacobiSysVec (cov := cov) x₀ u w t‖ ≤ (M : ℝ) := by
    intro t ht
    refine ContinuousLinearMap.opNorm_le_bound _ hCnn ?_
    intro x
    refine (norm_jacobiSysVec_le (cov := cov) x₀ u w t x.1 x.2).trans ?_
    have hgt : ‖gammaOp (cov := cov) x₀ u w t‖ ≤ CG := hCG t ht
    have hrt : ‖curvOp (cov := cov) x₀ u w t‖ ≤ CR := hCR t ht
    have hx : 0 ≤ ‖x‖ := norm_nonneg x
    have : (1 + 2 * ‖gammaOp (cov := cov) x₀ u w t‖ + ‖curvOp (cov := cov) x₀ u w t‖)
        ≤ C := by rw [hCdef]; linarith
    exact mul_le_mul_of_nonneg_right this hx
  set Y : ℝ → E × E := fun t => (y t, z t) with hYdef
  have hYode : ∀ t ∈ Icc (0:ℝ) t₀,
      HasDerivAt Y (jacobiSysVec (cov := cov) x₀ u w t (Y t)) t := by
    intro t ht
    have h := (hy t ht).prodMk (hz t ht)
    rw [jacobiSysVec_apply]
    exact h
  have hZode : ∀ t ∈ Icc (0:ℝ) t₀,
      HasDerivAt (fun _ : ℝ => (0 : E × E)) (jacobiSysVec (cov := cov) x₀ u w t
        ((fun _ : ℝ => (0 : E × E)) t)) t := by
    intro t ht
    rw [jacobiSysVec_apply]
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero, sub_zero, neg_zero]
    exact hasDerivAt_const t (0 : E × E)
  have hY0 : Y t₀ = (fun _ : ℝ => (0 : E × E)) t₀ := by
    rw [hYdef]
    simp only [hy0, hz0]
    rfl
  have hEq := Commons.Analysis.ODE.eqOn_of_hasDerivAt_linearODE
    (A := fun t => jacobiSysVec (cov := cov) x₀ u w t)
    (M := M) hAbound ⟨ht₀, le_refl t₀⟩ hYode hZode hY0
  intro t ht
  have h := hEq ht
  rw [show (fun _ : ℝ => (0 : E × E)) t = 0 from rfl] at h
  simp only [hYdef, Prod.mk_eq_zero] at h
  exact h

/-- **A chart Jacobi field vanishing with its covariant derivative at `t₀` is zero.** -/
theorem eqOn_zero_of_covDerivJacobi {x₀ : M} {u w y : ℝ → E} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (htgt : ∀ t ∈ Icc (0:ℝ) t₀, u t ∈ (extChartAt I x₀).target)
    (hGc : ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) (Icc 0 t₀))
    (hRc : ContinuousOn (fun t : ℝ => curvOp (cov := cov) x₀ u w t) (Icc 0 t₀))
    (hy : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Icc (0:ℝ) t₀,
      HasDerivAt (chartCovDeriv cov x₀ u w y) (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Icc (0:ℝ) t₀, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hy0 : y t₀ = 0) (hDy0 : chartCovDeriv cov x₀ u w y t₀ = 0) :
    ∀ t ∈ Icc (0:ℝ) t₀, y t = 0 := by
  have hy' : ∀ t ∈ Icc (0:ℝ) t₀,
      HasDerivAt y (chartCovDeriv cov x₀ u w y t - gammaOp (cov := cov) x₀ u w t (y t)) t := by
    intro t ht
    have h : deriv y t = chartCovDeriv cov x₀ u w y t - gammaOp (cov := cov) x₀ u w t (y t) := by
      simp only [Submission.Jacobi.chartCovDeriv, gammaOp]
      abel
    exact (hy t ht).congr_deriv h
  have hz' : ∀ t ∈ Icc (0:ℝ) t₀,
      HasDerivAt (chartCovDeriv cov x₀ u w y)
        (-gammaOp (cov := cov) x₀ u w t (chartCovDeriv cov x₀ u w y t)
          - curvOp (cov := cov) x₀ u w t (y t)) t := by
    intro t ht
    have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (htgt t ht)
    have hCv : curvOp (cov := cov) x₀ u w t (y t)
        = chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) :=
      curvOp_apply (cov := cov) hsrc (y t)
    have h : deriv (chartCovDeriv cov x₀ u w y) t
        = -gammaOp (cov := cov) x₀ u w t (chartCovDeriv cov x₀ u w y t)
          - curvOp (cov := cov) x₀ u w t (y t) := by
      have hj := hjac t ht
      rw [← hCv] at hj
      have h2 : deriv (chartCovDeriv cov x₀ u w y) t
          + (gammaOp (cov := cov) x₀ u w t (chartCovDeriv cov x₀ u w y t)
            + curvOp (cov := cov) x₀ u w t (y t)) = 0 := by
        simpa only [Submission.Jacobi.chartCovDeriv, gammaOp, add_assoc] using hj
      have h3 := eq_neg_of_add_eq_zero_left h2
      rw [neg_add] at h3
      rw [sub_eq_add_neg]
      exact h3
    exact (hDy t ht).congr_deriv h
  have h := eqOn_zero_of_jacobiSys (cov := cov) ht₀.le hGc hRc hy' hz' hy0 hDy0
  intro t ht
  exact (h t ht).1

/-- **Second variation of the energy of a two-piece family**: two independent fields on `[0,t₀]` and
on `[0,L-t₀]` matching at the corner. -/
theorem fam2Energy_second_deriv_pieces [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {u w w' η₁ e₁ η₂ e₂ : ℝ → E} {t₀ L : ℝ} (ht₀ : 0 < t₀) (hLt : t₀ < L)
    {a₁ a₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hwc : ContinuousOn w' (Icc 0 L))
    (hη₁ : ∀ t ∈ Icc 0 t₀, HasDerivAt η₁ (e₁ t) t) (he₁c : ContinuousOn e₁ (Icc 0 t₀))
    (hη₂ : ∀ t ∈ Icc 0 (L - t₀), HasDerivAt η₂ (e₂ t) t)
    (he₂c : ContinuousOn e₂ (Icc 0 (L - t₀)))
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hη₁0 : η₁ 0 = 0) (hη₂L : η₂ (L - t₀) = 0) (hmatch : η₁ t₀ = η₂ 0)
    (hstay₁ : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (0:ℝ) t₀,
      fam2 u η₁ (fun _ => (0 : E)) s t ∈ (extChartAt I x₀).target)
    (hstay₂ : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (0:ℝ) (L - t₀),
      fam2 (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0 : E)) s t ∈ (extChartAt I x₀).target)
    (htgt : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target) :
    HasDerivAt
      (deriv (fun s =>
        fam2Energy (I := I) x₀ u η₁ (fun _ => (0:E)) w e₁ (fun _ => (0:E)) t₀ s
        + fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E))
            (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) (L - t₀) s))
      (-2 * ((∫ t in (0 : ℝ)..t₀, indexIntegrand cov x₀ u η₁ w e₁ t)
        + (∫ τ in (0 : ℝ)..(L - t₀), indexIntegrand cov x₀ (fun τ' : ℝ => u (t₀ + τ'))
            η₂ (fun τ' : ℝ => w (t₀ + τ')) e₂ τ))) 0 := by
  classical
  have ht₀L : t₀ ≤ L := hLt.le
  have hmem₀ : ∀ τ ∈ Icc (0:ℝ) (L - t₀), t₀ + τ ∈ Icc (0:ℝ) L := fun τ hτ =>
    ⟨by linarith [ht₀, hτ.1], by linarith [hτ.2]⟩
  have huc : ContinuousOn u (Icc 0 L) := HasDerivAt.continuousOn hu
  have hwc0 : ContinuousOn w (Icc 0 L) := HasDerivAt.continuousOn hw
  have h1 := fam2Energy_second_deriv (I := I) (cov := cov) hmet htor x₀
    (ζ := fun _ => (0 : E)) (ζ' := fun _ => (0 : E)) (w := w) (e := e₁) (w' := w')
    (u := u) (η := η₁) (L := t₀) ht₀ ha₁ ha₂
    (fun t ht => hu t ⟨ht.1, ht.2.trans ht₀L⟩)
    (fun t ht => hw t ⟨ht.1, ht.2.trans ht₀L⟩)
    hη₁
    (fun _ _ => hasDerivAt_const _ (0 : E)) he₁c continuousOn_const
    (fun t ht => hgeo t ⟨ht.1, ht.2.trans ht₀L⟩)
    (A₀ := 0) (B₀ := t₀) (le_refl 0) (le_refl t₀) hstay₁
    (fun t ht => htgt t ⟨ht.1, ht.2.trans ht₀L⟩)
  have h2 := fam2Energy_second_deriv (I := I) (cov := cov) hmet htor x₀
    (ζ := fun _ => (0 : E)) (ζ' := fun _ => (0 : E))
    (u := fun τ : ℝ => u (t₀ + τ)) (η := η₂)
    (w := fun τ : ℝ => w (t₀ + τ)) (e := e₂)
    (w' := fun τ : ℝ => w' (t₀ + τ)) (L := L - t₀) (by linarith) ha₁ ha₂
    (fun t ht => (hu (t₀ + t) (hmem₀ t ht)).comp_const_add t₀ t)
    (fun t ht => (hw (t₀ + t) (hmem₀ t ht)).comp_const_add t₀ t)
    hη₂
    (fun _ _ => hasDerivAt_const _ (0 : E)) he₂c continuousOn_const
    (fun t ht => by simpa only using hgeo (t₀ + t) (hmem₀ t ht))
    (A₀ := 0) (B₀ := L - t₀) (le_refl 0) (le_refl (L - t₀)) hstay₂
    (fun t ht => htgt (t₀ + t) (hmem₀ t ht))
  have hbdy1 : fam2A (cov := cov) x₀ u η₁ (fun _ => (0 : E)) t₀
      = chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (η₁ t₀) (η₁ t₀) := by
    simp only [fam2A, zero_add]
  have hbdy10 : fam2A (cov := cov) x₀ u η₁ (fun _ => (0 : E)) 0 = 0 := by
    simp only [fam2A, zero_add, hη₁0, chrB_zero_fst]
  have hbdy2 : fam2A (cov := cov) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂
      (fun _ => (0 : E)) 0
      = chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (η₂ 0) (η₂ 0) := by
    simp only [fam2A, zero_add, add_zero]
  have hbdy2L : fam2A (cov := cov) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂
      (fun _ => (0 : E)) (L - t₀) = 0 := by
    simp only [fam2A, zero_add, show t₀ + (L - t₀) = L from by ring, hη₂L, chrB_zero_fst]
  rw [hbdy1, hbdy10] at h1
  rw [hbdy2, hbdy2L] at h2
  simp only [chartGram_zero_fst, sub_zero, add_zero] at h1 h2
  have hmatch' : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀))
      (chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (η₁ t₀) (η₁ t₀)) (w t₀)
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀))
        (chrB cov x₀ ((extChartAt I x₀).symm (u t₀)) (η₂ 0) (η₂ 0)) (w t₀) := by
    rw [hmatch]
  rw [hmatch'] at h1
  have hsum := h1.add h2
  have hev : (fun s : ℝ =>
        deriv (fun σ : ℝ => fam2Energy (I := I) x₀ u η₁ (fun _ => (0:E)) w e₁
          (fun _ => (0:E)) t₀ σ) s
        + deriv (fun σ : ℝ => fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E))
            (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) (L - t₀) σ) s)
      =ᶠ[𝓝 (0:ℝ)]
      deriv (fun s : ℝ =>
        fam2Energy (I := I) x₀ u η₁ (fun _ => (0:E)) w e₁ (fun _ => (0:E)) t₀ s
        + fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E))
            (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) (L - t₀) s) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0:ℝ) ∈ Ioo a₁ a₂ from ⟨ha₁, ha₂⟩)] with s hs
    have hd1 : DifferentiableAt ℝ
        (fun σ : ℝ => fam2Energy (I := I) x₀ u η₁ (fun _ => (0:E)) w e₁ (fun _ => (0:E)) t₀ σ) s :=
      (fam2Energy_hasDerivAt (I := I) (cov := cov) hmet x₀
        (ζ := fun _ => (0 : E)) (ζ' := fun _ => (0 : E)) (u := u) (η := η₁) (w := w) (e := e₁)
        (w' := w') (L := t₀) ht₀.le (a₁ := a₁) (a₂ := a₂) (δ₁ := (a₁ + s) / 2)
        (δ₂ := (s + a₂) / 2) (s₀ := s) (A₀ := 0) (B₀ := t₀)
        (by linarith [hs.1]) (by linarith [hs.2]) (by linarith [hs.1]) (by linarith [hs.2])
        (fun (t : ℝ) (ht : t ∈ Icc 0 t₀) => hu t ⟨ht.1, ht.2.trans ht₀L⟩)
        (fun (t : ℝ) (ht : t ∈ Icc 0 t₀) => hw t ⟨ht.1, ht.2.trans ht₀L⟩) hη₁
        (fun _ _ => hasDerivAt_const _ (0:E)) he₁c continuousOn_const
        (le_refl 0) (le_refl t₀) hstay₁).differentiableAt
    have hd2 : DifferentiableAt ℝ
        (fun σ : ℝ => fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E))
            (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) (L - t₀) σ) s :=
      (fam2Energy_hasDerivAt (I := I) (cov := cov) hmet x₀
        (ζ := fun _ => (0 : E)) (ζ' := fun _ => (0 : E))
        (u := fun τ : ℝ => u (t₀ + τ)) (η := η₂)
        (w := fun τ : ℝ => w (t₀ + τ)) (e := e₂)
        (w' := fun τ : ℝ => w' (t₀ + τ)) (L := L - t₀) (by linarith)
        (a₁ := a₁) (a₂ := a₂) (δ₁ := (a₁ + s) / 2) (δ₂ := (s + a₂) / 2) (s₀ := s)
        (A₀ := 0) (B₀ := L - t₀)
        (by linarith [hs.1]) (by linarith [hs.2]) (by linarith [hs.1]) (by linarith [hs.2])
        (fun (t : ℝ) (ht : t ∈ Icc 0 (L - t₀)) => (hu (t₀ + t) (hmem₀ t ht)).comp_const_add t₀ t)
        (fun (t : ℝ) (ht : t ∈ Icc 0 (L - t₀)) => (hw (t₀ + t) (hmem₀ t ht)).comp_const_add t₀ t)
        hη₂
        (fun _ _ => hasDerivAt_const _ (0:E)) he₂c continuousOn_const
        (le_refl 0) (le_refl (L - t₀)) hstay₂).differentiableAt
    have hd := deriv_add (f := fun σ : ℝ => fam2Energy (I := I) x₀ u η₁ (fun _ => (0:E)) w e₁ (fun _ => (0:E)) t₀ σ)
      (g := fun σ : ℝ => fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E))
          (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) (L - t₀) σ) hd1 hd2
    exact hd.symm
  refine (hsum.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  ring

/-- **Continuity of a Christoffel entry along any continuous chart curve.**  The proof avoids the
geodesic equation: it uses the polarisation identity and the smoothness of the chart spray. -/
lemma continuousOn_christoffelEval_entry_of_cont [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {B : Set ℝ}
    (hu : ContinuousOn u B) (hw : ContinuousOn w B)
    (hmem : ∀ t ∈ B, u t ∈ (extChartAt I x₀).target) (a : E) :
    ContinuousOn (fun t : ℝ => christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) B := by
  have hspray : ∀ t ∈ B, ∀ c : E,
      ContinuousAt (chartGeodesicVectorField cov x₀) (u t, c) := by
    intro t ht c
    have hz : (u t, c) ∈ (extChartAt I x₀).target ×ˢ (Set.univ : Set E) :=
      ⟨hmem t ht, Set.mem_univ _⟩
    have hnb : (extChartAt I x₀).target ×ˢ (Set.univ : Set E) ∈ 𝓝 (u t, c) :=
      ((isOpen_extChartAt_target x₀).prod isOpen_univ).mem_nhds hz
    exact (((Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray
      (cov := cov) x₀) (u t, c) hz).contDiffAt hnb).continuousAt
  have hu' : ∀ t ∈ B, ContinuousWithinAt u B t := fun t ht => hu.continuousWithinAt ht
  have hw' : ∀ t ∈ B, ContinuousWithinAt w B t := fun t ht => hw.continuousWithinAt ht
  have key : ∀ t ∈ B,
      christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        = (1/2 : ℝ) • (- chartGeodesicVectorField cov x₀ (u t, a + w t)
            + chartGeodesicVectorField cov x₀ (u t, a)
            + chartGeodesicVectorField cov x₀ (u t, w t)) := by
    intro t ht
    have hp : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (hmem t ht)
    have hpol := christoffelEval_polarize (cov := cov) htor hp a (w t)
    have hstep : christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        = (1/2 : ℝ) • (christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (a + w t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (a + w t))
          - christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) a)
          - christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (w t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) := by
      rw [← hpol]; module
    rw [hstep]
    simp only [chartGeodesicVectorField]
    module
  refine ContinuousOn.congr ?_ (fun t ht => (key t ht))
  refine ContinuousOn.const_smul ?_ _
  refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.neg ?_) ?_) ?_
  · exact fun t ht => (hspray t ht (a + w t)).comp_continuousWithinAt
      (f := fun s : ℝ => (u s, a + w s))
      ((hu' t ht).prodMk (continuousWithinAt_const.add (hw' t ht)))
  · exact fun t ht => (hspray t ht a).comp_continuousWithinAt
      (f := fun s : ℝ => (u s, a))
      ((hu' t ht).prodMk continuousWithinAt_const)
  · exact fun t ht => (hspray t ht (w t)).comp_continuousWithinAt
      (f := fun s : ℝ => (u s, w s))
      ((hu' t ht).prodMk (hw' t ht))

/-- **Continuity of the Christoffel operator `gammaOp` along any continuous chart curve.** -/
lemma continuousOn_gammaOp_of_cont [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {B : Set ℝ}
    (hu : ContinuousOn u B) (hw : ContinuousOn w B)
    (hmem : ∀ t ∈ B, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) B := by
  have hsum : ∀ t : ℝ, gammaOp (cov := cov) x₀ u w t
      = ∑ i : Fin (Module.finrank ℝ E),
          (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
            (christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) ((Module.finBasis ℝ E) i)
              (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) :=
    fun t => rfl
  simp only [hsum]
  refine continuousOn_finsetSum _ (fun i _ => ?_)
  exact (ContinuousLinearMap.smulRightL ℝ E E
      (((Module.finBasis ℝ E).coord i).toContinuousLinearMap)).continuous.comp_continuousOn
    (continuousOn_christoffelEval_entry_of_cont (cov := cov) htor hu hw hmem
      ((Module.finBasis ℝ E) i))

/-- **A chart Jacobi field which vanishes at `t₀` together with its covariant derivative is zero.**
(The `t₀`-endpoint form of uniqueness for the Jacobi equation, used to show that the covariant
derivative of a nonzero Jacobi field with `J t₀ = 0` cannot vanish.) -/
theorem eqOn_zero_of_chartJacobi [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {u w w' J J' J'' : ℝ → E} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hu : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt w (w' t) t)
    (htgt : ∀ t ∈ Icc (0:ℝ) t₀, u t ∈ (extChartAt I x₀).target)
    (hJ : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt J (J' t) t)
    (hJ' : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt J' (J'' t) t)
    (hjac : ∀ t ∈ Icc (0:ℝ) t₀, DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hJt : J t₀ = 0) (hz0 : DtQ cov x₀ u J w J' t₀ = 0) :
    ∀ t ∈ Icc (0:ℝ) t₀, J t = 0 := by
  have huC : ContinuousOn u (Icc (0:ℝ) t₀) := HasDerivAt.continuousOn hu
  have hwC : ContinuousOn w (Icc (0:ℝ) t₀) := HasDerivAt.continuousOn hw
  have hGc : ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) (Icc 0 t₀) :=
    continuousOn_gammaOp_of_cont (cov := cov) htor huC hwC htgt
  have hRc : ContinuousOn (fun t : ℝ => curvOp (cov := cov) x₀ u w t) (Icc 0 t₀) :=
    continuousOn_curvOp (cov := cov) huC hwC htgt
  set z : ℝ → E := fun t => DtQ cov x₀ u J w J' t with hzdef
  have hzfun : z = fun t => J' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (J t) := by
    funext t
    simp only [hzdef, DtQ, covDsP, fam, famP, zero_smul, add_zero]
  have hzd : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt z
      (J'' t + dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) (J t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w' t) (J t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (J' t)) t := by
    intro t ht
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      (hu t ht).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (htgt t ht))
    have h1 := (hJ' t ht).add (hasDerivAt_chrB_fam_t (cov := cov) (x₀ := x₀)
      (u := u) (η := J) (w := w) (e := J') (w' := w') (t₀ := t) (hu t ht) (hw t ht) (hJ t ht)
      (htgt t ht) hstay)
    have hfe : (J' + fun s : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (u s)) (w s) (J s))
        = fun s : ℝ => J' s + chrB cov x₀ ((extChartAt I x₀).symm (u s)) (w s) (J s) := by
      funext s; rfl
    rw [hfe] at h1
    rw [show (fun s : ℝ => J' s + chrB cov x₀ ((extChartAt I x₀).symm (u s)) (w s) (J s))
        = z from hzfun.symm] at h1
    simpa only [add_assoc] using h1
  have hzsys : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt z
      (-gammaOp (cov := cov) x₀ u w t (z t) - curvOp (cov := cov) x₀ u w t (J t)) t := by
    intro t ht
    have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (htgt t ht)
    have hDtds : DtDsP cov x₀ u J w J' t
        = deriv z t + gammaOp (cov := cov) x₀ u w t (z t) := by
      have h1 : DtDsP cov x₀ u J w J' t
          = deriv z t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (z t) (w t) := by
        show deriv (fun r => covDsP cov x₀ u J w J' 0 r) t
            + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (covDsP cov x₀ u J w J' 0 t) (w t)
          = deriv (fun t => DtQ cov x₀ u J w J' t) t
            + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (DtQ cov x₀ u J w J' t) (w t)
        rfl
      have h2 : chrB cov x₀ ((extChartAt I x₀).symm (u t)) (z t) (w t)
          = gammaOp (cov := cov) x₀ u w t (z t) := by
        simp only [chrB, gammaOp_apply (cov := cov) hsrc]
      rw [h1, h2]
    have hcv : curvOp (cov := cov) x₀ u w t (J t)
        = chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) :=
      curvOp_apply (cov := cov) hsrc (J t)
    have hj := hjac t ht
    rw [hDtds] at hj
    refine (hzd t ht).congr_deriv ?_
    rw [hcv]
    have hderv : deriv z t
        = J'' t + dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) (J t)
          + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w' t) (J t)
          + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (J' t) := (hzd t ht).deriv
    have hj' : deriv z t + (gammaOp (cov := cov) x₀ u w t (z t)
          + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t)) = 0 := by
      simpa only [add_assoc] using hj
    have h3 : deriv z t
        = -(gammaOp (cov := cov) x₀ u w t (z t)
            + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t)) :=
      eq_neg_of_add_eq_zero_left hj'
    rw [← hderv, h3, neg_add]
    rw [sub_eq_add_neg]
  have hy : ∀ t ∈ Icc (0:ℝ) t₀,
      HasDerivAt J (z t - gammaOp (cov := cov) x₀ u w t (J t)) t := by
    intro t ht
    have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (htgt t ht)
    have hkey : z t - gammaOp (cov := cov) x₀ u w t (J t) = J' t := by
      have h1 : z t = J' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (J t) := by
        rw [hzfun]
      have h2 : chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (J t)
          = gammaOp (cov := cov) x₀ u w t (J t) := by
        simp only [chrB, gammaOp_apply (cov := cov) hsrc, christoffelEval_comm (cov := cov) htor
          x₀ ((extChartAt I x₀).symm (u t)) hsrc (J t) (w t)]
      rw [h1, h2, add_sub_cancel_right]
    exact (hJ t ht).congr_deriv hkey.symm
  have hz0' : z t₀ = 0 := by rw [hzdef]; exact hz0
  have h := eqOn_zero_of_jacobiSys (cov := cov) (x₀ := x₀) (u := u) (w := w) ht₀.le hGc hRc
    hy hzsys hJt hz0'
  intro t ht
  exact (h t ht).1

/-! ## The cut-off field on `[0,L]` vanishing at `0` and `L` -/

/-- The polynomial cut-off `t ↦ t(L-t)/(t₀(L-t₀))`, equal to `0` at `0` and `L` and to `1` at `t₀`. -/
noncomputable def cutChi (t₀ L : ℝ) (t : ℝ) : ℝ := t * (L - t) / (t₀ * (L - t₀))

/-- The derivative of the cut-off. -/
noncomputable def cutChiD (t₀ L : ℝ) (t : ℝ) : ℝ := (L - 2 * t) / (t₀ * (L - t₀))

/-- The vector field `t ↦ χ(t) • z`. -/
noncomputable def cutField (t₀ L : ℝ) (z : E) : ℝ → E := fun t => cutChi t₀ L t • z

/-- Its derivative. -/
noncomputable def cutFieldD (t₀ L : ℝ) (z : E) : ℝ → E := fun t => cutChiD t₀ L t • z

lemma hasDerivAt_cutChi (t₀ L t : ℝ) :
    HasDerivAt (cutChi t₀ L) (cutChiD t₀ L t) t := by
  unfold cutChi cutChiD
  have h1 : HasDerivAt (fun s : ℝ => L - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub L
  have h2 := (hasDerivAt_id t).mul h1
  have h3 : HasDerivAt (fun s : ℝ => s * (L - s)) (1 * (L - t) + t * (-1)) t := h2
  have h4 : (1 * (L - t) + t * (-1) : ℝ) = L - 2 * t := by ring
  rw [h4] at h3
  exact h3.div_const _

lemma hasDerivAt_cutField (t₀ L : ℝ) (z : E) (t : ℝ) :
    HasDerivAt (cutField t₀ L z) (cutFieldD t₀ L z t) t := by
  have h := (hasDerivAt_cutChi t₀ L t).smul_const z
  exact h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by
    funext s; rfl)) |>.congr_deriv rfl

lemma cutField_zero (t₀ L : ℝ) (z : E) : cutField t₀ L z 0 = 0 := by
  simp [cutField, cutChi]

lemma cutField_L (t₀ L : ℝ) (z : E) : cutField t₀ L z L = 0 := by
  simp [cutField, cutChi]

lemma cutField_t₀ {t₀ L : ℝ} (ht₀ : t₀ ≠ 0) (htL : t₀ ≠ L) (z : E) :
    cutField t₀ L z t₀ = z := by
  have h : t₀ * (L - t₀) ≠ 0 := mul_ne_zero ht₀ (sub_ne_zero.mpr (Ne.symm htL))
  simp only [cutField, cutChi]
  rw [div_self h, one_smul]

lemma continuous_cutFieldD (t₀ L : ℝ) (z : E) : Continuous (cutFieldD t₀ L z) := by
  unfold cutFieldD cutChiD
  exact (continuous_const.sub (continuous_const.mul continuous_id)).div_const _ |>.smul continuous_const

lemma continuous_cutField (t₀ L : ℝ) (z : E) : Continuous (cutField t₀ L z) := by
  unfold cutField cutChi
  exact ((continuous_id.mul (continuous_const.sub continuous_id)).div_const _).smul continuous_const

/-- `DtQ` is homogeneous in the field. -/
lemma DtQ_smul (x₀ : M) (u w W W' : ℝ → E) (ε : ℝ) (t : ℝ) :
    DtQ cov x₀ u (fun s => ε • W s) w (fun s => ε • W' s) t
      = ε • DtQ cov x₀ u W w W' t := by
  simp only [DtQ, covDsP, fam, famP, zero_smul, add_zero, smul_add, chrB_smul_snd]

/-- The index integrand is homogeneous of degree two in the field. -/
lemma indexIntegrand_smul [ContMDiffCovariantDerivative cov ∞] (x₀ : M)
    (u w W W' : ℝ → E) (ε : ℝ) (t : ℝ) :
    indexIntegrand cov x₀ u (fun s => ε • W s) w (fun s => ε • W' s) t
      = ε ^ 2 * indexIntegrand cov x₀ u W w W' t := by
  simp only [indexIntegrand_eq, Rt_eq_Rq, DtQ_smul, Rq_smul_left, Rq_smul_right,
    Gq_smul_left, Gq_smul_right]
  ring

/-- **Continuity of the index integrand** from continuity of the four data only (no derivative of
`e` needed: the statement of `continuousOn_indexIntegrand'` asks for one but the proof does not
use it). -/
lemma continuousOn_indexIntegrand_of_cont [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) {x₀ : M} {u η w e : ℝ → E} {L : ℝ}
    (hu : ContinuousOn u (Icc 0 L)) (hη : ContinuousOn η (Icc 0 L))
    (hw : ContinuousOn w (Icc 0 L)) (he : ContinuousOn e (Icc 0 L))
    (hmem : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun t : ℝ => indexIntegrand cov x₀ u η w e t) (Icc 0 L) := by
  have hγ : ContinuousOn (fun t : ℝ => (extChartAt I x₀).symm (u t)) (Icc 0 L) :=
    continuousOn_chartCurve hu hmem
  have hsrc : ∀ t ∈ Icc 0 L, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (hmem t ht)
  have hRt := continuousOn_Rt (cov := cov) (x₀ := x₀) htor hu hη hw hmem
  have hGt : ContinuousOn (fun t : ℝ => Gt cov x₀ u η w e t) (Icc 0 L) := by
    rw [show (fun t : ℝ => Gt cov x₀ u η w e t) = fun t : ℝ =>
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (DtQ cov x₀ u η w e t) (DtQ cov x₀ u η w e t) from rfl]
    exact continuousOn_chartGram_curve (I := I) hγ
      (continuousOn_covDsP_along hu hη hw he hmem)
      (continuousOn_covDsP_along hu hη hw he hmem) hsrc
  exact hRt.sub hGt

/-- The index integrand is homogeneous of degree two, so its interval integral scales by `ε²`. -/
lemma integral_indexIntegrand_smul [ContMDiffCovariantDerivative cov ∞] {x₀ : M}
    {u w W W' : ℝ → E} {L ε : ℝ} :
    (∫ t in (0:ℝ)..L, indexIntegrand cov x₀ u (fun s => ε • W s) w (fun s => ε • W' s) t)
      = ε ^ 2 * (∫ t in (0:ℝ)..L, indexIntegrand cov x₀ u W w W' t) := by
  rw [intervalIntegral.integral_congr (fun t _ => indexIntegrand_smul (cov := cov) x₀ u w W W' ε t)]
  exact intervalIntegral.integral_const_mul (ε ^ 2) (fun t : ℝ => indexIntegrand cov x₀ u W w W' t)

/-- **The index integral of a perturbed Jacobi field.** -/
lemma integral_indexIntegrand_add_smul [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {u w w' J J' J'' W W' : ℝ → E} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hu : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt w (w' t) t) (hwc : ContinuousOn w' (Icc 0 t₀))
    (htgt : ∀ t ∈ Icc (0:ℝ) t₀, u t ∈ (extChartAt I x₀).target)
    (hJ : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt J (J' t) t) (hJc : ContinuousOn J' (Icc 0 t₀))
    (hJ' : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt J' (J'' t) t) (hJ''c : ContinuousOn J'' (Icc 0 t₀))
    (hjac : ∀ t ∈ Icc (0:ℝ) t₀, DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hJ0 : J 0 = 0) (hJt : J t₀ = 0)
    (hW : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt W (W' t) t) (hWc : ContinuousOn W' (Icc 0 t₀))
    (hW0 : W 0 = 0) {ε : ℝ} :
    (∫ t in (0:ℝ)..t₀, indexIntegrand cov x₀ u (fun s => J s + ε • W s) w
        (fun s => J' s + ε • W' s) t)
      = 2 * ε * (- chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀))
            (DtQ cov x₀ u J w J' t₀) (W t₀))
        + ε ^ 2 * (∫ t in (0:ℝ)..t₀, indexIntegrand cov x₀ u W w W' t) := by
  classical
  set G : ℝ → ℝ := fun t => indexBilin cov x₀ u w J J' W W' t with hGdef
  set A : ℝ → ℝ := fun t => indexIntegrand cov x₀ u J w J' t with hAdef
  set Cv : ℝ → ℝ := fun t => indexIntegrand cov x₀ u W w W' t with hCdef
  set F : ℝ → ℝ := fun t => indexIntegrand cov x₀ u (fun s => J s + ε • W s) w
    (fun s => J' s + ε • W' s) t with hFdef
  have hptF : ∀ t : ℝ, F t = A t + (2 * ε * G t + ε ^ 2 * Cv t) := by
    intro t
    have h := indexIntegrand_add (cov := cov) hmet htor x₀ u w J J' W W' ε t
    rw [hFdef, hAdef, hGdef, hCdef] at *
    linarith [h]
  have h2eGpt : ∀ t : ℝ, 2 * ε * G t = F t - A t - ε ^ 2 * Cv t := by
    intro t
    have h := hptF t
    rw [sub_eq_add_neg, sub_eq_add_neg]
    linarith [h]
  have hderJε : ∀ t ∈ Icc (0:ℝ) t₀,
      HasDerivAt (fun s : ℝ => J s + ε • W s) (J' t + ε • W' t) t := by
    intro t ht
    have h := (hJ t ht).add ((hW t ht).const_smul ε)
    refine h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext s
    simp only [Pi.add_apply, Pi.smul_apply]
  have huC : ContinuousOn u (Icc (0:ℝ) t₀) := HasDerivAt.continuousOn hu
  have hwC : ContinuousOn w (Icc (0:ℝ) t₀) := HasDerivAt.continuousOn hw
  have hJcC : ContinuousOn J (Icc (0:ℝ) t₀) := HasDerivAt.continuousOn hJ
  have hWcC : ContinuousOn W (Icc (0:ℝ) t₀) := HasDerivAt.continuousOn hW
  have hηεC : ContinuousOn (fun s : ℝ => J s + ε • W s) (Icc 0 t₀) :=
    hJcC.add (hWcC.const_smul ε)
  have heεC : ContinuousOn (fun s : ℝ => J' s + ε • W' s) (Icc 0 t₀) :=
    hJc.add (hWc.const_smul ε)
  have hFc : ContinuousOn F (Icc (0:ℝ) t₀) := by
    rw [hFdef]
    exact continuousOn_indexIntegrand_of_cont (cov := cov) htor huC hηεC hwC heεC htgt
  have hAc : ContinuousOn A (Icc (0:ℝ) t₀) := by
    rw [hAdef]
    exact continuousOn_indexIntegrand_of_cont (cov := cov) htor huC hJcC hwC hJc htgt
  have hCc : ContinuousOn Cv (Icc (0:ℝ) t₀) := by
    rw [hCdef]
    exact continuousOn_indexIntegrand_of_cont (cov := cov) htor huC hWcC hwC hWc htgt
  have h2eGc : ContinuousOn (fun t : ℝ => 2 * ε * G t) (Icc (0:ℝ) t₀) := by
    have hcont : ContinuousOn (fun t : ℝ => F t - A t - ε ^ 2 * Cv t) (Icc 0 t₀) :=
      (hFc.sub hAc).sub (hCc.const_mul (ε ^ 2))
    exact hcont.congr (fun t _ => by simpa only using (h2eGpt t))
  have hFint : IntervalIntegrable F volume (0:ℝ) t₀ := hFc.intervalIntegrable_of_Icc ht₀.le
  have hAint : IntervalIntegrable A volume (0:ℝ) t₀ := hAc.intervalIntegrable_of_Icc ht₀.le
  have hCint : IntervalIntegrable Cv volume (0:ℝ) t₀ := hCc.intervalIntegrable_of_Icc ht₀.le
  have h2eGint : IntervalIntegrable (fun t : ℝ => 2 * ε * G t) volume (0:ℝ) t₀ :=
    h2eGc.intervalIntegrable_of_Icc ht₀.le
  have h3 : ∫ t in (0:ℝ)..t₀, A t = 0 := by
    rw [hAdef]
    exact integral_indexIntegrand_of_jacobi (cov := cov) hmet htor x₀ ht₀ hu hw hwc htgt hJ hJc
      hJ' hJ''c hjac hJ0 hJt
  have h4 : ∫ t in (0:ℝ)..t₀, G t
      = - chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (DtQ cov x₀ u J w J' t₀)
          (W t₀) := by
    rw [hGdef]
    exact integral_indexBilin_of_jacobi (cov := cov) hmet htor x₀ ht₀ hu hw hwc htgt hJ hJc hJ'
      hJ''c hjac hW hWc hW0
  have h1 : ∫ t in (0:ℝ)..t₀, F t
      = (∫ t in (0:ℝ)..t₀, A t) + ∫ t in (0:ℝ)..t₀, (2 * ε * G t + ε ^ 2 * Cv t) := by
    rw [show F = fun t : ℝ => A t + (2 * ε * G t + ε ^ 2 * Cv t) from funext hptF]
    exact intervalIntegral.integral_add hAint (h2eGint.add (hCint.const_mul (ε ^ 2)))
  have h2 : ∫ t in (0:ℝ)..t₀, (2 * ε * G t + ε ^ 2 * Cv t)
      = 2 * ε * (∫ t in (0:ℝ)..t₀, G t) + ε ^ 2 * (∫ t in (0:ℝ)..t₀, Cv t) := by
    rw [intervalIntegral.integral_add h2eGint (hCint.const_mul (ε ^ 2)),
      intervalIntegral.integral_const_mul (2 * ε) G,
      intervalIntegral.integral_const_mul (ε ^ 2) Cv]
  rw [h1, h2, h3, h4]
  ring

/-- **Margins for the quadratic family** (the `Icc A₀ B₀` form of `GlobalBM.exists_margins_fam2`:
the membership in the chart target is needed only where the family lives). -/
lemma exists_margins_fam2_Icc {x₀ : M} {u η ζ : ℝ → E} {A₀ B₀ : ℝ}
    (huC : ContinuousOn u (Icc A₀ B₀)) (hηC : ContinuousOn η (Icc A₀ B₀))
    (hζC : ContinuousOn ζ (Icc A₀ B₀))
    (hu : ∀ t ∈ Icc A₀ B₀, u t ∈ (extChartAt I x₀).target) :
    ∃ a₁ a₂ : ℝ, a₁ < 0 ∧ 0 < a₂ ∧
      ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc A₀ B₀,
        fam2 u η ζ s t ∈ (extChartAt I x₀).target := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      u p.2 + p.1 • η p.2 + (p.1 ^ 2 / 2) • ζ p.2) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) := by
    have hsnd : ContinuousOn (fun p : ℝ × ℝ => p.2) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      continuousOn_snd
    have hfst : ContinuousOn (fun p : ℝ × ℝ => p.1) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      continuousOn_fst
    have h1 : ContinuousOn (fun p : ℝ × ℝ => u p.2) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      huC.comp hsnd (fun p hp => hp.2)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => η p.2) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      hηC.comp hsnd (fun p hp => hp.2)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => ζ p.2) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      hζC.comp hsnd (fun p hp => hp.2)
    have h4 : ContinuousOn (fun p : ℝ × ℝ => p.1 • η p.2) (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      hfst.smul h2
    have h5 : ContinuousOn (fun p : ℝ × ℝ => (p.1 ^ 2 / 2) • ζ p.2)
        (Icc (-1 : ℝ) 1 ×ˢ Icc A₀ B₀) :=
      ((hfst.pow 2).div_const 2).smul h3
    exact (h1.add h4).add h5
  obtain ⟨ε, hε, hmem⟩ := Commons.Topology.Compact.exists_pos_forall_mem_of_isCompact
    (X := E) (W := (extChartAt I x₀).target) (isOpen_extChartAt_target x₀) isCompact_Icc
    (f := fun s t => u t + s • η t + (s ^ 2 / 2) • ζ t)
    (by simpa only [] using hcont)
    (fun t ht => by simpa using hu t ht)
  exact ⟨-ε, ε, by linarith, hε, fun s hs t ht => hmem s hs t ht⟩

/-- The energy of a quadratic family is nonnegative. -/
lemma fam2Energy_nonneg (x₀ : M) (u η ζ w e ζ' : ℝ → E) {L s : ℝ} (hL : 0 ≤ L) :
    0 ≤ fam2Energy (I := I) x₀ u η ζ w e ζ' L s := by
  change 0 ≤ ∫ t in (0:ℝ)..L,
    chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
      (fam2T w e ζ' s t) (fam2T w e ζ' s t)
  exact intervalIntegral.integral_nonneg hL (fun t _ =>
    Submission.Minimal.chartGram_self_nonneg (I := I) x₀ _ _)

/-- **A minimising chart geodesic has no interior conjugate point.**  If a unit-speed chart geodesic
`γ t = (extChartAt I x₀).symm (u t)` on `[0,L]` realises the distance between its endpoints
(`hmin`) and `J` is a Jacobi field along it vanishing at `0` and at `t₀ ∈ (0,L)`, then `J ≡ 0` on
`[0,t₀]`. -/
theorem eqOn_zero_of_minimising_chart
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {u w w' : ℝ → E} {L : ℝ} (hL : 0 < L)
    (hu : ∀ t ∈ Icc (0:ℝ) L, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Icc (0:ℝ) L, HasDerivAt w (w' t) t) (hwc : ContinuousOn w' (Icc 0 L))
    (htgt : ∀ t ∈ Icc (0:ℝ) L, u t ∈ (extChartAt I x₀).target)
    (hgeo : ∀ t ∈ Icc (0:ℝ) L, w' t
      + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hunit : ∀ t ∈ Icc (0:ℝ) L,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    (hmin : Manifold.riemannianEDist I ((extChartAt I x₀).symm (u 0))
      ((extChartAt I x₀).symm (u L)) = ENNReal.ofReal L)
    {J J' J'' : ℝ → E} {t₀ : ℝ} (ht₀ : 0 < t₀) (htL : t₀ < L)
    (hJ : ∀ t ∈ Icc (0:ℝ) L, HasDerivAt J (J' t) t) (hJc : ContinuousOn J' (Icc 0 L))
    (hJ' : ∀ t ∈ Icc (0:ℝ) L, HasDerivAt J' (J'' t) t) (hJ''c : ContinuousOn J'' (Icc 0 L))
    (hjac : ∀ t ∈ Icc (0:ℝ) L, DtDsP cov x₀ u J w J' t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (J t) (w t) = 0)
    (hJ0 : J 0 = 0) (hJt : J t₀ = 0) :
    ∀ t ∈ Icc (0:ℝ) t₀, J t = 0 := by
  by_contra hcon
  have hcon' : ∃ t ∈ Icc (0:ℝ) t₀, J t ≠ 0 := by
    by_contra h
    exact hcon (fun t ht => by by_contra hne; exact h ⟨t, ht, hne⟩)
  obtain ⟨s, hs, hJs⟩ := hcon'
  have hsub : Icc (0:ℝ) t₀ ⊆ Icc (0:ℝ) L := Icc_subset_Icc le_rfl htL.le
  have hmem₀ : ∀ τ ∈ Icc (0:ℝ) (L - t₀), t₀ + τ ∈ Icc (0:ℝ) L := fun τ hτ =>
    ⟨by linarith [ht₀, hτ.1], by linarith [hτ.2]⟩
  have hs' : s ∈ Ioo (0:ℝ) t₀ := by
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hs.1 with h | h
      · exact absurd (by rw [← h]; exact hJ0) hJs
      · exact h
    · rcases eq_or_lt_of_le hs.2 with h | h
      · exact absurd (by rw [h]; exact hJt) hJs
      · exact h
  -- ## the covariant derivative of `J` at `t₀` is nonzero
  have hzp : DtQ cov x₀ u J w J' t₀ ≠ 0 := by
    intro hz
    exact hJs (eqOn_zero_of_chartJacobi (cov := cov) hmet htor x₀ ht₀
      (fun t ht => hu t (hsub ht)) (fun t ht => hw t (hsub ht))
      (fun t ht => htgt t (hsub ht)) (fun t ht => hJ t (hsub ht))
      (fun t ht => hJ' t (hsub ht)) (fun t ht => hjac t (hsub ht)) hJt hz s hs)
  set zp : E := DtQ cov x₀ u J w J' t₀ with hzpdef
  have hsrc₀ : (extChartAt I x₀).symm (u t₀) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) (htgt t₀ ⟨ht₀.le, htL.le⟩)
  have hppos : 0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) zp zp :=
    chartGram_self_pos hsrc₀ hzp
  -- ## the cut-off field
  set W : ℝ → E := cutField t₀ L (-zp) with hWdef
  set W' : ℝ → E := cutFieldD t₀ L (-zp) with hW'def
  have hWder : ∀ t : ℝ, HasDerivAt W (W' t) t := fun t => by
    rw [hWdef, hW'def]; exact hasDerivAt_cutField t₀ L (-zp) t
  have hW0 : W 0 = 0 := by rw [hWdef]; exact cutField_zero t₀ L (-zp)
  have hWL : W L = 0 := by rw [hWdef]; exact cutField_L t₀ L (-zp)
  have hWt₀ : W t₀ = -zp := by
    rw [hWdef]
    exact cutField_t₀ (ne_of_gt ht₀) (ne_of_lt htL) (-zp)
  have hWc : ContinuousOn W' (Icc (0:ℝ) L) := (continuous_cutFieldD t₀ L (-zp)).continuousOn
  have hWcC : ContinuousOn W (Icc (0:ℝ) L) := (continuous_cutField t₀ L (-zp)).continuousOn
  -- ## the perturbation integrals
  set C1 : ℝ := ∫ t in (0:ℝ)..t₀, indexIntegrand cov x₀ u W w W' t with hC1def
  set C2 : ℝ := ∫ τ in (0:ℝ)..(L - t₀), indexIntegrand cov x₀
    (fun τ' : ℝ => u (t₀ + τ')) (fun τ' : ℝ => W (t₀ + τ')) (fun τ' : ℝ => w (t₀ + τ'))
    (fun τ' : ℝ => W' (t₀ + τ')) τ with hC2def
  -- ## the choice of `ε`
  obtain ⟨ε, hεpos, hεneg⟩ := Commons.Analysis.Calculus.exists_pos_four_mul_sub_sq_mul_neg
    (a := - chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) zp zp) (c := C1 + C2)
    (by linarith)
  -- ## the variation fields
  set η₁ : ℝ → E := fun t => J t + ε • W t with hη₁def
  set e₁ : ℝ → E := fun t => J' t + ε • W' t with he₁def
  set η₂ : ℝ → E := fun τ => ε • W (t₀ + τ) with hη₂def
  set e₂ : ℝ → E := fun τ => ε • W' (t₀ + τ) with he₂def
  have hη₁der : ∀ t ∈ Icc (0:ℝ) t₀, HasDerivAt η₁ (e₁ t) t := by
    intro t ht
    have h := (hJ t (hsub ht)).add ((hWder t).const_smul ε)
    refine h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext r
    simp only [hη₁def, he₁def, Pi.add_apply, Pi.smul_apply]
  have he₁c : ContinuousOn e₁ (Icc (0:ℝ) t₀) := by
    have h1 : ContinuousOn J' (Icc (0:ℝ) t₀) := hJc.mono hsub
    have h2 : ContinuousOn W' (Icc (0:ℝ) t₀) := hWc.mono hsub
    have h := h1.add (h2.const_smul ε)
    exact h.congr (fun r _ => by simp only [he₁def, Pi.add_apply, Pi.smul_apply])
  have hη₁c : ContinuousOn η₁ (Icc (0:ℝ) t₀) := by
    have h1 : ContinuousOn J (Icc (0:ℝ) t₀) := (HasDerivAt.continuousOn hJ).mono hsub
    have h2 : ContinuousOn W (Icc (0:ℝ) t₀) := hWcC.mono hsub
    have h := h1.add (h2.const_smul ε)
    exact h.congr (fun r _ => by simp only [hη₁def, Pi.add_apply, Pi.smul_apply])
  have hη₂der : ∀ t ∈ Icc (0:ℝ) (L - t₀), HasDerivAt η₂ (e₂ t) t := by
    intro t ht
    have h := ((hWder (t₀ + t)).comp_const_add t₀ t).const_smul ε
    refine h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext r
    simp only [hη₂def, he₂def, Pi.smul_apply]
  have hW'shiftC : ContinuousOn (fun τ : ℝ => W' (t₀ + τ)) (Icc (0:ℝ) (L - t₀)) :=
    hWc.comp' (continuousOn_const.add continuousOn_id) (fun τ hτ => hmem₀ τ hτ)
  have he₂c : ContinuousOn e₂ (Icc (0:ℝ) (L - t₀)) :=
    (hW'shiftC.const_smul ε).congr (fun r _ => by simp only [he₂def, Pi.smul_apply])
  have hη₂c : ContinuousOn η₂ (Icc (0:ℝ) (L - t₀)) := by
    have hWs : ContinuousOn (fun τ : ℝ => W (t₀ + τ)) (Icc (0:ℝ) (L - t₀)) :=
      hWcC.comp' (continuousOn_const.add continuousOn_id) (fun τ hτ => hmem₀ τ hτ)
    exact (hWs.const_smul ε).congr (fun r _ => by simp only [hη₂def, Pi.smul_apply])
  have hη₁0 : η₁ 0 = 0 := by
    simp only [hη₁def, hJ0, hW0, smul_zero, add_zero]
  have hη₂L : η₂ (L - t₀) = 0 := by
    simp only [hη₂def]
    rw [show t₀ + (L - t₀) = L from by ring, hWL, smul_zero]
  have hmatch : η₁ t₀ = η₂ 0 := by
    simp only [hη₁def, hη₂def, hJt, hWt₀, add_zero, zero_add]
  -- ## margins
  have huIC : ContinuousOn u (Icc (0:ℝ) t₀) := (HasDerivAt.continuousOn hu).mono hsub
  obtain ⟨a₁', a₂', ha₁', ha₂', hstay₁'⟩ := exists_margins_fam2_Icc (x₀ := x₀)
    (u := u) (η := η₁) (ζ := fun _ => (0:E)) (A₀ := 0) (B₀ := t₀) huIC hη₁c
    continuousOn_const (fun t ht => htgt t (hsub ht))
  have hu'shiftC : ContinuousOn (fun τ : ℝ => u (t₀ + τ)) (Icc (0:ℝ) (L - t₀)) :=
    (HasDerivAt.continuousOn hu).comp' (continuousOn_const.add continuousOn_id)
      (fun τ hτ => hmem₀ τ hτ)
  obtain ⟨a₁'', a₂'', ha₁'', ha₂'', hstay₂'⟩ := exists_margins_fam2_Icc (x₀ := x₀)
    (u := fun τ : ℝ => u (t₀ + τ)) (η := η₂) (ζ := fun _ => (0:E)) (A₀ := 0) (B₀ := L - t₀)
    hu'shiftC hη₂c continuousOn_const (fun t ht => htgt (t₀ + t) (hmem₀ t ht))
  set a₁ : ℝ := max a₁' a₁'' with ha₁def
  set a₂ : ℝ := min a₂' a₂'' with ha₂def
  have ha₁ : a₁ < 0 := max_lt ha₁' ha₁''
  have ha₂ : 0 < a₂ := lt_min ha₂' ha₂''
  have hstay₁ : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (0:ℝ) t₀,
      fam2 u η₁ (fun _ => (0:E)) s t ∈ (extChartAt I x₀).target :=
    fun s hs t ht => hstay₁' s ⟨le_trans (le_max_left _ _) hs.1, le_trans hs.2 (min_le_left _ _)⟩ t ht
  have hstay₂ : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc (0:ℝ) (L - t₀),
      fam2 (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E)) s t ∈ (extChartAt I x₀).target :=
    fun s hs t ht => hstay₂' s ⟨le_trans (le_max_right _ _) hs.1, le_trans hs.2 (min_le_right _ _)⟩ t ht
  -- ## the two pieces of the energy
  set E₁ : ℝ → ℝ := fun s => fam2Energy (I := I) x₀ u η₁ (fun _ => (0:E)) w e₁
    (fun _ => (0:E)) t₀ s with hE₁def
  set E₂ : ℝ → ℝ := fun s => fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂
    (fun _ => (0:E)) (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) (L - t₀) s with hE₂def
  set En : ℝ → ℝ := fun s => E₁ s + E₂ s with hEndef
  -- ## the second derivative of the energy
  have hEd2 := fam2Energy_second_deriv_pieces (I := I) (cov := cov) hmet htor x₀
    (η₁ := η₁) (e₁ := e₁) (η₂ := η₂) (e₂ := e₂) ht₀ htL ha₁ ha₂
    hu hw hwc hη₁der he₁c hη₂der he₂c hgeo hη₁0 hη₂L hmatch hstay₁ hstay₂ htgt
  -- ## the value of the two index integrals
  have hI1 : (∫ t in (0:ℝ)..t₀, indexIntegrand cov x₀ u η₁ w e₁ t)
      = 2 * ε * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) zp zp + ε ^ 2 * C1 := by
    simp only [hη₁def, he₁def, hC1def]
    rw [integral_indexIntegrand_add_smul (cov := cov) (ε := ε) hmet htor x₀ ht₀
      (fun t ht => hu t (hsub ht)) (fun t ht => hw t (hsub ht)) (hwc.mono hsub)
      (fun t ht => htgt t (hsub ht)) (fun t ht => hJ t (hsub ht)) (hJc.mono hsub)
      (fun t ht => hJ' t (hsub ht)) (hJ''c.mono hsub)
      (fun t ht => hjac t (hsub ht)) hJ0 hJt
      (fun t _ => hWder t) (hWc.mono hsub) hW0]
    have hneg : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) zp (-zp)
        = - chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) zp zp := by
      rw [← neg_one_smul ℝ zp, chartGram_smul_snd]
      ring
    rw [← hzpdef, hWt₀, hneg]
    ring
  have hI2 : (∫ τ in (0:ℝ)..(L - t₀), indexIntegrand cov x₀ (fun τ' : ℝ => u (t₀ + τ'))
        η₂ (fun τ' : ℝ => w (t₀ + τ')) e₂ τ) = ε ^ 2 * C2 := by
    simp only [hη₂def, he₂def, hC2def]
    exact integral_indexIntegrand_smul (cov := cov) (x₀ := x₀)
      (u := fun τ : ℝ => u (t₀ + τ)) (w := fun τ : ℝ => w (t₀ + τ))
      (W := fun τ : ℝ => W (t₀ + τ)) (W' := fun τ : ℝ => W' (t₀ + τ))
      (L := L - t₀) (ε := ε)
  have hval : -2 * ((∫ t in (0:ℝ)..t₀, indexIntegrand cov x₀ u η₁ w e₁ t)
      + (∫ τ in (0:ℝ)..(L - t₀), indexIntegrand cov x₀ (fun τ' : ℝ => u (t₀ + τ'))
          η₂ (fun τ' : ℝ => w (t₀ + τ')) e₂ τ))
      = 4 * ε * (- chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) zp zp)
        - 2 * ε ^ 2 * (C1 + C2) := by
    rw [hI1, hI2]; ring
  have hEder : HasDerivAt (deriv En)
      (4 * ε * (- chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) zp zp)
        - 2 * ε ^ 2 * (C1 + C2)) 0 := by
    have hEfun : En = fun s : ℝ => fam2Energy (I := I) x₀ u η₁ (fun _ => (0:E)) w e₁
        (fun _ => (0:E)) t₀ s + fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂
        (fun _ => (0:E)) (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) (L - t₀) s := by
      funext s
      simp only [hEndef, hE₁def, hE₂def]
    rw [hEfun]
    exact hEd2.congr_deriv hval
  -- ## `En 0 = L`
  have hE1zero : E₁ 0 = t₀ := by
    have hpoint : ∀ t ∈ uIcc (0:ℝ) t₀,
        fam2G (I := I) x₀ u η₁ (fun _ => (0:E)) w e₁ (fun _ => (0:E)) 0 t = 1 := by
      intro t ht
      rw [uIcc_of_le ht₀.le] at ht
      show chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η₁ (fun _ => (0:E)) 0 t)
        (fam2T w e₁ (fun _ => (0:E)) 0 t) (fam2T w e₁ (fun _ => (0:E)) 0 t) = 1
      rw [show fam2Curve (I := I) x₀ u η₁ (fun _ => (0:E)) 0 t
          = (extChartAt I x₀).symm (u t) from by
        simp only [fam2Curve, fam2, zero_smul, zero_mul, pow_two, zero_div, add_zero]]
      rw [show fam2T w e₁ (fun _ => (0:E)) 0 t = w t from by
        simp only [fam2T, zero_smul, zero_mul, pow_two, zero_div, add_zero]]
      exact hunit t ⟨ht.1, ht.2.trans htL.le⟩
    have hfam : fam2Energy (I := I) x₀ u η₁ (fun _ => (0:E)) w e₁ (fun _ => (0:E)) t₀ 0 = t₀ := by
      change (∫ t in (0:ℝ)..t₀,
        fam2G (I := I) x₀ u η₁ (fun _ => (0:E)) w e₁ (fun _ => (0:E)) 0 t) = t₀
      rw [intervalIntegral.integral_congr hpoint]
      simp
    simpa only [hE₁def] using hfam
  have hE2zero : E₂ 0 = L - t₀ := by
    have hpoint : ∀ t ∈ uIcc (0:ℝ) (L - t₀),
        fam2G (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E))
          (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) 0 t = 1 := by
      intro t ht
      rw [uIcc_of_le (by linarith : (0:ℝ) ≤ L - t₀)] at ht
      show chartGram (I := I) x₀
        (fam2Curve (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E)) 0 t)
        (fam2T (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) 0 t)
        (fam2T (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) 0 t) = 1
      rw [show fam2Curve (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E)) 0 t
          = (extChartAt I x₀).symm (u (t₀ + t)) from by
        simp only [fam2Curve, fam2, zero_smul, zero_mul, pow_two, zero_div, add_zero]]
      rw [show fam2T (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) 0 t = w (t₀ + t) from by
        simp only [fam2T, zero_smul, zero_mul, pow_two, zero_div, add_zero]]
      exact hunit (t₀ + t) (hmem₀ t ht)
    have hfam : fam2Energy (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E))
        (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) (L - t₀) 0 = L - t₀ := by
      change (∫ t in (0:ℝ)..(L - t₀), fam2G (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂
        (fun _ => (0:E)) (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) 0 t) = L - t₀
      rw [intervalIntegral.integral_congr hpoint]
      simp
    simpa only [hE₂def] using hfam
  have hE0 : En 0 = L := by
    simp only [hEndef, hE1zero, hE2zero]
    ring
  -- ## `L ≤ En s` for all `s` in the margin
  have hEge : ∀ s ∈ Ioo a₁ a₂, L ≤ En s := by
    intro s hs
    have hsI : s ∈ Icc a₁ a₂ := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have h1 : Manifold.riemannianEDist I
        (fam2Curve (I := I) x₀ u η₁ (fun _ => (0:E)) s 0)
        (fam2Curve (I := I) x₀ u η₁ (fun _ => (0:E)) s t₀)
        ≤ ENNReal.ofReal (Real.sqrt (t₀ * E₁ s)) := by
      have h := Submission.GlobalBM.edist_piece_le (I := I) (cov := cov) hmet (x₀ := x₀)
        (u := u) (η := η₁) (ζ := fun _ => (0:E)) (w := w) (e := e₁) (ζ' := fun _ => (0:E))
        (w' := w') (L₀ := t₀) (s := s) ht₀
        (fun t ht => hu t (hsub ht)) (fun t ht => hw t (hsub ht))
        (fun t ht => hη₁der t ht) (fun t ht => hasDerivAt_const t (0:E))
        he₁c continuousOn_const (fun t ht => hstay₁ s hsI t ht)
      exact h
    have h2 : Manifold.riemannianEDist I
        (fam2Curve (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E)) s 0)
        (fam2Curve (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E)) s (L - t₀))
        ≤ ENNReal.ofReal (Real.sqrt ((L - t₀) * E₂ s)) := by
      have h := Submission.GlobalBM.edist_piece_le (I := I) (cov := cov) hmet (x₀ := x₀)
        (u := fun τ : ℝ => u (t₀ + τ)) (η := η₂) (ζ := fun _ => (0:E))
        (w := fun τ : ℝ => w (t₀ + τ)) (e := e₂) (ζ' := fun _ => (0:E))
        (w' := fun τ : ℝ => w' (t₀ + τ)) (L₀ := L - t₀) (s := s)
        (by linarith)
        (fun t ht => (hu (t₀ + t) (hmem₀ t ht)).comp_const_add t₀ t)
        (fun t ht => (hw (t₀ + t) (hmem₀ t ht)).comp_const_add t₀ t)
        (fun t ht => hη₂der t ht) (fun t ht => hasDerivAt_const t (0:E))
        he₂c continuousOn_const (fun t ht => hstay₂ s hsI t ht)
      exact h
    have hcorner : fam2Curve (I := I) x₀ u η₁ (fun _ => (0:E)) s t₀
        = fam2Curve (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E)) s 0 := by
      have h1 : fam2 u η₁ (fun _ => (0:E)) s t₀ = u t₀ + s • η₁ t₀ := by
        simp [fam2]
      have h2 : fam2 (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E)) s 0
          = u t₀ + s • η₂ 0 := by
        simp [fam2]
      rw [fam2Curve, fam2Curve, h1, h2, hmatch]
    have hbase : fam2Curve (I := I) x₀ u η₁ (fun _ => (0:E)) s 0
        = (extChartAt I x₀).symm (u 0) := by
      have hfam : fam2 u η₁ (fun _ => (0:E)) s 0 = u 0 := by
        simp [fam2, hη₁0]
      rw [fam2Curve, hfam]
    have htop : fam2Curve (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E))
        s (L - t₀) = (extChartAt I x₀).symm (u L) := by
      have hfam : fam2 (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E)) s (L - t₀)
          = u L := by
        simp only [fam2, hη₂L, smul_zero, zero_add, add_zero,
          show t₀ + (L - t₀) = L from by ring]
      rw [fam2Curve, hfam]
    rw [hcorner] at h1
    rw [hbase] at h1
    rw [htop] at h2
    have htri : Manifold.riemannianEDist I ((extChartAt I x₀).symm (u 0))
        ((extChartAt I x₀).symm (u L))
        ≤ Manifold.riemannianEDist I ((extChartAt I x₀).symm (u 0))
            (fam2Curve (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E)) s 0)
          + Manifold.riemannianEDist I
            (fam2Curve (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E)) s 0)
            ((extChartAt I x₀).symm (u L)) := Manifold.riemannianEDist_triangle
    have hsum := htri.trans (add_le_add h1 h2)
    rw [hmin] at hsum
    rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)] at hsum
    have hreal : L ≤ Real.sqrt (t₀ * E₁ s) + Real.sqrt ((L - t₀) * E₂ s) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsum
    have hE1nn : 0 ≤ E₁ s := by
      rw [hE₁def]
      exact fam2Energy_nonneg (I := I) x₀ u η₁ (fun _ => (0:E)) w e₁ (fun _ => (0:E)) ht₀.le
    have hE2nn : 0 ≤ E₂ s := by
      rw [hE₂def]
      exact fam2Energy_nonneg (I := I) x₀ (fun τ : ℝ => u (t₀ + τ)) η₂ (fun _ => (0:E))
        (fun τ : ℝ => w (t₀ + τ)) e₂ (fun _ => (0:E)) (by linarith : (0:ℝ) ≤ L - t₀)
    have hcs : (Real.sqrt (t₀ * E₁ s) + Real.sqrt ((L - t₀) * E₂ s)) ^ 2
        ≤ (t₀ + (L - t₀)) * (E₁ s + E₂ s) := by
      rw [Real.sqrt_mul (le_of_lt ht₀) (E₁ s),
        Real.sqrt_mul (by linarith : (0:ℝ) ≤ L - t₀) (E₂ s)]
      exact Commons.Analysis.Calculus.sq_sqrt_mul_add_sqrt_mul_le (le_of_lt ht₀) (by linarith) hE1nn hE2nn
    have hsq : L ^ 2 ≤ (t₀ + (L - t₀)) * (E₁ s + E₂ s) := by
      have h1 : L * L ≤ (Real.sqrt (t₀ * E₁ s) + Real.sqrt ((L - t₀) * E₂ s))
          * (Real.sqrt (t₀ * E₁ s) + Real.sqrt ((L - t₀) * E₂ s)) :=
        mul_self_le_mul_self (le_of_lt hL) hreal
      have h2 := hcs
      rw [pow_two] at h2
      rw [pow_two]
      exact h1.trans h2
    have hfin : L ≤ E₁ s + E₂ s := by
      have h2' : L * L ≤ L * (E₁ s + E₂ s) := by
        calc L * L = L ^ 2 := by ring
          _ ≤ (t₀ + (L - t₀)) * (E₁ s + E₂ s) := hsq
          _ = L * (E₁ s + E₂ s) := by ring
      exact le_of_mul_le_mul_left h2' hL
    rw [hEndef]
    exact hfin
  -- ## `En` has a local minimum at `0`
  have hloc : IsLocalMin En 0 := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨ha₁, ha₂⟩) ?_
    intro s hs
    rw [hE0]
    exact hEge s hs
  have hderiv0 : deriv En 0 = 0 := hloc.deriv_eq_zero
  have hE1diff : HasDerivAt E₁ (deriv E₁ 0) 0 := by
    rw [hE₁def]
    have h := fam2Energy_hasDerivAt (I := I) (cov := cov) hmet x₀
      (ζ := fun _ => (0:E)) (ζ' := fun _ => (0:E)) (u := u) (η := η₁) (w := w) (e := e₁)
      (w' := w') (L := t₀) ht₀.le (a₁ := a₁) (a₂ := a₂) (δ₁ := a₁ / 2) (δ₂ := a₂ / 2)
      (s₀ := 0) (A₀ := 0) (B₀ := t₀)
      (by linarith) (by linarith) (by linarith) (by linarith)
      (fun t ht => hu t (hsub ht)) (fun t ht => hw t (hsub ht))
      (fun t ht => hη₁der t ht) (fun t ht => hasDerivAt_const t (0:E))
      he₁c continuousOn_const (le_refl 0) (le_refl t₀) hstay₁
    exact h.congr_deriv h.deriv.symm
  have hE2diff : HasDerivAt E₂ (deriv E₂ 0) 0 := by
    rw [hE₂def]
    have h := fam2Energy_hasDerivAt (I := I) (cov := cov) hmet x₀
      (ζ := fun _ => (0:E)) (ζ' := fun _ => (0:E))
      (u := fun τ : ℝ => u (t₀ + τ)) (η := η₂) (w := fun τ : ℝ => w (t₀ + τ)) (e := e₂)
      (w' := fun τ : ℝ => w' (t₀ + τ)) (L := L - t₀) (by linarith)
      (a₁ := a₁) (a₂ := a₂) (δ₁ := a₁ / 2) (δ₂ := a₂ / 2) (s₀ := 0) (A₀ := 0) (B₀ := L - t₀)
      (by linarith) (by linarith) (by linarith) (by linarith)
      (fun t ht => (hu (t₀ + t) (hmem₀ t ht)).comp_const_add t₀ t)
      (fun t ht => (hw (t₀ + t) (hmem₀ t ht)).comp_const_add t₀ t)
      (fun t ht => hη₂der t ht) (fun t ht => hasDerivAt_const t (0:E))
      he₂c continuousOn_const (le_refl 0) (le_refl (L - t₀)) hstay₂
    exact h.congr_deriv h.deriv.symm
  have hEdiff : HasDerivAt En (deriv En 0) 0 := by
    have hsum : HasDerivAt (fun s : ℝ => E₁ s + E₂ s) (deriv E₁ 0 + deriv E₂ 0) 0 :=
      hE1diff.add hE2diff
    have hder : deriv (fun s : ℝ => E₁ s + E₂ s) 0 = deriv E₁ 0 + deriv E₂ 0 :=
      deriv_add hE1diff.differentiableAt hE2diff.differentiableAt
    rw [hEndef]
    exact hsum.congr_deriv hder.symm
  have hEder0 : HasDerivAt En 0 0 := hEdiff.congr_deriv hderiv0
  -- ## contradiction
  have hneg : 4 * ε * (- chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) zp zp)
      - 2 * ε ^ 2 * (C1 + C2) < 0 := hεneg
  obtain ⟨δ, hδpos, hδlt⟩ :=
    Commons.Analysis.Calculus.exists_lt_of_hasDerivAt_deriv_neg hEder0 hEder hneg
  set s₀ : ℝ := min (δ / 2) (a₂ / 2) with hs₀def
  have hs₀pos : 0 < s₀ := lt_min (by linarith) (by linarith)
  have hs₀δ : s₀ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs₀a : s₀ < a₂ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hlt := hδlt s₀ hs₀pos hs₀δ
  rw [hE0] at hlt
  have hge := hEge s₀ ⟨by linarith, hs₀a⟩
  linarith


end

end Submission.IndexCorner2
