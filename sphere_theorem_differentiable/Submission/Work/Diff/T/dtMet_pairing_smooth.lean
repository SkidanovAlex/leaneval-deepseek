import Mathlib
import Submission.Work.Diff.T.lc_deps
import Submission.Work.Diff.T.metric_pairing_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.T

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- The partial derivative in the first variable of a `C^∞` function on a product `ℝ × E` is
again `C^∞`. -/
theorem contDiffAt_deriv_param
    {E₁ F₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    {Ψ : ℝ × E₁ → F₁} {t₀ : ℝ} {u₀ : E₁} (h : ContDiffAt ℝ ∞ Ψ (t₀, u₀)) :
    ContDiffAt ℝ ∞ (fun u : E₁ => deriv (fun t : ℝ => Ψ (t, u)) t₀) u₀ := by
  have hswap : ContDiffAt ℝ ∞ (fun p : E₁ × ℝ => (p.2, p.1)) (u₀, t₀) :=
    (ContinuousLinearEquiv.prodComm ℝ E₁ ℝ).contDiff.contDiffAt
  have huncurry :
      ContDiffAt ℝ ∞ (Function.uncurry fun u : E₁ => fun t : ℝ => Ψ (t, u)) (u₀, t₀) :=
    ContDiffAt.comp (u₀, t₀) h hswap
  have h1 : ContDiffAt ℝ ∞ (fun u : E₁ => fderiv ℝ (fun t : ℝ => Ψ (t, u)) t₀) u₀ :=
    ContDiffAt.fderiv (x₀ := u₀) (g := fun _ : E₁ => t₀) (f := fun u t => Ψ (t, u))
      huncurry contDiffAt_const (by simp)
  have h2 : ContDiffAt ℝ ∞ (fun u : E₁ => (fderiv ℝ (fun t : ℝ => Ψ (t, u)) t₀) 1) u₀ :=
    h1.clm_apply (contDiffAt_const (c := (1 : ℝ)))
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  exact (fderiv_apply_one_eq_deriv :
    (fderiv ℝ (fun t : ℝ => Ψ (t, u)) t₀) 1 = deriv (fun t : ℝ => Ψ (t, u)) t₀)

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- If `Φ : ℝ × M → ℝ` is smooth at `(t₀, x)` then the partial derivative
`y ↦ ∂ₜ Φ (t₀, y)` is smooth at `x`. -/
theorem contMDiffAt_deriv_joint
    {Φ : ℝ × M → ℝ} {t₀ : ℝ} {x : M}
    (hΦ : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ Φ (t₀, x)) :
    ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y : M => deriv (fun t : ℝ => Φ (t, y)) t₀) x := by
  set c : E → M := fun u => (extChartAt I x).symm u with hc
  set u₀ : E := (extChartAt I x) x with hu₀
  have hcu : c u₀ = x := by
    simp only [c, u₀]
    exact (extChartAt I x).left_inv (mem_extChartAt_source x)
  have hc_smooth : ContMDiffAt 𝓘(ℝ,E) I ∞ c u₀ := by
    have h := contMDiffWithinAt_extChartAt_symm_range_self (I := I) (x := x) (n := ∞)
    rw [ModelWithCorners.Boundaryless.range_eq_univ, contMDiffWithinAt_univ] at h
    simpa only [c, u₀] using h
  have hσ : ContMDiffAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) (𝓘(ℝ,ℝ).prod I) ∞
      (fun p : ℝ × E => (p.1, c p.2)) (t₀, u₀) :=
    contMDiffAt_fst.prodMk (hc_smooth.comp (t₀, u₀) contMDiffAt_snd)
  have hpt : (fun p : ℝ × E => (p.1, c p.2)) (t₀, u₀) = (t₀, x) := by
    rw [show (fun p : ℝ × E => (p.1, c p.2)) (t₀, u₀) = (t₀, c u₀) from rfl, hcu]
  have hΨm : ContMDiffAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × E => Φ (p.1, c p.2)) (t₀, u₀) :=
    ContMDiffAt.comp_of_eq hΦ hσ hpt
  have hΨ : ContDiffAt ℝ ∞ (fun p : ℝ × E => Φ (p.1, c p.2)) (t₀, u₀) := by
    have h' : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × E => Φ (p.1, c p.2)) (t₀, u₀) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hΨm
    exact contMDiffAt_iff_contDiffAt.mp h'
  have hderiv : ContDiffAt ℝ ∞ (fun u : E => deriv (fun t : ℝ => Φ (t, c u)) t₀) u₀ :=
    contDiffAt_deriv_param hΨ
  have hFc : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞
      (fun u : E => deriv (fun t : ℝ => Φ (t, c u)) t₀) u₀ :=
    contMDiffAt_iff_contDiffAt.mpr hderiv
  have hcomp := ContMDiffAt.comp x hFc (contMDiffAt_extChartAt (I := I) (x := x))
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_source_mem_nhds (I := I) x] with y hy
  have hy' : (extChartAt I x).symm ((extChartAt I x) y) = y :=
    (extChartAt I x).left_inv hy
  simp only [Function.comp_apply, hc, hy']

theorem dtMet_pairing_smooth
    {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J) {t₀ : ℝ} (hJs : JointSmooth G J)
    (ht₀ : t₀ ∈ J) {Y Z : Π x : M, TangentSpace I x} (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (x : M) :
    ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y : M ↦ dtMet G t₀ y (Y y) (Z y)) x := by
  set Φ : ℝ × M → ℝ := fun p => (G p.1).inner p.2 (Y p.2) (Z p.2) with hΦ
  have hΦsm : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ Φ (J ×ˢ univ) := by
    rw [hΦ]
    exact metric_pairing_smooth (I := I) (M := M) hJs hY hZ
  have hmem : J ×ˢ univ ∈ 𝓝 (t₀, x) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (hJ.mem_nhds ht₀) Filter.univ_mem
  have hΦat : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ Φ (t₀, x) := hΦsm.contMDiffAt hmem
  have hmain := contMDiffAt_deriv_joint (I := I) (M := M) hΦat
  simpa only [dtMet, hΦ] using hmain

end Work.Diff.T
