import Mathlib
import Submission.Work.Diff.T.mvfderiv_frameVector_real
import Submission.Work.Diff.T.clairaut_fderiv_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-- If the chart representative `u ↦ g ((extChartAt I x₀).symm u)` of a real-valued function `g`
on a manifold is differentiable at the chart coordinates of `x₀`, then `g` is manifold
differentiable at `x₀`. -/
private theorem mdifferentiableAt_of_chart_rep_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : M → ℝ} {x₀ : M}
    (h : DifferentiableAt ℝ (fun u : E ↦ g ((extChartAt I x₀).symm u)) ((extChartAt I x₀) x₀)) :
    MDifferentiableAt I 𝓘(ℝ,ℝ) g x₀ := by
  have h' : DifferentiableWithinAt ℝ (fun u : E ↦ g ((extChartAt I x₀).symm u))
      ((fun u : E ↦ (extChartAt I x₀).symm u) ⁻¹' (Set.univ : Set M) ∩ Set.range I)
      ((extChartAt I x₀) x₀) :=
    h.differentiableWithinAt.mono (fun y _ => Set.mem_univ y)
  exact h'.mdifferentiableWithinAt_of_comp_extChartAt_symm

/-- Partial differentiation of a `C²` function `Ψ : ℝ × E → ℝ` in the first variable, at a fixed
time `t`, produces a function of the second variable which is differentiable at `u₀`. -/
private theorem differentiableAt_deriv_slice_fst_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : ℝ × E → ℝ} {t : ℝ} {u₀ : E} (hΨ : ContDiffAt ℝ 2 Ψ (t, u₀)) :
    DifferentiableAt ℝ (fun u : E ↦ deriv (fun s : ℝ ↦ Ψ (s, u)) t) u₀ := by
  -- `fderiv ℝ Ψ` is `C¹`, hence differentiable, at `(t, u₀)`.
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ Ψ) (t, u₀) := hΨ.fderiv_right (m := 1) (by norm_num)
  have hfd' : DifferentiableAt ℝ (fderiv ℝ Ψ) (t, u₀) := hfd.differentiableAt (by norm_num)
  have hslice : DifferentiableAt ℝ (fun u : E ↦ (t, u)) u₀ :=
    (differentiableAt_const t).prodMk differentiableAt_id
  have hcomp : DifferentiableAt ℝ (fun u : E ↦ fderiv ℝ Ψ (t, u)) u₀ :=
    hfd'.comp u₀ hslice
  have h1 : DifferentiableAt ℝ (fun u : E ↦ (fderiv ℝ Ψ (t, u)) (1, 0)) u₀ :=
    hcomp.clm_apply (differentiableAt_const ((1, 0) : ℝ × E))
  -- near `u₀` the two expressions agree
  refine h1.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℝ Ψ (t, u) := by
    have h2 : ∀ᶠ p in 𝓝 ((t, u₀) : ℝ × E), ContDiffAt ℝ 2 Ψ p := hΨ.eventually (by norm_num)
    exact ((tendsto_const_nhds.prodMk_nhds tendsto_id).eventually h2).mono
      fun u hu => hu.differentiableAt (by norm_num)
  filter_upwards [hev] with u hu
  have hP : HasFDerivAt Ψ (fderiv ℝ Ψ (t, u)) (t, u) := hu.hasFDerivAt
  have hγ : HasFDerivAt (fun s : ℝ ↦ (s, u)) (ContinuousLinearMap.inl ℝ ℝ E) t :=
    hasFDerivAt_prodMk_left (𝕜 := ℝ) t u
  have hcf : HasDerivAt (fun s : ℝ ↦ Ψ (s, u))
      (((fderiv ℝ Ψ (t, u)).comp (ContinuousLinearMap.inl ℝ ℝ E)) 1) t :=
    (hP.comp t hγ).hasDerivAt
  rw [hcf.deriv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- Interchange of the time derivative with `mvfderiv` along a jointly smooth family: if
`(s, y) ↦ Φ s y` is `C^∞` at `(t, x)`, then `s ↦ mvfderiv I (fun y ↦ Φ s y) x v` is differentiable
at `t` with derivative obtained by differentiating pointwise in `s` (Clairaut-Schwarz; the chart at
`x` is fixed, so neither the tangent vector `v` nor the trivialisation of the target `ℝ` moves). -/
theorem hasDerivAt_mvfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    {Φ : ℝ → M → ℝ} {t : ℝ} {x : M} {v : TangentSpace I x}
    (hΦ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ Φ p.1 p.2) (t, x)) :
    HasDerivAt (fun s : ℝ ↦ mvfderiv I (fun y : M ↦ Φ s y) x v)
      (mvfderiv I (fun y : M ↦ deriv (fun s : ℝ ↦ Φ s y) t) x v) t := by
  classical
  -- the coordinate vector of `v` in the chart at `x`, so that `v` is the corresponding frame vector
  set w : E := (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v with hwdef
  have hv : v = Submission.Geodesic.frameVector (I := I) x x w := by
    rw [hwdef]
    show v = (trivializationAt E (TangentSpace I) x).symmL ℝ x
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v)
    exact (Trivialization.symmL_continuousLinearMapAt (R := ℝ)
      (trivializationAt E (TangentSpace I) x) (mem_baseSet_trivializationAt E _ x) v).symm
  -- the chart representative of the family, and its `C²`-regularity
  let Ψ : ℝ × E → ℝ := fun p ↦ Φ p.1 ((extChartAt I x).symm p.2)
  have hΨcd : ContDiffAt ℝ 2 Ψ (t, (extChartAt I x) x) := by
    have hφsymm : ContMDiffAt 𝓘(ℝ,E) I ∞ (fun u : E ↦ (extChartAt I x).symm u)
        ((extChartAt I x) x) :=
      (contMDiffOn_extChartAt_symm (I := I) x).contMDiffAt
        ((isOpen_extChartAt_target (I := I) x).mem_nhds
          ((extChartAt I x).map_source (mem_extChartAt_source x)))
    have hchart : ContMDiffAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) (𝓘(ℝ,ℝ).prod I) ∞
        (fun p : ℝ × E ↦ (p.1, (extChartAt I x).symm p.2)) (t, (extChartAt I x) x) :=
      contMDiffAt_fst.prodMk (hφsymm.comp (t, (extChartAt I x) x) contMDiffAt_snd)
    have hΨmd : ContMDiffAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ Ψ (t, (extChartAt I x) x) :=
      hΦ.comp_of_eq hchart (by simp)
    have h' : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ,ℝ) ∞ Ψ (t, (extChartAt I x) x) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hΨmd
    exact ((contMDiffAt_iff_contDiffAt).mp h').of_le (by norm_num)
  -- `clairaut_fderiv_apply` in the chart at `x`
  have hcl := Work.Diff.T.clairaut_fderiv_apply hΨcd w
  -- the left-hand side, read in the chart at `x`, agrees with the chart expression near `t`
  have hLHS : (fun s : ℝ ↦ mvfderiv I (fun y : M ↦ Φ s y) x v)
      =ᶠ[𝓝 t] (fun s : ℝ ↦ fderiv ℝ (fun u : E ↦ Ψ (s, u)) ((extChartAt I x) x) w) := by
    have hev : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (fun u : E ↦ Ψ (s, u)) ((extChartAt I x) x) := by
      have h2 : ∀ᶠ p in 𝓝 ((t, (extChartAt I x) x) : ℝ × E), ContDiffAt ℝ 2 Ψ p :=
        hΨcd.eventually (by norm_num)
      have hslice : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 2 Ψ (s, (extChartAt I x) x) :=
        (tendsto_id.prodMk_nhds tendsto_const_nhds).eventually h2
      exact hslice.mono fun s hs =>
        (hs.differentiableAt (by norm_num)).comp ((extChartAt I x) x)
          ((differentiableAt_const s).prodMk differentiableAt_id)
    filter_upwards [hev] with s hs
    have hmd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M ↦ Φ s y) x :=
      mdifferentiableAt_of_chart_rep_aux hs
    rw [hv, Work.Diff.T.mvfderiv_frameVector_real (I := I) x (mem_chart_source H x) hmd w]
  -- the right-hand side, read in the chart at `x`
  have hRHS : mvfderiv I (fun y : M ↦ deriv (fun s : ℝ ↦ Φ s y) t) x v
      = fderiv ℝ (fun u : E ↦ deriv (fun s : ℝ ↦ Ψ (s, u)) t) ((extChartAt I x) x) w := by
    have hmd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M ↦ deriv (fun s : ℝ ↦ Φ s y) t) x :=
      mdifferentiableAt_of_chart_rep_aux (differentiableAt_deriv_slice_fst_aux hΨcd)
    rw [hv, Work.Diff.T.mvfderiv_frameVector_real (I := I) x (mem_chart_source H x) hmd w]
  rw [hRHS]
  exact (Filter.EventuallyEq.hasDerivAt_iff hLHS).mpr hcl

end Work.Diff.GE
