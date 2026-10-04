import Mathlib
import Submission.Work.Diff.T.clairaut_fderiv_apply
import Submission.Work.Diff.T.dtMet_pairing_smooth
import Submission.Work.Diff.T.mvfderiv_frameVector_real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Clairaut (Schwarz) for `mvfderiv` along a smooth one-parameter family

`clairaut_mvfderiv`: if `(s, y) ↦ Φ s y` is smooth at `(t₀, x)` then the `s`-derivative at `t₀` of
the manifold derivative `s ↦ d(Φ s) x v` is the manifold derivative at `x` in direction `v` of the
pointwise `s`-derivative `y ↦ ∂ₛ Φ(s,y)|_{s = t₀}`.

The proof fixes the preferred chart at `x`.  In that chart the two sides become the two mixed
partials of the coordinate representative `ψ(s,u) = Φ s ((extChartAt I x).symm u)`, which agree by
symmetry of the second Fréchet derivative (`Work.Diff.T.clairaut_fderiv_apply`).  The translations
between `mvfderiv` on `M` and `fderiv` of `ψ` are the chart formula
(`Work.Diff.T.mvfderiv_frameVector_real`) together with the slice-differentiability of `Φ`
(`Work.Diff.T.contMDiffAt_deriv_joint`).
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Evol

/-- **Reading `mvfderiv` in the preferred chart at the base point.**  For `g : M → ℝ`
differentiable at `x`, the manifold derivative of `g` at `x` is the ordinary Fréchet derivative of
the coordinate representative `u ↦ g ((extChartAt I x).symm u)` at the chart coordinates of `x`. -/
theorem mvfderiv_self_eq_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    {g : M → ℝ} {x : M} (hg : MDifferentiableAt I 𝓘(ℝ,ℝ) g x) (v : TangentSpace I x) :
    mvfderiv I g x v
      = fderiv ℝ (fun u : E ↦ g ((extChartAt I x).symm u)) ((extChartAt I x) x) v := by
  have h := Work.Diff.T.mvfderiv_frameVector_real (I := I) (M := M) x (mem_chart_source H x) hg v
  have hfv : Submission.Geodesic.frameVector (I := I) x x v = v := by
    have hsym : (trivializationAt E (TangentSpace I) x).symmL ℝ x
        = mfderiv[Set.range I] (extChartAt I x).symm ((extChartAt I x) x) :=
      TangentBundle.symmL_trivializationAt (I := I) (mem_chart_source H x)
    have hid : mfderiv[Set.range I] (extChartAt I x).symm ((extChartAt I x) x)
        = ContinuousLinearMap.id ℝ (TangentSpace I x) :=
      mfderivWithin_range_extChartAt_symm (I := I) (x := x)
    show (Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x) x) v = v
    rw [hsym, hid]
    rfl
  rwa [hfv] at h

/-- **Slice differentiability of a smooth family.**  If `(s, y) ↦ Φ s y` is smooth at `(t₀, x)`,
then for `s` near `t₀` the slice `y ↦ Φ s y` is differentiable at `x`. -/
theorem eventually_mdifferentiableAt_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    {Φ : ℝ → M → ℝ} {t₀ : ℝ} {x : M}
    (hΦ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ Φ p.1 p.2) (t₀, x)) :
    ∀ᶠ s in 𝓝 t₀, MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M ↦ Φ s y) x := by
  set ψ : ℝ × E → ℝ := fun p ↦ Φ p.1 ((extChartAt I x).symm p.2) with hψdef
  have h2Φ : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) 2 (fun p : ℝ × M ↦ Φ p.1 p.2) (t₀, x) :=
    hΦ.of_le (by simp)
  have hsymm : ContMDiffAt 𝓘(ℝ,E) I 2 (fun u : E ↦ (extChartAt I x).symm u)
      ((extChartAt I x) x) := by
    have h := contMDiffWithinAt_extChartAt_symm_range_self (I := I) (x := x) (n := 2)
    rw [ModelWithCorners.Boundaryless.range_eq_univ, contMDiffWithinAt_univ] at h
    exact h
  have hsnd : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 2 (Prod.snd : ℝ × E → E)
      (t₀, (extChartAt I x) x) := contMDiffAt_snd
  have hψman : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) 𝓘(ℝ,ℝ) 2 ψ (t₀, (extChartAt I x) x) := by
    have hσ : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) ((𝓘(ℝ,ℝ)).prod I) 2
        (fun p : ℝ × E ↦ (p.1, (extChartAt I x).symm p.2)) (t₀, (extChartAt I x) x) :=
      contMDiffAt_fst.prodMk (hsymm.comp (t₀, (extChartAt I x) x) hsnd)
    have hpt : (fun p : ℝ × E ↦ (p.1, (extChartAt I x).symm p.2)) (t₀, (extChartAt I x) x)
        = (t₀, x) := by
      simp only [Prod.mk.injEq, true_and]
      exact (extChartAt I x).left_inv (mem_extChartAt_source x)
    have h := h2Φ.comp_of_eq hσ hpt
    simpa only [hψdef, Function.comp_def] using h
  have hψ : ContDiffAt ℝ 2 ψ (t₀, (extChartAt I x) x) := by
    have h' : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ,ℝ) 2 ψ (t₀, (extChartAt I x) x) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hψman
    exact contMDiffAt_iff_contDiffAt.mp h'
  have hψev : ∀ᶠ p in 𝓝 (t₀, (extChartAt I x) x), ContDiffAt ℝ 2 ψ p :=
    hψ.eventually (by simp)
  have hslice : ∀ᶠ s in 𝓝 t₀, ContDiffAt ℝ 2 (fun u : E ↦ ψ (s, u)) ((extChartAt I x) x) := by
    filter_upwards [(tendsto_id.prodMk_nhds tendsto_const_nhds).eventually hψev] with s hs
    have hpair : ContDiffAt ℝ 2 (fun u : E ↦ (s, u)) ((extChartAt I x) x) :=
      (contDiffAt_const (c := s)).prodMk contDiffAt_id
    exact hs.comp _ hpair
  filter_upwards [hslice] with s hs
  have hcd : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 (fun u : E ↦ ψ (s,u)) ((extChartAt I x) x) :=
    contMDiffAt_iff_contDiffAt.mpr hs
  have hcomp : ContMDiffAt I 𝓘(ℝ,ℝ) 2 ((fun u : E ↦ ψ (s,u)) ∘ (extChartAt I x)) x :=
    hcd.comp x (contMDiffAt_extChartAt (I := I) (x := x))
  have heq : (fun y : M ↦ Φ s y) =ᶠ[𝓝 x] ((fun u : E ↦ ψ (s,u)) ∘ (extChartAt I x)) := by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x] with y hy
    have hy' : (extChartAt I x).symm ((extChartAt I x) y) = y := (extChartAt I x).left_inv hy
    simp only [Function.comp_apply, hψdef, hy']
  exact (hcomp.congr_of_eventuallyEq heq).mdifferentiableAt (by simp)

theorem clairaut_mvfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    {Φ : ℝ → M → ℝ} {t₀ : ℝ} {x : M} {v : TangentSpace I x}
    (hΦ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ Φ p.1 p.2) (t₀, x)) :
    HasDerivAt (fun s : ℝ ↦ mvfderiv I (fun y : M ↦ Φ s y) x v)
      (mvfderiv I (fun y : M ↦ deriv (fun s : ℝ ↦ Φ s y) t₀) x v) t₀ := by
  set ψ : ℝ × E → ℝ := fun p ↦ Φ p.1 ((extChartAt I x).symm p.2) with hψdef
  -- ## Step 1: the coordinate representative is `C²` at `(t₀, c)`.
  have h2Φ : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) 2 (fun p : ℝ × M ↦ Φ p.1 p.2) (t₀, x) :=
    hΦ.of_le (by simp)
  have hsymm : ContMDiffAt 𝓘(ℝ,E) I 2 (fun u : E ↦ (extChartAt I x).symm u)
      ((extChartAt I x) x) := by
    have h := contMDiffWithinAt_extChartAt_symm_range_self (I := I) (x := x) (n := 2)
    rw [ModelWithCorners.Boundaryless.range_eq_univ, contMDiffWithinAt_univ] at h
    exact h
  have hsnd : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 2 (Prod.snd : ℝ × E → E)
      (t₀, (extChartAt I x) x) := contMDiffAt_snd
  have hψman : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) 𝓘(ℝ,ℝ) 2 ψ (t₀, (extChartAt I x) x) := by
    have hσ : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) ((𝓘(ℝ,ℝ)).prod I) 2
        (fun p : ℝ × E ↦ (p.1, (extChartAt I x).symm p.2)) (t₀, (extChartAt I x) x) :=
      contMDiffAt_fst.prodMk (hsymm.comp (t₀, (extChartAt I x) x) hsnd)
    have hpt : (fun p : ℝ × E ↦ (p.1, (extChartAt I x).symm p.2)) (t₀, (extChartAt I x) x)
        = (t₀, x) := by
      simp only [Prod.mk.injEq, true_and]
      exact (extChartAt I x).left_inv (mem_extChartAt_source x)
    have h := h2Φ.comp_of_eq hσ hpt
    simpa only [hψdef, Function.comp_def] using h
  have hψ : ContDiffAt ℝ 2 ψ (t₀, (extChartAt I x) x) := by
    have h' : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ,ℝ) 2 ψ (t₀, (extChartAt I x) x) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hψman
    exact contMDiffAt_iff_contDiffAt.mp h'
  -- ## Step 2: Clairaut in the chart.
  have hcore : HasDerivAt (fun s : ℝ ↦ fderiv ℝ (fun u : E ↦ ψ (s, u)) ((extChartAt I x) x) v)
      (fderiv ℝ (fun u : E ↦ deriv (fun s : ℝ ↦ ψ (s, u)) t₀) ((extChartAt I x) x) v) t₀ :=
    Work.Diff.T.clairaut_fderiv_apply (Φ := ψ) hψ v
  -- ## Step 3: near `t₀` the left-hand side is the chart expression.
  have hsliceMD := eventually_mdifferentiableAt_slice (I := I) (M := M) hΦ
  have hLHS : (fun s : ℝ ↦ mvfderiv I (fun y : M ↦ Φ s y) x v)
      =ᶠ[𝓝 t₀] (fun s : ℝ ↦ fderiv ℝ (fun u : E ↦ ψ (s, u)) ((extChartAt I x) x) v) := by
    filter_upwards [hsliceMD] with s hs
    rw [mvfderiv_self_eq_fderiv (I := I) (M := M) hs v]
  -- ## Step 4: the value on the right-hand side.
  have hgMD : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M ↦ deriv (fun s : ℝ ↦ Φ s y) t₀) x :=
    (Work.Diff.T.contMDiffAt_deriv_joint (I := I) (M := M) hΦ).mdifferentiableAt (by simp)
  have hRHS : mvfderiv I (fun y : M ↦ deriv (fun s : ℝ ↦ Φ s y) t₀) x v
      = fderiv ℝ (fun u : E ↦ deriv (fun s : ℝ ↦ ψ (s, u)) t₀) ((extChartAt I x) x) v := by
    rw [mvfderiv_self_eq_fderiv (I := I) (M := M) hgMD v]
  rw [hRHS]
  exact hcore.congr_of_eventuallyEq hLHS

end Work.Diff.Evol
