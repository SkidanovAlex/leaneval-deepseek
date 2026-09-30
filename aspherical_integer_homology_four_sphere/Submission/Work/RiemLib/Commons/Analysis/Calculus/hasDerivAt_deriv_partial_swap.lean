import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.RiemLib.Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Swapping the order of partial differentiation (one-variable `deriv` form)

If `F : ℝ × ℝ → E` is `C²` at `(s₀, t₀)`, then the iterated partial derivatives
`∂/∂s (∂F/∂t)` and `∂/∂t (∂F/∂s)` agree at `(s₀, t₀)`. This is the
Clairaut–Schwarz theorem, stated here using the one-dimensional derivative
`deriv` on the two coordinate slices.
-/

open scoped Topology
open Filter

namespace Commons.Analysis.Calculus

/-- The derivative at `x₁` of the slice `s ↦ Ψ (s, x₂)` is `(fderiv Ψ (x₁,x₂)) (1,0)`. -/
lemma hasDerivAt_slice_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : ℝ × ℝ → E} {x₁ x₂ : ℝ} (h : DifferentiableAt ℝ Ψ (x₁, x₂)) :
    HasDerivAt (fun s : ℝ => Ψ (s, x₂)) ((fderiv ℝ Ψ (x₁, x₂)) (1, 0)) x₁ := by
  have hg : HasDerivAt (fun s : ℝ => (s, x₂)) (1, 0) x₁ := by
    simpa using (hasDerivAt_id x₁).prodMk (hasDerivAt_const (x := x₁) (c := x₂))
  exact h.hasFDerivAt.comp_hasDerivAt x₁ hg

/-- The derivative at `x₂` of the slice `t ↦ Ψ (x₁, t)` is `(fderiv Ψ (x₁,x₂)) (0,1)`. -/
lemma hasDerivAt_slice_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : ℝ × ℝ → E} {x₁ x₂ : ℝ} (h : DifferentiableAt ℝ Ψ (x₁, x₂)) :
    HasDerivAt (fun t : ℝ => Ψ (x₁, t)) ((fderiv ℝ Ψ (x₁, x₂)) (0, 1)) x₂ := by
  have hg : HasDerivAt (fun t : ℝ => (x₁, t)) (0, 1) x₂ := by
    simpa using (hasDerivAt_const (x := x₂) (c := x₁)).prodMk (hasDerivAt_id x₂)
  exact h.hasFDerivAt.comp_hasDerivAt x₂ hg

/-- `deriv` along the second coordinate slice computes the second partial derivative. -/
lemma deriv_slice_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} {s t₀ : ℝ} (h : DifferentiableAt ℝ F (s, t₀)) :
    deriv (fun t : ℝ => F (s, t)) t₀ = (fderiv ℝ F (s, t₀)) (0, 1) := by
  have hg : HasDerivAt (fun t : ℝ => (s, t)) (0, 1) t₀ := by
    simpa using (hasDerivAt_const (x := t₀) (c := s)).prodMk (hasDerivAt_id t₀)
  exact (h.hasFDerivAt.comp_hasDerivAt t₀ hg).deriv

/-- `deriv` along the first coordinate slice computes the first partial derivative. -/
lemma deriv_slice_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} {s₀ t : ℝ} (h : DifferentiableAt ℝ F (s₀, t)) :
    deriv (fun s : ℝ => F (s, t)) s₀ = (fderiv ℝ F (s₀, t)) (1, 0) := by
  have hg : HasDerivAt (fun s : ℝ => (s, t)) (1, 0) s₀ := by
    simpa using (hasDerivAt_id s₀).prodMk (hasDerivAt_const (x := s₀) (c := t))
  exact (h.hasFDerivAt.comp_hasDerivAt s₀ hg).deriv

/-- Evaluation of a `C¹` `fderiv` at a fixed vector stays differentiable. -/
lemma differentiableAt_fderiv_apply_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} {x : ℝ × ℝ} (hF : ContDiffAt ℝ 2 F x) (v : ℝ × ℝ) :
    DifferentiableAt ℝ (fun y : ℝ × ℝ => (fderiv ℝ F y) v) x := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact hfd.clm_apply (differentiableAt_const v)

theorem hasDerivAt_deriv_partial_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} {s₀ t₀ : ℝ} (hF : ContDiffAt ℝ 2 F (s₀, t₀)) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => F (s, t)) t₀)
      (deriv (fun t : ℝ => deriv (fun s : ℝ => F (s, t)) s₀) t₀) s₀ := by
  -- An open neighbourhood on which `F` is `C²`.
  obtain ⟨u, hu_mem, hu⟩ := hF.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨v, hvu, hv_open, hv_mem⟩ := mem_nhds_iff.mp hu_mem
  have hv_cd : ContDiffOn ℝ 2 F v := hu.mono hvu
  have diff_of_mem : ∀ y ∈ v, DifferentiableAt ℝ F y := fun y hy =>
    (hv_cd.contDiffAt (hv_open.mem_nhds hy)).differentiableAt (by norm_num)
  -- The two coordinate slices eventually stay in `v`.
  have htend_s : Tendsto (fun s : ℝ => (s, t₀)) (𝓝 s₀) (𝓝 (s₀, t₀)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  have htend_t : Tendsto (fun t : ℝ => (s₀, t)) (𝓝 t₀) (𝓝 (s₀, t₀)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  have hev_s : ∀ᶠ s in 𝓝 s₀, (s, t₀) ∈ v := htend_s.eventually (hv_open.mem_nhds hv_mem)
  have hev_t : ∀ᶠ t in 𝓝 t₀, (s₀, t) ∈ v := htend_t.eventually (hv_open.mem_nhds hv_mem)
  -- Replace the `deriv` slices by the corresponding `fderiv` evaluations, eventually.
  have hEq_s : (fun s : ℝ => deriv (fun t : ℝ => F (s, t)) t₀) =ᶠ[𝓝 s₀]
      (fun s : ℝ => (fderiv ℝ F (s, t₀)) (0, 1)) := by
    filter_upwards [hev_s] with s hs
    exact deriv_slice_snd (diff_of_mem (s, t₀) hs)
  have hEq_t : (fun t : ℝ => deriv (fun s : ℝ => F (s, t)) s₀) =ᶠ[𝓝 t₀]
      (fun t : ℝ => (fderiv ℝ F (s₀, t)) (1, 0)) := by
    filter_upwards [hev_t] with t ht
    exact deriv_slice_fst (diff_of_mem (s₀, t) ht)
  -- Derivative in the `s`-direction.
  have hMain : HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => F (s, t)) t₀)
      ((fderiv ℝ (fun y : ℝ × ℝ => (fderiv ℝ F y) (0, 1)) (s₀, t₀)) (1, 0)) s₀ := by
    rw [Filter.EventuallyEq.hasDerivAt_iff hEq_s]
    exact hasDerivAt_slice_snd (differentiableAt_fderiv_apply_prod hF (0, 1))
  -- Derivative in the `t`-direction, evaluated as the other mixed partial.
  have hDeriv_t : HasDerivAt (fun t : ℝ => (fderiv ℝ F (s₀, t)) (1, 0))
      ((fderiv ℝ (fun y : ℝ × ℝ => (fderiv ℝ F y) (1, 0)) (s₀, t₀)) (0, 1)) t₀ :=
    hasDerivAt_slice_fst (differentiableAt_fderiv_apply_prod hF (1, 0))
  have hC : deriv (fun t : ℝ => deriv (fun s : ℝ => F (s, t)) s₀) t₀
      = (fderiv ℝ (fun y : ℝ × ℝ => (fderiv ℝ F y) (1, 0)) (s₀, t₀)) (0, 1) := by
    rw [Filter.EventuallyEq.deriv_eq hEq_t]
    exact hDeriv_t.deriv
  -- Symmetry of the mixed second derivative.
  have hswap := Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two
    hv_open hv_mem hv_cd (1, 0) (0, 1)
  rw [hC, hswap]
  exact hMain

end Commons.Analysis.Calculus