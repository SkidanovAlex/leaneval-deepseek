import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Commons.Analysis.Calculus

/-- If `u` and `v` are smooth curves in a finite-dimensional real normed space and `u' t₀ ≠ 0`,
then `v` agrees, near `t₀`, with the composition of `u` with a smooth (indeed `C^∞`) function
defined on a neighbourhood of `u t₀`.  Equivalently, `v` depends smoothly on `u` locally.

This is the "reparametrisation" or "local section" form of the inverse function theorem: the
hypothesis `deriv u t₀ ≠ 0` makes `u` locally injective, and a smooth local left inverse to `u`
is produced by projecting along a linear functional that is non-degenerate on `u' t₀`. -/
theorem exists_contDiffAt_eqOn_of_deriv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u v : ℝ → E} {t₀ : ℝ}
    (hu : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) u t₀)
    (hv : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) v t₀)
    (hne : deriv u t₀ ≠ 0) :
    ∃ F : E → E, ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) F (u t₀) ∧
      (∀ᶠ t in nhds t₀, F (u t) = v t) := by
  have hn : (((⊤ : ENat) : WithTop ENat)) ≠ 0 := by simp
  -- A continuous linear functional taking the value `1` on `deriv u t₀`.
  obtain ⟨g, -, hg2⟩ := exists_dual_vector ℝ (deriv u t₀) (by rwa [norm_ne_zero_iff])
  have hgw : g (deriv u t₀) = ‖deriv u t₀‖ := hg2
  let φ : E →L[ℝ] ℝ := (‖deriv u t₀‖)⁻¹ • g
  have hφ : φ (deriv u t₀) = 1 := by
    show (‖deriv u t₀‖)⁻¹ * (g (deriv u t₀)) = 1
    rw [hgw, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
  have hφne : φ (deriv u t₀) ≠ 0 := by rw [hφ]; exact one_ne_zero
  -- The scalar curve `G = φ ∘ u`, whose derivative at `t₀` is `φ (deriv u t₀) ≠ 0`.
  let G : ℝ → ℝ := fun t => φ (u t)
  have hG_cd : ContDiffAt ℝ (((⊤ : ENat) : WithTop ENat)) G t₀ :=
    ((φ.contDiff).contDiffAt).comp t₀ hu
  have hu_deriv : HasDerivAt u (deriv u t₀) t₀ := (hu.differentiableAt hn).hasDerivAt
  have hG_deriv : HasDerivAt (fun t => φ (u t)) (φ (deriv u t₀)) t₀ :=
    φ.hasFDerivAt.comp_hasDerivAt t₀ hu_deriv
  -- An invertible linear map giving the derivative of `G` at `t₀`.
  have hG_fderiv : HasFDerivAt (fun t => φ (u t))
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (φ (deriv u t₀)) hφne) :
        ℝ →L[ℝ] ℝ) t₀ :=
    hG_deriv.hasFDerivAt_equiv hφne
  have hG_fderiv' : HasFDerivAt G
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (φ (deriv u t₀)) hφne) :
        ℝ →L[ℝ] ℝ) t₀ :=
    hG_fderiv
  -- A smooth local inverse of `G` near `G t₀`.
  let Ginv : ℝ → ℝ := hG_cd.localInverse hG_fderiv' hn
  have hGinv_cd : ContDiffAt ℝ (((⊤ : ENat) : WithTop ENat)) Ginv (G t₀) :=
    hG_cd.to_localInverse hG_fderiv' hn
  have hGinv_left : ∀ᶠ t in 𝓝 t₀, Ginv (G t) = t :=
    (hG_cd.hasStrictFDerivAt' hG_fderiv' hn).eventually_left_inverse
  have h_apply : Ginv (G t₀) = t₀ := hG_cd.localInverse_apply_image hG_fderiv' hn
  -- A smooth local left inverse of `u`: `h x = Ginv (φ x)`.
  let h : E → ℝ := fun x => Ginv (φ x)
  have h_cd : ContDiffAt ℝ (((⊤ : ENat) : WithTop ENat)) h (u t₀) :=
    hGinv_cd.comp (u t₀) ((φ.contDiff).contDiffAt)
  have h_apply' : h (u t₀) = t₀ := h_apply
  -- The desired function `F = v ∘ h`.
  let F : E → E := fun x => v (h x)
  have hF_cd : ContDiffAt ℝ (((⊤ : ENat) : WithTop ENat)) F (u t₀) := by
    have hv' : ContDiffAt ℝ (((⊤ : ENat) : WithTop ENat)) v (h (u t₀)) := by
      rw [h_apply']; exact hv
    exact hv'.comp (u t₀) h_cd
  refine ⟨F, hF_cd, ?_⟩
  filter_upwards [hGinv_left] with t ht
  simp only [F, h, G] at *
  rw [ht]

end Commons.Analysis.Calculus