import Mathlib
import Submission.Work.Drive.stripData
import Submission.Work.Drive.curve_deriv_ne_zero
import Submission.Work.Drive.dstripU_boundary_val

/-!
# The boundary derivative of the band datum `M` along the unit circle

At `τ = 0` the band datum `M` is the complexified curve point (`Work.Drive.dstripU_boundary_val`):

`M (e^{iσ}, 0) = symmC (curve γ σ)`,

so the derivative of the strip map `p ↦ M (e^{i p.1}, p.2)` at `(α, 0)` in the direction `(1, 0)`
is the derivative of `σ ↦ symmC (curve γ σ)`, i.e. the *complexification of the tangent vector*
`symmC (deriv (curve γ) α)`.  Since `symmC` is injective and the tangent of an embedded closed
plane curve never vanishes (`Work.Drive.curve_deriv_ne_zero`), this is non-zero.

The only point that needs care: the hypothesis `hMval` describes `M` on the *circle bundle*
`‖x‖ = 1`, `τ ≥ 0` (with `τ ↦ √τ` not differentiable at `0`), so the derivative of the *two-variable*
map `p ↦ M (e^{i p.1}, p.2)` at `(α, 0)` must be computed from its restriction to the line
`τ = 0` — which is a chain rule, not a computation.
-/

namespace Work.Drive

open scoped ContDiff Manifold

noncomputable section

/-- The complexification `Neutral.symmC : ℝ × ℝ → ℂ` of a plane vector, as a continuous linear map
of real normed spaces. -/
def symmCLM : (ℝ × ℝ) →L[ℝ] ℂ where
  toFun := Neutral.symmC
  map_add' := fun u v => Neutral.symmC_add u v
  map_smul' := fun c v => by rw [Neutral.symmC_smul, Complex.real_smul]; simp
  cont := Neutral.contDiff_symmC.continuous

lemma symmCLM_apply (v : ℝ × ℝ) : symmCLM v = Neutral.symmC v := rfl

lemma symmCLM_injective : Function.Injective symmCLM := by
  intro u v huv
  have h : Neutral.symmC (u - v) = 0 := by
    rw [Neutral.symmC_sub, ← symmCLM_apply u, ← symmCLM_apply v, huv, sub_self]
  exact sub_eq_zero.mp (Neutral.symmC_eq_zero_iff.mp h)

/-- **Boundary derivative.**  The derivative of the band datum along the unit circle at `τ = 0` is
the complexified tangent vector of the curve, hence non-zero. -/
theorem dstripU_boundary_deriv {γ : Circle → ℝ × ℝ} {M : ℂ × ℝ → ℂ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ))
    (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (α : ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => M (dstripU p.1, p.2)) (α, 0) (1, 0) ≠ 0 := by
  set F : ℝ × ℝ → ℂ := fun p => M (dstripU p.1, p.2) with hFdef
  -- ## smoothness and differentiability of `F`
  have hFsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
    hFdef.symm ▸ hMsm.comp ((contDiff_dstripU.comp contDiff_fst).prodMk contDiff_snd)
  have hFd : HasFDerivAt F (fderiv ℝ F (α, 0)) (α, 0) :=
    (hFsm.contDiffAt.differentiableAt (by decide)).hasFDerivAt
  -- ## the derivative of `s ↦ F (s, 0)` from the chain rule
  have hcomp : HasFDerivAt (F ∘ (ContinuousLinearMap.inl ℝ ℝ ℝ))
      ((fderiv ℝ F (α, 0)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) α :=
    hFd.comp α (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.inl ℝ ℝ ℝ))
  have hF1 : HasDerivAt (fun s : ℝ => F (s, 0)) (fderiv ℝ F (α, 0) (1, 0)) α := by
    have h := hcomp.hasDerivAt
    simpa [Function.comp_def, ContinuousLinearMap.inl_apply, ContinuousLinearMap.comp_apply]
      using h
  -- ## the derivative of the complexified curve `s ↦ symmC (curve γ s)`
  have hcurve : HasDerivAt (curve γ) (deriv (curve γ) α) α :=
    ((Neutral.contDiff_curve_top hγ).contDiffAt.differentiableAt (by decide)).hasDerivAt
  have hsC : HasFDerivAt (Neutral.symmC : ℝ × ℝ → ℂ) symmCLM (curve γ α) :=
    ContinuousLinearMap.hasFDerivAt symmCLM
  have hsc : HasDerivAt (fun s : ℝ => Neutral.symmC (curve γ s)) (symmCLM (deriv (curve γ) α)) α := by
    have h' := hsC.comp_hasDerivAt α hcurve
    simpa only [Function.comp_def] using h'
  -- ## the two derivatives agree (they are the derivative of the same function)
  have hM0 : ∀ s : ℝ, F (s, 0) = Neutral.symmC (curve γ s) :=
    fun s => dstripU_boundary_val hMval s
  have hF1' : HasDerivAt (fun s : ℝ => F (s, 0)) (symmCLM (deriv (curve γ) α)) α := by
    have hfun : (fun s : ℝ => F (s, 0)) = fun s : ℝ => Neutral.symmC (curve γ s) :=
      funext hM0
    exact hfun.symm ▸ hsc
  have hEq : fderiv ℝ F (α, 0) (1, 0) = symmCLM (deriv (curve γ) α) :=
    hF1.unique hF1'
  -- ## and it is non-zero
  have hne : symmCLM (deriv (curve γ) α) ≠ 0 := by
    intro h
    refine curve_deriv_ne_zero γ hγ α (symmCLM_injective ?_)
    rw [h, map_zero]
  rw [hEq]
  exact hne

end

end Work.Drive
