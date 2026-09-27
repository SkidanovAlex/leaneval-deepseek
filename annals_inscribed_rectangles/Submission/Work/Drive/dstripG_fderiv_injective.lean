import Mathlib
import Submission.Work.Drive.stripData

/-!
# The derivative of the strip map `dstripG` at `τ = 0` is injective

`dstripG M W p = (M (e^{i p.1}, p.2), dstripA M W p.1 p.2)` is the map whose injectivity on a thin
strip `-c ≤ τ ≤ 0` is the content of `Work.Drive.descent_strip_injective`.  This file provides the
*infinitesimal* input of that statement: at a point `(α, 0)` of the boundary `τ = 0` of the strip,
the derivative of `dstripG` is injective as soon as

* the `α`-derivative of the band datum `M` along the unit circle is non-zero
  (`hv`, i.e. `p ↦ M (e^{iα}, 0)` is immersive at `α`), and
* the *transversal* datum `W` does not vanish at the boundary point (`hW`).

The reason is the identity

`dstripA M W α τ = ‖M (e^{iα}, τ)‖² + τ ‖W (e^{iα}, τ)‖²`,

whose `τ`-derivative at `τ = 0` contributes exactly `‖W (e^{iα}, 0)‖² > 0` — the *only* term that
survives from the second summand, because the factor `τ` vanishes and the two `normSq`-terms pair
with the `τ`-derivative of the first summand through the real part of a complex product.  So if `v`
is in the kernel of the derivative and `v₂ ≠ 0`, the `α`-component of the derivative would force
`‖W‖² = 0`; hence `v₂ = 0`, and then the first component (`hv`) forces `v₁ = 0`.

This is the standard "the boundary of the strip is transversally crossed" computation; it is used to
separate the strip points of a band datum.
-/

namespace Work.Drive

open scoped ContDiff

noncomputable section

/-- The first component of the strip map: `p ↦ M (e^{i p.1}, p.2)` (with `dstripU p.1 = e^{i p.1}`). -/
private def stripM (M : ℂ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun p => M (dstripU p.1, p.2)

/-- The transversal datum of the strip map: `p ↦ W (e^{i p.1}, p.2)`. -/
private def stripN (W : ℂ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun p => W (dstripU p.1, p.2)

private lemma contDiff_strip {V : ℂ × ℝ → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => V (dstripU p.1, p.2)) :=
  h.comp ((contDiff_dstripU.comp contDiff_fst).prodMk contDiff_snd)

theorem dstripG_fderiv_injective {M W : ℂ × ℝ → ℂ}
    (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    {α : ℝ}
    (hv : fderiv ℝ (fun p : ℝ × ℝ => M (dstripU p.1, p.2)) (α, 0) (1, 0) ≠ 0)
    (hW : W (dstripU α, 0) ≠ 0) :
    Function.Injective (fderiv ℝ (dstripG M W) (α, 0)) := by
  -- `dstripG` is the pair of `stripM M` and `normSq (stripM M) + p.2 * normSq (stripN W)`
  show Function.Injective (fderiv ℝ (fun p : ℝ × ℝ =>
    (stripM M p, Complex.normSq (stripM M p) + p.2 * Complex.normSq (stripN W p))) (α, 0))
  have hFsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (stripM M) := contDiff_strip hMsm
  have hNsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (stripN W) := contDiff_strip hWsm
  have hF : HasFDerivAt (stripM M) (fderiv ℝ (stripM M) (α, 0)) (α, 0) :=
    (hFsm.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hN : HasFDerivAt (stripN W) (fderiv ℝ (stripN W) (α, 0)) (α, 0) :=
    (hNsm.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hv' : fderiv ℝ (stripM M) (α, 0) (1, 0) ≠ 0 := hv
  have hWne : Complex.normSq (stripN W (α, 0)) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hW)
  have hNF : HasFDerivAt (fun p : ℝ × ℝ => Complex.normSq (stripM M p))
      (fderiv ℝ (fun p : ℝ × ℝ => Complex.normSq (stripM M p)) (α, 0)) (α, 0) := by
    have h := hF.norm_sq
    have hconv : (fun p : ℝ × ℝ => Complex.normSq (stripM M p)) =
        fun p : ℝ × ℝ => ‖stripM M p‖ ^ 2 := by
      funext p; exact Complex.normSq_eq_norm_sq _
    rw [hconv, h.fderiv]
    exact h
  have hNW : HasFDerivAt (fun p : ℝ × ℝ => Complex.normSq (stripN W p))
      (fderiv ℝ (fun p : ℝ × ℝ => Complex.normSq (stripN W p)) (α, 0)) (α, 0) := by
    have h := hN.norm_sq
    have hconv : (fun p : ℝ × ℝ => Complex.normSq (stripN W p)) =
        fun p : ℝ × ℝ => ‖stripN W p‖ ^ 2 := by
      funext p; exact Complex.normSq_eq_norm_sq _
    rw [hconv, h.fderiv]
    exact h
  -- the `p.2 * normSq (stripN W p)` summand: at `p.2 = 0` only the `normSq` survives
  have hprod : HasFDerivAt (fun p : ℝ × ℝ => p.2 * Complex.normSq (stripN W p))
      (Complex.normSq (stripN W (α, 0)) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (α, 0) := by
    have h := hasFDerivAt_snd.mul hNW
    have hder : ((α, 0) : ℝ × ℝ).2 •
          (fderiv ℝ (fun p : ℝ × ℝ => Complex.normSq (stripN W p)) (α, 0)) +
        Complex.normSq (stripN W (α, 0)) • (ContinuousLinearMap.snd ℝ ℝ ℝ)
        = Complex.normSq (stripN W (α, 0)) • (ContinuousLinearMap.snd ℝ ℝ ℝ) := by simp
    rw [hder] at h
    exact h
  have hA : HasFDerivAt
      (fun p : ℝ × ℝ => Complex.normSq (stripM M p) + p.2 * Complex.normSq (stripN W p))
      ((fderiv ℝ (fun p : ℝ × ℝ => Complex.normSq (stripM M p)) (α, 0)) +
        Complex.normSq (stripN W (α, 0)) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (α, 0) :=
    hNF.add hprod
  have hG : HasFDerivAt
      (fun p : ℝ × ℝ =>
        (stripM M p, Complex.normSq (stripM M p) + p.2 * Complex.normSq (stripN W p)))
      ((fderiv ℝ (stripM M) (α, 0)).prod
        ((fderiv ℝ (fun p : ℝ × ℝ => Complex.normSq (stripM M p)) (α, 0)) +
          Complex.normSq (stripN W (α, 0)) • (ContinuousLinearMap.snd ℝ ℝ ℝ))) (α, 0) :=
    hF.prodMk hA
  have hL := hG.fderiv
  -- ## the kernel of the derivative is trivial
  have hker : ∀ v : ℝ × ℝ,
      fderiv ℝ (fun p : ℝ × ℝ =>
        (stripM M p, Complex.normSq (stripM M p) + p.2 * Complex.normSq (stripN W p))) (α, 0) v
        = 0 → v = 0 := by
    intro v hv0
    rw [hL, ContinuousLinearMap.prod_apply] at hv0
    have h1 : fderiv ℝ (stripM M) (α, 0) v = 0 := by
      simpa using congrArg Prod.fst hv0
    have h2 : ((fderiv ℝ (fun p : ℝ × ℝ => Complex.normSq (stripM M p)) (α, 0)) +
        Complex.normSq (stripN W (α, 0)) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) v = 0 := by
      simpa using congrArg Prod.snd hv0
    -- the derivative of the second component, with the `τ`-derivative of the first one killed
    have hD1v : fderiv ℝ (fun p : ℝ × ℝ => Complex.normSq (stripM M p)) (α, 0) v = 0 := by
      have h := hF.norm_sq
      have hconv : (fun p : ℝ × ℝ => Complex.normSq (stripM M p)) =
          fun p : ℝ × ℝ => ‖stripM M p‖ ^ 2 := by
        funext p; exact Complex.normSq_eq_norm_sq _
      rw [hconv, h.fderiv]
      simp only [smul_apply, ContinuousLinearMap.comp_apply, h1, map_zero, smul_zero]
    have hD2v : Complex.normSq (stripN W (α, 0)) * v.2 = 0 := by
      have h3 : (fderiv ℝ (fun p : ℝ × ℝ => Complex.normSq (stripM M p)) (α, 0)) v +
          Complex.normSq (stripN W (α, 0)) * v.2 = 0 := by
        simpa [add_apply, smul_apply] using h2
      rw [hD1v, zero_add] at h3
      exact h3
    have hv2 : v.2 = 0 := (mul_eq_zero.mp hD2v).resolve_left hWne
    have hv1 : v.1 = 0 := by
      have hsm : v = v.1 • (1, 0) := by ext <;> simp [hv2]
      have h3 : v.1 • (fderiv ℝ (stripM M) (α, 0) (1, 0)) = 0 := by
        rw [← map_smul, ← hsm]
        exact h1
      exact (smul_eq_zero.mp h3).resolve_right hv'
    exact Prod.ext hv1 hv2
  intro v w hvw
  have hz : v - w = 0 := hker (v - w) (by rw [map_sub, hvw, sub_self])
  exact sub_eq_zero.mp hz

end

end Work.Drive
