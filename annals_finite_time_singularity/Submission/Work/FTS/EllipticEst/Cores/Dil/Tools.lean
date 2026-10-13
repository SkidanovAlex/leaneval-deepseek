/-
Copyright: work module for the Elgindi finite-time singularity project.

# Clean tools for the radial second difference quotient

Three bookkeeping tools used by the `shiftedTwoL2` development, all of them consequences of
results that are available in *buildable* modules (the corresponding lemmas in
`Cores/Repair/DzShift.lean` are stated in a module whose import closure is currently broken):

* `smoothOpen_of_bslOp_eq`: the source `F` of a weak datum is `C^∞` on the open quadrant,
  because it agrees there with `bslOp α Ψ`;
* `HkMem_DzDz`: `ℋ²`-honesty of `f` gives `ℋ⁰`-honesty of `D_z (D_z f)` — the single slot
  `(D_z² f · w/sin(2θ)^{η/2})²` is one of the summands of `HkIntegrand α 2 f`, so the pointwise
  domination is immediate (`HkIntegrand_DzDz_le`);
* the two slice-integrability lemmas: for a `C^∞`-on-`Q0` function whose level-`0` weighted
  integrand is honest, and for a weak datum `Ψ`, the angular slices are `L¹` against
  `sin θ cos²θ` (the latter from `remov.Psi_slice_sinCos2_integrable`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.remov.Psi_slice_sinCos2_integrable
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.Cores.Dil.HkSqLimit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The source of a weak datum is `C^∞` on the open quadrant -/

theorem smoothOpen_of_bslOp_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ) heq

/-- `z² · Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothOpen_zsq_mul {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Ψ z θ) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall] at h ⊢
  intro n
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 ^ 2) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_fst (𝕜 := ℝ)).pow 2
  have h3 := h1.mul (h n)
  have hfun : Function.uncurry (fun z θ => z ^ 2 * Ψ z θ)
      = fun p : ℝ × ℝ => p.1 ^ 2 * Ψ p.1 p.2 := by
    funext p
    rfl
  rwa [hfun]

/-! ## `ℋ⁰`-honesty of `D_z (D_z f)` -/

/-- The single slot of `HkIntegrand α 0 (D_z (D_z f))` is a slot of `HkIntegrand α 2 f`. -/
theorem HkIntegrand_DzDz_le (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz f)) z θ
      ≤ Work.Spaces.HkIntegrand α 2 f z θ := by
  rw [HkIntegrand_zero_apply]
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
    (Work.Spaces.sq_le_HkIntegrand_z α 2 f z θ 2 (by norm_num))

theorem HkMem_DzDz {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 2 f) :
    Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.Dz f)) := by
  refine Work.FTS.LocData.HkMem_of_majorant α 0
    (f := Work.Spaces.Dz (Work.Spaces.Dz f))
    (M := fun z θ => Work.Spaces.HkIntegrand α 2 f z θ) ?_ ?_ ?_ ?_
  · exact (hf.Dz.Dz).continuousOn_HkIntegrand α 0
  · intro z hz
    exact hmem.1 z hz
  · exact hmem.2
  · intro z hz θ hθ
    exact HkIntegrand_DzDz_le α f z θ

/-! ## Slice integrability against `sin θ cos²θ` -/

/-- A function whose level-`0` weighted integrand is honest has its slices integrable against
`sin θ cos²θ` (pointwise absorption `|a sinθcos²θ| ≤ a² w² sin(2θ)^{-η} + 1`). -/
theorem integrableOn_sinCos2_of_HkMem {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 0 f)
    {y : ℝ} (hy : 0 < y) :
    MeasureTheory.IntegrableOn (fun θ => f y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  have hsq : MeasureTheory.IntegrableOn
      (fun θ => (f y θ * (Work.Spaces.w y / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ := by
    simpa only [HkIntegrand_zero_apply] using hmem.1 y (le_of_lt hy)
  have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine hf.continuousOn.mul ?_
    have hc : Continuous fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2 := by
      show Continuous fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2
      fun_prop
    exact hc.continuousOn
  refine MeasureTheory.Integrable.mono' (hsq.add hone)
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hy) ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs]
  exact Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted hy ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

/-- The `Ψ`-side: the slices of a weak datum are integrable against `sin θ cos²θ`. -/
theorem integrableOn_sinCos2_of_weak {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {y : ℝ} (hy : 0 < y) :
    MeasureTheory.IntegrableOn (fun θ => Ψ y θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hsinCos2_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.Elliptic.sinCos2 θ := by
    intro θ hθ
    rw [Work.Elliptic.sinCos2]
    have h1 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    nlinarith [sq_nonneg (Real.cos θ)]
  have hcontσ : Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
    simp only [Work.Elliptic.sinCos2]; fun_prop
  have h1 : MeasureTheory.Integrable (fun θ : ℝ => |Ψ y θ| * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (Work.FTS.EllipticEst.remov.Psi_slice_sinCos2_integrable hk h y hy).integrable
  refine h1.mono' ?_ ?_
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      (hΨ.continuousOn.mul hcontσ.continuousOn) hy
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hsinCos2_nn θ hθ)]

end Work.FTS.EllipticEst.Cores.Dil
