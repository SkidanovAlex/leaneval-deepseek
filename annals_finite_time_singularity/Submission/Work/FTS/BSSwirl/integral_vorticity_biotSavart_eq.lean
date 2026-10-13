import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.BSSwirl.integral_vorticity_eq
import Submission.Work.FTS.BSSwirl.vorticity_vorticity_eq
import Submission.Work.FTS.BSSwirl.weakDivFree_newtonPotential
import Submission.Work.FTS.BSSwirl.biotSavart_eq_vorticity_newtonPotential
import Submission.Work.FTS.BSSwirl.contDiff_vorticity_and_support
import Submission.Work.FTS.BSSwirl.contDiff_div_and_support
import Submission.Work.FTS.BSSwirl.integral_newtonPotential_laplacian
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity MeasureTheory Set

namespace Work.FTS.BSSwirl

/-!
# The weak form of the Biot–Savart law for a compactly supported Hölder vorticity

This module proves

`∫ x, ⟪∇×(BS ω) x, Ψ x⟫ = ∫ x, ⟪ω x, Ψ x⟫`

for every bounded, a.e. strongly measurable, compactly supported `α`-Hölder vorticity `ω`
(`α > 0`) whose Newtonian potential `A ω` is `C¹` with the expected derivative, and every smooth
compactly supported test field `Ψ`.  The weakly divergence-free hypothesis `WeakDivFree ω` is the
only structural input.  This is step 3 of the route in `NOTES.md` of the `BSSwirl` area.

The chain of identities is

```
∫ ⟪∇×(BS ω), Ψ⟫ = ∫ ⟪BS ω, ∇×Ψ⟫            (curl is self-adjoint, BS ω ∈ C¹)
                 = ∫ ⟪∇×(A ω), ∇×Ψ⟫        (BS ω = ∇×(A ω))
                 = ∫ ⟪A ω, ∇×(∇×Ψ)⟫        (curl is self-adjoint, A ω ∈ C¹)
                 = ∫ ⟪A ω, ∇(div Ψ)⟫ - ∫ ⟪A ω, ΔΨ⟫    (∇×(∇×Ψ) = ∇(div Ψ) - ΔΨ)
                 = 0 - (-∫ ⟪ω, Ψ⟫)          (div (A ω) = 0 weakly; ∫⟪A ω, ΔΨ⟫ = -∫⟪ω, Ψ⟫)
                 = ∫ ⟪ω, Ψ⟫.
```

The two auxiliary lemmas `ivbs_integrable_inner_cs` and `ivbs_integrable_inner_grad_cs` supply the
integrability needed to split the integral of the difference (the Newtonian potential is *not*
integrable, but it is continuous and the second factor is compactly supported).
-/

/-- **The inner product of a continuous field with a continuous compactly supported one is
integrable.**  (A local copy of the glue lemma of `Work.FTS.BSSwirl.Main`, under a distinct name so
that both modules may be imported together.) -/
theorem ivbs_integrable_inner_cs {V Ψ : R3 → R3} (hV : Continuous V)
    (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    Integrable (fun x => inner ℝ (V x) (Ψ x)) := by
  refine (hV.inner hΨ).integrable_of_hasCompactSupport ?_
  refine hΨc.isCompact.of_isClosed_subset (isClosed_tsupport _) (closure_mono ?_)
  intro y hy
  contrapose! hy
  rw [Function.mem_support, not_not] at hy ⊢
  rw [hy, inner_zero_right]

/-- **`⟪A, ∇k⟫` is integrable when `k` is smooth with compact support and `A` is continuous.**

The point is that `⟪A x, ∇k x⟫ = (fderiv ℝ k x) (A x)`: `fderiv ℝ k` is continuous with compact
support (`ContDiff.continuous_fderiv`, `HasCompactSupport.fderiv`), so `x ↦ (fderiv ℝ k x) (A x)` is
continuous with compact support, hence integrable.  This is the form needed for the Newtonian
potential `A ω`, which is continuous but not integrable. -/
theorem ivbs_integrable_inner_grad_cs {k : R3 → ℝ} {A : R3 → R3}
    (hk : ∀ n : ℕ, ContDiff ℝ n k) (hkcs : HasCompactSupport k) (hA : Continuous A) :
    Integrable (fun x => inner ℝ (A x) (gradient k x)) := by
  have hfderiv : Continuous (fderiv ℝ k) := (hk 1).continuous_fderiv one_ne_zero
  have hcont : Continuous (fun x => fderiv ℝ k x (A x)) := hfderiv.clm_apply hA
  have hcs : HasCompactSupport (fun x => fderiv ℝ k x (A x)) := by
    refine (hkcs.fderiv ℝ).mono' ?_
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxt
    apply hx
    rw [image_eq_zero_of_notMem_tsupport hxt, zero_apply]
  have hint : Integrable (fun x => fderiv ℝ k x (A x)) :=
    hcont.integrable_of_hasCompactSupport hcs
  refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [inner_gradient_right]

theorem integral_vorticity_biotSavart_eq {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    {R M α C : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hα : 0 < α) (hC : 0 ≤ C)
    (hbdd : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hholder : ∀ a b : Work.FTS.BSSwirl.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ α)
    (hdiv : Work.FTS.BSSwirl.WeakDivFree ω)
    (hdA : ∀ x, HasFDerivAt (Work.FTS.BSSwirl.newtonPotential ω)
      (Work.FTS.BSSwirl.potDeriv ω x) x)
    (hCA : ContDiff ℝ 1 (Work.FTS.BSSwirl.newtonPotential ω)) :
    ∀ Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3, (∀ n : ℕ, ContDiff ℝ n Ψ) →
      HasCompactSupport Ψ →
      ∫ x, inner ℝ (FiniteTimeSingularity.vorticity (Work.LWP.biotSavart ω) x) (Ψ x)
        = ∫ x, inner ℝ (ω x) (Ψ x) := by
  intro Ψ hΨ hΨc
  -- the Biot–Savart field is the curl of the vector Newtonian potential
  have hBS : ∀ x : R3, Work.LWP.biotSavart ω x = vorticity (newtonPotential ω) x :=
    fun x => biotSavart_eq_vorticity_newtonPotential hM hbdd hsupp hmeas hdA x
  -- the Biot–Savart field is `C¹` (Calderón–Zygmund chapter)
  have hBScd : ContDiff ℝ 1 (Work.LWP.biotSavart ω) :=
    Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one hR hM hα hbdd hsupp hmeas hholder
  -- the curl and the divergence of a test field are smooth and compactly supported
  obtain ⟨hvcd, hvcs⟩ := contDiff_vorticity_and_support hΨ hΨc
  obtain ⟨hdcd, hdcs⟩ := contDiff_div_and_support hΨ hΨc
  have hAcont : Continuous (newtonPotential ω) := hCA.continuous
  -- the two integrability facts needed to split the integral of a difference
  have hint1 : Integrable (fun x => inner ℝ (newtonPotential ω x) (gradient (div Ψ) x)) :=
    ivbs_integrable_inner_grad_cs hdcd hdcs hAcont
  have hint2 : Integrable (fun x => inner ℝ (newtonPotential ω x) (Laplacian.laplacian Ψ x)) :=
    ivbs_integrable_inner_cs hAcont (continuous_laplacian_vec (hΨ 2))
      (hasCompactSupport_laplacian_vec hΨc)
  -- the chain of identities
  have hstep1 : ∫ x, inner ℝ (vorticity (Work.LWP.biotSavart ω) x) (Ψ x)
      = ∫ x, inner ℝ (Work.LWP.biotSavart ω x) (vorticity Ψ x) :=
    integral_vorticity_eq hBScd hΨ hΨc
  have hstep2 : ∫ x, inner ℝ (Work.LWP.biotSavart ω x) (vorticity Ψ x)
      = ∫ x, inner ℝ (vorticity (newtonPotential ω) x) (vorticity Ψ x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hBS x])
  have hstep3 : ∫ x, inner ℝ (vorticity (newtonPotential ω) x) (vorticity Ψ x)
      = ∫ x, inner ℝ (newtonPotential ω x) (vorticity (vorticity Ψ) x) :=
    integral_vorticity_eq hCA hvcd hvcs
  have hstep4 : ∫ x, inner ℝ (newtonPotential ω x) (vorticity (vorticity Ψ) x)
      = ∫ x, inner ℝ (newtonPotential ω x) (gradient (div Ψ) x - Laplacian.laplacian Ψ x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [vorticity_vorticity_eq hΨ x])
  have hstep5 : ∫ x, inner ℝ (newtonPotential ω x) (gradient (div Ψ) x - Laplacian.laplacian Ψ x)
      = (∫ x, inner ℝ (newtonPotential ω x) (gradient (div Ψ) x))
        - (∫ x, inner ℝ (newtonPotential ω x) (Laplacian.laplacian Ψ x)) := by
    rw [← integral_sub hint1 hint2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => inner_sub_right _ _ _)
  -- `div (A ω) = 0` weakly, tested against `div Ψ`
  have hzero : ∫ x, inner ℝ (newtonPotential ω x) (gradient (div Ψ) x) = 0 :=
    (weakDivFree_newtonPotential (le_of_lt hR) hM hbdd hsupp hmeas hdiv) (div Ψ) hdcd hdcs
  -- `∫ ⟪A ω, ΔΨ⟫ = -∫ ⟪ω, Ψ⟫`
  have hlap : ∫ x, inner ℝ (newtonPotential ω x) (Laplacian.laplacian Ψ x)
      = - ∫ x, inner ℝ (ω x) (Ψ x) :=
    integral_newtonPotential_laplacian (le_of_lt hR) hM hbdd hsupp hmeas hΨ hΨc
  calc ∫ x, inner ℝ (vorticity (Work.LWP.biotSavart ω) x) (Ψ x)
      = ∫ x, inner ℝ (Work.LWP.biotSavart ω x) (vorticity Ψ x) := hstep1
    _ = ∫ x, inner ℝ (vorticity (newtonPotential ω) x) (vorticity Ψ x) := hstep2
    _ = ∫ x, inner ℝ (newtonPotential ω x) (vorticity (vorticity Ψ) x) := hstep3
    _ = ∫ x, inner ℝ (newtonPotential ω x) (gradient (div Ψ) x - Laplacian.laplacian Ψ x) := hstep4
    _ = (∫ x, inner ℝ (newtonPotential ω x) (gradient (div Ψ) x))
        - (∫ x, inner ℝ (newtonPotential ω x) (Laplacian.laplacian Ψ x)) := hstep5
    _ = 0 - (- ∫ x, inner ℝ (ω x) (Ψ x)) := by rw [hzero, hlap]
    _ = ∫ x, inner ℝ (ω x) (Ψ x) := by ring

end Work.FTS.BSSwirl
