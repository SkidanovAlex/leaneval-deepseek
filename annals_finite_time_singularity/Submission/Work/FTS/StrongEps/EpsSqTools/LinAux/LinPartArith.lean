import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.BSSwirl.integral_newtonPotential_laplacian
import Submission.Work.FTS.BSSwirl.weakDivFree_newtonPotential
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.H2.STEasyDefs
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PressureOn.PoissonAux.kernelGradAux2
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.Regularity.hkIntegrandZfarBound
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.Top.Main
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.HkSqZfar
import Submission.Work.Stability.PzFstarAdd
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.BSSwirl.integral_vorticity_biotSavart_eq =====
section

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
end
-- ===== merged: Submission.Work.FTS.FireFix.Prime.RegPkgClockData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

open Work.FTS.Physical (PhysClock)

/-- **The reciprocal amplitude is Lipschitz on the strip.**  Under the clock fields of `RegPkg'`
(`A` differentiable on `[0,S]` with `|A'| ≤ a₂`, and `A ≥ a₀ > 0`), the map `τ ↦ 1/A(τ)` is
Lipschitz on `[0,S]` with constant `a₂/a₀²`. -/
theorem one_div_A_lipschitz {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    ∃ L : ℝ, ∀ tau ∈ Set.Icc (0 : ℝ) S, ∀ tau' ∈ Set.Icc (0 : ℝ) S,
      |(A tau)⁻¹ - (A tau')⁻¹| ≤ L * |tau - tau'| := by
  obtain ⟨a₀, a₁, ha₀pos, ha⟩ := h.hAb
  obtain ⟨a₂, ha₂⟩ := h.hAd
  have ha₀pos' : 0 < a₀ := ha₀pos
  refine ⟨max (max a₂ 0 / a₀ ^ 2) 0, fun tau htau tau' htau' => ?_⟩
  have hAτ : a₀ ≤ A tau := (ha tau htau).1
  have hAτ' : a₀ ≤ A tau' := (ha tau' htau').1
  have hposτ : 0 < A tau := lt_of_lt_of_le ha₀pos' hAτ
  have hposτ' : 0 < A tau' := lt_of_lt_of_le ha₀pos' hAτ'
  -- Lipschitz bound for `A` on the strip
  have hlip : |A tau - A tau'| ≤ max a₂ 0 * |tau - tau'| := by
    have h2 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := A) (f' := deriv A) (s := Set.Icc (0 : ℝ) S)
      (fun x hx => (h.hAdiff x hx).hasDerivWithinAt)
      (fun x hx => by
        rw [Real.norm_eq_abs]
        exact le_trans (ha₂ x hx) (le_max_left a₂ 0))
      (convex_Icc 0 S) htau htau'
    simpa [Real.norm_eq_abs, abs_sub_comm] using h2
  have hkey : (A tau)⁻¹ - (A tau')⁻¹ = (A tau' - A tau) / (A tau * A tau') := by
    field_simp
  have hden : a₀ * a₀ ≤ A tau * A tau' :=
    mul_le_mul hAτ hAτ' ha₀pos'.le (le_trans ha₀pos'.le hAτ)
  have hdenpos : (0 : ℝ) < A tau * A tau' := mul_pos hposτ hposτ'
  have hnum : |A tau' - A tau| ≤ max a₂ 0 * |tau' - tau| := by
    simpa [abs_sub_comm] using hlip
  rw [hkey, abs_div, abs_of_pos hdenpos]
  have hstep1 : |A tau' - A tau| / (A tau * A tau')
      ≤ (max a₂ 0 * |tau' - tau|) / (A tau * A tau') :=
    div_le_div_of_nonneg_right hnum hdenpos.le
  have hstep2 : (max a₂ 0 * |tau' - tau|) / (A tau * A tau')
      ≤ (max a₂ 0 * |tau' - tau|) / (a₀ * a₀) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (le_max_right a₂ 0) (abs_nonneg _))
    simpa [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < a₀ * a₀) hden
  have hstep3 : (max a₂ 0 * |tau' - tau|) / (a₀ * a₀)
      = max a₂ 0 / a₀ ^ 2 * |tau' - tau| := by
    field_simp
  have hstep4 : max a₂ 0 / a₀ ^ 2 * |tau' - tau| ≤ max (max a₂ 0 / a₀ ^ 2) 0 * |tau' - tau| :=
    mul_le_mul_of_nonneg_right (le_max_left (max a₂ 0 / a₀ ^ 2) 0) (abs_nonneg _)
  have habs : |tau' - tau| = |tau - tau'| := abs_sub_comm tau' tau
  calc |A tau' - A tau| / (A tau * A tau')
      ≤ (max a₂ 0 * |tau' - tau|) / (A tau * A tau') := hstep1
    _ ≤ (max a₂ 0 * |tau' - tau|) / (a₀ * a₀) := hstep2
    _ = max a₂ 0 / a₀ ^ 2 * |tau' - tau| := hstep3
    _ ≤ max (max a₂ 0 / a₀ ^ 2) 0 * |tau' - tau| := hstep4
    _ = max (max a₂ 0 / a₀ ^ 2) 0 * |tau - tau'| := by rw [← habs]

/-- **A differentiable function with bounded derivative on `[0,T]` is Lipschitz** (the mean value
inequality, stated on the closed interval). -/
theorem lipschitz_of_hasDerivAt_bounded {T L : ℝ} {tau d : ℝ → ℝ} (hL : 0 ≤ L)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt tau (d t) t)
    (hbdd : ∀ t ∈ Set.Icc (0 : ℝ) T, |d t| ≤ L) :
    ∃ L' : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      |tau t - tau t'| ≤ L' * |t - t'| := by
  refine ⟨L, fun t ht t' ht' => ?_⟩
  have h2 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := tau) (f' := d) (s := Set.Icc (0 : ℝ) T)
    (fun x hx => (hderiv x hx).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hbdd x hx)
    (convex_Icc 0 T) ht ht'
  simpa [Real.norm_eq_abs, abs_sub_comm] using h2

/-- **The clock data of the reconstruction, from `RegPkg'`.**  If `τ` maps `[0,T]` into the
fake-time strip `[0,S]` and is Lipschitz, and `d t = (A (τ t))⁻¹`, then `d` is bounded on `[0,T]`
and `α`-Hölder there (with `α ` the `RegPkg'` exponent, `0 < α ≤ 1/3`). -/
theorem regPkg_clock_data {α S T : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hreg : Work.FTS.RegPkgGal.RegPkg' α S A B g) {tau d : ℝ → ℝ}
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) T, tau t ∈ Set.Icc (0 : ℝ) S)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) T, d t = (A (tau t))⁻¹)
    (hlip : ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      |tau t - tau t'| ≤ L * |t - t'|) :
    (∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, |d t| ≤ L) ∧
      (∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
        |d t - d t'| ≤ L * |t - t'| ^ α) := by
  obtain ⟨a₀, a₁, ha₀pos, ha⟩ := hreg.hAb
  obtain ⟨LA₀, hLA₀⟩ := one_div_A_lipschitz hreg
  obtain ⟨Lτ₀, hLτ₀⟩ := hlip
  have hαpos : 0 < α := hreg.hα
  have hαle : α ≤ 1 := by linarith [hreg.hα13]
  -- nonnegative versions of the constants
  have hLA : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |(A τ)⁻¹ - (A τ')⁻¹| ≤ max LA₀ 0 * |τ - τ'| := fun τ hτ τ' hτ' =>
    le_trans (hLA₀ τ hτ τ' hτ') (mul_le_mul_of_nonneg_right (le_max_left LA₀ 0) (abs_nonneg _))
  have hLτ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      |tau t - tau t'| ≤ max Lτ₀ 0 * |t - t'| := fun t ht t' ht' =>
    le_trans (hLτ₀ t ht t' ht') (mul_le_mul_of_nonneg_right (le_max_left Lτ₀ 0) (abs_nonneg _))
  have hLAnn : 0 ≤ max LA₀ 0 := le_max_right LA₀ 0
  have hLτnn : 0 ≤ max Lτ₀ 0 := le_max_right Lτ₀ 0
  -- boundedness of `d`
  have hbdd : ∀ t ∈ Set.Icc (0 : ℝ) T, |d t| ≤ max (a₀⁻¹) 0 := by
    intro t ht
    have hApos : 0 < A (tau t) := lt_of_lt_of_le ha₀pos (ha (tau t) (hmem t ht)).1
    rw [hd t ht, abs_of_pos (inv_pos.mpr hApos)]
    exact le_trans (by simpa [one_div] using
      one_div_le_one_div_of_le ha₀pos (ha (tau t) (hmem t ht)).1) (le_max_left (a₀⁻¹) 0)
  refine ⟨⟨max (a₀⁻¹) 0, hbdd⟩, ?_⟩
  -- Hölder bound for `d`
  refine ⟨max (max LA₀ 0 * max Lτ₀ 0) (2 * max (a₀⁻¹) 0), fun t ht t' ht' => ?_⟩
  rcases le_total |t - t'| 1 with hsmall | hbig
  · have h1 : |d t - d t'| ≤ max LA₀ 0 * |tau t - tau t'| := by
      rw [hd t ht, hd t' ht']
      exact hLA (tau t) (hmem t ht) (tau t') (hmem t' ht')
    have h3 : |t - t'| ≤ |t - t'| ^ α := Real.self_le_rpow_of_le_one (abs_nonneg _) hsmall hαle
    calc |d t - d t'| ≤ max LA₀ 0 * |tau t - tau t'| := h1
      _ ≤ max LA₀ 0 * (max Lτ₀ 0 * |t - t'|) := mul_le_mul_of_nonneg_left (hLτ t ht t' ht') hLAnn
      _ = (max LA₀ 0 * max Lτ₀ 0) * |t - t'| := by ring
      _ ≤ (max LA₀ 0 * max Lτ₀ 0) * |t - t'| ^ α :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hLAnn hLτnn)
      _ ≤ max (max LA₀ 0 * max Lτ₀ 0) (2 * max (a₀⁻¹) 0) * |t - t'| ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
  · have hone : (1 : ℝ) ≤ |t - t'| ^ α := Real.one_le_rpow hbig hαpos.le
    have h1 : |d t - d t'| ≤ 2 * max (a₀⁻¹) 0 := by
      have h2 := hbdd t ht
      have h3 := hbdd t' ht'
      calc |d t - d t'| ≤ |d t| + |d t'| :=
            abs_sub_le_iff.mpr ⟨by linarith [le_abs_self (d t), neg_le_abs (d t')],
              by linarith [le_abs_self (d t'), neg_le_abs (d t)]⟩
        _ ≤ 2 * max (a₀⁻¹) 0 := by linarith
    calc |d t - d t'| ≤ 2 * max (a₀⁻¹) 0 := h1
      _ = (2 * max (a₀⁻¹) 0) * 1 := by ring
      _ ≤ (2 * max (a₀⁻¹) 0) * |t - t'| ^ α :=
          mul_le_mul_of_nonneg_left hone (by positivity)
      _ ≤ max (max LA₀ 0 * max Lτ₀ 0) (2 * max (a₀⁻¹) 0) * |t - t'| ^ α :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _)

end Work.FTS.FireFix.Prime
end
-- ===== merged: Submission.Work.FTS.Regularity.regPkg_inhabited =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace Work.FTS.Regularity

/-! ## The `Jet` interface: closure properties -/

theorem Jet.neg {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Jet α S N h) :
    Jet α S N (fun z θ τ => -h z θ τ) := by
  refine ⟨H.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    simpa using H.2.1 z θ τ hz hθ hτ
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := H.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h2 : |(-h z θ τ) - (-h z' θ' τ')| = |h z θ τ - h z' θ' τ'| := by
      rw [show (-h z θ τ) - (-h z' θ' τ') = -(h z θ τ - h z' θ' τ') by ring, abs_neg]
    rw [h2]
    exact h1

theorem Jet.add {α S N₁ N₂ : ℝ} {a b : ℝ → ℝ → ℝ → ℝ} (Ha : Jet α S N₁ a)
    (Hb : Jet α S N₂ b) :
    Jet α S (N₁ + N₂) (fun z θ τ => a z θ τ + b z θ τ) := by
  refine ⟨add_nonneg Ha.1 Hb.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    calc |a z θ τ + b z θ τ| ≤ |a z θ τ| + |b z θ τ| := abs_add_le _ _
      _ ≤ N₁ + N₂ := add_le_add (Ha.2.1 z θ τ hz hθ hτ) (Hb.2.1 z θ τ hz hθ hτ)
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := Ha.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h2 := Hb.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h3 : a z θ τ + b z θ τ - (a z' θ' τ' + b z' θ' τ')
        = (a z θ τ - a z' θ' τ') + (b z θ τ - b z' θ' τ') := by ring
    rw [h3]
    calc |(a z θ τ - a z' θ' τ') + (b z θ τ - b z' θ' τ')|
        ≤ |a z θ τ - a z' θ' τ'| + |b z θ τ - b z' θ' τ'| := abs_add_le _ _
      _ ≤ N₁ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α
            + N₂ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := add_le_add h1 h2
      _ = (N₁ + N₂) * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by ring

theorem Jet.mul {α S N₁ N₂ : ℝ} {a b : ℝ → ℝ → ℝ → ℝ} (Ha : Jet α S N₁ a)
    (Hb : Jet α S N₂ b) :
    Jet α S (2 * N₁ * N₂) (fun z θ τ => a z θ τ * b z θ τ) := by
  have hN : 0 ≤ 2 * N₁ * N₂ := by nlinarith [Ha.1, Hb.1]
  refine ⟨hN, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    have h1 := Ha.2.1 z θ τ hz hθ hτ
    have h2 := Hb.2.1 z θ τ hz hθ hτ
    calc |a z θ τ * b z θ τ| = |a z θ τ| * |b z θ τ| := abs_mul _ _
      _ ≤ N₁ * N₂ := mul_le_mul h1 h2 (abs_nonneg _) Ha.1
      _ ≤ 2 * N₁ * N₂ := by nlinarith [Ha.1, Hb.1]
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := Ha.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h2 := Hb.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have hb1 := Ha.2.1 z θ τ hz hθ hτ
    have hb2 := Hb.2.1 z' θ' τ' hz' hθ' hτ'
    have hd : |a z θ τ * b z θ τ - a z' θ' τ' * b z' θ' τ'|
        ≤ |a z θ τ| * |b z θ τ - b z' θ' τ'| + |b z' θ' τ'| * |a z θ τ - a z' θ' τ'| := by
      rw [show a z θ τ * b z θ τ - a z' θ' τ' * b z' θ' τ'
          = a z θ τ * (b z θ τ - b z' θ' τ') + b z' θ' τ' * (a z θ τ - a z' θ' τ') by ring]
      refine le_trans (abs_add_le _ _) (le_of_eq ?_)
      rw [abs_mul, abs_mul]
    refine le_trans hd ?_
    have e1 : |a z θ τ| * |b z θ τ - b z' θ' τ'|
        ≤ N₁ * (N₂ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α) :=
      mul_le_mul hb1 h2 (abs_nonneg _) Ha.1
    have e2 : |b z' θ' τ'| * |a z θ τ - a z' θ' τ'|
        ≤ N₂ * (N₁ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α) :=
      mul_le_mul hb2 h1 (abs_nonneg _) Hb.1
    calc |a z θ τ| * |b z θ τ - b z' θ' τ'| + |b z' θ' τ'| * |a z θ τ - a z' θ' τ'|
        ≤ N₁ * (N₂ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α)
          + N₂ * (N₁ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α) := add_le_add e1 e2
      _ = 2 * N₁ * N₂ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by ring

theorem Jet.congr {α S N : ℝ} {a b : ℝ → ℝ → ℝ → ℝ} (Ha : Jet α S N a)
    (h : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → a z θ τ = b z θ τ) :
    Jet α S N b := by
  refine ⟨Ha.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    rw [← h z θ τ hz hθ hτ]
    exact Ha.2.1 z θ τ hz hθ hτ
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    rw [← h z θ τ hz hθ hτ, ← h z' θ' τ' hz' hθ' hτ']
    exact Ha.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'

theorem Jet.of_bounded_holder {α S N : ℝ} {h : ℝ → ℝ → ℝ} (hN : 0 ≤ N) (hα0 : 0 ≤ α)
    (hb : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |h z θ| ≤ N)
    (hh : ∀ z z' θ θ' : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |h z θ - h z' θ'| ≤ N * (|z - z'| + |θ - θ'|) ^ α) :
    Jet α S N (fun z θ _ => h z θ) := by
  refine ⟨hN, fun z θ τ hz hθ hτ => hb z θ hz hθ, ?_⟩
  intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
  refine le_trans (hh z z' θ θ' hz hz' hθ hθ') ?_
  refine mul_le_mul_of_nonneg_left ?_ hN
  refine Real.rpow_le_rpow (by positivity) ?_ hα0
  have h1 : 0 ≤ |θ - θ'| := abs_nonneg _
  have h2 : 0 ≤ |τ - τ'| := abs_nonneg _
  linarith

/-- For `0 ≤ α ≤ 1` and `0 ≤ a ≤ 1`, `0 ≤ b`: `a ≤ (a+b)^α`. -/
theorem le_rpow_add {α a b : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) : a ≤ (a + b) ^ α := by
  rcases eq_or_lt_of_le ha0 with ha | ha
  · rw [← ha]
    exact Real.rpow_nonneg (show (0 : ℝ) ≤ 0 + b by linarith) α
  · rcases le_total (a + b) 1 with h | h
    · have hpos : 0 < a + b := lt_of_lt_of_le ha (le_add_of_nonneg_right hb0)
      have hle := Real.rpow_le_rpow_of_exponent_ge hpos h hα1
      rw [Real.rpow_one] at hle
      linarith
    · have hle := Real.one_le_rpow h hα0
      linarith


/-! ## Two calculus auxiliaries -/



/-! ## The pointwise `ℋ⁴`-integrand bound on the whole domain

The delegated bound `hkIntegrandZfarBound` covers `z ≥ 4`; for `z ∈ [0,4)` the perturbation
vanishes on a neighbourhood of `(z,θ)`, so its `ℋ⁴`-integrand vanishes there
(`HkIntegrand_zfar_eq_zero`, and `HkIntegrand_zero_fst` at `z = 0`). -/


/-! ## The regularity package -/


end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.aestronglyMeasurable_L12dens =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

open MeasureTheory Set Filter
open scoped Real Topology

/-- **A.e. strong measurability of the `L₁₂`-density.**

`Work.FM.L12dens Work.Spaces.K Y s = ∫ θ in Iθ, K θ * Y s θ / s` is the angular
density of the fundamental model.  If the integrand `Y` is jointly a.e.-measurable
on `(0,∞) × Iθ` for the product of the restricted Lebesgue measures — the natural
hypothesis, since the full-plane pair `(s,θ) ↦ (K θ * Y s θ / s)` is *not* measurable
along `s = 0` — then the density is a.e.-strongly-measurable in `s`.

Proof: the multiplier `(s,θ) ↦ K θ / s` is (Borel) measurable on `ℝ × ℝ` (division is a
measurable operation on `ℝ`, with the junk value `0` at `s = 0`), so the product
`(s,θ) ↦ K θ / s * Y s θ` is a.e.-strongly-measurable for the product measure, hence so is
its `θ`-marginal by Fubini's measurability theorem
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`; the two expressions differ
only by the associativity of `*` / `⁻¹`, and `L12dens` is literally the set integral
against `volume.restrict Iθ`. -/
theorem aestronglyMeasurable_L12dens {Y : ℝ → ℝ → ℝ}
    (hY : AEMeasurable (Function.uncurry Y)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    MeasureTheory.AEStronglyMeasurable (fun s => Work.FM.L12dens Work.Spaces.K Y s)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hY' : MeasureTheory.AEStronglyMeasurable (Function.uncurry Y)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hY.aestronglyMeasurable
  have hK : Measurable (fun p : ℝ × ℝ => Work.Spaces.K p.2 / p.1) := by
    have h1 : Measurable fun θ : ℝ => Work.Spaces.K θ := by
      unfold Work.Spaces.K
      fun_prop
    exact (h1.comp measurable_snd).div measurable_fst
  have hprod : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 / p.1 * Y p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hK.aestronglyMeasurable.mul hY'
  have hprod' : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Y p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    convert hprod using 1
    funext p
    ring
  have h := hprod'.integral_prod_right'
  rw [show (fun s => Work.FM.L12dens Work.Spaces.K Y s)
      = fun s => ∫ θ, Work.Spaces.K θ * Y s θ / s
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) from by
    funext s
    rw [Work.FM.L12dens]
    rfl]
  exact h

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Law =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The star law at `Qd` -/

/-- `SmoothOpen Φs` gives joint `C²` on the open quadrant `Qd` (the two sets are the same). -/
theorem contDiffOn_two_of_smoothOpen_Qd {F : Fn} (h : Work.FTS.EllipticEst.SmoothOpen F) :
    ContDiffOn ℝ 2 (Function.uncurry F) Work.Construction.Qd :=
  h.forall 2

/-! ## The clause -/

/-- **The `law` clause of `E5` at a limit slice.**

Given the two laws `IsBslSolPos α (Fstar α) Φs` (`hstar.sol.toPos`) and the perturbation law
`IsBslSolPos α f (E f)` produced by `EllLimOK α E` from the class-`C` approximants `fn n → f`
(with uniform `ℋ⁶`-bound `B` and `C⁴` limit), together with the joint `C²`-smoothness of `Φs` and
of `E f` on the open quadrant, the *sum* is the law of the limit family:
`IsBslSolPos α (Ftau α g τ) (slice (PsiCan Φs E g) τ)`. -/
theorem E5Law {α Cs B τ : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam} {fn : ℕ → Fn} {f : Fn}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hELL : EllLimOK α E)
    (hclass : ∀ n : ℕ, Work.FTS.ClassC.ClassC α (fn n))
    (hB : ∀ n : ℕ, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B)
    (hc4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hslot : ∀ (j i : ℕ), j + i ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (fn n) z θ) Filter.atTop
        (𝓝 (Work.Spaces.mixed j i f z θ)))
    (hsmE : ContDiffOn ℝ 2 (Function.uncurry (E f)) Work.FTS.EllipticEst.Q0)
    (hfs : slice g τ = f) :
    Work.FTS.StrongGlobal.IsBslSolPos α (Work.Construction.Ftau α g τ)
      (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) := by
  obtain ⟨hsolE, _⟩ := hELL fn f B hclass hB hc4 hslot
  have hs : Work.FTS.StrongGlobal.IsBslSolPos α (Work.Construction.Fstar α) Φs :=
    Work.FTS.StrongGlobal.IsBslSol.toPos hstar.sol
  have hsmΦ : ContDiffOn ℝ 2 (Function.uncurry Φs) Work.Construction.Qd :=
    contDiffOn_two_of_smoothOpen_Qd hstar.smooth
  have hsmE' : ContDiffOn ℝ 2 (Function.uncurry (E f)) Work.Construction.Qd := hsmE
  have hadd := Work.FTS_EllLimOK.IsBslSolPos_add hs hsolE hsmΦ hsmE'
  have hF : (fun z θ => Work.Construction.Fstar α z θ + f z θ)
      = Work.Construction.Ftau α g τ := by
    funext z θ
    rw [Work.Construction.Ftau, ← congrFun (congrFun hfs z) θ]
    rfl
  have hΨ : (fun z θ => Φs z θ + E f z θ)
      = Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ := by
    funext z θ
    simp only [Work.FTS.Nonlin.PsiCan, Work.FTS.Galerkin.slice_apply, hfs]
  exact hadd.congr hF hΨ

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLimVolterraP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **E5-4(ii) for the `P₀`-scheme**: the limit of a convergent sequence of `P₀`-scheme solutions
satisfies the limiting equation, provided the right-hand sides converge pointwise, are continuous
in the fake time and uniformly bounded at each point of the quadrant, and the family values
converge at every fake time. -/
theorem EpsLimVolterraP {α T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {ε : ℕ → ℝ} {G : ℕ → Fam} {g : Fam}
    (hT : 0 < T)
    (hsol : ∀ n : ℕ, IsEpsSolP α ρ (ε n) T Φs E g₀ (G n))
    (hcont : ∀ n : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2) (Set.Icc (0 : ℝ) T))
    (hlim : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∀ s ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun n : ℕ => epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2) Filter.atTop
        (nhds (rhsFun α Φs E g s p.1 p.2)))
    (hbdd : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, ∀ n : ℕ,
      ∀ s ∈ Set.Icc (0 : ℝ) T, |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C)
    (hconv0 : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun n : ℕ => G n p.1 p.2 τ) Filter.atTop (nhds (g p.1 p.2 τ)))
    (hcontR : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => rhsFun α Φs E g s p.1 p.2) (Set.Icc (0 : ℝ) T)) :
    ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∀ τ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ => g p.1 p.2 s) (rhsFun α Φs E g τ p.1 p.2)
        (Set.Icc (0 : ℝ) T) τ := by
  intro p hp τ hτ
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hθ : p.2 ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  exact Work.FTS.StrongEps.hasDerivWithinAt_of_tendsto (T := T) hT.le
    (g := fun n s => G n p.1 p.2 s)
    (G := fun s => g p.1 p.2 s)
    (D := fun s => rhsFun α Φs E g s p.1 p.2)
    (dk := fun n s => epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
    (fun n s hs => (hsol n).2 p.1 p.2 s hz hθ hs)
    (fun n => hcont n p hp)
    (hbdd p hp)
    (hcontR p hp)
    (fun s hs => hconv0 p hp s hs)
    (fun s hs => hlim p hp s hs) τ hτ

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLimit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot IsDynEqOn IsDynGSolWith)

set_option autoImplicit false


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLimitDefsG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- Verbatim copy of `Work.FTS.FinalV2.EllLimOK3`. -/
def EllLimOK3 (α : ℝ) (E : Fn → Fn) : Prop :=
  ∀ (fn : ℕ → Fn) (f : Fn) (B : ℝ),
    (∀ n, Work.FTS.ClassC.ClassC α (fn n)) →
    (∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B) →
    ContDiffOn ℝ 4 (Function.uncurry f) Work.Construction.Qd →
    (∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (fn n) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i f z θ))) →
    Work.FTS.StrongGlobal.IsBslSolPos α f (E f) ∧
    ContDiffOn ℝ 3 (Function.uncurry (E f)) Work.Construction.Qd ∧
    ∀ j i : ℕ, j + i ≤ 3 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (E (fn n)) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i (E f) z θ))

theorem EllLimOK3.toEllLimOK {α : ℝ} {E : Fn → Fn} (h : EllLimOK3 α E) : EllLimOK α E := by
  intro fn f B hC hB h4 hj
  obtain ⟨hlaw, -, hconv⟩ := h fn f B hC hB h4 hj
  exact ⟨hlaw, fun j i hji z θ hzθ => hconv j i (by omega) z θ hzθ⟩

/-- **E5's new conclusion**: ONE family `g`, a limit package on every horizon. -/
def ExistsLimG (α C₀ K : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn) : Prop :=
  ∃ g : Fam, ∀ T : ℝ, 0 < T → ∃ Cd : ℝ, 0 < Cd ∧ EpsLimPkg α C₀ K Cd T Φs E g₀ g

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools.LinAux

set_option autoImplicit false

/-! ## The projection of a smooth profile -/

/-- `P₀ f = f − (L₁₂ f 0 / pzNorm) • bump` is smooth whenever `f` is. -/
theorem smoothOpen_Pz {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Pz f) := by
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
        * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul'
      (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
      Work.FTS.StrongEps.smoothOpen_bump
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => f z θ - (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
        * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.EllipticEst.smoothOpen_sub hf h2
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h4 : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => f z θ
        - (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
          * Work.FTS.StrongEps.bump z θ)) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp h3
  have hun : Function.uncurry (Work.FTS.StrongEps.Pz f)
      = Function.uncurry (fun z θ => f z θ
        - (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
          * Work.FTS.StrongEps.bump z θ) := by
    funext p
    rcases p with ⟨z, θ⟩
    exact Work.FTS.StrongEps.Pz_apply f z θ
  rw [hun]
  exact h4 n

/-! ## The angular–radial product -/


/-! ## The final constant -/


end Work.FTS.StrongEps.EpsSqTools.LinAux
end
end
