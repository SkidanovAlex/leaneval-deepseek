import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS_EllLimOK.L2Mem_of_HkMem_zero
import Submission.Work.FTS_EllLimOK.Pinning.smoothOpen_div_cos
import Submission.Work.FTS_EllLimOK.ProducerH.psiP_div_cos_defs
import Submission.Work.FTS_EllLimOK.ProducerH.kernel_le_small
import Submission.Work.FTS_EllLimOK.ProducerH.psiP_pointwise_cs
import Submission.Work.FTS_EllLimOK.ProducerH.slice_le_Gf
import Submission.Work.FTS_EllLimOK.ProducerH.Gf_le
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `psiP_div_cos` — the `U`-slot part of the stream function, divided by `cos θ`, is `ℋ⁰`

The producers of the `StreamBdry` chain run on the *particular solution* `psiP α Φ` of the
level-`0` ODE `α·D_z P + 3P = -sin(2θ)·U'(Φ)`.  This module shows that on the open quadrant
(where the fixed-point relation `Φ = psiP α Φ` holds) the quotient `Φ/cos θ` is in `ℋ⁰`, with
the quantitative bound `HkSq α 0 (Φ/cos) ≤ C · HkSq α 0 U'` and the per-slice bound
`∫_θ HkIntegrand α 0 (Φ/cos) z θ ≤ C(1 + 1/z)(M² + HkSq α 0 U')`, where `|U'| ≤ M` on the
quadrant.

The four ingredients are the modules imported above:

* `psiP_pointwise_cs` — the pointwise Cauchy–Schwarz bound
  `(Φ/cos θ)² ≤ (4/(3α))∫₀¹ v^β U'(zv,θ)² dv` on the quadrant;
* `slice_le_Gf` — the level-`0` slice of `Φ/cos` is dominated by `(4/(3α))·Gf α U'`, where
  `Gf α U z = w(z)²∫₀¹ v^β M₁(zv) dv` is the radial density of the angular moment
  `M₁(z) = ∫_θ U(z,θ)² sin(2θ)^{-η} dθ` (this is the Fubini step on the finite product
  `Iθ × (0,1)`);
* `Gf_le` — `Gf α U` is integrable on `(0,∞)` with `∫ Gf ≤ (1/β)·HkSq α 0 U`;
* `kernel_le_small` — the small-`z` bound `∫₀¹ v^β M₁(zv) dv ≤ z³·HkSq α 0 U`.

The assembly below additionally uses the direct `θ`-route at large `z`
(`∫₀¹ v^β U(zv,θ)² dv ≤ M²/(β+1)` pointwise in `θ`), which is the local lemma
`kernel_pointwise_le`. -/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **Pointwise kernel bound at fixed `θ`.**  For `z > 0`, `θ ∈ (0,π/2)` and `|U| ≤ M` on the
open quadrant: `∫₀¹ v^β U(zv,θ)² dv ≤ M²/(β+1)`. -/
theorem kernel_pointwise_le {α M : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {U : ℝ → ℝ → ℝ}
    (hbnd : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |U z θ| ≤ M)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (∫ v in (0 : ℝ)..1, v ^ (beta α) * (U (z * v) θ) ^ 2)
      ≤ M ^ 2 * (1 / (beta α + 1)) := by
  have hβ : -1 < beta α := by linarith [beta_pos hα hα1]
  have hval : (∫ v in (0 : ℝ)..1, M ^ 2 * v ^ (beta α)) = M ^ 2 * (1 / (beta α + 1)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hβ), Real.one_rpow,
      Real.zero_rpow (by linarith : beta α + 1 ≠ 0)]
    ring
  have hint : IntegrableOn (fun v : ℝ => v ^ (beta α)) (Set.Ioc (0 : ℝ) 1) := by
    have h2 := intervalIntegrable_iff.mp
      (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) hβ)
    rwa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h2
  rw [← hval, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    ?_ ?_ ?_
  · show ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        (0 : ℝ) ≤ v ^ (beta α) * (U (z * v) θ) ^ 2
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun v hv => mul_nonneg
      (Real.rpow_nonneg (le_of_lt hv.1) _) (sq_nonneg _)
  · exact hint.integrable.const_mul (M ^ 2)
  · show ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        v ^ (beta α) * (U (z * v) θ) ^ 2 ≤ M ^ 2 * v ^ (beta α)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun v hv => ?_
    have hv0 : 0 < v := hv.1
    have h2 := hbnd (z * v) θ (Set.mem_prod.mpr ⟨mul_pos hz hv0, hθ⟩)
    have h3 : (U (z * v) θ) ^ 2 ≤ M ^ 2 :=
      sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
    calc v ^ (beta α) * (U (z * v) θ) ^ 2 ≤ v ^ (beta α) * M ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (le_of_lt hv0) _)
      _ = M ^ 2 * v ^ (beta α) := by ring


/-- **`psiP/cos θ ∈ ℋ⁰` with its quantitative and slice bounds, controlled by the `U`-slot.**
For `Φ` smooth on the open quadrant with `Φ = psiP α Φ` there (no gauge summand), `U' := Uprime α Φ`
bounded by `M` on the quadrant and `HkMem α 0 U'`, the quotient `Φ/cos θ` is in `ℋ⁰`, with
`HkSq α 0 (Φ/cos θ) ≤ C * HkSq α 0 U'` and the per-slice bound
`∫_θ HkIntegrand α 0 (Φ/cos) z θ ≤ C (1 + 1/z) (M² + HkSq α 0 U')` for every `z > 0`.
Route (`psiP α Φ z θ = -(sin 2θ/α) ∫_0^1 v^(3/α-1) U'(zv,θ) dv`): Cauchy–Schwarz in `v` gives
`(Φ z θ/cos θ)² ≤ (4/(3α)) ∫_0^1 v^(3/α-1) U'(zv,θ)² dv` (using `sin²2θ/cos²θ = 4 sin²θ ≤ 4`).
- `ℋ⁰`: Tonelli, the substitution `t = zv` and `w(t/v) ≤ w(t)` for `0 < v ≤ 1` give
  `HkSq α 0 (Φ/cos) ≤ (4/(3(3-α))) HkSq α 0 U'`.
- slice: with `M₁(t) = ∫_θ U'(t,θ)² sin(2θ)^{-η} dθ`,
  `∫_θ (Φ z θ/cos θ)² sin(2θ)^{-η} dθ ≤ (4/(3α)) z^{-3/α} ∫_0^z t^{3/α-1} M₁(t) dt`;
  for `z ≤ 1` bound the inner integral by `z^{3/α+3} HkSq α 0 U'` (as `t^{-4} ≤ w(t)²`) and use
  `w(z)²z³ = (1+z)⁴/z ≤ 16/z`; at `z ≥ 1` use `|Φ/cos| ≤ 2M/3` and `w(z)² ≤ 16`.
Membership uses the per-slice finiteness of `M₁` from `HkMem α 0 U'` and the (a.e.) measurability
from `SmoothOpen Φ`; `w(0) = 0` gives the `z = 0` conjunct. -/
theorem psiP_div_cos {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Φ : ℝ → ℝ → ℝ) (M : ℝ), 0 ≤ M →
      Work.FTS.EllipticEst.SmoothOpen Φ →
      (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Φ z θ = Work.FTS.StreamBdryIface.psiP α Φ z θ) →
      (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        |Work.FTS.StreamBdryIface.Uprime α Φ z θ| ≤ M) →
      Work.Spaces.HkMem α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) →
      Work.Spaces.HkMem α 0 (fun z θ => Φ z θ / Real.cos θ) ∧
      Work.Spaces.HkSq α 0 (fun z θ => Φ z θ / Real.cos θ)
        ≤ C * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) ∧
      (∀ z : ℝ, 0 < z →
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
          ≤ C * (1 + 1 / z)
            * (M ^ 2 + Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ))) := by
  refine ⟨max (64 / (3 * α)) (64 * 10 ^ 4 / 9), by positivity, ?_⟩
  intro Φ M hM0 hsm hpsi hbnd hmem
  have hβ : 0 < beta α := beta_pos hα hα1
  -- `(4/(3α))·(1/β) ≤ C`
  have hCle : (4 / (3 * α)) * (1 / beta α) ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) := by
    have hb : beta α = 3 / α - 1 := rfl
    have h4 : (4 / (3 * α)) * (1 / (3 / α - 1)) = 4 / (3 * (3 - α)) := by
      have h1 : (0 : ℝ) < α := hα
      have h2 : (3 : ℝ) / α - 1 ≠ 0 := by linarith [hβ, hb]
      have h3 : (3 : ℝ) - α ≠ 0 := by linarith
      field_simp
    have h5 : 4 / (3 * (3 - α)) ≤ 64 / (3 * α) := by
      rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 3 * (3 - α)) (by linarith : (0 : ℝ) < 3 * α)]
      nlinarith [hα1, hα]
    calc (4 / (3 * α)) * (1 / beta α) = (4 / (3 * α)) * (1 / (3 / α - 1)) := by rw [hb]
      _ = 4 / (3 * (3 - α)) := h4
      _ ≤ 64 / (3 * α) := h5
      _ ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) := le_max_left _ _
  -- smoothness and measurability of the quotient
  have hXsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φ z θ / Real.cos θ) :=
    Work.FTS_EllLimOK.Pinning.smoothOpen_div_cos hsm
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hXsm.continuousOn_HkIntegrand α 0
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  -- the delegated pieces
  have hpt := Work.FTS_EllLimOK.ProducerH.psiP_pointwise_cs hα hM0 hpsi hbnd
  have hslice := Work.FTS_EllLimOK.ProducerH.slice_le_Gf hα hM0 hsm hbnd hpt
  obtain ⟨hGfint, hGfbd⟩ := Gf_le hα hα1 hmem
  have slice_nonneg : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ := fun z =>
    MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ) measurableSet_Icc
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
  -- the pointwise bound on `(Φ/cos θ)²`
  have hX2 : ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      (Φ z θ / Real.cos θ) ^ 2 ≤ (4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1))) := by
    intro z hz θ hθ
    have h1 := hpt z θ (Set.mem_prod.mpr ⟨hz, hθ⟩)
    have h2 := kernel_pointwise_le hα hα1 hbnd hz hθ
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
  -- the a.e. bound on the level-`0` integrand
  have hHk_ae : ∀ z : ℝ, 0 < z → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ
        ≤ ((Work.Spaces.w z) ^ 2 * ((4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1)))))
            * Work.FTS.EllipticEst.AngSecond.sig θ := by
    intro z hz
    have heq : MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))
        = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.restrict_Ioo_eq_restrict_Icc
    rw [← heq]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [HkIntegrand_eq_w2_sig α (fun z θ => Φ z θ / Real.cos θ) hθI]
    have hs : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg hθI
    have hx := hX2 z hz θ hθ
    have hw := sq_nonneg (Work.Spaces.w z)
    nlinarith [hx, hs, hw, mul_nonneg hw hs]
  have hSigInt : IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ := by
    simpa only [Work.FTS.EllipticEst.AngSecond.sig] using integrableOn_sin_rpow_neg
  have hSigVal : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ) ≤ 10 ^ 4 := by
    simpa only [Work.FTS.EllipticEst.AngSecond.sig] using integral_sin_rpow_le
  -- the membership
  have hmemX : Work.Spaces.HkMem α 0 (fun z θ => Φ z θ / Real.cos θ) := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
      · subst hz0
        have hzero : (fun θ : ℝ =>
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) 0 θ)
            = fun _ => (0 : ℝ) := by
          funext θ
          rw [HkIntegrand_zero_eq']
          simp [Work.Spaces.w]
        rw [hzero]
        exact integrableOn_zero
      · refine Integrable.mono'
          ((hSigInt.integrable).const_mul
            ((Work.Spaces.w z) ^ 2 * ((4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1)))))) ?_ ?_
        · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos
        · filter_upwards [hHk_ae z hzpos] with θ hθ
          rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)]
          exact hθ
    · have hIz : MeasureTheory.volume.restrict Work.Spaces.Iz
          = MeasureTheory.volume.restrict (Set.Ioi 0) := by
        rw [Work.Spaces.Iz]
        exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici).symm
      have hmaj : Integrable (fun z : ℝ =>
          (4 / (3 * α)) * Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        rw [hIz]
        exact hGfint.integrable.const_mul _
      refine Integrable.mono' hmaj haesm.integral_prod_right' ?_
      rw [hIz, MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun z hz => ?_
      rw [Real.norm_of_nonneg (slice_nonneg z)]
      rcases eq_or_lt_of_le (le_of_lt (Set.mem_Ioi.mp hz)) with hz0 | hzpos
      · subst hz0
        have hzero : (fun θ : ℝ =>
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) 0 θ)
            = fun _ => (0 : ℝ) := by
          funext θ
          rw [HkIntegrand_zero_eq']
          simp [Work.Spaces.w]
        have hGf0 : Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) 0 = 0 := by
          rw [Gf]
          simp [Work.Spaces.w]
        rw [hzero, integral_zero, hGf0]
        norm_num
      · exact hslice z hzpos
  -- the `HkSq` bound
  have hHkSqnn : 0 ≤ Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := by
    rw [Work.Spaces.HkSq]
    exact MeasureTheory.integral_nonneg fun z => MeasureTheory.setIntegral_nonneg
      measurableSet_Icc (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
  have hHkSq_le : Work.Spaces.HkSq α 0 (fun z θ => Φ z θ / Real.cos θ)
      ≤ ((4 / (3 * α)) * (1 / beta α))
          * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := by
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
        (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ) := by
      show ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ
      exact Filter.Eventually.of_forall fun z => slice_nonneg z
    have hae : (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
        ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
        (fun z => (4 / (3 * α)) * Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z) := by
      show ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
          ≤ (4 / (3 * α)) * Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall fun z hz => hslice z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg hnn
      (hGfint.integrable.const_mul _) hae
    rw [show (∫ z in Set.Ioi (0 : ℝ), (4 / (3 * α))
        * Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z)
        = (4 / (3 * α)) * ∫ z in Set.Ioi (0 : ℝ),
            Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z from
      MeasureTheory.integral_const_mul _ _] at hmono
    calc Work.Spaces.HkSq α 0 (fun z θ => Φ z θ / Real.cos θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ := rfl
      _ = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ := by
          rw [Work.Spaces.Iz]
          exact MeasureTheory.integral_Ici_eq_integral_Ioi
      _ ≤ (4 / (3 * α)) * ∫ z in Set.Ioi (0 : ℝ),
            Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z := hmono
      _ ≤ (4 / (3 * α)) * ((1 / beta α)
            * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)) :=
          mul_le_mul_of_nonneg_left hGfbd (by positivity)
      _ = ((4 / (3 * α)) * (1 / beta α))
            * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := by ring
  -- the per-slice bound
  have hslice_le : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
        ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z)
          * (M ^ 2 + Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)) := by
    intro z hz
    rcases le_total z 1 with hz1 | hz1
    · -- small `z`: use `Gf` and the kernel bound
      have hzpos : 0 < z := hz
      have hk := Work.FTS_EllLimOK.ProducerH.kernel_le_small hα hmem hz
      have hmain : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
          ≤ (4 / (3 * α)) * ((Work.Spaces.w z) ^ 2
              * ∫ v in (0 : ℝ)..1,
                  v ^ (beta α) * mom (Work.FTS.StreamBdryIface.Uprime α Φ) (z * v)) := by
        have h := hslice z hz
        rwa [Gf] at h
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hstep : (4 / (3 * α)) * ((Work.Spaces.w z) ^ 2
            * ∫ v in (0 : ℝ)..1, v ^ (beta α) * mom (Work.FTS.StreamBdryIface.Uprime α Φ) (z * v))
          ≤ (4 / (3 * α)) * ((Work.Spaces.w z) ^ 2
              * (z ^ 3 * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk hw2) (by positivity)
      have hw2z3 : (Work.Spaces.w z) ^ 2 * z ^ 3 = (1 + z) ^ 4 / z := by
        rw [show (Work.Spaces.w z) ^ 2 * z ^ 3 = ((Work.Spaces.w z) ^ 2 * z ^ 4) / z from by
          field_simp]
        rw [w_sq_mul_z4 (ne_of_gt hz)]
      have hc₀ : (0 : ℝ) ≤ 4 / (3 * α) := by positivity
      have hfin : (4 / (3 * α)) * ((Work.Spaces.w z) ^ 2
            * (z ^ 3 * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)))
          ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z)
            * (M ^ 2 + Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)) := by
        have hpow : (1 + z) ^ 4 ≤ 16 := by
          have h1 : 1 + z ≤ 2 := by linarith
          have h2 : (0 : ℝ) ≤ 1 + z := by linarith
          calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h2 h1 4
            _ = 16 := by norm_num
        have hC : 64 / (3 * α) ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) := le_max_left _ _
        have hCnn : (0 : ℝ) ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) := le_of_lt (by positivity)
        have h1z : 1 / z ≤ 1 + 1 / z := by linarith
        have h1zn : 0 ≤ 1 / z := by positivity
        have hH : 0 ≤ Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := hHkSqnn
        have hMnn : 0 ≤ M ^ 2 := sq_nonneg M
        have hstep1 : (4 / (3 * α)) * ((Work.Spaces.w z) ^ 2
              * (z ^ 3 * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)))
            = (4 / (3 * α)) * ((1 + z) ^ 4 / z)
              * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := by
          rw [← hw2z3]; ring
        have hstep2 : (4 / (3 * α)) * ((1 + z) ^ 4 / z)
              * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)
            ≤ (4 / (3 * α)) * (16 / z)
              * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := by
          refine mul_le_mul_of_nonneg_right ?_ hH
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hpow (le_of_lt hzpos)) hc₀
        have hstep3 : (4 / (3 * α)) * (16 / z)
              * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)
            ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z)
              * (M ^ 2 + Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)) := by
          have h4 : (4 / (3 * α)) * (16 / z) ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z) := by
            have h5 : (4 / (3 * α)) * (16 / z) = (64 / (3 * α)) * (1 / z) := by ring
            rw [h5]
            exact mul_le_mul hC h1z h1zn (by positivity)
          have h6 := mul_le_mul_of_nonneg_right h4 hH
          refine le_trans h6 ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
        rw [hstep1]
        exact le_trans hstep2 hstep3
      exact le_trans hmain (le_trans hstep hfin)
    · -- large `z`
      have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
      have hθb : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
          ≤ ((Work.Spaces.w z) ^ 2 * ((4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1)))))
              * ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ := by
        have h := MeasureTheory.integral_mono_of_nonneg
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
          ((hSigInt.integrable).const_mul _) (hHk_ae z hzpos)
        rwa [MeasureTheory.integral_const_mul] at h
      have hw16 : (Work.Spaces.w z) ^ 2 ≤ 16 := by
        have h2 : Work.Spaces.w z = (1 + 1 / z) ^ 2 := by
          rw [Work.Spaces.w]
          field_simp
          ring
        rw [h2]
        have h3 : 1 + 1 / z ≤ 2 := by
          have h4 : 1 / z ≤ 1 := by
            rw [div_le_one hzpos]
            exact hz1
          linarith
        have h4 : (0 : ℝ) ≤ 1 + 1 / z := by positivity
        have h5 : (1 + 1 / z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h4 h3 4
        have h6 : ((1 + 1 / z) ^ 2) ^ 2 = (1 + 1 / z) ^ 4 := by ring
        rw [h6]
        norm_num at h5 ⊢
        linarith
      have hβ1 : (4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1))) ≤ (4 / 9) * M ^ 2 := by
        have hb : beta α + 1 = 3 / α := by
          have h : beta α = 3 / α - 1 := rfl
          rw [h]; field_simp; ring
        rw [hb, one_div, inv_div]
        have h1 : (4 / (3 * α)) * (M ^ 2 * (α / 3)) = (4 / 9) * M ^ 2 := by
          field_simp
          ring
        rw [h1]
      have hfin : ((Work.Spaces.w z) ^ 2 * ((4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1)))))
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ)
          ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z)
            * (M ^ 2 + Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)) := by
        have hC : 64 * 10 ^ 4 / 9 ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) := le_max_right _ _
        have hCnn : (0 : ℝ) ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) := le_of_lt (by positivity)
        have h1z : 1 ≤ 1 + 1 / z := by
          have : 0 ≤ 1 / z := by positivity
          linarith
        have hMnn : 0 ≤ M ^ 2 := sq_nonneg M
        have hHnn' : 0 ≤ Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) := hHkSqnn
        have hsig : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ :=
          MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ) measurableSet_Icc
            (fun θ hθ => Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)
        have hprod : ((Work.Spaces.w z) ^ 2 * ((4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1)))))
              * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ)
            ≤ 16 * ((4 / 9) * M ^ 2) * 10 ^ 4 := by
          have h1 : (Work.Spaces.w z) ^ 2 * ((4 / (3 * α)) * (M ^ 2 * (1 / (beta α + 1))))
              ≤ 16 * ((4 / 9) * M ^ 2) :=
            mul_le_mul hw16 hβ1 (by positivity) (by positivity)
          exact mul_le_mul h1 hSigVal hsig (by positivity)
        have hval : 16 * ((4 / 9) * M ^ 2) * 10 ^ 4 = (64 * 10 ^ 4 / 9) * M ^ 2 := by ring
        rw [hval] at hprod
        have h8 : (64 * 10 ^ 4 / 9) * M ^ 2
            ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z) * M ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hMnn
          simpa using mul_le_mul hC h1z zero_le_one hCnn
        have h9 : max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z) * M ^ 2
            ≤ max (64 / (3 * α)) (64 * 10 ^ 4 / 9) * (1 + 1 / z)
              * (M ^ 2 + Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
        exact le_trans hprod (le_trans h8 h9)
      exact le_trans hθb hfin
  exact ⟨hmemX, le_trans hHkSq_le (mul_le_mul_of_nonneg_right hCle hHkSqnn), hslice_le⟩

end Work.FTS_EllLimOK.ProducerH
