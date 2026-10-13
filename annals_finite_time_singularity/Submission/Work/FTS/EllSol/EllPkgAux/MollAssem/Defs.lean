/-
# `Work.FTS.EllSol.EllPkgAux.MollAssem.Defs` — the Fatou device and the interval estimate

Two independent ingredients of the Fatou assembly of `Work.FTS.EllSol.EllPkgAux.mollFatouAssembly`
(kept in their own module because the assembly file is long):

* `fatou_lintegral_le_liminf` — Fatou's lemma at the `ℝ≥0∞` level (no integrability needed),
  together with the `ENNReal.ofReal`-measurability helper and the pointwise nonnegativity of
  `mixIntS`;
* `sliceIntBoundMFA` — the weighted interval Cauchy–Schwarz estimate
  `|∫_l^u (c-t)D t| ≤ (π/4)·√(π/4)·√(∫_{Iθ} D²thEta)` (length of `[l,u]` at most `π/4`, and
  `thEta = sin(2θ)^{-η} ≥ 1` on `(0,π/2)`), which is what the second-order Taylor formula of
  the slice domination `MollAssem.sliceDomMFA` consumes.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MollAssem

/-! ## The measure-theoretic Fatou device -/

/-- **Fatou's lemma** (lower semicontinuity of the lower Lebesgue integral), stated at the
`ℝ≥0∞` level so that no integrability hypothesis is needed: if `ofReal (f x) ≤ liminf_n
ofReal (G n x)` almost everywhere, then `∫⁻ ofReal f ≤ liminf_n ∫⁻ ofReal (G n)`. -/
theorem fatou_lintegral_le_liminf {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : ℕ → α → ℝ} {f : α → ℝ}
    (hG : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (G n x)) μ)
    (h : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) ≤
      Filter.liminf (fun n => ENNReal.ofReal (G n x)) Filter.atTop) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (G n x) ∂μ) Filter.atTop :=
  (MeasureTheory.lintegral_mono_ae h).trans (MeasureTheory.lintegral_liminf_le' hG)

/-- `ENNReal.ofReal` of an a.e. strongly measurable real function is a.e. measurable. -/
theorem aemeasurable_ofReal_of_aestronglyMeasurable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (h : AEStronglyMeasurable f μ) :
    AEMeasurable (fun x => ENNReal.ofReal (f x)) μ :=
  ENNReal.measurable_ofReal.comp_aemeasurable h.aemeasurable

/-- `mixIntS` is pointwise nonnegative (the `θ`-integrand is a square times `thEta ≥ 0`). -/
theorem mixIntS_nonneg_mfa (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ Work.EllipticEst.Core.mixIntS u z := by
  rw [Work.EllipticEst.Core.mixIntS]
  refine mul_nonneg (sq_nonneg _) ?_
  refine MeasureTheory.integral_nonneg_of_ae ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)

/-! ## The interval estimate of the slice domination -/

/-- On `(0, π/2)` the weight `thEta θ = sin(2θ)^{-η}` is at least `1`. -/
theorem one_le_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h := Real.rpow_le_rpow_of_nonpos hsinpos (Real.sin_le_one (2 * θ))
    (show -(Work.Spaces.eta) ≤ 0 by rw [Work.Spaces.eta]; norm_num)
  rw [Real.one_rpow] at h
  simpa only [Work.FTS.EllipticEst.thEta] using h

/-- **The interval estimate of the slice domination.**  Weighted Cauchy--Schwarz with the
constant weight `1` on the interval `[l,u]` (length at most `π/4`) against the angular weight
`thEta ≥ 1` on `(0,π/2)`:
`|∫_l^u (c-t)D t| ≤ (π/4)·√(π/4)·√(∫_{Iθ} D²thEta)`. -/
theorem sliceIntBoundMFA {D : ℝ → ℝ} {c l u : ℝ} (hlu : l ≤ u) (hl : 0 < l)
    (hu : u < Real.pi / 2) (hul : u - l ≤ Real.pi / 4) (hcont : ContinuousOn D (Set.uIcc l u))
    (hc : ∀ t ∈ Set.Icc l u, |c - t| ≤ Real.pi / 4)
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => D θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    |∫ t in l..u, (c - t) * D t| ≤ (Real.pi / 4) * Real.sqrt (Real.pi / 4) *
      Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hth : ∀ t ∈ Set.Icc l u, 1 ≤ Work.FTS.EllipticEst.thEta t := fun t ht =>
    one_le_thEta ⟨lt_of_lt_of_le hl ht.1, lt_of_le_of_lt ht.2 hu⟩
  have hIntAbs : IntervalIntegrable (fun t : ℝ => |D t|) volume l u :=
    hcont.abs.intervalIntegrable
  have h12 : |∫ t in l..u, (c - t) * D t| ≤ ∫ t in l..u, |(c - t) * D t| :=
    intervalIntegral.abs_integral_le_integral_abs hlu
  have h23 : ∫ t in l..u, |(c - t) * D t| ≤ (Real.pi / 4) * ∫ t in l..u, |D t| := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hlu
      (((continuousOn_const.sub continuousOn_id).mul hcont).abs.intervalIntegrable)
      (hIntAbs.const_mul _) ?_
    intro t ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hc t ht) (abs_nonneg _)
  have hD2int : MeasureTheory.IntegrableOn (fun t : ℝ => D t ^ 2) (Set.Ioc l u) := by
    have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => D t ^ 2) (Set.uIcc l u) :=
      (hcont.pow 2).integrableOn_compact isCompact_uIcc
    rw [Set.uIcc_of_le hlu] at h1
    exact h1.mono_set Set.Ioc_subset_Icc_self
  have h1int : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc l u) := by
    refine MeasureTheory.integrableOn_const (s := Set.Ioc l u) (C := (1 : ℝ)) ?_ ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    · simp
  have hcs : (∫ t in l..u, |D t|) ^ 2 ≤ (u - l) * (∫ t in l..u, D t ^ 2) := by
    have h := Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul (f := fun t : ℝ => |D t|)
      (σ := fun _ : ℝ => (1 : ℝ)) hlu (fun s _ => by norm_num)
      (hD2int.congr_fun (fun s _ => by rw [mul_one, sq_abs]) measurableSet_Ioc)
      (by simpa using h1int)
    have hs1 : (∫ s in l..u, |D s| ^ 2 * (1 : ℝ)) = ∫ s in l..u, D s ^ 2 :=
      intervalIntegral.integral_congr (fun s _ => by rw [mul_one, sq_abs])
    have hs2 : (∫ s in l..u, ((1 : ℝ))⁻¹) = u - l := by
      rw [inv_one, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    rw [hs1, hs2] at h
    exact h.trans_eq (mul_comm _ _)
  have hmono : ∫ t in l..u, D t ^ 2 ≤
      ∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    have hsub1 : Set.Ioc l u ⊆ Work.Spaces.Iθ := by
      intro t ht
      exact ⟨le_trans (le_of_lt hl) (le_of_lt ht.1), le_trans ht.2 (le_of_lt hu)⟩
    have h2int : MeasureTheory.IntegrableOn
        (fun t : ℝ => D t ^ 2 * Work.FTS.EllipticEst.thEta t) (Set.Ioc l u) :=
      hint.mono_set hsub1
    have hpoint : ∀ t ∈ Set.Ioc l u, D t ^ 2 ≤ D t ^ 2 * Work.FTS.EllipticEst.thEta t := by
      intro t ht
      have := hth t (Set.Ioc_subset_Icc_self ht)
      calc D t ^ 2 = D t ^ 2 * 1 := by ring
        _ ≤ D t ^ 2 * Work.FTS.EllipticEst.thEta t :=
            mul_le_mul_of_nonneg_left this (sq_nonneg _)
    have hA : ∫ t in l..u, D t ^ 2 ≤
        ∫ t in l..u, D t ^ 2 * Work.FTS.EllipticEst.thEta t := by
      rw [intervalIntegral.integral_of_le hlu, intervalIntegral.integral_of_le hlu]
      exact MeasureTheory.setIntegral_mono_on hD2int h2int measurableSet_Ioc hpoint
    have hB : ∫ t in l..u, D t ^ 2 * Work.FTS.EllipticEst.thEta t ≤
        ∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      rw [intervalIntegral.integral_of_le hlu]
      refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
      · refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
      · refine Filter.Eventually.of_forall (fun x hx => ?_)
        exact ⟨le_trans (le_of_lt hl) (le_of_lt hx.1), le_trans hx.2 (le_of_lt hu)⟩
    exact hA.trans hB
  have hsq : (∫ t in l..u, |D t|) ^ 2 ≤ (Real.pi / 4) *
      (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    refine hcs.trans ?_
    refine mul_le_mul hul hmono ?_ (le_of_lt hpi4)
    exact intervalIntegral.integral_nonneg_of_ae hlu (ae_of_all _ (fun t => sq_nonneg (D t)))
  have hIabs_nn : 0 ≤ ∫ t in l..u, |D t| :=
    intervalIntegral.integral_nonneg_of_ae hlu (ae_of_all _ (fun t => abs_nonneg _))
  have hRnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    MeasureTheory.integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))
  have hbound : ∫ t in l..u, |D t| ≤ Real.sqrt (Real.pi / 4) *
      Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    have h1 : ∫ t in l..u, |D t| ≤ Real.sqrt ((Real.pi / 4) *
        (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ)) :=
      (Real.le_sqrt hIabs_nn (mul_nonneg (le_of_lt hpi4) hRnn)).mpr hsq
    rwa [Real.sqrt_mul (le_of_lt hpi4)] at h1
  calc |∫ t in l..u, (c - t) * D t| ≤ ∫ t in l..u, |(c - t) * D t| := h12
    _ ≤ (Real.pi / 4) * ∫ t in l..u, |D t| := h23
    _ ≤ (Real.pi / 4) * (Real.sqrt (Real.pi / 4) *
        Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ)) :=
        mul_le_mul_of_nonneg_left hbound (le_of_lt hpi4)
    _ = (Real.pi / 4) * Real.sqrt (Real.pi / 4) *
        Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by ring

end MollAssem

end Work.FTS.EllSol.EllPkgAux
