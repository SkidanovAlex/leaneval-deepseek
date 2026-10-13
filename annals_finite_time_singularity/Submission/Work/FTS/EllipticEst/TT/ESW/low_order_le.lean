import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs
import Submission.Work.FTS.EllipticEst.TT.ESW.slice_tendsto_pi_half
import Submission.Work.FTS.EllipticEst.Honest.HonSliceRightTendsto
import Submission.Work.FTS.EllipticEst.TanTheta.slice_poincare_eta
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

/-!
# `low_order_le`

The low-order angular terms `∫∫ w²((∂_θΨ)² + Ψ²)` of a datum of the weak class
`TT.EllWeakPos α k F Ψ` are controlled by the `η`-weighted second angular derivative
`∫∫ w² (∂_θθΨ)² sin(2θ)^{-η}`.

The proof is slicewise.  For a single slice `u = Ψ z ·`:

* `∫ (u'')² sin(2θ)^{-η} < ∞` (the `i = 0` slot of `HkMem`), which also bounds `u` and `u'`
  uniformly (`Honest.SliceBddSqSigma`), so that `u σ` is honest;
* the moment condition `∫ u sinθcos²θ = 0` (a field of `EllWeakPos`) and the continuity of `u`
  on the open interval produce an **interior zero** `θ₁` of `u` (a constant sign would make the
  moment integral strictly signed);
* the right endpoint has limit `0`, so Rolle's theorem on `[θ₁, π/2]` produces an interior
  critical point `θ₀` of `u`;
* the fundamental theorem of calculus from `θ₀` bounds `(u')² ≤ (π/2)∫(u'')²`, and from `θ₁`
  bounds `|u| ≤ √((π/2)∫(u'')²)·|θ - θ₁|`.  Integrating gives the constant
  `(π/2)² + (π/2)⁴ < 20`.

No left endpoint limit is used, so the argument applies to the whole weak class.
-/

/-- `sin θ cos²θ > 0` on the open interval `(0, π/2)`. -/
theorem sinCos2_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Work.Elliptic.sinCos2 θ := by
  have h0 : (0 : ℝ) < θ := hθ.1
  have h1 : θ < Real.pi / 2 := hθ.2
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  rw [Work.Elliptic.sinCos2]
  exact mul_pos hsin (pow_pos hcos 2)

/-- A continuous function on the open interval with no zero there has constant sign. -/
theorem sign_const_of_no_zero {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u θ ≠ 0) :
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < u θ) ∨
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u θ < 0) := by
  have hq : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rcases lt_or_gt_of_ne (a := (0 : ℝ)) (b := u (Real.pi / 4))
    (Ne.symm (hne (Real.pi / 4) hq)) with hpos | hneg
  · left
    intro θ hθ
    by_contra hcon
    rw [not_lt] at hcon
    have hneg' : u θ < 0 := lt_of_le_of_ne hcon (hne θ hθ)
    have hiv := IsPreconnected.intermediate_value isPreconnected_Ioo hθ hq hcont
      (f := u) ⟨le_of_lt hneg', le_of_lt hpos⟩
    obtain ⟨x, hx, hxu⟩ := hiv
    exact hne x hx hxu
  · right
    intro θ hθ
    by_contra hcon
    rw [not_lt] at hcon
    have hpos' : 0 < u θ := lt_of_le_of_ne hcon (Ne.symm (hne θ hθ))
    have hiv := IsPreconnected.intermediate_value isPreconnected_Ioo hq hθ hcont
      (f := u) ⟨le_of_lt hneg, le_of_lt hpos'⟩
    obtain ⟨x, hx, hxu⟩ := hiv
    exact hne x hx hxu

/-- **The moment condition gives an interior zero.**  A continuous function on `(0, π/2)` which
is integrable against `sinθcos²θ` and has vanishing angular moment must vanish somewhere in the
open interval (otherwise it has a constant sign and the moment integral is strictly signed). -/
theorem exists_interior_zero_of_moment {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint : IntegrableOn (fun θ => u θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, u θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∃ θ₁ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u θ₁ = 0 := by
  by_contra h
  push_neg at h
  have hsupp_measure : ∀ v : ℝ → ℝ, Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Function.support v →
      0 < volume (Function.support v ∩ Work.Spaces.Iθ) := by
    intro v hsub
    have h1 : volume (Set.Ioo (0 : ℝ) (Real.pi / 2))
        ≤ volume (Function.support v ∩ Work.Spaces.Iθ) :=
      measure_mono fun x hx => ⟨hsub hx, ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩
    refine lt_of_lt_of_le ?_ h1
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
  rcases sign_const_of_no_zero hcont h with hpos | hneg
  · have hle : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => u θ * Work.Elliptic.sinCos2 θ) :=
      Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ =>
        le_of_lt (mul_pos (hpos θ hθ) (sinCos2_pos_of_mem_Ioo hθ))
    have hsupp : 0 < volume (Function.support (fun θ => u θ * Work.Elliptic.sinCos2 θ)
        ∩ Work.Spaces.Iθ) :=
      hsupp_measure _ fun θ hθ => by
        rw [Function.mem_support]
        exact ne_of_gt (mul_pos (hpos θ hθ) (sinCos2_pos_of_mem_Ioo hθ))
    have hpos' := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hle hint).mpr hsupp
    rw [hmom] at hpos'
    exact lt_irrefl 0 hpos'
  · have hle : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => -(u θ * Work.Elliptic.sinCos2 θ)) :=
      Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ =>
        le_of_lt (neg_pos.mpr (mul_neg_of_neg_of_pos (hneg θ hθ) (sinCos2_pos_of_mem_Ioo hθ)))
    have hsupp : 0 < volume (Function.support (fun θ => -(u θ * Work.Elliptic.sinCos2 θ))
        ∩ Work.Spaces.Iθ) :=
      hsupp_measure _ fun θ hθ => by
        rw [Function.mem_support]
        exact ne_of_gt
          (neg_pos.mpr (mul_neg_of_neg_of_pos (hneg θ hθ) (sinCos2_pos_of_mem_Ioo hθ)))
    have hneg' := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hle hint.neg).mpr hsupp
    rw [MeasureTheory.integral_neg, hmom, neg_zero] at hneg'
    exact lt_irrefl 0 hneg'

/-- Continuity on `[θ₁, π/2]` from continuity on the open interval, the right limit `0` and the
value `0` at `π/2`. -/
theorem continuousOn_Icc_of_tendsto {u : ℝ → ℝ} {a : ℝ}
    (hcont : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hπ : Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hval : u (Real.pi / 2) = 0) (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ContinuousOn u (Set.Icc a (Real.pi / 2)) := by
  intro x hx
  rcases lt_or_eq_of_le hx.2 with h | h
  · exact (hcont.continuousAt
      (isOpen_Ioo.mem_nhds ⟨lt_of_lt_of_le ha.1 hx.1, h⟩)).continuousWithinAt
  · subst h
    rw [ContinuousWithinAt, hval]
    have hsub : Set.Icc a (Real.pi / 2) ⊆ Set.Ico a (Real.pi / 2) ∪ {Real.pi / 2} := by
      intro y hy
      rcases eq_or_lt_of_le hy.2 with h2 | h2
      · exact Or.inr h2
      · exact Or.inl ⟨hy.1, h2⟩
    have hpure : Tendsto u (pure (Real.pi / 2)) (nhds 0) := by
      have h := tendsto_pure_nhds u (Real.pi / 2)
      rwa [hval] at h
    have h1 : Tendsto u (nhdsWithin (Real.pi / 2) (Set.Ico a (Real.pi / 2))
        ⊔ pure (Real.pi / 2)) (nhds 0) :=
      Tendsto.sup (hπ.mono_left (nhdsWithin_mono _ fun y hy => hy.2)) hpure
    have h2 : nhdsWithin (Real.pi / 2) (Set.Icc a (Real.pi / 2))
        ≤ nhdsWithin (Real.pi / 2) (Set.Ico a (Real.pi / 2)) ⊔ pure (Real.pi / 2) := by
      have h3 := nhdsWithin_mono (Real.pi / 2) hsub
      rwa [nhdsWithin_union, nhdsWithin_singleton] at h3
    exact h1.mono_left h2

/-- **The `(u')²`-bound from an interior critical point.**  On the open interval, `(u')²` is
bounded by `(π/2)·∫(u'')²` as soon as `u'` vanishes somewhere inside. -/
theorem slice_deriv_bound {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hcrit : deriv u θ₀ = 0)
    (h2 : IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2
      ≤ (Real.pi / 2) * (∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2) := by
  have hder1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hv_cont : ContinuousOn (fun s => deriv (fun t => deriv u t) s)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h2' : ContDiffOn ℝ 0 (deriv (fun t => deriv u t))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hder1.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)
    exact h2'.continuousOn
  -- integrability of `(u'')²` on the slice
  have hE2 : IntegrableOn (fun s => (deriv (fun t => deriv u t) s) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' h2
      ((measurable_deriv (fun t => deriv u t)).pow_const 2).aestronglyMeasurable ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 := Work.FTS.EllipticEst.Honest.one_le_sEta hθ
    nlinarith [sq_nonneg (deriv (fun t => deriv u t) θ)]
  -- the derivative of `deriv u` is `deriv (deriv u)`
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t => deriv u t) x) x := by
    intro x hx
    exact ((hder1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  -- fundamental theorem of calculus for `deriv u`
  have hftc : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      ∫ s in a..b, deriv (fun t => deriv u t) s = deriv u b - deriv u a := by
    intro a b hab hsub
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ ?_
    · exact hder1.continuousOn.mono hsub
    · intro x hx
      exact hderiv x (hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    · exact (hv_cont.mono hsub).intervalIntegrable_of_Icc hab
  -- monotonicity of the energy along subintervals
  have hmono : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (∫ s in a..b, (deriv (fun t => deriv u t) s) ^ 2)
        ≤ ∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2 := by
    intro a b hab hsub
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.setIntegral_mono_set hE2
      (Eventually.of_forall fun s => sq_nonneg _)
      (Eventually.of_forall fun s hs => by
        obtain ⟨h1, h2⟩ := hsub ⟨le_of_lt hs.1, hs.2⟩
        exact ⟨le_of_lt h1, le_of_lt h2⟩)
  intro θ hθ
  rcases le_total θ₀ θ with hle | hle
  · have hsub : Set.Icc θ₀ θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le hθ₀.1 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    have hdiff : deriv u θ - deriv u θ₀ = ∫ s in θ₀..θ, deriv (fun t => deriv u t) s :=
      (hftc hle hsub).symm
    have hcs := Work.FTS.EllipticEst.TanTheta.sq_integral_le
      (fun s => deriv (fun t => deriv u t) s) θ₀ θ hle (hv_cont.mono hsub)
    have hnn : 0 ≤ ∫ s in θ₀..θ, (deriv (fun t => deriv u t) s) ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hle fun s => sq_nonneg _
    calc (deriv u θ) ^ 2 = (deriv u θ - deriv u θ₀) ^ 2 := by rw [hcrit, sub_zero]
      _ = (∫ s in θ₀..θ, deriv (fun t => deriv u t) s) ^ 2 := by rw [hdiff]
      _ ≤ (θ - θ₀) * (∫ s in θ₀..θ, (deriv (fun t => deriv u t) s) ^ 2) := hcs
      _ ≤ (Real.pi / 2) * (∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2) :=
          mul_le_mul (by linarith [hθ.2, hθ₀.1]) (hmono hle hsub) hnn (by positivity)
  · have hsub : Set.Icc θ θ₀ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 hθ₀.2⟩
    have hdiff : deriv u θ₀ - deriv u θ = ∫ s in θ..θ₀, deriv (fun t => deriv u t) s :=
      (hftc hle hsub).symm
    have hcs := Work.FTS.EllipticEst.TanTheta.sq_integral_le
      (fun s => deriv (fun t => deriv u t) s) θ θ₀ hle (hv_cont.mono hsub)
    have hnn : 0 ≤ ∫ s in θ..θ₀, (deriv (fun t => deriv u t) s) ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hle fun s => sq_nonneg _
    calc (deriv u θ) ^ 2 = (deriv u θ - deriv u θ₀) ^ 2 := by rw [hcrit, sub_zero]
      _ = (∫ s in θ..θ₀, deriv (fun t => deriv u t) s) ^ 2 := by
          rw [← hdiff]; ring
      _ ≤ (θ₀ - θ) * (∫ s in θ..θ₀, (deriv (fun t => deriv u t) s) ^ 2) := hcs
      _ ≤ (Real.pi / 2) * (∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2) :=
          mul_le_mul (by linarith [hθ₀.2, hθ.1]) (hmono hle hsub) hnn (by positivity)

/-- **The `u²`-bound from an interior zero.**  If `u` vanishes at an interior point and
`(u')² ≤ (π/2)∫(u'')²` on the slice, then `u² ≤ (π/2)³∫(u'')²`. -/
theorem slice_value_bound {u : ℝ → ℝ} {θ₁ : ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hθ₁ : θ₁ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hzero : u θ₁ = 0)
    (h1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2
      ≤ (Real.pi / 2) * (∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2)) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ) ^ 2
      ≤ (Real.pi / 2) ^ 3 * (∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2) := by
  set E : ℝ := ∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2 with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact MeasureTheory.integral_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun s => (deriv (fun t => deriv u t) s) ^ 2) fun s => sq_nonneg _
  have hC : 0 ≤ (Real.pi / 2) * E := mul_nonneg (by positivity) hE0
  have hseed : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2 ≤ (Real.pi / 2) * E :=
    fun θ hθ => by rw [hE]; exact h1 θ hθ
  have hder1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  -- the norm bound on the difference quotient
  have hstep : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |∫ s in a..b, deriv u s| ≤ Real.sqrt ((Real.pi / 2) * E) * |b - a| := by
    intro a b hab hsub
    refine intervalIntegral.norm_integral_le_of_norm_le_const (f := fun s => deriv u s)
      (a := a) (b := b) (C := Real.sqrt ((Real.pi / 2) * E)) fun s hs => ?_
    rw [Set.uIoc_of_le hab] at hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨(hsub ⟨le_of_lt hs.1, hs.2⟩).1, (hsub ⟨le_of_lt hs.1, hs.2⟩).2⟩
    rw [Real.norm_eq_abs]
    calc |deriv u s| = Real.sqrt ((deriv u s) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((Real.pi / 2) * E) := Real.sqrt_le_sqrt (hseed s hs')
  -- fundamental theorem of calculus for `u`
  have hftc : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      ∫ s in a..b, deriv u s = u b - u a := by
    intro a b hab hsub
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ ?_
    · exact hsm.continuousOn.mono hsub
    · intro x hx
      exact ((hsm.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds (hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩))).hasDerivAt
    · exact hder1.continuousOn.mono hsub |>.intervalIntegrable_of_Icc hab
  intro θ hθ
  rcases le_total θ₁ θ with hle | hle
  · have hsub : Set.Icc θ₁ θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le hθ₁.1 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    have habs : |u θ| ≤ Real.sqrt ((Real.pi / 2) * E) * (θ - θ₁) := by
      calc |u θ| = |∫ s in θ₁..θ, deriv u s| := by rw [hftc hle hsub, hzero, sub_zero]
        _ ≤ Real.sqrt ((Real.pi / 2) * E) * |θ - θ₁| := hstep hle hsub
        _ = Real.sqrt ((Real.pi / 2) * E) * (θ - θ₁) := by
            rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ θ - θ₁)]
    have hkey : (u θ) ^ 2 ≤ ((Real.pi / 2) * E) * (θ - θ₁) ^ 2 := by
      have h2 := pow_le_pow_left₀ (abs_nonneg (u θ)) habs 2
      rwa [mul_pow, Real.sq_sqrt hC, sq_abs] at h2
    calc (u θ) ^ 2 ≤ ((Real.pi / 2) * E) * (θ - θ₁) ^ 2 := hkey
      _ ≤ ((Real.pi / 2) * E) * (Real.pi / 2) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          nlinarith [hθ.2, hθ₁.1]
      _ = (Real.pi / 2) ^ 3 * E := by ring
  · have hsub : Set.Icc θ θ₁ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 hθ₁.2⟩
    have habs : |u θ| ≤ Real.sqrt ((Real.pi / 2) * E) * (θ₁ - θ) := by
      calc |u θ| = |∫ s in θ..θ₁, deriv u s| := by rw [hftc hle hsub, hzero, zero_sub, abs_neg]
        _ ≤ Real.sqrt ((Real.pi / 2) * E) * |θ₁ - θ| := hstep hle hsub
        _ = Real.sqrt ((Real.pi / 2) * E) * (θ₁ - θ) := by
            rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ θ₁ - θ)]
    have hkey : (u θ) ^ 2 ≤ ((Real.pi / 2) * E) * (θ₁ - θ) ^ 2 := by
      have h2 := pow_le_pow_left₀ (abs_nonneg (u θ)) habs 2
      rwa [mul_pow, Real.sq_sqrt hC, sq_abs] at h2
    calc (u θ) ^ 2 ≤ ((Real.pi / 2) * E) * (θ₁ - θ) ^ 2 := hkey
      _ ≤ ((Real.pi / 2) * E) * (Real.pi / 2) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          nlinarith [hθ₁.2, hθ.1]
      _ = (Real.pi / 2) ^ 3 * E := by ring

/-- **The slice facts supplied by the weak class.**  For `z > 0`: the slice is `C²` on the open
interval, its `η`-weighted second derivative is integrable, `Ψ z · · sinθcos²θ` is integrable,
the angular moment vanishes, and the Dirichlet value at `π/2` is `0`. -/
theorem slice_class_facts {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    IntegrableOn (fun θ => (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
    IntegrableOn (fun θ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Elliptic.sinCos2 θ) = 0 ∧
    Ψ z (Real.pi / 2) = 0 := by
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hsm2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Honest.contDiffOn_slice Ψ hz (hwk.smooth 2)
  have hB2p : IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice ((hS.pth).pth) hwk.memB 0 (Nat.zero_le k) hz
  have hB2 : IntegrableOn (fun θ => (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using hB2p
  refine ⟨hsm2, hB2, ?_, ?_, hwk.pi_half z⟩
  · -- `Ψ z · · sinθcos²θ` is integrable (from the boundedness of the slice)
    obtain ⟨C, hC0, hC⟩ := Work.FTS.EllipticEst.Honest.SliceBddSqSigma hsm2 hB2
    have hσ : IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.remov.ws_sEta_integrableOn
    refine MeasureTheory.Integrable.mono' (hσ.const_mul C) ?_ ?_
    · have h1 : AEStronglyMeasurable (fun θ => Ψ z θ) (volume.restrict Work.Spaces.Iθ) :=
        Work.FTS.EllipticEst.remov.ws_aesm_slice hS hz
      have h2 : AEStronglyMeasurable (fun θ => Work.Elliptic.sinCos2 θ)
          (volume.restrict Work.Spaces.Iθ) :=
        (by simp only [Work.Elliptic.sinCos2]; fun_prop :
          Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ).aestronglyMeasurable
      exact h1.mul h2
    · refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ => ?_
      have hsin0 : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
      have hsc0 : 0 ≤ Work.Elliptic.sinCos2 θ := by
        rw [Work.Elliptic.sinCos2]; exact mul_nonneg hsin0 (sq_nonneg _)
      have hσ0 : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
        Work.FTS.EllipticEst.Honest.sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsc0]
      have hsc1 : Work.Elliptic.sinCos2 θ ≤ 1 := by
        rw [Work.Elliptic.sinCos2]
        have hc : Real.cos θ ^ 2 ≤ 1 := by
          nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ, sq_nonneg (Real.cos θ)]
        nlinarith [Real.sin_le_one θ, hsin0, hc]
      have hsc2 : Work.Elliptic.sinCos2 θ ≤ Work.FTS.EllipticEst.sEta θ :=
        le_trans hsc1 (Work.FTS.EllipticEst.Honest.one_le_sEta hθ)
      calc |Ψ z θ| * Work.Elliptic.sinCos2 θ ≤ C * Work.Elliptic.sinCos2 θ :=
            mul_le_mul_of_nonneg_right (hC θ hθ).2 hsc0
        _ ≤ C * Work.FTS.EllipticEst.sEta θ := mul_le_mul_of_nonneg_left hsc2 hC0.le
  · have h := hwk.orthPsi z hz
    simpa only [Work.Elliptic.Fstar] using h

/-- A.e. strong measurability in `z` of the angular energy of `∂_θθΨ`. -/
theorem aesm_slice_second {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iz) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hS2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := (hS.pth).pth
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pthIter 2 Ψ p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hS2.continuousOn.pow 2
  have hcontσ : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := Work.FTS.EllipticEst.remov.ws_contOn_sEta
  have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.pthIter 2 Ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hcont2.mul hcontσ)
  have h := hjoint.integral_prod_right' (ν := volume.restrict Work.Spaces.Iθ)
  simpa only [Function.uncurry] using h

/-- Integrability in `z` of `w(z)²·∫_θ (∂_θθΨ)² σ`: the `i = 0` slot of `HkMem`. -/
theorem integrable_w_sq_thetaEnergy {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      Work.Spaces.Iz := by
  have haesm : AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (volume.restrict Work.Spaces.Iz) := by
    have hw : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
      simp only [Work.Spaces.w, div_eq_mul_inv]
      fun_prop
    exact hw.aestronglyMeasurable.mul (aesm_slice_second hwk.smooth)
  refine MeasureTheory.Integrable.mono' hwk.memB.2 haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · rw [← h0, show Work.Spaces.w (0 : ℝ) = 0 by simp [Work.Spaces.w]]
    have hz0' : (0 : ℝ) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter 2 Ψ 0 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) = 0 := by
      rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    rw [Real.norm_eq_abs, hz0', abs_zero]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ _ =>
      Work.Spaces.HkIntegrand_nonneg α k _ 0 θ
  · -- the pointwise domination by the `i = 0` slot of the integrand
    have hθint : IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.remov.ws_slot_slice
        ((Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth).pth.pth) hwk.memB 0
        (Nat.zero_le k) hz0
    have hnonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.Honest.sEta_nonneg hθ)
    have hw0 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg (mul_nonneg hw0 hnonneg)]
    calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
          rw [MeasureTheory.integral_const_mul]
      _ = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
          rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq_Iθ α _ hθ]
          ring
      _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 Ψ) z θ := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
            (hwk.memB.1 z (Set.mem_Ici.mpr hz0.le)) ?_
          exact Eventually.of_forall fun θ => by
            rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α (Work.Spaces.pthIter 2 Ψ) z θ]
            exact Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 Ψ) z θ 0
              (Nat.zero_le k)

end

/-- **The one-dimensional slice bound.**  A `C²` function on `(0, π/2)` with vanishing angular
moment, right endpoint limit `0` and finite `η`-weighted second derivative satisfies the
low-order bound with constant `20`. -/
theorem slice_low_order {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hπ : Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hval : u (Real.pi / 2) = 0)
    (hint : IntegrableOn (fun θ => u θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, u θ * Work.Elliptic.sinCos2 θ) = 0)
    (h2 : IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 + (u θ) ^ 2)
      ≤ 20 * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) := by
  obtain ⟨θ₁, hθ₁, hzero⟩ := exists_interior_zero_of_moment hsm.continuousOn hint hmom
  have hcontIcc : ContinuousOn u (Set.Icc θ₁ (Real.pi / 2)) :=
    continuousOn_Icc_of_tendsto hsm.continuousOn hπ hval hθ₁
  have hlt : θ₁ < Real.pi / 2 := hθ₁.2
  obtain ⟨θ₀, hθ₀, hcrit⟩ :=
    exists_deriv_eq_zero hlt hcontIcc (by rw [hzero, hval])
  have hd := slice_deriv_bound hsm ⟨lt_trans hθ₁.1 hθ₀.1, hθ₀.2⟩ hcrit h2
  have hv := slice_value_bound hsm hθ₁ hzero hd
  set E : ℝ := ∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2 with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact MeasureTheory.integral_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun s => (deriv (fun t => deriv u t) s) ^ 2) fun s => sq_nonneg _
  have hdb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2 ≤ (Real.pi / 2) * E :=
    fun θ hθ => by rw [hE]; exact hd θ hθ
  have hvb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ) ^ 2 ≤ (Real.pi / 2) ^ 3 * E :=
    fun θ hθ => by rw [hE]; exact hv θ hθ
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv u θ) ^ 2 + (u θ) ^ 2 ≤ ((Real.pi / 2) + (Real.pi / 2) ^ 3) * E := by
    intro θ hθ
    have h1 := hdb θ hθ
    have h2' := hvb θ hθ
    nlinarith [h1, h2']
  -- integrate over the slice
  have hvol : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal (by positivity)]
  have hkey : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 + (u θ) ^ 2)
      ≤ ((Real.pi / 2) + (Real.pi / 2) ^ 3) * E * (Real.pi / 2) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 + (u θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, ((Real.pi / 2) + (Real.pi / 2) ^ 3) * E :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => by positivity)
        (MeasureTheory.integrable_const (((Real.pi / 2) + (Real.pi / 2) ^ 3) * E))
        (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt)
    have h2 : (∫ θ in Work.Spaces.Iθ, ((Real.pi / 2) + (Real.pi / 2) ^ 3) * E)
        = ((Real.pi / 2) + (Real.pi / 2) ^ 3) * E * (Real.pi / 2) := by
      rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
      ring
    linarith [h1, h2]
  -- the unweighted energy is dominated by the weighted one
  have hEB : E ≤ ∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ := by
    rw [hE]
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun s => sq_nonneg _) h2 ?_
    exact Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ => by
      have h1 := Work.FTS.EllipticEst.Honest.one_le_sEta hθ
      nlinarith [sq_nonneg (deriv (fun t => deriv u t) θ)]
  have hB0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.Honest.sEta_nonneg hθ)
  -- the arithmetic
  have hpi : (Real.pi / 2) ^ 2 + (Real.pi / 2) ^ 4 ≤ 20 := by
    have h1 : Real.pi / 2 < 2 := by linarith [Real.pi_lt_four]
    have h2 : (0 : ℝ) < Real.pi / 2 := by positivity
    have h3 : (Real.pi / 2) ^ 2 < 4 := by nlinarith [h1, h2]
    have h4 : (Real.pi / 2) ^ 4 < 16 := by nlinarith [h3, sq_nonneg (Real.pi / 2)]
    linarith
  calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 + (u θ) ^ 2)
      ≤ ((Real.pi / 2) + (Real.pi / 2) ^ 3) * E * (Real.pi / 2) := hkey
    _ = ((Real.pi / 2) ^ 2 + (Real.pi / 2) ^ 4) * E := by ring
    _ ≤ ((Real.pi / 2) ^ 2 + (Real.pi / 2) ^ 4)
          * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) :=
        mul_le_mul_of_nonneg_left hEB (by positivity)
    _ ≤ 20 * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) :=
        mul_le_mul_of_nonneg_right hpi hB0

/-- The low-order bound, given the right endpoint limits as a hypothesis. -/
theorem low_order_le_of_tendsto {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hπ : ∀ z, 0 < z → Tendsto (fun θ => Ψ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2 + (Ψ z θ) ^ 2))
      ≤ 20 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) := by
  set A : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 *
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2 + (Ψ z θ) ^ 2) with hA
  set B : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 *
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) with hB
  have hpt : ∀ z ∈ Work.Spaces.Iz, A z ≤ 20 * B z := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · rw [← h0, hA, hB]
      simp [Work.Spaces.w]
    · obtain ⟨hsm2, hB2, hint, hmom, hval⟩ := slice_class_facts hwk hz0
      have hslice := slice_low_order hsm2 (hπ z hz0) hval hint hmom hB2
      have hEq1 : (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2 + (Ψ z θ) ^ 2)
          = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2 + (Ψ z θ) ^ 2 :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by
          simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
      have hEq2 : (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
          = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by
          simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
      have hslice' : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2 + (Ψ z θ) ^ 2)
          ≤ 20 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by
        rw [← hEq1, ← hEq2]
        exact hslice
      have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      rw [hA, hB]
      exact le_trans (mul_le_mul_of_nonneg_left hslice' hw) (le_of_eq (by ring))
  have hAnonneg : ∀ z ∈ Work.Spaces.Iz, 0 ≤ A z := by
    intro z hz
    rw [hA]
    exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
      fun θ _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hBint : IntegrableOn (fun z => 20 * B z) Work.Spaces.Iz := by
    have h := integrable_w_sq_thetaEnergy hwk
    rw [hB]
    exact h.const_mul 20
  have hmain : (∫ z in Work.Spaces.Iz, A z) ≤ ∫ z in Work.Spaces.Iz, 20 * B z :=
    MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hAnonneg) hBint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt)
  rw [MeasureTheory.integral_const_mul] at hmain
  exact hmain

theorem low_order_le {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2 + (Ψ z θ) ^ 2))
      ≤ 20 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) :=
  low_order_le_of_tendsto hwk fun z hz => slice_tendsto_pi_half hwk hz

end Work.FTS.EllipticEst.TT.ESW
