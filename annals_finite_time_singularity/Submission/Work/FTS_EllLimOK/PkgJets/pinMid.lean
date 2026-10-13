/-
Copyright: work module for the Elgindi finite-time singularity project.

# `PkgJets.pinHardy` — the angular Hardy inequality behind the pinning estimate

The pinning estimate `PkgJets.pinningBound` reduces, through the reconstruction
`∂_θ(cos θ·Ψ) = cos θ · Vop Ψ`, to the following one-dimensional weighted Hardy inequality:
with `A := cos θ·Ψ`, `A' := cos θ·Vop Ψ`, `ν := sin(2θ)^{-η}`,

`∫_θ A²·W₁ ≤ K · ∫_θ (A')²·W₂`,   `W₁ = ν/cos⁴θ`, `W₂ = ν/cos²θ`,

for `A` whose `π/2`-boundary value vanishes (`cos θ·Ψ → 0`, the *pinning*).  The proof is the
classical proof of the weighted Hardy inequality: integrate `(A²Λ)' = 2AA'Λ + A²W₁` by parts
against the primitive `Λ` of `W₁` (here the primitive `pinL x` based at the *regular* end `x`, so
that the boundary term at `x` vanishes exactly), then Cauchy–Schwarz, with the two *pointwise /
quantitative* inputs

* `Λ(θ)² ≤ C₁·W₁(θ)·W₂(θ)` (`cosWeightPrim_sq_le`), which makes the Cauchy–Schwarz factor
  `∫ (A')²Λ²/W₁` comparable with `∫ (A')²W₂`;
* `(∫_T^{π/2} cos²s·sin(2s)^η ds)·Λ(T) ≤ C₂` (`cosWeightTail_le`), which bounds the boundary term
  at the singular end `π/2` using the *vanishing* of `A` there (the pinning, through the a-priori
  bound `A(T)² ≤ 2A(T')² + 2(∫_T^{T'}cos·V)² → 2(∫_T^{T'}cos·V)²`).

The two inputs are stated here as *hypotheses* `hLamB`, `hTailB`, so that this module is
independent of the two numerical lemmas; `PkgJets.pinningBound` instantiates them.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS_EllLimOK.PkgJets.pinCs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS_EllLimOK.Reconstruct
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The weight `cos²·sin(2·)^η` is bounded by `1` on `[0,π/2]` and integrable there. -/
theorem integrableOn_cosSq_sinEta {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π / 2) :
    MeasureTheory.IntegrableOn (fun u : ℝ => (Real.cos u) ^ 2 * (Real.sin (2 * u)) ^ (Work.Spaces.eta))
      (Set.Ioc a b) := by
  refine MeasureTheory.IntegrableOn.of_bound (by simp) ?_ 1 ?_
  · exact (Measurable.mul ((Real.measurable_cos.comp measurable_id).pow_const (2 : ℕ))
      ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have huI : u ∈ Work.Spaces.Iθ := ⟨le_trans ha hu.1.le, le_trans hu.2 hb⟩
    have hsinn : 0 ≤ Real.sin (2 * u) := sin_two_nonneg_of_mem_Iθ huI
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsinn _))]
    have h1 : (Real.cos u) ^ 2 ≤ 1 := by
      nlinarith [Real.abs_cos_le_one u, sq_abs (Real.cos u), abs_nonneg (Real.cos u)]
    have h2 : (Real.sin (2 * u)) ^ (Work.Spaces.eta) ≤ 1 :=
      Real.rpow_le_one hsinn (Real.sin_le_one (2 * u)) (le_of_lt Work.Spaces.eta_pos)
    nlinarith [h1, h2, sq_nonneg (Real.cos u), Real.rpow_nonneg hsinn (Work.Spaces.eta)]

/-- **The boundary term at the singular end.**  The vanishing of `A` at `π/2` (the pinning), the
Cauchy–Schwarz step `cs_cosV_sq` and the quantitative input `hTailB` bound
`A(y)²·Λ_x(y) ≤ A(y)²·Λ(y) ≤ 2C₂·B`. -/
theorem pinA_tail_bound {Ψ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hpin : Filter.Tendsto (fun s => Real.cos s * Ψ z s) (𝓝[<] (π / 2)) (𝓝 0))
    (hR : MeasureTheory.IntegrableOn (fun θ => (pinV Ψ z θ) ^ 2 * wNu θ) Work.Spaces.Iθ)
    {C₂ : ℝ}
    (hTailB : ∀ T ∈ Set.Ioo 0 (π / 2),
      (∫ s in T..(π / 2), (Real.cos s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta)) * wLam T ≤ C₂)
    {y : ℝ} (hy : y ∈ Set.Ioo 0 (π / 2)) :
    (pinA Ψ z y) ^ 2 * wLam y ≤ 2 * C₂ * (∫ θ in Work.Spaces.Iθ, (pinV Ψ z θ) ^ 2 * wNu θ) := by
  set G : ℝ := ∫ s in y..(π / 2), (Real.cos s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta)
    with hG
  set Vt : ℝ := ∫ s in y..(π / 2), (pinV Ψ z s) ^ 2 * wNu s with hVt
  have hGioc : MeasureTheory.IntegrableOn
      (fun u : ℝ => (Real.cos u) ^ 2 * (Real.sin (2 * u)) ^ (Work.Spaces.eta))
      (Set.Ioc y (π / 2)) := integrableOn_cosSq_sinEta hy.1.le le_rfl
  have hGnn : 0 ≤ G := by
    rw [hG, intervalIntegral.integral_of_le hy.2.le]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun u hu => ?_)
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (sin_two_nonneg_of_mem_Iθ ⟨le_of_lt (lt_trans hy.1 hu.1), hu.2⟩) _)
  have hVtnn : 0 ≤ Vt := by
    rw [hVt, intervalIntegral.integral_of_le hy.2.le]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun u hu => ?_)
    exact mul_nonneg (sq_nonneg _)
      (wNu_nonneg ⟨le_of_lt (lt_trans hy.1 hu.1), hu.2⟩)
  have hR' : MeasureTheory.IntegrableOn (fun s => (pinV Ψ z s) ^ 2 * wNu s)
      (Set.Ioc y (π / 2)) :=
    hR.mono_set (fun t ht => ⟨le_of_lt (lt_trans hy.1 ht.1), ht.2⟩)
  have hC₂nn : 0 ≤ C₂ := by
    have h := hTailB y hy
    rw [← hG] at h
    nlinarith [hGnn, wLam_nonneg hy.1.le hy.2.le]
  have hVtle : Vt ≤ ∫ θ in Work.Spaces.Iθ, (pinV Ψ z θ) ^ 2 * wNu θ := by
    rw [hVt, intervalIntegral.integral_of_le (a := y) (b := π / 2) hy.2.le]
    refine MeasureTheory.setIntegral_mono_set hR ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with u hu
      exact mul_nonneg (sq_nonneg _) (wNu_nonneg hu)
    · exact Filter.Eventually.of_forall (fun u hu => ⟨le_of_lt (lt_trans hy.1 hu.1), hu.2⟩)
  -- the pinning limit of `A²`
  have hAend : Filter.Tendsto (fun s => (pinA Ψ z s) ^ 2) (𝓝[<] (π / 2)) (𝓝 0) := by
    have h := hpin.pow 2
    simpa [pinA] using h
  -- the eventual bound, from the truncated reconstruction of `A`
  have hev : ∀ᶠ y' in 𝓝[<] (π / 2),
      (pinA Ψ z y) ^ 2 ≤ 2 * (pinA Ψ z y') ^ 2 + 2 * G * Vt := by
    have hmem : Set.Ioo y (π / 2) ∈ 𝓝[<] (π / 2) := by
      have h1 : Set.Ioi y ∈ 𝓝[<] (π / 2) := nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hy.2)
      have h2 : Set.Iio (π / 2) ∈ 𝓝[<] (π / 2) := self_mem_nhdsWithin
      have h3 : Set.Ioi y ∩ Set.Iio (π / 2) ∈ 𝓝[<] (π / 2) := Filter.inter_mem h1 h2
      rwa [show Set.Ioi y ∩ Set.Iio (π / 2) = Set.Ioo y (π / 2) from rfl] at h3
    refine Filter.eventually_of_mem hmem (fun y' hy' => ?_)
    have hy'1 : y < y' := hy'.1
    have hy'2 : y' < π / 2 := hy'.2
    have hsub : Set.Icc y y' ⊆ Set.Ioo 0 (π / 2) := fun t ht =>
      ⟨lt_of_lt_of_le hy.1 ht.1, lt_of_le_of_lt ht.2 hy'2⟩
    -- the FTC for `A` on `[y,y']`
    have hFTC : pinA Ψ z y - pinA Ψ z y' = -∫ t in y..y', Real.cos t * pinV Ψ z t := by
      have hderiv : ∀ t ∈ Set.uIcc y y',
          HasDerivAt (pinA Ψ z) (Real.cos t * pinV Ψ z t) t := by
        intro t ht
        have htI : t ∈ Set.Icc y y' := Set.uIcc_of_le hy'1.le ▸ ht
        exact pinA_hasDerivAt hsm hz ⟨lt_of_lt_of_le hy.1 htI.1, lt_of_le_of_lt htI.2 hy'2⟩
      have hint : IntervalIntegrable (fun t => Real.cos t * pinV Ψ z t) volume y y' :=
        ContinuousOn.intervalIntegrable ((Real.continuous_cos.continuousOn).mul
          (continuousOn_pinV hsm hz (fun t ht => hsub (Set.uIcc_of_le hy'1.le ▸ ht))))
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      linarith [h]
    have hCS := cs_cosV_sq hsm hz hy.1 hy'2 hy'1
    have hmono1 : (∫ t in y..y', (Real.cos t) ^ 2 * (Real.sin (2 * t)) ^ (Work.Spaces.eta)) ≤ G := by
      rw [hG, intervalIntegral.integral_of_le hy.2.le, intervalIntegral.integral_of_le hy'1.le]
      refine MeasureTheory.setIntegral_mono_set hGioc ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
          (Real.sin_nonneg_of_mem_Icc
            ⟨by linarith [lt_trans hy.1 hu.1], by linarith [hu.2, hy'2, Real.pi_pos]⟩) _)
      · exact Filter.Eventually.of_forall (fun u hu => ⟨hu.1, le_trans hu.2 hy'2.le⟩)
    have hmono2 : (∫ t in y..y', (pinV Ψ z t) ^ 2 * wNu t) ≤ Vt := by
      rw [hVt, intervalIntegral.integral_of_le hy.2.le, intervalIntegral.integral_of_le hy'1.le]
      refine MeasureTheory.setIntegral_mono_set hR' ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
        exact mul_nonneg (sq_nonneg _) (wNu_nonneg ⟨le_of_lt (lt_trans hy.1 hu.1), hu.2⟩)
      · exact Filter.Eventually.of_forall (fun u hu => ⟨hu.1, le_trans hu.2 hy'2.le⟩)
    have hI2nn : 0 ≤ ∫ t in y..y', (pinV Ψ z t) ^ 2 * wNu t :=
      intervalIntegral.integral_nonneg hy'1.le (fun t ht => mul_nonneg (sq_nonneg _)
        (wNu_nonneg ⟨le_of_lt (lt_of_lt_of_le hy.1 ht.1), le_trans ht.2 hy'2.le⟩))
    have hsq : (pinA Ψ z y - pinA Ψ z y') ^ 2
        = (∫ t in y..y', Real.cos t * pinV Ψ z t) ^ 2 := by rw [hFTC]; ring
    have hstep : (pinA Ψ z y - pinA Ψ z y') ^ 2 ≤ G * Vt := by
      rw [hsq]
      exact le_trans hCS (mul_le_mul hmono1 hmono2 hI2nn hGnn)
    have hdecomp : (pinA Ψ z y) ^ 2
        ≤ 2 * (pinA Ψ z y') ^ 2 + 2 * (pinA Ψ z y - pinA Ψ z y') ^ 2 := by
      nlinarith [sq_nonneg (pinA Ψ z y - 2 * pinA Ψ z y')]
    nlinarith [hstep, hdecomp]
  have hlim : Filter.Tendsto (fun y' => 2 * (pinA Ψ z y') ^ 2 + 2 * G * Vt)
      (𝓝[<] (π / 2)) (𝓝 (2 * G * Vt)) := by
    have h1 : Filter.Tendsto (fun y' => 2 * (pinA Ψ z y') ^ 2) (𝓝[<] (π / 2)) (𝓝 (2 * 0)) :=
      hAend.const_mul 2
    have h2 : Filter.Tendsto (fun _ : ℝ => 2 * G * Vt) (𝓝[<] (π / 2)) (𝓝 (2 * G * Vt)) :=
      tendsto_const_nhds
    simpa using h1.add h2
  have hA2 : (pinA Ψ z y) ^ 2 ≤ 2 * G * Vt :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hev
  calc (pinA Ψ z y) ^ 2 * wLam y ≤ (2 * G * Vt) * wLam y :=
        mul_le_mul_of_nonneg_right hA2 (wLam_nonneg hy.1.le hy.2.le)
    _ = 2 * (G * wLam y) * Vt := by ring
    _ ≤ 2 * C₂ * Vt := by
        have h := hTailB y hy
        rw [← hG] at h
        nlinarith [h, hVtnn, mul_nonneg hGnn (wLam_nonneg hy.1.le hy.2.le)]
    _ ≤ 2 * C₂ * (∫ θ in Work.Spaces.Iθ, (pinV Ψ z θ) ^ 2 * wNu θ) :=
        mul_le_mul_of_nonneg_left hVtle (by linarith)

/-! ## The integration by parts, and the weighted Cauchy–Schwarz -/

/-- **Integration by parts on a subinterval.**  For `0 < x < y < π/2`,
`∫_x^y A²W₁ = A(y)²Λ_x(y) - 2∫_x^y A·A'·Λ_x`, where `A' = cos·Vop Ψ` and `Λ_x = pinL x`.
The primitive is based at `x`, so the boundary term at `x` vanishes exactly. -/
theorem pinA_ibp {Ψ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {x y : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) (hy : y ∈ Set.Ioo 0 (π / 2)) (hxy : x < y) :
    (∫ t in x..y, (pinA Ψ z t) ^ 2 * wOne t)
      = (pinA Ψ z y) ^ 2 * pinL x y
        - 2 * ∫ t in x..y, pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t := by
  have hsub : Set.Icc x y ⊆ Set.Ioo 0 (π / 2) := fun t ht =>
    ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  have hA : ContinuousOn (pinA Ψ z) (Set.Icc x y) := continuousOn_pinA hsm hz hsub
  have hV : ContinuousOn (pinV Ψ z) (Set.Icc x y) := continuousOn_pinV hsm hz hsub
  have hL : ContinuousOn (pinL x) (Set.Icc x y) := continuousOn_pinL_Icc hx.1 hy.2 hxy.le
  have hW : ContinuousOn wOne (Set.Icc x y) := continuousOn_wOne hsub
  have hF' : ∀ t ∈ Set.uIcc x y, HasDerivAt (fun s => (pinA Ψ z s) ^ 2 * pinL x s)
      (2 * pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t
        + (pinA Ψ z t) ^ 2 * wOne t) t := by
    intro t ht
    have htI : t ∈ Set.Icc x y := Set.uIcc_of_le hxy.le ▸ ht
    have h1 : HasDerivAt (fun s => (pinA Ψ z s) ^ 2)
        (2 * pinA Ψ z t * (Real.cos t * pinV Ψ z t)) t := by
      exact ((pinA_hasDerivAt hsm hz (hsub htI)).pow 2).congr_deriv (by ring)
    have h2 : HasDerivAt (pinL x) (wOne t) t := by
      rcases lt_or_eq_of_le htI.1 with hlt | heq
      · exact pinL_hasDerivAt hx.1 ⟨hlt, (hsub htI).2⟩
      · subst heq
        exact pinL_hasDerivAt_self hx.1 hx.2
    have h := h1.mul h2
    exact h.congr_deriv (by ring)
  have hcont : ContinuousOn (fun t => 2 * pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t
      + (pinA Ψ z t) ^ 2 * wOne t) (Set.uIcc x y) := by
    rw [Set.uIcc_of_le hxy.le]
    exact (((continuous_const.continuousOn.mul hA).mul
      (Real.continuous_cos.continuousOn.mul hV)).mul hL).add ((hA.pow 2).mul hW)
  have hint : IntervalIntegrable (fun t => 2 * pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t
      + (pinA Ψ z t) ^ 2 * wOne t) volume x y :=
    ContinuousOn.intervalIntegrable hcont
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF' hint
  have hx0 : pinL x x = 0 := by simp [pinL]
  have hsplit : (∫ t in x..y, (2 * pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t
        + (pinA Ψ z t) ^ 2 * wOne t))
      = 2 * (∫ t in x..y, pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t)
        + ∫ t in x..y, (pinA Ψ z t) ^ 2 * wOne t := by
    rw [intervalIntegral.integral_add]
    · rw [show (∫ t in x..y, 2 * pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t)
            = ∫ t in x..y, 2 * (pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t) from
          intervalIntegral.integral_congr (fun t _ => by ring)]
      rw [intervalIntegral.integral_const_mul]
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hxy.le]
      exact ((continuous_const.continuousOn.mul hA).mul
        (Real.continuous_cos.continuousOn.mul hV)).mul hL
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hxy.le]
      exact (hA.pow 2).mul hW
  rw [hsplit] at hFTC
  rw [hx0, mul_zero, sub_zero] at hFTC
  linarith [hFTC]

/-- **The weighted Cauchy–Schwarz step**: `∫_x^y |A·A'·Λ_x|` is bounded by
`(∫_x^y A²W₁)^{1/2}·(C₁·∫_x^y V²ν)^{1/2}`. -/
theorem pinA_cs_mid {Ψ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {C₁ : ℝ}
    (hLamB : ∀ θ ∈ Set.Ioo 0 (π / 2), (wLam θ) ^ 2 ≤ C₁ * wOne θ * wTwo θ)
    {x y : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) (hy : y ∈ Set.Ioo 0 (π / 2)) (hxy : x < y) :
    (∫ t in x..y, |pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t|) ^ 2
      ≤ (∫ t in x..y, (pinA Ψ z t) ^ 2 * wOne t)
        * (C₁ * ∫ t in x..y, (pinV Ψ z t) ^ 2 * wNu t) := by
  have hsub : Set.Icc x y ⊆ Set.Ioo 0 (π / 2) := fun t ht =>
    ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  -- the two continuous factors of the Cauchy–Schwarz step
  have hsqrtW : ContinuousOn (fun t => Real.sqrt (wOne t)) (Set.Icc x y) :=
    Real.continuous_sqrt.continuousOn.comp (continuousOn_wOne hsub)
      (fun t ht => (wOne_pos (hsub ht)).le)
  have hu : ContinuousOn (fun t => |pinA Ψ z t| * Real.sqrt (wOne t)) (Set.Icc x y) :=
    ((continuousOn_pinA hsm hz hsub).abs).mul hsqrtW
  have hv : ContinuousOn (fun t => |Real.cos t * pinV Ψ z t| * pinL x t / Real.sqrt (wOne t))
      (Set.Icc x y) := by
    refine (((Real.continuous_cos.continuousOn.mul (continuousOn_pinV hsm hz hsub)).abs).mul
      (continuousOn_pinL_Icc hx.1 hy.2 hxy.le)).div hsqrtW ?_
    intro t ht
    exact ne_of_gt (Real.sqrt_pos.mpr (wOne_pos (hsub ht)))
  have hCS := cs_subinterval hxy hu hv
  have hu2 : (∫ t in x..y, (|pinA Ψ z t| * Real.sqrt (wOne t)) ^ 2)
      = ∫ t in x..y, (pinA Ψ z t) ^ 2 * wOne t := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have htI : t ∈ Set.Icc x y := Set.uIcc_of_le hxy.le ▸ ht
    rw [mul_pow, sq_abs, Real.sq_sqrt (wOne_pos (hsub htI)).le]
  have huv : (∫ t in x..y, (|pinA Ψ z t| * Real.sqrt (wOne t))
        * (|Real.cos t * pinV Ψ z t| * pinL x t / Real.sqrt (wOne t)))
      = ∫ t in x..y, |pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t| := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have htI : t ∈ Set.Icc x y := Set.uIcc_of_le hxy.le ▸ ht
    have hwpos : 0 < wOne t := wOne_pos (hsub htI)
    have hs : Real.sqrt (wOne t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hwpos)
    have hLnn : 0 ≤ pinL x t := pinL_nonneg hx.1.le htI.1 (hsub htI).2.le
    have hLX : (|pinA Ψ z t| * Real.sqrt (wOne t))
          * (|Real.cos t * pinV Ψ z t| * pinL x t / Real.sqrt (wOne t))
        = |pinA Ψ z t| * |Real.cos t * pinV Ψ z t| * pinL x t := by
      field_simp
    have hRX : |pinA Ψ z t * (Real.cos t * pinV Ψ z t) * pinL x t|
        = |pinA Ψ z t| * |Real.cos t * pinV Ψ z t| * pinL x t := by
      rw [abs_mul, abs_mul, abs_of_nonneg hLnn]
    rw [hLX, hRX]
  -- the pointwise bound on the second factor
  have hpt : ∀ t ∈ Set.Icc x y,
      (|Real.cos t * pinV Ψ z t| * pinL x t / Real.sqrt (wOne t)) ^ 2
        ≤ C₁ * ((pinV Ψ z t) ^ 2 * wNu t) := by
    intro t ht
    have htIoo : t ∈ Set.Ioo 0 (π / 2) := hsub ht
    have hW1 : 0 < wOne t := wOne_pos htIoo
    have hLam : pinL x t ≤ wLam t := pinL_le_wLam hx.1.le ht.1 htIoo
    have hLnn : 0 ≤ pinL x t := pinL_nonneg hx.1.le ht.1 htIoo.2.le
    have hsq : (pinL x t) ^ 2 ≤ (wLam t) ^ 2 := by nlinarith
    have h1 : (pinL x t) ^ 2 ≤ C₁ * (wOne t * wTwo t) := by
      have := le_trans hsq (hLamB t htIoo); nlinarith
    have hLHS : (|Real.cos t * pinV Ψ z t| * pinL x t / Real.sqrt (wOne t)) ^ 2
        = (Real.cos t * pinV Ψ z t) ^ 2 * (pinL x t) ^ 2 / wOne t := by
      rw [div_pow, mul_pow, sq_abs, Real.sq_sqrt hW1.le]
    have hcos : Real.cos t ≠ 0 := ne_of_gt (cos_pos_of_mem_Ioo htIoo)
    have hc2 : (Real.cos t) ^ 2 * wTwo t = wNu t := by
      rw [wTwo]
      field_simp
    rw [hLHS, div_le_iff₀ hW1]
    refine le_trans (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)) (le_of_eq ?_)
    rw [mul_pow]
    rw [show (Real.cos t) ^ 2 * (pinV Ψ z t) ^ 2 * (C₁ * (wOne t * wTwo t))
        = C₁ * ((pinV Ψ z t) ^ 2 * wNu t) * wOne t by
      rw [← hc2]; ring]
  have hv2 : (∫ t in x..y, (|Real.cos t * pinV Ψ z t| * pinL x t / Real.sqrt (wOne t)) ^ 2)
      ≤ C₁ * ∫ t in x..y, (pinV Ψ z t) ^ 2 * wNu t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hxy.le ?_ ?_ hpt
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hxy.le]
      exact hv.pow 2
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hxy.le]
      exact continuous_const.continuousOn.mul (((continuousOn_pinV hsm hz hsub).pow 2).mul
        (continuousOn_wNu hsub))
  have hA2nn : 0 ≤ ∫ t in x..y, (pinA Ψ z t) ^ 2 * wOne t :=
    intervalIntegral.integral_nonneg hxy.le (fun t ht =>
      mul_nonneg (sq_nonneg (pinA Ψ z t)) (wOne_pos (hsub ⟨ht.1, ht.2⟩)).le)
  rw [hu2, huv] at hCS
  exact le_trans hCS (mul_le_mul_of_nonneg_left hv2 hA2nn)

end Work.FTS_EllLimOK.PkgJets
