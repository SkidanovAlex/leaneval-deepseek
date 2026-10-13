/-
# The angular-transport coercivity in the interior class `SmoothQuad`

`Work.Coercivity.wip_TrV_ge` proves that the angular transport pairing
`⟨−(3/(1+z)) D_θv, v⟩_{w²sin^{-γ}}` is bounded below by `−(3α/10)⟨v,v⟩_{w²sin^{-γ}}`, from the
analytic package `Spaces.SmoothNbhd` (analyticity) and the `α`-specialised one-dimensional
integration by parts `Work.Coercivity.slice_ibp`.

This file re-proves the same estimate in the interior class `Work.FTS.LocData.SmoothQuad`
(`C^∞` on the open quadrant) and for an **arbitrary** exponent `β` of the angular weight
`Rho β = w²·sin(2θ)^{-β}`:

  `wip (Rho β) (Transport u) u ≤ 3|β - 1| · wip (Rho β) u u`.

The estimate is sharp exactly because `β = η = 99/100` gives `|β-1| = 1/100` and
`β = γ = 1 + α/10` gives `α/10`.  The proof is the one-dimensional integration by parts
`slice_ibp_gen_Q` at fixed `z > 0` (the boundary term `sin(2θ)^{1-β}u²` vanishes at `0⁺` and
`(π/2)⁻`), Fubini, and the pointwise bound `|cos(2θ)/(1+z)| ≤ 1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.Coercivity.slice_ibp_gen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Differentiability of the `θ`-slice of a `SmoothQuad` function at an interior angle. -/
theorem differentiableAt_slice_theta_Q {v : Fn} (hv : Work.FTS.LocData.SmoothQuad v)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun θ' => v z θ') θ :=
  ((hv.curry_θ (by simp only [Set.mem_Ioi]; linarith)).differentiableOn
    Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-- The derivative of the angular boundary term `ψ θ = sin(2θ)^{-(β-1)}·v(z,θ)²` at an
interior angle, in the form adapted to the two integrands of `slice_ibp_gen_Q`.  This is
`Work.Coercivity.slice_psi_hasDerivAt_gen` with `SmoothQuad` in place of `SmoothNbhd`. -/
theorem slice_psi_hasDerivAt_gen_Q (β : ℝ) (v : Fn) (hv : Work.FTS.LocData.SmoothQuad v)
    (z θ : ℝ) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hsin : 0 < Real.sin (2 * θ)) :
    HasDerivAt (fun θ' => (Real.sin (2 * θ')) ^ (-(β - 1)) * (v z θ') ^ 2)
      (2 * ((Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth v z θ * v z θ)
        - (2 * (β - 1)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2)) θ := by
  have hdiff : DifferentiableAt ℝ (fun θ' => v z θ') θ :=
    differentiableAt_slice_theta_Q hv hz hθ
  have hu : HasDerivAt (fun θ' => v z θ') (Work.Spaces.pth v z θ) θ := hdiff.hasDerivAt
  have hs2 : HasDerivAt (fun θ' => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    convert h using 1
    · ext θ'; simp [Function.comp]
    · ring
  have hsinne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsin
  have hφ : HasDerivAt (fun θ' => (Real.sin (2 * θ')) ^ (-(β - 1)))
      ((-(β - 1)) * (Real.sin (2 * θ)) ^ (-(β - 1) - 1)
        * (2 * Real.cos (2 * θ))) θ := by
    have h := (Real.hasDerivAt_rpow_const (x := Real.sin (2 * θ))
      (p := -(β - 1)) (Or.inl hsinne)).comp θ hs2
    convert h using 1
    · ext θ'; simp [Function.comp]
  have hu2 : HasDerivAt (fun θ' => (v z θ') ^ 2) (2 * (v z θ) * Work.Spaces.pth v z θ) θ := by
    have h := (hasDerivAt_pow 2 (v z θ)).comp θ hu
    convert h using 1
    · ext θ'; simp [Function.comp]
    · simp only [Nat.reduceSub, pow_one]; ring
  have hψ := hφ.mul hu2
  have key : ( (-(β - 1)) * Real.sin (2 * θ) ^ (-(β - 1) - 1)
          * (2 * Real.cos (2 * θ)) * (v z θ) ^ 2
        + Real.sin (2 * θ) ^ (-(β - 1)) * (2 * (v z θ) * Work.Spaces.pth v z θ) )
      = 2 * ((Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth v z θ * v z θ)
        - (2 * (β - 1)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2) := by
    have hA : Real.sin (2 * θ) ^ (-(β - 1))
        = Real.sin (2 * θ) ^ (-β) * Real.sin (2 * θ) := by
      rw [show -(β - 1) = -β + 1 by ring, Real.rpow_add hsin, Real.rpow_one]
    have hB : Real.sin (2 * θ) ^ (-(β - 1) - 1)
        = Real.sin (2 * θ) ^ (-β) := by
      rw [show -(β - 1) - 1 = -β by ring]
    rw [hA, hB, Work.Spaces.Dth]
    ring
  rw [key] at hψ
  exact hψ

/-- **The one-dimensional angular integration by parts** for the weight `sin(2θ)^{-β}`, in the
interior class: `∫_θ sin(2θ)^{-β} D_θv · v = (β-1) ∫_θ cos(2θ) sin(2θ)^{-β} v²`. -/
theorem slice_ibp_gen_Q (β : ℝ) (v : Fn) (hv : Work.FTS.LocData.SmoothQuad v)
    (hvan : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - β) * (v z θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hvan2 : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - β) * (v z θ) ^ 2)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0))
    (z : ℝ) (hz : 0 < z)
    (hI : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth v z θ * v z θ) Work.Spaces.Iθ)
    (hK : MeasureTheory.IntegrableOn
      (fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2) Work.Spaces.Iθ) :
    ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth v z θ * v z θ
      = (β - 1) * ∫ θ in Work.Spaces.Iθ,
          Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2 := by
  have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hpi2pos : (0 : ℝ) < Real.pi / 2 := by positivity
  set g : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth v z θ * v z θ with hg
  set k : ℝ → ℝ := fun θ =>
    Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2 with hk
  have hIg : MeasureTheory.IntegrableOn g (Set.Icc 0 (Real.pi / 2)) := hI
  have hKg : MeasureTheory.IntegrableOn k (Set.Icc 0 (Real.pi / 2)) := hK
  have hgi : IntervalIntegrable g volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr (hIg.mono_set Set.Ioc_subset_Icc_self)
  have hki : IntervalIntegrable k volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr (hKg.mono_set Set.Ioc_subset_Icc_self)
  have hvan' : ∀ z, 0 < z → Filter.Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (-(β - 1)) * (v z θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := fun z hz => by
    simpa only [neg_sub] using hvan z hz
  have hvan2' : ∀ z, 0 < z → Filter.Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (-(β - 1)) * (v z θ) ^ 2)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := fun z hz => by
    simpa only [neg_sub] using hvan2 z hz
  have hpsi_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ => (Real.sin (2 * θ)) ^ (-(β - 1)) * (v z θ) ^ 2)
        (2 * ((Real.sin (2 * x)) ^ (-β) * Work.Spaces.Dth v z x * v z x)
          - (2 * (β - 1)) *
              (Real.cos (2 * x) * (Real.sin (2 * x)) ^ (-β) * (v z x) ^ 2)) x := by
    intro x hx
    have hsin : 0 < Real.sin (2 * x) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
    exact slice_psi_hasDerivAt_gen_Q β v hv z x hz hx hsin
  have hf'int : IntervalIntegrable (fun y => 2 * g y - (2 * (β - 1)) * k y)
      volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr
      (((hIg.mono_set Set.Ioc_subset_Icc_self).const_mul 2).sub
        ((hKg.mono_set Set.Ioc_subset_Icc_self).const_mul (2 * (β - 1))))
  have hFTC0 : ∫ y in (0 : ℝ)..(Real.pi / 2), (2 * g y - (2 * (β - 1)) * k y) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := 0) (b := Real.pi / 2)
      hpi2pos
      (f := fun θ => (Real.sin (2 * θ)) ^ (-(β - 1)) * (v z θ) ^ 2)
      (f' := fun y => 2 * g y - (2 * (β - 1)) * k y)
      hpsi_deriv hf'int (hvan' z hz) (hvan2' z hz)
    simpa using h
  have hsplit : ∫ y in (0 : ℝ)..(Real.pi / 2), (2 * g y - (2 * (β - 1)) * k y)
      = 2 * (∫ y in (0 : ℝ)..(Real.pi / 2), g y)
        - (2 * (β - 1)) * (∫ y in (0 : ℝ)..(Real.pi / 2), k y) := by
    rw [intervalIntegral.integral_sub (hgi.const_mul 2) (hki.const_mul (2 * (β - 1))),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hg_eq : ∫ y in Work.Spaces.Iθ, g y = ∫ y in (0 : ℝ)..(Real.pi / 2), g y := by
    rw [Work.Spaces.Iθ]
    exact ((intervalIntegral.integral_of_le hpi2).trans
      (MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)))).symm
  have hk_eq : ∫ y in Work.Spaces.Iθ, k y = ∫ y in (0 : ℝ)..(Real.pi / 2), k y := by
    rw [Work.Spaces.Iθ]
    exact ((intervalIntegral.integral_of_le hpi2).trans
      (MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)))).symm
  have hmain : ∫ y in (0 : ℝ)..(Real.pi / 2), g y
      = (β - 1) * ∫ y in (0 : ℝ)..(Real.pi / 2), k y := by
    have h2 : 2 * (∫ y in (0 : ℝ)..(Real.pi / 2), g y)
        = 2 * ((β - 1) * ∫ y in (0 : ℝ)..(Real.pi / 2), k y) := by
      rw [hsplit] at hFTC0
      linarith
    exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) h2
  rw [hg_eq, hk_eq]
  exact hmain

/-- The `cos(2θ)·sin(2θ)^{-β}·v²` slice is integrable as soon as the `w²·sin(2θ)^{-β}·v²`
slice is (the constant `w(z)² ≠ 0` can be divided out and `cos(2·)` is bounded on the compact
interval `Iθ`). -/
theorem cos_sin_integrable_Q (β : ℝ) (v : Fn) {z : ℝ} (hz : 0 < z)
    (hC : MeasureTheory.IntegrableOn (fun θ => Rho β z θ * (v z θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2)
      Work.Spaces.Iθ := by
  have hw : Work.Spaces.w z ≠ 0 := by
    unfold Work.Spaces.w
    positivity
  have hg : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn] at hC ⊢
    have hrw : (fun θ => Rho β z θ * (v z θ) ^ 2)
        = fun θ => (Work.Spaces.w z) ^ 2 *
            ((Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2) := by
      funext θ
      simp only [Rho, sig]
      ring
    rw [hrw] at hC
    exact (MeasureTheory.integrable_const_mul_iff
      (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hw)) _).mp hC
  have hcont : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) Work.Spaces.Iθ :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hh := MeasureTheory.IntegrableOn.continuousOn_mul hcont hg isCompact_Icc
  simpa [mul_assoc] using hh

/-- **The angular transport pairing is bounded below** by `3|β-1|` times the `β`-weighted
energy, in the interior class `SmoothQuad`. -/
theorem wip_transport_le_Q (β : ℝ) (u : Fn) (hu : Work.FTS.LocData.SmoothQuad u)
    (hvan0 : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - β) * (u z θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hvan2 : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - β) * (u z θ) ^ 2)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ
        / (1 + z))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (Rho β) (Work.Coercivity.Transport u) u
      ≤ (3 * |β - 1|) * Work.Coercivity.wip (Rho β) u u := by
  -- the two integrands on the product space
  let Gp : ℝ × ℝ → ℝ := fun p =>
    Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-β) * Work.Spaces.Dth u p.1 p.2 * u p.1 p.2
      / (1 + p.1)
  let Bp : ℝ × ℝ → ℝ := fun p =>
    Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-β) * (u p.1 p.2) ^ 2
  have hvol : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hGp : MeasureTheory.Integrable Gp
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hvol]; exact hint
  have hBp : MeasureTheory.Integrable Bp
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hvol]; exact hint2
  have hGslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Gp (z, θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hGp.prod_right_ae
  have hBslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Bp (z, θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hBp.prod_right_ae
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [MeasureTheory.ae_restrict_iff (p := fun z => 0 < z) measurableSet_Ioi,
      MeasureTheory.ae_iff]
    have hset : {z : ℝ | ¬ (z ∈ Work.Spaces.Iz → 0 < z)} = {0} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Work.Spaces.Iz, Set.mem_Ici, not_imp]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) h1
      · rintro rfl; exact ⟨le_refl 0, lt_irrefl 0⟩
    rw [hset, Real.volume_singleton]
  -- the slice-wise inequality: `∫_θ Gp ≤ |β-1| ∫_θ Bp`
  have hkey : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ |β - 1| * (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    filter_upwards [hGslice, hBslice, hzpos] with z hGz hBz hzp
    have hwne : Work.Spaces.w z ^ 2 ≠ 0 := by
      have : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      positivity
    -- the core integrabilities, obtained from the two product integrabilities
    have hBcore : MeasureTheory.Integrable
        (fun θ => (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hBz' : MeasureTheory.Integrable
          (fun θ => Work.Spaces.w z ^ 2 * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        refine hBz.congr (Filter.Eventually.of_forall (fun θ => ?_))
        dsimp only [Bp]; ring
      have h2 := hBz'.const_mul ((Work.Spaces.w z ^ 2))⁻¹
      refine h2.congr (Filter.Eventually.of_forall (fun θ => ?_))
      show (Work.Spaces.w z ^ 2)⁻¹ *
          (Work.Spaces.w z ^ 2 * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
        = (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2
      rw [inv_mul_cancel_left₀ hwne]
    have hKcore : MeasureTheory.Integrable
        (fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      cos_sin_integrable_Q β u hzp hBz
    have hIcore : MeasureTheory.Integrable
        (fun θ => (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine (hGz.const_mul ((1 + z) / (Work.Spaces.w z) ^ 2)).congr
        (Filter.Eventually.of_forall (fun θ => ?_))
      dsimp only [Gp]
      have hw : Work.Spaces.w z ≠ 0 := by
        rw [Work.Spaces.w]; exact div_ne_zero (by positivity) (by positivity)
      have h1z : (1 : ℝ) + z ≠ 0 := by positivity
      field_simp
    -- the one-dimensional integration by parts
    have hslice := slice_ibp_gen_Q β u hu hvan0 hvan2 z hzp hIcore hKcore
    -- the `θ`-independent factor `w z ^ 2/(1+z)` out of the slice integrals
    have h1 : (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (∫ θ, (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [show (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = ∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
              ((Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) from
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun θ => by dsimp only [Gp]; ring))]
      rw [MeasureTheory.integral_const_mul]
    have hGval : (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (β - 1) * (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [h1, hslice]
      rw [show ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((β - 1) * (∫ θ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)))
          = (β - 1) * (((Work.Spaces.w z) ^ 2 / (1 + z)) *
              (∫ θ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) from by ring]
      rw [MeasureTheory.integral_const_mul]
    -- the three integral comparisons
    have hc1 : (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hintL : MeasureTheory.Integrable (fun θ => ((Work.Spaces.w z) ^ 2 / (1 + z)) *
          (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (hKcore.const_mul ((Work.Spaces.w z) ^ 2 / (1 + z))).congr
          (Filter.Eventually.of_forall (fun θ => by ring_nf))
      refine MeasureTheory.integral_mono_ae hintL hBz ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      have hsin : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])
      have hA : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _)) (sq_nonneg _)
      have hcoef : Real.cos (2 * θ) / (1 + z) ≤ 1 := by
        have h1z : 0 < 1 + z := by linarith [hzp]
        rw [div_le_iff₀ h1z]
        linarith [Real.cos_le_one (2 * θ)]
      dsimp only [Bp]
      calc ((Work.Spaces.w z) ^ 2 / (1 + z)) *
              (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
          = (Real.cos (2 * θ) / (1 + z)) *
              ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2) := by
            ring
        _ ≤ 1 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2) :=
            mul_le_mul_of_nonneg_right hcoef hA
        _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 := one_mul _
    have hc2 : (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hintL : MeasureTheory.Integrable (fun θ => ((Work.Spaces.w z) ^ 2 / (1 + z)) *
          ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (hBcore.const_mul ((Work.Spaces.w z) ^ 2 / (1 + z))).congr
          (Filter.Eventually.of_forall (fun θ => by ring))
      refine MeasureTheory.integral_mono_ae hintL hBz ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      have hsin : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])
      have hX : 0 ≤ (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hsin _) (sq_nonneg _)
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hcoef : (Work.Spaces.w z) ^ 2 / (1 + z) ≤ (Work.Spaces.w z) ^ 2 := by
        have h1z : 0 < 1 + z := by linarith [hzp]
        rw [div_le_iff₀ h1z]; nlinarith [hzp, hw2]
      dsimp only [Bp]
      calc ((Work.Spaces.w z) ^ 2 / (1 + z)) * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
          ≤ (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2) :=
            mul_le_mul_of_nonneg_right hcoef hX
        _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 := by ring
    have hc3 : -((∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hneg : (∫ θ, -(((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = -((∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
        simpa using MeasureTheory.integral_neg
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
      rw [← hneg]
      have hintL : MeasureTheory.Integrable (fun θ => -(((Work.Spaces.w z) ^ 2 / (1 + z)) *
          ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ((hBcore.const_mul ((Work.Spaces.w z) ^ 2 / (1 + z))).neg).congr
          (Filter.Eventually.of_forall (fun θ => by simp only [Pi.neg_apply]))
      have hintR : MeasureTheory.Integrable (fun θ => ((Work.Spaces.w z) ^ 2 / (1 + z)) *
          (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (hKcore.const_mul ((Work.Spaces.w z) ^ 2 / (1 + z))).congr
          (Filter.Eventually.of_forall (fun θ => by ring_nf))
      refine MeasureTheory.integral_mono_ae hintL hintR ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      have hsin : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])
      have hc : 0 ≤ (Work.Spaces.w z) ^ 2 / (1 + z) :=
        div_nonneg (sq_nonneg _) (by linarith [hzp])
      have hX : 0 ≤ (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hsin _) (sq_nonneg _)
      have hcos : -1 ≤ Real.cos (2 * θ) := Real.neg_one_le_cos (2 * θ)
      calc -(((Work.Spaces.w z) ^ 2 / (1 + z)) * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          = (Work.Spaces.w z) ^ 2 / (1 + z) *
              (-((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)) := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 / (1 + z) *
              (Real.cos (2 * θ) * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ hc
            have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2
                * (1 + Real.cos (2 * θ)) := mul_nonneg hX (by linarith)
            nlinarith [h1]
        _ = (Work.Spaces.w z) ^ 2 / (1 + z) *
              (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2) := by ring
    -- combine, by cases on `β ≥ 1`
    rcases le_total (1 : ℝ) β with hb | hb
    · have hb1 : 0 ≤ β - 1 := by linarith
      have habs : |β - 1| = β - 1 := abs_of_nonneg hb1
      rw [hGval, habs]
      exact mul_le_mul_of_nonneg_left hc1 hb1
    · have hb1 : β - 1 ≤ 0 := by linarith
      have habs : |β - 1| = -(β - 1) := abs_of_nonpos hb1
      rw [hGval, habs]
      have hstep : (β - 1) * (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ≤ (β - 1) * (-(∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
        mul_le_mul_of_nonpos_left hc3 hb1
      have hstep2 : (β - 1) * (-(∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)))
          ≤ (-(β - 1)) * (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        nlinarith [hc2, hb1]
      linarith [hstep, hstep2]
  -- integrate over `z`
  have hFz : MeasureTheory.Integrable
      (fun z => ∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hGp.integral_prod_left
  have hBzI : MeasureTheory.Integrable
      (fun z => ∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hBp.integral_prod_left
  have hmono : (∫ z, (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ (∫ z, |β - 1| *
          (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    MeasureTheory.integral_mono_ae hFz (hBzI.const_mul _) hkey
  have hmono2 : (∫ z, |β - 1| *
          (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      = |β - 1| *
          (∫ z, (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    MeasureTheory.integral_const_mul _ _
  have hAG : (∫ p, Gp p
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = (∫ z, (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    MeasureTheory.integral_prod Gp hGp
  have hAB : (∫ p, Bp p
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = (∫ z, (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    MeasureTheory.integral_prod Bp hBp
  have hAGle : (∫ p, Gp p
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ |β - 1| * (∫ p, Bp p
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [hAG, hAB]
    linarith [hmono, hmono2]
  -- identify the two `wip`s with the product integrals
  have h2' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ *
        (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β)))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hint2.congr (Filter.Eventually.of_forall (fun p => by
      dsimp only [Function.uncurry]; ring))
  have hIntB : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * Rho β z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h2'.congr (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [Function.uncurry, Rho, sig]
  have hwipB : Work.Coercivity.wip (Rho β) u u
      = (∫ p, Bp p
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [Work.Coercivity.wip_eq_integral_prod (Rho β) u u hIntB]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [Bp, Rho, sig]
    ring
  have hA' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.Transport u z θ * u z θ * Rho β z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hint.const_mul 3).congr (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [Function.uncurry, Work.Coercivity.Transport, Rho, sig]
    ring
  have hwipA : Work.Coercivity.wip (Rho β) (Work.Coercivity.Transport u) u
      = 3 * (∫ p, Gp p
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [Work.Coercivity.wip_eq_integral_prod (Rho β) (Work.Coercivity.Transport u) u hA']
    rw [show (∫ p, Work.Coercivity.Transport u p.1 p.2 * u p.1 p.2 * Rho β p.1 p.2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        = ∫ p, 3 * Gp p
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) from
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun p => by
          dsimp only [Gp, Work.Coercivity.Transport, Rho, sig]; ring))]
    rw [MeasureTheory.integral_const_mul]
  rw [hwipB, hwipA]
  linarith [hAGle]

end Work.FTS.CoercivityFix.Coer1
