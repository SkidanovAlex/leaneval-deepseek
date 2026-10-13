import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Coer1.thetaIBP
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1600000

/-- Differentiability of the `θ`-slice of a `SmoothOpen` function at an interior angle.  This is
the `SmoothOpen` analogue of `Work.FTS.CoercivityFix.Coer1.differentiableAt_slice_theta_Q`. -/
theorem differentiableAt_slice_theta_O {v : Fn} (hv : Work.FTS.EllipticEst.SmoothOpen v)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun θ' => v z θ') θ :=
  ((hv.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-- The derivative of the angular boundary term `ψ θ = sin(2θ)^{-(β-1)}·v(z,θ)²` at an
interior angle, where `sin(2θ) > 0` so that the power is genuinely differentiable.  The
derivative is written in the form `2·(sin(2θ)^{-β} D_θ v · v) - 2(β-1)·(cos(2θ) sin(2θ)^{-β} v²)`
adapted to the two integrands of `slice_ibp_gen_O`.  This is
`Work.FTS.CoercivityFix.Coer1.slice_psi_hasDerivAt_gen_Q` with `SmoothOpen` in place of
`SmoothQuad`. -/
theorem slice_psi_hasDerivAt_gen_O (β : ℝ) (v : Fn) (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (z θ : ℝ) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hsin : 0 < Real.sin (2 * θ)) :
    HasDerivAt (fun θ' => (Real.sin (2 * θ')) ^ (-(β - 1)) * (v z θ') ^ 2)
      (2 * ((Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth v z θ * v z θ)
        - (2 * (β - 1)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2)) θ := by
  have hdiff : DifferentiableAt ℝ (fun θ' => v z θ') θ :=
    differentiableAt_slice_theta_O hv hz hθ
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
open-quadrant class `SmoothOpen`: for `z > 0`,
`∫_θ sin(2θ)^{-β} D_θv · v = (β-1) ∫_θ cos(2θ) sin(2θ)^{-β} v²`,
the boundary term `sin(2θ)^{1-β}v²` vanishing at `0⁺` and `(π/2)⁻`. -/
theorem slice_ibp_gen_O (β : ℝ) (v : Work.FTS.Galerkin.Fn)
    (hv : Work.FTS.EllipticEst.SmoothOpen v)
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
    exact slice_psi_hasDerivAt_gen_O β v hv z x hz hx hsin
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

end Work.FTS.StrongEps.EpsE4Thr
