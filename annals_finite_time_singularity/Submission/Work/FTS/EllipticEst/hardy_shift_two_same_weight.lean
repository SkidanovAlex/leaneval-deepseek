import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.half_pi_sin_hardy
import Submission.Work.Elliptic.sharp_hardy_sin_two
import Submission.Work.Elliptic.sin_weight_integrable
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-- **Sharp Hardy on `[0,π/2]` with the shift `2`, correction against the *same* weight.**

For `0 ≤ η < 1` there is `C` with: for every `f : ℝ → ℝ` of class `C¹` on `[0,π/2]` with
`f 0 = 0`, `f (π/2) = 0`,

  `∫_0^{π/2} f² / sin(2θ)^{2+η} ≤ 1/(1+η)² ∫_0^{π/2} (f')² / sin(2θ)^η + C ∫_0^{π/2} f² / sin(2θ)^η`.

The constant `1/(1+η)²` is *sharp*: for the power weight it is the classical sharp value
`4/(1+η)²` on the half-line, and the substitution `sin(2θ) ≈ 2θ` (`sin(2θ) = 2θ` to first order)
contributes the factor `2^{-(2+η)}·2^{η} = 1/4`.  The correction term carries the *same* weight
`sin(2θ)^{-η}` as the derivative term (not the unweighted `H¹`-norm as in
`Work.Elliptic.sharp_hardy_sin_two`).

Derivation from what is already in the repository: apply the proved
`Work.Elliptic.half_sharp_hardy` (exactly this inequality integrated over `(0,π/4)`, with the
constant `1/(1+η)²` and the correction `C ∫ f² sin(2θ)^{-η}`) to `f`, and again to the reflected
function `f̃ θ = f (π/2 - θ)`; since `sin(2(π/2-θ)) = sin(2θ)`, `f̃ 0 = f (π/2) = 0` and
`f̃ (π/2) = f 0 = 0`, the two halves add up to the full interval `Iθ = Icc 0 (π/2)`. -/
theorem hardy_shift_two_same_weight (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, f θ ^ 2 / (Real.sin (2 * θ)) ^ (2 + η))
        ≤ 1 / (η + 1) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 / (Real.sin (2 * θ)) ^ η)
          + C * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 / (Real.sin (2 * θ)) ^ η) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.Elliptic.half_sharp_hardy hη0 hη1
  refine ⟨C0, hC0pos, fun f hf hf0 hfpi => ?_⟩
  have keyI : ∀ h : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, h θ) = ∫ θ in (0:ℝ)..(Real.pi/2), h θ := by
    intro h
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)]
  have hsin_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2*θ) := by
    intro θ hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hdiv : ∀ (a : ℝ → ℝ),
      (∫ θ in Work.Spaces.Iθ, a θ / (Real.sin (2*θ))^(2+η))
        = ∫ θ in Work.Spaces.Iθ, a θ * (Real.sin (2*θ))^(-(2+η)) := by
    intro a
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro θ hθ
    show a θ / (Real.sin (2*θ))^(2+η) = a θ * (Real.sin (2*θ))^(-(2+η))
    rw [div_eq_mul_inv, Real.rpow_neg (hsin_nn θ hθ) (2+η)]
  have hdiv2 : ∀ (a : ℝ → ℝ),
      (∫ θ in Work.Spaces.Iθ, a θ / (Real.sin (2*θ))^η)
        = ∫ θ in Work.Spaces.Iθ, a θ * (Real.sin (2*θ))^(-η) := by
    intro a
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro θ hθ
    show a θ / (Real.sin (2*θ))^η = a θ * (Real.sin (2*θ))^(-η)
    rw [div_eq_mul_inv, Real.rpow_neg (hsin_nn θ hθ) η]
  rw [hdiv (fun θ => f θ ^ 2), hdiv2 (fun θ => (deriv f θ) ^ 2), hdiv2 (fun θ => f θ ^ 2)]
  simp only [keyI]
  -- integrability of the five weighted integrands, and the two halves
  obtain ⟨hIL, hIN, hIP, hIM, hIQ⟩ := Work.Elliptic.sin_weight_integrable hη0 hη1 hf hf0 hfpi
  have hsub1 : Set.uIcc (0:ℝ) (Real.pi/4) ⊆ Set.uIcc 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/4),
        Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)]
    exact Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])
  have hsub2 : Set.uIcc (Real.pi/4) (Real.pi/2) ⊆ Set.uIcc 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : Real.pi/4 ≤ Real.pi/2),
        Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)]
    exact Set.Icc_subset_Icc (by positivity) le_rfl
  have hIL1 := hIL.mono_set hsub1
  have hIL2 := hIL.mono_set hsub2
  have hIN1 := hIN.mono_set hsub1
  have hIN2 := hIN.mono_set hsub2
  have hIP1 := hIP.mono_set hsub1
  have hIP2 := hIP.mono_set hsub2
  have hleft := hC0 f hf hf0 hfpi
  -- right half by reflection
  set g : ℝ → ℝ := fun φ => f (Real.pi/2 - φ) with hg_def
  have hg : ContDiffOn ℝ 1 g (Set.Icc 0 (Real.pi/2)) := by
    have h1 : ContDiffOn ℝ 1 (fun φ : ℝ => Real.pi/2 - φ) (Set.Icc 0 (Real.pi/2)) := by fun_prop
    have h2 : Set.MapsTo (fun φ : ℝ => Real.pi/2 - φ) (Set.Icc 0 (Real.pi/2)) (Set.Icc 0 (Real.pi/2)) := by
      intro x hx; simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.2, Real.pi_pos], by linarith [hx.1]⟩
    have := hf.comp h1 h2
    simpa only [hg_def, Function.comp_def] using this
  have hg0 : g 0 = 0 := by rw [hg_def]; simpa using hfpi
  have hgpi : g (Real.pi/2) = 0 := by rw [hg_def]; simpa using hf0
  have hright_raw := hC0 g hg hg0 hgpi
  have hr1 : (∫ φ in (0:ℝ)..(Real.pi/4), g φ ^ 2 * (Real.sin (2*φ)) ^ (-(2+η)))
      = ∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)) := by
    have hcomp := intervalIntegral.integral_comp_sub_left (fun θ => f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η))) (Real.pi/2)
        (a := (0:ℝ)) (b := Real.pi/4)
    rw [show Real.pi/2 - Real.pi/4 = Real.pi/4 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro φ hφ
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/4)] at hφ
    simp only [hg_def]
    rw [show 2*(Real.pi/2 - φ) = Real.pi - 2*φ by ring, Real.sin_pi_sub]
  have hr2 : (∫ φ in (0:ℝ)..(Real.pi/4), (deriv g φ) ^ 2 * (Real.sin (2*φ)) ^ (-η))
      = ∫ θ in (Real.pi/4)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η) := by
    have hcomp := intervalIntegral.integral_comp_sub_left (fun θ => (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η)) (Real.pi/2)
        (a := (0:ℝ)) (b := Real.pi/4)
    rw [show Real.pi/2 - Real.pi/4 = Real.pi/4 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro φ hφ
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/4)] at hφ
    show deriv g φ ^ 2 * (Real.sin (2*φ)) ^ (-η)
        = deriv f (Real.pi/2 - φ) ^ 2 * (Real.sin (2*(Real.pi/2 - φ))) ^ (-η)
    have hd : deriv g φ = - deriv f (Real.pi/2 - φ) := by
      rw [hg_def]; exact deriv_comp_const_sub f (Real.pi/2) φ
    rw [hd, show 2*(Real.pi/2 - φ) = Real.pi - 2*φ by ring, Real.sin_pi_sub]
    ring
  have hr3 : (∫ φ in (0:ℝ)..(Real.pi/4), g φ ^ 2 * (Real.sin (2*φ)) ^ (-η))
      = ∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η) := by
    have hcomp := intervalIntegral.integral_comp_sub_left (fun θ => f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) (Real.pi/2)
        (a := (0:ℝ)) (b := Real.pi/4)
    rw [show Real.pi/2 - Real.pi/4 = Real.pi/4 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro φ hφ
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/4)] at hφ
    simp only [hg_def]
    rw [show 2*(Real.pi/2 - φ) = Real.pi - 2*φ by ring, Real.sin_pi_sub]
  have hright : (∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
      ≤ 1/(1+η)^2 * (∫ θ in (Real.pi/4)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
        + C0 * (∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
    rw [← hr1, ← hr2, ← hr3]
    exact hright_raw
  have hsum : (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
        + (∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
      ≤ 1/(1+η)^2 * ((∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
          + (∫ θ in (Real.pi/4)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η)))
        + C0 * ((∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))
          + (∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))) := by
    linarith [hleft, hright]
  have e1 := intervalIntegral.integral_add_adjacent_intervals hIL1 hIL2
  have e2 := intervalIntegral.integral_add_adjacent_intervals hIN1 hIN2
  have e3 := intervalIntegral.integral_add_adjacent_intervals hIP1 hIP2
  have hkey : (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
      ≤ 1/(1+η)^2 * (∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
    rw [← e1, ← e2, ← e3]
    linarith [hsum]
  rw [show (1:ℝ) / (η + 1) ^ 2 = 1 / (1 + η) ^ 2 by ring]
  exact hkey

end Work.FTS.EllipticEst
