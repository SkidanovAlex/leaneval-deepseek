import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.Elliptic.sharp_hardy_sin_two

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! # Sharp weighted Hardy inequality with a `cos²(2θ)`-weight

The target lemma `SharpHardyCosWeight` is the sharp `L²`-Hardy inequality for the singular
weight `sin(2θ)^{-(2+η)}` on `Iθ = [0, π/2]` in which the leading singularity is produced by
`cos(2θ)²` (i.e. `cos²(2θ) sin(2θ)^{-(2+η)} = cot²(2θ) sin(2θ)^{-η}`):

`∫_Iθ f² cos²(2θ) sin(2θ)^{-(2+η)} ≤ (1+η)^{-2} ∫_Iθ f'² sin(2θ)^{-η} + C ∫_Iθ f² sin(2θ)^{-η}`.

* `CosSqWeightIntegrable`: the `cos²(2θ)`-weighted integrand is (interval-)integrable.
* `HalfSharpHardyCos`: the left-half `(0, π/4)` version of the inequality, obtained from the
  already proved `Work.Elliptic.half_sharp_hardy` together with the pointwise bound
  `cos² ≤ 1`.
* The right half `(π/4, π/2)` is obtained from the left half by reflection
  `θ ↦ π/2 - θ` (the identities `rA_cos`, `rB`, `rD` below), and the two halves are glued
  by `intervalIntegral.integral_add_adjacent_intervals`.
-/

/-- The interval-integrability of the `cos²(2θ)`-weighted integrand, obtained from
`Work.Elliptic.sin_weight_integrable` applied to the `C¹` function `θ ↦ f θ · cos(2θ)`. -/
theorem CosSqWeightIntegrable {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0) (hpi : f (Real.pi / 2) = 0) :
    IntervalIntegrable (fun θ => f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
      MeasureTheory.volume 0 (Real.pi / 2) := by
  have hg : ContDiffOn ℝ 1 (fun θ : ℝ => f θ * Real.cos (2 * θ)) (Set.Icc 0 (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 1 (fun θ : ℝ => Real.cos (2 * θ)) (Set.Icc 0 (Real.pi / 2)) := by
      fun_prop
    exact hf.mul h1
  have hg0 : (fun θ : ℝ => f θ * Real.cos (2 * θ)) 0 = 0 := by simp [h0]
  have hgpi : (fun θ : ℝ => f θ * Real.cos (2 * θ)) (Real.pi / 2) = 0 := by
    show f (Real.pi / 2) * Real.cos (2 * (Real.pi / 2)) = 0
    rw [hpi, zero_mul]
  have h := (Work.Elliptic.sin_weight_integrable hη0 hη1 hg hg0 hgpi).1
  refine h.congr (fun x _ => ?_)
  show (f x * Real.cos (2 * x)) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
      = f x ^ 2 * (Real.cos (2 * x)) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
  rw [mul_pow]

/-- **Sharp weighted Hardy inequality with `cos²`-weight on the left half `(0, π/4)`.**
Since `cos(2θ)² ≤ 1` there, the `cos²`-weighted integral is dominated by the unweighted one,
and `Work.Elliptic.half_sharp_hardy` gives the sharp constant `(1+η)^{-2}`. -/
theorem HalfSharpHardyCos {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2+η)))
        ≤ 1/(1+η)^2 * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
          + C * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.Elliptic.half_sharp_hardy hη0 hη1
  refine ⟨C0, hC0pos, fun f hf hf0 hfpi => ?_⟩
  have hπ4 : (0:ℝ) ≤ Real.pi/4 := by positivity
  have hπ2 : (0:ℝ) ≤ Real.pi/2 := by positivity
  have hsub : Set.uIcc (0:ℝ) (Real.pi/4) ⊆ Set.uIcc 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le hπ4, Set.uIcc_of_le hπ2]
    exact Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])
  have hA1 := (CosSqWeightIntegrable hη0 hη1 hf hf0 hfpi).mono_set hsub
  have hIL1 := (Work.Elliptic.sin_weight_integrable hη0 hη1 hf hf0 hfpi).1.mono_set hsub
  have hmono : (∫ θ in (0:ℝ)..(Real.pi/4),
        f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2+η)))
      ≤ ∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2+η)) :=
    intervalIntegral.integral_mono_on hπ4 hA1 hIL1 (fun x hx => by
      have hs : 0 ≤ (Real.sin (2 * x)) ^ (-(2 + η)) :=
        Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
          (by linarith [hx.2, Real.pi_pos])) _
      have hcos : (Real.cos (2 * x)) ^ 2 ≤ 1 := Real.cos_sq_le_one (2 * x)
      have h1 : (Real.cos (2 * x)) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
          ≤ 1 * (Real.sin (2 * x)) ^ (-(2 + η)) := mul_le_mul_of_nonneg_right hcos hs
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (f x))
      calc f x ^ 2 * (Real.cos (2 * x)) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
          = f x ^ 2 * ((Real.cos (2 * x)) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))) := by ring
        _ ≤ f x ^ 2 * (1 * (Real.sin (2 * x)) ^ (-(2 + η))) := h2
        _ = f x ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η)) := by ring)
  have hc := hC0 f hf hf0 hfpi
  linarith [hmono, hc]

/-- **Sharp Hardy inequality for the singular weight `sin(2θ)^{-(2+η)}` with a `cos²(2θ)`
factor**, on `Iθ = [0, π/2]`.  The proof splits `Iθ` at `π/4`, applies `HalfSharpHardyCos`
to `f` on the left half and to the reflection `φ ↦ f (π/2 - φ)` on the right half (the
reflection identities `rA_cos`, `rB`, `rD`), and glues the two halves together. -/
theorem SharpHardyCosWeight (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) → f 0 = 0 → f (Real.pi / 2) = 0 →
        (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + η)))
          ≤ 1 / (1 + η) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
            + C * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := HalfSharpHardyCos hη0 hη1
  refine ⟨C0, hC0pos, fun f hf hf0 hfpi => ?_⟩
  have hπ2 : (0:ℝ) ≤ Real.pi / 2 := by positivity
  have hπ4 : (0:ℝ) ≤ Real.pi / 4 := by positivity
  obtain ⟨hIL, hIN, hIP, _hIM, _hIQ⟩ := Work.Elliptic.sin_weight_integrable hη0 hη1 hf hf0 hfpi
  have hAint := CosSqWeightIntegrable hη0 hη1 hf hf0 hfpi
  have hsub1 : Set.uIcc (0:ℝ) (Real.pi/4) ⊆ Set.uIcc 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le hπ4, Set.uIcc_of_le hπ2]
    exact Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])
  have hsub2 : Set.uIcc (Real.pi/4) (Real.pi/2) ⊆ Set.uIcc 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : Real.pi/4 ≤ Real.pi/2), Set.uIcc_of_le hπ2]
    exact Set.Icc_subset_Icc (by positivity) le_rfl
  have hA1 := hAint.mono_set hsub1
  have hA2 := hAint.mono_set hsub2
  have hIL1 := hIL.mono_set hsub1
  have hIL2 := hIL.mono_set hsub2
  have hIN1 := hIN.mono_set hsub1
  have hIN2 := hIN.mono_set hsub2
  have hIP1 := hIP.mono_set hsub1
  have hIP2 := hIP.mono_set hsub2
  -- left half
  have hleft := hC0 f hf hf0 hfpi
  -- right half via the reflection `gr φ = f (π/2 - φ)`
  set gr : ℝ → ℝ := fun φ => f (Real.pi / 2 - φ) with hgr
  have hgr_cd : ContDiffOn ℝ 1 gr (Set.Icc 0 (Real.pi/2)) := by
    have h1 : ContDiffOn ℝ 1 (fun φ : ℝ => Real.pi/2 - φ) (Set.Icc 0 (Real.pi/2)) := by fun_prop
    have h2 : Set.MapsTo (fun φ : ℝ => Real.pi/2 - φ) (Set.Icc 0 (Real.pi/2))
        (Set.Icc 0 (Real.pi/2)) := by
      intro x hx; simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.2, Real.pi_pos], by linarith [hx.1]⟩
    simpa only [hgr, Function.comp_def] using hf.comp h1 h2
  have hgr0 : gr 0 = 0 := by rw [hgr]; simp only [sub_zero]; exact hfpi
  have hgrpi : gr (Real.pi/2) = 0 := by rw [hgr]; simp only [sub_self]; exact hf0
  have hright_raw := hC0 gr hgr_cd hgr0 hgrpi
  have rA_cos : (∫ φ in (0:ℝ)..(Real.pi/4),
        gr φ ^ 2 * (Real.cos (2*φ))^2 * (Real.sin (2*φ))^(-(2+η)))
      = ∫ θ in (Real.pi/4)..(Real.pi/2),
        f θ ^ 2 * (Real.cos (2*θ))^2 * (Real.sin (2*θ))^(-(2+η)) := by
    have hcomp := intervalIntegral.integral_comp_sub_left
        (fun θ : ℝ => f θ ^ 2 * (Real.cos (2*θ))^2 * (Real.sin (2*θ))^(-(2+η))) (Real.pi/2)
        (a := (0:ℝ)) (b := Real.pi/4)
    rw [show Real.pi/2 - Real.pi/4 = Real.pi/4 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro φ _hφ
    simp only [hgr]
    rw [show 2*(Real.pi/2 - φ) = Real.pi - 2*φ by ring, Real.cos_pi_sub, Real.sin_pi_sub]
    ring
  have rD : (∫ φ in (0:ℝ)..(Real.pi/4), gr φ ^ 2 * (Real.sin (2*φ))^(-η))
      = ∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ))^(-η) := by
    have hcomp := intervalIntegral.integral_comp_sub_left
        (fun θ : ℝ => f θ ^ 2 * (Real.sin (2*θ))^(-η)) (Real.pi/2) (a := (0:ℝ)) (b := Real.pi/4)
    rw [show Real.pi/2 - Real.pi/4 = Real.pi/4 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro φ _hφ
    simp only [hgr]
    rw [show 2*(Real.pi/2 - φ) = Real.pi - 2*φ by ring, Real.sin_pi_sub]
  have rB : (∫ φ in (0:ℝ)..(Real.pi/4), (deriv gr φ) ^ 2 * (Real.sin (2*φ))^(-η))
      = ∫ θ in (Real.pi/4)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ))^(-η) := by
    have hcomp := intervalIntegral.integral_comp_sub_left
        (fun θ : ℝ => (deriv f θ)^2 * (Real.sin (2*θ))^(-η)) (Real.pi/2) (a := (0:ℝ))
        (b := Real.pi/4)
    rw [show Real.pi/2 - Real.pi/4 = Real.pi/4 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro φ _hφ
    show deriv gr φ ^ 2 * (Real.sin (2*φ))^(-η)
      = (deriv f (Real.pi/2 - φ))^2 * (Real.sin (2*(Real.pi/2 - φ)))^(-η)
    have hd : deriv gr φ = - deriv f (Real.pi/2 - φ) := by
      simp only [hgr]; exact deriv_comp_const_sub f (Real.pi/2) φ
    rw [hd, show 2*(Real.pi/2 - φ) = Real.pi - 2*φ by ring, Real.sin_pi_sub]
    ring
  have hright : (∫ θ in (Real.pi/4)..(Real.pi/2),
        f θ ^ 2 * (Real.cos (2*θ))^2 * (Real.sin (2*θ))^(-(2+η)))
      ≤ 1/(1+η)^2 * (∫ θ in (Real.pi/4)..(Real.pi/2),
          (deriv f θ)^2 * (Real.sin (2*θ))^(-η))
        + C0 * (∫ θ in (Real.pi/4)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ))^(-η)) := by
    rw [rA_cos, rB, rD] at hright_raw
    exact hright_raw
  -- glue the two halves
  have e1 := intervalIntegral.integral_add_adjacent_intervals hA1 hA2
  have e2 := intervalIntegral.integral_add_adjacent_intervals hIN1 hIN2
  have e3 := intervalIntegral.integral_add_adjacent_intervals hIP1 hIP2
  have hmid : (∫ θ in (0:ℝ)..(Real.pi/2),
        f θ^2 * (Real.cos (2*θ))^2 * (Real.sin (2*θ))^(-(2+η)))
      ≤ 1/(1+η)^2 * (∫ θ in (0:ℝ)..(Real.pi/2),
          (deriv f θ)^2 * (Real.sin (2*θ))^(-η))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi/2), f θ^2 * (Real.sin (2*θ))^(-η)) := by
    have h1 := add_le_add hleft hright
    rw [← e1, ← e2, ← e3]
    exact le_of_le_of_eq h1 (by ring)
  have keyI : ∀ h : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, h θ) = ∫ θ in (0:ℝ)..(Real.pi/2), h θ := by
    intro h
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hπ2]
  rw [keyI (fun θ => f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))),
      keyI (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)),
      keyI (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))]
  exact hmid

end Work.FTS.EllipticEst.Honest
