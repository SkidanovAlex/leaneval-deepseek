import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.sin_pow_compare
import Submission.Work.Elliptic.power_hardy
import Submission.Work.Elliptic.sin_weight_integrable
import Submission.Work.FTS.EllipticEst.Honest.SharpHardyCosWeight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.PthCore

open scoped Real Topology
open MeasureTheory Set Filter

/-! # Sharp Hardy on `(0, π/4)` with a `cos²(2θ)`-weight and absolute constants

`Work.Elliptic.half_sharp_hardy` proves

`∫_0^{π/4} f² sin(2θ)^{-(2+η)} ≤ (1+η)^{-2} ∫_0^{π/4} (f')² sin(2θ)^{-η} + C ∫_0^{π/4} f² sin(2θ)^{-η}`

with an *existential* constant `C`; inspecting its proof one sees that `C = 2` always works
(the comparison `Work.Elliptic.sin_pow_compare` is proved with the very constant `2`).  This
file records that explicit form (`half_sharp_hardy_two`) and then adds the `cos²(2θ) ≤ 1`
step of `Work.FTS.EllipticEst.Honest.HalfSharpHardyCos` to obtain `HalfSharpHardyCosTwo`
with both constants absolute: `(1+η)^{-2}` and `2`. -/

/-- `Work.Elliptic.sin_pow_compare` with the constant pinned to `2` (its proof is
`refine ⟨2, by norm_num, ?_⟩`, so this is the same argument with `C = 2` inlined). -/
lemma sin_pow_compare_two {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∀ t : ℝ, 0 < t → t ≤ Real.pi / 2 →
      (Real.sin t) ^ (-(2 + η)) ≤ t ^ (-(2 + η)) + 2 * (Real.sin t) ^ (-η) := by
  intro t ht0 htpi
  set s := Real.sin t with hs_def
  have hs0 : 0 < s := by
    rw [hs_def]; exact Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [htpi, Real.pi_pos])
  have hst : s ≤ t := by rw [hs_def]; exact Real.sin_le ht0.le
  have hsπ : 2/π * t ≤ s := by rw [hs_def]; exact Real.mul_le_sin ht0.le htpi
  have hscube : t - t ^ 3 / 6 ≤ s := by rw [hs_def]; exact Real.sin_ge_sub_cube ht0.le
  -- the ratio `x = s / t` lies in `(0, 1]`
  have hx0 : 0 < s / t := div_pos hs0 ht0
  have hx1 : s / t ≤ 1 := (div_le_one ht0).mpr hst
  have hp3 : 2 + η ≤ 3 := by linarith
  have hxp : 1 - (s / t) ^ (2 + η) ≤ 3 * (1 - s / t) :=
    Work.Elliptic.one_sub_rpow_le_three_mul hx0 hx1 hp3
  have hm1 : 1 - s / t = (t - s) / t := by field_simp
  have hupper : (t - s) / t ≤ t ^ 2 / 6 := by
    rw [div_le_iff₀ ht0]; nlinarith [hscube]
  -- the correction is bounded by `t^2 / 2`
  have h1 : 1 - (s / t) ^ (2 + η) ≤ t ^ 2 / 2 := by
    calc 1 - (s / t) ^ (2 + η) ≤ 3 * (1 - s / t) := hxp
      _ = 3 * ((t - s) / t) := by rw [hm1]
      _ ≤ 3 * (t ^ 2 / 6) := by linarith
      _ = t ^ 2 / 2 := by ring
  have hs2 : s ^ (-(2:ℝ)) = (s ^ 2)⁻¹ := by
    rw [Real.rpow_neg hs0.le (2:ℝ), show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  -- and `t / s ≤ π / 2 < 2`
  have hts2 : t / s ≤ 2 := by
    rw [div_le_iff₀ hs0]
    have h2ts : 2 * t ≤ π * s := by
      have h := mul_le_mul_of_nonneg_left hsπ (le_of_lt Real.pi_pos)
      have he : π * (2 / π * t) = 2 * t := by field_simp
      rwa [he] at h
    nlinarith [h2ts, mul_lt_mul_of_pos_right Real.pi_lt_four hs0]
  have htsnn : 0 ≤ t / s := div_nonneg ht0.le hs0.le
  have hC : s ^ (-(2:ℝ)) * (1 - (s / t) ^ (2 + η)) ≤ 2 := by
    calc s ^ (-(2:ℝ)) * (1 - (s / t) ^ (2 + η))
        ≤ s ^ (-(2:ℝ)) * (t ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.rpow_pos_of_pos hs0 _))
      _ = (t / s) ^ 2 / 2 := by rw [hs2]; field_simp
      _ ≤ 2 := by nlinarith [hts2, htsnn,
            mul_nonneg (sub_nonneg.mpr hts2) (by linarith : (0:ℝ) ≤ t / s + 2)]
  have hsneg : 0 < s ^ (-η) := Real.rpow_pos_of_pos hs0 (-η)
  have hD : s ^ (-(2 + η)) - t ^ (-(2 + η)) = s ^ (-(2 + η)) * (1 - (s / t) ^ (2 + η)) := by
    rw [mul_sub, mul_one, Work.Elliptic.rpow_neg_mul_div_rpow hs0 ht0]
  have hsp : s ^ (-(2 + η)) = s ^ (-η) * s ^ (-(2:ℝ)) := by
    rw [← Real.rpow_add hs0 (-η) (-(2:ℝ))]; congr 1; ring
  have hfinal : s ^ (-(2 + η)) - t ^ (-(2 + η)) ≤ 2 * s ^ (-η) := by
    rw [hD, hsp]
    calc s ^ (-η) * s ^ (-(2:ℝ)) * (1 - (s / t) ^ (2 + η))
        = s ^ (-η) * (s ^ (-(2:ℝ)) * (1 - (s / t) ^ (2 + η))) := by ring
      _ ≤ s ^ (-η) * 2 := mul_le_mul_of_nonneg_left hC hsneg.le
      _ = 2 * s ^ (-η) := by ring
  linarith

/-- `Work.Elliptic.half_sharp_hardy` with the explicit constant `2`.  This is the proof of
`half_sharp_hardy` with `C₀ := 2` (supplied by `sin_pow_compare_two`) substituted for the
existential constant of `Work.Elliptic.sin_pow_compare`. -/
lemma half_sharp_hardy_two {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
        ≤ 1/(1+η)^2 * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ)^2 * (Real.sin (2*θ)) ^ (-η))
          + 2 * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
  intro f hf hf0 hfpi
  have hC0 := sin_pow_compare_two (η := η) hη0 hη1
  obtain ⟨hIL, hIN, hIP, hIM, hIQ⟩ := Work.Elliptic.sin_weight_integrable hη0 hη1 hf hf0 hfpi
  have hπ4 : (0:ℝ) ≤ Real.pi/4 := by positivity
  have hsub : Set.uIcc (0:ℝ) (Real.pi/4) ⊆ Set.uIcc 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le hπ4, Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)]
    exact Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])
  have hIL' := hIL.mono_set hsub
  have hIN' := hIN.mono_set hsub
  have hIP' := hIP.mono_set hsub
  have hIM' := hIM.mono_set hsub
  have hIQ' := hIQ.mono_set hsub
  -- pointwise comparison
  have hpoint : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi/4),
      f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η))
        ≤ f θ ^ 2 * (2*θ) ^ (-(2+η)) + 2 * (f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0]; simp [hf0]
    · have h2 : 0 < 2*θ := by linarith
      have h3 : 2*θ ≤ Real.pi/2 := by linarith [hθ.2]
      have hc := hC0 (2*θ) h2 h3
      have : 0 ≤ f θ ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hc this]
  have hmono : (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
      ≤ ∫ θ in (0:ℝ)..(Real.pi/4),
          (f θ ^ 2 * (2*θ) ^ (-(2+η)) + 2 * (f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))) :=
    intervalIntegral.integral_mono_on hπ4 hIL'
      (hIM'.add (hIN'.const_mul 2)) hpoint
  -- split the RHS
  have hsplit : (∫ θ in (0:ℝ)..(Real.pi/4),
        (f θ ^ 2 * (2*θ) ^ (-(2+η)) + 2 * (f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))))
      = (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (2*θ) ^ (-(2+η)))
        + 2 * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
    rw [intervalIntegral.integral_add hIM' (hIN'.const_mul 2),
        intervalIntegral.integral_const_mul]
  -- power-Hardy comparison
  have hpw := Work.Elliptic.power_hardy (a := Real.pi/4) (by positivity) hη0 hη1
      (hf.mono (Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos]))) hf0
  have hscal : (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (2*θ) ^ (-(2+η)))
      = 2 ^ (-(2+η)) * ∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * θ ^ (-(2+η)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hπ4] at hθ
    show f θ ^ 2 * (2*θ) ^ (-(2+η)) = 2 ^ (-(2+η)) * (f θ ^ 2 * θ ^ (-(2+η)))
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hθ.1]
    ring
  have hscal2 : (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * θ ^ (-η))
      = 2 ^ η * ∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (2*θ) ^ (-η) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hπ4] at hθ
    show (deriv f θ) ^ 2 * θ ^ (-η) = 2 ^ η * ((deriv f θ) ^ 2 * (2*θ) ^ (-η))
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hθ.1,
        show (2:ℝ) ^ (-η) = ((2:ℝ) ^ η)⁻¹ from Real.rpow_neg (by norm_num) η]
    field_simp
  have hQP : (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (2*θ) ^ (-η))
      ≤ ∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η) := by
    refine intervalIntegral.integral_mono_on hπ4 hIQ' hIP' ?_
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0]; simp
    · have hsinpos : 0 < Real.sin (2*θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2, Real.pi_pos])
      have hle : Real.sin (2*θ) ≤ 2*θ := Real.sin_le (by linarith)
      have hr := Real.rpow_le_rpow_of_nonpos hsinpos hle (by linarith : -η ≤ 0)
      exact mul_le_mul_of_nonneg_left hr (sq_nonneg _)
  have hMbound : (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (2*θ) ^ (-(2+η)))
      ≤ 1/(1+η)^2 * ∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η) := by
    have hcoef : 2 ^ (-(2+η)) * (4 / (1+η)^2) * (2^η) = 1/(1+η)^2 := by
      rw [show (2:ℝ) ^ (-(2+η)) = (2 ^ (2+η))⁻¹ from Real.rpow_neg (by norm_num) (2+η)]
      have h2 : (2:ℝ) ^ (2+η) = 2^2 * 2^η := by
        rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]; norm_num
      rw [h2]
      have h2η : (2:ℝ)^η ≠ 0 := by positivity
      have h1η : (1:ℝ) + η ≠ 0 := by linarith
      field_simp
      ring
    rw [hscal]
    calc 2 ^ (-(2+η)) * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * θ ^ (-(2+η)))
        ≤ 2 ^ (-(2+η)) * (4 / (1+η)^2
            * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * θ ^ (-η))) :=
          mul_le_mul_of_nonneg_left hpw (by positivity)
      _ = (2 ^ (-(2+η)) * (4 / (1+η)^2) * (2^η))
            * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (2*θ) ^ (-η)) := by
          rw [hscal2]; ring
      _ = (1/(1+η)^2) * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (2*θ) ^ (-η)) := by
          rw [hcoef]
      _ ≤ (1/(1+η)^2)
            * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η)) :=
          mul_le_mul_of_nonneg_left hQP (by positivity)
  calc (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
      ≤ ∫ θ in (0:ℝ)..(Real.pi/4),
          (f θ ^ 2 * (2*θ) ^ (-(2+η)) + 2 * (f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))) := hmono
    _ = (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (2*θ) ^ (-(2+η)))
        + 2 * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := hsplit
    _ ≤ 1/(1+η)^2 * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
        + 2 * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
          linarith [hMbound]

/-- **Sharp Hardy on the left half `(0,π/4)` with a `cos²(2θ)`-weight, with absolute constants.**
For every `0 ≤ η < 1` and every `C¹` `f` on `[0,π/2]` with `f 0 = f (π/2) = 0`,
`∫_0^{π/4} f²cos²(2θ)sin(2θ)^{-(2+η)} ≤ (1+η)^{-2}∫_0^{π/4}(f')²sin(2θ)^{-η} + 2∫_0^{π/4}f²sin(2θ)^{-η}`.
Suggested route (all constants absolute). `Work.Elliptic.sin_pow_compare` is stated with an
existential constant, but its proof begins `refine ⟨2, by norm_num, ?_⟩`, so copying that proof
verbatim (with the `obtain`/`hC0` plumbing replaced by the explicit `2`) yields
`0 ≤ η → η < 1 → 0 < t → t ≤ π/2 → sin t ^ (-(2+η)) ≤ t ^ (-(2+η)) + 2 * sin t ^ (-η)`.
Then run the proof of `Work.Elliptic.half_sharp_hardy` with `C₀ := 2` (its proof uses only that
comparison, `Work.Elliptic.power_hardy`, `Work.Elliptic.sin_weight_integrable` and the
`η`-independent algebra `2^(-(2+η)) * (4/(1+η)^2) * 2^η = 1/(1+η)^2`) to obtain the same
inequality without the `cos²`; finally add the `cos² ≤ 1` step exactly as in
`Work.FTS.EllipticEst.Honest.HalfSharpHardyCos` (the `cos²`-integrability comes from
`Work.FTS.EllipticEst.Honest.CosSqWeightIntegrable`). -/
theorem HalfSharpHardyCosTwo {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) → f 0 = 0 → f (Real.pi / 2) = 0 →
      (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2+η)))
        ≤ 1 / (1 + η) ^ 2 * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
          + 2 * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
  intro f hf hf0 hfpi
  have hπ4 : (0:ℝ) ≤ Real.pi/4 := by positivity
  have hsub : Set.uIcc (0:ℝ) (Real.pi/4) ⊆ Set.uIcc 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le hπ4, Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)]
    exact Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])
  have hA1 := (Work.FTS.EllipticEst.Honest.CosSqWeightIntegrable hη0 hη1 hf hf0 hfpi).mono_set hsub
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
  have hc := half_sharp_hardy_two hη0 hη1 f hf hf0 hfpi
  linarith [hmono, hc]

end Work.FTS.EllipticEst.Honest.PthCore
