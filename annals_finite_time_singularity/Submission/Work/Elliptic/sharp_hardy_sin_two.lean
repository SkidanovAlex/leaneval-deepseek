import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.sin_pow_compare
import Submission.Work.Elliptic.power_hardy
import Submission.Work.Elliptic.sin_weight_integrable
import Submission.Work.Elliptic.sin_l2_weight_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic


theorem half_sharp_hardy {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
        ≤ 1/(1+η)^2 * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ)^2 * (Real.sin (2*θ)) ^ (-η))
          + C * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := sin_pow_compare (η := η) hη0 hη1
  refine ⟨C0, hC0pos, fun f hf hf0 hfpi => ?_⟩
  obtain ⟨hIL, hIN, hIP, hIM, hIQ⟩ := sin_weight_integrable hη0 hη1 hf hf0 hfpi
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
        ≤ f θ ^ 2 * (2*θ) ^ (-(2+η)) + C0 * (f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
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
          (f θ ^ 2 * (2*θ) ^ (-(2+η)) + C0 * (f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))) :=
    intervalIntegral.integral_mono_on hπ4 hIL'
      (hIM'.add (hIN'.const_mul C0)) hpoint
  -- split the RHS
  have hsplit : (∫ θ in (0:ℝ)..(Real.pi/4),
        (f θ ^ 2 * (2*θ) ^ (-(2+η)) + C0 * (f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))))
      = (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (2*θ) ^ (-(2+η)))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
    rw [intervalIntegral.integral_add hIM' (hIN'.const_mul C0),
        intervalIntegral.integral_const_mul]
  -- power-Hardy comparison
  have hpw := power_hardy (a := Real.pi/4) (by positivity) hη0 hη1
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
          (f θ ^ 2 * (2*θ) ^ (-(2+η)) + C0 * (f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))) := hmono
    _ = (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (2*θ) ^ (-(2+η)))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := hsplit
    _ ≤ 1/(1+η)^2 * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
          linarith [hMbound]


theorem sharp_hardy_sin_two (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 (π / 2)) → f 0 = 0 → f (π / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, f θ ^ 2 / (Real.sin (2 * θ)) ^ (2 + η))
        ≤ 1 / (η + 1) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 / (Real.sin (2 * θ)) ^ η)
          + C * ((∫ θ in Work.Spaces.Iθ, f θ ^ 2) + ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2) := by
  obtain ⟨C0, hC0pos, hC0⟩ := half_sharp_hardy hη0 hη1
  obtain ⟨K, hKpos, hK⟩ := sin_l2_weight_bound hη0 hη1
  refine ⟨C0 * K, mul_pos hC0pos hKpos, fun f hf hf0 hfpi => ?_⟩
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
  rw [hdiv (fun θ => f θ ^ 2), hdiv2 (fun θ => (deriv f θ) ^ 2)]
  simp only [keyI]
  -- integrability and the two halves
  obtain ⟨hIL, hIN, hIP, hIM, hIQ⟩ := sin_weight_integrable hη0 hη1 hf hf0 hfpi
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
  have hK' : (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))
      ≤ K * (∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2) := by
    have h := hK f hf hf0
    have hL : (∫ θ in Set.Icc (0:ℝ) (Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))
        = (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := rfl
    have hR : (∫ θ in Set.Icc (0:ℝ) (Real.pi/2), (deriv f θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2) := rfl
    rw [hL, hR, keyI (fun θ => f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)),
        keyI (fun θ => (deriv f θ) ^ 2)] at h
    exact h
  have h4 : 0 ≤ (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2) :=
    intervalIntegral.integral_nonneg (by positivity) (fun θ _ => sq_nonneg _)
  have hkey : (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
      ≤ 1/(1+η)^2 * (∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
    rw [← e1, ← e2, ← e3]
    linarith [hsum]
  have hfin : (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
      ≤ 1/(η+1)^2 * (∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
        + C0 * K * ((∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2) + ∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2) := by
    have h5 : 0 ≤ (∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2) :=
      intervalIntegral.integral_nonneg (by positivity) (fun θ _ => sq_nonneg _)
    have hcoef : (1:ℝ)/(η+1)^2 = 1/(1+η)^2 := by ring
    have hstep : C0 * (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))
        ≤ C0 * K * ((∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2)
            + ∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2) := by
      have hm := mul_le_mul_of_nonneg_left hK' (le_of_lt hC0pos)
      have h5le : (∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2)
          ≤ (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2)
            + ∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2 := by linarith [h4]
      calc C0 * (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))
          ≤ C0 * (K * (∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2)) := hm
        _ = C0 * K * (∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2) := by ring
        _ ≤ C0 * K * ((∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2)
              + ∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2) :=
            mul_le_mul_of_nonneg_left h5le (by positivity)
    calc (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
        ≤ 1/(1+η)^2 * (∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
          + C0 * (∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := hkey
      _ ≤ 1/(1+η)^2 * (∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
          + C0 * K * ((∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2)
              + ∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2) := by linarith [hstep]
      _ = 1/(η+1)^2 * (∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
          + C0 * K * ((∫ θ in (0:ℝ)..(Real.pi/2), f θ ^ 2)
              + ∫ θ in (0:ℝ)..(Real.pi/2), (deriv f θ) ^ 2) := by rw [hcoef]
  exact hfin

end Work.Elliptic
