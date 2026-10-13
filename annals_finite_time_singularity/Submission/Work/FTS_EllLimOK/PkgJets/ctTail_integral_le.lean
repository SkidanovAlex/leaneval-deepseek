import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS_EllLimOK.PkgJets.CosTailDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real
open MeasureTheory Set

/-!
# The `cos`-weight tail bound on `[π/4, T]`

For `T ∈ (π/4, π/2)` we bound the tail of the divergent primitive

`∫_{π/4}^T sin(2s)^{-η}/cos(s)^4 ds ≤ 1000 · (π/2 - T)^{-(3+η)}`,  `η = 99/100`.

Writing `δ = π/2 - T ∈ (0, π/4)` and reflecting by `w = π/2 - s` (the substitution
`intervalIntegral.integral_comp_sub_left` together with `ctF_sub`, which turns `ctF (π/2 - w)`
into `ctG w`), the integral becomes `∫_δ^{π/4} ctG w dw`.  On `(0, π/4]` the elementary
Jordan-type inequalities `sin(2w) ≥ (4/π) w` and `sin w ≥ (2/π) w` give the pointwise bound
`ctG w ≤ 16 w^{-(4+η)}`; integrating `w^{-(4+η)}` exactly (`integral_rpow`) yields
`16·(δ^{-(3+η)} - (π/4)^{-(3+η)})/(3+η) ≤ 16 δ^{-(3+η)} ≤ 1000 δ^{-(3+η)}`.
-/

theorem ctTail_integral_le :
    ∀ T : ℝ, T ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) →
      (∫ s in (Real.pi / 4)..T, ctF s) ≤ 1000 * (Real.pi / 2 - T) ^ (-(3 + 99 / 100 : ℝ)) := by
  intro T hT
  obtain ⟨hT1, hT2⟩ := hT
  set δ : ℝ := Real.pi / 2 - T with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδle : δ ≤ Real.pi / 4 := by rw [hδdef]; linarith
  have hpi4pos : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  -- Pointwise bound `ctG w ≤ 16 w^{-(4+η)}` on `(0, π/4]`.
  have hpb : ∀ w ∈ Set.Icc δ (Real.pi / 4), ctG w ≤ 16 * w ^ (-(4 + 99/100 : ℝ)) := by
    intro w hw
    have hwp : 0 < w := lt_of_lt_of_le hδpos hw.1
    have hw4 : w ≤ Real.pi / 4 := hw.2
    -- `sin (2w) ≥ (4/π) w`
    have hsin2ge : 4 / Real.pi * w ≤ Real.sin (2 * w) := by
      have h := Real.mul_le_sin (by linarith : (0 : ℝ) ≤ 2 * w)
        (by linarith : 2 * w ≤ Real.pi / 2)
      calc 4 / Real.pi * w = 2 / Real.pi * (2 * w) := by ring
        _ ≤ Real.sin (2 * w) := h
    have hnum1 : Real.sin (2 * w) ^ (-(99/100 : ℝ)) ≤ (4 / Real.pi * w) ^ (-(99/100 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (x := 4 / Real.pi * w) (y := Real.sin (2 * w))
        (z := -(99/100 : ℝ)) (by positivity) hsin2ge (by norm_num)
    have hnum2 : (4 / Real.pi * w) ^ (-(99/100 : ℝ))
        = (4 / Real.pi) ^ (-(99/100 : ℝ)) * w ^ (-(99/100 : ℝ)) :=
      Real.mul_rpow (by positivity) (le_of_lt hwp)
    have hnum3 : (4 / Real.pi) ^ (-(99/100 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]) (by norm_num)
    have hnum : Real.sin (2 * w) ^ (-(99/100 : ℝ)) ≤ w ^ (-(99/100 : ℝ)) := by
      have hA : Real.sin (2 * w) ^ (-(99/100 : ℝ))
          ≤ (4 / Real.pi) ^ (-(99/100 : ℝ)) * w ^ (-(99/100 : ℝ)) := by
        rw [← hnum2]; exact hnum1
      have hB : (4 / Real.pi) ^ (-(99/100 : ℝ)) * w ^ (-(99/100 : ℝ))
          ≤ 1 * w ^ (-(99/100 : ℝ)) :=
        mul_le_mul_of_nonneg_right hnum3 (Real.rpow_nonneg (le_of_lt hwp) _)
      exact le_trans hA (by simpa using hB)
    -- `1 / (sin w)^4 ≤ 16 w^{-4}`
    have hden : 1 / (Real.sin w) ^ (4 : ℕ) ≤ 16 * w ^ (-(4 : ℝ)) := by
      have hsinwge : 2 / Real.pi * w ≤ Real.sin w :=
        Real.mul_le_sin (le_of_lt hwp) (by linarith)
      have hp4 : ((2 / Real.pi) * w) ^ (4 : ℕ) ≤ (Real.sin w) ^ (4 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hsinwge 4
      have h1 : 1 / (Real.sin w) ^ (4 : ℕ) ≤ 1 / ((2 / Real.pi) * w) ^ (4 : ℕ) :=
        one_div_le_one_div_of_le (by positivity) hp4
      have h2 : 1 / ((2 / Real.pi) * w) ^ (4 : ℕ) = ((2 / Real.pi) * w) ^ (-(4 : ℝ)) := by
        rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (2 / Real.pi) * w), inv_eq_one_div]
        simp
      have h3 : ((2 / Real.pi) * w) ^ (-(4 : ℝ))
          = (2 / Real.pi) ^ (-(4 : ℝ)) * w ^ (-(4 : ℝ)) :=
        Real.mul_rpow (by positivity) (le_of_lt hwp)
      have h4 : (2 / Real.pi) ^ (-(4 : ℝ)) ≤ 16 := by
        have hhalf : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
          rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
        have h := Real.rpow_le_rpow_of_nonpos (x := (1 / 2 : ℝ)) (y := 2 / Real.pi)
          (z := -(4 : ℝ)) (by norm_num) hhalf (by norm_num)
        have h16 : ((1 / 2 : ℝ)) ^ (-(4 : ℝ)) = 16 := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2), inv_eq_one_div]
          norm_num
        linarith
      calc 1 / (Real.sin w) ^ (4 : ℕ) ≤ 1 / ((2 / Real.pi) * w) ^ (4 : ℕ) := h1
        _ = ((2 / Real.pi) * w) ^ (-(4 : ℝ)) := h2
        _ = (2 / Real.pi) ^ (-(4 : ℝ)) * w ^ (-(4 : ℝ)) := h3
        _ ≤ 16 * w ^ (-(4 : ℝ)) :=
            mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg (le_of_lt hwp) _)
    calc ctG w = Real.sin (2 * w) ^ (-(99/100 : ℝ)) / (Real.sin w) ^ (4 : ℕ) := rfl
      _ ≤ w ^ (-(99/100 : ℝ)) / (Real.sin w) ^ (4 : ℕ) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = w ^ (-(99/100 : ℝ)) * (1 / (Real.sin w) ^ (4 : ℕ)) := by
          rw [div_eq_mul_inv, one_div]
      _ ≤ w ^ (-(99/100 : ℝ)) * (16 * w ^ (-(4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg (le_of_lt hwp) _)
      _ = 16 * w ^ (-(4 + 99/100 : ℝ)) := by
          rw [show w ^ (-(99/100 : ℝ)) * (16 * w ^ (-(4 : ℝ)))
                = 16 * (w ^ (-(99/100 : ℝ)) * w ^ (-(4 : ℝ))) from by ring,
              ← Real.rpow_add hwp (-(99/100 : ℝ)) (-(4 : ℝ)),
              show -(99/100 : ℝ) + -(4 : ℝ) = -(4 + 99/100 : ℝ) by norm_num]
  -- Reflect: `∫_{π/4}^T ctF = ∫_δ^{π/4} ctG`.
  have hsub : (∫ s in (Real.pi / 4)..T, ctF s) = ∫ w in δ..(Real.pi / 4), ctG w := by
    have h := intervalIntegral.integral_comp_sub_left (f := ctF) (a := δ) (b := Real.pi / 4)
      (Real.pi / 2)
    simp only [ctF_sub] at h
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring,
        show Real.pi / 2 - δ = T by rw [hδdef]; ring] at h
    exact h.symm
  have hintG : IntervalIntegrable ctG volume δ (Real.pi / 4) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hδle]
    unfold ctG
    refine ContinuousOn.div ?_ ?_ ?_
    · refine ContinuousOn.rpow_const ?_ ?_
      · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      · intro x hx
        left
        exact ne_of_gt (Real.sin_pos_of_mem_Ioo
          ⟨by linarith [hx.1, hδpos], by linarith [hx.2, Real.pi_pos]⟩)
    · exact (Real.continuous_sin.pow 4).continuousOn
    · intro x hx
      exact pow_ne_zero 4 (ne_of_gt (Real.sin_pos_of_mem_Ioo
        ⟨lt_of_lt_of_le hδpos hx.1, by linarith [hx.2, Real.pi_pos]⟩))
  have hintR : IntervalIntegrable (fun w : ℝ => 16 * w ^ (-(4 + 99/100 : ℝ))) volume δ
      (Real.pi / 4) := by
    have hc : ContinuousOn (fun w : ℝ => 16 * w ^ (-(4 + 99/100 : ℝ)))
        (Set.Icc δ (Real.pi / 4)) :=
      continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le hδpos hx.1))))
    rw [← Set.uIcc_of_le hδle] at hc
    exact hc.intervalIntegrable
  have hmono : (∫ w in δ..(Real.pi / 4), ctG w)
      ≤ ∫ w in δ..(Real.pi / 4), 16 * w ^ (-(4 + 99/100 : ℝ)) :=
    intervalIntegral.integral_mono_on hδle hintG hintR hpb
  -- Exact value of the majorant integral.
  have hval : (∫ w in δ..(Real.pi / 4), 16 * w ^ (-(4 + 99/100 : ℝ)))
      = 16 * ((δ ^ (-(3 + 99/100 : ℝ)) - (Real.pi / 4) ^ (-(3 + 99/100 : ℝ)))
          / (3 + 99/100 : ℝ)) := by
    have hcond : -1 < (-(4 + 99/100 : ℝ)) ∨
        (-(4 + 99/100 : ℝ)) ≠ -1 ∧ 0 ∉ Set.uIcc δ (Real.pi / 4) := by
      right
      constructor
      · norm_num
      · rw [Set.uIcc_of_le hδle]
        intro hmem
        exact (not_le_of_gt hδpos) hmem.1
    rw [intervalIntegral.integral_const_mul, integral_rpow hcond]
    rw [show -(4 + 99/100 : ℝ) + 1 = -(3 + 99/100 : ℝ) by norm_num]
    congr 1
    field_simp
    ring
  -- The arithmetic: `16 (δ^{-(3+η)} - (π/4)^{-(3+η)})/(3+η) ≤ 1000 δ^{-(3+η)}`.
  have hfinal : 16 * ((δ ^ (-(3 + 99/100 : ℝ)) - (Real.pi / 4) ^ (-(3 + 99/100 : ℝ)))
        / (3 + 99/100 : ℝ)) ≤ 1000 * δ ^ (-(3 + 99/100 : ℝ)) := by
    set A : ℝ := δ ^ (-(3 + 99/100 : ℝ)) with hA
    set B : ℝ := (Real.pi / 4) ^ (-(3 + 99/100 : ℝ)) with hB
    have hAp : 0 < A := by rw [hA]; exact Real.rpow_pos_of_pos hδpos _
    have hBp : 0 < B := by rw [hB]; exact Real.rpow_pos_of_pos hpi4pos _
    have hk : (0 : ℝ) < 3 + 99/100 := by norm_num
    have h1 : (A - B) / (3 + 99/100) ≤ A := by
      calc (A - B) / (3 + 99/100) ≤ A / (3 + 99/100) :=
            div_le_div_of_nonneg_right (by linarith) (le_of_lt hk)
        _ ≤ A := by rw [div_le_iff₀ hk]; nlinarith [hAp, hk]
    rw [hA, hB] at h1 ⊢
    linarith
  rw [hsub]
  calc (∫ w in δ..(Real.pi / 4), ctG w)
        ≤ ∫ w in δ..(Real.pi / 4), 16 * w ^ (-(4 + 99/100 : ℝ)) := hmono
    _ = 16 * ((δ ^ (-(3 + 99/100 : ℝ)) - (Real.pi / 4) ^ (-(3 + 99/100 : ℝ)))
          / (3 + 99/100 : ℝ)) := hval
    _ ≤ 1000 * δ ^ (-(3 + 99/100 : ℝ)) := hfinal

end Work.FTS_EllLimOK.PkgJets
