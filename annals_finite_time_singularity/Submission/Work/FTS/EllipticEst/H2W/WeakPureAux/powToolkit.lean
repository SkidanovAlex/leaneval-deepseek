import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.PowToolkitPieces.trigLeft
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.PowToolkitPieces.trigRight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

/-! ### Helpers for `powToolkit`

The eight conjuncts are

* two trigonometric comparisons on `(0, π/4]` resp. `[π/4, π/2)`, proved in the sibling modules
  `Work.FTS.EllipticEst.H2W.WeakPureAux.PowToolkitPieces.trigLeft` / `.trigRight` from Jordan's
  inequality `Real.mul_le_sin` (`2x/π ≤ sin x` for `x ∈ [0, π/2]`), with the exact constants
  `π²/8` and `π³/32`;
* six antiderivative evaluations, proved below from `integral_rpow` (together with the
  substitution `u = π/2 - s` in the last three). -/

/-- `0` is not in `uIcc a b` when both endpoints are positive. -/
private lemma powToolkit_zero_notMem_uIcc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (0 : ℝ) ∉ Set.uIcc a b := by
  rw [Set.mem_uIcc]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith

/-- `integral_rpow` in the case where both endpoints are positive (so the branch cut at `0`
is irrelevant): `∫_a^b x^r = (b^(r+1) - a^(r+1))/(r+1)`. -/
private lemma powToolkit_integral_rpow {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : r ≠ -1) :
    ∫ x in a..b, x ^ r = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) :=
  integral_rpow (Or.inr ⟨hr, powToolkit_zero_notMem_uIcc ha hb⟩)

/-- Moving the sign of the denominator out: `(x - y)/(-d) = (y - x)/d`. -/
private lemma powToolkit_div_neg_sub (x y d : ℝ) : (x - y) / (-d) = (y - x) / d := by
  rw [div_neg, ← neg_div]; ring

/-- The same with the denominator written `1 - d` (the case `r = -R` of `integral_rpow`). -/
private lemma powToolkit_div_one_sub (x y d : ℝ) : (x - y) / (1 - d) = (y - x) / (d - 1) := by
  rw [show (1 : ℝ) - d = -(d - 1) by ring, powToolkit_div_neg_sub]

/-- `π/2 - π/4 = π/4`, used to evaluate the substituted integrals in the rotation variable. -/
private lemma powToolkit_pi_half_sub_pi_quarter : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by
  field_simp
  ring

/-- Third conjunct: `∫_θ^(π/4) s^(-2) ≤ 1/θ`. -/
private lemma powToolkit_int3 :
    ∀ θ : ℝ, 0 < θ → ∫ s in θ..(Real.pi / 4), s ^ (-2 : ℝ) ≤ 1 / θ := by
  intro θ hθ
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by positivity
  rw [powToolkit_integral_rpow hθ hπ4 (by norm_num : (-2 : ℝ) ≠ -1)]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, Real.rpow_neg_one, one_div]
  rw [powToolkit_div_neg_sub, div_one]
  have h1 : 0 ≤ (Real.pi / 4)⁻¹ := inv_nonneg.mpr hπ4.le
  linarith

/-- Fourth conjunct: `∫_θ^(π/4) s^(-(R+1)) ≤ θ^(-R)/R`. -/
private lemma powToolkit_int4 (R : ℝ) (hR : 1 < R) :
    ∀ θ : ℝ, 0 < θ → ∫ s in θ..(Real.pi / 4), s ^ (-(R + 1)) ≤ θ ^ (-R) / R := by
  intro θ hθ
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hRpos : 0 < R := by linarith
  have hne : -(R + 1) ≠ (-1 : ℝ) := by intro h; linarith
  rw [powToolkit_integral_rpow hθ hπ4 hne]
  rw [show -(R + 1) + 1 = -R by ring, powToolkit_div_neg_sub]
  rw [div_le_div_iff_of_pos_right hRpos]
  have : 0 ≤ (Real.pi / 4) ^ (-R) := Real.rpow_nonneg hπ4.le (-R)
  linarith

/-- Fifth conjunct: `∫_θ^(π/4) s^(-(R+2)) ≤ θ^(-(R+1))/(R+1)`. -/
private lemma powToolkit_int5 (R : ℝ) (hR : 1 < R) :
    ∀ θ : ℝ, 0 < θ →
      ∫ s in θ..(Real.pi / 4), s ^ (-(R + 2)) ≤ θ ^ (-(R + 1)) / (R + 1) := by
  intro θ hθ
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hRpos : 0 < R + 1 := by linarith
  have hne : -(R + 2) ≠ (-1 : ℝ) := by intro h; linarith
  rw [powToolkit_integral_rpow hθ hπ4 hne]
  rw [show -(R + 2) + 1 = -(R + 1) by ring, powToolkit_div_neg_sub]
  rw [div_le_div_iff_of_pos_right hRpos]
  have : 0 ≤ (Real.pi / 4) ^ (-(R + 1)) := Real.rpow_nonneg hπ4.le (-(R + 1))
  linarith

/-- Sixth conjunct: `∫_(π/4)^θ (π/2 - s)^(-3) ≤ (π/2 - θ)^(-2)/2`.  Substitute `u = π/2 - s`
and then use the previous antiderivative. -/
private lemma powToolkit_int6 :
    ∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      ∫ s in (Real.pi / 4)..θ, (Real.pi / 2 - s) ^ (-3 : ℝ) ≤
        (Real.pi / 2 - θ) ^ (-2 : ℝ) / 2 := by
  intro θ hθ
  obtain ⟨hθ4, hθ2⟩ := hθ
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hδ : (0 : ℝ) < Real.pi / 2 - θ := by linarith
  rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-3 : ℝ)) (Real.pi / 2)]
  rw [powToolkit_pi_half_sub_pi_quarter]
  rw [powToolkit_integral_rpow hδ hπ4 (by norm_num : (-3 : ℝ) ≠ -1)]
  rw [show (-3 : ℝ) + 1 = -2 by norm_num, powToolkit_div_neg_sub]
  rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
  have : 0 ≤ (Real.pi / 4) ^ (-2 : ℝ) := Real.rpow_nonneg hπ4.le (-2)
  linarith

/-- Seventh conjunct: `∫_(π/4)^θ (π/2 - s)^(-R) ≤ (π/2 - θ)^(1-R)/(R-1)`. -/
private lemma powToolkit_int7 (R : ℝ) (hR : 1 < R) :
    ∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      ∫ s in (Real.pi / 4)..θ, (Real.pi / 2 - s) ^ (-R) ≤
        (Real.pi / 2 - θ) ^ (1 - R) / (R - 1) := by
  intro θ hθ
  obtain ⟨hθ4, hθ2⟩ := hθ
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hδ : (0 : ℝ) < Real.pi / 2 - θ := by linarith
  have hR1 : (0 : ℝ) < R - 1 := by linarith
  rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-R)) (Real.pi / 2)]
  rw [powToolkit_pi_half_sub_pi_quarter]
  rw [powToolkit_integral_rpow hδ hπ4 (by intro h; linarith)]
  rw [show -R + 1 = 1 - R by ring, powToolkit_div_one_sub]
  rw [div_le_div_iff_of_pos_right hR1]
  have : 0 ≤ (Real.pi / 4) ^ (1 - R) := Real.rpow_nonneg hπ4.le (1 - R)
  linarith

/-- Eighth conjunct: `∫_(π/4)^θ (π/2 - s)^(-(R+2)) ≤ (π/2 - θ)^(-(R+1))/(R+1)`. -/
private lemma powToolkit_int8 (R : ℝ) (hR : 1 < R) :
    ∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      ∫ s in (Real.pi / 4)..θ, (Real.pi / 2 - s) ^ (-(R + 2)) ≤
        (Real.pi / 2 - θ) ^ (-(R + 1)) / (R + 1) := by
  intro θ hθ
  obtain ⟨hθ4, hθ2⟩ := hθ
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hδ : (0 : ℝ) < Real.pi / 2 - θ := by linarith
  have hR1 : (0 : ℝ) < R + 1 := by linarith
  rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-(R + 2))) (Real.pi / 2)]
  rw [powToolkit_pi_half_sub_pi_quarter]
  rw [powToolkit_integral_rpow hδ hπ4 (by intro h; linarith)]
  rw [show -(R + 2) + 1 = -(R + 1) by ring, powToolkit_div_neg_sub]
  rw [div_le_div_iff_of_pos_right hR1]
  have : 0 ≤ (Real.pi / 4) ^ (-(R + 1)) := Real.rpow_nonneg hπ4.le (-(R + 1))
  linarith

theorem powToolkit (R : ℝ) (hR : 1 < R) :
    (∀ s ∈ Set.Ioc (0:ℝ) (Real.pi / 4),
        1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) ≤ (Real.pi ^ 2 / 8) / s ^ 2)
    ∧ (∀ s ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) ≤ (Real.pi ^ 3 / 32) / (Real.pi / 2 - s) ^ 3)
    ∧ (∀ θ : ℝ, 0 < θ → ∫ s in θ..(Real.pi / 4), s ^ (-2 : ℝ) ≤ 1 / θ)
    ∧ (∀ θ : ℝ, 0 < θ → ∫ s in θ..(Real.pi / 4), s ^ (-(R + 1)) ≤ θ ^ (-R) / R)
    ∧ (∀ θ : ℝ, 0 < θ → ∫ s in θ..(Real.pi / 4), s ^ (-(R + 2)) ≤ θ ^ (-(R + 1)) / (R + 1))
    ∧ (∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        ∫ s in (Real.pi / 4)..θ, (Real.pi / 2 - s) ^ (-3 : ℝ) ≤ (Real.pi / 2 - θ) ^ (-2 : ℝ) / 2)
    ∧ (∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        ∫ s in (Real.pi / 4)..θ, (Real.pi / 2 - s) ^ (-R) ≤ (Real.pi / 2 - θ) ^ (1 - R) / (R - 1))
    ∧ (∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        ∫ s in (Real.pi / 4)..θ, (Real.pi / 2 - s) ^ (-(R + 2))
          ≤ (Real.pi / 2 - θ) ^ (-(R + 1)) / (R + 1)) := by
  exact ⟨PowToolkitPieces.trigLeft, PowToolkitPieces.trigRight, powToolkit_int3,
    powToolkit_int4 R hR, powToolkit_int5 R hR, powToolkit_int6, powToolkit_int7 R hR,
    powToolkit_int8 R hR⟩

end Work.FTS.EllipticEst.H2W.WeakPureAux
