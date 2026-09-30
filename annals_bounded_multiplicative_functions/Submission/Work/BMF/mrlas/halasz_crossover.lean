import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.mrlas.Wsup_measurable
import Submission.Work.BMF.mrlas.Wsup_le_Zrcp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Halász "crossover" bound

This file proves `Work.BMF.mrlas.halasz_crossover`, the lemma requested by the
`halasz_series_bound` development.

It has two conjuncts.

* The first is a real-analysis statement: given two pointwise upper bounds for a
  function `g` on the interval `[1/L, 1]`, namely `g α ≤ Z - m + C₁` and the
  sharper `g α ≤ Z - log (α L) + C₁`, the weighted integral `∫_{1/L}^{1} exp (g α)/α dα`
  is controlled by `C · exp (Z + C₁) · ((1 + m) exp (-m) + 1)`.  The *second*
  hypothesis alone already gives `exp (g α) ≤ exp (Z + C₁) / (α L)`, whence
  `exp (g α)/α ≤ exp (Z + C₁)/(α² L)` whose integral over `[1/L, 1]` equals
  `exp (Z + C₁) (1 - 1/L) ≤ exp (Z + C₁)`; the extra factors `(1 + m) exp (-m) + 1`
  are `≥ 1`, so `C = 1` works.  (The first hypothesis is not needed; it is kept
  because it is part of the interface requested by the caller.)

* The second conjunct records the two basic facts about `Wsup` that the caller
  needs: `α ↦ Wsup f x α T` is measurable, and for `α ≥ 0` it is bounded by the
  trivial `Zrcp x = Σ_{p ≤ x} 1/p`.
-/

namespace Work.BMF.mrlas

open MeasureTheory

/-- Pointwise comparison: from `g α ≤ Z - log (α L) + C₁` on `α ≥ 1/L` we get
`exp (g α)/α ≤ (exp (Z + C₁)/L)/α²`. -/
lemma crossover_pointwise (g : ℝ → ℝ) (L Z C₁ α : ℝ) (hL : 1 ≤ L)
    (hα1 : 1 / L ≤ α)
    (h : g α ≤ Z - Real.log (α * L) + C₁) :
    Real.exp (g α) / α ≤ (Real.exp (Z + C₁) / L) / α ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hαpos : 0 < α := lt_of_lt_of_le (by positivity) hα1
  have hαL : 0 < α * L := mul_pos hαpos hLpos
  have hexp : Real.exp (g α) ≤ Real.exp (Z + C₁) / (α * L) := by
    calc Real.exp (g α) ≤ Real.exp (Z - Real.log (α * L) + C₁) := Real.exp_le_exp.mpr h
      _ = Real.exp (Z + C₁) * Real.exp (-(Real.log (α * L))) := by
            rw [show Z - Real.log (α * L) + C₁ = (Z + C₁) + -(Real.log (α * L)) by ring,
                Real.exp_add]
      _ = Real.exp (Z + C₁) * (α * L)⁻¹ := by rw [Real.exp_neg, Real.exp_log hαL]
      _ = Real.exp (Z + C₁) / (α * L) := by rw [div_eq_mul_inv]
  calc Real.exp (g α) / α ≤ (Real.exp (Z + C₁) / (α * L)) / α :=
        div_le_div_of_nonneg_right hexp (le_of_lt hαpos)
    _ = (Real.exp (Z + C₁) / L) / α ^ 2 := by
        rw [div_div, div_div, show (α * L) * α = L * α ^ 2 by ring]

/-- The exact value of `∫_{a}^{b} c/α²` for `0 < a ≤ b`. -/
lemma integral_div_sq (c a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ α in a..b, c / α ^ 2) = c * (1 / a - 1 / b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hcont : ContinuousOn (fun x : ℝ => -c * x⁻¹) (Set.Icc a b) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ continuousOn_id
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hInt : IntervalIntegrable (fun x : ℝ => c * (x ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ ((continuous_id.pow 2).continuousOn)
    intro x hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le ha hx.1
    exact pow_ne_zero 2 (ne_of_gt hx0)
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt (fun y : ℝ => -c * y⁻¹) (c * (x ^ 2)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans ha hx.1)
    have h := (hasDerivAt_inv hx0).const_mul (-c)
    convert h using 1
    ring
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hInt
  rw [show (∫ α in a..b, c / α ^ 2) = ∫ α in a..b, c * (α^2)⁻¹ from by
        simp only [div_eq_mul_inv]]
  rw [key]
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  field_simp
  ring

/-- The integral bound of the crossover lemma: the second pointwise hypothesis alone
gives `∫_{1/L}^{1} exp (g α)/α dα ≤ exp (Z + C₁)`. -/
lemma crossover_integral (g : ℝ → ℝ) (L Z C₁ : ℝ) (hL : 1 ≤ L)
    (h2 : ∀ α, 1 / L ≤ α → α ≤ 1 → g α ≤ Z - Real.log (α * L) + C₁)
    (hInt : IntervalIntegrable (fun α => Real.exp (g α) / α) volume (1 / L) 1) :
    (∫ α in (1 / L)..1, Real.exp (g α) / α) ≤ Real.exp (Z + C₁) := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have h1L : (0:ℝ) < 1 / L := div_pos one_pos hLpos
  have hle : 1 / L ≤ 1 := by rw [div_le_iff₀ hLpos]; linarith
  have hIntG : IntervalIntegrable (fun α : ℝ => Real.exp (Z + C₁) / L / α ^ 2)
      volume (1 / L) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]
    apply ContinuousOn.div continuousOn_const
    · exact (continuous_id.pow 2).continuousOn
    · intro x hx
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le h1L hx.1
      exact pow_ne_zero 2 (ne_of_gt hx0)
  calc (∫ α in (1 / L)..1, Real.exp (g α) / α)
      ≤ ∫ α in (1 / L)..1, Real.exp (Z + C₁) / L / α ^ 2 :=
        intervalIntegral.integral_mono_on hle hInt hIntG
          (fun x hx => crossover_pointwise g L Z C₁ x hL hx.1 (h2 x hx.1 hx.2))
    _ = Real.exp (Z + C₁) * (1 - 1 / L) := by
        rw [integral_div_sq _ _ _ (by positivity) hle]
        field_simp
    _ ≤ Real.exp (Z + C₁) :=
        mul_le_of_le_one_right (le_of_lt (Real.exp_pos _)) (by
          have : (0:ℝ) ≤ 1 / L := le_of_lt h1L
          linarith)

theorem halasz_crossover :
    (∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℝ) (L Z m C₁ : ℝ), 1 ≤ L → 0 ≤ m → 0 ≤ C₁ →
        IntervalIntegrable (fun α : ℝ => Real.exp (g α) / α) MeasureTheory.volume (1 / L) 1 →
        (∀ α : ℝ, 1 / L ≤ α → α ≤ 1 → g α ≤ Z - m + C₁) →
        (∀ α : ℝ, 1 / L ≤ α → α ≤ 1 → g α ≤ Z - Real.log (α * L) + C₁) →
        (∫ α in (1 / L)..1, Real.exp (g α) / α)
          ≤ C * Real.exp (Z + C₁) * ((1 + m) * Real.exp (-m) + 1)) ∧
    (∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ (x T : ℝ),
        Measurable (fun α : ℝ => Work.BMF.Wsup f x α T) ∧
        ∀ α : ℝ, 0 ≤ α → Work.BMF.Wsup f x α T ≤ Work.BMF.Zrcp x) := by
  refine ⟨?_, ?_⟩
  · refine ⟨1, one_pos, ?_⟩
    intro g L Z m C₁ hL hm hC₁ hInt h1 h2
    have hE : 0 < Real.exp (Z + C₁) := Real.exp_pos _
    have hge : (1:ℝ) ≤ (1 + m) * Real.exp (-m) + 1 := by
      have : (0:ℝ) ≤ (1 + m) * Real.exp (-m) :=
        mul_nonneg (by linarith) (le_of_lt (Real.exp_pos _))
      linarith
    calc (∫ α in (1 / L)..1, Real.exp (g α) / α)
        ≤ Real.exp (Z + C₁) := crossover_integral g L Z C₁ hL h2 hInt
      _ ≤ Real.exp (Z + C₁) * ((1 + m) * Real.exp (-m) + 1) :=
          le_mul_of_one_le_right (le_of_lt hE) hge
      _ = 1 * Real.exp (Z + C₁) * ((1 + m) * Real.exp (-m) + 1) := by ring
  · intro f hb x T
    exact ⟨Wsup_measurable f x T, fun α hα => Wsup_le_Zrcp f hb x T α hα⟩

end Work.BMF.mrlas
