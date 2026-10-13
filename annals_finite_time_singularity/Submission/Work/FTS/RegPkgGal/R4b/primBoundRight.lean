import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The right-endpoint bound for `Γ(θ)/sin(2θ)`

`Γ α θ = (sin θ · cos²θ)^α` vanishes like `θ^{2α}` as `θ → π/2⁻`, while `sin(2θ)` vanishes
linearly.  This file proves that on the right half interval `[π/4, π/2)` the quotient is
dominated by `(π/2 - θ)^{2α-1}`, i.e. the primitive `∫^θ Γ/sin(2·)` grows like `Γ` itself:

  `Γ α t / sin(2t) ≤ N · (π/2 - t)^{2α-1}`   for `π/4 ≤ t < π/2`.

## Mathematics

Write `δ = π/2 - t ∈ (0, π/4]`, `s = sin δ`, `c = cos δ`.  Then
`sin t = cos δ = c`, `cos t = sin δ = s`, `sin(2t) = 2sc`, so

  `Γ α t / sin(2t) = c^α s^{2α} / (2sc) = (1/2)·c^{α-1}·s^{2α-1}`.

Both factors are comparable with `δ`-powers: `c ∈ [√2/2, 1]` because `δ ∈ (0, π/4]`, and
`sin δ` is squeezed between `(2/π)δ ≤ sin δ ≤ δ` (Jordan's inequality and `sin ≤ id`).  Hence
`c^{α-1} ≤ max 1 ((√2/2)^{α-1})` and `s^{2α-1} ≤ max 1 ((2/π)^{2α-1})·δ^{2α-1}`, which gives the
statement with `N = (max 1 ((√2/2)^{α-1}))·(max 1 ((2/π)^{2α-1}))/2`.  (The bound in fact holds
for every real `α`; positivity of `α` is not used.)

## Formalisation note

The statement is fed to `Work.FTS.RegPkgGal.R4b.van_of_dthvan`, where one integrates the
`D_θ`-derivative of the class datum `|D_θ g| ≤ Cθ z²Γ` to obtain `|g| ≤ Cv Γ`.
-/

set_option linter.unusedVariables false

namespace Work.FTS.RegPkgGal.R4b

theorem primBoundRight {α : ℝ} (hα : 0 < α) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ t : ℝ, Real.pi / 4 ≤ t → t < Real.pi / 2 →
      Work.FTS.Regularity.Gamma α t / Real.sin (2 * t) ≤ N * (Real.pi / 2 - t) ^ (2 * α - 1) := by
  refine ⟨max 1 ((Real.sqrt 2 / 2) ^ (α - 1))
      * max 1 ((2 / Real.pi) ^ (2 * α - 1)) / 2, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ max 1 ((Real.sqrt 2 / 2) ^ (α - 1)) :=
      le_trans zero_le_one (le_max_left _ _)
    have h2 : (0 : ℝ) ≤ max 1 ((2 / Real.pi) ^ (2 * α - 1)) :=
      le_trans zero_le_one (le_max_left _ _)
    exact div_nonneg (mul_nonneg h1 h2) (by norm_num)
  · intro t ht1 ht2
    -- put `δ = π/2 - t`
    set δ : ℝ := Real.pi / 2 - t with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hδle : δ ≤ Real.pi / 4 := by rw [hδ]; linarith
    have hs : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδpos (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos δ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [hδle, Real.pi_pos]⟩
    -- the trigonometric identifications `sin t = cos δ`, `cos t = sin δ`
    have hsin_t : Real.sin t = Real.cos δ := by
      rw [hδ]; exact (Real.cos_pi_div_two_sub t).symm
    have hcos_t : Real.cos t = Real.sin δ := by
      rw [hδ]; exact (Real.sin_pi_div_two_sub t).symm
    -- the exact evaluation of the quotient
    have hkey : Work.FTS.Regularity.Gamma α t / Real.sin (2 * t)
        = (1 / 2) * Real.cos δ ^ (α - 1) * Real.sin δ ^ (2 * α - 1) := by
      have hG : Work.FTS.Regularity.Gamma α t = Real.cos δ ^ α * Real.sin δ ^ (2 * α) := by
        have h1 : Work.FTS.Regularity.Gamma α t = (Real.cos δ * Real.sin δ ^ (2 : ℕ)) ^ α := by
          simp only [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma]
          rw [hsin_t, hcos_t]
        rw [h1, Real.mul_rpow hc.le (by positivity)]
        congr 1
        rw [show Real.sin δ ^ (2 : ℕ) = Real.sin δ ^ (2 : ℝ) from
          by norm_num [Real.rpow_natCast]]
        rw [← Real.rpow_mul hs.le 2 α]
      have hsin2 : Real.sin (2 * t) = 2 * Real.cos δ * Real.sin δ := by
        rw [Real.sin_two_mul, hsin_t, hcos_t]
      rw [hG, hsin2]
      rw [Real.rpow_sub hc α 1, Real.rpow_sub hs (2 * α) 1, Real.rpow_one, Real.rpow_one]
      field_simp
    -- `√2/2 ≤ cos δ`, because `δ ≤ π/4`
    have hcge : Real.sqrt 2 / 2 ≤ Real.cos δ := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := δ) (y := Real.pi / 4)
        hδpos.le (by linarith [Real.pi_pos]) hδle
      rwa [Real.cos_pi_div_four] at h
    -- the `cos`-factor is bounded
    have hcb : Real.cos δ ^ (α - 1) ≤ max 1 ((Real.sqrt 2 / 2) ^ (α - 1)) := by
      rcases lt_or_ge α 1 with h | h
      · exact le_trans (Real.rpow_le_rpow_of_nonpos (by positivity) hcge (by linarith))
          (le_max_right _ _)
      · have h2 : Real.cos δ ^ (α - 1) ≤ (1 : ℝ) ^ (α - 1) :=
          Real.rpow_le_rpow hc.le (Real.cos_le_one δ) (by linarith)
        rw [Real.one_rpow] at h2
        exact le_trans h2 (le_max_left _ _)
    -- the `sin`-factor is bounded
    have hsb : Real.sin δ ^ (2 * α - 1)
        ≤ max 1 ((2 / Real.pi) ^ (2 * α - 1)) * δ ^ (2 * α - 1) := by
      rcases lt_or_ge (2 * α - 1) 0 with h | h
      · have hj : 2 / Real.pi * δ ≤ Real.sin δ :=
          Real.mul_le_sin hδpos.le (by linarith [hδle, Real.pi_pos])
        have h1 : Real.sin δ ^ (2 * α - 1) ≤ (2 / Real.pi * δ) ^ (2 * α - 1) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hj (le_of_lt h)
        have h2 : (2 / Real.pi * δ) ^ (2 * α - 1)
            = (2 / Real.pi) ^ (2 * α - 1) * δ ^ (2 * α - 1) :=
          Real.mul_rpow (by positivity) hδpos.le
        calc Real.sin δ ^ (2 * α - 1) ≤ (2 / Real.pi) ^ (2 * α - 1) * δ ^ (2 * α - 1) := by
              rw [← h2]; exact h1
          _ ≤ max 1 ((2 / Real.pi) ^ (2 * α - 1)) * δ ^ (2 * α - 1) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hδpos.le _)
      · have h1 : Real.sin δ ^ (2 * α - 1) ≤ δ ^ (2 * α - 1) :=
          Real.rpow_le_rpow hs.le (Real.sin_le hδpos.le) h
        calc Real.sin δ ^ (2 * α - 1) ≤ 1 * δ ^ (2 * α - 1) := by rw [one_mul]; exact h1
          _ ≤ max 1 ((2 / Real.pi) ^ (2 * α - 1)) * δ ^ (2 * α - 1) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hδpos.le _)
    have hMcnn : (0 : ℝ) ≤ max 1 ((Real.sqrt 2 / 2) ^ (α - 1)) :=
      le_trans zero_le_one (le_max_left _ _)
    calc Work.FTS.Regularity.Gamma α t / Real.sin (2 * t)
        = 1 / 2 * (Real.cos δ ^ (α - 1) * Real.sin δ ^ (2 * α - 1)) := by
          rw [hkey]; ring
      _ ≤ 1 / 2 * (max 1 ((Real.sqrt 2 / 2) ^ (α - 1))
            * (max 1 ((2 / Real.pi) ^ (2 * α - 1)) * δ ^ (2 * α - 1))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hcb hsb (Real.rpow_nonneg hs.le _) hMcnn
      _ = max 1 ((Real.sqrt 2 / 2) ^ (α - 1))
            * max 1 ((2 / Real.pi) ^ (2 * α - 1)) / 2 * δ ^ (2 * α - 1) := by ring
      _ = max 1 ((Real.sqrt 2 / 2) ^ (α - 1))
            * max 1 ((2 / Real.pi) ^ (2 * α - 1)) / 2 * (Real.pi / 2 - t) ^ (2 * α - 1) := by
          rw [hδ]

end Work.FTS.RegPkgGal.R4b
