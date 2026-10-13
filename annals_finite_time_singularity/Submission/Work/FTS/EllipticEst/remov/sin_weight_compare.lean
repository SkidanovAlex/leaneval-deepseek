import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

theorem sin_weight_compare (e : ℝ) (he : 0 ≤ e) :
    (∀ θ ∈ Set.Ioc 0 (Real.pi / 4),
        Real.rpow (Real.sin (2 * θ)) (-e) ≤ (Real.pi / 4) ^ e * Real.rpow θ (-e)) ∧
    (∀ θ ∈ Set.Ioc 0 (Real.pi / 4),
        Real.rpow θ (-e) ≤ 2 ^ e * Real.rpow (Real.sin (2 * θ)) (-e)) ∧
    (∀ θ ∈ Set.Ioc (Real.pi / 4) (Real.pi / 2),
        Real.rpow (Real.sin (2 * θ)) (-e) ≤ (Real.pi / 4) ^ e * Real.rpow (Real.pi / 2 - θ) (-e)) ∧
    (∀ θ ∈ Set.Ioc (Real.pi / 4) (Real.pi / 2),
        Real.rpow (Real.pi / 2 - θ) (-e) ≤ 2 ^ e * Real.rpow (Real.sin (2 * θ)) (-e)) ∧
    (∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 1) := by
  -- On `[0, π/4]` we have `sin (2θ) ≥ (4/π) θ` (concavity of `sin` on `[0, π/2]`),
  -- and on `[0, π/2]` we have `sin (2θ) ≤ 2θ`.  Since `t ↦ t^{-e}` is antitone
  -- (`e ≥ 0`), this gives both comparisons between `sin (2θ)` and `θ`; the two
  -- comparisons with `π/2 - θ` follow by substituting `θ ↦ π/2 - θ` and
  -- `sin (π - x) = sin x`.
  have key_left : ∀ θ ∈ Set.Icc 0 (Real.pi / 4),
      (Real.sin (2 * θ)) ^ (-e) ≤ (Real.pi / 4) ^ e * θ ^ (-e) := by
    intro θ hθ
    obtain ⟨hθnn, hθle⟩ := hθ
    rcases eq_or_lt_of_le hθnn with hθ0 | hθpos
    · -- boundary `θ = 0`: both sides are `0` (or both `1` when `e = 0`)
      subst hθ0
      simp only [mul_zero, Real.sin_zero]
      rcases eq_or_lt_of_le he with he0 | hepos
      · subst he0; norm_num
      · have hne : (-e) ≠ 0 := by linarith
        rw [Real.zero_rpow hne]; positivity
    · have h2θpos : 0 < 2 * θ := by linarith
      have h2θle : 2 * θ ≤ Real.pi / 2 := by linarith
      have hlow : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
        rw [show (4 / Real.pi) * θ = (2 / Real.pi) * (2 * θ) by ring]
        exact Real.mul_le_sin (le_of_lt h2θpos) h2θle
      have hbpos : 0 < (4 / Real.pi) * θ := by positivity
      have hapos : 0 < Real.sin (2 * θ) := lt_of_lt_of_le hbpos hlow
      calc (Real.sin (2 * θ)) ^ (-e)
          = ((Real.sin (2 * θ)) ^ e)⁻¹ := Real.rpow_neg (le_of_lt hapos) e
        _ ≤ (((4 / Real.pi) * θ) ^ e)⁻¹ :=
              (inv_le_inv₀ (Real.rpow_pos_of_pos hapos e) (Real.rpow_pos_of_pos hbpos e)).mpr
                (Real.rpow_le_rpow (le_of_lt hbpos) hlow he)
        _ = ((4 / Real.pi) * θ) ^ (-e) := (Real.rpow_neg (le_of_lt hbpos) e).symm
        _ = (Real.pi / 4) ^ e * θ ^ (-e) := by
              rw [Real.mul_rpow (by positivity) (le_of_lt hθpos),
                  Real.rpow_neg_eq_inv_rpow (4 / Real.pi) e, inv_div]
  have key_right : ∀ θ ∈ Set.Icc 0 (Real.pi / 4),
      θ ^ (-e) ≤ 2 ^ e * (Real.sin (2 * θ)) ^ (-e) := by
    intro θ hθ
    obtain ⟨hθnn, hθle⟩ := hθ
    rcases eq_or_lt_of_le hθnn with hθ0 | hθpos
    · -- boundary `θ = 0`
      subst hθ0
      simp only [mul_zero, Real.sin_zero]
      rcases eq_or_lt_of_le he with he0 | hepos
      · subst he0; norm_num
      · have hne : (-e) ≠ 0 := by linarith
        rw [Real.zero_rpow hne]; positivity
    · have h2θpos : 0 < 2 * θ := by linarith
      have h2θle : 2 * θ ≤ Real.pi / 2 := by linarith
      have hapos : 0 < Real.sin (2 * θ) := by
        have h := Real.mul_le_sin (le_of_lt h2θpos) h2θle
        have h2 : 0 < (2 / Real.pi) * (2 * θ) := by positivity
        linarith
      have hbase : θ⁻¹ ≤ 2 * (Real.sin (2 * θ))⁻¹ := by
        have hsinle : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (le_of_lt h2θpos)
        have hinv : (2 * θ)⁻¹ ≤ (Real.sin (2 * θ))⁻¹ :=
          (inv_le_inv₀ h2θpos hapos).mpr hsinle
        have hθinv : θ⁻¹ = 2 * (2 * θ)⁻¹ := by rw [mul_inv]; ring
        rw [hθinv]; linarith
      calc θ ^ (-e) = θ⁻¹ ^ e := Real.rpow_neg_eq_inv_rpow θ e
        _ ≤ (2 * (Real.sin (2 * θ))⁻¹) ^ e :=
              Real.rpow_le_rpow (inv_nonneg.mpr (le_of_lt hθpos)) hbase he
        _ = 2 ^ e * (Real.sin (2 * θ)) ^ (-e) := by
              rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr (le_of_lt hapos)),
                  ← Real.rpow_neg_eq_inv_rpow (Real.sin (2 * θ)) e]
  have key_sub : ∀ θ : ℝ, Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
    intro θ
    rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro θ hθ
    obtain ⟨h1, h2⟩ := hθ
    exact key_left θ ⟨le_of_lt h1, h2⟩
  · intro θ hθ
    obtain ⟨h1, h2⟩ := hθ
    exact key_right θ ⟨le_of_lt h1, h2⟩
  · intro θ hθ
    obtain ⟨h1, h2⟩ := hθ
    have hφ : Real.pi / 2 - θ ∈ Set.Icc 0 (Real.pi / 4) := ⟨by linarith, by linarith⟩
    rw [← key_sub θ]
    exact key_left (Real.pi / 2 - θ) hφ
  · intro θ hθ
    obtain ⟨h1, h2⟩ := hθ
    have hφ : Real.pi / 2 - θ ∈ Set.Icc 0 (Real.pi / 4) := ⟨by linarith, by linarith⟩
    rw [← key_sub θ]
    exact key_right (Real.pi / 2 - θ) hφ
  · intro θ hθ
    obtain ⟨h1, h2⟩ := hθ
    exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith),
      Real.sin_le_one _⟩

end Work.FTS.EllipticEst.remov
