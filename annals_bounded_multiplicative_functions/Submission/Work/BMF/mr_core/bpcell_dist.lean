import Mathlib
import Submission.Work.BMF.mr_direct.dist_scale_transfer_wide
import Submission.Work.BMF.mr_direct.D_mono
import Submission.Work.BMF.mr_direct.nat_cpow_I_norm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

/-- **Distribution of the "bad cell" pretentious distance.**

If `𝔻 g (n ↦ n^{iu}) ≥ B` at the single scale `Y` for all `|u| ≤ 4 T₀`, with `B ≥ 8`
and `Y ≥ 16⁸`, and if `Y^{1/8} ≤ X^{1/4}/16`, then the lower bound `√(B²/2)` holds at
*every* scale `x ≥ X^{1/4}/16`.

The proof combines the wide scale-transfer `dist_scale_transfer_wide` (valid on
`[Y^{1/8}, 16Y]`, hence on all `x` with `X^{1/4}/16 ≤ x ≤ 16Y` since `Y^{1/8} ≤ X^{1/4}/16`)
with monotonicity of `𝔻` in the truncation against the raw hypothesis at `Y`, which covers
all `x ≥ Y` (and a fortiori all `x > 16Y`). -/
theorem bpcell_dist {B T₀ Y X : ℝ} {g : ℕ → ℂ}
    (hB : 8 ≤ B) (hY : (16 : ℝ) ^ 8 ≤ Y) (hgb : ∀ n, ‖g n‖ ≤ 1)
    (hhyp : ∀ u : ℝ, |u| ≤ 4 * T₀ →
      B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y)
    (hX : 0 ≤ X) (hlow : Y ^ (1 / 8 : ℝ) ≤ X ^ (1 / 4 : ℝ) / 16) :
    ∀ x : ℝ, X ^ (1 / 4 : ℝ) / 16 ≤ x → x ≤ 16 * X → ∀ u : ℝ, |u| ≤ 4 * T₀ →
      Real.sqrt (B ^ 2 / 2) ≤
        BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) x := by
  intro x hxlow _hxupp u hu
  -- The hypothesis at scale `Y` transfers to the whole window `[Y^{1/8}, 16Y]`.
  have hlow' : Y ^ (1 / 8 : ℝ) ≤ x := le_trans hlow hxlow
  by_cases hx : x ≤ 16 * Y
  · exact Work.BMF.mr_direct.dist_scale_transfer_wide g hgb B (4 * T₀) Y hB hY hhyp
      x hlow' hx u hu
  · -- `x > 16Y ≥ Y`: the raw hypothesis at `Y` plus monotonicity of `𝔻` suffices.
    have hYpos : 0 < Y := by
      have : (0 : ℝ) < 16 ^ 8 := by norm_num
      linarith
    have hxY : Y ≤ x := by
      have h' : 16 * Y < x := lt_of_not_ge hx
      nlinarith
    have hψ : ∀ n : ℕ, ‖(n : ℂ) ^ (Complex.I * u)‖ ≤ 1 :=
      fun n => Work.BMF.mr_direct.nat_cpow_I_norm_le n u
    have hDY : B ≤ BoundedMultiplicativeFunctions.𝔻 g
        (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y := hhyp u hu
    have hmono : BoundedMultiplicativeFunctions.𝔻 g
          (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y
        ≤ BoundedMultiplicativeFunctions.𝔻 g
          (fun n ↦ (n : ℂ) ^ (Complex.I * u)) x :=
      Work.BMF.mr_direct.D_mono g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) hgb hψ hxY
    have hBpos : 0 < B := by linarith
    have hsqrt : Real.sqrt (B ^ 2 / 2) ≤ B := by
      rw [Real.sqrt_le_iff]
      exact ⟨hBpos.le, by nlinarith⟩
    linarith

end Work.BMF.mr_core
