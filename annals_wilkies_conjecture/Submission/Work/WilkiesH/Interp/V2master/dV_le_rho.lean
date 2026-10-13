import Mathlib
import Submission.Work.WilkiesH.Interp.V2master.Basic
import Submission.Work.WilkiesH.Interp.V2master.rpow_pow_add_two_le

set_option maxHeartbeats 4000000

namespace Work.WilkiesH.Interp.V2master

/-- Real-arithmetic core of `dV_le_rho`.

For reals `A ≥ 9`, `r ≥ 1`, `b = r^(μ+1)` and any `x` satisfying the `v2` `dV` bound
`x ≤ 8·A^(1/(μ+1))·(b+2)^(μ/(μ+1))`, one has `x + 1 ≤ 25·A·(b/r)`.

Indeed `A^(1/(μ+1)) ≤ A` (as `A ≥ 1`), `(b+2)^(μ/(μ+1)) ≤ 3·r^μ` (as `b = r^(μ+1) ≥ 1`,
whence `b + 2 ≤ 3b`), and `b/r = r^μ`, so the left side is `≤ 24·A·r^μ + 1 ≤ 25·A·r^μ`
because `A·r^μ ≥ 9`. -/
lemma dV_le_rho_aux (μ : ℕ) (A b r x : ℝ) (hA : 9 ≤ A) (hr : 1 ≤ r) (hb : b = r ^ (μ + 1))
    (hx : x ≤ 8 * A ^ (1 / ((μ : ℝ) + 1)) *
      ((b + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1)))) :
    x + 1 ≤ 25 * A * (b / r) := by
  have hrpos : (0 : ℝ) < r := by linarith
  have hb0 : (0 : ℝ) ≤ b := by rw [hb]; exact pow_nonneg (by linarith) _
  have hA1 : 1 ≤ A := by linarith
  have hmu1 : (0 : ℝ) < (μ : ℝ) + 1 := by positivity
  have hinv1 : 1 / ((μ : ℝ) + 1) ≤ 1 := by rw [div_le_one hmu1]; linarith
  have hAroot : A ^ (1 / ((μ : ℝ) + 1)) ≤ A := Real.rpow_le_self_of_one_le hA1 hinv1
  -- `b = r^(μ+1)` makes `(b+2)^(μ/(μ+1)) ≤ 3 r^μ`
  have hb2 : (b + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) ≤ 3 * r ^ μ := by
    rw [hb]
    exact rpow_pow_add_two_le μ r hr
  -- and `b / r = r^μ`
  have hbr : b / r = r ^ μ := by
    rw [hb, pow_succ, mul_div_cancel_right₀ _ (ne_of_gt hrpos)]
  have h8 : 8 * A ^ (1 / ((μ : ℝ) + 1)) * ((b + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1)))
      ≤ 8 * A * (3 * r ^ μ) := by
    have hleft : 8 * A ^ (1 / ((μ : ℝ) + 1)) ≤ 8 * A :=
      mul_le_mul_of_nonneg_left hAroot (by norm_num)
    have hright0 : (0 : ℝ) ≤ (b + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) :=
      Real.rpow_nonneg (by linarith) _
    have h8A0 : (0 : ℝ) ≤ 8 * A := by linarith
    calc 8 * A ^ (1 / ((μ : ℝ) + 1)) * ((b + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1)))
        ≤ (8 * A) * (3 * r ^ μ) := mul_le_mul hleft hb2 hright0 h8A0
      _ = 8 * A * (3 * r ^ μ) := by ring
  have hAr : 1 ≤ A * r ^ μ := by
    have h1r : (1 : ℝ) ≤ r ^ μ := one_le_pow₀ hr
    nlinarith [hA, h1r]
  rw [hbr]
  linarith [hx, h8, hAr]

lemma dV_le_rho (μ g H : ℕ)
    (hd : ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) ≤
      8 * ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
        (((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1))) :
    ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) + 1 ≤
      25 * (((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9) *
        (((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) /
          ((Work.WilkiesH.Interp.V2master.rhoN μ g H : ℕ) : ℝ)) := by
  -- `bV μ g H = (rhoN μ g H)^(μ+1)`
  have hb : ((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) =
      ((rhoN μ g H : ℕ) : ℝ) ^ (μ + 1) := by
    rw [bV_eq_rhoN]
    push_cast
    ring
  -- `rhoN μ g H ≥ 1`
  have hr1 : (1 : ℝ) ≤ ((rhoN μ g H : ℕ) : ℝ) := by
    exact_mod_cast one_le_rhoN μ g H
  -- `(μ+1)! (8g+9) ≥ 9`
  have hA9 : (9 : ℝ) ≤ (((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9) := by
    have hf : (1 : ℝ) ≤ (((μ + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (μ + 1)
    have hg : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg g
    have h89 : (9 : ℝ) ≤ 8 * (g : ℝ) + 9 := by linarith
    calc (9 : ℝ) = 1 * 9 := by ring
      _ ≤ (((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9) :=
          mul_le_mul hf h89 (by norm_num) (by linarith)
  have hmain := dV_le_rho_aux μ ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9))
      (((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ))
      (((rhoN μ g H : ℕ) : ℝ))
      (((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ))
      hA9 hr1 hb hd
  calc ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) + 1
      ≤ 25 * ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) *
          (((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) / ((rhoN μ g H : ℕ) : ℝ)) := hmain
    _ = 25 * (((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9) *
          (((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) / ((rhoN μ g H : ℕ) : ℝ)) := by ring

end Work.WilkiesH.Interp.V2master
