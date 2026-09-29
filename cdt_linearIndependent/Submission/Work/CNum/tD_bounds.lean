import Mathlib
import Submission.Work.CNum.Jfun_defs
import Submission.Work.CNum.tD_aux
import Submission.Work.CNum.u1J_summable
import Submission.Work.CNum.tD_abs_le
import Submission.Work.CNum.bndJ_core

/-! # CNum: the derivative bounds `tD_bounds`

We bound the first and second derivatives of the `m`-th summand `24 log ‖1 + wᵐ‖`
of `Jfun` along the arc where `‖w ψ‖ ≤ rJ`:

* `Summable (fun m => u1J (m+1))` and `‖tD m ψ‖ ≤ u1J m`,
* `|tD2 m ψ| ≤ bndJ m`, which gives both `‖tD2 m ψ‖ ≤ bndJ m` and
  `-tD2 m ψ ≤ bndJ m`.

The second estimate is entirely elementary: `|Re z| ≤ ‖z‖`, the triangle
inequality for the three summands, `‖tanf ψ‖ = ‖tanf2 ψ‖ = uJ`,
`‖1 + (w ψ)^m‖ ≥ 1 - rJ^m > 0`, and monotonicity of powers on `[0, rJ]`.
-/

namespace Work.CNum

open Complex

/-- Product norm bound, in the form needed below. -/
lemma tb_norm_mul_le {a b : ℂ} {A B : ℝ} (hA : 0 ≤ A) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) :
    ‖a * b‖ ≤ A * B := by
  rw [norm_mul]; exact mul_le_mul ha hb (norm_nonneg _) hA

/-- Quotient norm bound against a positive lower bound for the denominator. -/
lemma tb_norm_div_le {a M : ℂ} {B D : ℝ} (hB : 0 ≤ B) (ha : ‖a‖ ≤ B) (hD0 : 0 < D)
    (hD : D ≤ ‖M‖) : ‖a / M‖ ≤ B / D := by
  rw [norm_div]; exact div_le_div₀ hB ha hD0 hD

lemma tb_norm_natCast_sub_one {m : ℕ} (hm : 1 ≤ m) : ‖((m : ℂ) - 1)‖ = (m : ℝ) - 1 := by
  have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hcast : ((m : ℂ) - 1) = (((m : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast]
  exact (RCLike.norm_ofReal ((m : ℝ) - 1)).trans (abs_of_nonneg hm1)

lemma tb_norm_mm1_cast {m : ℕ} (hm : 1 ≤ m) :
    ‖(m : ℂ) * ((m : ℂ) - 1)‖ = (m : ℝ) * ((m : ℝ) - 1) := by
  rw [norm_mul, tb_norm_natCast_sub_one hm, Complex.norm_natCast]

lemma tb_cast_one_le {m : ℕ} (hm : 1 ≤ m) : (0 : ℝ) ≤ (m : ℝ) - 1 := by
  have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

/-- The absolute value of the second derivative of the `m`-th summand of `Jfun` is
dominated by `bndJ m` for `m ≥ 1` and `‖w ψ‖ ≤ rJ`. -/
lemma tb_tD2_abs_le {m : ℕ} (hm : 1 ≤ m) {ψ : ℝ} (hψ : ‖wf ψ‖ ≤ rJ) :
    |tD2 m ψ| ≤ bndJ m := by
  have hM0 : 0 < 1 - rJ ^ m := one_sub_rJ_pow_pos hm
  have hM : 1 - rJ ^ m ≤ ‖(1 : ℂ) + (wf ψ) ^ m‖ := norm_one_add_pow_ge hψ
  -- the three summands, bounded in norm
  have hE1 : ‖(m : ℂ) * ((m : ℂ) - 1) * (wf ψ) ^ (m - 2) * (tanf ψ) ^ 2 / (1 + (wf ψ) ^ m)‖
      ≤ (m : ℝ) * ((m : ℝ) - 1) * ‖wf ψ‖ ^ (m - 2) * uJ ^ 2 / (1 - rJ ^ m) := by
    have hB : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) * ‖wf ψ‖ ^ (m - 2) * uJ ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (tb_cast_one_le hm))
        (pow_nonneg (norm_nonneg _) _)) (sq_nonneg uJ)
    refine tb_norm_div_le hB ?_ hM0 hM
    have hnorm : ‖(m : ℂ) * ((m : ℂ) - 1) * (wf ψ) ^ (m - 2) * (tanf ψ) ^ 2‖
        = (m : ℝ) * ((m : ℝ) - 1) * ‖wf ψ‖ ^ (m - 2) * uJ ^ 2 := by
      rw [norm_mul, norm_mul, tb_norm_mm1_cast hm, norm_pow, norm_pow, norm_tanf]
    exact le_of_eq hnorm
  have hE2 : ‖(m : ℂ) * (wf ψ) ^ (m - 1) * tanf2 ψ / (1 + (wf ψ) ^ m)‖
      ≤ (m : ℝ) * ‖wf ψ‖ ^ (m - 1) * uJ / (1 - rJ ^ m) := by
    have hB : 0 ≤ (m : ℝ) * ‖wf ψ‖ ^ (m - 1) * uJ :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg (norm_nonneg _) _)) uJ_nonneg
    refine tb_norm_div_le hB ?_ hM0 hM
    have hnorm : ‖(m : ℂ) * (wf ψ) ^ (m - 1) * tanf2 ψ‖
        = (m : ℝ) * ‖wf ψ‖ ^ (m - 1) * uJ := by
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, norm_tanf2]
    exact le_of_eq hnorm
  have hE3 : ‖(m : ℂ) ^ 2 * (wf ψ) ^ (2 * m - 2) * (tanf ψ) ^ 2 / (1 + (wf ψ) ^ m) ^ 2‖
      ≤ (m : ℝ) ^ 2 * ‖wf ψ‖ ^ (2 * m - 2) * uJ ^ 2 / (1 - rJ ^ m) ^ 2 := by
    have hD : (1 - rJ ^ m) ^ 2 ≤ ‖((1 : ℂ) + (wf ψ) ^ m) ^ 2‖ := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (le_of_lt hM0) hM 2
    have hB : 0 ≤ (m : ℝ) ^ 2 * ‖wf ψ‖ ^ (2 * m - 2) * uJ ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)) (sq_nonneg uJ)
    refine tb_norm_div_le hB ?_ (pow_pos hM0 2) hD
    have hnorm : ‖(m : ℂ) ^ 2 * (wf ψ) ^ (2 * m - 2) * (tanf ψ) ^ 2‖
        = (m : ℝ) ^ 2 * ‖wf ψ‖ ^ (2 * m - 2) * uJ ^ 2 := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, norm_pow, norm_pow, norm_tanf]
    exact le_of_eq hnorm
  -- triangle inequality for the sum of the three summands
  have htri : ‖(m : ℂ) * ((m : ℂ) - 1) * (wf ψ) ^ (m - 2) * (tanf ψ) ^ 2 / (1 + (wf ψ) ^ m)
        + (m : ℂ) * (wf ψ) ^ (m - 1) * tanf2 ψ / (1 + (wf ψ) ^ m)
        - (m : ℂ) ^ 2 * (wf ψ) ^ (2 * m - 2) * (tanf ψ) ^ 2 / (1 + (wf ψ) ^ m) ^ 2‖
      ≤ (m : ℝ) * ((m : ℝ) - 1) * ‖wf ψ‖ ^ (m - 2) * uJ ^ 2 / (1 - rJ ^ m)
        + (m : ℝ) * ‖wf ψ‖ ^ (m - 1) * uJ / (1 - rJ ^ m)
        + (m : ℝ) ^ 2 * ‖wf ψ‖ ^ (2 * m - 2) * uJ ^ 2 / (1 - rJ ^ m) ^ 2 := by
    have h1 := norm_sub_le
      ((m : ℂ) * ((m : ℂ) - 1) * (wf ψ) ^ (m - 2) * (tanf ψ) ^ 2 / (1 + (wf ψ) ^ m)
        + (m : ℂ) * (wf ψ) ^ (m - 1) * tanf2 ψ / (1 + (wf ψ) ^ m))
      ((m : ℂ) ^ 2 * (wf ψ) ^ (2 * m - 2) * (tanf ψ) ^ 2 / (1 + (wf ψ) ^ m) ^ 2)
    have h2 := norm_add_le
      ((m : ℂ) * ((m : ℂ) - 1) * (wf ψ) ^ (m - 2) * (tanf ψ) ^ 2 / (1 + (wf ψ) ^ m))
      ((m : ℂ) * (wf ψ) ^ (m - 1) * tanf2 ψ / (1 + (wf ψ) ^ m))
    linarith
  have hre : |((m : ℂ) * ((m : ℂ) - 1) * (wf ψ) ^ (m - 2) * (tanf ψ) ^ 2 / (1 + (wf ψ) ^ m)
        + (m : ℂ) * (wf ψ) ^ (m - 1) * tanf2 ψ / (1 + (wf ψ) ^ m)
        - (m : ℂ) ^ 2 * (wf ψ) ^ (2 * m - 2) * (tanf ψ) ^ 2 / (1 + (wf ψ) ^ m) ^ 2).re| ≤
      ‖(m : ℂ) * ((m : ℂ) - 1) * (wf ψ) ^ (m - 2) * (tanf ψ) ^ 2 / (1 + (wf ψ) ^ m)
        + (m : ℂ) * (wf ψ) ^ (m - 1) * tanf2 ψ / (1 + (wf ψ) ^ m)
        - (m : ℂ) ^ 2 * (wf ψ) ^ (2 * m - 2) * (tanf ψ) ^ 2 / (1 + (wf ψ) ^ m) ^ 2‖ :=
    abs_re_le_norm _
  -- reduce the `rJ`-expression to `bndJ m`
  have hc : 24 * ((m : ℝ) * ((m : ℝ) - 1) * ‖wf ψ‖ ^ (m - 2) * uJ ^ 2 / (1 - rJ ^ m)
        + (m : ℝ) * ‖wf ψ‖ ^ (m - 1) * uJ / (1 - rJ ^ m)
        + (m : ℝ) ^ 2 * ‖wf ψ‖ ^ (2 * m - 2) * uJ ^ 2 / (1 - rJ ^ m) ^ 2) ≤ bndJ m :=
    bndJ_core (norm_nonneg _) hψ hm
  simp only [tD2, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 24)]
  linarith

theorem tD_bounds {ψ : ℝ} (hψ : ‖wf ψ‖ ≤ rJ) : Summable (fun m : ℕ => u1J (m + 1)) ∧ (∀ m : ℕ, 1 ≤ m → ‖tD m ψ‖ ≤ u1J m) ∧ (∀ m : ℕ, 1 ≤ m → ‖tD2 m ψ‖ ≤ bndJ m) ∧ (∀ m : ℕ, 1 ≤ m → -tD2 m ψ ≤ bndJ m) := by
  refine ⟨u1J_summable, fun m hm => tD_abs_le hm hψ, fun m hm => ?_, fun m hm => ?_⟩
  · have h := tb_tD2_abs_le hm hψ
    rwa [Real.norm_eq_abs]
  · exact le_trans (neg_le_abs _) (tb_tD2_abs_le hm hψ)

end Work.CNum
