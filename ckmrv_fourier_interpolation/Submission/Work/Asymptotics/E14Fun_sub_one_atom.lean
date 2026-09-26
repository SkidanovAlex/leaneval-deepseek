import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.Residues.ThetaDecay

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-!
# The first-order atom `E₁₄ - 1` at the cusp

`E₁₄ = E₄² E₆`, and both factors have an explicit linear `q`-expansion at `i∞`:
`E₄ = 1 + O(q)`, `E₆ = 1 + O(q)` on `{Im τ ≥ 1}`.  Hence

`E₁₄ - 1 = (E₄² - 1) E₆ + (E₆ - 1)`,  `E₄² - 1 = 2 (E₄ - 1) + (E₄ - 1)²`,

so writing `u = E₄ - 1`, `v = E₆ - 1` and `t = ‖q‖`,

`E₁₄ - 1 = 2u + u² + v + 2uv + u²v`,

and every term is `O(t)` once `0 ≤ t ≤ 1`: the linear terms directly, the quadratic
terms through `t² ≤ t` and the cubic through `t³ ≤ t`.

The inputs are the explicit first-order bound for `E₄` (`E4Fun_sub_one_explicit`) and the
first-order decay of `E₆` (`Work.Residues.E6Fun_decay`), combined with
`‖q‖ = exp (-2 π Im τ)` (`norm_qParamFun`).
-/

/-- Elementary expansion bound: if `‖a - 1‖ ≤ P t`, `‖b - 1‖ ≤ S t` with `P, S ≥ 0` and
`0 ≤ t ≤ 1`, then `‖a ^ 2 * b - 1‖ ≤ (2 P + P² + S + 2 P S + P² S) t`. -/
private lemma norm_sq_mul_sub_one_le {a b : ℂ} {P S t : ℝ}
    (hP : 0 ≤ P) (hS : 0 ≤ S) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : ‖a - 1‖ ≤ P * t) (hb : ‖b - 1‖ ≤ S * t) :
    ‖a ^ 2 * b - 1‖ ≤ (2 * P + P ^ 2 + S + 2 * P * S + P ^ 2 * S) * t := by
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have ht3 : t ^ 3 ≤ t := by nlinarith
  have hU0 : 0 ≤ ‖a - 1‖ := norm_nonneg _
  have hV0 : 0 ≤ ‖b - 1‖ := norm_nonneg _
  have hPt : 0 ≤ P * t := mul_nonneg hP ht0
  have hSt : 0 ≤ S * t := mul_nonneg hS ht0
  have hkey : a ^ 2 * b - 1
      = 2 * (a - 1) + (a - 1) ^ 2 + (b - 1) + 2 * ((a - 1) * (b - 1))
        + (a - 1) ^ 2 * (b - 1) := by ring
  have htri : ‖2 * (a - 1) + (a - 1) ^ 2 + (b - 1) + 2 * ((a - 1) * (b - 1))
        + (a - 1) ^ 2 * (b - 1)‖
      ≤ 2 * ‖a - 1‖ + ‖a - 1‖ ^ 2 + ‖b - 1‖ + 2 * (‖a - 1‖ * ‖b - 1‖)
        + ‖a - 1‖ ^ 2 * ‖b - 1‖ := by
    have h1 := norm_add_le (2 * (a - 1) + (a - 1) ^ 2 + (b - 1) + 2 * ((a - 1) * (b - 1)))
      ((a - 1) ^ 2 * (b - 1))
    have h2 := norm_add_le (2 * (a - 1) + (a - 1) ^ 2 + (b - 1)) (2 * ((a - 1) * (b - 1)))
    have h3 := norm_add_le (2 * (a - 1) + (a - 1) ^ 2) (b - 1)
    have h4 := norm_add_le (2 * (a - 1)) ((a - 1) ^ 2)
    have e1 : ‖2 * (a - 1)‖ = 2 * ‖a - 1‖ := by rw [norm_mul]; norm_num
    have e2 : ‖(a - 1) ^ 2‖ = ‖a - 1‖ ^ 2 := norm_pow _ _
    have e3 : ‖2 * ((a - 1) * (b - 1))‖ = 2 * (‖a - 1‖ * ‖b - 1‖) := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have e4 : ‖(a - 1) ^ 2 * (b - 1)‖ = ‖a - 1‖ ^ 2 * ‖b - 1‖ := by rw [norm_mul, norm_pow]
    linarith
  have e1 : 2 * ‖a - 1‖ ≤ 2 * (P * t) := by linarith
  have e2 : ‖a - 1‖ ^ 2 ≤ (P * t) ^ 2 := pow_le_pow_left₀ hU0 ha 2
  have e3 : 2 * (‖a - 1‖ * ‖b - 1‖) ≤ 2 * ((P * t) * (S * t)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul ha hb hV0 hPt) (by norm_num)
  have e4 : ‖a - 1‖ ^ 2 * ‖b - 1‖ ≤ (P * t) ^ 2 * (S * t) :=
    mul_le_mul e2 hb hV0 (by positivity)
  have hmid : ‖2 * (a - 1) + (a - 1) ^ 2 + (b - 1) + 2 * ((a - 1) * (b - 1))
        + (a - 1) ^ 2 * (b - 1)‖
      ≤ 2 * (P * t) + (P * t) ^ 2 + S * t + 2 * ((P * t) * (S * t)) + (P * t) ^ 2 * (S * t) := by
    linarith
  have hfin : 2 * (P * t) + (P * t) ^ 2 + S * t + 2 * ((P * t) * (S * t)) + (P * t) ^ 2 * (S * t)
      ≤ (2 * P + P ^ 2 + S + 2 * P * S + P ^ 2 * S) * t := by
    have hP2 : 0 ≤ P ^ 2 := by positivity
    have hPS : 0 ≤ 2 * P * S := by positivity
    have hP2S : 0 ≤ P ^ 2 * S := by positivity
    have k1 : P ^ 2 * t ^ 2 ≤ P ^ 2 * t := mul_le_mul_of_nonneg_left ht2 hP2
    have k2 : 2 * P * S * t ^ 2 ≤ 2 * P * S * t := mul_le_mul_of_nonneg_left ht2 hPS
    have k3 : P ^ 2 * S * t ^ 3 ≤ P ^ 2 * S * t := mul_le_mul_of_nonneg_left ht3 hP2S
    nlinarith [k1, k2, k3]
  rw [hkey]
  linarith

/-- **The atom `E₁₄ - 1` is `O(q)` at the cusp.**  There is `C > 0` with
`‖E₁₄(τ) - 1‖ ≤ C ‖q(τ)‖` for every `τ` with `Im τ ≥ 1`. -/
theorem E14Fun_sub_one_atom :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖Work.Kernels.E14Fun z - 1‖ ≤ C * ‖Work.Kernels.qParamFun z‖ := by
  obtain ⟨C6, hC6pos, hC6⟩ := Work.Residues.E6Fun_decay
  refine ⟨2 * 20000 + 20000 ^ 2 + C6 + 2 * 20000 * C6 + 20000 ^ 2 * C6 + 1, by positivity,
    fun z hz => ?_⟩
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [norm_qParamFun z, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hu : ‖Work.Kernels.E4Fun z - 1‖ ≤ 20000 * ‖Work.Kernels.qParamFun z‖ :=
    E4Fun_sub_one_explicit hz
  have hv : ‖Work.Kernels.E6Fun z - 1‖ ≤ C6 * ‖Work.Kernels.qParamFun z‖ := by
    simpa only [← norm_qParamFun z] using hC6 z hz
  have hmain := norm_sq_mul_sub_one_le (a := Work.Kernels.E4Fun z)
    (b := Work.Kernels.E6Fun z) (P := 20000) (S := C6) (t := ‖Work.Kernels.qParamFun z‖)
    (by norm_num) hC6pos.le hq0 hq1 hu hv
  have heq : Work.Kernels.E14Fun z = Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z := rfl
  calc ‖Work.Kernels.E14Fun z - 1‖
      = ‖Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z - 1‖ := by rw [heq]
    _ ≤ (2 * 20000 + 20000 ^ 2 + C6 + 2 * 20000 * C6 + 20000 ^ 2 * C6)
          * ‖Work.Kernels.qParamFun z‖ := hmain
    _ ≤ (2 * 20000 + 20000 ^ 2 + C6 + 2 * 20000 * C6 + 20000 ^ 2 * C6 + 1)
          * ‖Work.Kernels.qParamFun z‖ := by
        apply mul_le_mul_of_nonneg_right _ hq0
        linarith

end

end Work.Asymptotics
