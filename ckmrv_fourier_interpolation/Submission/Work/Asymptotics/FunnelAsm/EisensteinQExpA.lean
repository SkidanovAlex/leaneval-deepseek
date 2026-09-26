import Mathlib
import Submission.Work.Asymptotics.PGFar.Defs
import Submission.Work.Kernels.E2Laws
import Submission.Work.Asymptotics.FunnelAsm.E_jdiff_smallA

open UpperHalfPlane

namespace Work.Asymptotics

/-- `((n : ℝ) + 3)^2 ≤ 9 * 3^n`. -/
lemma sq_add_three_le (n : ℕ) : ((n : ℝ) + 3) ^ 2 ≤ 9 * 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k <;> norm_num
    · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
      have h1 : (k : ℝ) + 4 ≤ (3 / 2) * ((k : ℝ) + 3) := by linarith
      have h2 : ((k : ℝ) + 4) ^ 2 ≤ ((3 / 2) * ((k : ℝ) + 3)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      have h3 : ((3 / 2) * ((k : ℝ) + 3)) ^ 2 = (9 / 4) * ((k : ℝ) + 3) ^ 2 := by ring
      have h4 : (9 / 4 : ℝ) * ((k : ℝ) + 3) ^ 2 ≤ 3 * ((k : ℝ) + 3) ^ 2 := by
        nlinarith [sq_nonneg ((k : ℝ) + 3)]
      have hgoal : (9 : ℝ) * 3 ^ (k + 1) = 3 * (9 * 3 ^ k) := by rw [pow_succ]; ring
      have hcast : ((k + 1 : ℕ) : ℝ) + 3 = (k : ℝ) + 4 := by push_cast; ring
      rw [hcast, hgoal]
      calc ((k : ℝ) + 4) ^ 2 ≤ ((3 / 2) * ((k : ℝ) + 3)) ^ 2 := h2
        _ = (9 / 4) * ((k : ℝ) + 3) ^ 2 := h3
        _ ≤ 3 * ((k : ℝ) + 3) ^ 2 := h4
        _ ≤ 3 * (9 * 3 ^ k) := by linarith [ih]

/-- The `m`-th coefficient `1 - 24 σ₁(m)` of the `q`-expansion of `E₂`. -/
def e2qCoeff (m : ℕ) : ℂ :=
  if m = 0 then 1 else -24 * ((ArithmeticFunction.sigma 1 m : ℕ) : ℂ)

/-- Tail bound for `E₂` after three terms: on `Im w ≥ 1`,
`E₂ w = 1 - 24 q - 72 q² + O(‖q‖³)` with explicit constant `1000`. -/
theorem E2_third_order (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.E2Fun w - (1 - 24 * Work.Kernels.qParamFun w
        - 72 * Work.Kernels.qParamFun w ^ 2)‖
      ≤ 1000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
  set q := Work.Kernels.qParamFun w with hq
  have hqeq : Complex.exp (2 * ↑Real.pi * Complex.I * (w : ℂ)) = q := by
    rw [hq]
  have hs : HasSum (fun m : ℕ => e2qCoeff m * q ^ m) (Work.Kernels.E2Fun w) := by
    have h := EisensteinSeries.hasSum_qExpansion_E2 w
    simpa only [hqeq, smul_eq_mul, e2qCoeff] using h
  have hs3 := (hasSum_nat_add_iff' 3).mpr hs
  have hσ2 : ArithmeticFunction.sigma 1 2 = 3 := by decide +kernel
  have hc0 : e2qCoeff 0 = 1 := by simp [e2qCoeff]
  have hc1 : e2qCoeff 1 = -24 := by simp [e2qCoeff, ArithmeticFunction.sigma_one]
  have hc2 : e2qCoeff 2 = -72 := by simp [e2qCoeff, hσ2]; norm_num
  have hsum3 : (∑ i ∈ Finset.range 3, e2qCoeff i * q ^ i) = 1 - 24 * q - 72 * q ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1, hc2]
    simp only [pow_zero, pow_one, mul_one]
    ring
  rw [hsum3] at hs3
  have hr0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
  have hr : ‖q‖ ≤ 1 / 512 := by rw [hq]; exact norm_qParamFun_le_inv512 w hw
  have hr3 : 3 * ‖q‖ < 1 := by linarith
  have hcoeff : ∀ m : ℕ, 3 ≤ m → ‖e2qCoeff m‖ ≤ 24 * (m : ℝ) ^ 2 := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    have h1 : e2qCoeff m = -24 * ((ArithmeticFunction.sigma 1 m : ℕ) : ℂ) := by
      simp only [e2qCoeff, if_neg hm0]
    have hσ : ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) ≤ (m : ℝ) ^ 2 := by
      have h' : ArithmeticFunction.sigma 1 m ≤ m ^ 2 := by
        simpa [pow_two] using ArithmeticFunction.sigma_le_pow_succ 1 m
      exact_mod_cast h'
    rw [h1, norm_mul, show ‖(-24 : ℂ)‖ = (24 : ℝ) by norm_num, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hσ (by norm_num)
  have hterm : ∀ n : ℕ, ‖e2qCoeff (n + 3) * q ^ (n + 3)‖
      ≤ (24 * 9 : ℝ) * ((3 * ‖q‖) ^ n * ‖q‖ ^ 3) := by
    intro n
    have hc := hcoeff (n + 3) (by omega)
    have h2 : ((n : ℝ) + 3) ^ 2 ≤ 9 * 3 ^ n := sq_add_three_le n
    have hcast : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    rw [hcast] at hc
    calc ‖e2qCoeff (n + 3) * q ^ (n + 3)‖
        = ‖e2qCoeff (n + 3)‖ * ‖q‖ ^ (n + 3) := by rw [norm_mul, norm_pow]
      _ ≤ (24 * ((n : ℝ) + 3) ^ 2) * ‖q‖ ^ (n + 3) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ (24 * (9 * 3 ^ n)) * ‖q‖ ^ (n + 3) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = (24 * 9 : ℝ) * ((3 * ‖q‖) ^ n * ‖q‖ ^ 3) := by rw [pow_add, mul_pow]; ring
  have hgeo : Summable (fun n : ℕ => (3 * ‖q‖) ^ n) :=
    summable_geometric_of_lt_one (by positivity) hr3
  have hmaj : Summable (fun n : ℕ => (24 * 9 : ℝ) * ((3 * ‖q‖) ^ n * ‖q‖ ^ 3)) :=
    (hgeo.mul_right _).mul_left _
  have hsumm : Summable (fun n : ℕ => ‖e2qCoeff (n + 3) * q ^ (n + 3)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  have hkey : ‖Work.Kernels.E2Fun w - (1 - 24 * q - 72 * q ^ 2)‖
      = ‖∑' n : ℕ, e2qCoeff (n + 3) * q ^ (n + 3)‖ := by
    rw [hs3.tsum_eq]
  rw [hkey]
  calc ‖∑' n : ℕ, e2qCoeff (n + 3) * q ^ (n + 3)‖
      ≤ ∑' n : ℕ, ‖e2qCoeff (n + 3) * q ^ (n + 3)‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, (24 * 9 : ℝ) * ((3 * ‖q‖) ^ n * ‖q‖ ^ 3) :=
        Summable.tsum_le_tsum hterm hsumm hmaj
    _ = (24 * 9 : ℝ) * (∑' n : ℕ, (3 * ‖q‖) ^ n) * ‖q‖ ^ 3 := by
        rw [tsum_mul_left, tsum_mul_right]; ring
    _ = (24 * 9 : ℝ) * (1 - 3 * ‖q‖)⁻¹ * ‖q‖ ^ 3 := by
        rw [tsum_geometric_of_lt_one (by positivity) hr3]
    _ ≤ 1000 * ‖q‖ ^ 3 := by
        have hpos : 0 < 1 - 3 * ‖q‖ := by linarith
        have hb : (24 * 9 : ℝ) * (1 - 3 * ‖q‖)⁻¹ ≤ 1000 := by
          rw [mul_inv_le_iff₀ hpos]
          nlinarith [hr, hr0]
        exact mul_le_mul_of_nonneg_right hb (by positivity)

theorem EisensteinQExp :
    (∀ w : UpperHalfPlane, 2 ≤ w.im →
      ‖Work.Kernels.E2Fun w - (1 - 24 * Work.Asymptotics.nomeQ w - 72 * (Work.Asymptotics.nomeQ w) ^ 2)‖
        ≤ 1000 * ‖Work.Asymptotics.nomeQ w‖ ^ 3) ∧
    (∀ w : UpperHalfPlane, 2 ≤ w.im →
      ‖Work.Kernels.E4Fun w - (1 + 240 * Work.Asymptotics.nomeQ w + 2160 * (Work.Asymptotics.nomeQ w) ^ 2)‖
        ≤ 50000 * ‖Work.Asymptotics.nomeQ w‖ ^ 3) ∧
    (∀ w : UpperHalfPlane, 2 ≤ w.im →
      ‖Work.Kernels.E6Fun w - (1 - 504 * Work.Asymptotics.nomeQ w - 16632 * (Work.Asymptotics.nomeQ w) ^ 2)‖
        ≤ 1000000 * ‖Work.Asymptotics.nomeQ w‖ ^ 3) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    have hw1 : (1 : ℝ) ≤ w.im := by linarith
    simp only [nomeQ]
    exact E2_third_order w hw1
  · intro w hw
    have hw1 : (1 : ℝ) ≤ w.im := by linarith
    simp only [nomeQ]
    have h := E4_third_order w hw1
    have heq : Work.Kernels.E4Fun w - (1 + 240 * Work.Kernels.qParamFun w
          + 2160 * Work.Kernels.qParamFun w ^ 2)
        = Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
          - 2160 * Work.Kernels.qParamFun w ^ 2 := by ring
    rw [heq]
    calc ‖Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
          - 2160 * Work.Kernels.qParamFun w ^ 2‖
        ≤ 30000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := h
      _ ≤ 50000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
          have hnn : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ ^ 3 := by positivity
          linarith
  · intro w hw
    have hw1 : (1 : ℝ) ≤ w.im := by linarith
    simp only [nomeQ]
    have h := E6_third_order w hw1
    have heq : Work.Kernels.E6Fun w - (1 - 504 * Work.Kernels.qParamFun w
          - 16632 * Work.Kernels.qParamFun w ^ 2)
        = Work.Kernels.E6Fun w - 1 + 504 * Work.Kernels.qParamFun w
          + 16632 * Work.Kernels.qParamFun w ^ 2 := by ring
    rw [heq]
    exact h

end Work.Asymptotics
