import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KhatE1.cusp_L_fourth
import Submission.Work.Asymptotics.KhatE1Core.psi_second_order
import Submission.Work.Kernels.LogLambda.LogGrowth.Lfun_sub_pi_I_bound
import Submission.Work.Asymptotics.KhatE1.ratio_sixth_order
import Submission.Work.Asymptotics.KhatE1.thetaC00_sixth_order

/-!
# Fifth-order cusp expansion of the canonical logarithm `Lfun`

Writing `q = e^{πiz}`, the canonical branch of the CKMRV logarithm satisfies, on the
region `Im z ≥ 1`,

  `Lfun z = πiz + 4 log 2 - 8q + 12q² - (32/3)q³ + 6q⁴ - (48/5)q⁵ + O(‖q‖⁶)`,

which is the fifth-order refinement of `Lfun_fourth_order` (`Submission/Work/Asymptotics/KhatE1/cusp_L_fourth.lean`).

The proof follows the fourth-order one.  On `W = {Im > 1/2}` we have `Lfun = LU` and

  `LU z - πiz = 4 log 2 + 4 log r - 4 log θ`,   `r = θ₂(z/2,z)/2`, `θ = θ₀₀(z)`,

so it suffices to expand `4 log r - 4 log θ`.  Write `r = 1 + u₁` with `u₁ = q² + ρ`,
`ρ = r - 1 - q²`, and `θ = 1 + u₂` with `u₂ = v + σ`, `v = 2q + 2q⁴`,
`σ = θ - 1 - 2q - 2q⁴`.  The sharper remainder bounds

* `‖ρ‖ ≤ 2‖q‖⁶` (`ratio_sixth_order`),  * `‖σ‖ ≤ 4‖q‖⁶` (`thetaC00_sixth_order`)

replace the `O(‖q‖⁵)` bounds used at fourth order.  With the fifth Taylor polynomial
`P₅(u) = u - u²/2 + u³/3 - u⁴/4 + u⁵/5` and the sixth-order Taylor bound for `log`
(`log_fifth_order`), the two `log`s are then expanded through degree five; the leftover
polynomials in `q` (factored by `q⁶`) are `X₅` for the `r`-side, `Y₅` for the `θ`-side and
`V₅` for the purely algebraic combination `4P₅(q²) - 4P₅(2q + 2q⁴) + 8q - 12q² + (32/3)q³
- 6q⁴ + (48/5)q⁵`.
-/

open Complex Real
open scoped Topology

namespace Work.Asymptotics.KhatE1

noncomputable section

/-! ## Polynomials controlling the fifth-order remainders -/

/-- The fifth-order Taylor polynomial of `log(1+·)`. -/
private noncomputable def P5 (w : ℂ) : ℂ := w - w ^ 2 / 2 + w ^ 3 / 3 - w ^ 4 / 4 + w ^ 5 / 5

/-- `P5 (a²+b) - P5 (a²) = b * X5 a b`. -/
private noncomputable def X5 (a b : ℂ) : ℂ :=
  1 - a ^ 2 - b / 2 + a ^ 4 + a ^ 2 * b + b ^ 2 / 3 - a ^ 6
    - (3 / 2) * a ^ 4 * b - a ^ 2 * b ^ 2 - b ^ 3 / 4
    + a ^ 8 + 2 * a ^ 6 * b + 2 * a ^ 4 * b ^ 2 + a ^ 2 * b ^ 3 + b ^ 4 / 5

/-- The quartic polynomial `2a + 2a⁴`. -/
private noncomputable def Yvv5 (a : ℂ) : ℂ := 2 * a + 2 * a ^ 4

/-- `P5 (Yvv5 a + b) - P5 (Yvv5 a) = b * Y5 a b`. -/
private noncomputable def Y5 (a b : ℂ) : ℂ :=
  1 - Yvv5 a - b / 2 + (Yvv5 a) ^ 2 + Yvv5 a * b + b ^ 2 / 3 - (Yvv5 a) ^ 3
    - (3 / 2) * (Yvv5 a) ^ 2 * b - Yvv5 a * b ^ 2 - b ^ 3 / 4
    + (Yvv5 a) ^ 4 + 2 * (Yvv5 a) ^ 3 * b + 2 * (Yvv5 a) ^ 2 * b ^ 2 + Yvv5 a * b ^ 3
    + b ^ 4 / 5

/-- `V5 a` is the degree fourteen polynomial with
`-4 * P5 (2a + 2a⁴) + 4 * P5 (a²) + 8a - 12a² + (32/3)a³ - 6a⁴ + (48/5)a⁵ = a⁶ * V5 a`. -/
private noncomputable def V5 (a : ℂ) : ℂ :=
  -(92 / 3) + 64 * a - 121 * a ^ 2 - 32 * a ^ 3 + (484 / 5) * a ^ 4 - 256 * a ^ 5
    - (32 / 3) * a ^ 6 + 64 * a ^ 7 - 256 * a ^ 8 + 16 * a ^ 10 - 128 * a ^ 11
    - (128 / 5) * a ^ 14

private lemma P5_sq_add (a b : ℂ) : P5 (a ^ 2 + b) - P5 (a ^ 2) = b * X5 a b := by
  simp only [P5, X5]; ring

private lemma P5_vv_add (a b : ℂ) : P5 (Yvv5 a + b) - P5 (Yvv5 a) = b * Y5 a b := by
  simp only [P5, Yvv5, Y5]; ring

private lemma V5_spec (a : ℂ) :
    -4 * P5 (Yvv5 a) + 4 * P5 (a ^ 2) + 8 * a - 12 * a ^ 2 + (32 / 3) * a ^ 3
      - 6 * a ^ 4 + (48 / 5) * a ^ 5 = a ^ 6 * V5 a := by
  simp only [P5, Yvv5, V5]; ring

/-! ## Bounds for continuous auxiliary functions on a disc -/

/-- A continuous function of two complex variables is bounded on the square `‖·‖ ≤ K`. -/
private lemma exists_bound_continuous₂ (P : ℂ → ℂ → ℂ)
    (hP : Continuous fun p : ℂ × ℂ => P p.1 p.2) {K : ℝ} (_hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℂ, ‖a‖ ≤ K → ‖b‖ ≤ K → ‖P a b‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) K).prod (isCompact_closedBall (0 : ℂ) K)
    |>.exists_bound_of_continuousOn hP.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun a b ha hb => ?_⟩
  refine le_trans (hC (a, b) ?_) (le_max_left _ _)
  rw [Set.mem_prod]
  exact ⟨by rwa [Metric.mem_closedBall, dist_zero_right],
    by rwa [Metric.mem_closedBall, dist_zero_right]⟩

/-- A continuous function of one complex variable is bounded on `‖·‖ ≤ K`. -/
private lemma exists_bound_continuous₁ (P : ℂ → ℂ) (hP : Continuous P) {K : ℝ} (_hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℂ, ‖a‖ ≤ K → ‖P a‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) K).exists_bound_of_continuousOn
    hP.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun a ha =>
    le_trans (hC a (by rwa [Metric.mem_closedBall, dist_zero_right])) (le_max_left _ _)⟩

/-- Triangle inequality for five terms. -/
private lemma norm_five_le (a b c d e : ℂ) :
    ‖a - b + c - d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  have h1 : ‖a - b + c - d + e‖ ≤ ‖a - b + c - d‖ + ‖e‖ := norm_add_le _ _
  have h2 : ‖a - b + c - d‖ ≤ ‖a - b + c‖ + ‖d‖ := norm_sub_le _ _
  have h3 : ‖a - b + c‖ ≤ ‖a - b‖ + ‖c‖ := norm_add_le _ _
  have h4 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
  linarith [norm_nonneg a, norm_nonneg b, norm_nonneg c, norm_nonneg d, norm_nonneg e]

/-- **Sixth-order Taylor bound for `log`** (local form of `log_fifth_order`). -/
private lemma log_fifth_order_aux (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) :
    ‖Complex.log (1 + u) - (u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + u ^ 5 / 5)‖
      ≤ ‖u‖ ^ 6 := by
  have hu1 : ‖u‖ < 1 := by linarith
  have h1 : ‖Complex.log (1 + u) - Complex.logTaylor 6 u‖
      ≤ ‖u‖ ^ 6 * (1 - ‖u‖)⁻¹ / 6 := by
    have := Complex.norm_log_sub_logTaylor_le 5 hu1
    norm_num at this ⊢
    exact this
  rw [show Complex.logTaylor 6 u = u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + u ^ 5 / 5 from by
    simp only [Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero]
    ring] at h1
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h6 : (0 : ℝ) ≤ ‖u‖ ^ 6 := by positivity
  have h2 : ‖u‖ ^ 6 * (1 - ‖u‖)⁻¹ / 6 ≤ ‖u‖ ^ 6 := by nlinarith [hinv, h6]
  linarith [h1, h2]

/-! ## The main fifth-order expansion -/

theorem Lfun_fifth_order :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ z.im →
      ‖Work.Kernels.LogLambda.Lfun z - ((Real.pi : ℂ) * Complex.I * z + 4 * (Real.log 2 : ℂ)
          - 8 * Complex.exp (Real.pi * Complex.I * z)
          + 12 * (Complex.exp (Real.pi * Complex.I * z)) ^ 2
          - (32 / 3 : ℂ) * (Complex.exp (Real.pi * Complex.I * z)) ^ 3
          + 6 * (Complex.exp (Real.pi * Complex.I * z)) ^ 4
          - (48 / 5 : ℂ) * (Complex.exp (Real.pi * Complex.I * z)) ^ 5)‖
        ≤ C * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 6 := by
  obtain ⟨CX, hCX0, hCX⟩ :=
    exists_bound_continuous₂ X5 (by unfold X5; fun_prop) (K := 1 / 2) (by norm_num)
  obtain ⟨CY, hCY0, hCY⟩ :=
    exists_bound_continuous₂ Y5 (by unfold Y5 Yvv5; fun_prop) (K := 1 / 2) (by norm_num)
  obtain ⟨CV, hCV0, hCV⟩ :=
    exists_bound_continuous₁ V5 (by unfold V5; fun_prop) (K := 1 / 2) (by norm_num)
  refine ⟨256 + 1048576 + 8 * CX + 16 * CY + CV, by linarith, fun z hz => ?_⟩
  have hzW : z ∈ Work.Kernels.LogLambda.W := by
    show (1 / 2 : ℝ) < z.im
    linarith
  set q : ℂ := Complex.exp (Real.pi * Complex.I * z) with hq
  set r : ℂ := jacobiTheta₂ (z / 2) z / 2 with hr
  set th : ℂ := Work.Kernels.LogLambda.thetaC00 z with hth
  set s : ℝ := ‖q‖ with hs
  have hs_q : s = Real.exp (-(Real.pi * z.im)) := by
    rw [hs, hq, Complex.norm_exp]
    congr 1
    rw [show (Real.pi : ℂ) * Complex.I * z = ((Real.pi : ℝ) : ℂ) * (Complex.I * z) by ring]
    rw [Complex.re_ofReal_mul, Complex.I_mul_re]
    ring
  have hs0 : 0 ≤ s := by rw [hs]; exact norm_nonneg q
  have hs8 : s ≤ 1 / 8 := by
    rw [hs_q]
    exact (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hz])).trans
      (Work.Kernels.LogLambda.LogGrowth.exp_le_inv_eight_of_le_neg_pi le_rfl)
  have hs_half : s ≤ 1 / 2 := by linarith
  have hs1 : s ≤ 1 := by linarith
  have hq_half : ‖q‖ ≤ 1 / 2 := by rw [← hs]; exact hs_half
  have hLU : Work.Kernels.LogLambda.LU z - (Real.pi : ℂ) * Complex.I * z
      = 4 * (Real.log 2 : ℂ) + 4 * Complex.log r - 4 * Complex.log th := by
    rw [Work.Kernels.LogLambda.LU, Work.Kernels.LogLambda.thetaC10_div_exp]
    simp only [hr, hth, Work.Kernels.LogLambda.thetaC00]
    ring
  set rho : ℂ := r - 1 - q ^ 2 with hrhodef
  set vv : ℂ := 2 * q + 2 * q ^ 4 with hvvdef
  set sig : ℂ := th - 1 - 2 * q - 2 * q ^ 4 with hsigdef
  have hrho : ‖rho‖ ≤ 2 * s ^ 6 := by
    rw [hrhodef]
    simpa [hr, hq, hs] using ratio_sixth_order z hz
  have hsig : ‖sig‖ ≤ 4 * s ^ 6 := by
    rw [hsigdef]
    simpa [hth, hq, hs] using thetaC00_sixth_order z hz
  set u1 : ℂ := q ^ 2 + rho with hu1def
  set u2 : ℂ := vv + sig with hu2def
  have hr1 : 1 + u1 = r := by rw [hu1def, hrhodef]; ring
  have hth1 : 1 + u2 = th := by rw [hu2def, hvvdef, hsigdef]; ring
  have hu1_le : ‖u1‖ ≤ 2 * s ^ 2 := by
    rw [hu1def]
    calc ‖q ^ 2 + rho‖ ≤ ‖q ^ 2‖ + ‖rho‖ := norm_add_le _ _
      _ = s ^ 2 + ‖rho‖ := by rw [norm_pow, hs]
      _ ≤ s ^ 2 + 2 * s ^ 6 := by linarith [hrho]
      _ ≤ 2 * s ^ 2 := by
          have h4 : s ^ 4 ≤ (1 / 2 : ℝ) ^ 4 := pow_le_pow_left₀ hs0 hs_half 4
          have h6 : s ^ 6 = s ^ 4 * s ^ 2 := by ring
          nlinarith [h4, pow_nonneg hs0 2, h6]
  have hu1_half : ‖u1‖ ≤ 1 / 2 := by
    have h : s ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hs0 hs_half 2
    nlinarith [hu1_le, h]
  have hu2_le : ‖u2‖ ≤ 2 * s + 2 * s ^ 4 + 4 * s ^ 6 := by
    rw [hu2def, hvvdef]
    calc ‖2 * q + 2 * q ^ 4 + sig‖ ≤ ‖2 * q + 2 * q ^ 4‖ + ‖sig‖ := norm_add_le _ _
      _ ≤ (2 * s + 2 * s ^ 4) + 4 * s ^ 6 := by
          have h1 : ‖2 * q + 2 * q ^ 4‖ ≤ 2 * s + 2 * s ^ 4 := by
            calc ‖2 * q + 2 * q ^ 4‖ ≤ ‖2 * q‖ + ‖2 * q ^ 4‖ := norm_add_le _ _
              _ = 2 * s + 2 * s ^ 4 := by
                  simp only [norm_mul, Complex.norm_ofNat, norm_pow, hs]
          linarith [h1, hsig]
  have hu2_le8 : ‖u2‖ ≤ 8 * s := by
    refine le_trans hu2_le ?_
    have h4 : s ^ 4 ≤ s := by
      simpa using pow_le_pow_of_le_one hs0 hs1 (by norm_num : (1 : ℕ) ≤ 4)
    have h6 : s ^ 6 ≤ s := by
      simpa using pow_le_pow_of_le_one hs0 hs1 (by norm_num : (1 : ℕ) ≤ 6)
    linarith
  have hu2_half : ‖u2‖ ≤ 1 / 2 := by
    have h4 : s ^ 4 ≤ (1 / 8 : ℝ) ^ 4 := pow_le_pow_left₀ hs0 hs8 4
    have h6 : s ^ 6 ≤ (1 / 8 : ℝ) ^ 6 := pow_le_pow_left₀ hs0 hs8 6
    norm_num at h4 h6
    nlinarith [hu2_le, h4, h6, hs8]
  -- expansion of `log r`
  have hlogr : ‖Complex.log r - P5 u1‖ ≤ 64 * s ^ 6 := by
    have h2 : ‖Complex.log r - P5 u1‖ ≤ ‖u1‖ ^ 6 := by
      rw [show P5 u1 = u1 - u1 ^ 2 / 2 + u1 ^ 3 / 3 - u1 ^ 4 / 4 + u1 ^ 5 / 5 from rfl,
        ← hr1]
      exact log_fifth_order_aux u1 hu1_half
    have h5 : ‖u1‖ ^ 6 ≤ 64 * s ^ 6 := by
      have hh := pow_le_pow_left₀ (norm_nonneg u1) hu1_le 6
      have h2' : (2 * s ^ 2) ^ 6 = 64 * s ^ 12 := by ring
      rw [h2'] at hh
      have h12 : s ^ 12 ≤ s ^ 6 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
      linarith
    linarith
  -- expansion of `log θ`
  have hlogt : ‖Complex.log th - P5 u2‖ ≤ 262144 * s ^ 6 := by
    have h2 : ‖Complex.log th - P5 u2‖ ≤ ‖u2‖ ^ 6 := by
      rw [show P5 u2 = u2 - u2 ^ 2 / 2 + u2 ^ 3 / 3 - u2 ^ 4 / 4 + u2 ^ 5 / 5 from rfl,
        ← hth1]
      exact log_fifth_order_aux u2 hu2_half
    have h5 : ‖u2‖ ^ 6 ≤ 262144 * s ^ 6 := by
      have hh := pow_le_pow_left₀ (norm_nonneg u2) hu2_le8 6
      have h2' : (8 * s) ^ 6 = 262144 * s ^ 6 := by ring
      rwa [h2'] at hh
    linarith
  have hrhohalf : ‖rho‖ ≤ 1 / 2 := by
    have h : s ^ 6 ≤ (1 / 8 : ℝ) ^ 6 := pow_le_pow_left₀ hs0 hs8 6
    norm_num at h
    nlinarith [hrho, h]
  have hsighalf : ‖sig‖ ≤ 1 / 2 := by
    have h : s ^ 6 ≤ (1 / 8 : ℝ) ^ 6 := pow_le_pow_left₀ hs0 hs8 6
    norm_num at h
    nlinarith [hsig, h]
  -- the two "mid" contributions
  have hmid1 : ‖P5 u1 - P5 (q ^ 2)‖ ≤ 2 * CX * s ^ 6 := by
    have hidX : P5 u1 - P5 (q ^ 2) = rho * X5 q rho := by
      rw [hu1def]; exact P5_sq_add q rho
    rw [hidX, norm_mul]
    calc ‖rho‖ * ‖X5 q rho‖ ≤ (2 * s ^ 6) * CX :=
          mul_le_mul hrho (hCX q rho hq_half hrhohalf) (norm_nonneg _) (by positivity)
      _ = 2 * CX * s ^ 6 := by ring
  have hvvY : vv = Yvv5 q := by simp only [hvvdef, Yvv5]
  have hmid2 : ‖P5 u2 - P5 vv‖ ≤ 4 * CY * s ^ 6 := by
    have hidY : P5 u2 - P5 vv = sig * Y5 q sig := by
      rw [hu2def, hvvY]
      exact P5_vv_add q sig
    rw [hidY, norm_mul]
    calc ‖sig‖ * ‖Y5 q sig‖ ≤ (4 * s ^ 6) * CY :=
          mul_le_mul hsig (hCY q sig hq_half hsighalf) (norm_nonneg _) (by positivity)
      _ = 4 * CY * s ^ 6 := by ring
  -- the purely algebraic remainder
  have hV5term : ‖q ^ 6 * V5 q‖ ≤ CV * s ^ 6 := by
    rw [norm_mul]
    have hq6 : ‖q ^ 6‖ = s ^ 6 := by rw [norm_pow, hs]
    calc ‖q ^ 6‖ * ‖V5 q‖ ≤ s ^ 6 * CV :=
          mul_le_mul (le_of_eq hq6) (hCV q hq_half) (norm_nonneg _) (by positivity)
      _ = CV * s ^ 6 := by ring
  -- the exact algebra
  have hkey : Work.Kernels.LogLambda.Lfun z
      - ((Real.pi : ℂ) * Complex.I * z + 4 * (Real.log 2 : ℂ)
          - 8 * q + 12 * q ^ 2 - (32 / 3 : ℂ) * q ^ 3 + 6 * q ^ 4
          - (48 / 5 : ℂ) * q ^ 5)
      = 4 * (Complex.log r - P5 u1) - 4 * (Complex.log th - P5 u2)
        + 4 * (P5 u1 - P5 (q ^ 2)) - 4 * (P5 u2 - P5 vv) + q ^ 6 * V5 q := by
    have hLUeq : Work.Kernels.LogLambda.Lfun z = Work.Kernels.LogLambda.LU z :=
      Work.Kernels.LogLambda.Lfun_eq_LU_on_W z hzW
    have hre : Work.Kernels.LogLambda.LU z
        - ((Real.pi : ℂ) * Complex.I * z + 4 * (Real.log 2 : ℂ)
            - 8 * q + 12 * q ^ 2 - (32 / 3 : ℂ) * q ^ 3 + 6 * q ^ 4
            - (48 / 5 : ℂ) * q ^ 5)
        = (Work.Kernels.LogLambda.LU z - (Real.pi : ℂ) * Complex.I * z)
            - 4 * (Real.log 2 : ℂ) + 8 * q - 12 * q ^ 2 + (32 / 3 : ℂ) * q ^ 3
            - 6 * q ^ 4 + (48 / 5 : ℂ) * q ^ 5 := by ring
    rw [hLUeq, hre, hLU]
    rw [← V5_spec q, ← hvvY]
    ring
  rw [hkey]
  calc ‖4 * (Complex.log r - P5 u1) - 4 * (Complex.log th - P5 u2)
        + 4 * (P5 u1 - P5 (q ^ 2)) - 4 * (P5 u2 - P5 vv) + q ^ 6 * V5 q‖
      ≤ 4 * ‖Complex.log r - P5 u1‖ + 4 * ‖Complex.log th - P5 u2‖
        + 4 * ‖P5 u1 - P5 (q ^ 2)‖ + 4 * ‖P5 u2 - P5 vv‖ + ‖q ^ 6 * V5 q‖ := by
        refine le_trans (norm_five_le _ _ _ _ _) ?_
        simp only [norm_mul, Complex.norm_ofNat]
        linarith [norm_nonneg (Complex.log r - P5 u1), norm_nonneg (Complex.log th - P5 u2),
          norm_nonneg (P5 u1 - P5 (q ^ 2)), norm_nonneg (P5 u2 - P5 vv),
          norm_nonneg (q ^ 6 * V5 q)]
    _ ≤ 4 * (64 * s ^ 6) + 4 * (262144 * s ^ 6) + 4 * (2 * CX * s ^ 6)
        + 4 * (4 * CY * s ^ 6) + CV * s ^ 6 := by
        linarith [hlogr, hlogt, hmid1, hmid2, hV5term]
    _ = (256 + 1048576 + 8 * CX + 16 * CY + CV) * s ^ 6 := by ring
    _ = (256 + 1048576 + 8 * CX + 16 * CY + CV)
          * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 6 := by rw [← hq, ← hs]

end

end Work.Asymptotics.KhatE1
