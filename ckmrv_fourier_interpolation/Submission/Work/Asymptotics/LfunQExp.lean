/-
# Explicit-constant forms of the two cusp expansions used far out

`LfunQExp` is `Work.Asymptotics.Lfun_second_order` with the (implicit) constant made explicit:
the proof of `Lfun_second_order` establishes the bound with the constant `1000`, and we relax it
to `10000`.
-/
import Mathlib
import Submission.Work.Asymptotics.cusp_L_second
import Submission.Work.Kernels.LogLambda.LogExtension

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics

/-- The explicit second-order cusp expansion of `Lfun`. -/
theorem LfunQExp (z : ℂ) (hz : 1 ≤ z.im) :
    ‖Work.Kernels.LogLambda.Lfun z - ((Real.pi : ℂ) * Complex.I * z + 4 * (Real.log 2 : ℂ)
        - 8 * Complex.exp (Real.pi * Complex.I * z)
        + 12 * (Complex.exp (Real.pi * Complex.I * z)) ^ 2)‖
      ≤ 10000 * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 3 := by
  have key : Work.Kernels.LogLambda.Lfun z - ((Real.pi : ℂ) * Complex.I * z
        + 4 * (Real.log 2 : ℂ) - 8 * Complex.exp (Real.pi * Complex.I * z)
        + 12 * (Complex.exp (Real.pi * Complex.I * z)) ^ 2)
      = Work.Kernels.LogLambda.Lfun z - (Real.pi : ℂ) * Complex.I * z - 4 * (Real.log 2 : ℂ)
        + 8 * Complex.exp (Real.pi * Complex.I * z)
        - 12 * (Complex.exp (Real.pi * Complex.I * z)) ^ 2 := by ring
  rw [key]
  have h800 : ‖Work.Kernels.LogLambda.Lfun z - (Real.pi : ℂ) * Complex.I * z - 4 * (Real.log 2 : ℂ)
      + 8 * Complex.exp (Real.pi * Complex.I * z)
      - 12 * (Complex.exp (Real.pi * Complex.I * z)) ^ 2‖
      ≤ 800 * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 3 := by
    set E : ℂ := Complex.exp (Real.pi * Complex.I * z) with hEdef
    set r : ℂ := jacobiTheta₂ (z / 2) z / 2 with hrdef
    set θ : ℂ := Work.Kernels.LogLambda.thetaC00 z with hθdef
    have hEnorm : ‖E‖ = Real.exp (-(Real.pi * z.im)) := by rw [hEdef, norm_exp_pi_I_mul]
    have hEnn : 0 ≤ ‖E‖ := norm_nonneg E
    have hE8 : ‖E‖ ≤ 1 / 8 := by
      rw [hEnorm]
      refine le_trans (Real.exp_le_exp.mpr ?_) (by
        simpa using Work.Kernels.LogLambda.LogGrowth.exp_le_inv_eight_of_le_neg_pi
          (u := -Real.pi) le_rfl)
      nlinarith [Real.pi_pos, hz]
    have hE1 : ‖E‖ ≤ 1 := by linarith
    have hA : ‖r - 1 - E ^ 2‖ ≤ 4 * ‖E‖ ^ 3 := by
      rw [hrdef, hEdef]
      exact ratio_second_order z hz
    have hB : ‖θ - 1 - 2 * E‖ ≤ 4 * ‖E‖ ^ 4 := by
      rw [hθdef, hEdef]
      exact thetaC00_second_order z hz
    -- the two key bounds
    have hs_bound : ‖r - 1‖ ≤ 5 * ‖E‖ ^ 2 := by
      have h1 : r - 1 = E ^ 2 + (r - 1 - E ^ 2) := by ring
      have h2 : ‖r - 1‖ ≤ ‖E ^ 2‖ + ‖r - 1 - E ^ 2‖ := by
        calc ‖r - 1‖ = ‖E ^ 2 + (r - 1 - E ^ 2)‖ := congrArg norm h1
          _ ≤ ‖E ^ 2‖ + ‖r - 1 - E ^ 2‖ := norm_add_le _ _
      rw [norm_pow] at h2
      have h3 : ‖E‖ ^ 3 ≤ ‖E‖ ^ 2 := pow_le_pow_of_le_one hEnn hE1 (by norm_num : (2:ℕ) ≤ 3)
      nlinarith [h2, hA, h3]
    have hs2 : ‖r - 1‖ ≤ 1 / 2 := by
      have hE2 : ‖E‖ ^ 2 ≤ 1 / 64 := by nlinarith [hE8, hEnn]
      nlinarith [hs_bound, hE2]
    have hI : ‖Complex.log r - E ^ 2‖ ≤ 150 * ‖E‖ ^ 3 := by
      have hr1 : r = 1 + (r - 1) := by ring
      have hlr : Complex.log r = Complex.log (1 + (r - 1)) := congrArg Complex.log hr1
      have hlog : ‖Complex.log (1 + (r - 1)) - (r - 1) + (r - 1) ^ 2 / 2‖ ≤ ‖r - 1‖ ^ 3 :=
        log_second_order (r - 1) hs2
      rw [hlr,
        show Complex.log (1 + (r - 1)) - E ^ 2
          = (Complex.log (1 + (r - 1)) - (r - 1) + (r - 1) ^ 2 / 2)
            + (r - 1 - E ^ 2) - (r - 1) ^ 2 / 2 from by ring]
      have hnorm : ‖(Complex.log (1 + (r - 1)) - (r - 1) + (r - 1) ^ 2 / 2)
          + (r - 1 - E ^ 2) - (r - 1) ^ 2 / 2‖
          ≤ ‖Complex.log (1 + (r - 1)) - (r - 1) + (r - 1) ^ 2 / 2‖
            + ‖r - 1 - E ^ 2‖ + ‖(r - 1) ^ 2 / 2‖ := by
        refine le_trans (norm_sub_le ((Complex.log (1 + (r - 1)) - (r - 1) + (r - 1) ^ 2 / 2)
          + (r - 1 - E ^ 2)) ((r - 1) ^ 2 / 2)) ?_
        have h := norm_add_le (Complex.log (1 + (r - 1)) - (r - 1) + (r - 1) ^ 2 / 2)
          (r - 1 - E ^ 2)
        linarith
      have hsq : ‖(r - 1) ^ 2 / 2‖ ≤ (5 * ‖E‖ ^ 2) ^ 2 / 2 := by
        rw [norm_div, norm_pow, Complex.norm_ofNat]
        have h5 : ‖r - 1‖ ^ 2 ≤ (5 * ‖E‖ ^ 2) ^ 2 := by
          nlinarith [hs_bound, norm_nonneg (r - 1), norm_nonneg E]
        linarith
      have hcube : ‖r - 1‖ ^ 3 ≤ (5 * ‖E‖ ^ 2) ^ 3 := by gcongr
      have hE4 : ‖E‖ ^ 4 ≤ ‖E‖ ^ 3 := pow_le_pow_of_le_one hEnn hE1 (by norm_num : (3:ℕ) ≤ 4)
      have hE6 : ‖E‖ ^ 6 ≤ ‖E‖ ^ 3 := pow_le_pow_of_le_one hEnn hE1 (by norm_num : (3:ℕ) ≤ 6)
      have h1 : ‖E‖ ^ 3 ≤ 1 := pow_le_one₀ hEnn hE1
      nlinarith [hnorm, hlog, hA, hsq, hcube, hE4, hE6, h1, hEnn]
    have hv_bound : ‖θ - 1‖ ≤ 3 * ‖E‖ := by
      have h1 : θ - 1 = 2 * E + (θ - 1 - 2 * E) := by ring
      have h2 : ‖θ - 1‖ ≤ ‖2 * E‖ + ‖θ - 1 - 2 * E‖ := by
        calc ‖θ - 1‖ = ‖2 * E + (θ - 1 - 2 * E)‖ := congrArg norm h1
          _ ≤ ‖2 * E‖ + ‖θ - 1 - 2 * E‖ := norm_add_le _ _
      have h3 : ‖2 * E‖ = 2 * ‖E‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h4 : 4 * ‖E‖ ^ 4 ≤ ‖E‖ := by
        have h3' : ‖E‖ ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := pow_le_pow_left₀ hEnn hE8 3
        nlinarith [h3', hEnn]
      nlinarith [h2, hB, h3, h4, hEnn]
    have hv2 : ‖θ - 1‖ ≤ 1 / 2 := by nlinarith [hv_bound, hE8]
    have hII : ‖Complex.log θ - 2 * E + 2 * E ^ 2‖ ≤ 50 * ‖E‖ ^ 3 := by
      have hθ1 : θ = 1 + (θ - 1) := by ring
      have hlθ : Complex.log θ = Complex.log (1 + (θ - 1)) := congrArg Complex.log hθ1
      have hlog : ‖Complex.log (1 + (θ - 1)) - (θ - 1) + (θ - 1) ^ 2 / 2‖ ≤ ‖θ - 1‖ ^ 3 :=
        log_second_order (θ - 1) hv2
      have h3 : 2 * E ^ 2 - (θ - 1) ^ 2 / 2
          = -2 * E * (θ - 1 - 2 * E) - (θ - 1 - 2 * E) ^ 2 / 2 := by ring
      rw [hlθ,
        show Complex.log (1 + (θ - 1)) - 2 * E + 2 * E ^ 2
          = (Complex.log (1 + (θ - 1)) - (θ - 1) + (θ - 1) ^ 2 / 2)
            + (θ - 1 - 2 * E) + (2 * E ^ 2 - (θ - 1) ^ 2 / 2) from by ring, h3]
      have ha : ‖-2 * E * (θ - 1 - 2 * E)‖ = 2 * ‖E‖ * ‖θ - 1 - 2 * E‖ := by
        rw [norm_mul, norm_mul]
        norm_num
      have hb : ‖(θ - 1 - 2 * E) ^ 2 / 2‖ = ‖θ - 1 - 2 * E‖ ^ 2 / 2 := by
        rw [norm_div, norm_pow, Complex.norm_ofNat]
      have hnorm : ‖(Complex.log (1 + (θ - 1)) - (θ - 1) + (θ - 1) ^ 2 / 2)
          + (θ - 1 - 2 * E) + (-2 * E * (θ - 1 - 2 * E) - (θ - 1 - 2 * E) ^ 2 / 2)‖
          ≤ ‖Complex.log (1 + (θ - 1)) - (θ - 1) + (θ - 1) ^ 2 / 2‖ + ‖θ - 1 - 2 * E‖
            + (2 * ‖E‖ * ‖θ - 1 - 2 * E‖ + ‖θ - 1 - 2 * E‖ ^ 2 / 2) := by
        refine le_trans (norm_add_le ((Complex.log (1 + (θ - 1)) - (θ - 1) + (θ - 1) ^ 2 / 2)
          + (θ - 1 - 2 * E)) (-2 * E * (θ - 1 - 2 * E) - (θ - 1 - 2 * E) ^ 2 / 2)) ?_
        have h5 : ‖-2 * E * (θ - 1 - 2 * E) - (θ - 1 - 2 * E) ^ 2 / 2‖
            ≤ 2 * ‖E‖ * ‖θ - 1 - 2 * E‖ + ‖θ - 1 - 2 * E‖ ^ 2 / 2 := by
          calc ‖-2 * E * (θ - 1 - 2 * E) - (θ - 1 - 2 * E) ^ 2 / 2‖
              ≤ ‖-2 * E * (θ - 1 - 2 * E)‖ + ‖(θ - 1 - 2 * E) ^ 2 / 2‖ := norm_sub_le _ _
            _ = 2 * ‖E‖ * ‖θ - 1 - 2 * E‖ + ‖θ - 1 - 2 * E‖ ^ 2 / 2 := by rw [ha, hb]
        have h6 := norm_add_le (Complex.log (1 + (θ - 1)) - (θ - 1) + (θ - 1) ^ 2 / 2)
          (θ - 1 - 2 * E)
        linarith
      have hcube : ‖θ - 1‖ ^ 3 ≤ (3 * ‖E‖) ^ 3 := by gcongr
      have hB4 : ‖θ - 1 - 2 * E‖ ^ 2 ≤ (4 * ‖E‖ ^ 4) ^ 2 := by gcongr
      have hE4 : ‖E‖ ^ 4 ≤ ‖E‖ ^ 3 := pow_le_pow_of_le_one hEnn hE1 (by norm_num : (3:ℕ) ≤ 4)
      have hE5 : ‖E‖ ^ 5 ≤ ‖E‖ ^ 3 := pow_le_pow_of_le_one hEnn hE1 (by norm_num : (3:ℕ) ≤ 5)
      have hE8' : ‖E‖ ^ 8 ≤ ‖E‖ ^ 3 := pow_le_pow_of_le_one hEnn hE1 (by norm_num : (3:ℕ) ≤ 8)
      have h1 : ‖E‖ ^ 3 ≤ 1 := pow_le_one₀ hEnn hE1
      nlinarith [hnorm, hlog, hB, hB4, hcube, hE4, hE5, hE8', h1, hEnn, hv_bound]
    -- assemble
    have hzW : z ∈ Work.Kernels.LogLambda.W := by
      show (1 / 2 : ℝ) < z.im
      linarith
    have hLU : Work.Kernels.LogLambda.LU z - (Real.pi : ℂ) * Complex.I * z
        = 4 * (Real.log 2 : ℂ) + 4 * Complex.log r - 4 * Complex.log θ := by
      rw [Work.Kernels.LogLambda.LU, Work.Kernels.LogLambda.thetaC10_div_exp]
      simp only [hrdef, hθdef, Work.Kernels.LogLambda.thetaC00]
      ring
    have hkey : Work.Kernels.LogLambda.Lfun z - (Real.pi : ℂ) * Complex.I * z
          - 4 * (Real.log 2 : ℂ) + 8 * E - 12 * E ^ 2
        = 4 * (Complex.log r - E ^ 2) - 4 * (Complex.log θ - 2 * E + 2 * E ^ 2) := by
      rw [Work.Kernels.LogLambda.Lfun_eq_LU_on_W z hzW, hLU]
      ring
    rw [hkey]
    have hfin : ‖4 * (Complex.log r - E ^ 2) - 4 * (Complex.log θ - 2 * E + 2 * E ^ 2)‖
        ≤ 4 * ‖Complex.log r - E ^ 2‖ + 4 * ‖Complex.log θ - 2 * E + 2 * E ^ 2‖ := by
      calc ‖4 * (Complex.log r - E ^ 2) - 4 * (Complex.log θ - 2 * E + 2 * E ^ 2)‖
          ≤ ‖4 * (Complex.log r - E ^ 2)‖ + ‖4 * (Complex.log θ - 2 * E + 2 * E ^ 2)‖ :=
            norm_sub_le _ _
        _ = 4 * ‖Complex.log r - E ^ 2‖ + 4 * ‖Complex.log θ - 2 * E + 2 * E ^ 2‖ := by
            rw [norm_mul, norm_mul, Complex.norm_ofNat]
    calc ‖4 * (Complex.log r - E ^ 2) - 4 * (Complex.log θ - 2 * E + 2 * E ^ 2)‖
        ≤ 4 * ‖Complex.log r - E ^ 2‖ + 4 * ‖Complex.log θ - 2 * E + 2 * E ^ 2‖ := hfin
      _ ≤ 4 * (150 * ‖E‖ ^ 3) + 4 * (50 * ‖E‖ ^ 3) := by linarith [hI, hII]
      _ = 800 * ‖E‖ ^ 3 := by ring

  refine le_trans h800 ?_
  have : (0:ℝ) ≤ ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 3 := by positivity
  linarith

end Work.Asymptotics
