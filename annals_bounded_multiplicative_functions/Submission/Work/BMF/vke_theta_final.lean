import Mathlib
import Submission.Work.BMF.vke_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **The constant/log bookkeeping for the reduced block sum.** With `Z = 84 K (4^k)^2 (k-1)!`,
`bb = Cmv (k-1) r (1 + log((k-1)r))/2` and `vkLogErr ≤ δ_req log N`, the prefactor
`exp(Cv1a k³ + log(14k²) + log Z/(2s) + bb) ≤ 4 N^{δ_req}` (using `Z ≤ 56 K 4^k (k-1)! · 4^{2s}`,
which costs `log 4`). -/
theorem vke_theta_final {N t Cv1a Cmv Kcnt : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) (hKcnt : 0 < Kcnt)
    (hlogerr : vkLogErr Cv1a Cmv Kcnt N t ≤ vkDelta (1 / 100000) N t * Real.log N)
    (hδ0 : 0 ≤ vkDelta (1 / 100000) N t) :
    Real.exp (Cv1a * ((vkK N t : ℕ) : ℝ) ^ 3 + Real.log (14 * ((vkK N t : ℕ) : ℝ) ^ 2)
        + Real.log (84 * Kcnt * ((4 : ℝ) ^ (vkK N t)) ^ 2
            * ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)) / (2 * ((vkS N t : ℕ) : ℝ))
        + Cmv * ((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ)
            * (1 + Real.log (((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ))) / 2)
      ≤ 4 * N ^ vkDelta (1 / 100000) N t := by
  have hNpos : (0:ℝ) < N := by linarith
  have hk6 : 6 ≤ vkK N t := vkK_ge_six hN hNt
  have hrpos : 0 < vkR N t := by rw [vkR]; omega
  have hspos : (0:ℝ) < ((vkS N t : ℕ):ℝ) := by
    rw [vkS]; push_cast
    exact mul_pos (by exact_mod_cast (by omega : 0 < vkK N t - 1)) (by exact_mod_cast hrpos)
  -- split the `Z`-logarithm into the `vkLogErr` piece and a factor `(3/2)·4^k`
  have hZ : (84 : ℝ) * Kcnt * ((4:ℝ)^(vkK N t))^2 * ((Nat.factorial (vkK N t - 1):ℕ):ℝ)
      = (56 * Kcnt * (4:ℝ)^(vkK N t) * ((Nat.factorial (vkK N t - 1):ℕ):ℝ))
        * ((3:ℝ)/2 * (4:ℝ)^(vkK N t)) := by ring
  have hfacpos : (0:ℝ) < ((Nat.factorial (vkK N t - 1):ℕ):ℝ) := by
    exact_mod_cast Nat.factorial_pos (vkK N t - 1)
  have hpos1 : (0:ℝ) < 56 * Kcnt * (4:ℝ)^(vkK N t) * ((Nat.factorial (vkK N t - 1):ℕ):ℝ) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hKcnt) (by positivity)) hfacpos
  have hpos2 : (0:ℝ) < (3:ℝ)/2 * (4:ℝ)^(vkK N t) := by positivity
  have hlogZ : Real.log (84 * Kcnt * ((4:ℝ)^(vkK N t))^2 * ((Nat.factorial (vkK N t - 1):ℕ):ℝ))
      = Real.log (56 * Kcnt * (4:ℝ)^(vkK N t) * ((Nat.factorial (vkK N t - 1):ℕ):ℝ))
        + Real.log ((3:ℝ)/2 * (4:ℝ)^(vkK N t)) := by
    rw [hZ, Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)]
  -- the exponent in the goal is `vkLogErr` plus `log ((3/2)·4^k)/(2s)`
  have hA : Cv1a * ((vkK N t : ℕ):ℝ)^3 + Real.log (14 * ((vkK N t : ℕ):ℝ)^2)
        + Real.log (84 * Kcnt * ((4:ℝ)^(vkK N t))^2 * ((Nat.factorial (vkK N t - 1):ℕ):ℝ)) / (2 * ((vkS N t : ℕ):ℝ))
        + Cmv * ((vkK N t - 1 : ℕ):ℝ) * ((vkR N t : ℕ):ℝ) * (1 + Real.log (((vkK N t - 1 : ℕ):ℝ) * ((vkR N t : ℕ):ℝ))) / 2
      = vkLogErr Cv1a Cmv Kcnt N t + Real.log ((3:ℝ)/2 * (4:ℝ)^(vkK N t)) / (2 * ((vkS N t : ℕ):ℝ)) := by
    rw [vkLogErr, hlogZ]
    ring
  -- the numerical core: `(3/2)·4^k ≤ 4^{2s}`
  have hle : (3:ℝ)/2 * (4:ℝ)^(vkK N t) ≤ (4:ℝ)^(2 * vkS N t) := by
    have hr1 : 1 ≤ vkR N t := by rw [vkR]; omega
    have hs : vkS N t = (vkK N t - 1) * vkR N t := rfl
    have hge4 : 4 ≤ 2 * vkS N t - vkK N t := by
      rw [hs]
      have : (vkK N t - 1) * vkR N t ≥ (vkK N t - 1) * 1 := Nat.mul_le_mul_left _ hr1
      omega
    have hk2s : vkK N t ≤ 2 * vkS N t := by omega
    have hpow : (4:ℝ)^(2 * vkS N t) = (4:ℝ)^(vkK N t) * (4:ℝ)^(2 * vkS N t - vkK N t) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    have h256 : (3:ℝ)/2 ≤ (4:ℝ)^4 := by norm_num
    have h4pow : (4:ℝ)^4 ≤ (4:ℝ)^(2 * vkS N t - vkK N t) :=
      pow_le_pow_right₀ (by norm_num) hge4
    calc (3:ℝ)/2 * (4:ℝ)^(vkK N t) ≤ (4:ℝ)^(2 * vkS N t - vkK N t) * (4:ℝ)^(vkK N t) :=
          mul_le_mul_of_nonneg_right (le_trans h256 h4pow) (by positivity)
      _ = (4:ℝ)^(vkK N t) * (4:ℝ)^(2 * vkS N t - vkK N t) := by ring
  -- hence `log ((3/2)·4^k)/(2s) ≤ log 4`
  have hnum : Real.log ((3:ℝ)/2 * (4:ℝ)^(vkK N t)) ≤ 2 * ((vkS N t : ℕ):ℝ) * Real.log 4 := by
    calc Real.log ((3:ℝ)/2 * (4:ℝ)^(vkK N t)) ≤ Real.log ((4:ℝ)^(2 * vkS N t)) :=
          Real.log_le_log (by positivity) hle
      _ = ((2 * vkS N t : ℕ):ℝ) * Real.log 4 := Real.log_pow _ _
      _ = 2 * ((vkS N t : ℕ):ℝ) * Real.log 4 := by push_cast; ring
  have hfin : Real.log ((3:ℝ)/2 * (4:ℝ)^(vkK N t)) / (2 * ((vkS N t : ℕ):ℝ)) ≤ Real.log 4 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * ((vkS N t : ℕ):ℝ))]
    linarith [hnum]
  have hAle : vkLogErr Cv1a Cmv Kcnt N t + Real.log ((3:ℝ)/2 * (4:ℝ)^(vkK N t)) / (2 * ((vkS N t : ℕ):ℝ))
      ≤ vkDelta (1 / 100000) N t * Real.log N + Real.log 4 := by
    linarith [hlogerr, hfin]
  rw [hA]
  have hexpδ : Real.exp (vkDelta (1 / 100000) N t * Real.log N) = N ^ vkDelta (1 / 100000) N t := by
    rw [Real.rpow_def_of_pos hNpos]; congr 1; ring
  calc Real.exp (vkLogErr Cv1a Cmv Kcnt N t + Real.log ((3:ℝ)/2 * (4:ℝ)^(vkK N t)) / (2 * ((vkS N t : ℕ):ℝ)))
      ≤ Real.exp (vkDelta (1 / 100000) N t * Real.log N + Real.log 4) := Real.exp_le_exp.mpr hAle
    _ = Real.exp (vkDelta (1 / 100000) N t * Real.log N) * Real.exp (Real.log 4) := by rw [Real.exp_add]
    _ = N ^ vkDelta (1 / 100000) N t * 4 := by rw [hexpδ, Real.exp_log (by norm_num : (0:ℝ) < 4)]
    _ = 4 * N ^ vkDelta (1 / 100000) N t := by ring

end Work.BMF
