import Mathlib
import Submission.Work.BW.even_step_defs
import Submission.Work.BW.bprod_real_le
import Submission.Work.BW.num_xi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-- `ξ = 1 - 0.536/r` lies in `(0,1]` for `r ≥ 2`. -/
lemma pxi_pos_and_le_one {r : ℕ} (hr : 2 ≤ r) : 0 < pxi r ∧ pxi r ≤ 1 := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr2 : (2:ℝ) ≤ r := by exact_mod_cast hr
  refine ⟨?_, ?_⟩ <;> unfold pxi
  · have h : (0.536:ℝ) / r < 1 := by rw [div_lt_one hr0]; linarith
    linarith
  · have h : (0:ℝ) ≤ (0.536:ℝ) / r := by positivity
    linarith

/-- With `S ≥ 1`, the even-step parameter `S' = evSP` is at least `1` (in fact at least `2`). -/
lemma evSP_ge_one {r : ℕ} (hr : 2 ≤ r) {d h J : ℕ} (hS : 1 ≤ (pS r d h : ℝ)) :
    1 ≤ evSP r J (pS r d h : ℝ) := by
  obtain ⟨hxi0, hxi1⟩ := pxi_pos_and_le_one hr
  have hpow : pxi r ^ (-((r * J : ℕ) : ℤ)) = (pxi r ^ (r * J))⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have hp1 : pxi r ^ (r * J) ≤ 1 := pow_le_one₀ (le_of_lt hxi0) hxi1
  have hge1 : 1 ≤ (pxi r ^ (r * J))⁻¹ := (one_le_inv₀ (pow_pos hxi0 (r * J))).mpr hp1
  have haS : 1 ≤ (pxi r ^ (r * J))⁻¹ * (pS r d h : ℝ) := by
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ (pxi r ^ (r * J))⁻¹ * (pS r d h : ℝ) :=
          mul_le_mul hge1 hS (by norm_num) (by linarith)
  have harg : (2:ℝ) ≤ 2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)) := by
    rw [hpow]; linarith
  have h2 : 2 ≤ evSP r J (pS r d h : ℝ) := by
    unfold evSP; exact Nat.le_floor harg
  omega

/-- `(23')` combined with the definition of `evW`: for the lacunary Blaschke product with
`X = 2S'` and `R = 7.2S'`, `‖B'(s;X)‖^{T'+1} ≤ exp(−evW)` whenever `|s| ≤ X+2`. Indeed `(23')`
(proved in `bprod_real_le`) gives `‖B'(s;X)‖ ≤ (max(|s|,X)/R)^X ≤ ((X+2)/R)^X`, and
`(X+2)/R = exp(−log(R/(X+2)))`, so raising to the power `T'+1` gives `exp(−evW)` with
`evW = (T'+1)·X·log(R/(X+2))`. -/
theorem bprodOdd_pow_le_exp_neg_evW {r : ℕ} (hr : 2 ≤ r) {d h J : ℕ} {σ : Fin r → ℝ} {sz : ℝ}
    (hsz : |sz| ≤ (evX r J (pS r d h : ℝ) : ℝ) + 2) (hS : 1 ≤ (pS r d h : ℝ)) :
    ‖bprodOdd (evR r J (pS r d h : ℝ)) (evX r J (pS r d h : ℝ)) (sz : ℂ) ^
        (evTp r J (pT r d σ : ℝ) + 1)‖ ≤ Real.exp (-(evW r d h σ J)) := by
  have hevSP : (1:ℝ) ≤ (evSP r J (pS r d h : ℝ) : ℝ) := by
    exact_mod_cast evSP_ge_one hr hS
  have hevSPpos : (0:ℝ) < (evSP r J (pS r d h : ℝ) : ℝ) := by linarith
  have hRpos : 0 < evR r J (pS r d h : ℝ) := by
    unfold evR; exact mul_pos (by norm_num) hevSPpos
  have hXeq : ((evX r J (pS r d h : ℝ)) : ℝ) = 2 * (evSP r J (pS r d h : ℝ) : ℝ) := by
    unfold evX; push_cast; ring
  have hXR : ((evX r J (pS r d h : ℝ)) : ℝ) < evR r J (pS r d h : ℝ) := by
    rw [hXeq]; unfold evR; nlinarith [hevSPpos]
  have hX2R : ((evX r J (pS r d h : ℝ)) : ℝ) + 2 ≤ evR r J (pS r d h : ℝ) := by
    rw [hXeq]; unfold evR; nlinarith [hevSP]
  have hxR : |sz| ≤ evR r J (pS r d h : ℝ) := le_trans hsz hX2R
  have hEvenX : Even (evX r J (pS r d h : ℝ)) := by
    show Even (2 * evSP r J (pS r d h : ℝ))
    exact even_two_mul _
  have hb := (bprod_real_le (evR r J (pS r d h : ℝ)) (evX r J (pS r d h : ℝ)) hXR sz hxR).2 hEvenX
  have hmax : max |sz| ((evX r J (pS r d h : ℝ)) : ℝ) ≤ ((evX r J (pS r d h : ℝ)) : ℝ) + 2 :=
    max_le hsz (by linarith)
  have hbasenn : 0 ≤ max |sz| ((evX r J (pS r d h : ℝ)) : ℝ) / evR r J (pS r d h : ℝ) :=
    div_nonneg (le_trans (abs_nonneg sz) (le_max_left _ _)) (le_of_lt hRpos)
  have hstep : (max |sz| ((evX r J (pS r d h : ℝ)) : ℝ) / evR r J (pS r d h : ℝ)) ^
        (evX r J (pS r d h : ℝ))
      ≤ ((((evX r J (pS r d h : ℝ)) : ℝ) + 2) / evR r J (pS r d h : ℝ)) ^
        (evX r J (pS r d h : ℝ)) :=
    pow_le_pow_left₀ hbasenn (div_le_div_of_nonneg_right hmax (le_of_lt hRpos)) _
  have hpow : ‖bprodOdd (evR r J (pS r d h : ℝ)) (evX r J (pS r d h : ℝ)) (sz : ℂ)‖ ^
        (evTp r J (pT r d σ : ℝ) + 1)
      ≤ ((((evX r J (pS r d h : ℝ)) : ℝ) + 2) / evR r J (pS r d h : ℝ)) ^
        ((evX r J (pS r d h : ℝ)) * (evTp r J (pT r d σ : ℝ) + 1)) := by
    calc ‖bprodOdd (evR r J (pS r d h : ℝ)) (evX r J (pS r d h : ℝ)) (sz : ℂ)‖ ^
            (evTp r J (pT r d σ : ℝ) + 1)
        ≤ ((max |sz| ((evX r J (pS r d h : ℝ)) : ℝ) / evR r J (pS r d h : ℝ)) ^
            (evX r J (pS r d h : ℝ))) ^ (evTp r J (pT r d σ : ℝ) + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) hb _
      _ ≤ (((((evX r J (pS r d h : ℝ)) : ℝ) + 2) / evR r J (pS r d h : ℝ)) ^
            (evX r J (pS r d h : ℝ))) ^ (evTp r J (pT r d σ : ℝ) + 1) :=
          pow_le_pow_left₀ (pow_nonneg hbasenn _) hstep _
      _ = ((((evX r J (pS r d h : ℝ)) : ℝ) + 2) / evR r J (pS r d h : ℝ)) ^
            ((evX r J (pS r d h : ℝ)) * (evTp r J (pT r d σ : ℝ) + 1)) :=
          (pow_mul _ _ _).symm
  have hbasepos : 0 < (((evX r J (pS r d h : ℝ)) : ℝ) + 2) / evR r J (pS r d h : ℝ) :=
    div_pos (by positivity) hRpos
  have hX2pos : (0:ℝ) < ((evX r J (pS r d h : ℝ) : ℝ) + 2) := by positivity
  have hlog : Real.log ((((evX r J (pS r d h : ℝ)) : ℝ) + 2) / evR r J (pS r d h : ℝ))
      = - Real.log (evR r J (pS r d h : ℝ) / (((evX r J (pS r d h : ℝ)) : ℝ) + 2)) := by
    rw [Real.log_div (ne_of_gt hX2pos) (ne_of_gt hRpos),
        Real.log_div (ne_of_gt hRpos) (ne_of_gt hX2pos)]
    ring
  have hexpeq : Real.log ((((evX r J (pS r d h : ℝ)) : ℝ) + 2) / evR r J (pS r d h : ℝ)) *
        ((((evX r J (pS r d h : ℝ)) * (evTp r J (pT r d σ : ℝ) + 1) : ℕ)) : ℝ)
      = -(evW r d h σ J) := by
    rw [hlog]; unfold evW; push_cast; ring
  rw [norm_pow]
  calc ‖bprodOdd (evR r J (pS r d h : ℝ)) (evX r J (pS r d h : ℝ)) (sz : ℂ)‖ ^
        (evTp r J (pT r d σ : ℝ) + 1)
      ≤ ((((evX r J (pS r d h : ℝ)) : ℝ) + 2) / evR r J (pS r d h : ℝ)) ^
        ((evX r J (pS r d h : ℝ)) * (evTp r J (pT r d σ : ℝ) + 1)) := hpow
    _ = Real.exp (Real.log ((((evX r J (pS r d h : ℝ)) : ℝ) + 2) / evR r J (pS r d h : ℝ)) *
        ((((evX r J (pS r d h : ℝ)) * (evTp r J (pT r d σ : ℝ) + 1) : ℕ)) : ℝ)) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos hbasepos]
    _ = Real.exp (-(evW r d h σ J)) := by rw [hexpeq]

end Work.BW
