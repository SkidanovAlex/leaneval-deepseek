import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.logPhase_iteratedDeriv
import Submission.Work.BMF.J_mono_X
import Submission.Work.BMF.vke_defs
import Submission.Work.BMF.vke_delta
import Submission.Work.BMF.vke_deriv
import Submission.Work.BMF.vke_range_aux
import Submission.Work.BMF.vke_Mval
import Submission.Work.BMF.vk_count_Nset
import Submission.Work.BMF.vk_phase_basic
import Submission.Work.BMF.meanValue_polySum_J
import Submission.Work.BMF.vke_count_bookkeeping
import Submission.Work.BMF.vke_theta_final
import Submission.Work.BMF.vke_logerr_range
import Submission.Work.BMF.vke_Hmu_range
import Submission.Work.BMF.kth_derivative_reduction_uniform
import Submission.Work.BMF.vmvt_uniform

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

namespace Work.BMF

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

/-! ## Auxiliary estimates for the final assembly of `Work.BMF.vk_exp_sum` -/

/-- `0 ≤ η`. -/
theorem vkEta_nonneg {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) : 0 ≤ vkEta N t := by
  have hk6 : (6 : ℝ) ≤ ((vkK N t : ℕ) : ℝ) := by exact_mod_cast vkK_ge_six hN hNt
  have hk1 : 1 ≤ vkK N t := by have := vkK_ge_six hN hNt; omega
  have hmpos : (0 : ℝ) < (((vkK N t - 1 : ℕ)) : ℝ) := by
    rw [Nat.cast_sub hk1]; push_cast; linarith
  rw [vkEta]
  refine mul_nonneg (by positivity) (pow_nonneg ?_ _)
  rw [sub_nonneg, div_le_one hmpos]
  have h1 : (1 : ℝ) ≤ (((vkK N t - 1 : ℕ)) : ℝ) := by
    rw [Nat.cast_sub hk1]; push_cast; linarith
  linarith

/-- `η ≤ 1`. -/
theorem vkEta_le_one {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) : vkEta N t ≤ 1 := by
  have hk6 : (6 : ℝ) ≤ ((vkK N t : ℕ) : ℝ) := by exact_mod_cast vkK_ge_six hN hNt
  refine le_trans (vkEta_le hN hNt) ?_
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- `1 ≤ s`. -/
theorem vkS_ge_one {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) : 1 ≤ vkS N t := by
  have h1 : 1 ≤ vkK N t - 1 := by have := vkK_ge_six hN hNt; omega
  have h2 : 1 ≤ vkR N t := by rw [vkR]; omega
  rw [vkS]
  calc (1 : ℕ) = 1 * 1 := by ring
    _ ≤ (vkK N t - 1) * vkR N t := Nat.mul_le_mul h1 h2

/-- `0 < s`. -/
theorem vkS_pos {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) : (0 : ℝ) < ((vkS N t : ℕ) : ℝ) := by
  have h : (1 : ℝ) ≤ ((vkS N t : ℕ) : ℝ) := by exact_mod_cast vkS_ge_one hN hNt
  linarith

/-- `s = (k-1) r` as real numbers. -/
theorem vkS_cast {N t : ℝ} :
    ((vkS N t : ℕ) : ℝ) = (((vkK N t - 1 : ℕ) : ℝ)) * ((vkR N t : ℕ) : ℝ) := by
  rw [vkS]; push_cast; ring

/-- **The `k³` comparison.**  For `log N` large, `C₀ k³ + log 7 ≤ (λ/(2k)) log N`.
(This is a local copy of `Work.BMF.vke_k3_le` from the sibling module `vke_range`, kept here so
that this module does not depend on the (hazily owned) `vke_range.lean`.) -/
theorem vke_k3_le' (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1 / 100000) (C0 : ℝ) (hC0 : 0 < C0) :
    ∃ U : ℝ, 0 < U ∧ ∀ (N t : ℝ), 2 ≤ N → N ≤ t →
      Real.log t ≤ c * Real.log N ^ (7 / 6 : ℝ) → U ≤ Real.log N →
      C0 * ((vkK N t : ℕ) : ℝ) ^ 3 + Real.log 7 ≤
        (vkLam N t / (2 * ((vkK N t : ℕ) : ℝ))) * Real.log N := by
  obtain ⟨Ub, hUb, hbasic⟩ := vke_basic c hc hc1
  have h70 : (0 : ℝ) < Real.log 7 := Real.log_pos (by norm_num)
  have hA0 : (0 : ℝ) ≤ (32 * C0) ^ 2 := sq_nonneg _
  have hB0 : (0 : ℝ) ≤ 32 * Real.log 7 := by linarith
  refine ⟨Ub + (32 * C0) ^ 2 + 32 * Real.log 7, by linarith, ?_⟩
  intro N t hN hNt hlt hL
  have hLb : Ub ≤ Real.log N := by linarith
  have hLA : (32 * C0) ^ 2 ≤ Real.log N := by linarith
  have hLB : 32 * Real.log 7 ≤ Real.log N := by linarith
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ := hbasic N t hN hNt hlt hLb
  have hNpos : 0 < N := by linarith
  have hLpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hL1 : 1 ≤ Real.log N := by linarith
  have hkRpos : (0 : ℝ) < ((vkK N t : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < vkK N t)
  have hk3 : (((vkK N t : ℕ) : ℝ)) ^ 3 ≤ (Real.log N) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (((vkK N t : ℕ) : ℝ)) 3,
      Real.rpow_le_iff_le_log hkRpos (Real.rpow_pos_of_pos hLpos _), Real.log_rpow hLpos]
    push_cast
    linarith [hb10]
  have hmk : (1 : ℝ) / 8 ≤ vkLam N t / ((vkK N t : ℕ) : ℝ) := vkLam_div_k_ge hN hNt
  have heq : vkLam N t / (2 * ((vkK N t : ℕ) : ℝ))
      = (vkLam N t / ((vkK N t : ℕ) : ℝ)) / 2 := by
    rw [div_div]; congr 1; ring
  have hmk2 : (1 : ℝ) / 16 ≤ vkLam N t / (2 * ((vkK N t : ℕ) : ℝ)) := by
    rw [heq]; linarith
  have hsq : ((Real.log N) ^ (1 / 2 : ℝ)) ^ 2 = Real.log N := by
    rw [← Real.rpow_natCast ((Real.log N) ^ (1 / 2 : ℝ)) 2,
      ← Real.rpow_mul hLpos.le (1 / 2),
      show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have h32 : 32 * C0 ≤ (Real.log N) ^ (1 / 2 : ℝ) := by
    have h2 : (32 * C0) ^ 2 ≤ ((Real.log N) ^ (1 / 2 : ℝ)) ^ 2 := by rw [hsq]; exact hLA
    exact (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hLpos.le _)
      (by norm_num : (2 : ℕ) ≠ 0)).mp h2
  have hA : C0 * (((vkK N t : ℕ) : ℝ)) ^ 3 ≤ Real.log N / 32 := by
    have h1 : C0 * (((vkK N t : ℕ) : ℝ)) ^ 3 ≤ C0 * (Real.log N) ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hk3 hC0.le
    have h2 : C0 * (Real.log N) ^ (1 / 2 : ℝ) ≤ Real.log N / 32 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
      have hh := mul_le_mul_of_nonneg_right h32 (Real.rpow_nonneg hLpos.le (1 / 2 : ℝ))
      have h3 : (Real.log N) ^ (1 / 2 : ℝ) * (Real.log N) ^ (1 / 2 : ℝ) = Real.log N := by
        rw [← Real.rpow_add hLpos, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
      linarith [hh, h3.le, h3.ge]
    linarith [h1, h2]
  have hB : Real.log 7 ≤ Real.log N / 32 := by linarith
  have hfin : (1 : ℝ) / 16 * Real.log N
      ≤ (vkLam N t / (2 * ((vkK N t : ℕ) : ℝ))) * Real.log N :=
    mul_le_mul_of_nonneg_right hmk2 hLpos.le
  have : C0 * (((vkK N t : ℕ) : ℝ)) ^ 3 + Real.log 7 ≤ (1 : ℝ) / 16 * Real.log N := by
    linarith [hA, hB]
  linarith [this, hfin]

/-- **The `exp(C₀k³)·H` term is absorbed by `N^{1−δ}`.** -/
theorem vke_term1 {N t Cv1a : ℝ} (hN : 2 ≤ N) (_hNt : N ≤ t)
    (hHle : vkH N t ≤ 7 * N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)))
    (hC0k3 : Cv1a * ((vkK N t : ℕ) : ℝ)^3 + Real.log 7
        ≤ (vkLam N t / (2 * ((vkK N t : ℕ) : ℝ))) * Real.log N)
    (hδk : vkDelta (1/100000) N t ≤ vkLam N t / (2 * ((vkK N t : ℕ) : ℝ))) :
    Real.exp (Cv1a * ((vkK N t : ℕ) : ℝ)^3) * vkH N t
      ≤ N ^ (1 - vkDelta (1/100000) N t) := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogNpos : 0 < Real.log N := Real.log_pos (by linarith)
  have h1 : Real.exp (Cv1a * ((vkK N t : ℕ) : ℝ)^3) * 7
      ≤ N ^ (vkLam N t / ((vkK N t : ℕ) : ℝ) - vkDelta (1/100000) N t) := by
    rw [Real.le_rpow_iff_log_le (by positivity) hNpos]
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_exp]
    have h2 : vkDelta (1/100000) N t * Real.log N
        ≤ (vkLam N t / (2 * ((vkK N t : ℕ) : ℝ))) * Real.log N :=
      mul_le_mul_of_nonneg_right hδk hlogNpos.le
    have h3 : vkLam N t / ((vkK N t : ℕ) : ℝ)
        = 2 * (vkLam N t / (2 * ((vkK N t : ℕ) : ℝ))) := by field_simp
    rw [h3]
    nlinarith [hC0k3, h2]
  have h4 : Real.exp (Cv1a * ((vkK N t : ℕ) : ℝ)^3) * vkH N t
      ≤ Real.exp (Cv1a * ((vkK N t : ℕ) : ℝ)^3)
        * (7 * N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_left hHle (Real.exp_pos _).le
  have h5 : Real.exp (Cv1a * ((vkK N t : ℕ) : ℝ)^3)
        * (7 * N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)))
      ≤ N ^ (1 - vkDelta (1/100000) N t) := by
    calc Real.exp (Cv1a * ((vkK N t : ℕ) : ℝ)^3)
          * (7 * N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)))
        = (Real.exp (Cv1a * ((vkK N t : ℕ) : ℝ)^3) * 7)
          * N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)) := by ring
      _ ≤ N ^ (vkLam N t / ((vkK N t : ℕ) : ℝ) - vkDelta (1/100000) N t)
            * N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by linarith) _)
      _ = N ^ ((vkLam N t / ((vkK N t : ℕ) : ℝ) - vkDelta (1/100000) N t)
            + (1 - vkLam N t / ((vkK N t : ℕ) : ℝ))) := by
          rw [← Real.rpow_add hNpos]
      _ = N ^ (1 - vkDelta (1/100000) N t) := by congr 1; ring
  exact le_trans h4 h5



/-- **The final arithmetic assembly of the Vinogradov reduction.**  Combines the `H`-term, the
counting bound `hcount`, the `M`-value bound `hMvbd` and the constant bookkeeping `hΘle` into the
conclusion `exp(C₀k³)(H + k²M^{1−1/s}𝒩^{1/2s}(H^{−2s+k(k−1)/2}Mv)^{1/2s}) ≤ C_max N^{1−δ_req}`. -/
theorem vke_final_bound {N t u Cv1a Cmv Kcnt Mv Cmax : ℝ} {M : ℕ}
    (hN : 2 ≤ N) (hNt : N ≤ t) (hCmax : 5 ≤ Cmax) (hKcnt : 0 < Kcnt)
    (hH1 : 1 ≤ vkH N t)
    (hHle : vkH N t ≤ 7 * N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)))
    (hC0k3 : Cv1a * ((vkK N t : ℕ) : ℝ) ^ 3 + Real.log 7
        ≤ (vkLam N t / (2 * ((vkK N t : ℕ) : ℝ))) * Real.log N)
    (h2delta : 2 * vkDelta (1 / 100000) N t ≤ vkDeltaA N t)
    (hδk : vkDelta (1 / 100000) N t ≤ vkLam N t / (2 * ((vkK N t : ℕ) : ℝ)))
    (hM2N : (M : ℝ) ≤ 2 * N)
    (hcount : (((Nset (vkK N t) M (blkPh ⌊N⌋₊ t u) (vkH N t)).ncard : ℕ) : ℝ)
        ≤ 84 * Kcnt * ((4 : ℝ) ^ (vkK N t)) ^ 2 * ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)
            * N ^ (2 - vkLam N t / ((vkK N t : ℕ) : ℝ)))
    (hΘle : Real.exp (Cv1a * ((vkK N t : ℕ) : ℝ) ^ 3 + Real.log (14 * ((vkK N t : ℕ) : ℝ) ^ 2)
        + Real.log (84 * Kcnt * ((4 : ℝ) ^ (vkK N t)) ^ 2
            * ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)) / (2 * ((vkS N t : ℕ) : ℝ))
        + Cmv * ((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ)
            * (1 + Real.log (((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ))) / 2)
        ≤ 4 * N ^ vkDelta (1 / 100000) N t)
    (hMvbd : vkH N t ^ (-(2 * ((vkS N t : ℕ) : ℝ)) + ((vkK N t : ℕ) : ℝ) * (((vkK N t : ℕ) : ℝ) - 1) / 2) * Mv
        ≤ Real.exp (Cmv * (((vkK N t - 1 : ℕ) : ℝ)) ^ 2 * ((vkR N t : ℕ) : ℝ) ^ 2
            * (1 + Real.log ((((vkK N t - 1 : ℕ) : ℝ)) * ((vkR N t : ℕ) : ℝ))))
          * (7 * N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ))) ^ vkEta N t)
    (hMvnn : 0 ≤ Mv) :
    Real.exp (Cv1a * ((vkK N t : ℕ) : ℝ) ^ 3)
        * (vkH N t + ((vkK N t : ℕ) : ℝ) ^ 2 * (M : ℝ) ^ (1 - 1 / ((vkS N t : ℕ) : ℝ))
            * (((Nset (vkK N t) M (blkPh ⌊N⌋₊ t u) (vkH N t)).ncard : ℕ) : ℝ) ^ (1 / (2 * ((vkS N t : ℕ) : ℝ)))
            * ((vkH N t ^ (-(2 * ((vkS N t : ℕ) : ℝ)) + ((vkK N t : ℕ) : ℝ) * (((vkK N t : ℕ) : ℝ) - 1) / 2)) * Mv)
                ^ (1 / (2 * ((vkS N t : ℕ) : ℝ))))
      ≤ Cmax * N ^ (1 - (1 / 100000) * (Real.log N / Real.log t) ^ 2
          / Real.log (Real.log t / Real.log N + 2)) := by
  set kR : ℝ := ((vkK N t : ℕ) : ℝ) with hkR
  set k1R : ℝ := (((vkK N t - 1 : ℕ) : ℝ)) with hk1R
  set rR : ℝ := ((vkR N t : ℕ) : ℝ) with hrR
  set sR : ℝ := ((vkS N t : ℕ) : ℝ) with hsR
  set fR : ℝ := ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ) with hfR
  set A : ℝ := (4 : ℝ) ^ (vkK N t) with hA
  set NN : ℝ := (((Nset (vkK N t) M (blkPh ⌊N⌋₊ t u) (vkH N t)).ncard : ℕ) : ℝ) with hNN
  set X : ℝ := 7 * N ^ (1 - vkLam N t / kR) with hX
  set Z : ℝ := 84 * Kcnt * A ^ 2 * fR with hZ
  set bb : ℝ := Cmv * k1R * rR * (1 + Real.log (k1R * rR)) / 2 with hbb
  set Th : ℝ := Real.exp (Cv1a * kR ^ 3 + Real.log (14 * kR ^ 2) + Real.log Z / (2 * sR) + bb) with hTh
  have hNpos : (0 : ℝ) < N := by linarith
  have hHpos : 0 < vkH N t := lt_of_lt_of_le one_pos hH1
  have hkpos : 0 < kR := by
    rw [hkR]; exact_mod_cast (by have := vkK_ge_six hN hNt; omega : 0 < vkK N t)
  have hsRpos : 0 < sR := by rw [hsR]; exact vkS_pos hN hNt
  have hsR1 : (1 : ℝ) ≤ sR := by rw [hsR]; exact_mod_cast vkS_ge_one hN hNt
  have h2sRpos : 0 < 2 * sR := by linarith
  have hApos : 0 < A := by rw [hA]; positivity
  have hZpos : 0 < Z := by rw [hZ, hA, hfR]; positivity
  have heta_nn : 0 ≤ vkEta N t := vkEta_nonneg hN hNt
  have heta_le : vkEta N t ≤ 1 := vkEta_le_one hN hNt
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hs_eq : sR = k1R * rR := by rw [hsR, hk1R, hrR]; exact vkS_cast
  -- (1) the `H`-term
  have hterm1 : Real.exp (Cv1a * kR ^ 3) * vkH N t ≤ N ^ (1 - vkDelta (1 / 100000) N t) :=
    vke_term1 hN hNt hHle hC0k3 hδk
  -- (2) the M-value factor
  have hMvb : (vkH N t ^ (-(2 * sR) + kR * (kR - 1) / 2)) * Mv
      ≤ Real.exp (bb * (2 * sR)) * X ^ vkEta N t := by
    have hE : Cmv * k1R ^ 2 * rR ^ 2 * (1 + Real.log (k1R * rR)) = bb * (2 * sR) := by
      rw [hbb, hs_eq]; ring
    rw [hE] at hMvbd
    exact hMvbd
  have hA3 : ((vkH N t ^ (-(2 * sR) + kR * (kR - 1) / 2)) * Mv) ^ (1 / (2 * sR))
      ≤ Real.exp bb * (7 * N ^ ((1 - vkLam N t / kR) * vkEta N t / (2 * sR))) := by
    have hnn : 0 ≤ (vkH N t ^ (-(2 * sR) + kR * (kR - 1) / 2)) * Mv :=
      mul_nonneg (Real.rpow_nonneg hHpos.le _) hMvnn
    have h1 : (Real.exp (bb * (2 * sR)) * X ^ vkEta N t) ^ (1 / (2 * sR))
        = Real.exp (bb * (2 * sR) * (1 / (2 * sR))) * X ^ (vkEta N t * (1 / (2 * sR))) := by
      rw [Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg hXnn _)]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.rpow_mul hXnn]
    have h2 : X ^ (vkEta N t * (1 / (2 * sR)))
        = 7 ^ (vkEta N t * (1 / (2 * sR)))
          * N ^ ((1 - vkLam N t / kR) * (vkEta N t * (1 / (2 * sR)))) := by
      rw [hX, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hNpos.le _),
        ← Real.rpow_mul hNpos.le]
    have h3 : (7 : ℝ) ^ (vkEta N t * (1 / (2 * sR))) ≤ 7 := by
      have hh : vkEta N t * (1 / (2 * sR)) ≤ 1 := by
        rw [mul_one_div, div_le_one h2sRpos]; linarith
      calc (7 : ℝ) ^ (vkEta N t * (1 / (2 * sR))) ≤ (7 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 7 by norm_num) hh
        _ = 7 := Real.rpow_one 7
    have hbb' : bb * (2 * sR) * (1 / (2 * sR)) = bb := by field_simp
    have harg : (1 - vkLam N t / kR) * (vkEta N t * (1 / (2 * sR)))
        = (1 - vkLam N t / kR) * vkEta N t / (2 * sR) := by ring
    have hstep := Real.rpow_le_rpow hnn hMvb (show (0 : ℝ) ≤ 1 / (2 * sR) by positivity)
    refine le_trans hstep ?_
    rw [h1, h2, hbb', harg]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hNpos.le _))
      (Real.exp_pos bb).le
  -- (3) the three bounds on the individual factors
  have hA1 : (M : ℝ) ^ (1 - 1 / sR) ≤ 2 * N ^ (1 - 1 / sR) := by
    have hexp : (0 : ℝ) ≤ 1 - 1 / sR := by
      rw [sub_nonneg, div_le_one hsRpos]; linarith
    calc (M : ℝ) ^ (1 - 1 / sR) ≤ (2 * N) ^ (1 - 1 / sR) :=
          Real.rpow_le_rpow (by positivity) hM2N hexp
      _ = (2 : ℝ) ^ (1 - 1 / sR) * N ^ (1 - 1 / sR) :=
          Real.mul_rpow (by norm_num) hNpos.le
      _ ≤ 2 * N ^ (1 - 1 / sR) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hNpos.le _)
          calc (2 : ℝ) ^ (1 - 1 / sR) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
                  (by have h : (0 : ℝ) ≤ 1 / sR := by positivity
                      linarith)
            _ = 2 := Real.rpow_one 2
  have hA2 : NN ^ (1 / (2 * sR)) ≤ Z ^ (1 / (2 * sR)) * N ^ ((2 - vkLam N t / kR) / (2 * sR)) := by
    calc NN ^ (1 / (2 * sR)) ≤ (Z * N ^ (2 - vkLam N t / kR)) ^ (1 / (2 * sR)) :=
          Real.rpow_le_rpow (by positivity) (by rw [hZ]; exact hcount) (by positivity)
      _ = Z ^ (1 / (2 * sR)) * N ^ ((2 - vkLam N t / kR) * (1 / (2 * sR))) := by
          rw [Real.mul_rpow hZpos.le (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le]
      _ = Z ^ (1 / (2 * sR)) * N ^ ((2 - vkLam N t / kR) / (2 * sR)) := by
          congr 1; rw [mul_one_div]
  -- the exponent identity
  have hpow : N ^ (1 - 1 / sR) * (N ^ ((2 - vkLam N t / kR) / (2 * sR))
        * N ^ ((1 - vkLam N t / kR) * vkEta N t / (2 * sR))) = N ^ (1 - vkDeltaA N t) := by
    have e : (1 - 1 / sR) + ((2 - vkLam N t / kR) / (2 * sR)
          + (1 - vkLam N t / kR) * vkEta N t / (2 * sR)) = 1 - vkDeltaA N t := by
      rw [vkDeltaA, ← hkR, ← hsR]
      field_simp
      ring
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, e]
  -- the constant
  have hconst : 14 * Real.exp (Cv1a * kR ^ 3) * kR ^ 2 * Z ^ (1 / (2 * sR)) * Real.exp bb ≤ Th := by
    have hZpow : Z ^ (1 / (2 * sR)) = Real.exp (Real.log Z / (2 * sR)) := by
      rw [Real.rpow_def_of_pos hZpos, mul_one_div]
    have key : 14 * Real.exp (Cv1a * kR ^ 3) * kR ^ 2 * Z ^ (1 / (2 * sR)) * Real.exp bb
        = Real.exp (Cv1a * kR ^ 3) * Real.exp (Real.log (14 * kR ^ 2))
          * Real.exp (Real.log Z / (2 * sR)) * Real.exp bb := by
      rw [hZpow, Real.exp_log (by positivity : (0:ℝ) < 14 * kR ^ 2)]
      ring
    rw [key, hTh, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  -- (4) the second term
  have hterm2 : Real.exp (Cv1a * kR ^ 3)
      * (kR ^ 2 * (M : ℝ) ^ (1 - 1 / sR) * NN ^ (1 / (2 * sR))
          * ((vkH N t ^ (-(2 * sR) + kR * (kR - 1) / 2)) * Mv) ^ (1 / (2 * sR)))
      ≤ 4 * N ^ (1 - vkDelta (1 / 100000) N t) := by
    have hsplit : Real.exp (Cv1a * kR ^ 3)
        * (kR ^ 2 * (M : ℝ) ^ (1 - 1 / sR) * NN ^ (1 / (2 * sR))
            * ((vkH N t ^ (-(2 * sR) + kR * (kR - 1) / 2)) * Mv) ^ (1 / (2 * sR)))
        = Real.exp (Cv1a * kR ^ 3) * (kR ^ 2 * (M : ℝ) ^ (1 - 1 / sR)) * NN ^ (1 / (2 * sR))
          * ((vkH N t ^ (-(2 * sR) + kR * (kR - 1) / 2)) * Mv) ^ (1 / (2 * sR)) := by ring
    rw [hsplit]
    calc Real.exp (Cv1a * kR ^ 3) * (kR ^ 2 * (M : ℝ) ^ (1 - 1 / sR)) * NN ^ (1 / (2 * sR))
          * ((vkH N t ^ (-(2 * sR) + kR * (kR - 1) / 2)) * Mv) ^ (1 / (2 * sR))
        ≤ Real.exp (Cv1a * kR ^ 3) * (kR ^ 2 * (2 * N ^ (1 - 1 / sR)))
          * (Z ^ (1 / (2 * sR)) * N ^ ((2 - vkLam N t / kR) / (2 * sR)))
          * (Real.exp bb * (7 * N ^ ((1 - vkLam N t / kR) * vkEta N t / (2 * sR)))) := by
          gcongr
      _ = (14 * Real.exp (Cv1a * kR ^ 3) * kR ^ 2 * Z ^ (1 / (2 * sR)) * Real.exp bb)
          * (N ^ (1 - 1 / sR) * (N ^ ((2 - vkLam N t / kR) / (2 * sR))
              * N ^ ((1 - vkLam N t / kR) * vkEta N t / (2 * sR)))) := by ring
      _ = (14 * Real.exp (Cv1a * kR ^ 3) * kR ^ 2 * Z ^ (1 / (2 * sR)) * Real.exp bb)
          * N ^ (1 - vkDeltaA N t) := by rw [hpow]
      _ ≤ Th * N ^ (1 - vkDeltaA N t) :=
          mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hNpos.le _)
      _ ≤ (4 * N ^ vkDelta (1 / 100000) N t) * N ^ (1 - vkDeltaA N t) :=
          mul_le_mul_of_nonneg_right hΘle (Real.rpow_nonneg hNpos.le _)
      _ = 4 * (N ^ vkDelta (1 / 100000) N t * N ^ (1 - vkDeltaA N t)) := by ring
      _ = 4 * N ^ (vkDelta (1 / 100000) N t + (1 - vkDeltaA N t)) := by rw [← Real.rpow_add hNpos]
      _ ≤ 4 * N ^ (1 - vkDelta (1 / 100000) N t) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
          linarith [h2delta]
  -- (5) assemble
  have hgoal : Real.exp (Cv1a * kR ^ 3)
        * (vkH N t + kR ^ 2 * (M : ℝ) ^ (1 - 1 / sR) * NN ^ (1 / (2 * sR))
            * ((vkH N t ^ (-(2 * sR) + kR * (kR - 1) / 2)) * Mv) ^ (1 / (2 * sR)))
      ≤ Cmax * N ^ (1 - vkDelta (1 / 100000) N t) := by
    have hsplit : Real.exp (Cv1a * kR ^ 3)
        * (vkH N t + kR ^ 2 * (M : ℝ) ^ (1 - 1 / sR) * NN ^ (1 / (2 * sR))
            * ((vkH N t ^ (-(2 * sR) + kR * (kR - 1) / 2)) * Mv) ^ (1 / (2 * sR)))
        = Real.exp (Cv1a * kR ^ 3) * vkH N t
          + Real.exp (Cv1a * kR ^ 3)
            * (kR ^ 2 * (M : ℝ) ^ (1 - 1 / sR) * NN ^ (1 / (2 * sR))
                * ((vkH N t ^ (-(2 * sR) + kR * (kR - 1) / 2)) * Mv) ^ (1 / (2 * sR))) := by ring
    rw [hsplit]
    calc Real.exp (Cv1a * kR ^ 3) * vkH N t
          + Real.exp (Cv1a * kR ^ 3)
            * (kR ^ 2 * (M : ℝ) ^ (1 - 1 / sR) * NN ^ (1 / (2 * sR))
                * ((vkH N t ^ (-(2 * sR) + kR * (kR - 1) / 2)) * Mv) ^ (1 / (2 * sR)))
        ≤ N ^ (1 - vkDelta (1 / 100000) N t) + 4 * N ^ (1 - vkDelta (1 / 100000) N t) :=
          add_le_add hterm1 hterm2
      _ = 5 * N ^ (1 - vkDelta (1 / 100000) N t) := by ring
      _ ≤ Cmax * N ^ (1 - vkDelta (1 / 100000) N t) :=
          mul_le_mul_of_nonneg_right hCmax (Real.rpow_nonneg hNpos.le _)
  have hδeq : (1 - vkDelta (1 / 100000) N t)
      = 1 - (1 / 100000) * (Real.log N / Real.log t) ^ 2
          / Real.log (Real.log t / Real.log N + 2) := by
    rw [vkDelta, vkLam]
  rw [← hδeq]
  exact hgoal


lemma eC_exp_eq' (y : ℝ) : eC y = Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) := by
  unfold eC
  congr 1
  push_cast
  ring

lemma card_Ioc_floor_le (N R : ℝ) (hN : 0 ≤ N) (hR : R ≤ 2 * N) :
    (((Finset.Ioc ⌊N⌋₊ ⌊R⌋₊).card : ℕ) : ℝ) ≤ N + 1 := by
  rw [Nat.card_Ioc]
  have hRle : (⌊R⌋₊ : ℝ) ≤ 2 * N := by
    have h1 : ⌊R⌋₊ ≤ ⌊2 * N⌋₊ := Nat.floor_mono hR
    have h2 : (⌊2 * N⌋₊ : ℝ) ≤ 2 * N := Nat.floor_le (by linarith)
    exact le_trans (by exact_mod_cast h1) h2
  have hNlt : N < (⌊N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one N
  rcases le_or_gt ⌊R⌋₊ ⌊N⌋₊ with h | h
  · have hz : ⌊R⌋₊ - ⌊N⌋₊ = 0 := Nat.sub_eq_zero_of_le h
    rw [hz]; simp; linarith
  · have hcast : ((⌊R⌋₊ - ⌊N⌋₊ : ℕ) : ℝ) = (⌊R⌋₊ : ℝ) - (⌊N⌋₊ : ℝ) := by
      rw [Nat.cast_sub (le_of_lt h)]
    rw [hcast]; linarith

lemma norm_cpow_term_le_one (t u : ℝ) (n : ℕ) (hn : 1 ≤ n) (hu : 0 < u) :
    ‖((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + u := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  simp

/-- The phase of the block sum, shifted. -/
lemma blkPh_eq_comp (L : ℕ) (t u : ℝ) :
    blkPh L t u = fun x : ℝ => (fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi)) (x + (L:ℝ)) := by
  funext x
  simp only [blkPh]
  ring_nf

/-- Continuity/differentiability of the `(k-1)`-st iterated derivative of the block phase. -/
lemma blkPh_iteratedDeriv_eq (L : ℕ) (t u : ℝ) (n : ℕ) :
    (fun x : ℝ => iteratedDeriv n (blkPh L t u) x)
      = fun x : ℝ => iteratedDeriv n (fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi)) (x + (L:ℝ)) := by
  have hfun : blkPh L t u
      = fun x : ℝ => (fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi)) (x + (L : ℝ)) :=
    blkPh_eq_comp L t u
  have h := iteratedDeriv_comp_add_const
    (f := fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi)) (s := (L : ℝ)) (n := n)
  simp only [hfun, h]

/-- **V1 (revised 09-27). Vinogradov exponential sum, restricted range, classical exponent.**
With `λ = log t / log N`: `‖Σ_{N<n≤R} (n+u)^{-it}‖ ≤ C N^{1 − c/(λ² log(λ+2))}` whenever
`log t ≤ c (log N)^{7/6}`, i.e. `λ ≤ c (log N)^{1/6}`. The factor `log λ` comes from
`s ≍ k² log k` in V0; the range comes from the reduction constant `exp(C₀k³)` of V1a. -/
theorem vk_exp_sum :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (N t : ℝ), 2 ≤ N → N ≤ t →
      Real.log t ≤ c * Real.log N ^ (7 / 6 : ℝ) →
      ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ R : ℝ, N < R → R ≤ 2 * N →
        ‖∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
          C * N ^ (1 - c * (Real.log N / Real.log t) ^ 2 /
            Real.log (Real.log t / Real.log N + 2)) := by
  obtain ⟨Cv1a, hCv1a1, hV1a⟩ := kth_derivative_reduction_uniform
  have hCv1apos : 0 < Cv1a := by linarith
  obtain ⟨Kcnt, hKcnt, hcnt⟩ := vk_count_Nset
  obtain ⟨Cmv, hCmv, hMval⟩ := vke_Mval
  obtain ⟨U1, hU1pos, hU1⟩ := vke_Hmu_range
  obtain ⟨U2, hU2pos, hU2⟩ := vke_logerr_range Cv1a Cmv Kcnt hCv1apos hCmv hKcnt
  obtain ⟨U3, hU3pos, hU3⟩ := vke_k3_le' (1 / 100000) (by norm_num) (by norm_num) Cv1a hCv1apos
  set U : ℝ := U1 + U2 + U3 + 2 with hUdef
  have hUpos : 0 < U := by rw [hUdef]; linarith
  have hδeq : ∀ N t : ℝ, (1 - vkDelta (1 / 100000) N t)
      = 1 - (1 / 100000) * (Real.log N / Real.log t) ^ 2
          / Real.log (Real.log t / Real.log N + 2) := by
    intro N t
    rw [vkDelta, vkLam]
  refine ⟨max 5 (6 * Real.exp (U + 2)), 1 / 100000, by positivity, by norm_num, ?_⟩
  intro N t hN hNt hlog u hu hu1 R hR hR2
  have hNpos : (0 : ℝ) < N := by linarith
  by_cases hsmall : Real.log N ≤ U
  · -- ## the trivial branch
    have hcard := card_Ioc_floor_le N R (by linarith) hR2
    have hnorm : ‖∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊,
        ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ N + 1 := by
      refine le_trans (norm_sum_le _ _) ?_
      have h2 : ∀ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊,
          ‖((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ (1 : ℝ) := by
        intro n hn
        have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
        exact norm_cpow_term_le_one t u n hn1 hu
      calc (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊,
              ‖((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖)
          ≤ ∑ _n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, (1 : ℝ) := Finset.sum_le_sum h2
        _ = ((Finset.Ioc ⌊N⌋₊ ⌊R⌋₊).card : ℝ) := by simp
        _ ≤ N + 1 := hcard
    have hδle1 : vkDelta (1 / 100000) N t ≤ 1 := by
      have hlog2pos : 0 < Real.log (vkLam N t + 2) := by
        have := vkLam_ge_one hN hNt
        exact Real.log_pos (by linarith)
      rw [vkDelta, div_le_one hlog2pos]
      have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
      have hq : (Real.log N / Real.log t) ^ 2 ≤ 1 := by
        have h1 : Real.log N / Real.log t ≤ 1 :=
          (div_le_one hlogtpos).mpr (Real.log_le_log (by linarith) hNt)
        have h2 : 0 ≤ Real.log N / Real.log t :=
          div_nonneg (Real.log_pos (by linarith)).le hlogtpos.le
        nlinarith [h1, h2]
      have h2 : (1 / 100000 : ℝ) ≤ Real.log (vkLam N t + 2) := by
        have h3 : Real.log 2 ≤ Real.log (vkLam N t + 2) :=
          Real.log_le_log (by norm_num) (by have := vkLam_ge_one hN hNt; linarith)
        have h4 : (0.693 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
        linarith
      nlinarith [hq, h2]
    have hrpow1 : (1 : ℝ) ≤ N ^ (1 - vkDelta (1 / 100000) N t) :=
      Real.one_le_rpow (by linarith) (by linarith)
    have hNle : N ≤ Real.exp U := by
      calc N = Real.exp (Real.log N) := (Real.exp_log hNpos).symm
        _ ≤ Real.exp U := Real.exp_le_exp.mpr hsmall
    have hexp_le : Real.exp U ≤ Real.exp (U + 2) := Real.exp_le_exp.mpr (by linarith)
    have hmain : N + 1 ≤ max 5 (6 * Real.exp (U + 2)) * N ^ (1 - vkDelta (1 / 100000) N t) := by
      have h1 : (6 * Real.exp (U + 2)) ≤ max 5 (6 * Real.exp (U + 2)) := le_max_right _ _
      have h3 : N ≤ Real.exp (U + 2) := le_trans hNle hexp_le
      have h2 : (N : ℝ) + 1 ≤ 6 * Real.exp (U + 2) := by
        nlinarith [Real.exp_pos (U + 2), h3, hN]
      nlinarith [hrpow1, h1, h2]
    rw [← hδeq N t]
    exact le_trans hnorm hmain
  · -- ## the main branch
    push Not at hsmall
    have hleU1 : U1 ≤ U := by rw [hUdef]; linarith
    have hleU2 : U2 ≤ U := by rw [hUdef]; linarith
    have hleU3 : U3 ≤ U := by rw [hUdef]; linarith
    obtain ⟨hmu_le, hmuM_le, hH1, hHle⟩ := hU1 N t hN hNt hlog (le_trans hleU1 hsmall.le)
    have hlogerr := hU2 N t hN hNt hlog (le_trans hleU2 hsmall.le)
    have hC0k3 := hU3 N t hN hNt hlog (le_trans hleU3 hsmall.le)
    obtain ⟨h2delta, hδk, hδ0, hlamk⟩ :=
      vke_delta (1 / 100000) N t (by norm_num) (by norm_num) hN hNt
    have hlogNpos : 0 < Real.log N := Real.log_pos (by linarith)
    have hlogNge : 2 ≤ Real.log N := by
      have h2 : (2 : ℝ) ≤ U := by rw [hUdef]; linarith
      linarith
    have hN3 : 3 ≤ N := by
      have h3exp : (3 : ℝ) ≤ Real.exp 2 := by
        have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 1]
      have h2 : Real.exp 2 ≤ N :=
        (Real.log_le_log_iff (Real.exp_pos 2) hNpos).mp (by rw [Real.log_exp]; exact hlogNge)
      linarith
    have hRu : (⌊R⌋₊ : ℝ) ≤ 2 * N := by
      have h1 : ⌊R⌋₊ ≤ ⌊2 * N⌋₊ := Nat.floor_mono hR2
      have h2 : (⌊2 * N⌋₊ : ℝ) ≤ 2 * N := Nat.floor_le (by linarith)
      exact le_trans (by exact_mod_cast h1) h2
    have hLle : ⌊N⌋₊ ≤ ⌊R⌋₊ := Nat.floor_mono (le_of_lt hR)
    by_cases hM0 : ⌊R⌋₊ - ⌊N⌋₊ = 0
    · have hempty : Finset.Ioc ⌊N⌋₊ ⌊R⌋₊ = ∅ := by
        rw [← Finset.card_eq_zero, Nat.card_Ioc]; exact hM0
      rw [hempty, Finset.sum_empty, norm_zero]
      rw [← hδeq N t]
      exact mul_nonneg (le_trans (by norm_num) (le_max_left _ _)) (Real.rpow_nonneg (by linarith) _)
    · set M : ℕ := ⌊R⌋₊ - ⌊N⌋₊ with hMdef
      have hM1 : 1 ≤ M := by omega
      have hM2N : (M : ℝ) ≤ 2 * N := by
        have h9 : (M : ℝ) ≤ (⌊R⌋₊ : ℝ) := by
          have : M ≤ ⌊R⌋₊ := by omega
          exact_mod_cast this
        linarith
      have hLM : (⌊N⌋₊ : ℝ) + (M : ℝ) = (⌊R⌋₊ : ℝ) := by
        rw [hMdef, Nat.cast_sub hLle]; ring
      -- ## parameters
      have hk6 : 6 ≤ vkK N t := vkK_ge_six hN hNt
      have hk2 : 2 ≤ vkK N t := by omega
      have hk3 : 3 ≤ vkK N t := by omega
      have hk1 : 1 ≤ vkK N t := by omega
      have hkeven : Even (vkK N t) := ⟨⌈2 * vkLam N t⌉₊ + 1, by rw [vkK]; omega⟩
      have hk6r : (6 : ℝ) ≤ ((vkK N t : ℕ) : ℝ) := by exact_mod_cast hk6
      have hkpos : (0 : ℝ) < ((vkK N t : ℕ) : ℝ) := by linarith
      have ht_pos : 0 < t := by linarith
      have hs1 : 1 ≤ vkS N t := vkS_ge_one hN hNt
      have hspos : (0 : ℝ) < ((vkS N t : ℕ) : ℝ) := vkS_pos hN hNt
      have hA1 : (1 : ℝ) ≤ (4 : ℝ) ^ (vkK N t) := one_le_pow₀ (by norm_num)
      have hApos : (0 : ℝ) < (4 : ℝ) ^ (vkK N t) := lt_of_lt_of_le one_pos hA1
      have hlam_pos : 0 < vkMu N t / (4 : ℝ) ^ (vkK N t) :=
        div_pos (vkMu_pos N t hN hNt) hApos
      have hHpos : 0 < vkH N t := lt_of_lt_of_le one_pos hH1
      have hAlam : (4 : ℝ) ^ (vkK N t) * (vkMu N t / (4 : ℝ) ^ (vkK N t)) = vkMu N t := by
        rw [mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt hApos)
      have hAlam_le : (4 : ℝ) ^ (vkK N t) * (vkMu N t / (4 : ℝ) ^ (vkK N t)) ≤ 1 / 4 := by
        rw [hAlam]; exact hmu_le
      have hHdef : vkH N t
          = ((4 : ℝ) ^ (vkK N t) * (vkMu N t / (4 : ℝ) ^ (vkK N t))) ^ (-(1 / ((vkK N t : ℕ) : ℝ))) := by
        rw [hAlam]; rfl
      -- ## the phase facts
      have hbig := vk_phase_basic (vkK N t) hk1 t u ((⌊N⌋₊ : ℝ) + (M : ℝ)) hu
      have hmaps : Set.MapsTo (fun x : ℝ => x + (⌊N⌋₊ : ℝ)) (Set.Ioo 0 ((M : ℝ) + 1))
          (Set.Ioo 0 (((⌊N⌋₊ : ℝ) + (M : ℝ)) + 1)) := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := hx
        exact ⟨by linarith, by linarith⟩
      have hcd : ContDiffOn ℝ (vkK N t) (blkPh ⌊N⌋₊ t u) (Set.Ioo 0 ((M : ℝ) + 1)) := by
        rw [blkPh_eq_comp]
        exact (hbig.1).comp (contDiffOn_id.add contDiffOn_const) hmaps
      have hmapsc : Set.MapsTo (fun x : ℝ => x + (⌊N⌋₊ : ℝ)) (Set.Icc 0 (M : ℝ))
          (Set.Icc 0 ((⌊N⌋₊ : ℝ) + (M : ℝ))) := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := hx
        exact ⟨by linarith, by linarith⟩
      have hcont : ContinuousOn (fun x : ℝ => iteratedDeriv (vkK N t - 1) (blkPh ⌊N⌋₊ t u) x)
          (Set.Icc 0 (M : ℝ)) := by
        rw [blkPh_iteratedDeriv_eq]
        exact (hbig.2.1).comp ((continuous_id.add continuous_const).continuousOn) hmapsc
      have hmapsd : Set.MapsTo (fun x : ℝ => x + (⌊N⌋₊ : ℝ)) (Set.Ioo 0 (M : ℝ))
          (Set.Ioo 0 ((⌊N⌋₊ : ℝ) + (M : ℝ))) := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := hx
        exact ⟨by linarith, by linarith⟩
      have hdiff : DifferentiableOn ℝ (fun x : ℝ => iteratedDeriv (vkK N t - 1) (blkPh ⌊N⌋₊ t u) x)
          (Set.Ioo 0 (M : ℝ)) := by
        rw [blkPh_iteratedDeriv_eq]
        exact (hbig.2.2).comp (differentiableOn_id.add (differentiableOn_const (c := (⌊N⌋₊ : ℝ)))) hmapsd
      -- ## the derivative bounds
      have hD2 : ((⌊N⌋₊ : ℝ) + (M : ℝ) + 1 + u) ≤ 4 * (N - 1) := by
        rw [hLM]; nlinarith [hRu, hu1, hN3]
      have hD1 : (0 : ℝ) < 4 * (N - 1) := by linarith
      have hDpow : ((⌊N⌋₊ : ℝ) + (M : ℝ) + 1 + u) ^ (vkK N t) ≤ (4 * (N - 1)) ^ (vkK N t) :=
        pow_le_pow_left₀ (le_of_lt (by linarith : (0 : ℝ) < (⌊N⌋₊ : ℝ) + (M : ℝ) + 1 + u)) hD2 _
      have hnum_pos : (0 : ℝ) ≤ (t / (2 * Real.pi)) * ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ) :=
        mul_nonneg (div_nonneg ht_pos.le (by positivity)) (by positivity)
      have hderiv : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) ((M : ℝ) + 1) →
          vkMu N t / (4 : ℝ) ^ (vkK N t) ≤ iteratedDeriv (vkK N t) (blkPh ⌊N⌋₊ t u) x ∧
          iteratedDeriv (vkK N t) (blkPh ⌊N⌋₊ t u) x
            ≤ (4 : ℝ) ^ (vkK N t) * (vkMu N t / (4 : ℝ) ^ (vkK N t)) := by
        intro x hx
        obtain ⟨hlow, hup⟩ := vke_deriv (vkK N t) ⌊N⌋₊ M t u hk2 hkeven ht_pos hu x hx
        constructor
        · have hgoal : vkMu N t / (4 : ℝ) ^ (vkK N t)
              = (t / (2 * Real.pi)) * ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)
                  / ((4 : ℝ) ^ (vkK N t) * (N - 1) ^ (vkK N t)) := by
            rw [vkMu]; ring
          rw [hgoal]
          have hDpow2 : ((⌊N⌋₊ : ℝ) + (M : ℝ) + 1 + u) ^ (vkK N t)
              ≤ (4 : ℝ) ^ (vkK N t) * (N - 1) ^ (vkK N t) := by
            rw [mul_pow] at hDpow
            exact hDpow
          have hb : (0 : ℝ) < (4 : ℝ) ^ (vkK N t) * (N - 1) ^ (vkK N t) := by
            have h1 : (0 : ℝ) < N - 1 := by linarith
            positivity
          have hd : (0 : ℝ) < ((⌊N⌋₊ : ℝ) + (M : ℝ) + 1 + u) ^ (vkK N t) := by positivity
          exact le_trans (div_le_div_of_mul_le hb hd (mul_le_mul_of_nonneg_left hDpow2 hnum_pos)) hlow
        · have hgoal : (4 : ℝ) ^ (vkK N t) * (vkMu N t / (4 : ℝ) ^ (vkK N t))
              = (t / (2 * Real.pi)) * ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ) / (N - 1) ^ (vkK N t) := by
            rw [hAlam]; rfl
          rw [hgoal]
          refine le_trans hup ?_
          have hN1 : N - 1 ≤ (⌊N⌋₊ : ℝ) + u := by
            have h2 : N < (⌊N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one N
            linarith
          have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ N - 1) hN1 (vkK N t)
          have hd1 : (0 : ℝ) < ((⌊N⌋₊ : ℝ) + u) ^ (vkK N t) := by
            have : (0 : ℝ) < (⌊N⌋₊ : ℝ) + u := by
              have := Nat.cast_nonneg (α := ℝ) ⌊N⌋₊
              linarith
            exact pow_pos this _
          have hd2 : (0 : ℝ) < (N - 1) ^ (vkK N t) := pow_pos (by linarith) _
          exact div_le_div_of_mul_le hd1 hd2 (mul_le_mul_of_nonneg_left hp hnum_pos)
      -- ## the M-value hypothesis
      have hMhyp : ∀ x : ℝ, 0 ≤ x → x ≤ vkH N t →
          (∫ α in (Set.pi Set.univ (fun _ : Fin (vkK N t - 1) => Set.Icc (0 : ℝ) 1)),
            ‖∑ h ∈ Finset.Icc 1 ⌊x⌋₊,
              Complex.exp (((2 * Real.pi * (∑ j : Fin (vkK N t - 1), α j * (h : ℝ) ^ ((j : ℕ) + 1)) : ℝ) : ℂ) *
                Complex.I)‖ ^ (2 * ((vkS N t : ℕ) : ℝ))) ≤
            Real.exp (Cmv * (((vkK N t - 1 : ℕ) : ℝ)) ^ 2 * ((vkR N t : ℕ) : ℝ) ^ 2 *
                (1 + Real.log ((((vkK N t - 1 : ℕ) : ℝ)) * ((vkR N t : ℕ) : ℝ))))
              * (vkH N t) ^ (2 * ((vkS N t : ℕ) : ℝ)
                  - (((vkK N t - 1 : ℕ) : ℝ)) * ((vkK N t : ℕ) : ℝ) / 2 + vkEta N t) := by
        intro x hx0 hxH
        have hbase := hMval N t hN hNt x hx0 hxH
        have hset : (∫ α in unitBox (vkK N t - 1),
              ‖polySum (vkK N t - 1) α x‖ ^ (2 * ((vkS N t : ℕ) : ℝ)))
            = ∫ α in (Set.pi Set.univ (fun _ : Fin (vkK N t - 1) => Set.Icc (0 : ℝ) 1)),
                ‖∑ h ∈ Finset.Icc 1 ⌊x⌋₊,
                  Complex.exp (((2 * Real.pi * (∑ j : Fin (vkK N t - 1), α j * (h : ℝ) ^ ((j : ℕ) + 1)) : ℝ) : ℂ) *
                    Complex.I)‖ ^ (2 * ((vkS N t : ℕ) : ℝ)) := by
          simp only [unitBox]
          refine setIntegral_congr_fun (MeasurableSet.pi (Set.Finite.countable Set.finite_univ)
            (fun _ _ => measurableSet_Icc)) ?_
          intro α _
          have hone : polySum (vkK N t - 1) α x
              = ∑ h ∈ Finset.Icc 1 ⌊x⌋₊,
                  Complex.exp (((2 * Real.pi * (∑ j : Fin (vkK N t - 1), α j * (h : ℝ) ^ ((j : ℕ) + 1)) : ℝ) : ℂ) *
                    Complex.I) := by
            unfold polySum phase
            refine Finset.sum_congr rfl fun h _ => ?_
            rw [eC_exp_eq']
          simp only [hone]
        rw [← hset]
        exact hbase
      -- ## apply V1a
      set Mv : ℝ := Real.exp (Cmv * (((vkK N t - 1 : ℕ) : ℝ)) ^ 2 * ((vkR N t : ℕ) : ℝ) ^ 2 *
                (1 + Real.log ((((vkK N t - 1 : ℕ) : ℝ)) * ((vkR N t : ℕ) : ℝ))))
              * (vkH N t) ^ (2 * ((vkS N t : ℕ) : ℝ)
                  - (((vkK N t - 1 : ℕ) : ℝ)) * ((vkK N t : ℕ) : ℝ) / 2 + vkEta N t) with hMvdef
      have hV1ares := hV1a (vkK N t) hk2 M (blkPh ⌊N⌋₊ t u) (vkMu N t / (4 : ℝ) ^ (vkK N t))
        ((4 : ℝ) ^ (vkK N t)) (vkH N t) Mv (vkS N t) hM1 hlam_pos hA1 hAlam_le hHpos hHdef hs1
        hcd hderiv hMhyp
      have hsum_eq : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))))
          = ∑ i ∈ Finset.Icc 1 M, Complex.exp ((↑(2 * Real.pi * blkPh ⌊N⌋₊ t u (i : ℝ)) : ℂ) * Complex.I) := by
        rw [hMdef, sum_Ioc_eq_sum_Icc_sub]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have hLe : ⌊N⌋₊ ≤ ⌊N⌋₊ + i := Nat.le_add_right _ _
        have h := cpow_eq_blkPh ⌊N⌋₊ (⌊N⌋₊ + i) t u hu hLe (by omega)
        rwa [Nat.add_sub_cancel_left] at h
      -- ## the counting bound
      have hNset : (((Nset (vkK N t) M (blkPh ⌊N⌋₊ t u) (vkH N t)).ncard : ℕ) : ℝ)
          ≤ Kcnt * ((4 : ℝ) ^ (vkK N t)) ^ 2 * ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ) * (M : ℝ)
              * (1 + vkMu N t * (M : ℝ)) * (1 + vkH N t) := by
        have h := hcnt (vkK N t) M (blkPh ⌊N⌋₊ t u) (vkH N t) (vkMu N t / (4 : ℝ) ^ (vkK N t))
          ((4 : ℝ) ^ (vkK N t)) hk3 hM1 hlam_pos hA1 hAlam_le hH1 hHdef hcont hdiff hderiv
        simpa only [hAlam] using h
      have hcount := vke_count_bookkeeping hN hNt hKcnt (vkMu_pos N t hN hNt) hmuM_le hM2N hH1 hHle hNset
      have hΘle := vke_theta_final (N := N) (t := t) (Cv1a := Cv1a) (Cmv := Cmv) (Kcnt := Kcnt)
        hN hNt hKcnt hlogerr hδ0
      -- ## the M-value bound
      have hMvbd : vkH N t ^ (-(2 * ((vkS N t : ℕ) : ℝ)) + ((vkK N t : ℕ) : ℝ) * (((vkK N t : ℕ) : ℝ) - 1) / 2) * Mv
          ≤ Real.exp (Cmv * (((vkK N t - 1 : ℕ) : ℝ)) ^ 2 * ((vkR N t : ℕ) : ℝ) ^ 2 *
                (1 + Real.log ((((vkK N t - 1 : ℕ) : ℝ)) * ((vkR N t : ℕ) : ℝ))))
            * (7 * N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ))) ^ vkEta N t := by
        rw [hMvdef]
        have hab : (-(2 * ((vkS N t : ℕ) : ℝ)) + ((vkK N t : ℕ) : ℝ) * (((vkK N t : ℕ) : ℝ) - 1) / 2)
            + (2 * ((vkS N t : ℕ) : ℝ) - (((vkK N t - 1 : ℕ) : ℝ)) * ((vkK N t : ℕ) : ℝ) / 2 + vkEta N t)
            = vkEta N t := by
          have hcast : (((vkK N t - 1 : ℕ) : ℝ)) = ((vkK N t : ℕ) : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ vkK N t)]; norm_num
          rw [hcast]; ring
        calc (vkH N t ^ (-(2 * ((vkS N t : ℕ) : ℝ)) + ((vkK N t : ℕ) : ℝ) * (((vkK N t : ℕ) : ℝ) - 1) / 2))
              * (Real.exp (Cmv * (((vkK N t - 1 : ℕ) : ℝ)) ^ 2 * ((vkR N t : ℕ) : ℝ) ^ 2 *
                    (1 + Real.log ((((vkK N t - 1 : ℕ) : ℝ)) * ((vkR N t : ℕ) : ℝ))))
                * vkH N t ^ (2 * ((vkS N t : ℕ) : ℝ) - (((vkK N t - 1 : ℕ) : ℝ)) * ((vkK N t : ℕ) : ℝ) / 2 + vkEta N t))
            = Real.exp (Cmv * (((vkK N t - 1 : ℕ) : ℝ)) ^ 2 * ((vkR N t : ℕ) : ℝ) ^ 2 *
                    (1 + Real.log ((((vkK N t - 1 : ℕ) : ℝ)) * ((vkR N t : ℕ) : ℝ))))
                * (vkH N t ^ (-(2 * ((vkS N t : ℕ) : ℝ)) + ((vkK N t : ℕ) : ℝ) * (((vkK N t : ℕ) : ℝ) - 1) / 2)
                  * vkH N t ^ (2 * ((vkS N t : ℕ) : ℝ) - (((vkK N t - 1 : ℕ) : ℝ)) * ((vkK N t : ℕ) : ℝ) / 2 + vkEta N t)) := by ring
          _ = Real.exp (Cmv * (((vkK N t - 1 : ℕ) : ℝ)) ^ 2 * ((vkR N t : ℕ) : ℝ) ^ 2 *
                    (1 + Real.log ((((vkK N t - 1 : ℕ) : ℝ)) * ((vkR N t : ℕ) : ℝ))))
                * vkH N t ^ vkEta N t := by rw [← Real.rpow_add hHpos, hab]
          _ ≤ Real.exp (Cmv * (((vkK N t - 1 : ℕ) : ℝ)) ^ 2 * ((vkR N t : ℕ) : ℝ) ^ 2 *
                    (1 + Real.log ((((vkK N t - 1 : ℕ) : ℝ)) * ((vkR N t : ℕ) : ℝ))))
                * (7 * N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ))) ^ vkEta N t :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow hHpos.le hHle (vkEta_nonneg hN hNt))
                (Real.exp_pos _).le
      have hMvnn : 0 ≤ Mv := by rw [hMvdef]; positivity
      -- ## assemble
      have hbound : ‖∑ i ∈ Finset.Icc 1 M, Complex.exp ((↑(2 * Real.pi * blkPh ⌊N⌋₊ t u (i : ℝ)) : ℂ) * Complex.I)‖
          ≤ max 5 (6 * Real.exp (U + 2)) * N ^ (1 - (1 / 100000) * (Real.log N / Real.log t) ^ 2
              / Real.log (Real.log t / Real.log N + 2)) := by
        rw [← hδeq N t]
        exact le_trans hV1ares (vke_final_bound hN hNt (le_max_left _ _) hKcnt hH1 hHle hC0k3
          h2delta hδk hM2N hcount hΘle hMvbd hMvnn)
      rw [hsum_eq]
      exact hbound

end

end Work.BMF
