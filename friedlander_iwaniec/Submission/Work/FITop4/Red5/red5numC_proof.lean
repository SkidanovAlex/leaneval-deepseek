import Mathlib
import Submission.Work.FITop4.Red5.Red5NumC
import Submission.Work.FITop4.Red5.red5num_proof

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Work.FITop4.Red5

open Finset
open Filter
open scoped BigOperators
open scoped Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## An `η`-free threshold

`red5num_threshold` in `red5num_proof` needed the `η`-dependent bound
`Aprime Asave * log log x ≤ (η/3) log x` only for the `htau` field, which `Red5NumC` drops.
Everything `Red5NumC` needs is therefore eventually true with an `η`-independent threshold. -/

lemma red5numC_threshold :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      64 ≤ x ∧ 4 ≤ Real.log (x : ℝ) ∧ 8 ≤ Real.log (x : ℝ) ∧
      Asave + Aprime Asave ≤ Real.log (Real.log (x : ℝ)) ∧
      8 * Aprime Asave * Real.log (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) := by
  have hx64 : ∀ᶠ x : ℕ in atTop, 64 ≤ x :=
    Filter.eventually_atTop.2 ⟨64, fun b hb => hb⟩
  have hL4 : ∀ᶠ x : ℕ in atTop, (4 : ℝ) ≤ Real.log (x : ℝ) :=
    Numeric4.ev_const_le_log 4 (by norm_num)
  have hL8 : ∀ᶠ x : ℕ in atTop, (8 : ℝ) ≤ Real.log (x : ℝ) :=
    Numeric4.ev_const_le_log 8 (by norm_num)
  have hLL : ∀ᶠ x : ℕ in atTop,
      Asave + Aprime Asave ≤ Real.log (Real.log (x : ℝ)) :=
    Numeric4.ev_const_le_loglog _ Asave_Aprime_sum_nonneg
  have hD1 : ∀ᶠ x : ℕ in atTop,
      8 * Aprime Asave * Real.log (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) := by
    have hthr : ∀ᶠ x : ℕ in atTop,
        256 * (Aprime Asave) ^ 2 ≤ Real.log (x : ℝ) :=
      Numeric4.ev_const_le_log (256 * (Aprime Asave) ^ 2)
        (mul_nonneg (by norm_num) Aprime_Asave_sq_nonneg)
    filter_upwards [hthr] with x hx
    have hLnn : 0 ≤ Real.log (x : ℝ) := by
      have : 0 ≤ 256 * (Aprime Asave) ^ 2 :=
        mul_nonneg (by norm_num) Aprime_Asave_sq_nonneg
      linarith
    have hs : 0 ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_nonneg _
    have hlog := Real.log_le_rpow_div hLnn (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.rpow_div_two_eq_sqrt _ hLnn, Real.rpow_one,
        show Real.sqrt (Real.log (x : ℝ)) / (1 / 2) = 2 * Real.sqrt (Real.log (x : ℝ)) by
          ring] at hlog
    have hsqrt_ge : 16 * Aprime Asave ≤ Real.sqrt (Real.log (x : ℝ)) := by
      rw [← Real.sqrt_sq (mul_nonneg (by norm_num) Aprime_Asave_nonneg)]
      apply Real.sqrt_le_sqrt
      have h2 : (16 * Aprime Asave) ^ 2 = 256 * (Aprime Asave) ^ 2 := by ring
      rw [h2]; exact hx
    have h1 : 8 * Aprime Asave * Real.log (Real.log (x : ℝ))
        ≤ 8 * Aprime Asave * (2 * Real.sqrt (Real.log (x : ℝ))) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (by norm_num) Aprime_Asave_nonneg)
    have h3 : (16 : ℝ) * Aprime Asave * Real.sqrt (Real.log (x : ℝ))
        ≤ Real.sqrt (Real.log (x : ℝ)) * Real.sqrt (Real.log (x : ℝ)) :=
      mul_le_mul_of_nonneg_right hsqrt_ge hs
    have h4 : Real.sqrt (Real.log (x : ℝ)) * Real.sqrt (Real.log (x : ℝ))
        = Real.log (x : ℝ) := by
      rw [← pow_two]; exact Real.sq_sqrt hLnn
    nlinarith [h1, h3, h4]
  have hall := hx64.and (hL4.and (hL8.and (hLL.and hD1)))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hall
  exact ⟨x₀, hx₀⟩

theorem red5numC_proof :
    ∃ x₀ : ℕ, ∀ (x N Pz : ℕ) (η : ℝ),
      x₀ ≤ x → 1 ≤ N → 2 ≤ Pz → 0 < η → η < 3 / 32 →
      (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) →
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ) →
      (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(Work.FITop4.BmaxBig η)) →
      (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ) →
      Work.FITop4.Red5.Red5NumC x N Pz η := by
  obtain ⟨x₀, hthr⟩ := red5numC_threshold
  refine ⟨x₀, ?_⟩
  intro x N Pz η hx hN1 hPz2 hη0 hη1 _hll hNlo hNhi hPzin
  obtain ⟨hx64, hL4, hL8, hLL, hD1⟩ := hthr x hx
  have hxp : 0 < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hxnn : 0 ≤ (x : ℝ) := le_of_lt hxp
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hLnn : 0 ≤ Real.log (x : ℝ) := le_of_lt hLpos
  have hL1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNnn : 0 ≤ (N : ℝ) := le_of_lt hNpos
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hPzpos : 0 < (Pz : ℝ) := by exact_mod_cast (by omega : 0 < Pz)
  have hllnn : 0 ≤ Real.log (Real.log (x : ℝ)) := le_trans Asave_Aprime_sum_nonneg hLL
  have hBpos : 0 < BmaxBig η := BmaxBig_pos η
  have hBge : Asave ≤ BmaxBig η := Asave_le_BmaxBig η
  have hA1 : (1 : ℝ) ≤ Asave := Asave_ge_one
  have hLb : (Real.log (x : ℝ)) ^ (-(BmaxBig η)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith [hBpos])
  have hNle : (N : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)) :=
    le_of_lt hNhi
  have hNvx : (N : ℝ) ≤ varthetaOf x Asave * (x : ℝ) := by
    unfold varthetaOf
    calc (N : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)) := hNle
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-Asave) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [hBge]))
            (le_of_lt (Real.rpow_pos_of_pos hxp _))
      _ ≤ (x : ℝ) * (Real.log (x : ℝ)) ^ (-Asave) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.rpow_pos_of_pos hLpos _))
          calc (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
            _ = (x : ℝ) := Real.rpow_one _
      _ = (Real.log (x : ℝ)) ^ (-Asave) * (x : ℝ) := by ring
  have hNlt8 : (N : ℝ) < (x : ℝ) / 8 := by
    have hxs : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) / 8 := by
      rw [Real.rpow_div_two_eq_sqrt 1 hxnn, Real.rpow_one]
      have hge : (8 : ℝ) ≤ Real.sqrt (x : ℝ) := by
        rw [show (8 : ℝ) = Real.sqrt 64 by
              rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hx64)
      have hsq : Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) = (x : ℝ) := by
        rw [← pow_two]; exact Real.sq_sqrt hxnn
      have hA : (8 : ℝ) * Real.sqrt (x : ℝ) ≤ Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
        mul_le_mul_of_nonneg_right hge (Real.sqrt_nonneg _)
      rw [hsq] at hA
      linarith [hA]
    calc (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)) := hNhi
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left hLb (by positivity)
      _ = (x : ℝ) ^ ((1 : ℝ) / 2) := mul_one _
      _ ≤ (x : ℝ) / 8 := hxs
  have hvx_le : varthetaOf x Asave * (x : ℝ) ≤ (x : ℝ) / 4 := by
    have hle : (Real.log (x : ℝ)) ^ (-Asave) ≤ (1 : ℝ) / 4 := by
      have h1 : (Real.log (x : ℝ)) ^ (-Asave) ≤ (Real.log (x : ℝ)) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [Asave_ge_one])
      have h1' : (Real.log (x : ℝ)) ^ (-(1 : ℝ)) = (Real.log (x : ℝ))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hLpos), Real.rpow_one]
      rw [h1'] at h1
      have h3 : (Real.log (x : ℝ))⁻¹ ≤ (4 : ℝ)⁻¹ :=
        (inv_le_inv₀ hLpos (by norm_num)).mpr hL4
      have h4 : ((4 : ℝ)⁻¹) = (1 : ℝ) / 4 := by norm_num
      linarith [h1, h3, h4]
    unfold varthetaOf
    calc (Real.log (x : ℝ)) ^ (-Asave) * (x : ℝ) ≤ ((1 : ℝ) / 4) * (x : ℝ) :=
          mul_le_mul_of_nonneg_right hle hxnn
      _ = (x : ℝ) / 4 := by ring
  have hvxN_low : (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (BmaxBig η - Asave)
      ≤ varthetaOf x Asave * (x : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ hNpos]
    unfold varthetaOf
    calc (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (BmaxBig η - Asave) * (N : ℝ)
        ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (BmaxBig η - Asave)
            * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η))) :=
          mul_le_mul_of_nonneg_left hNle (by positivity)
      _ = (Real.log (x : ℝ)) ^ (-Asave) * (x : ℝ) := by
          rw [show (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (BmaxBig η - Asave)
                * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)))
              = (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2)
                * ((Real.log (x : ℝ)) ^ (BmaxBig η - Asave)
                  * (Real.log (x : ℝ)) ^ (-(BmaxBig η))) by ring]
          rw [← Real.rpow_add hxp, ← Real.rpow_add hLpos,
              show (1 : ℝ) / 2 + 1 / 2 = (1 : ℝ) by norm_num, Real.rpow_one,
              show BmaxBig η - Asave + -(BmaxBig η) = -Asave by ring]
          ring
  have h2Nle : 2 * (N : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (BmaxBig η - Asave) := by
    have h2 : 2 * (N : ℝ) < 2 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η))) :=
      mul_lt_mul_of_pos_left hNhi (by norm_num)
    have h3 : 2 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)))
        ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (BmaxBig η - Asave) := by
      rw [show 2 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)))
          = (x : ℝ) ^ ((1 : ℝ) / 2) * (2 * (Real.log (x : ℝ)) ^ (-(BmaxBig η))) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hLB : (2 : ℝ) ≤ (Real.log (x : ℝ)) ^ (2 * BmaxBig η - Asave) := by
        have h1 : (1 : ℝ) ≤ 2 * BmaxBig η - Asave := by linarith
        calc (2 : ℝ) ≤ Real.log (x : ℝ) := by linarith
          _ = (Real.log (x : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (Real.log (x : ℝ)) ^ (2 * BmaxBig η - Asave) :=
              Real.rpow_le_rpow_of_exponent_le hL1 h1
      have hne : (Real.log (x : ℝ)) ^ (2 * BmaxBig η - Asave)
            * (Real.log (x : ℝ)) ^ (-(BmaxBig η))
          = (Real.log (x : ℝ)) ^ (BmaxBig η - Asave) := by
        rw [← Real.rpow_add hLpos]; congr 1; ring
      calc 2 * (Real.log (x : ℝ)) ^ (-(BmaxBig η))
          ≤ (Real.log (x : ℝ)) ^ (2 * BmaxBig η - Asave)
              * (Real.log (x : ℝ)) ^ (-(BmaxBig η)) :=
            mul_le_mul_of_nonneg_right hLB (le_of_lt (Real.rpow_pos_of_pos hLpos _))
        _ = (Real.log (x : ℝ)) ^ (BmaxBig η - Asave) := hne
    linarith
  have hM0def : (M0N x N : ℝ) = (YsN x N : ℝ) + 2 := by
    unfold M0N; push_cast; ring
  have hYs_le : ((YsN x N : ℕ) : ℝ) ≤ varthetaOf x Asave * (x : ℝ) / (N : ℝ) := by
    apply Nat.floor_le
    exact div_nonneg (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hLpos _)) hxnn) hNnn
  have hvxdiv : (varthetaOf x Asave * (x : ℝ) / (N : ℝ)) * (N : ℝ)
      = varthetaOf x Asave * (x : ℝ) := by field_simp
  have hvxnn : 0 ≤ varthetaOf x Asave * (x : ℝ) :=
    mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hLpos _)) hxnn
  have hx4 : 4 ≤ x := by omega
  have hlog1 : 1 ≤ Real.log (x : ℝ) := hL1
  have hlog4 : 4 ≤ Real.log (x : ℝ) := hL4
  have hv0 : 0 < varthetaOf x Asave := by unfold varthetaOf; exact Real.rpow_pos_of_pos hLpos _
  have hv14 : varthetaOf x Asave ≤ 1 / 4 := by
    have hle : (Real.log (x : ℝ)) ^ (-Asave) ≤ (1 : ℝ) / 4 := by
      have h1 : (Real.log (x : ℝ)) ^ (-Asave) ≤ (Real.log (x : ℝ)) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [Asave_ge_one])
      have h1' : (Real.log (x : ℝ)) ^ (-(1 : ℝ)) = (Real.log (x : ℝ))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hLpos), Real.rpow_one]
      rw [h1'] at h1
      have h3 : (Real.log (x : ℝ))⁻¹ ≤ (4 : ℝ)⁻¹ :=
        (inv_le_inv₀ hLpos (by norm_num)).mpr hL4
      have h4 : ((4 : ℝ)⁻¹) = (1 : ℝ) / 4 := by norm_num
      linarith [h1, h3, h4]
    unfold varthetaOf; exact hle
  have hv8 : 8 * varthetaOf x Asave ≤ 1 := by
    have hle : (Real.log (x : ℝ)) ^ (-Asave) ≤ (1 : ℝ) / 8 := by
      have h1 : (Real.log (x : ℝ)) ^ (-Asave) ≤ (Real.log (x : ℝ)) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [Asave_ge_one])
      have h1' : (Real.log (x : ℝ)) ^ (-(1 : ℝ)) = (Real.log (x : ℝ))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hLpos), Real.rpow_one]
      rw [h1'] at h1
      have h3 : (Real.log (x : ℝ))⁻¹ ≤ (8 : ℝ)⁻¹ :=
        (inv_le_inv₀ hLpos (by norm_num)).mpr hL8
      have h4 : ((8 : ℝ)⁻¹) = (1 : ℝ) / 8 := by norm_num
      linarith [h1, h3, h4]
    unfold varthetaOf
    calc 8 * (Real.log (x : ℝ)) ^ (-Asave) ≤ 8 * ((1 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
      _ = 1 := by norm_num
  have hvx1 : 1 ≤ varthetaOf x Asave * (x : ℝ) := by
    have hAlleq : Real.log (Real.log (x : ℝ)) * Asave ≤ Real.log (x : ℝ) := by
      have h1 : Real.log (Real.log (x : ℝ)) * Asave
          ≤ Real.log (Real.log (x : ℝ)) * (8 * Aprime Asave) :=
        mul_le_mul_of_nonneg_left Asave_le_eight_Aprime hllnn
      nlinarith [h1, hD1]
    have hLrpow : (Real.log (x : ℝ)) ^ (Asave) ≤ (x : ℝ) := by
      calc (Real.log (x : ℝ)) ^ (Asave) = Real.exp (Real.log (Real.log (x : ℝ)) * Asave) :=
            Real.rpow_def_of_pos hLpos _
        _ ≤ Real.exp (Real.log (x : ℝ)) := Real.exp_le_exp.mpr hAlleq
        _ = (x : ℝ) := Real.exp_log hxp
    unfold varthetaOf
    rw [Real.rpow_neg (le_of_lt hLpos)]
    have hLpow_pos : 0 < (Real.log (x : ℝ)) ^ (Asave) := Real.rpow_pos_of_pos hLpos _
    rw [show ((Real.log (x : ℝ)) ^ (Asave))⁻¹ * (x : ℝ)
          = (x : ℝ) / (Real.log (x : ℝ)) ^ (Asave) by
        rw [div_eq_mul_inv, mul_comm]]
    exact (le_div_iff₀ hLpow_pos).mpr (by simpa using hLrpow)
  have ht0 : 0 < thetaOf x Asave := by unfold thetaOf; exact Real.rpow_pos_of_pos hLpos _
  have ht14 : thetaOf x Asave ≤ 1 / 4 := by
    have hle : (Real.log (x : ℝ)) ^ (-(Aprime Asave)) ≤ (1 : ℝ) / 4 := by
      have h1 : (Real.log (x : ℝ)) ^ (-(Aprime Asave)) ≤ (Real.log (x : ℝ)) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [Aprime_Asave_ge_one])
      have h1' : (Real.log (x : ℝ)) ^ (-(1 : ℝ)) = (Real.log (x : ℝ))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hLpos), Real.rpow_one]
      rw [h1'] at h1
      have h3 : (Real.log (x : ℝ))⁻¹ ≤ (4 : ℝ)⁻¹ :=
        (inv_le_inv₀ hLpos (by norm_num)).mpr hL4
      have h4 : ((4 : ℝ)⁻¹) = (1 : ℝ) / 4 := by norm_num
      linarith [h1, h3, h4]
    unfold thetaOf; exact hle
  have hM0ge4 : 4 ≤ M0N x N := by
    have hxsqrt2 : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_div_two_eq_sqrt 1 hxnn, Real.rpow_one]
      rw [show (2 : ℝ) = Real.sqrt 4 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 4 ≤ x))
    have hLpow_ge1 : (1 : ℝ) ≤ (Real.log (x : ℝ)) ^ (BmaxBig η - Asave) :=
      Real.one_le_rpow hL1 (by linarith)
    have h2le : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (BmaxBig η - Asave) := by
      have h := mul_le_mul hxsqrt2 hLpow_ge1 (by positivity) (by positivity)
      simpa using h
    have h2vxN : (2 : ℝ) ≤ varthetaOf x Asave * (x : ℝ) / (N : ℝ) := le_trans h2le hvxN_low
    have hfloor : 2 ≤ YsN x N := Nat.le_floor h2vxN
    show 4 ≤ M0N x N
    unfold M0N
    omega
  have hM0ge2N : 2 * (N : ℝ) ≤ (M0N x N : ℝ) := by
    have h2Nat : ((2 * N : ℕ) : ℝ) ≤ varthetaOf x Asave * (x : ℝ) / (N : ℝ) := by
      push_cast
      exact le_trans h2Nle hvxN_low
    have hfloor : 2 * N ≤ YsN x N := Nat.le_floor h2Nat
    rw [hM0def]
    have hc : ((2 * N : ℕ) : ℝ) ≤ (YsN x N : ℝ) := by exact_mod_cast hfloor
    push_cast at hc
    linarith
  have hM0le3 : (M0N x N : ℝ) * (N : ℝ) ≤ 3 * varthetaOf x Asave * (x : ℝ) := by
    rw [hM0def]
    nlinarith [hYs_le, hNvx, hvxdiv, hNnn, hvxnn]
  have hM0hing : varthetaOf x Asave * (x : ℝ) < (M0N x N : ℝ) * (N : ℝ) :=
    vartheta_mul_lt_M0N_mul x N (by omega : 0 < N)
  have hθsqrtN : 1 ≤ thetaOf x Asave * (N : ℝ) ^ ((1 : ℝ) / 2) := by
    have hx18_ge : (Real.log (x : ℝ)) ^ (Aprime Asave) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [Real.rpow_def_of_pos hLpos, Real.rpow_def_of_pos hxp]
      apply Real.exp_le_exp.mpr
      linarith [hD1]
    have hNhalf_ge : (x : ℝ) ^ ((1 : ℝ) / 8) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
      have hle : (x : ℝ) ^ ((1 : ℝ) / 4 + η) ≤ (N : ℝ) := le_of_lt hNlo
      have hmono : ((x : ℝ) ^ ((1 : ℝ) / 4 + η)) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hxnn _) hle (by norm_num)
      have heq : ((x : ℝ) ^ ((1 : ℝ) / 4 + η)) ^ ((1 : ℝ) / 2) = (x : ℝ) ^ ((1 : ℝ) / 8 + η / 2) := by
        rw [← Real.rpow_mul hxnn]; ring_nf
      rw [heq] at hmono
      calc (x : ℝ) ^ ((1 : ℝ) / 8) ≤ (x : ℝ) ^ ((1 : ℝ) / 8 + η / 2) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
        _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := hmono
    unfold thetaOf
    have hLp : 0 < (Real.log (x : ℝ)) ^ (-(Aprime Asave)) := Real.rpow_pos_of_pos hLpos _
    calc (1 : ℝ) = (Real.log (x : ℝ)) ^ (-(Aprime Asave)) * (Real.log (x : ℝ)) ^ (Aprime Asave) := by
          rw [← Real.rpow_add hLpos, show -(Aprime Asave) + Aprime Asave = 0 by ring, Real.rpow_zero]
      _ ≤ (Real.log (x : ℝ)) ^ (-(Aprime Asave)) * (N : ℝ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left (le_trans hx18_ge hNhalf_ge) (le_of_lt hLp)
  have hNs : (N : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    calc (N : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)) := hNle
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left hLb (by positivity)
      _ = (x : ℝ) ^ ((1 : ℝ) / 2) := mul_one _
  have hN2x : (N : ℝ) ^ 2 ≤ (x : ℝ) := by
    have hmm := mul_self_le_mul_self hNnn hNs
    rw [pow_two]
    calc (N : ℝ) * (N : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) := hmm
      _ = (x : ℝ) := by
          rw [Real.rpow_div_two_eq_sqrt 1 hxnn, Real.rpow_one, ← pow_two]
          exact Real.sq_sqrt hxnn
  have h2Nx : 2 * (N : ℝ) ≤ (x : ℝ) := by
    have h2s : 2 * (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) := by
      rw [Real.rpow_div_two_eq_sqrt 1 hxnn, Real.rpow_one]
      have hge : (2 : ℝ) ≤ Real.sqrt (x : ℝ) := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 4 ≤ x))
      have hsq : Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) = (x : ℝ) := by
        rw [← pow_two]; exact Real.sq_sqrt hxnn
      nlinarith [hge, Real.sqrt_nonneg (x : ℝ), hsq]
    linarith
  have htop : (MtopN x N : ℝ) * (2 * (N : ℝ)) ≤ (x : ℝ) := by
    calc (MtopN x N : ℝ) * (2 * (N : ℝ)) = (((MtopN x N) * (2 * N) : ℕ) : ℝ) := by
          push_cast; ring
      _ ≤ (x : ℝ) := by
          apply Nat.cast_le.mpr
          show MtopN x N * (2 * N) ≤ x
          exact Nat.div_mul_le_self x (2 * N)
  have h2Nsq : (2 * (N : ℝ)) ^ 2 ≤ (x : ℝ) := by
    have hNsq : (N : ℝ) ^ 2 ≤ (x : ℝ) * (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η)) := by
      have hmm : (N : ℝ) * (N : ℝ)
          ≤ ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)))
            * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η))) :=
        mul_self_le_mul_self hNnn hNle
      rw [pow_two]
      calc (N : ℝ) * (N : ℝ) ≤ _ := hmm
        _ = (x : ℝ) * (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η)) := by
            rw [show (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η))
                  * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η)))
                = (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2)
                  * ((Real.log (x : ℝ)) ^ (-(BmaxBig η))
                    * (Real.log (x : ℝ)) ^ (-(BmaxBig η))) by ring]
            rw [← Real.rpow_add hxp, ← Real.rpow_add hLpos,
                show (1 : ℝ) / 2 + 1 / 2 = (1 : ℝ) by norm_num, Real.rpow_one,
                show -(BmaxBig η) + -(BmaxBig η) = -(2 * BmaxBig η) by ring]
    have hL2B : (4 : ℝ) ≤ (Real.log (x : ℝ)) ^ (2 * BmaxBig η) := by
      have h2B : (1 : ℝ) ≤ 2 * BmaxBig η := by linarith
      calc (4 : ℝ) ≤ Real.log (x : ℝ) := by linarith
        _ = (Real.log (x : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (Real.log (x : ℝ)) ^ (2 * BmaxBig η) :=
            Real.rpow_le_rpow_of_exponent_le hL1 h2B
    have hposL : 0 < (Real.log (x : ℝ)) ^ (2 * BmaxBig η) := Real.rpow_pos_of_pos hLpos _
    have hinv : ((Real.log (x : ℝ)) ^ (2 * BmaxBig η))⁻¹ ≤ (4 : ℝ)⁻¹ :=
      (inv_le_inv₀ hposL (by norm_num)).mpr hL2B
    have hmul : 4 * (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η)) ≤ 1 := by
      rw [Real.rpow_neg (le_of_lt hLpos)]
      have := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    have h2 : 4 * ((x : ℝ) * (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η))) ≤ (x : ℝ) := by
      calc 4 * ((x : ℝ) * (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η)))
          = (x : ℝ) * (4 * (Real.log (x : ℝ)) ^ (-(2 * BmaxBig η))) := by ring
        _ ≤ (x : ℝ) * 1 := mul_le_mul_of_nonneg_left hmul hxnn
        _ = (x : ℝ) := mul_one _
    have h1 : (2 * (N : ℝ)) ^ 2 = 4 * (N : ℝ) ^ 2 := by ring
    rw [h1]; linarith [hNsq, h2]
  have h4N2nat : (2 * N : ℕ) * (2 * N : ℕ) ≤ x := by
    have : ((2 * N : ℕ) : ℝ) * ((2 * N : ℕ) : ℝ) ≤ (x : ℝ) := by
      push_cast
      calc (2 * (N : ℝ)) * (2 * (N : ℝ)) = (2 * (N : ℝ)) ^ 2 := by rw [pow_two]
        _ ≤ (x : ℝ) := h2Nsq
    exact_mod_cast this
  have hMtopge2Nnat : (2 * N : ℕ) ≤ MtopN x N :=
    (Nat.le_div_iff_mul_le (by omega : 0 < 2 * N)).mpr h4N2nat
  have hMtopge2N : 2 * (N : ℝ) ≤ (MtopN x N : ℝ) := by exact_mod_cast hMtopge2Nnat
  have hMtoping : varthetaOf x Asave * (x : ℝ) < (MtopN x N : ℝ) * (N : ℝ) := by
    have hMtop_low : (x : ℝ) / (2 * (N : ℝ)) - 1 < (MtopN x N : ℝ) := by
      have h2Npos : 0 < 2 * N := by omega
      have hq : (x : ℝ) / (2 * (N : ℝ)) < ((x / (2 * N) : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ))]
        have h := (Nat.div_lt_iff_lt_mul h2Npos).mp (Nat.lt_succ_self (x / (2 * N)))
        exact_mod_cast h
      have hMtop_eq : (MtopN x N : ℝ) = ((x / (2 * N) : ℕ) : ℝ) := rfl
      linarith [hq, hMtop_eq]
    have h3 : ((x : ℝ) / (2 * (N : ℝ)) - 1) * (N : ℝ) = (x : ℝ) / 2 - (N : ℝ) := by field_simp
    have h2 := mul_lt_mul_of_pos_right hMtop_low hNpos
    rw [h3] at h2
    linarith [h2, hvx_le, hNlt8]
  have hMtop1 : 1 ≤ MtopN x N := by omega
  have hM0leMtop : M0N x N ≤ MtopN x N := by
    have h2Npos : 0 < 2 * N := by omega
    apply (Nat.le_div_iff_mul_le h2Npos).mpr
    have hmul : (M0N x N : ℝ) * (2 * (N : ℝ)) < (x : ℝ) := by
      rw [hM0def]
      nlinarith [hYs_le, hvxdiv, hvx_le, hNlt8, hNnn, hxnn]
    have hnat : M0N x N * (2 * N) ≤ x := by
      have : ((M0N x N * (2 * N) : ℕ) : ℝ) < (x : ℝ) := by
        push_cast; exact hmul
      exact_mod_cast le_of_lt this
    exact hnat
  have hJJpos : 1 ≤ JJN x N := by
    rcases Nat.eq_zero_or_pos (JJN x N) with h0 | hpos
    · exfalso
      have hlt := MtopN_lt_two_pow_JJN x N
      rw [h0, pow_zero, one_mul] at hlt
      omega
    · exact hpos
  have hpowJJN : (2 : ℝ) ^ (JJN x N) * (M0N x N : ℝ) ≤ (x : ℝ) / (N : ℝ) := by
    have hpred := two_pow_pred_JJN_mul_le_MtopN hJJpos
    have hpredR : (2 : ℝ) ^ (JJN x N - 1) * (M0N x N : ℝ) ≤ (MtopN x N : ℝ) := by
      have : (((2 ^ (JJN x N - 1)) * M0N x N : ℕ) : ℝ) ≤ (MtopN x N : ℝ) := by
        exact_mod_cast hpred
      push_cast at this
      linarith [this]
    have hsplit : (2 : ℝ) ^ (JJN x N) * (M0N x N : ℝ)
        = 2 * ((2 : ℝ) ^ (JJN x N - 1) * (M0N x N : ℝ)) := by
      have h1 : (2 : ℝ) ^ (JJN x N) = (2 : ℝ) ^ ((JJN x N - 1) + 1) := by
        congr 1; omega
      rw [h1, pow_succ]
      ring
    rw [hsplit]
    have h2Mtop : 2 * (MtopN x N : ℝ) ≤ (x : ℝ) / (N : ℝ) := by
      rw [le_div_iff₀ hNpos]
      have hR : (MtopN x N : ℝ) * (2 * (N : ℝ)) ≤ (x : ℝ) := htop
      nlinarith [hR]
    linarith [hpredR, h2Mtop]
  have hMtoplepow : (MtopN x N : ℝ) ≤ (2 : ℝ) ^ (JJN x N) * (M0N x N : ℝ) := by
    have hlt := MtopN_lt_two_pow_JJN x N
    have : (MtopN x N : ℝ) ≤ ((2 ^ (JJN x N) * M0N x N : ℕ) : ℝ) := by
      exact_mod_cast le_of_lt hlt
    push_cast at this
    linarith [this]
  have hcop : (N : ℝ) ≤ varthetaOf x Asave * thetaOf x Asave * (x : ℝ) ^ ((1 : ℝ) / 2) := by
    have hvt : varthetaOf x Asave * thetaOf x Asave = (Real.log (x : ℝ)) ^ (-(Asave + Aprime Asave)) := by
      unfold varthetaOf thetaOf
      rw [← Real.rpow_add hLpos]; congr 1; ring
    have hle : (Real.log (x : ℝ)) ^ (-(BmaxBig η)) ≤ (Real.log (x : ℝ)) ^ (-(Asave + Aprime Asave)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [Asave_add_Aprime_le_BmaxBig η])
    have hNle' : (N : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(Asave + Aprime Asave)) :=
      le_trans hNle (mul_le_mul_of_nonneg_left hle (by positivity))
    have heq : (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(Asave + Aprime Asave))
        = varthetaOf x Asave * thetaOf x Asave * (x : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [hvt, mul_comm]
    exact le_trans hNle' (le_of_eq heq)
  have hPz : (Pz : ℝ)⁻¹ ≤ varthetaOf x Asave * thetaOf x Asave * (Real.log (x : ℝ)) ^ (100 : ℕ) := by
    have hPzge : Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2) ≤ (Pz : ℝ) := by
      have h := Real.exp_le_exp.mpr hPzin
      rwa [Real.exp_log hPzpos] at h
    have h1 : (Pz : ℝ)⁻¹ ≤ Real.exp (-(Real.log (Real.log (x : ℝ))) ^ 2) := by
      rw [Real.exp_neg]
      exact (inv_le_inv₀ hPzpos (Real.exp_pos _)).mpr hPzge
    have hineq : -(Real.log (Real.log (x : ℝ))) ^ 2
        ≤ (100 - Asave - Aprime Asave) * Real.log (Real.log (x : ℝ)) := by
      have h2 : (Asave + Aprime Asave - 100) * Real.log (Real.log (x : ℝ))
          ≤ Real.log (Real.log (x : ℝ)) ^ 2 := by
        nlinarith [hLL, hllnn]
      linarith [h2]
    have h2 : (Pz : ℝ)⁻¹ ≤ Real.exp ((100 - Asave - Aprime Asave) * Real.log (Real.log (x : ℝ))) :=
      le_trans h1 (Real.exp_le_exp.mpr hineq)
    have h3 : varthetaOf x Asave * thetaOf x Asave * (Real.log (x : ℝ)) ^ (100 : ℕ)
        = Real.exp ((100 - Asave - Aprime Asave) * Real.log (Real.log (x : ℝ))) := by
      unfold varthetaOf thetaOf
      rw [← Real.rpow_natCast (Real.log (x : ℝ)) 100,
          ← Real.rpow_add hLpos, ← Real.rpow_add hLpos,
          Real.rpow_def_of_pos hLpos]
      congr 1
      ring
    exact le_trans h2 (le_of_eq h3.symm)
  exact ⟨hx4, hlog1, hlog4, hv0, hv14, hv8, hvx1, ht0, ht14, hM0ge4, hM0ge2N,
    hM0le3, hM0hing, hθsqrtN, hN2x, h2Nx, htop, hMtopge2N, hMtoping, hMtop1,
    hM0leMtop, hpowJJN, hMtoplepow, hcop, hPz⟩

end

end Work.FITop4.Red5
