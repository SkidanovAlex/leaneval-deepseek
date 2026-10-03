import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FIArea6Road.DivisorWindowDefs
import Submission.Work.FIArea6Road.tau_sq_le_d4
import Submission.Work.FIArea6Road.D2_window_le
import Submission.Work.FIArea6Road.d4_window_decomp

set_option maxHeartbeats 1600000

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

private lemma cast_div_le_succ (n z : ℕ) : (n:ℝ)/(z:ℝ) ≤ ((n/z:ℕ):ℝ) + 1 := by
  rcases Nat.eq_zero_or_pos z with hz | hz
  · subst hz; simp
  have hzR : (0:ℝ) < (z:ℝ) := by exact_mod_cast hz
  have h := Nat.div_add_mod n z
  have hcast : (n:ℝ) = (z:ℝ)*((n/z:ℕ):ℝ) + ((n%z:ℕ):ℝ) := by
    have hh := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at hh
    linarith [hh]
  have hmod : ((n%z:ℕ):ℝ) < (z:ℝ) := by exact_mod_cast Nat.mod_lt n hz
  have hsplit : (n:ℝ)/(z:ℝ) = ((n/z:ℕ):ℝ) + ((n%z:ℕ):ℝ)/(z:ℝ) := by
    rw [hcast]; field_simp
  have hlt : ((n%z:ℕ):ℝ)/(z:ℝ) < 1 := by
    rw [div_lt_one hzR]; exact hmod
  linarith [hsplit, hlt]

private lemma div_sub_div_le (a b z : ℕ) :
    ((a/z:ℕ):ℝ) - ((b/z:ℕ):ℝ) ≤ ((a:ℝ)-(b:ℝ))/(z:ℝ) + 1 := by
  have h1 : ((a/z:ℕ):ℝ) ≤ (a:ℝ)/(z:ℝ) := Nat.cast_div_le
  have h2 : (b:ℝ)/(z:ℝ) ≤ ((b/z:ℕ):ℝ) + 1 := cast_div_le_succ b z
  have h3 : ((a:ℝ)-(b:ℝ))/(z:ℝ) = (a:ℝ)/(z:ℝ) - (b:ℝ)/(z:ℝ) := by ring
  linarith [h1, h2, h3]

private lemma Vbound {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) {C₂ : ℝ} (hC₂pos : 0 < C₂)
    (hC₂ : ∀ p q : ℕ, p ≤ q →
      D2 q - D2 p ≤ C₂ * (((q:ℝ)-(p:ℝ))+1) * Real.log ((q:ℝ)+2) + C₂ * Real.sqrt (q:ℝ))
    {z : ℕ} (hz : 1 ≤ z) :
    D2 (M/z) - D2 ((N-1)/z)
      ≤ C₂ * (((M:ℝ)-(N:ℝ)+1)/(z:ℝ)+2) * Real.log ((M:ℝ)+2) + C₂ * Real.sqrt ((M:ℝ)/(z:ℝ)) := by
  have hle : (N-1)/z ≤ M/z := Nat.div_le_div_right (by omega)
  have h := hC₂ ((N-1)/z) (M/z) hle
  have hNcast : (((N-1:ℕ)):ℝ) = (N:ℝ) - 1 := by
    rw [Nat.cast_sub hN]; norm_num
  have hcoef : (((M/z:ℕ):ℝ)-(((N-1)/z:ℕ):ℝ))+1 ≤ ((M:ℝ)-(N:ℝ)+1)/(z:ℝ)+2 := by
    have h3 := div_sub_div_le M (N-1) z
    rw [hNcast] at h3
    have h4 : ((M:ℝ)-((N:ℝ)-1))/(z:ℝ) = ((M:ℝ)-(N:ℝ)+1)/(z:ℝ) := by ring
    rw [h4] at h3
    linarith
  have hlog : Real.log (((M/z:ℕ):ℝ)+2) ≤ Real.log ((M:ℝ)+2) := by
    apply Real.log_le_log (by positivity)
    have : ((M/z:ℕ):ℝ) ≤ (M:ℝ) := by exact_mod_cast Nat.div_le_self M z
    linarith
  have hsqrt : Real.sqrt (((M/z:ℕ)):ℝ) ≤ Real.sqrt ((M:ℝ)/(z:ℝ)) :=
    Real.sqrt_le_sqrt (Nat.cast_div_le)
  have hA' : (0:ℝ) ≤ ((M:ℝ)-(N:ℝ)+1)/(z:ℝ)+2 := by
    have : (0:ℝ) ≤ (M:ℝ)-(N:ℝ) := by
      have : (N:ℝ) ≤ (M:ℝ) := by exact_mod_cast hNM
      linarith
    positivity
  have hlogq : (0:ℝ) ≤ Real.log (((M/z:ℕ):ℝ)+2) := by
    apply Real.log_nonneg
    have : (0:ℝ) ≤ ((M/z:ℕ):ℝ) := Nat.cast_nonneg _
    linarith
  calc D2 (M/z) - D2 ((N-1)/z)
      ≤ C₂ * ((((M/z:ℕ):ℝ)-(((N-1)/z:ℕ):ℝ))+1) * Real.log (((M/z:ℕ):ℝ)+2)
          + C₂ * Real.sqrt (((M/z:ℕ)):ℝ) := h
    _ ≤ C₂ * (((M:ℝ)-(N:ℝ)+1)/(z:ℝ)+2) * Real.log ((M:ℝ)+2) + C₂ * Real.sqrt ((M:ℝ)/(z:ℝ)) := by
        apply add_le_add
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hcoef (le_of_lt hC₂pos)) hlog hlogq
            (mul_nonneg (le_of_lt hC₂pos) hA')
        · exact mul_le_mul_of_nonneg_left hsqrt (le_of_lt hC₂pos)

/-- Elementary arithmetic core used for both halves of the decomposition. -/
private lemma arith_gen {aa LL lg s1 s0 s2 pp qq mm B1 B0 B2 KK : ℝ}
  (ha : 0 < aa) (hL : 0 ≤ LL) (hlg : 1 ≤ lg) (hp : 0 ≤ pp) (hm : 0 ≤ mm)
  (hB0 : 0 ≤ B0) (hB2 : 0 ≤ B2)
  (hs1 : s1 ≤ B1*lg^2) (hs0 : s0 ≤ B0*pp*lg) (hs2 : s2 ≤ B2*qq*lg^2)
  (hpm : pp ≤ mm) (hpmq : pp*qq ≤ mm)
  (hK1 : aa*B1 ≤ KK) (hK2 : 2*aa*B0 + aa*B2 ≤ KK) :
  aa*lg*(LL*s1+2*s0)+aa*(pp*s2) ≤ KK*(LL*lg^3+mm*lg^2) := by
  have hlg0 : 0 ≤ lg := le_trans (by norm_num) hlg
  have ha0 : 0 ≤ aa := le_of_lt ha
  have hLLlg3 : 0 ≤ LL*lg^3 := by positivity
  have hmmg2 : 0 ≤ mm*lg^2 := by positivity
  have h1 : aa*lg*LL*s1 ≤ aa*B1*(LL*lg^3) := by
    have h := mul_le_mul_of_nonneg_left hs1 (by positivity : (0:ℝ) ≤ aa*lg*LL)
    calc aa*lg*LL*s1 ≤ aa*lg*LL*(B1*lg^2) := h
      _ = aa*B1*(LL*lg^3) := by ring
  have h1' : aa*B1*(LL*lg^3) ≤ KK*(LL*lg^3) := mul_le_mul_of_nonneg_right hK1 hLLlg3
  have h2 : 2*(aa*lg)*s0 ≤ 2*aa*B0*(mm*lg^2) := by
    have hfac : (0:ℝ) ≤ 2*(aa*lg) := by nlinarith [ha0, hlg0]
    have h := mul_le_mul_of_nonneg_left hs0 hfac
    calc 2*(aa*lg)*s0 ≤ 2*(aa*lg)*(B0*pp*lg) := h
      _ = 2*aa*B0*(pp*lg^2) := by ring
      _ ≤ 2*aa*B0*(mm*lg^2) := by
          have hfac2 : (0:ℝ) ≤ 2*aa*B0 := by nlinarith [ha0, hB0]
          apply mul_le_mul_of_nonneg_left _ hfac2
          nlinarith [hp, hpm, hlg0, sq_nonneg lg]
  have h3 : aa*(pp*s2) ≤ aa*B2*(mm*lg^2) := by
    rw [← mul_assoc]
    have h := mul_le_mul_of_nonneg_left hs2 (by positivity : (0:ℝ) ≤ aa*pp)
    calc aa*pp*s2 ≤ aa*pp*(B2*qq*lg^2) := h
      _ = aa*B2*((pp*qq)*lg^2) := by ring
      _ ≤ aa*B2*(mm*lg^2) := by
          have hfac2 : (0:ℝ) ≤ aa*B2 := by nlinarith [ha0, hB2]
          apply mul_le_mul_of_nonneg_left _ hfac2
          exact mul_le_mul_of_nonneg_right hpmq (by positivity)
  have haux : aa*lg*(LL*s1+2*s0) = aa*lg*LL*s1 + 2*(aa*lg)*s0 := by ring
  have hkey : 2*aa*B0*(mm*lg^2) + aa*B2*(mm*lg^2) ≤ KK*(mm*lg^2) := by
    have : (2*aa*B0 + aa*B2)*(mm*lg^2) ≤ KK*(mm*lg^2) := mul_le_mul_of_nonneg_right hK2 hmmg2
    linarith [this]
  rw [haux]
  nlinarith [h1, h1', h2, h3, hkey, hLLlg3, hmmg2]

open scoped Real

theorem sum_tau_sq_window_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N M : ℕ, N ≤ M →
      ∑ n ∈ Finset.Icc N M, ((n.divisors.card : ℝ)) ^ 2
        ≤ C * ((M : ℝ) - (N : ℝ) + 1) * (Real.log ((M : ℝ) + 2)) ^ (3 : ℕ)
          + C * (M : ℝ) ^ ((3 : ℝ) / 4) * (Real.log ((M : ℝ) + 2)) ^ (2 : ℕ) := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := D2_window_le
  obtain ⟨Cd, hCdpos, hCd0⟩ := Work.FIArea2.sum_tau_pow_div_le 1
  obtain ⟨Cs, hCspos, hCs0⟩ := Commons.NumberTheory.DivisorSum.sum_tau_pow_le 1
  obtain ⟨Cr, hCrpos, hCr0⟩ := Work.FIArea3.sum_tau_pow_div_sqrt_le 1
  have hKcpos : (0:ℝ) < 20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300 := by positivity
  refine ⟨2*(20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300), by positivity, ?_⟩
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hmain : ∀ N M : ℕ, 1 ≤ N → N ≤ M →
      ∑ n ∈ Finset.Icc N M, ((n.divisors.card : ℝ)) ^ 2
        ≤ (2*(20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300)) * ((M : ℝ) - (N : ℝ) + 1)
            * (Real.log ((M : ℝ) + 2)) ^ (3 : ℕ)
          + (2*(20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300)) * (M : ℝ) ^ ((3 : ℝ) / 4)
            * (Real.log ((M : ℝ) + 2)) ^ (2 : ℕ) := by
    intro N M hN hNM
    by_cases hMle : M ≤ 3
    · -- small M
      have hcard3 : ∀ n ∈ Finset.Icc N M, ((n.divisors.card : ℝ))^2 ≤ 9 := by
        intro n hn
        have hn3 : n ≤ 3 := le_trans (Finset.mem_Icc.mp hn).2 hMle
        have hsub : n.divisors ⊆ Finset.Icc 1 3 := by
          intro d hd
          rw [Nat.mem_divisors] at hd
          exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd.1 (by omega),
            le_trans (Nat.le_of_dvd (by omega) hd.1) hn3⟩
        have hc : n.divisors.card ≤ 3 := by
          have h := Finset.card_le_card hsub
          simpa using h
        have : ((n.divisors.card : ℝ)) ≤ 3 := by exact_mod_cast hc
        have h0 : (0:ℝ) ≤ (n.divisors.card : ℝ) := by positivity
        nlinarith [this, h0]
      have hsum : (∑ n ∈ Finset.Icc N M, ((n.divisors.card : ℝ))^2) ≤ 9 * ((M:ℝ) - (N:ℝ) + 1) := by
        calc (∑ n ∈ Finset.Icc N M, ((n.divisors.card : ℝ))^2)
            ≤ ∑ _n ∈ Finset.Icc N M, (9:ℝ) := Finset.sum_le_sum hcard3
          _ = 9 * ((Finset.Icc N M).card : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ = 9 * ((M:ℝ) - (N:ℝ) + 1) := by
                rw [Nat.card_Icc]
                have hle : N ≤ M + 1 := by omega
                rw [Nat.cast_sub hle]; push_cast; ring
      have hLpos : (0:ℝ) < (M:ℝ) - (N:ℝ) + 1 := by
        have : (N:ℝ) ≤ (M:ℝ) := by exact_mod_cast hNM
        linarith
      have hlg1 : (1:ℝ) ≤ Real.log ((M:ℝ)+2) := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        have h1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast (le_trans hN hNM)
        linarith [Real.exp_one_lt_three]
      have hlog3 : (1:ℝ) ≤ (Real.log ((M:ℝ)+2))^(3:ℕ) := one_le_pow₀ hlg1
      have hKbig : (9:ℝ) ≤ (2*(20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300)) * (Real.log ((M:ℝ)+2))^(3:ℕ) := by
        have h6 : (0:ℝ) < 2*(20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300) := by positivity
        have := mul_le_mul_of_nonneg_left hlog3 h6.le
        nlinarith [this, h6]
      have hnonneg2 : (0:ℝ) ≤ (2*(20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300)) * (M:ℝ)^((3:ℝ)/4) * (Real.log ((M:ℝ)+2))^(2:ℕ) := by
        apply mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
        positivity
      nlinarith [hsum, hLpos, hKbig, hnonneg2, mul_le_mul_of_nonneg_right hKbig hLpos.le]
    · -- large M
      have hM4 : 4 ≤ M := by omega
      set U : ℕ := M.sqrt with hU
      set V : ℕ := M/U with hV
      have hUpos : 0 < U := by rw [hU, Nat.sqrt_pos]; omega
      have hUge2 : 2 ≤ U := by
        rw [hU]; exact (Nat.le_sqrt (m := 2) (n := M)).mpr (by omega)
      have hU2 : U*U ≤ M := by rw [hU]; simpa [pow_two] using Nat.sqrt_le' M
      have hUlt : M < (U+1)*(U+1) := by
        have h := Nat.lt_succ_sqrt M
        rw [← hU] at h
        simpa [Nat.succ_eq_add_one] using h
      have hUleM : U ≤ M := by rw [hU]; exact Nat.sqrt_le_self M
      have hMposR : (0:ℝ) < (M:ℝ) := by positivity
      have hMge1R : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
      have hUle : (U:ℝ) ≤ Real.sqrt (M:ℝ) := by
        have h2 : (U:ℝ)*(U:ℝ) ≤ (M:ℝ) := by exact_mod_cast hU2
        calc (U:ℝ) = Real.sqrt ((U:ℝ)*(U:ℝ)) :=
              (Real.sqrt_mul_self (by positivity : (0:ℝ) ≤ (U:ℝ))).symm
          _ ≤ Real.sqrt (M:ℝ) := Real.sqrt_le_sqrt h2
      -- log facts
      have hlg1 : (1:ℝ) ≤ Real.log ((M:ℝ)+2) := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        linarith [Real.exp_one_lt_three, hMge1R]
      have hlg0 : (0:ℝ) ≤ Real.log ((M:ℝ)+2) := le_trans zero_le_one hlg1
      have hlgU : Real.log ((U:ℝ)+2) ≤ Real.log ((M:ℝ)+2) := by
        apply Real.log_le_log (by positivity)
        have : (U:ℝ) ≤ (M:ℝ) := by exact_mod_cast hUleM
        linarith
      have hlgU9 : Real.log ((U:ℝ)+2) + 2 ≤ 3 * Real.log ((M:ℝ)+2) := by nlinarith [hlgU, hlg1]
      -- rpow facts
      have hM34def : (M:ℝ)^((3:ℝ)/4) = (M:ℝ)^((1:ℝ)/2) * (M:ℝ)^((1:ℝ)/4) := by
        rw [← Real.rpow_add (by positivity)]; norm_num
      have hM34nn : (0:ℝ) ≤ (M:ℝ)^((3:ℝ)/4) := Real.rpow_nonneg (by positivity) _
      have hsqrt_le34 : Real.sqrt (M:ℝ) ≤ (M:ℝ)^((3:ℝ)/4) := by
        rw [Real.sqrt_eq_rpow, hM34def]
        have h1 : (1:ℝ) ≤ (M:ℝ)^((1:ℝ)/4) := Real.one_le_rpow hMge1R (by norm_num)
        nlinarith [h1, Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (M:ℝ)) ((1:ℝ)/2)]
      have hssqrt_eq : Real.sqrt (Real.sqrt (M:ℝ)) = (M:ℝ)^((1:ℝ)/4) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]; norm_num
      have hUsqrt_le14 : Real.sqrt (U:ℝ) ≤ (M:ℝ)^((1:ℝ)/4) :=
        calc Real.sqrt (U:ℝ) ≤ Real.sqrt (Real.sqrt (M:ℝ)) := Real.sqrt_le_sqrt hUle
          _ = (M:ℝ)^((1:ℝ)/4) := hssqrt_eq
      have hprod34 : Real.sqrt (M:ℝ)*Real.sqrt (U:ℝ) ≤ (M:ℝ)^((3:ℝ)/4) := by
        have h2 : Real.sqrt (M:ℝ)*Real.sqrt (U:ℝ)
            ≤ (M:ℝ)^((1:ℝ)/2)*(M:ℝ)^((1:ℝ)/4) := by
          rw [Real.sqrt_eq_rpow]
          exact mul_le_mul_of_nonneg_left hUsqrt_le14 (Real.rpow_nonneg (by positivity) _)
        rwa [← hM34def] at h2
      have hsqrtMnn : (0:ℝ) ≤ Real.sqrt (M:ℝ) := Real.sqrt_nonneg _
      have hUsqrtnn : (0:ℝ) ≤ Real.sqrt (U:ℝ) := Real.sqrt_nonneg _
      -- sum bounds for the `e`-sum
      have hSe : (∑ e ∈ Finset.Icc 1 U, tauR e / (e:ℝ)) ≤ 9*Cd * (Real.log ((M:ℝ)+2))^2 := by
        have hh : (∑ e ∈ Finset.Icc 1 U, tauR e / (e:ℝ)) ≤ Cd * (Real.log (U:ℝ) + 2)^2 := by
          simpa only [pow_one, tauR] using hCd0 U
        have hlogUM : Real.log (U:ℝ) ≤ Real.log ((M:ℝ)+2) :=
          le_trans (Real.log_le_log (by positivity) (by exact_mod_cast hUleM : (U:ℝ) ≤ (M:ℝ)))
            (Real.log_le_log (by positivity) (by linarith))
        have h9 : (Real.log (U:ℝ) + 2)^2 ≤ (3*Real.log ((M:ℝ)+2))^2 := by
          apply pow_le_pow_left₀ (by positivity)
          nlinarith [hlogUM, hlg1]
        calc (∑ e ∈ Finset.Icc 1 U, tauR e / (e:ℝ))
            ≤ Cd * (Real.log (U:ℝ) + 2)^2 := hh
          _ ≤ Cd * (3*Real.log ((M:ℝ)+2))^2 := mul_le_mul_of_nonneg_left h9 hCdpos.le
          _ = 9*Cd * (Real.log ((M:ℝ)+2))^2 := by ring
      have hS1 : (∑ e ∈ Finset.Icc 1 U, tauR e) ≤ Cs * Real.sqrt (M:ℝ) * Real.log ((M:ℝ)+2) := by
        have hh : (∑ e ∈ Finset.Icc 1 U, tauR e) ≤ Cs * (U:ℝ) * Real.log ((U:ℝ)+1) := by
          simpa only [pow_one, Nat.reduceSub, tauR] using hCs0 U (by omega)
        have hlgl : Real.log ((U:ℝ)+1) ≤ Real.log ((M:ℝ)+2) := by
          apply Real.log_le_log (by positivity)
          have : (U:ℝ) ≤ (M:ℝ) := by exact_mod_cast hUleM
          linarith
        have hlogU : (0:ℝ) ≤ Real.log ((U:ℝ)+1) := Real.log_nonneg (by have h : (0:ℝ) ≤ (U:ℝ) := Nat.cast_nonneg _; linarith)
        calc (∑ e ∈ Finset.Icc 1 U, tauR e)
            ≤ Cs * (U:ℝ) * Real.log ((U:ℝ)+1) := hh
          _ ≤ Cs * Real.sqrt (M:ℝ) * Real.log ((M:ℝ)+2) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hUle hCspos.le) hlgl hlogU (by positivity)
      have hSr : (∑ e ∈ Finset.Icc 1 U, tauR e / Real.sqrt (e:ℝ)) ≤ 9*Cr * Real.sqrt (U:ℝ) * (Real.log ((M:ℝ)+2))^2 := by
        have hh : (∑ e ∈ Finset.Icc 1 U, tauR e / Real.sqrt (e:ℝ))
            ≤ Cr * Real.sqrt (U:ℝ) * (Real.log (U:ℝ) + 2)^2 := by
          simpa only [pow_one, tauR] using hCr0 U
        have hlogUM : Real.log (U:ℝ) ≤ Real.log ((M:ℝ)+2) :=
          le_trans (Real.log_le_log (by positivity) (by exact_mod_cast hUleM : (U:ℝ) ≤ (M:ℝ)))
            (Real.log_le_log (by positivity) (by linarith))
        have h9 : (Real.log (U:ℝ) + 2)^2 ≤ (3*Real.log ((M:ℝ)+2))^2 := by
          apply pow_le_pow_left₀ (by positivity)
          nlinarith [hlogUM, hlg1]
        calc (∑ e ∈ Finset.Icc 1 U, tauR e / Real.sqrt (e:ℝ))
            ≤ Cr * Real.sqrt (U:ℝ) * (Real.log (U:ℝ) + 2)^2 := hh
          _ ≤ Cr * Real.sqrt (U:ℝ) * (3*Real.log ((M:ℝ)+2))^2 :=
              mul_le_mul_of_nonneg_left h9 (by positivity)
          _ = 9*Cr * Real.sqrt (U:ℝ) * (Real.log ((M:ℝ)+2))^2 := by ring
      have hAA : (∑ e ∈ Finset.Icc 1 U, tauR e*(((M:ℝ)-(N:ℝ)+1)/(e:ℝ)+2))
          = ((M:ℝ)-(N:ℝ)+1)*(∑ e ∈ Finset.Icc 1 U, tauR e/(e:ℝ)) + 2*(∑ e ∈ Finset.Icc 1 U, tauR e) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro e he; ring
      have hBB : (∑ e ∈ Finset.Icc 1 U, tauR e*Real.sqrt ((M:ℝ)/(e:ℝ)))
          = Real.sqrt (M:ℝ) * (∑ e ∈ Finset.Icc 1 U, tauR e/Real.sqrt ((e:ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e he
        rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ (M:ℝ)) (e:ℝ)]
        ring
      have hterm1 : (∑ e ∈ Finset.Icc 1 U, tauR e * (D2 (M/e) - D2 ((N-1)/e)))
          ≤ (20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300) *
              (((M:ℝ)-(N:ℝ)+1) * (Real.log ((M:ℝ)+2))^3
                + (M:ℝ)^((3:ℝ)/4) * (Real.log ((M:ℝ)+2))^2) := by
        have hpt : ∀ e ∈ Finset.Icc 1 U, tauR e*(D2 (M/e) - D2 ((N-1)/e))
            ≤ tauR e*(C₂*(((M:ℝ)-(N:ℝ)+1)/(e:ℝ)+2)*Real.log ((M:ℝ)+2)
                + C₂*Real.sqrt ((M:ℝ)/(e:ℝ))) := by
          intro e he
          refine mul_le_mul_of_nonneg_left ?_ (tauR_nonneg e)
          exact Vbound hN hNM hC₂pos hC₂ (Finset.mem_Icc.mp he).1
        have hsum := Finset.sum_le_sum hpt
        have hexp : (∑ e ∈ Finset.Icc 1 U,
              tauR e*(C₂*(((M:ℝ)-(N:ℝ)+1)/(e:ℝ)+2)*Real.log ((M:ℝ)+2) + C₂*Real.sqrt ((M:ℝ)/(e:ℝ))))
            = C₂*Real.log ((M:ℝ)+2) * (∑ e ∈ Finset.Icc 1 U, tauR e*(((M:ℝ)-(N:ℝ)+1)/(e:ℝ)+2))
              + C₂*(∑ e ∈ Finset.Icc 1 U, tauR e*Real.sqrt ((M:ℝ)/(e:ℝ))) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro e he; ring
        rw [hexp, hAA, hBB] at hsum
        apply le_trans hsum
        have hLrnn : (0:ℝ) ≤ (M:ℝ)-(N:ℝ)+1 := by
          have hNM' : (N:ℝ) ≤ (M:ℝ) := by exact_mod_cast hNM
          linarith
        have hK1 : C₂*(9*Cd) ≤ 20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300 := by
          have h1 : (0:ℝ) ≤ 20*C₂*Cd := by positivity
          have h2 : (0:ℝ) ≤ 20*C₂*Cs := by positivity
          have h3 : (0:ℝ) ≤ 30*C₂*Cr := by positivity
          linarith
        have hK2 : 2*C₂*Cs + C₂*(9*Cr) ≤ 20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300 := by
          have h1 : (0:ℝ) ≤ 20*C₂*Cd := by positivity
          have h2 : (0:ℝ) ≤ 18*C₂*Cs := by positivity
          have h3 : (0:ℝ) ≤ 21*C₂*Cr := by positivity
          linarith
        exact arith_gen hC₂pos hLrnn hlg1 hsqrtMnn hM34nn hCspos.le (by positivity)
          hSe hS1 hSr hsqrt_le34 hprod34 hK1 hK2
      -- term 2
      have hVle4U : V ≤ 4*U := by
        rw [hV]
        have h1 : (U+1)*(U+1) ≤ 4*U*U := by nlinarith [hUge2]
        have hMsq : M < 4*U*U := lt_of_lt_of_le hUlt h1
        have h2 : M/U ≤ (4*U*U)/U := Nat.div_le_div_right hMsq.le
        have h3 : (4*U*U)/U = 4*U := by rw [mul_comm (4*U) U, Nat.mul_div_right (4*U) hUpos]
        rwa [h3] at h2
      have hVle4sqrtM : (V:ℝ) ≤ 4*Real.sqrt (M:ℝ) := by
        calc (V:ℝ) ≤ (4*U:ℝ) := by exact_mod_cast hVle4U
          _ = 4*(U:ℝ) := by ring
          _ ≤ 4*Real.sqrt (M:ℝ) := by linarith [hUle]
      have hVleM : V ≤ M := by rw [hV]; exact Nat.div_le_self M U
      have hV1 : 1 ≤ V := by rw [hV]; exact Nat.div_pos hUleM (by omega)
      have hlgV : Real.log ((V:ℝ)+2) ≤ Real.log ((M:ℝ)+2) := by
        apply Real.log_le_log (by positivity)
        have : (V:ℝ) ≤ (M:ℝ) := by exact_mod_cast hVleM
        linarith
      have hlgV9 : Real.log ((V:ℝ)+2) + 2 ≤ 3 * Real.log ((M:ℝ)+2) := by nlinarith [hlgV, hlg1]
      have hVsqrt_le : Real.sqrt (V:ℝ) ≤ 2*(M:ℝ)^((1:ℝ)/4) := by
        have h1 : Real.sqrt (V:ℝ) ≤ Real.sqrt (4*Real.sqrt (M:ℝ)) := by
          apply Real.sqrt_le_sqrt; exact hVle4sqrtM
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) (Real.sqrt (M:ℝ))] at h1
        have h2 : Real.sqrt (4:ℝ) = 2 := by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
        rw [h2] at h1
        calc Real.sqrt (V:ℝ) ≤ 2*Real.sqrt (Real.sqrt (M:ℝ)) := h1
          _ = 2*(M:ℝ)^((1:ℝ)/4) := by rw [hssqrt_eq]
      have hSe2 : (∑ f ∈ Finset.Icc 1 V, tauR f / (f:ℝ)) ≤ 9*Cd * (Real.log ((M:ℝ)+2))^2 := by
        have hh : (∑ f ∈ Finset.Icc 1 V, tauR f / (f:ℝ)) ≤ Cd * (Real.log (V:ℝ) + 2)^2 := by
          simpa only [pow_one, tauR] using hCd0 V
        have hlogVM : Real.log (V:ℝ) ≤ Real.log ((M:ℝ)+2) :=
          le_trans (Real.log_le_log (by positivity) (by exact_mod_cast hVleM : (V:ℝ) ≤ (M:ℝ)))
            (Real.log_le_log (by positivity) (by linarith))
        have h9 : (Real.log (V:ℝ) + 2)^2 ≤ (3*Real.log ((M:ℝ)+2))^2 := by
          apply pow_le_pow_left₀ (by positivity)
          nlinarith [hlogVM, hlg1]
        calc (∑ f ∈ Finset.Icc 1 V, tauR f / (f:ℝ))
            ≤ Cd * (Real.log (V:ℝ) + 2)^2 := hh
          _ ≤ Cd * (3*Real.log ((M:ℝ)+2))^2 := mul_le_mul_of_nonneg_left h9 hCdpos.le
          _ = 9*Cd * (Real.log ((M:ℝ)+2))^2 := by ring
      have hS12 : (∑ f ∈ Finset.Icc 1 V, tauR f) ≤ 4*Cs * Real.sqrt (M:ℝ) * Real.log ((M:ℝ)+2) := by
        have hh : (∑ f ∈ Finset.Icc 1 V, tauR f) ≤ Cs * (V:ℝ) * Real.log ((V:ℝ)+1) := by
          simpa only [pow_one, Nat.reduceSub, tauR] using hCs0 V hV1
        have hlgl : Real.log ((V:ℝ)+1) ≤ Real.log ((M:ℝ)+2) := by
          apply Real.log_le_log (by positivity)
          have : (V:ℝ) ≤ (M:ℝ) := by exact_mod_cast hVleM
          linarith
        have hlogV : (0:ℝ) ≤ Real.log ((V:ℝ)+1) := Real.log_nonneg (by have h : (0:ℝ) ≤ (V:ℝ) := Nat.cast_nonneg _; linarith)
        calc (∑ f ∈ Finset.Icc 1 V, tauR f)
            ≤ Cs * (V:ℝ) * Real.log ((V:ℝ)+1) := hh
          _ ≤ Cs * (4*Real.sqrt (M:ℝ)) * Real.log ((M:ℝ)+2) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hVle4sqrtM hCspos.le) hlgl hlogV (by positivity)
          _ = 4*Cs * Real.sqrt (M:ℝ) * Real.log ((M:ℝ)+2) := by ring
      have hSr2 : (∑ f ∈ Finset.Icc 1 V, tauR f / Real.sqrt (f:ℝ)) ≤ 18*Cr * (M:ℝ)^((1:ℝ)/4) * (Real.log ((M:ℝ)+2))^2 := by
        have hh : (∑ f ∈ Finset.Icc 1 V, tauR f / Real.sqrt (f:ℝ))
            ≤ Cr * Real.sqrt (V:ℝ) * (Real.log (V:ℝ) + 2)^2 := by
          simpa only [pow_one, tauR] using hCr0 V
        have hlogVM : Real.log (V:ℝ) ≤ Real.log ((M:ℝ)+2) :=
          le_trans (Real.log_le_log (by positivity) (by exact_mod_cast hVleM : (V:ℝ) ≤ (M:ℝ)))
            (Real.log_le_log (by positivity) (by linarith))
        have h9 : (Real.log (V:ℝ) + 2)^2 ≤ (3*Real.log ((M:ℝ)+2))^2 := by
          apply pow_le_pow_left₀ (by positivity)
          nlinarith [hlogVM, hlg1]
        calc (∑ f ∈ Finset.Icc 1 V, tauR f / Real.sqrt (f:ℝ))
            ≤ Cr * Real.sqrt (V:ℝ) * (Real.log (V:ℝ) + 2)^2 := hh
          _ ≤ Cr * (2*(M:ℝ)^((1:ℝ)/4)) * (3*Real.log ((M:ℝ)+2))^2 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hVsqrt_le hCrpos.le) h9 (by positivity) (by positivity)
          _ = 18*Cr * (M:ℝ)^((1:ℝ)/4) * (Real.log ((M:ℝ)+2))^2 := by ring
      have hAA2 : (∑ f ∈ Finset.Icc 1 V, tauR f*(((M:ℝ)-(N:ℝ)+1)/(f:ℝ)+2))
          = ((M:ℝ)-(N:ℝ)+1)*(∑ f ∈ Finset.Icc 1 V, tauR f/(f:ℝ)) + 2*(∑ f ∈ Finset.Icc 1 V, tauR f) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro f hf; ring
      have hBB2 : (∑ f ∈ Finset.Icc 1 V, tauR f*Real.sqrt ((M:ℝ)/(f:ℝ)))
          = Real.sqrt (M:ℝ) * (∑ f ∈ Finset.Icc 1 V, tauR f/Real.sqrt ((f:ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro f hf
        rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ (M:ℝ)) (f:ℝ)]
        ring
      have hterm2 : (∑ f ∈ Finset.Icc 1 V, tauR f * (D2 (M/f) - D2 ((N-1)/f)))
          ≤ (20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300) *
              (((M:ℝ)-(N:ℝ)+1) * (Real.log ((M:ℝ)+2))^3
                + (M:ℝ)^((3:ℝ)/4) * (Real.log ((M:ℝ)+2))^2) := by
        have hpt : ∀ f ∈ Finset.Icc 1 V, tauR f*(D2 (M/f) - D2 ((N-1)/f))
            ≤ tauR f*(C₂*(((M:ℝ)-(N:ℝ)+1)/(f:ℝ)+2)*Real.log ((M:ℝ)+2)
                + C₂*Real.sqrt ((M:ℝ)/(f:ℝ))) := by
          intro f hf
          refine mul_le_mul_of_nonneg_left ?_ (tauR_nonneg f)
          exact Vbound hN hNM hC₂pos hC₂ (Finset.mem_Icc.mp hf).1
        have hsum := Finset.sum_le_sum hpt
        have hexp : (∑ f ∈ Finset.Icc 1 V,
              tauR f*(C₂*(((M:ℝ)-(N:ℝ)+1)/(f:ℝ)+2)*Real.log ((M:ℝ)+2) + C₂*Real.sqrt ((M:ℝ)/(f:ℝ))))
            = C₂*Real.log ((M:ℝ)+2) * (∑ f ∈ Finset.Icc 1 V, tauR f*(((M:ℝ)-(N:ℝ)+1)/(f:ℝ)+2))
              + C₂*(∑ f ∈ Finset.Icc 1 V, tauR f*Real.sqrt ((M:ℝ)/(f:ℝ))) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro f hf; ring
        rw [hexp, hAA2, hBB2] at hsum
        apply le_trans hsum
        have hLrnn : (0:ℝ) ≤ (M:ℝ)-(N:ℝ)+1 := by
          have hNM' : (N:ℝ) ≤ (M:ℝ) := by exact_mod_cast hNM
          linarith
        have hK1 : C₂*(9*Cd) ≤ 20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300 := by
          have h1 : (0:ℝ) ≤ 20*C₂*Cd := by positivity
          have h2 : (0:ℝ) ≤ 20*C₂*Cs := by positivity
          have h3 : (0:ℝ) ≤ 30*C₂*Cr := by positivity
          linarith
        have hK2 : 2*C₂*(4*Cs) + C₂*(18*Cr) ≤ 20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300 := by
          have h1 : (0:ℝ) ≤ 20*C₂*Cd := by positivity
          have h2 : (0:ℝ) ≤ 12*C₂*Cs := by positivity
          have h3 : (0:ℝ) ≤ 12*C₂*Cr := by positivity
          linarith
        have hmm : (M:ℝ)^((3:ℝ)/4) = (M:ℝ)^((1:ℝ)/2) * (M:ℝ)^((1:ℝ)/4) := hM34def
        have hprod : Real.sqrt (M:ℝ) * (M:ℝ)^((1:ℝ)/4) ≤ (M:ℝ)^((3:ℝ)/4) := by
          rw [hM34def, Real.sqrt_eq_rpow]
        exact arith_gen hC₂pos hLrnn hlg1 hsqrtMnn hM34nn (by positivity) (by positivity)
          hSe2 hS12 hSr2 hsqrt_le34 hprod hK1 hK2
      have hcrux : (∑ n ∈ Finset.Icc N M, ((n.divisors.card : ℝ)) ^ 2)
          ≤ (∑ e ∈ Finset.Icc 1 U, tauR e * (D2 (M/e) - D2 ((N-1)/e)))
            + ∑ f ∈ Finset.Icc 1 V, tauR f * (D2 (M/f) - D2 ((N-1)/f)) := by
        rw [hV] at *
        refine le_trans (Finset.sum_le_sum (fun n _ => tau_sq_le_d4 n)) ?_
        exact d4_window_decomp N M U hN hNM (by omega)
      have htot : (∑ n ∈ Finset.Icc N M, ((n.divisors.card : ℝ)) ^ 2)
          ≤ (20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300) *
              (2 * (((M:ℝ)-(N:ℝ)+1) * (Real.log ((M:ℝ)+2))^3
                + (M:ℝ)^((3:ℝ)/4) * (Real.log ((M:ℝ)+2))^2)) := by
        nlinarith [hcrux, hterm1, hterm2]
      have hfin : (20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300) *
              (2 * (((M:ℝ)-(N:ℝ)+1) * (Real.log ((M:ℝ)+2))^3
                + (M:ℝ)^((3:ℝ)/4) * (Real.log ((M:ℝ)+2))^2))
          ≤ (2*(20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300)) * ((M:ℝ)-(N:ℝ)+1)
              * (Real.log ((M:ℝ)+2))^3
            + (2*(20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300)) * (M:ℝ)^((3:ℝ)/4)
              * (Real.log ((M:ℝ)+2))^2 := by ring_nf; norm_num
      linarith [htot, hfin]
  intro N M hNM
  rcases Nat.eq_zero_or_pos N with hN0 | hN1
  · subst hN0
    rcases Nat.eq_zero_or_pos M with hM0 | hM1
    · subst hM0
      have hsum0 : (∑ n ∈ Finset.Icc 0 0, ((n.divisors.card : ℝ))^2) = 0 := by
        simp [Nat.divisors_zero]
      rw [hsum0]
      simp only [Nat.cast_zero]
      have hKnn : (0:ℝ) ≤ 2*(20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300) := by positivity
      have hl3 : (0:ℝ) ≤ (Real.log ((0:ℝ)+2))^3 := by positivity
      have hl2 : (0:ℝ) ≤ (Real.log ((0:ℝ)+2))^2 := by positivity
      have hrp : (0:ℝ) ≤ (0:ℝ)^((3:ℝ)/4) := Real.rpow_nonneg (le_refl 0) _
      have hLnn : (0:ℝ) ≤ ((0:ℝ)-(0:ℝ)+1) := by norm_num
      apply add_nonneg
      · exact mul_nonneg (mul_nonneg hKnn hLnn) hl3
      · exact mul_nonneg (mul_nonneg hKnn hrp) hl2
    · have hS0 : (∑ n ∈ Finset.Icc 0 M, ((n.divisors.card : ℝ))^2)
          = ∑ n ∈ Finset.Icc 1 M, ((n.divisors.card : ℝ))^2 := by
        have hset : Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hset, Finset.sum_insert (by simp)]
        simp [Nat.divisors_zero]
      rw [hS0]
      have hb := hmain 1 M (le_refl 1) (by omega)
      refine le_trans hb ?_
      have hKnn : (0:ℝ) ≤ 2*(20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300) := by positivity
      have hl3 : (0:ℝ) ≤ (Real.log ((M:ℝ)+2))^3 := by
        have h1 : (0:ℝ) < Real.log ((M:ℝ)+2) := Real.log_pos (by linarith [show (1:ℝ) ≤ (M:ℝ) by exact_mod_cast (by omega : 1 ≤ M)])
        positivity
      have hstep : (2*(20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300)) * ((M:ℝ)-(1:ℝ)+1) * (Real.log ((M:ℝ)+2))^3
          ≤ (2*(20*C₂*Cd + 20*C₂*Cs + 30*C₂*Cr + 300)) * ((M:ℝ)-(0:ℝ)+1) * (Real.log ((M:ℝ)+2))^3 := by
        apply mul_le_mul_of_nonneg_right _ hl3
        apply mul_le_mul_of_nonneg_left _ hKnn
        linarith
      linarith [hb, hstep]
  · exact hmain N M hN1 hNM

end Work.FIArea6Road
