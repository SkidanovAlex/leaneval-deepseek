import Mathlib
import Submission.Work.BW.mahlerDefs
import Submission.Work.BW.logMoment_le
import Submission.Work.BW.logMoment_sq_ge_lin
import Submission.Work.BW.mahler_numeric
import Submission.Work.BW.sigma_pigeonhole

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

private noncomputable def sigmaF {N : ℕ} (ε θ : Fin N → ℝ) (k : ℕ) : ℝ :=
  ∑ j, Real.log ‖(1:ℂ) - (ε j : ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ j:ℂ))‖

private lemma exp_arg_eq (k : ℕ) (x : ℝ) :
    Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(x:ℂ))
      = Complex.exp (Complex.I * ((2*Real.pi*(k:ℝ)*x : ℝ) : ℂ)) := by
  congr 1
  push_cast
  ring

private lemma log_le_log_one_add {ε φ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Real.log ‖(1:ℂ) - (ε:ℂ) * Complex.exp (Complex.I * (φ:ℂ))‖ ≤ Real.log (1 + ε) := by
  have hnorm : ‖(ε:ℂ) * Complex.exp (Complex.I * (φ:ℂ))‖ = ε := by
    rw [norm_mul, Complex.norm_of_nonneg hε0]
    have hthis : Complex.exp (Complex.I * (φ:ℂ)) = Complex.exp ((φ:ℂ) * Complex.I) := by
      rw [mul_comm]
    rw [hthis, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hpos : 0 < ‖(1:ℂ) - (ε:ℂ) * Complex.exp (Complex.I * (φ:ℂ))‖ := by
    rw [norm_pos_iff]
    intro h
    have h2 : (1:ℂ) = (ε:ℂ) * Complex.exp (Complex.I * (φ:ℂ)) := sub_eq_zero.mp h
    have h3 : (1:ℝ) = ε := by
      have hc := congrArg norm h2
      rw [norm_one, hnorm] at hc
      exact hc
    linarith
  refine Real.log_le_log hpos ?_
  calc ‖(1:ℂ) - (ε:ℂ) * Complex.exp (Complex.I * (φ:ℂ))‖
      ≤ ‖(1:ℂ)‖ + ‖(ε:ℂ) * Complex.exp (Complex.I * (φ:ℂ))‖ := norm_sub_le _ _
    _ = 1 + ε := by rw [norm_one, hnorm]

private lemma sigmaF_le {N : ℕ} (ε θ : Fin N → ℝ) (k : ℕ)
    (hε0 : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j < 1) :
    sigmaF ε θ k ≤ ∑ j, Real.log (1 + ε j) := by
  rw [sigmaF]
  apply Finset.sum_le_sum
  intro j _
  rw [exp_arg_eq k (θ j)]
  exact log_le_log_one_add (le_of_lt (hε0 j)) (hε1 j)

private lemma forty_three_48_le {ε : ℝ} (h : Real.exp (-(1/A0)) ≤ ε) : (43:ℝ)/48 ≤ ε := by
  have h1 := Real.add_one_le_exp (-(1/A0))
  have h1A0 : (1:ℝ)/A0 = 5/48 := by rw [show A0 = (48:ℝ)/5 from rfl]; norm_num
  rw [h1A0] at h h1
  linarith

private lemma log_eps_add_nonneg {ε : ℝ} (hε : Real.exp (-(1/A0)) ≤ ε) (hε1 : ε < 1) :
    0 ≤ Real.log ε + Real.log (1 + ε) := by
  have h43 := forty_three_48_le hε
  have hpos : 0 < ε := by linarith
  have hprod : 1 ≤ ε * (1 + ε) := by
    have h3 : (43:ℝ)/48 * (1 + 43/48) ≤ ε * (1 + ε) := by nlinarith [h43, hpos]
    have h4 : (1:ℝ) ≤ 43/48 * (1 + 43/48) := by norm_num
    linarith
  have hlog : Real.log (ε * (1+ε)) = Real.log ε + Real.log (1+ε) :=
    Real.log_mul (ne_of_gt hpos) (by positivity)
  rw [← hlog]
  exact Real.log_nonneg hprod

private lemma half_le_log_one_add {ε : ℝ} (hε : Real.exp (-(1/A0)) ≤ ε) (hε1 : ε < 1) :
    (1:ℝ)/2 ≤ Real.log (1 + ε) := by
  have h43 := forty_three_48_le hε
  have h2 : (1:ℝ) + 43/48 ≤ 1 + ε := by linarith
  have hexp : Real.exp 1 < ((91:ℝ)/48)^2 := by
    have h := Real.exp_one_lt_d9
    have h' : (2.7182818286:ℝ) < ((91:ℝ)/48)^2 := by norm_num
    linarith
  have hsq : ((91:ℝ)/48)^2 ≤ (1 + ε)^2 := by
    have h4 : (0:ℝ) ≤ (91:ℝ)/48 := by norm_num
    have h5 : (0:ℝ) ≤ 1 + ε := by linarith [h43]
    nlinarith [h2, h4, h5]
  have hle : Real.exp 1 ≤ (1 + ε)^2 := le_of_lt (lt_of_lt_of_le hexp hsq)
  have hlog := Real.log_le_log (Real.exp_pos 1) hle
  rw [Real.log_exp, Real.log_pow] at hlog
  push_cast at hlog
  linarith

private lemma hnumEpsLocal {N : ℕ} (hN : 2 ≤ N) (ε : Fin N → ℝ)
    (hε0 : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j < 1)
    (hεlow : ∀ j, Real.exp (-(1/A0)) ≤ ε j)
    (hεhigh : ∀ j, ε j ≤ rhoP N)
    (hprod : Real.exp (-(2/A0)) ≤ ∏ j, ε j) :
    (∑ j, Real.log (1 + ε j)) * ((1/2) * ∑ j, Real.log (1/(1 - ε j)))
      + (∑ j, Real.log (ε j)) * ((1/2) * ∑ j, Real.log (1/(1 - ε j))
          - (∑ j, Real.log (1 + ε j)) * ((KK N : ℝ)/2))
      < ((KK N : ℝ) + 1)/4 * (∑ j, (ε j)^2)
          - (∑ j, ε j) * (∑ j, Real.log (1/(1 - ε j))) := by
  set Lp : ℝ := ∑ j, Real.log (1 + ε j) with hLp
  set L : ℝ := ∑ j, Real.log (1/(1 - ε j)) with hL
  set t : ℝ := ∑ j, Real.log (ε j) with ht
  set s1 : ℝ := ∑ j, ε j with hs1
  set s2 : ℝ := ∑ j, (ε j)^2 with hs2
  set x : ℝ := (N:ℝ) * Real.log (12*(N:ℝ)) with hx
  set K : ℝ := (KK N : ℝ) with hK
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hlog12pos : 0 < Real.log (12*(N:ℝ)) := Real.log_pos (by linarith)
  have hx_pos : 0 < x := by rw [hx]; exact mul_pos hNpos hlog12pos
  have hx_nn : 0 ≤ x := le_of_lt hx_pos
  have hK_nn : (0:ℝ) ≤ K := by rw [hK]; exact Nat.cast_nonneg _
  have hA0_1 : (1:ℝ)/A0 = 5/48 := by unfold A0; norm_num
  have hA0_2 : (2:ℝ)/A0 = 5/24 := by unfold A0; norm_num
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- (a) Lp ≤ N log 2
  have hLp_le : Lp ≤ (N:ℝ) * Real.log 2 := by
    rw [hLp]
    calc ∑ j, Real.log (1 + ε j) ≤ ∑ _j : Fin N, Real.log 2 := by
          apply Finset.sum_le_sum
          intro j _
          exact Real.log_le_log (by linarith [hε0 j]) (by linarith [hε1 j])
      _ = (N:ℝ) * Real.log 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hLp_nn : 0 ≤ Lp := by
    rw [hLp]
    exact Finset.sum_nonneg (fun j _ => Real.log_nonneg (by linarith [hε0 j]))
  -- (b) L ≥ 0, L ≤ x
  have hL_nn : 0 ≤ L := by
    rw [hL]
    apply Finset.sum_nonneg
    intro j _
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith [hε1 j])]
    linarith [hε0 j]
  have hL_le : L ≤ x := by
    rw [hL, hx]
    calc ∑ j, Real.log (1/(1 - ε j)) ≤ ∑ _j : Fin N, Real.log (12*(N:ℝ)) := by
          apply Finset.sum_le_sum
          intro j _
          apply Real.log_le_log
          · exact div_pos one_pos (by linarith [hε1 j])
          · rw [div_le_iff₀ (by linarith [hε1 j])]
            have h12 : (0:ℝ) < 12*(N:ℝ) := by positivity
            have hle : (1:ℝ)/(12*(N:ℝ)) ≤ 1 - ε j := by
              have hh := hεhigh j; rw [rhoP] at hh; linarith
            have h3 : (12*(N:ℝ)) * ((1:ℝ)/(12*(N:ℝ))) ≤ (12*(N:ℝ))*(1 - ε j) :=
              mul_le_mul_of_nonneg_left hle (le_of_lt h12)
            rw [mul_one_div, div_self (ne_of_gt h12)] at h3
            linarith
      _ = (N:ℝ) * Real.log (12*(N:ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- (c) s1 bounds
  have hs1_low : (N:ℝ) * Real.exp (-(1/A0)) ≤ s1 := by
    rw [hs1]
    calc (N:ℝ) * Real.exp (-(1/A0)) = ∑ _j : Fin N, Real.exp (-(1/A0)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ j, ε j := Finset.sum_le_sum (fun j _ => hεlow j)
  have hs1_high : s1 ≤ (N:ℝ) := by
    rw [hs1]
    calc ∑ j, ε j ≤ ∑ _j : Fin N, (1:ℝ) := Finset.sum_le_sum (fun j _ => le_of_lt (hε1 j))
      _ = (N:ℝ) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- (d) s2 ≥ N exp(-2/A0)
  have hs2_low : (N:ℝ) * Real.exp (-(2/A0)) ≤ s2 := by
    rw [hs2]
    have hpt : ∀ j, Real.exp (-(2/A0)) ≤ (ε j)^2 := by
      intro j
      have h1 : (Real.exp (-(1/A0)))^2 ≤ (ε j)^2 :=
        pow_le_pow_left₀ (Real.exp_pos _).le (hεlow j) 2
      have h2 : (Real.exp (-(1/A0)))^2 = Real.exp (-(2/A0)) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rwa [h2] at h1
    calc (N:ℝ) * Real.exp (-(2/A0)) = ∑ _j : Fin N, Real.exp (-(2/A0)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ j, (ε j)^2 := Finset.sum_le_sum (fun j _ => hpt j)
  -- (e) t bounds
  have ht_le : t ≤ 0 := by
    rw [ht]
    exact Finset.sum_nonpos (fun j _ => Real.log_nonpos (le_of_lt (hε0 j)) (le_of_lt (hε1 j)))
  have ht_low : -(2/A0) ≤ t := by
    rw [ht]
    have hprodlog : (∑ j, Real.log (ε j)) = Real.log (∏ j, ε j) := by
      rw [Real.log_prod (s := Finset.univ) (f := ε) (fun j _ => ne_of_gt (hε0 j))]
    rw [hprodlog]
    have := Real.log_le_log (Real.exp_pos (-(2/A0))) hprod
    rwa [Real.log_exp] at this
  -- (f) floor bounds
  have hK_le : K ≤ (54/5) * x := by
    rw [hK, hx]
    simp only [KK, B0]
    have hnn : (0:ℝ) ≤ 54/5 * ↑N * Real.log (12*↑N) :=
      mul_nonneg (mul_nonneg (by norm_num) hNpos.le) hlog12pos.le
    have hfl := Nat.floor_le hnn
    linarith
  have hK_ge : (54/5) * x ≤ K + 1 := by
    rw [hK, hx]
    simp only [KK, B0]
    have hfl := Nat.sub_one_lt_floor ((54/5) * (↑N) * Real.log (12*↑N))
    linarith
  -- bracket nonneg and upper bound
  have he_pos : (4:ℝ)/5 ≤ Real.exp (-(1/A0)) := by
    have h1 := mahler_num_exp.1
    have h2 : Real.exp (-(5/24)) ≤ Real.exp (-(1/A0)) := by
      apply Real.exp_le_exp.mpr
      rw [hA0_1]; norm_num
    linarith
  have hbr_nn : 0 ≤ s1 + (1/2)*Lp + (1/2)*t := by
    have h2e : 2 * (4/5:ℝ) ≤ (N:ℝ) * Real.exp (-(1/A0)) :=
      mul_le_mul hN2 he_pos (by norm_num) hNpos.le
    linarith [hs1_low, ht_low, h2e, hLp_nn, hA0_1, hA0_2]
  have hbr : s1 + (1/2)*Lp + (1/2)*t ≤ (N:ℝ) + (1/2)*((N:ℝ)*Real.log 2) := by
    linarith [hs1_high, hLp_le, ht_le]
  have hLL : L*(s1 + (1/2)*Lp + (1/2)*t) ≤ x*((N:ℝ) + (1/2)*((N:ℝ)*Real.log 2)) :=
    mul_le_mul hL_le hbr hbr_nn hx_nn
  -- t*Lp lower bound
  have h_tLp : -(2/A0) * ((N:ℝ)*Real.log 2) ≤ t*Lp := by
    have h1 : (-(2/A0))*Lp ≤ t*Lp := mul_le_mul_of_nonneg_right ht_low hLp_nn
    have hc : -(2/A0) ≤ 0 := by linarith [hA0_2]
    have h2 : (-(2/A0))*((N:ℝ)*Real.log 2) ≤ (-(2/A0))*Lp :=
      mul_le_mul_of_nonpos_left hLp_le hc
    linarith
  have hLk : -(1/A0) * ((N:ℝ)*Real.log 2) * K ≤ t*(Lp*(K/2)) := by
    have hK2 : (0:ℝ) ≤ K/2 := by linarith [hK_nn]
    have h1 : (-(2/A0) * ((N:ℝ)*Real.log 2)) * (K/2) ≤ (t*Lp) * (K/2) :=
      mul_le_mul_of_nonneg_right h_tLp hK2
    have h2 : (t*Lp)*(K/2) = t*(Lp*(K/2)) := by ring
    have h3 : (-(2/A0) * ((N:ℝ)*Real.log 2)) * (K/2) = -(1/A0) * ((N:ℝ)*Real.log 2) * K := by
      rw [hA0_2, hA0_1]; ring
    linarith [h1, h2, h3]
  -- (g) core numeric fact
  have hcore : 0 < (27/10)*Real.exp (-(5/24)) - (1 + (13/8)*Real.log 2) := by
    have h1 := mahler_num_exp.1
    have h2 := Real.log_two_lt_d9
    nlinarith [h1, h2]
  -- assemble
  have hexp_eq : Real.exp (-(2/A0)) = Real.exp (-(5/24)) := by
    congr 1; rw [hA0_2]
  have h1c : (27/10)*x ≤ (K+1)/4 := by linarith [hK_ge]
  have hA : (27/10)*x*((N:ℝ)*Real.exp (-(5/24))) ≤ (K+1)/4*s2 := by
    have ha : (27/10)*x*((N:ℝ)*Real.exp (-(2/A0))) ≤ (K+1)/4*((N:ℝ)*Real.exp (-(2/A0))) :=
      mul_le_mul_of_nonneg_right h1c (mul_nonneg hNpos.le (Real.exp_pos _).le)
    have hb : (K+1)/4*((N:ℝ)*Real.exp (-(2/A0))) ≤ (K+1)/4*s2 :=
      mul_le_mul_of_nonneg_left hs2_low (by linarith [hK_nn])
    have hc : (27/10)*x*((N:ℝ)*Real.exp (-(5/24))) = (27/10)*x*((N:ℝ)*Real.exp (-(2/A0))) := by
      rw [hexp_eq]
    rw [hc]; linarith
  have hC : -(9/8)*Real.log 2*((N:ℝ)*x) ≤ t*(Lp*(K/2)) := by
    have hc : -(1/A0) * ((N:ℝ)*Real.log 2) * ((54/5)*x) ≤
        -(1/A0) * ((N:ℝ)*Real.log 2) * K := by
      have hcoef : (0:ℝ) ≤ (1/A0) * ((N:ℝ)*Real.log 2) :=
        mul_nonneg (by rw [hA0_1]; norm_num) (mul_nonneg hNpos.le hlog2pos.le)
      nlinarith [hK_le, hcoef]
    have heq : -(1/A0) * ((N:ℝ)*Real.log 2) * ((54/5)*x) =
        -(9/8)*Real.log 2*((N:ℝ)*x) := by
      rw [hA0_1]; ring
    linarith [hc, hLk, heq]
  have hDlower : x*(N:ℝ)*((27/10)*Real.exp (-(5/24)) - (1 + (13/8)*Real.log 2))
      ≤ (K+1)/4*s2 - L*(s1 + (1/2)*Lp + (1/2)*t) + t*(Lp*(K/2)) := by
    have heq : x*(N:ℝ)*((27/10)*Real.exp (-(5/24)) - (1 + (13/8)*Real.log 2))
        = (27/10)*x*((N:ℝ)*Real.exp (-(5/24)))
          - x*((N:ℝ) + (1/2)*((N:ℝ)*Real.log 2))
          - (9/8)*Real.log 2*((N:ℝ)*x) := by ring
    rw [heq]
    linarith [hA, hLL, hC]
  have hpos : 0 < x*(N:ℝ)*((27/10)*Real.exp (-(5/24)) - (1 + (13/8)*Real.log 2)) :=
    mul_pos (mul_pos hx_pos hNpos) hcore
  have hDpos : 0 < (K+1)/4*s2 - L*(s1 + (1/2)*Lp + (1/2)*t) + t*(Lp*(K/2)) :=
    lt_of_lt_of_le hpos hDlower
  have hgoal : Lp * ((1/2)*L) + t*((1/2)*L - Lp*(K/2)) < (K+1)/4*s2 - s1*L := by
    have h := hDpos
    ring_nf at h ⊢
    linarith
  exact hgoal


theorem sigmaLessThanSumLog {N : ℕ} (hN : 2 ≤ N) (ε θ : Fin N → ℝ)
    (hε0 : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j < 1)
    (hεlow : ∀ j, Real.exp (-(1/A0)) ≤ ε j)
    (hεhigh : ∀ j, ε j ≤ rhoP N)
    (hprod : Real.exp (-(2/A0)) ≤ ∏ j, ε j) :
    ∃ k ∈ Finset.Icc 1 (KK N),
      (∑ j, Real.log ‖(1:ℂ) - (ε j : ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ j:ℂ))‖)
        < ∑ j, Real.log (ε j) := by
  classical
  obtain ⟨hK1, -, -, -⟩ := mahler_numeric hN
  by_contra hcon
  push_neg at hcon
  set K : ℕ := KK N with hKdef
  set t : ℝ := ∑ j, Real.log (ε j) with ht
  set Lp : ℝ := ∑ j, Real.log (1 + ε j) with hLp
  set L : ℝ := ∑ j, Real.log (1/(1 - ε j)) with hL
  set lam : ℝ := (1/2) * L with hlam
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hKpos : (0:ℝ) < (K:ℝ) := by
    have h1 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK1
    linarith
  obtain ⟨k0, hk0mem, hk0min⟩ :=
    Finset.exists_min_image (Finset.Icc 1 K) (sigmaF ε θ) (Finset.nonempty_Icc.mpr hK1)
  set M0 : ℝ := sigmaF ε θ k0 with hM0
  have hlow : t ≤ M0 := by
    rw [hM0]
    exact hcon k0 hk0mem
  have hupp : ∀ k ∈ Finset.Icc 1 K, sigmaF ε θ k ≤ Lp := by
    intro k _
    rw [hLp]
    exact sigmaF_le ε θ k hε0 hε1
  have hmin' : ∀ i ∈ Finset.Icc 1 K, M0 ≤ sigmaF ε θ i := by
    intro i hi; rw [hM0]; exact hk0min i hi
  have hsum_nonneg : 0 ≤ t + Lp := by
    rw [ht, hLp, ← Finset.sum_add_distrib]
    exact Finset.sum_nonneg (fun j _ => log_eps_add_nonneg (hεlow j) (hε1 j))
  have hTM : 0 ≤ M0 + Lp := by linarith
  have hw_nonneg : ∀ i ∈ Finset.Icc 1 K, 0 ≤ 1 - (i:ℝ)/((K:ℝ)+1) := by
    intro i hi
    have hi2 : i ≤ K := (Finset.mem_Icc.mp hi).2
    have hKp : (0:ℝ) < (K:ℝ) + 1 := by positivity
    rw [sub_nonneg, div_le_one hKp]
    have hcast : (i:ℝ) ≤ (K:ℝ) := by exact_mod_cast hi2
    linarith
  have hfejersum : ∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) = (K:ℝ)/2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using fejer_sum K
  have hμ : ∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) * sigmaF ε θ k ≤ lam := by
    rw [hlam, hL]
    simpa only [sigmaF] using logMoment_le ε θ K hε0 hε1
  have hsq : ((K:ℝ)+1)/4 * (∑ j, (ε j)^2) - (∑ j, ε j) * L
      ≤ ∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) * (sigmaF ε θ k)^2 := by
    rw [hL]
    simpa only [sigmaF] using logMoment_sq_ge_lin ε θ K hK1 hε0 hε1
  have haffine : ∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) * (sigmaF ε θ k)^2
      ≤ Lp * lam + M0 * (lam - Lp * ((K:ℝ)/2)) := by
    have h := weighted_sq_le (Finset.Icc 1 K) (fun k => 1 - (k:ℝ)/((K:ℝ)+1)) (sigmaF ε θ)
      (t := M0) (M := Lp) (A := lam) hw_nonneg hmin' hupp hμ hTM
    simp only [hfejersum] at h
    calc ∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) * (sigmaF ε θ k)^2
        ≤ (M0 + Lp) * lam - M0 * Lp * ((K:ℝ)/2) := h
      _ = Lp * lam + M0 * (lam - Lp * ((K:ℝ)/2)) := by ring
  have hmono : lam - Lp * ((K:ℝ)/2) ≤ 0 := by
    have hL_le : L ≤ (N:ℝ) * Real.log (12*(N:ℝ)) := by
      rw [hL]
      have hpt : ∀ j, Real.log (1/(1 - ε j)) ≤ Real.log (12*(N:ℝ)) := by
        intro j
        have hposj : (0:ℝ) < 1 - ε j := by linarith [hε1 j]
        refine Real.log_le_log (div_pos one_pos hposj) ?_
        rw [div_le_iff₀ hposj]
        have hle : (1:ℝ)/(12*(N:ℝ)) ≤ 1 - ε j := by
          have h := hεhigh j; rw [rhoP] at h; linarith
        have h12 : (0:ℝ) < 12*(N:ℝ) := by positivity
        have hmul : (12:ℝ)*(N:ℝ) * ((1:ℝ)/(12*(N:ℝ))) ≤ (12:ℝ)*(N:ℝ) * (1 - ε j) :=
          mul_le_mul_of_nonneg_left hle (le_of_lt h12)
        have hone : (12:ℝ)*(N:ℝ) * ((1:ℝ)/(12*(N:ℝ))) = 1 := by
          rw [mul_one_div, div_self (ne_of_gt h12)]
        linarith
      calc ∑ j, Real.log (1/(1 - ε j)) ≤ ∑ j, Real.log (12*(N:ℝ)) :=
            Finset.sum_le_sum (fun j _ => hpt j)
        _ = (N:ℝ) * Real.log (12*(N:ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hLp_ge : (N:ℝ)/2 ≤ Lp := by
      rw [hLp]
      have hpt : ∀ j, (1:ℝ)/2 ≤ Real.log (1 + ε j) :=
        fun j => half_le_log_one_add (hεlow j) (hε1 j)
      calc (N:ℝ)/2 = ∑ j : Fin N, (1:ℝ)/2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ ∑ j, Real.log (1 + ε j) := Finset.sum_le_sum (fun j _ => hpt j)
    have hLam : (1:ℝ) ≤ Real.log (12*(N:ℝ)) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have h := Real.exp_one_lt_three
      linarith
    have hK_ge : (54/5) * (N:ℝ) * Real.log (12*(N:ℝ)) - 1 < (K:ℝ) := by
      have h := Nat.sub_one_lt_floor ((54/5) * (N:ℝ) * Real.log (12*(N:ℝ)))
      rw [hKdef]
      simpa only [KK, B0] using h
    have hkey : (N:ℝ) * Real.log (12*(N:ℝ)) ≤ (K:ℝ) * Lp := by
      have h1 : ((54/5) * (N:ℝ) * Real.log (12*(N:ℝ)) - 1) * ((N:ℝ)/2)
          ≤ (K:ℝ) * ((N:ℝ)/2) :=
        mul_le_mul_of_nonneg_right (le_of_lt hK_ge) (by positivity)
      have h2 : (K:ℝ) * ((N:ℝ)/2) ≤ (K:ℝ) * Lp :=
        mul_le_mul_of_nonneg_left hLp_ge (le_of_lt hKpos)
      have h4 : Real.log (12*(N:ℝ)) ≤ 2.7 * (N:ℝ) * Real.log (12*(N:ℝ)) - 0.5 := by
        nlinarith [hLam, hN2]
      have h5 : (N:ℝ) * Real.log (12*(N:ℝ))
          ≤ (N:ℝ) * (2.7 * (N:ℝ) * Real.log (12*(N:ℝ)) - 0.5) :=
        mul_le_mul_of_nonneg_left h4 (le_of_lt hNpos)
      linarith [h1, h2, h5]
    rw [hlam]
    linarith [hL_le, hkey]
  have hM0le : M0 * (lam - Lp * ((K:ℝ)/2)) ≤ t * (lam - Lp * ((K:ℝ)/2)) :=
    mul_le_mul_of_nonpos_right hlow hmono
  have hkey' : ((K:ℝ)+1)/4 * (∑ j, (ε j)^2) - (∑ j, ε j) * L
      ≤ Lp * lam + t * (lam - Lp * ((K:ℝ)/2)) := by
    calc ((K:ℝ)+1)/4 * (∑ j, (ε j)^2) - (∑ j, ε j) * L
        ≤ ∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) * (sigmaF ε θ k)^2 := hsq
      _ ≤ Lp * lam + M0 * (lam - Lp * ((K:ℝ)/2)) := haffine
      _ ≤ Lp * lam + t * (lam - Lp * ((K:ℝ)/2)) := by linarith [hM0le]
  have hnum : Lp * lam + t * (lam - Lp * ((K:ℝ)/2))
      < ((K:ℝ)+1)/4 * (∑ j, (ε j)^2) - (∑ j, ε j) * L := by
    rw [hlam, hLp, hL, ht]
    rw [hKdef]
    exact hnumEpsLocal hN ε hε0 hε1 hεlow hεhigh hprod
  linarith [hkey', hnum]

end Work.BW
