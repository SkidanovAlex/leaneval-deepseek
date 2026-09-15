import Submission.Work.GYCorr7

/-!
# `GYCorr8`: the uniform form of the correlation main term (Green–Tao (GY2-est))

`GYCorr4.mainSum_eq_logR_corr` gives Green–Tao (10.2) for the degenerate system with constants
`∃ δ C`, i.e. depending on the shifts `h`.  This file restates the result with the **uniform**
constants `zbC m`, `zbD m` of Green–Tao Lemma 10.4 (`GYFactor9`), and uses the new uniform-in-`Δ`
majorant of `GYCorr2` to reduce the resulting error term to a multiple of the factor `LamD`
(`GYCorr7`).  This is what makes the error controllable **uniformly in the shifts**.
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace Corr

open GYMaj.BoxAvg
open Commons.NumberTheory.Sieve

variable {m : ℕ}

/-! ## 1. `G₂(0,0)` without any `Δ`-hypothesis -/

/-- **`G₂(0,0) = (W/φ(W))^m`** — the version of `GYFactor9.G2u_zero` for the correlation system
(no `LocHyp`, only `W ≠ 0`). -/
theorem G2u_zero_gen {W : ℕ} (hW0 : 0 < W) :
    G2u (m := m) W 0 0 = ((W : ℂ) / (Nat.totient W : ℂ)) ^ m := by
  have hW0' : W ≠ 0 := ne_of_gt hW0
  rw [G2u_eq_prod_corr hW0 0 0]
  have hstep : ∏ n ∈ W.divisors, E2p (m := m) W 0 0 n
      = ∏ n ∈ W.divisors.filter Nat.Prime, E2p (m := m) W 0 0 n := by
    rw [← Finset.prod_filter_mul_prod_filter_not (s := W.divisors) (p := fun n => n.Prime)
      (f := fun n => E2p (m := m) W 0 0 n)]
    have hz : ∏ n ∈ W.divisors.filter (fun n => ¬ n.Prime), E2p (m := m) W 0 0 n = 1 := by
      refine Finset.prod_eq_one (fun n hn => ?_)
      rw [Finset.mem_filter] at hn
      rw [BoxAvg.E2p_zero, if_neg]
      exact fun hc => hn.2 hc.1
    rw [hz, mul_one]
  rw [hstep]
  have hpf : W.divisors.filter Nat.Prime = W.primeFactors := by
    ext p
    rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h2, h1, hW0'⟩
    · rintro ⟨h1, h2, _⟩; exact ⟨⟨h2, hW0'⟩, h1⟩
  rw [hpf]
  have hval : ∀ p ∈ W.primeFactors, E2p (m := m) W 0 0 p = ((1 - (p : ℂ)⁻¹)⁻¹) ^ m := by
    intro p hp
    rw [BoxAvg.E2p_zero,
      if_pos ⟨(Nat.mem_primeFactors.mp hp).1, (Nat.mem_primeFactors.mp hp).2.1⟩]
  rw [Finset.prod_congr rfl hval, Finset.prod_pow,
    Commons.Data.Nat.prod_inv_one_sub_inv_primeFactors W hW0']

/-! ## 2. The main term with uniform constants -/

/-- **Green–Tao (10.2) for the degenerate system, with the uniform constants `zbC m`, `zbD m`.** -/
theorem mainSum_eq_logR_corr_expl {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) {R : ℕ} (hR : 3 ≤ R) :
      ‖(mainSum (m := m) (t := 1) R W (Ac m) h : ℂ)
          - (G1u W (Ac m) h 0 0 * G2u (m := m) W 0 0) * (Real.log (R : ℝ)) ^ m‖
        ≤ (zbC m) ^ m * stripBoundCorr (Delta h) W m * (1 + (Real.log (R : ℝ)) ^ (m - 1))
          + (zbC m) ^ m * stripBoundCorr (Delta h) W m
              * Real.exp (-(zbD m * Real.sqrt (Real.log (R : ℝ)))) := by
  have hspec := (Classical.choose_spec (Classical.choose_spec
    (Commons.NumberTheory.Zeta.zeta_bound_m_strip_sixth m hm))).2
  have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hR1
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3one : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_three
  have ha : 0 < 1 / Real.log (R : ℝ) := by positivity
  have hlogle : Real.log 3 ≤ Real.log (R : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hR)
  have hab : 1 / Real.log (R : ℝ) ≤ 1 + (m : ℝ) := by
    have h1 : 1 / Real.log (R : ℝ) ≤ 1 / Real.log 3 :=
      one_div_le_one_div_of_le hlog3 hlogle
    have h2 : 1 / Real.log 3 ≤ 1 := by
      rw [div_le_one hlog3]; exact le_of_lt hlog3one
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < R))
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hc1m : (1 : ℝ) < 1 + (m : ℝ) := by linarith
  have hmain' := hspec.2 (R : ℝ) (by exact_mod_cast hR)
    (fun z z' => G1u W (Ac m) h z z' * G2u W z z') (stripBoundCorr (Delta h) W m)
    (by unfold stripBoundCorr; positivity)
    (((continuousOn_G1c hm hW0 hΔ0).mul (continuousOn_G2c hm hW0)).mono
      (fun x hx => ⟨fun i => (hx.1 i).1, fun i => (hx.2 i).1⟩))
    (fun j z z' hz hz' =>
      (differentiableAt_G1c_curve₁ hm hW0 hΔ0 (fun i => (hz i).1) (fun i => (hz' i).1)).mul
        (differentiableAt_G2c_curve₁ hm hW0 (fun i => (hz i).1) (fun i => (hz' i).1)))
    (fun j z z' hz hz' =>
      (differentiableAt_G1c_curve₂ hm hW0 hΔ0 (fun i => (hz i).1) (fun i => (hz' i).1)).mul
        (differentiableAt_G2c_curve₂ hm hW0 (fun i => (hz i).1) (fun i => (hz' i).1)))
    (fun z z' hz hz' => by
      rw [norm_mul]
      exact mul_le_mul (norm_G1c_le hm hW0 hΔ0 (fun i => le_of_lt (hz i).1)
          (fun i => le_of_lt (hz' i).1))
        (norm_G2c_le hm hW0 (fun i => le_of_lt (hz i).1) (fun i => le_of_lt (hz' i).1))
        (norm_nonneg _) (Real.exp_nonneg _))
  rw [mainSum_eq_contour (m := m) (t := 1) hm (c := 1 + (m : ℝ)) (by linarith) R W (Ac m) h
      le_rfl (Ac_natAbs_le m) (Ac_ne_zero m) hW0, ContourInt_eq]
  rw [show (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Eker (t := 1) (1 + (m : ℝ)) R W (Ac m) h (fun i => (t_ i, t_' i)))
      = ∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W (Ac m) h (fun i => sline (1 + (m : ℝ)) (t_ i))
          (fun i => sline (1 + (m : ℝ)) (t_' i)) by
    simp_rw [Eker_eq_Psi_corr hc1m hm hW0 hΔ0]]
  rw [show (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W (Ac m) h (fun i => sline (1 + (m : ℝ)) (t_ i))
          (fun i => sline (1 + (m : ℝ)) (t_' i)))
      = ∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W (Ac m) h (fun i => sline (1 / Real.log (R : ℝ)) (t_ i))
          (fun i => sline (1 / Real.log (R : ℝ)) (t_' i)) from
    contourShift_Psi_corr hm hW0 hΔ0 hR ha hab]
  simp_rw [← MeasureTheory.integral_mul_const]
  have hI : (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W (Ac m) h (fun i => sline (1 / Real.log (R : ℝ)) (t_ i))
          (fun i => sline (1 / Real.log (R : ℝ)) (t_' i)) * (Complex.I ^ m * Complex.I ^ m))
      = (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
          (G1u W (Ac m) h (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j))
            * G2u W (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)))
          * (∏ j, (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j)
                + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j))
              / (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j))
                  * riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)))))
          * (((R : ℝ)) : ℂ) ^ (∑ j, (Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j)
              + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)))
          * (∏ j, ((Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j)) ^ 2
                * (Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)) ^ 2)⁻¹)
          * Complex.I ^ m * Complex.I ^ m) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t_ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t_' => ?_)
    exact Psi_mul_I_eq_corr hRc t_ t_'
  rw [hI]
  rw [zbC_eq hm, zbD_eq hm]
  exact hmain'

/-! ## 3. `exp(∑ e1pMajorCorr) ≤ const · ∏_{q | Δ}(1 + q^{-1/2})^{Da}`

This is the payoff of the redesign of the majorant in `GYCorr2`: the whole `Δ`-dependence of the
summable majorant collapses into the `LamD` factor. -/

/-- The constant `exp(∑_{n ≤ (6m)²+2} K0 m)` of the finite-supported part of the majorant. -/
noncomputable def EK (m : ℕ) : ℝ :=
  Real.exp ((((6 * m) ^ 2 + 3 : ℕ) : ℝ) * K0 m)

lemma EK_pos (m : ℕ) : 0 < EK m := Real.exp_pos _

/-- `q^{-2/3} ≤ 2 log(1 + q^{-1/2})` for `q ≥ 2`. -/
lemma rpow_neg_two_thirds_le_log {q : ℕ} (hq : 2 ≤ q) :
    (q : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 2 * Real.log (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have h1 : (q : ℝ) ^ (-(2 / 3 : ℝ)) ≤ (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
    norm_num
  have h2 : (q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
    rwa [Real.rpow_zero] at h
  have h3 := half_mul_le_log_one_add (Real.rpow_nonneg hq0.le _) h2
  linarith

/-- **The `Δ`-dependence of the correlation majorant is only through `LamD`.** -/
theorem stripBoundCorr_le {W : ℕ} {δ : Fin m → ℤ} (hm : 1 ≤ m) (hΔ0 : Delta δ ≠ 0) :
    stripBoundCorr (Delta δ) W m ≤ EK m * stripBound W m * LamD m δ := by
  set S : Finset ℕ := (Delta δ).primeFactors with hS
  have hsummable : Summable (e1pMajor m) := summable_e1pMajor hm
  have ha : Summable (fun n : ℕ => if n ≤ (6 * m) ^ 2 + 2 then K0 m else (0 : ℝ)) :=
    summable_of_ne_finset_zero (s := Finset.range ((6 * m) ^ 2 + 3)) (fun n hn => by
      rw [Finset.mem_range] at hn
      rw [if_neg (by omega : ¬ n ≤ (6 * m) ^ 2 + 2)])
  have hb : Summable (fun n : ℕ =>
      if n.Prime ∧ n ∣ Delta δ then K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ)) else (0 : ℝ)) :=
    summable_of_ne_finset_zero (s := S) (fun n hn => by
      rw [if_neg]
      rintro ⟨hpn, hdvd⟩
      exact hn (by rw [hS]; exact Nat.mem_primeFactors.mpr ⟨hpn, hdvd, hΔ0⟩))
  have hdecomp : (∑' n : ℕ, e1pMajorCorr (Delta δ) m n)
      = (∑' n : ℕ, e1pMajor m n)
        + (∑' n : ℕ, if n ≤ (6 * m) ^ 2 + 2 then K0 m else (0 : ℝ))
        + (∑' n : ℕ, if n.Prime ∧ n ∣ Delta δ then K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ))
            else (0 : ℝ)) := by
    rw [show (∑' n : ℕ, e1pMajorCorr (Delta δ) m n)
        = ∑' n : ℕ, (e1pMajor m n
            + (if n ≤ (6 * m) ^ 2 + 2 then K0 m else (0 : ℝ))
            + (if n.Prime ∧ n ∣ Delta δ then K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ)) else (0 : ℝ))) by
      exact tsum_congr (fun n => rfl)]
    rw [Summable.tsum_add (hsummable.add ha) hb, Summable.tsum_add hsummable ha]
  have hsum_a : (∑' n : ℕ, if n ≤ (6 * m) ^ 2 + 2 then K0 m else (0 : ℝ))
      = (((6 * m) ^ 2 + 3 : ℕ) : ℝ) * K0 m := by
    have h := tsum_eq_sum (L := SummationFilter.unconditional ℕ)
      (f := fun n : ℕ => if n ≤ (6 * m) ^ 2 + 2 then K0 m else (0 : ℝ))
      (s := Finset.range ((6 * m) ^ 2 + 3)) (fun n hn => by
        rw [Finset.mem_range] at hn
        rw [if_neg (by omega : ¬ n ≤ (6 * m) ^ 2 + 2)])
    rw [h]
    calc ∑ n ∈ Finset.range ((6 * m) ^ 2 + 3), (if n ≤ (6 * m) ^ 2 + 2 then K0 m else (0 : ℝ))
        = ∑ _n ∈ Finset.range ((6 * m) ^ 2 + 3), K0 m := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          rw [Finset.mem_range] at hn
          rw [if_pos (by omega)]
      _ = (((6 * m) ^ 2 + 3 : ℕ) : ℝ) * K0 m := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum_b : (∑' n : ℕ, if n.Prime ∧ n ∣ Delta δ then K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ))
        else (0 : ℝ)) = ∑ q ∈ S, K0 m * (q : ℝ) ^ (-(2 / 3 : ℝ)) := by
    have h := tsum_eq_sum (L := SummationFilter.unconditional ℕ)
      (f := fun n : ℕ => if n.Prime ∧ n ∣ Delta δ then K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ))
        else (0 : ℝ)) (s := S) (fun n hn => by
        rw [if_neg]
        rintro ⟨hpn, hdvd⟩
        exact hn (by rw [hS]; exact Nat.mem_primeFactors.mpr ⟨hpn, hdvd, hΔ0⟩))
    rw [h]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [if_pos ⟨(Nat.mem_primeFactors.mp (by rw [← hS]; exact hq)).1,
      (Nat.mem_primeFactors.mp (by rw [← hS]; exact hq)).2.1⟩]
  have hkey : (∑' n : ℕ, e1pMajorCorr (Delta δ) m n)
      ≤ (∑' n : ℕ, e1pMajor m n) + (((6 * m) ^ 2 + 3 : ℕ) : ℝ) * K0 m
        + ∑ q ∈ S, Da m * Real.log (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) := by
    rw [hdecomp, hsum_a, hsum_b]
    have h2 : ∑ q ∈ S, K0 m * (q : ℝ) ^ (-(2 / 3 : ℝ))
        ≤ ∑ q ∈ S, Da m * Real.log (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) := by
      refine Finset.sum_le_sum (fun q hq => ?_)
      have hqS : q ∈ (Delta δ).primeFactors := by rw [← hS]; exact hq
      have hq2 : 2 ≤ q := (Nat.mem_primeFactors.mp hqS).1.two_le
      have h1 := rpow_neg_two_thirds_le_log hq2
      have hDa : 2 * K0 m ≤ Da m := by unfold Da; exact le_max_right _ _
      have hlognn : 0 ≤ Real.log (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) :=
        Real.log_nonneg (by
          have hq0 : (0 : ℝ) < (q : ℝ) := by
            exact_mod_cast (Nat.mem_primeFactors.mp hqS).1.pos
          have : (0 : ℝ) ≤ (q : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hq0.le _
          linarith)
      nlinarith [h1, K0_nonneg m, hlognn, hDa]
    linarith
  have hprod : (∏ q ∈ S, Real.exp (Da m * Real.log (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))))
      = ∏ q ∈ S, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) ^ (Da m) := by
    refine Finset.prod_congr rfl (fun q hq => ?_)
    rw [mul_comm, Real.exp_mul, Real.exp_log]
    have hqS : q ∈ (Delta δ).primeFactors := by rw [← hS]; exact hq
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (Nat.mem_primeFactors.mp hqS).1.pos
    have : (0 : ℝ) < (q : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hq0 _
    linarith
  have h1 : Real.exp (∑' n : ℕ, e1pMajorCorr (Delta δ) m n)
      ≤ EK m * Real.exp (∑' n : ℕ, e1pMajor m n)
        * ∏ q ∈ S, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) ^ (Da m) := by
    calc Real.exp (∑' n : ℕ, e1pMajorCorr (Delta δ) m n)
        ≤ Real.exp ((∑' n : ℕ, e1pMajor m n) + (((6 * m) ^ 2 + 3 : ℕ) : ℝ) * K0 m
            + ∑ q ∈ S, Da m * Real.log (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) :=
          Real.exp_le_exp.mpr hkey
      _ = EK m * Real.exp (∑' n : ℕ, e1pMajor m n)
            * ∏ q ∈ S, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) ^ (Da m) := by
          rw [EK, ← hprod, Real.exp_add, Real.exp_add, Real.exp_sum]
          ring
  have h32 : (0 : ℝ) ≤ (32 : ℝ) ^ (m * W.divisors.card) := by positivity
  calc stripBoundCorr (Delta δ) W m
      = Real.exp (∑' n : ℕ, e1pMajorCorr (Delta δ) m n)
          * (32 : ℝ) ^ (m * W.divisors.card) := rfl
    _ ≤ (EK m * Real.exp (∑' n : ℕ, e1pMajor m n)
          * ∏ q ∈ S, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) ^ (Da m))
          * (32 : ℝ) ^ (m * W.divisors.card) := mul_le_mul_of_nonneg_right h1 h32
    _ = EK m * stripBound W m * LamD m δ := by
        rw [stripBound, LamD]
        ring


/-! ## 4. The `hmain` input of `boxAvgCorr_ub` -/

/-- `‖G₂(0,0)‖ = (W/φ(W))^a`. -/
lemma norm_G2u_zero_gen {W a : ℕ} (hW0 : 0 < W) :
    ‖G2u (m := a) W 0 0‖ = ((W : ℝ) / (Nat.totient W : ℝ)) ^ a := by
  rw [G2u_zero_gen (m := a) hW0, norm_pow]
  congr 1
  rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]

/-- **Green–Tao (GY2-est) upper bound for the main term**, uniformly in the shifts: this is the
`hmain` hypothesis of `boxAvgCorr_ub`.

The hypothesis `hsmall` is the only condition on `R`: after `stripBoundCorr_le` the contour-shift
error is a multiple of `LamD`, which cancels against the `LamD` of the main term.  Hence `hsmall`
is **uniform in the shifts `δ`** — the whole point of the uniform majorant of `GYCorr2`. -/
theorem mainSum_le_corr {W : ℕ} (hW0 : 0 < W) {a : ℕ} (ha1 : 1 ≤ a) {R : ℕ} (hR : 3 ≤ R)
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : 4 * ((zbC a) ^ a * (EK a * stripBound W a))
      ≤ (ε / 2) * Real.log (R : ℝ) * Kc a)
    {δ : Fin a → ℤ} (hΔ0 : Delta δ ≠ 0) :
    mainSum (m := a) (t := 1) R W (Ac a) δ
      ≤ (1 + ε / 2) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ a
          * (Kc a * LamD a δ) := by
  have hm := mainSum_eq_logR_corr_expl (m := a) ha1 hW0 hΔ0 hR
  have hG1 := G1u_zero_bound (a := a) ha1 hW0 (δ := δ) hΔ0
  have hsb := stripBoundCorr_le (m := a) (W := W) ha1 hΔ0
  have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
  have hL0 : (0 : ℝ) < Real.log (R : ℝ) := Real.log_pos hR1
  have hL1 : (1 : ℝ) ≤ Real.log (R : ℝ) := by
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      exact le_of_lt Real.exp_one_lt_three
    exact le_trans h3 (Real.log_le_log (by norm_num) (by exact_mod_cast hR))
  have hφpos : (0 : ℝ) < (Nat.totient W : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hW0)
  have hφW1 : (1 : ℝ) ≤ (W : ℝ) / (Nat.totient W : ℝ) := by
    rw [le_div_iff₀ hφpos]
    have h := Nat.totient_le W
    have h' : ((Nat.totient W : ℕ) : ℝ) ≤ (W : ℝ) := by exact_mod_cast h
    linarith
  set P : ℝ := (W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ) with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hLP : Real.log (R : ℝ) ≤ P := by
    have h2 : Real.log (R : ℝ) * 1
        ≤ Real.log (R : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) :=
      mul_le_mul_of_nonneg_left hφW1 hL0.le
    have h3 : (W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)
        = Real.log (R : ℝ) * ((W : ℝ) / (Nat.totient W : ℝ)) := by ring
    rw [hP]
    linarith [h2]
  -- the norm of the main term
  have hZnorm : ‖(G1u W (Ac a) δ 0 0 * G2u (m := a) W 0 0)
        * ((Real.log (R : ℝ) : ℂ)) ^ a‖ ≤ Kc a * LamD a δ * P ^ a := by
    have hPpow : P ^ a = ((W : ℝ) / (Nat.totient W : ℝ)) ^ a * Real.log (R : ℝ) ^ a := by
      rw [hP]; ring
    calc ‖(G1u W (Ac a) δ 0 0 * G2u (m := a) W 0 0)
            * ((Real.log (R : ℝ) : ℂ)) ^ a‖
        = ‖G1u W (Ac a) δ 0 0‖ * ‖G2u (m := a) W 0 0‖ * Real.log (R : ℝ) ^ a := by
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hL0.le]
      _ = ‖G1u W (Ac a) δ 0 0‖
            * (((W : ℝ) / (Nat.totient W : ℝ)) ^ a * Real.log (R : ℝ) ^ a) := by
          rw [norm_G2u_zero_gen hW0]; ring
      _ = ‖G1u W (Ac a) δ 0 0‖ * P ^ a := by rw [hPpow]
      _ ≤ (Kc a * LamD a δ) * P ^ a := mul_le_mul_of_nonneg_right hG1 (pow_nonneg hP0 a)
      _ = Kc a * LamD a δ * P ^ a := by ring
  -- the error term
  have hexp1 : Real.exp (-(zbD a * Real.sqrt (Real.log (R : ℝ)))) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (show -(zbD a * Real.sqrt (Real.log (R : ℝ))) ≤ 0 by
      have h1 : 0 ≤ zbD a * Real.sqrt (Real.log (R : ℝ)) :=
        mul_nonneg (le_of_lt (zbD_pos ha1)) (Real.sqrt_nonneg _)
      linarith)
    rwa [Real.exp_zero] at h
  have hLa1 : (1 : ℝ) ≤ Real.log (R : ℝ) ^ (a - 1) := one_le_pow₀ hL1
  have hLapos : (0 : ℝ) < Real.log (R : ℝ) ^ (a - 1) := lt_of_lt_of_le one_pos hLa1
  have hA0 : (0 : ℝ) ≤ (zbC a) ^ a := pow_nonneg (le_of_lt (zbC_pos ha1)) a
  have hB0 : (0 : ℝ) ≤ EK a * stripBound W a := by
    refine mul_nonneg (EK_pos a).le ?_
    rw [stripBound]
    exact mul_nonneg (Real.exp_nonneg _) (pow_nonneg (by norm_num) _)
  have hΛ0 : (0 : ℝ) ≤ LamD a δ := le_trans zero_le_one (one_le_LamD a δ)
  have hS0 : (0 : ℝ) ≤ stripBoundCorr (Delta δ) W a := by
    rw [stripBoundCorr]
    exact mul_nonneg (Real.exp_nonneg _) (pow_nonneg (by norm_num) _)
  -- `A * S ≤ A * B * Λ`
  have hAS : (zbC a) ^ a * stripBoundCorr (Delta δ) W a
      ≤ (zbC a) ^ a * (EK a * stripBound W a) * LamD a δ := by
    calc (zbC a) ^ a * stripBoundCorr (Delta δ) W a
        ≤ (zbC a) ^ a * (EK a * stripBound W a * LamD a δ) :=
          mul_le_mul_of_nonneg_left hsb hA0
      _ = (zbC a) ^ a * (EK a * stripBound W a) * LamD a δ := by ring
  have hAB0 : (0 : ℝ) ≤ (zbC a) ^ a * (EK a * stripBound W a) := mul_nonneg hA0 hB0
  have hErr : (zbC a) ^ a * stripBoundCorr (Delta δ) W a
        * (1 + Real.log (R : ℝ) ^ (a - 1))
      + (zbC a) ^ a * stripBoundCorr (Delta δ) W a
          * Real.exp (-(zbD a * Real.sqrt (Real.log (R : ℝ))))
      ≤ 4 * ((zbC a) ^ a * (EK a * stripBound W a)) * LamD a δ
          * Real.log (R : ℝ) ^ (a - 1) := by
    have h4 : (1 : ℝ) + Real.log (R : ℝ) ^ (a - 1)
        ≤ 2 * Real.log (R : ℝ) ^ (a - 1) := by linarith
    have h4' : Real.exp (-(zbD a * Real.sqrt (Real.log (R : ℝ))))
        ≤ Real.log (R : ℝ) ^ (a - 1) := le_trans hexp1 hLa1
    have hU0 : (0 : ℝ) ≤ (zbC a) ^ a * (EK a * stripBound W a) * LamD a δ :=
      mul_nonneg hAB0 hΛ0
    have hA1 : (zbC a) ^ a * stripBoundCorr (Delta δ) W a
          * (1 + Real.log (R : ℝ) ^ (a - 1))
        ≤ ((zbC a) ^ a * (EK a * stripBound W a) * LamD a δ)
            * (2 * Real.log (R : ℝ) ^ (a - 1)) :=
      mul_le_mul hAS h4 (by linarith) hU0
    have hA2 : (zbC a) ^ a * stripBoundCorr (Delta δ) W a
          * Real.exp (-(zbD a * Real.sqrt (Real.log (R : ℝ))))
        ≤ ((zbC a) ^ a * (EK a * stripBound W a) * LamD a δ)
            * Real.log (R : ℝ) ^ (a - 1) :=
      mul_le_mul hAS h4' (Real.exp_nonneg _) hU0
    have hEq1 : ((zbC a) ^ a * (EK a * stripBound W a) * LamD a δ)
          * (2 * Real.log (R : ℝ) ^ (a - 1))
        = 2 * ((zbC a) ^ a * (EK a * stripBound W a)) * LamD a δ
            * Real.log (R : ℝ) ^ (a - 1) := by ring
    have hEq2 : ((zbC a) ^ a * (EK a * stripBound W a) * LamD a δ)
          * Real.log (R : ℝ) ^ (a - 1)
        = ((zbC a) ^ a * (EK a * stripBound W a)) * LamD a δ
            * Real.log (R : ℝ) ^ (a - 1) := by ring
    have hNN : (0 : ℝ) ≤ (zbC a) ^ a * (EK a * stripBound W a) * LamD a δ
        * Real.log (R : ℝ) ^ (a - 1) := mul_nonneg (mul_nonneg hAB0 hΛ0) hLapos.le
    linarith [hA1, hA2, hEq1, hEq2, hNN]
  have hErr2 : 4 * ((zbC a) ^ a * (EK a * stripBound W a)) * LamD a δ
        * Real.log (R : ℝ) ^ (a - 1)
      ≤ (ε / 2) * (Kc a * LamD a δ * P ^ a) := by
    have hK : (0 : ℝ) ≤ Kc a := (Kc_pos a).le
    have hla : Real.log (R : ℝ) * Real.log (R : ℝ) ^ (a - 1) = Real.log (R : ℝ) ^ a := by
      conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ']
    have hLPow : Real.log (R : ℝ) ^ a ≤ P ^ a := pow_le_pow_left₀ hL0.le hLP a
    calc 4 * ((zbC a) ^ a * (EK a * stripBound W a)) * LamD a δ
            * Real.log (R : ℝ) ^ (a - 1)
        = (4 * ((zbC a) ^ a * (EK a * stripBound W a)))
            * (LamD a δ * Real.log (R : ℝ) ^ (a - 1)) := by ring
      _ ≤ ((ε / 2) * Real.log (R : ℝ) * Kc a) * (LamD a δ * Real.log (R : ℝ) ^ (a - 1)) :=
          mul_le_mul_of_nonneg_right hsmall (mul_nonneg hΛ0 hLapos.le)
      _ = (ε / 2) * Kc a * LamD a δ
            * (Real.log (R : ℝ) * Real.log (R : ℝ) ^ (a - 1)) := by ring
      _ = (ε / 2) * Kc a * LamD a δ * Real.log (R : ℝ) ^ a := by rw [hla]
      _ ≤ (ε / 2) * Kc a * LamD a δ * P ^ a :=
          mul_le_mul_of_nonneg_left hLPow (mul_nonneg (mul_nonneg (by linarith [hε]) hK) hΛ0)
      _ = (ε / 2) * (Kc a * LamD a δ * P ^ a) := by ring
  -- the "real part" trick
  have hreal : mainSum (m := a) (t := 1) R W (Ac a) δ
      ≤ ‖(G1u W (Ac a) δ 0 0 * G2u (m := a) W 0 0) * ((Real.log (R : ℝ) : ℂ)) ^ a‖
        + ‖(mainSum (m := a) (t := 1) R W (Ac a) δ : ℂ)
            - (G1u W (Ac a) δ 0 0 * G2u (m := a) W 0 0)
              * ((Real.log (R : ℝ) : ℂ)) ^ a‖ := by
    have h1 := Complex.abs_re_le_norm
      ((mainSum (m := a) (t := 1) R W (Ac a) δ : ℂ)
        - (G1u W (Ac a) δ 0 0 * G2u (m := a) W 0 0) * ((Real.log (R : ℝ) : ℂ)) ^ a)
    have h2 : ((mainSum (m := a) (t := 1) R W (Ac a) δ : ℂ)
        - (G1u W (Ac a) δ 0 0 * G2u (m := a) W 0 0)
          * ((Real.log (R : ℝ) : ℂ)) ^ a).re
        = mainSum (m := a) (t := 1) R W (Ac a) δ
          - ((G1u W (Ac a) δ 0 0 * G2u (m := a) W 0 0)
              * ((Real.log (R : ℝ) : ℂ)) ^ a).re := by
      simp [Complex.sub_re]
    have h3 := Complex.re_le_norm
      ((G1u W (Ac a) δ 0 0 * G2u (m := a) W 0 0) * ((Real.log (R : ℝ) : ℂ)) ^ a)
    rw [h2] at h1
    have h4 : mainSum (m := a) (t := 1) R W (Ac a) δ
        - ((G1u W (Ac a) δ 0 0 * G2u (m := a) W 0 0)
            * ((Real.log (R : ℝ) : ℂ)) ^ a).re
        ≤ ‖(mainSum (m := a) (t := 1) R W (Ac a) δ : ℂ)
            - (G1u W (Ac a) δ 0 0 * G2u (m := a) W 0 0)
              * ((Real.log (R : ℝ) : ℂ)) ^ a‖ :=
      le_trans (le_abs_self _) h1
    linarith
  calc mainSum (m := a) (t := 1) R W (Ac a) δ
      ≤ ‖(G1u W (Ac a) δ 0 0 * G2u (m := a) W 0 0) * ((Real.log (R : ℝ) : ℂ)) ^ a‖
        + ‖(mainSum (m := a) (t := 1) R W (Ac a) δ : ℂ)
            - (G1u W (Ac a) δ 0 0 * G2u (m := a) W 0 0)
              * ((Real.log (R : ℝ) : ℂ)) ^ a‖ := hreal
    _ ≤ Kc a * LamD a δ * P ^ a
        + ((zbC a) ^ a * stripBoundCorr (Delta δ) W a
              * (1 + Real.log (R : ℝ) ^ (a - 1))
            + (zbC a) ^ a * stripBoundCorr (Delta δ) W a
              * Real.exp (-(zbD a * Real.sqrt (Real.log (R : ℝ))))) :=
          add_le_add hZnorm hm
    _ ≤ Kc a * LamD a δ * P ^ a + (ε / 2) * (Kc a * LamD a δ * P ^ a) :=
          add_le_add le_rfl (le_trans hErr hErr2)
    _ = (1 + ε / 2) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ a
          * (Kc a * LamD a δ) := by rw [← hP]; ring

/-! ## 5. `boxAvgCorr_ub` with its hypotheses discharged -/

/-- **The box-average upper bound for the correlation system**, with the `hmain` and `herr`
hypotheses of `boxAvgCorr_ub` discharged. -/
theorem boxAvgCorr_ub' (k R W : ℕ) (ε : ℝ) (hk : 1 ≤ k) (hR : 3 ≤ R) (hRk : 3 * k ≤ R)
    (hW : 1 ≤ W) (hε : 0 < ε)
    (hsmallEr : 6 * (3 * (k : ℝ)) * (Real.log (R : ℝ)) ^ (k * 2 ^ (k - 1))
      ≤ ε * (R : ℝ) ^ 6)
    (hsmallMn : ∀ a : ℕ, 1 ≤ a → a ≤ k * 2 ^ (k - 1) →
      4 * ((zbC a) ^ a * (EK a * stripBound W a)) ≤ (ε / 2) * Real.log (R : ℝ) * Kc a) :
    ∀ (a : ℕ) (δ : Fin a → ℤ) (l r : Fin 1 → ℤ), CorrBoxData k R W a δ l r →
      (sideProd l r)⁻¹ * boxSum R W (Ac a) δ l r
        ≤ (1 + ε) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ a
            * (Kc a * LamD a δ) := by
  have hW0 : 0 < W := by omega
  refine boxAvgCorr_ub k R W ε hR hRk hW hε hsmallEr ?_ ?_
  · intro a δ l r hD
    obtain ⟨ha1, haK, hside, hpos, hΔ0⟩ := hD
    exact errBd_le k R W ε hR hRk hW hε hsmallEr a 1 (Ac a) δ l r ha1 haK le_rfl
      (by omega) hside hpos
  · intro a δ l r hD
    obtain ⟨ha1, haK, hside, hpos, hΔ0⟩ := hD
    exact mainSum_le_corr hW0 ha1 hR hε (hsmallMn a ha1 haK) hΔ0

end Corr
end GYMaj
