import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est14_defs
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.card_auxIdx
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.acH_lower
import Submission.Work.BW.est_Pi
import Submission.Work.BW.est_Theta_yu
import Submission.Work.BW.num_13
import Submission.Work.BW.ulcm_le_three_pow
import Submission.Work.BW.syl_log_facts
import Submission.Work.BW.est14_hanson_entropy
import Submission.Work.BW.est14_hanson_num
import Submission.Work.BW.num_T
import Submission.Work.BW.est14_phibound
import Submission.Work.BW.est14_thetaopt
import Submission.Work.BW.est14_torusbound
import Submission.Work.BW.est14_sigbound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester): BW (14) at descent level `J` (see the statement
below). The proof is assembled from the sibling nodes `acH_lower`, `est_Pi`, `est_Theta_yu`,
`num_T`, `sigma_ge`, `num_D_lower`, `card_auxIdx`, the shared evaluation algebra in
`est14_defs`, and the four helper lemmas `est14_phibound`, `est14_thetaopt`, `est14_torusbound`,
`est14_sigbound`. -/

namespace Work.BW

open MvPolynomial

section Bounds

variable {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
  {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
  {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
  {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}

theorem est14_arith {SD v Q u T' t0 Tst P L h : ℝ}
    (hh : 0 ≤ h) (hu : 0 ≤ u) (hQ : Q ≤ u)
    (hT : T' + t0 ≤ Tst)
    (hP : P * L ≤ 0.02058 * SD)
    (h1 : 0.1 * h * P ≤ 0.0735 * SD)
    (h2 : 0.001 * h * P ≤ 0.000735 * SD)
    (h3 : 0.007 * h * v ≤ 0.001185 * SD) :
    0.001 * h * P + h * T' + P * L + h * t0 + 0.1 * h * P
        + 0.108 * SD + 0.007 * Q + 0.007 * h * v + u + 0.001 * SD + 0.002 * u
      ≤ h * Tst + 0.205 * SD + 1.01 * u := by
  have hT' : h * (T' + t0) ≤ h * Tst := mul_le_mul_of_nonneg_left hT hh
  have hQ' : 0.007 * Q ≤ 0.007 * u := by linarith
  linarith

theorem est14_log_bound {t A : ℝ} (ht : 0 ≤ t) (hA : Real.log 1000 ≤ 0.001 * A) :
    t ≤ Real.exp (0.001 * A + 0.001 * t) := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · rw [← h0]; positivity
  · refine Real.le_exp_of_log_le ?_
    have h1 : Real.log (t / 1000) ≤ t / 1000 - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hpos (by norm_num))
    rw [Real.log_div (ne_of_gt hpos) (by norm_num : (1000:ℝ) ≠ 0)] at h1
    linarith

/-- `d = [K:ℚ] ≥ 1`. -/
lemma one_le_dK : 1 ≤ dK K := by
  have h : 0 < Module.finrank ℚ K := Module.finrank_pos
  simp only [dK]
  omega

lemma dK_pos_real : (0:ℝ) < (dK K : ℝ) := by
  have h : 0 < dK K := lt_of_lt_of_le Nat.zero_lt_one one_le_dK
  exact_mod_cast h

/-- `Λ ≠ 0` (from the `ℚ`-independence of the `log φ(αᵢ)` and `b k ≠ 0`). -/
lemma est14_lam_ne_zero (H : ACHyp φ α b k c v L α' σ ι p) : lam φ α b ≠ 0 := by
  intro h0
  have hlin := H.hst.2.2.1
  have hbk : b k ≠ 0 := H.hst.2.2.2.2.1
  have hsmul : ∀ i : Fin n,
      ((b i : ℚ) • Complex.log (φ (α i))) = (b i : ℂ) * Complex.log (φ (α i)) := by
    intro i
    rw [Algebra.smul_def]
    exact congrArg (· * Complex.log (φ (α i))) (Rat.cast_intCast (b i))
  have hsum : (∑ i, (b i : ℚ) • Complex.log (φ (α i))) = 0 := by
    calc (∑ i, (b i : ℚ) • Complex.log (φ (α i)))
        = ∑ i, (b i : ℂ) * Complex.log (φ (α i)) := Finset.sum_congr rfl (fun i _ => hsmul i)
      _ = lam φ α b := by rw [lam]
      _ = 0 := h0
  have hker := Fintype.linearIndependent_iff.mp hlin (fun i => (b i : ℚ)) hsum
  exact hbk (by exact_mod_cast hker k)

/-- BW (10): `‖Λ‖ ≤ exp(-9·2^r S D)`. -/
lemma est14_lambda_le (H : ACHyp φ α b k c v L α' σ ι p) :
    ‖lam φ α b‖ ≤ Real.exp (-(9 * 2 ^ r * acS K r b v * acD K σ)) := by
  have hne := est14_lam_ne_zero H
  have hpos : 0 < ‖lam φ α b‖ := norm_pos_iff.mpr hne
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr H.h10

/-- The Hanson bound in the logarithmic form needed here: `log (u(k)) ≤ 1·1 k` for `k ≥ 19`
(`u(k) = lcm(1,…,k)`), obtained from `est14_hanson_entropy` and `est14_hanson_num`. -/
lemma est14_log_ulcm_le (k : ℕ) (hk : 19 ≤ k) : Real.log (ulcm k) ≤ 1.1 * k := by
  have hlog3 : Real.log 3 ≤ 1.0987 := syl_log_facts.2.1
  have hLw : Lw k ≤ 1.0826 := syl_log_facts.2.2.2 k
  have hk0 : (0:ℝ) ≤ (k:ℝ) := by positivity
  have hupos : (0:ℝ) < (ulcm k : ℝ) := by exact_mod_cast ulcm_pos k
  rcases lt_or_ge k 4096 with hk' | hk'
  · have hsmall : (ulcm k : ℝ) ≤ (3:ℝ) ^ k := by
      have h := ulcm_le_three_pow_small k hk'
      have h2 : ((ulcm k : ℕ) : ℝ) ≤ ((3 ^ k : ℕ) : ℝ) := by exact_mod_cast h
      simpa using h2
    calc Real.log (ulcm k) ≤ Real.log ((3:ℝ) ^ k) := Real.log_le_log hupos hsmall
      _ = (k:ℝ) * Real.log 3 := by rw [Real.log_pow]
      _ ≤ (k:ℝ) * 1.0987 := mul_le_mul_of_nonneg_left hlog3 hk0
      _ ≤ 1.1 * (k:ℝ) := by linarith
  · have hdvd : sylBlocks k ∣ k.factorial :=
      (dvd_mul_left (sylBlocks k) (ulcm k)).trans (syl_divisibility k)
    have hMpos : 0 < sylBlocks k := Nat.pos_of_ne_zero (sylBlocks_ne_zero k)
    have hnat : ulcm k ≤ k.factorial / sylBlocks k := by
      rw [Nat.le_div_iff_mul_le hMpos]
      exact Nat.le_of_dvd (Nat.factorial_pos k) (syl_divisibility k)
    have hcast : ((k.factorial / sylBlocks k : ℕ) : ℝ) = (k.factorial : ℝ) / (sylBlocks k : ℝ) :=
      Nat.cast_div hdvd (by positivity)
    have hle : (ulcm k : ℝ) ≤ (k.factorial : ℝ) / (sylBlocks k : ℝ) := by
      rw [← hcast]; exact_mod_cast hnat
    have hlog1 : Real.log (ulcm k) ≤ Real.log ((k.factorial : ℝ) / (sylBlocks k : ℝ)) :=
      Real.log_le_log hupos hle
    have hE := est14_hanson_entropy k (by omega)
    have hN := est14_hanson_num k hk'
    have hLk : (k:ℝ) * Lw k ≤ (k:ℝ) * 1.0826 := mul_le_mul_of_nonneg_left hLw hk0
    have hnum : (((Finset.range (k + 1)).filter (fun i => syl i ≤ k)).card : ℝ) * Real.log k
        + Real.log k + Real.log (k + 1) + 1 + (k:ℝ) * 1.0826 ≤ (k:ℝ) * Real.log 3 := hN
    have hmain : Real.log ((k.factorial : ℝ) / (sylBlocks k : ℝ)) ≤ (k:ℝ) * 1.0987 := by
      have hk3 : (k:ℝ) * Real.log 3 ≤ (k:ℝ) * 1.0987 := mul_le_mul_of_nonneg_left hlog3 hk0
      linarith [hE, hLk, hnum, hk3]
    linarith [hlog1, hmain, hk0]

/-- `(u(h))^{t₀} ≤ exp(h t₀ + 0·1 h T)` (BW §13, from `u(h) ≤ 3^h` = `est14_log_ulcm_le`). -/
lemma est14_ulcm_le (H : ACHyp φ α b k c v L α' σ ι p) {t0 : ℕ}
    (ht0 : (t0 : ℝ) ≤ (pT r (dK K) σ : ℝ)) :
    ‖((ulcm (acH K b v) : ℂ) ^ t0)‖ ≤
      Real.exp ((acH K b v : ℝ) * (t0 : ℝ) + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) := by
  have hlogu := est14_log_ulcm_le (acH K b v) (acH_lower H).1
  have ht0nn : (0:ℝ) ≤ (t0:ℝ) := Nat.cast_nonneg _
  have hlog : (Real.log (ulcm (acH K b v)) - (acH K b v : ℝ)) * (t0:ℝ) ≤
      0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) := by
    have h1 : Real.log (ulcm (acH K b v)) - (acH K b v : ℝ) ≤ 0.1 * (acH K b v : ℝ) := by
      linarith [hlogu]
    calc (Real.log (ulcm (acH K b v)) - (acH K b v : ℝ)) * (t0:ℝ)
        ≤ (0.1 * (acH K b v : ℝ)) * (t0:ℝ) := mul_le_mul_of_nonneg_right h1 ht0nn
      _ = 0.1 * (acH K b v : ℝ) * (t0:ℝ) := by ring
      _ ≤ 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) := by
          have h3 : (0:ℝ) ≤ 0.1 * (acH K b v : ℝ) := by positivity
          nlinarith [ht0, h3]
  rw [Complex.norm_pow, Complex.norm_natCast]
  refine Real.le_exp_of_log_le ?_
  rw [Real.log_pow]
  nlinarith [hlog]

/-- The numeric factor of BW (13), assembled from the two sorry-free pieces `num13_hpart` and
`num13_xpart` of `Submission.Work.BW.num_13` (the `num_13` theorem itself is not used here: its
Hanson input `ulcm_le_three_pow` is still being completed). -/
lemma est14_num_CD {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (x : ℝ) (hx : 0 ≤ x) :
    ((Real.log (57 * (r : ℝ) * (d : ℝ)) + 2 / (57 * (r : ℝ) * (d : ℝ))) * (h : ℝ)
        + x / (57 * (r : ℝ) * (d : ℝ))) * ((pD0 r d σ : ℝ) + 1) ≤
      (0.108 * (pS r d h : ℝ) + 0.007 * x) * pD r d σ / (d : ℝ) := by
  have hpart := num13_hpart hr hd σ hσ
  have xpart := num13_xpart hr hd σ hσ
  have hh0 : (0:ℝ) ≤ (h:ℝ) := by positivity
  have hS : (pS r d h : ℝ) = 16 * (r:ℝ) * (d:ℝ) * (h:ℝ) := by
    simp only [pS]; push_cast; ring
  have h1 : (Real.log (57 * (r:ℝ) * (d:ℝ)) + 2 / (57 * (r:ℝ) * (d:ℝ))) * (h:ℝ)
        * ((pD0 r d σ : ℝ) + 1)
      ≤ 1.728 * (r:ℝ) * pD r d σ * (h:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hpart hh0
    linarith [h]
  have h2 : x / (57 * (r:ℝ) * (d:ℝ)) * ((pD0 r d σ : ℝ) + 1)
      ≤ 0.007 * x * pD r d σ / (d:ℝ) := by
    have hstep : x / (57 * (r:ℝ) * (d:ℝ)) * ((pD0 r d σ : ℝ) + 1)
        ≤ x / (57 * (r:ℝ) * (d:ℝ)) * (0.399 * ((r:ℝ) * pD r d σ)) :=
      mul_le_mul_of_nonneg_left xpart (by positivity)
    have hxe : x / (57 * (r:ℝ) * (d:ℝ)) * (0.399 * ((r:ℝ) * pD r d σ))
        = 0.007 * x * pD r d σ / (d:ℝ) := by
      field_simp
      ring
    rw [hxe] at hstep
    exact hstep
  rw [add_mul]
  have hS3 : (0.108:ℝ) * (pS r d h : ℝ) * pD r d σ / (d:ℝ)
      = 1.728 * (r:ℝ) * pD r d σ * (h:ℝ) := by
    rw [hS]; field_simp; ring
  have hRHS : (0.108 * (pS r d h : ℝ) + 0.007 * x) * pD r d σ / (d:ℝ)
      = 0.108 * (pS r d h : ℝ) * pD r d σ / (d:ℝ) + 0.007 * x * pD r d σ / (d:ℝ) := by
    ring
  rw [hRHS, hS3]
  linarith [h1, h2]

/-- The `Y₀`-part of a summand: `Θ(2^{-J}z + λ_{-1})` is at most
`exp((0·108 S + 0·007 (|z|/2^J + h))D/d)`. -/
lemma est14_aeval_le (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (t0 : ℕ) (z : ℂ)
    (ht0 : (t0 : ℝ) ≤ (pT r (dK K) σ : ℝ))
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    ‖Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ))
        (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))‖ ≤
      Real.exp ((0.108 * acS K r b v + 0.007 * (‖z‖ / 2 ^ J + (acH K b v : ℝ))) *
        acD K σ / (dK K : ℝ)) := by
  have hHn : 0 < acH K b v := by have h := (acH_lower H).1; omega
  have hh1 : 1 ≤ acH K b v := by have h := (acH_lower H).1; omega
  have hHpos : (0:ℝ) < (acH K b v : ℝ) := by exact_mod_cast hHn
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hr2' : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast H.hr
  have hdr : (0:ℝ) < (dK K : ℝ) := dK_pos_real
  have hmu : (0:ℝ) < 57 * (r : ℝ) * (dK K : ℝ) := by nlinarith [hr2', hdr]
  set w : ℂ := (((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ) with hwdef
  have hw : ‖w‖ ≤ ‖z‖ / 2 ^ J + (acH K b v : ℝ) := by
    have h1 : ‖(((2 : ℂ) ^ J)⁻¹) * z‖ = ‖z‖ / 2 ^ J := by
      rw [norm_mul, norm_inv, norm_pow, Complex.norm_two, div_eq_mul_inv]
      ring
    have h2n : (lm.1 : ℕ) ≤ acH K b v := le_of_lt lm.1.isLt
    have h2 : ((lm.1 : ℕ) : ℝ) ≤ (acH K b v : ℝ) := by exact_mod_cast h2n
    calc ‖w‖ = ‖(((2 : ℂ) ^ J)⁻¹) * z + (((lm.1 : ℕ)) : ℂ)‖ := rfl
      _ ≤ ‖(((2 : ℂ) ^ J)⁻¹) * z‖ + ‖(((lm.1 : ℕ)) : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ / 2 ^ J + ((lm.1 : ℕ) : ℝ) := by rw [h1, Complex.norm_natCast]
      _ ≤ ‖z‖ / 2 ^ J + (acH K b v : ℝ) := by linarith
  have hbase1 : (1:ℝ) ≤ Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ)) := by
    have ha : (0:ℝ) ≤ ‖w‖ / (acH K b v : ℝ) := div_nonneg (norm_nonneg w) hHpos.le
    have hb : (1:ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    have hc : (1:ℝ) ≤ 1 + ‖w‖ / (acH K b v : ℝ) := by linarith
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ)) :=
          mul_le_mul hb hc (by norm_num) (Real.exp_pos 1).le
  have hlog : Real.log ((Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ))) ^
        ((acH K b v) * (pD0 r (dK K) σ + 1))) ≤
      ((pD0 r (dK K) σ : ℝ) + 1) *
        ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 2 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ)
          + (‖z‖ / 2 ^ J + (acH K b v : ℝ)) / (57 * (r : ℝ) * (dK K : ℝ))) := by
    have hpos1 : (0:ℝ) < 1 + ‖w‖ / (acH K b v : ℝ) := by
      have ha : (0:ℝ) ≤ ‖w‖ / (acH K b v : ℝ) := div_nonneg (norm_nonneg w) hHpos.le
      linarith
    have hb : Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ)) =
        Real.exp (1 + Real.log (1 + ‖w‖ / (acH K b v : ℝ))) := by
      rw [Real.exp_add, Real.exp_log hpos1]
    rw [hb, Real.log_pow, Real.log_exp]
    have hcast : ((↑((acH K b v) * (pD0 r (dK K) σ + 1)) : ℝ)) =
        (acH K b v : ℝ) * ((pD0 r (dK K) σ : ℝ) + 1) := by push_cast; ring
    rw [hcast]
    have hopt := est14_thetaopt (mu := 57 * (r : ℝ) * (dK K : ℝ)) (h := (acH K b v : ℝ))
      (x := ‖w‖) hmu hHpos (norm_nonneg w)
    have hcomm : (acH K b v : ℝ) *
          (Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 2 / (57 * (r : ℝ) * (dK K : ℝ)))
        = (Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 2 / (57 * (r : ℝ) * (dK K : ℝ))) *
          (acH K b v : ℝ) := mul_comm _ _
    have hopt' : (acH K b v : ℝ) * (1 + Real.log (1 + ‖w‖ / (acH K b v : ℝ))) ≤
        (Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 2 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ)
          + ‖w‖ / (57 * (r : ℝ) * (dK K : ℝ)) := by linarith [hopt]
    have hstep : (acH K b v : ℝ) * (1 + Real.log (1 + ‖w‖ / (acH K b v : ℝ))) ≤
        (Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 2 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ)
          + (‖z‖ / 2 ^ J + (acH K b v : ℝ)) / (57 * (r : ℝ) * (dK K : ℝ)) := by
      have h1 : ‖w‖ / (57 * (r : ℝ) * (dK K : ℝ)) ≤
          (‖z‖ / 2 ^ J + (acH K b v : ℝ)) / (57 * (r : ℝ) * (dK K : ℝ)) :=
        div_le_div_of_nonneg_right hw hmu.le
      linarith [hopt']
    calc (acH K b v : ℝ) * ((pD0 r (dK K) σ : ℝ) + 1) *
            (1 + Real.log (1 + ‖w‖ / (acH K b v : ℝ)))
        = ((pD0 r (dK K) σ : ℝ) + 1) *
            ((acH K b v : ℝ) * (1 + Real.log (1 + ‖w‖ / (acH K b v : ℝ)))) := by ring
      _ ≤ ((pD0 r (dK K) σ : ℝ) + 1) *
            ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 2 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ)
              + (‖z‖ / 2 ^ J + (acH K b v : ℝ)) / (57 * (r : ℝ) * (dK K : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
  have hnum : ((pD0 r (dK K) σ : ℝ) + 1) *
        ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 2 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ)
          + (‖z‖ / 2 ^ J + (acH K b v : ℝ)) / (57 * (r : ℝ) * (dK K : ℝ))) ≤
      (0.108 * acS K r b v + 0.007 * (‖z‖ / 2 ^ J + (acH K b v : ℝ))) * acD K σ / (dK K : ℝ) := by
    have h := est14_num_CD (h := acH K b v) H.hr one_le_dK σ hσ
      (‖z‖ / 2 ^ J + (acH K b v : ℝ)) (by positivity)
    simpa only [acS, acD, mul_comm, mul_left_comm, mul_assoc] using h
  have hTheta : ‖Theta w (acH K b v) ((lm.2.1 : ℕ) + 1) t0‖ ≤
      (Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ))) ^ ((acH K b v) * ((lm.2.1 : ℕ) + 1)) :=
    est_Theta_yu w (acH K b v) ((lm.2.1 : ℕ) + 1) t0 hh1
  have hpow : (Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ))) ^ ((acH K b v) * ((lm.2.1 : ℕ) + 1))
      ≤ (Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ))) ^ ((acH K b v) * (pD0 r (dK K) σ + 1)) :=
    pow_le_pow_right₀ hbase1
      (Nat.mul_le_mul_left (acH K b v) (Nat.succ_le_succ (Nat.lt_succ_iff.mp lm.2.1.isLt)))
  calc ‖Polynomial.aeval w (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))‖
      = ‖Theta w (acH K b v) ((lm.2.1 : ℕ) + 1) t0‖ := rfl
    _ ≤ (Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ))) ^ ((acH K b v) * ((lm.2.1 : ℕ) + 1)) := hTheta
    _ ≤ (Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ))) ^ ((acH K b v) * (pD0 r (dK K) σ + 1)) := hpow
    _ ≤ Real.exp ((0.108 * acS K r b v + 0.007 * (‖z‖ / 2 ^ J + (acH K b v : ℝ))) *
          acD K σ / (dK K : ℝ)) := Real.le_exp_of_log_le (le_trans hlog hnum)

/-- The coefficient part `φ(p λ)·Π(t)·u(h)^{t₀}` of a summand. -/
lemma est14_coeff_le (H : ACHyp φ α b k c v L α' σ ι p) {t0 : ℕ} {t : Fin (r - 1) → ℕ}
    (ht0 : (t0 : ℝ) ≤ (pT r (dK K) σ : ℝ)) (htT : ((∑ m, t m : ℕ) : ℝ) ≤ acT K σ)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    ‖φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) *
        (ulcm (acH K b v) : ℂ) ^ t0‖ ≤
      Real.exp (lnp φ p + (acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)
        + (pT r (dK K) σ : ℝ) * Real.log 1.7 + (acH K b v : ℝ) * (t0 : ℝ)
        + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) := by
  have hlm : ∀ j, (fun i => (lm.2.2 i : ℕ)) j ≤ pDj r (dK K) σ j :=
    fun j => Nat.lt_succ_iff.mp (lm.2.2 j).isLt
  have hpi := est_Pi H (fun i => (lm.2.2 i : ℕ)) hlm t htT
  have hphi := est14_phibound φ p H.hp0 lm
  have hul := est14_ulcm_le H ht0
  have hexp17 : (1.7:ℝ) ^ (pT r (dK K) σ) =
      Real.exp ((pT r (dK K) σ : ℝ) * Real.log 1.7) := by
    conv_lhs => rw [← Real.exp_log (by norm_num : (0:ℝ) < 1.7)]
    rw [← Real.exp_nat_mul]
  rw [norm_mul, norm_mul]
  calc ‖φ (p lm)‖ * ‖∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)‖ *
        ‖(ulcm (acH K b v) : ℂ) ^ t0‖
      ≤ Real.exp (lnp φ p)
          * (Real.exp ((acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)) * (1.7:ℝ) ^ (pT r (dK K) σ))
          * Real.exp ((acH K b v : ℝ) * (t0 : ℝ) + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) := by
        exact mul_le_mul (mul_le_mul hphi hpi (norm_nonneg _) (Real.exp_pos _).le) hul
          (norm_nonneg _) (by positivity)
    _ = Real.exp (lnp φ p + (acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)
          + (pT r (dK K) σ : ℝ) * Real.log 1.7 + (acH K b v : ℝ) * (t0 : ℝ)
          + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) := by
        rw [hexp17, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

/-- The number of summands is at most `exp(0·001 h T)` (BW (11), via `num13_logN`). -/
lemma est14_count_le (H : ACHyp φ α b k c v L α' σ ι p) {t0 : ℕ}
    (ht0 : (t0 : ℝ) ≤ (pT r (dK K) σ : ℝ)) :
    ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ) ≤
      Real.exp (0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) := by
  have hlog := num13_logN H.hr one_le_dK (acH_lower H).1 σ (fun j => sigma_ge H j)
  rw [card_auxIdx]
  refine Real.le_exp_of_log_le ?_
  push_cast
  exact hlog

/-- Numeric facts: `9·2^r S D ≥ 1000` and `log 1000 ≤ 0·001 S D/d`. -/
lemma est14_num_basic (H : ACHyp φ α b k c v L α' σ ι p) :
    1000 ≤ 9 * 2 ^ r * acS K r b v * acD K σ ∧
      Real.log 1000 ≤ 0.001 * (acS K r b v * acD K σ / (dK K : ℝ)) := by
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hS : (608:ℝ) ≤ acS K r b v :=
    (num_T H.hr one_le_dK (acH_lower H).1 σ hσ).2.2.2
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast H.hr
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by linarith
  have hrr : (4:ℝ) ≤ (r:ℝ)^r := by
    calc (4:ℝ) = (2:ℝ)^2 := by norm_num
      _ ≤ (2:ℝ)^r := pow_le_pow_right₀ (by norm_num) H.hr
      _ ≤ (r:ℝ)^r := pow_le_pow_left₀ (by norm_num) hr2 r
  have h32 : (32:ℝ)^3 ≤ (32:ℝ)^(r+1) := by
    have h3 : 3 ≤ r + 1 := Nat.succ_le_succ H.hr
    exact pow_le_pow_right₀ (by norm_num) h3
  have hd : (1:ℝ) ≤ (dK K : ℝ) := by
    exact_mod_cast one_le_dK
  have hl : (1:ℝ) ≤ Real.log (2 * (r:ℝ) * (dK K : ℝ)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h4 : (4:ℝ) ≤ 2 * (r:ℝ) * (dK K : ℝ) := by
      have hdr : (0:ℝ) < (dK K : ℝ) := dK_pos_real
      nlinarith [hdr, hr1]
    linarith [Real.exp_one_lt_three]
  have hD262 : (262144:ℝ) ≤ acD K σ := by
    have h := (num_D_lower H.hr one_le_dK σ hσ).1
    have hA : (2:ℝ) * 4 ≤ 2 * (r:ℝ)^r := mul_le_mul_of_nonneg_left hrr (by norm_num)
    have hB : (2:ℝ) * 4 * 32^3 ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) :=
      mul_le_mul hA h32 (by norm_num) (by positivity)
    have hC : (2:ℝ) * 4 * 32^3 * 1 ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (dK K : ℝ) :=
      mul_le_mul hB hd (by norm_num) (by positivity)
    have hE : (2:ℝ) * 4 * 32^3 * 1 * 1 ≤
        2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (dK K : ℝ) * Real.log (2 * (r:ℝ) * (dK K : ℝ)) :=
      mul_le_mul hC hl (by norm_num) (by positivity)
    exact le_trans (le_trans (by norm_num : (262144:ℝ) ≤ 2 * 4 * 32^3 * 1 * 1) hE) h
  have hh19 : (19:ℝ) ≤ (acH K b v : ℝ) := by
    have h := (acH_lower H).1
    exact_mod_cast h
  have hprod : acS K r b v = 16 * (r:ℝ) * (dK K : ℝ) * (acH K b v : ℝ) := by
    simp only [acS, pS]; push_cast; ring
  constructor
  · have h2r : (4:ℝ) ≤ (2:ℝ)^r := by
      calc (4:ℝ) = (2:ℝ)^2 := by norm_num
        _ ≤ (2:ℝ)^r := pow_le_pow_right₀ (by norm_num) H.hr
    have hSD : (608:ℝ) * 262144 ≤ acS K r b v * acD K σ :=
      mul_le_mul hS hD262 (by norm_num) (by positivity)
    nlinarith [h2r, hSD]
  · have hbig : (1000000:ℝ) ≤ 16 * (r:ℝ) * (acH K b v : ℝ) * acD K σ := by
      have h4 : 16 * 2 * 19 * 262144 ≤ 16 * (r:ℝ) * (acH K b v : ℝ) * acD K σ := by
        have h1 : 16 * 2 ≤ 16 * (r:ℝ) := by linarith
        have h2 : 16 * 2 * 19 ≤ 16 * (r:ℝ) * (acH K b v : ℝ) :=
          mul_le_mul h1 hh19 (by norm_num) (by positivity)
        exact mul_le_mul h2 hD262 (by norm_num) (by positivity)
      linarith
    have hquot : acS K r b v * acD K σ / (dK K : ℝ) =
        16 * (r:ℝ) * (acH K b v : ℝ) * acD K σ := by
      rw [hprod, div_eq_iff (ne_of_gt dK_pos_real)]
      ring
    rw [hquot]
    have h1 : Real.log 1000 ≤ (1000:ℝ) := Real.log_le_self (by norm_num)
    linarith

/-- `Λ ≠ 0` and `‖Λ‖ ≤ 0·001` (BW (10)). -/
lemma est14_lam_small (H : ACHyp φ α b k c v L α' σ ι p) :
    lam φ α b ≠ 0 ∧ ‖lam φ α b‖ ≤ 0.001 := by
  refine ⟨est14_lam_ne_zero H, ?_⟩
  have hkey := (est14_num_basic H).1
  have hlog1000 : Real.log 1000 ≤ 9 * 2 ^ r * acS K r b v * acD K σ :=
    le_trans (Real.log_le_self (by norm_num)) hkey
  refine le_trans (est14_lambda_le H) ?_
  refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 0.001)).1 ?_
  have h1 : Real.log (0.001:ℝ) = -Real.log 1000 := by
    rw [show (0.001:ℝ) = (1000:ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [h1]
  linarith [hlog1000]

/-- `‖e^{δ_λ} - 1‖ ≤ ‖Λ‖·t·exp(0.001 t)` with `t = ‖z‖ D / 2^J` (BW (14)). -/
lemma est14_expSig_le (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (z : ℂ)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    ‖Complex.exp (estSig φ α b k v L J z lm) - 1‖ ≤
      ‖lam φ α b‖ * (‖z‖ * acD K σ / 2 ^ J) * Real.exp (0.001 * (‖z‖ * acD K σ / 2 ^ J)) := by
  have hsig := est14_sigbound H J z lm
  have hs := (est14_lam_small H).2
  have hDDnn : (0:ℝ) ≤ acD K σ := by
    have hσpos : ∀ j, 0 < σ j := by
      intro j
      have h := sigma_ge H j
      have h2 : (0:ℝ) < 1 / (dK K : ℝ) := div_pos one_pos dK_pos_real
      linarith
    have hprod : (0:ℝ) ≤ ∏ j, σ j := le_of_lt (Finset.prod_pos (fun j _ => hσpos j))
    have h1 : (0:ℝ) ≤ Real.log (2 * (r:ℝ) * (dK K : ℝ)) := by
      have hr1 : (1:ℝ) ≤ (r:ℝ) := by
        have h := H.hr
        have h2 : 1 ≤ r := by omega
        exact_mod_cast h2
      have h2 : (1:ℝ) ≤ 2 * (r:ℝ) * (dK K : ℝ) := by
        have hd1 : (1:ℝ) ≤ (dK K : ℝ) := by exact_mod_cast one_le_dK
        nlinarith [hd1, hr1]
      exact Real.log_nonneg h2
    simp only [acD, pD]
    positivity
  have h1 : ‖Complex.exp (estSig φ α b k v L J z lm) - 1‖ ≤
      ‖estSig φ α b k v L J z lm‖ * Real.exp ‖estSig φ α b k v L J z lm‖ := by
    simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp (estSig φ α b k v L J z lm) 1
  have h2 : Real.exp ‖estSig φ α b k v L J z lm‖ ≤ Real.exp (0.001 * (‖z‖ * acD K σ / 2 ^ J)) := by
    apply Real.exp_le_exp.mpr
    refine le_trans hsig ?_
    exact mul_le_mul_of_nonneg_right hs (div_nonneg (mul_nonneg (norm_nonneg z) hDDnn) (by positivity))
  calc ‖Complex.exp (estSig φ α b k v L J z lm) - 1‖
      ≤ ‖estSig φ α b k v L J z lm‖ * Real.exp ‖estSig φ α b k v L J z lm‖ := h1
    _ ≤ ‖lam φ α b‖ * (‖z‖ * acD K σ / 2 ^ J) * Real.exp (0.001 * (‖z‖ * acD K σ / 2 ^ J)) := by
        refine mul_le_mul hsig h2 (Real.exp_pos _).le ?_
        positivity


/-- The analytic bound for `log‖f^{(J)}(z) - g^{(J)}(z)‖`: the sum of all the pieces. -/
lemma est14_bound (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K))
    (μ : Fin r → ℕ) (Tst : ℝ) (hTst : Tst ≤ acT K σ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (z : ℂ) :
    ‖acf φ α b k L ι v σ p J μ t0 t z - acg φ α b k L ι v σ p J μ t0 t z‖ ≤
      Real.exp (0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)
        + lnp φ p + (acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)
        + (pT r (dK K) σ : ℝ) * Real.log 1.7 + (acH K b v : ℝ) * (t0 : ℝ)
        + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)
        + (0.108 * acS K r b v + 0.007 * (‖z‖ / 2 ^ J + (acH K b v : ℝ))) * acD K σ / (dK K : ℝ)
        + ‖z‖ * acD K σ / 2 ^ J
        - 9 * 2 ^ r * acS K r b v * acD K σ
        + 0.001 * (acS K r b v * acD K σ / (dK K : ℝ))
        + 0.002 * (‖z‖ * acD K σ / 2 ^ J)) := by
  classical
  have ht0 : (t0 : ℝ) ≤ (pT r (dK K) σ : ℝ) := by
    have h1 : ((t0 : ℕ) : ℝ) ≤ ((t0 + ∑ m, t m : ℕ) : ℝ) := by
      have h1n : t0 ≤ t0 + ∑ m, t m := Nat.le_add_right t0 (∑ m, t m)
      exact_mod_cast h1n
    have h2 : (acT K σ) = (pT r (dK K) σ : ℝ) := rfl
    linarith [ht, hTst]
  have htT : ((∑ m, t m : ℕ) : ℝ) ≤ acT K σ := by
    have h1 : ((∑ m, t m : ℕ) : ℝ) ≤ ((t0 + ∑ m, t m : ℕ) : ℝ) := by
      have h1n : (∑ m, t m) ≤ t0 + ∑ m, t m := Nat.le_add_left (∑ m, t m) t0
      exact_mod_cast h1n
    linarith [ht, hTst]
  have hDDnn : (0:ℝ) ≤ acD K σ := by
    have hσpos : ∀ j, 0 < σ j := by
      intro j
      have h := sigma_ge H j
      have h2 : (0:ℝ) < 1 / (dK K : ℝ) := div_pos one_pos dK_pos_real
      linarith
    have hprod : (0:ℝ) ≤ ∏ j, σ j := le_of_lt (Finset.prod_pos (fun j _ => hσpos j))
    have h1 : (0:ℝ) ≤ Real.log (2 * (r:ℝ) * (dK K : ℝ)) := by
      have hr1 : (1:ℝ) ≤ (r:ℝ) := by
        have h := H.hr
        have hω : 1 ≤ r := by omega
        exact_mod_cast hω
      have h2 : (1:ℝ) ≤ 2 * (r:ℝ) * (dK K : ℝ) := by
        have hd1 : (1:ℝ) ≤ (dK K : ℝ) := by exact_mod_cast one_le_dK
        nlinarith [hd1, hr1]
      exact Real.log_nonneg h2
    simp only [acD, pD]
    positivity
  set A1 : ℝ := lnp φ p + (acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)
      + (pT r (dK K) σ : ℝ) * Real.log 1.7 + (acH K b v : ℝ) * (t0 : ℝ)
      + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) with hA1
  set A2 : ℝ := (0.108 * acS K r b v + 0.007 * (‖z‖ / 2 ^ J + (acH K b v : ℝ))) *
      acD K σ / (dK K : ℝ) with hA2
  set A3 : ℝ := ‖z‖ * acD K σ / 2 ^ J with hA3
  have hterm : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
      ‖estGT φ b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J t0 t
        (fun j => lamP φ α v L j) z lm‖ ≤ Real.exp (A1 + A2 + A3) := by
    intro lm
    have h1 : ‖φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) *
        (ulcm (acH K b v) : ℂ) ^ t0‖ ≤ Real.exp A1 := by
      rw [hA1]; exact est14_coeff_le H ht0 htT lm
    have h2 : ‖Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ))
        (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))‖ ≤ Real.exp A2 := by
      rw [hA2]; exact est14_aeval_le H J t0 z ht0 lm
    have h3 : ‖estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))‖ ≤ Real.exp A3 := by
      rw [hA3]; exact est14_torusbound H J z lm
    have hsplit : estGT φ b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J t0 t
          (fun j => lamP φ α v L j) z lm =
        (φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) *
            (ulcm (acH K b v) : ℂ) ^ t0) *
          Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ))
            (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1))) *
          estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ)) := rfl
    rw [hsplit, norm_mul, norm_mul]
    refine le_trans (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le) h3
      (norm_nonneg _) (by positivity)) (le_of_eq ?_)
    simp only [← Real.exp_add]
  have hsigeq : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
      ‖Complex.exp (estSig φ α b k v L J z lm) - 1‖ ≤
        ‖lam φ α b‖ * (‖z‖ * acD K σ / 2 ^ J) *
          Real.exp (0.001 * (‖z‖ * acD K σ / 2 ^ J)) := fun lm => est14_expSig_le H J z lm
  have hnn : (0:ℝ) ≤ ‖lam φ α b‖ * (‖z‖ * acD K σ / 2 ^ J) *
      Real.exp (0.001 * (‖z‖ * acD K σ / 2 ^ J)) := by
    refine mul_nonneg (mul_nonneg (norm_nonneg _) ?_) (Real.exp_pos _).le
    exact div_nonneg (mul_nonneg (norm_nonneg _) hDDnn) (by positivity)
  have hsum : ‖acf φ α b k L ι v σ p J μ t0 t z - acg φ α b k L ι v σ p J μ t0 t z‖ ≤
      ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ) *
        Real.exp (A1 + A2 + A3) *
        (‖lam φ α b‖ * (‖z‖ * acD K σ / 2 ^ J) *
          Real.exp (0.001 * (‖z‖ * acD K σ / 2 ^ J))) := by
    rw [acf_sub_acg_eq_sum]
    refine le_trans (norm_sum_le _ _) ?_
    have hpoint : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
        ‖(if estCond J μ lm then
            estCoeff φ b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J t0 t z lm *
              estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ)) *
              (Complex.exp (estSig φ α b k v L J z lm) - 1)
          else 0)‖ ≤ Real.exp (A1 + A2 + A3) *
          (‖lam φ α b‖ * (‖z‖ * acD K σ / 2 ^ J) *
            Real.exp (0.001 * (‖z‖ * acD K σ / 2 ^ J))) := by
      intro lm
      by_cases hc : estCond J μ lm
      · rw [if_pos hc]
        have hsplit : estCoeff φ b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J t0 t z lm *
              estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ)) *
              (Complex.exp (estSig φ α b k v L J z lm) - 1) =
            estGT φ b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J t0 t
              (fun j => lamP φ α v L j) z lm *
              (Complex.exp (estSig φ α b k v L J z lm) - 1) := rfl
        rw [hsplit, norm_mul]
        exact mul_le_mul (hterm lm) (hsigeq lm) (norm_nonneg _) (Real.exp_pos _).le
      · rw [if_neg hc, norm_zero]
        exact mul_nonneg (Real.exp_pos _).le hnn
    refine le_trans (Finset.sum_le_sum (fun lm _ => hpoint lm)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact le_of_eq (by ring)
  have hNle : ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ) ≤
      Real.exp (0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) := est14_count_le H ht0
  have hLamle : ‖lam φ α b‖ ≤ Real.exp (-(9 * 2 ^ r * acS K r b v * acD K σ)) :=
    est14_lambda_le H
  have hlog1000 : Real.log 1000 ≤ 0.001 * (acS K r b v * acD K σ / (dK K : ℝ)) :=
    (est14_num_basic H).2
  have htle : ‖z‖ * acD K σ / 2 ^ J ≤
      Real.exp (0.001 * (acS K r b v * acD K σ / (dK K : ℝ)) + 0.001 * (‖z‖ * acD K σ / 2 ^ J)) :=
    est14_log_bound (div_nonneg (mul_nonneg (norm_nonneg z) hDDnn) (by positivity)) hlog1000
  calc ‖acf φ α b k L ι v σ p J μ t0 t z - acg φ α b k L ι v σ p J μ t0 t z‖
      ≤ ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ) *
          Real.exp (A1 + A2 + A3) *
          (‖lam φ α b‖ * (‖z‖ * acD K σ / 2 ^ J) *
            Real.exp (0.001 * (‖z‖ * acD K σ / 2 ^ J))) := hsum
    _ ≤ Real.exp (0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) * Real.exp (A1 + A2 + A3) *
          (Real.exp (-(9 * 2 ^ r * acS K r b v * acD K σ)) *
            Real.exp (0.001 * (acS K r b v * acD K σ / (dK K : ℝ)) +
              0.001 * (‖z‖ * acD K σ / 2 ^ J)) *
            Real.exp (0.001 * (‖z‖ * acD K σ / 2 ^ J))) := by
        refine mul_le_mul (mul_le_mul hNle (le_refl _) (Real.exp_pos _).le (Real.exp_pos _).le) ?_
          hnn (by positivity)
        refine mul_le_mul (mul_le_mul hLamle htle (by positivity) (by positivity)) (le_refl _)
          (Real.exp_pos _).le (by positivity)
    _ = Real.exp (0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) + (A1 + A2 + A3)
          + (-(9 * 2 ^ r * acS K r b v * acD K σ))
          + (0.001 * (acS K r b v * acD K σ / (dK K : ℝ)) + 0.001 * (‖z‖ * acD K σ / 2 ^ J))
          + 0.001 * (‖z‖ * acD K σ / 2 ^ J)) := by
        simp only [← Real.exp_add]
        exact congrArg Real.exp (by ring)
    _ ≤ Real.exp (0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)
        + lnp φ p + (acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)
        + (pT r (dK K) σ : ℝ) * Real.log 1.7 + (acH K b v : ℝ) * (t0 : ℝ)
        + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)
        + (0.108 * acS K r b v + 0.007 * (‖z‖ / 2 ^ J + (acH K b v : ℝ))) * acD K σ / (dK K : ℝ)
        + ‖z‖ * acD K σ / 2 ^ J
        - 9 * 2 ^ r * acS K r b v * acD K σ
        + 0.001 * (acS K r b v * acD K σ / (dK K : ℝ))
        + 0.002 * (‖z‖ * acD K σ / 2 ^ J)) := by
        apply Real.exp_le_exp.mpr
        rw [hA1, hA2, hA3]
        first | (exact le_of_eq rfl) | (exact le_of_eq (by ring)) | ring_nf | linarith

/-- **BW (14) at level `J`.** -/
theorem est14 {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K)) (μ : Fin r → ℕ) (Tst : ℝ) (hTst : Tst ≤ acT K σ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (z : ℂ) :
    ‖acf φ α b k L ι v σ p J μ t0 t z - acg φ α b k L ι v σ p J μ t0 t z‖ ≤
      Real.exp (lnp φ p + (acH K b v : ℝ) * Tst +
        (0.205 * (1 / (dK K : ℝ)) + 1.01 * (‖z‖ / 2 ^ J) / acS K r b v - 9 * 2 ^ r) * acS K r b v * acD K σ) := by
  refine le_trans (est14_bound H J hJ μ Tst hTst t0 t ht z) ?_
  apply Real.exp_le_exp.mpr
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hh19n : 19 ≤ acH K b v := (acH_lower H).1
  have hh19 : (0:ℝ) ≤ (acH K b v : ℝ) := by
    have h : 0 ≤ acH K b v := le_trans (by norm_num : (0:ℕ) ≤ 19) hh19n
    exact_mod_cast h
  have ht0 : (t0 : ℝ) ≤ (pT r (dK K) σ : ℝ) := by
    have h1 : ((t0 : ℕ) : ℝ) ≤ ((t0 + ∑ m, t m : ℕ) : ℝ) := by
      have h1n : t0 ≤ t0 + ∑ m, t m := Nat.le_add_right t0 (∑ m, t m)
      exact_mod_cast h1n
    linarith [ht, hTst, h1, (rfl : (acT K σ) = (pT r (dK K) σ : ℝ))]
  have hlog17 : Real.log 1.7 ≤ 0.028 * (acH K b v : ℝ) := by
    have h1 := num13_log_17_lt
    have h19 : (19:ℝ) ≤ (acH K b v : ℝ) := by exact_mod_cast hh19n
    linarith
  have hnumT3 : (dK K : ℝ) * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) ≤
      0.735 * acS K r b v * acD K σ := (num_T H.hr one_le_dK hh19n σ hσ).2.2.1
  have hd : (0:ℝ) < (dK K : ℝ) := dK_pos_real
  have hσpos : ∀ j, 0 < σ j := by
    intro j
    have h := hσ j
    have h2 : (0:ℝ) < 1 / (dK K : ℝ) := div_pos one_pos dK_pos_real
    linarith
  have hDDpos : (0:ℝ) < acD K σ := by
    have hprod : (0:ℝ) < ∏ j, σ j := Finset.prod_pos (fun j _ => hσpos j)
    have hlog : (0:ℝ) < Real.log (2 * (r:ℝ) * (dK K : ℝ)) := by
      rw [Real.log_pos_iff (by positivity)]
      have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast H.hr
      have hd1 : (1:ℝ) ≤ (dK K : ℝ) := by exact_mod_cast one_le_dK
      nlinarith [hd1, hr2]
    have h2 : (0:ℝ) < 2 := by norm_num
    have hr0 : (0:ℝ) < (r:ℝ) := by
      have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast H.hr
      linarith
    have hrr : (0:ℝ) < (r:ℝ)^r := by positivity
    have h32 : (0:ℝ) < (32 * (dK K : ℝ))^(r+1) := by positivity
    simp only [acD, pD]
    exact mul_pos (mul_pos (mul_pos (mul_pos h2 hrr) h32) hlog) hprod
  have hSpos : (0:ℝ) < acS K r b v := by
    have h1 : 0 < acH K b v := lt_of_lt_of_le (by norm_num : (0:ℕ) < 19) hh19n
    have hr0 : 0 < r := by
      have h := H.hr; omega
    have hd0 : 0 < dK K := lt_of_lt_of_le Nat.zero_lt_one one_le_dK
    have h2 : 0 < 16 * r * dK K * acH K b v := by positivity
    rw [acS, pS]
    exact_mod_cast h2
  have hPhT : (acH K b v : ℝ) * (((∑ m, t m : ℕ) : ℝ) + (t0 : ℝ)) ≤ (acH K b v : ℝ) * Tst := by
    have ht' : ((∑ m, t m : ℕ) : ℝ) + (t0 : ℝ) ≤ Tst := by
      have h1 := ht
      rw [show ((t0 + ∑ m, t m : ℕ) : ℝ) = (t0 : ℝ) + ((∑ m, t m : ℕ) : ℝ) from by push_cast; ring] at h1
      linarith
    exact mul_le_mul_of_nonneg_left ht' hh19
  have hhP : (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) ≤
      0.735 * (acS K r b v * acD K σ / (dK K : ℝ)) := by
    have heq : 0.735 * (acS K r b v * acD K σ / (dK K : ℝ)) =
        0.735 * (acS K r b v * acD K σ) / (dK K : ℝ) := by ring
    rw [heq, le_div_iff₀ hd]
    linarith [hnumT3]
  have hp17 : (pT r (dK K) σ : ℝ) * Real.log 1.7 ≤
      0.02058 * (acS K r b v * acD K σ / (dK K : ℝ)) := by
    have hP0 : (0:ℝ) ≤ (pT r (dK K) σ : ℝ) := by positivity
    have h2 := mul_le_mul_of_nonneg_left hlog17 hP0
    have h3 := mul_le_mul_of_nonneg_left hhP (by norm_num : (0:ℝ) ≤ 0.028)
    linarith [h2, h3]
  have h01 : 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) ≤
      0.0735 * (acS K r b v * acD K σ / (dK K : ℝ)) := by
    have h3 := mul_le_mul_of_nonneg_left hhP (by norm_num : (0:ℝ) ≤ 0.1)
    linarith [h3]
  have h001 : 0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) ≤
      0.000735 * (acS K r b v * acD K σ / (dK K : ℝ)) := by
    have h3 := mul_le_mul_of_nonneg_left hhP (by norm_num : (0:ℝ) ≤ 0.001)
    linarith [h3]
  have hS_eq : acS K r b v = 16 * (r:ℝ) * (dK K : ℝ) * (acH K b v : ℝ) := by
    simp only [acS, pS]; push_cast; ring
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast H.hr
  have h007h : 0.007 * (acH K b v : ℝ) * (acD K σ / (dK K : ℝ)) ≤
      0.001185 * (acS K r b v * acD K σ / (dK K : ℝ)) := by
    have hdinv : (dK K : ℝ) * ((dK K : ℝ))⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hd)
    have hDD0 : (0:ℝ) ≤ acD K σ := le_of_lt hDDpos
    have hdinv0 : (0:ℝ) ≤ ((dK K : ℝ))⁻¹ := (inv_pos.mpr hd).le
    have hd1 : (1:ℝ) ≤ (dK K : ℝ) := by exact_mod_cast one_le_dK
    rw [div_eq_mul_inv, div_eq_mul_inv, hS_eq]
    have hfac : 0.001185 * (16 * (r:ℝ) * (dK K : ℝ) * (acH K b v : ℝ) * acD K σ * ((dK K : ℝ))⁻¹)
        = 0.001185 * (16 * (r:ℝ) * (dK K : ℝ)) *
          ((acH K b v : ℝ) * (acD K σ * ((dK K : ℝ))⁻¹)) := by ring
    have hfac2 : 0.007 * (acH K b v : ℝ) * (acD K σ * ((dK K : ℝ))⁻¹)
        = 0.007 * ((acH K b v : ℝ) * (acD K σ * ((dK K : ℝ))⁻¹)) := by ring
    rw [hfac, hfac2]
    have hmono : (0:ℝ) ≤ (acH K b v : ℝ) * (acD K σ * ((dK K : ℝ))⁻¹) :=
      mul_nonneg hh19 (mul_nonneg hDD0 hdinv0)
    have hc : (0.007:ℝ) ≤ 0.001185 * (16 * (r:ℝ) * (dK K : ℝ)) := by nlinarith [hr2, hd1]
    nlinarith [hmono, hc]
  have hQ : (‖z‖ / 2 ^ J) * (acD K σ / (dK K : ℝ)) ≤ (‖z‖ / 2 ^ J) * acD K σ := by
    have hZ0 : (0:ℝ) ≤ ‖z‖ / 2 ^ J := div_nonneg (norm_nonneg z) (by positivity)
    rw [← mul_div_assoc]
    exact div_le_self (mul_nonneg hZ0 hDDpos.le) (by exact_mod_cast one_le_dK)
  have hZ0 : (0:ℝ) ≤ (‖z‖ / 2 ^ J) * acD K σ :=
    mul_nonneg (div_nonneg (norm_nonneg z) (by positivity)) hDDpos.le
  have hTsum : ((∑ m, t m : ℕ) : ℝ) + (t0 : ℝ) ≤ Tst := by
    have h2 : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst := ht
    have h3 : ((t0 + ∑ m, t m : ℕ) : ℝ) = ((∑ m, t m : ℕ) : ℝ) + (t0 : ℝ) := by push_cast; ring
    rwa [h3] at h2
  have hmain := est14_arith (SD := acS K r b v * acD K σ / (dK K : ℝ))
    (v := acD K σ / (dK K : ℝ))
    (Q := (‖z‖ / 2 ^ J) * (acD K σ / (dK K : ℝ)))
    (u := (‖z‖ / 2 ^ J) * acD K σ)
    (T' := ((∑ m, t m : ℕ) : ℝ)) (t0 := (t0 : ℝ)) (Tst := Tst)
    (P := (pT r (dK K) σ : ℝ)) (L := Real.log 1.7) (h := (acH K b v : ℝ))
    hh19 hZ0 hQ hTsum hp17 h01 h001 h007h
  have hexpand : (0.205 * (1 / (dK K : ℝ)) + 1.01 * (‖z‖ / 2 ^ J) / acS K r b v - 9 * 2 ^ r) *
        acS K r b v * acD K σ
      = 0.205 * (acS K r b v * acD K σ / (dK K : ℝ)) + 1.01 * ((‖z‖ / 2 ^ J) * acD K σ)
        - 9 * 2 ^ r * acS K r b v * acD K σ := by
    have hSne : acS K r b v ≠ 0 := ne_of_gt hSpos
    have hdne : (dK K : ℝ) ≠ 0 := ne_of_gt hd
    field_simp
  have hexpA : (0.108 * acS K r b v + 0.007 * (‖z‖ / 2 ^ J + (acH K b v : ℝ))) * acD K σ / (dK K : ℝ)
      = 0.108 * (acS K r b v * acD K σ / (dK K : ℝ))
        + 0.007 * (‖z‖ / 2 ^ J) * (acD K σ / (dK K : ℝ))
        + 0.007 * (acH K b v : ℝ) * (acD K σ / (dK K : ℝ)) := by ring
  have hZ2 : ‖z‖ * acD K σ / 2 ^ J = (‖z‖ / 2 ^ J) * acD K σ := by ring
  rw [hexpand, hexpA, hZ2]
  linarith [hmain]

end Bounds

end Work.BW
