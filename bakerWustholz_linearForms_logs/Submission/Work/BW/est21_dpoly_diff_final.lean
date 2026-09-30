import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est21_dpbA_coeff_le
import Submission.Work.BW.est21_dpbB_aeval_le
import Submission.Work.BW.est21_dpbC_count_le
import Submission.Work.BW.est21_dpbD_expSig_le
import Submission.Work.BW.est21_dpbE_diff
import Submission.Work.BW.est21_dpb_arith
import Submission.Work.BW.est21_dpn_eigfac
import Submission.Work.BW.est14_defs
import Submission.Work.BW.est14_torusbound
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

namespace Work.BW

open MvPolynomial

/-- BW (1993) p. 49, the normalised `0.255` estimate for the derivative polynomials over BW's `n`
operators `∂*_i = eulerDer (derVec b k L i ·)` — the same statement as
`Submission.Work.BW.est21_dpoly_diff_bound` (already proved) and
`Submission.Work.BW.est21_dpoly_diff_norm`, restated in a module that builds: those modules'
closures contain `Submission.Work.BW.est13`, which does not compile (its `two_pow_le_syl` collides
with `log_ulcm_le`'s public copy of the same name), so the live `est21_l` assembly cannot import
them.  A port can copy `est21_dpoly_diff_bound.lean` verbatim, replacing `import
Submission.Work.BW.est13` (directly or through its helpers `est21_dpb_clean`, `est21_dpb_diff`,
`est21_dpb_arith`, `est21_dpb_pt`, `est21_dpn_term`) by `Submission.Work.BW.est13_clean` (same
statement) and `import Submission.Work.BW.est21_l_vanish_n` by
`Submission.Work.BW.est21_l_vanish_n_red` (same statement, helpers named `fAt_sum_red`,
`fAt_smul_red`), inlining any helper that cannot be imported as such. -/
theorem est21_dpoly_diff_final {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K)) (μ : Fin r → ℕ) (Tst : ℝ)
    (hTst : Tst ≤ acT K σ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (a : ℕ) (t' : Fin n → ℕ)
    (hord : ((t0 + a + ∑ i, t' i + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (z : ℂ) :
    ‖((a.factorial : ℂ))⁻¹ *
        (∏ i, (((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (t' i) /
          ((t' i).factorial : ℂ)) *
        (fAt (ellM φ α b k v L)
            (applyDer (fun i j => (derVec b k L i j : ℚ)) a t' (QJ φ b k L ι v σ p J μ t0 t)) z
          - fAt (fun j => lamP φ α v L j)
            (applyDer (fun i j => (derVec b k L i j : ℚ)) a t' (QJ φ b k L ι v σ p J μ t0 t)) z)‖
      ≤ Real.exp (lnp φ p + (acH K b v : ℝ) * Tst +
          (0.255 * (1 / (dK K : ℝ)) + 1.01 * ((‖z‖ / 2 ^ J) / acS K r b v) - 9 * 2 ^ r) *
            acS K r b v * acD K σ) := by
  classical
  -- ## 0. basic positivity / order facts
  have hd1 : 1 ≤ dK K := by
    have h : 0 < Module.finrank ℚ K := Module.finrank_pos (R := ℚ) (M := K)
    show 1 ≤ Module.finrank ℚ K
    omega
  have hdR : (0 : ℝ) < (dK K : ℝ) := by
    have : (0:ℕ) < dK K := lt_of_lt_of_le Nat.zero_lt_one hd1
    exact_mod_cast this
  have hr2 : 2 ≤ r := H.hr
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have hh19 : 19 ≤ acH K b v := (acH_lower H).1
  have hh1 : 1 ≤ acH K b v := by omega
  have hhR : (0 : ℝ) < (acH K b v : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh1)
  have h5n : 5 * n ≤ acH K b v := (acH_lower H).2
  have hσ : ∀ j : Fin r, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hσpos : ∀ j : Fin r, (0:ℝ) < σ j := fun j =>
    lt_of_lt_of_le (one_div_pos.mpr hdR) (hσ j)
  have hDpos : (0:ℝ) < acD K σ := by
    have hprod : (0:ℝ) < ∏ j : Fin r, σ j := Finset.prod_pos (fun j _ => hσpos j)
    have hd1R : (1:ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd1
    have h2rd : (0:ℝ) < Real.log (2 * (r:ℝ) * (dK K : ℝ)) := by
      rw [Real.log_pos_iff (by positivity)]
      nlinarith [hrR, hd1R]
    simp only [acD, pD]
    positivity
  have hSpos : (0:ℝ) < acS K r b v := by
    simp only [acS, pS]
    have h : (0:ℕ) < 16 * r * dK K * acH K b v := by
      have h1 : 0 < r := by omega
      have h2 : 0 < dK K := by omega
      have h3 : 0 < acH K b v := by omega
      positivity
    exact_mod_cast h
  have hSne : acS K r b v ≠ 0 := ne_of_gt hSpos
  -- order facts
  have hTst' : Tst ≤ (pT r (dK K) σ : ℝ) := hTst
  have hord' : ((t0 + ∑ i, t' i + ∑ m, t m : ℕ) : ℝ) ≤ Tst := by
    have h1 : t0 + ∑ i, t' i + ∑ m, t m ≤ t0 + a + ∑ i, t' i + ∑ m, t m := by omega
    have h2 : ((t0 + ∑ i, t' i + ∑ m, t m : ℕ) : ℝ)
        ≤ ((t0 + a + ∑ i, t' i + ∑ m, t m : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have ht0T : (t0 : ℝ) ≤ (pT r (dK K) σ : ℝ) := by
    have h1 : t0 ≤ t0 + ∑ i, t' i + ∑ m, t m := by omega
    have h2 : ((t0 : ℕ) : ℝ) ≤ ((t0 + ∑ i, t' i + ∑ m, t m : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have htT : ((∑ m, t m : ℕ) : ℝ) ≤ acT K σ := by
    have h1 : (∑ m, t m) ≤ t0 + ∑ i, t' i + ∑ m, t m := by omega
    have h2 : (((∑ m, t m) : ℕ) : ℝ) ≤ ((t0 + ∑ i, t' i + ∑ m, t m : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h3 : Tst ≤ acT K σ := hTst
    linarith
  have hat0T : ((a + t0 : ℕ) : ℝ) ≤ (pT r (dK K) σ : ℝ) := by
    have h1 : a + t0 ≤ t0 + a + ∑ i, t' i + ∑ m, t m := by omega
    have h2 : ((a + t0 : ℕ) : ℝ) ≤ ((t0 + a + ∑ i, t' i + ∑ m, t m : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith
  have hat0Tn : a + t0 ≤ pT r (dK K) σ := by
    exact_mod_cast hat0T
  -- ## the product-bound exponent
  set BIG : ℝ := (acH K b v : ℝ) * ((∑ i, t' i : ℕ) : ℝ) + (n : ℝ) * Real.exp 1 * acD K σ
      + Real.log 2 * (pT r (dK K) σ : ℝ)
      + (lnp φ p + (acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)
          + (pT r (dK K) σ : ℝ) * Real.log 1.7 + (acH K b v : ℝ) * (t0 : ℝ)
          + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ))
      + (0.108 * acS K r b v + 0.007 * (‖z‖ / 2 ^ J + (acH K b v : ℝ))) * acD K σ / (dK K : ℝ)
      + (‖z‖ / 2 ^ J) * acD K σ
      + (0.001 * (acS K r b v * acD K σ / (dK K : ℝ)) + 0.002 * ((‖z‖ / 2 ^ J) * acD K σ)
          - 9 * 2 ^ r * acS K r b v * acD K σ) with hBIG
  -- ## the per-summand bound
  have hterm : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
      ‖((a.factorial : ℂ))⁻¹ *
        (∏ i, (((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (t' i) /
          ((t' i).factorial : ℂ)) *
        (if estCond J μ lm then
            (φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
              * (ulcm (acH K b v) : ℂ) ^ t0
              * (∏ i, (gam b k L i (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (t' i))
              * (((a.factorial : ℂ)) * (((2 : ℂ) ^ J)⁻¹) ^ a
                  * ((Nat.choose (a + t0) a : ℕ) : ℂ)))
              * Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ))
                  (Polynomial.hasseDeriv (a + t0) (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))
              * estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))
              * (Complex.exp (estSig φ α b k v L J z lm) - 1)
          else 0)‖ ≤ Real.exp BIG := by
    intro lm
    by_cases hc : estCond J μ lm
    · rw [if_pos hc]
      have hlm_le : ∀ j, (lm.2.2 j : ℕ) ≤ pDj r (dK K) σ j :=
        fun j => Nat.lt_succ_iff.mp (lm.2.2 j).isLt
      have b1 : ‖∏ i, ((((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (t' i) /
            ((t' i).factorial : ℂ)
            * (gam b k L i (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (t' i))‖
          ≤ Real.exp ((acH K b v : ℝ) * ((∑ i, t' i : ℕ) : ℝ)
              + (n : ℝ) * Real.exp 1 * acD K σ) :=
        est21_dpn_eigfac H (fun j => (lm.2.2 j : ℕ) / 2 ^ J)
          (fun j => le_trans (Nat.div_le_self _ _) (hlm_le j)) t'
      have b2 : ‖(((2 : ℂ) ^ J)⁻¹) ^ a * ((Nat.choose (a + t0) a : ℕ) : ℂ)‖
          ≤ Real.exp (Real.log 2 * (pT r (dK K) σ : ℝ)) := by
        rw [norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_ofNat, Complex.norm_natCast]
        have hle1 : (((2:ℝ) ^ J)⁻¹) ^ a ≤ 1 := by
          rw [inv_pow]
          apply inv_le_one_of_one_le₀
          exact one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
        have hch : ((Nat.choose (a + t0) a : ℕ) : ℝ) ≤ (2:ℝ) ^ (a + t0) := by
          exact_mod_cast (Nat.choose_le_two_pow (a + t0) a)
        have h2T : (2:ℝ) ^ (a + t0) ≤ (2:ℝ) ^ (pT r (dK K) σ) :=
          pow_le_pow_right₀ (by norm_num) hat0Tn
        calc (((2:ℝ) ^ J)⁻¹) ^ a * ((Nat.choose (a + t0) a : ℕ) : ℝ)
            ≤ 1 * (2:ℝ) ^ (a + t0) :=
              mul_le_mul hle1 hch (Nat.cast_nonneg _) (by norm_num)
          _ = (2:ℝ) ^ (a + t0) := one_mul _
          _ ≤ (2:ℝ) ^ (pT r (dK K) σ) := h2T
          _ = Real.exp (Real.log 2 * (pT r (dK K) σ : ℝ)) := by
              rw [← Real.rpow_natCast (2:ℝ) (pT r (dK K) σ),
                Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      have b3 : ‖φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
            * (ulcm (acH K b v) : ℂ) ^ t0‖
          ≤ Real.exp (lnp φ p + (acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)
              + (pT r (dK K) σ : ℝ) * Real.log 1.7 + (acH K b v : ℝ) * (t0 : ℝ)
              + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) :=
        est21_dpbA_coeff_le H ht0T htT lm
      have b4 : ‖Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ))
            (Polynomial.hasseDeriv (a + t0) (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))‖
          ≤ Real.exp ((0.108 * acS K r b v + 0.007 * (‖z‖ / 2 ^ J + (acH K b v : ℝ)))
              * acD K σ / (dK K : ℝ)) :=
        est21_dpbB_aeval_le H J (a + t0) z hat0T lm
      have b5 : ‖estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))‖
          ≤ Real.exp ((‖z‖ / 2 ^ J) * acD K σ) := by
        have h := est14_torusbound H J z lm
        rwa [show ‖z‖ * acD K σ / 2 ^ J = (‖z‖ / 2 ^ J) * acD K σ from by ring] at h
      have b6 : ‖Complex.exp (estSig φ α b k v L J z lm) - 1‖
          ≤ Real.exp (0.001 * (acS K r b v * acD K σ / (dK K : ℝ))
              + 0.002 * ((‖z‖ / 2 ^ J) * acD K σ) - 9 * 2 ^ r * acS K r b v * acD K σ) := by
        have hXDnn : (0:ℝ) ≤ (‖z‖ / 2 ^ J) * acD K σ :=
          mul_nonneg (div_nonneg (norm_nonneg z) (by positivity)) hDpos.le
        have hlog1000 : Real.log 1000
            ≤ 0.001 * (acS K r b v * acD K σ / (dK K : ℝ)) := (est21_dpbD_num_basic H).2
        have hXDle : (‖z‖ / 2 ^ J) * acD K σ
            ≤ Real.exp (0.001 * (acS K r b v * acD K σ / (dK K : ℝ))
                + 0.001 * ((‖z‖ / 2 ^ J) * acD K σ)) :=
          est21_dpbD_log_bound hXDnn hlog1000
        have hsig := est21_dpbD_expSig_le H J z lm
        rw [show ‖z‖ * acD K σ / 2 ^ J = (‖z‖ / 2 ^ J) * acD K σ from by ring] at hsig
        calc ‖Complex.exp (estSig φ α b k v L J z lm) - 1‖
            ≤ ‖lam φ α b‖ * ((‖z‖ / 2 ^ J) * acD K σ)
                * Real.exp (0.001 * ((‖z‖ / 2 ^ J) * acD K σ)) := hsig
          _ ≤ Real.exp (-(9 * 2 ^ r * acS K r b v * acD K σ))
                * Real.exp (0.001 * (acS K r b v * acD K σ / (dK K : ℝ))
                    + 0.001 * ((‖z‖ / 2 ^ J) * acD K σ))
                * Real.exp (0.001 * ((‖z‖ / 2 ^ J) * acD K σ)) :=
              mul_le_mul (mul_le_mul (est21_dpbD_lambda_le H) hXDle hXDnn (Real.exp_pos _).le)
                (le_refl _) (Real.exp_pos _).le (by positivity)
          _ = Real.exp (0.001 * (acS K r b v * acD K σ / (dK K : ℝ))
                + 0.002 * ((‖z‖ / 2 ^ J) * acD K σ) - 9 * 2 ^ r * acS K r b v * acD K σ) := by
              rw [← Real.exp_add, ← Real.exp_add]
              congr 1
              ring
      have hfac : ((a.factorial : ℂ))⁻¹ *
            (∏ i, (((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (t' i)
              / ((t' i).factorial : ℂ)) *
            (φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
              * (ulcm (acH K b v) : ℂ) ^ t0
              * (∏ i, (gam b k L i (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (t' i))
              * (((a.factorial : ℂ)) * (((2 : ℂ) ^ J)⁻¹) ^ a
                  * ((Nat.choose (a + t0) a : ℕ) : ℂ))
              * Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ))
                  (Polynomial.hasseDeriv (a + t0) (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))
              * estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))
              * (Complex.exp (estSig φ α b k v L J z lm) - 1))
          = (∏ i, ((((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (t' i)
                / ((t' i).factorial : ℂ)
                * (gam b k L i (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (t' i)))
            * ((((2 : ℂ) ^ J)⁻¹) ^ a * ((Nat.choose (a + t0) a : ℕ) : ℂ))
            * (φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
                * (ulcm (acH K b v) : ℂ) ^ t0)
            * Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ))
                (Polynomial.hasseDeriv (a + t0) (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))
            * estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))
            * (Complex.exp (estSig φ α b k v L J z lm) - 1) := by
        have ha0 : ((a.factorial : ℂ)) ≠ 0 := by
          exact_mod_cast (Nat.factorial_ne_zero a)
        rw [Finset.prod_mul_distrib]
        first
          | (field_simp [ha0]; ring)
          | field_simp [ha0]
      rw [hfac, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
      refine le_trans (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul b1 b2
          (norm_nonneg _) (by positivity)) b3 (norm_nonneg _) (by positivity)) b4
          (norm_nonneg _) (by positivity)) b5 (norm_nonneg _) (by positivity)) b6
          (norm_nonneg _) (by positivity)) (le_of_eq ?_)
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    · rw [if_neg hc, mul_zero, norm_zero]
      exact (Real.exp_pos BIG).le
  -- ## assemble
  rw [est21_dpbE_diff (J := J) (μ := μ) (t0 := t0) (t := t) (a := a) (t' := t') (z := z)]
  rw [Finset.mul_sum]
  refine le_trans (norm_sum_le _ _) ?_
  have hcard : (∑ _lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ), Real.exp BIG)
      = ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ)
        * Real.exp BIG := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc (∑ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
        ‖((a.factorial : ℂ))⁻¹ *
        (∏ i, (((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (t' i) /
          ((t' i).factorial : ℂ)) *
        (if estCond J μ lm then
            (φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
              * (ulcm (acH K b v) : ℂ) ^ t0
              * (∏ i, (gam b k L i (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (t' i))
              * (((a.factorial : ℂ)) * (((2 : ℂ) ^ J)⁻¹) ^ a
                  * ((Nat.choose (a + t0) a : ℕ) : ℂ)))
              * Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ))
                  (Polynomial.hasseDeriv (a + t0) (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))
              * estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ))
              * (Complex.exp (estSig φ α b k v L J z lm) - 1)
          else 0)‖)
      ≤ ∑ _lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ), Real.exp BIG :=
        Finset.sum_le_sum (fun lm _ => hterm lm)
    _ = ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ)
          * Real.exp BIG := hcard
    _ ≤ Real.exp (0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) * Real.exp BIG :=
        mul_le_mul_of_nonneg_right (est21_dpbC_count_le H (t0 := 0) (by rw [Nat.cast_zero]; exact Nat.cast_nonneg _))
          (Real.exp_pos _).le
    _ = Real.exp (0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) + BIG) :=
        (Real.exp_add _ _).symm
    _ ≤ Real.exp (lnp φ p + (acH K b v : ℝ) * Tst +
          (0.255 * (1 / (dK K : ℝ)) + 1.01 * ((‖z‖ / 2 ^ J) / acS K r b v) - 9 * 2 ^ r) *
            acS K r b v * acD K σ) := by
        apply Real.exp_le_exp.mpr
        have harith := est21_dpb_arith (K := K) (n := n) (r := r) (b := b) (v := v)
          (σ := σ) hr2 hh19 h5n hσ (X := ‖z‖ / 2 ^ J)
          (div_nonneg (norm_nonneg z) (by positivity))
        have hkeyc : (acH K b v : ℝ) * ((∑ i, t' i : ℕ) : ℝ)
              + (acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ) + (acH K b v : ℝ) * (t0 : ℝ)
            ≤ (acH K b v : ℝ) * Tst := by
          rw [← mul_add, ← mul_add]
          apply mul_le_mul_of_nonneg_left _ hhR.le
          have hcast : ((∑ i, t' i : ℕ) : ℝ) + ((∑ m, t m : ℕ) : ℝ) + (t0 : ℝ)
              = ((t0 + ∑ i, t' i + ∑ m, t m : ℕ) : ℝ) := by push_cast; ring
          rw [hcast]
          exact hord'
        have hE' : (0.255 * (1 / (dK K : ℝ))
              + 1.01 * ((‖z‖ / 2 ^ J) / acS K r b v) - 9 * 2 ^ r) * acS K r b v * acD K σ
            = (0.255 / (dK K : ℝ)) * acS K r b v * acD K σ
              + 1.01 * (‖z‖ / 2 ^ J) * acD K σ - 9 * 2 ^ r * acS K r b v * acD K σ := by
          field_simp
        rw [hBIG, hE']
        nlinarith [harith, hkeyc]



end Work.BW
