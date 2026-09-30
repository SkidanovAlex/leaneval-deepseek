import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est14_sigbound
import Submission.Work.BW.num_T
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

section Bounds

variable {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
  {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
  {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
  {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}

/-- Port of `Work.BW.est21_dpb_log_bound`. -/
theorem est21_dpbD_log_bound {t A : ℝ} (ht : 0 ≤ t) (hA : Real.log 1000 ≤ 0.001 * A) :
    t ≤ Real.exp (0.001 * A + 0.001 * t) := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · rw [← h0]; positivity
  · refine Real.le_exp_of_log_le ?_
    have h1 : Real.log (t / 1000) ≤ t / 1000 - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hpos (by norm_num))
    rw [Real.log_div (ne_of_gt hpos) (by norm_num : (1000:ℝ) ≠ 0)] at h1
    linarith

/-- Port of `Work.BW.est21_dpb_one_le_dK`. -/
lemma est21_dpbD_one_le_dK : 1 ≤ dK K := by
  have h : 0 < Module.finrank ℚ K := Module.finrank_pos
  simp only [dK]
  omega

/-- Port of `Work.BW.est21_dpb_dK_pos_real`. -/
lemma est21_dpbD_dK_pos_real : (0:ℝ) < (dK K : ℝ) := by
  have h : 0 < dK K := lt_of_lt_of_le Nat.zero_lt_one est21_dpbD_one_le_dK
  exact_mod_cast h

/-- Port of `Work.BW.est21_dpb_lam_ne_zero`. -/
lemma est21_dpbD_lam_ne_zero (H : ACHyp φ α b k c v L α' σ ι p) : lam φ α b ≠ 0 := by
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

/-- Port of `Work.BW.est21_dpb_lambda_le`. -/
lemma est21_dpbD_lambda_le (H : ACHyp φ α b k c v L α' σ ι p) :
    ‖lam φ α b‖ ≤ Real.exp (-(9 * 2 ^ r * acS K r b v * acD K σ)) := by
  have hne := est21_dpbD_lam_ne_zero H
  have hpos : 0 < ‖lam φ α b‖ := norm_pos_iff.mpr hne
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr H.h10

/-- Port of `Work.BW.est21_dpb_num_basic`. -/
lemma est21_dpbD_num_basic (H : ACHyp φ α b k c v L α' σ ι p) :
    1000 ≤ 9 * 2 ^ r * acS K r b v * acD K σ ∧
      Real.log 1000 ≤ 0.001 * (acS K r b v * acD K σ / (dK K : ℝ)) := by
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hS : (608:ℝ) ≤ acS K r b v :=
    (num_T H.hr est21_dpbD_one_le_dK (acH_lower H).1 σ hσ).2.2.2
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
    exact_mod_cast est21_dpbD_one_le_dK
  have hl : (1:ℝ) ≤ Real.log (2 * (r:ℝ) * (dK K : ℝ)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h4 : (4:ℝ) ≤ 2 * (r:ℝ) * (dK K : ℝ) := by
      have hdr : (0:ℝ) < (dK K : ℝ) := est21_dpbD_dK_pos_real
      nlinarith [hdr, hr1]
    linarith [Real.exp_one_lt_three]
  have hD262 : (262144:ℝ) ≤ acD K σ := by
    have h := (num_D_lower H.hr est21_dpbD_one_le_dK σ hσ).1
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
      rw [hprod, div_eq_iff (ne_of_gt est21_dpbD_dK_pos_real)]
      ring
    rw [hquot]
    have h1 : Real.log 1000 ≤ (1000:ℝ) := Real.log_le_self (by norm_num)
    linarith

/-- Port of `Work.BW.est21_dpb_lam_small`. -/
lemma est21_dpbD_lam_small (H : ACHyp φ α b k c v L α' σ ι p) :
    lam φ α b ≠ 0 ∧ ‖lam φ α b‖ ≤ 0.001 := by
  refine ⟨est21_dpbD_lam_ne_zero H, ?_⟩
  have hkey := (est21_dpbD_num_basic H).1
  have hlog1000 : Real.log 1000 ≤ 9 * 2 ^ r * acS K r b v * acD K σ :=
    le_trans (Real.log_le_self (by norm_num)) hkey
  refine le_trans (est21_dpbD_lambda_le H) ?_
  refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 0.001)).1 ?_
  have h1 : Real.log (0.001:ℝ) = -Real.log 1000 := by
    rw [show (0.001:ℝ) = (1000:ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [h1]
  linarith [hlog1000]

/-- Port of `Work.BW.est21_dpb_expSig_le` — the `‖e^{δ_λ} − 1‖` bound of the BW p. 49 `0.255` estimate.  The original lives in `Submission/Work/BW/est21_dpb_clean.lean` (line 366); copy its proof (it uses `est14_sigbound` and the lemmas below).  That file imports `Submission.Work.BW.est13`, which does not compile, so nothing is importable from it.

IMPORTANT: in the SAME file, declare the following five lemmas too, ported verbatim from `est21_dpb_clean.lean`, PUBLIC and with EXACTLY these names (the consumer refers to them by name):
* `est21_dpbD_log_bound {t A : ℝ} (ht : 0 ≤ t) (hA : Real.log 1000 ≤ 0.001 * A) : t ≤ Real.exp (0.001 * A + 0.001 * t)`  (line 242)
* `est21_dpbD_lam_ne_zero (H : ACHyp …) : lam φ α b ≠ 0`  (line 254)
* `est21_dpbD_lambda_le (H : ACHyp …) : ‖lam φ α b‖ ≤ Real.exp (-(9 * 2 ^ r * acS K r b v * acD K σ))`  (line 282)
* `est21_dpbD_num_basic (H : ACHyp …) : 1000 ≤ 9 * 2 ^ r * acS K r b v * acD K σ ∧ Real.log 1000 ≤ 0.001 * (acS K r b v * acD K σ / (dK K : ℝ))`  (line 290)
* `est21_dpbD_lam_small (H : ACHyp …) : lam φ α b ≠ 0 ∧ ‖lam φ α b‖ ≤ 0.001`  (line 348)
Any OTHER helper must be named with the prefix `est21_dpbD_` and be public. -/
lemma est21_dpbD_expSig_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (z : ℂ)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    ‖Complex.exp (estSig φ α b k v L J z lm) - 1‖ ≤
      ‖lam φ α b‖ * (‖z‖ * acD K σ / 2 ^ J) * Real.exp (0.001 * (‖z‖ * acD K σ / 2 ^ J)) := by
  have hsig := est14_sigbound H J z lm
  have hs := (est21_dpbD_lam_small H).2
  have hDDnn : (0:ℝ) ≤ acD K σ := by
    have hσpos : ∀ j, 0 < σ j := by
      intro j
      have h := sigma_ge H j
      have h2 : (0:ℝ) < 1 / (dK K : ℝ) := div_pos one_pos est21_dpbD_dK_pos_real
      linarith
    have hprod : (0:ℝ) ≤ ∏ j, σ j := le_of_lt (Finset.prod_pos (fun j _ => hσpos j))
    have h1 : (0:ℝ) ≤ Real.log (2 * (r:ℝ) * (dK K : ℝ)) := by
      have hr1 : (1:ℝ) ≤ (r:ℝ) := by
        have h := H.hr
        have h2 : 1 ≤ r := by omega
        exact_mod_cast h2
      have h2 : (1:ℝ) ≤ 2 * (r:ℝ) * (dK K : ℝ) := by
        have hd1 : (1:ℝ) ≤ (dK K : ℝ) := by exact_mod_cast est21_dpbD_one_le_dK
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

end Bounds

end Work.BW
