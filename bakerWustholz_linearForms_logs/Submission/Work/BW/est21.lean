import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est21_l
import Submission.Work.BW.est_f_ge_half_g
import Submission.Work.BW.est15
import Submission.Work.BW.num_T
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.num_D_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! ### `est21` (BW (21), §17 p. 47–50, level `J`)

The analytic core of (21) — BW's "desired estimate for `f^{(t)}(l)`" — is the sibling
`Submission.Work.BW.est21_l`; the present file supplies the assembly with `est15` (via
`est_f_ge_half_g`, the `|f| ≥ ½|g|` step) and the numerical bookkeeping
(`acH_lower`, `sigma_ge`, `num_T`, `num_D_lower`). -/

namespace Work.BW

open Complex

/-- `d = [K:ℚ] ≥ 1`. -/
lemma est21_one_le_dK (K : Type*) [Field K] [NumberField K] : 1 ≤ dK K := by
  have h := Module.finrank_pos (R := ℚ) (M := K)
  show 1 ≤ Module.finrank ℚ K
  omega

/-- `D > 0` (from `σ_j ≥ 1/d` and `r ≥ 2`). -/
lemma acD_pos {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) : 0 < acD K σ := by
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := est21_one_le_dK K
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have h := (num_D_lower hr hd σ hσ).1
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd
  have hlog : 0 < Real.log (2 * (r : ℝ) * (dK K : ℝ)) := by
    apply Real.log_pos
    have h2r : (2:ℝ) * 2 ≤ 2 * (r:ℝ) := by linarith
    have h4 : (2:ℝ) * 2 * 1 ≤ (2 * (r:ℝ)) * (dK K:ℝ) :=
      mul_le_mul h2r hd1 (by norm_num) (by linarith)
    linarith
  have hpos : 0 < 2 * (r : ℝ) ^ r * 32 ^ (r + 1) * (dK K : ℝ) := by
    have h1 : (0:ℝ) < (r:ℝ) := by linarith
    positivity
  have hmain : 0 < 2 * (r : ℝ) ^ r * 32 ^ (r + 1) * (dK K : ℝ)
      * Real.log (2 * (r : ℝ) * (dK K : ℝ)) := mul_pos hpos hlog
  linarith

/-- `D = acD K σ ≥ 262144 = 2·2^2·32^3·1·1` (from `num_D_lower`, `log(2rd) ≥ 1`). -/
lemma acD_ge {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) : (262144 : ℝ) ≤ acD K σ := by
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := est21_one_le_dK K
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hD := (num_D_lower hr hd σ hσ).1
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by linarith
  have hrr : (4 : ℝ) ≤ (r : ℝ) ^ r := by
    calc (4:ℝ) = (2:ℝ)^2 := by norm_num
      _ ≤ (r:ℝ)^2 := pow_le_pow_left₀ (by norm_num) hr2 2
      _ ≤ (r:ℝ)^r := pow_le_pow_right₀ hr1 hr
  have h32 : (32768 : ℝ) ≤ (32:ℝ)^(r+1) := by
    calc (32768:ℝ) = (32:ℝ)^3 := by norm_num
      _ ≤ (32:ℝ)^(r+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hlog1 : (1:ℝ) ≤ Real.log (2 * (r:ℝ) * (dK K:ℝ)) := by
    have h4 : Real.exp 1 ≤ 2 * (r:ℝ) * (dK K:ℝ) := by
      have h2r : (2:ℝ) * 2 ≤ 2 * (r:ℝ) := by linarith
      have h41 : (2:ℝ) * 2 * 1 ≤ (2 * (r:ℝ)) * (dK K:ℝ) :=
        mul_le_mul h2r hd1 (by norm_num) (by linarith)
      have := Real.exp_one_lt_three
      linarith
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 * (r:ℝ) * (dK K:ℝ)) := Real.log_le_log (Real.exp_pos 1) h4
  have h2 : (0:ℝ) < 2 * (r:ℝ) * (dK K:ℝ) := by positivity
  have hB : (0:ℝ) ≤ (r:ℝ)^r := by positivity
  have hD32 : (0:ℝ) ≤ (32:ℝ)^(r+1) := by positivity
  have hAB : 4 * 32768 ≤ (r:ℝ)^r * (32:ℝ)^(r+1) :=
    mul_le_mul hrr h32 (by norm_num) hB
  have hAB' : (0:ℝ) ≤ (r:ℝ)^r * (32:ℝ)^(r+1) := mul_nonneg hB hD32
  have hABd : 4 * 32768 * 1 ≤ (r:ℝ)^r * (32:ℝ)^(r+1) * (dK K:ℝ) :=
    mul_le_mul hAB hd1 (by norm_num) hAB'
  have h1 : (262144:ℝ) ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (dK K:ℝ) := by linarith
  have hprod : 262144 ≤ 2 * (r:ℝ)^r * 32^(r+1) * (dK K:ℝ)
      * Real.log (2 * (r:ℝ) * (dK K:ℝ)) := by nlinarith [h1, hlog1, h2]
  linarith

/-- `‖(s : ℂ)‖ = |s|` as a real number. -/
lemma norm_intCast_eq (s : ℤ) : ‖(s : ℂ)‖ = ((|s| : ℤ) : ℝ) := by
  rw [Complex.norm_intCast]
  simp

/-- `log 2 ≤ 0.001·S·D` (BW §15: `log 2` is absorbed in the `1.133`). -/
lemma log_two_le_SD {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) :
    Real.log 2 ≤ 0.001 * (acS K r b v * acD K σ) := by
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := est21_one_le_dK K
  have hh : 19 ≤ acH K b v := (acH_lower H).1
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hSge : (608 : ℝ) ≤ acS K r b v :=
    (num_T (r := r) (d := dK K) (h := acH K b v) hr hd hh σ hσ).2.2.2
  have hDge : (262144 : ℝ) ≤ acD K σ := acD_ge H
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hmul : (608:ℝ) * 262144 ≤ acS K r b v * acD K σ := by
    have h := mul_le_mul hSge hDge (by norm_num : (0:ℝ) ≤ 262144) (by linarith)
    linarith
  nlinarith

/-- `kumJ ≤ 2.2·S·D` (BW p. 59: `J ≤ 50 log(2rd)`). -/
lemma kumJ_le_two {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K)) :
    kumJ K b v σ J ≤ 2.2 * acS K r b v * acD K σ := by
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := est21_one_le_dK K
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd
  have hlog : 0 < Real.log (2 * (r : ℝ) * (dK K : ℝ)) := by
    apply Real.log_pos
    have h2r : (2:ℝ) * 2 ≤ 2 * (r:ℝ) := by linarith
    have h4 : (2:ℝ) * 2 * 1 ≤ (2 * (r:ℝ)) * (dK K:ℝ) :=
      mul_le_mul h2r hd1 (by norm_num) (by linarith)
    linarith
  have hpI : (pI r (dK K) : ℝ) ≤ 50 * Real.log (2 * (r : ℝ) * (dK K : ℝ)) := by
    rw [pI]
    exact Nat.floor_le (by positivity)
  have hJle : (J : ℝ) ≤ 50 * Real.log (2 * (r : ℝ) * (dK K : ℝ)) :=
    le_trans (by exact_mod_cast hJ) hpI
  have hk : 0.044 * (J : ℝ) / Real.log (2 * (r : ℝ) * (dK K : ℝ)) ≤ 2.2 := by
    rw [div_le_iff₀ hlog]; nlinarith
  have hSD : 0 ≤ acS K r b v * acD K σ := by
    have hD := acD_pos H
    have hS : 0 ≤ acS K r b v := by
      simp only [acS, pS]; positivity
    positivity
  have hdef : kumJ K b v σ J
      = (0.044 * (J : ℝ) / Real.log (2 * (r : ℝ) * (dK K : ℝ))) * (acS K r b v * acD K σ) := by
    unfold kumJ
    push_cast
    ring
  rw [hdef]
  calc (0.044 * (J : ℝ) / Real.log (2 * (r : ℝ) * (dK K : ℝ))) * (acS K r b v * acD K σ)
      ≤ 2.2 * (acS K r b v * acD K σ) := mul_le_mul_of_nonneg_right hk hSD
    _ = 2.2 * acS K r b v * acD K σ := by ring

/-- BW (15)/(16)-style lower bound at level `J` for `f` (not `g`) at an integer `s`: the (15)
bound with `acg` replaced by `acf` and an extra factor `e^{-0.001·SD}` (which absorbs `log 2`).
From `est15` (`exp(lnp − A) ≤ ‖g(s)‖`), `est_f_ge_half_g` (`‖g(s)‖ ≤ 2‖f(s)‖`) and
`log 2 ≤ 0.001·SD` (`log_two_le_SD`). -/
lemma est21_fs {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K)) (μ : Fin r → ℕ) (Tst : ℝ)
    (hTst : Tst ≤ acT K σ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (s : ℤ)
    (hs : ((|s| : ℤ) : ℝ) / 2 ^ J ≤ 2 ^ r * acS K r b v)
    (hg : acg φ α b k L ι v σ p J μ t0 t (s : ℂ) ≠ 0) :
    Real.exp (lnp φ p - (Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
        ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ)
      + 1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J)
      - 0.001 * acS K r b v * acD K σ) ≤ ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by
  have hlog2 : Real.log 2 ≤ 0.001 * (acS K r b v * acD K σ) := log_two_le_SD H
  have h15 := est15 H J μ Tst hTst t0 t ht s hg
  have hhalf := (est_f_ge_half_g H J hJ μ Tst hTst t0 t ht s).1 hs
  have hsfac : Real.exp (lnp φ p - (Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
          ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ)
        + 1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J)
      - 0.001 * acS K r b v * acD K σ)
      = Real.exp (lnp φ p - (Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
          ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ)
        + 1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J))
        * Real.exp (-(0.001 * acS K r b v * acD K σ)) := by
    rw [← Real.exp_add]
    congr 1 <;> ring
  have h2exp : 2 * Real.exp (-(0.001 * acS K r b v * acD K σ)) ≤ 1 := by
    have h1 : Real.exp (-(0.001 * acS K r b v * acD K σ)) ≤ Real.exp (-(Real.log 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-(Real.log 2)) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
      norm_num
    linarith
  have hnn : (0:ℝ) ≤ ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := norm_nonneg _
  calc Real.exp (lnp φ p - (Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
          ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ)
        + 1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J)
      - 0.001 * acS K r b v * acD K σ)
      = Real.exp (lnp φ p - (Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
          ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ)
        + 1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J))
        * Real.exp (-(0.001 * acS K r b v * acD K σ)) := hsfac
    _ ≤ ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖
          * Real.exp (-(0.001 * acS K r b v * acD K σ)) :=
        mul_le_mul_of_nonneg_right h15 (Real.exp_pos _).le
    _ ≤ (2 * ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖)
          * Real.exp (-(0.001 * acS K r b v * acD K σ)) :=
        mul_le_mul_of_nonneg_right hhalf (Real.exp_pos _).le
    _ = ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖
          * (2 * Real.exp (-(0.001 * acS K r b v * acD K σ))) := by ring
    _ ≤ ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left h2exp hnn
    _ = ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by ring

/-- BW (21) at level `J` (§17, p. 47–50; p. 58): if `g(l;t') = 0` for all `|t'| ≤ T'+T''`, then for `|t| ≤ T''`, `m ≤ T'` and integer `s` with `2^{-J}|s| ≤ 2^rS`, `g(s;t) ≠ 0`: `log|f_m(l)/f(s)| ≤ dhT* + (1·133 − 9·2^r)SD + 1·01·2^{-J}(|l|+|s|)D + kum_J`. Chain: `iteratedDeriv_fAt`, `ellM_eq_sum_derVec`, `derVec_mem_span_iota`, `applyDer_Qdesc_span` (so `g^{(t')}(l;t'') = 0`), the `f − g` comparison with 0·226, 0·255, 0·282 (`num_17`), then (12), (15). -/
theorem est21 {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K)) (μ : Fin r → ℕ) (Tst : ℝ)
    (hTst : Tst ≤ acT K σ) (Tp Tpp : ℝ) (hTp : 0 ≤ Tp) (hsum : Tp + Tpp ≤ Tst) (l : ℂ)
    (hvan : ∀ (t0' : ℕ) (t' : Fin (r - 1) → ℕ), ((t0' + ∑ m, t' m : ℕ) : ℝ) ≤ Tp + Tpp →
      acg φ α b k L ι v σ p J μ t0' t' l = 0)
    (t0 : ℕ) (t : Fin (r - 1) → ℕ) (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tpp) (m : ℕ)
    (hm : (m : ℝ) ≤ Tp) (s : ℤ) (hs : ((|s| : ℤ) : ℝ) / 2 ^ J ≤ 2 ^ r * acS K r b v)
    (hg : acg φ α b k L ι v σ p J μ t0 t (s : ℂ) ≠ 0) :
    ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖ ≤ ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ *
      Real.exp ((dK K : ℝ) * (acH K b v : ℝ) * Tst + (1.133 - 9 * 2 ^ r) * acS K r b v * acD K σ +
        1.01 * ((‖l‖ + ((|s| : ℤ) : ℝ)) / 2 ^ J) * acD K σ + kumJ K b v σ J) := by
  have hd : 1 ≤ dK K := est21_one_le_dK K
  have hord : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst := by linarith
  have hL := est21_l H J hJ μ Tst hTst Tp Tpp hTp hsum l hvan t0 t ht m hm
  have hR := est21_fs H J hJ μ Tst hTst t0 t hord s hs hg
  by_cases hzero : ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖ = 0
  · rw [hzero]; positivity
  · have hposL : 0 < ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    have hposR : 0 < ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ :=
      lt_of_lt_of_le (Real.exp_pos _) hR
    have hlogL : Real.log ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖
        ≤ lnp φ p + (acH K b v : ℝ) * Tst + 0.282 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ
          + 1.01 * (‖l‖ / 2 ^ J) * acD K σ - 9 * 2 ^ r * acS K r b v * acD K σ := by
      have h := Real.log_le_log hposL hL
      rwa [Real.log_exp] at h
    have hlogR : lnp φ p - (Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
          ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ)
        + 1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J)
        - 0.001 * acS K r b v * acD K σ
        ≤ Real.log ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by
      have h := Real.log_le_log (Real.exp_pos _) hR
      rwa [Real.log_exp] at h
    have hSDnn : (0 : ℝ) ≤ acS K r b v * acD K σ := by
      have h1 : (0 : ℝ) ≤ acS K r b v := by simp only [acS, pS]; positivity
      have h2 : (0 : ℝ) ≤ acD K σ := le_of_lt (acD_pos H)
      positivity
    have h1d : 1 / (dK K : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast hd
    have h204 : 0.204 * (1 - 1 / (dK K : ℝ)) + 0.282 * (1 / (dK K : ℝ)) + 0.001 ≤ 0.283 := by
      linarith [h1d]
    have hid : (acH K b v : ℝ) * Tst + (1 - 1 / (dK K : ℝ)) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst)
        = (dK K : ℝ) * (acH K b v : ℝ) * Tst := by
      field_simp
      ring
    have hsplit : ‖l‖ / 2 ^ J + ((|s| : ℤ) : ℝ) / 2 ^ J
        = (‖l‖ + ((|s| : ℤ) : ℝ)) / 2 ^ J := by ring
    have hwz : 1.01 * (‖l‖ / 2 ^ J) * acD K σ
        + 1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ
        ≤ 1.01 * ((‖l‖ + ((|s| : ℤ) : ℝ)) / 2 ^ J) * acD K σ := by
      have hDnn : (0:ℝ) ≤ acD K σ := le_of_lt (acD_pos H)
      have hwnn : (0:ℝ) ≤ ‖l‖ / 2 ^ J := by positivity
      have hznn : (0:ℝ) ≤ ((|s| : ℤ) : ℝ) / 2 ^ J := by positivity
      nlinarith [hsplit, hDnn, hwnn, hznn]
    have hkey : Real.log ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖
        - Real.log ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖
        ≤ (dK K : ℝ) * (acH K b v : ℝ) * Tst + (1.133 - 9 * 2 ^ r) * acS K r b v * acD K σ
          + 1.01 * ((‖l‖ + ((|s| : ℤ) : ℝ)) / 2 ^ J) * acD K σ + kumJ K b v σ J := by
      have hmid : Real.log ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖
          - Real.log ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖
          ≤ ((acH K b v : ℝ) * Tst + 0.282 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ
              + 1.01 * (‖l‖ / 2 ^ J) * acD K σ - 9 * 2 ^ r * acS K r b v * acD K σ)
            + (Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
                ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ)
              + 1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J)
            + 0.001 * acS K r b v * acD K σ := by
        linarith [hlogL, hlogR]
      have hh : Height.logHeight p ≤ 0.85 * (acS K r b v * acD K σ) := by
        have := H.hp12
        linarith
      have h101 : (1.007:ℝ) ≤ 1.01 := by norm_num
      nlinarith [hmid, h204, hid, hwz, hh, hSDnn, h101]
    calc ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖
        = Real.exp (Real.log ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖) :=
          (Real.exp_log hposL).symm
      _ = Real.exp (Real.log ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖
            - Real.log ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖
            + Real.log ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖) := by ring_nf
      _ = Real.exp (Real.log ‖taylorC (acf φ α b k L ι v σ p J μ t0 t) m l‖
            - Real.log ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖)
          * Real.exp (Real.log ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖) :=
          Real.exp_add _ _
      _ ≤ Real.exp ((dK K : ℝ) * (acH K b v : ℝ) * Tst + (1.133 - 9 * 2 ^ r) * acS K r b v * acD K σ
            + 1.01 * ((‖l‖ + ((|s| : ℤ) : ℝ)) / 2 ^ J) * acD K σ + kumJ K b v σ J)
          * ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by
          rw [Real.exp_log hposR]
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hkey) (norm_nonneg _)
      _ = ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖
          * Real.exp ((dK K : ℝ) * (acH K b v : ℝ) * Tst + (1.133 - 9 * 2 ^ r) * acS K r b v * acD K σ
            + 1.01 * ((‖l‖ + ((|s| : ℤ) : ℝ)) / 2 ^ J) * acD K σ + kumJ K b v σ J) := by ring

end Work.BW
