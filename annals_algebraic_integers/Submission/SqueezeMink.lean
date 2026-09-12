import Submission.SqueezeFull
import Mathlib.Tactic

/-!
# Prop:squeeze (Smith GON.tex) from the Minkowski lower box

`squeeze_of_mink_lower : MinkBox.minkLower → squeezeProp` — see the
declaration below.  Proof plan:

1. choose a good tuple α (via `Submission.SqueezeCore.exists_good_tuple`),
2. apply `minkLower` with `v k = w(α k)^n |R(α k)|` and
   `mu i = wnorm n (zmap (Q i) * zmap R)`,
3. absorb the polynomial slack `d^{CL·d}` into `n^{−C·n}`;
   the case `m = 0` is a direct one-point averaging.
-/

noncomputable section

open Polynomial
open scoped Real BigOperators Topology ENNReal
open MeasureTheory

namespace Submission.SqueezeMink

open Submission.MinkBox
open Submission.Contracts
open Submission.EnergyHalf
open Submission.EnergyNeg
open Submission.WeightedNorm
open Submission.SerreExample
open Submission.WnormToolkit
open Submission.SqueezeCore
open Submission.PotentialDefs

/-- Smith prop:squeeze for the Serre data (slack `n^{−C·n}` allowed). -/
def squeezeProp : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (m n : ℕ), 2 ≤ n → m ≤ n →
    ∀ (R : Polynomial ℤ), R ≠ 0 →
      (0 ≤ ∫ x : ℝ, Real.log |Polynomial.aeval x R| ∂muSerre) →
    ∀ (Q : Fin (m + 1) → Polynomial ℤ),
      LinIndepInt (m + 1) Q → (∀ i, (Q i).natDegree ≤ m) →
      (n : ℝ) ^ (-C * (n : ℝ)) *
          Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) * energy) ≤
        ∏ i : Fin (m + 1), wnorm n (zmap (Q i) * zmap R)

/-! ## small helpers -/

/-- the pair product in dimension one is trivial. -/
lemma pairProd_one (α : Fin 1 → ℝ) : pairProd 1 α = 1 := by
  rw [pairProd, Fin.prod_univ_one]
  have hf : (Finset.univ.filter (fun x : Fin 1 => (0 : Fin 1) < x)) = ∅ := by
    ext x
    fin_cases x
    simp
  rw [hf]
  simp

/-- `|(P*Q).eval x| = |P.eval x|·|Q.eval x|`. -/
lemma abs_eval_mul (P Q : Polynomial ℝ) (x : ℝ) :
    |(P * Q).eval x| = |P.eval x| * |Q.eval x| := by
  simp [abs_mul]

/-- a nonzero constant integer polynomial has |eval| ≥ 1 everywhere. -/
lemma const_poly_abs_ge_one {Q0 : Polynomial ℤ} (hQ0 : Q0 ≠ 0)
    (hdeg : Q0.natDegree ≤ 0) (x : ℝ) : (1 : ℝ) ≤ |(zmap Q0).eval x| := by
  have hdeg0 : Q0.natDegree = 0 := le_antisymm hdeg (Nat.zero_le _)
  have hC : Q0 = Polynomial.C (Q0.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
  have hc0 : Q0.coeff 0 ≠ 0 := by
    intro h
    apply hQ0
    rw [hC, h]
    simp
  have hmap : (zmap Q0).eval x = ((Q0.coeff 0 : ℤ) : ℝ) := by
    rw [zmap, hC]
    simp
  rw [hmap]
  exact_mod_cast (Int.one_le_abs hc0)

/-- `n^{−C·n}·exp(X) ≤ exp(X)` for `0 ≤ C`, `2 ≤ n`. -/
lemma n_pow_slack_le_one {C n X : ℝ} (hC : 0 ≤ C) (hn : 2 ≤ n) :
    (n : ℝ) ^ (-C * n) * Real.exp X ≤ Real.exp X := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hle1 : (n : ℝ) ^ (-C * n) ≤ 1 := by
    rw [Real.rpow_def_of_pos hnpos]
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.log_nonneg (by linarith)) (by nlinarith : -C * n ≤ 0)
  exact mul_le_of_le_one_left (Real.exp_pos X).le hle1

/-- log-level slack bound. -/
lemma log_slack_bound {CL n d : ℝ} (hCL : 0 ≤ CL) (hn : 2 ≤ n) (hd2 : 2 ≤ d)
    (hd : d ≤ n + 1) : (CL * d) * Real.log d ≤ (4 * CL + 2) * n * Real.log n := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd2
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hd2n : d ≤ 2 * n := by nlinarith
  have hlogd : Real.log d ≤ 2 * Real.log n := by
    have hle1 : Real.log d ≤ Real.log (2 * n) := Real.log_le_log hdpos (by nlinarith)
    have hmul : Real.log (2 * n) = Real.log 2 + Real.log n := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hnpos)]
    have hle2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by linarith)
    calc
      Real.log d ≤ Real.log (2 * n) := hle1
      _ = Real.log 2 + Real.log n := hmul
      _ ≤ 2 * Real.log n := by nlinarith
  calc
    (CL * d) * Real.log d ≤ (CL * d) * (2 * Real.log n) := by
          exact mul_le_mul_of_nonneg_left hlogd (mul_nonneg hCL (le_of_lt hdpos))
    _ = 2 * CL * d * Real.log n := by ring
    _ ≤ 2 * CL * (2 * n) * Real.log n := by
          have hc : 0 ≤ 2 * CL := mul_nonneg (by norm_num) hCL
          have hm1 : (2 * CL) * d ≤ (2 * CL) * (2 * n) :=
            mul_le_mul_of_nonneg_left hd2n hc
          exact mul_le_mul_of_nonneg_right hm1 hlog
    _ = 4 * CL * n * Real.log n := by ring
    _ ≤ (4 * CL + 2) * n * Real.log n := by
          have hadd : 0 ≤ 2 * n * Real.log n := by positivity
          linarith

/-- real-power exponent-slack: `d^{CL·d} ≤ n^{(4·CL+2)·n}`. -/
lemma d_pow_le_n_pow {CL n d : ℝ} (hCL : 0 ≤ CL) (hn : 2 ≤ n) (hd2 : 2 ≤ d)
    (hd : d ≤ n + 1) : d ^ (CL * d) ≤ n ^ ((4 * CL + 2) * n) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd2
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  rw [Real.rpow_def_of_pos hdpos, Real.rpow_def_of_pos hnpos]
  rw [Real.exp_le_exp]
  nlinarith [log_slack_bound hCL hn hd2 hd]

/-- inverse-slack: `n^{−(4CL+2)·n} ≤ d^{−CL·d}`. -/
lemma n_neg_pow_le_d_neg_pow {CL n d : ℝ} (hCL : 0 ≤ CL) (hn : 2 ≤ n) (hd2 : 2 ≤ d)
    (hd : d ≤ n + 1) : n ^ (-(4 * CL + 2) * n) ≤ d ^ (-(CL * d)) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd2
  rw [Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hdpos]
  rw [Real.exp_le_exp]
  nlinarith [log_slack_bound hCL hn hd2 hd]

/-- the theorem exponent (d = m+1 form). -/
lemma tm_exp_eq {m n : ℕ} :
    ((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) =
      ((m + 1 : ℕ) : ℝ) * (n : ℝ) - ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1) / 2 := by
  rw [Nat.cast_add, Nat.cast_one]
  ring

/-- m = 0: single factor lower bound from one-point averaging. -/
lemma m0_case {n : ℕ} (hn : 2 ≤ n) {C : ℝ} (hC : 0 ≤ C)
    (R : Polynomial ℤ) (hR : R ≠ 0)
    (hRint : 0 ≤ ∫ x : ℝ, Real.log |Polynomial.aeval x R| ∂muSerre)
    (Q0 : Polynomial ℤ) (hQ0 : Q0 ≠ 0) (hdeg : Q0.natDegree ≤ 0) :
    (n : ℝ) ^ (-C * (n : ℝ)) * Real.exp ((n : ℝ) * energy) ≤
      wnorm n (zmap Q0 * zmap R) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rcases exists_good_tuple (d := 1) (n := n) (by norm_num : 1 ≤ (1 : ℕ)) R hR hRint with
    ⟨α, hgood, hbig⟩
  have hxI : α (0 : Fin 1) ∈ Set.Icc aSerre bSerre := hgood.1 (0 : Fin 1)
  have hx1 : tupleF 1 n R α = (weight muSerre (α (0 : Fin 1))) ^ n *
      |Polynomial.aeval (α (0 : Fin 1)) R| := by
    simp [tupleF, pairProd_one]
  have hexp : Real.exp (((1 : ℝ) * (n : ℝ) - (1 : ℝ) * (1 - 1) / 2) * energy) =
      Real.exp ((n : ℝ) * energy) := by
    congr 1
    ring
  have hbig2 : Real.exp ((n : ℝ) * energy) ≤
      (weight muSerre (α (0 : Fin 1))) ^ n * |Polynomial.aeval (α (0 : Fin 1)) R| := by
    rw [← hexp, ← hx1]
    simpa using hbig
  have hRabs : |Polynomial.aeval (α (0 : Fin 1)) R| =
      |(zmap R).eval (α (0 : Fin 1))| := by
    rw [Submission.EnergyNeg.aeval_eq_zmap_eval R (α (0 : Fin 1))]
  have hprodabs : |Polynomial.aeval (α (0 : Fin 1)) R| * |(zmap Q0).eval (α (0 : Fin 1))| =
      |(zmap Q0 * zmap R).eval (α (0 : Fin 1))| := by
    rw [hRabs, mul_comm]
    rw [← abs_eval_mul (zmap Q0) (zmap R) (α (0 : Fin 1))]
  have hge_v : (weight muSerre (α (0 : Fin 1))) ^ n * |Polynomial.aeval (α (0 : Fin 1)) R| ≤
      wnorm n (zmap Q0 * zmap R) := by
    calc
      (weight muSerre (α (0 : Fin 1))) ^ n * |Polynomial.aeval (α (0 : Fin 1)) R|
          ≤ (weight muSerre (α (0 : Fin 1))) ^ n *
              (|Polynomial.aeval (α (0 : Fin 1)) R| * |(zmap Q0).eval (α (0 : Fin 1))|) := by
            have hc1 : (1 : ℝ) ≤ |(zmap Q0).eval (α (0 : Fin 1))| :=
              const_poly_abs_ge_one hQ0 hdeg (α (0 : Fin 1))
            have hm : (1 : ℝ) * |Polynomial.aeval (α (0 : Fin 1)) R| ≤
                |(zmap Q0).eval (α (0 : Fin 1))| * |Polynomial.aeval (α (0 : Fin 1)) R| :=
              mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
            have hm' : |Polynomial.aeval (α (0 : Fin 1)) R| ≤
                |Polynomial.aeval (α (0 : Fin 1)) R| * |(zmap Q0).eval (α (0 : Fin 1))| := by
              simpa [one_mul, mul_comm] using hm
            exact mul_le_mul_of_nonneg_left hm'
              (pow_nonneg (weight_pos muSerre (α (0 : Fin 1))).le n)
      _ = (weight muSerre (α (0 : Fin 1))) ^ n *
          |(zmap Q0 * zmap R).eval (α (0 : Fin 1))| := by rw [hprodabs]
      _ ≤ wnorm n (zmap Q0 * zmap R) := wnorm_ge_pointwise n (zmap Q0 * zmap R) hxI
  calc
    (n : ℝ) ^ (-C * (n : ℝ)) * Real.exp ((n : ℝ) * energy)
        ≤ Real.exp ((n : ℝ) * energy) := n_pow_slack_le_one (C := C) (X := (n : ℝ) * energy) hC hnR
    _ ≤ (weight muSerre (α (0 : Fin 1))) ^ n * |Polynomial.aeval (α (0 : Fin 1)) R| := hbig2
    _ ≤ wnorm n (zmap Q0 * zmap R) := hge_v

/-- m ≥ 1: the product of weighted norms beats `n^{−C·n}·exp`. -/
lemma m_ge_one_bound {CL : ℝ} (hCL0 : 0 ≤ CL)
    (hCL : ∀ d : ℕ, 2 ≤ d → ∀ α : Fin d → ℝ, Function.Injective α →
      ∀ v : Fin d → ℝ, (∀ k, 0 < v k) →
      ∀ Q : Fin d → Polynomial ℤ, LinIndepInt d Q →
        (∀ i, (Q i).natDegree ≤ d - 1) → ∀ mu : Fin d → ℝ,
          (∀ i k, v k * |evalInt (Q i) (α k)| ≤ mu i) →
          Dval d α v ≤ (d : ℝ) ^ (CL * (d : ℝ)) * (∏ i : Fin d, mu i))
    {m n : ℕ} (hn : 2 ≤ n) (hm : m ≤ n) (hm1 : 1 ≤ m)
    (R : Polynomial ℤ) (hR : R ≠ 0)
    (hRint : 0 ≤ ∫ x : ℝ, Real.log |Polynomial.aeval x R| ∂muSerre)
    (Q : Fin (m + 1) → Polynomial ℤ) (hlin : LinIndepInt (m + 1) Q)
    (hdeg : ∀ i, (Q i).natDegree ≤ m) :
    (n : ℝ) ^ (-(4 * CL + 2) * (n : ℝ)) *
        Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) * energy) ≤
      ∏ i : Fin (m + 1), wnorm n (zmap (Q i) * zmap R) := by
  classical
  have hd1 : 1 ≤ m + 1 := by omega
  have hd : 2 ≤ m + 1 := by omega
  rcases exists_good_tuple (d := m + 1) (n := n) hd1 R hR hRint with ⟨α, hgood, hbig⟩
  have hαI : ∀ k : Fin (m + 1), α k ∈ Set.Icc aSerre bSerre := hgood.1
  have hαR : ∀ k : Fin (m + 1), Polynomial.aeval (α k) R ≠ 0 := hgood.2.1
  have hαinj : Function.Injective α := hgood.2.2
  have hbig' : Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) * energy) ≤
      tupleF (m + 1) n R α := by
    convert hbig using 1
    congr 1
    push_cast
    ring
  let v : Fin (m + 1) → ℝ := fun k =>
    (weight muSerre (α k)) ^ n * |Polynomial.aeval (α k) R|
  let mu : Fin (m + 1) → ℝ := fun i => wnorm n (zmap (Q i) * zmap R)
  have hv : ∀ k : Fin (m + 1), 0 < v k := by
    intro k
    dsimp [v]
    exact mul_pos (pow_pos (weight_pos muSerre (α k)) n) (abs_pos.mpr (hαR k))
  have hprem : ∀ i k : Fin (m + 1), v k * |evalInt (Q i) (α k)| ≤ mu i := by
    intro i k
    have heval : |evalInt (Q i) (α k)| = |(zmap (Q i)).eval (α k)| := by
      simp [evalInt, zmap]
    have hRz : |Polynomial.aeval (α k) R| = |(zmap R).eval (α k)| := by
      rw [Submission.EnergyNeg.aeval_eq_zmap_eval R (α k)]
    have hpa : |Polynomial.aeval (α k) R| * |(zmap (Q i)).eval (α k)| =
        |(zmap (Q i) * zmap R).eval (α k)| := by
      rw [hRz, mul_comm]
      rw [← abs_eval_mul (zmap (Q i)) (zmap R) (α k)]
    calc
      v k * |evalInt (Q i) (α k)|
          = (weight muSerre (α k)) ^ n * |Polynomial.aeval (α k) R| *
              |(zmap (Q i)).eval (α k)| := by
                dsimp [v]
                rw [heval]
      _ = (weight muSerre (α k)) ^ n *
          (|Polynomial.aeval (α k) R| * |(zmap (Q i)).eval (α k)|) := by ring
      _ = (weight muSerre (α k)) ^ n * |(zmap (Q i) * zmap R).eval (α k)| := by rw [hpa]
      _ ≤ mu i := by
                dsimp [mu]
                exact wnorm_ge_pointwise n (zmap (Q i) * zmap R) (hαI k)
  have hdegQ : ∀ i : Fin (m + 1), (Q i).natDegree ≤ (m + 1) - 1 := by
    intro i
    have := hdeg i
    omega
  have hmain := hCL (m + 1) hd α hαinj v hv Q hlin hdegQ mu hprem
  have hDval : Dval (m + 1) α v = tupleF (m + 1) n R α := by
    simp [Dval, tupleF, v]
  have hlow : Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) * energy) ≤
      ((m + 1 : ℕ) : ℝ) ^ (CL * ((m + 1 : ℕ) : ℝ)) * (∏ i : Fin (m + 1), mu i) := by
    calc
      Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) * energy) ≤ tupleF (m + 1) n R α := hbig'
      _ = Dval (m + 1) α v := hDval.symm
      _ ≤ ((m + 1 : ℕ) : ℝ) ^ (CL * ((m + 1 : ℕ) : ℝ)) * (∏ i : Fin (m + 1), mu i) := hmain
  have hmmpos : 0 < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos m)
  have hpow : 0 < ((m + 1 : ℕ) : ℝ) ^ (CL * ((m + 1 : ℕ) : ℝ)) := Real.rpow_pos_of_pos hmmpos _
  have hdiv2 : Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) * energy) *
      (((m + 1 : ℕ) : ℝ) ^ (CL * ((m + 1 : ℕ) : ℝ)))⁻¹ ≤ ∏ i : Fin (m + 1), mu i := by
    have hle1 : Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) * energy) /
        (((m + 1 : ℕ) : ℝ) ^ (CL * ((m + 1 : ℕ) : ℝ))) ≤ ∏ i : Fin (m + 1), mu i :=
      (div_le_iff₀ hpow).mpr (by simpa [mul_comm] using hlow)
    simpa [div_eq_mul_inv] using hle1
  have hdc2 : (2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hd
  have hdc : ((m + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
    have hmn : m + 1 ≤ n + 1 := Nat.succ_le_succ hm
    exact_mod_cast hmn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hneg_slack : (n : ℝ) ^ (-(4 * CL + 2) * (n : ℝ)) ≤
      ((m + 1 : ℕ) : ℝ) ^ (-(CL * ((m + 1 : ℕ) : ℝ))) := by
    exact n_neg_pow_le_d_neg_pow hCL0 hnR hdc2 hdc
  have hdneg : ((m + 1 : ℕ) : ℝ) ^ (-(CL * ((m + 1 : ℕ) : ℝ))) =
      (((m + 1 : ℕ) : ℝ) ^ (CL * ((m + 1 : ℕ) : ℝ)))⁻¹ := by
    exact Real.rpow_neg (le_of_lt hmmpos) (CL * ((m + 1 : ℕ) : ℝ))
  calc
    (n : ℝ) ^ (-(4 * CL + 2) * (n : ℝ)) *
        Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) * energy)
        ≤ ((m + 1 : ℕ) : ℝ) ^ (-(CL * ((m + 1 : ℕ) : ℝ))) *
            Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) * energy) := by
          exact mul_le_mul_of_nonneg_right hneg_slack (Real.exp_pos _).le
    _ = Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) * energy) *
        (((m + 1 : ℕ) : ℝ) ^ (CL * ((m + 1 : ℕ) : ℝ)))⁻¹ := by
          rw [hdneg, mul_comm]
    _ ≤ ∏ i : Fin (m + 1), wnorm n (zmap (Q i) * zmap R) := by
          simpa [mu] using hdiv2

/-! ## the main theorem -/

theorem squeeze_of_mink_lower (hl : MinkBox.minkLower) : squeezeProp := by
  rcases hl with ⟨CL, hCLpos, hCL⟩
  refine ⟨4 * CL + 2, by positivity, ?_⟩
  intro m n hn hm R hR hRint Q hlin hdeg
  by_cases hm0 : m = 0
  · subst m
    have hC0 : 0 ≤ 4 * CL + 2 := by positivity
    have hQ0 : Q (0 : Fin (0 + 1)) ≠ 0 :=
      Submission.MinkLower.Q_ne_zero_of_LinIndepInt Q hlin (0 : Fin (0 + 1))
    have hdeg0 : (Q (0 : Fin (0 + 1))).natDegree ≤ 0 := by
      have := hdeg (0 : Fin (0 + 1))
      simpa using this
    have hmain := m0_case (n := n) hn (C := 4 * CL + 2) hC0 R hR hRint
      (Q (0 : Fin (0 + 1))) hQ0 hdeg0
    have hexp0 : Real.exp ((((0 : ℕ) : ℝ) + 1) * ((n : ℝ) - ((0 : ℕ) : ℝ) / 2) * energy) =
        Real.exp ((n : ℝ) * energy) := by
      congr 1
      ring
    have hprod : (∏ i : Fin (0 + 1), wnorm n (zmap (Q i) * zmap R)) =
        wnorm n (zmap (Q 0) * zmap R) := by
      simpa using (Fin.prod_univ_one (f := fun i : Fin (0 + 1) => wnorm n (zmap (Q i) * zmap R)))
    rw [hexp0, hprod]
    exact hmain
  · have hm1 : 1 ≤ m := by omega
    exact m_ge_one_bound (CL := CL) (le_of_lt hCLpos) hCL hn hm hm1 R hR hRint Q hlin hdeg

end Submission.SqueezeMink
