/-
# `Submission.Work.FIArea3.CrudeBracketReduce` — the reduction step of the crude bracket estimate

Extracted verbatim from `Submission/Work/FIArea3/pairSumCrude6_joint.lean` (where it is
error-free) so that colleagues can build on it without importing the broken parent module.
-/
import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.PairBracketDefs
import Submission.Work.FIArea3.jointCountNoBox
import Submission.Work.FIArea3.JointCount.card_filter_le_le_arith
import Submission.Work.FIArea3.JointCount.joint_sum_le_double

namespace Work.FIArea3

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable


/-- `1 ≤ log x`. -/
lemma pj_logx_ge_one (Pa : Work.FITop.Params) : 1 ≤ Real.log (Pa.x : ℝ) := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have h3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  exact le_trans h3 (Real.log_le_log (by norm_num) hx3)

/-- `loglog x ≥ 1/16`. -/
lemma pj_loglog_ge (Pa : Work.FITop.Params) :
    (1 / 16 : ℝ) ≤ Real.log (Real.log (Pa.x : ℝ)) := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have h3pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hle : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
  have hgt : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
  have hpos : (0 : ℝ) < (1.0986122885 : ℝ) := by norm_num
  have h1 : (1 / 16 : ℝ) ≤ Real.log (1.0986122885 : ℝ) := by
    refine le_trans (by norm_num) (Real.one_sub_inv_le_log_of_pos hpos)
  have h2 : Real.log (1.0986122885 : ℝ) ≤ Real.log (Real.log 3) :=
    Real.log_le_log hpos hgt.le
  have h3 : Real.log (Real.log 3) ≤ Real.log (Real.log (Pa.x : ℝ)) :=
    Real.log_le_log h3pos hle
  linarith

/-- `θ = (log x)^{-A'} ≤ 1`. -/
lemma pj_theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  refine Real.rpow_le_one_of_one_le_of_nonpos (pj_logx_ge_one Pa) ?_
  have : 0 ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
  linarith

/-- In the joint regime `η < 1/4`: `N > x^{1/4+η}` and `N < x^{1/2}`. -/

lemma pj_two_sum_const_mul (K1 K2 : ℕ) (c : ℝ) (X : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2, c * X d e)
      = c * ∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2, X d e := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.mul_sum]

/-- **The reduction step of the bracket estimate**: FI Lemma 2.2 with `k = 4` for both `τ`'s,
followed by the joint count `jointCountNoBox` for every pair `(d,e)`. -/
lemma pj_bracket_reduce (Pa : Work.FITop.Params) (φ : ℝ) (z₁ : GaussianInt)
    (hcop : Nat.Coprime z₁.re.natAbs z₁.im.natAbs)
    (hbox : ∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
        (Work.FIPlan.absDelta z₁ z : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N) :
    (∑ z₂ ∈ Work.FIArea3.polarBoxFinset Pa φ,
          ((((Work.FIPlan.gnorm z₂).divisors.card : ℕ)) : ℝ)
            * ((((Work.FIPlan.absDelta z₁ z₂).divisors.card : ℕ)) : ℝ))
      ≤ 65536 * (Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
            * Work.FIArea3.dsum1 (Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)))
                (Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)))
          + 80 * (Pa.θ * Real.sqrt Pa.N)
            * Work.FIArea3.dsum2 (Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)))
                (Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)))
          + Work.FIArea3.dsum3 (Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)))
                (Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)))) := by
  set B := Work.FIArea3.polarBoxFinset Pa φ with hBdef
  set K1 := Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)) with hK1def
  set K2 := Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)) with hK2def
  have hθ1 : Pa.θ ≤ 1 := pj_theta_le_one Pa
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have h2Npos : (0 : ℝ) < 2 * Pa.N := by linarith
  have h4p : (0 : ℝ) < 4 * Real.pi * Pa.θ * Pa.N := by
    have hp : (0 : ℝ) < Real.pi := Real.pi_pos
    have hθ0 := Pa.hθ0
    positivity
  have hτg : ∀ z ∈ B, ((((Work.FIPlan.gnorm z).divisors.card : ℕ)) : ℝ)
      ≤ 256 * ∑ d ∈ Finset.Icc 1 K1,
          (if d ∣ Work.FIPlan.gnorm z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) := by
    intro z hz
    refine Work.FIArea3.JointCount.tau_le_sum_Icc_aux (Work.FIPlan.gnorm z) K1 ?_
    have hzpol : Work.FITop3.InPolarBox Pa φ z :=
      (Work.FIArea3.mem_polarBoxFinset.mp (hBdef ▸ hz)).2
    have hgn : (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N := hzpol.2.2.1
    have h1 : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by nlinarith [hgn, hθ1, hNpos]
    have hrpow : ((2 * Pa.N) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = 2 * Pa.N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h2Npos.le]; norm_num
    have hK1ge : (2 * Pa.N) ^ ((1 : ℝ) / 4) ≤ (K1 : ℝ) := by
      rw [hK1def]; exact Nat.le_ceil _
    calc (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := h1
      _ = ((2 * Pa.N) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := hrpow.symm
      _ ≤ (K1 : ℝ) ^ (4 : ℕ) :=
          pow_le_pow_left₀ (Real.rpow_nonneg h2Npos.le _) hK1ge 4
  have hτδ : ∀ z ∈ B, ((((Work.FIPlan.absDelta z₁ z).divisors.card : ℕ)) : ℝ)
      ≤ 256 * ∑ e ∈ Finset.Icc 1 K2,
          (if e ∣ Work.FIPlan.absDelta z₁ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) := by
    intro z hz
    refine Work.FIArea3.JointCount.tau_le_sum_Icc_aux (Work.FIPlan.absDelta z₁ z) K2 ?_
    have hδ : (Work.FIPlan.absDelta z₁ z : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N := hbox z (hBdef ▸ hz)
    have hrpow : ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ)
        = 4 * Real.pi * Pa.θ * Pa.N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h4p.le]; norm_num
    have hK2ge : (4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4) ≤ (K2 : ℝ) := by
      rw [hK2def]; exact Nat.le_ceil _
    calc (Work.FIPlan.absDelta z₁ z : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N := hδ
      _ = ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := hrpow.symm
      _ ≤ (K2 : ℝ) ^ (4 : ℕ) :=
          pow_le_pow_left₀ (Real.rpow_nonneg h4p.le _) hK2ge 4
  have hmain := Work.FIArea3.JointCount.joint_double_sum_bound_aux B
      (fun z => Work.FIPlan.gnorm z) (fun z => Work.FIPlan.absDelta z₁ z) K1 K2 hτg hτδ
  refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  rw [hBdef]
  have hcount : ∀ d ∈ Finset.Icc 1 K1, ∀ e ∈ Finset.Icc 1 K2,
      ((((Work.FIArea3.polarBoxFinset Pa φ).filter
          (fun z => d ∣ Work.FIPlan.gnorm z ∧ e ∣ Work.FIPlan.absDelta z₁ z)).card : ℕ) : ℝ)
        ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
            * ((d.divisors.card : ℝ) * (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)))
          + 80 * (Pa.θ * Real.sqrt Pa.N) * (d.divisors.card : ℝ) / Real.sqrt (d : ℝ)
          + (d.divisors.card : ℝ) := by
    intro d hd e he
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    exact Work.FIArea3.jointCountNoBox Pa φ z₁ d e hcop hd1 he1
  have hpt : ∀ d ∈ Finset.Icc 1 K1, ∀ e ∈ Finset.Icc 1 K2,
      (d.divisors.card : ℝ) ^ (8 : ℕ) * (e.divisors.card : ℝ) ^ (8 : ℕ)
        * ((((Work.FIArea3.polarBoxFinset Pa φ).filter
            (fun z => d ∣ Work.FIPlan.gnorm z ∧ e ∣ Work.FIPlan.absDelta z₁ z)).card : ℕ) : ℝ)
      ≤ (d.divisors.card : ℝ) ^ (8 : ℕ) * (e.divisors.card : ℝ) ^ (8 : ℕ)
        * (Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
              * ((d.divisors.card : ℝ) * (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)))
          + 80 * (Pa.θ * Real.sqrt Pa.N) * (d.divisors.card : ℝ) / Real.sqrt (d : ℝ)
          + (d.divisors.card : ℝ)) := by
    intro d hd e he
    exact mul_le_mul_of_nonneg_left (hcount d hd e he) (by positivity)
  have hring : ∀ d e : ℕ, (d.divisors.card : ℝ) ^ (8 : ℕ) * (e.divisors.card : ℝ) ^ (8 : ℕ)
        * (Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
              * ((d.divisors.card : ℝ) * (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)))
          + 80 * (Pa.θ * Real.sqrt Pa.N) * (d.divisors.card : ℝ) / Real.sqrt (d : ℝ)
          + (d.divisors.card : ℝ))
      = Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
          * ((d.divisors.card : ℝ) ^ (9 : ℕ) * (e.divisors.card : ℝ) ^ (8 : ℕ)
              * (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)))
        + 80 * (Pa.θ * Real.sqrt Pa.N)
          * ((d.divisors.card : ℝ) ^ (9 : ℕ) * (e.divisors.card : ℝ) ^ (8 : ℕ) / Real.sqrt (d : ℝ))
        + (d.divisors.card : ℝ) ^ (9 : ℕ) * (e.divisors.card : ℝ) ^ (8 : ℕ) := by
    intro d e; ring
  calc (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
        (d.divisors.card : ℝ) ^ (8 : ℕ) * (e.divisors.card : ℝ) ^ (8 : ℕ)
          * ((((Work.FIArea3.polarBoxFinset Pa φ).filter
              (fun z => d ∣ Work.FIPlan.gnorm z ∧ e ∣ Work.FIPlan.absDelta z₁ z)).card : ℕ) : ℝ))
      ≤ (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
          (d.divisors.card : ℝ) ^ (8 : ℕ) * (e.divisors.card : ℝ) ^ (8 : ℕ)
            * (Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
                  * ((d.divisors.card : ℝ) * (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)))
              + 80 * (Pa.θ * Real.sqrt Pa.N) * (d.divisors.card : ℝ) / Real.sqrt (d : ℝ)
              + (d.divisors.card : ℝ))) :=
        Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hpt d hd e he))
    _ = Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 * Work.FIArea3.dsum1 K1 K2
        + 80 * (Pa.θ * Real.sqrt Pa.N) * Work.FIArea3.dsum2 K1 K2
        + Work.FIArea3.dsum3 K1 K2 := by
        rw [Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => hring d e))]
        rw [Work.FIArea3.dsum1, Work.FIArea3.dsum2, Work.FIArea3.dsum3]
        simp only [Work.FIArea2.tauR]
        simp_rw [Finset.sum_add_distrib]
        rw [pj_two_sum_const_mul, pj_two_sum_const_mul]

end

end Work.FIArea3
