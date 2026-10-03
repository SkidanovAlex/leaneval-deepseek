import Mathlib
import Submission.Work.FIArea2.Count.sec9_Z_defs
import Submission.Work.FIArea2.Count.class_delta_sum_le
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.Divisors.sum_filter_dvd_reindex
import Submission.Work.FIArea2.ladder_divisor_factor
import Submission.Commons.Data.Nat.gcd_eq_sum_totient_divisors_ne_zero
import Submission.Work.FIArea2.Count.r_sum_degenerate_le
import Submission.Work.FIArea2.Count.factor_le_nine
import Submission.Work.FIArea2.Count.log_D_pow_eight_le_real

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIArea2.Count

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Abbreviations -/

/-- The degenerate condition in `ZBc` (with `dlt ≠ 0` removed). -/
abbrev CondB (h1 h2 s1 s2 r1 r2 : ℤ) (thr : ℝ) : Prop :=
  thr < |(r1 : ℝ)| ∧ thr < |(s1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ thr < |(s2 : ℝ)|
    ∧ tA h1 h2 r1 r2 = 0

/-- The weight `τ(Δ)³/|Δ|`. -/
abbrev TauDiv (r1 s1 r2 s2 : ℤ) : ℝ :=
  (((dlt r1 s1 r2 s2).divisors.card : ℝ)) ^ 3 / ((dlt r1 s1 r2 s2 : ℕ) : ℝ)

/-! ## Elementary facts -/

private lemma natAbs_le_of_mem_Icc' {R x : ℤ} (h : x ∈ Finset.Icc (-R) R) (hR : 0 ≤ R) :
    x.natAbs ≤ R.natAbs := by
  rw [Finset.mem_Icc] at h
  have hx : |x| ≤ R := abs_le.mpr h
  have hR' : ((R.natAbs : ℕ) : ℤ) = R := Int.natAbs_of_nonneg hR
  have : ((x.natAbs : ℕ) : ℤ) ≤ ((R.natAbs : ℕ) : ℤ) := by
    rw [Nat.cast_natAbs, hR']; exact hx
  exact_mod_cast this

private lemma dlt_ne_zero_iff (r1 s1 r2 s2 : ℤ) : dlt r1 s1 r2 s2 ≠ 0 ↔ r1 * s2 - r2 * s1 ≠ 0 := by
  unfold dlt
  rw [Ne, Int.natAbs_eq_zero]

private lemma dvd_dlt_iff (d : ℕ) (r1 s1 r2 s2 : ℤ) :
    d ∣ dlt r1 s1 r2 s2 ↔ (d : ℤ) ∣ (r1 * s2 - r2 * s1) := by
  unfold dlt
  rw [← Int.natCast_dvd_natCast]
  exact Int.dvd_natAbs

private lemma ZW_eq_zero_of_dlt_zero (h1 h2 r1 s1 r2 s2 : ℤ) (h : dlt r1 s1 r2 s2 = 0) :
    ZW h1 h2 r1 s1 r2 s2 = 0 := by
  unfold ZW; rw [h]; simp

/-- In the degenerate half, `tB ≠ 0`. -/
theorem tB_ne_zero_degenerate (h1 h2 r1 s1 r2 s2 : ℤ)
    (hA : tA h1 h2 r1 r2 = 0) (hh : h1 ≠ 0 ∨ h2 ≠ 0) (hd : dlt r1 s1 r2 s2 ≠ 0) :
    tB h1 h2 s1 s2 ≠ 0 := by
  intro htB
  have hA' : r1 * h1 ^ 2 - r2 * h2 ^ 2 = 0 := by unfold tA at hA; linarith
  have key : (h1 : ℤ) ^ 2 * (r1 * s2 - r2 * s1) = -r2 * tB h1 h2 s1 s2 := by
    unfold tB; linear_combination (s2 : ℤ) * hA'
  have hdzero : r1 * s2 - r2 * s1 = 0 := by
    by_cases h1z : h1 = 0
    · have h2n : h2 ≠ 0 := by rcases hh with h | h; exact absurd h1z h; exact h
      have hr2 : r2 = 0 := by
        have h1 : r2 * (h2 : ℤ) ^ 2 = 0 := by rw [h1z] at hA'; nlinarith [hA']
        exact (mul_eq_zero.mp h1).resolve_right (pow_ne_zero 2 (by exact_mod_cast h2n))
      have hs2 : s2 = 0 := by
        have h1 : s2 * (h2 : ℤ) ^ 2 = 0 := by rw [h1z] at htB; unfold tB at htB; nlinarith [htB]
        exact (mul_eq_zero.mp h1).resolve_right (pow_ne_zero 2 (by exact_mod_cast h2n))
      rw [hs2, hr2]; ring
    · have hsq : (h1 : ℤ) ^ 2 * (r1 * s2 - r2 * s1) = 0 := by rw [key, htB]; ring
      exact (mul_eq_zero.mp hsq).resolve_left (pow_ne_zero 2 (by exact_mod_cast h1z))
  exact hd (by rw [dlt, hdzero]; simp)

/-- The pointwise expansion of `ZW` as a divisor sum. -/
private lemma ZW_eq_totient_sum (h1 h2 r1 s1 r2 s2 : ℤ) (hh : h1 ≠ 0 ∨ h2 ≠ 0)
    (hA : tA h1 h2 r1 r2 = 0) (hd : dlt r1 s1 r2 s2 ≠ 0) :
    ZW h1 h2 r1 s1 r2 s2
      = TauDiv r1 s1 r2 s2
        * ∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors.filter (fun d => d ∣ dlt r1 s1 r2 s2),
            (Nat.totient d : ℝ) := by
  rw [ZW, TauDiv]
  simp only [cdg]
  rw [hA]
  simp only [Int.natAbs_zero, Nat.gcd_zero_left]
  rw [Nat.gcd_comm]
  rw [Commons.Data.Nat.gcd_eq_sum_totient_divisors_ne_zero (m := (tB h1 h2 s1 s2).natAbs)
      (c := dlt r1 s1 r2 s2)
      (Int.natAbs_ne_zero.mpr (tB_ne_zero_degenerate h1 h2 r1 s1 r2 s2 hA hh hd))]
  push_cast
  ring

/-- Permutation of four nested sums. -/
private lemma sum4_perm {α : Type*} [DecidableEq α] (s : Finset α) (F : α → α → α → α → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, F a b c d)
      = ∑ b ∈ s, ∑ d ∈ s, ∑ a ∈ s, ∑ c ∈ s, F a b c d := by
  have h1 : (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, F a b c d)
      = ∑ a ∈ s, ∑ b ∈ s, ∑ d ∈ s, ∑ c ∈ s, F a b c d := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
  rw [h1]
  have h2 : (∑ a ∈ s, ∑ b ∈ s, ∑ d ∈ s, ∑ c ∈ s, F a b c d)
      = ∑ b ∈ s, ∑ a ∈ s, ∑ d ∈ s, ∑ c ∈ s, F a b c d := Finset.sum_comm
  rw [h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Finset.sum_comm

/-- Nonnegativity of the final bound. -/
private lemma bnd_nonneg (C₁ ϑ Nr : ℝ) (s1 s2 : ℤ) (tb : ℕ)
    (hC₁ : 0 < C₁) (hϑ : 0 < ϑ) (hNr : 1 ≤ Nr) :
    0 ≤ 9 * C₁ * 7 ^ 8 * ϑ ^ (-(1 : ℝ) / 2) * (Real.log (Nr + 2)) ^ 8
        * (((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * ((tb.divisors.card : ℝ) ^ 4)) := by
  have h1 : (0 : ℝ) ≤ ϑ ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hϑ.le _
  have h2 : (0 : ℝ) ≤ (Real.log (Nr + 2)) ^ 8 :=
    pow_nonneg (Real.log_nonneg (by linarith)) 8
  have h3 : (0 : ℝ) ≤ 9 * C₁ * 7 ^ 8 := by positivity
  have h4 : (0 : ℝ) ≤ ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) := Nat.cast_nonneg _
  have h5 : (0 : ℝ) ≤ ((tb.divisors.card : ℝ) ^ 4) := pow_nonneg (Nat.cast_nonneg _) 4
  have h34 : (0 : ℝ) ≤ 9 * C₁ * 7 ^ 8 * ϑ ^ (-(1 : ℝ) / 2) * (Real.log (Nr + 2)) ^ 8 := by
    exact mul_nonneg (mul_nonneg h3 h1) h2
  exact mul_nonneg h34 (mul_nonneg h4 h5)

/-! ## The inner bound for a fixed `(s₁,s₂)` -/

private lemma inner_le
    (C₁ : ℝ) (hC₁pos : 0 < C₁)
    (hC₁ : ∀ (R : ℤ) (s1 s2 : ℤ) (D d : ℕ), 0 ≤ R → 1 ≤ D → 1 ≤ d → s2 ≠ 0 →
      (∀ r1 ∈ Finset.Icc (-R) R, ∀ r2 ∈ Finset.Icc (-R) R, dlt r1 s1 r2 s2 ≤ D) →
      (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          (if (d : ℤ) ∣ (r1 * s2 - r2 * s1) ∧ (r1 * s2 - r2 * s1) ≠ 0 then
            TauDiv r1 s1 r2 s2
          else 0))
        ≤ C₁ * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
              / ((s2.natAbs : ℕ) : ℝ))
            * ((((d.divisors.card : ℝ)) ^ 3 / (d : ℝ))) * (Real.log ((D : ℕ) : ℝ) + 2) ^ 8)
    (R : ℤ) (h1 h2 s1 s2 : ℤ) (thr Nr ϑ : ℝ)
    (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hNr : 1 ≤ Nr) (hR : 0 ≤ R)
    (hthr : thr = Real.sqrt (ϑ * Nr)) (hbox : 2 * (R : ℝ) + 1 ≤ 8 * Real.sqrt Nr)
    (hh : h1 ≠ 0 ∨ h2 ≠ 0) (hs1 : s1 ∈ Finset.Icc (-R) R) (hs2 : s2 ∈ Finset.Icc (-R) R) :
    (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
      (if CondB h1 h2 s1 s2 r1 r2 thr then ZW h1 h2 r1 s1 r2 s2 else 0))
    ≤ 9 * C₁ * 7 ^ 8 * ϑ ^ (-(1 : ℝ) / 2) * (Real.log (Nr + 2)) ^ 8
        * (((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ)
            * (((tB h1 h2 s1 s2).natAbs.divisors.card : ℝ) ^ 4)) := by
  by_cases hthr2 : thr < |(s2 : ℝ)|
  · have hthrpos : 0 < thr := by
      rw [hthr]; exact Real.sqrt_pos.mpr (mul_pos hϑ0 (by linarith))
    have hs2ne : s2 ≠ 0 := by intro h; rw [h] at hthr2; simp at hthr2; linarith
    set D : ℕ := 2 * (R.natAbs * R.natAbs) + 1 with hDdef
    have hD1 : 1 ≤ D := by rw [hDdef]; omega
    have hbound : ∀ r1 ∈ Finset.Icc (-R) R, ∀ r2 ∈ Finset.Icc (-R) R, dlt r1 s1 r2 s2 ≤ D := by
      intro r1 hr1 r2 hr2
      have e1 : r1.natAbs ≤ R.natAbs := natAbs_le_of_mem_Icc' hr1 hR
      have e2 : r2.natAbs ≤ R.natAbs := natAbs_le_of_mem_Icc' hr2 hR
      have e3 : s1.natAbs ≤ R.natAbs := natAbs_le_of_mem_Icc' hs1 hR
      have e4 : s2.natAbs ≤ R.natAbs := natAbs_le_of_mem_Icc' hs2 hR
      have h1 : (r1 * s2).natAbs ≤ R.natAbs * R.natAbs := by
        rw [Int.natAbs_mul]; exact Nat.mul_le_mul e1 e4
      have h2 : (r2 * s1).natAbs ≤ R.natAbs * R.natAbs := by
        rw [Int.natAbs_mul]; exact Nat.mul_le_mul e2 e3
      calc dlt r1 s1 r2 s2 = (r1 * s2 - r2 * s1).natAbs := rfl
        _ ≤ (r1 * s2).natAbs + (r2 * s1).natAbs := Int.natAbs_sub_le _ _
        _ ≤ R.natAbs * R.natAbs + R.natAbs * R.natAbs := add_le_add h1 h2
        _ ≤ D := by rw [hDdef]; omega
    have hDle : ((D : ℕ) : ℝ) ≤ 33 * Nr := by
      have hRreal : ((R.natAbs : ℕ) : ℝ) = (R : ℝ) := by
        simp [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast hR)]
      have hle2 : 2 * (R : ℝ) ≤ 8 * Real.sqrt Nr := by linarith
      have hR4 : (R.natAbs : ℝ) ≤ 4 * Real.sqrt Nr := by rw [hRreal]; linarith
      have hsq : (R.natAbs : ℝ) ^ 2 ≤ 16 * Nr := by
        have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (R.natAbs : ℝ)) hR4 2
        have hs : Real.sqrt Nr ^ 2 = Nr := Real.sq_sqrt (by linarith)
        calc (R.natAbs : ℝ) ^ 2 ≤ (4 * Real.sqrt Nr) ^ 2 := h
          _ = 16 * Nr := by rw [mul_pow, hs]; norm_num
      have hDcast : ((D : ℕ) : ℝ) = 2 * (R.natAbs : ℝ) * (R.natAbs : ℝ) + 1 := by
        rw [hDdef]; push_cast; ring
      rw [hDcast]
      nlinarith [hsq, hNr]
    -- step 0 : insert `dlt ≠ 0`
    have hp0 : ∀ r1 r2 : ℤ,
        (if CondB h1 h2 s1 s2 r1 r2 thr then ZW h1 h2 r1 s1 r2 s2 else 0)
          = (if CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0 then
              ZW h1 h2 r1 s1 r2 s2 else 0) := by
      intro r1 r2
      by_cases hc : CondB h1 h2 s1 s2 r1 r2 thr
      · by_cases hz : dlt r1 s1 r2 s2 = 0
        · rw [if_pos hc, if_neg (fun h => h.2 hz)]
          exact ZW_eq_zero_of_dlt_zero h1 h2 r1 s1 r2 s2 hz
        · rw [if_pos hc, if_pos ⟨hc, hz⟩]
      · rw [if_neg hc, if_neg (fun h => hc h.1)]
    rw [Finset.sum_congr rfl (fun r1 _ => Finset.sum_congr rfl (fun r2 _ => hp0 r1 r2))]
    -- step A : pointwise expansion
    have hpoint : ∀ r1 r2 : ℤ,
        (if CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0 then
            ZW h1 h2 r1 s1 r2 s2 else 0)
        ≤ ∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
            (if (CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0)
                  ∧ (d : ℤ) ∣ (r1 * s2 - r2 * s1) then
              (Nat.totient d : ℝ) * TauDiv r1 s1 r2 s2
            else 0) := by
      intro r1 r2
      by_cases hc : CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0
      · have hAc : tA h1 h2 r1 r2 = 0 := hc.1.2.2.2.2
        have hdc : dlt r1 s1 r2 s2 ≠ 0 := hc.2
        rw [if_pos hc, ZW_eq_totient_sum h1 h2 r1 s1 r2 s2 hh hAc hdc]
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro d _
        by_cases hdl : d ∣ dlt r1 s1 r2 s2
        · have hdZ : (d : ℤ) ∣ (r1 * s2 - r2 * s1) := (dvd_dlt_iff d r1 s1 r2 s2).mp hdl
          rw [if_pos hdl, if_pos ⟨hc, hdZ⟩]
          exact le_of_eq (mul_comm _ _)
        · rw [if_neg hdl, mul_zero]
          by_cases h2 : (CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0)
              ∧ (d : ℤ) ∣ (r1 * s2 - r2 * s1)
          · rw [if_pos h2]
            exact mul_nonneg (Nat.cast_nonneg _) (by unfold TauDiv; positivity)
          · rw [if_neg h2]
      · rw [if_neg hc]
        refine Finset.sum_nonneg fun d _ => ?_
        rw [if_neg (fun h => hc h.1)]
    -- step B : swap the sums
    have hstep1 : (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
        (if CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0 then
            ZW h1 h2 r1 s1 r2 s2 else 0))
        ≤ ∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
            ∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
              (if (CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0)
                    ∧ (d : ℤ) ∣ (r1 * s2 - r2 * s1) then
                (Nat.totient d : ℝ) * TauDiv r1 s1 r2 s2
              else 0) := by
      calc (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
            (if CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0 then
                ZW h1 h2 r1 s1 r2 s2 else 0))
          ≤ ∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
              ∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
                (if (CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0)
                      ∧ (d : ℤ) ∣ (r1 * s2 - r2 * s1) then
                  (Nat.totient d : ℝ) * TauDiv r1 s1 r2 s2
                else 0) :=
            Finset.sum_le_sum fun r1 _ => Finset.sum_le_sum fun r2 _ => hpoint r1 r2
        _ = ∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
              ∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
                (if (CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0)
                      ∧ (d : ℤ) ∣ (r1 * s2 - r2 * s1) then
                  (Nat.totient d : ℝ) * TauDiv r1 s1 r2 s2
                else 0) := by
            refine (Finset.sum_congr rfl fun r1 _ => Finset.sum_comm).trans ?_
            exact Finset.sum_comm
    -- step C : bound each inner double sum
    have hinner : ∀ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
        (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          (if (CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0)
                ∧ (d : ℤ) ∣ (r1 * s2 - r2 * s1) then
            (Nat.totient d : ℝ) * TauDiv r1 s1 r2 s2
          else 0))
        ≤ (Nat.totient d : ℝ)
            * (C₁ * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
                  / ((s2.natAbs : ℕ) : ℝ))
              * ((((d.divisors.card : ℝ)) ^ 3 / (d : ℝ))) * (Real.log ((D : ℕ) : ℝ) + 2) ^ 8) := by
      intro d hdmem
      have hdvd : d ∣ (tB h1 h2 s1 s2).natAbs := (Nat.mem_divisors.mp hdmem).1
      have htBne : (tB h1 h2 s1 s2).natAbs ≠ 0 := (Nat.mem_divisors.mp hdmem).2
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero htBne)
      have hp : ∀ r1 r2 : ℤ,
          (if (CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0)
                ∧ (d : ℤ) ∣ (r1 * s2 - r2 * s1) then
              (Nat.totient d : ℝ) * TauDiv r1 s1 r2 s2
            else 0)
          ≤ (Nat.totient d : ℝ)
              * (if (d : ℤ) ∣ (r1 * s2 - r2 * s1) ∧ (r1 * s2 - r2 * s1) ≠ 0 then
                  TauDiv r1 s1 r2 s2 else 0) := by
        intro r1 r2
        by_cases hc : (CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0)
              ∧ (d : ℤ) ∣ (r1 * s2 - r2 * s1)
        · have hΔ : (r1 * s2 - r2 * s1) ≠ 0 := (dlt_ne_zero_iff r1 s1 r2 s2).mp hc.1.2
          rw [if_pos hc, if_pos ⟨hc.2, hΔ⟩]
        · rw [if_neg hc]
          apply mul_nonneg (Nat.cast_nonneg _)
          by_cases hΔ : (d : ℤ) ∣ (r1 * s2 - r2 * s1) ∧ (r1 * s2 - r2 * s1) ≠ 0
          · rw [if_pos hΔ]; unfold TauDiv; positivity
          · rw [if_neg hΔ]
      calc (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
              (if (CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0)
                    ∧ (d : ℤ) ∣ (r1 * s2 - r2 * s1) then
                (Nat.totient d : ℝ) * TauDiv r1 s1 r2 s2
              else 0))
          ≤ ∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
              (Nat.totient d : ℝ)
                * (if (d : ℤ) ∣ (r1 * s2 - r2 * s1) ∧ (r1 * s2 - r2 * s1) ≠ 0 then
                    TauDiv r1 s1 r2 s2 else 0) :=
            Finset.sum_le_sum fun r1 _ => Finset.sum_le_sum fun r2 _ => hp r1 r2
        _ = (Nat.totient d : ℝ)
              * (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
                  (if (d : ℤ) ∣ (r1 * s2 - r2 * s1) ∧ (r1 * s2 - r2 * s1) ≠ 0 then
                      TauDiv r1 s1 r2 s2 else 0)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r1 _ => ?_
            rw [Finset.mul_sum]
        _ ≤ (Nat.totient d : ℝ)
              * (C₁ * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
                    / ((s2.natAbs : ℕ) : ℝ))
                * ((((d.divisors.card : ℝ)) ^ 3 / (d : ℝ))) * (Real.log ((D : ℕ) : ℝ) + 2) ^ 8) :=
            mul_le_mul_of_nonneg_left (hC₁ R s1 s2 D d hR hD1 hd1 hs2ne hbound) (Nat.cast_nonneg _)
    -- step D : sum over d
    have hdivsum : (∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
        (Nat.totient d : ℝ) * ((((d.divisors.card : ℝ)) ^ 3 / (d : ℝ))))
        ≤ (((tB h1 h2 s1 s2).natAbs.divisors.card : ℝ)) ^ 4 := by
      have := Work.FIArea2.ladder_divisor_factor ((tB h1 h2 s1 s2).natAbs) 2
      simpa [Work.FIArea2.tauR] using this
    have hfac' := factor_le_nine R s1 s2 thr Nr ϑ hϑ0 hϑ1 hNr hR hthr hbox hthr2
    have hlog' := log_D_pow_eight_le_real D Nr hNr hDle
    have hSnn : (0 : ℝ) ≤ ∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
        (Nat.totient d : ℝ) * ((((d.divisors.card : ℝ)) ^ 3 / (d : ℝ))) :=
      Finset.sum_nonneg fun d _ => by positivity
    have hLDnn : (0 : ℝ) ≤ (Real.log ((D : ℕ) : ℝ) + 2) ^ 8 := by
      apply pow_nonneg
      have : (0 : ℝ) ≤ Real.log ((D : ℕ) : ℝ) := by
        rcases Nat.eq_zero_or_pos D with h | h
        · rw [h]; simp
        · exact Real.log_nonneg (by exact_mod_cast h)
      linarith
    have hτnn : (0 : ℝ) ≤ (((tB h1 h2 s1 s2).natAbs.divisors.card : ℝ) ^ 4) :=
      pow_nonneg (Nat.cast_nonneg _) 4
    have hgfac : (0 : ℝ) ≤ 1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ)
        * (((2 * R + 1).natAbs : ℕ) : ℝ) / ((s2.natAbs : ℕ) : ℝ) := le_of_lt (by positivity)
    have hmain : (∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
          (Nat.totient d : ℝ)
            * (C₁ * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
                  / ((s2.natAbs : ℕ) : ℝ))
              * ((((d.divisors.card : ℝ)) ^ 3 / (d : ℝ))) * (Real.log ((D : ℕ) : ℝ) + 2) ^ 8))
        ≤ 9 * C₁ * 7 ^ 8 * ϑ ^ (-(1 : ℝ) / 2) * (Real.log (Nr + 2)) ^ 8
            * (((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ)
              * (((tB h1 h2 s1 s2).natAbs.divisors.card : ℝ) ^ 4)) := by
      have eql : (∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
              (Nat.totient d : ℝ)
                * (C₁ * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
                      / ((s2.natAbs : ℕ) : ℝ))
                  * ((((d.divisors.card : ℝ)) ^ 3 / (d : ℝ))) * (Real.log ((D : ℕ) : ℝ) + 2) ^ 8))
            = (C₁ * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
                    / ((s2.natAbs : ℕ) : ℝ))
                * (Real.log ((D : ℕ) : ℝ) + 2) ^ 8)
              * (∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
                  (Nat.totient d : ℝ) * ((((d.divisors.card : ℝ)) ^ 3 / (d : ℝ)))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          ring
      have hA1 : C₁ * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
                    / ((s2.natAbs : ℕ) : ℝ))
            * (Real.log ((D : ℕ) : ℝ) + 2) ^ 8
          ≤ (C₁ * (9 * ϑ ^ (-(1 : ℝ) / 2) * ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ)))
            * (7 ^ 8 * (Real.log (Nr + 2)) ^ 8) := by
        have e1 : C₁ * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
                    / ((s2.natAbs : ℕ) : ℝ))
            ≤ C₁ * (9 * ϑ ^ (-(1 : ℝ) / 2) * ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hfac' hC₁pos.le
        exact mul_le_mul e1 hlog' (by positivity) (by positivity)
      have hAnn : (0 : ℝ) ≤ C₁ * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ)
            * (((2 * R + 1).natAbs : ℕ) : ℝ) / ((s2.natAbs : ℕ) : ℝ))
            * (Real.log ((D : ℕ) : ℝ) + 2) ^ 8 := by
        exact mul_nonneg (mul_nonneg hC₁pos.le hgfac) hLDnn
      have hAnn2 : (0 : ℝ) ≤ (C₁ * (9 * ϑ ^ (-(1 : ℝ) / 2)
            * ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ))) * (7 ^ 8 * (Real.log (Nr + 2)) ^ 8) := by
        apply mul_nonneg (mul_nonneg hC₁pos.le (by positivity)) (by positivity)
      calc (∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
              (Nat.totient d : ℝ)
                * (C₁ * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
                      / ((s2.natAbs : ℕ) : ℝ))
                  * ((((d.divisors.card : ℝ)) ^ 3 / (d : ℝ))) * (Real.log ((D : ℕ) : ℝ) + 2) ^ 8))
            = (C₁ * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
                    / ((s2.natAbs : ℕ) : ℝ))
                * (Real.log ((D : ℕ) : ℝ) + 2) ^ 8)
              * (∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
                  (Nat.totient d : ℝ) * ((((d.divisors.card : ℝ)) ^ 3 / (d : ℝ)))) := eql
          _ ≤ (C₁ * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
                    / ((s2.natAbs : ℕ) : ℝ))
                * (Real.log ((D : ℕ) : ℝ) + 2) ^ 8)
              * ((((tB h1 h2 s1 s2).natAbs.divisors.card : ℝ)) ^ 4) :=
              mul_le_mul_of_nonneg_left hdivsum hAnn
          _ ≤ ((C₁ * (9 * ϑ ^ (-(1 : ℝ) / 2) * ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ)))
                * (7 ^ 8 * (Real.log (Nr + 2)) ^ 8))
              * ((((tB h1 h2 s1 s2).natAbs.divisors.card : ℝ)) ^ 4) :=
              mul_le_mul_of_nonneg_right hA1 hτnn
          _ = 9 * C₁ * 7 ^ 8 * ϑ ^ (-(1 : ℝ) / 2) * (Real.log (Nr + 2)) ^ 8
              * (((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ)
                * (((tB h1 h2 s1 s2).natAbs.divisors.card : ℝ) ^ 4)) := by ring
    calc (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
            (if CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0 then
                ZW h1 h2 r1 s1 r2 s2 else 0))
        ≤ ∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
            ∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
              (if (CondB h1 h2 s1 s2 r1 r2 thr ∧ dlt r1 s1 r2 s2 ≠ 0)
                    ∧ (d : ℤ) ∣ (r1 * s2 - r2 * s1) then
                (Nat.totient d : ℝ) * TauDiv r1 s1 r2 s2
              else 0) := hstep1
      _ ≤ ∑ d ∈ (tB h1 h2 s1 s2).natAbs.divisors,
            (Nat.totient d : ℝ)
              * (C₁ * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
                    / ((s2.natAbs : ℕ) : ℝ))
                * ((((d.divisors.card : ℝ)) ^ 3 / (d : ℝ))) * (Real.log ((D : ℕ) : ℝ) + 2) ^ 8) :=
            Finset.sum_le_sum hinner
      _ ≤ _ := hmain
  · have hzero : (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
        (if CondB h1 h2 s1 s2 r1 r2 thr then ZW h1 h2 r1 s1 r2 s2 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro r1 _
      apply Finset.sum_eq_zero
      intro r2 _
      rw [if_neg]
      intro hc
      unfold CondB at hc
      exact hthr2 hc.2.2.2.1
    rw [hzero]
    exact bnd_nonneg C₁ ϑ Nr s1 s2 ((tB h1 h2 s1 s2).natAbs) hC₁pos hϑ0 hNr

/-- **§9 (9.5), the degenerate half `Re Λ = 0`, in coordinates.**

With `I = Finset.Icc (-R) R`, `0 ≤ R`, `0 < ϑ ≤ 1`, `Nr ≥ 1`, `thr = √(ϑ Nr)`, `2R+1 ≤ 8√Nr`,
`h₁ ≠ 0 ∨ h₂ ≠ 0`:

  `ZBc R h₁ h₂ thr = Σ_{(r₁,s₁,r₂,s₂) ∈ I⁴} [thr < |r₁|, |s₁|, |r₂|, |s₂|] [Re Λ = 0] τ(Δ)³(Λ,Δ)/|Δ|`

is `≤ C ϑ^{-1/2}(log(Nr+2))ᴷ · UB R h₁ h₂`, where
`UB R h₁ h₂ = Σ_{(u₁,u₂) ∈ I²} (u₁,u₂)·τ(u₁h₁²−u₂h₂²)⁴`.

Here the grouping must be done in `(s₁,s₂)` (not `(r₁,r₂)`): the `d`-sum is over divisors of
`Im Λ = s₁h₁² − s₂h₂²`, which is non-zero on every non-vanishing term, because `Re Λ = 0` and
`Δ ≠ 0` give, from the identity `h₁²Δ = (Re Λ)s₂ − (Im Λ)r₂` (and its `h₂²`-companion), that
`Im Λ ≠ 0` when `h₁ ≠ 0 ∨ h₂ ≠ 0`. The count in `(r₁,r₂)` is
`Work.FIArea2.Count.class_delta_sum_le` with the roles of `(r₁,r₂)` and `(s₁,s₂)` exchanged
(the linear form is `r₁s₂ − r₂s₁ = s₂r₁ + (−s₁)r₂`, coefficient `s₂` of `r₁`), and the count factor
is again `≤ 9 ϑ^{-1/2}(s₁,s₂)` because `thr < |s₂|`. -/
theorem ZBc_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ (R : ℤ) (h1 h2 : ℤ) (thr Nr ϑ : ℝ) (Dm : ℕ),
      0 < ϑ → ϑ ≤ 1 → 1 ≤ Nr → 0 ≤ R → thr = Real.sqrt (ϑ * Nr) →
      (2 * (R : ℝ) + 1) ≤ 8 * Real.sqrt Nr → 1 ≤ Dm →
      (h1 ≠ 0 ∨ h2 ≠ 0) →
      (∀ r1 ∈ Finset.Icc (-R) R, ∀ s1 ∈ Finset.Icc (-R) R, ∀ r2 ∈ Finset.Icc (-R) R,
        ∀ s2 ∈ Finset.Icc (-R) R, cdg h1 h2 r1 s1 r2 s2 ≤ Dm) →
      ZBc R h1 h2 thr
        ≤ C * ϑ ^ (-(1 : ℝ) / 2) * (Real.log (Nr + 2)) ^ K * UB R h1 h2 := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := r_sum_degenerate_le
  refine ⟨9 * C₁ * 7 ^ 8, by positivity, 8, ?_⟩
  intro R h1 h2 thr Nr ϑ Dm hϑ0 hϑ1 hNr hR hthr hbox hDm hh hcdg
  have hZBc : ZBc R h1 h2 thr
      = ∑ s1 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
          ∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
            (if CondB h1 h2 s1 s2 r1 r2 thr then ZW h1 h2 r1 s1 r2 s2 else 0) := by
    unfold ZBc
    exact sum4_perm (Finset.Icc (-R) R) (fun r1 s1 r2 s2 =>
      if CondB h1 h2 s1 s2 r1 r2 thr then ZW h1 h2 r1 s1 r2 s2 else 0)
  rw [hZBc]
  calc (∑ s1 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
          ∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
            (if CondB h1 h2 s1 s2 r1 r2 thr then ZW h1 h2 r1 s1 r2 s2 else 0))
      ≤ ∑ s1 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
          9 * C₁ * 7 ^ 8 * ϑ ^ (-(1 : ℝ) / 2) * (Real.log (Nr + 2)) ^ 8
            * (((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ)
              * (((tB h1 h2 s1 s2).natAbs.divisors.card : ℝ) ^ 4)) := by
        apply Finset.sum_le_sum
        intro s1 hs1
        apply Finset.sum_le_sum
        intro s2 hs2
        exact inner_le C₁ hC₁pos hC₁ R h1 h2 s1 s2 thr Nr ϑ hϑ0 hϑ1 hNr hR hthr hbox hh hs1 hs2
    _ = 9 * C₁ * 7 ^ 8 * ϑ ^ (-(1 : ℝ) / 2) * (Real.log (Nr + 2)) ^ 8 * UB R h1 h2 := by
        unfold UB
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s1 _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s2 _
        rfl

end

end Work.FIArea2.Count
