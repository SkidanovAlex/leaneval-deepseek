import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.mu_gtil_coprime_le
import Submission.Work.FIChain.mu_gtil_interval_le
import Submission.Work.FIChain.S3plusC_route_defs
import Submission.Work.FIChain.FIgtil_tau_div_sum_le
import Submission.Work.FIChain.FIgtil_prime_sum_loglog
import Submission.Work.FIChain.FIgtil_prime_div_sqrt_sum

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section


lemma sum_moebius_divisors_eq (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun (f : ArithmeticFunction ℝ) => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

lemma sum_pairs_eq_antidiagonal (N D n : ℕ) (h : ℕ → ℕ → ℝ) (hn : n ≤ N) (hnD : n ≤ D) :
    (∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 D, (if e * d = n then h e d else 0))
      = ∑ p ∈ n.divisorsAntidiagonal, h p.1 p.2 := by
  have key : (∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 D,
        (if e * d = n then h e d else 0))
      = ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 D),
          (if p.1 * p.2 = n then h p.1 p.2 else 0) :=
    (Finset.sum_product (Finset.Icc 1 N) (Finset.Icc 1 D)
      (fun p : ℕ × ℕ => (if p.1 * p.2 = n then h p.1 p.2 else 0))).symm
  rw [key, ← Finset.sum_filter]
  have hset : ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 D)).filter
        (fun p : ℕ × ℕ => p.1 * p.2 = n) = n.divisorsAntidiagonal := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, ⟨h2, _⟩⟩, hp⟩
      refine ⟨hp, fun hn0 => ?_⟩
      rw [hn0, Nat.mul_eq_zero] at hp
      omega
    · rintro ⟨hp, hn0⟩
      have h1 : p.1 ≠ 0 := by intro hh; rw [hh, Nat.zero_mul] at hp; exact hn0 hp.symm
      have h2 : p.2 ≠ 0 := by intro hh; rw [hh, Nat.mul_zero] at hp; exact hn0 hp.symm
      refine ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr h1, ?_⟩, ⟨Nat.one_le_iff_ne_zero.mpr h2, ?_⟩⟩, hp⟩
      · calc p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right p.1 (Nat.pos_of_ne_zero h2)
          _ = n := hp
          _ ≤ N := hn
      · calc p.2 ≤ p.1 * p.2 := Nat.le_mul_of_pos_left p.2 (Nat.pos_of_ne_zero h1)
          _ = n := hp
          _ ≤ D := hnD
  rw [hset]

lemma sum_antidiagonal_moebius (n : ℕ) :
    (∑ p ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius p.2 : ℝ))
      = if n = 1 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [Nat.divisorsAntidiagonal]
  · rw [Nat.sum_divisorsAntidiagonal (fun a b => (ArithmeticFunction.moebius b : ℝ))]
    rw [← Finset.sum_bij (fun i _ => n / i)]
    · exact sum_moebius_divisors_eq n
    · intro i hi
      rw [Nat.mem_divisors]
      exact ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hi), hn.ne'⟩
    · intro i hi j hj hij
      rw [Nat.mem_divisors] at hi hj
      rw [← Nat.div_div_self hi.1 hi.2, ← Nat.div_div_self hj.1 hj.2, hij]
    · intro b hb
      rw [Nat.mem_divisors] at hb
      refine ⟨n / b, ?_, ?_⟩
      · rw [Nat.mem_divisors]
        exact ⟨Nat.div_dvd_of_dvd hb.1, hn.ne'⟩
      · exact Nat.div_div_self hb.1 hb.2
    · intro i hi
      rw [Nat.mem_divisors] at hi
      rw [Nat.div_div_self hi.1 hi.2]

/-- The elementary collapse. -/
lemma collapse_double (A N D : ℕ) (G : ℕ → ℝ) (hA : 1 ≤ A) (hN : D / A ≤ N) :
    (∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 D,
        (if A * (e * d) ≤ D then (ArithmeticFunction.moebius d : ℝ) * G (e * d) else 0))
      = if A ≤ D then G 1 else 0 := by
  have hApos : 0 < A := hA
  set M := D / A with hM
  have hMN : M ≤ N := hN
  have hMD : M ≤ D := Nat.div_le_self D A
  have hcond : ∀ e d : ℕ, (A * (e * d) ≤ D) ↔ (e * d ≤ M) := by
    intro e d
    rw [hM, Nat.le_div_iff_mul_le hApos]
    constructor
    · intro h; rwa [mul_comm] at h
    · intro h; rwa [mul_comm] at h
  have hstep1 : (∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 D,
        (if A * (e * d) ≤ D then (ArithmeticFunction.moebius d : ℝ) * G (e * d) else 0))
      = (∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 D,
        (if e * d ≤ M then (ArithmeticFunction.moebius d : ℝ) * G (e * d) else 0)) := by
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h : A * (e * d) ≤ D
    · rw [if_pos h, if_pos ((hcond e d).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((hcond e d).mpr hh))]
  rw [hstep1]
  have hstep2 : ∀ e d : ℕ, 1 ≤ e → 1 ≤ d →
      (if e * d ≤ M then (ArithmeticFunction.moebius d : ℝ) * G (e * d) else 0)
        = ∑ n ∈ Finset.Icc 1 M,
            (if e * d = n then (ArithmeticFunction.moebius d : ℝ) * G (e * d) else 0) := by
    intro e d he hd
    rw [Finset.sum_ite_eq]
    have hmem : (e * d ∈ Finset.Icc 1 M) ↔ (e * d ≤ M) := by
      rw [Finset.mem_Icc]
      exact ⟨fun h => h.2, fun h => ⟨by simpa using Nat.mul_le_mul he hd, h⟩⟩
    by_cases h : e * d ≤ M
    · rw [if_pos h, if_pos (hmem.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (hmem.mp hh))]
  set F : ℕ → ℕ → ℕ → ℝ := fun e d n =>
    (if e * d = n then (ArithmeticFunction.moebius d : ℝ) * G (e * d) else 0) with hF
  calc (∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 D,
        (if e * d ≤ M then (ArithmeticFunction.moebius d : ℝ) * G (e * d) else 0))
      = ∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 D, ∑ n ∈ Finset.Icc 1 M, F e d n := by
        refine Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun d hd => ?_
        rw [hF]
        exact hstep2 e d (Finset.mem_Icc.mp he).1 (Finset.mem_Icc.mp hd).1
    _ = ∑ e ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 D, F e d n := by
        refine Finset.sum_congr rfl fun e _ => ?_
        exact Finset.sum_comm
    _ = ∑ n ∈ Finset.Icc 1 M, ∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 D, F e d n :=
        Finset.sum_comm
    _ = ∑ n ∈ Finset.Icc 1 M, G n *
          (∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 D,
            (if e * d = n then (ArithmeticFunction.moebius d : ℝ) else 0)) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        simp only [hF, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => ?_
        by_cases h : e * d = n
        · rw [if_pos h, if_pos h, h]; ring
        · rw [if_neg h, if_neg h, mul_zero]
    _ = ∑ n ∈ Finset.Icc 1 M, G n * (if n = 1 then 1 else 0) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have h1 : n ≤ N := le_trans (Finset.mem_Icc.mp hn).2 hMN
        have h2 : n ≤ D := le_trans (Finset.mem_Icc.mp hn).2 hMD
        rw [sum_pairs_eq_antidiagonal N D n
              (fun e d => (ArithmeticFunction.moebius d : ℝ)) h1 h2, sum_antidiagonal_moebius n]
    _ = if A ≤ D then G 1 else 0 := by
        have hmem : (1 ∈ Finset.Icc 1 M) ↔ A ≤ D := by
          simp only [Finset.mem_Icc, hM, Nat.le_div_iff_mul_le hApos, one_mul]
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨le_refl 1, h⟩
        simp only [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq']
        exact if_congr hmem rfl rfl


lemma sum_dvd_reindex (ν N : ℕ) (F : ℕ → ℝ) (hν : 1 ≤ ν) :
    (∑ e ∈ Finset.Icc 1 N, (if ν ∣ e then F e else 0))
      = ∑ e₁ ∈ Finset.Icc 1 (N / ν), F (ν * e₁) := by
  have hνpos : 0 < ν := hν
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun e _ => e / ν) ?_ ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter, Finset.mem_Icc] at he
    obtain ⟨⟨he1, he2⟩, hdvd⟩ := he
    obtain ⟨k, rfl⟩ := hdvd
    rw [Finset.mem_Icc, Nat.mul_div_right k hνpos]
    refine ⟨?_, (Nat.le_div_iff_mul_le hνpos).mpr (by rwa [mul_comm] at he2)⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp at he1
    · exact hk
  · intro e₁ he₁ e₂ he₂ h
    have d1 : e₁ = ν * (e₁ / ν) := by
      rw [Nat.mul_div_cancel' (Finset.mem_filter.mp he₁).2]
    have d2 : e₂ = ν * (e₂ / ν) := by
      rw [Nat.mul_div_cancel' (Finset.mem_filter.mp he₂).2]
    rw [d1, d2, h]
  · intro e₁ he₁
    refine ⟨ν * e₁, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, dvd_mul_right ν e₁⟩
      · simpa using Nat.mul_le_mul hν (Finset.mem_Icc.mp he₁).1
      · calc ν * e₁ ≤ ν * (N / ν) := Nat.mul_le_mul_left ν (Finset.mem_Icc.mp he₁).2
          _ = N / ν * ν := by ring
          _ ≤ N := Nat.div_mul_le_self N ν
    · exact Nat.mul_div_right e₁ hνpos
  · intro e he
    rw [Finset.mem_filter] at he
    rw [Nat.mul_div_cancel' he.2]

/-- Inner collapse for fixed `ν ≥ 1`, `b ≥ 1`. -/
lemma collapse_b_inner (D b ν : ℕ) (hν : 1 ≤ ν) (hb : 1 ≤ b) :
    (∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D,
        (if ν ∣ e * b ∧ e * b * d ≤ D then
          (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0))
      = if Nat.lcm ν b ≤ D then Submission.ASP.FIgtil (Nat.lcm ν b) else 0 := by
  set g := Nat.gcd ν b with hg
  have hgpos : 0 < g := by
    rw [hg]; exact Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left ν b) (by omega)
  set ν' := ν / g with hν'def
  have hν'pos : 1 ≤ ν' := by
    rw [hν'def]
    exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left ν b)) hgpos
  have hν'pos0 : 0 < ν' := hν'pos
  set A := Nat.lcm ν b with hAdef
  have hνeq : g * ν' = ν := by rw [hν'def]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left ν b)
  have hbeq : g * (b / g) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right ν b)
  have hAeq : A = ν' * b := by
    rw [hAdef, Nat.lcm_eq_mul_div, ← hg, hν'def, ← hνeq, Nat.mul_assoc,
      Nat.mul_div_right (ν' * b) hgpos, Nat.mul_div_right ν' hgpos]
  have hA1 : 1 ≤ A := by
    rw [hAeq]; simpa using Nat.mul_le_mul hν'pos hb
  have hAle : ν' ≤ A := by rw [hAeq]; exact Nat.le_mul_of_pos_right ν' (by omega)
  have hdvdiff : ∀ e : ℕ, (ν ∣ e * b) ↔ (ν' ∣ e) := by
    intro e
    have heq : e * b = g * (e * (b / g)) := by
      calc e * b = e * (g * (b / g)) := by rw [hbeq]
        _ = g * (e * (b / g)) := by ring
    have hcop : (ν').Coprime (b / g) := by
      rw [hν'def, hg]; exact Nat.coprime_div_gcd_div_gcd hgpos
    rw [← hνeq, heq, Nat.mul_dvd_mul_iff_left hgpos, hcop.dvd_mul_right]
  have hstep1 : (∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D,
        (if ν ∣ e * b ∧ e * b * d ≤ D then
          (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0))
      = ∑ e ∈ Finset.Icc 1 D, (if ν' ∣ e then
          (∑ d ∈ Finset.Icc 1 D,
            (if e * b * d ≤ D then
              (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0))
          else 0) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : ν' ∣ e
    · have h2 : ν ∣ e * b := (hdvdiff e).mpr h
      rw [if_pos h]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hd : e * b * d ≤ D
      · rw [if_pos ⟨h2, hd⟩, if_pos hd]
      · rw [if_neg (fun hh => hd hh.2), if_neg hd]
    · have h2 : ¬ (ν ∣ e * b) := fun hh => h ((hdvdiff e).mp hh)
      rw [if_neg h]
      exact Finset.sum_eq_zero fun d _ => if_neg fun hh => h2 hh.1
  rw [hstep1]
  have hstep2 : (∑ e ∈ Finset.Icc 1 D, (if ν' ∣ e then
          (∑ d ∈ Finset.Icc 1 D,
            (if e * b * d ≤ D then
              (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0))
          else 0))
      = ∑ e₁ ∈ Finset.Icc 1 (D / ν'), ∑ d ∈ Finset.Icc 1 D,
          (if (ν' * e₁) * b * d ≤ D then
            (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil ((ν' * e₁) * b * d) else 0) :=
    sum_dvd_reindex ν' D
      (fun e => ∑ d ∈ Finset.Icc 1 D,
        (if e * b * d ≤ D then
          (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0)) hν'pos
  rw [hstep2]
  have hconv : (∑ e₁ ∈ Finset.Icc 1 (D / ν'), ∑ d ∈ Finset.Icc 1 D,
          (if (ν' * e₁) * b * d ≤ D then
            (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil ((ν' * e₁) * b * d) else 0))
      = ∑ e₁ ∈ Finset.Icc 1 (D / ν'), ∑ d ∈ Finset.Icc 1 D,
          (if A * (e₁ * d) ≤ D then
            (ArithmeticFunction.moebius d : ℝ) * (fun m => Submission.ASP.FIgtil (A * m)) (e₁ * d)
            else 0) := by
    refine Finset.sum_congr rfl fun e₁ _ => Finset.sum_congr rfl fun d _ => ?_
    have hAc : (ν' * e₁) * b * d = A * (e₁ * d) := by rw [hAeq]; ring
    rw [hAc]
  rw [hconv]
  have hAN : D / A ≤ D / ν' := Nat.div_le_div_left hAle hν'pos0
  rw [collapse_double A (D / ν') D (fun m => Submission.ASP.FIgtil (A * m)) hA1 hAN]
  simp only [mul_one]

lemma rhoOf_eq_Icc (lam : ℕ → ℝ) (Δ n : ℕ) (hn : 1 ≤ n) (hlam : ∀ ν, Δ < ν → lam ν = 0) :
    Submission.ASP.rhoOf lam n = ∑ ν ∈ Finset.Icc 1 Δ, (if ν ∣ n then lam ν else 0) := by
  rw [Submission.ASP.rhoOf]
  have h1 : (∑ ν ∈ n.divisors, lam ν) = ∑ ν ∈ (n.divisors).filter (· ≤ Δ), lam ν := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ν _ => ?_
    by_cases h : ν ≤ Δ
    · rw [if_pos h]
    · rw [if_neg h, hlam ν (by omega)]
  rw [h1]
  have hset : (n.divisors).filter (· ≤ Δ) = (Finset.Icc 1 Δ).filter (· ∣ n) := by
    ext ν
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hdvd, -⟩, hle⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), hle⟩, hdvd⟩
    · rintro ⟨⟨-, hle⟩, hdvd⟩
      exact ⟨⟨hdvd, by omega⟩, hle⟩
  rw [hset, Finset.sum_filter]

lemma collapse_b (D b Δ : ℕ) (lam : ℕ → ℝ) (hb : 1 ≤ b)
    (hlam : ∀ ν, Δ < ν → lam ν = 0) :
    (∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D,
        (if e * b * d ≤ D then Submission.ASP.rhoOf lam (e * b)
          * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0))
      = ∑ ν ∈ Finset.Icc 1 Δ, lam ν *
          (if Nat.lcm ν b ≤ D then Submission.ASP.FIgtil (Nat.lcm ν b) else 0) := by
  have hrho : ∀ e ∈ Finset.Icc 1 D, Submission.ASP.rhoOf lam (e * b)
      = ∑ ν ∈ Finset.Icc 1 Δ, (if ν ∣ e * b then lam ν else 0) := by
    intro e he
    refine rhoOf_eq_Icc lam Δ (e * b) ?_ hlam
    simpa using Nat.mul_le_mul (Finset.mem_Icc.mp he).1 hb
  have hstepA : ∀ e ∈ Finset.Icc 1 D, ∀ d ∈ Finset.Icc 1 D,
      (if e * b * d ≤ D then Submission.ASP.rhoOf lam (e * b)
          * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0)
      = ∑ ν ∈ Finset.Icc 1 Δ,
          (if e * b * d ≤ D ∧ ν ∣ e * b then lam ν
            * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0) := by
    intro e he d hd
    rw [hrho e he]
    by_cases h : e * b * d ≤ D
    · rw [if_pos h, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ν _ => ?_
      by_cases hν : ν ∣ e * b
      · rw [if_pos hν, if_pos (And.intro h hν)]
      · rw [if_neg hν]
        rw [if_neg (fun hh => hν hh.2)]
        ring
    · rw [if_neg h]
      refine (Finset.sum_eq_zero fun ν _ => ?_).symm
      rw [if_neg (fun hh => h hh.1)]
  have hstepB : (∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D, ∑ ν ∈ Finset.Icc 1 Δ,
        (if e * b * d ≤ D ∧ ν ∣ e * b then lam ν
          * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0))
      = ∑ ν ∈ Finset.Icc 1 Δ, lam ν * (∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D,
          (if ν ∣ e * b ∧ e * b * d ≤ D then
            (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0)) := by
    calc (∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D, ∑ ν ∈ Finset.Icc 1 Δ,
        (if e * b * d ≤ D ∧ ν ∣ e * b then lam ν
          * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0))
        = ∑ e ∈ Finset.Icc 1 D, ∑ ν ∈ Finset.Icc 1 Δ, ∑ d ∈ Finset.Icc 1 D,
            (if e * b * d ≤ D ∧ ν ∣ e * b then lam ν
              * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          exact Finset.sum_comm
        _ = ∑ ν ∈ Finset.Icc 1 Δ, ∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D,
            (if e * b * d ≤ D ∧ ν ∣ e * b then lam ν
              * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0) :=
          Finset.sum_comm
        _ = ∑ ν ∈ Finset.Icc 1 Δ, lam ν * (∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D,
          (if ν ∣ e * b ∧ e * b * d ≤ D then
            (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0)) := by
          refine Finset.sum_congr rfl fun ν _ => ?_
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => ?_
          by_cases h : e * b * d ≤ D ∧ ν ∣ e * b
          · rw [if_pos (And.intro h.1 h.2), if_pos (And.intro h.2 h.1)]; ring
          · rw [if_neg h, if_neg (fun hh => h (And.intro hh.2 hh.1))]; ring
  calc (∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D,
        (if e * b * d ≤ D then Submission.ASP.rhoOf lam (e * b)
          * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0))
      = ∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D, ∑ ν ∈ Finset.Icc 1 Δ,
          (if e * b * d ≤ D ∧ ν ∣ e * b then lam ν
            * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0) := by
        refine Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun d hd => ?_
        exact hstepA e he d hd
    _ = ∑ ν ∈ Finset.Icc 1 Δ, lam ν * (∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D,
          (if ν ∣ e * b ∧ e * b * d ≤ D then
            (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d) else 0)) :=
        hstepB
    _ = ∑ ν ∈ Finset.Icc 1 Δ, lam ν *
          (if Nat.lcm ν b ≤ D then Submission.ASP.FIgtil (Nat.lcm ν b) else 0) := by
        refine Finset.sum_congr rfl fun ν hν => ?_
        rw [collapse_b_inner D b ν (Finset.mem_Icc.mp hν).1 hb]


theorem ebd_collapse (D b_lo b_hi Δ : ℕ) (lam : ℕ → ℝ)
    (hlam : ∀ ν : ℕ, Δ < ν → lam ν = 0) (hb : 1 ≤ b_lo) :
    (∑ e ∈ Finset.Icc 1 D, ∑ b ∈ Finset.Icc b_lo b_hi, ∑ d ∈ Finset.Icc 1 D,
        (if e * b * d ≤ D then
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
            * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d)
        else 0))
    = ∑ ν ∈ Finset.Icc 1 Δ, lam ν * ∑ b ∈ Finset.Icc b_lo b_hi,
        (if Nat.lcm ν b ≤ D then
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν b) else 0) := by
  have hfac : (∑ b ∈ Finset.Icc b_lo b_hi, ∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D,
        (if e * b * d ≤ D then
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
            * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d)
        else 0))
      = ∑ b ∈ Finset.Icc b_lo b_hi, (ArithmeticFunction.moebius b : ℝ) *
          (∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D,
            (if e * b * d ≤ D then Submission.ASP.rhoOf lam (e * b)
              * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d)
            else 0)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h : e * b * d ≤ D
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  have hcol : (∑ b ∈ Finset.Icc b_lo b_hi, (ArithmeticFunction.moebius b : ℝ) *
          (∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D,
            (if e * b * d ≤ D then Submission.ASP.rhoOf lam (e * b)
              * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d)
            else 0)))
      = ∑ b ∈ Finset.Icc b_lo b_hi, (ArithmeticFunction.moebius b : ℝ) *
          (∑ ν ∈ Finset.Icc 1 Δ, lam ν *
            (if Nat.lcm ν b ≤ D then Submission.ASP.FIgtil (Nat.lcm ν b) else 0)) := by
    refine Finset.sum_congr rfl fun b hb' => ?_
    rw [collapse_b D b Δ lam (le_trans hb (Finset.mem_Icc.mp hb').1) hlam]
  have hswap : (∑ b ∈ Finset.Icc b_lo b_hi, (ArithmeticFunction.moebius b : ℝ) *
          (∑ ν ∈ Finset.Icc 1 Δ, lam ν *
            (if Nat.lcm ν b ≤ D then Submission.ASP.FIgtil (Nat.lcm ν b) else 0)))
      = ∑ ν ∈ Finset.Icc 1 Δ, lam ν * ∑ b ∈ Finset.Icc b_lo b_hi,
        (if Nat.lcm ν b ≤ D then
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν b) else 0) := by
    simp only [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : Nat.lcm ν b ≤ D
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [Finset.sum_comm, hfac, hcol, hswap]


lemma sum_gcd_fiber (ν w b_lo b_hi : ℕ) (H : ℕ → ℝ) (hw : w ∈ ν.divisors) :
    (∑ b ∈ Finset.Icc b_lo b_hi, (if Nat.gcd ν b = w then H b else 0))
      = ∑ b' ∈ Finset.Icc ((b_lo + w - 1) / w) (b_hi / w),
          (if Nat.gcd (ν / w) b' = 1 then H (w * b') else 0) := by
  have hwd : w ∣ ν := (Nat.mem_divisors.mp hw).1
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact (Nat.mem_divisors.mp hw).2 (Nat.zero_dvd.mp hwd)
  have hwpos : 0 < w := Nat.pos_of_ne_zero hw0
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij (fun b _ => b / w) ?_ ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨hb1, hb2⟩, hg⟩ := hb
    have hwb : w ∣ b := by rw [← hg]; exact Nat.gcd_dvd_right ν b
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, Nat.div_le_div_right hb2⟩, ?_⟩
    · rw [Nat.div_le_iff_le_mul_add_pred hwpos, Nat.mul_div_cancel' hwb]
      omega
    · have h1 : Nat.gcd ν b = w * Nat.gcd (ν / w) (b / w) := by
        conv_lhs => rw [← Nat.mul_div_cancel' hwd, ← Nat.mul_div_cancel' hwb]
        rw [Nat.gcd_mul_left]
      have hg2 : w * Nat.gcd (ν / w) (b / w) = w * 1 := by rw [← h1, hg, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hwpos hg2
  · intro b₁ hb₁ b₂ hb₂ h
    rw [Finset.mem_filter] at hb₁ hb₂
    have h1 : w ∣ b₁ := by rw [← hb₁.2]; exact Nat.gcd_dvd_right ν b₁
    have h2 : w ∣ b₂ := by rw [← hb₂.2]; exact Nat.gcd_dvd_right ν b₂
    rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, h]
  · intro b' hb'
    rw [Finset.mem_filter, Finset.mem_Icc] at hb'
    obtain ⟨⟨hb'1, hb'2⟩, hg'⟩ := hb'
    refine ⟨w * b', ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [Nat.div_le_iff_le_mul_add_pred hwpos] at hb'1
        omega
      · have h := (Nat.le_div_iff_mul_le hwpos).mp hb'2
        rwa [mul_comm] at h
      · have h1 : Nat.gcd ν (w * b') = w * Nat.gcd (ν / w) b' := by
          conv_lhs => rw [← Nat.mul_div_cancel' hwd]
          rw [Nat.gcd_mul_left]
        rw [h1, hg', mul_one]
    · exact Nat.mul_div_right b' hwpos
  · intro b hb
    rw [Finset.mem_filter] at hb
    have hwb : w ∣ b := by rw [← hb.2]; exact Nat.gcd_dvd_right ν b
    rw [Nat.mul_div_cancel' hwb]


lemma sigmaTilde_nonneg (ℓ : ℕ) : 0 ≤ Work.FIChain.sigmaTilde ℓ := by
  rw [Work.FIChain.sigmaTilde]
  exact Finset.prod_nonneg fun p _ => by positivity

lemma b_lo_ge_w {ν w b_lo : ℕ} (hν : 1 ≤ ν) (hνb : ν * ν ≤ b_lo) (hw : w ∈ ν.divisors) :
    w ≤ b_lo := by
  have hwd : w ∣ ν := (Nat.mem_divisors.mp hw).1
  have hwν : w ≤ ν := Nat.le_of_dvd (by omega) hwd
  nlinarith [hν, hνb, hwν, Nat.zero_le w]

theorem T_nu_bound : ∃ C : ℝ, 0 < C ∧ ∀ (ν b_lo b_hi D : ℕ), 1 ≤ ν → 4 ≤ b_lo → ν * ν ≤ b_lo →
    |∑ b ∈ Finset.Icc b_lo b_hi,
        (if Nat.lcm ν b ≤ D then
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν b) else 0)|
      ≤ C * ((ν.divisors.card : ℝ)) * Submission.ASP.FIgtil ν * Work.FIChain.sigmaTilde ν
          * (Real.log (b_lo : ℝ)) ^ (-6 : ℝ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := mu_gtil_interval_le
  refine ⟨64 * C₀, by positivity, fun ν b_lo b_hi D hν hb hνb => ?_⟩
  have hνpos : 0 < ν := hν
  have hνposR : (0:ℝ) < (ν:ℝ) := by exact_mod_cast hνpos
  have hlogb : 0 < Real.log (b_lo : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < b_lo))
  have hσ0 : 0 ≤ Work.FIChain.sigmaTilde ν := sigmaTilde_nonneg ν
  have hg0 : 0 ≤ Submission.ASP.FIgtil ν := Submission.ASP.FIgtil_nonneg ν
  have hνsqrt : (ν:ℝ) ≤ Real.sqrt (b_lo:ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity), pow_two]
    exact_mod_cast hνb
  have hsqrt2 : (2:ℝ) ≤ Real.sqrt (b_lo:ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have : (4:ℝ) ≤ (b_lo:ℝ) := by exact_mod_cast hb
    linarith
  have hlogbnd : ∀ w ∈ ν.divisors,
      (Real.log (((max ((b_lo + w - 1) / w) 2 : ℕ)) : ℝ)) ^ (-6 : ℝ)
        ≤ 64 * (Real.log (b_lo : ℝ)) ^ (-6 : ℝ) := by
    intro w hw
    have hwd : w ∣ ν := (Nat.mem_divisors.mp hw).1
    have hwpos : 0 < w := Nat.pos_of_dvd_of_pos hwd hνpos
    have hwν : w ≤ ν := Nat.le_of_dvd hνpos hwd
    have hY1w : b_lo ≤ w * ((b_lo + w - 1) / w) := by
      have h := (Nat.div_le_iff_le_mul_add_pred hwpos).mp (le_refl ((b_lo + w - 1) / w))
      omega
    have hsqrt_le : Real.sqrt (b_lo:ℝ) ≤ (((max ((b_lo + w - 1) / w) 2 : ℕ)) : ℝ) := by
      have h1 : (b_lo:ℝ) / (ν:ℝ) ≤ (b_lo:ℝ) / (w:ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hwpos) (by exact_mod_cast hwν)
      have h2 : Real.sqrt (b_lo:ℝ) ≤ (b_lo:ℝ) / (ν:ℝ) := by
        rw [le_div_iff₀ hνposR]
        calc Real.sqrt (b_lo:ℝ) * (ν:ℝ) ≤ Real.sqrt (b_lo:ℝ) * Real.sqrt (b_lo:ℝ) :=
              mul_le_mul_of_nonneg_left hνsqrt (Real.sqrt_nonneg _)
          _ = (b_lo:ℝ) := Real.mul_self_sqrt (by positivity)
      have h3 : (b_lo:ℝ) / (w:ℝ) ≤ (((b_lo + w - 1) / w : ℕ) : ℝ) := by
        rw [div_le_iff₀ (by exact_mod_cast hwpos)]
        have h : (b_lo:ℝ) ≤ (w:ℝ) * (((b_lo + w - 1) / w : ℕ) : ℝ) := by
          exact_mod_cast hY1w
        linarith
      have h4 : ((((b_lo + w - 1) / w : ℕ)) : ℝ) ≤ (((max ((b_lo + w - 1) / w) 2 : ℕ)) : ℝ) := by
        exact_mod_cast Nat.le_max_left ((b_lo + w - 1) / w) 2
      linarith
    have hlog_ge : (1/2) * Real.log (b_lo:ℝ)
        ≤ Real.log (((max ((b_lo + w - 1) / w) 2 : ℕ)) : ℝ) := by
      have hx0 : 0 < Real.sqrt (b_lo:ℝ) := Real.sqrt_pos.mpr (by positivity)
      have h := Real.log_le_log hx0 hsqrt_le
      rw [Real.log_sqrt (by positivity)] at h
      linarith
    have h0 : 0 < (1/2) * Real.log (b_lo:ℝ) := by linarith
    have hmono := Real.rpow_le_rpow_of_nonpos h0 hlog_ge (by norm_num : (-6:ℝ) ≤ 0)
    have hkey : ((1/2) * Real.log (b_lo:ℝ)) ^ (-6 : ℝ) = 64 * (Real.log (b_lo:ℝ)) ^ (-6 : ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 1/2) hlogb.le]
      rw [show ((1:ℝ)/2) ^ (-6 : ℝ) = 64 by norm_num [Real.rpow_neg, Real.rpow_natCast]]
    linarith [hmono, hkey]
  have hT : (∑ b ∈ Finset.Icc b_lo b_hi,
        (if Nat.lcm ν b ≤ D then
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν b) else 0))
      = ∑ w ∈ ν.divisors, ∑ b ∈ Finset.Icc b_lo b_hi,
          (if Nat.gcd ν b = w then
            (if Nat.lcm ν b ≤ D then
              (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν b) else 0)
            else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_ite_eq]
    rw [if_pos (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left ν b, hνpos.ne'⟩)]
  rw [hT]
  have hpt : ∀ (w b' : ℕ), w ∣ ν →
      (if Nat.gcd (ν / w) b' = 1 then
        (if Nat.lcm ν (w * b') ≤ D then
          (ArithmeticFunction.moebius (w * b') : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν (w * b'))
          else 0) else 0)
      = (ArithmeticFunction.moebius w : ℝ) * Submission.ASP.FIgtil ν *
          (if Nat.gcd ν b' = 1 then
            (if ν * b' ≤ D then
              (ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b' else 0) else 0) := by
    intro w b' hwd
    have hwpos : 0 < w := Nat.pos_of_dvd_of_pos hwd hνpos
    by_cases hc2 : Nat.gcd (ν / w) b' = 1
    · rw [if_pos hc2]
      have hlcm : Nat.lcm ν (w * b') = ν * b' := by
        rw [Nat.lcm_eq_mul_div]
        have hg : Nat.gcd ν (w * b') = w := by
          have h1 : Nat.gcd ν (w * b') = w * Nat.gcd (ν / w) b' := by
            conv_lhs => rw [← Nat.mul_div_cancel' hwd]
            rw [Nat.gcd_mul_left]
          rw [h1, hc2, mul_one]
        rw [hg]
        have h2 : ν * (w * b') = w * (ν * b') := by ring
        rw [h2, Nat.mul_div_right (ν * b') hwpos]
      rw [hlcm]
      by_cases hc : Nat.gcd ν b' = 1
      · rw [if_pos hc]
        have hcop : Nat.Coprime ν b' := Nat.coprime_iff_gcd_eq_one.mpr hc
        have hwcop : Nat.Coprime w b' := by
          rw [Nat.coprime_iff_gcd_eq_one]
          have hdiv : Nat.gcd w b' ∣ Nat.gcd ν b' :=
            Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left w b') hwd) (Nat.gcd_dvd_right w b')
          rw [hc] at hdiv
          exact Nat.dvd_one.mp hdiv
        have hmul : (ArithmeticFunction.moebius (w * b') : ℝ) * Submission.ASP.FIgtil (ν * b')
            = (ArithmeticFunction.moebius w : ℝ) * Submission.ASP.FIgtil ν *
                ((ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b') := by
          rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
                (Nat.coprime_iff_gcd_eq_one.mp hwcop), Submission.ASP.FIgtil_mul hcop]
          push_cast
          ring
        rw [hmul]
        by_cases hd : ν * b' ≤ D
        · rw [if_pos hd, if_pos hd]
        · rw [if_neg hd, if_neg hd]; ring
      · rw [if_neg hc]
        have hnsq : ¬ Squarefree (ν * b') := by
          obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
          have hpν : p ∣ ν := dvd_trans hpd (Nat.gcd_dvd_left ν b')
          have hpb' : p ∣ b' := dvd_trans hpd (Nat.gcd_dvd_right ν b')
          rw [Nat.squarefree_iff_prime_squarefree]
          push_neg
          exact ⟨p, hp, mul_dvd_mul hpν hpb'⟩
        rw [Submission.ASP.FIgtil_eq_zero hnsq]
        by_cases hd : ν * b' ≤ D
        · simp [if_pos hd]
        · simp [if_neg hd]
    · rw [if_neg hc2]
      have hcne : Nat.gcd ν b' ≠ 1 := by
        intro h1
        exact hc2 (Nat.dvd_one.mp (h1 ▸ Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left (ν / w) b')
          (Nat.div_dvd_of_dvd hwd)) (Nat.gcd_dvd_right (ν / w) b')))
      rw [if_neg hcne, mul_zero]
  have hfiber : ∀ w ∈ ν.divisors,
      |∑ b ∈ Finset.Icc b_lo b_hi,
          (if Nat.gcd ν b = w then
            (if Nat.lcm ν b ≤ D then
              (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν b) else 0)
            else 0)|
      ≤ 64 * C₀ * Submission.ASP.FIgtil ν * Work.FIChain.sigmaTilde ν
          * (Real.log (b_lo : ℝ)) ^ (-6 : ℝ) := by
    intro w hw
    have hwd : w ∣ ν := (Nat.mem_divisors.mp hw).1
    have hwpos : 0 < w := Nat.pos_of_dvd_of_pos hwd hνpos
    set Y₁ := (b_lo + w - 1) / w with hY1def
    set Y₂ := b_hi / w with hY2def
    have hY1 : 1 ≤ Y₁ := by
      rw [hY1def, Nat.one_le_div_iff hwpos]
      have hwb : w ≤ b_lo := b_lo_ge_w hν hνb hw
      omega
    rw [sum_gcd_fiber ν w b_lo b_hi
        (fun b => (if Nat.lcm ν b ≤ D then
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν b) else 0)) hw]
    rw [Finset.sum_congr rfl (fun b' _ => hpt w b' hwd)]
    rw [← Finset.mul_sum]
    rw [abs_mul, abs_mul, abs_of_nonneg hg0]
    have habsμ : |(ArithmeticFunction.moebius w : ℝ)| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := w)
      exact_mod_cast h
    have hV : |∑ b' ∈ Finset.Icc Y₁ Y₂,
          (if Nat.gcd ν b' = 1 then
            (if ν * b' ≤ D then (ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b' else 0)
            else 0)|
        ≤ C₀ * Work.FIChain.sigmaTilde ν
            * (Real.log (((max Y₁ 2 : ℕ)) : ℝ)) ^ (-6 : ℝ) := by
      have hsub : Finset.Icc Y₁ (min Y₂ (D / ν)) ⊆ Finset.Icc Y₁ Y₂ := by
        intro x hx; rw [Finset.mem_Icc] at hx ⊢
        exact ⟨hx.1, le_trans hx.2 (min_le_left _ _)⟩
      have hV1 : (∑ b' ∈ Finset.Icc Y₁ Y₂,
            (if Nat.gcd ν b' = 1 then
              (if ν * b' ≤ D then (ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b' else 0)
              else 0))
          = ∑ b' ∈ Finset.Icc Y₁ Y₂,
              (if Nat.gcd ν b' = 1 ∧ ν * b' ≤ D then
                (ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b' else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases h1 : Nat.gcd ν x = 1
        · by_cases h2 : ν * x ≤ D
          · rw [if_pos h1, if_pos h2, if_pos (And.intro h1 h2)]
          · rw [if_pos h1, if_neg h2, if_neg (fun hh => h2 hh.2)]
        · rw [if_neg h1, if_neg (fun hh => h1 hh.1)]
      have hV2 : (∑ b' ∈ Finset.Icc Y₁ Y₂,
              (if Nat.gcd ν b' = 1 ∧ ν * b' ≤ D then
                (ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b' else 0))
          = ∑ b' ∈ Finset.Icc Y₁ (min Y₂ (D / ν)),
              (if Nat.gcd ν b' = 1 ∧ ν * b' ≤ D then
                (ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b' else 0) := by
        refine (Finset.sum_subset hsub ?_).symm
        intro x hx hxnot
        rw [Finset.mem_Icc] at hx
        have hxd : ¬ (ν * x ≤ D) := by
          intro hcon
          exact hxnot (by
            rw [Finset.mem_Icc]
            exact ⟨hx.1, le_min hx.2 ((Nat.le_div_iff_mul_le hνpos).mpr (by rwa [mul_comm] at hcon))⟩)
        exact if_neg (fun hh => hxd hh.2)
      have hV3 : (∑ b' ∈ Finset.Icc Y₁ (min Y₂ (D / ν)),
              (if Nat.gcd ν b' = 1 ∧ ν * b' ≤ D then
                (ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b' else 0))
          = ∑ b' ∈ Finset.Icc Y₁ (min Y₂ (D / ν)),
              (if Nat.gcd ν b' = 1 then
                (ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b' else 0) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.mem_Icc] at hx
        have hxd : ν * x ≤ D := by
          have h : x ≤ D / ν := le_trans hx.2 (min_le_right _ _)
          have h2 := (Nat.le_div_iff_mul_le hνpos).mp h
          rwa [mul_comm] at h2
        by_cases h1 : Nat.gcd ν x = 1
        · rw [if_pos (And.intro h1 hxd), if_pos h1]
        · rw [if_neg (fun hh => h1 hh.1), if_neg h1]
      rw [hV1, hV2, hV3]
      by_cases hle : Y₁ ≤ min Y₂ (D / ν)
      · have h24 := hC₀ ν Y₁ (min Y₂ (D / ν)) hν hY1 hle
        have heq : (∑ b' ∈ Finset.Icc Y₁ (min Y₂ (D / ν)),
              (if Nat.gcd ν b' = 1 then
                (ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b' else 0))
            = ∑ d ∈ (Finset.Icc Y₁ (min Y₂ (D / ν))).filter
                (fun d => Squarefree d ∧ Nat.Coprime d ν),
                (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil d := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : Squarefree x ∧ Nat.Coprime x ν
          · rw [if_pos hx, if_pos (by rw [← Nat.gcd_comm]; exact Nat.coprime_iff_gcd_eq_one.mp hx.2)]
          · rw [if_neg hx]
            by_cases hg : Nat.gcd ν x = 1
            · rw [if_pos hg]
              have hnc : ¬ Squarefree x := fun hs =>
                hx ⟨hs, Nat.coprime_iff_gcd_eq_one.mpr (by rwa [Nat.gcd_comm] at hg)⟩
              rw [Submission.ASP.FIgtil_eq_zero hnc, mul_zero]
            · rw [if_neg hg]
        rw [heq]
        exact h24
      · have hemp : Finset.Icc Y₁ (min Y₂ (D / ν)) = ∅ := Finset.Icc_eq_empty (by omega)
        rw [hemp, Finset.sum_empty, abs_zero]
        positivity
    calc |(ArithmeticFunction.moebius w : ℝ)| * Submission.ASP.FIgtil ν *
            |∑ b' ∈ Finset.Icc Y₁ Y₂,
              (if Nat.gcd ν b' = 1 then
                (if ν * b' ≤ D then (ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b' else 0)
                else 0)|
        ≤ 1 * Submission.ASP.FIgtil ν *
            (C₀ * Work.FIChain.sigmaTilde ν * (Real.log (((max Y₁ 2 : ℕ)) : ℝ)) ^ (-6 : ℝ)) := by
          have hA : |(ArithmeticFunction.moebius w : ℝ)| * Submission.ASP.FIgtil ν
              ≤ 1 * Submission.ASP.FIgtil ν := mul_le_mul_of_nonneg_right habsμ hg0
          exact mul_le_mul hA hV (abs_nonneg _) (by simpa using hg0)
      _ ≤ 64 * C₀ * Submission.ASP.FIgtil ν * Work.FIChain.sigmaTilde ν
            * (Real.log (b_lo : ℝ)) ^ (-6 : ℝ) := by
          have hlog' := hlogbnd w hw
          rw [← hY1def] at hlog'
          have hc : 0 ≤ C₀ * Submission.ASP.FIgtil ν * Work.FIChain.sigmaTilde ν :=
            mul_nonneg (mul_nonneg hC₀pos.le hg0) hσ0
          calc 1 * Submission.ASP.FIgtil ν
                  * (C₀ * Work.FIChain.sigmaTilde ν
                      * (Real.log (((max Y₁ 2 : ℕ)) : ℝ)) ^ (-6 : ℝ))
              = (C₀ * Submission.ASP.FIgtil ν * Work.FIChain.sigmaTilde ν)
                  * (Real.log (((max Y₁ 2 : ℕ)) : ℝ)) ^ (-6 : ℝ) := by ring
            _ ≤ (C₀ * Submission.ASP.FIgtil ν * Work.FIChain.sigmaTilde ν)
                  * (64 * (Real.log (b_lo : ℝ)) ^ (-6 : ℝ)) :=
                mul_le_mul_of_nonneg_left hlog' hc
            _ = 64 * C₀ * Submission.ASP.FIgtil ν * Work.FIChain.sigmaTilde ν
                  * (Real.log (b_lo : ℝ)) ^ (-6 : ℝ) := by ring
  calc |∑ w ∈ ν.divisors, ∑ b ∈ Finset.Icc b_lo b_hi,
          (if Nat.gcd ν b = w then
            (if Nat.lcm ν b ≤ D then
              (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν b) else 0)
            else 0)|
      ≤ ∑ w ∈ ν.divisors, |∑ b ∈ Finset.Icc b_lo b_hi,
          (if Nat.gcd ν b = w then
            (if Nat.lcm ν b ≤ D then
              (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν b) else 0)
            else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _w ∈ ν.divisors, (64 * C₀ * Submission.ASP.FIgtil ν * Work.FIChain.sigmaTilde ν
          * (Real.log (b_lo : ℝ)) ^ (-6 : ℝ)) := Finset.sum_le_sum hfiber
    _ = 64 * C₀ * ((ν.divisors.card : ℝ)) * Submission.ASP.FIgtil ν * Work.FIChain.sigmaTilde ν
          * (Real.log (b_lo : ℝ)) ^ (-6 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring


theorem tau_FIgtil_sigmaTilde_prod {ℓ : ℕ} (hℓ : Squarefree ℓ) :
    ((ℓ.divisors.card : ℝ)) * Submission.ASP.FIgtil ℓ * Work.FIChain.sigmaTilde ℓ
      = ∏ p ∈ ℓ.primeFactors, (2 * Submission.ASP.FIgtil p * (1 + 1 / Real.sqrt (p : ℝ))) := by
  have hℓ0 : ℓ ≠ 0 := fun h => Submission.ASP.not_squarefree_zero (h ▸ hℓ)
  have hcard : (ℓ.divisors.card : ℝ) = ∏ p ∈ ℓ.primeFactors, (2 : ℝ) := by
    rw [card_divisors_of_squarefree hℓ hℓ0]
    push_cast
    rfl
  have hFI : Submission.ASP.FIgtil ℓ
      = ∏ p ∈ ℓ.primeFactors, Submission.ASP.FIgtil p := by
    rw [Submission.ASP.FIgtil, if_pos hℓ]
    exact Finset.prod_congr rfl fun p hp =>
      (Submission.ASP.FIgtil_prime (Nat.prime_of_mem_primeFactors hp)).symm
  rw [hcard, hFI, Work.FIChain.sigmaTilde, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]

theorem FIgtil_divisor_sigma_sum_le : ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, 2 ≤ Y →
    ∑ ν ∈ Finset.Icc 1 Y, ((ν.divisors.card : ℝ)) * Submission.ASP.FIgtil ν
        * Work.FIChain.sigmaTilde ν
      ≤ C * (Real.log (Y : ℝ)) ^ (2 : ℕ) := by
  obtain ⟨K1, hK1⟩ := FIgtil_prime_sum_loglog
  obtain ⟨K2, hK2⟩ := FIgtil_prime_div_sqrt_sum
  refine ⟨Real.exp (2 * K1 + 2 * K2), Real.exp_pos _, fun Y hY => ?_⟩
  set w : ℕ → ℝ := fun p => 2 * Submission.ASP.FIgtil p * (1 + 1 / Real.sqrt (p : ℝ)) with hw
  have hw_nonneg : ∀ p, 0 ≤ w p := by
    intro p; rw [hw]
    have h1 : (0 : ℝ) ≤ Submission.ASP.FIgtil p := Submission.ASP.FIgtil_nonneg p
    have h2 : (0 : ℝ) ≤ 1 + 1 / Real.sqrt (p : ℝ) := by positivity
    positivity
  have hstep1 : ∑ ν ∈ Finset.Icc 1 Y, ((ν.divisors.card : ℝ)) * Submission.ASP.FIgtil ν
          * Work.FIChain.sigmaTilde ν
      = ∑ ν ∈ (Finset.Icc 1 Y).filter Squarefree, ((ν.divisors.card : ℝ))
          * Submission.ASP.FIgtil ν * Work.FIChain.sigmaTilde ν := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    by_cases h : Squarefree ℓ
    · rw [if_pos h]
    · rw [if_neg h]; simp [Submission.ASP.FIgtil_eq_zero h]
  have hstep2 : ∑ ν ∈ (Finset.Icc 1 Y).filter Squarefree, ((ν.divisors.card : ℝ))
          * Submission.ASP.FIgtil ν * Work.FIChain.sigmaTilde ν
      ≤ ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (1 + w p) := by
    calc ∑ ν ∈ (Finset.Icc 1 Y).filter Squarefree, ((ν.divisors.card : ℝ))
            * Submission.ASP.FIgtil ν * Work.FIChain.sigmaTilde ν
        = ∑ ν ∈ (Finset.Icc 1 Y).filter Squarefree, ∏ p ∈ ν.primeFactors, w p := by
          refine Finset.sum_congr rfl fun ℓ hℓ => ?_
          exact tau_FIgtil_sigmaTilde_prod (Finset.mem_filter.mp hℓ).2
      _ ≤ ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (1 + w p) :=
          sum_sqfree_prod_le_prod Y w hw_nonneg
  have hstep3 : ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (1 + w p)
      ≤ Real.exp (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, w p) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun p _ => by linarith [hw_nonneg p]) (fun p _ => ?_)
    have := Real.add_one_le_exp (w p); linarith
  have hwsum_eq : ∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, w p
      = 2 * (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, Submission.ASP.FIgtil p)
        + 2 * (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime,
            Submission.ASP.FIgtil p / Real.sqrt (p : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hw]; ring
  have hlogx : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
  have hwsum_le : ∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, w p
      ≤ 2 * Real.log (Real.log (Y : ℝ)) + (2 * K1 + 2 * K2) := by
    rw [hwsum_eq]
    have h1 := hK1 Y hY
    have h2 := hK2 Y
    linarith
  have hexp : Real.exp (2 * Real.log (Real.log (Y : ℝ)) + (2 * K1 + 2 * K2))
      = Real.exp (2 * K1 + 2 * K2) * (Real.log (Y : ℝ)) ^ (2 : ℕ) := by
    rw [Real.exp_add]
    have h4 : Real.exp (2 * Real.log (Real.log (Y : ℝ))) = (Real.log (Y : ℝ)) ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hlogx]
    rw [h4]; ring
  calc ∑ ν ∈ Finset.Icc 1 Y, ((ν.divisors.card : ℝ)) * Submission.ASP.FIgtil ν
          * Work.FIChain.sigmaTilde ν
      = _ := hstep1
    _ ≤ ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (1 + w p) := hstep2
    _ ≤ Real.exp (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, w p) := hstep3
    _ ≤ Real.exp (2 * Real.log (Real.log (Y : ℝ)) + (2 * K1 + 2 * K2)) :=
        Real.exp_le_exp.mpr hwsum_le
    _ = Real.exp (2 * K1 + 2 * K2) * (Real.log (Y : ℝ)) ^ (2 : ℕ) := hexp




theorem main_ebd_sum_le : ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
    ∀ (b_lo b_hi D Δ : ℕ), (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < (b_lo : ℝ) →
    b_lo ≤ b_hi → D ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ → Δ * Δ ≤ b_lo →
    ∀ (lam : ℕ → ℝ), (∀ ν : ℕ, |lam ν| ≤ 1) → (∀ ν : ℕ, Δ < ν → lam ν = 0) →
    |∑ e ∈ Finset.Icc 1 D, ∑ b ∈ (Finset.Icc b_lo b_hi), ∑ d ∈ Finset.Icc 1 D,
        (if e * b * d ≤ D then
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
            * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d)
        else 0)|
      ≤ C * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by
  obtain ⟨CT, hCTpos, hCT⟩ := T_nu_bound
  obtain ⟨CE, hCEpos, hCE⟩ := FIgtil_divisor_sigma_sum_le
  refine ⟨CT * CE * (64/17)^4 + 1, by positivity, 4, ?_⟩
  intro x hx b_lo b_hi D Δ hblo hle hD hΔ lam hlam1 hlam2
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hlogx : 0 < Real.log (x:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have h1 : (1:ℝ) ≤ (x:ℝ)^((1:ℝ)/4 + 1/64) := Real.one_le_rpow hx1 (by norm_num)
  have hb4 : 4 ≤ b_lo := by
    have h3 : (3:ℝ) < (b_lo:ℝ) := by linarith [hblo, h1]
    have h3' : (3:ℕ) < b_lo := by exact_mod_cast h3
    omega
  have hlogb : 0 < Real.log (b_lo:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < b_lo))
  rw [ebd_collapse D b_lo b_hi Δ lam hlam2 (by omega : 1 ≤ b_lo)]
  set T : ℕ → ℝ := fun ν => ∑ b ∈ Finset.Icc b_lo b_hi,
        (if Nat.lcm ν b ≤ D then
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν b) else 0)
    with hTdef
  have hσ0 : ∀ ν, 0 ≤ Work.FIChain.sigmaTilde ν := sigmaTilde_nonneg
  have hg0 : ∀ ν, 0 ≤ Submission.ASP.FIgtil ν := Submission.ASP.FIgtil_nonneg
  -- step 1: triangle inequality
  have hstep1 : |∑ ν ∈ Finset.Icc 1 Δ, lam ν * T ν|
      ≤ ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * |T ν| := by
    calc |∑ ν ∈ Finset.Icc 1 Δ, lam ν * T ν| ≤ ∑ ν ∈ Finset.Icc 1 Δ, |lam ν * T ν| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * |T ν| :=
          Finset.sum_congr rfl fun ν _ => abs_mul _ _
  -- step 2: per-nu bound
  have hstep2 : ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * |T ν|
      ≤ ∑ ν ∈ Finset.Icc 1 Δ, CT * ((ν.divisors.card:ℝ)) * Submission.ASP.FIgtil ν
          * Work.FIChain.sigmaTilde ν * (Real.log (b_lo:ℝ))^(-6:ℝ) := by
    refine Finset.sum_le_sum fun ν hν => ?_
    rw [Finset.mem_Icc] at hν
    have hνν : ν * ν ≤ b_lo := by nlinarith [hν.2, hΔ]
    have hb := hCT ν b_lo b_hi D hν.1 hb4 hνν
    rw [hTdef]
    calc |lam ν| * |∑ b ∈ Finset.Icc b_lo b_hi,
          (if Nat.lcm ν b ≤ D then
            (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν b) else 0)|
        ≤ 1 * |∑ b ∈ Finset.Icc b_lo b_hi,
          (if Nat.lcm ν b ≤ D then
            (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν b) else 0)| :=
          mul_le_mul_of_nonneg_right (hlam1 ν) (abs_nonneg _)
      _ = |∑ b ∈ Finset.Icc b_lo b_hi,
          (if Nat.lcm ν b ≤ D then
            (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil (Nat.lcm ν b) else 0)| := one_mul _
      _ ≤ CT * ((ν.divisors.card:ℝ)) * Submission.ASP.FIgtil ν
            * Work.FIChain.sigmaTilde ν * (Real.log (b_lo:ℝ))^(-6:ℝ) := hb
  -- step 3: the Euler sum
  have hE : ∑ ν ∈ Finset.Icc 1 Δ, ((ν.divisors.card:ℝ)) * Submission.ASP.FIgtil ν
        * Work.FIChain.sigmaTilde ν ≤ CE * (Real.log (b_lo:ℝ)) ^ (2:ℕ) := by
    have hsub : Finset.Icc 1 Δ ⊆ Finset.Icc 1 (max Δ 2) := by
      intro ν hν; rw [Finset.mem_Icc] at hν ⊢
      exact ⟨hν.1, le_trans hν.2 (le_max_left _ _)⟩
    have h1 : ∑ ν ∈ Finset.Icc 1 Δ, ((ν.divisors.card:ℝ)) * Submission.ASP.FIgtil ν
        * Work.FIChain.sigmaTilde ν
        ≤ ∑ ν ∈ Finset.Icc 1 (max Δ 2), ((ν.divisors.card:ℝ)) * Submission.ASP.FIgtil ν
        * Work.FIChain.sigmaTilde ν :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun x _ _ => mul_nonneg (mul_nonneg (by positivity) (hg0 x)) (hσ0 x))
    have h2 := hCE (max Δ 2) (le_max_right _ _)
    have h3 : Real.log (((max Δ 2 : ℕ)) : ℝ) ≤ Real.log (b_lo:ℝ) := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < max Δ 2))
      exact_mod_cast (by
        have : Δ ≤ b_lo := by
          rcases Nat.eq_zero_or_pos Δ with h | h
          · omega
          · nlinarith
        omega : max Δ 2 ≤ b_lo)
    have h4 : (Real.log (((max Δ 2 : ℕ)) : ℝ))^(2:ℕ) ≤ (Real.log (b_lo:ℝ))^(2:ℕ) := by
      have h0 : 0 ≤ Real.log (((max Δ 2 : ℕ)) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ max Δ 2 by omega))
      exact pow_le_pow_left₀ h0 h3 2
    calc ∑ ν ∈ Finset.Icc 1 Δ, ((ν.divisors.card:ℝ)) * Submission.ASP.FIgtil ν
          * Work.FIChain.sigmaTilde ν
        ≤ ∑ ν ∈ Finset.Icc 1 (max Δ 2), ((ν.divisors.card:ℝ)) * Submission.ASP.FIgtil ν
          * Work.FIChain.sigmaTilde ν := h1
      _ ≤ CE * (Real.log (((max Δ 2 : ℕ)) : ℝ))^(2:ℕ) := h2
      _ ≤ CE * (Real.log (b_lo:ℝ))^(2:ℕ) := by
          apply mul_le_mul_of_nonneg_left h4 hCEpos.le
  -- log bounds
  have hloglt : (17/64) * Real.log (x:ℝ) < Real.log (b_lo:ℝ) := by
    have hlt0 : (x:ℝ)^((1:ℝ)/4 + 1/64) < (b_lo:ℝ) := by linarith [hblo]
    have hloglt := Real.log_lt_log (Real.rpow_pos_of_pos hxpos _) hlt0
    rw [Real.log_rpow hxpos] at hloglt
    convert hloglt using 2
    norm_num
  have hlogbnd : (Real.log (b_lo:ℝ))^(-4:ℝ) ≤ (64/17)^4 * (Real.log (x:ℝ))^(-4:ℝ) := by
    have h0 : 0 < (17/64) * Real.log (x:ℝ) := by positivity
    have h := Real.rpow_le_rpow_of_nonpos h0 hloglt.le (by norm_num : (-4:ℝ) ≤ 0)
    have h2 : ((17/64) * Real.log (x:ℝ))^(-4:ℝ) = (64/17)^4 * (Real.log (x:ℝ))^(-4:ℝ) := by
      rw [Real.mul_rpow (by norm_num) hlogx.le]
      rw [show ((17:ℝ)/64)^(-4:ℝ) = (64/17)^4 by norm_num [Real.rpow_neg, Real.rpow_natCast]]
    linarith [h, h2]
  have hcombine : (Real.log (b_lo:ℝ))^(-6:ℝ) * (Real.log (b_lo:ℝ))^(2:ℕ)
      ≤ (64/17)^4 * (Real.log (x:ℝ))^(-4:ℝ) := by
    have h2 : (Real.log (b_lo:ℝ))^(2:ℕ) = (Real.log (b_lo:ℝ))^((2:ℝ)) :=
      (Real.rpow_natCast _ 2).symm
    have h3 : (Real.log (b_lo:ℝ))^(-6:ℝ) * (Real.log (b_lo:ℝ))^((2:ℝ))
        = (Real.log (b_lo:ℝ))^((-4:ℝ)) := by
      rw [← Real.rpow_add hlogb]
      norm_num
    rw [h2, h3]
    exact hlogbnd
  have hL4nonneg : 0 ≤ (Real.log (x:ℝ))^(-4:ℝ) := le_of_lt (Real.rpow_pos_of_pos hlogx _)
  calc |∑ ν ∈ Finset.Icc 1 Δ, lam ν * T ν|
      ≤ ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * |T ν| := hstep1
    _ ≤ ∑ ν ∈ Finset.Icc 1 Δ, CT * ((ν.divisors.card:ℝ)) * Submission.ASP.FIgtil ν
          * Work.FIChain.sigmaTilde ν * (Real.log (b_lo:ℝ))^(-6:ℝ) := hstep2
    _ = CT * (Real.log (b_lo:ℝ))^(-6:ℝ) * (∑ ν ∈ Finset.Icc 1 Δ,
          ((ν.divisors.card:ℝ)) * Submission.ASP.FIgtil ν * Work.FIChain.sigmaTilde ν) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        ring
    _ ≤ CT * (Real.log (b_lo:ℝ))^(-6:ℝ) * (CE * (Real.log (b_lo:ℝ))^(2:ℕ)) := by
        apply mul_le_mul_of_nonneg_left hE
        exact mul_nonneg hCTpos.le (le_of_lt (Real.rpow_pos_of_pos hlogb _))
    _ = CT * CE * ((Real.log (b_lo:ℝ))^(-6:ℝ) * (Real.log (b_lo:ℝ))^(2:ℕ)) := by ring
    _ ≤ CT * CE * ((64/17)^4 * (Real.log (x:ℝ))^(-4:ℝ)) := by
        apply mul_le_mul_of_nonneg_left hcombine
        exact mul_nonneg hCTpos.le hCEpos.le
    _ = CT * CE * (64/17)^4 * (Real.log (x:ℝ))^(-4:ℝ) := by ring
    _ ≤ (CT * CE * (64/17)^4 + 1) * (Real.log (x:ℝ))^(-4:ℝ) := by
        nlinarith [hL4nonneg]
    _ = (CT * CE * (64/17)^4 + 1) * (Real.log (x:ℝ))^(-(4:ℤ)) := by
        rw [show (-4:ℝ) = (((-(4:ℤ) : ℤ)) : ℝ) by norm_num, Real.rpow_intCast]

end
end Work.FIChain
