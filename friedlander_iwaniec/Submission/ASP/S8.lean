/-
  Companion paper ("Asymptotic sieve for primes"), §8 (`S₃`).

  This file contains the combinatorial layer of §8: the splitting of the von Mangoldt weight,
  `Λ(c) = λ⁻(c) − λ⁺(c)` for `c ≥ 2` (for `C > 0`), where

      `λ⁺(c) = ∑_{m | c, C < m} μ(m)·log(m/C)`,   `λ⁻(c) = ∑_{m | c, m ≤ C} μ(m)·log(C/m)`,

  together with the integral representation `λ⁻(c) = ∫_1^C ρ(c;t)·t^{-1} dt` of `λ⁻` in terms of
  the truncated Möbius sum `ρ(c;t) = ∑_{m | c, m ≤ t} μ(m)` — the object to which the bilinear
  hypothesis (B′) applies.
-/
import Mathlib
import Submission.ASP.S3v
import Submission.ASP.S7c
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_moebius_mul_log_eq_neg_vonMangoldt

namespace Submission.ASP

open Finset MeasureTheory
open scoped Interval

noncomputable section

/-! ### The truncations of `Λ` -/

/-- `λ⁺(c) = ∑_{m | c, C < m} μ(m)·log(m/C)`. -/
def lamPlus (c : ℕ) (C : ℝ) : ℝ :=
  ∑ m ∈ c.divisors.filter (fun m => C < ((m : ℕ) : ℝ)),
    (ArithmeticFunction.moebius m : ℝ) * Real.log ((m : ℝ) / C)

/-- `λ⁻(c) = ∑_{m | c, m ≤ C} μ(m)·log(C/m)`. -/
def lamMinus (c : ℕ) (C : ℝ) : ℝ :=
  ∑ m ∈ c.divisors.filter (fun m => ((m : ℕ) : ℝ) ≤ C),
    (ArithmeticFunction.moebius m : ℝ) * Real.log (C / (m : ℝ))

/-- The truncated Möbius sum `ρ(c; t) = ∑_{m | c, m ≤ t} μ(m)` (the companion's (B2)). -/
def rhoTrunc (c : ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ c.divisors.filter (fun m => ((m : ℕ) : ℝ) ≤ t), (ArithmeticFunction.moebius m : ℝ)

/-! ### The Möbius sums -/

/-- `∑_{d | n} μ(d) = [n = 1]`. -/
lemma sum_moebius_divisors_eq (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply
    (f := (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) (x := n)
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply] at h
  exact h.symm

/-- `∑_{d | n} μ(d)·log(d/C) = −Λ(n)` for `n ≥ 2` and `C ≠ 0`. -/
lemma sum_moebius_mul_log_div_eq (n : ℕ) (hn : 2 ≤ n) {C : ℝ} (hC : C ≠ 0) :
    (∑ m ∈ n.divisors, (ArithmeticFunction.moebius m : ℝ) * Real.log ((m : ℝ) / C))
      = -ArithmeticFunction.vonMangoldt n := by
  have hn0 : n ≠ 0 := by omega
  have hterm : ∀ m ∈ n.divisors,
      (ArithmeticFunction.moebius m : ℝ) * Real.log ((m : ℝ) / C)
        = (ArithmeticFunction.moebius m : ℝ) * Real.log (m : ℝ)
          - (ArithmeticFunction.moebius m : ℝ) * Real.log C := by
    intro m hm
    have hmne : (m : ℝ) ≠ 0 := by
      have h := (Nat.mem_divisors.mp hm).1
      have : m ≠ 0 := (Nat.pos_of_dvd_of_pos h (by omega)).ne'
      exact_mod_cast this
    rw [Real.log_div hmne hC, mul_sub]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Commons.NumberTheory.ArithmeticFunction.sum_moebius_mul_log_eq_neg_vonMangoldt n (by omega),
    sum_moebius_divisors_eq n]
  simp [show n ≠ 1 by omega]

/-! ### The splitting `Λ(c) = λ⁻(c) − λ⁺(c)` -/

/-- **§8, the splitting of `Λ`**: for `c ≥ 2` and `C > 0`,
`Λ(c) = λ⁻(c) − λ⁺(c)`. -/
theorem vonMangoldt_eq_lamMinus_sub_lamPlus (c : ℕ) (hc : 2 ≤ c) {C : ℝ} (hC : 0 < C) :
    ArithmeticFunction.vonMangoldt c = lamMinus c C - lamPlus c C := by
  have hCne : C ≠ 0 := hC.ne'
  have hkey := sum_moebius_mul_log_div_eq c hc hCne
  have hsplit : lamMinus c C - lamPlus c C
      = ∑ m ∈ c.divisors,
          (ArithmeticFunction.moebius m : ℝ) * (-Real.log ((m : ℝ) / C)) := by
    rw [lamMinus, lamPlus, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hmne : (m : ℝ) ≠ 0 := by
      have h := (Nat.mem_divisors.mp hm).1
      have : m ≠ 0 := (Nat.pos_of_dvd_of_pos h (by omega)).ne'
      exact_mod_cast this
    by_cases hle : (m : ℝ) ≤ C
    · have hlog : Real.log (C / (m : ℝ)) = -Real.log ((m : ℝ) / C) := by
        rw [Real.log_div hCne hmne, Real.log_div hmne hCne]; ring
      rw [if_pos hle, if_neg (not_lt.mpr hle), sub_zero, hlog]
    · rw [if_neg hle, if_pos (not_le.mp hle), zero_sub, mul_neg]
  rw [hsplit]
  have hneg : (∑ m ∈ c.divisors,
        (ArithmeticFunction.moebius m : ℝ) * -Real.log ((m : ℝ) / C))
      = -∑ m ∈ c.divisors,
        (ArithmeticFunction.moebius m : ℝ) * Real.log ((m : ℝ) / C) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun m _ => by rw [mul_neg])
  rw [hneg, hkey]
  ring

/-! ### The integral representation of `λ⁻` -/

/-- The step function `t ↦ 1_{m < t}/t` (a.e. equal to `t ↦ 1_{m ≤ t}/t`). -/
def stepInv (m : ℕ) (t : ℝ) : ℝ := if ((m : ℕ) : ℝ) < t then 1 / t else 0

lemma measurable_stepInv (m : ℕ) : Measurable (stepInv m) := by
  have h : stepInv m = (Set.Ioi (((m : ℕ) : ℝ))).indicator (fun t : ℝ => 1 / t) := by
    funext t
    rw [stepInv, Set.indicator_apply]
    by_cases ht : ((m : ℕ) : ℝ) < t
    · rw [if_pos ht, if_pos (Set.mem_Ioi.mpr ht)]
    · rw [if_neg ht, if_neg (fun h => ht (Set.mem_Ioi.mp h))]
  rw [h]
  exact (measurable_const.div measurable_id).indicator measurableSet_Ioi

lemma abs_stepInv_le (m : ℕ) (hm : 1 ≤ m) (t : ℝ) : |stepInv m t| ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by norm_num) hm1
  rw [stepInv]
  by_cases ht : ((m : ℕ) : ℝ) < t
  · have ht1 : (0 : ℝ) < t := lt_of_lt_of_le hmpos ht.le
    rw [if_pos ht, abs_of_pos (one_div_pos.mpr ht1), one_div]
    exact inv_le_one_of_one_le₀ (le_of_lt (lt_of_le_of_lt hm1 ht))
  · rw [if_neg ht, abs_zero]; norm_num

lemma intervalIntegrable_stepInv (m : ℕ) (hm : 1 ≤ m) (p q : ℝ) :
    IntervalIntegrable (stepInv m) volume p q :=
  intervalIntegrable_of_bound (p := p) (q := q) (measurable_stepInv m) (abs_stepInv_le m hm)

/-- `∫_1^C 1_{m < t}/t dt = log(C/m)` if `m ≤ C`, and `0` if `C < m`. -/
lemma integral_stepInv (m : ℕ) (hm : 1 ≤ m) {C : ℝ} (hC : 1 ≤ C) :
    (∫ t in (1 : ℝ)..C, stepInv m t)
      = if ((m : ℕ) : ℝ) ≤ C then Real.log (C / (m : ℝ)) else 0 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by norm_num) hm1
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC
  have hle_mC : ∀ t ∈ Set.uIoc (1 : ℝ) ((m : ℕ) : ℝ), ¬ ((m : ℕ) : ℝ) < t := by
    intro t ht hltm
    rcases Set.mem_uIoc.mp ht with ⟨-, h2⟩ | ⟨h2, h3⟩
    · exact absurd h2 (not_le.mpr hltm)
    · exact absurd h2 (not_lt.mpr (le_trans h3 hm1))
  rcases le_or_gt ((m : ℕ) : ℝ) C with hle | hlt
  · rw [if_pos hle]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_stepInv m hm 1 ((m : ℕ) : ℝ))
      (intervalIntegrable_stepInv m hm ((m : ℕ) : ℝ) C)]
    have h0 : (∫ t in (1 : ℝ)..((m : ℕ) : ℝ), stepInv m t) = 0 := by
      refine intervalIntegral.integral_zero_ae (Filter.Eventually.of_forall (fun t ht => ?_))
      rw [stepInv, if_neg (hle_mC t ht)]
    rw [h0, zero_add]
    have hcongr : (∫ t in ((m : ℕ) : ℝ)..C, stepInv m t)
        = ∫ t in ((m : ℕ) : ℝ)..C, 1 / t := by
      rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      rw [stepInv, if_pos ht.1]
    rw [hcongr, integral_one_div_of_pos hmpos hCpos]
  · rw [if_neg (not_le.mpr hlt)]
    refine intervalIntegral.integral_zero_ae (Filter.Eventually.of_forall (fun t ht => ?_))
    rw [stepInv, if_neg]
    intro hltm
    rcases Set.mem_uIoc.mp ht with ⟨-, h2⟩ | ⟨h2, h3⟩
    · exact absurd (lt_of_le_of_lt h2 hlt) (not_lt.mpr hltm.le)
    · exact absurd (le_trans h3 hm1) (not_le.mpr hltm)

/-- **§8, the integral representation of `λ⁻`**: `λ⁻(c) = ∫_1^C ρ(c;t)·t^{-1} dt` for `C ≥ 1`. -/
theorem lamMinus_eq_integral (c : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    lamMinus c C = ∫ t in (1 : ℝ)..C, rhoTrunc c t / t := by
  classical
  set S : Set ℝ := (c.divisors : Set ℕ).image (fun m : ℕ => (m : ℝ)) with hS
  have hSfin : S.Finite := by
    rw [hS]
    exact (Finset.finite_toSet c.divisors).image (fun m : ℕ => (m : ℝ))
  have haeS : ∀ᵐ t ∂volume, t ∉ S :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (hSfin.measure_zero volume)
  have hpt : ∀ t ∉ S, rhoTrunc c t / t
      = ∑ m ∈ c.divisors, (ArithmeticFunction.moebius m : ℝ) * stepInv m t := by
    intro t htS
    have hne : ∀ m ∈ c.divisors, (m : ℝ) ≠ t := by
      intro m hm hmt
      exact htS (by rw [hS]; exact ⟨m, hm, hmt⟩)
    rw [rhoTrunc, Finset.sum_filter, Finset.sum_div]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [stepInv]
    by_cases hle : ((m : ℕ) : ℝ) ≤ t
    · have hlt : ((m : ℕ) : ℝ) < t := lt_of_le_of_ne hle (hne m hm)
      rw [if_pos hle, if_pos hlt]
      ring
    · rw [if_neg hle, if_neg (not_lt.mpr (le_of_lt (not_le.mp hle)))]
      simp
  have hcongr : (∫ t in (1 : ℝ)..C, rhoTrunc c t / t)
      = ∫ t in (1 : ℝ)..C,
          ∑ m ∈ c.divisors, (ArithmeticFunction.moebius m : ℝ) * stepInv m t := by
    rw [intervalIntegral.integral_of_le hC, intervalIntegral.integral_of_le hC]
    refine MeasureTheory.integral_congr_ae ?_
    change ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 : ℝ) C)),
      rhoTrunc c t / t = ∑ m ∈ c.divisors,
        (ArithmeticFunction.moebius m : ℝ) * stepInv m t
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact haeS.mono (fun t htS _ => hpt t htS)
  rw [hcongr]
  rw [intervalIntegral.integral_finsetSum (fun m hm =>
    (intervalIntegrable_stepInv m (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hm).1
      (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm).2)) 1 C).const_mul _)]
  rw [lamMinus, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [intervalIntegral.integral_const_mul,
    integral_stepInv m (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hm).1
      (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm).2)) hC]
  by_cases hle : ((m : ℕ) : ℝ) ≤ C
  · rw [if_pos hle, if_pos hle]
  · rw [if_neg hle, if_neg hle, mul_zero]

/-! ### The reindexing of `S₃` (the triple sum and `ρ_{ebc} = ρ_{eb}`) -/

/-- **§8, first reindexing**: `S₃` as a triple sum over `(b,c,n)`. -/
theorem S3_eq_triple (a lam : ℕ → ℝ) (N : ℕ) (z sy sz : ℝ) :
    S3 a lam N z sy sz
      = ∑ b ∈ (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ c ∈ (Finset.Icc 1 N).filter
                (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
              ArithmeticFunction.vonMangoldt c *
                ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b * c ∣ n),
                  a n * rhoOf lam n := by
  unfold S3 Lam3
  exact (sum_triple_filter (fun n => a n * rhoOf lam n) N
    (fun b => sy < ((b : ℕ) : ℝ))
    (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz)).symm

/-- **§8, second reindexing**: the constraint `bc ∣ n` is eliminated by writing `n = b·c·e`. -/
theorem S3_eq_e (a lam : ℕ → ℝ) (N : ℕ) (z sy sz : ℝ) :
    S3 a lam N z sy sz
      = ∑ b ∈ (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ c ∈ (Finset.Icc 1 N).filter
                (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
              ArithmeticFunction.vonMangoldt c *
                ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
                  a (b * (c * e)) * rhoOf lam (b * (c * e)) := by
  rw [S3_eq_triple a lam N z sy sz]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  refine congrArg (fun x => (ArithmeticFunction.moebius b : ℝ) * x) ?_
  refine Finset.sum_congr rfl (fun c hc => ?_)
  congr 1
  rw [sum_filter_dvd_eq'' (q := b * c) (by
    have h1 : 1 ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    have h2 : 1 ≤ c := (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).1
    calc (1 : ℕ) = 1 * 1 := (mul_one 1).symm
      _ ≤ b * c := Nat.mul_le_mul h1 h2) (fun n => a n * rhoOf lam n)]
  refine Finset.sum_congr ?_ (fun e _ => ?_)
  · apply Finset.filter_congr
    intro e _
    rw [Nat.mul_assoc]
  · rw [Nat.mul_assoc]

/-- If `c` is a prime exceeding the level `Δ` of the sieve `λ`, then `ρ(bcn) = ρ(bn)`. -/
lemma rhoOf_mul_prime_eq (lam : ℕ → ℝ) {Δ : ℕ} (hlam_supp : ∀ ν, Δ < ν → lam ν = 0)
    {b c n : ℕ} (hc : c.Prime) (hΔc : Δ < c) :
    rhoOf lam (b * (c * n)) = rhoOf lam (b * n) := by
  rw [rhoOf, rhoOf]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro ν hν
    have hdvd : ν ∣ b * n := (Nat.mem_divisors.mp hν).1
    have hbn0 : b * n ≠ 0 := (Nat.mem_divisors.mp hν).2
    exact Nat.mem_divisors.mpr ⟨hdvd.trans ⟨c, by ring⟩, fun h0 => hbn0 (by
      rcases Nat.mul_eq_zero.mp h0 with h | h
      · rw [h, zero_mul]
      · have hn : n = 0 := by
          rcases Nat.mul_eq_zero.mp h with h' | h'
          · exact absurd h' hc.ne_zero
          · exact h'
        rw [hn, mul_zero])⟩
  · intro ν hν hνnot
    apply hlam_supp ν
    by_contra hcon
    push Not at hcon
    have hνdvd : ν ∣ b * (c * n) := (Nat.mem_divisors.mp hν).1
    have hbce0 : b * (c * n) ≠ 0 := (Nat.mem_divisors.mp hν).2
    have hνpos : 0 < ν := Nat.pos_of_dvd_of_pos hνdvd (Nat.pos_of_ne_zero hbce0)
    have hbn0 : b * n ≠ 0 := fun h0 => hbce0 (by
      rw [mul_comm c n, ← mul_assoc, h0, zero_mul])
    have hlt : ν < c := lt_of_le_of_lt hcon hΔc
    have hcop : ν.Coprime c := by
      refine (hc.coprime_iff_not_dvd).mpr ?_ |>.symm
      exact fun hd => absurd (Nat.le_of_dvd (by omega) hd) (not_le.mpr hlt)
    have hdvd' : ν ∣ c * (b * n) := by
      rw [show c * (b * n) = b * (c * n) by ring]
      exact hνdvd
    exact hνnot (Nat.mem_divisors.mpr ⟨hcop.dvd_of_dvd_mul_left hdvd', hbn0⟩)

/-- **§8, the crucial reduction**: because `c` is prime (for `Λ(c) ≠ 0` and `bce` squarefree),
the sieve weight `ρ_{ebc}` may be replaced by `ρ_{eb}`. -/
theorem S3_eq_rho_eb (a lam : ℕ → ℝ) (N : ℕ) (z sy sz : ℝ) (Δ : ℕ)
    (ha : ∀ n, ¬ Squarefree n → a n = 0)
    (hlam_supp : ∀ ν, Δ < ν → lam ν = 0)
    (hΔz : (Δ : ℝ) < z) :
    S3 a lam N z sy sz
      = ∑ b ∈ (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ c ∈ (Finset.Icc 1 N).filter
                (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
              ArithmeticFunction.vonMangoldt c *
                ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
                  a (b * (c * e)) * rhoOf lam (b * e) := by
  rw [S3_eq_e a lam N z sy sz]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine congrArg (fun x => (ArithmeticFunction.moebius b : ℝ) * x) ?_
  refine Finset.sum_congr rfl (fun c hc => ?_)
  by_cases hcΛ : ArithmeticFunction.vonMangoldt c = 0
  · rw [hcΛ, zero_mul, zero_mul]
  · congr 1
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases hae : a (b * (c * e)) = 0
    · rw [hae, zero_mul, zero_mul]
    · have hsq : Squarefree (b * (c * e)) := by
        by_contra h; exact hae (ha _ h)
      have hdvd : c ∣ b * (c * e) := ⟨b * e, by ring⟩
      have hsqc : Squarefree c := by
        rw [Nat.squarefree_iff_prime_squarefree] at hsq ⊢
        intro x hx hxc
        exact hsq x hx (dvd_trans hxc hdvd)
      have hcp : c.Prime := Nat.squarefree_and_prime_pow_iff_prime.mp
        ⟨hsqc, ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hcΛ⟩
      have hΔc : Δ < c := by
        have h1 : z < ((c : ℕ) : ℝ) := (Finset.mem_filter.mp hc).2.1
        exact_mod_cast lt_trans hΔz h1
      rw [rhoOf_mul_prime_eq lam hlam_supp hcp hΔc]

/-! ### The splitting `S₃ = S₃⁻ − S₃⁺` -/

/-- `S₃⁻(x;y,z) = ∑_{b>sy} μ(b) ∑_{z<c≤sz} λ⁻(c) ∑_{bce≤x} a(bce)ρ_{be}` (the `λ⁻` part of §8). -/
def S3minus (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) : ℝ :=
  ∑ b ∈ (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)),
    (ArithmeticFunction.moebius b : ℝ) *
      ∑ c ∈ (Finset.Icc 1 N).filter
          (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
        lamMinus c C *
          ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
            a (b * (c * e)) * rhoOf lam (b * e)

/-- `S₃⁺(x;y,z)` — the `λ⁺` part of §8. -/
def S3plus (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) : ℝ :=
  ∑ b ∈ (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)),
    (ArithmeticFunction.moebius b : ℝ) *
      ∑ c ∈ (Finset.Icc 1 N).filter
          (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
        lamPlus c C *
          ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
            a (b * (c * e)) * rhoOf lam (b * e)

/-- **§8, the splitting**: `S₃ = S₃⁻ − S₃⁺` (for `z ≥ 1` and `C > 0`). -/
theorem S3_eq_S3minus_sub_S3plus (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) (Δ : ℕ)
    (ha : ∀ n, ¬ Squarefree n → a n = 0)
    (hlam_supp : ∀ ν, Δ < ν → lam ν = 0)
    (hΔz : (Δ : ℝ) < z) (hz : 1 ≤ z) (hC : 0 < C) :
    S3 a lam N z sy sz = S3minus a lam N z sy sz C - S3plus a lam N z sy sz C := by
  rw [S3_eq_rho_eb a lam N z sy sz Δ ha hlam_supp hΔz, S3minus, S3plus,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hsplit : ∀ c ∈ (Finset.Icc 1 N).filter
      (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
      ArithmeticFunction.vonMangoldt c *
          (∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
            a (b * (c * e)) * rhoOf lam (b * e))
        = lamMinus c C * (∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
            a (b * (c * e)) * rhoOf lam (b * e))
          - lamPlus c C * (∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
            a (b * (c * e)) * rhoOf lam (b * e)) := by
    intro c hc
    have hc2 : 2 ≤ c := by
      have h1 : (1 : ℝ) ≤ z := by exact_mod_cast hz
      have h2 : z < ((c : ℕ) : ℝ) := (Finset.mem_filter.mp hc).2.1
      have h3 : (1 : ℕ) < c := by exact_mod_cast (lt_of_le_of_lt h1 h2)
      omega
    rw [vonMangoldt_eq_lamMinus_sub_lamPlus c hc2 hC, sub_mul]
  have hinner : (∑ c ∈ (Finset.Icc 1 N).filter
        (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
        ArithmeticFunction.vonMangoldt c *
          (∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
            a (b * (c * e)) * rhoOf lam (b * e)))
      = (∑ c ∈ (Finset.Icc 1 N).filter
        (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
        lamMinus c C *
          (∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
            a (b * (c * e)) * rhoOf lam (b * e)))
        - ∑ c ∈ (Finset.Icc 1 N).filter
        (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
        lamPlus c C *
          (∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
            a (b * (c * e)) * rhoOf lam (b * e)) := by
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
  rw [hinner, mul_sub]

end

end Submission.ASP
