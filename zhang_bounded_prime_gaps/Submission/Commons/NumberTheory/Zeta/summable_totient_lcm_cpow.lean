import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Submission.Commons.NumberTheory.Zeta.summable_lcm_inv_cpow

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Zeta

/-- For a finset `S` of natural numbers all at least `2`, the product of `p/(p-1)` over `S`
is at most `|S| + 1`.  Equivalently `∏ p ≤ (|S|+1) ∏ (p-1)`. -/
private lemma prod_le_card_succ_mul_prod_pred (S : Finset ℕ) (h2 : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, p ≤ (S.card + 1) * ∏ p ∈ S, (p - 1) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hmem : S.max' hne ∈ S := S.max'_mem hne
      have hm2 : 2 ≤ S.max' hne := h2 _ hmem
      have hcard : S.card ≤ S.max' hne - 1 := by
        have hsub : S ⊆ Finset.Icc 2 (S.max' hne) := fun p hp =>
          Finset.mem_Icc.mpr ⟨h2 p hp, S.le_max' p hp⟩
        calc S.card ≤ (Finset.Icc 2 (S.max' hne)).card := Finset.card_le_card hsub
          _ = S.max' hne + 1 - 2 := Nat.card_Icc 2 (S.max' hne)
          _ = S.max' hne - 1 := by omega
      have ihT := ih (S.erase (S.max' hne)) (Finset.erase_ssubset hmem)
        (fun p hp => h2 p (Finset.mem_of_mem_erase hp))
      have hTcard : (S.erase (S.max' hne)).card + 1 = S.card := by
        rw [Finset.card_erase_of_mem hmem,
            Nat.sub_add_cancel (Nat.succ_le_of_lt (Finset.card_pos.mpr hne))]
      have hm_eq : S.max' hne = (S.max' hne - 1) + 1 := by omega
      have hkm : S.card * S.max' hne ≤ (S.card + 1) * (S.max' hne - 1) := by
        calc S.card * S.max' hne = S.card * ((S.max' hne - 1) + 1) :=
              congrArg (fun x => S.card * x) hm_eq
          _ = S.card * (S.max' hne - 1) + S.card := by ring
          _ ≤ S.card * (S.max' hne - 1) + (S.max' hne - 1) := Nat.add_le_add_left hcard _
          _ = (S.card + 1) * (S.max' hne - 1) := by ring
      rw [← Finset.prod_erase_mul S (fun p => p) hmem,
          ← Finset.prod_erase_mul S (fun p => (p - 1)) hmem]
      calc (∏ x ∈ S.erase (S.max' hne), x) * S.max' hne
          ≤ ((S.erase (S.max' hne)).card + 1)
              * (∏ x ∈ S.erase (S.max' hne), (x - 1)) * S.max' hne :=
            Nat.mul_le_mul_right _ ihT
        _ = S.card * (∏ x ∈ S.erase (S.max' hne), (x - 1)) * S.max' hne := by rw [hTcard]
        _ = (∏ x ∈ S.erase (S.max' hne), (x - 1)) * (S.card * S.max' hne) := by ring
        _ ≤ (∏ x ∈ S.erase (S.max' hne), (x - 1)) * ((S.card + 1) * (S.max' hne - 1)) :=
            Nat.mul_le_mul_left _ hkm
        _ = (S.card + 1) * ((∏ x ∈ S.erase (S.max' hne), (x - 1)) * (S.max' hne - 1)) := by ring

/-- For `n ≠ 0`, `n ≤ (1 + logb 2 n) * φ n`. -/
private lemma totient_ge_mul_logb (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) ≤ (1 + Real.logb 2 (n : ℝ)) * (n.totient : ℝ) := by
  have hS2 : ∀ p ∈ n.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hprod := prod_le_card_succ_mul_prod_pred n.primeFactors hS2
  have hrad_dvd : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
  have hdecomp : n = (n / ∏ p ∈ n.primeFactors, p) * (∏ p ∈ n.primeFactors, p) :=
    (Nat.div_mul_cancel hrad_dvd).symm
  have hphi := Nat.totient_eq_div_primeFactors_mul n
  have hkey : n ≤ ((n.primeFactors).card + 1) * n.totient := by
    have h1 : (n / ∏ p ∈ n.primeFactors, p) * (∏ p ∈ n.primeFactors, p)
        ≤ ((n.primeFactors).card + 1) *
            ((n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p - 1)) := by
      calc (n / ∏ p ∈ n.primeFactors, p) * (∏ p ∈ n.primeFactors, p)
          ≤ (n / ∏ p ∈ n.primeFactors, p) *
              (((n.primeFactors).card + 1) * ∏ p ∈ n.primeFactors, (p - 1)) :=
            Nat.mul_le_mul_left _ hprod
        _ = ((n.primeFactors).card + 1) *
              ((n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p - 1)) := by ring
    calc n = (n / ∏ p ∈ n.primeFactors, p) * (∏ p ∈ n.primeFactors, p) := hdecomp
      _ ≤ ((n.primeFactors).card + 1) *
            ((n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p - 1)) := h1
      _ = ((n.primeFactors).card + 1) * n.totient := by rw [hphi]
  have hkeyR : (n : ℝ) ≤ ((n.primeFactors.card : ℝ) + 1) * (n.totient : ℝ) := by
    exact_mod_cast hkey
  have hcardle : (n.primeFactors.card : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    have h2le : (2 : ℕ) ^ (n.primeFactors.card) ≤ ∏ p ∈ n.primeFactors, p := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod (fun p _ => Nat.zero_le 2) (fun p hp => hS2 p hp)
    have h2n : (2 : ℕ) ^ (n.primeFactors.card) ≤ n :=
      le_trans h2le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hrad_dvd)
    have h2nR : (2 : ℝ) ^ ((n.primeFactors.card : ℕ) : ℝ) ≤ (n : ℝ) := by
      rw [Real.rpow_natCast]; exact_mod_cast h2n
    have h := (Real.logb_le_logb (b := 2)
      (x := (2 : ℝ) ^ ((n.primeFactors.card : ℕ) : ℝ)) (y := (n : ℝ))
      (by norm_num) (by positivity) (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr h2nR
    rwa [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at h
  calc (n : ℝ) ≤ ((n.primeFactors.card : ℝ) + 1) * (n.totient : ℝ) := hkeyR
    _ ≤ (1 + Real.logb 2 (n : ℝ)) * (n.totient : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        linarith [hcardle]

/-- For `n ≠ 0`, `(φ n)⁻¹ ≤ (1 + logb 2 n)/n`. -/
private lemma totient_inv_le (n : ℕ) (hn : n ≠ 0) :
    (n.totient : ℝ)⁻¹ ≤ (1 + Real.logb 2 (n : ℝ)) / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hPpos : 0 < (n.totient : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn))
  have key := totient_ge_mul_logb n hn
  rw [inv_le_iff_one_le_mul₀ hPpos, div_mul_eq_mul_div, le_div_iff₀ hnR]
  simpa using key

/-- `1 + logb 2 x ≤ (1 + (ε log 2)⁻¹) x^ε` for `x ≥ 1`, `ε > 0`. -/
private lemma one_add_logb_le {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 1 ≤ x) :
    1 + Real.logb 2 x ≤ (1 + (ε * Real.log 2)⁻¹) * x ^ ε := by
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxε : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hlogx : Real.log x * ε ≤ x ^ ε := by
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxpos ε)
    rw [Real.log_rpow hxpos ε] at h1
    rw [mul_comm]
    linarith
  have hεlpos : 0 < ε * Real.log 2 := mul_pos hε hlog2pos
  have hkey : Real.log x / Real.log 2 ≤ x ^ ε / (ε * Real.log 2) := by
    rw [div_le_div_iff₀ hlog2pos hεlpos]
    nlinarith [mul_le_mul_of_nonneg_right hlogx hlog2pos.le]
  rw [Real.logb]
  calc 1 + Real.log x / Real.log 2
      ≤ 1 + x ^ ε / (ε * Real.log 2) := by linarith
    _ ≤ (1 + (ε * Real.log 2)⁻¹) * x ^ ε := by
        have heq : (1 + (ε * Real.log 2)⁻¹) * x ^ ε
            = 1 + x ^ ε / (ε * Real.log 2) + (x ^ ε - 1) := by
          rw [add_mul, one_mul, div_eq_mul_inv]
          ring
        rw [heq]; linarith [hxε]

/-- Pointwise kernel bound: for a positive `ℓ ≤ m n`,
`(φ ℓ)⁻¹ m^{-s} n^{-t} ≤ C² ℓ⁻¹ m^{-(s-ε)} n^{-(t-ε)}` with `C = 1 + (ε log 2)⁻¹`. -/
private lemma kernel_bound (m n ℓ : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hℓ : ℓ ≠ 0) (hℓmn : ℓ ≤ m * n) {s t ε : ℝ} (hε : 0 < ε) :
    (ℓ.totient : ℝ)⁻¹ * (m : ℝ) ^ (-s) * (n : ℝ) ^ (-t) ≤
      (1 + (ε * Real.log 2)⁻¹) ^ 2 *
        ((ℓ : ℝ)⁻¹ * (m : ℝ) ^ (-(s - ε)) * (n : ℝ) ^ (-(t - ε))) := by
  have hXpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hYpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hℓ
  have hX1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
  have hY1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
  have hℓle : (ℓ : ℝ) ≤ (m : ℝ) * (n : ℝ) := by exact_mod_cast hℓmn
  have hlogprod : 1 + Real.logb 2 (ℓ : ℝ) ≤
      (1 + Real.logb 2 (m : ℝ)) * (1 + Real.logb 2 (n : ℝ)) := by
    have hlog : Real.logb 2 (ℓ : ℝ) ≤ Real.logb 2 ((m : ℝ) * (n : ℝ)) :=
      (Real.logb_le_logb (b := 2) (by norm_num) hℓpos (by positivity)).mpr hℓle
    rw [Real.logb_mul (ne_of_gt hXpos) (ne_of_gt hYpos)] at hlog
    have hnX := Real.logb_nonneg (b := 2) (by norm_num) hX1
    have hnY := Real.logb_nonneg (b := 2) (by norm_num) hY1
    nlinarith [hlog, hnX, hnY]
  have hpowX : 1 + Real.logb 2 (m : ℝ) ≤ (1 + (ε * Real.log 2)⁻¹) * (m : ℝ) ^ ε :=
    one_add_logb_le hε hX1
  have hpowY : 1 + Real.logb 2 (n : ℝ) ≤ (1 + (ε * Real.log 2)⁻¹) * (n : ℝ) ^ ε :=
    one_add_logb_le hε hY1
  have hnYnn : 0 ≤ 1 + Real.logb 2 (n : ℝ) := by
    have := Real.logb_nonneg (b := 2) (by norm_num) hY1; linarith
  have hprodbound : 1 + Real.logb 2 (ℓ : ℝ) ≤
      (1 + (ε * Real.log 2)⁻¹) ^ 2 * (m : ℝ) ^ ε * (n : ℝ) ^ ε := by
    calc 1 + Real.logb 2 (ℓ : ℝ)
          ≤ (1 + Real.logb 2 (m : ℝ)) * (1 + Real.logb 2 (n : ℝ)) := hlogprod
      _ ≤ ((1 + (ε * Real.log 2)⁻¹) * (m : ℝ) ^ ε) *
            ((1 + (ε * Real.log 2)⁻¹) * (n : ℝ) ^ ε) :=
          mul_le_mul hpowX hpowY hnYnn (by positivity)
      _ = (1 + (ε * Real.log 2)⁻¹) ^ 2 * (m : ℝ) ^ ε * (n : ℝ) ^ ε := by ring
  have hφ : (ℓ.totient : ℝ)⁻¹ ≤
      (1 + (ε * Real.log 2)⁻¹) ^ 2 * (m : ℝ) ^ ε * (n : ℝ) ^ ε * (ℓ : ℝ)⁻¹ := by
    have h1 := totient_inv_le ℓ hℓ
    calc (ℓ.totient : ℝ)⁻¹ ≤ (1 + Real.logb 2 (ℓ : ℝ)) / (ℓ : ℝ) := h1
      _ ≤ ((1 + (ε * Real.log 2)⁻¹) ^ 2 * (m : ℝ) ^ ε * (n : ℝ) ^ ε) / (ℓ : ℝ) :=
          div_le_div_of_nonneg_right hprodbound hℓpos.le
      _ = (1 + (ε * Real.log 2)⁻¹) ^ 2 * (m : ℝ) ^ ε * (n : ℝ) ^ ε * (ℓ : ℝ)⁻¹ := by
          rw [div_eq_mul_inv]
  have hXexp : (m : ℝ) ^ ε * (m : ℝ) ^ (-s) = (m : ℝ) ^ (-(s - ε)) := by
    rw [← Real.rpow_add hXpos]; congr 1; ring
  have hYexp : (n : ℝ) ^ ε * (n : ℝ) ^ (-t) = (n : ℝ) ^ (-(t - ε)) := by
    rw [← Real.rpow_add hYpos]; congr 1; ring
  have hmn : 0 ≤ (m : ℝ) ^ (-s) * (n : ℝ) ^ (-t) :=
    mul_nonneg (Real.rpow_nonneg hXpos.le _) (Real.rpow_nonneg hYpos.le _)
  calc (ℓ.totient : ℝ)⁻¹ * (m : ℝ) ^ (-s) * (n : ℝ) ^ (-t)
      = (ℓ.totient : ℝ)⁻¹ * ((m : ℝ) ^ (-s) * (n : ℝ) ^ (-t)) := by ring
    _ ≤ ((1 + (ε * Real.log 2)⁻¹) ^ 2 * (m : ℝ) ^ ε * (n : ℝ) ^ ε * (ℓ : ℝ)⁻¹) *
          ((m : ℝ) ^ (-s) * (n : ℝ) ^ (-t)) := mul_le_mul_of_nonneg_right hφ hmn
    _ = (1 + (ε * Real.log 2)⁻¹) ^ 2 * (ℓ : ℝ)⁻¹ *
          ((m : ℝ) ^ ε * (m : ℝ) ^ (-s)) * ((n : ℝ) ^ ε * (n : ℝ) ^ (-t)) := by ring
    _ = (1 + (ε * Real.log 2)⁻¹) ^ 2 *
          ((ℓ : ℝ)⁻¹ * (m : ℝ) ^ (-(s - ε)) * (n : ℝ) ^ (-(t - ε))) := by
        rw [hXexp, hYexp]; ring

theorem summable_totient_lcm_cpow {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Summable (fun x : ℕ × ℕ =>
      ‖(((Nat.lcm x.1 x.2).totient : ℕ) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) * (x.2 : ℂ) ^ (-b)‖) := by
  set ε : ℝ := min a.re b.re / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεa : ε < a.re := by rw [hεdef]; linarith [min_le_left a.re b.re, ha]
  have hεb : ε < b.re := by rw [hεdef]; linarith [min_le_right a.re b.re, hb]
  have hane : (-a).re ≠ 0 := by rw [Complex.neg_re]; exact neg_ne_zero.mpr ha.ne'
  have hbne : (-b).re ≠ 0 := by rw [Complex.neg_re]; exact neg_ne_zero.mpr hb.ne'
  have ha' : 0 < (a - (ε : ℂ)).re := by rw [Complex.sub_re, Complex.ofReal_re]; linarith
  have hb' : 0 < (b - (ε : ℂ)).re := by rw [Complex.sub_re, Complex.ofReal_re]; linarith
  have ha'ne : (-(a - (ε : ℂ))).re ≠ 0 := by
    rw [Complex.neg_re, Complex.sub_re, Complex.ofReal_re]; linarith
  have hb'ne : (-(b - (ε : ℂ))).re ≠ 0 := by
    rw [Complex.neg_re, Complex.sub_re, Complex.ofReal_re]; linarith
  have hmaj : Summable (fun x : ℕ × ℕ =>
      ‖((Nat.lcm x.1 x.2 : ℕ) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-(a - (ε : ℂ))) *
        (x.2 : ℂ) ^ (-(b - (ε : ℂ)))‖) :=
    summable_lcm_inv_cpow ha' hb'
  refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_)
    (hmaj.mul_left ((1 + (ε * Real.log 2)⁻¹) ^ 2))
  by_cases hx1 : x.1 = 0
  · have h0 : (((Nat.lcm x.1 x.2).totient : ℕ) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) *
        (x.2 : ℂ) ^ (-b) = 0 := by
      rw [hx1]; simp [Nat.lcm_zero_left, Nat.totient_zero]
    rw [h0, norm_zero]; positivity
  · by_cases hx2 : x.2 = 0
    · have h0 : (((Nat.lcm x.1 x.2).totient : ℕ) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) *
          (x.2 : ℂ) ^ (-b) = 0 := by
        rw [hx2]; simp [Nat.lcm_zero_right, Nat.totient_zero]
      rw [h0, norm_zero]; positivity
    · have hLne : Nat.lcm x.1 x.2 ≠ 0 := Nat.lcm_ne_zero hx1 hx2
      have hLle : Nat.lcm x.1 x.2 ≤ x.1 * x.2 :=
        Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hx1) (Nat.pos_of_ne_zero hx2))
          (Nat.lcm_dvd_mul x.1 x.2)
      have hLHS : ‖(((Nat.lcm x.1 x.2).totient : ℕ) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) *
            (x.2 : ℂ) ^ (-b)‖
          = ((Nat.lcm x.1 x.2).totient : ℝ)⁻¹ * (x.1 : ℝ) ^ (-a.re) * (x.2 : ℝ) ^ (-b.re) := by
        rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast,
            Complex.norm_natCast_cpow_of_re_ne_zero x.1 (s := -a) hane,
            Complex.norm_natCast_cpow_of_re_ne_zero x.2 (s := -b) hbne,
            Complex.neg_re, Complex.neg_re]
      have hRHS : ‖((Nat.lcm x.1 x.2 : ℕ) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-(a - (ε : ℂ))) *
            (x.2 : ℂ) ^ (-(b - (ε : ℂ)))‖
          = ((Nat.lcm x.1 x.2) : ℝ)⁻¹ * (x.1 : ℝ) ^ (-(a.re - ε)) *
              (x.2 : ℝ) ^ (-(b.re - ε)) := by
        rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast,
            Complex.norm_natCast_cpow_of_re_ne_zero x.1 (s := -(a - (ε : ℂ))) ha'ne,
            Complex.norm_natCast_cpow_of_re_ne_zero x.2 (s := -(b - (ε : ℂ))) hb'ne,
            Complex.neg_re, Complex.neg_re, Complex.sub_re, Complex.sub_re,
            Complex.ofReal_re]
      rw [hLHS, hRHS]
      exact kernel_bound x.1 x.2 (Nat.lcm x.1 x.2) hx1 hx2 hLne hLle (s := a.re) (t := b.re) hεpos

end Commons.NumberTheory.Zeta