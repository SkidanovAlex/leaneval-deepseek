import Mathlib
import Submission.Work.FIArea2.TsumDefs
import Submission.Work.FIArea2.ramanujan_primepow
import Submission.Work.FIArea2.ram_two_pow_value
import Submission.Work.FIArea2.stratum_count_bound
import Submission.Work.FIArea2.card_range_sq_roots_two_pow
import Submission.Work.FIArea2.Tsum_two_pow_recursion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Helpers -/

/-- A unit `a` modulo `2^ν` (`ν ≥ 1`) is odd. -/
theorem odd_of_isUnit_two_pow (ν : ℕ) (hν : 1 ≤ ν) (a : ℤ) (ha : IsUnit (a : ZMod (2 ^ ν))) :
    Odd a := by
  have hd : 2 ∣ 2 ^ ν := by
    refine ⟨2 ^ (ν - 1), ?_⟩
    rw [← pow_succ']; congr 1; omega
  have hu : IsUnit (a : ZMod 2) := by
    have h := IsUnit.map (ZMod.castHom hd (ZMod 2)) ha
    rw [ZMod.castHom_apply, ZMod.cast_intCast hd a] at h
    exact h
  rw [← Int.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  exact hu.ne_zero ((ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mpr h2)

/-- Norm of a power of two in `ℂ`. -/
theorem norm_two_pow_cplx (m : ℕ) : ‖(2 : ℂ) ^ m‖ = (2 : ℝ) ^ m := by
  rw [norm_pow]; norm_num

/-- Cast of a power of two to `ℝ`. -/
theorem two_pow_cast (ν : ℕ) : ((2 ^ ν : ℕ) : ℝ) = (2 : ℝ) ^ ν := by
  rw [Nat.cast_pow, Nat.cast_ofNat]

/-- Divisibility of `x.natAbs` by `m` from divisibility of `x` by `(m : ℤ)`. -/
theorem natAbs_dvd_of_int_dvd (m : ℕ) (x : ℤ) (h : (m : ℤ) ∣ x) : m ∣ x.natAbs := by
  have := Int.natAbs_dvd_natAbs.mpr h
  simpa using this

/-- If `t ≤ ν` and `2^t ∣ D` then `2^t ≤ Nat.gcd (2^ν) D`. -/
theorem le_gcd_two_pow (ν t D : ℕ) (ht : t ≤ ν) (h : 2 ^ t ∣ D) :
    2 ^ t ≤ Nat.gcd (2 ^ ν) D :=
  Nat.le_of_dvd (Nat.gcd_pos_of_pos_left D (pow_pos (by norm_num) ν))
    (Nat.dvd_gcd (pow_dvd_pow 2 ht) h)

/-- Card of a doubly filtered set, in the `∧`-form (avoids instance mismatch). -/
theorem filter_filter_card (s : Finset ℕ) (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q] :
    ((s.filter p).filter q).card = (s.filter (fun r => p r ∧ q r)).card := by
  congr 1
  ext r
  simp only [Finset.mem_filter]
  tauto

/-- Cardinality of a set of `ℕ` written as a sum of indicators. -/
theorem sum_ite_one_eq_card (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (∑ r ∈ s, (if p r then (1:ℝ) else 0)) = ((s.filter p).card : ℝ) := by
  rw [← Finset.sum_filter]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- `‖2^m - 2^(m-1)‖ = 2^(m-1)` in `ℂ`. -/
theorem norm_two_pow_sub (m : ℕ) (hm : 1 ≤ m) :
    ‖(2 : ℂ) ^ m - (2 : ℂ) ^ (m - 1)‖ = (2 : ℝ) ^ (m - 1) := by
  have hmul : (2 : ℂ) ^ m = (2 : ℂ) ^ (m - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [hmul]
  have h : (2 : ℂ) ^ (m - 1) * 2 - (2 : ℂ) ^ (m - 1) = (2 : ℂ) ^ (m - 1) * ((2:ℂ) - 1) := by
    ring
  rw [h, show ((2:ℂ) - 1) = 1 by norm_num, mul_one, norm_pow]
  norm_num

/-- The norm of the Ramanujan sum at a power of two. -/
theorem ram_two_pow_norm (m : ℕ) (hm : 1 ≤ m) (c : ℤ) :
    ‖ram (2 ^ m) c‖ = (2 : ℝ) ^ (m - 1) * (if ((2 ^ (m - 1) : ℕ) : ℤ) ∣ c then 1 else 0) := by
  have hdvd : ((2 ^ (m - 1) : ℕ) : ℤ) ∣ ((2 ^ m : ℕ) : ℤ) := by
    refine ⟨2, ?_⟩
    push_cast
    rw [← pow_succ]
    congr 1
    omega
  have hmain : ram (2 ^ m) c = (2 ^ m : ℂ) * (if ((2 ^ m : ℕ) : ℤ) ∣ c then 1 else 0)
      - (2 ^ (m - 1) : ℂ) * (if ((2 ^ (m - 1) : ℕ) : ℤ) ∣ c then 1 else 0) :=
    ram_two_pow_value m hm c
  rw [hmain]
  by_cases hb : ((2 ^ (m - 1) : ℕ) : ℤ) ∣ c
  · by_cases ha : ((2 ^ m : ℕ) : ℤ) ∣ c
    · have hexpr : (2 ^ m : ℂ) * (if ((2 ^ m : ℕ) : ℤ) ∣ c then 1 else 0)
          - (2 ^ (m - 1) : ℂ) * (if ((2 ^ (m - 1) : ℕ) : ℤ) ∣ c then 1 else 0)
          = (2 ^ m : ℂ) - (2 ^ (m - 1) : ℂ) := by
        rw [if_pos ha, if_pos hb, mul_one, mul_one]
      rw [hexpr, norm_two_pow_sub m hm, if_pos hb, mul_one]
    · have hexpr : (2 ^ m : ℂ) * (if ((2 ^ m : ℕ) : ℤ) ∣ c then 1 else 0)
          - (2 ^ (m - 1) : ℂ) * (if ((2 ^ (m - 1) : ℕ) : ℤ) ∣ c then 1 else 0)
          = 0 - (2 ^ (m - 1) : ℂ) := by
        rw [if_neg ha, if_pos hb, mul_one, mul_zero]
      rw [hexpr, zero_sub, norm_neg, norm_two_pow_cplx, if_pos hb, mul_one]
  · have ha : ¬ (((2 ^ m : ℕ) : ℤ) ∣ c) := fun hh => hb (dvd_trans hdvd hh)
    have hexpr : (2 ^ m : ℂ) * (if ((2 ^ m : ℕ) : ℤ) ∣ c then 1 else 0)
        - (2 ^ (m - 1) : ℂ) * (if ((2 ^ (m - 1) : ℕ) : ℤ) ∣ c then 1 else 0) = 0 := by
      rw [if_neg ha, if_neg hb, mul_zero, mul_zero, sub_zero]
    rw [hexpr, norm_zero, if_neg hb, mul_zero]

/-- `Tsum` at modulus `1`. -/
theorem Tsum_one_pow (a h1 h2 : ℤ) : Tsum 1 a h1 h2 = 1 := by
  unfold Tsum
  rw [Fintype.sum_unique]
  rw [Fintype.sum_unique]
  rw [← Unique.eq_default (0 : ZMod 1)]
  norm_num [E]

/-- Crude bound: `‖Tsum N a h1 h2‖ ≤ N^2`. -/
theorem norm_Tsum_le (N : ℕ) [NeZero N] (a h1 h2 : ℤ) :
    ‖Tsum N a h1 h2‖ ≤ (N : ℝ) ^ 2 := by
  unfold Tsum
  calc ‖∑ x : ZMod N, ∑ y : ZMod N,
        (if y ^ 2 = (a : ZMod N) * x ^ 2 then
          E ((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ) / (N : ℝ)) else 0)‖
      ≤ ∑ x : ZMod N, ‖∑ y : ZMod N,
        (if y ^ 2 = (a : ZMod N) * x ^ 2 then
          E ((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ) / (N : ℝ)) else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ x : ZMod N, ∑ y : ZMod N,
        ‖(if y ^ 2 = (a : ZMod N) * x ^ 2 then
          E ((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ) / (N : ℝ)) else 0)‖ :=
        Finset.sum_le_sum (fun x _ => norm_sum_le _ _)
    _ ≤ ∑ x : ZMod N, ∑ y : ZMod N, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
        by_cases h : y ^ 2 = (a : ZMod N) * x ^ 2
        · rw [if_pos h, E_norm]
        · rw [if_neg h, norm_zero]; norm_num
    _ = (N : ℝ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
        ring

/-- The main bound, by strong induction on `ν`. -/
theorem Tsum_prime_pow_two (ν : ℕ) (hν : 1 ≤ ν) (a h1 h2 : ℤ)
    (ha : IsUnit (a : ZMod (2 ^ ν))) :
    ‖Tsum (2 ^ ν) a h1 h2‖
      ≤ ((ν : ℝ) + 1) ^ 3 * (Nat.gcd (2 ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := by
  have key : ∀ n : ℕ, ∀ a h1 h2 : ℤ, Odd a →
      ‖Tsum (2 ^ n) a h1 h2‖
        ≤ ((n : ℝ) + 1) ^ 3 * (Nat.gcd (2 ^ n) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := by
    intro n0
    refine Nat.strong_induction_on (p := fun n => ∀ a h1 h2 : ℤ, Odd a →
        ‖Tsum (2 ^ n) a h1 h2‖ ≤
          ((n : ℝ) + 1) ^ 3 * (Nat.gcd (2 ^ n) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ)) n0 ?_
    intro n ih a h1 h2 ha
    · set G : ℕ := Nat.gcd (2 ^ n) ((h1 ^ 2 - a * h2 ^ 2).natAbs) with hG
      have hG1 : (1 : ℝ) ≤ (G : ℝ) := by
        have h : 1 ≤ G := by
          rw [hG]
          exact Nat.one_le_iff_ne_zero.mpr (Nat.gcd_ne_zero_left (by norm_num))
        exact_mod_cast h
      rcases Nat.lt_or_ge n 3 with h3 | h3
      · interval_cases n
        · -- n = 0
          have h := norm_Tsum_le (2 ^ 0) a h1 h2
          have hG' : (G : ℝ) = 1 := by
            rw [hG]
            show (((Nat.gcd 1 ((h1 ^ 2 - a * h2 ^ 2).natAbs)) : ℕ) : ℝ) = 1
            rw [Nat.gcd_one_left]; norm_num
          have h2' : ((2 ^ 0 : ℕ) : ℝ) ^ 2 ≤ (((0 : ℕ) : ℝ) + 1) ^ 3 * (G : ℝ) := by
            rw [hG']; norm_num
          exact le_trans h h2'
        · -- n = 1
          have h := norm_Tsum_le (2 ^ 1) a h1 h2
          have h2' : ((2 ^ 1 : ℕ) : ℝ) ^ 2 ≤ (((1 : ℕ) : ℝ) + 1) ^ 3 * (G : ℝ) := by
            norm_num
            linarith
          exact le_trans h h2'
        · -- n = 2
          have h := norm_Tsum_le (2 ^ 2) a h1 h2
          have h2' : ((2 ^ 2 : ℕ) : ℝ) ^ 2 ≤ (((2 : ℕ) : ℝ) + 1) ^ 3 * (G : ℝ) := by
            norm_num
            linarith
          exact le_trans h h2'
      · -- n ≥ 3
        have hrec := Tsum_two_pow_recursion n (by omega : 2 ≤ n) a h1 h2 ha
        set Tup : ℂ := ∑ r ∈ (Finset.range (2 ^ n)).filter
            (fun r : ℕ => ((2 ^ n : ℕ) : ℤ) ∣ (r : ℤ) ^ 2 - a),
          ram (2 ^ n) (h1 + (r : ℤ) * h2) with hTup
        rw [hrec]
        have hTup_le : ‖Tup‖ ≤ 2 * (G : ℝ) := by
          rw [hTup]
          set S : Finset ℕ := (Finset.range (2 ^ n)).filter
              (fun r : ℕ => ((2 ^ n : ℕ) : ℤ) ∣ (r : ℤ) ^ 2 - a) with hS
          set B0 : ℕ := (S.filter
              (fun r : ℕ => ((2 ^ (n - 1) : ℕ) : ℤ) ∣ h1 + (r : ℤ) * h2)).card with hB0
          have hnorm : ‖∑ r ∈ S, ram (2 ^ n) (h1 + (r : ℤ) * h2)‖
              ≤ (2 : ℝ) ^ (n - 1) * (B0 : ℝ) := by
            refine le_trans (norm_sum_le _ _) ?_
            have hsum : (∑ r ∈ S, ‖ram (2 ^ n) (h1 + (r : ℤ) * h2)‖)
                = (2 : ℝ) ^ (n - 1) * (∑ r ∈ S,
                    (if ((2 ^ (n - 1) : ℕ) : ℤ) ∣ h1 + (r : ℤ) * h2 then (1:ℝ) else 0)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun r hr => ?_)
              rw [ram_two_pow_norm n (by omega) (h1 + (r : ℤ) * h2)]
            rw [hsum, sum_ite_one_eq_card, ← hB0]
          have hB0eq : B0 = ((Finset.range (2 ^ n)).filter
              (fun r : ℕ => ((2 ^ n : ℕ) : ℤ) ∣ (r : ℤ) ^ 2 - a ∧
                ((2 ^ (n - 1) : ℕ) : ℤ) ∣ h1 + (r : ℤ) * h2)).card := by
            rw [hB0, hS, filter_filter_card]
          have hbound : (2 : ℝ) ^ (n - 1) * (B0 : ℝ) ≤ 2 * (G : ℝ) := by
            by_cases hD : (((2 ^ n : ℕ) : ℤ) ∣ h1 ^ 2 - a * h2 ^ 2)
            · have hGG : G = 2 ^ n := by
                rw [hG]
                exact Nat.gcd_eq_left (natAbs_dvd_of_int_dvd (2 ^ n) _ hD)
              have hB04 : B0 ≤ 4 := by
                rw [hB0eq]
                refine le_trans (Finset.card_le_card ?_)
                  (card_range_sq_roots_two_pow n (by omega) a ha)
                intro r hr
                simp only [Finset.mem_filter] at hr ⊢
                exact ⟨hr.1, hr.2.1⟩
              rw [hGG]
              have hfour : (2 : ℝ) ^ (n - 1) * 4 = 2 * (2 : ℝ) ^ n := by
                have h4 : (4 : ℝ) = 2 * 2 := by norm_num
                rw [h4, ← mul_assoc, ← pow_succ]
                rw [show n - 1 + 1 = n by omega]
                ring
              calc (2 : ℝ) ^ (n - 1) * (B0 : ℝ)
                  ≤ (2 : ℝ) ^ (n - 1) * 4 := by
                    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                    exact_mod_cast hB04
                _ = 2 * (2 : ℝ) ^ n := hfour
                _ = 2 * ((2 ^ n : ℕ) : ℝ) := by rw [two_pow_cast]
            · rcases Nat.eq_zero_or_pos B0 with h0 | hpos
              · rw [h0, Nat.cast_zero, mul_zero]
                positivity
              · have hcard : 0 < ((Finset.range (2 ^ n)).filter
                    (fun r : ℕ => ((2 ^ n : ℕ) : ℤ) ∣ (r : ℤ) ^ 2 - a ∧
                      ((2 ^ (n - 1) : ℕ) : ℤ) ∣ h1 + (r : ℤ) * h2)).card := by
                  rw [← hB0eq]; exact hpos
                have hres := stratum_count_bound n 0 (by omega) (by omega) a h1 h2 ha
                  (one_dvd h2) hD hcard
                obtain ⟨hD1, hcnt1⟩ := hres
                have hB01 : B0 ≤ 1 := by rw [hB0eq]; exact hcnt1
                have hGG : 2 ^ (n - 1) ≤ G := by
                  rw [hG]
                  exact le_gcd_two_pow n (n - 1) _ (by omega) (natAbs_dvd_of_int_dvd (2 ^ (n - 1)) _ hD1)
                calc (2 : ℝ) ^ (n - 1) * (B0 : ℝ)
                    ≤ (2 : ℝ) ^ (n - 1) * 1 := by
                      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                      exact_mod_cast hB01
                  _ ≤ 2 * (G : ℝ) := by
                      have h1' : (2 : ℝ) ^ (n - 1) ≤ ((2 ^ (n - 1) : ℕ) : ℝ) := by
                        rw [two_pow_cast]
                      have h2' : ((2 ^ (n - 1) : ℕ) : ℝ) ≤ (G : ℝ) := by exact_mod_cast hGG
                      linarith
          exact le_trans hnorm hbound
        have hEv_le : ‖(if (2 : ℤ) ∣ h1 ∧ (2 : ℤ) ∣ h2 then
            4 * Tsum (2 ^ (n - 2)) a (h1 / 2) (h2 / 2) else 0)‖
            ≤ ((n : ℝ) - 1) ^ 3 * (G : ℝ) := by
          by_cases hev : (2 : ℤ) ∣ h1 ∧ (2 : ℤ) ∣ h2
          · rw [if_pos hev]
            set g' : ℕ := Nat.gcd (2 ^ (n - 2))
              (((h1 / 2) ^ 2 - a * (h2 / 2) ^ 2).natAbs) with hg'
            have hIH := ih (n - 2) (by omega) a (h1 / 2) (h2 / 2) ha
            have hIH' : ‖Tsum (2 ^ (n - 2)) a (h1 / 2) (h2 / 2)‖
                ≤ (((n - 2 : ℕ) : ℝ) + 1) ^ 3 * (g' : ℝ) := by
              rw [hg']; exact hIH
            have hg4 : (4 : ℝ) * (g' : ℝ) = (G : ℝ) := by
              have hD4 : (4 : ℤ) * ((h1 / 2) ^ 2 - a * (h2 / 2) ^ 2)
                  = h1 ^ 2 - a * h2 ^ 2 := by
                have h1' : (4 : ℤ) * (h1 / 2) ^ 2 = h1 ^ 2 := by
                  conv_rhs => rw [← Int.ediv_mul_cancel hev.1]
                  ring
                have h2' : (4 : ℤ) * (h2 / 2) ^ 2 = h2 ^ 2 := by
                  conv_rhs => rw [← Int.ediv_mul_cancel hev.2]
                  ring
                linear_combination h1' - a * h2'
              have hnat : (h1 ^ 2 - a * h2 ^ 2).natAbs
                  = 4 * ((h1 / 2) ^ 2 - a * (h2 / 2) ^ 2).natAbs := by
                rw [← hD4, Int.natAbs_mul]
                norm_num
              have h2n : 2 ^ n = 4 * 2 ^ (n - 2) := by
                conv_lhs => rw [show n = (n - 2) + 2 by omega]
                ring
              rw [hG, hg', hnat, h2n, Nat.gcd_mul_left]
              push_cast
              ring
            have hnorm : ‖(4 : ℂ) * Tsum (2 ^ (n - 2)) a (h1 / 2) (h2 / 2)‖
                = 4 * ‖Tsum (2 ^ (n - 2)) a (h1 / 2) (h2 / 2)‖ := by
              rw [norm_mul]
              norm_num
            rw [hnorm]
            have hstep := mul_le_mul_of_nonneg_left hIH' (by norm_num : (0:ℝ) ≤ 4)
            calc 4 * ‖Tsum (2 ^ (n - 2)) a (h1 / 2) (h2 / 2)‖
                ≤ 4 * ((((n - 2 : ℕ) : ℝ) + 1) ^ 3 * (g' : ℝ)) := hstep
              _ = (((n - 2 : ℕ) : ℝ) + 1) ^ 3 * (4 * (g' : ℝ)) := by ring
              _ = (((n - 2 : ℕ) : ℝ) + 1) ^ 3 * (G : ℝ) := by rw [hg4]
              _ = ((n : ℝ) - 1) ^ 3 * (G : ℝ) := by
                  have hc : (((n - 2 : ℕ) : ℝ)) + 1 = (n : ℝ) - 1 := by
                    rw [Nat.cast_sub (by omega : 2 ≤ n)]
                    ring
                  rw [hc]
          · rw [if_neg hev, norm_zero]
            have hn3 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
            have h1n : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
            exact mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 1) 3)
              (Nat.cast_nonneg G)
        calc ‖Tup + (if (2 : ℤ) ∣ h1 ∧ (2 : ℤ) ∣ h2 then
              4 * Tsum (2 ^ (n - 2)) a (h1 / 2) (h2 / 2) else 0)‖
            ≤ ‖Tup‖ + ‖(if (2 : ℤ) ∣ h1 ∧ (2 : ℤ) ∣ h2 then
              4 * Tsum (2 ^ (n - 2)) a (h1 / 2) (h2 / 2) else 0)‖ := norm_add_le _ _
          _ ≤ 2 * (G : ℝ) + ((n : ℝ) - 1) ^ 3 * (G : ℝ) := add_le_add hTup_le hEv_le
          _ ≤ ((n : ℝ) + 1) ^ 3 * (G : ℝ) := by
              have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
              have hcube : (2 : ℝ) + ((n : ℝ) - 1) ^ 3 ≤ ((n : ℝ) + 1) ^ 3 := by
                nlinarith [sq_nonneg ((n : ℝ) - 1), hn1]
              have hG0 : (0 : ℝ) ≤ (G : ℝ) := by positivity
              nlinarith [hcube, hG0]
  exact key ν a h1 h2 (odd_of_isUnit_two_pow ν hν a ha)

end

end Work.FIArea2
