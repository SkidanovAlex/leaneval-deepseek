/-
# Element bounds for the Ionescu--Wainger denominator sets (auxiliaries for Area A7)

Auxiliary estimates for `Work.KMTAreas.A7.LpNonAliasAtWindow`: explicit bounds on the elements
of `iwP ρ l` (via `iwPconcrete ρ l = divisors (Q_0^{(l)}) · W_{≤l}`), on `iwW ρ l`, on the
threshold `iwC0 ρ` and on `iwD ρ`, plus the elementary real-power inequality
`2^t ≥ t^4/2` for `t ≥ 16`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedDefs

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open scoped BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-! ## The elementary parameters -/

lemma lp_iwD_gt (ρ : ℝ) : 2 / ρ < (iwD ρ : ℝ) := by
  rw [iwD, Nat.cast_add, Nat.cast_one]
  have := Nat.lt_floor_add_one (2 / ρ)
  linarith

lemma lp_iwD_le (ρ : ℝ) (hρ : 0 < ρ) : (iwD ρ : ℝ) ≤ 2 / ρ + 1 := by
  rw [iwD, Nat.cast_add, Nat.cast_one]
  have := Nat.floor_le (show (0 : ℝ) ≤ 2 / ρ by positivity)
  linarith

lemma lp_iwEps_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < iwEps ρ := by
  rw [iwEps]
  have h2 := mul_lt_mul_of_pos_left (lp_iwD_gt ρ) hρ
  rw [mul_comm ρ (2 / ρ), div_mul_cancel₀ 2 (ne_of_gt hρ)] at h2
  linarith

lemma lp_iwEps_le {ρ : ℝ} (hρ : 0 < ρ) : iwEps ρ ≤ ρ / 2 := by
  rw [iwEps]
  have hmul := mul_le_mul_of_nonneg_left (lp_iwD_le ρ hρ) hρ.le
  have heq : ρ * (2 / ρ + 1) = 2 + ρ := by field_simp
  rw [heq] at hmul
  linarith

/-- `iwC0 ρ ≥ 4/ρ²` for every `ρ > 0`. -/
lemma lp_iwC0_ge {ρ : ℝ} (hρ : 0 < ρ) : 4 / ρ ^ 2 ≤ (iwC0 ρ : ℝ) := by
  have hε := lp_iwEps_pos hρ
  have hεle := lp_iwEps_le hρ
  have h1 : (2 / ρ) * ((1 + iwEps ρ) / iwEps ρ) ≤ (iwC0 ρ : ℝ) := by
    rw [iwC0]
    have h := Nat.le_ceil ((2 / ρ) * ((1 + iwEps ρ) / iwEps ρ))
    push_cast
    linarith
  have h2 : (2 / ρ) * ((1 + iwEps ρ) / iwEps ρ) = (2 / ρ) * (1 / iwEps ρ + 1) := by
    rw [add_div, div_self (ne_of_gt hε)]
  have hinv : 2 / ρ ≤ 1 / iwEps ρ := by
    rw [le_div_iff₀ hε]
    rw [div_mul_eq_mul_div, div_le_iff₀ hρ]
    nlinarith
  rw [h2] at h1
  have h3 : (2 / ρ) * (2 / ρ) ≤ (2 / ρ) * (1 / iwEps ρ + 1) := by
    have hpos : (0 : ℝ) ≤ 2 / ρ := by positivity
    have hle : (2 / ρ : ℝ) ≤ 1 / iwEps ρ + 1 := by linarith [hinv]
    exact mul_le_mul_of_nonneg_left hle hpos
  have h4 : 4 / ρ ^ 2 = (2 / ρ) * (2 / ρ) := by ring
  rw [h4]
  linarith

/-! ## Element bounds for `W_{≤l}` and `P_{≤l}` -/

/-- **Element bound for `W_{≤l}`**: an element is a product of at most `D_ρ` distinct primes
`≤ 2^l`, each taken to a power at most `D_ρ`, hence at most `(2^l)^{D_ρ · D_ρ}`. -/
lemma lp_iwW_le {ρ : ℝ} {l w : ℕ} (hw : w ∈ iwW ρ l) :
    w ≤ (2 ^ l) ^ (iwD ρ * iwD ρ) := by
  classical
  have hw0 : w ≠ 0 := (pos_of_mem_iwW hw).ne'
  have hfact : ∀ p, w.factorization p ≤ iwD ρ := by
    intro p
    have h := iwW_factorization_le hw (q := p)
    split_ifs at h with hmem
    · exact h
    · exact h.trans (Nat.zero_le _)
  have hple : ∀ p ∈ w.factorization.support, p ≤ 2 ^ l := by
    intro p hp
    have hne : w.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    by_cases hmem : p ∈ iwPrimeRange ρ l
    · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).2
    · have h := iwW_factorization_le hw (q := p)
      rw [if_neg hmem] at h
      exact absurd (le_antisymm h (Nat.zero_le _)) hne
  calc w = ∏ p ∈ w.factorization.support, p ^ w.factorization p :=
        (Nat.prod_factorization_pow_eq_self hw0).symm
    _ ≤ ∏ _p ∈ w.factorization.support, (2 ^ l) ^ iwD ρ := by
        refine Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) fun p hp => ?_
        calc p ^ w.factorization p ≤ (2 ^ l) ^ w.factorization p :=
              Nat.pow_le_pow_left (hple p hp) _
          _ ≤ (2 ^ l) ^ iwD ρ := Nat.pow_le_pow_right (by positivity) (hfact p)
    _ = ((2 ^ l) ^ iwD ρ) ^ (w.factorization.support.card) := Finset.prod_const _
    _ ≤ ((2 ^ l) ^ iwD ρ) ^ iwD ρ :=
        Nat.pow_le_pow_right (by positivity) (mem_iwW.mp hw).2
    _ = (2 ^ l) ^ (iwD ρ * iwD ρ) := by rw [pow_mul]

/-- **Element bound for `P_{≤l}` in the second regime**: every `q ∈ iwPconcrete ρ l` is at most
`Q_0^{(l)} · (2^l)^{D_ρ · D_ρ}`. -/
lemma lp_iwPconcrete_le {ρ : ℝ} {l q : ℕ} (hq : q ∈ iwPconcrete ρ l) :
    q ≤ iwQ0 ρ l * (2 ^ l) ^ (iwD ρ * iwD ρ) := by
  rw [mem_iwPconcrete] at hq
  obtain ⟨Q, hQ, w, hw, rfl⟩ := hq
  have hQle : Q ≤ iwQ0 ρ l :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (iwQ0_ne_zero ρ l)) (Nat.mem_divisors.mp hQ).1
  exact Nat.mul_le_mul hQle (lp_iwW_le hw)

/-- The element bound in the first regime: `q ∈ iwP ρ l` and `l ≤ iwC0 ρ` give `q ≤ 2^l`. -/
lemma lp_iwP_le_two_pow {ρ : ℝ} {l q : ℕ} (hq : q ∈ iwP ρ l) (hl : l ≤ iwC0 ρ) :
    q ≤ 2 ^ l := by
  rw [mem_iwP] at hq
  rcases hq with ⟨-, -, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h (not_lt.mpr hl)

/-- `iqQ0 ρ l ≤ (iwN0 ρ l) ^ (iwN0 ρ l * iwD ρ)`. -/
lemma lp_iwQ0_le (ρ : ℝ) (l : ℕ) :
    iwQ0 ρ l ≤ (iwN0 ρ l) ^ (iwN0 ρ l * iwD ρ) := by
  rw [iwQ0]
  calc (iwN0 ρ l).factorial ^ iwD ρ ≤ ((iwN0 ρ l) ^ (iwN0 ρ l)) ^ iwD ρ :=
        Nat.pow_le_pow_left (Nat.factorial_le_pow (iwN0 ρ l)) _
    _ = (iwN0 ρ l) ^ (iwN0 ρ l * iwD ρ) := by rw [pow_mul]

/-- `iwN0 ρ l ≤ 2 · 2^{ρl/2}`. -/
lemma lp_iwN0_le_two (ρ : ℝ) (hρ : 0 ≤ ρ) (l : ℕ) :
    (iwN0 ρ l : ℝ) ≤ 2 * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := by
  rw [iwN0, Nat.cast_add, Nat.cast_one]
  have h1 : ((⌊(2 : ℝ) ^ (ρ * (l : ℝ) / 2)⌋₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) :=
    Nat.floor_le (Real.rpow_nonneg (by norm_num) _)
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  linarith

/-- `n^4 ≤ 2^n` for `n ≥ 16`. -/
lemma lp_nat_pow_four_le : ∀ n : ℕ, 16 ≤ n → n ^ 4 ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro hk
    rcases Nat.lt_or_ge k 16 with hk16 | hk16
    · have h16 : k + 1 = 16 := by omega
      rw [h16]; norm_num
    · have hstep : (k + 1 : ℕ) ^ 4 ≤ 2 * k ^ 4 := by
        have hR : ((k : ℝ) + 1) ^ 4 ≤ 2 * (k : ℝ) ^ 4 := by
          have h1 : (k : ℝ) + 1 ≤ (9 / 8) * (k : ℝ) := by
            have hk8 : (8 : ℝ) ≤ (k : ℝ) := by
              have : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk16
              linarith
            linarith
          have h2 : ((k : ℝ) + 1) ^ 4 ≤ (((9 / 8) * (k : ℝ))) ^ 4 :=
            pow_le_pow_left₀ (by positivity) h1 4
          have h3 : (((9 / 8) * (k : ℝ))) ^ 4 = (9 / 8 : ℝ) ^ 4 * (k : ℝ) ^ 4 := by
            rw [mul_pow]
          have h4 : (9 / 8 : ℝ) ^ 4 ≤ 2 := by norm_num
          have h5 : (9 / 8 : ℝ) ^ 4 * (k : ℝ) ^ 4 ≤ 2 * (k : ℝ) ^ 4 :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
          linarith [h2, h3, h5]
        exact_mod_cast hR
      calc (k + 1) ^ 4 ≤ 2 * k ^ 4 := hstep
        _ ≤ 2 * 2 ^ k := by
            have := ih hk16
            linarith
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- `2^t ≥ t^4/2` for `t ≥ 16`. -/
lemma lp_two_rpow_ge (t : ℝ) (ht : 16 ≤ t) : t ^ 4 / 2 ≤ (2 : ℝ) ^ t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hn : 16 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  have h1 : ((⌊t⌋₊ : ℕ) : ℝ) ^ 4 ≤ (2 : ℝ) ^ (⌊t⌋₊ : ℕ) := by
    have := lp_nat_pow_four_le ⌊t⌋₊ hn
    exact_mod_cast this
  have h2 : (2 : ℝ) ^ (⌊t⌋₊ : ℕ) ≤ (2 : ℝ) ^ t := by
    rw [← Real.rpow_natCast (2 : ℝ) ⌊t⌋₊]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le (le_of_lt ht0))
  have h3 : t - 1 ≤ ((⌊t⌋₊ : ℕ) : ℝ) := Nat.sub_one_lt_floor t |>.le
  have h4 : (0 : ℝ) ≤ t - 1 := by linarith
  have h5 : (t - 1) ^ 4 ≤ ((⌊t⌋₊ : ℕ) : ℝ) ^ 4 := by
    exact pow_le_pow_left₀ h4 h3 4
  have h6 : t ^ 4 / 2 ≤ (t - 1) ^ 4 := by
    have h7 : t ≤ (8 / 7) * (t - 1) := by linarith
    have h8 : t ^ 4 ≤ ((8 / 7) * (t - 1)) ^ 4 := by
      exact pow_le_pow_left₀ (le_of_lt ht0) h7 4
    have h9 : ((8 / 7 : ℝ) * (t - 1)) ^ 4 = (8 / 7) ^ 4 * (t - 1) ^ 4 := by rw [mul_pow]
    rw [h9] at h8
    have h10 : (1 : ℝ) / 2 ≤ (8 / 7 : ℝ) ^ 4 := by norm_num
    have h11 : (t - 1) ^ 4 * (1 / 2) ≤ (t - 1) ^ 4 * (8 / 7) ^ 4 := by
      refine mul_le_mul_of_nonneg_left h10 (by positivity)
    linarith [h11, h8]
  linarith [h1, h2, h5, h6]

end

end Work.KMTAreas.A7
