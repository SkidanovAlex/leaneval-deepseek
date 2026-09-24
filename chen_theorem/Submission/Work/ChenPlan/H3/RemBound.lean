import Mathlib
import Submission.Work.ChenPlan.H3.Defs
import Submission.Work.NumberTheory.Chen.bterm_count_tenth_survivor
import Submission.Work.NumberTheory.Chen.BTermCount.bSharedLevelOfDistribution
import Submission.Work.NumberTheory.Chen.BTermCount.primeCharSumBound

/-!
# The `3^{ω(d)}`-weighted sieve remainder of Chen's `h3`

The sieve used for `h3` (see `Defs.lean`) has remainder

`remSum = Σ_{d ∣ oddPrimLt Y, d < D} 3^{ω(d)} |bRem x M Y d|`,
`bRem x M Y d = #{n ∈ B̄ : d ∣ n - 2} - #B̄/φ(d)`.

Cauchy–Schwarz, exactly as in `Work.NumberPlan.H1.RemBound`, upgrades the two available inputs —
the *unweighted* level of distribution for the corrected remainder
(`bRemCorrLodUnweighted_tenth`, proved in `Submission.Work.NumberTheory.Chen.bterm_count_tenth_survivor`)
and the elementary shared-mass bound (`bShared_sum_le`) — to the weighted sum:

`(Σ 3^{ω(d)}|bRem d|)² ≤ (Σ 9^{ω(d)}|bRem d|)·(Σ |bRem d|)`,

where the first factor is the trivial bound `≪ x (log x)^{10}` supplied by the hypothesis
`TrivInputB` and the second is `≪ x/(log x)^A` for every `A`.
-/

open Finset Filter
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Work.ChenPlan.H3

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight
open Work.NumberTheory.Chen.BTermCount

/-! ## Elementary preliminaries -/

/-- The odd primorial below `Y` is positive. -/
lemma oddPrimLt_pos (Y : ℕ) : 0 < oddPrimLt Y := by
  rw [oddPrimLt_eq_prodOddLt]
  exact Finset.prod_pos (fun p hp => (Submission.mem_oddLt.mp hp).1.pos)

/-- A divisor of the odd primorial is odd. -/
lemma odd_of_dvd_oddPrimLt {M d : ℕ} (h : d ∣ oddPrimLt M) : d % 2 = 1 := by
  have hN := oddPrimLt_odd M
  rcases Nat.eq_zero_or_pos (d % 2) with h0 | hpos
  · have h2 : 2 ∣ d := Nat.dvd_of_mod_eq_zero h0
    have : oddPrimLt M % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans h2 h)
    omega
  · have : d % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega

/-- **Cauchy–Schwarz for the weighted remainder**: the square of the `3^{ω(d)}`-weighted sum is
bounded by the product of the `9^{ω(d)}`-weighted sum and the unweighted sum. -/
lemma pow3_sum_sq_le (s : Finset ℕ) (a : ℕ → ℝ) :
    (∑ d ∈ s, (3 : ℝ) ^ d.primeFactors.card * |a d|) ^ 2
      ≤ (∑ d ∈ s, (9 : ℝ) ^ d.primeFactors.card * |a d|) * (∑ d ∈ s, |a d|) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun d => (3 : ℝ) ^ d.primeFactors.card * Real.sqrt |a d|) (fun d => Real.sqrt |a d|)
  have h3 : ∀ d : ℕ, ((3 : ℝ) ^ d.primeFactors.card * Real.sqrt |a d|)
      * Real.sqrt |a d| = (3 : ℝ) ^ d.primeFactors.card * |a d| := by
    intro d
    rw [mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
  have h9 : ∀ d : ℕ, ((3 : ℝ) ^ d.primeFactors.card * Real.sqrt |a d|) ^ 2
      = (9 : ℝ) ^ d.primeFactors.card * |a d| := by
    intro d
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
    rw [show ((3 : ℝ) ^ d.primeFactors.card) ^ 2 = (9 : ℝ) ^ d.primeFactors.card by
      rw [← pow_mul, show d.primeFactors.card * 2 = 2 * d.primeFactors.card from by ring, pow_mul]
      norm_num]
  have h1 : ∀ d : ℕ, (Real.sqrt |a d|) ^ 2 = |a d| := fun d => Real.sq_sqrt (abs_nonneg _)
  rw [Finset.sum_congr rfl (fun d _ => h3 d), Finset.sum_congr rfl (fun d _ => h9 d),
    Finset.sum_congr rfl (fun d _ => h1 d)] at h
  exact h

/-- The trivial `9^{ω(d)}`-weighted bound on the `B`-term remainder at level `D ≤ √x`
(proved in `Submission.Work.ChenPlan.H3.triv_bound_bRem`; used here as an input). -/
def TrivInputB (C : ℝ) : Prop :=
  ∀ᶠ x : ℕ in Filter.atTop, ∀ (M Y : ℕ) (D : ℝ),
    (x : ℝ) ^ ((1 : ℝ) / 10) ≤ (M : ℝ) →
    (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 3) →
    4 ≤ D → D ≤ Real.sqrt (x : ℝ) →
    ∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < D),
        (9 : ℝ) ^ d.primeFactors.card * |bRem x M Y d|
      ≤ C * (x : ℝ) * (Real.log (x : ℝ)) ^ (10 : ℝ)

/-- `x^{1/10} ≤ chenSiftLimitTenth x`. -/
lemma rpow_tenth_le_chenSiftLimitTenth (x : ℕ) :
    (x : ℝ) ^ ((1 : ℝ) / 10) ≤ (Submission.chenSiftLimitTenth x : ℝ) := by
  have hfl : (x : ℝ) ^ ((1 : ℝ) / 10) < ((⌊Real.rpow (x : ℝ) ((1 : ℝ) / 10)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [Submission.chenSiftLimitTenth, Nat.cast_add, Nat.cast_one]
  exact le_of_lt hfl

/-! ## Reducing the divisor index set -/

/-- Divisors of the odd primorial below the real level `L` form a subset of the odd `d ≤ ⌊L⌋₊`. -/
lemma divisors_filter_subset_Icc (Y : ℕ) (L : ℝ) :
    (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L)
      ⊆ (Finset.Icc 1 ⌊L⌋₊).filter (fun d : ℕ => d % 2 = 1) := by
  intro d hd
  rw [Finset.mem_filter] at hd
  obtain ⟨hddiv, hdD⟩ := hd
  have hdvd : d ∣ oddPrimLt Y := (Nat.mem_divisors.mp hddiv).1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (oddPrimLt_pos Y)
  have hdodd : d % 2 = 1 := odd_of_dvd_oddPrimLt hdvd
  have hle : d ≤ ⌊L⌋₊ := Nat.le_floor (le_of_lt hdD)
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos, hle⟩, hdodd⟩

/-- For `log x ≥ 1` and `B ≤ B'` the level `√x/(log x)^{B'}` is the smaller one, so the
corresponding divisor index sets are nested. -/
lemma divisors_filter_mono_level {x Y : ℕ} {B B' : ℝ} (hlog : 1 ≤ Real.log (x : ℝ)) (hBB : B ≤ B') :
    (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B')
      ⊆ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B) := by
  have hx1 : (0 : ℝ) < (x : ℝ) := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h] at hlog; simp at hlog; linarith
    · exact_mod_cast h
  have hlog0 : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hlog
  intro d hd
  rw [Finset.mem_filter] at hd ⊢
  refine ⟨hd.1, ?_⟩
  have hle : (Real.log (x : ℝ)) ^ B ≤ (Real.log (x : ℝ)) ^ B' :=
    Real.rpow_le_rpow_of_exponent_le hlog hBB
  have h1 : Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B' ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hlog0 B) hle
  exact lt_of_lt_of_le hd.2 h1

/-! ## The shared-mass bound at the tenth sift limit and a general level -/

/-- **The shared-mass bound at a general level `D`.**  Immediate from `bShared_sum_le` (uniform in
`M, Y, D`) and `sum_pow_three_div_totient_le`; the factor `1/M ≤ x^{-1/10}` makes the bound
`≪ x^{9/10}(log x)^6`, which is `≤ x/(log x)^A` for every `A`. -/
theorem bShared_bound_tenth (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      (∑ d ∈ (oddPrimLt (Submission.chenWindowTop x)).divisors.filter
          (fun d : ℕ => (d : ℝ) < Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B),
        (3 : ℝ) ^ d.primeFactors.card *
          ((bShared x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x) d : ℝ)
            / (Nat.totient d : ℝ)))
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  refine ⟨1, by norm_num, ?_⟩
  simp only [Real.rpow_one]
  -- `12 * 2^6 * (log x)^{A+6} ≤ x^{1/10}` eventually
  have hmain : ∀ᶠ x : ℕ in Filter.atTop,
      12 * (2 : ℝ) ^ 6 * (Real.log (x : ℝ)) ^ (A + 6) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) :=
    eventually_nat_log_pow_mul_le_rpow (A + 6) (1 / 10) (by linarith) (by norm_num) _
  have hx2 : ∀ᶠ x : ℕ in Filter.atTop, 2 ≤ x := eventually_ge_atTop 2
  have hlog1 : ∀ᶠ x : ℕ in Filter.atTop, 1 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hmain, hx2, hlog1] with x hmainx hx2x hlog1x
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hlogpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hlog1x
  set M : ℕ := Submission.chenSiftLimitTenth x with hM
  set Y : ℕ := Submission.chenWindowTop x with hY
  set D : ℕ := ⌊Real.sqrt (x : ℝ) / Real.log (x : ℝ)⌋₊ with hD
  have hMge : (x : ℝ) ^ ((1 : ℝ) / 10) ≤ (M : ℝ) := rpow_tenth_le_chenSiftLimitTenth x
  have hM2 : 2 ≤ M := by
    have h1 : 1 ≤ ⌊Real.rpow (x : ℝ) ((1 : ℝ) / 10)⌋₊ := by
      apply Nat.le_floor
      push_cast
      exact Real.one_le_rpow hx1 (by norm_num)
    rw [hM, Submission.chenSiftLimitTenth]
    omega
  have hMY : M ≤ Y := by
    rw [hM, hY]; exact Work.NumberTheory.Chen.chenSiftLimitTenth_le_windowTop x
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hlogD : Real.log (D : ℝ) ≤ Real.log (x : ℝ) := by
    have hDle : (D : ℝ) ≤ (x : ℝ) := by
      rw [hD]
      refine le_trans (Nat.floor_le (div_nonneg (Real.sqrt_nonneg _) hlogpos.le)) ?_
      rw [div_le_iff₀ hlogpos]
      have hsx : Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
        rw [Real.sqrt_le_iff]
        exact ⟨le_of_lt hxpos, by nlinarith⟩
      calc Real.sqrt (x : ℝ) ≤ (x : ℝ) := hsx
        _ = (x : ℝ) * 1 := by ring
        _ ≤ (x : ℝ) * Real.log (x : ℝ) := mul_le_mul_of_nonneg_left hlog1x (le_of_lt hxpos)
    rcases Nat.eq_zero_or_pos D with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith
    · exact Real.log_le_log (by exact_mod_cast hpos) hDle
  -- the index set is contained in the odd part of `[1, D]`
  have hsub : (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < Real.sqrt (x : ℝ) / Real.log (x : ℝ))
      ⊆ (Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1) := by
    intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨hddiv, hdD⟩ := hd
    have hdvd : d ∣ oddPrimLt Y := (Nat.mem_divisors.mp hddiv).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (oddPrimLt_pos Y)
    have hdodd : d % 2 = 1 := odd_of_dvd_oddPrimLt hdvd
    have hle : d ≤ D := by
      rw [hD]; exact Nat.le_floor (le_of_lt hdD)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos, hle⟩, hdodd⟩
  have hstep : (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < Real.sqrt (x : ℝ) / Real.log (x : ℝ)),
        (3 : ℝ) ^ d.primeFactors.card *
          ((bShared x M Y d : ℝ) / (Nat.totient d : ℝ)))
      ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1),
        (3 : ℝ) ^ d.primeFactors.card *
          ((bShared x M Y d : ℝ) / (Nat.totient d : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d hd _ => ?_)
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    have hpos : 0 < Nat.totient d := Nat.totient_pos.mpr (by omega)
    exact mul_nonneg (by positivity) (div_nonneg (by positivity) (by exact_mod_cast hpos.le))
  refine le_trans hstep ?_
  have hbs := bShared_sum_le x M Y D hMY hM2
  have hG := sum_pow_three_div_totient_le D
  have hlogD1 : Real.log (D : ℝ) + 1 ≤ 2 * Real.log (x : ℝ) := by nlinarith [hlogD, hlog1x]
  have hrec : 2 / (M : ℝ) ≤ 2 / ((x : ℝ) ^ ((1 : ℝ) / 10)) :=
    div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hxpos _) hMge
  have hx2R : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2x
  have hx2' : (x : ℝ) + 2 ≤ 2 * (x : ℝ) := by linarith
  have hlog6 : (0 : ℝ) ≤ (Real.log (x : ℝ)) ^ 6 := by positivity
  have h6 : (Real.log (D : ℝ) + 1) ^ 6 ≤ (2 * Real.log (x : ℝ)) ^ 6 :=
    pow_le_pow_left₀ (by positivity) hlogD1 6
  have h2M : (0 : ℝ) ≤ 2 / (M : ℝ) := by positivity
  -- first: the sum is at most `48 (log x)^6 x^{9/10}`
  have hkey : (∑ d ∈ (Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1),
        (3 : ℝ) ^ d.primeFactors.card * ((bShared x M Y d : ℝ) / (Nat.totient d : ℝ)))
      ≤ 768 * (Real.log (x : ℝ)) ^ 6 * (x : ℝ) ^ ((9 : ℝ) / 10) := by
    refine le_trans hbs ?_
    have h1 : 3 * ((x : ℝ) + 2)
        * (∑ m ∈ Finset.Icc 1 D, (3 : ℝ) ^ m.primeFactors.card / (m.totient : ℝ))
        * (2 / (M : ℝ))
        ≤ 3 * ((x : ℝ) + 2) * (Real.log (D : ℝ) + 1) ^ 6 * (2 / (M : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ h2M
      exact mul_le_mul_of_nonneg_left hG (by positivity)
    have h2 : 3 * ((x : ℝ) + 2) * (Real.log (D : ℝ) + 1) ^ 6 * (2 / (M : ℝ))
        ≤ 3 * ((x : ℝ) + 2) * (2 * Real.log (x : ℝ)) ^ 6 * (2 / (M : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ h2M
      exact mul_le_mul_of_nonneg_left h6 (by positivity)
    have h3 : 3 * ((x : ℝ) + 2) * (2 * Real.log (x : ℝ)) ^ 6 * (2 / (M : ℝ))
        ≤ 3 * (2 * (x : ℝ)) * (2 * Real.log (x : ℝ)) ^ 6 * (2 / ((x : ℝ) ^ ((1 : ℝ) / 10))) := by
      have ha : 3 * ((x : ℝ) + 2) ≤ 3 * (2 * (x : ℝ)) := by linarith
      have hb : (2 / (M : ℝ)) ≤ 2 / ((x : ℝ) ^ ((1 : ℝ) / 10)) := hrec
      have hc : (0 : ℝ) ≤ (2 * Real.log (x : ℝ)) ^ 6 := by positivity
      calc 3 * ((x : ℝ) + 2) * (2 * Real.log (x : ℝ)) ^ 6 * (2 / (M : ℝ))
          ≤ 3 * (2 * (x : ℝ)) * (2 * Real.log (x : ℝ)) ^ 6 * (2 / (M : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right ha hc
        _ ≤ 3 * (2 * (x : ℝ)) * (2 * Real.log (x : ℝ)) ^ 6
              * (2 / ((x : ℝ) ^ ((1 : ℝ) / 10))) := by
            refine mul_le_mul_of_nonneg_left hb (by positivity)
    have h4 : 3 * (2 * (x : ℝ)) * (2 * Real.log (x : ℝ)) ^ 6 * (2 / ((x : ℝ) ^ ((1 : ℝ) / 10)))
        = 768 * (Real.log (x : ℝ)) ^ 6 * (x : ℝ) ^ ((9 : ℝ) / 10) := by
      have hx9 : (x : ℝ) * (((x : ℝ) ^ ((1 : ℝ) / 10)))⁻¹ = (x : ℝ) ^ ((9 : ℝ) / 10) := by
        calc (x : ℝ) * (((x : ℝ) ^ ((1 : ℝ) / 10)))⁻¹
            = (x : ℝ) * (x : ℝ) ^ (-((1 : ℝ) / 10)) := by
              rw [← Real.rpow_neg hxpos.le ((1 : ℝ) / 10)]
          _ = (x : ℝ) ^ (1 : ℝ) * (x : ℝ) ^ (-((1 : ℝ) / 10)) := by rw [Real.rpow_one]
          _ = (x : ℝ) ^ ((1 : ℝ) + (-((1 : ℝ) / 10))) :=
              (Real.rpow_add hxpos 1 (-((1 : ℝ) / 10))).symm
          _ = (x : ℝ) ^ ((9 : ℝ) / 10) := by norm_num
      have h2 : (2 / ((x : ℝ) ^ ((1 : ℝ) / 10))) = 2 * (((x : ℝ) ^ ((1 : ℝ) / 10)))⁻¹ :=
        div_eq_mul_inv 2 _
      rw [h2, mul_pow]
      have h3 : 3 * (2 * (x : ℝ)) * (2 ^ 6 * (Real.log (x : ℝ)) ^ 6)
          * (2 * (((x : ℝ) ^ ((1 : ℝ) / 10)))⁻¹)
          = 768 * ((x : ℝ) * (((x : ℝ) ^ ((1 : ℝ) / 10)))⁻¹) * (Real.log (x : ℝ)) ^ 6 := by
        ring
      rw [h3, hx9]
      ring
    linarith [h1, h2, h3, h4.le, h4.ge]
  -- second: `768 (log x)^6 x^{9/10} ≤ x/(log x)^A`
  have hfin : 768 * (Real.log (x : ℝ)) ^ 6 * (x : ℝ) ^ ((9 : ℝ) / 10)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
    have hlogApos : (0 : ℝ) < (Real.log (x : ℝ)) ^ A := Real.rpow_pos_of_pos hlogpos A
    rw [le_div_iff₀ hlogApos]
    have hcomb : 768 * (Real.log (x : ℝ)) ^ 6 * (x : ℝ) ^ ((9 : ℝ) / 10) * (Real.log (x : ℝ)) ^ A
        = 768 * ((Real.log (x : ℝ)) ^ 6 * (Real.log (x : ℝ)) ^ A) * (x : ℝ) ^ ((9 : ℝ) / 10) := by
      ring
    rw [hcomb]
    have hlogcomb : (Real.log (x : ℝ)) ^ 6 * (Real.log (x : ℝ)) ^ A
        = (Real.log (x : ℝ)) ^ (A + 6) := by
      calc (Real.log (x : ℝ)) ^ 6 * (Real.log (x : ℝ)) ^ A
          = (Real.log (x : ℝ)) ^ ((6 : ℕ) : ℝ) * (Real.log (x : ℝ)) ^ A := by
            rw [Real.rpow_natCast]
        _ = (Real.log (x : ℝ)) ^ (((6 : ℕ) : ℝ) + A) :=
            (Real.rpow_add hlogpos ((6 : ℕ) : ℝ) A).symm
        _ = (Real.log (x : ℝ)) ^ (A + 6) := by
          rw [show (((6 : ℕ)) : ℝ) + A = A + 6 from by push_cast; ring]
    rw [hlogcomb]
    have hxsplit : (x : ℝ) = (x : ℝ) ^ ((1 : ℝ) / 10) * (x : ℝ) ^ ((9 : ℝ) / 10) := by
      calc (x : ℝ) = (x : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ = (x : ℝ) ^ ((1 : ℝ) / 10 + (9 : ℝ) / 10) := by norm_num
        _ = (x : ℝ) ^ ((1 : ℝ) / 10) * (x : ℝ) ^ ((9 : ℝ) / 10) :=
            Real.rpow_add hxpos ((1 : ℝ) / 10) ((9 : ℝ) / 10)
    conv_rhs => rw [hxsplit]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (le_of_lt hxpos) ((9 : ℝ) / 10))
    have h48 : 768 * (Real.log (x : ℝ)) ^ (A + 6)
        ≤ 12 * (2 : ℝ) ^ 6 * (Real.log (x : ℝ)) ^ (A + 6) := by
      rw [show (12 : ℝ) * 2 ^ 6 = 768 from by norm_num]
    linarith [h48, hmainx]
  exact le_trans hkey hfin

/-! ## The unweighted remainder bound -/

/-- **The unweighted level of distribution for the naive `B`-term remainder** at the tenth sift
limit and a general level: `Σ_{d ∣ oddPrimLt Y, d < D} |bRem x M Y d| ≤ x/(log x)^A` eventually,
where `D = √x/(log x)^B` with `B` depending only on `A`.  It combines the proved unweighted
level of distribution for the *corrected* remainder (`bRemCorrLodUnweighted_tenth`) with the
elementary shared-mass bound, via `bRem = bRemCorr - bShared/φ`. -/
theorem bRem_abs_sum_bound :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      (∑ d ∈ (oddPrimLt (Submission.chenWindowTop x)).divisors.filter
          (fun d : ℕ => (d : ℝ) < Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B),
        |bRem x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x) d|)
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  intro A hA
  obtain ⟨B₁, hB₁pos, hbv⟩ := Work.NumberTheory.Chen.bRemCorrLodUnweighted_tenth (A + 1) (by linarith)
  obtain ⟨B₂, hB₂pos, hsh⟩ := bShared_bound_tenth (A + 1) (by linarith)
  refine ⟨max B₁ B₂, lt_of_lt_of_le hB₁pos (le_max_left _ _), ?_⟩
  have hlog1 : ∀ᶠ x : ℕ in Filter.atTop, 1 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hlog2 : ∀ᶠ x : ℕ in Filter.atTop, 2 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hbv, hsh, hlog1, hlog2] with x hbvx hshx hlog1x hlog2x
  set Y : ℕ := Submission.chenWindowTop x with hY
  set L₁ : ℝ := Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B₁ with hL₁
  set L₂ : ℝ := Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B₂ with hL₂
  set L : ℝ := Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ max B₁ B₂ with hL
  have hsub1 : (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L)
      ⊆ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₁) := by
    rw [hL, hL₁]
    exact divisors_filter_mono_level hlog1x (le_max_left _ _)
  have hsub2 : (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L)
      ⊆ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₂) := by
    rw [hL, hL₂]
    exact divisors_filter_mono_level hlog1x (le_max_right _ _)
  have hsubD1 : (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₁)
      ⊆ (Finset.Icc 1 ⌊L₁⌋₊).filter (fun d : ℕ => d % 2 = 1) :=
    divisors_filter_subset_Icc Y L₁
  have hbvx' : (∑ d ∈ (Finset.Icc 1 ⌊L₁⌋₊).filter (fun d : ℕ => d % 2 = 1),
      |bRemCorr x (Submission.chenSiftLimitTenth x) Y d|) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) := by
    rw [hY, hL₁]; exact hbvx
  have hshx' : (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₂),
      (3 : ℝ) ^ d.primeFactors.card *
        ((bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ)))
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) := by
    rw [hY, hL₂]; exact hshx
  have hterm : ∀ d : ℕ, |bRem x (Submission.chenSiftLimitTenth x) Y d|
      ≤ |bRemCorr x (Submission.chenSiftLimitTenth x) Y d|
        + (bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ) := by
    intro d
    rw [bRem_eq_bRemCorr_sub]
    have hnn : (0 : ℝ) ≤ (bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    calc |bRemCorr x (Submission.chenSiftLimitTenth x) Y d
          - (bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ)|
        = |bRemCorr x (Submission.chenSiftLimitTenth x) Y d
            + (-((bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ)))| := by
          ring_nf
      _ ≤ |bRemCorr x (Submission.chenSiftLimitTenth x) Y d|
          + |(-((bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ)))| :=
          abs_add_le _ _
      _ = |bRemCorr x (Submission.chenSiftLimitTenth x) Y d|
          + (bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ) := by
          rw [abs_neg, abs_of_nonneg hnn]
  have hshared_nonneg : ∀ d : ℕ, (0 : ℝ)
      ≤ (bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ) :=
    fun d => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  -- split the sum
  have hsplit : (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L),
        |bRem x (Submission.chenSiftLimitTenth x) Y d|)
      ≤ (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₁),
            |bRemCorr x (Submission.chenSiftLimitTenth x) Y d|)
        + (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₂),
            (bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ)) := by
    calc (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L),
          |bRem x (Submission.chenSiftLimitTenth x) Y d|)
        ≤ ∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L),
            (|bRemCorr x (Submission.chenSiftLimitTenth x) Y d|
              + (bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ)) :=
          Finset.sum_le_sum (fun d _ => hterm d)
      _ = (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L),
              |bRemCorr x (Submission.chenSiftLimitTenth x) Y d|)
            + (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L),
              (bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ)) :=
          Finset.sum_add_distrib
      _ ≤ (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₁),
              |bRemCorr x (Submission.chenSiftLimitTenth x) Y d|)
            + (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₂),
              (bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ)) := by
          refine add_le_add ?_ ?_
          · exact Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun d _ _ => abs_nonneg _)
          · exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun d _ _ => hshared_nonneg d)
  -- bound the two pieces by the two inputs
  have hpiece1 : (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₁),
        |bRemCorr x (Submission.chenSiftLimitTenth x) Y d|) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubD1 (fun d _ _ => abs_nonneg _)) hbvx'
  have hpiece2 : (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₂),
        (bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ))
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) := by
    have h1 : (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₂),
          (bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ))
        ≤ ∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₂),
            (3 : ℝ) ^ d.primeFactors.card *
              ((bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ)) := by
      refine Finset.sum_le_sum (fun d _ => ?_)
      have hge : (1 : ℝ) ≤ (3 : ℝ) ^ d.primeFactors.card := one_le_pow₀ (by norm_num)
      calc (bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ)
          = 1 * ((bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ)) := by ring
        _ ≤ (3 : ℝ) ^ d.primeFactors.card *
              ((bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ)) :=
            mul_le_mul_of_nonneg_right hge (hshared_nonneg d)
    exact le_trans h1 hshx'
  -- combine
  have hlogpow : (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) + (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
    have hpos : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hlog1x
    have hpA1 : (0 : ℝ) < (Real.log (x : ℝ)) ^ (A + 1) := Real.rpow_pos_of_pos hpos _
    have hpA : (0 : ℝ) < (Real.log (x : ℝ)) ^ A := Real.rpow_pos_of_pos hpos A
    have hxnn : (0 : ℝ) ≤ (x : ℝ) := by positivity
    have h2 : (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) + (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1)
        = 2 * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1)) := by ring
    rw [h2]
    rw [show 2 * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1))
        = (2 * (x : ℝ)) / (Real.log (x : ℝ)) ^ (A + 1) from by rw [mul_div_assoc]]
    rw [div_le_div_iff₀ hpA1 hpA]
    rw [show (Real.log (x : ℝ)) ^ (A + 1) = (Real.log (x : ℝ)) ^ A * Real.log (x : ℝ) from by
      rw [Real.rpow_add hpos A 1, Real.rpow_one]]
    have h1 : 2 * ((x : ℝ) * (Real.log (x : ℝ)) ^ A)
        ≤ Real.log (x : ℝ) * ((x : ℝ) * (Real.log (x : ℝ)) ^ A) :=
      mul_le_mul_of_nonneg_right hlog2x (mul_nonneg hxnn hpA.le)
    nlinarith [h1]
  calc (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L),
        |bRem x (Submission.chenSiftLimitTenth x) Y d|)
      ≤ (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₁),
              |bRemCorr x (Submission.chenSiftLimitTenth x) Y d|)
            + (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < L₂),
              (bShared x (Submission.chenSiftLimitTenth x) Y d : ℝ) / (Nat.totient d : ℝ)) := hsplit
    _ ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) + (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) :=
        add_le_add hpiece1 hpiece2
    _ ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := hlogpow

/-! ## The `3^{ω(d)}`-weighted remainder via Cauchy–Schwarz -/

/-- **The `h3` sieve remainder is `o(x/(log x)^2)`.**  From the trivial `9^{ω(d)}`-weighted bound
`TrivInputB C` and the unweighted level of distribution `bRem_abs_sum_bound` (applied with
exponent `2A + 20`), Cauchy–Schwarz gives, at level `D = √x/(log x)^B`,
`remSum ≤ x/(log x)^A` for every `A > 0`. -/
theorem remSum_bound (C : ℝ) (hC : 0 < C) (hW : TrivInputB C) :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      Submission.ChenPlan.remSum
          (bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
          (Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B)
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  intro A hA
  obtain ⟨B, hBpos, hrem⟩ := bRem_abs_sum_bound (2 * A + 20) (by linarith)
  refine ⟨B, hBpos, ?_⟩
  -- `4 ≤ D` eventually, where `D = √x/(log x)^B`
  have hD4 : ∀ᶠ x : ℕ in Filter.atTop,
      4 * (Real.log (x : ℝ)) ^ B ≤ Real.sqrt (x : ℝ) := by
    have h := eventually_nat_log_pow_mul_le_rpow B (1 / 2) hBpos (by norm_num) (4 : ℝ)
    filter_upwards [h] with x hx
    rwa [Real.sqrt_eq_rpow]
  have hlog1 : ∀ᶠ x : ℕ in Filter.atTop, 1 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hlogbig : ∀ᶠ x : ℕ in Filter.atTop, Real.sqrt C ≤ (Real.log (x : ℝ)) ^ 5 := by
    have h := eventually_const_le_nat_log (max 1 (C + 1))
    filter_upwards [h] with x hx
    have h1 : 1 ≤ Real.log (x : ℝ) := le_trans (le_max_left _ _) hx
    have h2 : C + 1 ≤ Real.log (x : ℝ) := le_trans (le_max_right _ _) hx
    have h3 : Real.sqrt C ≤ C + 1 := by
      have h4 := Real.sq_sqrt (le_of_lt hC)
      nlinarith [Real.sqrt_nonneg C, hC]
    calc Real.sqrt C ≤ C + 1 := h3
      _ ≤ Real.log (x : ℝ) := h2
      _ ≤ (Real.log (x : ℝ)) ^ 5 := le_self_pow₀ h1 (by norm_num)
  filter_upwards [hW, hrem, hD4, hlog1, hlogbig, eventually_ge_atTop 8] with x hWx hremx hD4x hlog1x hlogbigx hx8
  set Y : ℕ := Submission.chenWindowTop x with hY
  set M : ℕ := Submission.chenSiftLimitTenth x with hM
  set L : ℝ := Real.log (x : ℝ) with hL
  set D : ℝ := Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B with hD
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hLpos : 0 < L := by rw [hL]; exact lt_of_lt_of_le one_pos hlog1x
  have hsqrtL : Real.sqrt C ≤ L ^ (5 : ℕ) := by rw [hL]; exact hlogbigx
  have hDle : D ≤ Real.sqrt (x : ℝ) := by
    rw [hD, div_le_iff₀ (Real.rpow_pos_of_pos hLpos B)]
    have h1 : (1 : ℝ) ≤ L ^ B := Real.one_le_rpow hlog1x hBpos.le
    calc Real.sqrt (x : ℝ) ≤ Real.sqrt (x : ℝ) * 1 := by rw [mul_one]
      _ ≤ Real.sqrt (x : ℝ) * L ^ B := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
  have hDge4 : 4 ≤ D := by
    rw [hD, le_div_iff₀ (Real.rpow_pos_of_pos hLpos B)]
    have := hD4x
    rw [hL] at this
    linarith
  have hMge : (x : ℝ) ^ ((1 : ℝ) / 10) ≤ (M : ℝ) := by rw [hM]; exact rpow_tenth_le_chenSiftLimitTenth x
  have hYle : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [hY]; exact chenWindowTop_le_two_rpow x hx8
  -- the two factors of Cauchy–Schwarz
  have h9 : (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < D),
        (9 : ℝ) ^ d.primeFactors.card * |bRem x M Y d|)
      ≤ C * (x : ℝ) * (Real.log (x : ℝ)) ^ (10 : ℝ) := by
    exact hWx M Y D hMge hYle hDge4 hDle
  have h1 : (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < D),
        |bRem x M Y d|) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (2 * A + 20) := by
    have := hremx
    rw [hD, hL] at this
    exact this
  have hCS := pow3_sum_sq_le ((oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < D))
    (fun d => bRem x M Y d)
  have h9nn : (0 : ℝ) ≤ ∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < D),
      |bRem x M Y d| :=
    Finset.sum_nonneg (fun d _ => abs_nonneg _)
  have hsq : (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < D),
        (3 : ℝ) ^ d.primeFactors.card * |bRem x M Y d|) ^ 2
      ≤ (C * (x : ℝ) * L ^ (10 : ℝ)) * ((x : ℝ) / L ^ (2 * A + 20)) := by
    refine le_trans hCS (mul_le_mul ?_ ?_ h9nn (by positivity))
    · simpa [hL] using h9
    · simpa [hL] using h1
  -- the product is a square
  have hval : (C * (x : ℝ) * L ^ (10 : ℝ)) * ((x : ℝ) / L ^ (2 * A + 20))
      = (Real.sqrt C * ((x : ℝ) / L ^ (A + 5))) ^ 2 := by
    have h1 : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC.le
    have hL20 : L ^ (2 * A + 20) = L ^ (10 : ℝ) * L ^ (2 * A + 10) := by
      rw [show (2 * A + 20 : ℝ) = 10 + (2 * A + 10) from by ring, Real.rpow_add hLpos]
    have hL5' : L ^ (A + 5) * L ^ (A + 5) = L ^ (2 * A + 10) := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    have hsq5 : (L ^ (A + 5)) ^ 2 = L ^ (2 * A + 10) := by rw [pow_two, hL5']
    rw [hL20, mul_pow, div_pow, hsq5, h1]
    field_simp
  rw [hval] at hsq
  have hsqrt : (∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < D),
        (3 : ℝ) ^ d.primeFactors.card * |bRem x M Y d|)
      ≤ Real.sqrt C * ((x : ℝ) / L ^ (A + 5)) := by
    calc _ ≤ Real.sqrt ((Real.sqrt C * ((x : ℝ) / L ^ (A + 5))) ^ 2) :=
          Real.le_sqrt_of_sq_le hsq
      _ = Real.sqrt C * ((x : ℝ) / L ^ (A + 5)) := Real.sqrt_sq (by positivity)
  -- and the right-hand side is `≤ x/L^A`
  have hfin : Real.sqrt C * ((x : ℝ) / L ^ (A + 5)) ≤ (x : ℝ) / L ^ A := by
    have hLsplit : L ^ (A + 5) = L ^ A * L ^ (5 : ℝ) := by
      rw [Real.rpow_add hLpos]
    have hL5pos : (0 : ℝ) < L ^ (5 : ℝ) := Real.rpow_pos_of_pos hLpos 5
    have hLApos : (0 : ℝ) < L ^ A := Real.rpow_pos_of_pos hLpos A
    have hrew : Real.sqrt C * ((x : ℝ) / L ^ (A + 5))
        = (Real.sqrt C / L ^ (5 : ℝ)) * ((x : ℝ) / L ^ A) := by
      rw [hLsplit, div_mul_eq_div_div]
      ring
    rw [hrew]
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [div_le_one hL5pos]
    simpa [Real.rpow_natCast] using hsqrtL
  have hrewrite : Submission.ChenPlan.remSum (bSieve x M Y) D
      = ∑ d ∈ (oddPrimLt Y).divisors.filter (fun d : ℕ => (d : ℝ) < D),
          (3 : ℝ) ^ d.primeFactors.card * |bRem x M Y d| := by
    rw [bSieve_remSum]
  rw [hrewrite]
  simpa [hL] using le_trans hsqrt hfin

end

end Work.ChenPlan.H3
