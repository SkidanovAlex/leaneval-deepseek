import Mathlib
import Submission.Chen.SwitchDefs
import Submission.Work.NumberTheory.Chen.APSwitchUpper.level_of_distribution_theta_shift

/-!
# The `3^{ω(d)}`-weighted sieve remainder of Chen's `h1` is `≤ (1/500) x V`

The Bombieri–Vinogradov level of distribution for the shifted `θ`-function
(`Work.NumberTheory.Chen.APSwitchUpper.level_of_distribution_theta_shift`) bounds the *unweighted*
remainder sum `Σ_{d ≤ √x/(log x)^B, d odd} |r_d|`.  Cauchy–Schwarz upgrades it to the
`3^{ω(d)}`-weighted sum that the linear sieve produces:

`(Σ_{d ∈ S} 3^{ω(d)}|r_d|)² ≤ (Σ_{d ∈ S} 9^{ω(d)}|r_d|)·(Σ_{d ∈ S} |r_d|)`,

the first factor being the trivial bound `≪ x (log x)^{10}`.  With the level
`D = M^{49/10} ≤ √x/(log x)^B` (`M = ⌊x^{1/10}⌋ + 1`) and the Mertens lower bound
`x·VsieveOdd M ≥ (34/5)·x/log x` this gives `1/500`, exactly the margin left by
`LinearSieveLower` (`993/1000 - 1/1000 - 99/100 = 1/500`) for the `h1` constant `99/100`.

The trivial weighted bound and the level arithmetic are hypotheses here (`TrivInput`,
`chenLevel_eventually`), so this module does not depend on their proofs.
-/

open Finset
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Work.ChenPlan.H1

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight

/-- A divisor of the odd primorial is odd. -/
lemma odd_of_dvd_oddPrimLt {M d : ℕ} (h : d ∣ oddPrimLt M) : d % 2 = 1 := by
  have hN := oddPrimLt_odd M
  rcases Nat.eq_zero_or_pos (d % 2) with h0 | hpos
  · have h2 : 2 ∣ d := Nat.dvd_of_mod_eq_zero h0
    have : oddPrimLt M % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans h2 h)
    omega
  · have : d % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega

/-- The odd primorial below `M` is positive. -/
lemma oddPrimLt_pos (M : ℕ) : 0 < oddPrimLt M := by
  rw [oddPrimLt_eq_prod_oddLt]
  refine Finset.prod_pos (fun p hp => ?_)
  simp only [oddLt, Finset.mem_filter, Finset.mem_range] at hp
  exact hp.2.1.pos

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
    have hs : Real.sqrt |a d| ^ 2 = |a d| := Real.sq_sqrt (abs_nonneg _)
    rw [mul_pow, hs]
    congr 1
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have h1 : ∀ d : ℕ, (Real.sqrt |a d|) ^ 2 = |a d| := fun d => Real.sq_sqrt (abs_nonneg _)
  rw [Finset.sum_congr rfl (fun d _ => h3 d), Finset.sum_congr rfl (fun d _ => h9 d),
    Finset.sum_congr rfl (fun d _ => h1 d)] at h
  exact h

/-- The Bombieri–Vinogradov level of distribution in the form used below. -/
lemma bv_level_of_distribution :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      Work.NumberTheory.Chen.APSwitchUpper.bvSum x
          ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (20 : ℝ) :=
  Work.NumberTheory.Chen.APSwitchUpper.level_of_distribution_theta_shift 20 (by norm_num)

/-- The trivial (weighted) bound on the remainder sum, as a hypothesis. -/
def TrivInput (C : ℝ) : Prop :=
  ∀ᶠ x : ℕ in Filter.atTop, ∀ (M : ℕ) (D : ℝ),
    4 ≤ D → D ≤ Real.sqrt (x : ℝ) →
    ∑ d ∈ (oddPrimLt M).divisors.filter (fun d : ℕ => (d : ℝ) < D),
        (9 : ℝ) ^ d.primeFactors.card * |rD x d|
      ≤ C * (x : ℝ) * (Real.log (x : ℝ)) ^ 10

set_option maxHeartbeats 1600000 in
/-- **The remainder bound.**  From the trivial weighted bound, Bombieri–Vinogradov at quality `20`,
the level arithmetic and the Mertens lower bound, the `3^{ω(d)}`-weighted remainder of the linear
sieve at level `M^{49/10}` is at most `(1/500)·x·VsieveOdd M`. -/
theorem remBound_of_inputs (C : ℝ) (hC : 0 < C) (hW : TrivInput C) (B : ℝ) (hB : 0 < B)
    (hbv : ∀ᶠ x : ℕ in Filter.atTop,
      Work.NumberTheory.Chen.APSwitchUpper.bvSum x
          ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (20 : ℝ))
    (hcl : (∀ D₀ : ℝ, ∀ᶠ x : ℕ in Filter.atTop,
        D₀ ≤ (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10)) ∧
      (∀ᶠ x : ℕ in Filter.atTop,
        (1 : ℝ) < (Submission.chenSiftLimitTenth x : ℝ) ∧
        (4 : ℝ) ≤ (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10) ∧
        (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10)
          ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B))
    (hV : ∀ᶠ x : ℕ in Filter.atTop,
      (34 / 5 : ℝ) * (x : ℝ)
        ≤ (x : ℝ) * VsieveOdd (Submission.chenSiftLimitTenth x) * Real.log (x : ℝ)) :
    ∀ᶠ x : ℕ in Filter.atTop,
      ∑ d ∈ (oddPrimLt (Submission.chenSiftLimitTenth x)).divisors.filter
            (fun d : ℕ => (d : ℝ) < (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10)),
          (3 : ℝ) ^ d.primeFactors.card * |rD x d|
      ≤ (1 / 500) * (x : ℝ) * VsieveOdd (Submission.chenSiftLimitTenth x) := by
  obtain ⟨hD0, hlev⟩ := hcl
  have hlogev : ∀ᶠ x : ℕ in Filter.atTop,
      Real.sqrt C ≤ (34 / 2500 : ℝ) * (Real.log (x : ℝ)) ^ 4 := by
    have h1 : Filter.Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h4 : Filter.Tendsto (fun y : ℝ => y ^ 4) Filter.atTop Filter.atTop := by
      have := tendsto_rpow_atTop (y := (4 : ℝ)) (by norm_num)
      simpa [Real.rpow_natCast] using this
    have h2 : Filter.Tendsto (fun x : ℕ => (34 / 2500 : ℝ) * (Real.log (x : ℝ)) ^ 4)
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) (h4.comp h1)
    exact h2.eventually_ge_atTop (Real.sqrt C)
  filter_upwards [hW, hbv, hlev, hD0 (D₀ := 1), hlogev, hV, Filter.eventually_ge_atTop 8]
    with x hWx hbvx hlevx hD0x hlogx hVx hx8
  obtain ⟨hM1, hD4, hDle⟩ := hlevx
  set M : ℕ := Submission.chenSiftLimitTenth x with hMdef
  set D : ℝ := (M : ℝ) ^ ((49 : ℝ) / 10) with hDdef
  have hx8' : (8 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx8
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  have hL1 : 1 ≤ Real.log (x : ℝ) := by
    rw [Real.le_log_iff_exp_le (y := (x : ℝ)) hxpos]
    have := Real.exp_one_lt_three
    linarith
  have hLB1 : 1 ≤ (Real.log (x : ℝ)) ^ B := Real.one_le_rpow hL1 (le_of_lt hB)
  have hDle' : D ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B := by
    rw [hDdef, hMdef]; exact hDle
  have hD4' : 4 ≤ D := by rw [hDdef, hMdef]; exact hD4
  have hDsqrt : D ≤ Real.sqrt (x : ℝ) := by
    have h : Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B ≤ Real.sqrt (x : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.sqrt_nonneg (x : ℝ)]
    linarith
  -- transport the goal to the abbreviated sieve quantities
  have hgoal : (oddPrimLt (Submission.chenSiftLimitTenth x)).divisors.filter
        (fun d : ℕ => (d : ℝ) < (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10))
      = (oddPrimLt M).divisors.filter (fun d : ℕ => (d : ℝ) < D) := by
    rw [hMdef, hDdef]
  rw [hgoal]
  have hA : ∑ d ∈ (oddPrimLt M).divisors.filter (fun d : ℕ => (d : ℝ) < D),
        (9 : ℝ) ^ d.primeFactors.card * |rD x d|
      ≤ C * (x : ℝ) * (Real.log (x : ℝ)) ^ 10 := hWx M D hD4' hDsqrt
  have hbvnat : Work.NumberTheory.Chen.APSwitchUpper.bvSum x
        ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 20 := by
    simpa [Real.rpow_natCast] using hbvx
  have hB' : ∑ d ∈ (oddPrimLt M).divisors.filter (fun d : ℕ => (d : ℝ) < D), |rD x d|
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 20 := by
    have hsub : (oddPrimLt M).divisors.filter (fun d : ℕ => (d : ℝ) < D)
        ⊆ (Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter
            (fun d : ℕ => d % 2 = 1) := by
      intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨hddiv, hdD⟩ := hd
      have hdvd : d ∣ oddPrimLt M := (Nat.mem_divisors.mp hddiv).1
      have hdne : d ≠ 0 := fun h0 => by
        rw [h0] at hdvd
        have := Nat.pos_of_dvd_of_pos hdvd (oddPrimLt_pos M)
        omega
      have hdodd : d % 2 = 1 := odd_of_dvd_oddPrimLt hdvd
      have hdle : d ≤ ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ := by
        rw [Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B)]
        linarith [hdD, hDle']
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hdle⟩, hdodd⟩
    have h2 : Work.NumberTheory.Chen.APSwitchUpper.bvSum x
          ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊
        = ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter
            (fun d : ℕ => d % 2 = 1), |rD x d| := rfl
    rw [h2] at hbvnat
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => abs_nonneg _)) hbvnat
  have hWsq : (∑ d ∈ (oddPrimLt M).divisors.filter (fun d : ℕ => (d : ℝ) < D),
        (3 : ℝ) ^ d.primeFactors.card * |rD x d|) ^ 2
      ≤ (C * (x : ℝ) * (Real.log (x : ℝ)) ^ 10)
        * ((x : ℝ) / (Real.log (x : ℝ)) ^ 20) :=
    le_trans (pow3_sum_sq_le _ (fun d => rD x d))
      (mul_le_mul hA hB' (Finset.sum_nonneg (fun d _ => abs_nonneg _)) (by positivity))
  have hWbound : ∑ d ∈ (oddPrimLt M).divisors.filter (fun d : ℕ => (d : ℝ) < D),
        (3 : ℝ) ^ d.primeFactors.card * |rD x d|
      ≤ Real.sqrt C * ((x : ℝ) / (Real.log (x : ℝ)) ^ 5) := by
    have hval : C * (x : ℝ) * (Real.log (x : ℝ)) ^ 10
          * ((x : ℝ) / (Real.log (x : ℝ)) ^ 20)
        = (Real.sqrt C * ((x : ℝ) / (Real.log (x : ℝ)) ^ 5)) ^ 2 := by
      have h1 : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt (le_of_lt hC)
      have h2 : (Real.log (x : ℝ)) ^ 20
          = (Real.log (x : ℝ)) ^ 10 * (Real.log (x : ℝ)) ^ 10 := by ring
      rw [h2, mul_pow, h1]
      field_simp
    rw [hval] at hWsq
    calc _ ≤ Real.sqrt ((Real.sqrt C * ((x : ℝ) / (Real.log (x : ℝ)) ^ 5)) ^ 2) :=
          (Real.le_sqrt (Finset.sum_nonneg (fun d _ => mul_nonneg (by positivity) (abs_nonneg _)))
            (by positivity)).mpr hWsq
      _ = Real.sqrt C * ((x : ℝ) / (Real.log (x : ℝ)) ^ 5) :=
          Real.sqrt_sq (by positivity)
  have hVlow : (34 / 2500 : ℝ) * ((x : ℝ) / Real.log (x : ℝ))
      ≤ (1 / 500) * (x : ℝ) * VsieveOdd M := by
    have h' : (34 / 5 : ℝ) * (x : ℝ) ≤ (x : ℝ) * VsieveOdd M * Real.log (x : ℝ) := by
      rw [hMdef]; exact hVx
    have hstep : (34 / 2500 : ℝ) * ((x : ℝ) / Real.log (x : ℝ))
        = ((34 / 5 : ℝ) * (x : ℝ)) / (500 * Real.log (x : ℝ)) := by
      field_simp
      ring
    rw [hstep, div_le_iff₀ (by positivity : (0 : ℝ) < 500 * Real.log (x : ℝ))]
    nlinarith [h', hLpos, le_of_lt hxpos]
  calc _ ≤ Real.sqrt C * ((x : ℝ) / (Real.log (x : ℝ)) ^ 5) := hWbound
    _ ≤ (34 / 2500 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by
        have hb : Real.sqrt C ≤ (34 / 2500 : ℝ) * (Real.log (x : ℝ)) ^ 4 := hlogx
        have hsplit : Real.sqrt C * ((x : ℝ) / (Real.log (x : ℝ)) ^ 5)
            = (Real.sqrt C / (Real.log (x : ℝ)) ^ 4) * ((x : ℝ) / Real.log (x : ℝ)) := by
          field_simp
        rw [hsplit]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Real.log (x : ℝ)) ^ 4)]
        simpa [mul_comm] using hb
    _ ≤ (1 / 500) * (x : ℝ) * VsieveOdd M := hVlow

end

end Work.ChenPlan.H1
