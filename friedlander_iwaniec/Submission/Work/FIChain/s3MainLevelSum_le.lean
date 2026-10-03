import Mathlib
import Submission.Work.FIChain.s3MainLevelDefs
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.zc_sharp_bounds
import Submission.Work.FIChain.Yc_lower_sharp
import Submission.Work.FIChain.main_ebd_sum_le
import Submission.Work.FIChain.s3RemPlus_maj
import Submission.Work.FIChain.S3plusC_machinery

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## `σ̃` is submultiplicative -/

lemma one_le_sigmaTilde (n : ℕ) : (1 : ℝ) ≤ sigmaTilde n := by
  rw [sigmaTilde]
  exact Finset.one_le_prod₀ (fun p _ => by
    have : (0 : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := by positivity
    linarith)

lemma sigmaTilde_mul_le (m n : ℕ) : sigmaTilde (m * n) ≤ sigmaTilde m * sigmaTilde n := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have h0 : sigmaTilde 0 = 1 := by simp [sigmaTilde]
    simp only [zero_mul]
    rw [h0, one_mul]; exact one_le_sigmaTilde n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : sigmaTilde 0 = 1 := by simp [sigmaTilde]
    simp only [mul_zero]
    rw [h0, mul_one]; exact one_le_sigmaTilde m
  have hf1 : ∀ p ∈ m.primeFactors ∪ n.primeFactors, (0 : ℝ) ≤ 1 + 1 / Real.sqrt (p : ℝ) :=
    fun p _ => by positivity
  have hstep : ∏ p ∈ n.primeFactors \ m.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))
      ≤ ∏ p ∈ n.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) :=
    Finset.prod_le_prod_of_subset_of_one_le₀ Finset.sdiff_subset
      (fun p hp => hf1 p (Finset.mem_union_right _ (Finset.sdiff_subset hp)))
      (fun p _ _ => le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt (p : ℝ)))
  have hdisj : Disjoint m.primeFactors (n.primeFactors \ m.primeFactors) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp hb).2 ha
  have hunion : m.primeFactors ∪ n.primeFactors
      = m.primeFactors ∪ (n.primeFactors \ m.primeFactors) := by
    ext a
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hA : (0 : ℝ) ≤ ∏ p ∈ m.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) :=
    Finset.prod_nonneg (fun p hp => hf1 p (Finset.mem_union_left _ hp))
  rw [sigmaTilde, sigmaTilde, sigmaTilde, Nat.primeFactors_mul hm.ne' hn.ne', hunion,
    Finset.prod_union hdisj]
  nlinarith [hstep, hA]

/-- The `(e,d)`-summand bound: combining the `(2.4)`-window bound `hW` with the
submultiplicativity of `σ̃` and the factorisations `g̃(e·b·d) = g̃(e)g̃(b)g̃(d)`. -/
lemma levelWindow_inner_le
    (Cw : ℝ) (hCw : 0 < Cw)
    (hW : ∀ (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) (u : ℝ) (e d : ℕ) (lam : ℕ → ℝ) (Δ : ℕ),
      (∀ ν : ℕ, Δ < ν → lam ν = 0) → (∀ ν : ℕ, |lam ν| ≤ 1) →
      1 ≤ e → 1 ≤ d → 0 < u → 0 < z → 0 < sz → 1 < sy / (Δ : ℝ) →
      |∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
            * Submission.ASP.FIgtil (e * b * d)|
        ≤ Cw * Submission.ASP.FIgtil e * Submission.ASP.FIgtil d
            * (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ ν₂ ∈ e.divisors,
                Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| * sigmaTilde (e * d * ν₁))
            * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ)))
    (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) (u : ℝ) (e d : ℕ) (lam : ℕ → ℝ) (Δ : ℕ)
    (hlam : ∀ ν : ℕ, Δ < ν → lam ν = 0) (hlam1 : ∀ ν : ℕ, |lam ν| ≤ 1)
    (he : 1 ≤ e) (hd : 1 ≤ d) (hu : 0 < u) (hz : 0 < z) (hsz : 0 < sz)
    (hsyΔ : 1 < sy / (Δ : ℝ)) :
    |∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
        (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
          * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d)|
      ≤ Cw * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ))
          * (Submission.ASP.FIgtil e * sigmaTilde e * ((e.divisors.card : ℕ) : ℝ)
              * (∑ ν₁ ∈ Finset.Icc 1 Δ, Submission.ASP.FIgtil ν₁ * sigmaTilde ν₁))
          * (Submission.ASP.FIgtil d * sigmaTilde d) := by
  have hgd : 0 ≤ Submission.ASP.FIgtil d := Submission.ASP.FIgtil_nonneg d
  have hge : 0 ≤ Submission.ASP.FIgtil e := Submission.ASP.FIgtil_nonneg e
  have hσe : 0 ≤ sigmaTilde e := le_trans zero_le_one (one_le_sigmaTilde e)
  have hσd : 0 ≤ sigmaTilde d := le_trans zero_le_one (one_le_sigmaTilde d)
  have hA0 : 0 ≤ ∑ ν₁ ∈ Finset.Icc 1 Δ, Submission.ASP.FIgtil ν₁ * sigmaTilde ν₁ :=
    Finset.sum_nonneg (fun ν _ => mul_nonneg (Submission.ASP.FIgtil_nonneg ν)
      (le_trans zero_le_one (one_le_sigmaTilde ν)))
  -- pull the constant `μ d` out of the `b`-sum
  have hpull : (∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
        (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
          * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d))
      = (ArithmeticFunction.moebius d : ℝ) * (∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
            * Submission.ASP.FIgtil (e * b * d)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hpull, abs_mul]
  have hμd : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := d)
    exact_mod_cast h
  have hW' := hW x z sz Cm sy n u e d lam Δ hlam hlam1 he hd hu hz hsz hsyΔ
  -- the `(ν₁,ν₂)`-sum is at most `σ̃(e)σ̃(d)·τ(e)·A₀`
  have hsum : (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ ν₂ ∈ e.divisors,
        Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| * sigmaTilde (e * d * ν₁))
      ≤ sigmaTilde e * sigmaTilde d * ((e.divisors.card : ℕ) : ℝ)
          * (∑ ν₁ ∈ Finset.Icc 1 Δ, Submission.ASP.FIgtil ν₁ * sigmaTilde ν₁) := by
    have hstep1 : ∀ ν₁ ∈ Finset.Icc 1 Δ, ∀ ν₂ ∈ e.divisors,
        Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| * sigmaTilde (e * d * ν₁)
          ≤ Submission.ASP.FIgtil ν₁ * sigmaTilde ν₁ * (sigmaTilde e * sigmaTilde d) := by
      intro ν₁ hν₁ ν₂ hν₂
      have hgν : 0 ≤ Submission.ASP.FIgtil ν₁ := Submission.ASP.FIgtil_nonneg ν₁
      have hσν : 0 ≤ sigmaTilde ν₁ := le_trans zero_le_one (one_le_sigmaTilde ν₁)
      have hσ1 : 0 ≤ sigmaTilde (e * d * ν₁) := le_trans zero_le_one (one_le_sigmaTilde _)
      have hlb : |lam (ν₁ * ν₂)| ≤ 1 := hlam1 (ν₁ * ν₂)
      have h1 : Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| ≤ Submission.ASP.FIgtil ν₁ * 1 :=
        mul_le_mul_of_nonneg_left hlb hgν
      have h2 : sigmaTilde (e * d * ν₁) ≤ sigmaTilde (e * d) * sigmaTilde ν₁ :=
        sigmaTilde_mul_le (e * d) ν₁
      have h3 : sigmaTilde (e * d) ≤ sigmaTilde e * sigmaTilde d := sigmaTilde_mul_le e d
      have h4 : 0 ≤ sigmaTilde (e * d) := le_trans zero_le_one (one_le_sigmaTilde _)
      calc Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| * sigmaTilde (e * d * ν₁)
          ≤ Submission.ASP.FIgtil ν₁ * 1 * sigmaTilde (e * d * ν₁) :=
            mul_le_mul_of_nonneg_right h1 hσ1
        _ = Submission.ASP.FIgtil ν₁ * sigmaTilde (e * d * ν₁) := by ring
        _ ≤ Submission.ASP.FIgtil ν₁ * (sigmaTilde (e * d) * sigmaTilde ν₁) :=
            mul_le_mul_of_nonneg_left h2 hgν
        _ ≤ Submission.ASP.FIgtil ν₁ * ((sigmaTilde e * sigmaTilde d) * sigmaTilde ν₁) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hσν) hgν
        _ = Submission.ASP.FIgtil ν₁ * sigmaTilde ν₁ * (sigmaTilde e * sigmaTilde d) := by ring
    calc (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ ν₂ ∈ e.divisors,
          Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| * sigmaTilde (e * d * ν₁))
        ≤ ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ _ν₂ ∈ e.divisors,
            Submission.ASP.FIgtil ν₁ * sigmaTilde ν₁ * (sigmaTilde e * sigmaTilde d) :=
          Finset.sum_le_sum (fun ν₁ hν₁ => Finset.sum_le_sum (fun ν₂ hν₂ => hstep1 ν₁ hν₁ ν₂ hν₂))
      _ = ((e.divisors.card : ℕ) : ℝ)
            * (∑ ν₁ ∈ Finset.Icc 1 Δ,
                Submission.ASP.FIgtil ν₁ * sigmaTilde ν₁ * (sigmaTilde e * sigmaTilde d)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun ν₁ _ => ?_)
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = sigmaTilde e * sigmaTilde d * ((e.divisors.card : ℕ) : ℝ)
            * (∑ ν₁ ∈ Finset.Icc 1 Δ, Submission.ASP.FIgtil ν₁ * sigmaTilde ν₁) := by
          rw [show (∑ ν₁ ∈ Finset.Icc 1 Δ,
                Submission.ASP.FIgtil ν₁ * sigmaTilde ν₁ * (sigmaTilde e * sigmaTilde d))
              = (sigmaTilde e * sigmaTilde d)
                * (∑ ν₁ ∈ Finset.Icc 1 Δ, Submission.ASP.FIgtil ν₁ * sigmaTilde ν₁) from ?_]
          · ring
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun ν₁ _ => ?_)
          ring
  have hlog6 : 0 < (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ)) :=
    Real.rpow_pos_of_pos (Real.log_pos (by
      have : (1:ℝ) < max (sy / (Δ:ℝ)) 2 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
      exact this)) _
  calc |(ArithmeticFunction.moebius d : ℝ)| * |∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
            * Submission.ASP.FIgtil (e * b * d)|
      ≤ 1 * (Cw * Submission.ASP.FIgtil e * Submission.ASP.FIgtil d
            * (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ ν₂ ∈ e.divisors,
                Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| * sigmaTilde (e * d * ν₁))
            * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ))) := by
          refine mul_le_mul hμd hW' (abs_nonneg _) (by norm_num)
    _ ≤ 1 * (Cw * Submission.ASP.FIgtil e * Submission.ASP.FIgtil d
            * (sigmaTilde e * sigmaTilde d * ((e.divisors.card : ℕ) : ℝ)
                * (∑ ν₁ ∈ Finset.Icc 1 Δ, Submission.ASP.FIgtil ν₁ * sigmaTilde ν₁))
            * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine mul_le_mul_of_nonneg_right ?_ hlog6.le
          refine mul_le_mul_of_nonneg_left hsum ?_
          exact mul_nonneg (mul_nonneg hCw.le hge) hgd
    _ = Cw * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ))
          * (Submission.ASP.FIgtil e * sigmaTilde e * ((e.divisors.card : ℕ) : ℝ)
              * (∑ ν₁ ∈ Finset.Icc 1 Δ, Submission.ASP.FIgtil ν₁ * sigmaTilde ν₁))
          * (Submission.ASP.FIgtil d * sigmaTilde d) := by ring

/-- **The analytic core of the `λ⁺`-main half: the level sum is `≪ (log x)^{-1}`.**

For every `n ≤ x` the level sum `K(n) = Work.FIChain.s3MainLevelSum` is bounded by
`C·(log x)^{-1}`, uniformly in `n`, in the chain's windows, for every sieve input.

`hW` is the `(2.4)`-estimate `Work.FIChain.s3LevelWindow_sum_le` on the `b`-window (module
`Submission.Work.FIChain.s3LevelWindow_sum_le`); `hD` is the sharp density sum
`Work.FIChain.s3Density_sum_le` (module `Submission.Work.FIChain.s3Density_sum_le`).

A NEARLY COMPLETE DRAFT of this goal is on disk at `Submission/Work/FIChain/s3LevelScratch.lean`
(name `Work.FIChain.s3LevelSum_bound`, same statement, mathematics done, a few Lean-level goals
left: one has a dropped argument in a `s3LevelWindow` application).  Intended proof:
`|K(n)| ≤ ∫_1^{sz/Cm}(1/u)|Σ_{e,d,b} μ(b)ρ(eb)μ(d)g̃(ebd)|`; for `u ∈ (1,sz/Cm)` and
`(e,d) ∈ Icc 1 x × Icc 1 ⌊u⌋₊` the inner `b`-bound `hW` with `Work.FIChain.sigmaTilde_mul_le`
and `Σ_{ν₂|e}1 = τ(e)` gives `(1/u)|S(u)| ≤ c₀·D_d/u` where
`c₀ = Cw·(log x)^{-6}·(Σ_{e≤x}g̃(e)σ̃(e)τ(e))·(Σ_{ν₁≤Δ}g̃(ν₁)σ̃(ν₁))` and
`D_d = Σ_{d ≤ ⌊sz/Cm⌋₊}g̃(d)σ̃(d)` (monotonicity of the partial sums of the nonnegative `g̃σ̃`);
then `∫_1^{sz/Cm} c₀D_d/u = c₀D_d log(sz/Cm)` via `MeasureTheory.integral_mono_of_nonneg` with
the `Integrable` majorant `c₀D_d/u` and `integral_inv`.  Numerical inputs:
`Σ_{e≤x}g̃(e)σ̃(e)τ(e) ≤ CT(log x)²` (`Work.FIChain.FIgtil_divisor_sigma_sum_le`),
`Σ_{ν₁≤Deltac x}g̃σ̃ ≤ Cd log x` and `D_d log(sz/Cm) ≤ Cd(log x)²` (both `hD`), and
`(log max (sy/Deltac x) 2)^{-6} ≤ 100^6 (log x)^{-6}` because `Deltac x ≥ x^{1/100}` and
`(Deltac x)² ≤ ⌊Yc x B⌋₊ ≤ sy` (`Work.FIChain.scale_factsC`), so
`sy/Deltac x ≥ Deltac x ≥ x^{1/100}`.  Scale facts (from `scale_factsC`, `zc_sharp_bounds` and
the definition of `Yc`): `1 ≤ z`, `0 < Deltac x`, `Deltac x ≤ x`, `sz = sc x B * z ≤ x`,
`Cm := ⌊(zc x B)^{1-etac}⌋₊ ≤ z`, `1 ≤ sc x B * z / Cm`,
`Deltac x ^ 2 ≤ Yc x B ≤ y ≤ sc x B * y`. -/
theorem s3MainLevelSum_le
    (Cw : ℝ) (hCw : 0 < Cw)
    (hW : ∀ (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) (u : ℝ) (e d : ℕ) (lam : ℕ → ℝ) (Δ : ℕ),
      (∀ ν : ℕ, Δ < ν → lam ν = 0) → (∀ ν : ℕ, |lam ν| ≤ 1) →
      1 ≤ e → 1 ≤ d → 0 < u → 0 < z → 0 < sz → 1 < sy / (Δ : ℝ) →
      |∑ b ∈ Work.FIChain.s3LevelWindow x z sz Cm sy n u e,
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
            * Submission.ASP.FIgtil (e * b * d)|
        ≤ Cw * Submission.ASP.FIgtil e * Submission.ASP.FIgtil d
            * (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ ν₂ ∈ e.divisors,
                Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| * Work.FIChain.sigmaTilde (e * d * ν₁))
            * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ)))
    (Cd : ℝ) (hCd : 0 < Cd)
    (hD : ∀ Y : ℕ, 2 ≤ Y →
      ∑ n ∈ Finset.Icc 1 Y, Submission.ASP.FIgtil n * Work.FIChain.sigmaTilde n
        ≤ Cd * Real.log (Y : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ) →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        Work.FIChain.SieveInput Submission.ASP.FIgtil (Work.FIChain.Deltac x) lam C_sieve →
      ∀ z : ℝ, z ∈ Set.Icc (Work.FIChain.zc x B) (Real.exp 1 * Work.FIChain.zc x B) →
      ∀ y : ℝ, y ∈ Set.Icc (Work.FIChain.Yc x B) (Real.exp 1 * Work.FIChain.Yc x B) →
      ∀ n : ℕ, n ≤ x →
        |Work.FIChain.s3MainLevelSum lam x z (Work.FIChain.sc x B * z)
            (⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊) (Work.FIChain.sc x B * y) n|
          ≤ C * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by
  obtain ⟨CT, hCTpos, hCT⟩ := FIgtil_divisor_sigma_sum_le
  refine ⟨Cw * (100 : ℝ) ^ 6 * (Cd * Cd * CT) + 1, by positivity, fun B hB => ?_⟩
  obtain ⟨x1, h1⟩ := Filter.eventually_atTop.mp (scale_factsC B hB)
  obtain ⟨x2, h2⟩ := Filter.eventually_atTop.mp (Work.FITop.FI_ev_Lam1_ge_one)
  obtain ⟨x3, h3⟩ := Filter.eventually_atTop.mp (Work.FITop.FI_ev_log_ge_nat 64)
  obtain ⟨x4, h4⟩ := Filter.eventually_atTop.mp
    (Work.FITop.FI_ev_rpow_ge_nat ((1 : ℝ) / 2) (by norm_num) (4 * Real.exp 1 * Real.exp 1))
  obtain ⟨x5, h5⟩ := Filter.eventually_atTop.mp
    (Work.FITop.FI_ev_rpow_ge_nat ((1 : ℝ) / 100) (by norm_num) 2)
  refine ⟨x1 + x2 + x3 + x4 + x5 + 64, ?_⟩
  intro x hx hYc lam Cs hSi z hz y hy n hn
  have hx1 : 1 ≤ x := by omega
  have hx2 : 2 ≤ x := by omega
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le zero_lt_one hxR
  set L : ℝ := Real.log (x : ℝ) with hLdef
  have hL64 : (64 : ℝ) ≤ L := by rw [hLdef]; exact h3 x (by omega)
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := hLpos.le
  have hLam1 : 1 ≤ Work.FITop.Lam1 x := h2 x (by omega)
  have hRpow : 4 * Real.exp 1 * Real.exp 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := h4 x (by omega)
  have hX100 : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := h5 x (by omega)
  obtain ⟨hYcF256, hYcFle, hYcFleX, hlog4, hlog3_16, hDel2, hDel4, hDelLtZc, hZcLeX, hZc1,
    hDelLeZc, hDelLtSczc, hxLeSq, hDD2, hDD1, hScZc1⟩ := h1 x (by omega)
  -- the scales `zc`, `sc`, `Yc`
  have hZc1R : (1 : ℝ) ≤ (Zc x B : ℝ) := by exact_mod_cast hZc1
  have hzc1 : (1 : ℝ) ≤ zc x B := by simpa [zc] using hZc1R
  have hzcpos : 0 < zc x B := lt_of_lt_of_le zero_lt_one hzc1
  have hz1 : 1 ≤ z := le_trans hzc1 hz.1
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hsc1 : (1 : ℝ) ≤ sc x B := by rw [sc]; exact one_le_pow₀ (by norm_num)
  have hscpos : 0 < sc x B := lt_of_lt_of_le zero_lt_one hsc1
  have hYcpos : 0 < Yc x B := by
    rw [Yc]
    exact div_pos (Real.sqrt_pos.mpr hxpos) (mul_pos (pow_pos (by norm_num) _)
      (Real.rpow_pos_of_pos hLpos _))
  have hflYc : ((⌊Yc x B⌋₊ : ℕ) : ℝ) ≤ Yc x B := Nat.floor_le hYcpos.le
  -- `Δ = Deltac x`
  have hDell : (x : ℝ) ^ ((1 : ℝ) / 100) ≤ (Deltac x : ℝ) := by
    rw [Deltac, Work.FITop.Delta1, Work.FITop.Lam1]
    exact Nat.le_ceil _
  have hDel1 : 1 ≤ Deltac x := by
    have h : (1 : ℝ) ≤ (Deltac x : ℝ) := by
      rw [Deltac, Work.FITop.Delta1]
      exact le_trans hLam1 (Nat.le_ceil (Work.FITop.Lam1 x))
    exact_mod_cast h
  have hDel1R : (1 : ℝ) ≤ (Deltac x : ℝ) := by exact_mod_cast hDel1
  have hDelpos : (0 : ℝ) < (Deltac x : ℝ) := by linarith
  have hDel2R : (Deltac x : ℝ) ^ 2 ≤ ((⌊Yc x B⌋₊ : ℕ) : ℝ) := by
    have hh : ((Deltac x ^ 2 : ℕ) : ℝ) ≤ ((⌊Yc x B⌋₊ : ℕ) : ℝ) := by exact_mod_cast hDel2
    simpa using hh
  have hflYc_le_x : ((⌊Yc x B⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) := by
    have hle : ⌊Yc x B⌋₊ ≤ ⌊Real.exp 1 * Yc x B⌋₊ :=
      Nat.floor_mono (by nlinarith [hYcpos, Real.exp_one_gt_d9])
    exact_mod_cast le_trans hle hYcFleX
  have hDelx : (Deltac x : ℝ) ≤ (x : ℝ) := by
    nlinarith [hDel2R, hflYc_le_x, hDel1R, hDelpos]
  -- the level `Cm = ⌊(zc x B)^{1-η}⌋` and the window tops `sy`, `sz`
  set Cm : ℕ := ⌊(zc x B) ^ (1 - etac)⌋₊ with hCmdef
  set sy : ℝ := sc x B * y with hsydef
  set sz : ℝ := sc x B * z with hszdef
  have hCm1 : 1 ≤ Cm := by
    rw [hCmdef]
    refine Nat.le_floor ?_
    have h0 : (0 : ℝ) < 1 - etac := by norm_num [etac]
    have h1' : (1 : ℝ) ^ (1 - etac) ≤ (zc x B) ^ (1 - etac) :=
      Real.rpow_le_rpow zero_le_one hzc1 h0.le
    simpa using h1'
  have hCmR : (1 : ℝ) ≤ (Cm : ℝ) := by exact_mod_cast hCm1
  have hCmposR : (0 : ℝ) < (Cm : ℝ) := by linarith
  have hCmle : (Cm : ℝ) ≤ zc x B := by
    have h1' : (Cm : ℝ) ≤ (zc x B) ^ (1 - etac) := by
      rw [hCmdef]; exact Nat.floor_le (Real.rpow_nonneg hzcpos.le _)
    have h2' : (zc x B) ^ (1 - etac) ≤ zc x B := Real.rpow_le_self_of_one_le hzc1 (by norm_num [etac])
    linarith
  have hCmz : (Cm : ℝ) ≤ z := le_trans hCmle hz.1
  have hsz1 : 1 ≤ sz := by
    rw [hszdef]; nlinarith [hsc1, hz1, hscpos, hzpos]
  have hszpos : 0 < sz := lt_of_lt_of_le zero_lt_one hsz1
  have hsypos : 0 < sy := by
    rw [hsydef]; exact mul_pos hscpos (lt_of_lt_of_le hYcpos hy.1)
  -- `sc · Yc = √x / L^{B+2}`
  have hscYc : sc x B * Yc x B = Real.sqrt (x : ℝ) / L ^ (B + 2) := by
    rw [Yc, hLdef]
    field_simp
  have he_sqrt : Real.exp 1 ≤ Real.sqrt (x : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    nlinarith [hRpow, Real.exp_pos 1, Real.exp_one_gt_d9]
  have hLp : (1 : ℝ) ≤ L ^ (B + 2) := Real.one_le_rpow (by linarith) (by linarith [hB])
  have hszx : sz ≤ (x : ℝ) := by
    rw [hszdef]
    have h1' : sc x B * z ≤ Real.exp 1 * (sc x B * Yc x B) := by
      calc sc x B * z ≤ sc x B * (Real.exp 1 * zc x B) := mul_le_mul_of_nonneg_left hz.2 hscpos.le
        _ ≤ sc x B * (Real.exp 1 * Yc x B) := by
            refine mul_le_mul_of_nonneg_left ?_ hscpos.le
            exact mul_le_mul_of_nonneg_left hflYc (by positivity)
        _ = Real.exp 1 * (sc x B * Yc x B) := by ring
    have h2' : Real.exp 1 * (Real.sqrt (x : ℝ) / L ^ (B + 2)) ≤ (x : ℝ) := by
      have h3' : Real.sqrt (x : ℝ) / L ^ (B + 2) ≤ Real.sqrt (x : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hLp, Real.sqrt_nonneg (x : ℝ)]
      calc Real.exp 1 * (Real.sqrt (x : ℝ) / L ^ (B + 2))
          ≤ Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
            mul_le_mul he_sqrt h3' (by positivity) (Real.sqrt_nonneg _)
        _ = (x : ℝ) := Real.mul_self_sqrt hxpos.le
    rw [hscYc] at h1'
    linarith [h1', h2']
  -- `Δ² ≤ sy`, hence `sy/Δ > 1`
  have hDsy : (Deltac x : ℝ) * (Deltac x : ℝ) ≤ sy := by
    have h1' : ((⌊Yc x B⌋₊ : ℕ) : ℝ) ≤ y := le_trans hflYc hy.1
    have h2' : y ≤ sy := by
      rw [hsydef]
      exact le_mul_of_one_le_left (le_trans hYcpos.le hy.1) hsc1
    nlinarith [hDel2R, h1', h2', hDelpos]
  have hΔsy : (Deltac x : ℝ) ≤ sy / (Deltac x : ℝ) := by
    rw [le_div_iff₀ hDelpos]; nlinarith [hDsy]
  have hsyΔ : 1 < sy / (Deltac x : ℝ) := by
    have h1' : (2 : ℝ) ≤ (Deltac x : ℝ) := le_trans hX100 hDell
    linarith [hΔsy, h1']
  -- the logarithm facts and the `(2.4)`-gain
  have hlogDel : L / 100 ≤ Real.log (Deltac x : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hxpos _) hDell
    rw [Real.log_rpow hxpos] at h
    have h2' : (1 : ℝ) / 100 * Real.log (x : ℝ) = L / 100 := by rw [hLdef]; ring
    linarith [h, h2']
  have hlogmax : L / 100 ≤ Real.log (max (sy / (Deltac x : ℝ)) 2) := by
    have h2' : Real.log (Deltac x : ℝ) ≤ Real.log (max (sy / (Deltac x : ℝ)) 2) :=
      Real.log_le_log hDelpos (le_trans hΔsy (le_max_left _ _))
    linarith [hlogDel, h2']
  have hgain : (Real.log (max (sy / (Deltac x : ℝ)) 2)) ^ (-(6 : ℝ))
      ≤ (100 : ℝ) ^ 6 * L ^ (-(6 : ℝ)) := by
    have hx100 : (0 : ℝ) < L / 100 := by linarith
    have h1' := Real.rpow_le_rpow_of_nonpos hx100 hlogmax (by norm_num : (-(6 : ℝ)) ≤ 0)
    have h100 : (100 : ℝ) ^ (-(6 : ℝ)) = ((100 : ℝ) ^ 6)⁻¹ := by
      rw [show (-(6 : ℝ)) = -(((6 : ℕ) : ℝ)) by norm_num,
        Real.rpow_neg (x := (100 : ℝ)) (by norm_num : (0 : ℝ) ≤ 100), Real.rpow_natCast]
    have hL6 : L ^ (-(6 : ℝ)) = (L ^ 6)⁻¹ := by
      rw [show (-(6 : ℝ)) = -(((6 : ℕ) : ℝ)) by norm_num,
        Real.rpow_neg (x := L) hLnn, Real.rpow_natCast]
    have h2' : (L / 100) ^ (-(6 : ℝ)) = (100 : ℝ) ^ 6 * L ^ (-(6 : ℝ)) := by
      rw [Real.div_rpow hLnn (by norm_num : (0 : ℝ) ≤ 100), h100, hL6]
      field_simp
    linarith [h1', h2']
  -- the four numerical quantities
  set g0 : ℝ := (Real.log (max (sy / (Deltac x : ℝ)) 2)) ^ (-(6 : ℝ)) with hg0def
  set E : ℝ := ∑ e ∈ Finset.Icc 1 x, Submission.ASP.FIgtil e * sigmaTilde e
      * ((e.divisors.card : ℕ) : ℝ) with hEdef
  set A0 : ℝ := ∑ ν₁ ∈ Finset.Icc 1 (Deltac x), Submission.ASP.FIgtil ν₁ * sigmaTilde ν₁ with hA0def
  set Dd : ℝ := ∑ d ∈ Finset.Icc 1 ⌊sz / (Cm : ℝ)⌋₊, Submission.ASP.FIgtil d * sigmaTilde d with hDddef
  have hg0pos : 0 < g0 := by
    rw [hg0def]
    refine Real.rpow_pos_of_pos ?_ _
    exact Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
  have hg0nn : 0 ≤ g0 := hg0pos.le
  have hEnn : 0 ≤ E := by
    rw [hEdef]
    exact Finset.sum_nonneg (fun e _ => mul_nonneg (mul_nonneg (Submission.ASP.FIgtil_nonneg e)
      (le_trans zero_le_one (one_le_sigmaTilde e))) (by positivity))
  have hA0nn : 0 ≤ A0 := by
    rw [hA0def]
    exact Finset.sum_nonneg (fun ν _ => mul_nonneg (Submission.ASP.FIgtil_nonneg ν)
      (le_trans zero_le_one (one_le_sigmaTilde ν)))
  have hDdnn : 0 ≤ Dd := by
    rw [hDddef]
    exact Finset.sum_nonneg (fun d _ => mul_nonneg (Submission.ASP.FIgtil_nonneg d)
      (le_trans zero_le_one (one_le_sigmaTilde d)))
  have hE' : E ≤ CT * L ^ (2 : ℕ) := by
    have h := hCT x hx2
    have h2' : (∑ ν ∈ Finset.Icc 1 x, ((ν.divisors.card : ℕ) : ℝ) * Submission.ASP.FIgtil ν
        * sigmaTilde ν) = E := by
      rw [hEdef]
      exact Finset.sum_congr rfl (fun e _ => by ring)
    rw [h2', ← hLdef] at h
    exact h
  have hA0' : A0 ≤ Cd * L := by
    have hmax : 2 ≤ max (Deltac x) 2 := le_max_right _ _
    have h := hD (max (Deltac x) 2) hmax
    have hsub : A0 ≤ ∑ ν ∈ Finset.Icc 1 (max (Deltac x) 2),
        Submission.ASP.FIgtil ν * sigmaTilde ν := by
      rw [hA0def]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro ν hν
        rw [Finset.mem_Icc] at hν ⊢
        exact ⟨hν.1, le_trans hν.2 (le_max_left _ _)⟩
      · intro i _ _
        exact mul_nonneg (Submission.ASP.FIgtil_nonneg i) (le_trans zero_le_one (one_le_sigmaTilde i))
    have hlog : Real.log (((max (Deltac x) 2 : ℕ)) : ℝ) ≤ L := by
      rw [hLdef]
      refine Real.log_le_log (by positivity) ?_
      rw [Nat.cast_max]
      exact max_le hDelx (by exact_mod_cast hx2)
    exact le_trans hsub (le_trans h (mul_le_mul_of_nonneg_left hlog hCd.le))
  have hflU : ((⌊sz / (Cm : ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) := by
    have ha : (0 : ℝ) ≤ sz / (Cm : ℝ) := div_nonneg hszpos.le hCmposR.le
    have h1' := Nat.floor_le ha
    have h2' : sz / (Cm : ℝ) ≤ sz := by rw [div_le_iff₀ hCmposR]; nlinarith [hsz1]
    linarith [h1', h2', hszx]
  have hDd' : Dd ≤ Cd * L := by
    have hmax : 2 ≤ max ⌊sz / (Cm : ℝ)⌋₊ 2 := le_max_right _ _
    have h := hD (max ⌊sz / (Cm : ℝ)⌋₊ 2) hmax
    have hsub : Dd ≤ ∑ d ∈ Finset.Icc 1 (max ⌊sz / (Cm : ℝ)⌋₊ 2),
        Submission.ASP.FIgtil d * sigmaTilde d := by
      rw [hDddef]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro d hd
        rw [Finset.mem_Icc] at hd ⊢
        exact ⟨hd.1, le_trans hd.2 (le_max_left _ _)⟩
      · intro i _ _
        exact mul_nonneg (Submission.ASP.FIgtil_nonneg i) (le_trans zero_le_one (one_le_sigmaTilde i))
    have hlog : Real.log (((max ⌊sz / (Cm : ℝ)⌋₊ 2 : ℕ)) : ℝ) ≤ L := by
      rw [hLdef]
      refine Real.log_le_log (by positivity) ?_
      rw [Nat.cast_max]
      exact max_le hflU (by exact_mod_cast hx2)
    exact le_trans hsub (le_trans h (mul_le_mul_of_nonneg_left hlog hCd.le))
  set c0 : ℝ := Cw * g0 * E * A0 with hc0def
  have hc0nn : 0 ≤ c0 := by
    rw [hc0def]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCw.le hg0nn) hEnn) hA0nn
  have hU1 : (1 : ℝ) ≤ sz / (Cm : ℝ) := by
    rw [le_div_iff₀ hCmposR, one_mul]
    have hzsz : z ≤ sz := by rw [hszdef]; exact le_mul_of_one_le_left hzpos.le hsc1
    linarith [hCmz, hzsz]
  have hUpos : (0 : ℝ) < sz / (Cm : ℝ) := lt_of_lt_of_le zero_lt_one hU1
  -- Step 1: `|K(n)| ≤ ∫ (1/u)·|S(u)|`
  have hstep1 : |s3MainLevelSum lam x z sz Cm sy n|
      ≤ ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)),
          (1 / u) * |(∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
              ∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
                (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
                  * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d))| := by
    rw [s3MainLevelSum]
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hU1) ?_
    refine le_of_eq (intervalIntegral.integral_congr (fun u hu => ?_))
    have hu1 : (1 : ℝ) ≤ u := by
      rw [Set.uIcc_of_le hU1] at hu
      exact hu.1
    have hu0 : 0 < u := by linarith
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / u)]
  -- Step 2: the pointwise bound `|S(u)| ≤ c0 · Dd`
  have hinner : ∀ u ∈ Set.Ioc (1 : ℝ) (sz / (Cm : ℝ)), ∀ e ∈ Finset.Icc 1 x,
      ∀ d ∈ Finset.Icc 1 ⌊u⌋₊,
      |∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
            * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d)|
        ≤ (Cw * g0 * (Submission.ASP.FIgtil e * sigmaTilde e
              * ((e.divisors.card : ℕ) : ℝ) * A0))
          * (Submission.ASP.FIgtil d * sigmaTilde d) := by
    intro u hu e he d hd
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hu0 : 0 < u := by linarith [hu.1]
    exact levelWindow_inner_le Cw hCw hW x z sz Cm sy n u e d lam (Deltac x)
      hSi.2.1 hSi.2.2.2.1 he1 hd1 hu0 hzpos hszpos hsyΔ
  have hSbound : ∀ u ∈ Set.Ioc (1 : ℝ) (sz / (Cm : ℝ)),
      |(∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
              ∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
                (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
                  * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d))|
        ≤ c0 * Dd := by
    intro u hu
    have hdmono : (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, Submission.ASP.FIgtil d * sigmaTilde d) ≤ Dd := by
      rw [hDddef]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro d hd
        rw [Finset.mem_Icc] at hd ⊢
        exact ⟨hd.1, le_trans hd.2 (Nat.floor_mono hu.2)⟩
      · intro i _ _
        exact mul_nonneg (Submission.ASP.FIgtil_nonneg i) (le_trans zero_le_one (one_le_sigmaTilde i))
    have hcgEA : 0 ≤ Cw * g0 * A0 * E :=
      mul_nonneg (mul_nonneg (mul_nonneg hCw.le hg0nn) hA0nn) hEnn
    calc |(∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
              ∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
                (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
                  * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d))|
        ≤ ∑ e ∈ Finset.Icc 1 x, |∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
              ∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
                (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
                  * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
              |∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
                (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
                  * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d)| :=
            Finset.sum_le_sum (fun e _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
              (Cw * g0 * (Submission.ASP.FIgtil e * sigmaTilde e
                    * ((e.divisors.card : ℕ) : ℝ) * A0))
                * (Submission.ASP.FIgtil d * sigmaTilde d) :=
            Finset.sum_le_sum (fun e he => Finset.sum_le_sum (fun d hd => hinner u hu e he d hd))
      _ = (Cw * g0 * A0 * E)
              * (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, Submission.ASP.FIgtil d * sigmaTilde d) := by
            rw [← Finset.sum_mul_sum]
            congr 1
            rw [hEdef, Finset.mul_sum]
            exact Finset.sum_congr rfl (fun e _ => by ring)
      _ ≤ (Cw * g0 * A0 * E) * Dd := mul_le_mul_of_nonneg_left hdmono hcgEA
      _ = c0 * Dd := by rw [hc0def]; ring
  -- Step 3: the integral of the majorant
  have hstep3a : (∫ u in (1 : ℝ)..(sz / (Cm : ℝ)),
          (1 / u) * |(∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
              ∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
                (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
                  * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d))|)
      ≤ ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)), c0 * Dd / u := by
    rw [intervalIntegral.integral_of_le hU1, intervalIntegral.integral_of_le hU1]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · exact eventually_restrict_Ioc (fun u hu => by
        have hu0 : 0 < u := by linarith [hu.1]
        exact mul_nonneg (by positivity) (abs_nonneg _))
    · exact integrable_const_div_Ioc (c0 * Dd) 1 (sz / (Cm : ℝ)) (by norm_num)
    · exact eventually_restrict_Ioc (fun u hu => by
        have hu0 : 0 < u := by linarith [hu.1]
        calc (1 / u) * |(∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
                ∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
                  (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
                    * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d))|
            ≤ (1 / u) * (c0 * Dd) := mul_le_mul_of_nonneg_left (hSbound u hu) (by positivity)
          _ = c0 * Dd / u := by ring)
  have hstep3b : (∫ u in (1 : ℝ)..(sz / (Cm : ℝ)), c0 * Dd / u)
      = c0 * Dd * Real.log (sz / (Cm : ℝ)) := by
    rw [show (fun u : ℝ => c0 * Dd / u) = fun u => (c0 * Dd) * (1 / u) by
      funext u; ring]
    rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos (by norm_num) hUpos, div_one]
  have hstep3c : c0 * Dd * Real.log (sz / (Cm : ℝ)) ≤ c0 * Dd * L := by
    have hlogUle : Real.log (sz / (Cm : ℝ)) ≤ L := by
      rw [hLdef]
      refine Real.log_le_log (by positivity) ?_
      have hdiv : sz / (Cm : ℝ) ≤ sz := by rw [div_le_iff₀ hCmposR]; nlinarith [hsz1]
      linarith [hdiv, hszx]
    exact mul_le_mul_of_nonneg_left hlogUle (mul_nonneg hc0nn hDdnn)
  have hstep3 : (∫ u in (1 : ℝ)..(sz / (Cm : ℝ)),
          (1 / u) * |(∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
              ∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
                (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
                  * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d))|)
      ≤ c0 * Dd * L :=
    le_trans hstep3a (le_trans (le_of_eq hstep3b) hstep3c)
  -- Step 4: the numerical assembly
  have hgE : g0 * E ≤ ((100 : ℝ) ^ 6 * L ^ (-(6 : ℝ))) * (CT * L ^ (2 : ℕ)) :=
    mul_le_mul hgain hE' hEnn (by positivity)
  have hgEA : g0 * E * A0
      ≤ (((100 : ℝ) ^ 6 * L ^ (-(6 : ℝ))) * (CT * L ^ (2 : ℕ))) * (Cd * L) :=
    mul_le_mul hgE hA0' hA0nn (by positivity)
  have hgEAd : g0 * E * A0 * Dd
      ≤ ((((100 : ℝ) ^ 6 * L ^ (-(6 : ℝ))) * (CT * L ^ (2 : ℕ))) * (Cd * L)) * (Cd * L) :=
    mul_le_mul hgEA hDd' hDdnn (by positivity)
  have hgEAdL : g0 * E * A0 * Dd * L
      ≤ (((((100 : ℝ) ^ 6 * L ^ (-(6 : ℝ))) * (CT * L ^ (2 : ℕ))) * (Cd * L)) * (Cd * L)) * L :=
    mul_le_mul hgEAd le_rfl hLnn (by positivity)
  have hpow : L ^ (-(6 : ℝ)) * L ^ (2 : ℕ) * L * L * L = L ^ (-(1 : ℝ)) := by
    rw [show (-(6 : ℝ)) = -((6 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg hLnn, Real.rpow_natCast,
        show (-(1 : ℝ)) = -((1 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg hLnn, Real.rpow_natCast, pow_one]
    field_simp
  have hlogconv : L ^ (-(1 : ℤ)) = L ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_intCast L (-1)]; norm_num
  have hfinal : c0 * Dd * L ≤ Cw * (100 : ℝ) ^ 6 * (Cd * Cd * CT) * L ^ (-(1 : ℤ)) := by
    rw [hlogconv]
    have hcgEAdL := mul_le_mul_of_nonneg_left hgEAdL hCw.le
    calc c0 * Dd * L = Cw * (g0 * E * A0 * Dd * L) := by rw [hc0def]; ring
      _ ≤ Cw * ((((((100 : ℝ) ^ 6 * L ^ (-(6 : ℝ))) * (CT * L ^ (2 : ℕ))) * (Cd * L))
            * (Cd * L)) * L) := hcgEAdL
      _ = Cw * (100 : ℝ) ^ 6 * (Cd * Cd * CT) * L ^ (-(1 : ℝ)) := by
            rw [← hpow]; ring
  have hmain2 : |s3MainLevelSum lam x z sz Cm sy n| ≤ c0 * Dd * L :=
    le_trans hstep1 (le_trans hstep3 (le_refl _))
  refine le_trans hmain2 ?_
  refine le_trans hfinal ?_
  refine mul_le_mul_of_nonneg_right (by linarith) ?_
  exact zpow_nonneg hLnn _

end

end Work.FIChain
