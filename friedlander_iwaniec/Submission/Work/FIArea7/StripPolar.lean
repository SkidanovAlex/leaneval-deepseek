/-
# `Submission.Work.FIArea6.PolarCoeff` — the structural coefficient class of §§5–10

This file isolates the **structural content** of the round-6 coefficient predicate
`Work.FITop4.IsBetaCoeff6` that the elementary estimates of §§5–10 actually consume:

* the support lies in the polar box (5.14) of `Pa`, is free of primes `≤ Pa.Pz` (5.8) and has
  `τ(|z|²) ≤ Pa.τ` (5.9);
* `|z|²` is squarefree on the support (the Möbius factor of (5.13));
* the pointwise size bound `‖β z‖ ≤ τ(|z|²)`.

The mollifier clauses (`ContDiff`, derivative bounds) — which round 3 was missing and which are
*only* used by the analytic part of §16 (`FIArea5`) — play no role in any estimate of this
directory, so all the elementary bounds below are stated for the weaker class `StripPolar`.

`IsBetaCoeff6.toStripPolar` shows the round-6 predicate is a special case.

## How to reuse the round-3/round-4 proofs

Every lemma of `Submission.Work.FIArea6.*` (`beta_sq_mass_tight`, `beta_sq_mass_nonfat`,
`fiber_card_le`, `row_le`, `pair_phi_average`, ...) that takes
`hβ : Work.FITop3.IsBetaCoeff Pa φ β` uses `hβ` **only** through the structural facts, via the
five helper lemmas

* `Work.FIArea6.beta_support hβ hz`            ↔ `(h.1 z hz)`
* `Work.FIArea6.beta_support_norm hβ hz`       ↔ `h.norm_bounds hz`
* `Work.FIArea6.beta_norm_le_divisors hβ z`    ↔ `h.2 z`
* `Work.FIArea6.tau_le_two_pow hβ hz`          ↔ `h.tau_le_two_pow hz`
* `Work.FIArea6.card_support_le Pa φ β hβ`     ↔ `h.card_support_le Pa φ β`
* `Work.FIArea6.squarefree_of_beta_ne_zero hβ hz` ↔ `h.squarefree hz`

so each such theorem transfers verbatim to `StripPolar` by that textual substitution (the
mollifier clauses `ContDiff`/derivative bounds are never touched).
-/
import Mathlib
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea6.card_polarBox_dvd_le

/-!
# `Submission.Work.FIArea7.StripPolar` — the structural polar class, self-contained

This is a verbatim copy of `Submission.Work.FIArea6.PolarCoeff` (the structural coefficient class
`IsPolarCoeff` consumed by the mass bound `Work.FIArea6.vsq_polar`) with the single declaration
`IsPolarCoeff` renamed to `StripPolar`.  The renaming makes the module independent of the
`Work.FIArea6.PolarCoeff` module, which at the time of writing did not compile (the round-6.1
insertion of `IsAxisFree` into `Work.FITop4.IsBetaCoeff6` invalidated its `toIsPolarCoeff`); the
`∧ IsAxisFree Pa z` conjunct has been added below so that `IsBetaCoeff6.toStripPolar` compiles
against the current `IsBetaCoeff6`.  Nothing else is changed.
-/


set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The structural coefficient class.**  `StripPolar Pa φ β` records everything about
(4.13)+(5.13) that the elementary estimates of §§5–10 use: support in the polar box (5.14) with
(5.8)/(5.9), squarefreeness of `|z|²` (from the Möbius factor), and the pointwise bound
`‖β z‖ ≤ τ(|z|²)`. -/
def StripPolar (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ) : Prop :=
  (∀ z, β z ≠ 0 →
      Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
        (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧
        Squarefree (Work.FIPlan.gnorm z)) ∧
  (∀ z, ‖β z‖ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))

/-- The polar-box membership of a point of the support. -/
lemma StripPolar.inPolarBox {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : StripPolar Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Work.FITop3.InPolarBox Pa φ z := (h.1 z hz).1

/-- A point of the support is free of small primes (5.8). -/
lemma StripPolar.noSmallPrimes {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : StripPolar Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Work.FITop3.NoSmallPrimes Pa z := (h.1 z hz).2.1

/-- `τ(|z|²) ≤ Pa.τ` on the support (5.9). -/
lemma StripPolar.tau_le {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : StripPolar Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) := (h.1 z hz).2.2.1

/-- `|z|²` is squarefree on the support. -/
lemma StripPolar.squarefree {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : StripPolar Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Squarefree (Work.FIPlan.gnorm z) := (h.1 z hz).2.2.2

/-- The annulus confinement `N < |z|² ≤ (1+θ)N` on the support. -/
lemma StripPolar.norm_bounds {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : StripPolar Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Pa.N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) ∧
      ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := by
  have hp := h.inPolarBox hz
  exact ⟨hp.2.1, hp.2.2.1⟩

/-- **Round-6 coefficients are structural.**  The explicit formula of (4.13)+(5.13) gives all the
facts of `StripPolar`. -/
theorem IsBetaCoeff6.toStripPolar {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    StripPolar Pa φ β := by
  obtain ⟨q, p, -, -, hq0, hq1, -, -, hp0, hp1, -, -, hform⟩ := h
  constructor
  · intro z hz
    rw [hform z] at hz
    by_cases hc : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
        (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0
        ∧ Work.FITop4.IsAxisFree Pa z
    · rw [if_pos hc] at hz
      have hmu : (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ) ≠ 0 :=
        (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1).2
      have hmuZ : ArithmeticFunction.moebius (Work.FIPlan.gnorm z) ≠ 0 := by
        intro h0
        exact hmu (by rw [h0]; norm_num)
      exact ⟨hc.1, hc.2.1, hc.2.2.1,
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuZ⟩
    · rw [if_neg hc] at hz
      exact absurd rfl hz
  · intro z
    rw [hform z]
    split_ifs with hz
    · have hqp : ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 _) (hp0 _))]
        have h2 : q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) ≤ 1 * 1 :=
          mul_le_mul (hq1 _) (hp1 _) (hp0 _) (by norm_num)
        linarith
      have hμ : ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖ ≤ 1 :=
        Work.FITop3.norm_moebius_le_one _
      have hγ : ‖((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
          ≤ ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact Work.FITop3.abs_gammaTrunc_le _ _
      calc ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * ((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
          = ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)‖
              * ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖
              * ‖((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ 1 * 1 * ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by gcongr
        _ = ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by ring
    · simp

/-- **The `NoSmallPrimes` `τ`-bound.**  On the support, every prime factor of `|z|²` exceeds
`Pa.Pz`, so `Pa.Pz^{Ω(n)} ≤ n` and `τ(n) ≤ 2^{Ω(n)}`. -/
lemma StripPolar.tau_le_two_pow {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : StripPolar Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
      ≤ 2 ^ (Real.log (((Work.FIPlan.gnorm z) : ℕ) : ℝ) / Real.log (Pa.Pz : ℝ)) := by
  have hnsp : Work.FITop3.NoSmallPrimes Pa z := (hβ.1 z hz).2.1
  set n : ℕ := Work.FIPlan.gnorm z with hn
  have hn0 : n ≠ 0 := by
    intro h0
    have h2 : Pa.N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) := (hβ.1 z hz).1.2.1
    rw [← hn, h0] at h2
    simp at h2
    linarith [Pa.hN1]
  have hτ : n.divisors.card ≤ 2 ^ (∑ p ∈ n.primeFactors, n.factorization p) := by
    rw [Nat.card_divisors hn0, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p hp => ?_)
    have hp1 : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpdvd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
    have h1 : 1 ≤ n.factorization p := by
      have hne : n.factorization p ≠ 0 := by
        intro h0
        rw [Nat.factorization_eq_zero_iff] at h0
        tauto
      omega
    calc n.factorization p + 1 ≤ 2 ^ n.factorization p := by
          have := (Nat.lt_two_pow_self : n.factorization p < 2 ^ n.factorization p)
          omega
      _ = (2:ℕ) ^ n.factorization p := rfl
  have hle : (Pa.Pz : ℕ) ^ (∑ p ∈ n.primeFactors, n.factorization p) ≤ n := by
    rw [← Finset.prod_pow_eq_pow_sum (s := n.primeFactors) (f := n.factorization) (a := Pa.Pz)]
    have h1 : ∏ p ∈ n.primeFactors, Pa.Pz ^ n.factorization p
        ≤ ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      refine Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p hp => ?_)
      have hp1 : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hpdvd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
      have hnot : ¬ (p ≤ Pa.Pz) := fun hle' => hnsp p hp1 hle' (by rw [← hn]; exact hpdvd)
      have hpl : Pa.Pz ≤ p := by omega
      exact Nat.pow_le_pow_left hpl _
    have h2 : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
      Nat.prod_factorization_pow_eq_self hn0
    rw [h2] at h1
    exact h1
  set S : ℕ := ∑ p ∈ n.primeFactors, n.factorization p with hS
  have hPz0 : 0 < ((Pa.Pz : ℕ) : ℝ) := by
    have h : 0 < Pa.Pz := by have := Pa.hP2; omega
    exact_mod_cast h
  have hlog : (S : ℝ) * Real.log (Pa.Pz : ℝ) ≤ Real.log (n : ℝ) := by
    have h1 : (((Pa.Pz : ℕ) : ℝ)) ^ S ≤ (n : ℝ) := by exact_mod_cast hle
    have h1' : Real.log (((Pa.Pz : ℕ) : ℝ) ^ S) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (pow_pos hPz0 S) h1
    rwa [Real.log_pow] at h1'
  have hPz1 : (1 : ℝ) < (Pa.Pz : ℝ) := by
    have h : (1:ℕ) < Pa.Pz := by have := Pa.hP2; omega
    exact_mod_cast h
  have hlogPz : 0 < Real.log (Pa.Pz : ℝ) := Real.log_pos hPz1
  have hSle : (S : ℝ) ≤ Real.log (n : ℝ) / Real.log (Pa.Pz : ℝ) := by
    rw [le_div_iff₀ hlogPz]
    linarith [hlog]
  calc ((n.divisors.card : ℕ) : ℝ) ≤ ((2 : ℕ) ^ S : ℝ) := by exact_mod_cast hτ
    _ = (2 : ℝ) ^ (S : ℝ) := by
        push_cast
        rw [Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ (Real.log (n : ℝ) / Real.log (Pa.Pz : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hSle

/-- **The support count.**  At most `200(θ²N + θ√N + 1)` lattice points lie in the polar box. -/
lemma StripPolar.card_support_le (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : StripPolar Pa φ β) :
    (((Work.FITop.boxN Pa).filter (fun z => β z ≠ 0)).card : ℝ)
      ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) := by
  have hsub : (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0)
      ⊆ (Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, (hβ.1 z hz.2).1⟩
  have h1 : (((Work.FITop.boxN Pa).filter (fun z => β z ≠ 0)).card : ℝ)
      ≤ ((Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z)).card := by
    exact_mod_cast Finset.card_le_card hsub
  set A : Finset GaussianInt :=
    (Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z) with hA
  set c : ℂ := (Real.sqrt Pa.N : ℂ)
    * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I) with hc
  set ρ : ℝ := 5 * Pa.θ * Real.sqrt Pa.N with hρ
  have hρ0 : 0 ≤ ρ := by
    rw [hρ]
    exact mul_nonneg (mul_nonneg (by norm_num) Pa.hθ0.le) (Real.sqrt_nonneg _)
  have hdist : ∀ z ∈ A, ‖z.toComplex - c‖ ≤ ρ := by
    intro z hz
    have hbox : Work.FITop3.InPolarBox Pa φ z := by
      rw [hA] at hz
      exact (Finset.mem_filter.mp hz).2
    rw [hc, hρ]
    exact Work.FIArea4.dist_polarBox_le Pa φ z hbox
  have hcard := Work.FIArea4.card_le_of_dist_le A c hρ0 hdist
  have hs0 : 0 ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  have hts : 0 ≤ Pa.θ * Real.sqrt Pa.N := mul_nonneg Pa.hθ0.le hs0
  have hsq : (Real.sqrt Pa.N) ^ 2 = Pa.N := Real.sq_sqrt (by linarith [Pa.hN1])
  have hexpand : (2 * ρ + 1) ^ 2
      ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) := by
    rw [hρ]
    nlinarith [sq_nonneg Pa.θ, hs0, hsq, Pa.hθ0.le, hts]
  exact le_trans h1 (le_trans hcard hexpand)

end

end Work.FIArea6
