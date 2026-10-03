/-
# `Submission.Work.FIArea6Hecke.R.AxisLogDefs`

Vocabulary for the **real-axis logarithmic derivative bound** for the principal Hecke
`L`-function `L(s, 1) = Σ_n λ_d(n) n^{-s}` (`λ_d(n) = Σ_{z primary, |z|²=n} χ(z)`,
`χ = principalStrict d`), i.e. for

  `-Re(L'/L)(σ) ≤ 1/(σ-1) + C₁`  for `1 < σ ≤ 2`, uniformly in `d ≥ 1`.

The decomposition proved downstream is the classical one

  `L(s,1) = ζ(s)·L(s,χ₄)·G_d(s)`,   `G_d(s) = ∏_{p | 4d} (1 - p^{-s})(1 - χ₄(p)p^{-s})`,

with `χ₄` the quadratic character of `ℚ(i)` modulo `4` (so that `ζ(·)·L(·,χ₄) = ζ_{ℚ(i)}(·)` is the
Dedekind zeta function of `ℚ(i)`), and where the logarithmic derivative of the correction `G_d`
is `≤ 0` on the real axis.  This file fixes the two objects `axisChi4`, `axisBadCorr`/`axisBadPoly`
together with their elementary (proved) API; the analytic facts about them are delegated.
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 1. The quadratic character `χ₄` modulo `4` -/

/-- The quadratic Dirichlet character `χ₄` modulo `4` (the character of `ℚ(i)/ℚ`), as a
`ℂ`-valued function on `ℕ`: `χ₄ n = 1` for `n ≡ 1 (4)`, `χ₄ n = -1` for `n ≡ 3 (4)`, and
`χ₄ n = 0` for even `n`. -/
def axisChi4 (n : ℕ) : ℂ := ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℂ)

@[simp] lemma axisChi4_zero : axisChi4 0 = 0 := by simp [axisChi4]

@[simp] lemma axisChi4_one : axisChi4 1 = 1 := by simp [axisChi4]

/-- Explicit values of `χ₄`. -/
lemma axisChi4_eq_if (n : ℕ) :
    axisChi4 n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  rw [axisChi4, ZMod.χ₄_nat_eq_if_mod_four]
  push_cast
  by_cases h : n % 2 = 0 <;> simp [h]

lemma axisChi4_eq_one_of_mod_four {n : ℕ} (h : n % 4 = 1) : axisChi4 n = 1 := by
  rw [axisChi4_eq_if]
  rw [if_neg (by omega), if_pos h]

lemma axisChi4_eq_zero_of_even {n : ℕ} (h : 2 ∣ n) : axisChi4 n = 0 := by
  rw [axisChi4_eq_if]
  rw [if_pos (Nat.dvd_iff_mod_eq_zero.mp h)]

/-- `χ₄` is completely multiplicative. -/
lemma axisChi4_mul (m n : ℕ) : axisChi4 (m * n) = axisChi4 m * axisChi4 n := by
  simp only [axisChi4, Nat.cast_mul]
  rw [map_mul]
  push_cast
  ring

/-- `‖χ₄ n‖ ≤ 1`. -/
lemma axisChi4_norm_le_one (n : ℕ) : ‖axisChi4 n‖ ≤ 1 := by
  rw [axisChi4_eq_if]
  split_ifs <;> simp

/-- The value of `χ₄` at a rational prime. -/
lemma axisChi4_prime {p : ℕ} (hp : p.Prime) :
    axisChi4 p = if p = 2 then 0 else if p % 4 = 1 then 1 else -1 := by
  rw [axisChi4_eq_if]
  rcases hp.eq_two_or_odd' with h2 | hodd
  · subst h2; simp
  · obtain ⟨k, hk⟩ := hodd
    have hp2 : p ≠ 2 := by omega
    rw [if_neg hp2, if_neg (by omega : ¬ p % 2 = 0)]

/-! ## 2. The bad-prime correction `∏_{p | 4d} (1 - p^{-s})(1 - χ₄(p)p^{-s})` -/

/-- The correction factor at the prime `p`: `(1-p^{-s})(1-χ₄(p)p^{-s})` when `p ∣ 4d`, and `1`
otherwise. -/
def axisBadCorr (d : ℕ) (p : ℕ) (s : ℂ) : ℂ :=
  if p ∈ (4 * d).primeFactors then (1 - (p : ℂ) ^ (-s)) * (1 - axisChi4 p * (p : ℂ) ^ (-s))
  else 1

/-- The finite Euler-factor correction `G_d(s) = ∏_{p ∣ 4d}(1-p^{-s})(1-χ₄(p)p^{-s})`. -/
def axisBadPoly (d : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ (4 * d).primeFactors, (1 - (p : ℂ) ^ (-s)) * (1 - axisChi4 p * (p : ℂ) ^ (-s))

lemma axisBadPoly_eq_prod_corr (d : ℕ) (s : ℂ) :
    axisBadPoly d s = ∏ p ∈ (4 * d).primeFactors, axisBadCorr d p s := by
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [axisBadCorr, if_pos hp]

lemma axisBadCorr_eq_one {d : ℕ} {p : ℕ} {s : ℂ} (hp : p ∉ (4 * d).primeFactors) :
    axisBadCorr d p s = 1 := by rw [axisBadCorr, if_neg hp]

/-- `G_d` as an infinite product over the rational primes (the family is `1` off the finitely many
bad primes). -/
lemma tprod_axisBadCorr (d : ℕ) (s : ℂ) :
    (∏' p : Nat.Primes, axisBadCorr d (p : ℕ) s) = axisBadPoly d s := by
  classical
  let e : {p // p ∈ (4*d).primeFactors} ↪ Nat.Primes :=
    ⟨fun p => ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩,
     fun a b h => Subtype.ext (congrArg (fun x : Nat.Primes => (x : ℕ)) h)⟩
  have hmul : Function.mulSupport (fun p : Nat.Primes => axisBadCorr d (p : ℕ) s)
      ⊆ ((4*d).primeFactors).attach.map e := by
    intro p hp
    rw [Function.mem_mulSupport] at hp
    have hp' : (p : ℕ) ∈ (4*d).primeFactors := by
      by_contra hcon
      exact hp (axisBadCorr_eq_one hcon)
    exact Finset.mem_map.mpr ⟨⟨(p : ℕ), hp'⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
  rw [tprod_eq_prod' (f := fun p : Nat.Primes => axisBadCorr d (p : ℕ) s)
    (s := ((4*d).primeFactors).attach.map e) hmul]
  rw [Finset.prod_map]
  have hstep : (∏ x ∈ (4*d).primeFactors.attach, axisBadCorr d ((e x : Nat.Primes) : ℕ) s)
      = ∏ x ∈ (4*d).primeFactors, axisBadCorr d x s := by
    rw [← Finset.prod_attach (s := (4*d).primeFactors) (f := fun q : ℕ => axisBadCorr d q s)]
    exact Finset.prod_congr rfl fun x _ => rfl
  rw [hstep, axisBadPoly]
  exact Finset.prod_congr rfl fun p hp => by rw [axisBadCorr, if_pos hp]

/-- `p^{-s} ≠ 1` for `1 < re s` and a prime `p`. -/
lemma natCast_cpow_neg_ne_one {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : 1 < s.re) :
    (p : ℂ) ^ (-s) ≠ 1 := by
  intro h
  have h1 : ‖(p : ℂ) ^ (-s)‖ = 1 := by rw [h]; simp
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re] at h1
  have h2 : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) (by linarith)
  linarith

/-- `G_d(s) ≠ 0` for `1 < re s`. -/
lemma axisBadPoly_ne_zero (d : ℕ) {s : ℂ} (hs : 1 < s.re) : axisBadPoly d s ≠ 0 := by
  rw [axisBadPoly_eq_prod_corr]
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  rw [axisBadCorr, if_pos hp]
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp1 : 1 < p := hpp.one_lt
  refine mul_ne_zero (sub_ne_zero.mpr (natCast_cpow_neg_ne_one hp1 hs).symm) ?_
  intro h
  have h1 : axisChi4 p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖axisChi4 p * (p : ℂ) ^ (-s)‖ = 1 := by rw [h1]; simp
  have hle : ‖axisChi4 p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s.re) := by
    rw [norm_mul]
    calc ‖axisChi4 p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (axisChi4_norm_le_one p) (norm_nonneg _)
      _ = ‖(p : ℂ) ^ (-s)‖ := one_mul _
      _ = (p : ℝ) ^ (-s.re) := by
          rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have hlt : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp1) (by linarith)
  linarith

/-! ## 3. Differentiability of `G_d` -/

lemma differentiableAt_cpow_neg_of_ne_zero (c : ℂ) (hc : c ≠ 0) (s : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => c ^ (-z)) s :=
  (differentiableAt_id.neg).const_cpow (Or.inl hc)

lemma differentiableAt_axisBadPoly (d : ℕ) (s : ℂ) : DifferentiableAt ℂ (axisBadPoly d) s := by
  have hprod : DifferentiableAt ℂ
      (∏ p ∈ (4 * d).primeFactors,
        fun s : ℂ => (1 - (p : ℂ) ^ (-s)) * (1 - axisChi4 p * (p : ℂ) ^ (-s))) s := by
    refine DifferentiableAt.finsetProd (𝕜 := ℂ) (𝔸' := ℂ) (fun p hp => ?_)
    have hp0 : (p : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    have h := differentiableAt_cpow_neg_of_ne_zero (p : ℂ) hp0 s
    exact ((differentiableAt_const (1 : ℂ)).sub h).mul
      ((differentiableAt_const (1 : ℂ)).sub ((differentiableAt_const (axisChi4 p)).mul h))
  refine hprod.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  ext s
  simp only [axisBadPoly]
  rw [Finset.prod_apply]

end

end Work.FIArea6Hecke.R
