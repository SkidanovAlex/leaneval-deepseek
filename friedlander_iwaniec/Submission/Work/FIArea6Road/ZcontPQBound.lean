/-
# `Submission.Work.FIArea6Road.ZcontPQBound` (re-homed from `PQLocalBound`)

The local (half-plane) bound for the two Euler-product factors `P(s)` (16.33) and `Q(s)` (16.34)
of the Möbius-twisted Hecke series `Z(s)` (16.30) of *FI* §16:

* `P(s) = ∏_{p ≤ Pz} (1 - λ(p)p^{-s})^{-1}` is bounded on the half-plane
  `re s ≥ 1 - 1/log Pz`;
* `Q(s) = Σ_{c ≤ C, (c,Π)=1} λ(c)c^{-s}∏_{p|c}(1 - λ(p)p^{-s})^{-1}` satisfies
  `‖Q(s)‖ ≤ K·C^{1-re s}` there (for `re s ≤ 2`).

Both are proved from the single structural input that the Hecke eigenvalue at a *prime* is
`≤ 2` in modulus: `λ(p) = 0` for `p = 2` (primary elements have odd norm) and for `p ≡ 3 (mod 4)`
(inert primes), while for `p ≡ 1 (mod 4)` the primary elements of norm `p` are exactly the two
conjugate primary primes, so `‖λ(p)‖ ≤ 2` (`heckeLam_prime_norm_le_two`).  Consequently

  `‖λ(p)p^{-s}‖ ≤ 2p^{-σ} ≤ 2p^{-3/4} ≤ 2·3^{-3/4} < 1`  for odd primes `p` and `σ ≥ 3/4`,

so each local inverse factor is bounded by the explicit constant `(1 - 2p^{-3/4})^{-1}`; the
hypothesis `log Pz ≥ 4` is exactly what makes `σ ≥ 1 - 1/log Pz ≥ 3/4` available.  The general
`n`-bound `‖λ(n)‖ ≤ 4τ(n)` (`heckeLam_bound`) handles the summands of `Q`.
-/
import Mathlib
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_norm_le_two

set_option autoImplicit false

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

noncomputable section

/-- The explicit majorant `(1 - 2p^{-3/4})^{-1}` of a local inverse Euler factor at a prime `p ≥ 3`;
at the ramified prime `p = 2` (where `λ(2) = 0`, so the factor is `1`) it is set to `1`.  The value
at `p ≤ 2` is only ever used at `p = 2`. -/
def locBnd (p : ℕ) : ℝ := if p ≤ 2 then 1 else (1 - 2 * (p : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹

/-- `2·3^{-3/4} < 1`, i.e. `2 < 3^{3/4}` (equivalent to `2^4 < 3^3`).  This is the numerical input
that makes `‖λ(p)p^{-s}‖ ≤ 2p^{-3/4} < 1` at a prime `p ≥ 3`. -/
lemma two_mul_three_rpow_neg_three_quarters_lt_one : (2 : ℝ) * 3 ^ (-(3 / 4 : ℝ)) < 1 := by
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have h : (2 : ℝ) < (3 : ℝ) ^ ((3 : ℝ) / 4) := by
    have h4 : (2 : ℝ) ^ 4 < ((3 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 := by
      have heq : ((3 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 = (3 : ℝ) ^ 3 := by
        rw [← Real.rpow_natCast ((3 : ℝ) ^ ((3 : ℝ) / 4)) 4,
          ← Real.rpow_mul (show (0 : ℝ) ≤ 3 by norm_num)]
        norm_num
      rw [heq]; norm_num
    exact (pow_lt_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt h3pos)
      (by norm_num : (4 : ℕ) ≠ 0)).mp h4
  rw [show -(3 / 4 : ℝ) = -((3 : ℝ) / 4) by norm_num,
    Real.rpow_neg (show (0 : ℝ) ≤ 3 by norm_num), ← div_eq_mul_inv]
  exact (div_lt_one h3pos).mpr h

/-- `2p^{-3/4} < 1` for every `p ≥ 3`. -/
lemma two_mul_rpow_neg_lt_one {p : ℕ} (hp : 3 ≤ p) : 2 * (p : ℝ) ^ (-(3 / 4 : ℝ)) < 1 := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (p : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (3 : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp3 (by norm_num)
  linarith [two_mul_three_rpow_neg_three_quarters_lt_one]

lemma locBnd_pos (p : ℕ) : 0 < locBnd p := by
  rw [locBnd]
  split_ifs with h
  · norm_num
  · have hp3 : 3 ≤ p := by omega
    exact inv_pos.mpr (by linarith [two_mul_rpow_neg_lt_one hp3])

/-- `‖λ(p)‖ ≤ 2` at every rational prime `p`: `p = 2` and `p ≡ 3 (mod 4)` give `λ(p) = 0`, and
`p ≡ 1 (mod 4)` is `heckeLam_prime_norm_le_two`. -/
lemma zcontHeckeLamPrimeNormLeTwo' (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {p : ℕ} (hp : p.Prime) :
    ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖ ≤ 2 := by
  by_cases h4 : p % 4 = 1
  · exact Work.FIArea5.S16Hecke.heckeLam_prime_norm_le_two hp h4 hchi
  · rw [Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four hp h4]; norm_num

/-- **The local inverse Euler factor is bounded uniformly in the strip `re s ≥ 3/4`.**  For a
rational prime `p` and `re s ≥ 3/4` one has `‖(1 - λ(p)p^{-s})^{-1}‖ ≤ locBnd p`. -/
lemma locF_inv_bound (chi : GaussianInt → ℂ) (m : ℤ) (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hσ : (3 / 4 : ℝ) ≤ s.re) :
    ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖ ≤ locBnd p := by
  by_cases h2 : p = 2
  · subst h2
    have hzero : Work.FIArea5.S16Hecke.heckeLam chi m 2 = 0 :=
      Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four Nat.prime_two (by norm_num)
    rw [hzero, zero_mul, sub_zero, inv_one, norm_one, locBnd,
      if_pos (by norm_num : (2 : ℕ) ≤ 2)]
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hpbnd : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
    have hlam : ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖ ≤ 2 :=
      zcontHeckeLamPrimeNormLeTwo' chi m hchi hp
    have hwn : ‖Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖
        ≤ 2 * (p : ℝ) ^ (-s.re) := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
      exact mul_le_mul_of_nonneg_right hlam (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    have hexp : -(s.re) ≤ -(3 / 4 : ℝ) := by linarith
    have hle1 : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hpbnd hexp
    have hwn' : ‖Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖
        ≤ 2 * (p : ℝ) ^ (-(3 / 4 : ℝ)) := by linarith [hwn, hle1]
    have hlt : 2 * (p : ℝ) ^ (-(3 / 4 : ℝ)) < 1 := two_mul_rpow_neg_lt_one hp3
    rw [locBnd, if_neg (by omega : ¬ p ≤ 2)]
    have hge : 0 < 1 - ‖Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖ := by
      linarith [hwn', hlt]
    have htri : 1 - ‖Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖
        ≤ ‖1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖ := by
      have h := norm_sub_norm_le (1 : ℂ)
        (Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))
      rwa [norm_one] at h
    have h2pos : 0 < 1 - 2 * (p : ℝ) ^ (-(3 / 4 : ℝ)) := by linarith
    rw [norm_inv]
    calc (‖1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖)⁻¹
        = 1 / ‖1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖ := by rw [one_div]
      _ ≤ 1 / (1 - ‖Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖) :=
          one_div_le_one_div_of_le hge htri
      _ ≤ 1 / (1 - 2 * (p : ℝ) ^ (-(3 / 4 : ℝ))) :=
          one_div_le_one_div_of_le h2pos (by linarith)
      _ = (1 - 2 * (p : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹ := by rw [one_div]

/-- **`P(s)` is bounded on the half-plane `re s ≥ 1 - 1/log Pz`** (first half of `zcontPQLocalBound`):
the product (16.33) of the local inverse factors over the primes `p ≤ Pz`, each bounded by the
explicit constant `locBnd p` as soon as `re s ≥ 3/4 ≥ 1 - 1/log Pz`. -/
theorem Pfac_bound (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hlogPz : 4 ≤ Real.log (Pa.Pz : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re →
      ‖Work.FIArea6.TauPieces.Pfac Pa chi m s‖ ≤ K := by
  have hlogpos : 0 < Real.log (Pa.Pz : ℝ) := by linarith
  have hδ : 1 / Real.log (Pa.Pz : ℝ) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) hlogPz
  have h34 : ∀ s : ℂ, 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re → (3 / 4 : ℝ) ≤ s.re := by
    intro s hs; linarith
  refine ⟨∏ p ∈ Nat.primesBelow (Pa.Pz + 1), locBnd p,
    Finset.prod_pos (fun p _ => locBnd_pos p), ?_⟩
  intro s hs
  rw [Work.FIArea6.TauPieces.Pfac]
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
    (fun p hp => locF_inv_bound chi m hchibd (Nat.prime_of_mem_primesBelow hp) (h34 s hs))

/-- Termwise bound for the summands of `Q(s)`: the general Hecke bound `‖λ(c)‖ ≤ 4τ(c)`, the
power bound `c^{-σ} ≤ c^{-3/4}` and the local factor bounds at the primes `p ∣ c`. -/
lemma summand_bound (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hσ : (3 / 4 : ℝ) ≤ s.re) {c : ℕ}
    (hc : c ∈ (Finset.Icc 1 ⌊Pa.C⌋₊).filter
      (fun c => Squarefree c ∧ Nat.Coprime c (∏ p ∈ Nat.primesBelow (Pa.Pz + 1), p))) :
    ‖Work.FIArea5.S16Hecke.heckeLam chi m c * (c : ℂ) ^ (-s)
        * ∏ p ∈ c.primeFactors,
            (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖
      ≤ 4 * (c.divisors.card : ℝ) * (c : ℝ) ^ (-(3 / 4 : ℝ))
        * ∏ p ∈ c.primeFactors, locBnd p := by
  have hc1 : 1 ≤ c := (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).1
  have hc0 : 0 < c := by omega
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc0
  have hnorm_eq : ‖Work.FIArea5.S16Hecke.heckeLam chi m c * (c : ℂ) ^ (-s)
        * ∏ p ∈ c.primeFactors,
            (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖
      = ‖Work.FIArea5.S16Hecke.heckeLam chi m c‖ * (c : ℝ) ^ (-s.re)
        * ∏ p ∈ c.primeFactors,
            ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖ := by
    rw [norm_mul, norm_mul, norm_prod, Complex.norm_natCast_cpow_of_pos hc0]
    simp [Complex.neg_re]
  rw [hnorm_eq]
  have h1 : ‖Work.FIArea5.S16Hecke.heckeLam chi m c‖ ≤ 4 * (c.divisors.card : ℝ) :=
    Work.FIArea5.S16Hecke.heckeLam_bound chi m hchibd hc1
  have h2 : (c : ℝ) ^ (-s.re) ≤ (c : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hc1) (by linarith)
  have h3 : ∏ p ∈ c.primeFactors,
        ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖
      ≤ ∏ p ∈ c.primeFactors, locBnd p :=
    Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
      (fun p hp => locF_inv_bound chi m hchibd (Nat.mem_primeFactors.mp hp).1 hσ)
  have h5 : 0 ≤ (c : ℝ) ^ (-s.re) := Real.rpow_nonneg (le_of_lt hcpos) _
  have h4 : 0 ≤ ∏ p ∈ c.primeFactors,
      ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖ :=
    Finset.prod_nonneg (fun p _ => norm_nonneg _)
  exact mul_le_mul (mul_le_mul h1 h2 h5 (by positivity)) h3 h4 (by positivity)

/-- **`Q(s)` obeys `‖Q(s)‖ ≤ K·C^{1-re s}` on `1 - 1/log Pz ≤ re s ≤ 2`** (second half of
`zcontPQLocalBound`): every summand of (16.34) is bounded by `4τ(c)c^{-3/4}∏_{p∣c}locBnd p`, uniformly
in `s`, and `C^{1-re s} ≥ C^{-1}` there. -/
theorem Qfac_bound (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hlogPz : 4 ≤ Real.log (Pa.Pz : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖Work.FIArea6.TauPieces.Qfac Pa chi m s‖ ≤ K * Pa.C ^ (1 - s.re) := by
  have hlogpos : 0 < Real.log (Pa.Pz : ℝ) := by linarith
  have hδ : 1 / Real.log (Pa.Pz : ℝ) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) hlogPz
  have h34 : ∀ s : ℂ, 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re → (3 / 4 : ℝ) ≤ s.re := by
    intro s hs; linarith
  set S : Finset ℕ := (Finset.Icc 1 ⌊Pa.C⌋₊).filter
      (fun c => Squarefree c ∧ Nat.Coprime c (∏ p ∈ Nat.primesBelow (Pa.Pz + 1), p)) with hS
  set A : ℝ := ∑ c ∈ S, 4 * (c.divisors.card : ℝ) * (c : ℝ) ^ (-(3 / 4 : ℝ))
      * ∏ p ∈ c.primeFactors, locBnd p with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg fun c _ => by
      have hp := Finset.prod_nonneg (fun p (_ : p ∈ c.primeFactors) => (locBnd_pos p).le)
      exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg c) _)) hp
  refine ⟨Pa.C * A + 1, by nlinarith [Pa.hC1, hA0], ?_⟩
  intro s hs hs2
  have hσ : (3 / 4 : ℝ) ≤ s.re := h34 s hs
  have hC1 : (1 : ℝ) ≤ Pa.C := Pa.hC1
  have hCpos : 0 < Pa.C := by linarith
  rw [Work.FIArea6.TauPieces.Qfac, ← hS]
  refine le_trans (le_trans (norm_sum_le _ _)
    (Finset.sum_le_sum fun c hc => summand_bound Pa chi m hchibd hσ hc)) ?_
  rw [← hA]
  have hexp : 0 ≤ 2 - s.re := by linarith
  have hone : 1 ≤ Pa.C ^ (2 - s.re) := Real.one_le_rpow hC1 hexp
  have hkey : Pa.C * Pa.C ^ (1 - s.re) = Pa.C ^ (2 - s.re) := by
    rw [show (2 : ℝ) - s.re = 1 + (1 - s.re) by ring, Real.rpow_add hCpos, Real.rpow_one]
  have hx0 : 0 ≤ Pa.C ^ (1 - s.re) := Real.rpow_nonneg (by linarith) _
  have h1 : A ≤ A * Pa.C ^ (2 - s.re) := by nlinarith [hA0, hone]
  have h2 : A * Pa.C ^ (2 - s.re) = Pa.C * A * Pa.C ^ (1 - s.re) := by
    rw [← hkey]; ring
  have h3 : Pa.C * A * Pa.C ^ (1 - s.re) ≤ (Pa.C * A + 1) * Pa.C ^ (1 - s.re) :=
    mul_le_mul_of_nonneg_right (by linarith) hx0
  linarith [h1, h2, h3]

theorem zcontPQLocalBound (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hlogPz : 4 ≤ Real.log (Pa.Pz : ℝ)) :
    (∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re →
        ‖Work.FIArea6.TauPieces.Pfac Pa chi m s‖ ≤ K) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re → s.re ≤ 2 →
        ‖Work.FIArea6.TauPieces.Qfac Pa chi m s‖ ≤ K * Pa.C ^ (1 - s.re)) :=
  ⟨Pfac_bound Pa chi m hchibd hlogPz, Qfac_bound Pa chi m hchibd hlogPz⟩

end

end Work.FIArea6Road
