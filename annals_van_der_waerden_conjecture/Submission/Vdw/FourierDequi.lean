import Mathlib
import Submission.Vdw.FourierAssembly

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The §4 Fourier input in the paper's multi-prime form (Corollary `Dequi2`)

The §4 chapter of the project's development
(`BoxFourier`, `FourierExpand`, `FourierWeight`, `BoxFourierIndex`) provides,
for a *single* prime `p` and a modulus-`p` residue set `T`, the Fourier
counting bound

    `#{z ∈ (BddInt H)^n : z mod p ∈ T} ≤ |T|·(2H+1)^n/p^n
        + M/p^n·(5(p + 2H+1)(1+log p))^n`,

where `M` bounds the Fourier coefficients of `T` on the nonzero frequencies
(paper Proposition `ftgen2`, at the level of the index-`≥ k` sets; the
logarithmic factor is the `C^ε` of the paper, absorbed by choosing `ε`
smaller).

What Case I actually consumes is the *multi-prime* statement of the paper,
namely **Corollary `Dequi2`**: the number of monic degree-`n` integer
polynomials in `[-H,H]^n` that, modulo each of the primes `p_i | C`, have
index at least `k_i`, is at most

    `O_ε(c^{ω(C)}H^n/D + C^ε ∏_i p_i^{n-k_i-1/2})`,  `D = ∏_i p_i^{k_i}`.

(The proof in the paper is a twisted-Poisson-summation argument on the joint
set `∏_i Ψ_{p_i}`, whose error term is estimated via the gcd-decomposition of
the frequency tuple — this is *not* a consequence of the single-prime
counting bounds, which do not iterate; it is exactly the content of §4 that is
still missing from the project's §4 chapter.)

This module formalises the multi-prime statement as `DequiBound n` and proves
that it implies the index-form input `PerIrrBound n c` consumed by Case I.
The derivation is the paper's `fbound2`: writing `C = radical D` and using
`C ≤ H^{1+δ}` with `δ = 1/(2n) < 1/(2n-1)`, the error term

    `C^{n-1/2+ε}/D`

is dominated by `H^n/D` as soon as `ε < 1/(2(2n+1))` — this is precisely the
`δ < 1/(2n-1)` condition of the paper (the `-1/2` in the exponent is the Weil
improvement of `ftgen2` over `ftgen`, and is what makes `δ` as large as
`1/(2n)` admissible).

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **The §4 Fourier input in the paper's multi-prime form** (Corollary
`Dequi2`).

For every `ε > 0` there is `c ≥ 1` such that for every monic degree-`n`
discriminant-compatible modulus `D` (squarefull, `D ≥ 2`, all prime divisors
`> n`, exponent of each prime divisor `< n`), the number of box polynomials
satisfying the index conditions `index (f mod p) ≥ v_p(D)` for all `p | D` is
at most

    `c^{ω(D)}·H^n/D + (radical D)^{n-1/2+ε}/D`.

Here `(radical D)^{n-1/2+ε}/D = C^{n-1/2+ε}/D` with `C = radical D` is the
paper's second term `C^ε ∏_{p|D} p^{n-v_p(D)-1/2}`, rewritten using
`∏_{p|D} p^{n-v_p(D)} = C^n/D`. -/
def DequiBound (n : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℕ, 1 ≤ c ∧ ∀ H D : ℕ, D ≠ 0 → Squarefull D → 2 ≤ D →
    (∀ p ∈ D.primeFactors, n < p) →
    (∀ p ∈ D.primeFactors, D.factorization p < n) →
    ((Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (D.factorization (p : ℕ))
          (boxResidue n H (p : ℕ) f)} : ℕ) : ℝ)
      ≤ (c : ℝ) ^ omega D * ((H : ℝ) ^ n / (D : ℝ))
        + (radical D : ℝ) ^ ((n : ℝ) - 1 / 2 + ε) / (D : ℝ)

/-- The exponent comparison behind the paper's `δ < 1/(2n-1)` condition:
with `ε = 1/(4(2n+1))` and `s = n - 1/2 + ε` one has
`(1 + 1/(2n))·s ≤ n`. -/
lemma expo_comparison (n : ℕ) (hn : 1 ≤ n) :
    (1 + 1 / (2 * (n : ℝ))) * ((n : ℝ) - 1 / 2 + 1 / (4 * (2 * (n : ℝ) + 1)))
      ≤ (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega)
  have h1 : (1 + 1 / (2 * (n : ℝ))) * ((n : ℝ) - 1 / 2) = (n : ℝ) - 1 / (4 * (n : ℝ)) := by
    field_simp
    ring
  have h2 : (1 + 1 / (2 * (n : ℝ))) * (1 / (4 * (2 * (n : ℝ) + 1))) = 1 / (8 * (n : ℝ)) := by
    field_simp
    ring
  rw [mul_add, h1, h2]
  have h3 : (1 : ℝ) / (8 * (n : ℝ)) ≤ 1 / (4 * (n : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  linarith

/-- **The paper's `fbound2`**: the multi-prime Fourier input implies the
index-form input `PerIrrBound` consumed by Case I. -/
theorem perIrrBound_of_dequiBound (n : ℕ) (hn : 3 ≤ n) (h : DequiBound n) :
    ∃ c, 1 ≤ c ∧ PerIrrBound n c := by
  obtain ⟨c, hc1, hc⟩ := h (1 / (4 * (2 * (n : ℝ) + 1))) (by positivity)
  refine ⟨2 * c, by omega, ?_⟩
  intro H D hD0 hsq hD2 hgt hrad hfac
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hrad_ge : (1 : ℝ) ≤ (radical D : ℝ) := by
    have hru : radical D ≠ 0 := by
      rw [radical_eq_prod_primeFactors]
      exact Finset.prod_ne_zero_iff.mpr
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hru)
  have hH1 : 1 ≤ H := by
    have h3 : (1 : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) := le_trans hrad_ge hrad
    rcases Nat.eq_zero_or_pos H with h0 | hpos
    · exfalso
      rw [h0, Nat.cast_zero, Real.zero_rpow (by positivity)] at h3
      linarith
    · exact hpos
  have hkey := hc H D hD0 hsq hD2 hgt hfac
  -- the error term is dominated by `H^n`
  have herr : (radical D : ℝ) ^ ((n : ℝ) - 1 / 2 + 1 / (4 * (2 * (n : ℝ) + 1)))
      ≤ (H : ℝ) ^ n := by
    have hs_pos : (0 : ℝ) < (n : ℝ) - 1 / 2 + 1 / (4 * (2 * (n : ℝ) + 1)) := by
      have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h4 : (0 : ℝ) < 1 / (4 * (2 * (n : ℝ) + 1)) := by positivity
      linarith
    calc (radical D : ℝ) ^ ((n : ℝ) - 1 / 2 + 1 / (4 * (2 * (n : ℝ) + 1)))
        ≤ ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ)))) ^
            ((n : ℝ) - 1 / 2 + 1 / (4 * (2 * (n : ℝ) + 1))) :=
          Real.rpow_le_rpow (by positivity) hrad hs_pos.le
      _ = (H : ℝ) ^ ((1 + 1 / (2 * (n : ℝ))) *
            ((n : ℝ) - 1 / 2 + 1 / (4 * (2 * (n : ℝ) + 1)))) := by
          rw [Real.rpow_mul (Nat.cast_nonneg H)]
      _ ≤ (H : ℝ) ^ (n : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hH1) ?_
          exact expo_comparison n (by omega)
      _ = (H : ℝ) ^ n := Real.rpow_natCast _ _
  -- `ω D ≥ 1`, so `c^ω + 1 ≤ (2c)^ω`
  have homega1 : 1 ≤ omega D := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : D ≠ 1)
    have hmem : p ∈ D.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hD0⟩
    have : 0 < omega D := Finset.card_pos.mpr ⟨p, hmem⟩
    omega
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hpow1 : (1 : ℝ) ≤ (c : ℝ) ^ omega D := one_le_pow₀ hcR
  have h2pow : (2 : ℝ) ≤ (2 : ℝ) ^ omega D := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ omega D := pow_le_pow_right₀ (by norm_num) homega1
  have hconst : (c : ℝ) ^ omega D + 1 ≤ (((2 * c : ℕ)) : ℝ) ^ omega D := by
    calc (c : ℝ) ^ omega D + 1 ≤ (c : ℝ) ^ omega D + (c : ℝ) ^ omega D := by
          linarith [hpow1]
      _ = 2 * (c : ℝ) ^ omega D := by ring
      _ ≤ (2 : ℝ) ^ omega D * (c : ℝ) ^ omega D :=
          mul_le_mul_of_nonneg_right h2pow (by positivity)
      _ = ((2 : ℝ) * (c : ℝ)) ^ omega D := (mul_pow _ _ _).symm
      _ = (((2 * c : ℕ)) : ℝ) ^ omega D := by push_cast; ring
  have hsum : ((Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (D.factorization (p : ℕ))
          (boxResidue n H (p : ℕ) f)} : ℕ) : ℝ)
      ≤ ((c : ℝ) ^ omega D + 1) * ((H : ℝ) ^ n / (D : ℝ)) := by
    have hdiv : (radical D : ℝ) ^ ((n : ℝ) - 1 / 2 + 1 / (4 * (2 * (n : ℝ) + 1))) / (D : ℝ)
        ≤ (H : ℝ) ^ n / (D : ℝ) :=
      div_le_div_of_nonneg_right herr hDpos.le
    calc ((Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
          indexClass (F := ZMod (p : ℕ)) n (D.factorization (p : ℕ))
            (boxResidue n H (p : ℕ) f)} : ℕ) : ℝ)
        ≤ (c : ℝ) ^ omega D * ((H : ℝ) ^ n / (D : ℝ))
            + (radical D : ℝ) ^ ((n : ℝ) - 1 / 2 + 1 / (4 * (2 * (n : ℝ) + 1))) / (D : ℝ) :=
          hkey
      _ ≤ (c : ℝ) ^ omega D * ((H : ℝ) ^ n / (D : ℝ)) + (H : ℝ) ^ n / (D : ℝ) := by
          linarith [hdiv]
      _ = ((c : ℝ) ^ omega D + 1) * ((H : ℝ) ^ n / (D : ℝ)) := by ring
  calc ((Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (D.factorization (p : ℕ))
          (boxResidue n H (p : ℕ) f)} : ℕ) : ℝ)
      ≤ ((c : ℝ) ^ omega D + 1) * ((H : ℝ) ^ n / (D : ℝ)) := hsum
    _ ≤ (((2 * c : ℕ)) : ℝ) ^ omega D * ((H : ℝ) ^ n / (D : ℝ)) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = (((2 * c : ℕ)) : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by ring

/-! ## Endpoints

The strongest current reductions of the challenge theorem: from the paper's
Corollary `Dequi2` (`DequiBound`) plus the Case-II region bound `SubcaseI_P2`
plus (for composite `n`) the imprimitive bound `ImprimitiveBad`. -/

/-- **The challenge theorem from the paper's multi-prime Fourier input.** -/
theorem theorem_1_of_dequi (n : ℕ) (hn : 3 ≤ n) (h : DequiBound n)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h3 : (fun H : ℕ => ((SubcaseI_P3 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨c, hc1, hc⟩ := perIrrBound_of_dequiBound n hn h
  exact theorem_1_of_perIrr n c hn hc1 hc h2 h3 h4

/-- **The challenge theorem from `DequiBound` and the Case-II region**: the
subcase-(i) region `SubcaseI_P3` is discharged from the §4 Fourier input
(`SubcaseI_P3_isBigO_of_perIrrBound`), so only the Case-II region and the
imprimitive region remain. -/
theorem theorem_1_of_dequi_three (n : ℕ) (hn : 3 ≤ n) (h : DequiBound n)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨c, hc1, hc⟩ := perIrrBound_of_dequiBound n hn h
  exact theorem_1_of_perIrr_three n c hn hc1 hc h2 h4

/-- **The challenge theorem in prime degree from `DequiBound`**: only the
Case-II region bound remains (the imprimitive input is vacuous in prime degree
and the subcase-(i) region is discharged from `DequiBound`). -/
theorem theorem_1_of_dequi_one_prime (n : ℕ) (hn : 3 ≤ n) (hprime : Nat.Prime n)
    (h : DequiBound n)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨c, hc1, hc⟩ := perIrrBound_of_dequiBound n hn h
  exact theorem_1_of_perIrr_one_prime n c hn hprime hc1 hc h2

end

end Submission.Vdw
