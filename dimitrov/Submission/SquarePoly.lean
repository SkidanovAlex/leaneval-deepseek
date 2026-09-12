import Mathlib
import Submission.Powers
import Submission.RootCorr

/-!
# The polynomial dichotomy (Layer C)

For a monic polynomial `P`, `P₂ := pow2 P` and `P₄ := pow4 P` are monic of the
same degree as `P` (`Submission.RootCorr.pow2_natDegree`).  This module proves:

> If `P₂` is irreducible (as an element of `ℤ[X]`) and `P₂ · P₄` is a perfect
> square in `ℤ[X]`, then `P₄ = P₂`.

This is the algebraic dichotomy used in the analytic engine of the proof of
Dimitrov's theorem (the analogue of Lemma 2.3 of Dimitrov, arXiv:1912.12545):
rationality of the square root forces `P₂ P₄` to be a square; combined with
irreducibility of `P₂` this forces `P₄ = P₂`; and `P₄ = P₂` is what ultimately
contradicts "`α` is not a root of unity" (see `Submission.RootOfUnity`).

## Proof plan (all inside `ℤ[X]`, which is a UFD)

Let `d := P.natDegree`, `P₂ := pow2 P`, `P₄ := pow4 P`.

1. `P₂` and `P₄` are monic with `natDegree = d`:
   `pow2_monic P hP`, `pow2_monic (pow2 P) (pow2_monic P hP)`, and
   `pow2_natDegree` twice (`Submission.RootCorr.pow2_natDegree`).
   Consequently both are nonzero (monic) and not units.

2. `ℤ[X]` is a UFD (`Polynomial.uniqueFactorizationMonoid`; `ℤ` is a UFD) so an
   irreducible element is prime.  Find the lemma (search for
   `irreducible_iff_prime` / `Prime` / `UniqueFactorizationMonoid`), or use
   `Polynomial.irreducible_of_monic` + a prime lemma.  From `h2irr : Irreducible P₂`
   obtain `hprime : Prime P₂`.

3. From `hsq : ∃ g, P₂ * P₄ = g ^ 2`: `Prime P₂`, `P₂ ∣ g * g`, so
   `P₂ ∣ g` (Euclid's lemma: `Prime.dvd_of_dvd_pow` or similar).  Get `h : ℤ[X]`
   with `g = P₂ * h`, and substitute to obtain `P₂ * P₄ = P₂ * P₂ * h * h`.
   Cancel the nonzero `P₂` (`mul_left_cancel₀` in the domain `ℤ[X]`):
   `P₄ = P₂ * h ^ 2`.

4. Degrees: `natDegree (P₄) = d` and `natDegree (P₂ * h ^ 2) = d + 2 * natDegree h`
   (both `P₂` and `h^2` are... note `natDegree_mul` applies since the factors are
   monic/nonzero: `P₂` is monic nonzero; for `h` use that `natDegree (h^2)` is even
   or just bound: since `natDegree (P₄) ≤ d` and `d + 2 * natDegree h = natDegree P₄`
   argue `natDegree h = 0`).  Get `natDegree h = 0`, hence `h = C c` for some
   `c : ℤ` (`eq_C_of_natDegree_eq_zero`).

5. Substitute: `P₄ = P₂ * C (c ^ 2)`; compare the leading coefficient (coeff at `d`;
   both sides are monic of degree `d`): `1 = c ^ 2` in `ℤ`; since the monic
   coefficient of `P₄` is `1` and of `P₂ * C (c^2)` is `c^2`, get `c ^ 2 = 1`.
   Hence `P₄ = P₂ * C 1 = P₂`.

You may add helper lemmas. Do NOT change the statement of
`pow4_eq_pow2_of_square`.  No unfilled obligations may remain in this file.
-/

noncomputable section

open Polynomial
open scoped Polynomial

namespace Submission.SquarePoly

open Submission.Powers
open Submission.RootCorr

/-- **Dichotomy.** If the square-power polynomial `P₂ := pow2 P` of a monic `P`
is irreducible and `P₂ P₄` is a perfect square (all in `ℤ[X]`), then
`P₄ = P₂`. -/
theorem pow4_eq_pow2_of_square (P : ℤ[X]) (hP : P.Monic)
    (hP2irr : Irreducible (pow2 P))
    (hsq : ∃ g : ℤ[X], pow2 P * pow4 P = g ^ 2) :
    pow4 P = pow2 P := by
  classical
  -- Step 1: P₂ and P₄ are monic (hence nonzero) and have the same degree.
  have hP2monic : (pow2 P).Monic := pow2_monic P hP
  have hP4monic : (pow4 P).Monic := by
    simpa [pow4] using pow2_monic (pow2 P) (pow2_monic P hP)
  have hP2ne0 : pow2 P ≠ 0 := hP2monic.ne_zero
  have hP4ne0 : pow4 P ≠ 0 := hP4monic.ne_zero
  -- Step 2: irreducible in the UFD ℤ[X] ⟹ prime.
  have hprime : Prime (pow2 P) :=
    (UniqueFactorizationMonoid.irreducible_iff_prime (a := pow2 P)).mp hP2irr
  -- Step 3: P₂ ∣ g, write g = P₂ * h, cancel P₂.
  rcases hsq with ⟨g, hg⟩
  have hdvd : (pow2 P) ∣ g * g := by
    rw [← pow_two g]
    rw [← hg]
    exact dvd_mul_right (pow2 P) (pow4 P)
  have hPg : (pow2 P) ∣ g := (hprime.dvd_or_dvd hdvd).elim id id
  rcases hPg with ⟨h, rfl⟩
  have hmain : pow4 P = pow2 P * h ^ 2 := by
    apply mul_left_cancel₀ hP2ne0
    calc
      pow2 P * pow4 P = (pow2 P * h) ^ 2 := hg
      _ = pow2 P * (pow2 P * h ^ 2) := by ring
  -- Step 4: degree counting forces natDegree h = 0.
  have hh2ne0 : h ^ 2 ≠ 0 := by
    intro hz
    apply hP4ne0
    calc
      pow4 P = pow2 P * h ^ 2 := hmain
      _ = 0 := by simp [hz]
  have hdeg_mul : (pow2 P * h ^ 2).natDegree =
      (pow2 P).natDegree + (h ^ 2).natDegree :=
    Polynomial.natDegree_mul hP2ne0 hh2ne0
  have hdeg_h2 : (h ^ 2).natDegree = 2 * h.natDegree :=
    Polynomial.natDegree_pow h 2
  have hdeg4 : (pow4 P).natDegree = (pow2 P).natDegree := by
    simpa [pow4] using pow2_natDegree (pow2 P) hP2monic
  have hdeg0 : h.natDegree = 0 := by
    have hnat : (pow4 P).natDegree = (pow2 P).natDegree + 2 * h.natDegree := by
      calc
        (pow4 P).natDegree = (pow2 P * h ^ 2).natDegree := by rw [hmain]
        _ = (pow2 P).natDegree + (h ^ 2).natDegree := hdeg_mul
        _ = (pow2 P).natDegree + 2 * h.natDegree := by rw [hdeg_h2]
    omega
  have hC : h = C (h.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
  -- Step 5: h = C c with c² = 1, hence P₄ = P₂ · C 1 = P₂.
  have hsqC : h ^ 2 = (C (h.coeff 0)) ^ 2 := congrArg (fun x : ℤ[X] => x ^ 2) hC
  have hhC : h ^ 2 = C ((h.coeff 0) ^ 2) := by
    rw [hsqC]
    exact (map_pow C (h.coeff 0) 2).symm
  have hmain2 : pow4 P = pow2 P * C ((h.coeff 0) ^ 2) := by
    rw [hmain, hhC]
  have hcL : (pow4 P).coeff (pow2 P).natDegree = 1 := by
    rw [← hdeg4]
    rw [Polynomial.coeff_natDegree]
    exact hP4monic.leadingCoeff
  have hcR : (pow2 P * C ((h.coeff 0) ^ 2)).coeff (pow2 P).natDegree =
      (h.coeff 0) ^ 2 := by
    rw [Polynomial.coeff_mul_C]
    rw [Polynomial.coeff_natDegree]
    rw [hP2monic.leadingCoeff]
    simp
  have hc2 : (h.coeff 0) ^ 2 = 1 := by
    calc
      (h.coeff 0) ^ 2 =
          (pow2 P * C ((h.coeff 0) ^ 2)).coeff (pow2 P).natDegree := hcR.symm
      _ = (pow4 P).coeff (pow2 P).natDegree := by rw [hmain2]
      _ = 1 := hcL
  calc
    pow4 P = pow2 P * C ((h.coeff 0) ^ 2) := hmain2
    _ = pow2 P := by simp [hc2]

end Submission.SquarePoly

end
