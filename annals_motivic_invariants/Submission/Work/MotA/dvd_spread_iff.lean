import Mathlib
import Submission.Work.MotA.Defs
import Submission.Work.MotA.Spread
import Submission.Work.MotA.SpreadAux
import Submission.Work.MotA.spreadMap_injective
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option linter.style.haveILetI false

noncomputable section

namespace Work.MotA

open MvPolynomial

/-- A nonzero element of a field gives a unit among the constants of a polynomial ring.  (One line,
but used twice below.) -/
private lemma isUnit_C_of_ne_zero (K : Type) [Field K] (σ : Type) (a : K) (ha : a ≠ 0) :
    IsUnit (MvPolynomial.C a : MvPolynomial σ K) :=
  IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr ha)

/-- **`S1` census, horizontal primes.**  Let `p ∈ 𝕜[t,x₁,…,xₙ]` be a prime element that is *not*
vertical, in the sense that `Work.MotA.spreadMap 𝕜 n p` is not a unit of `K[x₁,…,xₙ]`
(`K = RatFunc 𝕜`); equivalently (and this is the only case that is used) `p` is not associated to a
polynomial in `t` alone.  Then `p` divides `F' ∈ 𝕜[t,x₁,…,xₙ]` if and only if its image
`spreadMap 𝕜 n p` divides `spreadMap 𝕜 n F'` in `K[x₁,…,xₙ]`.

(The hypothesis is necessary: for the vertical prime `p = t + 1` the image `spreadMap p = C (t+1)` is
a nonzero constant, hence a unit of `K[x]`, so it divides everything while `p ∤ 1`.  For `n = 0` there
are no primes satisfying the hypothesis, so the statement is vacuous there and that is correct.)

This is the horizontal half of the census used by `SPREAD`: with
`spreadMap 𝕜 n F' = C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c) * F` (node `S1`), the horizontal
prime factors of `F'` are exactly the prime factors of `F` over `K` that lie in `𝕜[t,x₁,…,xₙ]`, and
their residue fields agree (`Frac(𝕜[t,x]/pσ)` is `Frac(K[x]/p·K[x])`, since `K` embeds).

Route.  `(→)` apply `spreadMap 𝕜 n` to `p ∣ F'`.  `(←)`: from `spreadMap p · Q = spreadMap F'` with
`Q ∈ MvPolynomial (Fin n) (RatFunc 𝕜)`, choose a nonzero `s ∈ 𝕜[t]` (i.e. `s = aeval (X 0) s₀` for
some `0 ≠ s₀ : Polynomial 𝕜`) clearing the `t`-denominators of the coefficients of `Q`, so that
`s·Q = spreadMap h` for some `h ∈ 𝕜[t,x]` (`Q ∈ K[x] = 𝕜(t)[x]` and `𝕜[t]` is a UFD).  Then
`spreadMap (s · F') = C s · spreadMap F' = spreadMap p · spreadMap h = spreadMap (p · h)`, so by
injectivity of `spreadMap` (`Work.MotA.spreadMap_injective`, then
`Work.MotA.spreadMap_X_zero`/`spreadMap_C` for the `t`-polynomials) we get `s · F' = p · h` in
`𝕜[t,x]`; as `p` is a prime element and `p ∤ s` — otherwise `p` would be associated to an irreducible
factor of `s`, i.e. vertical, contradicting that `spreadMap p` is a nonunit — Euclid's divisibility
argument gives `p ∣ F'`. -/
theorem dvd_spread_iff (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) 𝕜) (hp : Prime p)
    (hu : ¬ IsUnit (Work.MotA.spreadMap 𝕜 n p))
    (F' : MvPolynomial (Fin (n + 1)) 𝕜) :
    p ∣ F' ↔ Work.MotA.spreadMap 𝕜 n p ∣ Work.MotA.spreadMap 𝕜 n F' := by
  constructor
  · -- `(→)`: push a divisibility witness through the algebra map.
    rintro ⟨g, rfl⟩
    exact ⟨spreadMap 𝕜 n g, by rw [map_mul]⟩
  · -- `(←)`: clear the `t`-denominators of the cofactor, then cancel `spreadMap`.
    rintro ⟨Q, hQ⟩
    obtain ⟨c, hc, b, hb⟩ := exists_clearing 𝕜 n Q
    -- `spreadMap 𝕜 n (tPoly 𝕜 n c * F') = spreadMap 𝕜 n (p * b)`
    have hkey : spreadMap 𝕜 n (tPoly 𝕜 n c * F') = spreadMap 𝕜 n (p * b) := by
      rw [spreadMap_tPoly_mul, hQ, map_mul, hb]
      first | refl_ring1 | ring
    have hcancel : tPoly 𝕜 n c * F' = p * b := spreadMap_injective 𝕜 n hkey
    have hdiv : p ∣ tPoly 𝕜 n c * F' := ⟨b, hcancel⟩
    -- `p` does not divide the `t`-polynomial `tPoly 𝕜 n c`: otherwise its image, the unit
    -- `C (algebraMap c)` of `K[x]`, would be divisible by the nonunit `spreadMap p`.
    have hndvd : ¬ p ∣ tPoly 𝕜 n c := by
      rintro ⟨u, hu'⟩
      have hdvd : spreadMap 𝕜 n p ∣
          MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c) := by
        refine ⟨spreadMap 𝕜 n u, ?_⟩
        have h := congrArg (spreadMap 𝕜 n) hu'
        rw [spreadMap_tPoly, map_mul] at h
        exact h
      have hunit : IsUnit (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c) :
          MvPolynomial (Fin n) (RatFunc 𝕜)) :=
        isUnit_C_of_ne_zero (RatFunc 𝕜) (Fin n) _
          (fun h0 => hc (IsFractionRing.injective (Polynomial 𝕜) (RatFunc 𝕜)
            (by simpa using h0)))
      exact hu (isUnit_of_dvd_unit hdvd hunit)
    exact (hp.dvd_or_dvd hdiv).resolve_left hndvd

end Work.MotA

end
