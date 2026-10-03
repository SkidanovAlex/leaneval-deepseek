/-
# `Submission.Work.FIArea5.S16Hecke.heckeLSeries_conj`

**Complex conjugation of the Hecke `L`-series.**  For a coefficient function `χ : ℤ[i] → ℂ`,
`m : ℕ` and `s : ℂ`:

`L(s, ψ̄ ^{(−m)}) = conj L(conj s, ψ ^{(m)})`,

i.e. conjugating the Größencharacter and negating the weight conjugates the `L`-value and
conjugates `s`.

The proof is termwise:

* `GaussianIntPsi.star_ratio`: the "unit factor" `z/|z|` of a Gaussian integer satisfies
  `conj (z/|z|) = (z/|z|)⁻¹` (its modulus is one, except at `z = 0` where both sides vanish).
* `psi_conj`: consequently `ψ(χ̄, −k)(z) = conj (ψ(χ, k)(z))`, since
  `(conj (z/|z|))^k = (z/|z|)^{-k}`.
* `heckeLam_conj`: summing the previous identity over the (conjugation-invariant) defining
  range of `heckeLam` gives `λ_{χ̄,−k}(n) = conj (λ_{χ,k}(n))`.
* `LSeries_conj`: `∑' star (f n)/n^s = star (∑' f n / n^{conj s})`, using
  `conj (n^conj s) = n^s` for a natural number `n`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

/-- The unit factor `z/|z|` of a Gaussian integer is a unit modulus complex number, so it is
equal to the inverse of its complex conjugate.  (At `z = 0` both sides are `0`.) -/
lemma star_ratio (z : GaussianInt) :
    star (z.toComplex / ((Real.sqrt (gnorm z : ℝ)) : ℂ))
      = (z.toComplex / ((Real.sqrt (gnorm z : ℝ)) : ℂ))⁻¹ := by
  rcases eq_or_ne (Real.sqrt (gnorm z : ℝ)) 0 with hr | hr
  · rw [hr, Complex.ofReal_zero, div_zero, star_zero, inv_zero]
  · refine (Complex.inv_eq_conj ?_).symm
    rw [norm_div, norm_toComplex, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_self hr]

/-- **(16.16), conjugation**: conjugating `χ` and negating the weight conjugates `ψ`. -/
lemma psi_conj (chi : GaussianInt → ℂ) (m : ℕ) (z : GaussianInt) :
    psi (fun z : GaussianInt => star (chi z)) (-(m : ℤ)) z = star (psi chi (m : ℤ) z) := by
  simp only [psi]
  rw [Complex.star_def, map_mul, map_zpow₀]
  rw [show starRingEnd ℂ (z.toComplex / ((Real.sqrt (gnorm z : ℝ)) : ℂ))
        = (z.toComplex / ((Real.sqrt (gnorm z : ℝ)) : ℂ))⁻¹ from star_ratio z,
    inv_zpow, zpow_neg]

/-- **(16.30), conjugation**: `λ_{χ̄,−k}(n) = conj (λ_{χ,k}(n))`. -/
lemma heckeLam_conj (chi : GaussianInt → ℂ) (m : ℕ) (n : ℕ) :
    heckeLam (fun z : GaussianInt => star (chi z)) (-(m : ℤ)) n
      = star (heckeLam chi (m : ℤ) n) := by
  simp only [heckeLam, Complex.star_def]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun z _ => psi_conj chi m z)

/-- **Conjugation of an `L`-series**: conjugating the coefficients and conjugating `s`. -/
lemma LSeries_conj (f : ℕ → ℂ) (s : ℂ) :
    LSeries (fun n => star (f n)) s = star (LSeries f (star s)) := by
  rw [LSeries, LSeries, tsum_star]
  refine tsum_congr (fun n => ?_)
  rw [LSeries.term_def, LSeries.term_def]
  split_ifs with _hn
  · simp
  · rw [Complex.star_def, map_div₀]
    congr 1
    have hx : ((n : ℂ)).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Ne.symm Real.pi_ne_zero
    rw [← Complex.conj_cpow (n : ℂ) s hx, Complex.conj_natCast]

theorem heckeLSeries_conj (chi : GaussianInt → ℂ) (m : ℕ) (s : ℂ) :
    heckeLSeries (fun z : GaussianInt => star (chi z)) (-(m : ℤ)) s
      = star (heckeLSeries chi (m : ℤ) (star s)) := by
  rw [heckeLSeries, heckeLSeries, ← LSeries_conj (fun n => heckeLam chi (m : ℤ) n) s]
  rw [funext (fun n => heckeLam_conj chi m n)]

end Work.FIArea5.S16Hecke
