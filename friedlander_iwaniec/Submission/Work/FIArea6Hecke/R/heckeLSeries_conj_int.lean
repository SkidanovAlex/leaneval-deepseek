/-
# `Submission.Work.FIArea6Hecke.R.heckeLSeries_conj_int`

**Complex conjugation of the Hecke `L`-series, integer weight.**

The companion lemma `Work.FIArea5.S16Hecke.heckeLSeries_conj` states the conjugation identity
only for nonnegative weight, i.e. it produces the series of weight `-(m : ℤ)` attached to
`star ∘ χ` from the series of weight `(m : ℤ)` attached to `χ`.  Here we record the same
identity with the weight an *arbitrary* integer `m : ℤ`:

`L(s, ψ̄^{(-m)}) = conj L(conj s, ψ^{(m)})`.

The proof is the same termwise argument as in the nonnegative case, and in fact the whole
argument goes through verbatim for `k : ℤ`, since `^` is `zpow` throughout:

* `psi_conj_int`: `ψ(χ̄, −k)(z) = conj (ψ(χ, k)(z))` for `k : ℤ`, using
  `star (z/|z|) = (z/|z|)⁻¹` (`Work.FIArea5.S16Hecke.star_ratio`).
* `heckeLam_conj_int`: summing over the conjugation-invariant range of `heckeLam`.
* `heckeLSeries_conj_int`: `LSeries_conj` (`∑' star (f n)/n^s = star (∑' f n / n^{conj s})`).
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_conj
import Submission.Work.FIArea5.S16Hecke.Defs

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators
open Work.FIPlan

/-- **(16.16), conjugation, integer weight**: conjugating `χ` and negating the weight
conjugates `ψ`, for an arbitrary integer weight. -/
lemma psi_conj_int (chi : GaussianInt → ℂ) (k : ℤ) (z : GaussianInt) :
    Work.FIArea5.S16Hecke.psi (fun z : GaussianInt => star (chi z)) (-k) z
      = star (Work.FIArea5.S16Hecke.psi chi k z) := by
  simp only [Work.FIArea5.S16Hecke.psi]
  rw [Complex.star_def, map_mul, map_zpow₀]
  rw [show starRingEnd ℂ (z.toComplex / ((Real.sqrt (gnorm z : ℝ)) : ℂ))
        = (z.toComplex / ((Real.sqrt (gnorm z : ℝ)) : ℂ))⁻¹
      from Work.FIArea5.S16Hecke.star_ratio z,
    inv_zpow, zpow_neg]

/-- **(16.30), conjugation, integer weight**: `λ_{χ̄,−k}(n) = conj (λ_{χ,k}(n))`. -/
lemma heckeLam_conj_int (chi : GaussianInt → ℂ) (k : ℤ) (n : ℕ) :
    Work.FIArea5.S16Hecke.heckeLam (fun z : GaussianInt => star (chi z)) (-k) n
      = star (Work.FIArea5.S16Hecke.heckeLam chi k n) := by
  simp only [Work.FIArea5.S16Hecke.heckeLam, Complex.star_def]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun z _ => psi_conj_int chi k z)

/-- **Conjugation of the Hecke `L`-series with integer weight.** -/
theorem heckeLSeries_conj_int (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) :
    Work.FIArea5.S16Hecke.heckeLSeries (fun z => star (chi z)) (-m) s
      = star (Work.FIArea5.S16Hecke.heckeLSeries chi m (star s)) := by
  rw [Work.FIArea5.S16Hecke.heckeLSeries, Work.FIArea5.S16Hecke.heckeLSeries,
    ← Work.FIArea5.S16Hecke.LSeries_conj (fun n => Work.FIArea5.S16Hecke.heckeLam chi m n) s]
  rw [funext (fun n => heckeLam_conj_int chi m n)]

end Work.FIArea6Hecke.R
