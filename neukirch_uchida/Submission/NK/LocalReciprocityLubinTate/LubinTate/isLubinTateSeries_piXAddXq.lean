import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Series

/-!
# The standard Lubin–Tate series `f(X) = πX + X^q`

Milne, *Class Field Theory*, Example 2.10(a): for a coefficient ring `A` (with `π : A`, `q : ℕ`) the
power series

`piXAddXq π q = π·X + X^q`

is a Lubin–Tate series, i.e. it has zero constant coefficient, linear coefficient `π`, and is
congruent to `X^q` modulo `π` (in positive degrees).  This file verifies the three defining
conditions by direct computation of its coefficients.

The hypothesis `2 ≤ q` is used only for the *linear* coefficient: for `q = 1` the series would be
`(π + 1)X`, whose linear coefficient is `π + 1 ≠ π` unless `1 = 0` in `A`.  The congruence
`f ≡ X^q (mod π)` holds for every `q`.

The universe binder `u` is introduced here because the target statement quantifies over `A : Type u`
— the module as it stood previously did not elaborate (`unknown universe level u`).
-/

namespace NK.LocalReciprocityLubinTate.LubinTate

open MvPowerSeries

universe u

/-- The coefficients of the standard Lubin–Tate series `πX + X^q`: the `k`-th coefficient is `π`
for `k = 1`, `1` for `k = q`, and `0` otherwise.  We record it in the form of a single identity,
`π * [k = 1] + [k = q]`, which is valid uniformly in `k` (and in particular also when `q = 1`). -/
theorem coeffX_piXAddXq {A : Type u} [CommRing A] (π : A) (q : ℕ) (k : ℕ) :
    coeffX k (piXAddXq π q) = π * (if k = 1 then 1 else 0) + (if k = q then 1 else 0) := by
  classical
  have h1 : (Finsupp.single (0 : Fin 1) k = Finsupp.single 0 1) ↔ k = 1 :=
    (Finsupp.single_injective (0 : Fin 1)).eq_iff
  have h2 : (Finsupp.single (0 : Fin 1) k = Finsupp.single 0 q) ↔ k = q :=
    (Finsupp.single_injective (0 : Fin 1)).eq_iff
  simp only [coeffX, piXAddXq, map_add, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_X_pow, MvPowerSeries.coeff_X, h1, h2]

/-- **The standard series `πX + X^q` is a Lubin–Tate series** (Milne, *CFT*, Example 2.10(a)). -/
theorem isLubinTateSeries_piXAddXq {A : Type u} [CommRing A] (π : A) (q : ℕ) (hq : 2 ≤ q) :
    NK.LocalReciprocityLubinTate.IsLubinTateSeries π q
      (NK.LocalReciprocityLubinTate.piXAddXq π q) := by
  have hcoeff := coeffX_piXAddXq (A := A) π q
  have h1q : ¬ ((1 : ℕ) = q) := by omega
  have h0q : ¬ ((0 : ℕ) = q) := by omega
  refine ⟨?_, ?_, fun n => ?_⟩
  · -- the constant coefficient: `hcoeff 0` says it is `π * 0 + 0 = 0`
    have hc : (piXAddXq π q).constantCoeff = coeffX 0 (piXAddXq π q) := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeffX, Finsupp.single_zero]
    rw [hc, hcoeff 0]
    simp [h0q]
  · -- the linear coefficient: `π * [1 = 1] + [1 = q] = π + 0 = π` because `q ≠ 1`
    rw [hcoeff 1]
    simp [h1q]
  · -- the congruence: `πX + X^q - X^q = πX` is divisible by `π`
    rw [hcoeff n, add_sub_cancel_right]
    exact Ideal.mem_span_singleton.mpr ⟨_, rfl⟩

end NK.LocalReciprocityLubinTate.LubinTate
