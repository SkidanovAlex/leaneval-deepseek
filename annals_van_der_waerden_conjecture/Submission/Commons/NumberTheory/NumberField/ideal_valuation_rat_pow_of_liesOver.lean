import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.RamificationInertia.Ramification

open scoped NumberField
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

theorem ideal_valuation_rat_pow_of_liesOver {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)]
    (V : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hV : V.asIdeal.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v.asIdeal = Ideal.span ({(p : ℤ)} : Set ℤ))
    (x : ℚ) :
    V.valuation K (x : K) = (v.valuation ℚ x) ^ V.asIdeal.ramificationIdx ℤ := by
  have hV' : V.asIdeal.LiesOver v.asIdeal := by
    rw [hv]
    exact hV
  haveI : V.asIdeal.LiesOver v.asIdeal := hV'
  have hram : v.asIdeal.ramificationIdx' V.asIdeal = V.asIdeal.ramificationIdx ℤ :=
    Ideal.ramificationIdx'_eq_ramificationIdx (R := ℤ) (S := 𝓞 K) v.asIdeal V.asIdeal v.ne_bot
  have hval : (v.valuation ℚ x) ^ v.asIdeal.ramificationIdx' V.asIdeal =
      V.valuation K (algebraMap ℚ K x) := by
    simpa using (IsDedekindDomain.HeightOneSpectrum.valuation_liesOver (A := ℤ) (B := 𝓞 K)
      (L := K) v V x)
  rw [hram] at hval
  simp [hval]

end Commons.NumberTheory.NumberField