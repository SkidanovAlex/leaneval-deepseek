import Mathlib
import Submission.Work.MotA.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotA

/-- Audit node **A2a**: the codimension-one points of affine `n`-space over a field are exactly
the points defined by a principal prime ideal.

The convention is fixed by `AlgebraicGeometry.idealHeight_eq_coheight (R) (x : Spec R) :
x.asIdeal.height = coheight x` (`Mathlib/AlgebraicGeometry/Properties.lean`): because the
specialization order on `Spec R` is the *reverse* of the inclusion order on prime ideals
(`AlgebraicGeometry.specOrderIsoPrimeSpectrum : Spec R ≃o (PrimeSpectrum R)ᵒᵈ`), `Order.coheight`
of a point is the *height* of the corresponding prime ideal.  In particular the generic point has
`coheight 0`, not `1`, and `coheight x = 1` says that `x.asIdeal` is a height-one prime.

Route.  In the UFD `MvPolynomial (Fin n) 𝕜` a nonzero prime ideal contains a prime element `p`
(`Ideal.IsPrime.exists_mem_prime`); `(p)` is a nonzero prime
(`Ideal.span_singleton_prime hp.ne_zero`) and has height one
(`Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors` with
`mem_nonZeroDivisors_iff_ne_zero.mpr hp.ne_zero` and `fun h => hp.not_isUnit h`); since
`(p) ≤ x.asIdeal` are both of height one, `x.asIdeal = (p)`
(`Ideal.eq_span_singleton_of_height_eq_one`).  Conversely, if `x.asIdeal = (p)` with `p` prime
then the same height computation gives `coheight x = 1`.  An analogous argument for `Fin 2` is in
`Submission/Work/CrauderKatz/BlowUp/exists_cInv_ne_zero_of_openImmersion_missingDivisor.lean`
(`eq_missingPoint_of_coheight_eq_one_of_notMem`). -/
theorem coheight_eq_one_iff (𝕜 : Type) [Field 𝕜] (n : ℕ) (x : polySpec 𝕜 n) :
    Order.coheight x = 1 ↔ ∃ p : MvPolynomial (Fin n) 𝕜, Prime p ∧ x.asIdeal = Ideal.span {p} := by
  constructor
  · intro h
    -- `x.asIdeal` is a height-one prime
    have hheight : x.asIdeal.height = 1 := by
      rw [AlgebraicGeometry.idealHeight_eq_coheight]
      exact h
    have hne : x.asIdeal ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hheight
    -- a nonzero prime ideal of a UFD contains a prime element
    obtain ⟨p, hpmem, hpprime⟩ :=
      Ideal.IsPrime.exists_mem_prime_of_ne_bot (I := x.asIdeal) x.isPrime hne
    exact ⟨p, hpprime,
      @Ideal.eq_span_singleton_of_height_eq_one _ _ _ x.asIdeal x.isPrime hheight p hpmem
        hpprime⟩
  · rintro ⟨p, hpprime, hx⟩
    rw [← AlgebraicGeometry.idealHeight_eq_coheight, hx]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hpprime.ne_zero)
      (fun hu => hpprime.not_isUnit hu)

end Work.MotA
