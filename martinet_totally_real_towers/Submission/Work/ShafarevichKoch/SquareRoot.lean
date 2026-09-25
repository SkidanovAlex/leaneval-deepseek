import Mathlib
import Submission.Work.ShafarevichKoch.Defs

/-!
# `Work.ShafarevichKoch.SquareRoot`

**Square roots are unique in the group of fractional ideals of a number field.**

The monoid of invertible fractional ideals of `𝓞 F` inside `F` is the free abelian group on the
nonzero prime ideals of `𝓞 F`; equivalently, a nonzero fractional ideal is determined by the
integers `FractionalIdeal.count F v I` (`v` ranging over the height-one primes).  Consequently the
map `I ↦ I * I` is injective.

This is the algebraic fact that makes the Kummer two-descent (`vClass` in `Defs.lean`) well
defined: a class `x ∈ V_∅` has a *unique* square root ideal, so its class in `Cl(F)` is
unambiguous.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped nonZeroDivisors
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **Squaring is injective on the group of fractional ideals of a number field.**
If two invertible fractional ideals have the same square, they are equal. -/
theorem squareRoot_unique (F : Type*) [Field F] [NumberField F]
    {J J' : IdealUnit F} (h : J * J = J' * J') : J = J' := by
  have hJ0 : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := Units.ne_zero J
  have hJ'0 : (J' : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := Units.ne_zero J'
  have hcount : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      FractionalIdeal.count F v (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
        = FractionalIdeal.count F v (J' : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    intro v
    have h1 := congrArg (fun I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F =>
      FractionalIdeal.count F v I) (congrArg (fun u : IdealUnit F =>
        (u : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) h)
    simp only [Units.val_mul] at h1
    rw [FractionalIdeal.count_mul F v hJ0 hJ0, FractionalIdeal.count_mul F v hJ'0 hJ'0] at h1
    linarith
  have hfac : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^
        FractionalIdeal.count F v (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      = (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
    FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := F) hJ0
  have hfac' : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^
        FractionalIdeal.count F v (J' : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      = (J' : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
    FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := F) hJ'0
  refine Units.ext ?_
  rw [← hfac, ← hfac']
  exact finprod_congr fun v => by rw [hcount v]

end Work.ShafarevichKoch
