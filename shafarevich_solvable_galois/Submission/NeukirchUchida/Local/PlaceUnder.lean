import Submission.NeukirchUchida.Local.DecompositionGroup
import Mathlib.RingTheory.Ideal.GoingUp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The place of an intermediate field below a given place

Let `M / K` be a finite extension of number fields and `L` an intermediate field.  Every finite
place `w` of `M` (a height one prime of `𝓞 M`) restricts to a finite place `w|_L` of `L`, obtained
by contracting the prime ideal `w.asIdeal` along `𝓞 L → 𝓞 M`.

This is the basic construction underlying the projective system of decomposition groups used in
the local-global bridge of the Neukirch–Uchida theorem: the decomposition group of `w` in
`Gal(M/K)` maps into the decomposition group of `w|_L` in `Gal(L/K)` (`LocalGalois`), and the
decomposition groups of the infinite extension are the projective limit of these.
-/

open scoped NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.NeukirchUchida.Local

variable {K M : Type*} [Field K] [Field M] [NumberField K] [NumberField M] [Algebra K M]
  [FiniteDimensional K M]

/-- The place of an intermediate field `L` of `M` lying below a place `w` of `M`: the contraction
of the prime ideal `w.asIdeal` along `𝓞 L → 𝓞 M`. -/
noncomputable def placeUnder (L : IntermediateField K M)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M)) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 L) where
  asIdeal := w.asIdeal.under (𝓞 L)
  isPrime := inferInstance
  ne_bot := Ideal.under_ne_bot (𝓞 L) w.ne_bot

@[simp]
theorem placeUnder_asIdeal (L : IntermediateField K M)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M)) :
    (placeUnder L w).asIdeal = w.asIdeal.under (𝓞 L) := rfl

theorem placeUnder_isPrime (L : IntermediateField K M)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M)) :
    (placeUnder L w).asIdeal.IsPrime := (placeUnder L w).isPrime

/-- If `w` lies over a place `p` of the base field `K`, then so does `w|_L`. -/
theorem liesOver_placeUnder (L : IntermediateField K M)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M))
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) [h : w.asIdeal.LiesOver p.asIdeal] :
    (placeUnder L w).asIdeal.LiesOver p.asIdeal := by
  refine ⟨?over⟩
  rw [placeUnder_asIdeal, Ideal.under_under (A := 𝓞 K) (B := 𝓞 L) w.asIdeal]
  exact h.over

end Submission.NeukirchUchida.Local
