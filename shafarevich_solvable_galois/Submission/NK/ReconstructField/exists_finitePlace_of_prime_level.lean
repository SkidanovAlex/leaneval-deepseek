import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.ReconstructField.Weak
import Submission.NK.ReconstructField.ncard_primesOver_levelMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Places of `K₁'` above a prime of a finite level

The extension-of-places statement for the reconstruction of Neukirch–Uchida
(`NK.Reconstruct.exists_place_of_prime_level`) produces, for a finite level `L ⊆ K₁'` of a
number field `K₁` and a nonzero prime `P` of `𝓞 L`, a valuation subring `A` of `K₁'` restricting
to the valuation ring `𝒪_{L,P}` on `L`.  What the reconstruction uses, however, is a place *over
a finite prime of `K₁`*: the trace of `A` on the base field `K₁` must be proper, i.e.
`A` must be a `FinitePlaceOf K₁ K₁'`.

That is the content of this file: a valuation subring of `K₁'` whose trace on a finite level is
the valuation ring of a nonzero prime is automatically proper on the base field.  Indeed, if `A`
contained the image of `K₁`, then — since `K₁'` is algebraic over `K₁` — the whole of `K₁'` would
lie in `A` (`Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top`),
contradicting the fact that the valuation ring of a nonzero prime is not everything.
-/

namespace NK.ReconstructField

/-- **Places of `K₁'` above a prime of a finite level, as places over a finite prime of `K₁`.**

For a finite level `L ⊆ K₁'` of a number field `K₁` (with `K₁'` a separable closure of `K₁`) and
a prime `P` of `𝓞 L`, there is a finite place of `K₁'` (i.e. a valuation subring whose trace on
`K₁` is proper) whose trace on `L` is the valuation ring `𝒪_{L,P}`. -/
theorem exists_finitePlace_of_prime_level
    {K₁ K₁' : Type*} [Field K₁] [Field K₁'] [NumberField K₁] [Algebra K₁ K₁']
    [IsSepClosure K₁ K₁'] (L : IntermediateField K₁ K₁') [NumberField ↥L]
    (P : NK.Chebotarev.PrimeIdeal ↥L) :
    ∃ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      A.1.comap (algebraMap ↥L K₁') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P := by
  -- extend the prime `P` of the level to a valuation subring of `K₁'`
  obtain ⟨A, hA⟩ := NK.Reconstruct.exists_place_of_prime_level (k := K₁) (K' := K₁') L P
  -- the trace on `K₁` is automatically proper: otherwise `A` would contain `K₁`, and since
  -- `K₁'` is algebraic over `K₁` the valuation would be trivial, contradicting `hA ≠ ⊤`
  refine ⟨⟨A, fun htop => ?_⟩, hA⟩
  have hAtop : A = ⊤ :=
    Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top A
      (IsSepClosure.separable (k := K₁) (K := K₁')).isAlgebraic htop
  have hLtop : A.comap (algebraMap ↥L K₁') = ⊤ := by
    rw [hAtop]
    ext x
    simp [ValuationSubring.mem_comap]
  exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top (K := ↥L) P
    (hA.symm.trans hLtop)

end NK.ReconstructField
