import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.kummerCharMonoidHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kernel inclusion for the descent of the Kummer map

`kernel of the local reduction modulo p-th powers ≤ kernel of the Kummer map`, i.e. the exact
hypothesis `h : N ≤ MonoidHom.ker f` of `QuotientGroup.lift` for building

`κˣ ⧸ (κˣ)^p →* ↥(lcHoms p ↥(decomp (k := ↥K) A))`.

It is `kummerCharMonoidHom_eq_one_iff` (the kernel of the Kummer map is the local `p`-th powers)
read as a statement about kernels; the reverse inclusion is the same equivalence, and together with
surjectivity of the reduction (`exists_globalUnit_mul_pow_eq_of_local`) they give that the induced
map is injective, hence -- with the equal cardinalities of
`natCard_lcHoms_levelK_localGroup` -- bijective.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} {A : ValuationSubring Ω}

/-- **Local `p`-th powers have trivial Kummer character**: the kernel inclusion consumed by
`QuotientGroup.lift` when descending the Kummer map to `κˣ ⧸ (κˣ)^p`. -/
theorem localPowClass_ker_le_kummerChar_ker (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) :
    MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭) ≤
      MonoidHom.ker (kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
        (hζ := hζ) (A := A) hA) := by
  intro β hβ
  rw [MonoidHom.mem_ker] at hβ ⊢
  exact (kummerCharMonoidHom_eq_one_iff (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
    (A := A) hA 𝔭 h𝔭 β).mpr hβ

/-- The reverse inclusion: a global unit with trivial Kummer character is a local `p`-th power. -/
theorem kummerChar_ker_le_localPowClass_ker (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) :
    MonoidHom.ker (kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
        (hζ := hζ) (A := A) hA) ≤
      MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭) := by
  intro β hβ
  rw [MonoidHom.mem_ker] at hβ ⊢
  exact (kummerCharMonoidHom_eq_one_iff (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
    (A := A) hA 𝔭 h𝔭 β).mp hβ

end Work.SSGRoute.ZConstruction
