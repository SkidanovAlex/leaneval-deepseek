import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.levelK_kummerCharHom_dictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer map as a group homomorphism, and its kernel

`Work.SSGRoute.ZConstruction.kummerCharHom` is additive in `β` and kills `p`-th powers
(`kummerCharHom_mul`, `kummerCharHom_pow`), so `β ↦ χ_β` is a genuine *monoid homomorphism*

`kummerCharMonoidHom : Kˣ →* ↥(lcHoms p ↥(decomp (k := ↥K) A))`

(`kummerCharHom_mem_lcHoms` puts the values in `lcHoms`).  This packaging is what the
quotient/`IsFirstIsomorphism` machinery consumes: `ker kummerCharMonoidHom` is the subgroup of
`β` with trivial Kummer character, which is exactly the group `N_𝔭` of local `p`-th powers at the
prime `𝔭` of `K` below `A` (`kummerCharHom_eq_one_iff`).

Hence, with
* `exists_globalUnit_mul_pow_eq_of_local` (the localisation `Kˣ → κˣ ⧸ (κˣ)^p` is surjective) and
* `natCard_lcHoms_levelK_localGroup` (`|↥(lcHoms p ↥(decomp A))| = |κˣ ⧸ (κˣ)^p|`),

the induced map `κˣ ⧸ (κˣ)^p → ↥(lcHoms p ↥(decomp A))` is injective (its kernel is `N_𝔭`, by
`kummerCharHom_eq_one_iff`) between finite groups of equal cardinality, hence bijective: the
level-`K` local Kummer isomorphism.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} {A : ValuationSubring Ω}

/-- **The Kummer map `β ↦ χ_β` as a monoid homomorphism `Kˣ →* ↥(lcHoms p ↥(decomp A))`.** -/
noncomputable def kummerCharMonoidHom (hA : SSGRoute.IsFinPlace k A) :
    Kˣ →* ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
  MonoidHom.mk' (fun β => ⟨kummerCharHom p k Ω K ζ hζ A β, kummerCharHom_mem_lcHoms hA β⟩)
    (fun β β' => Subtype.ext (kummerCharHom_mul β β'))

theorem kummerCharMonoidHom_apply (hA : SSGRoute.IsFinPlace k A) (β : Kˣ)
    (g : ↥(SSGRoute.decomp (k := ↥K) A)) :
    ((kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA β) : ↥(SSGRoute.decomp (k := ↥K) A) →* Multiplicative (ZMod p)) g =
      kummerCharHom p k Ω K ζ hζ A β g := rfl

/-- **The kernel of the Kummer map is the group of local `p`-th powers.** -/
theorem kummerCharMonoidHom_eq_one_iff (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) (β : Kˣ) :
    kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA β = 1
      ↔ NK.UchidaKummer.localPowClass ↥K p 𝔭 β = 1 := by
  rw [← kummerCharHom_eq_one_iff (p := p) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA 𝔭 h𝔭 β]
  constructor
  · intro h
    exact Subtype.ext_iff.mp h
  · intro h
    exact Subtype.ext_iff.mpr h

end Work.SSGRoute.ZConstruction
