import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.local_class_has_global_representative
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Surjectivity of the local reduction `Kˣ → κˣ ⧸ (κˣ)^p`

Every local `p`-th power class is the image of a global unit
(`exists_globalUnit_mul_pow_eq_of_local`, i.e. weak approximation at the completion), which says
exactly that `NK.UchidaKummer.localPowClass ↥K p 𝔭 : Kˣ →* κˣ ⧸ (κˣ)^p` is **surjective**.

Together with the kernel equivalence `ker (Kummer map) = ker (localPowClass)`
(`kummerChar_ker_le_localPowClass_ker` and `localPowClass_ker_le_kummerChar_ker`) this identifies
`Kˣ ⧸ ker ρ` with `κˣ ⧸ (κˣ)^p`, and hence — through the injective descent `kummerCharLift` — gives
the level-`K` local Kummer isomorphism.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} {A : ValuationSubring Ω}

/-- **The local reduction `Kˣ → κˣ ⧸ (κˣ)^p` is surjective.** -/
theorem localPowClass_surjective
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    Function.Surjective (NK.UchidaKummer.localPowClass ↥K p 𝔭) := by
  intro q
  -- lift the class to an element of `κˣ`
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective ((powMonoidHom p :
      (𝔭.adicCompletion ↥K)ˣ →* (𝔭.adicCompletion ↥K)ˣ).range) q
  -- a global representative of that local class
  obtain ⟨β, γ, hβγ⟩ := exists_globalUnit_mul_pow_eq_of_local (p := p) k Ω K 𝔭 a
  refine ⟨β, ?_⟩
  rw [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  -- name the two sides in the `mk'` spelling before rewriting
  show (QuotientGroup.mk' ((powMonoidHom p :
      (𝔭.adicCompletion ↥K)ˣ →* (𝔭.adicCompletion ↥K)ˣ).range))
        (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)) β)
      = (QuotientGroup.mk' ((powMonoidHom p :
      (𝔭.adicCompletion ↥K)ˣ →* (𝔭.adicCompletion ↥K)ˣ).range)) a
  -- `a` differs from the global unit by a `p`-th power
  have ha : a * (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)) β)⁻¹ = γ ^ p := by
    rw [← hβγ, mul_inv_eq_iff_eq_mul]
    exact mul_comm _ _
  have hmem : a * (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)) β)⁻¹ ∈
      (powMonoidHom p : (𝔭.adicCompletion ↥K)ˣ →* (𝔭.adicCompletion ↥K)ˣ).range := by
    rw [ha]
    exact MonoidHom.mem_range.mpr ⟨γ, rfl⟩
  -- so the two classes agree
  have h2 : (QuotientGroup.mk' ((powMonoidHom p :
      (𝔭.adicCompletion ↥K)ˣ →* (𝔭.adicCompletion ↥K)ˣ).range))
      (a * (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)) β)⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hmem
  rw [map_mul, map_inv] at h2
  exact (mul_inv_eq_one.mp h2).symm

end Work.SSGRoute.ZConstruction
