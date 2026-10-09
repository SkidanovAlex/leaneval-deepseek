import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.OrthL2KImports
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local images of elements with equal Kummer characters agree modulo `p`-th powers

If two global units `a`, `b` of `↥K` have the same Kummer character on the decomposition group
`decomp ↥K A` of a finite place `A` of `Ω`, then at the prime `𝔭` of `↥K` under `A` their local
images differ by a `p`-th power.

The proof is the local Kummer dictionary
(`Work.SSGRoute.ZConstruction.kummerCharHom_eq_one_iff`, the `MonoidHom`-valued form of
`Work.SSGRoute.local_kummer_dictionary`) applied to `a · b⁻¹`:

* the characters of `a` and `b` agree on `decomp ↥K A`, so the character of `a · b⁻¹` is trivial;
* by the local Kummer dictionary this says that `a · b⁻¹` is a local `p`-th power at `𝔭`, i.e.
  its local image `localImageAt (Place.ofFinite 𝔭) (a · b⁻¹)` lies in the range of the `p`-th power
  map — this is the very definition `NK.UchidaKummer.localPowClass` of the local `p`-power class;
* multiplying by `localImageAt (Place.ofFinite 𝔭) b` and using multiplicativity of `localImageAt`
  produces the `w : (𝔭.adicCompletion ↥K)ˣ` with `localImageAt a = localImageAt b * w ^ p`.
-/

namespace Work.GrunwaldEscapeCore

open scoped Pointwise

theorem exists_pow_eq_localImageAt_of_kummerChar_eq_on_decomp (p : ℕ) [Fact p.Prime]
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥K)
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (a b : (↥K)ˣ)
    (h : ∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp ↥K A →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a σ =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b σ) :
    ∃ w : (𝔭.adicCompletion ↥K)ˣ,
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a =
        NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) b * w ^ p := by
  classical
  -- `localImageAt` is multiplicative (it is `Units.map` of a monoid hom)
  have hmul : ∀ x y : (↥K)ˣ,
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) (x * y) =
        NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x *
          NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) y := by
    intro x y
    simp only [NK.CFTLib.IdeleHasse.localImageAt]
    exact map_mul _ x y
  have hinv : ∀ x : (↥K)ˣ,
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x⁻¹ =
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x)⁻¹ := by
    intro x
    simp only [NK.CFTLib.IdeleHasse.localImageAt]
    exact map_inv _ x
  -- the Kummer characters of `a` and `b` agree on the decomposition group
  have hchar : Work.SSGRoute.ZConstruction.kummerCharHom p k Ω K ζ hζ A a =
      Work.SSGRoute.ZConstruction.kummerCharHom p k Ω K ζ hζ A b := by
    ext σ
    exact congrArg Multiplicative.ofAdd (h (σ : Ω ≃ₐ[↥K] Ω) σ.2)
  -- the character of `1` is trivial (a `p`-th power)
  have hOne : Work.SSGRoute.ZConstruction.kummerCharHom p k Ω K ζ hζ A (1 : (↥K)ˣ) = 1 := by
    simpa using Work.SSGRoute.ZConstruction.kummerCharHom_pow (p := p) (k := k) (Ω := Ω)
      (K := K) (ζ := ζ) (hζ := hζ) (A := A) (1 : (↥K)ˣ)
  -- hence the character inverts
  have hCharInv : ∀ x : (↥K)ˣ,
      Work.SSGRoute.ZConstruction.kummerCharHom p k Ω K ζ hζ A x⁻¹ =
        (Work.SSGRoute.ZConstruction.kummerCharHom p k Ω K ζ hζ A x)⁻¹ := by
    intro x
    have hh := Work.SSGRoute.ZConstruction.kummerCharHom_mul (p := p) (k := k) (Ω := Ω)
      (K := K) (ζ := ζ) (hζ := hζ) (A := A) x x⁻¹
    rw [mul_inv_cancel, hOne] at hh
    exact eq_inv_of_mul_eq_one_right hh.symm
  -- so the character of `a · b⁻¹` is trivial on `decomp ↥K A`
  have hγ : Work.SSGRoute.ZConstruction.kummerCharHom p k Ω K ζ hζ A (a * b⁻¹) = 1 := by
    rw [Work.SSGRoute.ZConstruction.kummerCharHom_mul, hCharInv, hchar, mul_inv_cancel]
  -- the local Kummer dictionary: `a · b⁻¹` is a local `p`-th power at `𝔭`
  have hpowclass : NK.UchidaKummer.localPowClass ↥K p 𝔭 (a * b⁻¹) = 1 :=
    (Work.SSGRoute.ZConstruction.kummerCharHom_eq_one_iff (p := p) (k := k) (Ω := Ω) (K := K)
      (ζ := ζ) (hζ := hζ) (A := A) hA 𝔭 h𝔭 (a * b⁻¹)).mp hγ
  -- unpacking `localPowClass`: the local image of `a · b⁻¹` is a `p`-th power
  have hmem : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
        (a * b⁻¹) ∈
      (powMonoidHom p : ((𝔭.adicCompletion ↥K)ˣ →* (𝔭.adicCompletion ↥K)ˣ)).range := by
    have hh := hpowclass
    rw [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hh
    exact (QuotientGroup.eq_one_iff _).mp hh
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨w, ?_⟩
  have hw' : w ^ p = NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
      (a * b⁻¹) := hw
  rw [hw', hmul, hinv]
  rw [← mul_assoc, mul_comm (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
    (NK.GlobalCFT.Place.ofFinite 𝔭) b) (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
    (NK.GlobalCFT.Place.ofFinite 𝔭) a), mul_assoc, mul_inv_cancel, mul_one]

end Work.GrunwaldEscapeCore
