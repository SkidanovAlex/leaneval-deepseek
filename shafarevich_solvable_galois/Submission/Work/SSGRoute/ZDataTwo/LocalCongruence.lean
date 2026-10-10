import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.GrunwaldEscapeCore.grunwald_escape_correction
import Submission.Work.SSGRoute.ZDataTwo.RealPlaceInvolution
import Submission.Work.SSGRoute.ges_readoff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local half of the sign adjustment (`p = 2`): congruence ⟹ local vanishing

The local congruence half of `Work.SSGRoute.ZDataTwo.signAdjustment_mu2`.  If the image of `s ∈ Kˣ`
in the completion at a prime `𝔭` of `↥K` is a **square** (which is what a congruence
`s ≡ 1 (mod 𝔭^N)`, `N` large as in `GrunwaldEscapeCore.exists_pow_eq_of_isCongAt`, produces), then
the `ZMod 2`-valued Kummer character of `s` vanishes on the whole local group
`decomp k A ⊓ K.fixingSubgroup` of the place `A` below `𝔭`.

The chain is exactly the banked one:

* "the completion image of `s` is a square" ⟹ "the completion image lies in
  `NK.UchidaKummer.ellPowSubgroup _ 2`" (which is by definition the range of the squaring map);
* ⟹ `localPowClass ↥K 2 𝔭 s = 1` by `Work.SSGRoute.localPowClass_eq_one_of_unit_component`;
* ⟹ the local vanishing by
  `Work.SSGRoute.GrunwaldEscapeCore.kummerChar_eq_zero_on_decomp_of_localPow` (which transports
  `Work.SSGRoute.local_kummer_dictionary` along `gesLocalToGalK`).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

/-- **A square completion image kills the local Kummer character.**  The local congruence half of
the `p = 2` sign adjustment, in the vocabulary of the completion. -/
theorem kummerCharZMod_eq_zero_of_isSquare_completion (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (s : (↥K)ˣ)
    (hs : ∃ c : (𝔭.adicCompletion ↥K)ˣ,
      c ^ 2 = Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom s)
    (σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ s
      (Work.SSGRoute.gesLocalToGalK K σ) = 0 := by
  classical
  -- the completion image of `s` lies in the group of squares
  have he : (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom s)⁻¹ ∈
      NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion ↥K) 2 := by
    obtain ⟨c, hc⟩ := hs
    exact Subgroup.inv_mem _ ⟨c, hc⟩
  -- hence its local `2`-power class is trivial
  have h1 : NK.UchidaKummer.localPowClass ↥K 2 𝔭 s = 1 :=
    Work.SSGRoute.localPowClass_eq_one_of_unit_component (p := 2) Nat.prime_two
      (𝔭 := 𝔭) (γ := s)
      (e := (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom s)⁻¹) he (by rw [inv_inv])
  -- and the local Kummer dictionary gives the vanishing
  exact Work.SSGRoute.GrunwaldEscapeCore.kummerChar_eq_zero_on_decomp_of_localPow k Ω K 2 ζ hζ
    A hA 𝔭 h𝔭 s h1 σ

end Work.SSGRoute.ZDataTwo
