import Mathlib
import Submission.Work.SSGRoute.ZDataMup.mupOddLevel
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.LocalFactor
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.SupStructure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer character of a global element, descended to a Kummer level

The global Kummer character `χ_β : Gal(Ω/↥K) → ZMod p` of `β ∈ ↥Kˣ` kills the fixing subgroup of
every level `M` containing the Kummer field `K(β^{1/p})` of `β`
(`LTRecFamHonest.kummerCharZMod_eq_zero_of_mem_fixingSubgroup`), hence descends to a group
homomorphism `χ_β : Gal(M/↥K) →* Multiplicative (ZMod p)` (`hChar`); that descent is pinned by its
values on the restrictions of elements of `Gal(Ω/↥K)` (`hChar_apply`).

The descended character is the first-variable factor of the pairing of `localTateSystem_productFormula_odd`:
the pairing value is `χ_{x̃}(θ^{K(x̃^{1/p})}_A(ỹ))`, where `θ^L_A = Φ_L ∘ onePlace_𝔭 ∘ localImageAt_𝔭`
is the local factor of the global abelian Artin map of the level `L`.  This file contains only the
character (the pairing itself is in `mupOddForm.lean`), so that lemmas about the level dependence of
the Artin factor can import it without a cycle.
-/

open scoped Pointwise NumberField

namespace Work.SSGRoute.ZDataMup.OddForm

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The Kummer character of `β` descended to a level `M ⊇ K(β^{1/p})`.** -/
noncomputable def hChar (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    {M : IntermediateField ↥K Ω} [FiniteDimensional ↥K M] [IsGalois ↥K M]
    (hKM : NK.LocalAnabelian.kummerField (K' := Ω) p β ≤ M) :
    (↥M ≃ₐ[↥K] ↥M) →* Multiplicative (ZMod p) :=
  Classical.choose (exists_levelCharacter (K := K) (p := p) ζ hζ β hKM)

/-- The defining property of the descended character. -/
theorem hChar_apply (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    {M : IntermediateField ↥K Ω} [FiniteDimensional ↥K M] [IsGalois ↥K M]
    (hKM : NK.LocalAnabelian.kummerField (K' := Ω) p β ≤ M) (σ : Ω ≃ₐ[↥K] Ω) :
    hChar (K := K) (p := p) ζ hζ β hKM
        ((AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M) σ) =
      Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β σ) :=
  Classical.choose_spec (exists_levelCharacter (K := K) (p := p) ζ hζ β hKM) σ

/-- The descended character is additive. -/
theorem hChar_add (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    {M : IntermediateField ↥K Ω} [FiniteDimensional ↥K M] [IsGalois ↥K M]
    (hKM : NK.LocalAnabelian.kummerField (K' := Ω) p β ≤ M)
    (a b : ↥M ≃ₐ[↥K] ↥M) :
    hChar (K := K) (p := p) ζ hζ β hKM (a * b) =
      hChar (K := K) (p := p) ζ hζ β hKM a * hChar (K := K) (p := p) ζ hζ β hKM b :=
  map_mul _ a b

end

end Work.SSGRoute.ZDataMup.OddForm
