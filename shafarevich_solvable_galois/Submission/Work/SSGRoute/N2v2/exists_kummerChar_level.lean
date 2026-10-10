import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.N2v2.kummerSplit_of_hsplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped IntermediateField

set_option linter.style.haveILetI false

namespace Work.SSGRoute.N2v2

/-- **The Kummer character of an element whose Kummer field lies in `M` descends to `Gal(M/↥K)`.**

If `KummerField c ≤ M` (for `c ∈ Kˣ`), the Kummer character `χ_c`, an additive `ZMod p`-valued
function on `Gal(Ω/↥K)`, vanishes on `M.fixingSubgroup`: an automorphism fixing `M` fixes the chosen
`p`-th root of `c`, and by `kummerCharZMod_eq_zero_iff_apply_sqrt` the character vanishes exactly on
the automorphisms fixing that root.  It therefore factors through the restriction map
`Gal(Ω/↥K) →* Gal(M/↥K)`, giving a multiplicative character `χ` of the finite group `Gal(M/↥K)`
with `χ (σ|_M) = ofAdd (χ_c σ)` for every `σ`.

This is the interface between the Kummer-theoretic computation (`χ_c` is evaluated at local
elements, and the antisymmetry of the local Kummer pairing is stated in terms of `χ_c`) and the
ideal--idèle dictionary of the reduction `char_eq_neg_localSum`, which is stated for a
multiplicative character of `Gal(M/↥K)`.

(The same statement exists as `Work.SSGRoute.ZConstruction.exists_levelCharacter`, in a module of
the `ZConstruction` lane; it is reproduced here because that module does not currently build.)
-/
theorem exists_kummerChar_level (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (c : (↥K)ˣ) (hc : NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ M) :
    ∃ χ : (↥M ≃ₐ[↥K] ↥M) →* Multiplicative (ZMod p),
      ∀ σ : Ω ≃ₐ[↥K] Ω,
        χ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ) =
          Multiplicative.ofAdd
            (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hsepK : IsSepClosure ↥K Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  have hαpow : (Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p c) ^ p = algebraMap ↥K Ω (c : ↥K) :=
    Work.SSGRoute.kummerSqrtZMod_pow (Ω := Ω) p c
  have hαmem : Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p c ∈
      NK.LocalAnabelian.kummerField (K' := Ω) p c := by
    rw [NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple p Fact.out hζ c hαpow]
    exact IntermediateField.mem_adjoin_simple_self _ _
  -- `χ_c` vanishes on `M.fixingSubgroup`
  have hkill : ∀ τ : Ω ≃ₐ[↥K] Ω, τ ∈ M.fixingSubgroup →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c τ = 0 := by
    intro τ hτ
    rw [Work.SSGRoute.ZDataMup.LocalUnramified.kummerCharZMod_eq_zero_iff_apply_sqrt p hζ c τ]
    exact (IntermediateField.mem_fixingSubgroup_iff M τ).mp hτ _ (hc hαmem)
  -- additivity in the group variable
  have hadd : ∀ σ τ : Ω ≃ₐ[↥K] Ω,
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c (σ * τ) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ +
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c τ :=
    fun σ τ => Work.SSGRoute.ZConstruction.kummerCharZMod_apply_mul ζ hζ c σ τ
  -- well-definedness on the cosets of `M.fixingSubgroup`
  have hcongr : ∀ {σ σ' : Ω ≃ₐ[↥K] Ω},
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ =
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ' →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ' := by
    intro σ σ' h
    have hτ : σ⁻¹ * σ' ∈ M.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker M, MonoidHom.mem_ker, map_mul, map_inv, h,
        inv_mul_cancel]
    have h2 : σ' = σ * (σ⁻¹ * σ') := by group
    rw [h2, hadd, hkill _ hτ, add_zero]
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M) :=
    AlgEquiv.restrictNormalHom_surjective (F := ↥K) (E := Ω) (K₁ := ↥M)
  refine ⟨MonoidHom.mk' (fun g => Multiplicative.ofAdd
    (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c
      (Classical.choose (hsurj g)))) ?_, fun σ => ?_⟩
  · intro g g'
    rw [← ofAdd_add, ← hadd]
    refine congrArg Multiplicative.ofAdd ?_
    exact hcongr (by
      rw [map_mul, Classical.choose_spec (hsurj g), Classical.choose_spec (hsurj g'),
        Classical.choose_spec (hsurj (g * g'))])
  · refine congrArg Multiplicative.ofAdd ?_
    exact hcongr (Classical.choose_spec
      (hsurj (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ)))

end Work.SSGRoute.N2v2
