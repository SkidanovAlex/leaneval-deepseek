import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.H9.swPinnedFrob_exists
import Submission.Work.SSGRoute.ZConstruction.hLevel_sup_structure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option maxHeartbeats 1000000

/-!
# Restriction of the pinned Frobenius to a Kummer sub-level

`Work.SSGRoute.H9.swPinnedFrob_exists` pins an element `ψ` of the local group
`decomp k A ⊓ K.fixingSubgroup` at a big level `Λ` (its image in `Gal(Λ/↥K)` is a Frobenius at the
prime `oddPrime K A hA` of `↥K` below `A`).  The §4(b) chain of Schmidt--Wingberg consumes the *same*
element pinned at several Kummer *sub-levels* `hLevel w = ↥K(w^{1/p})` at once (for the two diagonal
readings of the local pairing--value dictionary `Work.SSGRoute.H9.swPairingValueFrob` and for the
promotion at the last escape prime), so the `Λ`-pinning has to be restricted to such a sub-level.

The sub-level is presented as an intermediate field `M` of `↥Λ` together with its identification `e`
with `hLevel w`; `he` is the naturality of `e` (both inclusions into `Ω` agree).  The construction is

* `NK.CFTLib.exists_isFrobAtPrime_restrict` (restriction of a Frobenius is a Frobenius — no
  unramifiedness, no commutativity),
* `NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase` (transport along the `↥K`-algebra isomorphism `e`),
* the identification of `e.symm.trans (σ.trans e)` with the restriction of `ψ` to `hLevel w`
  (the naturality `he` plus `AlgEquiv.restrictNormalHom_apply`),
* `NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq` at the abelian unramified Kummer level `hLevel w`
  (using `hunr` and `Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isMulCommutative`).
-/

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest

namespace Work.SSGRoute.H9

/-- **Restriction of a pinned Frobenius at `Λ` to a Kummer sub-level `hLevel w`.** -/
theorem swPinnedFrob_sublevel (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (Λ : IntermediateField ↥K Ω) [FiniteDimensional ↥K Λ] [IsGalois ↥K Λ] [NumberField ↥Λ]
    (w : (↥K)ˣ) [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) w)]
    [Normal ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) w)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) w)]
    (M : IntermediateField ↥K ↥Λ) [FiniteDimensional ↥K ↥M] [NumberField ↥M] [Normal ↥K ↥M]
    (e : ↥M ≃ₐ[↥K] ↥(hLevel (Ω := Ω) (K := K) (p := p) w))
    (he : ∀ x : ↥M, (e x : Ω) = ((x : ↥Λ) : Ω))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) w))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA))
    (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup)
    (hpin : NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥Λ)
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
      (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) Λ
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, (Subgroup.mem_inf.mp hψ).2⟩))) :
    AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (hLevel (Ω := Ω) (K := K) (p := p) w)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, (Subgroup.mem_inf.mp hψ).2⟩)
      = NK.Chebotarev.frobAtPrime (K := ↥K)
          (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) w))
          (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) := by
  classical
  set ψK : K.fixingSubgroup := ⟨ψ, (Subgroup.mem_inf.mp hψ).2⟩ with hψK
  set ψhat : Ω ≃ₐ[↥K] Ω := (IntermediateField.fixingSubgroupEquiv K) ψK with hψhat
  set ψΛ : ↥Λ ≃ₐ[↥K] ↥Λ :=
    AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) Λ ψhat with hψΛ
  set σM : ↥M ≃ₐ[↥K] ↥M :=
    AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥Λ) M ψΛ with hσM
  have hgalW : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) w) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) w
  have hcommW : ∀ a b : ↥(hLevel (Ω := Ω) (K := K) (p := p) w) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) w), a * b = b * a :=
    hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) w
  -- the restriction of the `Λ`-pinning to `M`
  have hFrobM : NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥M)
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) σM :=
    NK.CFTLib.exists_isFrobAtPrime_restrict (K := ↥K) (L := ↥Λ) M hpin
  -- transport along `e`
  have hFrobW : NK.Chebotarev.IsFrobAtPrime (K := ↥K)
      (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) w))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
      (e.symm.trans (σM.trans e)) :=
    (NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase e σM
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)).mp hFrobM
  -- `e.symm.trans (σM.trans e)` is the restriction of `ψ` to `hLevel w`
  have hcoe : e.symm.trans (σM.trans e) =
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (hLevel (Ω := Ω) (K := K) (p := p) w) ψhat := by
    ext x
    rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply]
    rw [AlgEquiv.restrictNormalHom_apply (hLevel (Ω := Ω) (K := K) (p := p) w) ψhat x]
    rw [he (σM (e.symm x))]
    rw [hσM, AlgEquiv.restrictNormalHom_apply]
    rw [hψΛ, AlgEquiv.restrictNormalHom_apply]
    congr 1
    have h := he (e.symm x)
    rw [e.apply_symm_apply] at h
    exact h.symm
  rw [hcoe] at hFrobW
  exact ((NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommW
    (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
    (fun P hP => hunr P hP) _).mp hFrobW).symm
end Work.SSGRoute.H9
