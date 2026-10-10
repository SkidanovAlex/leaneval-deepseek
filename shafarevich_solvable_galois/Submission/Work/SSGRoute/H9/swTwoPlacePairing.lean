import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.H9.swChainConjDefs
import Submission.Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia
import Submission.Work.SSGRoute.H9.swOoPairAt_add_swap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two-place product formula of the §4(b) chain, in confinement form

`Work.SSGRoute.ZDataMup.swZTwoPlaceReciprocity_of_Szero` states the localised product formula of the
odd-`p` Kummer pairing at the two escape classes, with the auxiliary place set `S` and the vanishing
of the `S`-terms as a hypothesis.  For the chain of Schmidt--Wingberg §4(b) the place set is *empty*
(the pairing of the two classes at the escape classes `Zi`, `ZN` is already supported there, since
each class kills the inertia outside its own escape class), so the `S`-terms are vacuous.  This file
packages that specialisation in the "confinement" form in which the chain consumes it:

    `⟨χ_α, χ_β⟩_{Zi} + ⟨χ_α, χ_β⟩_{ZN} = 0`

whenever `χ_α` (resp. `χ_β`) kills the inertia of every finite place which is not `K`-conjugate to
`Zi` (resp. `ZN`) — which is exactly the confinement clause of the recursion's history.
-/

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-- The `•`-spelling of level-`K` conjugacy of places (the spelling used by
`Work.SSGRoute.ZDataMup.swZTwoPlaceReciprocity_of_Szero`). -/
theorem gesKConj_iff_smul_form {K : IntermediateField k Ω} (A B : ValuationSubring Ω) :
    Work.SSGRoute.gesKConj K A B ↔
      ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A := by
  constructor
  · rintro ⟨τ, hτ, hτA⟩
    exact ⟨τ, hτ, fun x => by
      rw [← hτA, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]⟩
  · rintro ⟨τ, hτ, h⟩
    refine ⟨τ, hτ, SetLike.ext fun x => ?_⟩
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    exact (h x).symm

/-- **The two-place product formula of the §4(b) chain in confinement form.**  If each of the two
Kummer classes kills the inertia outside its own escape class, then the sum of the two local pairings
at the two escape classes vanishes.  This is `swZTwoPlaceReciprocity_of_Szero` with the auxiliary set
`S` empty (all its terms vacuous), specialised to the two Kummer cochains `χ_α`, `χ_β`. -/
theorem swTwoPlacePairing_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (α β : (↥K)ˣ)
    (Zi ZN : ValuationSubring Ω) (hZi : SSGRoute.IsFinPlace k Zi) (hZN : SSGRoute.IsFinPlace k ZN)
    (hZiN : ¬ Work.SSGRoute.gesKConj K Zi ZN)
    (hconfα : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Zi B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α u = 0)
    (hconfβ : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K ZN B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β u = 0) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := p) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        Zi hZi (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      + Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := p) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        ZN hZN (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) = 0 := by
  classical
  set ζ' : ↥K := ⟨ζ, hζK⟩ with hζ'def
  have hζ' : IsPrimitiveRoot ζ' p :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  have hacoc : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α) := by
    intro g hg h hh
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ α g hg h hh]
    rfl
  have hbcoc : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) := by
    intro g hg h hh
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ β g hg h hh]
    rfl
  refine Work.SSGRoute.ZDataMup.swZTwoPlaceReciprocity_of_Szero (K := K) (p := p) hp ζ' hζ'
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) α β hacoc
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ α) hbcoc
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ β)
    (fun σ hσ => Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := α) hσ)
    (fun σ hσ => Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := β) hσ)
    ∅ (by intro A hA; exact absurd hA (Finset.notMem_empty A))
    (by intro A hA; exact absurd hA (Finset.notMem_empty A))
    Zi ZN hZi hZN
    (by intro A hA; exact absurd hA (Finset.notMem_empty A))
    (by intro A hA; exact absurd hA (Finset.notMem_empty A))
    (fun h => hZiN (gesKConj_symm'' (A := ZN) (B := Zi)
      ((gesKConj_iff_smul_form (K := K) ZN Zi).mpr h)))
    (fun B hB _ hZi hZN u hu =>
      ⟨hconfα B hB (fun hc => hZi ((gesKConj_iff_smul_form (K := K) Zi B).mp hc)) u hu,
        hconfβ B hB (fun hc => hZN ((gesKConj_iff_smul_form (K := K) ZN B).mp hc)) u hu⟩)
    (by intro A hA; exact absurd hA (Finset.notMem_empty A))

end Work.SSGRoute.H9
