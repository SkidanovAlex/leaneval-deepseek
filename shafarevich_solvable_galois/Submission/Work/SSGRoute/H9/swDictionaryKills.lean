import Mathlib
import Submission.Work.SSGRoute.H9.swChainConjDefs
import Submission.Work.SSGRoute.H9.swPairingValueFrob
import Submission.Work.SSGRoute.H9.swOoPairAt_add_swap
import Submission.Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local dictionary of the §4(b) chain, with the unramifiedness discharged from a confinement

The two dictionary readings the chain of Schmidt--Wingberg §4(b) uses (steps `(d1)`,`(d2)`,`(d5)`,
`(d6)` of `H9/NOTE_chain_route_conjugates.md`) are `Work.SSGRoute.H9.swPairingValueFrob` and its
transpose.  In the chain, the hypothesis "the Kummer level of the *first* variable is unramified at
`A`" is not available as such: what the history supplies is the *confinement* — the Kummer cochain
kills the inertia at `A`.  The two lemmas below take the confinement and discharge the
unramifiedness with `Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia`.

The remaining input of each is the *pinning* of the Frobenius element `ψ` in the Kummer level of the
first variable (`IsFrobAtPrime`, supplied in the assembly by the level machinery of
`NodeS30/swLevel*.lean`).
-/

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup
open Work.SSGRoute.ZDataMup.OddForm

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-- **The local dictionary, from a confinement.**  If the Kummer cochain of `α` kills the inertia at
the finite place `A`, then the local pairing of the Kummer cochains of `α` and `β` at `A` is the
`A`-count of `β` times the value of `χ_α` at the pinned Frobenius `ψ`. -/
theorem swPairingValueFrob_of_kills {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (α β : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hkill : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k A u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α u = 0)
    (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ K.fixingSubgroup)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) α)]
    (hpin : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (hLevel (Ω := Ω) (K := K) (p := p) α)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, hψ⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) α))
        (oddPrime (K := K) A hA)) :
    oPairAt (K := K) (p := p) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K)
        (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = (FractionalIdeal.count ↥K (oddPrime (K := K) A hA)
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (β : ↥K))) • Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α ψ :=
  swPairingValueFrob (K := K) (p := p) (k := k) (Ω := Ω) A hA ζ hζ hζK α β ψ hψ
    (swIsUnramifiedIn_hLevel_of_kills_inertia (K := K) (p := p) ζ hζ hζK α A hA hkill) hpin

/-- **The local dictionary, transposed.**  If the Kummer cochain of the *second* variable `β` kills
the inertia at `A` (so that the Kummer level of `β` — the one that is *not* the one being paired —
is unramified there), then the local pairing of `χ_α` and `χ_β` at `A` is the negative of the
`A`-count of `α` times the value of `χ_β` at the pinned Frobenius `ψ`.

This is the form used for the steps `(d2)`,`(d6)`: at the escape prime `Q_i` the class `χ_{c_i}` is
*ramified*, so the dictionary cannot be read with `α = c_i`; one transposes with the antisymmetry of
the pairing (`H9.swOoPairAt_add_swap`) and reads the dictionary with the unramified variable. -/
theorem swPairingValueFrob_of_kills_swap {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    (hp : p ≠ 2) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (α β : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hkill : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k A u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β u = 0)
    (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ K.fixingSubgroup)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    (hpin : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (hLevel (Ω := Ω) (K := K) (p := p) β)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, hψ⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) β))
        (oddPrime (K := K) A hA)) :
    oPairAt (K := K) (p := p) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K)
        (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = - ((FractionalIdeal.count ↥K (oddPrime (K := K) A hA)
            (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
              (α : ↥K))) • Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β ψ) := by
  have hd := swPairingValueFrob_of_kills (K := K) (p := p) (k := k) (Ω := Ω)
    ζ hζ hζK β α A hA hkill ψ hψ hpin
  have has := swOoPairAt_add_swap (K := K) (p := p) (k := k) (Ω := Ω) hp
    (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
  rw [eq_neg_iff_add_eq_zero]
  rw [hd] at has
  exact has

end Work.SSGRoute.H9
