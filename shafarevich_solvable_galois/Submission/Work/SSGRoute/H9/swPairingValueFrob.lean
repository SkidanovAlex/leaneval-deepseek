import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataMup.localFactor_unramified_eq_frob_pow
import Submission.Work.SSGRoute.ZDataMup.swZTwoPlaceReciprocity
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unramified pairing–value dictionary of the Schmidt–Wingberg §4 chain

The chain of Schmidt–Wingberg §4(b) (arXiv:math/9809211, p. 16 — see
`NOTE_H9_odd_kummer_core_state.md`) passes between *values of Kummer cochains at Frobenius
elements* and *local pairings*.  The dictionary which makes this possible is proved here:

* `swOTheta_frobAtPrime_pow` — at a prime `𝔮` where the Kummer level `K(α^{1/p})` is unramified,
  the local factor `oTheta α β 𝔮` is the `count_𝔮 β`-th power of the canonical Frobenius (this is
  `localFactor_unramified_eq_frob_pow` with the chosen Artin map `oddArtin`);
* `swPairingValueFrob` — consequently the local Kummer pairing of the Kummer cochains of `α` and
  `β` at a finite place `A` is `count_A(β)` times the value of the Kummer cochain of `α` at any
  Frobenius element pinned to the canonical Frobenius, provided the Kummer level of `α` is
  unramified at `A`.

This is the arithmetic content of Schmidt–Wingberg's condition (1) (`(z_i)_{P_i} ≡ Frob_{P_i}
mod H¹_nr`): the local class of `β` being that of a uniformiser modulo `H¹_nr` is exactly
`count_A β ≡ ±1 (mod p)`, so the pairing equals `±` the value at the Frobenius.

-/


open scoped Pointwise

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.OddForm
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-- The trivial action of `Gal(K|k)` on `ZMod p`. -/
instance instDistribMulActionZModTrivialH9 {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (p : ℕ)
    (K : IntermediateField k Ω) : DistribMulAction (K ≃ₐ[k] K) (ZMod p) where
  smul := fun _ x => x
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

/-- Compatibility of the trivial action with the `ZMod p`-module structure. -/
instance instSMulCommClassZModTrivialH9 {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (p : ℕ)
    (K : IntermediateField k Ω) : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p) where
  smul_comm := fun _ _ _ => rfl

/-- A monoid hom into `Multiplicative A`, read additively, sends powers to multiples. -/
lemma toAdd_zpow_hom {G A : Type} [Group G] [AddCommGroup A] (f : G →* Multiplicative A)
    (g : G) (n : ℤ) : (f (g ^ n)).toAdd = n • (f g).toAdd := by
  have hpow : ∀ k : ℕ, (f (g ^ k)).toAdd = k • (f g).toAdd := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, map_mul]
      change (f (g ^ j)).toAdd + (f g).toAdd = (j + 1) • (f g).toAdd
      rw [ih, succ_nsmul]
  rcases n with k | k
  · simpa using hpow k
  · rw [zpow_negSucc, map_inv]
    rw [show ((f (g ^ (k + 1)))⁻¹).toAdd = -((f (g ^ (k + 1))).toAdd) from rfl, hpow (k+1)]
    simp

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-- The unramified local factor dictionary. -/
theorem swOTheta_frobAtPrime_pow (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (α β : (↥K)ˣ)
    [FiniteDimensional ↥K (hLevel (Ω := Ω) (K := K) (p := p) α)]
    [IsGalois ↥K (hLevel (Ω := Ω) (K := K) (p := p) α)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) α)]
    (hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) α))
      (oddPrime (K := K) A hA)) :
    oTheta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ α β
        (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)) =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) α))
          (oddPrime (K := K) A hA) ^
        (FractionalIdeal.count ↥K (oddPrime (K := K) A hA)
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (β : ↥K))) := by
  have h := Work.SSGRoute.ZDataMup.localFactor_unramified_eq_frob_pow (K := ↥K)
    (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) α))
    (Φ := oddArtin (K := K) (hLevel (Ω := Ω) (K := K) (p := p) α)
      (hLevel_isMulCommutative (Ω := Ω) (K := K) ζ hζ α))
    (oddArtin_norm (K := K) (hLevel (Ω := Ω) (K := K) (p := p) α) _)
    (oddArtin_frob (K := K) (hLevel (Ω := Ω) (K := K) (p := p) α) _)
    (oddPrime (K := K) A hA) hunr β
  simpa only [oTheta, hLocalFactor] using h

/-- **The unramified pairing-value dictionary.** -/
theorem swPairingValueFrob (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (α β : (↥K)ˣ) (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ K.fixingSubgroup)
    [FiniteDimensional ↥K (hLevel (Ω := Ω) (K := K) (p := p) α)]
    [IsGalois ↥K (hLevel (Ω := Ω) (K := K) (p := p) α)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) α)]
    (hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) α))
      (oddPrime (K := K) A hA))
    (hpinning : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) (hLevel (Ω := Ω) (K := K) (p := p) α)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, hψ⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) α)) (oddPrime (K := K) A hA)) :
    oPairAt (K := K) (p := p) (k := k) (Ω := Ω)
        (ζ := (⟨ζ, hζK⟩ : ↥K)) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α) (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = (FractionalIdeal.count ↥K (oddPrime (K := K) A hA) (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (β : ↥K))) • Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α ψ := by
  classical
  haveI hfd : FiniteDimensional ↥K (hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α
  haveI hgal : IsGalois ↥K (hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α
  haveI hnf : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α
  have h1 : oPairAt (K := K) (p := p) (k := k) (Ω := Ω) (ζ := (⟨ζ, hζK⟩ : ↥K)) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α) (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) = oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) (A := A) (ζ := (⟨ζ, hζK⟩ : ↥K)) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) hA α β := by
    have ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α) := by
      intro g hg h hh
      rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ α g hg h hh]
      rfl
    have hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) := by
      intro g hg h hh
      rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ β g hg h hh]
      rfl
    exact oPair_toClass_eq_oPairGlob (K := K) (p := p) (k := k) (Ω := Ω)
      (ζ := (⟨ζ, hζK⟩ : ↥K)) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (hA := hA) _ _ α β ha
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ α) hb
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ β)
      (fun σ hσ => Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
        (hζ := hζ) (β := α) hσ)
      (fun σ hσ => Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
        (hζ := hζ) (β := β) hσ)
  have h2 : oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) (A := A) (ζ := (⟨ζ, hζK⟩ : ↥K)) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) hA α β = (hChar (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α (le_refl (hLevel (Ω := Ω) (K := K) (p := p) α)) (oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) (A := A)
      (ζ := (⟨ζ, hζK⟩ : ↥K)) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) hA α β)).toAdd :=
    oPairGlob_def (K := K) (p := p) (k := k) (Ω := Ω) (A := A) (ζ := (⟨ζ, hζK⟩ : ↥K))
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) hA α β
  have h3 : (hChar (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α (le_refl (hLevel (Ω := Ω) (K := K) (p := p) α)) (oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) (A := A)
      (ζ := (⟨ζ, hζK⟩ : ↥K)) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) hA α β)).toAdd = (hChar (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α (le_refl (hLevel (Ω := Ω) (K := K) (p := p) α)) (oTheta (K := K) (p := p) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α β (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)))).toAdd := by
    rw [oFactorGlob_eq_oTheta]
  have h4 : (hChar (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α (le_refl (hLevel (Ω := Ω) (K := K) (p := p) α)) (oTheta (K := K) (p := p) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α β (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)))).toAdd = (hChar (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α (le_refl (hLevel (Ω := Ω) (K := K) (p := p) α)) (NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) α)) (oddPrime (K := K) A hA) ^ FractionalIdeal.count ↥K (oddPrime (K := K) A hA) (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (β : ↥K)))).toAdd := by
    rw [swOTheta_frobAtPrime_pow (K := K) (p := p) (k := k) (Ω := Ω) A hA (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α β hunr]
  have h5 : (hChar (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α (le_refl (hLevel (Ω := Ω) (K := K) (p := p) α)) (NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) α)) (oddPrime (K := K) A hA) ^ FractionalIdeal.count ↥K (oddPrime (K := K) A hA) (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (β : ↥K)))).toAdd = (FractionalIdeal.count ↥K (oddPrime (K := K) A hA) (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (β : ↥K))) • Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α ψ := by
    rw [toAdd_zpow_hom (hChar (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α (le_refl (hLevel (Ω := Ω) (K := K) (p := p) α))) (NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) α)) (oddPrime (K := K) A hA)) (FractionalIdeal.count ↥K (oddPrime (K := K) A hA) (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (β : ↥K)))]
    congr 1
    rw [← hpinning, hChar_apply (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α (hKM := le_refl (hLevel (Ω := Ω) (K := K) (p := p) α))]
    exact (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := α) hψ).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

end Work.SSGRoute.H9
