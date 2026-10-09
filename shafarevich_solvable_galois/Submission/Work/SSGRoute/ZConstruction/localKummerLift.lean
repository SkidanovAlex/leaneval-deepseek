import Mathlib
import Submission.Work.SSGRoute.ZDataMup.mupKummerDictionary
import Submission.Work.SSGRoute.ZDataMup.mupH1locLcHoms
import Submission.Work.SSGRoute.ZConstruction.localKummerHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The coherent lift of the local Kummer classes (step 1 of the wiring of gate (P))

For the gate `Work.SSGRoute.ZConstruction.auxPairingGate_odd` one has to choose, for every finite
place `A` of `Ω` over `k` and every class `x` in the level-`K` local `H¹`-group
`V_A = H1loc p k Ω K (ZMod p) (decomp k A ⊓ K.fixingSubgroup)`, a global lift `β x ∈ Kˣ` whose local
Kummer class at `A` is `x`.  Two properties are needed:

* each `β x` realises `x` at `A` (`kummerCharMonoidHom hA (β x) = localModelIso x`, i.e. the local
  Kummer character of `β x` is the character corresponding to `x`);
* the lifts are **coherent**: the Kummer character of `β (x + x') · (β x · β x')⁻¹` is trivial, i.e.
  `β (x + x')` and `β x · β x'` have the same local class at `A`.

Coherence is what makes the Kummer *levels* of the pairing construction multiply,
`K((β (x + x'))^{1/p})` differing from `K((β x · β x')^{1/p})` only by an extension which is locally
trivial at `A` (and hence invisible to the pairing, by step 4 of the wiring plan recorded in
`ZConstruction/auxPairingGate_odd.lean`).

The construction is the composition of the two on-disk Kummer dictionaries: the local Kummer
isomorphism `mupKummerDictionary` identifies `κ_Aˣ ⧸ (κ_Aˣ)^p` with the locally constant characters
of `decomp (k := ↥K) A`, `mupH1locLcHoms` identifies the latter with `V_A`, and
`localPowClass_surjective` lifts elements of `κ_Aˣ ⧸ (κ_Aˣ)^p` to `Kˣ`.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} {A : ValuationSubring Ω}

/-- **A finite place of `k` is a finite place of any intermediate field.**  `IsFinPlace` is
`A.comap (algebraMap · Ω) ≠ ⊤`, and the valuation is already non-trivial on `k ≤ K`. -/
theorem isFinPlace_of_isFinPlace_below (hA : SSGRoute.IsFinPlace k A) :
    A.comap (algebraMap ↥K Ω) ≠ ⊤ := by
  intro h
  apply hA
  have hval : ∀ x : ↥K, algebraMap ↥K Ω x ∈ A := by
    intro x
    have hx : x ∈ A.comap (algebraMap ↥K Ω) := by rw [h]; exact ValuationSubring.mem_top x
    rwa [ValuationSubring.mem_comap] at hx
  refine le_antisymm (ValuationSubring.le_top (A.comap (algebraMap k Ω))) ?_
  intro x _
  rw [ValuationSubring.mem_comap]
  simpa only [IsScalarTower.algebraMap_apply k ↥K Ω] using hval (algebraMap k ↥K x)

/-- **The model identification** `V_A ≅ ↥(lcHoms p ↥(decomp (k := ↥K) A))`: the level-`K` local
`H¹`-classes *are* the locally constant characters of the level-`K` local group
(`mupH1locLcHoms`), chosen once and for all. -/
noncomputable def localModelIso (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
      ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
  Classical.choose (Work.SSGRoute.ZDataMup.mupH1locLcHoms (p := p) (k := k) (Ω := Ω) (K := K)
    A hA)

/-- The chosen model identification is bijective. -/
theorem localModelIso_bijective (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Function.Bijective (localModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA) :=
  (Classical.choose_spec (Work.SSGRoute.ZDataMup.mupH1locLcHoms (p := p) (k := k) (Ω := Ω)
    (K := K) A hA)).1

/-- The chosen model identification is additive on `H¹` and multiplicative on characters. -/
theorem localModelIso_add (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (x y : Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    localModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA (x + y) =
      localModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x *
        localModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA y :=
  (Classical.choose_spec (Work.SSGRoute.ZDataMup.mupH1locLcHoms (p := p) (k := k) (Ω := Ω)
    (K := K) A hA)).2.1 x y

/-- The chosen model identification kills `0`. -/
theorem localModelIso_zero (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    localModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA 0 = 1 :=
  (Classical.choose_spec (Work.SSGRoute.ZDataMup.mupH1locLcHoms (p := p) (k := k) (Ω := Ω)
    (K := K) A hA)).2.2.1

/-- **The coherent lift of the level-`K` local Kummer classes.**  There is a choice, for every class
`x` in the level-`K` local `H¹`-group at `A`, of a global element `β x ∈ Kˣ` such that

* the local Kummer character of `β x` is the character of `x` (`kummerCharMonoidHom hA (β x) =
  localModelIso hA x`), and
* the lifts are coherent: `β (x + x') · (β x · β x')⁻¹` has trivial local Kummer character, i.e.
  `β (x + x')` and `β x · β x'` have the same local class at `A`.

The second clause is exactly what the pairing construction of step 2 of the wiring plan consumes:
the Kummer fields `K((β (x + x'))^{1/p})` and `K((β x · β x')^{1/p})` then differ by an extension
which is locally trivial at `A`. -/
theorem exists_localKummerLift (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    ∃ β : Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) → Kˣ,
      (∀ x, Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
          (ζ := ζ) (hζ := hζ) (A := A) hA (β x) =
        localModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x) ∧
      (∀ x x', Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
          (ζ := ζ) (hζ := hζ) (A := A) hA (β (x + x') * (β x * β x')⁻¹) = 1) := by
  classical
  have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ :=
    isFinPlace_of_isFinPlace_below (K := K) (A := A) hA
  -- the two dictionaries: `κ_Aˣ ⧸ (κ_Aˣ)^p ≃* ↥(lcHoms p (decomp A))` and the surjectivity of the
  -- local `p`-th power class map out of `Kˣ`
  obtain ⟨e, he⟩ := Work.SSGRoute.ZDataMup.mupKummerDictionary (p := p) (k := k) (Ω := Ω)
    (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA hAK
  have hsurj : Function.Surjective
      (NK.UchidaKummer.localPowClass ↥K p (Submission.NeukirchUchida.primeOf A hAK)) :=
    Work.SSGRoute.ZConstruction.localPowClass_surjective (p := p) (K := K)
      (Submission.NeukirchUchida.primeOf A hAK)
  -- the chosen lift, and the fact that it realises the local class
  let β : Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) → Kˣ :=
    fun x => Classical.choose (hsurj (e.symm (localModelIso (p := p) (k := k) (Ω := Ω) (K := K)
      (A := A) hA x)))
  have hβ : ∀ x, NK.UchidaKummer.localPowClass ↥K p (Submission.NeukirchUchida.primeOf A hAK)
      (β x) = e.symm (localModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x) :=
    fun x => Classical.choose_spec (hsurj (e.symm (localModelIso (p := p) (k := k) (Ω := Ω)
      (K := K) (A := A) hA x)))
  refine ⟨β, ?_, ?_⟩
  · intro x
    rw [← he (β x), hβ x, MulEquiv.apply_symm_apply]
  · intro x x'
    -- the two local classes agree, hence the Kummer character of the `p`-th power quotient is trivial
    have hclass : NK.UchidaKummer.localPowClass ↥K p (Submission.NeukirchUchida.primeOf A hAK)
        (β (x + x')) = NK.UchidaKummer.localPowClass ↥K p
          (Submission.NeukirchUchida.primeOf A hAK) (β x * β x') := by
      rw [hβ (x + x'), map_mul, hβ x, hβ x']
      exact (congrArg e.symm
        (localModelIso_add (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x x')).trans
        (map_mul e.symm _ _)
    have hEq : Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA (β (x + x')) =
        Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
          (ζ := ζ) (hζ := hζ) (A := A) hA (β x * β x') := by
      rw [← he (β (x + x')), ← he (β x * β x'), hclass]
    rw [map_mul, map_inv, hEq, mul_inv_cancel]

end

end Work.SSGRoute.ZConstruction
