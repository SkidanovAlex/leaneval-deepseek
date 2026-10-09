import Mathlib
import Submission.Work.SSGRoute.ZDataMup.mupOddPairLin
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.ZDataMup.mupLocalForm
import Submission.Work.SSGRoute.ZConstruction.localKummerLift
import Submission.Work.SSGRoute.ZConstruction.kummerCharMonoidHom
import Submission.Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The pairing on local classes of Kummer characters is the pairing computed with global units

The local pairing `oPair` on the level-`K` local `H¹`-group at a finite place `A` is
well-defined on local `p`-th power classes of global units (`oPair_congr`).  Here we compute it
for the two local classes that arise from *global* cocycles `a`, `b` which are the Kummer
characters of global units `α`, `β ∈ ↥Kˣ`: the pairing is the one computed with the global
representatives `α`, `β` (`oPairGlob`).

The bridge is `LTRecFamHonest.localModelIso_toClass_eq_kummerCharMonoidHom`: the model
identification of the local class of `a` is the locally constant character attached to `α`.  Since
the local Kummer dictionary `mupKummerEquiv` intertwines the local `p`-th power class map with the
Kummer character map out of `↥Kˣ`, this identifies the two local `p`-th power classes.
-/

namespace Work.SSGRoute.ZDataMup.OddForm

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

section Aux

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
  {A : ValuationSubring Ω}

/-- The prime of `↥K` below `A`, in the normal form used by the Kummer dictionary
`mupKummerEquiv`: the two definitions agree definitionally. -/
theorem oddPrime_eq_primeOf (hA : SSGRoute.IsFinPlace k A) :
    oddPrime (K := K) A hA =
      Submission.NeukirchUchida.primeOf A
        (Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA) :=
  rfl

/-- **The local `p`-th power class is read off from the local Kummer character**: two global units
with the same level-`K` local Kummer character at `A` have the same local `p`-th power class. -/
theorem localPowClass_eq_of_kummerCharMonoidHom_eq (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hA : SSGRoute.IsFinPlace k A) (α β : (↥K)ˣ)
    (h : Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA α =
      Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA β) :
    NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) α =
      NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) β := by
  have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ :=
    Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA
  have h' : NK.UchidaKummer.localPowClass ↥K p
        (Submission.NeukirchUchida.primeOf A hAK) α =
      NK.UchidaKummer.localPowClass ↥K p
        (Submission.NeukirchUchida.primeOf A hAK) β := by
    refine (Work.SSGRoute.ZDataMup.mupKummerEquiv (p := p) (k := k) (Ω := Ω) (K := K)
      (ζ := ζ) (hζ := hζ) hA hAK).injective ?_
    rw [Work.SSGRoute.ZDataMup.mupKummerEquiv_apply_localPowClass,
      Work.SSGRoute.ZDataMup.mupKummerEquiv_apply_localPowClass, h]
  exact h'

/-- **The value formula** (a private copy of
`Work.SSGRoute.ZDataMup.LTRecFamHonest.localModelIso_toClass_eq_kummerCharMonoidHom`, kept here so
that this module does not have to import `LTRecFamHonest/LocalForm.lean`, whose cone contains
`ZConstruction/auxPairingGate_odd_aux`): a global cocycle `a` on `K.fixingSubgroup` which is the
Kummer character of `α ∈ Kˣ` has, at the place `A`, the same local character as `α`. -/
theorem localModelIso_toClass_eq_kummerCharMonoidHom_of_toClass (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hA : SSGRoute.IsFinPlace k A) (α : (↥K)ˣ)
    (a : (Ω ≃ₐ[k] Ω) → ZMod p)
    (ha : a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) K.fixingSubgroup)
    (hα : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      a σ = Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ α
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩)) :
    Work.SSGRoute.ZConstruction.localModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA
        (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a) =
      Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA α := by
  classical
  have h4 := (Classical.choose_spec (Work.SSGRoute.ZDataMup.mupH1locLcHoms (p := p) (k := k)
    (Ω := Ω) (K := K) A hA)).2.2.2 a ha
  refine Subtype.ext (MonoidHom.ext fun d => ?_)
  obtain ⟨g, rfl⟩ := (Work.SSGRoute.decompEquiv_fok k Ω K A).surjective d
  have hL : (Work.SSGRoute.ZConstruction.localModelIso (p := p) (k := k) (Ω := Ω) (K := K)
      (A := A) hA (Work.SSGRoute.toClass p k Ω K (ZMod p)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a)).1
        (Work.SSGRoute.decompEquiv_fok k Ω K A g) =
      Multiplicative.ofAdd (a (g : Ω ≃ₐ[k] Ω)) :=
    congrArg Multiplicative.ofAdd (h4 g)
  have hR : (Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
      (ζ := ζ) (hζ := hζ) (A := A) hA α).1 (Work.SSGRoute.decompEquiv_fok k Ω K A g) =
      Multiplicative.ofAdd (Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ α
        ((Work.SSGRoute.decompEquiv_fok k Ω K A g : Ω ≃ₐ[↥K] Ω))) := rfl
  rw [hL, hR]
  exact congrArg Multiplicative.ofAdd (hα (g : Ω ≃ₐ[k] Ω) g.2.2)

end Aux

theorem oPair_toClass_eq_oPairGlob {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) {A : ValuationSubring Ω}
    (hA : SSGRoute.IsFinPlace k A)
    (a b : (Ω ≃ₐ[k] Ω) → ZMod p) (α β : (↥K)ˣ)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup a)
    (hla : SSGRoute.IsLocConstOn K.fixingSubgroup a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup b)
    (hlb : SSGRoute.IsLocConstOn K.fixingSubgroup b)
    (hα : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      a σ = Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ α
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))
    (hβ : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      b σ = Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩)) :
    Work.SSGRoute.ZDataMup.OddForm.oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA
        (Work.SSGRoute.toClass p k Ω K (ZMod p)
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a)
        (Work.SSGRoute.toClass p k Ω K (ZMod p)
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b) =
      Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA
        α β := by
  classical
  have hα' : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) α =
      NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA)
        (hLift ζ hζ A hA
          (Work.SSGRoute.toClass p k Ω K (ZMod p)
            (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a)) := by
    refine localPowClass_eq_of_kummerCharMonoidHom_eq (K := K) (p := p) (k := k) (Ω := Ω)
      (A := A) ζ hζ hA α _ ?_
    rw [hLift_realises,
      localModelIso_toClass_eq_kummerCharMonoidHom_of_toClass (A := A) ζ hζ hA α a
        ⟨ha, hla⟩ hα]
  have hβ' : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) β =
      NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA)
        (hLift ζ hζ A hA
          (Work.SSGRoute.toClass p k Ω K (ZMod p)
            (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b)) := by
    refine localPowClass_eq_of_kummerCharMonoidHom_eq (K := K) (p := p) (k := k) (Ω := Ω)
      (A := A) ζ hζ hA β _ ?_
    rw [hLift_realises,
      localModelIso_toClass_eq_kummerCharMonoidHom_of_toClass (A := A) ζ hζ hA β b
        ⟨hb, hlb⟩ hβ]
  rw [oPairForm_apply]
  exact oPair_congr (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA _ _ α β hα' hβ'

end

end Work.SSGRoute.ZDataMup.OddForm
