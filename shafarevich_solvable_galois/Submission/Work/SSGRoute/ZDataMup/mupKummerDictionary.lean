import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.finite_lcHoms_levelK_localGroup
import Submission.Work.SSGRoute.ZConstruction.localKummerHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-`K` local Kummer dictionary

At a finite place `A` of `Ω` over `k` (with `ζ_p ∈ K`), the level-`K` local Kummer map

  `localKummerHom : κˣ ⧸ (κˣ)^p ⟶ ↥(lcHoms p ↥(decomp (k := ↥K) A))`,   `κ = 𝔭.adicCompletion ↥K`,
  `𝔭 = primeOf A hAK`,

is injective (`ZConstruction.localKummerHom_injective`) and both sides are finite of equal
cardinality (`natCard_lcHoms_levelK_localGroup`, `finite_lcHoms_levelK_localGroup`); hence it is
**bijective**.  This is one half of the level-`K` local Kummer dictionary consumed by the wiring of
the `μ_p` local Tate system (see `NOTES_mup_wiring_session6.md`).

The remaining half — the compatibility `localKummerHom (localPowClass ↥K p 𝔭 β) =
kummerCharMonoidHom β` with the maps out of `Kˣ`, which gives the isomorphism in the form used by
the wiring — is the next target of this module.
-/

namespace Work.SSGRoute.ZDataMup

open _root_.SSGRoute

noncomputable section

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} {A : ValuationSubring Ω} [IsSepClosure ↥K Ω]

/-- **The level-`K` local Kummer map is bijective** at the canonical prime `𝔭 = primeOf A hAK`:
injective by `localKummerHom_injective`, and the source and target are finite of equal
cardinality (`natCard_lcHoms_levelK_localGroup`), so injective implies bijective. -/
theorem localKummerHom_bijective (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    Function.Bijective (Work.SSGRoute.ZConstruction.localKummerHom (p := p) (k := k) (Ω := Ω)
      (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA
      (Submission.NeukirchUchida.primeOf A hAK)
      (Submission.NeukirchUchida.primeOf_spec A hAK)) := by
  classical
  let F' := Work.SSGRoute.ZConstruction.localKummerHom (p := p) (k := k) (Ω := Ω)
    (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA
    (Submission.NeukirchUchida.primeOf A hAK)
    (Submission.NeukirchUchida.primeOf_spec A hAK)
  have hinj : Function.Injective F' :=
    Work.SSGRoute.ZConstruction.localKummerHom_injective (p := p) (k := k) (Ω := Ω)
      (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA
      (Submission.NeukirchUchida.primeOf A hAK)
      (Submission.NeukirchUchida.primeOf_spec A hAK)
  haveI hfinY : Finite ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
    Work.SSGRoute.ZConstruction.finite_lcHoms_levelK_localGroup (p := p) (k := k) (Ω := Ω)
      (K := K) hA hAK hAK
  have hcard := Work.SSGRoute.ZConstruction.natCard_lcHoms_levelK_localGroup (p := p) (k := k)
    (Ω := Ω) (K := K) A hA hAK hAK
  haveI hfinX : Finite
      (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
        (powMonoidHom p :
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range) :=
    Work.SSGRoute.finite_powClass_localField
      ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K) p Fact.out
  haveI : Fintype
      (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
        (powMonoidHom p :
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range) := Fintype.ofFinite _
  haveI : Fintype ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) := Fintype.ofFinite _
  have hcardF : Fintype.card
        (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
          (powMonoidHom p :
            ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
            ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range)
      = Fintype.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard.symm
  have hsurj : Function.Surjective F' := by
    let e : (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
        (powMonoidHom p :
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range) ≃
        ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
      Fintype.equivOfCardEq hcardF
    have hinj2 : Function.Injective (fun x => e.symm (F' x)) :=
      fun a b h => hinj (e.symm.injective h)
    have hsurj2 : Function.Surjective (fun x => e.symm (F' x)) :=
      Finite.surjective_of_injective hinj2
    intro y
    obtain ⟨x, hx⟩ := hsurj2 (e.symm y)
    exact ⟨x, by simpa using congrArg e hx⟩
  exact ⟨hinj, hsurj⟩

/-- **An injective map between finite types of equal cardinality is bijective.** -/
private theorem bijective_of_injective_of_card {X Y : Type*} [Finite X] [Finite Y] (f : X → Y)
    (hinj : Function.Injective f) (hcard : Nat.card X = Nat.card Y) : Function.Bijective f := by
  haveI := Fintype.ofFinite X
  haveI := Fintype.ofFinite Y
  have hcardF : Fintype.card X = Fintype.card Y := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  let e : X ≃ Y := Fintype.equivOfCardEq hcardF
  have hinj2 : Function.Injective (fun x => e.symm (f x)) := fun a b h => hinj (e.symm.injective h)
  have hsurj2 : Function.Surjective (fun x => e.symm (f x)) :=
    Finite.surjective_of_injective hinj2
  refine ⟨hinj, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hsurj2 (e.symm y)
  exact ⟨x, by simpa using congrArg e hx⟩

/-- **The local `p`-th power class group of the completion is `Kˣ ⧸ ker ρ`**, i.e. the first
isomorphism theorem for `ρ = localPowClass` in the direction used here: the inverse of the
surjectivity isomorphism.  Its computation on the class of `β` is
`mupKerEquiv_apply_localPowClass` below, and it reduces to `QuotientGroup.kerLift_mk`. -/
noncomputable def mupKerEquiv (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
        (powMonoidHom p :
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range) ≃*
      (Kˣ ⧸ MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p
        (Submission.NeukirchUchida.primeOf A hAK))) :=
  (QuotientGroup.quotientKerEquivOfSurjective
    (φ := NK.UchidaKummer.localPowClass ↥K p (Submission.NeukirchUchida.primeOf A hAK))
    (Work.SSGRoute.ZConstruction.localPowClass_surjective (p := p) (K := K)
      (Submission.NeukirchUchida.primeOf A hAK))).symm

/-- **The value of `mupKerEquiv` on a local `p`-th power class.** -/
theorem mupKerEquiv_apply_localPowClass (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) (β : Kˣ) :
    mupKerEquiv (p := p) (K := K) hAK
        (NK.UchidaKummer.localPowClass ↥K p (Submission.NeukirchUchida.primeOf A hAK) β) =
      QuotientGroup.mk' (MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p
        (Submission.NeukirchUchida.primeOf A hAK))) β := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective
        (φ := NK.UchidaKummer.localPowClass ↥K p (Submission.NeukirchUchida.primeOf A hAK))
        (Work.SSGRoute.ZConstruction.localPowClass_surjective (p := p) (K := K)
          (Submission.NeukirchUchida.primeOf A hAK)))
        (QuotientGroup.mk' (MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p
          (Submission.NeukirchUchida.primeOf A hAK))) β)
      = NK.UchidaKummer.localPowClass ↥K p (Submission.NeukirchUchida.primeOf A hAK) β :=
    QuotientGroup.kerLift_mk
      (φ := NK.UchidaKummer.localPowClass ↥K p (Submission.NeukirchUchida.primeOf A hAK)) β
  rw [mupKerEquiv, ← h1]
  exact MulEquiv.symm_apply_apply _ _

/-- **The level-`K` local Kummer map** `κˣ ⧸ (κˣ)^p →* ↥(lcHoms p ↥(decomp (k := ↥K) A))`, built
from the universal property of the quotient: identify `κˣ ⧸ (κˣ)^p` with `Kˣ ⧸ ker ρ` (surjectivity
of `ρ`) and descend the Kummer character map `Kˣ →* lcHoms` (whose kernel is `ker ρ`).  By
construction its value on the local class of `β` is the Kummer character of `β`
(`mupKummerLift_localPowClass`), which is the compatibility the wiring consumes. -/
noncomputable def mupKummerLift (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
        (powMonoidHom p :
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range) →*
      ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
  (Work.SSGRoute.ZConstruction.kummerCharLift (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
      (hζ := hζ) (A := A) hA (Submission.NeukirchUchida.primeOf A hAK)
      (Submission.NeukirchUchida.primeOf_spec A hAK)).comp
    (mupKerEquiv (p := p) (K := K) hAK).toMonoidHom

/-- **The level-`K` Kummer dictionary is compatible with the maps out of `Kˣ`.** -/
theorem mupKummerLift_localPowClass (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) (β : Kˣ) :
    mupKummerLift (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) hA hAK
        (NK.UchidaKummer.localPowClass ↥K p (Submission.NeukirchUchida.primeOf A hAK) β) =
      Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA β := by
  calc mupKummerLift (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) hA hAK
        (NK.UchidaKummer.localPowClass ↥K p (Submission.NeukirchUchida.primeOf A hAK) β)
      = Work.SSGRoute.ZConstruction.kummerCharLift (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
          (hζ := hζ) (A := A) hA (Submission.NeukirchUchida.primeOf A hAK)
          (Submission.NeukirchUchida.primeOf_spec A hAK)
          ((mupKerEquiv (p := p) (K := K) hAK)
            (NK.UchidaKummer.localPowClass ↥K p
              (Submission.NeukirchUchida.primeOf A hAK) β)) := rfl
    _ = Work.SSGRoute.ZConstruction.kummerCharLift (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
          (hζ := hζ) (A := A) hA (Submission.NeukirchUchida.primeOf A hAK)
          (Submission.NeukirchUchida.primeOf_spec A hAK)
          (QuotientGroup.mk' (MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p
            (Submission.NeukirchUchida.primeOf A hAK))) β) := by
        rw [mupKerEquiv_apply_localPowClass]
    _ = Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
          (ζ := ζ) (hζ := hζ) (A := A) hA β :=
        Work.SSGRoute.ZConstruction.kummerCharLift_mk (p := p) (k := k) (Ω := Ω) (K := K)
          (ζ := ζ) (hζ := hζ) (A := A) hA (Submission.NeukirchUchida.primeOf A hAK)
          (Submission.NeukirchUchida.primeOf_spec A hAK) β

/-- **The level-`K` local Kummer map is injective**: it is the composite of the isomorphism
`κˣ ⧸ (κˣ)^p ≃* Kˣ ⧸ ker ρ` with the injective descent `kummerCharLift`. -/
theorem mupKummerLift_injective (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    Function.Injective (mupKummerLift (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
      hA hAK) := by
  intro x y hxy
  have hxy' : Work.SSGRoute.ZConstruction.kummerCharLift (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA (Submission.NeukirchUchida.primeOf A hAK)
        (Submission.NeukirchUchida.primeOf_spec A hAK) ((mupKerEquiv (p := p) (K := K) hAK) x)
      = Work.SSGRoute.ZConstruction.kummerCharLift (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA (Submission.NeukirchUchida.primeOf A hAK)
        (Submission.NeukirchUchida.primeOf_spec A hAK) ((mupKerEquiv (p := p) (K := K) hAK) y) :=
    hxy
  have h1 := (Work.SSGRoute.ZConstruction.kummerCharLift_injective (p := p) (k := k) (Ω := Ω)
    (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA (Submission.NeukirchUchida.primeOf A hAK)
    (Submission.NeukirchUchida.primeOf_spec A hAK)) hxy'
  exact (mupKerEquiv (p := p) (K := K) hAK).injective h1

/-- **The level-`K` local Kummer dictionary**, in the form consumed by the wiring of the `μ_p`
local Tate system: an isomorphism `κˣ ⧸ (κˣ)^p ≃* ↥(lcHoms p ↥(decomp (k := ↥K) A))`
intertwining the local `p`-th power class map with the Kummer character map out of `Kˣ`. -/
theorem mupKummerDictionary (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    ∃ e : (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
            (powMonoidHom p :
              ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
              ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range) ≃*
          ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)),
      ∀ β : Kˣ,
        e (NK.UchidaKummer.localPowClass ↥K p (Submission.NeukirchUchida.primeOf A hAK) β) =
          Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
            (ζ := ζ) (hζ := hζ) (A := A) hA β := by
  classical
  haveI hfinX : Finite
      (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
        (powMonoidHom p :
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range) :=
    Work.SSGRoute.finite_powClass_localField
      ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K) p Fact.out
  haveI hfinY : Finite ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
    Work.SSGRoute.ZConstruction.finite_lcHoms_levelK_localGroup (p := p) (k := k) (Ω := Ω)
      (K := K) hA hAK hAK
  have hcard : Nat.card
        (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
          (powMonoidHom p :
            ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
            ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range)
      = Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
    (Work.SSGRoute.ZConstruction.natCard_lcHoms_levelK_localGroup (p := p) (k := k) (Ω := Ω)
      (K := K) A hA hAK hAK).symm
  exact ⟨MulEquiv.ofBijective _ (bijective_of_injective_of_card _
      (mupKummerLift_injective (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) hA hAK)
      hcard),
    fun β => mupKummerLift_localPowClass (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
      (hζ := hζ) hA hAK β⟩

/-- **The level-`K` local Kummer dictionary**, chosen once and for all: the isomorphism
`κˣ ⧸ (κˣ)^p ≃* ↥(lcHoms p ↥(decomp (k := ↥K) A))` commuting with the maps out of `Kˣ`
(`mupKummerEquiv_apply_localPowClass`). -/
noncomputable def mupKummerEquiv (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
        (powMonoidHom p :
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
          ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range) ≃*
      ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
  Classical.choose (mupKummerDictionary (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
    (hζ := hζ) hA hAK)

/-- **The computation rule of the chosen dictionary.** -/
theorem mupKummerEquiv_apply_localPowClass (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) (β : Kˣ) :
    mupKummerEquiv (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) hA hAK
        (NK.UchidaKummer.localPowClass ↥K p (Submission.NeukirchUchida.primeOf A hAK) β) =
      Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA β :=
  Classical.choose_spec (mupKummerDictionary (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
    (hζ := hζ) hA hAK) β

end

end Work.SSGRoute.ZDataMup
