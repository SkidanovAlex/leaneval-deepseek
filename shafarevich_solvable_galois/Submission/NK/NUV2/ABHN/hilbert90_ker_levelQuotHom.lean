import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RepresentationTheory.Rep.Basic
import Submission.NK.HassePrinciple.hilbert90_levelGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Hilbert 90 for the kernel of the level quotient map

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4, §10.4).

For a finite Galois level `L'` of `K'/K` the level group `LevelGroup ⊤ L'` acts on the units
`(↥L')ˣ` through the restriction `levelGroupRestrictHom ⊤ L' : LevelGroup ⊤ L' →* Gal(↥L'/K)`
(the representation `NK.HassePrinciple.unitsLevelRep`).  For `L ≤ L'` the quotient map
`levelQuotHom (U := ⊤) hh : LevelGroup ⊤ L' →* LevelGroup ⊤ L` has as kernel the image of
`Gal(K'/L)` in `LevelGroup ⊤ L'`, i.e. the Galois group of the extension `L'/L` (the "\(L'/L\)
part" of the level).

The theorem below is Hilbert 90 for that kernel: **every crossed homomorphism**
`α : ker (levelQuotHom ⊤ hh) → (↥L')ˣ` — written additively, since the representation is
transported along `Additive` — **is a coboundary**, `α a = ρ a y - y`.

The proof is the classical one, obtained by applying the general Noether/Hilbert 90
(`NK.HassePrinciple.hilbert90_injective`) to the composite of the kernel's inclusion with the
injective restriction map `levelGroupRestrictHom ⊤ L'`.  The only computational input is that
the `Additive` transport of the action is `Units.map` of the restriction
(`unitsLevelRep_ρ_ofMul`, definitional).
-/

namespace NK.NUV2.ABHN

open NK.BrauerHasse NK.HassePrinciple

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The action of the level group `LevelGroup V L` on the units `(↥L)ˣ`, computed on the `Additive`
transport used by `NK.HassePrinciple.unitsLevelRep`: it is `Units.map` of the restriction map
`levelGroupRestrictHom V L`.  This is the definitional computation rule for `unitsLevelRep` as a
`Rep.res` of `unitsRep`. -/
lemma unitsLevelRep_ρ_ofMul (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (g : LevelGroup V L) (x : (↥L)ˣ) :
    (unitsLevelRep V L).ρ g (Additive.ofMul x) =
      Additive.ofMul (Units.map ((levelGroupRestrictHom V L g : Gal(↥L/K)) : ↥L →* ↥L) x) := rfl

/-- **Hilbert 90 for the kernel of the level quotient map.**  Every crossed homomorphism from the
kernel of `levelQuotHom (U := ⊤) hh` to the units `(↥L')ˣ` of the larger level — for the action
given by the level group representation `unitsLevelRep (⊤) L'` — is a coboundary.

The crossed-homomorphism identity is stated additively (the representation lives on
`Additive (↥L')ˣ`), and correspondingly the conclusion is `α a = ρ a y - y`.

This is the input needed to run the classical Hilbert-90 argument on the `L'/L`-part of the level
group when comparing the units level system at two levels (`NK.NUV2.ABHN`). -/
theorem hilbert90_ker_levelQuotHom {K K' : Type} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] {L L' : FiniteGaloisIntermediateField K K'}
    (hh : (L : IntermediateField K K') ≤ (L' : IntermediateField K K'))
    (α : (NK.BrauerHasse.levelQuotHom (U := ⊤) hh).ker →
      (NK.HassePrinciple.unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L').V)
    (hα : ∀ a b : (NK.BrauerHasse.levelQuotHom (U := ⊤) hh).ker,
      α (a * b) = (NK.HassePrinciple.unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L').ρ
        (a : NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L') (α b) + α a) :
    ∃ y : (NK.HassePrinciple.unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L').V,
      ∀ a : (NK.BrauerHasse.levelQuotHom (U := ⊤) hh).ker,
        α a = (NK.HassePrinciple.unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L').ρ
          (a : NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L') y - y := by
  classical
  -- The `Additive` transport of the units of the large level, as an equivalence.
  let E : (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L').V ≃ (↥L')ˣ := Additive.toMul
  -- The group of the theorem: the kernel of the level quotient map.
  let N : Subgroup (LevelGroup (⊤ : Subgroup Gal(K'/K)) L') :=
    (levelQuotHom (U := ⊤) hh).ker
  have hfin : Finite ↥N := inferInstance
  -- The restriction of the kernel to `Gal(↥L'/K)`; it is injective because
  -- `levelGroupRestrictHom` is.
  let ψ : ↥N →* Gal(↥L'/K) :=
    (levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L').comp (Subgroup.subtype N)
  have hψinj : Function.Injective ψ :=
    (levelGroupRestrictHom_injective (⊤ : Subgroup Gal(K'/K)) L').comp Subtype.coe_injective
  -- `α` read as a crossed homomorphism with values in the units.
  let f : ↥N → (↥L')ˣ := fun a => E (α a)
  have hf : ∀ g h : ↥N, f (g * h) = Units.map (↑(ψ g) : ↥L' →* ↥L') (f h) * f g := by
    intro g h
    have h1 : α (g * h) = (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L').ρ
        (g : LevelGroup (⊤ : Subgroup Gal(K'/K)) L') (α h) + α g := hα g h
    have h2 : (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L').ρ
        (g : LevelGroup (⊤ : Subgroup Gal(K'/K)) L') (α h) =
        E.symm (Units.map (↑(ψ g) : ↥L' →* ↥L') (E (α h))) :=
      unitsLevelRep_ρ_ofMul (⊤ : Subgroup Gal(K'/K)) L'
        (g : LevelGroup (⊤ : Subgroup Gal(K'/K)) L') (E (α h))
    show E (α (g * h)) = Units.map (↑(ψ g) : ↥L' →* ↥L') (E (α h)) * E (α g)
    rw [h1, h2]
    rfl
  -- Noether's form of Hilbert 90 for the kernel.
  obtain ⟨x, hx⟩ := hilbert90_injective ψ hψinj f hf
  refine ⟨E.symm x, ?_⟩
  intro a
  have h := hx a
  have h2 : (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L').ρ
      (a : LevelGroup (⊤ : Subgroup Gal(K'/K)) L') (E.symm x) =
      E.symm (Units.map (↑(ψ a) : ↥L' →* ↥L') x) :=
    unitsLevelRep_ρ_ofMul (⊤ : Subgroup Gal(K'/K)) L'
      (a : LevelGroup (⊤ : Subgroup Gal(K'/K)) L') x
  show α a = (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L').ρ
      (a : LevelGroup (⊤ : Subgroup Gal(K'/K)) L') (E.symm x) - E.symm x
  rw [h2]
  apply E.injective
  rw [show E (α a) = f a from rfl, ← h]
  rfl

end NK.NUV2.ABHN
