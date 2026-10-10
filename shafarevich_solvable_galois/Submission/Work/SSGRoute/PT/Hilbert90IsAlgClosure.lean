import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.AbsoluteKummer
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.Work.SSGRoute.PT.H1Transfer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Hilbert 90 over an arbitrary algebraic closure, and the `Gal(E/F)`-action on `Additive Eˣ`

`Submission.hilbert90_H1_eq_zero` proves `H¹(Gal(k̄/k), k̄ˣ) = 0` for the concrete type
`AlgebraicClosure k`.  The class-formation axiom 1.1a of Milne, *ADT*, is needed for
`Gal(Ω/L)` where `Ω` is an arbitrary algebraic closure of `L` (the `Ω` of the workspace's
`localTatePairing_deg02` is only required to satisfy `IsAlgClosure k Ω`).

Two ingredients:

* `instDistribMulActionAddUnitsOfField` — the action of `Gal(E/F)` on the additive group
  `Additive Eˣ`, so that `Work.AbsoluteKummer.H1` can be formed.  The workspace only has the
  instance for the fixed type `AlgebraicClosure k`
  (`Work.AbsoluteKummer.instDistribMulActionAddUnits`), so this one is declared at **lower
  priority** to leave that instance untouched wherever it applies.
* `hilbert90_H1_eq_zero_of_isAlgClosure` — the transport of `H¹_eq_zero` from
  `AlgebraicClosure F` to `Ω` along the homeomorphic isomorphism
  `AlgEquiv.autCongr (IsAlgClosure.equiv F (AlgebraicClosure F) Ω)` of Galois groups, using the
  group-transfer `Work.SSGRoute.PT.h1Transfer`.
-/

open scoped Classical
open Work.AbsoluteKummer

namespace Work.SSGRoute.PT

noncomputable section

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

/-- The action of a field automorphism on the units, in the general form needed for an arbitrary
algebraic closure (`Work.AbsoluteKummer.algEquivUnitsMap` is the `AlgebraicClosure k` version). -/
def algEquivUnitsMapOfField (σ : E ≃ₐ[F] E) : (Units E) →* (Units E) :=
  Units.map σ.toAlgHom.toRingHom.toMonoidWithZeroHom

@[simp] theorem algEquivUnitsMapOfField_coe (σ : E ≃ₐ[F] E) (u : Units E) :
    ((algEquivUnitsMapOfField F E σ u : Units E) : E) = σ (u : E) := rfl

@[simp] theorem algEquivUnitsMapOfField_mul (σ τ : E ≃ₐ[F] E) (u : Units E) :
    algEquivUnitsMapOfField F E σ (algEquivUnitsMapOfField F E τ u) =
      algEquivUnitsMapOfField F E (σ * τ) u := rfl

@[simp] theorem algEquivUnitsMapOfField_one (u : Units E) :
    algEquivUnitsMapOfField F E (1 : E ≃ₐ[F] E) u = u := rfl

/-- **The action of `Gal(E/F)` on `Additive Eˣ`**, by transport of units along the field
automorphism.  Declared at low priority: for `E = AlgebraicClosure k` the workspace's instance
`Work.AbsoluteKummer.instDistribMulActionAddUnits` applies and is preferred, so existing
statements and proofs are untouched. -/
noncomputable instance (priority := 100) instDistribMulActionAddUnitsOfField :
    DistribMulAction (E ≃ₐ[F] E) (Additive (Units E)) where
  smul σ a := Additive.ofMul (algEquivUnitsMapOfField F E σ (Additive.toMul a))
  one_smul a := by
    show Additive.ofMul (algEquivUnitsMapOfField F E (1 : E ≃ₐ[F] E) (Additive.toMul a)) = a
    rw [algEquivUnitsMapOfField_one, ofMul_toMul]
  mul_smul σ τ a := by
    show Additive.ofMul (algEquivUnitsMapOfField F E (σ * τ) (Additive.toMul a)) =
      Additive.ofMul (algEquivUnitsMapOfField F E σ
        (algEquivUnitsMapOfField F E τ (Additive.toMul a)))
    rw [algEquivUnitsMapOfField_mul]
  smul_zero σ := by
    show Additive.ofMul (algEquivUnitsMapOfField F E σ (1 : Units E)) = 0
    rw [map_one, ofMul_one]
  smul_add σ a b := by
    show Additive.ofMul (algEquivUnitsMapOfField F E σ
      (Additive.toMul a * Additive.toMul b)) =
      Additive.ofMul (algEquivUnitsMapOfField F E σ (Additive.toMul a)) +
        Additive.ofMul (algEquivUnitsMapOfField F E σ (Additive.toMul b))
    rw [map_mul, ofMul_mul]

end


/-- The units of an algebraic-closure isomorphism intertwine the two Galois actions. -/
theorem algEquivUnitsMapOfField_comm (F : Type*) [Field F] {A₂ : Type*} [Field A₂]
    [Algebra F A₂] (e : AlgebraicClosure F ≃ₐ[F] A₂) (σ : A₂ ≃ₐ[F] A₂) (u : Units A₂) :
    Units.map (AlgEquiv.toRingEquiv (AlgEquiv.symm e)).toMonoidHom
        (algEquivUnitsMapOfField F A₂ σ u) =
      Work.AbsoluteKummer.algEquivUnitsMap F ((AlgEquiv.autCongr e).symm σ)
        (Units.map (AlgEquiv.toRingEquiv (AlgEquiv.symm e)).toMonoidHom u) := by
  ext
  simp only [Units.coe_map, Work.AbsoluteKummer.algEquivUnitsMap_coe,
    algEquivUnitsMapOfField_coe]
  have h1 := congrArg
    (fun (f : A₂ ≃ₐ[F] A₂) => f ((u : A₂)))
    (MulEquiv.apply_symm_apply (AlgEquiv.autCongr e) σ)
  rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply] at h1
  rw [← h1]
  exact AlgEquiv.symm_apply_apply e _


/-- **Hilbert 90 over an arbitrary algebraic closure**: for a field extension `F ⊆ Ω` with `Ω` an
algebraic closure of `F` and `F` of characteristic `0`, every continuous crossed homomorphism
`Gal(Ω/F) → Ωˣ` is principal, i.e. `H¹(Gal(Ω/F), Ωˣ) = 0`.  This is Milne, *ADT*, class-formation
axiom 1.1a for the class module `\bar k^×`, in the generality needed by
`Work.SSGRoute.PT.localTatePairing_deg02` (whose `Ω` only satisfies `IsAlgClosure k Ω`).

Proof: transport `Submission.hilbert90_H1_eq_zero` from `AlgebraicClosure F` to `Ω` along the
group isomorphism `(AlgEquiv.autCongr e)⁻¹` (`e := IsAlgClosure.equiv F (AlgebraicClosure F) Ω`),
which is a homeomorphism by `NK.Mine.isHomeomorph_autCongr` / `NK.Mine.isHomeomorph_symm`, using
the group transfer `Work.SSGRoute.PT.h1Transfer`; the compatibility of the coefficient
isomorphism with the two Galois actions is `algEquivUnitsMapOfField_comm`. -/
theorem hilbert90_H1_eq_zero_of_isAlgClosure (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
    [IsGalois F Ω] [IsAlgClosure F Ω] [CharZero F]
    (x : Work.AbsoluteKummer.H1 (Ω ≃ₐ[F] Ω) (Additive (Units Ω))) : x = 0 := by
  let e : AlgebraicClosure F ≃ₐ[F] Ω := IsAlgClosure.equiv F (AlgebraicClosure F) Ω
  have hΦ : IsHomeomorph ((AlgEquiv.autCongr e).symm :
      (Ω ≃ₐ[F] Ω) → (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) :=
    NK.Mine.isHomeomorph_symm (AlgEquiv.autCongr e) (NK.Mine.isHomeomorph_autCongr e)
  let Ψ : Additive (Units Ω) ≃+ Additive (Units (AlgebraicClosure F)) :=
    { toFun := fun a => Additive.ofMul
        ((Units.map (AlgEquiv.toRingEquiv (AlgEquiv.symm e)).toMonoidHom) (Additive.toMul a))
      invFun := fun b => Additive.ofMul
        ((Units.map (AlgEquiv.toRingEquiv e).toMonoidHom) (Additive.toMul b))
      left_inv := by
        intro a
        obtain ⟨u, rfl⟩ := Additive.ofMul.surjective a
        show Additive.ofMul _ = Additive.ofMul u
        congr 1
        exact Units.ext (by simp)
      right_inv := by
        intro b
        obtain ⟨u, rfl⟩ := Additive.ofMul.surjective b
        show Additive.ofMul _ = Additive.ofMul u
        congr 1
        exact Units.ext (by simp)
      map_add' := by
        intro a b
        obtain ⟨u, rfl⟩ := Additive.ofMul.surjective a
        obtain ⟨v, rfl⟩ := Additive.ofMul.surjective b
        show Additive.ofMul _ = Additive.ofMul _ + Additive.ofMul _
        congr 1
        exact map_mul _ u v }
  have hΨ : ∀ (σ : Ω ≃ₐ[F] Ω) (a : Additive (Units Ω)),
      Ψ (σ • a) = ((AlgEquiv.autCongr e).symm : (Ω ≃ₐ[F] Ω) ≃*
        (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) σ • Ψ a := by
    intro σ a
    obtain ⟨u, rfl⟩ := Additive.ofMul.surjective a
    show Additive.ofMul ((Units.map (AlgEquiv.toRingEquiv (AlgEquiv.symm e)).toMonoidHom)
        (algEquivUnitsMapOfField F Ω σ u)) =
      Additive.ofMul (Work.AbsoluteKummer.algEquivUnitsMap F ((AlgEquiv.autCongr e).symm σ)
        ((Units.map (AlgEquiv.toRingEquiv (AlgEquiv.symm e)).toMonoidHom) u))
    rw [algEquivUnitsMapOfField_comm F e σ u]
  haveI : Subsingleton
      (Work.AbsoluteKummer.H1 (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
        (Additive (Units (AlgebraicClosure F)))) :=
    ⟨fun a b => by
      rw [Submission.hilbert90_H1_eq_zero F a, Submission.hilbert90_H1_eq_zero F b]⟩
  have h := h1Transfer (G := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (G' := Ω ≃ₐ[F] Ω)
    (M := Additive (Units (AlgebraicClosure F))) (M' := Additive (Units Ω))
    (AlgEquiv.autCongr e).symm hΦ Ψ hΨ
  have hx : h x = 0 := Subsingleton.elim _ _
  have h2 : x = h.symm 0 := by rw [← hx, AddEquiv.symm_apply_apply]
  rw [h2, map_zero]

end Work.SSGRoute.PT
