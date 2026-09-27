import Mathlib
import Submission.Work.KT.Defs

/-!
# Functoriality of `K₀` on ring homomorphisms

`K₀` is the Grothendieck group of idempotent square matrices (`Work.KT.K0`), and `K0.map φ` is
its functorial action along a ring homomorphism `φ` (`Work.KT.K0.map`).  Here we prove that it is
a functor: `K₀(ψ ∘ φ) = K₀(ψ) ∘ K₀(φ)`.

The proof is the standard one for a quotient of a free abelian group: `K0.map` is defined by
extension from its values `mapCls φ p` on the generators `cls p`, so it suffices to check the
identity on generators, where it reduces to `Mat.map` being functorial (`Matrix.map_map`) and to
idempotency being preserved by ring maps.
-/

namespace Work.KT.K0map

open Work.KT

/-! ## Elementary facts about matrices -/

/-- `Mat.map` is functorial: mapping entries by `ψ ∘ φ` is mapping by `φ` then by `ψ`
(`Matrix.map_map` for ring homomorphisms). -/
lemma mat_map_map {R S T : Type} [Ring R] [Ring S] [Ring T]
    (φ : R →+* S) (ψ : S →+* T) (p : Mat R) :
    (p.map φ).map ψ = p.map (ψ.comp φ) := by
  unfold Mat.map
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext i j
  simp only [Matrix.map_apply, RingHom.comp_apply]

/-- Idempotency of a matrix is preserved by a ring homomorphism. -/
lemma isIdem_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) {p : Mat R} (hp : p.IsIdem) :
    (p.map φ).IsIdem := by
  unfold Mat.IsIdem Mat.map at *
  simp only
  rw [← Matrix.map_mul, hp]

/-! ## The action of `K0.map` on generators -/

/-- `K0.map φ` on the class of a matrix is `mapCls φ`, its defining value on generators. -/
lemma map_cls {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (p : Mat R) :
    K0.map φ (cls p) = mapCls φ p := by
  rw [K0.map, cls, QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]

/-- The defining values `mapCls` are compatible with composition: applying `K0.map ψ` to
`mapCls φ p` gives `mapCls (ψ ∘ φ) p`.  This is the heart of functoriality, and it is where the
idempotency condition is used. -/
lemma map_mapCls {A B C : Type} [Ring A] [Ring B] [Ring C]
    (φ : A →+* B) (ψ : B →+* C) (p : Mat A) :
    K0.map ψ (mapCls φ p) = mapCls (ψ.comp φ) p := by
  unfold mapCls
  by_cases hp : p.IsIdem
  · have h2 : (p.map φ).IsIdem := isIdem_map φ hp
    rw [if_pos hp, if_pos hp, map_cls ψ (p.map φ), mapCls, if_pos h2, mat_map_map]
  · rw [if_neg hp, if_neg hp, map_zero]

/-! ## Functoriality -/

/-- `K₀` is a functor: `K₀(ψ ∘ φ) = K₀(ψ) ∘ K₀(φ)`. -/
theorem map_comp (A B C : Type) [Ring A] [Ring B] [Ring C] (φ : A →+* B) (ψ : B →+* C) :
    Work.KT.K0.map (ψ.comp φ) = (Work.KT.K0.map ψ).comp (Work.KT.K0.map φ) := by
  apply AddMonoidHom.ext
  intro x
  -- `x` lives in `K0 A = FreeAbelianGroup (Mat A) ⧸ K0Rel A`: reduce to the quotient and then
  -- to the generators `of p` of the free abelian group.
  induction x using QuotientAddGroup.induction_on with
  | H g =>
    induction g using FreeAbelianGroup.induction_on with
    | zero =>
      rw [QuotientAddGroup.mk_zero, map_zero, map_zero]
    | of p =>
      change K0.map (ψ.comp φ) (cls p) = (K0.map ψ).comp (K0.map φ) (cls p)
      rw [AddMonoidHom.comp_apply, map_cls (ψ.comp φ) p, map_cls φ p, map_mapCls]
    | neg x ih =>
      rw [QuotientAddGroup.mk_neg, map_neg, map_neg]
      exact congrArg Neg.neg ih
    | add x y ihx ihy =>
      rw [QuotientAddGroup.mk_add, map_add, map_add]
      rw [ihx, ihy]

end Work.KT.K0map
