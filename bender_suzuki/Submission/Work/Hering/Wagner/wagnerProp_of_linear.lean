import Mathlib
import Submission.Work.Hering.Wagner.Defs
import Submission.Work.Hering.Step6.actsAsAut

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Wagner's proposition in the multiplicative form, from the linear form

`Work.Hering.Wagner.WagnerProp` is the "multiplicative" formulation of Wagner's proposition
(Peterfalvi I §1, p. 188): for a finite abelian group `V` of exponent `2`, a subgroup
`Gm ≤ Aut(V)` doubly transitive on `V \ {1}`, and a subgroup `U ≤ V` of order `8`, every
automorphism of `U` is induced by an element of `Gm`.

This file derives it from the "linear" formulation `core`, stated for a finite
`ZMod 2`-vector space `V`, a subgroup `Gm ≤ GL(V)` doubly transitive on `V \ {0}`, a
`3`-dimensional subspace `U` and a linear automorphism `φ` of `U`.

The bridge is the dictionary between an elementary abelian `2`-group and a `ZMod 2`-vector
space: an abelian group of exponent `2` carries the `ZMod 2`-module structure
`AddCommGroup.zmodModule`, and every `MulAut` is then automatically `ZMod 2`-linear.

Because `core` is stated at a fixed universe while `WagnerProp` is universe polymorphic, we
first prove the statement at the universe of `core` and then move it to the target universe with
`Work.Hering.Step6.wagnerProp_univ`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Hering.Wagner

/-- The multiplicative form of Wagner's proposition, obtained from the linear form `core`
**at the same universe** (so that `core` can be applied directly). -/
theorem wagnerProp_of_linear_aux.{u}
    (core : ∀ {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (Gm : Subgroup (V ≃ₗ[ZMod 2] V))
      (h2 : ∀ a b c d : V, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → a ≠ b → c ≠ d →
        ∃ g ∈ Gm, g a = c ∧ g b = d)
      (U : Submodule (ZMod 2) V) (hU : Module.finrank (ZMod 2) U = 3) (φ : U ≃ₗ[ZMod 2] U),
      ∃ g ∈ Gm, ∀ u : U, g u = φ u) :
    WagnerProp.{u} := by
  intro V _instG _instF habel hexp Gm h2 U hU φ
  -- An abelian group of exponent `2` is a `ZMod 2`-vector space.
  letI : CommGroup V := { ‹Group V› with mul_comm := habel }
  letI : AddCommGroup V := inferInstanceAs (AddCommGroup (Additive V))
  have h2' : ∀ x : V, (2 : ℕ) • x = 0 := fun x => by
    show (2 : ℕ) • Additive.ofMul x = (0 : Additive V)
    rw [← ofMul_pow, pow_two, hexp x]
    rfl
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (n := 2) h2'
  -- Every `MulAut` of `V` is a `ZMod 2`-linear automorphism.
  let toAdd : MulAut V → V ≃+ V := fun f =>
    { toFun := f, invFun := f.symm, map_add' := fun x y => f.map_mul x y,
      left_inv := f.left_inv, right_inv := f.right_inv }
  let toLin : MulAut V → V ≃ₗ[ZMod 2] V := fun f =>
    (toAdd f).toLinearEquiv (fun c x => ZMod.map_smul (n := 2) (toAdd f) c x)
  let toLinHom : MulAut V →* (V ≃ₗ[ZMod 2] V) :=
    { toFun := toLin
      map_one' := by ext x; rfl
      map_mul' := by intro f g; ext x; rfl }
  -- The subgroup `U` of order `8` is a `3`-dimensional subspace.
  let Uadd : AddSubgroup V :=
    { carrier := U, add_mem' := fun ha hb => U.mul_mem ha hb,
      zero_mem' := U.one_mem, neg_mem' := fun ha => U.inv_mem ha }
  let Usub : Submodule (ZMod 2) V := AddSubgroup.toZModSubmodule 2 Uadd
  haveI : Fintype ↥Usub := Fintype.ofFinite _
  have hfin : Module.finrank (ZMod 2) ↥Usub = 3 := by
    have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := ↥Usub)
    have hcardUsub : Nat.card ↥Usub = 8 := hU
    rw [Nat.card_eq_fintype_card] at hcardUsub
    rw [ZMod.card] at hc
    have : 2 ^ Module.finrank (ZMod 2) ↥Usub = 2 ^ 3 := by
      rw [← hc, hcardUsub]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) this
  -- The automorphism `φ` of `U` as a linear automorphism of the subspace.
  let φadd : ↥Usub ≃+ ↥Usub :=
    { toFun := fun u => φ ⟨u.1, u.2⟩
      invFun := fun u => φ.symm ⟨u.1, u.2⟩
      left_inv := fun u => by
        apply Subtype.ext
        change ((φ.symm (φ ⟨u.1, u.2⟩) : ↥U) : V) = u.1
        simp
      right_inv := fun u => by
        apply Subtype.ext
        change ((φ (φ.symm ⟨u.1, u.2⟩) : ↥U) : V) = u.1
        simp
      map_add' := fun x y => by
        apply Subtype.ext
        change ((φ (⟨x.1, x.2⟩ * ⟨y.1, y.2⟩) : ↥U) : V)
          = ((φ ⟨x.1, x.2⟩ * φ ⟨y.1, y.2⟩ : ↥U) : V)
        simp }
  let φ' : ↥Usub ≃ₗ[ZMod 2] ↥Usub :=
    φadd.toLinearEquiv (fun c x => ZMod.map_smul (n := 2) φadd c x)
  -- `Gm` is doubly transitive on the nonzero vectors of the vector space.
  have h2lin : ∀ a b c d : V, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → a ≠ b → c ≠ d →
      ∃ g ∈ Gm.map toLinHom, g a = c ∧ g b = d := by
    intro a b c d ha hb hc hd hab hcd
    obtain ⟨g, hg, hga, hgb⟩ := h2 a b c d ha hb hc hd hab hcd
    refine ⟨toLin g, Subgroup.mem_map_of_mem toLinHom hg, ?_, ?_⟩
    · show toLin g a = c
      rw [show toLin g a = g a from rfl]; exact hga
    · show toLin g b = d
      rw [show toLin g b = g b from rfl]; exact hgb
  -- Apply the linear form of Wagner's proposition.
  obtain ⟨g', hg', hg'prop⟩ := core (Gm.map toLinHom) h2lin Usub hfin φ'
  rw [Subgroup.mem_map] at hg'
  obtain ⟨g, hgGm, hgg'⟩ := hg'
  refine ⟨g, hgGm, ?_⟩
  intro u
  have h := hg'prop ⟨u.1, u.2⟩
  rw [← hgg'] at h
  change g (u : V) = ((φ u : ↥U) : V)
  exact h

theorem wagnerProp_of_linear
    (core : ∀ {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (Gm : Subgroup (V ≃ₗ[ZMod 2] V))
      (h2 : ∀ a b c d : V, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → a ≠ b → c ≠ d →
        ∃ g ∈ Gm, g a = c ∧ g b = d)
      (U : Submodule (ZMod 2) V) (hU : Module.finrank (ZMod 2) U = 3) (φ : U ≃ₗ[ZMod 2] U),
      ∃ g ∈ Gm, ∀ u : U, g u = φ u) :
    WagnerProp :=
  Work.Hering.Step6.wagnerProp_univ (wagnerProp_of_linear_aux core)

end Work.Hering.Wagner
