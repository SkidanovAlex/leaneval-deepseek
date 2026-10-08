import Mathlib
import Submission.Work.Hering.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Finite abelian groups of exponent two are elementary abelian `2`-groups

A finite group `V` in which every element satisfies `x * x = 1` and in which
multiplication is commutative is a vector space over `ZMod 2`; being finite it is
finite dimensional, hence isomorphic to `(ZMod 2)^n` for `n = finrank (ZMod 2) V`.

This is the `2`-group statement used when bounding the rank of a group acting on
its involutions (Hering / Bender–Suzuki).
-/

set_option linter.style.haveILetI false

namespace Work.Hering.F2

theorem groups_of_exponent_two {V : Type*} [Group V] [Finite V]
    (habel : ∀ x y : V, x * y = y * x) (hexp : ∀ x : V, x * x = 1) :
    ∃ n : ℕ, Nonempty (V ≃* Multiplicative (Fin n → ZMod 2)) := by
  -- Promote `V` to a commutative group using the commutativity hypothesis.
  letI : CommGroup V := { ‹Group V› with mul_comm := habel }
  -- In additive notation `V` is `2`-torsion, so it carries a `ZMod 2`-module structure.
  have h2 : ∀ x : Additive V, (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero, hexp]
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2
  -- A finite module is finitely generated (span of all its elements).
  haveI : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_fg_top (by
    rw [Submodule.fg_iff_exists_finite_generating_family]
    exact ⟨Additive V, inferInstance, id, by simp⟩)
  -- Choose a basis indexed by `Fin (finrank …)` and read off coordinates.
  let b := Module.finBasis (ZMod 2) (Additive V)
  refine ⟨Module.finrank (ZMod 2) (Additive V), ⟨{
    toFun := fun v => Multiplicative.ofAdd (b.equivFun (Additive.ofMul v))
    invFun := fun w => Additive.toMul (b.equivFun.symm (Multiplicative.toAdd w))
    left_inv := by intro v; simp
    right_inv := by
      intro w
      simp only [ofMul_toMul, LinearEquiv.apply_symm_apply, ofAdd_toAdd]
    map_mul' := by
      intro a b'
      show Multiplicative.ofAdd (b.equivFun (Additive.ofMul (a * b'))) =
        Multiplicative.ofAdd (b.equivFun (Additive.ofMul a)) *
          Multiplicative.ofAdd (b.equivFun (Additive.ofMul b'))
      rw [ofMul_mul, map_add, ofAdd_add]
  }⟩⟩

end Work.Hering.F2
