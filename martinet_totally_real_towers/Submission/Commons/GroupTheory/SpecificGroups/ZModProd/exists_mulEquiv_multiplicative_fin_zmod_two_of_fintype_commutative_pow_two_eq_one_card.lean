import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

/-!
# Finite commutative groups of exponent two are elementary abelian 2-groups

A finite commutative group all of whose elements are self-inverse (`x ^ 2 = 1`) satisfies the
`ZMod 2`-module axioms, hence is a vector space over `ZMod 2`.  If its cardinality is `2 ^ k`
then its dimension is `k`, so it is isomorphic to the direct product of `k` copies of `ZMod 2`,
i.e. to `Multiplicative (Fin k → ZMod 2)`.
-/

namespace Commons.GroupTheory.SpecificGroups.ZModProd

open scoped IsMulCommutative

set_option linter.style.haveILetI false

theorem exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card
    {G : Type*} [Group G] [Fintype G] [IsMulCommutative G]
    (hG : ∀ x : G, x ^ 2 = 1) {k : ℕ} (hcard : Nat.card G = 2 ^ k) :
    Nonempty (G ≃* Multiplicative (Fin k → ZMod 2)) := by
  classical
  -- The additive group underlying `G` is killed by `2`.
  have h2 : ∀ x : Additive G, (2 : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul]
    simp [hG]
  -- Hence it is a module over `ZMod 2`.
  letI : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule h2
  haveI : Module.Finite (ZMod 2) (Additive G) := Module.finite_iff_finite.mpr inferInstance
  -- Its dimension over `ZMod 2` is `k`, since `2 ^ k = Nat.card G = Nat.card (ZMod 2) ^ finrank`.
  have hfr : Module.finrank (ZMod 2) (Additive G) = k := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive G)
    rw [Nat.card_zmod] at h1
    have hcard' : Nat.card (Additive G) = 2 ^ k := by
      rw [← hcard]; simp
    rw [hcard'] at h1
    exact Nat.pow_right_injective (a := 2) (by norm_num) h1.symm
  -- A finite-dimensional vector space is isomorphic to `Fin (finrank) → ZMod 2`.
  obtain ⟨e⟩ : Nonempty (Additive G ≃ₗ[ZMod 2] (Fin k → ZMod 2)) :=
    ⟨LinearEquiv.ofFinrankEq (Additive G) (Fin k → ZMod 2)
      (by rw [hfr, Module.finrank_fin_fun])⟩
  exact ⟨e.toAddEquiv.toMultiplicativeRight⟩

end Commons.GroupTheory.SpecificGroups.ZModProd