/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Kummer bridge: degree-`p` Galois extensions versus `kˣ/(kˣ)^p`

This is part (A) of the `NK.LocalAnabelian` chapter, and it uses *no* class field
theory.  For a field `k` containing a primitive `p`-th root of unity `ζ` (`p` prime)
and a separable closure `K'` of `k` we prove

  `#{L : k ⊆ L ⊆ K', L/k Galois of degree p} = (|kˣ/(kˣ)^p| - 1) / (p - 1)`.

The proof is the standard one: the Kummer field `k(a^{1/p})` of a nontrivial class `a`
is a degree-`p` cyclic extension, every degree-`p` Galois extension arises this way
(`exists_kummerFieldQuot_eq_of_isGalois`), two classes give the same field exactly when
they generate the same cyclic subgroup of `kˣ/(kˣ)^p` (the two "fibre" lemmas), and the
groups `⟨a⟩ \ {1}` have `p - 1` elements each.
-/
import Submission.NK.LocalAnabelian.Kummer.QuotAPI
import Submission.NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank
import Submission.NK.LocalAnabelian.Kummer.exists_kummerFieldQuot_eq_of_isGalois
import Submission.NK.LocalAnabelian.Kummer.mem_zpowers_of_kummerFieldQuot_eq
import Submission.NK.LocalAnabelian.Kummer.kummerFieldQuot_eq_of_mem_zpowers
import Submission.NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup
import Submission.NK.LocalAnabelian.Counting.natCard_eq_mul_card_of_fiber_natCard
import Submission.NK.LocalAnabelian.Counting.natCard_subtype_ne_one

open scoped Classical
open IntermediateField

namespace NK.LocalAnabelian

noncomputable section

variable {k K' : Type*} [Field k] [Field K'] [Algebra k K']

/-- The type of degree-`p` Galois extensions of `k` inside `K'`. -/
abbrev DegreePGaloisFields (k K' : Type*) [Field k] [Field K'] [Algebra k K'] (p : ℕ) : Type _ :=
  {L : IntermediateField k K' // IsGalois k L ∧ Module.finrank k L = p}

variable [IsSepClosure k K']

/-- A nontrivial Kummer class gives a degree-`p` Galois extension. -/
theorem kummerFieldQuot_isGalois_finrank (p : ℕ) (hp : p.Prime) {ζ : k}
    (hζ : IsPrimitiveRoot ζ p) {x : KummerGroup p k} (hx : x ≠ 1) :
    IsGalois k (kummerFieldQuot (K' := K') p x) ∧
      Module.finrank k (kummerFieldQuot (K' := K') p x) = p :=
  Kummer.isGalois_kummerField_and_finrank (K' := K') p hp hζ (Quotient.out x)
    (notMem_powSubgroup_of_out_ne_one hx)

/-- The trivial class has Kummer field `k` itself. -/
theorem kummerFieldQuot_one_eq_bot (p : ℕ) (hp : p.Prime) {ζ : k} (hζ : IsPrimitiveRoot ζ p) :
    kummerFieldQuot (K' := K') p (QuotientGroup.mk (1 : kˣ)) = ⊥ := by
  rw [kummerFieldQuot_mk]
  exact Kummer.kummerField_eq_bot_of_mem_powSubgroup (K' := K') p hp hζ
    (MonoidHom.mem_range.mpr ⟨1, by simp [powMonoidHom_apply]⟩)

/-- Every degree-`p` Galois extension is the Kummer field of a *nontrivial* class. -/
theorem exists_ne_one_kummerFieldQuot_eq (p : ℕ) (hp : p.Prime) {ζ : k}
    (hζ : IsPrimitiveRoot ζ p) (b : DegreePGaloisFields k K' p) :
    ∃ x : KummerGroup p k, x ≠ 1 ∧ kummerFieldQuot (K' := K') p x = b.1 := by
  obtain ⟨x₀, hx₀⟩ := Kummer.exists_kummerFieldQuot_eq_of_isGalois (K' := K') p hp hζ b.1
    b.2.1 b.2.2
  have hx₀ne : x₀ ≠ 1 := by
    intro h1
    have hbot : kummerFieldQuot (K' := K') p x₀ = ⊥ := by
      rw [h1]
      show kummerFieldQuot (K' := K') p (QuotientGroup.mk (1 : kˣ)) = ⊥
      exact kummerFieldQuot_one_eq_bot p hp hζ
    have hdeg : Module.finrank k (kummerFieldQuot (K' := K') p x₀) = p := by
      rw [hx₀]; exact b.2.2
    rw [hbot] at hdeg
    rw [show Module.finrank k (⊥ : IntermediateField k K') = 1 from IntermediateField.finrank_bot] at hdeg
    have hp2 : 2 ≤ p := hp.two_le
    omega
  exact ⟨x₀, hx₀ne, hx₀⟩

/-- **The Kummer bridge.**  Over a field containing a primitive `p`-th root of unity, the
degree-`p` Galois extensions inside a separable closure are counted by the `p`-th power
class group:

  `#{L} = (|kˣ/(kˣ)^p| - 1)/(p - 1)`. -/
theorem natCard_galois_finrank_eq_p (p : ℕ) (hp : p.Prime) {ζ : k}
    (hζ : IsPrimitiveRoot ζ p) [Finite (KummerGroup p k)] :
    Nat.card (DegreePGaloisFields k K' p) =
      (Nat.card (KummerGroup p k) - 1) / (p - 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : 0 < p - 1 := by omega
  let f : {x : KummerGroup p k // x ≠ 1} → DegreePGaloisFields k K' p :=
    fun x => ⟨kummerFieldQuot (K' := K') p x.1, kummerFieldQuot_isGalois_finrank p hp hζ x.2⟩
  haveI : Finite {x : KummerGroup p k // x ≠ 1} :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨x₀, hx₀ne, hx₀⟩ := exists_ne_one_kummerFieldQuot_eq p hp hζ b
    exact ⟨⟨x₀, hx₀ne⟩, Subtype.ext hx₀⟩
  haveI : Finite (DegreePGaloisFields k K' p) := Finite.of_surjective f hsurj
  -- the fibre over each element has `p - 1` elements
  have hfib : ∀ b : DegreePGaloisFields k K' p,
      Nat.card {x : {x : KummerGroup p k // x ≠ 1} // f x = b} = p - 1 := by
    intro b
    obtain ⟨x₀, hx₀ne, hx₀⟩ := exists_ne_one_kummerFieldQuot_eq p hp hζ b
    -- `x₀` has order `p`
    have hxp : x₀ ^ p = 1 := kummerGroup_pow_self p x₀
    have hord : orderOf x₀ = p := by
      have hdvd : orderOf x₀ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hxp
      rcases hp.eq_one_or_self_of_dvd (orderOf x₀) hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx₀ne
      · exact h
    -- the fibre is the set of nontrivial powers of `x₀`
    have hequiv : (Subtype fun y : KummerGroup p k => y ≠ 1 ∧
          kummerFieldQuot (K' := K') p y = kummerFieldQuot (K' := K') p x₀) ≃
        (Subtype fun y : KummerGroup p k => y ∈ Subgroup.zpowers x₀ ∧ y ≠ 1) :=
      Equiv.subtypeEquivRight fun y => ⟨fun h => ⟨
        Kummer.mem_zpowers_of_kummerFieldQuot_eq (K' := K') p hp hζ hx₀ne h.1 h.2, h.1⟩,
        fun h => ⟨h.2,
          Kummer.kummerFieldQuot_eq_of_mem_zpowers (K' := K') p hp hζ hx₀ne h.2 h.1⟩⟩
    have hfib₀ : Nat.card {y : KummerGroup p k // y ∈ Subgroup.zpowers x₀ ∧ y ≠ 1} = p - 1 := by
      haveI : Finite (Subgroup.zpowers x₀) :=
        finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hxp⟩)
      have hcard : Nat.card {y : KummerGroup p k // y ∈ Subgroup.zpowers x₀ ∧ y ≠ 1} =
          Nat.card {y : Subgroup.zpowers x₀ // y ≠ 1} :=
        Nat.card_congr
          { toFun := fun y => ⟨⟨y.1, y.2.1⟩, fun h => y.2.2 (congrArg Subtype.val h)⟩
            invFun := fun y => ⟨y.1.1, y.1.2, fun h => y.2 (Subtype.ext h)⟩
            left_inv := fun y => Subtype.ext rfl
            right_inv := fun y => Subtype.ext rfl }
      rw [hcard, Counting.natCard_subtype_ne_one, Nat.card_zpowers, hord]
    rw [← hfib₀, ← Nat.card_congr hequiv]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, (congrArg Subtype.val x.2).trans hx₀.symm⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subtype.ext (y.2.2.trans hx₀)⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
  have hmul := Counting.natCard_eq_mul_card_of_fiber_natCard f (p - 1) hp1 hfib
  have hone := Counting.natCard_subtype_ne_one (KummerGroup p k)
  have hmain : (p - 1) * Nat.card (DegreePGaloisFields k K' p) =
      Nat.card (KummerGroup p k) - 1 := by
    rw [← hmul]
    exact hone
  rw [← hmain, Nat.mul_div_cancel_left _ hp1]

end

end NK.LocalAnabelian
