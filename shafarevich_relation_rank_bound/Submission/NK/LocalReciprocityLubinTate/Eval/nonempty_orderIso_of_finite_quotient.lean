import Mathlib

/-!
# An ordered abelian group that is virtually infinite cyclic is infinite cyclic

Let `Γ` be a linearly ordered commutative group with zero and let `G ≤ Γˣ` be a subgroup of
finite index with `WithZero G ≃*o WithZero (Multiplicative ℤ)` (i.e. `G`, with its induced
order, is an infinite cyclic ordered group).  Then `Γ` itself is order-isomorphic, as a monoid
with zero, to `WithZero (Multiplicative ℤ)`: `Γ ≃*o WithZero (Multiplicative ℤ)`.

The proof does not use the classification of torsion-free virtually cyclic groups: the `n`-th
power map (`n` the index of `G` in `Γˣ`) lands in `G ≅ ℤ`, and is injective because an ordered
group is torsion-free; an injective homomorphism into the cyclic group `ℤ` exhibits `Γˣ` as
cyclic, and Mathlib's `LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int` turns
cyclicity of a linearly ordered commutative group into an order isomorphism with
`Multiplicative ℤ`.
-/

namespace NK.LocalReciprocityLubinTate.Eval

/-- In a linearly ordered commutative group, an `n`-th power is `1` only if the element itself
is `1` (`n ≠ 0`).  Equivalently: a linearly ordered group is torsion-free. -/
private lemma pow_eq_one_iff_of_ne_zero {A : Type*} [CommGroup A] [LinearOrder A]
    [IsOrderedMonoid A] {n : ℕ} (hn : n ≠ 0) {a : A} : a ^ n = 1 ↔ a = 1 := by
  constructor
  · intro h
    rcases lt_trichotomy a 1 with hlt | heq | hgt
    · exact absurd h (ne_of_lt ((pow_lt_one_iff hn).mpr hlt))
    · exact heq
    · exact absurd h (ne_of_gt ((one_lt_pow_iff hn).mpr hgt))
  · rintro rfl; exact one_pow n

theorem nonempty_orderIso_of_finite_quotient {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (G : Subgroup Γˣ) (hfin : Finite (Γˣ ⧸ G))
    (hiso : Nonempty (WithZero G ≃*o WithZero (Multiplicative ℤ))) :
    Nonempty (Γ ≃*o WithZero (Multiplicative ℤ)) := by
  classical
  obtain ⟨φ⟩ := hiso
  -- `G` is infinite cyclic, with its induced order
  let e : G ≃*o Multiplicative ℤ :=
    (OrderMonoidIso.withZero (G := G) (H := Multiplicative ℤ)).symm φ
  have hfin' : Finite (Γˣ ⧸ G) := hfin
  -- `n` is the index of `G` in `Γˣ` (nonzero since the quotient is finite)
  let n := G.index
  have hn : n ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpow : ∀ a : Γˣ, a ^ n ∈ G := fun a => Subgroup.pow_index_mem G a
  -- the `n`-th power map, read through `G ≃*o Multiplicative ℤ`
  let k : Γˣ →* Multiplicative ℤ :=
    e.toMulEquiv.toMonoidHom.comp ((powMonoidHom n : Γˣ →* Γˣ).codRestrict G hpow)
  have hkval : ∀ x : Γˣ, k x = e ⟨x ^ n, hpow x⟩ := fun _ => rfl
  -- `k` is injective because `Γˣ` is torsion-free
  have hk : Function.Injective k := by
    intro a b hab
    have h1 : k (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    rw [hkval (a * b⁻¹)] at h1
    have h3 : (⟨(a * b⁻¹) ^ n, hpow (a * b⁻¹)⟩ : G) = 1 := by
      apply e.injective
      simpa using h1
    have h4 : (a * b⁻¹) ^ n = 1 := by
      simpa using congrArg (fun x : G => (x : Γˣ)) h3
    exact mul_inv_eq_one.mp ((pow_eq_one_iff_of_ne_zero hn).mp h4)
  -- hence `Γˣ` is cyclic
  have hcyc : IsCyclic Γˣ := isCyclic_of_injective k hk
  have hG : Nontrivial G := e.toEquiv.surjective.nontrivial
  have hA : Nontrivial Γˣ :=
    Function.Injective.nontrivial (f := (fun x : G => (x : Γˣ))) Subtype.coe_injective
  -- a nontrivial linearly ordered cyclic commutative group is order-isomorphic to `ℤ`
  obtain ⟨fA⟩ := (LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int (G := Γˣ)).mp hcyc
  exact ⟨(OrderMonoidIso.withZeroUnits (α := Γ)).symm.trans
    ((OrderMonoidIso.withZero (G := Γˣ) (H := Multiplicative ℤ)) fA)⟩

end NK.LocalReciprocityLubinTate.Eval
