import Mathlib

set_option linter.style.haveILetI false

namespace Work.ShafarevichKoch.Gaschutz

/-- A finite commutative group of exponent two and cardinality at most `2 ^ r` is isomorphic to
`(ℤ/2)^k` for some `k ≤ r`. -/
theorem exists_mulEquiv_pi_zmodTwo_of_natCard_le {V : Type*} [CommGroup V] [Fintype V]
    (h2 : ∀ x : V, x ^ 2 = 1) {r : ℕ} (hcard : Nat.card V ≤ 2 ^ r) :
    ∃ k : ℕ, k ≤ r ∧ Nonempty (V ≃* Multiplicative (Fin k → ZMod 2)) := by
  -- `Additive V` is an abelian group of exponent `2`, hence a `ZMod 2`-vector space.
  have hzero : ∀ x : Additive V, (2 : ℕ) • x = 0 := fun x => h2 x
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule hzero
  haveI : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  -- Choose a basis; its cardinality is the dimension `k = finrank`.
  let b := Module.finBasis (ZMod 2) (Additive V)
  refine ⟨Module.finrank (ZMod 2) (Additive V), ?_, ?_⟩
  · -- The cardinality of a finite-dimensional `𝔽₂`-vector space is `2 ^ finrank`.
    have hcardb : Nat.card (Additive V) = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
      have h := Module.card_fintype b
      rw [ZMod.card 2, Fintype.card_fin] at h
      rw [Nat.card_eq_fintype_card]
      exact h
    have hk : 2 ^ Module.finrank (ZMod 2) (Additive V) ≤ 2 ^ r := by
      rw [← hcardb, Nat.card_congr Additive.toMul]
      exact hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hk
  · -- Transport the additive linear equivalence to a multiplicative one.
    exact ⟨AddEquiv.toMultiplicativeRight b.equivFun.toAddEquiv⟩

end Work.ShafarevichKoch.Gaschutz
