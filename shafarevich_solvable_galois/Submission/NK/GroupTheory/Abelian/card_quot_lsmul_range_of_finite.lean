import Mathlib.Algebra.Module.Torsion.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GroupTheory.Abelian

/-- For a finite abelian group `T` and any `p : ℕ`, the quotient of `T` by the image of
multiplication by `p` has the same cardinality as the `p`-torsion subgroup of `T`.

This is the cardinality consequence of the exact sequence
`0 → T[p] → T --p--> T → T/pT → 0`: the first isomorphism theorem identifies
`T / T[p]` with `pT`, so `|T| = |T[p]| · |pT|` and `|T| = |pT| · |T/pT|`
simultaneously, whence `|T[p]| = |T/pT|`. -/
theorem card_quot_lsmul_range_of_finite {T : Type*} [AddCommGroup T] [Finite T] (p : ℕ) :
    Nat.card (T ⧸ (LinearMap.lsmul ℤ T (p : ℤ)).range) = Nat.card (Submodule.torsionBy ℤ T p) := by
  set f : T →ₗ[ℤ] T := LinearMap.lsmul ℤ T (p : ℤ) with hf
  have hker : f.ker = Submodule.torsionBy ℤ T p := rfl
  -- `|T| = |ker f| * |T / ker f|`
  have h1 : Nat.card T = Nat.card f.ker * Nat.card (T ⧸ f.ker) :=
    Submodule.card_eq_card_quotient_mul_card f.ker
  -- `|T| = |range f| * |T / range f|`
  have h2 : Nat.card T = Nat.card f.range * Nat.card (T ⧸ f.range) :=
    Submodule.card_eq_card_quotient_mul_card f.range
  -- first isomorphism theorem: `T / ker f ≃ range f`
  have h3 : Nat.card (T ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have key : Nat.card f.ker * Nat.card (T ⧸ f.ker) =
      Nat.card f.range * Nat.card (T ⧸ f.range) := by
    rw [← h1, ← h2]
  have key2 : Nat.card f.ker * Nat.card f.range =
      Nat.card f.range * Nat.card (T ⧸ f.range) := by
    conv_lhs => rw [← h3]
    exact key
  -- cancel the common positive factor `|range f|`
  have hfin : Nat.card f.ker = Nat.card (T ⧸ f.range) := by
    have hc : Nat.card f.range * Nat.card f.ker =
        Nat.card f.range * Nat.card (T ⧸ f.range) := by
      rw [mul_comm (Nat.card f.range) (Nat.card f.ker)]
      exact key2
    exact Nat.mul_left_cancel hpos hc
  calc Nat.card (T ⧸ (LinearMap.lsmul ℤ T (p : ℤ)).range)
      = Nat.card (T ⧸ f.range) := by rw [← hf]
    _ = Nat.card f.ker := hfin.symm
    _ = Nat.card (Submodule.torsionBy ℤ T p) := by rw [hker]

end NK.GroupTheory.Abelian
