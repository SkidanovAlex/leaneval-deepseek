import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Basic
import Submission.NK.LocalReciprocityLubinTate.Audit.PadicInstance
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The residue cardinality of `ℚ_[p]` is `p`

`NK.LocalReciprocityLubinTate.residueCard F = Nat.card 𝓀[F]` is the cardinality of the residue
field of a nonarchimedean local field, where `𝒪[F] = Valuation.integer (ValuativeRel.valuation F)`
is the ring of integers cut out by the valuative relation and `𝓀[F]` is its residue field.

For `F = ℚ_[p]` the residue field is `𝔽_p = ZMod p`, so `residueCard ℚ_[p] = p`.  Concretely,

* the valuative relation on `ℚ_[p]` is the one induced by the multiplicative `p`-adic valuation
  `Padic.mulValuation`, so its ring of integers is `{x : ℚ_[p] | mulValuation x ≤ 1}`, which is the
  unit ball `ℤ_[p] = {x : ℚ_[p] | ‖x‖ ≤ 1}` of the `p`-adic norm
  (`Mathlib.NumberTheory.Padics.PadicIntegers`);
* Mathlib's `PadicInt.residueField` is a ring isomorphism
  `IsLocalRing.ResidueField ℤ_[p] ≃+* ZMod p` and `Nat.card (ZMod p) = p`
  (`Nat.card_zmod`).

The only arithmetic input is `mulValuation x ≤ 1 ↔ ‖x‖ ≤ 1`, i.e. `Padic.norm_le_one_iff_val_nonneg`
combined with the description `mulValuation x = exp (-x.valuation)` of the multiplicative valuation.
-/

open scoped ValuativeRel WithZero

namespace NK.LocalReciprocityLubinTate.Audit

/-- The unit ball of the `p`-adic norm is the set on which the multiplicative `p`-adic valuation
`Padic.mulValuation` is `≤ 1`: for `x ≠ 0` one has `mulValuation x = exp (-x.valuation)`, and
`exp (-v) ≤ exp 0 ↔ 0 ≤ v`.

This is the arithmetic link between `Padic.mulValuation` (out of which the `ValuativeRel` on `ℚ_[p]`
is built) and the norm (out of which `ℤ_[p]` is built). -/
lemma padic_mulValuation_le_one_iff_norm_le_one (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    Padic.mulValuation x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  rw [Padic.norm_le_one_iff_val_nonneg]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [show Padic.mulValuation (p := p) x = WithZero.exp (-x.valuation) from by
        simp [Padic.mulValuation, hx],
      show (1 : ℤᵐ⁰) = WithZero.exp (0 : ℤ) from WithZero.exp_zero.symm,
      WithZero.exp_le_exp, neg_nonpos]

/-- The canonical valuation `ValuativeRel.valuation ℚ_[p]` attached to the valuative relation of
`ℚ_[p]` and the `p`-adic multiplicative valuation `Padic.mulValuation` generate the same value
relation, hence have the same unit ball: both are `Valuation.Compatible` with `≤ᵥ`. -/
lemma padic_valuation_le_one_iff_mulValuation_le_one (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    ValuativeRel.valuation ℚ_[p] x ≤ 1 ↔ Padic.mulValuation x ≤ 1 := by
  have h1 := (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation ℚ_[p]) x 1)
  have h2 := (Valuation.Compatible.vle_iff_le (v := Padic.mulValuation (p := p)) x 1)
  simp only [map_one] at h1 h2
  exact h1.symm.trans h2

/-- Membership in the ring of integers `𝒪[ℚ_[p]]` of the valuative relation is membership in the
unit ball `ℤ_[p]` of the `p`-adic norm. -/
lemma padic_valuation_le_one_iff_norm_le_one (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    ValuativeRel.valuation ℚ_[p] x ≤ 1 ↔ ‖x‖ ≤ 1 :=
  (padic_valuation_le_one_iff_mulValuation_le_one p x).trans
    (padic_mulValuation_le_one_iff_norm_le_one p x)

/-- **The ring of integers of `ℚ_[p]` is `ℤ_[p]`**: the two subtypes of `ℚ_[p]`,
`𝒪[ℚ_[p]] = {x | valuation x ≤ 1}` and `ℤ_[p] = {x | ‖x‖ ≤ 1}`, have the same underlying set, and
the identity map is a ring isomorphism between them (all ring operations are the ones induced from
`ℚ_[p]`). -/
noncomputable def padicIntegerEquiv (p : ℕ) [Fact p.Prime] :
    ↥(Valuation.integer (ValuativeRel.valuation ℚ_[p])) ≃+* ℤ_[p] where
  toFun x := ⟨x.1, (padic_valuation_le_one_iff_norm_le_one p x.1).mp x.2⟩
  invFun y := ⟨y.1, (padic_valuation_le_one_iff_norm_le_one p y.1).mpr y.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- The residue field of `ℚ_[p]` has `p` elements. -/
theorem residueCard_padic (p : ℕ) [Fact p.Prime] :
    NK.LocalReciprocityLubinTate.residueCard ℚ_[p] = p := by
  show Nat.card (IsLocalRing.ResidueField
    ↥(Valuation.integer (ValuativeRel.valuation ℚ_[p]))) = p
  rw [Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (padicIntegerEquiv p)).toEquiv,
      Nat.card_congr (PadicInt.residueField (p := p)).toEquiv, Nat.card_zmod]

end NK.LocalReciprocityLubinTate.Audit
