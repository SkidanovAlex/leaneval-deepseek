import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The value group of the valuation induced by a place of an extension of a local field

Let `K` be a nonarchimedean local field (so that its topology is the one induced by the
`ValuativeRel`-valuation of `K`) and let `W` be a valuation subring of a field `L` which is a
`K`-algebra.  If the trace of `W` on `K` is exactly the valuation subring of `K` — i.e. the place
of `L` corresponding to `W` restricts to the given place of `K` — then the value group with zero
of the valuation `W.valuation ∘ algebraMap K L` on `K` is, as an ordered monoid with zero,
isomorphic to `WithZero (Multiplicative ℤ)`: a local field has value group `ℤ`.

The proof is a two-step composition.

* `ValuativeRel.ValueGroupWithZero.orderMonoidIso` gives an ordered isomorphism between the
  canonical value group with zero `ValueGroupWithZero K` of the valuative relation on `K` and the
  value group with zero `ValueGroup₀ (ofClass v)` of *any* valuation `v` on `K` compatible with it,
  i.e. inducing the same preorder;
* `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` computes `ValueGroupWithZero K ≃*o ℤᵐ⁰`.

Compatibility of `v := W.valuation.comap (algebraMap K L)` is exactly the hypothesis `hW`: the
valuation subrings agree, hence (`Valuation.isEquiv_iff_valuationSubring`) `v` is equivalent to
the canonical valuation, hence induces the same preorder.

-/

set_option linter.style.haveILetI false

namespace NK.LocalReciprocityLubinTate.Eval

theorem nonempty_orderIso_valueGroupZero_of_localField
    {K L : Type*} [Field K] [Field L] [Algebra K L] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (W : ValuationSubring L)
    (hW : W.comap (algebraMap K L) = (ValuativeRel.valuation K).valuationSubring) :
    Nonempty ((MonoidWithZeroHom.ofClass (W.valuation.comap (algebraMap K L))).ValueGroup₀ ≃*o
      WithZero (Multiplicative ℤ)) := by
  -- The valuation subring of the pulled-back valuation is the pull-back of the valuation subring.
  have hsub : (W.valuation.comap (algebraMap K L)).valuationSubring = W.comap (algebraMap K L) := by
    ext x
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
      ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap]
  -- ... hence it agrees with the valuation subring of the canonical valuation of `K`.
  have hsub2 : (W.valuation.comap (algebraMap K L)).valuationSubring =
      (ValuativeRel.valuation K).valuationSubring := by rw [hsub, hW]
  -- Valuations with the same valuation subring are equivalent.
  have hiso : (ValuativeRel.valuation K).IsEquiv (W.valuation.comap (algebraMap K L)) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub2.symm
  -- So the pulled-back valuation is compatible with the valuative relation on `K`.
  haveI : (W.valuation.comap (algebraMap K L)).Compatible :=
    ⟨fun x y =>
      (Valuation.vle_iff_le (ValuativeRel.valuation K) (x := x) (y := y)).trans (hiso x y)⟩
  -- Compose the two ordered isomorphisms.
  exact ⟨(ValuativeRel.ValueGroupWithZero.orderMonoidIso
      (W.valuation.comap (algebraMap K L))).symm.trans
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)⟩

end NK.LocalReciprocityLubinTate.Eval
