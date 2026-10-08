import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Artin's theorem for a finite field, in cardinal form

For a finite field `F` and a subgroup `A` of its ring automorphism group, `F^A` denotes the
fixed field of `A`.  By Artin's theorem the extension `F / F^A` has degree `|A|`
(Mathlib's `FixedPoints.finrank_eq_card`), and for a finite extension the cardinality of `F`
is `|F^A| ^ [F : F^A]` (`Module.natCard_eq_pow_finrank`).  Hence

  `|F^A| ^ |A| = |F|`.

This is the field-theoretic content of Ch. V §3 step (1) of the Bender–Suzuki development
(`Work.ThmF.ChV12.prop3_card_fixed_pow`): for `P ≤ V` of prime order `p` with `P ∩ W = 1`, the
group `C_{Q₀}(P)` of fixed points in `Q₀ ≅ F` is the fixed field of a group of automorphisms
of order `p`, so its order is the `p`-th root of `|Q₀|`.
-/

namespace Work.ThmF.ChV12

/-- **Artin's theorem, cardinal form.**  For a finite field `F` and a subgroup `A` of its
automorphism group, `|F^A| ^ |A| = |F|`. -/
theorem fixedField_card_pow {F : Type} [Field F] [Fintype F] (A : Subgroup (F ≃+* F)) :
    Nat.card ↥(FixedPoints.subfield A F) ^ Nat.card A = Nat.card F := by
  classical
  -- `F ≃+* F` is finite, being a subtype of `F → F`
  haveI : Fintype (F ≃+* F) :=
    Fintype.ofInjective (fun f : F ≃+* F => (f : F → F))
      (fun f g h => RingEquiv.ext (congrFun h))
  haveI : Fintype A := inferInstance
  have hfr : Module.finrank (FixedPoints.subfield A F) F = Nat.card A := by
    rw [FixedPoints.finrank_eq_card A F, Nat.card_eq_fintype_card]
  rw [← hfr, ← Module.natCard_eq_pow_finrank (K := (FixedPoints.subfield A F)) (V := F)]

end Work.ThmF.ChV12
