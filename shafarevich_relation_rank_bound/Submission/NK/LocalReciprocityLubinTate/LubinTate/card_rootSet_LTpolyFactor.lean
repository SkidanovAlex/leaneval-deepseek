import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Division
import Submission.NK.LocalReciprocityLubinTate.LubinTate.irreducible_LTpolyFactor
import Submission.NK.LocalReciprocityLubinTate.Basic

/-!
# The number of roots of the Eisenstein factor `X ^ (q - 1) + π`

The polynomial `LTpolyFactor π q = X ^ (q - 1) + π` (the Eisenstein factor `f(T)/T` of the standard
Lubin–Tate polynomial `π X + X ^ q`, Milne, *CFT*, §I.3) is separable over a characteristic-zero
field `F` whenever `π ≠ 0`, hence has exactly `q - 1` *distinct* roots in the algebraic closure of
`F`.  This is the cardinality input for the description of the Lubin–Tate level `K_1 = F(π_1)` as
the splitting field of `f^{[1]}(T)`, of degree `q - 1` over `F` (Milne, *op. cit.*, §I.3).

## Main result

* `card_rootSet_LTpolyFactor` — the set of roots of `X ^ (q - 1) + π` in `AlgebraicClosure F` has
  cardinality `q - 1`.
-/

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

open Polynomial

theorem card_rootSet_LTpolyFactor (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π) (q : ℕ) (hq : 2 ≤ q) :
    {x : AlgebraicClosure F | ((NK.LocalReciprocityLubinTate.LTpolyFactor (π : F) q).map
        (algebraMap F (AlgebraicClosure F))).IsRoot x}.ncard = q - 1 := by
  classical
  set P := NK.LocalReciprocityLubinTate.LTpolyFactor (π : F) q with hPdef
  -- the explicit shape `X ^ (q - 1) + C π`
  have hP : P = X ^ (q - 1) + C (π : F) := by
    rw [hPdef]; rfl
  -- `π` remains nonzero in `F` (the ring of integers is the fraction ring's subring)
  have ha : (π : F) ≠ 0 := fun h =>
    hπ.ne_zero (IsFractionRing.injective (↥(ValuativeRel.valuation F).integer) F (by
      rw [map_zero]; exact h))
  have hP0 : P ≠ 0 := by
    rw [hP]; exact (monic_X_pow_add_C (π : F) (by omega)).ne_zero
  -- `X ^ (q - 1) + π = X ^ (q - 1) - (-π)` is separable in characteristic zero
  have hsep : P.Separable := by
    have hne : (-(π : F)) ≠ 0 := neg_ne_zero.mpr ha
    have hn : ((q - 1 : ℕ) : F) ≠ 0 := by
      rw [Nat.cast_ne_zero]; omega
    have h := separable_X_pow_sub_C (-(π : F)) hn hne
    have heq : X ^ (q - 1) + C (π : F) = X ^ (q - 1) - C (-(π : F)) := by
      rw [map_neg]; ring
    rw [hP, heq]; exact h
  -- in the algebraically closed field the polynomial splits, so it has `natDegree` roots
  have hsplit : (P.map (algebraMap F (AlgebraicClosure F))).Splits := IsAlgClosed.splits _
  have hcard : Fintype.card ↑(P.rootSet (AlgebraicClosure F)) = q - 1 := by
    rw [card_rootSet_eq_natDegree hsep hsplit, hP, natDegree_X_pow_add_C]
  -- the set of roots is the `rootSet` of `P`
  have hset : {x : AlgebraicClosure F | (P.map (algebraMap F (AlgebraicClosure F))).IsRoot x}
      = P.rootSet (AlgebraicClosure F) := by
    ext x
    rw [Set.mem_ofPred_eq, mem_rootSet_of_ne (S := AlgebraicClosure F) hP0, IsRoot.def,
        aeval_def, eval₂_eq_eval_map]
  rw [hset, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  exact hcard

end NK.LocalReciprocityLubinTate.LubinTate
