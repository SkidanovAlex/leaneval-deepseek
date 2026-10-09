import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The index of `⟨π^a⟩ · U^n` in `Fˣ`, keyed on the exponents themselves

`NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits` computes
`Nat.card (Fˣ ⧸ (⟨π^{m+1}⟩ ⊔ U^{n+1})) = (m+1)(q-1)q^n`.  The Lubin–Tate tower with unramified
degrees from a divisibility chain `a m` (see
`NK.LocalReciprocityLubinTate.LubinTateTowerGen`) needs the same computation keyed directly on the
exponents, i.e. for `⟨π^a⟩ ⊔ U^n`.  That is the statement recorded here (a reparametrisation of the
proved computation).

## Main result

* `NK.LocalReciprocityLubinTate.natCard_quotient_zpowers_pow_sup_higherUnits_gen`.
-/

namespace NK.LocalReciprocityLubinTate

universe u

/-- **The index of `⟨π^a⟩ · U^n` in `Fˣ`** for `a ≥ 1`, `n ≥ 1`:

`Nat.card (Fˣ ⧸ (⟨π^a⟩ ⊔ U^n)) = a·(q-1)·q^{n-1}`,  `q = residueCard F`.

This is `natCard_quotient_zpowers_pow_sup_higherUnits` with `m = a - 1` and `n = n' - 1`. -/
theorem natCard_quotient_zpowers_pow_sup_higherUnits_gen (F : Type u) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (π : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (π : F)) (a n : ℕ) (ha : 1 ≤ a)
    (hn : 1 ≤ n) :
    Nat.card (Fˣ ⧸ (Subgroup.zpowers (π ^ a) ⊔
        NK.LocalReciprocityLubinTate.higherUnits F n)) =
      a * (NK.LocalReciprocityLubinTate.residueCard F - 1) *
        NK.LocalReciprocityLubinTate.residueCard F ^ (n - 1) := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa using NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits F π hπ a' n'

end NK.LocalReciprocityLubinTate
