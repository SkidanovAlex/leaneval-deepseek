import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Basic
import Submission.NK.LocalReciprocityLubinTate.Units.unitsQuotPrincipalUnitsEquiv
import Submission.NK.LocalReciprocityLubinTate.Units.natCard_units_quot_pow_maximalIdeal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The successive quotients `U^(n-1)/U^n` of the higher unit filtration

For a nonarchimedean local field `F` with residue cardinality `q = residueCard F` and higher
principal units `U^n = principalUnits F n = 1 + 𝔪[F]^n ≤ 𝒪[F]ˣ` (Serre, *Local Fields*, Ch. IV §1),
the successive quotient `U^(n-1)/U^n` has order `q` for every `n ≥ 2`:

`Nat.card (principalUnits F (n-1) ⧸ (principalUnits F n).subgroupOf (principalUnits F (n-1))) =
residueCard F`.

This is the classical computation `U^(n-1)/U^n ≅ 𝔪[F]^(n-1)/𝔪[F]^n ≅ 𝓀[F]` (`1 + x ↦ x`), which
is the input for the `p`-primary part of the Lubin–Tate description of the local norm residue
symbol.

The proof here avoids constructing the isomorphism explicitly.  Instead it uses the identity

`(U^n).relIndex (U^(n-1)) * (U^(n-1)).index = (U^n).index`

for the relative index of subgroups (`Subgroup.relIndex_mul_index`), together with the known orders
of the finite quotients `𝒪[F]ˣ ⧸ U^k = (𝒪[F] ⧸ 𝔪[F]^k)ˣ` of order `(q - 1) q^(k-1)`
(`Units.unitsQuotPrincipalUnitsEquiv` and `Units.natCard_units_quot_pow_maximalIdeal`).  Since
`relIndex` *is* `Nat.card (U^(n-1) ⧸ U^n)` by definition, cancelling the common factor
`(q-1) q^(n-2)` leaves exactly `q`.
-/

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate.Eval

noncomputable section

/-- **The order of `𝒪[F]ˣ ⧸ U^k`** is `(q - 1) q^(k - 1)` for `k ≥ 1`, where `q = residueCard F`.

The reduction map `𝒪[F]ˣ →* (𝒪[F] ⧸ 𝔪[F]^k)ˣ` is surjective with kernel `U^k = 1 + 𝔪[F]^k`
(`Units.unitsQuotPrincipalUnitsEquiv`), and the target has `(q-1) q^(k-1)` elements
(`Units.natCard_units_quot_pow_maximalIdeal`). -/
theorem natCard_units_quot_principalUnits (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (k : ℕ) (hk : 1 ≤ k) :
    Nat.card ((↥𝒪[F])ˣ ⧸ NK.LocalReciprocityLubinTate.principalUnits F k) =
      (NK.LocalReciprocityLubinTate.residueCard F - 1) *
        NK.LocalReciprocityLubinTate.residueCard F ^ (k - 1) := by
  obtain ⟨e⟩ := NK.LocalReciprocityLubinTate.Units.unitsQuotPrincipalUnitsEquiv F k
  rw [Nat.card_congr e.toEquiv]
  exact NK.LocalReciprocityLubinTate.Units.natCard_units_quot_pow_maximalIdeal F k hk

/-- **The residue cardinality of a nonarchimedean local field is at least `2`**: the residue field
is a field, hence nontrivial, and finite. -/
theorem two_le_residueCard (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : 2 ≤ NK.LocalReciprocityLubinTate.residueCard F := by
  have h0 : Nat.card 𝓀[F] ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩
  have h1 : Nat.card 𝓀[F] ≠ 1 := by
    intro h
    haveI : Subsingleton 𝓀[F] := (Nat.card_eq_one_iff_unique.mp h).1
    obtain ⟨a, b, hab⟩ := exists_pair_ne 𝓀[F]
    exact hab (Subsingleton.elim a b)
  show 2 ≤ Nat.card 𝓀[F]
  omega

/-- **The pure arithmetic step**: if `x * ((q-1) q^(n-2)) = (q-1) q^(n-1)` with `q ≥ 2` and
`n ≥ 2`, then `x = q`.  The common factor `(q-1) q^(n-2)` is nonzero and can be cancelled. -/
theorem eq_of_mul_sub_one_pow_mul_eq {x q n : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n)
    (h : x * ((q - 1) * q ^ (n - 2)) = (q - 1) * q ^ (n - 1)) : x = q := by
  have hC : 0 < (q - 1) * q ^ (n - 2) :=
    Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hCq : (q - 1) * q ^ (n - 1) = ((q - 1) * q ^ (n - 2)) * q := by
    have hexp : n - 2 + 1 = n - 1 := by omega
    rw [← hexp, pow_succ]
    ring
  exact Nat.mul_right_cancel hC (by rw [h, hCq]; ring)

theorem natCard_principalUnits_quotient (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (NK.LocalReciprocityLubinTate.principalUnits F (n - 1) ⧸
      (NK.LocalReciprocityLubinTate.principalUnits F n).subgroupOf
        (NK.LocalReciprocityLubinTate.principalUnits F (n - 1))) =
      NK.LocalReciprocityLubinTate.residueCard F := by
  -- `relIndex` of `U^n` in `U^(n-1)` *is* the cardinality in question
  change (NK.LocalReciprocityLubinTate.principalUnits F n).relIndex
    (NK.LocalReciprocityLubinTate.principalUnits F (n - 1)) =
      NK.LocalReciprocityLubinTate.residueCard F
  -- `U^n ≤ U^(n-1)`, so the relative index satisfies `relIndex * index = index`
  have hle : NK.LocalReciprocityLubinTate.principalUnits F n ≤
      NK.LocalReciprocityLubinTate.principalUnits F (n - 1) :=
    NK.LocalReciprocityLubinTate.principalUnits_antitone F (by omega)
  have hkey := Subgroup.relIndex_mul_index hle
  -- replace the two indices by the orders of the corresponding quotients of `𝒪[F]ˣ`
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card] at hkey
  rw [natCard_units_quot_principalUnits F n (by omega),
    natCard_units_quot_principalUnits F (n - 1) (by omega)] at hkey
  rw [show (n - 1) - 1 = n - 2 from by omega] at hkey
  exact eq_of_mul_sub_one_pow_mul_eq (two_le_residueCard F) hn hkey

end

end NK.LocalReciprocityLubinTate.Eval
