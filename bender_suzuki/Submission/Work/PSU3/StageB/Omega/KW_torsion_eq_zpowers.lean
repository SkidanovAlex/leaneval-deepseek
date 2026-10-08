/-
# `Work.PSU3.StageB.Omega.KW_torsion_eq_zpowers`

The torsion of `KW` lies in `⟨ζ⟩`: if `d ^ orderOf ζ = 1` then `d ∈ Subgroup.zpowers ζ`.

`fr.KW ≤ D = H ∩ H^t` is embedded injectively into `(E n)ˣ` by `fr.κ`
(`CoarseFrame.κ_injective`), and the unit group of the finite field `E n = GF(2^(2n))` is
cyclic, so `KW` is cyclic (`isCyclic_of_injective`).  In a *finite cyclic* group the set
`{x | x ^ orderOf y = 1}` is the unique subgroup of order `gcd (Nat.card A) (orderOf y)`,
which equals `⟨y⟩`; this is `mem_zpowers_of_pow_orderOf_eq_one` below, proved by comparing
the cardinality of `Subgroup.zpowers y` with the count `#{a | a ^ orderOf y = 1} ≤ orderOf y`
(`IsCyclic.card_pow_eq_one_le`).
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.orbE_card
import Submission.Work.PSU3.StageB.fixedUnits_card
import Submission.Work.PSU3.StageB.Omega.API

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.Omega

/-- **In a finite cyclic group, the elements killed by `orderOf y` lie in `⟨y⟩`.**

Indeed `{a | a ^ orderOf y = 1}` is a subgroup containing `⟨y⟩` and, by
`IsCyclic.card_pow_eq_one_le`, its cardinality is at most `orderOf y = Nat.card ⟨y⟩`. -/
theorem mem_zpowers_of_pow_orderOf_eq_one {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {x y : A} (h : x ^ orderOf y = 1) : x ∈ Subgroup.zpowers y := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  -- `⟨y⟩` is contained in the "`orderOf y`-torsion".
  have hle : (Subgroup.zpowers y : Set A) ⊆ {a | a ^ orderOf y = 1} := by
    intro a ha
    show a ^ orderOf y = 1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_natCast (y ^ k) (orderOf y), ← zpow_mul, zpow_mul', zpow_natCast,
      pow_orderOf_eq_one, one_zpow]
  -- and the torsion has at most `orderOf y` elements.
  have hcard : Nat.card {a : A // a ^ orderOf y = 1} ≤ Nat.card ↥(Subgroup.zpowers y) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Fintype.card_zpowers]
    exact IsCyclic.card_pow_eq_one_le (orderOf_pos y)
  have heq : (Subgroup.zpowers y : Set A) = {a | a ^ orderOf y = 1} := by
    apply Set.eq_of_subset_of_ncard_le hle
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hcard
  have hx : x ∈ ({a | a ^ orderOf y = 1} : Set A) := h
  rwa [← heq] at hx

/-- **`KW` is cyclic**: `fr.κ` embeds it into the (cyclic) unit group of the finite field
`E n`. -/
theorem isCyclic_KW {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) : IsCyclic ↥(fr.KW) :=
  isCyclic_of_injective fr.κ fr.κ_injective

theorem KW_torsion_eq_zpowers {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) (hn : 1 ≤ n) {d : fr.KW}
    (hd : d ^ orderOf fr.ζ = 1) : d ∈ Subgroup.zpowers fr.ζ := by
  haveI : IsCyclic ↥(fr.KW) := isCyclic_KW fr
  exact mem_zpowers_of_pow_orderOf_eq_one hd

end Work.PSU3.StageB.Omega
