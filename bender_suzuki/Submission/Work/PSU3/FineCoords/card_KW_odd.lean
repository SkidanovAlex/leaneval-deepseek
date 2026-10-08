import Mathlib
import Submission.Work.PSU3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.FineCoords

open Work.PSU3

set_option linter.style.haveILetI false

/-- The unit group of `E n = GF(2^{2n})` has odd order: a finite field of characteristic `2`
has `2 ^ d` elements (`d ≥ 1`), hence `2 ^ d - 1` units. -/
private lemma odd_card_units_E (n : ℕ) : Odd (Nat.card (E n)ˣ) := by
  letI : Fintype (E n) := Fintype.ofFinite _
  have hchar : ringChar (E n) = 2 := ringChar.eq (E n) 2
  have hmod : Fintype.card (E n) % 2 = 0 := FiniteField.even_card_of_char_two hchar
  have heven : Even (Nat.card (E n)) := by
    rw [Nat.card_eq_fintype_card, Nat.even_iff]
    exact hmod
  rw [Nat.card_units (E n)]
  exact Nat.Even.sub_odd (Nat.card_pos (α := E n)) heven odd_one

/-- `KW` is embedded by `κ` into the odd-order group `(E n)ˣ`; as a subgroup it has order
dividing `Nat.card (E n)ˣ`, hence odd. -/
theorem card_KW_odd {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) : Odd (Nat.card fr.KW) := by
  have h1 : Nat.card fr.KW = Nat.card fr.κ.range :=
    Nat.card_congr (Equiv.ofBijective fr.κ.rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr fr.κ_injective,
       MonoidHom.rangeRestrict_surjective fr.κ⟩)
  have hdvd : Nat.card fr.κ.range ∣ Nat.card (E n)ˣ :=
    Subgroup.card_subgroup_dvd_card fr.κ.range
  rw [h1]
  exact (odd_card_units_E n).of_dvd_nat hdvd

end Work.PSU3.FineCoords
