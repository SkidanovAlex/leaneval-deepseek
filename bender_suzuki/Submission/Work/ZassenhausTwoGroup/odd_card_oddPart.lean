import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

/-- `|O_{2'}(Q)| = |O_{2'}(↥Q)|`: `oddPart Q` is the image of the `2'`-core of `Q` along the
injective inclusion `Q.subtype`. -/
theorem card_oddPart' {G : Type} [Group G] (Q : Subgroup G) :
    Nat.card (oddPart Q) = Nat.card (Work.Fitting.pPrimeCore 2 ↥Q) := by
  rw [oddPart]
  exact Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)

/-- `O_{2'}(Q)` is a `2'`-group, i.e. its order is odd. -/
theorem isPiNat_odd {n : ℕ} (h : Work.Fitting.IsPiNat (fun q => q ≠ 2) n) : Odd n := by
  rw [← Nat.not_even_iff_odd]
  intro hn
  exact h 2 Nat.prime_two (even_iff_two_dvd.mp hn) rfl

/-- The odd part `O_{2'}(Q)` of any subgroup `Q` of a finite group has odd order. -/
theorem odd_card_oddPart {G : Type} [Group G] [Finite G] {Q : Subgroup G} :
    Odd (Nat.card (Work.ZassenhausTwoGroup.oddPart Q)) := by
  rw [card_oddPart' Q]
  exact isPiNat_odd (Work.Fitting.piCore_isPiNat ↥Q (fun q => q ≠ 2))

end Work.ZassenhausTwoGroup
