import Mathlib
import Submission.Work.ThmF.Bender.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Bender

/-- If `H` has even order and `Q` is a Sylow 2-subgroup of `H`, then `Q` has even order, hence so
does its image in `G` under `H.subtype`.

The image is a subgroup of `G` isomorphic to `Q` (the inclusion `↥H ↪ G` is injective), so it has
the same cardinality as `Q` (`Subgroup.card_map_of_injective`).  And `2 ∣ |H|` forces `2 ∣ |Q|`:
the index `[H : Q]` is odd (a Sylow subgroup has index coprime to `p`, `Sylow.card_coprime_index`),
while `|H| = [H : Q] * |Q|`; so the factor `2` must sit in `|Q|`
(`Sylow.dvd_card_of_dvd_card`). -/
theorem evenCardMapSylow {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : Even (Nat.card H)) (Q : Sylow 2 ↥H) : Even (Nat.card ((Q : Subgroup ↥H).map H.subtype)) := by
  rw [Subgroup.card_map_of_injective H.subtype_injective]
  exact even_iff_two_dvd.mpr (Q.dvd_card_of_dvd_card (even_iff_two_dvd.mp hH))

end Work.ThmF.Bender
