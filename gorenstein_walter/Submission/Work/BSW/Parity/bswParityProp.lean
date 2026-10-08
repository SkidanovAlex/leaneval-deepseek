import Mathlib
import Submission.Work.BSW.Concl

namespace Work.BSW.Parity

/-- **Bender's parity fact**: `|K|` is even.

The element `t` has order `2` and lies in `K`, so the cyclic subgroup `⟨t⟩ ≤ K` has order `2`;
Lagrange's theorem (`Subgroup.card_dvd_of_le`) then gives `2 ∣ |K|`.

(Equivalently, as in the remark above: `K` is abelian with the unique involution `t`
(`Work.BSW.orderOf_eq_two_of_mem_K`), so the squaring endomorphism `K → K` has the two-element
kernel `{1, t}` and `|K| = 2 * |K²|`.) -/
theorem bswParityProp : Work.BSW.BSWParityProp := by
  intro G _ _ t s K h
  have htK : t ∈ K := h.2.2.1
  have hzg : Subgroup.zpowers t ≤ K := Subgroup.zpowers_le.mpr htK
  have hdvd : Nat.card (Subgroup.zpowers t : Subgroup G) ∣ Nat.card K :=
    Subgroup.card_dvd_of_le hzg
  have hcard : Nat.card (Subgroup.zpowers t : Subgroup G) = 2 := by
    rw [Nat.card_zpowers]
    exact h.1
  rw [hcard] at hdvd
  exact even_iff_two_dvd.mpr hdvd

end Work.BSW.Parity
