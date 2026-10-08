import Mathlib
import Submission.Work.AppXIDickson.card_center_le_two_of_ne_top

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIDickson

/-- A subgroup `K` of a finite group `M`, all of whose non-identity elements have order `2`,
has at most two elements, provided `M` has a unique element of order `2`.

Indeed, if `|K| ≥ 3` there are two distinct non-identity elements `a b : K`; both have
order `2` as elements of `M`, so the uniqueness hypothesis forces `a = b`, a contradiction. -/
theorem card_le_two_of_subgroup {M : Type*} [Group M] [Finite M]
    (K : Subgroup M)
    (hK : ∀ k : K, k ≠ 1 → orderOf (k : M) = 2)
    (huniq : ∀ x y : M, orderOf x = 2 → orderOf y = 2 → x = y) :
    Nat.card K ≤ 2 := by
  by_contra hle
  rw [not_le] at hle
  have hS3 : 3 ≤ Nat.card K := by omega
  obtain ⟨a, b, ha1, hb1, hab⟩ := exists_two_ne_of_three_le_card (1 : K) hS3
  have ha2 : orderOf (a : M) = 2 := hK a ha1
  have hb2 : orderOf (b : M) = 2 := hK b hb1
  exact hab (Subtype.ext (huniq (a : M) (b : M) ha2 hb2))

end Work.AppXIDickson
