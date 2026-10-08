import Mathlib
import Submission.Work.Hall.HallAPI.hall_card_comap_mk

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hall.SchurZassenhaus

/-- If `M ◁ G` is nontrivial and `M ≤ N`, then the image of `N` under the quotient map
`G → G ⧸ M` is strictly smaller than `N`: indeed `|N.map (mk' M)| = [N : M]` and
`|N| = |M| * [N : M]` with `|M| ≥ 2`. -/
theorem sz_card_map_mk_lt {G : Type*} [Group G] [Finite G] {N M : Subgroup G} [M.Normal]
    (hMN : M ≤ N) (hM : M ≠ ⊥) : Nat.card (N.map (QuotientGroup.mk' M)) < Nat.card N := by
  -- `|N.map (mk' M)| = [N : M]`, since the kernel of `mk' M` is `M`.
  have hcard : Nat.card (N.map (QuotientGroup.mk' M)) = M.relIndex N := by
    rw [← Subgroup.relIndex_ker N (QuotientGroup.mk' M), QuotientGroup.ker_mk']
  rw [hcard]
  -- `|N| = |M| * [N : M]` because `M ≤ N`.
  have hmul : Nat.card N = Nat.card M * M.relIndex N := by
    have h1 : Nat.card (M.subgroupOf N) * (M.subgroupOf N).index = Nat.card N :=
      Subgroup.card_mul_index (H := M.subgroupOf N)
    have h2 : Nat.card (M.subgroupOf N) = Nat.card M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMN).toEquiv
    have h3 : (M.subgroupOf N).index = M.relIndex N := rfl
    rw [h2, h3] at h1
    exact h1.symm
  rw [hmul]
  -- `|M| > 1` (nontrivial) and `[N : M] > 0`, so `[N : M] < |M| * [N : M]`.
  have hM1 : 1 < Nat.card M := Subgroup.one_lt_card_iff_ne_bot M |>.mpr hM
  have hpos : 0 < M.relIndex N := by
    rw [← hcard]
    exact Nat.card_pos
  exact lt_mul_of_one_lt_left hpos hM1

end Work.Hall.SchurZassenhaus
