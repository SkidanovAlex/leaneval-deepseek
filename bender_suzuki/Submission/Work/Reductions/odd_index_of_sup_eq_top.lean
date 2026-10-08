import Mathlib
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Reductions

/-- If `L` is a normal subgroup of `G` with `L ⊔ D = ⊤` and `D` has odd order, then the
index of `L` in `G` is odd.

Indeed `G ⧸ L` is the image of `D` under the quotient map, so `L.index = |G ⧸ L|` is the
index of the kernel of `↥D →* G ⧸ L`, which divides `Nat.card D`; an odd number has only
odd divisors. -/
theorem odd_index_of_sup_eq_top {G : Type} [Group G] {L D : Subgroup G} (hL : L.Normal)
    (hLD : L ⊔ D = ⊤) (hodd : Odd (Nat.card D)) : Odd L.index := by
  haveI := hL
  -- The image of `D` under the quotient map `G →* G ⧸ L` is everything.
  have hmap : Subgroup.map (QuotientGroup.mk' L) D = ⊤ := by
    have h := Subgroup.map_sup L D (QuotientGroup.mk' L)
    rw [hLD, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective L)] at h
    have hbot : Subgroup.map (QuotientGroup.mk' L) L = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hbot, bot_sup_eq] at h
    exact h.symm
  -- The restriction of the quotient map to `D`.
  let f : D →* G ⧸ L := (QuotientGroup.mk' L).comp D.subtype
  have hrange : f.range = ⊤ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  -- Its kernel has index `Nat.card (G ⧸ L) = L.index` inside `D`.
  have hker : f.ker.index = L.index := by
    rw [Subgroup.index_ker, hrange, Subgroup.index_eq_card]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  -- The index of a subgroup of `D` divides `Nat.card D`.
  have hdvd : L.index ∣ Nat.card D := by
    rw [← hker]
    exact Subgroup.index_dvd_card f.ker
  exact Odd.of_dvd_nat hodd hdvd

end Work.Reductions
