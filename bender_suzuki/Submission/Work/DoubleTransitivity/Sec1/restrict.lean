import Mathlib
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Restricting a Bender subgroup to a subgroup of divisible order

If `H` is a Bender subgroup for `p` of `G` and `X ≤ G` meets `H` in a subgroup of order
divisible by `p`, then `H ∩ X = H.subgroupOf X` is a Bender subgroup for `p` of `X`.

The whole content is that conjugation inside `X` agrees with conjugation in `G` followed by
intersection with `X`: for `x : X`,
`conj x (H.subgroupOf X) = (conj (x : G) H).subgroupOf X`,
so `(H.subgroupOf X) ∩ conj x (H.subgroupOf X)` is the trace on `X` of `H ∩ H^(x:G)`, whose
order divides `|H ∩ H^(x:G)|`.
-/

namespace Work.DoubleTransitivity.Sec1

open Submission.Blueprint

/-- Conjugating a restricted subgroup is restricting the conjugate: for `x : X`,
`conj x (H.subgroupOf X) = (conj (x : G) H).subgroupOf X`. -/
lemma conj_subgroupOf {G : Type} [Group G] {H X : Subgroup G} (x : X) :
    conj x (H.subgroupOf X) = (conj (x : G) H).subgroupOf X := by
  ext y
  rw [mem_conj, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_conj]
  norm_cast

/-- The order of `(H.subgroupOf X) ∩ conj x (H.subgroupOf X)` divides the order of
`H ∩ conj x H` in the ambient group. -/
lemma card_inf_conj_subgroupOf_dvd {G : Type} [Group G] {H X : Subgroup G} (x : X) :
    Nat.card ↥(H.subgroupOf X ⊓ conj x (H.subgroupOf X)) ∣
      Nat.card ↥(H ⊓ conj (x : G) H) := by
  rw [conj_subgroupOf]
  rw [show H.subgroupOf X ⊓ (conj (x : G) H).subgroupOf X
      = Subgroup.comap X.subtype (H ⊓ conj (x : G) H) from by
    rw [Subgroup.comap_inf]; rfl]
  exact Subgroup.card_comap_dvd_of_injective (H ⊓ conj (x : G) H) X.subtype
    (Subgroup.subtype_injective X)

theorem restrict {G : Type} [Group G] {p : ℕ} {H X : Subgroup G}
    (h : IsBenderFor p H) (hX : p ∣ Nat.card ↥(H ⊓ X)) :
    IsBenderFor p (H.subgroupOf X) := by
  refine ⟨?_, ?_⟩
  · rw [← Subgroup.card_subtype X (H.subgroupOf X), Subgroup.subgroupOf_map_subtype]
    exact hX
  · intro x hx
    have hxH : (x : G) ∉ H := fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem)
    intro hdvd
    exact h.2 (x : G) hxH (hdvd.trans (card_inf_conj_subgroupOf_dvd x))

end Work.DoubleTransitivity.Sec1
