import Mathlib
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- **Peterfalvi I Ch. I §1.**  A subgroup `X` of `G` fixing at least three points of
`Ω = G ⧸ H` has odd order.

Indeed, three (or even two) distinct fixed points have distinct stabilisers `H₁ ≠ H₂`
(a point of `Ω` is determined by its stabiliser, `mk_eq_of_conj_eq`), and `X ≤ H₁ ⊓ H₂`;
the intersection of two distinct conjugates of a strongly embedded subgroup has odd order,
so `|X|` divides an odd number. -/
theorem odd_card_of_fixes_three {G : Type} [Group G] [Finite G] {H X : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard) : Odd (Nat.card X) := by
  classical
  have h2 : 1 < (fixedPts H X).ncard := by omega
  obtain ⟨ω1, hω1, ω2, hω2, hne⟩ := (Set.one_lt_ncard (s := fixedPts H X)).mp h2
  obtain ⟨g1, rfl⟩ := QuotientGroup.mk_surjective ω1
  obtain ⟨g2, rfl⟩ := QuotientGroup.mk_surjective ω2
  have hXle1 : X ≤ conj g1 H := by
    rw [← stabilizer_mk H g1]
    exact mem_fixedPts_iff_le_stabilizer.mp hω1
  have hXle2 : X ≤ conj g2 H := by
    rw [← stabilizer_mk H g2]
    exact mem_fixedPts_iff_le_stabilizer.mp hω2
  have hconjne : conj g1 H ≠ conj g2 H := by
    intro heq
    exact hne (mk_eq_of_conj_eq hH heq)
  exact Odd.of_dvd (Subgroup.card_dvd_of_le (le_inf hXle1 hXle2)) (card_inf_conj_odd hH hconjne)

end Work.ThreePoints
