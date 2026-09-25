import Mathlib
import Submission.Work.ClassFieldTower.ProTwoDefs

namespace Work.ClassFieldTower

set_option linter.style.haveILetI false

open scoped Classical

/-- **`ResiduallyFiniteTwoGroup` is invariant under group isomorphisms.**

`ResiduallyFiniteTwoGroup G` says that every `g ≠ 1` in `G` has nontrivial image in some finite
`2`-group quotient of `G`.  If `e : G ≃* H` and `H` has this property, then so does `G`: given
`g ≠ 1` in `G`, apply the hypothesis to `e g ≠ 1`, obtaining a normal `N ◁ H` with `H ⧸ N` a
finite `2`-group and `e g ∉ N`; then `M := N.comap e ◁ G` has `G ⧸ M ≃* H ⧸ N`
(`QuotientGroup.congr`, using `Subgroup.map_comap_eq_self_of_surjective`), so `G ⧸ M` is again a
finite `2`-group, and `g ∉ M` because `e g ∉ N`. -/
theorem residuallyFiniteTwoGroup_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : ResiduallyFiniteTwoGroup H) : ResiduallyFiniteTwoGroup G := by
  intro g hg
  have hge : e g ≠ 1 := fun h1 => hg (e.injective (by rw [h1]; exact (map_one e).symm))
  obtain ⟨N, hN, hfin, hpg, hmk⟩ := h (e g) hge
  haveI : N.Normal := hN
  let M : Subgroup G := N.comap (e : G →* H)
  have hMN : M.Normal := hN.comap (e : G →* H)
  haveI : M.Normal := hMN
  have hmap : Subgroup.map (e : G →* H) M = N := by
    rw [Subgroup.map_comap_eq_self_of_surjective e.surjective]
  refine ⟨M, hMN, ?_, ?_, ?_⟩
  · exact Finite.of_equiv (H ⧸ N) (QuotientGroup.congr M N e hmap).symm.toEquiv
  · exact hpg.of_equiv (QuotientGroup.congr M N e hmap).symm
  · intro h1
    simp only [QuotientGroup.mk'_apply] at h1
    have hmem : g ∈ M := (QuotientGroup.eq_one_iff (N := M) g).mp h1
    have hmem' : g ∈ Subgroup.comap (e : G →* H) N := hmem
    have heN : e g ∈ N := Subgroup.mem_comap.mp hmem'
    have hmk' : QuotientGroup.mk' N (e g) = 1 := by
      simp only [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (N := N) (e g)).mpr heN
    exact hmk hmk'

end Work.ClassFieldTower
