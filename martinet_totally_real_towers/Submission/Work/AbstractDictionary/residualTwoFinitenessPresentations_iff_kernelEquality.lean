import Mathlib
import Submission.Work.AbstractDictionary.Defs
import Submission.Work.AbstractDictionary.Helpers
import Submission.Work.ShafarevichKoch.ProTwoClosed

/-!
# `Work.AbstractDictionary` -- the residual `2`-finiteness side condition *is* the kernel equality

**Namespace** `Work.AbstractDictionary`; module
`Submission.Work.AbstractDictionary.residualTwoFinitenessPresentations_iff_kernelEquality`.

`Work.AbstractDictionary.Defs` isolates the residual finiteness side condition

```
ResidualTwoFinitenessPresentations Γ
```

-- "every abstract group presented by a *closed* pro-`2` presentation of `Γ` is residually a finite
`2`-group" -- and records in its docstring that, *in this setting*, it is equivalent to the abstract
kernel equality itself.  This file proves that equivalence.

* **`⟹`** is `Work.AbstractDictionary.ker_eq_normalClosure_of_residualTwoFiniteness`
  (`Helpers.lean`), i.e. `Work.ShafarevichKoch.ker_eq_normalClosure_of_closed` with the relator set
  reindexed; it needs no further input.

* **`⟸`** is the substance of the statement, and it is where the hypothesis
  `ResiduallyFiniteTwoGroup Γ` is used.  Suppose the abstract kernel equality
  `ker (FreeGroup.lift gen) = ⟪S⟫` holds for every densely generating family `gen` and every
  relator set `S` satisfying the closed condition.  Given such `gen`, `S`, the presentation map
  factors as

  `FreeGroup (Fin d) ⧸ ⟪S⟫ ≃* FreeGroup (Fin d) ⧸ ker (FreeGroup.lift gen) ≃* (FreeGroup.lift gen).range`,

  a subgroup of `Γ`.  Subgroups of a residually finite `2`-group are residually finite `2`-groups
  (`Work.ShafarevichKoch.residuallyFiniteTwoGroup_of_injective`), and the property is invariant
  under isomorphism, so the presented group is residually a finite `2`-group.  The density
  hypothesis `DenseGenerating gen` is *not* used: exactly as in
  `Work.ShafarevichKoch.residuallyFiniteTwoGroup_presented`, only the injectivity of the descended
  map matters.

Note the asymmetry: the `⟹`-direction is a general group-theoretic conversion, while the
`⟸`-direction is what makes `ResidualTwoFinitenessPresentations` *not* an extra hypothesis but a
restatement of the abstract kernel equality -- so the abstract dictionary of
`Work.AbstractDictionary.Main` assumes nothing beyond the kernel equality itself.

## Contents

* `residuallyFiniteTwoGroup_of_mulEquiv'` -- the universe-polymorphic form of
  `Work.ClassFieldTower.residuallyFiniteTwoGroup_of_mulEquiv` (that lemma is pinned to `Type 0`,
  while the subgroup `(FreeGroup.lift gen).range` lives in the universe of `Γ`);
* `residualTwoFinitenessPresentations_iff_kernelEquality` -- **the target**.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Classical

namespace Work.AbstractDictionary

/-- **`ResiduallyFiniteTwoGroup` is invariant under isomorphism**, in the universe generality
needed here.

This is `Work.ClassFieldTower.residuallyFiniteTwoGroup_of_mulEquiv`, with the two groups allowed to
live in arbitrary universes (the published version fixes them in `Type 0`, while the subgroup
`(FreeGroup.lift gen).range` of the target has the universe of `Γ`).  Given `g ≠ 1` in `G`, apply
the hypothesis to `e g ≠ 1` in `H` to get a normal `N ◁ H` with `H ⧸ N` a finite `2`-group and
`e g ∉ N`; then `M := N.comap e ◁ G` has `G ⧸ M ≃* H ⧸ N` (`QuotientGroup.congr`, using
`Subgroup.map_comap_eq_self_of_surjective`), so `G ⧸ M` is again a finite `2`-group, and `g ∉ M`
because `e g ∉ N`. -/
theorem residuallyFiniteTwoGroup_of_mulEquiv' {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Work.ClassFieldTower.ResiduallyFiniteTwoGroup H) :
    Work.ClassFieldTower.ResiduallyFiniteTwoGroup G := by
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

/-- **The residual `2`-finiteness side condition of the abstract dictionary is equivalent to the
abstract kernel equality.**

In the setting of `Work.AbstractDictionary.Defs` -- `Γ` a *residually finite `2`* topological group
-- the condition

> every abstract group presented by a closed pro-`2` presentation of `Γ` is residually a finite
> `2`-group

is exactly the statement that the closed normal closure of the relators is the whole relation
kernel:

> for every densely generating family `gen : Fin d → Γ` and every finite relator set `S` whose
> elements die in `Γ` and which generates the kernel *closedly*, one has
> `ker (FreeGroup.lift gen) = ⟪S⟫` abstractly.

* `⟹`: `ker_eq_normalClosure_of_residualTwoFiniteness` (`Helpers.lean`).
* `⟸`: the kernel equality identifies `FreeGroup (Fin d) ⧸ ⟪S⟫` with the subgroup
  `(FreeGroup.lift gen).range ≤ Γ`, and residual `2`-finiteness passes to subgroups
  (`Work.ShafarevichKoch.residuallyFiniteTwoGroup_of_injective`).

This is why `Work.AbstractDictionary.Main` can assume the abstract presentation of `Γ` outright:
the side condition it carries is not an extra hypothesis, it is the same condition. -/
theorem residualTwoFinitenessPresentations_iff_kernelEquality {Γ : Type*} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] (hΓ : Work.ClassFieldTower.ResiduallyFiniteTwoGroup Γ) :
    Work.AbstractDictionary.ResidualTwoFinitenessPresentations (Γ := Γ) ↔
      (∀ (d : ℕ) (gen : Fin d → Γ) (S : Finset (FreeGroup (Fin d))),
        Work.RelatorRank.DenseGenerating gen →
        (∀ s ∈ S, FreeGroup.lift gen s = 1) →
        Work.AbstractDictionary.ClosedNormalGeneratesTwo (MonoidHom.ker (FreeGroup.lift gen)) S →
        MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (S : Set (FreeGroup (Fin d)))) := by
  classical
  constructor
  · -- closed presentation + residual `2`-finiteness of the presented group `⟹` abstract kernel
    -- equality
    intro hres d gen S hgen hS hclosed
    exact ker_eq_normalClosure_of_residualTwoFiniteness hres hgen hS hclosed
  · -- abstract kernel equality `⟹` the presented group is a subgroup of `Γ`, hence residually a
    -- finite `2`-group
    intro hker d gen S hgen hS hclosed
    have hK : MonoidHom.ker (FreeGroup.lift gen) =
        Subgroup.normalClosure (S : Set (FreeGroup (Fin d))) := hker d gen S hgen hS hclosed
    -- subgroups of a residually finite `2`-group are residually finite `2`-groups
    have hsub : Work.ClassFieldTower.ResiduallyFiniteTwoGroup ↥(FreeGroup.lift gen).range :=
      Work.ShafarevichKoch.residuallyFiniteTwoGroup_of_injective
        (Subgroup.subtype (FreeGroup.lift gen).range) Subtype.coe_injective hΓ
    -- `(FreeGroup (Fin d)) ⧸ ker (lift gen) ≃* range`
    have hq : Work.ClassFieldTower.ResiduallyFiniteTwoGroup
        (FreeGroup (Fin d) ⧸ MonoidHom.ker (FreeGroup.lift gen)) :=
      residuallyFiniteTwoGroup_of_mulEquiv'
        (QuotientGroup.quotientKerEquivRange (FreeGroup.lift gen)) hsub
    -- `ker (lift gen) = ⟪S⟫` identifies the two quotients of the free group
    have hmap : Subgroup.map (MulEquiv.refl (FreeGroup (Fin d)))
        (MonoidHom.ker (FreeGroup.lift gen)) =
        Subgroup.normalClosure (S : Set (FreeGroup (Fin d))) := by
      simpa using hK
    have e : (FreeGroup (Fin d) ⧸ MonoidHom.ker (FreeGroup.lift gen)) ≃*
        (FreeGroup (Fin d) ⧸ Subgroup.normalClosure (S : Set (FreeGroup (Fin d)))) :=
      QuotientGroup.congr _ _ (MulEquiv.refl _) hmap
    exact residuallyFiniteTwoGroup_of_mulEquiv' e.symm hq

end Work.AbstractDictionary
