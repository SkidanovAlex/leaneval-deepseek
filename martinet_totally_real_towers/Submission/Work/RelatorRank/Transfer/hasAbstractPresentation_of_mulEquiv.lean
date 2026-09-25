import Mathlib
import Submission.Work.RelatorRank.Bridge

/-!
# `Work.RelatorRank.Transfer` -- transport of abstract presentations along an isomorphism

**Namespace** `Work.RelatorRank.Transfer`; module
`Submission.Work.RelatorRank.Transfer.hasAbstractPresentation_of_mulEquiv`.

A presentation is an isomorphism-invariant property of a group: if `e : G ≃* H` and `G` admits a
presentation with `d` generators and at most `r` relators, then so does `H`, with *the same*
relator set.  Concretely, from a datum `P : AbstractPresentationData G d r` we obtain one for `H`
by transporting the generating family (`gen' := fun i => e (P.gen i)`) and reusing `P.rel`:

* `generating` -- a surjective homomorphism carries `⊤ = closure (range gen)` onto
  `closure (range (e ∘ gen))` (`MonoidHom.map_closure` plus `Subgroup.map_top_of_surjective`);
* `ker_eq` -- `FreeGroup.lift (e ∘ gen) = e ∘ FreeGroup.lift gen` by the universal property of the
  free group, and composition with an injective map does not change the kernel.

The helper `ker_lift_comp_mulEquiv` records the second half for an arbitrary family, which is the
topology-free analogue of `Work.RelatorRank.ker_lift_comp_continuousMulEquiv`.
-/

set_option autoImplicit false

namespace Work.RelatorRank.Transfer

/-- **The presentation kernel does not change under an isomorphism.** For an isomorphism of groups
`e : G ≃* H` and any family `gen : ι → G`, the kernels of `FreeGroup.lift gen` and of
`FreeGroup.lift (fun i => e (gen i))` coincide (as subgroups of the free group on `ι`).

This is the abstract-group analogue of
`Work.RelatorRank.ker_lift_comp_continuousMulEquiv`. -/
theorem ker_lift_comp_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {ι : Type*}
    (gen : ι → G) :
    MonoidHom.ker (FreeGroup.lift fun i => e (gen i)) = MonoidHom.ker (FreeGroup.lift gen) := by
  have hcomp : FreeGroup.lift (fun i => e (gen i))
      = (e : G →* H).comp (FreeGroup.lift gen) := by
    refine MonoidHom.ext fun x => ?_
    exact (FreeGroup.lift_unique ((e : G →* H).comp (FreeGroup.lift gen))
      (fun i => by simp) (x := x)).symm
  rw [hcomp, MonoidHom.ker_comp_of_injective _ _ e.injective]

/-- **A surjective homomorphism carries generation to generation.**  If `gen : ι → G` generates
`G` and `f : G →* H` is surjective, then `f ∘ gen` generates `H`. -/
theorem generating_comp_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) {ι : Type*} (gen : ι → G) (h : Generating gen) :
    Generating (fun i => f (gen i)) := by
  rw [generating_iff] at h ⊢
  have hrange : Set.range (fun i => f (gen i)) = f '' Set.range gen := by
    ext h
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨gen i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hrange, ← MonoidHom.map_closure, h, Subgroup.map_top_of_surjective _ hf]

/-- **Presentations transport along an isomorphism of groups.**  If `e : G ≃* H` and `G` admits an
abstract presentation with `d` generators and at most `r` relators, then so does `H`: transport the
generating family along `e` and keep the same relator set. -/
theorem hasAbstractPresentation_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {d r : ℕ} (h : HasAbstractPresentation G d r) : HasAbstractPresentation H d r := by
  obtain ⟨P⟩ := h
  exact ⟨{ gen := fun i => e (P.gen i),
           rel := P.rel,
           generating := generating_comp_of_surjective (e : G →* H) e.surjective P.gen P.generating,
           card_le := P.card_le,
           ker_eq := by rw [ker_lift_comp_mulEquiv, P.ker_eq] }⟩

end Work.RelatorRank.Transfer
