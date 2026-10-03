import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.magnusStepNielsenRoute
import Submission.Work.OROneRel.hnn_bot_presentedGroup_single_iso_freeGroup
import Submission.Work.OROneRel.not_isProperPower_of

/-!
# The Magnus step at `l = 1` when the one-relator group is free

The target `Work.OROneRel.MagnusStepData u 1` asks for a strictly shorter one-relator vertex `⟨β | v⟩`
together with an HNN decomposition `⟨α | u⟩ ≅ HNN(⟨β | v⟩, A, B, φ)` carrying the class of `u` to a
conjugate of the class of `v`.  When `⟨α | u⟩` is *free* — here, isomorphic to `F (Option γ)` — the
whole of `⟨α | u⟩` is recovered from the free vertex `⟨Option γ | of none⟩ ≅ F γ` by adjoining one
more free generator: the HNN extension with *trivial* associated subgroups is the free product with
`ℤ`, and `F γ ∗ ℤ ≅ F (Option γ)` (`Work.OROneRel.hnn_bot_presentedGroup_single_iso_freeGroup`).

At `l = 1` the root tracking is automatic: the class of the relator `u` in `⟨α | u⟩` and the class of
the vertex root `of none` in `⟨Option γ | of none⟩` are both trivial, so the tracking element is
`c = 1`.
-/

namespace Work.OROneRel

universe u

/-- The norm of a free generator is `1`. -/
theorem relatorNorm_freeGroup_of {β : Type u} (x : β) : relatorNorm (FreeGroup.of x) = 1 := by
  classical
  rw [relatorNorm, FreeGroup.norm_of]

/-- **The Magnus step at `l = 1` for a one-relator group that is free.**

If `⟨α | u ^ 1⟩ ≅ F (Option γ)` with `relatorNorm u ≥ 2`, then `MagnusStepData u 1` holds, with

* the free vertex `β = Option γ`, `v = FreeGroup.of none`, whose norm `1 < relatorNorm u` and which
  is never a proper power (`Work.OROneRel.not_isProperPower_of`),
* the associated subgroups `A = B = ⊥`, so that the HNN extension is the free product `F γ ∗ ℤ`,
  identified with `F (Option γ)` by `Work.OROneRel.hnn_bot_presentedGroup_single_iso_freeGroup`,
* the tracking element `c = 1`, since at `l = 1` both classes involved are trivial. -/
theorem magnusStepData_one_of_freeGroupPresentation {α : Type u} (u : FreeGroup α)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u) (γ : Type u)
    (e : PresentedGroup ({u ^ 1} : Set (FreeGroup α)) ≃* FreeGroup (Option γ)) :
    Work.OROneRel.MagnusStepData u 1 := by
  classical
  -- the free vertex: the HNN extension of `⟨Option γ | of none⟩` over trivial associated subgroups
  -- is `F γ ∗ ℤ ≅ F (Option γ)`.
  obtain ⟨E⟩ := hnn_bot_presentedGroup_single_iso_freeGroup (none : Option γ)
    (MulEquiv.refl (⊥ : Subgroup (PresentedGroup ({FreeGroup.of (none : Option γ)} :
      Set (FreeGroup (Option γ))))))
  refine ⟨Option γ, FreeGroup.of (none : Option γ), not_isProperPower_of (none : Option γ), ?_, ?_⟩
  · -- the norm of the vertex root
    rw [relatorNorm_freeGroup_of]
    omega
  · refine ⟨(⊥ : Subgroup (PresentedGroup ({FreeGroup.of (none : Option γ) ^ 1} :
        Set (FreeGroup (Option γ))))),
      (⊥ : Subgroup (PresentedGroup ({FreeGroup.of (none : Option γ) ^ 1} :
        Set (FreeGroup (Option γ))))),
      MulEquiv.refl _, e.trans E.symm, 1, ?_⟩
    -- the root tracking: at `l = 1` both classes are trivial
    have hmkU : PresentedGroup.mk ({u ^ 1} : Set (FreeGroup α)) u = 1 :=
      PresentedGroup.one_of_mem (by rw [Set.mem_singleton_iff]; exact (pow_one u).symm)
    have hmkV : PresentedGroup.mk ({FreeGroup.of (none : Option γ) ^ 1} :
        Set (FreeGroup (Option γ))) (FreeGroup.of (none : Option γ)) = 1 :=
      PresentedGroup.one_of_mem (by rw [Set.mem_singleton_iff]; exact (pow_one _).symm)
    rw [hmkU, hmkV]
    simp

end Work.OROneRel
