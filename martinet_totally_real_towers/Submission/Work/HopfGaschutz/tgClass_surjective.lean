import Mathlib
import Submission.Work.HopfGaschutz.Setup
import Submission.Work.HopfGaschutz.h2_freeGroup_subsingleton
import Submission.Work.ConCohomology.ker_H2Res_eq_range_tg
import Submission.Work.ConCohomology.All

/-!
# `Work.HopfGaschutz.tgClass_surjective` -- the transgression is onto `H²(Q, 𝔽₂)`

The extension `1 → K → F → Q → 1` of `Setup.lean` has `F = FreeGroup α` of cohomological
dimension one: every `2`-cocycle of a free group with coefficients in an abelian group acting
trivially is a coboundary (`Work.HopfGaschutz.h2_freeGroup_subsingleton`, proved at the level of
cochains in `Submission/Work/HopfGaschutz/h2_freeGroup_subsingleton.lean`).  Consequently
`inf₂ : H²(Q, 𝔽₂) → H²(F, 𝔽₂)` is the zero map, and the five term exact sequence
`ker(inf₂) = im(tg)` proved at the cochain level in `Work.ConCohomology.ker_H2Res_eq_range_tg`
makes the transgression

`tgClass : {φ ∈ Z¹(K,𝔽₂) // φ is F-invariant} → H²(Q, 𝔽₂)`

**surjective**.  This is the classical statement that the transgression detects the whole of
`H²(Q,𝔽₂)` when the presenting group is free (Koch, *Galois theory of `p`-extensions*, Ch. 11).

The target statement is not touched.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.HopfGaschutz

open Work.ConCohomology

theorem tgClass_surjective {α Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [TopologicalSpace (FreeGroup α)] [DiscreteTopology (FreeGroup α)] [DiscreteTopology Q]
    (gen : α → Q) (hgen : Subgroup.closure (Set.range gen) = ⊤) :
    Function.Surjective (fun φ : {φ : Work.ConCohomology.Z1 ↥(Work.HopfGaschutz.presKernel gen) (ZMod 2) //
        Work.HopfGaschutz.IsConjInvariant gen φ} =>
      Work.HopfGaschutz.tgClass gen hgen φ.1 φ.2) := by
  intro x
  haveI : Subsingleton (Work.ConCohomology.H2 (FreeGroup α) (ZMod 2)) :=
    h2_freeGroup_subsingleton α
  refine QuotientAddGroup.induction_on x ?_
  intro z
  -- `H²(FreeGroup α, 𝔽₂) = 0`, so the class of `z` dies under inflation
  have hzero : H2Res (presExt gen).q continuous_of_discreteTopology (fun y m => rfl) (H2.mk z) = 0 :=
    Subsingleton.elim _ _
  -- the coch-level exactness `ker(inf₂) = im(tg)` produces the required invariant cocycle
  obtain ⟨φ, hφcoc, hφinv, w, hw⟩ :=
    (ker_H2Res_eq_range_tg (presExt gen) continuous_of_discreteTopology
      continuous_of_discreteTopology (fun n m => rfl) (fun y m => rfl)
      (presSection gen hgen) (presSection_spec gen hgen) continuous_of_discreteTopology
      continuous_of_discreteTopology z).mp hzero
  -- with the trivial action, `F`-invariance is exactly the invariance of the cocycle
  have hinv : IsConjInvariant gen φ := fun g n => (hφinv g n).trans rfl
  refine ⟨⟨φ, hinv⟩, ?_⟩
  change H2.mk ⟨tgCochainOf gen hgen φ, mem_Z2.mpr (isCocycle2_tgCochainOf gen hgen hinv)⟩
    = H2.mk z
  rw [H2.mk_eq_mk_iff, mem_B2', mem_B2]
  refine ⟨w, ?_⟩
  ext p
  obtain ⟨y₁, y₂⟩ := p
  have h := congrFun hw (y₁, y₂)
  simp only [Pi.sub_apply] at h
  simpa only [d1Hom_apply, d1Fun_apply, tgCochainOf, LocallyConstant.sub_apply,
    AddSubgroup.coe_sub] using h.symm

end Work.HopfGaschutz
