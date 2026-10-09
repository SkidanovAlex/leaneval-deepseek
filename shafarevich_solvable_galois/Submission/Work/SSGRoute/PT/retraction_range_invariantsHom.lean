import Mathlib
import Submission.Work.SSGRoute.PT.AlphaPairing
import Submission.Work.SSGRoute.PT.submodule_retraction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A retraction of the range of `invariantsHom ψ`

Companion of `PT/retraction_invariantsHom.lean`: for `𝔽_p[G]`-modules and an equivariant
`ψ : N₂ →+ N₁`, the inclusion `range (invariantsHom ψ hψ) ↪ (invariants G N₁)` admits an additive
retraction.  This is the exactness input `hbot` of the `α²`-dévissage
(`PT/AlphaTwoAssembly.lean`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Classical

namespace Work.SSGRoute.PT

theorem retraction_range_invariantsHom (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] {N₁ : Type*} [AddCommGroup N₁] [Module (ZMod p) N₁]
    [DistribMulAction G N₁] [SMulCommClass G (ZMod p) N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module (ZMod p) N₂] [DistribMulAction G N₂]
    [SMulCommClass G (ZMod p) N₂]
    (ψ : N₂ →+ N₁) (hψ : Work.GroupCohomology.IsEquivariant G ψ) :
    ∃ r : ↥(Work.GroupCohomology.invariants G N₁) →+
        ↥((Work.SSGRoute.PT.invariantsHom ψ hψ).range),
      ∀ x : ↥((Work.SSGRoute.PT.invariantsHom ψ hψ).range),
        r (x : ↥(Work.GroupCohomology.invariants G N₁)) = x := by
  classical
  haveI hne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- the image of the range inside `N₁`
  let M : AddSubgroup N₁ := (Work.SSGRoute.PT.invariantsHom ψ hψ).range.map
    (AddSubgroup.subtype (Work.GroupCohomology.invariants G N₁))
  have hmap : ∀ (a : ↥(Work.GroupCohomology.invariants G N₁)),
      a ∈ (Work.SSGRoute.PT.invariantsHom ψ hψ).range →
      ((a : N₁)) ∈ M := fun a ha => ⟨a, ha, rfl⟩
  let L : Submodule (ZMod p) N₁ :=
    { carrier := M
      zero_mem' := M.zero_mem
      add_mem' := fun ha hb => M.add_mem ha hb
      smul_mem' := by
        intro c x hx
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨z, rfl⟩ := ha
        have hstep : c • ((Work.SSGRoute.PT.invariantsHom ψ hψ z) : N₁)
            = ((c.val : ℕ) : ZMod p) • ((Work.SSGRoute.PT.invariantsHom ψ hψ z) : N₁) :=
          congrArg (fun d : ZMod p => d • ((Work.SSGRoute.PT.invariantsHom ψ hψ z) : N₁))
            (ZMod.natCast_zmod_val c).symm
        refine ⟨c.val • Work.SSGRoute.PT.invariantsHom ψ hψ z,
          ⟨c.val • z, map_nsmul (Work.SSGRoute.PT.invariantsHom ψ hψ) c.val z⟩, ?_⟩
        change c.val • ((Work.SSGRoute.PT.invariantsHom ψ hψ z) : N₁)
          = c • ((Work.SSGRoute.PT.invariantsHom ψ hψ z) : N₁)
        rw [hstep, Nat.cast_smul_eq_nsmul] }
  obtain ⟨r', hr'⟩ := submodule_retraction p N₁ L
  have hinj : Function.Injective
      (AddSubgroup.subtype (Work.GroupCohomology.invariants G N₁)) :=
    AddSubgroup.subtype_injective _
  let e : ↥((Work.SSGRoute.PT.invariantsHom ψ hψ).range) ≃+ ↥L :=
    (Work.SSGRoute.PT.invariantsHom ψ hψ).range.equivMapOfInjective
      (AddSubgroup.subtype (Work.GroupCohomology.invariants G N₁)) hinj
  refine ⟨e.symm.toAddMonoidHom.comp (r'.comp (AddSubgroup.subtype _)), ?_⟩
  intro x
  have hcoe : ((e x : ↥L) : N₁) = ((x : ↥(Work.GroupCohomology.invariants G N₁)) : N₁) := rfl
  have hx : r' (((x : ↥((Work.SSGRoute.PT.invariantsHom ψ hψ).range)) :
      ↥(Work.GroupCohomology.invariants G N₁)) : N₁) = e x := by
    have h := hr' (e x)
    rw [hcoe] at h
    exact h
  show e.symm (r' (((x : ↥((Work.SSGRoute.PT.invariantsHom ψ hψ).range)) :
    ↥(Work.GroupCohomology.invariants G N₁)) : N₁)) = x
  rw [hx]
  exact e.symm_apply_apply x

end Work.SSGRoute.PT
