import Mathlib
import Submission.Work.SSGRoute.ZDataMup.levelKRigidity
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

/-- **A level family of local forms from a family of local forms at the places.**

A family of `𝔽_p`-bilinear forms indexed by the *finite places* `A` of `Ω` over `k` (the form at
`A` living on the local group `H_A = decomp k A ⊓ K.fixingSubgroup`) can be repackaged as a family
indexed by *all* subgroups `H ≤ G_k = Ω ≃ₐ[k] Ω`: declare the form to be `0` at a subgroup which is
not of the shape `H_A`, and for a subgroup of that shape choose a witness place.

This is well defined because a finite place is *determined* by its level-`K` decomposition group
(`Work.SSGRoute.ZDataMup.decomp_inf_fixingSubgroup_eq_imp_eq`): two witnesses for the same subgroup
are equal, so the local form transported along the witness equation does not depend on the witness —
which is exactly what the clause `F (decomp k A ⊓ K.fixingSubgroup) x y = G A hA x y` asserts for
the *given* witness `A`. -/
theorem exists_levelFamily_of_placeFamily (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsSepClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (G : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) →ₗ[ZMod p]
        (Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) →ₗ[ZMod p]
          ZMod p)) :
    ∃ F : ∀ H : Subgroup (Ω ≃ₐ[k] Ω),
        Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p]
          (Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p] ZMod p),
      ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
        (x y : Work.SSGRoute.H1loc p k Ω K (ZMod p)
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup)),
        F (SSGRoute.decomp k A ⊓ K.fixingSubgroup) x y = G A hA x y := by
  classical
  -- Transport bookkeeping: two places with the same level-`K` local group carry the *same* local
  -- form, so the witness selected by `Classical.choose` is harmless.
  have transport_G : ∀ {A' A : ValuationSubring Ω} (heq : A' = A)
      (hA' : SSGRoute.IsFinPlace k A') (hA : SSGRoute.IsFinPlace k A)
      (e : SSGRoute.decomp k A' ⊓ K.fixingSubgroup
        = SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      e ▸ (G A' hA') = G A hA := by
    intro A' A heq hA' hA e
    cases heq
    have h1 : e ▸ (G A' hA') = G A' hA' := by
      have h : e = rfl := Subsingleton.elim _ _
      rw [h]
    rw [h1]
  -- The level family: `0` away from the subgroups of the shape `H_A`, and the transported form of a
  -- chosen witness place at such a subgroup.
  let F : ∀ H : Subgroup (Ω ≃ₐ[k] Ω),
      Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p]
        (Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p] ZMod p) :=
    fun H => if h : ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
        SSGRoute.decomp k A ⊓ K.fixingSubgroup = H
      then h.choose_spec.2 ▸ G h.choose h.choose_spec.1
      else 0
  refine ⟨F, ?_⟩
  intro A hA x y
  have hh : ∃ A' : ValuationSubring Ω, SSGRoute.IsFinPlace k A' ∧
      SSGRoute.decomp k A' ⊓ K.fixingSubgroup = SSGRoute.decomp k A ⊓ K.fixingSubgroup :=
    ⟨A, hA, rfl⟩
  have hF : F (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
      = hh.choose_spec.2 ▸ G hh.choose hh.choose_spec.1 := by
    dsimp only [F]
    exact dif_pos hh
  rw [hF]
  -- the chosen witness has the same level-`K` group, hence it *is* the place `A`
  rw [transport_G (decomp_inf_fixingSubgroup_eq_imp_eq k Ω K hh.choose A
    hh.choose_spec.1 hA hh.choose_spec.2) hh.choose_spec.1 hA hh.choose_spec.2]

end Work.SSGRoute.ZDataMup
