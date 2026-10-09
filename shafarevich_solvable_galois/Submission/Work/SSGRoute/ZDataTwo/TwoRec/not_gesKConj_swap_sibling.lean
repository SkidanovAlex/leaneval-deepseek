import Mathlib
import Submission.Work.SSGRoute.P2Core.siblingPlace
import Submission.Work.SSGRoute.H9.swChainConjDefs
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo.TwoRec

/-- Replacing the second argument of `gesKConj K A` by a `K`-translate by an element of
`K.fixingSubgroup` does not change the relation: `K.fixingSubgroup` acts trivially on the set of
`K`-classes of places.  Both directions are the obvious transport of the witnessing element of
`K.fixingSubgroup` (multiply by `ρ` resp. by `ρ⁻¹`). -/
private lemma gesKConj_smul_mem_fixingSubgroup_iff {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} {ρ : Ω ≃ₐ[k] Ω} (hρ : ρ ∈ K.fixingSubgroup)
    (A B : ValuationSubring Ω) :
    Work.SSGRoute.gesKConj K A (ρ • B) ↔ Work.SSGRoute.gesKConj K A B := by
  constructor
  · rintro ⟨τ, hτ, hτA⟩
    exact ⟨ρ⁻¹ * τ, K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem hρ) hτ, by
      rw [mul_smul, hτA, inv_smul_smul]⟩
  · rintro ⟨τ, hτ, hτA⟩
    exact ⟨ρ * τ, K.fixingSubgroup.mul_mem hρ hτ, by rw [mul_smul, hτA]⟩

theorem not_gesKConj_swap_sibling {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (Qs Qt : ValuationSubring Ω) (σ : K ≃ₐ[k] K)
    (h : ¬ Work.SSGRoute.gesKConj K Qs (Work.SSGRoute.ZDataMup.siblingPlace K σ Qt)) :
    ¬ Work.SSGRoute.gesKConj K Qt (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Qs) := by
  -- `siblingPlace K τ Q` is by definition `galLift K τ • Q`.
  intro h2
  rw [Work.SSGRoute.ZDataMup.siblingPlace] at h2
  -- It suffices to contradict `h`; by symmetry it suffices to contradict
  -- `gesKConj K (galLift K σ⁻¹ • Qs) Qt`.
  apply h
  have h2' : Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.galLift K σ⁻¹ • Qs) Qt :=
    Work.SSGRoute.H9.gesKConj_symm'' h2
  -- Translate back by `galLift K σ⁻¹`: `Qs` is `K`-conjugate to `(galLift K σ⁻¹)⁻¹ • Qt`.
  have h3 : Work.SSGRoute.gesKConj K Qs
      ((Work.SSGRoute.ZDataMup.galLift K σ⁻¹)⁻¹ • Qt) :=
    (Work.SSGRoute.H9.swGesKConj_galLift_smul_iff (K := K) σ⁻¹ Qs Qt).mp h2'
  -- `(galLift K σ⁻¹)⁻¹` and `galLift K σ` differ by an element `ρ` of `K.fixingSubgroup`.
  have hρ : (Work.SSGRoute.ZDataMup.galLift K σ⁻¹)⁻¹
      * (Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ ∈ K.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker, map_mul, map_inv, map_inv,
      Work.SSGRoute.ZDataMup.galLift_spec, Work.SSGRoute.ZDataMup.galLift_spec, inv_inv,
      mul_inv_cancel]
  have h3' : Work.SSGRoute.gesKConj K Qs
      (((Work.SSGRoute.ZDataMup.galLift K σ⁻¹)⁻¹ * (Work.SSGRoute.ZDataMup.galLift K σ)⁻¹)
        • (Work.SSGRoute.ZDataMup.galLift K σ • Qt)) := by
    rw [mul_smul, inv_smul_smul]
    exact h3
  have h4 : Work.SSGRoute.gesKConj K Qs (Work.SSGRoute.ZDataMup.galLift K σ • Qt) :=
    (gesKConj_smul_mem_fixingSubgroup_iff (K := K) hρ Qs
      (Work.SSGRoute.ZDataMup.galLift K σ • Qt)).mp h3'
  rw [Work.SSGRoute.ZDataMup.siblingPlace]
  exact h4

end Work.SSGRoute.ZDataTwo.TwoRec
