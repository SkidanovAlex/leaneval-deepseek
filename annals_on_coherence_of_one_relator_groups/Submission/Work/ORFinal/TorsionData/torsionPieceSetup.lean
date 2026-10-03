import Mathlib
import Submission.Work.ORFinal.TorsionData.Defs
import Submission.Work.ORLinnell.CommonDenominators.exists_common_denominator
import Submission.Work.ORLinnell.Laurent.existsUnique_laurent_rep

namespace Work.ORFinal.TorsionData

open Work.ORLinnell

theorem torsionPieceSetup {G : Type*} [Group G] (G' : Subgroup G) [G'.Normal] [G'.FiniteIndex]
    (hG'tf : Work.ORLocInd.IsTorsionFree G') (H : Subgroup G) (φ : H →* Multiplicative ℤ)
    (hφ : Function.Surjective φ) :
    ((H ⊓ G').subgroupOf H).Normal ∧ ((H ⊓ G').subgroupOf H).FiniteIndex ∧
    (Work.ORFinal.TorsionData.Nsub φ ⊓ G' ≤ H ⊓ G') ∧
    ((Work.ORFinal.TorsionData.Nsub φ ⊓ G').subgroupOf (H ⊓ G')).Normal ∧
    Work.ORLinnell.IsExtensionByZ (Work.ORFinal.TorsionData.Nsub φ ⊓ G') (H ⊓ G') ∧
    (∃ s₀ : ↥(H ⊓ G'),
      (∀ h : ↥(H ⊓ G'), ∃ j : ℤ,
        h * s₀ ^ (-j) ∈ (Work.ORFinal.TorsionData.Nsub φ ⊓ G').subgroupOf (H ⊓ G')) ∧
      (∀ k : ℤ, s₀ ^ k ∈ (Work.ORFinal.TorsionData.Nsub φ ⊓ G').subgroupOf (H ⊓ G') → k = 0)) := by
  -- `H ⊓ G'` is `G'` cut down to `H`, so it inherits normality and finite index from `G'`.
  have hHfin : ((H ⊓ G').subgroupOf H).FiniteIndex := by
    rw [Subgroup.inf_subgroupOf_left G' H]
    infer_instance
  have hHnorm : ((H ⊓ G').subgroupOf H).Normal := by
    rw [Subgroup.inf_subgroupOf_left G' H]
    exact (inferInstance : G'.Normal).subgroupOf H
  -- `Nsub φ = ker φ` is normal in `H`, hence so is `Nsub φ ⊓ G'` in `H ⊓ G'`.
  haveI : ((Nsub φ).subgroupOf H).Normal := normal_subgroupOf_Nsub φ
  have hNnorm : ((Nsub φ ⊓ G').subgroupOf (H ⊓ G')).Normal :=
    Subgroup.inf_subgroupOf_inf_normal_of_left (A' := Nsub φ) (A := H) G'
  -- `φ` exhibits `H` as an extension of `Nsub φ` by `ℤ`.
  have hφext : IsExtensionByZ (Nsub φ) H := ⟨φ, hφ, (subgroupOf_Nsub φ).symm⟩
  -- Passing to the finite index subgroup `H ⊓ G'` preserves the extension by `ℤ`.
  have hIso : IsExtensionByZ (Nsub φ ⊓ G') (H ⊓ G') := by
    have h5 := CommonDenominators.isExtensionByZ_of_finiteIndex_le
      (N := Nsub φ) (H₀ := H ⊓ G') (H := H) inf_le_left hφext hHfin
    rwa [show Nsub φ ⊓ (H ⊓ G') = Nsub φ ⊓ G' from by
      rw [← inf_assoc, inf_eq_left.mpr (Nsub_le φ)]] at h5
  refine ⟨hHnorm, hHfin, ?_, hNnorm, hIso, ?_⟩
  · rintro x ⟨hx, hx'⟩
    exact ⟨Nsub_le φ hx, hx'⟩
  · obtain ⟨s₀, hs₀⟩ := hIso.exists_generator
    exact ⟨s₀, hs₀, Work.ORLinnell.Laurent.sPow_mem_subgroupOf hIso s₀ hs₀⟩

end Work.ORFinal.TorsionData
