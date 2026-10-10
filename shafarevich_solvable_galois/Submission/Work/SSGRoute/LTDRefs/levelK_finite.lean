import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.finite_H1loc_inertia_free
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.LTDRefs

set_option linter.style.haveILetI false

open Classical

theorem levelK_finite (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    Finite (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) := by
  let H : Subgroup (Ω ≃ₐ[k] Ω) := SSGRoute.decomp k A ⊓ K.fixingSubgroup
  letI : DistribMulAction ↥H M := SSGRoute.subgroupDistribMulAction k Ω K M H
  have hle : H ≤ K.fixingSubgroup := inf_le_right
  have hker_le : (K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) ≤ (SSGRoute.res k K).ker := by
    rw [IntermediateField.restrictNormalHom_ker (E := K)]
  have htriv : ∀ (u : ↥(H ⊓ K.fixingSubgroup)) (m : M),
      (Subgroup.inclusion inf_le_left u : ↥H) • m = m := by
    intro u m
    have hu : ((Subgroup.inclusion inf_le_left u : ↥H) : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup :=
      hle (Subgroup.inclusion inf_le_left u).2
    have h1 : SSGRoute.res k K
        ((Subgroup.inclusion inf_le_left u : ↥H) : Ω ≃ₐ[k] Ω) = 1 :=
      MonoidHom.mem_ker.mp (hker_le hu)
    show SSGRoute.res k K ((Subgroup.inclusion inf_le_left u : ↥H) : Ω ≃ₐ[k] Ω) • m = m
    rw [h1, one_smul]
  have hfin : Finite {χ : ↥(H ⊓ K.fixingSubgroup) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(H ⊓ K.fixingSubgroup))} := by
    have hEq : H ⊓ K.fixingSubgroup = H := inf_eq_left.mpr hle
    rw [hEq]
    exact finite_openKernel_homs_decomp_kernel p k Ω K A hA M
  haveI hZ1 : Finite ↥(Work.AbsoluteKummer.Z1 ↥H M) :=
    finite_Z1_of_finite_homs p k Ω K H M htriv hfin
  haveI hH1 : Finite (Work.AbsoluteKummer.H1 ↥H M) :=
    Finite.of_surjective (Work.AbsoluteKummer.H1π ↥H M) (QuotientAddGroup.mk'_surjective _)
  exact Finite.of_injective
    (H1locEquivH1 p k Ω K M H (fun _ _ => rfl))
    (H1locEquivH1 p k Ω K M H (fun _ _ => rfl)).injective

end Work.SSGRoute.LTDRefs
