import Mathlib
import Submission.Work.PSTAB.Defs
import Submission.Work.PSTAB.StabQuotientPGroup

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped commutatorElement
open Subgroup

namespace Work.PSTAB

theorem StabilityLift {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K : Subgroup M} [K.Normal] (hK : IsPGroup p K)
    {A : Subgroup M} (hA : IsPGroup p A)
    (hKAA : ⁅⁅K, A⁆, A⁆ = (⊥ : Subgroup M))
    (hstab : ∀ i : ℕ, ⁅OddOrder.GroupTheory.chiefSeriesInside K i, A⁆ ≤
      OddOrder.GroupTheory.chiefSeriesInside K (i + 1)) :
    A.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M))) ≤
      OddOrder.Isaacs.Ch01.opCore p (M ⧸ Subgroup.centralizer (K : Set M)) := by
  classical
  -- `H`: the chain stabilizer of the chief series of `K` inside `M`.
  set H : Subgroup M := ⨅ i : ℕ, OddOrder.GroupTheory.chiefFactorCentralizer
      (OddOrder.GroupTheory.chiefSeriesInside K i)
      (OddOrder.GroupTheory.chiefSeriesInside K (i + 1)) with hHdef
  -- (1) `A ≤ H` is exactly the hypothesis `hstab`.
  have hA_H : A ≤ H := by
    rw [hHdef]
    refine le_iInf (fun i => ?_)
    rw [OddOrder.GroupTheory.chiefFactorCentralizer.le_iff_commutator_le]
    exact hstab i
  -- (2) `C_M(K) ≤ H`.
  have hC_H : Subgroup.centralizer (K : Set M) ≤ H := by
    rw [hHdef]
    refine le_iInf (fun i => ?_)
    rw [OddOrder.GroupTheory.chiefFactorCentralizer.le_iff_commutator_le]
    refine le_trans ?_ (bot_le : (⊥ : Subgroup M) ≤ _)
    rw [Subgroup.commutator_le]
    intro u hu c hc
    have huK : u ∈ K := OddOrder.GroupTheory.chiefSeriesInside_le K i hu
    have hcomm : u * c = c * u := (Subgroup.mem_centralizer_iff.mp hc) u huK
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  -- (3) `H` stabilizes every chief factor of the series, elementwise.
  have hH_stab : ∀ h ∈ H, ∀ i : ℕ,
      ⁅OddOrder.GroupTheory.chiefSeriesInside K i, Subgroup.zpowers h⁆ ≤
        OddOrder.GroupTheory.chiefSeriesInside K (i + 1) := by
    intro h hh i
    have hle : Subgroup.zpowers h ≤ H := Subgroup.zpowers_le.mpr hh
    have hi : H ≤ OddOrder.GroupTheory.chiefFactorCentralizer
        (OddOrder.GroupTheory.chiefSeriesInside K i)
        (OddOrder.GroupTheory.chiefSeriesInside K (i + 1)) := by
      rw [hHdef]; exact iInf_le _ i
    exact le_trans (Subgroup.commutator_mono le_rfl hle)
      (OddOrder.GroupTheory.chiefFactorCentralizer.commutator_le_of_le hi)
  -- (4) `H ◁ M`.
  have hHnorm : H.Normal := by
    rw [hHdef]
    exact Subgroup.normal_iInf_normal (fun i => inferInstance)
  -- (5) `H C_M(K)/C_M(K)` is a `p`-group.
  have hHmap_pg : IsPGroup p
      (H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M)))) :=
    StabQuotientPGroup hK H hH_stab
  -- (6) Hence it is a normal `p`-subgroup of `M/C_M(K)`, so inside `O_p`.
  haveI hHmap_norm : (H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M)))).Normal :=
    hHnorm.map _ (QuotientGroup.mk'_surjective _)
  calc A.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M)))
      ≤ H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M))) := Subgroup.map_mono hA_H
    _ ≤ OddOrder.Isaacs.Ch01.opCore p (M ⧸ Subgroup.centralizer (K : Set M)) :=
        OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hHmap_pg

end Work.PSTAB
