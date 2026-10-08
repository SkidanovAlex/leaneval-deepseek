import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.PSL.centralizer_psl_dihedral
import Submission.Work.L2F.Dihedral.dihedral_oddSubgroup
import Submission.Work.L2F.Involution.lift_sq_neg_one

open scoped MatrixGroups
open Subgroup (centralizer)

namespace Work.L2F.Props

/-- `L2CentOddCyclicProp`: odd-order subgroups of the centralizer of an involution in `L₂(q)` are
cyclic and inverted by an involution of the centralizer.
Proof: for an involution `t`, `C(t) ≃* DihedralGroup n` (`PSL.centralizer_psl_dihedral`, with the
lifting `Involution.lift_sq_neg_one`); transport `Y ≤ C(t)` of odd order along the isomorphism and
apply `Dihedral.dihedral_oddSubgroup` to get `IsCyclic` and an inverting involution `s`; transport
back along the isomorphism (using `MulEquiv`-invariance of `Nat.card`, `IsCyclic` and `Inverts`). -/
theorem L2CentOddCyclic : Work.L2F.L2CentOddCyclicProp := by
  intro p k _ hp h5 t ht Y hYle hYodd
  -- The field `GaloisField p k` has odd characteristic, so `2 ≠ 0`.
  have h2 : (2 : GaloisField p k) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have h2p : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    have : p = 2 := le_antisymm hle h2p
    rw [this] at hp
    exact (by decide : ¬ Odd 2) hp
  -- Lift the involution `t` to `x ∈ SL(2,F)` with `x * x = -1`.
  obtain ⟨x, hx_eq, hx_sq⟩ :=
    Work.L2F.Involution.lift_sq_neg_one (GaloisField p k) h2 t ht
  -- The centralizer of `t` is dihedral of order `2n`.
  obtain ⟨n, hn, ⟨e0⟩⟩ :=
    @Work.L2F.PSL.centralizer_psl_dihedral (GaloisField p k) _
      (Fintype.ofFinite _) h2 x hx_sq
  set Ct := Subgroup.centralizer ({t} : Set (PSL(2, GaloisField p k))) with hCt
  have he0 : Ct ≃* DihedralGroup n := by
    have hset : ({t} : Set (PSL(2, GaloisField p k))) =
        {Work.PSL2.pslMap (GaloisField p k) x} := by
      rw [hx_eq]
    rw [hCt, hset]
    exact e0
  -- Transport `Y ≤ C(t)` to a subgroup of `DihedralGroup n`.
  set Yct : Subgroup ↥Ct := Y.subgroupOf Ct with hYct
  set Yc : Subgroup (DihedralGroup n) := Yct.map he0.toMonoidHom with hYc
  have hYct_card : Nat.card Yct = Nat.card Y := by
    rw [hYct]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYle).toEquiv
  have hYc_card : Nat.card Yc = Nat.card Y := by
    rw [hYc, Subgroup.card_map_of_injective (K := Yct) he0.injective, hYct_card]
  have hYc_odd : Odd (Nat.card Yc) := by rw [hYc_card]; exact hYodd
  obtain ⟨hcycYc, s, hsord, hsinv⟩ := Work.L2F.Dihedral.dihedral_oddSubgroup Yc hYc_odd
  refine ⟨?_, (he0.symm s : PSL(2, GaloisField p k)), ?_, ?_, ?_⟩
  · -- `Y` is cyclic: it is isomorphic to the cyclic group `Yc`.
    have hcycYct : IsCyclic ↥Yct :=
      (MulEquiv.isCyclic (Subgroup.equivMapOfInjective Yct he0.toMonoidHom
        he0.injective)).mpr hcycYc
    exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hYle)).mp hcycYct
  · -- the inverting involution lies in `C(t)`.
    exact (he0.symm s).2
  · -- and is an involution.
    have h1 : orderOf (he0.symm s : ↥Ct) = 2 :=
      (orderOf_injective (he0.symm : DihedralGroup n →* ↥Ct) he0.symm.injective s).trans hsord
    exact (Subgroup.orderOf_coe (he0.symm s)).trans h1
  · -- transport the inversion along the isomorphism.
    intro y hy
    have hysub : (⟨y, hYle hy⟩ : ↥Ct) ∈ Yct := by
      rw [hYct]
      exact Subgroup.mem_subgroupOf.mpr hy
    have hmem : he0 (⟨y, hYle hy⟩ : ↥Ct) ∈ Yc := by
      rw [hYc]
      exact Subgroup.mem_map.mpr ⟨⟨y, hYle hy⟩, hysub, rfl⟩
    have h1 : he0 (he0.symm s * (⟨y, hYle hy⟩ : ↥Ct) * (he0.symm s)⁻¹)
        = he0 ((⟨y, hYle hy⟩ : ↥Ct)⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
      exact hsinv (he0 (⟨y, hYle hy⟩ : ↥Ct)) hmem
    have h2 : he0.symm s * (⟨y, hYle hy⟩ : ↥Ct) * (he0.symm s)⁻¹
        = (⟨y, hYle hy⟩ : ↥Ct)⁻¹ := he0.injective h1
    show ((he0.symm s : ↥Ct) : PSL(2, GaloisField p k)) * y
        * ((he0.symm s : ↥Ct) : PSL(2, GaloisField p k))⁻¹ = y⁻¹
    have h3 : (((he0.symm s * (⟨y, hYle hy⟩ : ↥Ct) * (he0.symm s)⁻¹ : ↥Ct)) :
          PSL(2, GaloisField p k))
        = (((⟨y, hYle hy⟩ : ↥Ct)⁻¹ : ↥Ct) : PSL(2, GaloisField p k)) := by rw [h2]
    simpa using h3

end Work.L2F.Props
